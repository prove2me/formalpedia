-- Prove2me | solution 1 for syracuse_descends_range_1684042_1686042
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:22:54.751754+00:00
-- url     : https://prove2.me/submissions/644237c6-74ef-4ed2-81a4-5d8f43cf685b

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


theorem B2842661 : Blo 1684042 2842661 := bbase (se 4 (by rfl) ⟨266499, by rfl⟩ : syracuseStep 2842661 = 532999) (by norm_num)
theorem B3792941 : Blo 1684042 3792941 := bbase (se 3 (by rfl) ⟨711176, by rfl⟩ : syracuseStep 3792941 = 1422353) (by norm_num)
theorem B2400301 : Blo 1684042 2400301 := bbase (se 3 (by rfl) ⟨450056, by rfl⟩ : syracuseStep 2400301 = 900113) (by norm_num)
theorem B3793013 : Blo 1684042 3793013 := bbase (se 5 (by rfl) ⟨177797, by rfl⟩ : syracuseStep 3793013 = 355595) (by norm_num)
theorem B2842789 : Blo 1684042 2842789 := bbase (se 4 (by rfl) ⟨266511, by rfl⟩ : syracuseStep 2842789 = 533023) (by norm_num)
theorem B3793085 : Blo 1684042 3793085 := bbase (se 3 (by rfl) ⟨711203, by rfl⟩ : syracuseStep 3793085 = 1422407) (by norm_num)
theorem B2842877 : Blo 1684042 2842877 := bbase (se 3 (by rfl) ⟨533039, by rfl⟩ : syracuseStep 2842877 = 1066079) (by norm_num)
theorem B3793157 : Blo 1684042 3793157 := bbase (se 4 (by rfl) ⟨355608, by rfl⟩ : syracuseStep 3793157 = 711217) (by norm_num)
theorem B2162977 : Blo 1684042 2162977 := bbase (se 2 (by rfl) ⟨811116, by rfl⟩ : syracuseStep 2162977 = 1622233) (by norm_num)
theorem B2023717 : Blo 1684042 2023717 := bbase (se 4 (by rfl) ⟨189723, by rfl⟩ : syracuseStep 2023717 = 379447) (by norm_num)
theorem B8528165 : Blo 1684042 8528165 := bbase (se 4 (by rfl) ⟨799515, by rfl⟩ : syracuseStep 8528165 = 1599031) (by norm_num)
theorem B3793229 : Blo 1684042 3793229 := bbase (se 3 (by rfl) ⟨711230, by rfl⟩ : syracuseStep 3793229 = 1422461) (by norm_num)
theorem B2883917 : Blo 1684042 2883917 := bbase (se 3 (by rfl) ⟨540734, by rfl⟩ : syracuseStep 2883917 = 1081469) (by norm_num)
theorem B5685605 : Blo 1684042 5685605 := bbase (se 4 (by rfl) ⟨533025, by rfl⟩ : syracuseStep 5685605 = 1066051) (by norm_num)
theorem B2843005 : Blo 1684042 2843005 := bbase (se 3 (by rfl) ⟨533063, by rfl⟩ : syracuseStep 2843005 = 1066127) (by norm_num)
theorem B10797461 : Blo 1684042 10797461 := bbase (se 6 (by rfl) ⟨253065, by rfl⟩ : syracuseStep 10797461 = 506131) (by norm_num)
theorem B3793301 : Blo 1684042 3793301 := bbase (se 6 (by rfl) ⟨88905, by rfl⟩ : syracuseStep 3793301 = 177811) (by norm_num)
theorem B2023861 : Blo 1684042 2023861 := bbase (se 5 (by rfl) ⟨94868, by rfl⟩ : syracuseStep 2023861 = 189737) (by norm_num)
theorem B2843093 : Blo 1684042 2843093 := bbase (se 7 (by rfl) ⟨33317, by rfl⟩ : syracuseStep 2843093 = 66635) (by norm_num)
theorem B3793373 : Blo 1684042 3793373 := bbase (se 3 (by rfl) ⟨711257, by rfl⟩ : syracuseStep 3793373 = 1422515) (by norm_num)
theorem B3793445 : Blo 1684042 3793445 := bbase (se 4 (by rfl) ⟨355635, by rfl⟩ : syracuseStep 3793445 = 711271) (by norm_num)
theorem B2843221 : Blo 1684042 2843221 := bbase (se 8 (by rfl) ⟨16659, by rfl⟩ : syracuseStep 2843221 = 33319) (by norm_num)
theorem B7201381 : Blo 1684042 7201381 := bbase (se 4 (by rfl) ⟨675129, by rfl⟩ : syracuseStep 7201381 = 1350259) (by norm_num)
theorem B3793517 : Blo 1684042 3793517 := bbase (se 3 (by rfl) ⟨711284, by rfl⟩ : syracuseStep 3793517 = 1422569) (by norm_num)
theorem B2843309 : Blo 1684042 2843309 := bbase (se 3 (by rfl) ⟨533120, by rfl⟩ : syracuseStep 2843309 = 1066241) (by norm_num)
theorem B3793589 : Blo 1684042 3793589 := bbase (se 5 (by rfl) ⟨177824, by rfl⟩ : syracuseStep 3793589 = 355649) (by norm_num)
theorem B3597061 : Blo 1684042 3597061 := bbase (se 4 (by rfl) ⟨337224, by rfl⟩ : syracuseStep 3597061 = 674449) (by norm_num)
theorem B5686037 : Blo 1684042 5686037 := bbase (se 6 (by rfl) ⟨133266, by rfl⟩ : syracuseStep 5686037 = 266533) (by norm_num)
theorem B2843437 : Blo 1684042 2843437 := bbase (se 3 (by rfl) ⟨533144, by rfl⟩ : syracuseStep 2843437 = 1066289) (by norm_num)
theorem B11682613 : Blo 1684042 11682613 := bbase (se 5 (by rfl) ⟨547622, by rfl⟩ : syracuseStep 11682613 = 1095245) (by norm_num)
theorem B2843525 : Blo 1684042 2843525 := bbase (se 4 (by rfl) ⟨266580, by rfl⟩ : syracuseStep 2843525 = 533161) (by norm_num)
theorem B2597765 : Blo 1684042 2597765 := bbase (se 4 (by rfl) ⟨243540, by rfl⟩ : syracuseStep 2597765 = 487081) (by norm_num)
theorem B3597205 : Blo 1684042 3597205 := bbase (se 6 (by rfl) ⟨84309, by rfl⟩ : syracuseStep 3597205 = 168619) (by norm_num)
theorem B2843653 : Blo 1684042 2843653 := bbase (se 4 (by rfl) ⟨266592, by rfl⟩ : syracuseStep 2843653 = 533185) (by norm_num)
theorem B6071381 : Blo 1684042 6071381 := bbase (se 8 (by rfl) ⟨35574, by rfl⟩ : syracuseStep 6071381 = 71149) (by norm_num)
theorem B2843741 : Blo 1684042 2843741 := bbase (se 3 (by rfl) ⟨533201, by rfl⟩ : syracuseStep 2843741 = 1066403) (by norm_num)
theorem B3843197 : Blo 1684042 3843197 := bbase (se 3 (by rfl) ⟨720599, by rfl⟩ : syracuseStep 3843197 = 1441199) (by norm_num)
theorem B5686469 : Blo 1684042 5686469 := bbase (se 4 (by rfl) ⟨533106, by rfl⟩ : syracuseStep 5686469 = 1066213) (by norm_num)
theorem B4105421 : Blo 1684042 4105421 := bbase (se 3 (by rfl) ⟨769766, by rfl⟩ : syracuseStep 4105421 = 1539533) (by norm_num)
theorem B2843869 : Blo 1684042 2843869 := bbase (se 3 (by rfl) ⟨533225, by rfl⟩ : syracuseStep 2843869 = 1066451) (by norm_num)
theorem B8209637 : Blo 1684042 8209637 := bbase (se 4 (by rfl) ⟨769653, by rfl⟩ : syracuseStep 8209637 = 1539307) (by norm_num)
theorem B3597581 : Blo 1684042 3597581 := bbase (se 3 (by rfl) ⟨674546, by rfl⟩ : syracuseStep 3597581 = 1349093) (by norm_num)
theorem B6399269 : Blo 1684042 6399269 := bbase (se 4 (by rfl) ⟨599931, by rfl⟩ : syracuseStep 6399269 = 1199863) (by norm_num)
theorem B2843957 : Blo 1684042 2843957 := bbase (se 5 (by rfl) ⟨133310, by rfl⟩ : syracuseStep 2843957 = 266621) (by norm_num)
theorem B5399909 : Blo 1684042 5399909 := bbase (se 4 (by rfl) ⟨506241, by rfl⟩ : syracuseStep 5399909 = 1012483) (by norm_num)
theorem B6071669 : Blo 1684042 6071669 := bbase (se 5 (by rfl) ⟨284609, by rfl⟩ : syracuseStep 6071669 = 569219) (by norm_num)
theorem B2131373 : Blo 1684042 2131373 := bbase (se 3 (by rfl) ⟨399632, by rfl⟩ : syracuseStep 2131373 = 799265) (by norm_num)
theorem B2844085 : Blo 1684042 2844085 := bbase (se 5 (by rfl) ⟨133316, by rfl⟩ : syracuseStep 2844085 = 266633) (by norm_num)
theorem B2024885 : Blo 1684042 2024885 := bbase (se 5 (by rfl) ⟨94916, by rfl⟩ : syracuseStep 2024885 = 189833) (by norm_num)
theorem B3843541 : Blo 1684042 3843541 := bbase (se 7 (by rfl) ⟨45041, by rfl⟩ : syracuseStep 3843541 = 90083) (by norm_num)
theorem B2131429 : Blo 1684042 2131429 := bbase (se 4 (by rfl) ⟨199821, by rfl⟩ : syracuseStep 2131429 = 399643) (by norm_num)
theorem B5400037 : Blo 1684042 5400037 := bbase (se 4 (by rfl) ⟨506253, by rfl⟩ : syracuseStep 5400037 = 1012507) (by norm_num)
theorem B2844173 : Blo 1684042 2844173 := bbase (se 3 (by rfl) ⟨533282, by rfl⟩ : syracuseStep 2844173 = 1066565) (by norm_num)
theorem B27313685 : Blo 1684042 27313685 := bbase (se 6 (by rfl) ⟨640164, by rfl⟩ : syracuseStep 27313685 = 1280329) (by norm_num)
theorem B8529461 : Blo 1684042 8529461 := bbase (se 5 (by rfl) ⟨399818, by rfl⟩ : syracuseStep 8529461 = 799637) (by norm_num)
theorem B2131525 : Blo 1684042 2131525 := bbase (se 4 (by rfl) ⟨199830, by rfl⟩ : syracuseStep 2131525 = 399661) (by norm_num)
theorem B6399557 : Blo 1684042 6399557 := bbase (se 4 (by rfl) ⟨599958, by rfl⟩ : syracuseStep 6399557 = 1199917) (by norm_num)
theorem B5686901 : Blo 1684042 5686901 := bbase (se 5 (by rfl) ⟨266573, by rfl⟩ : syracuseStep 5686901 = 533147) (by norm_num)
theorem B3597949 : Blo 1684042 3597949 := bbase (se 3 (by rfl) ⟨674615, by rfl⟩ : syracuseStep 3597949 = 1349231) (by norm_num)
theorem B2844301 : Blo 1684042 2844301 := bbase (se 3 (by rfl) ⟨533306, by rfl⟩ : syracuseStep 2844301 = 1066613) (by norm_num)
theorem B31147733 : Blo 1684042 31147733 := bbase (se 7 (by rfl) ⟨365012, by rfl⟩ : syracuseStep 31147733 = 730025) (by norm_num)
theorem B2844389 : Blo 1684042 2844389 := bbase (se 4 (by rfl) ⟨266661, by rfl⟩ : syracuseStep 2844389 = 533323) (by norm_num)
theorem B2131697 : Blo 1684042 2131697 := bbase (se 2 (by rfl) ⟨799386, by rfl⟩ : syracuseStep 2131697 = 1598773) (by norm_num)
theorem B4441853 : Blo 1684042 4441853 := bbase (se 3 (by rfl) ⟨832847, by rfl⟩ : syracuseStep 4441853 = 1665695) (by norm_num)
theorem B5121829 : Blo 1684042 5121829 := bbase (se 4 (by rfl) ⟨480171, by rfl⟩ : syracuseStep 5121829 = 960343) (by norm_num)
theorem B2131753 : Blo 1684042 2131753 := bbase (se 2 (by rfl) ⟨799407, by rfl⟩ : syracuseStep 2131753 = 1598815) (by norm_num)
theorem B2844517 : Blo 1684042 2844517 := bbase (se 4 (by rfl) ⟨266673, by rfl⟩ : syracuseStep 2844517 = 533347) (by norm_num)
theorem B2131849 : Blo 1684042 2131849 := bbase (se 2 (by rfl) ⟨799443, by rfl⟩ : syracuseStep 2131849 = 1598887) (by norm_num)
theorem B2844605 : Blo 1684042 2844605 := bbase (se 3 (by rfl) ⟨533363, by rfl⟩ : syracuseStep 2844605 = 1066727) (by norm_num)
theorem B1779737 : Blo 1684042 1779737 := bbase (se 2 (by rfl) ⟨667401, by rfl⟩ : syracuseStep 1779737 = 1334803) (by norm_num)
theorem B5687333 : Blo 1684042 5687333 := bbase (se 4 (by rfl) ⟨533187, by rfl⟩ : syracuseStep 5687333 = 1066375) (by norm_num)
theorem B2132021 : Blo 1684042 2132021 := bbase (se 5 (by rfl) ⟨99938, by rfl⟩ : syracuseStep 2132021 = 199877) (by norm_num)
theorem B2844733 : Blo 1684042 2844733 := bbase (se 3 (by rfl) ⟨533387, by rfl⟩ : syracuseStep 2844733 = 1066775) (by norm_num)
theorem B2132077 : Blo 1684042 2132077 := bbase (se 3 (by rfl) ⟨399764, by rfl⟩ : syracuseStep 2132077 = 799529) (by norm_num)
theorem B14993525 : Blo 1684042 14993525 := bbase (se 5 (by rfl) ⟨702821, by rfl⟩ : syracuseStep 14993525 = 1405643) (by norm_num)
theorem B1894549 : Blo 1684042 1894549 := bbase (se 6 (by rfl) ⟨44403, by rfl⟩ : syracuseStep 1894549 = 88807) (by norm_num)
theorem B2844821 : Blo 1684042 2844821 := bbase (se 6 (by rfl) ⟨66675, by rfl⟩ : syracuseStep 2844821 = 133351) (by norm_num)
theorem B1894585 : Blo 1684042 1894585 := bbase (se 2 (by rfl) ⟨710469, by rfl⟩ : syracuseStep 1894585 = 1420939) (by norm_num)
theorem B2132173 : Blo 1684042 2132173 := bbase (se 3 (by rfl) ⟨399782, by rfl⟩ : syracuseStep 2132173 = 799565) (by norm_num)
theorem B1894621 : Blo 1684042 1894621 := bbase (se 3 (by rfl) ⟨355241, by rfl⟩ : syracuseStep 1894621 = 710483) (by norm_num)
theorem B1894657 : Blo 1684042 1894657 := bbase (se 2 (by rfl) ⟨710496, by rfl⟩ : syracuseStep 1894657 = 1420993) (by norm_num)
theorem B2844949 : Blo 1684042 2844949 := bbase (se 6 (by rfl) ⟨66678, by rfl⟩ : syracuseStep 2844949 = 133357) (by norm_num)
theorem B1894693 : Blo 1684042 1894693 := bbase (se 4 (by rfl) ⟨177627, by rfl⟩ : syracuseStep 1894693 = 355255) (by norm_num)
theorem B1894729 : Blo 1684042 1894729 := bbase (se 2 (by rfl) ⟨710523, by rfl⟩ : syracuseStep 1894729 = 1421047) (by norm_num)
theorem B1894765 : Blo 1684042 1894765 := bbase (se 3 (by rfl) ⟨355268, by rfl⟩ : syracuseStep 1894765 = 710537) (by norm_num)
theorem B2845037 : Blo 1684042 2845037 := bbase (se 3 (by rfl) ⟨533444, by rfl⟩ : syracuseStep 2845037 = 1066889) (by norm_num)
theorem B2132345 : Blo 1684042 2132345 := bbase (se 2 (by rfl) ⟨799629, by rfl⟩ : syracuseStep 2132345 = 1599259) (by norm_num)
theorem B1894801 : Blo 1684042 1894801 := bbase (se 2 (by rfl) ⟨710550, by rfl⟩ : syracuseStep 1894801 = 1421101) (by norm_num)
theorem B3197333 : Blo 1684042 3197333 := bbase (se 6 (by rfl) ⟨74937, by rfl⟩ : syracuseStep 3197333 = 149875) (by norm_num)
theorem B2132401 : Blo 1684042 2132401 := bbase (se 2 (by rfl) ⟨799650, by rfl⟩ : syracuseStep 2132401 = 1599301) (by norm_num)
theorem B1894837 : Blo 1684042 1894837 := bbase (se 5 (by rfl) ⟨88820, by rfl⟩ : syracuseStep 1894837 = 177641) (by norm_num)
theorem B2697661 : Blo 1684042 2697661 := bbase (se 3 (by rfl) ⟨505811, by rfl⟩ : syracuseStep 2697661 = 1011623) (by norm_num)
theorem B8096213 : Blo 1684042 8096213 := bbase (se 7 (by rfl) ⟨94877, by rfl⟩ : syracuseStep 8096213 = 189755) (by norm_num)
theorem B5687765 : Blo 1684042 5687765 := bbase (se 7 (by rfl) ⟨66653, by rfl⟩ : syracuseStep 5687765 = 133307) (by norm_num)
theorem B1894873 : Blo 1684042 1894873 := bbase (se 2 (by rfl) ⟨710577, by rfl⟩ : syracuseStep 1894873 = 1421155) (by norm_num)
theorem B2845165 : Blo 1684042 2845165 := bbase (se 3 (by rfl) ⟨533468, by rfl⟩ : syracuseStep 2845165 = 1066937) (by norm_num)
theorem B6072821 : Blo 1684042 6072821 := bbase (se 5 (by rfl) ⟨284663, by rfl⟩ : syracuseStep 6072821 = 569327) (by norm_num)
theorem B2697725 : Blo 1684042 2697725 := bbase (se 3 (by rfl) ⟨505823, by rfl⟩ : syracuseStep 2697725 = 1011647) (by norm_num)
theorem B1894909 : Blo 1684042 1894909 := bbase (se 3 (by rfl) ⟨355295, by rfl⟩ : syracuseStep 1894909 = 710591) (by norm_num)
theorem B2132497 : Blo 1684042 2132497 := bbase (se 2 (by rfl) ⟨799686, by rfl⟩ : syracuseStep 2132497 = 1599373) (by norm_num)
theorem B1894945 : Blo 1684042 1894945 := bbase (se 2 (by rfl) ⟨710604, by rfl⟩ : syracuseStep 1894945 = 1421209) (by norm_num)
theorem B3197485 : Blo 1684042 3197485 := bbase (se 3 (by rfl) ⟨599528, by rfl⟩ : syracuseStep 3197485 = 1199057) (by norm_num)
theorem B1894981 : Blo 1684042 1894981 := bbase (se 4 (by rfl) ⟨177654, by rfl⟩ : syracuseStep 1894981 = 355309) (by norm_num)
theorem B1895017 : Blo 1684042 1895017 := bbase (se 2 (by rfl) ⟨710631, by rfl⟩ : syracuseStep 1895017 = 1421263) (by norm_num)
theorem B2697853 : Blo 1684042 2697853 := bbase (se 3 (by rfl) ⟨505847, by rfl⟩ : syracuseStep 2697853 = 1011695) (by norm_num)
theorem B1895053 : Blo 1684042 1895053 := bbase (se 3 (by rfl) ⟨355322, by rfl⟩ : syracuseStep 1895053 = 710645) (by norm_num)
theorem B1895089 : Blo 1684042 1895089 := bbase (se 2 (by rfl) ⟨710658, by rfl⟩ : syracuseStep 1895089 = 1421317) (by norm_num)
theorem B2132669 : Blo 1684042 2132669 := bbase (se 3 (by rfl) ⟨399875, by rfl⟩ : syracuseStep 2132669 = 799751) (by norm_num)
theorem B1895125 : Blo 1684042 1895125 := bbase (se 7 (by rfl) ⟨22208, by rfl⟩ : syracuseStep 1895125 = 44417) (by norm_num)
theorem B9857749 : Blo 1684042 9857749 := bbase (se 7 (by rfl) ⟨115520, by rfl⟩ : syracuseStep 9857749 = 231041) (by norm_num)
theorem B6400741 : Blo 1684042 6400741 := bbase (se 4 (by rfl) ⟨600069, by rfl⟩ : syracuseStep 6400741 = 1200139) (by norm_num)
theorem B2132725 : Blo 1684042 2132725 := bbase (se 5 (by rfl) ⟨99971, by rfl⟩ : syracuseStep 2132725 = 199943) (by norm_num)
theorem B1895161 : Blo 1684042 1895161 := bbase (se 2 (by rfl) ⟨710685, by rfl⟩ : syracuseStep 1895161 = 1421371) (by norm_num)
theorem B1895197 : Blo 1684042 1895197 := bbase (se 3 (by rfl) ⟨355349, by rfl⟩ : syracuseStep 1895197 = 710699) (by norm_num)
theorem B1895233 : Blo 1684042 1895233 := bbase (se 2 (by rfl) ⟨710712, by rfl⟩ : syracuseStep 1895233 = 1421425) (by norm_num)
theorem B8530757 : Blo 1684042 8530757 := bbase (se 4 (by rfl) ⟨799758, by rfl⟩ : syracuseStep 8530757 = 1599517) (by norm_num)
theorem B2132821 : Blo 1684042 2132821 := bbase (se 9 (by rfl) ⟨6248, by rfl⟩ : syracuseStep 2132821 = 12497) (by norm_num)
theorem B3197789 : Blo 1684042 3197789 := bbase (se 3 (by rfl) ⟨599585, by rfl⟩ : syracuseStep 3197789 = 1199171) (by norm_num)
theorem B1895269 : Blo 1684042 1895269 := bbase (se 4 (by rfl) ⟨177681, by rfl⟩ : syracuseStep 1895269 = 355363) (by norm_num)
theorem B2526077 : Blo 1684042 2526077 := bbase (se 3 (by rfl) ⟨473639, by rfl⟩ : syracuseStep 2526077 = 947279) (by norm_num)
theorem B5688197 : Blo 1684042 5688197 := bbase (se 4 (by rfl) ⟨533268, by rfl⟩ : syracuseStep 5688197 = 1066537) (by norm_num)
theorem B1895305 : Blo 1684042 1895305 := bbase (se 2 (by rfl) ⟨710739, by rfl⟩ : syracuseStep 1895305 = 1421479) (by norm_num)
theorem B2050957 : Blo 1684042 2050957 := bbase (se 3 (by rfl) ⟨384554, by rfl⟩ : syracuseStep 2050957 = 769109) (by norm_num)
theorem B2526101 : Blo 1684042 2526101 := bbase (se 6 (by rfl) ⟨59205, by rfl⟩ : syracuseStep 2526101 = 118411) (by norm_num)
theorem B1895341 : Blo 1684042 1895341 := bbase (se 3 (by rfl) ⟨355376, by rfl⟩ : syracuseStep 1895341 = 710753) (by norm_num)
theorem B2526125 : Blo 1684042 2526125 := bbase (se 3 (by rfl) ⟨473648, by rfl⟩ : syracuseStep 2526125 = 947297) (by norm_num)
theorem B2526149 : Blo 1684042 2526149 := bbase (se 4 (by rfl) ⟨236826, by rfl⟩ : syracuseStep 2526149 = 473653) (by norm_num)
theorem B1895377 : Blo 1684042 1895377 := bbase (se 2 (by rfl) ⟨710766, by rfl⟩ : syracuseStep 1895377 = 1421533) (by norm_num)
theorem B2526173 : Blo 1684042 2526173 := bbase (se 3 (by rfl) ⟨473657, by rfl⟩ : syracuseStep 2526173 = 947315) (by norm_num)
theorem B2526197 : Blo 1684042 2526197 := bbase (se 5 (by rfl) ⟨118415, by rfl⟩ : syracuseStep 2526197 = 236831) (by norm_num)
theorem B1895413 : Blo 1684042 1895413 := bbase (se 5 (by rfl) ⟨88847, by rfl⟩ : syracuseStep 1895413 = 177695) (by norm_num)
theorem B2132993 : Blo 1684042 2132993 := bbase (se 2 (by rfl) ⟨799872, by rfl⟩ : syracuseStep 2132993 = 1599745) (by norm_num)
theorem B2526221 : Blo 1684042 2526221 := bbase (se 3 (by rfl) ⟨473666, by rfl⟩ : syracuseStep 2526221 = 947333) (by norm_num)
theorem B5123093 : Blo 1684042 5123093 := bbase (se 6 (by rfl) ⟨120072, by rfl⟩ : syracuseStep 5123093 = 240145) (by norm_num)
theorem B6401045 : Blo 1684042 6401045 := bbase (se 6 (by rfl) ⟨150024, by rfl⟩ : syracuseStep 6401045 = 300049) (by norm_num)
theorem B1895449 : Blo 1684042 1895449 := bbase (se 2 (by rfl) ⟨710793, by rfl⟩ : syracuseStep 1895449 = 1421587) (by norm_num)
theorem B1707037 : Blo 1684042 1707037 := bbase (se 3 (by rfl) ⟨320069, by rfl⟩ : syracuseStep 1707037 = 640139) (by norm_num)
theorem B2526245 : Blo 1684042 2526245 := bbase (se 4 (by rfl) ⟨236835, by rfl⟩ : syracuseStep 2526245 = 473671) (by norm_num)
theorem B2133049 : Blo 1684042 2133049 := bbase (se 2 (by rfl) ⟨799893, by rfl⟩ : syracuseStep 2133049 = 1599787) (by norm_num)
theorem B2526269 : Blo 1684042 2526269 := bbase (se 3 (by rfl) ⟨473675, by rfl⟩ : syracuseStep 2526269 = 947351) (by norm_num)
theorem B1895485 : Blo 1684042 1895485 := bbase (se 3 (by rfl) ⟨355403, by rfl⟩ : syracuseStep 1895485 = 710807) (by norm_num)
theorem B4262989 : Blo 1684042 4262989 := bbase (se 3 (by rfl) ⟨799310, by rfl⟩ : syracuseStep 4262989 = 1598621) (by norm_num)
theorem B2526293 : Blo 1684042 2526293 := bbase (se 8 (by rfl) ⟨14802, by rfl⟩ : syracuseStep 2526293 = 29605) (by norm_num)
theorem B3599453 : Blo 1684042 3599453 := bbase (se 3 (by rfl) ⟨674897, by rfl⟩ : syracuseStep 3599453 = 1349795) (by norm_num)
theorem B1895521 : Blo 1684042 1895521 := bbase (se 2 (by rfl) ⟨710820, by rfl⟩ : syracuseStep 1895521 = 1421641) (by norm_num)
theorem B2526317 : Blo 1684042 2526317 := bbase (se 3 (by rfl) ⟨473684, by rfl⟩ : syracuseStep 2526317 = 947369) (by norm_num)
theorem B2526341 : Blo 1684042 2526341 := bbase (se 4 (by rfl) ⟨236844, by rfl⟩ : syracuseStep 2526341 = 473689) (by norm_num)
theorem B1895557 : Blo 1684042 1895557 := bbase (se 4 (by rfl) ⟨177708, by rfl⟩ : syracuseStep 1895557 = 355417) (by norm_num)
theorem B2133145 : Blo 1684042 2133145 := bbase (se 2 (by rfl) ⟨799929, by rfl⟩ : syracuseStep 2133145 = 1599859) (by norm_num)
theorem B2526365 : Blo 1684042 2526365 := bbase (se 3 (by rfl) ⟨473693, by rfl⟩ : syracuseStep 2526365 = 947387) (by norm_num)
theorem B4050085 : Blo 1684042 4050085 := bbase (se 4 (by rfl) ⟨379695, by rfl⟩ : syracuseStep 4050085 = 759391) (by norm_num)
theorem B1895593 : Blo 1684042 1895593 := bbase (se 2 (by rfl) ⟨710847, by rfl⟩ : syracuseStep 1895593 = 1421695) (by norm_num)
theorem B2526389 : Blo 1684042 2526389 := bbase (se 5 (by rfl) ⟨118424, by rfl⟩ : syracuseStep 2526389 = 236849) (by norm_num)
theorem B4263101 : Blo 1684042 4263101 := bbase (se 3 (by rfl) ⟨799331, by rfl⟩ : syracuseStep 4263101 = 1598663) (by norm_num)
theorem B2526413 : Blo 1684042 2526413 := bbase (se 3 (by rfl) ⟨473702, by rfl⟩ : syracuseStep 2526413 = 947405) (by norm_num)
theorem B1895629 : Blo 1684042 1895629 := bbase (se 3 (by rfl) ⟨355430, by rfl⟩ : syracuseStep 1895629 = 710861) (by norm_num)
theorem B36457685 : Blo 1684042 36457685 := bbase (se 7 (by rfl) ⟨427238, by rfl⟩ : syracuseStep 36457685 = 854477) (by norm_num)
theorem B2526437 : Blo 1684042 2526437 := bbase (se 4 (by rfl) ⟨236853, by rfl⟩ : syracuseStep 2526437 = 473707) (by norm_num)
theorem B3599597 : Blo 1684042 3599597 := bbase (se 3 (by rfl) ⟨674924, by rfl⟩ : syracuseStep 3599597 = 1349849) (by norm_num)
theorem B1895665 : Blo 1684042 1895665 := bbase (se 2 (by rfl) ⟨710874, by rfl⟩ : syracuseStep 1895665 = 1421749) (by norm_num)
theorem B2526461 : Blo 1684042 2526461 := bbase (se 3 (by rfl) ⟨473711, by rfl⟩ : syracuseStep 2526461 = 947423) (by norm_num)
theorem B2526485 : Blo 1684042 2526485 := bbase (se 6 (by rfl) ⟨59214, by rfl⟩ : syracuseStep 2526485 = 118429) (by norm_num)
theorem B1895701 : Blo 1684042 1895701 := bbase (se 6 (by rfl) ⟨44430, by rfl⟩ : syracuseStep 1895701 = 88861) (by norm_num)
theorem B2526509 : Blo 1684042 2526509 := bbase (se 3 (by rfl) ⟨473720, by rfl⟩ : syracuseStep 2526509 = 947441) (by norm_num)
theorem B5688629 : Blo 1684042 5688629 := bbase (se 5 (by rfl) ⟨266654, by rfl⟩ : syracuseStep 5688629 = 533309) (by norm_num)
theorem B1895737 : Blo 1684042 1895737 := bbase (se 2 (by rfl) ⟨710901, by rfl⟩ : syracuseStep 1895737 = 1421803) (by norm_num)
theorem B2526533 : Blo 1684042 2526533 := bbase (se 4 (by rfl) ⟨236862, by rfl⟩ : syracuseStep 2526533 = 473725) (by norm_num)
theorem B2133317 : Blo 1684042 2133317 := bbase (se 4 (by rfl) ⟨199998, by rfl⟩ : syracuseStep 2133317 = 399997) (by norm_num)
theorem B2526557 : Blo 1684042 2526557 := bbase (se 3 (by rfl) ⟨473729, by rfl⟩ : syracuseStep 2526557 = 947459) (by norm_num)
theorem B1895773 : Blo 1684042 1895773 := bbase (se 3 (by rfl) ⟨355457, by rfl⟩ : syracuseStep 1895773 = 710915) (by norm_num)
theorem B2526581 : Blo 1684042 2526581 := bbase (se 5 (by rfl) ⟨118433, by rfl⟩ : syracuseStep 2526581 = 236867) (by norm_num)
theorem B4263293 : Blo 1684042 4263293 := bbase (se 3 (by rfl) ⟨799367, by rfl⟩ : syracuseStep 4263293 = 1598735) (by norm_num)
theorem B2133373 : Blo 1684042 2133373 := bbase (se 3 (by rfl) ⟨400007, by rfl⟩ : syracuseStep 2133373 = 800015) (by norm_num)
theorem B1895809 : Blo 1684042 1895809 := bbase (se 2 (by rfl) ⟨710928, by rfl⟩ : syracuseStep 1895809 = 1421857) (by norm_num)
theorem B2526605 : Blo 1684042 2526605 := bbase (se 3 (by rfl) ⟨473738, by rfl⟩ : syracuseStep 2526605 = 947477) (by norm_num)
theorem B4050317 : Blo 1684042 4050317 := bbase (se 3 (by rfl) ⟨759434, by rfl⟩ : syracuseStep 4050317 = 1518869) (by norm_num)
theorem B2526629 : Blo 1684042 2526629 := bbase (se 4 (by rfl) ⟨236871, by rfl⟩ : syracuseStep 2526629 = 473743) (by norm_num)
theorem B1895845 : Blo 1684042 1895845 := bbase (se 4 (by rfl) ⟨177735, by rfl⟩ : syracuseStep 1895845 = 355471) (by norm_num)
theorem B2526653 : Blo 1684042 2526653 := bbase (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) (by norm_num)
theorem B1895881 : Blo 1684042 1895881 := bbase (se 2 (by rfl) ⟨710955, by rfl⟩ : syracuseStep 1895881 = 1421911) (by norm_num)
theorem B6237653 : Blo 1684042 6237653 := bbase (se 7 (by rfl) ⟨73097, by rfl⟩ : syracuseStep 6237653 = 146195) (by norm_num)
theorem B2526677 : Blo 1684042 2526677 := bbase (se 7 (by rfl) ⟨29609, by rfl⟩ : syracuseStep 2526677 = 59219) (by norm_num)
theorem B14396885 : Blo 1684042 14396885 := bbase (se 7 (by rfl) ⟨168713, by rfl⟩ : syracuseStep 14396885 = 337427) (by norm_num)
theorem B2133469 : Blo 1684042 2133469 := bbase (se 3 (by rfl) ⟨400025, by rfl⟩ : syracuseStep 2133469 = 800051) (by norm_num)
theorem B2526701 : Blo 1684042 2526701 := bbase (se 3 (by rfl) ⟨473756, by rfl⟩ : syracuseStep 2526701 = 947513) (by norm_num)
theorem B1895917 : Blo 1684042 1895917 := bbase (se 3 (by rfl) ⟨355484, by rfl⟩ : syracuseStep 1895917 = 710969) (by norm_num)
theorem B7687669 : Blo 1684042 7687669 := bbase (se 5 (by rfl) ⟨360359, by rfl⟩ : syracuseStep 7687669 = 720719) (by norm_num)
theorem B2526725 : Blo 1684042 2526725 := bbase (se 4 (by rfl) ⟨236880, by rfl⟩ : syracuseStep 2526725 = 473761) (by norm_num)
theorem B1895953 : Blo 1684042 1895953 := bbase (se 2 (by rfl) ⟨710982, by rfl⟩ : syracuseStep 1895953 = 1421965) (by norm_num)
theorem B2526749 : Blo 1684042 2526749 := bbase (se 3 (by rfl) ⟨473765, by rfl⟩ : syracuseStep 2526749 = 947531) (by norm_num)
theorem B4050461 : Blo 1684042 4050461 := bbase (se 3 (by rfl) ⟨759461, by rfl⟩ : syracuseStep 4050461 = 1518923) (by norm_num)
theorem B2526773 : Blo 1684042 2526773 := bbase (se 5 (by rfl) ⟨118442, by rfl⟩ : syracuseStep 2526773 = 236885) (by norm_num)
theorem B1895989 : Blo 1684042 1895989 := bbase (se 5 (by rfl) ⟨88874, by rfl⟩ : syracuseStep 1895989 = 177749) (by norm_num)
theorem B2526797 : Blo 1684042 2526797 := bbase (se 3 (by rfl) ⟨473774, by rfl⟩ : syracuseStep 2526797 = 947549) (by norm_num)
theorem B3198541 : Blo 1684042 3198541 := bbase (se 3 (by rfl) ⟨599726, by rfl⟩ : syracuseStep 3198541 = 1199453) (by norm_num)
theorem B3599957 : Blo 1684042 3599957 := bbase (se 8 (by rfl) ⟨21093, by rfl⟩ : syracuseStep 3599957 = 42187) (by norm_num)
theorem B43789909 : Blo 1684042 43789909 := bbase (se 8 (by rfl) ⟨256581, by rfl⟩ : syracuseStep 43789909 = 513163) (by norm_num)
theorem B1896025 : Blo 1684042 1896025 := bbase (se 2 (by rfl) ⟨711009, by rfl⟩ : syracuseStep 1896025 = 1422019) (by norm_num)
theorem B2526821 : Blo 1684042 2526821 := bbase (se 4 (by rfl) ⟨236889, by rfl⟩ : syracuseStep 2526821 = 473779) (by norm_num)
theorem B2526845 : Blo 1684042 2526845 := bbase (se 3 (by rfl) ⟨473783, by rfl⟩ : syracuseStep 2526845 = 947567) (by norm_num)
theorem B1896061 : Blo 1684042 1896061 := bbase (se 3 (by rfl) ⟨355511, by rfl⟩ : syracuseStep 1896061 = 711023) (by norm_num)
theorem B2133641 : Blo 1684042 2133641 := bbase (se 2 (by rfl) ⟨800115, by rfl⟩ : syracuseStep 2133641 = 1600231) (by norm_num)
theorem B2526869 : Blo 1684042 2526869 := bbase (se 6 (by rfl) ⟨59223, by rfl⟩ : syracuseStep 2526869 = 118447) (by norm_num)
theorem B7196309 : Blo 1684042 7196309 := bbase (se 6 (by rfl) ⟨168663, by rfl⟩ : syracuseStep 7196309 = 337327) (by norm_num)
theorem B1896097 : Blo 1684042 1896097 := bbase (se 2 (by rfl) ⟨711036, by rfl⟩ : syracuseStep 1896097 = 1422073) (by norm_num)
theorem B2526893 : Blo 1684042 2526893 := bbase (se 3 (by rfl) ⟨473792, by rfl⟩ : syracuseStep 2526893 = 947585) (by norm_num)
theorem B2133697 : Blo 1684042 2133697 := bbase (se 2 (by rfl) ⟨800136, by rfl⟩ : syracuseStep 2133697 = 1600273) (by norm_num)
theorem B2526917 : Blo 1684042 2526917 := bbase (se 4 (by rfl) ⟨236898, by rfl⟩ : syracuseStep 2526917 = 473797) (by norm_num)
theorem B1896133 : Blo 1684042 1896133 := bbase (se 4 (by rfl) ⟨177762, by rfl⟩ : syracuseStep 1896133 = 355525) (by norm_num)
theorem B4263637 : Blo 1684042 4263637 := bbase (se 7 (by rfl) ⟨49964, by rfl⟩ : syracuseStep 4263637 = 99929) (by norm_num)
theorem B2526941 : Blo 1684042 2526941 := bbase (se 3 (by rfl) ⟨473801, by rfl⟩ : syracuseStep 2526941 = 947603) (by norm_num)
theorem B3198685 : Blo 1684042 3198685 := bbase (se 3 (by rfl) ⟨599753, by rfl⟩ : syracuseStep 3198685 = 1199507) (by norm_num)
theorem B5689061 : Blo 1684042 5689061 := bbase (se 4 (by rfl) ⟨533349, by rfl⟩ : syracuseStep 5689061 = 1066699) (by norm_num)
theorem B1896169 : Blo 1684042 1896169 := bbase (se 2 (by rfl) ⟨711063, by rfl⟩ : syracuseStep 1896169 = 1422127) (by norm_num)
theorem B2526965 : Blo 1684042 2526965 := bbase (se 5 (by rfl) ⟨118451, by rfl⟩ : syracuseStep 2526965 = 236903) (by norm_num)
theorem B2526989 : Blo 1684042 2526989 := bbase (se 3 (by rfl) ⟨473810, by rfl⟩ : syracuseStep 2526989 = 947621) (by norm_num)
theorem B1896205 : Blo 1684042 1896205 := bbase (se 3 (by rfl) ⟨355538, by rfl⟩ : syracuseStep 1896205 = 711077) (by norm_num)
theorem B4050701 : Blo 1684042 4050701 := bbase (se 3 (by rfl) ⟨759506, by rfl⟩ : syracuseStep 4050701 = 1519013) (by norm_num)
theorem B2133793 : Blo 1684042 2133793 := bbase (se 2 (by rfl) ⟨800172, by rfl⟩ : syracuseStep 2133793 = 1600345) (by norm_num)
theorem B2527013 : Blo 1684042 2527013 := bbase (se 4 (by rfl) ⟨236907, by rfl⟩ : syracuseStep 2527013 = 473815) (by norm_num)
theorem B6074149 : Blo 1684042 6074149 := bbase (se 4 (by rfl) ⟨569451, by rfl⟩ : syracuseStep 6074149 = 1138903) (by norm_num)
theorem B1896241 : Blo 1684042 1896241 := bbase (se 2 (by rfl) ⟨711090, by rfl⟩ : syracuseStep 1896241 = 1422181) (by norm_num)
theorem B2527037 : Blo 1684042 2527037 := bbase (se 3 (by rfl) ⟨473819, by rfl⟩ : syracuseStep 2527037 = 947639) (by norm_num)
theorem B4263749 : Blo 1684042 4263749 := bbase (se 4 (by rfl) ⟨399726, by rfl⟩ : syracuseStep 4263749 = 799453) (by norm_num)
theorem B2699077 : Blo 1684042 2699077 := bbase (se 4 (by rfl) ⟨253038, by rfl⟩ : syracuseStep 2699077 = 506077) (by norm_num)
theorem B2527061 : Blo 1684042 2527061 := bbase (se 9 (by rfl) ⟨7403, by rfl⟩ : syracuseStep 2527061 = 14807) (by norm_num)
theorem B1896277 : Blo 1684042 1896277 := bbase (se 9 (by rfl) ⟨5555, by rfl⟩ : syracuseStep 1896277 = 11111) (by norm_num)
theorem B2527085 : Blo 1684042 2527085 := bbase (se 3 (by rfl) ⟨473828, by rfl⟩ : syracuseStep 2527085 = 947657) (by norm_num)
theorem B1896313 : Blo 1684042 1896313 := bbase (se 2 (by rfl) ⟨711117, by rfl⟩ : syracuseStep 1896313 = 1422235) (by norm_num)
theorem B3198845 : Blo 1684042 3198845 := bbase (se 3 (by rfl) ⟨599783, by rfl⟩ : syracuseStep 3198845 = 1199567) (by norm_num)
theorem B2527109 : Blo 1684042 2527109 := bbase (se 4 (by rfl) ⟨236916, by rfl⟩ : syracuseStep 2527109 = 473833) (by norm_num)
theorem B2527133 : Blo 1684042 2527133 := bbase (se 3 (by rfl) ⟨473837, by rfl⟩ : syracuseStep 2527133 = 947675) (by norm_num)
theorem B1896349 : Blo 1684042 1896349 := bbase (se 3 (by rfl) ⟨355565, by rfl⟩ : syracuseStep 1896349 = 711131) (by norm_num)
theorem B1707949 : Blo 1684042 1707949 := bbase (se 3 (by rfl) ⟨320240, by rfl⟩ : syracuseStep 1707949 = 640481) (by norm_num)
theorem B2527157 : Blo 1684042 2527157 := bbase (se 5 (by rfl) ⟨118460, by rfl⟩ : syracuseStep 2527157 = 236921) (by norm_num)
theorem B7196597 : Blo 1684042 7196597 := bbase (se 5 (by rfl) ⟨337340, by rfl⟩ : syracuseStep 7196597 = 674681) (by norm_num)
theorem B1896385 : Blo 1684042 1896385 := bbase (se 2 (by rfl) ⟨711144, by rfl⟩ : syracuseStep 1896385 = 1422289) (by norm_num)
theorem B2527181 : Blo 1684042 2527181 := bbase (se 3 (by rfl) ⟨473846, by rfl⟩ : syracuseStep 2527181 = 947693) (by norm_num)
theorem B2527205 : Blo 1684042 2527205 := bbase (se 4 (by rfl) ⟨236925, by rfl⟩ : syracuseStep 2527205 = 473851) (by norm_num)
theorem B1896421 : Blo 1684042 1896421 := bbase (se 4 (by rfl) ⟨177789, by rfl⟩ : syracuseStep 1896421 = 355579) (by norm_num)
theorem B2527229 : Blo 1684042 2527229 := bbase (se 3 (by rfl) ⟨473855, by rfl⟩ : syracuseStep 2527229 = 947711) (by norm_num)
theorem B4263941 : Blo 1684042 4263941 := bbase (se 4 (by rfl) ⟨399744, by rfl⟩ : syracuseStep 4263941 = 799489) (by norm_num)
theorem B1896457 : Blo 1684042 1896457 := bbase (se 2 (by rfl) ⟨711171, by rfl⟩ : syracuseStep 1896457 = 1422343) (by norm_num)
theorem B3198989 : Blo 1684042 3198989 := bbase (se 3 (by rfl) ⟨599810, by rfl⟩ : syracuseStep 3198989 = 1199621) (by norm_num)
theorem B2527253 : Blo 1684042 2527253 := bbase (se 6 (by rfl) ⟨59232, by rfl⟩ : syracuseStep 2527253 = 118465) (by norm_num)
theorem B2527277 : Blo 1684042 2527277 := bbase (se 3 (by rfl) ⟨473864, by rfl⟩ : syracuseStep 2527277 = 947729) (by norm_num)
theorem B1896493 : Blo 1684042 1896493 := bbase (se 3 (by rfl) ⟨355592, by rfl⟩ : syracuseStep 1896493 = 711185) (by norm_num)
theorem B2527301 : Blo 1684042 2527301 := bbase (se 4 (by rfl) ⟨236934, by rfl⟩ : syracuseStep 2527301 = 473869) (by norm_num)
theorem B1896529 : Blo 1684042 1896529 := bbase (se 2 (by rfl) ⟨711198, by rfl⟩ : syracuseStep 1896529 = 1422397) (by norm_num)
theorem B8532053 : Blo 1684042 8532053 := bbase (se 8 (by rfl) ⟨49992, by rfl⟩ : syracuseStep 8532053 = 99985) (by norm_num)
theorem B2527325 : Blo 1684042 2527325 := bbase (se 3 (by rfl) ⟨473873, by rfl⟩ : syracuseStep 2527325 = 947747) (by norm_num)
theorem B2527349 : Blo 1684042 2527349 := bbase (se 5 (by rfl) ⟨118469, by rfl⟩ : syracuseStep 2527349 = 236939) (by norm_num)
theorem B1896565 : Blo 1684042 1896565 := bbase (se 5 (by rfl) ⟨88901, by rfl⟩ : syracuseStep 1896565 = 177803) (by norm_num)
theorem B2527373 : Blo 1684042 2527373 := bbase (se 3 (by rfl) ⟨473882, by rfl⟩ : syracuseStep 2527373 = 947765) (by norm_num)
theorem B5689493 : Blo 1684042 5689493 := bbase (se 6 (by rfl) ⟨133347, by rfl⟩ : syracuseStep 5689493 = 266695) (by norm_num)
theorem B1896601 : Blo 1684042 1896601 := bbase (se 2 (by rfl) ⟨711225, by rfl⟩ : syracuseStep 1896601 = 1422451) (by norm_num)
theorem B2527397 : Blo 1684042 2527397 := bbase (se 4 (by rfl) ⟨236943, by rfl⟩ : syracuseStep 2527397 = 473887) (by norm_num)
theorem B2527421 : Blo 1684042 2527421 := bbase (se 3 (by rfl) ⟨473891, by rfl⟩ : syracuseStep 2527421 = 947783) (by norm_num)
theorem B1896637 : Blo 1684042 1896637 := bbase (se 3 (by rfl) ⟨355619, by rfl⟩ : syracuseStep 1896637 = 711239) (by norm_num)
theorem B2527445 : Blo 1684042 2527445 := bbase (se 7 (by rfl) ⟨29618, by rfl⟩ : syracuseStep 2527445 = 59237) (by norm_num)
theorem B1896673 : Blo 1684042 1896673 := bbase (se 2 (by rfl) ⟨711252, by rfl⟩ : syracuseStep 1896673 = 1422505) (by norm_num)
theorem B2527469 : Blo 1684042 2527469 := bbase (se 3 (by rfl) ⟨473900, by rfl⟩ : syracuseStep 2527469 = 947801) (by norm_num)
theorem B2527493 : Blo 1684042 2527493 := bbase (se 4 (by rfl) ⟨236952, by rfl⟩ : syracuseStep 2527493 = 473905) (by norm_num)
theorem B1896709 : Blo 1684042 1896709 := bbase (se 4 (by rfl) ⟨177816, by rfl⟩ : syracuseStep 1896709 = 355633) (by norm_num)
theorem B2527517 : Blo 1684042 2527517 := bbase (se 3 (by rfl) ⟨473909, by rfl⟩ : syracuseStep 2527517 = 947819) (by norm_num)
theorem B1896745 : Blo 1684042 1896745 := bbase (se 2 (by rfl) ⟨711279, by rfl⟩ : syracuseStep 1896745 = 1422559) (by norm_num)
theorem B3199277 : Blo 1684042 3199277 := bbase (se 3 (by rfl) ⟨599864, by rfl⟩ : syracuseStep 3199277 = 1199729) (by norm_num)
theorem B2527541 : Blo 1684042 2527541 := bbase (se 5 (by rfl) ⟨118478, by rfl⟩ : syracuseStep 2527541 = 236957) (by norm_num)
theorem B3789125 : Blo 1684042 3789125 := bbase (se 4 (by rfl) ⟨355230, by rfl⟩ : syracuseStep 3789125 = 710461) (by norm_num)
theorem B2527565 : Blo 1684042 2527565 := bbase (se 3 (by rfl) ⟨473918, by rfl⟩ : syracuseStep 2527565 = 947837) (by norm_num)
theorem B1896781 : Blo 1684042 1896781 := bbase (se 3 (by rfl) ⟨355646, by rfl⟩ : syracuseStep 1896781 = 711293) (by norm_num)
theorem B4264285 : Blo 1684042 4264285 := bbase (se 3 (by rfl) ⟨799553, by rfl⟩ : syracuseStep 4264285 = 1599107) (by norm_num)
theorem B2527589 : Blo 1684042 2527589 := bbase (se 4 (by rfl) ⟨236961, by rfl⟩ : syracuseStep 2527589 = 473923) (by norm_num)
theorem B2527613 : Blo 1684042 2527613 := bbase (se 3 (by rfl) ⟨473927, by rfl⟩ : syracuseStep 2527613 = 947855) (by norm_num)
theorem B3789197 : Blo 1684042 3789197 := bbase (se 3 (by rfl) ⟨710474, by rfl⟩ : syracuseStep 3789197 = 1420949) (by norm_num)
theorem B2527637 : Blo 1684042 2527637 := bbase (se 6 (by rfl) ⟨59241, by rfl⟩ : syracuseStep 2527637 = 118483) (by norm_num)
theorem B2527661 : Blo 1684042 2527661 := bbase (se 3 (by rfl) ⟨473936, by rfl⟩ : syracuseStep 2527661 = 947873) (by norm_num)
theorem B2527685 : Blo 1684042 2527685 := bbase (se 4 (by rfl) ⟨236970, by rfl⟩ : syracuseStep 2527685 = 473941) (by norm_num)
theorem B3199429 : Blo 1684042 3199429 := bbase (se 4 (by rfl) ⟨299946, by rfl⟩ : syracuseStep 3199429 = 599893) (by norm_num)
theorem B4264397 : Blo 1684042 4264397 := bbase (se 3 (by rfl) ⟨799574, by rfl⟩ : syracuseStep 4264397 = 1599149) (by norm_num)
theorem B3600845 : Blo 1684042 3600845 := bbase (se 3 (by rfl) ⟨675158, by rfl⟩ : syracuseStep 3600845 = 1350317) (by norm_num)
theorem B3789269 : Blo 1684042 3789269 := bbase (se 7 (by rfl) ⟨44405, by rfl⟩ : syracuseStep 3789269 = 88811) (by norm_num)
theorem B2527709 : Blo 1684042 2527709 := bbase (se 3 (by rfl) ⟨473945, by rfl⟩ : syracuseStep 2527709 = 947891) (by norm_num)
theorem B2699749 : Blo 1684042 2699749 := bbase (se 4 (by rfl) ⟨253101, by rfl⟩ : syracuseStep 2699749 = 506203) (by norm_num)
theorem B1798633 : Blo 1684042 1798633 := bbase (se 2 (by rfl) ⟨674487, by rfl⟩ : syracuseStep 1798633 = 1348975) (by norm_num)
theorem B2527733 : Blo 1684042 2527733 := bbase (se 5 (by rfl) ⟨118487, by rfl⟩ : syracuseStep 2527733 = 236975) (by norm_num)
theorem B2527757 : Blo 1684042 2527757 := bbase (se 3 (by rfl) ⟨473954, by rfl⟩ : syracuseStep 2527757 = 947909) (by norm_num)
theorem B3789341 : Blo 1684042 3789341 := bbase (se 3 (by rfl) ⟨710501, by rfl⟩ : syracuseStep 3789341 = 1421003) (by norm_num)
theorem B2527781 : Blo 1684042 2527781 := bbase (se 4 (by rfl) ⟨236979, by rfl⟩ : syracuseStep 2527781 = 473959) (by norm_num)
theorem B1798705 : Blo 1684042 1798705 := bbase (se 2 (by rfl) ⟨674514, by rfl⟩ : syracuseStep 1798705 = 1349029) (by norm_num)
theorem B2527805 : Blo 1684042 2527805 := bbase (se 3 (by rfl) ⟨473963, by rfl⟩ : syracuseStep 2527805 = 947927) (by norm_num)
theorem B5689925 : Blo 1684042 5689925 := bbase (se 4 (by rfl) ⟨533430, by rfl⟩ : syracuseStep 5689925 = 1066861) (by norm_num)
theorem B2527829 : Blo 1684042 2527829 := bbase (se 8 (by rfl) ⟨14811, by rfl⟩ : syracuseStep 2527829 = 29623) (by norm_num)
theorem B3789413 : Blo 1684042 3789413 := bbase (se 4 (by rfl) ⟨355257, by rfl⟩ : syracuseStep 3789413 = 710515) (by norm_num)
theorem B2527853 : Blo 1684042 2527853 := bbase (se 3 (by rfl) ⟨473972, by rfl⟩ : syracuseStep 2527853 = 947945) (by norm_num)
theorem B2527877 : Blo 1684042 2527877 := bbase (se 4 (by rfl) ⟨236988, by rfl⟩ : syracuseStep 2527877 = 473977) (by norm_num)
theorem B4264589 : Blo 1684042 4264589 := bbase (se 3 (by rfl) ⟨799610, by rfl⟩ : syracuseStep 4264589 = 1599221) (by norm_num)
theorem B12145301 : Blo 1684042 12145301 := bbase (se 6 (by rfl) ⟨284655, by rfl⟩ : syracuseStep 12145301 = 569311) (by norm_num)
theorem B2527901 : Blo 1684042 2527901 := bbase (se 3 (by rfl) ⟨473981, by rfl⟩ : syracuseStep 2527901 = 947963) (by norm_num)
theorem B7197349 : Blo 1684042 7197349 := bbase (se 4 (by rfl) ⟨674751, by rfl⟩ : syracuseStep 7197349 = 1349503) (by norm_num)
theorem B3789485 : Blo 1684042 3789485 := bbase (se 3 (by rfl) ⟨710528, by rfl⟩ : syracuseStep 3789485 = 1421057) (by norm_num)
theorem B11522741 : Blo 1684042 11522741 := bbase (se 5 (by rfl) ⟨540128, by rfl⟩ : syracuseStep 11522741 = 1080257) (by norm_num)
theorem B2527925 : Blo 1684042 2527925 := bbase (se 5 (by rfl) ⟨118496, by rfl⟩ : syracuseStep 2527925 = 236993) (by norm_num)
theorem B2527949 : Blo 1684042 2527949 := bbase (se 3 (by rfl) ⟨473990, by rfl⟩ : syracuseStep 2527949 = 947981) (by norm_num)
theorem B1798885 : Blo 1684042 1798885 := bbase (se 4 (by rfl) ⟨168645, by rfl⟩ : syracuseStep 1798885 = 337291) (by norm_num)
theorem B2527973 : Blo 1684042 2527973 := bbase (se 4 (by rfl) ⟨236997, by rfl⟩ : syracuseStep 2527973 = 473995) (by norm_num)
theorem B3789557 : Blo 1684042 3789557 := bbase (se 5 (by rfl) ⟨177635, by rfl⟩ : syracuseStep 3789557 = 355271) (by norm_num)
theorem B3035893 : Blo 1684042 3035893 := bbase (se 5 (by rfl) ⟨142307, by rfl⟩ : syracuseStep 3035893 = 284615) (by norm_num)
theorem B3199733 : Blo 1684042 3199733 := bbase (se 5 (by rfl) ⟨149987, by rfl⟩ : syracuseStep 3199733 = 299975) (by norm_num)
theorem B2527997 : Blo 1684042 2527997 := bbase (se 3 (by rfl) ⟨473999, by rfl⟩ : syracuseStep 2527997 = 947999) (by norm_num)
theorem B2528021 : Blo 1684042 2528021 := bbase (se 6 (by rfl) ⟨59250, by rfl⟩ : syracuseStep 2528021 = 118501) (by norm_num)
theorem B2528045 : Blo 1684042 2528045 := bbase (se 3 (by rfl) ⟨474008, by rfl⟩ : syracuseStep 2528045 = 948017) (by norm_num)
theorem B3789629 : Blo 1684042 3789629 := bbase (se 3 (by rfl) ⟨710555, by rfl⟩ : syracuseStep 3789629 = 1421111) (by norm_num)
theorem B2528069 : Blo 1684042 2528069 := bbase (se 4 (by rfl) ⟨237006, by rfl⟩ : syracuseStep 2528069 = 474013) (by norm_num)
theorem B2528093 : Blo 1684042 2528093 := bbase (se 3 (by rfl) ⟨474017, by rfl⟩ : syracuseStep 2528093 = 948035) (by norm_num)
theorem B2528117 : Blo 1684042 2528117 := bbase (se 5 (by rfl) ⟨118505, by rfl⟩ : syracuseStep 2528117 = 237011) (by norm_num)
theorem B3789701 : Blo 1684042 3789701 := bbase (se 4 (by rfl) ⟨355284, by rfl⟩ : syracuseStep 3789701 = 710569) (by norm_num)
theorem B3036037 : Blo 1684042 3036037 := bbase (se 4 (by rfl) ⟨284628, by rfl⟩ : syracuseStep 3036037 = 569257) (by norm_num)
theorem B2528141 : Blo 1684042 2528141 := bbase (se 3 (by rfl) ⟨474026, by rfl⟩ : syracuseStep 2528141 = 948053) (by norm_num)
theorem B2528165 : Blo 1684042 2528165 := bbase (se 4 (by rfl) ⟨237015, by rfl⟩ : syracuseStep 2528165 = 474031) (by norm_num)
theorem B2528189 : Blo 1684042 2528189 := bbase (se 3 (by rfl) ⟨474035, by rfl⟩ : syracuseStep 2528189 = 948071) (by norm_num)
theorem B3789773 : Blo 1684042 3789773 := bbase (se 3 (by rfl) ⟨710582, by rfl⟩ : syracuseStep 3789773 = 1421165) (by norm_num)
theorem B2528213 : Blo 1684042 2528213 := bbase (se 7 (by rfl) ⟨29627, by rfl⟩ : syracuseStep 2528213 = 59255) (by norm_num)
theorem B4797413 : Blo 1684042 4797413 := bbase (se 4 (by rfl) ⟨449757, by rfl⟩ : syracuseStep 4797413 = 899515) (by norm_num)
theorem B4264933 : Blo 1684042 4264933 := bbase (se 4 (by rfl) ⟨399837, by rfl⟩ : syracuseStep 4264933 = 799675) (by norm_num)
theorem B2528237 : Blo 1684042 2528237 := bbase (se 3 (by rfl) ⟨474044, by rfl⟩ : syracuseStep 2528237 = 948089) (by norm_num)
theorem B5690357 : Blo 1684042 5690357 := bbase (se 5 (by rfl) ⟨266735, by rfl⟩ : syracuseStep 5690357 = 533471) (by norm_num)
theorem B2528261 : Blo 1684042 2528261 := bbase (se 4 (by rfl) ⟨237024, by rfl⟩ : syracuseStep 2528261 = 474049) (by norm_num)
theorem B3789845 : Blo 1684042 3789845 := bbase (se 6 (by rfl) ⟨88824, by rfl⟩ : syracuseStep 3789845 = 177649) (by norm_num)
theorem B2528285 : Blo 1684042 2528285 := bbase (se 3 (by rfl) ⟨474053, by rfl⟩ : syracuseStep 2528285 = 948107) (by norm_num)
theorem B2528309 : Blo 1684042 2528309 := bbase (se 5 (by rfl) ⟨118514, by rfl⟩ : syracuseStep 2528309 = 237029) (by norm_num)
theorem B2528333 : Blo 1684042 2528333 := bbase (se 3 (by rfl) ⟨474062, by rfl⟩ : syracuseStep 2528333 = 948125) (by norm_num)
theorem B4265045 : Blo 1684042 4265045 := bbase (se 8 (by rfl) ⟨24990, by rfl⟩ : syracuseStep 4265045 = 49981) (by norm_num)
theorem B3789917 : Blo 1684042 3789917 := bbase (se 3 (by rfl) ⟨710609, by rfl⟩ : syracuseStep 3789917 = 1421219) (by norm_num)
theorem B2528357 : Blo 1684042 2528357 := bbase (se 4 (by rfl) ⟨237033, by rfl⟩ : syracuseStep 2528357 = 474067) (by norm_num)
theorem B2528381 : Blo 1684042 2528381 := bbase (se 3 (by rfl) ⟨474071, by rfl⟩ : syracuseStep 2528381 = 948143) (by norm_num)
theorem B2528405 : Blo 1684042 2528405 := bbase (se 6 (by rfl) ⟨59259, by rfl⟩ : syracuseStep 2528405 = 118519) (by norm_num)
theorem B1799329 : Blo 1684042 1799329 := bbase (se 2 (by rfl) ⟨674748, by rfl⟩ : syracuseStep 1799329 = 1349497) (by norm_num)
theorem B3789989 : Blo 1684042 3789989 := bbase (se 4 (by rfl) ⟨355311, by rfl⟩ : syracuseStep 3789989 = 710623) (by norm_num)
theorem B2528429 : Blo 1684042 2528429 := bbase (se 3 (by rfl) ⟨474080, by rfl⟩ : syracuseStep 2528429 = 948161) (by norm_num)
theorem B2528453 : Blo 1684042 2528453 := bbase (se 4 (by rfl) ⟨237042, by rfl⟩ : syracuseStep 2528453 = 474085) (by norm_num)
theorem B6075589 : Blo 1684042 6075589 := bbase (se 4 (by rfl) ⟨569586, by rfl⟩ : syracuseStep 6075589 = 1139173) (by norm_num)
theorem B2561237 : Blo 1684042 2561237 := bbase (se 7 (by rfl) ⟨30014, by rfl⟩ : syracuseStep 2561237 = 60029) (by norm_num)
theorem B2528477 : Blo 1684042 2528477 := bbase (se 3 (by rfl) ⟨474089, by rfl⟩ : syracuseStep 2528477 = 948179) (by norm_num)
theorem B3790061 : Blo 1684042 3790061 := bbase (se 3 (by rfl) ⟨710636, by rfl⟩ : syracuseStep 3790061 = 1421273) (by norm_num)
theorem B2528501 : Blo 1684042 2528501 := bbase (se 5 (by rfl) ⟨118523, by rfl⟩ : syracuseStep 2528501 = 237047) (by norm_num)
theorem B2528525 : Blo 1684042 2528525 := bbase (se 3 (by rfl) ⟨474098, by rfl⟩ : syracuseStep 2528525 = 948197) (by norm_num)
theorem B4265237 : Blo 1684042 4265237 := bbase (se 6 (by rfl) ⟨99966, by rfl⟩ : syracuseStep 4265237 = 199933) (by norm_num)
theorem B1799453 : Blo 1684042 1799453 := bbase (se 3 (by rfl) ⟨337397, by rfl⟩ : syracuseStep 1799453 = 674795) (by norm_num)
theorem B2528549 : Blo 1684042 2528549 := bbase (se 4 (by rfl) ⟨237051, by rfl⟩ : syracuseStep 2528549 = 474103) (by norm_num)
theorem B3790133 : Blo 1684042 3790133 := bbase (se 5 (by rfl) ⟨177662, by rfl⟩ : syracuseStep 3790133 = 355325) (by norm_num)
theorem B3036469 : Blo 1684042 3036469 := bbase (se 5 (by rfl) ⟨142334, by rfl⟩ : syracuseStep 3036469 = 284669) (by norm_num)
theorem B2528573 : Blo 1684042 2528573 := bbase (se 3 (by rfl) ⟨474107, by rfl⟩ : syracuseStep 2528573 = 948215) (by norm_num)
theorem B2528597 : Blo 1684042 2528597 := bbase (se 14 (by rfl) ⟨231, by rfl⟩ : syracuseStep 2528597 = 463) (by norm_num)
theorem B8533349 : Blo 1684042 8533349 := bbase (se 4 (by rfl) ⟨800001, by rfl⟩ : syracuseStep 8533349 = 1600003) (by norm_num)
theorem B2880877 : Blo 1684042 2880877 := bbase (se 3 (by rfl) ⟨540164, by rfl⟩ : syracuseStep 2880877 = 1080329) (by norm_num)
theorem B2528621 : Blo 1684042 2528621 := bbase (se 3 (by rfl) ⟨474116, by rfl⟩ : syracuseStep 2528621 = 948233) (by norm_num)
theorem B3790205 : Blo 1684042 3790205 := bbase (se 3 (by rfl) ⟨710663, by rfl⟩ : syracuseStep 3790205 = 1421327) (by norm_num)
theorem B7198085 : Blo 1684042 7198085 := bbase (se 4 (by rfl) ⟨674820, by rfl⟩ : syracuseStep 7198085 = 1349641) (by norm_num)
theorem B2528645 : Blo 1684042 2528645 := bbase (se 4 (by rfl) ⟨237060, by rfl⟩ : syracuseStep 2528645 = 474121) (by norm_num)
theorem B2528669 : Blo 1684042 2528669 := bbase (se 3 (by rfl) ⟨474125, by rfl⟩ : syracuseStep 2528669 = 948251) (by norm_num)
theorem B2528693 : Blo 1684042 2528693 := bbase (se 5 (by rfl) ⟨118532, by rfl⟩ : syracuseStep 2528693 = 237065) (by norm_num)
theorem B3790277 : Blo 1684042 3790277 := bbase (se 4 (by rfl) ⟨355338, by rfl⟩ : syracuseStep 3790277 = 710677) (by norm_num)
theorem B2528717 : Blo 1684042 2528717 := bbase (se 3 (by rfl) ⟨474134, by rfl⟩ : syracuseStep 2528717 = 948269) (by norm_num)
theorem B5125589 : Blo 1684042 5125589 := bbase (se 7 (by rfl) ⟨60065, by rfl⟩ : syracuseStep 5125589 = 120131) (by norm_num)
theorem B2528741 : Blo 1684042 2528741 := bbase (se 4 (by rfl) ⟨237069, by rfl⟩ : syracuseStep 2528741 = 474139) (by norm_num)
theorem B3200485 : Blo 1684042 3200485 := bbase (se 4 (by rfl) ⟨300045, by rfl⟩ : syracuseStep 3200485 = 600091) (by norm_num)
theorem B6395381 : Blo 1684042 6395381 := bbase (se 5 (by rfl) ⟨299783, by rfl⟩ : syracuseStep 6395381 = 599567) (by norm_num)
theorem B10794485 : Blo 1684042 10794485 := bbase (se 5 (by rfl) ⟨505991, by rfl⟩ : syracuseStep 10794485 = 1011983) (by norm_num)
theorem B2528765 : Blo 1684042 2528765 := bbase (se 3 (by rfl) ⟨474143, by rfl⟩ : syracuseStep 2528765 = 948287) (by norm_num)
theorem B3790349 : Blo 1684042 3790349 := bbase (se 3 (by rfl) ⟨710690, by rfl⟩ : syracuseStep 3790349 = 1421381) (by norm_num)
theorem B6829589 : Blo 1684042 6829589 := bbase (se 6 (by rfl) ⟨160068, by rfl⟩ : syracuseStep 6829589 = 320137) (by norm_num)
theorem B2528789 : Blo 1684042 2528789 := bbase (se 6 (by rfl) ⟨59268, by rfl⟩ : syracuseStep 2528789 = 118537) (by norm_num)
theorem B1799705 : Blo 1684042 1799705 := bbase (se 2 (by rfl) ⟨674889, by rfl⟩ : syracuseStep 1799705 = 1349779) (by norm_num)
theorem B2528813 : Blo 1684042 2528813 := bbase (se 3 (by rfl) ⟨474152, by rfl⟩ : syracuseStep 2528813 = 948305) (by norm_num)
theorem B9229877 : Blo 1684042 9229877 := bbase (se 5 (by rfl) ⟨432650, by rfl⟩ : syracuseStep 9229877 = 865301) (by norm_num)
theorem B2528837 : Blo 1684042 2528837 := bbase (se 4 (by rfl) ⟨237078, by rfl⟩ : syracuseStep 2528837 = 474157) (by norm_num)
theorem B1922629 : Blo 1684042 1922629 := bbase (se 4 (by rfl) ⟨180246, by rfl⟩ : syracuseStep 1922629 = 360493) (by norm_num)
theorem B3790421 : Blo 1684042 3790421 := bbase (se 8 (by rfl) ⟨22209, by rfl⟩ : syracuseStep 3790421 = 44419) (by norm_num)
theorem B36435541 : Blo 1684042 36435541 := bbase (se 8 (by rfl) ⟨213489, by rfl⟩ : syracuseStep 36435541 = 426979) (by norm_num)
theorem B3036757 : Blo 1684042 3036757 := bbase (se 8 (by rfl) ⟨17793, by rfl⟩ : syracuseStep 3036757 = 35587) (by norm_num)
theorem B2528861 : Blo 1684042 2528861 := bbase (se 3 (by rfl) ⟨474161, by rfl⟩ : syracuseStep 2528861 = 948323) (by norm_num)
theorem B4265581 : Blo 1684042 4265581 := bbase (se 3 (by rfl) ⟨799796, by rfl⟩ : syracuseStep 4265581 = 1599593) (by norm_num)
theorem B2528885 : Blo 1684042 2528885 := bbase (se 5 (by rfl) ⟨118541, by rfl⟩ : syracuseStep 2528885 = 237083) (by norm_num)
theorem B3200629 : Blo 1684042 3200629 := bbase (se 5 (by rfl) ⟨150029, by rfl⟩ : syracuseStep 3200629 = 300059) (by norm_num)
theorem B2528909 : Blo 1684042 2528909 := bbase (se 3 (by rfl) ⟨474170, by rfl⟩ : syracuseStep 2528909 = 948341) (by norm_num)
theorem B1947289 : Blo 1684042 1947289 := bbase (se 2 (by rfl) ⟨730233, by rfl⟩ : syracuseStep 1947289 = 1460467) (by norm_num)
theorem B3790493 : Blo 1684042 3790493 := bbase (se 3 (by rfl) ⟨710717, by rfl⟩ : syracuseStep 3790493 = 1421435) (by norm_num)
theorem B2528933 : Blo 1684042 2528933 := bbase (se 4 (by rfl) ⟨237087, by rfl⟩ : syracuseStep 2528933 = 474175) (by norm_num)
theorem B2528957 : Blo 1684042 2528957 := bbase (se 3 (by rfl) ⟨474179, by rfl⟩ : syracuseStep 2528957 = 948359) (by norm_num)
theorem B2528981 : Blo 1684042 2528981 := bbase (se 7 (by rfl) ⟨29636, by rfl⟩ : syracuseStep 2528981 = 59273) (by norm_num)
theorem B4265693 : Blo 1684042 4265693 := bbase (se 3 (by rfl) ⟨799817, by rfl⟩ : syracuseStep 4265693 = 1599635) (by norm_num)
theorem B3790565 : Blo 1684042 3790565 := bbase (se 4 (by rfl) ⟨355365, by rfl⟩ : syracuseStep 3790565 = 710731) (by norm_num)
theorem B2529005 : Blo 1684042 2529005 := bbase (se 3 (by rfl) ⟨474188, by rfl⟩ : syracuseStep 2529005 = 948377) (by norm_num)
theorem B8525573 : Blo 1684042 8525573 := bbase (se 4 (by rfl) ⟨799272, by rfl⟩ : syracuseStep 8525573 = 1598545) (by norm_num)
theorem B2529029 : Blo 1684042 2529029 := bbase (se 4 (by rfl) ⟨237096, by rfl⟩ : syracuseStep 2529029 = 474193) (by norm_num)
theorem B6395669 : Blo 1684042 6395669 := bbase (se 6 (by rfl) ⟨149898, by rfl⟩ : syracuseStep 6395669 = 299797) (by norm_num)
theorem B3200789 : Blo 1684042 3200789 := bbase (se 6 (by rfl) ⟨75018, by rfl⟩ : syracuseStep 3200789 = 150037) (by norm_num)
theorem B2529053 : Blo 1684042 2529053 := bbase (se 3 (by rfl) ⟨474197, by rfl⟩ : syracuseStep 2529053 = 948395) (by norm_num)
theorem B3790637 : Blo 1684042 3790637 := bbase (se 3 (by rfl) ⟨710744, by rfl⟩ : syracuseStep 3790637 = 1421489) (by norm_num)
theorem B3790709 : Blo 1684042 3790709 := bbase (se 5 (by rfl) ⟨177689, by rfl⟩ : syracuseStep 3790709 = 355379) (by norm_num)
theorem B4265885 : Blo 1684042 4265885 := bbase (se 3 (by rfl) ⟨799853, by rfl⟩ : syracuseStep 4265885 = 1599707) (by norm_num)
theorem B3790781 : Blo 1684042 3790781 := bbase (se 3 (by rfl) ⟨710771, by rfl⟩ : syracuseStep 3790781 = 1421543) (by norm_num)
theorem B1800149 : Blo 1684042 1800149 := bbase (se 7 (by rfl) ⟨21095, by rfl⟩ : syracuseStep 1800149 = 42191) (by norm_num)
theorem B2398205 : Blo 1684042 2398205 := bbase (se 3 (by rfl) ⟨449663, by rfl⟩ : syracuseStep 2398205 = 899327) (by norm_num)
theorem B3790853 : Blo 1684042 3790853 := bbase (se 4 (by rfl) ⟨355392, by rfl⟩ : syracuseStep 3790853 = 710785) (by norm_num)
theorem B6486085 : Blo 1684042 6486085 := bbase (se 4 (by rfl) ⟨608070, by rfl⟩ : syracuseStep 6486085 = 1216141) (by norm_num)
theorem B2398285 : Blo 1684042 2398285 := bbase (se 3 (by rfl) ⟨449678, by rfl⟩ : syracuseStep 2398285 = 899357) (by norm_num)
theorem B3790925 : Blo 1684042 3790925 := bbase (se 3 (by rfl) ⟨710798, by rfl⟩ : syracuseStep 3790925 = 1421597) (by norm_num)
theorem B3037277 : Blo 1684042 3037277 := bbase (se 3 (by rfl) ⟨569489, by rfl⟩ : syracuseStep 3037277 = 1138979) (by norm_num)
theorem B2922589 : Blo 1684042 2922589 := bbase (se 3 (by rfl) ⟨547985, by rfl⟩ : syracuseStep 2922589 = 1095971) (by norm_num)
theorem B4798597 : Blo 1684042 4798597 := bbase (se 4 (by rfl) ⟨449868, by rfl⟩ : syracuseStep 4798597 = 899737) (by norm_num)
theorem B3790997 : Blo 1684042 3790997 := bbase (se 6 (by rfl) ⟨88851, by rfl⟩ : syracuseStep 3790997 = 177703) (by norm_num)
theorem B2398405 : Blo 1684042 2398405 := bbase (se 4 (by rfl) ⟨224850, by rfl⟩ : syracuseStep 2398405 = 449701) (by norm_num)
theorem B1800397 : Blo 1684042 1800397 := bbase (se 3 (by rfl) ⟨337574, by rfl⟩ : syracuseStep 1800397 = 675149) (by norm_num)
theorem B3791069 : Blo 1684042 3791069 := bbase (se 3 (by rfl) ⟨710825, by rfl⟩ : syracuseStep 3791069 = 1421651) (by norm_num)
theorem B3037421 : Blo 1684042 3037421 := bbase (se 3 (by rfl) ⟨569516, by rfl⟩ : syracuseStep 3037421 = 1139033) (by norm_num)
theorem B4266229 : Blo 1684042 4266229 := bbase (se 5 (by rfl) ⟨199979, by rfl⟩ : syracuseStep 4266229 = 399959) (by norm_num)
theorem B2398501 : Blo 1684042 2398501 := bbase (se 4 (by rfl) ⟨224859, by rfl⟩ : syracuseStep 2398501 = 449719) (by norm_num)
theorem B2881829 : Blo 1684042 2881829 := bbase (se 4 (by rfl) ⟨270171, by rfl⟩ : syracuseStep 2881829 = 540343) (by norm_num)
theorem B3791141 : Blo 1684042 3791141 := bbase (se 4 (by rfl) ⟨355419, by rfl⟩ : syracuseStep 3791141 = 710839) (by norm_num)
theorem B4798757 : Blo 1684042 4798757 := bbase (se 4 (by rfl) ⟨449883, by rfl⟩ : syracuseStep 4798757 = 899767) (by norm_num)
theorem B4266341 : Blo 1684042 4266341 := bbase (se 4 (by rfl) ⟨399969, by rfl⟩ : syracuseStep 4266341 = 799939) (by norm_num)
theorem B3791213 : Blo 1684042 3791213 := bbase (se 3 (by rfl) ⟨710852, by rfl⟩ : syracuseStep 3791213 = 1421705) (by norm_num)
theorem B9599381 : Blo 1684042 9599381 := bbase (se 6 (by rfl) ⟨224985, by rfl⟩ : syracuseStep 9599381 = 449971) (by norm_num)
theorem B3791285 : Blo 1684042 3791285 := bbase (se 5 (by rfl) ⟨177716, by rfl⟩ : syracuseStep 3791285 = 355433) (by norm_num)
theorem B3037637 : Blo 1684042 3037637 := bbase (se 4 (by rfl) ⟨284778, by rfl⟩ : syracuseStep 3037637 = 569557) (by norm_num)
theorem B5126597 : Blo 1684042 5126597 := bbase (se 4 (by rfl) ⟨480618, by rfl⟩ : syracuseStep 5126597 = 961237) (by norm_num)
theorem B3791357 : Blo 1684042 3791357 := bbase (se 3 (by rfl) ⟨710879, by rfl⟩ : syracuseStep 3791357 = 1421759) (by norm_num)
theorem B3037709 : Blo 1684042 3037709 := bbase (se 3 (by rfl) ⟨569570, by rfl⟩ : syracuseStep 3037709 = 1139141) (by norm_num)
theorem B9591317 : Blo 1684042 9591317 := bbase (se 6 (by rfl) ⟨224796, by rfl⟩ : syracuseStep 9591317 = 449593) (by norm_num)
theorem B4798997 : Blo 1684042 4798997 := bbase (se 6 (by rfl) ⟨112476, by rfl⟩ : syracuseStep 4798997 = 224953) (by norm_num)
theorem B5765669 : Blo 1684042 5765669 := bbase (se 4 (by rfl) ⟨540531, by rfl⟩ : syracuseStep 5765669 = 1081063) (by norm_num)
theorem B4266533 : Blo 1684042 4266533 := bbase (se 4 (by rfl) ⟨399987, by rfl⟩ : syracuseStep 4266533 = 799975) (by norm_num)
theorem B4381253 : Blo 1684042 4381253 := bbase (se 4 (by rfl) ⟨410742, by rfl⟩ : syracuseStep 4381253 = 821485) (by norm_num)
theorem B3791429 : Blo 1684042 3791429 := bbase (se 4 (by rfl) ⟨355446, by rfl⟩ : syracuseStep 3791429 = 710893) (by norm_num)
theorem B12147317 : Blo 1684042 12147317 := bbase (se 5 (by rfl) ⟨569405, by rfl⟩ : syracuseStep 12147317 = 1138811) (by norm_num)
theorem B3078773 : Blo 1684042 3078773 := bbase (se 5 (by rfl) ⟨144317, by rfl⟩ : syracuseStep 3078773 = 288635) (by norm_num)
theorem B8534645 : Blo 1684042 8534645 := bbase (se 5 (by rfl) ⟨400061, by rfl⟩ : syracuseStep 8534645 = 800123) (by norm_num)
theorem B3791501 : Blo 1684042 3791501 := bbase (se 3 (by rfl) ⟨710906, by rfl⟩ : syracuseStep 3791501 = 1421813) (by norm_num)
theorem B5683877 : Blo 1684042 5683877 := bbase (se 4 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 5683877 = 1065727) (by norm_num)
theorem B3791573 : Blo 1684042 3791573 := bbase (se 7 (by rfl) ⟨44432, by rfl⟩ : syracuseStep 3791573 = 88865) (by norm_num)
theorem B4799189 : Blo 1684042 4799189 := bbase (se 7 (by rfl) ⟨56240, by rfl⟩ : syracuseStep 4799189 = 112481) (by norm_num)
theorem B2398997 : Blo 1684042 2398997 := bbase (se 6 (by rfl) ⟨56226, by rfl⟩ : syracuseStep 2398997 = 112453) (by norm_num)
theorem B3791645 : Blo 1684042 3791645 := bbase (se 3 (by rfl) ⟨710933, by rfl⟩ : syracuseStep 3791645 = 1421867) (by norm_num)
theorem B3791717 : Blo 1684042 3791717 := bbase (se 4 (by rfl) ⟨355473, by rfl⟩ : syracuseStep 3791717 = 710947) (by norm_num)
theorem B4266877 : Blo 1684042 4266877 := bbase (se 3 (by rfl) ⟨800039, by rfl⟩ : syracuseStep 4266877 = 1600079) (by norm_num)
theorem B3038077 : Blo 1684042 3038077 := bbase (se 3 (by rfl) ⟨569639, by rfl⟩ : syracuseStep 3038077 = 1139279) (by norm_num)
theorem B3791789 : Blo 1684042 3791789 := bbase (se 3 (by rfl) ⟨710960, by rfl⟩ : syracuseStep 3791789 = 1421921) (by norm_num)
theorem B6396853 : Blo 1684042 6396853 := bbase (se 5 (by rfl) ⟨299852, by rfl⟩ : syracuseStep 6396853 = 599705) (by norm_num)
theorem B4266989 : Blo 1684042 4266989 := bbase (se 3 (by rfl) ⟨800060, by rfl⟩ : syracuseStep 4266989 = 1600121) (by norm_num)
theorem B5471221 : Blo 1684042 5471221 := bbase (se 5 (by rfl) ⟨256463, by rfl⟩ : syracuseStep 5471221 = 512927) (by norm_num)
theorem B3791861 : Blo 1684042 3791861 := bbase (se 5 (by rfl) ⟨177743, by rfl⟩ : syracuseStep 3791861 = 355487) (by norm_num)
theorem B8526869 : Blo 1684042 8526869 := bbase (se 6 (by rfl) ⟨199848, by rfl⟩ : syracuseStep 8526869 = 399697) (by norm_num)
theorem B3791933 : Blo 1684042 3791933 := bbase (se 3 (by rfl) ⟨710987, by rfl⟩ : syracuseStep 3791933 = 1421975) (by norm_num)
theorem B3079237 : Blo 1684042 3079237 := bbase (se 4 (by rfl) ⟨288678, by rfl⟩ : syracuseStep 3079237 = 577357) (by norm_num)
theorem B5684309 : Blo 1684042 5684309 := bbase (se 8 (by rfl) ⟨33306, by rfl⟩ : syracuseStep 5684309 = 66613) (by norm_num)
theorem B3792005 : Blo 1684042 3792005 := bbase (se 4 (by rfl) ⟨355500, by rfl⟩ : syracuseStep 3792005 = 711001) (by norm_num)
theorem B5397653 : Blo 1684042 5397653 := bbase (se 6 (by rfl) ⟨126507, by rfl⟩ : syracuseStep 5397653 = 253015) (by norm_num)
theorem B2161829 : Blo 1684042 2161829 := bbase (se 4 (by rfl) ⟨202671, by rfl⟩ : syracuseStep 2161829 = 405343) (by norm_num)
theorem B4267181 : Blo 1684042 4267181 := bbase (se 3 (by rfl) ⟨800096, by rfl⟩ : syracuseStep 4267181 = 1600193) (by norm_num)
theorem B3792077 : Blo 1684042 3792077 := bbase (se 3 (by rfl) ⟨711014, by rfl⟩ : syracuseStep 3792077 = 1422029) (by norm_num)
theorem B6397157 : Blo 1684042 6397157 := bbase (se 4 (by rfl) ⟨599733, by rfl⟩ : syracuseStep 6397157 = 1199467) (by norm_num)
theorem B8101093 : Blo 1684042 8101093 := bbase (se 4 (by rfl) ⟨759477, by rfl⟩ : syracuseStep 8101093 = 1518955) (by norm_num)
theorem B3792149 : Blo 1684042 3792149 := bbase (se 6 (by rfl) ⟨88878, by rfl⟩ : syracuseStep 3792149 = 177757) (by norm_num)
theorem B5193013 : Blo 1684042 5193013 := bbase (se 5 (by rfl) ⟨243422, by rfl⟩ : syracuseStep 5193013 = 486845) (by norm_num)
theorem B2399549 : Blo 1684042 2399549 := bbase (se 3 (by rfl) ⟨449915, by rfl⟩ : syracuseStep 2399549 = 899831) (by norm_num)
theorem B2841925 : Blo 1684042 2841925 := bbase (se 4 (by rfl) ⟨266430, by rfl⟩ : syracuseStep 2841925 = 532861) (by norm_num)
theorem B3792221 : Blo 1684042 3792221 := bbase (se 3 (by rfl) ⟨711041, by rfl⟩ : syracuseStep 3792221 = 1422083) (by norm_num)
theorem B2842013 : Blo 1684042 2842013 := bbase (se 3 (by rfl) ⟨532877, by rfl⟩ : syracuseStep 2842013 = 1065755) (by norm_num)
theorem B3792293 : Blo 1684042 3792293 := bbase (se 4 (by rfl) ⟨355527, by rfl⟩ : syracuseStep 3792293 = 711055) (by norm_num)
theorem B2276789 : Blo 1684042 2276789 := bbase (se 5 (by rfl) ⟨106724, by rfl⟩ : syracuseStep 2276789 = 213449) (by norm_num)
theorem B1973705 : Blo 1684042 1973705 := bbase (se 2 (by rfl) ⟨740139, by rfl⟩ : syracuseStep 1973705 = 1480279) (by norm_num)
theorem B3792365 : Blo 1684042 3792365 := bbase (se 3 (by rfl) ⟨711068, by rfl⟩ : syracuseStep 3792365 = 1422137) (by norm_num)
theorem B5684741 : Blo 1684042 5684741 := bbase (se 4 (by rfl) ⟨532944, by rfl⟩ : syracuseStep 5684741 = 1065889) (by norm_num)
theorem B4267525 : Blo 1684042 4267525 := bbase (se 4 (by rfl) ⟨400080, by rfl⟩ : syracuseStep 4267525 = 800161) (by norm_num)
theorem B4046357 : Blo 1684042 4046357 := bbase (se 6 (by rfl) ⟨94836, by rfl⟩ : syracuseStep 4046357 = 189673) (by norm_num)
theorem B2842141 : Blo 1684042 2842141 := bbase (se 3 (by rfl) ⟨532901, by rfl⟩ : syracuseStep 2842141 = 1065803) (by norm_num)
theorem B3792437 : Blo 1684042 3792437 := bbase (se 5 (by rfl) ⟨177770, by rfl⟩ : syracuseStep 3792437 = 355541) (by norm_num)
theorem B9600565 : Blo 1684042 9600565 := bbase (se 5 (by rfl) ⟨450026, by rfl⟩ : syracuseStep 9600565 = 900053) (by norm_num)
theorem B2842229 : Blo 1684042 2842229 := bbase (se 5 (by rfl) ⟨133229, by rfl⟩ : syracuseStep 2842229 = 266459) (by norm_num)
theorem B4267637 : Blo 1684042 4267637 := bbase (se 5 (by rfl) ⟨200045, by rfl⟩ : syracuseStep 4267637 = 400091) (by norm_num)
theorem B3792509 : Blo 1684042 3792509 := bbase (se 3 (by rfl) ⟨711095, by rfl⟩ : syracuseStep 3792509 = 1422191) (by norm_num)
theorem B30727829 : Blo 1684042 30727829 := bbase (se 6 (by rfl) ⟨720183, by rfl⟩ : syracuseStep 30727829 = 1440367) (by norm_num)
theorem B4800181 : Blo 1684042 4800181 := bbase (se 5 (by rfl) ⟨225008, by rfl⟩ : syracuseStep 4800181 = 450017) (by norm_num)
theorem B3792581 : Blo 1684042 3792581 := bbase (se 4 (by rfl) ⟨355554, by rfl⟩ : syracuseStep 3792581 = 711109) (by norm_num)
theorem B2842357 : Blo 1684042 2842357 := bbase (se 5 (by rfl) ⟨133235, by rfl⟩ : syracuseStep 2842357 = 266471) (by norm_num)
theorem B3792653 : Blo 1684042 3792653 := bbase (se 3 (by rfl) ⟨711122, by rfl⟩ : syracuseStep 3792653 = 1422245) (by norm_num)
theorem B4046645 : Blo 1684042 4046645 := bbase (se 5 (by rfl) ⟨189686, by rfl⟩ : syracuseStep 4046645 = 379373) (by norm_num)
theorem B2842445 : Blo 1684042 2842445 := bbase (se 3 (by rfl) ⟨532958, by rfl⟩ : syracuseStep 2842445 = 1065917) (by norm_num)
theorem B3792725 : Blo 1684042 3792725 := bbase (se 9 (by rfl) ⟨11111, by rfl⟩ : syracuseStep 3792725 = 22223) (by norm_num)
theorem B9723797 : Blo 1684042 9723797 := bbase (se 6 (by rfl) ⟨227901, by rfl⟩ : syracuseStep 9723797 = 455803) (by norm_num)
theorem B3792797 : Blo 1684042 3792797 := bbase (se 3 (by rfl) ⟨711149, by rfl⟩ : syracuseStep 3792797 = 1422299) (by norm_num)
theorem B5685173 : Blo 1684042 5685173 := bbase (se 5 (by rfl) ⟨266492, by rfl⟩ : syracuseStep 5685173 = 532985) (by norm_num)
theorem B2162629 : Blo 1684042 2162629 := bbase (se 4 (by rfl) ⟨202746, by rfl⟩ : syracuseStep 2162629 = 405493) (by norm_num)
theorem B2842573 : Blo 1684042 2842573 := bbase (se 3 (by rfl) ⟨532982, by rfl⟩ : syracuseStep 2842573 = 1065965) (by norm_num)
theorem B2023385 : Blo 1684042 2023385 := bbase (se 2 (by rfl) ⟨758769, by rfl⟩ : syracuseStep 2023385 = 1517539) (by norm_num)
theorem B3792869 : Blo 1684042 3792869 := bbase (se 4 (by rfl) ⟨355581, by rfl⟩ : syracuseStep 3792869 = 711163) (by norm_num)
theorem B9109493 : Blo 1684042 9109493 := bbase (se 5 (by rfl) ⟨427007, by rfl⟩ : syracuseStep 9109493 = 854015) (by norm_num)
theorem B12795893 : Blo 1684042 12795893 := bbase (se 5 (by rfl) ⟨599807, by rfl⟩ : syracuseStep 12795893 = 1199615) (by norm_num)
theorem B2842627 : Blo 1684042 2842627 := bstep (se 1 (by rfl) ⟨2131970, by rfl⟩ : syracuseStep 2842627 = 4263941) B4263941
theorem B3792977 : Blo 1684042 3792977 := bstep (se 2 (by rfl) ⟨1422366, by rfl⟩ : syracuseStep 3792977 = 2844733) B2844733
theorem B3792995 : Blo 1684042 3792995 := bstep (se 1 (by rfl) ⟨2844746, by rfl⟩ : syracuseStep 3792995 = 5689493) B5689493
theorem B5685389 : Blo 1684042 5685389 := bstep (se 3 (by rfl) ⟨1066010, by rfl⟩ : syracuseStep 5685389 = 2132021) B2132021
theorem B2842769 : Blo 1684042 2842769 := bstep (se 2 (by rfl) ⟨1066038, by rfl⟩ : syracuseStep 2842769 = 2132077) B2132077
theorem B6398129 : Blo 1684042 6398129 := bstep (se 2 (by rfl) ⟨2399298, by rfl⟩ : syracuseStep 6398129 = 4798597) B4798597
theorem B5685443 : Blo 1684042 5685443 := bstep (se 1 (by rfl) ⟨4264082, by rfl⟩ : syracuseStep 5685443 = 8528165) B8528165
theorem B9593093 : Blo 1684042 9593093 := bstep (se 4 (by rfl) ⟨899352, by rfl⟩ : syracuseStep 9593093 = 1798705) B1798705
theorem B2842897 : Blo 1684042 2842897 := bstep (se 2 (by rfl) ⟨1066086, by rfl⟩ : syracuseStep 2842897 = 2132173) B2132173
theorem B2400529 : Blo 1684042 2400529 := bstep (se 2 (by rfl) ⟨900198, by rfl⟩ : syracuseStep 2400529 = 1800397) B1800397
theorem B2842931 : Blo 1684042 2842931 := bstep (se 1 (by rfl) ⟨2132198, by rfl⟩ : syracuseStep 2842931 = 4264397) B4264397
theorem B2400563 : Blo 1684042 2400563 := bstep (se 1 (by rfl) ⟨1800422, by rfl⟩ : syracuseStep 2400563 = 3600845) B3600845
theorem B3793265 : Blo 1684042 3793265 := bstep (se 2 (by rfl) ⟨1422474, by rfl⟩ : syracuseStep 3793265 = 2844949) B2844949
theorem B3793283 : Blo 1684042 3793283 := bstep (se 1 (by rfl) ⟨2844962, by rfl⟩ : syracuseStep 3793283 = 5689925) B5689925
theorem B2843059 : Blo 1684042 2843059 := bstep (se 1 (by rfl) ⟨2132294, by rfl⟩ : syracuseStep 2843059 = 4264589) B4264589
theorem B5685713 : Blo 1684042 5685713 := bstep (se 2 (by rfl) ⟨2132142, by rfl⟩ : syracuseStep 5685713 = 4264285) B4264285
theorem B2843201 : Blo 1684042 2843201 := bstep (se 2 (by rfl) ⟨1066200, by rfl⟩ : syracuseStep 2843201 = 2132401) B2132401
theorem B3596881 : Blo 1684042 3596881 := bstep (se 2 (by rfl) ⟨1348830, by rfl⟩ : syracuseStep 3596881 = 2697661) B2697661
theorem B3793553 : Blo 1684042 3793553 := bstep (se 2 (by rfl) ⟨1422582, by rfl⟩ : syracuseStep 3793553 = 2845165) B2845165
theorem B3793571 : Blo 1684042 3793571 := bstep (se 1 (by rfl) ⟨2845178, by rfl⟩ : syracuseStep 3793571 = 5690357) B5690357
theorem B2843329 : Blo 1684042 2843329 := bstep (se 2 (by rfl) ⟨1066248, by rfl⟩ : syracuseStep 2843329 = 2132497) B2132497
theorem B9593549 : Blo 1684042 9593549 := bstep (se 3 (by rfl) ⟨1798790, by rfl⟩ : syracuseStep 9593549 = 3597581) B3597581
theorem B4047587 : Blo 1684042 4047587 := bstep (se 1 (by rfl) ⟨3035690, by rfl⟩ : syracuseStep 4047587 = 6071381) B6071381
theorem B2843363 : Blo 1684042 2843363 := bstep (se 1 (by rfl) ⟨2132522, by rfl⟩ : syracuseStep 2843363 = 4265045) B4265045
theorem B7684877 : Blo 1684042 7684877 := bstep (se 3 (by rfl) ⟨1440914, by rfl⟩ : syracuseStep 7684877 = 2881829) B2881829
theorem B9601841 : Blo 1684042 9601841 := bstep (se 2 (by rfl) ⟨3600690, by rfl⟩ : syracuseStep 9601841 = 7201381) B7201381
theorem B2736947 : Blo 1684042 2736947 := bstep (se 1 (by rfl) ⟨2052710, by rfl⟩ : syracuseStep 2736947 = 4105421) B4105421
theorem B5473091 : Blo 1684042 5473091 := bstep (se 1 (by rfl) ⟨4104818, by rfl⟩ : syracuseStep 5473091 = 8209637) B8209637
theorem B6398797 : Blo 1684042 6398797 := bstep (se 3 (by rfl) ⟨1199774, by rfl⟩ : syracuseStep 6398797 = 2399549) B2399549
theorem B3597137 : Blo 1684042 3597137 := bstep (se 2 (by rfl) ⟨1348926, by rfl⟩ : syracuseStep 3597137 = 2697853) B2697853
theorem B2843491 : Blo 1684042 2843491 := bstep (se 1 (by rfl) ⟨2132618, by rfl⟩ : syracuseStep 2843491 = 4265237) B4265237
theorem B4047779 : Blo 1684042 4047779 := bstep (se 1 (by rfl) ⟨3035834, by rfl⟩ : syracuseStep 4047779 = 6071669) B6071669
theorem B3417059 : Blo 1684042 3417059 := bstep (se 1 (by rfl) ⟨2562794, by rfl⟩ : syracuseStep 3417059 = 5125589) B5125589
theorem B5686253 : Blo 1684042 5686253 := bstep (se 3 (by rfl) ⟨1066172, by rfl⟩ : syracuseStep 5686253 = 2132345) B2132345
theorem B4047857 : Blo 1684042 4047857 := bstep (se 2 (by rfl) ⟨1517946, by rfl⟩ : syracuseStep 4047857 = 3035893) B3035893
theorem B2843633 : Blo 1684042 2843633 := bstep (se 2 (by rfl) ⟨1066362, by rfl⟩ : syracuseStep 2843633 = 2132725) B2132725
theorem B5686307 : Blo 1684042 5686307 := bstep (se 1 (by rfl) ⟨4264730, by rfl⟩ : syracuseStep 5686307 = 8529461) B8529461
theorem B6153251 : Blo 1684042 6153251 := bstep (se 1 (by rfl) ⟨4614938, by rfl⟩ : syracuseStep 6153251 = 9229877) B9229877
theorem B2843761 : Blo 1684042 2843761 := bstep (se 2 (by rfl) ⟨1066410, by rfl⟩ : syracuseStep 2843761 = 2132821) B2132821
theorem B6071437 : Blo 1684042 6071437 := bstep (se 3 (by rfl) ⟨1138394, by rfl⟩ : syracuseStep 6071437 = 2276789) B2276789
theorem B5399693 : Blo 1684042 5399693 := bstep (se 3 (by rfl) ⟨1012442, by rfl⟩ : syracuseStep 5399693 = 2024885) B2024885
theorem B2843795 : Blo 1684042 2843795 := bstep (se 1 (by rfl) ⟨2132846, by rfl⟩ : syracuseStep 2843795 = 4265693) B4265693
theorem B4048049 : Blo 1684042 4048049 := bstep (se 2 (by rfl) ⟨1518018, by rfl⟩ : syracuseStep 4048049 = 3036037) B3036037
theorem B8529137 : Blo 1684042 8529137 := bstep (se 2 (by rfl) ⟨3198426, by rfl⟩ : syracuseStep 8529137 = 6396853) B6396853
theorem B2843923 : Blo 1684042 2843923 := bstep (se 1 (by rfl) ⟨2132942, by rfl⟩ : syracuseStep 2843923 = 4265885) B4265885
theorem B5686577 : Blo 1684042 5686577 := bstep (se 2 (by rfl) ⟨2132466, by rfl⟩ : syracuseStep 5686577 = 4264933) B4264933
theorem B7193933 : Blo 1684042 7193933 := bstep (se 3 (by rfl) ⟨1348862, by rfl⟩ : syracuseStep 7193933 = 2697725) B2697725
theorem B2024851 : Blo 1684042 2024851 := bstep (se 1 (by rfl) ⟨1518638, by rfl⟩ : syracuseStep 2024851 = 3037277) B3037277
theorem B2844065 : Blo 1684042 2844065 := bstep (se 2 (by rfl) ⟨1066524, by rfl⟩ : syracuseStep 2844065 = 2133049) B2133049
theorem B4105649 : Blo 1684042 4105649 := bstep (se 2 (by rfl) ⟨1539618, by rfl⟩ : syracuseStep 4105649 = 3079237) B3079237
theorem B2024947 : Blo 1684042 2024947 := bstep (se 1 (by rfl) ⟨1518710, by rfl⟩ : syracuseStep 2024947 = 3037421) B3037421
theorem B11535877 : Blo 1684042 11535877 := bstep (se 4 (by rfl) ⟨1081488, by rfl⟩ : syracuseStep 11535877 = 2162977) B2162977
theorem B2844193 : Blo 1684042 2844193 := bstep (se 2 (by rfl) ⟨1066572, by rfl⟩ : syracuseStep 2844193 = 2133145) B2133145
theorem B5400113 : Blo 1684042 5400113 := bstep (se 2 (by rfl) ⟨2025042, by rfl⟩ : syracuseStep 5400113 = 4050085) B4050085
theorem B2844227 : Blo 1684042 2844227 := bstep (se 1 (by rfl) ⟨2133170, by rfl⟩ : syracuseStep 2844227 = 4266341) B4266341
theorem B6399587 : Blo 1684042 6399587 := bstep (se 1 (by rfl) ⟨4799690, by rfl⟩ : syracuseStep 6399587 = 9599381) B9599381
theorem B2025091 : Blo 1684042 2025091 := bstep (se 1 (by rfl) ⟨1518818, by rfl⟩ : syracuseStep 2025091 = 3037637) B3037637
theorem B3417731 : Blo 1684042 3417731 := bstep (se 1 (by rfl) ⟨2563298, by rfl⟩ : syracuseStep 3417731 = 5126597) B5126597
theorem B4048547 : Blo 1684042 4048547 := bstep (se 1 (by rfl) ⟨3036410, by rfl⟩ : syracuseStep 4048547 = 6072821) B6072821
theorem B3843779 : Blo 1684042 3843779 := bstep (se 1 (by rfl) ⟨2882834, by rfl⟩ : syracuseStep 3843779 = 5765669) B5765669
theorem B2844355 : Blo 1684042 2844355 := bstep (se 1 (by rfl) ⟨2133266, by rfl⟩ : syracuseStep 2844355 = 4266533) B4266533
theorem B6924017 : Blo 1684042 6924017 := bstep (se 2 (by rfl) ⟨2596506, by rfl⟩ : syracuseStep 6924017 = 5193013) B5193013
theorem B4048625 : Blo 1684042 4048625 := bstep (se 2 (by rfl) ⟨1518234, by rfl⟩ : syracuseStep 4048625 = 3036469) B3036469
theorem B5687117 : Blo 1684042 5687117 := bstep (se 3 (by rfl) ⟨1066334, by rfl⟩ : syracuseStep 5687117 = 2132669) B2132669
theorem B2844497 : Blo 1684042 2844497 := bstep (se 2 (by rfl) ⟨1066686, by rfl⟩ : syracuseStep 2844497 = 2133373) B2133373
theorem B5687171 : Blo 1684042 5687171 := bstep (se 1 (by rfl) ⟨4265378, by rfl⟩ : syracuseStep 5687171 = 8530757) B8530757
theorem B12797837 : Blo 1684042 12797837 := bstep (se 3 (by rfl) ⟨2399594, by rfl⟩ : syracuseStep 12797837 = 4799189) B4799189
theorem B2131859 : Blo 1684042 2131859 := bstep (se 1 (by rfl) ⟨1598894, by rfl⟩ : syracuseStep 2131859 = 3197789) B3197789
theorem B2844625 : Blo 1684042 2844625 := bstep (se 2 (by rfl) ⟨1066734, by rfl⟩ : syracuseStep 2844625 = 2133469) B2133469
theorem B10250225 : Blo 1684042 10250225 := bstep (se 2 (by rfl) ⟨3843834, by rfl⟩ : syracuseStep 10250225 = 7687669) B7687669
theorem B2844659 : Blo 1684042 2844659 := bstep (se 1 (by rfl) ⟨2133494, by rfl⟩ : syracuseStep 2844659 = 4266989) B4266989
theorem B3598435 : Blo 1684042 3598435 := bstep (se 1 (by rfl) ⟨2698826, by rfl⟩ : syracuseStep 3598435 = 5397653) B5397653
theorem B48580721 : Blo 1684042 48580721 := bstep (se 2 (by rfl) ⟨18217770, by rfl⟩ : syracuseStep 48580721 = 36435541) B36435541
theorem B4049009 : Blo 1684042 4049009 := bstep (se 2 (by rfl) ⟨1518378, by rfl⟩ : syracuseStep 4049009 = 3036757) B3036757
theorem B58386545 : Blo 1684042 58386545 := bstep (se 2 (by rfl) ⟨21894954, by rfl⟩ : syracuseStep 58386545 = 43789909) B43789909
theorem B2844787 : Blo 1684042 2844787 := bstep (se 1 (by rfl) ⟨2133590, by rfl⟩ : syracuseStep 2844787 = 4267181) B4267181
theorem B10791053 : Blo 1684042 10791053 := bstep (se 3 (by rfl) ⟨2023322, by rfl⟩ : syracuseStep 10791053 = 4046645) B4046645
theorem B5687441 : Blo 1684042 5687441 := bstep (se 2 (by rfl) ⟨2132790, by rfl⟩ : syracuseStep 5687441 = 4265581) B4265581
theorem B6400241 : Blo 1684042 6400241 := bstep (se 2 (by rfl) ⟨2400090, by rfl⟩ : syracuseStep 6400241 = 4800181) B4800181
theorem B2844929 : Blo 1684042 2844929 := bstep (se 2 (by rfl) ⟨1066848, by rfl⟩ : syracuseStep 2844929 = 2133697) B2133697
theorem B1894675 : Blo 1684042 1894675 := bstep (se 1 (by rfl) ⟨1421006, by rfl⟩ : syracuseStep 1894675 = 2842013) B2842013
theorem B61458709 : Blo 1684042 61458709 := bstep (se 6 (by rfl) ⟨1440438, by rfl⟩ : syracuseStep 61458709 = 2880877) B2880877
theorem B2697571 : Blo 1684042 2697571 := bstep (se 1 (by rfl) ⟨2023178, by rfl⟩ : syracuseStep 2697571 = 4046357) B4046357
theorem B2845057 : Blo 1684042 2845057 := bstep (se 2 (by rfl) ⟨1066896, by rfl⟩ : syracuseStep 2845057 = 2133793) B2133793
theorem B1894819 : Blo 1684042 1894819 := bstep (se 1 (by rfl) ⟨1421114, by rfl⟩ : syracuseStep 1894819 = 2842229) B2842229
theorem B2845091 : Blo 1684042 2845091 := bstep (se 1 (by rfl) ⟨2133818, by rfl⟩ : syracuseStep 2845091 = 4267637) B4267637
theorem B3598769 : Blo 1684042 3598769 := bstep (se 2 (by rfl) ⟨1349538, by rfl⟩ : syracuseStep 3598769 = 2699077) B2699077
theorem B20498885 : Blo 1684042 20498885 := bstep (se 4 (by rfl) ⟨1921770, by rfl⟩ : syracuseStep 20498885 = 3843541) B3843541
theorem B1894963 : Blo 1684042 1894963 := bstep (se 1 (by rfl) ⟨1421222, by rfl⟩ : syracuseStep 1894963 = 2842445) B2842445
theorem B2132563 : Blo 1684042 2132563 := bstep (se 1 (by rfl) ⟨1599422, by rfl⟩ : syracuseStep 2132563 = 3198845) B3198845
theorem B6482531 : Blo 1684042 6482531 := bstep (se 1 (by rfl) ⟨4861898, by rfl⟩ : syracuseStep 6482531 = 9723797) B9723797
theorem B6072995 : Blo 1684042 6072995 := bstep (se 1 (by rfl) ⟨4554746, by rfl⟩ : syracuseStep 6072995 = 9109493) B9109493
theorem B8530595 : Blo 1684042 8530595 := bstep (se 1 (by rfl) ⟨6397946, by rfl⟩ : syracuseStep 8530595 = 12795893) B12795893
theorem B5687981 : Blo 1684042 5687981 := bstep (se 3 (by rfl) ⟨1066496, by rfl⟩ : syracuseStep 5687981 = 2132993) B2132993
theorem B2132659 : Blo 1684042 2132659 := bstep (se 1 (by rfl) ⟨1599494, by rfl⟩ : syracuseStep 2132659 = 3198989) B3198989
theorem B1895107 : Blo 1684042 1895107 := bstep (se 1 (by rfl) ⟨1421330, by rfl⟩ : syracuseStep 1895107 = 2842661) B2842661
theorem B5688035 : Blo 1684042 5688035 := bstep (se 1 (by rfl) ⟨4266026, by rfl⟩ : syracuseStep 5688035 = 8532053) B8532053
theorem B4745965 : Blo 1684042 4745965 := bstep (se 3 (by rfl) ⟨889868, by rfl⟩ : syracuseStep 4745965 = 1779737) B1779737
theorem B3197713 : Blo 1684042 3197713 := bstep (se 2 (by rfl) ⟨1199142, by rfl⟩ : syracuseStep 3197713 = 2398285) B2398285
theorem B9104197 : Blo 1684042 9104197 := bstep (se 4 (by rfl) ⟨853518, by rfl⟩ : syracuseStep 9104197 = 1707037) B1707037
theorem B1895251 : Blo 1684042 1895251 := bstep (se 1 (by rfl) ⟨1421438, by rfl⟩ : syracuseStep 1895251 = 2842877) B2842877
theorem B2526065 : Blo 1684042 2526065 := bstep (se 2 (by rfl) ⟨947274, by rfl⟩ : syracuseStep 2526065 = 1894549) B1894549
theorem B2526083 : Blo 1684042 2526083 := bstep (se 1 (by rfl) ⟨1894562, by rfl⟩ : syracuseStep 2526083 = 3789125) B3789125
theorem B2526113 : Blo 1684042 2526113 := bstep (se 2 (by rfl) ⟨947292, by rfl⟩ : syracuseStep 2526113 = 1894585) B1894585
theorem B3197873 : Blo 1684042 3197873 := bstep (se 2 (by rfl) ⟨1199202, by rfl⟩ : syracuseStep 3197873 = 2398405) B2398405
theorem B2526131 : Blo 1684042 2526131 := bstep (se 1 (by rfl) ⟨1894598, by rfl⟩ : syracuseStep 2526131 = 3789197) B3789197
theorem B2526161 : Blo 1684042 2526161 := bstep (se 2 (by rfl) ⟨947310, by rfl⟩ : syracuseStep 2526161 = 1894621) B1894621
theorem B2526179 : Blo 1684042 2526179 := bstep (se 1 (by rfl) ⟨1894634, by rfl⟩ : syracuseStep 2526179 = 3789269) B3789269
theorem B1895395 : Blo 1684042 1895395 := bstep (se 1 (by rfl) ⟨1421546, by rfl⟩ : syracuseStep 1895395 = 2843093) B2843093
theorem B5688305 : Blo 1684042 5688305 := bstep (se 2 (by rfl) ⟨2133114, by rfl⟩ : syracuseStep 5688305 = 4266229) B4266229
theorem B2526209 : Blo 1684042 2526209 := bstep (se 2 (by rfl) ⟨947328, by rfl⟩ : syracuseStep 2526209 = 1894657) B1894657
theorem B2526227 : Blo 1684042 2526227 := bstep (se 1 (by rfl) ⟨1894670, by rfl⟩ : syracuseStep 2526227 = 3789341) B3789341
theorem B2526257 : Blo 1684042 2526257 := bstep (se 2 (by rfl) ⟨947346, by rfl⟩ : syracuseStep 2526257 = 1894693) B1894693
theorem B2698289 : Blo 1684042 2698289 := bstep (se 2 (by rfl) ⟨1011858, by rfl⟩ : syracuseStep 2698289 = 2023717) B2023717
theorem B2526275 : Blo 1684042 2526275 := bstep (se 1 (by rfl) ⟨1894706, by rfl⟩ : syracuseStep 2526275 = 3789413) B3789413
theorem B2526305 : Blo 1684042 2526305 := bstep (se 2 (by rfl) ⟨947364, by rfl⟩ : syracuseStep 2526305 = 1894729) B1894729
theorem B8096867 : Blo 1684042 8096867 := bstep (se 1 (by rfl) ⟨6072650, by rfl⟩ : syracuseStep 8096867 = 12145301) B12145301
theorem B2526323 : Blo 1684042 2526323 := bstep (se 1 (by rfl) ⟨1894742, by rfl⟩ : syracuseStep 2526323 = 3789485) B3789485
theorem B1895539 : Blo 1684042 1895539 := bstep (se 1 (by rfl) ⟨1421654, by rfl⟩ : syracuseStep 1895539 = 2843309) B2843309
theorem B2526353 : Blo 1684042 2526353 := bstep (se 2 (by rfl) ⟨947382, by rfl⟩ : syracuseStep 2526353 = 1894765) B1894765
theorem B2526371 : Blo 1684042 2526371 := bstep (se 1 (by rfl) ⟨1894778, by rfl⟩ : syracuseStep 2526371 = 3789557) B3789557
theorem B2133155 : Blo 1684042 2133155 := bstep (se 1 (by rfl) ⟨1599866, by rfl⟩ : syracuseStep 2133155 = 3199733) B3199733
theorem B2526401 : Blo 1684042 2526401 := bstep (se 2 (by rfl) ⟨947400, by rfl⟩ : syracuseStep 2526401 = 1894801) B1894801
theorem B2526419 : Blo 1684042 2526419 := bstep (se 1 (by rfl) ⟨1894814, by rfl⟩ : syracuseStep 2526419 = 3789629) B3789629
theorem B2526449 : Blo 1684042 2526449 := bstep (se 2 (by rfl) ⟨947418, by rfl⟩ : syracuseStep 2526449 = 1894837) B1894837
theorem B2698481 : Blo 1684042 2698481 := bstep (se 2 (by rfl) ⟨1011930, by rfl⟩ : syracuseStep 2698481 = 2023861) B2023861
theorem B2526467 : Blo 1684042 2526467 := bstep (se 1 (by rfl) ⟨1894850, by rfl⟩ : syracuseStep 2526467 = 3789701) B3789701
theorem B1895683 : Blo 1684042 1895683 := bstep (se 1 (by rfl) ⟨1421762, by rfl⟩ : syracuseStep 1895683 = 2843525) B2843525
theorem B2526497 : Blo 1684042 2526497 := bstep (se 2 (by rfl) ⟨947436, by rfl⟩ : syracuseStep 2526497 = 1894873) B1894873
theorem B2526515 : Blo 1684042 2526515 := bstep (se 1 (by rfl) ⟨1894886, by rfl⟩ : syracuseStep 2526515 = 3789773) B3789773
theorem B3198275 : Blo 1684042 3198275 := bstep (se 1 (by rfl) ⟨2398706, by rfl⟩ : syracuseStep 3198275 = 4797413) B4797413
theorem B2526545 : Blo 1684042 2526545 := bstep (se 2 (by rfl) ⟨947454, by rfl⟩ : syracuseStep 2526545 = 1894909) B1894909
theorem B2526563 : Blo 1684042 2526563 := bstep (se 1 (by rfl) ⟨1894922, by rfl⟩ : syracuseStep 2526563 = 3789845) B3789845
theorem B2526593 : Blo 1684042 2526593 := bstep (se 2 (by rfl) ⟨947472, by rfl⟩ : syracuseStep 2526593 = 1894945) B1894945
theorem B4263313 : Blo 1684042 4263313 := bstep (se 2 (by rfl) ⟨1598742, by rfl⟩ : syracuseStep 4263313 = 3197485) B3197485
theorem B2526611 : Blo 1684042 2526611 := bstep (se 1 (by rfl) ⟨1894958, by rfl⟩ : syracuseStep 2526611 = 3789917) B3789917
theorem B1895827 : Blo 1684042 1895827 := bstep (se 1 (by rfl) ⟨1421870, by rfl⟩ : syracuseStep 1895827 = 2843741) B2843741
theorem B2526641 : Blo 1684042 2526641 := bstep (se 2 (by rfl) ⟨947490, by rfl⟩ : syracuseStep 2526641 = 1894981) B1894981
theorem B2526659 : Blo 1684042 2526659 := bstep (se 1 (by rfl) ⟨1894994, by rfl⟩ : syracuseStep 2526659 = 3789989) B3789989
theorem B8531405 : Blo 1684042 8531405 := bstep (se 3 (by rfl) ⟨1599638, by rfl⟩ : syracuseStep 8531405 = 3199277) B3199277
theorem B2526689 : Blo 1684042 2526689 := bstep (se 2 (by rfl) ⟨947508, by rfl⟩ : syracuseStep 2526689 = 1895017) B1895017
theorem B1707491 : Blo 1684042 1707491 := bstep (se 1 (by rfl) ⟨1280618, by rfl⟩ : syracuseStep 1707491 = 2561237) B2561237
theorem B2526707 : Blo 1684042 2526707 := bstep (se 1 (by rfl) ⟨1895030, by rfl⟩ : syracuseStep 2526707 = 3790061) B3790061
theorem B5688845 : Blo 1684042 5688845 := bstep (se 3 (by rfl) ⟨1066658, by rfl⟩ : syracuseStep 5688845 = 2133317) B2133317
theorem B2526737 : Blo 1684042 2526737 := bstep (se 2 (by rfl) ⟨947526, by rfl⟩ : syracuseStep 2526737 = 1895053) B1895053
theorem B2526755 : Blo 1684042 2526755 := bstep (se 1 (by rfl) ⟨1895066, by rfl⟩ : syracuseStep 2526755 = 3790133) B3790133
theorem B1895971 : Blo 1684042 1895971 := bstep (se 1 (by rfl) ⟨1421978, by rfl⟩ : syracuseStep 1895971 = 2843957) B2843957
theorem B9596465 : Blo 1684042 9596465 := bstep (se 2 (by rfl) ⟨3598674, by rfl⟩ : syracuseStep 9596465 = 7197349) B7197349
theorem B2526785 : Blo 1684042 2526785 := bstep (se 2 (by rfl) ⟨947544, by rfl⟩ : syracuseStep 2526785 = 1895089) B1895089
theorem B3599939 : Blo 1684042 3599939 := bstep (se 1 (by rfl) ⟨2699954, by rfl⟩ : syracuseStep 3599939 = 5399909) B5399909
theorem B5688899 : Blo 1684042 5688899 := bstep (se 1 (by rfl) ⟨4266674, by rfl⟩ : syracuseStep 5688899 = 8533349) B8533349
theorem B2526803 : Blo 1684042 2526803 := bstep (se 1 (by rfl) ⟨1895102, by rfl⟩ : syracuseStep 2526803 = 3790205) B3790205
theorem B2526833 : Blo 1684042 2526833 := bstep (se 2 (by rfl) ⟨947562, by rfl⟩ : syracuseStep 2526833 = 1895125) B1895125
theorem B13143665 : Blo 1684042 13143665 := bstep (se 2 (by rfl) ⟨4928874, by rfl⟩ : syracuseStep 13143665 = 9857749) B9857749
theorem B2526851 : Blo 1684042 2526851 := bstep (se 1 (by rfl) ⟨1895138, by rfl⟩ : syracuseStep 2526851 = 3790277) B3790277
theorem B2526881 : Blo 1684042 2526881 := bstep (se 2 (by rfl) ⟨947580, by rfl⟩ : syracuseStep 2526881 = 1895161) B1895161
theorem B4263587 : Blo 1684042 4263587 := bstep (se 1 (by rfl) ⟨3197690, by rfl⟩ : syracuseStep 4263587 = 6395381) B6395381
theorem B4796081 : Blo 1684042 4796081 := bstep (se 2 (by rfl) ⟨1798530, by rfl⟩ : syracuseStep 4796081 = 3597061) B3597061
theorem B2526899 : Blo 1684042 2526899 := bstep (se 1 (by rfl) ⟨1895174, by rfl⟩ : syracuseStep 2526899 = 3790349) B3790349
theorem B1896115 : Blo 1684042 1896115 := bstep (se 1 (by rfl) ⟨1422086, by rfl⟩ : syracuseStep 1896115 = 2844173) B2844173
theorem B2526929 : Blo 1684042 2526929 := bstep (se 2 (by rfl) ⟨947598, by rfl⟩ : syracuseStep 2526929 = 1895197) B1895197
theorem B2526947 : Blo 1684042 2526947 := bstep (se 1 (by rfl) ⟨1895210, by rfl⟩ : syracuseStep 2526947 = 3790421) B3790421
theorem B2526977 : Blo 1684042 2526977 := bstep (se 2 (by rfl) ⟨947616, by rfl⟩ : syracuseStep 2526977 = 1895233) B1895233
theorem B2526995 : Blo 1684042 2526995 := bstep (se 1 (by rfl) ⟨1895246, by rfl⟩ : syracuseStep 2526995 = 3790493) B3790493
theorem B2527025 : Blo 1684042 2527025 := bstep (se 2 (by rfl) ⟨947634, by rfl⟩ : syracuseStep 2527025 = 1895269) B1895269
theorem B2527043 : Blo 1684042 2527043 := bstep (se 1 (by rfl) ⟨1895282, by rfl⟩ : syracuseStep 2527043 = 3790565) B3790565
theorem B1896259 : Blo 1684042 1896259 := bstep (se 1 (by rfl) ⟨1422194, by rfl⟩ : syracuseStep 1896259 = 2844389) B2844389
theorem B5689169 : Blo 1684042 5689169 := bstep (se 2 (by rfl) ⟨2133438, by rfl⟩ : syracuseStep 5689169 = 4266877) B4266877
theorem B4050769 : Blo 1684042 4050769 := bstep (se 2 (by rfl) ⟨1519038, by rfl⟩ : syracuseStep 4050769 = 3038077) B3038077
theorem B2961235 : Blo 1684042 2961235 := bstep (se 1 (by rfl) ⟨2220926, by rfl⟩ : syracuseStep 2961235 = 4441853) B4441853
theorem B2527073 : Blo 1684042 2527073 := bstep (se 2 (by rfl) ⟨947652, by rfl⟩ : syracuseStep 2527073 = 1895305) B1895305
theorem B4263779 : Blo 1684042 4263779 := bstep (se 1 (by rfl) ⟨3197834, by rfl⟩ : syracuseStep 4263779 = 6395669) B6395669
theorem B2133859 : Blo 1684042 2133859 := bstep (se 1 (by rfl) ⟨1600394, by rfl⟩ : syracuseStep 2133859 = 3200789) B3200789
theorem B4796273 : Blo 1684042 4796273 := bstep (se 2 (by rfl) ⟨1798602, by rfl⟩ : syracuseStep 4796273 = 3597205) B3597205
theorem B2527091 : Blo 1684042 2527091 := bstep (se 1 (by rfl) ⟨1895318, by rfl⟩ : syracuseStep 2527091 = 3790637) B3790637
theorem B2527121 : Blo 1684042 2527121 := bstep (se 2 (by rfl) ⟨947670, by rfl⟩ : syracuseStep 2527121 = 1895341) B1895341
theorem B2527139 : Blo 1684042 2527139 := bstep (se 1 (by rfl) ⟨1895354, by rfl⟩ : syracuseStep 2527139 = 3790709) B3790709
theorem B2527169 : Blo 1684042 2527169 := bstep (se 2 (by rfl) ⟨947688, by rfl⟩ : syracuseStep 2527169 = 1895377) B1895377
theorem B2527187 : Blo 1684042 2527187 := bstep (se 1 (by rfl) ⟨1895390, by rfl⟩ : syracuseStep 2527187 = 3790781) B3790781
theorem B1896403 : Blo 1684042 1896403 := bstep (se 1 (by rfl) ⟨1422302, by rfl⟩ : syracuseStep 1896403 = 2844605) B2844605
theorem B2527217 : Blo 1684042 2527217 := bstep (se 2 (by rfl) ⟨947706, by rfl⟩ : syracuseStep 2527217 = 1895413) B1895413
theorem B7294961 : Blo 1684042 7294961 := bstep (se 2 (by rfl) ⟨2735610, by rfl⟩ : syracuseStep 7294961 = 5471221) B5471221
theorem B2527235 : Blo 1684042 2527235 := bstep (se 1 (by rfl) ⟨1895426, by rfl⟩ : syracuseStep 2527235 = 3790853) B3790853
theorem B2527265 : Blo 1684042 2527265 := bstep (se 2 (by rfl) ⟨947724, by rfl⟩ : syracuseStep 2527265 = 1895449) B1895449
theorem B2527283 : Blo 1684042 2527283 := bstep (se 1 (by rfl) ⟨1895462, by rfl⟩ : syracuseStep 2527283 = 3790925) B3790925
theorem B2527313 : Blo 1684042 2527313 := bstep (se 2 (by rfl) ⟨947742, by rfl⟩ : syracuseStep 2527313 = 1895485) B1895485
theorem B2527331 : Blo 1684042 2527331 := bstep (se 1 (by rfl) ⟨1895498, by rfl⟩ : syracuseStep 2527331 = 3790997) B3790997
theorem B1896547 : Blo 1684042 1896547 := bstep (se 1 (by rfl) ⟨1422410, by rfl⟩ : syracuseStep 1896547 = 2844821) B2844821
theorem B2527361 : Blo 1684042 2527361 := bstep (se 2 (by rfl) ⟨947760, by rfl⟩ : syracuseStep 2527361 = 1895521) B1895521
theorem B2527379 : Blo 1684042 2527379 := bstep (se 1 (by rfl) ⟨1895534, by rfl⟩ : syracuseStep 2527379 = 3791069) B3791069
theorem B2527409 : Blo 1684042 2527409 := bstep (se 2 (by rfl) ⟨947778, by rfl⟩ : syracuseStep 2527409 = 1895557) B1895557
theorem B2527427 : Blo 1684042 2527427 := bstep (se 1 (by rfl) ⟨1895570, by rfl⟩ : syracuseStep 2527427 = 3791141) B3791141
theorem B3199171 : Blo 1684042 3199171 := bstep (se 1 (by rfl) ⟨2399378, by rfl⟩ : syracuseStep 3199171 = 4798757) B4798757
theorem B12792005 : Blo 1684042 12792005 := bstep (se 4 (by rfl) ⟨1199250, by rfl⟩ : syracuseStep 12792005 = 2398501) B2398501
theorem B2527457 : Blo 1684042 2527457 := bstep (se 2 (by rfl) ⟨947796, by rfl⟩ : syracuseStep 2527457 = 1895593) B1895593
theorem B2527475 : Blo 1684042 2527475 := bstep (se 1 (by rfl) ⟨1895606, by rfl⟩ : syracuseStep 2527475 = 3791213) B3791213
theorem B1896691 : Blo 1684042 1896691 := bstep (se 1 (by rfl) ⟨1422518, by rfl⟩ : syracuseStep 1896691 = 2845037) B2845037
theorem B2527505 : Blo 1684042 2527505 := bstep (se 2 (by rfl) ⟨947814, by rfl⟩ : syracuseStep 2527505 = 1895629) B1895629
theorem B2527523 : Blo 1684042 2527523 := bstep (se 1 (by rfl) ⟨1895642, by rfl⟩ : syracuseStep 2527523 = 3791285) B3791285
theorem B10801457 : Blo 1684042 10801457 := bstep (se 2 (by rfl) ⟨4050546, by rfl⟩ : syracuseStep 10801457 = 8101093) B8101093
theorem B2527553 : Blo 1684042 2527553 := bstep (se 2 (by rfl) ⟨947832, by rfl⟩ : syracuseStep 2527553 = 1895665) B1895665
theorem B2527571 : Blo 1684042 2527571 := bstep (se 1 (by rfl) ⟨1895678, by rfl⟩ : syracuseStep 2527571 = 3791357) B3791357
theorem B6394211 : Blo 1684042 6394211 := bstep (se 1 (by rfl) ⟨4795658, by rfl⟩ : syracuseStep 6394211 = 9591317) B9591317
theorem B3199331 : Blo 1684042 3199331 := bstep (se 1 (by rfl) ⟨2399498, by rfl⟩ : syracuseStep 3199331 = 4798997) B4798997
theorem B5689709 : Blo 1684042 5689709 := bstep (se 3 (by rfl) ⟨1066820, by rfl⟩ : syracuseStep 5689709 = 2133641) B2133641
theorem B2527601 : Blo 1684042 2527601 := bstep (se 2 (by rfl) ⟨947850, by rfl⟩ : syracuseStep 2527601 = 1895701) B1895701
theorem B2920835 : Blo 1684042 2920835 := bstep (se 1 (by rfl) ⟨2190626, by rfl⟩ : syracuseStep 2920835 = 4381253) B4381253
theorem B2527619 : Blo 1684042 2527619 := bstep (se 1 (by rfl) ⟨1895714, by rfl⟩ : syracuseStep 2527619 = 3791429) B3791429
theorem B2527649 : Blo 1684042 2527649 := bstep (se 2 (by rfl) ⟨947868, by rfl⟩ : syracuseStep 2527649 = 1895737) B1895737
theorem B8098211 : Blo 1684042 8098211 := bstep (se 1 (by rfl) ⟨6073658, by rfl⟩ : syracuseStep 8098211 = 12147317) B12147317
theorem B2052515 : Blo 1684042 2052515 := bstep (se 1 (by rfl) ⟨1539386, by rfl⟩ : syracuseStep 2052515 = 3078773) B3078773
theorem B5689763 : Blo 1684042 5689763 := bstep (se 1 (by rfl) ⟨4267322, by rfl⟩ : syracuseStep 5689763 = 8534645) B8534645
theorem B3789233 : Blo 1684042 3789233 := bstep (se 2 (by rfl) ⟨1420962, by rfl⟩ : syracuseStep 3789233 = 2841925) B2841925
theorem B2527667 : Blo 1684042 2527667 := bstep (se 1 (by rfl) ⟨1895750, by rfl⟩ : syracuseStep 2527667 = 3791501) B3791501
theorem B3789251 : Blo 1684042 3789251 := bstep (se 1 (by rfl) ⟨2841938, by rfl⟩ : syracuseStep 3789251 = 5683877) B5683877
theorem B2527697 : Blo 1684042 2527697 := bstep (se 2 (by rfl) ⟨947886, by rfl⟩ : syracuseStep 2527697 = 1895773) B1895773
theorem B2527715 : Blo 1684042 2527715 := bstep (se 1 (by rfl) ⟨1895786, by rfl⟩ : syracuseStep 2527715 = 3791573) B3791573
theorem B2527745 : Blo 1684042 2527745 := bstep (se 2 (by rfl) ⟨947904, by rfl⟩ : syracuseStep 2527745 = 1895809) B1895809
theorem B2527763 : Blo 1684042 2527763 := bstep (se 1 (by rfl) ⟨1895822, by rfl⟩ : syracuseStep 2527763 = 3791645) B3791645
theorem B2527793 : Blo 1684042 2527793 := bstep (se 2 (by rfl) ⟨947922, by rfl⟩ : syracuseStep 2527793 = 1895845) B1895845
theorem B2527811 : Blo 1684042 2527811 := bstep (se 1 (by rfl) ⟨1895858, by rfl⟩ : syracuseStep 2527811 = 3791717) B3791717
theorem B1684051 : Blo 1684042 1684051 := bstep (se 1 (by rfl) ⟨1263038, by rfl⟩ : syracuseStep 1684051 = 2526077) B2526077
theorem B1684067 : Blo 1684042 1684067 := bstep (se 1 (by rfl) ⟨1263050, by rfl⟩ : syracuseStep 1684067 = 2526101) B2526101
theorem B2527841 : Blo 1684042 2527841 := bstep (se 2 (by rfl) ⟨947940, by rfl⟩ : syracuseStep 2527841 = 1895881) B1895881
theorem B1684083 : Blo 1684042 1684083 := bstep (se 1 (by rfl) ⟨1263062, by rfl⟩ : syracuseStep 1684083 = 2526125) B2526125
theorem B2527859 : Blo 1684042 2527859 := bstep (se 1 (by rfl) ⟨1895894, by rfl⟩ : syracuseStep 2527859 = 3791789) B3791789
theorem B1684099 : Blo 1684042 1684099 := bstep (se 1 (by rfl) ⟨1263074, by rfl⟩ : syracuseStep 1684099 = 2526149) B2526149
theorem B2527889 : Blo 1684042 2527889 := bstep (se 2 (by rfl) ⟨947958, by rfl⟩ : syracuseStep 2527889 = 1895917) B1895917
theorem B1684115 : Blo 1684042 1684115 := bstep (se 1 (by rfl) ⟨1263086, by rfl⟩ : syracuseStep 1684115 = 2526173) B2526173
theorem B1684131 : Blo 1684042 1684131 := bstep (se 1 (by rfl) ⟨1263098, by rfl⟩ : syracuseStep 1684131 = 2526197) B2526197
theorem B2527907 : Blo 1684042 2527907 := bstep (se 1 (by rfl) ⟨1895930, by rfl⟩ : syracuseStep 2527907 = 3791861) B3791861
theorem B5690033 : Blo 1684042 5690033 := bstep (se 2 (by rfl) ⟨2133762, by rfl⟩ : syracuseStep 5690033 = 4267525) B4267525
theorem B1684147 : Blo 1684042 1684147 := bstep (se 1 (by rfl) ⟨1263110, by rfl⟩ : syracuseStep 1684147 = 2526221) B2526221
theorem B2527937 : Blo 1684042 2527937 := bstep (se 2 (by rfl) ⟨947976, by rfl⟩ : syracuseStep 2527937 = 1895953) B1895953
theorem B1684163 : Blo 1684042 1684163 := bstep (se 1 (by rfl) ⟨1263122, by rfl⟩ : syracuseStep 1684163 = 2526245) B2526245
theorem B3789521 : Blo 1684042 3789521 := bstep (se 2 (by rfl) ⟨1421070, by rfl⟩ : syracuseStep 3789521 = 2842141) B2842141
theorem B1684179 : Blo 1684042 1684179 := bstep (se 1 (by rfl) ⟨1263134, by rfl⟩ : syracuseStep 1684179 = 2526269) B2526269
theorem B2527955 : Blo 1684042 2527955 := bstep (se 1 (by rfl) ⟨1895966, by rfl⟩ : syracuseStep 2527955 = 3791933) B3791933
theorem B1684195 : Blo 1684042 1684195 := bstep (se 1 (by rfl) ⟨1263146, by rfl⟩ : syracuseStep 1684195 = 2526293) B2526293
theorem B3789539 : Blo 1684042 3789539 := bstep (se 1 (by rfl) ⟨2842154, by rfl⟩ : syracuseStep 3789539 = 5684309) B5684309
theorem B2527985 : Blo 1684042 2527985 := bstep (se 2 (by rfl) ⟨947994, by rfl⟩ : syracuseStep 2527985 = 1895989) B1895989
theorem B12800753 : Blo 1684042 12800753 := bstep (se 2 (by rfl) ⟨4800282, by rfl⟩ : syracuseStep 12800753 = 9600565) B9600565
theorem B1684211 : Blo 1684042 1684211 := bstep (se 1 (by rfl) ⟨1263158, by rfl⟩ : syracuseStep 1684211 = 2526317) B2526317
theorem B1684227 : Blo 1684042 1684227 := bstep (se 1 (by rfl) ⟨1263170, by rfl⟩ : syracuseStep 1684227 = 2526341) B2526341
theorem B2528003 : Blo 1684042 2528003 := bstep (se 1 (by rfl) ⟨1896002, by rfl⟩ : syracuseStep 2528003 = 3792005) B3792005
theorem B4264721 : Blo 1684042 4264721 := bstep (se 2 (by rfl) ⟨1599270, by rfl⟩ : syracuseStep 4264721 = 3198541) B3198541
theorem B1684243 : Blo 1684042 1684243 := bstep (se 1 (by rfl) ⟨1263182, by rfl⟩ : syracuseStep 1684243 = 2526365) B2526365
theorem B2528033 : Blo 1684042 2528033 := bstep (se 2 (by rfl) ⟨948012, by rfl⟩ : syracuseStep 2528033 = 1896025) B1896025
theorem B1684259 : Blo 1684042 1684259 := bstep (se 1 (by rfl) ⟨1263194, by rfl⟩ : syracuseStep 1684259 = 2526389) B2526389
theorem B1684275 : Blo 1684042 1684275 := bstep (se 1 (by rfl) ⟨1263206, by rfl⟩ : syracuseStep 1684275 = 2526413) B2526413
theorem B2528051 : Blo 1684042 2528051 := bstep (se 1 (by rfl) ⟨1896038, by rfl⟩ : syracuseStep 2528051 = 3792077) B3792077
theorem B1684291 : Blo 1684042 1684291 := bstep (se 1 (by rfl) ⟨1263218, by rfl⟩ : syracuseStep 1684291 = 2526437) B2526437
theorem B4264771 : Blo 1684042 4264771 := bstep (se 1 (by rfl) ⟨3198578, by rfl⟩ : syracuseStep 4264771 = 6397157) B6397157
theorem B4797265 : Blo 1684042 4797265 := bstep (se 2 (by rfl) ⟨1798974, by rfl⟩ : syracuseStep 4797265 = 3597949) B3597949
theorem B1684307 : Blo 1684042 1684307 := bstep (se 1 (by rfl) ⟨1263230, by rfl⟩ : syracuseStep 1684307 = 2526461) B2526461
theorem B2528081 : Blo 1684042 2528081 := bstep (se 2 (by rfl) ⟨948030, by rfl⟩ : syracuseStep 2528081 = 1896061) B1896061
theorem B1684323 : Blo 1684042 1684323 := bstep (se 1 (by rfl) ⟨1263242, by rfl⟩ : syracuseStep 1684323 = 2526485) B2526485
theorem B2528099 : Blo 1684042 2528099 := bstep (se 1 (by rfl) ⟨1896074, by rfl⟩ : syracuseStep 2528099 = 3792149) B3792149
theorem B1684339 : Blo 1684042 1684339 := bstep (se 1 (by rfl) ⟨1263254, by rfl⟩ : syracuseStep 1684339 = 2526509) B2526509
theorem B2528129 : Blo 1684042 2528129 := bstep (se 2 (by rfl) ⟨948048, by rfl⟩ : syracuseStep 2528129 = 1896097) B1896097
theorem B1684355 : Blo 1684042 1684355 := bstep (se 1 (by rfl) ⟨1263266, by rfl⟩ : syracuseStep 1684355 = 2526533) B2526533
theorem B1684371 : Blo 1684042 1684371 := bstep (se 1 (by rfl) ⟨1263278, by rfl⟩ : syracuseStep 1684371 = 2526557) B2526557
theorem B2528147 : Blo 1684042 2528147 := bstep (se 1 (by rfl) ⟨1896110, by rfl⟩ : syracuseStep 2528147 = 3792221) B3792221
theorem B1684387 : Blo 1684042 1684387 := bstep (se 1 (by rfl) ⟨1263290, by rfl⟩ : syracuseStep 1684387 = 2526581) B2526581
theorem B2528177 : Blo 1684042 2528177 := bstep (se 2 (by rfl) ⟨948066, by rfl⟩ : syracuseStep 2528177 = 1896133) B1896133
theorem B1684403 : Blo 1684042 1684403 := bstep (se 1 (by rfl) ⟨1263302, by rfl⟩ : syracuseStep 1684403 = 2526605) B2526605
theorem B21582773 : Blo 1684042 21582773 := bstep (se 5 (by rfl) ⟨1011692, by rfl⟩ : syracuseStep 21582773 = 2023385) B2023385
theorem B2700211 : Blo 1684042 2700211 := bstep (se 1 (by rfl) ⟨2025158, by rfl⟩ : syracuseStep 2700211 = 4050317) B4050317
theorem B1684419 : Blo 1684042 1684419 := bstep (se 1 (by rfl) ⟨1263314, by rfl⟩ : syracuseStep 1684419 = 2526629) B2526629
theorem B2528195 : Blo 1684042 2528195 := bstep (se 1 (by rfl) ⟨1896146, by rfl⟩ : syracuseStep 2528195 = 3792293) B3792293
theorem B4264913 : Blo 1684042 4264913 := bstep (se 2 (by rfl) ⟨1599342, by rfl⟩ : syracuseStep 4264913 = 3198685) B3198685
theorem B1684435 : Blo 1684042 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B2528225 : Blo 1684042 2528225 := bstep (se 2 (by rfl) ⟨948084, by rfl⟩ : syracuseStep 2528225 = 1896169) B1896169
theorem B1684451 : Blo 1684042 1684451 := bstep (se 1 (by rfl) ⟨1263338, by rfl⟩ : syracuseStep 1684451 = 2526677) B2526677
theorem B9597923 : Blo 1684042 9597923 := bstep (se 1 (by rfl) ⟨7198442, by rfl⟩ : syracuseStep 9597923 = 14396885) B14396885
theorem B3789809 : Blo 1684042 3789809 := bstep (se 2 (by rfl) ⟨1421178, by rfl⟩ : syracuseStep 3789809 = 2842357) B2842357
theorem B1684467 : Blo 1684042 1684467 := bstep (se 1 (by rfl) ⟨1263350, by rfl⟩ : syracuseStep 1684467 = 2526701) B2526701
theorem B2528243 : Blo 1684042 2528243 := bstep (se 1 (by rfl) ⟨1896182, by rfl⟩ : syracuseStep 2528243 = 3792365) B3792365
theorem B3789827 : Blo 1684042 3789827 := bstep (se 1 (by rfl) ⟨2842370, by rfl⟩ : syracuseStep 3789827 = 5684741) B5684741
theorem B1684483 : Blo 1684042 1684483 := bstep (se 1 (by rfl) ⟨1263362, by rfl⟩ : syracuseStep 1684483 = 2526725) B2526725
theorem B6927373 : Blo 1684042 6927373 := bstep (se 3 (by rfl) ⟨1298882, by rfl⟩ : syracuseStep 6927373 = 2597765) B2597765
theorem B2528273 : Blo 1684042 2528273 := bstep (se 2 (by rfl) ⟨948102, by rfl⟩ : syracuseStep 2528273 = 1896205) B1896205
theorem B1684499 : Blo 1684042 1684499 := bstep (se 1 (by rfl) ⟨1263374, by rfl⟩ : syracuseStep 1684499 = 2526749) B2526749
theorem B2700307 : Blo 1684042 2700307 := bstep (se 1 (by rfl) ⟨2025230, by rfl⟩ : syracuseStep 2700307 = 4050461) B4050461
theorem B1684515 : Blo 1684042 1684515 := bstep (se 1 (by rfl) ⟨1263386, by rfl⟩ : syracuseStep 1684515 = 2526773) B2526773
theorem B2528291 : Blo 1684042 2528291 := bstep (se 1 (by rfl) ⟨1896218, by rfl⟩ : syracuseStep 2528291 = 3792437) B3792437
theorem B6829105 : Blo 1684042 6829105 := bstep (se 2 (by rfl) ⟨2560914, by rfl⟩ : syracuseStep 6829105 = 5121829) B5121829
theorem B8098865 : Blo 1684042 8098865 := bstep (se 2 (by rfl) ⟨3037074, by rfl⟩ : syracuseStep 8098865 = 6074149) B6074149
theorem B1684531 : Blo 1684042 1684531 := bstep (se 1 (by rfl) ⟨1263398, by rfl⟩ : syracuseStep 1684531 = 2526797) B2526797
theorem B2528321 : Blo 1684042 2528321 := bstep (se 2 (by rfl) ⟨948120, by rfl⟩ : syracuseStep 2528321 = 1896241) B1896241
theorem B1684547 : Blo 1684042 1684547 := bstep (se 1 (by rfl) ⟨1263410, by rfl⟩ : syracuseStep 1684547 = 2526821) B2526821
theorem B1684563 : Blo 1684042 1684563 := bstep (se 1 (by rfl) ⟨1263422, by rfl⟩ : syracuseStep 1684563 = 2526845) B2526845
theorem B2528339 : Blo 1684042 2528339 := bstep (se 1 (by rfl) ⟨1896254, by rfl⟩ : syracuseStep 2528339 = 3792509) B3792509
theorem B249394261 : Blo 1684042 249394261 := bstep (se 8 (by rfl) ⟨1461294, by rfl⟩ : syracuseStep 249394261 = 2922589) B2922589
theorem B20485219 : Blo 1684042 20485219 := bstep (se 1 (by rfl) ⟨15363914, by rfl⟩ : syracuseStep 20485219 = 30727829) B30727829
theorem B1684579 : Blo 1684042 1684579 := bstep (se 1 (by rfl) ⟨1263434, by rfl⟩ : syracuseStep 1684579 = 2526869) B2526869
theorem B4797539 : Blo 1684042 4797539 := bstep (se 1 (by rfl) ⟨3598154, by rfl⟩ : syracuseStep 4797539 = 7196309) B7196309
theorem B2528369 : Blo 1684042 2528369 := bstep (se 2 (by rfl) ⟨948138, by rfl⟩ : syracuseStep 2528369 = 1896277) B1896277
theorem B1684595 : Blo 1684042 1684595 := bstep (se 1 (by rfl) ⟨1263446, by rfl⟩ : syracuseStep 1684595 = 2526893) B2526893
theorem B1684611 : Blo 1684042 1684611 := bstep (se 1 (by rfl) ⟨1263458, by rfl⟩ : syracuseStep 1684611 = 2526917) B2526917
theorem B2528387 : Blo 1684042 2528387 := bstep (se 1 (by rfl) ⟨1896290, by rfl⟩ : syracuseStep 2528387 = 3792581) B3792581
theorem B1684627 : Blo 1684042 1684627 := bstep (se 1 (by rfl) ⟨1263470, by rfl⟩ : syracuseStep 1684627 = 2526941) B2526941
theorem B2528417 : Blo 1684042 2528417 := bstep (se 2 (by rfl) ⟨948156, by rfl⟩ : syracuseStep 2528417 = 1896313) B1896313
theorem B1684643 : Blo 1684042 1684643 := bstep (se 1 (by rfl) ⟨1263482, by rfl⟩ : syracuseStep 1684643 = 2526965) B2526965
theorem B1684659 : Blo 1684042 1684659 := bstep (se 1 (by rfl) ⟨1263494, by rfl⟩ : syracuseStep 1684659 = 2526989) B2526989
theorem B2528435 : Blo 1684042 2528435 := bstep (se 1 (by rfl) ⟨1896326, by rfl⟩ : syracuseStep 2528435 = 3792653) B3792653
theorem B2700467 : Blo 1684042 2700467 := bstep (se 1 (by rfl) ⟨2025350, by rfl⟩ : syracuseStep 2700467 = 4050701) B4050701
theorem B1684675 : Blo 1684042 1684675 := bstep (se 1 (by rfl) ⟨1263506, by rfl⟩ : syracuseStep 1684675 = 2527013) B2527013
theorem B14398661 : Blo 1684042 14398661 := bstep (se 4 (by rfl) ⟨1349874, by rfl⟩ : syracuseStep 14398661 = 2699749) B2699749
theorem B2528465 : Blo 1684042 2528465 := bstep (se 2 (by rfl) ⟨948174, by rfl⟩ : syracuseStep 2528465 = 1896349) B1896349
theorem B1684691 : Blo 1684042 1684691 := bstep (se 1 (by rfl) ⟨1263518, by rfl⟩ : syracuseStep 1684691 = 2527037) B2527037
theorem B1684707 : Blo 1684042 1684707 := bstep (se 1 (by rfl) ⟨1263530, by rfl⟩ : syracuseStep 1684707 = 2527061) B2527061
theorem B2528483 : Blo 1684042 2528483 := bstep (se 1 (by rfl) ⟨1896362, by rfl⟩ : syracuseStep 2528483 = 3792725) B3792725
theorem B1684723 : Blo 1684042 1684723 := bstep (se 1 (by rfl) ⟨1263542, by rfl⟩ : syracuseStep 1684723 = 2527085) B2527085
theorem B1684739 : Blo 1684042 1684739 := bstep (se 1 (by rfl) ⟨1263554, by rfl⟩ : syracuseStep 1684739 = 2527109) B2527109
theorem B2528513 : Blo 1684042 2528513 := bstep (se 2 (by rfl) ⟨948192, by rfl⟩ : syracuseStep 2528513 = 1896385) B1896385
theorem B3790097 : Blo 1684042 3790097 := bstep (se 2 (by rfl) ⟨1421286, by rfl⟩ : syracuseStep 3790097 = 2842573) B2842573
theorem B1684755 : Blo 1684042 1684755 := bstep (se 1 (by rfl) ⟨1263566, by rfl⟩ : syracuseStep 1684755 = 2527133) B2527133
theorem B2528531 : Blo 1684042 2528531 := bstep (se 1 (by rfl) ⟨1896398, by rfl⟩ : syracuseStep 2528531 = 3792797) B3792797
theorem B3790115 : Blo 1684042 3790115 := bstep (se 1 (by rfl) ⟨2842586, by rfl⟩ : syracuseStep 3790115 = 5685173) B5685173
theorem B1684771 : Blo 1684042 1684771 := bstep (se 1 (by rfl) ⟨1263578, by rfl⟩ : syracuseStep 1684771 = 2527157) B2527157
theorem B4797731 : Blo 1684042 4797731 := bstep (se 1 (by rfl) ⟨3598298, by rfl⟩ : syracuseStep 4797731 = 7196597) B7196597
theorem B2528561 : Blo 1684042 2528561 := bstep (se 2 (by rfl) ⟨948210, by rfl⟩ : syracuseStep 2528561 = 1896421) B1896421
theorem B1684787 : Blo 1684042 1684787 := bstep (se 1 (by rfl) ⟨1263590, by rfl⟩ : syracuseStep 1684787 = 2527181) B2527181
theorem B1684803 : Blo 1684042 1684803 := bstep (se 1 (by rfl) ⟨1263602, by rfl⟩ : syracuseStep 1684803 = 2527205) B2527205
theorem B2528579 : Blo 1684042 2528579 := bstep (se 1 (by rfl) ⟨1896434, by rfl⟩ : syracuseStep 2528579 = 3792869) B3792869
theorem B6395213 : Blo 1684042 6395213 := bstep (se 3 (by rfl) ⟨1199102, by rfl⟩ : syracuseStep 6395213 = 2398205) B2398205
theorem B1684819 : Blo 1684042 1684819 := bstep (se 1 (by rfl) ⟨1263614, by rfl⟩ : syracuseStep 1684819 = 2527229) B2527229
theorem B2528609 : Blo 1684042 2528609 := bstep (se 2 (by rfl) ⟨948228, by rfl⟩ : syracuseStep 2528609 = 1896457) B1896457
theorem B1684835 : Blo 1684042 1684835 := bstep (se 1 (by rfl) ⟨1263626, by rfl⟩ : syracuseStep 1684835 = 2527253) B2527253
theorem B1684851 : Blo 1684042 1684851 := bstep (se 1 (by rfl) ⟨1263638, by rfl⟩ : syracuseStep 1684851 = 2527277) B2527277
theorem B2528627 : Blo 1684042 2528627 := bstep (se 1 (by rfl) ⟨1896470, by rfl⟩ : syracuseStep 2528627 = 3792941) B3792941
theorem B1684867 : Blo 1684042 1684867 := bstep (se 1 (by rfl) ⟨1263650, by rfl⟩ : syracuseStep 1684867 = 2527301) B2527301
theorem B13661581 : Blo 1684042 13661581 := bstep (se 3 (by rfl) ⟨2561546, by rfl⟩ : syracuseStep 13661581 = 5123093) B5123093
theorem B2528657 : Blo 1684042 2528657 := bstep (se 2 (by rfl) ⟨948246, by rfl⟩ : syracuseStep 2528657 = 1896493) B1896493
theorem B3200401 : Blo 1684042 3200401 := bstep (se 2 (by rfl) ⟨1200150, by rfl⟩ : syracuseStep 3200401 = 2400301) B2400301
theorem B1684883 : Blo 1684042 1684883 := bstep (se 1 (by rfl) ⟨1263662, by rfl⟩ : syracuseStep 1684883 = 2527325) B2527325
theorem B1684899 : Blo 1684042 1684899 := bstep (se 1 (by rfl) ⟨1263674, by rfl⟩ : syracuseStep 1684899 = 2527349) B2527349
theorem B2528675 : Blo 1684042 2528675 := bstep (se 1 (by rfl) ⟨1896506, by rfl⟩ : syracuseStep 2528675 = 3793013) B3793013
theorem B1684915 : Blo 1684042 1684915 := bstep (se 1 (by rfl) ⟨1263686, by rfl⟩ : syracuseStep 1684915 = 2527373) B2527373
theorem B2528705 : Blo 1684042 2528705 := bstep (se 2 (by rfl) ⟨948264, by rfl⟩ : syracuseStep 2528705 = 1896529) B1896529
theorem B1684931 : Blo 1684042 1684931 := bstep (se 1 (by rfl) ⟨1263698, by rfl⟩ : syracuseStep 1684931 = 2527397) B2527397
theorem B1684947 : Blo 1684042 1684947 := bstep (se 1 (by rfl) ⟨1263710, by rfl⟩ : syracuseStep 1684947 = 2527421) B2527421
theorem B2528723 : Blo 1684042 2528723 := bstep (se 1 (by rfl) ⟨1896542, by rfl⟩ : syracuseStep 2528723 = 3793085) B3793085
theorem B1684963 : Blo 1684042 1684963 := bstep (se 1 (by rfl) ⟨1263722, by rfl⟩ : syracuseStep 1684963 = 2527445) B2527445
theorem B2528753 : Blo 1684042 2528753 := bstep (se 2 (by rfl) ⟨948282, by rfl⟩ : syracuseStep 2528753 = 1896565) B1896565
theorem B1684979 : Blo 1684042 1684979 := bstep (se 1 (by rfl) ⟨1263734, by rfl⟩ : syracuseStep 1684979 = 2527469) B2527469
theorem B1684995 : Blo 1684042 1684995 := bstep (se 1 (by rfl) ⟨1263746, by rfl⟩ : syracuseStep 1684995 = 2527493) B2527493
theorem B2528771 : Blo 1684042 2528771 := bstep (se 1 (by rfl) ⟨1896578, by rfl⟩ : syracuseStep 2528771 = 3793157) B3793157
theorem B1685011 : Blo 1684042 1685011 := bstep (se 1 (by rfl) ⟨1263758, by rfl⟩ : syracuseStep 1685011 = 2527517) B2527517
theorem B1685027 : Blo 1684042 1685027 := bstep (se 1 (by rfl) ⟨1263770, by rfl⟩ : syracuseStep 1685027 = 2527541) B2527541
theorem B2528801 : Blo 1684042 2528801 := bstep (se 2 (by rfl) ⟨948300, by rfl⟩ : syracuseStep 2528801 = 1896601) B1896601
theorem B3790385 : Blo 1684042 3790385 := bstep (se 2 (by rfl) ⟨1421394, by rfl⟩ : syracuseStep 3790385 = 2842789) B2842789
theorem B1685043 : Blo 1684042 1685043 := bstep (se 1 (by rfl) ⟨1263782, by rfl⟩ : syracuseStep 1685043 = 2527565) B2527565
theorem B2528819 : Blo 1684042 2528819 := bstep (se 1 (by rfl) ⟨1896614, by rfl⟩ : syracuseStep 2528819 = 3793229) B3793229
theorem B1922611 : Blo 1684042 1922611 := bstep (se 1 (by rfl) ⟨1441958, by rfl⟩ : syracuseStep 1922611 = 2883917) B2883917
theorem B3790403 : Blo 1684042 3790403 := bstep (se 1 (by rfl) ⟨2842802, by rfl⟩ : syracuseStep 3790403 = 5685605) B5685605
theorem B1685059 : Blo 1684042 1685059 := bstep (se 1 (by rfl) ⟨1263794, by rfl⟩ : syracuseStep 1685059 = 2527589) B2527589
theorem B2528849 : Blo 1684042 2528849 := bstep (se 2 (by rfl) ⟨948318, by rfl⟩ : syracuseStep 2528849 = 1896637) B1896637
theorem B1685075 : Blo 1684042 1685075 := bstep (se 1 (by rfl) ⟨1263806, by rfl⟩ : syracuseStep 1685075 = 2527613) B2527613
theorem B1685091 : Blo 1684042 1685091 := bstep (se 1 (by rfl) ⟨1263818, by rfl⟩ : syracuseStep 1685091 = 2527637) B2527637
theorem B7198307 : Blo 1684042 7198307 := bstep (se 1 (by rfl) ⟨5398730, by rfl⟩ : syracuseStep 7198307 = 10797461) B10797461
theorem B2528867 : Blo 1684042 2528867 := bstep (se 1 (by rfl) ⟨1896650, by rfl⟩ : syracuseStep 2528867 = 3793301) B3793301
theorem B1685107 : Blo 1684042 1685107 := bstep (se 1 (by rfl) ⟨1263830, by rfl⟩ : syracuseStep 1685107 = 2527661) B2527661
theorem B2528897 : Blo 1684042 2528897 := bstep (se 2 (by rfl) ⟨948336, by rfl⟩ : syracuseStep 2528897 = 1896673) B1896673
theorem B1685123 : Blo 1684042 1685123 := bstep (se 1 (by rfl) ⟨1263842, by rfl⟩ : syracuseStep 1685123 = 2527685) B2527685
theorem B39982733 : Blo 1684042 39982733 := bstep (se 3 (by rfl) ⟨7496762, by rfl⟩ : syracuseStep 39982733 = 14993525) B14993525
theorem B1685139 : Blo 1684042 1685139 := bstep (se 1 (by rfl) ⟨1263854, by rfl⟩ : syracuseStep 1685139 = 2527709) B2527709
theorem B2528915 : Blo 1684042 2528915 := bstep (se 1 (by rfl) ⟨1896686, by rfl⟩ : syracuseStep 2528915 = 3793373) B3793373
theorem B1685155 : Blo 1684042 1685155 := bstep (se 1 (by rfl) ⟨1263866, by rfl⟩ : syracuseStep 1685155 = 2527733) B2527733
theorem B2528945 : Blo 1684042 2528945 := bstep (se 2 (by rfl) ⟨948354, by rfl⟩ : syracuseStep 2528945 = 1896709) B1896709
theorem B1685171 : Blo 1684042 1685171 := bstep (se 1 (by rfl) ⟨1263878, by rfl⟩ : syracuseStep 1685171 = 2527757) B2527757
theorem B1685187 : Blo 1684042 1685187 := bstep (se 1 (by rfl) ⟨1263890, by rfl⟩ : syracuseStep 1685187 = 2527781) B2527781
theorem B2528963 : Blo 1684042 2528963 := bstep (se 1 (by rfl) ⟨1896722, by rfl⟩ : syracuseStep 2528963 = 3793445) B3793445
theorem B34592453 : Blo 1684042 34592453 := bstep (se 4 (by rfl) ⟨3243042, by rfl⟩ : syracuseStep 34592453 = 6486085) B6486085
theorem B1685203 : Blo 1684042 1685203 := bstep (se 1 (by rfl) ⟨1263902, by rfl⟩ : syracuseStep 1685203 = 2527805) B2527805
theorem B2528993 : Blo 1684042 2528993 := bstep (se 2 (by rfl) ⟨948372, by rfl⟩ : syracuseStep 2528993 = 1896745) B1896745
theorem B1685219 : Blo 1684042 1685219 := bstep (se 1 (by rfl) ⟨1263914, by rfl⟩ : syracuseStep 1685219 = 2527829) B2527829
theorem B1685235 : Blo 1684042 1685235 := bstep (se 1 (by rfl) ⟨1263926, by rfl⟩ : syracuseStep 1685235 = 2527853) B2527853
theorem B2529011 : Blo 1684042 2529011 := bstep (se 1 (by rfl) ⟨1896758, by rfl⟩ : syracuseStep 2529011 = 3793517) B3793517
theorem B1685251 : Blo 1684042 1685251 := bstep (se 1 (by rfl) ⟨1263938, by rfl⟩ : syracuseStep 1685251 = 2527877) B2527877
theorem B5764877 : Blo 1684042 5764877 := bstep (se 3 (by rfl) ⟨1080914, by rfl⟩ : syracuseStep 5764877 = 2161829) B2161829
theorem B2529041 : Blo 1684042 2529041 := bstep (se 2 (by rfl) ⟨948390, by rfl⟩ : syracuseStep 2529041 = 1896781) B1896781
theorem B1685267 : Blo 1684042 1685267 := bstep (se 1 (by rfl) ⟨1263950, by rfl⟩ : syracuseStep 1685267 = 2527901) B2527901
theorem B1685283 : Blo 1684042 1685283 := bstep (se 1 (by rfl) ⟨1263962, by rfl⟩ : syracuseStep 1685283 = 2527925) B2527925
theorem B2529059 : Blo 1684042 2529059 := bstep (se 1 (by rfl) ⟨1896794, by rfl⟩ : syracuseStep 2529059 = 3793589) B3793589
theorem B1685299 : Blo 1684042 1685299 := bstep (se 1 (by rfl) ⟨1263974, by rfl⟩ : syracuseStep 1685299 = 2527949) B2527949
theorem B1685315 : Blo 1684042 1685315 := bstep (se 1 (by rfl) ⟨1263986, by rfl⟩ : syracuseStep 1685315 = 2527973) B2527973
theorem B3790673 : Blo 1684042 3790673 := bstep (se 2 (by rfl) ⟨1421502, by rfl⟩ : syracuseStep 3790673 = 2843005) B2843005
theorem B1685331 : Blo 1684042 1685331 := bstep (se 1 (by rfl) ⟨1263998, by rfl⟩ : syracuseStep 1685331 = 2527997) B2527997
theorem B3790691 : Blo 1684042 3790691 := bstep (se 1 (by rfl) ⟨2843018, by rfl⟩ : syracuseStep 3790691 = 5686037) B5686037
theorem B1685347 : Blo 1684042 1685347 := bstep (se 1 (by rfl) ⟨1264010, by rfl⟩ : syracuseStep 1685347 = 2528021) B2528021
theorem B1685363 : Blo 1684042 1685363 := bstep (se 1 (by rfl) ⟨1264022, by rfl⟩ : syracuseStep 1685363 = 2528045) B2528045
theorem B1685379 : Blo 1684042 1685379 := bstep (se 1 (by rfl) ⟨1264034, by rfl⟩ : syracuseStep 1685379 = 2528069) B2528069
theorem B1685395 : Blo 1684042 1685395 := bstep (se 1 (by rfl) ⟨1264046, by rfl⟩ : syracuseStep 1685395 = 2528093) B2528093
theorem B1685411 : Blo 1684042 1685411 := bstep (se 1 (by rfl) ⟨1264058, by rfl⟩ : syracuseStep 1685411 = 2528117) B2528117
theorem B4265905 : Blo 1684042 4265905 := bstep (se 2 (by rfl) ⟨1599714, by rfl⟩ : syracuseStep 4265905 = 3199429) B3199429
theorem B1685427 : Blo 1684042 1685427 := bstep (se 1 (by rfl) ⟨1264070, by rfl⟩ : syracuseStep 1685427 = 2528141) B2528141
theorem B1685443 : Blo 1684042 1685443 := bstep (se 1 (by rfl) ⟨1264082, by rfl⟩ : syracuseStep 1685443 = 2528165) B2528165
theorem B9598925 : Blo 1684042 9598925 := bstep (se 3 (by rfl) ⟨1799798, by rfl⟩ : syracuseStep 9598925 = 3599597) B3599597
theorem B1685459 : Blo 1684042 1685459 := bstep (se 1 (by rfl) ⟨1264094, by rfl⟩ : syracuseStep 1685459 = 2528189) B2528189
theorem B2398177 : Blo 1684042 2398177 := bstep (se 2 (by rfl) ⟨899316, by rfl⟩ : syracuseStep 2398177 = 1798633) B1798633
theorem B1685475 : Blo 1684042 1685475 := bstep (se 1 (by rfl) ⟨1264106, by rfl⟩ : syracuseStep 1685475 = 2528213) B2528213
theorem B1685491 : Blo 1684042 1685491 := bstep (se 1 (by rfl) ⟨1264118, by rfl⟩ : syracuseStep 1685491 = 2528237) B2528237
theorem B1685507 : Blo 1684042 1685507 := bstep (se 1 (by rfl) ⟨1264130, by rfl⟩ : syracuseStep 1685507 = 2528261) B2528261
theorem B1685523 : Blo 1684042 1685523 := bstep (se 1 (by rfl) ⟨1264142, by rfl⟩ : syracuseStep 1685523 = 2528285) B2528285
theorem B1685539 : Blo 1684042 1685539 := bstep (se 1 (by rfl) ⟨1264154, by rfl⟩ : syracuseStep 1685539 = 2528309) B2528309
theorem B1685555 : Blo 1684042 1685555 := bstep (se 1 (by rfl) ⟨1264166, by rfl⟩ : syracuseStep 1685555 = 2528333) B2528333
theorem B1685571 : Blo 1684042 1685571 := bstep (se 1 (by rfl) ⟨1264178, by rfl⟩ : syracuseStep 1685571 = 2528357) B2528357
theorem B4798541 : Blo 1684042 4798541 := bstep (se 3 (by rfl) ⟨899726, by rfl⟩ : syracuseStep 4798541 = 1799453) B1799453
theorem B2562131 : Blo 1684042 2562131 := bstep (se 1 (by rfl) ⟨1921598, by rfl⟩ : syracuseStep 2562131 = 3843197) B3843197
theorem B1685587 : Blo 1684042 1685587 := bstep (se 1 (by rfl) ⟨1264190, by rfl⟩ : syracuseStep 1685587 = 2528381) B2528381
theorem B1685603 : Blo 1684042 1685603 := bstep (se 1 (by rfl) ⟨1264202, by rfl⟩ : syracuseStep 1685603 = 2528405) B2528405
theorem B3790961 : Blo 1684042 3790961 := bstep (se 2 (by rfl) ⟨1421610, by rfl⟩ : syracuseStep 3790961 = 2843221) B2843221
theorem B1685619 : Blo 1684042 1685619 := bstep (se 1 (by rfl) ⟨1264214, by rfl⟩ : syracuseStep 1685619 = 2528429) B2528429
theorem B3790979 : Blo 1684042 3790979 := bstep (se 1 (by rfl) ⟨2843234, by rfl⟩ : syracuseStep 3790979 = 5686469) B5686469
theorem B1685635 : Blo 1684042 1685635 := bstep (se 1 (by rfl) ⟨1264226, by rfl⟩ : syracuseStep 1685635 = 2528453) B2528453
theorem B1685651 : Blo 1684042 1685651 := bstep (se 1 (by rfl) ⟨1264238, by rfl⟩ : syracuseStep 1685651 = 2528477) B2528477
theorem B1685667 : Blo 1684042 1685667 := bstep (se 1 (by rfl) ⟨1264250, by rfl⟩ : syracuseStep 1685667 = 2528501) B2528501
theorem B1685683 : Blo 1684042 1685683 := bstep (se 1 (by rfl) ⟨1264262, by rfl⟩ : syracuseStep 1685683 = 2528525) B2528525
theorem B4266179 : Blo 1684042 4266179 := bstep (se 1 (by rfl) ⟨3199634, by rfl⟩ : syracuseStep 4266179 = 6399269) B6399269
theorem B1685699 : Blo 1684042 1685699 := bstep (se 1 (by rfl) ⟨1264274, by rfl⟩ : syracuseStep 1685699 = 2528549) B2528549
theorem B1685715 : Blo 1684042 1685715 := bstep (se 1 (by rfl) ⟨1264286, by rfl⟩ : syracuseStep 1685715 = 2528573) B2528573
theorem B1685731 : Blo 1684042 1685731 := bstep (se 1 (by rfl) ⟨1264298, by rfl⟩ : syracuseStep 1685731 = 2528597) B2528597
theorem B1685747 : Blo 1684042 1685747 := bstep (se 1 (by rfl) ⟨1264310, by rfl⟩ : syracuseStep 1685747 = 2528621) B2528621
theorem B4798723 : Blo 1684042 4798723 := bstep (se 1 (by rfl) ⟨3599042, by rfl⟩ : syracuseStep 4798723 = 7198085) B7198085
theorem B1685763 : Blo 1684042 1685763 := bstep (se 1 (by rfl) ⟨1264322, by rfl⟩ : syracuseStep 1685763 = 2528645) B2528645
theorem B1685779 : Blo 1684042 1685779 := bstep (se 1 (by rfl) ⟨1264334, by rfl⟩ : syracuseStep 1685779 = 2528669) B2528669
theorem B1685795 : Blo 1684042 1685795 := bstep (se 1 (by rfl) ⟨1264346, by rfl⟩ : syracuseStep 1685795 = 2528693) B2528693
theorem B2398513 : Blo 1684042 2398513 := bstep (se 2 (by rfl) ⟨899442, by rfl⟩ : syracuseStep 2398513 = 1798885) B1798885
theorem B8534321 : Blo 1684042 8534321 := bstep (se 2 (by rfl) ⟨3200370, by rfl⟩ : syracuseStep 8534321 = 6400741) B6400741
theorem B1685811 : Blo 1684042 1685811 := bstep (se 1 (by rfl) ⟨1264358, by rfl⟩ : syracuseStep 1685811 = 2528717) B2528717
theorem B1685827 : Blo 1684042 1685827 := bstep (se 1 (by rfl) ⟨1264370, by rfl⟩ : syracuseStep 1685827 = 2528741) B2528741
theorem B1685843 : Blo 1684042 1685843 := bstep (se 1 (by rfl) ⟨1264382, by rfl⟩ : syracuseStep 1685843 = 2528765) B2528765
theorem B18209123 : Blo 1684042 18209123 := bstep (se 1 (by rfl) ⟨13656842, by rfl⟩ : syracuseStep 18209123 = 27313685) B27313685
theorem B4553059 : Blo 1684042 4553059 := bstep (se 1 (by rfl) ⟨3414794, by rfl⟩ : syracuseStep 4553059 = 6829589) B6829589
theorem B1685859 : Blo 1684042 1685859 := bstep (se 1 (by rfl) ⟨1264394, by rfl⟩ : syracuseStep 1685859 = 2528789) B2528789
theorem B1685875 : Blo 1684042 1685875 := bstep (se 1 (by rfl) ⟨1264406, by rfl⟩ : syracuseStep 1685875 = 2528813) B2528813
theorem B4266371 : Blo 1684042 4266371 := bstep (se 1 (by rfl) ⟨3199778, by rfl⟩ : syracuseStep 4266371 = 6399557) B6399557
theorem B1685891 : Blo 1684042 1685891 := bstep (se 1 (by rfl) ⟨1264418, by rfl⟩ : syracuseStep 1685891 = 2528837) B2528837
theorem B8526221 : Blo 1684042 8526221 := bstep (se 3 (by rfl) ⟨1598666, by rfl⟩ : syracuseStep 8526221 = 3197333) B3197333
theorem B3791249 : Blo 1684042 3791249 := bstep (se 2 (by rfl) ⟨1421718, by rfl⟩ : syracuseStep 3791249 = 2843437) B2843437
theorem B1685907 : Blo 1684042 1685907 := bstep (se 1 (by rfl) ⟨1264430, by rfl⟩ : syracuseStep 1685907 = 2528861) B2528861
theorem B3791267 : Blo 1684042 3791267 := bstep (se 1 (by rfl) ⟨2843450, by rfl⟩ : syracuseStep 3791267 = 5686901) B5686901
theorem B1685923 : Blo 1684042 1685923 := bstep (se 1 (by rfl) ⟨1264442, by rfl⟩ : syracuseStep 1685923 = 2528885) B2528885
theorem B1685939 : Blo 1684042 1685939 := bstep (se 1 (by rfl) ⟨1264454, by rfl⟩ : syracuseStep 1685939 = 2528909) B2528909
theorem B1685955 : Blo 1684042 1685955 := bstep (se 1 (by rfl) ⟨1264466, by rfl⟩ : syracuseStep 1685955 = 2528933) B2528933
theorem B5683661 : Blo 1684042 5683661 := bstep (se 3 (by rfl) ⟨1065686, by rfl⟩ : syracuseStep 5683661 = 2131373) B2131373
theorem B1685971 : Blo 1684042 1685971 := bstep (se 1 (by rfl) ⟨1264478, by rfl⟩ : syracuseStep 1685971 = 2528957) B2528957
theorem B20765155 : Blo 1684042 20765155 := bstep (se 1 (by rfl) ⟨15573866, by rfl⟩ : syracuseStep 20765155 = 31147733) B31147733
theorem B1685987 : Blo 1684042 1685987 := bstep (se 1 (by rfl) ⟨1264490, by rfl⟩ : syracuseStep 1685987 = 2528981) B2528981
theorem B1686003 : Blo 1684042 1686003 := bstep (se 1 (by rfl) ⟨1264502, by rfl⟩ : syracuseStep 1686003 = 2529005) B2529005
theorem B5683715 : Blo 1684042 5683715 := bstep (se 1 (by rfl) ⟨4262786, by rfl⟩ : syracuseStep 5683715 = 8525573) B8525573
theorem B1686019 : Blo 1684042 1686019 := bstep (se 1 (by rfl) ⟨1264514, by rfl⟩ : syracuseStep 1686019 = 2529029) B2529029
theorem B2734609 : Blo 1684042 2734609 := bstep (se 2 (by rfl) ⟨1025478, by rfl⟩ : syracuseStep 2734609 = 2050957) B2050957
theorem B1686035 : Blo 1684042 1686035 := bstep (se 1 (by rfl) ⟨1264526, by rfl⟩ : syracuseStep 1686035 = 2529053) B2529053
theorem B28785293 : Blo 1684042 28785293 := bstep (se 3 (by rfl) ⟨5397242, by rfl⟩ : syracuseStep 28785293 = 10794485) B10794485
theorem B3791537 : Blo 1684042 3791537 := bstep (se 2 (by rfl) ⟨1421826, by rfl⟩ : syracuseStep 3791537 = 2843653) B2843653
theorem B3791555 : Blo 1684042 3791555 := bstep (se 1 (by rfl) ⟨2843666, by rfl⟩ : syracuseStep 3791555 = 5687333) B5687333
theorem B8100557 : Blo 1684042 8100557 := bstep (se 3 (by rfl) ⟨1518854, by rfl⟩ : syracuseStep 8100557 = 3037709) B3037709
theorem B4799213 : Blo 1684042 4799213 := bstep (se 3 (by rfl) ⟨899852, by rfl⟩ : syracuseStep 4799213 = 1799705) B1799705
theorem B5683985 : Blo 1684042 5683985 := bstep (se 2 (by rfl) ⟨2131494, by rfl⟩ : syracuseStep 5683985 = 4262989) B4262989
theorem B2399105 : Blo 1684042 2399105 := bstep (se 2 (by rfl) ⟨899664, by rfl⟩ : syracuseStep 2399105 = 1799329) B1799329
theorem B8100785 : Blo 1684042 8100785 := bstep (se 2 (by rfl) ⟨3037794, by rfl⟩ : syracuseStep 8100785 = 6075589) B6075589
theorem B62307269 : Blo 1684042 62307269 := bstep (se 4 (by rfl) ⟨5841306, by rfl⟩ : syracuseStep 62307269 = 11682613) B11682613
theorem B3791825 : Blo 1684042 3791825 := bstep (se 2 (by rfl) ⟨1421934, by rfl⟩ : syracuseStep 3791825 = 2843869) B2843869
theorem B5397475 : Blo 1684042 5397475 := bstep (se 1 (by rfl) ⟨4048106, by rfl⟩ : syracuseStep 5397475 = 8096213) B8096213
theorem B3791843 : Blo 1684042 3791843 := bstep (se 1 (by rfl) ⟨2843882, by rfl⟩ : syracuseStep 3791843 = 5687765) B5687765
theorem B30727309 : Blo 1684042 30727309 := bstep (se 3 (by rfl) ⟨5761370, by rfl⟩ : syracuseStep 30727309 = 11522741) B11522741
theorem B3792113 : Blo 1684042 3792113 := bstep (se 2 (by rfl) ⟨1422042, by rfl⟩ : syracuseStep 3792113 = 2844085) B2844085
theorem B3792131 : Blo 1684042 3792131 := bstep (se 1 (by rfl) ⟨2844098, by rfl⟩ : syracuseStep 3792131 = 5688197) B5688197
theorem B5684525 : Blo 1684042 5684525 := bstep (se 3 (by rfl) ⟨1065848, by rfl⟩ : syracuseStep 5684525 = 2131697) B2131697
theorem B2841905 : Blo 1684042 2841905 := bstep (se 2 (by rfl) ⟨1065714, by rfl⟩ : syracuseStep 2841905 = 2131429) B2131429
theorem B7200049 : Blo 1684042 7200049 := bstep (se 2 (by rfl) ⟨2700018, by rfl⟩ : syracuseStep 7200049 = 5400037) B5400037
theorem B4267313 : Blo 1684042 4267313 := bstep (se 2 (by rfl) ⟨1600242, by rfl⟩ : syracuseStep 4267313 = 3200485) B3200485
theorem B5684579 : Blo 1684042 5684579 := bstep (se 1 (by rfl) ⟨4263434, by rfl⟩ : syracuseStep 5684579 = 8526869) B8526869
theorem B4267363 : Blo 1684042 4267363 := bstep (se 1 (by rfl) ⟨3200522, by rfl⟩ : syracuseStep 4267363 = 6401045) B6401045
theorem B6397325 : Blo 1684042 6397325 := bstep (se 3 (by rfl) ⟨1199498, by rfl⟩ : syracuseStep 6397325 = 2398997) B2398997
theorem B2399635 : Blo 1684042 2399635 := bstep (se 1 (by rfl) ⟨1799726, by rfl⟩ : syracuseStep 2399635 = 3599453) B3599453
theorem B2842033 : Blo 1684042 2842033 := bstep (se 2 (by rfl) ⟨1065762, by rfl⟩ : syracuseStep 2842033 = 2131525) B2131525
theorem B2563505 : Blo 1684042 2563505 := bstep (se 2 (by rfl) ⟨961314, by rfl⟩ : syracuseStep 2563505 = 1922629) B1922629
theorem B21052853 : Blo 1684042 21052853 := bstep (se 5 (by rfl) ⟨986852, by rfl⟩ : syracuseStep 21052853 = 1973705) B1973705
theorem B2842067 : Blo 1684042 2842067 := bstep (se 1 (by rfl) ⟨2131550, by rfl⟩ : syracuseStep 2842067 = 4263101) B4263101
theorem B24305123 : Blo 1684042 24305123 := bstep (se 1 (by rfl) ⟨18228842, by rfl⟩ : syracuseStep 24305123 = 36457685) B36457685
theorem B4267505 : Blo 1684042 4267505 := bstep (se 2 (by rfl) ⟨1600314, by rfl⟩ : syracuseStep 4267505 = 3200629) B3200629
theorem B3792401 : Blo 1684042 3792401 := bstep (se 2 (by rfl) ⟨1422150, by rfl⟩ : syracuseStep 3792401 = 2844301) B2844301
theorem B2596385 : Blo 1684042 2596385 := bstep (se 2 (by rfl) ⟨973644, by rfl⟩ : syracuseStep 2596385 = 1947289) B1947289
theorem B3792419 : Blo 1684042 3792419 := bstep (se 1 (by rfl) ⟨2844314, by rfl⟩ : syracuseStep 3792419 = 5688629) B5688629
theorem B66534965 : Blo 1684042 66534965 := bstep (se 5 (by rfl) ⟨3118826, by rfl⟩ : syracuseStep 66534965 = 6237653) B6237653
theorem B9109061 : Blo 1684042 9109061 := bstep (se 4 (by rfl) ⟨853974, by rfl⟩ : syracuseStep 9109061 = 1707949) B1707949
theorem B2842195 : Blo 1684042 2842195 := bstep (se 1 (by rfl) ⟨2131646, by rfl⟩ : syracuseStep 2842195 = 4263293) B4263293
theorem B5684849 : Blo 1684042 5684849 := bstep (se 2 (by rfl) ⟨2131818, by rfl⟩ : syracuseStep 5684849 = 4263637) B4263637
theorem B2842337 : Blo 1684042 2842337 := bstep (se 2 (by rfl) ⟨1065876, by rfl⟩ : syracuseStep 2842337 = 2131753) B2131753
theorem B2399971 : Blo 1684042 2399971 := bstep (se 1 (by rfl) ⟨1799978, by rfl⟩ : syracuseStep 2399971 = 3599957) B3599957
theorem B3792689 : Blo 1684042 3792689 := bstep (se 2 (by rfl) ⟨1422258, by rfl⟩ : syracuseStep 3792689 = 2844517) B2844517
theorem B3792707 : Blo 1684042 3792707 := bstep (se 1 (by rfl) ⟨2844530, by rfl⟩ : syracuseStep 3792707 = 5689061) B5689061
theorem B2842465 : Blo 1684042 2842465 := bstep (se 2 (by rfl) ⟨1065924, by rfl⟩ : syracuseStep 2842465 = 2131849) B2131849
theorem B2842499 : Blo 1684042 2842499 := bstep (se 1 (by rfl) ⟨2131874, by rfl⟩ : syracuseStep 2842499 = 4263749) B4263749
theorem B4800397 : Blo 1684042 4800397 := bstep (se 3 (by rfl) ⟨900074, by rfl⟩ : syracuseStep 4800397 = 1800149) B1800149
theorem B2883505 : Blo 1684042 2883505 := bstep (se 2 (by rfl) ⟨1081314, by rfl⟩ : syracuseStep 2883505 = 2162629) B2162629
theorem B16408669 : Blo 1684042 16408669 := bstep (se 3 (by rfl) ⟨3076625, by rfl⟩ : syracuseStep 16408669 = 6153251) B6153251
theorem B14401637 : Blo 1684042 14401637 := bstep (se 4 (by rfl) ⟨1350153, by rfl⟩ : syracuseStep 14401637 = 2700307) B2700307
theorem B8528003 : Blo 1684042 8528003 := bstep (se 1 (by rfl) ⟨6396002, by rfl⟩ : syracuseStep 8528003 = 12792005) B12792005
theorem B3793049 : Blo 1684042 3793049 := bstep (se 2 (by rfl) ⟨1422393, by rfl⟩ : syracuseStep 3793049 = 2844787) B2844787
theorem B7200971 : Blo 1684042 7200971 := bstep (se 1 (by rfl) ⟨5400728, by rfl⟩ : syracuseStep 7200971 = 10801457) B10801457
theorem B6832349 : Blo 1684042 6832349 := bstep (se 3 (by rfl) ⟨1281065, by rfl⟩ : syracuseStep 6832349 = 2562131) B2562131
theorem B3793139 : Blo 1684042 3793139 := bstep (se 1 (by rfl) ⟨2844854, by rfl⟩ : syracuseStep 3793139 = 5689709) B5689709
theorem B5398807 : Blo 1684042 5398807 := bstep (se 1 (by rfl) ⟨4049105, by rfl⟩ : syracuseStep 5398807 = 8098211) B8098211
theorem B3793175 : Blo 1684042 3793175 := bstep (se 1 (by rfl) ⟨2844881, by rfl⟩ : syracuseStep 3793175 = 5689763) B5689763
theorem B6398297 : Blo 1684042 6398297 := bstep (se 2 (by rfl) ⟨2399361, by rfl⟩ : syracuseStep 6398297 = 4798723) B4798723
theorem B81944945 : Blo 1684042 81944945 := bstep (se 2 (by rfl) ⟨30729354, by rfl⟩ : syracuseStep 81944945 = 61458709) B61458709
theorem B3793355 : Blo 1684042 3793355 := bstep (se 1 (by rfl) ⟨2845016, by rfl⟩ : syracuseStep 3793355 = 5690033) B5690033
theorem B3596761 : Blo 1684042 3596761 := bstep (se 2 (by rfl) ⟨1348785, by rfl⟩ : syracuseStep 3596761 = 2697571) B2697571
theorem B6070745 : Blo 1684042 6070745 := bstep (se 2 (by rfl) ⟨2276529, by rfl⟩ : syracuseStep 6070745 = 4553059) B4553059
theorem B3793409 : Blo 1684042 3793409 := bstep (se 2 (by rfl) ⟨1422528, by rfl⟩ : syracuseStep 3793409 = 2845057) B2845057
theorem B2843147 : Blo 1684042 2843147 := bstep (se 1 (by rfl) ⟨2132360, by rfl⟩ : syracuseStep 2843147 = 4264721) B4264721
theorem B2843275 : Blo 1684042 2843275 := bstep (se 1 (by rfl) ⟨2132456, by rfl⟩ : syracuseStep 2843275 = 4264913) B4264913
theorem B6398615 : Blo 1684042 6398615 := bstep (se 1 (by rfl) ⟨4798961, by rfl⟩ : syracuseStep 6398615 = 9597923) B9597923
theorem B2278039 : Blo 1684042 2278039 := bstep (se 1 (by rfl) ⟨1708529, by rfl⟩ : syracuseStep 2278039 = 3417059) B3417059
theorem B3646145 : Blo 1684042 3646145 := bstep (se 2 (by rfl) ⟨1367304, by rfl⟩ : syracuseStep 3646145 = 2734609) B2734609
theorem B5399243 : Blo 1684042 5399243 := bstep (se 1 (by rfl) ⟨4049432, by rfl⟩ : syracuseStep 5399243 = 8098865) B8098865
theorem B2843417 : Blo 1684042 2843417 := bstep (se 2 (by rfl) ⟨1066281, by rfl⟩ : syracuseStep 2843417 = 2132563) B2132563
theorem B5686091 : Blo 1684042 5686091 := bstep (se 1 (by rfl) ⟨4264568, by rfl⟩ : syracuseStep 5686091 = 8529137) B8529137
theorem B2843545 : Blo 1684042 2843545 := bstep (se 2 (by rfl) ⟨1066329, by rfl⟩ : syracuseStep 2843545 = 2132659) B2132659
theorem B2737099 : Blo 1684042 2737099 := bstep (se 1 (by rfl) ⟨2052824, by rfl⟩ : syracuseStep 2737099 = 4105649) B4105649
theorem B2278487 : Blo 1684042 2278487 := bstep (se 1 (by rfl) ⟨1708865, by rfl⟩ : syracuseStep 2278487 = 3417731) B3417731
theorem B5686361 : Blo 1684042 5686361 := bstep (se 2 (by rfl) ⟨2132385, by rfl⟩ : syracuseStep 5686361 = 4264771) B4264771
theorem B5473373 : Blo 1684042 5473373 := bstep (se 3 (by rfl) ⟨1026257, by rfl⟩ : syracuseStep 5473373 = 2052515) B2052515
theorem B23061635 : Blo 1684042 23061635 := bstep (se 1 (by rfl) ⟨17296226, by rfl⟩ : syracuseStep 23061635 = 34592453) B34592453
theorem B3843251 : Blo 1684042 3843251 := bstep (se 1 (by rfl) ⟨2882438, by rfl⟩ : syracuseStep 3843251 = 5764877) B5764877
theorem B6399283 : Blo 1684042 6399283 := bstep (se 1 (by rfl) ⟨4799462, by rfl⟩ : syracuseStep 6399283 = 9598925) B9598925
theorem B6833483 : Blo 1684042 6833483 := bstep (se 1 (by rfl) ⟨5125112, by rfl⟩ : syracuseStep 6833483 = 10250225) B10250225
theorem B6923693 : Blo 1684042 6923693 := bstep (se 3 (by rfl) ⟨1298192, by rfl⟩ : syracuseStep 6923693 = 2596385) B2596385
theorem B7194035 : Blo 1684042 7194035 := bstep (se 1 (by rfl) ⟨5395526, by rfl⟩ : syracuseStep 7194035 = 10791053) B10791053
theorem B2844119 : Blo 1684042 2844119 := bstep (se 1 (by rfl) ⟨2133089, by rfl⟩ : syracuseStep 2844119 = 4266179) B4266179
theorem B27313625 : Blo 1684042 27313625 := bstep (se 2 (by rfl) ⟨10242609, by rfl⟩ : syracuseStep 27313625 = 20485219) B20485219
theorem B40969745 : Blo 1684042 40969745 := bstep (se 2 (by rfl) ⟨15363654, by rfl⟩ : syracuseStep 40969745 = 30727309) B30727309
theorem B8095249 : Blo 1684042 8095249 := bstep (se 2 (by rfl) ⟨3035718, by rfl⟩ : syracuseStep 8095249 = 6071437) B6071437
theorem B2844247 : Blo 1684042 2844247 := bstep (se 1 (by rfl) ⟨2133185, by rfl⟩ : syracuseStep 2844247 = 4266371) B4266371
theorem B13665923 : Blo 1684042 13665923 := bstep (se 1 (by rfl) ⟨10249442, by rfl⟩ : syracuseStep 13665923 = 20498885) B20498885
theorem B5687063 : Blo 1684042 5687063 := bstep (se 1 (by rfl) ⟨4265297, by rfl⟩ : syracuseStep 5687063 = 8530595) B8530595
theorem B5400371 : Blo 1684042 5400371 := bstep (se 1 (by rfl) ⟨4050278, by rfl⟩ : syracuseStep 5400371 = 8100557) B8100557
theorem B10250077 : Blo 1684042 10250077 := bstep (se 3 (by rfl) ⟨1921889, by rfl⟩ : syracuseStep 10250077 = 3843779) B3843779
theorem B2131915 : Blo 1684042 2131915 := bstep (se 1 (by rfl) ⟨1598936, by rfl⟩ : syracuseStep 2131915 = 3197873) B3197873
theorem B5400523 : Blo 1684042 5400523 := bstep (se 1 (by rfl) ⟨4050392, by rfl⟩ : syracuseStep 5400523 = 8100785) B8100785
theorem B1894603 : Blo 1684042 1894603 := bstep (se 1 (by rfl) ⟨1420952, by rfl⟩ : syracuseStep 1894603 = 2841905) B2841905
theorem B2844875 : Blo 1684042 2844875 := bstep (se 1 (by rfl) ⟨2133656, by rfl⟩ : syracuseStep 2844875 = 4267313) B4267313
theorem B2132183 : Blo 1684042 2132183 := bstep (se 1 (by rfl) ⟨1599137, by rfl⟩ : syracuseStep 2132183 = 3198275) B3198275
theorem B14035235 : Blo 1684042 14035235 := bstep (se 1 (by rfl) ⟨10526426, by rfl⟩ : syracuseStep 14035235 = 21052853) B21052853
theorem B12790061 : Blo 1684042 12790061 := bstep (se 3 (by rfl) ⟨2398136, by rfl⟩ : syracuseStep 12790061 = 4796273) B4796273
theorem B5687603 : Blo 1684042 5687603 := bstep (se 1 (by rfl) ⟨4265702, by rfl⟩ : syracuseStep 5687603 = 8531405) B8531405
theorem B1894711 : Blo 1684042 1894711 := bstep (se 1 (by rfl) ⟨1421033, by rfl⟩ : syracuseStep 1894711 = 2842067) B2842067
theorem B2845003 : Blo 1684042 2845003 := bstep (se 1 (by rfl) ⟨2133752, by rfl⟩ : syracuseStep 2845003 = 4267505) B4267505
theorem B6072707 : Blo 1684042 6072707 := bstep (se 1 (by rfl) ⟨4554530, by rfl⟩ : syracuseStep 6072707 = 9109061) B9109061
theorem B5401025 : Blo 1684042 5401025 := bstep (se 2 (by rfl) ⟨2025384, by rfl⟩ : syracuseStep 5401025 = 4050769) B4050769
theorem B3197387 : Blo 1684042 3197387 := bstep (se 1 (by rfl) ⟨2398040, by rfl⟩ : syracuseStep 3197387 = 4796081) B4796081
theorem B2845145 : Blo 1684042 2845145 := bstep (se 2 (by rfl) ⟨1066929, by rfl⟩ : syracuseStep 2845145 = 2133859) B2133859
theorem B1894891 : Blo 1684042 1894891 := bstep (se 1 (by rfl) ⟨1421168, by rfl⟩ : syracuseStep 1894891 = 2842337) B2842337
theorem B6400529 : Blo 1684042 6400529 := bstep (se 2 (by rfl) ⟨2400198, by rfl⟩ : syracuseStep 6400529 = 4800397) B4800397
theorem B5687873 : Blo 1684042 5687873 := bstep (se 2 (by rfl) ⟨2132952, by rfl⟩ : syracuseStep 5687873 = 4265905) B4265905
theorem B3844673 : Blo 1684042 3844673 := bstep (se 2 (by rfl) ⟨1441752, by rfl⟩ : syracuseStep 3844673 = 2883505) B2883505
theorem B1894999 : Blo 1684042 1894999 := bstep (se 1 (by rfl) ⟨1421249, by rfl⟩ : syracuseStep 1894999 = 2842499) B2842499
theorem B3197569 : Blo 1684042 3197569 := bstep (se 2 (by rfl) ⟨1199088, by rfl⟩ : syracuseStep 3197569 = 2398177) B2398177
theorem B61524677 : Blo 1684042 61524677 := bstep (se 4 (by rfl) ⟨5767938, by rfl⟩ : syracuseStep 61524677 = 11535877) B11535877
theorem B1895179 : Blo 1684042 1895179 := bstep (se 1 (by rfl) ⟨1421384, by rfl⟩ : syracuseStep 1895179 = 2842769) B2842769
theorem B1895287 : Blo 1684042 1895287 := bstep (se 1 (by rfl) ⟨1421465, by rfl⟩ : syracuseStep 1895287 = 2842931) B2842931
theorem B4262807 : Blo 1684042 4262807 := bstep (se 1 (by rfl) ⟨3197105, by rfl⟩ : syracuseStep 4262807 = 6394211) B6394211
theorem B2132887 : Blo 1684042 2132887 := bstep (se 1 (by rfl) ⟨1599665, by rfl⟩ : syracuseStep 2132887 = 3199331) B3199331
theorem B2526155 : Blo 1684042 2526155 := bstep (se 1 (by rfl) ⟨1894616, by rfl⟩ : syracuseStep 2526155 = 3789233) B3789233
theorem B2526167 : Blo 1684042 2526167 := bstep (se 1 (by rfl) ⟨1894625, by rfl⟩ : syracuseStep 2526167 = 3789251) B3789251
theorem B2526233 : Blo 1684042 2526233 := bstep (se 2 (by rfl) ⟨947337, by rfl⟩ : syracuseStep 2526233 = 1894675) B1894675
theorem B1895467 : Blo 1684042 1895467 := bstep (se 1 (by rfl) ⟨1421600, by rfl⟩ : syracuseStep 1895467 = 2843201) B2843201
theorem B3198017 : Blo 1684042 3198017 := bstep (se 2 (by rfl) ⟨1199256, by rfl⟩ : syracuseStep 3198017 = 2398513) B2398513
theorem B5688413 : Blo 1684042 5688413 := bstep (se 3 (by rfl) ⟨1066577, by rfl⟩ : syracuseStep 5688413 = 2133155) B2133155
theorem B2526347 : Blo 1684042 2526347 := bstep (se 1 (by rfl) ⟨1894760, by rfl⟩ : syracuseStep 2526347 = 3789521) B3789521
theorem B2526359 : Blo 1684042 2526359 := bstep (se 1 (by rfl) ⟨1894769, by rfl⟩ : syracuseStep 2526359 = 3789539) B3789539
theorem B2698391 : Blo 1684042 2698391 := bstep (se 1 (by rfl) ⟨2023793, by rfl⟩ : syracuseStep 2698391 = 4047587) B4047587
theorem B1895575 : Blo 1684042 1895575 := bstep (se 1 (by rfl) ⟨1421681, by rfl⟩ : syracuseStep 1895575 = 2843363) B2843363
theorem B5123251 : Blo 1684042 5123251 := bstep (se 1 (by rfl) ⟨3842438, by rfl⟩ : syracuseStep 5123251 = 7684877) B7684877
theorem B6401227 : Blo 1684042 6401227 := bstep (se 1 (by rfl) ⟨4800920, by rfl⟩ : syracuseStep 6401227 = 9601841) B9601841
theorem B3648727 : Blo 1684042 3648727 := bstep (se 1 (by rfl) ⟨2736545, by rfl⟩ : syracuseStep 3648727 = 5473091) B5473091
theorem B2526425 : Blo 1684042 2526425 := bstep (se 2 (by rfl) ⟨947409, by rfl⟩ : syracuseStep 2526425 = 1894819) B1894819
theorem B2698519 : Blo 1684042 2698519 := bstep (se 1 (by rfl) ⟨2023889, by rfl⟩ : syracuseStep 2698519 = 4047779) B4047779
theorem B14388515 : Blo 1684042 14388515 := bstep (se 1 (by rfl) ⟨10791386, by rfl⟩ : syracuseStep 14388515 = 21582773) B21582773
theorem B7195949 : Blo 1684042 7195949 := bstep (se 3 (by rfl) ⟨1349240, by rfl⟩ : syracuseStep 7195949 = 2698481) B2698481
theorem B2526539 : Blo 1684042 2526539 := bstep (se 1 (by rfl) ⟨1894904, by rfl⟩ : syracuseStep 2526539 = 3789809) B3789809
theorem B2698571 : Blo 1684042 2698571 := bstep (se 1 (by rfl) ⟨2023928, by rfl⟩ : syracuseStep 2698571 = 4047857) B4047857
theorem B1895755 : Blo 1684042 1895755 := bstep (se 1 (by rfl) ⟨1421816, by rfl⟩ : syracuseStep 1895755 = 2843633) B2843633
theorem B2526551 : Blo 1684042 2526551 := bstep (se 1 (by rfl) ⟨1894913, by rfl⟩ : syracuseStep 2526551 = 3789827) B3789827
theorem B10800485 : Blo 1684042 10800485 := bstep (se 4 (by rfl) ⟨1012545, by rfl⟩ : syracuseStep 10800485 = 2025091) B2025091
theorem B3198359 : Blo 1684042 3198359 := bstep (se 1 (by rfl) ⟨2398769, by rfl⟩ : syracuseStep 3198359 = 4797539) B4797539
theorem B2526617 : Blo 1684042 2526617 := bstep (se 2 (by rfl) ⟨947481, by rfl⟩ : syracuseStep 2526617 = 1894963) B1894963
theorem B3599795 : Blo 1684042 3599795 := bstep (se 1 (by rfl) ⟨2699846, by rfl⟩ : syracuseStep 3599795 = 5399693) B5399693
theorem B1895863 : Blo 1684042 1895863 := bstep (se 1 (by rfl) ⟨1421897, by rfl⟩ : syracuseStep 1895863 = 2843795) B2843795
theorem B4795841 : Blo 1684042 4795841 := bstep (se 2 (by rfl) ⟨1798440, by rfl⟩ : syracuseStep 4795841 = 3596881) B3596881
theorem B2698699 : Blo 1684042 2698699 := bstep (se 1 (by rfl) ⟨2024024, by rfl⟩ : syracuseStep 2698699 = 4048049) B4048049
theorem B6401501 : Blo 1684042 6401501 := bstep (se 3 (by rfl) ⟨1200281, by rfl⟩ : syracuseStep 6401501 = 2400563) B2400563
theorem B2526731 : Blo 1684042 2526731 := bstep (se 1 (by rfl) ⟨1895048, by rfl⟩ : syracuseStep 2526731 = 3790097) B3790097
theorem B2526743 : Blo 1684042 2526743 := bstep (se 1 (by rfl) ⟨1895057, by rfl⟩ : syracuseStep 2526743 = 3790115) B3790115
theorem B4795955 : Blo 1684042 4795955 := bstep (se 1 (by rfl) ⟨3596966, by rfl⟩ : syracuseStep 4795955 = 7193933) B7193933
theorem B4263475 : Blo 1684042 4263475 := bstep (se 1 (by rfl) ⟨3197606, by rfl⟩ : syracuseStep 4263475 = 6395213) B6395213
theorem B2526809 : Blo 1684042 2526809 := bstep (se 2 (by rfl) ⟨947553, by rfl⟩ : syracuseStep 2526809 = 1895107) B1895107
theorem B1896043 : Blo 1684042 1896043 := bstep (se 1 (by rfl) ⟨1422032, by rfl⟩ : syracuseStep 1896043 = 2844065) B2844065
theorem B6327953 : Blo 1684042 6327953 := bstep (se 2 (by rfl) ⟨2372982, by rfl⟩ : syracuseStep 6327953 = 4745965) B4745965
theorem B4263617 : Blo 1684042 4263617 := bstep (se 2 (by rfl) ⟨1598856, by rfl⟩ : syracuseStep 4263617 = 3197713) B3197713
theorem B2526923 : Blo 1684042 2526923 := bstep (se 1 (by rfl) ⟨1895192, by rfl⟩ : syracuseStep 2526923 = 3790385) B3790385
theorem B2526935 : Blo 1684042 2526935 := bstep (se 1 (by rfl) ⟨1895201, by rfl⟩ : syracuseStep 2526935 = 3790403) B3790403
theorem B1896151 : Blo 1684042 1896151 := bstep (se 1 (by rfl) ⟨1422113, by rfl⟩ : syracuseStep 1896151 = 2844227) B2844227
theorem B8531729 : Blo 1684042 8531729 := bstep (se 2 (by rfl) ⟨3199398, by rfl⟩ : syracuseStep 8531729 = 6398797) B6398797
theorem B2527001 : Blo 1684042 2527001 := bstep (se 2 (by rfl) ⟨947625, by rfl⟩ : syracuseStep 2527001 = 1895251) B1895251
theorem B9596717 : Blo 1684042 9596717 := bstep (se 3 (by rfl) ⟨1799384, by rfl⟩ : syracuseStep 9596717 = 3598769) B3598769
theorem B4616011 : Blo 1684042 4616011 := bstep (se 1 (by rfl) ⟨3462008, by rfl⟩ : syracuseStep 4616011 = 6924017) B6924017
theorem B2699083 : Blo 1684042 2699083 := bstep (se 1 (by rfl) ⟨2024312, by rfl⟩ : syracuseStep 2699083 = 4048625) B4048625
theorem B2527115 : Blo 1684042 2527115 := bstep (se 1 (by rfl) ⟨1895336, by rfl⟩ : syracuseStep 2527115 = 3790673) B3790673
theorem B1896331 : Blo 1684042 1896331 := bstep (se 1 (by rfl) ⟨1422248, by rfl⟩ : syracuseStep 1896331 = 2844497) B2844497
theorem B2527127 : Blo 1684042 2527127 := bstep (se 1 (by rfl) ⟨1895345, by rfl⟩ : syracuseStep 2527127 = 3790691) B3790691
theorem B3600281 : Blo 1684042 3600281 := bstep (se 2 (by rfl) ⟨1350105, by rfl⟩ : syracuseStep 3600281 = 2700211) B2700211
theorem B8531891 : Blo 1684042 8531891 := bstep (se 1 (by rfl) ⟨6398918, by rfl⟩ : syracuseStep 8531891 = 12797837) B12797837
theorem B2527193 : Blo 1684042 2527193 := bstep (se 2 (by rfl) ⟨947697, by rfl⟩ : syracuseStep 2527193 = 1895395) B1895395
theorem B7196633 : Blo 1684042 7196633 := bstep (se 2 (by rfl) ⟨2698737, by rfl⟩ : syracuseStep 7196633 = 5397475) B5397475
theorem B1896439 : Blo 1684042 1896439 := bstep (se 1 (by rfl) ⟨1422329, by rfl⟩ : syracuseStep 1896439 = 2844659) B2844659
theorem B9236497 : Blo 1684042 9236497 := bstep (se 2 (by rfl) ⟨3463686, by rfl⟩ : syracuseStep 9236497 = 6927373) B6927373
theorem B3199027 : Blo 1684042 3199027 := bstep (se 1 (by rfl) ⟨2399270, by rfl⟩ : syracuseStep 3199027 = 4798541) B4798541
theorem B9105473 : Blo 1684042 9105473 := bstep (se 2 (by rfl) ⟨3414552, by rfl⟩ : syracuseStep 9105473 = 6829105) B6829105
theorem B2527307 : Blo 1684042 2527307 := bstep (se 1 (by rfl) ⟨1895480, by rfl⟩ : syracuseStep 2527307 = 3790961) B3790961
theorem B32387147 : Blo 1684042 32387147 := bstep (se 1 (by rfl) ⟨24290360, by rfl⟩ : syracuseStep 32387147 = 48580721) B48580721
theorem B2699339 : Blo 1684042 2699339 := bstep (se 1 (by rfl) ⟨2024504, by rfl⟩ : syracuseStep 2699339 = 4049009) B4049009
theorem B38924363 : Blo 1684042 38924363 := bstep (se 1 (by rfl) ⟨29193272, by rfl⟩ : syracuseStep 38924363 = 58386545) B58386545
theorem B2527319 : Blo 1684042 2527319 := bstep (se 1 (by rfl) ⟨1895489, by rfl⟩ : syracuseStep 2527319 = 3790979) B3790979
theorem B332525681 : Blo 1684042 332525681 := bstep (se 2 (by rfl) ⟨124697130, by rfl⟩ : syracuseStep 332525681 = 249394261) B249394261
theorem B2527385 : Blo 1684042 2527385 := bstep (se 2 (by rfl) ⟨947769, by rfl⟩ : syracuseStep 2527385 = 1895539) B1895539
theorem B1896619 : Blo 1684042 1896619 := bstep (se 1 (by rfl) ⟨1422464, by rfl⟩ : syracuseStep 1896619 = 2844929) B2844929
theorem B5689547 : Blo 1684042 5689547 := bstep (se 1 (by rfl) ⟨4267160, by rfl⟩ : syracuseStep 5689547 = 8534321) B8534321
theorem B2527499 : Blo 1684042 2527499 := bstep (se 1 (by rfl) ⟨1895624, by rfl⟩ : syracuseStep 2527499 = 3791249) B3791249
theorem B2527511 : Blo 1684042 2527511 := bstep (se 1 (by rfl) ⟨1895633, by rfl⟩ : syracuseStep 2527511 = 3791267) B3791267
theorem B1896727 : Blo 1684042 1896727 := bstep (se 1 (by rfl) ⟨1422545, by rfl⟩ : syracuseStep 1896727 = 2845091) B2845091
theorem B35049773 : Blo 1684042 35049773 := bstep (se 3 (by rfl) ⟨6571832, by rfl⟩ : syracuseStep 35049773 = 13143665) B13143665
theorem B3789107 : Blo 1684042 3789107 := bstep (se 1 (by rfl) ⟨2841830, by rfl⟩ : syracuseStep 3789107 = 5683661) B5683661
theorem B3789143 : Blo 1684042 3789143 := bstep (se 1 (by rfl) ⟨2841857, by rfl⟩ : syracuseStep 3789143 = 5683715) B5683715
theorem B2527577 : Blo 1684042 2527577 := bstep (se 2 (by rfl) ⟨947841, by rfl⟩ : syracuseStep 2527577 = 1895683) B1895683
theorem B43184501 : Blo 1684042 43184501 := bstep (se 5 (by rfl) ⟨2024273, by rfl⟩ : syracuseStep 43184501 = 4048547) B4048547
theorem B4321687 : Blo 1684042 4321687 := bstep (se 1 (by rfl) ⟨3241265, by rfl⟩ : syracuseStep 4321687 = 6482531) B6482531
theorem B19190195 : Blo 1684042 19190195 := bstep (se 1 (by rfl) ⟨14392646, by rfl⟩ : syracuseStep 19190195 = 28785293) B28785293
theorem B2527691 : Blo 1684042 2527691 := bstep (se 1 (by rfl) ⟨1895768, by rfl⟩ : syracuseStep 2527691 = 3791537) B3791537
theorem B2527703 : Blo 1684042 2527703 := bstep (se 1 (by rfl) ⟨1895777, by rfl⟩ : syracuseStep 2527703 = 3791555) B3791555
theorem B5689817 : Blo 1684042 5689817 := bstep (se 2 (by rfl) ⟨2133681, by rfl⟩ : syracuseStep 5689817 = 4267363) B4267363
theorem B3199475 : Blo 1684042 3199475 := bstep (se 1 (by rfl) ⟨2399606, by rfl⟩ : syracuseStep 3199475 = 4799213) B4799213
theorem B3789323 : Blo 1684042 3789323 := bstep (se 1 (by rfl) ⟨2841992, by rfl⟩ : syracuseStep 3789323 = 5683985) B5683985
theorem B18215441 : Blo 1684042 18215441 := bstep (se 2 (by rfl) ⟨6830790, by rfl⟩ : syracuseStep 18215441 = 13661581) B13661581
theorem B2527769 : Blo 1684042 2527769 := bstep (se 2 (by rfl) ⟨947913, by rfl⟩ : syracuseStep 2527769 = 1895827) B1895827
theorem B3199513 : Blo 1684042 3199513 := bstep (se 2 (by rfl) ⟨1199817, by rfl⟩ : syracuseStep 3199513 = 2399635) B2399635
theorem B2699801 : Blo 1684042 2699801 := bstep (se 2 (by rfl) ⟨1012425, by rfl⟩ : syracuseStep 2699801 = 2024851) B2024851
theorem B3789377 : Blo 1684042 3789377 := bstep (se 2 (by rfl) ⟨1421016, by rfl⟩ : syracuseStep 3789377 = 2842033) B2842033
theorem B1684043 : Blo 1684042 1684043 := bstep (se 1 (by rfl) ⟨1263032, by rfl⟩ : syracuseStep 1684043 = 2526065) B2526065
theorem B1684055 : Blo 1684042 1684055 := bstep (se 1 (by rfl) ⟨1263041, by rfl⟩ : syracuseStep 1684055 = 2526083) B2526083
theorem B1684075 : Blo 1684042 1684075 := bstep (se 1 (by rfl) ⟨1263056, by rfl⟩ : syracuseStep 1684075 = 2526113) B2526113
theorem B1684087 : Blo 1684042 1684087 := bstep (se 1 (by rfl) ⟨1263065, by rfl⟩ : syracuseStep 1684087 = 2526131) B2526131
theorem B41538179 : Blo 1684042 41538179 := bstep (se 1 (by rfl) ⟨31153634, by rfl⟩ : syracuseStep 41538179 = 62307269) B62307269
theorem B1684107 : Blo 1684042 1684107 := bstep (se 1 (by rfl) ⟨1263080, by rfl⟩ : syracuseStep 1684107 = 2526161) B2526161
theorem B2527883 : Blo 1684042 2527883 := bstep (se 1 (by rfl) ⟨1895912, by rfl⟩ : syracuseStep 2527883 = 3791825) B3791825
theorem B1684119 : Blo 1684042 1684119 := bstep (se 1 (by rfl) ⟨1263089, by rfl⟩ : syracuseStep 1684119 = 2526179) B2526179
theorem B2527895 : Blo 1684042 2527895 := bstep (se 1 (by rfl) ⟨1895921, by rfl⟩ : syracuseStep 2527895 = 3791843) B3791843
theorem B2699929 : Blo 1684042 2699929 := bstep (se 2 (by rfl) ⟨1012473, by rfl⟩ : syracuseStep 2699929 = 2024947) B2024947
theorem B1684139 : Blo 1684042 1684139 := bstep (se 1 (by rfl) ⟨1263104, by rfl⟩ : syracuseStep 1684139 = 2526209) B2526209
theorem B1684151 : Blo 1684042 1684151 := bstep (se 1 (by rfl) ⟨1263113, by rfl⟩ : syracuseStep 1684151 = 2526227) B2526227
theorem B1684171 : Blo 1684042 1684171 := bstep (se 1 (by rfl) ⟨1263128, by rfl⟩ : syracuseStep 1684171 = 2526257) B2526257
theorem B1798859 : Blo 1684042 1798859 := bstep (se 1 (by rfl) ⟨1349144, by rfl⟩ : syracuseStep 1798859 = 2698289) B2698289
theorem B1684183 : Blo 1684042 1684183 := bstep (se 1 (by rfl) ⟨1263137, by rfl⟩ : syracuseStep 1684183 = 2526275) B2526275
theorem B2527961 : Blo 1684042 2527961 := bstep (se 2 (by rfl) ⟨947985, by rfl⟩ : syracuseStep 2527961 = 1895971) B1895971
theorem B1684203 : Blo 1684042 1684203 := bstep (se 1 (by rfl) ⟨1263152, by rfl⟩ : syracuseStep 1684203 = 2526305) B2526305
theorem B1684215 : Blo 1684042 1684215 := bstep (se 1 (by rfl) ⟨1263161, by rfl⟩ : syracuseStep 1684215 = 2526323) B2526323
theorem B1684235 : Blo 1684042 1684235 := bstep (se 1 (by rfl) ⟨1263176, by rfl⟩ : syracuseStep 1684235 = 2526353) B2526353
theorem B1684247 : Blo 1684042 1684247 := bstep (se 1 (by rfl) ⟨1263185, by rfl⟩ : syracuseStep 1684247 = 2526371) B2526371
theorem B3789593 : Blo 1684042 3789593 := bstep (se 2 (by rfl) ⟨1421097, by rfl⟩ : syracuseStep 3789593 = 2842195) B2842195
theorem B1684267 : Blo 1684042 1684267 := bstep (se 1 (by rfl) ⟨1263200, by rfl⟩ : syracuseStep 1684267 = 2526401) B2526401
theorem B1684279 : Blo 1684042 1684279 := bstep (se 1 (by rfl) ⟨1263209, by rfl⟩ : syracuseStep 1684279 = 2526419) B2526419
theorem B1684299 : Blo 1684042 1684299 := bstep (se 1 (by rfl) ⟨1263224, by rfl⟩ : syracuseStep 1684299 = 2526449) B2526449
theorem B2528075 : Blo 1684042 2528075 := bstep (se 1 (by rfl) ⟨1896056, by rfl⟩ : syracuseStep 2528075 = 3792113) B3792113
theorem B1684311 : Blo 1684042 1684311 := bstep (se 1 (by rfl) ⟨1263233, by rfl⟩ : syracuseStep 1684311 = 2526467) B2526467
theorem B2528087 : Blo 1684042 2528087 := bstep (se 1 (by rfl) ⟨1896065, by rfl⟩ : syracuseStep 2528087 = 3792131) B3792131
theorem B1684331 : Blo 1684042 1684331 := bstep (se 1 (by rfl) ⟨1263248, by rfl⟩ : syracuseStep 1684331 = 2526497) B2526497
theorem B3789683 : Blo 1684042 3789683 := bstep (se 1 (by rfl) ⟨2842262, by rfl⟩ : syracuseStep 3789683 = 5684525) B5684525
theorem B1684343 : Blo 1684042 1684343 := bstep (se 1 (by rfl) ⟨1263257, by rfl⟩ : syracuseStep 1684343 = 2526515) B2526515
theorem B1684363 : Blo 1684042 1684363 := bstep (se 1 (by rfl) ⟨1263272, by rfl⟩ : syracuseStep 1684363 = 2526545) B2526545
theorem B3789719 : Blo 1684042 3789719 := bstep (se 1 (by rfl) ⟨2842289, by rfl⟩ : syracuseStep 3789719 = 5684579) B5684579
theorem B1684375 : Blo 1684042 1684375 := bstep (se 1 (by rfl) ⟨1263281, by rfl⟩ : syracuseStep 1684375 = 2526563) B2526563
theorem B2528153 : Blo 1684042 2528153 := bstep (se 2 (by rfl) ⟨948057, by rfl⟩ : syracuseStep 2528153 = 1896115) B1896115
theorem B1684395 : Blo 1684042 1684395 := bstep (se 1 (by rfl) ⟨1263296, by rfl⟩ : syracuseStep 1684395 = 2526593) B2526593
theorem B4264883 : Blo 1684042 4264883 := bstep (se 1 (by rfl) ⟨3198662, by rfl⟩ : syracuseStep 4264883 = 6397325) B6397325
theorem B1684407 : Blo 1684042 1684407 := bstep (se 1 (by rfl) ⟨1263305, by rfl⟩ : syracuseStep 1684407 = 2526611) B2526611
theorem B1684427 : Blo 1684042 1684427 := bstep (se 1 (by rfl) ⟨1263320, by rfl⟩ : syracuseStep 1684427 = 2526641) B2526641
theorem B1709003 : Blo 1684042 1709003 := bstep (se 1 (by rfl) ⟨1281752, by rfl⟩ : syracuseStep 1709003 = 2563505) B2563505
theorem B1684439 : Blo 1684042 1684439 := bstep (se 1 (by rfl) ⟨1263329, by rfl⟩ : syracuseStep 1684439 = 2526659) B2526659
theorem B3199961 : Blo 1684042 3199961 := bstep (se 2 (by rfl) ⟨1199985, by rfl⟩ : syracuseStep 3199961 = 2399971) B2399971
theorem B1684459 : Blo 1684042 1684459 := bstep (se 1 (by rfl) ⟨1263344, by rfl⟩ : syracuseStep 1684459 = 2526689) B2526689
theorem B1684471 : Blo 1684042 1684471 := bstep (se 1 (by rfl) ⟨1263353, by rfl⟩ : syracuseStep 1684471 = 2526707) B2526707
theorem B1684491 : Blo 1684042 1684491 := bstep (se 1 (by rfl) ⟨1263368, by rfl⟩ : syracuseStep 1684491 = 2526737) B2526737
theorem B2528267 : Blo 1684042 2528267 := bstep (se 1 (by rfl) ⟨1896200, by rfl⟩ : syracuseStep 2528267 = 3792401) B3792401
theorem B1684503 : Blo 1684042 1684503 := bstep (se 1 (by rfl) ⟨1263377, by rfl⟩ : syracuseStep 1684503 = 2526755) B2526755
theorem B2528279 : Blo 1684042 2528279 := bstep (se 1 (by rfl) ⟨1896209, by rfl⟩ : syracuseStep 2528279 = 3792419) B3792419
theorem B44356643 : Blo 1684042 44356643 := bstep (se 1 (by rfl) ⟨33267482, by rfl⟩ : syracuseStep 44356643 = 66534965) B66534965
theorem B1684523 : Blo 1684042 1684523 := bstep (se 1 (by rfl) ⟨1263392, by rfl⟩ : syracuseStep 1684523 = 2526785) B2526785
theorem B1684535 : Blo 1684042 1684535 := bstep (se 1 (by rfl) ⟨1263401, by rfl⟩ : syracuseStep 1684535 = 2526803) B2526803
theorem B3789899 : Blo 1684042 3789899 := bstep (se 1 (by rfl) ⟨2842424, by rfl⟩ : syracuseStep 3789899 = 5684849) B5684849
theorem B1684555 : Blo 1684042 1684555 := bstep (se 1 (by rfl) ⟨1263416, by rfl⟩ : syracuseStep 1684555 = 2526833) B2526833
theorem B1684567 : Blo 1684042 1684567 := bstep (se 1 (by rfl) ⟨1263425, by rfl⟩ : syracuseStep 1684567 = 2526851) B2526851
theorem B2528345 : Blo 1684042 2528345 := bstep (se 2 (by rfl) ⟨948129, by rfl⟩ : syracuseStep 2528345 = 1896259) B1896259
theorem B1684587 : Blo 1684042 1684587 := bstep (se 1 (by rfl) ⟨1263440, by rfl⟩ : syracuseStep 1684587 = 2526881) B2526881
theorem B1684599 : Blo 1684042 1684599 := bstep (se 1 (by rfl) ⟨1263449, by rfl⟩ : syracuseStep 1684599 = 2526899) B2526899
theorem B3789953 : Blo 1684042 3789953 := bstep (se 2 (by rfl) ⟨1421232, by rfl⟩ : syracuseStep 3789953 = 2842465) B2842465
theorem B1684619 : Blo 1684042 1684619 := bstep (se 1 (by rfl) ⟨1263464, by rfl⟩ : syracuseStep 1684619 = 2526929) B2526929
theorem B1684631 : Blo 1684042 1684631 := bstep (se 1 (by rfl) ⟨1263473, by rfl⟩ : syracuseStep 1684631 = 2526947) B2526947
theorem B1684651 : Blo 1684042 1684651 := bstep (se 1 (by rfl) ⟨1263488, by rfl⟩ : syracuseStep 1684651 = 2526977) B2526977
theorem B1684663 : Blo 1684042 1684663 := bstep (se 1 (by rfl) ⟨1263497, by rfl⟩ : syracuseStep 1684663 = 2526995) B2526995
theorem B1684683 : Blo 1684042 1684683 := bstep (se 1 (by rfl) ⟨1263512, by rfl⟩ : syracuseStep 1684683 = 2527025) B2527025
theorem B2528459 : Blo 1684042 2528459 := bstep (se 1 (by rfl) ⟨1896344, by rfl⟩ : syracuseStep 2528459 = 3792689) B3792689
theorem B1684695 : Blo 1684042 1684695 := bstep (se 1 (by rfl) ⟨1263521, by rfl⟩ : syracuseStep 1684695 = 2527043) B2527043
theorem B2528471 : Blo 1684042 2528471 := bstep (se 1 (by rfl) ⟨1896353, by rfl⟩ : syracuseStep 2528471 = 3792707) B3792707
theorem B1684715 : Blo 1684042 1684715 := bstep (se 1 (by rfl) ⟨1263536, by rfl⟩ : syracuseStep 1684715 = 2527073) B2527073
theorem B1684727 : Blo 1684042 1684727 := bstep (se 1 (by rfl) ⟨1263545, by rfl⟩ : syracuseStep 1684727 = 2527091) B2527091
theorem B1684747 : Blo 1684042 1684747 := bstep (se 1 (by rfl) ⟨1263560, by rfl⟩ : syracuseStep 1684747 = 2527121) B2527121
theorem B1684759 : Blo 1684042 1684759 := bstep (se 1 (by rfl) ⟨1263569, by rfl⟩ : syracuseStep 1684759 = 2527139) B2527139
theorem B2528537 : Blo 1684042 2528537 := bstep (se 2 (by rfl) ⟨948201, by rfl⟩ : syracuseStep 2528537 = 1896403) B1896403
theorem B1684779 : Blo 1684042 1684779 := bstep (se 1 (by rfl) ⟨1263584, by rfl⟩ : syracuseStep 1684779 = 2527169) B2527169
theorem B19453229 : Blo 1684042 19453229 := bstep (se 3 (by rfl) ⟨3647480, by rfl⟩ : syracuseStep 19453229 = 7294961) B7294961
theorem B1684791 : Blo 1684042 1684791 := bstep (se 1 (by rfl) ⟨1263593, by rfl⟩ : syracuseStep 1684791 = 2527187) B2527187
theorem B1684811 : Blo 1684042 1684811 := bstep (se 1 (by rfl) ⟨1263608, by rfl⟩ : syracuseStep 1684811 = 2527217) B2527217
theorem B1684823 : Blo 1684042 1684823 := bstep (se 1 (by rfl) ⟨1263617, by rfl⟩ : syracuseStep 1684823 = 2527235) B2527235
theorem B3790169 : Blo 1684042 3790169 := bstep (se 2 (by rfl) ⟨1421313, by rfl⟩ : syracuseStep 3790169 = 2842627) B2842627
theorem B1684843 : Blo 1684042 1684843 := bstep (se 1 (by rfl) ⟨1263632, by rfl⟩ : syracuseStep 1684843 = 2527265) B2527265
theorem B1684855 : Blo 1684042 1684855 := bstep (se 1 (by rfl) ⟨1263641, by rfl⟩ : syracuseStep 1684855 = 2527283) B2527283
theorem B1684875 : Blo 1684042 1684875 := bstep (se 1 (by rfl) ⟨1263656, by rfl⟩ : syracuseStep 1684875 = 2527313) B2527313
theorem B2528651 : Blo 1684042 2528651 := bstep (se 1 (by rfl) ⟨1896488, by rfl⟩ : syracuseStep 2528651 = 3792977) B3792977
theorem B1684887 : Blo 1684042 1684887 := bstep (se 1 (by rfl) ⟨1263665, by rfl⟩ : syracuseStep 1684887 = 2527331) B2527331
theorem B2528663 : Blo 1684042 2528663 := bstep (se 1 (by rfl) ⟨1896497, by rfl⟩ : syracuseStep 2528663 = 3792995) B3792995
theorem B1684907 : Blo 1684042 1684907 := bstep (se 1 (by rfl) ⟨1263680, by rfl⟩ : syracuseStep 1684907 = 2527361) B2527361
theorem B3790259 : Blo 1684042 3790259 := bstep (se 1 (by rfl) ⟨2842694, by rfl⟩ : syracuseStep 3790259 = 5685389) B5685389
theorem B1684919 : Blo 1684042 1684919 := bstep (se 1 (by rfl) ⟨1263689, by rfl⟩ : syracuseStep 1684919 = 2527379) B2527379
theorem B1684939 : Blo 1684042 1684939 := bstep (se 1 (by rfl) ⟨1263704, by rfl⟩ : syracuseStep 1684939 = 2527409) B2527409
theorem B4265419 : Blo 1684042 4265419 := bstep (se 1 (by rfl) ⟨3199064, by rfl⟩ : syracuseStep 4265419 = 6398129) B6398129
theorem B3790295 : Blo 1684042 3790295 := bstep (se 1 (by rfl) ⟨2842721, by rfl⟩ : syracuseStep 3790295 = 5685443) B5685443
theorem B1684951 : Blo 1684042 1684951 := bstep (se 1 (by rfl) ⟨1263713, by rfl⟩ : syracuseStep 1684951 = 2527427) B2527427
theorem B2528729 : Blo 1684042 2528729 := bstep (se 2 (by rfl) ⟨948273, by rfl⟩ : syracuseStep 2528729 = 1896547) B1896547
theorem B1684971 : Blo 1684042 1684971 := bstep (se 1 (by rfl) ⟨1263728, by rfl⟩ : syracuseStep 1684971 = 2527457) B2527457
theorem B1684983 : Blo 1684042 1684983 := bstep (se 1 (by rfl) ⟨1263737, by rfl⟩ : syracuseStep 1684983 = 2527475) B2527475
theorem B6395395 : Blo 1684042 6395395 := bstep (se 1 (by rfl) ⟨4796546, by rfl⟩ : syracuseStep 6395395 = 9593093) B9593093
theorem B1685003 : Blo 1684042 1685003 := bstep (se 1 (by rfl) ⟨1263752, by rfl⟩ : syracuseStep 1685003 = 2527505) B2527505
theorem B1685015 : Blo 1684042 1685015 := bstep (se 1 (by rfl) ⟨1263761, by rfl⟩ : syracuseStep 1685015 = 2527523) B2527523
theorem B1685035 : Blo 1684042 1685035 := bstep (se 1 (by rfl) ⟨1263776, by rfl⟩ : syracuseStep 1685035 = 2527553) B2527553
theorem B1685047 : Blo 1684042 1685047 := bstep (se 1 (by rfl) ⟨1263785, by rfl⟩ : syracuseStep 1685047 = 2527571) B2527571
theorem B1685067 : Blo 1684042 1685067 := bstep (se 1 (by rfl) ⟨1263800, by rfl⟩ : syracuseStep 1685067 = 2527601) B2527601
theorem B2528843 : Blo 1684042 2528843 := bstep (se 1 (by rfl) ⟨1896632, by rfl⟩ : syracuseStep 2528843 = 3793265) B3793265
theorem B1947223 : Blo 1684042 1947223 := bstep (se 1 (by rfl) ⟨1460417, by rfl⟩ : syracuseStep 1947223 = 2920835) B2920835
theorem B1685079 : Blo 1684042 1685079 := bstep (se 1 (by rfl) ⟨1263809, by rfl⟩ : syracuseStep 1685079 = 2527619) B2527619
theorem B4265561 : Blo 1684042 4265561 := bstep (se 2 (by rfl) ⟨1599585, by rfl⟩ : syracuseStep 4265561 = 3199171) B3199171
theorem B2528855 : Blo 1684042 2528855 := bstep (se 1 (by rfl) ⟨1896641, by rfl⟩ : syracuseStep 2528855 = 3793283) B3793283
theorem B1685099 : Blo 1684042 1685099 := bstep (se 1 (by rfl) ⟨1263824, by rfl⟩ : syracuseStep 1685099 = 2527649) B2527649
theorem B1685111 : Blo 1684042 1685111 := bstep (se 1 (by rfl) ⟨1263833, by rfl⟩ : syracuseStep 1685111 = 2527667) B2527667
theorem B3790475 : Blo 1684042 3790475 := bstep (se 1 (by rfl) ⟨2842856, by rfl⟩ : syracuseStep 3790475 = 5685713) B5685713
theorem B1685131 : Blo 1684042 1685131 := bstep (se 1 (by rfl) ⟨1263848, by rfl⟩ : syracuseStep 1685131 = 2527697) B2527697
theorem B1685143 : Blo 1684042 1685143 := bstep (se 1 (by rfl) ⟨1263857, by rfl⟩ : syracuseStep 1685143 = 2527715) B2527715
theorem B2528921 : Blo 1684042 2528921 := bstep (se 2 (by rfl) ⟨948345, by rfl⟩ : syracuseStep 2528921 = 1896691) B1896691
theorem B1685163 : Blo 1684042 1685163 := bstep (se 1 (by rfl) ⟨1263872, by rfl⟩ : syracuseStep 1685163 = 2527745) B2527745
theorem B1685175 : Blo 1684042 1685175 := bstep (se 1 (by rfl) ⟨1263881, by rfl⟩ : syracuseStep 1685175 = 2527763) B2527763
theorem B3790529 : Blo 1684042 3790529 := bstep (se 2 (by rfl) ⟨1421448, by rfl⟩ : syracuseStep 3790529 = 2842897) B2842897
theorem B3200705 : Blo 1684042 3200705 := bstep (se 2 (by rfl) ⟨1200264, by rfl⟩ : syracuseStep 3200705 = 2400529) B2400529
theorem B1685195 : Blo 1684042 1685195 := bstep (se 1 (by rfl) ⟨1263896, by rfl⟩ : syracuseStep 1685195 = 2527793) B2527793
theorem B1685207 : Blo 1684042 1685207 := bstep (se 1 (by rfl) ⟨1263905, by rfl⟩ : syracuseStep 1685207 = 2527811) B2527811
theorem B1685227 : Blo 1684042 1685227 := bstep (se 1 (by rfl) ⟨1263920, by rfl⟩ : syracuseStep 1685227 = 2527841) B2527841
theorem B1685239 : Blo 1684042 1685239 := bstep (se 1 (by rfl) ⟨1263929, by rfl⟩ : syracuseStep 1685239 = 2527859) B2527859
theorem B1685259 : Blo 1684042 1685259 := bstep (se 1 (by rfl) ⟨1263944, by rfl⟩ : syracuseStep 1685259 = 2527889) B2527889
theorem B2529035 : Blo 1684042 2529035 := bstep (se 1 (by rfl) ⟨1896776, by rfl⟩ : syracuseStep 2529035 = 3793553) B3793553
theorem B1685271 : Blo 1684042 1685271 := bstep (se 1 (by rfl) ⟨1263953, by rfl⟩ : syracuseStep 1685271 = 2527907) B2527907
theorem B2529047 : Blo 1684042 2529047 := bstep (se 1 (by rfl) ⟨1896785, by rfl⟩ : syracuseStep 2529047 = 3793571) B3793571
theorem B1685291 : Blo 1684042 1685291 := bstep (se 1 (by rfl) ⟨1263968, by rfl⟩ : syracuseStep 1685291 = 2527937) B2527937
theorem B6395699 : Blo 1684042 6395699 := bstep (se 1 (by rfl) ⟨4796774, by rfl⟩ : syracuseStep 6395699 = 9593549) B9593549
theorem B1685303 : Blo 1684042 1685303 := bstep (se 1 (by rfl) ⟨1263977, by rfl⟩ : syracuseStep 1685303 = 2527955) B2527955
theorem B1685323 : Blo 1684042 1685323 := bstep (se 1 (by rfl) ⟨1263992, by rfl⟩ : syracuseStep 1685323 = 2527985) B2527985
theorem B8533835 : Blo 1684042 8533835 := bstep (se 1 (by rfl) ⟨6400376, by rfl⟩ : syracuseStep 8533835 = 12800753) B12800753
theorem B1685335 : Blo 1684042 1685335 := bstep (se 1 (by rfl) ⟨1264001, by rfl⟩ : syracuseStep 1685335 = 2528003) B2528003
theorem B19191653 : Blo 1684042 19191653 := bstep (se 4 (by rfl) ⟨1799217, by rfl⟩ : syracuseStep 19191653 = 3598435) B3598435
theorem B1685355 : Blo 1684042 1685355 := bstep (se 1 (by rfl) ⟨1264016, by rfl⟩ : syracuseStep 1685355 = 2528033) B2528033
theorem B1685367 : Blo 1684042 1685367 := bstep (se 1 (by rfl) ⟨1264025, by rfl⟩ : syracuseStep 1685367 = 2528051) B2528051
theorem B1824631 : Blo 1684042 1824631 := bstep (se 1 (by rfl) ⟨1368473, by rfl⟩ : syracuseStep 1824631 = 2736947) B2736947
theorem B2398091 : Blo 1684042 2398091 := bstep (se 1 (by rfl) ⟨1798568, by rfl⟩ : syracuseStep 2398091 = 3597137) B3597137
theorem B1685387 : Blo 1684042 1685387 := bstep (se 1 (by rfl) ⟨1264040, by rfl⟩ : syracuseStep 1685387 = 2528081) B2528081
theorem B1685399 : Blo 1684042 1685399 := bstep (se 1 (by rfl) ⟨1264049, by rfl⟩ : syracuseStep 1685399 = 2528099) B2528099
theorem B3790745 : Blo 1684042 3790745 := bstep (se 2 (by rfl) ⟨1421529, by rfl⟩ : syracuseStep 3790745 = 2843059) B2843059
theorem B1685419 : Blo 1684042 1685419 := bstep (se 1 (by rfl) ⟨1264064, by rfl⟩ : syracuseStep 1685419 = 2528129) B2528129
theorem B1685431 : Blo 1684042 1685431 := bstep (se 1 (by rfl) ⟨1264073, by rfl⟩ : syracuseStep 1685431 = 2528147) B2528147
theorem B1685451 : Blo 1684042 1685451 := bstep (se 1 (by rfl) ⟨1264088, by rfl⟩ : syracuseStep 1685451 = 2528177) B2528177
theorem B1685463 : Blo 1684042 1685463 := bstep (se 1 (by rfl) ⟨1264097, by rfl⟩ : syracuseStep 1685463 = 2528195) B2528195
theorem B27686873 : Blo 1684042 27686873 := bstep (se 2 (by rfl) ⟨10382577, by rfl⟩ : syracuseStep 27686873 = 20765155) B20765155
theorem B1685483 : Blo 1684042 1685483 := bstep (se 1 (by rfl) ⟨1264112, by rfl⟩ : syracuseStep 1685483 = 2528225) B2528225
theorem B3790835 : Blo 1684042 3790835 := bstep (se 1 (by rfl) ⟨2843126, by rfl⟩ : syracuseStep 3790835 = 5686253) B5686253
theorem B1685495 : Blo 1684042 1685495 := bstep (se 1 (by rfl) ⟨1264121, by rfl⟩ : syracuseStep 1685495 = 2528243) B2528243
theorem B1685515 : Blo 1684042 1685515 := bstep (se 1 (by rfl) ⟨1264136, by rfl⟩ : syracuseStep 1685515 = 2528273) B2528273
theorem B3790871 : Blo 1684042 3790871 := bstep (se 1 (by rfl) ⟨2843153, by rfl⟩ : syracuseStep 3790871 = 5686307) B5686307
theorem B1685527 : Blo 1684042 1685527 := bstep (se 1 (by rfl) ⟨1264145, by rfl⟩ : syracuseStep 1685527 = 2528291) B2528291
theorem B1685547 : Blo 1684042 1685547 := bstep (se 1 (by rfl) ⟨1264160, by rfl⟩ : syracuseStep 1685547 = 2528321) B2528321
theorem B1685559 : Blo 1684042 1685559 := bstep (se 1 (by rfl) ⟨1264169, by rfl⟩ : syracuseStep 1685559 = 2528339) B2528339
theorem B1685579 : Blo 1684042 1685579 := bstep (se 1 (by rfl) ⟨1264184, by rfl⟩ : syracuseStep 1685579 = 2528369) B2528369
theorem B1685591 : Blo 1684042 1685591 := bstep (se 1 (by rfl) ⟨1264193, by rfl⟩ : syracuseStep 1685591 = 2528387) B2528387
theorem B12793949 : Blo 1684042 12793949 := bstep (se 3 (by rfl) ⟨2398865, by rfl⟩ : syracuseStep 12793949 = 4797731) B4797731
theorem B1685611 : Blo 1684042 1685611 := bstep (se 1 (by rfl) ⟨1264208, by rfl⟩ : syracuseStep 1685611 = 2528417) B2528417
theorem B1685623 : Blo 1684042 1685623 := bstep (se 1 (by rfl) ⟨1264217, by rfl⟩ : syracuseStep 1685623 = 2528435) B2528435
theorem B1800311 : Blo 1684042 1800311 := bstep (se 1 (by rfl) ⟨1350233, by rfl⟩ : syracuseStep 1800311 = 2700467) B2700467
theorem B9599107 : Blo 1684042 9599107 := bstep (se 1 (by rfl) ⟨7199330, by rfl⟩ : syracuseStep 9599107 = 14398661) B14398661
theorem B1685643 : Blo 1684042 1685643 := bstep (se 1 (by rfl) ⟨1264232, by rfl⟩ : syracuseStep 1685643 = 2528465) B2528465
theorem B1685655 : Blo 1684042 1685655 := bstep (se 1 (by rfl) ⟨1264241, by rfl⟩ : syracuseStep 1685655 = 2528483) B2528483
theorem B1685675 : Blo 1684042 1685675 := bstep (se 1 (by rfl) ⟨1264256, by rfl⟩ : syracuseStep 1685675 = 2528513) B2528513
theorem B1685687 : Blo 1684042 1685687 := bstep (se 1 (by rfl) ⟨1264265, by rfl⟩ : syracuseStep 1685687 = 2528531) B2528531
theorem B3791051 : Blo 1684042 3791051 := bstep (se 1 (by rfl) ⟨2843288, by rfl⟩ : syracuseStep 3791051 = 5686577) B5686577
theorem B1685707 : Blo 1684042 1685707 := bstep (se 1 (by rfl) ⟨1264280, by rfl⟩ : syracuseStep 1685707 = 2528561) B2528561
theorem B1685719 : Blo 1684042 1685719 := bstep (se 1 (by rfl) ⟨1264289, by rfl⟩ : syracuseStep 1685719 = 2528579) B2528579
theorem B1685739 : Blo 1684042 1685739 := bstep (se 1 (by rfl) ⟨1264304, by rfl⟩ : syracuseStep 1685739 = 2528609) B2528609
theorem B1685751 : Blo 1684042 1685751 := bstep (se 1 (by rfl) ⟨1264313, by rfl⟩ : syracuseStep 1685751 = 2528627) B2528627
theorem B3791105 : Blo 1684042 3791105 := bstep (se 2 (by rfl) ⟨1421664, by rfl⟩ : syracuseStep 3791105 = 2843329) B2843329
theorem B1685771 : Blo 1684042 1685771 := bstep (se 1 (by rfl) ⟨1264328, by rfl⟩ : syracuseStep 1685771 = 2528657) B2528657
theorem B1685783 : Blo 1684042 1685783 := bstep (se 1 (by rfl) ⟨1264337, by rfl⟩ : syracuseStep 1685783 = 2528675) B2528675
theorem B1685803 : Blo 1684042 1685803 := bstep (se 1 (by rfl) ⟨1264352, by rfl⟩ : syracuseStep 1685803 = 2528705) B2528705
theorem B1685815 : Blo 1684042 1685815 := bstep (se 1 (by rfl) ⟨1264361, by rfl⟩ : syracuseStep 1685815 = 2528723) B2528723
theorem B1685835 : Blo 1684042 1685835 := bstep (se 1 (by rfl) ⟨1264376, by rfl⟩ : syracuseStep 1685835 = 2528753) B2528753
theorem B1685847 : Blo 1684042 1685847 := bstep (se 1 (by rfl) ⟨1264385, by rfl⟩ : syracuseStep 1685847 = 2528771) B2528771
theorem B1685867 : Blo 1684042 1685867 := bstep (se 1 (by rfl) ⟨1264400, by rfl⟩ : syracuseStep 1685867 = 2528801) B2528801
theorem B1685879 : Blo 1684042 1685879 := bstep (se 1 (by rfl) ⟨1264409, by rfl⟩ : syracuseStep 1685879 = 2528819) B2528819
theorem B1685899 : Blo 1684042 1685899 := bstep (se 1 (by rfl) ⟨1264424, by rfl⟩ : syracuseStep 1685899 = 2528849) B2528849
theorem B4798871 : Blo 1684042 4798871 := bstep (se 1 (by rfl) ⟨3599153, by rfl⟩ : syracuseStep 4798871 = 7198307) B7198307
theorem B4266391 : Blo 1684042 4266391 := bstep (se 1 (by rfl) ⟨3199793, by rfl⟩ : syracuseStep 4266391 = 6399587) B6399587
theorem B1685911 : Blo 1684042 1685911 := bstep (se 1 (by rfl) ⟨1264433, by rfl⟩ : syracuseStep 1685911 = 2528867) B2528867
theorem B1685931 : Blo 1684042 1685931 := bstep (se 1 (by rfl) ⟨1264448, by rfl⟩ : syracuseStep 1685931 = 2528897) B2528897
theorem B12138929 : Blo 1684042 12138929 := bstep (se 2 (by rfl) ⟨4552098, by rfl⟩ : syracuseStep 12138929 = 9104197) B9104197
theorem B26655155 : Blo 1684042 26655155 := bstep (se 1 (by rfl) ⟨19991366, by rfl⟩ : syracuseStep 26655155 = 39982733) B39982733
theorem B1685943 : Blo 1684042 1685943 := bstep (se 1 (by rfl) ⟨1264457, by rfl⟩ : syracuseStep 1685943 = 2528915) B2528915
theorem B6396353 : Blo 1684042 6396353 := bstep (se 2 (by rfl) ⟨2398632, by rfl⟩ : syracuseStep 6396353 = 4797265) B4797265
theorem B1685963 : Blo 1684042 1685963 := bstep (se 1 (by rfl) ⟨1264472, by rfl⟩ : syracuseStep 1685963 = 2528945) B2528945
theorem B1685975 : Blo 1684042 1685975 := bstep (se 1 (by rfl) ⟨1264481, by rfl⟩ : syracuseStep 1685975 = 2528963) B2528963
theorem B3791321 : Blo 1684042 3791321 := bstep (se 2 (by rfl) ⟨1421745, by rfl⟩ : syracuseStep 3791321 = 2843491) B2843491
theorem B1685995 : Blo 1684042 1685995 := bstep (se 1 (by rfl) ⟨1264496, by rfl⟩ : syracuseStep 1685995 = 2528993) B2528993
theorem B1686007 : Blo 1684042 1686007 := bstep (se 1 (by rfl) ⟨1264505, by rfl⟩ : syracuseStep 1686007 = 2529011) B2529011
theorem B1686027 : Blo 1684042 1686027 := bstep (se 1 (by rfl) ⟨1264520, by rfl⟩ : syracuseStep 1686027 = 2529041) B2529041
theorem B1686039 : Blo 1684042 1686039 := bstep (se 1 (by rfl) ⟨1264529, by rfl⟩ : syracuseStep 1686039 = 2529059) B2529059
theorem B3791411 : Blo 1684042 3791411 := bstep (se 1 (by rfl) ⟨2843558, by rfl⟩ : syracuseStep 3791411 = 5687117) B5687117
theorem B3791447 : Blo 1684042 3791447 := bstep (se 1 (by rfl) ⟨2843585, by rfl⟩ : syracuseStep 3791447 = 5687171) B5687171
theorem B4553309 : Blo 1684042 4553309 := bstep (se 3 (by rfl) ⟨853745, by rfl⟩ : syracuseStep 4553309 = 1707491) B1707491
theorem B3791627 : Blo 1684042 3791627 := bstep (se 1 (by rfl) ⟨2843720, by rfl⟩ : syracuseStep 3791627 = 5687441) B5687441
theorem B14400301 : Blo 1684042 14400301 := bstep (se 3 (by rfl) ⟨2700056, by rfl⟩ : syracuseStep 14400301 = 5400113) B5400113
theorem B3791681 : Blo 1684042 3791681 := bstep (se 2 (by rfl) ⟨1421880, by rfl⟩ : syracuseStep 3791681 = 2843761) B2843761
theorem B4266827 : Blo 1684042 4266827 := bstep (se 1 (by rfl) ⟨3200120, by rfl⟩ : syracuseStep 4266827 = 6400241) B6400241
theorem B12139415 : Blo 1684042 12139415 := bstep (se 1 (by rfl) ⟨9104561, by rfl⟩ : syracuseStep 12139415 = 18209123) B18209123
theorem B5684147 : Blo 1684042 5684147 := bstep (se 1 (by rfl) ⟨4263110, by rfl⟩ : syracuseStep 5684147 = 8526221) B8526221
theorem B3791897 : Blo 1684042 3791897 := bstep (se 2 (by rfl) ⟨1421961, by rfl⟩ : syracuseStep 3791897 = 2843923) B2843923
theorem B9600065 : Blo 1684042 9600065 := bstep (se 2 (by rfl) ⟨3600024, by rfl⟩ : syracuseStep 9600065 = 7200049) B7200049
theorem B16194653 : Blo 1684042 16194653 := bstep (se 3 (by rfl) ⟨3036497, by rfl⟩ : syracuseStep 16194653 = 6072995) B6072995
theorem B3791987 : Blo 1684042 3791987 := bstep (se 1 (by rfl) ⟨2843990, by rfl⟩ : syracuseStep 3791987 = 5687981) B5687981
theorem B3792023 : Blo 1684042 3792023 := bstep (se 1 (by rfl) ⟨2844017, by rfl⟩ : syracuseStep 3792023 = 5688035) B5688035
theorem B5684417 : Blo 1684042 5684417 := bstep (se 2 (by rfl) ⟨2131656, by rfl⟩ : syracuseStep 5684417 = 4263313) B4263313
theorem B4267201 : Blo 1684042 4267201 := bstep (se 2 (by rfl) ⟨1600200, by rfl⟩ : syracuseStep 4267201 = 3200401) B3200401
theorem B3792203 : Blo 1684042 3792203 := bstep (se 1 (by rfl) ⟨2844152, by rfl⟩ : syracuseStep 3792203 = 5688305) B5688305
theorem B3792257 : Blo 1684042 3792257 := bstep (se 2 (by rfl) ⟨1422096, by rfl⟩ : syracuseStep 3792257 = 2844193) B2844193
theorem B5397911 : Blo 1684042 5397911 := bstep (se 1 (by rfl) ⟨4048433, by rfl⟩ : syracuseStep 5397911 = 8096867) B8096867
theorem B2563481 : Blo 1684042 2563481 := bstep (se 2 (by rfl) ⟨961305, by rfl⟩ : syracuseStep 2563481 = 1922611) B1922611
theorem B3792473 : Blo 1684042 3792473 := bstep (se 2 (by rfl) ⟨1422177, by rfl⟩ : syracuseStep 3792473 = 2844355) B2844355
theorem B16203415 : Blo 1684042 16203415 := bstep (se 1 (by rfl) ⟨12152561, by rfl⟩ : syracuseStep 16203415 = 24305123) B24305123
theorem B6397613 : Blo 1684042 6397613 := bstep (se 3 (by rfl) ⟨1199552, by rfl⟩ : syracuseStep 6397613 = 2399105) B2399105
theorem B3792563 : Blo 1684042 3792563 := bstep (se 1 (by rfl) ⟨2844422, by rfl⟩ : syracuseStep 3792563 = 5688845) B5688845
theorem B6397643 : Blo 1684042 6397643 := bstep (se 1 (by rfl) ⟨4798232, by rfl⟩ : syracuseStep 6397643 = 9596465) B9596465
theorem B2399959 : Blo 1684042 2399959 := bstep (se 1 (by rfl) ⟨1799969, by rfl⟩ : syracuseStep 2399959 = 3599939) B3599939
theorem B3792599 : Blo 1684042 3792599 := bstep (se 1 (by rfl) ⟨2844449, by rfl⟩ : syracuseStep 3792599 = 5688899) B5688899
theorem B5684957 : Blo 1684042 5684957 := bstep (se 3 (by rfl) ⟨1065929, by rfl⟩ : syracuseStep 5684957 = 2131859) B2131859
theorem B2842391 : Blo 1684042 2842391 := bstep (se 1 (by rfl) ⟨2131793, by rfl⟩ : syracuseStep 2842391 = 4263587) B4263587
theorem B3948313 : Blo 1684042 3948313 := bstep (se 2 (by rfl) ⟨1480617, by rfl⟩ : syracuseStep 3948313 = 2961235) B2961235
theorem B3792779 : Blo 1684042 3792779 := bstep (se 1 (by rfl) ⟨2844584, by rfl⟩ : syracuseStep 3792779 = 5689169) B5689169
theorem B2842519 : Blo 1684042 2842519 := bstep (se 1 (by rfl) ⟨2131889, by rfl⟩ : syracuseStep 2842519 = 4263779) B4263779
theorem B3792833 : Blo 1684042 3792833 := bstep (se 2 (by rfl) ⟨1422312, by rfl⟩ : syracuseStep 3792833 = 2844625) B2844625
theorem B6070315 : Blo 1684042 6070315 := bstep (se 1 (by rfl) ⟨4552736, by rfl⟩ : syracuseStep 6070315 = 9105473) B9105473
theorem B9601091 : Blo 1684042 9601091 := bstep (se 1 (by rfl) ⟨7200818, by rfl⟩ : syracuseStep 9601091 = 14401637) B14401637
theorem B221683787 : Blo 1684042 221683787 := bstep (se 1 (by rfl) ⟨166262840, by rfl⟩ : syracuseStep 221683787 = 332525681) B332525681
theorem B5685335 : Blo 1684042 5685335 := bstep (se 1 (by rfl) ⟨4264001, by rfl⟩ : syracuseStep 5685335 = 8528003) B8528003
theorem B3793031 : Blo 1684042 3793031 := bstep (se 1 (by rfl) ⟨2844773, by rfl⟩ : syracuseStep 3793031 = 5689547) B5689547
theorem B4800647 : Blo 1684042 4800647 := bstep (se 1 (by rfl) ⟨3600485, by rfl⟩ : syracuseStep 4800647 = 7200971) B7200971
theorem B4554899 : Blo 1684042 4554899 := bstep (se 1 (by rfl) ⟨3416174, by rfl⟩ : syracuseStep 4554899 = 6832349) B6832349
theorem B3793211 : Blo 1684042 3793211 := bstep (se 1 (by rfl) ⟨2844908, by rfl⟩ : syracuseStep 3793211 = 5689817) B5689817
theorem B3793337 : Blo 1684042 3793337 := bstep (se 2 (by rfl) ⟨1422501, by rfl⟩ : syracuseStep 3793337 = 2845003) B2845003
theorem B5685821 : Blo 1684042 5685821 := bstep (se 3 (by rfl) ⟨1066091, by rfl⟩ : syracuseStep 5685821 = 2132183) B2132183
theorem B2843255 : Blo 1684042 2843255 := bstep (se 1 (by rfl) ⟨2132441, by rfl⟩ : syracuseStep 2843255 = 4264883) B4264883
theorem B12968819 : Blo 1684042 12968819 := bstep (se 1 (by rfl) ⟨9726614, by rfl⟩ : syracuseStep 12968819 = 19453229) B19453229
theorem B4555655 : Blo 1684042 4555655 := bstep (se 1 (by rfl) ⟨3416741, by rfl⟩ : syracuseStep 4555655 = 6833483) B6833483
theorem B27313163 : Blo 1684042 27313163 := bstep (se 1 (by rfl) ⟨20484872, by rfl⟩ : syracuseStep 27313163 = 40969745) B40969745
theorem B2843707 : Blo 1684042 2843707 := bstep (se 1 (by rfl) ⟨2132780, by rfl⟩ : syracuseStep 2843707 = 4265561) B4265561
theorem B9110615 : Blo 1684042 9110615 := bstep (se 1 (by rfl) ⟨6832961, by rfl⟩ : syracuseStep 9110615 = 13665923) B13665923
theorem B2843849 : Blo 1684042 2843849 := bstep (se 2 (by rfl) ⟨1066443, by rfl⟩ : syracuseStep 2843849 = 2132887) B2132887
theorem B16188653 : Blo 1684042 16188653 := bstep (se 3 (by rfl) ⟨3035372, by rfl⟩ : syracuseStep 16188653 = 6070745) B6070745
theorem B19203317 : Blo 1684042 19203317 := bstep (se 5 (by rfl) ⟨900155, by rfl⟩ : syracuseStep 19203317 = 1800311) B1800311
theorem B18457915 : Blo 1684042 18457915 := bstep (se 1 (by rfl) ⟨13843436, by rfl⟩ : syracuseStep 18457915 = 27686873) B27686873
theorem B8529299 : Blo 1684042 8529299 := bstep (se 1 (by rfl) ⟨6396974, by rfl⟩ : syracuseStep 8529299 = 12793949) B12793949
theorem B4048471 : Blo 1684042 4048471 := bstep (se 1 (by rfl) ⟨3036353, by rfl⟩ : syracuseStep 4048471 = 6072707) B6072707
theorem B17770103 : Blo 1684042 17770103 := bstep (se 1 (by rfl) ⟨13327577, by rfl⟩ : syracuseStep 17770103 = 26655155) B26655155
theorem B2131591 : Blo 1684042 2131591 := bstep (se 1 (by rfl) ⟨1598693, by rfl⟩ : syracuseStep 2131591 = 3197387) B3197387
theorem B3598025 : Blo 1684042 3598025 := bstep (se 2 (by rfl) ⟨1349259, by rfl⟩ : syracuseStep 3598025 = 2698519) B2698519
theorem B24618725 : Blo 1684042 24618725 := bstep (se 4 (by rfl) ⟨2308005, by rfl⟩ : syracuseStep 24618725 = 4616011) B4616011
theorem B2844551 : Blo 1684042 2844551 := bstep (se 1 (by rfl) ⟨2133413, by rfl⟩ : syracuseStep 2844551 = 4266827) B4266827
theorem B3598265 : Blo 1684042 3598265 := bstep (se 2 (by rfl) ⟨1349349, by rfl⟩ : syracuseStep 3598265 = 2698699) B2698699
theorem B5687225 : Blo 1684042 5687225 := bstep (se 2 (by rfl) ⟨2132709, by rfl⟩ : syracuseStep 5687225 = 4265419) B4265419
theorem B2132011 : Blo 1684042 2132011 := bstep (se 1 (by rfl) ⟨1599008, by rfl⟩ : syracuseStep 2132011 = 3198017) B3198017
theorem B6400043 : Blo 1684042 6400043 := bstep (se 1 (by rfl) ⟨4800032, by rfl⟩ : syracuseStep 6400043 = 9600065) B9600065
theorem B21604553 : Blo 1684042 21604553 := bstep (se 2 (by rfl) ⟨8101707, by rfl⟩ : syracuseStep 21604553 = 16203415) B16203415
theorem B2132239 : Blo 1684042 2132239 := bstep (se 1 (by rfl) ⟨1599179, by rfl⟩ : syracuseStep 2132239 = 3198359) B3198359
theorem B3598607 : Blo 1684042 3598607 := bstep (se 1 (by rfl) ⟨2698955, by rfl⟩ : syracuseStep 3598607 = 5397911) B5397911
theorem B3197227 : Blo 1684042 3197227 := bstep (se 1 (by rfl) ⟨2397920, by rfl⟩ : syracuseStep 3197227 = 4795841) B4795841
theorem B3197303 : Blo 1684042 3197303 := bstep (se 1 (by rfl) ⟨2397977, by rfl⟩ : syracuseStep 3197303 = 4795955) B4795955
theorem B3598777 : Blo 1684042 3598777 := bstep (se 2 (by rfl) ⟨1349541, by rfl⟩ : syracuseStep 3598777 = 2699083) B2699083
theorem B13666769 : Blo 1684042 13666769 := bstep (se 2 (by rfl) ⟨5125038, by rfl⟩ : syracuseStep 13666769 = 10250077) B10250077
theorem B5687819 : Blo 1684042 5687819 := bstep (se 1 (by rfl) ⟨4265864, by rfl⟩ : syracuseStep 5687819 = 8531729) B8531729
theorem B1894927 : Blo 1684042 1894927 := bstep (se 1 (by rfl) ⟨1421195, by rfl⟩ : syracuseStep 1894927 = 2842391) B2842391
theorem B4557341 : Blo 1684042 4557341 := bstep (se 3 (by rfl) ⟨854501, by rfl⟩ : syracuseStep 4557341 = 1709003) B1709003
theorem B5687927 : Blo 1684042 5687927 := bstep (se 1 (by rfl) ⟨4265945, by rfl⟩ : syracuseStep 5687927 = 8531891) B8531891
theorem B12315329 : Blo 1684042 12315329 := bstep (se 2 (by rfl) ⟨4618248, by rfl⟩ : syracuseStep 12315329 = 9236497) B9236497
theorem B12798809 : Blo 1684042 12798809 := bstep (se 2 (by rfl) ⟨4799553, by rfl⟩ : syracuseStep 12798809 = 9599107) B9599107
theorem B2526071 : Blo 1684042 2526071 := bstep (se 1 (by rfl) ⟨1894553, by rfl⟩ : syracuseStep 2526071 = 3789107) B3789107
theorem B2526095 : Blo 1684042 2526095 := bstep (se 1 (by rfl) ⟨1894571, by rfl⟩ : syracuseStep 2526095 = 3789143) B3789143
theorem B28789667 : Blo 1684042 28789667 := bstep (se 1 (by rfl) ⟨21592250, by rfl⟩ : syracuseStep 28789667 = 43184501) B43184501
theorem B2526137 : Blo 1684042 2526137 := bstep (se 2 (by rfl) ⟨947301, by rfl⟩ : syracuseStep 2526137 = 1894603) B1894603
theorem B2132983 : Blo 1684042 2132983 := bstep (se 1 (by rfl) ⟨1599737, by rfl⟩ : syracuseStep 2132983 = 3199475) B3199475
theorem B1895431 : Blo 1684042 1895431 := bstep (se 1 (by rfl) ⟨1421573, by rfl⟩ : syracuseStep 1895431 = 2843147) B2843147
theorem B2526215 : Blo 1684042 2526215 := bstep (se 1 (by rfl) ⟨1894661, by rfl⟩ : syracuseStep 2526215 = 3789323) B3789323
theorem B12143627 : Blo 1684042 12143627 := bstep (se 1 (by rfl) ⟨9107720, by rfl⟩ : syracuseStep 12143627 = 18215441) B18215441
theorem B2526251 : Blo 1684042 2526251 := bstep (se 1 (by rfl) ⟨1894688, by rfl⟩ : syracuseStep 2526251 = 3789377) B3789377
theorem B7195709 : Blo 1684042 7195709 := bstep (se 3 (by rfl) ⟨1349195, by rfl⟩ : syracuseStep 7195709 = 2698391) B2698391
theorem B2526281 : Blo 1684042 2526281 := bstep (se 2 (by rfl) ⟨947355, by rfl⟩ : syracuseStep 2526281 = 1894711) B1894711
theorem B27692119 : Blo 1684042 27692119 := bstep (se 1 (by rfl) ⟨20769089, by rfl⟩ : syracuseStep 27692119 = 41538179) B41538179
theorem B3599495 : Blo 1684042 3599495 := bstep (se 1 (by rfl) ⟨2699621, by rfl⟩ : syracuseStep 3599495 = 5399243) B5399243
theorem B2526395 : Blo 1684042 2526395 := bstep (se 1 (by rfl) ⟨1894796, by rfl⟩ : syracuseStep 2526395 = 3789593) B3789593
theorem B1895611 : Blo 1684042 1895611 := bstep (se 1 (by rfl) ⟨1421708, by rfl⟩ : syracuseStep 1895611 = 2843417) B2843417
theorem B5762249 : Blo 1684042 5762249 := bstep (se 2 (by rfl) ⟨2160843, by rfl⟩ : syracuseStep 5762249 = 4321687) B4321687
theorem B5688521 : Blo 1684042 5688521 := bstep (se 2 (by rfl) ⟨2133195, by rfl⟩ : syracuseStep 5688521 = 4266391) B4266391
theorem B2526455 : Blo 1684042 2526455 := bstep (se 1 (by rfl) ⟨1894841, by rfl⟩ : syracuseStep 2526455 = 3789683) B3789683
theorem B2526479 : Blo 1684042 2526479 := bstep (se 1 (by rfl) ⟨1894859, by rfl⟩ : syracuseStep 2526479 = 3789719) B3789719
theorem B4795681 : Blo 1684042 4795681 := bstep (se 2 (by rfl) ⟨1798380, by rfl⟩ : syracuseStep 4795681 = 3596761) B3596761
theorem B2526521 : Blo 1684042 2526521 := bstep (se 2 (by rfl) ⟨947445, by rfl⟩ : syracuseStep 2526521 = 1894891) B1894891
theorem B2133307 : Blo 1684042 2133307 := bstep (se 1 (by rfl) ⟨1599980, by rfl⟩ : syracuseStep 2133307 = 3199961) B3199961
theorem B2526599 : Blo 1684042 2526599 := bstep (se 1 (by rfl) ⟨1894949, by rfl⟩ : syracuseStep 2526599 = 3789899) B3789899
theorem B2526635 : Blo 1684042 2526635 := bstep (se 1 (by rfl) ⟨1894976, by rfl⟩ : syracuseStep 2526635 = 3789953) B3789953
theorem B2526665 : Blo 1684042 2526665 := bstep (se 2 (by rfl) ⟨947499, by rfl⟩ : syracuseStep 2526665 = 1894999) B1894999
theorem B93466061 : Blo 1684042 93466061 := bstep (se 3 (by rfl) ⟨17524886, by rfl⟩ : syracuseStep 93466061 = 35049773) B35049773
theorem B4263425 : Blo 1684042 4263425 := bstep (se 2 (by rfl) ⟨1598784, by rfl⟩ : syracuseStep 4263425 = 3197569) B3197569
theorem B3599905 : Blo 1684042 3599905 := bstep (se 2 (by rfl) ⟨1349964, by rfl⟩ : syracuseStep 3599905 = 2699929) B2699929
theorem B2526779 : Blo 1684042 2526779 := bstep (se 1 (by rfl) ⟨1895084, by rfl⟩ : syracuseStep 2526779 = 3790169) B3790169
theorem B4615795 : Blo 1684042 4615795 := bstep (se 1 (by rfl) ⟨3461846, by rfl⟩ : syracuseStep 4615795 = 6923693) B6923693
theorem B4796023 : Blo 1684042 4796023 := bstep (se 1 (by rfl) ⟨3597017, by rfl⟩ : syracuseStep 4796023 = 7194035) B7194035
theorem B2526839 : Blo 1684042 2526839 := bstep (se 1 (by rfl) ⟨1895129, by rfl⟩ : syracuseStep 2526839 = 3790259) B3790259
theorem B2526863 : Blo 1684042 2526863 := bstep (se 1 (by rfl) ⟨1895147, by rfl⟩ : syracuseStep 2526863 = 3790295) B3790295
theorem B1896079 : Blo 1684042 1896079 := bstep (se 1 (by rfl) ⟨1422059, by rfl⟩ : syracuseStep 1896079 = 2844119) B2844119
theorem B2526905 : Blo 1684042 2526905 := bstep (se 2 (by rfl) ⟨947589, by rfl⟩ : syracuseStep 2526905 = 1895179) B1895179
theorem B2526983 : Blo 1684042 2526983 := bstep (se 1 (by rfl) ⟨1895237, by rfl⟩ : syracuseStep 2526983 = 3790475) B3790475
theorem B12799781 : Blo 1684042 12799781 := bstep (se 4 (by rfl) ⟨1199979, by rfl⟩ : syracuseStep 12799781 = 2399959) B2399959
theorem B2527019 : Blo 1684042 2527019 := bstep (se 1 (by rfl) ⟨1895264, by rfl⟩ : syracuseStep 2527019 = 3790529) B3790529
theorem B2133803 : Blo 1684042 2133803 := bstep (se 1 (by rfl) ⟨1600352, by rfl⟩ : syracuseStep 2133803 = 3200705) B3200705
theorem B2527049 : Blo 1684042 2527049 := bstep (se 2 (by rfl) ⟨947643, by rfl⟩ : syracuseStep 2527049 = 1895287) B1895287
theorem B4263799 : Blo 1684042 4263799 := bstep (se 1 (by rfl) ⟨3197849, by rfl⟩ : syracuseStep 4263799 = 6395699) B6395699
theorem B3600247 : Blo 1684042 3600247 := bstep (se 1 (by rfl) ⟨2700185, by rfl⟩ : syracuseStep 3600247 = 5400371) B5400371
theorem B5689223 : Blo 1684042 5689223 := bstep (se 1 (by rfl) ⟨4266917, by rfl⟩ : syracuseStep 5689223 = 8533835) B8533835
theorem B3649465 : Blo 1684042 3649465 := bstep (se 2 (by rfl) ⟨1368549, by rfl⟩ : syracuseStep 3649465 = 2737099) B2737099
theorem B2527163 : Blo 1684042 2527163 := bstep (se 1 (by rfl) ⟨1895372, by rfl⟩ : syracuseStep 2527163 = 3790745) B3790745
theorem B2527223 : Blo 1684042 2527223 := bstep (se 1 (by rfl) ⟨1895417, by rfl⟩ : syracuseStep 2527223 = 3790835) B3790835
theorem B2527247 : Blo 1684042 2527247 := bstep (se 1 (by rfl) ⟨1895435, by rfl⟩ : syracuseStep 2527247 = 3790871) B3790871
theorem B2527289 : Blo 1684042 2527289 := bstep (se 2 (by rfl) ⟨947733, by rfl⟩ : syracuseStep 2527289 = 1895467) B1895467
theorem B2527367 : Blo 1684042 2527367 := bstep (se 1 (by rfl) ⟨1895525, by rfl⟩ : syracuseStep 2527367 = 3791051) B3791051
theorem B1896583 : Blo 1684042 1896583 := bstep (se 1 (by rfl) ⟨1422437, by rfl⟩ : syracuseStep 1896583 = 2844875) B2844875
theorem B2527403 : Blo 1684042 2527403 := bstep (se 1 (by rfl) ⟨1895552, by rfl⟩ : syracuseStep 2527403 = 3791105) B3791105
theorem B2527433 : Blo 1684042 2527433 := bstep (se 2 (by rfl) ⟨947787, by rfl⟩ : syracuseStep 2527433 = 1895575) B1895575
theorem B5689601 : Blo 1684042 5689601 := bstep (se 2 (by rfl) ⟨2133600, by rfl⟩ : syracuseStep 5689601 = 4267201) B4267201
theorem B3199247 : Blo 1684042 3199247 := bstep (se 1 (by rfl) ⟨2399435, by rfl⟩ : syracuseStep 3199247 = 4798871) B4798871
theorem B4264235 : Blo 1684042 4264235 := bstep (se 1 (by rfl) ⟨3198176, by rfl⟩ : syracuseStep 4264235 = 6396353) B6396353
theorem B3600683 : Blo 1684042 3600683 := bstep (se 1 (by rfl) ⟨2700512, by rfl⟩ : syracuseStep 3600683 = 5401025) B5401025
theorem B2527547 : Blo 1684042 2527547 := bstep (se 1 (by rfl) ⟨1895660, by rfl⟩ : syracuseStep 2527547 = 3791321) B3791321
theorem B1896763 : Blo 1684042 1896763 := bstep (se 1 (by rfl) ⟨1422572, by rfl⟩ : syracuseStep 1896763 = 2845145) B2845145
theorem B2527607 : Blo 1684042 2527607 := bstep (se 1 (by rfl) ⟨1895705, by rfl⟩ : syracuseStep 2527607 = 3791411) B3791411
theorem B2527631 : Blo 1684042 2527631 := bstep (se 1 (by rfl) ⟨1895723, by rfl⟩ : syracuseStep 2527631 = 3791447) B3791447
theorem B3035539 : Blo 1684042 3035539 := bstep (se 1 (by rfl) ⟨2276654, by rfl⟩ : syracuseStep 3035539 = 4553309) B4553309
theorem B8532377 : Blo 1684042 8532377 := bstep (se 2 (by rfl) ⟨3199641, by rfl⟩ : syracuseStep 8532377 = 6399283) B6399283
theorem B2527673 : Blo 1684042 2527673 := bstep (se 2 (by rfl) ⟨947877, by rfl⟩ : syracuseStep 2527673 = 1895755) B1895755
theorem B2527751 : Blo 1684042 2527751 := bstep (se 1 (by rfl) ⟨1895813, by rfl⟩ : syracuseStep 2527751 = 3791627) B3791627
theorem B4796957 : Blo 1684042 4796957 := bstep (se 3 (by rfl) ⟨899429, by rfl⟩ : syracuseStep 4796957 = 1798859) B1798859
theorem B2527787 : Blo 1684042 2527787 := bstep (se 1 (by rfl) ⟨1895840, by rfl⟩ : syracuseStep 2527787 = 3791681) B3791681
theorem B2527817 : Blo 1684042 2527817 := bstep (se 2 (by rfl) ⟨947931, by rfl⟩ : syracuseStep 2527817 = 1895863) B1895863
theorem B3789431 : Blo 1684042 3789431 := bstep (se 1 (by rfl) ⟨2842073, by rfl⟩ : syracuseStep 3789431 = 5684147) B5684147
theorem B1684103 : Blo 1684042 1684103 := bstep (se 1 (by rfl) ⟨1263077, by rfl⟩ : syracuseStep 1684103 = 2526155) B2526155
theorem B1684111 : Blo 1684042 1684111 := bstep (se 1 (by rfl) ⟨1263083, by rfl⟩ : syracuseStep 1684111 = 2526167) B2526167
theorem B1684155 : Blo 1684042 1684155 := bstep (se 1 (by rfl) ⟨1263116, by rfl⟩ : syracuseStep 1684155 = 2526233) B2526233
theorem B2527931 : Blo 1684042 2527931 := bstep (se 1 (by rfl) ⟨1895948, by rfl⟩ : syracuseStep 2527931 = 3791897) B3791897
theorem B10793665 : Blo 1684042 10793665 := bstep (se 2 (by rfl) ⟨4047624, by rfl⟩ : syracuseStep 10793665 = 8095249) B8095249
theorem B2527991 : Blo 1684042 2527991 := bstep (se 1 (by rfl) ⟨1895993, by rfl⟩ : syracuseStep 2527991 = 3791987) B3791987
theorem B1684231 : Blo 1684042 1684231 := bstep (se 1 (by rfl) ⟨1263173, by rfl⟩ : syracuseStep 1684231 = 2526347) B2526347
theorem B1684239 : Blo 1684042 1684239 := bstep (se 1 (by rfl) ⟨1263179, by rfl⟩ : syracuseStep 1684239 = 2526359) B2526359
theorem B2528015 : Blo 1684042 2528015 := bstep (se 1 (by rfl) ⟨1896011, by rfl⟩ : syracuseStep 2528015 = 3792023) B3792023
theorem B3789611 : Blo 1684042 3789611 := bstep (se 1 (by rfl) ⟨2842208, by rfl⟩ : syracuseStep 3789611 = 5684417) B5684417
theorem B2528057 : Blo 1684042 2528057 := bstep (se 2 (by rfl) ⟨948021, by rfl⟩ : syracuseStep 2528057 = 1896043) B1896043
theorem B1684283 : Blo 1684042 1684283 := bstep (se 1 (by rfl) ⟨1263212, by rfl⟩ : syracuseStep 1684283 = 2526425) B2526425
theorem B4797299 : Blo 1684042 4797299 := bstep (se 1 (by rfl) ⟨3597974, by rfl⟩ : syracuseStep 4797299 = 7195949) B7195949
theorem B1684359 : Blo 1684042 1684359 := bstep (se 1 (by rfl) ⟨1263269, by rfl⟩ : syracuseStep 1684359 = 2526539) B2526539
theorem B1799047 : Blo 1684042 1799047 := bstep (se 1 (by rfl) ⟨1349285, by rfl⟩ : syracuseStep 1799047 = 2698571) B2698571
theorem B2528135 : Blo 1684042 2528135 := bstep (se 1 (by rfl) ⟨1896101, by rfl⟩ : syracuseStep 2528135 = 3792203) B3792203
theorem B1684367 : Blo 1684042 1684367 := bstep (se 1 (by rfl) ⟨1263275, by rfl⟩ : syracuseStep 1684367 = 2526551) B2526551
theorem B2528171 : Blo 1684042 2528171 := bstep (se 1 (by rfl) ⟨1896128, by rfl⟩ : syracuseStep 2528171 = 3792257) B3792257
theorem B1684411 : Blo 1684042 1684411 := bstep (se 1 (by rfl) ⟨1263308, by rfl⟩ : syracuseStep 1684411 = 2526617) B2526617
theorem B1708987 : Blo 1684042 1708987 := bstep (se 1 (by rfl) ⟨1281740, by rfl⟩ : syracuseStep 1708987 = 2563481) B2563481
theorem B2528201 : Blo 1684042 2528201 := bstep (se 2 (by rfl) ⟨948075, by rfl⟩ : syracuseStep 2528201 = 1896151) B1896151
theorem B1684487 : Blo 1684042 1684487 := bstep (se 1 (by rfl) ⟨1263365, by rfl⟩ : syracuseStep 1684487 = 2526731) B2526731
theorem B1684495 : Blo 1684042 1684495 := bstep (se 1 (by rfl) ⟨1263371, by rfl⟩ : syracuseStep 1684495 = 2526743) B2526743
theorem B6394909 : Blo 1684042 6394909 := bstep (se 3 (by rfl) ⟨1199045, by rfl⟩ : syracuseStep 6394909 = 2398091) B2398091
theorem B5264417 : Blo 1684042 5264417 := bstep (se 2 (by rfl) ⟨1974156, by rfl⟩ : syracuseStep 5264417 = 3948313) B3948313
theorem B1684539 : Blo 1684042 1684539 := bstep (se 1 (by rfl) ⟨1263404, by rfl⟩ : syracuseStep 1684539 = 2526809) B2526809
theorem B2528315 : Blo 1684042 2528315 := bstep (se 1 (by rfl) ⟨1896236, by rfl⟩ : syracuseStep 2528315 = 3792473) B3792473
theorem B4265075 : Blo 1684042 4265075 := bstep (se 1 (by rfl) ⟨3198806, by rfl⟩ : syracuseStep 4265075 = 6397613) B6397613
theorem B2528375 : Blo 1684042 2528375 := bstep (se 1 (by rfl) ⟨1896281, by rfl⟩ : syracuseStep 2528375 = 3792563) B3792563
theorem B1684615 : Blo 1684042 1684615 := bstep (se 1 (by rfl) ⟨1263461, by rfl⟩ : syracuseStep 1684615 = 2526923) B2526923
theorem B4265095 : Blo 1684042 4265095 := bstep (se 1 (by rfl) ⟨3198821, by rfl⟩ : syracuseStep 4265095 = 6397643) B6397643
theorem B1684623 : Blo 1684042 1684623 := bstep (se 1 (by rfl) ⟨1263467, by rfl⟩ : syracuseStep 1684623 = 2526935) B2526935
theorem B2528399 : Blo 1684042 2528399 := bstep (se 1 (by rfl) ⟨1896299, by rfl⟩ : syracuseStep 2528399 = 3792599) B3792599
theorem B3789971 : Blo 1684042 3789971 := bstep (se 1 (by rfl) ⟨2842478, by rfl⟩ : syracuseStep 3789971 = 5684957) B5684957
theorem B38925461 : Blo 1684042 38925461 := bstep (se 6 (by rfl) ⟨912315, by rfl⟩ : syracuseStep 38925461 = 1824631) B1824631
theorem B2528441 : Blo 1684042 2528441 := bstep (se 2 (by rfl) ⟨948165, by rfl⟩ : syracuseStep 2528441 = 1896331) B1896331
theorem B1684667 : Blo 1684042 1684667 := bstep (se 1 (by rfl) ⟨1263500, by rfl⟩ : syracuseStep 1684667 = 2527001) B2527001
theorem B3790025 : Blo 1684042 3790025 := bstep (se 2 (by rfl) ⟨1421259, by rfl⟩ : syracuseStep 3790025 = 2842519) B2842519
theorem B1684743 : Blo 1684042 1684743 := bstep (se 1 (by rfl) ⟨1263557, by rfl⟩ : syracuseStep 1684743 = 2527115) B2527115
theorem B2528519 : Blo 1684042 2528519 := bstep (se 1 (by rfl) ⟨1896389, by rfl⟩ : syracuseStep 2528519 = 3792779) B3792779
theorem B1684751 : Blo 1684042 1684751 := bstep (se 1 (by rfl) ⟨1263563, by rfl⟩ : syracuseStep 1684751 = 2527127) B2527127
theorem B2528555 : Blo 1684042 2528555 := bstep (se 1 (by rfl) ⟨1896416, by rfl⟩ : syracuseStep 2528555 = 3792833) B3792833
theorem B1684795 : Blo 1684042 1684795 := bstep (se 1 (by rfl) ⟨1263596, by rfl⟩ : syracuseStep 1684795 = 2527193) B2527193
theorem B4797755 : Blo 1684042 4797755 := bstep (se 1 (by rfl) ⟨3598316, by rfl⟩ : syracuseStep 4797755 = 7196633) B7196633
theorem B2528585 : Blo 1684042 2528585 := bstep (se 2 (by rfl) ⟨948219, by rfl⟩ : syracuseStep 2528585 = 1896439) B1896439
theorem B1684871 : Blo 1684042 1684871 := bstep (se 1 (by rfl) ⟨1263653, by rfl⟩ : syracuseStep 1684871 = 2527307) B2527307
theorem B21591431 : Blo 1684042 21591431 := bstep (se 1 (by rfl) ⟨16193573, by rfl⟩ : syracuseStep 21591431 = 32387147) B32387147
theorem B25949575 : Blo 1684042 25949575 := bstep (se 1 (by rfl) ⟨19462181, by rfl⟩ : syracuseStep 25949575 = 38924363) B38924363
theorem B1684879 : Blo 1684042 1684879 := bstep (se 1 (by rfl) ⟨1263659, by rfl⟩ : syracuseStep 1684879 = 2527319) B2527319
theorem B4265369 : Blo 1684042 4265369 := bstep (se 2 (by rfl) ⟨1599513, by rfl⟩ : syracuseStep 4265369 = 3199027) B3199027
theorem B1684923 : Blo 1684042 1684923 := bstep (se 1 (by rfl) ⟨1263692, by rfl⟩ : syracuseStep 1684923 = 2527385) B2527385
theorem B2528699 : Blo 1684042 2528699 := bstep (se 1 (by rfl) ⟨1896524, by rfl⟩ : syracuseStep 2528699 = 3793049) B3793049
theorem B21878225 : Blo 1684042 21878225 := bstep (se 2 (by rfl) ⟨8204334, by rfl⟩ : syracuseStep 21878225 = 16408669) B16408669
theorem B2528759 : Blo 1684042 2528759 := bstep (se 1 (by rfl) ⟨1896569, by rfl⟩ : syracuseStep 2528759 = 3793139) B3793139
theorem B1684999 : Blo 1684042 1684999 := bstep (se 1 (by rfl) ⟨1263749, by rfl⟩ : syracuseStep 1684999 = 2527499) B2527499
theorem B1685007 : Blo 1684042 1685007 := bstep (se 1 (by rfl) ⟨1263755, by rfl⟩ : syracuseStep 1685007 = 2527511) B2527511
theorem B2528783 : Blo 1684042 2528783 := bstep (se 1 (by rfl) ⟨1896587, by rfl⟩ : syracuseStep 2528783 = 3793175) B3793175
theorem B7198237 : Blo 1684042 7198237 := bstep (se 3 (by rfl) ⟨1349669, by rfl⟩ : syracuseStep 7198237 = 2699339) B2699339
theorem B2528825 : Blo 1684042 2528825 := bstep (se 2 (by rfl) ⟨948309, by rfl⟩ : syracuseStep 2528825 = 1896619) B1896619
theorem B1685051 : Blo 1684042 1685051 := bstep (se 1 (by rfl) ⟨1263788, by rfl⟩ : syracuseStep 1685051 = 2527577) B2527577
theorem B4265531 : Blo 1684042 4265531 := bstep (se 1 (by rfl) ⟨3199148, by rfl⟩ : syracuseStep 4265531 = 6398297) B6398297
theorem B6075965 : Blo 1684042 6075965 := bstep (se 3 (by rfl) ⟨1139243, by rfl⟩ : syracuseStep 6075965 = 2278487) B2278487
theorem B54629963 : Blo 1684042 54629963 := bstep (se 1 (by rfl) ⟨40972472, by rfl⟩ : syracuseStep 54629963 = 81944945) B81944945
theorem B14595661 : Blo 1684042 14595661 := bstep (se 3 (by rfl) ⟨2736686, by rfl⟩ : syracuseStep 14595661 = 5473373) B5473373
theorem B12793463 : Blo 1684042 12793463 := bstep (se 1 (by rfl) ⟨9595097, by rfl⟩ : syracuseStep 12793463 = 19190195) B19190195
theorem B1685127 : Blo 1684042 1685127 := bstep (se 1 (by rfl) ⟨1263845, by rfl⟩ : syracuseStep 1685127 = 2527691) B2527691
theorem B2528903 : Blo 1684042 2528903 := bstep (se 1 (by rfl) ⟨1896677, by rfl⟩ : syracuseStep 2528903 = 3793355) B3793355
theorem B1685135 : Blo 1684042 1685135 := bstep (se 1 (by rfl) ⟨1263851, by rfl⟩ : syracuseStep 1685135 = 2527703) B2527703
theorem B2528939 : Blo 1684042 2528939 := bstep (se 1 (by rfl) ⟨1896704, by rfl⟩ : syracuseStep 2528939 = 3793409) B3793409
theorem B1685179 : Blo 1684042 1685179 := bstep (se 1 (by rfl) ⟨1263884, by rfl⟩ : syracuseStep 1685179 = 2527769) B2527769
theorem B1799867 : Blo 1684042 1799867 := bstep (se 1 (by rfl) ⟨1349900, by rfl⟩ : syracuseStep 1799867 = 2699801) B2699801
theorem B7198409 : Blo 1684042 7198409 := bstep (se 2 (by rfl) ⟨2699403, by rfl⟩ : syracuseStep 7198409 = 5398807) B5398807
theorem B2528969 : Blo 1684042 2528969 := bstep (se 2 (by rfl) ⟨948363, by rfl⟩ : syracuseStep 2528969 = 1896727) B1896727
theorem B1685255 : Blo 1684042 1685255 := bstep (se 1 (by rfl) ⟨1263941, by rfl⟩ : syracuseStep 1685255 = 2527883) B2527883
theorem B4265743 : Blo 1684042 4265743 := bstep (se 1 (by rfl) ⟨3199307, by rfl⟩ : syracuseStep 4265743 = 6398615) B6398615
theorem B1685263 : Blo 1684042 1685263 := bstep (se 1 (by rfl) ⟨1263947, by rfl⟩ : syracuseStep 1685263 = 2527895) B2527895
theorem B10385189 : Blo 1684042 10385189 := bstep (se 4 (by rfl) ⟨973611, by rfl⟩ : syracuseStep 10385189 = 1947223) B1947223
theorem B1685307 : Blo 1684042 1685307 := bstep (se 1 (by rfl) ⟨1263980, by rfl⟩ : syracuseStep 1685307 = 2527961) B2527961
theorem B3790727 : Blo 1684042 3790727 := bstep (se 1 (by rfl) ⟨2843045, by rfl⟩ : syracuseStep 3790727 = 5686091) B5686091
theorem B1685383 : Blo 1684042 1685383 := bstep (se 1 (by rfl) ⟨1264037, by rfl⟩ : syracuseStep 1685383 = 2528075) B2528075
theorem B1685391 : Blo 1684042 1685391 := bstep (se 1 (by rfl) ⟨1264043, by rfl⟩ : syracuseStep 1685391 = 2528087) B2528087
theorem B1685435 : Blo 1684042 1685435 := bstep (se 1 (by rfl) ⟨1264076, by rfl⟩ : syracuseStep 1685435 = 2528153) B2528153
theorem B1685511 : Blo 1684042 1685511 := bstep (se 1 (by rfl) ⟨1264133, by rfl⟩ : syracuseStep 1685511 = 2528267) B2528267
theorem B1685519 : Blo 1684042 1685519 := bstep (se 1 (by rfl) ⟨1264139, by rfl⟩ : syracuseStep 1685519 = 2528279) B2528279
theorem B29571095 : Blo 1684042 29571095 := bstep (se 1 (by rfl) ⟨22178321, by rfl⟩ : syracuseStep 29571095 = 44356643) B44356643
theorem B4266017 : Blo 1684042 4266017 := bstep (se 2 (by rfl) ⟨1599756, by rfl⟩ : syracuseStep 4266017 = 3199513) B3199513
theorem B3790907 : Blo 1684042 3790907 := bstep (se 1 (by rfl) ⟨2843180, by rfl⟩ : syracuseStep 3790907 = 5686361) B5686361
theorem B1685563 : Blo 1684042 1685563 := bstep (se 1 (by rfl) ⟨1264172, by rfl⟩ : syracuseStep 1685563 = 2528345) B2528345
theorem B15374423 : Blo 1684042 15374423 := bstep (se 1 (by rfl) ⟨11530817, by rfl⟩ : syracuseStep 15374423 = 23061635) B23061635
theorem B37427293 : Blo 1684042 37427293 := bstep (se 3 (by rfl) ⟨7017617, by rfl⟩ : syracuseStep 37427293 = 14035235) B14035235
theorem B2562167 : Blo 1684042 2562167 := bstep (se 1 (by rfl) ⟨1921625, by rfl⟩ : syracuseStep 2562167 = 3843251) B3843251
theorem B1685639 : Blo 1684042 1685639 := bstep (se 1 (by rfl) ⟨1264229, by rfl⟩ : syracuseStep 1685639 = 2528459) B2528459
theorem B1685647 : Blo 1684042 1685647 := bstep (se 1 (by rfl) ⟨1264235, by rfl⟩ : syracuseStep 1685647 = 2528471) B2528471
theorem B3791033 : Blo 1684042 3791033 := bstep (se 2 (by rfl) ⟨1421637, by rfl⟩ : syracuseStep 3791033 = 2843275) B2843275
theorem B1685691 : Blo 1684042 1685691 := bstep (se 1 (by rfl) ⟨1264268, by rfl⟩ : syracuseStep 1685691 = 2528537) B2528537
theorem B3037385 : Blo 1684042 3037385 := bstep (se 2 (by rfl) ⟨1139019, by rfl⟩ : syracuseStep 3037385 = 2278039) B2278039
theorem B1685767 : Blo 1684042 1685767 := bstep (se 1 (by rfl) ⟨1264325, by rfl⟩ : syracuseStep 1685767 = 2528651) B2528651
theorem B1685775 : Blo 1684042 1685775 := bstep (se 1 (by rfl) ⟨1264331, by rfl⟩ : syracuseStep 1685775 = 2528663) B2528663
theorem B18209083 : Blo 1684042 18209083 := bstep (se 1 (by rfl) ⟨13656812, by rfl⟩ : syracuseStep 18209083 = 27313625) B27313625
theorem B1685819 : Blo 1684042 1685819 := bstep (se 1 (by rfl) ⟨1264364, by rfl⟩ : syracuseStep 1685819 = 2528729) B2528729
theorem B1685895 : Blo 1684042 1685895 := bstep (se 1 (by rfl) ⟨1264421, by rfl⟩ : syracuseStep 1685895 = 2528843) B2528843
theorem B1685903 : Blo 1684042 1685903 := bstep (se 1 (by rfl) ⟨1264427, by rfl⟩ : syracuseStep 1685903 = 2528855) B2528855
theorem B19200401 : Blo 1684042 19200401 := bstep (se 2 (by rfl) ⟨7200150, by rfl⟩ : syracuseStep 19200401 = 14400301) B14400301
theorem B1685947 : Blo 1684042 1685947 := bstep (se 1 (by rfl) ⟨1264460, by rfl⟩ : syracuseStep 1685947 = 2528921) B2528921
theorem B1686023 : Blo 1684042 1686023 := bstep (se 1 (by rfl) ⟨1264517, by rfl⟩ : syracuseStep 1686023 = 2529035) B2529035
theorem B3791375 : Blo 1684042 3791375 := bstep (se 1 (by rfl) ⟨2843531, by rfl⟩ : syracuseStep 3791375 = 5687063) B5687063
theorem B1686031 : Blo 1684042 1686031 := bstep (se 1 (by rfl) ⟨1264523, by rfl⟩ : syracuseStep 1686031 = 2529047) B2529047
theorem B3791393 : Blo 1684042 3791393 := bstep (se 2 (by rfl) ⟨1421772, by rfl⟩ : syracuseStep 3791393 = 2843545) B2843545
theorem B12794435 : Blo 1684042 12794435 := bstep (se 1 (by rfl) ⟨9595826, by rfl⟩ : syracuseStep 12794435 = 19191653) B19191653
theorem B8526707 : Blo 1684042 8526707 := bstep (se 1 (by rfl) ⟨6395030, by rfl⟩ : syracuseStep 8526707 = 12790061) B12790061
theorem B3791735 : Blo 1684042 3791735 := bstep (se 1 (by rfl) ⟨2843801, by rfl⟩ : syracuseStep 3791735 = 5687603) B5687603
theorem B6831001 : Blo 1684042 6831001 := bstep (se 2 (by rfl) ⟨2561625, by rfl⟩ : syracuseStep 6831001 = 5123251) B5123251
theorem B8534969 : Blo 1684042 8534969 := bstep (se 2 (by rfl) ⟨3200613, by rfl⟩ : syracuseStep 8534969 = 6401227) B6401227
theorem B4864969 : Blo 1684042 4864969 := bstep (se 2 (by rfl) ⟨1824363, by rfl⟩ : syracuseStep 4864969 = 3648727) B3648727
theorem B8092619 : Blo 1684042 8092619 := bstep (se 1 (by rfl) ⟨6069464, by rfl⟩ : syracuseStep 8092619 = 12138929) B12138929
theorem B4267019 : Blo 1684042 4267019 := bstep (se 1 (by rfl) ⟨3200264, by rfl⟩ : syracuseStep 4267019 = 6400529) B6400529
theorem B3791915 : Blo 1684042 3791915 := bstep (se 1 (by rfl) ⟨2843936, by rfl⟩ : syracuseStep 3791915 = 5687873) B5687873
theorem B2563115 : Blo 1684042 2563115 := bstep (se 1 (by rfl) ⟨1922336, by rfl⟩ : syracuseStep 2563115 = 3844673) B3844673
theorem B41016451 : Blo 1684042 41016451 := bstep (se 1 (by rfl) ⟨30762338, by rfl⟩ : syracuseStep 41016451 = 61524677) B61524677
theorem B9723053 : Blo 1684042 9723053 := bstep (se 3 (by rfl) ⟨1823072, by rfl⟩ : syracuseStep 9723053 = 3646145) B3646145
theorem B2841871 : Blo 1684042 2841871 := bstep (se 1 (by rfl) ⟨2131403, by rfl⟩ : syracuseStep 2841871 = 4262807) B4262807
theorem B8092943 : Blo 1684042 8092943 := bstep (se 1 (by rfl) ⟨6069707, by rfl⟩ : syracuseStep 8092943 = 12139415) B12139415
theorem B8527193 : Blo 1684042 8527193 := bstep (se 2 (by rfl) ⟨3197697, by rfl⟩ : syracuseStep 8527193 = 6395395) B6395395
theorem B10796435 : Blo 1684042 10796435 := bstep (se 1 (by rfl) ⟨8097326, by rfl⟩ : syracuseStep 10796435 = 16194653) B16194653
theorem B3792275 : Blo 1684042 3792275 := bstep (se 1 (by rfl) ⟨2844206, by rfl⟩ : syracuseStep 3792275 = 5688413) B5688413
theorem B5684633 : Blo 1684042 5684633 := bstep (se 2 (by rfl) ⟨2131737, by rfl⟩ : syracuseStep 5684633 = 4263475) B4263475
theorem B3792329 : Blo 1684042 3792329 := bstep (se 2 (by rfl) ⟨1422123, by rfl⟩ : syracuseStep 3792329 = 2844247) B2844247
theorem B9592343 : Blo 1684042 9592343 := bstep (se 1 (by rfl) ⟨7194257, by rfl⟩ : syracuseStep 9592343 = 14388515) B14388515
theorem B7200323 : Blo 1684042 7200323 := bstep (se 1 (by rfl) ⟨5400242, by rfl⟩ : syracuseStep 7200323 = 10800485) B10800485
theorem B2399863 : Blo 1684042 2399863 := bstep (se 1 (by rfl) ⟨1799897, by rfl⟩ : syracuseStep 2399863 = 3599795) B3599795
theorem B4267667 : Blo 1684042 4267667 := bstep (se 1 (by rfl) ⟨3200750, by rfl⟩ : syracuseStep 4267667 = 6401501) B6401501
theorem B28802789 : Blo 1684042 28802789 := bstep (se 4 (by rfl) ⟨2700261, by rfl⟩ : syracuseStep 28802789 = 5400523) B5400523
theorem B4218635 : Blo 1684042 4218635 := bstep (se 1 (by rfl) ⟨3163976, by rfl⟩ : syracuseStep 4218635 = 6327953) B6327953
theorem B2842411 : Blo 1684042 2842411 := bstep (se 1 (by rfl) ⟨2131808, by rfl⟩ : syracuseStep 2842411 = 4263617) B4263617
theorem B6397811 : Blo 1684042 6397811 := bstep (se 1 (by rfl) ⟨4798358, by rfl⟩ : syracuseStep 6397811 = 9596717) B9596717
theorem B2842553 : Blo 1684042 2842553 := bstep (se 2 (by rfl) ⟨1065957, by rfl⟩ : syracuseStep 2842553 = 2131915) B2131915
theorem B2400187 : Blo 1684042 2400187 := bstep (se 1 (by rfl) ⟨1800140, by rfl⟩ : syracuseStep 2400187 = 3600281) B3600281
theorem B8093753 : Blo 1684042 8093753 := bstep (se 2 (by rfl) ⟨3035157, by rfl⟩ : syracuseStep 8093753 = 6070315) B6070315
theorem B2842681 : Blo 1684042 2842681 := bstep (se 2 (by rfl) ⟨1066005, by rfl⟩ : syracuseStep 2842681 = 2132011) B2132011
theorem B3793067 : Blo 1684042 3793067 := bstep (se 1 (by rfl) ⟨2844800, by rfl⟩ : syracuseStep 3793067 = 5689601) B5689601
theorem B2842823 : Blo 1684042 2842823 := bstep (se 1 (by rfl) ⟨2132117, by rfl⟩ : syracuseStep 2842823 = 4264235) B4264235
theorem B2400455 : Blo 1684042 2400455 := bstep (se 1 (by rfl) ⟨1800341, by rfl⟩ : syracuseStep 2400455 = 3600683) B3600683
theorem B2842985 : Blo 1684042 2842985 := bstep (se 2 (by rfl) ⟨1066119, by rfl⟩ : syracuseStep 2842985 = 2132239) B2132239
theorem B2843383 : Blo 1684042 2843383 := bstep (se 1 (by rfl) ⟨2132537, by rfl⟩ : syracuseStep 2843383 = 4265075) B4265075
theorem B14394287 : Blo 1684042 14394287 := bstep (se 1 (by rfl) ⟨10795715, by rfl⟩ : syracuseStep 14394287 = 21591431) B21591431
theorem B5686199 : Blo 1684042 5686199 := bstep (se 1 (by rfl) ⟨4264649, by rfl⟩ : syracuseStep 5686199 = 8529299) B8529299
theorem B2843579 : Blo 1684042 2843579 := bstep (se 1 (by rfl) ⟨2132684, by rfl⟩ : syracuseStep 2843579 = 4265369) B4265369
theorem B2843687 : Blo 1684042 2843687 := bstep (se 1 (by rfl) ⟨2132765, by rfl⟩ : syracuseStep 2843687 = 4265531) B4265531
theorem B8528975 : Blo 1684042 8528975 := bstep (se 1 (by rfl) ⟨6396731, by rfl⟩ : syracuseStep 8528975 = 12793463) B12793463
theorem B11846735 : Blo 1684042 11846735 := bstep (se 1 (by rfl) ⟨8885051, by rfl⟩ : syracuseStep 11846735 = 17770103) B17770103
theorem B6923459 : Blo 1684042 6923459 := bstep (se 1 (by rfl) ⟨5192594, by rfl⟩ : syracuseStep 6923459 = 10385189) B10385189
theorem B2278649 : Blo 1684042 2278649 := bstep (se 2 (by rfl) ⟨854493, by rfl⟩ : syracuseStep 2278649 = 1708987) B1708987
theorem B2843977 : Blo 1684042 2843977 := bstep (se 2 (by rfl) ⟨1066491, by rfl⟩ : syracuseStep 2843977 = 2132983) B2132983
theorem B2844011 : Blo 1684042 2844011 := bstep (se 1 (by rfl) ⟨2133008, by rfl⟩ : syracuseStep 2844011 = 4266017) B4266017
theorem B10249615 : Blo 1684042 10249615 := bstep (se 1 (by rfl) ⟨7687211, by rfl⟩ : syracuseStep 10249615 = 15374423) B15374423
theorem B36922825 : Blo 1684042 36922825 := bstep (se 2 (by rfl) ⟨13846059, by rfl⟩ : syracuseStep 36922825 = 27692119) B27692119
theorem B2024923 : Blo 1684042 2024923 := bstep (se 1 (by rfl) ⟨1518692, by rfl⟩ : syracuseStep 2024923 = 3037385) B3037385
theorem B14403035 : Blo 1684042 14403035 := bstep (se 1 (by rfl) ⟨10802276, by rfl⟩ : syracuseStep 14403035 = 21604553) B21604553
theorem B5686793 : Blo 1684042 5686793 := bstep (se 2 (by rfl) ⟨2132547, by rfl⟩ : syracuseStep 5686793 = 4265095) B4265095
theorem B2131535 : Blo 1684042 2131535 := bstep (se 1 (by rfl) ⟨1598651, by rfl⟩ : syracuseStep 2131535 = 3197303) B3197303
theorem B9111179 : Blo 1684042 9111179 := bstep (se 1 (by rfl) ⟨6833384, by rfl⟩ : syracuseStep 9111179 = 13666769) B13666769
theorem B8529623 : Blo 1684042 8529623 := bstep (se 1 (by rfl) ⟨6397217, by rfl⟩ : syracuseStep 8529623 = 12794435) B12794435
theorem B24610553 : Blo 1684042 24610553 := bstep (se 2 (by rfl) ⟨9228957, by rfl⟩ : syracuseStep 24610553 = 18457915) B18457915
theorem B2844409 : Blo 1684042 2844409 := bstep (se 2 (by rfl) ⟨1066653, by rfl⟩ : syracuseStep 2844409 = 2133307) B2133307
theorem B8210219 : Blo 1684042 8210219 := bstep (se 1 (by rfl) ⟨6157664, by rfl⟩ : syracuseStep 8210219 = 12315329) B12315329
theorem B9594733 : Blo 1684042 9594733 := bstep (se 3 (by rfl) ⟨1799012, by rfl⟩ : syracuseStep 9594733 = 3598025) B3598025
theorem B8095751 : Blo 1684042 8095751 := bstep (se 1 (by rfl) ⟨6071813, by rfl⟩ : syracuseStep 8095751 = 12143627) B12143627
theorem B2844679 : Blo 1684042 2844679 := bstep (se 1 (by rfl) ⟨2133509, by rfl⟩ : syracuseStep 2844679 = 4267019) B4267019
theorem B16189541 : Blo 1684042 16189541 := bstep (se 4 (by rfl) ⟨1517769, by rfl⟩ : syracuseStep 16189541 = 3035539) B3035539
theorem B6482035 : Blo 1684042 6482035 := bstep (se 1 (by rfl) ⟨4861526, by rfl⟩ : syracuseStep 6482035 = 9723053) B9723053
theorem B6154393 : Blo 1684042 6154393 := bstep (se 2 (by rfl) ⟨2307897, by rfl⟩ : syracuseStep 6154393 = 4615795) B4615795
theorem B62310707 : Blo 1684042 62310707 := bstep (se 1 (by rfl) ⟨46733030, by rfl⟩ : syracuseStep 62310707 = 93466061) B93466061
theorem B5687657 : Blo 1684042 5687657 := bstep (se 2 (by rfl) ⟨2132871, by rfl⟩ : syracuseStep 5687657 = 4265743) B4265743
theorem B2845111 : Blo 1684042 2845111 := bstep (se 1 (by rfl) ⟨2133833, by rfl⟩ : syracuseStep 2845111 = 4267667) B4267667
theorem B2812423 : Blo 1684042 2812423 := bstep (se 1 (by rfl) ⟨2109317, by rfl⟩ : syracuseStep 2812423 = 4218635) B4218635
theorem B1895035 : Blo 1684042 1895035 := bstep (se 1 (by rfl) ⟨1421276, by rfl⟩ : syracuseStep 1895035 = 2842553) B2842553
theorem B6400727 : Blo 1684042 6400727 := bstep (se 1 (by rfl) ⟨4800545, by rfl⟩ : syracuseStep 6400727 = 9601091) B9601091
theorem B2132831 : Blo 1684042 2132831 := bstep (se 1 (by rfl) ⟨1599623, by rfl⟩ : syracuseStep 2132831 = 3199247) B3199247
theorem B5688251 : Blo 1684042 5688251 := bstep (se 1 (by rfl) ⟨4266188, by rfl⟩ : syracuseStep 5688251 = 8532377) B8532377
theorem B3197971 : Blo 1684042 3197971 := bstep (se 1 (by rfl) ⟨2398478, by rfl⟩ : syracuseStep 3197971 = 4796957) B4796957
theorem B4262969 : Blo 1684042 4262969 := bstep (se 2 (by rfl) ⟨1598613, by rfl⟩ : syracuseStep 4262969 = 3197227) B3197227
theorem B2526287 : Blo 1684042 2526287 := bstep (se 1 (by rfl) ⟨1894715, by rfl⟩ : syracuseStep 2526287 = 3789431) B3789431
theorem B1895503 : Blo 1684042 1895503 := bstep (se 1 (by rfl) ⟨1421627, by rfl⟩ : syracuseStep 1895503 = 2843255) B2843255
theorem B27339893 : Blo 1684042 27339893 := bstep (se 5 (by rfl) ⟨1281557, by rfl⟩ : syracuseStep 27339893 = 2563115) B2563115
theorem B2526407 : Blo 1684042 2526407 := bstep (se 1 (by rfl) ⟨1894805, by rfl⟩ : syracuseStep 2526407 = 3789611) B3789611
theorem B8645879 : Blo 1684042 8645879 := bstep (se 1 (by rfl) ⟨6484409, by rfl⟩ : syracuseStep 8645879 = 12968819) B12968819
theorem B3198199 : Blo 1684042 3198199 := bstep (se 1 (by rfl) ⟨2398649, by rfl⟩ : syracuseStep 3198199 = 4797299) B4797299
theorem B2526569 : Blo 1684042 2526569 := bstep (se 2 (by rfl) ⟨947463, by rfl⟩ : syracuseStep 2526569 = 1894927) B1894927
theorem B3509611 : Blo 1684042 3509611 := bstep (se 1 (by rfl) ⟨2632208, by rfl⟩ : syracuseStep 3509611 = 5264417) B5264417
theorem B2526647 : Blo 1684042 2526647 := bstep (se 1 (by rfl) ⟨1894985, by rfl⟩ : syracuseStep 2526647 = 3789971) B3789971
theorem B2526683 : Blo 1684042 2526683 := bstep (se 1 (by rfl) ⟨1895012, by rfl⟩ : syracuseStep 2526683 = 3790025) B3790025
theorem B1895899 : Blo 1684042 1895899 := bstep (se 1 (by rfl) ⟨1421924, by rfl⟩ : syracuseStep 1895899 = 2843849) B2843849
theorem B10792435 : Blo 1684042 10792435 := bstep (se 1 (by rfl) ⟨8094326, by rfl⟩ : syracuseStep 10792435 = 16188653) B16188653
theorem B3198503 : Blo 1684042 3198503 := bstep (se 1 (by rfl) ⟨2398877, by rfl⟩ : syracuseStep 3198503 = 4797755) B4797755
theorem B14585483 : Blo 1684042 14585483 := bstep (se 1 (by rfl) ⟨10939112, by rfl⟩ : syracuseStep 14585483 = 21878225) B21878225
theorem B4050643 : Blo 1684042 4050643 := bstep (se 1 (by rfl) ⟨3037982, by rfl⟩ : syracuseStep 4050643 = 6075965) B6075965
theorem B16412483 : Blo 1684042 16412483 := bstep (se 1 (by rfl) ⟨12309362, by rfl⟩ : syracuseStep 16412483 = 24618725) B24618725
theorem B2527151 : Blo 1684042 2527151 := bstep (se 1 (by rfl) ⟨1895363, by rfl⟩ : syracuseStep 2527151 = 3790727) B3790727
theorem B1896367 : Blo 1684042 1896367 := bstep (se 1 (by rfl) ⟨1422275, by rfl⟩ : syracuseStep 1896367 = 2844551) B2844551
theorem B2527241 : Blo 1684042 2527241 := bstep (se 2 (by rfl) ⟨947715, by rfl⟩ : syracuseStep 2527241 = 1895431) B1895431
theorem B19714063 : Blo 1684042 19714063 := bstep (se 1 (by rfl) ⟨14785547, by rfl⟩ : syracuseStep 19714063 = 29571095) B29571095
theorem B2527271 : Blo 1684042 2527271 := bstep (se 1 (by rfl) ⟨1895453, by rfl⟩ : syracuseStep 2527271 = 3790907) B3790907
theorem B1708111 : Blo 1684042 1708111 := bstep (se 1 (by rfl) ⟨1281083, by rfl⟩ : syracuseStep 1708111 = 2562167) B2562167
theorem B12152909 : Blo 1684042 12152909 := bstep (se 3 (by rfl) ⟨2278670, by rfl⟩ : syracuseStep 12152909 = 4557341) B4557341
theorem B2527355 : Blo 1684042 2527355 := bstep (se 1 (by rfl) ⟨1895516, by rfl⟩ : syracuseStep 2527355 = 3791033) B3791033
theorem B2527481 : Blo 1684042 2527481 := bstep (se 2 (by rfl) ⟨947805, by rfl⟩ : syracuseStep 2527481 = 1895611) B1895611
theorem B12800267 : Blo 1684042 12800267 := bstep (se 1 (by rfl) ⟨9600200, by rfl⟩ : syracuseStep 12800267 = 19200401) B19200401
theorem B2527583 : Blo 1684042 2527583 := bstep (se 1 (by rfl) ⟨1895687, by rfl⟩ : syracuseStep 2527583 = 3791375) B3791375
theorem B3789161 : Blo 1684042 3789161 := bstep (se 2 (by rfl) ⟨1420935, by rfl⟩ : syracuseStep 3789161 = 2841871) B2841871
theorem B2527595 : Blo 1684042 2527595 := bstep (se 1 (by rfl) ⟨1895696, by rfl⟩ : syracuseStep 2527595 = 3791393) B3791393
theorem B6394241 : Blo 1684042 6394241 := bstep (se 2 (by rfl) ⟨2397840, by rfl⟩ : syracuseStep 6394241 = 4795681) B4795681
theorem B34599433 : Blo 1684042 34599433 := bstep (se 2 (by rfl) ⟨12974787, by rfl⟩ : syracuseStep 34599433 = 25949575) B25949575
theorem B8532539 : Blo 1684042 8532539 := bstep (se 1 (by rfl) ⟨6399404, by rfl⟩ : syracuseStep 8532539 = 12798809) B12798809
theorem B1684047 : Blo 1684042 1684047 := bstep (se 1 (by rfl) ⟨1263035, by rfl⟩ : syracuseStep 1684047 = 2526071) B2526071
theorem B2527823 : Blo 1684042 2527823 := bstep (se 1 (by rfl) ⟨1895867, by rfl⟩ : syracuseStep 2527823 = 3791735) B3791735
theorem B1684063 : Blo 1684042 1684063 := bstep (se 1 (by rfl) ⟨1263047, by rfl⟩ : syracuseStep 1684063 = 2526095) B2526095
theorem B1684091 : Blo 1684042 1684091 := bstep (se 1 (by rfl) ⟨1263068, by rfl⟩ : syracuseStep 1684091 = 2526137) B2526137
theorem B5689979 : Blo 1684042 5689979 := bstep (se 1 (by rfl) ⟨4267484, by rfl⟩ : syracuseStep 5689979 = 8534969) B8534969
theorem B5395079 : Blo 1684042 5395079 := bstep (se 1 (by rfl) ⟨4046309, by rfl⟩ : syracuseStep 5395079 = 8092619) B8092619
theorem B1684143 : Blo 1684042 1684143 := bstep (se 1 (by rfl) ⟨1263107, by rfl⟩ : syracuseStep 1684143 = 2526215) B2526215
theorem B1684167 : Blo 1684042 1684167 := bstep (se 1 (by rfl) ⟨1263125, by rfl⟩ : syracuseStep 1684167 = 2526251) B2526251
theorem B2527943 : Blo 1684042 2527943 := bstep (se 1 (by rfl) ⟨1895957, by rfl⟩ : syracuseStep 2527943 = 3791915) B3791915
theorem B9597649 : Blo 1684042 9597649 := bstep (se 2 (by rfl) ⟨3599118, by rfl⟩ : syracuseStep 9597649 = 7198237) B7198237
theorem B4797139 : Blo 1684042 4797139 := bstep (se 1 (by rfl) ⟨3597854, by rfl⟩ : syracuseStep 4797139 = 7195709) B7195709
theorem B1684187 : Blo 1684042 1684187 := bstep (se 1 (by rfl) ⟨1263140, by rfl⟩ : syracuseStep 1684187 = 2526281) B2526281
theorem B19460881 : Blo 1684042 19460881 := bstep (se 2 (by rfl) ⟨7297830, by rfl⟩ : syracuseStep 19460881 = 14595661) B14595661
theorem B5690141 : Blo 1684042 5690141 := bstep (se 3 (by rfl) ⟨1066901, by rfl⟩ : syracuseStep 5690141 = 2133803) B2133803
theorem B1684263 : Blo 1684042 1684263 := bstep (se 1 (by rfl) ⟨1263197, by rfl⟩ : syracuseStep 1684263 = 2526395) B2526395
theorem B6394697 : Blo 1684042 6394697 := bstep (se 2 (by rfl) ⟨2398011, by rfl⟩ : syracuseStep 6394697 = 4796023) B4796023
theorem B3199817 : Blo 1684042 3199817 := bstep (se 2 (by rfl) ⟨1199931, by rfl⟩ : syracuseStep 3199817 = 2399863) B2399863
theorem B1684303 : Blo 1684042 1684303 := bstep (se 1 (by rfl) ⟨1263227, by rfl⟩ : syracuseStep 1684303 = 2526455) B2526455
theorem B5395295 : Blo 1684042 5395295 := bstep (se 1 (by rfl) ⟨4046471, by rfl⟩ : syracuseStep 5395295 = 8092943) B8092943
theorem B1684319 : Blo 1684042 1684319 := bstep (se 1 (by rfl) ⟨1263239, by rfl⟩ : syracuseStep 1684319 = 2526479) B2526479
theorem B2528105 : Blo 1684042 2528105 := bstep (se 2 (by rfl) ⟨948039, by rfl⟩ : syracuseStep 2528105 = 1896079) B1896079
theorem B1684347 : Blo 1684042 1684347 := bstep (se 1 (by rfl) ⟨1263260, by rfl⟩ : syracuseStep 1684347 = 2526521) B2526521
theorem B1684399 : Blo 1684042 1684399 := bstep (se 1 (by rfl) ⟨1263299, by rfl⟩ : syracuseStep 1684399 = 2526599) B2526599
theorem B7197623 : Blo 1684042 7197623 := bstep (se 1 (by rfl) ⟨5398217, by rfl⟩ : syracuseStep 7197623 = 10796435) B10796435
theorem B2528183 : Blo 1684042 2528183 := bstep (se 1 (by rfl) ⟨1896137, by rfl⟩ : syracuseStep 2528183 = 3792275) B3792275
theorem B3789755 : Blo 1684042 3789755 := bstep (se 1 (by rfl) ⟨2842316, by rfl⟩ : syracuseStep 3789755 = 5684633) B5684633
theorem B1684423 : Blo 1684042 1684423 := bstep (se 1 (by rfl) ⟨1263317, by rfl⟩ : syracuseStep 1684423 = 2526635) B2526635
theorem B1684443 : Blo 1684042 1684443 := bstep (se 1 (by rfl) ⟨1263332, by rfl⟩ : syracuseStep 1684443 = 2526665) B2526665
theorem B2528219 : Blo 1684042 2528219 := bstep (se 1 (by rfl) ⟨1896164, by rfl⟩ : syracuseStep 2528219 = 3792329) B3792329
theorem B6394895 : Blo 1684042 6394895 := bstep (se 1 (by rfl) ⟨4796171, by rfl⟩ : syracuseStep 6394895 = 9592343) B9592343
theorem B1684519 : Blo 1684042 1684519 := bstep (se 1 (by rfl) ⟨1263389, by rfl⟩ : syracuseStep 1684519 = 2526779) B2526779
theorem B3789881 : Blo 1684042 3789881 := bstep (se 2 (by rfl) ⟨1421205, by rfl⟩ : syracuseStep 3789881 = 2842411) B2842411
theorem B1684559 : Blo 1684042 1684559 := bstep (se 1 (by rfl) ⟨1263419, by rfl⟩ : syracuseStep 1684559 = 2526839) B2526839
theorem B1684575 : Blo 1684042 1684575 := bstep (se 1 (by rfl) ⟨1263431, by rfl⟩ : syracuseStep 1684575 = 2526863) B2526863
theorem B1684603 : Blo 1684042 1684603 := bstep (se 1 (by rfl) ⟨1263452, by rfl⟩ : syracuseStep 1684603 = 2526905) B2526905
theorem B1684655 : Blo 1684042 1684655 := bstep (se 1 (by rfl) ⟨1263491, by rfl⟩ : syracuseStep 1684655 = 2526983) B2526983
theorem B8533187 : Blo 1684042 8533187 := bstep (se 1 (by rfl) ⟨6399890, by rfl⟩ : syracuseStep 8533187 = 12799781) B12799781
theorem B1684679 : Blo 1684042 1684679 := bstep (se 1 (by rfl) ⟨1263509, by rfl⟩ : syracuseStep 1684679 = 2527019) B2527019
theorem B1684699 : Blo 1684042 1684699 := bstep (se 1 (by rfl) ⟨1263524, by rfl⟩ : syracuseStep 1684699 = 2527049) B2527049
theorem B4265207 : Blo 1684042 4265207 := bstep (se 1 (by rfl) ⟨3198905, by rfl⟩ : syracuseStep 4265207 = 6397811) B6397811
theorem B3200249 : Blo 1684042 3200249 := bstep (se 2 (by rfl) ⟨1200093, by rfl⟩ : syracuseStep 3200249 = 2400187) B2400187
theorem B1684775 : Blo 1684042 1684775 := bstep (se 1 (by rfl) ⟨1263581, by rfl⟩ : syracuseStep 1684775 = 2527163) B2527163
theorem B1684815 : Blo 1684042 1684815 := bstep (se 1 (by rfl) ⟨1263611, by rfl⟩ : syracuseStep 1684815 = 2527223) B2527223
theorem B1684831 : Blo 1684042 1684831 := bstep (se 1 (by rfl) ⟨1263623, by rfl⟩ : syracuseStep 1684831 = 2527247) B2527247
theorem B1684859 : Blo 1684042 1684859 := bstep (se 1 (by rfl) ⟨1263644, by rfl⟩ : syracuseStep 1684859 = 2527289) B2527289
theorem B147789191 : Blo 1684042 147789191 := bstep (se 1 (by rfl) ⟨110841893, by rfl⟩ : syracuseStep 147789191 = 221683787) B221683787
theorem B3790223 : Blo 1684042 3790223 := bstep (se 1 (by rfl) ⟨2842667, by rfl⟩ : syracuseStep 3790223 = 5685335) B5685335
theorem B1684911 : Blo 1684042 1684911 := bstep (se 1 (by rfl) ⟨1263683, by rfl⟩ : syracuseStep 1684911 = 2527367) B2527367
theorem B2528687 : Blo 1684042 2528687 := bstep (se 1 (by rfl) ⟨1896515, by rfl⟩ : syracuseStep 2528687 = 3793031) B3793031
theorem B3036599 : Blo 1684042 3036599 := bstep (se 1 (by rfl) ⟨2277449, by rfl⟩ : syracuseStep 3036599 = 4554899) B4554899
theorem B1684935 : Blo 1684042 1684935 := bstep (se 1 (by rfl) ⟨1263701, by rfl⟩ : syracuseStep 1684935 = 2527403) B2527403
theorem B49903057 : Blo 1684042 49903057 := bstep (se 2 (by rfl) ⟨18713646, by rfl⟩ : syracuseStep 49903057 = 37427293) B37427293
theorem B1684955 : Blo 1684042 1684955 := bstep (se 1 (by rfl) ⟨1263716, by rfl⟩ : syracuseStep 1684955 = 2527433) B2527433
theorem B2528777 : Blo 1684042 2528777 := bstep (se 2 (by rfl) ⟨948291, by rfl⟩ : syracuseStep 2528777 = 1896583) B1896583
theorem B1685031 : Blo 1684042 1685031 := bstep (se 1 (by rfl) ⟨1263773, by rfl⟩ : syracuseStep 1685031 = 2527547) B2527547
theorem B2528807 : Blo 1684042 2528807 := bstep (se 1 (by rfl) ⟨1896605, by rfl⟩ : syracuseStep 2528807 = 3793211) B3793211
theorem B24294973 : Blo 1684042 24294973 := bstep (se 3 (by rfl) ⟨4555307, by rfl⟩ : syracuseStep 24294973 = 9110615) B9110615
theorem B1685071 : Blo 1684042 1685071 := bstep (se 1 (by rfl) ⟨1263803, by rfl⟩ : syracuseStep 1685071 = 2527607) B2527607
theorem B1685087 : Blo 1684042 1685087 := bstep (se 1 (by rfl) ⟨1263815, by rfl⟩ : syracuseStep 1685087 = 2527631) B2527631
theorem B1685115 : Blo 1684042 1685115 := bstep (se 1 (by rfl) ⟨1263836, by rfl⟩ : syracuseStep 1685115 = 2527673) B2527673
theorem B2528891 : Blo 1684042 2528891 := bstep (se 1 (by rfl) ⟨1896668, by rfl⟩ : syracuseStep 2528891 = 3793337) B3793337
theorem B1685167 : Blo 1684042 1685167 := bstep (se 1 (by rfl) ⟨1263875, by rfl⟩ : syracuseStep 1685167 = 2527751) B2527751
theorem B12801725 : Blo 1684042 12801725 := bstep (se 3 (by rfl) ⟨2400323, by rfl⟩ : syracuseStep 12801725 = 4800647) B4800647
theorem B1685191 : Blo 1684042 1685191 := bstep (se 1 (by rfl) ⟨1263893, by rfl⟩ : syracuseStep 1685191 = 2527787) B2527787
theorem B3790547 : Blo 1684042 3790547 := bstep (se 1 (by rfl) ⟨2842910, by rfl⟩ : syracuseStep 3790547 = 5685821) B5685821
theorem B1685211 : Blo 1684042 1685211 := bstep (se 1 (by rfl) ⟨1263908, by rfl⟩ : syracuseStep 1685211 = 2527817) B2527817
theorem B24278777 : Blo 1684042 24278777 := bstep (se 2 (by rfl) ⟨9104541, by rfl⟩ : syracuseStep 24278777 = 18209083) B18209083
theorem B2529017 : Blo 1684042 2529017 := bstep (se 2 (by rfl) ⟨948381, by rfl⟩ : syracuseStep 2529017 = 1896763) B1896763
theorem B1685287 : Blo 1684042 1685287 := bstep (se 1 (by rfl) ⟨1263965, by rfl⟩ : syracuseStep 1685287 = 2527931) B2527931
theorem B1685327 : Blo 1684042 1685327 := bstep (se 1 (by rfl) ⟨1263995, by rfl⟩ : syracuseStep 1685327 = 2527991) B2527991
theorem B1685343 : Blo 1684042 1685343 := bstep (se 1 (by rfl) ⟨1264007, by rfl⟩ : syracuseStep 1685343 = 2528015) B2528015
theorem B1685371 : Blo 1684042 1685371 := bstep (se 1 (by rfl) ⟨1264028, by rfl⟩ : syracuseStep 1685371 = 2528057) B2528057
theorem B4798369 : Blo 1684042 4798369 := bstep (se 2 (by rfl) ⟨1799388, by rfl⟩ : syracuseStep 4798369 = 3598777) B3598777
theorem B3037103 : Blo 1684042 3037103 := bstep (se 1 (by rfl) ⟨2277827, by rfl⟩ : syracuseStep 3037103 = 4555655) B4555655
theorem B1685423 : Blo 1684042 1685423 := bstep (se 1 (by rfl) ⟨1264067, by rfl⟩ : syracuseStep 1685423 = 2528135) B2528135
theorem B1685447 : Blo 1684042 1685447 := bstep (se 1 (by rfl) ⟨1264085, by rfl⟩ : syracuseStep 1685447 = 2528171) B2528171
theorem B1685467 : Blo 1684042 1685467 := bstep (se 1 (by rfl) ⟨1264100, by rfl⟩ : syracuseStep 1685467 = 2528201) B2528201
theorem B18208775 : Blo 1684042 18208775 := bstep (se 1 (by rfl) ⟨13656581, by rfl⟩ : syracuseStep 18208775 = 27313163) B27313163
theorem B1685543 : Blo 1684042 1685543 := bstep (se 1 (by rfl) ⟨1264157, by rfl⟩ : syracuseStep 1685543 = 2528315) B2528315
theorem B1685583 : Blo 1684042 1685583 := bstep (se 1 (by rfl) ⟨1264187, by rfl⟩ : syracuseStep 1685583 = 2528375) B2528375
theorem B1685599 : Blo 1684042 1685599 := bstep (se 1 (by rfl) ⟨1264199, by rfl⟩ : syracuseStep 1685599 = 2528399) B2528399
theorem B25950307 : Blo 1684042 25950307 := bstep (se 1 (by rfl) ⟨19462730, by rfl⟩ : syracuseStep 25950307 = 38925461) B38925461
theorem B1685627 : Blo 1684042 1685627 := bstep (se 1 (by rfl) ⟨1264220, by rfl⟩ : syracuseStep 1685627 = 2528441) B2528441
theorem B12802211 : Blo 1684042 12802211 := bstep (se 1 (by rfl) ⟨9601658, by rfl⟩ : syracuseStep 12802211 = 19203317) B19203317
theorem B1685679 : Blo 1684042 1685679 := bstep (se 1 (by rfl) ⟨1264259, by rfl⟩ : syracuseStep 1685679 = 2528519) B2528519
theorem B1685703 : Blo 1684042 1685703 := bstep (se 1 (by rfl) ⟨1264277, by rfl⟩ : syracuseStep 1685703 = 2528555) B2528555
theorem B1685723 : Blo 1684042 1685723 := bstep (se 1 (by rfl) ⟨1264292, by rfl⟩ : syracuseStep 1685723 = 2528585) B2528585
theorem B14391553 : Blo 1684042 14391553 := bstep (se 2 (by rfl) ⟨5396832, by rfl⟩ : syracuseStep 14391553 = 10793665) B10793665
theorem B1685799 : Blo 1684042 1685799 := bstep (se 1 (by rfl) ⟨1264349, by rfl⟩ : syracuseStep 1685799 = 2528699) B2528699
theorem B1685839 : Blo 1684042 1685839 := bstep (se 1 (by rfl) ⟨1264379, by rfl⟩ : syracuseStep 1685839 = 2528759) B2528759
theorem B1685855 : Blo 1684042 1685855 := bstep (se 1 (by rfl) ⟨1264391, by rfl⟩ : syracuseStep 1685855 = 2528783) B2528783
theorem B1685883 : Blo 1684042 1685883 := bstep (se 1 (by rfl) ⟨1264412, by rfl⟩ : syracuseStep 1685883 = 2528825) B2528825
theorem B36419975 : Blo 1684042 36419975 := bstep (se 1 (by rfl) ⟨27314981, by rfl⟩ : syracuseStep 36419975 = 54629963) B54629963
theorem B1685935 : Blo 1684042 1685935 := bstep (se 1 (by rfl) ⟨1264451, by rfl⟩ : syracuseStep 1685935 = 2528903) B2528903
theorem B1685959 : Blo 1684042 1685959 := bstep (se 1 (by rfl) ⟨1264469, by rfl⟩ : syracuseStep 1685959 = 2528939) B2528939
theorem B4798939 : Blo 1684042 4798939 := bstep (se 1 (by rfl) ⟨3599204, by rfl⟩ : syracuseStep 4798939 = 7198409) B7198409
theorem B1685979 : Blo 1684042 1685979 := bstep (se 1 (by rfl) ⟨1264484, by rfl⟩ : syracuseStep 1685979 = 2528969) B2528969
theorem B2398729 : Blo 1684042 2398729 := bstep (se 2 (by rfl) ⟨899523, by rfl⟩ : syracuseStep 2398729 = 1799047) B1799047
theorem B9108001 : Blo 1684042 9108001 := bstep (se 2 (by rfl) ⟨3415500, by rfl⟩ : syracuseStep 9108001 = 6831001) B6831001
theorem B6486625 : Blo 1684042 6486625 := bstep (se 2 (by rfl) ⟨2432484, by rfl⟩ : syracuseStep 6486625 = 4864969) B4864969
theorem B2398843 : Blo 1684042 2398843 := bstep (se 1 (by rfl) ⟨1799132, by rfl⟩ : syracuseStep 2398843 = 3598265) B3598265
theorem B3791483 : Blo 1684042 3791483 := bstep (se 1 (by rfl) ⟨2843612, by rfl⟩ : syracuseStep 3791483 = 5687225) B5687225
theorem B4266695 : Blo 1684042 4266695 := bstep (se 1 (by rfl) ⟨3200021, by rfl⟩ : syracuseStep 4266695 = 6400043) B6400043
theorem B8526545 : Blo 1684042 8526545 := bstep (se 2 (by rfl) ⟨3197454, by rfl⟩ : syracuseStep 8526545 = 6394909) B6394909
theorem B3791609 : Blo 1684042 3791609 := bstep (se 2 (by rfl) ⟨1421853, by rfl⟩ : syracuseStep 3791609 = 2843707) B2843707
theorem B54688601 : Blo 1684042 54688601 := bstep (se 2 (by rfl) ⟨20508225, by rfl⟩ : syracuseStep 54688601 = 41016451) B41016451
theorem B2399071 : Blo 1684042 2399071 := bstep (se 1 (by rfl) ⟨1799303, by rfl⟩ : syracuseStep 2399071 = 3598607) B3598607
theorem B3791879 : Blo 1684042 3791879 := bstep (se 1 (by rfl) ⟨2843909, by rfl⟩ : syracuseStep 3791879 = 5687819) B5687819
theorem B3791951 : Blo 1684042 3791951 := bstep (se 1 (by rfl) ⟨2843963, by rfl⟩ : syracuseStep 3791951 = 5687927) B5687927
theorem B4799645 : Blo 1684042 4799645 := bstep (se 3 (by rfl) ⟨899933, by rfl⟩ : syracuseStep 4799645 = 1799867) B1799867
theorem B5684471 : Blo 1684042 5684471 := bstep (se 1 (by rfl) ⟨4263353, by rfl⟩ : syracuseStep 5684471 = 8526707) B8526707
theorem B19193111 : Blo 1684042 19193111 := bstep (se 1 (by rfl) ⟨14394833, by rfl⟩ : syracuseStep 19193111 = 28789667) B28789667
theorem B4799873 : Blo 1684042 4799873 := bstep (se 2 (by rfl) ⟨1799952, by rfl⟩ : syracuseStep 4799873 = 3599905) B3599905
theorem B2399663 : Blo 1684042 2399663 := bstep (se 1 (by rfl) ⟨1799747, by rfl⟩ : syracuseStep 2399663 = 3599495) B3599495
theorem B5397961 : Blo 1684042 5397961 := bstep (se 2 (by rfl) ⟨2024235, by rfl⟩ : syracuseStep 5397961 = 4048471) B4048471
theorem B3841499 : Blo 1684042 3841499 := bstep (se 1 (by rfl) ⟨2881124, by rfl⟩ : syracuseStep 3841499 = 5762249) B5762249
theorem B3792347 : Blo 1684042 3792347 := bstep (se 1 (by rfl) ⟨2844260, by rfl⟩ : syracuseStep 3792347 = 5688521) B5688521
theorem B2842121 : Blo 1684042 2842121 := bstep (se 2 (by rfl) ⟨1065795, by rfl⟩ : syracuseStep 2842121 = 2131591) B2131591
theorem B5684795 : Blo 1684042 5684795 := bstep (se 1 (by rfl) ⟨4263596, by rfl⟩ : syracuseStep 5684795 = 8527193) B8527193
theorem B2842283 : Blo 1684042 2842283 := bstep (se 1 (by rfl) ⟨2131712, by rfl⟩ : syracuseStep 2842283 = 4263425) B4263425
theorem B4800215 : Blo 1684042 4800215 := bstep (se 1 (by rfl) ⟨3600161, by rfl⟩ : syracuseStep 4800215 = 7200323) B7200323
theorem B19201859 : Blo 1684042 19201859 := bstep (se 1 (by rfl) ⟨14401394, by rfl⟩ : syracuseStep 19201859 = 28802789) B28802789
theorem B5685065 : Blo 1684042 5685065 := bstep (se 2 (by rfl) ⟨2131899, by rfl⟩ : syracuseStep 5685065 = 4263799) B4263799
theorem B4800329 : Blo 1684042 4800329 := bstep (se 2 (by rfl) ⟨1800123, by rfl⟩ : syracuseStep 4800329 = 3600247) B3600247
theorem B4865953 : Blo 1684042 4865953 := bstep (se 2 (by rfl) ⟨1824732, by rfl⟩ : syracuseStep 4865953 = 3649465) B3649465
theorem B3792815 : Blo 1684042 3792815 := bstep (se 1 (by rfl) ⟨2844611, by rfl⟩ : syracuseStep 3792815 = 5689223) B5689223
theorem B3792905 : Blo 1684042 3792905 := bstep (se 2 (by rfl) ⟨1422339, by rfl⟩ : syracuseStep 3792905 = 2844679) B2844679
theorem B8101939 : Blo 1684042 8101939 := bstep (se 1 (by rfl) ⟨6076454, by rfl⟩ : syracuseStep 8101939 = 12152909) B12152909
theorem B2277481 : Blo 1684042 2277481 := bstep (se 2 (by rfl) ⟨854055, by rfl⟩ : syracuseStep 2277481 = 1708111) B1708111
theorem B8642713 : Blo 1684042 8642713 := bstep (se 2 (by rfl) ⟨3241017, by rfl⟩ : syracuseStep 8642713 = 6482035) B6482035
theorem B3793319 : Blo 1684042 3793319 := bstep (se 1 (by rfl) ⟨2844989, by rfl⟩ : syracuseStep 3793319 = 5689979) B5689979
theorem B3596719 : Blo 1684042 3596719 := bstep (se 1 (by rfl) ⟨2697539, by rfl⟩ : syracuseStep 3596719 = 5395079) B5395079
theorem B34595333 : Blo 1684042 34595333 := bstep (se 4 (by rfl) ⟨3243312, by rfl⟩ : syracuseStep 34595333 = 6486625) B6486625
theorem B3793427 : Blo 1684042 3793427 := bstep (se 1 (by rfl) ⟨2845070, by rfl⟩ : syracuseStep 3793427 = 5690141) B5690141
theorem B3793481 : Blo 1684042 3793481 := bstep (se 2 (by rfl) ⟨1422555, by rfl⟩ : syracuseStep 3793481 = 2845111) B2845111
theorem B6398585 : Blo 1684042 6398585 := bstep (se 2 (by rfl) ⟨2399469, by rfl⟩ : syracuseStep 6398585 = 4798939) B4798939
theorem B5685983 : Blo 1684042 5685983 := bstep (se 1 (by rfl) ⟨4264487, by rfl⟩ : syracuseStep 5685983 = 8528975) B8528975
theorem B7897823 : Blo 1684042 7897823 := bstep (se 1 (by rfl) ⟨5923367, by rfl⟩ : syracuseStep 7897823 = 11846735) B11846735
theorem B2843471 : Blo 1684042 2843471 := bstep (se 1 (by rfl) ⟨2132603, by rfl⟩ : syracuseStep 2843471 = 4265207) B4265207
theorem B98526127 : Blo 1684042 98526127 := bstep (se 1 (by rfl) ⟨73894595, by rfl⟩ : syracuseStep 98526127 = 147789191) B147789191
theorem B12796865 : Blo 1684042 12796865 := bstep (se 2 (by rfl) ⟨4798824, by rfl⟩ : syracuseStep 12796865 = 9597649) B9597649
theorem B2024399 : Blo 1684042 2024399 := bstep (se 1 (by rfl) ⟨1518299, by rfl⟩ : syracuseStep 2024399 = 3036599) B3036599
theorem B9602023 : Blo 1684042 9602023 := bstep (se 1 (by rfl) ⟨7201517, by rfl⟩ : syracuseStep 9602023 = 14403035) B14403035
theorem B6399101 : Blo 1684042 6399101 := bstep (se 3 (by rfl) ⟨1199831, by rfl⟩ : syracuseStep 6399101 = 2399663) B2399663
theorem B5686415 : Blo 1684042 5686415 := bstep (se 1 (by rfl) ⟨4264811, by rfl⟩ : syracuseStep 5686415 = 8529623) B8529623
theorem B2024735 : Blo 1684042 2024735 := bstep (se 1 (by rfl) ⟨1518551, by rfl⟩ : syracuseStep 2024735 = 3037103) B3037103
theorem B2844463 : Blo 1684042 2844463 := bstep (se 1 (by rfl) ⟨2133347, by rfl⟩ : syracuseStep 2844463 = 4266695) B4266695
theorem B13666153 : Blo 1684042 13666153 := bstep (se 2 (by rfl) ⟨5124807, by rfl⟩ : syracuseStep 13666153 = 10249615) B10249615
theorem B66537409 : Blo 1684042 66537409 := bstep (se 2 (by rfl) ⟨24951528, by rfl⟩ : syracuseStep 66537409 = 49903057) B49903057
theorem B32393297 : Blo 1684042 32393297 := bstep (se 2 (by rfl) ⟨12147486, by rfl⟩ : syracuseStep 32393297 = 24294973) B24294973
theorem B14387453 : Blo 1684042 14387453 := bstep (se 3 (by rfl) ⟨2697647, by rfl⟩ : syracuseStep 14387453 = 5395295) B5395295
theorem B5687549 : Blo 1684042 5687549 := bstep (se 3 (by rfl) ⟨1066415, by rfl⟩ : syracuseStep 5687549 = 2132831) B2132831
theorem B5400857 : Blo 1684042 5400857 := bstep (se 2 (by rfl) ⟨2025321, by rfl⟩ : syracuseStep 5400857 = 4050643) B4050643
theorem B1894747 : Blo 1684042 1894747 := bstep (se 1 (by rfl) ⟨1421060, by rfl⟩ : syracuseStep 1894747 = 2842121) B2842121
theorem B2132335 : Blo 1684042 2132335 := bstep (se 1 (by rfl) ⟨1599251, by rfl⟩ : syracuseStep 2132335 = 3198503) B3198503
theorem B1894855 : Blo 1684042 1894855 := bstep (se 1 (by rfl) ⟨1421141, by rfl⟩ : syracuseStep 1894855 = 2842283) B2842283
theorem B1895215 : Blo 1684042 1895215 := bstep (se 1 (by rfl) ⟨1421411, by rfl⟩ : syracuseStep 1895215 = 2842823) B2842823
theorem B2526107 : Blo 1684042 2526107 := bstep (se 1 (by rfl) ⟨1894580, by rfl⟩ : syracuseStep 2526107 = 3789161) B3789161
theorem B1895323 : Blo 1684042 1895323 := bstep (se 1 (by rfl) ⟨1421492, by rfl⟩ : syracuseStep 1895323 = 2842985) B2842985
theorem B4262827 : Blo 1684042 4262827 := bstep (se 1 (by rfl) ⟨3197120, by rfl⟩ : syracuseStep 4262827 = 6394241) B6394241
theorem B19188737 : Blo 1684042 19188737 := bstep (se 2 (by rfl) ⟨7195776, by rfl⟩ : syracuseStep 19188737 = 14391553) B14391553
theorem B5688359 : Blo 1684042 5688359 := bstep (se 1 (by rfl) ⟨4266269, by rfl⟩ : syracuseStep 5688359 = 8532539) B8532539
theorem B6401213 : Blo 1684042 6401213 := bstep (se 3 (by rfl) ⟨1200227, by rfl⟩ : syracuseStep 6401213 = 2400455) B2400455
theorem B4263131 : Blo 1684042 4263131 := bstep (se 1 (by rfl) ⟨3197348, by rfl⟩ : syracuseStep 4263131 = 6394697) B6394697
theorem B2133211 : Blo 1684042 2133211 := bstep (se 1 (by rfl) ⟨1599908, by rfl⟩ : syracuseStep 2133211 = 3199817) B3199817
theorem B9596191 : Blo 1684042 9596191 := bstep (se 1 (by rfl) ⟨7197143, by rfl⟩ : syracuseStep 9596191 = 14394287) B14394287
theorem B2526503 : Blo 1684042 2526503 := bstep (se 1 (by rfl) ⟨1894877, by rfl⟩ : syracuseStep 2526503 = 3789755) B3789755
theorem B1895719 : Blo 1684042 1895719 := bstep (se 1 (by rfl) ⟨1421789, by rfl⟩ : syracuseStep 1895719 = 2843579) B2843579
theorem B4263263 : Blo 1684042 4263263 := bstep (se 1 (by rfl) ⟨3197447, by rfl⟩ : syracuseStep 4263263 = 6394895) B6394895
theorem B3198305 : Blo 1684042 3198305 := bstep (se 2 (by rfl) ⟨1199364, by rfl⟩ : syracuseStep 3198305 = 2398729) B2398729
theorem B46132577 : Blo 1684042 46132577 := bstep (se 2 (by rfl) ⟨17299716, by rfl⟩ : syracuseStep 46132577 = 34599433) B34599433
theorem B1895791 : Blo 1684042 1895791 := bstep (se 1 (by rfl) ⟨1421843, by rfl⟩ : syracuseStep 1895791 = 2843687) B2843687
theorem B2526587 : Blo 1684042 2526587 := bstep (se 1 (by rfl) ⟨1894940, by rfl⟩ : syracuseStep 2526587 = 3789881) B3789881
theorem B12144001 : Blo 1684042 12144001 := bstep (se 2 (by rfl) ⟨4554000, by rfl⟩ : syracuseStep 12144001 = 9108001) B9108001
theorem B4615639 : Blo 1684042 4615639 := bstep (se 1 (by rfl) ⟨3461729, by rfl⟩ : syracuseStep 4615639 = 6923459) B6923459
theorem B5688791 : Blo 1684042 5688791 := bstep (se 1 (by rfl) ⟨4266593, by rfl⟩ : syracuseStep 5688791 = 8533187) B8533187
theorem B2526713 : Blo 1684042 2526713 := bstep (se 2 (by rfl) ⟨947517, by rfl⟩ : syracuseStep 2526713 = 1895035) B1895035
theorem B3198457 : Blo 1684042 3198457 := bstep (se 2 (by rfl) ⟨1199421, by rfl⟩ : syracuseStep 3198457 = 2398843) B2398843
theorem B1896007 : Blo 1684042 1896007 := bstep (se 1 (by rfl) ⟨1422005, by rfl⟩ : syracuseStep 1896007 = 2844011) B2844011
theorem B2526815 : Blo 1684042 2526815 := bstep (se 1 (by rfl) ⟨1895111, by rfl⟩ : syracuseStep 2526815 = 3790223) B3790223
theorem B6074119 : Blo 1684042 6074119 := bstep (se 1 (by rfl) ⟨4555589, by rfl⟩ : syracuseStep 6074119 = 9111179) B9111179
theorem B3198761 : Blo 1684042 3198761 := bstep (se 2 (by rfl) ⟨1199535, by rfl⟩ : syracuseStep 3198761 = 2399071) B2399071
theorem B2527031 : Blo 1684042 2527031 := bstep (se 1 (by rfl) ⟨1895273, by rfl⟩ : syracuseStep 2527031 = 3790547) B3790547
theorem B4263961 : Blo 1684042 4263961 := bstep (se 2 (by rfl) ⟨1598985, by rfl⟩ : syracuseStep 4263961 = 3197971) B3197971
theorem B10793027 : Blo 1684042 10793027 := bstep (se 1 (by rfl) ⟨8094770, by rfl⟩ : syracuseStep 10793027 = 16189541) B16189541
theorem B2527337 : Blo 1684042 2527337 := bstep (se 2 (by rfl) ⟨947751, by rfl⟩ : syracuseStep 2527337 = 1895503) B1895503
theorem B4264265 : Blo 1684042 4264265 := bstep (se 2 (by rfl) ⟨1599099, by rfl⟩ : syracuseStep 4264265 = 3198199) B3198199
theorem B2527655 : Blo 1684042 2527655 := bstep (se 1 (by rfl) ⟨1895741, by rfl⟩ : syracuseStep 2527655 = 3791483) B3791483
theorem B2527739 : Blo 1684042 2527739 := bstep (se 1 (by rfl) ⟨1895804, by rfl⟩ : syracuseStep 2527739 = 3791609) B3791609
theorem B36459067 : Blo 1684042 36459067 := bstep (se 1 (by rfl) ⟨27344300, by rfl⟩ : syracuseStep 36459067 = 54688601) B54688601
theorem B49230433 : Blo 1684042 49230433 := bstep (se 2 (by rfl) ⟨18461412, by rfl⟩ : syracuseStep 49230433 = 36922825) B36922825
theorem B7197281 : Blo 1684042 7197281 := bstep (se 2 (by rfl) ⟨2698980, by rfl⟩ : syracuseStep 7197281 = 5397961) B5397961
theorem B2527865 : Blo 1684042 2527865 := bstep (se 2 (by rfl) ⟨947949, by rfl⟩ : syracuseStep 2527865 = 1895899) B1895899
theorem B2699897 : Blo 1684042 2699897 := bstep (se 2 (by rfl) ⟨1012461, by rfl⟩ : syracuseStep 2699897 = 2024923) B2024923
theorem B14389913 : Blo 1684042 14389913 := bstep (se 2 (by rfl) ⟨5396217, by rfl⟩ : syracuseStep 14389913 = 10792435) B10792435
theorem B2527919 : Blo 1684042 2527919 := bstep (se 1 (by rfl) ⟨1895939, by rfl⟩ : syracuseStep 2527919 = 3791879) B3791879
theorem B1684191 : Blo 1684042 1684191 := bstep (se 1 (by rfl) ⟨1263143, by rfl⟩ : syracuseStep 1684191 = 2526287) B2526287
theorem B2527967 : Blo 1684042 2527967 := bstep (se 1 (by rfl) ⟨1895975, by rfl⟩ : syracuseStep 2527967 = 3791951) B3791951
theorem B3199763 : Blo 1684042 3199763 := bstep (se 1 (by rfl) ⟨2399822, by rfl⟩ : syracuseStep 3199763 = 4799645) B4799645
theorem B21893917 : Blo 1684042 21893917 := bstep (se 3 (by rfl) ⟨4105109, by rfl⟩ : syracuseStep 21893917 = 8210219) B8210219
theorem B1684271 : Blo 1684042 1684271 := bstep (se 1 (by rfl) ⟨1263203, by rfl⟩ : syracuseStep 1684271 = 2526407) B2526407
theorem B3789647 : Blo 1684042 3789647 := bstep (se 1 (by rfl) ⟨2842235, by rfl⟩ : syracuseStep 3789647 = 5684471) B5684471
theorem B5763919 : Blo 1684042 5763919 := bstep (se 1 (by rfl) ⟨4322939, by rfl⟩ : syracuseStep 5763919 = 8645879) B8645879
theorem B43766621 : Blo 1684042 43766621 := bstep (se 3 (by rfl) ⟨8206241, by rfl⟩ : syracuseStep 43766621 = 16412483) B16412483
theorem B1684379 : Blo 1684042 1684379 := bstep (se 1 (by rfl) ⟨1263284, by rfl⟩ : syracuseStep 1684379 = 2526569) B2526569
theorem B3199915 : Blo 1684042 3199915 := bstep (se 1 (by rfl) ⟨2399936, by rfl⟩ : syracuseStep 3199915 = 4799873) B4799873
theorem B1684431 : Blo 1684042 1684431 := bstep (se 1 (by rfl) ⟨1263323, by rfl⟩ : syracuseStep 1684431 = 2526647) B2526647
theorem B2560999 : Blo 1684042 2560999 := bstep (se 1 (by rfl) ⟨1920749, by rfl⟩ : syracuseStep 2560999 = 3841499) B3841499
theorem B1684455 : Blo 1684042 1684455 := bstep (se 1 (by rfl) ⟨1263341, by rfl⟩ : syracuseStep 1684455 = 2526683) B2526683
theorem B2528231 : Blo 1684042 2528231 := bstep (se 1 (by rfl) ⟨1896173, by rfl⟩ : syracuseStep 2528231 = 3792347) B3792347
theorem B3789863 : Blo 1684042 3789863 := bstep (se 1 (by rfl) ⟨2842397, by rfl⟩ : syracuseStep 3789863 = 5684795) B5684795
theorem B12792977 : Blo 1684042 12792977 := bstep (se 2 (by rfl) ⟨4797366, by rfl⟩ : syracuseStep 12792977 = 9594733) B9594733
theorem B3200143 : Blo 1684042 3200143 := bstep (se 1 (by rfl) ⟨2400107, by rfl⟩ : syracuseStep 3200143 = 4800215) B4800215
theorem B12801239 : Blo 1684042 12801239 := bstep (se 1 (by rfl) ⟨9600929, by rfl⟩ : syracuseStep 12801239 = 19201859) B19201859
theorem B3790043 : Blo 1684042 3790043 := bstep (se 1 (by rfl) ⟨2842532, by rfl⟩ : syracuseStep 3790043 = 5685065) B5685065
theorem B3200219 : Blo 1684042 3200219 := bstep (se 1 (by rfl) ⟨2400164, by rfl⟩ : syracuseStep 3200219 = 4800329) B4800329
theorem B2528489 : Blo 1684042 2528489 := bstep (se 2 (by rfl) ⟨948183, by rfl⟩ : syracuseStep 2528489 = 1896367) B1896367
theorem B1684767 : Blo 1684042 1684767 := bstep (se 1 (by rfl) ⟨1263575, by rfl⟩ : syracuseStep 1684767 = 2527151) B2527151
theorem B2528543 : Blo 1684042 2528543 := bstep (se 1 (by rfl) ⟨1896407, by rfl⟩ : syracuseStep 2528543 = 3792815) B3792815
theorem B1684827 : Blo 1684042 1684827 := bstep (se 1 (by rfl) ⟨1263620, by rfl⟩ : syracuseStep 1684827 = 2527241) B2527241
theorem B26285417 : Blo 1684042 26285417 := bstep (se 2 (by rfl) ⟨9857031, by rfl⟩ : syracuseStep 26285417 = 19714063) B19714063
theorem B1684847 : Blo 1684042 1684847 := bstep (se 1 (by rfl) ⟨1263635, by rfl⟩ : syracuseStep 1684847 = 2527271) B2527271
theorem B5395835 : Blo 1684042 5395835 := bstep (se 1 (by rfl) ⟨4046876, by rfl⟩ : syracuseStep 5395835 = 8093753) B8093753
theorem B3790241 : Blo 1684042 3790241 := bstep (se 2 (by rfl) ⟨1421340, by rfl⟩ : syracuseStep 3790241 = 2842681) B2842681
theorem B1684903 : Blo 1684042 1684903 := bstep (se 1 (by rfl) ⟨1263677, by rfl⟩ : syracuseStep 1684903 = 2527355) B2527355
theorem B2528711 : Blo 1684042 2528711 := bstep (se 1 (by rfl) ⟨1896533, by rfl⟩ : syracuseStep 2528711 = 3793067) B3793067
theorem B34600409 : Blo 1684042 34600409 := bstep (se 2 (by rfl) ⟨12975153, by rfl⟩ : syracuseStep 34600409 = 25950307) B25950307
theorem B1684987 : Blo 1684042 1684987 := bstep (se 1 (by rfl) ⟨1263740, by rfl⟩ : syracuseStep 1684987 = 2527481) B2527481
theorem B8533511 : Blo 1684042 8533511 := bstep (se 1 (by rfl) ⟨6400133, by rfl⟩ : syracuseStep 8533511 = 12800267) B12800267
theorem B8205857 : Blo 1684042 8205857 := bstep (se 2 (by rfl) ⟨3077196, by rfl⟩ : syracuseStep 8205857 = 6154393) B6154393
theorem B1685055 : Blo 1684042 1685055 := bstep (se 1 (by rfl) ⟨1263791, by rfl⟩ : syracuseStep 1685055 = 2527583) B2527583
theorem B1685063 : Blo 1684042 1685063 := bstep (se 1 (by rfl) ⟨1263797, by rfl⟩ : syracuseStep 1685063 = 2527595) B2527595
theorem B1685215 : Blo 1684042 1685215 := bstep (se 1 (by rfl) ⟨1263911, by rfl⟩ : syracuseStep 1685215 = 2527823) B2527823
theorem B1685295 : Blo 1684042 1685295 := bstep (se 1 (by rfl) ⟨1263971, by rfl⟩ : syracuseStep 1685295 = 2527943) B2527943
theorem B1685403 : Blo 1684042 1685403 := bstep (se 1 (by rfl) ⟨1264052, by rfl⟩ : syracuseStep 1685403 = 2528105) B2528105
theorem B3790799 : Blo 1684042 3790799 := bstep (se 1 (by rfl) ⟨2843099, by rfl⟩ : syracuseStep 3790799 = 5686199) B5686199
theorem B4798415 : Blo 1684042 4798415 := bstep (se 1 (by rfl) ⟨3598811, by rfl⟩ : syracuseStep 4798415 = 7197623) B7197623
theorem B1685455 : Blo 1684042 1685455 := bstep (se 1 (by rfl) ⟨1264091, by rfl⟩ : syracuseStep 1685455 = 2528183) B2528183
theorem B1685479 : Blo 1684042 1685479 := bstep (se 1 (by rfl) ⟨1264109, by rfl⟩ : syracuseStep 1685479 = 2528219) B2528219
theorem B8533997 : Blo 1684042 8533997 := bstep (se 3 (by rfl) ⟨1600124, by rfl⟩ : syracuseStep 8533997 = 3200249) B3200249
theorem B6076397 : Blo 1684042 6076397 := bstep (se 3 (by rfl) ⟨1139324, by rfl⟩ : syracuseStep 6076397 = 2278649) B2278649
theorem B3749897 : Blo 1684042 3749897 := bstep (se 2 (by rfl) ⟨1406211, by rfl⟩ : syracuseStep 3749897 = 2812423) B2812423
theorem B6396185 : Blo 1684042 6396185 := bstep (se 2 (by rfl) ⟨2398569, by rfl⟩ : syracuseStep 6396185 = 4797139) B4797139
theorem B1685791 : Blo 1684042 1685791 := bstep (se 1 (by rfl) ⟨1264343, by rfl⟩ : syracuseStep 1685791 = 2528687) B2528687
theorem B3791177 : Blo 1684042 3791177 := bstep (se 2 (by rfl) ⟨1421691, by rfl⟩ : syracuseStep 3791177 = 2843383) B2843383
theorem B3791195 : Blo 1684042 3791195 := bstep (se 1 (by rfl) ⟨2843396, by rfl⟩ : syracuseStep 3791195 = 5686793) B5686793
theorem B1685851 : Blo 1684042 1685851 := bstep (se 1 (by rfl) ⟨1264388, by rfl⟩ : syracuseStep 1685851 = 2528777) B2528777
theorem B1685871 : Blo 1684042 1685871 := bstep (se 1 (by rfl) ⟨1264403, by rfl⟩ : syracuseStep 1685871 = 2528807) B2528807
theorem B1685927 : Blo 1684042 1685927 := bstep (se 1 (by rfl) ⟨1264445, by rfl⟩ : syracuseStep 1685927 = 2528891) B2528891
theorem B8534483 : Blo 1684042 8534483 := bstep (se 1 (by rfl) ⟨6400862, by rfl⟩ : syracuseStep 8534483 = 12801725) B12801725
theorem B16407035 : Blo 1684042 16407035 := bstep (se 1 (by rfl) ⟨12305276, by rfl⟩ : syracuseStep 16407035 = 24610553) B24610553
theorem B16185851 : Blo 1684042 16185851 := bstep (se 1 (by rfl) ⟨12139388, by rfl⟩ : syracuseStep 16185851 = 24278777) B24278777
theorem B1686011 : Blo 1684042 1686011 := bstep (se 1 (by rfl) ⟨1264508, by rfl⟩ : syracuseStep 1686011 = 2529017) B2529017
theorem B12139183 : Blo 1684042 12139183 := bstep (se 1 (by rfl) ⟨9104387, by rfl⟩ : syracuseStep 12139183 = 18208775) B18208775
theorem B5397167 : Blo 1684042 5397167 := bstep (se 1 (by rfl) ⟨4047875, by rfl⟩ : syracuseStep 5397167 = 8095751) B8095751
theorem B103791365 : Blo 1684042 103791365 := bstep (se 4 (by rfl) ⟨9730440, by rfl⟩ : syracuseStep 103791365 = 19460881) B19460881
theorem B8534807 : Blo 1684042 8534807 := bstep (se 1 (by rfl) ⟨6401105, by rfl⟩ : syracuseStep 8534807 = 12802211) B12802211
theorem B41540471 : Blo 1684042 41540471 := bstep (se 1 (by rfl) ⟨31155353, by rfl⟩ : syracuseStep 41540471 = 62310707) B62310707
theorem B5684093 : Blo 1684042 5684093 := bstep (se 3 (by rfl) ⟨1065767, by rfl⟩ : syracuseStep 5684093 = 2131535) B2131535
theorem B3791771 : Blo 1684042 3791771 := bstep (se 1 (by rfl) ⟨2843828, by rfl⟩ : syracuseStep 3791771 = 5687657) B5687657
theorem B24279983 : Blo 1684042 24279983 := bstep (se 1 (by rfl) ⟨18209987, by rfl⟩ : syracuseStep 24279983 = 36419975) B36419975
theorem B3791969 : Blo 1684042 3791969 := bstep (se 2 (by rfl) ⟨1421988, by rfl⟩ : syracuseStep 3791969 = 2843977) B2843977
theorem B5684363 : Blo 1684042 5684363 := bstep (se 1 (by rfl) ⟨4263272, by rfl⟩ : syracuseStep 5684363 = 8526545) B8526545
theorem B4267151 : Blo 1684042 4267151 := bstep (se 1 (by rfl) ⟨3200363, by rfl⟩ : syracuseStep 4267151 = 6400727) B6400727
theorem B18717925 : Blo 1684042 18717925 := bstep (se 4 (by rfl) ⟨1754805, by rfl⟩ : syracuseStep 18717925 = 3509611) B3509611
theorem B3792167 : Blo 1684042 3792167 := bstep (se 1 (by rfl) ⟨2844125, by rfl⟩ : syracuseStep 3792167 = 5688251) B5688251
theorem B2841979 : Blo 1684042 2841979 := bstep (se 1 (by rfl) ⟨2131484, by rfl⟩ : syracuseStep 2841979 = 4262969) B4262969
theorem B18226595 : Blo 1684042 18226595 := bstep (se 1 (by rfl) ⟨13669946, by rfl⟩ : syracuseStep 18226595 = 27339893) B27339893
theorem B12795407 : Blo 1684042 12795407 := bstep (se 1 (by rfl) ⟨9596555, by rfl⟩ : syracuseStep 12795407 = 19193111) B19193111
theorem B3792545 : Blo 1684042 3792545 := bstep (se 2 (by rfl) ⟨1422204, by rfl⟩ : syracuseStep 3792545 = 2844409) B2844409
theorem B9723655 : Blo 1684042 9723655 := bstep (se 1 (by rfl) ⟨7292741, by rfl⟩ : syracuseStep 9723655 = 14585483) B14585483
theorem B6397825 : Blo 1684042 6397825 := bstep (se 2 (by rfl) ⟨2399184, by rfl⟩ : syracuseStep 6397825 = 4798369) B4798369
theorem B6487937 : Blo 1684042 6487937 := bstep (se 2 (by rfl) ⟨2432976, by rfl⟩ : syracuseStep 6487937 = 4865953) B4865953
theorem B5685281 : Blo 1684042 5685281 := bstep (se 2 (by rfl) ⟨2131980, by rfl⟩ : syracuseStep 5685281 = 4263961) B4263961
theorem B2842843 : Blo 1684042 2842843 := bstep (se 1 (by rfl) ⟨2132132, by rfl⟩ : syracuseStep 2842843 = 4264265) B4264265
theorem B9593275 : Blo 1684042 9593275 := bstep (se 1 (by rfl) ⟨7194956, by rfl⟩ : syracuseStep 9593275 = 14389913) B14389913
theorem B2843113 : Blo 1684042 2843113 := bstep (se 2 (by rfl) ⟨1066167, by rfl⟩ : syracuseStep 2843113 = 2132335) B2132335
theorem B14402285 : Blo 1684042 14402285 := bstep (se 3 (by rfl) ⟨2700428, by rfl⟩ : syracuseStep 14402285 = 5400857) B5400857
theorem B48612089 : Blo 1684042 48612089 := bstep (se 2 (by rfl) ⟨18229533, by rfl⟩ : syracuseStep 48612089 = 36459067) B36459067
theorem B5399293 : Blo 1684042 5399293 := bstep (se 3 (by rfl) ⟨1012367, by rfl⟩ : syracuseStep 5399293 = 2024735) B2024735
theorem B8528651 : Blo 1684042 8528651 := bstep (se 1 (by rfl) ⟨6396488, by rfl⟩ : syracuseStep 8528651 = 12792977) B12792977
theorem B17523611 : Blo 1684042 17523611 := bstep (se 1 (by rfl) ⟨13142708, by rfl⟩ : syracuseStep 17523611 = 26285417) B26285417
theorem B3597223 : Blo 1684042 3597223 := bstep (se 1 (by rfl) ⟨2697917, by rfl⟩ : syracuseStep 3597223 = 5395835) B5395835
theorem B8528813 : Blo 1684042 8528813 := bstep (se 3 (by rfl) ⟨1599152, by rfl⟩ : syracuseStep 8528813 = 3198305) B3198305
theorem B7685225 : Blo 1684042 7685225 := bstep (se 2 (by rfl) ⟨2881959, by rfl⟩ : syracuseStep 7685225 = 5763919) B5763919
theorem B131368169 : Blo 1684042 131368169 := bstep (se 2 (by rfl) ⟨49263063, by rfl⟩ : syracuseStep 131368169 = 98526127) B98526127
theorem B2499931 : Blo 1684042 2499931 := bstep (se 1 (by rfl) ⟨1874948, by rfl⟩ : syracuseStep 2499931 = 3749897) B3749897
theorem B21595531 : Blo 1684042 21595531 := bstep (se 1 (by rfl) ⟨16196648, by rfl⟩ : syracuseStep 21595531 = 32393297) B32393297
theorem B2844281 : Blo 1684042 2844281 := bstep (se 2 (by rfl) ⟨1066605, by rfl⟩ : syracuseStep 2844281 = 2133211) B2133211
theorem B10790567 : Blo 1684042 10790567 := bstep (se 1 (by rfl) ⟨8092925, by rfl⟩ : syracuseStep 10790567 = 16185851) B16185851
theorem B10938023 : Blo 1684042 10938023 := bstep (se 1 (by rfl) ⟨8203517, by rfl⟩ : syracuseStep 10938023 = 16407035) B16407035
theorem B3598111 : Blo 1684042 3598111 := bstep (se 1 (by rfl) ⟨2698583, by rfl⟩ : syracuseStep 3598111 = 5397167) B5397167
theorem B2844767 : Blo 1684042 2844767 := bstep (se 1 (by rfl) ⟨2133575, by rfl⟩ : syracuseStep 2844767 = 4267151) B4267151
theorem B30755051 : Blo 1684042 30755051 := bstep (se 1 (by rfl) ⟨23066288, by rfl⟩ : syracuseStep 30755051 = 46132577) B46132577
theorem B12151063 : Blo 1684042 12151063 := bstep (se 1 (by rfl) ⟨9113297, by rfl⟩ : syracuseStep 12151063 = 18226595) B18226595
theorem B8530271 : Blo 1684042 8530271 := bstep (se 1 (by rfl) ⟨6397703, by rfl⟩ : syracuseStep 8530271 = 12795407) B12795407
theorem B18221537 : Blo 1684042 18221537 := bstep (se 2 (by rfl) ⟨6833076, by rfl⟩ : syracuseStep 18221537 = 13666153) B13666153
theorem B8530433 : Blo 1684042 8530433 := bstep (se 2 (by rfl) ⟨3198912, by rfl⟩ : syracuseStep 8530433 = 6397825) B6397825
theorem B2132507 : Blo 1684042 2132507 := bstep (se 1 (by rfl) ⟨1599380, by rfl⟩ : syracuseStep 2132507 = 3198761) B3198761
theorem B7195351 : Blo 1684042 7195351 := bstep (se 1 (by rfl) ⟨5396513, by rfl⟩ : syracuseStep 7195351 = 10793027) B10793027
theorem B23063555 : Blo 1684042 23063555 := bstep (se 1 (by rfl) ⟨17297666, by rfl⟩ : syracuseStep 23063555 = 34595333) B34595333
theorem B2526329 : Blo 1684042 2526329 := bstep (se 2 (by rfl) ⟨947373, by rfl⟩ : syracuseStep 2526329 = 1894747) B1894747
theorem B2526431 : Blo 1684042 2526431 := bstep (se 1 (by rfl) ⟨1894823, by rfl⟩ : syracuseStep 2526431 = 3789647) B3789647
theorem B1895647 : Blo 1684042 1895647 := bstep (se 1 (by rfl) ⟨1421735, by rfl⟩ : syracuseStep 1895647 = 2843471) B2843471
theorem B4795625 : Blo 1684042 4795625 := bstep (se 2 (by rfl) ⟨1798359, by rfl⟩ : syracuseStep 4795625 = 3596719) B3596719
theorem B2526473 : Blo 1684042 2526473 := bstep (se 2 (by rfl) ⟨947427, by rfl⟩ : syracuseStep 2526473 = 1894855) B1894855
theorem B8531243 : Blo 1684042 8531243 := bstep (se 1 (by rfl) ⟨6398432, by rfl⟩ : syracuseStep 8531243 = 12796865) B12796865
theorem B2526575 : Blo 1684042 2526575 := bstep (se 1 (by rfl) ⟨1894931, by rfl⟩ : syracuseStep 2526575 = 3789863) B3789863
theorem B2526695 : Blo 1684042 2526695 := bstep (se 1 (by rfl) ⟨1895021, by rfl⟩ : syracuseStep 2526695 = 3790043) B3790043
theorem B2133479 : Blo 1684042 2133479 := bstep (se 1 (by rfl) ⟨1600109, by rfl⟩ : syracuseStep 2133479 = 3200219) B3200219
theorem B2526827 : Blo 1684042 2526827 := bstep (se 1 (by rfl) ⟨1895120, by rfl⟩ : syracuseStep 2526827 = 3790241) B3790241
theorem B5689007 : Blo 1684042 5689007 := bstep (se 1 (by rfl) ⟨4266755, by rfl⟩ : syracuseStep 5689007 = 8533511) B8533511
theorem B29191889 : Blo 1684042 29191889 := bstep (se 2 (by rfl) ⟨10946958, by rfl⟩ : syracuseStep 29191889 = 21893917) B21893917
theorem B2526953 : Blo 1684042 2526953 := bstep (se 2 (by rfl) ⟨947607, by rfl⟩ : syracuseStep 2526953 = 1895215) B1895215
theorem B2527097 : Blo 1684042 2527097 := bstep (se 2 (by rfl) ⟨947661, by rfl⟩ : syracuseStep 2527097 = 1895323) B1895323
theorem B2527199 : Blo 1684042 2527199 := bstep (se 1 (by rfl) ⟨1895399, by rfl⟩ : syracuseStep 2527199 = 3790799) B3790799
theorem B3198943 : Blo 1684042 3198943 := bstep (se 1 (by rfl) ⟨2399207, by rfl⟩ : syracuseStep 3198943 = 4798415) B4798415
theorem B5689331 : Blo 1684042 5689331 := bstep (se 1 (by rfl) ⟨4266998, by rfl⟩ : syracuseStep 5689331 = 8533997) B8533997
theorem B32395301 : Blo 1684042 32395301 := bstep (se 4 (by rfl) ⟨3037059, by rfl⟩ : syracuseStep 32395301 = 6074119) B6074119
theorem B4264123 : Blo 1684042 4264123 := bstep (se 1 (by rfl) ⟨3198092, by rfl⟩ : syracuseStep 4264123 = 6396185) B6396185
theorem B2527451 : Blo 1684042 2527451 := bstep (se 1 (by rfl) ⟨1895588, by rfl⟩ : syracuseStep 2527451 = 3791177) B3791177
theorem B2527463 : Blo 1684042 2527463 := bstep (se 1 (by rfl) ⟨1895597, by rfl⟩ : syracuseStep 2527463 = 3791195) B3791195
theorem B24957233 : Blo 1684042 24957233 := bstep (se 2 (by rfl) ⟨9358962, by rfl⟩ : syracuseStep 24957233 = 18717925) B18717925
theorem B5689655 : Blo 1684042 5689655 := bstep (se 1 (by rfl) ⟨4267241, by rfl⟩ : syracuseStep 5689655 = 8534483) B8534483
theorem B2527625 : Blo 1684042 2527625 := bstep (se 2 (by rfl) ⟨947859, by rfl⟩ : syracuseStep 2527625 = 1895719) B1895719
theorem B2527721 : Blo 1684042 2527721 := bstep (se 2 (by rfl) ⟨947895, by rfl⟩ : syracuseStep 2527721 = 1895791) B1895791
theorem B3789305 : Blo 1684042 3789305 := bstep (se 2 (by rfl) ⟨1420989, by rfl⟩ : syracuseStep 3789305 = 2841979) B2841979
theorem B16192001 : Blo 1684042 16192001 := bstep (se 2 (by rfl) ⟨6072000, by rfl⟩ : syracuseStep 16192001 = 12144001) B12144001
theorem B69194243 : Blo 1684042 69194243 := bstep (se 1 (by rfl) ⟨51895682, by rfl⟩ : syracuseStep 69194243 = 103791365) B103791365
theorem B5689871 : Blo 1684042 5689871 := bstep (se 1 (by rfl) ⟨4267403, by rfl⟩ : syracuseStep 5689871 = 8534807) B8534807
theorem B27693647 : Blo 1684042 27693647 := bstep (se 1 (by rfl) ⟨20770235, by rfl⟩ : syracuseStep 27693647 = 41540471) B41540471
theorem B3789395 : Blo 1684042 3789395 := bstep (se 1 (by rfl) ⟨2842046, by rfl⟩ : syracuseStep 3789395 = 5684093) B5684093
theorem B1684071 : Blo 1684042 1684071 := bstep (se 1 (by rfl) ⟨1263053, by rfl⟩ : syracuseStep 1684071 = 2526107) B2526107
theorem B2527847 : Blo 1684042 2527847 := bstep (se 1 (by rfl) ⟨1895885, by rfl⟩ : syracuseStep 2527847 = 3791771) B3791771
theorem B4264609 : Blo 1684042 4264609 := bstep (se 2 (by rfl) ⟨1599228, by rfl⟩ : syracuseStep 4264609 = 3198457) B3198457
theorem B12792491 : Blo 1684042 12792491 := bstep (se 1 (by rfl) ⟨9594368, by rfl⟩ : syracuseStep 12792491 = 19188737) B19188737
theorem B8532701 : Blo 1684042 8532701 := bstep (se 3 (by rfl) ⟨1599881, by rfl⟩ : syracuseStep 8532701 = 3199763) B3199763
theorem B2527979 : Blo 1684042 2527979 := bstep (se 1 (by rfl) ⟨1895984, by rfl⟩ : syracuseStep 2527979 = 3791969) B3791969
theorem B3789575 : Blo 1684042 3789575 := bstep (se 1 (by rfl) ⟨2842181, by rfl⟩ : syracuseStep 3789575 = 5684363) B5684363
theorem B2528009 : Blo 1684042 2528009 := bstep (se 2 (by rfl) ⟨948003, by rfl⟩ : syracuseStep 2528009 = 1896007) B1896007
theorem B1684335 : Blo 1684042 1684335 := bstep (se 1 (by rfl) ⟨1263251, by rfl⟩ : syracuseStep 1684335 = 2526503) B2526503
theorem B2528111 : Blo 1684042 2528111 := bstep (se 1 (by rfl) ⟨1896083, by rfl⟩ : syracuseStep 2528111 = 3792167) B3792167
theorem B1684391 : Blo 1684042 1684391 := bstep (se 1 (by rfl) ⟨1263293, by rfl⟩ : syracuseStep 1684391 = 2526587) B2526587
theorem B1684475 : Blo 1684042 1684475 := bstep (se 1 (by rfl) ⟨1263356, by rfl⟩ : syracuseStep 1684475 = 2526713) B2526713
theorem B12964873 : Blo 1684042 12964873 := bstep (se 2 (by rfl) ⟨4861827, by rfl⟩ : syracuseStep 12964873 = 9723655) B9723655
theorem B1684543 : Blo 1684042 1684543 := bstep (se 1 (by rfl) ⟨1263407, by rfl⟩ : syracuseStep 1684543 = 2526815) B2526815
theorem B2528363 : Blo 1684042 2528363 := bstep (se 1 (by rfl) ⟨1896272, by rfl⟩ : syracuseStep 2528363 = 3792545) B3792545
theorem B1684687 : Blo 1684042 1684687 := bstep (se 1 (by rfl) ⟨1263515, by rfl⟩ : syracuseStep 1684687 = 2527031) B2527031
theorem B88716545 : Blo 1684042 88716545 := bstep (se 2 (by rfl) ⟨33268704, by rfl⟩ : syracuseStep 88716545 = 66537409) B66537409
theorem B2528603 : Blo 1684042 2528603 := bstep (se 1 (by rfl) ⟨1896452, by rfl⟩ : syracuseStep 2528603 = 3792905) B3792905
theorem B10802585 : Blo 1684042 10802585 := bstep (se 2 (by rfl) ⟨4050969, by rfl⟩ : syracuseStep 10802585 = 8101939) B8101939
theorem B1684891 : Blo 1684042 1684891 := bstep (se 1 (by rfl) ⟨1263668, by rfl⟩ : syracuseStep 1684891 = 2527337) B2527337
theorem B3036641 : Blo 1684042 3036641 := bstep (se 2 (by rfl) ⟨1138740, by rfl⟩ : syracuseStep 3036641 = 2277481) B2277481
theorem B11523617 : Blo 1684042 11523617 := bstep (se 2 (by rfl) ⟨4321356, by rfl⟩ : syracuseStep 11523617 = 8642713) B8642713
theorem B1685103 : Blo 1684042 1685103 := bstep (se 1 (by rfl) ⟨1263827, by rfl⟩ : syracuseStep 1685103 = 2527655) B2527655
theorem B2528879 : Blo 1684042 2528879 := bstep (se 1 (by rfl) ⟨1896659, by rfl⟩ : syracuseStep 2528879 = 3793319) B3793319
theorem B1685159 : Blo 1684042 1685159 := bstep (se 1 (by rfl) ⟨1263869, by rfl⟩ : syracuseStep 1685159 = 2527739) B2527739
theorem B2528951 : Blo 1684042 2528951 := bstep (se 1 (by rfl) ⟨1896713, by rfl⟩ : syracuseStep 2528951 = 3793427) B3793427
theorem B2528987 : Blo 1684042 2528987 := bstep (se 1 (by rfl) ⟨1896740, by rfl⟩ : syracuseStep 2528987 = 3793481) B3793481
theorem B4798187 : Blo 1684042 4798187 := bstep (se 1 (by rfl) ⟨3598640, by rfl⟩ : syracuseStep 4798187 = 7197281) B7197281
theorem B4265723 : Blo 1684042 4265723 := bstep (se 1 (by rfl) ⟨3199292, by rfl⟩ : syracuseStep 4265723 = 6398585) B6398585
theorem B1685243 : Blo 1684042 1685243 := bstep (se 1 (by rfl) ⟨1263932, by rfl⟩ : syracuseStep 1685243 = 2527865) B2527865
theorem B1685279 : Blo 1684042 1685279 := bstep (se 1 (by rfl) ⟨1263959, by rfl⟩ : syracuseStep 1685279 = 2527919) B2527919
theorem B3790655 : Blo 1684042 3790655 := bstep (se 1 (by rfl) ⟨2842991, by rfl⟩ : syracuseStep 3790655 = 5685983) B5685983
theorem B5265215 : Blo 1684042 5265215 := bstep (se 1 (by rfl) ⟨3948911, by rfl⟩ : syracuseStep 5265215 = 7897823) B7897823
theorem B1685311 : Blo 1684042 1685311 := bstep (se 1 (by rfl) ⟨1263983, by rfl⟩ : syracuseStep 1685311 = 2527967) B2527967
theorem B29177747 : Blo 1684042 29177747 := bstep (se 1 (by rfl) ⟨21883310, by rfl⟩ : syracuseStep 29177747 = 43766621) B43766621
theorem B1685487 : Blo 1684042 1685487 := bstep (se 1 (by rfl) ⟨1264115, by rfl⟩ : syracuseStep 1685487 = 2528231) B2528231
theorem B4266067 : Blo 1684042 4266067 := bstep (se 1 (by rfl) ⟨3199550, by rfl⟩ : syracuseStep 4266067 = 6399101) B6399101
theorem B3790943 : Blo 1684042 3790943 := bstep (se 1 (by rfl) ⟨2843207, by rfl⟩ : syracuseStep 3790943 = 5686415) B5686415
theorem B65640577 : Blo 1684042 65640577 := bstep (se 2 (by rfl) ⟨24615216, by rfl⟩ : syracuseStep 65640577 = 49230433) B49230433
theorem B8534159 : Blo 1684042 8534159 := bstep (se 1 (by rfl) ⟨6400619, by rfl⟩ : syracuseStep 8534159 = 12801239) B12801239
theorem B1685659 : Blo 1684042 1685659 := bstep (se 1 (by rfl) ⟨1264244, by rfl⟩ : syracuseStep 1685659 = 2528489) B2528489
theorem B1685695 : Blo 1684042 1685695 := bstep (se 1 (by rfl) ⟨1264271, by rfl⟩ : syracuseStep 1685695 = 2528543) B2528543
theorem B16185577 : Blo 1684042 16185577 := bstep (se 2 (by rfl) ⟨6069591, by rfl⟩ : syracuseStep 16185577 = 12139183) B12139183
theorem B1685807 : Blo 1684042 1685807 := bstep (se 1 (by rfl) ⟨1264355, by rfl⟩ : syracuseStep 1685807 = 2528711) B2528711
theorem B23066939 : Blo 1684042 23066939 := bstep (se 1 (by rfl) ⟨17300204, by rfl⟩ : syracuseStep 23066939 = 34600409) B34600409
theorem B5470571 : Blo 1684042 5470571 := bstep (se 1 (by rfl) ⟨4102928, by rfl⟩ : syracuseStep 5470571 = 8205857) B8205857
theorem B5683769 : Blo 1684042 5683769 := bstep (se 2 (by rfl) ⟨2131413, by rfl⟩ : syracuseStep 5683769 = 4262827) B4262827
theorem B4266553 : Blo 1684042 4266553 := bstep (se 2 (by rfl) ⟨1599957, by rfl⟩ : syracuseStep 4266553 = 3199915) B3199915
theorem B3414665 : Blo 1684042 3414665 := bstep (se 2 (by rfl) ⟨1280499, by rfl⟩ : syracuseStep 3414665 = 2560999) B2560999
theorem B12802697 : Blo 1684042 12802697 := bstep (se 2 (by rfl) ⟨4801011, by rfl⟩ : syracuseStep 12802697 = 9602023) B9602023
theorem B9591635 : Blo 1684042 9591635 := bstep (se 1 (by rfl) ⟨7193726, by rfl⟩ : syracuseStep 9591635 = 14387453) B14387453
theorem B3791699 : Blo 1684042 3791699 := bstep (se 1 (by rfl) ⟨2843774, by rfl⟩ : syracuseStep 3791699 = 5687549) B5687549
theorem B4266857 : Blo 1684042 4266857 := bstep (se 2 (by rfl) ⟨1600071, by rfl⟩ : syracuseStep 4266857 = 3200143) B3200143
theorem B7199725 : Blo 1684042 7199725 := bstep (se 3 (by rfl) ⟨1349948, by rfl⟩ : syracuseStep 7199725 = 2699897) B2699897
theorem B12794921 : Blo 1684042 12794921 := bstep (se 2 (by rfl) ⟨4798095, by rfl⟩ : syracuseStep 12794921 = 9596191) B9596191
theorem B98466965 : Blo 1684042 98466965 := bstep (se 6 (by rfl) ⟨2307819, by rfl⟩ : syracuseStep 98466965 = 4615639) B4615639
theorem B16186655 : Blo 1684042 16186655 := bstep (se 1 (by rfl) ⟨12139991, by rfl⟩ : syracuseStep 16186655 = 24279983) B24279983
theorem B3792239 : Blo 1684042 3792239 := bstep (se 1 (by rfl) ⟨2844179, by rfl⟩ : syracuseStep 3792239 = 5688359) B5688359
theorem B4267475 : Blo 1684042 4267475 := bstep (se 1 (by rfl) ⟨3200606, by rfl⟩ : syracuseStep 4267475 = 6401213) B6401213
theorem B2842087 : Blo 1684042 2842087 := bstep (se 1 (by rfl) ⟨2131565, by rfl⟩ : syracuseStep 2842087 = 4263131) B4263131
theorem B2842175 : Blo 1684042 2842175 := bstep (se 1 (by rfl) ⟨2131631, by rfl⟩ : syracuseStep 2842175 = 4263263) B4263263
theorem B3792527 : Blo 1684042 3792527 := bstep (se 1 (by rfl) ⟨2844395, by rfl⟩ : syracuseStep 3792527 = 5688791) B5688791
theorem B3792617 : Blo 1684042 3792617 := bstep (se 2 (by rfl) ⟨1422231, by rfl⟩ : syracuseStep 3792617 = 2844463) B2844463
theorem B5398397 : Blo 1684042 5398397 := bstep (se 3 (by rfl) ⟨1012199, by rfl⟩ : syracuseStep 5398397 = 2024399) B2024399
theorem B4325291 : Blo 1684042 4325291 := bstep (se 1 (by rfl) ⟨3243968, by rfl⟩ : syracuseStep 4325291 = 6487937) B6487937
theorem B16203725 : Blo 1684042 16203725 := bstep (se 3 (by rfl) ⟨3038198, by rfl⟩ : syracuseStep 16203725 = 6076397) B6076397
theorem B16638155 : Blo 1684042 16638155 := bstep (se 1 (by rfl) ⟨12478616, by rfl⟩ : syracuseStep 16638155 = 24957233) B24957233
theorem B3793103 : Blo 1684042 3793103 := bstep (se 1 (by rfl) ⟨2844827, by rfl⟩ : syracuseStep 3793103 = 5689655) B5689655
theorem B5685497 : Blo 1684042 5685497 := bstep (se 2 (by rfl) ⟨2132061, by rfl⟩ : syracuseStep 5685497 = 4264123) B4264123
theorem B46129495 : Blo 1684042 46129495 := bstep (se 1 (by rfl) ⟨34597121, by rfl⟩ : syracuseStep 46129495 = 69194243) B69194243
theorem B3793247 : Blo 1684042 3793247 := bstep (se 1 (by rfl) ⟨2844935, by rfl⟩ : syracuseStep 3793247 = 5689871) B5689871
theorem B8528327 : Blo 1684042 8528327 := bstep (se 1 (by rfl) ⟨6396245, by rfl⟩ : syracuseStep 8528327 = 12792491) B12792491
theorem B9601523 : Blo 1684042 9601523 := bstep (se 1 (by rfl) ⟨7201142, by rfl⟩ : syracuseStep 9601523 = 14402285) B14402285
theorem B32408059 : Blo 1684042 32408059 := bstep (se 1 (by rfl) ⟨24306044, by rfl⟩ : syracuseStep 32408059 = 48612089) B48612089
theorem B5685767 : Blo 1684042 5685767 := bstep (se 1 (by rfl) ⟨4264325, by rfl⟩ : syracuseStep 5685767 = 8528651) B8528651
theorem B11682407 : Blo 1684042 11682407 := bstep (se 1 (by rfl) ⟨8761805, by rfl⟩ : syracuseStep 11682407 = 17523611) B17523611
theorem B350315117 : Blo 1684042 350315117 := bstep (se 3 (by rfl) ⟨65684084, by rfl⟩ : syracuseStep 350315117 = 131368169) B131368169
theorem B5685875 : Blo 1684042 5685875 := bstep (se 1 (by rfl) ⟨4264406, by rfl⟩ : syracuseStep 5685875 = 8528813) B8528813
theorem B5686145 : Blo 1684042 5686145 := bstep (se 2 (by rfl) ⟨2132304, by rfl⟩ : syracuseStep 5686145 = 4264609) B4264609
theorem B7201723 : Blo 1684042 7201723 := bstep (se 1 (by rfl) ⟨5401292, by rfl⟩ : syracuseStep 7201723 = 10802585) B10802585
theorem B9593801 : Blo 1684042 9593801 := bstep (se 2 (by rfl) ⟨3597675, by rfl⟩ : syracuseStep 9593801 = 7195351) B7195351
theorem B7193711 : Blo 1684042 7193711 := bstep (se 1 (by rfl) ⟨5395283, by rfl⟩ : syracuseStep 7193711 = 10790567) B10790567
theorem B7292015 : Blo 1684042 7292015 := bstep (se 1 (by rfl) ⟨5469011, by rfl⟩ : syracuseStep 7292015 = 10938023) B10938023
theorem B2843815 : Blo 1684042 2843815 := bstep (se 1 (by rfl) ⟨2132861, by rfl⟩ : syracuseStep 2843815 = 4265723) B4265723
theorem B17286497 : Blo 1684042 17286497 := bstep (se 2 (by rfl) ⟨6482436, by rfl⟩ : syracuseStep 17286497 = 12964873) B12964873
theorem B5686685 : Blo 1684042 5686685 := bstep (se 3 (by rfl) ⟨1066253, by rfl⟩ : syracuseStep 5686685 = 2132507) B2132507
theorem B15377959 : Blo 1684042 15377959 := bstep (se 1 (by rfl) ⟨11533469, by rfl⟩ : syracuseStep 15377959 = 23066939) B23066939
theorem B5686847 : Blo 1684042 5686847 := bstep (se 1 (by rfl) ⟨4265135, by rfl⟩ : syracuseStep 5686847 = 8530271) B8530271
theorem B3647047 : Blo 1684042 3647047 := bstep (se 1 (by rfl) ⟨2735285, by rfl⟩ : syracuseStep 3647047 = 5470571) B5470571
theorem B5686955 : Blo 1684042 5686955 := bstep (se 1 (by rfl) ⟨4265216, by rfl⟩ : syracuseStep 5686955 = 8530433) B8530433
theorem B2844571 : Blo 1684042 2844571 := bstep (se 1 (by rfl) ⟨2133428, by rfl⟩ : syracuseStep 2844571 = 4266857) B4266857
theorem B8529947 : Blo 1684042 8529947 := bstep (se 1 (by rfl) ⟨6397460, by rfl⟩ : syracuseStep 8529947 = 12794921) B12794921
theorem B65644643 : Blo 1684042 65644643 := bstep (se 1 (by rfl) ⟨49233482, by rfl⟩ : syracuseStep 65644643 = 98466965) B98466965
theorem B3197083 : Blo 1684042 3197083 := bstep (se 1 (by rfl) ⟨2397812, by rfl⟩ : syracuseStep 3197083 = 4795625) B4795625
theorem B10791103 : Blo 1684042 10791103 := bstep (se 1 (by rfl) ⟨8093327, by rfl⟩ : syracuseStep 10791103 = 16186655) B16186655
theorem B5687495 : Blo 1684042 5687495 := bstep (se 1 (by rfl) ⟨4265621, by rfl⟩ : syracuseStep 5687495 = 8531243) B8531243
theorem B2844983 : Blo 1684042 2844983 := bstep (se 1 (by rfl) ⟨2133737, by rfl⟩ : syracuseStep 2844983 = 4267475) B4267475
theorem B1894783 : Blo 1684042 1894783 := bstep (se 1 (by rfl) ⟨1421087, by rfl⟩ : syracuseStep 1894783 = 2842175) B2842175
theorem B3598931 : Blo 1684042 3598931 := bstep (se 1 (by rfl) ⟨2699198, by rfl⟩ : syracuseStep 3598931 = 5398397) B5398397
theorem B21596867 : Blo 1684042 21596867 := bstep (se 1 (by rfl) ⟨16197650, by rfl⟩ : syracuseStep 21596867 = 32395301) B32395301
theorem B5688089 : Blo 1684042 5688089 := bstep (se 2 (by rfl) ⟨2133033, by rfl⟩ : syracuseStep 5688089 = 4266067) B4266067
theorem B21580769 : Blo 1684042 21580769 := bstep (se 2 (by rfl) ⟨8092788, by rfl⟩ : syracuseStep 21580769 = 16185577) B16185577
theorem B2526203 : Blo 1684042 2526203 := bstep (se 1 (by rfl) ⟨1894652, by rfl⟩ : syracuseStep 2526203 = 3789305) B3789305
theorem B2526263 : Blo 1684042 2526263 := bstep (se 1 (by rfl) ⟨1894697, by rfl⟩ : syracuseStep 2526263 = 3789395) B3789395
theorem B5688467 : Blo 1684042 5688467 := bstep (se 1 (by rfl) ⟨4266350, by rfl⟩ : syracuseStep 5688467 = 8532701) B8532701
theorem B2526383 : Blo 1684042 2526383 := bstep (se 1 (by rfl) ⟨1894787, by rfl⟩ : syracuseStep 2526383 = 3789575) B3789575
theorem B12791033 : Blo 1684042 12791033 := bstep (se 2 (by rfl) ⟨4796637, by rfl⟩ : syracuseStep 12791033 = 9593275) B9593275
theorem B5123483 : Blo 1684042 5123483 := bstep (se 1 (by rfl) ⟨3842612, by rfl⟩ : syracuseStep 5123483 = 7685225) B7685225
theorem B5688737 : Blo 1684042 5688737 := bstep (se 2 (by rfl) ⟨2133276, by rfl⟩ : syracuseStep 5688737 = 4266553) B4266553
theorem B1896187 : Blo 1684042 1896187 := bstep (se 1 (by rfl) ⟨1422140, by rfl⟩ : syracuseStep 1896187 = 2844281) B2844281
theorem B3198791 : Blo 1684042 3198791 := bstep (se 1 (by rfl) ⟨2399093, by rfl⟩ : syracuseStep 3198791 = 4798187) B4798187
theorem B2527103 : Blo 1684042 2527103 := bstep (se 1 (by rfl) ⟨1895327, by rfl⟩ : syracuseStep 2527103 = 3790655) B3790655
theorem B3510143 : Blo 1684042 3510143 := bstep (se 1 (by rfl) ⟨2632607, by rfl⟩ : syracuseStep 3510143 = 5265215) B5265215
theorem B4796297 : Blo 1684042 4796297 := bstep (se 2 (by rfl) ⟨1798611, by rfl⟩ : syracuseStep 4796297 = 3597223) B3597223
theorem B48590765 : Blo 1684042 48590765 := bstep (se 3 (by rfl) ⟨9110768, by rfl⟩ : syracuseStep 48590765 = 18221537) B18221537
theorem B19451831 : Blo 1684042 19451831 := bstep (se 1 (by rfl) ⟨14588873, by rfl⟩ : syracuseStep 19451831 = 29177747) B29177747
theorem B5689277 : Blo 1684042 5689277 := bstep (se 3 (by rfl) ⟨1066739, by rfl⟩ : syracuseStep 5689277 = 2133479) B2133479
theorem B2527295 : Blo 1684042 2527295 := bstep (se 1 (by rfl) ⟨1895471, by rfl⟩ : syracuseStep 2527295 = 3790943) B3790943
theorem B1896511 : Blo 1684042 1896511 := bstep (se 1 (by rfl) ⟨1422383, by rfl⟩ : syracuseStep 1896511 = 2844767) B2844767
theorem B5689439 : Blo 1684042 5689439 := bstep (se 1 (by rfl) ⟨4267079, by rfl⟩ : syracuseStep 5689439 = 8534159) B8534159
theorem B10802483 : Blo 1684042 10802483 := bstep (se 1 (by rfl) ⟨8101862, by rfl⟩ : syracuseStep 10802483 = 16203725) B16203725
theorem B2527529 : Blo 1684042 2527529 := bstep (se 2 (by rfl) ⟨947823, by rfl⟩ : syracuseStep 2527529 = 1895647) B1895647
theorem B3789179 : Blo 1684042 3789179 := bstep (se 1 (by rfl) ⟨2841884, by rfl⟩ : syracuseStep 3789179 = 5683769) B5683769
theorem B6394423 : Blo 1684042 6394423 := bstep (se 1 (by rfl) ⟨4795817, by rfl⟩ : syracuseStep 6394423 = 9591635) B9591635
theorem B2527799 : Blo 1684042 2527799 := bstep (se 1 (by rfl) ⟨1895849, by rfl⟩ : syracuseStep 2527799 = 3791699) B3791699
theorem B3789449 : Blo 1684042 3789449 := bstep (se 2 (by rfl) ⟨1421043, by rfl⟩ : syracuseStep 3789449 = 2842087) B2842087
theorem B1684219 : Blo 1684042 1684219 := bstep (se 1 (by rfl) ⟨1263164, by rfl⟩ : syracuseStep 1684219 = 2526329) B2526329
theorem B1684287 : Blo 1684042 1684287 := bstep (se 1 (by rfl) ⟨1263215, by rfl⟩ : syracuseStep 1684287 = 2526431) B2526431
theorem B1684315 : Blo 1684042 1684315 := bstep (se 1 (by rfl) ⟨1263236, by rfl⟩ : syracuseStep 1684315 = 2526473) B2526473
theorem B1684383 : Blo 1684042 1684383 := bstep (se 1 (by rfl) ⟨1263287, by rfl⟩ : syracuseStep 1684383 = 2526575) B2526575
theorem B2528159 : Blo 1684042 2528159 := bstep (se 1 (by rfl) ⟨1896119, by rfl⟩ : syracuseStep 2528159 = 3792239) B3792239
theorem B1684463 : Blo 1684042 1684463 := bstep (se 1 (by rfl) ⟨1263347, by rfl⟩ : syracuseStep 1684463 = 2526695) B2526695
theorem B4797481 : Blo 1684042 4797481 := bstep (se 2 (by rfl) ⟨1799055, by rfl⟩ : syracuseStep 4797481 = 3598111) B3598111
theorem B1684551 : Blo 1684042 1684551 := bstep (se 1 (by rfl) ⟨1263413, by rfl⟩ : syracuseStep 1684551 = 2526827) B2526827
theorem B2528351 : Blo 1684042 2528351 := bstep (se 1 (by rfl) ⟨1896263, by rfl⟩ : syracuseStep 2528351 = 3792527) B3792527
theorem B19461259 : Blo 1684042 19461259 := bstep (se 1 (by rfl) ⟨14595944, by rfl⟩ : syracuseStep 19461259 = 29191889) B29191889
theorem B1684635 : Blo 1684042 1684635 := bstep (se 1 (by rfl) ⟨1263476, by rfl⟩ : syracuseStep 1684635 = 2526953) B2526953
theorem B2528411 : Blo 1684042 2528411 := bstep (se 1 (by rfl) ⟨1896308, by rfl⟩ : syracuseStep 2528411 = 3792617) B3792617
theorem B1684731 : Blo 1684042 1684731 := bstep (se 1 (by rfl) ⟨1263548, by rfl⟩ : syracuseStep 1684731 = 2527097) B2527097
theorem B4265257 : Blo 1684042 4265257 := bstep (se 2 (by rfl) ⟨1599471, by rfl⟩ : syracuseStep 4265257 = 3198943) B3198943
theorem B1684799 : Blo 1684042 1684799 := bstep (se 1 (by rfl) ⟨1263599, by rfl⟩ : syracuseStep 1684799 = 2527199) B2527199
theorem B61502813 : Blo 1684042 61502813 := bstep (se 3 (by rfl) ⟨11531777, by rfl⟩ : syracuseStep 61502813 = 23063555) B23063555
theorem B3790187 : Blo 1684042 3790187 := bstep (se 1 (by rfl) ⟨2842640, by rfl⟩ : syracuseStep 3790187 = 5685281) B5685281
theorem B1684967 : Blo 1684042 1684967 := bstep (se 1 (by rfl) ⟨1263725, by rfl⟩ : syracuseStep 1684967 = 2527451) B2527451
theorem B1684975 : Blo 1684042 1684975 := bstep (se 1 (by rfl) ⟨1263731, by rfl⟩ : syracuseStep 1684975 = 2527463) B2527463
theorem B87520769 : Blo 1684042 87520769 := bstep (se 2 (by rfl) ⟨32820288, by rfl⟩ : syracuseStep 87520769 = 65640577) B65640577
theorem B1685083 : Blo 1684042 1685083 := bstep (se 1 (by rfl) ⟨1263812, by rfl⟩ : syracuseStep 1685083 = 2527625) B2527625
theorem B3790457 : Blo 1684042 3790457 := bstep (se 2 (by rfl) ⟨1421421, by rfl⟩ : syracuseStep 3790457 = 2842843) B2842843
theorem B1685147 : Blo 1684042 1685147 := bstep (se 1 (by rfl) ⟨1263860, by rfl⟩ : syracuseStep 1685147 = 2527721) B2527721
theorem B10794667 : Blo 1684042 10794667 := bstep (se 1 (by rfl) ⟨8096000, by rfl⟩ : syracuseStep 10794667 = 16192001) B16192001
theorem B16201417 : Blo 1684042 16201417 := bstep (se 2 (by rfl) ⟨6075531, by rfl⟩ : syracuseStep 16201417 = 12151063) B12151063
theorem B18462431 : Blo 1684042 18462431 := bstep (se 1 (by rfl) ⟨13846823, by rfl⟩ : syracuseStep 18462431 = 27693647) B27693647
theorem B1685231 : Blo 1684042 1685231 := bstep (se 1 (by rfl) ⟨1263923, by rfl⟩ : syracuseStep 1685231 = 2527847) B2527847
theorem B1685319 : Blo 1684042 1685319 := bstep (se 1 (by rfl) ⟨1263989, by rfl⟩ : syracuseStep 1685319 = 2527979) B2527979
theorem B1685339 : Blo 1684042 1685339 := bstep (se 1 (by rfl) ⟨1264004, by rfl⟩ : syracuseStep 1685339 = 2528009) B2528009
theorem B1685407 : Blo 1684042 1685407 := bstep (se 1 (by rfl) ⟨1264055, by rfl⟩ : syracuseStep 1685407 = 2528111) B2528111
theorem B3790817 : Blo 1684042 3790817 := bstep (se 2 (by rfl) ⟨1421556, by rfl⟩ : syracuseStep 3790817 = 2843113) B2843113
theorem B1685575 : Blo 1684042 1685575 := bstep (se 1 (by rfl) ⟨1264181, by rfl⟩ : syracuseStep 1685575 = 2528363) B2528363
theorem B59144363 : Blo 1684042 59144363 := bstep (se 1 (by rfl) ⟨44358272, by rfl⟩ : syracuseStep 59144363 = 88716545) B88716545
theorem B1685735 : Blo 1684042 1685735 := bstep (se 1 (by rfl) ⟨1264301, by rfl⟩ : syracuseStep 1685735 = 2528603) B2528603
theorem B7199057 : Blo 1684042 7199057 := bstep (se 2 (by rfl) ⟨2699646, by rfl⟩ : syracuseStep 7199057 = 5399293) B5399293
theorem B7682411 : Blo 1684042 7682411 := bstep (se 1 (by rfl) ⟨5761808, by rfl⟩ : syracuseStep 7682411 = 11523617) B11523617
theorem B1685919 : Blo 1684042 1685919 := bstep (se 1 (by rfl) ⟨1264439, by rfl⟩ : syracuseStep 1685919 = 2528879) B2528879
theorem B1685967 : Blo 1684042 1685967 := bstep (se 1 (by rfl) ⟨1264475, by rfl⟩ : syracuseStep 1685967 = 2528951) B2528951
theorem B1685991 : Blo 1684042 1685991 := bstep (se 1 (by rfl) ⟨1264493, by rfl⟩ : syracuseStep 1685991 = 2528987) B2528987
theorem B9599633 : Blo 1684042 9599633 := bstep (se 2 (by rfl) ⟨3599862, by rfl⟩ : syracuseStep 9599633 = 7199725) B7199725
theorem B20503367 : Blo 1684042 20503367 := bstep (se 1 (by rfl) ⟨15377525, by rfl⟩ : syracuseStep 20503367 = 30755051) B30755051
theorem B2276443 : Blo 1684042 2276443 := bstep (se 1 (by rfl) ⟨1707332, by rfl⟩ : syracuseStep 2276443 = 3414665) B3414665
theorem B8535131 : Blo 1684042 8535131 := bstep (se 1 (by rfl) ⟨6401348, by rfl⟩ : syracuseStep 8535131 = 12802697) B12802697
theorem B3333241 : Blo 1684042 3333241 := bstep (se 2 (by rfl) ⟨1249965, by rfl⟩ : syracuseStep 3333241 = 2499931) B2499931
theorem B28794041 : Blo 1684042 28794041 := bstep (se 2 (by rfl) ⟨10797765, by rfl⟩ : syracuseStep 28794041 = 21595531) B21595531
theorem B32390837 : Blo 1684042 32390837 := bstep (se 5 (by rfl) ⟨1518320, by rfl⟩ : syracuseStep 32390837 = 3036641) B3036641
theorem B3792671 : Blo 1684042 3792671 := bstep (se 1 (by rfl) ⟨2844503, by rfl⟩ : syracuseStep 3792671 = 5689007) B5689007
theorem B2883527 : Blo 1684042 2883527 := bstep (se 1 (by rfl) ⟨2162645, by rfl⟩ : syracuseStep 2883527 = 4325291) B4325291
theorem B3792887 : Blo 1684042 3792887 := bstep (se 1 (by rfl) ⟨2844665, by rfl⟩ : syracuseStep 3792887 = 5689331) B5689331
theorem B3792959 : Blo 1684042 3792959 := bstep (se 1 (by rfl) ⟨2844719, by rfl⟩ : syracuseStep 3792959 = 5689439) B5689439
theorem B11092103 : Blo 1684042 11092103 := bstep (se 1 (by rfl) ⟨8319077, by rfl⟩ : syracuseStep 11092103 = 16638155) B16638155
theorem B5685551 : Blo 1684042 5685551 := bstep (se 1 (by rfl) ⟨4264163, by rfl⟩ : syracuseStep 5685551 = 8528327) B8528327
theorem B61505993 : Blo 1684042 61505993 := bstep (se 2 (by rfl) ⟨23064747, by rfl⟩ : syracuseStep 61505993 = 46129495) B46129495
theorem B12141029 : Blo 1684042 12141029 := bstep (se 4 (by rfl) ⟨1138221, by rfl⟩ : syracuseStep 12141029 = 2276443) B2276443
theorem B7201655 : Blo 1684042 7201655 := bstep (se 1 (by rfl) ⟨5401241, by rfl⟩ : syracuseStep 7201655 = 10802483) B10802483
theorem B41001875 : Blo 1684042 41001875 := bstep (se 1 (by rfl) ⟨30751406, by rfl⟩ : syracuseStep 41001875 = 61502813) B61502813
theorem B9602297 : Blo 1684042 9602297 := bstep (se 2 (by rfl) ⟨3600861, by rfl⟩ : syracuseStep 9602297 = 7201723) B7201723
theorem B5686631 : Blo 1684042 5686631 := bstep (se 1 (by rfl) ⟨4264973, by rfl⟩ : syracuseStep 5686631 = 8529947) B8529947
theorem B43763095 : Blo 1684042 43763095 := bstep (se 1 (by rfl) ⟨32822321, by rfl⟩ : syracuseStep 43763095 = 65644643) B65644643
theorem B39429575 : Blo 1684042 39429575 := bstep (se 1 (by rfl) ⟨29572181, by rfl⟩ : syracuseStep 39429575 = 59144363) B59144363
theorem B5687009 : Blo 1684042 5687009 := bstep (se 2 (by rfl) ⟨2132628, by rfl⟩ : syracuseStep 5687009 = 4265257) B4265257
theorem B6399755 : Blo 1684042 6399755 := bstep (se 1 (by rfl) ⟨4799816, by rfl⟩ : syracuseStep 6399755 = 9599633) B9599633
theorem B14387179 : Blo 1684042 14387179 := bstep (se 1 (by rfl) ⟨10790384, by rfl⟩ : syracuseStep 14387179 = 21580769) B21580769
theorem B19196027 : Blo 1684042 19196027 := bstep (se 1 (by rfl) ⟨14397020, by rfl⟩ : syracuseStep 19196027 = 28794041) B28794041
theorem B8530109 : Blo 1684042 8530109 := bstep (se 3 (by rfl) ⟨1599395, by rfl⟩ : syracuseStep 8530109 = 3198791) B3198791
theorem B3197531 : Blo 1684042 3197531 := bstep (se 1 (by rfl) ⟨2398148, by rfl⟩ : syracuseStep 3197531 = 4796297) B4796297
theorem B32393843 : Blo 1684042 32393843 := bstep (se 1 (by rfl) ⟨24295382, by rfl⟩ : syracuseStep 32393843 = 48590765) B48590765
theorem B4262777 : Blo 1684042 4262777 := bstep (se 2 (by rfl) ⟨1598541, by rfl⟩ : syracuseStep 4262777 = 3197083) B3197083
theorem B2526119 : Blo 1684042 2526119 := bstep (se 1 (by rfl) ⟨1894589, by rfl⟩ : syracuseStep 2526119 = 3789179) B3789179
theorem B14388137 : Blo 1684042 14388137 := bstep (se 2 (by rfl) ⟨5395551, by rfl⟩ : syracuseStep 14388137 = 10791103) B10791103
theorem B6401015 : Blo 1684042 6401015 := bstep (se 1 (by rfl) ⟨4800761, by rfl⟩ : syracuseStep 6401015 = 9601523) B9601523
theorem B2526299 : Blo 1684042 2526299 := bstep (se 1 (by rfl) ⟨1894724, by rfl⟩ : syracuseStep 2526299 = 3789449) B3789449
theorem B2526377 : Blo 1684042 2526377 := bstep (se 2 (by rfl) ⟨947391, by rfl⟩ : syracuseStep 2526377 = 1894783) B1894783
theorem B4795807 : Blo 1684042 4795807 := bstep (se 1 (by rfl) ⟨3596855, by rfl⟩ : syracuseStep 4795807 = 7193711) B7193711
theorem B4861343 : Blo 1684042 4861343 := bstep (se 1 (by rfl) ⟨3646007, by rfl⟩ : syracuseStep 4861343 = 7292015) B7292015
theorem B19197485 : Blo 1684042 19197485 := bstep (se 3 (by rfl) ⟨3599528, by rfl⟩ : syracuseStep 19197485 = 7199057) B7199057
theorem B2526791 : Blo 1684042 2526791 := bstep (se 1 (by rfl) ⟨1895093, by rfl⟩ : syracuseStep 2526791 = 3790187) B3790187
theorem B58347179 : Blo 1684042 58347179 := bstep (se 1 (by rfl) ⟨43760384, by rfl⟩ : syracuseStep 58347179 = 87520769) B87520769
theorem B2526971 : Blo 1684042 2526971 := bstep (se 1 (by rfl) ⟨1895228, by rfl⟩ : syracuseStep 2526971 = 3790457) B3790457
theorem B12308287 : Blo 1684042 12308287 := bstep (se 1 (by rfl) ⟨9231215, by rfl⟩ : syracuseStep 12308287 = 18462431) B18462431
theorem B2527211 : Blo 1684042 2527211 := bstep (se 1 (by rfl) ⟨1895408, by rfl⟩ : syracuseStep 2527211 = 3790817) B3790817
theorem B4444321 : Blo 1684042 4444321 := bstep (se 2 (by rfl) ⟨1666620, by rfl⟩ : syracuseStep 4444321 = 3333241) B3333241
theorem B25948345 : Blo 1684042 25948345 := bstep (se 2 (by rfl) ⟨9730629, by rfl⟩ : syracuseStep 25948345 = 19461259) B19461259
theorem B1896655 : Blo 1684042 1896655 := bstep (se 1 (by rfl) ⟨1422491, by rfl⟩ : syracuseStep 1896655 = 2844983) B2844983
theorem B9597149 : Blo 1684042 9597149 := bstep (se 3 (by rfl) ⟨1799465, by rfl⟩ : syracuseStep 9597149 = 3598931) B3598931
theorem B14397911 : Blo 1684042 14397911 := bstep (se 1 (by rfl) ⟨10798433, by rfl⟩ : syracuseStep 14397911 = 21596867) B21596867
theorem B13668911 : Blo 1684042 13668911 := bstep (se 1 (by rfl) ⟨10251683, by rfl⟩ : syracuseStep 13668911 = 20503367) B20503367
theorem B1684135 : Blo 1684042 1684135 := bstep (se 1 (by rfl) ⟨1263101, by rfl⟩ : syracuseStep 1684135 = 2526203) B2526203
theorem B1684175 : Blo 1684042 1684175 := bstep (se 1 (by rfl) ⟨1263131, by rfl⟩ : syracuseStep 1684175 = 2526263) B2526263
theorem B5690087 : Blo 1684042 5690087 := bstep (se 1 (by rfl) ⟨4267565, by rfl⟩ : syracuseStep 5690087 = 8535131) B8535131
theorem B4862729 : Blo 1684042 4862729 := bstep (se 2 (by rfl) ⟨1823523, by rfl⟩ : syracuseStep 4862729 = 3647047) B3647047
theorem B1684255 : Blo 1684042 1684255 := bstep (se 1 (by rfl) ⟨1263191, by rfl⟩ : syracuseStep 1684255 = 2526383) B2526383
theorem B2528249 : Blo 1684042 2528249 := bstep (se 2 (by rfl) ⟨948093, by rfl⟩ : syracuseStep 2528249 = 1896187) B1896187
theorem B2528447 : Blo 1684042 2528447 := bstep (se 1 (by rfl) ⟨1896335, by rfl⟩ : syracuseStep 2528447 = 3792671) B3792671
theorem B1684735 : Blo 1684042 1684735 := bstep (se 1 (by rfl) ⟨1263551, by rfl⟩ : syracuseStep 1684735 = 2527103) B2527103
theorem B2340095 : Blo 1684042 2340095 := bstep (se 1 (by rfl) ⟨1755071, by rfl⟩ : syracuseStep 2340095 = 3510143) B3510143
theorem B1922351 : Blo 1684042 1922351 := bstep (se 1 (by rfl) ⟨1441763, by rfl⟩ : syracuseStep 1922351 = 2883527) B2883527
theorem B2528591 : Blo 1684042 2528591 := bstep (se 1 (by rfl) ⟨1896443, by rfl⟩ : syracuseStep 2528591 = 3792887) B3792887
theorem B1684863 : Blo 1684042 1684863 := bstep (se 1 (by rfl) ⟨1263647, by rfl⟩ : syracuseStep 1684863 = 2527295) B2527295
theorem B2528681 : Blo 1684042 2528681 := bstep (se 2 (by rfl) ⟨948255, by rfl⟩ : syracuseStep 2528681 = 1896511) B1896511
theorem B2528735 : Blo 1684042 2528735 := bstep (se 1 (by rfl) ⟨1896551, by rfl⟩ : syracuseStep 2528735 = 3793103) B3793103
theorem B3790331 : Blo 1684042 3790331 := bstep (se 1 (by rfl) ⟨2842748, by rfl⟩ : syracuseStep 3790331 = 5685497) B5685497
theorem B1685019 : Blo 1684042 1685019 := bstep (se 1 (by rfl) ⟨1263764, by rfl⟩ : syracuseStep 1685019 = 2527529) B2527529
theorem B2528831 : Blo 1684042 2528831 := bstep (se 1 (by rfl) ⟨1896623, by rfl⟩ : syracuseStep 2528831 = 3793247) B3793247
theorem B3790511 : Blo 1684042 3790511 := bstep (se 1 (by rfl) ⟨2842883, by rfl⟩ : syracuseStep 3790511 = 5685767) B5685767
theorem B1685199 : Blo 1684042 1685199 := bstep (se 1 (by rfl) ⟨1263899, by rfl⟩ : syracuseStep 1685199 = 2527799) B2527799
theorem B233543411 : Blo 1684042 233543411 := bstep (se 1 (by rfl) ⟨175157558, by rfl⟩ : syracuseStep 233543411 = 350315117) B350315117
theorem B3790583 : Blo 1684042 3790583 := bstep (se 1 (by rfl) ⟨2842937, by rfl⟩ : syracuseStep 3790583 = 5685875) B5685875
theorem B3790763 : Blo 1684042 3790763 := bstep (se 1 (by rfl) ⟨2843072, by rfl⟩ : syracuseStep 3790763 = 5686145) B5686145
theorem B1685439 : Blo 1684042 1685439 := bstep (se 1 (by rfl) ⟨1264079, by rfl⟩ : syracuseStep 1685439 = 2528159) B2528159
theorem B6395867 : Blo 1684042 6395867 := bstep (se 1 (by rfl) ⟨4796900, by rfl⟩ : syracuseStep 6395867 = 9593801) B9593801
theorem B43210745 : Blo 1684042 43210745 := bstep (se 2 (by rfl) ⟨16204029, by rfl⟩ : syracuseStep 43210745 = 32408059) B32408059
theorem B1685567 : Blo 1684042 1685567 := bstep (se 1 (by rfl) ⟨1264175, by rfl⟩ : syracuseStep 1685567 = 2528351) B2528351
theorem B8525897 : Blo 1684042 8525897 := bstep (se 2 (by rfl) ⟨3197211, by rfl⟩ : syracuseStep 8525897 = 6394423) B6394423
theorem B1685607 : Blo 1684042 1685607 := bstep (se 1 (by rfl) ⟨1264205, by rfl⟩ : syracuseStep 1685607 = 2528411) B2528411
theorem B11524331 : Blo 1684042 11524331 := bstep (se 1 (by rfl) ⟨8643248, by rfl⟩ : syracuseStep 11524331 = 17286497) B17286497
theorem B3791123 : Blo 1684042 3791123 := bstep (se 1 (by rfl) ⟨2843342, by rfl⟩ : syracuseStep 3791123 = 5686685) B5686685
theorem B20486429 : Blo 1684042 20486429 := bstep (se 3 (by rfl) ⟨3841205, by rfl⟩ : syracuseStep 20486429 = 7682411) B7682411
theorem B3791231 : Blo 1684042 3791231 := bstep (se 1 (by rfl) ⟨2843423, by rfl⟩ : syracuseStep 3791231 = 5686847) B5686847
theorem B3791303 : Blo 1684042 3791303 := bstep (se 1 (by rfl) ⟨2843477, by rfl⟩ : syracuseStep 3791303 = 5686955) B5686955
theorem B6396641 : Blo 1684042 6396641 := bstep (se 2 (by rfl) ⟨2398740, by rfl⟩ : syracuseStep 6396641 = 4797481) B4797481
theorem B3791663 : Blo 1684042 3791663 := bstep (se 1 (by rfl) ⟨2843747, by rfl⟩ : syracuseStep 3791663 = 5687495) B5687495
theorem B3791753 : Blo 1684042 3791753 := bstep (se 2 (by rfl) ⟨1421907, by rfl⟩ : syracuseStep 3791753 = 2843815) B2843815
theorem B31153085 : Blo 1684042 31153085 := bstep (se 3 (by rfl) ⟨5841203, by rfl⟩ : syracuseStep 31153085 = 11682407) B11682407
theorem B3792059 : Blo 1684042 3792059 := bstep (se 1 (by rfl) ⟨2844044, by rfl⟩ : syracuseStep 3792059 = 5688089) B5688089
theorem B20503945 : Blo 1684042 20503945 := bstep (se 2 (by rfl) ⟨7688979, by rfl⟩ : syracuseStep 20503945 = 15377959) B15377959
theorem B3792311 : Blo 1684042 3792311 := bstep (se 1 (by rfl) ⟨2844233, by rfl⟩ : syracuseStep 3792311 = 5688467) B5688467
theorem B8527355 : Blo 1684042 8527355 := bstep (se 1 (by rfl) ⟨6395516, by rfl⟩ : syracuseStep 8527355 = 12791033) B12791033
theorem B14392889 : Blo 1684042 14392889 := bstep (se 2 (by rfl) ⟨5397333, by rfl⟩ : syracuseStep 14392889 = 10794667) B10794667
theorem B21601889 : Blo 1684042 21601889 := bstep (se 2 (by rfl) ⟨8100708, by rfl⟩ : syracuseStep 21601889 = 16201417) B16201417
theorem B3415655 : Blo 1684042 3415655 := bstep (se 1 (by rfl) ⟨2561741, by rfl⟩ : syracuseStep 3415655 = 5123483) B5123483
theorem B3792491 : Blo 1684042 3792491 := bstep (se 1 (by rfl) ⟨2844368, by rfl⟩ : syracuseStep 3792491 = 5688737) B5688737
theorem B21593891 : Blo 1684042 21593891 := bstep (se 1 (by rfl) ⟨16195418, by rfl⟩ : syracuseStep 21593891 = 32390837) B32390837
theorem B51871549 : Blo 1684042 51871549 := bstep (se 3 (by rfl) ⟨9725915, by rfl⟩ : syracuseStep 51871549 = 19451831) B19451831
theorem B3792761 : Blo 1684042 3792761 := bstep (se 2 (by rfl) ⟨1422285, by rfl⟩ : syracuseStep 3792761 = 2844571) B2844571
theorem B3792851 : Blo 1684042 3792851 := bstep (se 1 (by rfl) ⟨2844638, by rfl⟩ : syracuseStep 3792851 = 5689277) B5689277
theorem B6398099 : Blo 1684042 6398099 := bstep (se 1 (by rfl) ⟨4798574, by rfl⟩ : syracuseStep 6398099 = 9597149) B9597149
theorem B8094019 : Blo 1684042 8094019 := bstep (se 1 (by rfl) ⟨6070514, by rfl⟩ : syracuseStep 8094019 = 12141029) B12141029
theorem B3793391 : Blo 1684042 3793391 := bstep (se 1 (by rfl) ⟨2845043, by rfl⟩ : syracuseStep 3793391 = 5690087) B5690087
theorem B4801103 : Blo 1684042 4801103 := bstep (se 1 (by rfl) ⟨3600827, by rfl⟩ : syracuseStep 4801103 = 7201655) B7201655
theorem B12797351 : Blo 1684042 12797351 := bstep (se 1 (by rfl) ⟨9598013, by rfl⟩ : syracuseStep 12797351 = 19196027) B19196027
theorem B5686739 : Blo 1684042 5686739 := bstep (se 1 (by rfl) ⟨4265054, by rfl⟩ : syracuseStep 5686739 = 8530109) B8530109
theorem B13657619 : Blo 1684042 13657619 := bstep (se 1 (by rfl) ⟨10243214, by rfl⟩ : syracuseStep 13657619 = 20486429) B20486429
theorem B2131687 : Blo 1684042 2131687 := bstep (se 1 (by rfl) ⟨1598765, by rfl⟩ : syracuseStep 2131687 = 3197531) B3197531
theorem B21595895 : Blo 1684042 21595895 := bstep (se 1 (by rfl) ⟨16196921, by rfl⟩ : syracuseStep 21595895 = 32393843) B32393843
theorem B20768723 : Blo 1684042 20768723 := bstep (se 1 (by rfl) ⟨15576542, by rfl⟩ : syracuseStep 20768723 = 31153085) B31153085
theorem B12798323 : Blo 1684042 12798323 := bstep (se 1 (by rfl) ⟨9598742, by rfl⟩ : syracuseStep 12798323 = 19197485) B19197485
theorem B9595259 : Blo 1684042 9595259 := bstep (se 1 (by rfl) ⟨7196444, by rfl⟩ : syracuseStep 9595259 = 14392889) B14392889
theorem B16411049 : Blo 1684042 16411049 := bstep (se 2 (by rfl) ⟨6154143, by rfl⟩ : syracuseStep 16411049 = 12308287) B12308287
theorem B38898119 : Blo 1684042 38898119 := bstep (se 1 (by rfl) ⟨29173589, by rfl⟩ : syracuseStep 38898119 = 58347179) B58347179
theorem B14395927 : Blo 1684042 14395927 := bstep (se 1 (by rfl) ⟨10796945, by rfl⟩ : syracuseStep 14395927 = 21593891) B21593891
theorem B5925761 : Blo 1684042 5925761 := bstep (se 2 (by rfl) ⟨2222160, by rfl⟩ : syracuseStep 5925761 = 4444321) B4444321
theorem B34597793 : Blo 1684042 34597793 := bstep (se 2 (by rfl) ⟨12974172, by rfl⟩ : syracuseStep 34597793 = 25948345) B25948345
theorem B41003995 : Blo 1684042 41003995 := bstep (se 1 (by rfl) ⟨30752996, by rfl⟩ : syracuseStep 41003995 = 61505993) B61505993
theorem B9112607 : Blo 1684042 9112607 := bstep (se 1 (by rfl) ⟨6834455, by rfl⟩ : syracuseStep 9112607 = 13668911) B13668911
theorem B6401531 : Blo 1684042 6401531 := bstep (se 1 (by rfl) ⟨4801148, by rfl⟩ : syracuseStep 6401531 = 9602297) B9602297
theorem B2526887 : Blo 1684042 2526887 := bstep (se 1 (by rfl) ⟨1895165, by rfl⟩ : syracuseStep 2526887 = 3790331) B3790331
theorem B2527007 : Blo 1684042 2527007 := bstep (se 1 (by rfl) ⟨1895255, by rfl⟩ : syracuseStep 2527007 = 3790511) B3790511
theorem B2527055 : Blo 1684042 2527055 := bstep (se 1 (by rfl) ⟨1895291, by rfl⟩ : syracuseStep 2527055 = 3790583) B3790583
theorem B2527175 : Blo 1684042 2527175 := bstep (se 1 (by rfl) ⟨1895381, by rfl⟩ : syracuseStep 2527175 = 3790763) B3790763
theorem B4263911 : Blo 1684042 4263911 := bstep (se 1 (by rfl) ⟨3197933, by rfl⟩ : syracuseStep 4263911 = 6395867) B6395867
theorem B28807163 : Blo 1684042 28807163 := bstep (se 1 (by rfl) ⟨21605372, by rfl⟩ : syracuseStep 28807163 = 43210745) B43210745
theorem B2527415 : Blo 1684042 2527415 := bstep (se 1 (by rfl) ⟨1895561, by rfl⟩ : syracuseStep 2527415 = 3791123) B3791123
theorem B2527487 : Blo 1684042 2527487 := bstep (se 1 (by rfl) ⟨1895615, by rfl⟩ : syracuseStep 2527487 = 3791231) B3791231
theorem B2527535 : Blo 1684042 2527535 := bstep (se 1 (by rfl) ⟨1895651, by rfl⟩ : syracuseStep 2527535 = 3791303) B3791303
theorem B4264427 : Blo 1684042 4264427 := bstep (se 1 (by rfl) ⟨3198320, by rfl⟩ : syracuseStep 4264427 = 6396641) B6396641
theorem B2527775 : Blo 1684042 2527775 := bstep (se 1 (by rfl) ⟨1895831, by rfl⟩ : syracuseStep 2527775 = 3791663) B3791663
theorem B6394409 : Blo 1684042 6394409 := bstep (se 2 (by rfl) ⟨2397903, by rfl⟩ : syracuseStep 6394409 = 4795807) B4795807
theorem B2527835 : Blo 1684042 2527835 := bstep (se 1 (by rfl) ⟨1895876, by rfl⟩ : syracuseStep 2527835 = 3791753) B3791753
theorem B1684079 : Blo 1684042 1684079 := bstep (se 1 (by rfl) ⟨1263059, by rfl⟩ : syracuseStep 1684079 = 2526119) B2526119
theorem B1684199 : Blo 1684042 1684199 := bstep (se 1 (by rfl) ⟨1263149, by rfl⟩ : syracuseStep 1684199 = 2526299) B2526299
theorem B1684251 : Blo 1684042 1684251 := bstep (se 1 (by rfl) ⟨1263188, by rfl⟩ : syracuseStep 1684251 = 2526377) B2526377
theorem B2528039 : Blo 1684042 2528039 := bstep (se 1 (by rfl) ⟨1896029, by rfl⟩ : syracuseStep 2528039 = 3792059) B3792059
theorem B3240895 : Blo 1684042 3240895 := bstep (se 1 (by rfl) ⟨2430671, by rfl⟩ : syracuseStep 3240895 = 4861343) B4861343
theorem B2528207 : Blo 1684042 2528207 := bstep (se 1 (by rfl) ⟨1896155, by rfl⟩ : syracuseStep 2528207 = 3792311) B3792311
theorem B1684527 : Blo 1684042 1684527 := bstep (se 1 (by rfl) ⟨1263395, by rfl⟩ : syracuseStep 1684527 = 2526791) B2526791
theorem B2528327 : Blo 1684042 2528327 := bstep (se 1 (by rfl) ⟨1896245, by rfl⟩ : syracuseStep 2528327 = 3792491) B3792491
theorem B69162065 : Blo 1684042 69162065 := bstep (se 2 (by rfl) ⟨25935774, by rfl⟩ : syracuseStep 69162065 = 51871549) B51871549
theorem B1684647 : Blo 1684042 1684647 := bstep (se 1 (by rfl) ⟨1263485, by rfl⟩ : syracuseStep 1684647 = 2526971) B2526971
theorem B2528507 : Blo 1684042 2528507 := bstep (se 1 (by rfl) ⟨1896380, by rfl⟩ : syracuseStep 2528507 = 3792761) B3792761
theorem B2528567 : Blo 1684042 2528567 := bstep (se 1 (by rfl) ⟨1896425, by rfl⟩ : syracuseStep 2528567 = 3792851) B3792851
theorem B19182905 : Blo 1684042 19182905 := bstep (se 2 (by rfl) ⟨7193589, by rfl⟩ : syracuseStep 19182905 = 14387179) B14387179
theorem B1684807 : Blo 1684042 1684807 := bstep (se 1 (by rfl) ⟨1263605, by rfl⟩ : syracuseStep 1684807 = 2527211) B2527211
theorem B2528639 : Blo 1684042 2528639 := bstep (se 1 (by rfl) ⟨1896479, by rfl⟩ : syracuseStep 2528639 = 3792959) B3792959
theorem B7394735 : Blo 1684042 7394735 := bstep (se 1 (by rfl) ⟨5546051, by rfl⟩ : syracuseStep 7394735 = 11092103) B11092103
theorem B3790367 : Blo 1684042 3790367 := bstep (se 1 (by rfl) ⟨2842775, by rfl⟩ : syracuseStep 3790367 = 5685551) B5685551
theorem B2528873 : Blo 1684042 2528873 := bstep (se 2 (by rfl) ⟨948327, by rfl⟩ : syracuseStep 2528873 = 1896655) B1896655
theorem B9598607 : Blo 1684042 9598607 := bstep (se 1 (by rfl) ⟨7198955, by rfl⟩ : syracuseStep 9598607 = 14397911) B14397911
theorem B3241819 : Blo 1684042 3241819 := bstep (se 1 (by rfl) ⟨2431364, by rfl⟩ : syracuseStep 3241819 = 4862729) B4862729
theorem B27334583 : Blo 1684042 27334583 := bstep (se 1 (by rfl) ⟨20500937, by rfl⟩ : syracuseStep 27334583 = 41001875) B41001875
theorem B1685499 : Blo 1684042 1685499 := bstep (se 1 (by rfl) ⟨1264124, by rfl⟩ : syracuseStep 1685499 = 2528249) B2528249
theorem B6240253 : Blo 1684042 6240253 := bstep (se 3 (by rfl) ⟨1170047, by rfl⟩ : syracuseStep 6240253 = 2340095) B2340095
theorem B5126269 : Blo 1684042 5126269 := bstep (se 3 (by rfl) ⟨961175, by rfl⟩ : syracuseStep 5126269 = 1922351) B1922351
theorem B1685631 : Blo 1684042 1685631 := bstep (se 1 (by rfl) ⟨1264223, by rfl⟩ : syracuseStep 1685631 = 2528447) B2528447
theorem B1685727 : Blo 1684042 1685727 := bstep (se 1 (by rfl) ⟨1264295, by rfl⟩ : syracuseStep 1685727 = 2528591) B2528591
theorem B3791087 : Blo 1684042 3791087 := bstep (se 1 (by rfl) ⟨2843315, by rfl⟩ : syracuseStep 3791087 = 5686631) B5686631
theorem B1685787 : Blo 1684042 1685787 := bstep (se 1 (by rfl) ⟨1264340, by rfl⟩ : syracuseStep 1685787 = 2528681) B2528681
theorem B26286383 : Blo 1684042 26286383 := bstep (se 1 (by rfl) ⟨19714787, by rfl⟩ : syracuseStep 26286383 = 39429575) B39429575
theorem B1685823 : Blo 1684042 1685823 := bstep (se 1 (by rfl) ⟨1264367, by rfl⟩ : syracuseStep 1685823 = 2528735) B2528735
theorem B1685887 : Blo 1684042 1685887 := bstep (se 1 (by rfl) ⟨1264415, by rfl⟩ : syracuseStep 1685887 = 2528831) B2528831
theorem B3791339 : Blo 1684042 3791339 := bstep (se 1 (by rfl) ⟨2843504, by rfl⟩ : syracuseStep 3791339 = 5687009) B5687009
theorem B155695607 : Blo 1684042 155695607 := bstep (se 1 (by rfl) ⟨116771705, by rfl⟩ : syracuseStep 155695607 = 233543411) B233543411
theorem B4266503 : Blo 1684042 4266503 := bstep (se 1 (by rfl) ⟨3199877, by rfl⟩ : syracuseStep 4266503 = 6399755) B6399755
theorem B5683931 : Blo 1684042 5683931 := bstep (se 1 (by rfl) ⟨4262948, by rfl⟩ : syracuseStep 5683931 = 8525897) B8525897
theorem B7682887 : Blo 1684042 7682887 := bstep (se 1 (by rfl) ⟨5762165, by rfl⟩ : syracuseStep 7682887 = 11524331) B11524331
theorem B58350793 : Blo 1684042 58350793 := bstep (se 2 (by rfl) ⟨21881547, by rfl⟩ : syracuseStep 58350793 = 43763095) B43763095
theorem B2841851 : Blo 1684042 2841851 := bstep (se 1 (by rfl) ⟨2131388, by rfl⟩ : syracuseStep 2841851 = 4262777) B4262777
theorem B9592091 : Blo 1684042 9592091 := bstep (se 1 (by rfl) ⟨7194068, by rfl⟩ : syracuseStep 9592091 = 14388137) B14388137
theorem B4267343 : Blo 1684042 4267343 := bstep (se 1 (by rfl) ⟨3200507, by rfl⟩ : syracuseStep 4267343 = 6401015) B6401015
theorem B109354373 : Blo 1684042 109354373 := bstep (se 4 (by rfl) ⟨10251972, by rfl⟩ : syracuseStep 109354373 = 20503945) B20503945
theorem B5684903 : Blo 1684042 5684903 := bstep (se 1 (by rfl) ⟨4263677, by rfl⟩ : syracuseStep 5684903 = 8527355) B8527355
theorem B14401259 : Blo 1684042 14401259 := bstep (se 1 (by rfl) ⟨10800944, by rfl⟩ : syracuseStep 14401259 = 21601889) B21601889
theorem B2277103 : Blo 1684042 2277103 := bstep (se 1 (by rfl) ⟨1707827, by rfl⟩ : syracuseStep 2277103 = 3415655) B3415655
theorem B2842951 : Blo 1684042 2842951 := bstep (se 1 (by rfl) ⟨2132213, by rfl⟩ : syracuseStep 2842951 = 4264427) B4264427
theorem B19194569 : Blo 1684042 19194569 := bstep (se 2 (by rfl) ⟨7197963, by rfl⟩ : syracuseStep 19194569 = 14395927) B14395927
theorem B12788603 : Blo 1684042 12788603 := bstep (se 1 (by rfl) ⟨9591452, by rfl⟩ : syracuseStep 12788603 = 19182905) B19182905
theorem B6399071 : Blo 1684042 6399071 := bstep (se 1 (by rfl) ⟨4799303, by rfl⟩ : syracuseStep 6399071 = 9598607) B9598607
theorem B13845815 : Blo 1684042 13845815 := bstep (se 1 (by rfl) ⟨10384361, by rfl⟩ : syracuseStep 13845815 = 20768723) B20768723
theorem B17524255 : Blo 1684042 17524255 := bstep (se 1 (by rfl) ⟨13143191, by rfl⟩ : syracuseStep 17524255 = 26286383) B26286383
theorem B77801057 : Blo 1684042 77801057 := bstep (se 2 (by rfl) ⟨29175396, by rfl⟩ : syracuseStep 77801057 = 58350793) B58350793
theorem B2844335 : Blo 1684042 2844335 := bstep (se 1 (by rfl) ⟨2133251, by rfl⟩ : syracuseStep 2844335 = 4266503) B4266503
theorem B3950507 : Blo 1684042 3950507 := bstep (se 1 (by rfl) ⟨2962880, by rfl⟩ : syracuseStep 3950507 = 5925761) B5925761
theorem B1894567 : Blo 1684042 1894567 := bstep (se 1 (by rfl) ⟨1420925, by rfl⟩ : syracuseStep 1894567 = 2841851) B2841851
theorem B2844895 : Blo 1684042 2844895 := bstep (se 1 (by rfl) ⟨2133671, by rfl⟩ : syracuseStep 2844895 = 4267343) B4267343
theorem B72902915 : Blo 1684042 72902915 := bstep (se 1 (by rfl) ⟨54677186, by rfl⟩ : syracuseStep 72902915 = 109354373) B109354373
theorem B19204775 : Blo 1684042 19204775 := bstep (se 1 (by rfl) ⟨14403581, by rfl⟩ : syracuseStep 19204775 = 28807163) B28807163
theorem B6835025 : Blo 1684042 6835025 := bstep (se 2 (by rfl) ⟨2563134, by rfl⟩ : syracuseStep 6835025 = 5126269) B5126269
theorem B4262939 : Blo 1684042 4262939 := bstep (se 1 (by rfl) ⟨3197204, by rfl⟩ : syracuseStep 4262939 = 6394409) B6394409
theorem B10792025 : Blo 1684042 10792025 := bstep (se 2 (by rfl) ⟨4047009, by rfl⟩ : syracuseStep 10792025 = 8094019) B8094019
theorem B46108043 : Blo 1684042 46108043 := bstep (se 1 (by rfl) ⟨34581032, by rfl⟩ : syracuseStep 46108043 = 69162065) B69162065
theorem B8531567 : Blo 1684042 8531567 := bstep (se 1 (by rfl) ⟨6398675, by rfl⟩ : syracuseStep 8531567 = 12797351) B12797351
theorem B2526911 : Blo 1684042 2526911 := bstep (se 1 (by rfl) ⟨1895183, by rfl⟩ : syracuseStep 2526911 = 3790367) B3790367
theorem B10243849 : Blo 1684042 10243849 := bstep (se 2 (by rfl) ⟨3841443, by rfl⟩ : syracuseStep 10243849 = 7682887) B7682887
theorem B14397263 : Blo 1684042 14397263 := bstep (se 1 (by rfl) ⟨10797947, by rfl⟩ : syracuseStep 14397263 = 21595895) B21595895
theorem B4321193 : Blo 1684042 4321193 := bstep (se 2 (by rfl) ⟨1620447, by rfl⟩ : syracuseStep 4321193 = 3240895) B3240895
theorem B18223055 : Blo 1684042 18223055 := bstep (se 1 (by rfl) ⟨13667291, by rfl⟩ : syracuseStep 18223055 = 27334583) B27334583
theorem B2527391 : Blo 1684042 2527391 := bstep (se 1 (by rfl) ⟨1895543, by rfl⟩ : syracuseStep 2527391 = 3791087) B3791087
theorem B8532215 : Blo 1684042 8532215 := bstep (se 1 (by rfl) ⟨6399161, by rfl⟩ : syracuseStep 8532215 = 12798323) B12798323
theorem B10940699 : Blo 1684042 10940699 := bstep (se 1 (by rfl) ⟨8205524, by rfl⟩ : syracuseStep 10940699 = 16411049) B16411049
theorem B25932079 : Blo 1684042 25932079 := bstep (se 1 (by rfl) ⟨19449059, by rfl⟩ : syracuseStep 25932079 = 38898119) B38898119
theorem B2527559 : Blo 1684042 2527559 := bstep (se 1 (by rfl) ⟨1895669, by rfl⟩ : syracuseStep 2527559 = 3791339) B3791339
theorem B103797071 : Blo 1684042 103797071 := bstep (se 1 (by rfl) ⟨77847803, by rfl⟩ : syracuseStep 103797071 = 155695607) B155695607
theorem B3789287 : Blo 1684042 3789287 := bstep (se 1 (by rfl) ⟨2841965, by rfl⟩ : syracuseStep 3789287 = 5683931) B5683931
theorem B23065195 : Blo 1684042 23065195 := bstep (se 1 (by rfl) ⟨17298896, by rfl⟩ : syracuseStep 23065195 = 34597793) B34597793
theorem B6075071 : Blo 1684042 6075071 := bstep (se 1 (by rfl) ⟨4556303, by rfl⟩ : syracuseStep 6075071 = 9112607) B9112607
theorem B6394727 : Blo 1684042 6394727 := bstep (se 1 (by rfl) ⟨4796045, by rfl⟩ : syracuseStep 6394727 = 9592091) B9592091
theorem B3036137 : Blo 1684042 3036137 := bstep (se 2 (by rfl) ⟨1138551, by rfl⟩ : syracuseStep 3036137 = 2277103) B2277103
theorem B3789935 : Blo 1684042 3789935 := bstep (se 1 (by rfl) ⟨2842451, by rfl⟩ : syracuseStep 3789935 = 5684903) B5684903
theorem B1684591 : Blo 1684042 1684591 := bstep (se 1 (by rfl) ⟨1263443, by rfl⟩ : syracuseStep 1684591 = 2526887) B2526887
theorem B4322425 : Blo 1684042 4322425 := bstep (se 2 (by rfl) ⟨1620909, by rfl⟩ : syracuseStep 4322425 = 3241819) B3241819
theorem B1684671 : Blo 1684042 1684671 := bstep (se 1 (by rfl) ⟨1263503, by rfl⟩ : syracuseStep 1684671 = 2527007) B2527007
theorem B1684703 : Blo 1684042 1684703 := bstep (se 1 (by rfl) ⟨1263527, by rfl⟩ : syracuseStep 1684703 = 2527055) B2527055
theorem B1684783 : Blo 1684042 1684783 := bstep (se 1 (by rfl) ⟨1263587, by rfl⟩ : syracuseStep 1684783 = 2527175) B2527175
theorem B8320337 : Blo 1684042 8320337 := bstep (se 2 (by rfl) ⟨3120126, by rfl⟩ : syracuseStep 8320337 = 6240253) B6240253
theorem B4265399 : Blo 1684042 4265399 := bstep (se 1 (by rfl) ⟨3199049, by rfl⟩ : syracuseStep 4265399 = 6398099) B6398099
theorem B1684943 : Blo 1684042 1684943 := bstep (se 1 (by rfl) ⟨1263707, by rfl⟩ : syracuseStep 1684943 = 2527415) B2527415
theorem B1684991 : Blo 1684042 1684991 := bstep (se 1 (by rfl) ⟨1263743, by rfl⟩ : syracuseStep 1684991 = 2527487) B2527487
theorem B1685023 : Blo 1684042 1685023 := bstep (se 1 (by rfl) ⟨1263767, by rfl⟩ : syracuseStep 1685023 = 2527535) B2527535
theorem B2528927 : Blo 1684042 2528927 := bstep (se 1 (by rfl) ⟨1896695, by rfl⟩ : syracuseStep 2528927 = 3793391) B3793391
theorem B1685183 : Blo 1684042 1685183 := bstep (se 1 (by rfl) ⟨1263887, by rfl⟩ : syracuseStep 1685183 = 2527775) B2527775
theorem B3200735 : Blo 1684042 3200735 := bstep (se 1 (by rfl) ⟨2400551, by rfl⟩ : syracuseStep 3200735 = 4801103) B4801103
theorem B1685223 : Blo 1684042 1685223 := bstep (se 1 (by rfl) ⟨1263917, by rfl⟩ : syracuseStep 1685223 = 2527835) B2527835
theorem B1685359 : Blo 1684042 1685359 := bstep (se 1 (by rfl) ⟨1264019, by rfl⟩ : syracuseStep 1685359 = 2528039) B2528039
theorem B1685471 : Blo 1684042 1685471 := bstep (se 1 (by rfl) ⟨1264103, by rfl⟩ : syracuseStep 1685471 = 2528207) B2528207
theorem B1685551 : Blo 1684042 1685551 := bstep (se 1 (by rfl) ⟨1264163, by rfl⟩ : syracuseStep 1685551 = 2528327) B2528327
theorem B1685671 : Blo 1684042 1685671 := bstep (se 1 (by rfl) ⟨1264253, by rfl⟩ : syracuseStep 1685671 = 2528507) B2528507
theorem B1685711 : Blo 1684042 1685711 := bstep (se 1 (by rfl) ⟨1264283, by rfl⟩ : syracuseStep 1685711 = 2528567) B2528567
theorem B1685759 : Blo 1684042 1685759 := bstep (se 1 (by rfl) ⟨1264319, by rfl⟩ : syracuseStep 1685759 = 2528639) B2528639
theorem B4929823 : Blo 1684042 4929823 := bstep (se 1 (by rfl) ⟨3697367, by rfl⟩ : syracuseStep 4929823 = 7394735) B7394735
theorem B3791159 : Blo 1684042 3791159 := bstep (se 1 (by rfl) ⟨2843369, by rfl⟩ : syracuseStep 3791159 = 5686739) B5686739
theorem B1685915 : Blo 1684042 1685915 := bstep (se 1 (by rfl) ⟨1264436, by rfl⟩ : syracuseStep 1685915 = 2528873) B2528873
theorem B54671993 : Blo 1684042 54671993 := bstep (se 2 (by rfl) ⟨20501997, by rfl⟩ : syracuseStep 54671993 = 41003995) B41003995
theorem B36420317 : Blo 1684042 36420317 := bstep (se 3 (by rfl) ⟨6828809, by rfl⟩ : syracuseStep 36420317 = 13657619) B13657619
theorem B6396839 : Blo 1684042 6396839 := bstep (se 1 (by rfl) ⟨4797629, by rfl⟩ : syracuseStep 6396839 = 9595259) B9595259
theorem B2842249 : Blo 1684042 2842249 := bstep (se 2 (by rfl) ⟨1065843, by rfl⟩ : syracuseStep 2842249 = 2131687) B2131687
theorem B4267687 : Blo 1684042 4267687 := bstep (se 1 (by rfl) ⟨3200765, by rfl⟩ : syracuseStep 4267687 = 6401531) B6401531
theorem B9600839 : Blo 1684042 9600839 := bstep (se 1 (by rfl) ⟨7200629, by rfl⟩ : syracuseStep 9600839 = 14401259) B14401259
theorem B2842607 : Blo 1684042 2842607 := bstep (se 1 (by rfl) ⟨2131955, by rfl⟩ : syracuseStep 2842607 = 4263911) B4263911
theorem B69198047 : Blo 1684042 69198047 := bstep (se 1 (by rfl) ⟨51898535, by rfl⟩ : syracuseStep 69198047 = 103797071) B103797071
theorem B3793193 : Blo 1684042 3793193 := bstep (se 2 (by rfl) ⟨1422447, by rfl⟩ : syracuseStep 3793193 = 2844895) B2844895
theorem B12796379 : Blo 1684042 12796379 := bstep (se 1 (by rfl) ⟨9597284, by rfl⟩ : syracuseStep 12796379 = 19194569) B19194569
theorem B30753593 : Blo 1684042 30753593 := bstep (se 2 (by rfl) ⟨11532597, by rfl⟩ : syracuseStep 30753593 = 23065195) B23065195
theorem B5546891 : Blo 1684042 5546891 := bstep (se 1 (by rfl) ⟨4160168, by rfl⟩ : syracuseStep 5546891 = 8320337) B8320337
theorem B2843599 : Blo 1684042 2843599 := bstep (se 1 (by rfl) ⟨2132699, by rfl⟩ : syracuseStep 2843599 = 4265399) B4265399
theorem B36447995 : Blo 1684042 36447995 := bstep (se 1 (by rfl) ⟨27335996, by rfl⟩ : syracuseStep 36447995 = 54671993) B54671993
theorem B4556683 : Blo 1684042 4556683 := bstep (se 1 (by rfl) ⟨3417512, by rfl⟩ : syracuseStep 4556683 = 6835025) B6835025
theorem B23365673 : Blo 1684042 23365673 := bstep (se 2 (by rfl) ⟨8762127, by rfl⟩ : syracuseStep 23365673 = 17524255) B17524255
theorem B7194683 : Blo 1684042 7194683 := bstep (se 1 (by rfl) ⟨5396012, by rfl⟩ : syracuseStep 7194683 = 10792025) B10792025
theorem B30738695 : Blo 1684042 30738695 := bstep (se 1 (by rfl) ⟨23054021, by rfl⟩ : syracuseStep 30738695 = 46108043) B46108043
theorem B13658465 : Blo 1684042 13658465 := bstep (se 2 (by rfl) ⟨5121924, by rfl⟩ : syracuseStep 13658465 = 10243849) B10243849
theorem B5687711 : Blo 1684042 5687711 := bstep (se 1 (by rfl) ⟨4265783, by rfl⟩ : syracuseStep 5687711 = 8531567) B8531567
theorem B6400559 : Blo 1684042 6400559 := bstep (se 1 (by rfl) ⟨4800419, by rfl⟩ : syracuseStep 6400559 = 9600839) B9600839
theorem B8096365 : Blo 1684042 8096365 := bstep (se 3 (by rfl) ⟨1518068, by rfl⟩ : syracuseStep 8096365 = 3036137) B3036137
theorem B1895071 : Blo 1684042 1895071 := bstep (se 1 (by rfl) ⟨1421303, by rfl⟩ : syracuseStep 1895071 = 2842607) B2842607
theorem B5688143 : Blo 1684042 5688143 := bstep (se 1 (by rfl) ⟨4266107, by rfl⟩ : syracuseStep 5688143 = 8532215) B8532215
theorem B7293799 : Blo 1684042 7293799 := bstep (se 1 (by rfl) ⟨5470349, by rfl⟩ : syracuseStep 7293799 = 10940699) B10940699
theorem B2526089 : Blo 1684042 2526089 := bstep (se 2 (by rfl) ⟨947283, by rfl⟩ : syracuseStep 2526089 = 1894567) B1894567
theorem B2526191 : Blo 1684042 2526191 := bstep (se 1 (by rfl) ⟨1894643, by rfl⟩ : syracuseStep 2526191 = 3789287) B3789287
theorem B6573097 : Blo 1684042 6573097 := bstep (se 2 (by rfl) ⟨2464911, by rfl⟩ : syracuseStep 6573097 = 4929823) B4929823
theorem B4050047 : Blo 1684042 4050047 := bstep (se 1 (by rfl) ⟨3037535, by rfl⟩ : syracuseStep 4050047 = 6075071) B6075071
theorem B4263151 : Blo 1684042 4263151 := bstep (se 1 (by rfl) ⟨3197363, by rfl⟩ : syracuseStep 4263151 = 6394727) B6394727
theorem B2526623 : Blo 1684042 2526623 := bstep (se 1 (by rfl) ⟨1894967, by rfl⟩ : syracuseStep 2526623 = 3789935) B3789935
theorem B51867371 : Blo 1684042 51867371 := bstep (se 1 (by rfl) ⟨38900528, by rfl⟩ : syracuseStep 51867371 = 77801057) B77801057
theorem B1896223 : Blo 1684042 1896223 := bstep (se 1 (by rfl) ⟨1422167, by rfl⟩ : syracuseStep 1896223 = 2844335) B2844335
theorem B2633671 : Blo 1684042 2633671 := bstep (se 1 (by rfl) ⟨1975253, by rfl⟩ : syracuseStep 2633671 = 3950507) B3950507
theorem B5763233 : Blo 1684042 5763233 := bstep (se 2 (by rfl) ⟨2161212, by rfl⟩ : syracuseStep 5763233 = 4322425) B4322425
theorem B2527439 : Blo 1684042 2527439 := bstep (se 1 (by rfl) ⟨1895579, by rfl⟩ : syracuseStep 2527439 = 3791159) B3791159
theorem B4264559 : Blo 1684042 4264559 := bstep (se 1 (by rfl) ⟨3198419, by rfl⟩ : syracuseStep 4264559 = 6396839) B6396839
theorem B3789665 : Blo 1684042 3789665 := bstep (se 2 (by rfl) ⟨1421124, by rfl⟩ : syracuseStep 3789665 = 2842249) B2842249
theorem B5690249 : Blo 1684042 5690249 := bstep (se 2 (by rfl) ⟨2133843, by rfl⟩ : syracuseStep 5690249 = 4267687) B4267687
theorem B11523181 : Blo 1684042 11523181 := bstep (se 3 (by rfl) ⟨2160596, by rfl⟩ : syracuseStep 11523181 = 4321193) B4321193
theorem B1684607 : Blo 1684042 1684607 := bstep (se 1 (by rfl) ⟨1263455, by rfl⟩ : syracuseStep 1684607 = 2526911) B2526911
theorem B9598175 : Blo 1684042 9598175 := bstep (se 1 (by rfl) ⟨7198631, by rfl⟩ : syracuseStep 9598175 = 14397263) B14397263
theorem B1684927 : Blo 1684042 1684927 := bstep (se 1 (by rfl) ⟨1263695, by rfl⟩ : syracuseStep 1684927 = 2527391) B2527391
theorem B1685039 : Blo 1684042 1685039 := bstep (se 1 (by rfl) ⟨1263779, by rfl⟩ : syracuseStep 1685039 = 2527559) B2527559
theorem B34576105 : Blo 1684042 34576105 := bstep (se 2 (by rfl) ⟨12966039, by rfl⟩ : syracuseStep 34576105 = 25932079) B25932079
theorem B3790601 : Blo 1684042 3790601 := bstep (se 2 (by rfl) ⟨1421475, by rfl⟩ : syracuseStep 3790601 = 2842951) B2842951
theorem B8525735 : Blo 1684042 8525735 := bstep (se 1 (by rfl) ⟨6394301, by rfl⟩ : syracuseStep 8525735 = 12788603) B12788603
theorem B4266047 : Blo 1684042 4266047 := bstep (se 1 (by rfl) ⟨3199535, by rfl⟩ : syracuseStep 4266047 = 6399071) B6399071
theorem B9230543 : Blo 1684042 9230543 := bstep (se 1 (by rfl) ⟨6922907, by rfl⟩ : syracuseStep 9230543 = 13845815) B13845815
theorem B1685951 : Blo 1684042 1685951 := bstep (se 1 (by rfl) ⟨1264463, by rfl⟩ : syracuseStep 1685951 = 2528927) B2528927
theorem B48601943 : Blo 1684042 48601943 := bstep (se 1 (by rfl) ⟨36451457, by rfl⟩ : syracuseStep 48601943 = 72902915) B72902915
theorem B12803183 : Blo 1684042 12803183 := bstep (se 1 (by rfl) ⟨9602387, by rfl⟩ : syracuseStep 12803183 = 19204775) B19204775
theorem B24280211 : Blo 1684042 24280211 := bstep (se 1 (by rfl) ⟨18210158, by rfl⟩ : syracuseStep 24280211 = 36420317) B36420317
theorem B8535293 : Blo 1684042 8535293 := bstep (se 3 (by rfl) ⟨1600367, by rfl⟩ : syracuseStep 8535293 = 3200735) B3200735
theorem B2841959 : Blo 1684042 2841959 := bstep (se 1 (by rfl) ⟨2131469, by rfl⟩ : syracuseStep 2841959 = 4262939) B4262939
theorem B12148703 : Blo 1684042 12148703 := bstep (se 1 (by rfl) ⟨9111527, by rfl⟩ : syracuseStep 12148703 = 18223055) B18223055
theorem B3842155 : Blo 1684042 3842155 := bstep (se 1 (by rfl) ⟨2881616, by rfl⟩ : syracuseStep 3842155 = 5763233) B5763233
theorem B19185821 : Blo 1684042 19185821 := bstep (se 3 (by rfl) ⟨3597341, by rfl⟩ : syracuseStep 19185821 = 7194683) B7194683
theorem B2843039 : Blo 1684042 2843039 := bstep (se 1 (by rfl) ⟨2132279, by rfl⟩ : syracuseStep 2843039 = 4264559) B4264559
theorem B3793499 : Blo 1684042 3793499 := bstep (se 1 (by rfl) ⟨2845124, by rfl⟩ : syracuseStep 3793499 = 5690249) B5690249
theorem B81969853 : Blo 1684042 81969853 := bstep (se 3 (by rfl) ⟨15369347, by rfl⟩ : syracuseStep 81969853 = 30738695) B30738695
theorem B6398783 : Blo 1684042 6398783 := bstep (se 1 (by rfl) ⟨4799087, by rfl⟩ : syracuseStep 6398783 = 9598175) B9598175
theorem B9725065 : Blo 1684042 9725065 := bstep (se 2 (by rfl) ⟨3646899, by rfl⟩ : syracuseStep 9725065 = 7293799) B7293799
theorem B2844031 : Blo 1684042 2844031 := bstep (se 1 (by rfl) ⟨2133023, by rfl⟩ : syracuseStep 2844031 = 4266047) B4266047
theorem B6153695 : Blo 1684042 6153695 := bstep (se 1 (by rfl) ⟨4615271, by rfl⟩ : syracuseStep 6153695 = 9230543) B9230543
theorem B32401295 : Blo 1684042 32401295 := bstep (se 1 (by rfl) ⟨24300971, by rfl⟩ : syracuseStep 32401295 = 48601943) B48601943
theorem B1894639 : Blo 1684042 1894639 := bstep (se 1 (by rfl) ⟨1420979, by rfl⟩ : syracuseStep 1894639 = 2841959) B2841959
theorem B46132031 : Blo 1684042 46132031 := bstep (se 1 (by rfl) ⟨34599023, by rfl⟩ : syracuseStep 46132031 = 69198047) B69198047
theorem B8530919 : Blo 1684042 8530919 := bstep (se 1 (by rfl) ⟨6398189, by rfl⟩ : syracuseStep 8530919 = 12796379) B12796379
theorem B10800125 : Blo 1684042 10800125 := bstep (se 3 (by rfl) ⟨2025023, by rfl⟩ : syracuseStep 10800125 = 4050047) B4050047
theorem B2526443 : Blo 1684042 2526443 := bstep (se 1 (by rfl) ⟨1894832, by rfl⟩ : syracuseStep 2526443 = 3789665) B3789665
theorem B2526761 : Blo 1684042 2526761 := bstep (se 2 (by rfl) ⟨947535, by rfl⟩ : syracuseStep 2526761 = 1895071) B1895071
theorem B2527067 : Blo 1684042 2527067 := bstep (se 1 (by rfl) ⟨1895300, by rfl⟩ : syracuseStep 2527067 = 3790601) B3790601
theorem B15577115 : Blo 1684042 15577115 := bstep (se 1 (by rfl) ⟨11682836, by rfl⟩ : syracuseStep 15577115 = 23365673) B23365673
theorem B15364241 : Blo 1684042 15364241 := bstep (se 2 (by rfl) ⟨5761590, by rfl⟩ : syracuseStep 15364241 = 11523181) B11523181
theorem B9105643 : Blo 1684042 9105643 := bstep (se 1 (by rfl) ⟨6829232, by rfl⟩ : syracuseStep 9105643 = 13658465) B13658465
theorem B1684059 : Blo 1684042 1684059 := bstep (se 1 (by rfl) ⟨1263044, by rfl⟩ : syracuseStep 1684059 = 2526089) B2526089
theorem B1684127 : Blo 1684042 1684127 := bstep (se 1 (by rfl) ⟨1263095, by rfl⟩ : syracuseStep 1684127 = 2526191) B2526191
theorem B97194653 : Blo 1684042 97194653 := bstep (se 3 (by rfl) ⟨18223997, by rfl⟩ : syracuseStep 97194653 = 36447995) B36447995
theorem B5690195 : Blo 1684042 5690195 := bstep (se 1 (by rfl) ⟨4267646, by rfl⟩ : syracuseStep 5690195 = 8535293) B8535293
theorem B1684415 : Blo 1684042 1684415 := bstep (se 1 (by rfl) ⟨1263311, by rfl⟩ : syracuseStep 1684415 = 2526623) B2526623
theorem B46101473 : Blo 1684042 46101473 := bstep (se 2 (by rfl) ⟨17288052, by rfl⟩ : syracuseStep 46101473 = 34576105) B34576105
theorem B14791709 : Blo 1684042 14791709 := bstep (se 3 (by rfl) ⟨2773445, by rfl⟩ : syracuseStep 14791709 = 5546891) B5546891
theorem B2528297 : Blo 1684042 2528297 := bstep (se 2 (by rfl) ⟨948111, by rfl⟩ : syracuseStep 2528297 = 1896223) B1896223
theorem B6075577 : Blo 1684042 6075577 := bstep (se 2 (by rfl) ⟨2278341, by rfl⟩ : syracuseStep 6075577 = 4556683) B4556683
theorem B3511561 : Blo 1684042 3511561 := bstep (se 2 (by rfl) ⟨1316835, by rfl⟩ : syracuseStep 3511561 = 2633671) B2633671
theorem B8099135 : Blo 1684042 8099135 := bstep (se 1 (by rfl) ⟨6074351, by rfl⟩ : syracuseStep 8099135 = 12148703) B12148703
theorem B1684959 : Blo 1684042 1684959 := bstep (se 1 (by rfl) ⟨1263719, by rfl⟩ : syracuseStep 1684959 = 2527439) B2527439
theorem B2528795 : Blo 1684042 2528795 := bstep (se 1 (by rfl) ⟨1896596, by rfl⟩ : syracuseStep 2528795 = 3793193) B3793193
theorem B20502395 : Blo 1684042 20502395 := bstep (se 1 (by rfl) ⟨15376796, by rfl⟩ : syracuseStep 20502395 = 30753593) B30753593
theorem B10795153 : Blo 1684042 10795153 := bstep (se 2 (by rfl) ⟨4048182, by rfl⟩ : syracuseStep 10795153 = 8096365) B8096365
theorem B3791465 : Blo 1684042 3791465 := bstep (se 2 (by rfl) ⟨1421799, by rfl⟩ : syracuseStep 3791465 = 2843599) B2843599
theorem B5683823 : Blo 1684042 5683823 := bstep (se 1 (by rfl) ⟨4262867, by rfl⟩ : syracuseStep 5683823 = 8525735) B8525735
theorem B8764129 : Blo 1684042 8764129 := bstep (se 2 (by rfl) ⟨3286548, by rfl⟩ : syracuseStep 8764129 = 6573097) B6573097
theorem B3791807 : Blo 1684042 3791807 := bstep (se 1 (by rfl) ⟨2843855, by rfl⟩ : syracuseStep 3791807 = 5687711) B5687711
theorem B5684201 : Blo 1684042 5684201 := bstep (se 2 (by rfl) ⟨2131575, by rfl⟩ : syracuseStep 5684201 = 4263151) B4263151
theorem B4267039 : Blo 1684042 4267039 := bstep (se 1 (by rfl) ⟨3200279, by rfl⟩ : syracuseStep 4267039 = 6400559) B6400559
theorem B3792095 : Blo 1684042 3792095 := bstep (se 1 (by rfl) ⟨2844071, by rfl⟩ : syracuseStep 3792095 = 5688143) B5688143
theorem B8535455 : Blo 1684042 8535455 := bstep (se 1 (by rfl) ⟨6401591, by rfl⟩ : syracuseStep 8535455 = 12803183) B12803183
theorem B16186807 : Blo 1684042 16186807 := bstep (se 1 (by rfl) ⟨12140105, by rfl⟩ : syracuseStep 16186807 = 24280211) B24280211
theorem B34578247 : Blo 1684042 34578247 := bstep (se 1 (by rfl) ⟨25933685, by rfl⟩ : syracuseStep 34578247 = 51867371) B51867371
theorem B14393537 : Blo 1684042 14393537 := bstep (se 2 (by rfl) ⟨5397576, by rfl⟩ : syracuseStep 14393537 = 10795153) B10795153
theorem B12140857 : Blo 1684042 12140857 := bstep (se 2 (by rfl) ⟨4552821, by rfl⟩ : syracuseStep 12140857 = 9105643) B9105643
theorem B3793463 : Blo 1684042 3793463 := bstep (se 1 (by rfl) ⟨2845097, by rfl⟩ : syracuseStep 3793463 = 5690195) B5690195
theorem B5399423 : Blo 1684042 5399423 := bstep (se 1 (by rfl) ⟨4049567, by rfl⟩ : syracuseStep 5399423 = 8099135) B8099135
theorem B5687279 : Blo 1684042 5687279 := bstep (se 1 (by rfl) ⟨4265459, by rfl⟩ : syracuseStep 5687279 = 8530919) B8530919
theorem B10242827 : Blo 1684042 10242827 := bstep (se 1 (by rfl) ⟨7682120, by rfl⟩ : syracuseStep 10242827 = 15364241) B15364241
theorem B12790547 : Blo 1684042 12790547 := bstep (se 1 (by rfl) ⟨9592910, by rfl⟩ : syracuseStep 12790547 = 19185821) B19185821
theorem B5122873 : Blo 1684042 5122873 := bstep (se 2 (by rfl) ⟨1921077, by rfl⟩ : syracuseStep 5122873 = 3842155) B3842155
theorem B1895359 : Blo 1684042 1895359 := bstep (se 1 (by rfl) ⟨1421519, by rfl⟩ : syracuseStep 1895359 = 2843039) B2843039
theorem B2526185 : Blo 1684042 2526185 := bstep (se 2 (by rfl) ⟨947319, by rfl⟩ : syracuseStep 2526185 = 1894639) B1894639
theorem B51867013 : Blo 1684042 51867013 := bstep (se 4 (by rfl) ⟨4862532, by rfl⟩ : syracuseStep 51867013 = 9725065) B9725065
theorem B109293137 : Blo 1684042 109293137 := bstep (se 2 (by rfl) ⟨40984926, by rfl⟩ : syracuseStep 109293137 = 81969853) B81969853
theorem B13668263 : Blo 1684042 13668263 := bstep (se 1 (by rfl) ⟨10251197, by rfl⟩ : syracuseStep 13668263 = 20502395) B20502395
theorem B5689385 : Blo 1684042 5689385 := bstep (se 2 (by rfl) ⟨2133519, by rfl⟩ : syracuseStep 5689385 = 4267039) B4267039
theorem B4682081 : Blo 1684042 4682081 := bstep (se 2 (by rfl) ⟨1755780, by rfl⟩ : syracuseStep 4682081 = 3511561) B3511561
theorem B2527643 : Blo 1684042 2527643 := bstep (se 1 (by rfl) ⟨1895732, by rfl⟩ : syracuseStep 2527643 = 3791465) B3791465
theorem B3789215 : Blo 1684042 3789215 := bstep (se 1 (by rfl) ⟨2841911, by rfl⟩ : syracuseStep 3789215 = 5683823) B5683823
theorem B21582409 : Blo 1684042 21582409 := bstep (se 2 (by rfl) ⟨8093403, by rfl⟩ : syracuseStep 21582409 = 16186807) B16186807
theorem B2527871 : Blo 1684042 2527871 := bstep (se 1 (by rfl) ⟨1895903, by rfl⟩ : syracuseStep 2527871 = 3791807) B3791807
theorem B3789467 : Blo 1684042 3789467 := bstep (se 1 (by rfl) ⟨2842100, by rfl⟩ : syracuseStep 3789467 = 5684201) B5684201
theorem B2528063 : Blo 1684042 2528063 := bstep (se 1 (by rfl) ⟨1896047, by rfl⟩ : syracuseStep 2528063 = 3792095) B3792095
theorem B1684295 : Blo 1684042 1684295 := bstep (se 1 (by rfl) ⟨1263221, by rfl⟩ : syracuseStep 1684295 = 2526443) B2526443
theorem B5690303 : Blo 1684042 5690303 := bstep (se 1 (by rfl) ⟨4267727, by rfl⟩ : syracuseStep 5690303 = 8535455) B8535455
theorem B1684507 : Blo 1684042 1684507 := bstep (se 1 (by rfl) ⟨1263380, by rfl⟩ : syracuseStep 1684507 = 2526761) B2526761
theorem B1684711 : Blo 1684042 1684711 := bstep (se 1 (by rfl) ⟨1263533, by rfl⟩ : syracuseStep 1684711 = 2527067) B2527067
theorem B41538973 : Blo 1684042 41538973 := bstep (se 3 (by rfl) ⟨7788557, by rfl⟩ : syracuseStep 41538973 = 15577115) B15577115
theorem B2528999 : Blo 1684042 2528999 := bstep (se 1 (by rfl) ⟨1896749, by rfl⟩ : syracuseStep 2528999 = 3793499) B3793499
theorem B64796435 : Blo 1684042 64796435 := bstep (se 1 (by rfl) ⟨48597326, by rfl⟩ : syracuseStep 64796435 = 97194653) B97194653
theorem B4265855 : Blo 1684042 4265855 := bstep (se 1 (by rfl) ⟨3199391, by rfl⟩ : syracuseStep 4265855 = 6398783) B6398783
theorem B30734315 : Blo 1684042 30734315 := bstep (se 1 (by rfl) ⟨23050736, by rfl⟩ : syracuseStep 30734315 = 46101473) B46101473
theorem B9861139 : Blo 1684042 9861139 := bstep (se 1 (by rfl) ⟨7395854, by rfl⟩ : syracuseStep 9861139 = 14791709) B14791709
theorem B1685531 : Blo 1684042 1685531 := bstep (se 1 (by rfl) ⟨1264148, by rfl⟩ : syracuseStep 1685531 = 2528297) B2528297
theorem B4102463 : Blo 1684042 4102463 := bstep (se 1 (by rfl) ⟨3076847, by rfl⟩ : syracuseStep 4102463 = 6153695) B6153695
theorem B1685863 : Blo 1684042 1685863 := bstep (se 1 (by rfl) ⟨1264397, by rfl⟩ : syracuseStep 1685863 = 2528795) B2528795
theorem B46742021 : Blo 1684042 46742021 := bstep (se 4 (by rfl) ⟨4382064, by rfl⟩ : syracuseStep 46742021 = 8764129) B8764129
theorem B21600863 : Blo 1684042 21600863 := bstep (se 1 (by rfl) ⟨16200647, by rfl⟩ : syracuseStep 21600863 = 32401295) B32401295
theorem B8100769 : Blo 1684042 8100769 := bstep (se 2 (by rfl) ⟨3037788, by rfl⟩ : syracuseStep 8100769 = 6075577) B6075577
theorem B3792041 : Blo 1684042 3792041 := bstep (se 2 (by rfl) ⟨1422015, by rfl⟩ : syracuseStep 3792041 = 2844031) B2844031
theorem B7200083 : Blo 1684042 7200083 := bstep (se 1 (by rfl) ⟨5400062, by rfl⟩ : syracuseStep 7200083 = 10800125) B10800125
theorem B123018749 : Blo 1684042 123018749 := bstep (se 3 (by rfl) ⟨23066015, by rfl⟩ : syracuseStep 123018749 = 46132031) B46132031
theorem B46104329 : Blo 1684042 46104329 := bstep (se 2 (by rfl) ⟨17289123, by rfl⟩ : syracuseStep 46104329 = 34578247) B34578247
theorem B13148185 : Blo 1684042 13148185 := bstep (se 2 (by rfl) ⟨4930569, by rfl⟩ : syracuseStep 13148185 = 9861139) B9861139
theorem B3792923 : Blo 1684042 3792923 := bstep (se 1 (by rfl) ⟨2844692, by rfl⟩ : syracuseStep 3792923 = 5689385) B5689385
theorem B16187809 : Blo 1684042 16187809 := bstep (se 2 (by rfl) ⟨6070428, by rfl⟩ : syracuseStep 16187809 = 12140857) B12140857
theorem B3793535 : Blo 1684042 3793535 := bstep (se 1 (by rfl) ⟨2845151, by rfl⟩ : syracuseStep 3793535 = 5690303) B5690303
theorem B12485549 : Blo 1684042 12485549 := bstep (se 3 (by rfl) ⟨2341040, by rfl⟩ : syracuseStep 12485549 = 4682081) B4682081
theorem B43197623 : Blo 1684042 43197623 := bstep (se 1 (by rfl) ⟨32398217, by rfl⟩ : syracuseStep 43197623 = 64796435) B64796435
theorem B2843903 : Blo 1684042 2843903 := bstep (se 1 (by rfl) ⟨2132927, by rfl⟩ : syracuseStep 2843903 = 4265855) B4265855
theorem B20489543 : Blo 1684042 20489543 := bstep (se 1 (by rfl) ⟨15367157, by rfl⟩ : syracuseStep 20489543 = 30734315) B30734315
theorem B82012499 : Blo 1684042 82012499 := bstep (se 1 (by rfl) ⟨61509374, by rfl⟩ : syracuseStep 82012499 = 123018749) B123018749
theorem B72862091 : Blo 1684042 72862091 := bstep (se 1 (by rfl) ⟨54646568, by rfl⟩ : syracuseStep 72862091 = 109293137) B109293137
theorem B9112175 : Blo 1684042 9112175 := bstep (se 1 (by rfl) ⟨6834131, by rfl⟩ : syracuseStep 9112175 = 13668263) B13668263
theorem B9595691 : Blo 1684042 9595691 := bstep (se 1 (by rfl) ⟨7196768, by rfl⟩ : syracuseStep 9595691 = 14393537) B14393537
theorem B2526143 : Blo 1684042 2526143 := bstep (se 1 (by rfl) ⟨1894607, by rfl⟩ : syracuseStep 2526143 = 3789215) B3789215
theorem B2526311 : Blo 1684042 2526311 := bstep (se 1 (by rfl) ⟨1894733, by rfl⟩ : syracuseStep 2526311 = 3789467) B3789467
theorem B3599615 : Blo 1684042 3599615 := bstep (se 1 (by rfl) ⟨2699711, by rfl⟩ : syracuseStep 3599615 = 5399423) B5399423
theorem B10801025 : Blo 1684042 10801025 := bstep (se 2 (by rfl) ⟨4050384, by rfl⟩ : syracuseStep 10801025 = 8100769) B8100769
theorem B2527145 : Blo 1684042 2527145 := bstep (se 2 (by rfl) ⟨947679, by rfl⟩ : syracuseStep 2527145 = 1895359) B1895359
theorem B6828551 : Blo 1684042 6828551 := bstep (se 1 (by rfl) ⟨5121413, by rfl⟩ : syracuseStep 6828551 = 10242827) B10242827
theorem B1684123 : Blo 1684042 1684123 := bstep (se 1 (by rfl) ⟨1263092, by rfl⟩ : syracuseStep 1684123 = 2526185) B2526185
theorem B2528027 : Blo 1684042 2528027 := bstep (se 1 (by rfl) ⟨1896020, by rfl⟩ : syracuseStep 2528027 = 3792041) B3792041
theorem B1685095 : Blo 1684042 1685095 := bstep (se 1 (by rfl) ⟨1263821, by rfl⟩ : syracuseStep 1685095 = 2527643) B2527643
theorem B2528975 : Blo 1684042 2528975 := bstep (se 1 (by rfl) ⟨1896731, by rfl⟩ : syracuseStep 2528975 = 3793463) B3793463
theorem B1685247 : Blo 1684042 1685247 := bstep (se 1 (by rfl) ⟨1263935, by rfl⟩ : syracuseStep 1685247 = 2527871) B2527871
theorem B1685375 : Blo 1684042 1685375 := bstep (se 1 (by rfl) ⟨1264031, by rfl⟩ : syracuseStep 1685375 = 2528063) B2528063
theorem B28776545 : Blo 1684042 28776545 := bstep (se 2 (by rfl) ⟨10791204, by rfl⟩ : syracuseStep 28776545 = 21582409) B21582409
theorem B6830497 : Blo 1684042 6830497 := bstep (se 2 (by rfl) ⟨2561436, by rfl⟩ : syracuseStep 6830497 = 5122873) B5122873
theorem B1685999 : Blo 1684042 1685999 := bstep (se 1 (by rfl) ⟨1264499, by rfl⟩ : syracuseStep 1685999 = 2528999) B2528999
theorem B3791519 : Blo 1684042 3791519 := bstep (se 1 (by rfl) ⟨2843639, by rfl⟩ : syracuseStep 3791519 = 5687279) B5687279
theorem B2734975 : Blo 1684042 2734975 := bstep (se 1 (by rfl) ⟨2051231, by rfl⟩ : syracuseStep 2734975 = 4102463) B4102463
theorem B31161347 : Blo 1684042 31161347 := bstep (se 1 (by rfl) ⟨23371010, by rfl⟩ : syracuseStep 31161347 = 46742021) B46742021
theorem B14400575 : Blo 1684042 14400575 := bstep (se 1 (by rfl) ⟨10800431, by rfl⟩ : syracuseStep 14400575 = 21600863) B21600863
theorem B69156017 : Blo 1684042 69156017 := bstep (se 2 (by rfl) ⟨25933506, by rfl⟩ : syracuseStep 69156017 = 51867013) B51867013
theorem B8527031 : Blo 1684042 8527031 := bstep (se 1 (by rfl) ⟨6395273, by rfl⟩ : syracuseStep 8527031 = 12790547) B12790547
theorem B55385297 : Blo 1684042 55385297 := bstep (se 2 (by rfl) ⟨20769486, by rfl⟩ : syracuseStep 55385297 = 41538973) B41538973
theorem B4800055 : Blo 1684042 4800055 := bstep (se 1 (by rfl) ⟨3600041, by rfl⟩ : syracuseStep 4800055 = 7200083) B7200083
theorem B30736219 : Blo 1684042 30736219 := bstep (se 1 (by rfl) ⟨23052164, by rfl⟩ : syracuseStep 30736219 = 46104329) B46104329
theorem B17530913 : Blo 1684042 17530913 := bstep (se 2 (by rfl) ⟨6574092, by rfl⟩ : syracuseStep 17530913 = 13148185) B13148185
theorem B3646633 : Blo 1684042 3646633 := bstep (se 2 (by rfl) ⟨1367487, by rfl⟩ : syracuseStep 3646633 = 2734975) B2734975
theorem B54674999 : Blo 1684042 54674999 := bstep (se 1 (by rfl) ⟨41006249, by rfl⟩ : syracuseStep 54674999 = 82012499) B82012499
theorem B6400073 : Blo 1684042 6400073 := bstep (se 2 (by rfl) ⟨2400027, by rfl⟩ : syracuseStep 6400073 = 4800055) B4800055
theorem B36923531 : Blo 1684042 36923531 := bstep (se 1 (by rfl) ⟨27692648, by rfl⟩ : syracuseStep 36923531 = 55385297) B55385297
theorem B33294797 : Blo 1684042 33294797 := bstep (se 3 (by rfl) ⟨6242774, by rfl⟩ : syracuseStep 33294797 = 12485549) B12485549
theorem B28798415 : Blo 1684042 28798415 := bstep (se 1 (by rfl) ⟨21598811, by rfl⟩ : syracuseStep 28798415 = 43197623) B43197623
theorem B1895935 : Blo 1684042 1895935 := bstep (se 1 (by rfl) ⟨1421951, by rfl⟩ : syracuseStep 1895935 = 2843903) B2843903
theorem B13659695 : Blo 1684042 13659695 := bstep (se 1 (by rfl) ⟨10244771, by rfl⟩ : syracuseStep 13659695 = 20489543) B20489543
theorem B48574727 : Blo 1684042 48574727 := bstep (se 1 (by rfl) ⟨36431045, by rfl⟩ : syracuseStep 48574727 = 72862091) B72862091
theorem B6074783 : Blo 1684042 6074783 := bstep (se 1 (by rfl) ⟨4556087, by rfl⟩ : syracuseStep 6074783 = 9112175) B9112175
theorem B2527679 : Blo 1684042 2527679 := bstep (se 1 (by rfl) ⟨1895759, by rfl⟩ : syracuseStep 2527679 = 3791519) B3791519
theorem B1684095 : Blo 1684042 1684095 := bstep (se 1 (by rfl) ⟨1263071, by rfl⟩ : syracuseStep 1684095 = 2526143) B2526143
theorem B1684207 : Blo 1684042 1684207 := bstep (se 1 (by rfl) ⟨1263155, by rfl⟩ : syracuseStep 1684207 = 2526311) B2526311
theorem B40981625 : Blo 1684042 40981625 := bstep (se 2 (by rfl) ⟨15368109, by rfl⟩ : syracuseStep 40981625 = 30736219) B30736219
theorem B1684763 : Blo 1684042 1684763 := bstep (se 1 (by rfl) ⟨1263572, by rfl⟩ : syracuseStep 1684763 = 2527145) B2527145
theorem B2528615 : Blo 1684042 2528615 := bstep (se 1 (by rfl) ⟨1896461, by rfl⟩ : syracuseStep 2528615 = 3792923) B3792923
theorem B4552367 : Blo 1684042 4552367 := bstep (se 1 (by rfl) ⟨3414275, by rfl⟩ : syracuseStep 4552367 = 6828551) B6828551
theorem B2529023 : Blo 1684042 2529023 := bstep (se 1 (by rfl) ⟨1896767, by rfl⟩ : syracuseStep 2529023 = 3793535) B3793535
theorem B1685351 : Blo 1684042 1685351 := bstep (se 1 (by rfl) ⟨1264013, by rfl⟩ : syracuseStep 1685351 = 2528027) B2528027
theorem B21583745 : Blo 1684042 21583745 := bstep (se 2 (by rfl) ⟨8093904, by rfl⟩ : syracuseStep 21583745 = 16187809) B16187809
theorem B9107329 : Blo 1684042 9107329 := bstep (se 2 (by rfl) ⟨3415248, by rfl⟩ : syracuseStep 9107329 = 6830497) B6830497
theorem B1685983 : Blo 1684042 1685983 := bstep (se 1 (by rfl) ⟨1264487, by rfl⟩ : syracuseStep 1685983 = 2528975) B2528975
theorem B19184363 : Blo 1684042 19184363 := bstep (se 1 (by rfl) ⟨14388272, by rfl⟩ : syracuseStep 19184363 = 28776545) B28776545
theorem B6397127 : Blo 1684042 6397127 := bstep (se 1 (by rfl) ⟨4797845, by rfl⟩ : syracuseStep 6397127 = 9595691) B9595691
theorem B20774231 : Blo 1684042 20774231 := bstep (se 1 (by rfl) ⟨15580673, by rfl⟩ : syracuseStep 20774231 = 31161347) B31161347
theorem B9600383 : Blo 1684042 9600383 := bstep (se 1 (by rfl) ⟨7200287, by rfl⟩ : syracuseStep 9600383 = 14400575) B14400575
theorem B46104011 : Blo 1684042 46104011 := bstep (se 1 (by rfl) ⟨34578008, by rfl⟩ : syracuseStep 46104011 = 69156017) B69156017
theorem B5684687 : Blo 1684042 5684687 := bstep (se 1 (by rfl) ⟨4263515, by rfl⟩ : syracuseStep 5684687 = 8527031) B8527031
theorem B2399743 : Blo 1684042 2399743 := bstep (se 1 (by rfl) ⟨1799807, by rfl⟩ : syracuseStep 2399743 = 3599615) B3599615
theorem B7200683 : Blo 1684042 7200683 := bstep (se 1 (by rfl) ⟨5400512, by rfl⟩ : syracuseStep 7200683 = 10801025) B10801025
theorem B32383151 : Blo 1684042 32383151 := bstep (se 1 (by rfl) ⟨24287363, by rfl⟩ : syracuseStep 32383151 = 48574727) B48574727
theorem B27321083 : Blo 1684042 27321083 := bstep (se 1 (by rfl) ⟨20490812, by rfl⟩ : syracuseStep 27321083 = 40981625) B40981625
theorem B12789575 : Blo 1684042 12789575 := bstep (se 1 (by rfl) ⟨9592181, by rfl⟩ : syracuseStep 12789575 = 19184363) B19184363
theorem B6400255 : Blo 1684042 6400255 := bstep (se 1 (by rfl) ⟨4800191, by rfl⟩ : syracuseStep 6400255 = 9600383) B9600383
theorem B12143105 : Blo 1684042 12143105 := bstep (se 2 (by rfl) ⟨4553664, by rfl⟩ : syracuseStep 12143105 = 9107329) B9107329
theorem B19198943 : Blo 1684042 19198943 := bstep (se 1 (by rfl) ⟨14399207, by rfl⟩ : syracuseStep 19198943 = 28798415) B28798415
theorem B4049855 : Blo 1684042 4049855 := bstep (se 1 (by rfl) ⟨3037391, by rfl⟩ : syracuseStep 4049855 = 6074783) B6074783
theorem B98462749 : Blo 1684042 98462749 := bstep (se 3 (by rfl) ⟨18461765, by rfl⟩ : syracuseStep 98462749 = 36923531) B36923531
theorem B36449999 : Blo 1684042 36449999 := bstep (se 1 (by rfl) ⟨27337499, by rfl⟩ : syracuseStep 36449999 = 54674999) B54674999
theorem B14389163 : Blo 1684042 14389163 := bstep (se 1 (by rfl) ⟨10791872, by rfl⟩ : syracuseStep 14389163 = 21583745) B21583745
theorem B4862177 : Blo 1684042 4862177 := bstep (se 2 (by rfl) ⟨1823316, by rfl⟩ : syracuseStep 4862177 = 3646633) B3646633
theorem B22196531 : Blo 1684042 22196531 := bstep (se 1 (by rfl) ⟨16647398, by rfl⟩ : syracuseStep 22196531 = 33294797) B33294797
theorem B2527913 : Blo 1684042 2527913 := bstep (se 2 (by rfl) ⟨947967, by rfl⟩ : syracuseStep 2527913 = 1895935) B1895935
theorem B3199657 : Blo 1684042 3199657 := bstep (se 2 (by rfl) ⟨1199871, by rfl⟩ : syracuseStep 3199657 = 2399743) B2399743
theorem B4264751 : Blo 1684042 4264751 := bstep (se 1 (by rfl) ⟨3198563, by rfl⟩ : syracuseStep 4264751 = 6397127) B6397127
theorem B13849487 : Blo 1684042 13849487 := bstep (se 1 (by rfl) ⟨10387115, by rfl⟩ : syracuseStep 13849487 = 20774231) B20774231
theorem B3789791 : Blo 1684042 3789791 := bstep (se 1 (by rfl) ⟨2842343, by rfl⟩ : syracuseStep 3789791 = 5684687) B5684687
theorem B9106463 : Blo 1684042 9106463 := bstep (se 1 (by rfl) ⟨6829847, by rfl⟩ : syracuseStep 9106463 = 13659695) B13659695
theorem B11687275 : Blo 1684042 11687275 := bstep (se 1 (by rfl) ⟨8765456, by rfl⟩ : syracuseStep 11687275 = 17530913) B17530913
theorem B1685119 : Blo 1684042 1685119 := bstep (se 1 (by rfl) ⟨1263839, by rfl⟩ : syracuseStep 1685119 = 2527679) B2527679
theorem B1685743 : Blo 1684042 1685743 := bstep (se 1 (by rfl) ⟨1264307, by rfl⟩ : syracuseStep 1685743 = 2528615) B2528615
theorem B1686015 : Blo 1684042 1686015 := bstep (se 1 (by rfl) ⟨1264511, by rfl⟩ : syracuseStep 1686015 = 2529023) B2529023
theorem B4266715 : Blo 1684042 4266715 := bstep (se 1 (by rfl) ⟨3200036, by rfl⟩ : syracuseStep 4266715 = 6400073) B6400073
theorem B12139645 : Blo 1684042 12139645 := bstep (se 3 (by rfl) ⟨2276183, by rfl⟩ : syracuseStep 12139645 = 4552367) B4552367
theorem B30736007 : Blo 1684042 30736007 := bstep (se 1 (by rfl) ⟨23052005, by rfl⟩ : syracuseStep 30736007 = 46104011) B46104011
theorem B4800455 : Blo 1684042 4800455 := bstep (se 1 (by rfl) ⟨3600341, by rfl⟩ : syracuseStep 4800455 = 7200683) B7200683
theorem B2843167 : Blo 1684042 2843167 := bstep (se 1 (by rfl) ⟨2132375, by rfl⟩ : syracuseStep 2843167 = 4264751) B4264751
theorem B9232991 : Blo 1684042 9232991 := bstep (se 1 (by rfl) ⟨6924743, by rfl⟩ : syracuseStep 9232991 = 13849487) B13849487
theorem B8095403 : Blo 1684042 8095403 := bstep (se 1 (by rfl) ⟨6071552, by rfl⟩ : syracuseStep 8095403 = 12143105) B12143105
theorem B15583033 : Blo 1684042 15583033 := bstep (se 2 (by rfl) ⟨5843637, by rfl⟩ : syracuseStep 15583033 = 11687275) B11687275
theorem B20490671 : Blo 1684042 20490671 := bstep (se 1 (by rfl) ⟨15368003, by rfl⟩ : syracuseStep 20490671 = 30736007) B30736007
theorem B24299999 : Blo 1684042 24299999 := bstep (se 1 (by rfl) ⟨18224999, by rfl⟩ : syracuseStep 24299999 = 36449999) B36449999
theorem B24283901 : Blo 1684042 24283901 := bstep (se 3 (by rfl) ⟨4553231, by rfl⟩ : syracuseStep 24283901 = 9106463) B9106463
theorem B21588767 : Blo 1684042 21588767 := bstep (se 1 (by rfl) ⟨16191575, by rfl⟩ : syracuseStep 21588767 = 32383151) B32383151
theorem B14797687 : Blo 1684042 14797687 := bstep (se 1 (by rfl) ⟨11098265, by rfl⟩ : syracuseStep 14797687 = 22196531) B22196531
theorem B18214055 : Blo 1684042 18214055 := bstep (se 1 (by rfl) ⟨13660541, by rfl⟩ : syracuseStep 18214055 = 27321083) B27321083
theorem B2526527 : Blo 1684042 2526527 := bstep (se 1 (by rfl) ⟨1894895, by rfl⟩ : syracuseStep 2526527 = 3789791) B3789791
theorem B12799295 : Blo 1684042 12799295 := bstep (se 1 (by rfl) ⟨9599471, by rfl⟩ : syracuseStep 12799295 = 19198943) B19198943
theorem B5688953 : Blo 1684042 5688953 := bstep (se 2 (by rfl) ⟨2133357, by rfl⟩ : syracuseStep 5688953 = 4266715) B4266715
theorem B2699903 : Blo 1684042 2699903 := bstep (se 1 (by rfl) ⟨2024927, by rfl⟩ : syracuseStep 2699903 = 4049855) B4049855
theorem B3200303 : Blo 1684042 3200303 := bstep (se 1 (by rfl) ⟨2400227, by rfl⟩ : syracuseStep 3200303 = 4800455) B4800455
theorem B3241451 : Blo 1684042 3241451 := bstep (se 1 (by rfl) ⟨2431088, by rfl⟩ : syracuseStep 3241451 = 4862177) B4862177
theorem B8533673 : Blo 1684042 8533673 := bstep (se 2 (by rfl) ⟨3200127, by rfl⟩ : syracuseStep 8533673 = 6400255) B6400255
theorem B1685275 : Blo 1684042 1685275 := bstep (se 1 (by rfl) ⟨1263956, by rfl⟩ : syracuseStep 1685275 = 2527913) B2527913
theorem B4266209 : Blo 1684042 4266209 := bstep (se 2 (by rfl) ⟨1599828, by rfl⟩ : syracuseStep 4266209 = 3199657) B3199657
theorem B8526383 : Blo 1684042 8526383 := bstep (se 1 (by rfl) ⟨6394787, by rfl⟩ : syracuseStep 8526383 = 12789575) B12789575
theorem B131283665 : Blo 1684042 131283665 := bstep (se 2 (by rfl) ⟨49231374, by rfl⟩ : syracuseStep 131283665 = 98462749) B98462749
theorem B16186193 : Blo 1684042 16186193 := bstep (se 2 (by rfl) ⟨6069822, by rfl⟩ : syracuseStep 16186193 = 12139645) B12139645
theorem B9592775 : Blo 1684042 9592775 := bstep (se 1 (by rfl) ⟨7194581, by rfl⟩ : syracuseStep 9592775 = 14389163) B14389163
theorem B2844139 : Blo 1684042 2844139 := bstep (se 1 (by rfl) ⟨2133104, by rfl⟩ : syracuseStep 2844139 = 4266209) B4266209
theorem B83109509 : Blo 1684042 83109509 := bstep (se 4 (by rfl) ⟨7791516, by rfl⟩ : syracuseStep 83109509 = 15583033) B15583033
theorem B21587741 : Blo 1684042 21587741 := bstep (se 3 (by rfl) ⟨4047701, by rfl⟩ : syracuseStep 21587741 = 8095403) B8095403
theorem B10790795 : Blo 1684042 10790795 := bstep (se 1 (by rfl) ⟨8093096, by rfl⟩ : syracuseStep 10790795 = 16186193) B16186193
theorem B12142703 : Blo 1684042 12142703 := bstep (se 1 (by rfl) ⟨9107027, by rfl⟩ : syracuseStep 12142703 = 18214055) B18214055
theorem B6155327 : Blo 1684042 6155327 := bstep (se 1 (by rfl) ⟨4616495, by rfl⟩ : syracuseStep 6155327 = 9232991) B9232991
theorem B2133535 : Blo 1684042 2133535 := bstep (se 1 (by rfl) ⟨1600151, by rfl⟩ : syracuseStep 2133535 = 3200303) B3200303
theorem B5689115 : Blo 1684042 5689115 := bstep (se 1 (by rfl) ⟨4266836, by rfl⟩ : syracuseStep 5689115 = 8533673) B8533673
theorem B19730249 : Blo 1684042 19730249 := bstep (se 2 (by rfl) ⟨7398843, by rfl⟩ : syracuseStep 19730249 = 14797687) B14797687
theorem B13660447 : Blo 1684042 13660447 := bstep (se 1 (by rfl) ⟨10245335, by rfl⟩ : syracuseStep 13660447 = 20490671) B20490671
theorem B16199999 : Blo 1684042 16199999 := bstep (se 1 (by rfl) ⟨12149999, by rfl⟩ : syracuseStep 16199999 = 24299999) B24299999
theorem B1684351 : Blo 1684042 1684351 := bstep (se 1 (by rfl) ⟨1263263, by rfl⟩ : syracuseStep 1684351 = 2526527) B2526527
theorem B8532863 : Blo 1684042 8532863 := bstep (se 1 (by rfl) ⟨6399647, by rfl⟩ : syracuseStep 8532863 = 12799295) B12799295
theorem B6395183 : Blo 1684042 6395183 := bstep (se 1 (by rfl) ⟨4796387, by rfl⟩ : syracuseStep 6395183 = 9592775) B9592775
theorem B3790889 : Blo 1684042 3790889 := bstep (se 2 (by rfl) ⟨1421583, by rfl⟩ : syracuseStep 3790889 = 2843167) B2843167
theorem B2160967 : Blo 1684042 2160967 := bstep (se 1 (by rfl) ⟨1620725, by rfl⟩ : syracuseStep 2160967 = 3241451) B3241451
theorem B7199741 : Blo 1684042 7199741 := bstep (se 3 (by rfl) ⟨1349951, by rfl⟩ : syracuseStep 7199741 = 2699903) B2699903
theorem B5684255 : Blo 1684042 5684255 := bstep (se 1 (by rfl) ⟨4263191, by rfl⟩ : syracuseStep 5684255 = 8526383) B8526383
theorem B87522443 : Blo 1684042 87522443 := bstep (se 1 (by rfl) ⟨65641832, by rfl⟩ : syracuseStep 87522443 = 131283665) B131283665
theorem B14392511 : Blo 1684042 14392511 := bstep (se 1 (by rfl) ⟨10794383, by rfl⟩ : syracuseStep 14392511 = 21588767) B21588767
theorem B64757069 : Blo 1684042 64757069 := bstep (se 3 (by rfl) ⟨12141950, by rfl⟩ : syracuseStep 64757069 = 24283901) B24283901
theorem B3792635 : Blo 1684042 3792635 := bstep (se 1 (by rfl) ⟨2844476, by rfl⟩ : syracuseStep 3792635 = 5688953) B5688953
theorem B7193863 : Blo 1684042 7193863 := bstep (se 1 (by rfl) ⟨5395397, by rfl⟩ : syracuseStep 7193863 = 10790795) B10790795
theorem B8095135 : Blo 1684042 8095135 := bstep (se 1 (by rfl) ⟨6071351, by rfl⟩ : syracuseStep 8095135 = 12142703) B12142703
theorem B2844713 : Blo 1684042 2844713 := bstep (se 2 (by rfl) ⟨1066767, by rfl⟩ : syracuseStep 2844713 = 2133535) B2133535
theorem B9595007 : Blo 1684042 9595007 := bstep (se 1 (by rfl) ⟨7196255, by rfl⟩ : syracuseStep 9595007 = 14392511) B14392511
theorem B10799999 : Blo 1684042 10799999 := bstep (se 1 (by rfl) ⟨8099999, by rfl⟩ : syracuseStep 10799999 = 16199999) B16199999
theorem B18213929 : Blo 1684042 18213929 := bstep (se 2 (by rfl) ⟨6830223, by rfl⟩ : syracuseStep 18213929 = 13660447) B13660447
theorem B5688575 : Blo 1684042 5688575 := bstep (se 1 (by rfl) ⟨4266431, by rfl⟩ : syracuseStep 5688575 = 8532863) B8532863
theorem B4263455 : Blo 1684042 4263455 := bstep (se 1 (by rfl) ⟨3197591, by rfl⟩ : syracuseStep 4263455 = 6395183) B6395183
theorem B55406339 : Blo 1684042 55406339 := bstep (se 1 (by rfl) ⟨41554754, by rfl⟩ : syracuseStep 55406339 = 83109509) B83109509
theorem B2527259 : Blo 1684042 2527259 := bstep (se 1 (by rfl) ⟨1895444, by rfl⟩ : syracuseStep 2527259 = 3790889) B3790889
theorem B3789503 : Blo 1684042 3789503 := bstep (se 1 (by rfl) ⟨2842127, by rfl⟩ : syracuseStep 3789503 = 5684255) B5684255
theorem B58348295 : Blo 1684042 58348295 := bstep (se 1 (by rfl) ⟨43761221, by rfl⟩ : syracuseStep 58348295 = 87522443) B87522443
theorem B2528423 : Blo 1684042 2528423 := bstep (se 1 (by rfl) ⟨1896317, by rfl⟩ : syracuseStep 2528423 = 3792635) B3792635
theorem B13153499 : Blo 1684042 13153499 := bstep (se 1 (by rfl) ⟨9865124, by rfl⟩ : syracuseStep 13153499 = 19730249) B19730249
theorem B2881289 : Blo 1684042 2881289 := bstep (se 2 (by rfl) ⟨1080483, by rfl⟩ : syracuseStep 2881289 = 2160967) B2160967
theorem B14391827 : Blo 1684042 14391827 := bstep (se 1 (by rfl) ⟨10793870, by rfl⟩ : syracuseStep 14391827 = 21587741) B21587741
theorem B3792185 : Blo 1684042 3792185 := bstep (se 2 (by rfl) ⟨1422069, by rfl⟩ : syracuseStep 3792185 = 2844139) B2844139
theorem B4799827 : Blo 1684042 4799827 := bstep (se 1 (by rfl) ⟨3599870, by rfl⟩ : syracuseStep 4799827 = 7199741) B7199741
theorem B4103551 : Blo 1684042 4103551 := bstep (se 1 (by rfl) ⟨3077663, by rfl⟩ : syracuseStep 4103551 = 6155327) B6155327
theorem B43171379 : Blo 1684042 43171379 := bstep (se 1 (by rfl) ⟨32378534, by rfl⟩ : syracuseStep 43171379 = 64757069) B64757069
theorem B3792743 : Blo 1684042 3792743 := bstep (se 1 (by rfl) ⟨2844557, by rfl⟩ : syracuseStep 3792743 = 5689115) B5689115
theorem B9594551 : Blo 1684042 9594551 := bstep (se 1 (by rfl) ⟨7195913, by rfl⟩ : syracuseStep 9594551 = 14391827) B14391827
theorem B6399769 : Blo 1684042 6399769 := bstep (se 2 (by rfl) ⟨2399913, by rfl⟩ : syracuseStep 6399769 = 4799827) B4799827
theorem B12142619 : Blo 1684042 12142619 := bstep (se 1 (by rfl) ⟨9106964, by rfl⟩ : syracuseStep 12142619 = 18213929) B18213929
theorem B28780919 : Blo 1684042 28780919 := bstep (se 1 (by rfl) ⟨21585689, by rfl⟩ : syracuseStep 28780919 = 43171379) B43171379
theorem B2526335 : Blo 1684042 2526335 := bstep (se 1 (by rfl) ⟨1894751, by rfl⟩ : syracuseStep 2526335 = 3789503) B3789503
theorem B38898863 : Blo 1684042 38898863 := bstep (se 1 (by rfl) ⟨29174147, by rfl⟩ : syracuseStep 38898863 = 58348295) B58348295
theorem B8768999 : Blo 1684042 8768999 := bstep (se 1 (by rfl) ⟨6576749, by rfl⟩ : syracuseStep 8768999 = 13153499) B13153499
theorem B1896475 : Blo 1684042 1896475 := bstep (se 1 (by rfl) ⟨1422356, by rfl⟩ : syracuseStep 1896475 = 2844713) B2844713
theorem B10793513 : Blo 1684042 10793513 := bstep (se 2 (by rfl) ⟨4047567, by rfl⟩ : syracuseStep 10793513 = 8095135) B8095135
theorem B2528123 : Blo 1684042 2528123 := bstep (se 1 (by rfl) ⟨1896092, by rfl⟩ : syracuseStep 2528123 = 3792185) B3792185
theorem B2528495 : Blo 1684042 2528495 := bstep (se 1 (by rfl) ⟨1896371, by rfl⟩ : syracuseStep 2528495 = 3792743) B3792743
theorem B1684839 : Blo 1684042 1684839 := bstep (se 1 (by rfl) ⟨1263629, by rfl⟩ : syracuseStep 1684839 = 2527259) B2527259
theorem B1685615 : Blo 1684042 1685615 := bstep (se 1 (by rfl) ⟨1264211, by rfl⟩ : syracuseStep 1685615 = 2528423) B2528423
theorem B6396671 : Blo 1684042 6396671 := bstep (se 1 (by rfl) ⟨4797503, by rfl⟩ : syracuseStep 6396671 = 9595007) B9595007
theorem B9591817 : Blo 1684042 9591817 := bstep (se 2 (by rfl) ⟨3596931, by rfl⟩ : syracuseStep 9591817 = 7193863) B7193863
theorem B5471401 : Blo 1684042 5471401 := bstep (se 2 (by rfl) ⟨2051775, by rfl⟩ : syracuseStep 5471401 = 4103551) B4103551
theorem B7199999 : Blo 1684042 7199999 := bstep (se 1 (by rfl) ⟨5399999, by rfl⟩ : syracuseStep 7199999 = 10799999) B10799999
theorem B7683437 : Blo 1684042 7683437 := bstep (se 3 (by rfl) ⟨1440644, by rfl⟩ : syracuseStep 7683437 = 2881289) B2881289
theorem B3792383 : Blo 1684042 3792383 := bstep (se 1 (by rfl) ⟨2844287, by rfl⟩ : syracuseStep 3792383 = 5688575) B5688575
theorem B2842303 : Blo 1684042 2842303 := bstep (se 1 (by rfl) ⟨2131727, by rfl⟩ : syracuseStep 2842303 = 4263455) B4263455
theorem B36937559 : Blo 1684042 36937559 := bstep (se 1 (by rfl) ⟨27703169, by rfl⟩ : syracuseStep 36937559 = 55406339) B55406339
theorem B12789089 : Blo 1684042 12789089 := bstep (se 2 (by rfl) ⟨4795908, by rfl⟩ : syracuseStep 12789089 = 9591817) B9591817
theorem B8095079 : Blo 1684042 8095079 := bstep (se 1 (by rfl) ⟨6071309, by rfl⟩ : syracuseStep 8095079 = 12142619) B12142619
theorem B19187279 : Blo 1684042 19187279 := bstep (se 1 (by rfl) ⟨14390459, by rfl⟩ : syracuseStep 19187279 = 28780919) B28780919
theorem B5122291 : Blo 1684042 5122291 := bstep (se 1 (by rfl) ⟨3841718, by rfl⟩ : syracuseStep 5122291 = 7683437) B7683437
theorem B7195675 : Blo 1684042 7195675 := bstep (se 1 (by rfl) ⟨5396756, by rfl⟩ : syracuseStep 7195675 = 10793513) B10793513
theorem B23383997 : Blo 1684042 23383997 := bstep (se 3 (by rfl) ⟨4384499, by rfl⟩ : syracuseStep 23383997 = 8768999) B8768999
theorem B7295201 : Blo 1684042 7295201 := bstep (se 2 (by rfl) ⟨2735700, by rfl⟩ : syracuseStep 7295201 = 5471401) B5471401
theorem B4264447 : Blo 1684042 4264447 := bstep (se 1 (by rfl) ⟨3198335, by rfl⟩ : syracuseStep 4264447 = 6396671) B6396671
theorem B1684223 : Blo 1684042 1684223 := bstep (se 1 (by rfl) ⟨1263167, by rfl⟩ : syracuseStep 1684223 = 2526335) B2526335
theorem B25932575 : Blo 1684042 25932575 := bstep (se 1 (by rfl) ⟨19449431, by rfl⟩ : syracuseStep 25932575 = 38898863) B38898863
theorem B3789737 : Blo 1684042 3789737 := bstep (se 2 (by rfl) ⟨1421151, by rfl⟩ : syracuseStep 3789737 = 2842303) B2842303
theorem B2528255 : Blo 1684042 2528255 := bstep (se 1 (by rfl) ⟨1896191, by rfl⟩ : syracuseStep 2528255 = 3792383) B3792383
theorem B8533025 : Blo 1684042 8533025 := bstep (se 2 (by rfl) ⟨3199884, by rfl⟩ : syracuseStep 8533025 = 6399769) B6399769
theorem B2528633 : Blo 1684042 2528633 := bstep (se 2 (by rfl) ⟨948237, by rfl⟩ : syracuseStep 2528633 = 1896475) B1896475
theorem B1685415 : Blo 1684042 1685415 := bstep (se 1 (by rfl) ⟨1264061, by rfl⟩ : syracuseStep 1685415 = 2528123) B2528123
theorem B1685663 : Blo 1684042 1685663 := bstep (se 1 (by rfl) ⟨1264247, by rfl⟩ : syracuseStep 1685663 = 2528495) B2528495
theorem B6396367 : Blo 1684042 6396367 := bstep (se 1 (by rfl) ⟨4797275, by rfl⟩ : syracuseStep 6396367 = 9594551) B9594551
theorem B4799999 : Blo 1684042 4799999 := bstep (se 1 (by rfl) ⟨3599999, by rfl⟩ : syracuseStep 4799999 = 7199999) B7199999
theorem B98500157 : Blo 1684042 98500157 := bstep (se 3 (by rfl) ⟨18468779, by rfl⟩ : syracuseStep 98500157 = 36937559) B36937559
theorem B8528489 : Blo 1684042 8528489 := bstep (se 2 (by rfl) ⟨3198183, by rfl⟩ : syracuseStep 8528489 = 6396367) B6396367
theorem B5685929 : Blo 1684042 5685929 := bstep (se 2 (by rfl) ⟨2132223, by rfl⟩ : syracuseStep 5685929 = 4264447) B4264447
theorem B9594233 : Blo 1684042 9594233 := bstep (se 2 (by rfl) ⟨3597837, by rfl⟩ : syracuseStep 9594233 = 7195675) B7195675
theorem B2526491 : Blo 1684042 2526491 := bstep (se 1 (by rfl) ⟨1894868, by rfl⟩ : syracuseStep 2526491 = 3789737) B3789737
theorem B5688683 : Blo 1684042 5688683 := bstep (se 1 (by rfl) ⟨4266512, by rfl⟩ : syracuseStep 5688683 = 8533025) B8533025
theorem B12791519 : Blo 1684042 12791519 := bstep (se 1 (by rfl) ⟨9593639, by rfl⟩ : syracuseStep 12791519 = 19187279) B19187279
theorem B69153533 : Blo 1684042 69153533 := bstep (se 3 (by rfl) ⟨12966287, by rfl⟩ : syracuseStep 69153533 = 25932575) B25932575
theorem B3199999 : Blo 1684042 3199999 := bstep (se 1 (by rfl) ⟨2399999, by rfl⟩ : syracuseStep 3199999 = 4799999) B4799999
theorem B4863467 : Blo 1684042 4863467 := bstep (se 1 (by rfl) ⟨3647600, by rfl⟩ : syracuseStep 4863467 = 7295201) B7295201
theorem B6829721 : Blo 1684042 6829721 := bstep (se 2 (by rfl) ⟨2561145, by rfl⟩ : syracuseStep 6829721 = 5122291) B5122291
theorem B1685503 : Blo 1684042 1685503 := bstep (se 1 (by rfl) ⟨1264127, by rfl⟩ : syracuseStep 1685503 = 2528255) B2528255
theorem B8526059 : Blo 1684042 8526059 := bstep (se 1 (by rfl) ⟨6394544, by rfl⟩ : syracuseStep 8526059 = 12789089) B12789089
theorem B5396719 : Blo 1684042 5396719 := bstep (se 1 (by rfl) ⟨4047539, by rfl⟩ : syracuseStep 5396719 = 8095079) B8095079
theorem B1685755 : Blo 1684042 1685755 := bstep (se 1 (by rfl) ⟨1264316, by rfl⟩ : syracuseStep 1685755 = 2528633) B2528633
theorem B65666771 : Blo 1684042 65666771 := bstep (se 1 (by rfl) ⟨49250078, by rfl⟩ : syracuseStep 65666771 = 98500157) B98500157
theorem B15589331 : Blo 1684042 15589331 := bstep (se 1 (by rfl) ⟨11691998, by rfl⟩ : syracuseStep 15589331 = 23383997) B23383997
theorem B5685659 : Blo 1684042 5685659 := bstep (se 1 (by rfl) ⟨4264244, by rfl⟩ : syracuseStep 5685659 = 8528489) B8528489
theorem B7195625 : Blo 1684042 7195625 := bstep (se 2 (by rfl) ⟨2698359, by rfl⟩ : syracuseStep 7195625 = 5396719) B5396719
theorem B1684327 : Blo 1684042 1684327 := bstep (se 1 (by rfl) ⟨1263245, by rfl⟩ : syracuseStep 1684327 = 2526491) B2526491
theorem B10392887 : Blo 1684042 10392887 := bstep (se 1 (by rfl) ⟨7794665, by rfl⟩ : syracuseStep 10392887 = 15589331) B15589331
theorem B3790619 : Blo 1684042 3790619 := bstep (se 1 (by rfl) ⟨2842964, by rfl⟩ : syracuseStep 3790619 = 5685929) B5685929
theorem B46102355 : Blo 1684042 46102355 := bstep (se 1 (by rfl) ⟨34576766, by rfl⟩ : syracuseStep 46102355 = 69153533) B69153533
theorem B6396155 : Blo 1684042 6396155 := bstep (se 1 (by rfl) ⟨4797116, by rfl⟩ : syracuseStep 6396155 = 9594233) B9594233
theorem B3242311 : Blo 1684042 3242311 := bstep (se 1 (by rfl) ⟨2431733, by rfl⟩ : syracuseStep 3242311 = 4863467) B4863467
theorem B4553147 : Blo 1684042 4553147 := bstep (se 1 (by rfl) ⟨3414860, by rfl⟩ : syracuseStep 4553147 = 6829721) B6829721
theorem B4266665 : Blo 1684042 4266665 := bstep (se 2 (by rfl) ⟨1599999, by rfl⟩ : syracuseStep 4266665 = 3199999) B3199999
theorem B5684039 : Blo 1684042 5684039 := bstep (se 1 (by rfl) ⟨4263029, by rfl⟩ : syracuseStep 5684039 = 8526059) B8526059
theorem B3792455 : Blo 1684042 3792455 := bstep (se 1 (by rfl) ⟨2844341, by rfl⟩ : syracuseStep 3792455 = 5688683) B5688683
theorem B43777847 : Blo 1684042 43777847 := bstep (se 1 (by rfl) ⟨32833385, by rfl⟩ : syracuseStep 43777847 = 65666771) B65666771
theorem B8527679 : Blo 1684042 8527679 := bstep (se 1 (by rfl) ⟨6395759, by rfl⟩ : syracuseStep 8527679 = 12791519) B12791519
theorem B2844443 : Blo 1684042 2844443 := bstep (se 1 (by rfl) ⟨2133332, by rfl⟩ : syracuseStep 2844443 = 4266665) B4266665
theorem B2527079 : Blo 1684042 2527079 := bstep (se 1 (by rfl) ⟨1895309, by rfl⟩ : syracuseStep 2527079 = 3790619) B3790619
theorem B4264103 : Blo 1684042 4264103 := bstep (se 1 (by rfl) ⟨3198077, by rfl⟩ : syracuseStep 4264103 = 6396155) B6396155
theorem B3035431 : Blo 1684042 3035431 := bstep (se 1 (by rfl) ⟨2276573, by rfl⟩ : syracuseStep 3035431 = 4553147) B4553147
theorem B3789359 : Blo 1684042 3789359 := bstep (se 1 (by rfl) ⟨2842019, by rfl⟩ : syracuseStep 3789359 = 5684039) B5684039
theorem B4797083 : Blo 1684042 4797083 := bstep (se 1 (by rfl) ⟨3597812, by rfl⟩ : syracuseStep 4797083 = 7195625) B7195625
theorem B2528303 : Blo 1684042 2528303 := bstep (se 1 (by rfl) ⟨1896227, by rfl⟩ : syracuseStep 2528303 = 3792455) B3792455
theorem B29185231 : Blo 1684042 29185231 := bstep (se 1 (by rfl) ⟨21888923, by rfl⟩ : syracuseStep 29185231 = 43777847) B43777847
theorem B3790439 : Blo 1684042 3790439 := bstep (se 1 (by rfl) ⟨2842829, by rfl⟩ : syracuseStep 3790439 = 5685659) B5685659
theorem B6928591 : Blo 1684042 6928591 := bstep (se 1 (by rfl) ⟨5196443, by rfl⟩ : syracuseStep 6928591 = 10392887) B10392887
theorem B30734903 : Blo 1684042 30734903 := bstep (se 1 (by rfl) ⟨23051177, by rfl⟩ : syracuseStep 30734903 = 46102355) B46102355
theorem B17292325 : Blo 1684042 17292325 := bstep (se 4 (by rfl) ⟨1621155, by rfl⟩ : syracuseStep 17292325 = 3242311) B3242311
theorem B5685119 : Blo 1684042 5685119 := bstep (se 1 (by rfl) ⟨4263839, by rfl⟩ : syracuseStep 5685119 = 8527679) B8527679
theorem B2842735 : Blo 1684042 2842735 := bstep (se 1 (by rfl) ⟨2132051, by rfl⟩ : syracuseStep 2842735 = 4264103) B4264103
theorem B4047241 : Blo 1684042 4047241 := bstep (se 2 (by rfl) ⟨1517715, by rfl⟩ : syracuseStep 4047241 = 3035431) B3035431
theorem B38913641 : Blo 1684042 38913641 := bstep (se 2 (by rfl) ⟨14592615, by rfl⟩ : syracuseStep 38913641 = 29185231) B29185231
theorem B20489935 : Blo 1684042 20489935 := bstep (se 1 (by rfl) ⟨15367451, by rfl⟩ : syracuseStep 20489935 = 30734903) B30734903
theorem B2526239 : Blo 1684042 2526239 := bstep (se 1 (by rfl) ⟨1894679, by rfl⟩ : syracuseStep 2526239 = 3789359) B3789359
theorem B3198055 : Blo 1684042 3198055 := bstep (se 1 (by rfl) ⟨2398541, by rfl⟩ : syracuseStep 3198055 = 4797083) B4797083
theorem B2526959 : Blo 1684042 2526959 := bstep (se 1 (by rfl) ⟨1895219, by rfl⟩ : syracuseStep 2526959 = 3790439) B3790439
theorem B1896295 : Blo 1684042 1896295 := bstep (se 1 (by rfl) ⟨1422221, by rfl⟩ : syracuseStep 1896295 = 2844443) B2844443
theorem B23056433 : Blo 1684042 23056433 := bstep (se 2 (by rfl) ⟨8646162, by rfl⟩ : syracuseStep 23056433 = 17292325) B17292325
theorem B1684719 : Blo 1684042 1684719 := bstep (se 1 (by rfl) ⟨1263539, by rfl⟩ : syracuseStep 1684719 = 2527079) B2527079
theorem B3790079 : Blo 1684042 3790079 := bstep (se 1 (by rfl) ⟨2842559, by rfl⟩ : syracuseStep 3790079 = 5685119) B5685119
theorem B9238121 : Blo 1684042 9238121 := bstep (se 2 (by rfl) ⟨3464295, by rfl⟩ : syracuseStep 9238121 = 6928591) B6928591
theorem B1685535 : Blo 1684042 1685535 := bstep (se 1 (by rfl) ⟨1264151, by rfl⟩ : syracuseStep 1685535 = 2528303) B2528303
theorem B15370955 : Blo 1684042 15370955 := bstep (se 1 (by rfl) ⟨11528216, by rfl⟩ : syracuseStep 15370955 = 23056433) B23056433
theorem B2526719 : Blo 1684042 2526719 := bstep (se 1 (by rfl) ⟨1895039, by rfl⟩ : syracuseStep 2526719 = 3790079) B3790079
theorem B4264073 : Blo 1684042 4264073 := bstep (se 2 (by rfl) ⟨1599027, by rfl⟩ : syracuseStep 4264073 = 3198055) B3198055
theorem B1684159 : Blo 1684042 1684159 := bstep (se 1 (by rfl) ⟨1263119, by rfl⟩ : syracuseStep 1684159 = 2526239) B2526239
theorem B2528393 : Blo 1684042 2528393 := bstep (se 2 (by rfl) ⟨948147, by rfl⟩ : syracuseStep 2528393 = 1896295) B1896295
theorem B1684639 : Blo 1684042 1684639 := bstep (se 1 (by rfl) ⟨1263479, by rfl⟩ : syracuseStep 1684639 = 2526959) B2526959
theorem B3790313 : Blo 1684042 3790313 := bstep (se 2 (by rfl) ⟨1421367, by rfl⟩ : syracuseStep 3790313 = 2842735) B2842735
theorem B5396321 : Blo 1684042 5396321 := bstep (se 2 (by rfl) ⟨2023620, by rfl⟩ : syracuseStep 5396321 = 4047241) B4047241
theorem B25942427 : Blo 1684042 25942427 := bstep (se 1 (by rfl) ⟨19456820, by rfl⟩ : syracuseStep 25942427 = 38913641) B38913641
theorem B6158747 : Blo 1684042 6158747 := bstep (se 1 (by rfl) ⟨4619060, by rfl⟩ : syracuseStep 6158747 = 9238121) B9238121
theorem B27319913 : Blo 1684042 27319913 := bstep (se 2 (by rfl) ⟨10244967, by rfl⟩ : syracuseStep 27319913 = 20489935) B20489935
theorem B2842715 : Blo 1684042 2842715 := bstep (se 1 (by rfl) ⟨2132036, by rfl⟩ : syracuseStep 2842715 = 4264073) B4264073
theorem B3597547 : Blo 1684042 3597547 := bstep (se 1 (by rfl) ⟨2698160, by rfl⟩ : syracuseStep 3597547 = 5396321) B5396321
theorem B17294951 : Blo 1684042 17294951 := bstep (se 1 (by rfl) ⟨12971213, by rfl⟩ : syracuseStep 17294951 = 25942427) B25942427
theorem B4105831 : Blo 1684042 4105831 := bstep (se 1 (by rfl) ⟨3079373, by rfl⟩ : syracuseStep 4105831 = 6158747) B6158747
theorem B18213275 : Blo 1684042 18213275 := bstep (se 1 (by rfl) ⟨13659956, by rfl⟩ : syracuseStep 18213275 = 27319913) B27319913
theorem B2526875 : Blo 1684042 2526875 := bstep (se 1 (by rfl) ⟨1895156, by rfl⟩ : syracuseStep 2526875 = 3790313) B3790313
theorem B1684479 : Blo 1684042 1684479 := bstep (se 1 (by rfl) ⟨1263359, by rfl⟩ : syracuseStep 1684479 = 2526719) B2526719
theorem B1685595 : Blo 1684042 1685595 := bstep (se 1 (by rfl) ⟨1264196, by rfl⟩ : syracuseStep 1685595 = 2528393) B2528393
theorem B10247303 : Blo 1684042 10247303 := bstep (se 1 (by rfl) ⟨7685477, by rfl⟩ : syracuseStep 10247303 = 15370955) B15370955
theorem B12142183 : Blo 1684042 12142183 := bstep (se 1 (by rfl) ⟨9106637, by rfl⟩ : syracuseStep 12142183 = 18213275) B18213275
theorem B5474441 : Blo 1684042 5474441 := bstep (se 2 (by rfl) ⟨2052915, by rfl⟩ : syracuseStep 5474441 = 4105831) B4105831
theorem B1895143 : Blo 1684042 1895143 := bstep (se 1 (by rfl) ⟨1421357, by rfl⟩ : syracuseStep 1895143 = 2842715) B2842715
theorem B11529967 : Blo 1684042 11529967 := bstep (se 1 (by rfl) ⟨8647475, by rfl⟩ : syracuseStep 11529967 = 17294951) B17294951
theorem B4796729 : Blo 1684042 4796729 := bstep (se 2 (by rfl) ⟨1798773, by rfl⟩ : syracuseStep 4796729 = 3597547) B3597547
theorem B1684583 : Blo 1684042 1684583 := bstep (se 1 (by rfl) ⟨1263437, by rfl⟩ : syracuseStep 1684583 = 2526875) B2526875
theorem B6831535 : Blo 1684042 6831535 := bstep (se 1 (by rfl) ⟨5123651, by rfl⟩ : syracuseStep 6831535 = 10247303) B10247303
theorem B16189577 : Blo 1684042 16189577 := bstep (se 2 (by rfl) ⟨6071091, by rfl⟩ : syracuseStep 16189577 = 12142183) B12142183
theorem B3197819 : Blo 1684042 3197819 := bstep (se 1 (by rfl) ⟨2398364, by rfl⟩ : syracuseStep 3197819 = 4796729) B4796729
theorem B2526857 : Blo 1684042 2526857 := bstep (se 2 (by rfl) ⟨947571, by rfl⟩ : syracuseStep 2526857 = 1895143) B1895143
theorem B3649627 : Blo 1684042 3649627 := bstep (se 1 (by rfl) ⟨2737220, by rfl⟩ : syracuseStep 3649627 = 5474441) B5474441
theorem B15373289 : Blo 1684042 15373289 := bstep (se 2 (by rfl) ⟨5764983, by rfl⟩ : syracuseStep 15373289 = 11529967) B11529967
theorem B9108713 : Blo 1684042 9108713 := bstep (se 2 (by rfl) ⟨3415767, by rfl⟩ : syracuseStep 9108713 = 6831535) B6831535
theorem B19464677 : Blo 1684042 19464677 := bstep (se 4 (by rfl) ⟨1824813, by rfl⟩ : syracuseStep 19464677 = 3649627) B3649627
theorem B24289901 : Blo 1684042 24289901 := bstep (se 3 (by rfl) ⟨4554356, by rfl⟩ : syracuseStep 24289901 = 9108713) B9108713
theorem B10248859 : Blo 1684042 10248859 := bstep (se 1 (by rfl) ⟨7686644, by rfl⟩ : syracuseStep 10248859 = 15373289) B15373289
theorem B10793051 : Blo 1684042 10793051 := bstep (se 1 (by rfl) ⟨8094788, by rfl⟩ : syracuseStep 10793051 = 16189577) B16189577
theorem B1684571 : Blo 1684042 1684571 := bstep (se 1 (by rfl) ⟨1263428, by rfl⟩ : syracuseStep 1684571 = 2526857) B2526857
theorem B8527517 : Blo 1684042 8527517 := bstep (se 3 (by rfl) ⟨1598909, by rfl⟩ : syracuseStep 8527517 = 3197819) B3197819
theorem B12976451 : Blo 1684042 12976451 := bstep (se 1 (by rfl) ⟨9732338, by rfl⟩ : syracuseStep 12976451 = 19464677) B19464677
theorem B7195367 : Blo 1684042 7195367 := bstep (se 1 (by rfl) ⟨5396525, by rfl⟩ : syracuseStep 7195367 = 10793051) B10793051
theorem B54660581 : Blo 1684042 54660581 := bstep (se 4 (by rfl) ⟨5124429, by rfl⟩ : syracuseStep 54660581 = 10248859) B10248859
theorem B16193267 : Blo 1684042 16193267 := bstep (se 1 (by rfl) ⟨12144950, by rfl⟩ : syracuseStep 16193267 = 24289901) B24289901
theorem B5685011 : Blo 1684042 5685011 := bstep (se 1 (by rfl) ⟨4263758, by rfl⟩ : syracuseStep 5685011 = 8527517) B8527517
theorem B8650967 : Blo 1684042 8650967 := bstep (se 1 (by rfl) ⟨6488225, by rfl⟩ : syracuseStep 8650967 = 12976451) B12976451
theorem B36440387 : Blo 1684042 36440387 := bstep (se 1 (by rfl) ⟨27330290, by rfl⟩ : syracuseStep 36440387 = 54660581) B54660581
theorem B4796911 : Blo 1684042 4796911 := bstep (se 1 (by rfl) ⟨3597683, by rfl⟩ : syracuseStep 4796911 = 7195367) B7195367
theorem B3790007 : Blo 1684042 3790007 := bstep (se 1 (by rfl) ⟨2842505, by rfl⟩ : syracuseStep 3790007 = 5685011) B5685011
theorem B10795511 : Blo 1684042 10795511 := bstep (se 1 (by rfl) ⟨8096633, by rfl⟩ : syracuseStep 10795511 = 16193267) B16193267
theorem B92276981 : Blo 1684042 92276981 := bstep (se 5 (by rfl) ⟨4325483, by rfl⟩ : syracuseStep 92276981 = 8650967) B8650967
theorem B2526671 : Blo 1684042 2526671 := bstep (se 1 (by rfl) ⟨1895003, by rfl⟩ : syracuseStep 2526671 = 3790007) B3790007
theorem B24293591 : Blo 1684042 24293591 := bstep (se 1 (by rfl) ⟨18220193, by rfl⟩ : syracuseStep 24293591 = 36440387) B36440387
theorem B7197007 : Blo 1684042 7197007 := bstep (se 1 (by rfl) ⟨5397755, by rfl⟩ : syracuseStep 7197007 = 10795511) B10795511
theorem B6395881 : Blo 1684042 6395881 := bstep (se 2 (by rfl) ⟨2398455, by rfl⟩ : syracuseStep 6395881 = 4796911) B4796911
theorem B16195727 : Blo 1684042 16195727 := bstep (se 1 (by rfl) ⟨12146795, by rfl⟩ : syracuseStep 16195727 = 24293591) B24293591
theorem B9596009 : Blo 1684042 9596009 := bstep (se 2 (by rfl) ⟨3598503, by rfl⟩ : syracuseStep 9596009 = 7197007) B7197007
theorem B61517987 : Blo 1684042 61517987 := bstep (se 1 (by rfl) ⟨46138490, by rfl⟩ : syracuseStep 61517987 = 92276981) B92276981
theorem B1684447 : Blo 1684042 1684447 := bstep (se 1 (by rfl) ⟨1263335, by rfl⟩ : syracuseStep 1684447 = 2526671) B2526671
theorem B8527841 : Blo 1684042 8527841 := bstep (se 2 (by rfl) ⟨3197940, by rfl⟩ : syracuseStep 8527841 = 6395881) B6395881
theorem B10797151 : Blo 1684042 10797151 := bstep (se 1 (by rfl) ⟨8097863, by rfl⟩ : syracuseStep 10797151 = 16195727) B16195727
theorem B41011991 : Blo 1684042 41011991 := bstep (se 1 (by rfl) ⟨30758993, by rfl⟩ : syracuseStep 41011991 = 61517987) B61517987
theorem B6397339 : Blo 1684042 6397339 := bstep (se 1 (by rfl) ⟨4798004, by rfl⟩ : syracuseStep 6397339 = 9596009) B9596009
theorem B5685227 : Blo 1684042 5685227 := bstep (se 1 (by rfl) ⟨4263920, by rfl⟩ : syracuseStep 5685227 = 8527841) B8527841
theorem B8529785 : Blo 1684042 8529785 := bstep (se 2 (by rfl) ⟨3198669, by rfl⟩ : syracuseStep 8529785 = 6397339) B6397339
theorem B14396201 : Blo 1684042 14396201 := bstep (se 2 (by rfl) ⟨5398575, by rfl⟩ : syracuseStep 14396201 = 10797151) B10797151
theorem B27341327 : Blo 1684042 27341327 := bstep (se 1 (by rfl) ⟨20505995, by rfl⟩ : syracuseStep 27341327 = 41011991) B41011991
theorem B3790151 : Blo 1684042 3790151 := bstep (se 1 (by rfl) ⟨2842613, by rfl⟩ : syracuseStep 3790151 = 5685227) B5685227
theorem B18227551 : Blo 1684042 18227551 := bstep (se 1 (by rfl) ⟨13670663, by rfl⟩ : syracuseStep 18227551 = 27341327) B27341327
theorem B5686523 : Blo 1684042 5686523 := bstep (se 1 (by rfl) ⟨4264892, by rfl⟩ : syracuseStep 5686523 = 8529785) B8529785
theorem B2526767 : Blo 1684042 2526767 := bstep (se 1 (by rfl) ⟨1895075, by rfl⟩ : syracuseStep 2526767 = 3790151) B3790151
theorem B9597467 : Blo 1684042 9597467 := bstep (se 1 (by rfl) ⟨7198100, by rfl⟩ : syracuseStep 9597467 = 14396201) B14396201
theorem B6398311 : Blo 1684042 6398311 := bstep (se 1 (by rfl) ⟨4798733, by rfl⟩ : syracuseStep 6398311 = 9597467) B9597467
theorem B1684511 : Blo 1684042 1684511 := bstep (se 1 (by rfl) ⟨1263383, by rfl⟩ : syracuseStep 1684511 = 2526767) B2526767
theorem B24303401 : Blo 1684042 24303401 := bstep (se 2 (by rfl) ⟨9113775, by rfl⟩ : syracuseStep 24303401 = 18227551) B18227551
theorem B3791015 : Blo 1684042 3791015 := bstep (se 1 (by rfl) ⟨2843261, by rfl⟩ : syracuseStep 3791015 = 5686523) B5686523
theorem B8531081 : Blo 1684042 8531081 := bstep (se 2 (by rfl) ⟨3199155, by rfl⟩ : syracuseStep 8531081 = 6398311) B6398311
theorem B2527343 : Blo 1684042 2527343 := bstep (se 1 (by rfl) ⟨1895507, by rfl⟩ : syracuseStep 2527343 = 3791015) B3791015
theorem B16202267 : Blo 1684042 16202267 := bstep (se 1 (by rfl) ⟨12151700, by rfl⟩ : syracuseStep 16202267 = 24303401) B24303401
theorem B5687387 : Blo 1684042 5687387 := bstep (se 1 (by rfl) ⟨4265540, by rfl⟩ : syracuseStep 5687387 = 8531081) B8531081
theorem B10801511 : Blo 1684042 10801511 := bstep (se 1 (by rfl) ⟨8101133, by rfl⟩ : syracuseStep 10801511 = 16202267) B16202267
theorem B1684895 : Blo 1684042 1684895 := bstep (se 1 (by rfl) ⟨1263671, by rfl⟩ : syracuseStep 1684895 = 2527343) B2527343
theorem B7201007 : Blo 1684042 7201007 := bstep (se 1 (by rfl) ⟨5400755, by rfl⟩ : syracuseStep 7201007 = 10801511) B10801511
theorem B3791591 : Blo 1684042 3791591 := bstep (se 1 (by rfl) ⟨2843693, by rfl⟩ : syracuseStep 3791591 = 5687387) B5687387
theorem B4800671 : Blo 1684042 4800671 := bstep (se 1 (by rfl) ⟨3600503, by rfl⟩ : syracuseStep 4800671 = 7201007) B7201007
theorem B2527727 : Blo 1684042 2527727 := bstep (se 1 (by rfl) ⟨1895795, by rfl⟩ : syracuseStep 2527727 = 3791591) B3791591
theorem B3200447 : Blo 1684042 3200447 := bstep (se 1 (by rfl) ⟨2400335, by rfl⟩ : syracuseStep 3200447 = 4800671) B4800671
theorem B1685151 : Blo 1684042 1685151 := bstep (se 1 (by rfl) ⟨1263863, by rfl⟩ : syracuseStep 1685151 = 2527727) B2527727
theorem B2133631 : Blo 1684042 2133631 := bstep (se 1 (by rfl) ⟨1600223, by rfl⟩ : syracuseStep 2133631 = 3200447) B3200447
theorem B2844841 : Blo 1684042 2844841 := bstep (se 2 (by rfl) ⟨1066815, by rfl⟩ : syracuseStep 2844841 = 2133631) B2133631
theorem B3793121 : Blo 1684042 3793121 := bstep (se 2 (by rfl) ⟨1422420, by rfl⟩ : syracuseStep 3793121 = 2844841) B2844841
theorem B2528747 : Blo 1684042 2528747 := bstep (se 1 (by rfl) ⟨1896560, by rfl⟩ : syracuseStep 2528747 = 3793121) B3793121
theorem B1685831 : Blo 1684042 1685831 := bstep (se 1 (by rfl) ⟨1264373, by rfl⟩ : syracuseStep 1685831 = 2528747) B2528747

theorem C0 (j : ℕ) (h1 : 421010 ≤ j) (h2 : j ≤ 421509) : Blo 1684042 (4 * j + 3) := by
  interval_cases j
  · exact B1684043
  · exact B1684047
  · exact B1684051
  · exact B1684055
  · exact B1684059
  · exact B1684063
  · exact B1684067
  · exact B1684071
  · exact B1684075
  · exact B1684079
  · exact B1684083
  · exact B1684087
  · exact B1684091
  · exact B1684095
  · exact B1684099
  · exact B1684103
  · exact B1684107
  · exact B1684111
  · exact B1684115
  · exact B1684119
  · exact B1684123
  · exact B1684127
  · exact B1684131
  · exact B1684135
  · exact B1684139
  · exact B1684143
  · exact B1684147
  · exact B1684151
  · exact B1684155
  · exact B1684159
  · exact B1684163
  · exact B1684167
  · exact B1684171
  · exact B1684175
  · exact B1684179
  · exact B1684183
  · exact B1684187
  · exact B1684191
  · exact B1684195
  · exact B1684199
  · exact B1684203
  · exact B1684207
  · exact B1684211
  · exact B1684215
  · exact B1684219
  · exact B1684223
  · exact B1684227
  · exact B1684231
  · exact B1684235
  · exact B1684239
  · exact B1684243
  · exact B1684247
  · exact B1684251
  · exact B1684255
  · exact B1684259
  · exact B1684263
  · exact B1684267
  · exact B1684271
  · exact B1684275
  · exact B1684279
  · exact B1684283
  · exact B1684287
  · exact B1684291
  · exact B1684295
  · exact B1684299
  · exact B1684303
  · exact B1684307
  · exact B1684311
  · exact B1684315
  · exact B1684319
  · exact B1684323
  · exact B1684327
  · exact B1684331
  · exact B1684335
  · exact B1684339
  · exact B1684343
  · exact B1684347
  · exact B1684351
  · exact B1684355
  · exact B1684359
  · exact B1684363
  · exact B1684367
  · exact B1684371
  · exact B1684375
  · exact B1684379
  · exact B1684383
  · exact B1684387
  · exact B1684391
  · exact B1684395
  · exact B1684399
  · exact B1684403
  · exact B1684407
  · exact B1684411
  · exact B1684415
  · exact B1684419
  · exact B1684423
  · exact B1684427
  · exact B1684431
  · exact B1684435
  · exact B1684439
  · exact B1684443
  · exact B1684447
  · exact B1684451
  · exact B1684455
  · exact B1684459
  · exact B1684463
  · exact B1684467
  · exact B1684471
  · exact B1684475
  · exact B1684479
  · exact B1684483
  · exact B1684487
  · exact B1684491
  · exact B1684495
  · exact B1684499
  · exact B1684503
  · exact B1684507
  · exact B1684511
  · exact B1684515
  · exact B1684519
  · exact B1684523
  · exact B1684527
  · exact B1684531
  · exact B1684535
  · exact B1684539
  · exact B1684543
  · exact B1684547
  · exact B1684551
  · exact B1684555
  · exact B1684559
  · exact B1684563
  · exact B1684567
  · exact B1684571
  · exact B1684575
  · exact B1684579
  · exact B1684583
  · exact B1684587
  · exact B1684591
  · exact B1684595
  · exact B1684599
  · exact B1684603
  · exact B1684607
  · exact B1684611
  · exact B1684615
  · exact B1684619
  · exact B1684623
  · exact B1684627
  · exact B1684631
  · exact B1684635
  · exact B1684639
  · exact B1684643
  · exact B1684647
  · exact B1684651
  · exact B1684655
  · exact B1684659
  · exact B1684663
  · exact B1684667
  · exact B1684671
  · exact B1684675
  · exact B1684679
  · exact B1684683
  · exact B1684687
  · exact B1684691
  · exact B1684695
  · exact B1684699
  · exact B1684703
  · exact B1684707
  · exact B1684711
  · exact B1684715
  · exact B1684719
  · exact B1684723
  · exact B1684727
  · exact B1684731
  · exact B1684735
  · exact B1684739
  · exact B1684743
  · exact B1684747
  · exact B1684751
  · exact B1684755
  · exact B1684759
  · exact B1684763
  · exact B1684767
  · exact B1684771
  · exact B1684775
  · exact B1684779
  · exact B1684783
  · exact B1684787
  · exact B1684791
  · exact B1684795
  · exact B1684799
  · exact B1684803
  · exact B1684807
  · exact B1684811
  · exact B1684815
  · exact B1684819
  · exact B1684823
  · exact B1684827
  · exact B1684831
  · exact B1684835
  · exact B1684839
  · exact B1684843
  · exact B1684847
  · exact B1684851
  · exact B1684855
  · exact B1684859
  · exact B1684863
  · exact B1684867
  · exact B1684871
  · exact B1684875
  · exact B1684879
  · exact B1684883
  · exact B1684887
  · exact B1684891
  · exact B1684895
  · exact B1684899
  · exact B1684903
  · exact B1684907
  · exact B1684911
  · exact B1684915
  · exact B1684919
  · exact B1684923
  · exact B1684927
  · exact B1684931
  · exact B1684935
  · exact B1684939
  · exact B1684943
  · exact B1684947
  · exact B1684951
  · exact B1684955
  · exact B1684959
  · exact B1684963
  · exact B1684967
  · exact B1684971
  · exact B1684975
  · exact B1684979
  · exact B1684983
  · exact B1684987
  · exact B1684991
  · exact B1684995
  · exact B1684999
  · exact B1685003
  · exact B1685007
  · exact B1685011
  · exact B1685015
  · exact B1685019
  · exact B1685023
  · exact B1685027
  · exact B1685031
  · exact B1685035
  · exact B1685039
  · exact B1685043
  · exact B1685047
  · exact B1685051
  · exact B1685055
  · exact B1685059
  · exact B1685063
  · exact B1685067
  · exact B1685071
  · exact B1685075
  · exact B1685079
  · exact B1685083
  · exact B1685087
  · exact B1685091
  · exact B1685095
  · exact B1685099
  · exact B1685103
  · exact B1685107
  · exact B1685111
  · exact B1685115
  · exact B1685119
  · exact B1685123
  · exact B1685127
  · exact B1685131
  · exact B1685135
  · exact B1685139
  · exact B1685143
  · exact B1685147
  · exact B1685151
  · exact B1685155
  · exact B1685159
  · exact B1685163
  · exact B1685167
  · exact B1685171
  · exact B1685175
  · exact B1685179
  · exact B1685183
  · exact B1685187
  · exact B1685191
  · exact B1685195
  · exact B1685199
  · exact B1685203
  · exact B1685207
  · exact B1685211
  · exact B1685215
  · exact B1685219
  · exact B1685223
  · exact B1685227
  · exact B1685231
  · exact B1685235
  · exact B1685239
  · exact B1685243
  · exact B1685247
  · exact B1685251
  · exact B1685255
  · exact B1685259
  · exact B1685263
  · exact B1685267
  · exact B1685271
  · exact B1685275
  · exact B1685279
  · exact B1685283
  · exact B1685287
  · exact B1685291
  · exact B1685295
  · exact B1685299
  · exact B1685303
  · exact B1685307
  · exact B1685311
  · exact B1685315
  · exact B1685319
  · exact B1685323
  · exact B1685327
  · exact B1685331
  · exact B1685335
  · exact B1685339
  · exact B1685343
  · exact B1685347
  · exact B1685351
  · exact B1685355
  · exact B1685359
  · exact B1685363
  · exact B1685367
  · exact B1685371
  · exact B1685375
  · exact B1685379
  · exact B1685383
  · exact B1685387
  · exact B1685391
  · exact B1685395
  · exact B1685399
  · exact B1685403
  · exact B1685407
  · exact B1685411
  · exact B1685415
  · exact B1685419
  · exact B1685423
  · exact B1685427
  · exact B1685431
  · exact B1685435
  · exact B1685439
  · exact B1685443
  · exact B1685447
  · exact B1685451
  · exact B1685455
  · exact B1685459
  · exact B1685463
  · exact B1685467
  · exact B1685471
  · exact B1685475
  · exact B1685479
  · exact B1685483
  · exact B1685487
  · exact B1685491
  · exact B1685495
  · exact B1685499
  · exact B1685503
  · exact B1685507
  · exact B1685511
  · exact B1685515
  · exact B1685519
  · exact B1685523
  · exact B1685527
  · exact B1685531
  · exact B1685535
  · exact B1685539
  · exact B1685543
  · exact B1685547
  · exact B1685551
  · exact B1685555
  · exact B1685559
  · exact B1685563
  · exact B1685567
  · exact B1685571
  · exact B1685575
  · exact B1685579
  · exact B1685583
  · exact B1685587
  · exact B1685591
  · exact B1685595
  · exact B1685599
  · exact B1685603
  · exact B1685607
  · exact B1685611
  · exact B1685615
  · exact B1685619
  · exact B1685623
  · exact B1685627
  · exact B1685631
  · exact B1685635
  · exact B1685639
  · exact B1685643
  · exact B1685647
  · exact B1685651
  · exact B1685655
  · exact B1685659
  · exact B1685663
  · exact B1685667
  · exact B1685671
  · exact B1685675
  · exact B1685679
  · exact B1685683
  · exact B1685687
  · exact B1685691
  · exact B1685695
  · exact B1685699
  · exact B1685703
  · exact B1685707
  · exact B1685711
  · exact B1685715
  · exact B1685719
  · exact B1685723
  · exact B1685727
  · exact B1685731
  · exact B1685735
  · exact B1685739
  · exact B1685743
  · exact B1685747
  · exact B1685751
  · exact B1685755
  · exact B1685759
  · exact B1685763
  · exact B1685767
  · exact B1685771
  · exact B1685775
  · exact B1685779
  · exact B1685783
  · exact B1685787
  · exact B1685791
  · exact B1685795
  · exact B1685799
  · exact B1685803
  · exact B1685807
  · exact B1685811
  · exact B1685815
  · exact B1685819
  · exact B1685823
  · exact B1685827
  · exact B1685831
  · exact B1685835
  · exact B1685839
  · exact B1685843
  · exact B1685847
  · exact B1685851
  · exact B1685855
  · exact B1685859
  · exact B1685863
  · exact B1685867
  · exact B1685871
  · exact B1685875
  · exact B1685879
  · exact B1685883
  · exact B1685887
  · exact B1685891
  · exact B1685895
  · exact B1685899
  · exact B1685903
  · exact B1685907
  · exact B1685911
  · exact B1685915
  · exact B1685919
  · exact B1685923
  · exact B1685927
  · exact B1685931
  · exact B1685935
  · exact B1685939
  · exact B1685943
  · exact B1685947
  · exact B1685951
  · exact B1685955
  · exact B1685959
  · exact B1685963
  · exact B1685967
  · exact B1685971
  · exact B1685975
  · exact B1685979
  · exact B1685983
  · exact B1685987
  · exact B1685991
  · exact B1685995
  · exact B1685999
  · exact B1686003
  · exact B1686007
  · exact B1686011
  · exact B1686015
  · exact B1686019
  · exact B1686023
  · exact B1686027
  · exact B1686031
  · exact B1686035
  · exact B1686039

theorem solution (m : ℕ) (hlo : 1684042 ≤ m) (hhi : m ≤ 1686042) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 421010 ≤ j := by omega
    have hj2 : j ≤ 421509 := by omega
    have hb : Blo 1684042 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
