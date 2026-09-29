-- Prove2me | solution 1 for syracuse_descends_range_1709055_1711055
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:27:29.416928+00:00
-- url     : https://prove2.me/submissions/6c006805-7723-42a3-b004-8a48c0c918af

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


theorem B2564117 : Blo 1709055 2564117 := bbase (se 6 (by rfl) ⟨60096, by rfl⟩ : syracuseStep 2564117 = 120193) (by norm_num)
theorem B5488661 : Blo 1709055 5488661 := bbase (se 6 (by rfl) ⟨128640, by rfl⟩ : syracuseStep 5488661 = 257281) (by norm_num)
theorem B2564141 : Blo 1709055 2564141 := bbase (se 3 (by rfl) ⟨480776, by rfl⟩ : syracuseStep 2564141 = 961553) (by norm_num)
theorem B2564165 : Blo 1709055 2564165 := bbase (se 4 (by rfl) ⟨240390, by rfl⟩ : syracuseStep 2564165 = 480781) (by norm_num)
theorem B2564189 : Blo 1709055 2564189 := bbase (se 3 (by rfl) ⟨480785, by rfl⟩ : syracuseStep 2564189 = 961571) (by norm_num)
theorem B2564213 : Blo 1709055 2564213 := bbase (se 5 (by rfl) ⟨120197, by rfl⟩ : syracuseStep 2564213 = 240395) (by norm_num)
theorem B8659061 : Blo 1709055 8659061 := bbase (se 5 (by rfl) ⟨405893, by rfl⟩ : syracuseStep 8659061 = 811787) (by norm_num)
theorem B2564237 : Blo 1709055 2564237 := bbase (se 3 (by rfl) ⟨480794, by rfl⟩ : syracuseStep 2564237 = 961589) (by norm_num)
theorem B21921941 : Blo 1709055 21921941 := bbase (se 6 (by rfl) ⟨513795, by rfl⟩ : syracuseStep 21921941 = 1027591) (by norm_num)
theorem B2564261 : Blo 1709055 2564261 := bbase (se 4 (by rfl) ⟨240399, by rfl⟩ : syracuseStep 2564261 = 480799) (by norm_num)
theorem B2564285 : Blo 1709055 2564285 := bbase (se 3 (by rfl) ⟨480803, by rfl⟩ : syracuseStep 2564285 = 961607) (by norm_num)
theorem B2564309 : Blo 1709055 2564309 := bbase (se 7 (by rfl) ⟨30050, by rfl⟩ : syracuseStep 2564309 = 60101) (by norm_num)
theorem B6496469 : Blo 1709055 6496469 := bbase (se 7 (by rfl) ⟨76130, by rfl⟩ : syracuseStep 6496469 = 152261) (by norm_num)
theorem B2564333 : Blo 1709055 2564333 := bbase (se 3 (by rfl) ⟨480812, by rfl⟩ : syracuseStep 2564333 = 961625) (by norm_num)
theorem B9740533 : Blo 1709055 9740533 := bbase (se 5 (by rfl) ⟨456587, by rfl⟩ : syracuseStep 9740533 = 913175) (by norm_num)
theorem B2564357 : Blo 1709055 2564357 := bbase (se 4 (by rfl) ⟨240408, by rfl⟩ : syracuseStep 2564357 = 480817) (by norm_num)
theorem B1827085 : Blo 1709055 1827085 := bbase (se 3 (by rfl) ⟨342578, by rfl⟩ : syracuseStep 1827085 = 685157) (by norm_num)
theorem B2564381 : Blo 1709055 2564381 := bbase (se 3 (by rfl) ⟨480821, by rfl⟩ : syracuseStep 2564381 = 961643) (by norm_num)
theorem B1949989 : Blo 1709055 1949989 := bbase (se 4 (by rfl) ⟨182811, by rfl⟩ : syracuseStep 1949989 = 365623) (by norm_num)
theorem B2564405 : Blo 1709055 2564405 := bbase (se 5 (by rfl) ⟨120206, by rfl⟩ : syracuseStep 2564405 = 240413) (by norm_num)
theorem B1827145 : Blo 1709055 1827145 := bbase (se 2 (by rfl) ⟨685179, by rfl⟩ : syracuseStep 1827145 = 1370359) (by norm_num)
theorem B2564429 : Blo 1709055 2564429 := bbase (se 3 (by rfl) ⟨480830, by rfl⟩ : syracuseStep 2564429 = 961661) (by norm_num)
theorem B2564453 : Blo 1709055 2564453 := bbase (se 4 (by rfl) ⟨240417, by rfl⟩ : syracuseStep 2564453 = 480835) (by norm_num)
theorem B2343277 : Blo 1709055 2343277 := bbase (se 3 (by rfl) ⟨439364, by rfl⟩ : syracuseStep 2343277 = 878729) (by norm_num)
theorem B14614901 : Blo 1709055 14614901 := bbase (se 5 (by rfl) ⟨685073, by rfl⟩ : syracuseStep 14614901 = 1370147) (by norm_num)
theorem B2564477 : Blo 1709055 2564477 := bbase (se 3 (by rfl) ⟨480839, by rfl⟩ : syracuseStep 2564477 = 961679) (by norm_num)
theorem B1950085 : Blo 1709055 1950085 := bbase (se 4 (by rfl) ⟨182820, by rfl⟩ : syracuseStep 1950085 = 365641) (by norm_num)
theorem B2564501 : Blo 1709055 2564501 := bbase (se 6 (by rfl) ⟨60105, by rfl⟩ : syracuseStep 2564501 = 120211) (by norm_num)
theorem B2564525 : Blo 1709055 2564525 := bbase (se 3 (by rfl) ⟨480848, by rfl⟩ : syracuseStep 2564525 = 961697) (by norm_num)
theorem B2163125 : Blo 1709055 2163125 := bbase (se 5 (by rfl) ⟨101396, by rfl⟩ : syracuseStep 2163125 = 202793) (by norm_num)
theorem B5480885 : Blo 1709055 5480885 := bbase (se 5 (by rfl) ⟨256916, by rfl⟩ : syracuseStep 5480885 = 513833) (by norm_num)
theorem B2564549 : Blo 1709055 2564549 := bbase (se 4 (by rfl) ⟨240426, by rfl⟩ : syracuseStep 2564549 = 480853) (by norm_num)
theorem B3654085 : Blo 1709055 3654085 := bbase (se 4 (by rfl) ⟨342570, by rfl⟩ : syracuseStep 3654085 = 685141) (by norm_num)
theorem B2884045 : Blo 1709055 2884045 := bbase (se 3 (by rfl) ⟨540758, by rfl⟩ : syracuseStep 2884045 = 1081517) (by norm_num)
theorem B2433493 : Blo 1709055 2433493 := bbase (se 7 (by rfl) ⟨28517, by rfl⟩ : syracuseStep 2433493 = 57035) (by norm_num)
theorem B2564573 : Blo 1709055 2564573 := bbase (se 3 (by rfl) ⟨480857, by rfl⟩ : syracuseStep 2564573 = 961715) (by norm_num)
theorem B2163181 : Blo 1709055 2163181 := bbase (se 3 (by rfl) ⟨405596, by rfl⟩ : syracuseStep 2163181 = 811193) (by norm_num)
theorem B2564597 : Blo 1709055 2564597 := bbase (se 5 (by rfl) ⟨120215, by rfl⟩ : syracuseStep 2564597 = 240431) (by norm_num)
theorem B14606837 : Blo 1709055 14606837 := bbase (se 5 (by rfl) ⟨684695, by rfl⟩ : syracuseStep 14606837 = 1369391) (by norm_num)
theorem B2564621 : Blo 1709055 2564621 := bbase (se 3 (by rfl) ⟨480866, by rfl⟩ : syracuseStep 2564621 = 961733) (by norm_num)
theorem B2884133 : Blo 1709055 2884133 := bbase (se 4 (by rfl) ⟨270387, by rfl⟩ : syracuseStep 2884133 = 540775) (by norm_num)
theorem B2564645 : Blo 1709055 2564645 := bbase (se 4 (by rfl) ⟨240435, by rfl⟩ : syracuseStep 2564645 = 480871) (by norm_num)
theorem B3080749 : Blo 1709055 3080749 := bbase (se 3 (by rfl) ⟨577640, by rfl⟩ : syracuseStep 3080749 = 1155281) (by norm_num)
theorem B2564669 : Blo 1709055 2564669 := bbase (se 3 (by rfl) ⟨480875, by rfl⟩ : syracuseStep 2564669 = 961751) (by norm_num)
theorem B2163277 : Blo 1709055 2163277 := bbase (se 3 (by rfl) ⟨405614, by rfl⟩ : syracuseStep 2163277 = 811229) (by norm_num)
theorem B2564693 : Blo 1709055 2564693 := bbase (se 8 (by rfl) ⟨15027, by rfl⟩ : syracuseStep 2564693 = 30055) (by norm_num)
theorem B2564717 : Blo 1709055 2564717 := bbase (se 3 (by rfl) ⟨480884, by rfl⟩ : syracuseStep 2564717 = 961769) (by norm_num)
theorem B2925181 : Blo 1709055 2925181 := bbase (se 3 (by rfl) ⟨548471, by rfl⟩ : syracuseStep 2925181 = 1096943) (by norm_num)
theorem B2564741 : Blo 1709055 2564741 := bbase (se 4 (by rfl) ⟨240444, by rfl⟩ : syracuseStep 2564741 = 480889) (by norm_num)
theorem B2310805 : Blo 1709055 2310805 := bbase (se 6 (by rfl) ⟨54159, by rfl⟩ : syracuseStep 2310805 = 108319) (by norm_num)
theorem B2564765 : Blo 1709055 2564765 := bbase (se 3 (by rfl) ⟨480893, by rfl⟩ : syracuseStep 2564765 = 961787) (by norm_num)
theorem B2884261 : Blo 1709055 2884261 := bbase (se 4 (by rfl) ⟨270399, by rfl⟩ : syracuseStep 2884261 = 540799) (by norm_num)
theorem B2564789 : Blo 1709055 2564789 := bbase (se 5 (by rfl) ⟨120224, by rfl⟩ : syracuseStep 2564789 = 240449) (by norm_num)
theorem B2564813 : Blo 1709055 2564813 := bbase (se 3 (by rfl) ⟨480902, by rfl⟩ : syracuseStep 2564813 = 961805) (by norm_num)
theorem B52675285 : Blo 1709055 52675285 := bbase (se 7 (by rfl) ⟨617288, by rfl⟩ : syracuseStep 52675285 = 1234577) (by norm_num)
theorem B2564837 : Blo 1709055 2564837 := bbase (se 4 (by rfl) ⟨240453, by rfl⟩ : syracuseStep 2564837 = 480907) (by norm_num)
theorem B2163449 : Blo 1709055 2163449 := bbase (se 2 (by rfl) ⟨811293, by rfl⟩ : syracuseStep 2163449 = 1622587) (by norm_num)
theorem B2884349 : Blo 1709055 2884349 := bbase (se 3 (by rfl) ⟨540815, by rfl⟩ : syracuseStep 2884349 = 1081631) (by norm_num)
theorem B2564861 : Blo 1709055 2564861 := bbase (se 3 (by rfl) ⟨480911, by rfl⟩ : syracuseStep 2564861 = 961823) (by norm_num)
theorem B4326149 : Blo 1709055 4326149 := bbase (se 4 (by rfl) ⟨405576, by rfl⟩ : syracuseStep 4326149 = 811153) (by norm_num)
theorem B2564885 : Blo 1709055 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B2564909 : Blo 1709055 2564909 := bbase (se 3 (by rfl) ⟨480920, by rfl⟩ : syracuseStep 2564909 = 961841) (by norm_num)
theorem B2163505 : Blo 1709055 2163505 := bbase (se 2 (by rfl) ⟨811314, by rfl⟩ : syracuseStep 2163505 = 1622629) (by norm_num)
theorem B2564933 : Blo 1709055 2564933 := bbase (se 4 (by rfl) ⟨240462, by rfl⟩ : syracuseStep 2564933 = 480925) (by norm_num)
theorem B2564957 : Blo 1709055 2564957 := bbase (se 3 (by rfl) ⟨480929, by rfl⟩ : syracuseStep 2564957 = 961859) (by norm_num)
theorem B2311021 : Blo 1709055 2311021 := bbase (se 3 (by rfl) ⟨433316, by rfl⟩ : syracuseStep 2311021 = 866633) (by norm_num)
theorem B2564981 : Blo 1709055 2564981 := bbase (se 5 (by rfl) ⟨120233, by rfl⟩ : syracuseStep 2564981 = 240467) (by norm_num)
theorem B2884477 : Blo 1709055 2884477 := bbase (se 3 (by rfl) ⟨540839, by rfl⟩ : syracuseStep 2884477 = 1081679) (by norm_num)
theorem B3466109 : Blo 1709055 3466109 := bbase (se 3 (by rfl) ⟨649895, by rfl⟩ : syracuseStep 3466109 = 1299791) (by norm_num)
theorem B2565005 : Blo 1709055 2565005 := bbase (se 3 (by rfl) ⟨480938, by rfl⟩ : syracuseStep 2565005 = 961877) (by norm_num)
theorem B2163601 : Blo 1709055 2163601 := bbase (se 2 (by rfl) ⟨811350, by rfl⟩ : syracuseStep 2163601 = 1622701) (by norm_num)
theorem B2565029 : Blo 1709055 2565029 := bbase (se 4 (by rfl) ⟨240471, by rfl⟩ : syracuseStep 2565029 = 480943) (by norm_num)
theorem B5768117 : Blo 1709055 5768117 := bbase (se 5 (by rfl) ⟨270380, by rfl⟩ : syracuseStep 5768117 = 540761) (by norm_num)
theorem B2565053 : Blo 1709055 2565053 := bbase (se 3 (by rfl) ⟨480947, by rfl⟩ : syracuseStep 2565053 = 961895) (by norm_num)
theorem B2433989 : Blo 1709055 2433989 := bbase (se 4 (by rfl) ⟨228186, by rfl⟩ : syracuseStep 2433989 = 456373) (by norm_num)
theorem B2884565 : Blo 1709055 2884565 := bbase (se 7 (by rfl) ⟨33803, by rfl⟩ : syracuseStep 2884565 = 67607) (by norm_num)
theorem B2565077 : Blo 1709055 2565077 := bbase (se 7 (by rfl) ⟨30059, by rfl⟩ : syracuseStep 2565077 = 60119) (by norm_num)
theorem B12329941 : Blo 1709055 12329941 := bbase (se 7 (by rfl) ⟨144491, by rfl⟩ : syracuseStep 12329941 = 288983) (by norm_num)
theorem B2565101 : Blo 1709055 2565101 := bbase (se 3 (by rfl) ⟨480956, by rfl⟩ : syracuseStep 2565101 = 961913) (by norm_num)
theorem B2565125 : Blo 1709055 2565125 := bbase (se 4 (by rfl) ⟨240480, by rfl⟩ : syracuseStep 2565125 = 480961) (by norm_num)
theorem B2565149 : Blo 1709055 2565149 := bbase (se 3 (by rfl) ⟨480965, by rfl⟩ : syracuseStep 2565149 = 961931) (by norm_num)
theorem B2565173 : Blo 1709055 2565173 := bbase (se 5 (by rfl) ⟨120242, by rfl⟩ : syracuseStep 2565173 = 240485) (by norm_num)
theorem B3900469 : Blo 1709055 3900469 := bbase (se 5 (by rfl) ⟨182834, by rfl⟩ : syracuseStep 3900469 = 365669) (by norm_num)
theorem B2163773 : Blo 1709055 2163773 := bbase (se 3 (by rfl) ⟨405707, by rfl⟩ : syracuseStep 2163773 = 811415) (by norm_num)
theorem B2565197 : Blo 1709055 2565197 := bbase (se 3 (by rfl) ⟨480974, by rfl⟩ : syracuseStep 2565197 = 961949) (by norm_num)
theorem B2884693 : Blo 1709055 2884693 := bbase (se 8 (by rfl) ⟨16902, by rfl⟩ : syracuseStep 2884693 = 33805) (by norm_num)
theorem B4326493 : Blo 1709055 4326493 := bbase (se 3 (by rfl) ⟨811217, by rfl⟩ : syracuseStep 4326493 = 1622435) (by norm_num)
theorem B2565221 : Blo 1709055 2565221 := bbase (se 4 (by rfl) ⟨240489, by rfl⟩ : syracuseStep 2565221 = 480979) (by norm_num)
theorem B2163829 : Blo 1709055 2163829 := bbase (se 5 (by rfl) ⟨101429, by rfl⟩ : syracuseStep 2163829 = 202859) (by norm_num)
theorem B2565245 : Blo 1709055 2565245 := bbase (se 3 (by rfl) ⟨480983, by rfl⟩ : syracuseStep 2565245 = 961967) (by norm_num)
theorem B3245197 : Blo 1709055 3245197 := bbase (se 3 (by rfl) ⟨608474, by rfl⟩ : syracuseStep 3245197 = 1216949) (by norm_num)
theorem B2565269 : Blo 1709055 2565269 := bbase (se 6 (by rfl) ⟨60123, by rfl⟩ : syracuseStep 2565269 = 120247) (by norm_num)
theorem B2884781 : Blo 1709055 2884781 := bbase (se 3 (by rfl) ⟨540896, by rfl⟩ : syracuseStep 2884781 = 1081793) (by norm_num)
theorem B2565293 : Blo 1709055 2565293 := bbase (se 3 (by rfl) ⟨480992, by rfl⟩ : syracuseStep 2565293 = 961985) (by norm_num)
theorem B2565317 : Blo 1709055 2565317 := bbase (se 4 (by rfl) ⟨240498, by rfl⟩ : syracuseStep 2565317 = 480997) (by norm_num)
theorem B4326605 : Blo 1709055 4326605 := bbase (se 3 (by rfl) ⟨811238, by rfl⟩ : syracuseStep 4326605 = 1622477) (by norm_num)
theorem B2163925 : Blo 1709055 2163925 := bbase (se 7 (by rfl) ⟨25358, by rfl⟩ : syracuseStep 2163925 = 50717) (by norm_num)
theorem B40035541 : Blo 1709055 40035541 := bbase (se 7 (by rfl) ⟨469166, by rfl⟩ : syracuseStep 40035541 = 938333) (by norm_num)
theorem B2565341 : Blo 1709055 2565341 := bbase (se 3 (by rfl) ⟨481001, by rfl⟩ : syracuseStep 2565341 = 962003) (by norm_num)
theorem B2565365 : Blo 1709055 2565365 := bbase (se 5 (by rfl) ⟨120251, by rfl⟩ : syracuseStep 2565365 = 240503) (by norm_num)
theorem B2565389 : Blo 1709055 2565389 := bbase (se 3 (by rfl) ⟨481010, by rfl⟩ : syracuseStep 2565389 = 962021) (by norm_num)
theorem B3245341 : Blo 1709055 3245341 := bbase (se 3 (by rfl) ⟨608501, by rfl⟩ : syracuseStep 3245341 = 1217003) (by norm_num)
theorem B2565413 : Blo 1709055 2565413 := bbase (se 4 (by rfl) ⟨240507, by rfl⟩ : syracuseStep 2565413 = 481015) (by norm_num)
theorem B2884909 : Blo 1709055 2884909 := bbase (se 3 (by rfl) ⟨540920, by rfl⟩ : syracuseStep 2884909 = 1081841) (by norm_num)
theorem B6931765 : Blo 1709055 6931765 := bbase (se 5 (by rfl) ⟨324926, by rfl⟩ : syracuseStep 6931765 = 649853) (by norm_num)
theorem B2565437 : Blo 1709055 2565437 := bbase (se 3 (by rfl) ⟨481019, by rfl⟩ : syracuseStep 2565437 = 962039) (by norm_num)
theorem B4867397 : Blo 1709055 4867397 := bbase (se 4 (by rfl) ⟨456318, by rfl⟩ : syracuseStep 4867397 = 912637) (by norm_num)
theorem B2565461 : Blo 1709055 2565461 := bbase (se 12 (by rfl) ⟨939, by rfl⟩ : syracuseStep 2565461 = 1879) (by norm_num)
theorem B5768549 : Blo 1709055 5768549 := bbase (se 4 (by rfl) ⟨540801, by rfl⟩ : syracuseStep 5768549 = 1081603) (by norm_num)
theorem B2565485 : Blo 1709055 2565485 := bbase (se 3 (by rfl) ⟨481028, by rfl⟩ : syracuseStep 2565485 = 962057) (by norm_num)
theorem B2164097 : Blo 1709055 2164097 := bbase (se 2 (by rfl) ⟨811536, by rfl⟩ : syracuseStep 2164097 = 1623073) (by norm_num)
theorem B2884997 : Blo 1709055 2884997 := bbase (se 4 (by rfl) ⟨270468, by rfl⟩ : syracuseStep 2884997 = 540937) (by norm_num)
theorem B2565509 : Blo 1709055 2565509 := bbase (se 4 (by rfl) ⟨240516, by rfl⟩ : syracuseStep 2565509 = 481033) (by norm_num)
theorem B8660357 : Blo 1709055 8660357 := bbase (se 4 (by rfl) ⟨811908, by rfl⟩ : syracuseStep 8660357 = 1623817) (by norm_num)
theorem B4326797 : Blo 1709055 4326797 := bbase (se 3 (by rfl) ⟨811274, by rfl⟩ : syracuseStep 4326797 = 1622549) (by norm_num)
theorem B2565533 : Blo 1709055 2565533 := bbase (se 3 (by rfl) ⟨481037, by rfl⟩ : syracuseStep 2565533 = 962075) (by norm_num)
theorem B2565557 : Blo 1709055 2565557 := bbase (se 5 (by rfl) ⟨120260, by rfl⟩ : syracuseStep 2565557 = 240521) (by norm_num)
theorem B2164153 : Blo 1709055 2164153 := bbase (se 2 (by rfl) ⟨811557, by rfl⟩ : syracuseStep 2164153 = 1623115) (by norm_num)
theorem B3245501 : Blo 1709055 3245501 := bbase (se 3 (by rfl) ⟨608531, by rfl⟩ : syracuseStep 3245501 = 1217063) (by norm_num)
theorem B2565581 : Blo 1709055 2565581 := bbase (se 3 (by rfl) ⟨481046, by rfl⟩ : syracuseStep 2565581 = 962093) (by norm_num)
theorem B2565605 : Blo 1709055 2565605 := bbase (se 4 (by rfl) ⟨240525, by rfl⟩ : syracuseStep 2565605 = 481051) (by norm_num)
theorem B2434541 : Blo 1709055 2434541 := bbase (se 3 (by rfl) ⟨456476, by rfl⟩ : syracuseStep 2434541 = 912953) (by norm_num)
theorem B2565629 : Blo 1709055 2565629 := bbase (se 3 (by rfl) ⟨481055, by rfl⟩ : syracuseStep 2565629 = 962111) (by norm_num)
theorem B2885125 : Blo 1709055 2885125 := bbase (se 4 (by rfl) ⟨270480, by rfl⟩ : syracuseStep 2885125 = 540961) (by norm_num)
theorem B2565653 : Blo 1709055 2565653 := bbase (se 6 (by rfl) ⟨60132, by rfl⟩ : syracuseStep 2565653 = 120265) (by norm_num)
theorem B2164249 : Blo 1709055 2164249 := bbase (se 2 (by rfl) ⟨811593, by rfl⟩ : syracuseStep 2164249 = 1623187) (by norm_num)
theorem B2565677 : Blo 1709055 2565677 := bbase (se 3 (by rfl) ⟨481064, by rfl⟩ : syracuseStep 2565677 = 962129) (by norm_num)
theorem B7505477 : Blo 1709055 7505477 := bbase (se 4 (by rfl) ⟨703638, by rfl⟩ : syracuseStep 7505477 = 1407277) (by norm_num)
theorem B2565701 : Blo 1709055 2565701 := bbase (se 4 (by rfl) ⟨240534, by rfl⟩ : syracuseStep 2565701 = 481069) (by norm_num)
theorem B3245645 : Blo 1709055 3245645 := bbase (se 3 (by rfl) ⟨608558, by rfl⟩ : syracuseStep 3245645 = 1217117) (by norm_num)
theorem B2737757 : Blo 1709055 2737757 := bbase (se 3 (by rfl) ⟨513329, by rfl⟩ : syracuseStep 2737757 = 1026659) (by norm_num)
theorem B2885213 : Blo 1709055 2885213 := bbase (se 3 (by rfl) ⟨540977, by rfl⟩ : syracuseStep 2885213 = 1081955) (by norm_num)
theorem B2565725 : Blo 1709055 2565725 := bbase (se 3 (by rfl) ⟨481073, by rfl⟩ : syracuseStep 2565725 = 962147) (by norm_num)
theorem B2565749 : Blo 1709055 2565749 := bbase (se 5 (by rfl) ⟨120269, by rfl⟩ : syracuseStep 2565749 = 240539) (by norm_num)
theorem B2565773 : Blo 1709055 2565773 := bbase (se 3 (by rfl) ⟨481082, by rfl⟩ : syracuseStep 2565773 = 962165) (by norm_num)
theorem B2565797 : Blo 1709055 2565797 := bbase (se 4 (by rfl) ⟨240543, by rfl⟩ : syracuseStep 2565797 = 481087) (by norm_num)
theorem B2565821 : Blo 1709055 2565821 := bbase (se 3 (by rfl) ⟨481091, by rfl⟩ : syracuseStep 2565821 = 962183) (by norm_num)
theorem B2164421 : Blo 1709055 2164421 := bbase (se 4 (by rfl) ⟨202914, by rfl⟩ : syracuseStep 2164421 = 405829) (by norm_num)
theorem B15599317 : Blo 1709055 15599317 := bbase (se 7 (by rfl) ⟨182804, by rfl⟩ : syracuseStep 15599317 = 365609) (by norm_num)
theorem B2565845 : Blo 1709055 2565845 := bbase (se 7 (by rfl) ⟨30068, by rfl⟩ : syracuseStep 2565845 = 60137) (by norm_num)
theorem B2885341 : Blo 1709055 2885341 := bbase (se 3 (by rfl) ⟨541001, by rfl⟩ : syracuseStep 2885341 = 1082003) (by norm_num)
theorem B2737885 : Blo 1709055 2737885 := bbase (se 3 (by rfl) ⟨513353, by rfl⟩ : syracuseStep 2737885 = 1026707) (by norm_num)
theorem B4933349 : Blo 1709055 4933349 := bbase (se 4 (by rfl) ⟨462501, by rfl⟩ : syracuseStep 4933349 = 925003) (by norm_num)
theorem B4327141 : Blo 1709055 4327141 := bbase (se 4 (by rfl) ⟨405669, by rfl⟩ : syracuseStep 4327141 = 811339) (by norm_num)
theorem B2565869 : Blo 1709055 2565869 := bbase (se 3 (by rfl) ⟨481100, by rfl⟩ : syracuseStep 2565869 = 962201) (by norm_num)
theorem B2164477 : Blo 1709055 2164477 := bbase (se 3 (by rfl) ⟨405839, by rfl⟩ : syracuseStep 2164477 = 811679) (by norm_num)
theorem B2565893 : Blo 1709055 2565893 := bbase (se 4 (by rfl) ⟨240552, by rfl⟩ : syracuseStep 2565893 = 481105) (by norm_num)
theorem B5768981 : Blo 1709055 5768981 := bbase (se 6 (by rfl) ⟨135210, by rfl⟩ : syracuseStep 5768981 = 270421) (by norm_num)
theorem B2565917 : Blo 1709055 2565917 := bbase (se 3 (by rfl) ⟨481109, by rfl⟩ : syracuseStep 2565917 = 962219) (by norm_num)
theorem B8652581 : Blo 1709055 8652581 := bbase (se 4 (by rfl) ⟨811179, by rfl⟩ : syracuseStep 8652581 = 1622359) (by norm_num)
theorem B2598701 : Blo 1709055 2598701 := bbase (se 3 (by rfl) ⟨487256, by rfl⟩ : syracuseStep 2598701 = 974513) (by norm_num)
theorem B2885429 : Blo 1709055 2885429 := bbase (se 5 (by rfl) ⟨135254, by rfl⟩ : syracuseStep 2885429 = 270509) (by norm_num)
theorem B2565941 : Blo 1709055 2565941 := bbase (se 5 (by rfl) ⟨120278, by rfl⟩ : syracuseStep 2565941 = 240557) (by norm_num)
theorem B2565965 : Blo 1709055 2565965 := bbase (se 3 (by rfl) ⟨481118, by rfl⟩ : syracuseStep 2565965 = 962237) (by norm_num)
theorem B4327253 : Blo 1709055 4327253 := bbase (se 9 (by rfl) ⟨12677, by rfl⟩ : syracuseStep 4327253 = 25355) (by norm_num)
theorem B2164573 : Blo 1709055 2164573 := bbase (se 3 (by rfl) ⟨405857, by rfl⟩ : syracuseStep 2164573 = 811715) (by norm_num)
theorem B2565989 : Blo 1709055 2565989 := bbase (se 4 (by rfl) ⟨240561, by rfl⟩ : syracuseStep 2565989 = 481123) (by norm_num)
theorem B3245933 : Blo 1709055 3245933 := bbase (se 3 (by rfl) ⟨608612, by rfl⟩ : syracuseStep 3245933 = 1217225) (by norm_num)
theorem B2566013 : Blo 1709055 2566013 := bbase (se 3 (by rfl) ⟨481127, by rfl⟩ : syracuseStep 2566013 = 962255) (by norm_num)
theorem B3082133 : Blo 1709055 3082133 := bbase (se 6 (by rfl) ⟨72237, by rfl⟩ : syracuseStep 3082133 = 144475) (by norm_num)
theorem B2566037 : Blo 1709055 2566037 := bbase (se 6 (by rfl) ⟨60141, by rfl⟩ : syracuseStep 2566037 = 120283) (by norm_num)
theorem B2566061 : Blo 1709055 2566061 := bbase (se 3 (by rfl) ⟨481136, by rfl⟩ : syracuseStep 2566061 = 962273) (by norm_num)
theorem B2885557 : Blo 1709055 2885557 := bbase (se 5 (by rfl) ⟨135260, by rfl⟩ : syracuseStep 2885557 = 270521) (by norm_num)
theorem B2566085 : Blo 1709055 2566085 := bbase (se 4 (by rfl) ⟨240570, by rfl⟩ : syracuseStep 2566085 = 481141) (by norm_num)
theorem B2566109 : Blo 1709055 2566109 := bbase (se 3 (by rfl) ⟨481145, by rfl⟩ : syracuseStep 2566109 = 962291) (by norm_num)
theorem B2566133 : Blo 1709055 2566133 := bbase (se 5 (by rfl) ⟨120287, by rfl⟩ : syracuseStep 2566133 = 240575) (by norm_num)
theorem B3246085 : Blo 1709055 3246085 := bbase (se 4 (by rfl) ⟨304320, by rfl⟩ : syracuseStep 3246085 = 608641) (by norm_num)
theorem B2164745 : Blo 1709055 2164745 := bbase (se 2 (by rfl) ⟨811779, by rfl⟩ : syracuseStep 2164745 = 1623559) (by norm_num)
theorem B2885645 : Blo 1709055 2885645 := bbase (se 3 (by rfl) ⟨541058, by rfl⟩ : syracuseStep 2885645 = 1082117) (by norm_num)
theorem B2566157 : Blo 1709055 2566157 := bbase (se 3 (by rfl) ⟨481154, by rfl⟩ : syracuseStep 2566157 = 962309) (by norm_num)
theorem B4327445 : Blo 1709055 4327445 := bbase (se 6 (by rfl) ⟨101424, by rfl⟩ : syracuseStep 4327445 = 202849) (by norm_num)
theorem B2566181 : Blo 1709055 2566181 := bbase (se 4 (by rfl) ⟨240579, by rfl⟩ : syracuseStep 2566181 = 481159) (by norm_num)
theorem B6490165 : Blo 1709055 6490165 := bbase (se 5 (by rfl) ⟨304226, by rfl⟩ : syracuseStep 6490165 = 608453) (by norm_num)
theorem B2566205 : Blo 1709055 2566205 := bbase (se 3 (by rfl) ⟨481163, by rfl⟩ : syracuseStep 2566205 = 962327) (by norm_num)
theorem B2164801 : Blo 1709055 2164801 := bbase (se 2 (by rfl) ⟨811800, by rfl⟩ : syracuseStep 2164801 = 1623601) (by norm_num)
theorem B2566229 : Blo 1709055 2566229 := bbase (se 8 (by rfl) ⟨15036, by rfl⟩ : syracuseStep 2566229 = 30073) (by norm_num)
theorem B2566253 : Blo 1709055 2566253 := bbase (se 3 (by rfl) ⟨481172, by rfl⟩ : syracuseStep 2566253 = 962345) (by norm_num)
theorem B2566277 : Blo 1709055 2566277 := bbase (se 4 (by rfl) ⟨240588, by rfl⟩ : syracuseStep 2566277 = 481177) (by norm_num)
theorem B2885773 : Blo 1709055 2885773 := bbase (se 3 (by rfl) ⟨541082, by rfl⟩ : syracuseStep 2885773 = 1082165) (by norm_num)
theorem B2566301 : Blo 1709055 2566301 := bbase (se 3 (by rfl) ⟨481181, by rfl⟩ : syracuseStep 2566301 = 962363) (by norm_num)
theorem B2164897 : Blo 1709055 2164897 := bbase (se 2 (by rfl) ⟨811836, by rfl⟩ : syracuseStep 2164897 = 1623673) (by norm_num)
theorem B7301285 : Blo 1709055 7301285 := bbase (se 4 (by rfl) ⟨684495, by rfl⟩ : syracuseStep 7301285 = 1368991) (by norm_num)
theorem B9742517 : Blo 1709055 9742517 := bbase (se 5 (by rfl) ⟨456680, by rfl⟩ : syracuseStep 9742517 = 913361) (by norm_num)
theorem B2566325 : Blo 1709055 2566325 := bbase (se 5 (by rfl) ⟨120296, by rfl⟩ : syracuseStep 2566325 = 240593) (by norm_num)
theorem B5769413 : Blo 1709055 5769413 := bbase (se 4 (by rfl) ⟨540882, by rfl⟩ : syracuseStep 5769413 = 1081765) (by norm_num)
theorem B2566349 : Blo 1709055 2566349 := bbase (se 3 (by rfl) ⟨481190, by rfl⟩ : syracuseStep 2566349 = 962381) (by norm_num)
theorem B2435293 : Blo 1709055 2435293 := bbase (se 3 (by rfl) ⟨456617, by rfl⟩ : syracuseStep 2435293 = 913235) (by norm_num)
theorem B2885861 : Blo 1709055 2885861 := bbase (se 4 (by rfl) ⟨270549, by rfl⟩ : syracuseStep 2885861 = 541099) (by norm_num)
theorem B2566373 : Blo 1709055 2566373 := bbase (se 4 (by rfl) ⟨240597, by rfl⟩ : syracuseStep 2566373 = 481195) (by norm_num)
theorem B2566397 : Blo 1709055 2566397 := bbase (se 3 (by rfl) ⟨481199, by rfl⟩ : syracuseStep 2566397 = 962399) (by norm_num)
theorem B2566421 : Blo 1709055 2566421 := bbase (se 6 (by rfl) ⟨60150, by rfl⟩ : syracuseStep 2566421 = 120301) (by norm_num)
theorem B2566445 : Blo 1709055 2566445 := bbase (se 3 (by rfl) ⟨481208, by rfl⟩ : syracuseStep 2566445 = 962417) (by norm_num)
theorem B3246389 : Blo 1709055 3246389 := bbase (se 5 (by rfl) ⟨152174, by rfl⟩ : syracuseStep 3246389 = 304349) (by norm_num)
theorem B2566469 : Blo 1709055 2566469 := bbase (se 4 (by rfl) ⟨240606, by rfl⟩ : syracuseStep 2566469 = 481213) (by norm_num)
theorem B2165069 : Blo 1709055 2165069 := bbase (se 3 (by rfl) ⟨405950, by rfl⟩ : syracuseStep 2165069 = 811901) (by norm_num)
theorem B2566493 : Blo 1709055 2566493 := bbase (se 3 (by rfl) ⟨481217, by rfl⟩ : syracuseStep 2566493 = 962435) (by norm_num)
theorem B6490469 : Blo 1709055 6490469 := bbase (se 4 (by rfl) ⟨608481, by rfl⟩ : syracuseStep 6490469 = 1216963) (by norm_num)
theorem B2885989 : Blo 1709055 2885989 := bbase (se 4 (by rfl) ⟨270561, by rfl⟩ : syracuseStep 2885989 = 541123) (by norm_num)
theorem B4327789 : Blo 1709055 4327789 := bbase (se 3 (by rfl) ⟨811460, by rfl⟩ : syracuseStep 4327789 = 1622921) (by norm_num)
theorem B2566517 : Blo 1709055 2566517 := bbase (se 5 (by rfl) ⟨120305, by rfl⟩ : syracuseStep 2566517 = 240611) (by norm_num)
theorem B2083205 : Blo 1709055 2083205 := bbase (se 4 (by rfl) ⟨195300, by rfl⟩ : syracuseStep 2083205 = 390601) (by norm_num)
theorem B2165125 : Blo 1709055 2165125 := bbase (se 4 (by rfl) ⟨202980, by rfl⟩ : syracuseStep 2165125 = 405961) (by norm_num)
theorem B2566541 : Blo 1709055 2566541 := bbase (se 3 (by rfl) ⟨481226, by rfl⟩ : syracuseStep 2566541 = 962453) (by norm_num)
theorem B2566565 : Blo 1709055 2566565 := bbase (se 4 (by rfl) ⟨240615, by rfl⟩ : syracuseStep 2566565 = 481231) (by norm_num)
theorem B6244789 : Blo 1709055 6244789 := bbase (se 5 (by rfl) ⟨292724, by rfl⟩ : syracuseStep 6244789 = 585449) (by norm_num)
theorem B2886077 : Blo 1709055 2886077 := bbase (se 3 (by rfl) ⟨541139, by rfl⟩ : syracuseStep 2886077 = 1082279) (by norm_num)
theorem B7301573 : Blo 1709055 7301573 := bbase (se 4 (by rfl) ⟨684522, by rfl⟩ : syracuseStep 7301573 = 1369045) (by norm_num)
theorem B4327901 : Blo 1709055 4327901 := bbase (se 3 (by rfl) ⟨811481, by rfl⟩ : syracuseStep 4327901 = 1622963) (by norm_num)
theorem B4868581 : Blo 1709055 4868581 := bbase (se 4 (by rfl) ⟨456429, by rfl⟩ : syracuseStep 4868581 = 912859) (by norm_num)
theorem B2165221 : Blo 1709055 2165221 := bbase (se 4 (by rfl) ⟨202989, by rfl⟩ : syracuseStep 2165221 = 405979) (by norm_num)
theorem B2083321 : Blo 1709055 2083321 := bbase (se 2 (by rfl) ⟨781245, by rfl⟩ : syracuseStep 2083321 = 1562491) (by norm_num)
theorem B2468381 : Blo 1709055 2468381 := bbase (se 3 (by rfl) ⟨462821, by rfl⟩ : syracuseStep 2468381 = 925643) (by norm_num)
theorem B2886205 : Blo 1709055 2886205 := bbase (se 3 (by rfl) ⟨541163, by rfl⟩ : syracuseStep 2886205 = 1082327) (by norm_num)
theorem B5769845 : Blo 1709055 5769845 := bbase (se 5 (by rfl) ⟨270461, by rfl⟩ : syracuseStep 5769845 = 540923) (by norm_num)
theorem B4868741 : Blo 1709055 4868741 := bbase (se 4 (by rfl) ⟨456444, by rfl⟩ : syracuseStep 4868741 = 912889) (by norm_num)
theorem B2165393 : Blo 1709055 2165393 := bbase (se 2 (by rfl) ⟨812022, by rfl⟩ : syracuseStep 2165393 = 1624045) (by norm_num)
theorem B2886293 : Blo 1709055 2886293 := bbase (se 6 (by rfl) ⟨67647, by rfl⟩ : syracuseStep 2886293 = 135295) (by norm_num)
theorem B5417621 : Blo 1709055 5417621 := bbase (se 6 (by rfl) ⟨126975, by rfl⟩ : syracuseStep 5417621 = 253951) (by norm_num)
theorem B8661653 : Blo 1709055 8661653 := bbase (se 6 (by rfl) ⟨203007, by rfl⟩ : syracuseStep 8661653 = 406015) (by norm_num)
theorem B4328093 : Blo 1709055 4328093 := bbase (se 3 (by rfl) ⟨811517, by rfl⟩ : syracuseStep 4328093 = 1623035) (by norm_num)
theorem B2165449 : Blo 1709055 2165449 := bbase (se 2 (by rfl) ⟨812043, by rfl⟩ : syracuseStep 2165449 = 1624087) (by norm_num)
theorem B4106981 : Blo 1709055 4106981 := bbase (se 4 (by rfl) ⟨385029, by rfl⟩ : syracuseStep 4106981 = 770059) (by norm_num)
theorem B2886421 : Blo 1709055 2886421 := bbase (se 6 (by rfl) ⟨67650, by rfl⟩ : syracuseStep 2886421 = 135301) (by norm_num)
theorem B2165545 : Blo 1709055 2165545 := bbase (se 2 (by rfl) ⟨812079, by rfl⟩ : syracuseStep 2165545 = 1624159) (by norm_num)
theorem B1756009 : Blo 1709055 1756009 := bbase (se 2 (by rfl) ⟨658503, by rfl⟩ : syracuseStep 1756009 = 1317007) (by norm_num)
theorem B2886509 : Blo 1709055 2886509 := bbase (se 3 (by rfl) ⟨541220, by rfl⟩ : syracuseStep 2886509 = 1082441) (by norm_num)
theorem B4868981 : Blo 1709055 4868981 := bbase (se 5 (by rfl) ⟨228233, by rfl⟩ : syracuseStep 4868981 = 456467) (by norm_num)
theorem B7908293 : Blo 1709055 7908293 := bbase (se 4 (by rfl) ⟨741402, by rfl⟩ : syracuseStep 7908293 = 1482805) (by norm_num)
theorem B2886637 : Blo 1709055 2886637 := bbase (se 3 (by rfl) ⟨541244, by rfl⟩ : syracuseStep 2886637 = 1082489) (by norm_num)
theorem B4328437 : Blo 1709055 4328437 := bbase (se 5 (by rfl) ⟨202895, by rfl⟩ : syracuseStep 4328437 = 405791) (by norm_num)
theorem B2436085 : Blo 1709055 2436085 := bbase (se 5 (by rfl) ⟨114191, by rfl⟩ : syracuseStep 2436085 = 228383) (by norm_num)
theorem B5770277 : Blo 1709055 5770277 := bbase (se 4 (by rfl) ⟨540963, by rfl⟩ : syracuseStep 5770277 = 1081927) (by norm_num)
theorem B3247141 : Blo 1709055 3247141 := bbase (se 4 (by rfl) ⟨304419, by rfl⟩ : syracuseStep 3247141 = 608839) (by norm_num)
theorem B7400501 : Blo 1709055 7400501 := bbase (se 5 (by rfl) ⟨346898, by rfl⟩ : syracuseStep 7400501 = 693797) (by norm_num)
theorem B8653877 : Blo 1709055 8653877 := bbase (se 5 (by rfl) ⟨405650, by rfl⟩ : syracuseStep 8653877 = 811301) (by norm_num)
theorem B4869173 : Blo 1709055 4869173 := bbase (se 5 (by rfl) ⟨228242, by rfl⟩ : syracuseStep 4869173 = 456485) (by norm_num)
theorem B2739269 : Blo 1709055 2739269 := bbase (se 4 (by rfl) ⟨256806, by rfl⟩ : syracuseStep 2739269 = 513613) (by norm_num)
theorem B2886725 : Blo 1709055 2886725 := bbase (se 4 (by rfl) ⟨270630, by rfl⟩ : syracuseStep 2886725 = 541261) (by norm_num)
theorem B2600021 : Blo 1709055 2600021 := bbase (se 8 (by rfl) ⟨15234, by rfl⟩ : syracuseStep 2600021 = 30469) (by norm_num)
theorem B4328549 : Blo 1709055 4328549 := bbase (se 4 (by rfl) ⟨405801, by rfl⟩ : syracuseStep 4328549 = 811603) (by norm_num)
theorem B7302325 : Blo 1709055 7302325 := bbase (se 5 (by rfl) ⟨342296, by rfl⟩ : syracuseStep 7302325 = 684593) (by norm_num)
theorem B3247285 : Blo 1709055 3247285 := bbase (se 5 (by rfl) ⟨152216, by rfl⟩ : syracuseStep 3247285 = 304433) (by norm_num)
theorem B2886853 : Blo 1709055 2886853 := bbase (se 4 (by rfl) ⟨270642, by rfl⟩ : syracuseStep 2886853 = 541285) (by norm_num)
theorem B2886941 : Blo 1709055 2886941 := bbase (se 3 (by rfl) ⟨541301, by rfl⟩ : syracuseStep 2886941 = 1082603) (by norm_num)
theorem B4328741 : Blo 1709055 4328741 := bbase (se 4 (by rfl) ⟨405819, by rfl⟩ : syracuseStep 4328741 = 811639) (by norm_num)
theorem B3845429 : Blo 1709055 3845429 := bbase (se 5 (by rfl) ⟨180254, by rfl⟩ : syracuseStep 3845429 = 360509) (by norm_num)
theorem B3247445 : Blo 1709055 3247445 := bbase (se 11 (by rfl) ⟨2378, by rfl⟩ : syracuseStep 3247445 = 4757) (by norm_num)
theorem B11701621 : Blo 1709055 11701621 := bbase (se 5 (by rfl) ⟨548513, by rfl⟩ : syracuseStep 11701621 = 1097027) (by norm_num)
theorem B3845501 : Blo 1709055 3845501 := bbase (se 3 (by rfl) ⟨721031, by rfl⟩ : syracuseStep 3845501 = 1442063) (by norm_num)
theorem B8220037 : Blo 1709055 8220037 := bbase (se 4 (by rfl) ⟨770628, by rfl⟩ : syracuseStep 8220037 = 1541257) (by norm_num)
theorem B2887069 : Blo 1709055 2887069 := bbase (se 3 (by rfl) ⟨541325, by rfl⟩ : syracuseStep 2887069 = 1082651) (by norm_num)
theorem B4386221 : Blo 1709055 4386221 := bbase (se 3 (by rfl) ⟨822416, by rfl⟩ : syracuseStep 4386221 = 1644833) (by norm_num)
theorem B3845573 : Blo 1709055 3845573 := bbase (se 4 (by rfl) ⟨360522, by rfl⟩ : syracuseStep 3845573 = 721045) (by norm_num)
theorem B43814357 : Blo 1709055 43814357 := bbase (se 7 (by rfl) ⟨513449, by rfl⟩ : syracuseStep 43814357 = 1026899) (by norm_num)
theorem B5770709 : Blo 1709055 5770709 := bbase (se 7 (by rfl) ⟨67625, by rfl⟩ : syracuseStep 5770709 = 135251) (by norm_num)
theorem B3247589 : Blo 1709055 3247589 := bbase (se 4 (by rfl) ⟨304461, by rfl⟩ : syracuseStep 3247589 = 608923) (by norm_num)
theorem B2887157 : Blo 1709055 2887157 := bbase (se 5 (by rfl) ⟨135335, by rfl⟩ : syracuseStep 2887157 = 270671) (by norm_num)
theorem B3845645 : Blo 1709055 3845645 := bbase (se 3 (by rfl) ⟨721058, by rfl⟩ : syracuseStep 3845645 = 1442117) (by norm_num)
theorem B3845717 : Blo 1709055 3845717 := bbase (se 8 (by rfl) ⟨22533, by rfl⟩ : syracuseStep 3845717 = 45067) (by norm_num)
theorem B2887285 : Blo 1709055 2887285 := bbase (se 5 (by rfl) ⟨135341, by rfl⟩ : syracuseStep 2887285 = 270683) (by norm_num)
theorem B4329085 : Blo 1709055 4329085 := bbase (se 3 (by rfl) ⟨811703, by rfl⟩ : syracuseStep 4329085 = 1623407) (by norm_num)
theorem B27741845 : Blo 1709055 27741845 := bbase (se 6 (by rfl) ⟨650199, by rfl⟩ : syracuseStep 27741845 = 1300399) (by norm_num)
theorem B3845789 : Blo 1709055 3845789 := bbase (se 3 (by rfl) ⟨721085, by rfl⟩ : syracuseStep 3845789 = 1442171) (by norm_num)
theorem B5852837 : Blo 1709055 5852837 := bbase (se 4 (by rfl) ⟨548703, by rfl⟩ : syracuseStep 5852837 = 1097407) (by norm_num)
theorem B2887373 : Blo 1709055 2887373 := bbase (se 3 (by rfl) ⟨541382, by rfl⟩ : syracuseStep 2887373 = 1082765) (by norm_num)
theorem B3845861 : Blo 1709055 3845861 := bbase (se 4 (by rfl) ⟨360549, by rfl⟩ : syracuseStep 3845861 = 721099) (by norm_num)
theorem B4329197 : Blo 1709055 4329197 := bbase (se 3 (by rfl) ⟨811724, by rfl⟩ : syracuseStep 4329197 = 1623449) (by norm_num)
theorem B3247877 : Blo 1709055 3247877 := bbase (se 4 (by rfl) ⟨304488, by rfl⟩ : syracuseStep 3247877 = 608977) (by norm_num)
theorem B3845933 : Blo 1709055 3845933 := bbase (se 3 (by rfl) ⟨721112, by rfl⟩ : syracuseStep 3845933 = 1442225) (by norm_num)
theorem B11702069 : Blo 1709055 11702069 := bbase (se 5 (by rfl) ⟨548534, by rfl⟩ : syracuseStep 11702069 = 1097069) (by norm_num)
theorem B4386653 : Blo 1709055 4386653 := bbase (se 3 (by rfl) ⟨822497, by rfl⟩ : syracuseStep 4386653 = 1644995) (by norm_num)
theorem B3846005 : Blo 1709055 3846005 := bbase (se 5 (by rfl) ⟨180281, by rfl⟩ : syracuseStep 3846005 = 360563) (by norm_num)
theorem B5771141 : Blo 1709055 5771141 := bbase (se 4 (by rfl) ⟨541044, by rfl⟩ : syracuseStep 5771141 = 1082089) (by norm_num)
theorem B7303061 : Blo 1709055 7303061 := bbase (se 6 (by rfl) ⟨171165, by rfl⟩ : syracuseStep 7303061 = 342331) (by norm_num)
theorem B3248029 : Blo 1709055 3248029 := bbase (se 3 (by rfl) ⟨609005, by rfl⟩ : syracuseStep 3248029 = 1218011) (by norm_num)
theorem B4329389 : Blo 1709055 4329389 := bbase (se 3 (by rfl) ⟨811760, by rfl⟩ : syracuseStep 4329389 = 1623521) (by norm_num)
theorem B3846077 : Blo 1709055 3846077 := bbase (se 3 (by rfl) ⟨721139, by rfl⟩ : syracuseStep 3846077 = 1442279) (by norm_num)
theorem B2740205 : Blo 1709055 2740205 := bbase (se 3 (by rfl) ⟨513788, by rfl⟩ : syracuseStep 2740205 = 1027577) (by norm_num)
theorem B1732609 : Blo 1709055 1732609 := bbase (se 2 (by rfl) ⟨649728, by rfl⟩ : syracuseStep 1732609 = 1299457) (by norm_num)
theorem B3846149 : Blo 1709055 3846149 := bbase (se 4 (by rfl) ⟨360576, by rfl⟩ : syracuseStep 3846149 = 721153) (by norm_num)
theorem B13340693 : Blo 1709055 13340693 := bbase (se 6 (by rfl) ⟨312672, by rfl⟩ : syracuseStep 13340693 = 625345) (by norm_num)
theorem B4870165 : Blo 1709055 4870165 := bbase (se 6 (by rfl) ⟨114144, by rfl⟩ : syracuseStep 4870165 = 228289) (by norm_num)
theorem B3846221 : Blo 1709055 3846221 := bbase (se 3 (by rfl) ⟨721166, by rfl⟩ : syracuseStep 3846221 = 1442333) (by norm_num)
theorem B2502749 : Blo 1709055 2502749 := bbase (se 3 (by rfl) ⟨469265, by rfl⟩ : syracuseStep 2502749 = 938531) (by norm_num)
theorem B3846293 : Blo 1709055 3846293 := bbase (se 6 (by rfl) ⟨90147, by rfl⟩ : syracuseStep 3846293 = 180295) (by norm_num)
theorem B3248333 : Blo 1709055 3248333 := bbase (se 3 (by rfl) ⟨609062, by rfl⟩ : syracuseStep 3248333 = 1218125) (by norm_num)
theorem B3846365 : Blo 1709055 3846365 := bbase (se 3 (by rfl) ⟨721193, by rfl⟩ : syracuseStep 3846365 = 1442387) (by norm_num)
theorem B4329733 : Blo 1709055 4329733 := bbase (se 4 (by rfl) ⟨405912, by rfl⟩ : syracuseStep 4329733 = 811825) (by norm_num)
theorem B3846437 : Blo 1709055 3846437 := bbase (se 4 (by rfl) ⟨360603, by rfl⟩ : syracuseStep 3846437 = 721207) (by norm_num)
theorem B5771573 : Blo 1709055 5771573 := bbase (se 5 (by rfl) ⟨270542, by rfl⟩ : syracuseStep 5771573 = 541085) (by norm_num)
theorem B8655173 : Blo 1709055 8655173 := bbase (se 4 (by rfl) ⟨811422, by rfl⟩ : syracuseStep 8655173 = 1622845) (by norm_num)
theorem B5476693 : Blo 1709055 5476693 := bbase (se 10 (by rfl) ⟨8022, by rfl⟩ : syracuseStep 5476693 = 16045) (by norm_num)
theorem B9744725 : Blo 1709055 9744725 := bbase (se 10 (by rfl) ⟨14274, by rfl⟩ : syracuseStep 9744725 = 28549) (by norm_num)
theorem B3846509 : Blo 1709055 3846509 := bbase (se 3 (by rfl) ⟨721220, by rfl⟩ : syracuseStep 3846509 = 1442441) (by norm_num)
theorem B5271925 : Blo 1709055 5271925 := bbase (se 5 (by rfl) ⟨247121, by rfl⟩ : syracuseStep 5271925 = 494243) (by norm_num)
theorem B4329845 : Blo 1709055 4329845 := bbase (se 5 (by rfl) ⟨202961, by rfl⟩ : syracuseStep 4329845 = 405923) (by norm_num)
theorem B6492581 : Blo 1709055 6492581 := bbase (se 4 (by rfl) ⟨608679, by rfl⟩ : syracuseStep 6492581 = 1217359) (by norm_num)
theorem B3846581 : Blo 1709055 3846581 := bbase (se 5 (by rfl) ⟨180308, by rfl⟩ : syracuseStep 3846581 = 360617) (by norm_num)
theorem B24654293 : Blo 1709055 24654293 := bbase (se 7 (by rfl) ⟨288917, by rfl⟩ : syracuseStep 24654293 = 577835) (by norm_num)
theorem B3846653 : Blo 1709055 3846653 := bbase (se 3 (by rfl) ⟨721247, by rfl⟩ : syracuseStep 3846653 = 1442495) (by norm_num)
theorem B4330037 : Blo 1709055 4330037 := bbase (se 5 (by rfl) ⟨202970, by rfl⟩ : syracuseStep 4330037 = 405941) (by norm_num)
theorem B3846725 : Blo 1709055 3846725 := bbase (se 4 (by rfl) ⟨360630, by rfl⟩ : syracuseStep 3846725 = 721261) (by norm_num)
theorem B13873781 : Blo 1709055 13873781 := bbase (se 5 (by rfl) ⟨650333, by rfl⟩ : syracuseStep 13873781 = 1300667) (by norm_num)
theorem B3846797 : Blo 1709055 3846797 := bbase (se 3 (by rfl) ⟨721274, by rfl⟩ : syracuseStep 3846797 = 1442549) (by norm_num)
theorem B4108981 : Blo 1709055 4108981 := bbase (se 5 (by rfl) ⟨192608, by rfl⟩ : syracuseStep 4108981 = 385217) (by norm_num)
theorem B6492869 : Blo 1709055 6492869 := bbase (se 4 (by rfl) ⟨608706, by rfl⟩ : syracuseStep 6492869 = 1217413) (by norm_num)
theorem B3846869 : Blo 1709055 3846869 := bbase (se 7 (by rfl) ⟨45080, by rfl⟩ : syracuseStep 3846869 = 90161) (by norm_num)
theorem B5772005 : Blo 1709055 5772005 := bbase (se 4 (by rfl) ⟨541125, by rfl⟩ : syracuseStep 5772005 = 1082251) (by norm_num)
theorem B4109077 : Blo 1709055 4109077 := bbase (se 6 (by rfl) ⟨96306, by rfl⟩ : syracuseStep 4109077 = 192613) (by norm_num)
theorem B10957589 : Blo 1709055 10957589 := bbase (se 6 (by rfl) ⟨256818, by rfl⟩ : syracuseStep 10957589 = 513637) (by norm_num)
theorem B3846941 : Blo 1709055 3846941 := bbase (se 3 (by rfl) ⟨721301, by rfl⟩ : syracuseStep 3846941 = 1442603) (by norm_num)
theorem B3847013 : Blo 1709055 3847013 := bbase (se 4 (by rfl) ⟨360657, by rfl⟩ : syracuseStep 3847013 = 721315) (by norm_num)
theorem B3650437 : Blo 1709055 3650437 := bbase (se 4 (by rfl) ⟨342228, by rfl⟩ : syracuseStep 3650437 = 684457) (by norm_num)
theorem B4330381 : Blo 1709055 4330381 := bbase (se 3 (by rfl) ⟨811946, by rfl⟩ : syracuseStep 4330381 = 1623893) (by norm_num)
theorem B3847085 : Blo 1709055 3847085 := bbase (se 3 (by rfl) ⟨721328, by rfl⟩ : syracuseStep 3847085 = 1442657) (by norm_num)
theorem B3847157 : Blo 1709055 3847157 := bbase (se 5 (by rfl) ⟨180335, by rfl⟩ : syracuseStep 3847157 = 360671) (by norm_num)
theorem B4330493 : Blo 1709055 4330493 := bbase (se 3 (by rfl) ⟨811967, by rfl⟩ : syracuseStep 4330493 = 1623935) (by norm_num)
theorem B3847229 : Blo 1709055 3847229 := bbase (se 3 (by rfl) ⟨721355, by rfl⟩ : syracuseStep 3847229 = 1442711) (by norm_num)
theorem B4871269 : Blo 1709055 4871269 := bbase (se 4 (by rfl) ⟨456681, by rfl⟩ : syracuseStep 4871269 = 913363) (by norm_num)
theorem B3847301 : Blo 1709055 3847301 := bbase (se 4 (by rfl) ⟨360684, by rfl⟩ : syracuseStep 3847301 = 721369) (by norm_num)
theorem B5772437 : Blo 1709055 5772437 := bbase (se 6 (by rfl) ⟨135291, by rfl⟩ : syracuseStep 5772437 = 270583) (by norm_num)
theorem B4330685 : Blo 1709055 4330685 := bbase (se 3 (by rfl) ⟨812003, by rfl⟩ : syracuseStep 4330685 = 1624007) (by norm_num)
theorem B3847373 : Blo 1709055 3847373 := bbase (se 3 (by rfl) ⟨721382, by rfl⟩ : syracuseStep 3847373 = 1442765) (by norm_num)
theorem B3699965 : Blo 1709055 3699965 := bbase (se 3 (by rfl) ⟨693743, by rfl⟩ : syracuseStep 3699965 = 1387487) (by norm_num)
theorem B8779013 : Blo 1709055 8779013 := bbase (se 4 (by rfl) ⟨823032, by rfl⟩ : syracuseStep 8779013 = 1646065) (by norm_num)
theorem B10827029 : Blo 1709055 10827029 := bbase (se 6 (by rfl) ⟨253758, by rfl⟩ : syracuseStep 10827029 = 507517) (by norm_num)
theorem B3847445 : Blo 1709055 3847445 := bbase (se 6 (by rfl) ⟨90174, by rfl⟩ : syracuseStep 3847445 = 180349) (by norm_num)
theorem B2053453 : Blo 1709055 2053453 := bbase (se 3 (by rfl) ⟨385022, by rfl⟩ : syracuseStep 2053453 = 770045) (by norm_num)
theorem B3847517 : Blo 1709055 3847517 := bbase (se 3 (by rfl) ⟨721409, by rfl⟩ : syracuseStep 3847517 = 1442819) (by norm_num)
theorem B3847589 : Blo 1709055 3847589 := bbase (se 4 (by rfl) ⟨360711, by rfl⟩ : syracuseStep 3847589 = 721423) (by norm_num)
theorem B2053549 : Blo 1709055 2053549 := bbase (se 3 (by rfl) ⟨385040, by rfl⟩ : syracuseStep 2053549 = 770081) (by norm_num)
theorem B9876917 : Blo 1709055 9876917 := bbase (se 5 (by rfl) ⟨462980, by rfl⟩ : syracuseStep 9876917 = 925961) (by norm_num)
theorem B1734089 : Blo 1709055 1734089 := bbase (se 2 (by rfl) ⟨650283, by rfl⟩ : syracuseStep 1734089 = 1300567) (by norm_num)
theorem B3847661 : Blo 1709055 3847661 := bbase (se 3 (by rfl) ⟨721436, by rfl⟩ : syracuseStep 3847661 = 1442873) (by norm_num)
theorem B4388357 : Blo 1709055 4388357 := bbase (se 4 (by rfl) ⟨411408, by rfl⟩ : syracuseStep 4388357 = 822817) (by norm_num)
theorem B4331029 : Blo 1709055 4331029 := bbase (se 6 (by rfl) ⟨101508, by rfl⟩ : syracuseStep 4331029 = 203017) (by norm_num)
theorem B3847733 : Blo 1709055 3847733 := bbase (se 5 (by rfl) ⟨180362, by rfl⟩ : syracuseStep 3847733 = 360725) (by norm_num)
theorem B5772869 : Blo 1709055 5772869 := bbase (se 4 (by rfl) ⟨541206, by rfl⟩ : syracuseStep 5772869 = 1082413) (by norm_num)
theorem B8656469 : Blo 1709055 8656469 := bbase (se 8 (by rfl) ⟨50721, by rfl⟩ : syracuseStep 8656469 = 101443) (by norm_num)
theorem B3847805 : Blo 1709055 3847805 := bbase (se 3 (by rfl) ⟨721463, by rfl⟩ : syracuseStep 3847805 = 1442927) (by norm_num)
theorem B1922701 : Blo 1709055 1922701 := bbase (se 3 (by rfl) ⟨360506, by rfl⟩ : syracuseStep 1922701 = 721013) (by norm_num)
theorem B4445837 : Blo 1709055 4445837 := bbase (se 3 (by rfl) ⟨833594, by rfl⟩ : syracuseStep 4445837 = 1667189) (by norm_num)
theorem B1922737 : Blo 1709055 1922737 := bbase (se 2 (by rfl) ⟨721026, by rfl⟩ : syracuseStep 1922737 = 1442053) (by norm_num)
theorem B3847877 : Blo 1709055 3847877 := bbase (se 4 (by rfl) ⟨360738, by rfl⟩ : syracuseStep 3847877 = 721477) (by norm_num)
theorem B2053837 : Blo 1709055 2053837 := bbase (se 3 (by rfl) ⟨385094, by rfl⟩ : syracuseStep 2053837 = 770189) (by norm_num)
theorem B1922773 : Blo 1709055 1922773 := bbase (se 7 (by rfl) ⟨22532, by rfl⟩ : syracuseStep 1922773 = 45065) (by norm_num)
theorem B10401493 : Blo 1709055 10401493 := bbase (se 7 (by rfl) ⟨121892, by rfl⟩ : syracuseStep 10401493 = 243785) (by norm_num)
theorem B1922809 : Blo 1709055 1922809 := bbase (se 2 (by rfl) ⟨721053, by rfl⟩ : syracuseStep 1922809 = 1442107) (by norm_num)
theorem B3847949 : Blo 1709055 3847949 := bbase (se 3 (by rfl) ⟨721490, by rfl⟩ : syracuseStep 3847949 = 1442981) (by norm_num)
theorem B1922845 : Blo 1709055 1922845 := bbase (se 3 (by rfl) ⟨360533, by rfl⟩ : syracuseStep 1922845 = 721067) (by norm_num)
theorem B1922881 : Blo 1709055 1922881 := bbase (se 2 (by rfl) ⟨721080, by rfl⟩ : syracuseStep 1922881 = 1442161) (by norm_num)
theorem B3848021 : Blo 1709055 3848021 := bbase (se 9 (by rfl) ⟨11273, by rfl⟩ : syracuseStep 3848021 = 22547) (by norm_num)
theorem B12990293 : Blo 1709055 12990293 := bbase (se 9 (by rfl) ⟨38057, by rfl⟩ : syracuseStep 12990293 = 76115) (by norm_num)
theorem B4110173 : Blo 1709055 4110173 := bbase (se 3 (by rfl) ⟨770657, by rfl⟩ : syracuseStep 4110173 = 1541315) (by norm_num)
theorem B1922917 : Blo 1709055 1922917 := bbase (se 4 (by rfl) ⟨180273, by rfl⟩ : syracuseStep 1922917 = 360547) (by norm_num)
theorem B6494053 : Blo 1709055 6494053 := bbase (se 4 (by rfl) ⟨608817, by rfl⟩ : syracuseStep 6494053 = 1217635) (by norm_num)
theorem B1922953 : Blo 1709055 1922953 := bbase (se 2 (by rfl) ⟨721107, by rfl⟩ : syracuseStep 1922953 = 1442215) (by norm_num)
theorem B2054029 : Blo 1709055 2054029 := bbase (se 3 (by rfl) ⟨385130, by rfl⟩ : syracuseStep 2054029 = 770261) (by norm_num)
theorem B3848093 : Blo 1709055 3848093 := bbase (se 3 (by rfl) ⟨721517, by rfl⟩ : syracuseStep 3848093 = 1443035) (by norm_num)
theorem B1922989 : Blo 1709055 1922989 := bbase (se 3 (by rfl) ⟨360560, by rfl⟩ : syracuseStep 1922989 = 721121) (by norm_num)
theorem B6166469 : Blo 1709055 6166469 := bbase (se 4 (by rfl) ⟨578106, by rfl⟩ : syracuseStep 6166469 = 1156213) (by norm_num)
theorem B1923025 : Blo 1709055 1923025 := bbase (se 2 (by rfl) ⟨721134, by rfl⟩ : syracuseStep 1923025 = 1442269) (by norm_num)
theorem B3848165 : Blo 1709055 3848165 := bbase (se 4 (by rfl) ⟨360765, by rfl⟩ : syracuseStep 3848165 = 721531) (by norm_num)
theorem B1923061 : Blo 1709055 1923061 := bbase (se 5 (by rfl) ⟨90143, by rfl⟩ : syracuseStep 1923061 = 180287) (by norm_num)
theorem B5773301 : Blo 1709055 5773301 := bbase (se 5 (by rfl) ⟨270623, by rfl⟩ : syracuseStep 5773301 = 541247) (by norm_num)
theorem B1923097 : Blo 1709055 1923097 := bbase (se 2 (by rfl) ⟨721161, by rfl⟩ : syracuseStep 1923097 = 1442323) (by norm_num)
theorem B3848237 : Blo 1709055 3848237 := bbase (se 3 (by rfl) ⟨721544, by rfl⟩ : syracuseStep 3848237 = 1443089) (by norm_num)
theorem B1923133 : Blo 1709055 1923133 := bbase (se 3 (by rfl) ⟨360587, by rfl⟩ : syracuseStep 1923133 = 721175) (by norm_num)
theorem B1923169 : Blo 1709055 1923169 := bbase (se 2 (by rfl) ⟨721188, by rfl⟩ : syracuseStep 1923169 = 1442377) (by norm_num)
theorem B3848309 : Blo 1709055 3848309 := bbase (se 5 (by rfl) ⟨180389, by rfl⟩ : syracuseStep 3848309 = 360779) (by norm_num)
theorem B1923205 : Blo 1709055 1923205 := bbase (se 4 (by rfl) ⟨180300, by rfl⟩ : syracuseStep 1923205 = 360601) (by norm_num)
theorem B6494357 : Blo 1709055 6494357 := bbase (se 6 (by rfl) ⟨152211, by rfl⟩ : syracuseStep 6494357 = 304423) (by norm_num)
theorem B1923241 : Blo 1709055 1923241 := bbase (se 2 (by rfl) ⟨721215, by rfl⟩ : syracuseStep 1923241 = 1442431) (by norm_num)
theorem B3848381 : Blo 1709055 3848381 := bbase (se 3 (by rfl) ⟨721571, by rfl⟩ : syracuseStep 3848381 = 1443143) (by norm_num)
theorem B1923277 : Blo 1709055 1923277 := bbase (se 3 (by rfl) ⟨360614, by rfl⟩ : syracuseStep 1923277 = 721229) (by norm_num)
theorem B1923313 : Blo 1709055 1923313 := bbase (se 2 (by rfl) ⟨721242, by rfl⟩ : syracuseStep 1923313 = 1442485) (by norm_num)
theorem B12982517 : Blo 1709055 12982517 := bbase (se 5 (by rfl) ⟨608555, by rfl⟩ : syracuseStep 12982517 = 1217111) (by norm_num)
theorem B3848453 : Blo 1709055 3848453 := bbase (se 4 (by rfl) ⟨360792, by rfl⟩ : syracuseStep 3848453 = 721585) (by norm_num)
theorem B1923349 : Blo 1709055 1923349 := bbase (se 6 (by rfl) ⟨45078, by rfl⟩ : syracuseStep 1923349 = 90157) (by norm_num)
theorem B2193685 : Blo 1709055 2193685 := bbase (se 6 (by rfl) ⟨51414, by rfl⟩ : syracuseStep 2193685 = 102829) (by norm_num)
theorem B3512605 : Blo 1709055 3512605 := bbase (se 3 (by rfl) ⟨658613, by rfl⟩ : syracuseStep 3512605 = 1317227) (by norm_num)
theorem B1923385 : Blo 1709055 1923385 := bbase (se 2 (by rfl) ⟨721269, by rfl⟩ : syracuseStep 1923385 = 1442539) (by norm_num)
theorem B3848525 : Blo 1709055 3848525 := bbase (se 3 (by rfl) ⟨721598, by rfl⟩ : syracuseStep 3848525 = 1443197) (by norm_num)
theorem B1923421 : Blo 1709055 1923421 := bbase (se 3 (by rfl) ⟨360641, by rfl⟩ : syracuseStep 1923421 = 721283) (by norm_num)
theorem B3651941 : Blo 1709055 3651941 := bbase (se 4 (by rfl) ⟨342369, by rfl⟩ : syracuseStep 3651941 = 684739) (by norm_num)
theorem B1825129 : Blo 1709055 1825129 := bbase (se 2 (by rfl) ⟨684423, by rfl⟩ : syracuseStep 1825129 = 1368847) (by norm_num)
theorem B1923457 : Blo 1709055 1923457 := bbase (se 2 (by rfl) ⟨721296, by rfl⟩ : syracuseStep 1923457 = 1442593) (by norm_num)
theorem B2193809 : Blo 1709055 2193809 := bbase (se 2 (by rfl) ⟨822678, by rfl⟩ : syracuseStep 2193809 = 1645357) (by norm_num)
theorem B3848597 : Blo 1709055 3848597 := bbase (se 6 (by rfl) ⟨90201, by rfl⟩ : syracuseStep 3848597 = 180403) (by norm_num)
theorem B1923493 : Blo 1709055 1923493 := bbase (se 4 (by rfl) ⟨180327, by rfl⟩ : syracuseStep 1923493 = 360655) (by norm_num)
theorem B5773733 : Blo 1709055 5773733 := bbase (se 4 (by rfl) ⟨541287, by rfl⟩ : syracuseStep 5773733 = 1082575) (by norm_num)
theorem B8214965 : Blo 1709055 8214965 := bbase (se 5 (by rfl) ⟨385076, by rfl⟩ : syracuseStep 8214965 = 770153) (by norm_num)
theorem B1923529 : Blo 1709055 1923529 := bbase (se 2 (by rfl) ⟨721323, by rfl⟩ : syracuseStep 1923529 = 1442647) (by norm_num)
theorem B3848669 : Blo 1709055 3848669 := bbase (se 3 (by rfl) ⟨721625, by rfl⟩ : syracuseStep 3848669 = 1443251) (by norm_num)
theorem B1923565 : Blo 1709055 1923565 := bbase (se 3 (by rfl) ⟨360668, by rfl⟩ : syracuseStep 1923565 = 721337) (by norm_num)
theorem B3652085 : Blo 1709055 3652085 := bbase (se 5 (by rfl) ⟨171191, by rfl⟩ : syracuseStep 3652085 = 342383) (by norm_num)
theorem B1923601 : Blo 1709055 1923601 := bbase (se 2 (by rfl) ⟨721350, by rfl⟩ : syracuseStep 1923601 = 1442701) (by norm_num)
theorem B3848741 : Blo 1709055 3848741 := bbase (se 4 (by rfl) ⟨360819, by rfl⟩ : syracuseStep 3848741 = 721639) (by norm_num)
theorem B1923637 : Blo 1709055 1923637 := bbase (se 5 (by rfl) ⟨90170, by rfl⟩ : syracuseStep 1923637 = 180341) (by norm_num)
theorem B13163093 : Blo 1709055 13163093 := bbase (se 8 (by rfl) ⟨77127, by rfl⟩ : syracuseStep 13163093 = 154255) (by norm_num)
theorem B1923673 : Blo 1709055 1923673 := bbase (se 2 (by rfl) ⟨721377, by rfl⟩ : syracuseStep 1923673 = 1442755) (by norm_num)
theorem B3848813 : Blo 1709055 3848813 := bbase (se 3 (by rfl) ⟨721652, by rfl⟩ : syracuseStep 3848813 = 1443305) (by norm_num)
theorem B1923709 : Blo 1709055 1923709 := bbase (se 3 (by rfl) ⟨360695, by rfl⟩ : syracuseStep 1923709 = 721391) (by norm_num)
theorem B1923745 : Blo 1709055 1923745 := bbase (se 2 (by rfl) ⟨721404, by rfl⟩ : syracuseStep 1923745 = 1442809) (by norm_num)
theorem B3848885 : Blo 1709055 3848885 := bbase (se 5 (by rfl) ⟨180416, by rfl⟩ : syracuseStep 3848885 = 360833) (by norm_num)
theorem B1923781 : Blo 1709055 1923781 := bbase (se 4 (by rfl) ⟨180354, by rfl⟩ : syracuseStep 1923781 = 360709) (by norm_num)
theorem B20798165 : Blo 1709055 20798165 := bbase (se 7 (by rfl) ⟨243728, by rfl⟩ : syracuseStep 20798165 = 487457) (by norm_num)
theorem B1923817 : Blo 1709055 1923817 := bbase (se 2 (by rfl) ⟨721431, by rfl⟩ : syracuseStep 1923817 = 1442863) (by norm_num)
theorem B2054909 : Blo 1709055 2054909 := bbase (se 3 (by rfl) ⟨385295, by rfl⟩ : syracuseStep 2054909 = 770591) (by norm_num)
theorem B3848957 : Blo 1709055 3848957 := bbase (se 3 (by rfl) ⟨721679, by rfl⟩ : syracuseStep 3848957 = 1443359) (by norm_num)
theorem B1923853 : Blo 1709055 1923853 := bbase (se 3 (by rfl) ⟨360722, by rfl⟩ : syracuseStep 1923853 = 721445) (by norm_num)
theorem B4111133 : Blo 1709055 4111133 := bbase (se 3 (by rfl) ⟨770837, by rfl⟩ : syracuseStep 4111133 = 1541675) (by norm_num)
theorem B1825573 : Blo 1709055 1825573 := bbase (se 4 (by rfl) ⟨171147, by rfl⟩ : syracuseStep 1825573 = 342295) (by norm_num)
theorem B1923889 : Blo 1709055 1923889 := bbase (se 2 (by rfl) ⟨721458, by rfl⟩ : syracuseStep 1923889 = 1442917) (by norm_num)
theorem B3849029 : Blo 1709055 3849029 := bbase (se 4 (by rfl) ⟨360846, by rfl⟩ : syracuseStep 3849029 = 721693) (by norm_num)
theorem B1923925 : Blo 1709055 1923925 := bbase (se 9 (by rfl) ⟨5636, by rfl⟩ : syracuseStep 1923925 = 11273) (by norm_num)
theorem B5774165 : Blo 1709055 5774165 := bbase (se 9 (by rfl) ⟨16916, by rfl⟩ : syracuseStep 5774165 = 33833) (by norm_num)
theorem B3652445 : Blo 1709055 3652445 := bbase (se 3 (by rfl) ⟨684833, by rfl⟩ : syracuseStep 3652445 = 1369667) (by norm_num)
theorem B8657765 : Blo 1709055 8657765 := bbase (se 4 (by rfl) ⟨811665, by rfl⟩ : syracuseStep 8657765 = 1623331) (by norm_num)
theorem B1923961 : Blo 1709055 1923961 := bbase (se 2 (by rfl) ⟨721485, by rfl⟩ : syracuseStep 1923961 = 1442971) (by norm_num)
theorem B3849101 : Blo 1709055 3849101 := bbase (se 3 (by rfl) ⟨721706, by rfl⟩ : syracuseStep 3849101 = 1443413) (by norm_num)
theorem B1923997 : Blo 1709055 1923997 := bbase (se 3 (by rfl) ⟨360749, by rfl⟩ : syracuseStep 1923997 = 721499) (by norm_num)
theorem B1825697 : Blo 1709055 1825697 := bbase (se 2 (by rfl) ⟨684636, by rfl⟩ : syracuseStep 1825697 = 1369273) (by norm_num)
theorem B1924033 : Blo 1709055 1924033 := bbase (se 2 (by rfl) ⟨721512, by rfl⟩ : syracuseStep 1924033 = 1443025) (by norm_num)
theorem B3849173 : Blo 1709055 3849173 := bbase (se 7 (by rfl) ⟨45107, by rfl⟩ : syracuseStep 3849173 = 90215) (by norm_num)
theorem B1924069 : Blo 1709055 1924069 := bbase (se 4 (by rfl) ⟨180381, by rfl⟩ : syracuseStep 1924069 = 360763) (by norm_num)
theorem B1850369 : Blo 1709055 1850369 := bbase (se 2 (by rfl) ⟨693888, by rfl⟩ : syracuseStep 1850369 = 1387777) (by norm_num)
theorem B1924105 : Blo 1709055 1924105 := bbase (se 2 (by rfl) ⟨721539, by rfl⟩ : syracuseStep 1924105 = 1443079) (by norm_num)
theorem B3849245 : Blo 1709055 3849245 := bbase (se 3 (by rfl) ⟨721733, by rfl⟩ : syracuseStep 3849245 = 1443467) (by norm_num)
theorem B1924141 : Blo 1709055 1924141 := bbase (se 3 (by rfl) ⟨360776, by rfl⟩ : syracuseStep 1924141 = 721553) (by norm_num)
theorem B1924177 : Blo 1709055 1924177 := bbase (se 2 (by rfl) ⟨721566, by rfl⟩ : syracuseStep 1924177 = 1443133) (by norm_num)
theorem B9739349 : Blo 1709055 9739349 := bbase (se 8 (by rfl) ⟨57066, by rfl⟩ : syracuseStep 9739349 = 114133) (by norm_num)
theorem B3849317 : Blo 1709055 3849317 := bbase (se 4 (by rfl) ⟨360873, by rfl⟩ : syracuseStep 3849317 = 721747) (by norm_num)
theorem B1924213 : Blo 1709055 1924213 := bbase (se 5 (by rfl) ⟨90197, by rfl⟩ : syracuseStep 1924213 = 180395) (by norm_num)
theorem B7306357 : Blo 1709055 7306357 := bbase (se 5 (by rfl) ⟨342485, by rfl⟩ : syracuseStep 7306357 = 684971) (by norm_num)
theorem B1924249 : Blo 1709055 1924249 := bbase (se 2 (by rfl) ⟨721593, by rfl⟩ : syracuseStep 1924249 = 1443187) (by norm_num)
theorem B1825949 : Blo 1709055 1825949 := bbase (se 3 (by rfl) ⟨342365, by rfl⟩ : syracuseStep 1825949 = 684731) (by norm_num)
theorem B5479589 : Blo 1709055 5479589 := bbase (se 4 (by rfl) ⟨513711, by rfl⟩ : syracuseStep 5479589 = 1027423) (by norm_num)
theorem B3849389 : Blo 1709055 3849389 := bbase (se 3 (by rfl) ⟨721760, by rfl⟩ : syracuseStep 3849389 = 1443521) (by norm_num)
theorem B1924285 : Blo 1709055 1924285 := bbase (se 3 (by rfl) ⟨360803, by rfl⟩ : syracuseStep 1924285 = 721607) (by norm_num)
theorem B1924321 : Blo 1709055 1924321 := bbase (se 2 (by rfl) ⟨721620, by rfl⟩ : syracuseStep 1924321 = 1443241) (by norm_num)
theorem B3849461 : Blo 1709055 3849461 := bbase (se 5 (by rfl) ⟨180443, by rfl⟩ : syracuseStep 3849461 = 360887) (by norm_num)
theorem B2055413 : Blo 1709055 2055413 := bbase (se 5 (by rfl) ⟨96347, by rfl⟩ : syracuseStep 2055413 = 192695) (by norm_num)
theorem B1924357 : Blo 1709055 1924357 := bbase (se 4 (by rfl) ⟨180408, by rfl⟩ : syracuseStep 1924357 = 360817) (by norm_num)
theorem B5774597 : Blo 1709055 5774597 := bbase (se 4 (by rfl) ⟨541368, by rfl⟩ : syracuseStep 5774597 = 1082737) (by norm_num)
theorem B12320021 : Blo 1709055 12320021 := bbase (se 6 (by rfl) ⟨288750, by rfl⟩ : syracuseStep 12320021 = 577501) (by norm_num)
theorem B2055461 : Blo 1709055 2055461 := bbase (se 4 (by rfl) ⟨192699, by rfl⟩ : syracuseStep 2055461 = 385399) (by norm_num)
theorem B1924393 : Blo 1709055 1924393 := bbase (se 2 (by rfl) ⟨721647, by rfl⟩ : syracuseStep 1924393 = 1443295) (by norm_num)
theorem B3849533 : Blo 1709055 3849533 := bbase (se 3 (by rfl) ⟨721787, by rfl⟩ : syracuseStep 3849533 = 1443575) (by norm_num)
theorem B1924429 : Blo 1709055 1924429 := bbase (se 3 (by rfl) ⟨360830, by rfl⟩ : syracuseStep 1924429 = 721661) (by norm_num)
theorem B1924465 : Blo 1709055 1924465 := bbase (se 2 (by rfl) ⟨721674, by rfl⟩ : syracuseStep 1924465 = 1443349) (by norm_num)
theorem B3849605 : Blo 1709055 3849605 := bbase (se 4 (by rfl) ⟨360900, by rfl⟩ : syracuseStep 3849605 = 721801) (by norm_num)
theorem B1924501 : Blo 1709055 1924501 := bbase (se 6 (by rfl) ⟨45105, by rfl⟩ : syracuseStep 1924501 = 90211) (by norm_num)
theorem B1949113 : Blo 1709055 1949113 := bbase (se 2 (by rfl) ⟨730917, by rfl⟩ : syracuseStep 1949113 = 1461835) (by norm_num)
theorem B1924537 : Blo 1709055 1924537 := bbase (se 2 (by rfl) ⟨721701, by rfl⟩ : syracuseStep 1924537 = 1443403) (by norm_num)
theorem B3849677 : Blo 1709055 3849677 := bbase (se 3 (by rfl) ⟨721814, by rfl⟩ : syracuseStep 3849677 = 1443629) (by norm_num)
theorem B1924573 : Blo 1709055 1924573 := bbase (se 3 (by rfl) ⟨360857, by rfl⟩ : syracuseStep 1924573 = 721715) (by norm_num)
theorem B4619749 : Blo 1709055 4619749 := bbase (se 4 (by rfl) ⟨433101, by rfl⟩ : syracuseStep 4619749 = 866203) (by norm_num)
theorem B1924609 : Blo 1709055 1924609 := bbase (se 2 (by rfl) ⟨721728, by rfl⟩ : syracuseStep 1924609 = 1443457) (by norm_num)
theorem B2563589 : Blo 1709055 2563589 := bbase (se 4 (by rfl) ⟨240336, by rfl⟩ : syracuseStep 2563589 = 480673) (by norm_num)
theorem B3849749 : Blo 1709055 3849749 := bbase (se 6 (by rfl) ⟨90228, by rfl⟩ : syracuseStep 3849749 = 180457) (by norm_num)
theorem B2563613 : Blo 1709055 2563613 := bbase (se 3 (by rfl) ⟨480677, by rfl⟩ : syracuseStep 2563613 = 961355) (by norm_num)
theorem B1924645 : Blo 1709055 1924645 := bbase (se 4 (by rfl) ⟨180435, by rfl⟩ : syracuseStep 1924645 = 360871) (by norm_num)
theorem B2563637 : Blo 1709055 2563637 := bbase (se 5 (by rfl) ⟨120170, by rfl⟩ : syracuseStep 2563637 = 240341) (by norm_num)
theorem B6159925 : Blo 1709055 6159925 := bbase (se 5 (by rfl) ⟨288746, by rfl⟩ : syracuseStep 6159925 = 577493) (by norm_num)
theorem B2924093 : Blo 1709055 2924093 := bbase (se 3 (by rfl) ⟨548267, by rfl⟩ : syracuseStep 2924093 = 1096535) (by norm_num)
theorem B1924681 : Blo 1709055 1924681 := bbase (se 2 (by rfl) ⟨721755, by rfl⟩ : syracuseStep 1924681 = 1443511) (by norm_num)
theorem B2563661 : Blo 1709055 2563661 := bbase (se 3 (by rfl) ⟨480686, by rfl⟩ : syracuseStep 2563661 = 961373) (by norm_num)
theorem B1826393 : Blo 1709055 1826393 := bbase (se 2 (by rfl) ⟨684897, by rfl⟩ : syracuseStep 1826393 = 1369795) (by norm_num)
theorem B3849821 : Blo 1709055 3849821 := bbase (se 3 (by rfl) ⟨721841, by rfl⟩ : syracuseStep 3849821 = 1443683) (by norm_num)
theorem B2563685 : Blo 1709055 2563685 := bbase (se 4 (by rfl) ⟨240345, by rfl⟩ : syracuseStep 2563685 = 480691) (by norm_num)
theorem B1924717 : Blo 1709055 1924717 := bbase (se 3 (by rfl) ⟨360884, by rfl⟩ : syracuseStep 1924717 = 721769) (by norm_num)
theorem B2563709 : Blo 1709055 2563709 := bbase (se 3 (by rfl) ⟨480695, by rfl⟩ : syracuseStep 2563709 = 961391) (by norm_num)
theorem B1924753 : Blo 1709055 1924753 := bbase (se 2 (by rfl) ⟨721782, by rfl⟩ : syracuseStep 1924753 = 1443565) (by norm_num)
theorem B2563733 : Blo 1709055 2563733 := bbase (se 6 (by rfl) ⟨60087, by rfl⟩ : syracuseStep 2563733 = 120175) (by norm_num)
theorem B6250133 : Blo 1709055 6250133 := bbase (se 6 (by rfl) ⟨146487, by rfl⟩ : syracuseStep 6250133 = 292975) (by norm_num)
theorem B2563757 : Blo 1709055 2563757 := bbase (se 3 (by rfl) ⟨480704, by rfl⟩ : syracuseStep 2563757 = 961409) (by norm_num)
theorem B1924789 : Blo 1709055 1924789 := bbase (se 5 (by rfl) ⟨90224, by rfl⟩ : syracuseStep 1924789 = 180449) (by norm_num)
theorem B2563781 : Blo 1709055 2563781 := bbase (se 4 (by rfl) ⟨240354, by rfl⟩ : syracuseStep 2563781 = 480709) (by norm_num)
theorem B3653333 : Blo 1709055 3653333 := bbase (se 7 (by rfl) ⟨42812, by rfl⟩ : syracuseStep 3653333 = 85625) (by norm_num)
theorem B1924825 : Blo 1709055 1924825 := bbase (se 2 (by rfl) ⟨721809, by rfl⟩ : syracuseStep 1924825 = 1443619) (by norm_num)
theorem B2563805 : Blo 1709055 2563805 := bbase (se 3 (by rfl) ⟨480713, by rfl⟩ : syracuseStep 2563805 = 961427) (by norm_num)
theorem B2563829 : Blo 1709055 2563829 := bbase (se 5 (by rfl) ⟨120179, by rfl⟩ : syracuseStep 2563829 = 240359) (by norm_num)
theorem B8216309 : Blo 1709055 8216309 := bbase (se 5 (by rfl) ⟨385139, by rfl⟩ : syracuseStep 8216309 = 770279) (by norm_num)
theorem B1924861 : Blo 1709055 1924861 := bbase (se 3 (by rfl) ⟨360911, by rfl⟩ : syracuseStep 1924861 = 721823) (by norm_num)
theorem B2563853 : Blo 1709055 2563853 := bbase (se 3 (by rfl) ⟨480722, by rfl⟩ : syracuseStep 2563853 = 961445) (by norm_num)
theorem B1924897 : Blo 1709055 1924897 := bbase (se 2 (by rfl) ⟨721836, by rfl⟩ : syracuseStep 1924897 = 1443673) (by norm_num)
theorem B2563877 : Blo 1709055 2563877 := bbase (se 4 (by rfl) ⟨240363, by rfl⟩ : syracuseStep 2563877 = 480727) (by norm_num)
theorem B2563901 : Blo 1709055 2563901 := bbase (se 3 (by rfl) ⟨480731, by rfl⟩ : syracuseStep 2563901 = 961463) (by norm_num)
theorem B1924933 : Blo 1709055 1924933 := bbase (se 4 (by rfl) ⟨180462, by rfl⟩ : syracuseStep 1924933 = 360925) (by norm_num)
theorem B1826641 : Blo 1709055 1826641 := bbase (se 2 (by rfl) ⟨684990, by rfl⟩ : syracuseStep 1826641 = 1369981) (by norm_num)
theorem B2563925 : Blo 1709055 2563925 := bbase (se 9 (by rfl) ⟨7511, by rfl⟩ : syracuseStep 2563925 = 15023) (by norm_num)
theorem B2563949 : Blo 1709055 2563949 := bbase (se 3 (by rfl) ⟨480740, by rfl⟩ : syracuseStep 2563949 = 961481) (by norm_num)
theorem B17792885 : Blo 1709055 17792885 := bbase (se 5 (by rfl) ⟨834041, by rfl⟩ : syracuseStep 17792885 = 1668083) (by norm_num)
theorem B2563973 : Blo 1709055 2563973 := bbase (se 4 (by rfl) ⟨240372, by rfl⟩ : syracuseStep 2563973 = 480745) (by norm_num)
theorem B2563997 : Blo 1709055 2563997 := bbase (se 3 (by rfl) ⟨480749, by rfl⟩ : syracuseStep 2563997 = 961499) (by norm_num)
theorem B2564021 : Blo 1709055 2564021 := bbase (se 5 (by rfl) ⟨120188, by rfl⟩ : syracuseStep 2564021 = 240377) (by norm_num)
theorem B2564045 : Blo 1709055 2564045 := bbase (se 3 (by rfl) ⟨480758, by rfl⟩ : syracuseStep 2564045 = 961517) (by norm_num)
theorem B3653581 : Blo 1709055 3653581 := bbase (se 3 (by rfl) ⟨685046, by rfl⟩ : syracuseStep 3653581 = 1370093) (by norm_num)
theorem B2564069 : Blo 1709055 2564069 := bbase (se 4 (by rfl) ⟨240381, by rfl⟩ : syracuseStep 2564069 = 480763) (by norm_num)
theorem B2564093 : Blo 1709055 2564093 := bbase (se 3 (by rfl) ⟨480767, by rfl⟩ : syracuseStep 2564093 = 961535) (by norm_num)
theorem B2564099 : Blo 1709055 2564099 := bstep (se 1 (by rfl) ⟨1923074, by rfl⟩ : syracuseStep 2564099 = 3846149) B3846149
theorem B9240581 : Blo 1709055 9240581 := bstep (se 4 (by rfl) ⟨866304, by rfl⟩ : syracuseStep 9240581 = 1732609) B1732609
theorem B2564129 : Blo 1709055 2564129 := bstep (se 2 (by rfl) ⟨961548, by rfl⟩ : syracuseStep 2564129 = 1923097) B1923097
theorem B2564147 : Blo 1709055 2564147 := bstep (se 1 (by rfl) ⟨1923110, by rfl⟩ : syracuseStep 2564147 = 3846221) B3846221
theorem B2564177 : Blo 1709055 2564177 := bstep (se 2 (by rfl) ⟨961566, by rfl⟩ : syracuseStep 2564177 = 1923133) B1923133
theorem B2564195 : Blo 1709055 2564195 := bstep (se 1 (by rfl) ⟨1923146, by rfl⟩ : syracuseStep 2564195 = 3846293) B3846293
theorem B14614627 : Blo 1709055 14614627 := bstep (se 1 (by rfl) ⟨10960970, by rfl⟩ : syracuseStep 14614627 = 21921941) B21921941
theorem B2564225 : Blo 1709055 2564225 := bstep (se 2 (by rfl) ⟨961584, by rfl⟩ : syracuseStep 2564225 = 1923169) B1923169
theorem B12984461 : Blo 1709055 12984461 := bstep (se 3 (by rfl) ⟨2434586, by rfl⟩ : syracuseStep 12984461 = 4869173) B4869173
theorem B2564243 : Blo 1709055 2564243 := bstep (se 1 (by rfl) ⟨1923182, by rfl⟩ : syracuseStep 2564243 = 3846365) B3846365
theorem B2564273 : Blo 1709055 2564273 := bstep (se 2 (by rfl) ⟨961602, by rfl⟩ : syracuseStep 2564273 = 1923205) B1923205
theorem B2564291 : Blo 1709055 2564291 := bstep (se 1 (by rfl) ⟨1923218, by rfl⟩ : syracuseStep 2564291 = 3846437) B3846437
theorem B2564321 : Blo 1709055 2564321 := bstep (se 2 (by rfl) ⟨961620, by rfl⟩ : syracuseStep 2564321 = 1923241) B1923241
theorem B6496483 : Blo 1709055 6496483 := bstep (se 1 (by rfl) ⟨4872362, by rfl⟩ : syracuseStep 6496483 = 9744725) B9744725
theorem B2564339 : Blo 1709055 2564339 := bstep (se 1 (by rfl) ⟨1923254, by rfl⟩ : syracuseStep 2564339 = 3846509) B3846509
theorem B2564369 : Blo 1709055 2564369 := bstep (se 2 (by rfl) ⟨961638, by rfl⟩ : syracuseStep 2564369 = 1923277) B1923277
theorem B2564387 : Blo 1709055 2564387 := bstep (se 1 (by rfl) ⟨1923290, by rfl⟩ : syracuseStep 2564387 = 3846581) B3846581
theorem B3653923 : Blo 1709055 3653923 := bstep (se 1 (by rfl) ⟨2740442, by rfl⟩ : syracuseStep 3653923 = 5480885) B5480885
theorem B2564417 : Blo 1709055 2564417 := bstep (se 2 (by rfl) ⟨961656, by rfl⟩ : syracuseStep 2564417 = 1923313) B1923313
theorem B2564435 : Blo 1709055 2564435 := bstep (se 1 (by rfl) ⟨1923326, by rfl⟩ : syracuseStep 2564435 = 3846653) B3846653
theorem B2564465 : Blo 1709055 2564465 := bstep (se 2 (by rfl) ⟨961674, by rfl⟩ : syracuseStep 2564465 = 1923349) B1923349
theorem B2564483 : Blo 1709055 2564483 := bstep (se 1 (by rfl) ⟨1923362, by rfl⟩ : syracuseStep 2564483 = 3846725) B3846725
theorem B2564513 : Blo 1709055 2564513 := bstep (se 2 (by rfl) ⟨961692, by rfl⟩ : syracuseStep 2564513 = 1923385) B1923385
theorem B9249187 : Blo 1709055 9249187 := bstep (se 1 (by rfl) ⟨6936890, by rfl⟩ : syracuseStep 9249187 = 13873781) B13873781
theorem B2564531 : Blo 1709055 2564531 := bstep (se 1 (by rfl) ⟨1923398, by rfl⟩ : syracuseStep 2564531 = 3846797) B3846797
theorem B2564561 : Blo 1709055 2564561 := bstep (se 2 (by rfl) ⟨961710, by rfl⟩ : syracuseStep 2564561 = 1923421) B1923421
theorem B2433505 : Blo 1709055 2433505 := bstep (se 2 (by rfl) ⟨912564, by rfl⟩ : syracuseStep 2433505 = 1825129) B1825129
theorem B2564579 : Blo 1709055 2564579 := bstep (se 1 (by rfl) ⟨1923434, by rfl⟩ : syracuseStep 2564579 = 3846869) B3846869
theorem B7029233 : Blo 1709055 7029233 := bstep (se 2 (by rfl) ⟨2635962, by rfl⟩ : syracuseStep 7029233 = 5271925) B5271925
theorem B2564609 : Blo 1709055 2564609 := bstep (se 2 (by rfl) ⟨961728, by rfl⟩ : syracuseStep 2564609 = 1923457) B1923457
theorem B2884099 : Blo 1709055 2884099 := bstep (se 1 (by rfl) ⟨2163074, by rfl⟩ : syracuseStep 2884099 = 4326149) B4326149
theorem B2564627 : Blo 1709055 2564627 := bstep (se 1 (by rfl) ⟨1923470, by rfl⟩ : syracuseStep 2564627 = 3846941) B3846941
theorem B2564657 : Blo 1709055 2564657 := bstep (se 2 (by rfl) ⟨961746, by rfl⟩ : syracuseStep 2564657 = 1923493) B1923493
theorem B2564675 : Blo 1709055 2564675 := bstep (se 1 (by rfl) ⟨1923506, by rfl⟩ : syracuseStep 2564675 = 3847013) B3847013
theorem B2564705 : Blo 1709055 2564705 := bstep (se 2 (by rfl) ⟨961764, by rfl⟩ : syracuseStep 2564705 = 1923529) B1923529
theorem B2564723 : Blo 1709055 2564723 := bstep (se 1 (by rfl) ⟨1923542, by rfl⟩ : syracuseStep 2564723 = 3847085) B3847085
theorem B5481101 : Blo 1709055 5481101 := bstep (se 3 (by rfl) ⟨1027706, by rfl⟩ : syracuseStep 5481101 = 2055413) B2055413
theorem B2884241 : Blo 1709055 2884241 := bstep (se 2 (by rfl) ⟨1081590, by rfl⟩ : syracuseStep 2884241 = 2163181) B2163181
theorem B2564753 : Blo 1709055 2564753 := bstep (se 2 (by rfl) ⟨961782, by rfl⟩ : syracuseStep 2564753 = 1923565) B1923565
theorem B2777761 : Blo 1709055 2777761 := bstep (se 2 (by rfl) ⟨1041660, by rfl⟩ : syracuseStep 2777761 = 2083321) B2083321
theorem B2564771 : Blo 1709055 2564771 := bstep (se 1 (by rfl) ⟨1923578, by rfl⟩ : syracuseStep 2564771 = 3847157) B3847157
theorem B2564801 : Blo 1709055 2564801 := bstep (se 2 (by rfl) ⟨961800, by rfl⟩ : syracuseStep 2564801 = 1923601) B1923601
theorem B2564819 : Blo 1709055 2564819 := bstep (se 1 (by rfl) ⟨1923614, by rfl⟩ : syracuseStep 2564819 = 3847229) B3847229
theorem B2564849 : Blo 1709055 2564849 := bstep (se 2 (by rfl) ⟨961818, by rfl⟩ : syracuseStep 2564849 = 1923637) B1923637
theorem B2564867 : Blo 1709055 2564867 := bstep (se 1 (by rfl) ⟨1923650, by rfl⟩ : syracuseStep 2564867 = 3847301) B3847301
theorem B2884369 : Blo 1709055 2884369 := bstep (se 2 (by rfl) ⟨1081638, by rfl⟩ : syracuseStep 2884369 = 2163277) B2163277
theorem B2564897 : Blo 1709055 2564897 := bstep (se 2 (by rfl) ⟨961836, by rfl⟩ : syracuseStep 2564897 = 1923673) B1923673
theorem B2884403 : Blo 1709055 2884403 := bstep (se 1 (by rfl) ⟨2163302, by rfl⟩ : syracuseStep 2884403 = 4326605) B4326605
theorem B2564915 : Blo 1709055 2564915 := bstep (se 1 (by rfl) ⟨1923686, by rfl⟩ : syracuseStep 2564915 = 3847373) B3847373
theorem B2564945 : Blo 1709055 2564945 := bstep (se 2 (by rfl) ⟨961854, by rfl⟩ : syracuseStep 2564945 = 1923709) B1923709
theorem B3900241 : Blo 1709055 3900241 := bstep (se 2 (by rfl) ⟨1462590, by rfl⟩ : syracuseStep 3900241 = 2925181) B2925181
theorem B7218019 : Blo 1709055 7218019 := bstep (se 1 (by rfl) ⟨5413514, by rfl⟩ : syracuseStep 7218019 = 10827029) B10827029
theorem B2564963 : Blo 1709055 2564963 := bstep (se 1 (by rfl) ⟨1923722, by rfl⟩ : syracuseStep 2564963 = 3847445) B3847445
theorem B3081073 : Blo 1709055 3081073 := bstep (se 2 (by rfl) ⟨1155402, by rfl⟩ : syracuseStep 3081073 = 2310805) B2310805
theorem B2564993 : Blo 1709055 2564993 := bstep (se 2 (by rfl) ⟨961872, by rfl⟩ : syracuseStep 2564993 = 1923745) B1923745
theorem B3244931 : Blo 1709055 3244931 := bstep (se 1 (by rfl) ⟨2433698, by rfl⟩ : syracuseStep 3244931 = 4867397) B4867397
theorem B2565011 : Blo 1709055 2565011 := bstep (se 1 (by rfl) ⟨1923758, by rfl⟩ : syracuseStep 2565011 = 3847517) B3847517
theorem B2565041 : Blo 1709055 2565041 := bstep (se 2 (by rfl) ⟨961890, by rfl⟩ : syracuseStep 2565041 = 1923781) B1923781
theorem B2884531 : Blo 1709055 2884531 := bstep (se 1 (by rfl) ⟨2163398, by rfl⟩ : syracuseStep 2884531 = 4326797) B4326797
theorem B2565059 : Blo 1709055 2565059 := bstep (se 1 (by rfl) ⟨1923794, by rfl⟩ : syracuseStep 2565059 = 3847589) B3847589
theorem B2163667 : Blo 1709055 2163667 := bstep (se 1 (by rfl) ⟨1622750, by rfl⟩ : syracuseStep 2163667 = 3245501) B3245501
theorem B2565089 : Blo 1709055 2565089 := bstep (se 2 (by rfl) ⟨961908, by rfl⟩ : syracuseStep 2565089 = 1923817) B1923817
theorem B2565107 : Blo 1709055 2565107 := bstep (se 1 (by rfl) ⟨1923830, by rfl⟩ : syracuseStep 2565107 = 3847661) B3847661
theorem B2925571 : Blo 1709055 2925571 := bstep (se 1 (by rfl) ⟨2194178, by rfl⟩ : syracuseStep 2925571 = 4388357) B4388357
theorem B5555213 : Blo 1709055 5555213 := bstep (se 3 (by rfl) ⟨1041602, by rfl⟩ : syracuseStep 5555213 = 2083205) B2083205
theorem B2565137 : Blo 1709055 2565137 := bstep (se 2 (by rfl) ⟨961926, by rfl⟩ : syracuseStep 2565137 = 1923853) B1923853
theorem B2565155 : Blo 1709055 2565155 := bstep (se 1 (by rfl) ⟨1923866, by rfl⟩ : syracuseStep 2565155 = 3847733) B3847733
theorem B5850157 : Blo 1709055 5850157 := bstep (se 3 (by rfl) ⟨1096904, by rfl⟩ : syracuseStep 5850157 = 2193809) B2193809
theorem B2434097 : Blo 1709055 2434097 := bstep (se 2 (by rfl) ⟨912786, by rfl⟩ : syracuseStep 2434097 = 1825573) B1825573
theorem B2163763 : Blo 1709055 2163763 := bstep (se 1 (by rfl) ⟨1622822, by rfl⟩ : syracuseStep 2163763 = 3245645) B3245645
theorem B2884673 : Blo 1709055 2884673 := bstep (se 2 (by rfl) ⟨1081752, by rfl⟩ : syracuseStep 2884673 = 2163505) B2163505
theorem B2565185 : Blo 1709055 2565185 := bstep (se 2 (by rfl) ⟨961944, by rfl⟩ : syracuseStep 2565185 = 1923889) B1923889
theorem B2565203 : Blo 1709055 2565203 := bstep (se 1 (by rfl) ⟨1923902, by rfl⟩ : syracuseStep 2565203 = 3847805) B3847805
theorem B2565233 : Blo 1709055 2565233 := bstep (se 2 (by rfl) ⟨961962, by rfl⟩ : syracuseStep 2565233 = 1923925) B1923925
theorem B2565251 : Blo 1709055 2565251 := bstep (se 1 (by rfl) ⟨1923938, by rfl⟩ : syracuseStep 2565251 = 3847877) B3847877
theorem B5768333 : Blo 1709055 5768333 := bstep (se 3 (by rfl) ⟨1081562, by rfl⟩ : syracuseStep 5768333 = 2163125) B2163125
theorem B26338445 : Blo 1709055 26338445 := bstep (se 3 (by rfl) ⟨4938458, by rfl⟩ : syracuseStep 26338445 = 9876917) B9876917
theorem B2565281 : Blo 1709055 2565281 := bstep (se 2 (by rfl) ⟨961980, by rfl⟩ : syracuseStep 2565281 = 1923961) B1923961
theorem B4867249 : Blo 1709055 4867249 := bstep (se 2 (by rfl) ⟨1825218, by rfl⟩ : syracuseStep 4867249 = 3650437) B3650437
theorem B2565299 : Blo 1709055 2565299 := bstep (se 1 (by rfl) ⟨1923974, by rfl⟩ : syracuseStep 2565299 = 3847949) B3847949
theorem B2884801 : Blo 1709055 2884801 := bstep (se 2 (by rfl) ⟨1081800, by rfl⟩ : syracuseStep 2884801 = 2163601) B2163601
theorem B5768387 : Blo 1709055 5768387 := bstep (se 1 (by rfl) ⟨4326290, by rfl⟩ : syracuseStep 5768387 = 8652581) B8652581
theorem B2565329 : Blo 1709055 2565329 := bstep (se 2 (by rfl) ⟨961998, by rfl⟩ : syracuseStep 2565329 = 1923997) B1923997
theorem B2884835 : Blo 1709055 2884835 := bstep (se 1 (by rfl) ⟨2163626, by rfl⟩ : syracuseStep 2884835 = 4327253) B4327253
theorem B2565347 : Blo 1709055 2565347 := bstep (se 1 (by rfl) ⟨1924010, by rfl⟩ : syracuseStep 2565347 = 3848021) B3848021
theorem B8660195 : Blo 1709055 8660195 := bstep (se 1 (by rfl) ⟨6495146, by rfl⟩ : syracuseStep 8660195 = 12990293) B12990293
theorem B2565377 : Blo 1709055 2565377 := bstep (se 2 (by rfl) ⟨962016, by rfl⟩ : syracuseStep 2565377 = 1924033) B1924033
theorem B2565395 : Blo 1709055 2565395 := bstep (se 1 (by rfl) ⟨1924046, by rfl⟩ : syracuseStep 2565395 = 3848093) B3848093
theorem B2565425 : Blo 1709055 2565425 := bstep (se 2 (by rfl) ⟨962034, by rfl⟩ : syracuseStep 2565425 = 1924069) B1924069
theorem B2565443 : Blo 1709055 2565443 := bstep (se 1 (by rfl) ⟨1924082, by rfl⟩ : syracuseStep 2565443 = 3848165) B3848165
theorem B2565473 : Blo 1709055 2565473 := bstep (se 2 (by rfl) ⟨962052, by rfl⟩ : syracuseStep 2565473 = 1924105) B1924105
theorem B2884963 : Blo 1709055 2884963 := bstep (se 1 (by rfl) ⟨2163722, by rfl⟩ : syracuseStep 2884963 = 4327445) B4327445
theorem B2565491 : Blo 1709055 2565491 := bstep (se 1 (by rfl) ⟨1924118, by rfl⟩ : syracuseStep 2565491 = 3848237) B3848237
theorem B2565521 : Blo 1709055 2565521 := bstep (se 2 (by rfl) ⟨962070, by rfl⟩ : syracuseStep 2565521 = 1924141) B1924141
theorem B2565539 : Blo 1709055 2565539 := bstep (se 1 (by rfl) ⟨1924154, by rfl⟩ : syracuseStep 2565539 = 3848309) B3848309
theorem B2565569 : Blo 1709055 2565569 := bstep (se 2 (by rfl) ⟨962088, by rfl⟩ : syracuseStep 2565569 = 1924177) B1924177
theorem B4867523 : Blo 1709055 4867523 := bstep (se 1 (by rfl) ⟨3650642, by rfl⟩ : syracuseStep 4867523 = 7301285) B7301285
theorem B11699653 : Blo 1709055 11699653 := bstep (se 4 (by rfl) ⟨1096842, by rfl⟩ : syracuseStep 11699653 = 2193685) B2193685
theorem B5768657 : Blo 1709055 5768657 := bstep (se 2 (by rfl) ⟨2163246, by rfl⟩ : syracuseStep 5768657 = 4326493) B4326493
theorem B2565587 : Blo 1709055 2565587 := bstep (se 1 (by rfl) ⟨1924190, by rfl⟩ : syracuseStep 2565587 = 3848381) B3848381
theorem B2885105 : Blo 1709055 2885105 := bstep (se 2 (by rfl) ⟨1081914, by rfl⟩ : syracuseStep 2885105 = 2163829) B2163829
theorem B2565617 : Blo 1709055 2565617 := bstep (se 2 (by rfl) ⟨962106, by rfl⟩ : syracuseStep 2565617 = 1924213) B1924213
theorem B9741809 : Blo 1709055 9741809 := bstep (se 2 (by rfl) ⟨3653178, by rfl⟩ : syracuseStep 9741809 = 7306357) B7306357
theorem B2565635 : Blo 1709055 2565635 := bstep (se 1 (by rfl) ⟨1924226, by rfl⟩ : syracuseStep 2565635 = 3848453) B3848453
theorem B4326929 : Blo 1709055 4326929 := bstep (se 2 (by rfl) ⟨1622598, by rfl⟩ : syracuseStep 4326929 = 3245197) B3245197
theorem B2565665 : Blo 1709055 2565665 := bstep (se 2 (by rfl) ⟨962124, by rfl⟩ : syracuseStep 2565665 = 1924249) B1924249
theorem B2164259 : Blo 1709055 2164259 := bstep (se 1 (by rfl) ⟨1623194, by rfl⟩ : syracuseStep 2164259 = 3246389) B3246389
theorem B2565683 : Blo 1709055 2565683 := bstep (se 1 (by rfl) ⟨1924262, by rfl⟩ : syracuseStep 2565683 = 3848525) B3848525
theorem B4326979 : Blo 1709055 4326979 := bstep (se 1 (by rfl) ⟨3245234, by rfl⟩ : syracuseStep 4326979 = 6490469) B6490469
theorem B2434627 : Blo 1709055 2434627 := bstep (se 1 (by rfl) ⟨1825970, by rfl⟩ : syracuseStep 2434627 = 3651941) B3651941
theorem B7300685 : Blo 1709055 7300685 := bstep (se 3 (by rfl) ⟨1368878, by rfl⟩ : syracuseStep 7300685 = 2737757) B2737757
theorem B2565713 : Blo 1709055 2565713 := bstep (se 2 (by rfl) ⟨962142, by rfl⟩ : syracuseStep 2565713 = 1924285) B1924285
theorem B2565731 : Blo 1709055 2565731 := bstep (se 1 (by rfl) ⟨1924298, by rfl⟩ : syracuseStep 2565731 = 3848597) B3848597
theorem B2885233 : Blo 1709055 2885233 := bstep (se 2 (by rfl) ⟨1081962, by rfl⟩ : syracuseStep 2885233 = 2163925) B2163925
theorem B53380721 : Blo 1709055 53380721 := bstep (se 2 (by rfl) ⟨20017770, by rfl⟩ : syracuseStep 53380721 = 40035541) B40035541
theorem B2565761 : Blo 1709055 2565761 := bstep (se 2 (by rfl) ⟨962160, by rfl⟩ : syracuseStep 2565761 = 1924321) B1924321
theorem B4867715 : Blo 1709055 4867715 := bstep (se 1 (by rfl) ⟨3650786, by rfl⟩ : syracuseStep 4867715 = 7301573) B7301573
theorem B2885267 : Blo 1709055 2885267 := bstep (se 1 (by rfl) ⟨2163950, by rfl⟩ : syracuseStep 2885267 = 4327901) B4327901
theorem B2565779 : Blo 1709055 2565779 := bstep (se 1 (by rfl) ⟨1924334, by rfl⟩ : syracuseStep 2565779 = 3848669) B3848669
theorem B2565809 : Blo 1709055 2565809 := bstep (se 2 (by rfl) ⟨962178, by rfl⟩ : syracuseStep 2565809 = 1924357) B1924357
theorem B2565827 : Blo 1709055 2565827 := bstep (se 1 (by rfl) ⟨1924370, by rfl⟩ : syracuseStep 2565827 = 3848741) B3848741
theorem B4327121 : Blo 1709055 4327121 := bstep (se 2 (by rfl) ⟨1622670, by rfl⟩ : syracuseStep 4327121 = 3245341) B3245341
theorem B2565857 : Blo 1709055 2565857 := bstep (se 2 (by rfl) ⟨962196, by rfl⟩ : syracuseStep 2565857 = 1924393) B1924393
theorem B8775395 : Blo 1709055 8775395 := bstep (se 1 (by rfl) ⟨6581546, by rfl⟩ : syracuseStep 8775395 = 13163093) B13163093
theorem B9242353 : Blo 1709055 9242353 := bstep (se 2 (by rfl) ⟨3465882, by rfl⟩ : syracuseStep 9242353 = 6931765) B6931765
theorem B2565875 : Blo 1709055 2565875 := bstep (se 1 (by rfl) ⟨1924406, by rfl⟩ : syracuseStep 2565875 = 3848813) B3848813
theorem B3245827 : Blo 1709055 3245827 := bstep (se 1 (by rfl) ⟨2434370, by rfl⟩ : syracuseStep 3245827 = 4868741) B4868741
theorem B15607565 : Blo 1709055 15607565 := bstep (se 3 (by rfl) ⟨2926418, by rfl⟩ : syracuseStep 15607565 = 5852837) B5852837
theorem B2737937 : Blo 1709055 2737937 := bstep (se 2 (by rfl) ⟨1026726, by rfl⟩ : syracuseStep 2737937 = 2053453) B2053453
theorem B2565905 : Blo 1709055 2565905 := bstep (se 2 (by rfl) ⟨962214, by rfl⟩ : syracuseStep 2565905 = 1924429) B1924429
theorem B2885395 : Blo 1709055 2885395 := bstep (se 1 (by rfl) ⟨2164046, by rfl⟩ : syracuseStep 2885395 = 4328093) B4328093
theorem B2565923 : Blo 1709055 2565923 := bstep (se 1 (by rfl) ⟨1924442, by rfl⟩ : syracuseStep 2565923 = 3848885) B3848885
theorem B2565953 : Blo 1709055 2565953 := bstep (se 2 (by rfl) ⟨962232, by rfl⟩ : syracuseStep 2565953 = 1924465) B1924465
theorem B2565971 : Blo 1709055 2565971 := bstep (se 1 (by rfl) ⟨1924478, by rfl⟩ : syracuseStep 2565971 = 3848957) B3848957
theorem B2566001 : Blo 1709055 2566001 := bstep (se 2 (by rfl) ⟨962250, by rfl⟩ : syracuseStep 2566001 = 1924501) B1924501
theorem B2566019 : Blo 1709055 2566019 := bstep (se 1 (by rfl) ⟨1924514, by rfl⟩ : syracuseStep 2566019 = 3849029) B3849029
theorem B55461773 : Blo 1709055 55461773 := bstep (se 3 (by rfl) ⟨10399082, by rfl⟩ : syracuseStep 55461773 = 20798165) B20798165
theorem B2738065 : Blo 1709055 2738065 := bstep (se 2 (by rfl) ⟨1026774, by rfl⟩ : syracuseStep 2738065 = 2053549) B2053549
theorem B2434963 : Blo 1709055 2434963 := bstep (se 1 (by rfl) ⟨1826222, by rfl⟩ : syracuseStep 2434963 = 3652445) B3652445
theorem B2598817 : Blo 1709055 2598817 := bstep (se 2 (by rfl) ⟨974556, by rfl⟩ : syracuseStep 2598817 = 1949113) B1949113
theorem B2885537 : Blo 1709055 2885537 := bstep (se 2 (by rfl) ⟨1082076, by rfl⟩ : syracuseStep 2885537 = 2164153) B2164153
theorem B3245987 : Blo 1709055 3245987 := bstep (se 1 (by rfl) ⟨2434490, by rfl⟩ : syracuseStep 3245987 = 4868981) B4868981
theorem B2566049 : Blo 1709055 2566049 := bstep (se 2 (by rfl) ⟨962268, by rfl⟩ : syracuseStep 2566049 = 1924537) B1924537
theorem B2566067 : Blo 1709055 2566067 := bstep (se 1 (by rfl) ⟨1924550, by rfl⟩ : syracuseStep 2566067 = 3849101) B3849101
theorem B2566097 : Blo 1709055 2566097 := bstep (se 2 (by rfl) ⟨962286, by rfl⟩ : syracuseStep 2566097 = 1924573) B1924573
theorem B2566115 : Blo 1709055 2566115 := bstep (se 1 (by rfl) ⟨1924586, by rfl⟩ : syracuseStep 2566115 = 3849173) B3849173
theorem B5769197 : Blo 1709055 5769197 := bstep (se 3 (by rfl) ⟨1081724, by rfl⟩ : syracuseStep 5769197 = 2163449) B2163449
theorem B2566145 : Blo 1709055 2566145 := bstep (se 2 (by rfl) ⟨962304, by rfl⟩ : syracuseStep 2566145 = 1924609) B1924609
theorem B8661005 : Blo 1709055 8661005 := bstep (se 3 (by rfl) ⟨1623938, by rfl⟩ : syracuseStep 8661005 = 3247877) B3247877
theorem B2566163 : Blo 1709055 2566163 := bstep (se 1 (by rfl) ⟨1924622, by rfl⟩ : syracuseStep 2566163 = 3849245) B3849245
theorem B2885665 : Blo 1709055 2885665 := bstep (se 2 (by rfl) ⟨1082124, by rfl⟩ : syracuseStep 2885665 = 2164249) B2164249
theorem B4933667 : Blo 1709055 4933667 := bstep (se 1 (by rfl) ⟨3700250, by rfl⟩ : syracuseStep 4933667 = 7400501) B7400501
theorem B5769251 : Blo 1709055 5769251 := bstep (se 1 (by rfl) ⟨4326938, by rfl⟩ : syracuseStep 5769251 = 8653877) B8653877
theorem B2566193 : Blo 1709055 2566193 := bstep (se 2 (by rfl) ⟨962322, by rfl⟩ : syracuseStep 2566193 = 1924645) B1924645
theorem B2885699 : Blo 1709055 2885699 := bstep (se 1 (by rfl) ⟨2164274, by rfl⟩ : syracuseStep 2885699 = 4328549) B4328549
theorem B2566211 : Blo 1709055 2566211 := bstep (se 1 (by rfl) ⟨1924658, by rfl⟩ : syracuseStep 2566211 = 3849317) B3849317
theorem B10963021 : Blo 1709055 10963021 := bstep (se 3 (by rfl) ⟨2055566, by rfl⟩ : syracuseStep 10963021 = 4111133) B4111133
theorem B2566241 : Blo 1709055 2566241 := bstep (se 2 (by rfl) ⟨962340, by rfl⟩ : syracuseStep 2566241 = 1924681) B1924681
theorem B2566259 : Blo 1709055 2566259 := bstep (se 1 (by rfl) ⟨1924694, by rfl⟩ : syracuseStep 2566259 = 3849389) B3849389
theorem B2566289 : Blo 1709055 2566289 := bstep (se 2 (by rfl) ⟨962358, by rfl⟩ : syracuseStep 2566289 = 1924717) B1924717
theorem B2566307 : Blo 1709055 2566307 := bstep (se 1 (by rfl) ⟨1924730, by rfl⟩ : syracuseStep 2566307 = 3849461) B3849461
theorem B2566337 : Blo 1709055 2566337 := bstep (se 2 (by rfl) ⟨962376, by rfl⟩ : syracuseStep 2566337 = 1924753) B1924753
theorem B2885827 : Blo 1709055 2885827 := bstep (se 1 (by rfl) ⟨2164370, by rfl⟩ : syracuseStep 2885827 = 4328741) B4328741
theorem B2566355 : Blo 1709055 2566355 := bstep (se 1 (by rfl) ⟨1924766, by rfl⟩ : syracuseStep 2566355 = 3849533) B3849533
theorem B2164963 : Blo 1709055 2164963 := bstep (se 1 (by rfl) ⟨1623722, by rfl⟩ : syracuseStep 2164963 = 3247445) B3247445
theorem B2566385 : Blo 1709055 2566385 := bstep (se 2 (by rfl) ⟨962394, by rfl⟩ : syracuseStep 2566385 = 1924789) B1924789
theorem B2566403 : Blo 1709055 2566403 := bstep (se 1 (by rfl) ⟨1924802, by rfl⟩ : syracuseStep 2566403 = 3849605) B3849605
theorem B2738449 : Blo 1709055 2738449 := bstep (se 2 (by rfl) ⟨1026918, by rfl⟩ : syracuseStep 2738449 = 2053837) B2053837
theorem B2566433 : Blo 1709055 2566433 := bstep (se 2 (by rfl) ⟨962412, by rfl⟩ : syracuseStep 2566433 = 1924825) B1924825
theorem B5769521 : Blo 1709055 5769521 := bstep (se 2 (by rfl) ⟨2163570, by rfl⟩ : syracuseStep 5769521 = 4327141) B4327141
theorem B2566451 : Blo 1709055 2566451 := bstep (se 1 (by rfl) ⟨1924838, by rfl⟩ : syracuseStep 2566451 = 3849677) B3849677
theorem B2165059 : Blo 1709055 2165059 := bstep (se 1 (by rfl) ⟨1623794, by rfl⟩ : syracuseStep 2165059 = 3247589) B3247589
theorem B9242957 : Blo 1709055 9242957 := bstep (se 3 (by rfl) ⟨1733054, by rfl⟩ : syracuseStep 9242957 = 3466109) B3466109
theorem B2885969 : Blo 1709055 2885969 := bstep (se 2 (by rfl) ⟨1082238, by rfl⟩ : syracuseStep 2885969 = 2164477) B2164477
theorem B2566481 : Blo 1709055 2566481 := bstep (se 2 (by rfl) ⟨962430, by rfl⟩ : syracuseStep 2566481 = 1924861) B1924861
theorem B2566499 : Blo 1709055 2566499 := bstep (se 1 (by rfl) ⟨1924874, by rfl⟩ : syracuseStep 2566499 = 3849749) B3849749
theorem B2566529 : Blo 1709055 2566529 := bstep (se 2 (by rfl) ⟨962448, by rfl⟩ : syracuseStep 2566529 = 1924897) B1924897
theorem B2566547 : Blo 1709055 2566547 := bstep (se 1 (by rfl) ⟨1924910, by rfl⟩ : syracuseStep 2566547 = 3849821) B3849821
theorem B4868525 : Blo 1709055 4868525 := bstep (se 3 (by rfl) ⟨912848, by rfl⟩ : syracuseStep 4868525 = 1825697) B1825697
theorem B2566577 : Blo 1709055 2566577 := bstep (se 2 (by rfl) ⟨962466, by rfl⟩ : syracuseStep 2566577 = 1924933) B1924933
theorem B2435521 : Blo 1709055 2435521 := bstep (se 2 (by rfl) ⟨913320, by rfl⟩ : syracuseStep 2435521 = 1826641) B1826641
theorem B12978629 : Blo 1709055 12978629 := bstep (se 4 (by rfl) ⟨1216746, by rfl⟩ : syracuseStep 12978629 = 2433493) B2433493
theorem B2886097 : Blo 1709055 2886097 := bstep (se 2 (by rfl) ⟨1082286, by rfl⟩ : syracuseStep 2886097 = 2164573) B2164573
theorem B2435555 : Blo 1709055 2435555 := bstep (se 1 (by rfl) ⟨1826666, by rfl⟩ : syracuseStep 2435555 = 3653333) B3653333
theorem B2886131 : Blo 1709055 2886131 := bstep (se 1 (by rfl) ⟨2164598, by rfl⟩ : syracuseStep 2886131 = 4329197) B4329197
theorem B6490637 : Blo 1709055 6490637 := bstep (se 3 (by rfl) ⟨1216994, by rfl⟩ : syracuseStep 6490637 = 2433989) B2433989
theorem B21088781 : Blo 1709055 21088781 := bstep (se 3 (by rfl) ⟨3954146, by rfl⟩ : syracuseStep 21088781 = 7908293) B7908293
theorem B16443917 : Blo 1709055 16443917 := bstep (se 3 (by rfl) ⟨3083234, by rfl⟩ : syracuseStep 16443917 = 6166469) B6166469
theorem B2738705 : Blo 1709055 2738705 := bstep (se 2 (by rfl) ⟨1027014, by rfl⟩ : syracuseStep 2738705 = 2054029) B2054029
theorem B7801379 : Blo 1709055 7801379 := bstep (se 1 (by rfl) ⟨5851034, by rfl⟩ : syracuseStep 7801379 = 11702069) B11702069
theorem B4868707 : Blo 1709055 4868707 := bstep (se 1 (by rfl) ⟨3651530, by rfl⟩ : syracuseStep 4868707 = 7303061) B7303061
theorem B2886259 : Blo 1709055 2886259 := bstep (se 1 (by rfl) ⟨2164694, by rfl⟩ : syracuseStep 2886259 = 4329389) B4329389
theorem B4934317 : Blo 1709055 4934317 := bstep (se 3 (by rfl) ⟨925184, by rfl⟩ : syracuseStep 4934317 = 1850369) B1850369
theorem B4328113 : Blo 1709055 4328113 := bstep (se 2 (by rfl) ⟨1623042, by rfl⟩ : syracuseStep 4328113 = 3246085) B3246085
theorem B8653553 : Blo 1709055 8653553 := bstep (se 2 (by rfl) ⟨3245082, by rfl⟩ : syracuseStep 8653553 = 6490165) B6490165
theorem B2886401 : Blo 1709055 2886401 := bstep (se 2 (by rfl) ⟨1082400, by rfl⟩ : syracuseStep 2886401 = 2164801) B2164801
theorem B2165555 : Blo 1709055 2165555 := bstep (se 1 (by rfl) ⟨1624166, by rfl⟩ : syracuseStep 2165555 = 3248333) B3248333
theorem B5770061 : Blo 1709055 5770061 := bstep (se 3 (by rfl) ⟨1081886, by rfl⟩ : syracuseStep 5770061 = 2163773) B2163773
theorem B2886529 : Blo 1709055 2886529 := bstep (se 2 (by rfl) ⟨1082448, by rfl⟩ : syracuseStep 2886529 = 2164897) B2164897
theorem B5770115 : Blo 1709055 5770115 := bstep (se 1 (by rfl) ⟨4327586, by rfl⟩ : syracuseStep 5770115 = 8655173) B8655173
theorem B2886563 : Blo 1709055 2886563 := bstep (se 1 (by rfl) ⟨2164922, by rfl⟩ : syracuseStep 2886563 = 4329845) B4329845
theorem B9743267 : Blo 1709055 9743267 := bstep (se 1 (by rfl) ⟨7307450, by rfl⟩ : syracuseStep 9743267 = 14614901) B14614901
theorem B4328387 : Blo 1709055 4328387 := bstep (se 1 (by rfl) ⟨3246290, by rfl⟩ : syracuseStep 4328387 = 6492581) B6492581
theorem B3247057 : Blo 1709055 3247057 := bstep (se 2 (by rfl) ⟨1217646, by rfl⟩ : syracuseStep 3247057 = 2435293) B2435293
theorem B16436195 : Blo 1709055 16436195 := bstep (se 1 (by rfl) ⟨12327146, by rfl⟩ : syracuseStep 16436195 = 24654293) B24654293
theorem B12987377 : Blo 1709055 12987377 := bstep (se 2 (by rfl) ⟨4870266, by rfl⟩ : syracuseStep 12987377 = 9740533) B9740533
theorem B2436113 : Blo 1709055 2436113 := bstep (se 2 (by rfl) ⟨913542, by rfl⟩ : syracuseStep 2436113 = 1827085) B1827085
theorem B2886691 : Blo 1709055 2886691 := bstep (se 1 (by rfl) ⟨2165018, by rfl⟩ : syracuseStep 2886691 = 4330037) B4330037
theorem B2599985 : Blo 1709055 2599985 := bstep (se 2 (by rfl) ⟨974994, by rfl⟩ : syracuseStep 2599985 = 1949989) B1949989
theorem B21924917 : Blo 1709055 21924917 := bstep (se 5 (by rfl) ⟨1027730, by rfl⟩ : syracuseStep 21924917 = 2055461) B2055461
theorem B4869197 : Blo 1709055 4869197 := bstep (se 3 (by rfl) ⟨912974, by rfl⟩ : syracuseStep 4869197 = 1825949) B1825949
theorem B2436193 : Blo 1709055 2436193 := bstep (se 2 (by rfl) ⟨913572, by rfl⟩ : syracuseStep 2436193 = 1827145) B1827145
theorem B7302257 : Blo 1709055 7302257 := bstep (se 2 (by rfl) ⟨2738346, by rfl⟩ : syracuseStep 7302257 = 5476693) B5476693
theorem B4328579 : Blo 1709055 4328579 := bstep (se 1 (by rfl) ⟨3246434, by rfl⟩ : syracuseStep 4328579 = 6492869) B6492869
theorem B5770385 : Blo 1709055 5770385 := bstep (se 2 (by rfl) ⟨2163894, by rfl⟩ : syracuseStep 5770385 = 4327789) B4327789
theorem B3124369 : Blo 1709055 3124369 := bstep (se 2 (by rfl) ⟨1171638, by rfl⟩ : syracuseStep 3124369 = 2343277) B2343277
theorem B2600113 : Blo 1709055 2600113 := bstep (se 2 (by rfl) ⟨975042, by rfl⟩ : syracuseStep 2600113 = 1950085) B1950085
theorem B2886833 : Blo 1709055 2886833 := bstep (se 2 (by rfl) ⟨1082562, by rfl⟩ : syracuseStep 2886833 = 2165125) B2165125
theorem B8326385 : Blo 1709055 8326385 := bstep (se 2 (by rfl) ⟨3122394, by rfl⟩ : syracuseStep 8326385 = 6244789) B6244789
theorem B3845393 : Blo 1709055 3845393 := bstep (se 2 (by rfl) ⟨1442022, by rfl⟩ : syracuseStep 3845393 = 2884045) B2884045
theorem B3845411 : Blo 1709055 3845411 := bstep (se 1 (by rfl) ⟨2884058, by rfl⟩ : syracuseStep 3845411 = 5768117) B5768117
theorem B6491441 : Blo 1709055 6491441 := bstep (se 2 (by rfl) ⟨2434290, by rfl⟩ : syracuseStep 6491441 = 4868581) B4868581
theorem B2886961 : Blo 1709055 2886961 := bstep (se 2 (by rfl) ⟨1082610, by rfl⟩ : syracuseStep 2886961 = 2165221) B2165221
theorem B9866573 : Blo 1709055 9866573 := bstep (se 3 (by rfl) ⟨1849982, by rfl⟩ : syracuseStep 9866573 = 3699965) B3699965
theorem B2886995 : Blo 1709055 2886995 := bstep (se 1 (by rfl) ⟨2165246, by rfl⟩ : syracuseStep 2886995 = 4330493) B4330493
theorem B4107665 : Blo 1709055 4107665 := bstep (se 2 (by rfl) ⟨1540374, by rfl⟩ : syracuseStep 4107665 = 3080749) B3080749
theorem B2887123 : Blo 1709055 2887123 := bstep (se 1 (by rfl) ⟨2165342, by rfl⟩ : syracuseStep 2887123 = 4330685) B4330685
theorem B5852675 : Blo 1709055 5852675 := bstep (se 1 (by rfl) ⟨4389506, by rfl⟩ : syracuseStep 5852675 = 8779013) B8779013
theorem B3845681 : Blo 1709055 3845681 := bstep (se 2 (by rfl) ⟨1442130, by rfl⟩ : syracuseStep 3845681 = 2884261) B2884261
theorem B3845699 : Blo 1709055 3845699 := bstep (se 1 (by rfl) ⟨2884274, by rfl⟩ : syracuseStep 3845699 = 5768549) B5768549
theorem B2887265 : Blo 1709055 2887265 := bstep (se 2 (by rfl) ⟨1082724, by rfl⟩ : syracuseStep 2887265 = 2165449) B2165449
theorem B70233713 : Blo 1709055 70233713 := bstep (se 2 (by rfl) ⟨26337642, by rfl⟩ : syracuseStep 70233713 = 52675285) B52675285
theorem B5770925 : Blo 1709055 5770925 := bstep (se 3 (by rfl) ⟨1082048, by rfl⟩ : syracuseStep 5770925 = 2164097) B2164097
theorem B2887393 : Blo 1709055 2887393 := bstep (se 2 (by rfl) ⟨1082772, by rfl⟩ : syracuseStep 2887393 = 2165545) B2165545
theorem B5770979 : Blo 1709055 5770979 := bstep (se 1 (by rfl) ⟨4328234, by rfl⟩ : syracuseStep 5770979 = 8656469) B8656469
theorem B3288899 : Blo 1709055 3288899 := bstep (se 1 (by rfl) ⟨2466674, by rfl⟩ : syracuseStep 3288899 = 4933349) B4933349
theorem B3845969 : Blo 1709055 3845969 := bstep (se 2 (by rfl) ⟨1442238, by rfl⟩ : syracuseStep 3845969 = 2884477) B2884477
theorem B3845987 : Blo 1709055 3845987 := bstep (se 1 (by rfl) ⟨2884490, by rfl⟩ : syracuseStep 3845987 = 5768981) B5768981
theorem B4624237 : Blo 1709055 4624237 := bstep (se 3 (by rfl) ⟨867044, by rfl⟩ : syracuseStep 4624237 = 1734089) B1734089
theorem B2740115 : Blo 1709055 2740115 := bstep (se 1 (by rfl) ⟨2055086, by rfl⟩ : syracuseStep 2740115 = 4110173) B4110173
theorem B6492109 : Blo 1709055 6492109 := bstep (se 3 (by rfl) ⟨1217270, by rfl⟩ : syracuseStep 6492109 = 2434541) B2434541
theorem B5771249 : Blo 1709055 5771249 := bstep (se 2 (by rfl) ⟨2164218, by rfl⟩ : syracuseStep 5771249 = 4328437) B4328437
theorem B3248113 : Blo 1709055 3248113 := bstep (se 2 (by rfl) ⟨1218042, by rfl⟩ : syracuseStep 3248113 = 2436085) B2436085
theorem B4329521 : Blo 1709055 4329521 := bstep (se 2 (by rfl) ⟨1623570, by rfl⟩ : syracuseStep 4329521 = 3247141) B3247141
theorem B6582349 : Blo 1709055 6582349 := bstep (se 3 (by rfl) ⟨1234190, by rfl⟩ : syracuseStep 6582349 = 2468381) B2468381
theorem B4329571 : Blo 1709055 4329571 := bstep (se 1 (by rfl) ⟨3247178, by rfl⟩ : syracuseStep 4329571 = 6494357) B6494357
theorem B3846257 : Blo 1709055 3846257 := bstep (se 2 (by rfl) ⟨1442346, by rfl⟩ : syracuseStep 3846257 = 2884693) B2884693
theorem B3846275 : Blo 1709055 3846275 := bstep (se 1 (by rfl) ⟨2884706, by rfl⟩ : syracuseStep 3846275 = 5769413) B5769413
theorem B8655011 : Blo 1709055 8655011 := bstep (se 1 (by rfl) ⟨6491258, by rfl⟩ : syracuseStep 8655011 = 12982517) B12982517
theorem B4870381 : Blo 1709055 4870381 := bstep (se 3 (by rfl) ⟨913196, by rfl⟩ : syracuseStep 4870381 = 1826393) B1826393
theorem B9736433 : Blo 1709055 9736433 := bstep (se 2 (by rfl) ⟨3651162, by rfl⟩ : syracuseStep 9736433 = 7302325) B7302325
theorem B4329713 : Blo 1709055 4329713 := bstep (se 2 (by rfl) ⟨1623642, by rfl⟩ : syracuseStep 4329713 = 3247285) B3247285
theorem B5476643 : Blo 1709055 5476643 := bstep (se 1 (by rfl) ⟨4107482, by rfl⟩ : syracuseStep 5476643 = 8214965) B8214965
theorem B16667021 : Blo 1709055 16667021 := bstep (se 3 (by rfl) ⟨3125066, by rfl⟩ : syracuseStep 16667021 = 6250133) B6250133
theorem B3846545 : Blo 1709055 3846545 := bstep (se 2 (by rfl) ⟨1442454, by rfl⟩ : syracuseStep 3846545 = 2884909) B2884909
theorem B3846563 : Blo 1709055 3846563 := bstep (se 1 (by rfl) ⟨2884922, by rfl⟩ : syracuseStep 3846563 = 5769845) B5769845
theorem B15602161 : Blo 1709055 15602161 := bstep (se 2 (by rfl) ⟨5850810, by rfl⟩ : syracuseStep 15602161 = 11701621) B11701621
theorem B5771789 : Blo 1709055 5771789 := bstep (se 3 (by rfl) ⟨1082210, by rfl⟩ : syracuseStep 5771789 = 2164421) B2164421
theorem B5771843 : Blo 1709055 5771843 := bstep (se 1 (by rfl) ⟨4328882, by rfl⟩ : syracuseStep 5771843 = 8657765) B8657765
theorem B12325445 : Blo 1709055 12325445 := bstep (se 4 (by rfl) ⟨1155510, by rfl⟩ : syracuseStep 12325445 = 2311021) B2311021
theorem B3846833 : Blo 1709055 3846833 := bstep (se 2 (by rfl) ⟨1442562, by rfl⟩ : syracuseStep 3846833 = 2885125) B2885125
theorem B3846851 : Blo 1709055 3846851 := bstep (se 1 (by rfl) ⟨2885138, by rfl⟩ : syracuseStep 3846851 = 5770277) B5770277
theorem B1733347 : Blo 1709055 1733347 := bstep (se 1 (by rfl) ⟨1300010, by rfl⟩ : syracuseStep 1733347 = 2600021) B2600021
theorem B6492899 : Blo 1709055 6492899 := bstep (se 1 (by rfl) ⟨4869674, by rfl⟩ : syracuseStep 6492899 = 9739349) B9739349
theorem B8213233 : Blo 1709055 8213233 := bstep (se 2 (by rfl) ⟨3079962, by rfl⟩ : syracuseStep 8213233 = 6159925) B6159925
theorem B5772113 : Blo 1709055 5772113 := bstep (se 2 (by rfl) ⟨2164542, by rfl⟩ : syracuseStep 5772113 = 4329085) B4329085
theorem B8213347 : Blo 1709055 8213347 := bstep (se 1 (by rfl) ⟨6160010, by rfl⟩ : syracuseStep 8213347 = 12320021) B12320021
theorem B8655821 : Blo 1709055 8655821 := bstep (se 3 (by rfl) ⟨1622966, by rfl⟩ : syracuseStep 8655821 = 3245933) B3245933
theorem B3650513 : Blo 1709055 3650513 := bstep (se 2 (by rfl) ⟨1368942, by rfl⟩ : syracuseStep 3650513 = 2737885) B2737885
theorem B3847121 : Blo 1709055 3847121 := bstep (se 2 (by rfl) ⟨1442670, by rfl⟩ : syracuseStep 3847121 = 2885341) B2885341
theorem B29209571 : Blo 1709055 29209571 := bstep (se 1 (by rfl) ⟨21907178, by rfl⟩ : syracuseStep 29209571 = 43814357) B43814357
theorem B3847139 : Blo 1709055 3847139 := bstep (se 1 (by rfl) ⟨2885354, by rfl⟩ : syracuseStep 3847139 = 5770709) B5770709
theorem B1709059 : Blo 1709055 1709059 := bstep (se 1 (by rfl) ⟨1281794, by rfl⟩ : syracuseStep 1709059 = 2563589) B2563589
theorem B1709075 : Blo 1709055 1709075 := bstep (se 1 (by rfl) ⟨1281806, by rfl⟩ : syracuseStep 1709075 = 2563613) B2563613
theorem B1709091 : Blo 1709055 1709091 := bstep (se 1 (by rfl) ⟨1281818, by rfl⟩ : syracuseStep 1709091 = 2563637) B2563637
theorem B1709107 : Blo 1709055 1709107 := bstep (se 1 (by rfl) ⟨1281830, by rfl⟩ : syracuseStep 1709107 = 2563661) B2563661
theorem B1709123 : Blo 1709055 1709123 := bstep (se 1 (by rfl) ⟨1281842, by rfl⟩ : syracuseStep 1709123 = 2563685) B2563685
theorem B1709139 : Blo 1709055 1709139 := bstep (se 1 (by rfl) ⟨1281854, by rfl⟩ : syracuseStep 1709139 = 2563709) B2563709
theorem B1709155 : Blo 1709055 1709155 := bstep (se 1 (by rfl) ⟨1281866, by rfl⟩ : syracuseStep 1709155 = 2563733) B2563733
theorem B18494563 : Blo 1709055 18494563 := bstep (se 1 (by rfl) ⟨13870922, by rfl⟩ : syracuseStep 18494563 = 27741845) B27741845
theorem B1709171 : Blo 1709055 1709171 := bstep (se 1 (by rfl) ⟨1281878, by rfl⟩ : syracuseStep 1709171 = 2563757) B2563757
theorem B1709187 : Blo 1709055 1709187 := bstep (se 1 (by rfl) ⟨1281890, by rfl⟩ : syracuseStep 1709187 = 2563781) B2563781
theorem B1709203 : Blo 1709055 1709203 := bstep (se 1 (by rfl) ⟨1281902, by rfl⟩ : syracuseStep 1709203 = 2563805) B2563805
theorem B1709219 : Blo 1709055 1709219 := bstep (se 1 (by rfl) ⟨1281914, by rfl⟩ : syracuseStep 1709219 = 2563829) B2563829
theorem B5477539 : Blo 1709055 5477539 := bstep (se 1 (by rfl) ⟨4108154, by rfl⟩ : syracuseStep 5477539 = 8216309) B8216309
theorem B1709235 : Blo 1709055 1709235 := bstep (se 1 (by rfl) ⟨1281926, by rfl⟩ : syracuseStep 1709235 = 2563853) B2563853
theorem B1709251 : Blo 1709055 1709251 := bstep (se 1 (by rfl) ⟨1281938, by rfl⟩ : syracuseStep 1709251 = 2563877) B2563877
theorem B4330705 : Blo 1709055 4330705 := bstep (se 2 (by rfl) ⟨1624014, by rfl⟩ : syracuseStep 4330705 = 3248029) B3248029
theorem B1709267 : Blo 1709055 1709267 := bstep (se 1 (by rfl) ⟨1281950, by rfl⟩ : syracuseStep 1709267 = 2563901) B2563901
theorem B1709283 : Blo 1709055 1709283 := bstep (se 1 (by rfl) ⟨1281962, by rfl⟩ : syracuseStep 1709283 = 2563925) B2563925
theorem B3847409 : Blo 1709055 3847409 := bstep (se 2 (by rfl) ⟨1442778, by rfl⟩ : syracuseStep 3847409 = 2885557) B2885557
theorem B1709299 : Blo 1709055 1709299 := bstep (se 1 (by rfl) ⟨1281974, by rfl⟩ : syracuseStep 1709299 = 2563949) B2563949
theorem B1709315 : Blo 1709055 1709315 := bstep (se 1 (by rfl) ⟨1281986, by rfl⟩ : syracuseStep 1709315 = 2563973) B2563973
theorem B3847427 : Blo 1709055 3847427 := bstep (se 1 (by rfl) ⟨2885570, by rfl⟩ : syracuseStep 3847427 = 5771141) B5771141
theorem B4871441 : Blo 1709055 4871441 := bstep (se 2 (by rfl) ⟨1826790, by rfl⟩ : syracuseStep 4871441 = 3653581) B3653581
theorem B1709331 : Blo 1709055 1709331 := bstep (se 1 (by rfl) ⟨1281998, by rfl⟩ : syracuseStep 1709331 = 2563997) B2563997
theorem B1709347 : Blo 1709055 1709347 := bstep (se 1 (by rfl) ⟨1282010, by rfl⟩ : syracuseStep 1709347 = 2564021) B2564021
theorem B1709363 : Blo 1709055 1709363 := bstep (se 1 (by rfl) ⟨1282022, by rfl⟩ : syracuseStep 1709363 = 2564045) B2564045
theorem B1709379 : Blo 1709055 1709379 := bstep (se 1 (by rfl) ⟨1282034, by rfl⟩ : syracuseStep 1709379 = 2564069) B2564069
theorem B1709395 : Blo 1709055 1709395 := bstep (se 1 (by rfl) ⟨1282046, by rfl⟩ : syracuseStep 1709395 = 2564093) B2564093
theorem B8893795 : Blo 1709055 8893795 := bstep (se 1 (by rfl) ⟨6670346, by rfl⟩ : syracuseStep 8893795 = 13340693) B13340693
theorem B1709411 : Blo 1709055 1709411 := bstep (se 1 (by rfl) ⟨1282058, by rfl⟩ : syracuseStep 1709411 = 2564117) B2564117
theorem B3659107 : Blo 1709055 3659107 := bstep (se 1 (by rfl) ⟨2744330, by rfl⟩ : syracuseStep 3659107 = 5488661) B5488661
theorem B5772653 : Blo 1709055 5772653 := bstep (se 3 (by rfl) ⟨1082372, by rfl⟩ : syracuseStep 5772653 = 2164745) B2164745
theorem B6493553 : Blo 1709055 6493553 := bstep (se 2 (by rfl) ⟨2435082, by rfl⟩ : syracuseStep 6493553 = 4870165) B4870165
theorem B1709427 : Blo 1709055 1709427 := bstep (se 1 (by rfl) ⟨1282070, by rfl⟩ : syracuseStep 1709427 = 2564141) B2564141
theorem B1709443 : Blo 1709055 1709443 := bstep (se 1 (by rfl) ⟨1282082, by rfl⟩ : syracuseStep 1709443 = 2564165) B2564165
theorem B1709459 : Blo 1709055 1709459 := bstep (se 1 (by rfl) ⟨1282094, by rfl⟩ : syracuseStep 1709459 = 2564189) B2564189
theorem B1709475 : Blo 1709055 1709475 := bstep (se 1 (by rfl) ⟨1282106, by rfl⟩ : syracuseStep 1709475 = 2564213) B2564213
theorem B5772707 : Blo 1709055 5772707 := bstep (se 1 (by rfl) ⟨4329530, by rfl⟩ : syracuseStep 5772707 = 8659061) B8659061
theorem B1709491 : Blo 1709055 1709491 := bstep (se 1 (by rfl) ⟨1282118, by rfl⟩ : syracuseStep 1709491 = 2564237) B2564237
theorem B1709507 : Blo 1709055 1709507 := bstep (se 1 (by rfl) ⟨1282130, by rfl⟩ : syracuseStep 1709507 = 2564261) B2564261
theorem B1709523 : Blo 1709055 1709523 := bstep (se 1 (by rfl) ⟨1282142, by rfl⟩ : syracuseStep 1709523 = 2564285) B2564285
theorem B1709539 : Blo 1709055 1709539 := bstep (se 1 (by rfl) ⟨1282154, by rfl⟩ : syracuseStep 1709539 = 2564309) B2564309
theorem B4330979 : Blo 1709055 4330979 := bstep (se 1 (by rfl) ⟨3248234, by rfl⟩ : syracuseStep 4330979 = 6496469) B6496469
theorem B1709555 : Blo 1709055 1709555 := bstep (se 1 (by rfl) ⟨1282166, by rfl⟩ : syracuseStep 1709555 = 2564333) B2564333
theorem B1709571 : Blo 1709055 1709571 := bstep (se 1 (by rfl) ⟨1282178, by rfl⟩ : syracuseStep 1709571 = 2564357) B2564357
theorem B7304717 : Blo 1709055 7304717 := bstep (se 3 (by rfl) ⟨1369634, by rfl⟩ : syracuseStep 7304717 = 2739269) B2739269
theorem B3847697 : Blo 1709055 3847697 := bstep (se 2 (by rfl) ⟨1442886, by rfl⟩ : syracuseStep 3847697 = 2885773) B2885773
theorem B1709587 : Blo 1709055 1709587 := bstep (se 1 (by rfl) ⟨1282190, by rfl⟩ : syracuseStep 1709587 = 2564381) B2564381
theorem B1709603 : Blo 1709055 1709603 := bstep (se 1 (by rfl) ⟨1282202, by rfl⟩ : syracuseStep 1709603 = 2564405) B2564405
theorem B3847715 : Blo 1709055 3847715 := bstep (se 1 (by rfl) ⟨2885786, by rfl⟩ : syracuseStep 3847715 = 5771573) B5771573
theorem B1709619 : Blo 1709055 1709619 := bstep (se 1 (by rfl) ⟨1282214, by rfl⟩ : syracuseStep 1709619 = 2564429) B2564429
theorem B1709635 : Blo 1709055 1709635 := bstep (se 1 (by rfl) ⟨1282226, by rfl⟩ : syracuseStep 1709635 = 2564453) B2564453
theorem B6673997 : Blo 1709055 6673997 := bstep (se 3 (by rfl) ⟨1251374, by rfl⟩ : syracuseStep 6673997 = 2502749) B2502749
theorem B1709651 : Blo 1709055 1709651 := bstep (se 1 (by rfl) ⟨1282238, by rfl⟩ : syracuseStep 1709651 = 2564477) B2564477
theorem B1709667 : Blo 1709055 1709667 := bstep (se 1 (by rfl) ⟨1282250, by rfl⟩ : syracuseStep 1709667 = 2564501) B2564501
theorem B1709683 : Blo 1709055 1709683 := bstep (se 1 (by rfl) ⟨1282262, by rfl⟩ : syracuseStep 1709683 = 2564525) B2564525
theorem B1709699 : Blo 1709055 1709699 := bstep (se 1 (by rfl) ⟨1282274, by rfl⟩ : syracuseStep 1709699 = 2564549) B2564549
theorem B1709715 : Blo 1709055 1709715 := bstep (se 1 (by rfl) ⟨1282286, by rfl⟩ : syracuseStep 1709715 = 2564573) B2564573
theorem B1709731 : Blo 1709055 1709731 := bstep (se 1 (by rfl) ⟨1282298, by rfl⟩ : syracuseStep 1709731 = 2564597) B2564597
theorem B9737891 : Blo 1709055 9737891 := bstep (se 1 (by rfl) ⟨7303418, by rfl⟩ : syracuseStep 9737891 = 14606837) B14606837
theorem B5772977 : Blo 1709055 5772977 := bstep (se 2 (by rfl) ⟨2164866, by rfl⟩ : syracuseStep 5772977 = 4329733) B4329733
theorem B1709747 : Blo 1709055 1709747 := bstep (se 1 (by rfl) ⟨1282310, by rfl⟩ : syracuseStep 1709747 = 2564621) B2564621
theorem B1922755 : Blo 1709055 1922755 := bstep (se 1 (by rfl) ⟨1442066, by rfl⟩ : syracuseStep 1922755 = 2884133) B2884133
theorem B1709763 : Blo 1709055 1709763 := bstep (se 1 (by rfl) ⟨1282322, by rfl⟩ : syracuseStep 1709763 = 2564645) B2564645
theorem B4683473 : Blo 1709055 4683473 := bstep (se 2 (by rfl) ⟨1756302, by rfl⟩ : syracuseStep 4683473 = 3512605) B3512605
theorem B1709779 : Blo 1709055 1709779 := bstep (se 1 (by rfl) ⟨1282334, by rfl⟩ : syracuseStep 1709779 = 2564669) B2564669
theorem B1709795 : Blo 1709055 1709795 := bstep (se 1 (by rfl) ⟨1282346, by rfl⟩ : syracuseStep 1709795 = 2564693) B2564693
theorem B1709811 : Blo 1709055 1709811 := bstep (se 1 (by rfl) ⟨1282358, by rfl⟩ : syracuseStep 1709811 = 2564717) B2564717
theorem B1709827 : Blo 1709055 1709827 := bstep (se 1 (by rfl) ⟨1282370, by rfl⟩ : syracuseStep 1709827 = 2564741) B2564741
theorem B14612237 : Blo 1709055 14612237 := bstep (se 3 (by rfl) ⟨2739794, by rfl⟩ : syracuseStep 14612237 = 5479589) B5479589
theorem B1709843 : Blo 1709055 1709843 := bstep (se 1 (by rfl) ⟨1282382, by rfl⟩ : syracuseStep 1709843 = 2564765) B2564765
theorem B1709859 : Blo 1709055 1709859 := bstep (se 1 (by rfl) ⟨1282394, by rfl⟩ : syracuseStep 1709859 = 2564789) B2564789
theorem B3847985 : Blo 1709055 3847985 := bstep (se 2 (by rfl) ⟨1442994, by rfl⟩ : syracuseStep 3847985 = 2885989) B2885989
theorem B1709875 : Blo 1709055 1709875 := bstep (se 1 (by rfl) ⟨1282406, by rfl⟩ : syracuseStep 1709875 = 2564813) B2564813
theorem B1709891 : Blo 1709055 1709891 := bstep (se 1 (by rfl) ⟨1282418, by rfl⟩ : syracuseStep 1709891 = 2564837) B2564837
theorem B3848003 : Blo 1709055 3848003 := bstep (se 1 (by rfl) ⟨2886002, by rfl⟩ : syracuseStep 3848003 = 5772005) B5772005
theorem B1922899 : Blo 1709055 1922899 := bstep (se 1 (by rfl) ⟨1442174, by rfl⟩ : syracuseStep 1922899 = 2884349) B2884349
theorem B1709907 : Blo 1709055 1709907 := bstep (se 1 (by rfl) ⟨1282430, by rfl⟩ : syracuseStep 1709907 = 2564861) B2564861
theorem B1709923 : Blo 1709055 1709923 := bstep (se 1 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 1709923 = 2564885) B2564885
theorem B7305059 : Blo 1709055 7305059 := bstep (se 1 (by rfl) ⟨5478794, by rfl⟩ : syracuseStep 7305059 = 10957589) B10957589
theorem B1709939 : Blo 1709055 1709939 := bstep (se 1 (by rfl) ⟨1282454, by rfl⟩ : syracuseStep 1709939 = 2564909) B2564909
theorem B1709955 : Blo 1709055 1709955 := bstep (se 1 (by rfl) ⟨1282466, by rfl⟩ : syracuseStep 1709955 = 2564933) B2564933
theorem B1709971 : Blo 1709055 1709971 := bstep (se 1 (by rfl) ⟨1282478, by rfl⟩ : syracuseStep 1709971 = 2564957) B2564957
theorem B1709987 : Blo 1709055 1709987 := bstep (se 1 (by rfl) ⟨1282490, by rfl⟩ : syracuseStep 1709987 = 2564981) B2564981
theorem B4872113 : Blo 1709055 4872113 := bstep (se 2 (by rfl) ⟨1827042, by rfl⟩ : syracuseStep 4872113 = 3654085) B3654085
theorem B1710003 : Blo 1709055 1710003 := bstep (se 1 (by rfl) ⟨1282502, by rfl⟩ : syracuseStep 1710003 = 2565005) B2565005
theorem B1710019 : Blo 1709055 1710019 := bstep (se 1 (by rfl) ⟨1282514, by rfl⟩ : syracuseStep 1710019 = 2565029) B2565029
theorem B1710035 : Blo 1709055 1710035 := bstep (se 1 (by rfl) ⟨1282526, by rfl⟩ : syracuseStep 1710035 = 2565053) B2565053
theorem B1923043 : Blo 1709055 1923043 := bstep (se 1 (by rfl) ⟨1442282, by rfl⟩ : syracuseStep 1923043 = 2884565) B2884565
theorem B1710051 : Blo 1709055 1710051 := bstep (se 1 (by rfl) ⟨1282538, by rfl⟩ : syracuseStep 1710051 = 2565077) B2565077
theorem B1710067 : Blo 1709055 1710067 := bstep (se 1 (by rfl) ⟨1282550, by rfl⟩ : syracuseStep 1710067 = 2565101) B2565101
theorem B1710083 : Blo 1709055 1710083 := bstep (se 1 (by rfl) ⟨1282562, by rfl⟩ : syracuseStep 1710083 = 2565125) B2565125
theorem B1710099 : Blo 1709055 1710099 := bstep (se 1 (by rfl) ⟨1282574, by rfl⟩ : syracuseStep 1710099 = 2565149) B2565149
theorem B1710115 : Blo 1709055 1710115 := bstep (se 1 (by rfl) ⟨1282586, by rfl⟩ : syracuseStep 1710115 = 2565173) B2565173
theorem B1710131 : Blo 1709055 1710131 := bstep (se 1 (by rfl) ⟨1282598, by rfl⟩ : syracuseStep 1710131 = 2565197) B2565197
theorem B1710147 : Blo 1709055 1710147 := bstep (se 1 (by rfl) ⟨1282610, by rfl⟩ : syracuseStep 1710147 = 2565221) B2565221
theorem B3848273 : Blo 1709055 3848273 := bstep (se 2 (by rfl) ⟨1443102, by rfl⟩ : syracuseStep 3848273 = 2886205) B2886205
theorem B1710163 : Blo 1709055 1710163 := bstep (se 1 (by rfl) ⟨1282622, by rfl⟩ : syracuseStep 1710163 = 2565245) B2565245
theorem B1710179 : Blo 1709055 1710179 := bstep (se 1 (by rfl) ⟨1282634, by rfl⟩ : syracuseStep 1710179 = 2565269) B2565269
theorem B3848291 : Blo 1709055 3848291 := bstep (se 1 (by rfl) ⟨2886218, by rfl⟩ : syracuseStep 3848291 = 5772437) B5772437
theorem B1923187 : Blo 1709055 1923187 := bstep (se 1 (by rfl) ⟨1442390, by rfl⟩ : syracuseStep 1923187 = 2884781) B2884781
theorem B1710195 : Blo 1709055 1710195 := bstep (se 1 (by rfl) ⟨1282646, by rfl⟩ : syracuseStep 1710195 = 2565293) B2565293
theorem B1710211 : Blo 1709055 1710211 := bstep (se 1 (by rfl) ⟨1282658, by rfl⟩ : syracuseStep 1710211 = 2565317) B2565317
theorem B1710227 : Blo 1709055 1710227 := bstep (se 1 (by rfl) ⟨1282670, by rfl⟩ : syracuseStep 1710227 = 2565341) B2565341
theorem B1710243 : Blo 1709055 1710243 := bstep (se 1 (by rfl) ⟨1282682, by rfl⟩ : syracuseStep 1710243 = 2565365) B2565365
theorem B1710259 : Blo 1709055 1710259 := bstep (se 1 (by rfl) ⟨1282694, by rfl⟩ : syracuseStep 1710259 = 2565389) B2565389
theorem B1710275 : Blo 1709055 1710275 := bstep (se 1 (by rfl) ⟨1282706, by rfl⟩ : syracuseStep 1710275 = 2565413) B2565413
theorem B1710291 : Blo 1709055 1710291 := bstep (se 1 (by rfl) ⟨1282718, by rfl⟩ : syracuseStep 1710291 = 2565437) B2565437
theorem B5773517 : Blo 1709055 5773517 := bstep (se 3 (by rfl) ⟨1082534, by rfl⟩ : syracuseStep 5773517 = 2165069) B2165069
theorem B1710307 : Blo 1709055 1710307 := bstep (se 1 (by rfl) ⟨1282730, by rfl⟩ : syracuseStep 1710307 = 2565461) B2565461
theorem B5478641 : Blo 1709055 5478641 := bstep (se 2 (by rfl) ⟨2054490, by rfl⟩ : syracuseStep 5478641 = 4108981) B4108981
theorem B1710323 : Blo 1709055 1710323 := bstep (se 1 (by rfl) ⟨1282742, by rfl⟩ : syracuseStep 1710323 = 2565485) B2565485
theorem B1923331 : Blo 1709055 1923331 := bstep (se 1 (by rfl) ⟨1442498, by rfl⟩ : syracuseStep 1923331 = 2884997) B2884997
theorem B1710339 : Blo 1709055 1710339 := bstep (se 1 (by rfl) ⟨1282754, by rfl⟩ : syracuseStep 1710339 = 2565509) B2565509
theorem B5773571 : Blo 1709055 5773571 := bstep (se 1 (by rfl) ⟨4330178, by rfl⟩ : syracuseStep 5773571 = 8660357) B8660357
theorem B1710355 : Blo 1709055 1710355 := bstep (se 1 (by rfl) ⟨1282766, by rfl⟩ : syracuseStep 1710355 = 2565533) B2565533
theorem B1710371 : Blo 1709055 1710371 := bstep (se 1 (by rfl) ⟨1282778, by rfl⟩ : syracuseStep 1710371 = 2565557) B2565557
theorem B1710387 : Blo 1709055 1710387 := bstep (se 1 (by rfl) ⟨1282790, by rfl⟩ : syracuseStep 1710387 = 2565581) B2565581
theorem B1710403 : Blo 1709055 1710403 := bstep (se 1 (by rfl) ⟨1282802, by rfl⟩ : syracuseStep 1710403 = 2565605) B2565605
theorem B1710419 : Blo 1709055 1710419 := bstep (se 1 (by rfl) ⟨1282814, by rfl⟩ : syracuseStep 1710419 = 2565629) B2565629
theorem B1710435 : Blo 1709055 1710435 := bstep (se 1 (by rfl) ⟨1282826, by rfl⟩ : syracuseStep 1710435 = 2565653) B2565653
theorem B5478769 : Blo 1709055 5478769 := bstep (se 2 (by rfl) ⟨2054538, by rfl⟩ : syracuseStep 5478769 = 4109077) B4109077
theorem B3848561 : Blo 1709055 3848561 := bstep (se 2 (by rfl) ⟨1443210, by rfl⟩ : syracuseStep 3848561 = 2886421) B2886421
theorem B1710451 : Blo 1709055 1710451 := bstep (se 1 (by rfl) ⟨1282838, by rfl⟩ : syracuseStep 1710451 = 2565677) B2565677
theorem B5003651 : Blo 1709055 5003651 := bstep (se 1 (by rfl) ⟨3752738, by rfl⟩ : syracuseStep 5003651 = 7505477) B7505477
theorem B1710467 : Blo 1709055 1710467 := bstep (se 1 (by rfl) ⟨1282850, by rfl⟩ : syracuseStep 1710467 = 2565701) B2565701
theorem B3848579 : Blo 1709055 3848579 := bstep (se 1 (by rfl) ⟨2886434, by rfl⟩ : syracuseStep 3848579 = 5772869) B5772869
theorem B1923475 : Blo 1709055 1923475 := bstep (se 1 (by rfl) ⟨1442606, by rfl⟩ : syracuseStep 1923475 = 2885213) B2885213
theorem B1710483 : Blo 1709055 1710483 := bstep (se 1 (by rfl) ⟨1282862, by rfl⟩ : syracuseStep 1710483 = 2565725) B2565725
theorem B1710499 : Blo 1709055 1710499 := bstep (se 1 (by rfl) ⟨1282874, by rfl⟩ : syracuseStep 1710499 = 2565749) B2565749
theorem B2963891 : Blo 1709055 2963891 := bstep (se 1 (by rfl) ⟨2222918, by rfl⟩ : syracuseStep 2963891 = 4445837) B4445837
theorem B1710515 : Blo 1709055 1710515 := bstep (se 1 (by rfl) ⟨1282886, by rfl⟩ : syracuseStep 1710515 = 2565773) B2565773
theorem B1710531 : Blo 1709055 1710531 := bstep (se 1 (by rfl) ⟨1282898, by rfl⟩ : syracuseStep 1710531 = 2565797) B2565797
theorem B1710547 : Blo 1709055 1710547 := bstep (se 1 (by rfl) ⟨1282910, by rfl⟩ : syracuseStep 1710547 = 2565821) B2565821
theorem B2341345 : Blo 1709055 2341345 := bstep (se 2 (by rfl) ⟨878004, by rfl⟩ : syracuseStep 2341345 = 1756009) B1756009
theorem B1710563 : Blo 1709055 1710563 := bstep (se 1 (by rfl) ⟨1282922, by rfl⟩ : syracuseStep 1710563 = 2565845) B2565845
theorem B1710579 : Blo 1709055 1710579 := bstep (se 1 (by rfl) ⟨1282934, by rfl⟩ : syracuseStep 1710579 = 2565869) B2565869
theorem B1710595 : Blo 1709055 1710595 := bstep (se 1 (by rfl) ⟨1282946, by rfl⟩ : syracuseStep 1710595 = 2565893) B2565893
theorem B5773841 : Blo 1709055 5773841 := bstep (se 2 (by rfl) ⟨2165190, by rfl⟩ : syracuseStep 5773841 = 4330381) B4330381
theorem B1710611 : Blo 1709055 1710611 := bstep (se 1 (by rfl) ⟨1282958, by rfl⟩ : syracuseStep 1710611 = 2565917) B2565917
theorem B1923619 : Blo 1709055 1923619 := bstep (se 1 (by rfl) ⟨1442714, by rfl⟩ : syracuseStep 1923619 = 2885429) B2885429
theorem B1710627 : Blo 1709055 1710627 := bstep (se 1 (by rfl) ⟨1282970, by rfl⟩ : syracuseStep 1710627 = 2565941) B2565941
theorem B1710643 : Blo 1709055 1710643 := bstep (se 1 (by rfl) ⟨1282982, by rfl⟩ : syracuseStep 1710643 = 2565965) B2565965
theorem B1710659 : Blo 1709055 1710659 := bstep (se 1 (by rfl) ⟨1282994, by rfl⟩ : syracuseStep 1710659 = 2565989) B2565989
theorem B1710675 : Blo 1709055 1710675 := bstep (se 1 (by rfl) ⟨1283006, by rfl⟩ : syracuseStep 1710675 = 2566013) B2566013
theorem B2054755 : Blo 1709055 2054755 := bstep (se 1 (by rfl) ⟨1541066, by rfl⟩ : syracuseStep 2054755 = 3082133) B3082133
theorem B1710691 : Blo 1709055 1710691 := bstep (se 1 (by rfl) ⟨1283018, by rfl⟩ : syracuseStep 1710691 = 2566037) B2566037
theorem B16439921 : Blo 1709055 16439921 := bstep (se 2 (by rfl) ⟨6164970, by rfl⟩ : syracuseStep 16439921 = 12329941) B12329941
theorem B1710707 : Blo 1709055 1710707 := bstep (se 1 (by rfl) ⟨1283030, by rfl⟩ : syracuseStep 1710707 = 2566061) B2566061
theorem B1710723 : Blo 1709055 1710723 := bstep (se 1 (by rfl) ⟨1283042, by rfl⟩ : syracuseStep 1710723 = 2566085) B2566085
theorem B9738893 : Blo 1709055 9738893 := bstep (se 3 (by rfl) ⟨1826042, by rfl⟩ : syracuseStep 9738893 = 3652085) B3652085
theorem B3848849 : Blo 1709055 3848849 := bstep (se 2 (by rfl) ⟨1443318, by rfl⟩ : syracuseStep 3848849 = 2886637) B2886637
theorem B1710739 : Blo 1709055 1710739 := bstep (se 1 (by rfl) ⟨1283054, by rfl⟩ : syracuseStep 1710739 = 2566109) B2566109
theorem B3848867 : Blo 1709055 3848867 := bstep (se 1 (by rfl) ⟨2886650, by rfl⟩ : syracuseStep 3848867 = 5773301) B5773301
theorem B1710755 : Blo 1709055 1710755 := bstep (se 1 (by rfl) ⟨1283066, by rfl⟩ : syracuseStep 1710755 = 2566133) B2566133
theorem B1923763 : Blo 1709055 1923763 := bstep (se 1 (by rfl) ⟨1442822, by rfl⟩ : syracuseStep 1923763 = 2885645) B2885645
theorem B1710771 : Blo 1709055 1710771 := bstep (se 1 (by rfl) ⟨1283078, by rfl⟩ : syracuseStep 1710771 = 2566157) B2566157
theorem B1710787 : Blo 1709055 1710787 := bstep (se 1 (by rfl) ⟨1283090, by rfl⟩ : syracuseStep 1710787 = 2566181) B2566181
theorem B1710803 : Blo 1709055 1710803 := bstep (se 1 (by rfl) ⟨1283102, by rfl⟩ : syracuseStep 1710803 = 2566205) B2566205
theorem B1710819 : Blo 1709055 1710819 := bstep (se 1 (by rfl) ⟨1283114, by rfl⟩ : syracuseStep 1710819 = 2566229) B2566229
theorem B5200625 : Blo 1709055 5200625 := bstep (se 2 (by rfl) ⟨1950234, by rfl⟩ : syracuseStep 5200625 = 3900469) B3900469
theorem B1710835 : Blo 1709055 1710835 := bstep (se 1 (by rfl) ⟨1283126, by rfl⟩ : syracuseStep 1710835 = 2566253) B2566253
theorem B1710851 : Blo 1709055 1710851 := bstep (se 1 (by rfl) ⟨1283138, by rfl⟩ : syracuseStep 1710851 = 2566277) B2566277
theorem B1710867 : Blo 1709055 1710867 := bstep (se 1 (by rfl) ⟨1283150, by rfl⟩ : syracuseStep 1710867 = 2566301) B2566301
theorem B6495011 : Blo 1709055 6495011 := bstep (se 1 (by rfl) ⟨4871258, by rfl⟩ : syracuseStep 6495011 = 9742517) B9742517
theorem B1710883 : Blo 1709055 1710883 := bstep (se 1 (by rfl) ⟨1283162, by rfl⟩ : syracuseStep 1710883 = 2566325) B2566325
theorem B6495025 : Blo 1709055 6495025 := bstep (se 2 (by rfl) ⟨2435634, by rfl⟩ : syracuseStep 6495025 = 4871269) B4871269
theorem B1710899 : Blo 1709055 1710899 := bstep (se 1 (by rfl) ⟨1283174, by rfl⟩ : syracuseStep 1710899 = 2566349) B2566349
theorem B1923907 : Blo 1709055 1923907 := bstep (se 1 (by rfl) ⟨1442930, by rfl⟩ : syracuseStep 1923907 = 2885861) B2885861
theorem B1710915 : Blo 1709055 1710915 := bstep (se 1 (by rfl) ⟨1283186, by rfl⟩ : syracuseStep 1710915 = 2566373) B2566373
theorem B1710931 : Blo 1709055 1710931 := bstep (se 1 (by rfl) ⟨1283198, by rfl⟩ : syracuseStep 1710931 = 2566397) B2566397
theorem B1710947 : Blo 1709055 1710947 := bstep (se 1 (by rfl) ⟨1283210, by rfl⟩ : syracuseStep 1710947 = 2566421) B2566421
theorem B1710963 : Blo 1709055 1710963 := bstep (se 1 (by rfl) ⟨1283222, by rfl⟩ : syracuseStep 1710963 = 2566445) B2566445
theorem B1710979 : Blo 1709055 1710979 := bstep (se 1 (by rfl) ⟨1283234, by rfl⟩ : syracuseStep 1710979 = 2566469) B2566469
theorem B1710995 : Blo 1709055 1710995 := bstep (se 1 (by rfl) ⟨1283246, by rfl⟩ : syracuseStep 1710995 = 2566493) B2566493
theorem B1711011 : Blo 1709055 1711011 := bstep (se 1 (by rfl) ⟨1283258, by rfl⟩ : syracuseStep 1711011 = 2566517) B2566517
theorem B3849137 : Blo 1709055 3849137 := bstep (se 2 (by rfl) ⟨1443426, by rfl⟩ : syracuseStep 3849137 = 2886853) B2886853
theorem B1711027 : Blo 1709055 1711027 := bstep (se 1 (by rfl) ⟨1283270, by rfl⟩ : syracuseStep 1711027 = 2566541) B2566541
theorem B3849155 : Blo 1709055 3849155 := bstep (se 1 (by rfl) ⟨2886866, by rfl⟩ : syracuseStep 3849155 = 5773733) B5773733
theorem B1711043 : Blo 1709055 1711043 := bstep (se 1 (by rfl) ⟨1283282, by rfl⟩ : syracuseStep 1711043 = 2566565) B2566565
theorem B1924051 : Blo 1709055 1924051 := bstep (se 1 (by rfl) ⟨1443038, by rfl⟩ : syracuseStep 1924051 = 2886077) B2886077
theorem B5774381 : Blo 1709055 5774381 := bstep (se 3 (by rfl) ⟨1082696, by rfl⟩ : syracuseStep 5774381 = 2165393) B2165393
theorem B1924195 : Blo 1709055 1924195 := bstep (se 1 (by rfl) ⟨1443146, by rfl⟩ : syracuseStep 1924195 = 2886293) B2886293
theorem B3611747 : Blo 1709055 3611747 := bstep (se 1 (by rfl) ⟨2708810, by rfl⟩ : syracuseStep 3611747 = 5417621) B5417621
theorem B5774435 : Blo 1709055 5774435 := bstep (se 1 (by rfl) ⟨4330826, by rfl⟩ : syracuseStep 5774435 = 8661653) B8661653
theorem B10960049 : Blo 1709055 10960049 := bstep (se 2 (by rfl) ⟨4110018, by rfl⟩ : syracuseStep 10960049 = 8220037) B8220037
theorem B3849425 : Blo 1709055 3849425 := bstep (se 2 (by rfl) ⟨1443534, by rfl⟩ : syracuseStep 3849425 = 2887069) B2887069
theorem B3849443 : Blo 1709055 3849443 := bstep (se 1 (by rfl) ⟨2887082, by rfl⟩ : syracuseStep 3849443 = 5774165) B5774165
theorem B1924339 : Blo 1709055 1924339 := bstep (se 1 (by rfl) ⟨1443254, by rfl⟩ : syracuseStep 1924339 = 2886509) B2886509
theorem B10951949 : Blo 1709055 10951949 := bstep (se 3 (by rfl) ⟨2053490, by rfl⟩ : syracuseStep 10951949 = 4106981) B4106981
theorem B6159665 : Blo 1709055 6159665 := bstep (se 2 (by rfl) ⟨2309874, by rfl⟩ : syracuseStep 6159665 = 4619749) B4619749
theorem B5479757 : Blo 1709055 5479757 := bstep (se 3 (by rfl) ⟨1027454, by rfl⟩ : syracuseStep 5479757 = 2054909) B2054909
theorem B5774705 : Blo 1709055 5774705 := bstep (se 2 (by rfl) ⟨2165514, by rfl⟩ : syracuseStep 5774705 = 4331029) B4331029
theorem B1924483 : Blo 1709055 1924483 := bstep (se 1 (by rfl) ⟨1443362, by rfl⟩ : syracuseStep 1924483 = 2886725) B2886725
theorem B6929869 : Blo 1709055 6929869 := bstep (se 3 (by rfl) ⟨1299350, by rfl⟩ : syracuseStep 6929869 = 2598701) B2598701
theorem B3849713 : Blo 1709055 3849713 := bstep (se 2 (by rfl) ⟨1443642, by rfl⟩ : syracuseStep 3849713 = 2887285) B2887285
theorem B3849731 : Blo 1709055 3849731 := bstep (se 1 (by rfl) ⟨2887298, by rfl⟩ : syracuseStep 3849731 = 5774597) B5774597
theorem B2563601 : Blo 1709055 2563601 := bstep (se 2 (by rfl) ⟨961350, by rfl⟩ : syracuseStep 2563601 = 1922701) B1922701
theorem B1924627 : Blo 1709055 1924627 := bstep (se 1 (by rfl) ⟨1443470, by rfl⟩ : syracuseStep 1924627 = 2886941) B2886941
theorem B2563619 : Blo 1709055 2563619 := bstep (se 1 (by rfl) ⟨1922714, by rfl⟩ : syracuseStep 2563619 = 3845429) B3845429
theorem B2563649 : Blo 1709055 2563649 := bstep (se 2 (by rfl) ⟨961368, by rfl⟩ : syracuseStep 2563649 = 1922737) B1922737
theorem B2563667 : Blo 1709055 2563667 := bstep (se 1 (by rfl) ⟨1922750, by rfl⟩ : syracuseStep 2563667 = 3845501) B3845501
theorem B2563697 : Blo 1709055 2563697 := bstep (se 2 (by rfl) ⟨961386, by rfl⟩ : syracuseStep 2563697 = 1922773) B1922773
theorem B20799089 : Blo 1709055 20799089 := bstep (se 2 (by rfl) ⟨7799658, by rfl⟩ : syracuseStep 20799089 = 15599317) B15599317
theorem B2924147 : Blo 1709055 2924147 := bstep (se 1 (by rfl) ⟨2193110, by rfl⟩ : syracuseStep 2924147 = 4386221) B4386221
theorem B13868657 : Blo 1709055 13868657 := bstep (se 2 (by rfl) ⟨5200746, by rfl⟩ : syracuseStep 13868657 = 10401493) B10401493
theorem B2563715 : Blo 1709055 2563715 := bstep (se 1 (by rfl) ⟨1922786, by rfl⟩ : syracuseStep 2563715 = 3845573) B3845573
theorem B2563745 : Blo 1709055 2563745 := bstep (se 2 (by rfl) ⟨961404, by rfl⟩ : syracuseStep 2563745 = 1922809) B1922809
theorem B1924771 : Blo 1709055 1924771 := bstep (se 1 (by rfl) ⟨1443578, by rfl⟩ : syracuseStep 1924771 = 2887157) B2887157
theorem B2563763 : Blo 1709055 2563763 := bstep (se 1 (by rfl) ⟨1922822, by rfl⟩ : syracuseStep 2563763 = 3845645) B3845645
theorem B2563793 : Blo 1709055 2563793 := bstep (se 2 (by rfl) ⟨961422, by rfl⟩ : syracuseStep 2563793 = 1922845) B1922845
theorem B1949395 : Blo 1709055 1949395 := bstep (se 1 (by rfl) ⟨1462046, by rfl⟩ : syracuseStep 1949395 = 2924093) B2924093
theorem B2563811 : Blo 1709055 2563811 := bstep (se 1 (by rfl) ⟨1922858, by rfl⟩ : syracuseStep 2563811 = 3845717) B3845717
theorem B2563841 : Blo 1709055 2563841 := bstep (se 2 (by rfl) ⟨961440, by rfl⟩ : syracuseStep 2563841 = 1922881) B1922881
theorem B2563859 : Blo 1709055 2563859 := bstep (se 1 (by rfl) ⟨1922894, by rfl⟩ : syracuseStep 2563859 = 3845789) B3845789
theorem B2563889 : Blo 1709055 2563889 := bstep (se 2 (by rfl) ⟨961458, by rfl⟩ : syracuseStep 2563889 = 1922917) B1922917
theorem B8658737 : Blo 1709055 8658737 := bstep (se 2 (by rfl) ⟨3247026, by rfl⟩ : syracuseStep 8658737 = 6494053) B6494053
theorem B1924915 : Blo 1709055 1924915 := bstep (se 1 (by rfl) ⟨1443686, by rfl⟩ : syracuseStep 1924915 = 2887373) B2887373
theorem B2563907 : Blo 1709055 2563907 := bstep (se 1 (by rfl) ⟨1922930, by rfl⟩ : syracuseStep 2563907 = 3845861) B3845861
theorem B2563937 : Blo 1709055 2563937 := bstep (se 2 (by rfl) ⟨961476, by rfl⟩ : syracuseStep 2563937 = 1922953) B1922953
theorem B2563955 : Blo 1709055 2563955 := bstep (se 1 (by rfl) ⟨1922966, by rfl⟩ : syracuseStep 2563955 = 3845933) B3845933
theorem B2563985 : Blo 1709055 2563985 := bstep (se 2 (by rfl) ⟨961494, by rfl⟩ : syracuseStep 2563985 = 1922989) B1922989
theorem B2924435 : Blo 1709055 2924435 := bstep (se 1 (by rfl) ⟨2193326, by rfl⟩ : syracuseStep 2924435 = 4386653) B4386653
theorem B2564003 : Blo 1709055 2564003 := bstep (se 1 (by rfl) ⟨1923002, by rfl⟩ : syracuseStep 2564003 = 3846005) B3846005
theorem B11861923 : Blo 1709055 11861923 := bstep (se 1 (by rfl) ⟨8896442, by rfl⟩ : syracuseStep 11861923 = 17792885) B17792885
theorem B2564033 : Blo 1709055 2564033 := bstep (se 2 (by rfl) ⟨961512, by rfl⟩ : syracuseStep 2564033 = 1923025) B1923025
theorem B2564051 : Blo 1709055 2564051 := bstep (se 1 (by rfl) ⟨1923038, by rfl⟩ : syracuseStep 2564051 = 3846077) B3846077
theorem B2564081 : Blo 1709055 2564081 := bstep (se 2 (by rfl) ⟨961530, by rfl⟩ : syracuseStep 2564081 = 1923061) B1923061
theorem B1826803 : Blo 1709055 1826803 := bstep (se 1 (by rfl) ⟨1370102, by rfl⟩ : syracuseStep 1826803 = 2740205) B2740205
theorem B6160387 : Blo 1709055 6160387 := bstep (se 1 (by rfl) ⟨4620290, by rfl⟩ : syracuseStep 6160387 = 9240581) B9240581
theorem B6496301 : Blo 1709055 6496301 := bstep (se 3 (by rfl) ⟨1218056, by rfl⟩ : syracuseStep 6496301 = 2436113) B2436113
theorem B2564171 : Blo 1709055 2564171 := bstep (se 1 (by rfl) ⟨1923128, by rfl⟩ : syracuseStep 2564171 = 3846257) B3846257
theorem B2564183 : Blo 1709055 2564183 := bstep (se 1 (by rfl) ⟨1923137, by rfl⟩ : syracuseStep 2564183 = 3846275) B3846275
theorem B13156445 : Blo 1709055 13156445 := bstep (se 3 (by rfl) ⟨2466833, by rfl⟩ : syracuseStep 13156445 = 4933667) B4933667
theorem B2564249 : Blo 1709055 2564249 := bstep (se 2 (by rfl) ⟨961593, by rfl⟩ : syracuseStep 2564249 = 1923187) B1923187
theorem B2564363 : Blo 1709055 2564363 := bstep (se 1 (by rfl) ⟨1923272, by rfl⟩ : syracuseStep 2564363 = 3846545) B3846545
theorem B2564375 : Blo 1709055 2564375 := bstep (se 1 (by rfl) ⟨1923281, by rfl⟩ : syracuseStep 2564375 = 3846563) B3846563
theorem B4686155 : Blo 1709055 4686155 := bstep (se 1 (by rfl) ⟨3514616, by rfl⟩ : syracuseStep 4686155 = 7029233) B7029233
theorem B2564441 : Blo 1709055 2564441 := bstep (se 2 (by rfl) ⟨961665, by rfl⟩ : syracuseStep 2564441 = 1923331) B1923331
theorem B8216963 : Blo 1709055 8216963 := bstep (se 1 (by rfl) ⟨6162722, by rfl⟩ : syracuseStep 8216963 = 12325445) B12325445
theorem B3654067 : Blo 1709055 3654067 := bstep (se 1 (by rfl) ⟨2740550, by rfl⟩ : syracuseStep 3654067 = 5481101) B5481101
theorem B2564555 : Blo 1709055 2564555 := bstep (se 1 (by rfl) ⟨1923416, by rfl⟩ : syracuseStep 2564555 = 3846833) B3846833
theorem B2564567 : Blo 1709055 2564567 := bstep (se 1 (by rfl) ⟨1923425, by rfl⟩ : syracuseStep 2564567 = 3846851) B3846851
theorem B2564633 : Blo 1709055 2564633 := bstep (se 2 (by rfl) ⟨961737, by rfl⟩ : syracuseStep 2564633 = 1923475) B1923475
theorem B2163287 : Blo 1709055 2163287 := bstep (se 1 (by rfl) ⟨1622465, by rfl⟩ : syracuseStep 2163287 = 3244931) B3244931
theorem B3121793 : Blo 1709055 3121793 := bstep (se 2 (by rfl) ⟨1170672, by rfl⟩ : syracuseStep 3121793 = 2341345) B2341345
theorem B3244673 : Blo 1709055 3244673 := bstep (se 2 (by rfl) ⟨1216752, by rfl⟩ : syracuseStep 3244673 = 2433505) B2433505
theorem B2564747 : Blo 1709055 2564747 := bstep (se 1 (by rfl) ⟨1923560, by rfl⟩ : syracuseStep 2564747 = 3847121) B3847121
theorem B19473047 : Blo 1709055 19473047 := bstep (se 1 (by rfl) ⟨14604785, by rfl⟩ : syracuseStep 19473047 = 29209571) B29209571
theorem B2564759 : Blo 1709055 2564759 := bstep (se 1 (by rfl) ⟨1923569, by rfl⟩ : syracuseStep 2564759 = 3847139) B3847139
theorem B3703475 : Blo 1709055 3703475 := bstep (se 1 (by rfl) ⟨2777606, by rfl⟩ : syracuseStep 3703475 = 5555213) B5555213
theorem B29205197 : Blo 1709055 29205197 := bstep (se 3 (by rfl) ⟨5475974, by rfl⟩ : syracuseStep 29205197 = 10951949) B10951949
theorem B2564825 : Blo 1709055 2564825 := bstep (se 2 (by rfl) ⟨961809, by rfl⟩ : syracuseStep 2564825 = 1923619) B1923619
theorem B16425773 : Blo 1709055 16425773 := bstep (se 3 (by rfl) ⟨3079832, by rfl⟩ : syracuseStep 16425773 = 6159665) B6159665
theorem B2564939 : Blo 1709055 2564939 := bstep (se 1 (by rfl) ⟨1923704, by rfl⟩ : syracuseStep 2564939 = 3847409) B3847409
theorem B2564951 : Blo 1709055 2564951 := bstep (se 1 (by rfl) ⟨1923713, by rfl⟩ : syracuseStep 2564951 = 3847427) B3847427
theorem B3703681 : Blo 1709055 3703681 := bstep (se 2 (by rfl) ⟨1388880, by rfl⟩ : syracuseStep 3703681 = 2777761) B2777761
theorem B6579089 : Blo 1709055 6579089 := bstep (se 2 (by rfl) ⟨2467158, by rfl⟩ : syracuseStep 6579089 = 4934317) B4934317
theorem B2565017 : Blo 1709055 2565017 := bstep (se 2 (by rfl) ⟨961881, by rfl⟩ : syracuseStep 2565017 = 1923763) B1923763
theorem B3245015 : Blo 1709055 3245015 := bstep (se 1 (by rfl) ⟨2433761, by rfl⟩ : syracuseStep 3245015 = 4867523) B4867523
theorem B2311129 : Blo 1709055 2311129 := bstep (se 2 (by rfl) ⟨866673, by rfl⟩ : syracuseStep 2311129 = 1733347) B1733347
theorem B2884619 : Blo 1709055 2884619 := bstep (se 1 (by rfl) ⟨2163464, by rfl⟩ : syracuseStep 2884619 = 4326929) B4326929
theorem B2565131 : Blo 1709055 2565131 := bstep (se 1 (by rfl) ⟨1923848, by rfl⟩ : syracuseStep 2565131 = 3847697) B3847697
theorem B2565143 : Blo 1709055 2565143 := bstep (se 1 (by rfl) ⟨1923857, by rfl⟩ : syracuseStep 2565143 = 3847715) B3847715
theorem B4867123 : Blo 1709055 4867123 := bstep (se 1 (by rfl) ⟨3650342, by rfl⟩ : syracuseStep 4867123 = 7300685) B7300685
theorem B4449331 : Blo 1709055 4449331 := bstep (se 1 (by rfl) ⟨3336998, by rfl⟩ : syracuseStep 4449331 = 6673997) B6673997
theorem B8660033 : Blo 1709055 8660033 := bstep (se 2 (by rfl) ⟨3247512, by rfl⟩ : syracuseStep 8660033 = 6495025) B6495025
theorem B35587147 : Blo 1709055 35587147 := bstep (se 1 (by rfl) ⟨26690360, by rfl⟩ : syracuseStep 35587147 = 53380721) B53380721
theorem B2565209 : Blo 1709055 2565209 := bstep (se 2 (by rfl) ⟨961953, by rfl⟩ : syracuseStep 2565209 = 1923907) B1923907
theorem B3122315 : Blo 1709055 3122315 := bstep (se 1 (by rfl) ⟨2341736, by rfl⟩ : syracuseStep 3122315 = 4683473) B4683473
theorem B2884747 : Blo 1709055 2884747 := bstep (se 1 (by rfl) ⟨2163560, by rfl⟩ : syracuseStep 2884747 = 4327121) B4327121
theorem B5850263 : Blo 1709055 5850263 := bstep (se 1 (by rfl) ⟨4387697, by rfl⟩ : syracuseStep 5850263 = 8775395) B8775395
theorem B9741491 : Blo 1709055 9741491 := bstep (se 1 (by rfl) ⟨7306118, by rfl⟩ : syracuseStep 9741491 = 14612237) B14612237
theorem B10405043 : Blo 1709055 10405043 := bstep (se 1 (by rfl) ⟨7803782, by rfl⟩ : syracuseStep 10405043 = 15607565) B15607565
theorem B2565323 : Blo 1709055 2565323 := bstep (se 1 (by rfl) ⟨1923992, by rfl⟩ : syracuseStep 2565323 = 3847985) B3847985
theorem B2565335 : Blo 1709055 2565335 := bstep (se 1 (by rfl) ⟨1924001, by rfl⟩ : syracuseStep 2565335 = 3848003) B3848003
theorem B2163991 : Blo 1709055 2163991 := bstep (se 1 (by rfl) ⟨1622993, by rfl⟩ : syracuseStep 2163991 = 3245987) B3245987
theorem B2884889 : Blo 1709055 2884889 := bstep (se 2 (by rfl) ⟨1081833, by rfl⟩ : syracuseStep 2884889 = 2163667) B2163667
theorem B2565401 : Blo 1709055 2565401 := bstep (se 2 (by rfl) ⟨962025, by rfl⟩ : syracuseStep 2565401 = 1924051) B1924051
theorem B3900761 : Blo 1709055 3900761 := bstep (se 2 (by rfl) ⟨1462785, by rfl⟩ : syracuseStep 3900761 = 2925571) B2925571
theorem B2565515 : Blo 1709055 2565515 := bstep (se 1 (by rfl) ⟨1924136, by rfl⟩ : syracuseStep 2565515 = 3848273) B3848273
theorem B7800209 : Blo 1709055 7800209 := bstep (se 2 (by rfl) ⟨2925078, by rfl⟩ : syracuseStep 7800209 = 5850157) B5850157
theorem B2565527 : Blo 1709055 2565527 := bstep (se 1 (by rfl) ⟨1924145, by rfl⟩ : syracuseStep 2565527 = 3848291) B3848291
theorem B2885017 : Blo 1709055 2885017 := bstep (se 2 (by rfl) ⟨1081881, by rfl⟩ : syracuseStep 2885017 = 2163763) B2163763
theorem B2565593 : Blo 1709055 2565593 := bstep (se 2 (by rfl) ⟨962097, by rfl⟩ : syracuseStep 2565593 = 1924195) B1924195
theorem B24659417 : Blo 1709055 24659417 := bstep (se 2 (by rfl) ⟨9247281, by rfl⟩ : syracuseStep 24659417 = 18494563) B18494563
theorem B6489665 : Blo 1709055 6489665 := bstep (se 2 (by rfl) ⟨2433624, by rfl⟩ : syracuseStep 6489665 = 4867249) B4867249
theorem B3466817 : Blo 1709055 3466817 := bstep (se 2 (by rfl) ⟨1300056, by rfl⟩ : syracuseStep 3466817 = 2600113) B2600113
theorem B2565707 : Blo 1709055 2565707 := bstep (se 1 (by rfl) ⟨1924280, by rfl⟩ : syracuseStep 2565707 = 3848561) B3848561
theorem B2565719 : Blo 1709055 2565719 := bstep (se 1 (by rfl) ⟨1924289, by rfl⟩ : syracuseStep 2565719 = 3848579) B3848579
theorem B3245683 : Blo 1709055 3245683 := bstep (se 1 (by rfl) ⟨2434262, by rfl⟩ : syracuseStep 3245683 = 4868525) B4868525
theorem B1975927 : Blo 1709055 1975927 := bstep (se 1 (by rfl) ⟨1481945, by rfl⟩ : syracuseStep 1975927 = 2963891) B2963891
theorem B8652419 : Blo 1709055 8652419 := bstep (se 1 (by rfl) ⟨6489314, by rfl⟩ : syracuseStep 8652419 = 12978629) B12978629
theorem B2565785 : Blo 1709055 2565785 := bstep (se 2 (by rfl) ⟨962169, by rfl⟩ : syracuseStep 2565785 = 1924339) B1924339
theorem B4327091 : Blo 1709055 4327091 := bstep (se 1 (by rfl) ⟨3245318, by rfl⟩ : syracuseStep 4327091 = 6490637) B6490637
theorem B14059187 : Blo 1709055 14059187 := bstep (se 1 (by rfl) ⟨10544390, by rfl⟩ : syracuseStep 14059187 = 21088781) B21088781
theorem B10962611 : Blo 1709055 10962611 := bstep (se 1 (by rfl) ⟨8221958, by rfl⟩ : syracuseStep 10962611 = 16443917) B16443917
theorem B20801285 : Blo 1709055 20801285 := bstep (se 4 (by rfl) ⟨1950120, by rfl⟩ : syracuseStep 20801285 = 3900241) B3900241
theorem B2565899 : Blo 1709055 2565899 := bstep (se 1 (by rfl) ⟨1924424, by rfl⟩ : syracuseStep 2565899 = 3848849) B3848849
theorem B2565911 : Blo 1709055 2565911 := bstep (se 1 (by rfl) ⟨1924433, by rfl⟩ : syracuseStep 2565911 = 3848867) B3848867
theorem B5769035 : Blo 1709055 5769035 := bstep (se 1 (by rfl) ⟨4326776, by rfl⟩ : syracuseStep 5769035 = 8653553) B8653553
theorem B3467083 : Blo 1709055 3467083 := bstep (se 1 (by rfl) ⟨2600312, by rfl⟩ : syracuseStep 3467083 = 5200625) B5200625
theorem B2565977 : Blo 1709055 2565977 := bstep (se 2 (by rfl) ⟨962241, by rfl⟩ : syracuseStep 2565977 = 1924483) B1924483
theorem B15599537 : Blo 1709055 15599537 := bstep (se 2 (by rfl) ⟨5849826, by rfl⟩ : syracuseStep 15599537 = 11699653) B11699653
theorem B2566091 : Blo 1709055 2566091 := bstep (se 1 (by rfl) ⟨1924568, by rfl⟩ : syracuseStep 2566091 = 3849137) B3849137
theorem B2885591 : Blo 1709055 2885591 := bstep (se 1 (by rfl) ⟨2164193, by rfl⟩ : syracuseStep 2885591 = 4328387) B4328387
theorem B2566103 : Blo 1709055 2566103 := bstep (se 1 (by rfl) ⟨1924577, by rfl⟩ : syracuseStep 2566103 = 3849155) B3849155
theorem B2566169 : Blo 1709055 2566169 := bstep (se 2 (by rfl) ⟨962313, by rfl⟩ : syracuseStep 2566169 = 1924627) B1924627
theorem B14616611 : Blo 1709055 14616611 := bstep (se 1 (by rfl) ⟨10962458, by rfl⟩ : syracuseStep 14616611 = 21924917) B21924917
theorem B3246131 : Blo 1709055 3246131 := bstep (se 1 (by rfl) ⟨2434598, by rfl⟩ : syracuseStep 3246131 = 4869197) B4869197
theorem B4868171 : Blo 1709055 4868171 := bstep (se 1 (by rfl) ⟨3651128, by rfl⟩ : syracuseStep 4868171 = 7302257) B7302257
theorem B2885719 : Blo 1709055 2885719 := bstep (se 1 (by rfl) ⟨2164289, by rfl⟩ : syracuseStep 2885719 = 4328579) B4328579
theorem B5769305 : Blo 1709055 5769305 := bstep (se 2 (by rfl) ⟨2163489, by rfl⟩ : syracuseStep 5769305 = 4326979) B4326979
theorem B3246169 : Blo 1709055 3246169 := bstep (se 2 (by rfl) ⟨1217313, by rfl⟩ : syracuseStep 3246169 = 2434627) B2434627
theorem B2566283 : Blo 1709055 2566283 := bstep (se 1 (by rfl) ⟨1924712, by rfl⟩ : syracuseStep 2566283 = 3849425) B3849425
theorem B2566295 : Blo 1709055 2566295 := bstep (se 1 (by rfl) ⟨1924721, by rfl⟩ : syracuseStep 2566295 = 3849443) B3849443
theorem B4327627 : Blo 1709055 4327627 := bstep (se 1 (by rfl) ⟨3245720, by rfl⟩ : syracuseStep 4327627 = 6491441) B6491441
theorem B2566361 : Blo 1709055 2566361 := bstep (se 2 (by rfl) ⟨962385, by rfl⟩ : syracuseStep 2566361 = 1924771) B1924771
theorem B2738443 : Blo 1709055 2738443 := bstep (se 1 (by rfl) ⟨2053832, by rfl⟩ : syracuseStep 2738443 = 4107665) B4107665
theorem B2599193 : Blo 1709055 2599193 := bstep (se 2 (by rfl) ⟨974697, by rfl⟩ : syracuseStep 2599193 = 1949395) B1949395
theorem B12323137 : Blo 1709055 12323137 := bstep (se 2 (by rfl) ⟨4621176, by rfl⟩ : syracuseStep 12323137 = 9242353) B9242353
theorem B2566475 : Blo 1709055 2566475 := bstep (se 1 (by rfl) ⟨1924856, by rfl⟩ : syracuseStep 2566475 = 3849713) B3849713
theorem B3901783 : Blo 1709055 3901783 := bstep (se 1 (by rfl) ⟨2926337, by rfl⟩ : syracuseStep 3901783 = 5852675) B5852675
theorem B4327769 : Blo 1709055 4327769 := bstep (se 2 (by rfl) ⟨1622913, by rfl⟩ : syracuseStep 4327769 = 3245827) B3245827
theorem B2566487 : Blo 1709055 2566487 := bstep (se 1 (by rfl) ⟨1924865, by rfl⟩ : syracuseStep 2566487 = 3849731) B3849731
theorem B2566553 : Blo 1709055 2566553 := bstep (se 2 (by rfl) ⟨962457, by rfl⟩ : syracuseStep 2566553 = 1924915) B1924915
theorem B3246617 : Blo 1709055 3246617 := bstep (se 2 (by rfl) ⟨1217481, by rfl⟩ : syracuseStep 3246617 = 2434963) B2434963
theorem B9734701 : Blo 1709055 9734701 := bstep (se 3 (by rfl) ⟨1825256, by rfl⟩ : syracuseStep 9734701 = 3650513) B3650513
theorem B9742949 : Blo 1709055 9742949 := bstep (se 4 (by rfl) ⟨913401, by rfl⟩ : syracuseStep 9742949 = 1826803) B1826803
theorem B2886347 : Blo 1709055 2886347 := bstep (se 1 (by rfl) ⟨2164760, by rfl⟩ : syracuseStep 2886347 = 4329521) B4329521
theorem B14617361 : Blo 1709055 14617361 := bstep (se 2 (by rfl) ⟨5481510, by rfl⟩ : syracuseStep 14617361 = 10963021) B10963021
theorem B5770007 : Blo 1709055 5770007 := bstep (se 1 (by rfl) ⟨4327505, by rfl⟩ : syracuseStep 5770007 = 8655011) B8655011
theorem B6490925 : Blo 1709055 6490925 := bstep (se 3 (by rfl) ⟨1217048, by rfl⟩ : syracuseStep 6490925 = 2434097) B2434097
theorem B6490955 : Blo 1709055 6490955 := bstep (se 1 (by rfl) ⟨4868216, by rfl⟩ : syracuseStep 6490955 = 9736433) B9736433
theorem B2886475 : Blo 1709055 2886475 := bstep (se 1 (by rfl) ⟨2164856, by rfl⟩ : syracuseStep 2886475 = 4329713) B4329713
theorem B11111347 : Blo 1709055 11111347 := bstep (se 1 (by rfl) ⟨8333510, by rfl⟩ : syracuseStep 11111347 = 16667021) B16667021
theorem B2886617 : Blo 1709055 2886617 := bstep (se 2 (by rfl) ⟨1082481, by rfl⟩ : syracuseStep 2886617 = 2164963) B2164963
theorem B8661977 : Blo 1709055 8661977 := bstep (se 2 (by rfl) ⟨3248241, by rfl⟩ : syracuseStep 8661977 = 6496483) B6496483
theorem B35105861 : Blo 1709055 35105861 := bstep (se 4 (by rfl) ⟨3291174, by rfl⟩ : syracuseStep 35105861 = 6582349) B6582349
theorem B2886745 : Blo 1709055 2886745 := bstep (se 2 (by rfl) ⟨1082529, by rfl⟩ : syracuseStep 2886745 = 2165059) B2165059
theorem B4328599 : Blo 1709055 4328599 := bstep (se 1 (by rfl) ⟨3246449, by rfl⟩ : syracuseStep 4328599 = 6492899) B6492899
theorem B12332249 : Blo 1709055 12332249 := bstep (se 2 (by rfl) ⟨4624593, by rfl⟩ : syracuseStep 12332249 = 9249187) B9249187
theorem B3247361 : Blo 1709055 3247361 := bstep (se 2 (by rfl) ⟨1217760, by rfl⟩ : syracuseStep 3247361 = 2435521) B2435521
theorem B5770547 : Blo 1709055 5770547 := bstep (se 1 (by rfl) ⟨4327910, by rfl⟩ : syracuseStep 5770547 = 8655821) B8655821
theorem B20802881 : Blo 1709055 20802881 := bstep (se 2 (by rfl) ⟨7801080, by rfl⟩ : syracuseStep 20802881 = 15602161) B15602161
theorem B3845465 : Blo 1709055 3845465 := bstep (se 2 (by rfl) ⟨1442049, by rfl⟩ : syracuseStep 3845465 = 2884099) B2884099
theorem B3845555 : Blo 1709055 3845555 := bstep (se 1 (by rfl) ⟨2884166, by rfl⟩ : syracuseStep 3845555 = 5768333) B5768333
theorem B17558963 : Blo 1709055 17558963 := bstep (se 1 (by rfl) ⟨13169222, by rfl⟩ : syracuseStep 17558963 = 26338445) B26338445
theorem B3845591 : Blo 1709055 3845591 := bstep (se 1 (by rfl) ⟨2884193, by rfl⟩ : syracuseStep 3845591 = 5768387) B5768387
theorem B6491609 : Blo 1709055 6491609 := bstep (se 2 (by rfl) ⟨2434353, by rfl⟩ : syracuseStep 6491609 = 4868707) B4868707
theorem B2739673 : Blo 1709055 2739673 := bstep (se 2 (by rfl) ⟨1027377, by rfl⟩ : syracuseStep 2739673 = 2054755) B2054755
theorem B3247627 : Blo 1709055 3247627 := bstep (se 1 (by rfl) ⟨2435720, by rfl⟩ : syracuseStep 3247627 = 4871441) B4871441
theorem B5770817 : Blo 1709055 5770817 := bstep (se 2 (by rfl) ⟨2164056, by rfl⟩ : syracuseStep 5770817 = 4328113) B4328113
theorem B4329035 : Blo 1709055 4329035 := bstep (se 1 (by rfl) ⟨3246776, by rfl⟩ : syracuseStep 4329035 = 6493553) B6493553
theorem B3845771 : Blo 1709055 3845771 := bstep (se 1 (by rfl) ⟨2884328, by rfl⟩ : syracuseStep 3845771 = 5768657) B5768657
theorem B2887319 : Blo 1709055 2887319 := bstep (se 1 (by rfl) ⟨2165489, by rfl⟩ : syracuseStep 2887319 = 4330979) B4330979
theorem B4869811 : Blo 1709055 4869811 := bstep (se 1 (by rfl) ⟨3652358, by rfl⟩ : syracuseStep 4869811 = 7304717) B7304717
theorem B3845825 : Blo 1709055 3845825 := bstep (se 2 (by rfl) ⟨1442184, by rfl⟩ : syracuseStep 3845825 = 2884369) B2884369
theorem B6491927 : Blo 1709055 6491927 := bstep (se 1 (by rfl) ⟨4868945, by rfl⟩ : syracuseStep 6491927 = 9737891) B9737891
theorem B4108097 : Blo 1709055 4108097 := bstep (se 2 (by rfl) ⟨1540536, by rfl⟩ : syracuseStep 4108097 = 3081073) B3081073
theorem B4870039 : Blo 1709055 4870039 := bstep (se 1 (by rfl) ⟨3652529, by rfl⟩ : syracuseStep 4870039 = 7305059) B7305059
theorem B3846041 : Blo 1709055 3846041 := bstep (se 2 (by rfl) ⟨1442265, by rfl⟩ : syracuseStep 3846041 = 2884531) B2884531
theorem B36974515 : Blo 1709055 36974515 := bstep (se 1 (by rfl) ⟨27730886, by rfl⟩ : syracuseStep 36974515 = 55461773) B55461773
theorem B4329409 : Blo 1709055 4329409 := bstep (se 2 (by rfl) ⟨1623528, by rfl⟩ : syracuseStep 4329409 = 3247057) B3247057
theorem B3248075 : Blo 1709055 3248075 := bstep (se 1 (by rfl) ⟨2436056, by rfl⟩ : syracuseStep 3248075 = 4872113) B4872113
theorem B3846131 : Blo 1709055 3846131 := bstep (se 1 (by rfl) ⟨2884598, by rfl⟩ : syracuseStep 3846131 = 5769197) B5769197
theorem B3846167 : Blo 1709055 3846167 := bstep (se 1 (by rfl) ⟨2884625, by rfl⟩ : syracuseStep 3846167 = 5769251) B5769251
theorem B7303213 : Blo 1709055 7303213 := bstep (se 3 (by rfl) ⟨1369352, by rfl⟩ : syracuseStep 7303213 = 2738705) B2738705
theorem B5771357 : Blo 1709055 5771357 := bstep (se 3 (by rfl) ⟨1082129, by rfl⟩ : syracuseStep 5771357 = 2164259) B2164259
theorem B3248257 : Blo 1709055 3248257 := bstep (se 2 (by rfl) ⟨1218096, by rfl⟩ : syracuseStep 3248257 = 2436193) B2436193
theorem B4165825 : Blo 1709055 4165825 := bstep (se 2 (by rfl) ⟨1562184, by rfl⟩ : syracuseStep 4165825 = 3124369) B3124369
theorem B3846347 : Blo 1709055 3846347 := bstep (se 1 (by rfl) ⟨2884760, by rfl⟩ : syracuseStep 3846347 = 5769521) B5769521
theorem B7303385 : Blo 1709055 7303385 := bstep (se 2 (by rfl) ⟨2738769, by rfl⟩ : syracuseStep 7303385 = 5477539) B5477539
theorem B3846401 : Blo 1709055 3846401 := bstep (se 2 (by rfl) ⟨1442400, by rfl⟩ : syracuseStep 3846401 = 2884801) B2884801
theorem B12980573 : Blo 1709055 12980573 := bstep (se 3 (by rfl) ⟨2433857, by rfl⟩ : syracuseStep 12980573 = 4867715) B4867715
theorem B6492595 : Blo 1709055 6492595 := bstep (se 1 (by rfl) ⟨4869446, by rfl⟩ : syracuseStep 6492595 = 9738893) B9738893
theorem B11858393 : Blo 1709055 11858393 := bstep (se 2 (by rfl) ⟨4446897, by rfl⟩ : syracuseStep 11858393 = 8893795) B8893795
theorem B3846617 : Blo 1709055 3846617 := bstep (se 2 (by rfl) ⟨1442481, by rfl⟩ : syracuseStep 3846617 = 2884963) B2884963
theorem B4878809 : Blo 1709055 4878809 := bstep (se 2 (by rfl) ⟨1829553, by rfl⟩ : syracuseStep 4878809 = 3659107) B3659107
theorem B4330007 : Blo 1709055 4330007 := bstep (se 1 (by rfl) ⟨3247505, by rfl⟩ : syracuseStep 4330007 = 6495011) B6495011
theorem B3846707 : Blo 1709055 3846707 := bstep (se 1 (by rfl) ⟨2885030, by rfl⟩ : syracuseStep 3846707 = 5770061) B5770061
theorem B3846743 : Blo 1709055 3846743 := bstep (se 1 (by rfl) ⟨2885057, by rfl⟩ : syracuseStep 3846743 = 5770115) B5770115
theorem B10957463 : Blo 1709055 10957463 := bstep (se 1 (by rfl) ⟨8218097, by rfl⟩ : syracuseStep 10957463 = 16436195) B16436195
theorem B1733323 : Blo 1709055 1733323 := bstep (se 1 (by rfl) ⟨1299992, by rfl⟩ : syracuseStep 1733323 = 2599985) B2599985
theorem B3846923 : Blo 1709055 3846923 := bstep (se 1 (by rfl) ⟨2885192, by rfl⟩ : syracuseStep 3846923 = 5770385) B5770385
theorem B3846977 : Blo 1709055 3846977 := bstep (se 2 (by rfl) ⟨1442616, by rfl⟩ : syracuseStep 3846977 = 2885233) B2885233
theorem B5550923 : Blo 1709055 5550923 := bstep (se 1 (by rfl) ⟨4163192, by rfl⟩ : syracuseStep 5550923 = 8326385) B8326385
theorem B1709067 : Blo 1709055 1709067 := bstep (se 1 (by rfl) ⟨1281800, by rfl⟩ : syracuseStep 1709067 = 2563601) B2563601
theorem B1709079 : Blo 1709055 1709079 := bstep (se 1 (by rfl) ⟨1281809, by rfl⟩ : syracuseStep 1709079 = 2563619) B2563619
theorem B3847193 : Blo 1709055 3847193 := bstep (se 2 (by rfl) ⟨1442697, by rfl⟩ : syracuseStep 3847193 = 2885395) B2885395
theorem B1709099 : Blo 1709055 1709099 := bstep (se 1 (by rfl) ⟨1281824, by rfl⟩ : syracuseStep 1709099 = 2563649) B2563649
theorem B1709111 : Blo 1709055 1709111 := bstep (se 1 (by rfl) ⟨1281833, by rfl⟩ : syracuseStep 1709111 = 2563667) B2563667
theorem B1709131 : Blo 1709055 1709131 := bstep (se 1 (by rfl) ⟨1281848, by rfl⟩ : syracuseStep 1709131 = 2563697) B2563697
theorem B13866059 : Blo 1709055 13866059 := bstep (se 1 (by rfl) ⟨10399544, by rfl⟩ : syracuseStep 13866059 = 20799089) B20799089
theorem B9245771 : Blo 1709055 9245771 := bstep (se 1 (by rfl) ⟨6934328, by rfl⟩ : syracuseStep 9245771 = 13868657) B13868657
theorem B46822475 : Blo 1709055 46822475 := bstep (se 1 (by rfl) ⟨35116856, by rfl⟩ : syracuseStep 46822475 = 70233713) B70233713
theorem B1709143 : Blo 1709055 1709143 := bstep (se 1 (by rfl) ⟨1281857, by rfl⟩ : syracuseStep 1709143 = 2563715) B2563715
theorem B1709163 : Blo 1709055 1709163 := bstep (se 1 (by rfl) ⟨1281872, by rfl⟩ : syracuseStep 1709163 = 2563745) B2563745
theorem B3847283 : Blo 1709055 3847283 := bstep (se 1 (by rfl) ⟨2885462, by rfl⟩ : syracuseStep 3847283 = 5770925) B5770925
theorem B1709175 : Blo 1709055 1709175 := bstep (se 1 (by rfl) ⟨1281881, by rfl⟩ : syracuseStep 1709175 = 2563763) B2563763
theorem B1709195 : Blo 1709055 1709195 := bstep (se 1 (by rfl) ⟨1281896, by rfl⟩ : syracuseStep 1709195 = 2563793) B2563793
theorem B6165649 : Blo 1709055 6165649 := bstep (se 2 (by rfl) ⟨2312118, by rfl⟩ : syracuseStep 6165649 = 4624237) B4624237
theorem B1709207 : Blo 1709055 1709207 := bstep (se 1 (by rfl) ⟨1281905, by rfl⟩ : syracuseStep 1709207 = 2563811) B2563811
theorem B3847319 : Blo 1709055 3847319 := bstep (se 1 (by rfl) ⟨2885489, by rfl⟩ : syracuseStep 3847319 = 5770979) B5770979
theorem B1709227 : Blo 1709055 1709227 := bstep (se 1 (by rfl) ⟨1281920, by rfl⟩ : syracuseStep 1709227 = 2563841) B2563841
theorem B1709239 : Blo 1709055 1709239 := bstep (se 1 (by rfl) ⟨1281929, by rfl⟩ : syracuseStep 1709239 = 2563859) B2563859
theorem B3650753 : Blo 1709055 3650753 := bstep (se 2 (by rfl) ⟨1369032, by rfl⟩ : syracuseStep 3650753 = 2738065) B2738065
theorem B1709259 : Blo 1709055 1709259 := bstep (se 1 (by rfl) ⟨1281944, by rfl⟩ : syracuseStep 1709259 = 2563889) B2563889
theorem B5772491 : Blo 1709055 5772491 := bstep (se 1 (by rfl) ⟨4329368, by rfl⟩ : syracuseStep 5772491 = 8658737) B8658737
theorem B2192599 : Blo 1709055 2192599 := bstep (se 1 (by rfl) ⟨1644449, by rfl⟩ : syracuseStep 2192599 = 3288899) B3288899
theorem B1709271 : Blo 1709055 1709271 := bstep (se 1 (by rfl) ⟨1281953, by rfl⟩ : syracuseStep 1709271 = 2563907) B2563907
theorem B15815897 : Blo 1709055 15815897 := bstep (se 2 (by rfl) ⟨5930961, by rfl⟩ : syracuseStep 15815897 = 11861923) B11861923
theorem B1709291 : Blo 1709055 1709291 := bstep (se 1 (by rfl) ⟨1281968, by rfl⟩ : syracuseStep 1709291 = 2563937) B2563937
theorem B1709303 : Blo 1709055 1709303 := bstep (se 1 (by rfl) ⟨1281977, by rfl⟩ : syracuseStep 1709303 = 2563955) B2563955
theorem B1709323 : Blo 1709055 1709323 := bstep (se 1 (by rfl) ⟨1281992, by rfl⟩ : syracuseStep 1709323 = 2563985) B2563985
theorem B8656145 : Blo 1709055 8656145 := bstep (se 2 (by rfl) ⟨3246054, by rfl⟩ : syracuseStep 8656145 = 6492109) B6492109
theorem B1709335 : Blo 1709055 1709335 := bstep (se 1 (by rfl) ⟨1282001, by rfl⟩ : syracuseStep 1709335 = 2564003) B2564003
theorem B1709355 : Blo 1709055 1709355 := bstep (se 1 (by rfl) ⟨1282016, by rfl⟩ : syracuseStep 1709355 = 2564033) B2564033
theorem B1709367 : Blo 1709055 1709367 := bstep (se 1 (by rfl) ⟨1282025, by rfl⟩ : syracuseStep 1709367 = 2564051) B2564051
theorem B4330817 : Blo 1709055 4330817 := bstep (se 2 (by rfl) ⟨1624056, by rfl⟩ : syracuseStep 4330817 = 3248113) B3248113
theorem B1709387 : Blo 1709055 1709387 := bstep (se 1 (by rfl) ⟨1282040, by rfl⟩ : syracuseStep 1709387 = 2564081) B2564081
theorem B3847499 : Blo 1709055 3847499 := bstep (se 1 (by rfl) ⟨2885624, by rfl⟩ : syracuseStep 3847499 = 5771249) B5771249
theorem B1709399 : Blo 1709055 1709399 := bstep (se 1 (by rfl) ⟨1282049, by rfl⟩ : syracuseStep 1709399 = 2564099) B2564099
theorem B1709419 : Blo 1709055 1709419 := bstep (se 1 (by rfl) ⟨1282064, by rfl⟩ : syracuseStep 1709419 = 2564129) B2564129
theorem B1709431 : Blo 1709055 1709431 := bstep (se 1 (by rfl) ⟨1282073, by rfl⟩ : syracuseStep 1709431 = 2564147) B2564147
theorem B3847553 : Blo 1709055 3847553 := bstep (se 2 (by rfl) ⟨1442832, by rfl⟩ : syracuseStep 3847553 = 2885665) B2885665
theorem B1709451 : Blo 1709055 1709451 := bstep (se 1 (by rfl) ⟨1282088, by rfl⟩ : syracuseStep 1709451 = 2564177) B2564177
theorem B1709463 : Blo 1709055 1709463 := bstep (se 1 (by rfl) ⟨1282097, by rfl⟩ : syracuseStep 1709463 = 2564195) B2564195
theorem B1709483 : Blo 1709055 1709483 := bstep (se 1 (by rfl) ⟨1282112, by rfl⟩ : syracuseStep 1709483 = 2564225) B2564225
theorem B8656307 : Blo 1709055 8656307 := bstep (se 1 (by rfl) ⟨6492230, by rfl⟩ : syracuseStep 8656307 = 12984461) B12984461
theorem B1709495 : Blo 1709055 1709495 := bstep (se 1 (by rfl) ⟨1282121, by rfl⟩ : syracuseStep 1709495 = 2564243) B2564243
theorem B1709515 : Blo 1709055 1709515 := bstep (se 1 (by rfl) ⟨1282136, by rfl⟩ : syracuseStep 1709515 = 2564273) B2564273
theorem B1709527 : Blo 1709055 1709527 := bstep (se 1 (by rfl) ⟨1282145, by rfl⟩ : syracuseStep 1709527 = 2564291) B2564291
theorem B5772761 : Blo 1709055 5772761 := bstep (se 2 (by rfl) ⟨2164785, by rfl⟩ : syracuseStep 5772761 = 4329571) B4329571
theorem B19486169 : Blo 1709055 19486169 := bstep (se 2 (by rfl) ⟨7307313, by rfl⟩ : syracuseStep 19486169 = 14614627) B14614627
theorem B1709547 : Blo 1709055 1709547 := bstep (se 1 (by rfl) ⟨1282160, by rfl⟩ : syracuseStep 1709547 = 2564321) B2564321
theorem B1709559 : Blo 1709055 1709559 := bstep (se 1 (by rfl) ⟨1282169, by rfl⟩ : syracuseStep 1709559 = 2564339) B2564339
theorem B1709579 : Blo 1709055 1709579 := bstep (se 1 (by rfl) ⟨1282184, by rfl⟩ : syracuseStep 1709579 = 2564369) B2564369
theorem B3651095 : Blo 1709055 3651095 := bstep (se 1 (by rfl) ⟨2738321, by rfl⟩ : syracuseStep 3651095 = 5476643) B5476643
theorem B1709591 : Blo 1709055 1709591 := bstep (se 1 (by rfl) ⟨1282193, by rfl⟩ : syracuseStep 1709591 = 2564387) B2564387
theorem B1709611 : Blo 1709055 1709611 := bstep (se 1 (by rfl) ⟨1282208, by rfl⟩ : syracuseStep 1709611 = 2564417) B2564417
theorem B1709623 : Blo 1709055 1709623 := bstep (se 1 (by rfl) ⟨1282217, by rfl⟩ : syracuseStep 1709623 = 2564435) B2564435
theorem B1709643 : Blo 1709055 1709643 := bstep (se 1 (by rfl) ⟨1282232, by rfl⟩ : syracuseStep 1709643 = 2564465) B2564465
theorem B1709655 : Blo 1709055 1709655 := bstep (se 1 (by rfl) ⟨1282241, by rfl⟩ : syracuseStep 1709655 = 2564483) B2564483
theorem B3847769 : Blo 1709055 3847769 := bstep (se 2 (by rfl) ⟨1442913, by rfl⟩ : syracuseStep 3847769 = 2885827) B2885827
theorem B9631325 : Blo 1709055 9631325 := bstep (se 3 (by rfl) ⟨1805873, by rfl⟩ : syracuseStep 9631325 = 3611747) B3611747
theorem B1709675 : Blo 1709055 1709675 := bstep (se 1 (by rfl) ⟨1282256, by rfl⟩ : syracuseStep 1709675 = 2564513) B2564513
theorem B1709687 : Blo 1709055 1709687 := bstep (se 1 (by rfl) ⟨1282265, by rfl⟩ : syracuseStep 1709687 = 2564531) B2564531
theorem B1709707 : Blo 1709055 1709707 := bstep (se 1 (by rfl) ⟨1282280, by rfl⟩ : syracuseStep 1709707 = 2564561) B2564561
theorem B6493841 : Blo 1709055 6493841 := bstep (se 2 (by rfl) ⟨2435190, by rfl⟩ : syracuseStep 6493841 = 4870381) B4870381
theorem B1709719 : Blo 1709055 1709719 := bstep (se 1 (by rfl) ⟨1282289, by rfl⟩ : syracuseStep 1709719 = 2564579) B2564579
theorem B1709739 : Blo 1709055 1709739 := bstep (se 1 (by rfl) ⟨1282304, by rfl⟩ : syracuseStep 1709739 = 2564609) B2564609
theorem B3847859 : Blo 1709055 3847859 := bstep (se 1 (by rfl) ⟨2885894, by rfl⟩ : syracuseStep 3847859 = 5771789) B5771789
theorem B1709751 : Blo 1709055 1709751 := bstep (se 1 (by rfl) ⟨1282313, by rfl⟩ : syracuseStep 1709751 = 2564627) B2564627
theorem B3651265 : Blo 1709055 3651265 := bstep (se 2 (by rfl) ⟨1369224, by rfl⟩ : syracuseStep 3651265 = 2738449) B2738449
theorem B1709771 : Blo 1709055 1709771 := bstep (se 1 (by rfl) ⟨1282328, by rfl⟩ : syracuseStep 1709771 = 2564657) B2564657
theorem B1709783 : Blo 1709055 1709783 := bstep (se 1 (by rfl) ⟨1282337, by rfl⟩ : syracuseStep 1709783 = 2564675) B2564675
theorem B3847895 : Blo 1709055 3847895 := bstep (se 1 (by rfl) ⟨2885921, by rfl⟩ : syracuseStep 3847895 = 5771843) B5771843
theorem B4871897 : Blo 1709055 4871897 := bstep (se 2 (by rfl) ⟨1826961, by rfl⟩ : syracuseStep 4871897 = 3653923) B3653923
theorem B1709803 : Blo 1709055 1709803 := bstep (se 1 (by rfl) ⟨1282352, by rfl⟩ : syracuseStep 1709803 = 2564705) B2564705
theorem B1709815 : Blo 1709055 1709815 := bstep (se 1 (by rfl) ⟨1282361, by rfl⟩ : syracuseStep 1709815 = 2564723) B2564723
theorem B1922827 : Blo 1709055 1922827 := bstep (se 1 (by rfl) ⟨1442120, by rfl⟩ : syracuseStep 1922827 = 2884241) B2884241
theorem B1709835 : Blo 1709055 1709835 := bstep (se 1 (by rfl) ⟨1282376, by rfl⟩ : syracuseStep 1709835 = 2564753) B2564753
theorem B1709847 : Blo 1709055 1709847 := bstep (se 1 (by rfl) ⟨1282385, by rfl⟩ : syracuseStep 1709847 = 2564771) B2564771
theorem B1709867 : Blo 1709055 1709867 := bstep (se 1 (by rfl) ⟨1282400, by rfl⟩ : syracuseStep 1709867 = 2564801) B2564801
theorem B1709879 : Blo 1709055 1709879 := bstep (se 1 (by rfl) ⟨1282409, by rfl⟩ : syracuseStep 1709879 = 2564819) B2564819
theorem B7305025 : Blo 1709055 7305025 := bstep (se 2 (by rfl) ⟨2739384, by rfl⟩ : syracuseStep 7305025 = 5478769) B5478769
theorem B1709899 : Blo 1709055 1709899 := bstep (se 1 (by rfl) ⟨1282424, by rfl⟩ : syracuseStep 1709899 = 2564849) B2564849
theorem B1709911 : Blo 1709055 1709911 := bstep (se 1 (by rfl) ⟨1282433, by rfl⟩ : syracuseStep 1709911 = 2564867) B2564867
theorem B1709931 : Blo 1709055 1709931 := bstep (se 1 (by rfl) ⟨1282448, by rfl⟩ : syracuseStep 1709931 = 2564897) B2564897
theorem B1922935 : Blo 1709055 1922935 := bstep (se 1 (by rfl) ⟨1442201, by rfl⟩ : syracuseStep 1922935 = 2884403) B2884403
theorem B1709943 : Blo 1709055 1709943 := bstep (se 1 (by rfl) ⟨1282457, by rfl⟩ : syracuseStep 1709943 = 2564915) B2564915
theorem B1709963 : Blo 1709055 1709963 := bstep (se 1 (by rfl) ⟨1282472, by rfl⟩ : syracuseStep 1709963 = 2564945) B2564945
theorem B3848075 : Blo 1709055 3848075 := bstep (se 1 (by rfl) ⟨2886056, by rfl⟩ : syracuseStep 3848075 = 5772113) B5772113
theorem B1709975 : Blo 1709055 1709975 := bstep (se 1 (by rfl) ⟨1282481, by rfl⟩ : syracuseStep 1709975 = 2564963) B2564963
theorem B1709995 : Blo 1709055 1709995 := bstep (se 1 (by rfl) ⟨1282496, by rfl⟩ : syracuseStep 1709995 = 2564993) B2564993
theorem B1710007 : Blo 1709055 1710007 := bstep (se 1 (by rfl) ⟨1282505, by rfl⟩ : syracuseStep 1710007 = 2565011) B2565011
theorem B3848129 : Blo 1709055 3848129 := bstep (se 2 (by rfl) ⟨1443048, by rfl⟩ : syracuseStep 3848129 = 2886097) B2886097
theorem B1710027 : Blo 1709055 1710027 := bstep (se 1 (by rfl) ⟨1282520, by rfl⟩ : syracuseStep 1710027 = 2565041) B2565041
theorem B1710039 : Blo 1709055 1710039 := bstep (se 1 (by rfl) ⟨1282529, by rfl⟩ : syracuseStep 1710039 = 2565059) B2565059
theorem B1710059 : Blo 1709055 1710059 := bstep (se 1 (by rfl) ⟨1282544, by rfl⟩ : syracuseStep 1710059 = 2565089) B2565089
theorem B1710071 : Blo 1709055 1710071 := bstep (se 1 (by rfl) ⟨1282553, by rfl⟩ : syracuseStep 1710071 = 2565107) B2565107
theorem B1710091 : Blo 1709055 1710091 := bstep (se 1 (by rfl) ⟨1282568, by rfl⟩ : syracuseStep 1710091 = 2565137) B2565137
theorem B1710103 : Blo 1709055 1710103 := bstep (se 1 (by rfl) ⟨1282577, by rfl⟩ : syracuseStep 1710103 = 2565155) B2565155
theorem B1923115 : Blo 1709055 1923115 := bstep (se 1 (by rfl) ⟨1442336, by rfl⟩ : syracuseStep 1923115 = 2884673) B2884673
theorem B1710123 : Blo 1709055 1710123 := bstep (se 1 (by rfl) ⟨1282592, by rfl⟩ : syracuseStep 1710123 = 2565185) B2565185
theorem B1710135 : Blo 1709055 1710135 := bstep (se 1 (by rfl) ⟨1282601, by rfl⟩ : syracuseStep 1710135 = 2565203) B2565203
theorem B1710155 : Blo 1709055 1710155 := bstep (se 1 (by rfl) ⟨1282616, by rfl⟩ : syracuseStep 1710155 = 2565233) B2565233
theorem B1710167 : Blo 1709055 1710167 := bstep (se 1 (by rfl) ⟨1282625, by rfl⟩ : syracuseStep 1710167 = 2565251) B2565251
theorem B1710187 : Blo 1709055 1710187 := bstep (se 1 (by rfl) ⟨1282640, by rfl⟩ : syracuseStep 1710187 = 2565281) B2565281
theorem B1710199 : Blo 1709055 1710199 := bstep (se 1 (by rfl) ⟨1282649, by rfl⟩ : syracuseStep 1710199 = 2565299) B2565299
theorem B1710219 : Blo 1709055 1710219 := bstep (se 1 (by rfl) ⟨1282664, by rfl⟩ : syracuseStep 1710219 = 2565329) B2565329
theorem B1923223 : Blo 1709055 1923223 := bstep (se 1 (by rfl) ⟨1442417, by rfl⟩ : syracuseStep 1923223 = 2884835) B2884835
theorem B1710231 : Blo 1709055 1710231 := bstep (se 1 (by rfl) ⟨1282673, by rfl⟩ : syracuseStep 1710231 = 2565347) B2565347
theorem B3848345 : Blo 1709055 3848345 := bstep (se 2 (by rfl) ⟨1443129, by rfl⟩ : syracuseStep 3848345 = 2886259) B2886259
theorem B5773463 : Blo 1709055 5773463 := bstep (se 1 (by rfl) ⟨4330097, by rfl⟩ : syracuseStep 5773463 = 8660195) B8660195
theorem B1710251 : Blo 1709055 1710251 := bstep (se 1 (by rfl) ⟨1282688, by rfl⟩ : syracuseStep 1710251 = 2565377) B2565377
theorem B1710263 : Blo 1709055 1710263 := bstep (se 1 (by rfl) ⟨1282697, by rfl⟩ : syracuseStep 1710263 = 2565395) B2565395
theorem B1710283 : Blo 1709055 1710283 := bstep (se 1 (by rfl) ⟨1282712, by rfl⟩ : syracuseStep 1710283 = 2565425) B2565425
theorem B24647885 : Blo 1709055 24647885 := bstep (se 3 (by rfl) ⟨4621478, by rfl⟩ : syracuseStep 24647885 = 9242957) B9242957
theorem B1710295 : Blo 1709055 1710295 := bstep (se 1 (by rfl) ⟨1282721, by rfl⟩ : syracuseStep 1710295 = 2565443) B2565443
theorem B1710315 : Blo 1709055 1710315 := bstep (se 1 (by rfl) ⟨1282736, by rfl⟩ : syracuseStep 1710315 = 2565473) B2565473
theorem B1710327 : Blo 1709055 1710327 := bstep (se 1 (by rfl) ⟨1282745, by rfl⟩ : syracuseStep 1710327 = 2565491) B2565491
theorem B3848435 : Blo 1709055 3848435 := bstep (se 1 (by rfl) ⟨2886326, by rfl⟩ : syracuseStep 3848435 = 5772653) B5772653
theorem B1710347 : Blo 1709055 1710347 := bstep (se 1 (by rfl) ⟨1282760, by rfl⟩ : syracuseStep 1710347 = 2565521) B2565521
theorem B1710359 : Blo 1709055 1710359 := bstep (se 1 (by rfl) ⟨1282769, by rfl⟩ : syracuseStep 1710359 = 2565539) B2565539
theorem B3848471 : Blo 1709055 3848471 := bstep (se 1 (by rfl) ⟨2886353, by rfl⟩ : syracuseStep 3848471 = 5772707) B5772707
theorem B1710379 : Blo 1709055 1710379 := bstep (se 1 (by rfl) ⟨1282784, by rfl⟩ : syracuseStep 1710379 = 2565569) B2565569
theorem B1710391 : Blo 1709055 1710391 := bstep (se 1 (by rfl) ⟨1282793, by rfl⟩ : syracuseStep 1710391 = 2565587) B2565587
theorem B10950977 : Blo 1709055 10950977 := bstep (se 2 (by rfl) ⟨4106616, by rfl⟩ : syracuseStep 10950977 = 8213233) B8213233
theorem B1923403 : Blo 1709055 1923403 := bstep (se 1 (by rfl) ⟨1442552, by rfl⟩ : syracuseStep 1923403 = 2885105) B2885105
theorem B1710411 : Blo 1709055 1710411 := bstep (se 1 (by rfl) ⟨1282808, by rfl⟩ : syracuseStep 1710411 = 2565617) B2565617
theorem B6494539 : Blo 1709055 6494539 := bstep (se 1 (by rfl) ⟨4870904, by rfl⟩ : syracuseStep 6494539 = 9741809) B9741809
theorem B1710423 : Blo 1709055 1710423 := bstep (se 1 (by rfl) ⟨1282817, by rfl⟩ : syracuseStep 1710423 = 2565635) B2565635
theorem B13343069 : Blo 1709055 13343069 := bstep (se 3 (by rfl) ⟨2501825, by rfl⟩ : syracuseStep 13343069 = 5003651) B5003651
theorem B1710443 : Blo 1709055 1710443 := bstep (se 1 (by rfl) ⟨1282832, by rfl⟩ : syracuseStep 1710443 = 2565665) B2565665
theorem B1710455 : Blo 1709055 1710455 := bstep (se 1 (by rfl) ⟨1282841, by rfl⟩ : syracuseStep 1710455 = 2565683) B2565683
theorem B1710475 : Blo 1709055 1710475 := bstep (se 1 (by rfl) ⟨1282856, by rfl⟩ : syracuseStep 1710475 = 2565713) B2565713
theorem B1710487 : Blo 1709055 1710487 := bstep (se 1 (by rfl) ⟨1282865, by rfl⟩ : syracuseStep 1710487 = 2565731) B2565731
theorem B1710507 : Blo 1709055 1710507 := bstep (se 1 (by rfl) ⟨1282880, by rfl⟩ : syracuseStep 1710507 = 2565761) B2565761
theorem B1923511 : Blo 1709055 1923511 := bstep (se 1 (by rfl) ⟨1442633, by rfl⟩ : syracuseStep 1923511 = 2885267) B2885267
theorem B1710519 : Blo 1709055 1710519 := bstep (se 1 (by rfl) ⟨1282889, by rfl⟩ : syracuseStep 1710519 = 2565779) B2565779
theorem B3848651 : Blo 1709055 3848651 := bstep (se 1 (by rfl) ⟨2886488, by rfl⟩ : syracuseStep 3848651 = 5772977) B5772977
theorem B1710539 : Blo 1709055 1710539 := bstep (se 1 (by rfl) ⟨1282904, by rfl⟩ : syracuseStep 1710539 = 2565809) B2565809
theorem B1710551 : Blo 1709055 1710551 := bstep (se 1 (by rfl) ⟨1282913, by rfl⟩ : syracuseStep 1710551 = 2565827) B2565827
theorem B10951129 : Blo 1709055 10951129 := bstep (se 2 (by rfl) ⟨4106673, by rfl⟩ : syracuseStep 10951129 = 8213347) B8213347
theorem B9624025 : Blo 1709055 9624025 := bstep (se 2 (by rfl) ⟨3609009, by rfl⟩ : syracuseStep 9624025 = 7218019) B7218019
theorem B1710571 : Blo 1709055 1710571 := bstep (se 1 (by rfl) ⟨1282928, by rfl⟩ : syracuseStep 1710571 = 2565857) B2565857
theorem B1710583 : Blo 1709055 1710583 := bstep (se 1 (by rfl) ⟨1282937, by rfl⟩ : syracuseStep 1710583 = 2565875) B2565875
theorem B3848705 : Blo 1709055 3848705 := bstep (se 2 (by rfl) ⟨1443264, by rfl⟩ : syracuseStep 3848705 = 2886529) B2886529
theorem B1825291 : Blo 1709055 1825291 := bstep (se 1 (by rfl) ⟨1368968, by rfl⟩ : syracuseStep 1825291 = 2737937) B2737937
theorem B1710603 : Blo 1709055 1710603 := bstep (se 1 (by rfl) ⟨1282952, by rfl⟩ : syracuseStep 1710603 = 2565905) B2565905
theorem B1710615 : Blo 1709055 1710615 := bstep (se 1 (by rfl) ⟨1282961, by rfl⟩ : syracuseStep 1710615 = 2565923) B2565923
theorem B1710635 : Blo 1709055 1710635 := bstep (se 1 (by rfl) ⟨1282976, by rfl⟩ : syracuseStep 1710635 = 2565953) B2565953
theorem B1710647 : Blo 1709055 1710647 := bstep (se 1 (by rfl) ⟨1282985, by rfl⟩ : syracuseStep 1710647 = 2565971) B2565971
theorem B1710667 : Blo 1709055 1710667 := bstep (se 1 (by rfl) ⟨1283000, by rfl⟩ : syracuseStep 1710667 = 2566001) B2566001
theorem B1710679 : Blo 1709055 1710679 := bstep (se 1 (by rfl) ⟨1283009, by rfl⟩ : syracuseStep 1710679 = 2566019) B2566019
theorem B6494813 : Blo 1709055 6494813 := bstep (se 3 (by rfl) ⟨1217777, by rfl⟩ : syracuseStep 6494813 = 2435555) B2435555
theorem B1923691 : Blo 1709055 1923691 := bstep (se 1 (by rfl) ⟨1442768, by rfl⟩ : syracuseStep 1923691 = 2885537) B2885537
theorem B1710699 : Blo 1709055 1710699 := bstep (se 1 (by rfl) ⟨1283024, by rfl⟩ : syracuseStep 1710699 = 2566049) B2566049
theorem B1710711 : Blo 1709055 1710711 := bstep (se 1 (by rfl) ⟨1283033, by rfl⟩ : syracuseStep 1710711 = 2566067) B2566067
theorem B1710731 : Blo 1709055 1710731 := bstep (se 1 (by rfl) ⟨1283048, by rfl⟩ : syracuseStep 1710731 = 2566097) B2566097
theorem B1710743 : Blo 1709055 1710743 := bstep (se 1 (by rfl) ⟨1283057, by rfl⟩ : syracuseStep 1710743 = 2566115) B2566115
theorem B1710763 : Blo 1709055 1710763 := bstep (se 1 (by rfl) ⟨1283072, by rfl⟩ : syracuseStep 1710763 = 2566145) B2566145
theorem B5774003 : Blo 1709055 5774003 := bstep (se 1 (by rfl) ⟨4330502, by rfl⟩ : syracuseStep 5774003 = 8661005) B8661005
theorem B1710775 : Blo 1709055 1710775 := bstep (se 1 (by rfl) ⟨1283081, by rfl⟩ : syracuseStep 1710775 = 2566163) B2566163
theorem B1710795 : Blo 1709055 1710795 := bstep (se 1 (by rfl) ⟨1283096, by rfl⟩ : syracuseStep 1710795 = 2566193) B2566193
theorem B1923799 : Blo 1709055 1923799 := bstep (se 1 (by rfl) ⟨1442849, by rfl⟩ : syracuseStep 1923799 = 2885699) B2885699
theorem B1710807 : Blo 1709055 1710807 := bstep (se 1 (by rfl) ⟨1283105, by rfl⟩ : syracuseStep 1710807 = 2566211) B2566211
theorem B3848921 : Blo 1709055 3848921 := bstep (se 2 (by rfl) ⟨1443345, by rfl⟩ : syracuseStep 3848921 = 2886691) B2886691
theorem B1710827 : Blo 1709055 1710827 := bstep (se 1 (by rfl) ⟨1283120, by rfl⟩ : syracuseStep 1710827 = 2566241) B2566241
theorem B1710839 : Blo 1709055 1710839 := bstep (se 1 (by rfl) ⟨1283129, by rfl⟩ : syracuseStep 1710839 = 2566259) B2566259
theorem B1710859 : Blo 1709055 1710859 := bstep (se 1 (by rfl) ⟨1283144, by rfl⟩ : syracuseStep 1710859 = 2566289) B2566289
theorem B1710871 : Blo 1709055 1710871 := bstep (se 1 (by rfl) ⟨1283153, by rfl⟩ : syracuseStep 1710871 = 2566307) B2566307
theorem B1710891 : Blo 1709055 1710891 := bstep (se 1 (by rfl) ⟨1283168, by rfl⟩ : syracuseStep 1710891 = 2566337) B2566337
theorem B3849011 : Blo 1709055 3849011 := bstep (se 1 (by rfl) ⟨2886758, by rfl⟩ : syracuseStep 3849011 = 5773517) B5773517
theorem B1710903 : Blo 1709055 1710903 := bstep (se 1 (by rfl) ⟨1283177, by rfl⟩ : syracuseStep 1710903 = 2566355) B2566355
theorem B3652427 : Blo 1709055 3652427 := bstep (se 1 (by rfl) ⟨2739320, by rfl⟩ : syracuseStep 3652427 = 5478641) B5478641
theorem B1710923 : Blo 1709055 1710923 := bstep (se 1 (by rfl) ⟨1283192, by rfl⟩ : syracuseStep 1710923 = 2566385) B2566385
theorem B3849047 : Blo 1709055 3849047 := bstep (se 1 (by rfl) ⟨2886785, by rfl⟩ : syracuseStep 3849047 = 5773571) B5773571
theorem B1710935 : Blo 1709055 1710935 := bstep (se 1 (by rfl) ⟨1283201, by rfl⟩ : syracuseStep 1710935 = 2566403) B2566403
theorem B1710955 : Blo 1709055 1710955 := bstep (se 1 (by rfl) ⟨1283216, by rfl⟩ : syracuseStep 1710955 = 2566433) B2566433
theorem B1710967 : Blo 1709055 1710967 := bstep (se 1 (by rfl) ⟨1283225, by rfl⟩ : syracuseStep 1710967 = 2566451) B2566451
theorem B1923979 : Blo 1709055 1923979 := bstep (se 1 (by rfl) ⟨1442984, by rfl⟩ : syracuseStep 1923979 = 2885969) B2885969
theorem B1710987 : Blo 1709055 1710987 := bstep (se 1 (by rfl) ⟨1283240, by rfl⟩ : syracuseStep 1710987 = 2566481) B2566481
theorem B1710999 : Blo 1709055 1710999 := bstep (se 1 (by rfl) ⟨1283249, by rfl⟩ : syracuseStep 1710999 = 2566499) B2566499
theorem B1711019 : Blo 1709055 1711019 := bstep (se 1 (by rfl) ⟨1283264, by rfl⟩ : syracuseStep 1711019 = 2566529) B2566529
theorem B1711031 : Blo 1709055 1711031 := bstep (se 1 (by rfl) ⟨1283273, by rfl⟩ : syracuseStep 1711031 = 2566547) B2566547
theorem B5774273 : Blo 1709055 5774273 := bstep (se 2 (by rfl) ⟨2165352, by rfl⟩ : syracuseStep 5774273 = 4330705) B4330705
theorem B1711051 : Blo 1709055 1711051 := bstep (se 1 (by rfl) ⟨1283288, by rfl⟩ : syracuseStep 1711051 = 2566577) B2566577
theorem B1924087 : Blo 1709055 1924087 := bstep (se 1 (by rfl) ⟨1443065, by rfl⟩ : syracuseStep 1924087 = 2886131) B2886131
theorem B3849227 : Blo 1709055 3849227 := bstep (se 1 (by rfl) ⟨2886920, by rfl⟩ : syracuseStep 3849227 = 5773841) B5773841
theorem B5200919 : Blo 1709055 5200919 := bstep (se 1 (by rfl) ⟨3900689, by rfl⟩ : syracuseStep 5200919 = 7801379) B7801379
theorem B3849281 : Blo 1709055 3849281 := bstep (se 2 (by rfl) ⟨1443480, by rfl⟩ : syracuseStep 3849281 = 2886961) B2886961
theorem B10959947 : Blo 1709055 10959947 := bstep (se 1 (by rfl) ⟨8219960, by rfl⟩ : syracuseStep 10959947 = 16439921) B16439921
theorem B1924267 : Blo 1709055 1924267 := bstep (se 1 (by rfl) ⟨1443200, by rfl⟩ : syracuseStep 1924267 = 2886401) B2886401
theorem B9239825 : Blo 1709055 9239825 := bstep (se 2 (by rfl) ⟨3464934, by rfl⟩ : syracuseStep 9239825 = 6929869) B6929869
theorem B1924375 : Blo 1709055 1924375 := bstep (se 1 (by rfl) ⟨1443281, by rfl⟩ : syracuseStep 1924375 = 2886563) B2886563
theorem B6495511 : Blo 1709055 6495511 := bstep (se 1 (by rfl) ⟨4871633, by rfl⟩ : syracuseStep 6495511 = 9743267) B9743267
theorem B3849497 : Blo 1709055 3849497 := bstep (se 2 (by rfl) ⟨1443561, by rfl⟩ : syracuseStep 3849497 = 2887123) B2887123
theorem B8658251 : Blo 1709055 8658251 := bstep (se 1 (by rfl) ⟨6493688, by rfl⟩ : syracuseStep 8658251 = 12987377) B12987377
theorem B3849587 : Blo 1709055 3849587 := bstep (se 1 (by rfl) ⟨2887190, by rfl⟩ : syracuseStep 3849587 = 5774381) B5774381
theorem B3849623 : Blo 1709055 3849623 := bstep (se 1 (by rfl) ⟨2887217, by rfl⟩ : syracuseStep 3849623 = 5774435) B5774435
theorem B7306699 : Blo 1709055 7306699 := bstep (se 1 (by rfl) ⟨5480024, by rfl⟩ : syracuseStep 7306699 = 10960049) B10960049
theorem B1924555 : Blo 1709055 1924555 := bstep (se 1 (by rfl) ⟨1443416, by rfl⟩ : syracuseStep 1924555 = 2886833) B2886833
theorem B5774813 : Blo 1709055 5774813 := bstep (se 3 (by rfl) ⟨1082777, by rfl⟩ : syracuseStep 5774813 = 2165555) B2165555
theorem B2563595 : Blo 1709055 2563595 := bstep (se 1 (by rfl) ⟨1922696, by rfl⟩ : syracuseStep 2563595 = 3845393) B3845393
theorem B2563607 : Blo 1709055 2563607 := bstep (se 1 (by rfl) ⟨1922705, by rfl⟩ : syracuseStep 2563607 = 3845411) B3845411
theorem B6577715 : Blo 1709055 6577715 := bstep (se 1 (by rfl) ⟨4933286, by rfl⟩ : syracuseStep 6577715 = 9866573) B9866573
theorem B3653171 : Blo 1709055 3653171 := bstep (se 1 (by rfl) ⟨2739878, by rfl⟩ : syracuseStep 3653171 = 5479757) B5479757
theorem B1924663 : Blo 1709055 1924663 := bstep (se 1 (by rfl) ⟨1443497, by rfl⟩ : syracuseStep 1924663 = 2886995) B2886995
theorem B3849803 : Blo 1709055 3849803 := bstep (se 1 (by rfl) ⟨2887352, by rfl⟩ : syracuseStep 3849803 = 5774705) B5774705
theorem B2563673 : Blo 1709055 2563673 := bstep (se 2 (by rfl) ⟨961377, by rfl⟩ : syracuseStep 2563673 = 1922755) B1922755
theorem B3849857 : Blo 1709055 3849857 := bstep (se 2 (by rfl) ⟨1443696, by rfl⟩ : syracuseStep 3849857 = 2887393) B2887393
theorem B2563787 : Blo 1709055 2563787 := bstep (se 1 (by rfl) ⟨1922840, by rfl⟩ : syracuseStep 2563787 = 3845681) B3845681
theorem B2563799 : Blo 1709055 2563799 := bstep (se 1 (by rfl) ⟨1922849, by rfl⟩ : syracuseStep 2563799 = 3845699) B3845699
theorem B7798493 : Blo 1709055 7798493 := bstep (se 3 (by rfl) ⟨1462217, by rfl⟩ : syracuseStep 7798493 = 2924435) B2924435
theorem B7306973 : Blo 1709055 7306973 := bstep (se 3 (by rfl) ⟨1370057, by rfl⟩ : syracuseStep 7306973 = 2740115) B2740115
theorem B1924843 : Blo 1709055 1924843 := bstep (se 1 (by rfl) ⟨1443632, by rfl⟩ : syracuseStep 1924843 = 2887265) B2887265
theorem B1949431 : Blo 1709055 1949431 := bstep (se 1 (by rfl) ⟨1462073, by rfl⟩ : syracuseStep 1949431 = 2924147) B2924147
theorem B2563865 : Blo 1709055 2563865 := bstep (se 2 (by rfl) ⟨961449, by rfl⟩ : syracuseStep 2563865 = 1922899) B1922899
theorem B3465089 : Blo 1709055 3465089 := bstep (se 2 (by rfl) ⟨1299408, by rfl⟩ : syracuseStep 3465089 = 2598817) B2598817
theorem B2563979 : Blo 1709055 2563979 := bstep (se 1 (by rfl) ⟨1922984, by rfl⟩ : syracuseStep 2563979 = 3845969) B3845969
theorem B2563991 : Blo 1709055 2563991 := bstep (se 1 (by rfl) ⟨1922993, by rfl⟩ : syracuseStep 2563991 = 3845987) B3845987
theorem B2564057 : Blo 1709055 2564057 := bstep (se 2 (by rfl) ⟨961521, by rfl⟩ : syracuseStep 2564057 = 1923043) B1923043
theorem B2564111 : Blo 1709055 2564111 := bstep (se 1 (by rfl) ⟨1923083, by rfl⟩ : syracuseStep 2564111 = 3846167) B3846167
theorem B2564153 : Blo 1709055 2564153 := bstep (se 2 (by rfl) ⟨961557, by rfl⟩ : syracuseStep 2564153 = 1923115) B1923115
theorem B2564231 : Blo 1709055 2564231 := bstep (se 1 (by rfl) ⟨1923173, by rfl⟩ : syracuseStep 2564231 = 3846347) B3846347
theorem B2564267 : Blo 1709055 2564267 := bstep (se 1 (by rfl) ⟨1923200, by rfl⟩ : syracuseStep 2564267 = 3846401) B3846401
theorem B2564297 : Blo 1709055 2564297 := bstep (se 2 (by rfl) ⟨961611, by rfl⟩ : syracuseStep 2564297 = 1923223) B1923223
theorem B5554433 : Blo 1709055 5554433 := bstep (se 2 (by rfl) ⟨2082912, by rfl⟩ : syracuseStep 5554433 = 4165825) B4165825
theorem B2564411 : Blo 1709055 2564411 := bstep (se 1 (by rfl) ⟨1923308, by rfl⟩ : syracuseStep 2564411 = 3846617) B3846617
theorem B3252539 : Blo 1709055 3252539 := bstep (se 1 (by rfl) ⟨2439404, by rfl⟩ : syracuseStep 3252539 = 4878809) B4878809
theorem B7905595 : Blo 1709055 7905595 := bstep (se 1 (by rfl) ⟨5929196, by rfl⟩ : syracuseStep 7905595 = 11858393) B11858393
theorem B2564471 : Blo 1709055 2564471 := bstep (se 1 (by rfl) ⟨1923353, by rfl⟩ : syracuseStep 2564471 = 3846707) B3846707
theorem B2564495 : Blo 1709055 2564495 := bstep (se 1 (by rfl) ⟨1923371, by rfl⟩ : syracuseStep 2564495 = 3846743) B3846743
theorem B2163115 : Blo 1709055 2163115 := bstep (se 1 (by rfl) ⟨1622336, by rfl⟩ : syracuseStep 2163115 = 3244673) B3244673
theorem B2564537 : Blo 1709055 2564537 := bstep (se 2 (by rfl) ⟨961701, by rfl⟩ : syracuseStep 2564537 = 1923403) B1923403
theorem B8659385 : Blo 1709055 8659385 := bstep (se 2 (by rfl) ⟨3247269, by rfl⟩ : syracuseStep 8659385 = 6494539) B6494539
theorem B5202377 : Blo 1709055 5202377 := bstep (se 2 (by rfl) ⟨1950891, by rfl⟩ : syracuseStep 5202377 = 3901783) B3901783
theorem B2564615 : Blo 1709055 2564615 := bstep (se 1 (by rfl) ⟨1923461, by rfl⟩ : syracuseStep 2564615 = 3846923) B3846923
theorem B2564651 : Blo 1709055 2564651 := bstep (se 1 (by rfl) ⟨1923488, by rfl⟩ : syracuseStep 2564651 = 3846977) B3846977
theorem B2564681 : Blo 1709055 2564681 := bstep (se 2 (by rfl) ⟨961755, by rfl⟩ : syracuseStep 2564681 = 1923511) B1923511
theorem B2163343 : Blo 1709055 2163343 := bstep (se 1 (by rfl) ⟨1622507, by rfl⟩ : syracuseStep 2163343 = 3245015) B3245015
theorem B2433721 : Blo 1709055 2433721 := bstep (se 2 (by rfl) ⟨912645, by rfl⟩ : syracuseStep 2433721 = 1825291) B1825291
theorem B2564795 : Blo 1709055 2564795 := bstep (se 1 (by rfl) ⟨1923596, by rfl⟩ : syracuseStep 2564795 = 3847193) B3847193
theorem B2564855 : Blo 1709055 2564855 := bstep (se 1 (by rfl) ⟨1923641, by rfl⟩ : syracuseStep 2564855 = 3847283) B3847283
theorem B2081543 : Blo 1709055 2081543 := bstep (se 1 (by rfl) ⟨1561157, by rfl⟩ : syracuseStep 2081543 = 3122315) B3122315
theorem B2564879 : Blo 1709055 2564879 := bstep (se 1 (by rfl) ⟨1923659, by rfl⟩ : syracuseStep 2564879 = 3847319) B3847319
theorem B2433835 : Blo 1709055 2433835 := bstep (se 1 (by rfl) ⟨1825376, by rfl⟩ : syracuseStep 2433835 = 3650753) B3650753
theorem B2564921 : Blo 1709055 2564921 := bstep (se 2 (by rfl) ⟨961845, by rfl⟩ : syracuseStep 2564921 = 1923691) B1923691
theorem B10543931 : Blo 1709055 10543931 := bstep (se 1 (by rfl) ⟨7907948, by rfl⟩ : syracuseStep 10543931 = 15815897) B15815897
theorem B2564999 : Blo 1709055 2564999 := bstep (se 1 (by rfl) ⟨1923749, by rfl⟩ : syracuseStep 2564999 = 3847499) B3847499
theorem B2565035 : Blo 1709055 2565035 := bstep (se 1 (by rfl) ⟨1923776, by rfl⟩ : syracuseStep 2565035 = 3847553) B3847553
theorem B2311097 : Blo 1709055 2311097 := bstep (se 2 (by rfl) ⟨866661, by rfl⟩ : syracuseStep 2311097 = 1733323) B1733323
theorem B2565065 : Blo 1709055 2565065 := bstep (se 2 (by rfl) ⟨961899, by rfl⟩ : syracuseStep 2565065 = 1923799) B1923799
theorem B2434063 : Blo 1709055 2434063 := bstep (se 1 (by rfl) ⟨1825547, by rfl⟩ : syracuseStep 2434063 = 3651095) B3651095
theorem B4326443 : Blo 1709055 4326443 := bstep (se 1 (by rfl) ⟨3244832, by rfl⟩ : syracuseStep 4326443 = 6489665) B6489665
theorem B2311211 : Blo 1709055 2311211 := bstep (se 1 (by rfl) ⟨1733408, by rfl⟩ : syracuseStep 2311211 = 3466817) B3466817
theorem B2565179 : Blo 1709055 2565179 := bstep (se 1 (by rfl) ⟨1923884, by rfl⟩ : syracuseStep 2565179 = 3847769) B3847769
theorem B5768279 : Blo 1709055 5768279 := bstep (se 1 (by rfl) ⟨4326209, by rfl⟩ : syracuseStep 5768279 = 8652419) B8652419
theorem B2884727 : Blo 1709055 2884727 := bstep (se 1 (by rfl) ⟨2163545, by rfl⟩ : syracuseStep 2884727 = 4327091) B4327091
theorem B2565239 : Blo 1709055 2565239 := bstep (se 1 (by rfl) ⟨1923929, by rfl⟩ : syracuseStep 2565239 = 3847859) B3847859
theorem B9372791 : Blo 1709055 9372791 := bstep (se 1 (by rfl) ⟨7029593, by rfl⟩ : syracuseStep 9372791 = 14059187) B14059187
theorem B7308407 : Blo 1709055 7308407 := bstep (se 1 (by rfl) ⟨5481305, by rfl⟩ : syracuseStep 7308407 = 10962611) B10962611
theorem B2565263 : Blo 1709055 2565263 := bstep (se 1 (by rfl) ⟨1923947, by rfl⟩ : syracuseStep 2565263 = 3847895) B3847895
theorem B2565305 : Blo 1709055 2565305 := bstep (se 2 (by rfl) ⟨961989, by rfl⟩ : syracuseStep 2565305 = 1923979) B1923979
theorem B2565383 : Blo 1709055 2565383 := bstep (se 1 (by rfl) ⟨1924037, by rfl⟩ : syracuseStep 2565383 = 3848075) B3848075
theorem B3081505 : Blo 1709055 3081505 := bstep (se 2 (by rfl) ⟨1155564, by rfl⟩ : syracuseStep 3081505 = 2311129) B2311129
theorem B2565419 : Blo 1709055 2565419 := bstep (se 1 (by rfl) ⟨1924064, by rfl⟩ : syracuseStep 2565419 = 3848129) B3848129
theorem B2565449 : Blo 1709055 2565449 := bstep (se 2 (by rfl) ⟨962043, by rfl⟩ : syracuseStep 2565449 = 1924087) B1924087
theorem B2164087 : Blo 1709055 2164087 := bstep (se 1 (by rfl) ⟨1623065, by rfl⟩ : syracuseStep 2164087 = 3246131) B3246131
theorem B3245447 : Blo 1709055 3245447 := bstep (se 1 (by rfl) ⟨2434085, by rfl⟩ : syracuseStep 3245447 = 4868171) B4868171
theorem B6489497 : Blo 1709055 6489497 := bstep (se 2 (by rfl) ⟨2433561, by rfl⟩ : syracuseStep 6489497 = 4867123) B4867123
theorem B5932441 : Blo 1709055 5932441 := bstep (se 2 (by rfl) ⟨2224665, by rfl⟩ : syracuseStep 5932441 = 4449331) B4449331
theorem B47449529 : Blo 1709055 47449529 := bstep (se 2 (by rfl) ⟨17793573, by rfl⟩ : syracuseStep 47449529 = 35587147) B35587147
theorem B2565563 : Blo 1709055 2565563 := bstep (se 1 (by rfl) ⟨1924172, by rfl⟩ : syracuseStep 2565563 = 3848345) B3848345
theorem B2565623 : Blo 1709055 2565623 := bstep (se 1 (by rfl) ⟨1924217, by rfl⟩ : syracuseStep 2565623 = 3848435) B3848435
theorem B2565647 : Blo 1709055 2565647 := bstep (se 1 (by rfl) ⟨1924235, by rfl⟩ : syracuseStep 2565647 = 3848471) B3848471
theorem B7300651 : Blo 1709055 7300651 := bstep (se 1 (by rfl) ⟨5475488, by rfl⟩ : syracuseStep 7300651 = 10950977) B10950977
theorem B2565689 : Blo 1709055 2565689 := bstep (se 2 (by rfl) ⟨962133, by rfl⟩ : syracuseStep 2565689 = 1924267) B1924267
theorem B2885179 : Blo 1709055 2885179 := bstep (se 1 (by rfl) ⟨2163884, by rfl⟩ : syracuseStep 2885179 = 4327769) B4327769
theorem B5768765 : Blo 1709055 5768765 := bstep (se 3 (by rfl) ⟨1081643, by rfl⟩ : syracuseStep 5768765 = 2163287) B2163287
theorem B25683533 : Blo 1709055 25683533 := bstep (se 3 (by rfl) ⟨4815662, by rfl⟩ : syracuseStep 25683533 = 9631325) B9631325
theorem B2565767 : Blo 1709055 2565767 := bstep (se 1 (by rfl) ⟨1924325, by rfl⟩ : syracuseStep 2565767 = 3848651) B3848651
theorem B2565803 : Blo 1709055 2565803 := bstep (se 1 (by rfl) ⟨1924352, by rfl⟩ : syracuseStep 2565803 = 3848705) B3848705
theorem B2164411 : Blo 1709055 2164411 := bstep (se 1 (by rfl) ⟨1623308, by rfl⟩ : syracuseStep 2164411 = 3246617) B3246617
theorem B2885321 : Blo 1709055 2885321 := bstep (se 2 (by rfl) ⟨1081995, by rfl⟩ : syracuseStep 2885321 = 2163991) B2163991
theorem B2565833 : Blo 1709055 2565833 := bstep (se 2 (by rfl) ⟨962187, by rfl⟩ : syracuseStep 2565833 = 1924375) B1924375
theorem B8660681 : Blo 1709055 8660681 := bstep (se 2 (by rfl) ⟨3247755, by rfl⟩ : syracuseStep 8660681 = 6495511) B6495511
theorem B2565947 : Blo 1709055 2565947 := bstep (se 1 (by rfl) ⟨1924460, by rfl⟩ : syracuseStep 2565947 = 3848921) B3848921
theorem B4327283 : Blo 1709055 4327283 := bstep (se 1 (by rfl) ⟨3245462, by rfl⟩ : syracuseStep 4327283 = 6490925) B6490925
theorem B2566007 : Blo 1709055 2566007 := bstep (se 1 (by rfl) ⟨1924505, by rfl⟩ : syracuseStep 2566007 = 3849011) B3849011
theorem B4327303 : Blo 1709055 4327303 := bstep (se 1 (by rfl) ⟨3245477, by rfl⟩ : syracuseStep 4327303 = 6490955) B6490955
theorem B2434951 : Blo 1709055 2434951 := bstep (se 1 (by rfl) ⟨1826213, by rfl⟩ : syracuseStep 2434951 = 3652427) B3652427
theorem B2566031 : Blo 1709055 2566031 := bstep (se 1 (by rfl) ⟨1924523, by rfl⟩ : syracuseStep 2566031 = 3849047) B3849047
theorem B9742265 : Blo 1709055 9742265 := bstep (se 2 (by rfl) ⟨3653349, by rfl⟩ : syracuseStep 9742265 = 7306699) B7306699
theorem B2566073 : Blo 1709055 2566073 := bstep (se 2 (by rfl) ⟨962277, by rfl⟩ : syracuseStep 2566073 = 1924555) B1924555
theorem B2566151 : Blo 1709055 2566151 := bstep (se 1 (by rfl) ⟨1924613, by rfl⟩ : syracuseStep 2566151 = 3849227) B3849227
theorem B3467279 : Blo 1709055 3467279 := bstep (se 1 (by rfl) ⟨2600459, by rfl⟩ : syracuseStep 3467279 = 5200919) B5200919
theorem B2566187 : Blo 1709055 2566187 := bstep (se 1 (by rfl) ⟨1924640, by rfl⟩ : syracuseStep 2566187 = 3849281) B3849281
theorem B2566217 : Blo 1709055 2566217 := bstep (se 2 (by rfl) ⟨962331, by rfl⟩ : syracuseStep 2566217 = 1924663) B1924663
theorem B4327577 : Blo 1709055 4327577 := bstep (se 2 (by rfl) ⟨1622841, by rfl⟩ : syracuseStep 4327577 = 3245683) B3245683
theorem B2164907 : Blo 1709055 2164907 := bstep (se 1 (by rfl) ⟨1623680, by rfl⟩ : syracuseStep 2164907 = 3247361) B3247361
theorem B10954925 : Blo 1709055 10954925 := bstep (se 3 (by rfl) ⟨2054048, by rfl⟩ : syracuseStep 10954925 = 4108097) B4108097
theorem B2566331 : Blo 1709055 2566331 := bstep (se 1 (by rfl) ⟨1924748, by rfl⟩ : syracuseStep 2566331 = 3849497) B3849497
theorem B2566391 : Blo 1709055 2566391 := bstep (se 1 (by rfl) ⟨1924793, by rfl⟩ : syracuseStep 2566391 = 3849587) B3849587
theorem B4868353 : Blo 1709055 4868353 := bstep (se 2 (by rfl) ⟨1825632, by rfl⟩ : syracuseStep 4868353 = 3651265) B3651265
theorem B2566415 : Blo 1709055 2566415 := bstep (se 1 (by rfl) ⟨1924811, by rfl⟩ : syracuseStep 2566415 = 3849623) B3849623
theorem B2566457 : Blo 1709055 2566457 := bstep (se 2 (by rfl) ⟨962421, by rfl⟩ : syracuseStep 2566457 = 1924843) B1924843
theorem B4327739 : Blo 1709055 4327739 := bstep (se 1 (by rfl) ⟨3245804, by rfl⟩ : syracuseStep 4327739 = 6491609) B6491609
theorem B2599241 : Blo 1709055 2599241 := bstep (se 2 (by rfl) ⟨974715, by rfl⟩ : syracuseStep 2599241 = 1949431) B1949431
theorem B4385143 : Blo 1709055 4385143 := bstep (se 1 (by rfl) ⟨3288857, by rfl⟩ : syracuseStep 4385143 = 6577715) B6577715
theorem B2435447 : Blo 1709055 2435447 := bstep (se 1 (by rfl) ⟨1826585, by rfl⟩ : syracuseStep 2435447 = 3653171) B3653171
theorem B2886023 : Blo 1709055 2886023 := bstep (se 1 (by rfl) ⟨2164517, by rfl⟩ : syracuseStep 2886023 = 4329035) B4329035
theorem B2566535 : Blo 1709055 2566535 := bstep (se 1 (by rfl) ⟨1924901, by rfl⟩ : syracuseStep 2566535 = 3849803) B3849803
theorem B2566571 : Blo 1709055 2566571 := bstep (se 1 (by rfl) ⟨1924928, by rfl⟩ : syracuseStep 2566571 = 3849857) B3849857
theorem B4622777 : Blo 1709055 4622777 := bstep (se 2 (by rfl) ⟨1733541, by rfl⟩ : syracuseStep 4622777 = 3467083) B3467083
theorem B4327951 : Blo 1709055 4327951 := bstep (se 1 (by rfl) ⟨3245963, by rfl⟩ : syracuseStep 4327951 = 6491927) B6491927
theorem B2165383 : Blo 1709055 2165383 := bstep (se 1 (by rfl) ⟨1624037, by rfl⟩ : syracuseStep 2165383 = 3248075) B3248075
theorem B133196501 : Blo 1709055 133196501 := bstep (se 7 (by rfl) ⟨1560896, by rfl⟩ : syracuseStep 133196501 = 3121793) B3121793
theorem B4328225 : Blo 1709055 4328225 := bstep (se 2 (by rfl) ⟨1623084, by rfl⟩ : syracuseStep 4328225 = 3246169) B3246169
theorem B4868923 : Blo 1709055 4868923 := bstep (se 1 (by rfl) ⟨3651692, by rfl⟩ : syracuseStep 4868923 = 7303385) B7303385
theorem B3124103 : Blo 1709055 3124103 := bstep (se 1 (by rfl) ⟨2343077, by rfl⟩ : syracuseStep 3124103 = 4686155) B4686155
theorem B8653715 : Blo 1709055 8653715 := bstep (se 1 (by rfl) ⟨6490286, by rfl⟩ : syracuseStep 8653715 = 12980573) B12980573
theorem B5770169 : Blo 1709055 5770169 := bstep (se 2 (by rfl) ⟨2163813, by rfl⟩ : syracuseStep 5770169 = 4327627) B4327627
theorem B2886671 : Blo 1709055 2886671 := bstep (se 1 (by rfl) ⟨2165003, by rfl⟩ : syracuseStep 2886671 = 4330007) B4330007
theorem B15600701 : Blo 1709055 15600701 := bstep (se 3 (by rfl) ⟨2925131, by rfl⟩ : syracuseStep 15600701 = 5850263) B5850263
theorem B2468983 : Blo 1709055 2468983 := bstep (se 1 (by rfl) ⟨1851737, by rfl⟩ : syracuseStep 2468983 = 3703475) B3703475
theorem B4386059 : Blo 1709055 4386059 := bstep (se 1 (by rfl) ⟨3289544, by rfl⟩ : syracuseStep 4386059 = 6579089) B6579089
theorem B14601505 : Blo 1709055 14601505 := bstep (se 2 (by rfl) ⟨5475564, by rfl⟩ : syracuseStep 14601505 = 10951129) B10951129
theorem B12832033 : Blo 1709055 12832033 := bstep (se 2 (by rfl) ⟨4812012, by rfl⟩ : syracuseStep 12832033 = 9624025) B9624025
theorem B9244039 : Blo 1709055 9244039 := bstep (se 1 (by rfl) ⟨6933029, by rfl⟩ : syracuseStep 9244039 = 13866059) B13866059
theorem B6163847 : Blo 1709055 6163847 := bstep (se 1 (by rfl) ⟨4622885, by rfl⟩ : syracuseStep 6163847 = 9245771) B9245771
theorem B31214983 : Blo 1709055 31214983 := bstep (se 1 (by rfl) ⟨23411237, by rfl⟩ : syracuseStep 31214983 = 46822475) B46822475
theorem B12979601 : Blo 1709055 12979601 := bstep (se 2 (by rfl) ⟨4867350, by rfl⟩ : syracuseStep 12979601 = 9734701) B9734701
theorem B5770763 : Blo 1709055 5770763 := bstep (se 1 (by rfl) ⟨4328072, by rfl⟩ : syracuseStep 5770763 = 8656145) B8656145
theorem B2887211 : Blo 1709055 2887211 := bstep (se 1 (by rfl) ⟨2165408, by rfl⟩ : syracuseStep 2887211 = 4330817) B4330817
theorem B2600507 : Blo 1709055 2600507 := bstep (se 1 (by rfl) ⟨1950380, by rfl⟩ : syracuseStep 2600507 = 3900761) B3900761
theorem B5770871 : Blo 1709055 5770871 := bstep (se 1 (by rfl) ⟨4328153, by rfl⟩ : syracuseStep 5770871 = 8656307) B8656307
theorem B4329227 : Blo 1709055 4329227 := bstep (se 1 (by rfl) ⟨3246920, by rfl⟩ : syracuseStep 4329227 = 6493841) B6493841
theorem B3247931 : Blo 1709055 3247931 := bstep (se 1 (by rfl) ⟨2435948, by rfl⟩ : syracuseStep 3247931 = 4871897) B4871897
theorem B3846023 : Blo 1709055 3846023 := bstep (se 1 (by rfl) ⟨2884517, by rfl⟩ : syracuseStep 3846023 = 5769035) B5769035
theorem B10399691 : Blo 1709055 10399691 := bstep (se 1 (by rfl) ⟨7799768, by rfl⟩ : syracuseStep 10399691 = 15599537) B15599537
theorem B9744407 : Blo 1709055 9744407 := bstep (se 1 (by rfl) ⟨7308305, by rfl⟩ : syracuseStep 9744407 = 14616611) B14616611
theorem B3846203 : Blo 1709055 3846203 := bstep (se 1 (by rfl) ⟨2884652, by rfl⟩ : syracuseStep 3846203 = 5769305) B5769305
theorem B3846329 : Blo 1709055 3846329 := bstep (se 2 (by rfl) ⟨1442373, by rfl⟩ : syracuseStep 3846329 = 2884747) B2884747
theorem B1732795 : Blo 1709055 1732795 := bstep (se 1 (by rfl) ⟨1299596, by rfl⟩ : syracuseStep 1732795 = 2599193) B2599193
theorem B8220865 : Blo 1709055 8220865 := bstep (se 2 (by rfl) ⟨3082824, by rfl⟩ : syracuseStep 8220865 = 6165649) B6165649
theorem B5771465 : Blo 1709055 5771465 := bstep (se 2 (by rfl) ⟨2164299, by rfl⟩ : syracuseStep 5771465 = 4328599) B4328599
theorem B4329875 : Blo 1709055 4329875 := bstep (se 1 (by rfl) ⟨3247406, by rfl⟩ : syracuseStep 4329875 = 6494813) B6494813
theorem B9744907 : Blo 1709055 9744907 := bstep (se 1 (by rfl) ⟨7308680, by rfl⟩ : syracuseStep 9744907 = 14617361) B14617361
theorem B3846671 : Blo 1709055 3846671 := bstep (se 1 (by rfl) ⟨2885003, by rfl⟩ : syracuseStep 3846671 = 5770007) B5770007
theorem B3846689 : Blo 1709055 3846689 := bstep (se 2 (by rfl) ⟨1442508, by rfl⟩ : syracuseStep 3846689 = 2885017) B2885017
theorem B4330169 : Blo 1709055 4330169 := bstep (se 2 (by rfl) ⟨1623813, by rfl⟩ : syracuseStep 4330169 = 3247627) B3247627
theorem B8221499 : Blo 1709055 8221499 := bstep (se 1 (by rfl) ⟨6166124, by rfl⟩ : syracuseStep 8221499 = 12332249) B12332249
theorem B2634569 : Blo 1709055 2634569 := bstep (se 2 (by rfl) ⟨987963, by rfl⟩ : syracuseStep 2634569 = 1975927) B1975927
theorem B3847031 : Blo 1709055 3847031 := bstep (se 1 (by rfl) ⟨2885273, by rfl⟩ : syracuseStep 3847031 = 5770547) B5770547
theorem B5772167 : Blo 1709055 5772167 := bstep (se 1 (by rfl) ⟨4329125, by rfl⟩ : syracuseStep 5772167 = 8658251) B8658251
theorem B6493081 : Blo 1709055 6493081 := bstep (se 2 (by rfl) ⟨2434905, by rfl⟩ : syracuseStep 6493081 = 4869811) B4869811
theorem B1709063 : Blo 1709055 1709063 := bstep (se 1 (by rfl) ⟨1281797, by rfl⟩ : syracuseStep 1709063 = 2563595) B2563595
theorem B1709071 : Blo 1709055 1709071 := bstep (se 1 (by rfl) ⟨1281803, by rfl⟩ : syracuseStep 1709071 = 2563607) B2563607
theorem B3847211 : Blo 1709055 3847211 := bstep (se 1 (by rfl) ⟨2885408, by rfl⟩ : syracuseStep 3847211 = 5770817) B5770817
theorem B1709115 : Blo 1709055 1709115 := bstep (se 1 (by rfl) ⟨1281836, by rfl⟩ : syracuseStep 1709115 = 2563673) B2563673
theorem B14611589 : Blo 1709055 14611589 := bstep (se 4 (by rfl) ⟨1369836, by rfl⟩ : syracuseStep 14611589 = 2739673) B2739673
theorem B1709191 : Blo 1709055 1709191 := bstep (se 1 (by rfl) ⟨1281893, by rfl⟩ : syracuseStep 1709191 = 2563787) B2563787
theorem B1709199 : Blo 1709055 1709199 := bstep (se 1 (by rfl) ⟨1281899, by rfl⟩ : syracuseStep 1709199 = 2563799) B2563799
theorem B5198995 : Blo 1709055 5198995 := bstep (se 1 (by rfl) ⟨3899246, by rfl⟩ : syracuseStep 5198995 = 7798493) B7798493
theorem B4871315 : Blo 1709055 4871315 := bstep (se 1 (by rfl) ⟨3653486, by rfl⟩ : syracuseStep 4871315 = 7306973) B7306973
theorem B1709243 : Blo 1709055 1709243 := bstep (se 1 (by rfl) ⟨1281932, by rfl⟩ : syracuseStep 1709243 = 2563865) B2563865
theorem B6493385 : Blo 1709055 6493385 := bstep (se 2 (by rfl) ⟨2435019, by rfl⟩ : syracuseStep 6493385 = 4870039) B4870039
theorem B5772545 : Blo 1709055 5772545 := bstep (se 2 (by rfl) ⟨2164704, by rfl⟩ : syracuseStep 5772545 = 4329409) B4329409
theorem B1709319 : Blo 1709055 1709319 := bstep (se 1 (by rfl) ⟨1281989, by rfl⟩ : syracuseStep 1709319 = 2563979) B2563979
theorem B1709327 : Blo 1709055 1709327 := bstep (se 1 (by rfl) ⟨1281995, by rfl⟩ : syracuseStep 1709327 = 2563991) B2563991
theorem B1709371 : Blo 1709055 1709371 := bstep (se 1 (by rfl) ⟨1282028, by rfl⟩ : syracuseStep 1709371 = 2564057) B2564057
theorem B8213849 : Blo 1709055 8213849 := bstep (se 2 (by rfl) ⟨3080193, by rfl⟩ : syracuseStep 8213849 = 6160387) B6160387
theorem B4330867 : Blo 1709055 4330867 := bstep (se 1 (by rfl) ⟨3248150, by rfl⟩ : syracuseStep 4330867 = 6496301) B6496301
theorem B1709447 : Blo 1709055 1709447 := bstep (se 1 (by rfl) ⟨1282085, by rfl⟩ : syracuseStep 1709447 = 2564171) B2564171
theorem B1709455 : Blo 1709055 1709455 := bstep (se 1 (by rfl) ⟨1282091, by rfl⟩ : syracuseStep 1709455 = 2564183) B2564183
theorem B9737617 : Blo 1709055 9737617 := bstep (se 2 (by rfl) ⟨3651606, by rfl⟩ : syracuseStep 9737617 = 7303213) B7303213
theorem B3847571 : Blo 1709055 3847571 := bstep (se 1 (by rfl) ⟨2885678, by rfl⟩ : syracuseStep 3847571 = 5771357) B5771357
theorem B1709499 : Blo 1709055 1709499 := bstep (se 1 (by rfl) ⟨1282124, by rfl⟩ : syracuseStep 1709499 = 2564249) B2564249
theorem B3847625 : Blo 1709055 3847625 := bstep (se 2 (by rfl) ⟨1442859, by rfl⟩ : syracuseStep 3847625 = 2885719) B2885719
theorem B4331009 : Blo 1709055 4331009 := bstep (se 2 (by rfl) ⟨1624128, by rfl⟩ : syracuseStep 4331009 = 3248257) B3248257
theorem B1709575 : Blo 1709055 1709575 := bstep (se 1 (by rfl) ⟨1282181, by rfl⟩ : syracuseStep 1709575 = 2564363) B2564363
theorem B1709583 : Blo 1709055 1709583 := bstep (se 1 (by rfl) ⟨1282187, by rfl⟩ : syracuseStep 1709583 = 2564375) B2564375
theorem B1709627 : Blo 1709055 1709627 := bstep (se 1 (by rfl) ⟨1282220, by rfl⟩ : syracuseStep 1709627 = 2564441) B2564441
theorem B35083853 : Blo 1709055 35083853 := bstep (se 3 (by rfl) ⟨6578222, by rfl⟩ : syracuseStep 35083853 = 13156445) B13156445
theorem B5477975 : Blo 1709055 5477975 := bstep (se 1 (by rfl) ⟨4108481, by rfl⟩ : syracuseStep 5477975 = 8216963) B8216963
theorem B1709703 : Blo 1709055 1709703 := bstep (se 1 (by rfl) ⟨1282277, by rfl⟩ : syracuseStep 1709703 = 2564555) B2564555
theorem B1709711 : Blo 1709055 1709711 := bstep (se 1 (by rfl) ⟨1282283, by rfl⟩ : syracuseStep 1709711 = 2564567) B2564567
theorem B3651257 : Blo 1709055 3651257 := bstep (se 2 (by rfl) ⟨1369221, by rfl⟩ : syracuseStep 3651257 = 2738443) B2738443
theorem B1709755 : Blo 1709055 1709755 := bstep (se 1 (by rfl) ⟨1282316, by rfl⟩ : syracuseStep 1709755 = 2564633) B2564633
theorem B16430849 : Blo 1709055 16430849 := bstep (se 2 (by rfl) ⟨6161568, by rfl⟩ : syracuseStep 16430849 = 12323137) B12323137
theorem B1709831 : Blo 1709055 1709831 := bstep (se 1 (by rfl) ⟨1282373, by rfl⟩ : syracuseStep 1709831 = 2564747) B2564747
theorem B12982031 : Blo 1709055 12982031 := bstep (se 1 (by rfl) ⟨9736523, by rfl⟩ : syracuseStep 12982031 = 19473047) B19473047
theorem B1709839 : Blo 1709055 1709839 := bstep (se 1 (by rfl) ⟨1282379, by rfl⟩ : syracuseStep 1709839 = 2564759) B2564759
theorem B7304975 : Blo 1709055 7304975 := bstep (se 1 (by rfl) ⟨5478731, by rfl⟩ : syracuseStep 7304975 = 10957463) B10957463
theorem B19470131 : Blo 1709055 19470131 := bstep (se 1 (by rfl) ⟨14602598, by rfl⟩ : syracuseStep 19470131 = 29205197) B29205197
theorem B1709883 : Blo 1709055 1709883 := bstep (se 1 (by rfl) ⟨1282412, by rfl⟩ : syracuseStep 1709883 = 2564825) B2564825
theorem B10950515 : Blo 1709055 10950515 := bstep (se 1 (by rfl) ⟨8212886, by rfl⟩ : syracuseStep 10950515 = 16425773) B16425773
theorem B3700615 : Blo 1709055 3700615 := bstep (se 1 (by rfl) ⟨2775461, by rfl⟩ : syracuseStep 3700615 = 5550923) B5550923
theorem B1709959 : Blo 1709055 1709959 := bstep (se 1 (by rfl) ⟨1282469, by rfl⟩ : syracuseStep 1709959 = 2564939) B2564939
theorem B1709967 : Blo 1709055 1709967 := bstep (se 1 (by rfl) ⟨1282475, by rfl⟩ : syracuseStep 1709967 = 2564951) B2564951
theorem B8656793 : Blo 1709055 8656793 := bstep (se 2 (by rfl) ⟨3246297, by rfl⟩ : syracuseStep 8656793 = 6492595) B6492595
theorem B4872089 : Blo 1709055 4872089 := bstep (se 2 (by rfl) ⟨1827033, by rfl⟩ : syracuseStep 4872089 = 3654067) B3654067
theorem B1710011 : Blo 1709055 1710011 := bstep (se 1 (by rfl) ⟨1282508, by rfl⟩ : syracuseStep 1710011 = 2565017) B2565017
theorem B1923079 : Blo 1709055 1923079 := bstep (se 1 (by rfl) ⟨1442309, by rfl⟩ : syracuseStep 1923079 = 2884619) B2884619
theorem B1710087 : Blo 1709055 1710087 := bstep (se 1 (by rfl) ⟨1282565, by rfl⟩ : syracuseStep 1710087 = 2565131) B2565131
theorem B1710095 : Blo 1709055 1710095 := bstep (se 1 (by rfl) ⟨1282571, by rfl⟩ : syracuseStep 1710095 = 2565143) B2565143
theorem B5773355 : Blo 1709055 5773355 := bstep (se 1 (by rfl) ⟨4330016, by rfl⟩ : syracuseStep 5773355 = 8660033) B8660033
theorem B1710139 : Blo 1709055 1710139 := bstep (se 1 (by rfl) ⟨1282604, by rfl⟩ : syracuseStep 1710139 = 2565209) B2565209
theorem B6494327 : Blo 1709055 6494327 := bstep (se 1 (by rfl) ⟨4870745, by rfl⟩ : syracuseStep 6494327 = 9741491) B9741491
theorem B6936695 : Blo 1709055 6936695 := bstep (se 1 (by rfl) ⟨5202521, by rfl⟩ : syracuseStep 6936695 = 10405043) B10405043
theorem B1710215 : Blo 1709055 1710215 := bstep (se 1 (by rfl) ⟨1282661, by rfl⟩ : syracuseStep 1710215 = 2565323) B2565323
theorem B3848327 : Blo 1709055 3848327 := bstep (se 1 (by rfl) ⟨2886245, by rfl⟩ : syracuseStep 3848327 = 5772491) B5772491
theorem B1710223 : Blo 1709055 1710223 := bstep (se 1 (by rfl) ⟨1282667, by rfl⟩ : syracuseStep 1710223 = 2565335) B2565335
theorem B1923259 : Blo 1709055 1923259 := bstep (se 1 (by rfl) ⟨1442444, by rfl⟩ : syracuseStep 1923259 = 2884889) B2884889
theorem B1710267 : Blo 1709055 1710267 := bstep (se 1 (by rfl) ⟨1282700, by rfl⟩ : syracuseStep 1710267 = 2565401) B2565401
theorem B1710343 : Blo 1709055 1710343 := bstep (se 1 (by rfl) ⟨1282757, by rfl⟩ : syracuseStep 1710343 = 2565515) B2565515
theorem B5200139 : Blo 1709055 5200139 := bstep (se 1 (by rfl) ⟨3900104, by rfl⟩ : syracuseStep 5200139 = 7800209) B7800209
theorem B1710351 : Blo 1709055 1710351 := bstep (se 1 (by rfl) ⟨1282763, by rfl⟩ : syracuseStep 1710351 = 2565527) B2565527
theorem B1710395 : Blo 1709055 1710395 := bstep (se 1 (by rfl) ⟨1282796, by rfl⟩ : syracuseStep 1710395 = 2565593) B2565593
theorem B3848507 : Blo 1709055 3848507 := bstep (se 1 (by rfl) ⟨2886380, by rfl⟩ : syracuseStep 3848507 = 5772761) B5772761
theorem B16439611 : Blo 1709055 16439611 := bstep (se 1 (by rfl) ⟨12329708, by rfl⟩ : syracuseStep 16439611 = 24659417) B24659417
theorem B12990779 : Blo 1709055 12990779 := bstep (se 1 (by rfl) ⟨9743084, by rfl⟩ : syracuseStep 12990779 = 19486169) B19486169
theorem B1710471 : Blo 1709055 1710471 := bstep (se 1 (by rfl) ⟨1282853, by rfl⟩ : syracuseStep 1710471 = 2565707) B2565707
theorem B1710479 : Blo 1709055 1710479 := bstep (se 1 (by rfl) ⟨1282859, by rfl⟩ : syracuseStep 1710479 = 2565719) B2565719
theorem B3848633 : Blo 1709055 3848633 := bstep (se 2 (by rfl) ⟨1443237, by rfl⟩ : syracuseStep 3848633 = 2886475) B2886475
theorem B1710523 : Blo 1709055 1710523 := bstep (se 1 (by rfl) ⟨1282892, by rfl⟩ : syracuseStep 1710523 = 2565785) B2565785
theorem B4938241 : Blo 1709055 4938241 := bstep (se 2 (by rfl) ⟨1851840, by rfl⟩ : syracuseStep 4938241 = 3703681) B3703681
theorem B13867523 : Blo 1709055 13867523 := bstep (se 1 (by rfl) ⟨10400642, by rfl⟩ : syracuseStep 13867523 = 20801285) B20801285
theorem B1710599 : Blo 1709055 1710599 := bstep (se 1 (by rfl) ⟨1282949, by rfl⟩ : syracuseStep 1710599 = 2565899) B2565899
theorem B1710607 : Blo 1709055 1710607 := bstep (se 1 (by rfl) ⟨1282955, by rfl⟩ : syracuseStep 1710607 = 2565911) B2565911
theorem B1710651 : Blo 1709055 1710651 := bstep (se 1 (by rfl) ⟨1282988, by rfl⟩ : syracuseStep 1710651 = 2565977) B2565977
theorem B1710727 : Blo 1709055 1710727 := bstep (se 1 (by rfl) ⟨1283045, by rfl⟩ : syracuseStep 1710727 = 2566091) B2566091
theorem B1923727 : Blo 1709055 1923727 := bstep (se 1 (by rfl) ⟨1442795, by rfl⟩ : syracuseStep 1923727 = 2885591) B2885591
theorem B1710735 : Blo 1709055 1710735 := bstep (se 1 (by rfl) ⟨1283051, by rfl⟩ : syracuseStep 1710735 = 2566103) B2566103
theorem B1710779 : Blo 1709055 1710779 := bstep (se 1 (by rfl) ⟨1283084, by rfl⟩ : syracuseStep 1710779 = 2566169) B2566169
theorem B1710855 : Blo 1709055 1710855 := bstep (se 1 (by rfl) ⟨1283141, by rfl⟩ : syracuseStep 1710855 = 2566283) B2566283
theorem B3848975 : Blo 1709055 3848975 := bstep (se 1 (by rfl) ⟨2886731, by rfl⟩ : syracuseStep 3848975 = 5773463) B5773463
theorem B1710863 : Blo 1709055 1710863 := bstep (se 1 (by rfl) ⟨1283147, by rfl⟩ : syracuseStep 1710863 = 2566295) B2566295
theorem B3848993 : Blo 1709055 3848993 := bstep (se 2 (by rfl) ⟨1443372, by rfl⟩ : syracuseStep 3848993 = 2886745) B2886745
theorem B16431923 : Blo 1709055 16431923 := bstep (se 1 (by rfl) ⟨12323942, by rfl⟩ : syracuseStep 16431923 = 24647885) B24647885
theorem B1710907 : Blo 1709055 1710907 := bstep (se 1 (by rfl) ⟨1283180, by rfl⟩ : syracuseStep 1710907 = 2566361) B2566361
theorem B1710983 : Blo 1709055 1710983 := bstep (se 1 (by rfl) ⟨1283237, by rfl⟩ : syracuseStep 1710983 = 2566475) B2566475
theorem B1710991 : Blo 1709055 1710991 := bstep (se 1 (by rfl) ⟨1283243, by rfl⟩ : syracuseStep 1710991 = 2566487) B2566487
theorem B8895379 : Blo 1709055 8895379 := bstep (se 1 (by rfl) ⟨6671534, by rfl⟩ : syracuseStep 8895379 = 13343069) B13343069
theorem B1711035 : Blo 1709055 1711035 := bstep (se 1 (by rfl) ⟨1283276, by rfl⟩ : syracuseStep 1711035 = 2566553) B2566553
theorem B2923465 : Blo 1709055 2923465 := bstep (se 2 (by rfl) ⟨1096299, by rfl⟩ : syracuseStep 2923465 = 2192599) B2192599
theorem B6495299 : Blo 1709055 6495299 := bstep (se 1 (by rfl) ⟨4871474, by rfl⟩ : syracuseStep 6495299 = 9742949) B9742949
theorem B3849335 : Blo 1709055 3849335 := bstep (se 1 (by rfl) ⟨2887001, by rfl⟩ : syracuseStep 3849335 = 5774003) B5774003
theorem B1924231 : Blo 1709055 1924231 := bstep (se 1 (by rfl) ⟨1443173, by rfl⟩ : syracuseStep 1924231 = 2886347) B2886347
theorem B3849515 : Blo 1709055 3849515 := bstep (se 1 (by rfl) ⟨2887136, by rfl⟩ : syracuseStep 3849515 = 5774273) B5774273
theorem B1924411 : Blo 1709055 1924411 := bstep (se 1 (by rfl) ⟨1443308, by rfl⟩ : syracuseStep 1924411 = 2886617) B2886617
theorem B5774651 : Blo 1709055 5774651 := bstep (se 1 (by rfl) ⟨4330988, by rfl⟩ : syracuseStep 5774651 = 8661977) B8661977
theorem B23403907 : Blo 1709055 23403907 := bstep (se 1 (by rfl) ⟨17552930, by rfl⟩ : syracuseStep 23403907 = 35105861) B35105861
theorem B7306631 : Blo 1709055 7306631 := bstep (se 1 (by rfl) ⟨5479973, by rfl⟩ : syracuseStep 7306631 = 10959947) B10959947
theorem B6159883 : Blo 1709055 6159883 := bstep (se 1 (by rfl) ⟨4619912, by rfl⟩ : syracuseStep 6159883 = 9239825) B9239825
theorem B13868587 : Blo 1709055 13868587 := bstep (se 1 (by rfl) ⟨10401440, by rfl⟩ : syracuseStep 13868587 = 20802881) B20802881
theorem B2563643 : Blo 1709055 2563643 := bstep (se 1 (by rfl) ⟨1922732, by rfl⟩ : syracuseStep 2563643 = 3845465) B3845465
theorem B59260517 : Blo 1709055 59260517 := bstep (se 4 (by rfl) ⟨5555673, by rfl⟩ : syracuseStep 59260517 = 11111347) B11111347
theorem B2563703 : Blo 1709055 2563703 := bstep (se 1 (by rfl) ⟨1922777, by rfl⟩ : syracuseStep 2563703 = 3845555) B3845555
theorem B11705975 : Blo 1709055 11705975 := bstep (se 1 (by rfl) ⟨8779481, by rfl⟩ : syracuseStep 11705975 = 17558963) B17558963
theorem B2563727 : Blo 1709055 2563727 := bstep (se 1 (by rfl) ⟨1922795, by rfl⟩ : syracuseStep 2563727 = 3845591) B3845591
theorem B3849875 : Blo 1709055 3849875 := bstep (se 1 (by rfl) ⟨2887406, by rfl⟩ : syracuseStep 3849875 = 5774813) B5774813
theorem B2563769 : Blo 1709055 2563769 := bstep (se 2 (by rfl) ⟨961413, by rfl⟩ : syracuseStep 2563769 = 1922827) B1922827
theorem B9740033 : Blo 1709055 9740033 := bstep (se 2 (by rfl) ⟨3652512, by rfl⟩ : syracuseStep 9740033 = 7305025) B7305025
theorem B2563847 : Blo 1709055 2563847 := bstep (se 1 (by rfl) ⟨1922885, by rfl⟩ : syracuseStep 2563847 = 3845771) B3845771
theorem B1924879 : Blo 1709055 1924879 := bstep (se 1 (by rfl) ⟨1443659, by rfl⟩ : syracuseStep 1924879 = 2887319) B2887319
theorem B2563883 : Blo 1709055 2563883 := bstep (se 1 (by rfl) ⟨1922912, by rfl⟩ : syracuseStep 2563883 = 3845825) B3845825
theorem B2563913 : Blo 1709055 2563913 := bstep (se 2 (by rfl) ⟨961467, by rfl⟩ : syracuseStep 2563913 = 1922935) B1922935
theorem B49299353 : Blo 1709055 49299353 := bstep (se 2 (by rfl) ⟨18487257, by rfl⟩ : syracuseStep 49299353 = 36974515) B36974515
theorem B2310059 : Blo 1709055 2310059 := bstep (se 1 (by rfl) ⟨1732544, by rfl⟩ : syracuseStep 2310059 = 3465089) B3465089
theorem B2564027 : Blo 1709055 2564027 := bstep (se 1 (by rfl) ⟨1923020, by rfl⟩ : syracuseStep 2564027 = 3846041) B3846041
theorem B2564087 : Blo 1709055 2564087 := bstep (se 1 (by rfl) ⟨1923065, by rfl⟩ : syracuseStep 2564087 = 3846131) B3846131
theorem B2564105 : Blo 1709055 2564105 := bstep (se 2 (by rfl) ⟨961539, by rfl⟩ : syracuseStep 2564105 = 1923079) B1923079
theorem B6496271 : Blo 1709055 6496271 := bstep (se 1 (by rfl) ⟨4872203, by rfl⟩ : syracuseStep 6496271 = 9744407) B9744407
theorem B2564135 : Blo 1709055 2564135 := bstep (se 1 (by rfl) ⟨1923101, by rfl⟩ : syracuseStep 2564135 = 3846203) B3846203
theorem B2564219 : Blo 1709055 2564219 := bstep (se 1 (by rfl) ⟨1923164, by rfl⟩ : syracuseStep 2564219 = 3846329) B3846329
theorem B73965797 : Blo 1709055 73965797 := bstep (se 4 (by rfl) ⟨6934293, by rfl⟩ : syracuseStep 73965797 = 13868587) B13868587
theorem B2564345 : Blo 1709055 2564345 := bstep (se 2 (by rfl) ⟨961629, by rfl⟩ : syracuseStep 2564345 = 1923259) B1923259
theorem B10961153 : Blo 1709055 10961153 := bstep (se 2 (by rfl) ⟨4110432, by rfl⟩ : syracuseStep 10961153 = 8220865) B8220865
theorem B24994109 : Blo 1709055 24994109 := bstep (se 3 (by rfl) ⟨4686395, by rfl⟩ : syracuseStep 24994109 = 9372791) B9372791
theorem B19489085 : Blo 1709055 19489085 := bstep (se 3 (by rfl) ⟨3654203, by rfl⟩ : syracuseStep 19489085 = 7308407) B7308407
theorem B2564447 : Blo 1709055 2564447 := bstep (se 1 (by rfl) ⟨1923335, by rfl⟩ : syracuseStep 2564447 = 3846671) B3846671
theorem B2564459 : Blo 1709055 2564459 := bstep (se 1 (by rfl) ⟨1923344, by rfl⟩ : syracuseStep 2564459 = 3846689) B3846689
theorem B7029287 : Blo 1709055 7029287 := bstep (se 1 (by rfl) ⟨5271965, by rfl⟩ : syracuseStep 7029287 = 10543931) B10543931
theorem B5480999 : Blo 1709055 5480999 := bstep (se 1 (by rfl) ⟨4110749, by rfl⟩ : syracuseStep 5480999 = 8221499) B8221499
theorem B2884153 : Blo 1709055 2884153 := bstep (se 2 (by rfl) ⟨1081557, by rfl⟩ : syracuseStep 2884153 = 2163115) B2163115
theorem B2564687 : Blo 1709055 2564687 := bstep (se 1 (by rfl) ⟨1923515, by rfl⟩ : syracuseStep 2564687 = 3847031) B3847031
theorem B14811821 : Blo 1709055 14811821 := bstep (se 3 (by rfl) ⟨2777216, by rfl⟩ : syracuseStep 14811821 = 5554433) B5554433
theorem B12993209 : Blo 1709055 12993209 := bstep (se 2 (by rfl) ⟨4872453, by rfl⟩ : syracuseStep 12993209 = 9744907) B9744907
theorem B2884295 : Blo 1709055 2884295 := bstep (se 1 (by rfl) ⟨2163221, by rfl⟩ : syracuseStep 2884295 = 4326443) B4326443
theorem B2564807 : Blo 1709055 2564807 := bstep (se 1 (by rfl) ⟨1923605, by rfl⟩ : syracuseStep 2564807 = 3847211) B3847211
theorem B9741059 : Blo 1709055 9741059 := bstep (se 1 (by rfl) ⟨7305794, by rfl⟩ : syracuseStep 9741059 = 14611589) B14611589
theorem B2884457 : Blo 1709055 2884457 := bstep (se 2 (by rfl) ⟨1081671, by rfl⟩ : syracuseStep 2884457 = 2163343) B2163343
theorem B2564969 : Blo 1709055 2564969 := bstep (se 2 (by rfl) ⟨961863, by rfl⟩ : syracuseStep 2564969 = 1923727) B1923727
theorem B3244961 : Blo 1709055 3244961 := bstep (se 2 (by rfl) ⟨1216860, by rfl⟩ : syracuseStep 3244961 = 2433721) B2433721
theorem B2565047 : Blo 1709055 2565047 := bstep (se 1 (by rfl) ⟨1923785, by rfl⟩ : syracuseStep 2565047 = 3847571) B3847571
theorem B4326331 : Blo 1709055 4326331 := bstep (se 1 (by rfl) ⟨3244748, by rfl⟩ : syracuseStep 4326331 = 6489497) B6489497
theorem B2565083 : Blo 1709055 2565083 := bstep (se 1 (by rfl) ⟨1923812, by rfl⟩ : syracuseStep 2565083 = 3847625) B3847625
theorem B23389235 : Blo 1709055 23389235 := bstep (se 1 (by rfl) ⟨17541926, by rfl⟩ : syracuseStep 23389235 = 35083853) B35083853
theorem B17122355 : Blo 1709055 17122355 := bstep (se 1 (by rfl) ⟨12841766, by rfl⟩ : syracuseStep 17122355 = 25683533) B25683533
theorem B3245113 : Blo 1709055 3245113 := bstep (se 2 (by rfl) ⟨1216917, by rfl⟩ : syracuseStep 3245113 = 2433835) B2433835
theorem B10953899 : Blo 1709055 10953899 := bstep (se 1 (by rfl) ⟨8215424, by rfl⟩ : syracuseStep 10953899 = 16430849) B16430849
theorem B7300343 : Blo 1709055 7300343 := bstep (se 1 (by rfl) ⟨5475257, by rfl⟩ : syracuseStep 7300343 = 10950515) B10950515
theorem B2884855 : Blo 1709055 2884855 := bstep (se 1 (by rfl) ⟨2163641, by rfl⟩ : syracuseStep 2884855 = 4327283) B4327283
theorem B2311519 : Blo 1709055 2311519 := bstep (se 1 (by rfl) ⟨1733639, by rfl⟩ : syracuseStep 2311519 = 3467279) B3467279
theorem B3245417 : Blo 1709055 3245417 := bstep (se 2 (by rfl) ⟨1217031, by rfl⟩ : syracuseStep 3245417 = 2434063) B2434063
theorem B2565551 : Blo 1709055 2565551 := bstep (se 1 (by rfl) ⟨1924163, by rfl⟩ : syracuseStep 2565551 = 3848327) B3848327
theorem B2885051 : Blo 1709055 2885051 := bstep (se 1 (by rfl) ⟨2163788, by rfl⟩ : syracuseStep 2885051 = 4327577) B4327577
theorem B2565641 : Blo 1709055 2565641 := bstep (se 2 (by rfl) ⟨962115, by rfl⟩ : syracuseStep 2565641 = 1924231) B1924231
theorem B6931993 : Blo 1709055 6931993 := bstep (se 2 (by rfl) ⟨2599497, by rfl⟩ : syracuseStep 6931993 = 5198995) B5198995
theorem B2885159 : Blo 1709055 2885159 := bstep (se 1 (by rfl) ⟨2163869, by rfl⟩ : syracuseStep 2885159 = 4327739) B4327739
theorem B2565671 : Blo 1709055 2565671 := bstep (se 1 (by rfl) ⟨1924253, by rfl⟩ : syracuseStep 2565671 = 3848507) B3848507
theorem B8660519 : Blo 1709055 8660519 := bstep (se 1 (by rfl) ⟨6495389, by rfl⟩ : syracuseStep 8660519 = 12990779) B12990779
theorem B3081851 : Blo 1709055 3081851 := bstep (se 1 (by rfl) ⟨2311388, by rfl⟩ : syracuseStep 3081851 = 4622777) B4622777
theorem B2565755 : Blo 1709055 2565755 := bstep (se 1 (by rfl) ⟨1924316, by rfl⟩ : syracuseStep 2565755 = 3848633) B3848633
theorem B2565881 : Blo 1709055 2565881 := bstep (se 2 (by rfl) ⟨962205, by rfl⟩ : syracuseStep 2565881 = 1924411) B1924411
theorem B2885449 : Blo 1709055 2885449 := bstep (se 2 (by rfl) ⟨1082043, by rfl⟩ : syracuseStep 2885449 = 2164087) B2164087
theorem B31205209 : Blo 1709055 31205209 := bstep (se 2 (by rfl) ⟨11701953, by rfl⟩ : syracuseStep 31205209 = 23403907) B23403907
theorem B2565983 : Blo 1709055 2565983 := bstep (se 1 (by rfl) ⟨1924487, by rfl⟩ : syracuseStep 2565983 = 3848975) B3848975
theorem B2885483 : Blo 1709055 2885483 := bstep (se 1 (by rfl) ⟨2164112, by rfl⟩ : syracuseStep 2885483 = 4328225) B4328225
theorem B2565995 : Blo 1709055 2565995 := bstep (se 1 (by rfl) ⟨1924496, by rfl⟩ : syracuseStep 2565995 = 3848993) B3848993
theorem B10954615 : Blo 1709055 10954615 := bstep (se 1 (by rfl) ⟨8215961, by rfl⟩ : syracuseStep 10954615 = 16431923) B16431923
theorem B5769143 : Blo 1709055 5769143 := bstep (se 1 (by rfl) ⟨4326857, by rfl⟩ : syracuseStep 5769143 = 8653715) B8653715
theorem B12986405 : Blo 1709055 12986405 := bstep (se 4 (by rfl) ⟨1217475, by rfl⟩ : syracuseStep 12986405 = 2434951) B2434951
theorem B9734201 : Blo 1709055 9734201 := bstep (se 2 (by rfl) ⟨3650325, by rfl⟩ : syracuseStep 9734201 = 7300651) B7300651
theorem B2566223 : Blo 1709055 2566223 := bstep (se 1 (by rfl) ⟨1924667, by rfl⟩ : syracuseStep 2566223 = 3849335) B3849335
theorem B2566343 : Blo 1709055 2566343 := bstep (se 1 (by rfl) ⟨1924757, by rfl⟩ : syracuseStep 2566343 = 3849515) B3849515
theorem B2885881 : Blo 1709055 2885881 := bstep (se 2 (by rfl) ⟨1082205, by rfl⟩ : syracuseStep 2885881 = 2164411) B2164411
theorem B8653067 : Blo 1709055 8653067 := bstep (se 1 (by rfl) ⟨6489800, by rfl⟩ : syracuseStep 8653067 = 12979601) B12979601
theorem B2566505 : Blo 1709055 2566505 := bstep (se 2 (by rfl) ⟨962439, by rfl⟩ : syracuseStep 2566505 = 1924879) B1924879
theorem B2566583 : Blo 1709055 2566583 := bstep (se 1 (by rfl) ⟨1924937, by rfl⟩ : syracuseStep 2566583 = 3849875) B3849875
theorem B6162925 : Blo 1709055 6162925 := bstep (se 3 (by rfl) ⟨1155548, by rfl⟩ : syracuseStep 6162925 = 2311097) B2311097
theorem B2886151 : Blo 1709055 2886151 := bstep (se 1 (by rfl) ⟨2164613, by rfl⟩ : syracuseStep 2886151 = 4329227) B4329227
theorem B4934153 : Blo 1709055 4934153 := bstep (se 2 (by rfl) ⟨1850307, by rfl⟩ : syracuseStep 4934153 = 3700615) B3700615
theorem B5769737 : Blo 1709055 5769737 := bstep (se 2 (by rfl) ⟨2163651, by rfl⟩ : syracuseStep 5769737 = 4327303) B4327303
theorem B2165287 : Blo 1709055 2165287 := bstep (se 1 (by rfl) ⟨1623965, by rfl⟩ : syracuseStep 2165287 = 3247931) B3247931
theorem B6933127 : Blo 1709055 6933127 := bstep (se 1 (by rfl) ⟨5199845, by rfl⟩ : syracuseStep 6933127 = 10399691) B10399691
theorem B6163229 : Blo 1709055 6163229 := bstep (se 3 (by rfl) ⟨1155605, by rfl⟩ : syracuseStep 6163229 = 2311211) B2311211
theorem B2886583 : Blo 1709055 2886583 := bstep (se 1 (by rfl) ⟨2164937, by rfl⟩ : syracuseStep 2886583 = 4329875) B4329875
theorem B3468251 : Blo 1709055 3468251 := bstep (se 1 (by rfl) ⟨2601188, by rfl⟩ : syracuseStep 3468251 = 5202377) B5202377
theorem B6491137 : Blo 1709055 6491137 := bstep (se 2 (by rfl) ⟨2434176, by rfl⟩ : syracuseStep 6491137 = 4868353) B4868353
theorem B2886779 : Blo 1709055 2886779 := bstep (se 1 (by rfl) ⟨2165084, by rfl⟩ : syracuseStep 2886779 = 4330169) B4330169
theorem B1756379 : Blo 1709055 1756379 := bstep (se 1 (by rfl) ⟨1317284, by rfl⟩ : syracuseStep 1756379 = 2634569) B2634569
theorem B5770601 : Blo 1709055 5770601 := bstep (se 2 (by rfl) ⟨2163975, by rfl⟩ : syracuseStep 5770601 = 4327951) B4327951
theorem B3845519 : Blo 1709055 3845519 := bstep (se 1 (by rfl) ⟨2884139, by rfl⟩ : syracuseStep 3845519 = 5768279) B5768279
theorem B27725237 : Blo 1709055 27725237 := bstep (se 5 (by rfl) ⟨1299620, by rfl⟩ : syracuseStep 27725237 = 2599241) B2599241
theorem B3247543 : Blo 1709055 3247543 := bstep (se 1 (by rfl) ⟨2435657, by rfl⟩ : syracuseStep 3247543 = 4871315) B4871315
theorem B4328923 : Blo 1709055 4328923 := bstep (se 1 (by rfl) ⟨3246692, by rfl⟩ : syracuseStep 4328923 = 6493385) B6493385
theorem B2887177 : Blo 1709055 2887177 := bstep (se 2 (by rfl) ⟨1082691, by rfl⟩ : syracuseStep 2887177 = 2165383) B2165383
theorem B5475899 : Blo 1709055 5475899 := bstep (se 1 (by rfl) ⟨4106924, by rfl⟩ : syracuseStep 5475899 = 8213849) B8213849
theorem B31633019 : Blo 1709055 31633019 := bstep (se 1 (by rfl) ⟨23724764, by rfl⟩ : syracuseStep 31633019 = 47449529) B47449529
theorem B2887339 : Blo 1709055 2887339 := bstep (se 1 (by rfl) ⟨2165504, by rfl⟩ : syracuseStep 2887339 = 4331009) B4331009
theorem B8654525 : Blo 1709055 8654525 := bstep (se 3 (by rfl) ⟨1622723, by rfl⟩ : syracuseStep 8654525 = 3245447) B3245447
theorem B3845843 : Blo 1709055 3845843 := bstep (se 1 (by rfl) ⟨2884382, by rfl⟩ : syracuseStep 3845843 = 5768765) B5768765
theorem B6491897 : Blo 1709055 6491897 := bstep (se 2 (by rfl) ⟨2434461, by rfl⟩ : syracuseStep 6491897 = 4868923) B4868923
theorem B8654687 : Blo 1709055 8654687 := bstep (se 1 (by rfl) ⟨6491015, by rfl⟩ : syracuseStep 8654687 = 12982031) B12982031
theorem B4869983 : Blo 1709055 4869983 := bstep (se 1 (by rfl) ⟨3652487, by rfl⟩ : syracuseStep 4869983 = 7304975) B7304975
theorem B12980087 : Blo 1709055 12980087 := bstep (se 1 (by rfl) ⟨9735065, by rfl⟩ : syracuseStep 12980087 = 19470131) B19470131
theorem B36966293 : Blo 1709055 36966293 := bstep (se 6 (by rfl) ⟨866397, by rfl⟩ : syracuseStep 36966293 = 1732795) B1732795
theorem B5771195 : Blo 1709055 5771195 := bstep (se 1 (by rfl) ⟨4328396, by rfl⟩ : syracuseStep 5771195 = 8656793) B8656793
theorem B4329551 : Blo 1709055 4329551 := bstep (se 1 (by rfl) ⟨3247163, by rfl⟩ : syracuseStep 4329551 = 6494327) B6494327
theorem B4624463 : Blo 1709055 4624463 := bstep (se 1 (by rfl) ⟨3468347, by rfl⟩ : syracuseStep 4624463 = 6936695) B6936695
theorem B7303283 : Blo 1709055 7303283 := bstep (se 1 (by rfl) ⟨5477462, by rfl⟩ : syracuseStep 7303283 = 10954925) B10954925
theorem B9245015 : Blo 1709055 9245015 := bstep (se 1 (by rfl) ⟨6933761, by rfl⟩ : syracuseStep 9245015 = 13867523) B13867523
theorem B19468673 : Blo 1709055 19468673 := bstep (se 2 (by rfl) ⟨7300752, by rfl⟩ : syracuseStep 19468673 = 14601505) B14601505
theorem B17109377 : Blo 1709055 17109377 := bstep (se 2 (by rfl) ⟨6416016, by rfl⟩ : syracuseStep 17109377 = 12832033) B12832033
theorem B4108673 : Blo 1709055 4108673 := bstep (se 2 (by rfl) ⟨1540752, by rfl⟩ : syracuseStep 4108673 = 3081505) B3081505
theorem B88797667 : Blo 1709055 88797667 := bstep (se 1 (by rfl) ⟨66598250, by rfl⟩ : syracuseStep 88797667 = 133196501) B133196501
theorem B9736685 : Blo 1709055 9736685 := bstep (se 3 (by rfl) ⟨1825628, by rfl⟩ : syracuseStep 9736685 = 3651257) B3651257
theorem B12325385 : Blo 1709055 12325385 := bstep (se 2 (by rfl) ⟨4622019, by rfl⟩ : syracuseStep 12325385 = 9244039) B9244039
theorem B41619977 : Blo 1709055 41619977 := bstep (se 2 (by rfl) ⟨15607491, by rfl⟩ : syracuseStep 41619977 = 31214983) B31214983
theorem B7909921 : Blo 1709055 7909921 := bstep (se 2 (by rfl) ⟨2966220, by rfl⟩ : syracuseStep 7909921 = 5932441) B5932441
theorem B3846779 : Blo 1709055 3846779 := bstep (se 1 (by rfl) ⟨2885084, by rfl⟩ : syracuseStep 3846779 = 5770169) B5770169
theorem B8213177 : Blo 1709055 8213177 := bstep (se 2 (by rfl) ⟨3079941, by rfl⟩ : syracuseStep 8213177 = 6159883) B6159883
theorem B5550781 : Blo 1709055 5550781 := bstep (se 3 (by rfl) ⟨1040771, by rfl⟩ : syracuseStep 5550781 = 2081543) B2081543
theorem B10400467 : Blo 1709055 10400467 := bstep (se 1 (by rfl) ⟨7800350, by rfl⟩ : syracuseStep 10400467 = 15600701) B15600701
theorem B4330199 : Blo 1709055 4330199 := bstep (se 1 (by rfl) ⟨3247649, by rfl⟩ : syracuseStep 4330199 = 6495299) B6495299
theorem B3846905 : Blo 1709055 3846905 := bstep (se 2 (by rfl) ⟨1442589, by rfl⟩ : syracuseStep 3846905 = 2885179) B2885179
theorem B4109231 : Blo 1709055 4109231 := bstep (se 1 (by rfl) ⟨3081923, by rfl⟩ : syracuseStep 4109231 = 6163847) B6163847
theorem B4871087 : Blo 1709055 4871087 := bstep (se 1 (by rfl) ⟨3653315, by rfl⟩ : syracuseStep 4871087 = 7306631) B7306631
theorem B3847175 : Blo 1709055 3847175 := bstep (se 1 (by rfl) ⟨2885381, by rfl⟩ : syracuseStep 3847175 = 5770763) B5770763
theorem B1709095 : Blo 1709055 1709095 := bstep (se 1 (by rfl) ⟨1281821, by rfl⟩ : syracuseStep 1709095 = 2563643) B2563643
theorem B1733671 : Blo 1709055 1733671 := bstep (se 1 (by rfl) ⟨1300253, by rfl⟩ : syracuseStep 1733671 = 2600507) B2600507
theorem B39507011 : Blo 1709055 39507011 := bstep (se 1 (by rfl) ⟨29630258, by rfl⟩ : syracuseStep 39507011 = 59260517) B59260517
theorem B1709135 : Blo 1709055 1709135 := bstep (se 1 (by rfl) ⟨1281851, by rfl⟩ : syracuseStep 1709135 = 2563703) B2563703
theorem B3847247 : Blo 1709055 3847247 := bstep (se 1 (by rfl) ⟨2885435, by rfl⟩ : syracuseStep 3847247 = 5770871) B5770871
theorem B7803983 : Blo 1709055 7803983 := bstep (se 1 (by rfl) ⟨5852987, by rfl⟩ : syracuseStep 7803983 = 11705975) B11705975
theorem B1709151 : Blo 1709055 1709151 := bstep (se 1 (by rfl) ⟨1281863, by rfl⟩ : syracuseStep 1709151 = 2563727) B2563727
theorem B1709179 : Blo 1709055 1709179 := bstep (se 1 (by rfl) ⟨1281884, by rfl⟩ : syracuseStep 1709179 = 2563769) B2563769
theorem B6493355 : Blo 1709055 6493355 := bstep (se 1 (by rfl) ⟨4870016, by rfl⟩ : syracuseStep 6493355 = 9740033) B9740033
theorem B1709231 : Blo 1709055 1709231 := bstep (se 1 (by rfl) ⟨1281923, by rfl⟩ : syracuseStep 1709231 = 2563847) B2563847
theorem B1709255 : Blo 1709055 1709255 := bstep (se 1 (by rfl) ⟨1281941, by rfl⟩ : syracuseStep 1709255 = 2563883) B2563883
theorem B1709275 : Blo 1709055 1709275 := bstep (se 1 (by rfl) ⟨1281956, by rfl⟩ : syracuseStep 1709275 = 2563913) B2563913
theorem B1709351 : Blo 1709055 1709351 := bstep (se 1 (by rfl) ⟨1282013, by rfl⟩ : syracuseStep 1709351 = 2564027) B2564027
theorem B1709391 : Blo 1709055 1709391 := bstep (se 1 (by rfl) ⟨1282043, by rfl⟩ : syracuseStep 1709391 = 2564087) B2564087
theorem B1709407 : Blo 1709055 1709407 := bstep (se 1 (by rfl) ⟨1282055, by rfl⟩ : syracuseStep 1709407 = 2564111) B2564111
theorem B1709435 : Blo 1709055 1709435 := bstep (se 1 (by rfl) ⟨1282076, by rfl⟩ : syracuseStep 1709435 = 2564153) B2564153
theorem B1709487 : Blo 1709055 1709487 := bstep (se 1 (by rfl) ⟨1282115, by rfl⟩ : syracuseStep 1709487 = 2564231) B2564231
theorem B1709511 : Blo 1709055 1709511 := bstep (se 1 (by rfl) ⟨1282133, by rfl⟩ : syracuseStep 1709511 = 2564267) B2564267
theorem B1709531 : Blo 1709055 1709531 := bstep (se 1 (by rfl) ⟨1282148, by rfl⟩ : syracuseStep 1709531 = 2564297) B2564297
theorem B3847643 : Blo 1709055 3847643 := bstep (se 1 (by rfl) ⟨2885732, by rfl⟩ : syracuseStep 3847643 = 5771465) B5771465
theorem B1709607 : Blo 1709055 1709607 := bstep (se 1 (by rfl) ⟨1282205, by rfl⟩ : syracuseStep 1709607 = 2564411) B2564411
theorem B1709647 : Blo 1709055 1709647 := bstep (se 1 (by rfl) ⟨1282235, by rfl⟩ : syracuseStep 1709647 = 2564471) B2564471
theorem B1709663 : Blo 1709055 1709663 := bstep (se 1 (by rfl) ⟨1282247, by rfl⟩ : syracuseStep 1709663 = 2564495) B2564495
theorem B1709691 : Blo 1709055 1709691 := bstep (se 1 (by rfl) ⟨1282268, by rfl⟩ : syracuseStep 1709691 = 2564537) B2564537
theorem B5772923 : Blo 1709055 5772923 := bstep (se 1 (by rfl) ⟨4329692, by rfl⟩ : syracuseStep 5772923 = 8659385) B8659385
theorem B1709743 : Blo 1709055 1709743 := bstep (se 1 (by rfl) ⟨1282307, by rfl⟩ : syracuseStep 1709743 = 2564615) B2564615
theorem B1709767 : Blo 1709055 1709767 := bstep (se 1 (by rfl) ⟨1282325, by rfl⟩ : syracuseStep 1709767 = 2564651) B2564651
theorem B1709787 : Blo 1709055 1709787 := bstep (se 1 (by rfl) ⟨1282340, by rfl⟩ : syracuseStep 1709787 = 2564681) B2564681
theorem B10540793 : Blo 1709055 10540793 := bstep (se 2 (by rfl) ⟨3952797, by rfl⟩ : syracuseStep 10540793 = 7905595) B7905595
theorem B21919481 : Blo 1709055 21919481 := bstep (se 2 (by rfl) ⟨8219805, by rfl⟩ : syracuseStep 21919481 = 16439611) B16439611
theorem B5773085 : Blo 1709055 5773085 := bstep (se 3 (by rfl) ⟨1082453, by rfl⟩ : syracuseStep 5773085 = 2164907) B2164907
theorem B1709863 : Blo 1709055 1709863 := bstep (se 1 (by rfl) ⟨1282397, by rfl⟩ : syracuseStep 1709863 = 2564795) B2564795
theorem B1709903 : Blo 1709055 1709903 := bstep (se 1 (by rfl) ⟨1282427, by rfl⟩ : syracuseStep 1709903 = 2564855) B2564855
theorem B1709919 : Blo 1709055 1709919 := bstep (se 1 (by rfl) ⟨1282439, by rfl⟩ : syracuseStep 1709919 = 2564879) B2564879
theorem B1709947 : Blo 1709055 1709947 := bstep (se 1 (by rfl) ⟨1282460, by rfl⟩ : syracuseStep 1709947 = 2564921) B2564921
theorem B1709999 : Blo 1709055 1709999 := bstep (se 1 (by rfl) ⟨1282499, by rfl⟩ : syracuseStep 1709999 = 2564999) B2564999
theorem B3848111 : Blo 1709055 3848111 := bstep (se 1 (by rfl) ⟨2886083, by rfl⟩ : syracuseStep 3848111 = 5772167) B5772167
theorem B1710023 : Blo 1709055 1710023 := bstep (se 1 (by rfl) ⟨1282517, by rfl⟩ : syracuseStep 1710023 = 2565035) B2565035
theorem B1710043 : Blo 1709055 1710043 := bstep (se 1 (by rfl) ⟨1282532, by rfl⟩ : syracuseStep 1710043 = 2565065) B2565065
theorem B6584321 : Blo 1709055 6584321 := bstep (se 2 (by rfl) ⟨2469120, by rfl⟩ : syracuseStep 6584321 = 4938241) B4938241
theorem B13867037 : Blo 1709055 13867037 := bstep (se 3 (by rfl) ⟨2600069, by rfl⟩ : syracuseStep 13867037 = 5200139) B5200139
theorem B1710119 : Blo 1709055 1710119 := bstep (se 1 (by rfl) ⟨1282589, by rfl⟩ : syracuseStep 1710119 = 2565179) B2565179
theorem B1923151 : Blo 1709055 1923151 := bstep (se 1 (by rfl) ⟨1442363, by rfl⟩ : syracuseStep 1923151 = 2884727) B2884727
theorem B1710159 : Blo 1709055 1710159 := bstep (se 1 (by rfl) ⟨1282619, by rfl⟩ : syracuseStep 1710159 = 2565239) B2565239
theorem B1710175 : Blo 1709055 1710175 := bstep (se 1 (by rfl) ⟨1282631, by rfl⟩ : syracuseStep 1710175 = 2565263) B2565263
theorem B1710203 : Blo 1709055 1710203 := bstep (se 1 (by rfl) ⟨1282652, by rfl⟩ : syracuseStep 1710203 = 2565305) B2565305
theorem B8673437 : Blo 1709055 8673437 := bstep (se 3 (by rfl) ⟨1626269, by rfl⟩ : syracuseStep 8673437 = 3252539) B3252539
theorem B3848363 : Blo 1709055 3848363 := bstep (se 1 (by rfl) ⟨2886272, by rfl⟩ : syracuseStep 3848363 = 5772545) B5772545
theorem B1710255 : Blo 1709055 1710255 := bstep (se 1 (by rfl) ⟨1282691, by rfl⟩ : syracuseStep 1710255 = 2565383) B2565383
theorem B1710279 : Blo 1709055 1710279 := bstep (se 1 (by rfl) ⟨1282709, by rfl⟩ : syracuseStep 1710279 = 2565419) B2565419
theorem B1710299 : Blo 1709055 1710299 := bstep (se 1 (by rfl) ⟨1282724, by rfl⟩ : syracuseStep 1710299 = 2565449) B2565449
theorem B1710375 : Blo 1709055 1710375 := bstep (se 1 (by rfl) ⟨1282781, by rfl⟩ : syracuseStep 1710375 = 2565563) B2565563
theorem B6494525 : Blo 1709055 6494525 := bstep (se 3 (by rfl) ⟨1217723, by rfl⟩ : syracuseStep 6494525 = 2435447) B2435447
theorem B1710415 : Blo 1709055 1710415 := bstep (se 1 (by rfl) ⟨1282811, by rfl⟩ : syracuseStep 1710415 = 2565623) B2565623
theorem B1710431 : Blo 1709055 1710431 := bstep (se 1 (by rfl) ⟨1282823, by rfl⟩ : syracuseStep 1710431 = 2565647) B2565647
theorem B1710459 : Blo 1709055 1710459 := bstep (se 1 (by rfl) ⟨1282844, by rfl⟩ : syracuseStep 1710459 = 2565689) B2565689
theorem B3651983 : Blo 1709055 3651983 := bstep (se 1 (by rfl) ⟨2738987, by rfl⟩ : syracuseStep 3651983 = 5477975) B5477975
theorem B1710511 : Blo 1709055 1710511 := bstep (se 1 (by rfl) ⟨1282883, by rfl⟩ : syracuseStep 1710511 = 2565767) B2565767
theorem B1710535 : Blo 1709055 1710535 := bstep (se 1 (by rfl) ⟨1282901, by rfl⟩ : syracuseStep 1710535 = 2565803) B2565803
theorem B1923547 : Blo 1709055 1923547 := bstep (se 1 (by rfl) ⟨1442660, by rfl⟩ : syracuseStep 1923547 = 2885321) B2885321
theorem B1710555 : Blo 1709055 1710555 := bstep (se 1 (by rfl) ⟨1282916, by rfl⟩ : syracuseStep 1710555 = 2565833) B2565833
theorem B5773787 : Blo 1709055 5773787 := bstep (se 1 (by rfl) ⟨4330340, by rfl⟩ : syracuseStep 5773787 = 8660681) B8660681
theorem B11860505 : Blo 1709055 11860505 := bstep (se 2 (by rfl) ⟨4447689, by rfl⟩ : syracuseStep 11860505 = 8895379) B8895379
theorem B8657441 : Blo 1709055 8657441 := bstep (se 2 (by rfl) ⟨3246540, by rfl⟩ : syracuseStep 8657441 = 6493081) B6493081
theorem B1710631 : Blo 1709055 1710631 := bstep (se 1 (by rfl) ⟨1282973, by rfl⟩ : syracuseStep 1710631 = 2565947) B2565947
theorem B1710671 : Blo 1709055 1710671 := bstep (se 1 (by rfl) ⟨1283003, by rfl⟩ : syracuseStep 1710671 = 2566007) B2566007
theorem B1710687 : Blo 1709055 1710687 := bstep (se 1 (by rfl) ⟨1283015, by rfl⟩ : syracuseStep 1710687 = 2566031) B2566031
theorem B3897953 : Blo 1709055 3897953 := bstep (se 2 (by rfl) ⟨1461732, by rfl⟩ : syracuseStep 3897953 = 2923465) B2923465
theorem B6494843 : Blo 1709055 6494843 := bstep (se 1 (by rfl) ⟨4871132, by rfl⟩ : syracuseStep 6494843 = 9742265) B9742265
theorem B1710715 : Blo 1709055 1710715 := bstep (se 1 (by rfl) ⟨1283036, by rfl⟩ : syracuseStep 1710715 = 2566073) B2566073
theorem B1710767 : Blo 1709055 1710767 := bstep (se 1 (by rfl) ⟨1283075, by rfl⟩ : syracuseStep 1710767 = 2566151) B2566151
theorem B3848903 : Blo 1709055 3848903 := bstep (se 1 (by rfl) ⟨2886677, by rfl⟩ : syracuseStep 3848903 = 5773355) B5773355
theorem B1710791 : Blo 1709055 1710791 := bstep (se 1 (by rfl) ⟨1283093, by rfl⟩ : syracuseStep 1710791 = 2566187) B2566187
theorem B1710811 : Blo 1709055 1710811 := bstep (se 1 (by rfl) ⟨1283108, by rfl⟩ : syracuseStep 1710811 = 2566217) B2566217
theorem B1710887 : Blo 1709055 1710887 := bstep (se 1 (by rfl) ⟨1283165, by rfl⟩ : syracuseStep 1710887 = 2566331) B2566331
theorem B3291977 : Blo 1709055 3291977 := bstep (se 2 (by rfl) ⟨1234491, by rfl⟩ : syracuseStep 3291977 = 2468983) B2468983
theorem B1710927 : Blo 1709055 1710927 := bstep (se 1 (by rfl) ⟨1283195, by rfl⟩ : syracuseStep 1710927 = 2566391) B2566391
theorem B1710943 : Blo 1709055 1710943 := bstep (se 1 (by rfl) ⟨1283207, by rfl⟩ : syracuseStep 1710943 = 2566415) B2566415
theorem B1710971 : Blo 1709055 1710971 := bstep (se 1 (by rfl) ⟨1283228, by rfl⟩ : syracuseStep 1710971 = 2566457) B2566457
theorem B1924015 : Blo 1709055 1924015 := bstep (se 1 (by rfl) ⟨1443011, by rfl⟩ : syracuseStep 1924015 = 2886023) B2886023
theorem B1711023 : Blo 1709055 1711023 := bstep (se 1 (by rfl) ⟨1283267, by rfl⟩ : syracuseStep 1711023 = 2566535) B2566535
theorem B1711047 : Blo 1709055 1711047 := bstep (se 1 (by rfl) ⟨1283285, by rfl⟩ : syracuseStep 1711047 = 2566571) B2566571
theorem B5774489 : Blo 1709055 5774489 := bstep (se 2 (by rfl) ⟨2165433, by rfl⟩ : syracuseStep 5774489 = 4330867) B4330867
theorem B12983489 : Blo 1709055 12983489 := bstep (se 2 (by rfl) ⟨4868808, by rfl⟩ : syracuseStep 12983489 = 9737617) B9737617
theorem B23387429 : Blo 1709055 23387429 := bstep (se 4 (by rfl) ⟨2192571, by rfl⟩ : syracuseStep 23387429 = 4385143) B4385143
theorem B1924447 : Blo 1709055 1924447 := bstep (se 1 (by rfl) ⟨1443335, by rfl⟩ : syracuseStep 1924447 = 2886671) B2886671
theorem B2924039 : Blo 1709055 2924039 := bstep (se 1 (by rfl) ⟨2193029, by rfl⟩ : syracuseStep 2924039 = 4386059) B4386059
theorem B3849767 : Blo 1709055 3849767 := bstep (se 1 (by rfl) ⟨2887325, by rfl⟩ : syracuseStep 3849767 = 5774651) B5774651
theorem B8330941 : Blo 1709055 8330941 := bstep (se 3 (by rfl) ⟨1562051, by rfl⟩ : syracuseStep 8330941 = 3124103) B3124103
theorem B1924807 : Blo 1709055 1924807 := bstep (se 1 (by rfl) ⟨1443605, by rfl⟩ : syracuseStep 1924807 = 2887211) B2887211
theorem B12992237 : Blo 1709055 12992237 := bstep (se 3 (by rfl) ⟨2436044, by rfl⟩ : syracuseStep 12992237 = 4872089) B4872089
theorem B6160157 : Blo 1709055 6160157 := bstep (se 3 (by rfl) ⟨1155029, by rfl⟩ : syracuseStep 6160157 = 2310059) B2310059
theorem B2564015 : Blo 1709055 2564015 := bstep (se 1 (by rfl) ⟨1923011, by rfl⟩ : syracuseStep 2564015 = 3846023) B3846023
theorem B32866235 : Blo 1709055 32866235 := bstep (se 1 (by rfl) ⟨24649676, by rfl⟩ : syracuseStep 32866235 = 49299353) B49299353
theorem B2564201 : Blo 1709055 2564201 := bstep (se 2 (by rfl) ⟨961575, by rfl⟩ : syracuseStep 2564201 = 1923151) B1923151
theorem B7307435 : Blo 1709055 7307435 := bstep (se 1 (by rfl) ⟨5480576, by rfl⟩ : syracuseStep 7307435 = 10961153) B10961153
theorem B12992723 : Blo 1709055 12992723 := bstep (se 1 (by rfl) ⟨9744542, by rfl⟩ : syracuseStep 12992723 = 19489085) B19489085
theorem B27746651 : Blo 1709055 27746651 := bstep (se 1 (by rfl) ⟨20809988, by rfl⟩ : syracuseStep 27746651 = 41619977) B41619977
theorem B4686191 : Blo 1709055 4686191 := bstep (se 1 (by rfl) ⟨3514643, by rfl⟩ : syracuseStep 4686191 = 7029287) B7029287
theorem B3653999 : Blo 1709055 3653999 := bstep (se 1 (by rfl) ⟨2740499, by rfl⟩ : syracuseStep 3653999 = 5480999) B5480999
theorem B2564519 : Blo 1709055 2564519 := bstep (se 1 (by rfl) ⟨1923389, by rfl⟩ : syracuseStep 2564519 = 3846779) B3846779
theorem B2564603 : Blo 1709055 2564603 := bstep (se 1 (by rfl) ⟨1923452, by rfl⟩ : syracuseStep 2564603 = 3846905) B3846905
theorem B2564729 : Blo 1709055 2564729 := bstep (se 2 (by rfl) ⟨961773, by rfl⟩ : syracuseStep 2564729 = 1923547) B1923547
theorem B8217233 : Blo 1709055 8217233 := bstep (se 2 (by rfl) ⟨3081462, by rfl⟩ : syracuseStep 8217233 = 6162925) B6162925
theorem B2564783 : Blo 1709055 2564783 := bstep (se 1 (by rfl) ⟨1923587, by rfl⟩ : syracuseStep 2564783 = 3847175) B3847175
theorem B26338007 : Blo 1709055 26338007 := bstep (se 1 (by rfl) ⟨19753505, by rfl⟩ : syracuseStep 26338007 = 39507011) B39507011
theorem B2564831 : Blo 1709055 2564831 := bstep (se 1 (by rfl) ⟨1923623, by rfl⟩ : syracuseStep 2564831 = 3847247) B3847247
theorem B66650957 : Blo 1709055 66650957 := bstep (se 3 (by rfl) ⟨12497054, by rfl⟩ : syracuseStep 66650957 = 24994109) B24994109
theorem B4866895 : Blo 1709055 4866895 := bstep (se 1 (by rfl) ⟨3650171, by rfl⟩ : syracuseStep 4866895 = 7300343) B7300343
theorem B2163611 : Blo 1709055 2163611 := bstep (se 1 (by rfl) ⟨1622708, by rfl⟩ : syracuseStep 2163611 = 3245417) B3245417
theorem B2565095 : Blo 1709055 2565095 := bstep (se 1 (by rfl) ⟨1923821, by rfl⟩ : syracuseStep 2565095 = 3847643) B3847643
theorem B2565353 : Blo 1709055 2565353 := bstep (se 2 (by rfl) ⟨962007, by rfl⟩ : syracuseStep 2565353 = 1924015) B1924015
theorem B5768441 : Blo 1709055 5768441 := bstep (se 2 (by rfl) ⟨2163165, by rfl⟩ : syracuseStep 5768441 = 4326331) B4326331
theorem B2565407 : Blo 1709055 2565407 := bstep (se 1 (by rfl) ⟨1924055, by rfl⟩ : syracuseStep 2565407 = 3848111) B3848111
theorem B13157741 : Blo 1709055 13157741 := bstep (se 3 (by rfl) ⟨2467076, by rfl⟩ : syracuseStep 13157741 = 4934153) B4934153
theorem B32867693 : Blo 1709055 32867693 := bstep (se 3 (by rfl) ⟨6162692, by rfl⟩ : syracuseStep 32867693 = 12325385) B12325385
theorem B6489467 : Blo 1709055 6489467 := bstep (se 1 (by rfl) ⟨4867100, by rfl⟩ : syracuseStep 6489467 = 9734201) B9734201
theorem B2311561 : Blo 1709055 2311561 := bstep (se 2 (by rfl) ⟨866835, by rfl⟩ : syracuseStep 2311561 = 1733671) B1733671
theorem B4326817 : Blo 1709055 4326817 := bstep (se 2 (by rfl) ⟨1622556, by rfl⟩ : syracuseStep 4326817 = 3245113) B3245113
theorem B2565575 : Blo 1709055 2565575 := bstep (se 1 (by rfl) ⟨1924181, by rfl⟩ : syracuseStep 2565575 = 3848363) B3848363
theorem B5768711 : Blo 1709055 5768711 := bstep (se 1 (by rfl) ⟨4326533, by rfl⟩ : syracuseStep 5768711 = 8653067) B8653067
theorem B2434655 : Blo 1709055 2434655 := bstep (se 1 (by rfl) ⟨1825991, by rfl⟩ : syracuseStep 2434655 = 3651983) B3651983
theorem B7907003 : Blo 1709055 7907003 := bstep (se 1 (by rfl) ⟨5930252, by rfl⟩ : syracuseStep 7907003 = 11860505) B11860505
theorem B2598635 : Blo 1709055 2598635 := bstep (se 1 (by rfl) ⟨1948976, by rfl⟩ : syracuseStep 2598635 = 3897953) B3897953
theorem B3082025 : Blo 1709055 3082025 := bstep (se 2 (by rfl) ⟨1155759, by rfl⟩ : syracuseStep 3082025 = 2311519) B2311519
theorem B2565929 : Blo 1709055 2565929 := bstep (se 2 (by rfl) ⟨962223, by rfl⟩ : syracuseStep 2565929 = 1924447) B1924447
theorem B2565935 : Blo 1709055 2565935 := bstep (se 1 (by rfl) ⟨1924451, by rfl⟩ : syracuseStep 2565935 = 3848903) B3848903
theorem B2312167 : Blo 1709055 2312167 := bstep (se 1 (by rfl) ⟨1734125, by rfl⟩ : syracuseStep 2312167 = 3468251) B3468251
theorem B9242657 : Blo 1709055 9242657 := bstep (se 2 (by rfl) ⟨3465996, by rfl⟩ : syracuseStep 9242657 = 6931993) B6931993
theorem B15591619 : Blo 1709055 15591619 := bstep (se 1 (by rfl) ⟨11693714, by rfl⟩ : syracuseStep 15591619 = 23387429) B23387429
theorem B2566409 : Blo 1709055 2566409 := bstep (se 2 (by rfl) ⟨962403, by rfl⟩ : syracuseStep 2566409 = 1924807) B1924807
theorem B18483491 : Blo 1709055 18483491 := bstep (se 1 (by rfl) ⟨13862618, by rfl⟩ : syracuseStep 18483491 = 27725237) B27725237
theorem B2566511 : Blo 1709055 2566511 := bstep (se 1 (by rfl) ⟨1924883, by rfl⟩ : syracuseStep 2566511 = 3849767) B3849767
theorem B21088679 : Blo 1709055 21088679 := bstep (se 1 (by rfl) ⟨15816509, by rfl⟩ : syracuseStep 21088679 = 31633019) B31633019
theorem B8653229 : Blo 1709055 8653229 := bstep (se 3 (by rfl) ⟨1622480, by rfl⟩ : syracuseStep 8653229 = 3244961) B3244961
theorem B5769683 : Blo 1709055 5769683 := bstep (se 1 (by rfl) ⟨4327262, by rfl⟩ : syracuseStep 5769683 = 8654525) B8654525
theorem B8661491 : Blo 1709055 8661491 := bstep (se 1 (by rfl) ⟨6496118, by rfl⟩ : syracuseStep 8661491 = 12992237) B12992237
theorem B4327931 : Blo 1709055 4327931 := bstep (se 1 (by rfl) ⟨3245948, by rfl⟩ : syracuseStep 4327931 = 6491897) B6491897
theorem B4106771 : Blo 1709055 4106771 := bstep (se 1 (by rfl) ⟨3080078, by rfl⟩ : syracuseStep 4106771 = 6160157) B6160157
theorem B5769791 : Blo 1709055 5769791 := bstep (se 1 (by rfl) ⟨4327343, by rfl⟩ : syracuseStep 5769791 = 8654687) B8654687
theorem B3246655 : Blo 1709055 3246655 := bstep (se 1 (by rfl) ⟨2434991, by rfl⟩ : syracuseStep 3246655 = 4869983) B4869983
theorem B8653391 : Blo 1709055 8653391 := bstep (se 1 (by rfl) ⟨6490043, by rfl⟩ : syracuseStep 8653391 = 12980087) B12980087
theorem B24644195 : Blo 1709055 24644195 := bstep (se 1 (by rfl) ⟨18483146, by rfl⟩ : syracuseStep 24644195 = 36966293) B36966293
theorem B2886367 : Blo 1709055 2886367 := bstep (se 1 (by rfl) ⟨2164775, by rfl⟩ : syracuseStep 2886367 = 4329551) B4329551
theorem B4868855 : Blo 1709055 4868855 := bstep (se 1 (by rfl) ⟨3651641, by rfl⟩ : syracuseStep 4868855 = 7303283) B7303283
theorem B49310531 : Blo 1709055 49310531 := bstep (se 1 (by rfl) ⟨36982898, by rfl⟩ : syracuseStep 49310531 = 73965797) B73965797
theorem B12331901 : Blo 1709055 12331901 := bstep (se 3 (by rfl) ⟨2312231, by rfl⟩ : syracuseStep 12331901 = 4624463) B4624463
theorem B20810621 : Blo 1709055 20810621 := bstep (se 3 (by rfl) ⟨3901991, by rfl⟩ : syracuseStep 20810621 = 7803983) B7803983
theorem B6163343 : Blo 1709055 6163343 := bstep (se 1 (by rfl) ⟨4622507, by rfl⟩ : syracuseStep 6163343 = 9245015) B9245015
theorem B12979115 : Blo 1709055 12979115 := bstep (se 1 (by rfl) ⟨9734336, by rfl⟩ : syracuseStep 12979115 = 19468673) B19468673
theorem B11406251 : Blo 1709055 11406251 := bstep (se 1 (by rfl) ⟨8554688, by rfl⟩ : syracuseStep 11406251 = 17109377) B17109377
theorem B2739115 : Blo 1709055 2739115 := bstep (se 1 (by rfl) ⟨2054336, by rfl⟩ : syracuseStep 2739115 = 4108673) B4108673
theorem B6491123 : Blo 1709055 6491123 := bstep (se 1 (by rfl) ⟨4868342, by rfl⟩ : syracuseStep 6491123 = 9736685) B9736685
theorem B23129165 : Blo 1709055 23129165 := bstep (se 3 (by rfl) ⟨4336718, by rfl⟩ : syracuseStep 23129165 = 8673437) B8673437
theorem B9874547 : Blo 1709055 9874547 := bstep (se 1 (by rfl) ⟨7405910, by rfl⟩ : syracuseStep 9874547 = 14811821) B14811821
theorem B5475451 : Blo 1709055 5475451 := bstep (se 1 (by rfl) ⟨4106588, by rfl⟩ : syracuseStep 5475451 = 8213177) B8213177
theorem B8662139 : Blo 1709055 8662139 := bstep (se 1 (by rfl) ⟨6496604, by rfl⟩ : syracuseStep 8662139 = 12993209) B12993209
theorem B2886799 : Blo 1709055 2886799 := bstep (se 1 (by rfl) ⟨2165099, by rfl⟩ : syracuseStep 2886799 = 4330199) B4330199
theorem B3247391 : Blo 1709055 3247391 := bstep (se 1 (by rfl) ⟨2435543, by rfl⟩ : syracuseStep 3247391 = 4871087) B4871087
theorem B15592823 : Blo 1709055 15592823 := bstep (se 1 (by rfl) ⟨11694617, by rfl⟩ : syracuseStep 15592823 = 23389235) B23389235
theorem B11414903 : Blo 1709055 11414903 := bstep (se 1 (by rfl) ⟨8561177, by rfl⟩ : syracuseStep 11414903 = 17122355) B17122355
theorem B10546561 : Blo 1709055 10546561 := bstep (se 2 (by rfl) ⟨3954960, by rfl⟩ : syracuseStep 10546561 = 7909921) B7909921
theorem B2887049 : Blo 1709055 2887049 := bstep (se 2 (by rfl) ⟨1082643, by rfl⟩ : syracuseStep 2887049 = 2165287) B2165287
theorem B3845537 : Blo 1709055 3845537 := bstep (se 2 (by rfl) ⟨1442076, by rfl⟩ : syracuseStep 3845537 = 2884153) B2884153
theorem B7302599 : Blo 1709055 7302599 := bstep (se 1 (by rfl) ⟨5476949, by rfl⟩ : syracuseStep 7302599 = 10953899) B10953899
theorem B4328903 : Blo 1709055 4328903 := bstep (se 1 (by rfl) ⟨3246677, by rfl⟩ : syracuseStep 4328903 = 6493355) B6493355
theorem B9244169 : Blo 1709055 9244169 := bstep (se 2 (by rfl) ⟨3466563, by rfl⟩ : syracuseStep 9244169 = 6933127) B6933127
theorem B7401041 : Blo 1709055 7401041 := bstep (se 2 (by rfl) ⟨2775390, by rfl⟩ : syracuseStep 7401041 = 5550781) B5550781
theorem B3846095 : Blo 1709055 3846095 := bstep (se 1 (by rfl) ⟨2884571, by rfl⟩ : syracuseStep 3846095 = 5769143) B5769143
theorem B8654849 : Blo 1709055 8654849 := bstep (se 2 (by rfl) ⟨3245568, by rfl⟩ : syracuseStep 8654849 = 6491137) B6491137
theorem B9244691 : Blo 1709055 9244691 := bstep (se 1 (by rfl) ⟨6933518, by rfl⟩ : syracuseStep 9244691 = 13867037) B13867037
theorem B4329683 : Blo 1709055 4329683 := bstep (se 1 (by rfl) ⟨3247262, by rfl⟩ : syracuseStep 4329683 = 6494525) B6494525
theorem B3846473 : Blo 1709055 3846473 := bstep (se 2 (by rfl) ⟨1442427, by rfl⟩ : syracuseStep 3846473 = 2884855) B2884855
theorem B3846491 : Blo 1709055 3846491 := bstep (se 1 (by rfl) ⟨2884868, by rfl⟩ : syracuseStep 3846491 = 5769737) B5769737
theorem B5771627 : Blo 1709055 5771627 := bstep (se 1 (by rfl) ⟨4328720, by rfl⟩ : syracuseStep 5771627 = 8657441) B8657441
theorem B4329895 : Blo 1709055 4329895 := bstep (se 1 (by rfl) ⟨3247421, by rfl⟩ : syracuseStep 4329895 = 6494843) B6494843
theorem B4108819 : Blo 1709055 4108819 := bstep (se 1 (by rfl) ⟨3081614, by rfl⟩ : syracuseStep 4108819 = 6163229) B6163229
theorem B4330057 : Blo 1709055 4330057 := bstep (se 2 (by rfl) ⟨1623771, by rfl⟩ : syracuseStep 4330057 = 3247543) B3247543
theorem B5771897 : Blo 1709055 5771897 := bstep (se 2 (by rfl) ⟨2164461, by rfl⟩ : syracuseStep 5771897 = 4328923) B4328923
theorem B8655659 : Blo 1709055 8655659 := bstep (se 1 (by rfl) ⟨6491744, by rfl⟩ : syracuseStep 8655659 = 12983489) B12983489
theorem B3847067 : Blo 1709055 3847067 := bstep (se 1 (by rfl) ⟨2885300, by rfl⟩ : syracuseStep 3847067 = 5770601) B5770601
theorem B3650599 : Blo 1709055 3650599 := bstep (se 1 (by rfl) ⟨2737949, by rfl⟩ : syracuseStep 3650599 = 5475899) B5475899
theorem B3847265 : Blo 1709055 3847265 := bstep (se 2 (by rfl) ⟨1442724, by rfl⟩ : syracuseStep 3847265 = 2885449) B2885449
theorem B10957949 : Blo 1709055 10957949 := bstep (se 3 (by rfl) ⟨2054615, by rfl⟩ : syracuseStep 10957949 = 4109231) B4109231
theorem B1709343 : Blo 1709055 1709343 := bstep (se 1 (by rfl) ⟨1282007, by rfl⟩ : syracuseStep 1709343 = 2564015) B2564015
theorem B21910823 : Blo 1709055 21910823 := bstep (se 1 (by rfl) ⟨16433117, by rfl⟩ : syracuseStep 21910823 = 32866235) B32866235
theorem B3847463 : Blo 1709055 3847463 := bstep (se 1 (by rfl) ⟨2885597, by rfl⟩ : syracuseStep 3847463 = 5771195) B5771195
theorem B1709403 : Blo 1709055 1709403 := bstep (se 1 (by rfl) ⟨1282052, by rfl⟩ : syracuseStep 1709403 = 2564105) B2564105
theorem B4330847 : Blo 1709055 4330847 := bstep (se 1 (by rfl) ⟨3248135, by rfl⟩ : syracuseStep 4330847 = 6496271) B6496271
theorem B1709423 : Blo 1709055 1709423 := bstep (se 1 (by rfl) ⟨1282067, by rfl⟩ : syracuseStep 1709423 = 2564135) B2564135
theorem B1709479 : Blo 1709055 1709479 := bstep (se 1 (by rfl) ⟨1282109, by rfl⟩ : syracuseStep 1709479 = 2564219) B2564219
theorem B1709563 : Blo 1709055 1709563 := bstep (se 1 (by rfl) ⟨1282172, by rfl⟩ : syracuseStep 1709563 = 2564345) B2564345
theorem B1709631 : Blo 1709055 1709631 := bstep (se 1 (by rfl) ⟨1282223, by rfl⟩ : syracuseStep 1709631 = 2564447) B2564447
theorem B1709639 : Blo 1709055 1709639 := bstep (se 1 (by rfl) ⟨1282229, by rfl⟩ : syracuseStep 1709639 = 2564459) B2564459
theorem B3847841 : Blo 1709055 3847841 := bstep (se 2 (by rfl) ⟨1442940, by rfl⟩ : syracuseStep 3847841 = 2885881) B2885881
theorem B1709791 : Blo 1709055 1709791 := bstep (se 1 (by rfl) ⟨1282343, by rfl⟩ : syracuseStep 1709791 = 2564687) B2564687
theorem B1922863 : Blo 1709055 1922863 := bstep (se 1 (by rfl) ⟨1442147, by rfl⟩ : syracuseStep 1922863 = 2884295) B2884295
theorem B1709871 : Blo 1709055 1709871 := bstep (se 1 (by rfl) ⟨1282403, by rfl⟩ : syracuseStep 1709871 = 2564807) B2564807
theorem B6494039 : Blo 1709055 6494039 := bstep (se 1 (by rfl) ⟨4870529, by rfl⟩ : syracuseStep 6494039 = 9741059) B9741059
theorem B1922971 : Blo 1709055 1922971 := bstep (se 1 (by rfl) ⟨1442228, by rfl⟩ : syracuseStep 1922971 = 2884457) B2884457
theorem B1709979 : Blo 1709055 1709979 := bstep (se 1 (by rfl) ⟨1282484, by rfl⟩ : syracuseStep 1709979 = 2564969) B2564969
theorem B4683677 : Blo 1709055 4683677 := bstep (se 3 (by rfl) ⟨878189, by rfl⟩ : syracuseStep 4683677 = 1756379) B1756379
theorem B1710031 : Blo 1709055 1710031 := bstep (se 1 (by rfl) ⟨1282523, by rfl⟩ : syracuseStep 1710031 = 2565047) B2565047
theorem B118396889 : Blo 1709055 118396889 := bstep (se 2 (by rfl) ⟨44398833, by rfl⟩ : syracuseStep 118396889 = 88797667) B88797667
theorem B1710055 : Blo 1709055 1710055 := bstep (se 1 (by rfl) ⟨1282541, by rfl⟩ : syracuseStep 1710055 = 2565083) B2565083
theorem B3848201 : Blo 1709055 3848201 := bstep (se 2 (by rfl) ⟨1443075, by rfl⟩ : syracuseStep 3848201 = 2886151) B2886151
theorem B13867289 : Blo 1709055 13867289 := bstep (se 2 (by rfl) ⟨5200233, by rfl⟩ : syracuseStep 13867289 = 10400467) B10400467
theorem B1710367 : Blo 1709055 1710367 := bstep (se 1 (by rfl) ⟨1282775, by rfl⟩ : syracuseStep 1710367 = 2565551) B2565551
theorem B1923367 : Blo 1709055 1923367 := bstep (se 1 (by rfl) ⟨1442525, by rfl⟩ : syracuseStep 1923367 = 2885051) B2885051
theorem B44431685 : Blo 1709055 44431685 := bstep (se 4 (by rfl) ⟨4165470, by rfl⟩ : syracuseStep 44431685 = 8330941) B8330941
theorem B1710427 : Blo 1709055 1710427 := bstep (se 1 (by rfl) ⟨1282820, by rfl⟩ : syracuseStep 1710427 = 2565641) B2565641
theorem B1923439 : Blo 1709055 1923439 := bstep (se 1 (by rfl) ⟨1442579, by rfl⟩ : syracuseStep 1923439 = 2885159) B2885159
theorem B1710447 : Blo 1709055 1710447 := bstep (se 1 (by rfl) ⟨1282835, by rfl⟩ : syracuseStep 1710447 = 2565671) B2565671
theorem B5773679 : Blo 1709055 5773679 := bstep (se 1 (by rfl) ⟨4330259, by rfl⟩ : syracuseStep 5773679 = 8660519) B8660519
theorem B2054567 : Blo 1709055 2054567 := bstep (se 1 (by rfl) ⟨1540925, by rfl⟩ : syracuseStep 2054567 = 3081851) B3081851
theorem B3848615 : Blo 1709055 3848615 := bstep (se 1 (by rfl) ⟨2886461, by rfl⟩ : syracuseStep 3848615 = 5772923) B5772923
theorem B1710503 : Blo 1709055 1710503 := bstep (se 1 (by rfl) ⟨1282877, by rfl⟩ : syracuseStep 1710503 = 2565755) B2565755
theorem B7027195 : Blo 1709055 7027195 := bstep (se 1 (by rfl) ⟨5270396, by rfl⟩ : syracuseStep 7027195 = 10540793) B10540793
theorem B14612987 : Blo 1709055 14612987 := bstep (se 1 (by rfl) ⟨10959740, by rfl⟩ : syracuseStep 14612987 = 21919481) B21919481
theorem B1710587 : Blo 1709055 1710587 := bstep (se 1 (by rfl) ⟨1282940, by rfl⟩ : syracuseStep 1710587 = 2565881) B2565881
theorem B3848723 : Blo 1709055 3848723 := bstep (se 1 (by rfl) ⟨2886542, by rfl⟩ : syracuseStep 3848723 = 5773085) B5773085
theorem B1710655 : Blo 1709055 1710655 := bstep (se 1 (by rfl) ⟨1282991, by rfl⟩ : syracuseStep 1710655 = 2565983) B2565983
theorem B1923655 : Blo 1709055 1923655 := bstep (se 1 (by rfl) ⟨1442741, by rfl⟩ : syracuseStep 1923655 = 2885483) B2885483
theorem B3848777 : Blo 1709055 3848777 := bstep (se 2 (by rfl) ⟨1443291, by rfl⟩ : syracuseStep 3848777 = 2886583) B2886583
theorem B1710663 : Blo 1709055 1710663 := bstep (se 1 (by rfl) ⟨1282997, by rfl⟩ : syracuseStep 1710663 = 2565995) B2565995
theorem B4389547 : Blo 1709055 4389547 := bstep (se 1 (by rfl) ⟨3292160, by rfl⟩ : syracuseStep 4389547 = 6584321) B6584321
theorem B8657603 : Blo 1709055 8657603 := bstep (se 1 (by rfl) ⟨6493202, by rfl⟩ : syracuseStep 8657603 = 12986405) B12986405
theorem B1710815 : Blo 1709055 1710815 := bstep (se 1 (by rfl) ⟨1283111, by rfl⟩ : syracuseStep 1710815 = 2566223) B2566223
theorem B1710895 : Blo 1709055 1710895 := bstep (se 1 (by rfl) ⟨1283171, by rfl⟩ : syracuseStep 1710895 = 2566343) B2566343
theorem B1711003 : Blo 1709055 1711003 := bstep (se 1 (by rfl) ⟨1283252, by rfl⟩ : syracuseStep 1711003 = 2566505) B2566505
theorem B1711055 : Blo 1709055 1711055 := bstep (se 1 (by rfl) ⟨1283291, by rfl⟩ : syracuseStep 1711055 = 2566583) B2566583
theorem B3849191 : Blo 1709055 3849191 := bstep (se 1 (by rfl) ⟨2886893, by rfl⟩ : syracuseStep 3849191 = 5773787) B5773787
theorem B2194651 : Blo 1709055 2194651 := bstep (se 1 (by rfl) ⟨1645988, by rfl⟩ : syracuseStep 2194651 = 3291977) B3291977
theorem B3849569 : Blo 1709055 3849569 := bstep (se 2 (by rfl) ⟨1443588, by rfl⟩ : syracuseStep 3849569 = 2887177) B2887177
theorem B1924519 : Blo 1709055 1924519 := bstep (se 1 (by rfl) ⟨1443389, by rfl⟩ : syracuseStep 1924519 = 2886779) B2886779
theorem B3849659 : Blo 1709055 3849659 := bstep (se 1 (by rfl) ⟨2887244, by rfl⟩ : syracuseStep 3849659 = 5774489) B5774489
theorem B3849785 : Blo 1709055 3849785 := bstep (se 2 (by rfl) ⟨1443669, by rfl⟩ : syracuseStep 3849785 = 2887339) B2887339
theorem B2563679 : Blo 1709055 2563679 := bstep (se 1 (by rfl) ⟨1922759, by rfl⟩ : syracuseStep 2563679 = 3845519) B3845519
theorem B1949359 : Blo 1709055 1949359 := bstep (se 1 (by rfl) ⟨1462019, by rfl⟩ : syracuseStep 1949359 = 2924039) B2924039
theorem B41606945 : Blo 1709055 41606945 := bstep (se 2 (by rfl) ⟨15602604, by rfl⟩ : syracuseStep 41606945 = 31205209) B31205209
theorem B2563895 : Blo 1709055 2563895 := bstep (se 1 (by rfl) ⟨1922921, by rfl⟩ : syracuseStep 2563895 = 3845843) B3845843
theorem B14606153 : Blo 1709055 14606153 := bstep (se 2 (by rfl) ⟨5477307, by rfl⟩ : syracuseStep 14606153 = 10954615) B10954615
theorem B2564315 : Blo 1709055 2564315 := bstep (se 1 (by rfl) ⟨1923236, by rfl⟩ : syracuseStep 2564315 = 3846473) B3846473
theorem B2564327 : Blo 1709055 2564327 := bstep (se 1 (by rfl) ⟨1923245, by rfl⟩ : syracuseStep 2564327 = 3846491) B3846491
theorem B18497767 : Blo 1709055 18497767 := bstep (se 1 (by rfl) ⟨13873325, by rfl⟩ : syracuseStep 18497767 = 27746651) B27746651
theorem B2564489 : Blo 1709055 2564489 := bstep (se 2 (by rfl) ⟨961683, by rfl⟩ : syracuseStep 2564489 = 1923367) B1923367
theorem B2564585 : Blo 1709055 2564585 := bstep (se 2 (by rfl) ⟨961719, by rfl⟩ : syracuseStep 2564585 = 1923439) B1923439
theorem B44433971 : Blo 1709055 44433971 := bstep (se 1 (by rfl) ⟨33325478, by rfl⟩ : syracuseStep 44433971 = 66650957) B66650957
theorem B2564711 : Blo 1709055 2564711 := bstep (se 1 (by rfl) ⟨1923533, by rfl⟩ : syracuseStep 2564711 = 3847067) B3847067
theorem B2564843 : Blo 1709055 2564843 := bstep (se 1 (by rfl) ⟨1923632, by rfl⟩ : syracuseStep 2564843 = 3847265) B3847265
theorem B8659709 : Blo 1709055 8659709 := bstep (se 3 (by rfl) ⟨1623695, by rfl⟩ : syracuseStep 8659709 = 3247391) B3247391
theorem B2564873 : Blo 1709055 2564873 := bstep (se 2 (by rfl) ⟨961827, by rfl⟩ : syracuseStep 2564873 = 1923655) B1923655
theorem B14607215 : Blo 1709055 14607215 := bstep (se 1 (by rfl) ⟨10955411, by rfl⟩ : syracuseStep 14607215 = 21910823) B21910823
theorem B2564975 : Blo 1709055 2564975 := bstep (se 1 (by rfl) ⟨1923731, by rfl⟩ : syracuseStep 2564975 = 3847463) B3847463
theorem B4326311 : Blo 1709055 4326311 := bstep (se 1 (by rfl) ⟨3244733, by rfl⟩ : syracuseStep 4326311 = 6489467) B6489467
theorem B6489193 : Blo 1709055 6489193 := bstep (se 2 (by rfl) ⟨2433447, by rfl⟩ : syracuseStep 6489193 = 4866895) B4866895
theorem B2565227 : Blo 1709055 2565227 := bstep (se 1 (by rfl) ⟨1923920, by rfl⟩ : syracuseStep 2565227 = 3847841) B3847841
theorem B78931259 : Blo 1709055 78931259 := bstep (se 1 (by rfl) ⟨59198444, by rfl⟩ : syracuseStep 78931259 = 118396889) B118396889
theorem B2565467 : Blo 1709055 2565467 := bstep (se 1 (by rfl) ⟨1924100, by rfl⟩ : syracuseStep 2565467 = 3848201) B3848201
theorem B6161771 : Blo 1709055 6161771 := bstep (se 1 (by rfl) ⟨4621328, by rfl⟩ : syracuseStep 6161771 = 9242657) B9242657
theorem B4867465 : Blo 1709055 4867465 := bstep (se 2 (by rfl) ⟨1825299, by rfl⟩ : syracuseStep 4867465 = 3650599) B3650599
theorem B7300601 : Blo 1709055 7300601 := bstep (se 2 (by rfl) ⟨2737725, by rfl⟩ : syracuseStep 7300601 = 5475451) B5475451
theorem B2565743 : Blo 1709055 2565743 := bstep (se 1 (by rfl) ⟨1924307, by rfl⟩ : syracuseStep 2565743 = 3848615) B3848615
theorem B5768819 : Blo 1709055 5768819 := bstep (se 1 (by rfl) ⟨4326614, by rfl⟩ : syracuseStep 5768819 = 8653229) B8653229
theorem B2926201 : Blo 1709055 2926201 := bstep (se 2 (by rfl) ⟨1097325, by rfl⟩ : syracuseStep 2926201 = 2194651) B2194651
theorem B2885287 : Blo 1709055 2885287 := bstep (se 1 (by rfl) ⟨2163965, by rfl⟩ : syracuseStep 2885287 = 4327931) B4327931
theorem B9741991 : Blo 1709055 9741991 := bstep (se 1 (by rfl) ⟨7306493, by rfl⟩ : syracuseStep 9741991 = 14612987) B14612987
theorem B2737847 : Blo 1709055 2737847 := bstep (se 1 (by rfl) ⟨2053385, by rfl⟩ : syracuseStep 2737847 = 4106771) B4106771
theorem B2565815 : Blo 1709055 2565815 := bstep (se 1 (by rfl) ⟨1924361, by rfl⟩ : syracuseStep 2565815 = 3848723) B3848723
theorem B2565851 : Blo 1709055 2565851 := bstep (se 1 (by rfl) ⟨1924388, by rfl⟩ : syracuseStep 2565851 = 3848777) B3848777
theorem B5768927 : Blo 1709055 5768927 := bstep (se 1 (by rfl) ⟨4326695, by rfl⟩ : syracuseStep 5768927 = 8653391) B8653391
theorem B3245903 : Blo 1709055 3245903 := bstep (se 1 (by rfl) ⟨2434427, by rfl⟩ : syracuseStep 3245903 = 4868855) B4868855
theorem B5769089 : Blo 1709055 5769089 := bstep (se 2 (by rfl) ⟨2163408, by rfl⟩ : syracuseStep 5769089 = 4326817) B4326817
theorem B2566025 : Blo 1709055 2566025 := bstep (se 2 (by rfl) ⟨962259, by rfl⟩ : syracuseStep 2566025 = 1924519) B1924519
theorem B8652743 : Blo 1709055 8652743 := bstep (se 1 (by rfl) ⟨6489557, by rfl⟩ : syracuseStep 8652743 = 12979115) B12979115
theorem B7604167 : Blo 1709055 7604167 := bstep (se 1 (by rfl) ⟨5703125, by rfl⟩ : syracuseStep 7604167 = 11406251) B11406251
theorem B2566127 : Blo 1709055 2566127 := bstep (se 1 (by rfl) ⟨1924595, by rfl⟩ : syracuseStep 2566127 = 3849191) B3849191
theorem B4327415 : Blo 1709055 4327415 := bstep (se 1 (by rfl) ⟨3245561, by rfl⟩ : syracuseStep 4327415 = 6491123) B6491123
theorem B56248325 : Blo 1709055 56248325 := bstep (se 4 (by rfl) ⟨5273280, by rfl⟩ : syracuseStep 56248325 = 10546561) B10546561
theorem B15419443 : Blo 1709055 15419443 := bstep (se 1 (by rfl) ⟨11564582, by rfl⟩ : syracuseStep 15419443 = 23129165) B23129165
theorem B14608613 : Blo 1709055 14608613 := bstep (se 4 (by rfl) ⟨1369557, by rfl⟩ : syracuseStep 14608613 = 2739115) B2739115
theorem B2599145 : Blo 1709055 2599145 := bstep (se 2 (by rfl) ⟨974679, by rfl⟩ : syracuseStep 2599145 = 1949359) B1949359
theorem B2566379 : Blo 1709055 2566379 := bstep (se 1 (by rfl) ⟨1924784, by rfl⟩ : syracuseStep 2566379 = 3849569) B3849569
theorem B2566439 : Blo 1709055 2566439 := bstep (se 1 (by rfl) ⟨1924829, by rfl⟩ : syracuseStep 2566439 = 3849659) B3849659
theorem B4868399 : Blo 1709055 4868399 := bstep (se 1 (by rfl) ⟨3651299, by rfl⟩ : syracuseStep 4868399 = 7302599) B7302599
theorem B2885935 : Blo 1709055 2885935 := bstep (se 1 (by rfl) ⟨2164451, by rfl⟩ : syracuseStep 2885935 = 4328903) B4328903
theorem B55494989 : Blo 1709055 55494989 := bstep (se 3 (by rfl) ⟨10405310, by rfl⟩ : syracuseStep 55494989 = 20810621) B20810621
theorem B6162779 : Blo 1709055 6162779 := bstep (se 1 (by rfl) ⟨4622084, by rfl⟩ : syracuseStep 6162779 = 9244169) B9244169
theorem B2566523 : Blo 1709055 2566523 := bstep (se 1 (by rfl) ⟨1924892, by rfl⟩ : syracuseStep 2566523 = 3849785) B3849785
theorem B4934027 : Blo 1709055 4934027 := bstep (se 1 (by rfl) ⟨3700520, by rfl⟩ : syracuseStep 4934027 = 7401041) B7401041
theorem B5769629 : Blo 1709055 5769629 := bstep (se 3 (by rfl) ⟨1081805, by rfl⟩ : syracuseStep 5769629 = 2163611) B2163611
theorem B3082889 : Blo 1709055 3082889 := bstep (se 2 (by rfl) ⟨1156083, by rfl⟩ : syracuseStep 3082889 = 2312167) B2312167
theorem B5769899 : Blo 1709055 5769899 := bstep (se 1 (by rfl) ⟨4327424, by rfl⟩ : syracuseStep 5769899 = 8654849) B8654849
theorem B6163127 : Blo 1709055 6163127 := bstep (se 1 (by rfl) ⟨4622345, by rfl⟩ : syracuseStep 6163127 = 9244691) B9244691
theorem B2886455 : Blo 1709055 2886455 := bstep (se 1 (by rfl) ⟨2164841, by rfl⟩ : syracuseStep 2886455 = 4329683) B4329683
theorem B8661815 : Blo 1709055 8661815 := bstep (se 1 (by rfl) ⟨6496361, by rfl⟩ : syracuseStep 8661815 = 12992723) B12992723
theorem B3124127 : Blo 1709055 3124127 := bstep (se 1 (by rfl) ⟨2343095, by rfl⟩ : syracuseStep 3124127 = 4686191) B4686191
theorem B2435999 : Blo 1709055 2435999 := bstep (se 1 (by rfl) ⟨1826999, by rfl⟩ : syracuseStep 2435999 = 3653999) B3653999
theorem B5770439 : Blo 1709055 5770439 := bstep (se 1 (by rfl) ⟨4327829, by rfl⟩ : syracuseStep 5770439 = 8655659) B8655659
theorem B4328873 : Blo 1709055 4328873 := bstep (se 2 (by rfl) ⟨1623327, by rfl⟩ : syracuseStep 4328873 = 3246655) B3246655
theorem B3845627 : Blo 1709055 3845627 := bstep (se 1 (by rfl) ⟨2884220, by rfl⟩ : syracuseStep 3845627 = 5768441) B5768441
theorem B5852729 : Blo 1709055 5852729 := bstep (se 2 (by rfl) ⟨2194773, by rfl⟩ : syracuseStep 5852729 = 4389547) B4389547
theorem B2887231 : Blo 1709055 2887231 := bstep (se 1 (by rfl) ⟨2165423, by rfl⟩ : syracuseStep 2887231 = 4330847) B4330847
theorem B3845807 : Blo 1709055 3845807 := bstep (se 1 (by rfl) ⟨2884355, by rfl⟩ : syracuseStep 3845807 = 5768711) B5768711
theorem B5271335 : Blo 1709055 5271335 := bstep (se 1 (by rfl) ⟨3953501, by rfl⟩ : syracuseStep 5271335 = 7907003) B7907003
theorem B1732423 : Blo 1709055 1732423 := bstep (se 1 (by rfl) ⟨1299317, by rfl⟩ : syracuseStep 1732423 = 2598635) B2598635
theorem B4329359 : Blo 1709055 4329359 := bstep (se 1 (by rfl) ⟨3247019, by rfl⟩ : syracuseStep 4329359 = 6494039) B6494039
theorem B9244859 : Blo 1709055 9244859 := bstep (se 1 (by rfl) ⟨6933644, by rfl⟩ : syracuseStep 9244859 = 13867289) B13867289
theorem B6492413 : Blo 1709055 6492413 := bstep (se 3 (by rfl) ⟨1217327, by rfl⟩ : syracuseStep 6492413 = 2434655) B2434655
theorem B3846455 : Blo 1709055 3846455 := bstep (se 1 (by rfl) ⟨2884841, by rfl⟩ : syracuseStep 3846455 = 5769683) B5769683
theorem B3846527 : Blo 1709055 3846527 := bstep (se 1 (by rfl) ⟨2884895, by rfl⟩ : syracuseStep 3846527 = 5769791) B5769791
theorem B16429463 : Blo 1709055 16429463 := bstep (se 1 (by rfl) ⟨12322097, by rfl⟩ : syracuseStep 16429463 = 24644195) B24644195
theorem B5771735 : Blo 1709055 5771735 := bstep (se 1 (by rfl) ⟨4328801, by rfl⟩ : syracuseStep 5771735 = 8657603) B8657603
theorem B70234685 : Blo 1709055 70234685 := bstep (se 3 (by rfl) ⟨13169003, by rfl⟩ : syracuseStep 70234685 = 26338007) B26338007
theorem B8221267 : Blo 1709055 8221267 := bstep (se 1 (by rfl) ⟨6165950, by rfl⟩ : syracuseStep 8221267 = 12331901) B12331901
theorem B4108895 : Blo 1709055 4108895 := bstep (se 1 (by rfl) ⟨3081671, by rfl⟩ : syracuseStep 4108895 = 6163343) B6163343
theorem B6583031 : Blo 1709055 6583031 := bstep (se 1 (by rfl) ⟨4937273, by rfl⟩ : syracuseStep 6583031 = 9874547) B9874547
theorem B1709119 : Blo 1709055 1709119 := bstep (se 1 (by rfl) ⟨1281839, by rfl⟩ : syracuseStep 1709119 = 2563679) B2563679
theorem B12489805 : Blo 1709055 12489805 := bstep (se 3 (by rfl) ⟨2341838, by rfl⟩ : syracuseStep 12489805 = 4683677) B4683677
theorem B1709263 : Blo 1709055 1709263 := bstep (se 1 (by rfl) ⟨1281947, by rfl⟩ : syracuseStep 1709263 = 2563895) B2563895
theorem B9737435 : Blo 1709055 9737435 := bstep (se 1 (by rfl) ⟨7303076, by rfl⟩ : syracuseStep 9737435 = 14606153) B14606153
theorem B1709467 : Blo 1709055 1709467 := bstep (se 1 (by rfl) ⟨1282100, by rfl⟩ : syracuseStep 1709467 = 2564201) B2564201
theorem B4871623 : Blo 1709055 4871623 := bstep (se 1 (by rfl) ⟨3653717, by rfl⟩ : syracuseStep 4871623 = 7307435) B7307435
theorem B3847751 : Blo 1709055 3847751 := bstep (se 1 (by rfl) ⟨2885813, by rfl⟩ : syracuseStep 3847751 = 5771627) B5771627
theorem B20788825 : Blo 1709055 20788825 := bstep (se 2 (by rfl) ⟨7795809, by rfl⟩ : syracuseStep 20788825 = 15591619) B15591619
theorem B1709679 : Blo 1709055 1709679 := bstep (se 1 (by rfl) ⟨1282259, by rfl⟩ : syracuseStep 1709679 = 2564519) B2564519
theorem B1709735 : Blo 1709055 1709735 := bstep (se 1 (by rfl) ⟨1282301, by rfl⟩ : syracuseStep 1709735 = 2564603) B2564603
theorem B1709819 : Blo 1709055 1709819 := bstep (se 1 (by rfl) ⟨1282364, by rfl⟩ : syracuseStep 1709819 = 2564729) B2564729
theorem B3847931 : Blo 1709055 3847931 := bstep (se 1 (by rfl) ⟨2885948, by rfl⟩ : syracuseStep 3847931 = 5771897) B5771897
theorem B5478155 : Blo 1709055 5478155 := bstep (se 1 (by rfl) ⟨4108616, by rfl⟩ : syracuseStep 5478155 = 8217233) B8217233
theorem B1709855 : Blo 1709055 1709855 := bstep (se 1 (by rfl) ⟨1282391, by rfl⟩ : syracuseStep 1709855 = 2564783) B2564783
theorem B1709887 : Blo 1709055 1709887 := bstep (se 1 (by rfl) ⟨1282415, by rfl⟩ : syracuseStep 1709887 = 2564831) B2564831
theorem B5773193 : Blo 1709055 5773193 := bstep (se 2 (by rfl) ⟨2164947, by rfl⟩ : syracuseStep 5773193 = 4329895) B4329895
theorem B1710063 : Blo 1709055 1710063 := bstep (se 1 (by rfl) ⟨1282547, by rfl⟩ : syracuseStep 1710063 = 2565095) B2565095
theorem B9369593 : Blo 1709055 9369593 := bstep (se 2 (by rfl) ⟨3513597, by rfl⟩ : syracuseStep 9369593 = 7027195) B7027195
theorem B5478425 : Blo 1709055 5478425 := bstep (se 2 (by rfl) ⟨2054409, by rfl⟩ : syracuseStep 5478425 = 4108819) B4108819
theorem B7305299 : Blo 1709055 7305299 := bstep (se 1 (by rfl) ⟨5478974, by rfl⟩ : syracuseStep 7305299 = 10957949) B10957949
theorem B49289309 : Blo 1709055 49289309 := bstep (se 3 (by rfl) ⟨9241745, by rfl⟩ : syracuseStep 49289309 = 18483491) B18483491
theorem B5773409 : Blo 1709055 5773409 := bstep (se 2 (by rfl) ⟨2165028, by rfl⟩ : syracuseStep 5773409 = 4330057) B4330057
theorem B1710235 : Blo 1709055 1710235 := bstep (se 1 (by rfl) ⟨1282676, by rfl⟩ : syracuseStep 1710235 = 2565353) B2565353
theorem B1710271 : Blo 1709055 1710271 := bstep (se 1 (by rfl) ⟨1282703, by rfl⟩ : syracuseStep 1710271 = 2565407) B2565407
theorem B8771827 : Blo 1709055 8771827 := bstep (se 1 (by rfl) ⟨6578870, by rfl⟩ : syracuseStep 8771827 = 13157741) B13157741
theorem B21911795 : Blo 1709055 21911795 := bstep (se 1 (by rfl) ⟨16433846, by rfl⟩ : syracuseStep 21911795 = 32867693) B32867693
theorem B3848489 : Blo 1709055 3848489 := bstep (se 2 (by rfl) ⟨1443183, by rfl⟩ : syracuseStep 3848489 = 2886367) B2886367
theorem B1710383 : Blo 1709055 1710383 := bstep (se 1 (by rfl) ⟨1282787, by rfl⟩ : syracuseStep 1710383 = 2565575) B2565575
theorem B30439741 : Blo 1709055 30439741 := bstep (se 3 (by rfl) ⟨5707451, by rfl⟩ : syracuseStep 30439741 = 11414903) B11414903
theorem B5478845 : Blo 1709055 5478845 := bstep (se 3 (by rfl) ⟨1027283, by rfl⟩ : syracuseStep 5478845 = 2054567) B2054567
theorem B56236477 : Blo 1709055 56236477 := bstep (se 3 (by rfl) ⟨10544339, by rfl⟩ : syracuseStep 56236477 = 21088679) B21088679
theorem B2054683 : Blo 1709055 2054683 := bstep (se 1 (by rfl) ⟨1541012, by rfl⟩ : syracuseStep 2054683 = 3082025) B3082025
theorem B1710619 : Blo 1709055 1710619 := bstep (se 1 (by rfl) ⟨1282964, by rfl⟩ : syracuseStep 1710619 = 2565929) B2565929
theorem B1710623 : Blo 1709055 1710623 := bstep (se 1 (by rfl) ⟨1282967, by rfl⟩ : syracuseStep 1710623 = 2565935) B2565935
theorem B1710939 : Blo 1709055 1710939 := bstep (se 1 (by rfl) ⟨1283204, by rfl⟩ : syracuseStep 1710939 = 2566409) B2566409
theorem B3849065 : Blo 1709055 3849065 := bstep (se 2 (by rfl) ⟨1443399, by rfl⟩ : syracuseStep 3849065 = 2886799) B2886799
theorem B29621123 : Blo 1709055 29621123 := bstep (se 1 (by rfl) ⟨22215842, by rfl⟩ : syracuseStep 29621123 = 44431685) B44431685
theorem B3849119 : Blo 1709055 3849119 := bstep (se 1 (by rfl) ⟨2886839, by rfl⟩ : syracuseStep 3849119 = 5773679) B5773679
theorem B1711007 : Blo 1709055 1711007 := bstep (se 1 (by rfl) ⟨1283255, by rfl⟩ : syracuseStep 1711007 = 2566511) B2566511
theorem B5774327 : Blo 1709055 5774327 := bstep (se 1 (by rfl) ⟨4330745, by rfl⟩ : syracuseStep 5774327 = 8661491) B8661491
theorem B32873687 : Blo 1709055 32873687 := bstep (se 1 (by rfl) ⟨24655265, by rfl⟩ : syracuseStep 32873687 = 49310531) B49310531
theorem B12328325 : Blo 1709055 12328325 := bstep (se 4 (by rfl) ⟨1155780, by rfl⟩ : syracuseStep 12328325 = 2311561) B2311561
theorem B5774759 : Blo 1709055 5774759 := bstep (se 1 (by rfl) ⟨4331069, by rfl⟩ : syracuseStep 5774759 = 8662139) B8662139
theorem B10395215 : Blo 1709055 10395215 := bstep (se 1 (by rfl) ⟨7796411, by rfl⟩ : syracuseStep 10395215 = 15592823) B15592823
theorem B1924699 : Blo 1709055 1924699 := bstep (se 1 (by rfl) ⟨1443524, by rfl⟩ : syracuseStep 1924699 = 2887049) B2887049
theorem B2563691 : Blo 1709055 2563691 := bstep (se 1 (by rfl) ⟨1922768, by rfl⟩ : syracuseStep 2563691 = 3845537) B3845537
theorem B2563817 : Blo 1709055 2563817 := bstep (se 2 (by rfl) ⟨961431, by rfl⟩ : syracuseStep 2563817 = 1922863) B1922863
theorem B27737963 : Blo 1709055 27737963 := bstep (se 1 (by rfl) ⟨20803472, by rfl⟩ : syracuseStep 27737963 = 41606945) B41606945
theorem B2563961 : Blo 1709055 2563961 := bstep (se 2 (by rfl) ⟨961485, by rfl⟩ : syracuseStep 2563961 = 1922971) B1922971
theorem B2564063 : Blo 1709055 2564063 := bstep (se 1 (by rfl) ⟨1923047, by rfl⟩ : syracuseStep 2564063 = 3846095) B3846095
theorem B2564303 : Blo 1709055 2564303 := bstep (se 1 (by rfl) ⟨1923227, by rfl⟩ : syracuseStep 2564303 = 3846455) B3846455
theorem B2564351 : Blo 1709055 2564351 := bstep (se 1 (by rfl) ⟨1923263, by rfl⟩ : syracuseStep 2564351 = 3846527) B3846527
theorem B10952975 : Blo 1709055 10952975 := bstep (se 1 (by rfl) ⟨8214731, by rfl⟩ : syracuseStep 10952975 = 16429463) B16429463
theorem B29622647 : Blo 1709055 29622647 := bstep (se 1 (by rfl) ⟨22216985, by rfl⟩ : syracuseStep 29622647 = 44433971) B44433971
theorem B74981969 : Blo 1709055 74981969 := bstep (se 2 (by rfl) ⟨28118238, by rfl⟩ : syracuseStep 74981969 = 56236477) B56236477
theorem B2884207 : Blo 1709055 2884207 := bstep (se 1 (by rfl) ⟨2163155, by rfl⟩ : syracuseStep 2884207 = 4326311) B4326311
theorem B10961689 : Blo 1709055 10961689 := bstep (se 2 (by rfl) ⟨4110633, by rfl⟩ : syracuseStep 10961689 = 8221267) B8221267
theorem B4867067 : Blo 1709055 4867067 := bstep (se 1 (by rfl) ⟨3650300, by rfl⟩ : syracuseStep 4867067 = 7300601) B7300601
theorem B2565167 : Blo 1709055 2565167 := bstep (se 1 (by rfl) ⟨1923875, by rfl⟩ : syracuseStep 2565167 = 3847751) B3847751
theorem B2565287 : Blo 1709055 2565287 := bstep (se 1 (by rfl) ⟨1923965, by rfl⟩ : syracuseStep 2565287 = 3847931) B3847931
theorem B2163935 : Blo 1709055 2163935 := bstep (se 1 (by rfl) ⟨1622951, by rfl⟩ : syracuseStep 2163935 = 3245903) B3245903
theorem B5768495 : Blo 1709055 5768495 := bstep (se 1 (by rfl) ⟨4326371, by rfl⟩ : syracuseStep 5768495 = 8652743) B8652743
theorem B2884943 : Blo 1709055 2884943 := bstep (se 1 (by rfl) ⟨2163707, by rfl⟩ : syracuseStep 2884943 = 4327415) B4327415
theorem B32859539 : Blo 1709055 32859539 := bstep (se 1 (by rfl) ⟨24644654, by rfl⟩ : syracuseStep 32859539 = 49289309) B49289309
theorem B8652257 : Blo 1709055 8652257 := bstep (se 2 (by rfl) ⟨3244596, by rfl⟩ : syracuseStep 8652257 = 6489193) B6489193
theorem B14607863 : Blo 1709055 14607863 := bstep (se 1 (by rfl) ⟨10955897, by rfl⟩ : syracuseStep 14607863 = 21911795) B21911795
theorem B2565659 : Blo 1709055 2565659 := bstep (se 1 (by rfl) ⟨1924244, by rfl⟩ : syracuseStep 2565659 = 3848489) B3848489
theorem B3245599 : Blo 1709055 3245599 := bstep (se 1 (by rfl) ⟨2434199, by rfl⟩ : syracuseStep 3245599 = 4868399) B4868399
theorem B36996659 : Blo 1709055 36996659 := bstep (se 1 (by rfl) ⟨27747494, by rfl⟩ : syracuseStep 36996659 = 55494989) B55494989
theorem B7300925 : Blo 1709055 7300925 := bstep (se 3 (by rfl) ⟨1368923, by rfl⟩ : syracuseStep 7300925 = 2737847) B2737847
theorem B6489953 : Blo 1709055 6489953 := bstep (se 2 (by rfl) ⟨2433732, by rfl⟩ : syracuseStep 6489953 = 4867465) B4867465
theorem B2566043 : Blo 1709055 2566043 := bstep (se 1 (by rfl) ⟨1924532, by rfl⟩ : syracuseStep 2566043 = 3849065) B3849065
theorem B2566079 : Blo 1709055 2566079 := bstep (se 1 (by rfl) ⟨1924559, by rfl⟩ : syracuseStep 2566079 = 3849119) B3849119
theorem B2566265 : Blo 1709055 2566265 := bstep (se 2 (by rfl) ⟨962349, by rfl⟩ : syracuseStep 2566265 = 1924699) B1924699
theorem B21915791 : Blo 1709055 21915791 := bstep (se 1 (by rfl) ⟨16436843, by rfl⟩ : syracuseStep 21915791 = 32873687) B32873687
theorem B3901601 : Blo 1709055 3901601 := bstep (se 2 (by rfl) ⟨1463100, by rfl⟩ : syracuseStep 3901601 = 2926201) B2926201
theorem B8218883 : Blo 1709055 8218883 := bstep (se 1 (by rfl) ⟨6164162, by rfl⟩ : syracuseStep 8218883 = 12328325) B12328325
theorem B2885915 : Blo 1709055 2885915 := bstep (se 1 (by rfl) ⟨2164436, by rfl⟩ : syracuseStep 2885915 = 4328873) B4328873
theorem B3901819 : Blo 1709055 3901819 := bstep (se 1 (by rfl) ⟨2926364, by rfl⟩ : syracuseStep 3901819 = 5852729) B5852729
theorem B18491975 : Blo 1709055 18491975 := bstep (se 1 (by rfl) ⟨13868981, by rfl⟩ : syracuseStep 18491975 = 27737963) B27737963
theorem B2886239 : Blo 1709055 2886239 := bstep (se 1 (by rfl) ⟨2164679, by rfl⟩ : syracuseStep 2886239 = 4329359) B4329359
theorem B4328275 : Blo 1709055 4328275 := bstep (se 1 (by rfl) ⟨3246206, by rfl⟩ : syracuseStep 4328275 = 6492413) B6492413
theorem B2739263 : Blo 1709055 2739263 := bstep (se 1 (by rfl) ⟨2054447, by rfl⟩ : syracuseStep 2739263 = 4108895) B4108895
theorem B66612293 : Blo 1709055 66612293 := bstep (se 4 (by rfl) ⟨6244902, by rfl⟩ : syracuseStep 66612293 = 12489805) B12489805
theorem B40586321 : Blo 1709055 40586321 := bstep (se 2 (by rfl) ⟨15219870, by rfl⟩ : syracuseStep 40586321 = 30439741) B30439741
theorem B2739577 : Blo 1709055 2739577 := bstep (se 2 (by rfl) ⟨1027341, by rfl⟩ : syracuseStep 2739577 = 2054683) B2054683
theorem B6491623 : Blo 1709055 6491623 := bstep (se 1 (by rfl) ⟨4868717, by rfl⟩ : syracuseStep 6491623 = 9737435) B9737435
theorem B52620839 : Blo 1709055 52620839 := bstep (se 1 (by rfl) ⟨39465629, by rfl⟩ : syracuseStep 52620839 = 78931259) B78931259
theorem B4107847 : Blo 1709055 4107847 := bstep (se 1 (by rfl) ⟨3080885, by rfl⟩ : syracuseStep 4107847 = 6161771) B6161771
theorem B3845879 : Blo 1709055 3845879 := bstep (se 1 (by rfl) ⟨2884409, by rfl⟩ : syracuseStep 3845879 = 5768819) B5768819
theorem B3845951 : Blo 1709055 3845951 := bstep (se 1 (by rfl) ⟨2884463, by rfl⟩ : syracuseStep 3845951 = 5768927) B5768927
theorem B14610253 : Blo 1709055 14610253 := bstep (se 3 (by rfl) ⟨2739422, by rfl⟩ : syracuseStep 14610253 = 5478845) B5478845
theorem B3846059 : Blo 1709055 3846059 := bstep (se 1 (by rfl) ⟨2884544, by rfl⟩ : syracuseStep 3846059 = 5769089) B5769089
theorem B6246395 : Blo 1709055 6246395 := bstep (se 1 (by rfl) ⟨4684796, by rfl⟩ : syracuseStep 6246395 = 9369593) B9369593
theorem B37498883 : Blo 1709055 37498883 := bstep (se 1 (by rfl) ⟨28124162, by rfl⟩ : syracuseStep 37498883 = 56248325) B56248325
theorem B4870199 : Blo 1709055 4870199 := bstep (se 1 (by rfl) ⟨3652649, by rfl⟩ : syracuseStep 4870199 = 7305299) B7305299
theorem B1732763 : Blo 1709055 1732763 := bstep (se 1 (by rfl) ⟨1299572, by rfl⟩ : syracuseStep 1732763 = 2599145) B2599145
theorem B4108519 : Blo 1709055 4108519 := bstep (se 1 (by rfl) ⟨3081389, by rfl⟩ : syracuseStep 4108519 = 6162779) B6162779
theorem B3289351 : Blo 1709055 3289351 := bstep (se 1 (by rfl) ⟨2467013, by rfl⟩ : syracuseStep 3289351 = 4934027) B4934027
theorem B3846419 : Blo 1709055 3846419 := bstep (se 1 (by rfl) ⟨2884814, by rfl⟩ : syracuseStep 3846419 = 5769629) B5769629
theorem B3846599 : Blo 1709055 3846599 := bstep (se 1 (by rfl) ⟨2884949, by rfl⟩ : syracuseStep 3846599 = 5769899) B5769899
theorem B4108751 : Blo 1709055 4108751 := bstep (se 1 (by rfl) ⟨3081563, by rfl⟩ : syracuseStep 4108751 = 6163127) B6163127
theorem B19747415 : Blo 1709055 19747415 := bstep (se 1 (by rfl) ⟨14810561, by rfl⟩ : syracuseStep 19747415 = 29621123) B29621123
theorem B98611829 : Blo 1709055 98611829 := bstep (se 5 (by rfl) ⟨4622429, by rfl⟩ : syracuseStep 98611829 = 9244859) B9244859
theorem B27718433 : Blo 1709055 27718433 := bstep (se 2 (by rfl) ⟨10394412, by rfl⟩ : syracuseStep 27718433 = 20788825) B20788825
theorem B3846959 : Blo 1709055 3846959 := bstep (se 1 (by rfl) ⟨2885219, by rfl⟩ : syracuseStep 3846959 = 5770439) B5770439
theorem B3847049 : Blo 1709055 3847049 := bstep (se 2 (by rfl) ⟨1442643, by rfl⟩ : syracuseStep 3847049 = 2885287) B2885287
theorem B12989321 : Blo 1709055 12989321 := bstep (se 2 (by rfl) ⟨4870995, by rfl⟩ : syracuseStep 12989321 = 9741991) B9741991
theorem B1709127 : Blo 1709055 1709127 := bstep (se 1 (by rfl) ⟨1281845, by rfl⟩ : syracuseStep 1709127 = 2563691) B2563691
theorem B1709211 : Blo 1709055 1709211 := bstep (se 1 (by rfl) ⟨1281908, by rfl⟩ : syracuseStep 1709211 = 2563817) B2563817
theorem B1709307 : Blo 1709055 1709307 := bstep (se 1 (by rfl) ⟨1281980, by rfl⟩ : syracuseStep 1709307 = 2563961) B2563961
theorem B10138889 : Blo 1709055 10138889 := bstep (se 2 (by rfl) ⟨3802083, by rfl⟩ : syracuseStep 10138889 = 7604167) B7604167
theorem B1709375 : Blo 1709055 1709375 := bstep (se 1 (by rfl) ⟨1282031, by rfl⟩ : syracuseStep 1709375 = 2564063) B2564063
theorem B20559257 : Blo 1709055 20559257 := bstep (se 2 (by rfl) ⟨7709721, by rfl⟩ : syracuseStep 20559257 = 15419443) B15419443
theorem B1709543 : Blo 1709055 1709543 := bstep (se 1 (by rfl) ⟨1282157, by rfl⟩ : syracuseStep 1709543 = 2564315) B2564315
theorem B1709551 : Blo 1709055 1709551 := bstep (se 1 (by rfl) ⟨1282163, by rfl⟩ : syracuseStep 1709551 = 2564327) B2564327
theorem B1709659 : Blo 1709055 1709659 := bstep (se 1 (by rfl) ⟨1282244, by rfl⟩ : syracuseStep 1709659 = 2564489) B2564489
theorem B24663689 : Blo 1709055 24663689 := bstep (se 2 (by rfl) ⟨9248883, by rfl⟩ : syracuseStep 24663689 = 18497767) B18497767
theorem B3847823 : Blo 1709055 3847823 := bstep (se 1 (by rfl) ⟨2885867, by rfl⟩ : syracuseStep 3847823 = 5771735) B5771735
theorem B11695769 : Blo 1709055 11695769 := bstep (se 2 (by rfl) ⟨4385913, by rfl⟩ : syracuseStep 11695769 = 8771827) B8771827
theorem B1709723 : Blo 1709055 1709723 := bstep (se 1 (by rfl) ⟨1282292, by rfl⟩ : syracuseStep 1709723 = 2564585) B2564585
theorem B46823123 : Blo 1709055 46823123 := bstep (se 1 (by rfl) ⟨35117342, by rfl⟩ : syracuseStep 46823123 = 70234685) B70234685
theorem B3847913 : Blo 1709055 3847913 := bstep (se 2 (by rfl) ⟨1442967, by rfl⟩ : syracuseStep 3847913 = 2885935) B2885935
theorem B1709807 : Blo 1709055 1709807 := bstep (se 1 (by rfl) ⟨1282355, by rfl⟩ : syracuseStep 1709807 = 2564711) B2564711
theorem B1709895 : Blo 1709055 1709895 := bstep (se 1 (by rfl) ⟨1282421, by rfl⟩ : syracuseStep 1709895 = 2564843) B2564843
theorem B4388687 : Blo 1709055 4388687 := bstep (se 1 (by rfl) ⟨3291515, by rfl⟩ : syracuseStep 4388687 = 6583031) B6583031
theorem B5773139 : Blo 1709055 5773139 := bstep (se 1 (by rfl) ⟨4329854, by rfl⟩ : syracuseStep 5773139 = 8659709) B8659709
theorem B1709915 : Blo 1709055 1709915 := bstep (se 1 (by rfl) ⟨1282436, by rfl⟩ : syracuseStep 1709915 = 2564873) B2564873
theorem B9738143 : Blo 1709055 9738143 := bstep (se 1 (by rfl) ⟨7303607, by rfl⟩ : syracuseStep 9738143 = 14607215) B14607215
theorem B1709983 : Blo 1709055 1709983 := bstep (se 1 (by rfl) ⟨1282487, by rfl⟩ : syracuseStep 1709983 = 2564975) B2564975
theorem B1710151 : Blo 1709055 1710151 := bstep (se 1 (by rfl) ⟨1282613, by rfl⟩ : syracuseStep 1710151 = 2565227) B2565227
theorem B1710311 : Blo 1709055 1710311 := bstep (se 1 (by rfl) ⟨1282733, by rfl⟩ : syracuseStep 1710311 = 2565467) B2565467
theorem B1710495 : Blo 1709055 1710495 := bstep (se 1 (by rfl) ⟨1282871, by rfl⟩ : syracuseStep 1710495 = 2565743) B2565743
theorem B1710543 : Blo 1709055 1710543 := bstep (se 1 (by rfl) ⟨1282907, by rfl⟩ : syracuseStep 1710543 = 2565815) B2565815
theorem B1710567 : Blo 1709055 1710567 := bstep (se 1 (by rfl) ⟨1282925, by rfl⟩ : syracuseStep 1710567 = 2565851) B2565851
theorem B3652103 : Blo 1709055 3652103 := bstep (se 1 (by rfl) ⟨2739077, by rfl⟩ : syracuseStep 3652103 = 5478155) B5478155
theorem B3848795 : Blo 1709055 3848795 := bstep (se 1 (by rfl) ⟨2886596, by rfl⟩ : syracuseStep 3848795 = 5773193) B5773193
theorem B1710683 : Blo 1709055 1710683 := bstep (se 1 (by rfl) ⟨1283012, by rfl⟩ : syracuseStep 1710683 = 2566025) B2566025
theorem B1710751 : Blo 1709055 1710751 := bstep (se 1 (by rfl) ⟨1283063, by rfl⟩ : syracuseStep 1710751 = 2566127) B2566127
theorem B3652283 : Blo 1709055 3652283 := bstep (se 1 (by rfl) ⟨2739212, by rfl⟩ : syracuseStep 3652283 = 5478425) B5478425
theorem B3848939 : Blo 1709055 3848939 := bstep (se 1 (by rfl) ⟨2886704, by rfl⟩ : syracuseStep 3848939 = 5773409) B5773409
theorem B9739075 : Blo 1709055 9739075 := bstep (se 1 (by rfl) ⟨7304306, by rfl⟩ : syracuseStep 9739075 = 14608613) B14608613
theorem B1710919 : Blo 1709055 1710919 := bstep (se 1 (by rfl) ⟨1283189, by rfl⟩ : syracuseStep 1710919 = 2566379) B2566379
theorem B1710959 : Blo 1709055 1710959 := bstep (se 1 (by rfl) ⟨1283219, by rfl⟩ : syracuseStep 1710959 = 2566439) B2566439
theorem B1711015 : Blo 1709055 1711015 := bstep (se 1 (by rfl) ⟨1283261, by rfl⟩ : syracuseStep 1711015 = 2566523) B2566523
theorem B2055259 : Blo 1709055 2055259 := bstep (se 1 (by rfl) ⟨1541444, by rfl⟩ : syracuseStep 2055259 = 3082889) B3082889
theorem B1924303 : Blo 1709055 1924303 := bstep (se 1 (by rfl) ⟨1443227, by rfl⟩ : syracuseStep 1924303 = 2886455) B2886455
theorem B5774543 : Blo 1709055 5774543 := bstep (se 1 (by rfl) ⟨4330907, by rfl⟩ : syracuseStep 5774543 = 8661815) B8661815
theorem B6495497 : Blo 1709055 6495497 := bstep (se 2 (by rfl) ⟨2435811, by rfl⟩ : syracuseStep 6495497 = 4871623) B4871623
theorem B3849551 : Blo 1709055 3849551 := bstep (se 1 (by rfl) ⟨2887163, by rfl⟩ : syracuseStep 3849551 = 5774327) B5774327
theorem B3849641 : Blo 1709055 3849641 := bstep (se 2 (by rfl) ⟨1443615, by rfl⟩ : syracuseStep 3849641 = 2887231) B2887231
theorem B3849839 : Blo 1709055 3849839 := bstep (se 1 (by rfl) ⟨2887379, by rfl⟩ : syracuseStep 3849839 = 5774759) B5774759
theorem B2563751 : Blo 1709055 2563751 := bstep (se 1 (by rfl) ⟨1922813, by rfl⟩ : syracuseStep 2563751 = 3845627) B3845627
theorem B6930143 : Blo 1709055 6930143 := bstep (se 1 (by rfl) ⟨5197607, by rfl⟩ : syracuseStep 6930143 = 10395215) B10395215
theorem B8331005 : Blo 1709055 8331005 := bstep (se 3 (by rfl) ⟨1562063, by rfl⟩ : syracuseStep 8331005 = 3124127) B3124127
theorem B6495997 : Blo 1709055 6495997 := bstep (se 3 (by rfl) ⟨1217999, by rfl⟩ : syracuseStep 6495997 = 2435999) B2435999
theorem B2309897 : Blo 1709055 2309897 := bstep (se 2 (by rfl) ⟨866211, by rfl⟩ : syracuseStep 2309897 = 1732423) B1732423
theorem B2563871 : Blo 1709055 2563871 := bstep (se 1 (by rfl) ⟨1922903, by rfl⟩ : syracuseStep 2563871 = 3845807) B3845807
theorem B3514223 : Blo 1709055 3514223 := bstep (se 1 (by rfl) ⟨2635667, by rfl⟩ : syracuseStep 3514223 = 5271335) B5271335
theorem B2564279 : Blo 1709055 2564279 := bstep (se 1 (by rfl) ⟨1923209, by rfl⟩ : syracuseStep 2564279 = 3846419) B3846419
theorem B2564399 : Blo 1709055 2564399 := bstep (se 1 (by rfl) ⟨1923299, by rfl⟩ : syracuseStep 2564399 = 3846599) B3846599
theorem B49987979 : Blo 1709055 49987979 := bstep (se 1 (by rfl) ⟨37490984, by rfl⟩ : syracuseStep 49987979 = 74981969) B74981969
theorem B13164943 : Blo 1709055 13164943 := bstep (se 1 (by rfl) ⟨9873707, by rfl⟩ : syracuseStep 13164943 = 19747415) B19747415
theorem B4620701 : Blo 1709055 4620701 := bstep (se 3 (by rfl) ⟨866381, by rfl⟩ : syracuseStep 4620701 = 1732763) B1732763
theorem B65741219 : Blo 1709055 65741219 := bstep (se 1 (by rfl) ⟨49305914, by rfl⟩ : syracuseStep 65741219 = 98611829) B98611829
theorem B10961381 : Blo 1709055 10961381 := bstep (se 4 (by rfl) ⟨1027629, by rfl⟩ : syracuseStep 10961381 = 2055259) B2055259
theorem B5202425 : Blo 1709055 5202425 := bstep (se 2 (by rfl) ⟨1950909, by rfl⟩ : syracuseStep 5202425 = 3901819) B3901819
theorem B2564639 : Blo 1709055 2564639 := bstep (se 1 (by rfl) ⟨1923479, by rfl⟩ : syracuseStep 2564639 = 3846959) B3846959
theorem B2564699 : Blo 1709055 2564699 := bstep (se 1 (by rfl) ⟨1923524, by rfl⟩ : syracuseStep 2564699 = 3847049) B3847049
theorem B8659547 : Blo 1709055 8659547 := bstep (se 1 (by rfl) ⟨6494660, by rfl⟩ : syracuseStep 8659547 = 12989321) B12989321
theorem B3244711 : Blo 1709055 3244711 := bstep (se 1 (by rfl) ⟨2433533, by rfl⟩ : syracuseStep 3244711 = 4867067) B4867067
theorem B21906359 : Blo 1709055 21906359 := bstep (se 1 (by rfl) ⟨16429769, by rfl⟩ : syracuseStep 21906359 = 32859539) B32859539
theorem B13706171 : Blo 1709055 13706171 := bstep (se 1 (by rfl) ⟨10279628, by rfl⟩ : syracuseStep 13706171 = 20559257) B20559257
theorem B5768171 : Blo 1709055 5768171 := bstep (se 1 (by rfl) ⟨4326128, by rfl⟩ : syracuseStep 5768171 = 8652257) B8652257
theorem B14615585 : Blo 1709055 14615585 := bstep (se 2 (by rfl) ⟨5480844, by rfl⟩ : syracuseStep 14615585 = 10961689) B10961689
theorem B12985433 : Blo 1709055 12985433 := bstep (se 2 (by rfl) ⟨4869537, by rfl⟩ : syracuseStep 12985433 = 9739075) B9739075
theorem B16442459 : Blo 1709055 16442459 := bstep (se 1 (by rfl) ⟨12331844, by rfl⟩ : syracuseStep 16442459 = 24663689) B24663689
theorem B2565215 : Blo 1709055 2565215 := bstep (se 1 (by rfl) ⟨1923911, by rfl⟩ : syracuseStep 2565215 = 3847823) B3847823
theorem B2565275 : Blo 1709055 2565275 := bstep (se 1 (by rfl) ⟨1923956, by rfl⟩ : syracuseStep 2565275 = 3847913) B3847913
theorem B4867283 : Blo 1709055 4867283 := bstep (se 1 (by rfl) ⟨3650462, by rfl⟩ : syracuseStep 4867283 = 7300925) B7300925
theorem B2925791 : Blo 1709055 2925791 := bstep (se 1 (by rfl) ⟨2194343, by rfl⟩ : syracuseStep 2925791 = 4388687) B4388687
theorem B4326635 : Blo 1709055 4326635 := bstep (se 1 (by rfl) ⟨3244976, by rfl⟩ : syracuseStep 4326635 = 6489953) B6489953
theorem B2565737 : Blo 1709055 2565737 := bstep (se 2 (by rfl) ⟨962151, by rfl⟩ : syracuseStep 2565737 = 1924303) B1924303
theorem B2434735 : Blo 1709055 2434735 := bstep (se 1 (by rfl) ⟨1826051, by rfl⟩ : syracuseStep 2434735 = 3652103) B3652103
theorem B2565863 : Blo 1709055 2565863 := bstep (se 1 (by rfl) ⟨1924397, by rfl⟩ : syracuseStep 2565863 = 3848795) B3848795
theorem B2434855 : Blo 1709055 2434855 := bstep (se 1 (by rfl) ⟨1826141, by rfl⟩ : syracuseStep 2434855 = 3652283) B3652283
theorem B2565959 : Blo 1709055 2565959 := bstep (se 1 (by rfl) ⟨1924469, by rfl⟩ : syracuseStep 2565959 = 3848939) B3848939
theorem B4327465 : Blo 1709055 4327465 := bstep (se 2 (by rfl) ⟨1622799, by rfl⟩ : syracuseStep 4327465 = 3245599) B3245599
theorem B2566367 : Blo 1709055 2566367 := bstep (se 1 (by rfl) ⟨1924775, by rfl⟩ : syracuseStep 2566367 = 3849551) B3849551
theorem B2566427 : Blo 1709055 2566427 := bstep (se 1 (by rfl) ⟨1924820, by rfl⟩ : syracuseStep 2566427 = 3849641) B3849641
theorem B8661329 : Blo 1709055 8661329 := bstep (se 2 (by rfl) ⟨3247998, by rfl⟩ : syracuseStep 8661329 = 6495997) B6495997
theorem B35080559 : Blo 1709055 35080559 := bstep (se 1 (by rfl) ⟨26310419, by rfl⟩ : syracuseStep 35080559 = 52620839) B52620839
theorem B2566559 : Blo 1709055 2566559 := bstep (se 1 (by rfl) ⟨1924919, by rfl⟩ : syracuseStep 2566559 = 3849839) B3849839
theorem B4164263 : Blo 1709055 4164263 := bstep (se 1 (by rfl) ⟨3123197, by rfl⟩ : syracuseStep 4164263 = 6246395) B6246395
theorem B3246799 : Blo 1709055 3246799 := bstep (se 1 (by rfl) ⟨2435099, by rfl⟩ : syracuseStep 3246799 = 4870199) B4870199
theorem B7301983 : Blo 1709055 7301983 := bstep (se 1 (by rfl) ⟨5476487, by rfl⟩ : syracuseStep 7301983 = 10952975) B10952975
theorem B2739167 : Blo 1709055 2739167 := bstep (se 1 (by rfl) ⟨2054375, by rfl⟩ : syracuseStep 2739167 = 4108751) B4108751
theorem B4385801 : Blo 1709055 4385801 := bstep (se 2 (by rfl) ⟨1644675, by rfl⟩ : syracuseStep 4385801 = 3289351) B3289351
theorem B5770493 : Blo 1709055 5770493 := bstep (se 3 (by rfl) ⟨1081967, by rfl⟩ : syracuseStep 5770493 = 2163935) B2163935
theorem B27037037 : Blo 1709055 27037037 := bstep (se 3 (by rfl) ⟨5069444, by rfl⟩ : syracuseStep 27037037 = 10138889) B10138889
theorem B3845609 : Blo 1709055 3845609 := bstep (se 2 (by rfl) ⟨1442103, by rfl⟩ : syracuseStep 3845609 = 2884207) B2884207
theorem B3845663 : Blo 1709055 3845663 := bstep (se 1 (by rfl) ⟨2884247, by rfl⟩ : syracuseStep 3845663 = 5768495) B5768495
theorem B5771033 : Blo 1709055 5771033 := bstep (se 2 (by rfl) ⟨2164137, by rfl⟩ : syracuseStep 5771033 = 4328275) B4328275
theorem B31215415 : Blo 1709055 31215415 := bstep (se 1 (by rfl) ⟨23411561, by rfl⟩ : syracuseStep 31215415 = 46823123) B46823123
theorem B6492095 : Blo 1709055 6492095 := bstep (se 1 (by rfl) ⟨4869071, by rfl⟩ : syracuseStep 6492095 = 9738143) B9738143
theorem B14610527 : Blo 1709055 14610527 := bstep (se 1 (by rfl) ⟨10957895, by rfl⟩ : syracuseStep 14610527 = 21915791) B21915791
theorem B2601067 : Blo 1709055 2601067 := bstep (se 1 (by rfl) ⟨1950800, by rfl⟩ : syracuseStep 2601067 = 3901601) B3901601
theorem B8655497 : Blo 1709055 8655497 := bstep (se 2 (by rfl) ⟨3245811, by rfl⟩ : syracuseStep 8655497 = 6491623) B6491623
theorem B5477129 : Blo 1709055 5477129 := bstep (se 2 (by rfl) ⟨2053923, by rfl⟩ : syracuseStep 5477129 = 4107847) B4107847
theorem B4330331 : Blo 1709055 4330331 := bstep (se 1 (by rfl) ⟨3247748, by rfl⟩ : syracuseStep 4330331 = 6495497) B6495497
theorem B1709167 : Blo 1709055 1709167 := bstep (se 1 (by rfl) ⟨1281875, by rfl⟩ : syracuseStep 1709167 = 2563751) B2563751
theorem B1709247 : Blo 1709055 1709247 := bstep (se 1 (by rfl) ⟨1281935, by rfl⟩ : syracuseStep 1709247 = 2563871) B2563871
theorem B99997021 : Blo 1709055 99997021 := bstep (se 3 (by rfl) ⟨18749441, by rfl⟩ : syracuseStep 99997021 = 37498883) B37498883
theorem B1709535 : Blo 1709055 1709535 := bstep (se 1 (by rfl) ⟨1282151, by rfl⟩ : syracuseStep 1709535 = 2564303) B2564303
theorem B7304701 : Blo 1709055 7304701 := bstep (se 3 (by rfl) ⟨1369631, by rfl⟩ : syracuseStep 7304701 = 2739263) B2739263
theorem B1709567 : Blo 1709055 1709567 := bstep (se 1 (by rfl) ⟨1282175, by rfl⟩ : syracuseStep 1709567 = 2564351) B2564351
theorem B19748431 : Blo 1709055 19748431 := bstep (se 1 (by rfl) ⟨14811323, by rfl⟩ : syracuseStep 19748431 = 29622647) B29622647
theorem B5478025 : Blo 1709055 5478025 := bstep (se 2 (by rfl) ⟨2054259, by rfl⟩ : syracuseStep 5478025 = 4108519) B4108519
theorem B18478955 : Blo 1709055 18478955 := bstep (se 1 (by rfl) ⟨13859216, by rfl⟩ : syracuseStep 18478955 = 27718433) B27718433
theorem B1710111 : Blo 1709055 1710111 := bstep (se 1 (by rfl) ⟨1282583, by rfl⟩ : syracuseStep 1710111 = 2565167) B2565167
theorem B1710191 : Blo 1709055 1710191 := bstep (se 1 (by rfl) ⟨1282643, by rfl⟩ : syracuseStep 1710191 = 2565287) B2565287
theorem B1923295 : Blo 1709055 1923295 := bstep (se 1 (by rfl) ⟨1442471, by rfl⟩ : syracuseStep 1923295 = 2884943) B2884943
theorem B9738575 : Blo 1709055 9738575 := bstep (se 1 (by rfl) ⟨7303931, by rfl⟩ : syracuseStep 9738575 = 14607863) B14607863
theorem B1710439 : Blo 1709055 1710439 := bstep (se 1 (by rfl) ⟨1282829, by rfl⟩ : syracuseStep 1710439 = 2565659) B2565659
theorem B24664439 : Blo 1709055 24664439 := bstep (se 1 (by rfl) ⟨18498329, by rfl⟩ : syracuseStep 24664439 = 36996659) B36996659
theorem B7797179 : Blo 1709055 7797179 := bstep (se 1 (by rfl) ⟨5847884, by rfl⟩ : syracuseStep 7797179 = 11695769) B11695769
theorem B3848759 : Blo 1709055 3848759 := bstep (se 1 (by rfl) ⟨2886569, by rfl⟩ : syracuseStep 3848759 = 5773139) B5773139
theorem B1710695 : Blo 1709055 1710695 := bstep (se 1 (by rfl) ⟨1283021, by rfl⟩ : syracuseStep 1710695 = 2566043) B2566043
theorem B1710719 : Blo 1709055 1710719 := bstep (se 1 (by rfl) ⟨1283039, by rfl⟩ : syracuseStep 1710719 = 2566079) B2566079
theorem B1710843 : Blo 1709055 1710843 := bstep (se 1 (by rfl) ⟨1283132, by rfl⟩ : syracuseStep 1710843 = 2566265) B2566265
theorem B5479255 : Blo 1709055 5479255 := bstep (se 1 (by rfl) ⟨4109441, by rfl⟩ : syracuseStep 5479255 = 8218883) B8218883
theorem B1923943 : Blo 1709055 1923943 := bstep (se 1 (by rfl) ⟨1442957, by rfl⟩ : syracuseStep 1923943 = 2885915) B2885915
theorem B12327983 : Blo 1709055 12327983 := bstep (se 1 (by rfl) ⟨9245987, by rfl⟩ : syracuseStep 12327983 = 18491975) B18491975
theorem B1924159 : Blo 1709055 1924159 := bstep (se 1 (by rfl) ⟨1443119, by rfl⟩ : syracuseStep 1924159 = 2886239) B2886239
theorem B3652769 : Blo 1709055 3652769 := bstep (se 2 (by rfl) ⟨1369788, by rfl⟩ : syracuseStep 3652769 = 2739577) B2739577
theorem B6159725 : Blo 1709055 6159725 := bstep (se 3 (by rfl) ⟨1154948, by rfl⟩ : syracuseStep 6159725 = 2309897) B2309897
theorem B44408195 : Blo 1709055 44408195 := bstep (se 1 (by rfl) ⟨33306146, by rfl⟩ : syracuseStep 44408195 = 66612293) B66612293
theorem B27057547 : Blo 1709055 27057547 := bstep (se 1 (by rfl) ⟨20293160, by rfl⟩ : syracuseStep 27057547 = 40586321) B40586321
theorem B3849695 : Blo 1709055 3849695 := bstep (se 1 (by rfl) ⟨2887271, by rfl⟩ : syracuseStep 3849695 = 5774543) B5774543
theorem B9371261 : Blo 1709055 9371261 := bstep (se 3 (by rfl) ⟨1757111, by rfl⟩ : syracuseStep 9371261 = 3514223) B3514223
theorem B19480337 : Blo 1709055 19480337 := bstep (se 2 (by rfl) ⟨7305126, by rfl⟩ : syracuseStep 19480337 = 14610253) B14610253
theorem B4620095 : Blo 1709055 4620095 := bstep (se 1 (by rfl) ⟨3465071, by rfl⟩ : syracuseStep 4620095 = 6930143) B6930143
theorem B2563919 : Blo 1709055 2563919 := bstep (se 1 (by rfl) ⟨1922939, by rfl⟩ : syracuseStep 2563919 = 3845879) B3845879
theorem B5554003 : Blo 1709055 5554003 := bstep (se 1 (by rfl) ⟨4165502, by rfl⟩ : syracuseStep 5554003 = 8331005) B8331005
theorem B2563967 : Blo 1709055 2563967 := bstep (se 1 (by rfl) ⟨1922975, by rfl⟩ : syracuseStep 2563967 = 3845951) B3845951
theorem B2564039 : Blo 1709055 2564039 := bstep (se 1 (by rfl) ⟨1923029, by rfl⟩ : syracuseStep 2564039 = 3846059) B3846059
theorem B9740351 : Blo 1709055 9740351 := bstep (se 1 (by rfl) ⟨7305263, by rfl⟩ : syracuseStep 9740351 = 14610527) B14610527
theorem B33325319 : Blo 1709055 33325319 := bstep (se 1 (by rfl) ⟨24993989, by rfl⟩ : syracuseStep 33325319 = 49987979) B49987979
theorem B3080467 : Blo 1709055 3080467 := bstep (se 1 (by rfl) ⟨2310350, by rfl⟩ : syracuseStep 3080467 = 4620701) B4620701
theorem B43827479 : Blo 1709055 43827479 := bstep (se 1 (by rfl) ⟨32870609, by rfl⟩ : syracuseStep 43827479 = 65741219) B65741219
theorem B2564393 : Blo 1709055 2564393 := bstep (se 2 (by rfl) ⟨961647, by rfl⟩ : syracuseStep 2564393 = 1923295) B1923295
theorem B7307587 : Blo 1709055 7307587 := bstep (se 1 (by rfl) ⟨5480690, by rfl⟩ : syracuseStep 7307587 = 10961381) B10961381
theorem B10961639 : Blo 1709055 10961639 := bstep (se 1 (by rfl) ⟨8221229, by rfl⟩ : syracuseStep 10961639 = 16442459) B16442459
theorem B3244855 : Blo 1709055 3244855 := bstep (se 1 (by rfl) ⟨2433641, by rfl⟩ : syracuseStep 3244855 = 4867283) B4867283
theorem B1950527 : Blo 1709055 1950527 := bstep (se 1 (by rfl) ⟨1462895, by rfl⟩ : syracuseStep 1950527 = 2925791) B2925791
theorem B2884423 : Blo 1709055 2884423 := bstep (se 1 (by rfl) ⟨2163317, by rfl⟩ : syracuseStep 2884423 = 4326635) B4326635
theorem B4326281 : Blo 1709055 4326281 := bstep (se 2 (by rfl) ⟨1622355, by rfl⟩ : syracuseStep 4326281 = 3244711) B3244711
theorem B72098765 : Blo 1709055 72098765 := bstep (se 3 (by rfl) ⟨13518518, by rfl⟩ : syracuseStep 72098765 = 27037037) B27037037
theorem B2565257 : Blo 1709055 2565257 := bstep (se 2 (by rfl) ⟨961971, by rfl⟩ : syracuseStep 2565257 = 1923943) B1923943
theorem B20792477 : Blo 1709055 20792477 := bstep (se 3 (by rfl) ⟨3898589, by rfl⟩ : syracuseStep 20792477 = 7797179) B7797179
theorem B2565545 : Blo 1709055 2565545 := bstep (se 2 (by rfl) ⟨962079, by rfl⟩ : syracuseStep 2565545 = 1924159) B1924159
theorem B16442959 : Blo 1709055 16442959 := bstep (se 1 (by rfl) ⟨12332219, by rfl⟩ : syracuseStep 16442959 = 24664439) B24664439
theorem B2565839 : Blo 1709055 2565839 := bstep (se 1 (by rfl) ⟨1924379, by rfl⟩ : syracuseStep 2565839 = 3848759) B3848759
theorem B29222693 : Blo 1709055 29222693 := bstep (se 4 (by rfl) ⟨2739627, by rfl⟩ : syracuseStep 29222693 = 5479255) B5479255
theorem B8218655 : Blo 1709055 8218655 := bstep (se 1 (by rfl) ⟨6163991, by rfl⟩ : syracuseStep 8218655 = 12327983) B12327983
theorem B26331241 : Blo 1709055 26331241 := bstep (se 2 (by rfl) ⟨9874215, by rfl⟩ : syracuseStep 26331241 = 19748431) B19748431
theorem B2435179 : Blo 1709055 2435179 := bstep (se 1 (by rfl) ⟨1826384, by rfl⟩ : syracuseStep 2435179 = 3652769) B3652769
theorem B3246313 : Blo 1709055 3246313 := bstep (se 2 (by rfl) ⟨1217367, by rfl⟩ : syracuseStep 3246313 = 2434735) B2434735
theorem B4106483 : Blo 1709055 4106483 := bstep (se 1 (by rfl) ⟨3079862, by rfl⟩ : syracuseStep 4106483 = 6159725) B6159725
theorem B2566463 : Blo 1709055 2566463 := bstep (se 1 (by rfl) ⟨1924847, by rfl⟩ : syracuseStep 2566463 = 3849695) B3849695
theorem B3246473 : Blo 1709055 3246473 := bstep (se 2 (by rfl) ⟨1217427, by rfl⟩ : syracuseStep 3246473 = 2434855) B2434855
theorem B12986891 : Blo 1709055 12986891 := bstep (se 1 (by rfl) ⟨9740168, by rfl⟩ : syracuseStep 12986891 = 19480337) B19480337
theorem B4328063 : Blo 1709055 4328063 := bstep (se 1 (by rfl) ⟨3246047, by rfl⟩ : syracuseStep 4328063 = 6492095) B6492095
theorem B5769953 : Blo 1709055 5769953 := bstep (se 2 (by rfl) ⟨2163732, by rfl⟩ : syracuseStep 5769953 = 4327465) B4327465
theorem B3468089 : Blo 1709055 3468089 := bstep (se 2 (by rfl) ⟨1300533, by rfl⟩ : syracuseStep 3468089 = 2601067) B2601067
theorem B5770331 : Blo 1709055 5770331 := bstep (se 1 (by rfl) ⟨4327748, by rfl⟩ : syracuseStep 5770331 = 8655497) B8655497
theorem B2886887 : Blo 1709055 2886887 := bstep (se 1 (by rfl) ⟨2165165, by rfl⟩ : syracuseStep 2886887 = 4330331) B4330331
theorem B9137447 : Blo 1709055 9137447 := bstep (se 1 (by rfl) ⟨6853085, by rfl⟩ : syracuseStep 9137447 = 13706171) B13706171
theorem B3845447 : Blo 1709055 3845447 := bstep (se 1 (by rfl) ⟨2884085, by rfl⟩ : syracuseStep 3845447 = 5768171) B5768171
theorem B9743723 : Blo 1709055 9743723 := bstep (se 1 (by rfl) ⟨7307792, by rfl⟩ : syracuseStep 9743723 = 14615585) B14615585
theorem B4329065 : Blo 1709055 4329065 := bstep (se 2 (by rfl) ⟨1623399, by rfl⟩ : syracuseStep 4329065 = 3246799) B3246799
theorem B9735977 : Blo 1709055 9735977 := bstep (se 2 (by rfl) ⟨3650991, by rfl⟩ : syracuseStep 9735977 = 7301983) B7301983
theorem B13873133 : Blo 1709055 13873133 := bstep (se 3 (by rfl) ⟨2601212, by rfl⟩ : syracuseStep 13873133 = 5202425) B5202425
theorem B6492383 : Blo 1709055 6492383 := bstep (se 1 (by rfl) ⟨4869287, by rfl⟩ : syracuseStep 6492383 = 9738575) B9738575
theorem B24990029 : Blo 1709055 24990029 := bstep (se 3 (by rfl) ⟨4685630, by rfl⟩ : syracuseStep 24990029 = 9371261) B9371261
theorem B133329361 : Blo 1709055 133329361 := bstep (se 2 (by rfl) ⟨49998510, by rfl⟩ : syracuseStep 133329361 = 99997021) B99997021
theorem B144306917 : Blo 1709055 144306917 := bstep (se 4 (by rfl) ⟨13528773, by rfl⟩ : syracuseStep 144306917 = 27057547) B27057547
theorem B3846995 : Blo 1709055 3846995 := bstep (se 1 (by rfl) ⟨2885246, by rfl⟩ : syracuseStep 3846995 = 5770493) B5770493
theorem B7304033 : Blo 1709055 7304033 := bstep (se 2 (by rfl) ⟨2739012, by rfl⟩ : syracuseStep 7304033 = 5478025) B5478025
theorem B41620553 : Blo 1709055 41620553 := bstep (se 2 (by rfl) ⟨15607707, by rfl⟩ : syracuseStep 41620553 = 31215415) B31215415
theorem B3847355 : Blo 1709055 3847355 := bstep (se 1 (by rfl) ⟨2885516, by rfl⟩ : syracuseStep 3847355 = 5771033) B5771033
theorem B1709279 : Blo 1709055 1709279 := bstep (se 1 (by rfl) ⟨1281959, by rfl⟩ : syracuseStep 1709279 = 2563919) B2563919
theorem B1709311 : Blo 1709055 1709311 := bstep (se 1 (by rfl) ⟨1281983, by rfl⟩ : syracuseStep 1709311 = 2563967) B2563967
theorem B1709359 : Blo 1709055 1709359 := bstep (se 1 (by rfl) ⟨1282019, by rfl⟩ : syracuseStep 1709359 = 2564039) B2564039
theorem B1709519 : Blo 1709055 1709519 := bstep (se 1 (by rfl) ⟨1282139, by rfl⟩ : syracuseStep 1709519 = 2564279) B2564279
theorem B1709599 : Blo 1709055 1709599 := bstep (se 1 (by rfl) ⟨1282199, by rfl⟩ : syracuseStep 1709599 = 2564399) B2564399
theorem B1709759 : Blo 1709055 1709759 := bstep (se 1 (by rfl) ⟨1282319, by rfl⟩ : syracuseStep 1709759 = 2564639) B2564639
theorem B1709799 : Blo 1709055 1709799 := bstep (se 1 (by rfl) ⟨1282349, by rfl⟩ : syracuseStep 1709799 = 2564699) B2564699
theorem B5773031 : Blo 1709055 5773031 := bstep (se 1 (by rfl) ⟨4329773, by rfl⟩ : syracuseStep 5773031 = 8659547) B8659547
theorem B3651419 : Blo 1709055 3651419 := bstep (se 1 (by rfl) ⟨2738564, by rfl⟩ : syracuseStep 3651419 = 5477129) B5477129
theorem B17553257 : Blo 1709055 17553257 := bstep (se 2 (by rfl) ⟨6582471, by rfl⟩ : syracuseStep 17553257 = 13164943) B13164943
theorem B14604239 : Blo 1709055 14604239 := bstep (se 1 (by rfl) ⟨10953179, by rfl⟩ : syracuseStep 14604239 = 21906359) B21906359
theorem B8656955 : Blo 1709055 8656955 := bstep (se 1 (by rfl) ⟨6492716, by rfl⟩ : syracuseStep 8656955 = 12985433) B12985433
theorem B1710143 : Blo 1709055 1710143 := bstep (se 1 (by rfl) ⟨1282607, by rfl⟩ : syracuseStep 1710143 = 2565215) B2565215
theorem B1710183 : Blo 1709055 1710183 := bstep (se 1 (by rfl) ⟨1282637, by rfl⟩ : syracuseStep 1710183 = 2565275) B2565275
theorem B1710491 : Blo 1709055 1710491 := bstep (se 1 (by rfl) ⟨1282868, by rfl⟩ : syracuseStep 1710491 = 2565737) B2565737
theorem B1710575 : Blo 1709055 1710575 := bstep (se 1 (by rfl) ⟨1282931, by rfl⟩ : syracuseStep 1710575 = 2565863) B2565863
theorem B1710639 : Blo 1709055 1710639 := bstep (se 1 (by rfl) ⟨1282979, by rfl⟩ : syracuseStep 1710639 = 2565959) B2565959
theorem B12319303 : Blo 1709055 12319303 := bstep (se 1 (by rfl) ⟨9239477, by rfl⟩ : syracuseStep 12319303 = 18478955) B18478955
theorem B1710911 : Blo 1709055 1710911 := bstep (se 1 (by rfl) ⟨1283183, by rfl⟩ : syracuseStep 1710911 = 2566367) B2566367
theorem B1710951 : Blo 1709055 1710951 := bstep (se 1 (by rfl) ⟨1283213, by rfl⟩ : syracuseStep 1710951 = 2566427) B2566427
theorem B5774219 : Blo 1709055 5774219 := bstep (se 1 (by rfl) ⟨4330664, by rfl⟩ : syracuseStep 5774219 = 8661329) B8661329
theorem B23387039 : Blo 1709055 23387039 := bstep (se 1 (by rfl) ⟨17540279, by rfl⟩ : syracuseStep 23387039 = 35080559) B35080559
theorem B1711039 : Blo 1709055 1711039 := bstep (se 1 (by rfl) ⟨1283279, by rfl⟩ : syracuseStep 1711039 = 2566559) B2566559
theorem B2776175 : Blo 1709055 2776175 := bstep (se 1 (by rfl) ⟨2082131, by rfl⟩ : syracuseStep 2776175 = 4164263) B4164263
theorem B1826111 : Blo 1709055 1826111 := bstep (se 1 (by rfl) ⟨1369583, by rfl⟩ : syracuseStep 1826111 = 2739167) B2739167
theorem B9739601 : Blo 1709055 9739601 := bstep (se 2 (by rfl) ⟨3652350, by rfl⟩ : syracuseStep 9739601 = 7304701) B7304701
theorem B2923867 : Blo 1709055 2923867 := bstep (se 1 (by rfl) ⟨2192900, by rfl⟩ : syracuseStep 2923867 = 4385801) B4385801
theorem B29605463 : Blo 1709055 29605463 := bstep (se 1 (by rfl) ⟨22204097, by rfl⟩ : syracuseStep 29605463 = 44408195) B44408195
theorem B2563739 : Blo 1709055 2563739 := bstep (se 1 (by rfl) ⟨1922804, by rfl⟩ : syracuseStep 2563739 = 3845609) B3845609
theorem B2563775 : Blo 1709055 2563775 := bstep (se 1 (by rfl) ⟨1922831, by rfl⟩ : syracuseStep 2563775 = 3845663) B3845663
theorem B7405337 : Blo 1709055 7405337 := bstep (se 2 (by rfl) ⟨2777001, by rfl⟩ : syracuseStep 7405337 = 5554003) B5554003
theorem B3080063 : Blo 1709055 3080063 := bstep (se 1 (by rfl) ⟨2310047, by rfl⟩ : syracuseStep 3080063 = 4620095) B4620095
theorem B22216879 : Blo 1709055 22216879 := bstep (se 1 (by rfl) ⟨16662659, by rfl⟩ : syracuseStep 22216879 = 33325319) B33325319
theorem B7307759 : Blo 1709055 7307759 := bstep (se 1 (by rfl) ⟨5480819, by rfl⟩ : syracuseStep 7307759 = 10961639) B10961639
theorem B2564663 : Blo 1709055 2564663 := bstep (se 1 (by rfl) ⟨1923497, by rfl⟩ : syracuseStep 2564663 = 3846995) B3846995
theorem B2884187 : Blo 1709055 2884187 := bstep (se 1 (by rfl) ⟨2163140, by rfl⟩ : syracuseStep 2884187 = 4326281) B4326281
theorem B27747035 : Blo 1709055 27747035 := bstep (se 1 (by rfl) ⟨20810276, by rfl⟩ : syracuseStep 27747035 = 41620553) B41620553
theorem B16425737 : Blo 1709055 16425737 := bstep (se 2 (by rfl) ⟨6159651, by rfl⟩ : syracuseStep 16425737 = 12319303) B12319303
theorem B13861651 : Blo 1709055 13861651 := bstep (se 1 (by rfl) ⟨10396238, by rfl⟩ : syracuseStep 13861651 = 20792477) B20792477
theorem B2564903 : Blo 1709055 2564903 := bstep (se 1 (by rfl) ⟨1923677, by rfl⟩ : syracuseStep 2564903 = 3847355) B3847355
theorem B4326473 : Blo 1709055 4326473 := bstep (se 2 (by rfl) ⟨1622427, by rfl⟩ : syracuseStep 4326473 = 3244855) B3244855
theorem B19481795 : Blo 1709055 19481795 := bstep (se 1 (by rfl) ⟨14611346, by rfl⟩ : syracuseStep 19481795 = 29222693) B29222693
theorem B2737655 : Blo 1709055 2737655 := bstep (se 1 (by rfl) ⟨2053241, by rfl⟩ : syracuseStep 2737655 = 4106483) B4106483
theorem B2164315 : Blo 1709055 2164315 := bstep (se 1 (by rfl) ⟨1623236, by rfl⟩ : syracuseStep 2164315 = 3246473) B3246473
theorem B2885375 : Blo 1709055 2885375 := bstep (se 1 (by rfl) ⟨2164031, by rfl⟩ : syracuseStep 2885375 = 4328063) B4328063
theorem B2312059 : Blo 1709055 2312059 := bstep (se 1 (by rfl) ⟨1734044, by rfl⟩ : syracuseStep 2312059 = 3468089) B3468089
theorem B15591359 : Blo 1709055 15591359 := bstep (se 1 (by rfl) ⟨11693519, by rfl⟩ : syracuseStep 15591359 = 23387039) B23387039
theorem B21923945 : Blo 1709055 21923945 := bstep (se 2 (by rfl) ⟨8221479, by rfl⟩ : syracuseStep 21923945 = 16442959) B16442959
theorem B19736975 : Blo 1709055 19736975 := bstep (se 1 (by rfl) ⟨14802731, by rfl⟩ : syracuseStep 19736975 = 29605463) B29605463
theorem B2886043 : Blo 1709055 2886043 := bstep (se 1 (by rfl) ⟨2164532, by rfl⟩ : syracuseStep 2886043 = 4329065) B4329065
theorem B6490651 : Blo 1709055 6490651 := bstep (se 1 (by rfl) ⟨4867988, by rfl⟩ : syracuseStep 6490651 = 9735977) B9735977
theorem B3246905 : Blo 1709055 3246905 := bstep (se 2 (by rfl) ⟨1217589, by rfl⟩ : syracuseStep 3246905 = 2435179) B2435179
theorem B4328255 : Blo 1709055 4328255 := bstep (se 1 (by rfl) ⟨3246191, by rfl⟩ : syracuseStep 4328255 = 6492383) B6492383
theorem B4328417 : Blo 1709055 4328417 := bstep (se 2 (by rfl) ⟨1623156, by rfl⟩ : syracuseStep 4328417 = 3246313) B3246313
theorem B4107289 : Blo 1709055 4107289 := bstep (se 2 (by rfl) ⟨1540233, by rfl⟩ : syracuseStep 4107289 = 3080467) B3080467
theorem B9743449 : Blo 1709055 9743449 := bstep (se 2 (by rfl) ⟨3653793, by rfl⟩ : syracuseStep 9743449 = 7307587) B7307587
theorem B48065843 : Blo 1709055 48065843 := bstep (se 1 (by rfl) ⟨36049382, by rfl⟩ : syracuseStep 48065843 = 72098765) B72098765
theorem B4869629 : Blo 1709055 4869629 := bstep (se 3 (by rfl) ⟨913055, by rfl⟩ : syracuseStep 4869629 = 1826111) B1826111
theorem B3845897 : Blo 1709055 3845897 := bstep (se 2 (by rfl) ⟨1442211, by rfl⟩ : syracuseStep 3845897 = 2884423) B2884423
theorem B11702171 : Blo 1709055 11702171 := bstep (se 1 (by rfl) ⟨8776628, by rfl⟩ : syracuseStep 11702171 = 17553257) B17553257
theorem B9736159 : Blo 1709055 9736159 := bstep (se 1 (by rfl) ⟨7302119, by rfl⟩ : syracuseStep 9736159 = 14604239) B14604239
theorem B5771303 : Blo 1709055 5771303 := bstep (se 1 (by rfl) ⟨4328477, by rfl⟩ : syracuseStep 5771303 = 8656955) B8656955
theorem B15593957 : Blo 1709055 15593957 := bstep (se 4 (by rfl) ⟨1461933, by rfl⟩ : syracuseStep 15593957 = 2923867) B2923867
theorem B3846635 : Blo 1709055 3846635 := bstep (se 1 (by rfl) ⟨2884976, by rfl⟩ : syracuseStep 3846635 = 5769953) B5769953
theorem B3846887 : Blo 1709055 3846887 := bstep (se 1 (by rfl) ⟨2885165, by rfl⟩ : syracuseStep 3846887 = 5770331) B5770331
theorem B6091631 : Blo 1709055 6091631 := bstep (se 1 (by rfl) ⟨4568723, by rfl⟩ : syracuseStep 6091631 = 9137447) B9137447
theorem B6493067 : Blo 1709055 6493067 := bstep (se 1 (by rfl) ⟨4869800, by rfl⟩ : syracuseStep 6493067 = 9739601) B9739601
theorem B9737117 : Blo 1709055 9737117 := bstep (se 3 (by rfl) ⟨1825709, by rfl⟩ : syracuseStep 9737117 = 3651419) B3651419
theorem B19477421 : Blo 1709055 19477421 := bstep (se 3 (by rfl) ⟨3652016, by rfl⟩ : syracuseStep 19477421 = 7304033) B7304033
theorem B8213501 : Blo 1709055 8213501 := bstep (se 3 (by rfl) ⟨1540031, by rfl⟩ : syracuseStep 8213501 = 3080063) B3080063
theorem B1709159 : Blo 1709055 1709159 := bstep (se 1 (by rfl) ⟨1281869, by rfl⟩ : syracuseStep 1709159 = 2563739) B2563739
theorem B1709183 : Blo 1709055 1709183 := bstep (se 1 (by rfl) ⟨1281887, by rfl⟩ : syracuseStep 1709183 = 2563775) B2563775
theorem B4936891 : Blo 1709055 4936891 := bstep (se 1 (by rfl) ⟨3702668, by rfl⟩ : syracuseStep 4936891 = 7405337) B7405337
theorem B6493567 : Blo 1709055 6493567 := bstep (se 1 (by rfl) ⟨4870175, by rfl⟩ : syracuseStep 6493567 = 9740351) B9740351
theorem B35108321 : Blo 1709055 35108321 := bstep (se 2 (by rfl) ⟨13165620, by rfl⟩ : syracuseStep 35108321 = 26331241) B26331241
theorem B29218319 : Blo 1709055 29218319 := bstep (se 1 (by rfl) ⟨21913739, by rfl⟩ : syracuseStep 29218319 = 43827479) B43827479
theorem B1709595 : Blo 1709055 1709595 := bstep (se 1 (by rfl) ⟨1282196, by rfl⟩ : syracuseStep 1709595 = 2564393) B2564393
theorem B16660019 : Blo 1709055 16660019 := bstep (se 1 (by rfl) ⟨12495014, by rfl⟩ : syracuseStep 16660019 = 24990029) B24990029
theorem B96204611 : Blo 1709055 96204611 := bstep (se 1 (by rfl) ⟨72153458, by rfl⟩ : syracuseStep 96204611 = 144306917) B144306917
theorem B177772481 : Blo 1709055 177772481 := bstep (se 2 (by rfl) ⟨66664680, by rfl⟩ : syracuseStep 177772481 = 133329361) B133329361
theorem B1710171 : Blo 1709055 1710171 := bstep (se 1 (by rfl) ⟨1282628, by rfl⟩ : syracuseStep 1710171 = 2565257) B2565257
theorem B1710363 : Blo 1709055 1710363 := bstep (se 1 (by rfl) ⟨1282772, by rfl⟩ : syracuseStep 1710363 = 2565545) B2565545
theorem B1710559 : Blo 1709055 1710559 := bstep (se 1 (by rfl) ⟨1282919, by rfl⟩ : syracuseStep 1710559 = 2565839) B2565839
theorem B3848687 : Blo 1709055 3848687 := bstep (se 1 (by rfl) ⟨2886515, by rfl⟩ : syracuseStep 3848687 = 5773031) B5773031
theorem B5479103 : Blo 1709055 5479103 := bstep (se 1 (by rfl) ⟨4109327, by rfl⟩ : syracuseStep 5479103 = 8218655) B8218655
theorem B1710975 : Blo 1709055 1710975 := bstep (se 1 (by rfl) ⟨1283231, by rfl⟩ : syracuseStep 1710975 = 2566463) B2566463
theorem B8657927 : Blo 1709055 8657927 := bstep (se 1 (by rfl) ⟨6493445, by rfl⟩ : syracuseStep 8657927 = 12986891) B12986891
theorem B3849479 : Blo 1709055 3849479 := bstep (se 1 (by rfl) ⟨2887109, by rfl⟩ : syracuseStep 3849479 = 5774219) B5774219
theorem B1850783 : Blo 1709055 1850783 := bstep (se 1 (by rfl) ⟨1388087, by rfl⟩ : syracuseStep 1850783 = 2776175) B2776175
theorem B1924591 : Blo 1709055 1924591 := bstep (se 1 (by rfl) ⟨1443443, by rfl⟩ : syracuseStep 1924591 = 2886887) B2886887
theorem B5201405 : Blo 1709055 5201405 := bstep (se 3 (by rfl) ⟨975263, by rfl⟩ : syracuseStep 5201405 = 1950527) B1950527
theorem B2563631 : Blo 1709055 2563631 := bstep (se 1 (by rfl) ⟨1922723, by rfl⟩ : syracuseStep 2563631 = 3845447) B3845447
theorem B6495815 : Blo 1709055 6495815 := bstep (se 1 (by rfl) ⟨4871861, by rfl⟩ : syracuseStep 6495815 = 9743723) B9743723
theorem B9248755 : Blo 1709055 9248755 := bstep (se 1 (by rfl) ⟨6936566, by rfl⟩ : syracuseStep 9248755 = 13873133) B13873133
theorem B29622505 : Blo 1709055 29622505 := bstep (se 2 (by rfl) ⟨11108439, by rfl⟩ : syracuseStep 29622505 = 22216879) B22216879
theorem B10395971 : Blo 1709055 10395971 := bstep (se 1 (by rfl) ⟨7796978, by rfl⟩ : syracuseStep 10395971 = 15593957) B15593957
theorem B2564423 : Blo 1709055 2564423 := bstep (se 1 (by rfl) ⟨1923317, by rfl⟩ : syracuseStep 2564423 = 3846635) B3846635
theorem B18498023 : Blo 1709055 18498023 := bstep (se 1 (by rfl) ⟨13873517, by rfl⟩ : syracuseStep 18498023 = 27747035) B27747035
theorem B2564591 : Blo 1709055 2564591 := bstep (se 1 (by rfl) ⟨1923443, by rfl⟩ : syracuseStep 2564591 = 3846887) B3846887
theorem B12984947 : Blo 1709055 12984947 := bstep (se 1 (by rfl) ⟨9738710, by rfl⟩ : syracuseStep 12984947 = 19477421) B19477421
theorem B2884315 : Blo 1709055 2884315 := bstep (se 1 (by rfl) ⟨2163236, by rfl⟩ : syracuseStep 2884315 = 4326473) B4326473
theorem B18482201 : Blo 1709055 18482201 := bstep (se 2 (by rfl) ⟨6930825, by rfl⟩ : syracuseStep 18482201 = 13861651) B13861651
theorem B64136407 : Blo 1709055 64136407 := bstep (se 1 (by rfl) ⟨48102305, by rfl⟩ : syracuseStep 64136407 = 96204611) B96204611
theorem B118514987 : Blo 1709055 118514987 := bstep (se 1 (by rfl) ⟨88886240, by rfl⟩ : syracuseStep 118514987 = 177772481) B177772481
theorem B14615963 : Blo 1709055 14615963 := bstep (se 1 (by rfl) ⟨10961972, by rfl⟩ : syracuseStep 14615963 = 21923945) B21923945
theorem B44426717 : Blo 1709055 44426717 := bstep (se 3 (by rfl) ⟨8330009, by rfl⟩ : syracuseStep 44426717 = 16660019) B16660019
theorem B13157983 : Blo 1709055 13157983 := bstep (se 1 (by rfl) ⟨9868487, by rfl⟩ : syracuseStep 13157983 = 19736975) B19736975
theorem B2565791 : Blo 1709055 2565791 := bstep (se 1 (by rfl) ⟨1924343, by rfl⟩ : syracuseStep 2565791 = 3848687) B3848687
theorem B2885503 : Blo 1709055 2885503 := bstep (se 1 (by rfl) ⟨2164127, by rfl⟩ : syracuseStep 2885503 = 4328255) B4328255
theorem B2566121 : Blo 1709055 2566121 := bstep (se 2 (by rfl) ⟨962295, by rfl⟩ : syracuseStep 2566121 = 1924591) B1924591
theorem B2885611 : Blo 1709055 2885611 := bstep (se 1 (by rfl) ⟨2164208, by rfl⟩ : syracuseStep 2885611 = 4328417) B4328417
theorem B2885753 : Blo 1709055 2885753 := bstep (se 2 (by rfl) ⟨1082157, by rfl⟩ : syracuseStep 2885753 = 2164315) B2164315
theorem B2566319 : Blo 1709055 2566319 := bstep (se 1 (by rfl) ⟨1924739, by rfl⟩ : syracuseStep 2566319 = 3849479) B3849479
theorem B3246419 : Blo 1709055 3246419 := bstep (se 1 (by rfl) ⟨2434814, by rfl⟩ : syracuseStep 3246419 = 4869629) B4869629
theorem B3467603 : Blo 1709055 3467603 := bstep (se 1 (by rfl) ⟨2600702, by rfl⟩ : syracuseStep 3467603 = 5201405) B5201405
theorem B3082745 : Blo 1709055 3082745 := bstep (se 2 (by rfl) ⟨1156029, by rfl⟩ : syracuseStep 3082745 = 2312059) B2312059
theorem B7801447 : Blo 1709055 7801447 := bstep (se 1 (by rfl) ⟨5851085, by rfl⟩ : syracuseStep 7801447 = 11702171) B11702171
theorem B12331673 : Blo 1709055 12331673 := bstep (se 2 (by rfl) ⟨4624377, by rfl⟩ : syracuseStep 12331673 = 9248755) B9248755
theorem B4328711 : Blo 1709055 4328711 := bstep (se 1 (by rfl) ⟨3246533, by rfl⟩ : syracuseStep 4328711 = 6493067) B6493067
theorem B6491411 : Blo 1709055 6491411 := bstep (se 1 (by rfl) ⟨4868558, by rfl⟩ : syracuseStep 6491411 = 9737117) B9737117
theorem B8654201 : Blo 1709055 8654201 := bstep (se 2 (by rfl) ⟨3245325, by rfl⟩ : syracuseStep 8654201 = 6490651) B6490651
theorem B12987863 : Blo 1709055 12987863 := bstep (se 1 (by rfl) ⟨9740897, by rfl⟩ : syracuseStep 12987863 = 19481795) B19481795
theorem B128175581 : Blo 1709055 128175581 := bstep (se 3 (by rfl) ⟨24032921, by rfl⟩ : syracuseStep 128175581 = 48065843) B48065843
theorem B4935421 : Blo 1709055 4935421 := bstep (se 3 (by rfl) ⟨925391, by rfl⟩ : syracuseStep 4935421 = 1850783) B1850783
theorem B93622189 : Blo 1709055 93622189 := bstep (se 3 (by rfl) ⟨17554160, by rfl⟩ : syracuseStep 93622189 = 35108321) B35108321
theorem B5476385 : Blo 1709055 5476385 := bstep (se 2 (by rfl) ⟨2053644, by rfl⟩ : syracuseStep 5476385 = 4107289) B4107289
theorem B6582521 : Blo 1709055 6582521 := bstep (se 2 (by rfl) ⟨2468445, by rfl⟩ : syracuseStep 6582521 = 4936891) B4936891
theorem B5771951 : Blo 1709055 5771951 := bstep (se 1 (by rfl) ⟨4328963, by rfl⟩ : syracuseStep 5771951 = 8657927) B8657927
theorem B1709087 : Blo 1709055 1709087 := bstep (se 1 (by rfl) ⟨1281815, by rfl⟩ : syracuseStep 1709087 = 2563631) B2563631
theorem B4330543 : Blo 1709055 4330543 := bstep (se 1 (by rfl) ⟨3247907, by rfl⟩ : syracuseStep 4330543 = 6495815) B6495815
theorem B12981545 : Blo 1709055 12981545 := bstep (se 2 (by rfl) ⟨4868079, by rfl⟩ : syracuseStep 12981545 = 9736159) B9736159
theorem B21902669 : Blo 1709055 21902669 := bstep (se 3 (by rfl) ⟨4106750, by rfl⟩ : syracuseStep 21902669 = 8213501) B8213501
theorem B3847535 : Blo 1709055 3847535 := bstep (se 1 (by rfl) ⟨2885651, by rfl⟩ : syracuseStep 3847535 = 5771303) B5771303
theorem B4871839 : Blo 1709055 4871839 := bstep (se 1 (by rfl) ⟨3653879, by rfl⟩ : syracuseStep 4871839 = 7307759) B7307759
theorem B1709775 : Blo 1709055 1709775 := bstep (se 1 (by rfl) ⟨1282331, by rfl⟩ : syracuseStep 1709775 = 2564663) B2564663
theorem B1922791 : Blo 1709055 1922791 := bstep (se 1 (by rfl) ⟨1442093, by rfl⟩ : syracuseStep 1922791 = 2884187) B2884187
theorem B10950491 : Blo 1709055 10950491 := bstep (se 1 (by rfl) ⟨8212868, by rfl⟩ : syracuseStep 10950491 = 16425737) B16425737
theorem B1709935 : Blo 1709055 1709935 := bstep (se 1 (by rfl) ⟨1282451, by rfl⟩ : syracuseStep 1709935 = 2564903) B2564903
theorem B3848057 : Blo 1709055 3848057 := bstep (se 2 (by rfl) ⟨1443021, by rfl⟩ : syracuseStep 3848057 = 2886043) B2886043
theorem B4061087 : Blo 1709055 4061087 := bstep (se 1 (by rfl) ⟨3045815, by rfl⟩ : syracuseStep 4061087 = 6091631) B6091631
theorem B1825103 : Blo 1709055 1825103 := bstep (se 1 (by rfl) ⟨1368827, by rfl⟩ : syracuseStep 1825103 = 2737655) B2737655
theorem B19478879 : Blo 1709055 19478879 := bstep (se 1 (by rfl) ⟨14609159, by rfl⟩ : syracuseStep 19478879 = 29218319) B29218319
theorem B1923583 : Blo 1709055 1923583 := bstep (se 1 (by rfl) ⟨1442687, by rfl⟩ : syracuseStep 1923583 = 2885375) B2885375
theorem B10394239 : Blo 1709055 10394239 := bstep (se 1 (by rfl) ⟨7795679, by rfl⟩ : syracuseStep 10394239 = 15591359) B15591359
theorem B12991265 : Blo 1709055 12991265 := bstep (se 2 (by rfl) ⟨4871724, by rfl⟩ : syracuseStep 12991265 = 9743449) B9743449
theorem B3652735 : Blo 1709055 3652735 := bstep (se 1 (by rfl) ⟨2739551, by rfl⟩ : syracuseStep 3652735 = 5479103) B5479103
theorem B8658089 : Blo 1709055 8658089 := bstep (se 2 (by rfl) ⟨3246783, by rfl⟩ : syracuseStep 8658089 = 6493567) B6493567
theorem B8658413 : Blo 1709055 8658413 := bstep (se 3 (by rfl) ⟨1623452, by rfl⟩ : syracuseStep 8658413 = 3246905) B3246905
theorem B2563931 : Blo 1709055 2563931 := bstep (se 1 (by rfl) ⟨1922948, by rfl⟩ : syracuseStep 2563931 = 3845897) B3845897
theorem B6930647 : Blo 1709055 6930647 := bstep (se 1 (by rfl) ⟨5197985, by rfl⟩ : syracuseStep 6930647 = 10395971) B10395971
theorem B2564777 : Blo 1709055 2564777 := bstep (se 2 (by rfl) ⟨961791, by rfl⟩ : syracuseStep 2564777 = 1923583) B1923583
theorem B12321467 : Blo 1709055 12321467 := bstep (se 1 (by rfl) ⟨9241100, by rfl⟩ : syracuseStep 12321467 = 18482201) B18482201
theorem B4866941 : Blo 1709055 4866941 := bstep (se 3 (by rfl) ⟨912551, by rfl⟩ : syracuseStep 4866941 = 1825103) B1825103
theorem B2565023 : Blo 1709055 2565023 := bstep (se 1 (by rfl) ⟨1923767, by rfl⟩ : syracuseStep 2565023 = 3847535) B3847535
theorem B7300327 : Blo 1709055 7300327 := bstep (se 1 (by rfl) ⟨5475245, by rfl⟩ : syracuseStep 7300327 = 10950491) B10950491
theorem B2565371 : Blo 1709055 2565371 := bstep (se 1 (by rfl) ⟨1924028, by rfl⟩ : syracuseStep 2565371 = 3848057) B3848057
theorem B26322245 : Blo 1709055 26322245 := bstep (se 4 (by rfl) ⟨2467710, by rfl⟩ : syracuseStep 26322245 = 4935421) B4935421
theorem B2311735 : Blo 1709055 2311735 := bstep (se 1 (by rfl) ⟨1733801, by rfl⟩ : syracuseStep 2311735 = 3467603) B3467603
theorem B12985919 : Blo 1709055 12985919 := bstep (se 1 (by rfl) ⟨9739439, by rfl⟩ : syracuseStep 12985919 = 19478879) B19478879
theorem B8660843 : Blo 1709055 8660843 := bstep (se 1 (by rfl) ⟨6495632, by rfl⟩ : syracuseStep 8660843 = 12991265) B12991265
theorem B2885807 : Blo 1709055 2885807 := bstep (se 1 (by rfl) ⟨2164355, by rfl⟩ : syracuseStep 2885807 = 4328711) B4328711
theorem B4327607 : Blo 1709055 4327607 := bstep (se 1 (by rfl) ⟨3245705, by rfl⟩ : syracuseStep 4327607 = 6491411) B6491411
theorem B5769467 : Blo 1709055 5769467 := bstep (se 1 (by rfl) ⟨4327100, by rfl⟩ : syracuseStep 5769467 = 8654201) B8654201
theorem B39496673 : Blo 1709055 39496673 := bstep (se 2 (by rfl) ⟨14811252, by rfl⟩ : syracuseStep 39496673 = 29622505) B29622505
theorem B12332015 : Blo 1709055 12332015 := bstep (se 1 (by rfl) ⟨9249011, by rfl⟩ : syracuseStep 12332015 = 18498023) B18498023
theorem B70175909 : Blo 1709055 70175909 := bstep (se 4 (by rfl) ⟨6578991, by rfl⟩ : syracuseStep 70175909 = 13157983) B13157983
theorem B8654363 : Blo 1709055 8654363 := bstep (se 1 (by rfl) ⟨6490772, by rfl⟩ : syracuseStep 8654363 = 12981545) B12981545
theorem B14601779 : Blo 1709055 14601779 := bstep (se 1 (by rfl) ⟨10951334, by rfl⟩ : syracuseStep 14601779 = 21902669) B21902669
theorem B9743975 : Blo 1709055 9743975 := bstep (se 1 (by rfl) ⟨7307981, by rfl⟩ : syracuseStep 9743975 = 14615963) B14615963
theorem B3845753 : Blo 1709055 3845753 := bstep (se 2 (by rfl) ⟨1442157, by rfl⟩ : syracuseStep 3845753 = 2884315) B2884315
theorem B29617811 : Blo 1709055 29617811 := bstep (se 1 (by rfl) ⟨22213358, by rfl⟩ : syracuseStep 29617811 = 44426717) B44426717
theorem B2707391 : Blo 1709055 2707391 := bstep (se 1 (by rfl) ⟨2030543, by rfl⟩ : syracuseStep 2707391 = 4061087) B4061087
theorem B8220653 : Blo 1709055 8220653 := bstep (se 3 (by rfl) ⟨1541372, by rfl⟩ : syracuseStep 8220653 = 3082745) B3082745
theorem B4870313 : Blo 1709055 4870313 := bstep (se 2 (by rfl) ⟨1826367, by rfl⟩ : syracuseStep 4870313 = 3652735) B3652735
theorem B8221115 : Blo 1709055 8221115 := bstep (se 1 (by rfl) ⟨6165836, by rfl⟩ : syracuseStep 8221115 = 12331673) B12331673
theorem B5772059 : Blo 1709055 5772059 := bstep (se 1 (by rfl) ⟨4329044, by rfl⟩ : syracuseStep 5772059 = 8658089) B8658089
theorem B5772275 : Blo 1709055 5772275 := bstep (se 1 (by rfl) ⟨4329206, by rfl⟩ : syracuseStep 5772275 = 8658413) B8658413
theorem B3847337 : Blo 1709055 3847337 := bstep (se 2 (by rfl) ⟨1442751, by rfl⟩ : syracuseStep 3847337 = 2885503) B2885503
theorem B1709287 : Blo 1709055 1709287 := bstep (se 1 (by rfl) ⟨1281965, by rfl⟩ : syracuseStep 1709287 = 2563931) B2563931
theorem B3847481 : Blo 1709055 3847481 := bstep (se 2 (by rfl) ⟨1442805, by rfl⟩ : syracuseStep 3847481 = 2885611) B2885611
theorem B3650923 : Blo 1709055 3650923 := bstep (se 1 (by rfl) ⟨2738192, by rfl⟩ : syracuseStep 3650923 = 5476385) B5476385
theorem B4388347 : Blo 1709055 4388347 := bstep (se 1 (by rfl) ⟨3291260, by rfl⟩ : syracuseStep 4388347 = 6582521) B6582521
theorem B1709615 : Blo 1709055 1709615 := bstep (se 1 (by rfl) ⟨1282211, by rfl⟩ : syracuseStep 1709615 = 2564423) B2564423
theorem B1709727 : Blo 1709055 1709727 := bstep (se 1 (by rfl) ⟨1282295, by rfl⟩ : syracuseStep 1709727 = 2564591) B2564591
theorem B8656631 : Blo 1709055 8656631 := bstep (se 1 (by rfl) ⟨6492473, by rfl⟩ : syracuseStep 8656631 = 12984947) B12984947
theorem B3847967 : Blo 1709055 3847967 := bstep (se 1 (by rfl) ⟨2885975, by rfl⟩ : syracuseStep 3847967 = 5771951) B5771951
theorem B10401929 : Blo 1709055 10401929 := bstep (se 2 (by rfl) ⟨3900723, by rfl⟩ : syracuseStep 10401929 = 7801447) B7801447
theorem B13858985 : Blo 1709055 13858985 := bstep (se 2 (by rfl) ⟨5197119, by rfl⟩ : syracuseStep 13858985 = 10394239) B10394239
theorem B79009991 : Blo 1709055 79009991 := bstep (se 1 (by rfl) ⟨59257493, by rfl⟩ : syracuseStep 79009991 = 118514987) B118514987
theorem B8657117 : Blo 1709055 8657117 := bstep (se 3 (by rfl) ⟨1623209, by rfl⟩ : syracuseStep 8657117 = 3246419) B3246419
theorem B1710527 : Blo 1709055 1710527 := bstep (se 1 (by rfl) ⟨1282895, by rfl⟩ : syracuseStep 1710527 = 2565791) B2565791
theorem B341801549 : Blo 1709055 341801549 := bstep (se 3 (by rfl) ⟨64087790, by rfl⟩ : syracuseStep 341801549 = 128175581) B128175581
theorem B1710747 : Blo 1709055 1710747 := bstep (se 1 (by rfl) ⟨1283060, by rfl⟩ : syracuseStep 1710747 = 2566121) B2566121
theorem B5774057 : Blo 1709055 5774057 := bstep (se 2 (by rfl) ⟨2165271, by rfl⟩ : syracuseStep 5774057 = 4330543) B4330543
theorem B1923835 : Blo 1709055 1923835 := bstep (se 1 (by rfl) ⟨1442876, by rfl⟩ : syracuseStep 1923835 = 2885753) B2885753
theorem B1710879 : Blo 1709055 1710879 := bstep (se 1 (by rfl) ⟨1283159, by rfl⟩ : syracuseStep 1710879 = 2566319) B2566319
theorem B85515209 : Blo 1709055 85515209 := bstep (se 2 (by rfl) ⟨32068203, by rfl⟩ : syracuseStep 85515209 = 64136407) B64136407
theorem B6495785 : Blo 1709055 6495785 := bstep (se 2 (by rfl) ⟨2435919, by rfl⟩ : syracuseStep 6495785 = 4871839) B4871839
theorem B2563721 : Blo 1709055 2563721 := bstep (se 2 (by rfl) ⟨961395, by rfl⟩ : syracuseStep 2563721 = 1922791) B1922791
theorem B8658575 : Blo 1709055 8658575 := bstep (se 1 (by rfl) ⟨6493931, by rfl⟩ : syracuseStep 8658575 = 12987863) B12987863
theorem B124829585 : Blo 1709055 124829585 := bstep (se 2 (by rfl) ⟨46811094, by rfl⟩ : syracuseStep 124829585 = 93622189) B93622189
theorem B4620431 : Blo 1709055 4620431 := bstep (se 1 (by rfl) ⟨3465323, by rfl⟩ : syracuseStep 4620431 = 6930647) B6930647
theorem B5480743 : Blo 1709055 5480743 := bstep (se 1 (by rfl) ⟨4110557, by rfl⟩ : syracuseStep 5480743 = 8221115) B8221115
theorem B3244627 : Blo 1709055 3244627 := bstep (se 1 (by rfl) ⟨2433470, by rfl⟩ : syracuseStep 3244627 = 4866941) B4866941
theorem B2564891 : Blo 1709055 2564891 := bstep (se 1 (by rfl) ⟨1923668, by rfl⟩ : syracuseStep 2564891 = 3847337) B3847337
theorem B2564987 : Blo 1709055 2564987 := bstep (se 1 (by rfl) ⟨1923740, by rfl⟩ : syracuseStep 2564987 = 3847481) B3847481
theorem B17548163 : Blo 1709055 17548163 := bstep (se 1 (by rfl) ⟨13161122, by rfl⟩ : syracuseStep 17548163 = 26322245) B26322245
theorem B2565113 : Blo 1709055 2565113 := bstep (se 2 (by rfl) ⟨961917, by rfl⟩ : syracuseStep 2565113 = 1923835) B1923835
theorem B2565311 : Blo 1709055 2565311 := bstep (se 1 (by rfl) ⟨1923983, by rfl⟩ : syracuseStep 2565311 = 3847967) B3847967
theorem B2885071 : Blo 1709055 2885071 := bstep (se 1 (by rfl) ⟨2163803, by rfl⟩ : syracuseStep 2885071 = 4327607) B4327607
theorem B9733769 : Blo 1709055 9733769 := bstep (se 2 (by rfl) ⟨3650163, by rfl⟩ : syracuseStep 9733769 = 7300327) B7300327
theorem B57010139 : Blo 1709055 57010139 := bstep (se 1 (by rfl) ⟨42757604, by rfl⟩ : syracuseStep 57010139 = 85515209) B85515209
theorem B26331115 : Blo 1709055 26331115 := bstep (se 1 (by rfl) ⟨19748336, by rfl⟩ : syracuseStep 26331115 = 39496673) B39496673
theorem B5851129 : Blo 1709055 5851129 := bstep (se 2 (by rfl) ⟨2194173, by rfl⟩ : syracuseStep 5851129 = 4388347) B4388347
theorem B3082313 : Blo 1709055 3082313 := bstep (se 2 (by rfl) ⟨1155867, by rfl⟩ : syracuseStep 3082313 = 2311735) B2311735
theorem B5769575 : Blo 1709055 5769575 := bstep (se 1 (by rfl) ⟨4327181, by rfl⟩ : syracuseStep 5769575 = 8654363) B8654363
theorem B9734519 : Blo 1709055 9734519 := bstep (se 1 (by rfl) ⟨7300889, by rfl⟩ : syracuseStep 9734519 = 14601779) B14601779
theorem B19745207 : Blo 1709055 19745207 := bstep (se 1 (by rfl) ⟨14808905, by rfl⟩ : syracuseStep 19745207 = 29617811) B29617811
theorem B7219709 : Blo 1709055 7219709 := bstep (se 3 (by rfl) ⟨1353695, by rfl⟩ : syracuseStep 7219709 = 2707391) B2707391
theorem B3246875 : Blo 1709055 3246875 := bstep (se 1 (by rfl) ⟨2435156, by rfl⟩ : syracuseStep 3246875 = 4870313) B4870313
theorem B36957293 : Blo 1709055 36957293 := bstep (se 3 (by rfl) ⟨6929492, by rfl⟩ : syracuseStep 36957293 = 13858985) B13858985
theorem B5771087 : Blo 1709055 5771087 := bstep (se 1 (by rfl) ⟨4328315, by rfl⟩ : syracuseStep 5771087 = 8656631) B8656631
theorem B6934619 : Blo 1709055 6934619 := bstep (se 1 (by rfl) ⟨5200964, by rfl⟩ : syracuseStep 6934619 = 10401929) B10401929
theorem B5771411 : Blo 1709055 5771411 := bstep (se 1 (by rfl) ⟨4328558, by rfl⟩ : syracuseStep 5771411 = 8657117) B8657117
theorem B3846311 : Blo 1709055 3846311 := bstep (se 1 (by rfl) ⟨2884733, by rfl⟩ : syracuseStep 3846311 = 5769467) B5769467
theorem B8221343 : Blo 1709055 8221343 := bstep (se 1 (by rfl) ⟨6166007, by rfl⟩ : syracuseStep 8221343 = 12332015) B12332015
theorem B4330523 : Blo 1709055 4330523 := bstep (se 1 (by rfl) ⟨3247892, by rfl⟩ : syracuseStep 4330523 = 6495785) B6495785
theorem B1709147 : Blo 1709055 1709147 := bstep (se 1 (by rfl) ⟨1281860, by rfl⟩ : syracuseStep 1709147 = 2563721) B2563721
theorem B5772383 : Blo 1709055 5772383 := bstep (se 1 (by rfl) ⟨4329287, by rfl⟩ : syracuseStep 5772383 = 8658575) B8658575
theorem B83219723 : Blo 1709055 83219723 := bstep (se 1 (by rfl) ⟨62414792, by rfl⟩ : syracuseStep 83219723 = 124829585) B124829585
theorem B1709851 : Blo 1709055 1709851 := bstep (se 1 (by rfl) ⟨1282388, by rfl⟩ : syracuseStep 1709851 = 2564777) B2564777
theorem B8214311 : Blo 1709055 8214311 := bstep (se 1 (by rfl) ⟨6160733, by rfl⟩ : syracuseStep 8214311 = 12321467) B12321467
theorem B3848039 : Blo 1709055 3848039 := bstep (se 1 (by rfl) ⟨2886029, by rfl⟩ : syracuseStep 3848039 = 5772059) B5772059
theorem B1710015 : Blo 1709055 1710015 := bstep (se 1 (by rfl) ⟨1282511, by rfl⟩ : syracuseStep 1710015 = 2565023) B2565023
theorem B3848183 : Blo 1709055 3848183 := bstep (se 1 (by rfl) ⟨2886137, by rfl⟩ : syracuseStep 3848183 = 5772275) B5772275
theorem B1710247 : Blo 1709055 1710247 := bstep (se 1 (by rfl) ⟨1282685, by rfl⟩ : syracuseStep 1710247 = 2565371) B2565371
theorem B8657279 : Blo 1709055 8657279 := bstep (se 1 (by rfl) ⟨6492959, by rfl⟩ : syracuseStep 8657279 = 12985919) B12985919
theorem B5773895 : Blo 1709055 5773895 := bstep (se 1 (by rfl) ⟨4330421, by rfl⟩ : syracuseStep 5773895 = 8660843) B8660843
theorem B1923871 : Blo 1709055 1923871 := bstep (se 1 (by rfl) ⟨1442903, by rfl⟩ : syracuseStep 1923871 = 2885807) B2885807
theorem B52673327 : Blo 1709055 52673327 := bstep (se 1 (by rfl) ⟨39504995, by rfl⟩ : syracuseStep 52673327 = 79009991) B79009991
theorem B227867699 : Blo 1709055 227867699 := bstep (se 1 (by rfl) ⟨170900774, by rfl⟩ : syracuseStep 227867699 = 341801549) B341801549
theorem B3849371 : Blo 1709055 3849371 := bstep (se 1 (by rfl) ⟨2887028, by rfl⟩ : syracuseStep 3849371 = 5774057) B5774057
theorem B19471589 : Blo 1709055 19471589 := bstep (se 4 (by rfl) ⟨1825461, by rfl⟩ : syracuseStep 19471589 = 3650923) B3650923
theorem B46783939 : Blo 1709055 46783939 := bstep (se 1 (by rfl) ⟨35087954, by rfl⟩ : syracuseStep 46783939 = 70175909) B70175909
theorem B6495983 : Blo 1709055 6495983 := bstep (se 1 (by rfl) ⟨4871987, by rfl⟩ : syracuseStep 6495983 = 9743975) B9743975
theorem B2563835 : Blo 1709055 2563835 := bstep (se 1 (by rfl) ⟨1922876, by rfl⟩ : syracuseStep 2563835 = 3845753) B3845753
theorem B5480435 : Blo 1709055 5480435 := bstep (se 1 (by rfl) ⟨4110326, by rfl⟩ : syracuseStep 5480435 = 8220653) B8220653
theorem B3080287 : Blo 1709055 3080287 := bstep (se 1 (by rfl) ⟨2310215, by rfl⟩ : syracuseStep 3080287 = 4620431) B4620431
theorem B2564207 : Blo 1709055 2564207 := bstep (se 1 (by rfl) ⟨1923155, by rfl⟩ : syracuseStep 2564207 = 3846311) B3846311
theorem B7307657 : Blo 1709055 7307657 := bstep (se 2 (by rfl) ⟨2740371, by rfl⟩ : syracuseStep 7307657 = 5480743) B5480743
theorem B11698775 : Blo 1709055 11698775 := bstep (se 1 (by rfl) ⟨8774081, by rfl⟩ : syracuseStep 11698775 = 17548163) B17548163
theorem B4326169 : Blo 1709055 4326169 := bstep (se 2 (by rfl) ⟨1622313, by rfl⟩ : syracuseStep 4326169 = 3244627) B3244627
theorem B2565161 : Blo 1709055 2565161 := bstep (se 2 (by rfl) ⟨961935, by rfl⟩ : syracuseStep 2565161 = 1923871) B1923871
theorem B6489179 : Blo 1709055 6489179 := bstep (se 1 (by rfl) ⟨4866884, by rfl⟩ : syracuseStep 6489179 = 9733769) B9733769
theorem B2565359 : Blo 1709055 2565359 := bstep (se 1 (by rfl) ⟨1924019, by rfl⟩ : syracuseStep 2565359 = 3848039) B3848039
theorem B2565455 : Blo 1709055 2565455 := bstep (se 1 (by rfl) ⟨1924091, by rfl⟩ : syracuseStep 2565455 = 3848183) B3848183
theorem B6489679 : Blo 1709055 6489679 := bstep (se 1 (by rfl) ⟨4867259, by rfl⟩ : syracuseStep 6489679 = 9734519) B9734519
theorem B21923581 : Blo 1709055 21923581 := bstep (se 3 (by rfl) ⟨4110671, by rfl⟩ : syracuseStep 21923581 = 8221343) B8221343
theorem B2164583 : Blo 1709055 2164583 := bstep (se 1 (by rfl) ⟨1623437, by rfl⟩ : syracuseStep 2164583 = 3246875) B3246875
theorem B2566247 : Blo 1709055 2566247 := bstep (se 1 (by rfl) ⟨1924685, by rfl⟩ : syracuseStep 2566247 = 3849371) B3849371
theorem B7801505 : Blo 1709055 7801505 := bstep (se 2 (by rfl) ⟨2925564, by rfl⟩ : syracuseStep 7801505 = 5851129) B5851129
theorem B4623079 : Blo 1709055 4623079 := bstep (se 1 (by rfl) ⟨3467309, by rfl⟩ : syracuseStep 4623079 = 6934619) B6934619
theorem B2887015 : Blo 1709055 2887015 := bstep (se 1 (by rfl) ⟨2165261, by rfl⟩ : syracuseStep 2887015 = 4330523) B4330523
theorem B55479815 : Blo 1709055 55479815 := bstep (se 1 (by rfl) ⟨41609861, by rfl⟩ : syracuseStep 55479815 = 83219723) B83219723
theorem B5476207 : Blo 1709055 5476207 := bstep (se 1 (by rfl) ⟨4107155, by rfl⟩ : syracuseStep 5476207 = 8214311) B8214311
theorem B38006759 : Blo 1709055 38006759 := bstep (se 1 (by rfl) ⟨28505069, by rfl⟩ : syracuseStep 38006759 = 57010139) B57010139
theorem B3846383 : Blo 1709055 3846383 := bstep (se 1 (by rfl) ⟨2884787, by rfl⟩ : syracuseStep 3846383 = 5769575) B5769575
theorem B5771519 : Blo 1709055 5771519 := bstep (se 1 (by rfl) ⟨4328639, by rfl⟩ : syracuseStep 5771519 = 8657279) B8657279
theorem B4813139 : Blo 1709055 4813139 := bstep (se 1 (by rfl) ⟨3609854, by rfl⟩ : syracuseStep 4813139 = 7219709) B7219709
theorem B35115551 : Blo 1709055 35115551 := bstep (se 1 (by rfl) ⟨26336663, by rfl⟩ : syracuseStep 35115551 = 52673327) B52673327
theorem B62378585 : Blo 1709055 62378585 := bstep (se 2 (by rfl) ⟨23391969, by rfl⟩ : syracuseStep 62378585 = 46783939) B46783939
theorem B3846761 : Blo 1709055 3846761 := bstep (se 2 (by rfl) ⟨1442535, by rfl⟩ : syracuseStep 3846761 = 2885071) B2885071
theorem B24638195 : Blo 1709055 24638195 := bstep (se 1 (by rfl) ⟨18478646, by rfl⟩ : syracuseStep 24638195 = 36957293) B36957293
theorem B12981059 : Blo 1709055 12981059 := bstep (se 1 (by rfl) ⟨9735794, by rfl⟩ : syracuseStep 12981059 = 19471589) B19471589
theorem B4330655 : Blo 1709055 4330655 := bstep (se 1 (by rfl) ⟨3247991, by rfl⟩ : syracuseStep 4330655 = 6495983) B6495983
theorem B1709223 : Blo 1709055 1709223 := bstep (se 1 (by rfl) ⟨1281917, by rfl⟩ : syracuseStep 1709223 = 2563835) B2563835
theorem B3847391 : Blo 1709055 3847391 := bstep (se 1 (by rfl) ⟨2885543, by rfl⟩ : syracuseStep 3847391 = 5771087) B5771087
theorem B35108153 : Blo 1709055 35108153 := bstep (se 2 (by rfl) ⟨13165557, by rfl⟩ : syracuseStep 35108153 = 26331115) B26331115
theorem B3847607 : Blo 1709055 3847607 := bstep (se 1 (by rfl) ⟨2885705, by rfl⟩ : syracuseStep 3847607 = 5771411) B5771411
theorem B607647197 : Blo 1709055 607647197 := bstep (se 3 (by rfl) ⟨113933849, by rfl⟩ : syracuseStep 607647197 = 227867699) B227867699
theorem B1709927 : Blo 1709055 1709927 := bstep (se 1 (by rfl) ⟨1282445, by rfl⟩ : syracuseStep 1709927 = 2564891) B2564891
theorem B1709991 : Blo 1709055 1709991 := bstep (se 1 (by rfl) ⟨1282493, by rfl⟩ : syracuseStep 1709991 = 2564987) B2564987
theorem B1710075 : Blo 1709055 1710075 := bstep (se 1 (by rfl) ⟨1282556, by rfl⟩ : syracuseStep 1710075 = 2565113) B2565113
theorem B3848255 : Blo 1709055 3848255 := bstep (se 1 (by rfl) ⟨2886191, by rfl⟩ : syracuseStep 3848255 = 5772383) B5772383
theorem B1710207 : Blo 1709055 1710207 := bstep (se 1 (by rfl) ⟨1282655, by rfl⟩ : syracuseStep 1710207 = 2565311) B2565311
theorem B2054875 : Blo 1709055 2054875 := bstep (se 1 (by rfl) ⟨1541156, by rfl⟩ : syracuseStep 2054875 = 3082313) B3082313
theorem B13163471 : Blo 1709055 13163471 := bstep (se 1 (by rfl) ⟨9872603, by rfl⟩ : syracuseStep 13163471 = 19745207) B19745207
theorem B3849263 : Blo 1709055 3849263 := bstep (se 1 (by rfl) ⟨2886947, by rfl⟩ : syracuseStep 3849263 = 5773895) B5773895
theorem B3653623 : Blo 1709055 3653623 := bstep (se 1 (by rfl) ⟨2740217, by rfl⟩ : syracuseStep 3653623 = 5480435) B5480435
theorem B2564255 : Blo 1709055 2564255 := bstep (se 1 (by rfl) ⟨1923191, by rfl⟩ : syracuseStep 2564255 = 3846383) B3846383
theorem B7799183 : Blo 1709055 7799183 := bstep (se 1 (by rfl) ⟨5849387, by rfl⟩ : syracuseStep 7799183 = 11698775) B11698775
theorem B2564507 : Blo 1709055 2564507 := bstep (se 1 (by rfl) ⟨1923380, by rfl⟩ : syracuseStep 2564507 = 3846761) B3846761
theorem B4326119 : Blo 1709055 4326119 := bstep (se 1 (by rfl) ⟨3244589, by rfl⟩ : syracuseStep 4326119 = 6489179) B6489179
theorem B2564927 : Blo 1709055 2564927 := bstep (se 1 (by rfl) ⟨1923695, by rfl⟩ : syracuseStep 2564927 = 3847391) B3847391
theorem B23405435 : Blo 1709055 23405435 := bstep (se 1 (by rfl) ⟨17554076, by rfl⟩ : syracuseStep 23405435 = 35108153) B35108153
theorem B2565071 : Blo 1709055 2565071 := bstep (se 1 (by rfl) ⟨1923803, by rfl⟩ : syracuseStep 2565071 = 3847607) B3847607
theorem B5768225 : Blo 1709055 5768225 := bstep (se 2 (by rfl) ⟨2163084, by rfl⟩ : syracuseStep 5768225 = 4326169) B4326169
theorem B2565503 : Blo 1709055 2565503 := bstep (se 1 (by rfl) ⟨1924127, by rfl⟩ : syracuseStep 2565503 = 3848255) B3848255
theorem B65701853 : Blo 1709055 65701853 := bstep (se 3 (by rfl) ⟨12319097, by rfl⟩ : syracuseStep 65701853 = 24638195) B24638195
theorem B8775647 : Blo 1709055 8775647 := bstep (se 1 (by rfl) ⟨6581735, by rfl⟩ : syracuseStep 8775647 = 13163471) B13163471
theorem B2566175 : Blo 1709055 2566175 := bstep (se 1 (by rfl) ⟨1924631, by rfl⟩ : syracuseStep 2566175 = 3849263) B3849263
theorem B8652905 : Blo 1709055 8652905 := bstep (se 2 (by rfl) ⟨3244839, by rfl⟩ : syracuseStep 8652905 = 6489679) B6489679
theorem B29231441 : Blo 1709055 29231441 := bstep (se 2 (by rfl) ⟨10961790, by rfl⟩ : syracuseStep 29231441 = 21923581) B21923581
theorem B7301609 : Blo 1709055 7301609 := bstep (se 2 (by rfl) ⟨2738103, by rfl⟩ : syracuseStep 7301609 = 5476207) B5476207
theorem B41585723 : Blo 1709055 41585723 := bstep (se 1 (by rfl) ⟨31189292, by rfl⟩ : syracuseStep 41585723 = 62378585) B62378585
theorem B16428197 : Blo 1709055 16428197 := bstep (se 4 (by rfl) ⟨1540143, by rfl⟩ : syracuseStep 16428197 = 3080287) B3080287
theorem B8654039 : Blo 1709055 8654039 := bstep (se 1 (by rfl) ⟨6490529, by rfl⟩ : syracuseStep 8654039 = 12981059) B12981059
theorem B2887103 : Blo 1709055 2887103 := bstep (se 1 (by rfl) ⟨2165327, by rfl⟩ : syracuseStep 2887103 = 4330655) B4330655
theorem B2739833 : Blo 1709055 2739833 := bstep (se 2 (by rfl) ⟨1027437, by rfl⟩ : syracuseStep 2739833 = 2054875) B2054875
theorem B6164105 : Blo 1709055 6164105 := bstep (se 2 (by rfl) ⟨2311539, by rfl⟩ : syracuseStep 6164105 = 4623079) B4623079
theorem B405098131 : Blo 1709055 405098131 := bstep (se 1 (by rfl) ⟨303823598, by rfl⟩ : syracuseStep 405098131 = 607647197) B607647197
theorem B5772221 : Blo 1709055 5772221 := bstep (se 3 (by rfl) ⟨1082291, by rfl⟩ : syracuseStep 5772221 = 2164583) B2164583
theorem B4871497 : Blo 1709055 4871497 := bstep (se 2 (by rfl) ⟨1826811, by rfl⟩ : syracuseStep 4871497 = 3653623) B3653623
theorem B1709471 : Blo 1709055 1709471 := bstep (se 1 (by rfl) ⟨1282103, by rfl⟩ : syracuseStep 1709471 = 2564207) B2564207
theorem B3847679 : Blo 1709055 3847679 := bstep (se 1 (by rfl) ⟨2885759, by rfl⟩ : syracuseStep 3847679 = 5771519) B5771519
theorem B4871771 : Blo 1709055 4871771 := bstep (se 1 (by rfl) ⟨3653828, by rfl⟩ : syracuseStep 4871771 = 7307657) B7307657
theorem B23410367 : Blo 1709055 23410367 := bstep (se 1 (by rfl) ⟨17557775, by rfl⟩ : syracuseStep 23410367 = 35115551) B35115551
theorem B1710107 : Blo 1709055 1710107 := bstep (se 1 (by rfl) ⟨1282580, by rfl⟩ : syracuseStep 1710107 = 2565161) B2565161
theorem B1710239 : Blo 1709055 1710239 := bstep (se 1 (by rfl) ⟨1282679, by rfl⟩ : syracuseStep 1710239 = 2565359) B2565359
theorem B12835037 : Blo 1709055 12835037 := bstep (se 3 (by rfl) ⟨2406569, by rfl⟩ : syracuseStep 12835037 = 4813139) B4813139
theorem B1710303 : Blo 1709055 1710303 := bstep (se 1 (by rfl) ⟨1282727, by rfl⟩ : syracuseStep 1710303 = 2565455) B2565455
theorem B1710831 : Blo 1709055 1710831 := bstep (se 1 (by rfl) ⟨1283123, by rfl⟩ : syracuseStep 1710831 = 2566247) B2566247
theorem B5201003 : Blo 1709055 5201003 := bstep (se 1 (by rfl) ⟨3900752, by rfl⟩ : syracuseStep 5201003 = 7801505) B7801505
theorem B3849353 : Blo 1709055 3849353 := bstep (se 2 (by rfl) ⟨1443507, by rfl⟩ : syracuseStep 3849353 = 2887015) B2887015
theorem B36986543 : Blo 1709055 36986543 := bstep (se 1 (by rfl) ⟨27739907, by rfl⟩ : syracuseStep 36986543 = 55479815) B55479815
theorem B101351357 : Blo 1709055 101351357 := bstep (se 3 (by rfl) ⟨19003379, by rfl⟩ : syracuseStep 101351357 = 38006759) B38006759
theorem B2884079 : Blo 1709055 2884079 := bstep (se 1 (by rfl) ⟨2163059, by rfl⟩ : syracuseStep 2884079 = 4326119) B4326119
theorem B2565119 : Blo 1709055 2565119 := bstep (se 1 (by rfl) ⟨1923839, by rfl⟩ : syracuseStep 2565119 = 3847679) B3847679
theorem B15606911 : Blo 1709055 15606911 := bstep (se 1 (by rfl) ⟨11705183, by rfl⟩ : syracuseStep 15606911 = 23410367) B23410367
theorem B5850431 : Blo 1709055 5850431 := bstep (se 1 (by rfl) ⟨4387823, by rfl⟩ : syracuseStep 5850431 = 8775647) B8775647
theorem B5768603 : Blo 1709055 5768603 := bstep (se 1 (by rfl) ⟨4326452, by rfl⟩ : syracuseStep 5768603 = 8652905) B8652905
theorem B4867739 : Blo 1709055 4867739 := bstep (se 1 (by rfl) ⟨3650804, by rfl⟩ : syracuseStep 4867739 = 7301609) B7301609
theorem B27723815 : Blo 1709055 27723815 := bstep (se 1 (by rfl) ⟨20792861, by rfl⟩ : syracuseStep 27723815 = 41585723) B41585723
theorem B3467335 : Blo 1709055 3467335 := bstep (se 1 (by rfl) ⟨2600501, by rfl⟩ : syracuseStep 3467335 = 5201003) B5201003
theorem B2566235 : Blo 1709055 2566235 := bstep (se 1 (by rfl) ⟨1924676, by rfl⟩ : syracuseStep 2566235 = 3849353) B3849353
theorem B5769359 : Blo 1709055 5769359 := bstep (se 1 (by rfl) ⟨4327019, by rfl⟩ : syracuseStep 5769359 = 8654039) B8654039
theorem B3845483 : Blo 1709055 3845483 := bstep (se 1 (by rfl) ⟨2884112, by rfl⟩ : syracuseStep 3845483 = 5768225) B5768225
theorem B3247847 : Blo 1709055 3247847 := bstep (se 1 (by rfl) ⟨2435885, by rfl⟩ : syracuseStep 3247847 = 4871771) B4871771
theorem B8556691 : Blo 1709055 8556691 := bstep (se 1 (by rfl) ⟨6417518, by rfl⟩ : syracuseStep 8556691 = 12835037) B12835037
theorem B16437613 : Blo 1709055 16437613 := bstep (se 3 (by rfl) ⟨3082052, by rfl⟩ : syracuseStep 16437613 = 6164105) B6164105
theorem B1709503 : Blo 1709055 1709503 := bstep (se 1 (by rfl) ⟨1282127, by rfl⟩ : syracuseStep 1709503 = 2564255) B2564255
theorem B5199455 : Blo 1709055 5199455 := bstep (se 1 (by rfl) ⟨3899591, by rfl⟩ : syracuseStep 5199455 = 7799183) B7799183
theorem B1709671 : Blo 1709055 1709671 := bstep (se 1 (by rfl) ⟨1282253, by rfl⟩ : syracuseStep 1709671 = 2564507) B2564507
theorem B1709951 : Blo 1709055 1709951 := bstep (se 1 (by rfl) ⟨1282463, by rfl⟩ : syracuseStep 1709951 = 2564927) B2564927
theorem B15603623 : Blo 1709055 15603623 := bstep (se 1 (by rfl) ⟨11702717, by rfl⟩ : syracuseStep 15603623 = 23405435) B23405435
theorem B3848147 : Blo 1709055 3848147 := bstep (se 1 (by rfl) ⟨2886110, by rfl⟩ : syracuseStep 3848147 = 5772221) B5772221
theorem B1710047 : Blo 1709055 1710047 := bstep (se 1 (by rfl) ⟨1282535, by rfl⟩ : syracuseStep 1710047 = 2565071) B2565071
theorem B1710335 : Blo 1709055 1710335 := bstep (se 1 (by rfl) ⟨1282751, by rfl⟩ : syracuseStep 1710335 = 2565503) B2565503
theorem B43801235 : Blo 1709055 43801235 := bstep (se 1 (by rfl) ⟨32850926, by rfl⟩ : syracuseStep 43801235 = 65701853) B65701853
theorem B1710783 : Blo 1709055 1710783 := bstep (se 1 (by rfl) ⟨1283087, by rfl⟩ : syracuseStep 1710783 = 2566175) B2566175
theorem B19487627 : Blo 1709055 19487627 := bstep (se 1 (by rfl) ⟨14615720, by rfl⟩ : syracuseStep 19487627 = 29231441) B29231441
theorem B6495329 : Blo 1709055 6495329 := bstep (se 2 (by rfl) ⟨2435748, by rfl⟩ : syracuseStep 6495329 = 4871497) B4871497
theorem B10952131 : Blo 1709055 10952131 := bstep (se 1 (by rfl) ⟨8214098, by rfl⟩ : syracuseStep 10952131 = 16428197) B16428197
theorem B540130841 : Blo 1709055 540130841 := bstep (se 2 (by rfl) ⟨202549065, by rfl⟩ : syracuseStep 540130841 = 405098131) B405098131
theorem B1924735 : Blo 1709055 1924735 := bstep (se 1 (by rfl) ⟨1443551, by rfl⟩ : syracuseStep 1924735 = 2887103) B2887103
theorem B1826555 : Blo 1709055 1826555 := bstep (se 1 (by rfl) ⟨1369916, by rfl⟩ : syracuseStep 1826555 = 2739833) B2739833
theorem B24657695 : Blo 1709055 24657695 := bstep (se 1 (by rfl) ⟨18493271, by rfl⟩ : syracuseStep 24657695 = 36986543) B36986543
theorem B67567571 : Blo 1709055 67567571 := bstep (se 1 (by rfl) ⟨50675678, by rfl⟩ : syracuseStep 67567571 = 101351357) B101351357
theorem B10404607 : Blo 1709055 10404607 := bstep (se 1 (by rfl) ⟨7803455, by rfl⟩ : syracuseStep 10404607 = 15606911) B15606911
theorem B3900287 : Blo 1709055 3900287 := bstep (se 1 (by rfl) ⟨2925215, by rfl⟩ : syracuseStep 3900287 = 5850431) B5850431
theorem B3245159 : Blo 1709055 3245159 := bstep (se 1 (by rfl) ⟨2433869, by rfl⟩ : syracuseStep 3245159 = 4867739) B4867739
theorem B2565431 : Blo 1709055 2565431 := bstep (se 1 (by rfl) ⟨1924073, by rfl⟩ : syracuseStep 2565431 = 3848147) B3848147
theorem B18482543 : Blo 1709055 18482543 := bstep (se 1 (by rfl) ⟨13861907, by rfl⟩ : syracuseStep 18482543 = 27723815) B27723815
theorem B2566313 : Blo 1709055 2566313 := bstep (se 2 (by rfl) ⟨962367, by rfl⟩ : syracuseStep 2566313 = 1924735) B1924735
theorem B2165231 : Blo 1709055 2165231 := bstep (se 1 (by rfl) ⟨1623923, by rfl⟩ : syracuseStep 2165231 = 3247847) B3247847
theorem B19483253 : Blo 1709055 19483253 := bstep (se 5 (by rfl) ⟨913277, by rfl⟩ : syracuseStep 19483253 = 1826555) B1826555
theorem B4623113 : Blo 1709055 4623113 := bstep (se 2 (by rfl) ⟨1733667, by rfl⟩ : syracuseStep 4623113 = 3467335) B3467335
theorem B21916817 : Blo 1709055 21916817 := bstep (se 2 (by rfl) ⟨8218806, by rfl⟩ : syracuseStep 21916817 = 16437613) B16437613
theorem B3845735 : Blo 1709055 3845735 := bstep (se 1 (by rfl) ⟨2884301, by rfl⟩ : syracuseStep 3845735 = 5768603) B5768603
theorem B3846239 : Blo 1709055 3846239 := bstep (se 1 (by rfl) ⟨2884679, by rfl⟩ : syracuseStep 3846239 = 5769359) B5769359
theorem B13865213 : Blo 1709055 13865213 := bstep (se 3 (by rfl) ⟨2599727, by rfl⟩ : syracuseStep 13865213 = 5199455) B5199455
theorem B29200823 : Blo 1709055 29200823 := bstep (se 1 (by rfl) ⟨21900617, by rfl⟩ : syracuseStep 29200823 = 43801235) B43801235
theorem B14602841 : Blo 1709055 14602841 := bstep (se 2 (by rfl) ⟨5476065, by rfl⟩ : syracuseStep 14602841 = 10952131) B10952131
theorem B4330219 : Blo 1709055 4330219 := bstep (se 1 (by rfl) ⟨3247664, by rfl⟩ : syracuseStep 4330219 = 6495329) B6495329
theorem B16438463 : Blo 1709055 16438463 := bstep (se 1 (by rfl) ⟨12328847, by rfl⟩ : syracuseStep 16438463 = 24657695) B24657695
theorem B45045047 : Blo 1709055 45045047 := bstep (se 1 (by rfl) ⟨33783785, by rfl⟩ : syracuseStep 45045047 = 67567571) B67567571
theorem B11408921 : Blo 1709055 11408921 := bstep (se 2 (by rfl) ⟨4278345, by rfl⟩ : syracuseStep 11408921 = 8556691) B8556691
theorem B1922719 : Blo 1709055 1922719 := bstep (se 1 (by rfl) ⟨1442039, by rfl⟩ : syracuseStep 1922719 = 2884079) B2884079
theorem B1710079 : Blo 1709055 1710079 := bstep (se 1 (by rfl) ⟨1282559, by rfl⟩ : syracuseStep 1710079 = 2565119) B2565119
theorem B10402415 : Blo 1709055 10402415 := bstep (se 1 (by rfl) ⟨7801811, by rfl⟩ : syracuseStep 10402415 = 15603623) B15603623
theorem B1710823 : Blo 1709055 1710823 := bstep (se 1 (by rfl) ⟨1283117, by rfl⟩ : syracuseStep 1710823 = 2566235) B2566235
theorem B12991751 : Blo 1709055 12991751 := bstep (se 1 (by rfl) ⟨9743813, by rfl⟩ : syracuseStep 12991751 = 19487627) B19487627
theorem B2563655 : Blo 1709055 2563655 := bstep (se 1 (by rfl) ⟨1922741, by rfl⟩ : syracuseStep 2563655 = 3845483) B3845483
theorem B360087227 : Blo 1709055 360087227 := bstep (se 1 (by rfl) ⟨270065420, by rfl⟩ : syracuseStep 360087227 = 540130841) B540130841
theorem B2564159 : Blo 1709055 2564159 := bstep (se 1 (by rfl) ⟨1923119, by rfl⟩ : syracuseStep 2564159 = 3846239) B3846239
theorem B2163439 : Blo 1709055 2163439 := bstep (se 1 (by rfl) ⟨1622579, by rfl⟩ : syracuseStep 2163439 = 3245159) B3245159
theorem B12321695 : Blo 1709055 12321695 := bstep (se 1 (by rfl) ⟨9241271, by rfl⟩ : syracuseStep 12321695 = 18482543) B18482543
theorem B8661167 : Blo 1709055 8661167 := bstep (se 1 (by rfl) ⟨6495875, by rfl⟩ : syracuseStep 8661167 = 12991751) B12991751
theorem B19467215 : Blo 1709055 19467215 := bstep (se 1 (by rfl) ⟨14600411, by rfl⟩ : syracuseStep 19467215 = 29200823) B29200823
theorem B9735227 : Blo 1709055 9735227 := bstep (se 1 (by rfl) ⟨7301420, by rfl⟩ : syracuseStep 9735227 = 14602841) B14602841
theorem B2600191 : Blo 1709055 2600191 := bstep (se 1 (by rfl) ⟨1950143, by rfl⟩ : syracuseStep 2600191 = 3900287) B3900287
theorem B36973901 : Blo 1709055 36973901 := bstep (se 3 (by rfl) ⟨6932606, by rfl⟩ : syracuseStep 36973901 = 13865213) B13865213
theorem B13872809 : Blo 1709055 13872809 := bstep (se 2 (by rfl) ⟨5202303, by rfl⟩ : syracuseStep 13872809 = 10404607) B10404607
theorem B7605947 : Blo 1709055 7605947 := bstep (se 1 (by rfl) ⟨5704460, by rfl⟩ : syracuseStep 7605947 = 11408921) B11408921
theorem B6934943 : Blo 1709055 6934943 := bstep (se 1 (by rfl) ⟨5201207, by rfl⟩ : syracuseStep 6934943 = 10402415) B10402415
theorem B12988835 : Blo 1709055 12988835 := bstep (se 1 (by rfl) ⟨9741626, by rfl⟩ : syracuseStep 12988835 = 19483253) B19483253
theorem B14611211 : Blo 1709055 14611211 := bstep (se 1 (by rfl) ⟨10958408, by rfl⟩ : syracuseStep 14611211 = 21916817) B21916817
theorem B1709103 : Blo 1709055 1709103 := bstep (se 1 (by rfl) ⟨1281827, by rfl⟩ : syracuseStep 1709103 = 2563655) B2563655
theorem B10958975 : Blo 1709055 10958975 := bstep (se 1 (by rfl) ⟨8219231, by rfl⟩ : syracuseStep 10958975 = 16438463) B16438463
theorem B1710287 : Blo 1709055 1710287 := bstep (se 1 (by rfl) ⟨1282715, by rfl⟩ : syracuseStep 1710287 = 2565431) B2565431
theorem B30030031 : Blo 1709055 30030031 := bstep (se 1 (by rfl) ⟨22522523, by rfl⟩ : syracuseStep 30030031 = 45045047) B45045047
theorem B5773625 : Blo 1709055 5773625 := bstep (se 2 (by rfl) ⟨2165109, by rfl⟩ : syracuseStep 5773625 = 4330219) B4330219
theorem B5773949 : Blo 1709055 5773949 := bstep (se 3 (by rfl) ⟨1082615, by rfl⟩ : syracuseStep 5773949 = 2165231) B2165231
theorem B1710875 : Blo 1709055 1710875 := bstep (se 1 (by rfl) ⟨1283156, by rfl⟩ : syracuseStep 1710875 = 2566313) B2566313
theorem B12328301 : Blo 1709055 12328301 := bstep (se 3 (by rfl) ⟨2311556, by rfl⟩ : syracuseStep 12328301 = 4623113) B4623113
theorem B2563625 : Blo 1709055 2563625 := bstep (se 2 (by rfl) ⟨961359, by rfl⟩ : syracuseStep 2563625 = 1922719) B1922719
theorem B2563823 : Blo 1709055 2563823 := bstep (se 1 (by rfl) ⟨1922867, by rfl⟩ : syracuseStep 2563823 = 3845735) B3845735
theorem B240058151 : Blo 1709055 240058151 := bstep (se 1 (by rfl) ⟨180043613, by rfl⟩ : syracuseStep 240058151 = 360087227) B360087227
theorem B8659223 : Blo 1709055 8659223 := bstep (se 1 (by rfl) ⟨6494417, by rfl⟩ : syracuseStep 8659223 = 12988835) B12988835
theorem B9740807 : Blo 1709055 9740807 := bstep (se 1 (by rfl) ⟨7305605, by rfl⟩ : syracuseStep 9740807 = 14611211) B14611211
theorem B2884585 : Blo 1709055 2884585 := bstep (se 2 (by rfl) ⟨1081719, by rfl⟩ : syracuseStep 2884585 = 2163439) B2163439
theorem B12978143 : Blo 1709055 12978143 := bstep (se 1 (by rfl) ⟨9733607, by rfl⟩ : syracuseStep 12978143 = 19467215) B19467215
theorem B6490151 : Blo 1709055 6490151 := bstep (se 1 (by rfl) ⟨4867613, by rfl⟩ : syracuseStep 6490151 = 9735227) B9735227
theorem B8218867 : Blo 1709055 8218867 := bstep (se 1 (by rfl) ⟨6164150, by rfl⟩ : syracuseStep 8218867 = 12328301) B12328301
theorem B18493181 : Blo 1709055 18493181 := bstep (se 3 (by rfl) ⟨3467471, by rfl⟩ : syracuseStep 18493181 = 6934943) B6934943
theorem B1709083 : Blo 1709055 1709083 := bstep (se 1 (by rfl) ⟨1281812, by rfl⟩ : syracuseStep 1709083 = 2563625) B2563625
theorem B1709215 : Blo 1709055 1709215 := bstep (se 1 (by rfl) ⟨1281911, by rfl⟩ : syracuseStep 1709215 = 2563823) B2563823
theorem B1709439 : Blo 1709055 1709439 := bstep (se 1 (by rfl) ⟨1282079, by rfl⟩ : syracuseStep 1709439 = 2564159) B2564159
theorem B40040041 : Blo 1709055 40040041 := bstep (se 2 (by rfl) ⟨15015015, by rfl⟩ : syracuseStep 40040041 = 30030031) B30030031
theorem B8214463 : Blo 1709055 8214463 := bstep (se 1 (by rfl) ⟨6160847, by rfl⟩ : syracuseStep 8214463 = 12321695) B12321695
theorem B13867685 : Blo 1709055 13867685 := bstep (se 4 (by rfl) ⟨1300095, by rfl⟩ : syracuseStep 13867685 = 2600191) B2600191
theorem B7305983 : Blo 1709055 7305983 := bstep (se 1 (by rfl) ⟨5479487, by rfl⟩ : syracuseStep 7305983 = 10958975) B10958975
theorem B5774111 : Blo 1709055 5774111 := bstep (se 1 (by rfl) ⟨4330583, by rfl⟩ : syracuseStep 5774111 = 8661167) B8661167
theorem B3849083 : Blo 1709055 3849083 := bstep (se 1 (by rfl) ⟨2886812, by rfl⟩ : syracuseStep 3849083 = 5773625) B5773625
theorem B3849299 : Blo 1709055 3849299 := bstep (se 1 (by rfl) ⟨2886974, by rfl⟩ : syracuseStep 3849299 = 5773949) B5773949
theorem B24649267 : Blo 1709055 24649267 := bstep (se 1 (by rfl) ⟨18486950, by rfl⟩ : syracuseStep 24649267 = 36973901) B36973901
theorem B9248539 : Blo 1709055 9248539 := bstep (se 1 (by rfl) ⟨6936404, by rfl⟩ : syracuseStep 9248539 = 13872809) B13872809
theorem B5070631 : Blo 1709055 5070631 := bstep (se 1 (by rfl) ⟨3802973, by rfl⟩ : syracuseStep 5070631 = 7605947) B7605947
theorem B160038767 : Blo 1709055 160038767 := bstep (se 1 (by rfl) ⟨120029075, by rfl⟩ : syracuseStep 160038767 = 240058151) B240058151
theorem B8652095 : Blo 1709055 8652095 := bstep (se 1 (by rfl) ⟨6489071, by rfl⟩ : syracuseStep 8652095 = 12978143) B12978143
theorem B4326767 : Blo 1709055 4326767 := bstep (se 1 (by rfl) ⟨3245075, by rfl⟩ : syracuseStep 4326767 = 6490151) B6490151
theorem B2566055 : Blo 1709055 2566055 := bstep (se 1 (by rfl) ⟨1924541, by rfl⟩ : syracuseStep 2566055 = 3849083) B3849083
theorem B2566199 : Blo 1709055 2566199 := bstep (se 1 (by rfl) ⟨1924649, by rfl⟩ : syracuseStep 2566199 = 3849299) B3849299
theorem B12331385 : Blo 1709055 12331385 := bstep (se 2 (by rfl) ⟨4624269, by rfl⟩ : syracuseStep 12331385 = 9248539) B9248539
theorem B6760841 : Blo 1709055 6760841 := bstep (se 2 (by rfl) ⟨2535315, by rfl⟩ : syracuseStep 6760841 = 5070631) B5070631
theorem B3846113 : Blo 1709055 3846113 := bstep (se 2 (by rfl) ⟨1442292, by rfl⟩ : syracuseStep 3846113 = 2884585) B2884585
theorem B9245123 : Blo 1709055 9245123 := bstep (se 1 (by rfl) ⟨6933842, by rfl⟩ : syracuseStep 9245123 = 13867685) B13867685
theorem B4870655 : Blo 1709055 4870655 := bstep (se 1 (by rfl) ⟨3652991, by rfl⟩ : syracuseStep 4870655 = 7305983) B7305983
theorem B5772815 : Blo 1709055 5772815 := bstep (se 1 (by rfl) ⟨4329611, by rfl⟩ : syracuseStep 5772815 = 8659223) B8659223
theorem B10958489 : Blo 1709055 10958489 := bstep (se 2 (by rfl) ⟨4109433, by rfl⟩ : syracuseStep 10958489 = 8218867) B8218867
theorem B6493871 : Blo 1709055 6493871 := bstep (se 1 (by rfl) ⟨4870403, by rfl⟩ : syracuseStep 6493871 = 9740807) B9740807
theorem B3849407 : Blo 1709055 3849407 := bstep (se 1 (by rfl) ⟨2887055, by rfl⟩ : syracuseStep 3849407 = 5774111) B5774111
theorem B32865689 : Blo 1709055 32865689 := bstep (se 2 (by rfl) ⟨12324633, by rfl⟩ : syracuseStep 32865689 = 24649267) B24649267
theorem B53386721 : Blo 1709055 53386721 := bstep (se 2 (by rfl) ⟨20020020, by rfl⟩ : syracuseStep 53386721 = 40040041) B40040041
theorem B12328787 : Blo 1709055 12328787 := bstep (se 1 (by rfl) ⟨9246590, by rfl⟩ : syracuseStep 12328787 = 18493181) B18493181
theorem B106692511 : Blo 1709055 106692511 := bstep (se 1 (by rfl) ⟨80019383, by rfl⟩ : syracuseStep 106692511 = 160038767) B160038767
theorem B10952617 : Blo 1709055 10952617 := bstep (se 2 (by rfl) ⟨4107231, by rfl⟩ : syracuseStep 10952617 = 8214463) B8214463
theorem B5768063 : Blo 1709055 5768063 := bstep (se 1 (by rfl) ⟨4326047, by rfl⟩ : syracuseStep 5768063 = 8652095) B8652095
theorem B2884511 : Blo 1709055 2884511 := bstep (se 1 (by rfl) ⟨2163383, by rfl⟩ : syracuseStep 2884511 = 4326767) B4326767
theorem B2566271 : Blo 1709055 2566271 := bstep (se 1 (by rfl) ⟨1924703, by rfl⟩ : syracuseStep 2566271 = 3849407) B3849407
theorem B142256681 : Blo 1709055 142256681 := bstep (se 2 (by rfl) ⟨53346255, by rfl⟩ : syracuseStep 142256681 = 106692511) B106692511
theorem B8219191 : Blo 1709055 8219191 := bstep (se 1 (by rfl) ⟨6164393, by rfl⟩ : syracuseStep 8219191 = 12328787) B12328787
theorem B6163415 : Blo 1709055 6163415 := bstep (se 1 (by rfl) ⟨4622561, by rfl⟩ : syracuseStep 6163415 = 9245123) B9245123
theorem B3247103 : Blo 1709055 3247103 := bstep (se 1 (by rfl) ⟨2435327, by rfl⟩ : syracuseStep 3247103 = 4870655) B4870655
theorem B4329247 : Blo 1709055 4329247 := bstep (se 1 (by rfl) ⟨3246935, by rfl⟩ : syracuseStep 4329247 = 6493871) B6493871
theorem B8220923 : Blo 1709055 8220923 := bstep (se 1 (by rfl) ⟨6165692, by rfl⟩ : syracuseStep 8220923 = 12331385) B12331385
theorem B21910459 : Blo 1709055 21910459 := bstep (se 1 (by rfl) ⟨16432844, by rfl⟩ : syracuseStep 21910459 = 32865689) B32865689
theorem B35591147 : Blo 1709055 35591147 := bstep (se 1 (by rfl) ⟨26693360, by rfl⟩ : syracuseStep 35591147 = 53386721) B53386721
theorem B14603489 : Blo 1709055 14603489 := bstep (se 2 (by rfl) ⟨5476308, by rfl⟩ : syracuseStep 14603489 = 10952617) B10952617
theorem B3848543 : Blo 1709055 3848543 := bstep (se 1 (by rfl) ⟨2886407, by rfl⟩ : syracuseStep 3848543 = 5772815) B5772815
theorem B18028909 : Blo 1709055 18028909 := bstep (se 3 (by rfl) ⟨3380420, by rfl⟩ : syracuseStep 18028909 = 6760841) B6760841
theorem B7305659 : Blo 1709055 7305659 := bstep (se 1 (by rfl) ⟨5479244, by rfl⟩ : syracuseStep 7305659 = 10958489) B10958489
theorem B1710703 : Blo 1709055 1710703 := bstep (se 1 (by rfl) ⟨1283027, by rfl⟩ : syracuseStep 1710703 = 2566055) B2566055
theorem B1710799 : Blo 1709055 1710799 := bstep (se 1 (by rfl) ⟨1283099, by rfl⟩ : syracuseStep 1710799 = 2566199) B2566199
theorem B2564075 : Blo 1709055 2564075 := bstep (se 1 (by rfl) ⟨1923056, by rfl⟩ : syracuseStep 2564075 = 3846113) B3846113
theorem B5480615 : Blo 1709055 5480615 := bstep (se 1 (by rfl) ⟨4110461, by rfl⟩ : syracuseStep 5480615 = 8220923) B8220923
theorem B29213945 : Blo 1709055 29213945 := bstep (se 2 (by rfl) ⟨10955229, by rfl⟩ : syracuseStep 29213945 = 21910459) B21910459
theorem B2565695 : Blo 1709055 2565695 := bstep (se 1 (by rfl) ⟨1924271, by rfl⟩ : syracuseStep 2565695 = 3848543) B3848543
theorem B2164735 : Blo 1709055 2164735 := bstep (se 1 (by rfl) ⟨1623551, by rfl⟩ : syracuseStep 2164735 = 3247103) B3247103
theorem B24038545 : Blo 1709055 24038545 := bstep (se 2 (by rfl) ⟨9014454, by rfl⟩ : syracuseStep 24038545 = 18028909) B18028909
theorem B3845375 : Blo 1709055 3845375 := bstep (se 1 (by rfl) ⟨2884031, by rfl⟩ : syracuseStep 3845375 = 5768063) B5768063
theorem B23727431 : Blo 1709055 23727431 := bstep (se 1 (by rfl) ⟨17795573, by rfl⟩ : syracuseStep 23727431 = 35591147) B35591147
theorem B9735659 : Blo 1709055 9735659 := bstep (se 1 (by rfl) ⟨7301744, by rfl⟩ : syracuseStep 9735659 = 14603489) B14603489
theorem B4870439 : Blo 1709055 4870439 := bstep (se 1 (by rfl) ⟨3652829, by rfl⟩ : syracuseStep 4870439 = 7305659) B7305659
theorem B4108943 : Blo 1709055 4108943 := bstep (se 1 (by rfl) ⟨3081707, by rfl⟩ : syracuseStep 4108943 = 6163415) B6163415
theorem B5772329 : Blo 1709055 5772329 := bstep (se 2 (by rfl) ⟨2164623, by rfl⟩ : syracuseStep 5772329 = 4329247) B4329247
theorem B1709383 : Blo 1709055 1709383 := bstep (se 1 (by rfl) ⟨1282037, by rfl⟩ : syracuseStep 1709383 = 2564075) B2564075
theorem B1923007 : Blo 1709055 1923007 := bstep (se 1 (by rfl) ⟨1442255, by rfl⟩ : syracuseStep 1923007 = 2884511) B2884511
theorem B10958921 : Blo 1709055 10958921 := bstep (se 2 (by rfl) ⟨4109595, by rfl⟩ : syracuseStep 10958921 = 8219191) B8219191
theorem B1710847 : Blo 1709055 1710847 := bstep (se 1 (by rfl) ⟨1283135, by rfl⟩ : syracuseStep 1710847 = 2566271) B2566271
theorem B94837787 : Blo 1709055 94837787 := bstep (se 1 (by rfl) ⟨71128340, by rfl⟩ : syracuseStep 94837787 = 142256681) B142256681
theorem B3653743 : Blo 1709055 3653743 := bstep (se 1 (by rfl) ⟨2740307, by rfl⟩ : syracuseStep 3653743 = 5480615) B5480615
theorem B6490439 : Blo 1709055 6490439 := bstep (se 1 (by rfl) ⟨4867829, by rfl⟩ : syracuseStep 6490439 = 9735659) B9735659
theorem B2886313 : Blo 1709055 2886313 := bstep (se 2 (by rfl) ⟨1082367, by rfl⟩ : syracuseStep 2886313 = 2164735) B2164735
theorem B3246959 : Blo 1709055 3246959 := bstep (se 1 (by rfl) ⟨2435219, by rfl⟩ : syracuseStep 3246959 = 4870439) B4870439
theorem B2739295 : Blo 1709055 2739295 := bstep (se 1 (by rfl) ⟨2054471, by rfl⟩ : syracuseStep 2739295 = 4108943) B4108943
theorem B19475963 : Blo 1709055 19475963 := bstep (se 1 (by rfl) ⟨14606972, by rfl⟩ : syracuseStep 19475963 = 29213945) B29213945
theorem B32051393 : Blo 1709055 32051393 := bstep (se 2 (by rfl) ⟨12019272, by rfl⟩ : syracuseStep 32051393 = 24038545) B24038545
theorem B3848219 : Blo 1709055 3848219 := bstep (se 1 (by rfl) ⟨2886164, by rfl⟩ : syracuseStep 3848219 = 5772329) B5772329
theorem B1710463 : Blo 1709055 1710463 := bstep (se 1 (by rfl) ⟨1282847, by rfl⟩ : syracuseStep 1710463 = 2565695) B2565695
theorem B7305947 : Blo 1709055 7305947 := bstep (se 1 (by rfl) ⟨5479460, by rfl⟩ : syracuseStep 7305947 = 10958921) B10958921
theorem B63225191 : Blo 1709055 63225191 := bstep (se 1 (by rfl) ⟨47418893, by rfl⟩ : syracuseStep 63225191 = 94837787) B94837787
theorem B2563583 : Blo 1709055 2563583 := bstep (se 1 (by rfl) ⟨1922687, by rfl⟩ : syracuseStep 2563583 = 3845375) B3845375
theorem B15818287 : Blo 1709055 15818287 := bstep (se 1 (by rfl) ⟨11863715, by rfl⟩ : syracuseStep 15818287 = 23727431) B23727431
theorem B2564009 : Blo 1709055 2564009 := bstep (se 2 (by rfl) ⟨961503, by rfl⟩ : syracuseStep 2564009 = 1923007) B1923007
theorem B2565479 : Blo 1709055 2565479 := bstep (se 1 (by rfl) ⟨1924109, by rfl⟩ : syracuseStep 2565479 = 3848219) B3848219
theorem B4326959 : Blo 1709055 4326959 := bstep (se 1 (by rfl) ⟨3245219, by rfl⟩ : syracuseStep 4326959 = 6490439) B6490439
theorem B2164639 : Blo 1709055 2164639 := bstep (se 1 (by rfl) ⟨1623479, by rfl⟩ : syracuseStep 2164639 = 3246959) B3246959
theorem B42150127 : Blo 1709055 42150127 := bstep (se 1 (by rfl) ⟨31612595, by rfl⟩ : syracuseStep 42150127 = 63225191) B63225191
theorem B21367595 : Blo 1709055 21367595 := bstep (se 1 (by rfl) ⟨16025696, by rfl⟩ : syracuseStep 21367595 = 32051393) B32051393
theorem B4870631 : Blo 1709055 4870631 := bstep (se 1 (by rfl) ⟨3652973, by rfl⟩ : syracuseStep 4870631 = 7305947) B7305947
theorem B21091049 : Blo 1709055 21091049 := bstep (se 2 (by rfl) ⟨7909143, by rfl⟩ : syracuseStep 21091049 = 15818287) B15818287
theorem B1709055 : Blo 1709055 1709055 := bstep (se 1 (by rfl) ⟨1281791, by rfl⟩ : syracuseStep 1709055 = 2563583) B2563583
theorem B1709339 : Blo 1709055 1709339 := bstep (se 1 (by rfl) ⟨1282004, by rfl⟩ : syracuseStep 1709339 = 2564009) B2564009
theorem B4871657 : Blo 1709055 4871657 := bstep (se 2 (by rfl) ⟨1826871, by rfl⟩ : syracuseStep 4871657 = 3653743) B3653743
theorem B3848417 : Blo 1709055 3848417 := bstep (se 2 (by rfl) ⟨1443156, by rfl⟩ : syracuseStep 3848417 = 2886313) B2886313
theorem B3652393 : Blo 1709055 3652393 := bstep (se 2 (by rfl) ⟨1369647, by rfl⟩ : syracuseStep 3652393 = 2739295) B2739295
theorem B12983975 : Blo 1709055 12983975 := bstep (se 1 (by rfl) ⟨9737981, by rfl⟩ : syracuseStep 12983975 = 19475963) B19475963
theorem B2884639 : Blo 1709055 2884639 := bstep (se 1 (by rfl) ⟨2163479, by rfl⟩ : syracuseStep 2884639 = 4326959) B4326959
theorem B2565611 : Blo 1709055 2565611 := bstep (se 1 (by rfl) ⟨1924208, by rfl⟩ : syracuseStep 2565611 = 3848417) B3848417
theorem B2886185 : Blo 1709055 2886185 := bstep (se 2 (by rfl) ⟨1082319, by rfl⟩ : syracuseStep 2886185 = 2164639) B2164639
theorem B56200169 : Blo 1709055 56200169 := bstep (se 2 (by rfl) ⟨21075063, by rfl⟩ : syracuseStep 56200169 = 42150127) B42150127
theorem B14060699 : Blo 1709055 14060699 := bstep (se 1 (by rfl) ⟨10545524, by rfl⟩ : syracuseStep 14060699 = 21091049) B21091049
theorem B3247771 : Blo 1709055 3247771 := bstep (se 1 (by rfl) ⟨2435828, by rfl⟩ : syracuseStep 3247771 = 4871657) B4871657
theorem B4869857 : Blo 1709055 4869857 := bstep (se 2 (by rfl) ⟨1826196, by rfl⟩ : syracuseStep 4869857 = 3652393) B3652393
theorem B12988349 : Blo 1709055 12988349 := bstep (se 3 (by rfl) ⟨2435315, by rfl⟩ : syracuseStep 12988349 = 4870631) B4870631
theorem B56980253 : Blo 1709055 56980253 := bstep (se 3 (by rfl) ⟨10683797, by rfl⟩ : syracuseStep 56980253 = 21367595) B21367595
theorem B8655983 : Blo 1709055 8655983 := bstep (se 1 (by rfl) ⟨6491987, by rfl⟩ : syracuseStep 8655983 = 12983975) B12983975
theorem B1710319 : Blo 1709055 1710319 := bstep (se 1 (by rfl) ⟨1282739, by rfl⟩ : syracuseStep 1710319 = 2565479) B2565479
theorem B37986835 : Blo 1709055 37986835 := bstep (se 1 (by rfl) ⟨28490126, by rfl⟩ : syracuseStep 37986835 = 56980253) B56980253
theorem B9373799 : Blo 1709055 9373799 := bstep (se 1 (by rfl) ⟨7030349, by rfl⟩ : syracuseStep 9373799 = 14060699) B14060699
theorem B3246571 : Blo 1709055 3246571 := bstep (se 1 (by rfl) ⟨2434928, by rfl⟩ : syracuseStep 3246571 = 4869857) B4869857
theorem B5770655 : Blo 1709055 5770655 := bstep (se 1 (by rfl) ⟨4327991, by rfl⟩ : syracuseStep 5770655 = 8655983) B8655983
theorem B3846185 : Blo 1709055 3846185 := bstep (se 2 (by rfl) ⟨1442319, by rfl⟩ : syracuseStep 3846185 = 2884639) B2884639
theorem B37466779 : Blo 1709055 37466779 := bstep (se 1 (by rfl) ⟨28100084, by rfl⟩ : syracuseStep 37466779 = 56200169) B56200169
theorem B4330361 : Blo 1709055 4330361 := bstep (se 2 (by rfl) ⟨1623885, by rfl⟩ : syracuseStep 4330361 = 3247771) B3247771
theorem B1710407 : Blo 1709055 1710407 := bstep (se 1 (by rfl) ⟨1282805, by rfl⟩ : syracuseStep 1710407 = 2565611) B2565611
theorem B1924123 : Blo 1709055 1924123 := bstep (se 1 (by rfl) ⟨1443092, by rfl⟩ : syracuseStep 1924123 = 2886185) B2886185
theorem B8658899 : Blo 1709055 8658899 := bstep (se 1 (by rfl) ⟨6494174, by rfl⟩ : syracuseStep 8658899 = 12988349) B12988349
theorem B2564123 : Blo 1709055 2564123 := bstep (se 1 (by rfl) ⟨1923092, by rfl⟩ : syracuseStep 2564123 = 3846185) B3846185
theorem B49955705 : Blo 1709055 49955705 := bstep (se 2 (by rfl) ⟨18733389, by rfl⟩ : syracuseStep 49955705 = 37466779) B37466779
theorem B2565497 : Blo 1709055 2565497 := bstep (se 2 (by rfl) ⟨962061, by rfl⟩ : syracuseStep 2565497 = 1924123) B1924123
theorem B2886907 : Blo 1709055 2886907 := bstep (se 1 (by rfl) ⟨2165180, by rfl⟩ : syracuseStep 2886907 = 4330361) B4330361
theorem B4328761 : Blo 1709055 4328761 := bstep (se 2 (by rfl) ⟨1623285, by rfl⟩ : syracuseStep 4328761 = 3246571) B3246571
theorem B3847103 : Blo 1709055 3847103 := bstep (se 1 (by rfl) ⟨2885327, by rfl⟩ : syracuseStep 3847103 = 5770655) B5770655
theorem B5772599 : Blo 1709055 5772599 := bstep (se 1 (by rfl) ⟨4329449, by rfl⟩ : syracuseStep 5772599 = 8658899) B8658899
theorem B50649113 : Blo 1709055 50649113 := bstep (se 2 (by rfl) ⟨18993417, by rfl⟩ : syracuseStep 50649113 = 37986835) B37986835
theorem B6249199 : Blo 1709055 6249199 := bstep (se 1 (by rfl) ⟨4686899, by rfl⟩ : syracuseStep 6249199 = 9373799) B9373799
theorem B2564735 : Blo 1709055 2564735 := bstep (se 1 (by rfl) ⟨1923551, by rfl⟩ : syracuseStep 2564735 = 3847103) B3847103
theorem B8332265 : Blo 1709055 8332265 := bstep (se 2 (by rfl) ⟨3124599, by rfl⟩ : syracuseStep 8332265 = 6249199) B6249199
theorem B33303803 : Blo 1709055 33303803 := bstep (se 1 (by rfl) ⟨24977852, by rfl⟩ : syracuseStep 33303803 = 49955705) B49955705
theorem B5771681 : Blo 1709055 5771681 := bstep (se 2 (by rfl) ⟨2164380, by rfl⟩ : syracuseStep 5771681 = 4328761) B4328761
theorem B1709415 : Blo 1709055 1709415 := bstep (se 1 (by rfl) ⟨1282061, by rfl⟩ : syracuseStep 1709415 = 2564123) B2564123
theorem B3848399 : Blo 1709055 3848399 := bstep (se 1 (by rfl) ⟨2886299, by rfl⟩ : syracuseStep 3848399 = 5772599) B5772599
theorem B1710331 : Blo 1709055 1710331 := bstep (se 1 (by rfl) ⟨1282748, by rfl⟩ : syracuseStep 1710331 = 2565497) B2565497
theorem B33766075 : Blo 1709055 33766075 := bstep (se 1 (by rfl) ⟨25324556, by rfl⟩ : syracuseStep 33766075 = 50649113) B50649113
theorem B3849209 : Blo 1709055 3849209 := bstep (se 2 (by rfl) ⟨1443453, by rfl⟩ : syracuseStep 3849209 = 2886907) B2886907
theorem B88810141 : Blo 1709055 88810141 := bstep (se 3 (by rfl) ⟨16651901, by rfl⟩ : syracuseStep 88810141 = 33303803) B33303803
theorem B2565599 : Blo 1709055 2565599 := bstep (se 1 (by rfl) ⟨1924199, by rfl⟩ : syracuseStep 2565599 = 3848399) B3848399
theorem B2566139 : Blo 1709055 2566139 := bstep (se 1 (by rfl) ⟨1924604, by rfl⟩ : syracuseStep 2566139 = 3849209) B3849209
theorem B22219373 : Blo 1709055 22219373 := bstep (se 3 (by rfl) ⟨4166132, by rfl⟩ : syracuseStep 22219373 = 8332265) B8332265
theorem B3847787 : Blo 1709055 3847787 := bstep (se 1 (by rfl) ⟨2885840, by rfl⟩ : syracuseStep 3847787 = 5771681) B5771681
theorem B1709823 : Blo 1709055 1709823 := bstep (se 1 (by rfl) ⟨1282367, by rfl⟩ : syracuseStep 1709823 = 2564735) B2564735
theorem B45021433 : Blo 1709055 45021433 := bstep (se 2 (by rfl) ⟨16883037, by rfl⟩ : syracuseStep 45021433 = 33766075) B33766075
theorem B2565191 : Blo 1709055 2565191 := bstep (se 1 (by rfl) ⟨1923893, by rfl⟩ : syracuseStep 2565191 = 3847787) B3847787
theorem B14812915 : Blo 1709055 14812915 := bstep (se 1 (by rfl) ⟨11109686, by rfl⟩ : syracuseStep 14812915 = 22219373) B22219373
theorem B60028577 : Blo 1709055 60028577 := bstep (se 2 (by rfl) ⟨22510716, by rfl⟩ : syracuseStep 60028577 = 45021433) B45021433
theorem B118413521 : Blo 1709055 118413521 := bstep (se 2 (by rfl) ⟨44405070, by rfl⟩ : syracuseStep 118413521 = 88810141) B88810141
theorem B1710399 : Blo 1709055 1710399 := bstep (se 1 (by rfl) ⟨1282799, by rfl⟩ : syracuseStep 1710399 = 2565599) B2565599
theorem B1710759 : Blo 1709055 1710759 := bstep (se 1 (by rfl) ⟨1283069, by rfl⟩ : syracuseStep 1710759 = 2566139) B2566139
theorem B40019051 : Blo 1709055 40019051 := bstep (se 1 (by rfl) ⟨30014288, by rfl⟩ : syracuseStep 40019051 = 60028577) B60028577
theorem B78942347 : Blo 1709055 78942347 := bstep (se 1 (by rfl) ⟨59206760, by rfl⟩ : syracuseStep 78942347 = 118413521) B118413521
theorem B1710127 : Blo 1709055 1710127 := bstep (se 1 (by rfl) ⟨1282595, by rfl⟩ : syracuseStep 1710127 = 2565191) B2565191
theorem B19750553 : Blo 1709055 19750553 := bstep (se 2 (by rfl) ⟨7406457, by rfl⟩ : syracuseStep 19750553 = 14812915) B14812915
theorem B13167035 : Blo 1709055 13167035 := bstep (se 1 (by rfl) ⟨9875276, by rfl⟩ : syracuseStep 13167035 = 19750553) B19750553
theorem B52628231 : Blo 1709055 52628231 := bstep (se 1 (by rfl) ⟨39471173, by rfl⟩ : syracuseStep 52628231 = 78942347) B78942347
theorem B26679367 : Blo 1709055 26679367 := bstep (se 1 (by rfl) ⟨20009525, by rfl⟩ : syracuseStep 26679367 = 40019051) B40019051
theorem B35572489 : Blo 1709055 35572489 := bstep (se 2 (by rfl) ⟨13339683, by rfl⟩ : syracuseStep 35572489 = 26679367) B26679367
theorem B8778023 : Blo 1709055 8778023 := bstep (se 1 (by rfl) ⟨6583517, by rfl⟩ : syracuseStep 8778023 = 13167035) B13167035
theorem B35085487 : Blo 1709055 35085487 := bstep (se 1 (by rfl) ⟨26314115, by rfl⟩ : syracuseStep 35085487 = 52628231) B52628231
theorem B189719941 : Blo 1709055 189719941 := bstep (se 4 (by rfl) ⟨17786244, by rfl⟩ : syracuseStep 189719941 = 35572489) B35572489
theorem B5852015 : Blo 1709055 5852015 := bstep (se 1 (by rfl) ⟨4389011, by rfl⟩ : syracuseStep 5852015 = 8778023) B8778023
theorem B46780649 : Blo 1709055 46780649 := bstep (se 2 (by rfl) ⟨17542743, by rfl⟩ : syracuseStep 46780649 = 35085487) B35085487
theorem B31187099 : Blo 1709055 31187099 := bstep (se 1 (by rfl) ⟨23390324, by rfl⟩ : syracuseStep 31187099 = 46780649) B46780649
theorem B3901343 : Blo 1709055 3901343 := bstep (se 1 (by rfl) ⟨2926007, by rfl⟩ : syracuseStep 3901343 = 5852015) B5852015
theorem B252959921 : Blo 1709055 252959921 := bstep (se 2 (by rfl) ⟨94859970, by rfl⟩ : syracuseStep 252959921 = 189719941) B189719941
theorem B20791399 : Blo 1709055 20791399 := bstep (se 1 (by rfl) ⟨15593549, by rfl⟩ : syracuseStep 20791399 = 31187099) B31187099
theorem B168639947 : Blo 1709055 168639947 := bstep (se 1 (by rfl) ⟨126479960, by rfl⟩ : syracuseStep 168639947 = 252959921) B252959921
theorem B10403581 : Blo 1709055 10403581 := bstep (se 3 (by rfl) ⟨1950671, by rfl⟩ : syracuseStep 10403581 = 3901343) B3901343
theorem B27721865 : Blo 1709055 27721865 := bstep (se 2 (by rfl) ⟨10395699, by rfl⟩ : syracuseStep 27721865 = 20791399) B20791399
theorem B13871441 : Blo 1709055 13871441 := bstep (se 2 (by rfl) ⟨5201790, by rfl⟩ : syracuseStep 13871441 = 10403581) B10403581
theorem B112426631 : Blo 1709055 112426631 := bstep (se 1 (by rfl) ⟨84319973, by rfl⟩ : syracuseStep 112426631 = 168639947) B168639947
theorem B73924973 : Blo 1709055 73924973 := bstep (se 3 (by rfl) ⟨13860932, by rfl⟩ : syracuseStep 73924973 = 27721865) B27721865
theorem B74951087 : Blo 1709055 74951087 := bstep (se 1 (by rfl) ⟨56213315, by rfl⟩ : syracuseStep 74951087 = 112426631) B112426631
theorem B9247627 : Blo 1709055 9247627 := bstep (se 1 (by rfl) ⟨6935720, by rfl⟩ : syracuseStep 9247627 = 13871441) B13871441
theorem B49283315 : Blo 1709055 49283315 := bstep (se 1 (by rfl) ⟨36962486, by rfl⟩ : syracuseStep 49283315 = 73924973) B73924973
theorem B199869565 : Blo 1709055 199869565 := bstep (se 3 (by rfl) ⟨37475543, by rfl⟩ : syracuseStep 199869565 = 74951087) B74951087
theorem B49320677 : Blo 1709055 49320677 := bstep (se 4 (by rfl) ⟨4623813, by rfl⟩ : syracuseStep 49320677 = 9247627) B9247627
theorem B32855543 : Blo 1709055 32855543 := bstep (se 1 (by rfl) ⟨24641657, by rfl⟩ : syracuseStep 32855543 = 49283315) B49283315
theorem B32880451 : Blo 1709055 32880451 := bstep (se 1 (by rfl) ⟨24660338, by rfl⟩ : syracuseStep 32880451 = 49320677) B49320677
theorem B266492753 : Blo 1709055 266492753 := bstep (se 2 (by rfl) ⟨99934782, by rfl⟩ : syracuseStep 266492753 = 199869565) B199869565
theorem B177661835 : Blo 1709055 177661835 := bstep (se 1 (by rfl) ⟨133246376, by rfl⟩ : syracuseStep 177661835 = 266492753) B266492753
theorem B43840601 : Blo 1709055 43840601 := bstep (se 2 (by rfl) ⟨16440225, by rfl⟩ : syracuseStep 43840601 = 32880451) B32880451
theorem B21903695 : Blo 1709055 21903695 := bstep (se 1 (by rfl) ⟨16427771, by rfl⟩ : syracuseStep 21903695 = 32855543) B32855543
theorem B118441223 : Blo 1709055 118441223 := bstep (se 1 (by rfl) ⟨88830917, by rfl⟩ : syracuseStep 118441223 = 177661835) B177661835
theorem B14602463 : Blo 1709055 14602463 := bstep (se 1 (by rfl) ⟨10951847, by rfl⟩ : syracuseStep 14602463 = 21903695) B21903695
theorem B29227067 : Blo 1709055 29227067 := bstep (se 1 (by rfl) ⟨21920300, by rfl⟩ : syracuseStep 29227067 = 43840601) B43840601
theorem B9734975 : Blo 1709055 9734975 := bstep (se 1 (by rfl) ⟨7301231, by rfl⟩ : syracuseStep 9734975 = 14602463) B14602463
theorem B19484711 : Blo 1709055 19484711 := bstep (se 1 (by rfl) ⟨14613533, by rfl⟩ : syracuseStep 19484711 = 29227067) B29227067
theorem B78960815 : Blo 1709055 78960815 := bstep (se 1 (by rfl) ⟨59220611, by rfl⟩ : syracuseStep 78960815 = 118441223) B118441223
theorem B6489983 : Blo 1709055 6489983 := bstep (se 1 (by rfl) ⟨4867487, by rfl⟩ : syracuseStep 6489983 = 9734975) B9734975
theorem B12989807 : Blo 1709055 12989807 := bstep (se 1 (by rfl) ⟨9742355, by rfl⟩ : syracuseStep 12989807 = 19484711) B19484711
theorem B52640543 : Blo 1709055 52640543 := bstep (se 1 (by rfl) ⟨39480407, by rfl⟩ : syracuseStep 52640543 = 78960815) B78960815
theorem B8659871 : Blo 1709055 8659871 := bstep (se 1 (by rfl) ⟨6494903, by rfl⟩ : syracuseStep 8659871 = 12989807) B12989807
theorem B4326655 : Blo 1709055 4326655 := bstep (se 1 (by rfl) ⟨3244991, by rfl⟩ : syracuseStep 4326655 = 6489983) B6489983
theorem B140374781 : Blo 1709055 140374781 := bstep (se 3 (by rfl) ⟨26320271, by rfl⟩ : syracuseStep 140374781 = 52640543) B52640543
theorem B5768873 : Blo 1709055 5768873 := bstep (se 2 (by rfl) ⟨2163327, by rfl⟩ : syracuseStep 5768873 = 4326655) B4326655
theorem B93583187 : Blo 1709055 93583187 := bstep (se 1 (by rfl) ⟨70187390, by rfl⟩ : syracuseStep 93583187 = 140374781) B140374781
theorem B5773247 : Blo 1709055 5773247 := bstep (se 1 (by rfl) ⟨4329935, by rfl⟩ : syracuseStep 5773247 = 8659871) B8659871
theorem B3845915 : Blo 1709055 3845915 := bstep (se 1 (by rfl) ⟨2884436, by rfl⟩ : syracuseStep 3845915 = 5768873) B5768873
theorem B62388791 : Blo 1709055 62388791 := bstep (se 1 (by rfl) ⟨46791593, by rfl⟩ : syracuseStep 62388791 = 93583187) B93583187
theorem B3848831 : Blo 1709055 3848831 := bstep (se 1 (by rfl) ⟨2886623, by rfl⟩ : syracuseStep 3848831 = 5773247) B5773247
theorem B41592527 : Blo 1709055 41592527 := bstep (se 1 (by rfl) ⟨31194395, by rfl⟩ : syracuseStep 41592527 = 62388791) B62388791
theorem B2565887 : Blo 1709055 2565887 := bstep (se 1 (by rfl) ⟨1924415, by rfl⟩ : syracuseStep 2565887 = 3848831) B3848831
theorem B2563943 : Blo 1709055 2563943 := bstep (se 1 (by rfl) ⟨1922957, by rfl⟩ : syracuseStep 2563943 = 3845915) B3845915
theorem B1709295 : Blo 1709055 1709295 := bstep (se 1 (by rfl) ⟨1281971, by rfl⟩ : syracuseStep 1709295 = 2563943) B2563943
theorem B27728351 : Blo 1709055 27728351 := bstep (se 1 (by rfl) ⟨20796263, by rfl⟩ : syracuseStep 27728351 = 41592527) B41592527
theorem B1710591 : Blo 1709055 1710591 := bstep (se 1 (by rfl) ⟨1282943, by rfl⟩ : syracuseStep 1710591 = 2565887) B2565887
theorem B18485567 : Blo 1709055 18485567 := bstep (se 1 (by rfl) ⟨13864175, by rfl⟩ : syracuseStep 18485567 = 27728351) B27728351
theorem B12323711 : Blo 1709055 12323711 := bstep (se 1 (by rfl) ⟨9242783, by rfl⟩ : syracuseStep 12323711 = 18485567) B18485567
theorem B32863229 : Blo 1709055 32863229 := bstep (se 3 (by rfl) ⟨6161855, by rfl⟩ : syracuseStep 32863229 = 12323711) B12323711
theorem B21908819 : Blo 1709055 21908819 := bstep (se 1 (by rfl) ⟨16431614, by rfl⟩ : syracuseStep 21908819 = 32863229) B32863229
theorem B14605879 : Blo 1709055 14605879 := bstep (se 1 (by rfl) ⟨10954409, by rfl⟩ : syracuseStep 14605879 = 21908819) B21908819
theorem B19474505 : Blo 1709055 19474505 := bstep (se 2 (by rfl) ⟨7302939, by rfl⟩ : syracuseStep 19474505 = 14605879) B14605879
theorem B12983003 : Blo 1709055 12983003 := bstep (se 1 (by rfl) ⟨9737252, by rfl⟩ : syracuseStep 12983003 = 19474505) B19474505
theorem B8655335 : Blo 1709055 8655335 := bstep (se 1 (by rfl) ⟨6491501, by rfl⟩ : syracuseStep 8655335 = 12983003) B12983003
theorem B5770223 : Blo 1709055 5770223 := bstep (se 1 (by rfl) ⟨4327667, by rfl⟩ : syracuseStep 5770223 = 8655335) B8655335
theorem B3846815 : Blo 1709055 3846815 := bstep (se 1 (by rfl) ⟨2885111, by rfl⟩ : syracuseStep 3846815 = 5770223) B5770223
theorem B2564543 : Blo 1709055 2564543 := bstep (se 1 (by rfl) ⟨1923407, by rfl⟩ : syracuseStep 2564543 = 3846815) B3846815
theorem B1709695 : Blo 1709055 1709695 := bstep (se 1 (by rfl) ⟨1282271, by rfl⟩ : syracuseStep 1709695 = 2564543) B2564543

theorem C0 (j : ℕ) (h1 : 427263 ≤ j) (h2 : j ≤ 427763) : Blo 1709055 (4 * j + 3) := by
  interval_cases j
  · exact B1709055
  · exact B1709059
  · exact B1709063
  · exact B1709067
  · exact B1709071
  · exact B1709075
  · exact B1709079
  · exact B1709083
  · exact B1709087
  · exact B1709091
  · exact B1709095
  · exact B1709099
  · exact B1709103
  · exact B1709107
  · exact B1709111
  · exact B1709115
  · exact B1709119
  · exact B1709123
  · exact B1709127
  · exact B1709131
  · exact B1709135
  · exact B1709139
  · exact B1709143
  · exact B1709147
  · exact B1709151
  · exact B1709155
  · exact B1709159
  · exact B1709163
  · exact B1709167
  · exact B1709171
  · exact B1709175
  · exact B1709179
  · exact B1709183
  · exact B1709187
  · exact B1709191
  · exact B1709195
  · exact B1709199
  · exact B1709203
  · exact B1709207
  · exact B1709211
  · exact B1709215
  · exact B1709219
  · exact B1709223
  · exact B1709227
  · exact B1709231
  · exact B1709235
  · exact B1709239
  · exact B1709243
  · exact B1709247
  · exact B1709251
  · exact B1709255
  · exact B1709259
  · exact B1709263
  · exact B1709267
  · exact B1709271
  · exact B1709275
  · exact B1709279
  · exact B1709283
  · exact B1709287
  · exact B1709291
  · exact B1709295
  · exact B1709299
  · exact B1709303
  · exact B1709307
  · exact B1709311
  · exact B1709315
  · exact B1709319
  · exact B1709323
  · exact B1709327
  · exact B1709331
  · exact B1709335
  · exact B1709339
  · exact B1709343
  · exact B1709347
  · exact B1709351
  · exact B1709355
  · exact B1709359
  · exact B1709363
  · exact B1709367
  · exact B1709371
  · exact B1709375
  · exact B1709379
  · exact B1709383
  · exact B1709387
  · exact B1709391
  · exact B1709395
  · exact B1709399
  · exact B1709403
  · exact B1709407
  · exact B1709411
  · exact B1709415
  · exact B1709419
  · exact B1709423
  · exact B1709427
  · exact B1709431
  · exact B1709435
  · exact B1709439
  · exact B1709443
  · exact B1709447
  · exact B1709451
  · exact B1709455
  · exact B1709459
  · exact B1709463
  · exact B1709467
  · exact B1709471
  · exact B1709475
  · exact B1709479
  · exact B1709483
  · exact B1709487
  · exact B1709491
  · exact B1709495
  · exact B1709499
  · exact B1709503
  · exact B1709507
  · exact B1709511
  · exact B1709515
  · exact B1709519
  · exact B1709523
  · exact B1709527
  · exact B1709531
  · exact B1709535
  · exact B1709539
  · exact B1709543
  · exact B1709547
  · exact B1709551
  · exact B1709555
  · exact B1709559
  · exact B1709563
  · exact B1709567
  · exact B1709571
  · exact B1709575
  · exact B1709579
  · exact B1709583
  · exact B1709587
  · exact B1709591
  · exact B1709595
  · exact B1709599
  · exact B1709603
  · exact B1709607
  · exact B1709611
  · exact B1709615
  · exact B1709619
  · exact B1709623
  · exact B1709627
  · exact B1709631
  · exact B1709635
  · exact B1709639
  · exact B1709643
  · exact B1709647
  · exact B1709651
  · exact B1709655
  · exact B1709659
  · exact B1709663
  · exact B1709667
  · exact B1709671
  · exact B1709675
  · exact B1709679
  · exact B1709683
  · exact B1709687
  · exact B1709691
  · exact B1709695
  · exact B1709699
  · exact B1709703
  · exact B1709707
  · exact B1709711
  · exact B1709715
  · exact B1709719
  · exact B1709723
  · exact B1709727
  · exact B1709731
  · exact B1709735
  · exact B1709739
  · exact B1709743
  · exact B1709747
  · exact B1709751
  · exact B1709755
  · exact B1709759
  · exact B1709763
  · exact B1709767
  · exact B1709771
  · exact B1709775
  · exact B1709779
  · exact B1709783
  · exact B1709787
  · exact B1709791
  · exact B1709795
  · exact B1709799
  · exact B1709803
  · exact B1709807
  · exact B1709811
  · exact B1709815
  · exact B1709819
  · exact B1709823
  · exact B1709827
  · exact B1709831
  · exact B1709835
  · exact B1709839
  · exact B1709843
  · exact B1709847
  · exact B1709851
  · exact B1709855
  · exact B1709859
  · exact B1709863
  · exact B1709867
  · exact B1709871
  · exact B1709875
  · exact B1709879
  · exact B1709883
  · exact B1709887
  · exact B1709891
  · exact B1709895
  · exact B1709899
  · exact B1709903
  · exact B1709907
  · exact B1709911
  · exact B1709915
  · exact B1709919
  · exact B1709923
  · exact B1709927
  · exact B1709931
  · exact B1709935
  · exact B1709939
  · exact B1709943
  · exact B1709947
  · exact B1709951
  · exact B1709955
  · exact B1709959
  · exact B1709963
  · exact B1709967
  · exact B1709971
  · exact B1709975
  · exact B1709979
  · exact B1709983
  · exact B1709987
  · exact B1709991
  · exact B1709995
  · exact B1709999
  · exact B1710003
  · exact B1710007
  · exact B1710011
  · exact B1710015
  · exact B1710019
  · exact B1710023
  · exact B1710027
  · exact B1710031
  · exact B1710035
  · exact B1710039
  · exact B1710043
  · exact B1710047
  · exact B1710051
  · exact B1710055
  · exact B1710059
  · exact B1710063
  · exact B1710067
  · exact B1710071
  · exact B1710075
  · exact B1710079
  · exact B1710083
  · exact B1710087
  · exact B1710091
  · exact B1710095
  · exact B1710099
  · exact B1710103
  · exact B1710107
  · exact B1710111
  · exact B1710115
  · exact B1710119
  · exact B1710123
  · exact B1710127
  · exact B1710131
  · exact B1710135
  · exact B1710139
  · exact B1710143
  · exact B1710147
  · exact B1710151
  · exact B1710155
  · exact B1710159
  · exact B1710163
  · exact B1710167
  · exact B1710171
  · exact B1710175
  · exact B1710179
  · exact B1710183
  · exact B1710187
  · exact B1710191
  · exact B1710195
  · exact B1710199
  · exact B1710203
  · exact B1710207
  · exact B1710211
  · exact B1710215
  · exact B1710219
  · exact B1710223
  · exact B1710227
  · exact B1710231
  · exact B1710235
  · exact B1710239
  · exact B1710243
  · exact B1710247
  · exact B1710251
  · exact B1710255
  · exact B1710259
  · exact B1710263
  · exact B1710267
  · exact B1710271
  · exact B1710275
  · exact B1710279
  · exact B1710283
  · exact B1710287
  · exact B1710291
  · exact B1710295
  · exact B1710299
  · exact B1710303
  · exact B1710307
  · exact B1710311
  · exact B1710315
  · exact B1710319
  · exact B1710323
  · exact B1710327
  · exact B1710331
  · exact B1710335
  · exact B1710339
  · exact B1710343
  · exact B1710347
  · exact B1710351
  · exact B1710355
  · exact B1710359
  · exact B1710363
  · exact B1710367
  · exact B1710371
  · exact B1710375
  · exact B1710379
  · exact B1710383
  · exact B1710387
  · exact B1710391
  · exact B1710395
  · exact B1710399
  · exact B1710403
  · exact B1710407
  · exact B1710411
  · exact B1710415
  · exact B1710419
  · exact B1710423
  · exact B1710427
  · exact B1710431
  · exact B1710435
  · exact B1710439
  · exact B1710443
  · exact B1710447
  · exact B1710451
  · exact B1710455
  · exact B1710459
  · exact B1710463
  · exact B1710467
  · exact B1710471
  · exact B1710475
  · exact B1710479
  · exact B1710483
  · exact B1710487
  · exact B1710491
  · exact B1710495
  · exact B1710499
  · exact B1710503
  · exact B1710507
  · exact B1710511
  · exact B1710515
  · exact B1710519
  · exact B1710523
  · exact B1710527
  · exact B1710531
  · exact B1710535
  · exact B1710539
  · exact B1710543
  · exact B1710547
  · exact B1710551
  · exact B1710555
  · exact B1710559
  · exact B1710563
  · exact B1710567
  · exact B1710571
  · exact B1710575
  · exact B1710579
  · exact B1710583
  · exact B1710587
  · exact B1710591
  · exact B1710595
  · exact B1710599
  · exact B1710603
  · exact B1710607
  · exact B1710611
  · exact B1710615
  · exact B1710619
  · exact B1710623
  · exact B1710627
  · exact B1710631
  · exact B1710635
  · exact B1710639
  · exact B1710643
  · exact B1710647
  · exact B1710651
  · exact B1710655
  · exact B1710659
  · exact B1710663
  · exact B1710667
  · exact B1710671
  · exact B1710675
  · exact B1710679
  · exact B1710683
  · exact B1710687
  · exact B1710691
  · exact B1710695
  · exact B1710699
  · exact B1710703
  · exact B1710707
  · exact B1710711
  · exact B1710715
  · exact B1710719
  · exact B1710723
  · exact B1710727
  · exact B1710731
  · exact B1710735
  · exact B1710739
  · exact B1710743
  · exact B1710747
  · exact B1710751
  · exact B1710755
  · exact B1710759
  · exact B1710763
  · exact B1710767
  · exact B1710771
  · exact B1710775
  · exact B1710779
  · exact B1710783
  · exact B1710787
  · exact B1710791
  · exact B1710795
  · exact B1710799
  · exact B1710803
  · exact B1710807
  · exact B1710811
  · exact B1710815
  · exact B1710819
  · exact B1710823
  · exact B1710827
  · exact B1710831
  · exact B1710835
  · exact B1710839
  · exact B1710843
  · exact B1710847
  · exact B1710851
  · exact B1710855
  · exact B1710859
  · exact B1710863
  · exact B1710867
  · exact B1710871
  · exact B1710875
  · exact B1710879
  · exact B1710883
  · exact B1710887
  · exact B1710891
  · exact B1710895
  · exact B1710899
  · exact B1710903
  · exact B1710907
  · exact B1710911
  · exact B1710915
  · exact B1710919
  · exact B1710923
  · exact B1710927
  · exact B1710931
  · exact B1710935
  · exact B1710939
  · exact B1710943
  · exact B1710947
  · exact B1710951
  · exact B1710955
  · exact B1710959
  · exact B1710963
  · exact B1710967
  · exact B1710971
  · exact B1710975
  · exact B1710979
  · exact B1710983
  · exact B1710987
  · exact B1710991
  · exact B1710995
  · exact B1710999
  · exact B1711003
  · exact B1711007
  · exact B1711011
  · exact B1711015
  · exact B1711019
  · exact B1711023
  · exact B1711027
  · exact B1711031
  · exact B1711035
  · exact B1711039
  · exact B1711043
  · exact B1711047
  · exact B1711051
  · exact B1711055

theorem solution (m : ℕ) (hlo : 1709055 ≤ m) (hhi : m ≤ 1711055) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 427263 ≤ j := by omega
    have hj2 : j ≤ 427763 := by omega
    have hb : Blo 1709055 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
