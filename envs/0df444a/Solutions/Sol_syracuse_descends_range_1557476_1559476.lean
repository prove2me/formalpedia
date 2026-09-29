-- Prove2me | solution 1 for syracuse_descends_range_1557476_1559476
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:06:06.194622+00:00
-- url     : https://prove2.me/submissions/52e573e9-cb78-4dcd-95ff-bc5680ffce6a

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


theorem B1753105 : Blo 1557476 1753105 := bbase (se 2 (by rfl) ⟨657414, by rfl⟩ : syracuseStep 1753105 = 1314829) (by norm_num)
theorem B2629685 : Blo 1557476 2629685 := bbase (se 5 (by rfl) ⟨123266, by rfl⟩ : syracuseStep 2629685 = 246533) (by norm_num)
theorem B1753141 : Blo 1557476 1753141 := bbase (se 5 (by rfl) ⟨82178, by rfl⟩ : syracuseStep 1753141 = 164357) (by norm_num)
theorem B3506237 : Blo 1557476 3506237 := bbase (se 3 (by rfl) ⟨657419, by rfl⟩ : syracuseStep 3506237 = 1314839) (by norm_num)
theorem B1753177 : Blo 1557476 1753177 := bbase (se 2 (by rfl) ⟨657441, by rfl⟩ : syracuseStep 1753177 = 1314883) (by norm_num)
theorem B3743837 : Blo 1557476 3743837 := bbase (se 3 (by rfl) ⟨701969, by rfl⟩ : syracuseStep 3743837 = 1403939) (by norm_num)
theorem B5914741 : Blo 1557476 5914741 := bbase (se 5 (by rfl) ⟨277253, by rfl⟩ : syracuseStep 5914741 = 554507) (by norm_num)
theorem B1753213 : Blo 1557476 1753213 := bbase (se 3 (by rfl) ⟨328727, by rfl⟩ : syracuseStep 1753213 = 657455) (by norm_num)
theorem B3506309 : Blo 1557476 3506309 := bbase (se 4 (by rfl) ⟨328716, by rfl⟩ : syracuseStep 3506309 = 657433) (by norm_num)
theorem B1753249 : Blo 1557476 1753249 := bbase (se 2 (by rfl) ⟨657468, by rfl⟩ : syracuseStep 1753249 = 1314937) (by norm_num)
theorem B2957485 : Blo 1557476 2957485 := bbase (se 3 (by rfl) ⟨554528, by rfl⟩ : syracuseStep 2957485 = 1109057) (by norm_num)
theorem B2629813 : Blo 1557476 2629813 := bbase (se 5 (by rfl) ⟨123272, by rfl⟩ : syracuseStep 2629813 = 246545) (by norm_num)
theorem B1753285 : Blo 1557476 1753285 := bbase (se 4 (by rfl) ⟨164370, by rfl⟩ : syracuseStep 1753285 = 328741) (by norm_num)
theorem B1851589 : Blo 1557476 1851589 := bbase (se 4 (by rfl) ⟨173586, by rfl⟩ : syracuseStep 1851589 = 347173) (by norm_num)
theorem B3506381 : Blo 1557476 3506381 := bbase (se 3 (by rfl) ⟨657446, by rfl⟩ : syracuseStep 3506381 = 1314893) (by norm_num)
theorem B1753321 : Blo 1557476 1753321 := bbase (se 2 (by rfl) ⟨657495, by rfl⟩ : syracuseStep 1753321 = 1314991) (by norm_num)
theorem B2629901 : Blo 1557476 2629901 := bbase (se 3 (by rfl) ⟨493106, by rfl⟩ : syracuseStep 2629901 = 986213) (by norm_num)
theorem B1753357 : Blo 1557476 1753357 := bbase (se 3 (by rfl) ⟨328754, by rfl⟩ : syracuseStep 1753357 = 657509) (by norm_num)
theorem B2220301 : Blo 1557476 2220301 := bbase (se 3 (by rfl) ⟨416306, by rfl⟩ : syracuseStep 2220301 = 832613) (by norm_num)
theorem B3506453 : Blo 1557476 3506453 := bbase (se 6 (by rfl) ⟨82182, by rfl⟩ : syracuseStep 3506453 = 164365) (by norm_num)
theorem B1663265 : Blo 1557476 1663265 := bbase (se 2 (by rfl) ⟨623724, by rfl⟩ : syracuseStep 1663265 = 1247449) (by norm_num)
theorem B1753393 : Blo 1557476 1753393 := bbase (se 2 (by rfl) ⟨657522, by rfl⟩ : syracuseStep 1753393 = 1315045) (by norm_num)
theorem B1802549 : Blo 1557476 1802549 := bbase (se 5 (by rfl) ⟨84494, by rfl⟩ : syracuseStep 1802549 = 168989) (by norm_num)
theorem B2957629 : Blo 1557476 2957629 := bbase (se 3 (by rfl) ⟨554555, by rfl⟩ : syracuseStep 2957629 = 1109111) (by norm_num)
theorem B7889237 : Blo 1557476 7889237 := bbase (se 10 (by rfl) ⟨11556, by rfl⟩ : syracuseStep 7889237 = 23113) (by norm_num)
theorem B1753429 : Blo 1557476 1753429 := bbase (se 10 (by rfl) ⟨2568, by rfl⟩ : syracuseStep 1753429 = 5137) (by norm_num)
theorem B47997269 : Blo 1557476 47997269 := bbase (se 10 (by rfl) ⟨70308, by rfl⟩ : syracuseStep 47997269 = 140617) (by norm_num)
theorem B3506525 : Blo 1557476 3506525 := bbase (se 3 (by rfl) ⟨657473, by rfl⟩ : syracuseStep 3506525 = 1314947) (by norm_num)
theorem B1753465 : Blo 1557476 1753465 := bbase (se 2 (by rfl) ⟨657549, by rfl⟩ : syracuseStep 1753465 = 1315099) (by norm_num)
theorem B5259653 : Blo 1557476 5259653 := bbase (se 4 (by rfl) ⟨493092, by rfl⟩ : syracuseStep 5259653 = 986185) (by norm_num)
theorem B2630029 : Blo 1557476 2630029 := bbase (se 3 (by rfl) ⟨493130, by rfl⟩ : syracuseStep 2630029 = 986261) (by norm_num)
theorem B14975381 : Blo 1557476 14975381 := bbase (se 6 (by rfl) ⟨350985, by rfl⟩ : syracuseStep 14975381 = 701971) (by norm_num)
theorem B1778069 : Blo 1557476 1778069 := bbase (se 6 (by rfl) ⟨41673, by rfl⟩ : syracuseStep 1778069 = 83347) (by norm_num)
theorem B1753501 : Blo 1557476 1753501 := bbase (se 3 (by rfl) ⟨328781, by rfl⟩ : syracuseStep 1753501 = 657563) (by norm_num)
theorem B5915045 : Blo 1557476 5915045 := bbase (se 4 (by rfl) ⟨554535, by rfl⟩ : syracuseStep 5915045 = 1109071) (by norm_num)
theorem B3506597 : Blo 1557476 3506597 := bbase (se 4 (by rfl) ⟨328743, by rfl⟩ : syracuseStep 3506597 = 657487) (by norm_num)
theorem B1753537 : Blo 1557476 1753537 := bbase (se 2 (by rfl) ⟨657576, by rfl⟩ : syracuseStep 1753537 = 1315153) (by norm_num)
theorem B1663453 : Blo 1557476 1663453 := bbase (se 3 (by rfl) ⟨311897, by rfl⟩ : syracuseStep 1663453 = 623795) (by norm_num)
theorem B2957789 : Blo 1557476 2957789 := bbase (se 3 (by rfl) ⟨554585, by rfl⟩ : syracuseStep 2957789 = 1109171) (by norm_num)
theorem B2630117 : Blo 1557476 2630117 := bbase (se 4 (by rfl) ⟨246573, by rfl⟩ : syracuseStep 2630117 = 493147) (by norm_num)
theorem B1753573 : Blo 1557476 1753573 := bbase (se 4 (by rfl) ⟨164397, by rfl⟩ : syracuseStep 1753573 = 328795) (by norm_num)
theorem B3506669 : Blo 1557476 3506669 := bbase (se 3 (by rfl) ⟨657500, by rfl⟩ : syracuseStep 3506669 = 1315001) (by norm_num)
theorem B1753609 : Blo 1557476 1753609 := bbase (se 2 (by rfl) ⟨657603, by rfl⟩ : syracuseStep 1753609 = 1315207) (by norm_num)
theorem B8430101 : Blo 1557476 8430101 := bbase (se 6 (by rfl) ⟨197580, by rfl⟩ : syracuseStep 8430101 = 395161) (by norm_num)
theorem B1753645 : Blo 1557476 1753645 := bbase (se 3 (by rfl) ⟨328808, by rfl⟩ : syracuseStep 1753645 = 657617) (by norm_num)
theorem B3506741 : Blo 1557476 3506741 := bbase (se 5 (by rfl) ⟨164378, by rfl⟩ : syracuseStep 3506741 = 328757) (by norm_num)
theorem B1753681 : Blo 1557476 1753681 := bbase (se 2 (by rfl) ⟨657630, by rfl⟩ : syracuseStep 1753681 = 1315261) (by norm_num)
theorem B7111253 : Blo 1557476 7111253 := bbase (se 8 (by rfl) ⟨41667, by rfl⟩ : syracuseStep 7111253 = 83335) (by norm_num)
theorem B2630245 : Blo 1557476 2630245 := bbase (se 4 (by rfl) ⟨246585, by rfl⟩ : syracuseStep 2630245 = 493171) (by norm_num)
theorem B2957933 : Blo 1557476 2957933 := bbase (se 3 (by rfl) ⟨554612, by rfl⟩ : syracuseStep 2957933 = 1109225) (by norm_num)
theorem B1753717 : Blo 1557476 1753717 := bbase (se 5 (by rfl) ⟨82205, by rfl⟩ : syracuseStep 1753717 = 164411) (by norm_num)
theorem B3506813 : Blo 1557476 3506813 := bbase (se 3 (by rfl) ⟨657527, by rfl⟩ : syracuseStep 3506813 = 1315055) (by norm_num)
theorem B1753753 : Blo 1557476 1753753 := bbase (se 2 (by rfl) ⟨657657, by rfl⟩ : syracuseStep 1753753 = 1315315) (by norm_num)
theorem B2630333 : Blo 1557476 2630333 := bbase (se 3 (by rfl) ⟨493187, by rfl⟩ : syracuseStep 2630333 = 986375) (by norm_num)
theorem B1753789 : Blo 1557476 1753789 := bbase (se 3 (by rfl) ⟨328835, by rfl⟩ : syracuseStep 1753789 = 657671) (by norm_num)
theorem B3506885 : Blo 1557476 3506885 := bbase (se 4 (by rfl) ⟨328770, by rfl⟩ : syracuseStep 3506885 = 657541) (by norm_num)
theorem B3744461 : Blo 1557476 3744461 := bbase (se 3 (by rfl) ⟨702086, by rfl⟩ : syracuseStep 3744461 = 1404173) (by norm_num)
theorem B1753825 : Blo 1557476 1753825 := bbase (se 2 (by rfl) ⟨657684, by rfl⟩ : syracuseStep 1753825 = 1315369) (by norm_num)
theorem B7111397 : Blo 1557476 7111397 := bbase (se 4 (by rfl) ⟨666693, by rfl⟩ : syracuseStep 7111397 = 1333387) (by norm_num)
theorem B1753861 : Blo 1557476 1753861 := bbase (se 4 (by rfl) ⟨164424, by rfl⟩ : syracuseStep 1753861 = 328849) (by norm_num)
theorem B3506957 : Blo 1557476 3506957 := bbase (se 3 (by rfl) ⟨657554, by rfl⟩ : syracuseStep 3506957 = 1315109) (by norm_num)
theorem B1753897 : Blo 1557476 1753897 := bbase (se 2 (by rfl) ⟨657711, by rfl⟩ : syracuseStep 1753897 = 1315423) (by norm_num)
theorem B5260085 : Blo 1557476 5260085 := bbase (se 5 (by rfl) ⟨246566, by rfl⟩ : syracuseStep 5260085 = 493133) (by norm_num)
theorem B2630461 : Blo 1557476 2630461 := bbase (se 3 (by rfl) ⟨493211, by rfl⟩ : syracuseStep 2630461 = 986423) (by norm_num)
theorem B1753933 : Blo 1557476 1753933 := bbase (se 3 (by rfl) ⟨328862, by rfl⟩ : syracuseStep 1753933 = 657725) (by norm_num)
theorem B3507029 : Blo 1557476 3507029 := bbase (se 9 (by rfl) ⟨10274, by rfl⟩ : syracuseStep 3507029 = 20549) (by norm_num)
theorem B1753969 : Blo 1557476 1753969 := bbase (se 2 (by rfl) ⟨657738, by rfl⟩ : syracuseStep 1753969 = 1315477) (by norm_num)
theorem B3326837 : Blo 1557476 3326837 := bbase (se 5 (by rfl) ⟨155945, by rfl⟩ : syracuseStep 3326837 = 311891) (by norm_num)
theorem B3556229 : Blo 1557476 3556229 := bbase (se 4 (by rfl) ⟨333396, by rfl⟩ : syracuseStep 3556229 = 666793) (by norm_num)
theorem B2958221 : Blo 1557476 2958221 := bbase (se 3 (by rfl) ⟨554666, by rfl⟩ : syracuseStep 2958221 = 1109333) (by norm_num)
theorem B2630549 : Blo 1557476 2630549 := bbase (se 6 (by rfl) ⟨61653, by rfl⟩ : syracuseStep 2630549 = 123307) (by norm_num)
theorem B1754005 : Blo 1557476 1754005 := bbase (se 6 (by rfl) ⟨41109, by rfl⟩ : syracuseStep 1754005 = 82219) (by norm_num)
theorem B3507101 : Blo 1557476 3507101 := bbase (se 3 (by rfl) ⟨657581, by rfl⟩ : syracuseStep 3507101 = 1315163) (by norm_num)
theorem B3556277 : Blo 1557476 3556277 := bbase (se 5 (by rfl) ⟨166700, by rfl⟩ : syracuseStep 3556277 = 333401) (by norm_num)
theorem B1754041 : Blo 1557476 1754041 := bbase (se 2 (by rfl) ⟨657765, by rfl⟩ : syracuseStep 1754041 = 1315531) (by norm_num)
theorem B1754077 : Blo 1557476 1754077 := bbase (se 3 (by rfl) ⟨328889, by rfl⟩ : syracuseStep 1754077 = 657779) (by norm_num)
theorem B3507173 : Blo 1557476 3507173 := bbase (se 4 (by rfl) ⟨328797, by rfl⟩ : syracuseStep 3507173 = 657595) (by norm_num)
theorem B3556349 : Blo 1557476 3556349 := bbase (se 3 (by rfl) ⟨666815, by rfl⟩ : syracuseStep 3556349 = 1333631) (by norm_num)
theorem B1754113 : Blo 1557476 1754113 := bbase (se 2 (by rfl) ⟨657792, by rfl⟩ : syracuseStep 1754113 = 1315585) (by norm_num)
theorem B2630677 : Blo 1557476 2630677 := bbase (se 6 (by rfl) ⟨61656, by rfl⟩ : syracuseStep 2630677 = 123313) (by norm_num)
theorem B2958373 : Blo 1557476 2958373 := bbase (se 4 (by rfl) ⟨277347, by rfl⟩ : syracuseStep 2958373 = 554695) (by norm_num)
theorem B1754149 : Blo 1557476 1754149 := bbase (se 4 (by rfl) ⟨164451, by rfl⟩ : syracuseStep 1754149 = 328903) (by norm_num)
theorem B3507245 : Blo 1557476 3507245 := bbase (se 3 (by rfl) ⟨657608, by rfl⟩ : syracuseStep 3507245 = 1315217) (by norm_num)
theorem B1754185 : Blo 1557476 1754185 := bbase (se 2 (by rfl) ⟨657819, by rfl⟩ : syracuseStep 1754185 = 1315639) (by norm_num)
theorem B3327077 : Blo 1557476 3327077 := bbase (se 4 (by rfl) ⟨311913, by rfl⟩ : syracuseStep 3327077 = 623827) (by norm_num)
theorem B2630765 : Blo 1557476 2630765 := bbase (se 3 (by rfl) ⟨493268, by rfl⟩ : syracuseStep 2630765 = 986537) (by norm_num)
theorem B1754221 : Blo 1557476 1754221 := bbase (se 3 (by rfl) ⟨328916, by rfl⟩ : syracuseStep 1754221 = 657833) (by norm_num)
theorem B3507317 : Blo 1557476 3507317 := bbase (se 5 (by rfl) ⟨164405, by rfl⟩ : syracuseStep 3507317 = 328811) (by norm_num)
theorem B4801669 : Blo 1557476 4801669 := bbase (se 4 (by rfl) ⟨450156, by rfl⟩ : syracuseStep 4801669 = 900313) (by norm_num)
theorem B1754257 : Blo 1557476 1754257 := bbase (se 2 (by rfl) ⟨657846, by rfl⟩ : syracuseStep 1754257 = 1315693) (by norm_num)
theorem B1754293 : Blo 1557476 1754293 := bbase (se 5 (by rfl) ⟨82232, by rfl⟩ : syracuseStep 1754293 = 164465) (by norm_num)
theorem B3507389 : Blo 1557476 3507389 := bbase (se 3 (by rfl) ⟨657635, by rfl⟩ : syracuseStep 3507389 = 1315271) (by norm_num)
theorem B3556541 : Blo 1557476 3556541 := bbase (se 3 (by rfl) ⟨666851, by rfl⟩ : syracuseStep 3556541 = 1333703) (by norm_num)
theorem B19981525 : Blo 1557476 19981525 := bbase (se 7 (by rfl) ⟨234158, by rfl⟩ : syracuseStep 19981525 = 468317) (by norm_num)
theorem B1754329 : Blo 1557476 1754329 := bbase (se 2 (by rfl) ⟨657873, by rfl⟩ : syracuseStep 1754329 = 1315747) (by norm_num)
theorem B5260517 : Blo 1557476 5260517 := bbase (se 4 (by rfl) ⟨493173, by rfl⟩ : syracuseStep 5260517 = 986347) (by norm_num)
theorem B2630893 : Blo 1557476 2630893 := bbase (se 3 (by rfl) ⟨493292, by rfl⟩ : syracuseStep 2630893 = 986585) (by norm_num)
theorem B4211957 : Blo 1557476 4211957 := bbase (se 5 (by rfl) ⟨197435, by rfl⟩ : syracuseStep 4211957 = 394871) (by norm_num)
theorem B1754365 : Blo 1557476 1754365 := bbase (se 3 (by rfl) ⟨328943, by rfl⟩ : syracuseStep 1754365 = 657887) (by norm_num)
theorem B4736261 : Blo 1557476 4736261 := bbase (se 4 (by rfl) ⟨444024, by rfl⟩ : syracuseStep 4736261 = 888049) (by norm_num)
theorem B3507461 : Blo 1557476 3507461 := bbase (se 4 (by rfl) ⟨328824, by rfl⟩ : syracuseStep 3507461 = 657649) (by norm_num)
theorem B1664273 : Blo 1557476 1664273 := bbase (se 2 (by rfl) ⟨624102, by rfl⟩ : syracuseStep 1664273 = 1248205) (by norm_num)
theorem B3999013 : Blo 1557476 3999013 := bbase (se 4 (by rfl) ⟨374907, by rfl⟩ : syracuseStep 3999013 = 749815) (by norm_num)
theorem B1754401 : Blo 1557476 1754401 := bbase (se 2 (by rfl) ⟨657900, by rfl⟩ : syracuseStep 1754401 = 1315801) (by norm_num)
theorem B2630981 : Blo 1557476 2630981 := bbase (se 4 (by rfl) ⟨246654, by rfl⟩ : syracuseStep 2630981 = 493309) (by norm_num)
theorem B3507533 : Blo 1557476 3507533 := bbase (se 3 (by rfl) ⟨657662, by rfl⟩ : syracuseStep 3507533 = 1315325) (by norm_num)
theorem B2958677 : Blo 1557476 2958677 := bbase (se 12 (by rfl) ⟨1083, by rfl⟩ : syracuseStep 2958677 = 2167) (by norm_num)
theorem B2368909 : Blo 1557476 2368909 := bbase (se 3 (by rfl) ⟨444170, by rfl⟩ : syracuseStep 2368909 = 888341) (by norm_num)
theorem B6653333 : Blo 1557476 6653333 := bbase (se 6 (by rfl) ⟨155937, by rfl⟩ : syracuseStep 6653333 = 311875) (by norm_num)
theorem B3507605 : Blo 1557476 3507605 := bbase (se 6 (by rfl) ⟨82209, by rfl⟩ : syracuseStep 3507605 = 164419) (by norm_num)
theorem B8881589 : Blo 1557476 8881589 := bbase (se 5 (by rfl) ⟨416324, by rfl⟩ : syracuseStep 8881589 = 832649) (by norm_num)
theorem B2631109 : Blo 1557476 2631109 := bbase (se 4 (by rfl) ⟨246666, by rfl⟩ : syracuseStep 2631109 = 493333) (by norm_num)
theorem B3507677 : Blo 1557476 3507677 := bbase (se 3 (by rfl) ⟨657689, by rfl⟩ : syracuseStep 3507677 = 1315379) (by norm_num)
theorem B2336237 : Blo 1557476 2336237 := bbase (se 3 (by rfl) ⟨438044, by rfl⟩ : syracuseStep 2336237 = 876089) (by norm_num)
theorem B2336261 : Blo 1557476 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B2336285 : Blo 1557476 2336285 := bbase (se 3 (by rfl) ⟨438053, by rfl⟩ : syracuseStep 2336285 = 876107) (by norm_num)
theorem B2631197 : Blo 1557476 2631197 := bbase (se 3 (by rfl) ⟨493349, by rfl⟩ : syracuseStep 2631197 = 986699) (by norm_num)
theorem B3507749 : Blo 1557476 3507749 := bbase (se 4 (by rfl) ⟨328851, by rfl⟩ : syracuseStep 3507749 = 657703) (by norm_num)
theorem B2336309 : Blo 1557476 2336309 := bbase (se 5 (by rfl) ⟨109514, by rfl⟩ : syracuseStep 2336309 = 219029) (by norm_num)
theorem B2336333 : Blo 1557476 2336333 := bbase (se 3 (by rfl) ⟨438062, by rfl⟩ : syracuseStep 2336333 = 876125) (by norm_num)
theorem B3327581 : Blo 1557476 3327581 := bbase (se 3 (by rfl) ⟨623921, by rfl⟩ : syracuseStep 3327581 = 1247843) (by norm_num)
theorem B2336357 : Blo 1557476 2336357 := bbase (se 4 (by rfl) ⟨219033, by rfl⟩ : syracuseStep 2336357 = 438067) (by norm_num)
theorem B3327589 : Blo 1557476 3327589 := bbase (se 4 (by rfl) ⟨311961, by rfl⟩ : syracuseStep 3327589 = 623923) (by norm_num)
theorem B7890533 : Blo 1557476 7890533 := bbase (se 4 (by rfl) ⟨739737, by rfl⟩ : syracuseStep 7890533 = 1479475) (by norm_num)
theorem B3507821 : Blo 1557476 3507821 := bbase (se 3 (by rfl) ⟨657716, by rfl⟩ : syracuseStep 3507821 = 1315433) (by norm_num)
theorem B2336381 : Blo 1557476 2336381 := bbase (se 3 (by rfl) ⟨438071, by rfl⟩ : syracuseStep 2336381 = 876143) (by norm_num)
theorem B6653573 : Blo 1557476 6653573 := bbase (se 4 (by rfl) ⟨623772, by rfl⟩ : syracuseStep 6653573 = 1247545) (by norm_num)
theorem B2336405 : Blo 1557476 2336405 := bbase (se 6 (by rfl) ⟨54759, by rfl⟩ : syracuseStep 2336405 = 109519) (by norm_num)
theorem B5260949 : Blo 1557476 5260949 := bbase (se 6 (by rfl) ⟨123303, by rfl⟩ : syracuseStep 5260949 = 246607) (by norm_num)
theorem B2631325 : Blo 1557476 2631325 := bbase (se 3 (by rfl) ⟨493373, by rfl⟩ : syracuseStep 2631325 = 986747) (by norm_num)
theorem B2336429 : Blo 1557476 2336429 := bbase (se 3 (by rfl) ⟨438080, by rfl⟩ : syracuseStep 2336429 = 876161) (by norm_num)
theorem B3507893 : Blo 1557476 3507893 := bbase (se 5 (by rfl) ⟨164432, by rfl⟩ : syracuseStep 3507893 = 328865) (by norm_num)
theorem B2336453 : Blo 1557476 2336453 := bbase (se 4 (by rfl) ⟨219042, by rfl⟩ : syracuseStep 2336453 = 438085) (by norm_num)
theorem B1664717 : Blo 1557476 1664717 := bbase (se 3 (by rfl) ⟨312134, by rfl⟩ : syracuseStep 1664717 = 624269) (by norm_num)
theorem B2311885 : Blo 1557476 2311885 := bbase (se 3 (by rfl) ⟨433478, by rfl⟩ : syracuseStep 2311885 = 866957) (by norm_num)
theorem B2336477 : Blo 1557476 2336477 := bbase (se 3 (by rfl) ⟨438089, by rfl⟩ : syracuseStep 2336477 = 876179) (by norm_num)
theorem B4990693 : Blo 1557476 4990693 := bbase (se 4 (by rfl) ⟨467877, by rfl⟩ : syracuseStep 4990693 = 935755) (by norm_num)
theorem B2336501 : Blo 1557476 2336501 := bbase (se 5 (by rfl) ⟨109523, by rfl⟩ : syracuseStep 2336501 = 219047) (by norm_num)
theorem B2631413 : Blo 1557476 2631413 := bbase (se 5 (by rfl) ⟨123347, by rfl⟩ : syracuseStep 2631413 = 246695) (by norm_num)
theorem B3507965 : Blo 1557476 3507965 := bbase (se 3 (by rfl) ⟨657743, by rfl⟩ : syracuseStep 3507965 = 1315487) (by norm_num)
theorem B2336525 : Blo 1557476 2336525 := bbase (se 3 (by rfl) ⟨438098, by rfl⟩ : syracuseStep 2336525 = 876197) (by norm_num)
theorem B2336549 : Blo 1557476 2336549 := bbase (se 4 (by rfl) ⟨219051, by rfl⟩ : syracuseStep 2336549 = 438103) (by norm_num)
theorem B9987893 : Blo 1557476 9987893 := bbase (se 5 (by rfl) ⟨468182, by rfl⟩ : syracuseStep 9987893 = 936365) (by norm_num)
theorem B2336573 : Blo 1557476 2336573 := bbase (se 3 (by rfl) ⟨438107, by rfl⟩ : syracuseStep 2336573 = 876215) (by norm_num)
theorem B3508037 : Blo 1557476 3508037 := bbase (se 4 (by rfl) ⟨328878, by rfl⟩ : syracuseStep 3508037 = 657757) (by norm_num)
theorem B2336597 : Blo 1557476 2336597 := bbase (se 9 (by rfl) ⟨6845, by rfl⟩ : syracuseStep 2336597 = 13691) (by norm_num)
theorem B2336621 : Blo 1557476 2336621 := bbase (se 3 (by rfl) ⟨438116, by rfl⟩ : syracuseStep 2336621 = 876233) (by norm_num)
theorem B13313909 : Blo 1557476 13313909 := bbase (se 5 (by rfl) ⟨624089, by rfl⟩ : syracuseStep 13313909 = 1248179) (by norm_num)
theorem B2631541 : Blo 1557476 2631541 := bbase (se 5 (by rfl) ⟨123353, by rfl⟩ : syracuseStep 2631541 = 246707) (by norm_num)
theorem B2336645 : Blo 1557476 2336645 := bbase (se 4 (by rfl) ⟨219060, by rfl⟩ : syracuseStep 2336645 = 438121) (by norm_num)
theorem B3508109 : Blo 1557476 3508109 := bbase (se 3 (by rfl) ⟨657770, by rfl⟩ : syracuseStep 3508109 = 1315541) (by norm_num)
theorem B2336669 : Blo 1557476 2336669 := bbase (se 3 (by rfl) ⟨438125, by rfl⟩ : syracuseStep 2336669 = 876251) (by norm_num)
theorem B2107309 : Blo 1557476 2107309 := bbase (se 3 (by rfl) ⟨395120, by rfl⟩ : syracuseStep 2107309 = 790241) (by norm_num)
theorem B2336693 : Blo 1557476 2336693 := bbase (se 5 (by rfl) ⟨109532, by rfl⟩ : syracuseStep 2336693 = 219065) (by norm_num)
theorem B1664965 : Blo 1557476 1664965 := bbase (se 4 (by rfl) ⟨156090, by rfl⟩ : syracuseStep 1664965 = 312181) (by norm_num)
theorem B2336717 : Blo 1557476 2336717 := bbase (se 3 (by rfl) ⟨438134, by rfl⟩ : syracuseStep 2336717 = 876269) (by norm_num)
theorem B11839445 : Blo 1557476 11839445 := bbase (se 7 (by rfl) ⟨138743, by rfl⟩ : syracuseStep 11839445 = 277487) (by norm_num)
theorem B3508181 : Blo 1557476 3508181 := bbase (se 7 (by rfl) ⟨41111, by rfl⟩ : syracuseStep 3508181 = 82223) (by norm_num)
theorem B2336741 : Blo 1557476 2336741 := bbase (se 4 (by rfl) ⟨219069, by rfl⟩ : syracuseStep 2336741 = 438139) (by norm_num)
theorem B2336765 : Blo 1557476 2336765 := bbase (se 3 (by rfl) ⟨438143, by rfl⟩ : syracuseStep 2336765 = 876287) (by norm_num)
theorem B2336789 : Blo 1557476 2336789 := bbase (se 6 (by rfl) ⟨54768, by rfl⟩ : syracuseStep 2336789 = 109537) (by norm_num)
theorem B3508253 : Blo 1557476 3508253 := bbase (se 3 (by rfl) ⟨657797, by rfl⟩ : syracuseStep 3508253 = 1315595) (by norm_num)
theorem B2336813 : Blo 1557476 2336813 := bbase (se 3 (by rfl) ⟨438152, by rfl⟩ : syracuseStep 2336813 = 876305) (by norm_num)
theorem B2336837 : Blo 1557476 2336837 := bbase (se 4 (by rfl) ⟨219078, by rfl⟩ : syracuseStep 2336837 = 438157) (by norm_num)
theorem B2959429 : Blo 1557476 2959429 := bbase (se 4 (by rfl) ⟨277446, by rfl⟩ : syracuseStep 2959429 = 554893) (by norm_num)
theorem B5261381 : Blo 1557476 5261381 := bbase (se 4 (by rfl) ⟨493254, by rfl⟩ : syracuseStep 5261381 = 986509) (by norm_num)
theorem B2336861 : Blo 1557476 2336861 := bbase (se 3 (by rfl) ⟨438161, by rfl⟩ : syracuseStep 2336861 = 876323) (by norm_num)
theorem B3508325 : Blo 1557476 3508325 := bbase (se 4 (by rfl) ⟨328905, by rfl⟩ : syracuseStep 3508325 = 657811) (by norm_num)
theorem B2336885 : Blo 1557476 2336885 := bbase (se 5 (by rfl) ⟨109541, by rfl⟩ : syracuseStep 2336885 = 219083) (by norm_num)
theorem B12814453 : Blo 1557476 12814453 := bbase (se 5 (by rfl) ⟨600677, by rfl⟩ : syracuseStep 12814453 = 1201355) (by norm_num)
theorem B3942533 : Blo 1557476 3942533 := bbase (se 4 (by rfl) ⟨369612, by rfl⟩ : syracuseStep 3942533 = 739225) (by norm_num)
theorem B2336909 : Blo 1557476 2336909 := bbase (se 3 (by rfl) ⟨438170, by rfl⟩ : syracuseStep 2336909 = 876341) (by norm_num)
theorem B2336933 : Blo 1557476 2336933 := bbase (se 4 (by rfl) ⟨219087, by rfl⟩ : syracuseStep 2336933 = 438175) (by norm_num)
theorem B3999917 : Blo 1557476 3999917 := bbase (se 3 (by rfl) ⟨749984, by rfl⟩ : syracuseStep 3999917 = 1499969) (by norm_num)
theorem B3508397 : Blo 1557476 3508397 := bbase (se 3 (by rfl) ⟨657824, by rfl⟩ : syracuseStep 3508397 = 1315649) (by norm_num)
theorem B2336957 : Blo 1557476 2336957 := bbase (se 3 (by rfl) ⟨438179, by rfl⟩ : syracuseStep 2336957 = 876359) (by norm_num)
theorem B2336981 : Blo 1557476 2336981 := bbase (se 7 (by rfl) ⟨27386, by rfl⟩ : syracuseStep 2336981 = 54773) (by norm_num)
theorem B2959573 : Blo 1557476 2959573 := bbase (se 7 (by rfl) ⟨34682, by rfl⟩ : syracuseStep 2959573 = 69365) (by norm_num)
theorem B2337005 : Blo 1557476 2337005 := bbase (se 3 (by rfl) ⟨438188, by rfl⟩ : syracuseStep 2337005 = 876377) (by norm_num)
theorem B3508469 : Blo 1557476 3508469 := bbase (se 5 (by rfl) ⟨164459, by rfl⟩ : syracuseStep 3508469 = 328919) (by norm_num)
theorem B2337029 : Blo 1557476 2337029 := bbase (se 4 (by rfl) ⟨219096, by rfl⟩ : syracuseStep 2337029 = 438193) (by norm_num)
theorem B2337053 : Blo 1557476 2337053 := bbase (se 3 (by rfl) ⟨438197, by rfl⟩ : syracuseStep 2337053 = 876395) (by norm_num)
theorem B2337077 : Blo 1557476 2337077 := bbase (se 5 (by rfl) ⟨109550, by rfl⟩ : syracuseStep 2337077 = 219101) (by norm_num)
theorem B3508541 : Blo 1557476 3508541 := bbase (se 3 (by rfl) ⟨657851, by rfl⟩ : syracuseStep 3508541 = 1315703) (by norm_num)
theorem B2337101 : Blo 1557476 2337101 := bbase (se 3 (by rfl) ⟨438206, by rfl⟩ : syracuseStep 2337101 = 876413) (by norm_num)
theorem B26978645 : Blo 1557476 26978645 := bbase (se 10 (by rfl) ⟨39519, by rfl⟩ : syracuseStep 26978645 = 79039) (by norm_num)
theorem B2337125 : Blo 1557476 2337125 := bbase (se 4 (by rfl) ⟨219105, by rfl⟩ : syracuseStep 2337125 = 438211) (by norm_num)
theorem B11831669 : Blo 1557476 11831669 := bbase (se 5 (by rfl) ⟨554609, by rfl⟩ : syracuseStep 11831669 = 1109219) (by norm_num)
theorem B2959733 : Blo 1557476 2959733 := bbase (se 5 (by rfl) ⟨138737, by rfl⟩ : syracuseStep 2959733 = 277475) (by norm_num)
theorem B2337149 : Blo 1557476 2337149 := bbase (se 3 (by rfl) ⟨438215, by rfl⟩ : syracuseStep 2337149 = 876431) (by norm_num)
theorem B3508613 : Blo 1557476 3508613 := bbase (se 4 (by rfl) ⟨328932, by rfl⟩ : syracuseStep 3508613 = 657865) (by norm_num)
theorem B2279821 : Blo 1557476 2279821 := bbase (se 3 (by rfl) ⟨427466, by rfl⟩ : syracuseStep 2279821 = 854933) (by norm_num)
theorem B2337173 : Blo 1557476 2337173 := bbase (se 6 (by rfl) ⟨54777, by rfl⟩ : syracuseStep 2337173 = 109555) (by norm_num)
theorem B2337197 : Blo 1557476 2337197 := bbase (se 3 (by rfl) ⟨438224, by rfl⟩ : syracuseStep 2337197 = 876449) (by norm_num)
theorem B2337221 : Blo 1557476 2337221 := bbase (se 4 (by rfl) ⟨219114, by rfl⟩ : syracuseStep 2337221 = 438229) (by norm_num)
theorem B3508685 : Blo 1557476 3508685 := bbase (se 3 (by rfl) ⟨657878, by rfl⟩ : syracuseStep 3508685 = 1315757) (by norm_num)
theorem B3942877 : Blo 1557476 3942877 := bbase (se 3 (by rfl) ⟨739289, by rfl⟩ : syracuseStep 3942877 = 1478579) (by norm_num)
theorem B2337245 : Blo 1557476 2337245 := bbase (se 3 (by rfl) ⟨438233, by rfl⟩ : syracuseStep 2337245 = 876467) (by norm_num)
theorem B5917157 : Blo 1557476 5917157 := bbase (se 4 (by rfl) ⟨554733, by rfl⟩ : syracuseStep 5917157 = 1109467) (by norm_num)
theorem B2337269 : Blo 1557476 2337269 := bbase (se 5 (by rfl) ⟨109559, by rfl⟩ : syracuseStep 2337269 = 219119) (by norm_num)
theorem B5261813 : Blo 1557476 5261813 := bbase (se 5 (by rfl) ⟨246647, by rfl⟩ : syracuseStep 5261813 = 493295) (by norm_num)
theorem B5401093 : Blo 1557476 5401093 := bbase (se 4 (by rfl) ⟨506352, by rfl⟩ : syracuseStep 5401093 = 1012705) (by norm_num)
theorem B2959877 : Blo 1557476 2959877 := bbase (se 4 (by rfl) ⟨277488, by rfl⟩ : syracuseStep 2959877 = 554977) (by norm_num)
theorem B2337293 : Blo 1557476 2337293 := bbase (se 3 (by rfl) ⟨438242, by rfl⟩ : syracuseStep 2337293 = 876485) (by norm_num)
theorem B3508757 : Blo 1557476 3508757 := bbase (se 6 (by rfl) ⟨82236, by rfl⟩ : syracuseStep 3508757 = 164473) (by norm_num)
theorem B2337317 : Blo 1557476 2337317 := bbase (se 4 (by rfl) ⟨219123, by rfl⟩ : syracuseStep 2337317 = 438247) (by norm_num)
theorem B2337341 : Blo 1557476 2337341 := bbase (se 3 (by rfl) ⟨438251, by rfl⟩ : syracuseStep 2337341 = 876503) (by norm_num)
theorem B3942989 : Blo 1557476 3942989 := bbase (se 3 (by rfl) ⟨739310, by rfl⟩ : syracuseStep 3942989 = 1478621) (by norm_num)
theorem B2337365 : Blo 1557476 2337365 := bbase (se 8 (by rfl) ⟨13695, by rfl⟩ : syracuseStep 2337365 = 27391) (by norm_num)
theorem B2337389 : Blo 1557476 2337389 := bbase (se 3 (by rfl) ⟨438260, by rfl⟩ : syracuseStep 2337389 = 876521) (by norm_num)
theorem B2337413 : Blo 1557476 2337413 := bbase (se 4 (by rfl) ⟨219132, by rfl⟩ : syracuseStep 2337413 = 438265) (by norm_num)
theorem B2337437 : Blo 1557476 2337437 := bbase (se 3 (by rfl) ⟨438269, by rfl⟩ : syracuseStep 2337437 = 876539) (by norm_num)
theorem B2337461 : Blo 1557476 2337461 := bbase (se 5 (by rfl) ⟨109568, by rfl⟩ : syracuseStep 2337461 = 219137) (by norm_num)
theorem B2337485 : Blo 1557476 2337485 := bbase (se 3 (by rfl) ⟨438278, by rfl⟩ : syracuseStep 2337485 = 876557) (by norm_num)
theorem B3328717 : Blo 1557476 3328717 := bbase (se 3 (by rfl) ⟨624134, by rfl⟩ : syracuseStep 3328717 = 1248269) (by norm_num)
theorem B2337509 : Blo 1557476 2337509 := bbase (se 4 (by rfl) ⟨219141, by rfl⟩ : syracuseStep 2337509 = 438283) (by norm_num)
theorem B2337533 : Blo 1557476 2337533 := bbase (se 3 (by rfl) ⟨438287, by rfl⟩ : syracuseStep 2337533 = 876575) (by norm_num)
theorem B5917445 : Blo 1557476 5917445 := bbase (se 4 (by rfl) ⟨554760, by rfl⟩ : syracuseStep 5917445 = 1109521) (by norm_num)
theorem B3943181 : Blo 1557476 3943181 := bbase (se 3 (by rfl) ⟨739346, by rfl⟩ : syracuseStep 3943181 = 1478693) (by norm_num)
theorem B2337557 : Blo 1557476 2337557 := bbase (se 6 (by rfl) ⟨54786, by rfl⟩ : syracuseStep 2337557 = 109573) (by norm_num)
theorem B2960165 : Blo 1557476 2960165 := bbase (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) (by norm_num)
theorem B2337581 : Blo 1557476 2337581 := bbase (se 3 (by rfl) ⟨438296, by rfl⟩ : syracuseStep 2337581 = 876593) (by norm_num)
theorem B4000565 : Blo 1557476 4000565 := bbase (se 5 (by rfl) ⟨187526, by rfl⟩ : syracuseStep 4000565 = 375053) (by norm_num)
theorem B2337605 : Blo 1557476 2337605 := bbase (se 4 (by rfl) ⟨219150, by rfl⟩ : syracuseStep 2337605 = 438301) (by norm_num)
theorem B2337629 : Blo 1557476 2337629 := bbase (se 3 (by rfl) ⟨438305, by rfl⟩ : syracuseStep 2337629 = 876611) (by norm_num)
theorem B2337653 : Blo 1557476 2337653 := bbase (se 5 (by rfl) ⟨109577, by rfl⟩ : syracuseStep 2337653 = 219155) (by norm_num)
theorem B7891829 : Blo 1557476 7891829 := bbase (se 5 (by rfl) ⟨369929, by rfl⟩ : syracuseStep 7891829 = 739859) (by norm_num)
theorem B2337677 : Blo 1557476 2337677 := bbase (se 3 (by rfl) ⟨438314, by rfl⟩ : syracuseStep 2337677 = 876629) (by norm_num)
theorem B2337701 : Blo 1557476 2337701 := bbase (se 4 (by rfl) ⟨219159, by rfl⟩ : syracuseStep 2337701 = 438319) (by norm_num)
theorem B5262245 : Blo 1557476 5262245 := bbase (se 4 (by rfl) ⟨493335, by rfl⟩ : syracuseStep 5262245 = 986671) (by norm_num)
theorem B2337725 : Blo 1557476 2337725 := bbase (se 3 (by rfl) ⟨438323, by rfl⟩ : syracuseStep 2337725 = 876647) (by norm_num)
theorem B2960317 : Blo 1557476 2960317 := bbase (se 3 (by rfl) ⟨555059, by rfl⟩ : syracuseStep 2960317 = 1110119) (by norm_num)
theorem B2337749 : Blo 1557476 2337749 := bbase (se 7 (by rfl) ⟨27395, by rfl⟩ : syracuseStep 2337749 = 54791) (by norm_num)
theorem B2337773 : Blo 1557476 2337773 := bbase (se 3 (by rfl) ⟨438332, by rfl⟩ : syracuseStep 2337773 = 876665) (by norm_num)
theorem B2337797 : Blo 1557476 2337797 := bbase (se 4 (by rfl) ⟨219168, by rfl⟩ : syracuseStep 2337797 = 438337) (by norm_num)
theorem B2337821 : Blo 1557476 2337821 := bbase (se 3 (by rfl) ⟨438341, by rfl⟩ : syracuseStep 2337821 = 876683) (by norm_num)
theorem B2337845 : Blo 1557476 2337845 := bbase (se 5 (by rfl) ⟨109586, by rfl⟩ : syracuseStep 2337845 = 219173) (by norm_num)
theorem B3329093 : Blo 1557476 3329093 := bbase (se 4 (by rfl) ⟨312102, by rfl⟩ : syracuseStep 3329093 = 624205) (by norm_num)
theorem B2337869 : Blo 1557476 2337869 := bbase (se 3 (by rfl) ⟨438350, by rfl⟩ : syracuseStep 2337869 = 876701) (by norm_num)
theorem B2370637 : Blo 1557476 2370637 := bbase (se 3 (by rfl) ⟨444494, by rfl⟩ : syracuseStep 2370637 = 888989) (by norm_num)
theorem B11103317 : Blo 1557476 11103317 := bbase (se 8 (by rfl) ⟨65058, by rfl⟩ : syracuseStep 11103317 = 130117) (by norm_num)
theorem B3943525 : Blo 1557476 3943525 := bbase (se 4 (by rfl) ⟨369705, by rfl⟩ : syracuseStep 3943525 = 739411) (by norm_num)
theorem B2337893 : Blo 1557476 2337893 := bbase (se 4 (by rfl) ⟨219177, by rfl⟩ : syracuseStep 2337893 = 438355) (by norm_num)
theorem B2337917 : Blo 1557476 2337917 := bbase (se 3 (by rfl) ⟨438359, by rfl⟩ : syracuseStep 2337917 = 876719) (by norm_num)
theorem B2337941 : Blo 1557476 2337941 := bbase (se 6 (by rfl) ⟨54795, by rfl⟩ : syracuseStep 2337941 = 109591) (by norm_num)
theorem B2337965 : Blo 1557476 2337965 := bbase (se 3 (by rfl) ⟨438368, by rfl⟩ : syracuseStep 2337965 = 876737) (by norm_num)
theorem B2337989 : Blo 1557476 2337989 := bbase (se 4 (by rfl) ⟨219186, by rfl⟩ : syracuseStep 2337989 = 438373) (by norm_num)
theorem B21318869 : Blo 1557476 21318869 := bbase (se 7 (by rfl) ⟨249830, by rfl⟩ : syracuseStep 21318869 = 499661) (by norm_num)
theorem B3943637 : Blo 1557476 3943637 := bbase (se 7 (by rfl) ⟨46214, by rfl⟩ : syracuseStep 3943637 = 92429) (by norm_num)
theorem B2338013 : Blo 1557476 2338013 := bbase (se 3 (by rfl) ⟨438377, by rfl⟩ : syracuseStep 2338013 = 876755) (by norm_num)
theorem B12807413 : Blo 1557476 12807413 := bbase (se 5 (by rfl) ⟨600347, by rfl⟩ : syracuseStep 12807413 = 1200695) (by norm_num)
theorem B2338037 : Blo 1557476 2338037 := bbase (se 5 (by rfl) ⟨109595, by rfl⟩ : syracuseStep 2338037 = 219191) (by norm_num)
theorem B2338061 : Blo 1557476 2338061 := bbase (se 3 (by rfl) ⟨438386, by rfl⟩ : syracuseStep 2338061 = 876773) (by norm_num)
theorem B2338085 : Blo 1557476 2338085 := bbase (se 4 (by rfl) ⟨219195, by rfl⟩ : syracuseStep 2338085 = 438391) (by norm_num)
theorem B2338109 : Blo 1557476 2338109 := bbase (se 3 (by rfl) ⟨438395, by rfl⟩ : syracuseStep 2338109 = 876791) (by norm_num)
theorem B2338133 : Blo 1557476 2338133 := bbase (se 11 (by rfl) ⟨1712, by rfl⟩ : syracuseStep 2338133 = 3425) (by norm_num)
theorem B5262677 : Blo 1557476 5262677 := bbase (se 11 (by rfl) ⟨3854, by rfl⟩ : syracuseStep 5262677 = 7709) (by norm_num)
theorem B2338157 : Blo 1557476 2338157 := bbase (se 3 (by rfl) ⟨438404, by rfl⟩ : syracuseStep 2338157 = 876809) (by norm_num)
theorem B2338181 : Blo 1557476 2338181 := bbase (se 4 (by rfl) ⟨219204, by rfl⟩ : syracuseStep 2338181 = 438409) (by norm_num)
theorem B3943829 : Blo 1557476 3943829 := bbase (se 6 (by rfl) ⟨92433, by rfl⟩ : syracuseStep 3943829 = 184867) (by norm_num)
theorem B2338205 : Blo 1557476 2338205 := bbase (se 3 (by rfl) ⟨438413, by rfl⟩ : syracuseStep 2338205 = 876827) (by norm_num)
theorem B1871269 : Blo 1557476 1871269 := bbase (se 4 (by rfl) ⟨175431, by rfl⟩ : syracuseStep 1871269 = 350863) (by norm_num)
theorem B2338229 : Blo 1557476 2338229 := bbase (se 5 (by rfl) ⟨109604, by rfl⟩ : syracuseStep 2338229 = 219209) (by norm_num)
theorem B2338253 : Blo 1557476 2338253 := bbase (se 3 (by rfl) ⟨438422, by rfl⟩ : syracuseStep 2338253 = 876845) (by norm_num)
theorem B5615077 : Blo 1557476 5615077 := bbase (se 4 (by rfl) ⟨526413, by rfl⟩ : syracuseStep 5615077 = 1052827) (by norm_num)
theorem B2338277 : Blo 1557476 2338277 := bbase (se 4 (by rfl) ⟨219213, by rfl⟩ : syracuseStep 2338277 = 438427) (by norm_num)
theorem B2338301 : Blo 1557476 2338301 := bbase (se 3 (by rfl) ⟨438431, by rfl⟩ : syracuseStep 2338301 = 876863) (by norm_num)
theorem B2338325 : Blo 1557476 2338325 := bbase (se 6 (by rfl) ⟨54804, by rfl⟩ : syracuseStep 2338325 = 109609) (by norm_num)
theorem B2338349 : Blo 1557476 2338349 := bbase (se 3 (by rfl) ⟨438440, by rfl⟩ : syracuseStep 2338349 = 876881) (by norm_num)
theorem B2338373 : Blo 1557476 2338373 := bbase (se 4 (by rfl) ⟨219222, by rfl⟩ : syracuseStep 2338373 = 438445) (by norm_num)
theorem B2248285 : Blo 1557476 2248285 := bbase (se 3 (by rfl) ⟨421553, by rfl⟩ : syracuseStep 2248285 = 843107) (by norm_num)
theorem B2666077 : Blo 1557476 2666077 := bbase (se 3 (by rfl) ⟨499889, by rfl⟩ : syracuseStep 2666077 = 999779) (by norm_num)
theorem B2338397 : Blo 1557476 2338397 := bbase (se 3 (by rfl) ⟨438449, by rfl⟩ : syracuseStep 2338397 = 876899) (by norm_num)
theorem B2338421 : Blo 1557476 2338421 := bbase (se 5 (by rfl) ⟨109613, by rfl⟩ : syracuseStep 2338421 = 219227) (by norm_num)
theorem B2338445 : Blo 1557476 2338445 := bbase (se 3 (by rfl) ⟨438458, by rfl⟩ : syracuseStep 2338445 = 876917) (by norm_num)
theorem B9981589 : Blo 1557476 9981589 := bbase (se 6 (by rfl) ⟨233943, by rfl⟩ : syracuseStep 9981589 = 467887) (by norm_num)
theorem B2338469 : Blo 1557476 2338469 := bbase (se 4 (by rfl) ⟨219231, by rfl⟩ : syracuseStep 2338469 = 438463) (by norm_num)
theorem B2338493 : Blo 1557476 2338493 := bbase (se 3 (by rfl) ⟨438467, by rfl⟩ : syracuseStep 2338493 = 876935) (by norm_num)
theorem B2338517 : Blo 1557476 2338517 := bbase (se 7 (by rfl) ⟨27404, by rfl⟩ : syracuseStep 2338517 = 54809) (by norm_num)
theorem B3944173 : Blo 1557476 3944173 := bbase (se 3 (by rfl) ⟨739532, by rfl⟩ : syracuseStep 3944173 = 1479065) (by norm_num)
theorem B2338541 : Blo 1557476 2338541 := bbase (se 3 (by rfl) ⟨438476, by rfl⟩ : syracuseStep 2338541 = 876953) (by norm_num)
theorem B2338565 : Blo 1557476 2338565 := bbase (se 4 (by rfl) ⟨219240, by rfl⟩ : syracuseStep 2338565 = 438481) (by norm_num)
theorem B5263109 : Blo 1557476 5263109 := bbase (se 4 (by rfl) ⟨493416, by rfl⟩ : syracuseStep 5263109 = 986833) (by norm_num)
theorem B2338589 : Blo 1557476 2338589 := bbase (se 3 (by rfl) ⟨438485, by rfl⟩ : syracuseStep 2338589 = 876971) (by norm_num)
theorem B7491365 : Blo 1557476 7491365 := bbase (se 4 (by rfl) ⟨702315, by rfl⟩ : syracuseStep 7491365 = 1404631) (by norm_num)
theorem B2338613 : Blo 1557476 2338613 := bbase (se 5 (by rfl) ⟨109622, by rfl⟩ : syracuseStep 2338613 = 219245) (by norm_num)
theorem B2666309 : Blo 1557476 2666309 := bbase (se 4 (by rfl) ⟨249966, by rfl⟩ : syracuseStep 2666309 = 499933) (by norm_num)
theorem B2338637 : Blo 1557476 2338637 := bbase (se 3 (by rfl) ⟨438494, by rfl⟩ : syracuseStep 2338637 = 876989) (by norm_num)
theorem B3944285 : Blo 1557476 3944285 := bbase (se 3 (by rfl) ⟨739553, by rfl⟩ : syracuseStep 3944285 = 1479107) (by norm_num)
theorem B2338661 : Blo 1557476 2338661 := bbase (se 4 (by rfl) ⟨219249, by rfl⟩ : syracuseStep 2338661 = 438499) (by norm_num)
theorem B4435829 : Blo 1557476 4435829 := bbase (se 5 (by rfl) ⟨207929, by rfl⟩ : syracuseStep 4435829 = 415859) (by norm_num)
theorem B6655861 : Blo 1557476 6655861 := bbase (se 5 (by rfl) ⟨311993, by rfl⟩ : syracuseStep 6655861 = 623987) (by norm_num)
theorem B2338685 : Blo 1557476 2338685 := bbase (se 3 (by rfl) ⟨438503, by rfl⟩ : syracuseStep 2338685 = 877007) (by norm_num)
theorem B2338709 : Blo 1557476 2338709 := bbase (se 6 (by rfl) ⟨54813, by rfl⟩ : syracuseStep 2338709 = 109627) (by norm_num)
theorem B5918629 : Blo 1557476 5918629 := bbase (se 4 (by rfl) ⟨554871, by rfl⟩ : syracuseStep 5918629 = 1109743) (by norm_num)
theorem B2338733 : Blo 1557476 2338733 := bbase (se 3 (by rfl) ⟨438512, by rfl⟩ : syracuseStep 2338733 = 877025) (by norm_num)
theorem B2338757 : Blo 1557476 2338757 := bbase (se 4 (by rfl) ⟨219258, by rfl⟩ : syracuseStep 2338757 = 438517) (by norm_num)
theorem B2666461 : Blo 1557476 2666461 := bbase (se 3 (by rfl) ⟨499961, by rfl⟩ : syracuseStep 2666461 = 999923) (by norm_num)
theorem B2338781 : Blo 1557476 2338781 := bbase (se 3 (by rfl) ⟨438521, by rfl⟩ : syracuseStep 2338781 = 877043) (by norm_num)
theorem B2338805 : Blo 1557476 2338805 := bbase (se 5 (by rfl) ⟨109631, by rfl⟩ : syracuseStep 2338805 = 219263) (by norm_num)
theorem B3158021 : Blo 1557476 3158021 := bbase (se 4 (by rfl) ⟨296064, by rfl⟩ : syracuseStep 3158021 = 592129) (by norm_num)
theorem B2338829 : Blo 1557476 2338829 := bbase (se 3 (by rfl) ⟨438530, by rfl⟩ : syracuseStep 2338829 = 877061) (by norm_num)
theorem B3944477 : Blo 1557476 3944477 := bbase (se 3 (by rfl) ⟨739589, by rfl⟩ : syracuseStep 3944477 = 1479179) (by norm_num)
theorem B2338853 : Blo 1557476 2338853 := bbase (se 4 (by rfl) ⟨219267, by rfl⟩ : syracuseStep 2338853 = 438535) (by norm_num)
theorem B2338877 : Blo 1557476 2338877 := bbase (se 3 (by rfl) ⟨438539, by rfl⟩ : syracuseStep 2338877 = 877079) (by norm_num)
theorem B2338901 : Blo 1557476 2338901 := bbase (se 8 (by rfl) ⟨13704, by rfl⟩ : syracuseStep 2338901 = 27409) (by norm_num)
theorem B2338925 : Blo 1557476 2338925 := bbase (se 3 (by rfl) ⟨438548, by rfl⟩ : syracuseStep 2338925 = 877097) (by norm_num)
theorem B7893125 : Blo 1557476 7893125 := bbase (se 4 (by rfl) ⟨739980, by rfl⟩ : syracuseStep 7893125 = 1479961) (by norm_num)
theorem B2338949 : Blo 1557476 2338949 := bbase (se 4 (by rfl) ⟨219276, by rfl⟩ : syracuseStep 2338949 = 438553) (by norm_num)
theorem B2338973 : Blo 1557476 2338973 := bbase (se 3 (by rfl) ⟨438557, by rfl⟩ : syracuseStep 2338973 = 877115) (by norm_num)
theorem B8876213 : Blo 1557476 8876213 := bbase (se 5 (by rfl) ⟨416072, by rfl⟩ : syracuseStep 8876213 = 832145) (by norm_num)
theorem B2338997 : Blo 1557476 2338997 := bbase (se 5 (by rfl) ⟨109640, by rfl⟩ : syracuseStep 2338997 = 219281) (by norm_num)
theorem B2339021 : Blo 1557476 2339021 := bbase (se 3 (by rfl) ⟨438566, by rfl⟩ : syracuseStep 2339021 = 877133) (by norm_num)
theorem B5918933 : Blo 1557476 5918933 := bbase (se 7 (by rfl) ⟨69362, by rfl⟩ : syracuseStep 5918933 = 138725) (by norm_num)
theorem B2339045 : Blo 1557476 2339045 := bbase (se 4 (by rfl) ⟨219285, by rfl⟩ : syracuseStep 2339045 = 438571) (by norm_num)
theorem B2339069 : Blo 1557476 2339069 := bbase (se 3 (by rfl) ⟨438575, by rfl⟩ : syracuseStep 2339069 = 877151) (by norm_num)
theorem B2339093 : Blo 1557476 2339093 := bbase (se 6 (by rfl) ⟨54822, by rfl⟩ : syracuseStep 2339093 = 109645) (by norm_num)
theorem B1872173 : Blo 1557476 1872173 := bbase (se 3 (by rfl) ⟨351032, by rfl⟩ : syracuseStep 1872173 = 702065) (by norm_num)
theorem B2339117 : Blo 1557476 2339117 := bbase (se 3 (by rfl) ⟨438584, by rfl⟩ : syracuseStep 2339117 = 877169) (by norm_num)
theorem B2339141 : Blo 1557476 2339141 := bbase (se 4 (by rfl) ⟨219294, by rfl⟩ : syracuseStep 2339141 = 438589) (by norm_num)
theorem B2339165 : Blo 1557476 2339165 := bbase (se 3 (by rfl) ⟨438593, by rfl⟩ : syracuseStep 2339165 = 877187) (by norm_num)
theorem B3944821 : Blo 1557476 3944821 := bbase (se 5 (by rfl) ⟨184913, by rfl⟩ : syracuseStep 3944821 = 369827) (by norm_num)
theorem B2339189 : Blo 1557476 2339189 := bbase (se 5 (by rfl) ⟨109649, by rfl⟩ : syracuseStep 2339189 = 219299) (by norm_num)
theorem B2339213 : Blo 1557476 2339213 := bbase (se 3 (by rfl) ⟨438602, by rfl⟩ : syracuseStep 2339213 = 877205) (by norm_num)
theorem B3944933 : Blo 1557476 3944933 := bbase (se 4 (by rfl) ⟨369837, by rfl⟩ : syracuseStep 3944933 = 739675) (by norm_num)
theorem B7885349 : Blo 1557476 7885349 := bbase (se 4 (by rfl) ⟨739251, by rfl⟩ : syracuseStep 7885349 = 1478503) (by norm_num)
theorem B1872433 : Blo 1557476 1872433 := bbase (se 2 (by rfl) ⟨702162, by rfl⟩ : syracuseStep 1872433 = 1404325) (by norm_num)
theorem B4993589 : Blo 1557476 4993589 := bbase (se 5 (by rfl) ⟨234074, by rfl⟩ : syracuseStep 4993589 = 468149) (by norm_num)
theorem B4739717 : Blo 1557476 4739717 := bbase (se 4 (by rfl) ⟨444348, by rfl⟩ : syracuseStep 4739717 = 888697) (by norm_num)
theorem B3945125 : Blo 1557476 3945125 := bbase (se 4 (by rfl) ⟨369855, by rfl⟩ : syracuseStep 3945125 = 739711) (by norm_num)
theorem B1872625 : Blo 1557476 1872625 := bbase (se 2 (by rfl) ⟨702234, by rfl⟩ : syracuseStep 1872625 = 1404469) (by norm_num)
theorem B2667269 : Blo 1557476 2667269 := bbase (se 4 (by rfl) ⟨250056, by rfl⟩ : syracuseStep 2667269 = 500113) (by norm_num)
theorem B1872649 : Blo 1557476 1872649 := bbase (se 2 (by rfl) ⟨702243, by rfl⟩ : syracuseStep 1872649 = 1404487) (by norm_num)
theorem B1872653 : Blo 1557476 1872653 := bbase (se 3 (by rfl) ⟨351122, by rfl⟩ : syracuseStep 1872653 = 702245) (by norm_num)
theorem B13316885 : Blo 1557476 13316885 := bbase (se 6 (by rfl) ⟨312114, by rfl⟩ : syracuseStep 13316885 = 624229) (by norm_num)
theorem B1897249 : Blo 1557476 1897249 := bbase (se 2 (by rfl) ⟨711468, by rfl⟩ : syracuseStep 1897249 = 1422937) (by norm_num)
theorem B2495333 : Blo 1557476 2495333 := bbase (se 4 (by rfl) ⟨233937, by rfl⟩ : syracuseStep 2495333 = 467875) (by norm_num)
theorem B2806645 : Blo 1557476 2806645 := bbase (se 5 (by rfl) ⟨131561, by rfl⟩ : syracuseStep 2806645 = 263123) (by norm_num)
theorem B3945469 : Blo 1557476 3945469 := bbase (se 3 (by rfl) ⟨739775, by rfl⟩ : syracuseStep 3945469 = 1479551) (by norm_num)
theorem B3552269 : Blo 1557476 3552269 := bbase (se 3 (by rfl) ⟨666050, by rfl⟩ : syracuseStep 3552269 = 1332101) (by norm_num)
theorem B2806805 : Blo 1557476 2806805 := bbase (se 6 (by rfl) ⟨65784, by rfl⟩ : syracuseStep 2806805 = 131569) (by norm_num)
theorem B4437013 : Blo 1557476 4437013 := bbase (se 6 (by rfl) ⟨103992, by rfl⟩ : syracuseStep 4437013 = 207985) (by norm_num)
theorem B25621525 : Blo 1557476 25621525 := bbase (se 6 (by rfl) ⟨600504, by rfl⟩ : syracuseStep 25621525 = 1201009) (by norm_num)
theorem B2806861 : Blo 1557476 2806861 := bbase (se 3 (by rfl) ⟨526286, by rfl⟩ : syracuseStep 2806861 = 1052573) (by norm_num)
theorem B3847253 : Blo 1557476 3847253 := bbase (se 8 (by rfl) ⟨22542, by rfl⟩ : syracuseStep 3847253 = 45085) (by norm_num)
theorem B3945581 : Blo 1557476 3945581 := bbase (se 3 (by rfl) ⟨739796, by rfl⟩ : syracuseStep 3945581 = 1479593) (by norm_num)
theorem B1971317 : Blo 1557476 1971317 := bbase (se 5 (by rfl) ⟨92405, by rfl⟩ : syracuseStep 1971317 = 184811) (by norm_num)
theorem B1971373 : Blo 1557476 1971373 := bbase (se 3 (by rfl) ⟨369632, by rfl⟩ : syracuseStep 1971373 = 739265) (by norm_num)
theorem B4437173 : Blo 1557476 4437173 := bbase (se 5 (by rfl) ⟨207992, by rfl⟩ : syracuseStep 4437173 = 415985) (by norm_num)
theorem B3159253 : Blo 1557476 3159253 := bbase (se 7 (by rfl) ⟨37022, by rfl⟩ : syracuseStep 3159253 = 74045) (by norm_num)
theorem B14226677 : Blo 1557476 14226677 := bbase (se 5 (by rfl) ⟨666875, by rfl⟩ : syracuseStep 14226677 = 1333751) (by norm_num)
theorem B1873153 : Blo 1557476 1873153 := bbase (se 2 (by rfl) ⟨702432, by rfl⟩ : syracuseStep 1873153 = 1404865) (by norm_num)
theorem B1971469 : Blo 1557476 1971469 := bbase (se 3 (by rfl) ⟨369650, by rfl⟩ : syracuseStep 1971469 = 739301) (by norm_num)
theorem B2495789 : Blo 1557476 2495789 := bbase (se 3 (by rfl) ⟨467960, by rfl⟩ : syracuseStep 2495789 = 935921) (by norm_num)
theorem B3945773 : Blo 1557476 3945773 := bbase (se 3 (by rfl) ⟨739832, by rfl⟩ : syracuseStep 3945773 = 1479665) (by norm_num)
theorem B6657349 : Blo 1557476 6657349 := bbase (se 4 (by rfl) ⟨624126, by rfl⟩ : syracuseStep 6657349 = 1248253) (by norm_num)
theorem B6657365 : Blo 1557476 6657365 := bbase (se 14 (by rfl) ⟨609, by rfl⟩ : syracuseStep 6657365 = 1219) (by norm_num)
theorem B8877397 : Blo 1557476 8877397 := bbase (se 13 (by rfl) ⟨1625, by rfl⟩ : syracuseStep 8877397 = 3251) (by norm_num)
theorem B1873249 : Blo 1557476 1873249 := bbase (se 2 (by rfl) ⟨702468, by rfl⟩ : syracuseStep 1873249 = 1404937) (by norm_num)
theorem B7894421 : Blo 1557476 7894421 := bbase (se 6 (by rfl) ⟨185025, by rfl⟩ : syracuseStep 7894421 = 370051) (by norm_num)
theorem B4437413 : Blo 1557476 4437413 := bbase (se 4 (by rfl) ⟨416007, by rfl⟩ : syracuseStep 4437413 = 832015) (by norm_num)
theorem B5256629 : Blo 1557476 5256629 := bbase (se 5 (by rfl) ⟨246404, by rfl⟩ : syracuseStep 5256629 = 492809) (by norm_num)
theorem B1971641 : Blo 1557476 1971641 := bbase (se 2 (by rfl) ⟨739365, by rfl⟩ : syracuseStep 1971641 = 1478731) (by norm_num)
theorem B16848341 : Blo 1557476 16848341 := bbase (se 7 (by rfl) ⟨197441, by rfl⟩ : syracuseStep 16848341 = 394883) (by norm_num)
theorem B8000981 : Blo 1557476 8000981 := bbase (se 7 (by rfl) ⟨93761, by rfl⟩ : syracuseStep 8000981 = 187523) (by norm_num)
theorem B1971697 : Blo 1557476 1971697 := bbase (se 2 (by rfl) ⟨739386, by rfl⟩ : syracuseStep 1971697 = 1478773) (by norm_num)
theorem B1971793 : Blo 1557476 1971793 := bbase (se 2 (by rfl) ⟨739422, by rfl⟩ : syracuseStep 1971793 = 1478845) (by norm_num)
theorem B4437605 : Blo 1557476 4437605 := bbase (se 4 (by rfl) ⟨416025, by rfl⟩ : syracuseStep 4437605 = 832051) (by norm_num)
theorem B7108229 : Blo 1557476 7108229 := bbase (se 4 (by rfl) ⟨666396, by rfl⟩ : syracuseStep 7108229 = 1332793) (by norm_num)
theorem B3946117 : Blo 1557476 3946117 := bbase (se 4 (by rfl) ⟨369948, by rfl⟩ : syracuseStep 3946117 = 739897) (by norm_num)
theorem B2217613 : Blo 1557476 2217613 := bbase (se 3 (by rfl) ⟨415802, by rfl⟩ : syracuseStep 2217613 = 831605) (by norm_num)
theorem B2217709 : Blo 1557476 2217709 := bbase (se 3 (by rfl) ⟨415820, by rfl⟩ : syracuseStep 2217709 = 831641) (by norm_num)
theorem B3946229 : Blo 1557476 3946229 := bbase (se 5 (by rfl) ⟨184979, by rfl⟩ : syracuseStep 3946229 = 369959) (by norm_num)
theorem B1971965 : Blo 1557476 1971965 := bbase (se 3 (by rfl) ⟨369743, by rfl⟩ : syracuseStep 1971965 = 739487) (by norm_num)
theorem B7493381 : Blo 1557476 7493381 := bbase (se 4 (by rfl) ⟨702504, by rfl⟩ : syracuseStep 7493381 = 1405009) (by norm_num)
theorem B7886645 : Blo 1557476 7886645 := bbase (se 5 (by rfl) ⟨369686, by rfl⟩ : syracuseStep 7886645 = 739373) (by norm_num)
theorem B1972021 : Blo 1557476 1972021 := bbase (se 5 (by rfl) ⟨92438, by rfl⟩ : syracuseStep 1972021 = 184877) (by norm_num)
theorem B4052813 : Blo 1557476 4052813 := bbase (se 3 (by rfl) ⟨759902, by rfl⟩ : syracuseStep 4052813 = 1519805) (by norm_num)
theorem B5257061 : Blo 1557476 5257061 := bbase (se 4 (by rfl) ⟨492849, by rfl⟩ : syracuseStep 5257061 = 985699) (by norm_num)
theorem B1972117 : Blo 1557476 1972117 := bbase (se 6 (by rfl) ⟨46221, by rfl⟩ : syracuseStep 1972117 = 92443) (by norm_num)
theorem B3946421 : Blo 1557476 3946421 := bbase (se 5 (by rfl) ⟨184988, by rfl⟩ : syracuseStep 3946421 = 369977) (by norm_num)
theorem B7493573 : Blo 1557476 7493573 := bbase (se 4 (by rfl) ⟨702522, by rfl⟩ : syracuseStep 7493573 = 1405045) (by norm_num)
theorem B3651533 : Blo 1557476 3651533 := bbase (se 3 (by rfl) ⟨684662, by rfl⟩ : syracuseStep 3651533 = 1369325) (by norm_num)
theorem B1972289 : Blo 1557476 1972289 := bbase (se 2 (by rfl) ⟨739608, by rfl⟩ : syracuseStep 1972289 = 1479217) (by norm_num)
theorem B1972345 : Blo 1557476 1972345 := bbase (se 2 (by rfl) ⟨739629, by rfl⟩ : syracuseStep 1972345 = 1479259) (by norm_num)
theorem B1710217 : Blo 1557476 1710217 := bbase (se 2 (by rfl) ⟨641331, by rfl⟩ : syracuseStep 1710217 = 1282663) (by norm_num)
theorem B1579225 : Blo 1557476 1579225 := bbase (se 2 (by rfl) ⟨592209, by rfl⟩ : syracuseStep 1579225 = 1184419) (by norm_num)
theorem B1972441 : Blo 1557476 1972441 := bbase (se 2 (by rfl) ⟨739665, by rfl⟩ : syracuseStep 1972441 = 1479331) (by norm_num)
theorem B2218205 : Blo 1557476 2218205 := bbase (se 3 (by rfl) ⟨415913, by rfl⟩ : syracuseStep 2218205 = 831827) (by norm_num)
theorem B2808029 : Blo 1557476 2808029 := bbase (se 3 (by rfl) ⟨526505, by rfl⟩ : syracuseStep 2808029 = 1053011) (by norm_num)
theorem B3504365 : Blo 1557476 3504365 := bbase (se 3 (by rfl) ⟨657068, by rfl⟩ : syracuseStep 3504365 = 1314137) (by norm_num)
theorem B3946765 : Blo 1557476 3946765 := bbase (se 3 (by rfl) ⟨740018, by rfl⟩ : syracuseStep 3946765 = 1480037) (by norm_num)
theorem B5257493 : Blo 1557476 5257493 := bbase (se 6 (by rfl) ⟨123222, by rfl⟩ : syracuseStep 5257493 = 246445) (by norm_num)
theorem B11229461 : Blo 1557476 11229461 := bbase (se 6 (by rfl) ⟨263190, by rfl⟩ : syracuseStep 11229461 = 526381) (by norm_num)
theorem B5921045 : Blo 1557476 5921045 := bbase (se 6 (by rfl) ⟨138774, by rfl⟩ : syracuseStep 5921045 = 277549) (by norm_num)
theorem B3504437 : Blo 1557476 3504437 := bbase (se 5 (by rfl) ⟨164270, by rfl⟩ : syracuseStep 3504437 = 328541) (by norm_num)
theorem B3504509 : Blo 1557476 3504509 := bbase (se 3 (by rfl) ⟨657095, by rfl⟩ : syracuseStep 3504509 = 1314191) (by norm_num)
theorem B3946877 : Blo 1557476 3946877 := bbase (se 3 (by rfl) ⟨740039, by rfl⟩ : syracuseStep 3946877 = 1480079) (by norm_num)
theorem B1972613 : Blo 1557476 1972613 := bbase (se 4 (by rfl) ⟨184932, by rfl⟩ : syracuseStep 1972613 = 369865) (by norm_num)
theorem B1972669 : Blo 1557476 1972669 := bbase (se 3 (by rfl) ⟨369875, by rfl⟩ : syracuseStep 1972669 = 739751) (by norm_num)
theorem B3504581 : Blo 1557476 3504581 := bbase (se 4 (by rfl) ⟨328554, by rfl⟩ : syracuseStep 3504581 = 657109) (by norm_num)
theorem B3504653 : Blo 1557476 3504653 := bbase (se 3 (by rfl) ⟨657122, by rfl⟩ : syracuseStep 3504653 = 1314245) (by norm_num)
theorem B1972765 : Blo 1557476 1972765 := bbase (se 3 (by rfl) ⟨369893, by rfl⟩ : syracuseStep 1972765 = 739787) (by norm_num)
theorem B3947069 : Blo 1557476 3947069 := bbase (se 3 (by rfl) ⟨740075, by rfl⟩ : syracuseStep 3947069 = 1480151) (by norm_num)
theorem B4438597 : Blo 1557476 4438597 := bbase (se 4 (by rfl) ⟨416118, by rfl⟩ : syracuseStep 4438597 = 832237) (by norm_num)
theorem B3504725 : Blo 1557476 3504725 := bbase (se 8 (by rfl) ⟨20535, by rfl⟩ : syracuseStep 3504725 = 41071) (by norm_num)
theorem B1776277 : Blo 1557476 1776277 := bbase (se 6 (by rfl) ⟨41631, by rfl⟩ : syracuseStep 1776277 = 83263) (by norm_num)
theorem B3504797 : Blo 1557476 3504797 := bbase (se 3 (by rfl) ⟨657149, by rfl⟩ : syracuseStep 3504797 = 1314299) (by norm_num)
theorem B2497205 : Blo 1557476 2497205 := bbase (se 5 (by rfl) ⟨117056, by rfl⟩ : syracuseStep 2497205 = 234113) (by norm_num)
theorem B5257925 : Blo 1557476 5257925 := bbase (se 4 (by rfl) ⟨492930, by rfl⟩ : syracuseStep 5257925 = 985861) (by norm_num)
theorem B1972937 : Blo 1557476 1972937 := bbase (se 2 (by rfl) ⟨739851, by rfl⟩ : syracuseStep 1972937 = 1479703) (by norm_num)
theorem B2628301 : Blo 1557476 2628301 := bbase (se 3 (by rfl) ⟨492806, by rfl⟩ : syracuseStep 2628301 = 985613) (by norm_num)
theorem B3504869 : Blo 1557476 3504869 := bbase (se 4 (by rfl) ⟨328581, by rfl⟩ : syracuseStep 3504869 = 657163) (by norm_num)
theorem B3742453 : Blo 1557476 3742453 := bbase (se 5 (by rfl) ⟨175427, by rfl⟩ : syracuseStep 3742453 = 350855) (by norm_num)
theorem B1972993 : Blo 1557476 1972993 := bbase (se 2 (by rfl) ⟨739872, by rfl⟩ : syracuseStep 1972993 = 1479745) (by norm_num)
theorem B2218757 : Blo 1557476 2218757 := bbase (se 4 (by rfl) ⟨208008, by rfl⟩ : syracuseStep 2218757 = 416017) (by norm_num)
theorem B2628389 : Blo 1557476 2628389 := bbase (se 4 (by rfl) ⟨246411, by rfl⟩ : syracuseStep 2628389 = 492823) (by norm_num)
theorem B3504941 : Blo 1557476 3504941 := bbase (se 3 (by rfl) ⟨657176, by rfl⟩ : syracuseStep 3504941 = 1314353) (by norm_num)
theorem B4053821 : Blo 1557476 4053821 := bbase (se 3 (by rfl) ⟨760091, by rfl⟩ : syracuseStep 4053821 = 1520183) (by norm_num)
theorem B1973089 : Blo 1557476 1973089 := bbase (se 2 (by rfl) ⟨739908, by rfl⟩ : syracuseStep 1973089 = 1479817) (by norm_num)
theorem B2808685 : Blo 1557476 2808685 := bbase (se 3 (by rfl) ⟨526628, by rfl⟩ : syracuseStep 2808685 = 1053257) (by norm_num)
theorem B3505013 : Blo 1557476 3505013 := bbase (se 5 (by rfl) ⟨164297, by rfl⟩ : syracuseStep 3505013 = 328595) (by norm_num)
theorem B2497429 : Blo 1557476 2497429 := bbase (se 6 (by rfl) ⟨58533, by rfl⟩ : syracuseStep 2497429 = 117067) (by norm_num)
theorem B3947413 : Blo 1557476 3947413 := bbase (se 6 (by rfl) ⟨92517, by rfl⟩ : syracuseStep 3947413 = 185035) (by norm_num)
theorem B2628517 : Blo 1557476 2628517 := bbase (se 4 (by rfl) ⟨246423, by rfl⟩ : syracuseStep 2628517 = 492847) (by norm_num)
theorem B2808749 : Blo 1557476 2808749 := bbase (se 3 (by rfl) ⟨526640, by rfl⟩ : syracuseStep 2808749 = 1053281) (by norm_num)
theorem B3505085 : Blo 1557476 3505085 := bbase (se 3 (by rfl) ⟨657203, by rfl⟩ : syracuseStep 3505085 = 1314407) (by norm_num)
theorem B5913557 : Blo 1557476 5913557 := bbase (se 7 (by rfl) ⟨69299, by rfl⟩ : syracuseStep 5913557 = 138599) (by norm_num)
theorem B3161045 : Blo 1557476 3161045 := bbase (se 7 (by rfl) ⟨37043, by rfl⟩ : syracuseStep 3161045 = 74087) (by norm_num)
theorem B2628605 : Blo 1557476 2628605 := bbase (se 3 (by rfl) ⟨492863, by rfl⟩ : syracuseStep 2628605 = 985727) (by norm_num)
theorem B3505157 : Blo 1557476 3505157 := bbase (se 4 (by rfl) ⟨328608, by rfl⟩ : syracuseStep 3505157 = 657217) (by norm_num)
theorem B1973261 : Blo 1557476 1973261 := bbase (se 3 (by rfl) ⟨369986, by rfl⟩ : syracuseStep 1973261 = 739973) (by norm_num)
theorem B22461461 : Blo 1557476 22461461 := bbase (se 6 (by rfl) ⟨526440, by rfl⟩ : syracuseStep 22461461 = 1052881) (by norm_num)
theorem B3742789 : Blo 1557476 3742789 := bbase (se 4 (by rfl) ⟨350886, by rfl⟩ : syracuseStep 3742789 = 701773) (by norm_num)
theorem B7887941 : Blo 1557476 7887941 := bbase (se 4 (by rfl) ⟨739494, by rfl⟩ : syracuseStep 7887941 = 1478989) (by norm_num)
theorem B1973317 : Blo 1557476 1973317 := bbase (se 4 (by rfl) ⟨184998, by rfl⟩ : syracuseStep 1973317 = 369997) (by norm_num)
theorem B3505229 : Blo 1557476 3505229 := bbase (se 3 (by rfl) ⟨657230, by rfl⟩ : syracuseStep 3505229 = 1314461) (by norm_num)
theorem B2530381 : Blo 1557476 2530381 := bbase (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) (by norm_num)
theorem B1752169 : Blo 1557476 1752169 := bbase (se 2 (by rfl) ⟨657063, by rfl⟩ : syracuseStep 1752169 = 1314127) (by norm_num)
theorem B5258357 : Blo 1557476 5258357 := bbase (se 5 (by rfl) ⟨246485, by rfl⟩ : syracuseStep 5258357 = 492971) (by norm_num)
theorem B2628733 : Blo 1557476 2628733 := bbase (se 3 (by rfl) ⟨492887, by rfl⟩ : syracuseStep 2628733 = 985775) (by norm_num)
theorem B1752205 : Blo 1557476 1752205 := bbase (se 3 (by rfl) ⟨328538, by rfl⟩ : syracuseStep 1752205 = 657077) (by norm_num)
theorem B3505301 : Blo 1557476 3505301 := bbase (se 6 (by rfl) ⟨82155, by rfl⟩ : syracuseStep 3505301 = 164311) (by norm_num)
theorem B1973413 : Blo 1557476 1973413 := bbase (se 4 (by rfl) ⟨185007, by rfl⟩ : syracuseStep 1973413 = 370015) (by norm_num)
theorem B1752241 : Blo 1557476 1752241 := bbase (se 2 (by rfl) ⟨657090, by rfl⟩ : syracuseStep 1752241 = 1314181) (by norm_num)
theorem B1752277 : Blo 1557476 1752277 := bbase (se 7 (by rfl) ⟨20534, by rfl⟩ : syracuseStep 1752277 = 41069) (by norm_num)
theorem B2628821 : Blo 1557476 2628821 := bbase (se 7 (by rfl) ⟨30806, by rfl⟩ : syracuseStep 2628821 = 61613) (by norm_num)
theorem B3505373 : Blo 1557476 3505373 := bbase (se 3 (by rfl) ⟨657257, by rfl⟩ : syracuseStep 3505373 = 1314515) (by norm_num)
theorem B3554525 : Blo 1557476 3554525 := bbase (se 3 (by rfl) ⟨666473, by rfl⟩ : syracuseStep 3554525 = 1332947) (by norm_num)
theorem B1752313 : Blo 1557476 1752313 := bbase (se 2 (by rfl) ⟨657117, by rfl⟩ : syracuseStep 1752313 = 1314235) (by norm_num)
theorem B8879381 : Blo 1557476 8879381 := bbase (se 6 (by rfl) ⟨208110, by rfl⟩ : syracuseStep 8879381 = 416221) (by norm_num)
theorem B1752349 : Blo 1557476 1752349 := bbase (se 3 (by rfl) ⟨328565, by rfl⟩ : syracuseStep 1752349 = 657131) (by norm_num)
theorem B3505445 : Blo 1557476 3505445 := bbase (se 4 (by rfl) ⟨328635, by rfl⟩ : syracuseStep 3505445 = 657271) (by norm_num)
theorem B1752385 : Blo 1557476 1752385 := bbase (se 2 (by rfl) ⟨657144, by rfl⟩ : syracuseStep 1752385 = 1314289) (by norm_num)
theorem B1973585 : Blo 1557476 1973585 := bbase (se 2 (by rfl) ⟨740094, by rfl⟩ : syracuseStep 1973585 = 1480189) (by norm_num)
theorem B2628949 : Blo 1557476 2628949 := bbase (se 11 (by rfl) ⟨1925, by rfl⟩ : syracuseStep 2628949 = 3851) (by norm_num)
theorem B1752421 : Blo 1557476 1752421 := bbase (se 4 (by rfl) ⟨164289, by rfl⟩ : syracuseStep 1752421 = 328579) (by norm_num)
theorem B3505517 : Blo 1557476 3505517 := bbase (se 3 (by rfl) ⟨657284, by rfl⟩ : syracuseStep 3505517 = 1314569) (by norm_num)
theorem B1752457 : Blo 1557476 1752457 := bbase (se 2 (by rfl) ⟨657171, by rfl⟩ : syracuseStep 1752457 = 1314343) (by norm_num)
theorem B1973641 : Blo 1557476 1973641 := bbase (se 2 (by rfl) ⟨740115, by rfl⟩ : syracuseStep 1973641 = 1480231) (by norm_num)
theorem B1752493 : Blo 1557476 1752493 := bbase (se 3 (by rfl) ⟨328592, by rfl⟩ : syracuseStep 1752493 = 657185) (by norm_num)
theorem B2629037 : Blo 1557476 2629037 := bbase (se 3 (by rfl) ⟨492944, by rfl⟩ : syracuseStep 2629037 = 985889) (by norm_num)
theorem B3505589 : Blo 1557476 3505589 := bbase (se 5 (by rfl) ⟨164324, by rfl⟩ : syracuseStep 3505589 = 328649) (by norm_num)
theorem B1752529 : Blo 1557476 1752529 := bbase (se 2 (by rfl) ⟨657198, by rfl⟩ : syracuseStep 1752529 = 1314397) (by norm_num)
theorem B1752565 : Blo 1557476 1752565 := bbase (se 5 (by rfl) ⟨82151, by rfl⟩ : syracuseStep 1752565 = 164303) (by norm_num)
theorem B2219509 : Blo 1557476 2219509 := bbase (se 5 (by rfl) ⟨104039, by rfl⟩ : syracuseStep 2219509 = 208079) (by norm_num)
theorem B3505661 : Blo 1557476 3505661 := bbase (se 3 (by rfl) ⟨657311, by rfl⟩ : syracuseStep 3505661 = 1314623) (by norm_num)
theorem B8420885 : Blo 1557476 8420885 := bbase (se 6 (by rfl) ⟨197364, by rfl⟩ : syracuseStep 8420885 = 394729) (by norm_num)
theorem B1752601 : Blo 1557476 1752601 := bbase (se 2 (by rfl) ⟨657225, by rfl⟩ : syracuseStep 1752601 = 1314451) (by norm_num)
theorem B5258789 : Blo 1557476 5258789 := bbase (se 4 (by rfl) ⟨493011, by rfl⟩ : syracuseStep 5258789 = 986023) (by norm_num)
theorem B6659621 : Blo 1557476 6659621 := bbase (se 4 (by rfl) ⟨624339, by rfl⟩ : syracuseStep 6659621 = 1248679) (by norm_num)
theorem B2629165 : Blo 1557476 2629165 := bbase (se 3 (by rfl) ⟨492968, by rfl⟩ : syracuseStep 2629165 = 985937) (by norm_num)
theorem B1752637 : Blo 1557476 1752637 := bbase (se 3 (by rfl) ⟨328619, by rfl⟩ : syracuseStep 1752637 = 657239) (by norm_num)
theorem B3505733 : Blo 1557476 3505733 := bbase (se 4 (by rfl) ⟨328662, by rfl⟩ : syracuseStep 3505733 = 657325) (by norm_num)
theorem B1752673 : Blo 1557476 1752673 := bbase (se 2 (by rfl) ⟨657252, by rfl⟩ : syracuseStep 1752673 = 1314505) (by norm_num)
theorem B1752709 : Blo 1557476 1752709 := bbase (se 4 (by rfl) ⟨164316, by rfl⟩ : syracuseStep 1752709 = 328633) (by norm_num)
theorem B2629253 : Blo 1557476 2629253 := bbase (se 4 (by rfl) ⟨246492, by rfl⟩ : syracuseStep 2629253 = 492985) (by norm_num)
theorem B3505805 : Blo 1557476 3505805 := bbase (se 3 (by rfl) ⟨657338, by rfl⟩ : syracuseStep 3505805 = 1314677) (by norm_num)
theorem B4439701 : Blo 1557476 4439701 := bbase (se 6 (by rfl) ⟨104055, by rfl⟩ : syracuseStep 4439701 = 208111) (by norm_num)
theorem B1752745 : Blo 1557476 1752745 := bbase (se 2 (by rfl) ⟨657279, by rfl⟩ : syracuseStep 1752745 = 1314559) (by norm_num)
theorem B3743405 : Blo 1557476 3743405 := bbase (se 3 (by rfl) ⟨701888, by rfl⟩ : syracuseStep 3743405 = 1403777) (by norm_num)
theorem B1752781 : Blo 1557476 1752781 := bbase (se 3 (by rfl) ⟨328646, by rfl⟩ : syracuseStep 1752781 = 657293) (by norm_num)
theorem B3505877 : Blo 1557476 3505877 := bbase (se 7 (by rfl) ⟨41084, by rfl⟩ : syracuseStep 3505877 = 82169) (by norm_num)
theorem B1752817 : Blo 1557476 1752817 := bbase (se 2 (by rfl) ⟨657306, by rfl⟩ : syracuseStep 1752817 = 1314613) (by norm_num)
theorem B2629381 : Blo 1557476 2629381 := bbase (se 4 (by rfl) ⟨246504, by rfl⟩ : syracuseStep 2629381 = 493009) (by norm_num)
theorem B1752853 : Blo 1557476 1752853 := bbase (se 6 (by rfl) ⟨41082, by rfl⟩ : syracuseStep 1752853 = 82165) (by norm_num)
theorem B3505949 : Blo 1557476 3505949 := bbase (se 3 (by rfl) ⟨657365, by rfl⟩ : syracuseStep 3505949 = 1314731) (by norm_num)
theorem B1752889 : Blo 1557476 1752889 := bbase (se 2 (by rfl) ⟨657333, by rfl⟩ : syracuseStep 1752889 = 1314667) (by norm_num)
theorem B1998685 : Blo 1557476 1998685 := bbase (se 3 (by rfl) ⟨374753, by rfl⟩ : syracuseStep 1998685 = 749507) (by norm_num)
theorem B1752925 : Blo 1557476 1752925 := bbase (se 3 (by rfl) ⟨328673, by rfl⟩ : syracuseStep 1752925 = 657347) (by norm_num)
theorem B2629469 : Blo 1557476 2629469 := bbase (se 3 (by rfl) ⟨493025, by rfl⟩ : syracuseStep 2629469 = 986051) (by norm_num)
theorem B3506021 : Blo 1557476 3506021 := bbase (se 4 (by rfl) ⟨328689, by rfl⟩ : syracuseStep 3506021 = 657379) (by norm_num)
theorem B1752961 : Blo 1557476 1752961 := bbase (se 2 (by rfl) ⟨657360, by rfl⟩ : syracuseStep 1752961 = 1314721) (by norm_num)
theorem B1752997 : Blo 1557476 1752997 := bbase (se 4 (by rfl) ⟨164343, by rfl⟩ : syracuseStep 1752997 = 328687) (by norm_num)
theorem B3506093 : Blo 1557476 3506093 := bbase (se 3 (by rfl) ⟨657392, by rfl⟩ : syracuseStep 3506093 = 1314785) (by norm_num)
theorem B1753033 : Blo 1557476 1753033 := bbase (se 2 (by rfl) ⟨657387, by rfl⟩ : syracuseStep 1753033 = 1314775) (by norm_num)
theorem B5259221 : Blo 1557476 5259221 := bbase (se 7 (by rfl) ⟨61631, by rfl⟩ : syracuseStep 5259221 = 123263) (by norm_num)
theorem B2629597 : Blo 1557476 2629597 := bbase (se 3 (by rfl) ⟨493049, by rfl⟩ : syracuseStep 2629597 = 986099) (by norm_num)
theorem B1753069 : Blo 1557476 1753069 := bbase (se 3 (by rfl) ⟨328700, by rfl⟩ : syracuseStep 1753069 = 657401) (by norm_num)
theorem B3506165 : Blo 1557476 3506165 := bbase (se 5 (by rfl) ⟨164351, by rfl⟩ : syracuseStep 3506165 = 328703) (by norm_num)
theorem B2105347 : Blo 1557476 2105347 := bstep (se 1 (by rfl) ⟨1579010, by rfl⟩ : syracuseStep 2105347 = 3158021) B3158021
theorem B2629651 : Blo 1557476 2629651 := bstep (se 1 (by rfl) ⟨1972238, by rfl⟩ : syracuseStep 2629651 = 3944477) B3944477
theorem B1753123 : Blo 1557476 1753123 := bstep (se 1 (by rfl) ⟨1314842, by rfl⟩ : syracuseStep 1753123 = 2629685) B2629685
theorem B2629793 : Blo 1557476 2629793 := bstep (se 2 (by rfl) ⟨986172, by rfl⟩ : syracuseStep 2629793 = 1972345) B1972345
theorem B5259437 : Blo 1557476 5259437 := bstep (se 3 (by rfl) ⟨986144, by rfl⟩ : syracuseStep 5259437 = 1972289) B1972289
theorem B1753267 : Blo 1557476 1753267 := bstep (se 1 (by rfl) ⟨1314950, by rfl⟩ : syracuseStep 1753267 = 2629901) B2629901
theorem B5259491 : Blo 1557476 5259491 := bstep (se 1 (by rfl) ⟨3944618, by rfl⟩ : syracuseStep 5259491 = 7889237) B7889237
theorem B31998179 : Blo 1557476 31998179 := bstep (se 1 (by rfl) ⟨23998634, by rfl⟩ : syracuseStep 31998179 = 47997269) B47997269
theorem B3506417 : Blo 1557476 3506417 := bstep (se 2 (by rfl) ⟨1314906, by rfl⟩ : syracuseStep 3506417 = 2629813) B2629813
theorem B3506435 : Blo 1557476 3506435 := bstep (se 1 (by rfl) ⟨2629826, by rfl⟩ : syracuseStep 3506435 = 5259653) B5259653
theorem B2105633 : Blo 1557476 2105633 := bstep (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) B1579225
theorem B2629921 : Blo 1557476 2629921 := bstep (se 2 (by rfl) ⟨986220, by rfl⟩ : syracuseStep 2629921 = 1972441) B1972441
theorem B2629955 : Blo 1557476 2629955 := bstep (se 1 (by rfl) ⟨1972466, by rfl⟩ : syracuseStep 2629955 = 3944933) B3944933
theorem B1753411 : Blo 1557476 1753411 := bstep (se 1 (by rfl) ⟨1315058, by rfl⟩ : syracuseStep 1753411 = 2630117) B2630117
theorem B5620067 : Blo 1557476 5620067 := bstep (se 1 (by rfl) ⟨4215050, by rfl⟩ : syracuseStep 5620067 = 8430101) B8430101
theorem B2630083 : Blo 1557476 2630083 := bstep (se 1 (by rfl) ⟨1972562, by rfl⟩ : syracuseStep 2630083 = 3945125) B3945125
theorem B1753555 : Blo 1557476 1753555 := bstep (se 1 (by rfl) ⟨1315166, by rfl⟩ : syracuseStep 1753555 = 2630333) B2630333
theorem B5259761 : Blo 1557476 5259761 := bstep (se 2 (by rfl) ⟨1972410, by rfl⟩ : syracuseStep 5259761 = 3944821) B3944821
theorem B3039761 : Blo 1557476 3039761 := bstep (se 2 (by rfl) ⟨1139910, by rfl⟩ : syracuseStep 3039761 = 2279821) B2279821
theorem B3506705 : Blo 1557476 3506705 := bstep (se 2 (by rfl) ⟨1315014, by rfl⟩ : syracuseStep 3506705 = 2630029) B2630029
theorem B3506723 : Blo 1557476 3506723 := bstep (se 1 (by rfl) ⟨2630042, by rfl⟩ : syracuseStep 3506723 = 5260085) B5260085
theorem B5915213 : Blo 1557476 5915213 := bstep (se 3 (by rfl) ⟨1109102, by rfl⟩ : syracuseStep 5915213 = 2218205) B2218205
theorem B2630225 : Blo 1557476 2630225 := bstep (se 2 (by rfl) ⟨986334, by rfl⟩ : syracuseStep 2630225 = 1972669) B1972669
theorem B1753699 : Blo 1557476 1753699 := bstep (se 1 (by rfl) ⟨1315274, by rfl⟩ : syracuseStep 1753699 = 2630549) B2630549
theorem B11231885 : Blo 1557476 11231885 := bstep (se 3 (by rfl) ⟨2105978, by rfl⟩ : syracuseStep 11231885 = 4211957) B4211957
theorem B7201457 : Blo 1557476 7201457 := bstep (se 2 (by rfl) ⟨2700546, by rfl⟩ : syracuseStep 7201457 = 5401093) B5401093
theorem B25608901 : Blo 1557476 25608901 := bstep (se 4 (by rfl) ⟨2400834, by rfl⟩ : syracuseStep 25608901 = 4801669) B4801669
theorem B2630353 : Blo 1557476 2630353 := bstep (se 2 (by rfl) ⟨986382, by rfl⟩ : syracuseStep 2630353 = 1972765) B1972765
theorem B2630387 : Blo 1557476 2630387 := bstep (se 1 (by rfl) ⟨1972790, by rfl⟩ : syracuseStep 2630387 = 3945581) B3945581
theorem B1753843 : Blo 1557476 1753843 := bstep (se 1 (by rfl) ⟨1315382, by rfl⟩ : syracuseStep 1753843 = 2630765) B2630765
theorem B2958115 : Blo 1557476 2958115 := bstep (se 1 (by rfl) ⟨2218586, by rfl⟩ : syracuseStep 2958115 = 4437173) B4437173
theorem B3506993 : Blo 1557476 3506993 := bstep (se 2 (by rfl) ⟨1315122, by rfl⟩ : syracuseStep 3506993 = 2630245) B2630245
theorem B3507011 : Blo 1557476 3507011 := bstep (se 1 (by rfl) ⟨2630258, by rfl⟩ : syracuseStep 3507011 = 5260517) B5260517
theorem B307635029 : Blo 1557476 307635029 := bstep (se 9 (by rfl) ⟨901274, by rfl⟩ : syracuseStep 307635029 = 1802549) B1802549
theorem B2368369 : Blo 1557476 2368369 := bstep (se 2 (by rfl) ⟨888138, by rfl⟩ : syracuseStep 2368369 = 1776277) B1776277
theorem B1663859 : Blo 1557476 1663859 := bstep (se 1 (by rfl) ⟨1247894, by rfl⟩ : syracuseStep 1663859 = 2495789) B2495789
theorem B2630515 : Blo 1557476 2630515 := bstep (se 1 (by rfl) ⟨1972886, by rfl⟩ : syracuseStep 2630515 = 3945773) B3945773
theorem B1753987 : Blo 1557476 1753987 := bstep (se 1 (by rfl) ⟨1315490, by rfl⟩ : syracuseStep 1753987 = 2630981) B2630981
theorem B2958275 : Blo 1557476 2958275 := bstep (se 1 (by rfl) ⟨2218706, by rfl⟩ : syracuseStep 2958275 = 4437413) B4437413
theorem B11232227 : Blo 1557476 11232227 := bstep (se 1 (by rfl) ⟨8424170, by rfl⟩ : syracuseStep 11232227 = 16848341) B16848341
theorem B5333987 : Blo 1557476 5333987 := bstep (se 1 (by rfl) ⟨4000490, by rfl⟩ : syracuseStep 5333987 = 8000981) B8000981
theorem B4989937 : Blo 1557476 4989937 := bstep (se 2 (by rfl) ⟨1871226, by rfl⟩ : syracuseStep 4989937 = 3742453) B3742453
theorem B1557491 : Blo 1557476 1557491 := bstep (se 1 (by rfl) ⟨1168118, by rfl⟩ : syracuseStep 1557491 = 2336237) B2336237
theorem B2630657 : Blo 1557476 2630657 := bstep (se 2 (by rfl) ⟨986496, by rfl⟩ : syracuseStep 2630657 = 1972993) B1972993
theorem B1557507 : Blo 1557476 1557507 := bstep (se 1 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 1557507 = 2336261) B2336261
theorem B5260301 : Blo 1557476 5260301 := bstep (se 3 (by rfl) ⟨986306, by rfl⟩ : syracuseStep 5260301 = 1972613) B1972613
theorem B1557523 : Blo 1557476 1557523 := bstep (se 1 (by rfl) ⟨1168142, by rfl⟩ : syracuseStep 1557523 = 2336285) B2336285
theorem B1754131 : Blo 1557476 1754131 := bstep (se 1 (by rfl) ⟨1315598, by rfl⟩ : syracuseStep 1754131 = 2631197) B2631197
theorem B1557539 : Blo 1557476 1557539 := bstep (se 1 (by rfl) ⟨1168154, by rfl⟩ : syracuseStep 1557539 = 2336309) B2336309
theorem B1557555 : Blo 1557476 1557555 := bstep (se 1 (by rfl) ⟨1168166, by rfl⟩ : syracuseStep 1557555 = 2336333) B2336333
theorem B1557571 : Blo 1557476 1557571 := bstep (se 1 (by rfl) ⟨1168178, by rfl⟩ : syracuseStep 1557571 = 2336357) B2336357
theorem B5260355 : Blo 1557476 5260355 := bstep (se 1 (by rfl) ⟨3945266, by rfl⟩ : syracuseStep 5260355 = 7890533) B7890533
theorem B12330053 : Blo 1557476 12330053 := bstep (se 4 (by rfl) ⟨1155942, by rfl⟩ : syracuseStep 12330053 = 2311885) B2311885
theorem B3507281 : Blo 1557476 3507281 := bstep (se 2 (by rfl) ⟨1315230, by rfl⟩ : syracuseStep 3507281 = 2630461) B2630461
theorem B1557587 : Blo 1557476 1557587 := bstep (se 1 (by rfl) ⟨1168190, by rfl⟩ : syracuseStep 1557587 = 2336381) B2336381
theorem B1557603 : Blo 1557476 1557603 := bstep (se 1 (by rfl) ⟨1168202, by rfl⟩ : syracuseStep 1557603 = 2336405) B2336405
theorem B3507299 : Blo 1557476 3507299 := bstep (se 1 (by rfl) ⟨2630474, by rfl⟩ : syracuseStep 3507299 = 5260949) B5260949
theorem B1557619 : Blo 1557476 1557619 := bstep (se 1 (by rfl) ⟨1168214, by rfl⟩ : syracuseStep 1557619 = 2336429) B2336429
theorem B2630785 : Blo 1557476 2630785 := bstep (se 2 (by rfl) ⟨986544, by rfl⟩ : syracuseStep 2630785 = 1973089) B1973089
theorem B1557635 : Blo 1557476 1557635 := bstep (se 1 (by rfl) ⟨1168226, by rfl⟩ : syracuseStep 1557635 = 2336453) B2336453
theorem B1557651 : Blo 1557476 1557651 := bstep (se 1 (by rfl) ⟨1168238, by rfl⟩ : syracuseStep 1557651 = 2336477) B2336477
theorem B1557667 : Blo 1557476 1557667 := bstep (se 1 (by rfl) ⟨1168250, by rfl⟩ : syracuseStep 1557667 = 2336501) B2336501
theorem B2630819 : Blo 1557476 2630819 := bstep (se 1 (by rfl) ⟨1973114, by rfl⟩ : syracuseStep 2630819 = 3946229) B3946229
theorem B1754275 : Blo 1557476 1754275 := bstep (se 1 (by rfl) ⟨1315706, by rfl⟩ : syracuseStep 1754275 = 2631413) B2631413
theorem B1557683 : Blo 1557476 1557683 := bstep (se 1 (by rfl) ⟨1168262, by rfl⟩ : syracuseStep 1557683 = 2336525) B2336525
theorem B1557699 : Blo 1557476 1557699 := bstep (se 1 (by rfl) ⟨1168274, by rfl⟩ : syracuseStep 1557699 = 2336549) B2336549
theorem B1557715 : Blo 1557476 1557715 := bstep (se 1 (by rfl) ⟨1168286, by rfl⟩ : syracuseStep 1557715 = 2336573) B2336573
theorem B1557731 : Blo 1557476 1557731 := bstep (se 1 (by rfl) ⟨1168298, by rfl⟩ : syracuseStep 1557731 = 2336597) B2336597
theorem B1557747 : Blo 1557476 1557747 := bstep (se 1 (by rfl) ⟨1168310, by rfl⟩ : syracuseStep 1557747 = 2336621) B2336621
theorem B1557763 : Blo 1557476 1557763 := bstep (se 1 (by rfl) ⟨1168322, by rfl⟩ : syracuseStep 1557763 = 2336645) B2336645
theorem B1557779 : Blo 1557476 1557779 := bstep (se 1 (by rfl) ⟨1168334, by rfl⟩ : syracuseStep 1557779 = 2336669) B2336669
theorem B1557795 : Blo 1557476 1557795 := bstep (se 1 (by rfl) ⟨1168346, by rfl⟩ : syracuseStep 1557795 = 2336693) B2336693
theorem B2630947 : Blo 1557476 2630947 := bstep (se 1 (by rfl) ⟨1973210, by rfl⟩ : syracuseStep 2630947 = 3946421) B3946421
theorem B1557811 : Blo 1557476 1557811 := bstep (se 1 (by rfl) ⟨1168358, by rfl⟩ : syracuseStep 1557811 = 2336717) B2336717
theorem B2434355 : Blo 1557476 2434355 := bstep (se 1 (by rfl) ⟨1825766, by rfl⟩ : syracuseStep 2434355 = 3651533) B3651533
theorem B1557827 : Blo 1557476 1557827 := bstep (se 1 (by rfl) ⟨1168370, by rfl⟩ : syracuseStep 1557827 = 2336741) B2336741
theorem B5260625 : Blo 1557476 5260625 := bstep (se 2 (by rfl) ⟨1972734, by rfl⟩ : syracuseStep 5260625 = 3945469) B3945469
theorem B1557843 : Blo 1557476 1557843 := bstep (se 1 (by rfl) ⟨1168382, by rfl⟩ : syracuseStep 1557843 = 2336765) B2336765
theorem B1557859 : Blo 1557476 1557859 := bstep (se 1 (by rfl) ⟨1168394, by rfl⟩ : syracuseStep 1557859 = 2336789) B2336789
theorem B5916017 : Blo 1557476 5916017 := bstep (se 2 (by rfl) ⟨2218506, by rfl⟩ : syracuseStep 5916017 = 4437013) B4437013
theorem B34162033 : Blo 1557476 34162033 := bstep (se 2 (by rfl) ⟨12810762, by rfl⟩ : syracuseStep 34162033 = 25621525) B25621525
theorem B1557875 : Blo 1557476 1557875 := bstep (se 1 (by rfl) ⟨1168406, by rfl⟩ : syracuseStep 1557875 = 2336813) B2336813
theorem B3507569 : Blo 1557476 3507569 := bstep (se 2 (by rfl) ⟨1315338, by rfl⟩ : syracuseStep 3507569 = 2630677) B2630677
theorem B1557891 : Blo 1557476 1557891 := bstep (se 1 (by rfl) ⟨1168418, by rfl⟩ : syracuseStep 1557891 = 2336837) B2336837
theorem B9987461 : Blo 1557476 9987461 := bstep (se 4 (by rfl) ⟨936324, by rfl⟩ : syracuseStep 9987461 = 1872649) B1872649
theorem B3507587 : Blo 1557476 3507587 := bstep (se 1 (by rfl) ⟨2630690, by rfl⟩ : syracuseStep 3507587 = 5261381) B5261381
theorem B1557907 : Blo 1557476 1557907 := bstep (se 1 (by rfl) ⟨1168430, by rfl⟩ : syracuseStep 1557907 = 2336861) B2336861
theorem B1557923 : Blo 1557476 1557923 := bstep (se 1 (by rfl) ⟨1168442, by rfl⟩ : syracuseStep 1557923 = 2336885) B2336885
theorem B4990385 : Blo 1557476 4990385 := bstep (se 2 (by rfl) ⟨1871394, by rfl⟩ : syracuseStep 4990385 = 3742789) B3742789
theorem B2631089 : Blo 1557476 2631089 := bstep (se 2 (by rfl) ⟨986658, by rfl⟩ : syracuseStep 2631089 = 1973317) B1973317
theorem B1557939 : Blo 1557476 1557939 := bstep (se 1 (by rfl) ⟨1168454, by rfl⟩ : syracuseStep 1557939 = 2336909) B2336909
theorem B1557955 : Blo 1557476 1557955 := bstep (se 1 (by rfl) ⟨1168466, by rfl⟩ : syracuseStep 1557955 = 2336933) B2336933
theorem B1557971 : Blo 1557476 1557971 := bstep (se 1 (by rfl) ⟨1168478, by rfl⟩ : syracuseStep 1557971 = 2336957) B2336957
theorem B2336225 : Blo 1557476 2336225 := bstep (se 2 (by rfl) ⟨876084, by rfl⟩ : syracuseStep 2336225 = 1752169) B1752169
theorem B1557987 : Blo 1557476 1557987 := bstep (se 1 (by rfl) ⟨1168490, by rfl⟩ : syracuseStep 1557987 = 2336981) B2336981
theorem B2336243 : Blo 1557476 2336243 := bstep (se 1 (by rfl) ⟨1752182, by rfl⟩ : syracuseStep 2336243 = 3504365) B3504365
theorem B1558003 : Blo 1557476 1558003 := bstep (se 1 (by rfl) ⟨1168502, by rfl⟩ : syracuseStep 1558003 = 2337005) B2337005
theorem B1558019 : Blo 1557476 1558019 := bstep (se 1 (by rfl) ⟨1168514, by rfl⟩ : syracuseStep 1558019 = 2337029) B2337029
theorem B2336273 : Blo 1557476 2336273 := bstep (se 2 (by rfl) ⟨876102, by rfl⟩ : syracuseStep 2336273 = 1752205) B1752205
theorem B1558035 : Blo 1557476 1558035 := bstep (se 1 (by rfl) ⟨1168526, by rfl⟩ : syracuseStep 1558035 = 2337053) B2337053
theorem B2336291 : Blo 1557476 2336291 := bstep (se 1 (by rfl) ⟨1752218, by rfl⟩ : syracuseStep 2336291 = 3504437) B3504437
theorem B1558051 : Blo 1557476 1558051 := bstep (se 1 (by rfl) ⟨1168538, by rfl⟩ : syracuseStep 1558051 = 2337077) B2337077
theorem B2631217 : Blo 1557476 2631217 := bstep (se 2 (by rfl) ⟨986706, by rfl⟩ : syracuseStep 2631217 = 1973413) B1973413
theorem B1558067 : Blo 1557476 1558067 := bstep (se 1 (by rfl) ⟨1168550, by rfl⟩ : syracuseStep 1558067 = 2337101) B2337101
theorem B2336321 : Blo 1557476 2336321 := bstep (se 2 (by rfl) ⟨876120, by rfl⟩ : syracuseStep 2336321 = 1752241) B1752241
theorem B1558083 : Blo 1557476 1558083 := bstep (se 1 (by rfl) ⟨1168562, by rfl⟩ : syracuseStep 1558083 = 2337125) B2337125
theorem B8873549 : Blo 1557476 8873549 := bstep (se 3 (by rfl) ⟨1663790, by rfl⟩ : syracuseStep 8873549 = 3327581) B3327581
theorem B2336339 : Blo 1557476 2336339 := bstep (se 1 (by rfl) ⟨1752254, by rfl⟩ : syracuseStep 2336339 = 3504509) B3504509
theorem B1558099 : Blo 1557476 1558099 := bstep (se 1 (by rfl) ⟨1168574, by rfl⟩ : syracuseStep 1558099 = 2337149) B2337149
theorem B2631251 : Blo 1557476 2631251 := bstep (se 1 (by rfl) ⟨1973438, by rfl⟩ : syracuseStep 2631251 = 3946877) B3946877
theorem B1558115 : Blo 1557476 1558115 := bstep (se 1 (by rfl) ⟨1168586, by rfl⟩ : syracuseStep 1558115 = 2337173) B2337173
theorem B2336369 : Blo 1557476 2336369 := bstep (se 2 (by rfl) ⟨876138, by rfl⟩ : syracuseStep 2336369 = 1752277) B1752277
theorem B4212337 : Blo 1557476 4212337 := bstep (se 2 (by rfl) ⟨1579626, by rfl⟩ : syracuseStep 4212337 = 3159253) B3159253
theorem B1558131 : Blo 1557476 1558131 := bstep (se 1 (by rfl) ⟨1168598, by rfl⟩ : syracuseStep 1558131 = 2337197) B2337197
theorem B26642033 : Blo 1557476 26642033 := bstep (se 2 (by rfl) ⟨9990762, by rfl⟩ : syracuseStep 26642033 = 19981525) B19981525
theorem B2336387 : Blo 1557476 2336387 := bstep (se 1 (by rfl) ⟨1752290, by rfl⟩ : syracuseStep 2336387 = 3504581) B3504581
theorem B1558147 : Blo 1557476 1558147 := bstep (se 1 (by rfl) ⟨1168610, by rfl⟩ : syracuseStep 1558147 = 2337221) B2337221
theorem B3507857 : Blo 1557476 3507857 := bstep (se 2 (by rfl) ⟨1315446, by rfl⟩ : syracuseStep 3507857 = 2630893) B2630893
theorem B1558163 : Blo 1557476 1558163 := bstep (se 1 (by rfl) ⟨1168622, by rfl⟩ : syracuseStep 1558163 = 2337245) B2337245
theorem B2336417 : Blo 1557476 2336417 := bstep (se 2 (by rfl) ⟨876156, by rfl⟩ : syracuseStep 2336417 = 1752313) B1752313
theorem B1558179 : Blo 1557476 1558179 := bstep (se 1 (by rfl) ⟨1168634, by rfl⟩ : syracuseStep 1558179 = 2337269) B2337269
theorem B3507875 : Blo 1557476 3507875 := bstep (se 1 (by rfl) ⟨2630906, by rfl⟩ : syracuseStep 3507875 = 5261813) B5261813
theorem B2336435 : Blo 1557476 2336435 := bstep (se 1 (by rfl) ⟨1752326, by rfl⟩ : syracuseStep 2336435 = 3504653) B3504653
theorem B1558195 : Blo 1557476 1558195 := bstep (se 1 (by rfl) ⟨1168646, by rfl⟩ : syracuseStep 1558195 = 2337293) B2337293
theorem B1558211 : Blo 1557476 1558211 := bstep (se 1 (by rfl) ⟨1168658, by rfl⟩ : syracuseStep 1558211 = 2337317) B2337317
theorem B2336465 : Blo 1557476 2336465 := bstep (se 2 (by rfl) ⟨876174, by rfl⟩ : syracuseStep 2336465 = 1752349) B1752349
theorem B1558227 : Blo 1557476 1558227 := bstep (se 1 (by rfl) ⟨1168670, by rfl⟩ : syracuseStep 1558227 = 2337341) B2337341
theorem B2631379 : Blo 1557476 2631379 := bstep (se 1 (by rfl) ⟨1973534, by rfl⟩ : syracuseStep 2631379 = 3947069) B3947069
theorem B2336483 : Blo 1557476 2336483 := bstep (se 1 (by rfl) ⟨1752362, by rfl⟩ : syracuseStep 2336483 = 3504725) B3504725
theorem B1558243 : Blo 1557476 1558243 := bstep (se 1 (by rfl) ⟨1168682, by rfl⟩ : syracuseStep 1558243 = 2337365) B2337365
theorem B1558259 : Blo 1557476 1558259 := bstep (se 1 (by rfl) ⟨1168694, by rfl⟩ : syracuseStep 1558259 = 2337389) B2337389
theorem B2336513 : Blo 1557476 2336513 := bstep (se 2 (by rfl) ⟨876192, by rfl⟩ : syracuseStep 2336513 = 1752385) B1752385
theorem B1558275 : Blo 1557476 1558275 := bstep (se 1 (by rfl) ⟨1168706, by rfl⟩ : syracuseStep 1558275 = 2337413) B2337413
theorem B2336531 : Blo 1557476 2336531 := bstep (se 1 (by rfl) ⟨1752398, by rfl⟩ : syracuseStep 2336531 = 3504797) B3504797
theorem B1558291 : Blo 1557476 1558291 := bstep (se 1 (by rfl) ⟨1168718, by rfl⟩ : syracuseStep 1558291 = 2337437) B2337437
theorem B1558307 : Blo 1557476 1558307 := bstep (se 1 (by rfl) ⟨1168730, by rfl⟩ : syracuseStep 1558307 = 2337461) B2337461
theorem B1664803 : Blo 1557476 1664803 := bstep (se 1 (by rfl) ⟨1248602, by rfl⟩ : syracuseStep 1664803 = 2497205) B2497205
theorem B2336561 : Blo 1557476 2336561 := bstep (se 2 (by rfl) ⟨876210, by rfl⟩ : syracuseStep 2336561 = 1752421) B1752421
theorem B1558323 : Blo 1557476 1558323 := bstep (se 1 (by rfl) ⟨1168742, by rfl⟩ : syracuseStep 1558323 = 2337485) B2337485
theorem B2336579 : Blo 1557476 2336579 := bstep (se 1 (by rfl) ⟨1752434, by rfl⟩ : syracuseStep 2336579 = 3504869) B3504869
theorem B1558339 : Blo 1557476 1558339 := bstep (se 1 (by rfl) ⟨1168754, by rfl⟩ : syracuseStep 1558339 = 2337509) B2337509
theorem B10659653 : Blo 1557476 10659653 := bstep (se 4 (by rfl) ⟨999342, by rfl⟩ : syracuseStep 10659653 = 1998685) B1998685
theorem B1558355 : Blo 1557476 1558355 := bstep (se 1 (by rfl) ⟨1168766, by rfl⟩ : syracuseStep 1558355 = 2337533) B2337533
theorem B2336609 : Blo 1557476 2336609 := bstep (se 2 (by rfl) ⟨876228, by rfl⟩ : syracuseStep 2336609 = 1752457) B1752457
theorem B2631521 : Blo 1557476 2631521 := bstep (se 2 (by rfl) ⟨986820, by rfl⟩ : syracuseStep 2631521 = 1973641) B1973641
theorem B1558371 : Blo 1557476 1558371 := bstep (se 1 (by rfl) ⟨1168778, by rfl⟩ : syracuseStep 1558371 = 2337557) B2337557
theorem B5261165 : Blo 1557476 5261165 := bstep (se 3 (by rfl) ⟨986468, by rfl⟩ : syracuseStep 5261165 = 1972937) B1972937
theorem B2336627 : Blo 1557476 2336627 := bstep (se 1 (by rfl) ⟨1752470, by rfl⟩ : syracuseStep 2336627 = 3504941) B3504941
theorem B1558387 : Blo 1557476 1558387 := bstep (se 1 (by rfl) ⟨1168790, by rfl⟩ : syracuseStep 1558387 = 2337581) B2337581
theorem B1558403 : Blo 1557476 1558403 := bstep (se 1 (by rfl) ⟨1168802, by rfl⟩ : syracuseStep 1558403 = 2337605) B2337605
theorem B2336657 : Blo 1557476 2336657 := bstep (se 2 (by rfl) ⟨876246, by rfl⟩ : syracuseStep 2336657 = 1752493) B1752493
theorem B1558419 : Blo 1557476 1558419 := bstep (se 1 (by rfl) ⟨1168814, by rfl⟩ : syracuseStep 1558419 = 2337629) B2337629
theorem B2336675 : Blo 1557476 2336675 := bstep (se 1 (by rfl) ⟨1752506, by rfl⟩ : syracuseStep 2336675 = 3505013) B3505013
theorem B1558435 : Blo 1557476 1558435 := bstep (se 1 (by rfl) ⟨1168826, by rfl⟩ : syracuseStep 1558435 = 2337653) B2337653
theorem B5261219 : Blo 1557476 5261219 := bstep (se 1 (by rfl) ⟨3945914, by rfl⟩ : syracuseStep 5261219 = 7891829) B7891829
theorem B3508145 : Blo 1557476 3508145 := bstep (se 2 (by rfl) ⟨1315554, by rfl⟩ : syracuseStep 3508145 = 2631109) B2631109
theorem B1558451 : Blo 1557476 1558451 := bstep (se 1 (by rfl) ⟨1168838, by rfl⟩ : syracuseStep 1558451 = 2337677) B2337677
theorem B2336705 : Blo 1557476 2336705 := bstep (se 2 (by rfl) ⟨876264, by rfl⟩ : syracuseStep 2336705 = 1752529) B1752529
theorem B1558467 : Blo 1557476 1558467 := bstep (se 1 (by rfl) ⟨1168850, by rfl⟩ : syracuseStep 1558467 = 2337701) B2337701
theorem B3508163 : Blo 1557476 3508163 := bstep (se 1 (by rfl) ⟨2631122, by rfl⟩ : syracuseStep 3508163 = 5262245) B5262245
theorem B2336723 : Blo 1557476 2336723 := bstep (se 1 (by rfl) ⟨1752542, by rfl⟩ : syracuseStep 2336723 = 3505085) B3505085
theorem B1558483 : Blo 1557476 1558483 := bstep (se 1 (by rfl) ⟨1168862, by rfl⟩ : syracuseStep 1558483 = 2337725) B2337725
theorem B3942371 : Blo 1557476 3942371 := bstep (se 1 (by rfl) ⟨2956778, by rfl⟩ : syracuseStep 3942371 = 5913557) B5913557
theorem B1558499 : Blo 1557476 1558499 := bstep (se 1 (by rfl) ⟨1168874, by rfl⟩ : syracuseStep 1558499 = 2337749) B2337749
theorem B2107363 : Blo 1557476 2107363 := bstep (se 1 (by rfl) ⟨1580522, by rfl⟩ : syracuseStep 2107363 = 3161045) B3161045
theorem B2336753 : Blo 1557476 2336753 := bstep (se 2 (by rfl) ⟨876282, by rfl⟩ : syracuseStep 2336753 = 1752565) B1752565
theorem B2959345 : Blo 1557476 2959345 := bstep (se 2 (by rfl) ⟨1109754, by rfl⟩ : syracuseStep 2959345 = 2219509) B2219509
theorem B1558515 : Blo 1557476 1558515 := bstep (se 1 (by rfl) ⟨1168886, by rfl⟩ : syracuseStep 1558515 = 2337773) B2337773
theorem B2336771 : Blo 1557476 2336771 := bstep (se 1 (by rfl) ⟨1752578, by rfl⟩ : syracuseStep 2336771 = 3505157) B3505157
theorem B1558531 : Blo 1557476 1558531 := bstep (se 1 (by rfl) ⟨1168898, by rfl⟩ : syracuseStep 1558531 = 2337797) B2337797
theorem B5916685 : Blo 1557476 5916685 := bstep (se 3 (by rfl) ⟨1109378, by rfl⟩ : syracuseStep 5916685 = 2218757) B2218757
theorem B7112717 : Blo 1557476 7112717 := bstep (se 3 (by rfl) ⟨1333634, by rfl⟩ : syracuseStep 7112717 = 2667269) B2667269
theorem B1558547 : Blo 1557476 1558547 := bstep (se 1 (by rfl) ⟨1168910, by rfl⟩ : syracuseStep 1558547 = 2337821) B2337821
theorem B2336801 : Blo 1557476 2336801 := bstep (se 2 (by rfl) ⟨876300, by rfl⟩ : syracuseStep 2336801 = 1752601) B1752601
theorem B1558563 : Blo 1557476 1558563 := bstep (se 1 (by rfl) ⟨1168922, by rfl⟩ : syracuseStep 1558563 = 2337845) B2337845
theorem B2336819 : Blo 1557476 2336819 := bstep (se 1 (by rfl) ⟨1752614, by rfl⟩ : syracuseStep 2336819 = 3505229) B3505229
theorem B1558579 : Blo 1557476 1558579 := bstep (se 1 (by rfl) ⟨1168934, by rfl⟩ : syracuseStep 1558579 = 2337869) B2337869
theorem B1558595 : Blo 1557476 1558595 := bstep (se 1 (by rfl) ⟨1168946, by rfl⟩ : syracuseStep 1558595 = 2337893) B2337893
theorem B12634181 : Blo 1557476 12634181 := bstep (se 4 (by rfl) ⟨1184454, by rfl⟩ : syracuseStep 12634181 = 2368909) B2368909
theorem B2336849 : Blo 1557476 2336849 := bstep (se 2 (by rfl) ⟨876318, by rfl⟩ : syracuseStep 2336849 = 1752637) B1752637
theorem B1558611 : Blo 1557476 1558611 := bstep (se 1 (by rfl) ⟨1168958, by rfl⟩ : syracuseStep 1558611 = 2337917) B2337917
theorem B2336867 : Blo 1557476 2336867 := bstep (se 1 (by rfl) ⟨1752650, by rfl⟩ : syracuseStep 2336867 = 3505301) B3505301
theorem B1558627 : Blo 1557476 1558627 := bstep (se 1 (by rfl) ⟨1168970, by rfl⟩ : syracuseStep 1558627 = 2337941) B2337941
theorem B1558643 : Blo 1557476 1558643 := bstep (se 1 (by rfl) ⟨1168982, by rfl⟩ : syracuseStep 1558643 = 2337965) B2337965
theorem B2336897 : Blo 1557476 2336897 := bstep (se 2 (by rfl) ⟨876336, by rfl⟩ : syracuseStep 2336897 = 1752673) B1752673
theorem B1558659 : Blo 1557476 1558659 := bstep (se 1 (by rfl) ⟨1168994, by rfl⟩ : syracuseStep 1558659 = 2337989) B2337989
theorem B2336915 : Blo 1557476 2336915 := bstep (se 1 (by rfl) ⟨1752686, by rfl⟩ : syracuseStep 2336915 = 3505373) B3505373
theorem B2369683 : Blo 1557476 2369683 := bstep (se 1 (by rfl) ⟨1777262, by rfl⟩ : syracuseStep 2369683 = 3554525) B3554525
theorem B1558675 : Blo 1557476 1558675 := bstep (se 1 (by rfl) ⟨1169006, by rfl⟩ : syracuseStep 1558675 = 2338013) B2338013
theorem B8538275 : Blo 1557476 8538275 := bstep (se 1 (by rfl) ⟨6403706, by rfl⟩ : syracuseStep 8538275 = 12807413) B12807413
theorem B1558691 : Blo 1557476 1558691 := bstep (se 1 (by rfl) ⟨1169018, by rfl⟩ : syracuseStep 1558691 = 2338037) B2338037
theorem B2336945 : Blo 1557476 2336945 := bstep (se 2 (by rfl) ⟨876354, by rfl⟩ : syracuseStep 2336945 = 1752709) B1752709
theorem B5261489 : Blo 1557476 5261489 := bstep (se 2 (by rfl) ⟨1973058, by rfl⟩ : syracuseStep 5261489 = 3946117) B3946117
theorem B1558707 : Blo 1557476 1558707 := bstep (se 1 (by rfl) ⟨1169030, by rfl⟩ : syracuseStep 1558707 = 2338061) B2338061
theorem B2336963 : Blo 1557476 2336963 := bstep (se 1 (by rfl) ⟨1752722, by rfl⟩ : syracuseStep 2336963 = 3505445) B3505445
theorem B1558723 : Blo 1557476 1558723 := bstep (se 1 (by rfl) ⟨1169042, by rfl⟩ : syracuseStep 1558723 = 2338085) B2338085
theorem B9980101 : Blo 1557476 9980101 := bstep (se 4 (by rfl) ⟨935634, by rfl⟩ : syracuseStep 9980101 = 1871269) B1871269
theorem B10807501 : Blo 1557476 10807501 := bstep (se 3 (by rfl) ⟨2026406, by rfl⟩ : syracuseStep 10807501 = 4052813) B4052813
theorem B3508433 : Blo 1557476 3508433 := bstep (se 2 (by rfl) ⟨1315662, by rfl⟩ : syracuseStep 3508433 = 2631325) B2631325
theorem B1558739 : Blo 1557476 1558739 := bstep (se 1 (by rfl) ⟨1169054, by rfl⟩ : syracuseStep 1558739 = 2338109) B2338109
theorem B2336993 : Blo 1557476 2336993 := bstep (se 2 (by rfl) ⟨876372, by rfl⟩ : syracuseStep 2336993 = 1752745) B1752745
theorem B1558755 : Blo 1557476 1558755 := bstep (se 1 (by rfl) ⟨1169066, by rfl⟩ : syracuseStep 1558755 = 2338133) B2338133
theorem B3508451 : Blo 1557476 3508451 := bstep (se 1 (by rfl) ⟨2631338, by rfl⟩ : syracuseStep 3508451 = 5262677) B5262677
theorem B2337011 : Blo 1557476 2337011 := bstep (se 1 (by rfl) ⟨1752758, by rfl⟩ : syracuseStep 2337011 = 3505517) B3505517
theorem B1558771 : Blo 1557476 1558771 := bstep (se 1 (by rfl) ⟨1169078, by rfl⟩ : syracuseStep 1558771 = 2338157) B2338157
theorem B1558787 : Blo 1557476 1558787 := bstep (se 1 (by rfl) ⟨1169090, by rfl⟩ : syracuseStep 1558787 = 2338181) B2338181
theorem B6654221 : Blo 1557476 6654221 := bstep (se 3 (by rfl) ⟨1247666, by rfl⟩ : syracuseStep 6654221 = 2495333) B2495333
theorem B2337041 : Blo 1557476 2337041 := bstep (se 2 (by rfl) ⟨876390, by rfl⟩ : syracuseStep 2337041 = 1752781) B1752781
theorem B1558803 : Blo 1557476 1558803 := bstep (se 1 (by rfl) ⟨1169102, by rfl⟩ : syracuseStep 1558803 = 2338205) B2338205
theorem B2337059 : Blo 1557476 2337059 := bstep (se 1 (by rfl) ⟨1752794, by rfl⟩ : syracuseStep 2337059 = 3505589) B3505589
theorem B1558819 : Blo 1557476 1558819 := bstep (se 1 (by rfl) ⟨1169114, by rfl⟩ : syracuseStep 1558819 = 2338229) B2338229
theorem B6654257 : Blo 1557476 6654257 := bstep (se 2 (by rfl) ⟨2495346, by rfl⟩ : syracuseStep 6654257 = 4990693) B4990693
theorem B1558835 : Blo 1557476 1558835 := bstep (se 1 (by rfl) ⟨1169126, by rfl⟩ : syracuseStep 1558835 = 2338253) B2338253
theorem B2337089 : Blo 1557476 2337089 := bstep (se 2 (by rfl) ⟨876408, by rfl⟩ : syracuseStep 2337089 = 1752817) B1752817
theorem B1558851 : Blo 1557476 1558851 := bstep (se 1 (by rfl) ⟨1169138, by rfl⟩ : syracuseStep 1558851 = 2338277) B2338277
theorem B2337107 : Blo 1557476 2337107 := bstep (se 1 (by rfl) ⟨1752830, by rfl⟩ : syracuseStep 2337107 = 3505661) B3505661
theorem B1558867 : Blo 1557476 1558867 := bstep (se 1 (by rfl) ⟨1169150, by rfl⟩ : syracuseStep 1558867 = 2338301) B2338301
theorem B5613923 : Blo 1557476 5613923 := bstep (se 1 (by rfl) ⟨4210442, by rfl⟩ : syracuseStep 5613923 = 8420885) B8420885
theorem B1558883 : Blo 1557476 1558883 := bstep (se 1 (by rfl) ⟨1169162, by rfl⟩ : syracuseStep 1558883 = 2338325) B2338325
theorem B2337137 : Blo 1557476 2337137 := bstep (se 2 (by rfl) ⟨876426, by rfl⟩ : syracuseStep 2337137 = 1752853) B1752853
theorem B1558899 : Blo 1557476 1558899 := bstep (se 1 (by rfl) ⟨1169174, by rfl⟩ : syracuseStep 1558899 = 2338349) B2338349
theorem B2337155 : Blo 1557476 2337155 := bstep (se 1 (by rfl) ⟨1752866, by rfl⟩ : syracuseStep 2337155 = 3505733) B3505733
theorem B1558915 : Blo 1557476 1558915 := bstep (se 1 (by rfl) ⟨1169186, by rfl⟩ : syracuseStep 1558915 = 2338373) B2338373
theorem B1558931 : Blo 1557476 1558931 := bstep (se 1 (by rfl) ⟨1169198, by rfl⟩ : syracuseStep 1558931 = 2338397) B2338397
theorem B2337185 : Blo 1557476 2337185 := bstep (se 2 (by rfl) ⟨876444, by rfl⟩ : syracuseStep 2337185 = 1752889) B1752889
theorem B1558947 : Blo 1557476 1558947 := bstep (se 1 (by rfl) ⟨1169210, by rfl⟩ : syracuseStep 1558947 = 2338421) B2338421
theorem B2337203 : Blo 1557476 2337203 := bstep (se 1 (by rfl) ⟨1752902, by rfl⟩ : syracuseStep 2337203 = 3505805) B3505805
theorem B1558963 : Blo 1557476 1558963 := bstep (se 1 (by rfl) ⟨1169222, by rfl⟩ : syracuseStep 1558963 = 2338445) B2338445
theorem B1558979 : Blo 1557476 1558979 := bstep (se 1 (by rfl) ⟨1169234, by rfl⟩ : syracuseStep 1558979 = 2338469) B2338469
theorem B7489997 : Blo 1557476 7489997 := bstep (se 3 (by rfl) ⟨1404374, by rfl⟩ : syracuseStep 7489997 = 2808749) B2808749
theorem B2337233 : Blo 1557476 2337233 := bstep (se 2 (by rfl) ⟨876462, by rfl⟩ : syracuseStep 2337233 = 1752925) B1752925
theorem B1558995 : Blo 1557476 1558995 := bstep (se 1 (by rfl) ⟨1169246, by rfl⟩ : syracuseStep 1558995 = 2338493) B2338493
theorem B2337251 : Blo 1557476 2337251 := bstep (se 1 (by rfl) ⟨1752938, by rfl⟩ : syracuseStep 2337251 = 3505877) B3505877
theorem B1559011 : Blo 1557476 1559011 := bstep (se 1 (by rfl) ⟨1169258, by rfl⟩ : syracuseStep 1559011 = 2338517) B2338517
theorem B8874481 : Blo 1557476 8874481 := bstep (se 2 (by rfl) ⟨3327930, by rfl⟩ : syracuseStep 8874481 = 6655861) B6655861
theorem B1559027 : Blo 1557476 1559027 := bstep (se 1 (by rfl) ⟨1169270, by rfl⟩ : syracuseStep 1559027 = 2338541) B2338541
theorem B3508721 : Blo 1557476 3508721 := bstep (se 2 (by rfl) ⟨1315770, by rfl⟩ : syracuseStep 3508721 = 2631541) B2631541
theorem B2337281 : Blo 1557476 2337281 := bstep (se 2 (by rfl) ⟨876480, by rfl⟩ : syracuseStep 2337281 = 1752961) B1752961
theorem B1559043 : Blo 1557476 1559043 := bstep (se 1 (by rfl) ⟨1169282, by rfl⟩ : syracuseStep 1559043 = 2338565) B2338565
theorem B3508739 : Blo 1557476 3508739 := bstep (se 1 (by rfl) ⟨2631554, by rfl⟩ : syracuseStep 3508739 = 5263109) B5263109
theorem B19982861 : Blo 1557476 19982861 := bstep (se 3 (by rfl) ⟨3746786, by rfl⟩ : syracuseStep 19982861 = 7493573) B7493573
theorem B2337299 : Blo 1557476 2337299 := bstep (se 1 (by rfl) ⟨1752974, by rfl⟩ : syracuseStep 2337299 = 3505949) B3505949
theorem B1559059 : Blo 1557476 1559059 := bstep (se 1 (by rfl) ⟨1169294, by rfl⟩ : syracuseStep 1559059 = 2338589) B2338589
theorem B1559075 : Blo 1557476 1559075 := bstep (se 1 (by rfl) ⟨1169306, by rfl⟩ : syracuseStep 1559075 = 2338613) B2338613
theorem B2337329 : Blo 1557476 2337329 := bstep (se 2 (by rfl) ⟨876498, by rfl⟩ : syracuseStep 2337329 = 1752997) B1752997
theorem B7891505 : Blo 1557476 7891505 := bstep (se 2 (by rfl) ⟨2959314, by rfl⟩ : syracuseStep 7891505 = 5918629) B5918629
theorem B1559091 : Blo 1557476 1559091 := bstep (se 1 (by rfl) ⟨1169318, by rfl⟩ : syracuseStep 1559091 = 2338637) B2338637
theorem B2337347 : Blo 1557476 2337347 := bstep (se 1 (by rfl) ⟨1753010, by rfl⟩ : syracuseStep 2337347 = 3506021) B3506021
theorem B1559107 : Blo 1557476 1559107 := bstep (se 1 (by rfl) ⟨1169330, by rfl⟩ : syracuseStep 1559107 = 2338661) B2338661
theorem B1559123 : Blo 1557476 1559123 := bstep (se 1 (by rfl) ⟨1169342, by rfl⟩ : syracuseStep 1559123 = 2338685) B2338685
theorem B2337377 : Blo 1557476 2337377 := bstep (se 2 (by rfl) ⟨876516, by rfl⟩ : syracuseStep 2337377 = 1753033) B1753033
theorem B1559139 : Blo 1557476 1559139 := bstep (se 1 (by rfl) ⟨1169354, by rfl⟩ : syracuseStep 1559139 = 2338709) B2338709
theorem B2337395 : Blo 1557476 2337395 := bstep (se 1 (by rfl) ⟨1753046, by rfl⟩ : syracuseStep 2337395 = 3506093) B3506093
theorem B1559155 : Blo 1557476 1559155 := bstep (se 1 (by rfl) ⟨1169366, by rfl⟩ : syracuseStep 1559155 = 2338733) B2338733
theorem B1559171 : Blo 1557476 1559171 := bstep (se 1 (by rfl) ⟨1169378, by rfl⟩ : syracuseStep 1559171 = 2338757) B2338757
theorem B2337425 : Blo 1557476 2337425 := bstep (se 2 (by rfl) ⟨876534, by rfl⟩ : syracuseStep 2337425 = 1753069) B1753069
theorem B1559187 : Blo 1557476 1559187 := bstep (se 1 (by rfl) ⟨1169390, by rfl⟩ : syracuseStep 1559187 = 2338781) B2338781
theorem B2337443 : Blo 1557476 2337443 := bstep (se 1 (by rfl) ⟨1753082, by rfl⟩ : syracuseStep 2337443 = 3506165) B3506165
theorem B1559203 : Blo 1557476 1559203 := bstep (se 1 (by rfl) ⟨1169402, by rfl⟩ : syracuseStep 1559203 = 2338805) B2338805
theorem B1559219 : Blo 1557476 1559219 := bstep (se 1 (by rfl) ⟨1169414, by rfl⟩ : syracuseStep 1559219 = 2338829) B2338829
theorem B2337473 : Blo 1557476 2337473 := bstep (se 2 (by rfl) ⟨876552, by rfl⟩ : syracuseStep 2337473 = 1753105) B1753105
theorem B1559235 : Blo 1557476 1559235 := bstep (se 1 (by rfl) ⟨1169426, by rfl⟩ : syracuseStep 1559235 = 2338853) B2338853
theorem B9472717 : Blo 1557476 9472717 := bstep (se 3 (by rfl) ⟨1776134, by rfl⟩ : syracuseStep 9472717 = 3552269) B3552269
theorem B5262029 : Blo 1557476 5262029 := bstep (se 3 (by rfl) ⟨986630, by rfl⟩ : syracuseStep 5262029 = 1973261) B1973261
theorem B2337491 : Blo 1557476 2337491 := bstep (se 1 (by rfl) ⟨1753118, by rfl⟩ : syracuseStep 2337491 = 3506237) B3506237
theorem B1559251 : Blo 1557476 1559251 := bstep (se 1 (by rfl) ⟨1169438, by rfl⟩ : syracuseStep 1559251 = 2338877) B2338877
theorem B1559267 : Blo 1557476 1559267 := bstep (se 1 (by rfl) ⟨1169450, by rfl⟩ : syracuseStep 1559267 = 2338901) B2338901
theorem B2337521 : Blo 1557476 2337521 := bstep (se 2 (by rfl) ⟨876570, by rfl⟩ : syracuseStep 2337521 = 1753141) B1753141
theorem B1559283 : Blo 1557476 1559283 := bstep (se 1 (by rfl) ⟨1169462, by rfl⟩ : syracuseStep 1559283 = 2338925) B2338925
theorem B2337539 : Blo 1557476 2337539 := bstep (se 1 (by rfl) ⟨1753154, by rfl⟩ : syracuseStep 2337539 = 3506309) B3506309
theorem B5262083 : Blo 1557476 5262083 := bstep (se 1 (by rfl) ⟨3946562, by rfl⟩ : syracuseStep 5262083 = 7893125) B7893125
theorem B1559299 : Blo 1557476 1559299 := bstep (se 1 (by rfl) ⟨1169474, by rfl⟩ : syracuseStep 1559299 = 2338949) B2338949
theorem B1559315 : Blo 1557476 1559315 := bstep (se 1 (by rfl) ⟨1169486, by rfl⟩ : syracuseStep 1559315 = 2338973) B2338973
theorem B2337569 : Blo 1557476 2337569 := bstep (se 2 (by rfl) ⟨876588, by rfl⟩ : syracuseStep 2337569 = 1753177) B1753177
theorem B5917475 : Blo 1557476 5917475 := bstep (se 1 (by rfl) ⟨4438106, by rfl⟩ : syracuseStep 5917475 = 8876213) B8876213
theorem B1559331 : Blo 1557476 1559331 := bstep (se 1 (by rfl) ⟨1169498, by rfl⟩ : syracuseStep 1559331 = 2338997) B2338997
theorem B2337587 : Blo 1557476 2337587 := bstep (se 1 (by rfl) ⟨1753190, by rfl⟩ : syracuseStep 2337587 = 3506381) B3506381
theorem B1559347 : Blo 1557476 1559347 := bstep (se 1 (by rfl) ⟨1169510, by rfl⟩ : syracuseStep 1559347 = 2339021) B2339021
theorem B1559363 : Blo 1557476 1559363 := bstep (se 1 (by rfl) ⟨1169522, by rfl⟩ : syracuseStep 1559363 = 2339045) B2339045
theorem B2337617 : Blo 1557476 2337617 := bstep (se 2 (by rfl) ⟨876606, by rfl⟩ : syracuseStep 2337617 = 1753213) B1753213
theorem B1559379 : Blo 1557476 1559379 := bstep (se 1 (by rfl) ⟨1169534, by rfl⟩ : syracuseStep 1559379 = 2339069) B2339069
theorem B2337635 : Blo 1557476 2337635 := bstep (se 1 (by rfl) ⟨1753226, by rfl⟩ : syracuseStep 2337635 = 3506453) B3506453
theorem B1559395 : Blo 1557476 1559395 := bstep (se 1 (by rfl) ⟨1169546, by rfl⟩ : syracuseStep 1559395 = 2339093) B2339093
theorem B1559411 : Blo 1557476 1559411 := bstep (se 1 (by rfl) ⟨1169558, by rfl⟩ : syracuseStep 1559411 = 2339117) B2339117
theorem B2337665 : Blo 1557476 2337665 := bstep (se 2 (by rfl) ⟨876624, by rfl⟩ : syracuseStep 2337665 = 1753249) B1753249
theorem B1559427 : Blo 1557476 1559427 := bstep (se 1 (by rfl) ⟨1169570, by rfl⟩ : syracuseStep 1559427 = 2339141) B2339141
theorem B10259341 : Blo 1557476 10259341 := bstep (se 3 (by rfl) ⟨1923626, by rfl⟩ : syracuseStep 10259341 = 3847253) B3847253
theorem B3943313 : Blo 1557476 3943313 := bstep (se 2 (by rfl) ⟨1478742, by rfl⟩ : syracuseStep 3943313 = 2957485) B2957485
theorem B2337683 : Blo 1557476 2337683 := bstep (se 1 (by rfl) ⟨1753262, by rfl⟩ : syracuseStep 2337683 = 3506525) B3506525
theorem B1559443 : Blo 1557476 1559443 := bstep (se 1 (by rfl) ⟨1169582, by rfl⟩ : syracuseStep 1559443 = 2339165) B2339165
theorem B1559459 : Blo 1557476 1559459 := bstep (se 1 (by rfl) ⟨1169594, by rfl⟩ : syracuseStep 1559459 = 2339189) B2339189
theorem B2337713 : Blo 1557476 2337713 := bstep (se 2 (by rfl) ⟨876642, by rfl⟩ : syracuseStep 2337713 = 1753285) B1753285
theorem B1559475 : Blo 1557476 1559475 := bstep (se 1 (by rfl) ⟨1169606, by rfl⟩ : syracuseStep 1559475 = 2339213) B2339213
theorem B3943363 : Blo 1557476 3943363 := bstep (se 1 (by rfl) ⟨2957522, by rfl⟩ : syracuseStep 3943363 = 5915045) B5915045
theorem B2337731 : Blo 1557476 2337731 := bstep (se 1 (by rfl) ⟨1753298, by rfl⟩ : syracuseStep 2337731 = 3506597) B3506597
theorem B2337761 : Blo 1557476 2337761 := bstep (se 2 (by rfl) ⟨876660, by rfl⟩ : syracuseStep 2337761 = 1753321) B1753321
theorem B2337779 : Blo 1557476 2337779 := bstep (se 1 (by rfl) ⟨1753334, by rfl⟩ : syracuseStep 2337779 = 3506669) B3506669
theorem B2337809 : Blo 1557476 2337809 := bstep (se 2 (by rfl) ⟨876678, by rfl⟩ : syracuseStep 2337809 = 1753357) B1753357
theorem B5262353 : Blo 1557476 5262353 := bstep (se 2 (by rfl) ⟨1973382, by rfl⟩ : syracuseStep 5262353 = 3946765) B3946765
theorem B2960401 : Blo 1557476 2960401 := bstep (se 2 (by rfl) ⟨1110150, by rfl⟩ : syracuseStep 2960401 = 2220301) B2220301
theorem B2337827 : Blo 1557476 2337827 := bstep (se 1 (by rfl) ⟨1753370, by rfl⟩ : syracuseStep 2337827 = 3506741) B3506741
theorem B3329059 : Blo 1557476 3329059 := bstep (se 1 (by rfl) ⟨2496794, by rfl⟩ : syracuseStep 3329059 = 4993589) B4993589
theorem B2337857 : Blo 1557476 2337857 := bstep (se 2 (by rfl) ⟨876696, by rfl⟩ : syracuseStep 2337857 = 1753393) B1753393
theorem B12643397 : Blo 1557476 12643397 := bstep (se 4 (by rfl) ⟨1185318, by rfl⟩ : syracuseStep 12643397 = 2370637) B2370637
theorem B3943505 : Blo 1557476 3943505 := bstep (se 2 (by rfl) ⟨1478814, by rfl⟩ : syracuseStep 3943505 = 2957629) B2957629
theorem B2337875 : Blo 1557476 2337875 := bstep (se 1 (by rfl) ⟨1753406, by rfl⟩ : syracuseStep 2337875 = 3506813) B3506813
theorem B2337905 : Blo 1557476 2337905 := bstep (se 2 (by rfl) ⟨876714, by rfl⟩ : syracuseStep 2337905 = 1753429) B1753429
theorem B2337923 : Blo 1557476 2337923 := bstep (se 1 (by rfl) ⟨1753442, by rfl⟩ : syracuseStep 2337923 = 3506885) B3506885
theorem B2337953 : Blo 1557476 2337953 := bstep (se 2 (by rfl) ⟨876732, by rfl⟩ : syracuseStep 2337953 = 1753465) B1753465
theorem B2337971 : Blo 1557476 2337971 := bstep (se 1 (by rfl) ⟨1753478, by rfl⟩ : syracuseStep 2337971 = 3506957) B3506957
theorem B2338001 : Blo 1557476 2338001 := bstep (se 2 (by rfl) ⟨876750, by rfl⟩ : syracuseStep 2338001 = 1753501) B1753501
theorem B2338019 : Blo 1557476 2338019 := bstep (se 1 (by rfl) ⟨1753514, by rfl⟩ : syracuseStep 2338019 = 3507029) B3507029
theorem B2338049 : Blo 1557476 2338049 := bstep (se 2 (by rfl) ⟨876768, by rfl⟩ : syracuseStep 2338049 = 1753537) B1753537
theorem B2338067 : Blo 1557476 2338067 := bstep (se 1 (by rfl) ⟨1753550, by rfl⟩ : syracuseStep 2338067 = 3507101) B3507101
theorem B2370851 : Blo 1557476 2370851 := bstep (se 1 (by rfl) ⟨1778138, by rfl⟩ : syracuseStep 2370851 = 3556277) B3556277
theorem B2338097 : Blo 1557476 2338097 := bstep (se 2 (by rfl) ⟨876786, by rfl⟩ : syracuseStep 2338097 = 1753573) B1753573
theorem B43240757 : Blo 1557476 43240757 := bstep (se 5 (by rfl) ⟨2026910, by rfl⟩ : syracuseStep 43240757 = 4053821) B4053821
theorem B2338115 : Blo 1557476 2338115 := bstep (se 1 (by rfl) ⟨1753586, by rfl⟩ : syracuseStep 2338115 = 3507173) B3507173
theorem B2370899 : Blo 1557476 2370899 := bstep (se 1 (by rfl) ⟨1778174, by rfl⟩ : syracuseStep 2370899 = 3556349) B3556349
theorem B2338145 : Blo 1557476 2338145 := bstep (se 2 (by rfl) ⟨876804, by rfl⟩ : syracuseStep 2338145 = 1753609) B1753609
theorem B1871203 : Blo 1557476 1871203 := bstep (se 1 (by rfl) ⟨1403402, by rfl⟩ : syracuseStep 1871203 = 2806805) B2806805
theorem B2338163 : Blo 1557476 2338163 := bstep (se 1 (by rfl) ⟨1753622, by rfl⟩ : syracuseStep 2338163 = 3507245) B3507245
theorem B9121157 : Blo 1557476 9121157 := bstep (se 4 (by rfl) ⟨855108, by rfl⟩ : syracuseStep 9121157 = 1710217) B1710217
theorem B2338193 : Blo 1557476 2338193 := bstep (se 2 (by rfl) ⟨876822, by rfl⟩ : syracuseStep 2338193 = 1753645) B1753645
theorem B2338211 : Blo 1557476 2338211 := bstep (se 1 (by rfl) ⟨1753658, by rfl⟩ : syracuseStep 2338211 = 3507317) B3507317
theorem B4435373 : Blo 1557476 4435373 := bstep (se 3 (by rfl) ⟨831632, by rfl⟩ : syracuseStep 4435373 = 1663265) B1663265
theorem B5918129 : Blo 1557476 5918129 := bstep (se 2 (by rfl) ⟨2219298, by rfl⟩ : syracuseStep 5918129 = 4438597) B4438597
theorem B2338241 : Blo 1557476 2338241 := bstep (se 2 (by rfl) ⟨876840, by rfl⟩ : syracuseStep 2338241 = 1753681) B1753681
theorem B4992461 : Blo 1557476 4992461 := bstep (se 3 (by rfl) ⟨936086, by rfl⟩ : syracuseStep 4992461 = 1872173) B1872173
theorem B2338259 : Blo 1557476 2338259 := bstep (se 1 (by rfl) ⟨1753694, by rfl⟩ : syracuseStep 2338259 = 3507389) B3507389
theorem B2371027 : Blo 1557476 2371027 := bstep (se 1 (by rfl) ⟨1778270, by rfl⟩ : syracuseStep 2371027 = 3556541) B3556541
theorem B2338289 : Blo 1557476 2338289 := bstep (se 2 (by rfl) ⟨876858, by rfl⟩ : syracuseStep 2338289 = 1753717) B1753717
theorem B3157507 : Blo 1557476 3157507 := bstep (se 1 (by rfl) ⟨2368130, by rfl⟩ : syracuseStep 3157507 = 4736261) B4736261
theorem B2338307 : Blo 1557476 2338307 := bstep (se 1 (by rfl) ⟨1753730, by rfl⟩ : syracuseStep 2338307 = 3507461) B3507461
theorem B2338337 : Blo 1557476 2338337 := bstep (se 2 (by rfl) ⟨876876, by rfl⟩ : syracuseStep 2338337 = 1753753) B1753753
theorem B5262893 : Blo 1557476 5262893 := bstep (se 3 (by rfl) ⟨986792, by rfl⟩ : syracuseStep 5262893 = 1973585) B1973585
theorem B2338355 : Blo 1557476 2338355 := bstep (se 1 (by rfl) ⟨1753766, by rfl⟩ : syracuseStep 2338355 = 3507533) B3507533
theorem B2338385 : Blo 1557476 2338385 := bstep (se 2 (by rfl) ⟨876894, by rfl⟩ : syracuseStep 2338385 = 1753789) B1753789
theorem B4435555 : Blo 1557476 4435555 := bstep (se 1 (by rfl) ⟨3326666, by rfl⟩ : syracuseStep 4435555 = 6653333) B6653333
theorem B2338403 : Blo 1557476 2338403 := bstep (se 1 (by rfl) ⟨1753802, by rfl⟩ : syracuseStep 2338403 = 3507605) B3507605
theorem B5262947 : Blo 1557476 5262947 := bstep (se 1 (by rfl) ⟨3947210, by rfl⟩ : syracuseStep 5262947 = 7894421) B7894421
theorem B2338433 : Blo 1557476 2338433 := bstep (se 2 (by rfl) ⟨876912, by rfl⟩ : syracuseStep 2338433 = 1753825) B1753825
theorem B2338451 : Blo 1557476 2338451 := bstep (se 1 (by rfl) ⟨1753838, by rfl⟩ : syracuseStep 2338451 = 3507677) B3507677
theorem B2338481 : Blo 1557476 2338481 := bstep (se 2 (by rfl) ⟨876930, by rfl⟩ : syracuseStep 2338481 = 1753861) B1753861
theorem B2338499 : Blo 1557476 2338499 := bstep (se 1 (by rfl) ⟨1753874, by rfl⟩ : syracuseStep 2338499 = 3507749) B3507749
theorem B9875141 : Blo 1557476 9875141 := bstep (se 4 (by rfl) ⟨925794, by rfl⟩ : syracuseStep 9875141 = 1851589) B1851589
theorem B2338529 : Blo 1557476 2338529 := bstep (se 2 (by rfl) ⟨876948, by rfl⟩ : syracuseStep 2338529 = 1753897) B1753897
theorem B2338547 : Blo 1557476 2338547 := bstep (se 1 (by rfl) ⟨1753910, by rfl⟩ : syracuseStep 2338547 = 3507821) B3507821
theorem B4435715 : Blo 1557476 4435715 := bstep (se 1 (by rfl) ⟨3326786, by rfl⟩ : syracuseStep 4435715 = 6653573) B6653573
theorem B4738819 : Blo 1557476 4738819 := bstep (se 1 (by rfl) ⟨3554114, by rfl⟩ : syracuseStep 4738819 = 7108229) B7108229
theorem B2338577 : Blo 1557476 2338577 := bstep (se 2 (by rfl) ⟨876966, by rfl⟩ : syracuseStep 2338577 = 1753933) B1753933
theorem B2338595 : Blo 1557476 2338595 := bstep (se 1 (by rfl) ⟨1753946, by rfl⟩ : syracuseStep 2338595 = 3507893) B3507893
theorem B2338625 : Blo 1557476 2338625 := bstep (se 2 (by rfl) ⟨876984, by rfl⟩ : syracuseStep 2338625 = 1753969) B1753969
theorem B2338643 : Blo 1557476 2338643 := bstep (se 1 (by rfl) ⟨1753982, by rfl⟩ : syracuseStep 2338643 = 3507965) B3507965
theorem B2338673 : Blo 1557476 2338673 := bstep (se 2 (by rfl) ⟨877002, by rfl⟩ : syracuseStep 2338673 = 1754005) B1754005
theorem B3329905 : Blo 1557476 3329905 := bstep (se 2 (by rfl) ⟨1248714, by rfl⟩ : syracuseStep 3329905 = 2497429) B2497429
theorem B5263217 : Blo 1557476 5263217 := bstep (se 2 (by rfl) ⟨1973706, by rfl⟩ : syracuseStep 5263217 = 3947413) B3947413
theorem B2338691 : Blo 1557476 2338691 := bstep (se 1 (by rfl) ⟨1754018, by rfl⟩ : syracuseStep 2338691 = 3508037) B3508037
theorem B2338721 : Blo 1557476 2338721 := bstep (se 2 (by rfl) ⟨877020, by rfl⟩ : syracuseStep 2338721 = 1754041) B1754041
theorem B8875939 : Blo 1557476 8875939 := bstep (se 1 (by rfl) ⟨6656954, by rfl⟩ : syracuseStep 8875939 = 13313909) B13313909
theorem B2338739 : Blo 1557476 2338739 := bstep (se 1 (by rfl) ⟨1754054, by rfl⟩ : syracuseStep 2338739 = 3508109) B3508109
theorem B2338769 : Blo 1557476 2338769 := bstep (se 2 (by rfl) ⟨877038, by rfl⟩ : syracuseStep 2338769 = 1754077) B1754077
theorem B7892963 : Blo 1557476 7892963 := bstep (se 1 (by rfl) ⟨5919722, by rfl⟩ : syracuseStep 7892963 = 11839445) B11839445
theorem B2338787 : Blo 1557476 2338787 := bstep (se 1 (by rfl) ⟨1754090, by rfl⟩ : syracuseStep 2338787 = 3508181) B3508181
theorem B2338817 : Blo 1557476 2338817 := bstep (se 2 (by rfl) ⟨877056, by rfl⟩ : syracuseStep 2338817 = 1754113) B1754113
theorem B2338835 : Blo 1557476 2338835 := bstep (se 1 (by rfl) ⟨1754126, by rfl⟩ : syracuseStep 2338835 = 3508253) B3508253
theorem B3944497 : Blo 1557476 3944497 := bstep (se 2 (by rfl) ⟨1479186, by rfl⟩ : syracuseStep 3944497 = 2958373) B2958373
theorem B2338865 : Blo 1557476 2338865 := bstep (se 2 (by rfl) ⟨877074, by rfl⟩ : syracuseStep 2338865 = 1754149) B1754149
theorem B2338883 : Blo 1557476 2338883 := bstep (se 1 (by rfl) ⟨1754162, by rfl⟩ : syracuseStep 2338883 = 3508325) B3508325
theorem B2338913 : Blo 1557476 2338913 := bstep (se 2 (by rfl) ⟨877092, by rfl⟩ : syracuseStep 2338913 = 1754185) B1754185
theorem B2666611 : Blo 1557476 2666611 := bstep (se 1 (by rfl) ⟨1999958, by rfl⟩ : syracuseStep 2666611 = 3999917) B3999917
theorem B2338931 : Blo 1557476 2338931 := bstep (se 1 (by rfl) ⟨1754198, by rfl⟩ : syracuseStep 2338931 = 3508397) B3508397
theorem B2338961 : Blo 1557476 2338961 := bstep (se 2 (by rfl) ⟨877110, by rfl⟩ : syracuseStep 2338961 = 1754221) B1754221
theorem B1872019 : Blo 1557476 1872019 := bstep (se 1 (by rfl) ⟨1404014, by rfl⟩ : syracuseStep 1872019 = 2808029) B2808029
theorem B2338979 : Blo 1557476 2338979 := bstep (se 1 (by rfl) ⟨1754234, by rfl⟩ : syracuseStep 2338979 = 3508469) B3508469
theorem B2339009 : Blo 1557476 2339009 := bstep (se 2 (by rfl) ⟨877128, by rfl⟩ : syracuseStep 2339009 = 1754257) B1754257
theorem B21328069 : Blo 1557476 21328069 := bstep (se 4 (by rfl) ⟨1999506, by rfl⟩ : syracuseStep 21328069 = 3999013) B3999013
theorem B2339027 : Blo 1557476 2339027 := bstep (se 1 (by rfl) ⟨1754270, by rfl⟩ : syracuseStep 2339027 = 3508541) B3508541
theorem B17985763 : Blo 1557476 17985763 := bstep (se 1 (by rfl) ⟨13489322, by rfl⟩ : syracuseStep 17985763 = 26978645) B26978645
theorem B2339057 : Blo 1557476 2339057 := bstep (se 2 (by rfl) ⟨877146, by rfl⟩ : syracuseStep 2339057 = 1754293) B1754293
theorem B2339075 : Blo 1557476 2339075 := bstep (se 1 (by rfl) ⟨1754306, by rfl⟩ : syracuseStep 2339075 = 3508613) B3508613
theorem B11833613 : Blo 1557476 11833613 := bstep (se 3 (by rfl) ⟨2218802, by rfl⟩ : syracuseStep 11833613 = 4437605) B4437605
theorem B2339105 : Blo 1557476 2339105 := bstep (se 2 (by rfl) ⟨877164, by rfl⟩ : syracuseStep 2339105 = 1754329) B1754329
theorem B2339123 : Blo 1557476 2339123 := bstep (se 1 (by rfl) ⟨1754342, by rfl⟩ : syracuseStep 2339123 = 3508685) B3508685
theorem B3944771 : Blo 1557476 3944771 := bstep (se 1 (by rfl) ⟨2958578, by rfl⟩ : syracuseStep 3944771 = 5917157) B5917157
theorem B2339153 : Blo 1557476 2339153 := bstep (se 2 (by rfl) ⟨877182, by rfl⟩ : syracuseStep 2339153 = 1754365) B1754365
theorem B2339171 : Blo 1557476 2339171 := bstep (se 1 (by rfl) ⟨1754378, by rfl⟩ : syracuseStep 2339171 = 3508757) B3508757
theorem B2339201 : Blo 1557476 2339201 := bstep (se 2 (by rfl) ⟨877200, by rfl⟩ : syracuseStep 2339201 = 1754401) B1754401
theorem B8876465 : Blo 1557476 8876465 := bstep (se 2 (by rfl) ⟨3328674, by rfl⟩ : syracuseStep 8876465 = 6657349) B6657349
theorem B3944963 : Blo 1557476 3944963 := bstep (se 1 (by rfl) ⟨2958722, by rfl⟩ : syracuseStep 3944963 = 5917445) B5917445
theorem B9990661 : Blo 1557476 9990661 := bstep (se 4 (by rfl) ⟨936624, by rfl⟩ : syracuseStep 9990661 = 1873249) B1873249
theorem B2667043 : Blo 1557476 2667043 := bstep (se 1 (by rfl) ⟨2000282, by rfl⟩ : syracuseStep 2667043 = 4000565) B4000565
theorem B14979653 : Blo 1557476 14979653 := bstep (se 4 (by rfl) ⟨1404342, by rfl⟩ : syracuseStep 14979653 = 2808685) B2808685
theorem B4993741 : Blo 1557476 4993741 := bstep (se 3 (by rfl) ⟨936326, by rfl⟩ : syracuseStep 4993741 = 1872653) B1872653
theorem B7402211 : Blo 1557476 7402211 := bstep (se 1 (by rfl) ⟨5551658, by rfl⟩ : syracuseStep 7402211 = 11103317) B11103317
theorem B7893773 : Blo 1557476 7893773 := bstep (se 3 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 7893773 = 2960165) B2960165
theorem B4436785 : Blo 1557476 4436785 := bstep (se 2 (by rfl) ⟨1663794, by rfl⟩ : syracuseStep 4436785 = 3327589) B3327589
theorem B17756981 : Blo 1557476 17756981 := bstep (se 5 (by rfl) ⟨832358, by rfl⟩ : syracuseStep 17756981 = 1664717) B1664717
theorem B5919587 : Blo 1557476 5919587 := bstep (se 1 (by rfl) ⟨4439690, by rfl⟩ : syracuseStep 5919587 = 8879381) B8879381
theorem B13308785 : Blo 1557476 13308785 := bstep (se 2 (by rfl) ⟨4990794, by rfl⟩ : syracuseStep 13308785 = 9981589) B9981589
theorem B5919601 : Blo 1557476 5919601 := bstep (se 2 (by rfl) ⟨2219850, by rfl⟩ : syracuseStep 5919601 = 4439701) B4439701
theorem B9483277 : Blo 1557476 9483277 := bstep (se 3 (by rfl) ⟨1778114, by rfl⟩ : syracuseStep 9483277 = 3556229) B3556229
theorem B2495603 : Blo 1557476 2495603 := bstep (se 1 (by rfl) ⟨1871702, by rfl⟩ : syracuseStep 2495603 = 3743405) B3743405
theorem B4994243 : Blo 1557476 4994243 := bstep (se 1 (by rfl) ⟨3745682, by rfl⟩ : syracuseStep 4994243 = 7491365) B7491365
theorem B2495891 : Blo 1557476 2495891 := bstep (se 1 (by rfl) ⟨1871918, by rfl⟩ : syracuseStep 2495891 = 3743837) B3743837
theorem B3945905 : Blo 1557476 3945905 := bstep (se 2 (by rfl) ⟨1479714, by rfl⟩ : syracuseStep 3945905 = 2959429) B2959429
theorem B3945955 : Blo 1557476 3945955 := bstep (se 1 (by rfl) ⟨2959466, by rfl⟩ : syracuseStep 3945955 = 5918933) B5918933
theorem B7886321 : Blo 1557476 7886321 := bstep (se 2 (by rfl) ⟨2957370, by rfl⟩ : syracuseStep 7886321 = 5914741) B5914741
theorem B17085937 : Blo 1557476 17085937 := bstep (se 2 (by rfl) ⟨6407226, by rfl⟩ : syracuseStep 17085937 = 12814453) B12814453
theorem B9983587 : Blo 1557476 9983587 := bstep (se 1 (by rfl) ⟨7487690, by rfl⟩ : syracuseStep 9983587 = 14975381) B14975381
theorem B3946097 : Blo 1557476 3946097 := bstep (se 2 (by rfl) ⟨1479786, by rfl⟩ : syracuseStep 3946097 = 2959573) B2959573
theorem B5256845 : Blo 1557476 5256845 := bstep (se 3 (by rfl) ⟨985658, by rfl⟩ : syracuseStep 5256845 = 1971317) B1971317
theorem B1971859 : Blo 1557476 1971859 := bstep (se 1 (by rfl) ⟨1478894, by rfl⟩ : syracuseStep 1971859 = 2957789) B2957789
theorem B5256899 : Blo 1557476 5256899 := bstep (se 1 (by rfl) ⟨3942674, by rfl⟩ : syracuseStep 5256899 = 7885349) B7885349
theorem B1971955 : Blo 1557476 1971955 := bstep (se 1 (by rfl) ⟨1478966, by rfl⟩ : syracuseStep 1971955 = 2957933) B2957933
theorem B3159811 : Blo 1557476 3159811 := bstep (se 1 (by rfl) ⟨2369858, by rfl⟩ : syracuseStep 3159811 = 4739717) B4739717
theorem B2496307 : Blo 1557476 2496307 := bstep (se 1 (by rfl) ⟨1872230, by rfl⟩ : syracuseStep 2496307 = 3744461) B3744461
theorem B14219077 : Blo 1557476 14219077 := bstep (se 4 (by rfl) ⟨1333038, by rfl⟩ : syracuseStep 14219077 = 2666077) B2666077
theorem B8877923 : Blo 1557476 8877923 := bstep (se 1 (by rfl) ⟨6658442, by rfl⟩ : syracuseStep 8877923 = 13316885) B13316885
theorem B5257169 : Blo 1557476 5257169 := bstep (se 2 (by rfl) ⟨1971438, by rfl⟩ : syracuseStep 5257169 = 3942877) B3942877
theorem B2217937 : Blo 1557476 2217937 := bstep (se 2 (by rfl) ⟨831726, by rfl⟩ : syracuseStep 2217937 = 1663453) B1663453
theorem B4438061 : Blo 1557476 4438061 := bstep (se 3 (by rfl) ⟨832136, by rfl⟩ : syracuseStep 4438061 = 1664273) B1664273
theorem B28440629 : Blo 1557476 28440629 := bstep (se 5 (by rfl) ⟨1333154, by rfl⟩ : syracuseStep 28440629 = 2666309) B2666309
theorem B2496577 : Blo 1557476 2496577 := bstep (se 2 (by rfl) ⟨936216, by rfl⟩ : syracuseStep 2496577 = 1872433) B1872433
theorem B2218051 : Blo 1557476 2218051 := bstep (se 1 (by rfl) ⟨1663538, by rfl⟩ : syracuseStep 2218051 = 3327077) B3327077
theorem B9484451 : Blo 1557476 9484451 := bstep (se 1 (by rfl) ⟨7113338, by rfl⟩ : syracuseStep 9484451 = 14226677) B14226677
theorem B1972451 : Blo 1557476 1972451 := bstep (se 1 (by rfl) ⟨1479338, by rfl⟩ : syracuseStep 1972451 = 2958677) B2958677
theorem B4438243 : Blo 1557476 4438243 := bstep (se 1 (by rfl) ⟨3328682, by rfl⟩ : syracuseStep 4438243 = 6657365) B6657365
theorem B3504401 : Blo 1557476 3504401 := bstep (se 2 (by rfl) ⟨1314150, by rfl⟩ : syracuseStep 3504401 = 2628301) B2628301
theorem B4438289 : Blo 1557476 4438289 := bstep (se 2 (by rfl) ⟨1664358, by rfl⟩ : syracuseStep 4438289 = 3328717) B3328717
theorem B3504419 : Blo 1557476 3504419 := bstep (se 1 (by rfl) ⟨2628314, by rfl⟩ : syracuseStep 3504419 = 5256629) B5256629
theorem B5921059 : Blo 1557476 5921059 := bstep (se 1 (by rfl) ⟨4440794, by rfl⟩ : syracuseStep 5921059 = 8881589) B8881589
theorem B2496833 : Blo 1557476 2496833 := bstep (se 2 (by rfl) ⟨936312, by rfl⟩ : syracuseStep 2496833 = 1872625) B1872625
theorem B2529665 : Blo 1557476 2529665 := bstep (se 2 (by rfl) ⟨948624, by rfl⟩ : syracuseStep 2529665 = 1897249) B1897249
theorem B4741517 : Blo 1557476 4741517 := bstep (se 3 (by rfl) ⟨889034, by rfl⟩ : syracuseStep 4741517 = 1778069) B1778069
theorem B5257709 : Blo 1557476 5257709 := bstep (se 3 (by rfl) ⟨985820, by rfl⟩ : syracuseStep 5257709 = 1971641) B1971641
theorem B3742193 : Blo 1557476 3742193 := bstep (se 2 (by rfl) ⟨1403322, by rfl⟩ : syracuseStep 3742193 = 2806645) B2806645
theorem B4995587 : Blo 1557476 4995587 := bstep (se 1 (by rfl) ⟨3746690, by rfl⟩ : syracuseStep 4995587 = 7493381) B7493381
theorem B5257763 : Blo 1557476 5257763 := bstep (se 1 (by rfl) ⟨3943322, by rfl⟩ : syracuseStep 5257763 = 7886645) B7886645
theorem B6658595 : Blo 1557476 6658595 := bstep (se 1 (by rfl) ⟨4993946, by rfl⟩ : syracuseStep 6658595 = 9987893) B9987893
theorem B3504689 : Blo 1557476 3504689 := bstep (se 2 (by rfl) ⟨1314258, by rfl⟩ : syracuseStep 3504689 = 2628517) B2628517
theorem B3504707 : Blo 1557476 3504707 := bstep (se 1 (by rfl) ⟨2628530, by rfl⟩ : syracuseStep 3504707 = 5257061) B5257061
theorem B11827781 : Blo 1557476 11827781 := bstep (se 4 (by rfl) ⟨1108854, by rfl⟩ : syracuseStep 11827781 = 2217709) B2217709
theorem B3947089 : Blo 1557476 3947089 := bstep (se 2 (by rfl) ⟨1480158, by rfl⟩ : syracuseStep 3947089 = 2960317) B2960317
theorem B2628355 : Blo 1557476 2628355 := bstep (se 1 (by rfl) ⟨1971266, by rfl⟩ : syracuseStep 2628355 = 3942533) B3942533
theorem B3742481 : Blo 1557476 3742481 := bstep (se 2 (by rfl) ⟨1403430, by rfl⟩ : syracuseStep 3742481 = 2806861) B2806861
theorem B3373841 : Blo 1557476 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B5258033 : Blo 1557476 5258033 := bstep (se 2 (by rfl) ⟨1971762, by rfl⟩ : syracuseStep 5258033 = 3943525) B3943525
theorem B3504977 : Blo 1557476 3504977 := bstep (se 2 (by rfl) ⟨1314366, by rfl⟩ : syracuseStep 3504977 = 2628733) B2628733
theorem B3504995 : Blo 1557476 3504995 := bstep (se 1 (by rfl) ⟨2628746, by rfl⟩ : syracuseStep 3504995 = 5257493) B5257493
theorem B7486307 : Blo 1557476 7486307 := bstep (se 1 (by rfl) ⟨5614730, by rfl⟩ : syracuseStep 7486307 = 11229461) B11229461
theorem B3947363 : Blo 1557476 3947363 := bstep (se 1 (by rfl) ⟨2960522, by rfl⟩ : syracuseStep 3947363 = 5921045) B5921045
theorem B18963341 : Blo 1557476 18963341 := bstep (se 3 (by rfl) ⟨3555626, by rfl⟩ : syracuseStep 18963341 = 7111253) B7111253
theorem B2628497 : Blo 1557476 2628497 := bstep (se 2 (by rfl) ⟨985686, by rfl⟩ : syracuseStep 2628497 = 1971373) B1971373
theorem B7887779 : Blo 1557476 7887779 := bstep (se 1 (by rfl) ⟨5915834, by rfl⟩ : syracuseStep 7887779 = 11831669) B11831669
theorem B1973155 : Blo 1557476 1973155 := bstep (se 1 (by rfl) ⟨1479866, by rfl⟩ : syracuseStep 1973155 = 2959733) B2959733
theorem B2497537 : Blo 1557476 2497537 := bstep (se 2 (by rfl) ⟨936576, by rfl⟩ : syracuseStep 2497537 = 1873153) B1873153
theorem B1973251 : Blo 1557476 1973251 := bstep (se 1 (by rfl) ⟨1479938, by rfl⟩ : syracuseStep 1973251 = 2959877) B2959877
theorem B2628625 : Blo 1557476 2628625 := bstep (se 2 (by rfl) ⟨985734, by rfl⟩ : syracuseStep 2628625 = 1971469) B1971469
theorem B2628659 : Blo 1557476 2628659 := bstep (se 1 (by rfl) ⟨1971494, by rfl⟩ : syracuseStep 2628659 = 3942989) B3942989
theorem B3505265 : Blo 1557476 3505265 := bstep (se 2 (by rfl) ⟨1314474, by rfl⟩ : syracuseStep 3505265 = 2628949) B2628949
theorem B11836529 : Blo 1557476 11836529 := bstep (se 2 (by rfl) ⟨4438698, by rfl⟩ : syracuseStep 11836529 = 8877397) B8877397
theorem B3505283 : Blo 1557476 3505283 := bstep (se 1 (by rfl) ⟨2628962, by rfl⟩ : syracuseStep 3505283 = 5257925) B5257925
theorem B2628787 : Blo 1557476 2628787 := bstep (se 1 (by rfl) ⟨1971590, by rfl⟩ : syracuseStep 2628787 = 3943181) B3943181
theorem B1752259 : Blo 1557476 1752259 := bstep (se 1 (by rfl) ⟨1314194, by rfl⟩ : syracuseStep 1752259 = 2628389) B2628389
theorem B18963725 : Blo 1557476 18963725 := bstep (se 3 (by rfl) ⟨3555698, by rfl⟩ : syracuseStep 18963725 = 7111397) B7111397
theorem B7486769 : Blo 1557476 7486769 := bstep (se 2 (by rfl) ⟨2807538, by rfl⟩ : syracuseStep 7486769 = 5615077) B5615077
theorem B2628929 : Blo 1557476 2628929 := bstep (se 2 (by rfl) ⟨985848, by rfl⟩ : syracuseStep 2628929 = 1971697) B1971697
theorem B5258573 : Blo 1557476 5258573 := bstep (se 3 (by rfl) ⟨985982, by rfl⟩ : syracuseStep 5258573 = 1971965) B1971965
theorem B1752403 : Blo 1557476 1752403 := bstep (se 1 (by rfl) ⟨1314302, by rfl⟩ : syracuseStep 1752403 = 2628605) B2628605
theorem B14974307 : Blo 1557476 14974307 := bstep (se 1 (by rfl) ⟨11230730, by rfl⟩ : syracuseStep 14974307 = 22461461) B22461461
theorem B5258627 : Blo 1557476 5258627 := bstep (se 1 (by rfl) ⟨3943970, by rfl⟩ : syracuseStep 5258627 = 7887941) B7887941
theorem B2219395 : Blo 1557476 2219395 := bstep (se 1 (by rfl) ⟨1664546, by rfl⟩ : syracuseStep 2219395 = 3329093) B3329093
theorem B3505553 : Blo 1557476 3505553 := bstep (se 2 (by rfl) ⟨1314582, by rfl⟩ : syracuseStep 3505553 = 2629165) B2629165
theorem B3505571 : Blo 1557476 3505571 := bstep (se 1 (by rfl) ⟨2629178, by rfl⟩ : syracuseStep 3505571 = 5258357) B5258357
theorem B2629057 : Blo 1557476 2629057 := bstep (se 2 (by rfl) ⟨985896, by rfl⟩ : syracuseStep 2629057 = 1971793) B1971793
theorem B2997713 : Blo 1557476 2997713 := bstep (se 2 (by rfl) ⟨1124142, by rfl⟩ : syracuseStep 2997713 = 2248285) B2248285
theorem B1752547 : Blo 1557476 1752547 := bstep (se 1 (by rfl) ⟨1314410, by rfl⟩ : syracuseStep 1752547 = 2628821) B2628821
theorem B14212579 : Blo 1557476 14212579 := bstep (se 1 (by rfl) ⟨10659434, by rfl⟩ : syracuseStep 14212579 = 21318869) B21318869
theorem B2629091 : Blo 1557476 2629091 := bstep (se 1 (by rfl) ⟨1971818, by rfl⟩ : syracuseStep 2629091 = 3943637) B3943637
theorem B2956817 : Blo 1557476 2956817 := bstep (se 2 (by rfl) ⟨1108806, by rfl⟩ : syracuseStep 2956817 = 2217613) B2217613
theorem B2629219 : Blo 1557476 2629219 := bstep (se 1 (by rfl) ⟨1971914, by rfl⟩ : syracuseStep 2629219 = 3943829) B3943829
theorem B1752691 : Blo 1557476 1752691 := bstep (se 1 (by rfl) ⟨1314518, by rfl⟩ : syracuseStep 1752691 = 2629037) B2629037
theorem B8871565 : Blo 1557476 8871565 := bstep (se 3 (by rfl) ⟨1663418, by rfl⟩ : syracuseStep 8871565 = 3326837) B3326837
theorem B5258897 : Blo 1557476 5258897 := bstep (se 2 (by rfl) ⟨1972086, by rfl⟩ : syracuseStep 5258897 = 3944173) B3944173
theorem B3505841 : Blo 1557476 3505841 := bstep (se 2 (by rfl) ⟨1314690, by rfl⟩ : syracuseStep 3505841 = 2629381) B2629381
theorem B3505859 : Blo 1557476 3505859 := bstep (se 1 (by rfl) ⟨2629394, by rfl⟩ : syracuseStep 3505859 = 5258789) B5258789
theorem B4439747 : Blo 1557476 4439747 := bstep (se 1 (by rfl) ⟨3329810, by rfl⟩ : syracuseStep 4439747 = 6659621) B6659621
theorem B8879813 : Blo 1557476 8879813 := bstep (se 4 (by rfl) ⟨832482, by rfl⟩ : syracuseStep 8879813 = 1664965) B1664965
theorem B7888589 : Blo 1557476 7888589 := bstep (se 3 (by rfl) ⟨1479110, by rfl⟩ : syracuseStep 7888589 = 2958221) B2958221
theorem B2629361 : Blo 1557476 2629361 := bstep (se 2 (by rfl) ⟨986010, by rfl⟩ : syracuseStep 2629361 = 1972021) B1972021
theorem B1752835 : Blo 1557476 1752835 := bstep (se 1 (by rfl) ⟨1314626, by rfl⟩ : syracuseStep 1752835 = 2629253) B2629253
theorem B2629489 : Blo 1557476 2629489 := bstep (se 2 (by rfl) ⟨986058, by rfl⟩ : syracuseStep 2629489 = 1972117) B1972117
theorem B2809745 : Blo 1557476 2809745 := bstep (se 2 (by rfl) ⟨1053654, by rfl⟩ : syracuseStep 2809745 = 2107309) B2107309
theorem B1752979 : Blo 1557476 1752979 := bstep (se 1 (by rfl) ⟨1314734, by rfl⟩ : syracuseStep 1752979 = 2629469) B2629469
theorem B2629523 : Blo 1557476 2629523 := bstep (se 1 (by rfl) ⟨1972142, by rfl⟩ : syracuseStep 2629523 = 3944285) B3944285
theorem B2957219 : Blo 1557476 2957219 := bstep (se 1 (by rfl) ⟨2217914, by rfl⟩ : syracuseStep 2957219 = 4435829) B4435829
theorem B3506129 : Blo 1557476 3506129 := bstep (se 2 (by rfl) ⟨1314798, by rfl⟩ : syracuseStep 3506129 = 2629597) B2629597
theorem B3555281 : Blo 1557476 3555281 := bstep (se 2 (by rfl) ⟨1333230, by rfl⟩ : syracuseStep 3555281 = 2666461) B2666461
theorem B3506147 : Blo 1557476 3506147 := bstep (se 1 (by rfl) ⟨2629610, by rfl⟩ : syracuseStep 3506147 = 5259221) B5259221
theorem B13320197 : Blo 1557476 13320197 := bstep (se 4 (by rfl) ⟨1248768, by rfl⟩ : syracuseStep 13320197 = 2497537) B2497537
theorem B7888913 : Blo 1557476 7888913 := bstep (se 2 (by rfl) ⟨2958342, by rfl⟩ : syracuseStep 7888913 = 5916685) B5916685
theorem B3506201 : Blo 1557476 3506201 := bstep (se 2 (by rfl) ⟨1314825, by rfl⟩ : syracuseStep 3506201 = 2629651) B2629651
theorem B5259329 : Blo 1557476 5259329 := bstep (se 2 (by rfl) ⟨1972248, by rfl⟩ : syracuseStep 5259329 = 3944497) B3944497
theorem B2957401 : Blo 1557476 2957401 := bstep (se 2 (by rfl) ⟨1109025, by rfl⟩ : syracuseStep 2957401 = 2218051) B2218051
theorem B1753195 : Blo 1557476 1753195 := bstep (se 1 (by rfl) ⟨1314896, by rfl⟩ : syracuseStep 1753195 = 2629793) B2629793
theorem B3506291 : Blo 1557476 3506291 := bstep (se 1 (by rfl) ⟨2629718, by rfl⟩ : syracuseStep 3506291 = 5259437) B5259437
theorem B3506327 : Blo 1557476 3506327 := bstep (se 1 (by rfl) ⟨2629745, by rfl⟩ : syracuseStep 3506327 = 5259491) B5259491
theorem B21332119 : Blo 1557476 21332119 := bstep (se 1 (by rfl) ⟨15999089, by rfl⟩ : syracuseStep 21332119 = 31998179) B31998179
theorem B7889075 : Blo 1557476 7889075 := bstep (se 1 (by rfl) ⟨5916806, by rfl⟩ : syracuseStep 7889075 = 11833613) B11833613
theorem B2629847 : Blo 1557476 2629847 := bstep (se 1 (by rfl) ⟨1972385, by rfl⟩ : syracuseStep 2629847 = 3944771) B3944771
theorem B1753303 : Blo 1557476 1753303 := bstep (se 1 (by rfl) ⟨1314977, by rfl⟩ : syracuseStep 1753303 = 2629955) B2629955
theorem B14410001 : Blo 1557476 14410001 := bstep (se 2 (by rfl) ⟨5403750, by rfl⟩ : syracuseStep 14410001 = 10807501) B10807501
theorem B3506507 : Blo 1557476 3506507 := bstep (se 1 (by rfl) ⟨2629880, by rfl⟩ : syracuseStep 3506507 = 5259761) B5259761
theorem B2629975 : Blo 1557476 2629975 := bstep (se 1 (by rfl) ⟨1972481, by rfl⟩ : syracuseStep 2629975 = 3944963) B3944963
theorem B3506561 : Blo 1557476 3506561 := bstep (se 2 (by rfl) ⟨1314960, by rfl⟩ : syracuseStep 3506561 = 2629921) B2629921
theorem B9986435 : Blo 1557476 9986435 := bstep (se 1 (by rfl) ⟨7489826, by rfl⟩ : syracuseStep 9986435 = 14979653) B14979653
theorem B1753483 : Blo 1557476 1753483 := bstep (se 1 (by rfl) ⟨1315112, by rfl⟩ : syracuseStep 1753483 = 2630225) B2630225
theorem B7487923 : Blo 1557476 7487923 := bstep (se 1 (by rfl) ⟨5615942, by rfl⟩ : syracuseStep 7487923 = 11231885) B11231885
theorem B4800971 : Blo 1557476 4800971 := bstep (se 1 (by rfl) ⟨3600728, by rfl⟩ : syracuseStep 4800971 = 7201457) B7201457
theorem B1753591 : Blo 1557476 1753591 := bstep (se 1 (by rfl) ⟨1315193, by rfl⟩ : syracuseStep 1753591 = 2630387) B2630387
theorem B11837987 : Blo 1557476 11837987 := bstep (se 1 (by rfl) ⟨8878490, by rfl⟩ : syracuseStep 11837987 = 17756981) B17756981
theorem B8872523 : Blo 1557476 8872523 := bstep (se 1 (by rfl) ⟨6654392, by rfl⟩ : syracuseStep 8872523 = 13308785) B13308785
theorem B3506777 : Blo 1557476 3506777 := bstep (se 2 (by rfl) ⟨1315041, by rfl⟩ : syracuseStep 3506777 = 2630083) B2630083
theorem B5259869 : Blo 1557476 5259869 := bstep (se 3 (by rfl) ⟨986225, by rfl⟩ : syracuseStep 5259869 = 1972451) B1972451
theorem B14221925 : Blo 1557476 14221925 := bstep (se 4 (by rfl) ⟨1333305, by rfl⟩ : syracuseStep 14221925 = 2666611) B2666611
theorem B3555991 : Blo 1557476 3555991 := bstep (se 1 (by rfl) ⟨2666993, by rfl⟩ : syracuseStep 3555991 = 5333987) B5333987
theorem B1753771 : Blo 1557476 1753771 := bstep (se 1 (by rfl) ⟨1315328, by rfl⟩ : syracuseStep 1753771 = 2630657) B2630657
theorem B13320881 : Blo 1557476 13320881 := bstep (se 2 (by rfl) ⟨4995330, by rfl⟩ : syracuseStep 13320881 = 9990661) B9990661
theorem B3506867 : Blo 1557476 3506867 := bstep (se 1 (by rfl) ⟨2630150, by rfl⟩ : syracuseStep 3506867 = 5260301) B5260301
theorem B50569933 : Blo 1557476 50569933 := bstep (se 3 (by rfl) ⟨9481862, by rfl⟩ : syracuseStep 50569933 = 18963725) B18963725
theorem B3506903 : Blo 1557476 3506903 := bstep (se 1 (by rfl) ⟨2630177, by rfl⟩ : syracuseStep 3506903 = 5260355) B5260355
theorem B3556057 : Blo 1557476 3556057 := bstep (se 2 (by rfl) ⟨1333521, by rfl⟩ : syracuseStep 3556057 = 2667043) B2667043
theorem B1663735 : Blo 1557476 1663735 := bstep (se 1 (by rfl) ⟨1247801, by rfl⟩ : syracuseStep 1663735 = 2495603) B2495603
theorem B1753879 : Blo 1557476 1753879 := bstep (se 1 (by rfl) ⟨1315409, by rfl⟩ : syracuseStep 1753879 = 2630819) B2630819
theorem B3507083 : Blo 1557476 3507083 := bstep (se 1 (by rfl) ⟨2630312, by rfl⟩ : syracuseStep 3507083 = 5260625) B5260625
theorem B34145201 : Blo 1557476 34145201 := bstep (se 2 (by rfl) ⟨12804450, by rfl⟩ : syracuseStep 34145201 = 25608901) B25608901
theorem B3507137 : Blo 1557476 3507137 := bstep (se 2 (by rfl) ⟨1315176, by rfl⟩ : syracuseStep 3507137 = 2630353) B2630353
theorem B3326923 : Blo 1557476 3326923 := bstep (se 1 (by rfl) ⟨2495192, by rfl⟩ : syracuseStep 3326923 = 4990385) B4990385
theorem B2630603 : Blo 1557476 2630603 := bstep (se 1 (by rfl) ⟨1972952, by rfl⟩ : syracuseStep 2630603 = 3945905) B3945905
theorem B1754059 : Blo 1557476 1754059 := bstep (se 1 (by rfl) ⟨1315544, by rfl⟩ : syracuseStep 1754059 = 2631089) B2631089
theorem B1557483 : Blo 1557476 1557483 := bstep (se 1 (by rfl) ⟨1168112, by rfl⟩ : syracuseStep 1557483 = 2336225) B2336225
theorem B1557495 : Blo 1557476 1557495 := bstep (se 1 (by rfl) ⟨1168121, by rfl⟩ : syracuseStep 1557495 = 2336243) B2336243
theorem B1557515 : Blo 1557476 1557515 := bstep (se 1 (by rfl) ⟨1168136, by rfl⟩ : syracuseStep 1557515 = 2336273) B2336273
theorem B1557527 : Blo 1557476 1557527 := bstep (se 1 (by rfl) ⟨1168145, by rfl⟩ : syracuseStep 1557527 = 2336291) B2336291
theorem B1557547 : Blo 1557476 1557547 := bstep (se 1 (by rfl) ⟨1168160, by rfl⟩ : syracuseStep 1557547 = 2336321) B2336321
theorem B5915699 : Blo 1557476 5915699 := bstep (se 1 (by rfl) ⟨4436774, by rfl⟩ : syracuseStep 5915699 = 8873549) B8873549
theorem B1557559 : Blo 1557476 1557559 := bstep (se 1 (by rfl) ⟨1168169, by rfl⟩ : syracuseStep 1557559 = 2336339) B2336339
theorem B1754167 : Blo 1557476 1754167 := bstep (se 1 (by rfl) ⟨1315625, by rfl⟩ : syracuseStep 1754167 = 2631251) B2631251
theorem B5915713 : Blo 1557476 5915713 := bstep (se 2 (by rfl) ⟨2218392, by rfl⟩ : syracuseStep 5915713 = 4436785) B4436785
theorem B50521157 : Blo 1557476 50521157 := bstep (se 4 (by rfl) ⟨4736358, by rfl⟩ : syracuseStep 50521157 = 9472717) B9472717
theorem B26633285 : Blo 1557476 26633285 := bstep (se 4 (by rfl) ⟨2496870, by rfl⟩ : syracuseStep 26633285 = 4993741) B4993741
theorem B1557579 : Blo 1557476 1557579 := bstep (se 1 (by rfl) ⟨1168184, by rfl⟩ : syracuseStep 1557579 = 2336369) B2336369
theorem B2630731 : Blo 1557476 2630731 := bstep (se 1 (by rfl) ⟨1973048, by rfl⟩ : syracuseStep 2630731 = 3946097) B3946097
theorem B17761355 : Blo 1557476 17761355 := bstep (se 1 (by rfl) ⟨13321016, by rfl⟩ : syracuseStep 17761355 = 26642033) B26642033
theorem B1557591 : Blo 1557476 1557591 := bstep (se 1 (by rfl) ⟨1168193, by rfl⟩ : syracuseStep 1557591 = 2336387) B2336387
theorem B1557611 : Blo 1557476 1557611 := bstep (se 1 (by rfl) ⟨1168208, by rfl⟩ : syracuseStep 1557611 = 2336417) B2336417
theorem B1557623 : Blo 1557476 1557623 := bstep (se 1 (by rfl) ⟨1168217, by rfl⟩ : syracuseStep 1557623 = 2336435) B2336435
theorem B1557643 : Blo 1557476 1557643 := bstep (se 1 (by rfl) ⟨1168232, by rfl⟩ : syracuseStep 1557643 = 2336465) B2336465
theorem B1557655 : Blo 1557476 1557655 := bstep (se 1 (by rfl) ⟨1168241, by rfl⟩ : syracuseStep 1557655 = 2336483) B2336483
theorem B3507353 : Blo 1557476 3507353 := bstep (se 2 (by rfl) ⟨1315257, by rfl⟩ : syracuseStep 3507353 = 2630515) B2630515
theorem B1557675 : Blo 1557476 1557675 := bstep (se 1 (by rfl) ⟨1168256, by rfl⟩ : syracuseStep 1557675 = 2336513) B2336513
theorem B1557687 : Blo 1557476 1557687 := bstep (se 1 (by rfl) ⟨1168265, by rfl⟩ : syracuseStep 1557687 = 2336531) B2336531
theorem B1557707 : Blo 1557476 1557707 := bstep (se 1 (by rfl) ⟨1168280, by rfl⟩ : syracuseStep 1557707 = 2336561) B2336561
theorem B1557719 : Blo 1557476 1557719 := bstep (se 1 (by rfl) ⟨1168289, by rfl⟩ : syracuseStep 1557719 = 2336579) B2336579
theorem B2630873 : Blo 1557476 2630873 := bstep (se 2 (by rfl) ⟨986577, by rfl⟩ : syracuseStep 2630873 = 1973155) B1973155
theorem B1557739 : Blo 1557476 1557739 := bstep (se 1 (by rfl) ⟨1168304, by rfl⟩ : syracuseStep 1557739 = 2336609) B2336609
theorem B1754347 : Blo 1557476 1754347 := bstep (se 1 (by rfl) ⟨1315760, by rfl⟩ : syracuseStep 1754347 = 2631521) B2631521
theorem B3507443 : Blo 1557476 3507443 := bstep (se 1 (by rfl) ⟨2630582, by rfl⟩ : syracuseStep 3507443 = 5261165) B5261165
theorem B1557751 : Blo 1557476 1557751 := bstep (se 1 (by rfl) ⟨1168313, by rfl⟩ : syracuseStep 1557751 = 2336627) B2336627
theorem B1557771 : Blo 1557476 1557771 := bstep (se 1 (by rfl) ⟨1168328, by rfl⟩ : syracuseStep 1557771 = 2336657) B2336657
theorem B1557783 : Blo 1557476 1557783 := bstep (se 1 (by rfl) ⟨1168337, by rfl⟩ : syracuseStep 1557783 = 2336675) B2336675
theorem B3507479 : Blo 1557476 3507479 := bstep (se 1 (by rfl) ⟨2630609, by rfl⟩ : syracuseStep 3507479 = 5261219) B5261219
theorem B1557803 : Blo 1557476 1557803 := bstep (se 1 (by rfl) ⟨1168352, by rfl⟩ : syracuseStep 1557803 = 2336705) B2336705
theorem B1557815 : Blo 1557476 1557815 := bstep (se 1 (by rfl) ⟨1168361, by rfl⟩ : syracuseStep 1557815 = 2336723) B2336723
theorem B6653249 : Blo 1557476 6653249 := bstep (se 2 (by rfl) ⟨2494968, by rfl⟩ : syracuseStep 6653249 = 4989937) B4989937
theorem B1557835 : Blo 1557476 1557835 := bstep (se 1 (by rfl) ⟨1168376, by rfl⟩ : syracuseStep 1557835 = 2336753) B2336753
theorem B1557847 : Blo 1557476 1557847 := bstep (se 1 (by rfl) ⟨1168385, by rfl⟩ : syracuseStep 1557847 = 2336771) B2336771
theorem B2631001 : Blo 1557476 2631001 := bstep (se 2 (by rfl) ⟨986625, by rfl⟩ : syracuseStep 2631001 = 1973251) B1973251
theorem B1557867 : Blo 1557476 1557867 := bstep (se 1 (by rfl) ⟨1168400, by rfl⟩ : syracuseStep 1557867 = 2336801) B2336801
theorem B2958707 : Blo 1557476 2958707 := bstep (se 1 (by rfl) ⟨2219030, by rfl⟩ : syracuseStep 2958707 = 4438061) B4438061
theorem B1557879 : Blo 1557476 1557879 := bstep (se 1 (by rfl) ⟨1168409, by rfl⟩ : syracuseStep 1557879 = 2336819) B2336819
theorem B8422787 : Blo 1557476 8422787 := bstep (se 1 (by rfl) ⟨6317090, by rfl⟩ : syracuseStep 8422787 = 12634181) B12634181
theorem B1557899 : Blo 1557476 1557899 := bstep (se 1 (by rfl) ⟨1168424, by rfl⟩ : syracuseStep 1557899 = 2336849) B2336849
theorem B1557911 : Blo 1557476 1557911 := bstep (se 1 (by rfl) ⟨1168433, by rfl⟩ : syracuseStep 1557911 = 2336867) B2336867
theorem B1557931 : Blo 1557476 1557931 := bstep (se 1 (by rfl) ⟨1168448, by rfl⟩ : syracuseStep 1557931 = 2336897) B2336897
theorem B1557943 : Blo 1557476 1557943 := bstep (se 1 (by rfl) ⟨1168457, by rfl⟩ : syracuseStep 1557943 = 2336915) B2336915
theorem B1557963 : Blo 1557476 1557963 := bstep (se 1 (by rfl) ⟨1168472, by rfl⟩ : syracuseStep 1557963 = 2336945) B2336945
theorem B3507659 : Blo 1557476 3507659 := bstep (se 1 (by rfl) ⟨2630744, by rfl⟩ : syracuseStep 3507659 = 5261489) B5261489
theorem B1557975 : Blo 1557476 1557975 := bstep (se 1 (by rfl) ⟨1168481, by rfl⟩ : syracuseStep 1557975 = 2336963) B2336963
theorem B1557995 : Blo 1557476 1557995 := bstep (se 1 (by rfl) ⟨1168496, by rfl⟩ : syracuseStep 1557995 = 2336993) B2336993
theorem B1558007 : Blo 1557476 1558007 := bstep (se 1 (by rfl) ⟨1168505, by rfl⟩ : syracuseStep 1558007 = 2337011) B2337011
theorem B3507713 : Blo 1557476 3507713 := bstep (se 2 (by rfl) ⟨1315392, by rfl⟩ : syracuseStep 3507713 = 2630785) B2630785
theorem B2336267 : Blo 1557476 2336267 := bstep (se 1 (by rfl) ⟨1752200, by rfl⟩ : syracuseStep 2336267 = 3504401) B3504401
theorem B1558027 : Blo 1557476 1558027 := bstep (se 1 (by rfl) ⟨1168520, by rfl⟩ : syracuseStep 1558027 = 2337041) B2337041
theorem B2958859 : Blo 1557476 2958859 := bstep (se 1 (by rfl) ⟨2219144, by rfl⟩ : syracuseStep 2958859 = 4438289) B4438289
theorem B2336279 : Blo 1557476 2336279 := bstep (se 1 (by rfl) ⟨1752209, by rfl⟩ : syracuseStep 2336279 = 3504419) B3504419
theorem B1558039 : Blo 1557476 1558039 := bstep (se 1 (by rfl) ⟨1168529, by rfl⟩ : syracuseStep 1558039 = 2337059) B2337059
theorem B1558059 : Blo 1557476 1558059 := bstep (se 1 (by rfl) ⟨1168544, by rfl⟩ : syracuseStep 1558059 = 2337089) B2337089
theorem B1664555 : Blo 1557476 1664555 := bstep (se 1 (by rfl) ⟨1248416, by rfl⟩ : syracuseStep 1664555 = 2496833) B2496833
theorem B1558071 : Blo 1557476 1558071 := bstep (se 1 (by rfl) ⟨1168553, by rfl⟩ : syracuseStep 1558071 = 2337107) B2337107
theorem B1558091 : Blo 1557476 1558091 := bstep (se 1 (by rfl) ⟨1168568, by rfl⟩ : syracuseStep 1558091 = 2337137) B2337137
theorem B1558103 : Blo 1557476 1558103 := bstep (se 1 (by rfl) ⟨1168577, by rfl⟩ : syracuseStep 1558103 = 2337155) B2337155
theorem B2336345 : Blo 1557476 2336345 := bstep (se 2 (by rfl) ⟨876129, by rfl⟩ : syracuseStep 2336345 = 1752259) B1752259
theorem B1558123 : Blo 1557476 1558123 := bstep (se 1 (by rfl) ⟨1168592, by rfl⟩ : syracuseStep 1558123 = 2337185) B2337185
theorem B1558135 : Blo 1557476 1558135 := bstep (se 1 (by rfl) ⟨1168601, by rfl⟩ : syracuseStep 1558135 = 2337203) B2337203
theorem B1558155 : Blo 1557476 1558155 := bstep (se 1 (by rfl) ⟨1168616, by rfl⟩ : syracuseStep 1558155 = 2337233) B2337233
theorem B1558167 : Blo 1557476 1558167 := bstep (se 1 (by rfl) ⟨1168625, by rfl⟩ : syracuseStep 1558167 = 2337251) B2337251
theorem B1558187 : Blo 1557476 1558187 := bstep (se 1 (by rfl) ⟨1168640, by rfl⟩ : syracuseStep 1558187 = 2337281) B2337281
theorem B13321907 : Blo 1557476 13321907 := bstep (se 1 (by rfl) ⟨9991430, by rfl⟩ : syracuseStep 13321907 = 19982861) B19982861
theorem B1558199 : Blo 1557476 1558199 := bstep (se 1 (by rfl) ⟨1168649, by rfl⟩ : syracuseStep 1558199 = 2337299) B2337299
theorem B2336459 : Blo 1557476 2336459 := bstep (se 1 (by rfl) ⟨1752344, by rfl⟩ : syracuseStep 2336459 = 3504689) B3504689
theorem B1558219 : Blo 1557476 1558219 := bstep (se 1 (by rfl) ⟨1168664, by rfl⟩ : syracuseStep 1558219 = 2337329) B2337329
theorem B5261003 : Blo 1557476 5261003 := bstep (se 1 (by rfl) ⟨3945752, by rfl⟩ : syracuseStep 5261003 = 7891505) B7891505
theorem B2336471 : Blo 1557476 2336471 := bstep (se 1 (by rfl) ⟨1752353, by rfl⟩ : syracuseStep 2336471 = 3504707) B3504707
theorem B1558231 : Blo 1557476 1558231 := bstep (se 1 (by rfl) ⟨1168673, by rfl⟩ : syracuseStep 1558231 = 2337347) B2337347
theorem B3507929 : Blo 1557476 3507929 := bstep (se 2 (by rfl) ⟨1315473, by rfl⟩ : syracuseStep 3507929 = 2630947) B2630947
theorem B1558251 : Blo 1557476 1558251 := bstep (se 1 (by rfl) ⟨1168688, by rfl⟩ : syracuseStep 1558251 = 2337377) B2337377
theorem B1558263 : Blo 1557476 1558263 := bstep (se 1 (by rfl) ⟨1168697, by rfl⟩ : syracuseStep 1558263 = 2337395) B2337395
theorem B1558283 : Blo 1557476 1558283 := bstep (se 1 (by rfl) ⟨1168712, by rfl⟩ : syracuseStep 1558283 = 2337425) B2337425
theorem B1558295 : Blo 1557476 1558295 := bstep (se 1 (by rfl) ⟨1168721, by rfl⟩ : syracuseStep 1558295 = 2337443) B2337443
theorem B2336537 : Blo 1557476 2336537 := bstep (se 2 (by rfl) ⟨876201, by rfl⟩ : syracuseStep 2336537 = 1752403) B1752403
theorem B1558315 : Blo 1557476 1558315 := bstep (se 1 (by rfl) ⟨1168736, by rfl⟩ : syracuseStep 1558315 = 2337473) B2337473
theorem B3508019 : Blo 1557476 3508019 := bstep (se 1 (by rfl) ⟨2631014, by rfl⟩ : syracuseStep 3508019 = 5262029) B5262029
theorem B1558327 : Blo 1557476 1558327 := bstep (se 1 (by rfl) ⟨1168745, by rfl⟩ : syracuseStep 1558327 = 2337491) B2337491
theorem B45549377 : Blo 1557476 45549377 := bstep (se 2 (by rfl) ⟨17081016, by rfl⟩ : syracuseStep 45549377 = 34162033) B34162033
theorem B1558347 : Blo 1557476 1558347 := bstep (se 1 (by rfl) ⟨1168760, by rfl⟩ : syracuseStep 1558347 = 2337521) B2337521
theorem B1558359 : Blo 1557476 1558359 := bstep (se 1 (by rfl) ⟨1168769, by rfl⟩ : syracuseStep 1558359 = 2337539) B2337539
theorem B2959193 : Blo 1557476 2959193 := bstep (se 2 (by rfl) ⟨1109697, by rfl⟩ : syracuseStep 2959193 = 2219395) B2219395
theorem B3508055 : Blo 1557476 3508055 := bstep (se 1 (by rfl) ⟨2631041, by rfl⟩ : syracuseStep 3508055 = 5262083) B5262083
theorem B1558379 : Blo 1557476 1558379 := bstep (se 1 (by rfl) ⟨1168784, by rfl⟩ : syracuseStep 1558379 = 2337569) B2337569
theorem B1558391 : Blo 1557476 1558391 := bstep (se 1 (by rfl) ⟨1168793, by rfl⟩ : syracuseStep 1558391 = 2337587) B2337587
theorem B2336651 : Blo 1557476 2336651 := bstep (se 1 (by rfl) ⟨1752488, by rfl⟩ : syracuseStep 2336651 = 3504977) B3504977
theorem B1558411 : Blo 1557476 1558411 := bstep (se 1 (by rfl) ⟨1168808, by rfl⟩ : syracuseStep 1558411 = 2337617) B2337617
theorem B2336663 : Blo 1557476 2336663 := bstep (se 1 (by rfl) ⟨1752497, by rfl⟩ : syracuseStep 2336663 = 3504995) B3504995
theorem B4990871 : Blo 1557476 4990871 := bstep (se 1 (by rfl) ⟨3743153, by rfl⟩ : syracuseStep 4990871 = 7486307) B7486307
theorem B1558423 : Blo 1557476 1558423 := bstep (se 1 (by rfl) ⟨1168817, by rfl⟩ : syracuseStep 1558423 = 2337635) B2337635
theorem B2631575 : Blo 1557476 2631575 := bstep (se 1 (by rfl) ⟨1973681, by rfl⟩ : syracuseStep 2631575 = 3947363) B3947363
theorem B1558443 : Blo 1557476 1558443 := bstep (se 1 (by rfl) ⟨1168832, by rfl⟩ : syracuseStep 1558443 = 2337665) B2337665
theorem B12642227 : Blo 1557476 12642227 := bstep (se 1 (by rfl) ⟨9481670, by rfl⟩ : syracuseStep 12642227 = 18963341) B18963341
theorem B1558455 : Blo 1557476 1558455 := bstep (se 1 (by rfl) ⟨1168841, by rfl⟩ : syracuseStep 1558455 = 2337683) B2337683
theorem B1558475 : Blo 1557476 1558475 := bstep (se 1 (by rfl) ⟨1168856, by rfl⟩ : syracuseStep 1558475 = 2337713) B2337713
theorem B1558487 : Blo 1557476 1558487 := bstep (se 1 (by rfl) ⟨1168865, by rfl⟩ : syracuseStep 1558487 = 2337731) B2337731
theorem B2336729 : Blo 1557476 2336729 := bstep (se 2 (by rfl) ⟨876273, by rfl⟩ : syracuseStep 2336729 = 1752547) B1752547
theorem B18950105 : Blo 1557476 18950105 := bstep (se 2 (by rfl) ⟨7106289, by rfl⟩ : syracuseStep 18950105 = 14212579) B14212579
theorem B5261273 : Blo 1557476 5261273 := bstep (se 2 (by rfl) ⟨1972977, by rfl⟩ : syracuseStep 5261273 = 3945955) B3945955
theorem B1558507 : Blo 1557476 1558507 := bstep (se 1 (by rfl) ⟨1168880, by rfl⟩ : syracuseStep 1558507 = 2337761) B2337761
theorem B1558519 : Blo 1557476 1558519 := bstep (se 1 (by rfl) ⟨1168889, by rfl⟩ : syracuseStep 1558519 = 2337779) B2337779
theorem B1558539 : Blo 1557476 1558539 := bstep (se 1 (by rfl) ⟨1168904, by rfl⟩ : syracuseStep 1558539 = 2337809) B2337809
theorem B3508235 : Blo 1557476 3508235 := bstep (se 1 (by rfl) ⟨2631176, by rfl⟩ : syracuseStep 3508235 = 5262353) B5262353
theorem B1558551 : Blo 1557476 1558551 := bstep (se 1 (by rfl) ⟨1168913, by rfl⟩ : syracuseStep 1558551 = 2337827) B2337827
theorem B1558571 : Blo 1557476 1558571 := bstep (se 1 (by rfl) ⟨1168928, by rfl⟩ : syracuseStep 1558571 = 2337857) B2337857
theorem B9979949 : Blo 1557476 9979949 := bstep (se 3 (by rfl) ⟨1871240, by rfl⟩ : syracuseStep 9979949 = 3742481) B3742481
theorem B1558583 : Blo 1557476 1558583 := bstep (se 1 (by rfl) ⟨1168937, by rfl⟩ : syracuseStep 1558583 = 2337875) B2337875
theorem B3508289 : Blo 1557476 3508289 := bstep (se 2 (by rfl) ⟨1315608, by rfl⟩ : syracuseStep 3508289 = 2631217) B2631217
theorem B54716485 : Blo 1557476 54716485 := bstep (se 4 (by rfl) ⟨5129670, by rfl⟩ : syracuseStep 54716485 = 10259341) B10259341
theorem B2336843 : Blo 1557476 2336843 := bstep (se 1 (by rfl) ⟨1752632, by rfl⟩ : syracuseStep 2336843 = 3505265) B3505265
theorem B1558603 : Blo 1557476 1558603 := bstep (se 1 (by rfl) ⟨1168952, by rfl⟩ : syracuseStep 1558603 = 2337905) B2337905
theorem B7891019 : Blo 1557476 7891019 := bstep (se 1 (by rfl) ⟨5918264, by rfl⟩ : syracuseStep 7891019 = 11836529) B11836529
theorem B2336855 : Blo 1557476 2336855 := bstep (se 1 (by rfl) ⟨1752641, by rfl⟩ : syracuseStep 2336855 = 3505283) B3505283
theorem B1558615 : Blo 1557476 1558615 := bstep (se 1 (by rfl) ⟨1168961, by rfl⟩ : syracuseStep 1558615 = 2337923) B2337923
theorem B1558635 : Blo 1557476 1558635 := bstep (se 1 (by rfl) ⟨1168976, by rfl⟩ : syracuseStep 1558635 = 2337953) B2337953
theorem B1558647 : Blo 1557476 1558647 := bstep (se 1 (by rfl) ⟨1168985, by rfl⟩ : syracuseStep 1558647 = 2337971) B2337971
theorem B1558667 : Blo 1557476 1558667 := bstep (se 1 (by rfl) ⟨1169000, by rfl⟩ : syracuseStep 1558667 = 2338001) B2338001
theorem B1558679 : Blo 1557476 1558679 := bstep (se 1 (by rfl) ⟨1169009, by rfl⟩ : syracuseStep 1558679 = 2338019) B2338019
theorem B2336921 : Blo 1557476 2336921 := bstep (se 2 (by rfl) ⟨876345, by rfl⟩ : syracuseStep 2336921 = 1752691) B1752691
theorem B1558699 : Blo 1557476 1558699 := bstep (se 1 (by rfl) ⟨1169024, by rfl⟩ : syracuseStep 1558699 = 2338049) B2338049
theorem B1558711 : Blo 1557476 1558711 := bstep (se 1 (by rfl) ⟨1169033, by rfl⟩ : syracuseStep 1558711 = 2338067) B2338067
theorem B4991179 : Blo 1557476 4991179 := bstep (se 1 (by rfl) ⟨3743384, by rfl⟩ : syracuseStep 4991179 = 7486769) B7486769
theorem B1558731 : Blo 1557476 1558731 := bstep (se 1 (by rfl) ⟨1169048, by rfl⟩ : syracuseStep 1558731 = 2338097) B2338097
theorem B1558743 : Blo 1557476 1558743 := bstep (se 1 (by rfl) ⟨1169057, by rfl⟩ : syracuseStep 1558743 = 2338115) B2338115
theorem B1558763 : Blo 1557476 1558763 := bstep (se 1 (by rfl) ⟨1169072, by rfl⟩ : syracuseStep 1558763 = 2338145) B2338145
theorem B1558775 : Blo 1557476 1558775 := bstep (se 1 (by rfl) ⟨1169081, by rfl⟩ : syracuseStep 1558775 = 2338163) B2338163
theorem B6080771 : Blo 1557476 6080771 := bstep (se 1 (by rfl) ⟨4560578, by rfl⟩ : syracuseStep 6080771 = 9121157) B9121157
theorem B2337035 : Blo 1557476 2337035 := bstep (se 1 (by rfl) ⟨1752776, by rfl⟩ : syracuseStep 2337035 = 3505553) B3505553
theorem B1558795 : Blo 1557476 1558795 := bstep (se 1 (by rfl) ⟨1169096, by rfl⟩ : syracuseStep 1558795 = 2338193) B2338193
theorem B2337047 : Blo 1557476 2337047 := bstep (se 1 (by rfl) ⟨1752785, by rfl⟩ : syracuseStep 2337047 = 3505571) B3505571
theorem B1558807 : Blo 1557476 1558807 := bstep (se 1 (by rfl) ⟨1169105, by rfl⟩ : syracuseStep 1558807 = 2338211) B2338211
theorem B3508505 : Blo 1557476 3508505 := bstep (se 2 (by rfl) ⟨1315689, by rfl⟩ : syracuseStep 3508505 = 2631379) B2631379
theorem B1558827 : Blo 1557476 1558827 := bstep (se 1 (by rfl) ⟨1169120, by rfl⟩ : syracuseStep 1558827 = 2338241) B2338241
theorem B3328307 : Blo 1557476 3328307 := bstep (se 1 (by rfl) ⟨2496230, by rfl⟩ : syracuseStep 3328307 = 4992461) B4992461
theorem B1558839 : Blo 1557476 1558839 := bstep (se 1 (by rfl) ⟨1169129, by rfl⟩ : syracuseStep 1558839 = 2338259) B2338259
theorem B1558859 : Blo 1557476 1558859 := bstep (se 1 (by rfl) ⟨1169144, by rfl⟩ : syracuseStep 1558859 = 2338289) B2338289
theorem B1558871 : Blo 1557476 1558871 := bstep (se 1 (by rfl) ⟨1169153, by rfl⟩ : syracuseStep 1558871 = 2338307) B2338307
theorem B2337113 : Blo 1557476 2337113 := bstep (se 2 (by rfl) ⟨876417, by rfl⟩ : syracuseStep 2337113 = 1752835) B1752835
theorem B6318425 : Blo 1557476 6318425 := bstep (se 2 (by rfl) ⟨2369409, by rfl⟩ : syracuseStep 6318425 = 4738819) B4738819
theorem B4213081 : Blo 1557476 4213081 := bstep (se 2 (by rfl) ⟨1579905, by rfl⟩ : syracuseStep 4213081 = 3159811) B3159811
theorem B1558891 : Blo 1557476 1558891 := bstep (se 1 (by rfl) ⟨1169168, by rfl⟩ : syracuseStep 1558891 = 2338337) B2338337
theorem B3508595 : Blo 1557476 3508595 := bstep (se 1 (by rfl) ⟨2631446, by rfl⟩ : syracuseStep 3508595 = 5262893) B5262893
theorem B1558903 : Blo 1557476 1558903 := bstep (se 1 (by rfl) ⟨1169177, by rfl⟩ : syracuseStep 1558903 = 2338355) B2338355
theorem B1558923 : Blo 1557476 1558923 := bstep (se 1 (by rfl) ⟨1169192, by rfl⟩ : syracuseStep 1558923 = 2338385) B2338385
theorem B1558935 : Blo 1557476 1558935 := bstep (se 1 (by rfl) ⟨1169201, by rfl⟩ : syracuseStep 1558935 = 2338403) B2338403
theorem B3508631 : Blo 1557476 3508631 := bstep (se 1 (by rfl) ⟨2631473, by rfl⟩ : syracuseStep 3508631 = 5262947) B5262947
theorem B3328409 : Blo 1557476 3328409 := bstep (se 2 (by rfl) ⟨1248153, by rfl⟩ : syracuseStep 3328409 = 2496307) B2496307
theorem B1558955 : Blo 1557476 1558955 := bstep (se 1 (by rfl) ⟨1169216, by rfl⟩ : syracuseStep 1558955 = 2338433) B2338433
theorem B18958769 : Blo 1557476 18958769 := bstep (se 2 (by rfl) ⟨7109538, by rfl⟩ : syracuseStep 18958769 = 14219077) B14219077
theorem B1558967 : Blo 1557476 1558967 := bstep (se 1 (by rfl) ⟨1169225, by rfl⟩ : syracuseStep 1558967 = 2338451) B2338451
theorem B2337227 : Blo 1557476 2337227 := bstep (se 1 (by rfl) ⟨1752920, by rfl⟩ : syracuseStep 2337227 = 3505841) B3505841
theorem B1558987 : Blo 1557476 1558987 := bstep (se 1 (by rfl) ⟨1169240, by rfl⟩ : syracuseStep 1558987 = 2338481) B2338481
theorem B2337239 : Blo 1557476 2337239 := bstep (se 1 (by rfl) ⟨1752929, by rfl⟩ : syracuseStep 2337239 = 3505859) B3505859
theorem B1558999 : Blo 1557476 1558999 := bstep (se 1 (by rfl) ⟨1169249, by rfl⟩ : syracuseStep 1558999 = 2338499) B2338499
theorem B2959831 : Blo 1557476 2959831 := bstep (se 1 (by rfl) ⟨2219873, by rfl⟩ : syracuseStep 2959831 = 4439747) B4439747
theorem B1559019 : Blo 1557476 1559019 := bstep (se 1 (by rfl) ⟨1169264, by rfl⟩ : syracuseStep 1559019 = 2338529) B2338529
theorem B1559031 : Blo 1557476 1559031 := bstep (se 1 (by rfl) ⟨1169273, by rfl⟩ : syracuseStep 1559031 = 2338547) B2338547
theorem B1559051 : Blo 1557476 1559051 := bstep (se 1 (by rfl) ⟨1169288, by rfl⟩ : syracuseStep 1559051 = 2338577) B2338577
theorem B1559063 : Blo 1557476 1559063 := bstep (se 1 (by rfl) ⟨1169297, by rfl⟩ : syracuseStep 1559063 = 2338595) B2338595
theorem B2337305 : Blo 1557476 2337305 := bstep (se 2 (by rfl) ⟨876489, by rfl⟩ : syracuseStep 2337305 = 1752979) B1752979
theorem B1559083 : Blo 1557476 1559083 := bstep (se 1 (by rfl) ⟨1169312, by rfl⟩ : syracuseStep 1559083 = 2338625) B2338625
theorem B1559095 : Blo 1557476 1559095 := bstep (se 1 (by rfl) ⟨1169321, by rfl⟩ : syracuseStep 1559095 = 2338643) B2338643
theorem B1559115 : Blo 1557476 1559115 := bstep (se 1 (by rfl) ⟨1169336, by rfl⟩ : syracuseStep 1559115 = 2338673) B2338673
theorem B3508811 : Blo 1557476 3508811 := bstep (se 1 (by rfl) ⟨2631608, by rfl⟩ : syracuseStep 3508811 = 5263217) B5263217
theorem B1559127 : Blo 1557476 1559127 := bstep (se 1 (by rfl) ⟨1169345, by rfl⟩ : syracuseStep 1559127 = 2338691) B2338691
theorem B29952605 : Blo 1557476 29952605 := bstep (se 3 (by rfl) ⟨5616113, by rfl⟩ : syracuseStep 29952605 = 11232227) B11232227
theorem B1559147 : Blo 1557476 1559147 := bstep (se 1 (by rfl) ⟨1169360, by rfl⟩ : syracuseStep 1559147 = 2338721) B2338721
theorem B1559159 : Blo 1557476 1559159 := bstep (se 1 (by rfl) ⟨1169369, by rfl⟩ : syracuseStep 1559159 = 2338739) B2338739
theorem B2337419 : Blo 1557476 2337419 := bstep (se 1 (by rfl) ⟨1753064, by rfl⟩ : syracuseStep 2337419 = 3506129) B3506129
theorem B2370187 : Blo 1557476 2370187 := bstep (se 1 (by rfl) ⟨1777640, by rfl⟩ : syracuseStep 2370187 = 3555281) B3555281
theorem B1559179 : Blo 1557476 1559179 := bstep (se 1 (by rfl) ⟨1169384, by rfl⟩ : syracuseStep 1559179 = 2338769) B2338769
theorem B2337431 : Blo 1557476 2337431 := bstep (se 1 (by rfl) ⟨1753073, by rfl⟩ : syracuseStep 2337431 = 3506147) B3506147
theorem B5261975 : Blo 1557476 5261975 := bstep (se 1 (by rfl) ⟨3946481, by rfl⟩ : syracuseStep 5261975 = 7892963) B7892963
theorem B1559191 : Blo 1557476 1559191 := bstep (se 1 (by rfl) ⟨1169393, by rfl⟩ : syracuseStep 1559191 = 2338787) B2338787
theorem B1559211 : Blo 1557476 1559211 := bstep (se 1 (by rfl) ⟨1169408, by rfl⟩ : syracuseStep 1559211 = 2338817) B2338817
theorem B1559223 : Blo 1557476 1559223 := bstep (se 1 (by rfl) ⟨1169417, by rfl⟩ : syracuseStep 1559223 = 2338835) B2338835
theorem B1559243 : Blo 1557476 1559243 := bstep (se 1 (by rfl) ⟨1169432, by rfl⟩ : syracuseStep 1559243 = 2338865) B2338865
theorem B1559255 : Blo 1557476 1559255 := bstep (se 1 (by rfl) ⟨1169441, by rfl⟩ : syracuseStep 1559255 = 2338883) B2338883
theorem B2337497 : Blo 1557476 2337497 := bstep (se 2 (by rfl) ⟨876561, by rfl⟩ : syracuseStep 2337497 = 1753123) B1753123
theorem B1559275 : Blo 1557476 1559275 := bstep (se 1 (by rfl) ⟨1169456, by rfl⟩ : syracuseStep 1559275 = 2338913) B2338913
theorem B1559287 : Blo 1557476 1559287 := bstep (se 1 (by rfl) ⟨1169465, by rfl⟩ : syracuseStep 1559287 = 2338931) B2338931
theorem B3328769 : Blo 1557476 3328769 := bstep (se 2 (by rfl) ⟨1248288, by rfl⟩ : syracuseStep 3328769 = 2496577) B2496577
theorem B1559307 : Blo 1557476 1559307 := bstep (se 1 (by rfl) ⟨1169480, by rfl⟩ : syracuseStep 1559307 = 2338961) B2338961
theorem B1559319 : Blo 1557476 1559319 := bstep (se 1 (by rfl) ⟨1169489, by rfl⟩ : syracuseStep 1559319 = 2338979) B2338979
theorem B1559339 : Blo 1557476 1559339 := bstep (se 1 (by rfl) ⟨1169504, by rfl⟩ : syracuseStep 1559339 = 2339009) B2339009
theorem B1559351 : Blo 1557476 1559351 := bstep (se 1 (by rfl) ⟨1169513, by rfl⟩ : syracuseStep 1559351 = 2339027) B2339027
theorem B2337611 : Blo 1557476 2337611 := bstep (se 1 (by rfl) ⟨1753208, by rfl⟩ : syracuseStep 2337611 = 3506417) B3506417
theorem B1559371 : Blo 1557476 1559371 := bstep (se 1 (by rfl) ⟨1169528, by rfl⟩ : syracuseStep 1559371 = 2339057) B2339057
theorem B2337623 : Blo 1557476 2337623 := bstep (se 1 (by rfl) ⟨1753217, by rfl⟩ : syracuseStep 2337623 = 3506435) B3506435
theorem B1559383 : Blo 1557476 1559383 := bstep (se 1 (by rfl) ⟨1169537, by rfl⟩ : syracuseStep 1559383 = 2339075) B2339075
theorem B1559403 : Blo 1557476 1559403 := bstep (se 1 (by rfl) ⟨1169552, by rfl⟩ : syracuseStep 1559403 = 2339105) B2339105
theorem B1559415 : Blo 1557476 1559415 := bstep (se 1 (by rfl) ⟨1169561, by rfl⟩ : syracuseStep 1559415 = 2339123) B2339123
theorem B1559435 : Blo 1557476 1559435 := bstep (se 1 (by rfl) ⟨1169576, by rfl⟩ : syracuseStep 1559435 = 2339153) B2339153
theorem B3746711 : Blo 1557476 3746711 := bstep (se 1 (by rfl) ⟨2810033, by rfl⟩ : syracuseStep 3746711 = 5620067) B5620067
theorem B1559447 : Blo 1557476 1559447 := bstep (se 1 (by rfl) ⟨1169585, by rfl⟩ : syracuseStep 1559447 = 2339171) B2339171
theorem B2337689 : Blo 1557476 2337689 := bstep (se 2 (by rfl) ⟨876633, by rfl⟩ : syracuseStep 2337689 = 1753267) B1753267
theorem B1559467 : Blo 1557476 1559467 := bstep (se 1 (by rfl) ⟨1169600, by rfl⟩ : syracuseStep 1559467 = 2339201) B2339201
theorem B13306801 : Blo 1557476 13306801 := bstep (se 2 (by rfl) ⟨4990050, by rfl⟩ : syracuseStep 13306801 = 9980101) B9980101
theorem B28437425 : Blo 1557476 28437425 := bstep (se 2 (by rfl) ⟨10664034, by rfl⟩ : syracuseStep 28437425 = 21328069) B21328069
theorem B5917643 : Blo 1557476 5917643 := bstep (se 1 (by rfl) ⟨4438232, by rfl⟩ : syracuseStep 5917643 = 8876465) B8876465
theorem B23981017 : Blo 1557476 23981017 := bstep (se 2 (by rfl) ⟨8992881, by rfl⟩ : syracuseStep 23981017 = 17985763) B17985763
theorem B5917657 : Blo 1557476 5917657 := bstep (se 2 (by rfl) ⟨2219121, by rfl⟩ : syracuseStep 5917657 = 4438243) B4438243
theorem B2026507 : Blo 1557476 2026507 := bstep (se 1 (by rfl) ⟨1519880, by rfl⟩ : syracuseStep 2026507 = 3039761) B3039761
theorem B2337803 : Blo 1557476 2337803 := bstep (se 1 (by rfl) ⟨1753352, by rfl⟩ : syracuseStep 2337803 = 3506705) B3506705
theorem B2337815 : Blo 1557476 2337815 := bstep (se 1 (by rfl) ⟨1753361, by rfl⟩ : syracuseStep 2337815 = 3506723) B3506723
theorem B3943475 : Blo 1557476 3943475 := bstep (se 1 (by rfl) ⟨2957606, by rfl⟩ : syracuseStep 3943475 = 5915213) B5915213
theorem B2337881 : Blo 1557476 2337881 := bstep (se 2 (by rfl) ⟨876705, by rfl⟩ : syracuseStep 2337881 = 1753411) B1753411
theorem B4934807 : Blo 1557476 4934807 := bstep (se 1 (by rfl) ⟨3701105, by rfl⟩ : syracuseStep 4934807 = 7402211) B7402211
theorem B5262515 : Blo 1557476 5262515 := bstep (se 1 (by rfl) ⟨3946886, by rfl⟩ : syracuseStep 5262515 = 7893773) B7893773
theorem B2337995 : Blo 1557476 2337995 := bstep (se 1 (by rfl) ⟨1753496, by rfl⟩ : syracuseStep 2337995 = 3506993) B3506993
theorem B2338007 : Blo 1557476 2338007 := bstep (se 1 (by rfl) ⟨1753505, by rfl⟩ : syracuseStep 2338007 = 3507011) B3507011
theorem B205090019 : Blo 1557476 205090019 := bstep (se 1 (by rfl) ⟨153817514, by rfl⟩ : syracuseStep 205090019 = 307635029) B307635029
theorem B2338073 : Blo 1557476 2338073 := bstep (se 2 (by rfl) ⟨876777, by rfl⟩ : syracuseStep 2338073 = 1753555) B1753555
theorem B11832641 : Blo 1557476 11832641 := bstep (se 2 (by rfl) ⟨4437240, by rfl⟩ : syracuseStep 11832641 = 8874481) B8874481
theorem B8220035 : Blo 1557476 8220035 := bstep (se 1 (by rfl) ⟨6165026, by rfl⟩ : syracuseStep 8220035 = 12330053) B12330053
theorem B2338187 : Blo 1557476 2338187 := bstep (se 1 (by rfl) ⟨1753640, by rfl⟩ : syracuseStep 2338187 = 3507281) B3507281
theorem B2338199 : Blo 1557476 2338199 := bstep (se 1 (by rfl) ⟨1753649, by rfl⟩ : syracuseStep 2338199 = 3507299) B3507299
theorem B5615021 : Blo 1557476 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B5262785 : Blo 1557476 5262785 := bstep (se 2 (by rfl) ⟨1973544, by rfl⟩ : syracuseStep 5262785 = 3947089) B3947089
theorem B3329495 : Blo 1557476 3329495 := bstep (se 1 (by rfl) ⟨2497121, by rfl⟩ : syracuseStep 3329495 = 4994243) B4994243
theorem B2338265 : Blo 1557476 2338265 := bstep (se 2 (by rfl) ⟨876849, by rfl⟩ : syracuseStep 2338265 = 1753699) B1753699
theorem B3944011 : Blo 1557476 3944011 := bstep (se 1 (by rfl) ⟨2958008, by rfl⟩ : syracuseStep 3944011 = 5916017) B5916017
theorem B2338379 : Blo 1557476 2338379 := bstep (se 1 (by rfl) ⟨1753784, by rfl⟩ : syracuseStep 2338379 = 3507569) B3507569
theorem B2338391 : Blo 1557476 2338391 := bstep (se 1 (by rfl) ⟨1753793, by rfl⟩ : syracuseStep 2338391 = 3507587) B3507587
theorem B2338457 : Blo 1557476 2338457 := bstep (se 2 (by rfl) ⟨876921, by rfl⟩ : syracuseStep 2338457 = 1753843) B1753843
theorem B3944153 : Blo 1557476 3944153 := bstep (se 2 (by rfl) ⟨1479057, by rfl⟩ : syracuseStep 3944153 = 2958115) B2958115
theorem B6655709 : Blo 1557476 6655709 := bstep (se 3 (by rfl) ⟨1247945, by rfl⟩ : syracuseStep 6655709 = 2495891) B2495891
theorem B2338571 : Blo 1557476 2338571 := bstep (se 1 (by rfl) ⟨1753928, by rfl⟩ : syracuseStep 2338571 = 3507857) B3507857
theorem B2338583 : Blo 1557476 2338583 := bstep (se 1 (by rfl) ⟨1753937, by rfl⟩ : syracuseStep 2338583 = 3507875) B3507875
theorem B7892801 : Blo 1557476 7892801 := bstep (se 2 (by rfl) ⟨2959800, by rfl⟩ : syracuseStep 7892801 = 5919601) B5919601
theorem B2338649 : Blo 1557476 2338649 := bstep (se 2 (by rfl) ⟨876993, by rfl⟩ : syracuseStep 2338649 = 1753987) B1753987
theorem B7106435 : Blo 1557476 7106435 := bstep (se 1 (by rfl) ⟨5329826, by rfl⟩ : syracuseStep 7106435 = 10659653) B10659653
theorem B5918615 : Blo 1557476 5918615 := bstep (se 1 (by rfl) ⟨4438961, by rfl⟩ : syracuseStep 5918615 = 8877923) B8877923
theorem B2338763 : Blo 1557476 2338763 := bstep (se 1 (by rfl) ⟨1754072, by rfl⟩ : syracuseStep 2338763 = 3508145) B3508145
theorem B2338775 : Blo 1557476 2338775 := bstep (se 1 (by rfl) ⟨1754081, by rfl⟩ : syracuseStep 2338775 = 3508163) B3508163
theorem B12644369 : Blo 1557476 12644369 := bstep (se 2 (by rfl) ⟨4741638, by rfl⟩ : syracuseStep 12644369 = 9483277) B9483277
theorem B2338841 : Blo 1557476 2338841 := bstep (se 2 (by rfl) ⟨877065, by rfl⟩ : syracuseStep 2338841 = 1754131) B1754131
theorem B18960419 : Blo 1557476 18960419 := bstep (se 1 (by rfl) ⟨14220314, by rfl⟩ : syracuseStep 18960419 = 28440629) B28440629
theorem B2338955 : Blo 1557476 2338955 := bstep (se 1 (by rfl) ⟨1754216, by rfl⟩ : syracuseStep 2338955 = 3508433) B3508433
theorem B2338967 : Blo 1557476 2338967 := bstep (se 1 (by rfl) ⟨1754225, by rfl⟩ : syracuseStep 2338967 = 3508451) B3508451
theorem B4436147 : Blo 1557476 4436147 := bstep (se 1 (by rfl) ⟨3327110, by rfl⟩ : syracuseStep 4436147 = 6654221) B6654221
theorem B4436171 : Blo 1557476 4436171 := bstep (se 1 (by rfl) ⟨3327128, by rfl⟩ : syracuseStep 4436171 = 6654257) B6654257
theorem B2339033 : Blo 1557476 2339033 := bstep (se 2 (by rfl) ⟨877137, by rfl⟩ : syracuseStep 2339033 = 1754275) B1754275
theorem B4993331 : Blo 1557476 4993331 := bstep (se 1 (by rfl) ⟨3744998, by rfl⟩ : syracuseStep 4993331 = 7489997) B7489997
theorem B2494795 : Blo 1557476 2494795 := bstep (se 1 (by rfl) ⟨1871096, by rfl⟩ : syracuseStep 2494795 = 3742193) B3742193
theorem B2339147 : Blo 1557476 2339147 := bstep (se 1 (by rfl) ⟨1754360, by rfl⟩ : syracuseStep 2339147 = 3508721) B3508721
theorem B3330391 : Blo 1557476 3330391 := bstep (se 1 (by rfl) ⟨2497793, by rfl⟩ : syracuseStep 3330391 = 4995587) B4995587
theorem B2339159 : Blo 1557476 2339159 := bstep (se 1 (by rfl) ⟨1754369, by rfl⟩ : syracuseStep 2339159 = 3508739) B3508739
theorem B7885187 : Blo 1557476 7885187 := bstep (se 1 (by rfl) ⟨5913890, by rfl⟩ : syracuseStep 7885187 = 11827781) B11827781
theorem B2494937 : Blo 1557476 2494937 := bstep (se 2 (by rfl) ⟨935601, by rfl⟩ : syracuseStep 2494937 = 1871203) B1871203
theorem B2249227 : Blo 1557476 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B3944983 : Blo 1557476 3944983 := bstep (se 1 (by rfl) ⟨2958737, by rfl⟩ : syracuseStep 3944983 = 5917475) B5917475
theorem B5616449 : Blo 1557476 5616449 := bstep (se 2 (by rfl) ⟨2106168, by rfl⟩ : syracuseStep 5616449 = 4212337) B4212337
theorem B9982871 : Blo 1557476 9982871 := bstep (se 1 (by rfl) ⟨7487153, by rfl⟩ : syracuseStep 9982871 = 14974307) B14974307
theorem B3945419 : Blo 1557476 3945419 := bstep (se 1 (by rfl) ⟨2959064, by rfl⟩ : syracuseStep 3945419 = 5918129) B5918129
theorem B4436957 : Blo 1557476 4436957 := bstep (se 3 (by rfl) ⟨831929, by rfl⟩ : syracuseStep 4436957 = 1663859) B1663859
theorem B1971211 : Blo 1557476 1971211 := bstep (se 1 (by rfl) ⟨1478408, by rfl⟩ : syracuseStep 1971211 = 2956817) B2956817
theorem B6583427 : Blo 1557476 6583427 := bstep (se 1 (by rfl) ⟨4937570, by rfl⟩ : syracuseStep 6583427 = 9875141) B9875141
theorem B5919875 : Blo 1557476 5919875 := bstep (se 1 (by rfl) ⟨4439906, by rfl⟩ : syracuseStep 5919875 = 8879813) B8879813
theorem B11834585 : Blo 1557476 11834585 := bstep (se 2 (by rfl) ⟨4437969, by rfl⟩ : syracuseStep 11834585 = 8875939) B8875939
theorem B1873163 : Blo 1557476 1873163 := bstep (se 1 (by rfl) ⟨1404872, by rfl⟩ : syracuseStep 1873163 = 2809745) B2809745
theorem B1971479 : Blo 1557476 1971479 := bstep (se 1 (by rfl) ⟨1478609, by rfl⟩ : syracuseStep 1971479 = 2957219) B2957219
theorem B3945793 : Blo 1557476 3945793 := bstep (se 2 (by rfl) ⟨1479672, by rfl⟩ : syracuseStep 3945793 = 2959345) B2959345
theorem B2807129 : Blo 1557476 2807129 := bstep (se 2 (by rfl) ⟨1052673, by rfl⟩ : syracuseStep 2807129 = 2105347) B2105347
theorem B16840037 : Blo 1557476 16840037 := bstep (se 4 (by rfl) ⟨1578753, by rfl⟩ : syracuseStep 16840037 = 3157507) B3157507
theorem B2496025 : Blo 1557476 2496025 := bstep (se 2 (by rfl) ⟨936009, by rfl⟩ : syracuseStep 2496025 = 1872019) B1872019
theorem B3159577 : Blo 1557476 3159577 := bstep (se 2 (by rfl) ⟨1184841, by rfl⟩ : syracuseStep 3159577 = 2369683) B2369683
theorem B7894745 : Blo 1557476 7894745 := bstep (se 2 (by rfl) ⟨2960529, by rfl⟩ : syracuseStep 7894745 = 5921059) B5921059
theorem B25966453 : Blo 1557476 25966453 := bstep (se 5 (by rfl) ⟨1217177, by rfl⟩ : syracuseStep 25966453 = 2434355) B2434355
theorem B3946391 : Blo 1557476 3946391 := bstep (se 1 (by rfl) ⟨2959793, by rfl⟩ : syracuseStep 3946391 = 5919587) B5919587
theorem B1972183 : Blo 1557476 1972183 := bstep (se 1 (by rfl) ⟨1479137, by rfl⟩ : syracuseStep 1972183 = 2958275) B2958275
theorem B115308685 : Blo 1557476 115308685 := bstep (se 3 (by rfl) ⟨21620378, by rfl⟩ : syracuseStep 115308685 = 43240757) B43240757
theorem B6658307 : Blo 1557476 6658307 := bstep (se 1 (by rfl) ⟨4993730, by rfl⟩ : syracuseStep 6658307 = 9987461) B9987461
theorem B5257547 : Blo 1557476 5257547 := bstep (se 1 (by rfl) ⟨3943160, by rfl⟩ : syracuseStep 5257547 = 7886321) B7886321
theorem B3504473 : Blo 1557476 3504473 := bstep (se 2 (by rfl) ⟨1314177, by rfl⟩ : syracuseStep 3504473 = 2628355) B2628355
theorem B3504563 : Blo 1557476 3504563 := bstep (se 1 (by rfl) ⟨2628422, by rfl⟩ : syracuseStep 3504563 = 5256845) B5256845
theorem B3504599 : Blo 1557476 3504599 := bstep (se 1 (by rfl) ⟨2628449, by rfl⟩ : syracuseStep 3504599 = 5256899) B5256899
theorem B5257817 : Blo 1557476 5257817 := bstep (se 2 (by rfl) ⟨1971681, by rfl⟩ : syracuseStep 5257817 = 3943363) B3943363
theorem B3504779 : Blo 1557476 3504779 := bstep (se 1 (by rfl) ⟨2628584, by rfl⟩ : syracuseStep 3504779 = 5257169) B5257169
theorem B2628247 : Blo 1557476 2628247 := bstep (se 1 (by rfl) ⟨1971185, by rfl⟩ : syracuseStep 2628247 = 3942371) B3942371
theorem B4741811 : Blo 1557476 4741811 := bstep (se 1 (by rfl) ⟨3556358, by rfl⟩ : syracuseStep 4741811 = 7112717) B7112717
theorem B3504833 : Blo 1557476 3504833 := bstep (se 2 (by rfl) ⟨1314312, by rfl⟩ : syracuseStep 3504833 = 2628625) B2628625
theorem B3947201 : Blo 1557476 3947201 := bstep (se 2 (by rfl) ⟨1480200, by rfl⟩ : syracuseStep 3947201 = 2960401) B2960401
theorem B4438745 : Blo 1557476 4438745 := bstep (se 2 (by rfl) ⟨1664529, by rfl⟩ : syracuseStep 4438745 = 3329059) B3329059
theorem B5692183 : Blo 1557476 5692183 := bstep (se 1 (by rfl) ⟨4269137, by rfl⟩ : syracuseStep 5692183 = 8538275) B8538275
theorem B6322967 : Blo 1557476 6322967 := bstep (se 1 (by rfl) ⟨4742225, by rfl⟩ : syracuseStep 6322967 = 9484451) B9484451
theorem B3742615 : Blo 1557476 3742615 := bstep (se 1 (by rfl) ⟨2806961, by rfl⟩ : syracuseStep 3742615 = 5613923) B5613923
theorem B3505049 : Blo 1557476 3505049 := bstep (se 2 (by rfl) ⟨1314393, by rfl⟩ : syracuseStep 3505049 = 2628787) B2628787
theorem B1686443 : Blo 1557476 1686443 := bstep (se 1 (by rfl) ⟨1264832, by rfl⟩ : syracuseStep 1686443 = 2529665) B2529665
theorem B3161011 : Blo 1557476 3161011 := bstep (se 1 (by rfl) ⟨2370758, by rfl⟩ : syracuseStep 3161011 = 4741517) B4741517
theorem B3505139 : Blo 1557476 3505139 := bstep (se 1 (by rfl) ⟨2628854, by rfl⟩ : syracuseStep 3505139 = 5257709) B5257709
theorem B3505175 : Blo 1557476 3505175 := bstep (se 1 (by rfl) ⟨2628881, by rfl⟩ : syracuseStep 3505175 = 5257763) B5257763
theorem B4439063 : Blo 1557476 4439063 := bstep (se 1 (by rfl) ⟨3329297, by rfl⟩ : syracuseStep 4439063 = 6658595) B6658595
theorem B3505355 : Blo 1557476 3505355 := bstep (se 1 (by rfl) ⟨2629016, by rfl⟩ : syracuseStep 3505355 = 5258033) B5258033
theorem B3505409 : Blo 1557476 3505409 := bstep (se 2 (by rfl) ⟨1314528, by rfl⟩ : syracuseStep 3505409 = 2629057) B2629057
theorem B12631301 : Blo 1557476 12631301 := bstep (se 4 (by rfl) ⟨1184184, by rfl⟩ : syracuseStep 12631301 = 2368369) B2368369
theorem B1752331 : Blo 1557476 1752331 := bstep (se 1 (by rfl) ⟨1314248, by rfl⟩ : syracuseStep 1752331 = 2628497) B2628497
theorem B2628875 : Blo 1557476 2628875 := bstep (se 1 (by rfl) ⟨1971656, by rfl⟩ : syracuseStep 2628875 = 3943313) B3943313
theorem B5258519 : Blo 1557476 5258519 := bstep (se 1 (by rfl) ⟨3943889, by rfl⟩ : syracuseStep 5258519 = 7887779) B7887779
theorem B3161369 : Blo 1557476 3161369 := bstep (se 2 (by rfl) ⟨1185513, by rfl⟩ : syracuseStep 3161369 = 2371027) B2371027
theorem B22781249 : Blo 1557476 22781249 := bstep (se 2 (by rfl) ⟨8542968, by rfl⟩ : syracuseStep 22781249 = 17085937) B17085937
theorem B1752439 : Blo 1557476 1752439 := bstep (se 1 (by rfl) ⟨1314329, by rfl⟩ : syracuseStep 1752439 = 2628659) B2628659
theorem B8428931 : Blo 1557476 8428931 := bstep (se 1 (by rfl) ⟨6321698, by rfl⟩ : syracuseStep 8428931 = 12643397) B12643397
theorem B2629003 : Blo 1557476 2629003 := bstep (se 1 (by rfl) ⟨1971752, by rfl⟩ : syracuseStep 2629003 = 3943505) B3943505
theorem B5914073 : Blo 1557476 5914073 := bstep (se 2 (by rfl) ⟨2217777, by rfl⟩ : syracuseStep 5914073 = 4435555) B4435555
theorem B3505625 : Blo 1557476 3505625 := bstep (se 2 (by rfl) ⟨1314609, by rfl⟩ : syracuseStep 3505625 = 2629219) B2629219
theorem B13311449 : Blo 1557476 13311449 := bstep (se 2 (by rfl) ⟨4991793, by rfl⟩ : syracuseStep 13311449 = 9983587) B9983587
theorem B11828753 : Blo 1557476 11828753 := bstep (se 2 (by rfl) ⟨4435782, by rfl⟩ : syracuseStep 11828753 = 8871565) B8871565
theorem B1580567 : Blo 1557476 1580567 := bstep (se 1 (by rfl) ⟨1185425, by rfl⟩ : syracuseStep 1580567 = 2370851) B2370851
theorem B2629145 : Blo 1557476 2629145 := bstep (se 2 (by rfl) ⟨985929, by rfl⟩ : syracuseStep 2629145 = 1971859) B1971859
theorem B1752619 : Blo 1557476 1752619 := bstep (se 1 (by rfl) ⟨1314464, by rfl⟩ : syracuseStep 1752619 = 2628929) B2628929
theorem B3505715 : Blo 1557476 3505715 := bstep (se 1 (by rfl) ⟨2629286, by rfl⟩ : syracuseStep 3505715 = 5258573) B5258573
theorem B1580599 : Blo 1557476 1580599 := bstep (se 1 (by rfl) ⟨1185449, by rfl⟩ : syracuseStep 1580599 = 2370899) B2370899
theorem B3505751 : Blo 1557476 3505751 := bstep (se 1 (by rfl) ⟨2629313, by rfl⟩ : syracuseStep 3505751 = 5258627) B5258627
theorem B2956915 : Blo 1557476 2956915 := bstep (se 1 (by rfl) ⟨2217686, by rfl⟩ : syracuseStep 2956915 = 4435373) B4435373
theorem B1998475 : Blo 1557476 1998475 := bstep (se 1 (by rfl) ⟨1498856, by rfl⟩ : syracuseStep 1998475 = 2997713) B2997713
theorem B1752727 : Blo 1557476 1752727 := bstep (se 1 (by rfl) ⟨1314545, by rfl⟩ : syracuseStep 1752727 = 2629091) B2629091
theorem B2629273 : Blo 1557476 2629273 := bstep (se 2 (by rfl) ⟨985977, by rfl⟩ : syracuseStep 2629273 = 1971955) B1971955
theorem B2219737 : Blo 1557476 2219737 := bstep (se 2 (by rfl) ⟨832401, by rfl⟩ : syracuseStep 2219737 = 1664803) B1664803
theorem B3505931 : Blo 1557476 3505931 := bstep (se 1 (by rfl) ⟨2629448, by rfl⟩ : syracuseStep 3505931 = 5258897) B5258897
theorem B5259059 : Blo 1557476 5259059 := bstep (se 1 (by rfl) ⟨3944294, by rfl⟩ : syracuseStep 5259059 = 7888589) B7888589
theorem B3505985 : Blo 1557476 3505985 := bstep (se 2 (by rfl) ⟨1314744, by rfl⟩ : syracuseStep 3505985 = 2629489) B2629489
theorem B4439873 : Blo 1557476 4439873 := bstep (se 2 (by rfl) ⟨1664952, by rfl⟩ : syracuseStep 4439873 = 3329905) B3329905
theorem B1752907 : Blo 1557476 1752907 := bstep (se 1 (by rfl) ⟨1314680, by rfl⟩ : syracuseStep 1752907 = 2629361) B2629361
theorem B2957143 : Blo 1557476 2957143 := bstep (se 1 (by rfl) ⟨2217857, by rfl⟩ : syracuseStep 2957143 = 4435715) B4435715
theorem B1753015 : Blo 1557476 1753015 := bstep (se 1 (by rfl) ⟨1314761, by rfl⟩ : syracuseStep 1753015 = 2629523) B2629523
theorem B2957249 : Blo 1557476 2957249 := bstep (se 2 (by rfl) ⟨1108968, by rfl⟩ : syracuseStep 2957249 = 2217937) B2217937
theorem B2809817 : Blo 1557476 2809817 := bstep (se 2 (by rfl) ⟨1053681, by rfl⟩ : syracuseStep 2809817 = 2107363) B2107363
theorem B8880131 : Blo 1557476 8880131 := bstep (se 1 (by rfl) ⟨6660098, by rfl⟩ : syracuseStep 8880131 = 13320197) B13320197
theorem B5259275 : Blo 1557476 5259275 := bstep (se 1 (by rfl) ⟨3944456, by rfl⟩ : syracuseStep 5259275 = 7888913) B7888913
theorem B8429579 : Blo 1557476 8429579 := bstep (se 1 (by rfl) ⟨6322184, by rfl⟩ : syracuseStep 8429579 = 12644369) B12644369
theorem B3506219 : Blo 1557476 3506219 := bstep (se 1 (by rfl) ⟨2629664, by rfl⟩ : syracuseStep 3506219 = 5259329) B5259329
theorem B11837501 : Blo 1557476 11837501 := bstep (se 3 (by rfl) ⟨2219531, by rfl⟩ : syracuseStep 11837501 = 4439063) B4439063
theorem B50561117 : Blo 1557476 50561117 := bstep (se 3 (by rfl) ⟨9480209, by rfl⟩ : syracuseStep 50561117 = 18960419) B18960419
theorem B5259383 : Blo 1557476 5259383 := bstep (se 1 (by rfl) ⟨3944537, by rfl⟩ : syracuseStep 5259383 = 7889075) B7889075
theorem B13312133 : Blo 1557476 13312133 := bstep (se 4 (by rfl) ⟨1248012, by rfl⟩ : syracuseStep 13312133 = 2496025) B2496025
theorem B2957447 : Blo 1557476 2957447 := bstep (se 1 (by rfl) ⟨2218085, by rfl⟩ : syracuseStep 2957447 = 4436171) B4436171
theorem B16851077 : Blo 1557476 16851077 := bstep (se 4 (by rfl) ⟨1579788, by rfl⟩ : syracuseStep 16851077 = 3159577) B3159577
theorem B1753231 : Blo 1557476 1753231 := bstep (se 1 (by rfl) ⟨1314923, by rfl⟩ : syracuseStep 1753231 = 2629847) B2629847
theorem B28442825 : Blo 1557476 28442825 := bstep (se 2 (by rfl) ⟨10666059, by rfl⟩ : syracuseStep 28442825 = 21332119) B21332119
theorem B1663291 : Blo 1557476 1663291 := bstep (se 1 (by rfl) ⟨1247468, by rfl⟩ : syracuseStep 1663291 = 2494937) B2494937
theorem B5915015 : Blo 1557476 5915015 := bstep (se 1 (by rfl) ⟨4436261, by rfl⟩ : syracuseStep 5915015 = 8872523) B8872523
theorem B3506579 : Blo 1557476 3506579 := bstep (se 1 (by rfl) ⟨2629934, by rfl⟩ : syracuseStep 3506579 = 5259869) B5259869
theorem B3326393 : Blo 1557476 3326393 := bstep (se 2 (by rfl) ⟨1247397, by rfl⟩ : syracuseStep 3326393 = 2494795) B2494795
theorem B3506633 : Blo 1557476 3506633 := bstep (se 2 (by rfl) ⟨1314987, by rfl⟩ : syracuseStep 3506633 = 2629975) B2629975
theorem B4440521 : Blo 1557476 4440521 := bstep (se 2 (by rfl) ⟨1665195, by rfl⟩ : syracuseStep 4440521 = 3330391) B3330391
theorem B8880587 : Blo 1557476 8880587 := bstep (se 1 (by rfl) ⟨6660440, by rfl⟩ : syracuseStep 8880587 = 13320881) B13320881
theorem B11829725 : Blo 1557476 11829725 := bstep (se 3 (by rfl) ⟨2218073, by rfl⟩ : syracuseStep 11829725 = 4436147) B4436147
theorem B3744299 : Blo 1557476 3744299 := bstep (se 1 (by rfl) ⟨2808224, by rfl⟩ : syracuseStep 3744299 = 5616449) B5616449
theorem B2630279 : Blo 1557476 2630279 := bstep (se 1 (by rfl) ⟨1972709, by rfl⟩ : syracuseStep 2630279 = 3945419) B3945419
theorem B1753735 : Blo 1557476 1753735 := bstep (se 1 (by rfl) ⟨1315301, by rfl⟩ : syracuseStep 1753735 = 2630603) B2630603
theorem B2957971 : Blo 1557476 2957971 := bstep (se 1 (by rfl) ⟨2218478, by rfl⟩ : syracuseStep 2957971 = 4436957) B4436957
theorem B5259977 : Blo 1557476 5259977 := bstep (se 2 (by rfl) ⟨1972491, by rfl⟩ : syracuseStep 5259977 = 3944983) B3944983
theorem B10658533 : Blo 1557476 10658533 := bstep (se 4 (by rfl) ⟨999237, by rfl⟩ : syracuseStep 10658533 = 1998475) B1998475
theorem B12640997 : Blo 1557476 12640997 := bstep (se 4 (by rfl) ⟨1185093, by rfl⟩ : syracuseStep 12640997 = 2370187) B2370187
theorem B8430317 : Blo 1557476 8430317 := bstep (se 3 (by rfl) ⟨1580684, by rfl⟩ : syracuseStep 8430317 = 3161369) B3161369
theorem B18965285 : Blo 1557476 18965285 := bstep (se 4 (by rfl) ⟨1777995, by rfl⟩ : syracuseStep 18965285 = 3555991) B3555991
theorem B7889723 : Blo 1557476 7889723 := bstep (se 1 (by rfl) ⟨5917292, by rfl⟩ : syracuseStep 7889723 = 11834585) B11834585
theorem B1753915 : Blo 1557476 1753915 := bstep (se 1 (by rfl) ⟨1315436, by rfl⟩ : syracuseStep 1753915 = 2630873) B2630873
theorem B7889885 : Blo 1557476 7889885 := bstep (se 3 (by rfl) ⟨1479353, by rfl⟩ : syracuseStep 7889885 = 2958707) B2958707
theorem B1557511 : Blo 1557476 1557511 := bstep (se 1 (by rfl) ⟨1168133, by rfl⟩ : syracuseStep 1557511 = 2336267) B2336267
theorem B1557519 : Blo 1557476 1557519 := bstep (se 1 (by rfl) ⟨1168139, by rfl⟩ : syracuseStep 1557519 = 2336279) B2336279
theorem B1557563 : Blo 1557476 1557563 := bstep (se 1 (by rfl) ⟨1168172, by rfl⟩ : syracuseStep 1557563 = 2336345) B2336345
theorem B8881271 : Blo 1557476 8881271 := bstep (se 1 (by rfl) ⟨6660953, by rfl⟩ : syracuseStep 8881271 = 13321907) B13321907
theorem B1557639 : Blo 1557476 1557639 := bstep (se 1 (by rfl) ⟨1168229, by rfl⟩ : syracuseStep 1557639 = 2336459) B2336459
theorem B3507335 : Blo 1557476 3507335 := bstep (se 1 (by rfl) ⟨2630501, by rfl⟩ : syracuseStep 3507335 = 5261003) B5261003
theorem B1557647 : Blo 1557476 1557647 := bstep (se 1 (by rfl) ⟨1168235, by rfl⟩ : syracuseStep 1557647 = 2336471) B2336471
theorem B1557691 : Blo 1557476 1557691 := bstep (se 1 (by rfl) ⟨1168268, by rfl⟩ : syracuseStep 1557691 = 2336537) B2336537
theorem B1557767 : Blo 1557476 1557767 := bstep (se 1 (by rfl) ⟨1168325, by rfl⟩ : syracuseStep 1557767 = 2336651) B2336651
theorem B1557775 : Blo 1557476 1557775 := bstep (se 1 (by rfl) ⟨1168331, by rfl⟩ : syracuseStep 1557775 = 2336663) B2336663
theorem B3327247 : Blo 1557476 3327247 := bstep (se 1 (by rfl) ⟨2495435, by rfl⟩ : syracuseStep 3327247 = 4990871) B4990871
theorem B2630927 : Blo 1557476 2630927 := bstep (se 1 (by rfl) ⟨1973195, by rfl⟩ : syracuseStep 2630927 = 3946391) B3946391
theorem B1754383 : Blo 1557476 1754383 := bstep (se 1 (by rfl) ⟨1315787, by rfl⟩ : syracuseStep 1754383 = 2631575) B2631575
theorem B31974689 : Blo 1557476 31974689 := bstep (se 2 (by rfl) ⟨11990508, by rfl⟩ : syracuseStep 31974689 = 23981017) B23981017
theorem B7890209 : Blo 1557476 7890209 := bstep (se 2 (by rfl) ⟨2958828, by rfl⟩ : syracuseStep 7890209 = 5917657) B5917657
theorem B1557819 : Blo 1557476 1557819 := bstep (se 1 (by rfl) ⟨1168364, by rfl⟩ : syracuseStep 1557819 = 2336729) B2336729
theorem B12633403 : Blo 1557476 12633403 := bstep (se 1 (by rfl) ⟨9475052, by rfl⟩ : syracuseStep 12633403 = 18950105) B18950105
theorem B3507515 : Blo 1557476 3507515 := bstep (se 1 (by rfl) ⟨2630636, by rfl⟩ : syracuseStep 3507515 = 5261273) B5261273
theorem B6653299 : Blo 1557476 6653299 := bstep (se 1 (by rfl) ⟨4989974, by rfl⟩ : syracuseStep 6653299 = 9979949) B9979949
theorem B1557895 : Blo 1557476 1557895 := bstep (se 1 (by rfl) ⟨1168421, by rfl⟩ : syracuseStep 1557895 = 2336843) B2336843
theorem B5260679 : Blo 1557476 5260679 := bstep (se 1 (by rfl) ⟨3945509, by rfl⟩ : syracuseStep 5260679 = 7891019) B7891019
theorem B1557903 : Blo 1557476 1557903 := bstep (se 1 (by rfl) ⟨1168427, by rfl⟩ : syracuseStep 1557903 = 2336855) B2336855
theorem B3507641 : Blo 1557476 3507641 := bstep (se 2 (by rfl) ⟨1315365, by rfl⟩ : syracuseStep 3507641 = 2630731) B2630731
theorem B1557947 : Blo 1557476 1557947 := bstep (se 1 (by rfl) ⟨1168460, by rfl⟩ : syracuseStep 1557947 = 2336921) B2336921
theorem B1558023 : Blo 1557476 1558023 := bstep (se 1 (by rfl) ⟨1168517, by rfl⟩ : syracuseStep 1558023 = 2337035) B2337035
theorem B1558031 : Blo 1557476 1558031 := bstep (se 1 (by rfl) ⟨1168523, by rfl⟩ : syracuseStep 1558031 = 2337047) B2337047
theorem B2336315 : Blo 1557476 2336315 := bstep (se 1 (by rfl) ⟨1752236, by rfl⟩ : syracuseStep 2336315 = 3504473) B3504473
theorem B1558075 : Blo 1557476 1558075 := bstep (se 1 (by rfl) ⟨1168556, by rfl⟩ : syracuseStep 1558075 = 2337113) B2337113
theorem B4212283 : Blo 1557476 4212283 := bstep (se 1 (by rfl) ⟨3159212, by rfl⟩ : syracuseStep 4212283 = 6318425) B6318425
theorem B2336375 : Blo 1557476 2336375 := bstep (se 1 (by rfl) ⟨1752281, by rfl⟩ : syracuseStep 2336375 = 3504563) B3504563
theorem B1558151 : Blo 1557476 1558151 := bstep (se 1 (by rfl) ⟨1168613, by rfl⟩ : syracuseStep 1558151 = 2337227) B2337227
theorem B2336399 : Blo 1557476 2336399 := bstep (se 1 (by rfl) ⟨1752299, by rfl⟩ : syracuseStep 2336399 = 3504599) B3504599
theorem B1558159 : Blo 1557476 1558159 := bstep (se 1 (by rfl) ⟨1168619, by rfl⟩ : syracuseStep 1558159 = 2337239) B2337239
theorem B2336441 : Blo 1557476 2336441 := bstep (se 2 (by rfl) ⟨876165, by rfl⟩ : syracuseStep 2336441 = 1752331) B1752331
theorem B1558203 : Blo 1557476 1558203 := bstep (se 1 (by rfl) ⟨1168652, by rfl⟩ : syracuseStep 1558203 = 2337305) B2337305
theorem B5261057 : Blo 1557476 5261057 := bstep (se 2 (by rfl) ⟨1972896, by rfl⟩ : syracuseStep 5261057 = 3945793) B3945793
theorem B2336519 : Blo 1557476 2336519 := bstep (se 1 (by rfl) ⟨1752389, by rfl⟩ : syracuseStep 2336519 = 3504779) B3504779
theorem B1558279 : Blo 1557476 1558279 := bstep (se 1 (by rfl) ⟨1168709, by rfl⟩ : syracuseStep 1558279 = 2337419) B2337419
theorem B1558287 : Blo 1557476 1558287 := bstep (se 1 (by rfl) ⟨1168715, by rfl⟩ : syracuseStep 1558287 = 2337431) B2337431
theorem B3507983 : Blo 1557476 3507983 := bstep (se 1 (by rfl) ⟨2630987, by rfl⟩ : syracuseStep 3507983 = 5261975) B5261975
theorem B3508001 : Blo 1557476 3508001 := bstep (se 2 (by rfl) ⟨1315500, by rfl⟩ : syracuseStep 3508001 = 2631001) B2631001
theorem B2336555 : Blo 1557476 2336555 := bstep (se 1 (by rfl) ⟨1752416, by rfl⟩ : syracuseStep 2336555 = 3504833) B3504833
theorem B2631467 : Blo 1557476 2631467 := bstep (se 1 (by rfl) ⟨1973600, by rfl⟩ : syracuseStep 2631467 = 3947201) B3947201
theorem B1558331 : Blo 1557476 1558331 := bstep (se 1 (by rfl) ⟨1168748, by rfl⟩ : syracuseStep 1558331 = 2337497) B2337497
theorem B2959163 : Blo 1557476 2959163 := bstep (se 1 (by rfl) ⟨2219372, by rfl⟩ : syracuseStep 2959163 = 4438745) B4438745
theorem B2336585 : Blo 1557476 2336585 := bstep (se 2 (by rfl) ⟨876219, by rfl⟩ : syracuseStep 2336585 = 1752439) B1752439
theorem B1558407 : Blo 1557476 1558407 := bstep (se 1 (by rfl) ⟨1168805, by rfl⟩ : syracuseStep 1558407 = 2337611) B2337611
theorem B1558415 : Blo 1557476 1558415 := bstep (se 1 (by rfl) ⟨1168811, by rfl⟩ : syracuseStep 1558415 = 2337623) B2337623
theorem B2336699 : Blo 1557476 2336699 := bstep (se 1 (by rfl) ⟨1752524, by rfl⟩ : syracuseStep 2336699 = 3505049) B3505049
theorem B1558459 : Blo 1557476 1558459 := bstep (se 1 (by rfl) ⟨1168844, by rfl⟩ : syracuseStep 1558459 = 2337689) B2337689
theorem B18958283 : Blo 1557476 18958283 := bstep (se 1 (by rfl) ⟨14218712, by rfl⟩ : syracuseStep 18958283 = 28437425) B28437425
theorem B2336759 : Blo 1557476 2336759 := bstep (se 1 (by rfl) ⟨1752569, by rfl⟩ : syracuseStep 2336759 = 3505139) B3505139
theorem B1558535 : Blo 1557476 1558535 := bstep (se 1 (by rfl) ⟨1168901, by rfl⟩ : syracuseStep 1558535 = 2337803) B2337803
theorem B2336783 : Blo 1557476 2336783 := bstep (se 1 (by rfl) ⟨1752587, by rfl⟩ : syracuseStep 2336783 = 3505175) B3505175
theorem B1558543 : Blo 1557476 1558543 := bstep (se 1 (by rfl) ⟨1168907, by rfl⟩ : syracuseStep 1558543 = 2337815) B2337815
theorem B2336825 : Blo 1557476 2336825 := bstep (se 2 (by rfl) ⟨876309, by rfl⟩ : syracuseStep 2336825 = 1752619) B1752619
theorem B1558587 : Blo 1557476 1558587 := bstep (se 1 (by rfl) ⟨1168940, by rfl⟩ : syracuseStep 1558587 = 2337881) B2337881
theorem B2107465 : Blo 1557476 2107465 := bstep (se 2 (by rfl) ⟨790299, by rfl⟩ : syracuseStep 2107465 = 1580599) B1580599
theorem B3508343 : Blo 1557476 3508343 := bstep (se 1 (by rfl) ⟨2631257, by rfl⟩ : syracuseStep 3508343 = 5262515) B5262515
theorem B2336903 : Blo 1557476 2336903 := bstep (se 1 (by rfl) ⟨1752677, by rfl⟩ : syracuseStep 2336903 = 3505355) B3505355
theorem B1558663 : Blo 1557476 1558663 := bstep (se 1 (by rfl) ⟨1168997, by rfl⟩ : syracuseStep 1558663 = 2337995) B2337995
theorem B1558671 : Blo 1557476 1558671 := bstep (se 1 (by rfl) ⟨1169003, by rfl⟩ : syracuseStep 1558671 = 2338007) B2338007
theorem B136726679 : Blo 1557476 136726679 := bstep (se 1 (by rfl) ⟨102545009, by rfl⟩ : syracuseStep 136726679 = 205090019) B205090019
theorem B3942553 : Blo 1557476 3942553 := bstep (se 2 (by rfl) ⟨1478457, by rfl⟩ : syracuseStep 3942553 = 2956915) B2956915
theorem B2336939 : Blo 1557476 2336939 := bstep (se 1 (by rfl) ⟨1752704, by rfl⟩ : syracuseStep 2336939 = 3505409) B3505409
theorem B1558715 : Blo 1557476 1558715 := bstep (se 1 (by rfl) ⟨1169036, by rfl⟩ : syracuseStep 1558715 = 2338073) B2338073
theorem B2336969 : Blo 1557476 2336969 := bstep (se 2 (by rfl) ⟨876363, by rfl⟩ : syracuseStep 2336969 = 1752727) B1752727
theorem B7891181 : Blo 1557476 7891181 := bstep (se 3 (by rfl) ⟨1479596, by rfl⟩ : syracuseStep 7891181 = 2959193) B2959193
theorem B1558791 : Blo 1557476 1558791 := bstep (se 1 (by rfl) ⟨1169093, by rfl⟩ : syracuseStep 1558791 = 2338187) B2338187
theorem B1558799 : Blo 1557476 1558799 := bstep (se 1 (by rfl) ⟨1169099, by rfl⟩ : syracuseStep 1558799 = 2338199) B2338199
theorem B2959649 : Blo 1557476 2959649 := bstep (se 2 (by rfl) ⟨1109868, by rfl⟩ : syracuseStep 2959649 = 2219737) B2219737
theorem B3508523 : Blo 1557476 3508523 := bstep (se 1 (by rfl) ⟨2631392, by rfl⟩ : syracuseStep 3508523 = 5262785) B5262785
theorem B3942715 : Blo 1557476 3942715 := bstep (se 1 (by rfl) ⟨2957036, by rfl⟩ : syracuseStep 3942715 = 5914073) B5914073
theorem B2337083 : Blo 1557476 2337083 := bstep (se 1 (by rfl) ⟨1752812, by rfl⟩ : syracuseStep 2337083 = 3505625) B3505625
theorem B8874299 : Blo 1557476 8874299 := bstep (se 1 (by rfl) ⟨6655724, by rfl⟩ : syracuseStep 8874299 = 13311449) B13311449
theorem B1558843 : Blo 1557476 1558843 := bstep (se 1 (by rfl) ⟨1169132, by rfl⟩ : syracuseStep 1558843 = 2338265) B2338265
theorem B2337143 : Blo 1557476 2337143 := bstep (se 1 (by rfl) ⟨1752857, by rfl⟩ : syracuseStep 2337143 = 3505715) B3505715
theorem B1558919 : Blo 1557476 1558919 := bstep (se 1 (by rfl) ⟨1169189, by rfl⟩ : syracuseStep 1558919 = 2338379) B2338379
theorem B2337167 : Blo 1557476 2337167 := bstep (se 1 (by rfl) ⟨1752875, by rfl⟩ : syracuseStep 2337167 = 3505751) B3505751
theorem B1558927 : Blo 1557476 1558927 := bstep (se 1 (by rfl) ⟨1169195, by rfl⟩ : syracuseStep 1558927 = 2338391) B2338391
theorem B2337209 : Blo 1557476 2337209 := bstep (se 2 (by rfl) ⟨876453, by rfl⟩ : syracuseStep 2337209 = 1752907) B1752907
theorem B1558971 : Blo 1557476 1558971 := bstep (se 1 (by rfl) ⟨1169228, by rfl⟩ : syracuseStep 1558971 = 2338457) B2338457
theorem B3942857 : Blo 1557476 3942857 := bstep (se 2 (by rfl) ⟨1478571, by rfl⟩ : syracuseStep 3942857 = 2957143) B2957143
theorem B34621937 : Blo 1557476 34621937 := bstep (se 2 (by rfl) ⟨12983226, by rfl⟩ : syracuseStep 34621937 = 25966453) B25966453
theorem B2337287 : Blo 1557476 2337287 := bstep (se 1 (by rfl) ⟨1752965, by rfl⟩ : syracuseStep 2337287 = 3505931) B3505931
theorem B1559047 : Blo 1557476 1559047 := bstep (se 1 (by rfl) ⟨1169285, by rfl⟩ : syracuseStep 1559047 = 2338571) B2338571
theorem B1559055 : Blo 1557476 1559055 := bstep (se 1 (by rfl) ⟨1169291, by rfl⟩ : syracuseStep 1559055 = 2338583) B2338583
theorem B2337323 : Blo 1557476 2337323 := bstep (se 1 (by rfl) ⟨1752992, by rfl⟩ : syracuseStep 2337323 = 3505985) B3505985
theorem B5261867 : Blo 1557476 5261867 := bstep (se 1 (by rfl) ⟨3946400, by rfl⟩ : syracuseStep 5261867 = 7892801) B7892801
theorem B2959915 : Blo 1557476 2959915 := bstep (se 1 (by rfl) ⟨2219936, by rfl⟩ : syracuseStep 2959915 = 4439873) B4439873
theorem B1559099 : Blo 1557476 1559099 := bstep (se 1 (by rfl) ⟨1169324, by rfl⟩ : syracuseStep 1559099 = 2338649) B2338649
theorem B2337353 : Blo 1557476 2337353 := bstep (se 2 (by rfl) ⟨876507, by rfl⟩ : syracuseStep 2337353 = 1753015) B1753015
theorem B4737623 : Blo 1557476 4737623 := bstep (se 1 (by rfl) ⟨3553217, by rfl⟩ : syracuseStep 4737623 = 7106435) B7106435
theorem B1559175 : Blo 1557476 1559175 := bstep (se 1 (by rfl) ⟨1169381, by rfl⟩ : syracuseStep 1559175 = 2338763) B2338763
theorem B1559183 : Blo 1557476 1559183 := bstep (se 1 (by rfl) ⟨1169387, by rfl⟩ : syracuseStep 1559183 = 2338775) B2338775
theorem B2337467 : Blo 1557476 2337467 := bstep (se 1 (by rfl) ⟨1753100, by rfl⟩ : syracuseStep 2337467 = 3506201) B3506201
theorem B1559227 : Blo 1557476 1559227 := bstep (se 1 (by rfl) ⟨1169420, by rfl⟩ : syracuseStep 1559227 = 2338841) B2338841
theorem B11995877 : Blo 1557476 11995877 := bstep (se 4 (by rfl) ⟨1124613, by rfl⟩ : syracuseStep 11995877 = 2249227) B2249227
theorem B2337527 : Blo 1557476 2337527 := bstep (se 1 (by rfl) ⟨1753145, by rfl⟩ : syracuseStep 2337527 = 3506291) B3506291
theorem B1559303 : Blo 1557476 1559303 := bstep (se 1 (by rfl) ⟨1169477, by rfl⟩ : syracuseStep 1559303 = 2338955) B2338955
theorem B2337551 : Blo 1557476 2337551 := bstep (se 1 (by rfl) ⟨1753163, by rfl⟩ : syracuseStep 2337551 = 3506327) B3506327
theorem B1559311 : Blo 1557476 1559311 := bstep (se 1 (by rfl) ⟨1169483, by rfl⟩ : syracuseStep 1559311 = 2338967) B2338967
theorem B3943201 : Blo 1557476 3943201 := bstep (se 2 (by rfl) ⟨1478700, by rfl⟩ : syracuseStep 3943201 = 2957401) B2957401
theorem B2337593 : Blo 1557476 2337593 := bstep (se 2 (by rfl) ⟨876597, by rfl⟩ : syracuseStep 2337593 = 1753195) B1753195
theorem B1559355 : Blo 1557476 1559355 := bstep (se 1 (by rfl) ⟨1169516, by rfl⟩ : syracuseStep 1559355 = 2339033) B2339033
theorem B2337671 : Blo 1557476 2337671 := bstep (se 1 (by rfl) ⟨1753253, by rfl⟩ : syracuseStep 2337671 = 3506507) B3506507
theorem B1559431 : Blo 1557476 1559431 := bstep (se 1 (by rfl) ⟨1169573, by rfl⟩ : syracuseStep 1559431 = 2339147) B2339147
theorem B1559439 : Blo 1557476 1559439 := bstep (se 1 (by rfl) ⟨1169579, by rfl⟩ : syracuseStep 1559439 = 2339159) B2339159
theorem B2337707 : Blo 1557476 2337707 := bstep (se 1 (by rfl) ⟨1753280, by rfl⟩ : syracuseStep 2337707 = 3506561) B3506561
theorem B6654905 : Blo 1557476 6654905 := bstep (se 2 (by rfl) ⟨2495589, by rfl⟩ : syracuseStep 6654905 = 4991179) B4991179
theorem B2337737 : Blo 1557476 2337737 := bstep (se 2 (by rfl) ⟨876651, by rfl⟩ : syracuseStep 2337737 = 1753303) B1753303
theorem B7891991 : Blo 1557476 7891991 := bstep (se 1 (by rfl) ⟨5918993, by rfl⟩ : syracuseStep 7891991 = 11837987) B11837987
theorem B2337851 : Blo 1557476 2337851 := bstep (se 1 (by rfl) ⟨1753388, by rfl⟩ : syracuseStep 2337851 = 3506777) B3506777
theorem B9481283 : Blo 1557476 9481283 := bstep (se 1 (by rfl) ⟨7110962, by rfl⟩ : syracuseStep 9481283 = 14221925) B14221925
theorem B2337911 : Blo 1557476 2337911 := bstep (se 1 (by rfl) ⟨1753433, by rfl⟩ : syracuseStep 2337911 = 3506867) B3506867
theorem B2337935 : Blo 1557476 2337935 := bstep (se 1 (by rfl) ⟨1753451, by rfl⟩ : syracuseStep 2337935 = 3506903) B3506903
theorem B2337977 : Blo 1557476 2337977 := bstep (se 2 (by rfl) ⟨876741, by rfl⟩ : syracuseStep 2337977 = 1753483) B1753483
theorem B2338055 : Blo 1557476 2338055 := bstep (se 1 (by rfl) ⟨1753541, by rfl⟩ : syracuseStep 2338055 = 3507083) B3507083
theorem B6655247 : Blo 1557476 6655247 := bstep (se 1 (by rfl) ⟨4991435, by rfl⟩ : syracuseStep 6655247 = 9982871) B9982871
theorem B2338091 : Blo 1557476 2338091 := bstep (se 1 (by rfl) ⟨1753568, by rfl⟩ : syracuseStep 2338091 = 3507137) B3507137
theorem B2338121 : Blo 1557476 2338121 := bstep (se 2 (by rfl) ⟨876795, by rfl⟩ : syracuseStep 2338121 = 1753591) B1753591
theorem B16215389 : Blo 1557476 16215389 := bstep (se 3 (by rfl) ⟨3040385, by rfl⟩ : syracuseStep 16215389 = 6080771) B6080771
theorem B3943799 : Blo 1557476 3943799 := bstep (se 1 (by rfl) ⟨2957849, by rfl⟩ : syracuseStep 3943799 = 5915699) B5915699
theorem B33680771 : Blo 1557476 33680771 := bstep (se 1 (by rfl) ⟨25260578, by rfl⟩ : syracuseStep 33680771 = 50521157) B50521157
theorem B17755523 : Blo 1557476 17755523 := bstep (se 1 (by rfl) ⟨13316642, by rfl⟩ : syracuseStep 17755523 = 26633285) B26633285
theorem B11840903 : Blo 1557476 11840903 := bstep (se 1 (by rfl) ⟨8880677, by rfl⟩ : syracuseStep 11840903 = 17761355) B17761355
theorem B2338235 : Blo 1557476 2338235 := bstep (se 1 (by rfl) ⟨1753676, by rfl⟩ : syracuseStep 2338235 = 3507353) B3507353
theorem B13315549 : Blo 1557476 13315549 := bstep (se 3 (by rfl) ⟨2496665, by rfl⟩ : syracuseStep 13315549 = 4993331) B4993331
theorem B2338295 : Blo 1557476 2338295 := bstep (se 1 (by rfl) ⟨1753721, by rfl⟩ : syracuseStep 2338295 = 3507443) B3507443
theorem B2338319 : Blo 1557476 2338319 := bstep (se 1 (by rfl) ⟨1753739, by rfl⟩ : syracuseStep 2338319 = 3507479) B3507479
theorem B4435499 : Blo 1557476 4435499 := bstep (se 1 (by rfl) ⟨3326624, by rfl⟩ : syracuseStep 4435499 = 6653249) B6653249
theorem B2338361 : Blo 1557476 2338361 := bstep (se 2 (by rfl) ⟨876885, by rfl⟩ : syracuseStep 2338361 = 1753771) B1753771
theorem B1871419 : Blo 1557476 1871419 := bstep (se 1 (by rfl) ⟨1403564, by rfl⟩ : syracuseStep 1871419 = 2807129) B2807129
theorem B11226691 : Blo 1557476 11226691 := bstep (se 1 (by rfl) ⟨8420018, by rfl⟩ : syracuseStep 11226691 = 16840037) B16840037
theorem B5615191 : Blo 1557476 5615191 := bstep (se 1 (by rfl) ⟨4211393, by rfl⟩ : syracuseStep 5615191 = 8422787) B8422787
theorem B2338439 : Blo 1557476 2338439 := bstep (se 1 (by rfl) ⟨1753829, by rfl⟩ : syracuseStep 2338439 = 3507659) B3507659
theorem B2338475 : Blo 1557476 2338475 := bstep (se 1 (by rfl) ⟨1753856, by rfl⟩ : syracuseStep 2338475 = 3507713) B3507713
theorem B2338505 : Blo 1557476 2338505 := bstep (se 2 (by rfl) ⟨876939, by rfl⟩ : syracuseStep 2338505 = 1753879) B1753879
theorem B8875757 : Blo 1557476 8875757 := bstep (se 3 (by rfl) ⟨1664204, by rfl⟩ : syracuseStep 8875757 = 3328409) B3328409
theorem B2338619 : Blo 1557476 2338619 := bstep (se 1 (by rfl) ⟨1753964, by rfl⟩ : syracuseStep 2338619 = 3507929) B3507929
theorem B5263163 : Blo 1557476 5263163 := bstep (se 1 (by rfl) ⟨3947372, by rfl⟩ : syracuseStep 5263163 = 7894745) B7894745
theorem B2338679 : Blo 1557476 2338679 := bstep (se 1 (by rfl) ⟨1754009, by rfl⟩ : syracuseStep 2338679 = 3508019) B3508019
theorem B2338703 : Blo 1557476 2338703 := bstep (se 1 (by rfl) ⟨1754027, by rfl⟩ : syracuseStep 2338703 = 3508055) B3508055
theorem B4214681 : Blo 1557476 4214681 := bstep (se 2 (by rfl) ⟨1580505, by rfl⟩ : syracuseStep 4214681 = 3161011) B3161011
theorem B4435897 : Blo 1557476 4435897 := bstep (se 2 (by rfl) ⟨1663461, by rfl⟩ : syracuseStep 4435897 = 3326923) B3326923
theorem B2338745 : Blo 1557476 2338745 := bstep (se 2 (by rfl) ⟨877029, by rfl⟩ : syracuseStep 2338745 = 1754059) B1754059
theorem B2338823 : Blo 1557476 2338823 := bstep (se 1 (by rfl) ⟨1754117, by rfl⟩ : syracuseStep 2338823 = 3508235) B3508235
theorem B2338859 : Blo 1557476 2338859 := bstep (se 1 (by rfl) ⟨1754144, by rfl⟩ : syracuseStep 2338859 = 3508289) B3508289
theorem B4214845 : Blo 1557476 4214845 := bstep (se 3 (by rfl) ⟨790283, by rfl⟩ : syracuseStep 4214845 = 1580567) B1580567
theorem B2338889 : Blo 1557476 2338889 := bstep (se 2 (by rfl) ⟨877083, by rfl⟩ : syracuseStep 2338889 = 1754167) B1754167
theorem B2339003 : Blo 1557476 2339003 := bstep (se 1 (by rfl) ⟨1754252, by rfl⟩ : syracuseStep 2339003 = 3508505) B3508505
theorem B2339063 : Blo 1557476 2339063 := bstep (se 1 (by rfl) ⟨1754297, by rfl⟩ : syracuseStep 2339063 = 3508595) B3508595
theorem B2339087 : Blo 1557476 2339087 := bstep (se 1 (by rfl) ⟨1754315, by rfl⟩ : syracuseStep 2339087 = 3508631) B3508631
theorem B2339129 : Blo 1557476 2339129 := bstep (se 2 (by rfl) ⟨877173, by rfl⟩ : syracuseStep 2339129 = 1754347) B1754347
theorem B2339207 : Blo 1557476 2339207 := bstep (se 1 (by rfl) ⟨1754405, by rfl⟩ : syracuseStep 2339207 = 3508811) B3508811
theorem B19968403 : Blo 1557476 19968403 := bstep (se 1 (by rfl) ⟨14976302, by rfl⟩ : syracuseStep 19968403 = 29952605) B29952605
theorem B4215311 : Blo 1557476 4215311 := bstep (se 1 (by rfl) ⟨3161483, by rfl⟩ : syracuseStep 4215311 = 6322967) B6322967
theorem B3945095 : Blo 1557476 3945095 := bstep (se 1 (by rfl) ⟨2958821, by rfl⟩ : syracuseStep 3945095 = 5917643) B5917643
theorem B3945145 : Blo 1557476 3945145 := bstep (se 2 (by rfl) ⟨1479429, by rfl⟩ : syracuseStep 3945145 = 2958859) B2958859
theorem B3289871 : Blo 1557476 3289871 := bstep (se 1 (by rfl) ⟨2467403, by rfl⟩ : syracuseStep 3289871 = 4934807) B4934807
theorem B19960613 : Blo 1557476 19960613 := bstep (se 4 (by rfl) ⟨1871307, by rfl⟩ : syracuseStep 19960613 = 3742615) B3742615
theorem B7885835 : Blo 1557476 7885835 := bstep (se 1 (by rfl) ⟨5914376, by rfl⟩ : syracuseStep 7885835 = 11828753) B11828753
theorem B4437139 : Blo 1557476 4437139 := bstep (se 1 (by rfl) ⟨3327854, by rfl⟩ : syracuseStep 4437139 = 6655709) B6655709
theorem B7885997 : Blo 1557476 7885997 := bstep (se 3 (by rfl) ⟨1478624, by rfl⟩ : syracuseStep 7885997 = 2957249) B2957249
theorem B3945743 : Blo 1557476 3945743 := bstep (se 1 (by rfl) ⟨2959307, by rfl⟩ : syracuseStep 3945743 = 5918615) B5918615
theorem B1873211 : Blo 1557476 1873211 := bstep (se 1 (by rfl) ⟨1404908, by rfl⟩ : syracuseStep 1873211 = 2809817) B2809817
theorem B72955313 : Blo 1557476 72955313 := bstep (se 2 (by rfl) ⟨27358242, by rfl⟩ : syracuseStep 72955313 = 54716485) B54716485
theorem B153744913 : Blo 1557476 153744913 := bstep (se 2 (by rfl) ⟨57654342, by rfl⟩ : syracuseStep 153744913 = 115308685) B115308685
theorem B5256791 : Blo 1557476 5256791 := bstep (se 1 (by rfl) ⟨3942593, by rfl⟩ : syracuseStep 5256791 = 7885187) B7885187
theorem B6657623 : Blo 1557476 6657623 := bstep (se 1 (by rfl) ⟨4993217, by rfl⟩ : syracuseStep 6657623 = 9986435) B9986435
theorem B3200647 : Blo 1557476 3200647 := bstep (se 1 (by rfl) ⟨2400485, by rfl⟩ : syracuseStep 3200647 = 4800971) B4800971
theorem B5617441 : Blo 1557476 5617441 := bstep (se 2 (by rfl) ⟨2106540, by rfl⟩ : syracuseStep 5617441 = 4213081) B4213081
theorem B9983897 : Blo 1557476 9983897 := bstep (se 2 (by rfl) ⟨3743961, by rfl⟩ : syracuseStep 9983897 = 7487923) B7487923
theorem B3946441 : Blo 1557476 3946441 := bstep (se 2 (by rfl) ⟨1479915, by rfl⟩ : syracuseStep 3946441 = 2959831) B2959831
theorem B22763467 : Blo 1557476 22763467 := bstep (se 1 (by rfl) ⟨17072600, by rfl⟩ : syracuseStep 22763467 = 34145201) B34145201
theorem B4995101 : Blo 1557476 4995101 := bstep (se 3 (by rfl) ⟨936581, by rfl⟩ : syracuseStep 4995101 = 1873163) B1873163
theorem B38426669 : Blo 1557476 38426669 := bstep (se 3 (by rfl) ⟨7205000, by rfl⟩ : syracuseStep 38426669 = 14410001) B14410001
theorem B5257277 : Blo 1557476 5257277 := bstep (se 3 (by rfl) ⟨985739, by rfl⟩ : syracuseStep 5257277 = 1971479) B1971479
theorem B4388951 : Blo 1557476 4388951 := bstep (se 1 (by rfl) ⟨3291713, by rfl⟩ : syracuseStep 4388951 = 6583427) B6583427
theorem B3946583 : Blo 1557476 3946583 := bstep (se 1 (by rfl) ⟨2959937, by rfl⟩ : syracuseStep 3946583 = 5919875) B5919875
theorem B3504329 : Blo 1557476 3504329 := bstep (se 2 (by rfl) ⟨1314123, by rfl⟩ : syracuseStep 3504329 = 2628247) B2628247
theorem B67426577 : Blo 1557476 67426577 := bstep (se 2 (by rfl) ⟨25284966, by rfl⟩ : syracuseStep 67426577 = 50569933) B50569933
theorem B4741409 : Blo 1557476 4741409 := bstep (se 2 (by rfl) ⟨1778028, by rfl⟩ : syracuseStep 4741409 = 3556057) B3556057
theorem B2218313 : Blo 1557476 2218313 := bstep (se 2 (by rfl) ⟨831867, by rfl⟩ : syracuseStep 2218313 = 1663735) B1663735
theorem B30366251 : Blo 1557476 30366251 := bstep (se 1 (by rfl) ⟨22774688, by rfl⟩ : syracuseStep 30366251 = 45549377) B45549377
theorem B17742401 : Blo 1557476 17742401 := bstep (se 2 (by rfl) ⟨6653400, by rfl⟩ : syracuseStep 17742401 = 13306801) B13306801
theorem B8428151 : Blo 1557476 8428151 := bstep (se 1 (by rfl) ⟨6321113, by rfl⟩ : syracuseStep 8428151 = 12642227) B12642227
theorem B2628281 : Blo 1557476 2628281 := bstep (se 2 (by rfl) ⟨985605, by rfl⟩ : syracuseStep 2628281 = 1971211) B1971211
theorem B2702009 : Blo 1557476 2702009 := bstep (se 2 (by rfl) ⟨1013253, by rfl⟩ : syracuseStep 2702009 = 2026507) B2026507
theorem B7887617 : Blo 1557476 7887617 := bstep (se 2 (by rfl) ⟨2957856, by rfl⟩ : syracuseStep 7887617 = 5915713) B5915713
theorem B4438813 : Blo 1557476 4438813 := bstep (se 3 (by rfl) ⟨832277, by rfl⟩ : syracuseStep 4438813 = 1664555) B1664555
theorem B30358309 : Blo 1557476 30358309 := bstep (se 4 (by rfl) ⟨2846091, by rfl⟩ : syracuseStep 30358309 = 5692183) B5692183
theorem B4438871 : Blo 1557476 4438871 := bstep (se 1 (by rfl) ⟨3329153, by rfl⟩ : syracuseStep 4438871 = 6658307) B6658307
theorem B2218871 : Blo 1557476 2218871 := bstep (se 1 (by rfl) ⟨1664153, by rfl⟩ : syracuseStep 2218871 = 3328307) B3328307
theorem B3505031 : Blo 1557476 3505031 := bstep (se 1 (by rfl) ⟨2628773, by rfl⟩ : syracuseStep 3505031 = 5257547) B5257547
theorem B12639179 : Blo 1557476 12639179 := bstep (se 1 (by rfl) ⟨9479384, by rfl⟩ : syracuseStep 12639179 = 18958769) B18958769
theorem B3505211 : Blo 1557476 3505211 := bstep (se 1 (by rfl) ⟨2628908, by rfl⟩ : syracuseStep 3505211 = 5257817) B5257817
theorem B17988725 : Blo 1557476 17988725 := bstep (se 5 (by rfl) ⟨843221, by rfl⟩ : syracuseStep 17988725 = 1686443) B1686443
theorem B3161207 : Blo 1557476 3161207 := bstep (se 1 (by rfl) ⟨2370905, by rfl⟩ : syracuseStep 3161207 = 4741811) B4741811
theorem B2219179 : Blo 1557476 2219179 := bstep (se 1 (by rfl) ⟨1664384, by rfl⟩ : syracuseStep 2219179 = 3328769) B3328769
theorem B3505337 : Blo 1557476 3505337 := bstep (se 2 (by rfl) ⟨1314501, by rfl⟩ : syracuseStep 3505337 = 2629003) B2629003
theorem B2497807 : Blo 1557476 2497807 := bstep (se 1 (by rfl) ⟨1873355, by rfl⟩ : syracuseStep 2497807 = 3746711) B3746711
theorem B2628983 : Blo 1557476 2628983 := bstep (se 1 (by rfl) ⟨1971737, by rfl⟩ : syracuseStep 2628983 = 3943475) B3943475
theorem B5258681 : Blo 1557476 5258681 := bstep (se 2 (by rfl) ⟨1972005, by rfl⟩ : syracuseStep 5258681 = 3944011) B3944011
theorem B8420867 : Blo 1557476 8420867 := bstep (se 1 (by rfl) ⟨6315650, by rfl⟩ : syracuseStep 8420867 = 12631301) B12631301
theorem B1752583 : Blo 1557476 1752583 := bstep (se 1 (by rfl) ⟨1314437, by rfl⟩ : syracuseStep 1752583 = 2628875) B2628875
theorem B3505679 : Blo 1557476 3505679 := bstep (se 1 (by rfl) ⟨2629259, by rfl⟩ : syracuseStep 3505679 = 5258519) B5258519
theorem B3505697 : Blo 1557476 3505697 := bstep (se 2 (by rfl) ⟨1314636, by rfl⟩ : syracuseStep 3505697 = 2629273) B2629273
theorem B7888427 : Blo 1557476 7888427 := bstep (se 1 (by rfl) ⟨5916320, by rfl⟩ : syracuseStep 7888427 = 11832641) B11832641
theorem B15187499 : Blo 1557476 15187499 := bstep (se 1 (by rfl) ⟨11390624, by rfl⟩ : syracuseStep 15187499 = 22781249) B22781249
theorem B5480023 : Blo 1557476 5480023 := bstep (se 1 (by rfl) ⟨4110017, by rfl⟩ : syracuseStep 5480023 = 8220035) B8220035
theorem B5619287 : Blo 1557476 5619287 := bstep (se 1 (by rfl) ⟨4214465, by rfl⟩ : syracuseStep 5619287 = 8428931) B8428931
theorem B3743347 : Blo 1557476 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B2219663 : Blo 1557476 2219663 := bstep (se 1 (by rfl) ⟨1664747, by rfl⟩ : syracuseStep 2219663 = 3329495) B3329495
theorem B1752763 : Blo 1557476 1752763 := bstep (se 1 (by rfl) ⟨1314572, by rfl⟩ : syracuseStep 1752763 = 2629145) B2629145
theorem B2629435 : Blo 1557476 2629435 := bstep (se 1 (by rfl) ⟨1972076, by rfl⟩ : syracuseStep 2629435 = 3944153) B3944153
theorem B3506039 : Blo 1557476 3506039 := bstep (se 1 (by rfl) ⟨2629529, by rfl⟩ : syracuseStep 3506039 = 5259059) B5259059
theorem B2629577 : Blo 1557476 2629577 := bstep (se 2 (by rfl) ⟨986091, by rfl⟩ : syracuseStep 2629577 = 1972183) B1972183
theorem B3506183 : Blo 1557476 3506183 := bstep (se 1 (by rfl) ⟨2629637, by rfl⟩ : syracuseStep 3506183 = 5259275) B5259275
theorem B5619719 : Blo 1557476 5619719 := bstep (se 1 (by rfl) ⟨4214789, by rfl⟩ : syracuseStep 5619719 = 8429579) B8429579
theorem B3506255 : Blo 1557476 3506255 := bstep (se 1 (by rfl) ⟨2629691, by rfl⟩ : syracuseStep 3506255 = 5259383) B5259383
theorem B5619793 : Blo 1557476 5619793 := bstep (se 2 (by rfl) ⟨2107422, by rfl⟩ : syracuseStep 5619793 = 4214845) B4214845
theorem B2810207 : Blo 1557476 2810207 := bstep (se 1 (by rfl) ⟨2107655, by rfl⟩ : syracuseStep 2810207 = 4215311) B4215311
theorem B59875685 : Blo 1557476 59875685 := bstep (se 4 (by rfl) ⟨5613345, by rfl⟩ : syracuseStep 59875685 = 11226691) B11226691
theorem B11239813 : Blo 1557476 11239813 := bstep (se 4 (by rfl) ⟨1053732, by rfl⟩ : syracuseStep 11239813 = 2107465) B2107465
theorem B2630063 : Blo 1557476 2630063 := bstep (se 1 (by rfl) ⟨1972547, by rfl⟩ : syracuseStep 2630063 = 3945095) B3945095
theorem B1753519 : Blo 1557476 1753519 := bstep (se 1 (by rfl) ⟨1315139, by rfl⟩ : syracuseStep 1753519 = 2630279) B2630279
theorem B3506651 : Blo 1557476 3506651 := bstep (se 1 (by rfl) ⟨2629988, by rfl⟩ : syracuseStep 3506651 = 5259977) B5259977
theorem B5620211 : Blo 1557476 5620211 := bstep (se 1 (by rfl) ⟨4215158, by rfl⟩ : syracuseStep 5620211 = 8430317) B8430317
theorem B26624537 : Blo 1557476 26624537 := bstep (se 2 (by rfl) ⟨9984201, by rfl⟩ : syracuseStep 26624537 = 19968403) B19968403
theorem B5259815 : Blo 1557476 5259815 := bstep (se 1 (by rfl) ⟨3944861, by rfl⟩ : syracuseStep 5259815 = 7889723) B7889723
theorem B5259923 : Blo 1557476 5259923 := bstep (se 1 (by rfl) ⟨3944942, by rfl⟩ : syracuseStep 5259923 = 7889885) B7889885
theorem B2630495 : Blo 1557476 2630495 := bstep (se 1 (by rfl) ⟨1972871, by rfl⟩ : syracuseStep 2630495 = 3945743) B3945743
theorem B1753951 : Blo 1557476 1753951 := bstep (se 1 (by rfl) ⟨1315463, by rfl⟩ : syracuseStep 1753951 = 2630927) B2630927
theorem B21316459 : Blo 1557476 21316459 := bstep (se 1 (by rfl) ⟨15987344, by rfl⟩ : syracuseStep 21316459 = 31974689) B31974689
theorem B5260139 : Blo 1557476 5260139 := bstep (se 1 (by rfl) ⟨3945104, by rfl⟩ : syracuseStep 5260139 = 7890209) B7890209
theorem B5915501 : Blo 1557476 5915501 := bstep (se 3 (by rfl) ⟨1109156, by rfl⟩ : syracuseStep 5915501 = 2218313) B2218313
theorem B5260193 : Blo 1557476 5260193 := bstep (se 2 (by rfl) ⟨1972572, by rfl⟩ : syracuseStep 5260193 = 3945145) B3945145
theorem B3507119 : Blo 1557476 3507119 := bstep (se 1 (by rfl) ⟨2630339, by rfl⟩ : syracuseStep 3507119 = 5260679) B5260679
theorem B48636875 : Blo 1557476 48636875 := bstep (se 1 (by rfl) ⟨36477656, by rfl⟩ : syracuseStep 48636875 = 72955313) B72955313
theorem B1557543 : Blo 1557476 1557543 := bstep (se 1 (by rfl) ⟨1168157, by rfl⟩ : syracuseStep 1557543 = 2336315) B2336315
theorem B40477745 : Blo 1557476 40477745 := bstep (se 2 (by rfl) ⟨15179154, by rfl⟩ : syracuseStep 40477745 = 30358309) B30358309
theorem B1557583 : Blo 1557476 1557583 := bstep (se 1 (by rfl) ⟨1168187, by rfl⟩ : syracuseStep 1557583 = 2336375) B2336375
theorem B1557599 : Blo 1557476 1557599 := bstep (se 1 (by rfl) ⟨1168199, by rfl⟩ : syracuseStep 1557599 = 2336399) B2336399
theorem B1557627 : Blo 1557476 1557627 := bstep (se 1 (by rfl) ⟨1168220, by rfl⟩ : syracuseStep 1557627 = 2336441) B2336441
theorem B3507371 : Blo 1557476 3507371 := bstep (se 1 (by rfl) ⟨2630528, by rfl⟩ : syracuseStep 3507371 = 5261057) B5261057
theorem B1557679 : Blo 1557476 1557679 := bstep (se 1 (by rfl) ⟨1168259, by rfl⟩ : syracuseStep 1557679 = 2336519) B2336519
theorem B1557703 : Blo 1557476 1557703 := bstep (se 1 (by rfl) ⟨1168277, by rfl⟩ : syracuseStep 1557703 = 2336555) B2336555
theorem B1754311 : Blo 1557476 1754311 := bstep (se 1 (by rfl) ⟨1315733, by rfl⟩ : syracuseStep 1754311 = 2631467) B2631467
theorem B1557723 : Blo 1557476 1557723 := bstep (se 1 (by rfl) ⟨1168292, by rfl⟩ : syracuseStep 1557723 = 2336585) B2336585
theorem B1557799 : Blo 1557476 1557799 := bstep (se 1 (by rfl) ⟨1168349, by rfl⟩ : syracuseStep 1557799 = 2336699) B2336699
theorem B1557839 : Blo 1557476 1557839 := bstep (se 1 (by rfl) ⟨1168379, by rfl⟩ : syracuseStep 1557839 = 2336759) B2336759
theorem B1557855 : Blo 1557476 1557855 := bstep (se 1 (by rfl) ⟨1168391, by rfl⟩ : syracuseStep 1557855 = 2336783) B2336783
theorem B25617779 : Blo 1557476 25617779 := bstep (se 1 (by rfl) ⟨19213334, by rfl⟩ : syracuseStep 25617779 = 38426669) B38426669
theorem B1557883 : Blo 1557476 1557883 := bstep (se 1 (by rfl) ⟨1168412, by rfl⟩ : syracuseStep 1557883 = 2336825) B2336825
theorem B2925967 : Blo 1557476 2925967 := bstep (se 1 (by rfl) ⟨2194475, by rfl⟩ : syracuseStep 2925967 = 4388951) B4388951
theorem B2631055 : Blo 1557476 2631055 := bstep (se 1 (by rfl) ⟨1973291, by rfl⟩ : syracuseStep 2631055 = 3946583) B3946583
theorem B17745317 : Blo 1557476 17745317 := bstep (se 4 (by rfl) ⟨1663623, by rfl⟩ : syracuseStep 17745317 = 3327247) B3327247
theorem B1557935 : Blo 1557476 1557935 := bstep (se 1 (by rfl) ⟨1168451, by rfl⟩ : syracuseStep 1557935 = 2336903) B2336903
theorem B1557959 : Blo 1557476 1557959 := bstep (se 1 (by rfl) ⟨1168469, by rfl⟩ : syracuseStep 1557959 = 2336939) B2336939
theorem B2336219 : Blo 1557476 2336219 := bstep (se 1 (by rfl) ⟨1752164, by rfl⟩ : syracuseStep 2336219 = 3504329) B3504329
theorem B1557979 : Blo 1557476 1557979 := bstep (se 1 (by rfl) ⟨1168484, by rfl⟩ : syracuseStep 1557979 = 2336969) B2336969
theorem B5260787 : Blo 1557476 5260787 := bstep (se 1 (by rfl) ⟨3945590, by rfl⟩ : syracuseStep 5260787 = 7891181) B7891181
theorem B44951051 : Blo 1557476 44951051 := bstep (se 1 (by rfl) ⟨33713288, by rfl⟩ : syracuseStep 44951051 = 67426577) B67426577
theorem B5916185 : Blo 1557476 5916185 := bstep (se 2 (by rfl) ⟨2218569, by rfl⟩ : syracuseStep 5916185 = 4437139) B4437139
theorem B1558055 : Blo 1557476 1558055 := bstep (se 1 (by rfl) ⟨1168541, by rfl⟩ : syracuseStep 1558055 = 2337083) B2337083
theorem B5916199 : Blo 1557476 5916199 := bstep (se 1 (by rfl) ⟨4437149, by rfl⟩ : syracuseStep 5916199 = 8874299) B8874299
theorem B2958905 : Blo 1557476 2958905 := bstep (se 2 (by rfl) ⟨1109589, by rfl⟩ : syracuseStep 2958905 = 2219179) B2219179
theorem B12633661 : Blo 1557476 12633661 := bstep (se 3 (by rfl) ⟨2368811, by rfl⟩ : syracuseStep 12633661 = 4737623) B4737623
theorem B1558095 : Blo 1557476 1558095 := bstep (se 1 (by rfl) ⟨1168571, by rfl⟩ : syracuseStep 1558095 = 2337143) B2337143
theorem B1558111 : Blo 1557476 1558111 := bstep (se 1 (by rfl) ⟨1168583, by rfl⟩ : syracuseStep 1558111 = 2337167) B2337167
theorem B1558139 : Blo 1557476 1558139 := bstep (se 1 (by rfl) ⟨1168604, by rfl⟩ : syracuseStep 1558139 = 2337209) B2337209
theorem B1558191 : Blo 1557476 1558191 := bstep (se 1 (by rfl) ⟨1168643, by rfl⟩ : syracuseStep 1558191 = 2337287) B2337287
theorem B1558215 : Blo 1557476 1558215 := bstep (se 1 (by rfl) ⟨1168661, by rfl⟩ : syracuseStep 1558215 = 2337323) B2337323
theorem B20244167 : Blo 1557476 20244167 := bstep (se 1 (by rfl) ⟨15183125, by rfl⟩ : syracuseStep 20244167 = 30366251) B30366251
theorem B3507911 : Blo 1557476 3507911 := bstep (se 1 (by rfl) ⟨2630933, by rfl⟩ : syracuseStep 3507911 = 5261867) B5261867
theorem B1558235 : Blo 1557476 1558235 := bstep (se 1 (by rfl) ⟨1168676, by rfl⟩ : syracuseStep 1558235 = 2337353) B2337353
theorem B16844537 : Blo 1557476 16844537 := bstep (se 2 (by rfl) ⟨6316701, by rfl⟩ : syracuseStep 16844537 = 12633403) B12633403
theorem B1558311 : Blo 1557476 1558311 := bstep (se 1 (by rfl) ⟨1168733, by rfl⟩ : syracuseStep 1558311 = 2337467) B2337467
theorem B7997251 : Blo 1557476 7997251 := bstep (se 1 (by rfl) ⟨5997938, by rfl⟩ : syracuseStep 7997251 = 11995877) B11995877
theorem B1558351 : Blo 1557476 1558351 := bstep (se 1 (by rfl) ⟨1168763, by rfl⟩ : syracuseStep 1558351 = 2337527) B2337527
theorem B1558367 : Blo 1557476 1558367 := bstep (se 1 (by rfl) ⟨1168775, by rfl⟩ : syracuseStep 1558367 = 2337551) B2337551
theorem B1558395 : Blo 1557476 1558395 := bstep (se 1 (by rfl) ⟨1168796, by rfl⟩ : syracuseStep 1558395 = 2337593) B2337593
theorem B2959247 : Blo 1557476 2959247 := bstep (se 1 (by rfl) ⟨2219435, by rfl⟩ : syracuseStep 2959247 = 4438871) B4438871
theorem B2336687 : Blo 1557476 2336687 := bstep (se 1 (by rfl) ⟨1752515, by rfl⟩ : syracuseStep 2336687 = 3505031) B3505031
theorem B1558447 : Blo 1557476 1558447 := bstep (se 1 (by rfl) ⟨1168835, by rfl⟩ : syracuseStep 1558447 = 2337671) B2337671
theorem B1558471 : Blo 1557476 1558471 := bstep (se 1 (by rfl) ⟨1168853, by rfl⟩ : syracuseStep 1558471 = 2337707) B2337707
theorem B17754065 : Blo 1557476 17754065 := bstep (se 2 (by rfl) ⟨6657774, by rfl⟩ : syracuseStep 17754065 = 13315549) B13315549
theorem B1558491 : Blo 1557476 1558491 := bstep (se 1 (by rfl) ⟨1168868, by rfl⟩ : syracuseStep 1558491 = 2337737) B2337737
theorem B2336777 : Blo 1557476 2336777 := bstep (se 2 (by rfl) ⟨876291, by rfl⟩ : syracuseStep 2336777 = 1752583) B1752583
theorem B5261327 : Blo 1557476 5261327 := bstep (se 1 (by rfl) ⟨3945995, by rfl⟩ : syracuseStep 5261327 = 7891991) B7891991
theorem B2336807 : Blo 1557476 2336807 := bstep (se 1 (by rfl) ⟨1752605, by rfl⟩ : syracuseStep 2336807 = 3505211) B3505211
theorem B1558567 : Blo 1557476 1558567 := bstep (se 1 (by rfl) ⟨1168925, by rfl⟩ : syracuseStep 1558567 = 2337851) B2337851
theorem B1558607 : Blo 1557476 1558607 := bstep (se 1 (by rfl) ⟨1168955, by rfl⟩ : syracuseStep 1558607 = 2337911) B2337911
theorem B2107471 : Blo 1557476 2107471 := bstep (se 1 (by rfl) ⟨1580603, by rfl⟩ : syracuseStep 2107471 = 3161207) B3161207
theorem B1558623 : Blo 1557476 1558623 := bstep (se 1 (by rfl) ⟨1168967, by rfl⟩ : syracuseStep 1558623 = 2337935) B2337935
theorem B2336891 : Blo 1557476 2336891 := bstep (se 1 (by rfl) ⟨1752668, by rfl⟩ : syracuseStep 2336891 = 3505337) B3505337
theorem B1558651 : Blo 1557476 1558651 := bstep (se 1 (by rfl) ⟨1168988, by rfl⟩ : syracuseStep 1558651 = 2337977) B2337977
theorem B4991129 : Blo 1557476 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B1558703 : Blo 1557476 1558703 := bstep (se 1 (by rfl) ⟨1169027, by rfl⟩ : syracuseStep 1558703 = 2338055) B2338055
theorem B1558727 : Blo 1557476 1558727 := bstep (se 1 (by rfl) ⟨1169045, by rfl⟩ : syracuseStep 1558727 = 2338091) B2338091
theorem B1558747 : Blo 1557476 1558747 := bstep (se 1 (by rfl) ⟨1169060, by rfl⟩ : syracuseStep 1558747 = 2338121) B2338121
theorem B2337017 : Blo 1557476 2337017 := bstep (se 2 (by rfl) ⟨876381, by rfl⟩ : syracuseStep 2337017 = 1752763) B1752763
theorem B1558823 : Blo 1557476 1558823 := bstep (se 1 (by rfl) ⟨1169117, by rfl⟩ : syracuseStep 1558823 = 2338235) B2338235
theorem B5916989 : Blo 1557476 5916989 := bstep (se 3 (by rfl) ⟨1109435, by rfl⟩ : syracuseStep 5916989 = 2218871) B2218871
theorem B1558863 : Blo 1557476 1558863 := bstep (se 1 (by rfl) ⟨1169147, by rfl⟩ : syracuseStep 1558863 = 2338295) B2338295
theorem B5613911 : Blo 1557476 5613911 := bstep (se 1 (by rfl) ⟨4210433, by rfl⟩ : syracuseStep 5613911 = 8420867) B8420867
theorem B2337119 : Blo 1557476 2337119 := bstep (se 1 (by rfl) ⟨1752839, by rfl⟩ : syracuseStep 2337119 = 3505679) B3505679
theorem B1558879 : Blo 1557476 1558879 := bstep (se 1 (by rfl) ⟨1169159, by rfl⟩ : syracuseStep 1558879 = 2338319) B2338319
theorem B2337131 : Blo 1557476 2337131 := bstep (se 1 (by rfl) ⟨1752848, by rfl⟩ : syracuseStep 2337131 = 3505697) B3505697
theorem B1558907 : Blo 1557476 1558907 := bstep (se 1 (by rfl) ⟨1169180, by rfl⟩ : syracuseStep 1558907 = 2338361) B2338361
theorem B7489921 : Blo 1557476 7489921 := bstep (se 2 (by rfl) ⟨2808720, by rfl⟩ : syracuseStep 7489921 = 5617441) B5617441
theorem B3746191 : Blo 1557476 3746191 := bstep (se 1 (by rfl) ⟨2809643, by rfl⟩ : syracuseStep 3746191 = 5619287) B5619287
theorem B1558959 : Blo 1557476 1558959 := bstep (se 1 (by rfl) ⟨1169219, by rfl⟩ : syracuseStep 1558959 = 2338439) B2338439
theorem B1558983 : Blo 1557476 1558983 := bstep (se 1 (by rfl) ⟨1169237, by rfl⟩ : syracuseStep 1558983 = 2338475) B2338475
theorem B1559003 : Blo 1557476 1559003 := bstep (se 1 (by rfl) ⟨1169252, by rfl⟩ : syracuseStep 1559003 = 2338505) B2338505
theorem B5917171 : Blo 1557476 5917171 := bstep (se 1 (by rfl) ⟨4437878, by rfl⟩ : syracuseStep 5917171 = 8875757) B8875757
theorem B1559079 : Blo 1557476 1559079 := bstep (se 1 (by rfl) ⟨1169309, by rfl⟩ : syracuseStep 1559079 = 2338619) B2338619
theorem B3508775 : Blo 1557476 3508775 := bstep (se 1 (by rfl) ⟨2631581, by rfl⟩ : syracuseStep 3508775 = 5263163) B5263163
theorem B2337359 : Blo 1557476 2337359 := bstep (se 1 (by rfl) ⟨1753019, by rfl⟩ : syracuseStep 2337359 = 3506039) B3506039
theorem B1559119 : Blo 1557476 1559119 := bstep (se 1 (by rfl) ⟨1169339, by rfl⟩ : syracuseStep 1559119 = 2338679) B2338679
theorem B1559135 : Blo 1557476 1559135 := bstep (se 1 (by rfl) ⟨1169351, by rfl⟩ : syracuseStep 1559135 = 2338703) B2338703
theorem B5261921 : Blo 1557476 5261921 := bstep (se 2 (by rfl) ⟨1973220, by rfl⟩ : syracuseStep 5261921 = 3946441) B3946441
theorem B1559163 : Blo 1557476 1559163 := bstep (se 1 (by rfl) ⟨1169372, by rfl⟩ : syracuseStep 1559163 = 2338745) B2338745
theorem B1559215 : Blo 1557476 1559215 := bstep (se 1 (by rfl) ⟨1169411, by rfl⟩ : syracuseStep 1559215 = 2338823) B2338823
theorem B2337479 : Blo 1557476 2337479 := bstep (se 1 (by rfl) ⟨1753109, by rfl⟩ : syracuseStep 2337479 = 3506219) B3506219
theorem B1559239 : Blo 1557476 1559239 := bstep (se 1 (by rfl) ⟨1169429, by rfl⟩ : syracuseStep 1559239 = 2338859) B2338859
theorem B7891667 : Blo 1557476 7891667 := bstep (se 1 (by rfl) ⟨5918750, by rfl⟩ : syracuseStep 7891667 = 11837501) B11837501
theorem B1559259 : Blo 1557476 1559259 := bstep (se 1 (by rfl) ⟨1169444, by rfl⟩ : syracuseStep 1559259 = 2338889) B2338889
theorem B8874755 : Blo 1557476 8874755 := bstep (se 1 (by rfl) ⟨6656066, by rfl⟩ : syracuseStep 8874755 = 13312133) B13312133
theorem B11234051 : Blo 1557476 11234051 := bstep (se 1 (by rfl) ⟨8425538, by rfl⟩ : syracuseStep 11234051 = 16851077) B16851077
theorem B1559335 : Blo 1557476 1559335 := bstep (se 1 (by rfl) ⟨1169501, by rfl⟩ : syracuseStep 1559335 = 2339003) B2339003
theorem B1559375 : Blo 1557476 1559375 := bstep (se 1 (by rfl) ⟨1169531, by rfl⟩ : syracuseStep 1559375 = 2339063) B2339063
theorem B1559391 : Blo 1557476 1559391 := bstep (se 1 (by rfl) ⟨1169543, by rfl⟩ : syracuseStep 1559391 = 2339087) B2339087
theorem B2337641 : Blo 1557476 2337641 := bstep (se 2 (by rfl) ⟨876615, by rfl⟩ : syracuseStep 2337641 = 1753231) B1753231
theorem B1559419 : Blo 1557476 1559419 := bstep (se 1 (by rfl) ⟨1169564, by rfl⟩ : syracuseStep 1559419 = 2339129) B2339129
theorem B3943343 : Blo 1557476 3943343 := bstep (se 1 (by rfl) ⟨2957507, by rfl⟩ : syracuseStep 3943343 = 5915015) B5915015
theorem B1559471 : Blo 1557476 1559471 := bstep (se 1 (by rfl) ⟨1169603, by rfl⟩ : syracuseStep 1559471 = 2339207) B2339207
theorem B2337719 : Blo 1557476 2337719 := bstep (se 1 (by rfl) ⟨1753289, by rfl⟩ : syracuseStep 2337719 = 3506579) B3506579
theorem B2337755 : Blo 1557476 2337755 := bstep (se 1 (by rfl) ⟨1753316, by rfl⟩ : syracuseStep 2337755 = 3506633) B3506633
theorem B13307075 : Blo 1557476 13307075 := bstep (se 1 (by rfl) ⟨9980306, by rfl⟩ : syracuseStep 13307075 = 19960613) B19960613
theorem B12643523 : Blo 1557476 12643523 := bstep (se 1 (by rfl) ⟨9482642, by rfl⟩ : syracuseStep 12643523 = 18965285) B18965285
theorem B2338223 : Blo 1557476 2338223 := bstep (se 1 (by rfl) ⟨1753667, by rfl⟩ : syracuseStep 2338223 = 3507335) B3507335
theorem B2338313 : Blo 1557476 2338313 := bstep (se 2 (by rfl) ⟨876867, by rfl⟩ : syracuseStep 2338313 = 1753735) B1753735
theorem B3943961 : Blo 1557476 3943961 := bstep (se 2 (by rfl) ⟨1478985, by rfl⟩ : syracuseStep 3943961 = 2957971) B2957971
theorem B2338343 : Blo 1557476 2338343 := bstep (se 1 (by rfl) ⟨1753757, by rfl⟩ : syracuseStep 2338343 = 3507515) B3507515
theorem B2338427 : Blo 1557476 2338427 := bstep (se 1 (by rfl) ⟨1753820, by rfl⟩ : syracuseStep 2338427 = 3507641) B3507641
theorem B5918417 : Blo 1557476 5918417 := bstep (se 2 (by rfl) ⟨2219406, by rfl⟩ : syracuseStep 5918417 = 4438813) B4438813
theorem B2338553 : Blo 1557476 2338553 := bstep (se 2 (by rfl) ⟨876957, by rfl⟩ : syracuseStep 2338553 = 1753915) B1753915
theorem B2338655 : Blo 1557476 2338655 := bstep (se 1 (by rfl) ⟨1753991, by rfl⟩ : syracuseStep 2338655 = 3507983) B3507983
theorem B2338667 : Blo 1557476 2338667 := bstep (se 1 (by rfl) ⟨1754000, by rfl⟩ : syracuseStep 2338667 = 3508001) B3508001
theorem B11841389 : Blo 1557476 11841389 := bstep (se 3 (by rfl) ⟨2220260, by rfl⟩ : syracuseStep 11841389 = 4440521) B4440521
theorem B6655931 : Blo 1557476 6655931 := bstep (se 1 (by rfl) ⟨4991948, by rfl⟩ : syracuseStep 6655931 = 9983897) B9983897
theorem B3330067 : Blo 1557476 3330067 := bstep (se 1 (by rfl) ⟨2497550, by rfl⟩ : syracuseStep 3330067 = 4995101) B4995101
theorem B2338895 : Blo 1557476 2338895 := bstep (se 1 (by rfl) ⟨1754171, by rfl⟩ : syracuseStep 2338895 = 3508343) B3508343
theorem B2339015 : Blo 1557476 2339015 := bstep (se 1 (by rfl) ⟨1754261, by rfl⟩ : syracuseStep 2339015 = 3508523) B3508523
theorem B22475069 : Blo 1557476 22475069 := bstep (se 3 (by rfl) ⟨4214075, by rfl⟩ : syracuseStep 22475069 = 8428151) B8428151
theorem B23081291 : Blo 1557476 23081291 := bstep (se 1 (by rfl) ⟨17310968, by rfl⟩ : syracuseStep 23081291 = 34621937) B34621937
theorem B3330409 : Blo 1557476 3330409 := bstep (se 2 (by rfl) ⟨1248903, by rfl⟩ : syracuseStep 3330409 = 2497807) B2497807
theorem B2339177 : Blo 1557476 2339177 := bstep (se 2 (by rfl) ⟨877191, by rfl⟩ : syracuseStep 2339177 = 1754383) B1754383
theorem B5919101 : Blo 1557476 5919101 := bstep (se 3 (by rfl) ⟨1109831, by rfl⟩ : syracuseStep 5919101 = 2219663) B2219663
theorem B7205357 : Blo 1557476 7205357 := bstep (se 3 (by rfl) ⟨1351004, by rfl⟩ : syracuseStep 7205357 = 2702009) B2702009
theorem B4436603 : Blo 1557476 4436603 := bstep (se 1 (by rfl) ⟨3327452, by rfl⟩ : syracuseStep 4436603 = 6654905) B6654905
theorem B8426119 : Blo 1557476 8426119 := bstep (se 1 (by rfl) ⟨6319589, by rfl⟩ : syracuseStep 8426119 = 12639179) B12639179
theorem B204993217 : Blo 1557476 204993217 := bstep (se 2 (by rfl) ⟨76872456, by rfl⟩ : syracuseStep 204993217 = 153744913) B153744913
theorem B6320855 : Blo 1557476 6320855 := bstep (se 1 (by rfl) ⟨4740641, by rfl⟩ : syracuseStep 6320855 = 9481283) B9481283
theorem B2495225 : Blo 1557476 2495225 := bstep (se 2 (by rfl) ⟨935709, by rfl⟩ : syracuseStep 2495225 = 1871419) B1871419
theorem B5616377 : Blo 1557476 5616377 := bstep (se 2 (by rfl) ⟨2106141, by rfl⟩ : syracuseStep 5616377 = 4212283) B4212283
theorem B4436831 : Blo 1557476 4436831 := bstep (se 1 (by rfl) ⟨3327623, by rfl⟩ : syracuseStep 4436831 = 6655247) B6655247
theorem B10810259 : Blo 1557476 10810259 := bstep (se 1 (by rfl) ⟨8107694, by rfl⟩ : syracuseStep 10810259 = 16215389) B16215389
theorem B7893935 : Blo 1557476 7893935 := bstep (se 1 (by rfl) ⟨5920451, by rfl⟩ : syracuseStep 7893935 = 11840903) B11840903
theorem B5920087 : Blo 1557476 5920087 := bstep (se 1 (by rfl) ⟨4440065, by rfl⟩ : syracuseStep 5920087 = 8880131) B8880131
theorem B33707411 : Blo 1557476 33707411 := bstep (se 1 (by rfl) ⟨25280558, by rfl⟩ : syracuseStep 33707411 = 50561117) B50561117
theorem B1971631 : Blo 1557476 1971631 := bstep (se 1 (by rfl) ⟨1478723, by rfl⟩ : syracuseStep 1971631 = 2957447) B2957447
theorem B18961883 : Blo 1557476 18961883 := bstep (se 1 (by rfl) ⟨14221412, by rfl⟩ : syracuseStep 18961883 = 28442825) B28442825
theorem B5256737 : Blo 1557476 5256737 := bstep (se 2 (by rfl) ⟨1971276, by rfl⟩ : syracuseStep 5256737 = 3942553) B3942553
theorem B5920391 : Blo 1557476 5920391 := bstep (se 1 (by rfl) ⟨4440293, by rfl⟩ : syracuseStep 5920391 = 8880587) B8880587
theorem B7886483 : Blo 1557476 7886483 := bstep (se 1 (by rfl) ⟨5914862, by rfl⟩ : syracuseStep 7886483 = 11829725) B11829725
theorem B2496199 : Blo 1557476 2496199 := bstep (se 1 (by rfl) ⟨1872149, by rfl⟩ : syracuseStep 2496199 = 3744299) B3744299
theorem B2217721 : Blo 1557476 2217721 := bstep (se 2 (by rfl) ⟨831645, by rfl⟩ : syracuseStep 2217721 = 1663291) B1663291
theorem B5256953 : Blo 1557476 5256953 := bstep (se 2 (by rfl) ⟨1971357, by rfl⟩ : syracuseStep 5256953 = 3942715) B3942715
theorem B8427331 : Blo 1557476 8427331 := bstep (se 1 (by rfl) ⟨6320498, by rfl⟩ : syracuseStep 8427331 = 12640997) B12640997
theorem B2193247 : Blo 1557476 2193247 := bstep (se 1 (by rfl) ⟨1644935, by rfl⟩ : syracuseStep 2193247 = 3289871) B3289871
theorem B5257223 : Blo 1557476 5257223 := bstep (se 1 (by rfl) ⟨3942917, by rfl⟩ : syracuseStep 5257223 = 7885835) B7885835
theorem B3946553 : Blo 1557476 3946553 := bstep (se 2 (by rfl) ⟨1479957, by rfl⟩ : syracuseStep 3946553 = 2959915) B2959915
theorem B5920847 : Blo 1557476 5920847 := bstep (se 1 (by rfl) ⟨4440635, by rfl⟩ : syracuseStep 5920847 = 8881271) B8881271
theorem B5257331 : Blo 1557476 5257331 := bstep (se 1 (by rfl) ⟨3942998, by rfl⟩ : syracuseStep 5257331 = 7885997) B7885997
theorem B4995229 : Blo 1557476 4995229 := bstep (se 3 (by rfl) ⟨936605, by rfl⟩ : syracuseStep 4995229 = 1873211) B1873211
theorem B14211377 : Blo 1557476 14211377 := bstep (se 2 (by rfl) ⟨5329266, by rfl⟩ : syracuseStep 14211377 = 10658533) B10658533
theorem B5257601 : Blo 1557476 5257601 := bstep (se 2 (by rfl) ⟨1971600, by rfl⟩ : syracuseStep 5257601 = 3943201) B3943201
theorem B3504527 : Blo 1557476 3504527 := bstep (se 1 (by rfl) ⟨2628395, by rfl⟩ : syracuseStep 3504527 = 5256791) B5256791
theorem B4438415 : Blo 1557476 4438415 := bstep (se 1 (by rfl) ⟨3328811, by rfl⟩ : syracuseStep 4438415 = 6657623) B6657623
theorem B8870381 : Blo 1557476 8870381 := bstep (se 3 (by rfl) ⟨1663196, by rfl⟩ : syracuseStep 8870381 = 3326393) B3326393
theorem B1972775 : Blo 1557476 1972775 := bstep (se 1 (by rfl) ⟨1479581, by rfl⟩ : syracuseStep 1972775 = 2959163) B2959163
theorem B12638855 : Blo 1557476 12638855 := bstep (se 1 (by rfl) ⟨9479141, by rfl⟩ : syracuseStep 12638855 = 18958283) B18958283
theorem B3504851 : Blo 1557476 3504851 := bstep (se 1 (by rfl) ⟨2628638, by rfl⟩ : syracuseStep 3504851 = 5257277) B5257277
theorem B91151119 : Blo 1557476 91151119 := bstep (se 1 (by rfl) ⟨68363339, by rfl⟩ : syracuseStep 91151119 = 136726679) B136726679
theorem B1973099 : Blo 1557476 1973099 := bstep (se 1 (by rfl) ⟨1479824, by rfl⟩ : syracuseStep 1973099 = 2959649) B2959649
theorem B3160939 : Blo 1557476 3160939 := bstep (se 1 (by rfl) ⟨2370704, by rfl⟩ : syracuseStep 3160939 = 4741409) B4741409
theorem B2628571 : Blo 1557476 2628571 := bstep (se 1 (by rfl) ⟨1971428, by rfl⟩ : syracuseStep 2628571 = 3942857) B3942857
theorem B11828267 : Blo 1557476 11828267 := bstep (se 1 (by rfl) ⟨8871200, by rfl⟩ : syracuseStep 11828267 = 17742401) B17742401
theorem B1752187 : Blo 1557476 1752187 := bstep (se 1 (by rfl) ⟨1314140, by rfl⟩ : syracuseStep 1752187 = 2628281) B2628281
theorem B8871065 : Blo 1557476 8871065 := bstep (se 2 (by rfl) ⟨3326649, by rfl⟩ : syracuseStep 8871065 = 6653299) B6653299
theorem B5258411 : Blo 1557476 5258411 := bstep (se 1 (by rfl) ⟨3943808, by rfl⟩ : syracuseStep 5258411 = 7887617) B7887617
theorem B11992483 : Blo 1557476 11992483 := bstep (se 1 (by rfl) ⟨8994362, by rfl⟩ : syracuseStep 11992483 = 17988725) B17988725
theorem B7486921 : Blo 1557476 7486921 := bstep (se 2 (by rfl) ⟨2807595, by rfl⟩ : syracuseStep 7486921 = 5615191) B5615191
theorem B7306697 : Blo 1557476 7306697 := bstep (se 2 (by rfl) ⟨2740011, by rfl⟩ : syracuseStep 7306697 = 5480023) B5480023
theorem B4267529 : Blo 1557476 4267529 := bstep (se 2 (by rfl) ⟨1600323, by rfl⟩ : syracuseStep 4267529 = 3200647) B3200647
theorem B1752655 : Blo 1557476 1752655 := bstep (se 1 (by rfl) ⟨1314491, by rfl⟩ : syracuseStep 1752655 = 2628983) B2628983
theorem B2629199 : Blo 1557476 2629199 := bstep (se 1 (by rfl) ⟨1971899, by rfl⟩ : syracuseStep 2629199 = 3943799) B3943799
theorem B22453847 : Blo 1557476 22453847 := bstep (se 1 (by rfl) ⟨16840385, by rfl⟩ : syracuseStep 22453847 = 33680771) B33680771
theorem B11837015 : Blo 1557476 11837015 := bstep (se 1 (by rfl) ⟨8877761, by rfl⟩ : syracuseStep 11837015 = 17755523) B17755523
theorem B3505787 : Blo 1557476 3505787 := bstep (se 1 (by rfl) ⟨2629340, by rfl⟩ : syracuseStep 3505787 = 5258681) B5258681
theorem B2956999 : Blo 1557476 2956999 := bstep (se 1 (by rfl) ⟨2217749, by rfl⟩ : syracuseStep 2956999 = 4435499) B4435499
theorem B5258951 : Blo 1557476 5258951 := bstep (se 1 (by rfl) ⟨3944213, by rfl⟩ : syracuseStep 5258951 = 7888427) B7888427
theorem B10124999 : Blo 1557476 10124999 := bstep (se 1 (by rfl) ⟨7593749, by rfl⟩ : syracuseStep 10124999 = 15187499) B15187499
theorem B3505913 : Blo 1557476 3505913 := bstep (se 2 (by rfl) ⟨1314717, by rfl⟩ : syracuseStep 3505913 = 2629435) B2629435
theorem B5914529 : Blo 1557476 5914529 := bstep (se 2 (by rfl) ⟨2217948, by rfl⟩ : syracuseStep 5914529 = 4435897) B4435897
theorem B30351289 : Blo 1557476 30351289 := bstep (se 2 (by rfl) ⟨11381733, by rfl⟩ : syracuseStep 30351289 = 22763467) B22763467
theorem B2809787 : Blo 1557476 2809787 := bstep (se 1 (by rfl) ⟨2107340, by rfl⟩ : syracuseStep 2809787 = 4214681) B4214681
theorem B1753051 : Blo 1557476 1753051 := bstep (se 1 (by rfl) ⟨1314788, by rfl⟩ : syracuseStep 1753051 = 2629577) B2629577
theorem B4440089 : Blo 1557476 4440089 := bstep (se 2 (by rfl) ⟨1665033, by rfl⟩ : syracuseStep 4440089 = 3330067) B3330067
theorem B2809961 : Blo 1557476 2809961 := bstep (se 2 (by rfl) ⟨1053735, by rfl⟩ : syracuseStep 2809961 = 2107471) B2107471
theorem B6660305 : Blo 1557476 6660305 := bstep (se 2 (by rfl) ⟨2497614, by rfl⟩ : syracuseStep 6660305 = 4995229) B4995229
theorem B14983379 : Blo 1557476 14983379 := bstep (se 1 (by rfl) ⟨11237534, by rfl⟩ : syracuseStep 14983379 = 22475069) B22475069
theorem B1753375 : Blo 1557476 1753375 := bstep (se 1 (by rfl) ⟨1315031, by rfl⟩ : syracuseStep 1753375 = 2630063) B2630063
theorem B67379525 : Blo 1557476 67379525 := bstep (se 4 (by rfl) ⟨6316830, by rfl⟩ : syracuseStep 67379525 = 12633661) B12633661
theorem B3506543 : Blo 1557476 3506543 := bstep (se 1 (by rfl) ⟨2629907, by rfl⟩ : syracuseStep 3506543 = 5259815) B5259815
theorem B2957735 : Blo 1557476 2957735 := bstep (se 1 (by rfl) ⟨2218301, by rfl⟩ : syracuseStep 2957735 = 4436603) B4436603
theorem B3506615 : Blo 1557476 3506615 := bstep (se 1 (by rfl) ⟨2629961, by rfl⟩ : syracuseStep 3506615 = 5259923) B5259923
theorem B4440545 : Blo 1557476 4440545 := bstep (se 2 (by rfl) ⟨1665204, by rfl⟩ : syracuseStep 4440545 = 3330409) B3330409
theorem B3744251 : Blo 1557476 3744251 := bstep (se 1 (by rfl) ⟨2808188, by rfl⟩ : syracuseStep 3744251 = 5616377) B5616377
theorem B9986561 : Blo 1557476 9986561 := bstep (se 2 (by rfl) ⟨3744960, by rfl⟩ : syracuseStep 9986561 = 7489921) B7489921
theorem B2957887 : Blo 1557476 2957887 := bstep (se 1 (by rfl) ⟨2218415, by rfl⟩ : syracuseStep 2957887 = 4436831) B4436831
theorem B1753663 : Blo 1557476 1753663 := bstep (se 1 (by rfl) ⟨1315247, by rfl⟩ : syracuseStep 1753663 = 2630495) B2630495
theorem B3506759 : Blo 1557476 3506759 := bstep (se 1 (by rfl) ⟨2630069, by rfl⟩ : syracuseStep 3506759 = 5260139) B5260139
theorem B3506795 : Blo 1557476 3506795 := bstep (se 1 (by rfl) ⟨2630096, by rfl⟩ : syracuseStep 3506795 = 5260193) B5260193
theorem B32424583 : Blo 1557476 32424583 := bstep (se 1 (by rfl) ⟨24318437, by rfl⟩ : syracuseStep 32424583 = 48636875) B48636875
theorem B7889561 : Blo 1557476 7889561 := bstep (se 2 (by rfl) ⟨2958585, by rfl⟩ : syracuseStep 7889561 = 5917171) B5917171
theorem B26985163 : Blo 1557476 26985163 := bstep (se 1 (by rfl) ⟨20238872, by rfl⟩ : syracuseStep 26985163 = 40477745) B40477745
theorem B22471607 : Blo 1557476 22471607 := bstep (se 1 (by rfl) ⟨16853705, by rfl⟩ : syracuseStep 22471607 = 33707411) B33707411
theorem B11830211 : Blo 1557476 11830211 := bstep (se 1 (by rfl) ⟨8872658, by rfl⟩ : syracuseStep 11830211 = 17745317) B17745317
theorem B1557479 : Blo 1557476 1557479 := bstep (se 1 (by rfl) ⟨1168109, by rfl⟩ : syracuseStep 1557479 = 2336219) B2336219
theorem B12641255 : Blo 1557476 12641255 := bstep (se 1 (by rfl) ⟨9480941, by rfl⟩ : syracuseStep 12641255 = 18961883) B18961883
theorem B3507191 : Blo 1557476 3507191 := bstep (se 1 (by rfl) ⟨2630393, by rfl⟩ : syracuseStep 3507191 = 5260787) B5260787
theorem B29967367 : Blo 1557476 29967367 := bstep (se 1 (by rfl) ⟨22475525, by rfl⟩ : syracuseStep 29967367 = 44951051) B44951051
theorem B1557791 : Blo 1557476 1557791 := bstep (se 1 (by rfl) ⟨1168343, by rfl⟩ : syracuseStep 1557791 = 2336687) B2336687
theorem B1557851 : Blo 1557476 1557851 := bstep (se 1 (by rfl) ⟨1168388, by rfl⟩ : syracuseStep 1557851 = 2336777) B2336777
theorem B3507551 : Blo 1557476 3507551 := bstep (se 1 (by rfl) ⟨2630663, by rfl⟩ : syracuseStep 3507551 = 5261327) B5261327
theorem B1557871 : Blo 1557476 1557871 := bstep (se 1 (by rfl) ⟨1168403, by rfl⟩ : syracuseStep 1557871 = 2336807) B2336807
theorem B2631035 : Blo 1557476 2631035 := bstep (se 1 (by rfl) ⟨1973276, by rfl⟩ : syracuseStep 2631035 = 3946553) B3946553
theorem B1557927 : Blo 1557476 1557927 := bstep (se 1 (by rfl) ⟨1168445, by rfl⟩ : syracuseStep 1557927 = 2336891) B2336891
theorem B3327419 : Blo 1557476 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B5260733 : Blo 1557476 5260733 := bstep (se 3 (by rfl) ⟨986387, by rfl⟩ : syracuseStep 5260733 = 1972775) B1972775
theorem B2336249 : Blo 1557476 2336249 := bstep (se 2 (by rfl) ⟨876093, by rfl⟩ : syracuseStep 2336249 = 1752187) B1752187
theorem B1558011 : Blo 1557476 1558011 := bstep (se 1 (by rfl) ⟨1168508, by rfl⟩ : syracuseStep 1558011 = 2337017) B2337017
theorem B1558079 : Blo 1557476 1558079 := bstep (se 1 (by rfl) ⟨1168559, by rfl⟩ : syracuseStep 1558079 = 2337119) B2337119
theorem B1558087 : Blo 1557476 1558087 := bstep (se 1 (by rfl) ⟨1168565, by rfl⟩ : syracuseStep 1558087 = 2337131) B2337131
theorem B2336351 : Blo 1557476 2336351 := bstep (se 1 (by rfl) ⟨1752263, by rfl⟩ : syracuseStep 2336351 = 3504527) B3504527
theorem B2958943 : Blo 1557476 2958943 := bstep (se 1 (by rfl) ⟨2219207, by rfl⟩ : syracuseStep 2958943 = 4438415) B4438415
theorem B1558239 : Blo 1557476 1558239 := bstep (se 1 (by rfl) ⟨1168679, by rfl⟩ : syracuseStep 1558239 = 2337359) B2337359
theorem B3507947 : Blo 1557476 3507947 := bstep (se 1 (by rfl) ⟨2630960, by rfl⟩ : syracuseStep 3507947 = 5261921) B5261921
theorem B1558319 : Blo 1557476 1558319 := bstep (se 1 (by rfl) ⟨1168739, by rfl⟩ : syracuseStep 1558319 = 2337479) B2337479
theorem B2336567 : Blo 1557476 2336567 := bstep (se 1 (by rfl) ⟨1752425, by rfl⟩ : syracuseStep 2336567 = 3504851) B3504851
theorem B5261111 : Blo 1557476 5261111 := bstep (se 1 (by rfl) ⟨3945833, by rfl⟩ : syracuseStep 5261111 = 7891667) B7891667
theorem B5916503 : Blo 1557476 5916503 := bstep (se 1 (by rfl) ⟨4437377, by rfl⟩ : syracuseStep 5916503 = 8874755) B8874755
theorem B7489367 : Blo 1557476 7489367 := bstep (se 1 (by rfl) ⟨5617025, by rfl⟩ : syracuseStep 7489367 = 11234051) B11234051
theorem B3901289 : Blo 1557476 3901289 := bstep (se 2 (by rfl) ⟨1462983, by rfl⟩ : syracuseStep 3901289 = 2925967) B2925967
theorem B3508073 : Blo 1557476 3508073 := bstep (se 2 (by rfl) ⟨1315527, by rfl⟩ : syracuseStep 3508073 = 2631055) B2631055
theorem B1558427 : Blo 1557476 1558427 := bstep (se 1 (by rfl) ⟨1168820, by rfl⟩ : syracuseStep 1558427 = 2337641) B2337641
theorem B1558479 : Blo 1557476 1558479 := bstep (se 1 (by rfl) ⟨1168859, by rfl⟩ : syracuseStep 1558479 = 2337719) B2337719
theorem B1558503 : Blo 1557476 1558503 := bstep (se 1 (by rfl) ⟨1168877, by rfl⟩ : syracuseStep 1558503 = 2337755) B2337755
theorem B6653933 : Blo 1557476 6653933 := bstep (se 3 (by rfl) ⟨1247612, by rfl⟩ : syracuseStep 6653933 = 2495225) B2495225
theorem B2336873 : Blo 1557476 2336873 := bstep (se 2 (by rfl) ⟨876327, by rfl⟩ : syracuseStep 2336873 = 1752655) B1752655
theorem B3942665 : Blo 1557476 3942665 := bstep (se 2 (by rfl) ⟨1478499, by rfl⟩ : syracuseStep 3942665 = 2956999) B2956999
theorem B3328265 : Blo 1557476 3328265 := bstep (se 2 (by rfl) ⟨1248099, by rfl⟩ : syracuseStep 3328265 = 2496199) B2496199
theorem B5261597 : Blo 1557476 5261597 := bstep (se 3 (by rfl) ⟨986549, by rfl⟩ : syracuseStep 5261597 = 1973099) B1973099
theorem B1558815 : Blo 1557476 1558815 := bstep (se 1 (by rfl) ⟨1169111, by rfl⟩ : syracuseStep 1558815 = 2338223) B2338223
theorem B2845019 : Blo 1557476 2845019 := bstep (se 1 (by rfl) ⟨2133764, by rfl⟩ : syracuseStep 2845019 = 4267529) B4267529
theorem B1558875 : Blo 1557476 1558875 := bstep (se 1 (by rfl) ⟨1169156, by rfl⟩ : syracuseStep 1558875 = 2338313) B2338313
theorem B1558895 : Blo 1557476 1558895 := bstep (se 1 (by rfl) ⟨1169171, by rfl⟩ : syracuseStep 1558895 = 2338343) B2338343
theorem B39930245 : Blo 1557476 39930245 := bstep (se 4 (by rfl) ⟨3743460, by rfl⟩ : syracuseStep 39930245 = 7486921) B7486921
theorem B14969231 : Blo 1557476 14969231 := bstep (se 1 (by rfl) ⟨11226923, by rfl⟩ : syracuseStep 14969231 = 22453847) B22453847
theorem B7891343 : Blo 1557476 7891343 := bstep (se 1 (by rfl) ⟨5918507, by rfl⟩ : syracuseStep 7891343 = 11837015) B11837015
theorem B2337191 : Blo 1557476 2337191 := bstep (se 1 (by rfl) ⟨1752893, by rfl⟩ : syracuseStep 2337191 = 3505787) B3505787
theorem B1558951 : Blo 1557476 1558951 := bstep (se 1 (by rfl) ⟨1169213, by rfl⟩ : syracuseStep 1558951 = 2338427) B2338427
theorem B2337275 : Blo 1557476 2337275 := bstep (se 1 (by rfl) ⟨1752956, by rfl⟩ : syracuseStep 2337275 = 3505913) B3505913
theorem B1559035 : Blo 1557476 1559035 := bstep (se 1 (by rfl) ⟨1169276, by rfl⟩ : syracuseStep 1559035 = 2338553) B2338553
theorem B1559103 : Blo 1557476 1559103 := bstep (se 1 (by rfl) ⟨1169327, by rfl⟩ : syracuseStep 1559103 = 2338655) B2338655
theorem B1559111 : Blo 1557476 1559111 := bstep (se 1 (by rfl) ⟨1169333, by rfl⟩ : syracuseStep 1559111 = 2338667) B2338667
theorem B3943019 : Blo 1557476 3943019 := bstep (se 1 (by rfl) ⟨2957264, by rfl⟩ : syracuseStep 3943019 = 5914529) B5914529
theorem B2337401 : Blo 1557476 2337401 := bstep (se 2 (by rfl) ⟨876525, by rfl⟩ : syracuseStep 2337401 = 1753051) B1753051
theorem B2337455 : Blo 1557476 2337455 := bstep (se 1 (by rfl) ⟨1753091, by rfl⟩ : syracuseStep 2337455 = 3506183) B3506183
theorem B14985917 : Blo 1557476 14985917 := bstep (se 3 (by rfl) ⟨2809859, by rfl⟩ : syracuseStep 14985917 = 5619719) B5619719
theorem B2337503 : Blo 1557476 2337503 := bstep (se 1 (by rfl) ⟨1753127, by rfl⟩ : syracuseStep 2337503 = 3506255) B3506255
theorem B1559263 : Blo 1557476 1559263 := bstep (se 1 (by rfl) ⟨1169447, by rfl⟩ : syracuseStep 1559263 = 2338895) B2338895
theorem B1559343 : Blo 1557476 1559343 := bstep (se 1 (by rfl) ⟨1169507, by rfl⟩ : syracuseStep 1559343 = 2339015) B2339015
theorem B15387527 : Blo 1557476 15387527 := bstep (se 1 (by rfl) ⟨11540645, by rfl⟩ : syracuseStep 15387527 = 23081291) B23081291
theorem B1559451 : Blo 1557476 1559451 := bstep (se 1 (by rfl) ⟨1169588, by rfl⟩ : syracuseStep 1559451 = 2339177) B2339177
theorem B2337767 : Blo 1557476 2337767 := bstep (se 1 (by rfl) ⟨1753325, by rfl⟩ : syracuseStep 2337767 = 3506651) B3506651
theorem B4803571 : Blo 1557476 4803571 := bstep (se 1 (by rfl) ⟨3602678, by rfl⟩ : syracuseStep 4803571 = 7205357) B7205357
theorem B3746807 : Blo 1557476 3746807 := bstep (se 1 (by rfl) ⟨2810105, by rfl⟩ : syracuseStep 3746807 = 5620211) B5620211
theorem B4213903 : Blo 1557476 4213903 := bstep (se 1 (by rfl) ⟨3160427, by rfl⟩ : syracuseStep 4213903 = 6320855) B6320855
theorem B14986417 : Blo 1557476 14986417 := bstep (se 2 (by rfl) ⟨5619906, by rfl⟩ : syracuseStep 14986417 = 11239813) B11239813
theorem B2338025 : Blo 1557476 2338025 := bstep (se 2 (by rfl) ⟨876759, by rfl⟩ : syracuseStep 2338025 = 1753519) B1753519
theorem B3943667 : Blo 1557476 3943667 := bstep (se 1 (by rfl) ⟨2957750, by rfl⟩ : syracuseStep 3943667 = 5915501) B5915501
theorem B2338079 : Blo 1557476 2338079 := bstep (se 1 (by rfl) ⟨1753559, by rfl⟩ : syracuseStep 2338079 = 3507119) B3507119
theorem B5262623 : Blo 1557476 5262623 := bstep (se 1 (by rfl) ⟨3946967, by rfl⟩ : syracuseStep 5262623 = 7893935) B7893935
theorem B2338247 : Blo 1557476 2338247 := bstep (se 1 (by rfl) ⟨1753685, by rfl⟩ : syracuseStep 2338247 = 3507371) B3507371
theorem B11234825 : Blo 1557476 11234825 := bstep (se 2 (by rfl) ⟨4213059, by rfl⟩ : syracuseStep 11234825 = 8426119) B8426119
theorem B3944123 : Blo 1557476 3944123 := bstep (se 1 (by rfl) ⟨2958092, by rfl⟩ : syracuseStep 3944123 = 5916185) B5916185
theorem B2338601 : Blo 1557476 2338601 := bstep (se 2 (by rfl) ⟨876975, by rfl⟩ : syracuseStep 2338601 = 1753951) B1753951
theorem B13496111 : Blo 1557476 13496111 := bstep (se 1 (by rfl) ⟨10122083, by rfl⟩ : syracuseStep 13496111 = 20244167) B20244167
theorem B2338607 : Blo 1557476 2338607 := bstep (se 1 (by rfl) ⟨1753955, by rfl⟩ : syracuseStep 2338607 = 3507911) B3507911
theorem B28421945 : Blo 1557476 28421945 := bstep (se 2 (by rfl) ⟨10658229, by rfl⟩ : syracuseStep 28421945 = 21316459) B21316459
theorem B4214585 : Blo 1557476 4214585 := bstep (se 2 (by rfl) ⟨1580469, by rfl⟩ : syracuseStep 4214585 = 3160939) B3160939
theorem B19484525 : Blo 1557476 19484525 := bstep (se 3 (by rfl) ⟨3653348, by rfl⟩ : syracuseStep 19484525 = 7306697) B7306697
theorem B9474251 : Blo 1557476 9474251 := bstep (se 1 (by rfl) ⟨7105688, by rfl⟩ : syracuseStep 9474251 = 14211377) B14211377
theorem B3944659 : Blo 1557476 3944659 := bstep (se 1 (by rfl) ⟨2958494, by rfl⟩ : syracuseStep 3944659 = 5916989) B5916989
theorem B2339081 : Blo 1557476 2339081 := bstep (se 2 (by rfl) ⟨877155, by rfl⟩ : syracuseStep 2339081 = 1754311) B1754311
theorem B2339183 : Blo 1557476 2339183 := bstep (se 1 (by rfl) ⟨1754387, by rfl⟩ : syracuseStep 2339183 = 3508775) B3508775
theorem B8425903 : Blo 1557476 8425903 := bstep (se 1 (by rfl) ⟨6319427, by rfl⟩ : syracuseStep 8425903 = 12638855) B12638855
theorem B7893449 : Blo 1557476 7893449 := bstep (se 2 (by rfl) ⟨2960043, by rfl⟩ : syracuseStep 7893449 = 5920087) B5920087
theorem B7885511 : Blo 1557476 7885511 := bstep (se 1 (by rfl) ⟨5914133, by rfl⟩ : syracuseStep 7885511 = 11828267) B11828267
theorem B10663001 : Blo 1557476 10663001 := bstep (se 2 (by rfl) ⟨3998625, by rfl⟩ : syracuseStep 10663001 = 7997251) B7997251
theorem B11236441 : Blo 1557476 11236441 := bstep (se 2 (by rfl) ⟨4213665, by rfl⟩ : syracuseStep 11236441 = 8427331) B8427331
theorem B3945611 : Blo 1557476 3945611 := bstep (se 1 (by rfl) ⟨2959208, by rfl⟩ : syracuseStep 3945611 = 5918417) B5918417
theorem B7492765 : Blo 1557476 7492765 := bstep (se 3 (by rfl) ⟨1404893, by rfl⟩ : syracuseStep 7492765 = 2809787) B2809787
theorem B7894259 : Blo 1557476 7894259 := bstep (se 1 (by rfl) ⟨5920694, by rfl⟩ : syracuseStep 7894259 = 11841389) B11841389
theorem B4437287 : Blo 1557476 4437287 := bstep (se 1 (by rfl) ⟨3327965, by rfl⟩ : syracuseStep 4437287 = 6655931) B6655931
theorem B7493057 : Blo 1557476 7493057 := bstep (se 2 (by rfl) ⟨2809896, by rfl⟩ : syracuseStep 7493057 = 5619793) B5619793
theorem B1873471 : Blo 1557476 1873471 := bstep (se 1 (by rfl) ⟨1405103, by rfl⟩ : syracuseStep 1873471 = 2810207) B2810207
theorem B39917123 : Blo 1557476 39917123 := bstep (se 1 (by rfl) ⟨29937842, by rfl⟩ : syracuseStep 39917123 = 59875685) B59875685
theorem B3946067 : Blo 1557476 3946067 := bstep (se 1 (by rfl) ⟨2959550, by rfl⟩ : syracuseStep 3946067 = 5919101) B5919101
theorem B17749691 : Blo 1557476 17749691 := bstep (se 1 (by rfl) ⟨13312268, by rfl⟩ : syracuseStep 17749691 = 26624537) B26624537
theorem B4994921 : Blo 1557476 4994921 := bstep (se 2 (by rfl) ⟨1873095, by rfl⟩ : syracuseStep 4994921 = 3746191) B3746191
theorem B7206839 : Blo 1557476 7206839 := bstep (se 1 (by rfl) ⟨5405129, by rfl⟩ : syracuseStep 7206839 = 10810259) B10810259
theorem B17078519 : Blo 1557476 17078519 := bstep (se 1 (by rfl) ⟨12808889, by rfl⟩ : syracuseStep 17078519 = 25617779) B25617779
theorem B273324289 : Blo 1557476 273324289 := bstep (se 2 (by rfl) ⟨102496608, by rfl⟩ : syracuseStep 273324289 = 204993217) B204993217
theorem B121534825 : Blo 1557476 121534825 := bstep (se 2 (by rfl) ⟨45575559, by rfl⟩ : syracuseStep 121534825 = 91151119) B91151119
theorem B3504491 : Blo 1557476 3504491 := bstep (se 1 (by rfl) ⟨2628368, by rfl⟩ : syracuseStep 3504491 = 5256737) B5256737
theorem B1972603 : Blo 1557476 1972603 := bstep (se 1 (by rfl) ⟨1479452, by rfl⟩ : syracuseStep 1972603 = 2958905) B2958905
theorem B3946927 : Blo 1557476 3946927 := bstep (se 1 (by rfl) ⟨2960195, by rfl⟩ : syracuseStep 3946927 = 5920391) B5920391
theorem B5257655 : Blo 1557476 5257655 := bstep (se 1 (by rfl) ⟨3943241, by rfl⟩ : syracuseStep 5257655 = 7886483) B7886483
theorem B3504635 : Blo 1557476 3504635 := bstep (se 1 (by rfl) ⟨2628476, by rfl⟩ : syracuseStep 3504635 = 5256953) B5256953
theorem B11229691 : Blo 1557476 11229691 := bstep (se 1 (by rfl) ⟨8422268, by rfl⟩ : syracuseStep 11229691 = 16844537) B16844537
theorem B1972831 : Blo 1557476 1972831 := bstep (se 1 (by rfl) ⟨1479623, by rfl⟩ : syracuseStep 1972831 = 2959247) B2959247
theorem B3504761 : Blo 1557476 3504761 := bstep (se 2 (by rfl) ⟨1314285, by rfl⟩ : syracuseStep 3504761 = 2628571) B2628571
theorem B11836043 : Blo 1557476 11836043 := bstep (se 1 (by rfl) ⟨8877032, by rfl⟩ : syracuseStep 11836043 = 17754065) B17754065
theorem B3504815 : Blo 1557476 3504815 := bstep (se 1 (by rfl) ⟨2628611, by rfl⟩ : syracuseStep 3504815 = 5257223) B5257223
theorem B3947231 : Blo 1557476 3947231 := bstep (se 1 (by rfl) ⟨2960423, by rfl⟩ : syracuseStep 3947231 = 5920847) B5920847
theorem B3504887 : Blo 1557476 3504887 := bstep (se 1 (by rfl) ⟨2628665, by rfl⟩ : syracuseStep 3504887 = 5257331) B5257331
theorem B3742607 : Blo 1557476 3742607 := bstep (se 1 (by rfl) ⟨2806955, by rfl⟩ : syracuseStep 3742607 = 5613911) B5613911
theorem B3505067 : Blo 1557476 3505067 := bstep (se 1 (by rfl) ⟨2628800, by rfl⟩ : syracuseStep 3505067 = 5257601) B5257601
theorem B5913587 : Blo 1557476 5913587 := bstep (se 1 (by rfl) ⟨4435190, by rfl⟩ : syracuseStep 5913587 = 8870381) B8870381
theorem B11697317 : Blo 1557476 11697317 := bstep (se 4 (by rfl) ⟨1096623, by rfl⟩ : syracuseStep 11697317 = 2193247) B2193247
theorem B15989977 : Blo 1557476 15989977 := bstep (se 2 (by rfl) ⟨5996241, by rfl⟩ : syracuseStep 15989977 = 11992483) B11992483
theorem B2628841 : Blo 1557476 2628841 := bstep (se 2 (by rfl) ⟨985815, by rfl⟩ : syracuseStep 2628841 = 1971631) B1971631
theorem B2628895 : Blo 1557476 2628895 := bstep (se 1 (by rfl) ⟨1971671, by rfl⟩ : syracuseStep 2628895 = 3943343) B3943343
theorem B7888265 : Blo 1557476 7888265 := bstep (se 2 (by rfl) ⟨2958099, by rfl⟩ : syracuseStep 7888265 = 5916199) B5916199
theorem B5914043 : Blo 1557476 5914043 := bstep (se 1 (by rfl) ⟨4435532, by rfl⟩ : syracuseStep 5914043 = 8871065) B8871065
theorem B3505607 : Blo 1557476 3505607 := bstep (se 1 (by rfl) ⟨2629205, by rfl⟩ : syracuseStep 3505607 = 5258411) B5258411
theorem B8871383 : Blo 1557476 8871383 := bstep (se 1 (by rfl) ⟨6653537, by rfl⟩ : syracuseStep 8871383 = 13307075) B13307075
theorem B8429015 : Blo 1557476 8429015 := bstep (se 1 (by rfl) ⟨6321761, by rfl⟩ : syracuseStep 8429015 = 12643523) B12643523
theorem B2956961 : Blo 1557476 2956961 := bstep (se 2 (by rfl) ⟨1108860, by rfl⟩ : syracuseStep 2956961 = 2217721) B2217721
theorem B2629307 : Blo 1557476 2629307 := bstep (se 1 (by rfl) ⟨1971980, by rfl⟩ : syracuseStep 2629307 = 3943961) B3943961
theorem B1752799 : Blo 1557476 1752799 := bstep (se 1 (by rfl) ⟨1314599, by rfl⟩ : syracuseStep 1752799 = 2629199) B2629199
theorem B3505967 : Blo 1557476 3505967 := bstep (se 1 (by rfl) ⟨2629475, by rfl⟩ : syracuseStep 3505967 = 5258951) B5258951
theorem B6749999 : Blo 1557476 6749999 := bstep (se 1 (by rfl) ⟨5062499, by rfl⟩ : syracuseStep 6749999 = 10124999) B10124999
theorem B40468385 : Blo 1557476 40468385 := bstep (se 2 (by rfl) ⟨15175644, by rfl⟩ : syracuseStep 40468385 = 30351289) B30351289
theorem B4440203 : Blo 1557476 4440203 := bstep (se 1 (by rfl) ⟨3330152, by rfl⟩ : syracuseStep 4440203 = 6660305) B6660305
theorem B5259545 : Blo 1557476 5259545 := bstep (se 2 (by rfl) ⟨1972329, by rfl⟩ : syracuseStep 5259545 = 3944659) B3944659
theorem B5259707 : Blo 1557476 5259707 := bstep (se 1 (by rfl) ⟨3944780, by rfl⟩ : syracuseStep 5259707 = 7889561) B7889561
theorem B162046433 : Blo 1557476 162046433 := bstep (se 2 (by rfl) ⟨60767412, by rfl⟩ : syracuseStep 162046433 = 121534825) B121534825
theorem B2630137 : Blo 1557476 2630137 := bstep (se 2 (by rfl) ⟨986301, by rfl⟩ : syracuseStep 2630137 = 1972603) B1972603
theorem B25264669 : Blo 1557476 25264669 := bstep (se 3 (by rfl) ⟨4737125, by rfl⟩ : syracuseStep 25264669 = 9474251) B9474251
theorem B2630407 : Blo 1557476 2630407 := bstep (se 1 (by rfl) ⟨1972805, by rfl⟩ : syracuseStep 2630407 = 3945611) B3945611
theorem B2630441 : Blo 1557476 2630441 := bstep (se 2 (by rfl) ⟨986415, by rfl⟩ : syracuseStep 2630441 = 1972831) B1972831
theorem B2958191 : Blo 1557476 2958191 := bstep (se 1 (by rfl) ⟨2218643, by rfl⟩ : syracuseStep 2958191 = 4437287) B4437287
theorem B1754023 : Blo 1557476 1754023 := bstep (se 1 (by rfl) ⟨1315517, by rfl⟩ : syracuseStep 1754023 = 2631035) B2631035
theorem B35980217 : Blo 1557476 35980217 := bstep (se 2 (by rfl) ⟨13492581, by rfl⟩ : syracuseStep 35980217 = 26985163) B26985163
theorem B3507155 : Blo 1557476 3507155 := bstep (se 1 (by rfl) ⟨2630366, by rfl⟩ : syracuseStep 3507155 = 5260733) B5260733
theorem B1557499 : Blo 1557476 1557499 := bstep (se 1 (by rfl) ⟨1168124, by rfl⟩ : syracuseStep 1557499 = 2336249) B2336249
theorem B2630711 : Blo 1557476 2630711 := bstep (se 1 (by rfl) ⟨1973033, by rfl⟩ : syracuseStep 2630711 = 3946067) B3946067
theorem B1557567 : Blo 1557476 1557567 := bstep (se 1 (by rfl) ⟨1168175, by rfl⟩ : syracuseStep 1557567 = 2336351) B2336351
theorem B1557711 : Blo 1557476 1557711 := bstep (se 1 (by rfl) ⟨1168283, by rfl⟩ : syracuseStep 1557711 = 2336567) B2336567
theorem B3507407 : Blo 1557476 3507407 := bstep (se 1 (by rfl) ⟨2630555, by rfl⟩ : syracuseStep 3507407 = 5261111) B5261111
theorem B1557915 : Blo 1557476 1557915 := bstep (se 1 (by rfl) ⟨1168436, by rfl⟩ : syracuseStep 1557915 = 2336873) B2336873
theorem B3507731 : Blo 1557476 3507731 := bstep (se 1 (by rfl) ⟨2630798, by rfl⟩ : syracuseStep 3507731 = 5261597) B5261597
theorem B19981889 : Blo 1557476 19981889 := bstep (se 2 (by rfl) ⟨7493208, by rfl⟩ : syracuseStep 19981889 = 14986417) B14986417
theorem B2336327 : Blo 1557476 2336327 := bstep (se 1 (by rfl) ⟨1752245, by rfl⟩ : syracuseStep 2336327 = 3504491) B3504491
theorem B9979487 : Blo 1557476 9979487 := bstep (se 1 (by rfl) ⟨7484615, by rfl⟩ : syracuseStep 9979487 = 14969231) B14969231
theorem B5260895 : Blo 1557476 5260895 := bstep (se 1 (by rfl) ⟨3945671, by rfl⟩ : syracuseStep 5260895 = 7891343) B7891343
theorem B1558127 : Blo 1557476 1558127 := bstep (se 1 (by rfl) ⟨1168595, by rfl⟩ : syracuseStep 1558127 = 2337191) B2337191
theorem B2336423 : Blo 1557476 2336423 := bstep (se 1 (by rfl) ⟨1752317, by rfl⟩ : syracuseStep 2336423 = 3504635) B3504635
theorem B1558183 : Blo 1557476 1558183 := bstep (se 1 (by rfl) ⟨1168637, by rfl⟩ : syracuseStep 1558183 = 2337275) B2337275
theorem B2336507 : Blo 1557476 2336507 := bstep (se 1 (by rfl) ⟨1752380, by rfl⟩ : syracuseStep 2336507 = 3504761) B3504761
theorem B1558267 : Blo 1557476 1558267 := bstep (se 1 (by rfl) ⟨1168700, by rfl⟩ : syracuseStep 1558267 = 2337401) B2337401
theorem B7890695 : Blo 1557476 7890695 := bstep (se 1 (by rfl) ⟨5918021, by rfl⟩ : syracuseStep 7890695 = 11836043) B11836043
theorem B2336543 : Blo 1557476 2336543 := bstep (se 1 (by rfl) ⟨1752407, by rfl⟩ : syracuseStep 2336543 = 3504815) B3504815
theorem B1558303 : Blo 1557476 1558303 := bstep (se 1 (by rfl) ⟨1168727, by rfl⟩ : syracuseStep 1558303 = 2337455) B2337455
theorem B1558335 : Blo 1557476 1558335 := bstep (se 1 (by rfl) ⟨1168751, by rfl⟩ : syracuseStep 1558335 = 2337503) B2337503
theorem B2631487 : Blo 1557476 2631487 := bstep (se 1 (by rfl) ⟨1973615, by rfl⟩ : syracuseStep 2631487 = 3947231) B3947231
theorem B2336591 : Blo 1557476 2336591 := bstep (se 1 (by rfl) ⟨1752443, by rfl⟩ : syracuseStep 2336591 = 3504887) B3504887
theorem B2336711 : Blo 1557476 2336711 := bstep (se 1 (by rfl) ⟨1752533, by rfl⟩ : syracuseStep 2336711 = 3505067) B3505067
theorem B1558511 : Blo 1557476 1558511 := bstep (se 1 (by rfl) ⟨1168883, by rfl⟩ : syracuseStep 1558511 = 2337767) B2337767
theorem B3942391 : Blo 1557476 3942391 := bstep (se 1 (by rfl) ⟨2956793, by rfl⟩ : syracuseStep 3942391 = 5913587) B5913587
theorem B1558683 : Blo 1557476 1558683 := bstep (se 1 (by rfl) ⟨1169012, by rfl⟩ : syracuseStep 1558683 = 2338025) B2338025
theorem B1558719 : Blo 1557476 1558719 := bstep (se 1 (by rfl) ⟨1169039, by rfl⟩ : syracuseStep 1558719 = 2338079) B2338079
theorem B3508415 : Blo 1557476 3508415 := bstep (se 1 (by rfl) ⟨2631311, by rfl⟩ : syracuseStep 3508415 = 5262623) B5262623
theorem B3942695 : Blo 1557476 3942695 := bstep (se 1 (by rfl) ⟨2957021, by rfl⟩ : syracuseStep 3942695 = 5914043) B5914043
theorem B2337065 : Blo 1557476 2337065 := bstep (se 2 (by rfl) ⟨876399, by rfl⟩ : syracuseStep 2337065 = 1752799) B1752799
theorem B2337071 : Blo 1557476 2337071 := bstep (se 1 (by rfl) ⟨1752803, by rfl⟩ : syracuseStep 2337071 = 3505607) B3505607
theorem B1558831 : Blo 1557476 1558831 := bstep (se 1 (by rfl) ⟨1169123, by rfl⟩ : syracuseStep 1558831 = 2338247) B2338247
theorem B7489883 : Blo 1557476 7489883 := bstep (se 1 (by rfl) ⟨5617412, by rfl⟩ : syracuseStep 7489883 = 11234825) B11234825
theorem B1559067 : Blo 1557476 1559067 := bstep (se 1 (by rfl) ⟨1169300, by rfl⟩ : syracuseStep 1559067 = 2338601) B2338601
theorem B2337311 : Blo 1557476 2337311 := bstep (se 1 (by rfl) ⟨1752983, by rfl⟩ : syracuseStep 2337311 = 3505967) B3505967
theorem B8997407 : Blo 1557476 8997407 := bstep (se 1 (by rfl) ⟨6748055, by rfl⟩ : syracuseStep 8997407 = 13496111) B13496111
theorem B4499999 : Blo 1557476 4499999 := bstep (se 1 (by rfl) ⟨3374999, by rfl⟩ : syracuseStep 4499999 = 6749999) B6749999
theorem B1559071 : Blo 1557476 1559071 := bstep (se 1 (by rfl) ⟨1169303, by rfl⟩ : syracuseStep 1559071 = 2338607) B2338607
theorem B26978923 : Blo 1557476 26978923 := bstep (se 1 (by rfl) ⟨20234192, by rfl⟩ : syracuseStep 26978923 = 40468385) B40468385
theorem B2960059 : Blo 1557476 2960059 := bstep (se 1 (by rfl) ⟨2220044, by rfl⟩ : syracuseStep 2960059 = 4440089) B4440089
theorem B9988919 : Blo 1557476 9988919 := bstep (se 1 (by rfl) ⟨7491689, by rfl⟩ : syracuseStep 9988919 = 14983379) B14983379
theorem B1559387 : Blo 1557476 1559387 := bstep (se 1 (by rfl) ⟨1169540, by rfl⟩ : syracuseStep 1559387 = 2339081) B2339081
theorem B44919683 : Blo 1557476 44919683 := bstep (se 1 (by rfl) ⟨33689762, by rfl⟩ : syracuseStep 44919683 = 67379525) B67379525
theorem B2337695 : Blo 1557476 2337695 := bstep (se 1 (by rfl) ⟨1753271, by rfl⟩ : syracuseStep 2337695 = 3506543) B3506543
theorem B1559455 : Blo 1557476 1559455 := bstep (se 1 (by rfl) ⟨1169591, by rfl⟩ : syracuseStep 1559455 = 2339183) B2339183
theorem B2337743 : Blo 1557476 2337743 := bstep (se 1 (by rfl) ⟨1753307, by rfl⟩ : syracuseStep 2337743 = 3506615) B3506615
theorem B5262299 : Blo 1557476 5262299 := bstep (se 1 (by rfl) ⟨3946724, by rfl⟩ : syracuseStep 5262299 = 7893449) B7893449
theorem B2960363 : Blo 1557476 2960363 := bstep (se 1 (by rfl) ⟨2220272, by rfl⟩ : syracuseStep 2960363 = 4440545) B4440545
theorem B364432385 : Blo 1557476 364432385 := bstep (se 2 (by rfl) ⟨136662144, by rfl⟩ : syracuseStep 364432385 = 273324289) B273324289
theorem B2337833 : Blo 1557476 2337833 := bstep (se 2 (by rfl) ⟨876687, by rfl⟩ : syracuseStep 2337833 = 1753375) B1753375
theorem B2337839 : Blo 1557476 2337839 := bstep (se 1 (by rfl) ⟨1753379, by rfl⟩ : syracuseStep 2337839 = 3506759) B3506759
theorem B2337863 : Blo 1557476 2337863 := bstep (se 1 (by rfl) ⟨1753397, by rfl⟩ : syracuseStep 2337863 = 3506795) B3506795
theorem B11234537 : Blo 1557476 11234537 := bstep (se 2 (by rfl) ⟨4212951, by rfl⟩ : syracuseStep 11234537 = 8425903) B8425903
theorem B5262569 : Blo 1557476 5262569 := bstep (se 2 (by rfl) ⟨1973463, by rfl⟩ : syracuseStep 5262569 = 3946927) B3946927
theorem B45542717 : Blo 1557476 45542717 := bstep (se 3 (by rfl) ⟨8539259, by rfl⟩ : syracuseStep 45542717 = 17078519) B17078519
theorem B2338127 : Blo 1557476 2338127 := bstep (se 1 (by rfl) ⟨1753595, by rfl⟩ : syracuseStep 2338127 = 3507191) B3507191
theorem B3943849 : Blo 1557476 3943849 := bstep (se 2 (by rfl) ⟨1478943, by rfl⟩ : syracuseStep 3943849 = 2957887) B2957887
theorem B2338217 : Blo 1557476 2338217 := bstep (se 2 (by rfl) ⟨876831, by rfl⟩ : syracuseStep 2338217 = 1753663) B1753663
theorem B5262839 : Blo 1557476 5262839 := bstep (se 1 (by rfl) ⟨3947129, by rfl⟩ : syracuseStep 5262839 = 7894259) B7894259
theorem B43232777 : Blo 1557476 43232777 := bstep (se 2 (by rfl) ⟨16212291, by rfl⟩ : syracuseStep 43232777 = 32424583) B32424583
theorem B2338367 : Blo 1557476 2338367 := bstep (se 1 (by rfl) ⟨1753775, by rfl⟩ : syracuseStep 2338367 = 3507551) B3507551
theorem B26611415 : Blo 1557476 26611415 := bstep (se 1 (by rfl) ⟨19958561, by rfl⟩ : syracuseStep 26611415 = 39917123) B39917123
theorem B11833127 : Blo 1557476 11833127 := bstep (se 1 (by rfl) ⟨8874845, by rfl⟩ : syracuseStep 11833127 = 17749691) B17749691
theorem B2338631 : Blo 1557476 2338631 := bstep (se 1 (by rfl) ⟨1753973, by rfl⟩ : syracuseStep 2338631 = 3507947) B3507947
theorem B3944335 : Blo 1557476 3944335 := bstep (se 1 (by rfl) ⟨2958251, by rfl⟩ : syracuseStep 3944335 = 5916503) B5916503
theorem B4992911 : Blo 1557476 4992911 := bstep (se 1 (by rfl) ⟨3744683, by rfl⟩ : syracuseStep 4992911 = 7489367) B7489367
theorem B2338715 : Blo 1557476 2338715 := bstep (se 1 (by rfl) ⟨1754036, by rfl⟩ : syracuseStep 2338715 = 3508073) B3508073
theorem B3329947 : Blo 1557476 3329947 := bstep (se 1 (by rfl) ⟨2497460, by rfl⟩ : syracuseStep 3329947 = 4994921) B4994921
theorem B4804559 : Blo 1557476 4804559 := bstep (se 1 (by rfl) ⟨3603419, by rfl⟩ : syracuseStep 4804559 = 7206839) B7206839
theorem B4435955 : Blo 1557476 4435955 := bstep (se 1 (by rfl) ⟨3326966, by rfl⟩ : syracuseStep 4435955 = 6653933) B6653933
theorem B39956489 : Blo 1557476 39956489 := bstep (se 2 (by rfl) ⟨14983683, by rfl⟩ : syracuseStep 39956489 = 29967367) B29967367
theorem B9990353 : Blo 1557476 9990353 := bstep (se 2 (by rfl) ⟨3746382, by rfl⟩ : syracuseStep 9990353 = 7492765) B7492765
theorem B1896679 : Blo 1557476 1896679 := bstep (se 1 (by rfl) ⟨1422509, by rfl⟩ : syracuseStep 1896679 = 2845019) B2845019
theorem B26620163 : Blo 1557476 26620163 := bstep (se 1 (by rfl) ⟨19965122, by rfl⟩ : syracuseStep 26620163 = 39930245) B39930245
theorem B21319969 : Blo 1557476 21319969 := bstep (se 2 (by rfl) ⟨7994988, by rfl⟩ : syracuseStep 21319969 = 15989977) B15989977
theorem B9990611 : Blo 1557476 9990611 := bstep (se 1 (by rfl) ⟨7492958, by rfl⟩ : syracuseStep 9990611 = 14985917) B14985917
theorem B2495071 : Blo 1557476 2495071 := bstep (se 1 (by rfl) ⟨1871303, by rfl⟩ : syracuseStep 2495071 = 3742607) B3742607
theorem B3945257 : Blo 1557476 3945257 := bstep (se 2 (by rfl) ⟨1479471, by rfl⟩ : syracuseStep 3945257 = 2958943) B2958943
theorem B1971307 : Blo 1557476 1971307 := bstep (se 1 (by rfl) ⟨1478480, by rfl⟩ : syracuseStep 1971307 = 2956961) B2956961
theorem B12989683 : Blo 1557476 12989683 := bstep (se 1 (by rfl) ⟨9742262, by rfl⟩ : syracuseStep 12989683 = 19484525) B19484525
theorem B1873307 : Blo 1557476 1873307 := bstep (se 1 (by rfl) ⟨1404980, by rfl⟩ : syracuseStep 1873307 = 2809961) B2809961
theorem B2496167 : Blo 1557476 2496167 := bstep (se 1 (by rfl) ⟨1872125, by rfl⟩ : syracuseStep 2496167 = 3744251) B3744251
theorem B6657707 : Blo 1557476 6657707 := bstep (se 1 (by rfl) ⟨4993280, by rfl⟩ : syracuseStep 6657707 = 9986561) B9986561
theorem B5257007 : Blo 1557476 5257007 := bstep (se 1 (by rfl) ⟨3942755, by rfl⟩ : syracuseStep 5257007 = 7885511) B7885511
theorem B14981071 : Blo 1557476 14981071 := bstep (se 1 (by rfl) ⟨11235803, by rfl⟩ : syracuseStep 14981071 = 22471607) B22471607
theorem B7886807 : Blo 1557476 7886807 := bstep (se 1 (by rfl) ⟨5915105, by rfl⟩ : syracuseStep 7886807 = 11830211) B11830211
theorem B8427503 : Blo 1557476 8427503 := bstep (se 1 (by rfl) ⟨6320627, by rfl⟩ : syracuseStep 8427503 = 12641255) B12641255
theorem B14972921 : Blo 1557476 14972921 := bstep (se 2 (by rfl) ⟨5614845, by rfl⟩ : syracuseStep 14972921 = 11229691) B11229691
theorem B7108667 : Blo 1557476 7108667 := bstep (se 1 (by rfl) ⟨5331500, by rfl⟩ : syracuseStep 7108667 = 10663001) B10663001
theorem B2218279 : Blo 1557476 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B4995371 : Blo 1557476 4995371 := bstep (se 1 (by rfl) ⟨3746528, by rfl⟩ : syracuseStep 4995371 = 7493057) B7493057
theorem B41613749 : Blo 1557476 41613749 := bstep (se 5 (by rfl) ⟨1950644, by rfl⟩ : syracuseStep 41613749 = 3901289) B3901289
theorem B7887293 : Blo 1557476 7887293 := bstep (se 3 (by rfl) ⟨1478867, by rfl⟩ : syracuseStep 7887293 = 2957735) B2957735
theorem B6404761 : Blo 1557476 6404761 := bstep (se 2 (by rfl) ⟨2401785, by rfl⟩ : syracuseStep 6404761 = 4803571) B4803571
theorem B14981921 : Blo 1557476 14981921 := bstep (se 2 (by rfl) ⟨5618220, by rfl⟩ : syracuseStep 14981921 = 11236441) B11236441
theorem B2628443 : Blo 1557476 2628443 := bstep (se 1 (by rfl) ⟨1971332, by rfl⟩ : syracuseStep 2628443 = 3942665) B3942665
theorem B2218843 : Blo 1557476 2218843 := bstep (se 1 (by rfl) ⟨1664132, by rfl⟩ : syracuseStep 2218843 = 3328265) B3328265
theorem B5618537 : Blo 1557476 5618537 := bstep (se 2 (by rfl) ⟨2106951, by rfl⟩ : syracuseStep 5618537 = 4213903) B4213903
theorem B3505103 : Blo 1557476 3505103 := bstep (se 1 (by rfl) ⟨2628827, by rfl⟩ : syracuseStep 3505103 = 5257655) B5257655
theorem B3505121 : Blo 1557476 3505121 := bstep (se 2 (by rfl) ⟨1314420, by rfl⟩ : syracuseStep 3505121 = 2628841) B2628841
theorem B3505193 : Blo 1557476 3505193 := bstep (se 2 (by rfl) ⟨1314447, by rfl⟩ : syracuseStep 3505193 = 2628895) B2628895
theorem B2628679 : Blo 1557476 2628679 := bstep (se 1 (by rfl) ⟨1971509, by rfl⟩ : syracuseStep 2628679 = 3943019) B3943019
theorem B2497871 : Blo 1557476 2497871 := bstep (se 1 (by rfl) ⟨1873403, by rfl⟩ : syracuseStep 2497871 = 3746807) B3746807
theorem B2497961 : Blo 1557476 2497961 := bstep (se 2 (by rfl) ⟨936735, by rfl⟩ : syracuseStep 2497961 = 1873471) B1873471
theorem B7798211 : Blo 1557476 7798211 := bstep (se 1 (by rfl) ⟨5848658, by rfl⟩ : syracuseStep 7798211 = 11697317) B11697317
theorem B2629111 : Blo 1557476 2629111 := bstep (se 1 (by rfl) ⟨1971833, by rfl⟩ : syracuseStep 2629111 = 3943667) B3943667
theorem B5258843 : Blo 1557476 5258843 := bstep (se 1 (by rfl) ⟨3944132, by rfl⟩ : syracuseStep 5258843 = 7888265) B7888265
theorem B5914255 : Blo 1557476 5914255 := bstep (se 1 (by rfl) ⟨4435691, by rfl⟩ : syracuseStep 5914255 = 8871383) B8871383
theorem B5619343 : Blo 1557476 5619343 := bstep (se 1 (by rfl) ⟨4214507, by rfl⟩ : syracuseStep 5619343 = 8429015) B8429015
theorem B41033405 : Blo 1557476 41033405 := bstep (se 3 (by rfl) ⟨7693763, by rfl⟩ : syracuseStep 41033405 = 15387527) B15387527
theorem B1752871 : Blo 1557476 1752871 := bstep (se 1 (by rfl) ⟨1314653, by rfl⟩ : syracuseStep 1752871 = 2629307) B2629307
theorem B2629415 : Blo 1557476 2629415 := bstep (se 1 (by rfl) ⟨1972061, by rfl⟩ : syracuseStep 2629415 = 3944123) B3944123
theorem B18947963 : Blo 1557476 18947963 := bstep (se 1 (by rfl) ⟨14210972, by rfl⟩ : syracuseStep 18947963 = 28421945) B28421945
theorem B2809723 : Blo 1557476 2809723 := bstep (se 1 (by rfl) ⟨2107292, by rfl⟩ : syracuseStep 2809723 = 4214585) B4214585
theorem B6660235 : Blo 1557476 6660235 := bstep (se 1 (by rfl) ⟨4995176, by rfl⟩ : syracuseStep 6660235 = 9990353) B9990353
theorem B3506363 : Blo 1557476 3506363 := bstep (se 1 (by rfl) ⟨2629772, by rfl⟩ : syracuseStep 3506363 = 5259545) B5259545
theorem B3506471 : Blo 1557476 3506471 := bstep (se 1 (by rfl) ⟨2629853, by rfl⟩ : syracuseStep 3506471 = 5259707) B5259707
theorem B6660407 : Blo 1557476 6660407 := bstep (se 1 (by rfl) ⟨4995305, by rfl⟩ : syracuseStep 6660407 = 9990611) B9990611
theorem B28426625 : Blo 1557476 28426625 := bstep (se 2 (by rfl) ⟨10659984, by rfl⟩ : syracuseStep 28426625 = 21319969) B21319969
theorem B2957705 : Blo 1557476 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B2630171 : Blo 1557476 2630171 := bstep (se 1 (by rfl) ⟨1972628, by rfl⟩ : syracuseStep 2630171 = 3945257) B3945257
theorem B1753627 : Blo 1557476 1753627 := bstep (se 1 (by rfl) ⟨1315220, by rfl⟩ : syracuseStep 1753627 = 2630441) B2630441
theorem B23986811 : Blo 1557476 23986811 := bstep (se 1 (by rfl) ⟨17990108, by rfl⟩ : syracuseStep 23986811 = 35980217) B35980217
theorem B3506849 : Blo 1557476 3506849 := bstep (se 2 (by rfl) ⟨1315068, by rfl⟩ : syracuseStep 3506849 = 2630137) B2630137
theorem B1753807 : Blo 1557476 1753807 := bstep (se 1 (by rfl) ⟨1315355, by rfl⟩ : syracuseStep 1753807 = 2630711) B2630711
theorem B33686225 : Blo 1557476 33686225 := bstep (se 2 (by rfl) ⟨12632334, by rfl⟩ : syracuseStep 33686225 = 25264669) B25264669
theorem B3326761 : Blo 1557476 3326761 := bstep (se 2 (by rfl) ⟨1247535, by rfl⟩ : syracuseStep 3326761 = 2495071) B2495071
theorem B35971897 : Blo 1557476 35971897 := bstep (se 2 (by rfl) ⟨13489461, by rfl⟩ : syracuseStep 35971897 = 26978923) B26978923
theorem B3507209 : Blo 1557476 3507209 := bstep (se 2 (by rfl) ⟨1315203, by rfl⟩ : syracuseStep 3507209 = 2630407) B2630407
theorem B13321259 : Blo 1557476 13321259 := bstep (se 1 (by rfl) ⟨9990944, by rfl⟩ : syracuseStep 13321259 = 19981889) B19981889
theorem B1557551 : Blo 1557476 1557551 := bstep (se 1 (by rfl) ⟨1168163, by rfl⟩ : syracuseStep 1557551 = 2336327) B2336327
theorem B6652991 : Blo 1557476 6652991 := bstep (se 1 (by rfl) ⟨4989743, by rfl⟩ : syracuseStep 6652991 = 9979487) B9979487
theorem B3507263 : Blo 1557476 3507263 := bstep (se 1 (by rfl) ⟨2630447, by rfl⟩ : syracuseStep 3507263 = 5260895) B5260895
theorem B1557615 : Blo 1557476 1557615 := bstep (se 1 (by rfl) ⟨1168211, by rfl⟩ : syracuseStep 1557615 = 2336423) B2336423
theorem B1664111 : Blo 1557476 1664111 := bstep (se 1 (by rfl) ⟨1248083, by rfl⟩ : syracuseStep 1664111 = 2496167) B2496167
theorem B2958457 : Blo 1557476 2958457 := bstep (se 2 (by rfl) ⟨1109421, by rfl⟩ : syracuseStep 2958457 = 2218843) B2218843
theorem B1557671 : Blo 1557476 1557671 := bstep (se 1 (by rfl) ⟨1168253, by rfl⟩ : syracuseStep 1557671 = 2336507) B2336507
theorem B5260463 : Blo 1557476 5260463 := bstep (se 1 (by rfl) ⟨3945347, by rfl⟩ : syracuseStep 5260463 = 7890695) B7890695
theorem B1557695 : Blo 1557476 1557695 := bstep (se 1 (by rfl) ⟨1168271, by rfl⟩ : syracuseStep 1557695 = 2336543) B2336543
theorem B1557727 : Blo 1557476 1557727 := bstep (se 1 (by rfl) ⟨1168295, by rfl⟩ : syracuseStep 1557727 = 2336591) B2336591
theorem B1557807 : Blo 1557476 1557807 := bstep (se 1 (by rfl) ⟨1168355, by rfl⟩ : syracuseStep 1557807 = 2336711) B2336711
theorem B1558043 : Blo 1557476 1558043 := bstep (se 1 (by rfl) ⟨1168532, by rfl⟩ : syracuseStep 1558043 = 2337065) B2337065
theorem B1558047 : Blo 1557476 1558047 := bstep (se 1 (by rfl) ⟨1168535, by rfl⟩ : syracuseStep 1558047 = 2337071) B2337071
theorem B17319577 : Blo 1557476 17319577 := bstep (se 2 (by rfl) ⟨6494841, by rfl⟩ : syracuseStep 17319577 = 12989683) B12989683
theorem B1558207 : Blo 1557476 1558207 := bstep (se 1 (by rfl) ⟨1168655, by rfl⟩ : syracuseStep 1558207 = 2337311) B2337311
theorem B5998271 : Blo 1557476 5998271 := bstep (se 1 (by rfl) ⟨4498703, by rfl⟩ : syracuseStep 5998271 = 8997407) B8997407
theorem B2999999 : Blo 1557476 2999999 := bstep (se 1 (by rfl) ⟨2249999, by rfl⟩ : syracuseStep 2999999 = 4499999) B4499999
theorem B109422413 : Blo 1557476 109422413 := bstep (se 3 (by rfl) ⟨20516702, by rfl⟩ : syracuseStep 109422413 = 41033405) B41033405
theorem B9987947 : Blo 1557476 9987947 := bstep (se 1 (by rfl) ⟨7490960, by rfl⟩ : syracuseStep 9987947 = 14981921) B14981921
theorem B3745691 : Blo 1557476 3745691 := bstep (se 1 (by rfl) ⟨2809268, by rfl⟩ : syracuseStep 3745691 = 5618537) B5618537
theorem B1558463 : Blo 1557476 1558463 := bstep (se 1 (by rfl) ⟨1168847, by rfl⟩ : syracuseStep 1558463 = 2337695) B2337695
theorem B2336735 : Blo 1557476 2336735 := bstep (se 1 (by rfl) ⟨1752551, by rfl⟩ : syracuseStep 2336735 = 3505103) B3505103
theorem B1558495 : Blo 1557476 1558495 := bstep (se 1 (by rfl) ⟨1168871, by rfl⟩ : syracuseStep 1558495 = 2337743) B2337743
theorem B3508199 : Blo 1557476 3508199 := bstep (se 1 (by rfl) ⟨2631149, by rfl⟩ : syracuseStep 3508199 = 5262299) B5262299
theorem B2336747 : Blo 1557476 2336747 := bstep (se 1 (by rfl) ⟨1752560, by rfl⟩ : syracuseStep 2336747 = 3505121) B3505121
theorem B2336795 : Blo 1557476 2336795 := bstep (se 1 (by rfl) ⟨1752596, by rfl⟩ : syracuseStep 2336795 = 3505193) B3505193
theorem B1558555 : Blo 1557476 1558555 := bstep (se 1 (by rfl) ⟨1168916, by rfl⟩ : syracuseStep 1558555 = 2337833) B2337833
theorem B1558559 : Blo 1557476 1558559 := bstep (se 1 (by rfl) ⟨1168919, by rfl⟩ : syracuseStep 1558559 = 2337839) B2337839
theorem B1558575 : Blo 1557476 1558575 := bstep (se 1 (by rfl) ⟨1168931, by rfl⟩ : syracuseStep 1558575 = 2337863) B2337863
theorem B7489691 : Blo 1557476 7489691 := bstep (se 1 (by rfl) ⟨5617268, by rfl⟩ : syracuseStep 7489691 = 11234537) B11234537
theorem B3508379 : Blo 1557476 3508379 := bstep (se 1 (by rfl) ⟨2631284, by rfl⟩ : syracuseStep 3508379 = 5262569) B5262569
theorem B30361811 : Blo 1557476 30361811 := bstep (se 1 (by rfl) ⟨22771358, by rfl⟩ : syracuseStep 30361811 = 45542717) B45542717
theorem B1558751 : Blo 1557476 1558751 := bstep (se 1 (by rfl) ⟨1169063, by rfl⟩ : syracuseStep 1558751 = 2338127) B2338127
theorem B1665247 : Blo 1557476 1665247 := bstep (se 1 (by rfl) ⟨1248935, by rfl⟩ : syracuseStep 1665247 = 2497871) B2497871
theorem B1558811 : Blo 1557476 1558811 := bstep (se 1 (by rfl) ⟨1169108, by rfl⟩ : syracuseStep 1558811 = 2338217) B2338217
theorem B1665307 : Blo 1557476 1665307 := bstep (se 1 (by rfl) ⟨1248980, by rfl⟩ : syracuseStep 1665307 = 2497961) B2497961
theorem B3508559 : Blo 1557476 3508559 := bstep (se 1 (by rfl) ⟨2631419, by rfl⟩ : syracuseStep 3508559 = 5262839) B5262839
theorem B28821851 : Blo 1557476 28821851 := bstep (se 1 (by rfl) ⟨21616388, by rfl⟩ : syracuseStep 28821851 = 43232777) B43232777
theorem B1558911 : Blo 1557476 1558911 := bstep (se 1 (by rfl) ⟨1169183, by rfl⟩ : syracuseStep 1558911 = 2338367) B2338367
theorem B2337161 : Blo 1557476 2337161 := bstep (se 2 (by rfl) ⟨876435, by rfl⟩ : syracuseStep 2337161 = 1752871) B1752871
theorem B3508649 : Blo 1557476 3508649 := bstep (se 2 (by rfl) ⟨1315743, by rfl⟩ : syracuseStep 3508649 = 2631487) B2631487
theorem B3746297 : Blo 1557476 3746297 := bstep (se 2 (by rfl) ⟨1404861, by rfl⟩ : syracuseStep 3746297 = 2809723) B2809723
theorem B1559087 : Blo 1557476 1559087 := bstep (se 1 (by rfl) ⟨1169315, by rfl⟩ : syracuseStep 1559087 = 2338631) B2338631
theorem B3328607 : Blo 1557476 3328607 := bstep (se 1 (by rfl) ⟨2496455, by rfl⟩ : syracuseStep 3328607 = 4992911) B4992911
theorem B1559143 : Blo 1557476 1559143 := bstep (se 1 (by rfl) ⟨1169357, by rfl⟩ : syracuseStep 1559143 = 2338715) B2338715
theorem B19974761 : Blo 1557476 19974761 := bstep (se 2 (by rfl) ⟨7490535, by rfl⟩ : syracuseStep 19974761 = 14981071) B14981071
theorem B2960135 : Blo 1557476 2960135 := bstep (se 1 (by rfl) ⟨2220101, by rfl⟩ : syracuseStep 2960135 = 4440203) B4440203
theorem B17746775 : Blo 1557476 17746775 := bstep (se 1 (by rfl) ⟨13310081, by rfl⟩ : syracuseStep 17746775 = 26620163) B26620163
theorem B108030955 : Blo 1557476 108030955 := bstep (se 1 (by rfl) ⟨81023216, by rfl⟩ : syracuseStep 108030955 = 162046433) B162046433
theorem B2338103 : Blo 1557476 2338103 := bstep (se 1 (by rfl) ⟨1753577, by rfl⟩ : syracuseStep 2338103 = 3507155) B3507155
theorem B2338271 : Blo 1557476 2338271 := bstep (se 1 (by rfl) ⟨1753703, by rfl⟩ : syracuseStep 2338271 = 3507407) B3507407
theorem B8539681 : Blo 1557476 8539681 := bstep (se 2 (by rfl) ⟨3202380, by rfl⟩ : syracuseStep 8539681 = 6404761) B6404761
theorem B2338487 : Blo 1557476 2338487 := bstep (se 1 (by rfl) ⟨1753865, by rfl⟩ : syracuseStep 2338487 = 3507731) B3507731
theorem B2338697 : Blo 1557476 2338697 := bstep (se 2 (by rfl) ⟨877011, by rfl⟩ : syracuseStep 2338697 = 1754023) B1754023
theorem B9981947 : Blo 1557476 9981947 := bstep (se 1 (by rfl) ⟨7486460, by rfl⟩ : syracuseStep 9981947 = 14972921) B14972921
theorem B4739111 : Blo 1557476 4739111 := bstep (se 1 (by rfl) ⟨3554333, by rfl⟩ : syracuseStep 4739111 = 7108667) B7108667
theorem B2338943 : Blo 1557476 2338943 := bstep (se 1 (by rfl) ⟨1754207, by rfl⟩ : syracuseStep 2338943 = 3508415) B3508415
theorem B3330247 : Blo 1557476 3330247 := bstep (se 1 (by rfl) ⟨2497685, by rfl⟩ : syracuseStep 3330247 = 4995371) B4995371
theorem B4993255 : Blo 1557476 4993255 := bstep (se 1 (by rfl) ⟨3744941, by rfl⟩ : syracuseStep 4993255 = 7489883) B7489883
theorem B27742499 : Blo 1557476 27742499 := bstep (se 1 (by rfl) ⟨20806874, by rfl⟩ : syracuseStep 27742499 = 41613749) B41613749
theorem B29946455 : Blo 1557476 29946455 := bstep (se 1 (by rfl) ⟨22459841, by rfl⟩ : syracuseStep 29946455 = 44919683) B44919683
theorem B242954923 : Blo 1557476 242954923 := bstep (se 1 (by rfl) ⟨182216192, by rfl⟩ : syracuseStep 242954923 = 364432385) B364432385
theorem B7885673 : Blo 1557476 7885673 := bstep (se 2 (by rfl) ⟨2957127, by rfl⟩ : syracuseStep 7885673 = 5914255) B5914255
theorem B7492457 : Blo 1557476 7492457 := bstep (se 2 (by rfl) ⟨2809671, by rfl⟩ : syracuseStep 7492457 = 5619343) B5619343
theorem B5198807 : Blo 1557476 5198807 := bstep (se 1 (by rfl) ⟨3899105, by rfl⟩ : syracuseStep 5198807 = 7798211) B7798211
theorem B17740943 : Blo 1557476 17740943 := bstep (se 1 (by rfl) ⟨13305707, by rfl⟩ : syracuseStep 17740943 = 26611415) B26611415
theorem B5256521 : Blo 1557476 5256521 := bstep (se 2 (by rfl) ⟨1971195, by rfl⟩ : syracuseStep 5256521 = 3942391) B3942391
theorem B26637659 : Blo 1557476 26637659 := bstep (se 1 (by rfl) ⟨19978244, by rfl⟩ : syracuseStep 26637659 = 39956489) B39956489
theorem B2528905 : Blo 1557476 2528905 := bstep (se 2 (by rfl) ⟨948339, by rfl⟩ : syracuseStep 2528905 = 1896679) B1896679
theorem B1972127 : Blo 1557476 1972127 := bstep (se 1 (by rfl) ⟨1479095, by rfl⟩ : syracuseStep 1972127 = 2958191) B2958191
theorem B3946745 : Blo 1557476 3946745 := bstep (se 2 (by rfl) ⟨1480029, by rfl⟩ : syracuseStep 3946745 = 2960059) B2960059
theorem B4995485 : Blo 1557476 4995485 := bstep (se 3 (by rfl) ⟨936653, by rfl⟩ : syracuseStep 4995485 = 1873307) B1873307
theorem B4438471 : Blo 1557476 4438471 := bstep (se 1 (by rfl) ⟨3328853, by rfl⟩ : syracuseStep 4438471 = 6657707) B6657707
theorem B3504671 : Blo 1557476 3504671 := bstep (se 1 (by rfl) ⟨2628503, by rfl⟩ : syracuseStep 3504671 = 5257007) B5257007
theorem B5257871 : Blo 1557476 5257871 := bstep (se 1 (by rfl) ⟨3943403, by rfl⟩ : syracuseStep 5257871 = 7886807) B7886807
theorem B5618335 : Blo 1557476 5618335 := bstep (se 1 (by rfl) ⟨4213751, by rfl⟩ : syracuseStep 5618335 = 8427503) B8427503
theorem B3504905 : Blo 1557476 3504905 := bstep (se 2 (by rfl) ⟨1314339, by rfl⟩ : syracuseStep 3504905 = 2628679) B2628679
theorem B2628409 : Blo 1557476 2628409 := bstep (se 2 (by rfl) ⟨985653, by rfl⟩ : syracuseStep 2628409 = 1971307) B1971307
theorem B2628463 : Blo 1557476 2628463 := bstep (se 1 (by rfl) ⟨1971347, by rfl⟩ : syracuseStep 2628463 = 3942695) B3942695
theorem B5258195 : Blo 1557476 5258195 := bstep (se 1 (by rfl) ⟨3943646, by rfl⟩ : syracuseStep 5258195 = 7887293) B7887293
theorem B6659279 : Blo 1557476 6659279 := bstep (se 1 (by rfl) ⟨4994459, by rfl⟩ : syracuseStep 6659279 = 9988919) B9988919
theorem B5258465 : Blo 1557476 5258465 := bstep (se 2 (by rfl) ⟨1971924, by rfl⟩ : syracuseStep 5258465 = 3943849) B3943849
theorem B1752295 : Blo 1557476 1752295 := bstep (se 1 (by rfl) ⟨1314221, by rfl⟩ : syracuseStep 1752295 = 2628443) B2628443
theorem B1973575 : Blo 1557476 1973575 := bstep (se 1 (by rfl) ⟨1480181, by rfl⟩ : syracuseStep 1973575 = 2960363) B2960363
theorem B3505481 : Blo 1557476 3505481 := bstep (se 2 (by rfl) ⟨1314555, by rfl⟩ : syracuseStep 3505481 = 2629111) B2629111
theorem B50527901 : Blo 1557476 50527901 := bstep (se 3 (by rfl) ⟨9473981, by rfl⟩ : syracuseStep 50527901 = 18947963) B18947963
theorem B3505895 : Blo 1557476 3505895 := bstep (se 1 (by rfl) ⟨2629421, by rfl⟩ : syracuseStep 3505895 = 5258843) B5258843
theorem B5259113 : Blo 1557476 5259113 := bstep (se 2 (by rfl) ⟨1972167, by rfl⟩ : syracuseStep 5259113 = 3944335) B3944335
theorem B1752943 : Blo 1557476 1752943 := bstep (se 1 (by rfl) ⟨1314707, by rfl⟩ : syracuseStep 1752943 = 2629415) B2629415
theorem B7888751 : Blo 1557476 7888751 := bstep (se 1 (by rfl) ⟨5916563, by rfl⟩ : syracuseStep 7888751 = 11833127) B11833127
theorem B4439929 : Blo 1557476 4439929 := bstep (se 2 (by rfl) ⟨1664973, by rfl⟩ : syracuseStep 4439929 = 3329947) B3329947
theorem B3203039 : Blo 1557476 3203039 := bstep (se 1 (by rfl) ⟨2402279, by rfl⟩ : syracuseStep 3203039 = 4804559) B4804559
theorem B2957303 : Blo 1557476 2957303 := bstep (se 1 (by rfl) ⟨2217977, by rfl⟩ : syracuseStep 2957303 = 4435955) B4435955
theorem B8880313 : Blo 1557476 8880313 := bstep (se 2 (by rfl) ⟨3330117, by rfl⟩ : syracuseStep 8880313 = 6660235) B6660235
theorem B4440271 : Blo 1557476 4440271 := bstep (se 1 (by rfl) ⟨3330203, by rfl⟩ : syracuseStep 4440271 = 6660407) B6660407
theorem B4440329 : Blo 1557476 4440329 := bstep (se 2 (by rfl) ⟨1665123, by rfl⟩ : syracuseStep 4440329 = 3330247) B3330247
theorem B2220329 : Blo 1557476 2220329 := bstep (se 2 (by rfl) ⟨832623, by rfl⟩ : syracuseStep 2220329 = 1665247) B1665247
theorem B1753447 : Blo 1557476 1753447 := bstep (se 1 (by rfl) ⟨1315085, by rfl⟩ : syracuseStep 1753447 = 2630171) B2630171
theorem B2220409 : Blo 1557476 2220409 := bstep (se 2 (by rfl) ⟨832653, by rfl⟩ : syracuseStep 2220409 = 1665307) B1665307
theorem B19964303 : Blo 1557476 19964303 := bstep (se 1 (by rfl) ⟨14973227, by rfl⟩ : syracuseStep 19964303 = 29946455) B29946455
theorem B3465871 : Blo 1557476 3465871 := bstep (se 1 (by rfl) ⟨2599403, by rfl⟩ : syracuseStep 3465871 = 5198807) B5198807
theorem B8880839 : Blo 1557476 8880839 := bstep (se 1 (by rfl) ⟨6660629, by rfl⟩ : syracuseStep 8880839 = 13321259) B13321259
theorem B3506975 : Blo 1557476 3506975 := bstep (se 1 (by rfl) ⟨2630231, by rfl⟩ : syracuseStep 3506975 = 5260463) B5260463
theorem B1999999 : Blo 1557476 1999999 := bstep (se 1 (by rfl) ⟨1499999, by rfl⟩ : syracuseStep 1999999 = 2999999) B2999999
theorem B144041273 : Blo 1557476 144041273 := bstep (se 2 (by rfl) ⟨54015477, by rfl⟩ : syracuseStep 144041273 = 108030955) B108030955
theorem B1557823 : Blo 1557476 1557823 := bstep (se 1 (by rfl) ⟨1168367, by rfl⟩ : syracuseStep 1557823 = 2336735) B2336735
theorem B1557831 : Blo 1557476 1557831 := bstep (se 1 (by rfl) ⟨1168373, by rfl⟩ : syracuseStep 1557831 = 2336747) B2336747
theorem B1557863 : Blo 1557476 1557863 := bstep (se 1 (by rfl) ⟨1168397, by rfl⟩ : syracuseStep 1557863 = 2336795) B2336795
theorem B2631163 : Blo 1557476 2631163 := bstep (se 1 (by rfl) ⟨1973372, by rfl⟩ : syracuseStep 2631163 = 3946745) B3946745
theorem B1558107 : Blo 1557476 1558107 := bstep (se 1 (by rfl) ⟨1168580, by rfl⟩ : syracuseStep 1558107 = 2337161) B2337161
theorem B2336393 : Blo 1557476 2336393 := bstep (se 2 (by rfl) ⟨876147, by rfl⟩ : syracuseStep 2336393 = 1752295) B1752295
theorem B63964829 : Blo 1557476 63964829 := bstep (se 3 (by rfl) ⟨11993405, by rfl⟩ : syracuseStep 63964829 = 23986811) B23986811
theorem B2336447 : Blo 1557476 2336447 := bstep (se 1 (by rfl) ⟨1752335, by rfl⟩ : syracuseStep 2336447 = 3504671) B3504671
theorem B2631433 : Blo 1557476 2631433 := bstep (se 2 (by rfl) ⟨986787, by rfl⟩ : syracuseStep 2631433 = 1973575) B1973575
theorem B2336603 : Blo 1557476 2336603 := bstep (se 1 (by rfl) ⟨1752452, by rfl⟩ : syracuseStep 2336603 = 3504905) B3504905
theorem B11831183 : Blo 1557476 11831183 := bstep (se 1 (by rfl) ⟨8873387, by rfl⟩ : syracuseStep 11831183 = 17746775) B17746775
theorem B1558735 : Blo 1557476 1558735 := bstep (se 1 (by rfl) ⟨1169051, by rfl⟩ : syracuseStep 1558735 = 2338103) B2338103
theorem B2336987 : Blo 1557476 2336987 := bstep (se 1 (by rfl) ⟨1752740, by rfl⟩ : syracuseStep 2336987 = 3505481) B3505481
theorem B1558847 : Blo 1557476 1558847 := bstep (se 1 (by rfl) ⟨1169135, by rfl⟩ : syracuseStep 1558847 = 2338271) B2338271
theorem B1558991 : Blo 1557476 1558991 := bstep (se 1 (by rfl) ⟨1169243, by rfl⟩ : syracuseStep 1558991 = 2338487) B2338487
theorem B2337257 : Blo 1557476 2337257 := bstep (se 2 (by rfl) ⟨876471, by rfl⟩ : syracuseStep 2337257 = 1752943) B1752943
theorem B2337263 : Blo 1557476 2337263 := bstep (se 1 (by rfl) ⟨1752947, by rfl⟩ : syracuseStep 2337263 = 3505895) B3505895
theorem B1559131 : Blo 1557476 1559131 := bstep (se 1 (by rfl) ⟨1169348, by rfl⟩ : syracuseStep 1559131 = 2338697) B2338697
theorem B6654631 : Blo 1557476 6654631 := bstep (se 1 (by rfl) ⟨4990973, by rfl⟩ : syracuseStep 6654631 = 9981947) B9981947
theorem B1559295 : Blo 1557476 1559295 := bstep (se 1 (by rfl) ⟨1169471, by rfl⟩ : syracuseStep 1559295 = 2338943) B2338943
theorem B2337575 : Blo 1557476 2337575 := bstep (se 1 (by rfl) ⟨1753181, by rfl⟩ : syracuseStep 2337575 = 3506363) B3506363
theorem B2337647 : Blo 1557476 2337647 := bstep (se 1 (by rfl) ⟨1753235, by rfl⟩ : syracuseStep 2337647 = 3506471) B3506471
theorem B18951083 : Blo 1557476 18951083 := bstep (se 1 (by rfl) ⟨14213312, by rfl⟩ : syracuseStep 18951083 = 28426625) B28426625
theorem B2337899 : Blo 1557476 2337899 := bstep (se 1 (by rfl) ⟨1753424, by rfl⟩ : syracuseStep 2337899 = 3506849) B3506849
theorem B22457483 : Blo 1557476 22457483 := bstep (se 1 (by rfl) ⟨16843112, by rfl⟩ : syracuseStep 22457483 = 33686225) B33686225
theorem B80964829 : Blo 1557476 80964829 := bstep (se 3 (by rfl) ⟨15180905, by rfl⟩ : syracuseStep 80964829 = 30361811) B30361811
theorem B5917961 : Blo 1557476 5917961 := bstep (se 2 (by rfl) ⟨2219235, by rfl⟩ : syracuseStep 5917961 = 4438471) B4438471
theorem B2338139 : Blo 1557476 2338139 := bstep (se 1 (by rfl) ⟨1753604, by rfl⟩ : syracuseStep 2338139 = 3507209) B3507209
theorem B2338169 : Blo 1557476 2338169 := bstep (se 2 (by rfl) ⟨876813, by rfl⟩ : syracuseStep 2338169 = 1753627) B1753627
theorem B4435327 : Blo 1557476 4435327 := bstep (se 1 (by rfl) ⟨3326495, by rfl⟩ : syracuseStep 4435327 = 6652991) B6652991
theorem B2338175 : Blo 1557476 2338175 := bstep (se 1 (by rfl) ⟨1753631, by rfl⟩ : syracuseStep 2338175 = 3507263) B3507263
theorem B7491113 : Blo 1557476 7491113 := bstep (se 2 (by rfl) ⟨2809167, by rfl⟩ : syracuseStep 7491113 = 5618335) B5618335
theorem B323939897 : Blo 1557476 323939897 := bstep (se 2 (by rfl) ⟨121477461, by rfl⟩ : syracuseStep 323939897 = 242954923) B242954923
theorem B2338409 : Blo 1557476 2338409 := bstep (se 2 (by rfl) ⟨876903, by rfl⟩ : syracuseStep 2338409 = 1753807) B1753807
theorem B4435681 : Blo 1557476 4435681 := bstep (se 2 (by rfl) ⟨1663380, by rfl⟩ : syracuseStep 4435681 = 3326761) B3326761
theorem B9990125 : Blo 1557476 9990125 := bstep (se 3 (by rfl) ⟨1873148, by rfl⟩ : syracuseStep 9990125 = 3746297) B3746297
theorem B2338799 : Blo 1557476 2338799 := bstep (se 1 (by rfl) ⟨1754099, by rfl⟩ : syracuseStep 2338799 = 3508199) B3508199
theorem B4993127 : Blo 1557476 4993127 := bstep (se 1 (by rfl) ⟨3744845, by rfl⟩ : syracuseStep 4993127 = 7489691) B7489691
theorem B2338919 : Blo 1557476 2338919 := bstep (se 1 (by rfl) ⟨1754189, by rfl⟩ : syracuseStep 2338919 = 3508379) B3508379
theorem B3944609 : Blo 1557476 3944609 := bstep (se 2 (by rfl) ⟨1479228, by rfl⟩ : syracuseStep 3944609 = 2958457) B2958457
theorem B2339039 : Blo 1557476 2339039 := bstep (se 1 (by rfl) ⟨1754279, by rfl⟩ : syracuseStep 2339039 = 3508559) B3508559
theorem B19214567 : Blo 1557476 19214567 := bstep (se 1 (by rfl) ⟨14410925, by rfl⟩ : syracuseStep 19214567 = 28821851) B28821851
theorem B3330323 : Blo 1557476 3330323 := bstep (se 1 (by rfl) ⟨2497742, by rfl⟩ : syracuseStep 3330323 = 4995485) B4995485
theorem B2339099 : Blo 1557476 2339099 := bstep (se 1 (by rfl) ⟨1754324, by rfl⟩ : syracuseStep 2339099 = 3508649) B3508649
theorem B13316507 : Blo 1557476 13316507 := bstep (se 1 (by rfl) ⟨9987380, by rfl⟩ : syracuseStep 13316507 = 19974761) B19974761
theorem B15995389 : Blo 1557476 15995389 := bstep (se 3 (by rfl) ⟨2999135, by rfl⟩ : syracuseStep 15995389 = 5998271) B5998271
theorem B3371873 : Blo 1557476 3371873 := bstep (se 2 (by rfl) ⟨1264452, by rfl⟩ : syracuseStep 3371873 = 2528905) B2528905
theorem B5919905 : Blo 1557476 5919905 := bstep (se 2 (by rfl) ⟨2219964, by rfl⟩ : syracuseStep 5919905 = 4439929) B4439929
theorem B2135359 : Blo 1557476 2135359 := bstep (se 1 (by rfl) ⟨1601519, by rfl⟩ : syracuseStep 2135359 = 3203039) B3203039
theorem B1971535 : Blo 1557476 1971535 := bstep (se 1 (by rfl) ⟨1478651, by rfl⟩ : syracuseStep 1971535 = 2957303) B2957303
theorem B3159407 : Blo 1557476 3159407 := bstep (se 1 (by rfl) ⟨2369555, by rfl⟩ : syracuseStep 3159407 = 4739111) B4739111
theorem B18494999 : Blo 1557476 18494999 := bstep (se 1 (by rfl) ⟨13871249, by rfl⟩ : syracuseStep 18494999 = 27742499) B27742499
theorem B1971803 : Blo 1557476 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B4437629 : Blo 1557476 4437629 := bstep (se 3 (by rfl) ⟨832055, by rfl⟩ : syracuseStep 4437629 = 1664111) B1664111
theorem B6657673 : Blo 1557476 6657673 := bstep (se 2 (by rfl) ⟨2496627, by rfl⟩ : syracuseStep 6657673 = 4993255) B4993255
theorem B5257115 : Blo 1557476 5257115 := bstep (se 1 (by rfl) ⟨3942836, by rfl⟩ : syracuseStep 5257115 = 7885673) B7885673
theorem B11827295 : Blo 1557476 11827295 := bstep (se 1 (by rfl) ⟨8870471, by rfl⟩ : syracuseStep 11827295 = 17740943) B17740943
theorem B3504347 : Blo 1557476 3504347 := bstep (se 1 (by rfl) ⟨2628260, by rfl⟩ : syracuseStep 3504347 = 5256521) B5256521
theorem B17758439 : Blo 1557476 17758439 := bstep (se 1 (by rfl) ⟨13318829, by rfl⟩ : syracuseStep 17758439 = 26637659) B26637659
theorem B3504545 : Blo 1557476 3504545 := bstep (se 2 (by rfl) ⟨1314204, by rfl⟩ : syracuseStep 3504545 = 2628409) B2628409
theorem B47962529 : Blo 1557476 47962529 := bstep (se 2 (by rfl) ⟨17985948, by rfl⟩ : syracuseStep 47962529 = 35971897) B35971897
theorem B3504617 : Blo 1557476 3504617 := bstep (se 2 (by rfl) ⟨1314231, by rfl⟩ : syracuseStep 3504617 = 2628463) B2628463
theorem B72948275 : Blo 1557476 72948275 := bstep (se 1 (by rfl) ⟨54711206, by rfl⟩ : syracuseStep 72948275 = 109422413) B109422413
theorem B6658631 : Blo 1557476 6658631 := bstep (se 1 (by rfl) ⟨4993973, by rfl⟩ : syracuseStep 6658631 = 9987947) B9987947
theorem B2497127 : Blo 1557476 2497127 := bstep (se 1 (by rfl) ⟨1872845, by rfl⟩ : syracuseStep 2497127 = 3745691) B3745691
theorem B2219071 : Blo 1557476 2219071 := bstep (se 1 (by rfl) ⟨1664303, by rfl⟩ : syracuseStep 2219071 = 3328607) B3328607
theorem B3505247 : Blo 1557476 3505247 := bstep (se 1 (by rfl) ⟨2628935, by rfl⟩ : syracuseStep 3505247 = 5257871) B5257871
theorem B1973423 : Blo 1557476 1973423 := bstep (se 1 (by rfl) ⟨1480067, by rfl⟩ : syracuseStep 1973423 = 2960135) B2960135
theorem B3505463 : Blo 1557476 3505463 := bstep (se 1 (by rfl) ⟨2629097, by rfl⟩ : syracuseStep 3505463 = 5258195) B5258195
theorem B11386241 : Blo 1557476 11386241 := bstep (se 2 (by rfl) ⟨4269840, by rfl⟩ : syracuseStep 11386241 = 8539681) B8539681
theorem B4439519 : Blo 1557476 4439519 := bstep (se 1 (by rfl) ⟨3329639, by rfl⟩ : syracuseStep 4439519 = 6659279) B6659279
theorem B3505643 : Blo 1557476 3505643 := bstep (se 1 (by rfl) ⟨2629232, by rfl⟩ : syracuseStep 3505643 = 5258465) B5258465
theorem B23092769 : Blo 1557476 23092769 := bstep (se 2 (by rfl) ⟨8659788, by rfl⟩ : syracuseStep 23092769 = 17319577) B17319577
theorem B19979885 : Blo 1557476 19979885 := bstep (se 3 (by rfl) ⟨3746228, by rfl⟩ : syracuseStep 19979885 = 7492457) B7492457
theorem B5259005 : Blo 1557476 5259005 := bstep (se 3 (by rfl) ⟨986063, by rfl⟩ : syracuseStep 5259005 = 1972127) B1972127
theorem B33685267 : Blo 1557476 33685267 := bstep (se 1 (by rfl) ⟨25263950, by rfl⟩ : syracuseStep 33685267 = 50527901) B50527901
theorem B3506075 : Blo 1557476 3506075 := bstep (se 1 (by rfl) ⟨2629556, by rfl⟩ : syracuseStep 3506075 = 5259113) B5259113
theorem B5259167 : Blo 1557476 5259167 := bstep (se 1 (by rfl) ⟨3944375, by rfl⟩ : syracuseStep 5259167 = 7888751) B7888751
theorem B2629739 : Blo 1557476 2629739 := bstep (se 1 (by rfl) ⟨1972304, by rfl⟩ : syracuseStep 2629739 = 3944609) B3944609
theorem B2220215 : Blo 1557476 2220215 := bstep (se 1 (by rfl) ⟨1665161, by rfl⟩ : syracuseStep 2220215 = 3330323) B3330323
theorem B96027515 : Blo 1557476 96027515 := bstep (se 1 (by rfl) ⟨72020636, by rfl⟩ : syracuseStep 96027515 = 144041273) B144041273
theorem B8872841 : Blo 1557476 8872841 := bstep (se 2 (by rfl) ⟨3327315, by rfl⟩ : syracuseStep 8872841 = 6654631) B6654631
theorem B2106271 : Blo 1557476 2106271 := bstep (se 1 (by rfl) ⟨1579703, by rfl⟩ : syracuseStep 2106271 = 3159407) B3159407
theorem B12329999 : Blo 1557476 12329999 := bstep (se 1 (by rfl) ⟨9247499, by rfl⟩ : syracuseStep 12329999 = 18494999) B18494999
theorem B2958419 : Blo 1557476 2958419 := bstep (se 1 (by rfl) ⟨2218814, by rfl⟩ : syracuseStep 2958419 = 4437629) B4437629
theorem B1557595 : Blo 1557476 1557595 := bstep (se 1 (by rfl) ⟨1168196, by rfl⟩ : syracuseStep 1557595 = 2336393) B2336393
theorem B1557631 : Blo 1557476 1557631 := bstep (se 1 (by rfl) ⟨1168223, by rfl⟩ : syracuseStep 1557631 = 2336447) B2336447
theorem B1557735 : Blo 1557476 1557735 := bstep (se 1 (by rfl) ⟨1168301, by rfl⟩ : syracuseStep 1557735 = 2336603) B2336603
theorem B2958761 : Blo 1557476 2958761 := bstep (se 2 (by rfl) ⟨1109535, by rfl⟩ : syracuseStep 2958761 = 2219071) B2219071
theorem B2336231 : Blo 1557476 2336231 := bstep (se 1 (by rfl) ⟨1752173, by rfl⟩ : syracuseStep 2336231 = 3504347) B3504347
theorem B1557991 : Blo 1557476 1557991 := bstep (se 1 (by rfl) ⟨1168493, by rfl⟩ : syracuseStep 1557991 = 2336987) B2336987
theorem B11838959 : Blo 1557476 11838959 := bstep (se 1 (by rfl) ⟨8879219, by rfl⟩ : syracuseStep 11838959 = 17758439) B17758439
theorem B2336363 : Blo 1557476 2336363 := bstep (se 1 (by rfl) ⟨1752272, by rfl⟩ : syracuseStep 2336363 = 3504545) B3504545
theorem B31975019 : Blo 1557476 31975019 := bstep (se 1 (by rfl) ⟨23981264, by rfl⟩ : syracuseStep 31975019 = 47962529) B47962529
theorem B2336411 : Blo 1557476 2336411 := bstep (se 1 (by rfl) ⟨1752308, by rfl⟩ : syracuseStep 2336411 = 3504617) B3504617
theorem B1558171 : Blo 1557476 1558171 := bstep (se 1 (by rfl) ⟨1168628, by rfl⟩ : syracuseStep 1558171 = 2337257) B2337257
theorem B1558175 : Blo 1557476 1558175 := bstep (se 1 (by rfl) ⟨1168631, by rfl⟩ : syracuseStep 1558175 = 2337263) B2337263
theorem B1558383 : Blo 1557476 1558383 := bstep (se 1 (by rfl) ⟨1168787, by rfl⟩ : syracuseStep 1558383 = 2337575) B2337575
theorem B1558431 : Blo 1557476 1558431 := bstep (se 1 (by rfl) ⟨1168823, by rfl⟩ : syracuseStep 1558431 = 2337647) B2337647
theorem B12634055 : Blo 1557476 12634055 := bstep (se 1 (by rfl) ⟨9475541, by rfl⟩ : syracuseStep 12634055 = 18951083) B18951083
theorem B3508217 : Blo 1557476 3508217 := bstep (se 2 (by rfl) ⟨1315581, by rfl⟩ : syracuseStep 3508217 = 2631163) B2631163
theorem B2336831 : Blo 1557476 2336831 := bstep (se 1 (by rfl) ⟨1752623, by rfl⟩ : syracuseStep 2336831 = 3505247) B3505247
theorem B1558599 : Blo 1557476 1558599 := bstep (se 1 (by rfl) ⟨1168949, by rfl⟩ : syracuseStep 1558599 = 2337899) B2337899
theorem B2336975 : Blo 1557476 2336975 := bstep (se 1 (by rfl) ⟨1752731, by rfl⟩ : syracuseStep 2336975 = 3505463) B3505463
theorem B1558759 : Blo 1557476 1558759 := bstep (se 1 (by rfl) ⟨1169069, by rfl⟩ : syracuseStep 1558759 = 2338139) B2338139
theorem B1558779 : Blo 1557476 1558779 := bstep (se 1 (by rfl) ⟨1169084, by rfl⟩ : syracuseStep 1558779 = 2338169) B2338169
theorem B1558783 : Blo 1557476 1558783 := bstep (se 1 (by rfl) ⟨1169087, by rfl⟩ : syracuseStep 1558783 = 2338175) B2338175
theorem B2959679 : Blo 1557476 2959679 := bstep (se 1 (by rfl) ⟨2219759, by rfl⟩ : syracuseStep 2959679 = 4439519) B4439519
theorem B2337095 : Blo 1557476 2337095 := bstep (se 1 (by rfl) ⟨1752821, by rfl⟩ : syracuseStep 2337095 = 3505643) B3505643
theorem B3508577 : Blo 1557476 3508577 := bstep (se 2 (by rfl) ⟨1315716, by rfl⟩ : syracuseStep 3508577 = 2631433) B2631433
theorem B15395179 : Blo 1557476 15395179 := bstep (se 1 (by rfl) ⟨11546384, by rfl⟩ : syracuseStep 15395179 = 23092769) B23092769
theorem B215959931 : Blo 1557476 215959931 := bstep (se 1 (by rfl) ⟨161969948, by rfl⟩ : syracuseStep 215959931 = 323939897) B323939897
theorem B1558939 : Blo 1557476 1558939 := bstep (se 1 (by rfl) ⟨1169204, by rfl⟩ : syracuseStep 1558939 = 2338409) B2338409
theorem B2337383 : Blo 1557476 2337383 := bstep (se 1 (by rfl) ⟨1753037, by rfl⟩ : syracuseStep 2337383 = 3506075) B3506075
theorem B1559199 : Blo 1557476 1559199 := bstep (se 1 (by rfl) ⟨1169399, by rfl⟩ : syracuseStep 1559199 = 2338799) B2338799
theorem B3328751 : Blo 1557476 3328751 := bstep (se 1 (by rfl) ⟨2496563, by rfl⟩ : syracuseStep 3328751 = 4993127) B4993127
theorem B1559279 : Blo 1557476 1559279 := bstep (se 1 (by rfl) ⟨1169459, by rfl⟩ : syracuseStep 1559279 = 2338919) B2338919
theorem B1559359 : Blo 1557476 1559359 := bstep (se 1 (by rfl) ⟨1169519, by rfl⟩ : syracuseStep 1559359 = 2339039) B2339039
theorem B2960219 : Blo 1557476 2960219 := bstep (se 1 (by rfl) ⟨2220164, by rfl⟩ : syracuseStep 2960219 = 4440329) B4440329
theorem B1559399 : Blo 1557476 1559399 := bstep (se 1 (by rfl) ⟨1169549, by rfl⟩ : syracuseStep 1559399 = 2339099) B2339099
theorem B11840417 : Blo 1557476 11840417 := bstep (se 2 (by rfl) ⟨4440156, by rfl⟩ : syracuseStep 11840417 = 8880313) B8880313
theorem B5262461 : Blo 1557476 5262461 := bstep (se 3 (by rfl) ⟨986711, by rfl⟩ : syracuseStep 5262461 = 1973423) B1973423
theorem B2337929 : Blo 1557476 2337929 := bstep (se 2 (by rfl) ⟨876723, by rfl⟩ : syracuseStep 2337929 = 1753447) B1753447
theorem B2960545 : Blo 1557476 2960545 := bstep (se 2 (by rfl) ⟨1110204, by rfl⟩ : syracuseStep 2960545 = 2220409) B2220409
theorem B2337983 : Blo 1557476 2337983 := bstep (se 1 (by rfl) ⟨1753487, by rfl⟩ : syracuseStep 2337983 = 3506975) B3506975
theorem B21327185 : Blo 1557476 21327185 := bstep (se 2 (by rfl) ⟨7997694, by rfl⟩ : syracuseStep 21327185 = 15995389) B15995389
theorem B18484645 : Blo 1557476 18484645 := bstep (se 4 (by rfl) ⟨1732935, by rfl⟩ : syracuseStep 18484645 = 3465871) B3465871
theorem B42643219 : Blo 1557476 42643219 := bstep (se 1 (by rfl) ⟨31982414, by rfl⟩ : syracuseStep 42643219 = 63964829) B63964829
theorem B431812421 : Blo 1557476 431812421 := bstep (se 4 (by rfl) ⟨40482414, by rfl⟩ : syracuseStep 431812421 = 80964829) B80964829
theorem B7884863 : Blo 1557476 7884863 := bstep (se 1 (by rfl) ⟨5913647, by rfl⟩ : syracuseStep 7884863 = 11827295) B11827295
theorem B2666665 : Blo 1557476 2666665 := bstep (se 2 (by rfl) ⟨999999, by rfl⟩ : syracuseStep 2666665 = 1999999) B1999999
theorem B48632183 : Blo 1557476 48632183 := bstep (se 1 (by rfl) ⟨36474137, by rfl⟩ : syracuseStep 48632183 = 72948275) B72948275
theorem B2847145 : Blo 1557476 2847145 := bstep (se 2 (by rfl) ⟨1067679, by rfl⟩ : syracuseStep 2847145 = 2135359) B2135359
theorem B14971655 : Blo 1557476 14971655 := bstep (se 1 (by rfl) ⟨11228741, by rfl⟩ : syracuseStep 14971655 = 22457483) B22457483
theorem B3945307 : Blo 1557476 3945307 := bstep (se 1 (by rfl) ⟨2958980, by rfl⟩ : syracuseStep 3945307 = 5917961) B5917961
theorem B8876897 : Blo 1557476 8876897 := bstep (se 2 (by rfl) ⟨3328836, by rfl⟩ : syracuseStep 8876897 = 6657673) B6657673
theorem B7590827 : Blo 1557476 7590827 := bstep (se 1 (by rfl) ⟨5693120, by rfl⟩ : syracuseStep 7590827 = 11386241) B11386241
theorem B8991661 : Blo 1557476 8991661 := bstep (se 3 (by rfl) ⟨1685936, by rfl⟩ : syracuseStep 8991661 = 3371873) B3371873
theorem B44913689 : Blo 1557476 44913689 := bstep (se 2 (by rfl) ⟨16842633, by rfl⟩ : syracuseStep 44913689 = 33685267) B33685267
theorem B4994075 : Blo 1557476 4994075 := bstep (se 1 (by rfl) ⟨3745556, by rfl⟩ : syracuseStep 4994075 = 7491113) B7491113
theorem B12809711 : Blo 1557476 12809711 := bstep (se 1 (by rfl) ⟨9607283, by rfl⟩ : syracuseStep 12809711 = 19214567) B19214567
theorem B13309535 : Blo 1557476 13309535 := bstep (se 1 (by rfl) ⟨9982151, by rfl⟩ : syracuseStep 13309535 = 19964303) B19964303
theorem B8877671 : Blo 1557476 8877671 := bstep (se 1 (by rfl) ⟨6658253, by rfl⟩ : syracuseStep 8877671 = 13316507) B13316507
theorem B5920361 : Blo 1557476 5920361 := bstep (se 2 (by rfl) ⟨2220135, by rfl⟩ : syracuseStep 5920361 = 4440271) B4440271
theorem B5920559 : Blo 1557476 5920559 := bstep (se 1 (by rfl) ⟨4440419, by rfl⟩ : syracuseStep 5920559 = 8880839) B8880839
theorem B3946603 : Blo 1557476 3946603 := bstep (se 1 (by rfl) ⟨2959952, by rfl⟩ : syracuseStep 3946603 = 5919905) B5919905
theorem B5920877 : Blo 1557476 5920877 := bstep (se 3 (by rfl) ⟨1110164, by rfl⟩ : syracuseStep 5920877 = 2220329) B2220329
theorem B7887455 : Blo 1557476 7887455 := bstep (se 1 (by rfl) ⟨5915591, by rfl⟩ : syracuseStep 7887455 = 11831183) B11831183
theorem B3504743 : Blo 1557476 3504743 := bstep (se 1 (by rfl) ⟨2628557, by rfl⟩ : syracuseStep 3504743 = 5257115) B5257115
theorem B5258141 : Blo 1557476 5258141 := bstep (se 3 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 5258141 = 1971803) B1971803
theorem B6659005 : Blo 1557476 6659005 := bstep (se 3 (by rfl) ⟨1248563, by rfl⟩ : syracuseStep 6659005 = 2497127) B2497127
theorem B4439087 : Blo 1557476 4439087 := bstep (se 1 (by rfl) ⟨3329315, by rfl⟩ : syracuseStep 4439087 = 6658631) B6658631
theorem B2628713 : Blo 1557476 2628713 := bstep (se 2 (by rfl) ⟨985767, by rfl⟩ : syracuseStep 2628713 = 1971535) B1971535
theorem B5913769 : Blo 1557476 5913769 := bstep (se 2 (by rfl) ⟨2217663, by rfl⟩ : syracuseStep 5913769 = 4435327) B4435327
theorem B5914241 : Blo 1557476 5914241 := bstep (se 2 (by rfl) ⟨2217840, by rfl⟩ : syracuseStep 5914241 = 4435681) B4435681
theorem B13319923 : Blo 1557476 13319923 := bstep (se 1 (by rfl) ⟨9989942, by rfl⟩ : syracuseStep 13319923 = 19979885) B19979885
theorem B3506003 : Blo 1557476 3506003 := bstep (se 1 (by rfl) ⟨2629502, by rfl⟩ : syracuseStep 3506003 = 5259005) B5259005
theorem B3506111 : Blo 1557476 3506111 := bstep (se 1 (by rfl) ⟨2629583, by rfl⟩ : syracuseStep 3506111 = 5259167) B5259167
theorem B6660083 : Blo 1557476 6660083 := bstep (se 1 (by rfl) ⟨4995062, by rfl⟩ : syracuseStep 6660083 = 9990125) B9990125
theorem B1753159 : Blo 1557476 1753159 := bstep (se 1 (by rfl) ⟨1314869, by rfl⟩ : syracuseStep 1753159 = 2629739) B2629739
theorem B5915227 : Blo 1557476 5915227 := bstep (se 1 (by rfl) ⟨4436420, by rfl⟩ : syracuseStep 5915227 = 8872841) B8872841
theorem B29942459 : Blo 1557476 29942459 := bstep (se 1 (by rfl) ⟨22456844, by rfl⟩ : syracuseStep 29942459 = 44913689) B44913689
theorem B14222213 : Blo 1557476 14222213 := bstep (se 4 (by rfl) ⟨1333332, by rfl⟩ : syracuseStep 14222213 = 2666665) B2666665
theorem B1557487 : Blo 1557476 1557487 := bstep (se 1 (by rfl) ⟨1168115, by rfl⟩ : syracuseStep 1557487 = 2336231) B2336231
theorem B8873023 : Blo 1557476 8873023 := bstep (se 1 (by rfl) ⟨6654767, by rfl⟩ : syracuseStep 8873023 = 13309535) B13309535
theorem B1557575 : Blo 1557476 1557575 := bstep (se 1 (by rfl) ⟨1168181, by rfl⟩ : syracuseStep 1557575 = 2336363) B2336363
theorem B21316679 : Blo 1557476 21316679 := bstep (se 1 (by rfl) ⟨15987509, by rfl⟩ : syracuseStep 21316679 = 31975019) B31975019
theorem B1557607 : Blo 1557476 1557607 := bstep (se 1 (by rfl) ⟨1168205, by rfl⟩ : syracuseStep 1557607 = 2336411) B2336411
theorem B5260409 : Blo 1557476 5260409 := bstep (se 2 (by rfl) ⟨1972653, by rfl⟩ : syracuseStep 5260409 = 3945307) B3945307
theorem B8422703 : Blo 1557476 8422703 := bstep (se 1 (by rfl) ⟨6317027, by rfl⟩ : syracuseStep 8422703 = 12634055) B12634055
theorem B1557887 : Blo 1557476 1557887 := bstep (se 1 (by rfl) ⟨1168415, by rfl⟩ : syracuseStep 1557887 = 2336831) B2336831
theorem B1557983 : Blo 1557476 1557983 := bstep (se 1 (by rfl) ⟨1168487, by rfl⟩ : syracuseStep 1557983 = 2336975) B2336975
theorem B1558063 : Blo 1557476 1558063 := bstep (se 1 (by rfl) ⟨1168547, by rfl⟩ : syracuseStep 1558063 = 2337095) B2337095
theorem B2336495 : Blo 1557476 2336495 := bstep (se 1 (by rfl) ⟨1752371, by rfl⟩ : syracuseStep 2336495 = 3504743) B3504743
theorem B1558255 : Blo 1557476 1558255 := bstep (se 1 (by rfl) ⟨1168691, by rfl⟩ : syracuseStep 1558255 = 2337383) B2337383
theorem B2959391 : Blo 1557476 2959391 := bstep (se 1 (by rfl) ⟨2219543, by rfl⟩ : syracuseStep 2959391 = 4439087) B4439087
theorem B3508307 : Blo 1557476 3508307 := bstep (se 1 (by rfl) ⟨2631230, by rfl⟩ : syracuseStep 3508307 = 5262461) B5262461
theorem B1558619 : Blo 1557476 1558619 := bstep (se 1 (by rfl) ⟨1168964, by rfl⟩ : syracuseStep 1558619 = 2337929) B2337929
theorem B1558655 : Blo 1557476 1558655 := bstep (se 1 (by rfl) ⟨1168991, by rfl⟩ : syracuseStep 1558655 = 2337983) B2337983
theorem B3942827 : Blo 1557476 3942827 := bstep (se 1 (by rfl) ⟨2957120, by rfl⟩ : syracuseStep 3942827 = 5914241) B5914241
theorem B2337335 : Blo 1557476 2337335 := bstep (se 1 (by rfl) ⟨1753001, by rfl⟩ : syracuseStep 2337335 = 3506003) B3506003
theorem B2337407 : Blo 1557476 2337407 := bstep (se 1 (by rfl) ⟨1753055, by rfl⟩ : syracuseStep 2337407 = 3506111) B3506111
theorem B5262137 : Blo 1557476 5262137 := bstep (se 2 (by rfl) ⟨1973301, by rfl⟩ : syracuseStep 5262137 = 3946603) B3946603
theorem B9981103 : Blo 1557476 9981103 := bstep (se 1 (by rfl) ⟨7485827, by rfl⟩ : syracuseStep 9981103 = 14971655) B14971655
theorem B3796193 : Blo 1557476 3796193 := bstep (se 2 (by rfl) ⟨1423572, by rfl⟩ : syracuseStep 3796193 = 2847145) B2847145
theorem B5917931 : Blo 1557476 5917931 := bstep (se 1 (by rfl) ⟨4438448, by rfl⟩ : syracuseStep 5917931 = 8876897) B8876897
theorem B8219999 : Blo 1557476 8219999 := bstep (se 1 (by rfl) ⟨6164999, by rfl⟩ : syracuseStep 8219999 = 12329999) B12329999
theorem B7892477 : Blo 1557476 7892477 := bstep (se 3 (by rfl) ⟨1479839, by rfl⟩ : syracuseStep 7892477 = 2959679) B2959679
theorem B7892639 : Blo 1557476 7892639 := bstep (se 1 (by rfl) ⟨5919479, by rfl⟩ : syracuseStep 7892639 = 11838959) B11838959
theorem B5918447 : Blo 1557476 5918447 := bstep (se 1 (by rfl) ⟨4438835, by rfl⟩ : syracuseStep 5918447 = 8877671) B8877671
theorem B11988881 : Blo 1557476 11988881 := bstep (se 2 (by rfl) ⟨4495830, by rfl⟩ : syracuseStep 11988881 = 8991661) B8991661
theorem B2338811 : Blo 1557476 2338811 := bstep (se 1 (by rfl) ⟨1754108, by rfl⟩ : syracuseStep 2338811 = 3508217) B3508217
theorem B7885025 : Blo 1557476 7885025 := bstep (se 2 (by rfl) ⟨2956884, by rfl⟩ : syracuseStep 7885025 = 5913769) B5913769
theorem B2339051 : Blo 1557476 2339051 := bstep (se 1 (by rfl) ⟨1754288, by rfl⟩ : syracuseStep 2339051 = 3508577) B3508577
theorem B24646193 : Blo 1557476 24646193 := bstep (se 2 (by rfl) ⟨9242322, by rfl⟩ : syracuseStep 24646193 = 18484645) B18484645
theorem B7893611 : Blo 1557476 7893611 := bstep (se 1 (by rfl) ⟨5920208, by rfl⟩ : syracuseStep 7893611 = 11840417) B11840417
theorem B14218123 : Blo 1557476 14218123 := bstep (se 1 (by rfl) ⟨10663592, by rfl⟩ : syracuseStep 14218123 = 21327185) B21327185
theorem B56857625 : Blo 1557476 56857625 := bstep (se 2 (by rfl) ⟨21321609, by rfl⟩ : syracuseStep 56857625 = 42643219) B42643219
theorem B5256575 : Blo 1557476 5256575 := bstep (se 1 (by rfl) ⟨3942431, by rfl⟩ : syracuseStep 5256575 = 7884863) B7884863
theorem B13317533 : Blo 1557476 13317533 := bstep (se 3 (by rfl) ⟨2497037, by rfl⟩ : syracuseStep 13317533 = 4994075) B4994075
theorem B32421455 : Blo 1557476 32421455 := bstep (se 1 (by rfl) ⟨24316091, by rfl⟩ : syracuseStep 32421455 = 48632183) B48632183
theorem B20526905 : Blo 1557476 20526905 := bstep (se 2 (by rfl) ⟨7697589, by rfl⟩ : syracuseStep 20526905 = 15395179) B15395179
theorem B5920573 : Blo 1557476 5920573 := bstep (se 3 (by rfl) ⟨1110107, by rfl⟩ : syracuseStep 5920573 = 2220215) B2220215
theorem B64018343 : Blo 1557476 64018343 := bstep (se 1 (by rfl) ⟨48013757, by rfl⟩ : syracuseStep 64018343 = 96027515) B96027515
theorem B5060551 : Blo 1557476 5060551 := bstep (se 1 (by rfl) ⟨3795413, by rfl⟩ : syracuseStep 5060551 = 7590827) B7590827
theorem B1972279 : Blo 1557476 1972279 := bstep (se 1 (by rfl) ⟨1479209, by rfl⟩ : syracuseStep 1972279 = 2958419) B2958419
theorem B1972507 : Blo 1557476 1972507 := bstep (se 1 (by rfl) ⟨1479380, by rfl⟩ : syracuseStep 1972507 = 2958761) B2958761
theorem B3946907 : Blo 1557476 3946907 := bstep (se 1 (by rfl) ⟨2960180, by rfl⟩ : syracuseStep 3946907 = 5920361) B5920361
theorem B3947039 : Blo 1557476 3947039 := bstep (se 1 (by rfl) ⟨2960279, by rfl⟩ : syracuseStep 3947039 = 5920559) B5920559
theorem B2808361 : Blo 1557476 2808361 := bstep (se 2 (by rfl) ⟨1053135, by rfl⟩ : syracuseStep 2808361 = 2106271) B2106271
theorem B8878673 : Blo 1557476 8878673 := bstep (se 2 (by rfl) ⟨3329502, by rfl⟩ : syracuseStep 8878673 = 6659005) B6659005
theorem B34159229 : Blo 1557476 34159229 := bstep (se 3 (by rfl) ⟨6404855, by rfl⟩ : syracuseStep 34159229 = 12809711) B12809711
theorem B3947251 : Blo 1557476 3947251 := bstep (se 1 (by rfl) ⟨2960438, by rfl⟩ : syracuseStep 3947251 = 5920877) B5920877
theorem B3947393 : Blo 1557476 3947393 := bstep (se 2 (by rfl) ⟨1480272, by rfl⟩ : syracuseStep 3947393 = 2960545) B2960545
theorem B143973287 : Blo 1557476 143973287 := bstep (se 1 (by rfl) ⟨107979965, by rfl⟩ : syracuseStep 143973287 = 215959931) B215959931
theorem B5258303 : Blo 1557476 5258303 := bstep (se 1 (by rfl) ⟨3943727, by rfl⟩ : syracuseStep 5258303 = 7887455) B7887455
theorem B2219167 : Blo 1557476 2219167 := bstep (se 1 (by rfl) ⟨1664375, by rfl⟩ : syracuseStep 2219167 = 3328751) B3328751
theorem B1973479 : Blo 1557476 1973479 := bstep (se 1 (by rfl) ⟨1480109, by rfl⟩ : syracuseStep 1973479 = 2960219) B2960219
theorem B3505427 : Blo 1557476 3505427 := bstep (se 1 (by rfl) ⟨2629070, by rfl⟩ : syracuseStep 3505427 = 5258141) B5258141
theorem B1752475 : Blo 1557476 1752475 := bstep (se 1 (by rfl) ⟨1314356, by rfl⟩ : syracuseStep 1752475 = 2628713) B2628713
theorem B4440055 : Blo 1557476 4440055 := bstep (se 1 (by rfl) ⟨3330041, by rfl⟩ : syracuseStep 4440055 = 6660083) B6660083
theorem B17759897 : Blo 1557476 17759897 := bstep (se 2 (by rfl) ⟨6659961, by rfl⟩ : syracuseStep 17759897 = 13319923) B13319923
theorem B287874947 : Blo 1557476 287874947 := bstep (se 1 (by rfl) ⟨215906210, by rfl⟩ : syracuseStep 287874947 = 431812421) B431812421
theorem B2629705 : Blo 1557476 2629705 := bstep (se 2 (by rfl) ⟨986139, by rfl⟩ : syracuseStep 2629705 = 1972279) B1972279
theorem B2630009 : Blo 1557476 2630009 := bstep (se 2 (by rfl) ⟨986253, by rfl⟩ : syracuseStep 2630009 = 1972507) B1972507
theorem B37905083 : Blo 1557476 37905083 := bstep (se 1 (by rfl) ⟨28428812, by rfl⟩ : syracuseStep 37905083 = 56857625) B56857625
theorem B3744481 : Blo 1557476 3744481 := bstep (se 2 (by rfl) ⟨1404180, by rfl⟩ : syracuseStep 3744481 = 2808361) B2808361
theorem B3506939 : Blo 1557476 3506939 := bstep (se 1 (by rfl) ⟨2630204, by rfl⟩ : syracuseStep 3506939 = 5260409) B5260409
theorem B1557663 : Blo 1557476 1557663 := bstep (se 1 (by rfl) ⟨1168247, by rfl⟩ : syracuseStep 1557663 = 2336495) B2336495
theorem B18957497 : Blo 1557476 18957497 := bstep (se 2 (by rfl) ⟨7109061, by rfl⟩ : syracuseStep 18957497 = 14218123) B14218123
theorem B11830697 : Blo 1557476 11830697 := bstep (se 2 (by rfl) ⟨4436511, by rfl⟩ : syracuseStep 11830697 = 8873023) B8873023
theorem B2631271 : Blo 1557476 2631271 := bstep (se 1 (by rfl) ⟨1973453, by rfl⟩ : syracuseStep 2631271 = 3946907) B3946907
theorem B2631305 : Blo 1557476 2631305 := bstep (se 2 (by rfl) ⟨986739, by rfl⟩ : syracuseStep 2631305 = 1973479) B1973479
theorem B2631359 : Blo 1557476 2631359 := bstep (se 1 (by rfl) ⟨1973519, by rfl⟩ : syracuseStep 2631359 = 3947039) B3947039
theorem B1558223 : Blo 1557476 1558223 := bstep (se 1 (by rfl) ⟨1168667, by rfl⟩ : syracuseStep 1558223 = 2337335) B2337335
theorem B1558271 : Blo 1557476 1558271 := bstep (se 1 (by rfl) ⟨1168703, by rfl⟩ : syracuseStep 1558271 = 2337407) B2337407
theorem B2336633 : Blo 1557476 2336633 := bstep (se 2 (by rfl) ⟨876237, by rfl⟩ : syracuseStep 2336633 = 1752475) B1752475
theorem B3508091 : Blo 1557476 3508091 := bstep (se 1 (by rfl) ⟨2631068, by rfl⟩ : syracuseStep 3508091 = 5262137) B5262137
theorem B2631595 : Blo 1557476 2631595 := bstep (se 1 (by rfl) ⟨1973696, by rfl⟩ : syracuseStep 2631595 = 3947393) B3947393
theorem B2336951 : Blo 1557476 2336951 := bstep (se 1 (by rfl) ⟨1752713, by rfl⟩ : syracuseStep 2336951 = 3505427) B3505427
theorem B5261651 : Blo 1557476 5261651 := bstep (se 1 (by rfl) ⟨3946238, by rfl⟩ : syracuseStep 5261651 = 7892477) B7892477
theorem B11839931 : Blo 1557476 11839931 := bstep (se 1 (by rfl) ⟨8879948, by rfl⟩ : syracuseStep 11839931 = 17759897) B17759897
theorem B5261759 : Blo 1557476 5261759 := bstep (se 1 (by rfl) ⟨3946319, by rfl⟩ : syracuseStep 5261759 = 7892639) B7892639
theorem B191916631 : Blo 1557476 191916631 := bstep (se 1 (by rfl) ⟨143937473, by rfl⟩ : syracuseStep 191916631 = 287874947) B287874947
theorem B1559207 : Blo 1557476 1559207 := bstep (se 1 (by rfl) ⟨1169405, by rfl⟩ : syracuseStep 1559207 = 2338811) B2338811
theorem B2337545 : Blo 1557476 2337545 := bstep (se 2 (by rfl) ⟨876579, by rfl⟩ : syracuseStep 2337545 = 1753159) B1753159
theorem B1559367 : Blo 1557476 1559367 := bstep (se 1 (by rfl) ⟨1169525, by rfl⟩ : syracuseStep 1559367 = 2339051) B2339051
theorem B5262407 : Blo 1557476 5262407 := bstep (se 1 (by rfl) ⟨3946805, by rfl⟩ : syracuseStep 5262407 = 7893611) B7893611
theorem B9481475 : Blo 1557476 9481475 := bstep (se 1 (by rfl) ⟨7111106, by rfl⟩ : syracuseStep 9481475 = 14222213) B14222213
theorem B5615135 : Blo 1557476 5615135 := bstep (se 1 (by rfl) ⟨4211351, by rfl⟩ : syracuseStep 5615135 = 8422703) B8422703
theorem B5263001 : Blo 1557476 5263001 := bstep (se 2 (by rfl) ⟨1973625, by rfl⟩ : syracuseStep 5263001 = 3947251) B3947251
theorem B21614303 : Blo 1557476 21614303 := bstep (se 1 (by rfl) ⟨16210727, by rfl⟩ : syracuseStep 21614303 = 32421455) B32421455
theorem B2338871 : Blo 1557476 2338871 := bstep (se 1 (by rfl) ⟨1754153, by rfl⟩ : syracuseStep 2338871 = 3508307) B3508307
theorem B13308137 : Blo 1557476 13308137 := bstep (se 2 (by rfl) ⟨4990551, by rfl⟩ : syracuseStep 13308137 = 9981103) B9981103
theorem B5919115 : Blo 1557476 5919115 := bstep (se 1 (by rfl) ⟨4439336, by rfl⟩ : syracuseStep 5919115 = 8878673) B8878673
theorem B95982191 : Blo 1557476 95982191 := bstep (se 1 (by rfl) ⟨71986643, by rfl⟩ : syracuseStep 95982191 = 143973287) B143973287
theorem B3945287 : Blo 1557476 3945287 := bstep (se 1 (by rfl) ⟨2958965, by rfl⟩ : syracuseStep 3945287 = 5917931) B5917931
theorem B7894097 : Blo 1557476 7894097 := bstep (se 2 (by rfl) ⟨2960286, by rfl⟩ : syracuseStep 7894097 = 5920573) B5920573
theorem B3945631 : Blo 1557476 3945631 := bstep (se 1 (by rfl) ⟨2959223, by rfl⟩ : syracuseStep 3945631 = 5918447) B5918447
theorem B6747401 : Blo 1557476 6747401 := bstep (se 2 (by rfl) ⟨2530275, by rfl⟩ : syracuseStep 6747401 = 5060551) B5060551
theorem B7992587 : Blo 1557476 7992587 := bstep (se 1 (by rfl) ⟨5994440, by rfl⟩ : syracuseStep 7992587 = 11988881) B11988881
theorem B5920073 : Blo 1557476 5920073 := bstep (se 2 (by rfl) ⟨2220027, by rfl⟩ : syracuseStep 5920073 = 4440055) B4440055
theorem B5256683 : Blo 1557476 5256683 := bstep (se 1 (by rfl) ⟨3942512, by rfl⟩ : syracuseStep 5256683 = 7885025) B7885025
theorem B16430795 : Blo 1557476 16430795 := bstep (se 1 (by rfl) ⟨12323096, by rfl⟩ : syracuseStep 16430795 = 24646193) B24646193
theorem B19961639 : Blo 1557476 19961639 := bstep (se 1 (by rfl) ⟨14971229, by rfl⟩ : syracuseStep 19961639 = 29942459) B29942459
theorem B14211119 : Blo 1557476 14211119 := bstep (se 1 (by rfl) ⟨10658339, by rfl⟩ : syracuseStep 14211119 = 21316679) B21316679
theorem B7886969 : Blo 1557476 7886969 := bstep (se 2 (by rfl) ⟨2957613, by rfl⟩ : syracuseStep 7886969 = 5915227) B5915227
theorem B11835557 : Blo 1557476 11835557 := bstep (se 4 (by rfl) ⟨1109583, by rfl⟩ : syracuseStep 11835557 = 2219167) B2219167
theorem B21919997 : Blo 1557476 21919997 := bstep (se 3 (by rfl) ⟨4109999, by rfl⟩ : syracuseStep 21919997 = 8219999) B8219999
theorem B3504383 : Blo 1557476 3504383 := bstep (se 1 (by rfl) ⟨2628287, by rfl⟩ : syracuseStep 3504383 = 5256575) B5256575
theorem B8878355 : Blo 1557476 8878355 := bstep (se 1 (by rfl) ⟨6658766, by rfl⟩ : syracuseStep 8878355 = 13317533) B13317533
theorem B42678895 : Blo 1557476 42678895 := bstep (se 1 (by rfl) ⟨32009171, by rfl⟩ : syracuseStep 42678895 = 64018343) B64018343
theorem B1972927 : Blo 1557476 1972927 := bstep (se 1 (by rfl) ⟨1479695, by rfl⟩ : syracuseStep 1972927 = 2959391) B2959391
theorem B2628551 : Blo 1557476 2628551 := bstep (se 1 (by rfl) ⟨1971413, by rfl⟩ : syracuseStep 2628551 = 3942827) B3942827
theorem B22772819 : Blo 1557476 22772819 := bstep (se 1 (by rfl) ⟨17079614, by rfl⟩ : syracuseStep 22772819 = 34159229) B34159229
theorem B3505535 : Blo 1557476 3505535 := bstep (se 1 (by rfl) ⟨2629151, by rfl⟩ : syracuseStep 3505535 = 5258303) B5258303
theorem B2530795 : Blo 1557476 2530795 := bstep (se 1 (by rfl) ⟨1898096, by rfl⟩ : syracuseStep 2530795 = 3796193) B3796193
theorem B54738413 : Blo 1557476 54738413 := bstep (se 3 (by rfl) ⟨10263452, by rfl⟩ : syracuseStep 54738413 = 20526905) B20526905
theorem B3506273 : Blo 1557476 3506273 := bstep (se 2 (by rfl) ⟨1314852, by rfl⟩ : syracuseStep 3506273 = 2629705) B2629705
theorem B8872091 : Blo 1557476 8872091 := bstep (se 1 (by rfl) ⟨6654068, by rfl⟩ : syracuseStep 8872091 = 13308137) B13308137
theorem B1753339 : Blo 1557476 1753339 := bstep (se 1 (by rfl) ⟨1315004, by rfl⟩ : syracuseStep 1753339 = 2630009) B2630009
theorem B63988127 : Blo 1557476 63988127 := bstep (se 1 (by rfl) ⟨47991095, by rfl⟩ : syracuseStep 63988127 = 95982191) B95982191
theorem B50553325 : Blo 1557476 50553325 := bstep (se 3 (by rfl) ⟨9478748, by rfl⟩ : syracuseStep 50553325 = 18957497) B18957497
theorem B2630191 : Blo 1557476 2630191 := bstep (se 1 (by rfl) ⟨1972643, by rfl⟩ : syracuseStep 2630191 = 3945287) B3945287
theorem B4498267 : Blo 1557476 4498267 := bstep (se 1 (by rfl) ⟨3373700, by rfl⟩ : syracuseStep 4498267 = 6747401) B6747401
theorem B2630569 : Blo 1557476 2630569 := bstep (se 2 (by rfl) ⟨986463, by rfl⟩ : syracuseStep 2630569 = 1972927) B1972927
theorem B1754203 : Blo 1557476 1754203 := bstep (se 1 (by rfl) ⟨1315652, by rfl⟩ : syracuseStep 1754203 = 2631305) B2631305
theorem B1754239 : Blo 1557476 1754239 := bstep (se 1 (by rfl) ⟨1315679, by rfl⟩ : syracuseStep 1754239 = 2631359) B2631359
theorem B10953863 : Blo 1557476 10953863 := bstep (se 1 (by rfl) ⟨8215397, by rfl⟩ : syracuseStep 10953863 = 16430795) B16430795
theorem B1557755 : Blo 1557476 1557755 := bstep (se 1 (by rfl) ⟨1168316, by rfl⟩ : syracuseStep 1557755 = 2336633) B2336633
theorem B7890371 : Blo 1557476 7890371 := bstep (se 1 (by rfl) ⟨5917778, by rfl⟩ : syracuseStep 7890371 = 11835557) B11835557
theorem B1557967 : Blo 1557476 1557967 := bstep (se 1 (by rfl) ⟨1168475, by rfl⟩ : syracuseStep 1557967 = 2336951) B2336951
theorem B2336255 : Blo 1557476 2336255 := bstep (se 1 (by rfl) ⟨1752191, by rfl⟩ : syracuseStep 2336255 = 3504383) B3504383
theorem B5260841 : Blo 1557476 5260841 := bstep (se 2 (by rfl) ⟨1972815, by rfl⟩ : syracuseStep 5260841 = 3945631) B3945631
theorem B3507767 : Blo 1557476 3507767 := bstep (se 1 (by rfl) ⟨2630825, by rfl⟩ : syracuseStep 3507767 = 5261651) B5261651
theorem B3507839 : Blo 1557476 3507839 := bstep (se 1 (by rfl) ⟨2630879, by rfl⟩ : syracuseStep 3507839 = 5261759) B5261759
theorem B1558363 : Blo 1557476 1558363 := bstep (se 1 (by rfl) ⟨1168772, by rfl⟩ : syracuseStep 1558363 = 2337545) B2337545
theorem B3508271 : Blo 1557476 3508271 := bstep (se 1 (by rfl) ⟨2631203, by rfl⟩ : syracuseStep 3508271 = 5262407) B5262407
theorem B15181879 : Blo 1557476 15181879 := bstep (se 1 (by rfl) ⟨11386409, by rfl⟩ : syracuseStep 15181879 = 22772819) B22772819
theorem B3508361 : Blo 1557476 3508361 := bstep (se 2 (by rfl) ⟨1315635, by rfl⟩ : syracuseStep 3508361 = 2631271) B2631271
theorem B2337023 : Blo 1557476 2337023 := bstep (se 1 (by rfl) ⟨1752767, by rfl⟩ : syracuseStep 2337023 = 3505535) B3505535
theorem B3508667 : Blo 1557476 3508667 := bstep (se 1 (by rfl) ⟨2631500, by rfl⟩ : syracuseStep 3508667 = 5263001) B5263001
theorem B3508793 : Blo 1557476 3508793 := bstep (se 2 (by rfl) ⟨1315797, by rfl⟩ : syracuseStep 3508793 = 2631595) B2631595
theorem B1559247 : Blo 1557476 1559247 := bstep (se 1 (by rfl) ⟨1169435, by rfl⟩ : syracuseStep 1559247 = 2338871) B2338871
theorem B2337959 : Blo 1557476 2337959 := bstep (se 1 (by rfl) ⟨1753469, by rfl⟩ : syracuseStep 2337959 = 3506939) B3506939
theorem B7892153 : Blo 1557476 7892153 := bstep (se 2 (by rfl) ⟨2959557, by rfl⟩ : syracuseStep 7892153 = 5919115) B5919115
theorem B58453325 : Blo 1557476 58453325 := bstep (se 3 (by rfl) ⟨10959998, by rfl⟩ : syracuseStep 58453325 = 21919997) B21919997
theorem B5262731 : Blo 1557476 5262731 := bstep (se 1 (by rfl) ⟨3947048, by rfl⟩ : syracuseStep 5262731 = 7894097) B7894097
theorem B255888841 : Blo 1557476 255888841 := bstep (se 2 (by rfl) ⟨95958315, by rfl⟩ : syracuseStep 255888841 = 191916631) B191916631
theorem B56905193 : Blo 1557476 56905193 := bstep (se 2 (by rfl) ⟨21339447, by rfl⟩ : syracuseStep 56905193 = 42678895) B42678895
theorem B5328391 : Blo 1557476 5328391 := bstep (se 1 (by rfl) ⟨3996293, by rfl⟩ : syracuseStep 5328391 = 7992587) B7992587
theorem B4992641 : Blo 1557476 4992641 := bstep (se 2 (by rfl) ⟨1872240, by rfl⟩ : syracuseStep 4992641 = 3744481) B3744481
theorem B13307759 : Blo 1557476 13307759 := bstep (se 1 (by rfl) ⟨9980819, by rfl⟩ : syracuseStep 13307759 = 19961639) B19961639
theorem B2338727 : Blo 1557476 2338727 := bstep (se 1 (by rfl) ⟨1754045, by rfl⟩ : syracuseStep 2338727 = 3508091) B3508091
theorem B9474079 : Blo 1557476 9474079 := bstep (se 1 (by rfl) ⟨7105559, by rfl⟩ : syracuseStep 9474079 = 14211119) B14211119
theorem B5918903 : Blo 1557476 5918903 := bstep (se 1 (by rfl) ⟨4439177, by rfl⟩ : syracuseStep 5918903 = 8878355) B8878355
theorem B7893287 : Blo 1557476 7893287 := bstep (se 1 (by rfl) ⟨5919965, by rfl⟩ : syracuseStep 7893287 = 11839931) B11839931
theorem B6320983 : Blo 1557476 6320983 := bstep (se 1 (by rfl) ⟨4740737, by rfl⟩ : syracuseStep 6320983 = 9481475) B9481475
theorem B36492275 : Blo 1557476 36492275 := bstep (se 1 (by rfl) ⟨27369206, by rfl⟩ : syracuseStep 36492275 = 54738413) B54738413
theorem B25270055 : Blo 1557476 25270055 := bstep (se 1 (by rfl) ⟨18952541, by rfl⟩ : syracuseStep 25270055 = 37905083) B37905083
theorem B3946715 : Blo 1557476 3946715 := bstep (se 1 (by rfl) ⟨2960036, by rfl⟩ : syracuseStep 3946715 = 5920073) B5920073
theorem B7887131 : Blo 1557476 7887131 := bstep (se 1 (by rfl) ⟨5915348, by rfl⟩ : syracuseStep 7887131 = 11830697) B11830697
theorem B3504455 : Blo 1557476 3504455 := bstep (se 1 (by rfl) ⟨2628341, by rfl⟩ : syracuseStep 3504455 = 5256683) B5256683
theorem B5257979 : Blo 1557476 5257979 := bstep (se 1 (by rfl) ⟨3943484, by rfl⟩ : syracuseStep 5257979 = 7886969) B7886969
theorem B1752367 : Blo 1557476 1752367 := bstep (se 1 (by rfl) ⟨1314275, by rfl⟩ : syracuseStep 1752367 = 2628551) B2628551
theorem B3374393 : Blo 1557476 3374393 := bstep (se 2 (by rfl) ⟨1265397, by rfl⟩ : syracuseStep 3374393 = 2530795) B2530795
theorem B3743423 : Blo 1557476 3743423 := bstep (se 1 (by rfl) ⟨2807567, by rfl⟩ : syracuseStep 3743423 = 5615135) B5615135
theorem B14409535 : Blo 1557476 14409535 := bstep (se 1 (by rfl) ⟨10807151, by rfl⟩ : syracuseStep 14409535 = 21614303) B21614303
theorem B12632105 : Blo 1557476 12632105 := bstep (se 2 (by rfl) ⟨4737039, by rfl⟩ : syracuseStep 12632105 = 9474079) B9474079
theorem B20242505 : Blo 1557476 20242505 := bstep (se 2 (by rfl) ⟨7590939, by rfl⟩ : syracuseStep 20242505 = 15181879) B15181879
theorem B5914727 : Blo 1557476 5914727 := bstep (se 1 (by rfl) ⟨4436045, by rfl⟩ : syracuseStep 5914727 = 8872091) B8872091
theorem B67404433 : Blo 1557476 67404433 := bstep (se 2 (by rfl) ⟨25276662, by rfl⟩ : syracuseStep 67404433 = 50553325) B50553325
theorem B3506921 : Blo 1557476 3506921 := bstep (se 2 (by rfl) ⟨1315095, by rfl⟩ : syracuseStep 3506921 = 2630191) B2630191
theorem B5260247 : Blo 1557476 5260247 := bstep (se 1 (by rfl) ⟨3945185, by rfl⟩ : syracuseStep 5260247 = 7890371) B7890371
theorem B1557503 : Blo 1557476 1557503 := bstep (se 1 (by rfl) ⟨1168127, by rfl⟩ : syracuseStep 1557503 = 2336255) B2336255
theorem B3507227 : Blo 1557476 3507227 := bstep (se 1 (by rfl) ⟨2630420, by rfl⟩ : syracuseStep 3507227 = 5260841) B5260841
theorem B5997689 : Blo 1557476 5997689 := bstep (se 2 (by rfl) ⟨2249133, by rfl⟩ : syracuseStep 5997689 = 4498267) B4498267
theorem B3507425 : Blo 1557476 3507425 := bstep (se 2 (by rfl) ⟨1315284, by rfl⟩ : syracuseStep 3507425 = 2630569) B2630569
theorem B2631143 : Blo 1557476 2631143 := bstep (se 1 (by rfl) ⟨1973357, by rfl⟩ : syracuseStep 2631143 = 3946715) B3946715
theorem B1558015 : Blo 1557476 1558015 := bstep (se 1 (by rfl) ⟨1168511, by rfl⟩ : syracuseStep 1558015 = 2337023) B2337023
theorem B2336303 : Blo 1557476 2336303 := bstep (se 1 (by rfl) ⟨1752227, by rfl⟩ : syracuseStep 2336303 = 3504455) B3504455
theorem B2336489 : Blo 1557476 2336489 := bstep (se 2 (by rfl) ⟨876183, by rfl⟩ : syracuseStep 2336489 = 1752367) B1752367
theorem B7104521 : Blo 1557476 7104521 := bstep (se 2 (by rfl) ⟨2664195, by rfl⟩ : syracuseStep 7104521 = 5328391) B5328391
theorem B1558639 : Blo 1557476 1558639 := bstep (se 1 (by rfl) ⟨1168979, by rfl⟩ : syracuseStep 1558639 = 2337959) B2337959
theorem B5261435 : Blo 1557476 5261435 := bstep (se 1 (by rfl) ⟨3946076, by rfl⟩ : syracuseStep 5261435 = 7892153) B7892153
theorem B3508487 : Blo 1557476 3508487 := bstep (se 1 (by rfl) ⟨2631365, by rfl⟩ : syracuseStep 3508487 = 5262731) B5262731
theorem B19212713 : Blo 1557476 19212713 := bstep (se 2 (by rfl) ⟨7204767, by rfl⟩ : syracuseStep 19212713 = 14409535) B14409535
theorem B3328427 : Blo 1557476 3328427 := bstep (se 1 (by rfl) ⟨2496320, by rfl⟩ : syracuseStep 3328427 = 4992641) B4992641
theorem B1559151 : Blo 1557476 1559151 := bstep (se 1 (by rfl) ⟨1169363, by rfl⟩ : syracuseStep 1559151 = 2338727) B2338727
theorem B2337515 : Blo 1557476 2337515 := bstep (se 1 (by rfl) ⟨1753136, by rfl⟩ : syracuseStep 2337515 = 3506273) B3506273
theorem B5262191 : Blo 1557476 5262191 := bstep (se 1 (by rfl) ⟨3946643, by rfl⟩ : syracuseStep 5262191 = 7893287) B7893287
theorem B42658751 : Blo 1557476 42658751 := bstep (se 1 (by rfl) ⟨31994063, by rfl⟩ : syracuseStep 42658751 = 63988127) B63988127
theorem B2337785 : Blo 1557476 2337785 := bstep (se 2 (by rfl) ⟨876669, by rfl⟩ : syracuseStep 2337785 = 1753339) B1753339
theorem B7302575 : Blo 1557476 7302575 := bstep (se 1 (by rfl) ⟨5476931, by rfl⟩ : syracuseStep 7302575 = 10953863) B10953863
theorem B8998381 : Blo 1557476 8998381 := bstep (se 3 (by rfl) ⟨1687196, by rfl⟩ : syracuseStep 8998381 = 3374393) B3374393
theorem B2338511 : Blo 1557476 2338511 := bstep (se 1 (by rfl) ⟨1753883, by rfl⟩ : syracuseStep 2338511 = 3507767) B3507767
theorem B2338559 : Blo 1557476 2338559 := bstep (se 1 (by rfl) ⟨1753919, by rfl⟩ : syracuseStep 2338559 = 3507839) B3507839
theorem B16846703 : Blo 1557476 16846703 := bstep (se 1 (by rfl) ⟨12635027, by rfl⟩ : syracuseStep 16846703 = 25270055) B25270055
theorem B2338847 : Blo 1557476 2338847 := bstep (se 1 (by rfl) ⟨1754135, by rfl⟩ : syracuseStep 2338847 = 3508271) B3508271
theorem B2338907 : Blo 1557476 2338907 := bstep (se 1 (by rfl) ⟨1754180, by rfl⟩ : syracuseStep 2338907 = 3508361) B3508361
theorem B2338937 : Blo 1557476 2338937 := bstep (se 2 (by rfl) ⟨877101, by rfl⟩ : syracuseStep 2338937 = 1754203) B1754203
theorem B2338985 : Blo 1557476 2338985 := bstep (se 2 (by rfl) ⟨877119, by rfl⟩ : syracuseStep 2338985 = 1754239) B1754239
theorem B2339111 : Blo 1557476 2339111 := bstep (se 1 (by rfl) ⟨1754333, by rfl⟩ : syracuseStep 2339111 = 3508667) B3508667
theorem B2339195 : Blo 1557476 2339195 := bstep (se 1 (by rfl) ⟨1754396, by rfl⟩ : syracuseStep 2339195 = 3508793) B3508793
theorem B341185121 : Blo 1557476 341185121 := bstep (se 2 (by rfl) ⟨127944420, by rfl⟩ : syracuseStep 341185121 = 255888841) B255888841
theorem B2495615 : Blo 1557476 2495615 := bstep (se 1 (by rfl) ⟨1871711, by rfl⟩ : syracuseStep 2495615 = 3743423) B3743423
theorem B3945935 : Blo 1557476 3945935 := bstep (se 1 (by rfl) ⟨2959451, by rfl⟩ : syracuseStep 3945935 = 5918903) B5918903
theorem B24328183 : Blo 1557476 24328183 := bstep (se 1 (by rfl) ⟨18246137, by rfl⟩ : syracuseStep 24328183 = 36492275) B36492275
theorem B8427977 : Blo 1557476 8427977 := bstep (se 2 (by rfl) ⟨3160491, by rfl⟩ : syracuseStep 8427977 = 6320983) B6320983
theorem B5258087 : Blo 1557476 5258087 := bstep (se 1 (by rfl) ⟨3943565, by rfl⟩ : syracuseStep 5258087 = 7887131) B7887131
theorem B3505319 : Blo 1557476 3505319 := bstep (se 1 (by rfl) ⟨2628989, by rfl⟩ : syracuseStep 3505319 = 5257979) B5257979
theorem B38968883 : Blo 1557476 38968883 := bstep (se 1 (by rfl) ⟨29226662, by rfl⟩ : syracuseStep 38968883 = 58453325) B58453325
theorem B37936795 : Blo 1557476 37936795 := bstep (se 1 (by rfl) ⟨28452596, by rfl⟩ : syracuseStep 37936795 = 56905193) B56905193
theorem B8871839 : Blo 1557476 8871839 := bstep (se 1 (by rfl) ⟨6653879, by rfl⟩ : syracuseStep 8871839 = 13307759) B13307759
theorem B8421403 : Blo 1557476 8421403 := bstep (se 1 (by rfl) ⟨6316052, by rfl⟩ : syracuseStep 8421403 = 12632105) B12632105
theorem B3506831 : Blo 1557476 3506831 := bstep (se 1 (by rfl) ⟨2630123, by rfl⟩ : syracuseStep 3506831 = 5260247) B5260247
theorem B3998459 : Blo 1557476 3998459 := bstep (se 1 (by rfl) ⟨2998844, by rfl⟩ : syracuseStep 3998459 = 5997689) B5997689
theorem B2630623 : Blo 1557476 2630623 := bstep (se 1 (by rfl) ⟨1972967, by rfl⟩ : syracuseStep 2630623 = 3945935) B3945935
theorem B1754095 : Blo 1557476 1754095 := bstep (se 1 (by rfl) ⟨1315571, by rfl⟩ : syracuseStep 1754095 = 2631143) B2631143
theorem B1557535 : Blo 1557476 1557535 := bstep (se 1 (by rfl) ⟨1168151, by rfl⟩ : syracuseStep 1557535 = 2336303) B2336303
theorem B1557659 : Blo 1557476 1557659 := bstep (se 1 (by rfl) ⟨1168244, by rfl⟩ : syracuseStep 1557659 = 2336489) B2336489
theorem B3507623 : Blo 1557476 3507623 := bstep (se 1 (by rfl) ⟨2630717, by rfl⟩ : syracuseStep 3507623 = 5261435) B5261435
theorem B1558343 : Blo 1557476 1558343 := bstep (se 1 (by rfl) ⟨1168757, by rfl⟩ : syracuseStep 1558343 = 2337515) B2337515
theorem B3508127 : Blo 1557476 3508127 := bstep (se 1 (by rfl) ⟨2631095, by rfl⟩ : syracuseStep 3508127 = 5262191) B5262191
theorem B1558523 : Blo 1557476 1558523 := bstep (se 1 (by rfl) ⟨1168892, by rfl⟩ : syracuseStep 1558523 = 2337785) B2337785
theorem B2336879 : Blo 1557476 2336879 := bstep (se 1 (by rfl) ⟨1752659, by rfl⟩ : syracuseStep 2336879 = 3505319) B3505319
theorem B4868383 : Blo 1557476 4868383 := bstep (se 1 (by rfl) ⟨3651287, by rfl⟩ : syracuseStep 4868383 = 7302575) B7302575
theorem B25979255 : Blo 1557476 25979255 := bstep (se 1 (by rfl) ⟨19484441, by rfl⟩ : syracuseStep 25979255 = 38968883) B38968883
theorem B1559007 : Blo 1557476 1559007 := bstep (se 1 (by rfl) ⟨1169255, by rfl⟩ : syracuseStep 1559007 = 2338511) B2338511
theorem B113756669 : Blo 1557476 113756669 := bstep (se 3 (by rfl) ⟨21329375, by rfl⟩ : syracuseStep 113756669 = 42658751) B42658751
theorem B1559039 : Blo 1557476 1559039 := bstep (se 1 (by rfl) ⟨1169279, by rfl⟩ : syracuseStep 1559039 = 2338559) B2338559
theorem B1559231 : Blo 1557476 1559231 := bstep (se 1 (by rfl) ⟨1169423, by rfl⟩ : syracuseStep 1559231 = 2338847) B2338847
theorem B1559271 : Blo 1557476 1559271 := bstep (se 1 (by rfl) ⟨1169453, by rfl⟩ : syracuseStep 1559271 = 2338907) B2338907
theorem B3943151 : Blo 1557476 3943151 := bstep (se 1 (by rfl) ⟨2957363, by rfl⟩ : syracuseStep 3943151 = 5914727) B5914727
theorem B1559291 : Blo 1557476 1559291 := bstep (se 1 (by rfl) ⟨1169468, by rfl⟩ : syracuseStep 1559291 = 2338937) B2338937
theorem B1559323 : Blo 1557476 1559323 := bstep (se 1 (by rfl) ⟨1169492, by rfl⟩ : syracuseStep 1559323 = 2338985) B2338985
theorem B53980013 : Blo 1557476 53980013 := bstep (se 3 (by rfl) ⟨10121252, by rfl⟩ : syracuseStep 53980013 = 20242505) B20242505
theorem B1559407 : Blo 1557476 1559407 := bstep (se 1 (by rfl) ⟨1169555, by rfl⟩ : syracuseStep 1559407 = 2339111) B2339111
theorem B1559463 : Blo 1557476 1559463 := bstep (se 1 (by rfl) ⟨1169597, by rfl⟩ : syracuseStep 1559463 = 2339195) B2339195
theorem B6654973 : Blo 1557476 6654973 := bstep (se 3 (by rfl) ⟨1247807, by rfl⟩ : syracuseStep 6654973 = 2495615) B2495615
theorem B2337947 : Blo 1557476 2337947 := bstep (se 1 (by rfl) ⟨1753460, by rfl⟩ : syracuseStep 2337947 = 3506921) B3506921
theorem B2338151 : Blo 1557476 2338151 := bstep (se 1 (by rfl) ⟨1753613, by rfl⟩ : syracuseStep 2338151 = 3507227) B3507227
theorem B2338283 : Blo 1557476 2338283 := bstep (se 1 (by rfl) ⟨1753712, by rfl⟩ : syracuseStep 2338283 = 3507425) B3507425
theorem B2338991 : Blo 1557476 2338991 := bstep (se 1 (by rfl) ⟨1754243, by rfl⟩ : syracuseStep 2338991 = 3508487) B3508487
theorem B12808475 : Blo 1557476 12808475 := bstep (se 1 (by rfl) ⟨9606356, by rfl⟩ : syracuseStep 12808475 = 19212713) B19212713
theorem B11997841 : Blo 1557476 11997841 := bstep (se 2 (by rfl) ⟨4499190, by rfl⟩ : syracuseStep 11997841 = 8998381) B8998381
theorem B50582393 : Blo 1557476 50582393 := bstep (se 2 (by rfl) ⟨18968397, by rfl⟩ : syracuseStep 50582393 = 37936795) B37936795
theorem B32437577 : Blo 1557476 32437577 := bstep (se 2 (by rfl) ⟨12164091, by rfl⟩ : syracuseStep 32437577 = 24328183) B24328183
theorem B18945389 : Blo 1557476 18945389 := bstep (se 3 (by rfl) ⟨3552260, by rfl⟩ : syracuseStep 18945389 = 7104521) B7104521
theorem B227456747 : Blo 1557476 227456747 := bstep (se 1 (by rfl) ⟨170592560, by rfl⟩ : syracuseStep 227456747 = 341185121) B341185121
theorem B89872577 : Blo 1557476 89872577 := bstep (se 2 (by rfl) ⟨33702216, by rfl⟩ : syracuseStep 89872577 = 67404433) B67404433
theorem B2218951 : Blo 1557476 2218951 := bstep (se 1 (by rfl) ⟨1664213, by rfl⟩ : syracuseStep 2218951 = 3328427) B3328427
theorem B5618651 : Blo 1557476 5618651 := bstep (se 1 (by rfl) ⟨4213988, by rfl⟩ : syracuseStep 5618651 = 8427977) B8427977
theorem B3505391 : Blo 1557476 3505391 := bstep (se 1 (by rfl) ⟨2629043, by rfl⟩ : syracuseStep 3505391 = 5258087) B5258087
theorem B11231135 : Blo 1557476 11231135 := bstep (se 1 (by rfl) ⟨8423351, by rfl⟩ : syracuseStep 11231135 = 16846703) B16846703
theorem B5914559 : Blo 1557476 5914559 := bstep (se 1 (by rfl) ⟨4435919, by rfl⟩ : syracuseStep 5914559 = 8871839) B8871839
theorem B2958601 : Blo 1557476 2958601 := bstep (se 2 (by rfl) ⟨1109475, by rfl⟩ : syracuseStep 2958601 = 2218951) B2218951
theorem B3507497 : Blo 1557476 3507497 := bstep (se 2 (by rfl) ⟨1315311, by rfl⟩ : syracuseStep 3507497 = 2630623) B2630623
theorem B8873297 : Blo 1557476 8873297 := bstep (se 2 (by rfl) ⟨3327486, by rfl⟩ : syracuseStep 8873297 = 6654973) B6654973
theorem B1557919 : Blo 1557476 1557919 := bstep (se 1 (by rfl) ⟨1168439, by rfl⟩ : syracuseStep 1557919 = 2336879) B2336879
theorem B17319503 : Blo 1557476 17319503 := bstep (se 1 (by rfl) ⟨12989627, by rfl⟩ : syracuseStep 17319503 = 25979255) B25979255
theorem B1558631 : Blo 1557476 1558631 := bstep (se 1 (by rfl) ⟨1168973, by rfl⟩ : syracuseStep 1558631 = 2337947) B2337947
theorem B2336927 : Blo 1557476 2336927 := bstep (se 1 (by rfl) ⟨1752695, by rfl⟩ : syracuseStep 2336927 = 3505391) B3505391
theorem B1558767 : Blo 1557476 1558767 := bstep (se 1 (by rfl) ⟨1169075, by rfl⟩ : syracuseStep 1558767 = 2338151) B2338151
theorem B1558855 : Blo 1557476 1558855 := bstep (se 1 (by rfl) ⟨1169141, by rfl⟩ : syracuseStep 1558855 = 2338283) B2338283
theorem B3943039 : Blo 1557476 3943039 := bstep (se 1 (by rfl) ⟨2957279, by rfl⟩ : syracuseStep 3943039 = 5914559) B5914559
theorem B1559327 : Blo 1557476 1559327 := bstep (se 1 (by rfl) ⟨1169495, by rfl⟩ : syracuseStep 1559327 = 2338991) B2338991
theorem B8538983 : Blo 1557476 8538983 := bstep (se 1 (by rfl) ⟨6404237, by rfl⟩ : syracuseStep 8538983 = 12808475) B12808475
theorem B6491177 : Blo 1557476 6491177 := bstep (se 2 (by rfl) ⟨2434191, by rfl⟩ : syracuseStep 6491177 = 4868383) B4868383
theorem B2337887 : Blo 1557476 2337887 := bstep (se 1 (by rfl) ⟨1753415, by rfl⟩ : syracuseStep 2337887 = 3506831) B3506831
theorem B2665639 : Blo 1557476 2665639 := bstep (se 1 (by rfl) ⟨1999229, by rfl⟩ : syracuseStep 2665639 = 3998459) B3998459
theorem B33721595 : Blo 1557476 33721595 := bstep (se 1 (by rfl) ⟨25291196, by rfl⟩ : syracuseStep 33721595 = 50582393) B50582393
theorem B2338415 : Blo 1557476 2338415 := bstep (se 1 (by rfl) ⟨1753811, by rfl⟩ : syracuseStep 2338415 = 3507623) B3507623
theorem B151637831 : Blo 1557476 151637831 := bstep (se 1 (by rfl) ⟨113728373, by rfl⟩ : syracuseStep 151637831 = 227456747) B227456747
theorem B2338751 : Blo 1557476 2338751 := bstep (se 1 (by rfl) ⟨1754063, by rfl⟩ : syracuseStep 2338751 = 3508127) B3508127
theorem B2338793 : Blo 1557476 2338793 := bstep (se 2 (by rfl) ⟨877047, by rfl⟩ : syracuseStep 2338793 = 1754095) B1754095
theorem B75837779 : Blo 1557476 75837779 := bstep (se 1 (by rfl) ⟨56878334, by rfl⟩ : syracuseStep 75837779 = 113756669) B113756669
theorem B11228537 : Blo 1557476 11228537 := bstep (se 2 (by rfl) ⟨4210701, by rfl⟩ : syracuseStep 11228537 = 8421403) B8421403
theorem B15997121 : Blo 1557476 15997121 := bstep (se 2 (by rfl) ⟨5998920, by rfl⟩ : syracuseStep 15997121 = 11997841) B11997841
theorem B21625051 : Blo 1557476 21625051 := bstep (se 1 (by rfl) ⟨16218788, by rfl⟩ : syracuseStep 21625051 = 32437577) B32437577
theorem B12630259 : Blo 1557476 12630259 := bstep (se 1 (by rfl) ⟨9472694, by rfl⟩ : syracuseStep 12630259 = 18945389) B18945389
theorem B59915051 : Blo 1557476 59915051 := bstep (se 1 (by rfl) ⟨44936288, by rfl⟩ : syracuseStep 59915051 = 89872577) B89872577
theorem B2628767 : Blo 1557476 2628767 := bstep (se 1 (by rfl) ⟨1971575, by rfl⟩ : syracuseStep 2628767 = 3943151) B3943151
theorem B35986675 : Blo 1557476 35986675 := bstep (se 1 (by rfl) ⟨26990006, by rfl⟩ : syracuseStep 35986675 = 53980013) B53980013
theorem B14983069 : Blo 1557476 14983069 := bstep (se 3 (by rfl) ⟨2809325, by rfl⟩ : syracuseStep 14983069 = 5618651) B5618651
theorem B7487423 : Blo 1557476 7487423 := bstep (se 1 (by rfl) ⟨5615567, by rfl⟩ : syracuseStep 7487423 = 11231135) B11231135
theorem B5915531 : Blo 1557476 5915531 := bstep (se 1 (by rfl) ⟨4436648, by rfl⟩ : syracuseStep 5915531 = 8873297) B8873297
theorem B1557951 : Blo 1557476 1557951 := bstep (se 1 (by rfl) ⟨1168463, by rfl⟩ : syracuseStep 1557951 = 2336927) B2336927
theorem B47982233 : Blo 1557476 47982233 := bstep (se 2 (by rfl) ⟨17993337, by rfl⟩ : syracuseStep 47982233 = 35986675) B35986675
theorem B4327451 : Blo 1557476 4327451 := bstep (se 1 (by rfl) ⟨3245588, by rfl⟩ : syracuseStep 4327451 = 6491177) B6491177
theorem B1558591 : Blo 1557476 1558591 := bstep (se 1 (by rfl) ⟨1168943, by rfl⟩ : syracuseStep 1558591 = 2337887) B2337887
theorem B22481063 : Blo 1557476 22481063 := bstep (se 1 (by rfl) ⟨16860797, by rfl⟩ : syracuseStep 22481063 = 33721595) B33721595
theorem B1558943 : Blo 1557476 1558943 := bstep (se 1 (by rfl) ⟨1169207, by rfl⟩ : syracuseStep 1558943 = 2338415) B2338415
theorem B101091887 : Blo 1557476 101091887 := bstep (se 1 (by rfl) ⟨75818915, by rfl⟩ : syracuseStep 101091887 = 151637831) B151637831
theorem B4991615 : Blo 1557476 4991615 := bstep (se 1 (by rfl) ⟨3743711, by rfl⟩ : syracuseStep 4991615 = 7487423) B7487423
theorem B1559167 : Blo 1557476 1559167 := bstep (se 1 (by rfl) ⟨1169375, by rfl⟩ : syracuseStep 1559167 = 2338751) B2338751
theorem B1559195 : Blo 1557476 1559195 := bstep (se 1 (by rfl) ⟨1169396, by rfl⟩ : syracuseStep 1559195 = 2338793) B2338793
theorem B2338331 : Blo 1557476 2338331 := bstep (se 1 (by rfl) ⟨1753748, by rfl⟩ : syracuseStep 2338331 = 3507497) B3507497
theorem B14216741 : Blo 1557476 14216741 := bstep (se 4 (by rfl) ⟨1332819, by rfl⟩ : syracuseStep 14216741 = 2665639) B2665639
theorem B11546335 : Blo 1557476 11546335 := bstep (se 1 (by rfl) ⟨8659751, by rfl⟩ : syracuseStep 11546335 = 17319503) B17319503
theorem B3944801 : Blo 1557476 3944801 := bstep (se 2 (by rfl) ⟨1479300, by rfl⟩ : syracuseStep 3944801 = 2958601) B2958601
theorem B19977425 : Blo 1557476 19977425 := bstep (se 2 (by rfl) ⟨7491534, by rfl⟩ : syracuseStep 19977425 = 14983069) B14983069
theorem B50558519 : Blo 1557476 50558519 := bstep (se 1 (by rfl) ⟨37918889, by rfl⟩ : syracuseStep 50558519 = 75837779) B75837779
theorem B28833401 : Blo 1557476 28833401 := bstep (se 2 (by rfl) ⟨10812525, by rfl⟩ : syracuseStep 28833401 = 21625051) B21625051
theorem B16840345 : Blo 1557476 16840345 := bstep (se 2 (by rfl) ⟨6315129, by rfl⟩ : syracuseStep 16840345 = 12630259) B12630259
theorem B5257385 : Blo 1557476 5257385 := bstep (se 2 (by rfl) ⟨1971519, by rfl⟩ : syracuseStep 5257385 = 3943039) B3943039
theorem B7485691 : Blo 1557476 7485691 := bstep (se 1 (by rfl) ⟨5614268, by rfl⟩ : syracuseStep 7485691 = 11228537) B11228537
theorem B10664747 : Blo 1557476 10664747 := bstep (se 1 (by rfl) ⟨7998560, by rfl⟩ : syracuseStep 10664747 = 15997121) B15997121
theorem B39943367 : Blo 1557476 39943367 := bstep (se 1 (by rfl) ⟨29957525, by rfl⟩ : syracuseStep 39943367 = 59915051) B59915051
theorem B5692655 : Blo 1557476 5692655 := bstep (se 1 (by rfl) ⟨4269491, by rfl⟩ : syracuseStep 5692655 = 8538983) B8538983
theorem B1752511 : Blo 1557476 1752511 := bstep (se 1 (by rfl) ⟨1314383, by rfl⟩ : syracuseStep 1752511 = 2628767) B2628767
theorem B2629867 : Blo 1557476 2629867 := bstep (se 1 (by rfl) ⟨1972400, by rfl⟩ : syracuseStep 2629867 = 3944801) B3944801
theorem B2884967 : Blo 1557476 2884967 := bstep (se 1 (by rfl) ⟨2163725, by rfl⟩ : syracuseStep 2884967 = 4327451) B4327451
theorem B127952621 : Blo 1557476 127952621 := bstep (se 3 (by rfl) ⟨23991116, by rfl⟩ : syracuseStep 127952621 = 47982233) B47982233
theorem B3327743 : Blo 1557476 3327743 := bstep (se 1 (by rfl) ⟨2495807, by rfl⟩ : syracuseStep 3327743 = 4991615) B4991615
theorem B2336681 : Blo 1557476 2336681 := bstep (se 2 (by rfl) ⟨876255, by rfl⟩ : syracuseStep 2336681 = 1752511) B1752511
theorem B3795103 : Blo 1557476 3795103 := bstep (se 1 (by rfl) ⟨2846327, by rfl⟩ : syracuseStep 3795103 = 5692655) B5692655
theorem B15395113 : Blo 1557476 15395113 := bstep (se 2 (by rfl) ⟨5773167, by rfl⟩ : syracuseStep 15395113 = 11546335) B11546335
theorem B1558887 : Blo 1557476 1558887 := bstep (se 1 (by rfl) ⟨1169165, by rfl⟩ : syracuseStep 1558887 = 2338331) B2338331
theorem B9980921 : Blo 1557476 9980921 := bstep (se 2 (by rfl) ⟨3742845, by rfl⟩ : syracuseStep 9980921 = 7485691) B7485691
theorem B3943687 : Blo 1557476 3943687 := bstep (se 1 (by rfl) ⟨2957765, by rfl⟩ : syracuseStep 3943687 = 5915531) B5915531
theorem B33705679 : Blo 1557476 33705679 := bstep (se 1 (by rfl) ⟨25279259, by rfl⟩ : syracuseStep 33705679 = 50558519) B50558519
theorem B19222267 : Blo 1557476 19222267 := bstep (se 1 (by rfl) ⟨14416700, by rfl⟩ : syracuseStep 19222267 = 28833401) B28833401
theorem B14987375 : Blo 1557476 14987375 := bstep (se 1 (by rfl) ⟨11240531, by rfl⟩ : syracuseStep 14987375 = 22481063) B22481063
theorem B26628911 : Blo 1557476 26628911 := bstep (se 1 (by rfl) ⟨19971683, by rfl⟩ : syracuseStep 26628911 = 39943367) B39943367
theorem B13318283 : Blo 1557476 13318283 := bstep (se 1 (by rfl) ⟨9988712, by rfl⟩ : syracuseStep 13318283 = 19977425) B19977425
theorem B3504923 : Blo 1557476 3504923 := bstep (se 1 (by rfl) ⟨2628692, by rfl⟩ : syracuseStep 3504923 = 5257385) B5257385
theorem B67394591 : Blo 1557476 67394591 := bstep (se 1 (by rfl) ⟨50545943, by rfl⟩ : syracuseStep 67394591 = 101091887) B101091887
theorem B7109831 : Blo 1557476 7109831 := bstep (se 1 (by rfl) ⟨5332373, by rfl⟩ : syracuseStep 7109831 = 10664747) B10664747
theorem B22453793 : Blo 1557476 22453793 := bstep (se 2 (by rfl) ⟨8420172, by rfl⟩ : syracuseStep 22453793 = 16840345) B16840345
theorem B9477827 : Blo 1557476 9477827 := bstep (se 1 (by rfl) ⟨7108370, by rfl⟩ : syracuseStep 9477827 = 14216741) B14216741
theorem B3506489 : Blo 1557476 3506489 := bstep (se 2 (by rfl) ⟨1314933, by rfl⟩ : syracuseStep 3506489 = 2629867) B2629867
theorem B17752607 : Blo 1557476 17752607 := bstep (se 1 (by rfl) ⟨13314455, by rfl⟩ : syracuseStep 17752607 = 26628911) B26628911
theorem B1557787 : Blo 1557476 1557787 := bstep (se 1 (by rfl) ⟨1168340, by rfl⟩ : syracuseStep 1557787 = 2336681) B2336681
theorem B2336615 : Blo 1557476 2336615 := bstep (se 1 (by rfl) ⟨1752461, by rfl⟩ : syracuseStep 2336615 = 3504923) B3504923
theorem B8873981 : Blo 1557476 8873981 := bstep (se 3 (by rfl) ⟨1663871, by rfl⟩ : syracuseStep 8873981 = 3327743) B3327743
theorem B14969195 : Blo 1557476 14969195 := bstep (se 1 (by rfl) ⟨11226896, by rfl⟩ : syracuseStep 14969195 = 22453793) B22453793
theorem B6318551 : Blo 1557476 6318551 := bstep (se 1 (by rfl) ⟨4738913, by rfl⟩ : syracuseStep 6318551 = 9477827) B9477827
theorem B44929727 : Blo 1557476 44929727 := bstep (se 1 (by rfl) ⟨33697295, by rfl⟩ : syracuseStep 44929727 = 67394591) B67394591
theorem B4739887 : Blo 1557476 4739887 := bstep (se 1 (by rfl) ⟨3554915, by rfl⟩ : syracuseStep 4739887 = 7109831) B7109831
theorem B25629689 : Blo 1557476 25629689 := bstep (se 2 (by rfl) ⟨9611133, by rfl⟩ : syracuseStep 25629689 = 19222267) B19222267
theorem B9991583 : Blo 1557476 9991583 := bstep (se 1 (by rfl) ⟨7493687, by rfl⟩ : syracuseStep 9991583 = 14987375) B14987375
theorem B20526817 : Blo 1557476 20526817 := bstep (se 2 (by rfl) ⟨7697556, by rfl⟩ : syracuseStep 20526817 = 15395113) B15395113
theorem B20240549 : Blo 1557476 20240549 := bstep (se 4 (by rfl) ⟨1897551, by rfl⟩ : syracuseStep 20240549 = 3795103) B3795103
theorem B1923311 : Blo 1557476 1923311 := bstep (se 1 (by rfl) ⟨1442483, by rfl⟩ : syracuseStep 1923311 = 2884967) B2884967
theorem B85301747 : Blo 1557476 85301747 := bstep (se 1 (by rfl) ⟨63976310, by rfl⟩ : syracuseStep 85301747 = 127952621) B127952621
theorem B8878855 : Blo 1557476 8878855 := bstep (se 1 (by rfl) ⟨6659141, by rfl⟩ : syracuseStep 8878855 = 13318283) B13318283
theorem B5258249 : Blo 1557476 5258249 := bstep (se 2 (by rfl) ⟨1971843, by rfl⟩ : syracuseStep 5258249 = 3943687) B3943687
theorem B44940905 : Blo 1557476 44940905 := bstep (se 2 (by rfl) ⟨16852839, by rfl⟩ : syracuseStep 44940905 = 33705679) B33705679
theorem B26615789 : Blo 1557476 26615789 := bstep (se 3 (by rfl) ⟨4990460, by rfl⟩ : syracuseStep 26615789 = 9980921) B9980921
theorem B5128829 : Blo 1557476 5128829 := bstep (se 3 (by rfl) ⟨961655, by rfl⟩ : syracuseStep 5128829 = 1923311) B1923311
theorem B6661055 : Blo 1557476 6661055 := bstep (se 1 (by rfl) ⟨4995791, by rfl⟩ : syracuseStep 6661055 = 9991583) B9991583
theorem B11838473 : Blo 1557476 11838473 := bstep (se 2 (by rfl) ⟨4439427, by rfl⟩ : syracuseStep 11838473 = 8878855) B8878855
theorem B1557743 : Blo 1557476 1557743 := bstep (se 1 (by rfl) ⟨1168307, by rfl⟩ : syracuseStep 1557743 = 2336615) B2336615
theorem B5915987 : Blo 1557476 5915987 := bstep (se 1 (by rfl) ⟨4436990, by rfl⟩ : syracuseStep 5915987 = 8873981) B8873981
theorem B13493699 : Blo 1557476 13493699 := bstep (se 1 (by rfl) ⟨10120274, by rfl⟩ : syracuseStep 13493699 = 20240549) B20240549
theorem B9979463 : Blo 1557476 9979463 := bstep (se 1 (by rfl) ⟨7484597, by rfl⟩ : syracuseStep 9979463 = 14969195) B14969195
theorem B4212367 : Blo 1557476 4212367 := bstep (se 1 (by rfl) ⟨3159275, by rfl⟩ : syracuseStep 4212367 = 6318551) B6318551
theorem B29960603 : Blo 1557476 29960603 := bstep (se 1 (by rfl) ⟨22470452, by rfl⟩ : syracuseStep 29960603 = 44940905) B44940905
theorem B2337659 : Blo 1557476 2337659 := bstep (se 1 (by rfl) ⟨1753244, by rfl⟩ : syracuseStep 2337659 = 3506489) B3506489
theorem B29953151 : Blo 1557476 29953151 := bstep (se 1 (by rfl) ⟨22464863, by rfl⟩ : syracuseStep 29953151 = 44929727) B44929727
theorem B11835071 : Blo 1557476 11835071 := bstep (se 1 (by rfl) ⟨8876303, by rfl⟩ : syracuseStep 11835071 = 17752607) B17752607
theorem B17086459 : Blo 1557476 17086459 := bstep (se 1 (by rfl) ⟨12814844, by rfl⟩ : syracuseStep 17086459 = 25629689) B25629689
theorem B25279397 : Blo 1557476 25279397 := bstep (se 4 (by rfl) ⟨2369943, by rfl⟩ : syracuseStep 25279397 = 4739887) B4739887
theorem B56867831 : Blo 1557476 56867831 := bstep (se 1 (by rfl) ⟨42650873, by rfl⟩ : syracuseStep 56867831 = 85301747) B85301747
theorem B3505499 : Blo 1557476 3505499 := bstep (se 1 (by rfl) ⟨2629124, by rfl⟩ : syracuseStep 3505499 = 5258249) B5258249
theorem B27369089 : Blo 1557476 27369089 := bstep (se 2 (by rfl) ⟨10263408, by rfl⟩ : syracuseStep 27369089 = 20526817) B20526817
theorem B17743859 : Blo 1557476 17743859 := bstep (se 1 (by rfl) ⟨13307894, by rfl⟩ : syracuseStep 17743859 = 26615789) B26615789
theorem B11829239 : Blo 1557476 11829239 := bstep (se 1 (by rfl) ⟨8871929, by rfl⟩ : syracuseStep 11829239 = 17743859) B17743859
theorem B8995799 : Blo 1557476 8995799 := bstep (se 1 (by rfl) ⟨6746849, by rfl⟩ : syracuseStep 8995799 = 13493699) B13493699
theorem B6652975 : Blo 1557476 6652975 := bstep (se 1 (by rfl) ⟨4989731, by rfl⟩ : syracuseStep 6652975 = 9979463) B9979463
theorem B7890047 : Blo 1557476 7890047 := bstep (se 1 (by rfl) ⟨5917535, by rfl⟩ : syracuseStep 7890047 = 11835071) B11835071
theorem B19973735 : Blo 1557476 19973735 := bstep (se 1 (by rfl) ⟨14980301, by rfl⟩ : syracuseStep 19973735 = 29960603) B29960603
theorem B1558439 : Blo 1557476 1558439 := bstep (se 1 (by rfl) ⟨1168829, by rfl⟩ : syracuseStep 1558439 = 2337659) B2337659
theorem B16852931 : Blo 1557476 16852931 := bstep (se 1 (by rfl) ⟨12639698, by rfl⟩ : syracuseStep 16852931 = 25279397) B25279397
theorem B2336999 : Blo 1557476 2336999 := bstep (se 1 (by rfl) ⟨1752749, by rfl⟩ : syracuseStep 2336999 = 3505499) B3505499
theorem B18246059 : Blo 1557476 18246059 := bstep (se 1 (by rfl) ⟨13684544, by rfl⟩ : syracuseStep 18246059 = 27369089) B27369089
theorem B17762813 : Blo 1557476 17762813 := bstep (se 3 (by rfl) ⟨3330527, by rfl⟩ : syracuseStep 17762813 = 6661055) B6661055
theorem B3419219 : Blo 1557476 3419219 := bstep (se 1 (by rfl) ⟨2564414, by rfl⟩ : syracuseStep 3419219 = 5128829) B5128829
theorem B7892315 : Blo 1557476 7892315 := bstep (se 1 (by rfl) ⟨5919236, by rfl⟩ : syracuseStep 7892315 = 11838473) B11838473
theorem B22465957 : Blo 1557476 22465957 := bstep (se 4 (by rfl) ⟨2106183, by rfl⟩ : syracuseStep 22465957 = 4212367) B4212367
theorem B3943991 : Blo 1557476 3943991 := bstep (se 1 (by rfl) ⟨2957993, by rfl⟩ : syracuseStep 3943991 = 5915987) B5915987
theorem B19968767 : Blo 1557476 19968767 := bstep (se 1 (by rfl) ⟨14976575, by rfl⟩ : syracuseStep 19968767 = 29953151) B29953151
theorem B37911887 : Blo 1557476 37911887 := bstep (se 1 (by rfl) ⟨28433915, by rfl⟩ : syracuseStep 37911887 = 56867831) B56867831
theorem B22781945 : Blo 1557476 22781945 := bstep (se 2 (by rfl) ⟨8543229, by rfl⟩ : syracuseStep 22781945 = 17086459) B17086459
theorem B13312511 : Blo 1557476 13312511 := bstep (se 1 (by rfl) ⟨9984383, by rfl⟩ : syracuseStep 13312511 = 19968767) B19968767
theorem B5997199 : Blo 1557476 5997199 := bstep (se 1 (by rfl) ⟨4497899, by rfl⟩ : syracuseStep 5997199 = 8995799) B8995799
theorem B5260031 : Blo 1557476 5260031 := bstep (se 1 (by rfl) ⟨3945023, by rfl⟩ : syracuseStep 5260031 = 7890047) B7890047
theorem B1557999 : Blo 1557476 1557999 := bstep (se 1 (by rfl) ⟨1168499, by rfl⟩ : syracuseStep 1557999 = 2336999) B2336999
theorem B2279479 : Blo 1557476 2279479 := bstep (se 1 (by rfl) ⟨1709609, by rfl⟩ : syracuseStep 2279479 = 3419219) B3419219
theorem B25274591 : Blo 1557476 25274591 := bstep (se 1 (by rfl) ⟨18955943, by rfl⟩ : syracuseStep 25274591 = 37911887) B37911887
theorem B5261543 : Blo 1557476 5261543 := bstep (se 1 (by rfl) ⟨3946157, by rfl⟩ : syracuseStep 5261543 = 7892315) B7892315
theorem B13315823 : Blo 1557476 13315823 := bstep (se 1 (by rfl) ⟨9986867, by rfl⟩ : syracuseStep 13315823 = 19973735) B19973735
theorem B11235287 : Blo 1557476 11235287 := bstep (se 1 (by rfl) ⟨8426465, by rfl⟩ : syracuseStep 11235287 = 16852931) B16852931
theorem B11841875 : Blo 1557476 11841875 := bstep (se 1 (by rfl) ⟨8881406, by rfl⟩ : syracuseStep 11841875 = 17762813) B17762813
theorem B29954609 : Blo 1557476 29954609 := bstep (se 2 (by rfl) ⟨11232978, by rfl⟩ : syracuseStep 29954609 = 22465957) B22465957
theorem B7886159 : Blo 1557476 7886159 := bstep (se 1 (by rfl) ⟨5914619, by rfl⟩ : syracuseStep 7886159 = 11829239) B11829239
theorem B8870633 : Blo 1557476 8870633 := bstep (se 2 (by rfl) ⟨3326487, by rfl⟩ : syracuseStep 8870633 = 6652975) B6652975
theorem B12164039 : Blo 1557476 12164039 := bstep (se 1 (by rfl) ⟨9123029, by rfl⟩ : syracuseStep 12164039 = 18246059) B18246059
theorem B2629327 : Blo 1557476 2629327 := bstep (se 1 (by rfl) ⟨1971995, by rfl⟩ : syracuseStep 2629327 = 3943991) B3943991
theorem B60751853 : Blo 1557476 60751853 := bstep (se 3 (by rfl) ⟨11390972, by rfl⟩ : syracuseStep 60751853 = 22781945) B22781945
theorem B3506687 : Blo 1557476 3506687 := bstep (se 1 (by rfl) ⟨2630015, by rfl⟩ : syracuseStep 3506687 = 5260031) B5260031
theorem B7996265 : Blo 1557476 7996265 := bstep (se 2 (by rfl) ⟨2998599, by rfl⟩ : syracuseStep 7996265 = 5997199) B5997199
theorem B48628885 : Blo 1557476 48628885 := bstep (se 6 (by rfl) ⟨1139739, by rfl⟩ : syracuseStep 48628885 = 2279479) B2279479
theorem B3507695 : Blo 1557476 3507695 := bstep (se 1 (by rfl) ⟨2630771, by rfl⟩ : syracuseStep 3507695 = 5261543) B5261543
theorem B7490191 : Blo 1557476 7490191 := bstep (se 1 (by rfl) ⟨5617643, by rfl⟩ : syracuseStep 7490191 = 11235287) B11235287
theorem B8875007 : Blo 1557476 8875007 := bstep (se 1 (by rfl) ⟨6656255, by rfl⟩ : syracuseStep 8875007 = 13312511) B13312511
theorem B8877215 : Blo 1557476 8877215 := bstep (se 1 (by rfl) ⟨6657911, by rfl⟩ : syracuseStep 8877215 = 13315823) B13315823
theorem B7894583 : Blo 1557476 7894583 := bstep (se 1 (by rfl) ⟨5920937, by rfl⟩ : syracuseStep 7894583 = 11841875) B11841875
theorem B19969739 : Blo 1557476 19969739 := bstep (se 1 (by rfl) ⟨14977304, by rfl⟩ : syracuseStep 19969739 = 29954609) B29954609
theorem B5257439 : Blo 1557476 5257439 := bstep (se 1 (by rfl) ⟨3943079, by rfl⟩ : syracuseStep 5257439 = 7886159) B7886159
theorem B16849727 : Blo 1557476 16849727 := bstep (se 1 (by rfl) ⟨12637295, by rfl⟩ : syracuseStep 16849727 = 25274591) B25274591
theorem B5913755 : Blo 1557476 5913755 := bstep (se 1 (by rfl) ⟨4435316, by rfl⟩ : syracuseStep 5913755 = 8870633) B8870633
theorem B8109359 : Blo 1557476 8109359 := bstep (se 1 (by rfl) ⟨6082019, by rfl⟩ : syracuseStep 8109359 = 12164039) B12164039
theorem B3505769 : Blo 1557476 3505769 := bstep (se 2 (by rfl) ⟨1314663, by rfl⟩ : syracuseStep 3505769 = 2629327) B2629327
theorem B40501235 : Blo 1557476 40501235 := bstep (se 1 (by rfl) ⟨30375926, by rfl⟩ : syracuseStep 40501235 = 60751853) B60751853
theorem B9986921 : Blo 1557476 9986921 := bstep (se 2 (by rfl) ⟨3745095, by rfl⟩ : syracuseStep 9986921 = 7490191) B7490191
theorem B13313159 : Blo 1557476 13313159 := bstep (se 1 (by rfl) ⟨9984869, by rfl⟩ : syracuseStep 13313159 = 19969739) B19969739
theorem B11233151 : Blo 1557476 11233151 := bstep (se 1 (by rfl) ⟨8424863, by rfl⟩ : syracuseStep 11233151 = 16849727) B16849727
theorem B5916671 : Blo 1557476 5916671 := bstep (se 1 (by rfl) ⟨4437503, by rfl⟩ : syracuseStep 5916671 = 8875007) B8875007
theorem B3942503 : Blo 1557476 3942503 := bstep (se 1 (by rfl) ⟨2956877, by rfl⟩ : syracuseStep 3942503 = 5913755) B5913755
theorem B2337179 : Blo 1557476 2337179 := bstep (se 1 (by rfl) ⟨1752884, by rfl⟩ : syracuseStep 2337179 = 3505769) B3505769
theorem B2337791 : Blo 1557476 2337791 := bstep (se 1 (by rfl) ⟨1753343, by rfl⟩ : syracuseStep 2337791 = 3506687) B3506687
theorem B5918143 : Blo 1557476 5918143 := bstep (se 1 (by rfl) ⟨4438607, by rfl⟩ : syracuseStep 5918143 = 8877215) B8877215
theorem B2338463 : Blo 1557476 2338463 := bstep (se 1 (by rfl) ⟨1753847, by rfl⟩ : syracuseStep 2338463 = 3507695) B3507695
theorem B5263055 : Blo 1557476 5263055 := bstep (se 1 (by rfl) ⟨3947291, by rfl⟩ : syracuseStep 5263055 = 7894583) B7894583
theorem B5330843 : Blo 1557476 5330843 := bstep (se 1 (by rfl) ⟨3998132, by rfl⟩ : syracuseStep 5330843 = 7996265) B7996265
theorem B3504959 : Blo 1557476 3504959 := bstep (se 1 (by rfl) ⟨2628719, by rfl⟩ : syracuseStep 3504959 = 5257439) B5257439
theorem B64838513 : Blo 1557476 64838513 := bstep (se 2 (by rfl) ⟨24314442, by rfl⟩ : syracuseStep 64838513 = 48628885) B48628885
theorem B5406239 : Blo 1557476 5406239 := bstep (se 1 (by rfl) ⟨4054679, by rfl⟩ : syracuseStep 5406239 = 8109359) B8109359
theorem B27000823 : Blo 1557476 27000823 := bstep (se 1 (by rfl) ⟨20250617, by rfl⟩ : syracuseStep 27000823 = 40501235) B40501235
theorem B7488767 : Blo 1557476 7488767 := bstep (se 1 (by rfl) ⟨5616575, by rfl⟩ : syracuseStep 7488767 = 11233151) B11233151
theorem B1558119 : Blo 1557476 1558119 := bstep (se 1 (by rfl) ⟨1168589, by rfl⟩ : syracuseStep 1558119 = 2337179) B2337179
theorem B2336639 : Blo 1557476 2336639 := bstep (se 1 (by rfl) ⟨1752479, by rfl⟩ : syracuseStep 2336639 = 3504959) B3504959
theorem B7890857 : Blo 1557476 7890857 := bstep (se 2 (by rfl) ⟨2959071, by rfl⟩ : syracuseStep 7890857 = 5918143) B5918143
theorem B1558527 : Blo 1557476 1558527 := bstep (se 1 (by rfl) ⟨1168895, by rfl⟩ : syracuseStep 1558527 = 2337791) B2337791
theorem B172902701 : Blo 1557476 172902701 := bstep (se 3 (by rfl) ⟨32419256, by rfl⟩ : syracuseStep 172902701 = 64838513) B64838513
theorem B1558975 : Blo 1557476 1558975 := bstep (se 1 (by rfl) ⟨1169231, by rfl⟩ : syracuseStep 1558975 = 2338463) B2338463
theorem B3508703 : Blo 1557476 3508703 := bstep (se 1 (by rfl) ⟨2631527, by rfl⟩ : syracuseStep 3508703 = 5263055) B5263055
theorem B8875439 : Blo 1557476 8875439 := bstep (se 1 (by rfl) ⟨6656579, by rfl⟩ : syracuseStep 8875439 = 13313159) B13313159
theorem B3944447 : Blo 1557476 3944447 := bstep (se 1 (by rfl) ⟨2958335, by rfl⟩ : syracuseStep 3944447 = 5916671) B5916671
theorem B36001097 : Blo 1557476 36001097 := bstep (se 2 (by rfl) ⟨13500411, by rfl⟩ : syracuseStep 36001097 = 27000823) B27000823
theorem B6657947 : Blo 1557476 6657947 := bstep (se 1 (by rfl) ⟨4993460, by rfl⟩ : syracuseStep 6657947 = 9986921) B9986921
theorem B3553895 : Blo 1557476 3553895 := bstep (se 1 (by rfl) ⟨2665421, by rfl⟩ : syracuseStep 3553895 = 5330843) B5330843
theorem B2628335 : Blo 1557476 2628335 := bstep (se 1 (by rfl) ⟨1971251, by rfl⟩ : syracuseStep 2628335 = 3942503) B3942503
theorem B3604159 : Blo 1557476 3604159 := bstep (se 1 (by rfl) ⟨2703119, by rfl⟩ : syracuseStep 3604159 = 5406239) B5406239
theorem B1557759 : Blo 1557476 1557759 := bstep (se 1 (by rfl) ⟨1168319, by rfl⟩ : syracuseStep 1557759 = 2336639) B2336639
theorem B5260571 : Blo 1557476 5260571 := bstep (se 1 (by rfl) ⟨3945428, by rfl⟩ : syracuseStep 5260571 = 7890857) B7890857
theorem B2369263 : Blo 1557476 2369263 := bstep (se 1 (by rfl) ⟨1776947, by rfl⟩ : syracuseStep 2369263 = 3553895) B3553895
theorem B5916959 : Blo 1557476 5916959 := bstep (se 1 (by rfl) ⟨4437719, by rfl⟩ : syracuseStep 5916959 = 8875439) B8875439
theorem B4992511 : Blo 1557476 4992511 := bstep (se 1 (by rfl) ⟨3744383, by rfl⟩ : syracuseStep 4992511 = 7488767) B7488767
theorem B19222181 : Blo 1557476 19222181 := bstep (se 4 (by rfl) ⟨1802079, by rfl⟩ : syracuseStep 19222181 = 3604159) B3604159
theorem B2339135 : Blo 1557476 2339135 := bstep (se 1 (by rfl) ⟨1754351, by rfl⟩ : syracuseStep 2339135 = 3508703) B3508703
theorem B24000731 : Blo 1557476 24000731 := bstep (se 1 (by rfl) ⟨18000548, by rfl⟩ : syracuseStep 24000731 = 36001097) B36001097
theorem B4438631 : Blo 1557476 4438631 := bstep (se 1 (by rfl) ⟨3328973, by rfl⟩ : syracuseStep 4438631 = 6657947) B6657947
theorem B115268467 : Blo 1557476 115268467 := bstep (se 1 (by rfl) ⟨86451350, by rfl⟩ : syracuseStep 115268467 = 172902701) B172902701
theorem B1752223 : Blo 1557476 1752223 := bstep (se 1 (by rfl) ⟨1314167, by rfl⟩ : syracuseStep 1752223 = 2628335) B2628335
theorem B2629631 : Blo 1557476 2629631 := bstep (se 1 (by rfl) ⟨1972223, by rfl⟩ : syracuseStep 2629631 = 3944447) B3944447
theorem B3507047 : Blo 1557476 3507047 := bstep (se 1 (by rfl) ⟨2630285, by rfl⟩ : syracuseStep 3507047 = 5260571) B5260571
theorem B153691289 : Blo 1557476 153691289 := bstep (se 2 (by rfl) ⟨57634233, by rfl⟩ : syracuseStep 153691289 = 115268467) B115268467
theorem B16000487 : Blo 1557476 16000487 := bstep (se 1 (by rfl) ⟨12000365, by rfl⟩ : syracuseStep 16000487 = 24000731) B24000731
theorem B2336297 : Blo 1557476 2336297 := bstep (se 2 (by rfl) ⟨876111, by rfl⟩ : syracuseStep 2336297 = 1752223) B1752223
theorem B2959087 : Blo 1557476 2959087 := bstep (se 1 (by rfl) ⟨2219315, by rfl⟩ : syracuseStep 2959087 = 4438631) B4438631
theorem B12814787 : Blo 1557476 12814787 := bstep (se 1 (by rfl) ⟨9611090, by rfl⟩ : syracuseStep 12814787 = 19222181) B19222181
theorem B1559423 : Blo 1557476 1559423 := bstep (se 1 (by rfl) ⟨1169567, by rfl⟩ : syracuseStep 1559423 = 2339135) B2339135
theorem B3944639 : Blo 1557476 3944639 := bstep (se 1 (by rfl) ⟨2958479, by rfl⟩ : syracuseStep 3944639 = 5916959) B5916959
theorem B6656681 : Blo 1557476 6656681 := bstep (se 2 (by rfl) ⟨2496255, by rfl⟩ : syracuseStep 6656681 = 4992511) B4992511
theorem B3159017 : Blo 1557476 3159017 := bstep (se 2 (by rfl) ⟨1184631, by rfl⟩ : syracuseStep 3159017 = 2369263) B2369263
theorem B1753087 : Blo 1557476 1753087 := bstep (se 1 (by rfl) ⟨1314815, by rfl⟩ : syracuseStep 1753087 = 2629631) B2629631
theorem B2629759 : Blo 1557476 2629759 := bstep (se 1 (by rfl) ⟨1972319, by rfl⟩ : syracuseStep 2629759 = 3944639) B3944639
theorem B2106011 : Blo 1557476 2106011 := bstep (se 1 (by rfl) ⟨1579508, by rfl⟩ : syracuseStep 2106011 = 3159017) B3159017
theorem B10666991 : Blo 1557476 10666991 := bstep (se 1 (by rfl) ⟨8000243, by rfl⟩ : syracuseStep 10666991 = 16000487) B16000487
theorem B1557531 : Blo 1557476 1557531 := bstep (se 1 (by rfl) ⟨1168148, by rfl⟩ : syracuseStep 1557531 = 2336297) B2336297
theorem B2337449 : Blo 1557476 2337449 := bstep (se 2 (by rfl) ⟨876543, by rfl⟩ : syracuseStep 2337449 = 1753087) B1753087
theorem B2338031 : Blo 1557476 2338031 := bstep (se 1 (by rfl) ⟨1753523, by rfl⟩ : syracuseStep 2338031 = 3507047) B3507047
theorem B102460859 : Blo 1557476 102460859 := bstep (se 1 (by rfl) ⟨76845644, by rfl⟩ : syracuseStep 102460859 = 153691289) B153691289
theorem B34172765 : Blo 1557476 34172765 := bstep (se 3 (by rfl) ⟨6407393, by rfl⟩ : syracuseStep 34172765 = 12814787) B12814787
theorem B3945449 : Blo 1557476 3945449 := bstep (se 2 (by rfl) ⟨1479543, by rfl⟩ : syracuseStep 3945449 = 2959087) B2959087
theorem B17751149 : Blo 1557476 17751149 := bstep (se 3 (by rfl) ⟨3328340, by rfl⟩ : syracuseStep 17751149 = 6656681) B6656681
theorem B3506345 : Blo 1557476 3506345 := bstep (se 2 (by rfl) ⟨1314879, by rfl⟩ : syracuseStep 3506345 = 2629759) B2629759
theorem B2630299 : Blo 1557476 2630299 := bstep (se 1 (by rfl) ⟨1972724, by rfl⟩ : syracuseStep 2630299 = 3945449) B3945449
theorem B7111327 : Blo 1557476 7111327 := bstep (se 1 (by rfl) ⟨5333495, by rfl⟩ : syracuseStep 7111327 = 10666991) B10666991
theorem B1558299 : Blo 1557476 1558299 := bstep (se 1 (by rfl) ⟨1168724, by rfl⟩ : syracuseStep 1558299 = 2337449) B2337449
theorem B1558687 : Blo 1557476 1558687 := bstep (se 1 (by rfl) ⟨1169015, by rfl⟩ : syracuseStep 1558687 = 2338031) B2338031
theorem B68307239 : Blo 1557476 68307239 := bstep (se 1 (by rfl) ⟨51230429, by rfl⟩ : syracuseStep 68307239 = 102460859) B102460859
theorem B5616029 : Blo 1557476 5616029 := bstep (se 3 (by rfl) ⟨1053005, by rfl⟩ : syracuseStep 5616029 = 2106011) B2106011
theorem B11834099 : Blo 1557476 11834099 := bstep (se 1 (by rfl) ⟨8875574, by rfl⟩ : syracuseStep 11834099 = 17751149) B17751149
theorem B22781843 : Blo 1557476 22781843 := bstep (se 1 (by rfl) ⟨17086382, by rfl⟩ : syracuseStep 22781843 = 34172765) B34172765
theorem B3744019 : Blo 1557476 3744019 := bstep (se 1 (by rfl) ⟨2808014, by rfl⟩ : syracuseStep 3744019 = 5616029) B5616029
theorem B7889399 : Blo 1557476 7889399 := bstep (se 1 (by rfl) ⟨5917049, by rfl⟩ : syracuseStep 7889399 = 11834099) B11834099
theorem B3507065 : Blo 1557476 3507065 := bstep (se 2 (by rfl) ⟨1315149, by rfl⟩ : syracuseStep 3507065 = 2630299) B2630299
theorem B2337563 : Blo 1557476 2337563 := bstep (se 1 (by rfl) ⟨1753172, by rfl⟩ : syracuseStep 2337563 = 3506345) B3506345
theorem B9481769 : Blo 1557476 9481769 := bstep (se 2 (by rfl) ⟨3555663, by rfl⟩ : syracuseStep 9481769 = 7111327) B7111327
theorem B45538159 : Blo 1557476 45538159 := bstep (se 1 (by rfl) ⟨34153619, by rfl⟩ : syracuseStep 45538159 = 68307239) B68307239
theorem B15187895 : Blo 1557476 15187895 := bstep (se 1 (by rfl) ⟨11390921, by rfl⟩ : syracuseStep 15187895 = 22781843) B22781843
theorem B5259599 : Blo 1557476 5259599 := bstep (se 1 (by rfl) ⟨3944699, by rfl⟩ : syracuseStep 5259599 = 7889399) B7889399
theorem B1558375 : Blo 1557476 1558375 := bstep (se 1 (by rfl) ⟨1168781, by rfl⟩ : syracuseStep 1558375 = 2337563) B2337563
theorem B4992025 : Blo 1557476 4992025 := bstep (se 2 (by rfl) ⟨1872009, by rfl⟩ : syracuseStep 4992025 = 3744019) B3744019
theorem B2338043 : Blo 1557476 2338043 := bstep (se 1 (by rfl) ⟨1753532, by rfl⟩ : syracuseStep 2338043 = 3507065) B3507065
theorem B6321179 : Blo 1557476 6321179 := bstep (se 1 (by rfl) ⟨4740884, by rfl⟩ : syracuseStep 6321179 = 9481769) B9481769
theorem B60717545 : Blo 1557476 60717545 := bstep (se 2 (by rfl) ⟨22769079, by rfl⟩ : syracuseStep 60717545 = 45538159) B45538159
theorem B10125263 : Blo 1557476 10125263 := bstep (se 1 (by rfl) ⟨7593947, by rfl⟩ : syracuseStep 10125263 = 15187895) B15187895
theorem B3506399 : Blo 1557476 3506399 := bstep (se 1 (by rfl) ⟨2629799, by rfl⟩ : syracuseStep 3506399 = 5259599) B5259599
theorem B40478363 : Blo 1557476 40478363 := bstep (se 1 (by rfl) ⟨30358772, by rfl⟩ : syracuseStep 40478363 = 60717545) B60717545
theorem B1558695 : Blo 1557476 1558695 := bstep (se 1 (by rfl) ⟨1169021, by rfl⟩ : syracuseStep 1558695 = 2338043) B2338043
theorem B4214119 : Blo 1557476 4214119 := bstep (se 1 (by rfl) ⟨3160589, by rfl⟩ : syracuseStep 4214119 = 6321179) B6321179
theorem B6656033 : Blo 1557476 6656033 := bstep (se 2 (by rfl) ⟨2496012, by rfl⟩ : syracuseStep 6656033 = 4992025) B4992025
theorem B27000701 : Blo 1557476 27000701 := bstep (se 3 (by rfl) ⟨5062631, by rfl⟩ : syracuseStep 27000701 = 10125263) B10125263
theorem B26985575 : Blo 1557476 26985575 := bstep (se 1 (by rfl) ⟨20239181, by rfl⟩ : syracuseStep 26985575 = 40478363) B40478363
theorem B18000467 : Blo 1557476 18000467 := bstep (se 1 (by rfl) ⟨13500350, by rfl⟩ : syracuseStep 18000467 = 27000701) B27000701
theorem B2337599 : Blo 1557476 2337599 := bstep (se 1 (by rfl) ⟨1753199, by rfl⟩ : syracuseStep 2337599 = 3506399) B3506399
theorem B4437355 : Blo 1557476 4437355 := bstep (se 1 (by rfl) ⟨3328016, by rfl⟩ : syracuseStep 4437355 = 6656033) B6656033
theorem B5618825 : Blo 1557476 5618825 := bstep (se 2 (by rfl) ⟨2107059, by rfl⟩ : syracuseStep 5618825 = 4214119) B4214119
theorem B17990383 : Blo 1557476 17990383 := bstep (se 1 (by rfl) ⟨13492787, by rfl⟩ : syracuseStep 17990383 = 26985575) B26985575
theorem B5916473 : Blo 1557476 5916473 := bstep (se 2 (by rfl) ⟨2218677, by rfl⟩ : syracuseStep 5916473 = 4437355) B4437355
theorem B1558399 : Blo 1557476 1558399 := bstep (se 1 (by rfl) ⟨1168799, by rfl⟩ : syracuseStep 1558399 = 2337599) B2337599
theorem B3745883 : Blo 1557476 3745883 := bstep (se 1 (by rfl) ⟨2809412, by rfl⟩ : syracuseStep 3745883 = 5618825) B5618825
theorem B12000311 : Blo 1557476 12000311 := bstep (se 1 (by rfl) ⟨9000233, by rfl⟩ : syracuseStep 12000311 = 18000467) B18000467
theorem B23987177 : Blo 1557476 23987177 := bstep (se 2 (by rfl) ⟨8995191, by rfl⟩ : syracuseStep 23987177 = 17990383) B17990383
theorem B9989021 : Blo 1557476 9989021 := bstep (se 3 (by rfl) ⟨1872941, by rfl⟩ : syracuseStep 9989021 = 3745883) B3745883
theorem B3944315 : Blo 1557476 3944315 := bstep (se 1 (by rfl) ⟨2958236, by rfl⟩ : syracuseStep 3944315 = 5916473) B5916473
theorem B8000207 : Blo 1557476 8000207 := bstep (se 1 (by rfl) ⟨6000155, by rfl⟩ : syracuseStep 8000207 = 12000311) B12000311
theorem B5333471 : Blo 1557476 5333471 := bstep (se 1 (by rfl) ⟨4000103, by rfl⟩ : syracuseStep 5333471 = 8000207) B8000207
theorem B15991451 : Blo 1557476 15991451 := bstep (se 1 (by rfl) ⟨11993588, by rfl⟩ : syracuseStep 15991451 = 23987177) B23987177
theorem B6659347 : Blo 1557476 6659347 := bstep (se 1 (by rfl) ⟨4994510, by rfl⟩ : syracuseStep 6659347 = 9989021) B9989021
theorem B2629543 : Blo 1557476 2629543 := bstep (se 1 (by rfl) ⟨1972157, by rfl⟩ : syracuseStep 2629543 = 3944315) B3944315
theorem B3555647 : Blo 1557476 3555647 := bstep (se 1 (by rfl) ⟨2666735, by rfl⟩ : syracuseStep 3555647 = 5333471) B5333471
theorem B10660967 : Blo 1557476 10660967 := bstep (se 1 (by rfl) ⟨7995725, by rfl⟩ : syracuseStep 10660967 = 15991451) B15991451
theorem B8879129 : Blo 1557476 8879129 := bstep (se 2 (by rfl) ⟨3329673, by rfl⟩ : syracuseStep 8879129 = 6659347) B6659347
theorem B3506057 : Blo 1557476 3506057 := bstep (se 2 (by rfl) ⟨1314771, by rfl⟩ : syracuseStep 3506057 = 2629543) B2629543
theorem B2337371 : Blo 1557476 2337371 := bstep (se 1 (by rfl) ⟨1753028, by rfl⟩ : syracuseStep 2337371 = 3506057) B3506057
theorem B2370431 : Blo 1557476 2370431 := bstep (se 1 (by rfl) ⟨1777823, by rfl⟩ : syracuseStep 2370431 = 3555647) B3555647
theorem B5919419 : Blo 1557476 5919419 := bstep (se 1 (by rfl) ⟨4439564, by rfl⟩ : syracuseStep 5919419 = 8879129) B8879129
theorem B7107311 : Blo 1557476 7107311 := bstep (se 1 (by rfl) ⟨5330483, by rfl⟩ : syracuseStep 7107311 = 10660967) B10660967
theorem B1558247 : Blo 1557476 1558247 := bstep (se 1 (by rfl) ⟨1168685, by rfl⟩ : syracuseStep 1558247 = 2337371) B2337371
theorem B4738207 : Blo 1557476 4738207 := bstep (se 1 (by rfl) ⟨3553655, by rfl⟩ : syracuseStep 4738207 = 7107311) B7107311
theorem B6321149 : Blo 1557476 6321149 := bstep (se 3 (by rfl) ⟨1185215, by rfl⟩ : syracuseStep 6321149 = 2370431) B2370431
theorem B3946279 : Blo 1557476 3946279 := bstep (se 1 (by rfl) ⟨2959709, by rfl⟩ : syracuseStep 3946279 = 5919419) B5919419
theorem B6317609 : Blo 1557476 6317609 := bstep (se 2 (by rfl) ⟨2369103, by rfl⟩ : syracuseStep 6317609 = 4738207) B4738207
theorem B5261705 : Blo 1557476 5261705 := bstep (se 2 (by rfl) ⟨1973139, by rfl⟩ : syracuseStep 5261705 = 3946279) B3946279
theorem B4214099 : Blo 1557476 4214099 := bstep (se 1 (by rfl) ⟨3160574, by rfl⟩ : syracuseStep 4214099 = 6321149) B6321149
theorem B3507803 : Blo 1557476 3507803 := bstep (se 1 (by rfl) ⟨2630852, by rfl⟩ : syracuseStep 3507803 = 5261705) B5261705
theorem B16846957 : Blo 1557476 16846957 := bstep (se 3 (by rfl) ⟨3158804, by rfl⟩ : syracuseStep 16846957 = 6317609) B6317609
theorem B2809399 : Blo 1557476 2809399 := bstep (se 1 (by rfl) ⟨2107049, by rfl⟩ : syracuseStep 2809399 = 4214099) B4214099
theorem B22462609 : Blo 1557476 22462609 := bstep (se 2 (by rfl) ⟨8423478, by rfl⟩ : syracuseStep 22462609 = 16846957) B16846957
theorem B3745865 : Blo 1557476 3745865 := bstep (se 2 (by rfl) ⟨1404699, by rfl⟩ : syracuseStep 3745865 = 2809399) B2809399
theorem B2338535 : Blo 1557476 2338535 := bstep (se 1 (by rfl) ⟨1753901, by rfl⟩ : syracuseStep 2338535 = 3507803) B3507803
theorem B29950145 : Blo 1557476 29950145 := bstep (se 2 (by rfl) ⟨11231304, by rfl⟩ : syracuseStep 29950145 = 22462609) B22462609
theorem B1559023 : Blo 1557476 1559023 := bstep (se 1 (by rfl) ⟨1169267, by rfl⟩ : syracuseStep 1559023 = 2338535) B2338535
theorem B2497243 : Blo 1557476 2497243 := bstep (se 1 (by rfl) ⟨1872932, by rfl⟩ : syracuseStep 2497243 = 3745865) B3745865
theorem B19966763 : Blo 1557476 19966763 := bstep (se 1 (by rfl) ⟨14975072, by rfl⟩ : syracuseStep 19966763 = 29950145) B29950145
theorem B3329657 : Blo 1557476 3329657 := bstep (se 2 (by rfl) ⟨1248621, by rfl⟩ : syracuseStep 3329657 = 2497243) B2497243
theorem B13311175 : Blo 1557476 13311175 := bstep (se 1 (by rfl) ⟨9983381, by rfl⟩ : syracuseStep 13311175 = 19966763) B19966763
theorem B2219771 : Blo 1557476 2219771 := bstep (se 1 (by rfl) ⟨1664828, by rfl⟩ : syracuseStep 2219771 = 3329657) B3329657
theorem B17748233 : Blo 1557476 17748233 := bstep (se 2 (by rfl) ⟨6655587, by rfl⟩ : syracuseStep 17748233 = 13311175) B13311175
theorem B5919389 : Blo 1557476 5919389 := bstep (se 3 (by rfl) ⟨1109885, by rfl⟩ : syracuseStep 5919389 = 2219771) B2219771
theorem B11832155 : Blo 1557476 11832155 := bstep (se 1 (by rfl) ⟨8874116, by rfl⟩ : syracuseStep 11832155 = 17748233) B17748233
theorem B3946259 : Blo 1557476 3946259 := bstep (se 1 (by rfl) ⟨2959694, by rfl⟩ : syracuseStep 3946259 = 5919389) B5919389
theorem B2630839 : Blo 1557476 2630839 := bstep (se 1 (by rfl) ⟨1973129, by rfl⟩ : syracuseStep 2630839 = 3946259) B3946259
theorem B7888103 : Blo 1557476 7888103 := bstep (se 1 (by rfl) ⟨5916077, by rfl⟩ : syracuseStep 7888103 = 11832155) B11832155
theorem B3507785 : Blo 1557476 3507785 := bstep (se 2 (by rfl) ⟨1315419, by rfl⟩ : syracuseStep 3507785 = 2630839) B2630839
theorem B5258735 : Blo 1557476 5258735 := bstep (se 1 (by rfl) ⟨3944051, by rfl⟩ : syracuseStep 5258735 = 7888103) B7888103
theorem B2338523 : Blo 1557476 2338523 := bstep (se 1 (by rfl) ⟨1753892, by rfl⟩ : syracuseStep 2338523 = 3507785) B3507785
theorem B3505823 : Blo 1557476 3505823 := bstep (se 1 (by rfl) ⟨2629367, by rfl⟩ : syracuseStep 3505823 = 5258735) B5258735
theorem B2337215 : Blo 1557476 2337215 := bstep (se 1 (by rfl) ⟨1752911, by rfl⟩ : syracuseStep 2337215 = 3505823) B3505823
theorem B1559015 : Blo 1557476 1559015 := bstep (se 1 (by rfl) ⟨1169261, by rfl⟩ : syracuseStep 1559015 = 2338523) B2338523
theorem B1558143 : Blo 1557476 1558143 := bstep (se 1 (by rfl) ⟨1168607, by rfl⟩ : syracuseStep 1558143 = 2337215) B2337215

theorem C0 (j : ℕ) (h1 : 389369 ≤ j) (h2 : j ≤ 389868) : Blo 1557476 (4 * j + 3) := by
  interval_cases j
  · exact B1557479
  · exact B1557483
  · exact B1557487
  · exact B1557491
  · exact B1557495
  · exact B1557499
  · exact B1557503
  · exact B1557507
  · exact B1557511
  · exact B1557515
  · exact B1557519
  · exact B1557523
  · exact B1557527
  · exact B1557531
  · exact B1557535
  · exact B1557539
  · exact B1557543
  · exact B1557547
  · exact B1557551
  · exact B1557555
  · exact B1557559
  · exact B1557563
  · exact B1557567
  · exact B1557571
  · exact B1557575
  · exact B1557579
  · exact B1557583
  · exact B1557587
  · exact B1557591
  · exact B1557595
  · exact B1557599
  · exact B1557603
  · exact B1557607
  · exact B1557611
  · exact B1557615
  · exact B1557619
  · exact B1557623
  · exact B1557627
  · exact B1557631
  · exact B1557635
  · exact B1557639
  · exact B1557643
  · exact B1557647
  · exact B1557651
  · exact B1557655
  · exact B1557659
  · exact B1557663
  · exact B1557667
  · exact B1557671
  · exact B1557675
  · exact B1557679
  · exact B1557683
  · exact B1557687
  · exact B1557691
  · exact B1557695
  · exact B1557699
  · exact B1557703
  · exact B1557707
  · exact B1557711
  · exact B1557715
  · exact B1557719
  · exact B1557723
  · exact B1557727
  · exact B1557731
  · exact B1557735
  · exact B1557739
  · exact B1557743
  · exact B1557747
  · exact B1557751
  · exact B1557755
  · exact B1557759
  · exact B1557763
  · exact B1557767
  · exact B1557771
  · exact B1557775
  · exact B1557779
  · exact B1557783
  · exact B1557787
  · exact B1557791
  · exact B1557795
  · exact B1557799
  · exact B1557803
  · exact B1557807
  · exact B1557811
  · exact B1557815
  · exact B1557819
  · exact B1557823
  · exact B1557827
  · exact B1557831
  · exact B1557835
  · exact B1557839
  · exact B1557843
  · exact B1557847
  · exact B1557851
  · exact B1557855
  · exact B1557859
  · exact B1557863
  · exact B1557867
  · exact B1557871
  · exact B1557875
  · exact B1557879
  · exact B1557883
  · exact B1557887
  · exact B1557891
  · exact B1557895
  · exact B1557899
  · exact B1557903
  · exact B1557907
  · exact B1557911
  · exact B1557915
  · exact B1557919
  · exact B1557923
  · exact B1557927
  · exact B1557931
  · exact B1557935
  · exact B1557939
  · exact B1557943
  · exact B1557947
  · exact B1557951
  · exact B1557955
  · exact B1557959
  · exact B1557963
  · exact B1557967
  · exact B1557971
  · exact B1557975
  · exact B1557979
  · exact B1557983
  · exact B1557987
  · exact B1557991
  · exact B1557995
  · exact B1557999
  · exact B1558003
  · exact B1558007
  · exact B1558011
  · exact B1558015
  · exact B1558019
  · exact B1558023
  · exact B1558027
  · exact B1558031
  · exact B1558035
  · exact B1558039
  · exact B1558043
  · exact B1558047
  · exact B1558051
  · exact B1558055
  · exact B1558059
  · exact B1558063
  · exact B1558067
  · exact B1558071
  · exact B1558075
  · exact B1558079
  · exact B1558083
  · exact B1558087
  · exact B1558091
  · exact B1558095
  · exact B1558099
  · exact B1558103
  · exact B1558107
  · exact B1558111
  · exact B1558115
  · exact B1558119
  · exact B1558123
  · exact B1558127
  · exact B1558131
  · exact B1558135
  · exact B1558139
  · exact B1558143
  · exact B1558147
  · exact B1558151
  · exact B1558155
  · exact B1558159
  · exact B1558163
  · exact B1558167
  · exact B1558171
  · exact B1558175
  · exact B1558179
  · exact B1558183
  · exact B1558187
  · exact B1558191
  · exact B1558195
  · exact B1558199
  · exact B1558203
  · exact B1558207
  · exact B1558211
  · exact B1558215
  · exact B1558219
  · exact B1558223
  · exact B1558227
  · exact B1558231
  · exact B1558235
  · exact B1558239
  · exact B1558243
  · exact B1558247
  · exact B1558251
  · exact B1558255
  · exact B1558259
  · exact B1558263
  · exact B1558267
  · exact B1558271
  · exact B1558275
  · exact B1558279
  · exact B1558283
  · exact B1558287
  · exact B1558291
  · exact B1558295
  · exact B1558299
  · exact B1558303
  · exact B1558307
  · exact B1558311
  · exact B1558315
  · exact B1558319
  · exact B1558323
  · exact B1558327
  · exact B1558331
  · exact B1558335
  · exact B1558339
  · exact B1558343
  · exact B1558347
  · exact B1558351
  · exact B1558355
  · exact B1558359
  · exact B1558363
  · exact B1558367
  · exact B1558371
  · exact B1558375
  · exact B1558379
  · exact B1558383
  · exact B1558387
  · exact B1558391
  · exact B1558395
  · exact B1558399
  · exact B1558403
  · exact B1558407
  · exact B1558411
  · exact B1558415
  · exact B1558419
  · exact B1558423
  · exact B1558427
  · exact B1558431
  · exact B1558435
  · exact B1558439
  · exact B1558443
  · exact B1558447
  · exact B1558451
  · exact B1558455
  · exact B1558459
  · exact B1558463
  · exact B1558467
  · exact B1558471
  · exact B1558475
  · exact B1558479
  · exact B1558483
  · exact B1558487
  · exact B1558491
  · exact B1558495
  · exact B1558499
  · exact B1558503
  · exact B1558507
  · exact B1558511
  · exact B1558515
  · exact B1558519
  · exact B1558523
  · exact B1558527
  · exact B1558531
  · exact B1558535
  · exact B1558539
  · exact B1558543
  · exact B1558547
  · exact B1558551
  · exact B1558555
  · exact B1558559
  · exact B1558563
  · exact B1558567
  · exact B1558571
  · exact B1558575
  · exact B1558579
  · exact B1558583
  · exact B1558587
  · exact B1558591
  · exact B1558595
  · exact B1558599
  · exact B1558603
  · exact B1558607
  · exact B1558611
  · exact B1558615
  · exact B1558619
  · exact B1558623
  · exact B1558627
  · exact B1558631
  · exact B1558635
  · exact B1558639
  · exact B1558643
  · exact B1558647
  · exact B1558651
  · exact B1558655
  · exact B1558659
  · exact B1558663
  · exact B1558667
  · exact B1558671
  · exact B1558675
  · exact B1558679
  · exact B1558683
  · exact B1558687
  · exact B1558691
  · exact B1558695
  · exact B1558699
  · exact B1558703
  · exact B1558707
  · exact B1558711
  · exact B1558715
  · exact B1558719
  · exact B1558723
  · exact B1558727
  · exact B1558731
  · exact B1558735
  · exact B1558739
  · exact B1558743
  · exact B1558747
  · exact B1558751
  · exact B1558755
  · exact B1558759
  · exact B1558763
  · exact B1558767
  · exact B1558771
  · exact B1558775
  · exact B1558779
  · exact B1558783
  · exact B1558787
  · exact B1558791
  · exact B1558795
  · exact B1558799
  · exact B1558803
  · exact B1558807
  · exact B1558811
  · exact B1558815
  · exact B1558819
  · exact B1558823
  · exact B1558827
  · exact B1558831
  · exact B1558835
  · exact B1558839
  · exact B1558843
  · exact B1558847
  · exact B1558851
  · exact B1558855
  · exact B1558859
  · exact B1558863
  · exact B1558867
  · exact B1558871
  · exact B1558875
  · exact B1558879
  · exact B1558883
  · exact B1558887
  · exact B1558891
  · exact B1558895
  · exact B1558899
  · exact B1558903
  · exact B1558907
  · exact B1558911
  · exact B1558915
  · exact B1558919
  · exact B1558923
  · exact B1558927
  · exact B1558931
  · exact B1558935
  · exact B1558939
  · exact B1558943
  · exact B1558947
  · exact B1558951
  · exact B1558955
  · exact B1558959
  · exact B1558963
  · exact B1558967
  · exact B1558971
  · exact B1558975
  · exact B1558979
  · exact B1558983
  · exact B1558987
  · exact B1558991
  · exact B1558995
  · exact B1558999
  · exact B1559003
  · exact B1559007
  · exact B1559011
  · exact B1559015
  · exact B1559019
  · exact B1559023
  · exact B1559027
  · exact B1559031
  · exact B1559035
  · exact B1559039
  · exact B1559043
  · exact B1559047
  · exact B1559051
  · exact B1559055
  · exact B1559059
  · exact B1559063
  · exact B1559067
  · exact B1559071
  · exact B1559075
  · exact B1559079
  · exact B1559083
  · exact B1559087
  · exact B1559091
  · exact B1559095
  · exact B1559099
  · exact B1559103
  · exact B1559107
  · exact B1559111
  · exact B1559115
  · exact B1559119
  · exact B1559123
  · exact B1559127
  · exact B1559131
  · exact B1559135
  · exact B1559139
  · exact B1559143
  · exact B1559147
  · exact B1559151
  · exact B1559155
  · exact B1559159
  · exact B1559163
  · exact B1559167
  · exact B1559171
  · exact B1559175
  · exact B1559179
  · exact B1559183
  · exact B1559187
  · exact B1559191
  · exact B1559195
  · exact B1559199
  · exact B1559203
  · exact B1559207
  · exact B1559211
  · exact B1559215
  · exact B1559219
  · exact B1559223
  · exact B1559227
  · exact B1559231
  · exact B1559235
  · exact B1559239
  · exact B1559243
  · exact B1559247
  · exact B1559251
  · exact B1559255
  · exact B1559259
  · exact B1559263
  · exact B1559267
  · exact B1559271
  · exact B1559275
  · exact B1559279
  · exact B1559283
  · exact B1559287
  · exact B1559291
  · exact B1559295
  · exact B1559299
  · exact B1559303
  · exact B1559307
  · exact B1559311
  · exact B1559315
  · exact B1559319
  · exact B1559323
  · exact B1559327
  · exact B1559331
  · exact B1559335
  · exact B1559339
  · exact B1559343
  · exact B1559347
  · exact B1559351
  · exact B1559355
  · exact B1559359
  · exact B1559363
  · exact B1559367
  · exact B1559371
  · exact B1559375
  · exact B1559379
  · exact B1559383
  · exact B1559387
  · exact B1559391
  · exact B1559395
  · exact B1559399
  · exact B1559403
  · exact B1559407
  · exact B1559411
  · exact B1559415
  · exact B1559419
  · exact B1559423
  · exact B1559427
  · exact B1559431
  · exact B1559435
  · exact B1559439
  · exact B1559443
  · exact B1559447
  · exact B1559451
  · exact B1559455
  · exact B1559459
  · exact B1559463
  · exact B1559467
  · exact B1559471
  · exact B1559475

theorem solution (m : ℕ) (hlo : 1557476 ≤ m) (hhi : m ≤ 1559476) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 389369 ≤ j := by omega
    have hj2 : j ≤ 389868 := by omega
    have hb : Blo 1557476 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
