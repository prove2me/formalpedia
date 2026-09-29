-- Prove2me | solution 1 for syracuse_descends_range_1634016_1636016
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:15:02.100499+00:00
-- url     : https://prove2.me/submissions/79b517da-565e-4120-a4d3-cefca94a33c0

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


theorem B2760709 : Blo 1634016 2760709 := bbase (se 4 (by rfl) ⟨258816, by rfl⟩ : syracuseStep 2760709 = 517633) (by norm_num)
theorem B3678245 : Blo 1634016 3678245 := bbase (se 4 (by rfl) ⟨344835, by rfl⟩ : syracuseStep 3678245 = 689671) (by norm_num)
theorem B5521445 : Blo 1634016 5521445 := bbase (se 4 (by rfl) ⟨517635, by rfl⟩ : syracuseStep 5521445 = 1035271) (by norm_num)
theorem B1744949 : Blo 1634016 1744949 := bbase (se 5 (by rfl) ⟨81794, by rfl⟩ : syracuseStep 1744949 = 163589) (by norm_num)
theorem B3678317 : Blo 1634016 3678317 := bbase (se 3 (by rfl) ⟨689684, by rfl⟩ : syracuseStep 3678317 = 1379369) (by norm_num)
theorem B1745021 : Blo 1634016 1745021 := bbase (se 3 (by rfl) ⟨327191, by rfl⟩ : syracuseStep 1745021 = 654383) (by norm_num)
theorem B3678389 : Blo 1634016 3678389 := bbase (se 5 (by rfl) ⟨172424, by rfl⟩ : syracuseStep 3678389 = 344849) (by norm_num)
theorem B10625237 : Blo 1634016 10625237 := bbase (se 7 (by rfl) ⟨124514, by rfl⟩ : syracuseStep 10625237 = 249029) (by norm_num)
theorem B8274149 : Blo 1634016 8274149 := bbase (se 4 (by rfl) ⟨775701, by rfl⟩ : syracuseStep 8274149 = 1551403) (by norm_num)
theorem B3678461 : Blo 1634016 3678461 := bbase (se 3 (by rfl) ⟨689711, by rfl⟩ : syracuseStep 3678461 = 1379423) (by norm_num)
theorem B2359589 : Blo 1634016 2359589 := bbase (se 4 (by rfl) ⟨221211, by rfl⟩ : syracuseStep 2359589 = 442423) (by norm_num)
theorem B1745209 : Blo 1634016 1745209 := bbase (se 2 (by rfl) ⟨654453, by rfl⟩ : syracuseStep 1745209 = 1308907) (by norm_num)
theorem B4137277 : Blo 1634016 4137277 := bbase (se 3 (by rfl) ⟨775739, by rfl⟩ : syracuseStep 4137277 = 1551479) (by norm_num)
theorem B3678533 : Blo 1634016 3678533 := bbase (se 4 (by rfl) ⟨344862, by rfl⟩ : syracuseStep 3678533 = 689725) (by norm_num)
theorem B37749077 : Blo 1634016 37749077 := bbase (se 10 (by rfl) ⟨55296, by rfl⟩ : syracuseStep 37749077 = 110593) (by norm_num)
theorem B4653413 : Blo 1634016 4653413 := bbase (se 4 (by rfl) ⟨436257, by rfl⟩ : syracuseStep 4653413 = 872515) (by norm_num)
theorem B6988133 : Blo 1634016 6988133 := bbase (se 4 (by rfl) ⟨655137, by rfl⟩ : syracuseStep 6988133 = 1310275) (by norm_num)
theorem B3678605 : Blo 1634016 3678605 := bbase (se 3 (by rfl) ⟨689738, by rfl⟩ : syracuseStep 3678605 = 1379477) (by norm_num)
theorem B25174421 : Blo 1634016 25174421 := bbase (se 6 (by rfl) ⟨590025, by rfl⟩ : syracuseStep 25174421 = 1180051) (by norm_num)
theorem B4137389 : Blo 1634016 4137389 := bbase (se 3 (by rfl) ⟨775760, by rfl⟩ : syracuseStep 4137389 = 1551521) (by norm_num)
theorem B3105229 : Blo 1634016 3105229 := bbase (se 3 (by rfl) ⟨582230, by rfl⟩ : syracuseStep 3105229 = 1164461) (by norm_num)
theorem B3678677 : Blo 1634016 3678677 := bbase (se 7 (by rfl) ⟨43109, by rfl⟩ : syracuseStep 3678677 = 86219) (by norm_num)
theorem B1745393 : Blo 1634016 1745393 := bbase (se 2 (by rfl) ⟨654522, by rfl⟩ : syracuseStep 1745393 = 1309045) (by norm_num)
theorem B3727901 : Blo 1634016 3727901 := bbase (se 3 (by rfl) ⟨698981, by rfl⟩ : syracuseStep 3727901 = 1397963) (by norm_num)
theorem B3678749 : Blo 1634016 3678749 := bbase (se 3 (by rfl) ⟨689765, by rfl⟩ : syracuseStep 3678749 = 1379531) (by norm_num)
theorem B5972549 : Blo 1634016 5972549 := bbase (se 4 (by rfl) ⟨559926, by rfl⟩ : syracuseStep 5972549 = 1119853) (by norm_num)
theorem B3105373 : Blo 1634016 3105373 := bbase (se 3 (by rfl) ⟨582257, by rfl⟩ : syracuseStep 3105373 = 1164515) (by norm_num)
theorem B3678821 : Blo 1634016 3678821 := bbase (se 4 (by rfl) ⟨344889, by rfl⟩ : syracuseStep 3678821 = 689779) (by norm_num)
theorem B4137581 : Blo 1634016 4137581 := bbase (se 3 (by rfl) ⟨775796, by rfl⟩ : syracuseStep 4137581 = 1551593) (by norm_num)
theorem B3490445 : Blo 1634016 3490445 := bbase (se 3 (by rfl) ⟨654458, by rfl⟩ : syracuseStep 3490445 = 1308917) (by norm_num)
theorem B3981973 : Blo 1634016 3981973 := bbase (se 6 (by rfl) ⟨93327, by rfl⟩ : syracuseStep 3981973 = 186655) (by norm_num)
theorem B3678893 : Blo 1634016 3678893 := bbase (se 3 (by rfl) ⟨689792, by rfl⟩ : syracuseStep 3678893 = 1379585) (by norm_num)
theorem B6210229 : Blo 1634016 6210229 := bbase (se 5 (by rfl) ⟨291104, by rfl⟩ : syracuseStep 6210229 = 582209) (by norm_num)
theorem B3678965 : Blo 1634016 3678965 := bbase (se 5 (by rfl) ⟨172451, by rfl⟩ : syracuseStep 3678965 = 344903) (by norm_num)
theorem B3105533 : Blo 1634016 3105533 := bbase (se 3 (by rfl) ⟨582287, by rfl⟩ : syracuseStep 3105533 = 1164575) (by norm_num)
theorem B6980357 : Blo 1634016 6980357 := bbase (se 4 (by rfl) ⟨654408, by rfl⟩ : syracuseStep 6980357 = 1308817) (by norm_num)
theorem B4653845 : Blo 1634016 4653845 := bbase (se 6 (by rfl) ⟨109074, by rfl⟩ : syracuseStep 4653845 = 218149) (by norm_num)
theorem B3490589 : Blo 1634016 3490589 := bbase (se 3 (by rfl) ⟨654485, by rfl⟩ : syracuseStep 3490589 = 1308971) (by norm_num)
theorem B3679037 : Blo 1634016 3679037 := bbase (se 3 (by rfl) ⟨689819, by rfl⟩ : syracuseStep 3679037 = 1379639) (by norm_num)
theorem B3679109 : Blo 1634016 3679109 := bbase (se 4 (by rfl) ⟨344916, by rfl⟩ : syracuseStep 3679109 = 689833) (by norm_num)
theorem B3105677 : Blo 1634016 3105677 := bbase (se 3 (by rfl) ⟨582314, by rfl⟩ : syracuseStep 3105677 = 1164629) (by norm_num)
theorem B4137925 : Blo 1634016 4137925 := bbase (se 4 (by rfl) ⟨387930, by rfl⟩ : syracuseStep 4137925 = 775861) (by norm_num)
theorem B3679181 : Blo 1634016 3679181 := bbase (se 3 (by rfl) ⟨689846, by rfl⟩ : syracuseStep 3679181 = 1379693) (by norm_num)
theorem B31859669 : Blo 1634016 31859669 := bbase (se 7 (by rfl) ⟨373355, by rfl⟩ : syracuseStep 31859669 = 746711) (by norm_num)
theorem B6210533 : Blo 1634016 6210533 := bbase (se 4 (by rfl) ⟨582237, by rfl⟩ : syracuseStep 6210533 = 1164475) (by norm_num)
theorem B2270197 : Blo 1634016 2270197 := bbase (se 5 (by rfl) ⟨106415, by rfl⟩ : syracuseStep 2270197 = 212831) (by norm_num)
theorem B3679253 : Blo 1634016 3679253 := bbase (se 6 (by rfl) ⟨86232, by rfl⟩ : syracuseStep 3679253 = 172465) (by norm_num)
theorem B11789333 : Blo 1634016 11789333 := bbase (se 6 (by rfl) ⟨276312, by rfl⟩ : syracuseStep 11789333 = 552625) (by norm_num)
theorem B4138037 : Blo 1634016 4138037 := bbase (se 5 (by rfl) ⟨193970, by rfl⟩ : syracuseStep 4138037 = 387941) (by norm_num)
theorem B5235781 : Blo 1634016 5235781 := bbase (se 4 (by rfl) ⟨490854, by rfl⟩ : syracuseStep 5235781 = 981709) (by norm_num)
theorem B2327629 : Blo 1634016 2327629 := bbase (se 3 (by rfl) ⟨436430, by rfl⟩ : syracuseStep 2327629 = 872861) (by norm_num)
theorem B3679325 : Blo 1634016 3679325 := bbase (se 3 (by rfl) ⟨689873, by rfl⟩ : syracuseStep 3679325 = 1379747) (by norm_num)
theorem B3728485 : Blo 1634016 3728485 := bbase (se 4 (by rfl) ⟨349545, by rfl⟩ : syracuseStep 3728485 = 699091) (by norm_num)
theorem B5891237 : Blo 1634016 5891237 := bbase (se 4 (by rfl) ⟨552303, by rfl⟩ : syracuseStep 5891237 = 1104607) (by norm_num)
theorem B3679397 : Blo 1634016 3679397 := bbase (se 4 (by rfl) ⟨344943, by rfl⟩ : syracuseStep 3679397 = 689887) (by norm_num)
theorem B1746145 : Blo 1634016 1746145 := bbase (se 2 (by rfl) ⟨654804, by rfl⟩ : syracuseStep 1746145 = 1309609) (by norm_num)
theorem B3679469 : Blo 1634016 3679469 := bbase (se 3 (by rfl) ⟨689900, by rfl⟩ : syracuseStep 3679469 = 1379801) (by norm_num)
theorem B4138229 : Blo 1634016 4138229 := bbase (se 5 (by rfl) ⟨193979, by rfl⟩ : syracuseStep 4138229 = 387959) (by norm_num)
theorem B2360605 : Blo 1634016 2360605 := bbase (se 3 (by rfl) ⟨442613, by rfl⟩ : syracuseStep 2360605 = 885227) (by norm_num)
theorem B1746217 : Blo 1634016 1746217 := bbase (se 2 (by rfl) ⟨654831, by rfl⟩ : syracuseStep 1746217 = 1309663) (by norm_num)
theorem B3679541 : Blo 1634016 3679541 := bbase (se 5 (by rfl) ⟨172478, by rfl⟩ : syracuseStep 3679541 = 344957) (by norm_num)
theorem B1680733 : Blo 1634016 1680733 := bbase (se 3 (by rfl) ⟨315137, by rfl⟩ : syracuseStep 1680733 = 630275) (by norm_num)
theorem B4416869 : Blo 1634016 4416869 := bbase (se 4 (by rfl) ⟨414081, by rfl⟩ : syracuseStep 4416869 = 828163) (by norm_num)
theorem B3679613 : Blo 1634016 3679613 := bbase (se 3 (by rfl) ⟨689927, by rfl⟩ : syracuseStep 3679613 = 1379855) (by norm_num)
theorem B7857557 : Blo 1634016 7857557 := bbase (se 6 (by rfl) ⟨184161, by rfl⟩ : syracuseStep 7857557 = 368323) (by norm_num)
theorem B3728813 : Blo 1634016 3728813 := bbase (se 3 (by rfl) ⟨699152, by rfl⟩ : syracuseStep 3728813 = 1398305) (by norm_num)
theorem B3679685 : Blo 1634016 3679685 := bbase (se 4 (by rfl) ⟨344970, by rfl⟩ : syracuseStep 3679685 = 689941) (by norm_num)
theorem B1746397 : Blo 1634016 1746397 := bbase (se 3 (by rfl) ⟨327449, by rfl⟩ : syracuseStep 1746397 = 654899) (by norm_num)
theorem B8275445 : Blo 1634016 8275445 := bbase (se 5 (by rfl) ⟨387911, by rfl⟩ : syracuseStep 8275445 = 775823) (by norm_num)
theorem B4654597 : Blo 1634016 4654597 := bbase (se 4 (by rfl) ⟨436368, by rfl⟩ : syracuseStep 4654597 = 872737) (by norm_num)
theorem B3491333 : Blo 1634016 3491333 := bbase (se 4 (by rfl) ⟨327312, by rfl⟩ : syracuseStep 3491333 = 654625) (by norm_num)
theorem B3679757 : Blo 1634016 3679757 := bbase (se 3 (by rfl) ⟨689954, by rfl⟩ : syracuseStep 3679757 = 1379909) (by norm_num)
theorem B4195901 : Blo 1634016 4195901 := bbase (se 3 (by rfl) ⟨786731, by rfl⟩ : syracuseStep 4195901 = 1573463) (by norm_num)
theorem B4138573 : Blo 1634016 4138573 := bbase (se 3 (by rfl) ⟨775982, by rfl⟩ : syracuseStep 4138573 = 1551965) (by norm_num)
theorem B2451029 : Blo 1634016 2451029 := bbase (se 8 (by rfl) ⟨14361, by rfl⟩ : syracuseStep 2451029 = 28723) (by norm_num)
theorem B3679829 : Blo 1634016 3679829 := bbase (se 8 (by rfl) ⟨21561, by rfl⟩ : syracuseStep 3679829 = 43123) (by norm_num)
theorem B2451053 : Blo 1634016 2451053 := bbase (se 3 (by rfl) ⟨459572, by rfl⟩ : syracuseStep 2451053 = 919145) (by norm_num)
theorem B2451077 : Blo 1634016 2451077 := bbase (se 4 (by rfl) ⟨229788, by rfl⟩ : syracuseStep 2451077 = 459577) (by norm_num)
theorem B2451101 : Blo 1634016 2451101 := bbase (se 3 (by rfl) ⟨459581, by rfl⟩ : syracuseStep 2451101 = 919163) (by norm_num)
theorem B2328221 : Blo 1634016 2328221 := bbase (se 3 (by rfl) ⟨436541, by rfl⟩ : syracuseStep 2328221 = 873083) (by norm_num)
theorem B3679901 : Blo 1634016 3679901 := bbase (se 3 (by rfl) ⟨689981, by rfl⟩ : syracuseStep 3679901 = 1379963) (by norm_num)
theorem B2451125 : Blo 1634016 2451125 := bbase (se 5 (by rfl) ⟨114896, by rfl⟩ : syracuseStep 2451125 = 229793) (by norm_num)
theorem B4138685 : Blo 1634016 4138685 := bbase (se 3 (by rfl) ⟨776003, by rfl⟩ : syracuseStep 4138685 = 1552007) (by norm_num)
theorem B2451149 : Blo 1634016 2451149 := bbase (se 3 (by rfl) ⟨459590, by rfl⟩ : syracuseStep 2451149 = 919181) (by norm_num)
theorem B5514965 : Blo 1634016 5514965 := bbase (se 7 (by rfl) ⟨64628, by rfl⟩ : syracuseStep 5514965 = 129257) (by norm_num)
theorem B8840917 : Blo 1634016 8840917 := bbase (se 7 (by rfl) ⟨103604, by rfl⟩ : syracuseStep 8840917 = 207209) (by norm_num)
theorem B2451173 : Blo 1634016 2451173 := bbase (se 4 (by rfl) ⟨229797, by rfl⟩ : syracuseStep 2451173 = 459595) (by norm_num)
theorem B2795237 : Blo 1634016 2795237 := bbase (se 4 (by rfl) ⟨262053, by rfl⟩ : syracuseStep 2795237 = 524107) (by norm_num)
theorem B6981349 : Blo 1634016 6981349 := bbase (se 4 (by rfl) ⟨654501, by rfl⟩ : syracuseStep 6981349 = 1309003) (by norm_num)
theorem B3679973 : Blo 1634016 3679973 := bbase (se 4 (by rfl) ⟨344997, by rfl⟩ : syracuseStep 3679973 = 689995) (by norm_num)
theorem B2328301 : Blo 1634016 2328301 := bbase (se 3 (by rfl) ⟨436556, by rfl⟩ : syracuseStep 2328301 = 873113) (by norm_num)
theorem B2451197 : Blo 1634016 2451197 := bbase (se 3 (by rfl) ⟨459599, by rfl⟩ : syracuseStep 2451197 = 919199) (by norm_num)
theorem B8390405 : Blo 1634016 8390405 := bbase (se 4 (by rfl) ⟨786600, by rfl⟩ : syracuseStep 8390405 = 1573201) (by norm_num)
theorem B2017045 : Blo 1634016 2017045 := bbase (se 6 (by rfl) ⟨47274, by rfl⟩ : syracuseStep 2017045 = 94549) (by norm_num)
theorem B2451221 : Blo 1634016 2451221 := bbase (se 6 (by rfl) ⟨57450, by rfl⟩ : syracuseStep 2451221 = 114901) (by norm_num)
theorem B15722261 : Blo 1634016 15722261 := bbase (se 6 (by rfl) ⟨368490, by rfl⟩ : syracuseStep 15722261 = 736981) (by norm_num)
theorem B2451245 : Blo 1634016 2451245 := bbase (se 3 (by rfl) ⟨459608, by rfl⟩ : syracuseStep 2451245 = 919217) (by norm_num)
theorem B3680045 : Blo 1634016 3680045 := bbase (se 3 (by rfl) ⟨690008, by rfl⟩ : syracuseStep 3680045 = 1380017) (by norm_num)
theorem B2451269 : Blo 1634016 2451269 := bbase (se 4 (by rfl) ⟨229806, by rfl⟩ : syracuseStep 2451269 = 459613) (by norm_num)
theorem B2451293 : Blo 1634016 2451293 := bbase (se 3 (by rfl) ⟨459617, by rfl⟩ : syracuseStep 2451293 = 919235) (by norm_num)
theorem B2328421 : Blo 1634016 2328421 := bbase (se 4 (by rfl) ⟨218289, by rfl⟩ : syracuseStep 2328421 = 436579) (by norm_num)
theorem B2451317 : Blo 1634016 2451317 := bbase (se 5 (by rfl) ⟨114905, by rfl⟩ : syracuseStep 2451317 = 229811) (by norm_num)
theorem B3680117 : Blo 1634016 3680117 := bbase (se 5 (by rfl) ⟨172505, by rfl⟩ : syracuseStep 3680117 = 345011) (by norm_num)
theorem B4138877 : Blo 1634016 4138877 := bbase (se 3 (by rfl) ⟨776039, by rfl⟩ : syracuseStep 4138877 = 1552079) (by norm_num)
theorem B2451341 : Blo 1634016 2451341 := bbase (se 3 (by rfl) ⟨459626, by rfl⟩ : syracuseStep 2451341 = 919253) (by norm_num)
theorem B1746841 : Blo 1634016 1746841 := bbase (se 2 (by rfl) ⟨655065, by rfl⟩ : syracuseStep 1746841 = 1310131) (by norm_num)
theorem B2451365 : Blo 1634016 2451365 := bbase (se 4 (by rfl) ⟨229815, by rfl⟩ : syracuseStep 2451365 = 459631) (by norm_num)
theorem B2451389 : Blo 1634016 2451389 := bbase (se 3 (by rfl) ⟨459635, by rfl⟩ : syracuseStep 2451389 = 919271) (by norm_num)
theorem B3680189 : Blo 1634016 3680189 := bbase (se 3 (by rfl) ⟨690035, by rfl⟩ : syracuseStep 3680189 = 1380071) (by norm_num)
theorem B2328517 : Blo 1634016 2328517 := bbase (se 4 (by rfl) ⟨218298, by rfl⟩ : syracuseStep 2328517 = 436597) (by norm_num)
theorem B2451413 : Blo 1634016 2451413 := bbase (se 7 (by rfl) ⟨28727, by rfl⟩ : syracuseStep 2451413 = 57455) (by norm_num)
theorem B2451437 : Blo 1634016 2451437 := bbase (se 3 (by rfl) ⟨459644, by rfl⟩ : syracuseStep 2451437 = 919289) (by norm_num)
theorem B2451461 : Blo 1634016 2451461 := bbase (se 4 (by rfl) ⟨229824, by rfl⟩ : syracuseStep 2451461 = 459649) (by norm_num)
theorem B5892101 : Blo 1634016 5892101 := bbase (se 4 (by rfl) ⟨552384, by rfl⟩ : syracuseStep 5892101 = 1104769) (by norm_num)
theorem B3680261 : Blo 1634016 3680261 := bbase (se 4 (by rfl) ⟨345024, by rfl⟩ : syracuseStep 3680261 = 690049) (by norm_num)
theorem B1746965 : Blo 1634016 1746965 := bbase (se 6 (by rfl) ⟨40944, by rfl⟩ : syracuseStep 1746965 = 81889) (by norm_num)
theorem B2451485 : Blo 1634016 2451485 := bbase (se 3 (by rfl) ⟨459653, by rfl⟩ : syracuseStep 2451485 = 919307) (by norm_num)
theorem B2451509 : Blo 1634016 2451509 := bbase (se 5 (by rfl) ⟨114914, by rfl⟩ : syracuseStep 2451509 = 229829) (by norm_num)
theorem B2451533 : Blo 1634016 2451533 := bbase (se 3 (by rfl) ⟨459662, by rfl⟩ : syracuseStep 2451533 = 919325) (by norm_num)
theorem B3680333 : Blo 1634016 3680333 := bbase (se 3 (by rfl) ⟨690062, by rfl⟩ : syracuseStep 3680333 = 1380125) (by norm_num)
theorem B2451557 : Blo 1634016 2451557 := bbase (se 4 (by rfl) ⟨229833, by rfl⟩ : syracuseStep 2451557 = 459667) (by norm_num)
theorem B2451581 : Blo 1634016 2451581 := bbase (se 3 (by rfl) ⟨459671, by rfl⟩ : syracuseStep 2451581 = 919343) (by norm_num)
theorem B5515397 : Blo 1634016 5515397 := bbase (se 4 (by rfl) ⟨517068, by rfl⟩ : syracuseStep 5515397 = 1034137) (by norm_num)
theorem B2451605 : Blo 1634016 2451605 := bbase (se 6 (by rfl) ⟨57459, by rfl⟩ : syracuseStep 2451605 = 114919) (by norm_num)
theorem B3680405 : Blo 1634016 3680405 := bbase (se 6 (by rfl) ⟨86259, by rfl⟩ : syracuseStep 3680405 = 172519) (by norm_num)
theorem B2451629 : Blo 1634016 2451629 := bbase (se 3 (by rfl) ⟨459680, by rfl⟩ : syracuseStep 2451629 = 919361) (by norm_num)
theorem B2451653 : Blo 1634016 2451653 := bbase (se 4 (by rfl) ⟨229842, by rfl⟩ : syracuseStep 2451653 = 459685) (by norm_num)
theorem B3147973 : Blo 1634016 3147973 := bbase (se 4 (by rfl) ⟨295122, by rfl⟩ : syracuseStep 3147973 = 590245) (by norm_num)
theorem B4139221 : Blo 1634016 4139221 := bbase (se 7 (by rfl) ⟨48506, by rfl⟩ : syracuseStep 4139221 = 97013) (by norm_num)
theorem B2451677 : Blo 1634016 2451677 := bbase (se 3 (by rfl) ⟨459689, by rfl⟩ : syracuseStep 2451677 = 919379) (by norm_num)
theorem B3680477 : Blo 1634016 3680477 := bbase (se 3 (by rfl) ⟨690089, by rfl⟩ : syracuseStep 3680477 = 1380179) (by norm_num)
theorem B2451701 : Blo 1634016 2451701 := bbase (se 5 (by rfl) ⟨114923, by rfl⟩ : syracuseStep 2451701 = 229847) (by norm_num)
theorem B3492085 : Blo 1634016 3492085 := bbase (se 5 (by rfl) ⟨163691, by rfl⟩ : syracuseStep 3492085 = 327383) (by norm_num)
theorem B2451725 : Blo 1634016 2451725 := bbase (se 3 (by rfl) ⟨459698, by rfl⟩ : syracuseStep 2451725 = 919397) (by norm_num)
theorem B3541261 : Blo 1634016 3541261 := bbase (se 3 (by rfl) ⟨663986, by rfl⟩ : syracuseStep 3541261 = 1327973) (by norm_num)
theorem B2451749 : Blo 1634016 2451749 := bbase (se 4 (by rfl) ⟨229851, by rfl⟩ : syracuseStep 2451749 = 459703) (by norm_num)
theorem B5892389 : Blo 1634016 5892389 := bbase (se 4 (by rfl) ⟨552411, by rfl⟩ : syracuseStep 5892389 = 1104823) (by norm_num)
theorem B3680549 : Blo 1634016 3680549 := bbase (se 4 (by rfl) ⟨345051, by rfl⟩ : syracuseStep 3680549 = 690103) (by norm_num)
theorem B2451773 : Blo 1634016 2451773 := bbase (se 3 (by rfl) ⟨459707, by rfl⟩ : syracuseStep 2451773 = 919415) (by norm_num)
theorem B4139333 : Blo 1634016 4139333 := bbase (se 4 (by rfl) ⟨388062, by rfl⟩ : syracuseStep 4139333 = 776125) (by norm_num)
theorem B2451797 : Blo 1634016 2451797 := bbase (se 10 (by rfl) ⟨3591, by rfl⟩ : syracuseStep 2451797 = 7183) (by norm_num)
theorem B2451821 : Blo 1634016 2451821 := bbase (se 3 (by rfl) ⟨459716, by rfl⟩ : syracuseStep 2451821 = 919433) (by norm_num)
theorem B3680621 : Blo 1634016 3680621 := bbase (se 3 (by rfl) ⟨690116, by rfl⟩ : syracuseStep 3680621 = 1380233) (by norm_num)
theorem B3148157 : Blo 1634016 3148157 := bbase (se 3 (by rfl) ⟨590279, by rfl⟩ : syracuseStep 3148157 = 1180559) (by norm_num)
theorem B2451845 : Blo 1634016 2451845 := bbase (se 4 (by rfl) ⟨229860, by rfl⟩ : syracuseStep 2451845 = 459721) (by norm_num)
theorem B3492229 : Blo 1634016 3492229 := bbase (se 4 (by rfl) ⟨327396, by rfl⟩ : syracuseStep 3492229 = 654793) (by norm_num)
theorem B2451869 : Blo 1634016 2451869 := bbase (se 3 (by rfl) ⟨459725, by rfl⟩ : syracuseStep 2451869 = 919451) (by norm_num)
theorem B2451893 : Blo 1634016 2451893 := bbase (se 5 (by rfl) ⟨114932, by rfl⟩ : syracuseStep 2451893 = 229865) (by norm_num)
theorem B2329013 : Blo 1634016 2329013 := bbase (se 5 (by rfl) ⟨109172, by rfl⟩ : syracuseStep 2329013 = 218345) (by norm_num)
theorem B3680693 : Blo 1634016 3680693 := bbase (se 5 (by rfl) ⟨172532, by rfl⟩ : syracuseStep 3680693 = 345065) (by norm_num)
theorem B2484685 : Blo 1634016 2484685 := bbase (se 3 (by rfl) ⟨465878, by rfl⟩ : syracuseStep 2484685 = 931757) (by norm_num)
theorem B2451917 : Blo 1634016 2451917 := bbase (se 3 (by rfl) ⟨459734, by rfl⟩ : syracuseStep 2451917 = 919469) (by norm_num)
theorem B2451941 : Blo 1634016 2451941 := bbase (se 4 (by rfl) ⟨229869, by rfl⟩ : syracuseStep 2451941 = 459739) (by norm_num)
theorem B3729901 : Blo 1634016 3729901 := bbase (se 3 (by rfl) ⟨699356, by rfl⟩ : syracuseStep 3729901 = 1398713) (by norm_num)
theorem B2451965 : Blo 1634016 2451965 := bbase (se 3 (by rfl) ⟨459743, by rfl⟩ : syracuseStep 2451965 = 919487) (by norm_num)
theorem B3680765 : Blo 1634016 3680765 := bbase (se 3 (by rfl) ⟨690143, by rfl⟩ : syracuseStep 3680765 = 1380287) (by norm_num)
theorem B4139525 : Blo 1634016 4139525 := bbase (se 4 (by rfl) ⟨388080, by rfl⟩ : syracuseStep 4139525 = 776161) (by norm_num)
theorem B2484757 : Blo 1634016 2484757 := bbase (se 6 (by rfl) ⟨58236, by rfl⟩ : syracuseStep 2484757 = 116473) (by norm_num)
theorem B3926549 : Blo 1634016 3926549 := bbase (se 6 (by rfl) ⟨92028, by rfl⟩ : syracuseStep 3926549 = 184057) (by norm_num)
theorem B2451989 : Blo 1634016 2451989 := bbase (se 6 (by rfl) ⟨57468, by rfl⟩ : syracuseStep 2451989 = 114937) (by norm_num)
theorem B2452013 : Blo 1634016 2452013 := bbase (se 3 (by rfl) ⟨459752, by rfl⟩ : syracuseStep 2452013 = 919505) (by norm_num)
theorem B5515829 : Blo 1634016 5515829 := bbase (se 5 (by rfl) ⟨258554, by rfl⟩ : syracuseStep 5515829 = 517109) (by norm_num)
theorem B2452037 : Blo 1634016 2452037 := bbase (se 4 (by rfl) ⟨229878, by rfl⟩ : syracuseStep 2452037 = 459757) (by norm_num)
theorem B3680837 : Blo 1634016 3680837 := bbase (se 4 (by rfl) ⟨345078, by rfl⟩ : syracuseStep 3680837 = 690157) (by norm_num)
theorem B3926605 : Blo 1634016 3926605 := bbase (se 3 (by rfl) ⟨736238, by rfl⟩ : syracuseStep 3926605 = 1472477) (by norm_num)
theorem B2452061 : Blo 1634016 2452061 := bbase (se 3 (by rfl) ⟨459761, by rfl⟩ : syracuseStep 2452061 = 919523) (by norm_num)
theorem B2452085 : Blo 1634016 2452085 := bbase (se 5 (by rfl) ⟨114941, by rfl⟩ : syracuseStep 2452085 = 229883) (by norm_num)
theorem B2452109 : Blo 1634016 2452109 := bbase (se 3 (by rfl) ⟨459770, by rfl⟩ : syracuseStep 2452109 = 919541) (by norm_num)
theorem B3680909 : Blo 1634016 3680909 := bbase (se 3 (by rfl) ⟨690170, by rfl⟩ : syracuseStep 3680909 = 1380341) (by norm_num)
theorem B2452133 : Blo 1634016 2452133 := bbase (se 4 (by rfl) ⟨229887, by rfl⟩ : syracuseStep 2452133 = 459775) (by norm_num)
theorem B2452157 : Blo 1634016 2452157 := bbase (se 3 (by rfl) ⟨459779, by rfl⟩ : syracuseStep 2452157 = 919559) (by norm_num)
theorem B2452181 : Blo 1634016 2452181 := bbase (se 7 (by rfl) ⟨28736, by rfl⟩ : syracuseStep 2452181 = 57473) (by norm_num)
theorem B5892821 : Blo 1634016 5892821 := bbase (se 7 (by rfl) ⟨69056, by rfl⟩ : syracuseStep 5892821 = 138113) (by norm_num)
theorem B3680981 : Blo 1634016 3680981 := bbase (se 7 (by rfl) ⟨43136, by rfl⟩ : syracuseStep 3680981 = 86273) (by norm_num)
theorem B2452205 : Blo 1634016 2452205 := bbase (se 3 (by rfl) ⟨459788, by rfl⟩ : syracuseStep 2452205 = 919577) (by norm_num)
theorem B3492605 : Blo 1634016 3492605 := bbase (se 3 (by rfl) ⟨654863, by rfl⟩ : syracuseStep 3492605 = 1309727) (by norm_num)
theorem B2452229 : Blo 1634016 2452229 := bbase (se 4 (by rfl) ⟨229896, by rfl⟩ : syracuseStep 2452229 = 459793) (by norm_num)
theorem B8276741 : Blo 1634016 8276741 := bbase (se 4 (by rfl) ⟨775944, by rfl⟩ : syracuseStep 8276741 = 1551889) (by norm_num)
theorem B2485013 : Blo 1634016 2485013 := bbase (se 6 (by rfl) ⟨58242, by rfl⟩ : syracuseStep 2485013 = 116485) (by norm_num)
theorem B4721429 : Blo 1634016 4721429 := bbase (se 6 (by rfl) ⟨110658, by rfl⟩ : syracuseStep 4721429 = 221317) (by norm_num)
theorem B2452253 : Blo 1634016 2452253 := bbase (se 3 (by rfl) ⟨459797, by rfl⟩ : syracuseStep 2452253 = 919595) (by norm_num)
theorem B2452277 : Blo 1634016 2452277 := bbase (se 5 (by rfl) ⟨114950, by rfl⟩ : syracuseStep 2452277 = 229901) (by norm_num)
theorem B2452301 : Blo 1634016 2452301 := bbase (se 3 (by rfl) ⟨459806, by rfl⟩ : syracuseStep 2452301 = 919613) (by norm_num)
theorem B4139869 : Blo 1634016 4139869 := bbase (se 3 (by rfl) ⟨776225, by rfl⟩ : syracuseStep 4139869 = 1552451) (by norm_num)
theorem B2452325 : Blo 1634016 2452325 := bbase (se 4 (by rfl) ⟨229905, by rfl⟩ : syracuseStep 2452325 = 459811) (by norm_num)
theorem B2452349 : Blo 1634016 2452349 := bbase (se 3 (by rfl) ⟨459815, by rfl⟩ : syracuseStep 2452349 = 919631) (by norm_num)
theorem B2452373 : Blo 1634016 2452373 := bbase (se 6 (by rfl) ⟨57477, by rfl⟩ : syracuseStep 2452373 = 114955) (by norm_num)
theorem B2452397 : Blo 1634016 2452397 := bbase (se 3 (by rfl) ⟨459824, by rfl⟩ : syracuseStep 2452397 = 919649) (by norm_num)
theorem B3926981 : Blo 1634016 3926981 := bbase (se 4 (by rfl) ⟨368154, by rfl⟩ : syracuseStep 3926981 = 736309) (by norm_num)
theorem B2452421 : Blo 1634016 2452421 := bbase (se 4 (by rfl) ⟨229914, by rfl⟩ : syracuseStep 2452421 = 459829) (by norm_num)
theorem B4139981 : Blo 1634016 4139981 := bbase (se 3 (by rfl) ⟨776246, by rfl⟩ : syracuseStep 4139981 = 1552493) (by norm_num)
theorem B2452445 : Blo 1634016 2452445 := bbase (se 3 (by rfl) ⟨459833, by rfl⟩ : syracuseStep 2452445 = 919667) (by norm_num)
theorem B5516261 : Blo 1634016 5516261 := bbase (se 4 (by rfl) ⟨517149, by rfl⟩ : syracuseStep 5516261 = 1034299) (by norm_num)
theorem B2452469 : Blo 1634016 2452469 := bbase (se 5 (by rfl) ⟨114959, by rfl⟩ : syracuseStep 2452469 = 229919) (by norm_num)
theorem B2452493 : Blo 1634016 2452493 := bbase (se 3 (by rfl) ⟨459842, by rfl⟩ : syracuseStep 2452493 = 919685) (by norm_num)
theorem B2452517 : Blo 1634016 2452517 := bbase (se 4 (by rfl) ⟨229923, by rfl⟩ : syracuseStep 2452517 = 459847) (by norm_num)
theorem B2452541 : Blo 1634016 2452541 := bbase (se 3 (by rfl) ⟨459851, by rfl⟩ : syracuseStep 2452541 = 919703) (by norm_num)
theorem B2452565 : Blo 1634016 2452565 := bbase (se 8 (by rfl) ⟨14370, by rfl⟩ : syracuseStep 2452565 = 28741) (by norm_num)
theorem B2452589 : Blo 1634016 2452589 := bbase (se 3 (by rfl) ⟨459860, by rfl⟩ : syracuseStep 2452589 = 919721) (by norm_num)
theorem B3492973 : Blo 1634016 3492973 := bbase (se 3 (by rfl) ⟨654932, by rfl⟩ : syracuseStep 3492973 = 1309865) (by norm_num)
theorem B2452613 : Blo 1634016 2452613 := bbase (se 4 (by rfl) ⟨229932, by rfl⟩ : syracuseStep 2452613 = 459865) (by norm_num)
theorem B4140173 : Blo 1634016 4140173 := bbase (se 3 (by rfl) ⟨776282, by rfl⟩ : syracuseStep 4140173 = 1552565) (by norm_num)
theorem B2452637 : Blo 1634016 2452637 := bbase (se 3 (by rfl) ⟨459869, by rfl⟩ : syracuseStep 2452637 = 919739) (by norm_num)
theorem B3927221 : Blo 1634016 3927221 := bbase (se 5 (by rfl) ⟨184088, by rfl⟩ : syracuseStep 3927221 = 368177) (by norm_num)
theorem B2452661 : Blo 1634016 2452661 := bbase (se 5 (by rfl) ⟨114968, by rfl⟩ : syracuseStep 2452661 = 229937) (by norm_num)
theorem B7081141 : Blo 1634016 7081141 := bbase (se 5 (by rfl) ⟨331928, by rfl⟩ : syracuseStep 7081141 = 663857) (by norm_num)
theorem B1838281 : Blo 1634016 1838281 := bbase (se 2 (by rfl) ⟨689355, by rfl⟩ : syracuseStep 1838281 = 1378711) (by norm_num)
theorem B2452685 : Blo 1634016 2452685 := bbase (se 3 (by rfl) ⟨459878, by rfl⟩ : syracuseStep 2452685 = 919757) (by norm_num)
theorem B2452709 : Blo 1634016 2452709 := bbase (se 4 (by rfl) ⟨229941, by rfl⟩ : syracuseStep 2452709 = 459883) (by norm_num)
theorem B1838317 : Blo 1634016 1838317 := bbase (se 3 (by rfl) ⟨344684, by rfl⟩ : syracuseStep 1838317 = 689369) (by norm_num)
theorem B2452733 : Blo 1634016 2452733 := bbase (se 3 (by rfl) ⟨459887, by rfl⟩ : syracuseStep 2452733 = 919775) (by norm_num)
theorem B1838353 : Blo 1634016 1838353 := bbase (se 2 (by rfl) ⟨689382, by rfl⟩ : syracuseStep 1838353 = 1378765) (by norm_num)
theorem B2452757 : Blo 1634016 2452757 := bbase (se 6 (by rfl) ⟨57486, by rfl⟩ : syracuseStep 2452757 = 114973) (by norm_num)
theorem B2452781 : Blo 1634016 2452781 := bbase (se 3 (by rfl) ⟨459896, by rfl⟩ : syracuseStep 2452781 = 919793) (by norm_num)
theorem B1838389 : Blo 1634016 1838389 := bbase (se 5 (by rfl) ⟨86174, by rfl⟩ : syracuseStep 1838389 = 172349) (by norm_num)
theorem B2452805 : Blo 1634016 2452805 := bbase (se 4 (by rfl) ⟨229950, by rfl⟩ : syracuseStep 2452805 = 459901) (by norm_num)
theorem B1838425 : Blo 1634016 1838425 := bbase (se 2 (by rfl) ⟨689409, by rfl⟩ : syracuseStep 1838425 = 1378819) (by norm_num)
theorem B2452829 : Blo 1634016 2452829 := bbase (se 3 (by rfl) ⟨459905, by rfl⟩ : syracuseStep 2452829 = 919811) (by norm_num)
theorem B2452853 : Blo 1634016 2452853 := bbase (se 5 (by rfl) ⟨114977, by rfl⟩ : syracuseStep 2452853 = 229955) (by norm_num)
theorem B1838461 : Blo 1634016 1838461 := bbase (se 3 (by rfl) ⟨344711, by rfl⟩ : syracuseStep 1838461 = 689423) (by norm_num)
theorem B2452877 : Blo 1634016 2452877 := bbase (se 3 (by rfl) ⟨459914, by rfl⟩ : syracuseStep 2452877 = 919829) (by norm_num)
theorem B5516693 : Blo 1634016 5516693 := bbase (se 6 (by rfl) ⟨129297, by rfl⟩ : syracuseStep 5516693 = 258595) (by norm_num)
theorem B1838497 : Blo 1634016 1838497 := bbase (se 2 (by rfl) ⟨689436, by rfl⟩ : syracuseStep 1838497 = 1378873) (by norm_num)
theorem B2452901 : Blo 1634016 2452901 := bbase (se 4 (by rfl) ⟨229959, by rfl⟩ : syracuseStep 2452901 = 459919) (by norm_num)
theorem B2452925 : Blo 1634016 2452925 := bbase (se 3 (by rfl) ⟨459923, by rfl⟩ : syracuseStep 2452925 = 919847) (by norm_num)
theorem B6204869 : Blo 1634016 6204869 := bbase (se 4 (by rfl) ⟨581706, by rfl⟩ : syracuseStep 6204869 = 1163413) (by norm_num)
theorem B1838533 : Blo 1634016 1838533 := bbase (se 4 (by rfl) ⟨172362, by rfl⟩ : syracuseStep 1838533 = 344725) (by norm_num)
theorem B2452949 : Blo 1634016 2452949 := bbase (se 7 (by rfl) ⟨28745, by rfl⟩ : syracuseStep 2452949 = 57491) (by norm_num)
theorem B4140517 : Blo 1634016 4140517 := bbase (se 4 (by rfl) ⟨388173, by rfl⟩ : syracuseStep 4140517 = 776347) (by norm_num)
theorem B1838569 : Blo 1634016 1838569 := bbase (se 2 (by rfl) ⟨689463, by rfl⟩ : syracuseStep 1838569 = 1378927) (by norm_num)
theorem B2452973 : Blo 1634016 2452973 := bbase (se 3 (by rfl) ⟨459932, by rfl⟩ : syracuseStep 2452973 = 919865) (by norm_num)
theorem B12422645 : Blo 1634016 12422645 := bbase (se 5 (by rfl) ⟨582311, by rfl⟩ : syracuseStep 12422645 = 1164623) (by norm_num)
theorem B2452997 : Blo 1634016 2452997 := bbase (se 4 (by rfl) ⟨229968, by rfl⟩ : syracuseStep 2452997 = 459937) (by norm_num)
theorem B1838605 : Blo 1634016 1838605 := bbase (se 3 (by rfl) ⟨344738, by rfl⟩ : syracuseStep 1838605 = 689477) (by norm_num)
theorem B2453021 : Blo 1634016 2453021 := bbase (se 3 (by rfl) ⟨459941, by rfl⟩ : syracuseStep 2453021 = 919883) (by norm_num)
theorem B1838641 : Blo 1634016 1838641 := bbase (se 2 (by rfl) ⟨689490, by rfl⟩ : syracuseStep 1838641 = 1378981) (by norm_num)
theorem B2453045 : Blo 1634016 2453045 := bbase (se 5 (by rfl) ⟨114986, by rfl⟩ : syracuseStep 2453045 = 229973) (by norm_num)
theorem B2453069 : Blo 1634016 2453069 := bbase (se 3 (by rfl) ⟨459950, by rfl⟩ : syracuseStep 2453069 = 919901) (by norm_num)
theorem B1838677 : Blo 1634016 1838677 := bbase (se 8 (by rfl) ⟨10773, by rfl⟩ : syracuseStep 1838677 = 21547) (by norm_num)
theorem B4140629 : Blo 1634016 4140629 := bbase (se 8 (by rfl) ⟨24261, by rfl⟩ : syracuseStep 4140629 = 48523) (by norm_num)
theorem B2453093 : Blo 1634016 2453093 := bbase (se 4 (by rfl) ⟨229977, by rfl⟩ : syracuseStep 2453093 = 459955) (by norm_num)
theorem B3313261 : Blo 1634016 3313261 := bbase (se 3 (by rfl) ⟨621236, by rfl⟩ : syracuseStep 3313261 = 1242473) (by norm_num)
theorem B1838713 : Blo 1634016 1838713 := bbase (se 2 (by rfl) ⟨689517, by rfl⟩ : syracuseStep 1838713 = 1379035) (by norm_num)
theorem B2453117 : Blo 1634016 2453117 := bbase (se 3 (by rfl) ⟨459959, by rfl⟩ : syracuseStep 2453117 = 919919) (by norm_num)
theorem B13962901 : Blo 1634016 13962901 := bbase (se 6 (by rfl) ⟨327255, by rfl⟩ : syracuseStep 13962901 = 654511) (by norm_num)
theorem B2453141 : Blo 1634016 2453141 := bbase (se 6 (by rfl) ⟨57495, by rfl⟩ : syracuseStep 2453141 = 114991) (by norm_num)
theorem B1838749 : Blo 1634016 1838749 := bbase (se 3 (by rfl) ⟨344765, by rfl⟩ : syracuseStep 1838749 = 689531) (by norm_num)
theorem B2240165 : Blo 1634016 2240165 := bbase (se 4 (by rfl) ⟨210015, by rfl⟩ : syracuseStep 2240165 = 420031) (by norm_num)
theorem B2453165 : Blo 1634016 2453165 := bbase (se 3 (by rfl) ⟨459968, by rfl⟩ : syracuseStep 2453165 = 919937) (by norm_num)
theorem B1838785 : Blo 1634016 1838785 := bbase (se 2 (by rfl) ⟨689544, by rfl⟩ : syracuseStep 1838785 = 1379089) (by norm_num)
theorem B2453189 : Blo 1634016 2453189 := bbase (se 4 (by rfl) ⟨229986, by rfl⟩ : syracuseStep 2453189 = 459973) (by norm_num)
theorem B2453213 : Blo 1634016 2453213 := bbase (se 3 (by rfl) ⟨459977, by rfl⟩ : syracuseStep 2453213 = 919955) (by norm_num)
theorem B2068193 : Blo 1634016 2068193 := bbase (se 2 (by rfl) ⟨775572, by rfl⟩ : syracuseStep 2068193 = 1551145) (by norm_num)
theorem B6205157 : Blo 1634016 6205157 := bbase (se 4 (by rfl) ⟨581733, by rfl⟩ : syracuseStep 6205157 = 1163467) (by norm_num)
theorem B1838821 : Blo 1634016 1838821 := bbase (se 4 (by rfl) ⟨172389, by rfl⟩ : syracuseStep 1838821 = 344779) (by norm_num)
theorem B2453237 : Blo 1634016 2453237 := bbase (se 5 (by rfl) ⟨114995, by rfl⟩ : syracuseStep 2453237 = 229991) (by norm_num)
theorem B1838857 : Blo 1634016 1838857 := bbase (se 2 (by rfl) ⟨689571, by rfl⟩ : syracuseStep 1838857 = 1379143) (by norm_num)
theorem B2453261 : Blo 1634016 2453261 := bbase (se 3 (by rfl) ⟨459986, by rfl⟩ : syracuseStep 2453261 = 919973) (by norm_num)
theorem B4140821 : Blo 1634016 4140821 := bbase (se 6 (by rfl) ⟨97050, by rfl⟩ : syracuseStep 4140821 = 194101) (by norm_num)
theorem B2068249 : Blo 1634016 2068249 := bbase (se 2 (by rfl) ⟨775593, by rfl⟩ : syracuseStep 2068249 = 1551187) (by norm_num)
theorem B2453285 : Blo 1634016 2453285 := bbase (se 4 (by rfl) ⟨229995, by rfl⟩ : syracuseStep 2453285 = 459991) (by norm_num)
theorem B1838893 : Blo 1634016 1838893 := bbase (se 3 (by rfl) ⟨344792, by rfl⟩ : syracuseStep 1838893 = 689585) (by norm_num)
theorem B2453309 : Blo 1634016 2453309 := bbase (se 3 (by rfl) ⟨459995, by rfl⟩ : syracuseStep 2453309 = 919991) (by norm_num)
theorem B5517125 : Blo 1634016 5517125 := bbase (se 4 (by rfl) ⟨517230, by rfl⟩ : syracuseStep 5517125 = 1034461) (by norm_num)
theorem B1838929 : Blo 1634016 1838929 := bbase (se 2 (by rfl) ⟨689598, by rfl⟩ : syracuseStep 1838929 = 1379197) (by norm_num)
theorem B2453333 : Blo 1634016 2453333 := bbase (se 9 (by rfl) ⟨7187, by rfl⟩ : syracuseStep 2453333 = 14375) (by norm_num)
theorem B2453357 : Blo 1634016 2453357 := bbase (se 3 (by rfl) ⟨460004, by rfl⟩ : syracuseStep 2453357 = 920009) (by norm_num)
theorem B1838965 : Blo 1634016 1838965 := bbase (se 5 (by rfl) ⟨86201, by rfl⟩ : syracuseStep 1838965 = 172403) (by norm_num)
theorem B2068345 : Blo 1634016 2068345 := bbase (se 2 (by rfl) ⟨775629, by rfl⟩ : syracuseStep 2068345 = 1551259) (by norm_num)
theorem B2453381 : Blo 1634016 2453381 := bbase (se 4 (by rfl) ⟨230004, by rfl⟩ : syracuseStep 2453381 = 460009) (by norm_num)
theorem B12414869 : Blo 1634016 12414869 := bbase (se 6 (by rfl) ⟨290973, by rfl⟩ : syracuseStep 12414869 = 581947) (by norm_num)
theorem B1839001 : Blo 1634016 1839001 := bbase (se 2 (by rfl) ⟨689625, by rfl⟩ : syracuseStep 1839001 = 1379251) (by norm_num)
theorem B2453405 : Blo 1634016 2453405 := bbase (se 3 (by rfl) ⟨460013, by rfl⟩ : syracuseStep 2453405 = 920027) (by norm_num)
theorem B2453429 : Blo 1634016 2453429 := bbase (se 5 (by rfl) ⟨115004, by rfl⟩ : syracuseStep 2453429 = 230009) (by norm_num)
theorem B1839037 : Blo 1634016 1839037 := bbase (se 3 (by rfl) ⟨344819, by rfl⟩ : syracuseStep 1839037 = 689639) (by norm_num)
theorem B2453453 : Blo 1634016 2453453 := bbase (se 3 (by rfl) ⟨460022, by rfl⟩ : syracuseStep 2453453 = 920045) (by norm_num)
theorem B1839073 : Blo 1634016 1839073 := bbase (se 2 (by rfl) ⟨689652, by rfl⟩ : syracuseStep 1839073 = 1379305) (by norm_num)
theorem B2797541 : Blo 1634016 2797541 := bbase (se 4 (by rfl) ⟨262269, by rfl⟩ : syracuseStep 2797541 = 524539) (by norm_num)
theorem B4542437 : Blo 1634016 4542437 := bbase (se 4 (by rfl) ⟨425853, by rfl⟩ : syracuseStep 4542437 = 851707) (by norm_num)
theorem B2453477 : Blo 1634016 2453477 := bbase (se 4 (by rfl) ⟨230013, by rfl⟩ : syracuseStep 2453477 = 460027) (by norm_num)
theorem B10473461 : Blo 1634016 10473461 := bbase (se 5 (by rfl) ⟨490943, by rfl⟩ : syracuseStep 10473461 = 981887) (by norm_num)
theorem B2453501 : Blo 1634016 2453501 := bbase (se 3 (by rfl) ⟨460031, by rfl⟩ : syracuseStep 2453501 = 920063) (by norm_num)
theorem B1839109 : Blo 1634016 1839109 := bbase (se 4 (by rfl) ⟨172416, by rfl⟩ : syracuseStep 1839109 = 344833) (by norm_num)
theorem B8278037 : Blo 1634016 8278037 := bbase (se 6 (by rfl) ⟨194016, by rfl⟩ : syracuseStep 8278037 = 388033) (by norm_num)
theorem B2453525 : Blo 1634016 2453525 := bbase (se 6 (by rfl) ⟨57504, by rfl⟩ : syracuseStep 2453525 = 115009) (by norm_num)
theorem B2068517 : Blo 1634016 2068517 := bbase (se 4 (by rfl) ⟨193923, by rfl⟩ : syracuseStep 2068517 = 387847) (by norm_num)
theorem B1839145 : Blo 1634016 1839145 := bbase (se 2 (by rfl) ⟨689679, by rfl⟩ : syracuseStep 1839145 = 1379359) (by norm_num)
theorem B2453549 : Blo 1634016 2453549 := bbase (se 3 (by rfl) ⟨460040, by rfl⟩ : syracuseStep 2453549 = 920081) (by norm_num)
theorem B2453573 : Blo 1634016 2453573 := bbase (se 4 (by rfl) ⟨230022, by rfl⟩ : syracuseStep 2453573 = 460045) (by norm_num)
theorem B1839181 : Blo 1634016 1839181 := bbase (se 3 (by rfl) ⟨344846, by rfl⟩ : syracuseStep 1839181 = 689693) (by norm_num)
theorem B2986069 : Blo 1634016 2986069 := bbase (se 8 (by rfl) ⟨17496, by rfl⟩ : syracuseStep 2986069 = 34993) (by norm_num)
theorem B2068573 : Blo 1634016 2068573 := bbase (se 3 (by rfl) ⟨387857, by rfl⟩ : syracuseStep 2068573 = 775715) (by norm_num)
theorem B2453597 : Blo 1634016 2453597 := bbase (se 3 (by rfl) ⟨460049, by rfl⟩ : syracuseStep 2453597 = 920099) (by norm_num)
theorem B4141165 : Blo 1634016 4141165 := bbase (se 3 (by rfl) ⟨776468, by rfl⟩ : syracuseStep 4141165 = 1552937) (by norm_num)
theorem B1839217 : Blo 1634016 1839217 := bbase (se 2 (by rfl) ⟨689706, by rfl⟩ : syracuseStep 1839217 = 1379413) (by norm_num)
theorem B2453621 : Blo 1634016 2453621 := bbase (se 5 (by rfl) ⟨115013, by rfl⟩ : syracuseStep 2453621 = 230027) (by norm_num)
theorem B1863805 : Blo 1634016 1863805 := bbase (se 3 (by rfl) ⟨349463, by rfl⟩ : syracuseStep 1863805 = 698927) (by norm_num)
theorem B2453645 : Blo 1634016 2453645 := bbase (se 3 (by rfl) ⟨460058, by rfl⟩ : syracuseStep 2453645 = 920117) (by norm_num)
theorem B1839253 : Blo 1634016 1839253 := bbase (se 6 (by rfl) ⟨43107, by rfl⟩ : syracuseStep 1839253 = 86215) (by norm_num)
theorem B2453669 : Blo 1634016 2453669 := bbase (se 4 (by rfl) ⟨230031, by rfl⟩ : syracuseStep 2453669 = 460063) (by norm_num)
theorem B1839289 : Blo 1634016 1839289 := bbase (se 2 (by rfl) ⟨689733, by rfl⟩ : syracuseStep 1839289 = 1379467) (by norm_num)
theorem B1863869 : Blo 1634016 1863869 := bbase (se 3 (by rfl) ⟨349475, by rfl⟩ : syracuseStep 1863869 = 698951) (by norm_num)
theorem B2068669 : Blo 1634016 2068669 := bbase (se 3 (by rfl) ⟨387875, by rfl⟩ : syracuseStep 2068669 = 775751) (by norm_num)
theorem B2453693 : Blo 1634016 2453693 := bbase (se 3 (by rfl) ⟨460067, by rfl⟩ : syracuseStep 2453693 = 920135) (by norm_num)
theorem B2453717 : Blo 1634016 2453717 := bbase (se 7 (by rfl) ⟨28754, by rfl⟩ : syracuseStep 2453717 = 57509) (by norm_num)
theorem B1839325 : Blo 1634016 1839325 := bbase (se 3 (by rfl) ⟨344873, by rfl⟩ : syracuseStep 1839325 = 689747) (by norm_num)
theorem B2453741 : Blo 1634016 2453741 := bbase (se 3 (by rfl) ⟨460076, by rfl⟩ : syracuseStep 2453741 = 920153) (by norm_num)
theorem B5517557 : Blo 1634016 5517557 := bbase (se 5 (by rfl) ⟨258635, by rfl⟩ : syracuseStep 5517557 = 517271) (by norm_num)
theorem B1839361 : Blo 1634016 1839361 := bbase (se 2 (by rfl) ⟨689760, by rfl⟩ : syracuseStep 1839361 = 1379521) (by norm_num)
theorem B2453765 : Blo 1634016 2453765 := bbase (se 4 (by rfl) ⟨230040, by rfl⟩ : syracuseStep 2453765 = 460081) (by norm_num)
theorem B1863965 : Blo 1634016 1863965 := bbase (se 3 (by rfl) ⟨349493, by rfl⟩ : syracuseStep 1863965 = 698987) (by norm_num)
theorem B2453789 : Blo 1634016 2453789 := bbase (se 3 (by rfl) ⟨460085, by rfl⟩ : syracuseStep 2453789 = 920171) (by norm_num)
theorem B1839397 : Blo 1634016 1839397 := bbase (se 4 (by rfl) ⟨172443, by rfl⟩ : syracuseStep 1839397 = 344887) (by norm_num)
theorem B4657445 : Blo 1634016 4657445 := bbase (se 4 (by rfl) ⟨436635, by rfl⟩ : syracuseStep 4657445 = 873271) (by norm_num)
theorem B2453813 : Blo 1634016 2453813 := bbase (se 5 (by rfl) ⟨115022, by rfl⟩ : syracuseStep 2453813 = 230045) (by norm_num)
theorem B1839433 : Blo 1634016 1839433 := bbase (se 2 (by rfl) ⟨689787, by rfl⟩ : syracuseStep 1839433 = 1379575) (by norm_num)
theorem B2453837 : Blo 1634016 2453837 := bbase (se 3 (by rfl) ⟨460094, by rfl⟩ : syracuseStep 2453837 = 920189) (by norm_num)
theorem B2453861 : Blo 1634016 2453861 := bbase (se 4 (by rfl) ⟨230049, by rfl⟩ : syracuseStep 2453861 = 460099) (by norm_num)
theorem B2068841 : Blo 1634016 2068841 := bbase (se 2 (by rfl) ⟨775815, by rfl⟩ : syracuseStep 2068841 = 1551631) (by norm_num)
theorem B1839469 : Blo 1634016 1839469 := bbase (se 3 (by rfl) ⟨344900, by rfl⟩ : syracuseStep 1839469 = 689801) (by norm_num)
theorem B2453885 : Blo 1634016 2453885 := bbase (se 3 (by rfl) ⟨460103, by rfl⟩ : syracuseStep 2453885 = 920207) (by norm_num)
theorem B1839505 : Blo 1634016 1839505 := bbase (se 2 (by rfl) ⟨689814, by rfl⟩ : syracuseStep 1839505 = 1379629) (by norm_num)
theorem B13250965 : Blo 1634016 13250965 := bbase (se 6 (by rfl) ⟨310569, by rfl⟩ : syracuseStep 13250965 = 621139) (by norm_num)
theorem B2453909 : Blo 1634016 2453909 := bbase (se 6 (by rfl) ⟨57513, by rfl⟩ : syracuseStep 2453909 = 115027) (by norm_num)
theorem B2068897 : Blo 1634016 2068897 := bbase (se 2 (by rfl) ⟨775836, by rfl⟩ : syracuseStep 2068897 = 1551673) (by norm_num)
theorem B2453933 : Blo 1634016 2453933 := bbase (se 3 (by rfl) ⟨460112, by rfl⟩ : syracuseStep 2453933 = 920225) (by norm_num)
theorem B1839541 : Blo 1634016 1839541 := bbase (se 5 (by rfl) ⟨86228, by rfl⟩ : syracuseStep 1839541 = 172457) (by norm_num)
theorem B2453957 : Blo 1634016 2453957 := bbase (se 4 (by rfl) ⟨230058, by rfl⟩ : syracuseStep 2453957 = 460117) (by norm_num)
theorem B1839577 : Blo 1634016 1839577 := bbase (se 2 (by rfl) ⟨689841, by rfl⟩ : syracuseStep 1839577 = 1379683) (by norm_num)
theorem B2453981 : Blo 1634016 2453981 := bbase (se 3 (by rfl) ⟨460121, by rfl⟩ : syracuseStep 2453981 = 920243) (by norm_num)
theorem B2454005 : Blo 1634016 2454005 := bbase (se 5 (by rfl) ⟨115031, by rfl⟩ : syracuseStep 2454005 = 230063) (by norm_num)
theorem B1839613 : Blo 1634016 1839613 := bbase (se 3 (by rfl) ⟨344927, by rfl⟩ : syracuseStep 1839613 = 689855) (by norm_num)
theorem B2068993 : Blo 1634016 2068993 := bbase (se 2 (by rfl) ⟨775872, by rfl⟩ : syracuseStep 2068993 = 1551745) (by norm_num)
theorem B1864225 : Blo 1634016 1864225 := bbase (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) (by norm_num)
theorem B1839649 : Blo 1634016 1839649 := bbase (se 2 (by rfl) ⟨689868, by rfl⟩ : syracuseStep 1839649 = 1379737) (by norm_num)
theorem B1839685 : Blo 1634016 1839685 := bbase (se 4 (by rfl) ⟨172470, by rfl⟩ : syracuseStep 1839685 = 344941) (by norm_num)
theorem B1839721 : Blo 1634016 1839721 := bbase (se 2 (by rfl) ⟨689895, by rfl⟩ : syracuseStep 1839721 = 1379791) (by norm_num)
theorem B1839757 : Blo 1634016 1839757 := bbase (se 3 (by rfl) ⟨344954, by rfl⟩ : syracuseStep 1839757 = 689909) (by norm_num)
theorem B5517989 : Blo 1634016 5517989 := bbase (se 4 (by rfl) ⟨517311, by rfl⟩ : syracuseStep 5517989 = 1034623) (by norm_num)
theorem B2069165 : Blo 1634016 2069165 := bbase (se 3 (by rfl) ⟨387968, by rfl⟩ : syracuseStep 2069165 = 775937) (by norm_num)
theorem B1839793 : Blo 1634016 1839793 := bbase (se 2 (by rfl) ⟨689922, by rfl⟩ : syracuseStep 1839793 = 1379845) (by norm_num)
theorem B6632117 : Blo 1634016 6632117 := bbase (se 5 (by rfl) ⟨310880, by rfl⟩ : syracuseStep 6632117 = 621761) (by norm_num)
theorem B1839829 : Blo 1634016 1839829 := bbase (se 7 (by rfl) ⟨21560, by rfl⟩ : syracuseStep 1839829 = 43121) (by norm_num)
theorem B2069221 : Blo 1634016 2069221 := bbase (se 4 (by rfl) ⟨193989, by rfl⟩ : syracuseStep 2069221 = 387979) (by norm_num)
theorem B1839865 : Blo 1634016 1839865 := bbase (se 2 (by rfl) ⟨689949, by rfl⟩ : syracuseStep 1839865 = 1379899) (by norm_num)
theorem B2519837 : Blo 1634016 2519837 := bbase (se 3 (by rfl) ⟨472469, by rfl⟩ : syracuseStep 2519837 = 944939) (by norm_num)
theorem B1839901 : Blo 1634016 1839901 := bbase (se 3 (by rfl) ⟨344981, by rfl⟩ : syracuseStep 1839901 = 689963) (by norm_num)
theorem B2618173 : Blo 1634016 2618173 := bbase (se 3 (by rfl) ⟨490907, by rfl⟩ : syracuseStep 2618173 = 981815) (by norm_num)
theorem B1839937 : Blo 1634016 1839937 := bbase (se 2 (by rfl) ⟨689976, by rfl⟩ : syracuseStep 1839937 = 1379953) (by norm_num)
theorem B2069317 : Blo 1634016 2069317 := bbase (se 4 (by rfl) ⟨193998, by rfl⟩ : syracuseStep 2069317 = 387997) (by norm_num)
theorem B2757469 : Blo 1634016 2757469 := bbase (se 3 (by rfl) ⟨517025, by rfl⟩ : syracuseStep 2757469 = 1034051) (by norm_num)
theorem B5591909 : Blo 1634016 5591909 := bbase (se 4 (by rfl) ⟨524241, by rfl⟩ : syracuseStep 5591909 = 1048483) (by norm_num)
theorem B1839973 : Blo 1634016 1839973 := bbase (se 4 (by rfl) ⟨172497, by rfl⟩ : syracuseStep 1839973 = 344995) (by norm_num)
theorem B5895013 : Blo 1634016 5895013 := bbase (se 4 (by rfl) ⟨552657, by rfl⟩ : syracuseStep 5895013 = 1105315) (by norm_num)
theorem B6206341 : Blo 1634016 6206341 := bbase (se 4 (by rfl) ⟨581844, by rfl⟩ : syracuseStep 6206341 = 1163689) (by norm_num)
theorem B1840009 : Blo 1634016 1840009 := bbase (se 2 (by rfl) ⟨690003, by rfl⟩ : syracuseStep 1840009 = 1380007) (by norm_num)
theorem B1840045 : Blo 1634016 1840045 := bbase (se 3 (by rfl) ⟨345008, by rfl⟩ : syracuseStep 1840045 = 690017) (by norm_num)
theorem B2757557 : Blo 1634016 2757557 := bbase (se 5 (by rfl) ⟨129260, by rfl⟩ : syracuseStep 2757557 = 258521) (by norm_num)
theorem B1840081 : Blo 1634016 1840081 := bbase (se 2 (by rfl) ⟨690030, by rfl⟩ : syracuseStep 1840081 = 1380061) (by norm_num)
theorem B2069489 : Blo 1634016 2069489 := bbase (se 2 (by rfl) ⟨776058, by rfl⟩ : syracuseStep 2069489 = 1552117) (by norm_num)
theorem B1840117 : Blo 1634016 1840117 := bbase (se 5 (by rfl) ⟨86255, by rfl⟩ : syracuseStep 1840117 = 172511) (by norm_num)
theorem B1840153 : Blo 1634016 1840153 := bbase (se 2 (by rfl) ⟨690057, by rfl⟩ : syracuseStep 1840153 = 1380115) (by norm_num)
theorem B2069545 : Blo 1634016 2069545 := bbase (se 2 (by rfl) ⟨776079, by rfl⟩ : syracuseStep 2069545 = 1552159) (by norm_num)
theorem B2757685 : Blo 1634016 2757685 := bbase (se 5 (by rfl) ⟨129266, by rfl⟩ : syracuseStep 2757685 = 258533) (by norm_num)
theorem B1840189 : Blo 1634016 1840189 := bbase (se 3 (by rfl) ⟨345035, by rfl⟩ : syracuseStep 1840189 = 690071) (by norm_num)
theorem B5518421 : Blo 1634016 5518421 := bbase (se 8 (by rfl) ⟨32334, by rfl⟩ : syracuseStep 5518421 = 64669) (by norm_num)
theorem B19895381 : Blo 1634016 19895381 := bbase (se 8 (by rfl) ⟨116574, by rfl⟩ : syracuseStep 19895381 = 233149) (by norm_num)
theorem B1840225 : Blo 1634016 1840225 := bbase (se 2 (by rfl) ⟨690084, by rfl⟩ : syracuseStep 1840225 = 1380169) (by norm_num)
theorem B1840261 : Blo 1634016 1840261 := bbase (se 4 (by rfl) ⟨172524, by rfl⟩ : syracuseStep 1840261 = 345049) (by norm_num)
theorem B2069641 : Blo 1634016 2069641 := bbase (se 2 (by rfl) ⟨776115, by rfl⟩ : syracuseStep 2069641 = 1552231) (by norm_num)
theorem B2757773 : Blo 1634016 2757773 := bbase (se 3 (by rfl) ⟨517082, by rfl⟩ : syracuseStep 2757773 = 1034165) (by norm_num)
theorem B9311381 : Blo 1634016 9311381 := bbase (se 6 (by rfl) ⟨218235, by rfl⟩ : syracuseStep 9311381 = 436471) (by norm_num)
theorem B1840297 : Blo 1634016 1840297 := bbase (se 2 (by rfl) ⟨690111, by rfl⟩ : syracuseStep 1840297 = 1380223) (by norm_num)
theorem B1864877 : Blo 1634016 1864877 := bbase (se 3 (by rfl) ⟨349664, by rfl⟩ : syracuseStep 1864877 = 699329) (by norm_num)
theorem B6206645 : Blo 1634016 6206645 := bbase (se 5 (by rfl) ⟨290936, by rfl⟩ : syracuseStep 6206645 = 581873) (by norm_num)
theorem B1840333 : Blo 1634016 1840333 := bbase (se 3 (by rfl) ⟨345062, by rfl⟩ : syracuseStep 1840333 = 690125) (by norm_num)
theorem B10360021 : Blo 1634016 10360021 := bbase (se 7 (by rfl) ⟨121406, by rfl⟩ : syracuseStep 10360021 = 242813) (by norm_num)
theorem B1840369 : Blo 1634016 1840369 := bbase (se 2 (by rfl) ⟨690138, by rfl⟩ : syracuseStep 1840369 = 1380277) (by norm_num)
theorem B2757901 : Blo 1634016 2757901 := bbase (se 3 (by rfl) ⟨517106, by rfl⟩ : syracuseStep 2757901 = 1034213) (by norm_num)
theorem B1840405 : Blo 1634016 1840405 := bbase (se 6 (by rfl) ⟨43134, by rfl⟩ : syracuseStep 1840405 = 86269) (by norm_num)
theorem B8279333 : Blo 1634016 8279333 := bbase (se 4 (by rfl) ⟨776187, by rfl⟩ : syracuseStep 8279333 = 1552375) (by norm_num)
theorem B2069813 : Blo 1634016 2069813 := bbase (se 5 (by rfl) ⟨97022, by rfl⟩ : syracuseStep 2069813 = 194045) (by norm_num)
theorem B1840441 : Blo 1634016 1840441 := bbase (se 2 (by rfl) ⟨690165, by rfl⟩ : syracuseStep 1840441 = 1380331) (by norm_num)
theorem B1840477 : Blo 1634016 1840477 := bbase (se 3 (by rfl) ⟨345089, by rfl⟩ : syracuseStep 1840477 = 690179) (by norm_num)
theorem B2757989 : Blo 1634016 2757989 := bbase (se 4 (by rfl) ⟨258561, by rfl⟩ : syracuseStep 2757989 = 517123) (by norm_num)
theorem B2069869 : Blo 1634016 2069869 := bbase (se 3 (by rfl) ⟨388100, by rfl⟩ : syracuseStep 2069869 = 776201) (by norm_num)
theorem B1840513 : Blo 1634016 1840513 := bbase (se 2 (by rfl) ⟨690192, by rfl⟩ : syracuseStep 1840513 = 1380385) (by norm_num)
theorem B4658629 : Blo 1634016 4658629 := bbase (se 4 (by rfl) ⟨436746, by rfl⟩ : syracuseStep 4658629 = 873493) (by norm_num)
theorem B2069965 : Blo 1634016 2069965 := bbase (se 3 (by rfl) ⟨388118, by rfl⟩ : syracuseStep 2069965 = 776237) (by norm_num)
theorem B2758117 : Blo 1634016 2758117 := bbase (se 4 (by rfl) ⟨258573, by rfl⟩ : syracuseStep 2758117 = 517147) (by norm_num)
theorem B5518853 : Blo 1634016 5518853 := bbase (se 4 (by rfl) ⟨517392, by rfl⟩ : syracuseStep 5518853 = 1034785) (by norm_num)
theorem B3102229 : Blo 1634016 3102229 := bbase (se 6 (by rfl) ⟨72708, by rfl⟩ : syracuseStep 3102229 = 145417) (by norm_num)
theorem B9942581 : Blo 1634016 9942581 := bbase (se 5 (by rfl) ⟨466058, by rfl⟩ : syracuseStep 9942581 = 932117) (by norm_num)
theorem B2758205 : Blo 1634016 2758205 := bbase (se 3 (by rfl) ⟨517163, by rfl⟩ : syracuseStep 2758205 = 1034327) (by norm_num)
theorem B13964885 : Blo 1634016 13964885 := bbase (se 8 (by rfl) ⟨81825, by rfl⟩ : syracuseStep 13964885 = 163651) (by norm_num)
theorem B8074853 : Blo 1634016 8074853 := bbase (se 4 (by rfl) ⟨757017, by rfl⟩ : syracuseStep 8074853 = 1514035) (by norm_num)
theorem B4658789 : Blo 1634016 4658789 := bbase (se 4 (by rfl) ⟨436761, by rfl⟩ : syracuseStep 4658789 = 873523) (by norm_num)
theorem B2070137 : Blo 1634016 2070137 := bbase (se 2 (by rfl) ⟨776301, by rfl⟩ : syracuseStep 2070137 = 1552603) (by norm_num)
theorem B1963649 : Blo 1634016 1963649 := bbase (se 2 (by rfl) ⟨736368, by rfl⟩ : syracuseStep 1963649 = 1472737) (by norm_num)
theorem B2070193 : Blo 1634016 2070193 := bbase (se 2 (by rfl) ⟨776322, by rfl⟩ : syracuseStep 2070193 = 1552645) (by norm_num)
theorem B2758333 : Blo 1634016 2758333 := bbase (se 3 (by rfl) ⟨517187, by rfl⟩ : syracuseStep 2758333 = 1034375) (by norm_num)
theorem B1963721 : Blo 1634016 1963721 := bbase (se 2 (by rfl) ⟨736395, by rfl⟩ : syracuseStep 1963721 = 1472791) (by norm_num)
theorem B2070289 : Blo 1634016 2070289 := bbase (se 2 (by rfl) ⟨776358, by rfl⟩ : syracuseStep 2070289 = 1552717) (by norm_num)
theorem B2758421 : Blo 1634016 2758421 := bbase (se 6 (by rfl) ⟨64650, by rfl⟩ : syracuseStep 2758421 = 129301) (by norm_num)
theorem B3102533 : Blo 1634016 3102533 := bbase (se 4 (by rfl) ⟨290862, by rfl⟩ : syracuseStep 3102533 = 581725) (by norm_num)
theorem B20952917 : Blo 1634016 20952917 := bbase (se 9 (by rfl) ⟨61385, by rfl⟩ : syracuseStep 20952917 = 122771) (by norm_num)
theorem B2758549 : Blo 1634016 2758549 := bbase (se 6 (by rfl) ⟨64653, by rfl⟩ : syracuseStep 2758549 = 129307) (by norm_num)
theorem B5519285 : Blo 1634016 5519285 := bbase (se 5 (by rfl) ⟨258716, by rfl⟩ : syracuseStep 5519285 = 517433) (by norm_num)
theorem B2070461 : Blo 1634016 2070461 := bbase (se 3 (by rfl) ⟨388211, by rfl⟩ : syracuseStep 2070461 = 776423) (by norm_num)
theorem B2758637 : Blo 1634016 2758637 := bbase (se 3 (by rfl) ⟨517244, by rfl⟩ : syracuseStep 2758637 = 1034489) (by norm_num)
theorem B2070517 : Blo 1634016 2070517 := bbase (se 5 (by rfl) ⟨97055, by rfl⟩ : syracuseStep 2070517 = 194111) (by norm_num)
theorem B1964029 : Blo 1634016 1964029 := bbase (se 3 (by rfl) ⟨368255, by rfl⟩ : syracuseStep 1964029 = 736511) (by norm_num)
theorem B2947117 : Blo 1634016 2947117 := bbase (se 3 (by rfl) ⟨552584, by rfl⟩ : syracuseStep 2947117 = 1105169) (by norm_num)
theorem B5240933 : Blo 1634016 5240933 := bbase (se 4 (by rfl) ⟨491337, by rfl⟩ : syracuseStep 5240933 = 982675) (by norm_num)
theorem B2758765 : Blo 1634016 2758765 := bbase (se 3 (by rfl) ⟨517268, by rfl⟩ : syracuseStep 2758765 = 1034537) (by norm_num)
theorem B1964197 : Blo 1634016 1964197 := bbase (se 4 (by rfl) ⟨184143, by rfl⟩ : syracuseStep 1964197 = 368287) (by norm_num)
theorem B2619557 : Blo 1634016 2619557 := bbase (se 4 (by rfl) ⟨245583, by rfl⟩ : syracuseStep 2619557 = 491167) (by norm_num)
theorem B2947261 : Blo 1634016 2947261 := bbase (se 3 (by rfl) ⟨552611, by rfl⟩ : syracuseStep 2947261 = 1105223) (by norm_num)
theorem B2758853 : Blo 1634016 2758853 := bbase (se 4 (by rfl) ⟨258642, by rfl⟩ : syracuseStep 2758853 = 517285) (by norm_num)
theorem B1964245 : Blo 1634016 1964245 := bbase (se 7 (by rfl) ⟨23018, by rfl⟩ : syracuseStep 1964245 = 46037) (by norm_num)
theorem B3930373 : Blo 1634016 3930373 := bbase (se 4 (by rfl) ⟨368472, by rfl⟩ : syracuseStep 3930373 = 736945) (by norm_num)
theorem B6715669 : Blo 1634016 6715669 := bbase (se 6 (by rfl) ⟨157398, by rfl⟩ : syracuseStep 6715669 = 314797) (by norm_num)
theorem B1964341 : Blo 1634016 1964341 := bbase (se 5 (by rfl) ⟨92078, by rfl⟩ : syracuseStep 1964341 = 184157) (by norm_num)
theorem B2758981 : Blo 1634016 2758981 := bbase (se 4 (by rfl) ⟨258654, by rfl⟩ : syracuseStep 2758981 = 517309) (by norm_num)
theorem B5519717 : Blo 1634016 5519717 := bbase (se 4 (by rfl) ⟨517473, by rfl⟩ : syracuseStep 5519717 = 1034947) (by norm_num)
theorem B2619749 : Blo 1634016 2619749 := bbase (se 4 (by rfl) ⟨245601, by rfl⟩ : syracuseStep 2619749 = 491203) (by norm_num)
theorem B2759069 : Blo 1634016 2759069 := bbase (se 3 (by rfl) ⟨517325, by rfl⟩ : syracuseStep 2759069 = 1034651) (by norm_num)
theorem B3676589 : Blo 1634016 3676589 := bbase (se 3 (by rfl) ⟨689360, by rfl⟩ : syracuseStep 3676589 = 1378721) (by norm_num)
theorem B1890769 : Blo 1634016 1890769 := bbase (se 2 (by rfl) ⟨709038, by rfl⟩ : syracuseStep 1890769 = 1418077) (by norm_num)
theorem B3676661 : Blo 1634016 3676661 := bbase (se 5 (by rfl) ⟨172343, by rfl⟩ : syracuseStep 3676661 = 344687) (by norm_num)
theorem B2759197 : Blo 1634016 2759197 := bbase (se 3 (by rfl) ⟨517349, by rfl⟩ : syracuseStep 2759197 = 1034699) (by norm_num)
theorem B3103285 : Blo 1634016 3103285 := bbase (se 5 (by rfl) ⟨145466, by rfl⟩ : syracuseStep 3103285 = 290933) (by norm_num)
theorem B8280629 : Blo 1634016 8280629 := bbase (se 5 (by rfl) ⟨388154, by rfl⟩ : syracuseStep 8280629 = 776309) (by norm_num)
theorem B3676733 : Blo 1634016 3676733 := bbase (se 3 (by rfl) ⟨689387, by rfl⟩ : syracuseStep 3676733 = 1378775) (by norm_num)
theorem B2759285 : Blo 1634016 2759285 := bbase (se 5 (by rfl) ⟨129341, by rfl⟩ : syracuseStep 2759285 = 258683) (by norm_num)
theorem B11188853 : Blo 1634016 11188853 := bbase (se 5 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 11188853 = 1048955) (by norm_num)
theorem B6986357 : Blo 1634016 6986357 := bbase (se 5 (by rfl) ⟨327485, by rfl⟩ : syracuseStep 6986357 = 654971) (by norm_num)
theorem B3676805 : Blo 1634016 3676805 := bbase (se 4 (by rfl) ⟨344700, by rfl⟩ : syracuseStep 3676805 = 689401) (by norm_num)
theorem B3103429 : Blo 1634016 3103429 := bbase (se 4 (by rfl) ⟨290946, by rfl⟩ : syracuseStep 3103429 = 581893) (by norm_num)
theorem B3676877 : Blo 1634016 3676877 := bbase (se 3 (by rfl) ⟨689414, by rfl⟩ : syracuseStep 3676877 = 1378829) (by norm_num)
theorem B2759413 : Blo 1634016 2759413 := bbase (se 5 (by rfl) ⟨129347, by rfl⟩ : syracuseStep 2759413 = 258695) (by norm_num)
theorem B2947837 : Blo 1634016 2947837 := bbase (se 3 (by rfl) ⟨552719, by rfl⟩ : syracuseStep 2947837 = 1105439) (by norm_num)
theorem B3676949 : Blo 1634016 3676949 := bbase (se 6 (by rfl) ⟨86178, by rfl⟩ : syracuseStep 3676949 = 172357) (by norm_num)
theorem B5520149 : Blo 1634016 5520149 := bbase (se 6 (by rfl) ⟨129378, by rfl⟩ : syracuseStep 5520149 = 258757) (by norm_num)
theorem B2759501 : Blo 1634016 2759501 := bbase (se 3 (by rfl) ⟨517406, by rfl⟩ : syracuseStep 2759501 = 1034813) (by norm_num)
theorem B23886677 : Blo 1634016 23886677 := bbase (se 9 (by rfl) ⟨69980, by rfl⟩ : syracuseStep 23886677 = 139961) (by norm_num)
theorem B3677021 : Blo 1634016 3677021 := bbase (se 3 (by rfl) ⟨689441, by rfl⟩ : syracuseStep 3677021 = 1378883) (by norm_num)
theorem B3103589 : Blo 1634016 3103589 := bbase (se 4 (by rfl) ⟨290961, by rfl⟩ : syracuseStep 3103589 = 581923) (by norm_num)
theorem B1964917 : Blo 1634016 1964917 := bbase (se 5 (by rfl) ⟨92105, by rfl⟩ : syracuseStep 1964917 = 184211) (by norm_num)
theorem B6986645 : Blo 1634016 6986645 := bbase (se 6 (by rfl) ⟨163749, by rfl⟩ : syracuseStep 6986645 = 327499) (by norm_num)
theorem B3677093 : Blo 1634016 3677093 := bbase (se 4 (by rfl) ⟨344727, by rfl⟩ : syracuseStep 3677093 = 689455) (by norm_num)
theorem B2759629 : Blo 1634016 2759629 := bbase (se 3 (by rfl) ⟨517430, by rfl⟩ : syracuseStep 2759629 = 1034861) (by norm_num)
theorem B8272853 : Blo 1634016 8272853 := bbase (se 7 (by rfl) ⟨96947, by rfl⟩ : syracuseStep 8272853 = 193895) (by norm_num)
theorem B3677165 : Blo 1634016 3677165 := bbase (se 3 (by rfl) ⟨689468, by rfl⟩ : syracuseStep 3677165 = 1378937) (by norm_num)
theorem B3103733 : Blo 1634016 3103733 := bbase (se 5 (by rfl) ⟨145487, by rfl⟩ : syracuseStep 3103733 = 290975) (by norm_num)
theorem B2759717 : Blo 1634016 2759717 := bbase (se 4 (by rfl) ⟨258723, by rfl⟩ : syracuseStep 2759717 = 517447) (by norm_num)
theorem B3677237 : Blo 1634016 3677237 := bbase (se 5 (by rfl) ⟨172370, by rfl⟩ : syracuseStep 3677237 = 344741) (by norm_num)
theorem B1637465 : Blo 1634016 1637465 := bbase (se 2 (by rfl) ⟨614049, by rfl⟩ : syracuseStep 1637465 = 1228099) (by norm_num)
theorem B2210917 : Blo 1634016 2210917 := bbase (se 4 (by rfl) ⟨207273, by rfl⟩ : syracuseStep 2210917 = 414547) (by norm_num)
theorem B2653309 : Blo 1634016 2653309 := bbase (se 3 (by rfl) ⟨497495, by rfl⟩ : syracuseStep 2653309 = 994991) (by norm_num)
theorem B3677309 : Blo 1634016 3677309 := bbase (se 3 (by rfl) ⟨689495, by rfl⟩ : syracuseStep 3677309 = 1378991) (by norm_num)
theorem B2759845 : Blo 1634016 2759845 := bbase (se 4 (by rfl) ⟨258735, by rfl⟩ : syracuseStep 2759845 = 517471) (by norm_num)
theorem B3677381 : Blo 1634016 3677381 := bbase (se 4 (by rfl) ⟨344754, by rfl⟩ : syracuseStep 3677381 = 689509) (by norm_num)
theorem B5520581 : Blo 1634016 5520581 := bbase (se 4 (by rfl) ⟨517554, by rfl⟩ : syracuseStep 5520581 = 1035109) (by norm_num)
theorem B14351573 : Blo 1634016 14351573 := bbase (se 7 (by rfl) ⟨168182, by rfl⟩ : syracuseStep 14351573 = 336365) (by norm_num)
theorem B6462709 : Blo 1634016 6462709 := bbase (se 5 (by rfl) ⟨302939, by rfl⟩ : syracuseStep 6462709 = 605879) (by norm_num)
theorem B6208757 : Blo 1634016 6208757 := bbase (se 5 (by rfl) ⟨291035, by rfl⟩ : syracuseStep 6208757 = 582071) (by norm_num)
theorem B2759933 : Blo 1634016 2759933 := bbase (se 3 (by rfl) ⟨517487, by rfl⟩ : syracuseStep 2759933 = 1034975) (by norm_num)
theorem B3538181 : Blo 1634016 3538181 := bbase (se 4 (by rfl) ⟨331704, by rfl⟩ : syracuseStep 3538181 = 663409) (by norm_num)
theorem B3677453 : Blo 1634016 3677453 := bbase (se 3 (by rfl) ⟨689522, by rfl⟩ : syracuseStep 3677453 = 1379045) (by norm_num)
theorem B3104021 : Blo 1634016 3104021 := bbase (se 6 (by rfl) ⟨72750, by rfl⟩ : syracuseStep 3104021 = 145501) (by norm_num)
theorem B3677525 : Blo 1634016 3677525 := bbase (se 11 (by rfl) ⟨2693, by rfl⟩ : syracuseStep 3677525 = 5387) (by norm_num)
theorem B4136285 : Blo 1634016 4136285 := bbase (se 3 (by rfl) ⟨775553, by rfl⟩ : syracuseStep 4136285 = 1551107) (by norm_num)
theorem B2760061 : Blo 1634016 2760061 := bbase (se 3 (by rfl) ⟨517511, by rfl⟩ : syracuseStep 2760061 = 1035023) (by norm_num)
theorem B3677597 : Blo 1634016 3677597 := bbase (se 3 (by rfl) ⟨689549, by rfl⟩ : syracuseStep 3677597 = 1379099) (by norm_num)
theorem B3104173 : Blo 1634016 3104173 := bbase (se 3 (by rfl) ⟨582032, by rfl⟩ : syracuseStep 3104173 = 1164065) (by norm_num)
theorem B2760149 : Blo 1634016 2760149 := bbase (se 7 (by rfl) ⟨32345, by rfl⟩ : syracuseStep 2760149 = 64691) (by norm_num)
theorem B3677669 : Blo 1634016 3677669 := bbase (se 4 (by rfl) ⟨344781, by rfl⟩ : syracuseStep 3677669 = 689563) (by norm_num)
theorem B3538421 : Blo 1634016 3538421 := bbase (se 5 (by rfl) ⟨165863, by rfl⟩ : syracuseStep 3538421 = 331727) (by norm_num)
theorem B6209045 : Blo 1634016 6209045 := bbase (se 6 (by rfl) ⟨145524, by rfl⟩ : syracuseStep 6209045 = 291049) (by norm_num)
theorem B3677741 : Blo 1634016 3677741 := bbase (se 3 (by rfl) ⟨689576, by rfl⟩ : syracuseStep 3677741 = 1379153) (by norm_num)
theorem B2760277 : Blo 1634016 2760277 := bbase (se 8 (by rfl) ⟨16173, by rfl⟩ : syracuseStep 2760277 = 32347) (by norm_num)
theorem B3677813 : Blo 1634016 3677813 := bbase (se 5 (by rfl) ⟨172397, by rfl⟩ : syracuseStep 3677813 = 344795) (by norm_num)
theorem B5521013 : Blo 1634016 5521013 := bbase (se 5 (by rfl) ⟨258797, by rfl⟩ : syracuseStep 5521013 = 517595) (by norm_num)
theorem B6987397 : Blo 1634016 6987397 := bbase (se 4 (by rfl) ⟨655068, by rfl⟩ : syracuseStep 6987397 = 1310137) (by norm_num)
theorem B2760365 : Blo 1634016 2760365 := bbase (se 3 (by rfl) ⟨517568, by rfl⟩ : syracuseStep 2760365 = 1035137) (by norm_num)
theorem B4136629 : Blo 1634016 4136629 := bbase (se 5 (by rfl) ⟨193904, by rfl⟩ : syracuseStep 4136629 = 387809) (by norm_num)
theorem B3677885 : Blo 1634016 3677885 := bbase (se 3 (by rfl) ⟨689603, by rfl⟩ : syracuseStep 3677885 = 1379207) (by norm_num)
theorem B18620117 : Blo 1634016 18620117 := bbase (se 7 (by rfl) ⟨218204, by rfl⟩ : syracuseStep 18620117 = 436409) (by norm_num)
theorem B3104477 : Blo 1634016 3104477 := bbase (se 3 (by rfl) ⟨582089, by rfl⟩ : syracuseStep 3104477 = 1164179) (by norm_num)
theorem B3677957 : Blo 1634016 3677957 := bbase (se 4 (by rfl) ⟨344808, by rfl⟩ : syracuseStep 3677957 = 689617) (by norm_num)
theorem B4136741 : Blo 1634016 4136741 := bbase (se 4 (by rfl) ⟨387819, by rfl⟩ : syracuseStep 4136741 = 775639) (by norm_num)
theorem B2760493 : Blo 1634016 2760493 := bbase (se 3 (by rfl) ⟨517592, by rfl⟩ : syracuseStep 2760493 = 1035185) (by norm_num)
theorem B8281925 : Blo 1634016 8281925 := bbase (se 4 (by rfl) ⟨776430, by rfl⟩ : syracuseStep 8281925 = 1552861) (by norm_num)
theorem B3678029 : Blo 1634016 3678029 := bbase (se 3 (by rfl) ⟨689630, by rfl⟩ : syracuseStep 3678029 = 1379261) (by norm_num)
theorem B35839829 : Blo 1634016 35839829 := bbase (se 9 (by rfl) ⟨104999, by rfl⟩ : syracuseStep 35839829 = 209999) (by norm_num)
theorem B2760581 : Blo 1634016 2760581 := bbase (se 4 (by rfl) ⟨258804, by rfl⟩ : syracuseStep 2760581 = 517609) (by norm_num)
theorem B3678101 : Blo 1634016 3678101 := bbase (se 6 (by rfl) ⟨86205, by rfl⟩ : syracuseStep 3678101 = 172411) (by norm_num)
theorem B3678173 : Blo 1634016 3678173 := bbase (se 3 (by rfl) ⟨689657, by rfl⟩ : syracuseStep 3678173 = 1379315) (by norm_num)
theorem B4136933 : Blo 1634016 4136933 := bbase (se 4 (by rfl) ⟨387837, by rfl⟩ : syracuseStep 4136933 = 775675) (by norm_num)
theorem B3981425 : Blo 1634016 3981425 := bstep (se 2 (by rfl) ⟨1493034, by rfl⟩ : syracuseStep 3981425 = 2986069) B2986069
theorem B4653197 : Blo 1634016 4653197 := bstep (se 3 (by rfl) ⟨872474, by rfl⟩ : syracuseStep 4653197 = 1744949) B1744949
theorem B3678353 : Blo 1634016 3678353 := bstep (se 2 (by rfl) ⟨1379382, by rfl⟩ : syracuseStep 3678353 = 2758765) B2758765
theorem B5521553 : Blo 1634016 5521553 := bstep (se 2 (by rfl) ⟨2070582, by rfl⟩ : syracuseStep 5521553 = 4141165) B4141165
theorem B3678371 : Blo 1634016 3678371 := bstep (se 1 (by rfl) ⟨2758778, by rfl⟩ : syracuseStep 3678371 = 5517557) B5517557
theorem B3104963 : Blo 1634016 3104963 := bstep (se 1 (by rfl) ⟨2328722, by rfl⟩ : syracuseStep 3104963 = 4657445) B4657445
theorem B25166051 : Blo 1634016 25166051 := bstep (se 1 (by rfl) ⟨18874538, by rfl⟩ : syracuseStep 25166051 = 37749077) B37749077
theorem B4653389 : Blo 1634016 4653389 := bstep (se 3 (by rfl) ⟨872510, by rfl⟩ : syracuseStep 4653389 = 1745021) B1745021
theorem B8954225 : Blo 1634016 8954225 := bstep (se 2 (by rfl) ⟨3357834, by rfl⟩ : syracuseStep 8954225 = 6715669) B6715669
theorem B3678641 : Blo 1634016 3678641 := bstep (se 2 (by rfl) ⟨1379490, by rfl⟩ : syracuseStep 3678641 = 2758981) B2758981
theorem B2326963 : Blo 1634016 2326963 := bstep (se 1 (by rfl) ⟨1745222, by rfl⟩ : syracuseStep 2326963 = 3490445) B3490445
theorem B3678659 : Blo 1634016 3678659 := bstep (se 1 (by rfl) ⟨2758994, by rfl⟩ : syracuseStep 3678659 = 5517989) B5517989
theorem B4973005 : Blo 1634016 4973005 := bstep (se 3 (by rfl) ⟨932438, by rfl⟩ : syracuseStep 4973005 = 1864877) B1864877
theorem B2327059 : Blo 1634016 2327059 := bstep (se 1 (by rfl) ⟨1745294, by rfl⟩ : syracuseStep 2327059 = 3490589) B3490589
theorem B1679891 : Blo 1634016 1679891 := bstep (se 1 (by rfl) ⟨1259918, by rfl⟩ : syracuseStep 1679891 = 2519837) B2519837
theorem B3727939 : Blo 1634016 3727939 := bstep (se 1 (by rfl) ⟨2795954, by rfl⟩ : syracuseStep 3727939 = 5591909) B5591909
theorem B4973201 : Blo 1634016 4973201 := bstep (se 2 (by rfl) ⟨1864950, by rfl⟩ : syracuseStep 4973201 = 3729901) B3729901
theorem B3678929 : Blo 1634016 3678929 := bstep (se 2 (by rfl) ⟨1379598, by rfl⟩ : syracuseStep 3678929 = 2759197) B2759197
theorem B3678947 : Blo 1634016 3678947 := bstep (se 1 (by rfl) ⟨2759210, by rfl⟩ : syracuseStep 3678947 = 5518421) B5518421
theorem B13263587 : Blo 1634016 13263587 := bstep (se 1 (by rfl) ⟨9947690, by rfl⟩ : syracuseStep 13263587 = 19895381) B19895381
theorem B4137713 : Blo 1634016 4137713 := bstep (se 2 (by rfl) ⟨1551642, by rfl⟩ : syracuseStep 4137713 = 3103285) B3103285
theorem B6292237 : Blo 1634016 6292237 := bstep (se 3 (by rfl) ⟨1179794, by rfl⟩ : syracuseStep 6292237 = 2359589) B2359589
theorem B5235473 : Blo 1634016 5235473 := bstep (se 2 (by rfl) ⟨1963302, by rfl⟩ : syracuseStep 5235473 = 3926605) B3926605
theorem B4137763 : Blo 1634016 4137763 := bstep (se 1 (by rfl) ⟨3103322, by rfl⟩ : syracuseStep 4137763 = 6206645) B6206645
theorem B5309297 : Blo 1634016 5309297 := bstep (se 2 (by rfl) ⟨1990986, by rfl⟩ : syracuseStep 5309297 = 3981973) B3981973
theorem B4137905 : Blo 1634016 4137905 := bstep (se 2 (by rfl) ⟨1551714, by rfl⟩ : syracuseStep 4137905 = 3103429) B3103429
theorem B17466293 : Blo 1634016 17466293 := bstep (se 5 (by rfl) ⟨818732, by rfl⟩ : syracuseStep 17466293 = 1637465) B1637465
theorem B3679217 : Blo 1634016 3679217 := bstep (se 2 (by rfl) ⟨1379706, by rfl⟩ : syracuseStep 3679217 = 2759413) B2759413
theorem B2327555 : Blo 1634016 2327555 := bstep (se 1 (by rfl) ⟨1745666, by rfl⟩ : syracuseStep 2327555 = 3491333) B3491333
theorem B3679235 : Blo 1634016 3679235 := bstep (se 1 (by rfl) ⟨2759426, by rfl⟩ : syracuseStep 3679235 = 5518853) B5518853
theorem B6628387 : Blo 1634016 6628387 := bstep (se 1 (by rfl) ⟨4971290, by rfl⟩ : syracuseStep 6628387 = 9942581) B9942581
theorem B5383235 : Blo 1634016 5383235 := bstep (se 1 (by rfl) ⟨4037426, by rfl⟩ : syracuseStep 5383235 = 8074853) B8074853
theorem B3105859 : Blo 1634016 3105859 := bstep (se 1 (by rfl) ⟨2329394, by rfl⟩ : syracuseStep 3105859 = 4658789) B4658789
theorem B3490897 : Blo 1634016 3490897 := bstep (se 2 (by rfl) ⟨1309086, by rfl⟩ : syracuseStep 3490897 = 2618173) B2618173
theorem B6210701 : Blo 1634016 6210701 := bstep (se 3 (by rfl) ⟨1164506, by rfl⟩ : syracuseStep 6210701 = 2329013) B2329013
theorem B8275121 : Blo 1634016 8275121 := bstep (se 2 (by rfl) ⟨3103170, by rfl⟩ : syracuseStep 8275121 = 6206341) B6206341
theorem B13968611 : Blo 1634016 13968611 := bstep (se 1 (by rfl) ⟨10476458, by rfl⟩ : syracuseStep 13968611 = 20952917) B20952917
theorem B3679505 : Blo 1634016 3679505 := bstep (se 2 (by rfl) ⟨1379814, by rfl⟩ : syracuseStep 3679505 = 2759629) B2759629
theorem B3679523 : Blo 1634016 3679523 := bstep (se 1 (by rfl) ⟨2759642, by rfl⟩ : syracuseStep 3679523 = 5519285) B5519285
theorem B4654381 : Blo 1634016 4654381 := bstep (se 3 (by rfl) ⟨872696, by rfl⟩ : syracuseStep 4654381 = 1745393) B1745393
theorem B6981041 : Blo 1634016 6981041 := bstep (se 2 (by rfl) ⟨2617890, by rfl⟩ : syracuseStep 6981041 = 5235781) B5235781
theorem B1746371 : Blo 1634016 1746371 := bstep (se 1 (by rfl) ⟨1309778, by rfl⟩ : syracuseStep 1746371 = 2619557) B2619557
theorem B15926797 : Blo 1634016 15926797 := bstep (se 3 (by rfl) ⟨2986274, by rfl⟩ : syracuseStep 15926797 = 5972549) B5972549
theorem B3679793 : Blo 1634016 3679793 := bstep (se 2 (by rfl) ⟨1379922, by rfl⟩ : syracuseStep 3679793 = 2759845) B2759845
theorem B3679811 : Blo 1634016 3679811 := bstep (se 1 (by rfl) ⟨2759858, by rfl⟩ : syracuseStep 3679811 = 5519717) B5519717
theorem B2451041 : Blo 1634016 2451041 := bstep (se 2 (by rfl) ⟨919140, by rfl⟩ : syracuseStep 2451041 = 1838281) B1838281
theorem B13813361 : Blo 1634016 13813361 := bstep (se 2 (by rfl) ⟨5180010, by rfl⟩ : syracuseStep 13813361 = 10360021) B10360021
theorem B2451059 : Blo 1634016 2451059 := bstep (se 1 (by rfl) ⟨1838294, by rfl⟩ : syracuseStep 2451059 = 3676589) B3676589
theorem B2328193 : Blo 1634016 2328193 := bstep (se 2 (by rfl) ⟨873072, by rfl⟩ : syracuseStep 2328193 = 1746145) B1746145
theorem B9307781 : Blo 1634016 9307781 := bstep (se 4 (by rfl) ⟨872604, by rfl⟩ : syracuseStep 9307781 = 1745209) B1745209
theorem B2451089 : Blo 1634016 2451089 := bstep (se 2 (by rfl) ⟨919158, by rfl⟩ : syracuseStep 2451089 = 1838317) B1838317
theorem B2451107 : Blo 1634016 2451107 := bstep (se 1 (by rfl) ⟨1838330, by rfl⟩ : syracuseStep 2451107 = 3676661) B3676661
theorem B5236397 : Blo 1634016 5236397 := bstep (se 3 (by rfl) ⟨981824, by rfl⟩ : syracuseStep 5236397 = 1963649) B1963649
theorem B2451137 : Blo 1634016 2451137 := bstep (se 2 (by rfl) ⟨919176, by rfl⟩ : syracuseStep 2451137 = 1838353) B1838353
theorem B3147473 : Blo 1634016 3147473 := bstep (se 2 (by rfl) ⟨1180302, by rfl⟩ : syracuseStep 3147473 = 2360605) B2360605
theorem B2451155 : Blo 1634016 2451155 := bstep (se 1 (by rfl) ⟨1838366, by rfl⟩ : syracuseStep 2451155 = 3676733) B3676733
theorem B2451185 : Blo 1634016 2451185 := bstep (se 2 (by rfl) ⟨919194, by rfl⟩ : syracuseStep 2451185 = 1838389) B1838389
theorem B2451203 : Blo 1634016 2451203 := bstep (se 1 (by rfl) ⟨1838402, by rfl⟩ : syracuseStep 2451203 = 3676805) B3676805
theorem B5973773 : Blo 1634016 5973773 := bstep (se 3 (by rfl) ⟨1120082, by rfl⟩ : syracuseStep 5973773 = 2240165) B2240165
theorem B2451233 : Blo 1634016 2451233 := bstep (se 2 (by rfl) ⟨919212, by rfl⟩ : syracuseStep 2451233 = 1838425) B1838425
theorem B2451251 : Blo 1634016 2451251 := bstep (se 1 (by rfl) ⟨1838438, by rfl⟩ : syracuseStep 2451251 = 3676877) B3676877
theorem B8963909 : Blo 1634016 8963909 := bstep (se 4 (by rfl) ⟨840366, by rfl⟩ : syracuseStep 8963909 = 1680733) B1680733
theorem B2451281 : Blo 1634016 2451281 := bstep (se 2 (by rfl) ⟨919230, by rfl⟩ : syracuseStep 2451281 = 1838461) B1838461
theorem B3680081 : Blo 1634016 3680081 := bstep (se 2 (by rfl) ⟨1380030, by rfl⟩ : syracuseStep 3680081 = 2760061) B2760061
theorem B2451299 : Blo 1634016 2451299 := bstep (se 1 (by rfl) ⟨1838474, by rfl⟩ : syracuseStep 2451299 = 3676949) B3676949
theorem B3680099 : Blo 1634016 3680099 := bstep (se 1 (by rfl) ⟨2760074, by rfl⟩ : syracuseStep 3680099 = 5520149) B5520149
theorem B5236589 : Blo 1634016 5236589 := bstep (se 3 (by rfl) ⟨981860, by rfl⟩ : syracuseStep 5236589 = 1963721) B1963721
theorem B2451329 : Blo 1634016 2451329 := bstep (se 2 (by rfl) ⟨919248, by rfl⟩ : syracuseStep 2451329 = 1838497) B1838497
theorem B4138897 : Blo 1634016 4138897 := bstep (se 2 (by rfl) ⟨1552086, by rfl⟩ : syracuseStep 4138897 = 3104173) B3104173
theorem B2451347 : Blo 1634016 2451347 := bstep (se 1 (by rfl) ⟨1838510, by rfl⟩ : syracuseStep 2451347 = 3677021) B3677021
theorem B5515181 : Blo 1634016 5515181 := bstep (se 3 (by rfl) ⟨1034096, by rfl⟩ : syracuseStep 5515181 = 2068193) B2068193
theorem B2451377 : Blo 1634016 2451377 := bstep (se 2 (by rfl) ⟨919266, by rfl⟩ : syracuseStep 2451377 = 1838533) B1838533
theorem B6211505 : Blo 1634016 6211505 := bstep (se 2 (by rfl) ⟨2329314, by rfl⟩ : syracuseStep 6211505 = 4658629) B4658629
theorem B2451395 : Blo 1634016 2451395 := bstep (se 1 (by rfl) ⟨1838546, by rfl⟩ : syracuseStep 2451395 = 3677093) B3677093
theorem B10479557 : Blo 1634016 10479557 := bstep (se 4 (by rfl) ⟨982458, by rfl⟩ : syracuseStep 10479557 = 1964917) B1964917
theorem B2328529 : Blo 1634016 2328529 := bstep (se 2 (by rfl) ⟨873198, by rfl⟩ : syracuseStep 2328529 = 1746397) B1746397
theorem B2451425 : Blo 1634016 2451425 := bstep (se 2 (by rfl) ⟨919284, by rfl⟩ : syracuseStep 2451425 = 1838569) B1838569
theorem B5515235 : Blo 1634016 5515235 := bstep (se 1 (by rfl) ⟨4136426, by rfl⟩ : syracuseStep 5515235 = 8272853) B8272853
theorem B2451443 : Blo 1634016 2451443 := bstep (se 1 (by rfl) ⟨1838582, by rfl⟩ : syracuseStep 2451443 = 3677165) B3677165
theorem B18614285 : Blo 1634016 18614285 := bstep (se 3 (by rfl) ⟨3490178, by rfl⟩ : syracuseStep 18614285 = 6980357) B6980357
theorem B22374413 : Blo 1634016 22374413 := bstep (se 3 (by rfl) ⟨4195202, by rfl⟩ : syracuseStep 22374413 = 8390405) B8390405
theorem B2451473 : Blo 1634016 2451473 := bstep (se 2 (by rfl) ⟨919302, by rfl⟩ : syracuseStep 2451473 = 1838605) B1838605
theorem B2451491 : Blo 1634016 2451491 := bstep (se 1 (by rfl) ⟨1838618, by rfl⟩ : syracuseStep 2451491 = 3677237) B3677237
theorem B2451521 : Blo 1634016 2451521 := bstep (se 2 (by rfl) ⟨919320, by rfl⟩ : syracuseStep 2451521 = 1838641) B1838641
theorem B2451539 : Blo 1634016 2451539 := bstep (se 1 (by rfl) ⟨1838654, by rfl⟩ : syracuseStep 2451539 = 3677309) B3677309
theorem B2451569 : Blo 1634016 2451569 := bstep (se 2 (by rfl) ⟨919338, by rfl⟩ : syracuseStep 2451569 = 1838677) B1838677
theorem B3680369 : Blo 1634016 3680369 := bstep (se 2 (by rfl) ⟨1380138, by rfl⟩ : syracuseStep 3680369 = 2760277) B2760277
theorem B2451587 : Blo 1634016 2451587 := bstep (se 1 (by rfl) ⟨1838690, by rfl⟩ : syracuseStep 2451587 = 3677381) B3677381
theorem B3680387 : Blo 1634016 3680387 := bstep (se 1 (by rfl) ⟨2760290, by rfl⟩ : syracuseStep 3680387 = 5520581) B5520581
theorem B4417681 : Blo 1634016 4417681 := bstep (se 2 (by rfl) ⟨1656630, by rfl⟩ : syracuseStep 4417681 = 3313261) B3313261
theorem B2451617 : Blo 1634016 2451617 := bstep (se 2 (by rfl) ⟨919356, by rfl⟩ : syracuseStep 2451617 = 1838713) B1838713
theorem B4139171 : Blo 1634016 4139171 := bstep (se 1 (by rfl) ⟨3104378, by rfl⟩ : syracuseStep 4139171 = 6208757) B6208757
theorem B9316529 : Blo 1634016 9316529 := bstep (se 2 (by rfl) ⟨3493698, by rfl⟩ : syracuseStep 9316529 = 6987397) B6987397
theorem B2451635 : Blo 1634016 2451635 := bstep (se 1 (by rfl) ⟨1838726, by rfl⟩ : syracuseStep 2451635 = 3677453) B3677453
theorem B2451665 : Blo 1634016 2451665 := bstep (se 2 (by rfl) ⟨919374, by rfl⟩ : syracuseStep 2451665 = 1838749) B1838749
theorem B2451683 : Blo 1634016 2451683 := bstep (se 1 (by rfl) ⟨1838762, by rfl⟩ : syracuseStep 2451683 = 3677525) B3677525
theorem B5515505 : Blo 1634016 5515505 := bstep (se 2 (by rfl) ⟨2068314, by rfl⟩ : syracuseStep 5515505 = 4136629) B4136629
theorem B2451713 : Blo 1634016 2451713 := bstep (se 2 (by rfl) ⟨919392, by rfl⟩ : syracuseStep 2451713 = 1838785) B1838785
theorem B2451731 : Blo 1634016 2451731 := bstep (se 1 (by rfl) ⟨1838798, by rfl⟩ : syracuseStep 2451731 = 3677597) B3677597
theorem B9308465 : Blo 1634016 9308465 := bstep (se 2 (by rfl) ⟨3490674, by rfl⟩ : syracuseStep 9308465 = 6981349) B6981349
theorem B2451761 : Blo 1634016 2451761 := bstep (se 2 (by rfl) ⟨919410, by rfl⟩ : syracuseStep 2451761 = 1838821) B1838821
theorem B2451779 : Blo 1634016 2451779 := bstep (se 1 (by rfl) ⟨1838834, by rfl⟩ : syracuseStep 2451779 = 3677669) B3677669
theorem B2451809 : Blo 1634016 2451809 := bstep (se 2 (by rfl) ⟨919428, by rfl⟩ : syracuseStep 2451809 = 1838857) B1838857
theorem B4139363 : Blo 1634016 4139363 := bstep (se 1 (by rfl) ⟨3104522, by rfl⟩ : syracuseStep 4139363 = 6209045) B6209045
theorem B2689393 : Blo 1634016 2689393 := bstep (se 2 (by rfl) ⟨1008522, by rfl⟩ : syracuseStep 2689393 = 2017045) B2017045
theorem B2451827 : Blo 1634016 2451827 := bstep (se 1 (by rfl) ⟨1838870, by rfl⟩ : syracuseStep 2451827 = 3677741) B3677741
theorem B2451857 : Blo 1634016 2451857 := bstep (se 2 (by rfl) ⟨919446, by rfl⟩ : syracuseStep 2451857 = 1838893) B1838893
theorem B3680657 : Blo 1634016 3680657 := bstep (se 2 (by rfl) ⟨1380246, by rfl⟩ : syracuseStep 3680657 = 2760493) B2760493
theorem B2451875 : Blo 1634016 2451875 := bstep (se 1 (by rfl) ⟨1838906, by rfl⟩ : syracuseStep 2451875 = 3677813) B3677813
theorem B3680675 : Blo 1634016 3680675 := bstep (se 1 (by rfl) ⟨2760506, by rfl⟩ : syracuseStep 3680675 = 5521013) B5521013
theorem B2451905 : Blo 1634016 2451905 := bstep (se 2 (by rfl) ⟨919464, by rfl⟩ : syracuseStep 2451905 = 1838929) B1838929
theorem B2451923 : Blo 1634016 2451923 := bstep (se 1 (by rfl) ⟨1838942, by rfl⟩ : syracuseStep 2451923 = 3677885) B3677885
theorem B12413411 : Blo 1634016 12413411 := bstep (se 1 (by rfl) ⟨9310058, by rfl⟩ : syracuseStep 12413411 = 18620117) B18620117
theorem B2451953 : Blo 1634016 2451953 := bstep (se 2 (by rfl) ⟨919482, by rfl⟩ : syracuseStep 2451953 = 1838965) B1838965
theorem B2451971 : Blo 1634016 2451971 := bstep (se 1 (by rfl) ⟨1838978, by rfl⟩ : syracuseStep 2451971 = 3677957) B3677957
theorem B10471949 : Blo 1634016 10471949 := bstep (se 3 (by rfl) ⟨1963490, by rfl⟩ : syracuseStep 10471949 = 3926981) B3926981
theorem B2452001 : Blo 1634016 2452001 := bstep (se 2 (by rfl) ⟨919500, by rfl⟩ : syracuseStep 2452001 = 1839001) B1839001
theorem B2329121 : Blo 1634016 2329121 := bstep (se 2 (by rfl) ⟨873420, by rfl⟩ : syracuseStep 2329121 = 1746841) B1746841
theorem B2452019 : Blo 1634016 2452019 := bstep (se 1 (by rfl) ⟨1839014, by rfl⟩ : syracuseStep 2452019 = 3678029) B3678029
theorem B2452049 : Blo 1634016 2452049 := bstep (se 2 (by rfl) ⟨919518, by rfl⟩ : syracuseStep 2452049 = 1839037) B1839037
theorem B2452067 : Blo 1634016 2452067 := bstep (se 1 (by rfl) ⟨1839050, by rfl⟩ : syracuseStep 2452067 = 3678101) B3678101
theorem B8276579 : Blo 1634016 8276579 := bstep (se 1 (by rfl) ⟨6207434, by rfl⟩ : syracuseStep 8276579 = 12414869) B12414869
theorem B2452097 : Blo 1634016 2452097 := bstep (se 2 (by rfl) ⟨919536, by rfl⟩ : syracuseStep 2452097 = 1839073) B1839073
theorem B2452115 : Blo 1634016 2452115 := bstep (se 1 (by rfl) ⟨1839086, by rfl⟩ : syracuseStep 2452115 = 3678173) B3678173
theorem B6982307 : Blo 1634016 6982307 := bstep (se 1 (by rfl) ⟨5236730, by rfl⟩ : syracuseStep 6982307 = 10473461) B10473461
theorem B2452145 : Blo 1634016 2452145 := bstep (se 2 (by rfl) ⟨919554, by rfl⟩ : syracuseStep 2452145 = 1839109) B1839109
theorem B3680945 : Blo 1634016 3680945 := bstep (se 2 (by rfl) ⟨1380354, by rfl⟩ : syracuseStep 3680945 = 2760709) B2760709
theorem B2452163 : Blo 1634016 2452163 := bstep (se 1 (by rfl) ⟨1839122, by rfl⟩ : syracuseStep 2452163 = 3678245) B3678245
theorem B3680963 : Blo 1634016 3680963 := bstep (se 1 (by rfl) ⟨2760722, by rfl⟩ : syracuseStep 3680963 = 5521445) B5521445
theorem B2452193 : Blo 1634016 2452193 := bstep (se 2 (by rfl) ⟨919572, by rfl⟩ : syracuseStep 2452193 = 1839145) B1839145
theorem B2452211 : Blo 1634016 2452211 := bstep (se 1 (by rfl) ⟨1839158, by rfl⟩ : syracuseStep 2452211 = 3678317) B3678317
theorem B5516045 : Blo 1634016 5516045 := bstep (se 3 (by rfl) ⟨1034258, by rfl⟩ : syracuseStep 5516045 = 2068517) B2068517
theorem B2452241 : Blo 1634016 2452241 := bstep (se 2 (by rfl) ⟨919590, by rfl⟩ : syracuseStep 2452241 = 1839181) B1839181
theorem B2452259 : Blo 1634016 2452259 := bstep (se 1 (by rfl) ⟨1839194, by rfl⟩ : syracuseStep 2452259 = 3678389) B3678389
theorem B2452289 : Blo 1634016 2452289 := bstep (se 2 (by rfl) ⟨919608, by rfl⟩ : syracuseStep 2452289 = 1839217) B1839217
theorem B5516099 : Blo 1634016 5516099 := bstep (se 1 (by rfl) ⟨4137074, by rfl⟩ : syracuseStep 5516099 = 8274149) B8274149
theorem B2485073 : Blo 1634016 2485073 := bstep (se 2 (by rfl) ⟨931902, by rfl⟩ : syracuseStep 2485073 = 1863805) B1863805
theorem B2452307 : Blo 1634016 2452307 := bstep (se 1 (by rfl) ⟨1839230, by rfl⟩ : syracuseStep 2452307 = 3678461) B3678461
theorem B2452337 : Blo 1634016 2452337 := bstep (se 2 (by rfl) ⟨919626, by rfl⟩ : syracuseStep 2452337 = 1839253) B1839253
theorem B2452355 : Blo 1634016 2452355 := bstep (se 1 (by rfl) ⟨1839266, by rfl⟩ : syracuseStep 2452355 = 3678533) B3678533
theorem B2452385 : Blo 1634016 2452385 := bstep (se 2 (by rfl) ⟨919644, by rfl⟩ : syracuseStep 2452385 = 1839289) B1839289
theorem B2452403 : Blo 1634016 2452403 := bstep (se 1 (by rfl) ⟨1839302, by rfl⟩ : syracuseStep 2452403 = 3678605) B3678605
theorem B2452433 : Blo 1634016 2452433 := bstep (se 2 (by rfl) ⟨919662, by rfl⟩ : syracuseStep 2452433 = 1839325) B1839325
theorem B2452451 : Blo 1634016 2452451 := bstep (se 1 (by rfl) ⟨1839338, by rfl⟩ : syracuseStep 2452451 = 3678677) B3678677
theorem B4656113 : Blo 1634016 4656113 := bstep (se 2 (by rfl) ⟨1746042, by rfl⟩ : syracuseStep 4656113 = 3492085) B3492085
theorem B2452481 : Blo 1634016 2452481 := bstep (se 2 (by rfl) ⟨919680, by rfl⟩ : syracuseStep 2452481 = 1839361) B1839361
theorem B4721681 : Blo 1634016 4721681 := bstep (se 2 (by rfl) ⟨1770630, by rfl⟩ : syracuseStep 4721681 = 3541261) B3541261
theorem B2452499 : Blo 1634016 2452499 := bstep (se 1 (by rfl) ⟨1839374, by rfl⟩ : syracuseStep 2452499 = 3678749) B3678749
theorem B2452529 : Blo 1634016 2452529 := bstep (se 2 (by rfl) ⟨919698, by rfl⟩ : syracuseStep 2452529 = 1839397) B1839397
theorem B2452547 : Blo 1634016 2452547 := bstep (se 1 (by rfl) ⟨1839410, by rfl⟩ : syracuseStep 2452547 = 3678821) B3678821
theorem B5516369 : Blo 1634016 5516369 := bstep (se 2 (by rfl) ⟨2068638, by rfl⟩ : syracuseStep 5516369 = 4137277) B4137277
theorem B2452577 : Blo 1634016 2452577 := bstep (se 2 (by rfl) ⟨919716, by rfl⟩ : syracuseStep 2452577 = 1839433) B1839433
theorem B2452595 : Blo 1634016 2452595 := bstep (se 1 (by rfl) ⟨1839446, by rfl⟩ : syracuseStep 2452595 = 3678893) B3678893
theorem B2452625 : Blo 1634016 2452625 := bstep (se 2 (by rfl) ⟨919734, by rfl⟩ : syracuseStep 2452625 = 1839469) B1839469
theorem B2452643 : Blo 1634016 2452643 := bstep (se 1 (by rfl) ⟨1839482, by rfl⟩ : syracuseStep 2452643 = 3678965) B3678965
theorem B4656305 : Blo 1634016 4656305 := bstep (se 2 (by rfl) ⟨1746114, by rfl⟩ : syracuseStep 4656305 = 3492229) B3492229
theorem B2452673 : Blo 1634016 2452673 := bstep (se 2 (by rfl) ⟨919752, by rfl⟩ : syracuseStep 2452673 = 1839505) B1839505
theorem B2452691 : Blo 1634016 2452691 := bstep (se 1 (by rfl) ⟨1839518, by rfl⟩ : syracuseStep 2452691 = 3679037) B3679037
theorem B2452721 : Blo 1634016 2452721 := bstep (se 2 (by rfl) ⟨919770, by rfl⟩ : syracuseStep 2452721 = 1839541) B1839541
theorem B2452739 : Blo 1634016 2452739 := bstep (se 1 (by rfl) ⟨1839554, by rfl⟩ : syracuseStep 2452739 = 3679109) B3679109
theorem B3312913 : Blo 1634016 3312913 := bstep (se 2 (by rfl) ⟨1242342, by rfl⟩ : syracuseStep 3312913 = 2484685) B2484685
theorem B4140305 : Blo 1634016 4140305 := bstep (se 2 (by rfl) ⟨1552614, by rfl⟩ : syracuseStep 4140305 = 3105229) B3105229
theorem B2452769 : Blo 1634016 2452769 := bstep (se 2 (by rfl) ⟨919788, by rfl⟩ : syracuseStep 2452769 = 1839577) B1839577
theorem B1838371 : Blo 1634016 1838371 := bstep (se 1 (by rfl) ⟨1378778, by rfl⟩ : syracuseStep 1838371 = 2757557) B2757557
theorem B2452787 : Blo 1634016 2452787 := bstep (se 1 (by rfl) ⟨1839590, by rfl⟩ : syracuseStep 2452787 = 3679181) B3679181
theorem B4140355 : Blo 1634016 4140355 := bstep (se 1 (by rfl) ⟨3105266, by rfl⟩ : syracuseStep 4140355 = 6210533) B6210533
theorem B2452817 : Blo 1634016 2452817 := bstep (se 2 (by rfl) ⟨919806, by rfl⟩ : syracuseStep 2452817 = 1839613) B1839613
theorem B2452835 : Blo 1634016 2452835 := bstep (se 1 (by rfl) ⟨1839626, by rfl⟩ : syracuseStep 2452835 = 3679253) B3679253
theorem B7859555 : Blo 1634016 7859555 := bstep (se 1 (by rfl) ⟨5894666, by rfl⟩ : syracuseStep 7859555 = 11789333) B11789333
theorem B3313009 : Blo 1634016 3313009 := bstep (se 2 (by rfl) ⟨1242378, by rfl⟩ : syracuseStep 3313009 = 2484757) B2484757
theorem B2485633 : Blo 1634016 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B2452865 : Blo 1634016 2452865 := bstep (se 2 (by rfl) ⟨919824, by rfl⟩ : syracuseStep 2452865 = 1839649) B1839649
theorem B8277389 : Blo 1634016 8277389 := bstep (se 3 (by rfl) ⟨1552010, by rfl⟩ : syracuseStep 8277389 = 3104021) B3104021
theorem B2452883 : Blo 1634016 2452883 := bstep (se 1 (by rfl) ⟨1839662, by rfl⟩ : syracuseStep 2452883 = 3679325) B3679325
theorem B2452913 : Blo 1634016 2452913 := bstep (se 2 (by rfl) ⟨919842, by rfl⟩ : syracuseStep 2452913 = 1839685) B1839685
theorem B1838515 : Blo 1634016 1838515 := bstep (se 1 (by rfl) ⟨1378886, by rfl⟩ : syracuseStep 1838515 = 2757773) B2757773
theorem B3927491 : Blo 1634016 3927491 := bstep (se 1 (by rfl) ⟨2945618, by rfl⟩ : syracuseStep 3927491 = 5891237) B5891237
theorem B2452931 : Blo 1634016 2452931 := bstep (se 1 (by rfl) ⟨1839698, by rfl⟩ : syracuseStep 2452931 = 3679397) B3679397
theorem B4140497 : Blo 1634016 4140497 := bstep (se 2 (by rfl) ⟨1552686, by rfl⟩ : syracuseStep 4140497 = 3105373) B3105373
theorem B2452961 : Blo 1634016 2452961 := bstep (se 2 (by rfl) ⟨919860, by rfl⟩ : syracuseStep 2452961 = 1839721) B1839721
theorem B2452979 : Blo 1634016 2452979 := bstep (se 1 (by rfl) ⟨1839734, by rfl⟩ : syracuseStep 2452979 = 3679469) B3679469
theorem B2453009 : Blo 1634016 2453009 := bstep (se 2 (by rfl) ⟨919878, by rfl⟩ : syracuseStep 2453009 = 1839757) B1839757
theorem B2453027 : Blo 1634016 2453027 := bstep (se 1 (by rfl) ⟨1839770, by rfl⟩ : syracuseStep 2453027 = 3679541) B3679541
theorem B2453057 : Blo 1634016 2453057 := bstep (se 2 (by rfl) ⟨919896, by rfl⟩ : syracuseStep 2453057 = 1839793) B1839793
theorem B1838659 : Blo 1634016 1838659 := bstep (se 1 (by rfl) ⟨1378994, by rfl⟩ : syracuseStep 1838659 = 2757989) B2757989
theorem B2453075 : Blo 1634016 2453075 := bstep (se 1 (by rfl) ⟨1839806, by rfl⟩ : syracuseStep 2453075 = 3679613) B3679613
theorem B5238371 : Blo 1634016 5238371 := bstep (se 1 (by rfl) ⟨3928778, by rfl⟩ : syracuseStep 5238371 = 7857557) B7857557
theorem B5516909 : Blo 1634016 5516909 := bstep (se 3 (by rfl) ⟨1034420, by rfl⟩ : syracuseStep 5516909 = 2068841) B2068841
theorem B2453105 : Blo 1634016 2453105 := bstep (se 2 (by rfl) ⟨919914, by rfl⟩ : syracuseStep 2453105 = 1839829) B1839829
theorem B2453123 : Blo 1634016 2453123 := bstep (se 1 (by rfl) ⟨1839842, by rfl⟩ : syracuseStep 2453123 = 3679685) B3679685
theorem B2453153 : Blo 1634016 2453153 := bstep (se 2 (by rfl) ⟨919932, by rfl⟩ : syracuseStep 2453153 = 1839865) B1839865
theorem B5516963 : Blo 1634016 5516963 := bstep (se 1 (by rfl) ⟨4137722, by rfl⟩ : syracuseStep 5516963 = 8275445) B8275445
theorem B2453171 : Blo 1634016 2453171 := bstep (se 1 (by rfl) ⟨1839878, by rfl⟩ : syracuseStep 2453171 = 3679757) B3679757
theorem B16789189 : Blo 1634016 16789189 := bstep (se 4 (by rfl) ⟨1573986, by rfl⟩ : syracuseStep 16789189 = 3147973) B3147973
theorem B2453201 : Blo 1634016 2453201 := bstep (se 2 (by rfl) ⟨919950, by rfl⟩ : syracuseStep 2453201 = 1839901) B1839901
theorem B1838803 : Blo 1634016 1838803 := bstep (se 1 (by rfl) ⟨1379102, by rfl⟩ : syracuseStep 1838803 = 2758205) B2758205
theorem B2797267 : Blo 1634016 2797267 := bstep (se 1 (by rfl) ⟨2097950, by rfl⟩ : syracuseStep 2797267 = 4195901) B4195901
theorem B1634019 : Blo 1634016 1634019 := bstep (se 1 (by rfl) ⟨1225514, by rfl⟩ : syracuseStep 1634019 = 2451029) B2451029
theorem B9309923 : Blo 1634016 9309923 := bstep (se 1 (by rfl) ⟨6982442, by rfl⟩ : syracuseStep 9309923 = 13964885) B13964885
theorem B2453219 : Blo 1634016 2453219 := bstep (se 1 (by rfl) ⟨1839914, by rfl⟩ : syracuseStep 2453219 = 3679829) B3679829
theorem B1634035 : Blo 1634016 1634035 := bstep (se 1 (by rfl) ⟨1225526, by rfl⟩ : syracuseStep 1634035 = 2451053) B2451053
theorem B2453249 : Blo 1634016 2453249 := bstep (se 2 (by rfl) ⟨919968, by rfl⟩ : syracuseStep 2453249 = 1839937) B1839937
theorem B1634051 : Blo 1634016 1634051 := bstep (se 1 (by rfl) ⟨1225538, by rfl⟩ : syracuseStep 1634051 = 2451077) B2451077
theorem B1634067 : Blo 1634016 1634067 := bstep (se 1 (by rfl) ⟨1225550, by rfl⟩ : syracuseStep 1634067 = 2451101) B2451101
theorem B2453267 : Blo 1634016 2453267 := bstep (se 1 (by rfl) ⟨1839950, by rfl⟩ : syracuseStep 2453267 = 3679901) B3679901
theorem B1634083 : Blo 1634016 1634083 := bstep (se 1 (by rfl) ⟨1225562, by rfl⟩ : syracuseStep 1634083 = 2451125) B2451125
theorem B2453297 : Blo 1634016 2453297 := bstep (se 2 (by rfl) ⟨919986, by rfl⟩ : syracuseStep 2453297 = 1839973) B1839973
theorem B1634099 : Blo 1634016 1634099 := bstep (se 1 (by rfl) ⟨1225574, by rfl⟩ : syracuseStep 1634099 = 2451149) B2451149
theorem B7860017 : Blo 1634016 7860017 := bstep (se 2 (by rfl) ⟨2947506, by rfl⟩ : syracuseStep 7860017 = 5895013) B5895013
theorem B1634115 : Blo 1634016 1634115 := bstep (se 1 (by rfl) ⟨1225586, by rfl⟩ : syracuseStep 1634115 = 2451173) B2451173
theorem B1863491 : Blo 1634016 1863491 := bstep (se 1 (by rfl) ⟨1397618, by rfl⟩ : syracuseStep 1863491 = 2795237) B2795237
theorem B2453315 : Blo 1634016 2453315 := bstep (se 1 (by rfl) ⟨1839986, by rfl⟩ : syracuseStep 2453315 = 3679973) B3679973
theorem B1634131 : Blo 1634016 1634131 := bstep (se 1 (by rfl) ⟨1225598, by rfl⟩ : syracuseStep 1634131 = 2451197) B2451197
theorem B2453345 : Blo 1634016 2453345 := bstep (se 2 (by rfl) ⟨920004, by rfl⟩ : syracuseStep 2453345 = 1840009) B1840009
theorem B1634147 : Blo 1634016 1634147 := bstep (se 1 (by rfl) ⟨1225610, by rfl⟩ : syracuseStep 1634147 = 2451221) B2451221
theorem B1838947 : Blo 1634016 1838947 := bstep (se 1 (by rfl) ⟨1379210, by rfl⟩ : syracuseStep 1838947 = 2758421) B2758421
theorem B10481507 : Blo 1634016 10481507 := bstep (se 1 (by rfl) ⟨7861130, by rfl⟩ : syracuseStep 10481507 = 15722261) B15722261
theorem B1634163 : Blo 1634016 1634163 := bstep (se 1 (by rfl) ⟨1225622, by rfl⟩ : syracuseStep 1634163 = 2451245) B2451245
theorem B2453363 : Blo 1634016 2453363 := bstep (se 1 (by rfl) ⟨1840022, by rfl⟩ : syracuseStep 2453363 = 3680045) B3680045
theorem B1634179 : Blo 1634016 1634179 := bstep (se 1 (by rfl) ⟨1225634, by rfl⟩ : syracuseStep 1634179 = 2451269) B2451269
theorem B2068355 : Blo 1634016 2068355 := bstep (se 1 (by rfl) ⟨1551266, by rfl⟩ : syracuseStep 2068355 = 3102533) B3102533
theorem B2453393 : Blo 1634016 2453393 := bstep (se 2 (by rfl) ⟨920022, by rfl⟩ : syracuseStep 2453393 = 1840045) B1840045
theorem B1634195 : Blo 1634016 1634195 := bstep (se 1 (by rfl) ⟨1225646, by rfl⟩ : syracuseStep 1634195 = 2451293) B2451293
theorem B1634211 : Blo 1634016 1634211 := bstep (se 1 (by rfl) ⟨1225658, by rfl⟩ : syracuseStep 1634211 = 2451317) B2451317
theorem B2453411 : Blo 1634016 2453411 := bstep (se 1 (by rfl) ⟨1840058, by rfl⟩ : syracuseStep 2453411 = 3680117) B3680117
theorem B5517233 : Blo 1634016 5517233 := bstep (se 2 (by rfl) ⟨2068962, by rfl⟩ : syracuseStep 5517233 = 4137925) B4137925
theorem B1634227 : Blo 1634016 1634227 := bstep (se 1 (by rfl) ⟨1225670, by rfl⟩ : syracuseStep 1634227 = 2451341) B2451341
theorem B2453441 : Blo 1634016 2453441 := bstep (se 2 (by rfl) ⟨920040, by rfl⟩ : syracuseStep 2453441 = 1840081) B1840081
theorem B1634243 : Blo 1634016 1634243 := bstep (se 1 (by rfl) ⟨1225682, by rfl⟩ : syracuseStep 1634243 = 2451365) B2451365
theorem B34467781 : Blo 1634016 34467781 := bstep (se 4 (by rfl) ⟨3231354, by rfl⟩ : syracuseStep 34467781 = 6462709) B6462709
theorem B1634259 : Blo 1634016 1634259 := bstep (se 1 (by rfl) ⟨1225694, by rfl⟩ : syracuseStep 1634259 = 2451389) B2451389
theorem B2453459 : Blo 1634016 2453459 := bstep (se 1 (by rfl) ⟨1840094, by rfl⟩ : syracuseStep 2453459 = 3680189) B3680189
theorem B1634275 : Blo 1634016 1634275 := bstep (se 1 (by rfl) ⟨1225706, by rfl⟩ : syracuseStep 1634275 = 2451413) B2451413
theorem B2453489 : Blo 1634016 2453489 := bstep (se 2 (by rfl) ⟨920058, by rfl⟩ : syracuseStep 2453489 = 1840117) B1840117
theorem B1634291 : Blo 1634016 1634291 := bstep (se 1 (by rfl) ⟨1225718, by rfl⟩ : syracuseStep 1634291 = 2451437) B2451437
theorem B1839091 : Blo 1634016 1839091 := bstep (se 1 (by rfl) ⟨1379318, by rfl⟩ : syracuseStep 1839091 = 2758637) B2758637
theorem B1634307 : Blo 1634016 1634307 := bstep (se 1 (by rfl) ⟨1225730, by rfl⟩ : syracuseStep 1634307 = 2451461) B2451461
theorem B3928067 : Blo 1634016 3928067 := bstep (se 1 (by rfl) ⟨2946050, by rfl⟩ : syracuseStep 3928067 = 5892101) B5892101
theorem B2453507 : Blo 1634016 2453507 := bstep (se 1 (by rfl) ⟨1840130, by rfl⟩ : syracuseStep 2453507 = 3680261) B3680261
theorem B1634323 : Blo 1634016 1634323 := bstep (se 1 (by rfl) ⟨1225742, by rfl⟩ : syracuseStep 1634323 = 2451485) B2451485
theorem B2453537 : Blo 1634016 2453537 := bstep (se 2 (by rfl) ⟨920076, by rfl⟩ : syracuseStep 2453537 = 1840153) B1840153
theorem B1634339 : Blo 1634016 1634339 := bstep (se 1 (by rfl) ⟨1225754, by rfl⟩ : syracuseStep 1634339 = 2451509) B2451509
theorem B1634355 : Blo 1634016 1634355 := bstep (se 1 (by rfl) ⟨1225766, by rfl⟩ : syracuseStep 1634355 = 2451533) B2451533
theorem B2453555 : Blo 1634016 2453555 := bstep (se 1 (by rfl) ⟨1840166, by rfl⟩ : syracuseStep 2453555 = 3680333) B3680333
theorem B1634371 : Blo 1634016 1634371 := bstep (se 1 (by rfl) ⟨1225778, by rfl⟩ : syracuseStep 1634371 = 2451557) B2451557
theorem B3493955 : Blo 1634016 3493955 := bstep (se 1 (by rfl) ⟨2620466, by rfl⟩ : syracuseStep 3493955 = 5240933) B5240933
theorem B9941069 : Blo 1634016 9941069 := bstep (se 3 (by rfl) ⟨1863950, by rfl⟩ : syracuseStep 9941069 = 3727901) B3727901
theorem B2453585 : Blo 1634016 2453585 := bstep (se 2 (by rfl) ⟨920094, by rfl⟩ : syracuseStep 2453585 = 1840189) B1840189
theorem B1634387 : Blo 1634016 1634387 := bstep (se 1 (by rfl) ⟨1225790, by rfl⟩ : syracuseStep 1634387 = 2451581) B2451581
theorem B1634403 : Blo 1634016 1634403 := bstep (se 1 (by rfl) ⟨1225802, by rfl⟩ : syracuseStep 1634403 = 2451605) B2451605
theorem B2453603 : Blo 1634016 2453603 := bstep (se 1 (by rfl) ⟨1840202, by rfl⟩ : syracuseStep 2453603 = 3680405) B3680405
theorem B1634419 : Blo 1634016 1634419 := bstep (se 1 (by rfl) ⟨1225814, by rfl⟩ : syracuseStep 1634419 = 2451629) B2451629
theorem B2453633 : Blo 1634016 2453633 := bstep (se 2 (by rfl) ⟨920112, by rfl⟩ : syracuseStep 2453633 = 1840225) B1840225
theorem B1634435 : Blo 1634016 1634435 := bstep (se 1 (by rfl) ⟨1225826, by rfl⟩ : syracuseStep 1634435 = 2451653) B2451653
theorem B1839235 : Blo 1634016 1839235 := bstep (se 1 (by rfl) ⟨1379426, by rfl⟩ : syracuseStep 1839235 = 2758853) B2758853
theorem B4657297 : Blo 1634016 4657297 := bstep (se 2 (by rfl) ⟨1746486, by rfl⟩ : syracuseStep 4657297 = 3492973) B3492973
theorem B1634451 : Blo 1634016 1634451 := bstep (se 1 (by rfl) ⟨1225838, by rfl⟩ : syracuseStep 1634451 = 2451677) B2451677
theorem B2453651 : Blo 1634016 2453651 := bstep (se 1 (by rfl) ⟨1840238, by rfl⟩ : syracuseStep 2453651 = 3680477) B3680477
theorem B1634467 : Blo 1634016 1634467 := bstep (se 1 (by rfl) ⟨1225850, by rfl⟩ : syracuseStep 1634467 = 2451701) B2451701
theorem B2453681 : Blo 1634016 2453681 := bstep (se 2 (by rfl) ⟨920130, by rfl⟩ : syracuseStep 2453681 = 1840261) B1840261
theorem B1634483 : Blo 1634016 1634483 := bstep (se 1 (by rfl) ⟨1225862, by rfl⟩ : syracuseStep 1634483 = 2451725) B2451725
theorem B1634499 : Blo 1634016 1634499 := bstep (se 1 (by rfl) ⟨1225874, by rfl⟩ : syracuseStep 1634499 = 2451749) B2451749
theorem B3928259 : Blo 1634016 3928259 := bstep (se 1 (by rfl) ⟨2946194, by rfl⟩ : syracuseStep 3928259 = 5892389) B5892389
theorem B2453699 : Blo 1634016 2453699 := bstep (se 1 (by rfl) ⟨1840274, by rfl⟩ : syracuseStep 2453699 = 3680549) B3680549
theorem B1634515 : Blo 1634016 1634515 := bstep (se 1 (by rfl) ⟨1225886, by rfl⟩ : syracuseStep 1634515 = 2451773) B2451773
theorem B2453729 : Blo 1634016 2453729 := bstep (se 2 (by rfl) ⟨920148, by rfl⟩ : syracuseStep 2453729 = 1840297) B1840297
theorem B1634531 : Blo 1634016 1634531 := bstep (se 1 (by rfl) ⟨1225898, by rfl⟩ : syracuseStep 1634531 = 2451797) B2451797
theorem B9441521 : Blo 1634016 9441521 := bstep (se 2 (by rfl) ⟨3540570, by rfl⟩ : syracuseStep 9441521 = 7081141) B7081141
theorem B1634547 : Blo 1634016 1634547 := bstep (se 1 (by rfl) ⟨1225910, by rfl⟩ : syracuseStep 1634547 = 2451821) B2451821
theorem B2453747 : Blo 1634016 2453747 := bstep (se 1 (by rfl) ⟨1840310, by rfl⟩ : syracuseStep 2453747 = 3680621) B3680621
theorem B1634563 : Blo 1634016 1634563 := bstep (se 1 (by rfl) ⟨1225922, by rfl⟩ : syracuseStep 1634563 = 2451845) B2451845
theorem B2453777 : Blo 1634016 2453777 := bstep (se 2 (by rfl) ⟨920166, by rfl⟩ : syracuseStep 2453777 = 1840333) B1840333
theorem B1634579 : Blo 1634016 1634579 := bstep (se 1 (by rfl) ⟨1225934, by rfl⟩ : syracuseStep 1634579 = 2451869) B2451869
theorem B1839379 : Blo 1634016 1839379 := bstep (se 1 (by rfl) ⟨1379534, by rfl⟩ : syracuseStep 1839379 = 2759069) B2759069
theorem B1634595 : Blo 1634016 1634595 := bstep (se 1 (by rfl) ⟨1225946, by rfl⟩ : syracuseStep 1634595 = 2451893) B2451893
theorem B2453795 : Blo 1634016 2453795 := bstep (se 1 (by rfl) ⟨1840346, by rfl⟩ : syracuseStep 2453795 = 3680693) B3680693
theorem B1634611 : Blo 1634016 1634611 := bstep (se 1 (by rfl) ⟨1225958, by rfl⟩ : syracuseStep 1634611 = 2451917) B2451917
theorem B2453825 : Blo 1634016 2453825 := bstep (se 2 (by rfl) ⟨920184, by rfl⟩ : syracuseStep 2453825 = 1840369) B1840369
theorem B1634627 : Blo 1634016 1634627 := bstep (se 1 (by rfl) ⟨1225970, by rfl⟩ : syracuseStep 1634627 = 2451941) B2451941
theorem B1634643 : Blo 1634016 1634643 := bstep (se 1 (by rfl) ⟨1225982, by rfl⟩ : syracuseStep 1634643 = 2451965) B2451965
theorem B2453843 : Blo 1634016 2453843 := bstep (se 1 (by rfl) ⟨1840382, by rfl⟩ : syracuseStep 2453843 = 3680765) B3680765
theorem B2617699 : Blo 1634016 2617699 := bstep (se 1 (by rfl) ⟨1963274, by rfl⟩ : syracuseStep 2617699 = 3926549) B3926549
theorem B1634659 : Blo 1634016 1634659 := bstep (se 1 (by rfl) ⟨1225994, by rfl⟩ : syracuseStep 1634659 = 2451989) B2451989
theorem B2453873 : Blo 1634016 2453873 := bstep (se 2 (by rfl) ⟨920202, by rfl⟩ : syracuseStep 2453873 = 1840405) B1840405
theorem B1634675 : Blo 1634016 1634675 := bstep (se 1 (by rfl) ⟨1226006, by rfl⟩ : syracuseStep 1634675 = 2452013) B2452013
theorem B1634691 : Blo 1634016 1634691 := bstep (se 1 (by rfl) ⟨1226018, by rfl⟩ : syracuseStep 1634691 = 2452037) B2452037
theorem B2453891 : Blo 1634016 2453891 := bstep (se 1 (by rfl) ⟨1840418, by rfl⟩ : syracuseStep 2453891 = 3680837) B3680837
theorem B1634707 : Blo 1634016 1634707 := bstep (se 1 (by rfl) ⟨1226030, by rfl⟩ : syracuseStep 1634707 = 2452061) B2452061
theorem B2453921 : Blo 1634016 2453921 := bstep (se 2 (by rfl) ⟨920220, by rfl⟩ : syracuseStep 2453921 = 1840441) B1840441
theorem B1634723 : Blo 1634016 1634723 := bstep (se 1 (by rfl) ⟨1226042, by rfl⟩ : syracuseStep 1634723 = 2452085) B2452085
theorem B1839523 : Blo 1634016 1839523 := bstep (se 1 (by rfl) ⟨1379642, by rfl⟩ : syracuseStep 1839523 = 2759285) B2759285
theorem B7459235 : Blo 1634016 7459235 := bstep (se 1 (by rfl) ⟨5594426, by rfl⟩ : syracuseStep 7459235 = 11188853) B11188853
theorem B4657571 : Blo 1634016 4657571 := bstep (se 1 (by rfl) ⟨3493178, by rfl⟩ : syracuseStep 4657571 = 6986357) B6986357
theorem B1634739 : Blo 1634016 1634739 := bstep (se 1 (by rfl) ⟨1226054, by rfl⟩ : syracuseStep 1634739 = 2452109) B2452109
theorem B2453939 : Blo 1634016 2453939 := bstep (se 1 (by rfl) ⟨1840454, by rfl⟩ : syracuseStep 2453939 = 3680909) B3680909
theorem B1634755 : Blo 1634016 1634755 := bstep (se 1 (by rfl) ⟨1226066, by rfl⟩ : syracuseStep 1634755 = 2452133) B2452133
theorem B5517773 : Blo 1634016 5517773 := bstep (se 3 (by rfl) ⟨1034582, by rfl⟩ : syracuseStep 5517773 = 2069165) B2069165
theorem B2453969 : Blo 1634016 2453969 := bstep (se 2 (by rfl) ⟨920238, by rfl⟩ : syracuseStep 2453969 = 1840477) B1840477
theorem B1634771 : Blo 1634016 1634771 := bstep (se 1 (by rfl) ⟨1226078, by rfl⟩ : syracuseStep 1634771 = 2452157) B2452157
theorem B1634787 : Blo 1634016 1634787 := bstep (se 1 (by rfl) ⟨1226090, by rfl⟩ : syracuseStep 1634787 = 2452181) B2452181
theorem B3928547 : Blo 1634016 3928547 := bstep (se 1 (by rfl) ⟨2946410, by rfl⟩ : syracuseStep 3928547 = 5892821) B5892821
theorem B2453987 : Blo 1634016 2453987 := bstep (se 1 (by rfl) ⟨1840490, by rfl⟩ : syracuseStep 2453987 = 3680981) B3680981
theorem B1634803 : Blo 1634016 1634803 := bstep (se 1 (by rfl) ⟨1226102, by rfl⟩ : syracuseStep 1634803 = 2452205) B2452205
theorem B1634819 : Blo 1634016 1634819 := bstep (se 1 (by rfl) ⟨1226114, by rfl⟩ : syracuseStep 1634819 = 2452229) B2452229
theorem B5517827 : Blo 1634016 5517827 := bstep (se 1 (by rfl) ⟨4138370, by rfl⟩ : syracuseStep 5517827 = 8276741) B8276741
theorem B2454017 : Blo 1634016 2454017 := bstep (se 2 (by rfl) ⟨920256, by rfl⟩ : syracuseStep 2454017 = 1840513) B1840513
theorem B1634835 : Blo 1634016 1634835 := bstep (se 1 (by rfl) ⟨1226126, by rfl⟩ : syracuseStep 1634835 = 2452253) B2452253
theorem B1634851 : Blo 1634016 1634851 := bstep (se 1 (by rfl) ⟨1226138, by rfl⟩ : syracuseStep 1634851 = 2452277) B2452277
theorem B1634867 : Blo 1634016 1634867 := bstep (se 1 (by rfl) ⟨1226150, by rfl⟩ : syracuseStep 1634867 = 2452301) B2452301
theorem B1839667 : Blo 1634016 1839667 := bstep (se 1 (by rfl) ⟨1379750, by rfl⟩ : syracuseStep 1839667 = 2759501) B2759501
theorem B2069059 : Blo 1634016 2069059 := bstep (se 1 (by rfl) ⟨1551794, by rfl⟩ : syracuseStep 2069059 = 3103589) B3103589
theorem B1634883 : Blo 1634016 1634883 := bstep (se 1 (by rfl) ⟨1226162, by rfl⟩ : syracuseStep 1634883 = 2452325) B2452325
theorem B1634899 : Blo 1634016 1634899 := bstep (se 1 (by rfl) ⟨1226174, by rfl⟩ : syracuseStep 1634899 = 2452349) B2452349
theorem B1634915 : Blo 1634016 1634915 := bstep (se 1 (by rfl) ⟨1226186, by rfl⟩ : syracuseStep 1634915 = 2452373) B2452373
theorem B4657763 : Blo 1634016 4657763 := bstep (se 1 (by rfl) ⟨3493322, by rfl⟩ : syracuseStep 4657763 = 6986645) B6986645
theorem B1634931 : Blo 1634016 1634931 := bstep (se 1 (by rfl) ⟨1226198, by rfl⟩ : syracuseStep 1634931 = 2452397) B2452397
theorem B1634947 : Blo 1634016 1634947 := bstep (se 1 (by rfl) ⟨1226210, by rfl⟩ : syracuseStep 1634947 = 2452421) B2452421
theorem B1634963 : Blo 1634016 1634963 := bstep (se 1 (by rfl) ⟨1226222, by rfl⟩ : syracuseStep 1634963 = 2452445) B2452445
theorem B2069155 : Blo 1634016 2069155 := bstep (se 1 (by rfl) ⟨1551866, by rfl⟩ : syracuseStep 2069155 = 3103733) B3103733
theorem B1634979 : Blo 1634016 1634979 := bstep (se 1 (by rfl) ⟨1226234, by rfl⟩ : syracuseStep 1634979 = 2452469) B2452469
theorem B6206129 : Blo 1634016 6206129 := bstep (se 2 (by rfl) ⟨2327298, by rfl⟩ : syracuseStep 6206129 = 4654597) B4654597
theorem B1634995 : Blo 1634016 1634995 := bstep (se 1 (by rfl) ⟨1226246, by rfl⟩ : syracuseStep 1634995 = 2452493) B2452493
theorem B1635011 : Blo 1634016 1635011 := bstep (se 1 (by rfl) ⟨1226258, by rfl⟩ : syracuseStep 1635011 = 2452517) B2452517
theorem B1839811 : Blo 1634016 1839811 := bstep (se 1 (by rfl) ⟨1379858, by rfl⟩ : syracuseStep 1839811 = 2759717) B2759717
theorem B1635027 : Blo 1634016 1635027 := bstep (se 1 (by rfl) ⟨1226270, by rfl⟩ : syracuseStep 1635027 = 2452541) B2452541
theorem B1635043 : Blo 1634016 1635043 := bstep (se 1 (by rfl) ⟨1226282, by rfl⟩ : syracuseStep 1635043 = 2452565) B2452565
theorem B1635059 : Blo 1634016 1635059 := bstep (se 1 (by rfl) ⟨1226294, by rfl⟩ : syracuseStep 1635059 = 2452589) B2452589
theorem B1635075 : Blo 1634016 1635075 := bstep (se 1 (by rfl) ⟨1226306, by rfl⟩ : syracuseStep 1635075 = 2452613) B2452613
theorem B5518097 : Blo 1634016 5518097 := bstep (se 2 (by rfl) ⟨2069286, by rfl⟩ : syracuseStep 5518097 = 4138573) B4138573
theorem B1635091 : Blo 1634016 1635091 := bstep (se 1 (by rfl) ⟨1226318, by rfl⟩ : syracuseStep 1635091 = 2452637) B2452637
theorem B2618147 : Blo 1634016 2618147 := bstep (se 1 (by rfl) ⟨1963610, by rfl⟩ : syracuseStep 2618147 = 3927221) B3927221
theorem B1635107 : Blo 1634016 1635107 := bstep (se 1 (by rfl) ⟨1226330, by rfl⟩ : syracuseStep 1635107 = 2452661) B2452661
theorem B1635123 : Blo 1634016 1635123 := bstep (se 1 (by rfl) ⟨1226342, by rfl⟩ : syracuseStep 1635123 = 2452685) B2452685
theorem B1635139 : Blo 1634016 1635139 := bstep (se 1 (by rfl) ⟨1226354, by rfl⟩ : syracuseStep 1635139 = 2452709) B2452709
theorem B1635155 : Blo 1634016 1635155 := bstep (se 1 (by rfl) ⟨1226366, by rfl⟩ : syracuseStep 1635155 = 2452733) B2452733
theorem B1839955 : Blo 1634016 1839955 := bstep (se 1 (by rfl) ⟨1379966, by rfl⟩ : syracuseStep 1839955 = 2759933) B2759933
theorem B1635171 : Blo 1634016 1635171 := bstep (se 1 (by rfl) ⟨1226378, by rfl⟩ : syracuseStep 1635171 = 2452757) B2452757
theorem B18617201 : Blo 1634016 18617201 := bstep (se 2 (by rfl) ⟨6981450, by rfl⟩ : syracuseStep 18617201 = 13962901) B13962901
theorem B1635187 : Blo 1634016 1635187 := bstep (se 1 (by rfl) ⟨1226390, by rfl⟩ : syracuseStep 1635187 = 2452781) B2452781
theorem B1635203 : Blo 1634016 1635203 := bstep (se 1 (by rfl) ⟨1226402, by rfl⟩ : syracuseStep 1635203 = 2452805) B2452805
theorem B2757523 : Blo 1634016 2757523 := bstep (se 1 (by rfl) ⟨2068142, by rfl⟩ : syracuseStep 2757523 = 4136285) B4136285
theorem B1635219 : Blo 1634016 1635219 := bstep (se 1 (by rfl) ⟨1226414, by rfl⟩ : syracuseStep 1635219 = 2452829) B2452829
theorem B1635235 : Blo 1634016 1635235 := bstep (se 1 (by rfl) ⟨1226426, by rfl⟩ : syracuseStep 1635235 = 2452853) B2452853
theorem B1635251 : Blo 1634016 1635251 := bstep (se 1 (by rfl) ⟨1226438, by rfl⟩ : syracuseStep 1635251 = 2452877) B2452877
theorem B1635267 : Blo 1634016 1635267 := bstep (se 1 (by rfl) ⟨1226450, by rfl⟩ : syracuseStep 1635267 = 2452901) B2452901
theorem B1635283 : Blo 1634016 1635283 := bstep (se 1 (by rfl) ⟨1226462, by rfl⟩ : syracuseStep 1635283 = 2452925) B2452925
theorem B1635299 : Blo 1634016 1635299 := bstep (se 1 (by rfl) ⟨1226474, by rfl⟩ : syracuseStep 1635299 = 2452949) B2452949
theorem B1840099 : Blo 1634016 1840099 := bstep (se 1 (by rfl) ⟨1380074, by rfl⟩ : syracuseStep 1840099 = 2760149) B2760149
theorem B1635315 : Blo 1634016 1635315 := bstep (se 1 (by rfl) ⟨1226486, by rfl⟩ : syracuseStep 1635315 = 2452973) B2452973
theorem B1635331 : Blo 1634016 1635331 := bstep (se 1 (by rfl) ⟨1226498, by rfl⟩ : syracuseStep 1635331 = 2452997) B2452997
theorem B1635347 : Blo 1634016 1635347 := bstep (se 1 (by rfl) ⟨1226510, by rfl⟩ : syracuseStep 1635347 = 2453021) B2453021
theorem B2757665 : Blo 1634016 2757665 := bstep (se 2 (by rfl) ⟨1034124, by rfl⟩ : syracuseStep 2757665 = 2068249) B2068249
theorem B1635363 : Blo 1634016 1635363 := bstep (se 1 (by rfl) ⟨1226522, by rfl⟩ : syracuseStep 1635363 = 2453045) B2453045
theorem B1635379 : Blo 1634016 1635379 := bstep (se 1 (by rfl) ⟨1226534, by rfl⟩ : syracuseStep 1635379 = 2453069) B2453069
theorem B1635395 : Blo 1634016 1635395 := bstep (se 1 (by rfl) ⟨1226546, by rfl⟩ : syracuseStep 1635395 = 2453093) B2453093
theorem B1635411 : Blo 1634016 1635411 := bstep (se 1 (by rfl) ⟨1226558, by rfl⟩ : syracuseStep 1635411 = 2453117) B2453117
theorem B1635427 : Blo 1634016 1635427 := bstep (se 1 (by rfl) ⟨1226570, by rfl⟩ : syracuseStep 1635427 = 2453141) B2453141
theorem B1635443 : Blo 1634016 1635443 := bstep (se 1 (by rfl) ⟨1226582, by rfl⟩ : syracuseStep 1635443 = 2453165) B2453165
theorem B1840243 : Blo 1634016 1840243 := bstep (se 1 (by rfl) ⟨1380182, by rfl⟩ : syracuseStep 1840243 = 2760365) B2760365
theorem B1635459 : Blo 1634016 1635459 := bstep (se 1 (by rfl) ⟨1226594, by rfl⟩ : syracuseStep 1635459 = 2453189) B2453189
theorem B2069651 : Blo 1634016 2069651 := bstep (se 1 (by rfl) ⟨1552238, by rfl⟩ : syracuseStep 2069651 = 3104477) B3104477
theorem B1635475 : Blo 1634016 1635475 := bstep (se 1 (by rfl) ⟨1226606, by rfl⟩ : syracuseStep 1635475 = 2453213) B2453213
theorem B2757793 : Blo 1634016 2757793 := bstep (se 2 (by rfl) ⟨1034172, by rfl⟩ : syracuseStep 2757793 = 2068345) B2068345
theorem B1635491 : Blo 1634016 1635491 := bstep (se 1 (by rfl) ⟨1226618, by rfl⟩ : syracuseStep 1635491 = 2453237) B2453237
theorem B1635507 : Blo 1634016 1635507 := bstep (se 1 (by rfl) ⟨1226630, by rfl⟩ : syracuseStep 1635507 = 2453261) B2453261
theorem B2757827 : Blo 1634016 2757827 := bstep (se 1 (by rfl) ⟨2068370, by rfl⟩ : syracuseStep 2757827 = 4136741) B4136741
theorem B1635523 : Blo 1634016 1635523 := bstep (se 1 (by rfl) ⟨1226642, by rfl⟩ : syracuseStep 1635523 = 2453285) B2453285
theorem B1635539 : Blo 1634016 1635539 := bstep (se 1 (by rfl) ⟨1226654, by rfl⟩ : syracuseStep 1635539 = 2453309) B2453309
theorem B23893219 : Blo 1634016 23893219 := bstep (se 1 (by rfl) ⟨17919914, by rfl⟩ : syracuseStep 23893219 = 35839829) B35839829
theorem B1635555 : Blo 1634016 1635555 := bstep (se 1 (by rfl) ⟨1226666, by rfl⟩ : syracuseStep 1635555 = 2453333) B2453333
theorem B1635571 : Blo 1634016 1635571 := bstep (se 1 (by rfl) ⟨1226678, by rfl⟩ : syracuseStep 1635571 = 2453357) B2453357
theorem B1635587 : Blo 1634016 1635587 := bstep (se 1 (by rfl) ⟨1226690, by rfl⟩ : syracuseStep 1635587 = 2453381) B2453381
theorem B1840387 : Blo 1634016 1840387 := bstep (se 1 (by rfl) ⟨1380290, by rfl⟩ : syracuseStep 1840387 = 2760581) B2760581
theorem B1635603 : Blo 1634016 1635603 := bstep (se 1 (by rfl) ⟨1226702, by rfl⟩ : syracuseStep 1635603 = 2453405) B2453405
theorem B1635619 : Blo 1634016 1635619 := bstep (se 1 (by rfl) ⟨1226714, by rfl⟩ : syracuseStep 1635619 = 2453429) B2453429
theorem B5518637 : Blo 1634016 5518637 := bstep (se 3 (by rfl) ⟨1034744, by rfl⟩ : syracuseStep 5518637 = 2069489) B2069489
theorem B1635635 : Blo 1634016 1635635 := bstep (se 1 (by rfl) ⟨1226726, by rfl⟩ : syracuseStep 1635635 = 2453453) B2453453
theorem B2757955 : Blo 1634016 2757955 := bstep (se 1 (by rfl) ⟨2068466, by rfl⟩ : syracuseStep 2757955 = 4136933) B4136933
theorem B1865027 : Blo 1634016 1865027 := bstep (se 1 (by rfl) ⟨1398770, by rfl⟩ : syracuseStep 1865027 = 2797541) B2797541
theorem B3028291 : Blo 1634016 3028291 := bstep (se 1 (by rfl) ⟨2271218, by rfl⟩ : syracuseStep 3028291 = 4542437) B4542437
theorem B1635651 : Blo 1634016 1635651 := bstep (se 1 (by rfl) ⟨1226738, by rfl⟩ : syracuseStep 1635651 = 2453477) B2453477
theorem B2618705 : Blo 1634016 2618705 := bstep (se 2 (by rfl) ⟨982014, by rfl⟩ : syracuseStep 2618705 = 1964029) B1964029
theorem B1635667 : Blo 1634016 1635667 := bstep (se 1 (by rfl) ⟨1226750, by rfl⟩ : syracuseStep 1635667 = 2453501) B2453501
theorem B5518691 : Blo 1634016 5518691 := bstep (se 1 (by rfl) ⟨4139018, by rfl⟩ : syracuseStep 5518691 = 8278037) B8278037
theorem B1635683 : Blo 1634016 1635683 := bstep (se 1 (by rfl) ⟨1226762, by rfl⟩ : syracuseStep 1635683 = 2453525) B2453525
theorem B1635699 : Blo 1634016 1635699 := bstep (se 1 (by rfl) ⟨1226774, by rfl⟩ : syracuseStep 1635699 = 2453549) B2453549
theorem B1635715 : Blo 1634016 1635715 := bstep (se 1 (by rfl) ⟨1226786, by rfl⟩ : syracuseStep 1635715 = 2453573) B2453573
theorem B4658573 : Blo 1634016 4658573 := bstep (se 3 (by rfl) ⟨873482, by rfl⟩ : syracuseStep 4658573 = 1746965) B1746965
theorem B3929489 : Blo 1634016 3929489 := bstep (se 2 (by rfl) ⟨1473558, by rfl⟩ : syracuseStep 3929489 = 2947117) B2947117
theorem B1635731 : Blo 1634016 1635731 := bstep (se 1 (by rfl) ⟨1226798, by rfl⟩ : syracuseStep 1635731 = 2453597) B2453597
theorem B1635747 : Blo 1634016 1635747 := bstep (se 1 (by rfl) ⟨1226810, by rfl⟩ : syracuseStep 1635747 = 2453621) B2453621
theorem B1635763 : Blo 1634016 1635763 := bstep (se 1 (by rfl) ⟨1226822, by rfl⟩ : syracuseStep 1635763 = 2453645) B2453645
theorem B1635779 : Blo 1634016 1635779 := bstep (se 1 (by rfl) ⟨1226834, by rfl⟩ : syracuseStep 1635779 = 2453669) B2453669
theorem B2758097 : Blo 1634016 2758097 := bstep (se 2 (by rfl) ⟨1034286, by rfl⟩ : syracuseStep 2758097 = 2068573) B2068573
theorem B1635795 : Blo 1634016 1635795 := bstep (se 1 (by rfl) ⟨1226846, by rfl⟩ : syracuseStep 1635795 = 2453693) B2453693
theorem B1635811 : Blo 1634016 1635811 := bstep (se 1 (by rfl) ⟨1226858, by rfl⟩ : syracuseStep 1635811 = 2453717) B2453717
theorem B7083491 : Blo 1634016 7083491 := bstep (se 1 (by rfl) ⟨5312618, by rfl⟩ : syracuseStep 7083491 = 10625237) B10625237
theorem B1635827 : Blo 1634016 1635827 := bstep (se 1 (by rfl) ⟨1226870, by rfl⟩ : syracuseStep 1635827 = 2453741) B2453741
theorem B1635843 : Blo 1634016 1635843 := bstep (se 1 (by rfl) ⟨1226882, by rfl⟩ : syracuseStep 1635843 = 2453765) B2453765
theorem B1635859 : Blo 1634016 1635859 := bstep (se 1 (by rfl) ⟨1226894, by rfl⟩ : syracuseStep 1635859 = 2453789) B2453789
theorem B1635875 : Blo 1634016 1635875 := bstep (se 1 (by rfl) ⟨1226906, by rfl⟩ : syracuseStep 1635875 = 2453813) B2453813
theorem B2618929 : Blo 1634016 2618929 := bstep (se 2 (by rfl) ⟨982098, by rfl⟩ : syracuseStep 2618929 = 1964197) B1964197
theorem B1635891 : Blo 1634016 1635891 := bstep (se 1 (by rfl) ⟨1226918, by rfl⟩ : syracuseStep 1635891 = 2453837) B2453837
theorem B3102275 : Blo 1634016 3102275 := bstep (se 1 (by rfl) ⟨2326706, by rfl⟩ : syracuseStep 3102275 = 4653413) B4653413
theorem B1635907 : Blo 1634016 1635907 := bstep (se 1 (by rfl) ⟨1226930, by rfl⟩ : syracuseStep 1635907 = 2453861) B2453861
theorem B4658755 : Blo 1634016 4658755 := bstep (se 1 (by rfl) ⟨3494066, by rfl⟩ : syracuseStep 4658755 = 6988133) B6988133
theorem B2758225 : Blo 1634016 2758225 := bstep (se 2 (by rfl) ⟨1034334, by rfl⟩ : syracuseStep 2758225 = 2068669) B2068669
theorem B3929681 : Blo 1634016 3929681 := bstep (se 2 (by rfl) ⟨1473630, by rfl⟩ : syracuseStep 3929681 = 2947261) B2947261
theorem B1635923 : Blo 1634016 1635923 := bstep (se 1 (by rfl) ⟨1226942, by rfl⟩ : syracuseStep 1635923 = 2453885) B2453885
theorem B16782947 : Blo 1634016 16782947 := bstep (se 1 (by rfl) ⟨12587210, by rfl⟩ : syracuseStep 16782947 = 25174421) B25174421
theorem B1635939 : Blo 1634016 1635939 := bstep (se 1 (by rfl) ⟨1226954, by rfl⟩ : syracuseStep 1635939 = 2453909) B2453909
theorem B2618993 : Blo 1634016 2618993 := bstep (se 2 (by rfl) ⟨982122, by rfl⟩ : syracuseStep 2618993 = 1964245) B1964245
theorem B5518961 : Blo 1634016 5518961 := bstep (se 2 (by rfl) ⟨2069610, by rfl⟩ : syracuseStep 5518961 = 4139221) B4139221
theorem B2758259 : Blo 1634016 2758259 := bstep (se 1 (by rfl) ⟨2068694, by rfl⟩ : syracuseStep 2758259 = 4137389) B4137389
theorem B1635955 : Blo 1634016 1635955 := bstep (se 1 (by rfl) ⟨1226966, by rfl⟩ : syracuseStep 1635955 = 2453933) B2453933
theorem B1635971 : Blo 1634016 1635971 := bstep (se 1 (by rfl) ⟨1226978, by rfl⟩ : syracuseStep 1635971 = 2453957) B2453957
theorem B1635987 : Blo 1634016 1635987 := bstep (se 1 (by rfl) ⟨1226990, by rfl⟩ : syracuseStep 1635987 = 2453981) B2453981
theorem B1636003 : Blo 1634016 1636003 := bstep (se 1 (by rfl) ⟨1227002, by rfl⟩ : syracuseStep 1636003 = 2454005) B2454005
theorem B5240497 : Blo 1634016 5240497 := bstep (se 2 (by rfl) ⟨1965186, by rfl⟩ : syracuseStep 5240497 = 3930373) B3930373
theorem B2619121 : Blo 1634016 2619121 := bstep (se 2 (by rfl) ⟨982170, by rfl⟩ : syracuseStep 2619121 = 1964341) B1964341
theorem B2758387 : Blo 1634016 2758387 := bstep (se 1 (by rfl) ⟨2068790, by rfl⟩ : syracuseStep 2758387 = 4137581) B4137581
theorem B4421411 : Blo 1634016 4421411 := bstep (se 1 (by rfl) ⟨3316058, by rfl⟩ : syracuseStep 4421411 = 6632117) B6632117
theorem B4970317 : Blo 1634016 4970317 := bstep (se 3 (by rfl) ⟨931934, by rfl⟩ : syracuseStep 4970317 = 1863869) B1863869
theorem B2070355 : Blo 1634016 2070355 := bstep (se 1 (by rfl) ⟨1552766, by rfl⟩ : syracuseStep 2070355 = 3105533) B3105533
theorem B3102563 : Blo 1634016 3102563 := bstep (se 1 (by rfl) ⟨2326922, by rfl⟩ : syracuseStep 3102563 = 4653845) B4653845
theorem B17667953 : Blo 1634016 17667953 := bstep (se 2 (by rfl) ⟨6625482, by rfl⟩ : syracuseStep 17667953 = 13250965) B13250965
theorem B2758529 : Blo 1634016 2758529 := bstep (se 2 (by rfl) ⟨1034448, by rfl⟩ : syracuseStep 2758529 = 2068897) B2068897
theorem B2070451 : Blo 1634016 2070451 := bstep (se 1 (by rfl) ⟨1552838, by rfl⟩ : syracuseStep 2070451 = 3105677) B3105677
theorem B2521025 : Blo 1634016 2521025 := bstep (se 2 (by rfl) ⟨945384, by rfl⟩ : syracuseStep 2521025 = 1890769) B1890769
theorem B21239779 : Blo 1634016 21239779 := bstep (se 1 (by rfl) ⟨15929834, by rfl⟩ : syracuseStep 21239779 = 31859669) B31859669
theorem B2758657 : Blo 1634016 2758657 := bstep (se 2 (by rfl) ⟨1034496, by rfl⟩ : syracuseStep 2758657 = 2068993) B2068993
theorem B2758691 : Blo 1634016 2758691 := bstep (se 1 (by rfl) ⟨2069018, by rfl⟩ : syracuseStep 2758691 = 4138037) B4138037
theorem B4970573 : Blo 1634016 4970573 := bstep (se 3 (by rfl) ⟨931982, by rfl⟩ : syracuseStep 4970573 = 1863965) B1863965
theorem B6207587 : Blo 1634016 6207587 := bstep (se 1 (by rfl) ⟨4655690, by rfl⟩ : syracuseStep 6207587 = 9311381) B9311381
theorem B5519501 : Blo 1634016 5519501 := bstep (se 3 (by rfl) ⟨1034906, by rfl⟩ : syracuseStep 5519501 = 2069813) B2069813
theorem B2758819 : Blo 1634016 2758819 := bstep (se 1 (by rfl) ⟨2069114, by rfl⟩ : syracuseStep 2758819 = 4138229) B4138229
theorem B5519555 : Blo 1634016 5519555 := bstep (se 1 (by rfl) ⟨4139666, by rfl⟩ : syracuseStep 5519555 = 8279333) B8279333
theorem B8280305 : Blo 1634016 8280305 := bstep (se 2 (by rfl) ⟨3105114, by rfl⟩ : syracuseStep 8280305 = 6210229) B6210229
theorem B11778317 : Blo 1634016 11778317 := bstep (se 3 (by rfl) ⟨2208434, by rfl⟩ : syracuseStep 11778317 = 4416869) B4416869
theorem B6985997 : Blo 1634016 6985997 := bstep (se 3 (by rfl) ⟨1309874, by rfl⟩ : syracuseStep 6985997 = 2619749) B2619749
theorem B2758961 : Blo 1634016 2758961 := bstep (se 2 (by rfl) ⟨1034610, by rfl⟩ : syracuseStep 2758961 = 2069221) B2069221
theorem B8395085 : Blo 1634016 8395085 := bstep (se 3 (by rfl) ⟨1574078, by rfl⟩ : syracuseStep 8395085 = 3148157) B3148157
theorem B3930449 : Blo 1634016 3930449 := bstep (se 2 (by rfl) ⟨1473918, by rfl⟩ : syracuseStep 3930449 = 2947837) B2947837
theorem B2759089 : Blo 1634016 2759089 := bstep (se 2 (by rfl) ⟨1034658, by rfl⟩ : syracuseStep 2759089 = 2069317) B2069317
theorem B9943501 : Blo 1634016 9943501 := bstep (se 3 (by rfl) ⟨1864406, by rfl⟩ : syracuseStep 9943501 = 3728813) B3728813
theorem B3676625 : Blo 1634016 3676625 := bstep (se 2 (by rfl) ⟨1378734, by rfl⟩ : syracuseStep 3676625 = 2757469) B2757469
theorem B2759123 : Blo 1634016 2759123 := bstep (se 1 (by rfl) ⟨2069342, by rfl⟩ : syracuseStep 2759123 = 4138685) B4138685
theorem B5519825 : Blo 1634016 5519825 := bstep (se 2 (by rfl) ⟨2069934, by rfl⟩ : syracuseStep 5519825 = 4139869) B4139869
theorem B3676643 : Blo 1634016 3676643 := bstep (se 1 (by rfl) ⟨2757482, by rfl⟩ : syracuseStep 3676643 = 5514965) B5514965
theorem B2759251 : Blo 1634016 2759251 := bstep (se 1 (by rfl) ⟨2069438, by rfl⟩ : syracuseStep 2759251 = 4138877) B4138877
theorem B2759393 : Blo 1634016 2759393 := bstep (se 2 (by rfl) ⟨1034772, by rfl⟩ : syracuseStep 2759393 = 2069545) B2069545
theorem B3676913 : Blo 1634016 3676913 := bstep (se 2 (by rfl) ⟨1378842, by rfl⟩ : syracuseStep 3676913 = 2757685) B2757685
theorem B3676931 : Blo 1634016 3676931 := bstep (se 1 (by rfl) ⟨2757698, by rfl⟩ : syracuseStep 3676931 = 5515397) B5515397
theorem B3103505 : Blo 1634016 3103505 := bstep (se 2 (by rfl) ⟨1163814, by rfl⟩ : syracuseStep 3103505 = 2327629) B2327629
theorem B4971313 : Blo 1634016 4971313 := bstep (se 2 (by rfl) ⟨1864242, by rfl⟩ : syracuseStep 4971313 = 3728485) B3728485
theorem B2947889 : Blo 1634016 2947889 := bstep (se 2 (by rfl) ⟨1105458, by rfl⟩ : syracuseStep 2947889 = 2210917) B2210917
theorem B3537745 : Blo 1634016 3537745 := bstep (se 2 (by rfl) ⟨1326654, by rfl⟩ : syracuseStep 3537745 = 2653309) B2653309
theorem B2759521 : Blo 1634016 2759521 := bstep (se 2 (by rfl) ⟨1034820, by rfl⟩ : syracuseStep 2759521 = 2069641) B2069641
theorem B2759555 : Blo 1634016 2759555 := bstep (se 1 (by rfl) ⟨2069666, by rfl⟩ : syracuseStep 2759555 = 4139333) B4139333
theorem B9313157 : Blo 1634016 9313157 := bstep (se 4 (by rfl) ⟨873108, by rfl⟩ : syracuseStep 9313157 = 1746217) B1746217
theorem B5520365 : Blo 1634016 5520365 := bstep (se 3 (by rfl) ⟨1035068, by rfl⟩ : syracuseStep 5520365 = 2070137) B2070137
theorem B2759683 : Blo 1634016 2759683 := bstep (se 1 (by rfl) ⟨2069762, by rfl⟩ : syracuseStep 2759683 = 4139525) B4139525
theorem B3677201 : Blo 1634016 3677201 := bstep (se 2 (by rfl) ⟨1378950, by rfl⟩ : syracuseStep 3677201 = 2757901) B2757901
theorem B3677219 : Blo 1634016 3677219 := bstep (se 1 (by rfl) ⟨2757914, by rfl⟩ : syracuseStep 3677219 = 5515829) B5515829
theorem B5520419 : Blo 1634016 5520419 := bstep (se 1 (by rfl) ⟨4140314, by rfl⟩ : syracuseStep 5520419 = 8280629) B8280629
theorem B6208589 : Blo 1634016 6208589 := bstep (se 3 (by rfl) ⟨1164110, by rfl⟩ : syracuseStep 6208589 = 2328221) B2328221
theorem B2759825 : Blo 1634016 2759825 := bstep (se 2 (by rfl) ⟨1034934, by rfl⟩ : syracuseStep 2759825 = 2069869) B2069869
theorem B15924451 : Blo 1634016 15924451 := bstep (se 1 (by rfl) ⟨11943338, by rfl⟩ : syracuseStep 15924451 = 23886677) B23886677
theorem B2759953 : Blo 1634016 2759953 := bstep (se 2 (by rfl) ⟨1034982, by rfl⟩ : syracuseStep 2759953 = 2069965) B2069965
theorem B3677489 : Blo 1634016 3677489 := bstep (se 2 (by rfl) ⟨1379058, by rfl⟩ : syracuseStep 3677489 = 2758117) B2758117
theorem B5520689 : Blo 1634016 5520689 := bstep (se 2 (by rfl) ⟨2070258, by rfl⟩ : syracuseStep 5520689 = 4140517) B4140517
theorem B2759987 : Blo 1634016 2759987 := bstep (se 1 (by rfl) ⟨2069990, by rfl⟩ : syracuseStep 2759987 = 4139981) B4139981
theorem B3677507 : Blo 1634016 3677507 := bstep (se 1 (by rfl) ⟨2758130, by rfl⟩ : syracuseStep 3677507 = 5516261) B5516261
theorem B9313613 : Blo 1634016 9313613 := bstep (se 3 (by rfl) ⟨1746302, by rfl⟩ : syracuseStep 9313613 = 3492605) B3492605
theorem B4136305 : Blo 1634016 4136305 := bstep (se 2 (by rfl) ⟨1551114, by rfl⟩ : syracuseStep 4136305 = 3102229) B3102229
theorem B6626701 : Blo 1634016 6626701 := bstep (se 3 (by rfl) ⟨1242506, by rfl⟩ : syracuseStep 6626701 = 2485013) B2485013
theorem B12590477 : Blo 1634016 12590477 := bstep (se 3 (by rfl) ⟨2360714, by rfl⟩ : syracuseStep 12590477 = 4721429) B4721429
theorem B2760115 : Blo 1634016 2760115 := bstep (se 1 (by rfl) ⟨2070086, by rfl⟩ : syracuseStep 2760115 = 4140173) B4140173
theorem B9567715 : Blo 1634016 9567715 := bstep (se 1 (by rfl) ⟨7175786, by rfl⟩ : syracuseStep 9567715 = 14351573) B14351573
theorem B2358787 : Blo 1634016 2358787 := bstep (se 1 (by rfl) ⟨1769090, by rfl⟩ : syracuseStep 2358787 = 3538181) B3538181
theorem B2760257 : Blo 1634016 2760257 := bstep (se 2 (by rfl) ⟨1035096, by rfl⟩ : syracuseStep 2760257 = 2070193) B2070193
theorem B3677777 : Blo 1634016 3677777 := bstep (se 2 (by rfl) ⟨1379166, by rfl⟩ : syracuseStep 3677777 = 2758333) B2758333
theorem B3677795 : Blo 1634016 3677795 := bstep (se 1 (by rfl) ⟨2758346, by rfl⟩ : syracuseStep 3677795 = 5516693) B5516693
theorem B11787889 : Blo 1634016 11787889 := bstep (se 2 (by rfl) ⟨4420458, by rfl⟩ : syracuseStep 11787889 = 8840917) B8840917
theorem B4136579 : Blo 1634016 4136579 := bstep (se 1 (by rfl) ⟨3102434, by rfl⟩ : syracuseStep 4136579 = 6204869) B6204869
theorem B3104401 : Blo 1634016 3104401 := bstep (se 2 (by rfl) ⟨1164150, by rfl⟩ : syracuseStep 3104401 = 2328301) B2328301
theorem B2358947 : Blo 1634016 2358947 := bstep (se 1 (by rfl) ⟨1769210, by rfl⟩ : syracuseStep 2358947 = 3538421) B3538421
theorem B8281763 : Blo 1634016 8281763 := bstep (se 1 (by rfl) ⟨6211322, by rfl⟩ : syracuseStep 8281763 = 12422645) B12422645
theorem B2760385 : Blo 1634016 2760385 := bstep (se 2 (by rfl) ⟨1035144, by rfl⟩ : syracuseStep 2760385 = 2070289) B2070289
theorem B12418757 : Blo 1634016 12418757 := bstep (se 4 (by rfl) ⟨1164258, by rfl⟩ : syracuseStep 12418757 = 2328517) B2328517
theorem B2760419 : Blo 1634016 2760419 := bstep (se 1 (by rfl) ⟨2070314, by rfl⟩ : syracuseStep 2760419 = 4140629) B4140629
theorem B3104561 : Blo 1634016 3104561 := bstep (se 2 (by rfl) ⟨1164210, by rfl⟩ : syracuseStep 3104561 = 2328421) B2328421
theorem B4136771 : Blo 1634016 4136771 := bstep (se 1 (by rfl) ⟨3102578, by rfl⟩ : syracuseStep 4136771 = 6205157) B6205157
theorem B5521229 : Blo 1634016 5521229 := bstep (se 3 (by rfl) ⟨1035230, by rfl⟩ : syracuseStep 5521229 = 2070461) B2070461
theorem B2760547 : Blo 1634016 2760547 := bstep (se 1 (by rfl) ⟨2070410, by rfl⟩ : syracuseStep 2760547 = 4140821) B4140821
theorem B3678065 : Blo 1634016 3678065 := bstep (se 2 (by rfl) ⟨1379274, by rfl⟩ : syracuseStep 3678065 = 2758549) B2758549
theorem B3678083 : Blo 1634016 3678083 := bstep (se 1 (by rfl) ⟨2758562, by rfl⟩ : syracuseStep 3678083 = 5517125) B5517125
theorem B5521283 : Blo 1634016 5521283 := bstep (se 1 (by rfl) ⟨4140962, by rfl⟩ : syracuseStep 5521283 = 8281925) B8281925
theorem B12107717 : Blo 1634016 12107717 := bstep (se 4 (by rfl) ⟨1135098, by rfl⟩ : syracuseStep 12107717 = 2270197) B2270197
theorem B2760689 : Blo 1634016 2760689 := bstep (se 2 (by rfl) ⟨1035258, by rfl⟩ : syracuseStep 2760689 = 2070517) B2070517
theorem B3678209 : Blo 1634016 3678209 := bstep (se 2 (by rfl) ⟨1379328, by rfl⟩ : syracuseStep 3678209 = 2758657) B2758657
theorem B12410981 : Blo 1634016 12410981 := bstep (se 4 (by rfl) ⟨1163529, by rfl⟩ : syracuseStep 12410981 = 2327059) B2327059
theorem B16777367 : Blo 1634016 16777367 := bstep (se 1 (by rfl) ⟨12583025, by rfl⟩ : syracuseStep 16777367 = 25166051) B25166051
theorem B5890241 : Blo 1634016 5890241 := bstep (se 2 (by rfl) ⟨2208840, by rfl⟩ : syracuseStep 5890241 = 4417681) B4417681
theorem B6209729 : Blo 1634016 6209729 := bstep (se 2 (by rfl) ⟨2328648, by rfl⟩ : syracuseStep 6209729 = 4657297) B4657297
theorem B26509517 : Blo 1634016 26509517 := bstep (se 3 (by rfl) ⟨4970534, by rfl⟩ : syracuseStep 26509517 = 9941069) B9941069
theorem B3678425 : Blo 1634016 3678425 := bstep (se 2 (by rfl) ⟨1379409, by rfl⟩ : syracuseStep 3678425 = 2758819) B2758819
theorem B4972823 : Blo 1634016 4972823 := bstep (se 1 (by rfl) ⟨3729617, by rfl⟩ : syracuseStep 4972823 = 7459235) B7459235
theorem B3105047 : Blo 1634016 3105047 := bstep (se 1 (by rfl) ⟨2328785, by rfl⟩ : syracuseStep 3105047 = 4657571) B4657571
theorem B3678515 : Blo 1634016 3678515 := bstep (se 1 (by rfl) ⟨2758886, by rfl⟩ : syracuseStep 3678515 = 5517773) B5517773
theorem B3678551 : Blo 1634016 3678551 := bstep (se 1 (by rfl) ⟨2758913, by rfl⟩ : syracuseStep 3678551 = 5517827) B5517827
theorem B4137419 : Blo 1634016 4137419 := bstep (se 1 (by rfl) ⟨3103064, by rfl⟩ : syracuseStep 4137419 = 6206129) B6206129
theorem B3490265 : Blo 1634016 3490265 := bstep (se 2 (by rfl) ⟨1308849, by rfl⟩ : syracuseStep 3490265 = 2617699) B2617699
theorem B3678731 : Blo 1634016 3678731 := bstep (se 1 (by rfl) ⟨2759048, by rfl⟩ : syracuseStep 3678731 = 5518097) B5518097
theorem B1745431 : Blo 1634016 1745431 := bstep (se 1 (by rfl) ⟨1309073, by rfl⟩ : syracuseStep 1745431 = 2618147) B2618147
theorem B3678785 : Blo 1634016 3678785 := bstep (se 2 (by rfl) ⟨1379544, by rfl⟩ : syracuseStep 3678785 = 2759089) B2759089
theorem B12411467 : Blo 1634016 12411467 := bstep (se 1 (by rfl) ⟨9308600, by rfl⟩ : syracuseStep 12411467 = 18617201) B18617201
theorem B3539531 : Blo 1634016 3539531 := bstep (se 1 (by rfl) ⟨2654648, by rfl⟩ : syracuseStep 3539531 = 5309297) B5309297
theorem B3588823 : Blo 1634016 3588823 := bstep (se 1 (by rfl) ⟨2691617, by rfl⟩ : syracuseStep 3588823 = 5383235) B5383235
theorem B3679001 : Blo 1634016 3679001 := bstep (se 2 (by rfl) ⟨1379625, by rfl⟩ : syracuseStep 3679001 = 2759251) B2759251
theorem B4973405 : Blo 1634016 4973405 := bstep (se 3 (by rfl) ⟨932513, by rfl⟩ : syracuseStep 4973405 = 1865027) B1865027
theorem B3679091 : Blo 1634016 3679091 := bstep (se 1 (by rfl) ⟨2759318, by rfl⟩ : syracuseStep 3679091 = 5518637) B5518637
theorem B1745803 : Blo 1634016 1745803 := bstep (se 1 (by rfl) ⟨1309352, by rfl⟩ : syracuseStep 1745803 = 2618705) B2618705
theorem B3679127 : Blo 1634016 3679127 := bstep (se 1 (by rfl) ⟨2759345, by rfl⟩ : syracuseStep 3679127 = 5518691) B5518691
theorem B3105715 : Blo 1634016 3105715 := bstep (se 1 (by rfl) ⟨2329286, by rfl⟩ : syracuseStep 3105715 = 4658573) B4658573
theorem B4654027 : Blo 1634016 4654027 := bstep (se 1 (by rfl) ⟨3490520, by rfl⟩ : syracuseStep 4654027 = 6981041) B6981041
theorem B8389649 : Blo 1634016 8389649 := bstep (se 2 (by rfl) ⟨3146118, by rfl⟩ : syracuseStep 8389649 = 6292237) B6292237
theorem B3679307 : Blo 1634016 3679307 := bstep (se 1 (by rfl) ⟨2759480, by rfl⟩ : syracuseStep 3679307 = 5518961) B5518961
theorem B9208907 : Blo 1634016 9208907 := bstep (se 1 (by rfl) ⟨6906680, by rfl⟩ : syracuseStep 9208907 = 13813361) B13813361
theorem B3490931 : Blo 1634016 3490931 := bstep (se 1 (by rfl) ⟨2618198, by rfl⟩ : syracuseStep 3490931 = 5236397) B5236397
theorem B3679361 : Blo 1634016 3679361 := bstep (se 2 (by rfl) ⟨1379760, by rfl⟩ : syracuseStep 3679361 = 2759521) B2759521
theorem B2098315 : Blo 1634016 2098315 := bstep (se 1 (by rfl) ⟨1573736, by rfl⟩ : syracuseStep 2098315 = 3147473) B3147473
theorem B42468533 : Blo 1634016 42468533 := bstep (se 5 (by rfl) ⟨1990712, by rfl⟩ : syracuseStep 42468533 = 3981425) B3981425
theorem B1680683 : Blo 1634016 1680683 := bstep (se 1 (by rfl) ⟨1260512, by rfl⟩ : syracuseStep 1680683 = 2521025) B2521025
theorem B3679577 : Blo 1634016 3679577 := bstep (se 2 (by rfl) ⟨1379841, by rfl⟩ : syracuseStep 3679577 = 2759683) B2759683
theorem B64603541 : Blo 1634016 64603541 := bstep (se 6 (by rfl) ⟨1514145, by rfl⟩ : syracuseStep 64603541 = 3028291) B3028291
theorem B4138391 : Blo 1634016 4138391 := bstep (se 1 (by rfl) ⟨3103793, by rfl⟩ : syracuseStep 4138391 = 6207587) B6207587
theorem B6210989 : Blo 1634016 6210989 := bstep (se 3 (by rfl) ⟨1164560, by rfl⟩ : syracuseStep 6210989 = 2329121) B2329121
theorem B3679667 : Blo 1634016 3679667 := bstep (se 1 (by rfl) ⟨2759750, by rfl⟩ : syracuseStep 3679667 = 5519501) B5519501
theorem B4654529 : Blo 1634016 4654529 := bstep (se 2 (by rfl) ⟨1745448, by rfl⟩ : syracuseStep 4654529 = 3490897) B3490897
theorem B6211019 : Blo 1634016 6211019 := bstep (se 1 (by rfl) ⟨4658264, by rfl⟩ : syracuseStep 6211019 = 9316529) B9316529
theorem B3679703 : Blo 1634016 3679703 := bstep (se 1 (by rfl) ⟨2759777, by rfl⟩ : syracuseStep 3679703 = 5519555) B5519555
theorem B5596723 : Blo 1634016 5596723 := bstep (se 1 (by rfl) ⟨4197542, by rfl⟩ : syracuseStep 5596723 = 8395085) B8395085
theorem B12420701 : Blo 1634016 12420701 := bstep (se 3 (by rfl) ⟨2328881, by rfl⟩ : syracuseStep 12420701 = 4657763) B4657763
theorem B2451083 : Blo 1634016 2451083 := bstep (se 1 (by rfl) ⟨1838312, by rfl⟩ : syracuseStep 2451083 = 3676625) B3676625
theorem B3679883 : Blo 1634016 3679883 := bstep (se 1 (by rfl) ⟨2759912, by rfl⟩ : syracuseStep 3679883 = 5519825) B5519825
theorem B2451095 : Blo 1634016 2451095 := bstep (se 1 (by rfl) ⟨1838321, by rfl⟩ : syracuseStep 2451095 = 3676643) B3676643
theorem B8275607 : Blo 1634016 8275607 := bstep (se 1 (by rfl) ⟨6206705, by rfl⟩ : syracuseStep 8275607 = 12413411) B12413411
theorem B6981299 : Blo 1634016 6981299 := bstep (se 1 (by rfl) ⟨5235974, by rfl⟩ : syracuseStep 6981299 = 10471949) B10471949
theorem B4417217 : Blo 1634016 4417217 := bstep (se 2 (by rfl) ⟨1656456, by rfl⟩ : syracuseStep 4417217 = 3312913) B3312913
theorem B3679937 : Blo 1634016 3679937 := bstep (se 2 (by rfl) ⟨1379976, by rfl⟩ : syracuseStep 3679937 = 2759953) B2759953
theorem B2451161 : Blo 1634016 2451161 := bstep (se 2 (by rfl) ⟨919185, by rfl⟩ : syracuseStep 2451161 = 1838371) B1838371
theorem B18867973 : Blo 1634016 18867973 := bstep (se 4 (by rfl) ⟨1768872, by rfl⟩ : syracuseStep 18867973 = 3537745) B3537745
theorem B4654871 : Blo 1634016 4654871 := bstep (se 1 (by rfl) ⟨3491153, by rfl⟩ : syracuseStep 4654871 = 6982307) B6982307
theorem B5515073 : Blo 1634016 5515073 := bstep (se 2 (by rfl) ⟨2068152, by rfl⟩ : syracuseStep 5515073 = 4136305) B4136305
theorem B4417345 : Blo 1634016 4417345 := bstep (se 2 (by rfl) ⟨1656504, by rfl⟩ : syracuseStep 4417345 = 3313009) B3313009
theorem B2451275 : Blo 1634016 2451275 := bstep (se 1 (by rfl) ⟨1838456, by rfl⟩ : syracuseStep 2451275 = 3676913) B3676913
theorem B2451287 : Blo 1634016 2451287 := bstep (se 1 (by rfl) ⟨1838465, by rfl⟩ : syracuseStep 2451287 = 3676931) B3676931
theorem B2451353 : Blo 1634016 2451353 := bstep (se 2 (by rfl) ⟨919257, by rfl⟩ : syracuseStep 2451353 = 1838515) B1838515
theorem B3680153 : Blo 1634016 3680153 := bstep (se 2 (by rfl) ⟨1380057, by rfl⟩ : syracuseStep 3680153 = 2760115) B2760115
theorem B12756953 : Blo 1634016 12756953 := bstep (se 2 (by rfl) ⟨4783857, by rfl⟩ : syracuseStep 12756953 = 9567715) B9567715
theorem B3680243 : Blo 1634016 3680243 := bstep (se 1 (by rfl) ⟨2760182, by rfl⟩ : syracuseStep 3680243 = 5520365) B5520365
theorem B2451467 : Blo 1634016 2451467 := bstep (se 1 (by rfl) ⟨1838600, by rfl⟩ : syracuseStep 2451467 = 3677201) B3677201
theorem B3147787 : Blo 1634016 3147787 := bstep (se 1 (by rfl) ⟨2360840, by rfl⟩ : syracuseStep 3147787 = 4721681) B4721681
theorem B21235729 : Blo 1634016 21235729 := bstep (se 2 (by rfl) ⟨7963398, by rfl⟩ : syracuseStep 21235729 = 15926797) B15926797
theorem B2451479 : Blo 1634016 2451479 := bstep (se 1 (by rfl) ⟨1838609, by rfl⟩ : syracuseStep 2451479 = 3677219) B3677219
theorem B3680279 : Blo 1634016 3680279 := bstep (se 1 (by rfl) ⟨2760209, by rfl⟩ : syracuseStep 3680279 = 5520419) B5520419
theorem B13961261 : Blo 1634016 13961261 := bstep (se 3 (by rfl) ⟨2617736, by rfl⟩ : syracuseStep 13961261 = 5235473) B5235473
theorem B4139059 : Blo 1634016 4139059 := bstep (se 1 (by rfl) ⟨3104294, by rfl⟩ : syracuseStep 4139059 = 6208589) B6208589
theorem B3491905 : Blo 1634016 3491905 := bstep (se 2 (by rfl) ⟨1309464, by rfl⟩ : syracuseStep 3491905 = 2618929) B2618929
theorem B2451545 : Blo 1634016 2451545 := bstep (se 2 (by rfl) ⟨919329, by rfl⟩ : syracuseStep 2451545 = 1838659) B1838659
theorem B6211673 : Blo 1634016 6211673 := bstep (se 2 (by rfl) ⟨2329377, by rfl⟩ : syracuseStep 6211673 = 4658755) B4658755
theorem B4139201 : Blo 1634016 4139201 := bstep (se 2 (by rfl) ⟨1552200, by rfl⟩ : syracuseStep 4139201 = 3104401) B3104401
theorem B2451659 : Blo 1634016 2451659 := bstep (se 1 (by rfl) ⟨1838744, by rfl⟩ : syracuseStep 2451659 = 3677489) B3677489
theorem B3680459 : Blo 1634016 3680459 := bstep (se 1 (by rfl) ⟨2760344, by rfl⟩ : syracuseStep 3680459 = 5520689) B5520689
theorem B2451671 : Blo 1634016 2451671 := bstep (se 1 (by rfl) ⟨1838753, by rfl⟩ : syracuseStep 2451671 = 3677507) B3677507
theorem B3680513 : Blo 1634016 3680513 := bstep (se 2 (by rfl) ⟨1380192, by rfl⟩ : syracuseStep 3680513 = 2760385) B2760385
theorem B2451737 : Blo 1634016 2451737 := bstep (se 2 (by rfl) ⟨919401, by rfl⟩ : syracuseStep 2451737 = 1838803) B1838803
theorem B3729689 : Blo 1634016 3729689 := bstep (se 2 (by rfl) ⟨1398633, by rfl⟩ : syracuseStep 3729689 = 2797267) B2797267
theorem B3492161 : Blo 1634016 3492161 := bstep (se 2 (by rfl) ⟨1309560, by rfl⟩ : syracuseStep 3492161 = 2619121) B2619121
theorem B5515613 : Blo 1634016 5515613 := bstep (se 3 (by rfl) ⟨1034177, by rfl⟩ : syracuseStep 5515613 = 2068355) B2068355
theorem B2451851 : Blo 1634016 2451851 := bstep (se 1 (by rfl) ⟨1838888, by rfl⟩ : syracuseStep 2451851 = 3677777) B3677777
theorem B2451863 : Blo 1634016 2451863 := bstep (se 1 (by rfl) ⟨1838897, by rfl⟩ : syracuseStep 2451863 = 3677795) B3677795
theorem B3492247 : Blo 1634016 3492247 := bstep (se 1 (by rfl) ⟨2619185, by rfl⟩ : syracuseStep 3492247 = 5238371) B5238371
theorem B2451929 : Blo 1634016 2451929 := bstep (se 2 (by rfl) ⟨919473, by rfl⟩ : syracuseStep 2451929 = 1838947) B1838947
theorem B3680729 : Blo 1634016 3680729 := bstep (se 2 (by rfl) ⟨1380273, by rfl⟩ : syracuseStep 3680729 = 2760547) B2760547
theorem B27945485 : Blo 1634016 27945485 := bstep (se 3 (by rfl) ⟨5239778, by rfl⟩ : syracuseStep 27945485 = 10479557) B10479557
theorem B3680819 : Blo 1634016 3680819 := bstep (se 1 (by rfl) ⟨2760614, by rfl⟩ : syracuseStep 3680819 = 5521229) B5521229
theorem B2452043 : Blo 1634016 2452043 := bstep (se 1 (by rfl) ⟨1839032, by rfl⟩ : syracuseStep 2452043 = 3678065) B3678065
theorem B2452055 : Blo 1634016 2452055 := bstep (se 1 (by rfl) ⟨1839041, by rfl⟩ : syracuseStep 2452055 = 3678083) B3678083
theorem B3680855 : Blo 1634016 3680855 := bstep (se 1 (by rfl) ⟨2760641, by rfl⟩ : syracuseStep 3680855 = 5521283) B5521283
theorem B8071811 : Blo 1634016 8071811 := bstep (se 1 (by rfl) ⟨6053858, by rfl⟩ : syracuseStep 8071811 = 12107717) B12107717
theorem B2452121 : Blo 1634016 2452121 := bstep (se 2 (by rfl) ⟨919545, by rfl⟩ : syracuseStep 2452121 = 1839091) B1839091
theorem B2452235 : Blo 1634016 2452235 := bstep (se 1 (by rfl) ⟨1839176, by rfl⟩ : syracuseStep 2452235 = 3678353) B3678353
theorem B3681035 : Blo 1634016 3681035 := bstep (se 1 (by rfl) ⟨2760776, by rfl⟩ : syracuseStep 3681035 = 5521553) B5521553
theorem B2452247 : Blo 1634016 2452247 := bstep (se 1 (by rfl) ⟨1839185, by rfl⟩ : syracuseStep 2452247 = 3678371) B3678371
theorem B63720245 : Blo 1634016 63720245 := bstep (se 5 (by rfl) ⟨2986886, by rfl⟩ : syracuseStep 63720245 = 5973773) B5973773
theorem B6294347 : Blo 1634016 6294347 := bstep (se 1 (by rfl) ⟨4720760, by rfl⟩ : syracuseStep 6294347 = 9441521) B9441521
theorem B2452313 : Blo 1634016 2452313 := bstep (se 2 (by rfl) ⟨919617, by rfl⟩ : syracuseStep 2452313 = 1839235) B1839235
theorem B9317213 : Blo 1634016 9317213 := bstep (se 3 (by rfl) ⟨1746977, by rfl⟩ : syracuseStep 9317213 = 3493955) B3493955
theorem B2452427 : Blo 1634016 2452427 := bstep (se 1 (by rfl) ⟨1839320, by rfl⟩ : syracuseStep 2452427 = 3678641) B3678641
theorem B2452439 : Blo 1634016 2452439 := bstep (se 1 (by rfl) ⟨1839329, by rfl⟩ : syracuseStep 2452439 = 3678659) B3678659
theorem B2452505 : Blo 1634016 2452505 := bstep (se 2 (by rfl) ⟨919689, by rfl⟩ : syracuseStep 2452505 = 1839379) B1839379
theorem B2452619 : Blo 1634016 2452619 := bstep (se 1 (by rfl) ⟨1839464, by rfl⟩ : syracuseStep 2452619 = 3678929) B3678929
theorem B2452631 : Blo 1634016 2452631 := bstep (se 1 (by rfl) ⟨1839473, by rfl⟩ : syracuseStep 2452631 = 3678947) B3678947
theorem B8842391 : Blo 1634016 8842391 := bstep (se 1 (by rfl) ⟨6631793, by rfl⟩ : syracuseStep 8842391 = 13263587) B13263587
theorem B2452697 : Blo 1634016 2452697 := bstep (se 2 (by rfl) ⟨919761, by rfl⟩ : syracuseStep 2452697 = 1839523) B1839523
theorem B13258001 : Blo 1634016 13258001 := bstep (se 2 (by rfl) ⟨4971750, by rfl⟩ : syracuseStep 13258001 = 9943501) B9943501
theorem B6630673 : Blo 1634016 6630673 := bstep (se 2 (by rfl) ⟨2486502, by rfl⟩ : syracuseStep 6630673 = 4973005) B4973005
theorem B2452811 : Blo 1634016 2452811 := bstep (se 1 (by rfl) ⟨1839608, by rfl⟩ : syracuseStep 2452811 = 3679217) B3679217
theorem B2452823 : Blo 1634016 2452823 := bstep (se 1 (by rfl) ⟨1839617, by rfl⟩ : syracuseStep 2452823 = 3679235) B3679235
theorem B1838443 : Blo 1634016 1838443 := bstep (se 1 (by rfl) ⟨1378832, by rfl⟩ : syracuseStep 1838443 = 2757665) B2757665
theorem B2452889 : Blo 1634016 2452889 := bstep (se 2 (by rfl) ⟨919833, by rfl⟩ : syracuseStep 2452889 = 1839667) B1839667
theorem B4140467 : Blo 1634016 4140467 := bstep (se 1 (by rfl) ⟨3105350, by rfl⟩ : syracuseStep 4140467 = 6210701) B6210701
theorem B5516747 : Blo 1634016 5516747 := bstep (se 1 (by rfl) ⟨4137560, by rfl⟩ : syracuseStep 5516747 = 8275121) B8275121
theorem B1838551 : Blo 1634016 1838551 := bstep (se 1 (by rfl) ⟨1378913, by rfl⟩ : syracuseStep 1838551 = 2757827) B2757827
theorem B2453003 : Blo 1634016 2453003 := bstep (se 1 (by rfl) ⟨1839752, by rfl⟩ : syracuseStep 2453003 = 3679505) B3679505
theorem B2453015 : Blo 1634016 2453015 := bstep (se 1 (by rfl) ⟨1839761, by rfl⟩ : syracuseStep 2453015 = 3679523) B3679523
theorem B2453081 : Blo 1634016 2453081 := bstep (se 2 (by rfl) ⟨919905, by rfl⟩ : syracuseStep 2453081 = 1839811) B1839811
theorem B1838731 : Blo 1634016 1838731 := bstep (se 1 (by rfl) ⟨1379048, by rfl⟩ : syracuseStep 1838731 = 2758097) B2758097
theorem B2453195 : Blo 1634016 2453195 := bstep (se 1 (by rfl) ⟨1839896, by rfl⟩ : syracuseStep 2453195 = 3679793) B3679793
theorem B2068183 : Blo 1634016 2068183 := bstep (se 1 (by rfl) ⟨1551137, by rfl⟩ : syracuseStep 2068183 = 3102275) B3102275
theorem B2453207 : Blo 1634016 2453207 := bstep (se 1 (by rfl) ⟨1839905, by rfl⟩ : syracuseStep 2453207 = 3679811) B3679811
theorem B5517017 : Blo 1634016 5517017 := bstep (se 2 (by rfl) ⟨2068881, by rfl⟩ : syracuseStep 5517017 = 4137763) B4137763
theorem B1634027 : Blo 1634016 1634027 := bstep (se 1 (by rfl) ⟨1225520, by rfl⟩ : syracuseStep 1634027 = 2451041) B2451041
theorem B1634039 : Blo 1634016 1634039 := bstep (se 1 (by rfl) ⟨1225529, by rfl⟩ : syracuseStep 1634039 = 2451059) B2451059
theorem B1838839 : Blo 1634016 1838839 := bstep (se 1 (by rfl) ⟨1379129, by rfl⟩ : syracuseStep 1838839 = 2758259) B2758259
theorem B6205187 : Blo 1634016 6205187 := bstep (se 1 (by rfl) ⟨4653890, by rfl⟩ : syracuseStep 6205187 = 9307781) B9307781
theorem B1634059 : Blo 1634016 1634059 := bstep (se 1 (by rfl) ⟨1225544, by rfl⟩ : syracuseStep 1634059 = 2451089) B2451089
theorem B1634071 : Blo 1634016 1634071 := bstep (se 1 (by rfl) ⟨1225553, by rfl⟩ : syracuseStep 1634071 = 2451107) B2451107
theorem B2453273 : Blo 1634016 2453273 := bstep (se 2 (by rfl) ⟨919977, by rfl⟩ : syracuseStep 2453273 = 1839955) B1839955
theorem B1634091 : Blo 1634016 1634091 := bstep (se 1 (by rfl) ⟨1225568, by rfl⟩ : syracuseStep 1634091 = 2451137) B2451137
theorem B1634103 : Blo 1634016 1634103 := bstep (se 1 (by rfl) ⟨1225577, by rfl⟩ : syracuseStep 1634103 = 2451155) B2451155
theorem B1634123 : Blo 1634016 1634123 := bstep (se 1 (by rfl) ⟨1225592, by rfl⟩ : syracuseStep 1634123 = 2451185) B2451185
theorem B1634135 : Blo 1634016 1634135 := bstep (se 1 (by rfl) ⟨1225601, by rfl⟩ : syracuseStep 1634135 = 2451203) B2451203
theorem B4656989 : Blo 1634016 4656989 := bstep (se 3 (by rfl) ⟨873185, by rfl⟩ : syracuseStep 4656989 = 1746371) B1746371
theorem B1634155 : Blo 1634016 1634155 := bstep (se 1 (by rfl) ⟨1225616, by rfl⟩ : syracuseStep 1634155 = 2451233) B2451233
theorem B1634167 : Blo 1634016 1634167 := bstep (se 1 (by rfl) ⟨1225625, by rfl⟩ : syracuseStep 1634167 = 2451251) B2451251
theorem B5975939 : Blo 1634016 5975939 := bstep (se 1 (by rfl) ⟨4481954, by rfl⟩ : syracuseStep 5975939 = 8963909) B8963909
theorem B1634187 : Blo 1634016 1634187 := bstep (se 1 (by rfl) ⟨1225640, by rfl⟩ : syracuseStep 1634187 = 2451281) B2451281
theorem B2453387 : Blo 1634016 2453387 := bstep (se 1 (by rfl) ⟨1840040, by rfl⟩ : syracuseStep 2453387 = 3680081) B3680081
theorem B1634199 : Blo 1634016 1634199 := bstep (se 1 (by rfl) ⟨1225649, by rfl⟩ : syracuseStep 1634199 = 2451299) B2451299
theorem B2453399 : Blo 1634016 2453399 := bstep (se 1 (by rfl) ⟨1840049, by rfl⟩ : syracuseStep 2453399 = 3680099) B3680099
theorem B1634219 : Blo 1634016 1634219 := bstep (se 1 (by rfl) ⟨1225664, by rfl⟩ : syracuseStep 1634219 = 2451329) B2451329
theorem B1839019 : Blo 1634016 1839019 := bstep (se 1 (by rfl) ⟨1379264, by rfl⟩ : syracuseStep 1839019 = 2758529) B2758529
theorem B1634231 : Blo 1634016 1634231 := bstep (se 1 (by rfl) ⟨1225673, by rfl⟩ : syracuseStep 1634231 = 2451347) B2451347
theorem B1634251 : Blo 1634016 1634251 := bstep (se 1 (by rfl) ⟨1225688, by rfl⟩ : syracuseStep 1634251 = 2451377) B2451377
theorem B4141003 : Blo 1634016 4141003 := bstep (se 1 (by rfl) ⟨3105752, by rfl⟩ : syracuseStep 4141003 = 6211505) B6211505
theorem B1634263 : Blo 1634016 1634263 := bstep (se 1 (by rfl) ⟨1225697, by rfl⟩ : syracuseStep 1634263 = 2451395) B2451395
theorem B2453465 : Blo 1634016 2453465 := bstep (se 2 (by rfl) ⟨920049, by rfl⟩ : syracuseStep 2453465 = 1840099) B1840099
theorem B1634283 : Blo 1634016 1634283 := bstep (se 1 (by rfl) ⟨1225712, by rfl⟩ : syracuseStep 1634283 = 2451425) B2451425
theorem B1634295 : Blo 1634016 1634295 := bstep (se 1 (by rfl) ⟨1225721, by rfl⟩ : syracuseStep 1634295 = 2451443) B2451443
theorem B1634315 : Blo 1634016 1634315 := bstep (se 1 (by rfl) ⟨1225736, by rfl⟩ : syracuseStep 1634315 = 2451473) B2451473
theorem B1634327 : Blo 1634016 1634327 := bstep (se 1 (by rfl) ⟨1225745, by rfl⟩ : syracuseStep 1634327 = 2451491) B2451491
theorem B1839127 : Blo 1634016 1839127 := bstep (se 1 (by rfl) ⟨1379345, by rfl⟩ : syracuseStep 1839127 = 2758691) B2758691
theorem B1634347 : Blo 1634016 1634347 := bstep (se 1 (by rfl) ⟨1225760, by rfl⟩ : syracuseStep 1634347 = 2451521) B2451521
theorem B3313715 : Blo 1634016 3313715 := bstep (se 1 (by rfl) ⟨2485286, by rfl⟩ : syracuseStep 3313715 = 4970573) B4970573
theorem B1634359 : Blo 1634016 1634359 := bstep (se 1 (by rfl) ⟨1225769, by rfl⟩ : syracuseStep 1634359 = 2451539) B2451539
theorem B1634379 : Blo 1634016 1634379 := bstep (se 1 (by rfl) ⟨1225784, by rfl⟩ : syracuseStep 1634379 = 2451569) B2451569
theorem B2453579 : Blo 1634016 2453579 := bstep (se 1 (by rfl) ⟨1840184, by rfl⟩ : syracuseStep 2453579 = 3680369) B3680369
theorem B1634391 : Blo 1634016 1634391 := bstep (se 1 (by rfl) ⟨1225793, by rfl⟩ : syracuseStep 1634391 = 2451587) B2451587
theorem B2453591 : Blo 1634016 2453591 := bstep (se 1 (by rfl) ⟨1840193, by rfl⟩ : syracuseStep 2453591 = 3680387) B3680387
theorem B4141145 : Blo 1634016 4141145 := bstep (se 2 (by rfl) ⟨1552929, by rfl⟩ : syracuseStep 4141145 = 3105859) B3105859
theorem B1634411 : Blo 1634016 1634411 := bstep (se 1 (by rfl) ⟨1225808, by rfl⟩ : syracuseStep 1634411 = 2451617) B2451617
theorem B1634423 : Blo 1634016 1634423 := bstep (se 1 (by rfl) ⟨1225817, by rfl⟩ : syracuseStep 1634423 = 2451635) B2451635
theorem B1634443 : Blo 1634016 1634443 := bstep (se 1 (by rfl) ⟨1225832, by rfl⟩ : syracuseStep 1634443 = 2451665) B2451665
theorem B1634455 : Blo 1634016 1634455 := bstep (se 1 (by rfl) ⟨1225841, by rfl⟩ : syracuseStep 1634455 = 2451683) B2451683
theorem B2453657 : Blo 1634016 2453657 := bstep (se 2 (by rfl) ⟨920121, by rfl⟩ : syracuseStep 2453657 = 1840243) B1840243
theorem B1634475 : Blo 1634016 1634475 := bstep (se 1 (by rfl) ⟨1225856, by rfl⟩ : syracuseStep 1634475 = 2451713) B2451713
theorem B7852211 : Blo 1634016 7852211 := bstep (se 1 (by rfl) ⟨5889158, by rfl⟩ : syracuseStep 7852211 = 11778317) B11778317
theorem B4657331 : Blo 1634016 4657331 := bstep (se 1 (by rfl) ⟨3492998, by rfl⟩ : syracuseStep 4657331 = 6985997) B6985997
theorem B1634487 : Blo 1634016 1634487 := bstep (se 1 (by rfl) ⟨1225865, by rfl⟩ : syracuseStep 1634487 = 2451731) B2451731
theorem B6205643 : Blo 1634016 6205643 := bstep (se 1 (by rfl) ⟨4654232, by rfl⟩ : syracuseStep 6205643 = 9308465) B9308465
theorem B1634507 : Blo 1634016 1634507 := bstep (se 1 (by rfl) ⟨1225880, by rfl⟩ : syracuseStep 1634507 = 2451761) B2451761
theorem B1839307 : Blo 1634016 1839307 := bstep (se 1 (by rfl) ⟨1379480, by rfl⟩ : syracuseStep 1839307 = 2758961) B2758961
theorem B1634519 : Blo 1634016 1634519 := bstep (se 1 (by rfl) ⟨1225889, by rfl⟩ : syracuseStep 1634519 = 2451779) B2451779
theorem B1634539 : Blo 1634016 1634539 := bstep (se 1 (by rfl) ⟨1225904, by rfl⟩ : syracuseStep 1634539 = 2451809) B2451809
theorem B1634551 : Blo 1634016 1634551 := bstep (se 1 (by rfl) ⟨1225913, by rfl⟩ : syracuseStep 1634551 = 2451827) B2451827
theorem B26513669 : Blo 1634016 26513669 := bstep (se 4 (by rfl) ⟨2485656, by rfl⟩ : syracuseStep 26513669 = 4971313) B4971313
theorem B1634571 : Blo 1634016 1634571 := bstep (se 1 (by rfl) ⟨1225928, by rfl⟩ : syracuseStep 1634571 = 2451857) B2451857
theorem B2453771 : Blo 1634016 2453771 := bstep (se 1 (by rfl) ⟨1840328, by rfl⟩ : syracuseStep 2453771 = 3680657) B3680657
theorem B1634583 : Blo 1634016 1634583 := bstep (se 1 (by rfl) ⟨1225937, by rfl⟩ : syracuseStep 1634583 = 2451875) B2451875
theorem B2453783 : Blo 1634016 2453783 := bstep (se 1 (by rfl) ⟨1840337, by rfl⟩ : syracuseStep 2453783 = 3680675) B3680675
theorem B1634603 : Blo 1634016 1634603 := bstep (se 1 (by rfl) ⟨1225952, by rfl⟩ : syracuseStep 1634603 = 2451905) B2451905
theorem B6983981 : Blo 1634016 6983981 := bstep (se 3 (by rfl) ⟨1309496, by rfl⟩ : syracuseStep 6983981 = 2618993) B2618993
theorem B1634615 : Blo 1634016 1634615 := bstep (se 1 (by rfl) ⟨1225961, by rfl⟩ : syracuseStep 1634615 = 2451923) B2451923
theorem B1839415 : Blo 1634016 1839415 := bstep (se 1 (by rfl) ⟨1379561, by rfl⟩ : syracuseStep 1839415 = 2759123) B2759123
theorem B1634635 : Blo 1634016 1634635 := bstep (se 1 (by rfl) ⟨1225976, by rfl⟩ : syracuseStep 1634635 = 2451953) B2451953
theorem B1634647 : Blo 1634016 1634647 := bstep (se 1 (by rfl) ⟨1225985, by rfl⟩ : syracuseStep 1634647 = 2451971) B2451971
theorem B2453849 : Blo 1634016 2453849 := bstep (se 2 (by rfl) ⟨920193, by rfl⟩ : syracuseStep 2453849 = 1840387) B1840387
theorem B1634667 : Blo 1634016 1634667 := bstep (se 1 (by rfl) ⟨1226000, by rfl⟩ : syracuseStep 1634667 = 2452001) B2452001
theorem B1634679 : Blo 1634016 1634679 := bstep (se 1 (by rfl) ⟨1226009, by rfl⟩ : syracuseStep 1634679 = 2452019) B2452019
theorem B1634699 : Blo 1634016 1634699 := bstep (se 1 (by rfl) ⟨1226024, by rfl⟩ : syracuseStep 1634699 = 2452049) B2452049
theorem B6205841 : Blo 1634016 6205841 := bstep (se 2 (by rfl) ⟨2327190, by rfl⟩ : syracuseStep 6205841 = 4654381) B4654381
theorem B1634711 : Blo 1634016 1634711 := bstep (se 1 (by rfl) ⟨1226033, by rfl⟩ : syracuseStep 1634711 = 2452067) B2452067
theorem B5517719 : Blo 1634016 5517719 := bstep (se 1 (by rfl) ⟨4138289, by rfl⟩ : syracuseStep 5517719 = 8276579) B8276579
theorem B1634731 : Blo 1634016 1634731 := bstep (se 1 (by rfl) ⟨1226048, by rfl⟩ : syracuseStep 1634731 = 2452097) B2452097
theorem B1634743 : Blo 1634016 1634743 := bstep (se 1 (by rfl) ⟨1226057, by rfl⟩ : syracuseStep 1634743 = 2452115) B2452115
theorem B1634763 : Blo 1634016 1634763 := bstep (se 1 (by rfl) ⟨1226072, by rfl⟩ : syracuseStep 1634763 = 2452145) B2452145
theorem B2453963 : Blo 1634016 2453963 := bstep (se 1 (by rfl) ⟨1840472, by rfl⟩ : syracuseStep 2453963 = 3680945) B3680945
theorem B1634775 : Blo 1634016 1634775 := bstep (se 1 (by rfl) ⟨1226081, by rfl⟩ : syracuseStep 1634775 = 2452163) B2452163
theorem B2453975 : Blo 1634016 2453975 := bstep (se 1 (by rfl) ⟨1840481, by rfl⟩ : syracuseStep 2453975 = 3680963) B3680963
theorem B1634795 : Blo 1634016 1634795 := bstep (se 1 (by rfl) ⟨1226096, by rfl⟩ : syracuseStep 1634795 = 2452193) B2452193
theorem B1839595 : Blo 1634016 1839595 := bstep (se 1 (by rfl) ⟨1379696, by rfl⟩ : syracuseStep 1839595 = 2759393) B2759393
theorem B1634807 : Blo 1634016 1634807 := bstep (se 1 (by rfl) ⟨1226105, by rfl⟩ : syracuseStep 1634807 = 2452211) B2452211
theorem B3314177 : Blo 1634016 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B2069003 : Blo 1634016 2069003 := bstep (se 1 (by rfl) ⟨1551752, by rfl⟩ : syracuseStep 2069003 = 3103505) B3103505
theorem B1634827 : Blo 1634016 1634827 := bstep (se 1 (by rfl) ⟨1226120, by rfl⟩ : syracuseStep 1634827 = 2452241) B2452241
theorem B8835601 : Blo 1634016 8835601 := bstep (se 2 (by rfl) ⟨3313350, by rfl⟩ : syracuseStep 8835601 = 6626701) B6626701
theorem B1634839 : Blo 1634016 1634839 := bstep (se 1 (by rfl) ⟨1226129, by rfl⟩ : syracuseStep 1634839 = 2452259) B2452259
theorem B1634859 : Blo 1634016 1634859 := bstep (se 1 (by rfl) ⟨1226144, by rfl⟩ : syracuseStep 1634859 = 2452289) B2452289
theorem B1634871 : Blo 1634016 1634871 := bstep (se 1 (by rfl) ⟨1226153, by rfl⟩ : syracuseStep 1634871 = 2452307) B2452307
theorem B1634891 : Blo 1634016 1634891 := bstep (se 1 (by rfl) ⟨1226168, by rfl⟩ : syracuseStep 1634891 = 2452337) B2452337
theorem B1634903 : Blo 1634016 1634903 := bstep (se 1 (by rfl) ⟨1226177, by rfl⟩ : syracuseStep 1634903 = 2452355) B2452355
theorem B1839703 : Blo 1634016 1839703 := bstep (se 1 (by rfl) ⟨1379777, by rfl⟩ : syracuseStep 1839703 = 2759555) B2759555
theorem B1634923 : Blo 1634016 1634923 := bstep (se 1 (by rfl) ⟨1226192, by rfl⟩ : syracuseStep 1634923 = 2452385) B2452385
theorem B1634935 : Blo 1634016 1634935 := bstep (se 1 (by rfl) ⟨1226201, by rfl⟩ : syracuseStep 1634935 = 2452403) B2452403
theorem B1634955 : Blo 1634016 1634955 := bstep (se 1 (by rfl) ⟨1226216, by rfl⟩ : syracuseStep 1634955 = 2452433) B2452433
theorem B1634967 : Blo 1634016 1634967 := bstep (se 1 (by rfl) ⟨1226225, by rfl⟩ : syracuseStep 1634967 = 2452451) B2452451
theorem B1634987 : Blo 1634016 1634987 := bstep (se 1 (by rfl) ⟨1226240, by rfl⟩ : syracuseStep 1634987 = 2452481) B2452481
theorem B1634999 : Blo 1634016 1634999 := bstep (se 1 (by rfl) ⟨1226249, by rfl⟩ : syracuseStep 1634999 = 2452499) B2452499
theorem B1635019 : Blo 1634016 1635019 := bstep (se 1 (by rfl) ⟨1226264, by rfl⟩ : syracuseStep 1635019 = 2452529) B2452529
theorem B1635031 : Blo 1634016 1635031 := bstep (se 1 (by rfl) ⟨1226273, by rfl⟩ : syracuseStep 1635031 = 2452547) B2452547
theorem B1635051 : Blo 1634016 1635051 := bstep (se 1 (by rfl) ⟨1226288, by rfl⟩ : syracuseStep 1635051 = 2452577) B2452577
theorem B1635063 : Blo 1634016 1635063 := bstep (se 1 (by rfl) ⟨1226297, by rfl⟩ : syracuseStep 1635063 = 2452595) B2452595
theorem B1635083 : Blo 1634016 1635083 := bstep (se 1 (by rfl) ⟨1226312, by rfl⟩ : syracuseStep 1635083 = 2452625) B2452625
theorem B1839883 : Blo 1634016 1839883 := bstep (se 1 (by rfl) ⟨1379912, by rfl⟩ : syracuseStep 1839883 = 2759825) B2759825
theorem B1635095 : Blo 1634016 1635095 := bstep (se 1 (by rfl) ⟨1226321, by rfl⟩ : syracuseStep 1635095 = 2452643) B2452643
theorem B1635115 : Blo 1634016 1635115 := bstep (se 1 (by rfl) ⟨1226336, by rfl⟩ : syracuseStep 1635115 = 2452673) B2452673
theorem B1635127 : Blo 1634016 1635127 := bstep (se 1 (by rfl) ⟨1226345, by rfl⟩ : syracuseStep 1635127 = 2452691) B2452691
theorem B15717185 : Blo 1634016 15717185 := bstep (se 2 (by rfl) ⟨5893944, by rfl⟩ : syracuseStep 15717185 = 11787889) B11787889
theorem B1635147 : Blo 1634016 1635147 := bstep (se 1 (by rfl) ⟨1226360, by rfl⟩ : syracuseStep 1635147 = 2452721) B2452721
theorem B1635159 : Blo 1634016 1635159 := bstep (se 1 (by rfl) ⟨1226369, by rfl⟩ : syracuseStep 1635159 = 2452739) B2452739
theorem B4969309 : Blo 1634016 4969309 := bstep (se 3 (by rfl) ⟨931745, by rfl⟩ : syracuseStep 4969309 = 1863491) B1863491
theorem B1635179 : Blo 1634016 1635179 := bstep (se 1 (by rfl) ⟨1226384, by rfl⟩ : syracuseStep 1635179 = 2452769) B2452769
theorem B1635191 : Blo 1634016 1635191 := bstep (se 1 (by rfl) ⟨1226393, by rfl⟩ : syracuseStep 1635191 = 2452787) B2452787
theorem B1839991 : Blo 1634016 1839991 := bstep (se 1 (by rfl) ⟨1379993, by rfl⟩ : syracuseStep 1839991 = 2759987) B2759987
theorem B1635211 : Blo 1634016 1635211 := bstep (se 1 (by rfl) ⟨1226408, by rfl⟩ : syracuseStep 1635211 = 2452817) B2452817
theorem B1635223 : Blo 1634016 1635223 := bstep (se 1 (by rfl) ⟨1226417, by rfl⟩ : syracuseStep 1635223 = 2452835) B2452835
theorem B5239703 : Blo 1634016 5239703 := bstep (se 1 (by rfl) ⟨3929777, by rfl⟩ : syracuseStep 5239703 = 7859555) B7859555
theorem B1635243 : Blo 1634016 1635243 := bstep (se 1 (by rfl) ⟨1226432, by rfl⟩ : syracuseStep 1635243 = 2452865) B2452865
theorem B22385585 : Blo 1634016 22385585 := bstep (se 2 (by rfl) ⟨8394594, by rfl⟩ : syracuseStep 22385585 = 16789189) B16789189
theorem B5518259 : Blo 1634016 5518259 := bstep (se 1 (by rfl) ⟨4138694, by rfl⟩ : syracuseStep 5518259 = 8277389) B8277389
theorem B8393651 : Blo 1634016 8393651 := bstep (se 1 (by rfl) ⟨6295238, by rfl⟩ : syracuseStep 8393651 = 12590477) B12590477
theorem B1635255 : Blo 1634016 1635255 := bstep (se 1 (by rfl) ⟨1226441, by rfl⟩ : syracuseStep 1635255 = 2452883) B2452883
theorem B1635275 : Blo 1634016 1635275 := bstep (se 1 (by rfl) ⟨1226456, by rfl⟩ : syracuseStep 1635275 = 2452913) B2452913
theorem B13964237 : Blo 1634016 13964237 := bstep (se 3 (by rfl) ⟨2618294, by rfl⟩ : syracuseStep 13964237 = 5236589) B5236589
theorem B2618327 : Blo 1634016 2618327 := bstep (se 1 (by rfl) ⟨1963745, by rfl⟩ : syracuseStep 2618327 = 3927491) B3927491
theorem B1635287 : Blo 1634016 1635287 := bstep (se 1 (by rfl) ⟨1226465, by rfl⟩ : syracuseStep 1635287 = 2452931) B2452931
theorem B1635307 : Blo 1634016 1635307 := bstep (se 1 (by rfl) ⟨1226480, by rfl⟩ : syracuseStep 1635307 = 2452961) B2452961
theorem B1635319 : Blo 1634016 1635319 := bstep (se 1 (by rfl) ⟨1226489, by rfl⟩ : syracuseStep 1635319 = 2452979) B2452979
theorem B1635339 : Blo 1634016 1635339 := bstep (se 1 (by rfl) ⟨1226504, by rfl⟩ : syracuseStep 1635339 = 2453009) B2453009
theorem B57373717 : Blo 1634016 57373717 := bstep (se 6 (by rfl) ⟨1344696, by rfl⟩ : syracuseStep 57373717 = 2689393) B2689393
theorem B1635351 : Blo 1634016 1635351 := bstep (se 1 (by rfl) ⟨1226513, by rfl⟩ : syracuseStep 1635351 = 2453027) B2453027
theorem B1635371 : Blo 1634016 1635371 := bstep (se 1 (by rfl) ⟨1226528, by rfl⟩ : syracuseStep 1635371 = 2453057) B2453057
theorem B1840171 : Blo 1634016 1840171 := bstep (se 1 (by rfl) ⟨1380128, by rfl⟩ : syracuseStep 1840171 = 2760257) B2760257
theorem B1635383 : Blo 1634016 1635383 := bstep (se 1 (by rfl) ⟨1226537, by rfl⟩ : syracuseStep 1635383 = 2453075) B2453075
theorem B1635403 : Blo 1634016 1635403 := bstep (se 1 (by rfl) ⟨1226552, by rfl⟩ : syracuseStep 1635403 = 2453105) B2453105
theorem B2757719 : Blo 1634016 2757719 := bstep (se 1 (by rfl) ⟨2068289, by rfl⟩ : syracuseStep 2757719 = 4136579) B4136579
theorem B1635415 : Blo 1634016 1635415 := bstep (se 1 (by rfl) ⟨1226561, by rfl⟩ : syracuseStep 1635415 = 2453123) B2453123
theorem B1635435 : Blo 1634016 1635435 := bstep (se 1 (by rfl) ⟨1226576, by rfl⟩ : syracuseStep 1635435 = 2453153) B2453153
theorem B1635447 : Blo 1634016 1635447 := bstep (se 1 (by rfl) ⟨1226585, by rfl⟩ : syracuseStep 1635447 = 2453171) B2453171
theorem B8279171 : Blo 1634016 8279171 := bstep (se 1 (by rfl) ⟨6209378, by rfl⟩ : syracuseStep 8279171 = 12418757) B12418757
theorem B1635467 : Blo 1634016 1635467 := bstep (se 1 (by rfl) ⟨1226600, by rfl⟩ : syracuseStep 1635467 = 2453201) B2453201
theorem B46576781 : Blo 1634016 46576781 := bstep (se 3 (by rfl) ⟨8733146, by rfl⟩ : syracuseStep 46576781 = 17466293) B17466293
theorem B6206615 : Blo 1634016 6206615 := bstep (se 1 (by rfl) ⟨4654961, by rfl⟩ : syracuseStep 6206615 = 9309923) B9309923
theorem B1635479 : Blo 1634016 1635479 := bstep (se 1 (by rfl) ⟨1226609, by rfl⟩ : syracuseStep 1635479 = 2453219) B2453219
theorem B1840279 : Blo 1634016 1840279 := bstep (se 1 (by rfl) ⟨1380209, by rfl⟩ : syracuseStep 1840279 = 2760419) B2760419
theorem B1635499 : Blo 1634016 1635499 := bstep (se 1 (by rfl) ⟨1226624, by rfl⟩ : syracuseStep 1635499 = 2453249) B2453249
theorem B1635511 : Blo 1634016 1635511 := bstep (se 1 (by rfl) ⟨1226633, by rfl⟩ : syracuseStep 1635511 = 2453267) B2453267
theorem B5518529 : Blo 1634016 5518529 := bstep (se 2 (by rfl) ⟨2069448, by rfl⟩ : syracuseStep 5518529 = 4138897) B4138897
theorem B2069707 : Blo 1634016 2069707 := bstep (se 1 (by rfl) ⟨1552280, by rfl⟩ : syracuseStep 2069707 = 3104561) B3104561
theorem B1635531 : Blo 1634016 1635531 := bstep (se 1 (by rfl) ⟨1226648, by rfl⟩ : syracuseStep 1635531 = 2453297) B2453297
theorem B5240011 : Blo 1634016 5240011 := bstep (se 1 (by rfl) ⟨3930008, by rfl⟩ : syracuseStep 5240011 = 7860017) B7860017
theorem B2757847 : Blo 1634016 2757847 := bstep (se 1 (by rfl) ⟨2068385, by rfl⟩ : syracuseStep 2757847 = 4136771) B4136771
theorem B1635543 : Blo 1634016 1635543 := bstep (se 1 (by rfl) ⟨1226657, by rfl⟩ : syracuseStep 1635543 = 2453315) B2453315
theorem B1635563 : Blo 1634016 1635563 := bstep (se 1 (by rfl) ⟨1226672, by rfl⟩ : syracuseStep 1635563 = 2453345) B2453345
theorem B1635575 : Blo 1634016 1635575 := bstep (se 1 (by rfl) ⟨1226681, by rfl⟩ : syracuseStep 1635575 = 2453363) B2453363
theorem B1635595 : Blo 1634016 1635595 := bstep (se 1 (by rfl) ⟨1226696, by rfl⟩ : syracuseStep 1635595 = 2453393) B2453393
theorem B1635607 : Blo 1634016 1635607 := bstep (se 1 (by rfl) ⟨1226705, by rfl⟩ : syracuseStep 1635607 = 2453411) B2453411
theorem B1635627 : Blo 1634016 1635627 := bstep (se 1 (by rfl) ⟨1226720, by rfl⟩ : syracuseStep 1635627 = 2453441) B2453441
theorem B1635639 : Blo 1634016 1635639 := bstep (se 1 (by rfl) ⟨1226729, by rfl⟩ : syracuseStep 1635639 = 2453459) B2453459
theorem B1635659 : Blo 1634016 1635659 := bstep (se 1 (by rfl) ⟨1226744, by rfl⟩ : syracuseStep 1635659 = 2453489) B2453489
theorem B1840459 : Blo 1634016 1840459 := bstep (se 1 (by rfl) ⟨1380344, by rfl⟩ : syracuseStep 1840459 = 2760689) B2760689
theorem B2618711 : Blo 1634016 2618711 := bstep (se 1 (by rfl) ⟨1964033, by rfl⟩ : syracuseStep 2618711 = 3928067) B3928067
theorem B1635671 : Blo 1634016 1635671 := bstep (se 1 (by rfl) ⟨1226753, by rfl⟩ : syracuseStep 1635671 = 2453507) B2453507
theorem B6206813 : Blo 1634016 6206813 := bstep (se 3 (by rfl) ⟨1163777, by rfl⟩ : syracuseStep 6206813 = 2327555) B2327555
theorem B1635691 : Blo 1634016 1635691 := bstep (se 1 (by rfl) ⟨1226768, by rfl⟩ : syracuseStep 1635691 = 2453537) B2453537
theorem B1635703 : Blo 1634016 1635703 := bstep (se 1 (by rfl) ⟨1226777, by rfl⟩ : syracuseStep 1635703 = 2453555) B2453555
theorem B1635723 : Blo 1634016 1635723 := bstep (se 1 (by rfl) ⟨1226792, by rfl⟩ : syracuseStep 1635723 = 2453585) B2453585
theorem B1635735 : Blo 1634016 1635735 := bstep (se 1 (by rfl) ⟨1226801, by rfl⟩ : syracuseStep 1635735 = 2453603) B2453603
theorem B1635755 : Blo 1634016 1635755 := bstep (se 1 (by rfl) ⟨1226816, by rfl⟩ : syracuseStep 1635755 = 2453633) B2453633
theorem B3102131 : Blo 1634016 3102131 := bstep (se 1 (by rfl) ⟨2326598, by rfl⟩ : syracuseStep 3102131 = 4653197) B4653197
theorem B1635767 : Blo 1634016 1635767 := bstep (se 1 (by rfl) ⟨1226825, by rfl⟩ : syracuseStep 1635767 = 2453651) B2453651
theorem B1635787 : Blo 1634016 1635787 := bstep (se 1 (by rfl) ⟨1226840, by rfl⟩ : syracuseStep 1635787 = 2453681) B2453681
theorem B2618839 : Blo 1634016 2618839 := bstep (se 1 (by rfl) ⟨1964129, by rfl⟩ : syracuseStep 2618839 = 3928259) B3928259
theorem B2069975 : Blo 1634016 2069975 := bstep (se 1 (by rfl) ⟨1552481, by rfl⟩ : syracuseStep 2069975 = 3104963) B3104963
theorem B1635799 : Blo 1634016 1635799 := bstep (se 1 (by rfl) ⟨1226849, by rfl⟩ : syracuseStep 1635799 = 2453699) B2453699
theorem B1635819 : Blo 1634016 1635819 := bstep (se 1 (by rfl) ⟨1226864, by rfl⟩ : syracuseStep 1635819 = 2453729) B2453729
theorem B1635831 : Blo 1634016 1635831 := bstep (se 1 (by rfl) ⟨1226873, by rfl⟩ : syracuseStep 1635831 = 2453747) B2453747
theorem B1635851 : Blo 1634016 1635851 := bstep (se 1 (by rfl) ⟨1226888, by rfl⟩ : syracuseStep 1635851 = 2453777) B2453777
theorem B1635863 : Blo 1634016 1635863 := bstep (se 1 (by rfl) ⟨1226897, by rfl⟩ : syracuseStep 1635863 = 2453795) B2453795
theorem B1635883 : Blo 1634016 1635883 := bstep (se 1 (by rfl) ⟨1226912, by rfl⟩ : syracuseStep 1635883 = 2453825) B2453825
theorem B1635895 : Blo 1634016 1635895 := bstep (se 1 (by rfl) ⟨1226921, by rfl⟩ : syracuseStep 1635895 = 2453843) B2453843
theorem B5969483 : Blo 1634016 5969483 := bstep (se 1 (by rfl) ⟨4477112, by rfl⟩ : syracuseStep 5969483 = 8954225) B8954225
theorem B1635915 : Blo 1634016 1635915 := bstep (se 1 (by rfl) ⟨1226936, by rfl⟩ : syracuseStep 1635915 = 2453873) B2453873
theorem B1635927 : Blo 1634016 1635927 := bstep (se 1 (by rfl) ⟨1226945, by rfl⟩ : syracuseStep 1635927 = 2453891) B2453891
theorem B1635947 : Blo 1634016 1635947 := bstep (se 1 (by rfl) ⟨1226960, by rfl⟩ : syracuseStep 1635947 = 2453921) B2453921
theorem B1635959 : Blo 1634016 1635959 := bstep (se 1 (by rfl) ⟨1226969, by rfl⟩ : syracuseStep 1635959 = 2453939) B2453939
theorem B1635979 : Blo 1634016 1635979 := bstep (se 1 (by rfl) ⟨1226984, by rfl⟩ : syracuseStep 1635979 = 2453969) B2453969
theorem B1635991 : Blo 1634016 1635991 := bstep (se 1 (by rfl) ⟨1226993, by rfl⟩ : syracuseStep 1635991 = 2453987) B2453987
theorem B1636011 : Blo 1634016 1636011 := bstep (se 1 (by rfl) ⟨1227008, by rfl⟩ : syracuseStep 1636011 = 2454017) B2454017
theorem B5519069 : Blo 1634016 5519069 := bstep (se 3 (by rfl) ⟨1034825, by rfl⟩ : syracuseStep 5519069 = 2069651) B2069651
theorem B3315467 : Blo 1634016 3315467 := bstep (se 1 (by rfl) ⟨2486600, by rfl⟩ : syracuseStep 3315467 = 4973201) B4973201
theorem B12416813 : Blo 1634016 12416813 := bstep (se 3 (by rfl) ⟨2328152, by rfl⟩ : syracuseStep 12416813 = 4656305) B4656305
theorem B2758475 : Blo 1634016 2758475 := bstep (se 1 (by rfl) ⟨2068856, by rfl⟩ : syracuseStep 2758475 = 4137713) B4137713
theorem B3102617 : Blo 1634016 3102617 := bstep (se 2 (by rfl) ⟨1163481, by rfl⟩ : syracuseStep 3102617 = 2326963) B2326963
theorem B2758603 : Blo 1634016 2758603 := bstep (se 1 (by rfl) ⟨2068952, by rfl⟩ : syracuseStep 2758603 = 4137905) B4137905
theorem B4970585 : Blo 1634016 4970585 := bstep (se 2 (by rfl) ⟨1863969, by rfl⟩ : syracuseStep 4970585 = 3727939) B3727939
theorem B2758745 : Blo 1634016 2758745 := bstep (se 2 (by rfl) ⟨1034529, by rfl⟩ : syracuseStep 2758745 = 2069059) B2069059
theorem B9312407 : Blo 1634016 9312407 := bstep (se 1 (by rfl) ⟨6984305, by rfl⟩ : syracuseStep 9312407 = 13968611) B13968611
theorem B41924789 : Blo 1634016 41924789 := bstep (se 5 (by rfl) ⟨1965224, by rfl⟩ : syracuseStep 41924789 = 3930449) B3930449
theorem B12409037 : Blo 1634016 12409037 := bstep (se 3 (by rfl) ⟨2326694, by rfl⟩ : syracuseStep 12409037 = 4653389) B4653389
theorem B2758873 : Blo 1634016 2758873 := bstep (se 2 (by rfl) ⟨1034577, by rfl⟩ : syracuseStep 2758873 = 2069155) B2069155
theorem B2619659 : Blo 1634016 2619659 := bstep (se 1 (by rfl) ⟨1964744, by rfl⟩ : syracuseStep 2619659 = 3929489) B3929489
theorem B2619787 : Blo 1634016 2619787 := bstep (se 1 (by rfl) ⟨1964840, by rfl⟩ : syracuseStep 2619787 = 3929681) B3929681
theorem B11188631 : Blo 1634016 11188631 := bstep (se 1 (by rfl) ⟨8391473, by rfl⟩ : syracuseStep 11188631 = 16782947) B16782947
theorem B2947607 : Blo 1634016 2947607 := bstep (se 1 (by rfl) ⟨2210705, by rfl⟩ : syracuseStep 2947607 = 4421411) B4421411
theorem B3676697 : Blo 1634016 3676697 := bstep (se 2 (by rfl) ⟨1378761, by rfl⟩ : syracuseStep 3676697 = 2757523) B2757523
theorem B11778635 : Blo 1634016 11778635 := bstep (se 1 (by rfl) ⟨8833976, by rfl⟩ : syracuseStep 11778635 = 17667953) B17667953
theorem B10476125 : Blo 1634016 10476125 := bstep (se 3 (by rfl) ⟨1964273, by rfl⟩ : syracuseStep 10476125 = 3928547) B3928547
theorem B18889309 : Blo 1634016 18889309 := bstep (se 3 (by rfl) ⟨3541745, by rfl⟩ : syracuseStep 18889309 = 7083491) B7083491
theorem B3676787 : Blo 1634016 3676787 := bstep (se 1 (by rfl) ⟨2757590, by rfl⟩ : syracuseStep 3676787 = 5515181) B5515181
theorem B3676823 : Blo 1634016 3676823 := bstep (se 1 (by rfl) ⟨2757617, by rfl⟩ : syracuseStep 3676823 = 5515235) B5515235
theorem B12409523 : Blo 1634016 12409523 := bstep (se 1 (by rfl) ⟨9307142, by rfl⟩ : syracuseStep 12409523 = 18614285) B18614285
theorem B14916275 : Blo 1634016 14916275 := bstep (se 1 (by rfl) ⟨11187206, by rfl⟩ : syracuseStep 14916275 = 22374413) B22374413
theorem B8837849 : Blo 1634016 8837849 := bstep (se 2 (by rfl) ⟨3314193, by rfl⟩ : syracuseStep 8837849 = 6628387) B6628387
theorem B4479709 : Blo 1634016 4479709 := bstep (se 3 (by rfl) ⟨839945, by rfl⟩ : syracuseStep 4479709 = 1679891) B1679891
theorem B2759447 : Blo 1634016 2759447 := bstep (se 1 (by rfl) ⟨2069585, by rfl⟩ : syracuseStep 2759447 = 4139171) B4139171
theorem B3677003 : Blo 1634016 3677003 := bstep (se 1 (by rfl) ⟨2757752, by rfl⟩ : syracuseStep 3677003 = 5515505) B5515505
theorem B5520203 : Blo 1634016 5520203 := bstep (se 1 (by rfl) ⟨4140152, by rfl⟩ : syracuseStep 5520203 = 8280305) B8280305
theorem B3677057 : Blo 1634016 3677057 := bstep (se 2 (by rfl) ⟨1378896, by rfl⟩ : syracuseStep 3677057 = 2757793) B2757793
theorem B2759575 : Blo 1634016 2759575 := bstep (se 1 (by rfl) ⟨2069681, by rfl⟩ : syracuseStep 2759575 = 4139363) B4139363
theorem B21232601 : Blo 1634016 21232601 := bstep (se 2 (by rfl) ⟨7962225, by rfl⟩ : syracuseStep 21232601 = 15924451) B15924451
theorem B31857625 : Blo 1634016 31857625 := bstep (se 2 (by rfl) ⟨11946609, by rfl⟩ : syracuseStep 31857625 = 23893219) B23893219
theorem B3677273 : Blo 1634016 3677273 := bstep (se 2 (by rfl) ⟨1378977, by rfl⟩ : syracuseStep 3677273 = 2757955) B2757955
theorem B5520473 : Blo 1634016 5520473 := bstep (se 2 (by rfl) ⟨2070177, by rfl⟩ : syracuseStep 5520473 = 4140355) B4140355
theorem B6290525 : Blo 1634016 6290525 := bstep (se 3 (by rfl) ⟨1179473, by rfl⟩ : syracuseStep 6290525 = 2358947) B2358947
theorem B3677363 : Blo 1634016 3677363 := bstep (se 1 (by rfl) ⟨2758022, by rfl⟩ : syracuseStep 3677363 = 5516045) B5516045
theorem B1965259 : Blo 1634016 1965259 := bstep (se 1 (by rfl) ⟨1473944, by rfl⟩ : syracuseStep 1965259 = 2947889) B2947889
theorem B3677399 : Blo 1634016 3677399 := bstep (se 1 (by rfl) ⟨2758049, by rfl⟩ : syracuseStep 3677399 = 5516099) B5516099
theorem B6208771 : Blo 1634016 6208771 := bstep (se 1 (by rfl) ⟨4656578, by rfl⟩ : syracuseStep 6208771 = 9313157) B9313157
theorem B3104075 : Blo 1634016 3104075 := bstep (se 1 (by rfl) ⟨2328056, by rfl⟩ : syracuseStep 3104075 = 4656113) B4656113
theorem B3145049 : Blo 1634016 3145049 := bstep (se 2 (by rfl) ⟨1179393, by rfl⟩ : syracuseStep 3145049 = 2358787) B2358787
theorem B3677579 : Blo 1634016 3677579 := bstep (se 1 (by rfl) ⟨2758184, by rfl⟩ : syracuseStep 3677579 = 5516369) B5516369
theorem B3677633 : Blo 1634016 3677633 := bstep (se 2 (by rfl) ⟨1379112, by rfl⟩ : syracuseStep 3677633 = 2758225) B2758225
theorem B3104257 : Blo 1634016 3104257 := bstep (se 2 (by rfl) ⟨1164096, by rfl⟩ : syracuseStep 3104257 = 2328193) B2328193
theorem B2760203 : Blo 1634016 2760203 := bstep (se 1 (by rfl) ⟨2070152, by rfl⟩ : syracuseStep 2760203 = 4140305) B4140305
theorem B6626861 : Blo 1634016 6626861 := bstep (se 3 (by rfl) ⟨1242536, by rfl⟩ : syracuseStep 6626861 = 2485073) B2485073
theorem B6209075 : Blo 1634016 6209075 := bstep (se 1 (by rfl) ⟨4656806, by rfl⟩ : syracuseStep 6209075 = 9313613) B9313613
theorem B6987329 : Blo 1634016 6987329 := bstep (se 2 (by rfl) ⟨2620248, by rfl⟩ : syracuseStep 6987329 = 5240497) B5240497
theorem B8273501 : Blo 1634016 8273501 := bstep (se 3 (by rfl) ⟨1551281, by rfl⟩ : syracuseStep 8273501 = 3102563) B3102563
theorem B2760331 : Blo 1634016 2760331 := bstep (se 1 (by rfl) ⟨2070248, by rfl⟩ : syracuseStep 2760331 = 4140497) B4140497
theorem B3677849 : Blo 1634016 3677849 := bstep (se 2 (by rfl) ⟨1379193, by rfl⟩ : syracuseStep 3677849 = 2758387) B2758387
theorem B3677939 : Blo 1634016 3677939 := bstep (se 1 (by rfl) ⟨2758454, by rfl⟩ : syracuseStep 3677939 = 5516909) B5516909
theorem B6627089 : Blo 1634016 6627089 := bstep (se 2 (by rfl) ⟨2485158, by rfl⟩ : syracuseStep 6627089 = 4970317) B4970317
theorem B3677975 : Blo 1634016 3677975 := bstep (se 1 (by rfl) ⟨2758481, by rfl⟩ : syracuseStep 3677975 = 5516963) B5516963
theorem B5521175 : Blo 1634016 5521175 := bstep (se 1 (by rfl) ⟨4140881, by rfl⟩ : syracuseStep 5521175 = 8281763) B8281763
theorem B2760473 : Blo 1634016 2760473 := bstep (se 2 (by rfl) ⟨1035177, by rfl⟩ : syracuseStep 2760473 = 2070355) B2070355
theorem B6987671 : Blo 1634016 6987671 := bstep (se 1 (by rfl) ⟨5240753, by rfl⟩ : syracuseStep 6987671 = 10481507) B10481507
theorem B2760601 : Blo 1634016 2760601 := bstep (se 2 (by rfl) ⟨1035225, by rfl⟩ : syracuseStep 2760601 = 2070451) B2070451
theorem B45957041 : Blo 1634016 45957041 := bstep (se 2 (by rfl) ⟨17233890, by rfl⟩ : syracuseStep 45957041 = 34467781) B34467781
theorem B3104705 : Blo 1634016 3104705 := bstep (se 2 (by rfl) ⟨1164264, by rfl⟩ : syracuseStep 3104705 = 2328529) B2328529
theorem B3678155 : Blo 1634016 3678155 := bstep (se 1 (by rfl) ⟨2758616, by rfl⟩ : syracuseStep 3678155 = 5517233) B5517233
theorem B28319705 : Blo 1634016 28319705 := bstep (se 2 (by rfl) ⟨10619889, by rfl⟩ : syracuseStep 28319705 = 21239779) B21239779
theorem B2760763 : Blo 1634016 2760763 := bstep (se 1 (by rfl) ⟨2070572, by rfl⟩ : syracuseStep 2760763 = 4141145) B4141145
theorem B8273987 : Blo 1634016 8273987 := bstep (se 1 (by rfl) ⟨6205490, by rfl⟩ : syracuseStep 8273987 = 12410981) B12410981
theorem B5234807 : Blo 1634016 5234807 := bstep (se 1 (by rfl) ⟨3926105, by rfl⟩ : syracuseStep 5234807 = 7852211) B7852211
theorem B3104887 : Blo 1634016 3104887 := bstep (se 1 (by rfl) ⟨2328665, by rfl⟩ : syracuseStep 3104887 = 4657331) B4657331
theorem B4137095 : Blo 1634016 4137095 := bstep (se 1 (by rfl) ⟨3102821, by rfl⟩ : syracuseStep 4137095 = 6205643) B6205643
theorem B4137227 : Blo 1634016 4137227 := bstep (se 1 (by rfl) ⟨3102920, by rfl⟩ : syracuseStep 4137227 = 6205841) B6205841
theorem B3678479 : Blo 1634016 3678479 := bstep (se 1 (by rfl) ⟨2758859, by rfl⟩ : syracuseStep 3678479 = 5517719) B5517719
theorem B3678497 : Blo 1634016 3678497 := bstep (se 2 (by rfl) ⟨1379436, by rfl⟩ : syracuseStep 3678497 = 2758873) B2758873
theorem B2326843 : Blo 1634016 2326843 := bstep (se 1 (by rfl) ⟨1745132, by rfl⟩ : syracuseStep 2326843 = 3490265) B3490265
theorem B8274311 : Blo 1634016 8274311 := bstep (se 1 (by rfl) ⟨6205733, by rfl⟩ : syracuseStep 8274311 = 12411467) B12411467
theorem B2359687 : Blo 1634016 2359687 := bstep (se 1 (by rfl) ⟨1769765, by rfl⟩ : syracuseStep 2359687 = 3539531) B3539531
theorem B10478123 : Blo 1634016 10478123 := bstep (se 1 (by rfl) ⟨7858592, by rfl⟩ : syracuseStep 10478123 = 15717185) B15717185
theorem B3678839 : Blo 1634016 3678839 := bstep (se 1 (by rfl) ⟨2759129, by rfl⟩ : syracuseStep 3678839 = 5518259) B5518259
theorem B5595767 : Blo 1634016 5595767 := bstep (se 1 (by rfl) ⟨4196825, by rfl⟩ : syracuseStep 5595767 = 8393651) B8393651
theorem B1745551 : Blo 1634016 1745551 := bstep (se 1 (by rfl) ⟨1309163, by rfl⟩ : syracuseStep 1745551 = 2618327) B2618327
theorem B11780801 : Blo 1634016 11780801 := bstep (se 2 (by rfl) ⟨4417800, by rfl⟩ : syracuseStep 11780801 = 8835601) B8835601
theorem B11191013 : Blo 1634016 11191013 := bstep (se 4 (by rfl) ⟨1049157, by rfl⟩ : syracuseStep 11191013 = 2098315) B2098315
theorem B2327287 : Blo 1634016 2327287 := bstep (se 1 (by rfl) ⟨1745465, by rfl⟩ : syracuseStep 2327287 = 3490931) B3490931
theorem B4137743 : Blo 1634016 4137743 := bstep (se 1 (by rfl) ⟨3103307, by rfl⟩ : syracuseStep 4137743 = 6206615) B6206615
theorem B4481821 : Blo 1634016 4481821 := bstep (se 3 (by rfl) ⟨840341, by rfl⟩ : syracuseStep 4481821 = 1680683) B1680683
theorem B28312355 : Blo 1634016 28312355 := bstep (se 1 (by rfl) ⟨21234266, by rfl⟩ : syracuseStep 28312355 = 42468533) B42468533
theorem B3679019 : Blo 1634016 3679019 := bstep (se 1 (by rfl) ⟨2759264, by rfl⟩ : syracuseStep 3679019 = 5518529) B5518529
theorem B1745807 : Blo 1634016 1745807 := bstep (se 1 (by rfl) ⟨1309355, by rfl⟩ : syracuseStep 1745807 = 2618711) B2618711
theorem B4137875 : Blo 1634016 4137875 := bstep (se 1 (by rfl) ⟨3103406, by rfl⟩ : syracuseStep 4137875 = 6206813) B6206813
theorem B4785097 : Blo 1634016 4785097 := bstep (se 2 (by rfl) ⟨1794411, by rfl⟩ : syracuseStep 4785097 = 3588823) B3588823
theorem B5972945 : Blo 1634016 5972945 := bstep (se 2 (by rfl) ⟨2239854, by rfl⟩ : syracuseStep 5972945 = 4479709) B4479709
theorem B4654199 : Blo 1634016 4654199 := bstep (se 1 (by rfl) ⟨3490649, by rfl⟩ : syracuseStep 4654199 = 6981299) B6981299
theorem B3679379 : Blo 1634016 3679379 := bstep (se 1 (by rfl) ⟨2759534, by rfl⟩ : syracuseStep 3679379 = 5519069) B5519069
theorem B3679433 : Blo 1634016 3679433 := bstep (se 2 (by rfl) ⟨1379787, by rfl⟩ : syracuseStep 3679433 = 2759575) B2759575
theorem B42476833 : Blo 1634016 42476833 := bstep (se 2 (by rfl) ⟨15928812, by rfl⟩ : syracuseStep 42476833 = 31857625) B31857625
theorem B8504635 : Blo 1634016 8504635 := bstep (se 1 (by rfl) ⟨6378476, by rfl⟩ : syracuseStep 8504635 = 12756953) B12756953
theorem B76498289 : Blo 1634016 76498289 := bstep (se 2 (by rfl) ⟨28686858, by rfl⟩ : syracuseStep 76498289 = 57373717) B57373717
theorem B9307507 : Blo 1634016 9307507 := bstep (se 1 (by rfl) ⟨6980630, by rfl⟩ : syracuseStep 9307507 = 13961261) B13961261
theorem B31409693 : Blo 1634016 31409693 := bstep (se 3 (by rfl) ⟨5889317, by rfl⟩ : syracuseStep 31409693 = 11778635) B11778635
theorem B2328107 : Blo 1634016 2328107 := bstep (se 1 (by rfl) ⟨1746080, by rfl⟩ : syracuseStep 2328107 = 3492161) B3492161
theorem B18630323 : Blo 1634016 18630323 := bstep (se 1 (by rfl) ⟨13972742, by rfl⟩ : syracuseStep 18630323 = 27945485) B27945485
theorem B2451131 : Blo 1634016 2451131 := bstep (se 1 (by rfl) ⟨1838348, by rfl⟩ : syracuseStep 2451131 = 3676697) B3676697
theorem B8840897 : Blo 1634016 8840897 := bstep (se 2 (by rfl) ⟨3315336, by rfl⟩ : syracuseStep 8840897 = 6630673) B6630673
theorem B2451191 : Blo 1634016 2451191 := bstep (se 1 (by rfl) ⟨1838393, by rfl⟩ : syracuseStep 2451191 = 3676787) B3676787
theorem B2451215 : Blo 1634016 2451215 := bstep (se 1 (by rfl) ⟨1838411, by rfl⟩ : syracuseStep 2451215 = 3676823) B3676823
theorem B2451257 : Blo 1634016 2451257 := bstep (se 2 (by rfl) ⟨919221, by rfl⟩ : syracuseStep 2451257 = 1838443) B1838443
theorem B5891899 : Blo 1634016 5891899 := bstep (se 1 (by rfl) ⟨4418924, by rfl⟩ : syracuseStep 5891899 = 8837849) B8837849
theorem B2451335 : Blo 1634016 2451335 := bstep (se 1 (by rfl) ⟨1838501, by rfl⟩ : syracuseStep 2451335 = 3677003) B3677003
theorem B4196231 : Blo 1634016 4196231 := bstep (se 1 (by rfl) ⟨3147173, by rfl⟩ : syracuseStep 4196231 = 6294347) B6294347
theorem B3680135 : Blo 1634016 3680135 := bstep (se 1 (by rfl) ⟨2760101, by rfl⟩ : syracuseStep 3680135 = 5520203) B5520203
theorem B6211475 : Blo 1634016 6211475 := bstep (se 1 (by rfl) ⟨4658606, by rfl⟩ : syracuseStep 6211475 = 9317213) B9317213
theorem B2451371 : Blo 1634016 2451371 := bstep (se 1 (by rfl) ⟨1838528, by rfl⟩ : syracuseStep 2451371 = 3677057) B3677057
theorem B2451401 : Blo 1634016 2451401 := bstep (se 2 (by rfl) ⟨919275, by rfl⟩ : syracuseStep 2451401 = 1838551) B1838551
theorem B3491785 : Blo 1634016 3491785 := bstep (se 2 (by rfl) ⟨1309419, by rfl⟩ : syracuseStep 3491785 = 2618839) B2618839
theorem B4139009 : Blo 1634016 4139009 := bstep (se 2 (by rfl) ⟨1552128, by rfl⟩ : syracuseStep 4139009 = 3104257) B3104257
theorem B2451515 : Blo 1634016 2451515 := bstep (se 1 (by rfl) ⟨1838636, by rfl⟩ : syracuseStep 2451515 = 3677273) B3677273
theorem B3680315 : Blo 1634016 3680315 := bstep (se 1 (by rfl) ⟨2760236, by rfl⟩ : syracuseStep 3680315 = 5520473) B5520473
theorem B2451575 : Blo 1634016 2451575 := bstep (se 1 (by rfl) ⟨1838681, by rfl⟩ : syracuseStep 2451575 = 3677363) B3677363
theorem B2451599 : Blo 1634016 2451599 := bstep (se 1 (by rfl) ⟨1838699, by rfl⟩ : syracuseStep 2451599 = 3677399) B3677399
theorem B2451641 : Blo 1634016 2451641 := bstep (se 2 (by rfl) ⟨919365, by rfl⟩ : syracuseStep 2451641 = 1838731) B1838731
theorem B3680441 : Blo 1634016 3680441 := bstep (se 2 (by rfl) ⟨1380165, by rfl⟩ : syracuseStep 3680441 = 2760331) B2760331
theorem B2451719 : Blo 1634016 2451719 := bstep (se 1 (by rfl) ⟨1838789, by rfl⟩ : syracuseStep 2451719 = 3677579) B3677579
theorem B2451755 : Blo 1634016 2451755 := bstep (se 1 (by rfl) ⟨1838816, by rfl⟩ : syracuseStep 2451755 = 3677633) B3677633
theorem B2451785 : Blo 1634016 2451785 := bstep (se 2 (by rfl) ⟨919419, by rfl⟩ : syracuseStep 2451785 = 1838839) B1838839
theorem B4417907 : Blo 1634016 4417907 := bstep (se 1 (by rfl) ⟨3313430, by rfl⟩ : syracuseStep 4417907 = 6626861) B6626861
theorem B4139383 : Blo 1634016 4139383 := bstep (se 1 (by rfl) ⟨3104537, by rfl⟩ : syracuseStep 4139383 = 6209075) B6209075
theorem B5515667 : Blo 1634016 5515667 := bstep (se 1 (by rfl) ⟨4136750, by rfl⟩ : syracuseStep 5515667 = 8273501) B8273501
theorem B2451899 : Blo 1634016 2451899 := bstep (se 1 (by rfl) ⟨1838924, by rfl⟩ : syracuseStep 2451899 = 3677849) B3677849
theorem B2451959 : Blo 1634016 2451959 := bstep (se 1 (by rfl) ⟨1838969, by rfl⟩ : syracuseStep 2451959 = 3677939) B3677939
theorem B4418059 : Blo 1634016 4418059 := bstep (se 1 (by rfl) ⟨3313544, by rfl⟩ : syracuseStep 4418059 = 6627089) B6627089
theorem B2451983 : Blo 1634016 2451983 := bstep (se 1 (by rfl) ⟨1838987, by rfl⟩ : syracuseStep 2451983 = 3677975) B3677975
theorem B3680783 : Blo 1634016 3680783 := bstep (se 1 (by rfl) ⟨2760587, by rfl⟩ : syracuseStep 3680783 = 5521175) B5521175
theorem B3680801 : Blo 1634016 3680801 := bstep (se 2 (by rfl) ⟨1380300, by rfl⟩ : syracuseStep 3680801 = 2760601) B2760601
theorem B2452025 : Blo 1634016 2452025 := bstep (se 2 (by rfl) ⟨919509, by rfl⟩ : syracuseStep 2452025 = 1839019) B1839019
theorem B3983959 : Blo 1634016 3983959 := bstep (se 1 (by rfl) ⟨2987969, by rfl⟩ : syracuseStep 3983959 = 5975939) B5975939
theorem B2452103 : Blo 1634016 2452103 := bstep (se 1 (by rfl) ⟨1839077, by rfl⟩ : syracuseStep 2452103 = 3678155) B3678155
theorem B2452139 : Blo 1634016 2452139 := bstep (se 1 (by rfl) ⟨1839104, by rfl⟩ : syracuseStep 2452139 = 3678209) B3678209
theorem B28314305 : Blo 1634016 28314305 := bstep (se 2 (by rfl) ⟨10617864, by rfl⟩ : syracuseStep 28314305 = 21235729) B21235729
theorem B2452169 : Blo 1634016 2452169 := bstep (se 2 (by rfl) ⟨919563, by rfl⟩ : syracuseStep 2452169 = 1839127) B1839127
theorem B16788197 : Blo 1634016 16788197 := bstep (se 4 (by rfl) ⟨1573893, by rfl⟩ : syracuseStep 16788197 = 3147787) B3147787
theorem B4655873 : Blo 1634016 4655873 := bstep (se 2 (by rfl) ⟨1745952, by rfl⟩ : syracuseStep 4655873 = 3491905) B3491905
theorem B11184911 : Blo 1634016 11184911 := bstep (se 1 (by rfl) ⟨8388683, by rfl⟩ : syracuseStep 11184911 = 16777367) B16777367
theorem B9308965 : Blo 1634016 9308965 := bstep (se 4 (by rfl) ⟨872715, by rfl⟩ : syracuseStep 9308965 = 1745431) B1745431
theorem B3926827 : Blo 1634016 3926827 := bstep (se 1 (by rfl) ⟨2945120, by rfl⟩ : syracuseStep 3926827 = 5890241) B5890241
theorem B4139819 : Blo 1634016 4139819 := bstep (se 1 (by rfl) ⟨3104864, by rfl⟩ : syracuseStep 4139819 = 6209729) B6209729
theorem B17673011 : Blo 1634016 17673011 := bstep (se 1 (by rfl) ⟨13254758, by rfl⟩ : syracuseStep 17673011 = 26509517) B26509517
theorem B2452283 : Blo 1634016 2452283 := bstep (se 1 (by rfl) ⟨1839212, by rfl⟩ : syracuseStep 2452283 = 3678425) B3678425
theorem B4655987 : Blo 1634016 4655987 := bstep (se 1 (by rfl) ⟨3491990, by rfl⟩ : syracuseStep 4655987 = 6983981) B6983981
theorem B2452343 : Blo 1634016 2452343 := bstep (se 1 (by rfl) ⟨1839257, by rfl⟩ : syracuseStep 2452343 = 3678515) B3678515
theorem B2452367 : Blo 1634016 2452367 := bstep (se 1 (by rfl) ⟨1839275, by rfl⟩ : syracuseStep 2452367 = 3678551) B3678551
theorem B2452409 : Blo 1634016 2452409 := bstep (se 2 (by rfl) ⟨919653, by rfl⟩ : syracuseStep 2452409 = 1839307) B1839307
theorem B2452487 : Blo 1634016 2452487 := bstep (se 1 (by rfl) ⟨1839365, by rfl⟩ : syracuseStep 2452487 = 3678731) B3678731
theorem B2452523 : Blo 1634016 2452523 := bstep (se 1 (by rfl) ⟨1839392, by rfl⟩ : syracuseStep 2452523 = 3678785) B3678785
theorem B2452553 : Blo 1634016 2452553 := bstep (se 2 (by rfl) ⟨919707, by rfl⟩ : syracuseStep 2452553 = 1839415) B1839415
theorem B3493049 : Blo 1634016 3493049 := bstep (se 2 (by rfl) ⟨1309893, by rfl⟩ : syracuseStep 3493049 = 2619787) B2619787
theorem B2452667 : Blo 1634016 2452667 := bstep (se 1 (by rfl) ⟨1839500, by rfl⟩ : syracuseStep 2452667 = 3679001) B3679001
theorem B4656329 : Blo 1634016 4656329 := bstep (se 2 (by rfl) ⟨1746123, by rfl⟩ : syracuseStep 4656329 = 3492247) B3492247
theorem B2452727 : Blo 1634016 2452727 := bstep (se 1 (by rfl) ⟨1839545, by rfl⟩ : syracuseStep 2452727 = 3679091) B3679091
theorem B2452751 : Blo 1634016 2452751 := bstep (se 1 (by rfl) ⟨1839563, by rfl⟩ : syracuseStep 2452751 = 3679127) B3679127
theorem B3493135 : Blo 1634016 3493135 := bstep (se 1 (by rfl) ⟨2619851, by rfl⟩ : syracuseStep 3493135 = 5239703) B5239703
theorem B9309491 : Blo 1634016 9309491 := bstep (se 1 (by rfl) ⟨6982118, by rfl⟩ : syracuseStep 9309491 = 13964237) B13964237
theorem B2452793 : Blo 1634016 2452793 := bstep (se 2 (by rfl) ⟨919797, by rfl⟩ : syracuseStep 2452793 = 1839595) B1839595
theorem B2452871 : Blo 1634016 2452871 := bstep (se 1 (by rfl) ⟨1839653, by rfl⟩ : syracuseStep 2452871 = 3679307) B3679307
theorem B6139271 : Blo 1634016 6139271 := bstep (se 1 (by rfl) ⟨4604453, by rfl⟩ : syracuseStep 6139271 = 9208907) B9208907
theorem B1838479 : Blo 1634016 1838479 := bstep (se 1 (by rfl) ⟨1378859, by rfl⟩ : syracuseStep 1838479 = 2757719) B2757719
theorem B2452907 : Blo 1634016 2452907 := bstep (se 1 (by rfl) ⟨1839680, by rfl⟩ : syracuseStep 2452907 = 3679361) B3679361
theorem B31051187 : Blo 1634016 31051187 := bstep (se 1 (by rfl) ⟨23288390, by rfl⟩ : syracuseStep 31051187 = 46576781) B46576781
theorem B2452937 : Blo 1634016 2452937 := bstep (se 2 (by rfl) ⟨919851, by rfl⟩ : syracuseStep 2452937 = 1839703) B1839703
theorem B25185745 : Blo 1634016 25185745 := bstep (se 2 (by rfl) ⟨9444654, by rfl⟩ : syracuseStep 25185745 = 18889309) B18889309
theorem B2453051 : Blo 1634016 2453051 := bstep (se 1 (by rfl) ⟨1839788, by rfl⟩ : syracuseStep 2453051 = 3679577) B3679577
theorem B43069027 : Blo 1634016 43069027 := bstep (se 1 (by rfl) ⟨32301770, by rfl⟩ : syracuseStep 43069027 = 64603541) B64603541
theorem B4140659 : Blo 1634016 4140659 := bstep (se 1 (by rfl) ⟨3105494, by rfl⟩ : syracuseStep 4140659 = 6210989) B6210989
theorem B2068087 : Blo 1634016 2068087 := bstep (se 1 (by rfl) ⟨1551065, by rfl⟩ : syracuseStep 2068087 = 3102131) B3102131
theorem B2453111 : Blo 1634016 2453111 := bstep (se 1 (by rfl) ⟨1839833, by rfl⟩ : syracuseStep 2453111 = 3679667) B3679667
theorem B4140679 : Blo 1634016 4140679 := bstep (se 1 (by rfl) ⟨3105509, by rfl⟩ : syracuseStep 4140679 = 6211019) B6211019
theorem B2453135 : Blo 1634016 2453135 := bstep (se 1 (by rfl) ⟨1839851, by rfl⟩ : syracuseStep 2453135 = 3679703) B3679703
theorem B2453177 : Blo 1634016 2453177 := bstep (se 2 (by rfl) ⟨919941, by rfl⟩ : syracuseStep 2453177 = 1839883) B1839883
theorem B1634055 : Blo 1634016 1634055 := bstep (se 1 (by rfl) ⟨1225541, by rfl⟩ : syracuseStep 1634055 = 2451083) B2451083
theorem B2453255 : Blo 1634016 2453255 := bstep (se 1 (by rfl) ⟨1839941, by rfl⟩ : syracuseStep 2453255 = 3679883) B3679883
theorem B1634063 : Blo 1634016 1634063 := bstep (se 1 (by rfl) ⟨1225547, by rfl⟩ : syracuseStep 1634063 = 2451095) B2451095
theorem B5517071 : Blo 1634016 5517071 := bstep (se 1 (by rfl) ⟨4137803, by rfl⟩ : syracuseStep 5517071 = 8275607) B8275607
theorem B2944811 : Blo 1634016 2944811 := bstep (se 1 (by rfl) ⟨2208608, by rfl⟩ : syracuseStep 2944811 = 4417217) B4417217
theorem B2453291 : Blo 1634016 2453291 := bstep (se 1 (by rfl) ⟨1839968, by rfl⟩ : syracuseStep 2453291 = 3679937) B3679937
theorem B1634107 : Blo 1634016 1634107 := bstep (se 1 (by rfl) ⟨1225580, by rfl⟩ : syracuseStep 1634107 = 2451161) B2451161
theorem B2453321 : Blo 1634016 2453321 := bstep (se 2 (by rfl) ⟨919995, by rfl⟩ : syracuseStep 2453321 = 1839991) B1839991
theorem B8277875 : Blo 1634016 8277875 := bstep (se 1 (by rfl) ⟨6208406, by rfl⟩ : syracuseStep 8277875 = 12416813) B12416813
theorem B1634183 : Blo 1634016 1634183 := bstep (se 1 (by rfl) ⟨1225637, by rfl⟩ : syracuseStep 1634183 = 2451275) B2451275
theorem B1838983 : Blo 1634016 1838983 := bstep (se 1 (by rfl) ⟨1379237, by rfl⟩ : syracuseStep 1838983 = 2758475) B2758475
theorem B1634191 : Blo 1634016 1634191 := bstep (se 1 (by rfl) ⟨1225643, by rfl⟩ : syracuseStep 1634191 = 2451287) B2451287
theorem B4140953 : Blo 1634016 4140953 := bstep (se 2 (by rfl) ⟨1552857, by rfl⟩ : syracuseStep 4140953 = 3105715) B3105715
theorem B6205369 : Blo 1634016 6205369 := bstep (se 2 (by rfl) ⟨2327013, by rfl⟩ : syracuseStep 6205369 = 4654027) B4654027
theorem B1634235 : Blo 1634016 1634235 := bstep (se 1 (by rfl) ⟨1225676, by rfl⟩ : syracuseStep 1634235 = 2451353) B2451353
theorem B2068411 : Blo 1634016 2068411 := bstep (se 1 (by rfl) ⟨1551308, by rfl⟩ : syracuseStep 2068411 = 3102617) B3102617
theorem B2453435 : Blo 1634016 2453435 := bstep (se 1 (by rfl) ⟨1840076, by rfl⟩ : syracuseStep 2453435 = 3680153) B3680153
theorem B2453495 : Blo 1634016 2453495 := bstep (se 1 (by rfl) ⟨1840121, by rfl⟩ : syracuseStep 2453495 = 3680243) B3680243
theorem B1634311 : Blo 1634016 1634311 := bstep (se 1 (by rfl) ⟨1225733, by rfl⟩ : syracuseStep 1634311 = 2451467) B2451467
theorem B1634319 : Blo 1634016 1634319 := bstep (se 1 (by rfl) ⟨1225739, by rfl⟩ : syracuseStep 1634319 = 2451479) B2451479
theorem B2453519 : Blo 1634016 2453519 := bstep (se 1 (by rfl) ⟨1840139, by rfl⟩ : syracuseStep 2453519 = 3680279) B3680279
theorem B5517341 : Blo 1634016 5517341 := bstep (se 3 (by rfl) ⟨1034501, by rfl⟩ : syracuseStep 5517341 = 2069003) B2069003
theorem B2453561 : Blo 1634016 2453561 := bstep (se 2 (by rfl) ⟨920085, by rfl⟩ : syracuseStep 2453561 = 1840171) B1840171
theorem B1634363 : Blo 1634016 1634363 := bstep (se 1 (by rfl) ⟨1225772, by rfl⟩ : syracuseStep 1634363 = 2451545) B2451545
theorem B3313723 : Blo 1634016 3313723 := bstep (se 1 (by rfl) ⟨2485292, by rfl⟩ : syracuseStep 3313723 = 4970585) B4970585
theorem B1839163 : Blo 1634016 1839163 := bstep (se 1 (by rfl) ⟨1379372, by rfl⟩ : syracuseStep 1839163 = 2758745) B2758745
theorem B4141115 : Blo 1634016 4141115 := bstep (se 1 (by rfl) ⟨3105836, by rfl⟩ : syracuseStep 4141115 = 6211673) B6211673
theorem B1634439 : Blo 1634016 1634439 := bstep (se 1 (by rfl) ⟨1225829, by rfl⟩ : syracuseStep 1634439 = 2451659) B2451659
theorem B2453639 : Blo 1634016 2453639 := bstep (se 1 (by rfl) ⟨1840229, by rfl⟩ : syracuseStep 2453639 = 3680459) B3680459
theorem B1634447 : Blo 1634016 1634447 := bstep (se 1 (by rfl) ⟨1225835, by rfl⟩ : syracuseStep 1634447 = 2451671) B2451671
theorem B2453675 : Blo 1634016 2453675 := bstep (se 1 (by rfl) ⟨1840256, by rfl⟩ : syracuseStep 2453675 = 3680513) B3680513
theorem B1634491 : Blo 1634016 1634491 := bstep (se 1 (by rfl) ⟨1225868, by rfl⟩ : syracuseStep 1634491 = 2451737) B2451737
theorem B2486459 : Blo 1634016 2486459 := bstep (se 1 (by rfl) ⟨1864844, by rfl⟩ : syracuseStep 2486459 = 3729689) B3729689
theorem B2453705 : Blo 1634016 2453705 := bstep (se 2 (by rfl) ⟨920139, by rfl⟩ : syracuseStep 2453705 = 1840279) B1840279
theorem B1634567 : Blo 1634016 1634567 := bstep (se 1 (by rfl) ⟨1225925, by rfl⟩ : syracuseStep 1634567 = 2451851) B2451851
theorem B1634575 : Blo 1634016 1634575 := bstep (se 1 (by rfl) ⟨1225931, by rfl⟩ : syracuseStep 1634575 = 2451863) B2451863
theorem B7459087 : Blo 1634016 7459087 := bstep (se 1 (by rfl) ⟨5594315, by rfl⟩ : syracuseStep 7459087 = 11188631) B11188631
theorem B1634619 : Blo 1634016 1634619 := bstep (se 1 (by rfl) ⟨1225964, by rfl⟩ : syracuseStep 1634619 = 2451929) B2451929
theorem B2453819 : Blo 1634016 2453819 := bstep (se 1 (by rfl) ⟨1840364, by rfl⟩ : syracuseStep 2453819 = 3680729) B3680729
theorem B8278361 : Blo 1634016 8278361 := bstep (se 2 (by rfl) ⟨3104385, by rfl⟩ : syracuseStep 8278361 = 6208771) B6208771
theorem B2453879 : Blo 1634016 2453879 := bstep (se 1 (by rfl) ⟨1840409, by rfl⟩ : syracuseStep 2453879 = 3680819) B3680819
theorem B1634695 : Blo 1634016 1634695 := bstep (se 1 (by rfl) ⟨1226021, by rfl⟩ : syracuseStep 1634695 = 2452043) B2452043
theorem B1634703 : Blo 1634016 1634703 := bstep (se 1 (by rfl) ⟨1226027, by rfl⟩ : syracuseStep 1634703 = 2452055) B2452055
theorem B2453903 : Blo 1634016 2453903 := bstep (se 1 (by rfl) ⟨1840427, by rfl⟩ : syracuseStep 2453903 = 3680855) B3680855
theorem B6984083 : Blo 1634016 6984083 := bstep (se 1 (by rfl) ⟨5238062, by rfl⟩ : syracuseStep 6984083 = 10476125) B10476125
theorem B2453945 : Blo 1634016 2453945 := bstep (se 2 (by rfl) ⟨920229, by rfl⟩ : syracuseStep 2453945 = 1840459) B1840459
theorem B1634747 : Blo 1634016 1634747 := bstep (se 1 (by rfl) ⟨1226060, by rfl⟩ : syracuseStep 1634747 = 2452121) B2452121
theorem B1634823 : Blo 1634016 1634823 := bstep (se 1 (by rfl) ⟨1226117, by rfl⟩ : syracuseStep 1634823 = 2452235) B2452235
theorem B2454023 : Blo 1634016 2454023 := bstep (se 1 (by rfl) ⟨1840517, by rfl⟩ : syracuseStep 2454023 = 3681035) B3681035
theorem B1634831 : Blo 1634016 1634831 := bstep (se 1 (by rfl) ⟨1226123, by rfl⟩ : syracuseStep 1634831 = 2452247) B2452247
theorem B1839631 : Blo 1634016 1839631 := bstep (se 1 (by rfl) ⟨1379723, by rfl⟩ : syracuseStep 1839631 = 2759447) B2759447
theorem B42480163 : Blo 1634016 42480163 := bstep (se 1 (by rfl) ⟨31860122, by rfl⟩ : syracuseStep 42480163 = 63720245) B63720245
theorem B1634875 : Blo 1634016 1634875 := bstep (se 1 (by rfl) ⟨1226156, by rfl⟩ : syracuseStep 1634875 = 2452313) B2452313
theorem B1634951 : Blo 1634016 1634951 := bstep (se 1 (by rfl) ⟨1226213, by rfl⟩ : syracuseStep 1634951 = 2452427) B2452427
theorem B1634959 : Blo 1634016 1634959 := bstep (se 1 (by rfl) ⟨1226219, by rfl⟩ : syracuseStep 1634959 = 2452439) B2452439
theorem B1635003 : Blo 1634016 1635003 := bstep (se 1 (by rfl) ⟨1226252, by rfl⟩ : syracuseStep 1635003 = 2452505) B2452505
theorem B9310949 : Blo 1634016 9310949 := bstep (se 4 (by rfl) ⟨872901, by rfl⟩ : syracuseStep 9310949 = 1745803) B1745803
theorem B1635079 : Blo 1634016 1635079 := bstep (se 1 (by rfl) ⟨1226309, by rfl⟩ : syracuseStep 1635079 = 2452619) B2452619
theorem B1635087 : Blo 1634016 1635087 := bstep (se 1 (by rfl) ⟨1226315, by rfl⟩ : syracuseStep 1635087 = 2452631) B2452631
theorem B5894927 : Blo 1634016 5894927 := bstep (se 1 (by rfl) ⟨4421195, by rfl⟩ : syracuseStep 5894927 = 8842391) B8842391
theorem B1635131 : Blo 1634016 1635131 := bstep (se 1 (by rfl) ⟨1226348, by rfl⟩ : syracuseStep 1635131 = 2452697) B2452697
theorem B2069383 : Blo 1634016 2069383 := bstep (se 1 (by rfl) ⟨1552037, by rfl⟩ : syracuseStep 2069383 = 3104075) B3104075
theorem B1635207 : Blo 1634016 1635207 := bstep (se 1 (by rfl) ⟨1226405, by rfl⟩ : syracuseStep 1635207 = 2452811) B2452811
theorem B1635215 : Blo 1634016 1635215 := bstep (se 1 (by rfl) ⟨1226411, by rfl⟩ : syracuseStep 1635215 = 2452823) B2452823
theorem B1635259 : Blo 1634016 1635259 := bstep (se 1 (by rfl) ⟨1226444, by rfl⟩ : syracuseStep 1635259 = 2452889) B2452889
theorem B2757577 : Blo 1634016 2757577 := bstep (se 2 (by rfl) ⟨1034091, by rfl⟩ : syracuseStep 2757577 = 2068183) B2068183
theorem B1635335 : Blo 1634016 1635335 := bstep (se 1 (by rfl) ⟨1226501, by rfl⟩ : syracuseStep 1635335 = 2453003) B2453003
theorem B1840135 : Blo 1634016 1840135 := bstep (se 1 (by rfl) ⟨1380101, by rfl⟩ : syracuseStep 1840135 = 2760203) B2760203
theorem B1635343 : Blo 1634016 1635343 := bstep (se 1 (by rfl) ⟨1226507, by rfl⟩ : syracuseStep 1635343 = 2453015) B2453015
theorem B4658219 : Blo 1634016 4658219 := bstep (se 1 (by rfl) ⟨3493664, by rfl⟩ : syracuseStep 4658219 = 6987329) B6987329
theorem B1635387 : Blo 1634016 1635387 := bstep (se 1 (by rfl) ⟨1226540, by rfl⟩ : syracuseStep 1635387 = 2453081) B2453081
theorem B1635463 : Blo 1634016 1635463 := bstep (se 1 (by rfl) ⟨1226597, by rfl⟩ : syracuseStep 1635463 = 2453195) B2453195
theorem B1635471 : Blo 1634016 1635471 := bstep (se 1 (by rfl) ⟨1226603, by rfl⟩ : syracuseStep 1635471 = 2453207) B2453207
theorem B1635515 : Blo 1634016 1635515 := bstep (se 1 (by rfl) ⟨1226636, by rfl⟩ : syracuseStep 1635515 = 2453273) B2453273
theorem B1840315 : Blo 1634016 1840315 := bstep (se 1 (by rfl) ⟨1380236, by rfl⟩ : syracuseStep 1840315 = 2760473) B2760473
theorem B1635591 : Blo 1634016 1635591 := bstep (se 1 (by rfl) ⟨1226693, by rfl⟩ : syracuseStep 1635591 = 2453387) B2453387
theorem B1635599 : Blo 1634016 1635599 := bstep (se 1 (by rfl) ⟨1226699, by rfl⟩ : syracuseStep 1635599 = 2453399) B2453399
theorem B4658447 : Blo 1634016 4658447 := bstep (se 1 (by rfl) ⟨3493835, by rfl⟩ : syracuseStep 4658447 = 6987671) B6987671
theorem B2069803 : Blo 1634016 2069803 := bstep (se 1 (by rfl) ⟨1552352, by rfl⟩ : syracuseStep 2069803 = 3104705) B3104705
theorem B18879803 : Blo 1634016 18879803 := bstep (se 1 (by rfl) ⟨14159852, by rfl⟩ : syracuseStep 18879803 = 28319705) B28319705
theorem B1635643 : Blo 1634016 1635643 := bstep (se 1 (by rfl) ⟨1226732, by rfl⟩ : syracuseStep 1635643 = 2453465) B2453465
theorem B1635719 : Blo 1634016 1635719 := bstep (se 1 (by rfl) ⟨1226789, by rfl⟩ : syracuseStep 1635719 = 2453579) B2453579
theorem B1635727 : Blo 1634016 1635727 := bstep (se 1 (by rfl) ⟨1226795, by rfl⟩ : syracuseStep 1635727 = 2453591) B2453591
theorem B5518745 : Blo 1634016 5518745 := bstep (se 2 (by rfl) ⟨2069529, by rfl⟩ : syracuseStep 5518745 = 4139059) B4139059
theorem B1635771 : Blo 1634016 1635771 := bstep (se 1 (by rfl) ⟨1226828, by rfl⟩ : syracuseStep 1635771 = 2453657) B2453657
theorem B17675779 : Blo 1634016 17675779 := bstep (se 1 (by rfl) ⟨13256834, by rfl⟩ : syracuseStep 17675779 = 26513669) B26513669
theorem B1635847 : Blo 1634016 1635847 := bstep (se 1 (by rfl) ⟨1226885, by rfl⟩ : syracuseStep 1635847 = 2453771) B2453771
theorem B3315215 : Blo 1634016 3315215 := bstep (se 1 (by rfl) ⟨2486411, by rfl⟩ : syracuseStep 3315215 = 4972823) B4972823
theorem B2070031 : Blo 1634016 2070031 := bstep (se 1 (by rfl) ⟨1552523, by rfl⟩ : syracuseStep 2070031 = 3105047) B3105047
theorem B1635855 : Blo 1634016 1635855 := bstep (se 1 (by rfl) ⟨1226891, by rfl⟩ : syracuseStep 1635855 = 2453783) B2453783
theorem B1635899 : Blo 1634016 1635899 := bstep (se 1 (by rfl) ⟨1226924, by rfl⟩ : syracuseStep 1635899 = 2453849) B2453849
theorem B2758279 : Blo 1634016 2758279 := bstep (se 1 (by rfl) ⟨2068709, by rfl⟩ : syracuseStep 2758279 = 4137419) B4137419
theorem B1635975 : Blo 1634016 1635975 := bstep (se 1 (by rfl) ⟨1226981, by rfl⟩ : syracuseStep 1635975 = 2453963) B2453963
theorem B1635983 : Blo 1634016 1635983 := bstep (se 1 (by rfl) ⟨1226987, by rfl⟩ : syracuseStep 1635983 = 2453975) B2453975
theorem B2209451 : Blo 1634016 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B35346293 : Blo 1634016 35346293 := bstep (se 5 (by rfl) ⟨1656857, by rfl⟩ : syracuseStep 35346293 = 3313715) B3313715
theorem B14923723 : Blo 1634016 14923723 := bstep (se 1 (by rfl) ⟨11192792, by rfl⟩ : syracuseStep 14923723 = 22385585) B22385585
theorem B5593099 : Blo 1634016 5593099 := bstep (se 1 (by rfl) ⟨4194824, by rfl⟩ : syracuseStep 5593099 = 8389649) B8389649
theorem B6985757 : Blo 1634016 6985757 := bstep (se 3 (by rfl) ⟨1309829, by rfl⟩ : syracuseStep 6985757 = 2619659) B2619659
theorem B5519447 : Blo 1634016 5519447 := bstep (se 1 (by rfl) ⟨4139585, by rfl⟩ : syracuseStep 5519447 = 8279171) B8279171
theorem B2758927 : Blo 1634016 2758927 := bstep (se 1 (by rfl) ⟨2069195, by rfl⟩ : syracuseStep 2758927 = 4138391) B4138391
theorem B3103019 : Blo 1634016 3103019 := bstep (se 1 (by rfl) ⟨2327264, by rfl⟩ : syracuseStep 3103019 = 4654529) B4654529
theorem B3979655 : Blo 1634016 3979655 := bstep (se 1 (by rfl) ⟨2984741, by rfl⟩ : syracuseStep 3979655 = 5969483) B5969483
theorem B8280467 : Blo 1634016 8280467 := bstep (se 1 (by rfl) ⟨6210350, by rfl⟩ : syracuseStep 8280467 = 12420701) B12420701
theorem B6625745 : Blo 1634016 6625745 := bstep (se 2 (by rfl) ⟨2484654, by rfl⟩ : syracuseStep 6625745 = 4969309) B4969309
theorem B2210311 : Blo 1634016 2210311 := bstep (se 1 (by rfl) ⟨1657733, by rfl⟩ : syracuseStep 2210311 = 3315467) B3315467
theorem B3103247 : Blo 1634016 3103247 := bstep (se 1 (by rfl) ⟨2327435, by rfl⟩ : syracuseStep 3103247 = 4654871) B4654871
theorem B3676715 : Blo 1634016 3676715 := bstep (se 1 (by rfl) ⟨2757536, by rfl⟩ : syracuseStep 3676715 = 5515073) B5515073
theorem B5519933 : Blo 1634016 5519933 := bstep (se 3 (by rfl) ⟨1034987, by rfl⟩ : syracuseStep 5519933 = 2069975) B2069975
theorem B6208271 : Blo 1634016 6208271 := bstep (se 1 (by rfl) ⟨4656203, by rfl⟩ : syracuseStep 6208271 = 9312407) B9312407
theorem B27949859 : Blo 1634016 27949859 := bstep (se 1 (by rfl) ⟨20962394, by rfl⟩ : syracuseStep 27949859 = 41924789) B41924789
theorem B2759467 : Blo 1634016 2759467 := bstep (se 1 (by rfl) ⟨2069600, by rfl⟩ : syracuseStep 2759467 = 4139201) B4139201
theorem B8272691 : Blo 1634016 8272691 := bstep (se 1 (by rfl) ⟨6204518, by rfl⟩ : syracuseStep 8272691 = 12409037) B12409037
theorem B3677075 : Blo 1634016 3677075 := bstep (se 1 (by rfl) ⟨2757806, by rfl⟩ : syracuseStep 3677075 = 5515613) B5515613
theorem B2759609 : Blo 1634016 2759609 := bstep (se 2 (by rfl) ⟨1034853, by rfl⟩ : syracuseStep 2759609 = 2069707) B2069707
theorem B6986681 : Blo 1634016 6986681 := bstep (se 2 (by rfl) ⟨2620005, by rfl⟩ : syracuseStep 6986681 = 5240011) B5240011
theorem B2620345 : Blo 1634016 2620345 := bstep (se 2 (by rfl) ⟨982629, by rfl⟩ : syracuseStep 2620345 = 1965259) B1965259
theorem B3677129 : Blo 1634016 3677129 := bstep (se 2 (by rfl) ⟨1378923, by rfl⟩ : syracuseStep 3677129 = 2757847) B2757847
theorem B1965071 : Blo 1634016 1965071 := bstep (se 1 (by rfl) ⟨1473803, by rfl⟩ : syracuseStep 1965071 = 2947607) B2947607
theorem B5381207 : Blo 1634016 5381207 := bstep (se 1 (by rfl) ⟨4035905, by rfl⟩ : syracuseStep 5381207 = 8071811) B8071811
theorem B8273015 : Blo 1634016 8273015 := bstep (se 1 (by rfl) ⟨6204761, by rfl⟩ : syracuseStep 8273015 = 12409523) B12409523
theorem B9944183 : Blo 1634016 9944183 := bstep (se 1 (by rfl) ⟨7458137, by rfl⟩ : syracuseStep 9944183 = 14916275) B14916275
theorem B14155067 : Blo 1634016 14155067 := bstep (se 1 (by rfl) ⟨10616300, by rfl⟩ : syracuseStep 14155067 = 21232601) B21232601
theorem B4193683 : Blo 1634016 4193683 := bstep (se 1 (by rfl) ⟨3145262, by rfl⟩ : syracuseStep 4193683 = 6290525) B6290525
theorem B7462297 : Blo 1634016 7462297 := bstep (se 2 (by rfl) ⟨2798361, by rfl⟩ : syracuseStep 7462297 = 5596723) B5596723
theorem B8838667 : Blo 1634016 8838667 := bstep (se 1 (by rfl) ⟨6629000, by rfl⟩ : syracuseStep 8838667 = 13258001) B13258001
theorem B2096699 : Blo 1634016 2096699 := bstep (se 1 (by rfl) ⟨1572524, by rfl⟩ : syracuseStep 2096699 = 3145049) B3145049
theorem B13262413 : Blo 1634016 13262413 := bstep (se 3 (by rfl) ⟨2486702, by rfl⟩ : syracuseStep 13262413 = 4973405) B4973405
theorem B2760311 : Blo 1634016 2760311 := bstep (se 1 (by rfl) ⟨2070233, by rfl⟩ : syracuseStep 2760311 = 4140467) B4140467
theorem B3677831 : Blo 1634016 3677831 := bstep (se 1 (by rfl) ⟨2758373, by rfl⟩ : syracuseStep 3677831 = 5516747) B5516747
theorem B25157297 : Blo 1634016 25157297 := bstep (se 2 (by rfl) ⟨9433986, by rfl⟩ : syracuseStep 25157297 = 18867973) B18867973
theorem B5889793 : Blo 1634016 5889793 := bstep (se 2 (by rfl) ⟨2208672, by rfl⟩ : syracuseStep 5889793 = 4417345) B4417345
theorem B3678011 : Blo 1634016 3678011 := bstep (se 1 (by rfl) ⟨2758508, by rfl⟩ : syracuseStep 3678011 = 5517017) B5517017
theorem B4136791 : Blo 1634016 4136791 := bstep (se 1 (by rfl) ⟨3102593, by rfl⟩ : syracuseStep 4136791 = 6205187) B6205187
theorem B3104659 : Blo 1634016 3104659 := bstep (se 1 (by rfl) ⟨2328494, by rfl⟩ : syracuseStep 3104659 = 4656989) B4656989
theorem B3678137 : Blo 1634016 3678137 := bstep (se 2 (by rfl) ⟨1379301, by rfl⟩ : syracuseStep 3678137 = 2758603) B2758603
theorem B5521337 : Blo 1634016 5521337 := bstep (se 2 (by rfl) ⟨2070501, by rfl⟩ : syracuseStep 5521337 = 4141003) B4141003
theorem B30638027 : Blo 1634016 30638027 := bstep (se 1 (by rfl) ⟨22978520, by rfl⟩ : syracuseStep 30638027 = 45957041) B45957041
theorem B3678227 : Blo 1634016 3678227 := bstep (se 1 (by rfl) ⟨2758670, by rfl⟩ : syracuseStep 3678227 = 5517341) B5517341
theorem B11788325 : Blo 1634016 11788325 := bstep (se 4 (by rfl) ⟨1105155, by rfl⟩ : syracuseStep 11788325 = 2210311) B2210311
theorem B2760743 : Blo 1634016 2760743 := bstep (se 1 (by rfl) ⟨2070557, by rfl⟩ : syracuseStep 2760743 = 4141115) B4141115
theorem B13959485 : Blo 1634016 13959485 := bstep (se 3 (by rfl) ⟨2617403, by rfl⟩ : syracuseStep 13959485 = 5234807) B5234807
theorem B3678569 : Blo 1634016 3678569 := bstep (se 2 (by rfl) ⟨1379463, by rfl⟩ : syracuseStep 3678569 = 2758927) B2758927
theorem B9945449 : Blo 1634016 9945449 := bstep (se 2 (by rfl) ⟨3729543, by rfl⟩ : syracuseStep 9945449 = 7459087) B7459087
theorem B9314797 : Blo 1634016 9314797 := bstep (se 3 (by rfl) ⟨1746524, by rfl⟩ : syracuseStep 9314797 = 3493049) B3493049
theorem B3146249 : Blo 1634016 3146249 := bstep (se 2 (by rfl) ⟨1179843, by rfl⟩ : syracuseStep 3146249 = 2359687) B2359687
theorem B5890745 : Blo 1634016 5890745 := bstep (se 2 (by rfl) ⟨2209029, by rfl⟩ : syracuseStep 5890745 = 4418059) B4418059
theorem B3105479 : Blo 1634016 3105479 := bstep (se 1 (by rfl) ⟨2329109, by rfl⟩ : syracuseStep 3105479 = 4658219) B4658219
theorem B56640217 : Blo 1634016 56640217 := bstep (se 2 (by rfl) ⟨21240081, by rfl⟩ : syracuseStep 56640217 = 42480163) B42480163
theorem B3105631 : Blo 1634016 3105631 := bstep (se 1 (by rfl) ⟨2329223, by rfl⟩ : syracuseStep 3105631 = 4658447) B4658447
theorem B2327401 : Blo 1634016 2327401 := bstep (se 2 (by rfl) ⟨872775, by rfl⟩ : syracuseStep 2327401 = 1745551) B1745551
theorem B3679163 : Blo 1634016 3679163 := bstep (se 1 (by rfl) ⟨2759372, by rfl⟩ : syracuseStep 3679163 = 5518745) B5518745
theorem B11781085 : Blo 1634016 11781085 := bstep (se 3 (by rfl) ⟨2208953, by rfl⟩ : syracuseStep 11781085 = 4417907) B4417907
theorem B20939795 : Blo 1634016 20939795 := bstep (se 1 (by rfl) ⟨15704846, by rfl⟩ : syracuseStep 20939795 = 31409693) B31409693
theorem B12411953 : Blo 1634016 12411953 := bstep (se 2 (by rfl) ⟨4654482, by rfl⟩ : syracuseStep 12411953 = 9308965) B9308965
theorem B5235769 : Blo 1634016 5235769 := bstep (se 2 (by rfl) ⟨1963413, by rfl⟩ : syracuseStep 5235769 = 3926827) B3926827
theorem B3679289 : Blo 1634016 3679289 := bstep (se 2 (by rfl) ⟨1379733, by rfl⟩ : syracuseStep 3679289 = 2759467) B2759467
theorem B12420215 : Blo 1634016 12420215 := bstep (se 1 (by rfl) ⟨9315161, by rfl⟩ : syracuseStep 12420215 = 18630323) B18630323
theorem B8840573 : Blo 1634016 8840573 := bstep (se 3 (by rfl) ⟨1657607, by rfl⟩ : syracuseStep 8840573 = 3315215) B3315215
theorem B3679631 : Blo 1634016 3679631 := bstep (se 1 (by rfl) ⟨2759723, by rfl⟩ : syracuseStep 3679631 = 5519447) B5519447
theorem B4417163 : Blo 1634016 4417163 := bstep (se 1 (by rfl) ⟨3312872, by rfl⟩ : syracuseStep 4417163 = 6625745) B6625745
theorem B2451143 : Blo 1634016 2451143 := bstep (se 1 (by rfl) ⟨1838357, by rfl⟩ : syracuseStep 2451143 = 3676715) B3676715
theorem B3679955 : Blo 1634016 3679955 := bstep (se 1 (by rfl) ⟨2759966, by rfl⟩ : syracuseStep 3679955 = 5519933) B5519933
theorem B11339513 : Blo 1634016 11339513 := bstep (se 2 (by rfl) ⟨4252317, by rfl⟩ : syracuseStep 11339513 = 8504635) B8504635
theorem B5891869 : Blo 1634016 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B18876203 : Blo 1634016 18876203 := bstep (se 1 (by rfl) ⟨14157152, by rfl⟩ : syracuseStep 18876203 = 28314305) B28314305
theorem B11192131 : Blo 1634016 11192131 := bstep (se 1 (by rfl) ⟨8394098, by rfl⟩ : syracuseStep 11192131 = 16788197) B16788197
theorem B7456607 : Blo 1634016 7456607 := bstep (se 1 (by rfl) ⟨5592455, by rfl⟩ : syracuseStep 7456607 = 11184911) B11184911
theorem B4138847 : Blo 1634016 4138847 := bstep (se 1 (by rfl) ⟨3104135, by rfl⟩ : syracuseStep 4138847 = 6208271) B6208271
theorem B2451305 : Blo 1634016 2451305 := bstep (se 2 (by rfl) ⟨919239, by rfl⟩ : syracuseStep 2451305 = 1838479) B1838479
theorem B5515127 : Blo 1634016 5515127 := bstep (se 1 (by rfl) ⟨4136345, by rfl⟩ : syracuseStep 5515127 = 8272691) B8272691
theorem B11782007 : Blo 1634016 11782007 := bstep (se 1 (by rfl) ⟨8836505, by rfl⟩ : syracuseStep 11782007 = 17673011) B17673011
theorem B2451383 : Blo 1634016 2451383 := bstep (se 1 (by rfl) ⟨1838537, by rfl⟩ : syracuseStep 2451383 = 3677075) B3677075
theorem B33580993 : Blo 1634016 33580993 := bstep (se 2 (by rfl) ⟨12592872, by rfl⟩ : syracuseStep 33580993 = 25185745) B25185745
theorem B2451419 : Blo 1634016 2451419 := bstep (se 1 (by rfl) ⟨1838564, by rfl⟩ : syracuseStep 2451419 = 3677129) B3677129
theorem B5515343 : Blo 1634016 5515343 := bstep (se 1 (by rfl) ⟨4136507, by rfl⟩ : syracuseStep 5515343 = 8273015) B8273015
theorem B6629455 : Blo 1634016 6629455 := bstep (se 1 (by rfl) ⟨4972091, by rfl⟩ : syracuseStep 6629455 = 9944183) B9944183
theorem B75499613 : Blo 1634016 75499613 := bstep (se 3 (by rfl) ⟨14156177, by rfl⟩ : syracuseStep 75499613 = 28312355) B28312355
theorem B22366309 : Blo 1634016 22366309 := bstep (se 4 (by rfl) ⟨2096841, by rfl⟩ : syracuseStep 22366309 = 4193683) B4193683
theorem B4655485 : Blo 1634016 4655485 := bstep (se 3 (by rfl) ⟨872903, by rfl⟩ : syracuseStep 4655485 = 1745807) B1745807
theorem B2451887 : Blo 1634016 2451887 := bstep (se 1 (by rfl) ⟨1838915, by rfl⟩ : syracuseStep 2451887 = 3677831) B3677831
theorem B5515721 : Blo 1634016 5515721 := bstep (se 2 (by rfl) ⟨2068395, by rfl⟩ : syracuseStep 5515721 = 4136791) B4136791
theorem B16771531 : Blo 1634016 16771531 := bstep (se 1 (by rfl) ⟨12578648, by rfl⟩ : syracuseStep 16771531 = 25157297) B25157297
theorem B2451977 : Blo 1634016 2451977 := bstep (se 2 (by rfl) ⟨919491, by rfl⟩ : syracuseStep 2451977 = 1838983) B1838983
theorem B4139545 : Blo 1634016 4139545 := bstep (se 2 (by rfl) ⟨1552329, by rfl⟩ : syracuseStep 4139545 = 3104659) B3104659
theorem B81701405 : Blo 1634016 81701405 := bstep (se 3 (by rfl) ⟨15319013, by rfl⟩ : syracuseStep 81701405 = 30638027) B30638027
theorem B2452007 : Blo 1634016 2452007 := bstep (se 1 (by rfl) ⟨1839005, by rfl⟩ : syracuseStep 2452007 = 3678011) B3678011
theorem B15927853 : Blo 1634016 15927853 := bstep (se 3 (by rfl) ⟨2986472, by rfl⟩ : syracuseStep 15927853 = 5972945) B5972945
theorem B4655713 : Blo 1634016 4655713 := bstep (se 2 (by rfl) ⟨1745892, by rfl⟩ : syracuseStep 4655713 = 3491785) B3491785
theorem B2452091 : Blo 1634016 2452091 := bstep (se 1 (by rfl) ⟨1839068, by rfl⟩ : syracuseStep 2452091 = 3678137) B3678137
theorem B3680891 : Blo 1634016 3680891 := bstep (se 1 (by rfl) ⟨2760668, by rfl⟩ : syracuseStep 3680891 = 5521337) B5521337
theorem B7457465 : Blo 1634016 7457465 := bstep (se 2 (by rfl) ⟨2796549, by rfl⟩ : syracuseStep 7457465 = 5593099) B5593099
theorem B5515991 : Blo 1634016 5515991 := bstep (se 1 (by rfl) ⟨4136993, by rfl⟩ : syracuseStep 5515991 = 8273987) B8273987
theorem B4418297 : Blo 1634016 4418297 := bstep (se 2 (by rfl) ⟨1656861, by rfl⟩ : syracuseStep 4418297 = 3313723) B3313723
theorem B2452217 : Blo 1634016 2452217 := bstep (se 2 (by rfl) ⟨919581, by rfl⟩ : syracuseStep 2452217 = 1839163) B1839163
theorem B3681017 : Blo 1634016 3681017 := bstep (se 2 (by rfl) ⟨1380381, by rfl⟩ : syracuseStep 3681017 = 2760763) B2760763
theorem B4139849 : Blo 1634016 4139849 := bstep (se 2 (by rfl) ⟨1552443, by rfl⟩ : syracuseStep 4139849 = 3104887) B3104887
theorem B2452319 : Blo 1634016 2452319 := bstep (se 1 (by rfl) ⟨1839239, by rfl⟩ : syracuseStep 2452319 = 3678479) B3678479
theorem B2452331 : Blo 1634016 2452331 := bstep (se 1 (by rfl) ⟨1839248, by rfl⟩ : syracuseStep 2452331 = 3678497) B3678497
theorem B5516207 : Blo 1634016 5516207 := bstep (se 1 (by rfl) ⟨4137155, by rfl⟩ : syracuseStep 5516207 = 8274311) B8274311
theorem B4656055 : Blo 1634016 4656055 := bstep (se 1 (by rfl) ⟨3492041, by rfl⟩ : syracuseStep 4656055 = 6984083) B6984083
theorem B2452559 : Blo 1634016 2452559 := bstep (se 1 (by rfl) ⟨1839419, by rfl⟩ : syracuseStep 2452559 = 3678839) B3678839
theorem B3730511 : Blo 1634016 3730511 := bstep (se 1 (by rfl) ⟨2797883, by rfl⟩ : syracuseStep 3730511 = 5595767) B5595767
theorem B6630557 : Blo 1634016 6630557 := bstep (se 3 (by rfl) ⟨1243229, by rfl⟩ : syracuseStep 6630557 = 2486459) B2486459
theorem B2452679 : Blo 1634016 2452679 := bstep (se 1 (by rfl) ⟨1839509, by rfl⟩ : syracuseStep 2452679 = 3679019) B3679019
theorem B2452841 : Blo 1634016 2452841 := bstep (se 2 (by rfl) ⟨919815, by rfl⟩ : syracuseStep 2452841 = 1839631) B1839631
theorem B2452919 : Blo 1634016 2452919 := bstep (se 1 (by rfl) ⟨1839689, by rfl⟩ : syracuseStep 2452919 = 3679379) B3679379
theorem B5311945 : Blo 1634016 5311945 := bstep (se 2 (by rfl) ⟨1991979, by rfl⟩ : syracuseStep 5311945 = 3983959) B3983959
theorem B2452955 : Blo 1634016 2452955 := bstep (se 1 (by rfl) ⟨1839716, by rfl⟩ : syracuseStep 2452955 = 3679433) B3679433
theorem B12586535 : Blo 1634016 12586535 := bstep (se 1 (by rfl) ⟨9439901, by rfl⟩ : syracuseStep 12586535 = 18879803) B18879803
theorem B50998859 : Blo 1634016 50998859 := bstep (se 1 (by rfl) ⟨38249144, by rfl⟩ : syracuseStep 50998859 = 76498289) B76498289
theorem B16371389 : Blo 1634016 16371389 := bstep (se 3 (by rfl) ⟨3069635, by rfl⟩ : syracuseStep 16371389 = 6139271) B6139271
theorem B1634087 : Blo 1634016 1634087 := bstep (se 1 (by rfl) ⟨1225565, by rfl⟩ : syracuseStep 1634087 = 2451131) B2451131
theorem B5893931 : Blo 1634016 5893931 := bstep (se 1 (by rfl) ⟨4420448, by rfl⟩ : syracuseStep 5893931 = 8840897) B8840897
theorem B1634127 : Blo 1634016 1634127 := bstep (se 1 (by rfl) ⟨1225595, by rfl⟩ : syracuseStep 1634127 = 2451191) B2451191
theorem B1634143 : Blo 1634016 1634143 := bstep (se 1 (by rfl) ⟨1225607, by rfl⟩ : syracuseStep 1634143 = 2451215) B2451215
theorem B1634171 : Blo 1634016 1634171 := bstep (se 1 (by rfl) ⟨1225628, by rfl⟩ : syracuseStep 1634171 = 2451257) B2451257
theorem B3493793 : Blo 1634016 3493793 := bstep (se 2 (by rfl) ⟨1310172, by rfl⟩ : syracuseStep 3493793 = 2620345) B2620345
theorem B23564195 : Blo 1634016 23564195 := bstep (se 1 (by rfl) ⟨17673146, by rfl⟩ : syracuseStep 23564195 = 35346293) B35346293
theorem B1634223 : Blo 1634016 1634223 := bstep (se 1 (by rfl) ⟨1225667, by rfl⟩ : syracuseStep 1634223 = 2451335) B2451335
theorem B2797487 : Blo 1634016 2797487 := bstep (se 1 (by rfl) ⟨2098115, by rfl⟩ : syracuseStep 2797487 = 4196231) B4196231
theorem B2453423 : Blo 1634016 2453423 := bstep (se 1 (by rfl) ⟨1840067, by rfl⟩ : syracuseStep 2453423 = 3680135) B3680135
theorem B4140983 : Blo 1634016 4140983 := bstep (se 1 (by rfl) ⟨3105737, by rfl⟩ : syracuseStep 4140983 = 6211475) B6211475
theorem B1634247 : Blo 1634016 1634247 := bstep (se 1 (by rfl) ⟨1225685, by rfl⟩ : syracuseStep 1634247 = 2451371) B2451371
theorem B1634267 : Blo 1634016 1634267 := bstep (se 1 (by rfl) ⟨1225700, by rfl⟩ : syracuseStep 1634267 = 2451401) B2451401
theorem B2453513 : Blo 1634016 2453513 := bstep (se 2 (by rfl) ⟨920067, by rfl⟩ : syracuseStep 2453513 = 1840135) B1840135
theorem B4657171 : Blo 1634016 4657171 := bstep (se 1 (by rfl) ⟨3492878, by rfl⟩ : syracuseStep 4657171 = 6985757) B6985757
theorem B1634343 : Blo 1634016 1634343 := bstep (se 1 (by rfl) ⟨1225757, by rfl⟩ : syracuseStep 1634343 = 2451515) B2451515
theorem B2453543 : Blo 1634016 2453543 := bstep (se 1 (by rfl) ⟨1840157, by rfl⟩ : syracuseStep 2453543 = 3680315) B3680315
theorem B1634383 : Blo 1634016 1634383 := bstep (se 1 (by rfl) ⟨1225787, by rfl⟩ : syracuseStep 1634383 = 2451575) B2451575
theorem B1634399 : Blo 1634016 1634399 := bstep (se 1 (by rfl) ⟨1225799, by rfl⟩ : syracuseStep 1634399 = 2451599) B2451599
theorem B1634427 : Blo 1634016 1634427 := bstep (se 1 (by rfl) ⟨1225820, by rfl⟩ : syracuseStep 1634427 = 2451641) B2451641
theorem B2453627 : Blo 1634016 2453627 := bstep (se 1 (by rfl) ⟨1840220, by rfl⟩ : syracuseStep 2453627 = 3680441) B3680441
theorem B5591197 : Blo 1634016 5591197 := bstep (se 3 (by rfl) ⟨1048349, by rfl⟩ : syracuseStep 5591197 = 2096699) B2096699
theorem B1634479 : Blo 1634016 1634479 := bstep (se 1 (by rfl) ⟨1225859, by rfl⟩ : syracuseStep 1634479 = 2451719) B2451719
theorem B1634503 : Blo 1634016 1634503 := bstep (se 1 (by rfl) ⟨1225877, by rfl⟩ : syracuseStep 1634503 = 2451755) B2451755
theorem B2068679 : Blo 1634016 2068679 := bstep (se 1 (by rfl) ⟨1551509, by rfl⟩ : syracuseStep 2068679 = 3103019) B3103019
theorem B1634523 : Blo 1634016 1634523 := bstep (se 1 (by rfl) ⟨1225892, by rfl⟩ : syracuseStep 1634523 = 2451785) B2451785
theorem B2453753 : Blo 1634016 2453753 := bstep (se 2 (by rfl) ⟨920157, by rfl⟩ : syracuseStep 2453753 = 1840315) B1840315
theorem B1634599 : Blo 1634016 1634599 := bstep (se 1 (by rfl) ⟨1225949, by rfl⟩ : syracuseStep 1634599 = 2451899) B2451899
theorem B1634639 : Blo 1634016 1634639 := bstep (se 1 (by rfl) ⟨1225979, by rfl⟩ : syracuseStep 1634639 = 2451959) B2451959
theorem B2068831 : Blo 1634016 2068831 := bstep (se 1 (by rfl) ⟨1551623, by rfl⟩ : syracuseStep 2068831 = 3103247) B3103247
theorem B1634655 : Blo 1634016 1634655 := bstep (se 1 (by rfl) ⟨1225991, by rfl⟩ : syracuseStep 1634655 = 2451983) B2451983
theorem B2453855 : Blo 1634016 2453855 := bstep (se 1 (by rfl) ⟨1840391, by rfl⟩ : syracuseStep 2453855 = 3680783) B3680783
theorem B4657513 : Blo 1634016 4657513 := bstep (se 2 (by rfl) ⟨1746567, by rfl⟩ : syracuseStep 4657513 = 3493135) B3493135
theorem B2453867 : Blo 1634016 2453867 := bstep (se 1 (by rfl) ⟨1840400, by rfl⟩ : syracuseStep 2453867 = 3680801) B3680801
theorem B1634683 : Blo 1634016 1634683 := bstep (se 1 (by rfl) ⟨1226012, by rfl⟩ : syracuseStep 1634683 = 2452025) B2452025
theorem B56635777 : Blo 1634016 56635777 := bstep (se 2 (by rfl) ⟨21238416, by rfl⟩ : syracuseStep 56635777 = 42476833) B42476833
theorem B1634735 : Blo 1634016 1634735 := bstep (se 1 (by rfl) ⟨1226051, by rfl⟩ : syracuseStep 1634735 = 2452103) B2452103
theorem B1634759 : Blo 1634016 1634759 := bstep (se 1 (by rfl) ⟨1226069, by rfl⟩ : syracuseStep 1634759 = 2452139) B2452139
theorem B1634779 : Blo 1634016 1634779 := bstep (se 1 (by rfl) ⟨1226084, by rfl⟩ : syracuseStep 1634779 = 2452169) B2452169
theorem B18633239 : Blo 1634016 18633239 := bstep (se 1 (by rfl) ⟨13974929, by rfl⟩ : syracuseStep 18633239 = 27949859) B27949859
theorem B9949729 : Blo 1634016 9949729 := bstep (se 2 (by rfl) ⟨3731148, by rfl⟩ : syracuseStep 9949729 = 7462297) B7462297
theorem B1634855 : Blo 1634016 1634855 := bstep (se 1 (by rfl) ⟨1226141, by rfl⟩ : syracuseStep 1634855 = 2452283) B2452283
theorem B1634895 : Blo 1634016 1634895 := bstep (se 1 (by rfl) ⟨1226171, by rfl⟩ : syracuseStep 1634895 = 2452343) B2452343
theorem B1634911 : Blo 1634016 1634911 := bstep (se 1 (by rfl) ⟨1226183, by rfl⟩ : syracuseStep 1634911 = 2452367) B2452367
theorem B1634939 : Blo 1634016 1634939 := bstep (se 1 (by rfl) ⟨1226204, by rfl⟩ : syracuseStep 1634939 = 2452409) B2452409
theorem B1839739 : Blo 1634016 1839739 := bstep (se 1 (by rfl) ⟨1379804, by rfl⟩ : syracuseStep 1839739 = 2759609) B2759609
theorem B4657787 : Blo 1634016 4657787 := bstep (se 1 (by rfl) ⟨3493340, by rfl⟩ : syracuseStep 4657787 = 6986681) B6986681
theorem B1634991 : Blo 1634016 1634991 := bstep (se 1 (by rfl) ⟨1226243, by rfl⟩ : syracuseStep 1634991 = 2452487) B2452487
theorem B11784889 : Blo 1634016 11784889 := bstep (se 2 (by rfl) ⟨4419333, by rfl⟩ : syracuseStep 11784889 = 8838667) B8838667
theorem B1635015 : Blo 1634016 1635015 := bstep (se 1 (by rfl) ⟨1226261, by rfl⟩ : syracuseStep 1635015 = 2452523) B2452523
theorem B1635035 : Blo 1634016 1635035 := bstep (se 1 (by rfl) ⟨1226276, by rfl⟩ : syracuseStep 1635035 = 2452553) B2452553
theorem B17683217 : Blo 1634016 17683217 := bstep (se 2 (by rfl) ⟨6631206, by rfl⟩ : syracuseStep 17683217 = 13262413) B13262413
theorem B1635111 : Blo 1634016 1635111 := bstep (se 1 (by rfl) ⟨1226333, by rfl⟩ : syracuseStep 1635111 = 2452667) B2452667
theorem B2757449 : Blo 1634016 2757449 := bstep (se 2 (by rfl) ⟨1034043, by rfl⟩ : syracuseStep 2757449 = 2068087) B2068087
theorem B1635151 : Blo 1634016 1635151 := bstep (se 1 (by rfl) ⟨1226363, by rfl⟩ : syracuseStep 1635151 = 2452727) B2452727
theorem B1635167 : Blo 1634016 1635167 := bstep (se 1 (by rfl) ⟨1226375, by rfl⟩ : syracuseStep 1635167 = 2452751) B2452751
theorem B6206327 : Blo 1634016 6206327 := bstep (se 1 (by rfl) ⟨4654745, by rfl⟩ : syracuseStep 6206327 = 9309491) B9309491
theorem B1635195 : Blo 1634016 1635195 := bstep (se 1 (by rfl) ⟨1226396, by rfl⟩ : syracuseStep 1635195 = 2452793) B2452793
theorem B1635247 : Blo 1634016 1635247 := bstep (se 1 (by rfl) ⟨1226435, by rfl⟩ : syracuseStep 1635247 = 2452871) B2452871
theorem B1635271 : Blo 1634016 1635271 := bstep (se 1 (by rfl) ⟨1226453, by rfl⟩ : syracuseStep 1635271 = 2452907) B2452907
theorem B1635291 : Blo 1634016 1635291 := bstep (se 1 (by rfl) ⟨1226468, by rfl⟩ : syracuseStep 1635291 = 2452937) B2452937
theorem B7853057 : Blo 1634016 7853057 := bstep (se 2 (by rfl) ⟨2944896, by rfl⟩ : syracuseStep 7853057 = 5889793) B5889793
theorem B1635367 : Blo 1634016 1635367 := bstep (se 1 (by rfl) ⟨1226525, by rfl⟩ : syracuseStep 1635367 = 2453051) B2453051
theorem B1635407 : Blo 1634016 1635407 := bstep (se 1 (by rfl) ⟨1226555, by rfl⟩ : syracuseStep 1635407 = 2453111) B2453111
theorem B1840207 : Blo 1634016 1840207 := bstep (se 1 (by rfl) ⟨1380155, by rfl⟩ : syracuseStep 1840207 = 2760311) B2760311
theorem B1635423 : Blo 1634016 1635423 := bstep (se 1 (by rfl) ⟨1226567, by rfl⟩ : syracuseStep 1635423 = 2453135) B2453135
theorem B1635451 : Blo 1634016 1635451 := bstep (se 1 (by rfl) ⟨1226588, by rfl⟩ : syracuseStep 1635451 = 2453177) B2453177
theorem B1635503 : Blo 1634016 1635503 := bstep (se 1 (by rfl) ⟨1226627, by rfl⟩ : syracuseStep 1635503 = 2453255) B2453255
theorem B1963207 : Blo 1634016 1963207 := bstep (se 1 (by rfl) ⟨1472405, by rfl⟩ : syracuseStep 1963207 = 2944811) B2944811
theorem B1635527 : Blo 1634016 1635527 := bstep (se 1 (by rfl) ⟨1226645, by rfl⟩ : syracuseStep 1635527 = 2453291) B2453291
theorem B1635547 : Blo 1634016 1635547 := bstep (se 1 (by rfl) ⟨1226660, by rfl⟩ : syracuseStep 1635547 = 2453321) B2453321
theorem B5518583 : Blo 1634016 5518583 := bstep (se 1 (by rfl) ⟨4138937, by rfl⟩ : syracuseStep 5518583 = 8277875) B8277875
theorem B2757881 : Blo 1634016 2757881 := bstep (se 2 (by rfl) ⟨1034205, by rfl⟩ : syracuseStep 2757881 = 2068411) B2068411
theorem B1635623 : Blo 1634016 1635623 := bstep (se 1 (by rfl) ⟨1226717, by rfl⟩ : syracuseStep 1635623 = 2453435) B2453435
theorem B1635663 : Blo 1634016 1635663 := bstep (se 1 (by rfl) ⟨1226747, by rfl⟩ : syracuseStep 1635663 = 2453495) B2453495
theorem B1635679 : Blo 1634016 1635679 := bstep (se 1 (by rfl) ⟨1226759, by rfl⟩ : syracuseStep 1635679 = 2453519) B2453519
theorem B1635707 : Blo 1634016 1635707 := bstep (se 1 (by rfl) ⟨1226780, by rfl⟩ : syracuseStep 1635707 = 2453561) B2453561
theorem B5240189 : Blo 1634016 5240189 := bstep (se 3 (by rfl) ⟨982535, by rfl⟩ : syracuseStep 5240189 = 1965071) B1965071
theorem B2758063 : Blo 1634016 2758063 := bstep (se 1 (by rfl) ⟨2068547, by rfl⟩ : syracuseStep 2758063 = 4137095) B4137095
theorem B1635759 : Blo 1634016 1635759 := bstep (se 1 (by rfl) ⟨1226819, by rfl⟩ : syracuseStep 1635759 = 2453639) B2453639
theorem B1635783 : Blo 1634016 1635783 := bstep (se 1 (by rfl) ⟨1226837, by rfl⟩ : syracuseStep 1635783 = 2453675) B2453675
theorem B1635803 : Blo 1634016 1635803 := bstep (se 1 (by rfl) ⟨1226852, by rfl⟩ : syracuseStep 1635803 = 2453705) B2453705
theorem B2758151 : Blo 1634016 2758151 := bstep (se 1 (by rfl) ⟨2068613, by rfl⟩ : syracuseStep 2758151 = 4137227) B4137227
theorem B1635879 : Blo 1634016 1635879 := bstep (se 1 (by rfl) ⟨1226909, by rfl⟩ : syracuseStep 1635879 = 2453819) B2453819
theorem B5518907 : Blo 1634016 5518907 := bstep (se 1 (by rfl) ⟨4139180, by rfl⟩ : syracuseStep 5518907 = 8278361) B8278361
theorem B1635919 : Blo 1634016 1635919 := bstep (se 1 (by rfl) ⟨1226939, by rfl⟩ : syracuseStep 1635919 = 2453879) B2453879
theorem B1635935 : Blo 1634016 1635935 := bstep (se 1 (by rfl) ⟨1226951, by rfl⟩ : syracuseStep 1635935 = 2453903) B2453903
theorem B1635963 : Blo 1634016 1635963 := bstep (se 1 (by rfl) ⟨1226972, by rfl⟩ : syracuseStep 1635963 = 2453945) B2453945
theorem B1636015 : Blo 1634016 1636015 := bstep (se 1 (by rfl) ⟨1227011, by rfl⟩ : syracuseStep 1636015 = 2454023) B2454023
theorem B6985415 : Blo 1634016 6985415 := bstep (se 1 (by rfl) ⟨5239061, by rfl⟩ : syracuseStep 6985415 = 10478123) B10478123
theorem B3102457 : Blo 1634016 3102457 := bstep (se 2 (by rfl) ⟨1163421, by rfl⟩ : syracuseStep 3102457 = 2326843) B2326843
theorem B7853867 : Blo 1634016 7853867 := bstep (se 1 (by rfl) ⟨5890400, by rfl⟩ : syracuseStep 7853867 = 11780801) B11780801
theorem B6207299 : Blo 1634016 6207299 := bstep (se 1 (by rfl) ⟨4655474, by rfl⟩ : syracuseStep 6207299 = 9310949) B9310949
theorem B7460675 : Blo 1634016 7460675 := bstep (se 1 (by rfl) ⟨5595506, by rfl⟩ : syracuseStep 7460675 = 11191013) B11191013
theorem B5519177 : Blo 1634016 5519177 := bstep (se 2 (by rfl) ⟨2069691, by rfl⟩ : syracuseStep 5519177 = 4139383) B4139383
theorem B2758495 : Blo 1634016 2758495 := bstep (se 1 (by rfl) ⟨2068871, by rfl⟩ : syracuseStep 2758495 = 4137743) B4137743
theorem B3929951 : Blo 1634016 3929951 := bstep (se 1 (by rfl) ⟨2947463, by rfl⟩ : syracuseStep 3929951 = 5894927) B5894927
theorem B2758583 : Blo 1634016 2758583 := bstep (se 1 (by rfl) ⟨2068937, by rfl⟩ : syracuseStep 2758583 = 4137875) B4137875
theorem B3102799 : Blo 1634016 3102799 := bstep (se 1 (by rfl) ⟨2327099, by rfl⟩ : syracuseStep 3102799 = 4654199) B4654199
theorem B3103049 : Blo 1634016 3103049 := bstep (se 2 (by rfl) ⟨1163643, by rfl⟩ : syracuseStep 3103049 = 2327287) B2327287
theorem B2759177 : Blo 1634016 2759177 := bstep (se 2 (by rfl) ⟨1034691, by rfl⟩ : syracuseStep 2759177 = 2069383) B2069383
theorem B3676769 : Blo 1634016 3676769 := bstep (se 2 (by rfl) ⟨1378788, by rfl⟩ : syracuseStep 3676769 = 2757577) B2757577
theorem B6380129 : Blo 1634016 6380129 := bstep (se 2 (by rfl) ⟨2392548, by rfl⟩ : syracuseStep 6380129 = 4785097) B4785097
theorem B2759339 : Blo 1634016 2759339 := bstep (se 1 (by rfl) ⟨2069504, by rfl⟩ : syracuseStep 2759339 = 4139009) B4139009
theorem B6208285 : Blo 1634016 6208285 := bstep (se 3 (by rfl) ⟨1164053, by rfl⟩ : syracuseStep 6208285 = 2328107) B2328107
theorem B23903045 : Blo 1634016 23903045 := bstep (se 4 (by rfl) ⟨2240910, by rfl⟩ : syracuseStep 23903045 = 4481821) B4481821
theorem B2653103 : Blo 1634016 2653103 := bstep (se 1 (by rfl) ⟨1989827, by rfl⟩ : syracuseStep 2653103 = 3979655) B3979655
theorem B3677111 : Blo 1634016 3677111 := bstep (se 1 (by rfl) ⟨2757833, by rfl⟩ : syracuseStep 3677111 = 5515667) B5515667
theorem B5520311 : Blo 1634016 5520311 := bstep (se 1 (by rfl) ⟨4140233, by rfl⟩ : syracuseStep 5520311 = 8280467) B8280467
theorem B2759737 : Blo 1634016 2759737 := bstep (se 2 (by rfl) ⟨1034901, by rfl⟩ : syracuseStep 2759737 = 2069803) B2069803
theorem B12410009 : Blo 1634016 12410009 := bstep (se 2 (by rfl) ⟨4653753, by rfl⟩ : syracuseStep 12410009 = 9307507) B9307507
theorem B3103915 : Blo 1634016 3103915 := bstep (se 1 (by rfl) ⟨2327936, by rfl⟩ : syracuseStep 3103915 = 4655873) B4655873
theorem B2759879 : Blo 1634016 2759879 := bstep (se 1 (by rfl) ⟨2069909, by rfl⟩ : syracuseStep 2759879 = 4139819) B4139819
theorem B3103991 : Blo 1634016 3103991 := bstep (se 1 (by rfl) ⟨2327993, by rfl⟩ : syracuseStep 3103991 = 4655987) B4655987
theorem B23567705 : Blo 1634016 23567705 := bstep (se 2 (by rfl) ⟨8837889, by rfl⟩ : syracuseStep 23567705 = 17675779) B17675779
theorem B2760041 : Blo 1634016 2760041 := bstep (se 2 (by rfl) ⟨1035015, by rfl⟩ : syracuseStep 2760041 = 2070031) B2070031
theorem B3587471 : Blo 1634016 3587471 := bstep (se 1 (by rfl) ⟨2690603, by rfl⟩ : syracuseStep 3587471 = 5381207) B5381207
theorem B57425369 : Blo 1634016 57425369 := bstep (se 2 (by rfl) ⟨21534513, by rfl⟩ : syracuseStep 57425369 = 43069027) B43069027
theorem B3104219 : Blo 1634016 3104219 := bstep (se 1 (by rfl) ⟨2328164, by rfl⟩ : syracuseStep 3104219 = 4656329) B4656329
theorem B3677705 : Blo 1634016 3677705 := bstep (se 2 (by rfl) ⟨1379139, by rfl⟩ : syracuseStep 3677705 = 2758279) B2758279
theorem B5520905 : Blo 1634016 5520905 := bstep (se 2 (by rfl) ⟨2070339, by rfl⟩ : syracuseStep 5520905 = 4140679) B4140679
theorem B9436711 : Blo 1634016 9436711 := bstep (se 1 (by rfl) ⟨7077533, by rfl⟩ : syracuseStep 9436711 = 14155067) B14155067
theorem B20700791 : Blo 1634016 20700791 := bstep (se 1 (by rfl) ⟨15525593, by rfl⟩ : syracuseStep 20700791 = 31051187) B31051187
theorem B2760439 : Blo 1634016 2760439 := bstep (se 1 (by rfl) ⟨2070329, by rfl⟩ : syracuseStep 2760439 = 4140659) B4140659
theorem B7855865 : Blo 1634016 7855865 := bstep (se 2 (by rfl) ⟨2945949, by rfl⟩ : syracuseStep 7855865 = 5891899) B5891899
theorem B3678047 : Blo 1634016 3678047 := bstep (se 1 (by rfl) ⟨2758535, by rfl⟩ : syracuseStep 3678047 = 5517071) B5517071
theorem B8273825 : Blo 1634016 8273825 := bstep (se 2 (by rfl) ⟨3102684, by rfl⟩ : syracuseStep 8273825 = 6205369) B6205369
theorem B19898297 : Blo 1634016 19898297 := bstep (se 2 (by rfl) ⟨7461861, by rfl⟩ : syracuseStep 19898297 = 14923723) B14923723
theorem B2760635 : Blo 1634016 2760635 := bstep (se 1 (by rfl) ⟨2070476, by rfl⟩ : syracuseStep 2760635 = 4140953) B4140953
theorem B6209561 : Blo 1634016 6209561 := bstep (se 2 (by rfl) ⟨2328585, by rfl⟩ : syracuseStep 6209561 = 4657171) B4657171
theorem B4137065 : Blo 1634016 4137065 := bstep (se 2 (by rfl) ⟨1551399, by rfl⟩ : syracuseStep 4137065 = 3102799) B3102799
theorem B7454929 : Blo 1634016 7454929 := bstep (se 2 (by rfl) ⟨2795598, by rfl⟩ : syracuseStep 7454929 = 5591197) B5591197
theorem B9306323 : Blo 1634016 9306323 := bstep (se 1 (by rfl) ⟨6979742, by rfl⟩ : syracuseStep 9306323 = 13959485) B13959485
theorem B2097499 : Blo 1634016 2097499 := bstep (se 1 (by rfl) ⟨1573124, by rfl⟩ : syracuseStep 2097499 = 3146249) B3146249
theorem B35357093 : Blo 1634016 35357093 := bstep (se 4 (by rfl) ⟨3314727, by rfl⟩ : syracuseStep 35357093 = 6629455) B6629455
theorem B3105191 : Blo 1634016 3105191 := bstep (se 1 (by rfl) ⟨2328893, by rfl⟩ : syracuseStep 3105191 = 4657787) B4657787
theorem B6210017 : Blo 1634016 6210017 := bstep (se 2 (by rfl) ⟨2328756, by rfl⟩ : syracuseStep 6210017 = 4657513) B4657513
theorem B75514369 : Blo 1634016 75514369 := bstep (se 2 (by rfl) ⟨28317888, by rfl⟩ : syracuseStep 75514369 = 56635777) B56635777
theorem B11788811 : Blo 1634016 11788811 := bstep (se 1 (by rfl) ⟨8841608, by rfl⟩ : syracuseStep 11788811 = 17683217) B17683217
theorem B4137551 : Blo 1634016 4137551 := bstep (se 1 (by rfl) ⟨3103163, by rfl⟩ : syracuseStep 4137551 = 6206327) B6206327
theorem B12419729 : Blo 1634016 12419729 := bstep (se 2 (by rfl) ⟨4657398, by rfl⟩ : syracuseStep 12419729 = 9314797) B9314797
theorem B5235371 : Blo 1634016 5235371 := bstep (se 1 (by rfl) ⟨3926528, by rfl⟩ : syracuseStep 5235371 = 7853057) B7853057
theorem B13959863 : Blo 1634016 13959863 := bstep (se 1 (by rfl) ⟨10469897, by rfl⟩ : syracuseStep 13959863 = 20939795) B20939795
theorem B8274635 : Blo 1634016 8274635 := bstep (se 1 (by rfl) ⟨6205976, by rfl⟩ : syracuseStep 8274635 = 12411953) B12411953
theorem B3679055 : Blo 1634016 3679055 := bstep (se 1 (by rfl) ⟨2759291, by rfl⟩ : syracuseStep 3679055 = 5518583) B5518583
theorem B8274797 : Blo 1634016 8274797 := bstep (se 3 (by rfl) ⟨1551524, by rfl⟩ : syracuseStep 8274797 = 3103049) B3103049
theorem B15713185 : Blo 1634016 15713185 := bstep (se 2 (by rfl) ⟨5892444, by rfl⟩ : syracuseStep 15713185 = 11784889) B11784889
theorem B3679271 : Blo 1634016 3679271 := bstep (se 1 (by rfl) ⟨2759453, by rfl⟩ : syracuseStep 3679271 = 5518907) B5518907
theorem B5235911 : Blo 1634016 5235911 := bstep (se 1 (by rfl) ⟨3926933, by rfl⟩ : syracuseStep 5235911 = 7853867) B7853867
theorem B12584135 : Blo 1634016 12584135 := bstep (se 1 (by rfl) ⟨9438101, by rfl⟩ : syracuseStep 12584135 = 18876203) B18876203
theorem B4138199 : Blo 1634016 4138199 := bstep (se 1 (by rfl) ⟨3103649, by rfl⟩ : syracuseStep 4138199 = 6207299) B6207299
theorem B4973783 : Blo 1634016 4973783 := bstep (se 1 (by rfl) ⟨3730337, by rfl⟩ : syracuseStep 4973783 = 7460675) B7460675
theorem B3679451 : Blo 1634016 3679451 := bstep (se 1 (by rfl) ⟨2759588, by rfl⟩ : syracuseStep 3679451 = 5519177) B5519177
theorem B153134317 : Blo 1634016 153134317 := bstep (se 3 (by rfl) ⟨28712684, by rfl⟩ : syracuseStep 153134317 = 57425369) B57425369
theorem B2454011 : Blo 1634016 2454011 := bstep (se 1 (by rfl) ⟨1840508, by rfl⟩ : syracuseStep 2454011 = 3681017) B3681017
theorem B50333075 : Blo 1634016 50333075 := bstep (se 1 (by rfl) ⟨37749806, by rfl⟩ : syracuseStep 50333075 = 75499613) B75499613
theorem B6981025 : Blo 1634016 6981025 := bstep (se 2 (by rfl) ⟨2617884, by rfl⟩ : syracuseStep 6981025 = 5235769) B5235769
theorem B3679649 : Blo 1634016 3679649 := bstep (se 2 (by rfl) ⟨1379868, by rfl⟩ : syracuseStep 3679649 = 2759737) B2759737
theorem B4138553 : Blo 1634016 4138553 := bstep (se 2 (by rfl) ⟨1551957, by rfl⟩ : syracuseStep 4138553 = 3103915) B3103915
theorem B2451179 : Blo 1634016 2451179 := bstep (se 1 (by rfl) ⟨1838384, by rfl⟩ : syracuseStep 2451179 = 3676769) B3676769
theorem B4253419 : Blo 1634016 4253419 := bstep (se 1 (by rfl) ⟨3190064, by rfl⟩ : syracuseStep 4253419 = 6380129) B6380129
theorem B15935363 : Blo 1634016 15935363 := bstep (se 1 (by rfl) ⟨11951522, by rfl⟩ : syracuseStep 15935363 = 23903045) B23903045
theorem B2451407 : Blo 1634016 2451407 := bstep (se 1 (by rfl) ⟨1838555, by rfl⟩ : syracuseStep 2451407 = 3677111) B3677111
theorem B3680207 : Blo 1634016 3680207 := bstep (se 1 (by rfl) ⟨2760155, by rfl⟩ : syracuseStep 3680207 = 5520311) B5520311
theorem B3680585 : Blo 1634016 3680585 := bstep (se 2 (by rfl) ⟨1380219, by rfl⟩ : syracuseStep 3680585 = 2760439) B2760439
theorem B2451803 : Blo 1634016 2451803 := bstep (se 1 (by rfl) ⟨1838852, by rfl⟩ : syracuseStep 2451803 = 3677705) B3677705
theorem B3680603 : Blo 1634016 3680603 := bstep (se 1 (by rfl) ⟨2760452, by rfl⟩ : syracuseStep 3680603 = 5520905) B5520905
theorem B8391023 : Blo 1634016 8391023 := bstep (se 1 (by rfl) ⟨6293267, by rfl⟩ : syracuseStep 8391023 = 12586535) B12586535
theorem B33999239 : Blo 1634016 33999239 := bstep (se 1 (by rfl) ⟨25499429, by rfl⟩ : syracuseStep 33999239 = 50998859) B50998859
theorem B28330373 : Blo 1634016 28330373 := bstep (se 4 (by rfl) ⟨2655972, by rfl⟩ : syracuseStep 28330373 = 5311945) B5311945
theorem B9316781 : Blo 1634016 9316781 := bstep (se 3 (by rfl) ⟨1746896, by rfl⟩ : syracuseStep 9316781 = 3493793) B3493793
theorem B10914259 : Blo 1634016 10914259 := bstep (se 1 (by rfl) ⟨8185694, by rfl⟩ : syracuseStep 10914259 = 16371389) B16371389
theorem B5237243 : Blo 1634016 5237243 := bstep (se 1 (by rfl) ⟨3927932, by rfl⟩ : syracuseStep 5237243 = 7855865) B7855865
theorem B2452031 : Blo 1634016 2452031 := bstep (se 1 (by rfl) ⟨1839023, by rfl⟩ : syracuseStep 2452031 = 3678047) B3678047
theorem B5515883 : Blo 1634016 5515883 := bstep (se 1 (by rfl) ⟨4136912, by rfl⟩ : syracuseStep 5515883 = 8273825) B8273825
theorem B13265531 : Blo 1634016 13265531 := bstep (se 1 (by rfl) ⟨9949148, by rfl⟩ : syracuseStep 13265531 = 19898297) B19898297
theorem B2452151 : Blo 1634016 2452151 := bstep (se 1 (by rfl) ⟨1839113, by rfl⟩ : syracuseStep 2452151 = 3678227) B3678227
theorem B7858883 : Blo 1634016 7858883 := bstep (se 1 (by rfl) ⟨5894162, by rfl⟩ : syracuseStep 7858883 = 11788325) B11788325
theorem B29821745 : Blo 1634016 29821745 := bstep (se 2 (by rfl) ⟨11183154, by rfl⟩ : syracuseStep 29821745 = 22366309) B22366309
theorem B2452379 : Blo 1634016 2452379 := bstep (se 1 (by rfl) ⟨1839284, by rfl⟩ : syracuseStep 2452379 = 3678569) B3678569
theorem B6630299 : Blo 1634016 6630299 := bstep (se 1 (by rfl) ⟨4972724, by rfl⟩ : syracuseStep 6630299 = 9945449) B9945449
theorem B12422159 : Blo 1634016 12422159 := bstep (se 1 (by rfl) ⟨9316619, by rfl⟩ : syracuseStep 12422159 = 18633239) B18633239
theorem B17681485 : Blo 1634016 17681485 := bstep (se 3 (by rfl) ⟨3315278, by rfl⟩ : syracuseStep 17681485 = 6630557) B6630557
theorem B5516477 : Blo 1634016 5516477 := bstep (se 3 (by rfl) ⟨1034339, by rfl⟩ : syracuseStep 5516477 = 2068679) B2068679
theorem B1838299 : Blo 1634016 1838299 := bstep (se 1 (by rfl) ⟨1378724, by rfl⟩ : syracuseStep 1838299 = 2757449) B2757449
theorem B2452775 : Blo 1634016 2452775 := bstep (se 1 (by rfl) ⟨1839581, by rfl⟩ : syracuseStep 2452775 = 3679163) B3679163
theorem B2452859 : Blo 1634016 2452859 := bstep (se 1 (by rfl) ⟨1839644, by rfl⟩ : syracuseStep 2452859 = 3679289) B3679289
theorem B13266305 : Blo 1634016 13266305 := bstep (se 2 (by rfl) ⟨4974864, by rfl⟩ : syracuseStep 13266305 = 9949729) B9949729
theorem B21237137 : Blo 1634016 21237137 := bstep (se 2 (by rfl) ⟨7963926, by rfl⟩ : syracuseStep 21237137 = 15927853) B15927853
theorem B2452985 : Blo 1634016 2452985 := bstep (se 2 (by rfl) ⟨919869, by rfl⟩ : syracuseStep 2452985 = 1839739) B1839739
theorem B1838587 : Blo 1634016 1838587 := bstep (se 1 (by rfl) ⟨1378940, by rfl⟩ : syracuseStep 1838587 = 2757881) B2757881
theorem B5893715 : Blo 1634016 5893715 := bstep (se 1 (by rfl) ⟨4420286, by rfl⟩ : syracuseStep 5893715 = 8840573) B8840573
theorem B3493459 : Blo 1634016 3493459 := bstep (se 1 (by rfl) ⟨2620094, by rfl⟩ : syracuseStep 3493459 = 5240189) B5240189
theorem B2453087 : Blo 1634016 2453087 := bstep (se 1 (by rfl) ⟨1839815, by rfl⟩ : syracuseStep 2453087 = 3679631) B3679631
theorem B1838767 : Blo 1634016 1838767 := bstep (se 1 (by rfl) ⟨1379075, by rfl⟩ : syracuseStep 1838767 = 2758151) B2758151
theorem B8277713 : Blo 1634016 8277713 := bstep (se 2 (by rfl) ⟨3104142, by rfl⟩ : syracuseStep 8277713 = 6208285) B6208285
theorem B2944775 : Blo 1634016 2944775 := bstep (se 1 (by rfl) ⟨2208581, by rfl⟩ : syracuseStep 2944775 = 4417163) B4417163
theorem B4140841 : Blo 1634016 4140841 := bstep (se 2 (by rfl) ⟨1552815, by rfl⟩ : syracuseStep 4140841 = 3105631) B3105631
theorem B1634095 : Blo 1634016 1634095 := bstep (se 1 (by rfl) ⟨1225571, by rfl⟩ : syracuseStep 1634095 = 2451143) B2451143
theorem B4656943 : Blo 1634016 4656943 := bstep (se 1 (by rfl) ⟨3492707, by rfl⟩ : syracuseStep 4656943 = 6985415) B6985415
theorem B2453303 : Blo 1634016 2453303 := bstep (se 1 (by rfl) ⟨1839977, by rfl⟩ : syracuseStep 2453303 = 3679955) B3679955
theorem B1634203 : Blo 1634016 1634203 := bstep (se 1 (by rfl) ⟨1225652, by rfl⟩ : syracuseStep 1634203 = 2451305) B2451305
theorem B1634255 : Blo 1634016 1634255 := bstep (se 1 (by rfl) ⟨1225691, by rfl⟩ : syracuseStep 1634255 = 2451383) B2451383
theorem B1839055 : Blo 1634016 1839055 := bstep (se 1 (by rfl) ⟨1379291, by rfl⟩ : syracuseStep 1839055 = 2758583) B2758583
theorem B15708113 : Blo 1634016 15708113 := bstep (se 2 (by rfl) ⟨5890542, by rfl⟩ : syracuseStep 15708113 = 11781085) B11781085
theorem B1634279 : Blo 1634016 1634279 := bstep (se 1 (by rfl) ⟨1225709, by rfl⟩ : syracuseStep 1634279 = 2451419) B2451419
theorem B2453609 : Blo 1634016 2453609 := bstep (se 2 (by rfl) ⟨920103, by rfl⟩ : syracuseStep 2453609 = 1840207) B1840207
theorem B2617609 : Blo 1634016 2617609 := bstep (se 2 (by rfl) ⟨981603, by rfl⟩ : syracuseStep 2617609 = 1963207) B1963207
theorem B1634591 : Blo 1634016 1634591 := bstep (se 1 (by rfl) ⟨1225943, by rfl⟩ : syracuseStep 1634591 = 2451887) B2451887
theorem B1634651 : Blo 1634016 1634651 := bstep (se 1 (by rfl) ⟨1225988, by rfl⟩ : syracuseStep 1634651 = 2451977) B2451977
theorem B1839451 : Blo 1634016 1839451 := bstep (se 1 (by rfl) ⟨1379588, by rfl⟩ : syracuseStep 1839451 = 2759177) B2759177
theorem B1634671 : Blo 1634016 1634671 := bstep (se 1 (by rfl) ⟨1226003, by rfl⟩ : syracuseStep 1634671 = 2452007) B2452007
theorem B1634727 : Blo 1634016 1634727 := bstep (se 1 (by rfl) ⟨1226045, by rfl⟩ : syracuseStep 1634727 = 2452091) B2452091
theorem B2453927 : Blo 1634016 2453927 := bstep (se 1 (by rfl) ⟨1840445, by rfl⟩ : syracuseStep 2453927 = 3680891) B3680891
theorem B1839559 : Blo 1634016 1839559 := bstep (se 1 (by rfl) ⟨1379669, by rfl⟩ : syracuseStep 1839559 = 2759339) B2759339
theorem B15708653 : Blo 1634016 15708653 := bstep (se 3 (by rfl) ⟨2945372, by rfl⟩ : syracuseStep 15708653 = 5890745) B5890745
theorem B19886573 : Blo 1634016 19886573 := bstep (se 3 (by rfl) ⟨3728732, by rfl⟩ : syracuseStep 19886573 = 7457465) B7457465
theorem B2945531 : Blo 1634016 2945531 := bstep (se 1 (by rfl) ⟨2209148, by rfl⟩ : syracuseStep 2945531 = 4418297) B4418297
theorem B1634811 : Blo 1634016 1634811 := bstep (se 1 (by rfl) ⟨1226108, by rfl⟩ : syracuseStep 1634811 = 2452217) B2452217
theorem B1634879 : Blo 1634016 1634879 := bstep (se 1 (by rfl) ⟨1226159, by rfl⟩ : syracuseStep 1634879 = 2452319) B2452319
theorem B1634887 : Blo 1634016 1634887 := bstep (se 1 (by rfl) ⟨1226165, by rfl⟩ : syracuseStep 1634887 = 2452331) B2452331
theorem B1635039 : Blo 1634016 1635039 := bstep (se 1 (by rfl) ⟨1226279, by rfl⟩ : syracuseStep 1635039 = 2452559) B2452559
theorem B2487007 : Blo 1634016 2487007 := bstep (se 1 (by rfl) ⟨1865255, by rfl⟩ : syracuseStep 2487007 = 3730511) B3730511
theorem B15717149 : Blo 1634016 15717149 := bstep (se 3 (by rfl) ⟨2946965, by rfl⟩ : syracuseStep 15717149 = 5893931) B5893931
theorem B1635119 : Blo 1634016 1635119 := bstep (se 1 (by rfl) ⟨1226339, by rfl⟩ : syracuseStep 1635119 = 2452679) B2452679
theorem B1839919 : Blo 1634016 1839919 := bstep (se 1 (by rfl) ⟨1379939, by rfl⟩ : syracuseStep 1839919 = 2759879) B2759879
theorem B2069327 : Blo 1634016 2069327 := bstep (se 1 (by rfl) ⟨1551995, by rfl⟩ : syracuseStep 2069327 = 3103991) B3103991
theorem B1635227 : Blo 1634016 1635227 := bstep (se 1 (by rfl) ⟨1226420, by rfl⟩ : syracuseStep 1635227 = 2452841) B2452841
theorem B1840027 : Blo 1634016 1840027 := bstep (se 1 (by rfl) ⟨1380020, by rfl⟩ : syracuseStep 1840027 = 2760041) B2760041
theorem B1635279 : Blo 1634016 1635279 := bstep (se 1 (by rfl) ⟨1226459, by rfl⟩ : syracuseStep 1635279 = 2452919) B2452919
theorem B2069479 : Blo 1634016 2069479 := bstep (se 1 (by rfl) ⟨1552109, by rfl⟩ : syracuseStep 2069479 = 3104219) B3104219
theorem B1635303 : Blo 1634016 1635303 := bstep (se 1 (by rfl) ⟨1226477, by rfl⟩ : syracuseStep 1635303 = 2452955) B2452955
theorem B13800527 : Blo 1634016 13800527 := bstep (se 1 (by rfl) ⟨10350395, by rfl⟩ : syracuseStep 13800527 = 20700791) B20700791
theorem B14922841 : Blo 1634016 14922841 := bstep (se 2 (by rfl) ⟨5596065, by rfl⟩ : syracuseStep 14922841 = 11192131) B11192131
theorem B44774657 : Blo 1634016 44774657 := bstep (se 2 (by rfl) ⟨16790496, by rfl⟩ : syracuseStep 44774657 = 33580993) B33580993
theorem B15709463 : Blo 1634016 15709463 := bstep (se 1 (by rfl) ⟨11782097, by rfl⟩ : syracuseStep 15709463 = 23564195) B23564195
theorem B1864991 : Blo 1634016 1864991 := bstep (se 1 (by rfl) ⟨1398743, by rfl⟩ : syracuseStep 1864991 = 2797487) B2797487
theorem B1635615 : Blo 1634016 1635615 := bstep (se 1 (by rfl) ⟨1226711, by rfl⟩ : syracuseStep 1635615 = 2453423) B2453423
theorem B1840423 : Blo 1634016 1840423 := bstep (se 1 (by rfl) ⟨1380317, by rfl⟩ : syracuseStep 1840423 = 2760635) B2760635
theorem B1635675 : Blo 1634016 1635675 := bstep (se 1 (by rfl) ⟨1226756, by rfl⟩ : syracuseStep 1635675 = 2453513) B2453513
theorem B1635695 : Blo 1634016 1635695 := bstep (se 1 (by rfl) ⟨1226771, by rfl⟩ : syracuseStep 1635695 = 2453543) B2453543
theorem B1840495 : Blo 1634016 1840495 := bstep (se 1 (by rfl) ⟨1380371, by rfl⟩ : syracuseStep 1840495 = 2760743) B2760743
theorem B1635751 : Blo 1634016 1635751 := bstep (se 1 (by rfl) ⟨1226813, by rfl⟩ : syracuseStep 1635751 = 2453627) B2453627
theorem B1635835 : Blo 1634016 1635835 := bstep (se 1 (by rfl) ⟨1226876, by rfl⟩ : syracuseStep 1635835 = 2453753) B2453753
theorem B1635903 : Blo 1634016 1635903 := bstep (se 1 (by rfl) ⟨1226927, by rfl⟩ : syracuseStep 1635903 = 2453855) B2453855
theorem B1635911 : Blo 1634016 1635911 := bstep (se 1 (by rfl) ⟨1226933, by rfl⟩ : syracuseStep 1635911 = 2453867) B2453867
theorem B2758441 : Blo 1634016 2758441 := bstep (se 2 (by rfl) ⟨1034415, by rfl⟩ : syracuseStep 2758441 = 2068831) B2068831
theorem B6207313 : Blo 1634016 6207313 := bstep (se 2 (by rfl) ⟨2327742, by rfl⟩ : syracuseStep 6207313 = 4655485) B4655485
theorem B22362041 : Blo 1634016 22362041 := bstep (se 2 (by rfl) ⟨8385765, by rfl⟩ : syracuseStep 22362041 = 16771531) B16771531
theorem B5519393 : Blo 1634016 5519393 := bstep (se 2 (by rfl) ⟨2069772, by rfl⟩ : syracuseStep 5519393 = 4139545) B4139545
theorem B8280143 : Blo 1634016 8280143 := bstep (se 1 (by rfl) ⟨6210107, by rfl⟩ : syracuseStep 8280143 = 12420215) B12420215
theorem B6207617 : Blo 1634016 6207617 := bstep (se 2 (by rfl) ⟨2327856, by rfl⟩ : syracuseStep 6207617 = 4655713) B4655713
theorem B75520289 : Blo 1634016 75520289 := bstep (se 2 (by rfl) ⟨28320108, by rfl⟩ : syracuseStep 75520289 = 56640217) B56640217
theorem B3103201 : Blo 1634016 3103201 := bstep (se 2 (by rfl) ⟨1163700, by rfl⟩ : syracuseStep 3103201 = 2327401) B2327401
theorem B7559675 : Blo 1634016 7559675 := bstep (se 1 (by rfl) ⟨5669756, by rfl⟩ : syracuseStep 7559675 = 11339513) B11339513
theorem B4971071 : Blo 1634016 4971071 := bstep (se 1 (by rfl) ⟨3728303, by rfl⟩ : syracuseStep 4971071 = 7456607) B7456607
theorem B2759231 : Blo 1634016 2759231 := bstep (se 1 (by rfl) ⟨2069423, by rfl⟩ : syracuseStep 2759231 = 4138847) B4138847
theorem B2619967 : Blo 1634016 2619967 := bstep (se 1 (by rfl) ⟨1964975, by rfl⟩ : syracuseStep 2619967 = 3929951) B3929951
theorem B6208073 : Blo 1634016 6208073 := bstep (se 2 (by rfl) ⟨2328027, by rfl⟩ : syracuseStep 6208073 = 4656055) B4656055
theorem B3676751 : Blo 1634016 3676751 := bstep (se 1 (by rfl) ⟨2757563, by rfl⟩ : syracuseStep 3676751 = 5515127) B5515127
theorem B7854671 : Blo 1634016 7854671 := bstep (se 1 (by rfl) ⟨5891003, by rfl⟩ : syracuseStep 7854671 = 11782007) B11782007
theorem B3676895 : Blo 1634016 3676895 := bstep (se 1 (by rfl) ⟨2757671, by rfl⟩ : syracuseStep 3676895 = 5515343) B5515343
theorem B3677147 : Blo 1634016 3677147 := bstep (se 1 (by rfl) ⟨2757860, by rfl⟩ : syracuseStep 3677147 = 5515721) B5515721
theorem B54467603 : Blo 1634016 54467603 := bstep (se 1 (by rfl) ⟨40850702, by rfl⟩ : syracuseStep 54467603 = 81701405) B81701405
theorem B3677327 : Blo 1634016 3677327 := bstep (se 1 (by rfl) ⟨2757995, by rfl⟩ : syracuseStep 3677327 = 5515991) B5515991
theorem B8281277 : Blo 1634016 8281277 := bstep (se 3 (by rfl) ⟨1552739, by rfl⟩ : syracuseStep 8281277 = 3105479) B3105479
theorem B2759899 : Blo 1634016 2759899 := bstep (se 1 (by rfl) ⟨2069924, by rfl⟩ : syracuseStep 2759899 = 4139849) B4139849
theorem B3677417 : Blo 1634016 3677417 := bstep (se 2 (by rfl) ⟨1379031, by rfl⟩ : syracuseStep 3677417 = 2758063) B2758063
theorem B1768735 : Blo 1634016 1768735 := bstep (se 1 (by rfl) ⟨1326551, by rfl⟩ : syracuseStep 1768735 = 2653103) B2653103
theorem B3677471 : Blo 1634016 3677471 := bstep (se 1 (by rfl) ⟨2758103, by rfl⟩ : syracuseStep 3677471 = 5516207) B5516207
theorem B12582281 : Blo 1634016 12582281 := bstep (se 2 (by rfl) ⟨4718355, by rfl⟩ : syracuseStep 12582281 = 9436711) B9436711
theorem B8273339 : Blo 1634016 8273339 := bstep (se 1 (by rfl) ⟨6205004, by rfl⟩ : syracuseStep 8273339 = 12410009) B12410009
theorem B15711803 : Blo 1634016 15711803 := bstep (se 1 (by rfl) ⟨11783852, by rfl⟩ : syracuseStep 15711803 = 23567705) B23567705
theorem B2391647 : Blo 1634016 2391647 := bstep (se 1 (by rfl) ⟨1793735, by rfl⟩ : syracuseStep 2391647 = 3587471) B3587471
theorem B4136609 : Blo 1634016 4136609 := bstep (se 2 (by rfl) ⟨1551228, by rfl⟩ : syracuseStep 4136609 = 3102457) B3102457
theorem B7855825 : Blo 1634016 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B3677993 : Blo 1634016 3677993 := bstep (se 2 (by rfl) ⟨1379247, by rfl⟩ : syracuseStep 3677993 = 2758495) B2758495
theorem B2760655 : Blo 1634016 2760655 := bstep (se 1 (by rfl) ⟨2070491, by rfl⟩ : syracuseStep 2760655 = 4140983) B4140983
theorem B3490145 : Blo 1634016 3490145 := bstep (se 2 (by rfl) ⟨1308804, by rfl⟩ : syracuseStep 3490145 = 2617609) B2617609
theorem B3490247 : Blo 1634016 3490247 := bstep (se 1 (by rfl) ⟨2617685, by rfl⟩ : syracuseStep 3490247 = 5235371) B5235371
theorem B9306575 : Blo 1634016 9306575 := bstep (se 1 (by rfl) ⟨6979931, by rfl⟩ : syracuseStep 9306575 = 13959863) B13959863
theorem B10478099 : Blo 1634016 10478099 := bstep (se 1 (by rfl) ⟨7858574, by rfl⟩ : syracuseStep 10478099 = 15717149) B15717149
theorem B13263421 : Blo 1634016 13263421 := bstep (se 3 (by rfl) ⟨2486891, by rfl⟩ : syracuseStep 13263421 = 4973783) B4973783
theorem B4137601 : Blo 1634016 4137601 := bstep (se 2 (by rfl) ⟨1551600, by rfl⟩ : syracuseStep 4137601 = 3103201) B3103201
theorem B9200351 : Blo 1634016 9200351 := bstep (se 1 (by rfl) ⟨6900263, by rfl⟩ : syracuseStep 9200351 = 13800527) B13800527
theorem B4973309 : Blo 1634016 4973309 := bstep (se 3 (by rfl) ⟨932495, by rfl⟩ : syracuseStep 4973309 = 1864991) B1864991
theorem B3490607 : Blo 1634016 3490607 := bstep (se 1 (by rfl) ⟨2617955, by rfl⟩ : syracuseStep 3490607 = 5235911) B5235911
theorem B8389423 : Blo 1634016 8389423 := bstep (se 1 (by rfl) ⟨6292067, by rfl⟩ : syracuseStep 8389423 = 12584135) B12584135
theorem B33555383 : Blo 1634016 33555383 := bstep (se 1 (by rfl) ⟨25166537, by rfl⟩ : syracuseStep 33555383 = 50333075) B50333075
theorem B13264037 : Blo 1634016 13264037 := bstep (se 4 (by rfl) ⟨1243503, by rfl⟩ : syracuseStep 13264037 = 2487007) B2487007
theorem B3679595 : Blo 1634016 3679595 := bstep (se 1 (by rfl) ⟨2759696, by rfl⟩ : syracuseStep 3679595 = 5519393) B5519393
theorem B4138411 : Blo 1634016 4138411 := bstep (se 1 (by rfl) ⟨3103808, by rfl⟩ : syracuseStep 4138411 = 6207617) B6207617
theorem B6211187 : Blo 1634016 6211187 := bstep (se 1 (by rfl) ⟨4658390, by rfl⟩ : syracuseStep 6211187 = 9316781) B9316781
theorem B2451065 : Blo 1634016 2451065 := bstep (se 2 (by rfl) ⟨919149, by rfl⟩ : syracuseStep 2451065 = 1838299) B1838299
theorem B3679865 : Blo 1634016 3679865 := bstep (se 2 (by rfl) ⟨1379949, by rfl⟩ : syracuseStep 3679865 = 2759899) B2759899
theorem B3491495 : Blo 1634016 3491495 := bstep (se 1 (by rfl) ⟨2618621, by rfl⟩ : syracuseStep 3491495 = 5237243) B5237243
theorem B5039783 : Blo 1634016 5039783 := bstep (se 1 (by rfl) ⟨3779837, by rfl⟩ : syracuseStep 5039783 = 7559675) B7559675
theorem B4138715 : Blo 1634016 4138715 := bstep (se 1 (by rfl) ⟨3104036, by rfl⟩ : syracuseStep 4138715 = 6208073) B6208073
theorem B2451167 : Blo 1634016 2451167 := bstep (se 1 (by rfl) ⟨1838375, by rfl⟩ : syracuseStep 2451167 = 3676751) B3676751
theorem B2451263 : Blo 1634016 2451263 := bstep (se 1 (by rfl) ⟨1838447, by rfl⟩ : syracuseStep 2451263 = 3676895) B3676895
theorem B9308033 : Blo 1634016 9308033 := bstep (se 2 (by rfl) ⟨3490512, by rfl⟩ : syracuseStep 9308033 = 6981025) B6981025
theorem B2451431 : Blo 1634016 2451431 := bstep (se 1 (by rfl) ⟨1838573, by rfl⟩ : syracuseStep 2451431 = 3677147) B3677147
theorem B2451449 : Blo 1634016 2451449 := bstep (se 2 (by rfl) ⟨919293, by rfl⟩ : syracuseStep 2451449 = 1838587) B1838587
theorem B2451551 : Blo 1634016 2451551 := bstep (se 1 (by rfl) ⟨1838663, by rfl⟩ : syracuseStep 2451551 = 3677327) B3677327
theorem B2451611 : Blo 1634016 2451611 := bstep (se 1 (by rfl) ⟨1838708, by rfl⟩ : syracuseStep 2451611 = 3677417) B3677417
theorem B2451647 : Blo 1634016 2451647 := bstep (se 1 (by rfl) ⟨1838735, by rfl⟩ : syracuseStep 2451647 = 3677471) B3677471
theorem B2451689 : Blo 1634016 2451689 := bstep (se 2 (by rfl) ⟨919383, by rfl⟩ : syracuseStep 2451689 = 1838767) B1838767
theorem B14158091 : Blo 1634016 14158091 := bstep (se 1 (by rfl) ⟨10618568, by rfl⟩ : syracuseStep 14158091 = 21237137) B21237137
theorem B5515559 : Blo 1634016 5515559 := bstep (se 1 (by rfl) ⟨4136669, by rfl⟩ : syracuseStep 5515559 = 8273339) B8273339
theorem B5671225 : Blo 1634016 5671225 := bstep (se 2 (by rfl) ⟨2126709, by rfl⟩ : syracuseStep 5671225 = 4253419) B4253419
theorem B8276417 : Blo 1634016 8276417 := bstep (se 2 (by rfl) ⟨3103656, by rfl⟩ : syracuseStep 8276417 = 6207313) B6207313
theorem B59632109 : Blo 1634016 59632109 := bstep (se 3 (by rfl) ⟨11181020, by rfl⟩ : syracuseStep 59632109 = 22362041) B22362041
theorem B2451995 : Blo 1634016 2451995 := bstep (se 1 (by rfl) ⟨1838996, by rfl⟩ : syracuseStep 2451995 = 3677993) B3677993
theorem B2452073 : Blo 1634016 2452073 := bstep (se 2 (by rfl) ⟨919527, by rfl⟩ : syracuseStep 2452073 = 1839055) B1839055
theorem B3680873 : Blo 1634016 3680873 := bstep (se 2 (by rfl) ⟨1380327, by rfl⟩ : syracuseStep 3680873 = 2760655) B2760655
theorem B10472075 : Blo 1634016 10472075 := bstep (se 1 (by rfl) ⟨7854056, by rfl⟩ : syracuseStep 10472075 = 15708113) B15708113
theorem B4139707 : Blo 1634016 4139707 := bstep (se 1 (by rfl) ⟨3104780, by rfl⟩ : syracuseStep 4139707 = 6209561) B6209561
theorem B6204215 : Blo 1634016 6204215 := bstep (se 1 (by rfl) ⟨4653161, by rfl⟩ : syracuseStep 6204215 = 9306323) B9306323
theorem B9939905 : Blo 1634016 9939905 := bstep (se 2 (by rfl) ⟨3727464, by rfl⟩ : syracuseStep 9939905 = 7454929) B7454929
theorem B23571395 : Blo 1634016 23571395 := bstep (se 1 (by rfl) ⟨17678546, by rfl⟩ : syracuseStep 23571395 = 35357093) B35357093
theorem B4140011 : Blo 1634016 4140011 := bstep (se 1 (by rfl) ⟨3105008, by rfl⟩ : syracuseStep 4140011 = 6210017) B6210017
theorem B10472435 : Blo 1634016 10472435 := bstep (se 1 (by rfl) ⟨7854326, by rfl⟩ : syracuseStep 10472435 = 15708653) B15708653
theorem B13257715 : Blo 1634016 13257715 := bstep (se 1 (by rfl) ⟨9943286, by rfl⟩ : syracuseStep 13257715 = 19886573) B19886573
theorem B7859207 : Blo 1634016 7859207 := bstep (se 1 (by rfl) ⟨5894405, by rfl⟩ : syracuseStep 7859207 = 11788811) B11788811
theorem B18631781 : Blo 1634016 18631781 := bstep (se 4 (by rfl) ⟨1746729, by rfl⟩ : syracuseStep 18631781 = 3493459) B3493459
theorem B2796665 : Blo 1634016 2796665 := bstep (se 2 (by rfl) ⟨1048749, by rfl⟩ : syracuseStep 2796665 = 2097499) B2097499
theorem B2452601 : Blo 1634016 2452601 := bstep (se 2 (by rfl) ⟨919725, by rfl⟩ : syracuseStep 2452601 = 1839451) B1839451
theorem B5516423 : Blo 1634016 5516423 := bstep (se 1 (by rfl) ⟨4137317, by rfl⟩ : syracuseStep 5516423 = 8274635) B8274635
theorem B2452703 : Blo 1634016 2452703 := bstep (se 1 (by rfl) ⟨1839527, by rfl⟩ : syracuseStep 2452703 = 3679055) B3679055
theorem B5516531 : Blo 1634016 5516531 := bstep (se 1 (by rfl) ⟨4137398, by rfl⟩ : syracuseStep 5516531 = 8274797) B8274797
theorem B2452745 : Blo 1634016 2452745 := bstep (se 2 (by rfl) ⟨919779, by rfl⟩ : syracuseStep 2452745 = 1839559) B1839559
theorem B14552345 : Blo 1634016 14552345 := bstep (se 2 (by rfl) ⟨5457129, by rfl⟩ : syracuseStep 14552345 = 10914259) B10914259
theorem B2452847 : Blo 1634016 2452847 := bstep (se 1 (by rfl) ⟨1839635, by rfl⟩ : syracuseStep 2452847 = 3679271) B3679271
theorem B3493289 : Blo 1634016 3493289 := bstep (se 2 (by rfl) ⟨1309983, by rfl⟩ : syracuseStep 3493289 = 2619967) B2619967
theorem B2452967 : Blo 1634016 2452967 := bstep (se 1 (by rfl) ⟨1839725, by rfl⟩ : syracuseStep 2452967 = 3679451) B3679451
theorem B10472975 : Blo 1634016 10472975 := bstep (se 1 (by rfl) ⟨7854731, by rfl⟩ : syracuseStep 10472975 = 15709463) B15709463
theorem B2453099 : Blo 1634016 2453099 := bstep (se 1 (by rfl) ⟨1839824, by rfl⟩ : syracuseStep 2453099 = 3679649) B3679649
theorem B2453225 : Blo 1634016 2453225 := bstep (se 2 (by rfl) ⟨919959, by rfl⟩ : syracuseStep 2453225 = 1839919) B1839919
theorem B1634119 : Blo 1634016 1634119 := bstep (se 1 (by rfl) ⟨1225589, by rfl⟩ : syracuseStep 1634119 = 2451179) B2451179
theorem B2453369 : Blo 1634016 2453369 := bstep (se 2 (by rfl) ⟨920013, by rfl⟩ : syracuseStep 2453369 = 1840027) B1840027
theorem B20950913 : Blo 1634016 20950913 := bstep (se 2 (by rfl) ⟨7856592, by rfl⟩ : syracuseStep 20950913 = 15713185) B15713185
theorem B1634271 : Blo 1634016 1634271 := bstep (se 1 (by rfl) ⟨1225703, by rfl⟩ : syracuseStep 1634271 = 2451407) B2451407
theorem B2453471 : Blo 1634016 2453471 := bstep (se 1 (by rfl) ⟨1840103, by rfl⟩ : syracuseStep 2453471 = 3680207) B3680207
theorem B9433253 : Blo 1634016 9433253 := bstep (se 4 (by rfl) ⟨884367, by rfl⟩ : syracuseStep 9433253 = 1768735) B1768735
theorem B2453723 : Blo 1634016 2453723 := bstep (se 1 (by rfl) ⟨1840292, by rfl⟩ : syracuseStep 2453723 = 3680585) B3680585
theorem B1634535 : Blo 1634016 1634535 := bstep (se 1 (by rfl) ⟨1225901, by rfl⟩ : syracuseStep 1634535 = 2451803) B2451803
theorem B2453735 : Blo 1634016 2453735 := bstep (se 1 (by rfl) ⟨1840301, by rfl⟩ : syracuseStep 2453735 = 3680603) B3680603
theorem B6377725 : Blo 1634016 6377725 := bstep (se 3 (by rfl) ⟨1195823, by rfl⟩ : syracuseStep 6377725 = 2391647) B2391647
theorem B18886915 : Blo 1634016 18886915 := bstep (se 1 (by rfl) ⟨14165186, by rfl⟩ : syracuseStep 18886915 = 28330373) B28330373
theorem B1634687 : Blo 1634016 1634687 := bstep (se 1 (by rfl) ⟨1226015, by rfl⟩ : syracuseStep 1634687 = 2452031) B2452031
theorem B3314047 : Blo 1634016 3314047 := bstep (se 1 (by rfl) ⟨2485535, by rfl⟩ : syracuseStep 3314047 = 4971071) B4971071
theorem B1839487 : Blo 1634016 1839487 := bstep (se 1 (by rfl) ⟨1379615, by rfl⟩ : syracuseStep 1839487 = 2759231) B2759231
theorem B2453897 : Blo 1634016 2453897 := bstep (se 2 (by rfl) ⟨920211, by rfl⟩ : syracuseStep 2453897 = 1840423) B1840423
theorem B8843687 : Blo 1634016 8843687 := bstep (se 1 (by rfl) ⟨6632765, by rfl⟩ : syracuseStep 8843687 = 13265531) B13265531
theorem B1634767 : Blo 1634016 1634767 := bstep (se 1 (by rfl) ⟨1226075, by rfl⟩ : syracuseStep 1634767 = 2452151) B2452151
theorem B5239255 : Blo 1634016 5239255 := bstep (se 1 (by rfl) ⟨3929441, by rfl⟩ : syracuseStep 5239255 = 7858883) B7858883
theorem B2453993 : Blo 1634016 2453993 := bstep (se 2 (by rfl) ⟨920247, by rfl⟩ : syracuseStep 2453993 = 1840495) B1840495
theorem B1634919 : Blo 1634016 1634919 := bstep (se 1 (by rfl) ⟨1226189, by rfl⟩ : syracuseStep 1634919 = 2452379) B2452379
theorem B4420199 : Blo 1634016 4420199 := bstep (se 1 (by rfl) ⟨3315149, by rfl⟩ : syracuseStep 4420199 = 6630299) B6630299
theorem B36311735 : Blo 1634016 36311735 := bstep (se 1 (by rfl) ⟨27233801, by rfl⟩ : syracuseStep 36311735 = 54467603) B54467603
theorem B7852733 : Blo 1634016 7852733 := bstep (se 3 (by rfl) ⟨1472387, by rfl⟩ : syracuseStep 7852733 = 2944775) B2944775
theorem B1635183 : Blo 1634016 1635183 := bstep (se 1 (by rfl) ⟨1226387, by rfl⟩ : syracuseStep 1635183 = 2452775) B2452775
theorem B5518205 : Blo 1634016 5518205 := bstep (se 3 (by rfl) ⟨1034663, by rfl⟩ : syracuseStep 5518205 = 2069327) B2069327
theorem B1635239 : Blo 1634016 1635239 := bstep (se 1 (by rfl) ⟨1226429, by rfl⟩ : syracuseStep 1635239 = 2452859) B2452859
theorem B8844203 : Blo 1634016 8844203 := bstep (se 1 (by rfl) ⟨6633152, by rfl⟩ : syracuseStep 8844203 = 13266305) B13266305
theorem B10474433 : Blo 1634016 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B1635323 : Blo 1634016 1635323 := bstep (se 1 (by rfl) ⟨1226492, by rfl⟩ : syracuseStep 1635323 = 2452985) B2452985
theorem B10474535 : Blo 1634016 10474535 := bstep (se 1 (by rfl) ⟨7855901, by rfl⟩ : syracuseStep 10474535 = 15711803) B15711803
theorem B3929143 : Blo 1634016 3929143 := bstep (se 1 (by rfl) ⟨2946857, by rfl⟩ : syracuseStep 3929143 = 5893715) B5893715
theorem B1635391 : Blo 1634016 1635391 := bstep (se 1 (by rfl) ⟨1226543, by rfl⟩ : syracuseStep 1635391 = 2453087) B2453087
theorem B2757739 : Blo 1634016 2757739 := bstep (se 1 (by rfl) ⟨2068304, by rfl⟩ : syracuseStep 2757739 = 4136609) B4136609
theorem B5518475 : Blo 1634016 5518475 := bstep (se 1 (by rfl) ⟨4138856, by rfl⟩ : syracuseStep 5518475 = 8277713) B8277713
theorem B1635535 : Blo 1634016 1635535 := bstep (se 1 (by rfl) ⟨1226651, by rfl⟩ : syracuseStep 1635535 = 2453303) B2453303
theorem B2758043 : Blo 1634016 2758043 := bstep (se 1 (by rfl) ⟨2068532, by rfl⟩ : syracuseStep 2758043 = 4137065) B4137065
theorem B1635739 : Blo 1634016 1635739 := bstep (se 1 (by rfl) ⟨1226804, by rfl⟩ : syracuseStep 1635739 = 2453609) B2453609
theorem B2070127 : Blo 1634016 2070127 := bstep (se 1 (by rfl) ⟨1552595, by rfl⟩ : syracuseStep 2070127 = 3105191) B3105191
theorem B1635951 : Blo 1634016 1635951 := bstep (se 1 (by rfl) ⟨1226963, by rfl⟩ : syracuseStep 1635951 = 2453927) B2453927
theorem B1963687 : Blo 1634016 1963687 := bstep (se 1 (by rfl) ⟨1472765, by rfl⟩ : syracuseStep 1963687 = 2945531) B2945531
theorem B1636007 : Blo 1634016 1636007 := bstep (se 1 (by rfl) ⟨1227005, by rfl⟩ : syracuseStep 1636007 = 2454011) B2454011
theorem B2758367 : Blo 1634016 2758367 := bstep (se 1 (by rfl) ⟨2068775, by rfl⟩ : syracuseStep 2758367 = 4137551) B4137551
theorem B8279819 : Blo 1634016 8279819 := bstep (se 1 (by rfl) ⟨6209864, by rfl⟩ : syracuseStep 8279819 = 12419729) B12419729
theorem B100685825 : Blo 1634016 100685825 := bstep (se 2 (by rfl) ⟨37757184, by rfl⟩ : syracuseStep 100685825 = 75514369) B75514369
theorem B2758799 : Blo 1634016 2758799 := bstep (se 1 (by rfl) ⟨2069099, by rfl⟩ : syracuseStep 2758799 = 4138199) B4138199
theorem B29849771 : Blo 1634016 29849771 := bstep (se 1 (by rfl) ⟨22387328, by rfl⟩ : syracuseStep 29849771 = 44774657) B44774657
theorem B33552749 : Blo 1634016 33552749 := bstep (se 3 (by rfl) ⟨6291140, by rfl⟩ : syracuseStep 33552749 = 12582281) B12582281
theorem B2759035 : Blo 1634016 2759035 := bstep (se 1 (by rfl) ⟨2069276, by rfl⟩ : syracuseStep 2759035 = 4138553) B4138553
theorem B816716357 : Blo 1634016 816716357 := bstep (se 4 (by rfl) ⟨76567158, by rfl⟩ : syracuseStep 816716357 = 153134317) B153134317
theorem B10623575 : Blo 1634016 10623575 := bstep (se 1 (by rfl) ⟨7967681, by rfl⟩ : syracuseStep 10623575 = 15935363) B15935363
theorem B2759305 : Blo 1634016 2759305 := bstep (se 2 (by rfl) ⟨1034739, by rfl⟩ : syracuseStep 2759305 = 2069479) B2069479
theorem B5520095 : Blo 1634016 5520095 := bstep (se 1 (by rfl) ⟨4140071, by rfl⟩ : syracuseStep 5520095 = 8280143) B8280143
theorem B23575313 : Blo 1634016 23575313 := bstep (se 2 (by rfl) ⟨8840742, by rfl⟩ : syracuseStep 23575313 = 17681485) B17681485
theorem B19897121 : Blo 1634016 19897121 := bstep (se 2 (by rfl) ⟨7461420, by rfl⟩ : syracuseStep 19897121 = 14922841) B14922841
theorem B50346859 : Blo 1634016 50346859 := bstep (se 1 (by rfl) ⟨37760144, by rfl⟩ : syracuseStep 50346859 = 75520289) B75520289
theorem B20945789 : Blo 1634016 20945789 := bstep (se 3 (by rfl) ⟨3927335, by rfl⟩ : syracuseStep 20945789 = 7854671) B7854671
theorem B5594015 : Blo 1634016 5594015 := bstep (se 1 (by rfl) ⟨4195511, by rfl⟩ : syracuseStep 5594015 = 8391023) B8391023
theorem B22666159 : Blo 1634016 22666159 := bstep (se 1 (by rfl) ⟨16999619, by rfl⟩ : syracuseStep 22666159 = 33999239) B33999239
theorem B3677255 : Blo 1634016 3677255 := bstep (se 1 (by rfl) ⟨2757941, by rfl⟩ : syracuseStep 3677255 = 5515883) B5515883
theorem B19881163 : Blo 1634016 19881163 := bstep (se 1 (by rfl) ⟨14910872, by rfl⟩ : syracuseStep 19881163 = 29821745) B29821745
theorem B8281439 : Blo 1634016 8281439 := bstep (se 1 (by rfl) ⟨6211079, by rfl⟩ : syracuseStep 8281439 = 12422159) B12422159
theorem B3677651 : Blo 1634016 3677651 := bstep (se 1 (by rfl) ⟨2758238, by rfl⟩ : syracuseStep 3677651 = 5516477) B5516477
theorem B5520851 : Blo 1634016 5520851 := bstep (se 1 (by rfl) ⟨4140638, by rfl⟩ : syracuseStep 5520851 = 8281277) B8281277
theorem B3677921 : Blo 1634016 3677921 := bstep (se 2 (by rfl) ⟨1379220, by rfl⟩ : syracuseStep 3677921 = 2758441) B2758441
theorem B5521121 : Blo 1634016 5521121 := bstep (se 2 (by rfl) ⟨2070420, by rfl⟩ : syracuseStep 5521121 = 4140841) B4140841
theorem B6209257 : Blo 1634016 6209257 := bstep (se 2 (by rfl) ⟨2328471, by rfl⟩ : syracuseStep 6209257 = 4656943) B4656943
theorem B2326763 : Blo 1634016 2326763 := bstep (se 1 (by rfl) ⟨1745072, by rfl⟩ : syracuseStep 2326763 = 3490145) B3490145
theorem B8503633 : Blo 1634016 8503633 := bstep (se 2 (by rfl) ⟨3188862, by rfl⟩ : syracuseStep 8503633 = 6377725) B6377725
theorem B7561633 : Blo 1634016 7561633 := bstep (se 2 (by rfl) ⟨2835612, by rfl⟩ : syracuseStep 7561633 = 5671225) B5671225
theorem B5235155 : Blo 1634016 5235155 := bstep (se 1 (by rfl) ⟨3926366, by rfl⟩ : syracuseStep 5235155 = 7852733) B7852733
theorem B3678713 : Blo 1634016 3678713 := bstep (se 2 (by rfl) ⟨1379517, by rfl⟩ : syracuseStep 3678713 = 2759035) B2759035
theorem B2327071 : Blo 1634016 2327071 := bstep (se 1 (by rfl) ⟨1745303, by rfl⟩ : syracuseStep 2327071 = 3490607) B3490607
theorem B3678803 : Blo 1634016 3678803 := bstep (se 1 (by rfl) ⟨2759102, by rfl⟩ : syracuseStep 3678803 = 5518205) B5518205
theorem B3678983 : Blo 1634016 3678983 := bstep (se 1 (by rfl) ⟨2759237, by rfl⟩ : syracuseStep 3678983 = 5518475) B5518475
theorem B3679073 : Blo 1634016 3679073 := bstep (se 2 (by rfl) ⟨1379652, by rfl⟩ : syracuseStep 3679073 = 2759305) B2759305
theorem B89473997 : Blo 1634016 89473997 := bstep (se 3 (by rfl) ⟨16776374, by rfl⟩ : syracuseStep 89473997 = 33552749) B33552749
theorem B2327663 : Blo 1634016 2327663 := bstep (se 1 (by rfl) ⟨1745747, by rfl⟩ : syracuseStep 2327663 = 3491495) B3491495
theorem B3359855 : Blo 1634016 3359855 := bstep (se 1 (by rfl) ⟨2519891, by rfl⟩ : syracuseStep 3359855 = 5039783) B5039783
theorem B9307325 : Blo 1634016 9307325 := bstep (se 3 (by rfl) ⟨1745123, by rfl⟩ : syracuseStep 9307325 = 3490247) B3490247
theorem B30221545 : Blo 1634016 30221545 := bstep (se 2 (by rfl) ⟨11333079, by rfl⟩ : syracuseStep 30221545 = 22666159) B22666159
theorem B100730213 : Blo 1634016 100730213 := bstep (se 4 (by rfl) ⟨9443457, by rfl⟩ : syracuseStep 100730213 = 18886915) B18886915
theorem B19899847 : Blo 1634016 19899847 := bstep (se 1 (by rfl) ⟨14924885, by rfl⟩ : syracuseStep 19899847 = 29849771) B29849771
theorem B9438727 : Blo 1634016 9438727 := bstep (se 1 (by rfl) ⟨7079045, by rfl⟩ : syracuseStep 9438727 = 14158091) B14158091
theorem B28329533 : Blo 1634016 28329533 := bstep (se 3 (by rfl) ⟨5311787, by rfl⟩ : syracuseStep 28329533 = 10623575) B10623575
theorem B6981383 : Blo 1634016 6981383 := bstep (se 1 (by rfl) ⟨5236037, by rfl⟩ : syracuseStep 6981383 = 10472075) B10472075
theorem B96831293 : Blo 1634016 96831293 := bstep (se 3 (by rfl) ⟨18155867, by rfl⟩ : syracuseStep 96831293 = 36311735) B36311735
theorem B3680063 : Blo 1634016 3680063 := bstep (se 1 (by rfl) ⟨2760047, by rfl⟩ : syracuseStep 3680063 = 5520095) B5520095
theorem B3729343 : Blo 1634016 3729343 := bstep (se 1 (by rfl) ⟨2797007, by rfl⟩ : syracuseStep 3729343 = 5594015) B5594015
theorem B15714263 : Blo 1634016 15714263 := bstep (se 1 (by rfl) ⟨11785697, by rfl⟩ : syracuseStep 15714263 = 23571395) B23571395
theorem B6981623 : Blo 1634016 6981623 := bstep (se 1 (by rfl) ⟨5236217, by rfl⟩ : syracuseStep 6981623 = 10472435) B10472435
theorem B62867501 : Blo 1634016 62867501 := bstep (se 3 (by rfl) ⟨11787656, by rfl⟩ : syracuseStep 62867501 = 23575313) B23575313
theorem B2451503 : Blo 1634016 2451503 := bstep (se 1 (by rfl) ⟨1838627, by rfl⟩ : syracuseStep 2451503 = 3677255) B3677255
theorem B12421187 : Blo 1634016 12421187 := bstep (se 1 (by rfl) ⟨9315890, by rfl⟩ : syracuseStep 12421187 = 18631781) B18631781
theorem B9701563 : Blo 1634016 9701563 := bstep (se 1 (by rfl) ⟨7276172, by rfl⟩ : syracuseStep 9701563 = 14552345) B14552345
theorem B2328859 : Blo 1634016 2328859 := bstep (se 1 (by rfl) ⟨1746644, by rfl⟩ : syracuseStep 2328859 = 3493289) B3493289
theorem B2451767 : Blo 1634016 2451767 := bstep (se 1 (by rfl) ⟨1838825, by rfl⟩ : syracuseStep 2451767 = 3677651) B3677651
theorem B3680567 : Blo 1634016 3680567 := bstep (se 1 (by rfl) ⟨2760425, by rfl⟩ : syracuseStep 3680567 = 5520851) B5520851
theorem B6981983 : Blo 1634016 6981983 := bstep (se 1 (by rfl) ⟨5236487, by rfl⟩ : syracuseStep 6981983 = 10472975) B10472975
theorem B2451947 : Blo 1634016 2451947 := bstep (se 1 (by rfl) ⟨1838960, by rfl⟩ : syracuseStep 2451947 = 3677921) B3677921
theorem B3680747 : Blo 1634016 3680747 := bstep (se 1 (by rfl) ⟨2760560, by rfl⟩ : syracuseStep 3680747 = 5521121) B5521121
theorem B20957885 : Blo 1634016 20957885 := bstep (se 3 (by rfl) ⟨3929603, by rfl⟩ : syracuseStep 20957885 = 7859207) B7859207
theorem B6204383 : Blo 1634016 6204383 := bstep (se 1 (by rfl) ⟨4653287, by rfl⟩ : syracuseStep 6204383 = 9306575) B9306575
theorem B7457773 : Blo 1634016 7457773 := bstep (se 3 (by rfl) ⟨1398332, by rfl⟩ : syracuseStep 7457773 = 2796665) B2796665
theorem B4418729 : Blo 1634016 4418729 := bstep (se 2 (by rfl) ⟨1657023, by rfl⟩ : syracuseStep 4418729 = 3314047) B3314047
theorem B2452649 : Blo 1634016 2452649 := bstep (se 2 (by rfl) ⟨919743, by rfl⟩ : syracuseStep 2452649 = 1839487) B1839487
theorem B6982955 : Blo 1634016 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B6983023 : Blo 1634016 6983023 := bstep (se 1 (by rfl) ⟨5237267, by rfl⟩ : syracuseStep 6983023 = 10474535) B10474535
theorem B8842691 : Blo 1634016 8842691 := bstep (se 1 (by rfl) ⟨6632018, by rfl⟩ : syracuseStep 8842691 = 13264037) B13264037
theorem B5516801 : Blo 1634016 5516801 := bstep (se 2 (by rfl) ⟨2068800, by rfl⟩ : syracuseStep 5516801 = 4137601) B4137601
theorem B2453063 : Blo 1634016 2453063 := bstep (se 1 (by rfl) ⟨1839797, by rfl⟩ : syracuseStep 2453063 = 3679595) B3679595
theorem B1838695 : Blo 1634016 1838695 := bstep (se 1 (by rfl) ⟨1379021, by rfl⟩ : syracuseStep 1838695 = 2758043) B2758043
theorem B11185897 : Blo 1634016 11185897 := bstep (se 2 (by rfl) ⟨4194711, by rfl⟩ : syracuseStep 11185897 = 8389423) B8389423
theorem B4140791 : Blo 1634016 4140791 := bstep (se 1 (by rfl) ⟨3105593, by rfl⟩ : syracuseStep 4140791 = 6211187) B6211187
theorem B1634043 : Blo 1634016 1634043 := bstep (se 1 (by rfl) ⟨1225532, by rfl⟩ : syracuseStep 1634043 = 2451065) B2451065
theorem B2453243 : Blo 1634016 2453243 := bstep (se 1 (by rfl) ⟨1839932, by rfl⟩ : syracuseStep 2453243 = 3679865) B3679865
theorem B67129145 : Blo 1634016 67129145 := bstep (se 2 (by rfl) ⟨25173429, by rfl⟩ : syracuseStep 67129145 = 50346859) B50346859
theorem B1838911 : Blo 1634016 1838911 := bstep (se 1 (by rfl) ⟨1379183, by rfl⟩ : syracuseStep 1838911 = 2758367) B2758367
theorem B1634111 : Blo 1634016 1634111 := bstep (se 1 (by rfl) ⟨1225583, by rfl⟩ : syracuseStep 1634111 = 2451167) B2451167
theorem B1634175 : Blo 1634016 1634175 := bstep (se 1 (by rfl) ⟨1225631, by rfl⟩ : syracuseStep 1634175 = 2451263) B2451263
theorem B6205355 : Blo 1634016 6205355 := bstep (se 1 (by rfl) ⟨4654016, by rfl⟩ : syracuseStep 6205355 = 9308033) B9308033
theorem B1634287 : Blo 1634016 1634287 := bstep (se 1 (by rfl) ⟨1225715, by rfl⟩ : syracuseStep 1634287 = 2451431) B2451431
theorem B1634299 : Blo 1634016 1634299 := bstep (se 1 (by rfl) ⟨1225724, by rfl⟩ : syracuseStep 1634299 = 2451449) B2451449
theorem B1634367 : Blo 1634016 1634367 := bstep (se 1 (by rfl) ⟨1225775, by rfl⟩ : syracuseStep 1634367 = 2451551) B2451551
theorem B5238857 : Blo 1634016 5238857 := bstep (se 2 (by rfl) ⟨1964571, by rfl⟩ : syracuseStep 5238857 = 3929143) B3929143
theorem B1839199 : Blo 1634016 1839199 := bstep (se 1 (by rfl) ⟨1379399, by rfl⟩ : syracuseStep 1839199 = 2758799) B2758799
theorem B1634407 : Blo 1634016 1634407 := bstep (se 1 (by rfl) ⟨1225805, by rfl⟩ : syracuseStep 1634407 = 2451611) B2451611
theorem B1634431 : Blo 1634016 1634431 := bstep (se 1 (by rfl) ⟨1225823, by rfl⟩ : syracuseStep 1634431 = 2451647) B2451647
theorem B1634459 : Blo 1634016 1634459 := bstep (se 1 (by rfl) ⟨1225844, by rfl⟩ : syracuseStep 1634459 = 2451689) B2451689
theorem B5517611 : Blo 1634016 5517611 := bstep (se 1 (by rfl) ⟨4138208, by rfl⟩ : syracuseStep 5517611 = 8276417) B8276417
theorem B1634663 : Blo 1634016 1634663 := bstep (se 1 (by rfl) ⟨1225997, by rfl⟩ : syracuseStep 1634663 = 2451995) B2451995
theorem B544477571 : Blo 1634016 544477571 := bstep (se 1 (by rfl) ⟨408358178, by rfl⟩ : syracuseStep 544477571 = 816716357) B816716357
theorem B1634715 : Blo 1634016 1634715 := bstep (se 1 (by rfl) ⟨1226036, by rfl⟩ : syracuseStep 1634715 = 2452073) B2452073
theorem B2453915 : Blo 1634016 2453915 := bstep (se 1 (by rfl) ⟨1840436, by rfl⟩ : syracuseStep 2453915 = 3680873) B3680873
theorem B5517881 : Blo 1634016 5517881 := bstep (se 2 (by rfl) ⟨2069205, by rfl⟩ : syracuseStep 5517881 = 4138411) B4138411
theorem B13963859 : Blo 1634016 13963859 := bstep (se 1 (by rfl) ⟨10472894, by rfl⟩ : syracuseStep 13963859 = 20945789) B20945789
theorem B1635067 : Blo 1634016 1635067 := bstep (se 1 (by rfl) ⟨1226300, by rfl⟩ : syracuseStep 1635067 = 2452601) B2452601
theorem B1635135 : Blo 1634016 1635135 := bstep (se 1 (by rfl) ⟨1226351, by rfl⟩ : syracuseStep 1635135 = 2452703) B2452703
theorem B1635163 : Blo 1634016 1635163 := bstep (se 1 (by rfl) ⟨1226372, by rfl⟩ : syracuseStep 1635163 = 2452745) B2452745
theorem B2618249 : Blo 1634016 2618249 := bstep (se 2 (by rfl) ⟨981843, by rfl⟩ : syracuseStep 2618249 = 1963687) B1963687
theorem B1635231 : Blo 1634016 1635231 := bstep (se 1 (by rfl) ⟨1226423, by rfl⟩ : syracuseStep 1635231 = 2452847) B2452847
theorem B8279009 : Blo 1634016 8279009 := bstep (se 2 (by rfl) ⟨3104628, by rfl⟩ : syracuseStep 8279009 = 6209257) B6209257
theorem B1635311 : Blo 1634016 1635311 := bstep (se 1 (by rfl) ⟨1226483, by rfl⟩ : syracuseStep 1635311 = 2452967) B2452967
theorem B1635399 : Blo 1634016 1635399 := bstep (se 1 (by rfl) ⟨1226549, by rfl⟩ : syracuseStep 1635399 = 2453099) B2453099
theorem B1635483 : Blo 1634016 1635483 := bstep (se 1 (by rfl) ⟨1226612, by rfl⟩ : syracuseStep 1635483 = 2453225) B2453225
theorem B1635579 : Blo 1634016 1635579 := bstep (se 1 (by rfl) ⟨1226684, by rfl⟩ : syracuseStep 1635579 = 2453369) B2453369
theorem B1635647 : Blo 1634016 1635647 := bstep (se 1 (by rfl) ⟨1226735, by rfl⟩ : syracuseStep 1635647 = 2453471) B2453471
theorem B6288835 : Blo 1634016 6288835 := bstep (se 1 (by rfl) ⟨4716626, by rfl⟩ : syracuseStep 6288835 = 9433253) B9433253
theorem B1635815 : Blo 1634016 1635815 := bstep (se 1 (by rfl) ⟨1226861, by rfl⟩ : syracuseStep 1635815 = 2453723) B2453723
theorem B1635823 : Blo 1634016 1635823 := bstep (se 1 (by rfl) ⟨1226867, by rfl⟩ : syracuseStep 1635823 = 2453735) B2453735
theorem B1635931 : Blo 1634016 1635931 := bstep (se 1 (by rfl) ⟨1226948, by rfl⟩ : syracuseStep 1635931 = 2453897) B2453897
theorem B5895791 : Blo 1634016 5895791 := bstep (se 1 (by rfl) ⟨4421843, by rfl⟩ : syracuseStep 5895791 = 8843687) B8843687
theorem B1635995 : Blo 1634016 1635995 := bstep (se 1 (by rfl) ⟨1226996, by rfl⟩ : syracuseStep 1635995 = 2453993) B2453993
theorem B6985399 : Blo 1634016 6985399 := bstep (se 1 (by rfl) ⟨5239049, by rfl⟩ : syracuseStep 6985399 = 10478099) B10478099
theorem B2946799 : Blo 1634016 2946799 := bstep (se 1 (by rfl) ⟨2210099, by rfl⟩ : syracuseStep 2946799 = 4420199) B4420199
theorem B6133567 : Blo 1634016 6133567 := bstep (se 1 (by rfl) ⟨4600175, by rfl⟩ : syracuseStep 6133567 = 9200351) B9200351
theorem B3315539 : Blo 1634016 3315539 := bstep (se 1 (by rfl) ⟨2486654, by rfl⟩ : syracuseStep 3315539 = 4973309) B4973309
theorem B5896135 : Blo 1634016 5896135 := bstep (se 1 (by rfl) ⟨4422101, by rfl⟩ : syracuseStep 5896135 = 8844203) B8844203
theorem B6985673 : Blo 1634016 6985673 := bstep (se 2 (by rfl) ⟨2619627, by rfl⟩ : syracuseStep 6985673 = 5239255) B5239255
theorem B22370255 : Blo 1634016 22370255 := bstep (se 1 (by rfl) ⟨16777691, by rfl⟩ : syracuseStep 22370255 = 33555383) B33555383
theorem B17684561 : Blo 1634016 17684561 := bstep (se 2 (by rfl) ⟨6631710, by rfl⟩ : syracuseStep 17684561 = 13263421) B13263421
theorem B5519609 : Blo 1634016 5519609 := bstep (se 2 (by rfl) ⟨2069853, by rfl⟩ : syracuseStep 5519609 = 4139707) B4139707
theorem B2759143 : Blo 1634016 2759143 := bstep (se 1 (by rfl) ⟨2069357, by rfl⟩ : syracuseStep 2759143 = 4138715) B4138715
theorem B5519879 : Blo 1634016 5519879 := bstep (se 1 (by rfl) ⟨4139909, by rfl⟩ : syracuseStep 5519879 = 8279819) B8279819
theorem B17676953 : Blo 1634016 17676953 := bstep (se 2 (by rfl) ⟨6628857, by rfl⟩ : syracuseStep 17676953 = 13257715) B13257715
theorem B67123883 : Blo 1634016 67123883 := bstep (se 1 (by rfl) ⟨50342912, by rfl⟩ : syracuseStep 67123883 = 100685825) B100685825
theorem B3676985 : Blo 1634016 3676985 := bstep (se 2 (by rfl) ⟨1378869, by rfl⟩ : syracuseStep 3676985 = 2757739) B2757739
theorem B3677039 : Blo 1634016 3677039 := bstep (se 1 (by rfl) ⟨2757779, by rfl⟩ : syracuseStep 3677039 = 5515559) B5515559
theorem B26508217 : Blo 1634016 26508217 := bstep (se 2 (by rfl) ⟨9940581, by rfl⟩ : syracuseStep 26508217 = 19881163) B19881163
theorem B39754739 : Blo 1634016 39754739 := bstep (se 1 (by rfl) ⟨29816054, by rfl⟩ : syracuseStep 39754739 = 59632109) B59632109
theorem B4136143 : Blo 1634016 4136143 := bstep (se 1 (by rfl) ⟨3102107, by rfl⟩ : syracuseStep 4136143 = 6204215) B6204215
theorem B6626603 : Blo 1634016 6626603 := bstep (se 1 (by rfl) ⟨4969952, by rfl⟩ : syracuseStep 6626603 = 9939905) B9939905
theorem B2760007 : Blo 1634016 2760007 := bstep (se 1 (by rfl) ⟨2070005, by rfl⟩ : syracuseStep 2760007 = 4140011) B4140011
theorem B53058989 : Blo 1634016 53058989 := bstep (se 3 (by rfl) ⟨9948560, by rfl⟩ : syracuseStep 53058989 = 19897121) B19897121
theorem B3677615 : Blo 1634016 3677615 := bstep (se 1 (by rfl) ⟨2758211, by rfl⟩ : syracuseStep 3677615 = 5516423) B5516423
theorem B2760169 : Blo 1634016 2760169 := bstep (se 2 (by rfl) ⟨1035063, by rfl⟩ : syracuseStep 2760169 = 2070127) B2070127
theorem B3677687 : Blo 1634016 3677687 := bstep (se 1 (by rfl) ⟨2758265, by rfl⟩ : syracuseStep 3677687 = 5516531) B5516531
theorem B5520959 : Blo 1634016 5520959 := bstep (se 1 (by rfl) ⟨4140719, by rfl⟩ : syracuseStep 5520959 = 8281439) B8281439
theorem B13967275 : Blo 1634016 13967275 := bstep (se 1 (by rfl) ⟨10475456, by rfl⟩ : syracuseStep 13967275 = 20950913) B20950913
theorem B3678407 : Blo 1634016 3678407 := bstep (se 1 (by rfl) ⟨2758805, by rfl⟩ : syracuseStep 3678407 = 5517611) B5517611
theorem B12935417 : Blo 1634016 12935417 := bstep (se 2 (by rfl) ⟨4850781, by rfl⟩ : syracuseStep 12935417 = 9701563) B9701563
theorem B3490103 : Blo 1634016 3490103 := bstep (se 1 (by rfl) ⟨2617577, by rfl⟩ : syracuseStep 3490103 = 5235155) B5235155
theorem B3105145 : Blo 1634016 3105145 := bstep (se 2 (by rfl) ⟨1164429, by rfl⟩ : syracuseStep 3105145 = 2328859) B2328859
theorem B3678587 : Blo 1634016 3678587 := bstep (se 1 (by rfl) ⟨2758940, by rfl⟩ : syracuseStep 3678587 = 5517881) B5517881
theorem B3678857 : Blo 1634016 3678857 := bstep (se 2 (by rfl) ⟨1379571, by rfl⟩ : syracuseStep 3678857 = 2759143) B2759143
theorem B4654255 : Blo 1634016 4654255 := bstep (se 1 (by rfl) ⟨3490691, by rfl⟩ : syracuseStep 4654255 = 6981383) B6981383
theorem B4654415 : Blo 1634016 4654415 := bstep (se 1 (by rfl) ⟨3490811, by rfl⟩ : syracuseStep 4654415 = 6981623) B6981623
theorem B41911667 : Blo 1634016 41911667 := bstep (se 1 (by rfl) ⟨31433750, by rfl⟩ : syracuseStep 41911667 = 62867501) B62867501
theorem B11789707 : Blo 1634016 11789707 := bstep (se 1 (by rfl) ⟨8842280, by rfl⟩ : syracuseStep 11789707 = 17684561) B17684561
theorem B27927989 : Blo 1634016 27927989 := bstep (se 5 (by rfl) ⟨1309124, by rfl⟩ : syracuseStep 27927989 = 2618249) B2618249
theorem B3679739 : Blo 1634016 3679739 := bstep (se 1 (by rfl) ⟨2759804, by rfl⟩ : syracuseStep 3679739 = 5519609) B5519609
theorem B4654655 : Blo 1634016 4654655 := bstep (se 1 (by rfl) ⟨3490991, by rfl⟩ : syracuseStep 4654655 = 6981983) B6981983
theorem B5514857 : Blo 1634016 5514857 := bstep (se 2 (by rfl) ⟨2068071, by rfl⟩ : syracuseStep 5514857 = 4136143) B4136143
theorem B3679919 : Blo 1634016 3679919 := bstep (se 1 (by rfl) ⟨2759939, by rfl⟩ : syracuseStep 3679919 = 5519879) B5519879
theorem B45352709 : Blo 1634016 45352709 := bstep (se 4 (by rfl) ⟨4251816, by rfl⟩ : syracuseStep 45352709 = 8503633) B8503633
theorem B3680009 : Blo 1634016 3680009 := bstep (se 2 (by rfl) ⟨1380003, by rfl⟩ : syracuseStep 3680009 = 2760007) B2760007
theorem B2451323 : Blo 1634016 2451323 := bstep (se 1 (by rfl) ⟨1838492, by rfl⟩ : syracuseStep 2451323 = 3676985) B3676985
theorem B2451359 : Blo 1634016 2451359 := bstep (se 1 (by rfl) ⟨1838519, by rfl⟩ : syracuseStep 2451359 = 3677039) B3677039
theorem B3680225 : Blo 1634016 3680225 := bstep (se 2 (by rfl) ⟨1380084, by rfl⟩ : syracuseStep 3680225 = 2760169) B2760169
theorem B12584969 : Blo 1634016 12584969 := bstep (se 2 (by rfl) ⟨4719363, by rfl⟩ : syracuseStep 12584969 = 9438727) B9438727
theorem B2451593 : Blo 1634016 2451593 := bstep (se 2 (by rfl) ⟨919347, by rfl⟩ : syracuseStep 2451593 = 1838695) B1838695
theorem B4417735 : Blo 1634016 4417735 := bstep (se 1 (by rfl) ⟨3313301, by rfl⟩ : syracuseStep 4417735 = 6626603) B6626603
theorem B4655303 : Blo 1634016 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B2451743 : Blo 1634016 2451743 := bstep (se 1 (by rfl) ⟨1838807, by rfl⟩ : syracuseStep 2451743 = 3677615) B3677615
theorem B2451791 : Blo 1634016 2451791 := bstep (se 1 (by rfl) ⟨1838843, by rfl⟩ : syracuseStep 2451791 = 3677687) B3677687
theorem B3680639 : Blo 1634016 3680639 := bstep (se 1 (by rfl) ⟨2760479, by rfl⟩ : syracuseStep 3680639 = 5520959) B5520959
theorem B8178089 : Blo 1634016 8178089 := bstep (se 2 (by rfl) ⟨3066783, by rfl⟩ : syracuseStep 8178089 = 6133567) B6133567
theorem B2451881 : Blo 1634016 2451881 := bstep (se 2 (by rfl) ⟨919455, by rfl⟩ : syracuseStep 2451881 = 1838911) B1838911
theorem B18623033 : Blo 1634016 18623033 := bstep (se 2 (by rfl) ⟨6983637, by rfl⟩ : syracuseStep 18623033 = 13967275) B13967275
theorem B3492571 : Blo 1634016 3492571 := bstep (se 1 (by rfl) ⟨2619428, by rfl⟩ : syracuseStep 3492571 = 5238857) B5238857
theorem B2452265 : Blo 1634016 2452265 := bstep (se 2 (by rfl) ⟨919599, by rfl⟩ : syracuseStep 2452265 = 1839199) B1839199
theorem B2452475 : Blo 1634016 2452475 := bstep (se 1 (by rfl) ⟨1839356, by rfl⟩ : syracuseStep 2452475 = 3678713) B3678713
theorem B9309239 : Blo 1634016 9309239 := bstep (se 1 (by rfl) ⟨6981929, by rfl⟩ : syracuseStep 9309239 = 13963859) B13963859
theorem B2452535 : Blo 1634016 2452535 := bstep (se 1 (by rfl) ⟨1839401, by rfl⟩ : syracuseStep 2452535 = 3678803) B3678803
theorem B2452655 : Blo 1634016 2452655 := bstep (se 1 (by rfl) ⟨1839491, by rfl⟩ : syracuseStep 2452655 = 3678983) B3678983
theorem B2452715 : Blo 1634016 2452715 := bstep (se 1 (by rfl) ⟨1839536, by rfl⟩ : syracuseStep 2452715 = 3679073) B3679073
theorem B6204701 : Blo 1634016 6204701 := bstep (se 3 (by rfl) ⟨1163381, by rfl⟩ : syracuseStep 6204701 = 2326763) B2326763
theorem B59649331 : Blo 1634016 59649331 := bstep (se 1 (by rfl) ⟨44736998, by rfl⟩ : syracuseStep 59649331 = 89473997) B89473997
theorem B2239903 : Blo 1634016 2239903 := bstep (se 1 (by rfl) ⟨1679927, by rfl⟩ : syracuseStep 2239903 = 3359855) B3359855
theorem B6204883 : Blo 1634016 6204883 := bstep (se 1 (by rfl) ⟨4653662, by rfl⟩ : syracuseStep 6204883 = 9307325) B9307325
theorem B67153475 : Blo 1634016 67153475 := bstep (se 1 (by rfl) ⟨50365106, by rfl⟩ : syracuseStep 67153475 = 100730213) B100730213
theorem B18886355 : Blo 1634016 18886355 := bstep (se 1 (by rfl) ⟨14164766, by rfl⟩ : syracuseStep 18886355 = 28329533) B28329533
theorem B2453375 : Blo 1634016 2453375 := bstep (se 1 (by rfl) ⟨1840031, by rfl⟩ : syracuseStep 2453375 = 3680063) B3680063
theorem B35344289 : Blo 1634016 35344289 := bstep (se 2 (by rfl) ⟨13254108, by rfl⟩ : syracuseStep 35344289 = 26508217) B26508217
theorem B15716261 : Blo 1634016 15716261 := bstep (se 4 (by rfl) ⟨1473399, by rfl⟩ : syracuseStep 15716261 = 2946799) B2946799
theorem B4657115 : Blo 1634016 4657115 := bstep (se 1 (by rfl) ⟨3492836, by rfl⟩ : syracuseStep 4657115 = 6985673) B6985673
theorem B14913503 : Blo 1634016 14913503 := bstep (se 1 (by rfl) ⟨11185127, by rfl⟩ : syracuseStep 14913503 = 22370255) B22370255
theorem B1634335 : Blo 1634016 1634335 := bstep (se 1 (by rfl) ⟨1225751, by rfl⟩ : syracuseStep 1634335 = 2451503) B2451503
theorem B1634511 : Blo 1634016 1634511 := bstep (se 1 (by rfl) ⟨1225883, by rfl⟩ : syracuseStep 1634511 = 2451767) B2451767
theorem B2453711 : Blo 1634016 2453711 := bstep (se 1 (by rfl) ⟨1840283, by rfl⟩ : syracuseStep 2453711 = 3680567) B3680567
theorem B1634631 : Blo 1634016 1634631 := bstep (se 1 (by rfl) ⟨1225973, by rfl⟩ : syracuseStep 1634631 = 2451947) B2451947
theorem B2453831 : Blo 1634016 2453831 := bstep (se 1 (by rfl) ⟨1840373, by rfl⟩ : syracuseStep 2453831 = 3680747) B3680747
theorem B11784635 : Blo 1634016 11784635 := bstep (se 1 (by rfl) ⟨8838476, by rfl⟩ : syracuseStep 11784635 = 17676953) B17676953
theorem B44749255 : Blo 1634016 44749255 := bstep (se 1 (by rfl) ⟨33561941, by rfl⟩ : syracuseStep 44749255 = 67123883) B67123883
theorem B13971923 : Blo 1634016 13971923 := bstep (se 1 (by rfl) ⟨10478942, by rfl⟩ : syracuseStep 13971923 = 20957885) B20957885
theorem B9310697 : Blo 1634016 9310697 := bstep (se 2 (by rfl) ⟨3491511, by rfl⟩ : syracuseStep 9310697 = 6983023) B6983023
theorem B8385113 : Blo 1634016 8385113 := bstep (se 2 (by rfl) ⟨3144417, by rfl⟩ : syracuseStep 8385113 = 6288835) B6288835
theorem B2945819 : Blo 1634016 2945819 := bstep (se 1 (by rfl) ⟨2209364, by rfl⟩ : syracuseStep 2945819 = 4418729) B4418729
theorem B1635099 : Blo 1634016 1635099 := bstep (se 1 (by rfl) ⟨1226324, by rfl⟩ : syracuseStep 1635099 = 2452649) B2452649
theorem B258216781 : Blo 1634016 258216781 := bstep (se 3 (by rfl) ⟨48415646, by rfl⟩ : syracuseStep 258216781 = 96831293) B96831293
theorem B5895127 : Blo 1634016 5895127 := bstep (se 1 (by rfl) ⟨4421345, by rfl⟩ : syracuseStep 5895127 = 8842691) B8842691
theorem B14914529 : Blo 1634016 14914529 := bstep (se 2 (by rfl) ⟨5592948, by rfl⟩ : syracuseStep 14914529 = 11185897) B11185897
theorem B31446053 : Blo 1634016 31446053 := bstep (se 4 (by rfl) ⟨2948067, by rfl⟩ : syracuseStep 31446053 = 5896135) B5896135
theorem B1635375 : Blo 1634016 1635375 := bstep (se 1 (by rfl) ⟨1226531, by rfl⟩ : syracuseStep 1635375 = 2453063) B2453063
theorem B1635495 : Blo 1634016 1635495 := bstep (se 1 (by rfl) ⟨1226621, by rfl⟩ : syracuseStep 1635495 = 2453243) B2453243
theorem B362985047 : Blo 1634016 362985047 := bstep (se 1 (by rfl) ⟨272238785, by rfl⟩ : syracuseStep 362985047 = 544477571) B544477571
theorem B1635943 : Blo 1634016 1635943 := bstep (se 1 (by rfl) ⟨1226957, by rfl⟩ : syracuseStep 1635943 = 2453915) B2453915
theorem B6207101 : Blo 1634016 6207101 := bstep (se 3 (by rfl) ⟨1163831, by rfl⟩ : syracuseStep 6207101 = 2327663) B2327663
theorem B10082177 : Blo 1634016 10082177 := bstep (se 2 (by rfl) ⟨3780816, by rfl⟩ : syracuseStep 10082177 = 7561633) B7561633
theorem B5519339 : Blo 1634016 5519339 := bstep (se 1 (by rfl) ⟨4139504, by rfl⟩ : syracuseStep 5519339 = 8279009) B8279009
theorem B3102761 : Blo 1634016 3102761 := bstep (se 2 (by rfl) ⟨1163535, by rfl⟩ : syracuseStep 3102761 = 2327071) B2327071
theorem B3930527 : Blo 1634016 3930527 := bstep (se 1 (by rfl) ⟨2947895, by rfl⟩ : syracuseStep 3930527 = 5895791) B5895791
theorem B2210359 : Blo 1634016 2210359 := bstep (se 1 (by rfl) ⟨1657769, by rfl⟩ : syracuseStep 2210359 = 3315539) B3315539
theorem B10476175 : Blo 1634016 10476175 := bstep (se 1 (by rfl) ⟨7857131, by rfl⟩ : syracuseStep 10476175 = 15714263) B15714263
theorem B9943697 : Blo 1634016 9943697 := bstep (se 2 (by rfl) ⟨3728886, by rfl⟩ : syracuseStep 9943697 = 7457773) B7457773
theorem B8280791 : Blo 1634016 8280791 := bstep (se 1 (by rfl) ⟨6210593, by rfl⟩ : syracuseStep 8280791 = 12421187) B12421187
theorem B40295393 : Blo 1634016 40295393 := bstep (se 2 (by rfl) ⟨15110772, by rfl⟩ : syracuseStep 40295393 = 30221545) B30221545
theorem B26533129 : Blo 1634016 26533129 := bstep (se 2 (by rfl) ⟨9949923, by rfl⟩ : syracuseStep 26533129 = 19899847) B19899847
theorem B4136255 : Blo 1634016 4136255 := bstep (se 1 (by rfl) ⟨3102191, by rfl⟩ : syracuseStep 4136255 = 6204383) B6204383
theorem B9313865 : Blo 1634016 9313865 := bstep (se 2 (by rfl) ⟨3492699, by rfl⟩ : syracuseStep 9313865 = 6985399) B6985399
theorem B35372659 : Blo 1634016 35372659 := bstep (se 1 (by rfl) ⟨26529494, by rfl⟩ : syracuseStep 35372659 = 53058989) B53058989
theorem B3677867 : Blo 1634016 3677867 := bstep (se 1 (by rfl) ⟨2758400, by rfl⟩ : syracuseStep 3677867 = 5516801) B5516801
theorem B2760527 : Blo 1634016 2760527 := bstep (se 1 (by rfl) ⟨2070395, by rfl⟩ : syracuseStep 2760527 = 4140791) B4140791
theorem B44752763 : Blo 1634016 44752763 := bstep (se 1 (by rfl) ⟨33564572, by rfl⟩ : syracuseStep 44752763 = 67129145) B67129145
theorem B4972457 : Blo 1634016 4972457 := bstep (se 2 (by rfl) ⟨1864671, by rfl⟩ : syracuseStep 4972457 = 3729343) B3729343
theorem B4136903 : Blo 1634016 4136903 := bstep (se 1 (by rfl) ⟨3102677, by rfl⟩ : syracuseStep 4136903 = 6205355) B6205355
theorem B106012637 : Blo 1634016 106012637 := bstep (se 3 (by rfl) ⟨19877369, by rfl⟩ : syracuseStep 106012637 = 39754739) B39754739
theorem B2326735 : Blo 1634016 2326735 := bstep (se 1 (by rfl) ⟨1745051, by rfl⟩ : syracuseStep 2326735 = 3490103) B3490103
theorem B5890313 : Blo 1634016 5890313 := bstep (se 2 (by rfl) ⟨2208867, by rfl⟩ : syracuseStep 5890313 = 4417735) B4417735
theorem B7856423 : Blo 1634016 7856423 := bstep (se 1 (by rfl) ⟨5892317, by rfl⟩ : syracuseStep 7856423 = 11784635) B11784635
theorem B9314615 : Blo 1634016 9314615 := bstep (se 1 (by rfl) ⟨6985961, by rfl⟩ : syracuseStep 9314615 = 13971923) B13971923
theorem B20964035 : Blo 1634016 20964035 := bstep (se 1 (by rfl) ⟨15723026, by rfl⟩ : syracuseStep 20964035 = 31446053) B31446053
theorem B13968233 : Blo 1634016 13968233 := bstep (se 2 (by rfl) ⟨5238087, by rfl⟩ : syracuseStep 13968233 = 10476175) B10476175
theorem B4138067 : Blo 1634016 4138067 := bstep (se 1 (by rfl) ⟨3103550, by rfl⟩ : syracuseStep 4138067 = 6207101) B6207101
theorem B21808237 : Blo 1634016 21808237 := bstep (se 3 (by rfl) ⟨4089044, by rfl⟩ : syracuseStep 21808237 = 8178089) B8178089
theorem B3679559 : Blo 1634016 3679559 := bstep (se 1 (by rfl) ⟨2759669, by rfl⟩ : syracuseStep 3679559 = 5519339) B5519339
theorem B8389979 : Blo 1634016 8389979 := bstep (se 1 (by rfl) ⟨6292484, by rfl⟩ : syracuseStep 8389979 = 12584969) B12584969
theorem B6629131 : Blo 1634016 6629131 := bstep (se 1 (by rfl) ⟨4971848, by rfl⟩ : syracuseStep 6629131 = 9943697) B9943697
theorem B26863595 : Blo 1634016 26863595 := bstep (se 1 (by rfl) ⟨20147696, by rfl⟩ : syracuseStep 26863595 = 40295393) B40295393
theorem B47163545 : Blo 1634016 47163545 := bstep (se 2 (by rfl) ⟨17686329, by rfl⟩ : syracuseStep 47163545 = 35372659) B35372659
theorem B2451911 : Blo 1634016 2451911 := bstep (se 1 (by rfl) ⟨1838933, by rfl⟩ : syracuseStep 2451911 = 3677867) B3677867
theorem B23562859 : Blo 1634016 23562859 := bstep (se 1 (by rfl) ⟨17672144, by rfl⟩ : syracuseStep 23562859 = 35344289) B35344289
theorem B70675091 : Blo 1634016 70675091 := bstep (se 1 (by rfl) ⟨53006318, by rfl⟩ : syracuseStep 70675091 = 106012637) B106012637
theorem B2452271 : Blo 1634016 2452271 := bstep (se 1 (by rfl) ⟨1839203, by rfl⟩ : syracuseStep 2452271 = 3678407) B3678407
theorem B2452391 : Blo 1634016 2452391 := bstep (se 1 (by rfl) ⟨1839293, by rfl⟩ : syracuseStep 2452391 = 3678587) B3678587
theorem B5590075 : Blo 1634016 5590075 := bstep (se 1 (by rfl) ⟨4192556, by rfl⟩ : syracuseStep 5590075 = 8385113) B8385113
theorem B2452571 : Blo 1634016 2452571 := bstep (se 1 (by rfl) ⟨1839428, by rfl⟩ : syracuseStep 2452571 = 3678857) B3678857
theorem B4140193 : Blo 1634016 4140193 := bstep (se 2 (by rfl) ⟨1552572, by rfl⟩ : syracuseStep 4140193 = 3105145) B3105145
theorem B59665673 : Blo 1634016 59665673 := bstep (se 2 (by rfl) ⟨22374627, by rfl⟩ : syracuseStep 59665673 = 44749255) B44749255
theorem B4656761 : Blo 1634016 4656761 := bstep (se 2 (by rfl) ⟨1746285, by rfl⟩ : syracuseStep 4656761 = 3492571) B3492571
theorem B2453159 : Blo 1634016 2453159 := bstep (se 1 (by rfl) ⟨1839869, by rfl⟩ : syracuseStep 2453159 = 3679739) B3679739
theorem B344289041 : Blo 1634016 344289041 := bstep (se 2 (by rfl) ⟨129108390, by rfl⟩ : syracuseStep 344289041 = 258216781) B258216781
theorem B2453279 : Blo 1634016 2453279 := bstep (se 1 (by rfl) ⟨1839959, by rfl⟩ : syracuseStep 2453279 = 3679919) B3679919
theorem B2453339 : Blo 1634016 2453339 := bstep (se 1 (by rfl) ⟨1840004, by rfl⟩ : syracuseStep 2453339 = 3680009) B3680009
theorem B1634215 : Blo 1634016 1634215 := bstep (se 1 (by rfl) ⟨1225661, by rfl⟩ : syracuseStep 1634215 = 2451323) B2451323
theorem B6721451 : Blo 1634016 6721451 := bstep (se 1 (by rfl) ⟨5041088, by rfl⟩ : syracuseStep 6721451 = 10082177) B10082177
theorem B1634239 : Blo 1634016 1634239 := bstep (se 1 (by rfl) ⟨1225679, by rfl⟩ : syracuseStep 1634239 = 2451359) B2451359
theorem B7860169 : Blo 1634016 7860169 := bstep (se 2 (by rfl) ⟨2947563, by rfl⟩ : syracuseStep 7860169 = 5895127) B5895127
theorem B2453483 : Blo 1634016 2453483 := bstep (se 1 (by rfl) ⟨1840112, by rfl⟩ : syracuseStep 2453483 = 3680225) B3680225
theorem B2068507 : Blo 1634016 2068507 := bstep (se 1 (by rfl) ⟨1551380, by rfl⟩ : syracuseStep 2068507 = 3102761) B3102761
theorem B1634395 : Blo 1634016 1634395 := bstep (se 1 (by rfl) ⟨1225796, by rfl⟩ : syracuseStep 1634395 = 2451593) B2451593
theorem B1634495 : Blo 1634016 1634495 := bstep (se 1 (by rfl) ⟨1225871, by rfl⟩ : syracuseStep 1634495 = 2451743) B2451743
theorem B1634527 : Blo 1634016 1634527 := bstep (se 1 (by rfl) ⟨1225895, by rfl⟩ : syracuseStep 1634527 = 2451791) B2451791
theorem B6205673 : Blo 1634016 6205673 := bstep (se 2 (by rfl) ⟨2327127, by rfl⟩ : syracuseStep 6205673 = 4654255) B4654255
theorem B2453759 : Blo 1634016 2453759 := bstep (se 1 (by rfl) ⟨1840319, by rfl⟩ : syracuseStep 2453759 = 3680639) B3680639
theorem B1634587 : Blo 1634016 1634587 := bstep (se 1 (by rfl) ⟨1225940, by rfl⟩ : syracuseStep 1634587 = 2451881) B2451881
theorem B35377505 : Blo 1634016 35377505 := bstep (se 2 (by rfl) ⟨13266564, by rfl⟩ : syracuseStep 35377505 = 26533129) B26533129
theorem B12415355 : Blo 1634016 12415355 := bstep (se 1 (by rfl) ⟨9311516, by rfl⟩ : syracuseStep 12415355 = 18623033) B18623033
theorem B79532441 : Blo 1634016 79532441 := bstep (se 2 (by rfl) ⟨29824665, by rfl⟩ : syracuseStep 79532441 = 59649331) B59649331
theorem B1634843 : Blo 1634016 1634843 := bstep (se 1 (by rfl) ⟨1226132, by rfl⟩ : syracuseStep 1634843 = 2452265) B2452265
theorem B2986537 : Blo 1634016 2986537 := bstep (se 2 (by rfl) ⟨1119951, by rfl⟩ : syracuseStep 2986537 = 2239903) B2239903
theorem B1634983 : Blo 1634016 1634983 := bstep (se 1 (by rfl) ⟨1226237, by rfl⟩ : syracuseStep 1634983 = 2452475) B2452475
theorem B6206159 : Blo 1634016 6206159 := bstep (se 1 (by rfl) ⟨4654619, by rfl⟩ : syracuseStep 6206159 = 9309239) B9309239
theorem B1635023 : Blo 1634016 1635023 := bstep (se 1 (by rfl) ⟨1226267, by rfl⟩ : syracuseStep 1635023 = 2452535) B2452535
theorem B1635103 : Blo 1634016 1635103 := bstep (se 1 (by rfl) ⟨1226327, by rfl⟩ : syracuseStep 1635103 = 2452655) B2452655
theorem B1635143 : Blo 1634016 1635143 := bstep (se 1 (by rfl) ⟨1226357, by rfl⟩ : syracuseStep 1635143 = 2452715) B2452715
theorem B2757503 : Blo 1634016 2757503 := bstep (se 1 (by rfl) ⟨2068127, by rfl⟩ : syracuseStep 2757503 = 4136255) B4136255
theorem B1840351 : Blo 1634016 1840351 := bstep (se 1 (by rfl) ⟨1380263, by rfl⟩ : syracuseStep 1840351 = 2760527) B2760527
theorem B1635583 : Blo 1634016 1635583 := bstep (se 1 (by rfl) ⟨1226687, by rfl⟩ : syracuseStep 1635583 = 2453375) B2453375
theorem B3314971 : Blo 1634016 3314971 := bstep (se 1 (by rfl) ⟨2486228, by rfl⟩ : syracuseStep 3314971 = 4972457) B4972457
theorem B2757935 : Blo 1634016 2757935 := bstep (se 1 (by rfl) ⟨2068451, by rfl⟩ : syracuseStep 2757935 = 4136903) B4136903
theorem B9942335 : Blo 1634016 9942335 := bstep (se 1 (by rfl) ⟨7456751, by rfl⟩ : syracuseStep 9942335 = 14913503) B14913503
theorem B1635807 : Blo 1634016 1635807 := bstep (se 1 (by rfl) ⟨1226855, by rfl⟩ : syracuseStep 1635807 = 2453711) B2453711
theorem B1635887 : Blo 1634016 1635887 := bstep (se 1 (by rfl) ⟨1226915, by rfl⟩ : syracuseStep 1635887 = 2453831) B2453831
theorem B6207131 : Blo 1634016 6207131 := bstep (se 1 (by rfl) ⟨4655348, by rfl⟩ : syracuseStep 6207131 = 9310697) B9310697
theorem B9943019 : Blo 1634016 9943019 := bstep (se 1 (by rfl) ⟨7457264, by rfl⟩ : syracuseStep 9943019 = 14914529) B14914529
theorem B34494445 : Blo 1634016 34494445 := bstep (se 3 (by rfl) ⟨6467708, by rfl⟩ : syracuseStep 34494445 = 12935417) B12935417
theorem B2947145 : Blo 1634016 2947145 := bstep (se 2 (by rfl) ⟨1105179, by rfl⟩ : syracuseStep 2947145 = 2210359) B2210359
theorem B3102943 : Blo 1634016 3102943 := bstep (se 1 (by rfl) ⟨2327207, by rfl⟩ : syracuseStep 3102943 = 4654415) B4654415
theorem B27941111 : Blo 1634016 27941111 := bstep (se 1 (by rfl) ⟨20955833, by rfl⟩ : syracuseStep 27941111 = 41911667) B41911667
theorem B18618659 : Blo 1634016 18618659 := bstep (se 1 (by rfl) ⟨13963994, by rfl⟩ : syracuseStep 18618659 = 27927989) B27927989
theorem B3103103 : Blo 1634016 3103103 := bstep (se 1 (by rfl) ⟨2327327, by rfl⟩ : syracuseStep 3103103 = 4654655) B4654655
theorem B241990031 : Blo 1634016 241990031 := bstep (se 1 (by rfl) ⟨181492523, by rfl⟩ : syracuseStep 241990031 = 362985047) B362985047
theorem B3676571 : Blo 1634016 3676571 := bstep (se 1 (by rfl) ⟨2757428, by rfl⟩ : syracuseStep 3676571 = 5514857) B5514857
theorem B30235139 : Blo 1634016 30235139 := bstep (se 1 (by rfl) ⟨22676354, by rfl⟩ : syracuseStep 30235139 = 45352709) B45352709
theorem B3103535 : Blo 1634016 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B2620351 : Blo 1634016 2620351 := bstep (se 1 (by rfl) ⟨1965263, by rfl⟩ : syracuseStep 2620351 = 3930527) B3930527
theorem B5520527 : Blo 1634016 5520527 := bstep (se 1 (by rfl) ⟨4140395, by rfl⟩ : syracuseStep 5520527 = 8280791) B8280791
theorem B15719609 : Blo 1634016 15719609 := bstep (se 2 (by rfl) ⟨5894853, by rfl⟩ : syracuseStep 15719609 = 11789707) B11789707
theorem B8273177 : Blo 1634016 8273177 := bstep (se 2 (by rfl) ⟨3102441, by rfl⟩ : syracuseStep 8273177 = 6204883) B6204883
theorem B7855517 : Blo 1634016 7855517 := bstep (se 3 (by rfl) ⟨1472909, by rfl⟩ : syracuseStep 7855517 = 2945819) B2945819
theorem B4136467 : Blo 1634016 4136467 := bstep (se 1 (by rfl) ⟨3102350, by rfl⟩ : syracuseStep 4136467 = 6204701) B6204701
theorem B44768983 : Blo 1634016 44768983 := bstep (se 1 (by rfl) ⟨33576737, by rfl⟩ : syracuseStep 44768983 = 67153475) B67153475
theorem B6209243 : Blo 1634016 6209243 := bstep (se 1 (by rfl) ⟨4656932, by rfl⟩ : syracuseStep 6209243 = 9313865) B9313865
theorem B12590903 : Blo 1634016 12590903 := bstep (se 1 (by rfl) ⟨9443177, by rfl⟩ : syracuseStep 12590903 = 18886355) B18886355
theorem B29835175 : Blo 1634016 29835175 := bstep (se 1 (by rfl) ⟨22376381, by rfl⟩ : syracuseStep 29835175 = 44752763) B44752763
theorem B10477507 : Blo 1634016 10477507 := bstep (se 1 (by rfl) ⟨7858130, by rfl⟩ : syracuseStep 10477507 = 15716261) B15716261
theorem B3104743 : Blo 1634016 3104743 := bstep (se 1 (by rfl) ⟨2328557, by rfl⟩ : syracuseStep 3104743 = 4657115) B4657115
theorem B4137115 : Blo 1634016 4137115 := bstep (se 1 (by rfl) ⟨3102836, by rfl⟩ : syracuseStep 4137115 = 6205673) B6205673
theorem B6209743 : Blo 1634016 6209743 := bstep (se 1 (by rfl) ⟨4657307, by rfl⟩ : syracuseStep 6209743 = 9314615) B9314615
theorem B23585003 : Blo 1634016 23585003 := bstep (se 1 (by rfl) ⟨17688752, by rfl⟩ : syracuseStep 23585003 = 35377505) B35377505
theorem B4137257 : Blo 1634016 4137257 := bstep (se 2 (by rfl) ⟨1551471, by rfl⟩ : syracuseStep 4137257 = 3102943) B3102943
theorem B13976023 : Blo 1634016 13976023 := bstep (se 1 (by rfl) ⟨10482017, by rfl⟩ : syracuseStep 13976023 = 20964035) B20964035
theorem B4137439 : Blo 1634016 4137439 := bstep (se 1 (by rfl) ⟨3103079, by rfl⟩ : syracuseStep 4137439 = 6206159) B6206159
theorem B3982049 : Blo 1634016 3982049 := bstep (se 2 (by rfl) ⟨1493268, by rfl⟩ : syracuseStep 3982049 = 2986537) B2986537
theorem B31417145 : Blo 1634016 31417145 := bstep (se 2 (by rfl) ⟨11781429, by rfl⟩ : syracuseStep 31417145 = 23562859) B23562859
theorem B6628223 : Blo 1634016 6628223 := bstep (se 1 (by rfl) ⟨4971167, by rfl⟩ : syracuseStep 6628223 = 9942335) B9942335
theorem B4138087 : Blo 1634016 4138087 := bstep (se 1 (by rfl) ⟨3103565, by rfl⟩ : syracuseStep 4138087 = 6207131) B6207131
theorem B17909063 : Blo 1634016 17909063 := bstep (se 1 (by rfl) ⟨13431797, by rfl⟩ : syracuseStep 17909063 = 26863595) B26863595
theorem B6628679 : Blo 1634016 6628679 := bstep (se 1 (by rfl) ⟨4971509, by rfl⟩ : syracuseStep 6628679 = 9943019) B9943019
theorem B31442363 : Blo 1634016 31442363 := bstep (se 1 (by rfl) ⟨23581772, by rfl⟩ : syracuseStep 31442363 = 47163545) B47163545
theorem B17679845 : Blo 1634016 17679845 := bstep (se 4 (by rfl) ⟨1657485, by rfl⟩ : syracuseStep 17679845 = 3314971) B3314971
theorem B12412439 : Blo 1634016 12412439 := bstep (se 1 (by rfl) ⟨9309329, by rfl⟩ : syracuseStep 12412439 = 18618659) B18618659
theorem B161326687 : Blo 1634016 161326687 := bstep (se 1 (by rfl) ⟨120995015, by rfl⟩ : syracuseStep 161326687 = 241990031) B241990031
theorem B2451047 : Blo 1634016 2451047 := bstep (se 1 (by rfl) ⟨1838285, by rfl⟩ : syracuseStep 2451047 = 3676571) B3676571
theorem B5515289 : Blo 1634016 5515289 := bstep (se 2 (by rfl) ⟨2068233, by rfl⟩ : syracuseStep 5515289 = 4136467) B4136467
theorem B3680351 : Blo 1634016 3680351 := bstep (se 1 (by rfl) ⟨2760263, by rfl⟩ : syracuseStep 3680351 = 5520527) B5520527
theorem B10479739 : Blo 1634016 10479739 := bstep (se 1 (by rfl) ⟨7859804, by rfl⟩ : syracuseStep 10479739 = 15719609) B15719609
theorem B8276093 : Blo 1634016 8276093 := bstep (se 3 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 8276093 = 3103535) B3103535
theorem B5515451 : Blo 1634016 5515451 := bstep (se 1 (by rfl) ⟨4136588, by rfl⟩ : syracuseStep 5515451 = 8273177) B8273177
theorem B5237011 : Blo 1634016 5237011 := bstep (se 1 (by rfl) ⟨3927758, by rfl⟩ : syracuseStep 5237011 = 7855517) B7855517
theorem B4139495 : Blo 1634016 4139495 := bstep (se 1 (by rfl) ⟨3104621, by rfl⟩ : syracuseStep 4139495 = 6209243) B6209243
theorem B229526027 : Blo 1634016 229526027 := bstep (se 1 (by rfl) ⟨172144520, by rfl⟩ : syracuseStep 229526027 = 344289041) B344289041
theorem B13970009 : Blo 1634016 13970009 := bstep (se 2 (by rfl) ⟨5238753, by rfl⟩ : syracuseStep 13970009 = 10477507) B10477507
theorem B10480225 : Blo 1634016 10480225 := bstep (se 2 (by rfl) ⟨3930084, by rfl⟩ : syracuseStep 10480225 = 7860169) B7860169
theorem B4139657 : Blo 1634016 4139657 := bstep (se 2 (by rfl) ⟨1552371, by rfl⟩ : syracuseStep 4139657 = 3104743) B3104743
theorem B45992593 : Blo 1634016 45992593 := bstep (se 2 (by rfl) ⟨17247222, by rfl⟩ : syracuseStep 45992593 = 34494445) B34494445
theorem B3926875 : Blo 1634016 3926875 := bstep (se 1 (by rfl) ⟨2945156, by rfl⟩ : syracuseStep 3926875 = 5890313) B5890313
theorem B7859053 : Blo 1634016 7859053 := bstep (se 3 (by rfl) ⟨1473572, by rfl⟩ : syracuseStep 7859053 = 2947145) B2947145
theorem B5237615 : Blo 1634016 5237615 := bstep (se 1 (by rfl) ⟨3928211, by rfl⟩ : syracuseStep 5237615 = 7856423) B7856423
theorem B8276903 : Blo 1634016 8276903 := bstep (se 1 (by rfl) ⟨6207677, by rfl⟩ : syracuseStep 8276903 = 12415355) B12415355
theorem B53021627 : Blo 1634016 53021627 := bstep (se 1 (by rfl) ⟨39766220, by rfl⟩ : syracuseStep 53021627 = 79532441) B79532441
theorem B1838335 : Blo 1634016 1838335 := bstep (se 1 (by rfl) ⟨1378751, by rfl⟩ : syracuseStep 1838335 = 2757503) B2757503
theorem B1838623 : Blo 1634016 1838623 := bstep (se 1 (by rfl) ⟨1378967, by rfl⟩ : syracuseStep 1838623 = 2757935) B2757935
theorem B2453039 : Blo 1634016 2453039 := bstep (se 1 (by rfl) ⟨1839779, by rfl⟩ : syracuseStep 2453039 = 3679559) B3679559
theorem B3493801 : Blo 1634016 3493801 := bstep (se 2 (by rfl) ⟨1310175, by rfl⟩ : syracuseStep 3493801 = 2620351) B2620351
theorem B29077649 : Blo 1634016 29077649 := bstep (se 2 (by rfl) ⟨10904118, by rfl⟩ : syracuseStep 29077649 = 21808237) B21808237
theorem B2068735 : Blo 1634016 2068735 := bstep (se 1 (by rfl) ⟨1551551, by rfl⟩ : syracuseStep 2068735 = 3103103) B3103103
theorem B2453801 : Blo 1634016 2453801 := bstep (se 2 (by rfl) ⟨920175, by rfl⟩ : syracuseStep 2453801 = 1840351) B1840351
theorem B1634607 : Blo 1634016 1634607 := bstep (se 1 (by rfl) ⟨1225955, by rfl⟩ : syracuseStep 1634607 = 2451911) B2451911
theorem B20156759 : Blo 1634016 20156759 := bstep (se 1 (by rfl) ⟨15117569, by rfl⟩ : syracuseStep 20156759 = 30235139) B30235139
theorem B47116727 : Blo 1634016 47116727 := bstep (se 1 (by rfl) ⟨35337545, by rfl⟩ : syracuseStep 47116727 = 70675091) B70675091
theorem B1634847 : Blo 1634016 1634847 := bstep (se 1 (by rfl) ⟨1226135, by rfl⟩ : syracuseStep 1634847 = 2452271) B2452271
theorem B1634927 : Blo 1634016 1634927 := bstep (se 1 (by rfl) ⟨1226195, by rfl⟩ : syracuseStep 1634927 = 2452391) B2452391
theorem B1635047 : Blo 1634016 1635047 := bstep (se 1 (by rfl) ⟨1226285, by rfl⟩ : syracuseStep 1635047 = 2452571) B2452571
theorem B33575741 : Blo 1634016 33575741 := bstep (se 3 (by rfl) ⟨6295451, by rfl⟩ : syracuseStep 33575741 = 12590903) B12590903
theorem B39777115 : Blo 1634016 39777115 := bstep (se 1 (by rfl) ⟨29832836, by rfl⟩ : syracuseStep 39777115 = 59665673) B59665673
theorem B59691977 : Blo 1634016 59691977 := bstep (se 2 (by rfl) ⟨22384491, by rfl⟩ : syracuseStep 59691977 = 44768983) B44768983
theorem B1635439 : Blo 1634016 1635439 := bstep (se 1 (by rfl) ⟨1226579, by rfl⟩ : syracuseStep 1635439 = 2453159) B2453159
theorem B1635519 : Blo 1634016 1635519 := bstep (se 1 (by rfl) ⟨1226639, by rfl⟩ : syracuseStep 1635519 = 2453279) B2453279
theorem B1635559 : Blo 1634016 1635559 := bstep (se 1 (by rfl) ⟨1226669, by rfl⟩ : syracuseStep 1635559 = 2453339) B2453339
theorem B1635655 : Blo 1634016 1635655 := bstep (se 1 (by rfl) ⟨1226741, by rfl⟩ : syracuseStep 1635655 = 2453483) B2453483
theorem B2758009 : Blo 1634016 2758009 := bstep (se 2 (by rfl) ⟨1034253, by rfl⟩ : syracuseStep 2758009 = 2068507) B2068507
theorem B1635839 : Blo 1634016 1635839 := bstep (se 1 (by rfl) ⟨1226879, by rfl⟩ : syracuseStep 1635839 = 2453759) B2453759
theorem B3102313 : Blo 1634016 3102313 := bstep (se 2 (by rfl) ⟨1163367, by rfl⟩ : syracuseStep 3102313 = 2326735) B2326735
theorem B9312155 : Blo 1634016 9312155 := bstep (se 1 (by rfl) ⟨6984116, by rfl⟩ : syracuseStep 9312155 = 13968233) B13968233
theorem B2758711 : Blo 1634016 2758711 := bstep (se 1 (by rfl) ⟨2069033, by rfl⟩ : syracuseStep 2758711 = 4138067) B4138067
theorem B5593319 : Blo 1634016 5593319 := bstep (se 1 (by rfl) ⟨4194989, by rfl⟩ : syracuseStep 5593319 = 8389979) B8389979
theorem B7453433 : Blo 1634016 7453433 := bstep (se 2 (by rfl) ⟨2795037, by rfl⟩ : syracuseStep 7453433 = 5590075) B5590075
theorem B18627407 : Blo 1634016 18627407 := bstep (se 1 (by rfl) ⟨13970555, by rfl⟩ : syracuseStep 18627407 = 27941111) B27941111
theorem B5520257 : Blo 1634016 5520257 := bstep (se 2 (by rfl) ⟨2070096, by rfl⟩ : syracuseStep 5520257 = 4140193) B4140193
theorem B8838841 : Blo 1634016 8838841 := bstep (se 2 (by rfl) ⟨3314565, by rfl⟩ : syracuseStep 8838841 = 6629131) B6629131
theorem B3104507 : Blo 1634016 3104507 := bstep (se 1 (by rfl) ⟨2328380, by rfl⟩ : syracuseStep 3104507 = 4656761) B4656761
theorem B39780233 : Blo 1634016 39780233 := bstep (se 2 (by rfl) ⟨14917587, by rfl⟩ : syracuseStep 39780233 = 29835175) B29835175
theorem B4480967 : Blo 1634016 4480967 := bstep (se 1 (by rfl) ⟨3360725, by rfl⟩ : syracuseStep 4480967 = 6721451) B6721451
theorem B3678281 : Blo 1634016 3678281 := bstep (se 2 (by rfl) ⟨1379355, by rfl⟩ : syracuseStep 3678281 = 2758711) B2758711
theorem B2654699 : Blo 1634016 2654699 := bstep (se 1 (by rfl) ⟨1991024, by rfl⟩ : syracuseStep 2654699 = 3982049) B3982049
theorem B245293829 : Blo 1634016 245293829 := bstep (se 4 (by rfl) ⟨22996296, by rfl⟩ : syracuseStep 245293829 = 45992593) B45992593
theorem B8274959 : Blo 1634016 8274959 := bstep (se 1 (by rfl) ⟨6206219, by rfl⟩ : syracuseStep 8274959 = 12412439) B12412439
theorem B5235833 : Blo 1634016 5235833 := bstep (se 2 (by rfl) ⟨1963437, by rfl⟩ : syracuseStep 5235833 = 3926875) B3926875
theorem B53036153 : Blo 1634016 53036153 := bstep (se 2 (by rfl) ⟨19888557, by rfl⟩ : syracuseStep 53036153 = 39777115) B39777115
theorem B10478737 : Blo 1634016 10478737 := bstep (se 2 (by rfl) ⟨3929526, by rfl⟩ : syracuseStep 10478737 = 7859053) B7859053
theorem B3728879 : Blo 1634016 3728879 := bstep (se 1 (by rfl) ⟨2796659, by rfl⟩ : syracuseStep 3728879 = 5593319) B5593319
theorem B2451113 : Blo 1634016 2451113 := bstep (se 2 (by rfl) ⟨919167, by rfl⟩ : syracuseStep 2451113 = 1838335) B1838335
theorem B3491743 : Blo 1634016 3491743 := bstep (se 1 (by rfl) ⟨2618807, by rfl⟩ : syracuseStep 3491743 = 5237615) B5237615
theorem B3680171 : Blo 1634016 3680171 := bstep (se 1 (by rfl) ⟨2760128, by rfl⟩ : syracuseStep 3680171 = 5520257) B5520257
theorem B2451497 : Blo 1634016 2451497 := bstep (se 2 (by rfl) ⟨919311, by rfl⟩ : syracuseStep 2451497 = 1838623) B1838623
theorem B26520155 : Blo 1634016 26520155 := bstep (se 1 (by rfl) ⟨19890116, by rfl⟩ : syracuseStep 26520155 = 39780233) B39780233
theorem B19385099 : Blo 1634016 19385099 := bstep (se 1 (by rfl) ⟨14538824, by rfl⟩ : syracuseStep 19385099 = 29077649) B29077649
theorem B15723335 : Blo 1634016 15723335 := bstep (se 1 (by rfl) ⟨11792501, by rfl⟩ : syracuseStep 15723335 = 23585003) B23585003
theorem B5516153 : Blo 1634016 5516153 := bstep (se 2 (by rfl) ⟨2068557, by rfl⟩ : syracuseStep 5516153 = 4137115) B4137115
theorem B13437839 : Blo 1634016 13437839 := bstep (se 1 (by rfl) ⟨10078379, by rfl⟩ : syracuseStep 13437839 = 20156759) B20156759
theorem B31411151 : Blo 1634016 31411151 := bstep (se 1 (by rfl) ⟨23558363, by rfl⟩ : syracuseStep 31411151 = 47116727) B47116727
theorem B6982681 : Blo 1634016 6982681 := bstep (se 2 (by rfl) ⟨2618505, by rfl⟩ : syracuseStep 6982681 = 5237011) B5237011
theorem B22383827 : Blo 1634016 22383827 := bstep (se 1 (by rfl) ⟨16787870, by rfl⟩ : syracuseStep 22383827 = 33575741) B33575741
theorem B4418815 : Blo 1634016 4418815 := bstep (se 1 (by rfl) ⟨3314111, by rfl⟩ : syracuseStep 4418815 = 6628223) B6628223
theorem B5516585 : Blo 1634016 5516585 := bstep (se 2 (by rfl) ⟨2068719, by rfl⟩ : syracuseStep 5516585 = 4137439) B4137439
theorem B11939375 : Blo 1634016 11939375 := bstep (se 1 (by rfl) ⟨8954531, by rfl⟩ : syracuseStep 11939375 = 17909063) B17909063
theorem B4419119 : Blo 1634016 4419119 := bstep (se 1 (by rfl) ⟨3314339, by rfl⟩ : syracuseStep 4419119 = 6628679) B6628679
theorem B1634031 : Blo 1634016 1634031 := bstep (se 1 (by rfl) ⟨1225523, by rfl⟩ : syracuseStep 1634031 = 2451047) B2451047
theorem B2453567 : Blo 1634016 2453567 := bstep (se 1 (by rfl) ⟨1840175, by rfl⟩ : syracuseStep 2453567 = 3680351) B3680351
theorem B5517395 : Blo 1634016 5517395 := bstep (se 1 (by rfl) ⟨4138046, by rfl⟩ : syracuseStep 5517395 = 8276093) B8276093
theorem B5517449 : Blo 1634016 5517449 := bstep (se 2 (by rfl) ⟨2069043, by rfl⟩ : syracuseStep 5517449 = 4138087) B4138087
theorem B4968955 : Blo 1634016 4968955 := bstep (se 1 (by rfl) ⟨3726716, by rfl⟩ : syracuseStep 4968955 = 7453433) B7453433
theorem B5517935 : Blo 1634016 5517935 := bstep (se 1 (by rfl) ⟨4138451, by rfl⟩ : syracuseStep 5517935 = 8276903) B8276903
theorem B8278685 : Blo 1634016 8278685 := bstep (se 3 (by rfl) ⟨1552253, by rfl⟩ : syracuseStep 8278685 = 3104507) B3104507
theorem B215102249 : Blo 1634016 215102249 := bstep (se 2 (by rfl) ⟨80663343, by rfl⟩ : syracuseStep 215102249 = 161326687) B161326687
theorem B11785121 : Blo 1634016 11785121 := bstep (se 2 (by rfl) ⟨4419420, by rfl⟩ : syracuseStep 11785121 = 8838841) B8838841
theorem B1635359 : Blo 1634016 1635359 := bstep (se 1 (by rfl) ⟨1226519, by rfl⟩ : syracuseStep 1635359 = 2453039) B2453039
theorem B4658401 : Blo 1634016 4658401 := bstep (se 2 (by rfl) ⟨1746900, by rfl⟩ : syracuseStep 4658401 = 3493801) B3493801
theorem B2987311 : Blo 1634016 2987311 := bstep (se 1 (by rfl) ⟨2240483, by rfl⟩ : syracuseStep 2987311 = 4480967) B4480967
theorem B13972985 : Blo 1634016 13972985 := bstep (se 2 (by rfl) ⟨5239869, by rfl⟩ : syracuseStep 13972985 = 10479739) B10479739
theorem B2758171 : Blo 1634016 2758171 := bstep (se 1 (by rfl) ⟨2068628, by rfl⟩ : syracuseStep 2758171 = 4137257) B4137257
theorem B1635867 : Blo 1634016 1635867 := bstep (se 1 (by rfl) ⟨1226900, by rfl⟩ : syracuseStep 1635867 = 2453801) B2453801
theorem B8279657 : Blo 1634016 8279657 := bstep (se 2 (by rfl) ⟨3104871, by rfl⟩ : syracuseStep 8279657 = 6209743) B6209743
theorem B2758313 : Blo 1634016 2758313 := bstep (se 2 (by rfl) ⟨1034367, by rfl⟩ : syracuseStep 2758313 = 2068735) B2068735
theorem B20944763 : Blo 1634016 20944763 := bstep (se 1 (by rfl) ⟨15708572, by rfl⟩ : syracuseStep 20944763 = 31417145) B31417145
theorem B18634697 : Blo 1634016 18634697 := bstep (se 2 (by rfl) ⟨6988011, by rfl⟩ : syracuseStep 18634697 = 13976023) B13976023
theorem B39794651 : Blo 1634016 39794651 := bstep (se 1 (by rfl) ⟨29845988, by rfl⟩ : syracuseStep 39794651 = 59691977) B59691977
theorem B13973633 : Blo 1634016 13973633 := bstep (se 2 (by rfl) ⟨5240112, by rfl⟩ : syracuseStep 13973633 = 10480225) B10480225
theorem B20961575 : Blo 1634016 20961575 := bstep (se 1 (by rfl) ⟨15721181, by rfl⟩ : syracuseStep 20961575 = 31442363) B31442363
theorem B11786563 : Blo 1634016 11786563 := bstep (se 1 (by rfl) ⟨8839922, by rfl⟩ : syracuseStep 11786563 = 17679845) B17679845
theorem B6208103 : Blo 1634016 6208103 := bstep (se 1 (by rfl) ⟨4656077, by rfl⟩ : syracuseStep 6208103 = 9312155) B9312155
theorem B3676859 : Blo 1634016 3676859 := bstep (se 1 (by rfl) ⟨2757644, by rfl⟩ : syracuseStep 3676859 = 5515289) B5515289
theorem B3676967 : Blo 1634016 3676967 := bstep (se 1 (by rfl) ⟨2757725, by rfl⟩ : syracuseStep 3676967 = 5515451) B5515451
theorem B2759663 : Blo 1634016 2759663 := bstep (se 1 (by rfl) ⟨2069747, by rfl⟩ : syracuseStep 2759663 = 4139495) B4139495
theorem B153017351 : Blo 1634016 153017351 := bstep (se 1 (by rfl) ⟨114763013, by rfl⟩ : syracuseStep 153017351 = 229526027) B229526027
theorem B9313339 : Blo 1634016 9313339 := bstep (se 1 (by rfl) ⟨6985004, by rfl⟩ : syracuseStep 9313339 = 13970009) B13970009
theorem B2759771 : Blo 1634016 2759771 := bstep (se 1 (by rfl) ⟨2069828, by rfl⟩ : syracuseStep 2759771 = 4139657) B4139657
theorem B3677345 : Blo 1634016 3677345 := bstep (se 2 (by rfl) ⟨1379004, by rfl⟩ : syracuseStep 3677345 = 2758009) B2758009
theorem B12418271 : Blo 1634016 12418271 := bstep (se 1 (by rfl) ⟨9313703, by rfl⟩ : syracuseStep 12418271 = 18627407) B18627407
theorem B35347751 : Blo 1634016 35347751 := bstep (se 1 (by rfl) ⟨26510813, by rfl⟩ : syracuseStep 35347751 = 53021627) B53021627
theorem B4136417 : Blo 1634016 4136417 := bstep (se 2 (by rfl) ⟨1551156, by rfl⟩ : syracuseStep 4136417 = 3102313) B3102313
theorem B3678263 : Blo 1634016 3678263 := bstep (se 1 (by rfl) ⟨2758697, by rfl⟩ : syracuseStep 3678263 = 5517395) B5517395
theorem B3678299 : Blo 1634016 3678299 := bstep (se 1 (by rfl) ⟨2758724, by rfl⟩ : syracuseStep 3678299 = 5517449) B5517449
theorem B3678623 : Blo 1634016 3678623 := bstep (se 1 (by rfl) ⟨2758967, by rfl⟩ : syracuseStep 3678623 = 5517935) B5517935
theorem B163529219 : Blo 1634016 163529219 := bstep (se 1 (by rfl) ⟨122646914, by rfl⟩ : syracuseStep 163529219 = 245293829) B245293829
theorem B143401499 : Blo 1634016 143401499 := bstep (se 1 (by rfl) ⟨107551124, by rfl⟩ : syracuseStep 143401499 = 215102249) B215102249
theorem B7856747 : Blo 1634016 7856747 := bstep (se 1 (by rfl) ⟨5892560, by rfl⟩ : syracuseStep 7856747 = 11785121) B11785121
theorem B3490555 : Blo 1634016 3490555 := bstep (se 1 (by rfl) ⟨2617916, by rfl⟩ : syracuseStep 3490555 = 5235833) B5235833
theorem B35357435 : Blo 1634016 35357435 := bstep (se 1 (by rfl) ⟨26518076, by rfl⟩ : syracuseStep 35357435 = 53036153) B53036153
theorem B9315323 : Blo 1634016 9315323 := bstep (se 1 (by rfl) ⟨6986492, by rfl⟩ : syracuseStep 9315323 = 13972985) B13972985
theorem B9315755 : Blo 1634016 9315755 := bstep (se 1 (by rfl) ⟨6986816, by rfl⟩ : syracuseStep 9315755 = 13973633) B13973633
theorem B6211201 : Blo 1634016 6211201 := bstep (se 2 (by rfl) ⟨2329200, by rfl⟩ : syracuseStep 6211201 = 4658401) B4658401
theorem B5891753 : Blo 1634016 5891753 := bstep (se 2 (by rfl) ⟨2209407, by rfl⟩ : syracuseStep 5891753 = 4418815) B4418815
theorem B17680103 : Blo 1634016 17680103 := bstep (se 1 (by rfl) ⟨13260077, by rfl⟩ : syracuseStep 17680103 = 26520155) B26520155
theorem B4138735 : Blo 1634016 4138735 := bstep (se 1 (by rfl) ⟨3104051, by rfl⟩ : syracuseStep 4138735 = 6208103) B6208103
theorem B2451239 : Blo 1634016 2451239 := bstep (se 1 (by rfl) ⟨1838429, by rfl⟩ : syracuseStep 2451239 = 3676859) B3676859
theorem B2451311 : Blo 1634016 2451311 := bstep (se 1 (by rfl) ⟨1838483, by rfl⟩ : syracuseStep 2451311 = 3676967) B3676967
theorem B20940767 : Blo 1634016 20940767 := bstep (se 1 (by rfl) ⟨15705575, by rfl⟩ : syracuseStep 20940767 = 31411151) B31411151
theorem B2451563 : Blo 1634016 2451563 := bstep (se 1 (by rfl) ⟨1838672, by rfl⟩ : syracuseStep 2451563 = 3677345) B3677345
theorem B35834237 : Blo 1634016 35834237 := bstep (se 3 (by rfl) ⟨6718919, by rfl⟩ : syracuseStep 35834237 = 13437839) B13437839
theorem B4655657 : Blo 1634016 4655657 := bstep (se 2 (by rfl) ⟨1745871, by rfl⟩ : syracuseStep 4655657 = 3491743) B3491743
theorem B2452187 : Blo 1634016 2452187 := bstep (se 1 (by rfl) ⟨1839140, by rfl⟩ : syracuseStep 2452187 = 3678281) B3678281
theorem B15715417 : Blo 1634016 15715417 := bstep (se 2 (by rfl) ⟨5893281, by rfl⟩ : syracuseStep 15715417 = 11786563) B11786563
theorem B5516639 : Blo 1634016 5516639 := bstep (se 1 (by rfl) ⟨4137479, by rfl⟩ : syracuseStep 5516639 = 8274959) B8274959
theorem B63729301 : Blo 1634016 63729301 := bstep (se 6 (by rfl) ⟨1493655, by rfl⟩ : syracuseStep 63729301 = 2987311) B2987311
theorem B2485919 : Blo 1634016 2485919 := bstep (se 1 (by rfl) ⟨1864439, by rfl⟩ : syracuseStep 2485919 = 3728879) B3728879
theorem B1634075 : Blo 1634016 1634075 := bstep (se 1 (by rfl) ⟨1225556, by rfl⟩ : syracuseStep 1634075 = 2451113) B2451113
theorem B1838875 : Blo 1634016 1838875 := bstep (se 1 (by rfl) ⟨1379156, by rfl⟩ : syracuseStep 1838875 = 2758313) B2758313
theorem B13963175 : Blo 1634016 13963175 := bstep (se 1 (by rfl) ⟨10472381, by rfl⟩ : syracuseStep 13963175 = 20944763) B20944763
theorem B2453447 : Blo 1634016 2453447 := bstep (se 1 (by rfl) ⟨1840085, by rfl⟩ : syracuseStep 2453447 = 3680171) B3680171
theorem B12423131 : Blo 1634016 12423131 := bstep (se 1 (by rfl) ⟨9317348, by rfl⟩ : syracuseStep 12423131 = 18634697) B18634697
theorem B26529767 : Blo 1634016 26529767 := bstep (se 1 (by rfl) ⟨19897325, by rfl⟩ : syracuseStep 26529767 = 39794651) B39794651
theorem B1634331 : Blo 1634016 1634331 := bstep (se 1 (by rfl) ⟨1225748, by rfl⟩ : syracuseStep 1634331 = 2451497) B2451497
theorem B9310241 : Blo 1634016 9310241 := bstep (se 2 (by rfl) ⟨3491340, by rfl⟩ : syracuseStep 9310241 = 6982681) B6982681
theorem B13971649 : Blo 1634016 13971649 := bstep (se 2 (by rfl) ⟨5239368, by rfl⟩ : syracuseStep 13971649 = 10478737) B10478737
theorem B12923399 : Blo 1634016 12923399 := bstep (se 1 (by rfl) ⟨9692549, by rfl⟩ : syracuseStep 12923399 = 19385099) B19385099
theorem B10482223 : Blo 1634016 10482223 := bstep (se 1 (by rfl) ⟨7861667, by rfl⟩ : syracuseStep 10482223 = 15723335) B15723335
theorem B1839775 : Blo 1634016 1839775 := bstep (se 1 (by rfl) ⟨1379831, by rfl⟩ : syracuseStep 1839775 = 2759663) B2759663
theorem B102011567 : Blo 1634016 102011567 := bstep (se 1 (by rfl) ⟨76508675, by rfl⟩ : syracuseStep 102011567 = 153017351) B153017351
theorem B1839847 : Blo 1634016 1839847 := bstep (se 1 (by rfl) ⟨1379885, by rfl⟩ : syracuseStep 1839847 = 2759771) B2759771
theorem B14922551 : Blo 1634016 14922551 := bstep (se 1 (by rfl) ⟨11191913, by rfl⟩ : syracuseStep 14922551 = 22383827) B22383827
theorem B8278847 : Blo 1634016 8278847 := bstep (se 1 (by rfl) ⟨6209135, by rfl⟩ : syracuseStep 8278847 = 12418271) B12418271
theorem B23565167 : Blo 1634016 23565167 := bstep (se 1 (by rfl) ⟨17673875, by rfl⟩ : syracuseStep 23565167 = 35347751) B35347751
theorem B2757611 : Blo 1634016 2757611 := bstep (se 1 (by rfl) ⟨2068208, by rfl⟩ : syracuseStep 2757611 = 4136417) B4136417
theorem B7959583 : Blo 1634016 7959583 := bstep (se 1 (by rfl) ⟨5969687, by rfl⟩ : syracuseStep 7959583 = 11939375) B11939375
theorem B2946079 : Blo 1634016 2946079 := bstep (se 1 (by rfl) ⟨2209559, by rfl⟩ : syracuseStep 2946079 = 4419119) B4419119
theorem B28316789 : Blo 1634016 28316789 := bstep (se 5 (by rfl) ⟨1327349, by rfl⟩ : syracuseStep 28316789 = 2654699) B2654699
theorem B1635711 : Blo 1634016 1635711 := bstep (se 1 (by rfl) ⟨1226783, by rfl⟩ : syracuseStep 1635711 = 2453567) B2453567
theorem B5519123 : Blo 1634016 5519123 := bstep (se 1 (by rfl) ⟨4139342, by rfl⟩ : syracuseStep 5519123 = 8278685) B8278685
theorem B6625273 : Blo 1634016 6625273 := bstep (se 2 (by rfl) ⟨2484477, by rfl⟩ : syracuseStep 6625273 = 4968955) B4968955
theorem B5519771 : Blo 1634016 5519771 := bstep (se 1 (by rfl) ⟨4139828, by rfl⟩ : syracuseStep 5519771 = 8279657) B8279657
theorem B12417785 : Blo 1634016 12417785 := bstep (se 2 (by rfl) ⟨4656669, by rfl⟩ : syracuseStep 12417785 = 9313339) B9313339
theorem B13974383 : Blo 1634016 13974383 := bstep (se 1 (by rfl) ⟨10480787, by rfl⟩ : syracuseStep 13974383 = 20961575) B20961575
theorem B3677435 : Blo 1634016 3677435 := bstep (se 1 (by rfl) ⟨2758076, by rfl⟩ : syracuseStep 3677435 = 5516153) B5516153
theorem B3677561 : Blo 1634016 3677561 := bstep (se 2 (by rfl) ⟨1379085, by rfl⟩ : syracuseStep 3677561 = 2758171) B2758171
theorem B3677723 : Blo 1634016 3677723 := bstep (se 1 (by rfl) ⟨2758292, by rfl⟩ : syracuseStep 3677723 = 5516585) B5516585
theorem B18628865 : Blo 1634016 18628865 := bstep (se 2 (by rfl) ⟨6985824, by rfl⟩ : syracuseStep 18628865 = 13971649) B13971649
theorem B109019479 : Blo 1634016 109019479 := bstep (se 1 (by rfl) ⟨81764609, by rfl⟩ : syracuseStep 109019479 = 163529219) B163529219
theorem B95600999 : Blo 1634016 95600999 := bstep (se 1 (by rfl) ⟨71700749, by rfl⟩ : syracuseStep 95600999 = 143401499) B143401499
theorem B6210215 : Blo 1634016 6210215 := bstep (se 1 (by rfl) ⟨4657661, by rfl⟩ : syracuseStep 6210215 = 9315323) B9315323
theorem B13976297 : Blo 1634016 13976297 := bstep (se 2 (by rfl) ⟨5241111, by rfl⟩ : syracuseStep 13976297 = 10482223) B10482223
theorem B6210503 : Blo 1634016 6210503 := bstep (se 1 (by rfl) ⟨4657877, by rfl⟩ : syracuseStep 6210503 = 9315755) B9315755
theorem B4654073 : Blo 1634016 4654073 := bstep (se 2 (by rfl) ⟨1745277, by rfl⟩ : syracuseStep 4654073 = 3490555) B3490555
theorem B3679415 : Blo 1634016 3679415 := bstep (se 1 (by rfl) ⟨2759561, by rfl⟩ : syracuseStep 3679415 = 5519123) B5519123
theorem B13960511 : Blo 1634016 13960511 := bstep (se 1 (by rfl) ⟨10470383, by rfl⟩ : syracuseStep 13960511 = 20940767) B20940767
theorem B23889491 : Blo 1634016 23889491 := bstep (se 1 (by rfl) ⟨17917118, by rfl⟩ : syracuseStep 23889491 = 35834237) B35834237
theorem B3679847 : Blo 1634016 3679847 := bstep (se 1 (by rfl) ⟨2759885, by rfl⟩ : syracuseStep 3679847 = 5519771) B5519771
theorem B9316255 : Blo 1634016 9316255 := bstep (se 1 (by rfl) ⟨6987191, by rfl⟩ : syracuseStep 9316255 = 13974383) B13974383
theorem B2451623 : Blo 1634016 2451623 := bstep (se 1 (by rfl) ⟨1838717, by rfl⟩ : syracuseStep 2451623 = 3677435) B3677435
theorem B2451707 : Blo 1634016 2451707 := bstep (se 1 (by rfl) ⟨1838780, by rfl⟩ : syracuseStep 2451707 = 3677561) B3677561
theorem B2451815 : Blo 1634016 2451815 := bstep (se 1 (by rfl) ⟨1838861, by rfl⟩ : syracuseStep 2451815 = 3677723) B3677723
theorem B2451833 : Blo 1634016 2451833 := bstep (se 2 (by rfl) ⟨919437, by rfl⟩ : syracuseStep 2451833 = 1838875) B1838875
theorem B1657279 : Blo 1634016 1657279 := bstep (se 1 (by rfl) ⟨1242959, by rfl⟩ : syracuseStep 1657279 = 2485919) B2485919
theorem B9308783 : Blo 1634016 9308783 := bstep (se 1 (by rfl) ⟨6981587, by rfl⟩ : syracuseStep 9308783 = 13963175) B13963175
theorem B8833697 : Blo 1634016 8833697 := bstep (se 2 (by rfl) ⟨3312636, by rfl⟩ : syracuseStep 8833697 = 6625273) B6625273
theorem B2452175 : Blo 1634016 2452175 := bstep (se 1 (by rfl) ⟨1839131, by rfl⟩ : syracuseStep 2452175 = 3678263) B3678263
theorem B2452199 : Blo 1634016 2452199 := bstep (se 1 (by rfl) ⟨1839149, by rfl⟩ : syracuseStep 2452199 = 3678299) B3678299
theorem B2452415 : Blo 1634016 2452415 := bstep (se 1 (by rfl) ⟨1839311, by rfl⟩ : syracuseStep 2452415 = 3678623) B3678623
theorem B5237831 : Blo 1634016 5237831 := bstep (se 1 (by rfl) ⟨3928373, by rfl⟩ : syracuseStep 5237831 = 7856747) B7856747
theorem B23571623 : Blo 1634016 23571623 := bstep (se 1 (by rfl) ⟨17678717, by rfl⟩ : syracuseStep 23571623 = 35357435) B35357435
theorem B9948367 : Blo 1634016 9948367 := bstep (se 1 (by rfl) ⟨7461275, by rfl⟩ : syracuseStep 9948367 = 14922551) B14922551
theorem B1838407 : Blo 1634016 1838407 := bstep (se 1 (by rfl) ⟨1378805, by rfl⟩ : syracuseStep 1838407 = 2757611) B2757611
theorem B18877859 : Blo 1634016 18877859 := bstep (se 1 (by rfl) ⟨14158394, by rfl⟩ : syracuseStep 18877859 = 28316789) B28316789
theorem B2453033 : Blo 1634016 2453033 := bstep (se 2 (by rfl) ⟨919887, by rfl⟩ : syracuseStep 2453033 = 1839775) B1839775
theorem B2453129 : Blo 1634016 2453129 := bstep (se 2 (by rfl) ⟨919923, by rfl⟩ : syracuseStep 2453129 = 1839847) B1839847
theorem B3927835 : Blo 1634016 3927835 := bstep (se 1 (by rfl) ⟨2945876, by rfl⟩ : syracuseStep 3927835 = 5891753) B5891753
theorem B1634159 : Blo 1634016 1634159 := bstep (se 1 (by rfl) ⟨1225619, by rfl⟩ : syracuseStep 1634159 = 2451239) B2451239
theorem B1634207 : Blo 1634016 1634207 := bstep (se 1 (by rfl) ⟨1225655, by rfl⟩ : syracuseStep 1634207 = 2451311) B2451311
theorem B10612777 : Blo 1634016 10612777 := bstep (se 2 (by rfl) ⟨3979791, by rfl⟩ : syracuseStep 10612777 = 7959583) B7959583
theorem B3928105 : Blo 1634016 3928105 := bstep (se 2 (by rfl) ⟨1473039, by rfl⟩ : syracuseStep 3928105 = 2946079) B2946079
theorem B1634375 : Blo 1634016 1634375 := bstep (se 1 (by rfl) ⟨1225781, by rfl⟩ : syracuseStep 1634375 = 2451563) B2451563
theorem B1634791 : Blo 1634016 1634791 := bstep (se 1 (by rfl) ⟨1226093, by rfl⟩ : syracuseStep 1634791 = 2452187) B2452187
theorem B8278523 : Blo 1634016 8278523 := bstep (se 1 (by rfl) ⟨6208892, by rfl⟩ : syracuseStep 8278523 = 12417785) B12417785
theorem B84972401 : Blo 1634016 84972401 := bstep (se 2 (by rfl) ⟨31864650, by rfl⟩ : syracuseStep 84972401 = 63729301) B63729301
theorem B5518313 : Blo 1634016 5518313 := bstep (se 2 (by rfl) ⟨2069367, by rfl⟩ : syracuseStep 5518313 = 4138735) B4138735
theorem B1635631 : Blo 1634016 1635631 := bstep (se 1 (by rfl) ⟨1226723, by rfl⟩ : syracuseStep 1635631 = 2453447) B2453447
theorem B6206827 : Blo 1634016 6206827 := bstep (se 1 (by rfl) ⟨4655120, by rfl⟩ : syracuseStep 6206827 = 9310241) B9310241
theorem B8615599 : Blo 1634016 8615599 := bstep (se 1 (by rfl) ⟨6461699, by rfl⟩ : syracuseStep 8615599 = 12923399) B12923399
theorem B5519231 : Blo 1634016 5519231 := bstep (se 1 (by rfl) ⟨4139423, by rfl⟩ : syracuseStep 5519231 = 8278847) B8278847
theorem B15710111 : Blo 1634016 15710111 := bstep (se 1 (by rfl) ⟨11782583, by rfl⟩ : syracuseStep 15710111 = 23565167) B23565167
theorem B11786735 : Blo 1634016 11786735 := bstep (se 1 (by rfl) ⟨8840051, by rfl⟩ : syracuseStep 11786735 = 17680103) B17680103
theorem B20953889 : Blo 1634016 20953889 := bstep (se 2 (by rfl) ⟨7857708, by rfl⟩ : syracuseStep 20953889 = 15715417) B15715417
theorem B3103771 : Blo 1634016 3103771 := bstep (se 1 (by rfl) ⟨2327828, by rfl⟩ : syracuseStep 3103771 = 4655657) B4655657
theorem B272030845 : Blo 1634016 272030845 := bstep (se 3 (by rfl) ⟨51005783, by rfl⟩ : syracuseStep 272030845 = 102011567) B102011567
theorem B8281601 : Blo 1634016 8281601 := bstep (se 2 (by rfl) ⟨3105600, by rfl⟩ : syracuseStep 8281601 = 6211201) B6211201
theorem B3677759 : Blo 1634016 3677759 := bstep (se 1 (by rfl) ⟨2758319, by rfl⟩ : syracuseStep 3677759 = 5516639) B5516639
theorem B8282087 : Blo 1634016 8282087 := bstep (se 1 (by rfl) ⟨6211565, by rfl⟩ : syracuseStep 8282087 = 12423131) B12423131
theorem B17686511 : Blo 1634016 17686511 := bstep (se 1 (by rfl) ⟨13264883, by rfl⟩ : syracuseStep 17686511 = 26529767) B26529767
theorem B12419243 : Blo 1634016 12419243 := bstep (se 1 (by rfl) ⟨9314432, by rfl⟩ : syracuseStep 12419243 = 18628865) B18628865
theorem B13967549 : Blo 1634016 13967549 := bstep (se 3 (by rfl) ⟨2618915, by rfl⟩ : syracuseStep 13967549 = 5237831) B5237831
theorem B63733999 : Blo 1634016 63733999 := bstep (se 1 (by rfl) ⟨47800499, by rfl⟩ : syracuseStep 63733999 = 95600999) B95600999
theorem B145359305 : Blo 1634016 145359305 := bstep (se 2 (by rfl) ⟨54509739, by rfl⟩ : syracuseStep 145359305 = 109019479) B109019479
theorem B56648267 : Blo 1634016 56648267 := bstep (se 1 (by rfl) ⟨42486200, by rfl⟩ : syracuseStep 56648267 = 84972401) B84972401
theorem B3678875 : Blo 1634016 3678875 := bstep (se 1 (by rfl) ⟨2759156, by rfl⟩ : syracuseStep 3678875 = 5518313) B5518313
theorem B9307007 : Blo 1634016 9307007 := bstep (se 1 (by rfl) ⟨6980255, by rfl⟩ : syracuseStep 9307007 = 13960511) B13960511
theorem B45949861 : Blo 1634016 45949861 := bstep (se 4 (by rfl) ⟨4307799, by rfl⟩ : syracuseStep 45949861 = 8615599) B8615599
theorem B15926327 : Blo 1634016 15926327 := bstep (se 1 (by rfl) ⟨11944745, by rfl⟩ : syracuseStep 15926327 = 23889491) B23889491
theorem B3679487 : Blo 1634016 3679487 := bstep (se 1 (by rfl) ⟨2759615, by rfl⟩ : syracuseStep 3679487 = 5519231) B5519231
theorem B4138361 : Blo 1634016 4138361 := bstep (se 2 (by rfl) ⟨1551885, by rfl⟩ : syracuseStep 4138361 = 3103771) B3103771
theorem B20948453 : Blo 1634016 20948453 := bstep (se 4 (by rfl) ⟨1963917, by rfl⟩ : syracuseStep 20948453 = 3927835) B3927835
theorem B13264489 : Blo 1634016 13264489 := bstep (se 2 (by rfl) ⟨4974183, by rfl⟩ : syracuseStep 13264489 = 9948367) B9948367
theorem B7857823 : Blo 1634016 7857823 := bstep (se 1 (by rfl) ⟨5893367, by rfl⟩ : syracuseStep 7857823 = 11786735) B11786735
theorem B2451209 : Blo 1634016 2451209 := bstep (se 2 (by rfl) ⟨919203, by rfl⟩ : syracuseStep 2451209 = 1838407) B1838407
theorem B8275769 : Blo 1634016 8275769 := bstep (se 2 (by rfl) ⟨3103413, by rfl⟩ : syracuseStep 8275769 = 6206827) B6206827
theorem B13969259 : Blo 1634016 13969259 := bstep (se 1 (by rfl) ⟨10476944, by rfl⟩ : syracuseStep 13969259 = 20953889) B20953889
theorem B15714415 : Blo 1634016 15714415 := bstep (se 1 (by rfl) ⟨11785811, by rfl⟩ : syracuseStep 15714415 = 23571623) B23571623
theorem B12585239 : Blo 1634016 12585239 := bstep (se 1 (by rfl) ⟨9438929, by rfl⟩ : syracuseStep 12585239 = 18877859) B18877859
theorem B2451839 : Blo 1634016 2451839 := bstep (se 1 (by rfl) ⟨1838879, by rfl⟩ : syracuseStep 2451839 = 3677759) B3677759
theorem B12421673 : Blo 1634016 12421673 := bstep (se 2 (by rfl) ⟨4658127, by rfl⟩ : syracuseStep 12421673 = 9316255) B9316255
theorem B11791007 : Blo 1634016 11791007 := bstep (se 1 (by rfl) ⟨8843255, by rfl⟩ : syracuseStep 11791007 = 17686511) B17686511
theorem B14150369 : Blo 1634016 14150369 := bstep (se 2 (by rfl) ⟨5306388, by rfl⟩ : syracuseStep 14150369 = 10612777) B10612777
theorem B5237473 : Blo 1634016 5237473 := bstep (se 2 (by rfl) ⟨1964052, by rfl⟩ : syracuseStep 5237473 = 3928105) B3928105
theorem B4140143 : Blo 1634016 4140143 := bstep (se 1 (by rfl) ⟨3105107, by rfl⟩ : syracuseStep 4140143 = 6210215) B6210215
theorem B9317531 : Blo 1634016 9317531 := bstep (se 1 (by rfl) ⟨6988148, by rfl⟩ : syracuseStep 9317531 = 13976297) B13976297
theorem B4140335 : Blo 1634016 4140335 := bstep (se 1 (by rfl) ⟨3105251, by rfl⟩ : syracuseStep 4140335 = 6210503) B6210503
theorem B2452943 : Blo 1634016 2452943 := bstep (se 1 (by rfl) ⟨1839707, by rfl⟩ : syracuseStep 2452943 = 3679415) B3679415
theorem B2453231 : Blo 1634016 2453231 := bstep (se 1 (by rfl) ⟨1839923, by rfl⟩ : syracuseStep 2453231 = 3679847) B3679847
theorem B10473407 : Blo 1634016 10473407 := bstep (se 1 (by rfl) ⟨7855055, by rfl⟩ : syracuseStep 10473407 = 15710111) B15710111
theorem B1634415 : Blo 1634016 1634415 := bstep (se 1 (by rfl) ⟨1225811, by rfl⟩ : syracuseStep 1634415 = 2451623) B2451623
theorem B1634471 : Blo 1634016 1634471 := bstep (se 1 (by rfl) ⟨1225853, by rfl⟩ : syracuseStep 1634471 = 2451707) B2451707
theorem B1634543 : Blo 1634016 1634543 := bstep (se 1 (by rfl) ⟨1225907, by rfl⟩ : syracuseStep 1634543 = 2451815) B2451815
theorem B1634555 : Blo 1634016 1634555 := bstep (se 1 (by rfl) ⟨1225916, by rfl⟩ : syracuseStep 1634555 = 2451833) B2451833
theorem B6205855 : Blo 1634016 6205855 := bstep (se 1 (by rfl) ⟨4654391, by rfl⟩ : syracuseStep 6205855 = 9308783) B9308783
theorem B1634783 : Blo 1634016 1634783 := bstep (se 1 (by rfl) ⟨1226087, by rfl⟩ : syracuseStep 1634783 = 2452175) B2452175
theorem B1634799 : Blo 1634016 1634799 := bstep (se 1 (by rfl) ⟨1226099, by rfl⟩ : syracuseStep 1634799 = 2452199) B2452199
theorem B1634943 : Blo 1634016 1634943 := bstep (se 1 (by rfl) ⟨1226207, by rfl⟩ : syracuseStep 1634943 = 2452415) B2452415
theorem B1635355 : Blo 1634016 1635355 := bstep (se 1 (by rfl) ⟨1226516, by rfl⟩ : syracuseStep 1635355 = 2453033) B2453033
theorem B1635419 : Blo 1634016 1635419 := bstep (se 1 (by rfl) ⟨1226564, by rfl⟩ : syracuseStep 1635419 = 2453129) B2453129
theorem B5519015 : Blo 1634016 5519015 := bstep (se 1 (by rfl) ⟨4139261, by rfl⟩ : syracuseStep 5519015 = 8278523) B8278523
theorem B3102715 : Blo 1634016 3102715 := bstep (se 1 (by rfl) ⟨2327036, by rfl⟩ : syracuseStep 3102715 = 4654073) B4654073
theorem B362707793 : Blo 1634016 362707793 := bstep (se 2 (by rfl) ⟨136015422, by rfl⟩ : syracuseStep 362707793 = 272030845) B272030845
theorem B5889131 : Blo 1634016 5889131 := bstep (se 1 (by rfl) ⟨4416848, by rfl⟩ : syracuseStep 5889131 = 8833697) B8833697
theorem B8838821 : Blo 1634016 8838821 := bstep (se 4 (by rfl) ⟨828639, by rfl⟩ : syracuseStep 8838821 = 1657279) B1657279
theorem B5521067 : Blo 1634016 5521067 := bstep (se 1 (by rfl) ⟨4140800, by rfl⟩ : syracuseStep 5521067 = 8281601) B8281601
theorem B5521391 : Blo 1634016 5521391 := bstep (se 1 (by rfl) ⟨4141043, by rfl⟩ : syracuseStep 5521391 = 8282087) B8282087
theorem B37765511 : Blo 1634016 37765511 := bstep (se 1 (by rfl) ⟨28324133, by rfl⟩ : syracuseStep 37765511 = 56648267) B56648267
theorem B8274473 : Blo 1634016 8274473 := bstep (se 2 (by rfl) ⟨3102927, by rfl⟩ : syracuseStep 8274473 = 6205855) B6205855
theorem B10617551 : Blo 1634016 10617551 := bstep (se 1 (by rfl) ⟨7963163, by rfl⟩ : syracuseStep 10617551 = 15926327) B15926327
theorem B3679343 : Blo 1634016 3679343 := bstep (se 1 (by rfl) ⟨2759507, by rfl⟩ : syracuseStep 3679343 = 5519015) B5519015
theorem B8390159 : Blo 1634016 8390159 := bstep (se 1 (by rfl) ⟨6292619, by rfl⟩ : syracuseStep 8390159 = 12585239) B12585239
theorem B23570189 : Blo 1634016 23570189 := bstep (se 3 (by rfl) ⟨4419410, by rfl⟩ : syracuseStep 23570189 = 8838821) B8838821
theorem B241805195 : Blo 1634016 241805195 := bstep (se 1 (by rfl) ⟨181353896, by rfl⟩ : syracuseStep 241805195 = 362707793) B362707793
theorem B3926087 : Blo 1634016 3926087 := bstep (se 1 (by rfl) ⟨2944565, by rfl⟩ : syracuseStep 3926087 = 5889131) B5889131
theorem B6211687 : Blo 1634016 6211687 := bstep (se 1 (by rfl) ⟨4658765, by rfl⟩ : syracuseStep 6211687 = 9317531) B9317531
theorem B245065925 : Blo 1634016 245065925 := bstep (se 4 (by rfl) ⟨22974930, by rfl⟩ : syracuseStep 245065925 = 45949861) B45949861
theorem B3680711 : Blo 1634016 3680711 := bstep (se 1 (by rfl) ⟨2760533, by rfl⟩ : syracuseStep 3680711 = 5521067) B5521067
theorem B6982271 : Blo 1634016 6982271 := bstep (se 1 (by rfl) ⟨5236703, by rfl⟩ : syracuseStep 6982271 = 10473407) B10473407
theorem B3680927 : Blo 1634016 3680927 := bstep (se 1 (by rfl) ⟨2760695, by rfl⟩ : syracuseStep 3680927 = 5521391) B5521391
theorem B96906203 : Blo 1634016 96906203 := bstep (se 1 (by rfl) ⟨72679652, by rfl⟩ : syracuseStep 96906203 = 145359305) B145359305
theorem B84978665 : Blo 1634016 84978665 := bstep (se 2 (by rfl) ⟨31866999, by rfl⟩ : syracuseStep 84978665 = 63733999) B63733999
theorem B2452583 : Blo 1634016 2452583 := bstep (se 1 (by rfl) ⟨1839437, by rfl⟩ : syracuseStep 2452583 = 3678875) B3678875
theorem B6204671 : Blo 1634016 6204671 := bstep (se 1 (by rfl) ⟨4653503, by rfl⟩ : syracuseStep 6204671 = 9307007) B9307007
theorem B2452991 : Blo 1634016 2452991 := bstep (se 1 (by rfl) ⟨1839743, by rfl⟩ : syracuseStep 2452991 = 3679487) B3679487
theorem B6983297 : Blo 1634016 6983297 := bstep (se 2 (by rfl) ⟨2618736, by rfl⟩ : syracuseStep 6983297 = 5237473) B5237473
theorem B1634139 : Blo 1634016 1634139 := bstep (se 1 (by rfl) ⟨1225604, by rfl⟩ : syracuseStep 1634139 = 2451209) B2451209
theorem B5517179 : Blo 1634016 5517179 := bstep (se 1 (by rfl) ⟨4137884, by rfl⟩ : syracuseStep 5517179 = 8275769) B8275769
theorem B1634559 : Blo 1634016 1634559 := bstep (se 1 (by rfl) ⟨1225919, by rfl⟩ : syracuseStep 1634559 = 2451839) B2451839
theorem B7860671 : Blo 1634016 7860671 := bstep (se 1 (by rfl) ⟨5895503, by rfl⟩ : syracuseStep 7860671 = 11791007) B11791007
theorem B9433579 : Blo 1634016 9433579 := bstep (se 1 (by rfl) ⟨7075184, by rfl⟩ : syracuseStep 9433579 = 14150369) B14150369
theorem B1635295 : Blo 1634016 1635295 := bstep (se 1 (by rfl) ⟨1226471, by rfl⟩ : syracuseStep 1635295 = 2452943) B2452943
theorem B1635487 : Blo 1634016 1635487 := bstep (se 1 (by rfl) ⟨1226615, by rfl⟩ : syracuseStep 1635487 = 2453231) B2453231
theorem B8279495 : Blo 1634016 8279495 := bstep (se 1 (by rfl) ⟨6209621, by rfl⟩ : syracuseStep 8279495 = 12419243) B12419243
theorem B9311699 : Blo 1634016 9311699 := bstep (se 1 (by rfl) ⟨6983774, by rfl⟩ : syracuseStep 9311699 = 13967549) B13967549
theorem B20952553 : Blo 1634016 20952553 := bstep (se 2 (by rfl) ⟨7857207, by rfl⟩ : syracuseStep 20952553 = 15714415) B15714415
theorem B2758907 : Blo 1634016 2758907 := bstep (se 1 (by rfl) ⟨2069180, by rfl⟩ : syracuseStep 2758907 = 4138361) B4138361
theorem B13965635 : Blo 1634016 13965635 := bstep (se 1 (by rfl) ⟨10474226, by rfl⟩ : syracuseStep 13965635 = 20948453) B20948453
theorem B9312839 : Blo 1634016 9312839 := bstep (se 1 (by rfl) ⟨6984629, by rfl⟩ : syracuseStep 9312839 = 13969259) B13969259
theorem B8281115 : Blo 1634016 8281115 := bstep (se 1 (by rfl) ⟨6210836, by rfl⟩ : syracuseStep 8281115 = 12421673) B12421673
theorem B2760095 : Blo 1634016 2760095 := bstep (se 1 (by rfl) ⟨2070071, by rfl⟩ : syracuseStep 2760095 = 4140143) B4140143
theorem B17685985 : Blo 1634016 17685985 := bstep (se 2 (by rfl) ⟨6632244, by rfl⟩ : syracuseStep 17685985 = 13264489) B13264489
theorem B2760223 : Blo 1634016 2760223 := bstep (se 1 (by rfl) ⟨2070167, by rfl⟩ : syracuseStep 2760223 = 4140335) B4140335
theorem B10477097 : Blo 1634016 10477097 := bstep (se 2 (by rfl) ⟨3928911, by rfl⟩ : syracuseStep 10477097 = 7857823) B7857823
theorem B4136953 : Blo 1634016 4136953 := bstep (se 2 (by rfl) ⟨1551357, by rfl⟩ : syracuseStep 4136953 = 3102715) B3102715
theorem B8282249 : Blo 1634016 8282249 := bstep (se 2 (by rfl) ⟨3105843, by rfl⟩ : syracuseStep 8282249 = 6211687) B6211687
theorem B7078367 : Blo 1634016 7078367 := bstep (se 1 (by rfl) ⟨5308775, by rfl⟩ : syracuseStep 7078367 = 10617551) B10617551
theorem B15713459 : Blo 1634016 15713459 := bstep (se 1 (by rfl) ⟨11785094, by rfl⟩ : syracuseStep 15713459 = 23570189) B23570189
theorem B161203463 : Blo 1634016 161203463 := bstep (se 1 (by rfl) ⟨120902597, by rfl⟩ : syracuseStep 161203463 = 241805195) B241805195
theorem B4654847 : Blo 1634016 4654847 := bstep (se 1 (by rfl) ⟨3491135, by rfl⟩ : syracuseStep 4654847 = 6982271) B6982271
theorem B27936737 : Blo 1634016 27936737 := bstep (se 2 (by rfl) ⟨10476276, by rfl⟩ : syracuseStep 27936737 = 20952553) B20952553
theorem B64604135 : Blo 1634016 64604135 := bstep (se 1 (by rfl) ⟨48453101, by rfl⟩ : syracuseStep 64604135 = 96906203) B96906203
theorem B3680297 : Blo 1634016 3680297 := bstep (se 2 (by rfl) ⟨1380111, by rfl⟩ : syracuseStep 3680297 = 2760223) B2760223
theorem B4655531 : Blo 1634016 4655531 := bstep (se 1 (by rfl) ⟨3491648, by rfl⟩ : syracuseStep 4655531 = 6983297) B6983297
theorem B5515937 : Blo 1634016 5515937 := bstep (se 2 (by rfl) ⟨2068476, by rfl⟩ : syracuseStep 5515937 = 4136953) B4136953
theorem B25177007 : Blo 1634016 25177007 := bstep (se 1 (by rfl) ⟨18882755, by rfl⟩ : syracuseStep 25177007 = 37765511) B37765511
theorem B5516315 : Blo 1634016 5516315 := bstep (se 1 (by rfl) ⟨4137236, by rfl⟩ : syracuseStep 5516315 = 8274473) B8274473
theorem B12578105 : Blo 1634016 12578105 := bstep (se 2 (by rfl) ⟨4716789, by rfl⟩ : syracuseStep 12578105 = 9433579) B9433579
theorem B2452895 : Blo 1634016 2452895 := bstep (se 1 (by rfl) ⟨1839671, by rfl⟩ : syracuseStep 2452895 = 3679343) B3679343
theorem B2617391 : Blo 1634016 2617391 := bstep (se 1 (by rfl) ⟨1963043, by rfl⟩ : syracuseStep 2617391 = 3926087) B3926087
theorem B163377283 : Blo 1634016 163377283 := bstep (se 1 (by rfl) ⟨122532962, by rfl⟩ : syracuseStep 163377283 = 245065925) B245065925
theorem B1839271 : Blo 1634016 1839271 := bstep (se 1 (by rfl) ⟨1379453, by rfl⟩ : syracuseStep 1839271 = 2758907) B2758907
theorem B9310423 : Blo 1634016 9310423 := bstep (se 1 (by rfl) ⟨6982817, by rfl⟩ : syracuseStep 9310423 = 13965635) B13965635
theorem B2453807 : Blo 1634016 2453807 := bstep (se 1 (by rfl) ⟨1840355, by rfl⟩ : syracuseStep 2453807 = 3680711) B3680711
theorem B2453951 : Blo 1634016 2453951 := bstep (se 1 (by rfl) ⟨1840463, by rfl⟩ : syracuseStep 2453951 = 3680927) B3680927
theorem B23581313 : Blo 1634016 23581313 := bstep (se 2 (by rfl) ⟨8842992, by rfl⟩ : syracuseStep 23581313 = 17685985) B17685985
theorem B56652443 : Blo 1634016 56652443 := bstep (se 1 (by rfl) ⟨42489332, by rfl⟩ : syracuseStep 56652443 = 84978665) B84978665
theorem B1635055 : Blo 1634016 1635055 := bstep (se 1 (by rfl) ⟨1226291, by rfl⟩ : syracuseStep 1635055 = 2452583) B2452583
theorem B1840063 : Blo 1634016 1840063 := bstep (se 1 (by rfl) ⟨1380047, by rfl⟩ : syracuseStep 1840063 = 2760095) B2760095
theorem B1635327 : Blo 1634016 1635327 := bstep (se 1 (by rfl) ⟨1226495, by rfl⟩ : syracuseStep 1635327 = 2452991) B2452991
theorem B6984731 : Blo 1634016 6984731 := bstep (se 1 (by rfl) ⟨5238548, by rfl⟩ : syracuseStep 6984731 = 10477097) B10477097
theorem B5240447 : Blo 1634016 5240447 := bstep (se 1 (by rfl) ⟨3930335, by rfl⟩ : syracuseStep 5240447 = 7860671) B7860671
theorem B5519663 : Blo 1634016 5519663 := bstep (se 1 (by rfl) ⟨4139747, by rfl⟩ : syracuseStep 5519663 = 8279495) B8279495
theorem B6207799 : Blo 1634016 6207799 := bstep (se 1 (by rfl) ⟨4655849, by rfl⟩ : syracuseStep 6207799 = 9311699) B9311699
theorem B5593439 : Blo 1634016 5593439 := bstep (se 1 (by rfl) ⟨4195079, by rfl⟩ : syracuseStep 5593439 = 8390159) B8390159
theorem B6208559 : Blo 1634016 6208559 := bstep (se 1 (by rfl) ⟨4656419, by rfl⟩ : syracuseStep 6208559 = 9312839) B9312839
theorem B5520743 : Blo 1634016 5520743 := bstep (se 1 (by rfl) ⟨4140557, by rfl⟩ : syracuseStep 5520743 = 8281115) B8281115
theorem B4136447 : Blo 1634016 4136447 := bstep (se 1 (by rfl) ⟨3102335, by rfl⟩ : syracuseStep 4136447 = 6204671) B6204671
theorem B3678119 : Blo 1634016 3678119 := bstep (se 1 (by rfl) ⟨2758589, by rfl⟩ : syracuseStep 3678119 = 5517179) B5517179
theorem B5521499 : Blo 1634016 5521499 := bstep (se 1 (by rfl) ⟨4141124, by rfl⟩ : syracuseStep 5521499 = 8282249) B8282249
theorem B6979709 : Blo 1634016 6979709 := bstep (se 3 (by rfl) ⟨1308695, by rfl⟩ : syracuseStep 6979709 = 2617391) B2617391
theorem B4718911 : Blo 1634016 4718911 := bstep (se 1 (by rfl) ⟨3539183, by rfl⟩ : syracuseStep 4718911 = 7078367) B7078367
theorem B15720875 : Blo 1634016 15720875 := bstep (se 1 (by rfl) ⟨11790656, by rfl⟩ : syracuseStep 15720875 = 23581313) B23581313
theorem B3679775 : Blo 1634016 3679775 := bstep (se 1 (by rfl) ⟨2759831, by rfl⟩ : syracuseStep 3679775 = 5519663) B5519663
theorem B3728959 : Blo 1634016 3728959 := bstep (se 1 (by rfl) ⟨2796719, by rfl⟩ : syracuseStep 3728959 = 5593439) B5593439
theorem B12412925 : Blo 1634016 12412925 := bstep (se 3 (by rfl) ⟨2327423, by rfl⟩ : syracuseStep 12412925 = 4654847) B4654847
theorem B4139039 : Blo 1634016 4139039 := bstep (se 1 (by rfl) ⟨3104279, by rfl⟩ : syracuseStep 4139039 = 6208559) B6208559
theorem B3680495 : Blo 1634016 3680495 := bstep (se 1 (by rfl) ⟨2760371, by rfl⟩ : syracuseStep 3680495 = 5520743) B5520743
theorem B2452079 : Blo 1634016 2452079 := bstep (se 1 (by rfl) ⟨1839059, by rfl⟩ : syracuseStep 2452079 = 3678119) B3678119
theorem B217836377 : Blo 1634016 217836377 := bstep (se 2 (by rfl) ⟨81688641, by rfl⟩ : syracuseStep 217836377 = 163377283) B163377283
theorem B2452361 : Blo 1634016 2452361 := bstep (se 2 (by rfl) ⟨919635, by rfl⟩ : syracuseStep 2452361 = 1839271) B1839271
theorem B12413897 : Blo 1634016 12413897 := bstep (se 2 (by rfl) ⟨4655211, by rfl⟩ : syracuseStep 12413897 = 9310423) B9310423
theorem B8277065 : Blo 1634016 8277065 := bstep (se 2 (by rfl) ⟨3103899, by rfl⟩ : syracuseStep 8277065 = 6207799) B6207799
theorem B37768295 : Blo 1634016 37768295 := bstep (se 1 (by rfl) ⟨28326221, by rfl⟩ : syracuseStep 37768295 = 56652443) B56652443
theorem B3493631 : Blo 1634016 3493631 := bstep (se 1 (by rfl) ⟨2620223, by rfl⟩ : syracuseStep 3493631 = 5240447) B5240447
theorem B2453417 : Blo 1634016 2453417 := bstep (se 2 (by rfl) ⟨920031, by rfl⟩ : syracuseStep 2453417 = 1840063) B1840063
theorem B18624491 : Blo 1634016 18624491 := bstep (se 1 (by rfl) ⟨13968368, by rfl⟩ : syracuseStep 18624491 = 27936737) B27936737
theorem B43069423 : Blo 1634016 43069423 := bstep (se 1 (by rfl) ⟨32302067, by rfl⟩ : syracuseStep 43069423 = 64604135) B64604135
theorem B2453531 : Blo 1634016 2453531 := bstep (se 1 (by rfl) ⟨1840148, by rfl⟩ : syracuseStep 2453531 = 3680297) B3680297
theorem B8385403 : Blo 1634016 8385403 := bstep (se 1 (by rfl) ⟨6289052, by rfl⟩ : syracuseStep 8385403 = 12578105) B12578105
theorem B1635263 : Blo 1634016 1635263 := bstep (se 1 (by rfl) ⟨1226447, by rfl⟩ : syracuseStep 1635263 = 2452895) B2452895
theorem B2757631 : Blo 1634016 2757631 := bstep (se 1 (by rfl) ⟨2068223, by rfl⟩ : syracuseStep 2757631 = 4136447) B4136447
theorem B18625949 : Blo 1634016 18625949 := bstep (se 3 (by rfl) ⟨3492365, by rfl⟩ : syracuseStep 18625949 = 6984731) B6984731
theorem B1635871 : Blo 1634016 1635871 := bstep (se 1 (by rfl) ⟨1226903, by rfl⟩ : syracuseStep 1635871 = 2453807) B2453807
theorem B1635967 : Blo 1634016 1635967 := bstep (se 1 (by rfl) ⟨1226975, by rfl⟩ : syracuseStep 1635967 = 2453951) B2453951
theorem B10475639 : Blo 1634016 10475639 := bstep (se 1 (by rfl) ⟨7856729, by rfl⟩ : syracuseStep 10475639 = 15713459) B15713459
theorem B107468975 : Blo 1634016 107468975 := bstep (se 1 (by rfl) ⟨80601731, by rfl⟩ : syracuseStep 107468975 = 161203463) B161203463
theorem B3103687 : Blo 1634016 3103687 := bstep (se 1 (by rfl) ⟨2327765, by rfl⟩ : syracuseStep 3103687 = 4655531) B4655531
theorem B3677291 : Blo 1634016 3677291 := bstep (se 1 (by rfl) ⟨2757968, by rfl⟩ : syracuseStep 3677291 = 5515937) B5515937
theorem B16784671 : Blo 1634016 16784671 := bstep (se 1 (by rfl) ⟨12588503, by rfl⟩ : syracuseStep 16784671 = 25177007) B25177007
theorem B3677543 : Blo 1634016 3677543 := bstep (se 1 (by rfl) ⟨2758157, by rfl⟩ : syracuseStep 3677543 = 5516315) B5516315
theorem B4653139 : Blo 1634016 4653139 := bstep (se 1 (by rfl) ⟨3489854, by rfl⟩ : syracuseStep 4653139 = 6979709) B6979709
theorem B6291881 : Blo 1634016 6291881 := bstep (se 2 (by rfl) ⟨2359455, by rfl⟩ : syracuseStep 6291881 = 4718911) B4718911
theorem B4138249 : Blo 1634016 4138249 := bstep (se 2 (by rfl) ⟨1551843, by rfl⟩ : syracuseStep 4138249 = 3103687) B3103687
theorem B8275283 : Blo 1634016 8275283 := bstep (se 1 (by rfl) ⟨6206462, by rfl⟩ : syracuseStep 8275283 = 12412925) B12412925
theorem B8275931 : Blo 1634016 8275931 := bstep (se 1 (by rfl) ⟨6206948, by rfl⟩ : syracuseStep 8275931 = 12413897) B12413897
theorem B2451527 : Blo 1634016 2451527 := bstep (se 1 (by rfl) ⟨1838645, by rfl⟩ : syracuseStep 2451527 = 3677291) B3677291
theorem B2451695 : Blo 1634016 2451695 := bstep (se 1 (by rfl) ⟨1838771, by rfl⟩ : syracuseStep 2451695 = 3677543) B3677543
theorem B2329087 : Blo 1634016 2329087 := bstep (se 1 (by rfl) ⟨1746815, by rfl⟩ : syracuseStep 2329087 = 3493631) B3493631
theorem B3680999 : Blo 1634016 3680999 := bstep (se 1 (by rfl) ⟨2760749, by rfl⟩ : syracuseStep 3680999 = 5521499) B5521499
theorem B10480583 : Blo 1634016 10480583 := bstep (se 1 (by rfl) ⟨7860437, by rfl⟩ : syracuseStep 10480583 = 15720875) B15720875
theorem B286583933 : Blo 1634016 286583933 := bstep (se 3 (by rfl) ⟨53734487, by rfl⟩ : syracuseStep 286583933 = 107468975) B107468975
theorem B2453183 : Blo 1634016 2453183 := bstep (se 1 (by rfl) ⟨1839887, by rfl⟩ : syracuseStep 2453183 = 3679775) B3679775
theorem B6983759 : Blo 1634016 6983759 := bstep (se 1 (by rfl) ⟨5237819, by rfl⟩ : syracuseStep 6983759 = 10475639) B10475639
theorem B2453663 : Blo 1634016 2453663 := bstep (se 1 (by rfl) ⟨1840247, by rfl⟩ : syracuseStep 2453663 = 3680495) B3680495
theorem B1634719 : Blo 1634016 1634719 := bstep (se 1 (by rfl) ⟨1226039, by rfl⟩ : syracuseStep 1634719 = 2452079) B2452079
theorem B145224251 : Blo 1634016 145224251 := bstep (se 1 (by rfl) ⟨108918188, by rfl⟩ : syracuseStep 145224251 = 217836377) B217836377
theorem B1634907 : Blo 1634016 1634907 := bstep (se 1 (by rfl) ⟨1226180, by rfl⟩ : syracuseStep 1634907 = 2452361) B2452361
theorem B5518043 : Blo 1634016 5518043 := bstep (se 1 (by rfl) ⟨4138532, by rfl⟩ : syracuseStep 5518043 = 8277065) B8277065
theorem B25178863 : Blo 1634016 25178863 := bstep (se 1 (by rfl) ⟨18884147, by rfl⟩ : syracuseStep 25178863 = 37768295) B37768295
theorem B1635611 : Blo 1634016 1635611 := bstep (se 1 (by rfl) ⟨1226708, by rfl⟩ : syracuseStep 1635611 = 2453417) B2453417
theorem B12416327 : Blo 1634016 12416327 := bstep (se 1 (by rfl) ⟨9312245, by rfl⟩ : syracuseStep 12416327 = 18624491) B18624491
theorem B1635687 : Blo 1634016 1635687 := bstep (se 1 (by rfl) ⟨1226765, by rfl⟩ : syracuseStep 1635687 = 2453531) B2453531
theorem B19887781 : Blo 1634016 19887781 := bstep (se 4 (by rfl) ⟨1864479, by rfl⟩ : syracuseStep 19887781 = 3728959) B3728959
theorem B12417299 : Blo 1634016 12417299 := bstep (se 1 (by rfl) ⟨9312974, by rfl⟩ : syracuseStep 12417299 = 18625949) B18625949
theorem B11180537 : Blo 1634016 11180537 := bstep (se 2 (by rfl) ⟨4192701, by rfl⟩ : syracuseStep 11180537 = 8385403) B8385403
theorem B3676841 : Blo 1634016 3676841 := bstep (se 2 (by rfl) ⟨1378815, by rfl⟩ : syracuseStep 3676841 = 2757631) B2757631
theorem B2759359 : Blo 1634016 2759359 := bstep (se 1 (by rfl) ⟨2069519, by rfl⟩ : syracuseStep 2759359 = 4139039) B4139039
theorem B22379561 : Blo 1634016 22379561 := bstep (se 2 (by rfl) ⟨8392335, by rfl⟩ : syracuseStep 22379561 = 16784671) B16784671
theorem B57425897 : Blo 1634016 57425897 := bstep (se 2 (by rfl) ⟨21534711, by rfl⟩ : syracuseStep 57425897 = 43069423) B43069423
theorem B4194587 : Blo 1634016 4194587 := bstep (se 1 (by rfl) ⟨3145940, by rfl⟩ : syracuseStep 4194587 = 6291881) B6291881
theorem B3678695 : Blo 1634016 3678695 := bstep (se 1 (by rfl) ⟨2759021, by rfl⟩ : syracuseStep 3678695 = 5518043) B5518043
theorem B3105449 : Blo 1634016 3105449 := bstep (se 2 (by rfl) ⟨1164543, by rfl⟩ : syracuseStep 3105449 = 2329087) B2329087
theorem B3679145 : Blo 1634016 3679145 := bstep (se 2 (by rfl) ⟨1379679, by rfl⟩ : syracuseStep 3679145 = 2759359) B2759359
theorem B33571817 : Blo 1634016 33571817 := bstep (se 2 (by rfl) ⟨12589431, by rfl⟩ : syracuseStep 33571817 = 25178863) B25178863
theorem B2451227 : Blo 1634016 2451227 := bstep (se 1 (by rfl) ⟨1838420, by rfl⟩ : syracuseStep 2451227 = 3676841) B3676841
theorem B14919707 : Blo 1634016 14919707 := bstep (se 1 (by rfl) ⟨11189780, by rfl⟩ : syracuseStep 14919707 = 22379561) B22379561
theorem B191055955 : Blo 1634016 191055955 := bstep (se 1 (by rfl) ⟨143291966, by rfl⟩ : syracuseStep 191055955 = 286583933) B286583933
theorem B38283931 : Blo 1634016 38283931 := bstep (se 1 (by rfl) ⟨28712948, by rfl⟩ : syracuseStep 38283931 = 57425897) B57425897
theorem B4655839 : Blo 1634016 4655839 := bstep (se 1 (by rfl) ⟨3491879, by rfl⟩ : syracuseStep 4655839 = 6983759) B6983759
theorem B6204185 : Blo 1634016 6204185 := bstep (se 2 (by rfl) ⟨2326569, by rfl⟩ : syracuseStep 6204185 = 4653139) B4653139
theorem B96816167 : Blo 1634016 96816167 := bstep (se 1 (by rfl) ⟨72612125, by rfl⟩ : syracuseStep 96816167 = 145224251) B145224251
theorem B8277551 : Blo 1634016 8277551 := bstep (se 1 (by rfl) ⟨6208163, by rfl⟩ : syracuseStep 8277551 = 12416327) B12416327
theorem B5516855 : Blo 1634016 5516855 := bstep (se 1 (by rfl) ⟨4137641, by rfl⟩ : syracuseStep 5516855 = 8275283) B8275283
theorem B5517287 : Blo 1634016 5517287 := bstep (se 1 (by rfl) ⟨4137965, by rfl⟩ : syracuseStep 5517287 = 8275931) B8275931
theorem B1634351 : Blo 1634016 1634351 := bstep (se 1 (by rfl) ⟨1225763, by rfl⟩ : syracuseStep 1634351 = 2451527) B2451527
theorem B1634463 : Blo 1634016 1634463 := bstep (se 1 (by rfl) ⟨1225847, by rfl⟩ : syracuseStep 1634463 = 2451695) B2451695
theorem B8278199 : Blo 1634016 8278199 := bstep (se 1 (by rfl) ⟨6208649, by rfl⟩ : syracuseStep 8278199 = 12417299) B12417299
theorem B5517665 : Blo 1634016 5517665 := bstep (se 2 (by rfl) ⟨2069124, by rfl⟩ : syracuseStep 5517665 = 4138249) B4138249
theorem B2453999 : Blo 1634016 2453999 := bstep (se 1 (by rfl) ⟨1840499, by rfl⟩ : syracuseStep 2453999 = 3680999) B3680999
theorem B1635455 : Blo 1634016 1635455 := bstep (se 1 (by rfl) ⟨1226591, by rfl⟩ : syracuseStep 1635455 = 2453183) B2453183
theorem B1635775 : Blo 1634016 1635775 := bstep (se 1 (by rfl) ⟨1226831, by rfl⟩ : syracuseStep 1635775 = 2453663) B2453663
theorem B7453691 : Blo 1634016 7453691 := bstep (se 1 (by rfl) ⟨5590268, by rfl⟩ : syracuseStep 7453691 = 11180537) B11180537
theorem B6987055 : Blo 1634016 6987055 := bstep (se 1 (by rfl) ⟨5240291, by rfl⟩ : syracuseStep 6987055 = 10480583) B10480583
theorem B26517041 : Blo 1634016 26517041 := bstep (se 2 (by rfl) ⟨9943890, by rfl⟩ : syracuseStep 26517041 = 19887781) B19887781
theorem B3678443 : Blo 1634016 3678443 := bstep (se 1 (by rfl) ⟨2758832, by rfl⟩ : syracuseStep 3678443 = 5517665) B5517665
theorem B22381211 : Blo 1634016 22381211 := bstep (se 1 (by rfl) ⟨16785908, by rfl⟩ : syracuseStep 22381211 = 33571817) B33571817
theorem B51045241 : Blo 1634016 51045241 := bstep (se 2 (by rfl) ⟨19141965, by rfl⟩ : syracuseStep 51045241 = 38283931) B38283931
theorem B9946471 : Blo 1634016 9946471 := bstep (se 1 (by rfl) ⟨7459853, by rfl⟩ : syracuseStep 9946471 = 14919707) B14919707
theorem B9316073 : Blo 1634016 9316073 := bstep (se 2 (by rfl) ⟨3493527, by rfl⟩ : syracuseStep 9316073 = 6987055) B6987055
theorem B254741273 : Blo 1634016 254741273 := bstep (se 2 (by rfl) ⟨95527977, by rfl⟩ : syracuseStep 254741273 = 191055955) B191055955
theorem B2796391 : Blo 1634016 2796391 := bstep (se 1 (by rfl) ⟨2097293, by rfl⟩ : syracuseStep 2796391 = 4194587) B4194587
theorem B2452463 : Blo 1634016 2452463 := bstep (se 1 (by rfl) ⟨1839347, by rfl⟩ : syracuseStep 2452463 = 3678695) B3678695
theorem B2452763 : Blo 1634016 2452763 := bstep (se 1 (by rfl) ⟨1839572, by rfl⟩ : syracuseStep 2452763 = 3679145) B3679145
theorem B1634151 : Blo 1634016 1634151 := bstep (se 1 (by rfl) ⟨1225613, by rfl⟩ : syracuseStep 1634151 = 2451227) B2451227
theorem B4969127 : Blo 1634016 4969127 := bstep (se 1 (by rfl) ⟨3726845, by rfl⟩ : syracuseStep 4969127 = 7453691) B7453691
theorem B5518367 : Blo 1634016 5518367 := bstep (se 1 (by rfl) ⟨4138775, by rfl⟩ : syracuseStep 5518367 = 8277551) B8277551
theorem B5518799 : Blo 1634016 5518799 := bstep (se 1 (by rfl) ⟨4139099, by rfl⟩ : syracuseStep 5518799 = 8278199) B8278199
theorem B1635999 : Blo 1634016 1635999 := bstep (se 1 (by rfl) ⟨1226999, by rfl⟩ : syracuseStep 1635999 = 2453999) B2453999
theorem B2070299 : Blo 1634016 2070299 := bstep (se 1 (by rfl) ⟨1552724, by rfl⟩ : syracuseStep 2070299 = 3105449) B3105449
theorem B6207785 : Blo 1634016 6207785 := bstep (se 2 (by rfl) ⟨2327919, by rfl⟩ : syracuseStep 6207785 = 4655839) B4655839
theorem B4136123 : Blo 1634016 4136123 := bstep (se 1 (by rfl) ⟨3102092, by rfl⟩ : syracuseStep 4136123 = 6204185) B6204185
theorem B64544111 : Blo 1634016 64544111 := bstep (se 1 (by rfl) ⟨48408083, by rfl⟩ : syracuseStep 64544111 = 96816167) B96816167
theorem B17678027 : Blo 1634016 17678027 := bstep (se 1 (by rfl) ⟨13258520, by rfl⟩ : syracuseStep 17678027 = 26517041) B26517041
theorem B3677903 : Blo 1634016 3677903 := bstep (se 1 (by rfl) ⟨2758427, by rfl⟩ : syracuseStep 3677903 = 5516855) B5516855
theorem B3678191 : Blo 1634016 3678191 := bstep (se 1 (by rfl) ⟨2758643, by rfl⟩ : syracuseStep 3678191 = 5517287) B5517287
theorem B3678911 : Blo 1634016 3678911 := bstep (se 1 (by rfl) ⟨2759183, by rfl⟩ : syracuseStep 3678911 = 5518367) B5518367
theorem B3679199 : Blo 1634016 3679199 := bstep (se 1 (by rfl) ⟨2759399, by rfl⟩ : syracuseStep 3679199 = 5518799) B5518799
theorem B3728521 : Blo 1634016 3728521 := bstep (se 2 (by rfl) ⟨1398195, by rfl⟩ : syracuseStep 3728521 = 2796391) B2796391
theorem B6210715 : Blo 1634016 6210715 := bstep (se 1 (by rfl) ⟨4658036, by rfl⟩ : syracuseStep 6210715 = 9316073) B9316073
theorem B68060321 : Blo 1634016 68060321 := bstep (se 2 (by rfl) ⟨25522620, by rfl⟩ : syracuseStep 68060321 = 51045241) B51045241
theorem B4138523 : Blo 1634016 4138523 := bstep (se 1 (by rfl) ⟨3103892, by rfl⟩ : syracuseStep 4138523 = 6207785) B6207785
theorem B2451935 : Blo 1634016 2451935 := bstep (se 1 (by rfl) ⟨1838951, by rfl⟩ : syracuseStep 2451935 = 3677903) B3677903
theorem B2452127 : Blo 1634016 2452127 := bstep (se 1 (by rfl) ⟨1839095, by rfl⟩ : syracuseStep 2452127 = 3678191) B3678191
theorem B2452295 : Blo 1634016 2452295 := bstep (se 1 (by rfl) ⟨1839221, by rfl⟩ : syracuseStep 2452295 = 3678443) B3678443
theorem B14920807 : Blo 1634016 14920807 := bstep (se 1 (by rfl) ⟨11190605, by rfl⟩ : syracuseStep 14920807 = 22381211) B22381211
theorem B3312751 : Blo 1634016 3312751 := bstep (se 1 (by rfl) ⟨2484563, by rfl⟩ : syracuseStep 3312751 = 4969127) B4969127
theorem B1634975 : Blo 1634016 1634975 := bstep (se 1 (by rfl) ⟨1226231, by rfl⟩ : syracuseStep 1634975 = 2452463) B2452463
theorem B2757415 : Blo 1634016 2757415 := bstep (se 1 (by rfl) ⟨2068061, by rfl⟩ : syracuseStep 2757415 = 4136123) B4136123
theorem B1635175 : Blo 1634016 1635175 := bstep (se 1 (by rfl) ⟨1226381, by rfl⟩ : syracuseStep 1635175 = 2452763) B2452763
theorem B43029407 : Blo 1634016 43029407 := bstep (se 1 (by rfl) ⟨32272055, by rfl⟩ : syracuseStep 43029407 = 64544111) B64544111
theorem B11785351 : Blo 1634016 11785351 := bstep (se 1 (by rfl) ⟨8839013, by rfl⟩ : syracuseStep 11785351 = 17678027) B17678027
theorem B13261961 : Blo 1634016 13261961 := bstep (se 2 (by rfl) ⟨4973235, by rfl⟩ : syracuseStep 13261961 = 9946471) B9946471
theorem B169827515 : Blo 1634016 169827515 := bstep (se 1 (by rfl) ⟨127370636, by rfl⟩ : syracuseStep 169827515 = 254741273) B254741273
theorem B5520797 : Blo 1634016 5520797 := bstep (se 3 (by rfl) ⟨1035149, by rfl⟩ : syracuseStep 5520797 = 2070299) B2070299
theorem B4417001 : Blo 1634016 4417001 := bstep (se 2 (by rfl) ⟨1656375, by rfl⟩ : syracuseStep 4417001 = 3312751) B3312751
theorem B15713801 : Blo 1634016 15713801 := bstep (se 2 (by rfl) ⟨5892675, by rfl⟩ : syracuseStep 15713801 = 11785351) B11785351
theorem B8841307 : Blo 1634016 8841307 := bstep (se 1 (by rfl) ⟨6630980, by rfl⟩ : syracuseStep 8841307 = 13261961) B13261961
theorem B3680531 : Blo 1634016 3680531 := bstep (se 1 (by rfl) ⟨2760398, by rfl⟩ : syracuseStep 3680531 = 5520797) B5520797
theorem B2452607 : Blo 1634016 2452607 := bstep (se 1 (by rfl) ⟨1839455, by rfl⟩ : syracuseStep 2452607 = 3678911) B3678911
theorem B2452799 : Blo 1634016 2452799 := bstep (se 1 (by rfl) ⟨1839599, by rfl⟩ : syracuseStep 2452799 = 3679199) B3679199
theorem B19885445 : Blo 1634016 19885445 := bstep (se 4 (by rfl) ⟨1864260, by rfl⟩ : syracuseStep 19885445 = 3728521) B3728521
theorem B19894409 : Blo 1634016 19894409 := bstep (se 2 (by rfl) ⟨7460403, by rfl⟩ : syracuseStep 19894409 = 14920807) B14920807
theorem B1634623 : Blo 1634016 1634623 := bstep (se 1 (by rfl) ⟨1225967, by rfl⟩ : syracuseStep 1634623 = 2451935) B2451935
theorem B1634751 : Blo 1634016 1634751 := bstep (se 1 (by rfl) ⟨1226063, by rfl⟩ : syracuseStep 1634751 = 2452127) B2452127
theorem B1634863 : Blo 1634016 1634863 := bstep (se 1 (by rfl) ⟨1226147, by rfl⟩ : syracuseStep 1634863 = 2452295) B2452295
theorem B113218343 : Blo 1634016 113218343 := bstep (se 1 (by rfl) ⟨84913757, by rfl⟩ : syracuseStep 113218343 = 169827515) B169827515
theorem B28686271 : Blo 1634016 28686271 := bstep (se 1 (by rfl) ⟨21514703, by rfl⟩ : syracuseStep 28686271 = 43029407) B43029407
theorem B45373547 : Blo 1634016 45373547 := bstep (se 1 (by rfl) ⟨34030160, by rfl⟩ : syracuseStep 45373547 = 68060321) B68060321
theorem B2759015 : Blo 1634016 2759015 := bstep (se 1 (by rfl) ⟨2069261, by rfl⟩ : syracuseStep 2759015 = 4138523) B4138523
theorem B3676553 : Blo 1634016 3676553 := bstep (se 2 (by rfl) ⟨1378707, by rfl⟩ : syracuseStep 3676553 = 2757415) B2757415
theorem B8280953 : Blo 1634016 8280953 := bstep (se 2 (by rfl) ⟨3105357, by rfl⟩ : syracuseStep 8280953 = 6210715) B6210715
theorem B13262939 : Blo 1634016 13262939 := bstep (se 1 (by rfl) ⟨9947204, by rfl⟩ : syracuseStep 13262939 = 19894409) B19894409
theorem B11788409 : Blo 1634016 11788409 := bstep (se 2 (by rfl) ⟨4420653, by rfl⟩ : syracuseStep 11788409 = 8841307) B8841307
theorem B120996125 : Blo 1634016 120996125 := bstep (se 3 (by rfl) ⟨22686773, by rfl⟩ : syracuseStep 120996125 = 45373547) B45373547
theorem B2451035 : Blo 1634016 2451035 := bstep (se 1 (by rfl) ⟨1838276, by rfl⟩ : syracuseStep 2451035 = 3676553) B3676553
theorem B13256963 : Blo 1634016 13256963 := bstep (se 1 (by rfl) ⟨9942722, by rfl⟩ : syracuseStep 13256963 = 19885445) B19885445
theorem B2944667 : Blo 1634016 2944667 := bstep (se 1 (by rfl) ⟨2208500, by rfl⟩ : syracuseStep 2944667 = 4417001) B4417001
theorem B2453687 : Blo 1634016 2453687 := bstep (se 1 (by rfl) ⟨1840265, by rfl⟩ : syracuseStep 2453687 = 3680531) B3680531
theorem B1839343 : Blo 1634016 1839343 := bstep (se 1 (by rfl) ⟨1379507, by rfl⟩ : syracuseStep 1839343 = 2759015) B2759015
theorem B1635071 : Blo 1634016 1635071 := bstep (se 1 (by rfl) ⟨1226303, by rfl⟩ : syracuseStep 1635071 = 2452607) B2452607
theorem B1635199 : Blo 1634016 1635199 := bstep (se 1 (by rfl) ⟨1226399, by rfl⟩ : syracuseStep 1635199 = 2452799) B2452799
theorem B75478895 : Blo 1634016 75478895 := bstep (se 1 (by rfl) ⟨56609171, by rfl⟩ : syracuseStep 75478895 = 113218343) B113218343
theorem B10475867 : Blo 1634016 10475867 := bstep (se 1 (by rfl) ⟨7856900, by rfl⟩ : syracuseStep 10475867 = 15713801) B15713801
theorem B5520635 : Blo 1634016 5520635 := bstep (se 1 (by rfl) ⟨4140476, by rfl⟩ : syracuseStep 5520635 = 8280953) B8280953
theorem B38248361 : Blo 1634016 38248361 := bstep (se 2 (by rfl) ⟨14343135, by rfl⟩ : syracuseStep 38248361 = 28686271) B28686271
theorem B3680423 : Blo 1634016 3680423 := bstep (se 1 (by rfl) ⟨2760317, by rfl⟩ : syracuseStep 3680423 = 5520635) B5520635
theorem B8841959 : Blo 1634016 8841959 := bstep (se 1 (by rfl) ⟨6631469, by rfl⟩ : syracuseStep 8841959 = 13262939) B13262939
theorem B7858939 : Blo 1634016 7858939 := bstep (se 1 (by rfl) ⟨5894204, by rfl⟩ : syracuseStep 7858939 = 11788409) B11788409
theorem B2452457 : Blo 1634016 2452457 := bstep (se 2 (by rfl) ⟨919671, by rfl⟩ : syracuseStep 2452457 = 1839343) B1839343
theorem B1634023 : Blo 1634016 1634023 := bstep (se 1 (by rfl) ⟨1225517, by rfl⟩ : syracuseStep 1634023 = 2451035) B2451035
theorem B50319263 : Blo 1634016 50319263 := bstep (se 1 (by rfl) ⟨37739447, by rfl⟩ : syracuseStep 50319263 = 75478895) B75478895
theorem B6983911 : Blo 1634016 6983911 := bstep (se 1 (by rfl) ⟨5237933, by rfl⟩ : syracuseStep 6983911 = 10475867) B10475867
theorem B1963111 : Blo 1634016 1963111 := bstep (se 1 (by rfl) ⟨1472333, by rfl⟩ : syracuseStep 1963111 = 2944667) B2944667
theorem B25498907 : Blo 1634016 25498907 := bstep (se 1 (by rfl) ⟨19124180, by rfl⟩ : syracuseStep 25498907 = 38248361) B38248361
theorem B1635791 : Blo 1634016 1635791 := bstep (se 1 (by rfl) ⟨1226843, by rfl⟩ : syracuseStep 1635791 = 2453687) B2453687
theorem B80664083 : Blo 1634016 80664083 := bstep (se 1 (by rfl) ⟨60498062, by rfl⟩ : syracuseStep 80664083 = 120996125) B120996125
theorem B8837975 : Blo 1634016 8837975 := bstep (se 1 (by rfl) ⟨6628481, by rfl⟩ : syracuseStep 8837975 = 13256963) B13256963
theorem B16999271 : Blo 1634016 16999271 := bstep (se 1 (by rfl) ⟨12749453, by rfl⟩ : syracuseStep 16999271 = 25498907) B25498907
theorem B10478585 : Blo 1634016 10478585 := bstep (se 2 (by rfl) ⟨3929469, by rfl⟩ : syracuseStep 10478585 = 7858939) B7858939
theorem B5891983 : Blo 1634016 5891983 := bstep (se 1 (by rfl) ⟨4418987, by rfl⟩ : syracuseStep 5891983 = 8837975) B8837975
theorem B53776055 : Blo 1634016 53776055 := bstep (se 1 (by rfl) ⟨40332041, by rfl⟩ : syracuseStep 53776055 = 80664083) B80664083
theorem B2453615 : Blo 1634016 2453615 := bstep (se 1 (by rfl) ⟨1840211, by rfl⟩ : syracuseStep 2453615 = 3680423) B3680423
theorem B2617481 : Blo 1634016 2617481 := bstep (se 2 (by rfl) ⟨981555, by rfl⟩ : syracuseStep 2617481 = 1963111) B1963111
theorem B5894639 : Blo 1634016 5894639 := bstep (se 1 (by rfl) ⟨4420979, by rfl⟩ : syracuseStep 5894639 = 8841959) B8841959
theorem B1634971 : Blo 1634016 1634971 := bstep (se 1 (by rfl) ⟨1226228, by rfl⟩ : syracuseStep 1634971 = 2452457) B2452457
theorem B9311881 : Blo 1634016 9311881 := bstep (se 2 (by rfl) ⟨3491955, by rfl⟩ : syracuseStep 9311881 = 6983911) B6983911
theorem B134184701 : Blo 1634016 134184701 := bstep (se 3 (by rfl) ⟨25159631, by rfl⟩ : syracuseStep 134184701 = 50319263) B50319263
theorem B1744987 : Blo 1634016 1744987 := bstep (se 1 (by rfl) ⟨1308740, by rfl⟩ : syracuseStep 1744987 = 2617481) B2617481
theorem B35850703 : Blo 1634016 35850703 := bstep (se 1 (by rfl) ⟨26888027, by rfl⟩ : syracuseStep 35850703 = 53776055) B53776055
theorem B11332847 : Blo 1634016 11332847 := bstep (se 1 (by rfl) ⟨8499635, by rfl⟩ : syracuseStep 11332847 = 16999271) B16999271
theorem B12415841 : Blo 1634016 12415841 := bstep (se 2 (by rfl) ⟨4655940, by rfl⟩ : syracuseStep 12415841 = 9311881) B9311881
theorem B1635743 : Blo 1634016 1635743 := bstep (se 1 (by rfl) ⟨1226807, by rfl⟩ : syracuseStep 1635743 = 2453615) B2453615
theorem B3929759 : Blo 1634016 3929759 := bstep (se 1 (by rfl) ⟨2947319, by rfl⟩ : syracuseStep 3929759 = 5894639) B5894639
theorem B6985723 : Blo 1634016 6985723 := bstep (se 1 (by rfl) ⟨5239292, by rfl⟩ : syracuseStep 6985723 = 10478585) B10478585
theorem B357825869 : Blo 1634016 357825869 := bstep (se 3 (by rfl) ⟨67092350, by rfl⟩ : syracuseStep 357825869 = 134184701) B134184701
theorem B31423909 : Blo 1634016 31423909 := bstep (se 4 (by rfl) ⟨2945991, by rfl⟩ : syracuseStep 31423909 = 5891983) B5891983
theorem B2326649 : Blo 1634016 2326649 := bstep (se 2 (by rfl) ⟨872493, by rfl⟩ : syracuseStep 2326649 = 1744987) B1744987
theorem B47800937 : Blo 1634016 47800937 := bstep (se 2 (by rfl) ⟨17925351, by rfl⟩ : syracuseStep 47800937 = 35850703) B35850703
theorem B7555231 : Blo 1634016 7555231 := bstep (se 1 (by rfl) ⟨5666423, by rfl⟩ : syracuseStep 7555231 = 11332847) B11332847
theorem B8277227 : Blo 1634016 8277227 := bstep (se 1 (by rfl) ⟨6207920, by rfl⟩ : syracuseStep 8277227 = 12415841) B12415841
theorem B9314297 : Blo 1634016 9314297 := bstep (se 2 (by rfl) ⟨3492861, by rfl⟩ : syracuseStep 9314297 = 6985723) B6985723
theorem B41898545 : Blo 1634016 41898545 := bstep (se 2 (by rfl) ⟨15711954, by rfl⟩ : syracuseStep 41898545 = 31423909) B31423909
theorem B2619839 : Blo 1634016 2619839 := bstep (se 1 (by rfl) ⟨1964879, by rfl⟩ : syracuseStep 2619839 = 3929759) B3929759
theorem B238550579 : Blo 1634016 238550579 := bstep (se 1 (by rfl) ⟨178912934, by rfl⟩ : syracuseStep 238550579 = 357825869) B357825869
theorem B31867291 : Blo 1634016 31867291 := bstep (se 1 (by rfl) ⟨23900468, by rfl⟩ : syracuseStep 31867291 = 47800937) B47800937
theorem B1746559 : Blo 1634016 1746559 := bstep (se 1 (by rfl) ⟨1309919, by rfl⟩ : syracuseStep 1746559 = 2619839) B2619839
theorem B159033719 : Blo 1634016 159033719 := bstep (se 1 (by rfl) ⟨119275289, by rfl⟩ : syracuseStep 159033719 = 238550579) B238550579
theorem B6204397 : Blo 1634016 6204397 := bstep (se 3 (by rfl) ⟨1163324, by rfl⟩ : syracuseStep 6204397 = 2326649) B2326649
theorem B5518151 : Blo 1634016 5518151 := bstep (se 1 (by rfl) ⟨4138613, by rfl⟩ : syracuseStep 5518151 = 8277227) B8277227
theorem B10073641 : Blo 1634016 10073641 := bstep (se 2 (by rfl) ⟨3777615, by rfl⟩ : syracuseStep 10073641 = 7555231) B7555231
theorem B27932363 : Blo 1634016 27932363 := bstep (se 1 (by rfl) ⟨20949272, by rfl⟩ : syracuseStep 27932363 = 41898545) B41898545
theorem B6209531 : Blo 1634016 6209531 := bstep (se 1 (by rfl) ⟨4657148, by rfl⟩ : syracuseStep 6209531 = 9314297) B9314297
theorem B3678767 : Blo 1634016 3678767 := bstep (se 1 (by rfl) ⟨2759075, by rfl⟩ : syracuseStep 3678767 = 5518151) B5518151
theorem B18621575 : Blo 1634016 18621575 := bstep (se 1 (by rfl) ⟨13966181, by rfl⟩ : syracuseStep 18621575 = 27932363) B27932363
theorem B106022479 : Blo 1634016 106022479 := bstep (se 1 (by rfl) ⟨79516859, by rfl⟩ : syracuseStep 106022479 = 159033719) B159033719
theorem B2328745 : Blo 1634016 2328745 := bstep (se 2 (by rfl) ⟨873279, by rfl⟩ : syracuseStep 2328745 = 1746559) B1746559
theorem B4139687 : Blo 1634016 4139687 := bstep (se 1 (by rfl) ⟨3104765, by rfl⟩ : syracuseStep 4139687 = 6209531) B6209531
theorem B13431521 : Blo 1634016 13431521 := bstep (se 2 (by rfl) ⟨5036820, by rfl⟩ : syracuseStep 13431521 = 10073641) B10073641
theorem B42489721 : Blo 1634016 42489721 := bstep (se 2 (by rfl) ⟨15933645, by rfl⟩ : syracuseStep 42489721 = 31867291) B31867291
theorem B8272529 : Blo 1634016 8272529 := bstep (se 2 (by rfl) ⟨3102198, by rfl⟩ : syracuseStep 8272529 = 6204397) B6204397
theorem B3104993 : Blo 1634016 3104993 := bstep (se 2 (by rfl) ⟨1164372, by rfl⟩ : syracuseStep 3104993 = 2328745) B2328745
theorem B5515019 : Blo 1634016 5515019 := bstep (se 1 (by rfl) ⟨4136264, by rfl⟩ : syracuseStep 5515019 = 8272529) B8272529
theorem B35817389 : Blo 1634016 35817389 := bstep (se 3 (by rfl) ⟨6715760, by rfl⟩ : syracuseStep 35817389 = 13431521) B13431521
theorem B141363305 : Blo 1634016 141363305 := bstep (se 2 (by rfl) ⟨53011239, by rfl⟩ : syracuseStep 141363305 = 106022479) B106022479
theorem B2452511 : Blo 1634016 2452511 := bstep (se 1 (by rfl) ⟨1839383, by rfl⟩ : syracuseStep 2452511 = 3678767) B3678767
theorem B12414383 : Blo 1634016 12414383 := bstep (se 1 (by rfl) ⟨9310787, by rfl⟩ : syracuseStep 12414383 = 18621575) B18621575
theorem B56652961 : Blo 1634016 56652961 := bstep (se 2 (by rfl) ⟨21244860, by rfl⟩ : syracuseStep 56652961 = 42489721) B42489721
theorem B2759791 : Blo 1634016 2759791 := bstep (se 1 (by rfl) ⟨2069843, by rfl⟩ : syracuseStep 2759791 = 4139687) B4139687
theorem B94242203 : Blo 1634016 94242203 := bstep (se 1 (by rfl) ⟨70681652, by rfl⟩ : syracuseStep 94242203 = 141363305) B141363305
theorem B3679721 : Blo 1634016 3679721 := bstep (se 2 (by rfl) ⟨1379895, by rfl⟩ : syracuseStep 3679721 = 2759791) B2759791
theorem B8276255 : Blo 1634016 8276255 := bstep (se 1 (by rfl) ⟨6207191, by rfl⟩ : syracuseStep 8276255 = 12414383) B12414383
theorem B1635007 : Blo 1634016 1635007 := bstep (se 1 (by rfl) ⟨1226255, by rfl⟩ : syracuseStep 1635007 = 2452511) B2452511
theorem B8279981 : Blo 1634016 8279981 := bstep (se 3 (by rfl) ⟨1552496, by rfl⟩ : syracuseStep 8279981 = 3104993) B3104993
theorem B3676679 : Blo 1634016 3676679 := bstep (se 1 (by rfl) ⟨2757509, by rfl⟩ : syracuseStep 3676679 = 5515019) B5515019
theorem B23878259 : Blo 1634016 23878259 := bstep (se 1 (by rfl) ⟨17908694, by rfl⟩ : syracuseStep 23878259 = 35817389) B35817389
theorem B75537281 : Blo 1634016 75537281 := bstep (se 2 (by rfl) ⟨28326480, by rfl⟩ : syracuseStep 75537281 = 56652961) B56652961
theorem B2451119 : Blo 1634016 2451119 := bstep (se 1 (by rfl) ⟨1838339, by rfl⟩ : syracuseStep 2451119 = 3676679) B3676679
theorem B15918839 : Blo 1634016 15918839 := bstep (se 1 (by rfl) ⟨11939129, by rfl⟩ : syracuseStep 15918839 = 23878259) B23878259
theorem B50358187 : Blo 1634016 50358187 := bstep (se 1 (by rfl) ⟨37768640, by rfl⟩ : syracuseStep 50358187 = 75537281) B75537281
theorem B62828135 : Blo 1634016 62828135 := bstep (se 1 (by rfl) ⟨47121101, by rfl⟩ : syracuseStep 62828135 = 94242203) B94242203
theorem B2453147 : Blo 1634016 2453147 := bstep (se 1 (by rfl) ⟨1839860, by rfl⟩ : syracuseStep 2453147 = 3679721) B3679721
theorem B5517503 : Blo 1634016 5517503 := bstep (se 1 (by rfl) ⟨4138127, by rfl⟩ : syracuseStep 5517503 = 8276255) B8276255
theorem B5519987 : Blo 1634016 5519987 := bstep (se 1 (by rfl) ⟨4139990, by rfl⟩ : syracuseStep 5519987 = 8279981) B8279981
theorem B3678335 : Blo 1634016 3678335 := bstep (se 1 (by rfl) ⟨2758751, by rfl⟩ : syracuseStep 3678335 = 5517503) B5517503
theorem B3679991 : Blo 1634016 3679991 := bstep (se 1 (by rfl) ⟨2759993, by rfl⟩ : syracuseStep 3679991 = 5519987) B5519987
theorem B67144249 : Blo 1634016 67144249 := bstep (se 2 (by rfl) ⟨25179093, by rfl⟩ : syracuseStep 67144249 = 50358187) B50358187
theorem B1634079 : Blo 1634016 1634079 := bstep (se 1 (by rfl) ⟨1225559, by rfl⟩ : syracuseStep 1634079 = 2451119) B2451119
theorem B10612559 : Blo 1634016 10612559 := bstep (se 1 (by rfl) ⟨7959419, by rfl⟩ : syracuseStep 10612559 = 15918839) B15918839
theorem B1635431 : Blo 1634016 1635431 := bstep (se 1 (by rfl) ⟨1226573, by rfl⟩ : syracuseStep 1635431 = 2453147) B2453147
theorem B41885423 : Blo 1634016 41885423 := bstep (se 1 (by rfl) ⟨31414067, by rfl⟩ : syracuseStep 41885423 = 62828135) B62828135
theorem B2452223 : Blo 1634016 2452223 := bstep (se 1 (by rfl) ⟨1839167, by rfl⟩ : syracuseStep 2452223 = 3678335) B3678335
theorem B89525665 : Blo 1634016 89525665 := bstep (se 2 (by rfl) ⟨33572124, by rfl⟩ : syracuseStep 89525665 = 67144249) B67144249
theorem B2453327 : Blo 1634016 2453327 := bstep (se 1 (by rfl) ⟨1839995, by rfl⟩ : syracuseStep 2453327 = 3679991) B3679991
theorem B27923615 : Blo 1634016 27923615 := bstep (se 1 (by rfl) ⟨20942711, by rfl⟩ : syracuseStep 27923615 = 41885423) B41885423
theorem B7075039 : Blo 1634016 7075039 := bstep (se 1 (by rfl) ⟨5306279, by rfl⟩ : syracuseStep 7075039 = 10612559) B10612559
theorem B119367553 : Blo 1634016 119367553 := bstep (se 2 (by rfl) ⟨44762832, by rfl⟩ : syracuseStep 119367553 = 89525665) B89525665
theorem B18615743 : Blo 1634016 18615743 := bstep (se 1 (by rfl) ⟨13961807, by rfl⟩ : syracuseStep 18615743 = 27923615) B27923615
theorem B9433385 : Blo 1634016 9433385 := bstep (se 2 (by rfl) ⟨3537519, by rfl⟩ : syracuseStep 9433385 = 7075039) B7075039
theorem B1634815 : Blo 1634016 1634815 := bstep (se 1 (by rfl) ⟨1226111, by rfl⟩ : syracuseStep 1634815 = 2452223) B2452223
theorem B1635551 : Blo 1634016 1635551 := bstep (se 1 (by rfl) ⟨1226663, by rfl⟩ : syracuseStep 1635551 = 2453327) B2453327
theorem B159156737 : Blo 1634016 159156737 := bstep (se 2 (by rfl) ⟨59683776, by rfl⟩ : syracuseStep 159156737 = 119367553) B119367553
theorem B6288923 : Blo 1634016 6288923 := bstep (se 1 (by rfl) ⟨4716692, by rfl⟩ : syracuseStep 6288923 = 9433385) B9433385
theorem B12410495 : Blo 1634016 12410495 := bstep (se 1 (by rfl) ⟨9307871, by rfl⟩ : syracuseStep 12410495 = 18615743) B18615743
theorem B16770461 : Blo 1634016 16770461 := bstep (se 3 (by rfl) ⟨3144461, by rfl⟩ : syracuseStep 16770461 = 6288923) B6288923
theorem B106104491 : Blo 1634016 106104491 := bstep (se 1 (by rfl) ⟨79578368, by rfl⟩ : syracuseStep 106104491 = 159156737) B159156737
theorem B8273663 : Blo 1634016 8273663 := bstep (se 1 (by rfl) ⟨6205247, by rfl⟩ : syracuseStep 8273663 = 12410495) B12410495
theorem B44721229 : Blo 1634016 44721229 := bstep (se 3 (by rfl) ⟨8385230, by rfl⟩ : syracuseStep 44721229 = 16770461) B16770461
theorem B5515775 : Blo 1634016 5515775 := bstep (se 1 (by rfl) ⟨4136831, by rfl⟩ : syracuseStep 5515775 = 8273663) B8273663
theorem B70736327 : Blo 1634016 70736327 := bstep (se 1 (by rfl) ⟨53052245, by rfl⟩ : syracuseStep 70736327 = 106104491) B106104491
theorem B47157551 : Blo 1634016 47157551 := bstep (se 1 (by rfl) ⟨35368163, by rfl⟩ : syracuseStep 47157551 = 70736327) B70736327
theorem B59628305 : Blo 1634016 59628305 := bstep (se 2 (by rfl) ⟨22360614, by rfl⟩ : syracuseStep 59628305 = 44721229) B44721229
theorem B3677183 : Blo 1634016 3677183 := bstep (se 1 (by rfl) ⟨2757887, by rfl⟩ : syracuseStep 3677183 = 5515775) B5515775
theorem B2451455 : Blo 1634016 2451455 := bstep (se 1 (by rfl) ⟨1838591, by rfl⟩ : syracuseStep 2451455 = 3677183) B3677183
theorem B39752203 : Blo 1634016 39752203 := bstep (se 1 (by rfl) ⟨29814152, by rfl⟩ : syracuseStep 39752203 = 59628305) B59628305
theorem B31438367 : Blo 1634016 31438367 := bstep (se 1 (by rfl) ⟨23578775, by rfl⟩ : syracuseStep 31438367 = 47157551) B47157551
theorem B53002937 : Blo 1634016 53002937 := bstep (se 2 (by rfl) ⟨19876101, by rfl⟩ : syracuseStep 53002937 = 39752203) B39752203
theorem B20958911 : Blo 1634016 20958911 := bstep (se 1 (by rfl) ⟨15719183, by rfl⟩ : syracuseStep 20958911 = 31438367) B31438367
theorem B1634303 : Blo 1634016 1634303 := bstep (se 1 (by rfl) ⟨1225727, by rfl⟩ : syracuseStep 1634303 = 2451455) B2451455
theorem B35335291 : Blo 1634016 35335291 := bstep (se 1 (by rfl) ⟨26501468, by rfl⟩ : syracuseStep 35335291 = 53002937) B53002937
theorem B13972607 : Blo 1634016 13972607 := bstep (se 1 (by rfl) ⟨10479455, by rfl⟩ : syracuseStep 13972607 = 20958911) B20958911
theorem B9315071 : Blo 1634016 9315071 := bstep (se 1 (by rfl) ⟨6986303, by rfl⟩ : syracuseStep 9315071 = 13972607) B13972607
theorem B47113721 : Blo 1634016 47113721 := bstep (se 2 (by rfl) ⟨17667645, by rfl⟩ : syracuseStep 47113721 = 35335291) B35335291
theorem B6210047 : Blo 1634016 6210047 := bstep (se 1 (by rfl) ⟨4657535, by rfl⟩ : syracuseStep 6210047 = 9315071) B9315071
theorem B31409147 : Blo 1634016 31409147 := bstep (se 1 (by rfl) ⟨23556860, by rfl⟩ : syracuseStep 31409147 = 47113721) B47113721
theorem B20939431 : Blo 1634016 20939431 := bstep (se 1 (by rfl) ⟨15704573, by rfl⟩ : syracuseStep 20939431 = 31409147) B31409147
theorem B4140031 : Blo 1634016 4140031 := bstep (se 1 (by rfl) ⟨3105023, by rfl⟩ : syracuseStep 4140031 = 6210047) B6210047
theorem B27919241 : Blo 1634016 27919241 := bstep (se 2 (by rfl) ⟨10469715, by rfl⟩ : syracuseStep 27919241 = 20939431) B20939431
theorem B5520041 : Blo 1634016 5520041 := bstep (se 2 (by rfl) ⟨2070015, by rfl⟩ : syracuseStep 5520041 = 4140031) B4140031
theorem B18612827 : Blo 1634016 18612827 := bstep (se 1 (by rfl) ⟨13959620, by rfl⟩ : syracuseStep 18612827 = 27919241) B27919241
theorem B3680027 : Blo 1634016 3680027 := bstep (se 1 (by rfl) ⟨2760020, by rfl⟩ : syracuseStep 3680027 = 5520041) B5520041
theorem B2453351 : Blo 1634016 2453351 := bstep (se 1 (by rfl) ⟨1840013, by rfl⟩ : syracuseStep 2453351 = 3680027) B3680027
theorem B12408551 : Blo 1634016 12408551 := bstep (se 1 (by rfl) ⟨9306413, by rfl⟩ : syracuseStep 12408551 = 18612827) B18612827
theorem B1635567 : Blo 1634016 1635567 := bstep (se 1 (by rfl) ⟨1226675, by rfl⟩ : syracuseStep 1635567 = 2453351) B2453351
theorem B8272367 : Blo 1634016 8272367 := bstep (se 1 (by rfl) ⟨6204275, by rfl⟩ : syracuseStep 8272367 = 12408551) B12408551
theorem B5514911 : Blo 1634016 5514911 := bstep (se 1 (by rfl) ⟨4136183, by rfl⟩ : syracuseStep 5514911 = 8272367) B8272367
theorem B3676607 : Blo 1634016 3676607 := bstep (se 1 (by rfl) ⟨2757455, by rfl⟩ : syracuseStep 3676607 = 5514911) B5514911
theorem B2451071 : Blo 1634016 2451071 := bstep (se 1 (by rfl) ⟨1838303, by rfl⟩ : syracuseStep 2451071 = 3676607) B3676607
theorem B1634047 : Blo 1634016 1634047 := bstep (se 1 (by rfl) ⟨1225535, by rfl⟩ : syracuseStep 1634047 = 2451071) B2451071

theorem C0 (j : ℕ) (h1 : 408504 ≤ j) (h2 : j ≤ 409003) : Blo 1634016 (4 * j + 3) := by
  interval_cases j
  · exact B1634019
  · exact B1634023
  · exact B1634027
  · exact B1634031
  · exact B1634035
  · exact B1634039
  · exact B1634043
  · exact B1634047
  · exact B1634051
  · exact B1634055
  · exact B1634059
  · exact B1634063
  · exact B1634067
  · exact B1634071
  · exact B1634075
  · exact B1634079
  · exact B1634083
  · exact B1634087
  · exact B1634091
  · exact B1634095
  · exact B1634099
  · exact B1634103
  · exact B1634107
  · exact B1634111
  · exact B1634115
  · exact B1634119
  · exact B1634123
  · exact B1634127
  · exact B1634131
  · exact B1634135
  · exact B1634139
  · exact B1634143
  · exact B1634147
  · exact B1634151
  · exact B1634155
  · exact B1634159
  · exact B1634163
  · exact B1634167
  · exact B1634171
  · exact B1634175
  · exact B1634179
  · exact B1634183
  · exact B1634187
  · exact B1634191
  · exact B1634195
  · exact B1634199
  · exact B1634203
  · exact B1634207
  · exact B1634211
  · exact B1634215
  · exact B1634219
  · exact B1634223
  · exact B1634227
  · exact B1634231
  · exact B1634235
  · exact B1634239
  · exact B1634243
  · exact B1634247
  · exact B1634251
  · exact B1634255
  · exact B1634259
  · exact B1634263
  · exact B1634267
  · exact B1634271
  · exact B1634275
  · exact B1634279
  · exact B1634283
  · exact B1634287
  · exact B1634291
  · exact B1634295
  · exact B1634299
  · exact B1634303
  · exact B1634307
  · exact B1634311
  · exact B1634315
  · exact B1634319
  · exact B1634323
  · exact B1634327
  · exact B1634331
  · exact B1634335
  · exact B1634339
  · exact B1634343
  · exact B1634347
  · exact B1634351
  · exact B1634355
  · exact B1634359
  · exact B1634363
  · exact B1634367
  · exact B1634371
  · exact B1634375
  · exact B1634379
  · exact B1634383
  · exact B1634387
  · exact B1634391
  · exact B1634395
  · exact B1634399
  · exact B1634403
  · exact B1634407
  · exact B1634411
  · exact B1634415
  · exact B1634419
  · exact B1634423
  · exact B1634427
  · exact B1634431
  · exact B1634435
  · exact B1634439
  · exact B1634443
  · exact B1634447
  · exact B1634451
  · exact B1634455
  · exact B1634459
  · exact B1634463
  · exact B1634467
  · exact B1634471
  · exact B1634475
  · exact B1634479
  · exact B1634483
  · exact B1634487
  · exact B1634491
  · exact B1634495
  · exact B1634499
  · exact B1634503
  · exact B1634507
  · exact B1634511
  · exact B1634515
  · exact B1634519
  · exact B1634523
  · exact B1634527
  · exact B1634531
  · exact B1634535
  · exact B1634539
  · exact B1634543
  · exact B1634547
  · exact B1634551
  · exact B1634555
  · exact B1634559
  · exact B1634563
  · exact B1634567
  · exact B1634571
  · exact B1634575
  · exact B1634579
  · exact B1634583
  · exact B1634587
  · exact B1634591
  · exact B1634595
  · exact B1634599
  · exact B1634603
  · exact B1634607
  · exact B1634611
  · exact B1634615
  · exact B1634619
  · exact B1634623
  · exact B1634627
  · exact B1634631
  · exact B1634635
  · exact B1634639
  · exact B1634643
  · exact B1634647
  · exact B1634651
  · exact B1634655
  · exact B1634659
  · exact B1634663
  · exact B1634667
  · exact B1634671
  · exact B1634675
  · exact B1634679
  · exact B1634683
  · exact B1634687
  · exact B1634691
  · exact B1634695
  · exact B1634699
  · exact B1634703
  · exact B1634707
  · exact B1634711
  · exact B1634715
  · exact B1634719
  · exact B1634723
  · exact B1634727
  · exact B1634731
  · exact B1634735
  · exact B1634739
  · exact B1634743
  · exact B1634747
  · exact B1634751
  · exact B1634755
  · exact B1634759
  · exact B1634763
  · exact B1634767
  · exact B1634771
  · exact B1634775
  · exact B1634779
  · exact B1634783
  · exact B1634787
  · exact B1634791
  · exact B1634795
  · exact B1634799
  · exact B1634803
  · exact B1634807
  · exact B1634811
  · exact B1634815
  · exact B1634819
  · exact B1634823
  · exact B1634827
  · exact B1634831
  · exact B1634835
  · exact B1634839
  · exact B1634843
  · exact B1634847
  · exact B1634851
  · exact B1634855
  · exact B1634859
  · exact B1634863
  · exact B1634867
  · exact B1634871
  · exact B1634875
  · exact B1634879
  · exact B1634883
  · exact B1634887
  · exact B1634891
  · exact B1634895
  · exact B1634899
  · exact B1634903
  · exact B1634907
  · exact B1634911
  · exact B1634915
  · exact B1634919
  · exact B1634923
  · exact B1634927
  · exact B1634931
  · exact B1634935
  · exact B1634939
  · exact B1634943
  · exact B1634947
  · exact B1634951
  · exact B1634955
  · exact B1634959
  · exact B1634963
  · exact B1634967
  · exact B1634971
  · exact B1634975
  · exact B1634979
  · exact B1634983
  · exact B1634987
  · exact B1634991
  · exact B1634995
  · exact B1634999
  · exact B1635003
  · exact B1635007
  · exact B1635011
  · exact B1635015
  · exact B1635019
  · exact B1635023
  · exact B1635027
  · exact B1635031
  · exact B1635035
  · exact B1635039
  · exact B1635043
  · exact B1635047
  · exact B1635051
  · exact B1635055
  · exact B1635059
  · exact B1635063
  · exact B1635067
  · exact B1635071
  · exact B1635075
  · exact B1635079
  · exact B1635083
  · exact B1635087
  · exact B1635091
  · exact B1635095
  · exact B1635099
  · exact B1635103
  · exact B1635107
  · exact B1635111
  · exact B1635115
  · exact B1635119
  · exact B1635123
  · exact B1635127
  · exact B1635131
  · exact B1635135
  · exact B1635139
  · exact B1635143
  · exact B1635147
  · exact B1635151
  · exact B1635155
  · exact B1635159
  · exact B1635163
  · exact B1635167
  · exact B1635171
  · exact B1635175
  · exact B1635179
  · exact B1635183
  · exact B1635187
  · exact B1635191
  · exact B1635195
  · exact B1635199
  · exact B1635203
  · exact B1635207
  · exact B1635211
  · exact B1635215
  · exact B1635219
  · exact B1635223
  · exact B1635227
  · exact B1635231
  · exact B1635235
  · exact B1635239
  · exact B1635243
  · exact B1635247
  · exact B1635251
  · exact B1635255
  · exact B1635259
  · exact B1635263
  · exact B1635267
  · exact B1635271
  · exact B1635275
  · exact B1635279
  · exact B1635283
  · exact B1635287
  · exact B1635291
  · exact B1635295
  · exact B1635299
  · exact B1635303
  · exact B1635307
  · exact B1635311
  · exact B1635315
  · exact B1635319
  · exact B1635323
  · exact B1635327
  · exact B1635331
  · exact B1635335
  · exact B1635339
  · exact B1635343
  · exact B1635347
  · exact B1635351
  · exact B1635355
  · exact B1635359
  · exact B1635363
  · exact B1635367
  · exact B1635371
  · exact B1635375
  · exact B1635379
  · exact B1635383
  · exact B1635387
  · exact B1635391
  · exact B1635395
  · exact B1635399
  · exact B1635403
  · exact B1635407
  · exact B1635411
  · exact B1635415
  · exact B1635419
  · exact B1635423
  · exact B1635427
  · exact B1635431
  · exact B1635435
  · exact B1635439
  · exact B1635443
  · exact B1635447
  · exact B1635451
  · exact B1635455
  · exact B1635459
  · exact B1635463
  · exact B1635467
  · exact B1635471
  · exact B1635475
  · exact B1635479
  · exact B1635483
  · exact B1635487
  · exact B1635491
  · exact B1635495
  · exact B1635499
  · exact B1635503
  · exact B1635507
  · exact B1635511
  · exact B1635515
  · exact B1635519
  · exact B1635523
  · exact B1635527
  · exact B1635531
  · exact B1635535
  · exact B1635539
  · exact B1635543
  · exact B1635547
  · exact B1635551
  · exact B1635555
  · exact B1635559
  · exact B1635563
  · exact B1635567
  · exact B1635571
  · exact B1635575
  · exact B1635579
  · exact B1635583
  · exact B1635587
  · exact B1635591
  · exact B1635595
  · exact B1635599
  · exact B1635603
  · exact B1635607
  · exact B1635611
  · exact B1635615
  · exact B1635619
  · exact B1635623
  · exact B1635627
  · exact B1635631
  · exact B1635635
  · exact B1635639
  · exact B1635643
  · exact B1635647
  · exact B1635651
  · exact B1635655
  · exact B1635659
  · exact B1635663
  · exact B1635667
  · exact B1635671
  · exact B1635675
  · exact B1635679
  · exact B1635683
  · exact B1635687
  · exact B1635691
  · exact B1635695
  · exact B1635699
  · exact B1635703
  · exact B1635707
  · exact B1635711
  · exact B1635715
  · exact B1635719
  · exact B1635723
  · exact B1635727
  · exact B1635731
  · exact B1635735
  · exact B1635739
  · exact B1635743
  · exact B1635747
  · exact B1635751
  · exact B1635755
  · exact B1635759
  · exact B1635763
  · exact B1635767
  · exact B1635771
  · exact B1635775
  · exact B1635779
  · exact B1635783
  · exact B1635787
  · exact B1635791
  · exact B1635795
  · exact B1635799
  · exact B1635803
  · exact B1635807
  · exact B1635811
  · exact B1635815
  · exact B1635819
  · exact B1635823
  · exact B1635827
  · exact B1635831
  · exact B1635835
  · exact B1635839
  · exact B1635843
  · exact B1635847
  · exact B1635851
  · exact B1635855
  · exact B1635859
  · exact B1635863
  · exact B1635867
  · exact B1635871
  · exact B1635875
  · exact B1635879
  · exact B1635883
  · exact B1635887
  · exact B1635891
  · exact B1635895
  · exact B1635899
  · exact B1635903
  · exact B1635907
  · exact B1635911
  · exact B1635915
  · exact B1635919
  · exact B1635923
  · exact B1635927
  · exact B1635931
  · exact B1635935
  · exact B1635939
  · exact B1635943
  · exact B1635947
  · exact B1635951
  · exact B1635955
  · exact B1635959
  · exact B1635963
  · exact B1635967
  · exact B1635971
  · exact B1635975
  · exact B1635979
  · exact B1635983
  · exact B1635987
  · exact B1635991
  · exact B1635995
  · exact B1635999
  · exact B1636003
  · exact B1636007
  · exact B1636011
  · exact B1636015

theorem solution (m : ℕ) (hlo : 1634016 ≤ m) (hhi : m ≤ 1636016) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 408504 ≤ j := by omega
    have hj2 : j ≤ 409003 := by omega
    have hb : Blo 1634016 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
