-- Prove2me | solution 1 for syracuse_descends_range_566810_570810
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:38.581579+00:00
-- url     : https://prove2.me/submissions/1144a585-76cc-4df3-b1be-066fddf13b9f

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


theorem B851981 : Blo 566810 851981 := bbase (se 3 (by rfl) ⟨159746, by rfl⟩ : syracuseStep 851981 = 319493) (by norm_num)
theorem B1277981 : Blo 566810 1277981 := bbase (se 3 (by rfl) ⟨239621, by rfl⟩ : syracuseStep 1277981 = 479243) (by norm_num)
theorem B852005 : Blo 566810 852005 := bbase (se 4 (by rfl) ⟨79875, by rfl⟩ : syracuseStep 852005 = 159751) (by norm_num)
theorem B852029 : Blo 566810 852029 := bbase (se 3 (by rfl) ⟨159755, by rfl⟩ : syracuseStep 852029 = 319511) (by norm_num)
theorem B852053 : Blo 566810 852053 := bbase (se 8 (by rfl) ⟨4992, by rfl⟩ : syracuseStep 852053 = 9985) (by norm_num)
theorem B1278053 : Blo 566810 1278053 := bbase (se 4 (by rfl) ⟨119817, by rfl⟩ : syracuseStep 1278053 = 239635) (by norm_num)
theorem B721001 : Blo 566810 721001 := bbase (se 2 (by rfl) ⟨270375, by rfl⟩ : syracuseStep 721001 = 540751) (by norm_num)
theorem B852077 : Blo 566810 852077 := bbase (se 3 (by rfl) ⟨159764, by rfl⟩ : syracuseStep 852077 = 319529) (by norm_num)
theorem B1441901 : Blo 566810 1441901 := bbase (se 3 (by rfl) ⟨270356, by rfl⟩ : syracuseStep 1441901 = 540713) (by norm_num)
theorem B852101 : Blo 566810 852101 := bbase (se 4 (by rfl) ⟨79884, by rfl⟩ : syracuseStep 852101 = 159769) (by norm_num)
theorem B2162821 : Blo 566810 2162821 := bbase (se 4 (by rfl) ⟨202764, by rfl⟩ : syracuseStep 2162821 = 405529) (by norm_num)
theorem B852125 : Blo 566810 852125 := bbase (se 3 (by rfl) ⟨159773, by rfl⟩ : syracuseStep 852125 = 319547) (by norm_num)
theorem B721057 : Blo 566810 721057 := bbase (se 2 (by rfl) ⟨270396, by rfl⟩ : syracuseStep 721057 = 540793) (by norm_num)
theorem B1278125 : Blo 566810 1278125 := bbase (se 3 (by rfl) ⟨239648, by rfl⟩ : syracuseStep 1278125 = 479297) (by norm_num)
theorem B852149 : Blo 566810 852149 := bbase (se 5 (by rfl) ⟨39944, by rfl⟩ : syracuseStep 852149 = 79889) (by norm_num)
theorem B1081525 : Blo 566810 1081525 := bbase (se 5 (by rfl) ⟨50696, by rfl⟩ : syracuseStep 1081525 = 101393) (by norm_num)
theorem B852173 : Blo 566810 852173 := bbase (se 3 (by rfl) ⟨159782, by rfl⟩ : syracuseStep 852173 = 319565) (by norm_num)
theorem B852197 : Blo 566810 852197 := bbase (se 4 (by rfl) ⟨79893, by rfl⟩ : syracuseStep 852197 = 159787) (by norm_num)
theorem B1310957 : Blo 566810 1310957 := bbase (se 3 (by rfl) ⟨245804, by rfl⟩ : syracuseStep 1310957 = 491609) (by norm_num)
theorem B1278197 : Blo 566810 1278197 := bbase (se 5 (by rfl) ⟨59915, by rfl⟩ : syracuseStep 1278197 = 119831) (by norm_num)
theorem B852221 : Blo 566810 852221 := bbase (se 3 (by rfl) ⟨159791, by rfl⟩ : syracuseStep 852221 = 319583) (by norm_num)
theorem B721153 : Blo 566810 721153 := bbase (se 2 (by rfl) ⟨270432, by rfl⟩ : syracuseStep 721153 = 540865) (by norm_num)
theorem B852245 : Blo 566810 852245 := bbase (se 6 (by rfl) ⟨19974, by rfl⟩ : syracuseStep 852245 = 39949) (by norm_num)
theorem B852269 : Blo 566810 852269 := bbase (se 3 (by rfl) ⟨159800, by rfl⟩ : syracuseStep 852269 = 319601) (by norm_num)
theorem B1278269 : Blo 566810 1278269 := bbase (se 3 (by rfl) ⟨239675, by rfl⟩ : syracuseStep 1278269 = 479351) (by norm_num)
theorem B852293 : Blo 566810 852293 := bbase (se 4 (by rfl) ⟨79902, by rfl⟩ : syracuseStep 852293 = 159805) (by norm_num)
theorem B1081669 : Blo 566810 1081669 := bbase (se 4 (by rfl) ⟨101406, by rfl⟩ : syracuseStep 1081669 = 202813) (by norm_num)
theorem B852317 : Blo 566810 852317 := bbase (se 3 (by rfl) ⟨159809, by rfl⟩ : syracuseStep 852317 = 319619) (by norm_num)
theorem B852341 : Blo 566810 852341 := bbase (se 5 (by rfl) ⟨39953, by rfl⟩ : syracuseStep 852341 = 79907) (by norm_num)
theorem B1278341 : Blo 566810 1278341 := bbase (se 4 (by rfl) ⟨119844, by rfl⟩ : syracuseStep 1278341 = 239689) (by norm_num)
theorem B852365 : Blo 566810 852365 := bbase (se 3 (by rfl) ⟨159818, by rfl⟩ : syracuseStep 852365 = 319637) (by norm_num)
theorem B852389 : Blo 566810 852389 := bbase (se 4 (by rfl) ⟨79911, by rfl⟩ : syracuseStep 852389 = 159823) (by norm_num)
theorem B721325 : Blo 566810 721325 := bbase (se 3 (by rfl) ⟨135248, by rfl⟩ : syracuseStep 721325 = 270497) (by norm_num)
theorem B2163125 : Blo 566810 2163125 := bbase (se 5 (by rfl) ⟨101396, by rfl⟩ : syracuseStep 2163125 = 202793) (by norm_num)
theorem B852413 : Blo 566810 852413 := bbase (se 3 (by rfl) ⟨159827, by rfl⟩ : syracuseStep 852413 = 319655) (by norm_num)
theorem B1442245 : Blo 566810 1442245 := bbase (se 4 (by rfl) ⟨135210, by rfl⟩ : syracuseStep 1442245 = 270421) (by norm_num)
theorem B1278413 : Blo 566810 1278413 := bbase (se 3 (by rfl) ⟨239702, by rfl⟩ : syracuseStep 1278413 = 479405) (by norm_num)
theorem B852437 : Blo 566810 852437 := bbase (se 7 (by rfl) ⟨9989, by rfl⟩ : syracuseStep 852437 = 19979) (by norm_num)
theorem B819677 : Blo 566810 819677 := bbase (se 3 (by rfl) ⟨153689, by rfl⟩ : syracuseStep 819677 = 307379) (by norm_num)
theorem B1081829 : Blo 566810 1081829 := bbase (se 4 (by rfl) ⟨101421, by rfl⟩ : syracuseStep 1081829 = 202843) (by norm_num)
theorem B721381 : Blo 566810 721381 := bbase (se 4 (by rfl) ⟨67629, by rfl⟩ : syracuseStep 721381 = 135259) (by norm_num)
theorem B852461 : Blo 566810 852461 := bbase (se 3 (by rfl) ⟨159836, by rfl⟩ : syracuseStep 852461 = 319673) (by norm_num)
theorem B2884085 : Blo 566810 2884085 := bbase (se 5 (by rfl) ⟨135191, by rfl⟩ : syracuseStep 2884085 = 270383) (by norm_num)
theorem B852485 : Blo 566810 852485 := bbase (se 4 (by rfl) ⟨79920, by rfl⟩ : syracuseStep 852485 = 159841) (by norm_num)
theorem B1278485 : Blo 566810 1278485 := bbase (se 6 (by rfl) ⟨29964, by rfl⟩ : syracuseStep 1278485 = 59929) (by norm_num)
theorem B852509 : Blo 566810 852509 := bbase (se 3 (by rfl) ⟨159845, by rfl⟩ : syracuseStep 852509 = 319691) (by norm_num)
theorem B852533 : Blo 566810 852533 := bbase (se 5 (by rfl) ⟨39962, by rfl⟩ : syracuseStep 852533 = 79925) (by norm_num)
theorem B1442357 : Blo 566810 1442357 := bbase (se 5 (by rfl) ⟨67610, by rfl⟩ : syracuseStep 1442357 = 135221) (by norm_num)
theorem B721477 : Blo 566810 721477 := bbase (se 4 (by rfl) ⟨67638, by rfl⟩ : syracuseStep 721477 = 135277) (by norm_num)
theorem B852557 : Blo 566810 852557 := bbase (se 3 (by rfl) ⟨159854, by rfl⟩ : syracuseStep 852557 = 319709) (by norm_num)
theorem B1278557 : Blo 566810 1278557 := bbase (se 3 (by rfl) ⟨239729, by rfl⟩ : syracuseStep 1278557 = 479459) (by norm_num)
theorem B852581 : Blo 566810 852581 := bbase (se 4 (by rfl) ⟨79929, by rfl⟩ : syracuseStep 852581 = 159859) (by norm_num)
theorem B1081973 : Blo 566810 1081973 := bbase (se 5 (by rfl) ⟨50717, by rfl⟩ : syracuseStep 1081973 = 101435) (by norm_num)
theorem B852605 : Blo 566810 852605 := bbase (se 3 (by rfl) ⟨159863, by rfl⟩ : syracuseStep 852605 = 319727) (by norm_num)
theorem B852629 : Blo 566810 852629 := bbase (se 6 (by rfl) ⟨19983, by rfl⟩ : syracuseStep 852629 = 39967) (by norm_num)
theorem B1278629 : Blo 566810 1278629 := bbase (se 4 (by rfl) ⟨119871, by rfl⟩ : syracuseStep 1278629 = 239743) (by norm_num)
theorem B852653 : Blo 566810 852653 := bbase (se 3 (by rfl) ⟨159872, by rfl⟩ : syracuseStep 852653 = 319745) (by norm_num)
theorem B852677 : Blo 566810 852677 := bbase (se 4 (by rfl) ⟨79938, by rfl⟩ : syracuseStep 852677 = 159877) (by norm_num)
theorem B3637973 : Blo 566810 3637973 := bbase (se 7 (by rfl) ⟨42632, by rfl⟩ : syracuseStep 3637973 = 85265) (by norm_num)
theorem B852701 : Blo 566810 852701 := bbase (se 3 (by rfl) ⟨159881, by rfl⟩ : syracuseStep 852701 = 319763) (by norm_num)
theorem B1278701 : Blo 566810 1278701 := bbase (se 3 (by rfl) ⟨239756, by rfl⟩ : syracuseStep 1278701 = 479513) (by norm_num)
theorem B721649 : Blo 566810 721649 := bbase (se 2 (by rfl) ⟨270618, by rfl⟩ : syracuseStep 721649 = 541237) (by norm_num)
theorem B2425589 : Blo 566810 2425589 := bbase (se 5 (by rfl) ⟨113699, by rfl⟩ : syracuseStep 2425589 = 227399) (by norm_num)
theorem B4096757 : Blo 566810 4096757 := bbase (se 5 (by rfl) ⟨192035, by rfl⟩ : syracuseStep 4096757 = 384071) (by norm_num)
theorem B852725 : Blo 566810 852725 := bbase (se 5 (by rfl) ⟨39971, by rfl⟩ : syracuseStep 852725 = 79943) (by norm_num)
theorem B1442549 : Blo 566810 1442549 := bbase (se 5 (by rfl) ⟨67619, by rfl⟩ : syracuseStep 1442549 = 135239) (by norm_num)
theorem B852749 : Blo 566810 852749 := bbase (se 3 (by rfl) ⟨159890, by rfl⟩ : syracuseStep 852749 = 319781) (by norm_num)
theorem B852773 : Blo 566810 852773 := bbase (se 4 (by rfl) ⟨79947, by rfl⟩ : syracuseStep 852773 = 159895) (by norm_num)
theorem B721705 : Blo 566810 721705 := bbase (se 2 (by rfl) ⟨270639, by rfl⟩ : syracuseStep 721705 = 541279) (by norm_num)
theorem B1278773 : Blo 566810 1278773 := bbase (se 5 (by rfl) ⟨59942, by rfl⟩ : syracuseStep 1278773 = 119885) (by norm_num)
theorem B852797 : Blo 566810 852797 := bbase (se 3 (by rfl) ⟨159899, by rfl⟩ : syracuseStep 852797 = 319799) (by norm_num)
theorem B852821 : Blo 566810 852821 := bbase (se 9 (by rfl) ⟨2498, by rfl⟩ : syracuseStep 852821 = 4997) (by norm_num)
theorem B852845 : Blo 566810 852845 := bbase (se 3 (by rfl) ⟨159908, by rfl⟩ : syracuseStep 852845 = 319817) (by norm_num)
theorem B2196341 : Blo 566810 2196341 := bbase (se 5 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 2196341 = 205907) (by norm_num)
theorem B1278845 : Blo 566810 1278845 := bbase (se 3 (by rfl) ⟨239783, by rfl⟩ : syracuseStep 1278845 = 479567) (by norm_num)
theorem B852869 : Blo 566810 852869 := bbase (se 4 (by rfl) ⟨79956, by rfl⟩ : syracuseStep 852869 = 159913) (by norm_num)
theorem B721801 : Blo 566810 721801 := bbase (se 2 (by rfl) ⟨270675, by rfl⟩ : syracuseStep 721801 = 541351) (by norm_num)
theorem B1082261 : Blo 566810 1082261 := bbase (se 6 (by rfl) ⟨25365, by rfl⟩ : syracuseStep 1082261 = 50731) (by norm_num)
theorem B852893 : Blo 566810 852893 := bbase (se 3 (by rfl) ⟨159917, by rfl⟩ : syracuseStep 852893 = 319835) (by norm_num)
theorem B852917 : Blo 566810 852917 := bbase (se 5 (by rfl) ⟨39980, by rfl⟩ : syracuseStep 852917 = 79961) (by norm_num)
theorem B1278917 : Blo 566810 1278917 := bbase (se 4 (by rfl) ⟨119898, by rfl⟩ : syracuseStep 1278917 = 239797) (by norm_num)
theorem B852941 : Blo 566810 852941 := bbase (se 3 (by rfl) ⟨159926, by rfl⟩ : syracuseStep 852941 = 319853) (by norm_num)
theorem B852965 : Blo 566810 852965 := bbase (se 4 (by rfl) ⟨79965, by rfl⟩ : syracuseStep 852965 = 159931) (by norm_num)
theorem B852989 : Blo 566810 852989 := bbase (se 3 (by rfl) ⟨159935, by rfl⟩ : syracuseStep 852989 = 319871) (by norm_num)
theorem B1278989 : Blo 566810 1278989 := bbase (se 3 (by rfl) ⟨239810, by rfl⟩ : syracuseStep 1278989 = 479621) (by norm_num)
theorem B853013 : Blo 566810 853013 := bbase (se 6 (by rfl) ⟨19992, by rfl⟩ : syracuseStep 853013 = 39985) (by norm_num)
theorem B2950181 : Blo 566810 2950181 := bbase (se 4 (by rfl) ⟨276579, by rfl⟩ : syracuseStep 2950181 = 553159) (by norm_num)
theorem B853037 : Blo 566810 853037 := bbase (se 3 (by rfl) ⟨159944, by rfl⟩ : syracuseStep 853037 = 319889) (by norm_num)
theorem B1082413 : Blo 566810 1082413 := bbase (se 3 (by rfl) ⟨202952, by rfl⟩ : syracuseStep 1082413 = 405905) (by norm_num)
theorem B721973 : Blo 566810 721973 := bbase (se 5 (by rfl) ⟨33842, by rfl⟩ : syracuseStep 721973 = 67685) (by norm_num)
theorem B853061 : Blo 566810 853061 := bbase (se 4 (by rfl) ⟨79974, by rfl⟩ : syracuseStep 853061 = 159949) (by norm_num)
theorem B1442893 : Blo 566810 1442893 := bbase (se 3 (by rfl) ⟨270542, by rfl⟩ : syracuseStep 1442893 = 541085) (by norm_num)
theorem B1279061 : Blo 566810 1279061 := bbase (se 8 (by rfl) ⟨7494, by rfl⟩ : syracuseStep 1279061 = 14989) (by norm_num)
theorem B853085 : Blo 566810 853085 := bbase (se 3 (by rfl) ⟨159953, by rfl⟩ : syracuseStep 853085 = 319907) (by norm_num)
theorem B722029 : Blo 566810 722029 := bbase (se 3 (by rfl) ⟨135380, by rfl⟩ : syracuseStep 722029 = 270761) (by norm_num)
theorem B853109 : Blo 566810 853109 := bbase (se 5 (by rfl) ⟨39989, by rfl⟩ : syracuseStep 853109 = 79979) (by norm_num)
theorem B853133 : Blo 566810 853133 := bbase (se 3 (by rfl) ⟨159962, by rfl⟩ : syracuseStep 853133 = 319925) (by norm_num)
theorem B1279133 : Blo 566810 1279133 := bbase (se 3 (by rfl) ⟨239837, by rfl⟩ : syracuseStep 1279133 = 479675) (by norm_num)
theorem B853157 : Blo 566810 853157 := bbase (se 4 (by rfl) ⟨79983, by rfl⟩ : syracuseStep 853157 = 159967) (by norm_num)
theorem B853181 : Blo 566810 853181 := bbase (se 3 (by rfl) ⟨159971, by rfl⟩ : syracuseStep 853181 = 319943) (by norm_num)
theorem B1443005 : Blo 566810 1443005 := bbase (se 3 (by rfl) ⟨270563, by rfl⟩ : syracuseStep 1443005 = 541127) (by norm_num)
theorem B722125 : Blo 566810 722125 := bbase (se 3 (by rfl) ⟨135398, by rfl⟩ : syracuseStep 722125 = 270797) (by norm_num)
theorem B853205 : Blo 566810 853205 := bbase (se 7 (by rfl) ⟨9998, by rfl⟩ : syracuseStep 853205 = 19997) (by norm_num)
theorem B5473493 : Blo 566810 5473493 := bbase (se 7 (by rfl) ⟨64142, by rfl⟩ : syracuseStep 5473493 = 128285) (by norm_num)
theorem B1279205 : Blo 566810 1279205 := bbase (se 4 (by rfl) ⟨119925, by rfl⟩ : syracuseStep 1279205 = 239851) (by norm_num)
theorem B853229 : Blo 566810 853229 := bbase (se 3 (by rfl) ⟨159980, by rfl⟩ : syracuseStep 853229 = 319961) (by norm_num)
theorem B853253 : Blo 566810 853253 := bbase (se 4 (by rfl) ⟨79992, by rfl⟩ : syracuseStep 853253 = 159985) (by norm_num)
theorem B1213717 : Blo 566810 1213717 := bbase (se 6 (by rfl) ⟨28446, by rfl⟩ : syracuseStep 1213717 = 56893) (by norm_num)
theorem B853277 : Blo 566810 853277 := bbase (se 3 (by rfl) ⟨159989, by rfl⟩ : syracuseStep 853277 = 319979) (by norm_num)
theorem B1279277 : Blo 566810 1279277 := bbase (se 3 (by rfl) ⟨239864, by rfl⟩ : syracuseStep 1279277 = 479729) (by norm_num)
theorem B853301 : Blo 566810 853301 := bbase (se 5 (by rfl) ⟨39998, by rfl⟩ : syracuseStep 853301 = 79997) (by norm_num)
theorem B853325 : Blo 566810 853325 := bbase (se 3 (by rfl) ⟨159998, by rfl⟩ : syracuseStep 853325 = 319997) (by norm_num)
theorem B1082717 : Blo 566810 1082717 := bbase (se 3 (by rfl) ⟨203009, by rfl⟩ : syracuseStep 1082717 = 406019) (by norm_num)
theorem B853349 : Blo 566810 853349 := bbase (se 4 (by rfl) ⟨80001, by rfl⟩ : syracuseStep 853349 = 160003) (by norm_num)
theorem B1279349 : Blo 566810 1279349 := bbase (se 5 (by rfl) ⟨59969, by rfl⟩ : syracuseStep 1279349 = 119939) (by norm_num)
theorem B722297 : Blo 566810 722297 := bbase (se 2 (by rfl) ⟨270861, by rfl⟩ : syracuseStep 722297 = 541723) (by norm_num)
theorem B853373 : Blo 566810 853373 := bbase (se 3 (by rfl) ⟨160007, by rfl⟩ : syracuseStep 853373 = 320015) (by norm_num)
theorem B1443197 : Blo 566810 1443197 := bbase (se 3 (by rfl) ⟨270599, by rfl⟩ : syracuseStep 1443197 = 541199) (by norm_num)
theorem B853397 : Blo 566810 853397 := bbase (se 6 (by rfl) ⟨20001, by rfl⟩ : syracuseStep 853397 = 40003) (by norm_num)
theorem B853421 : Blo 566810 853421 := bbase (se 3 (by rfl) ⟨160016, by rfl⟩ : syracuseStep 853421 = 320033) (by norm_num)
theorem B722353 : Blo 566810 722353 := bbase (se 2 (by rfl) ⟨270882, by rfl⟩ : syracuseStep 722353 = 541765) (by norm_num)
theorem B1279421 : Blo 566810 1279421 := bbase (se 3 (by rfl) ⟨239891, by rfl⟩ : syracuseStep 1279421 = 479783) (by norm_num)
theorem B853445 : Blo 566810 853445 := bbase (se 4 (by rfl) ⟨80010, by rfl⟩ : syracuseStep 853445 = 160021) (by norm_num)
theorem B6489557 : Blo 566810 6489557 := bbase (se 7 (by rfl) ⟨76049, by rfl⟩ : syracuseStep 6489557 = 152099) (by norm_num)
theorem B853469 : Blo 566810 853469 := bbase (se 3 (by rfl) ⟨160025, by rfl⟩ : syracuseStep 853469 = 320051) (by norm_num)
theorem B853493 : Blo 566810 853493 := bbase (se 5 (by rfl) ⟨40007, by rfl⟩ : syracuseStep 853493 = 80015) (by norm_num)
theorem B1279493 : Blo 566810 1279493 := bbase (se 4 (by rfl) ⟨119952, by rfl⟩ : syracuseStep 1279493 = 239905) (by norm_num)
theorem B853517 : Blo 566810 853517 := bbase (se 3 (by rfl) ⟨160034, by rfl⟩ : syracuseStep 853517 = 320069) (by norm_num)
theorem B853541 : Blo 566810 853541 := bbase (se 4 (by rfl) ⟨80019, by rfl⟩ : syracuseStep 853541 = 160039) (by norm_num)
theorem B853565 : Blo 566810 853565 := bbase (se 3 (by rfl) ⟨160043, by rfl⟩ : syracuseStep 853565 = 320087) (by norm_num)
theorem B1279565 : Blo 566810 1279565 := bbase (se 3 (by rfl) ⟨239918, by rfl⟩ : syracuseStep 1279565 = 479837) (by norm_num)
theorem B853589 : Blo 566810 853589 := bbase (se 8 (by rfl) ⟨5001, by rfl⟩ : syracuseStep 853589 = 10003) (by norm_num)
theorem B853613 : Blo 566810 853613 := bbase (se 3 (by rfl) ⟨160052, by rfl⟩ : syracuseStep 853613 = 320105) (by norm_num)
theorem B853637 : Blo 566810 853637 := bbase (se 4 (by rfl) ⟨80028, by rfl⟩ : syracuseStep 853637 = 160057) (by norm_num)
theorem B1279637 : Blo 566810 1279637 := bbase (se 6 (by rfl) ⟨29991, by rfl⟩ : syracuseStep 1279637 = 59983) (by norm_num)
theorem B853661 : Blo 566810 853661 := bbase (se 3 (by rfl) ⟨160061, by rfl⟩ : syracuseStep 853661 = 320123) (by norm_num)
theorem B853685 : Blo 566810 853685 := bbase (se 5 (by rfl) ⟨40016, by rfl⟩ : syracuseStep 853685 = 80033) (by norm_num)
theorem B853709 : Blo 566810 853709 := bbase (se 3 (by rfl) ⟨160070, by rfl⟩ : syracuseStep 853709 = 320141) (by norm_num)
theorem B1443541 : Blo 566810 1443541 := bbase (se 7 (by rfl) ⟨16916, by rfl⟩ : syracuseStep 1443541 = 33833) (by norm_num)
theorem B1279709 : Blo 566810 1279709 := bbase (se 3 (by rfl) ⟨239945, by rfl⟩ : syracuseStep 1279709 = 479891) (by norm_num)
theorem B853733 : Blo 566810 853733 := bbase (se 4 (by rfl) ⟨80037, by rfl⟩ : syracuseStep 853733 = 160075) (by norm_num)
theorem B853757 : Blo 566810 853757 := bbase (se 3 (by rfl) ⟨160079, by rfl⟩ : syracuseStep 853757 = 320159) (by norm_num)
theorem B2885381 : Blo 566810 2885381 := bbase (se 4 (by rfl) ⟨270504, by rfl⟩ : syracuseStep 2885381 = 541009) (by norm_num)
theorem B853781 : Blo 566810 853781 := bbase (se 6 (by rfl) ⟨20010, by rfl⟩ : syracuseStep 853781 = 40021) (by norm_num)
theorem B1279781 : Blo 566810 1279781 := bbase (se 4 (by rfl) ⟨119979, by rfl⟩ : syracuseStep 1279781 = 239959) (by norm_num)
theorem B853805 : Blo 566810 853805 := bbase (se 3 (by rfl) ⟨160088, by rfl⟩ : syracuseStep 853805 = 320177) (by norm_num)
theorem B853829 : Blo 566810 853829 := bbase (se 4 (by rfl) ⟨80046, by rfl⟩ : syracuseStep 853829 = 160093) (by norm_num)
theorem B1443653 : Blo 566810 1443653 := bbase (se 4 (by rfl) ⟨135342, by rfl⟩ : syracuseStep 1443653 = 270685) (by norm_num)
theorem B853853 : Blo 566810 853853 := bbase (se 3 (by rfl) ⟨160097, by rfl⟩ : syracuseStep 853853 = 320195) (by norm_num)
theorem B1279853 : Blo 566810 1279853 := bbase (se 3 (by rfl) ⟨239972, by rfl⟩ : syracuseStep 1279853 = 479945) (by norm_num)
theorem B853877 : Blo 566810 853877 := bbase (se 5 (by rfl) ⟨40025, by rfl⟩ : syracuseStep 853877 = 80051) (by norm_num)
theorem B853901 : Blo 566810 853901 := bbase (se 3 (by rfl) ⟨160106, by rfl⟩ : syracuseStep 853901 = 320213) (by norm_num)
theorem B1542037 : Blo 566810 1542037 := bbase (se 6 (by rfl) ⟨36141, by rfl⟩ : syracuseStep 1542037 = 72283) (by norm_num)
theorem B853925 : Blo 566810 853925 := bbase (se 4 (by rfl) ⟨80055, by rfl⟩ : syracuseStep 853925 = 160111) (by norm_num)
theorem B1279925 : Blo 566810 1279925 := bbase (se 5 (by rfl) ⟨59996, by rfl⟩ : syracuseStep 1279925 = 119993) (by norm_num)
theorem B853949 : Blo 566810 853949 := bbase (se 3 (by rfl) ⟨160115, by rfl⟩ : syracuseStep 853949 = 320231) (by norm_num)
theorem B853973 : Blo 566810 853973 := bbase (se 7 (by rfl) ⟨10007, by rfl⟩ : syracuseStep 853973 = 20015) (by norm_num)
theorem B853997 : Blo 566810 853997 := bbase (se 3 (by rfl) ⟨160124, by rfl⟩ : syracuseStep 853997 = 320249) (by norm_num)
theorem B1279997 : Blo 566810 1279997 := bbase (se 3 (by rfl) ⟨239999, by rfl⟩ : syracuseStep 1279997 = 479999) (by norm_num)
theorem B854021 : Blo 566810 854021 := bbase (se 4 (by rfl) ⟨80064, by rfl⟩ : syracuseStep 854021 = 160129) (by norm_num)
theorem B1443845 : Blo 566810 1443845 := bbase (se 4 (by rfl) ⟨135360, by rfl⟩ : syracuseStep 1443845 = 270721) (by norm_num)
theorem B3246101 : Blo 566810 3246101 := bbase (se 6 (by rfl) ⟨76080, by rfl⟩ : syracuseStep 3246101 = 152161) (by norm_num)
theorem B854045 : Blo 566810 854045 := bbase (se 3 (by rfl) ⟨160133, by rfl⟩ : syracuseStep 854045 = 320267) (by norm_num)
theorem B854069 : Blo 566810 854069 := bbase (se 5 (by rfl) ⟨40034, by rfl⟩ : syracuseStep 854069 = 80069) (by norm_num)
theorem B1280069 : Blo 566810 1280069 := bbase (se 4 (by rfl) ⟨120006, by rfl⟩ : syracuseStep 1280069 = 240013) (by norm_num)
theorem B854093 : Blo 566810 854093 := bbase (se 3 (by rfl) ⟨160142, by rfl⟩ : syracuseStep 854093 = 320285) (by norm_num)
theorem B1083469 : Blo 566810 1083469 := bbase (se 3 (by rfl) ⟨203150, by rfl⟩ : syracuseStep 1083469 = 406301) (by norm_num)
theorem B854117 : Blo 566810 854117 := bbase (se 4 (by rfl) ⟨80073, by rfl⟩ : syracuseStep 854117 = 160147) (by norm_num)
theorem B854141 : Blo 566810 854141 := bbase (se 3 (by rfl) ⟨160151, by rfl⟩ : syracuseStep 854141 = 320303) (by norm_num)
theorem B1214605 : Blo 566810 1214605 := bbase (se 3 (by rfl) ⟨227738, by rfl⟩ : syracuseStep 1214605 = 455477) (by norm_num)
theorem B1280141 : Blo 566810 1280141 := bbase (se 3 (by rfl) ⟨240026, by rfl⟩ : syracuseStep 1280141 = 480053) (by norm_num)
theorem B854165 : Blo 566810 854165 := bbase (se 6 (by rfl) ⟨20019, by rfl⟩ : syracuseStep 854165 = 40039) (by norm_num)
theorem B854189 : Blo 566810 854189 := bbase (se 3 (by rfl) ⟨160160, by rfl⟩ : syracuseStep 854189 = 320321) (by norm_num)
theorem B854213 : Blo 566810 854213 := bbase (se 4 (by rfl) ⟨80082, by rfl⟩ : syracuseStep 854213 = 160165) (by norm_num)
theorem B1542341 : Blo 566810 1542341 := bbase (se 4 (by rfl) ⟨144594, by rfl⟩ : syracuseStep 1542341 = 289189) (by norm_num)
theorem B1280213 : Blo 566810 1280213 := bbase (se 7 (by rfl) ⟨15002, by rfl⟩ : syracuseStep 1280213 = 30005) (by norm_num)
theorem B854237 : Blo 566810 854237 := bbase (se 3 (by rfl) ⟨160169, by rfl⟩ : syracuseStep 854237 = 320339) (by norm_num)
theorem B1083613 : Blo 566810 1083613 := bbase (se 3 (by rfl) ⟨203177, by rfl⟩ : syracuseStep 1083613 = 406355) (by norm_num)
theorem B854261 : Blo 566810 854261 := bbase (se 5 (by rfl) ⟨40043, by rfl⟩ : syracuseStep 854261 = 80087) (by norm_num)
theorem B854285 : Blo 566810 854285 := bbase (se 3 (by rfl) ⟨160178, by rfl⟩ : syracuseStep 854285 = 320357) (by norm_num)
theorem B1280285 : Blo 566810 1280285 := bbase (se 3 (by rfl) ⟨240053, by rfl⟩ : syracuseStep 1280285 = 480107) (by norm_num)
theorem B854309 : Blo 566810 854309 := bbase (se 4 (by rfl) ⟨80091, by rfl⟩ : syracuseStep 854309 = 160183) (by norm_num)
theorem B854333 : Blo 566810 854333 := bbase (se 3 (by rfl) ⟨160187, by rfl⟩ : syracuseStep 854333 = 320375) (by norm_num)
theorem B854357 : Blo 566810 854357 := bbase (se 10 (by rfl) ⟨1251, by rfl⟩ : syracuseStep 854357 = 2503) (by norm_num)
theorem B1444189 : Blo 566810 1444189 := bbase (se 3 (by rfl) ⟨270785, by rfl⟩ : syracuseStep 1444189 = 541571) (by norm_num)
theorem B1280357 : Blo 566810 1280357 := bbase (se 4 (by rfl) ⟨120033, by rfl⟩ : syracuseStep 1280357 = 240067) (by norm_num)
theorem B854381 : Blo 566810 854381 := bbase (se 3 (by rfl) ⟨160196, by rfl⟩ : syracuseStep 854381 = 320393) (by norm_num)
theorem B854405 : Blo 566810 854405 := bbase (se 4 (by rfl) ⟨80100, by rfl⟩ : syracuseStep 854405 = 160201) (by norm_num)
theorem B4327829 : Blo 566810 4327829 := bbase (se 6 (by rfl) ⟨101433, by rfl⟩ : syracuseStep 4327829 = 202867) (by norm_num)
theorem B3082645 : Blo 566810 3082645 := bbase (se 6 (by rfl) ⟨72249, by rfl⟩ : syracuseStep 3082645 = 144499) (by norm_num)
theorem B854429 : Blo 566810 854429 := bbase (se 3 (by rfl) ⟨160205, by rfl⟩ : syracuseStep 854429 = 320411) (by norm_num)
theorem B1280429 : Blo 566810 1280429 := bbase (se 3 (by rfl) ⟨240080, by rfl⟩ : syracuseStep 1280429 = 480161) (by norm_num)
theorem B854453 : Blo 566810 854453 := bbase (se 5 (by rfl) ⟨40052, by rfl⟩ : syracuseStep 854453 = 80105) (by norm_num)
theorem B854477 : Blo 566810 854477 := bbase (se 3 (by rfl) ⟨160214, by rfl⟩ : syracuseStep 854477 = 320429) (by norm_num)
theorem B1444301 : Blo 566810 1444301 := bbase (se 3 (by rfl) ⟨270806, by rfl⟩ : syracuseStep 1444301 = 541613) (by norm_num)
theorem B854501 : Blo 566810 854501 := bbase (se 4 (by rfl) ⟨80109, by rfl⟩ : syracuseStep 854501 = 160219) (by norm_num)
theorem B1280501 : Blo 566810 1280501 := bbase (se 5 (by rfl) ⟨60023, by rfl⟩ : syracuseStep 1280501 = 120047) (by norm_num)
theorem B2165237 : Blo 566810 2165237 := bbase (se 5 (by rfl) ⟨101495, by rfl⟩ : syracuseStep 2165237 = 202991) (by norm_num)
theorem B854525 : Blo 566810 854525 := bbase (se 3 (by rfl) ⟨160223, by rfl⟩ : syracuseStep 854525 = 320447) (by norm_num)
theorem B854549 : Blo 566810 854549 := bbase (se 6 (by rfl) ⟨20028, by rfl⟩ : syracuseStep 854549 = 40057) (by norm_num)
theorem B854573 : Blo 566810 854573 := bbase (se 3 (by rfl) ⟨160232, by rfl⟩ : syracuseStep 854573 = 320465) (by norm_num)
theorem B1280573 : Blo 566810 1280573 := bbase (se 3 (by rfl) ⟨240107, by rfl⟩ : syracuseStep 1280573 = 480215) (by norm_num)
theorem B854597 : Blo 566810 854597 := bbase (se 4 (by rfl) ⟨80118, by rfl⟩ : syracuseStep 854597 = 160237) (by norm_num)
theorem B854621 : Blo 566810 854621 := bbase (se 3 (by rfl) ⟨160241, by rfl⟩ : syracuseStep 854621 = 320483) (by norm_num)
theorem B854645 : Blo 566810 854645 := bbase (se 5 (by rfl) ⟨40061, by rfl⟩ : syracuseStep 854645 = 80123) (by norm_num)
theorem B1215101 : Blo 566810 1215101 := bbase (se 3 (by rfl) ⟨227831, by rfl⟩ : syracuseStep 1215101 = 455663) (by norm_num)
theorem B1280645 : Blo 566810 1280645 := bbase (se 4 (by rfl) ⟨120060, by rfl⟩ : syracuseStep 1280645 = 240121) (by norm_num)
theorem B854669 : Blo 566810 854669 := bbase (se 3 (by rfl) ⟨160250, by rfl⟩ : syracuseStep 854669 = 320501) (by norm_num)
theorem B1444493 : Blo 566810 1444493 := bbase (se 3 (by rfl) ⟨270842, by rfl⟩ : syracuseStep 1444493 = 541685) (by norm_num)
theorem B854693 : Blo 566810 854693 := bbase (se 4 (by rfl) ⟨80127, by rfl⟩ : syracuseStep 854693 = 160255) (by norm_num)
theorem B854717 : Blo 566810 854717 := bbase (se 3 (by rfl) ⟨160259, by rfl⟩ : syracuseStep 854717 = 320519) (by norm_num)
theorem B1280717 : Blo 566810 1280717 := bbase (se 3 (by rfl) ⟨240134, by rfl⟩ : syracuseStep 1280717 = 480269) (by norm_num)
theorem B854741 : Blo 566810 854741 := bbase (se 7 (by rfl) ⟨10016, by rfl⟩ : syracuseStep 854741 = 20033) (by norm_num)
theorem B854765 : Blo 566810 854765 := bbase (se 3 (by rfl) ⟨160268, by rfl⟩ : syracuseStep 854765 = 320537) (by norm_num)
theorem B854789 : Blo 566810 854789 := bbase (se 4 (by rfl) ⟨80136, by rfl⟩ : syracuseStep 854789 = 160273) (by norm_num)
theorem B1280789 : Blo 566810 1280789 := bbase (se 6 (by rfl) ⟨30018, by rfl⟩ : syracuseStep 1280789 = 60037) (by norm_num)
theorem B2165525 : Blo 566810 2165525 := bbase (se 6 (by rfl) ⟨50754, by rfl⟩ : syracuseStep 2165525 = 101509) (by norm_num)
theorem B854813 : Blo 566810 854813 := bbase (se 3 (by rfl) ⟨160277, by rfl⟩ : syracuseStep 854813 = 320555) (by norm_num)
theorem B658217 : Blo 566810 658217 := bbase (se 2 (by rfl) ⟨246831, by rfl⟩ : syracuseStep 658217 = 493663) (by norm_num)
theorem B854837 : Blo 566810 854837 := bbase (se 5 (by rfl) ⟨40070, by rfl⟩ : syracuseStep 854837 = 80141) (by norm_num)
theorem B854861 : Blo 566810 854861 := bbase (se 3 (by rfl) ⟨160286, by rfl⟩ : syracuseStep 854861 = 320573) (by norm_num)
theorem B1280861 : Blo 566810 1280861 := bbase (se 3 (by rfl) ⟨240161, by rfl⟩ : syracuseStep 1280861 = 480323) (by norm_num)
theorem B854885 : Blo 566810 854885 := bbase (se 4 (by rfl) ⟨80145, by rfl⟩ : syracuseStep 854885 = 160291) (by norm_num)
theorem B854909 : Blo 566810 854909 := bbase (se 3 (by rfl) ⟨160295, by rfl⟩ : syracuseStep 854909 = 320591) (by norm_num)
theorem B854933 : Blo 566810 854933 := bbase (se 6 (by rfl) ⟨20037, by rfl⟩ : syracuseStep 854933 = 40075) (by norm_num)
theorem B1280933 : Blo 566810 1280933 := bbase (se 4 (by rfl) ⟨120087, by rfl⟩ : syracuseStep 1280933 = 240175) (by norm_num)
theorem B854957 : Blo 566810 854957 := bbase (se 3 (by rfl) ⟨160304, by rfl⟩ : syracuseStep 854957 = 320609) (by norm_num)
theorem B854981 : Blo 566810 854981 := bbase (se 4 (by rfl) ⟨80154, by rfl⟩ : syracuseStep 854981 = 160309) (by norm_num)
theorem B855005 : Blo 566810 855005 := bbase (se 3 (by rfl) ⟨160313, by rfl⟩ : syracuseStep 855005 = 320627) (by norm_num)
theorem B1444837 : Blo 566810 1444837 := bbase (se 4 (by rfl) ⟨135453, by rfl⟩ : syracuseStep 1444837 = 270907) (by norm_num)
theorem B1281005 : Blo 566810 1281005 := bbase (se 3 (by rfl) ⟨240188, by rfl⟩ : syracuseStep 1281005 = 480377) (by norm_num)
theorem B855029 : Blo 566810 855029 := bbase (se 5 (by rfl) ⟨40079, by rfl⟩ : syracuseStep 855029 = 80159) (by norm_num)
theorem B855053 : Blo 566810 855053 := bbase (se 3 (by rfl) ⟨160322, by rfl⟩ : syracuseStep 855053 = 320645) (by norm_num)
theorem B2886677 : Blo 566810 2886677 := bbase (se 6 (by rfl) ⟨67656, by rfl⟩ : syracuseStep 2886677 = 135313) (by norm_num)
theorem B855077 : Blo 566810 855077 := bbase (se 4 (by rfl) ⟨80163, by rfl⟩ : syracuseStep 855077 = 160327) (by norm_num)
theorem B1281077 : Blo 566810 1281077 := bbase (se 5 (by rfl) ⟨60050, by rfl⟩ : syracuseStep 1281077 = 120101) (by norm_num)
theorem B855101 : Blo 566810 855101 := bbase (se 3 (by rfl) ⟨160331, by rfl⟩ : syracuseStep 855101 = 320663) (by norm_num)
theorem B855125 : Blo 566810 855125 := bbase (se 8 (by rfl) ⟨5010, by rfl⟩ : syracuseStep 855125 = 10021) (by norm_num)
theorem B855149 : Blo 566810 855149 := bbase (se 3 (by rfl) ⟨160340, by rfl⟩ : syracuseStep 855149 = 320681) (by norm_num)
theorem B1281149 : Blo 566810 1281149 := bbase (se 3 (by rfl) ⟨240215, by rfl⟩ : syracuseStep 1281149 = 480431) (by norm_num)
theorem B855173 : Blo 566810 855173 := bbase (se 4 (by rfl) ⟨80172, by rfl⟩ : syracuseStep 855173 = 160345) (by norm_num)
theorem B855197 : Blo 566810 855197 := bbase (se 3 (by rfl) ⟨160349, by rfl⟩ : syracuseStep 855197 = 320699) (by norm_num)
theorem B855221 : Blo 566810 855221 := bbase (se 5 (by rfl) ⟨40088, by rfl⟩ : syracuseStep 855221 = 80177) (by norm_num)
theorem B1281221 : Blo 566810 1281221 := bbase (se 4 (by rfl) ⟨120114, by rfl⟩ : syracuseStep 1281221 = 240229) (by norm_num)
theorem B855245 : Blo 566810 855245 := bbase (se 3 (by rfl) ⟨160358, by rfl⟩ : syracuseStep 855245 = 320717) (by norm_num)
theorem B855269 : Blo 566810 855269 := bbase (se 4 (by rfl) ⟨80181, by rfl⟩ : syracuseStep 855269 = 160363) (by norm_num)
theorem B855293 : Blo 566810 855293 := bbase (se 3 (by rfl) ⟨160367, by rfl⟩ : syracuseStep 855293 = 320735) (by norm_num)
theorem B1281293 : Blo 566810 1281293 := bbase (se 3 (by rfl) ⟨240242, by rfl⟩ : syracuseStep 1281293 = 480485) (by norm_num)
theorem B855317 : Blo 566810 855317 := bbase (se 6 (by rfl) ⟨20046, by rfl⟩ : syracuseStep 855317 = 40093) (by norm_num)
theorem B855341 : Blo 566810 855341 := bbase (se 3 (by rfl) ⟨160376, by rfl⟩ : syracuseStep 855341 = 320753) (by norm_num)
theorem B855365 : Blo 566810 855365 := bbase (se 4 (by rfl) ⟨80190, by rfl⟩ : syracuseStep 855365 = 160381) (by norm_num)
theorem B52596053 : Blo 566810 52596053 := bbase (se 11 (by rfl) ⟨38522, by rfl⟩ : syracuseStep 52596053 = 77045) (by norm_num)
theorem B1281365 : Blo 566810 1281365 := bbase (se 11 (by rfl) ⟨938, by rfl⟩ : syracuseStep 1281365 = 1877) (by norm_num)
theorem B855389 : Blo 566810 855389 := bbase (se 3 (by rfl) ⟨160385, by rfl⟩ : syracuseStep 855389 = 320771) (by norm_num)
theorem B855413 : Blo 566810 855413 := bbase (se 5 (by rfl) ⟨40097, by rfl⟩ : syracuseStep 855413 = 80195) (by norm_num)
theorem B855437 : Blo 566810 855437 := bbase (se 3 (by rfl) ⟨160394, by rfl⟩ : syracuseStep 855437 = 320789) (by norm_num)
theorem B10390933 : Blo 566810 10390933 := bbase (se 6 (by rfl) ⟨243537, by rfl⟩ : syracuseStep 10390933 = 487075) (by norm_num)
theorem B1478045 : Blo 566810 1478045 := bbase (se 3 (by rfl) ⟨277133, by rfl⟩ : syracuseStep 1478045 = 554267) (by norm_num)
theorem B1281437 : Blo 566810 1281437 := bbase (se 3 (by rfl) ⟨240269, by rfl⟩ : syracuseStep 1281437 = 480539) (by norm_num)
theorem B855461 : Blo 566810 855461 := bbase (se 4 (by rfl) ⟨80199, by rfl⟩ : syracuseStep 855461 = 160399) (by norm_num)
theorem B855485 : Blo 566810 855485 := bbase (se 3 (by rfl) ⟨160403, by rfl⟩ : syracuseStep 855485 = 320807) (by norm_num)
theorem B7769557 : Blo 566810 7769557 := bbase (se 7 (by rfl) ⟨91049, by rfl⟩ : syracuseStep 7769557 = 182099) (by norm_num)
theorem B1641941 : Blo 566810 1641941 := bbase (se 7 (by rfl) ⟨19241, by rfl⟩ : syracuseStep 1641941 = 38483) (by norm_num)
theorem B855509 : Blo 566810 855509 := bbase (se 7 (by rfl) ⟨10025, by rfl⟩ : syracuseStep 855509 = 20051) (by norm_num)
theorem B1215965 : Blo 566810 1215965 := bbase (se 3 (by rfl) ⟨227993, by rfl⟩ : syracuseStep 1215965 = 455987) (by norm_num)
theorem B1281509 : Blo 566810 1281509 := bbase (se 4 (by rfl) ⟨120141, by rfl⟩ : syracuseStep 1281509 = 240283) (by norm_num)
theorem B855533 : Blo 566810 855533 := bbase (se 3 (by rfl) ⟨160412, by rfl⟩ : syracuseStep 855533 = 320825) (by norm_num)
theorem B855557 : Blo 566810 855557 := bbase (se 4 (by rfl) ⟨80208, by rfl⟩ : syracuseStep 855557 = 160417) (by norm_num)
theorem B855581 : Blo 566810 855581 := bbase (se 3 (by rfl) ⟨160421, by rfl⟩ : syracuseStep 855581 = 320843) (by norm_num)
theorem B1281581 : Blo 566810 1281581 := bbase (se 3 (by rfl) ⟨240296, by rfl⟩ : syracuseStep 1281581 = 480593) (by norm_num)
theorem B855605 : Blo 566810 855605 := bbase (se 5 (by rfl) ⟨40106, by rfl⟩ : syracuseStep 855605 = 80213) (by norm_num)
theorem B855629 : Blo 566810 855629 := bbase (se 3 (by rfl) ⟨160430, by rfl⟩ : syracuseStep 855629 = 320861) (by norm_num)
theorem B855653 : Blo 566810 855653 := bbase (se 4 (by rfl) ⟨80217, by rfl⟩ : syracuseStep 855653 = 160435) (by norm_num)
theorem B1216109 : Blo 566810 1216109 := bbase (se 3 (by rfl) ⟨228020, by rfl⟩ : syracuseStep 1216109 = 456041) (by norm_num)
theorem B1281653 : Blo 566810 1281653 := bbase (se 5 (by rfl) ⟨60077, by rfl⟩ : syracuseStep 1281653 = 120155) (by norm_num)
theorem B855677 : Blo 566810 855677 := bbase (se 3 (by rfl) ⟨160439, by rfl⟩ : syracuseStep 855677 = 320879) (by norm_num)
theorem B855701 : Blo 566810 855701 := bbase (se 6 (by rfl) ⟨20055, by rfl⟩ : syracuseStep 855701 = 40111) (by norm_num)
theorem B855725 : Blo 566810 855725 := bbase (se 3 (by rfl) ⟨160448, by rfl⟩ : syracuseStep 855725 = 320897) (by norm_num)
theorem B1281725 : Blo 566810 1281725 := bbase (se 3 (by rfl) ⟨240323, by rfl⟩ : syracuseStep 1281725 = 480647) (by norm_num)
theorem B855749 : Blo 566810 855749 := bbase (se 4 (by rfl) ⟨80226, by rfl⟩ : syracuseStep 855749 = 160453) (by norm_num)
theorem B855773 : Blo 566810 855773 := bbase (se 3 (by rfl) ⟨160457, by rfl⟩ : syracuseStep 855773 = 320915) (by norm_num)
theorem B855797 : Blo 566810 855797 := bbase (se 5 (by rfl) ⟨40115, by rfl⟩ : syracuseStep 855797 = 80231) (by norm_num)
theorem B1281797 : Blo 566810 1281797 := bbase (se 4 (by rfl) ⟨120168, by rfl⟩ : syracuseStep 1281797 = 240337) (by norm_num)
theorem B855821 : Blo 566810 855821 := bbase (se 3 (by rfl) ⟨160466, by rfl⟩ : syracuseStep 855821 = 320933) (by norm_num)
theorem B855845 : Blo 566810 855845 := bbase (se 4 (by rfl) ⟨80235, by rfl⟩ : syracuseStep 855845 = 160471) (by norm_num)
theorem B1052461 : Blo 566810 1052461 := bbase (se 3 (by rfl) ⟨197336, by rfl⟩ : syracuseStep 1052461 = 394673) (by norm_num)
theorem B855869 : Blo 566810 855869 := bbase (se 3 (by rfl) ⟨160475, by rfl⟩ : syracuseStep 855869 = 320951) (by norm_num)
theorem B1281869 : Blo 566810 1281869 := bbase (se 3 (by rfl) ⟨240350, by rfl⟩ : syracuseStep 1281869 = 480701) (by norm_num)
theorem B855893 : Blo 566810 855893 := bbase (se 9 (by rfl) ⟨2507, by rfl⟩ : syracuseStep 855893 = 5015) (by norm_num)
theorem B855917 : Blo 566810 855917 := bbase (se 3 (by rfl) ⟨160484, by rfl⟩ : syracuseStep 855917 = 320969) (by norm_num)
theorem B855941 : Blo 566810 855941 := bbase (se 4 (by rfl) ⟨80244, by rfl⟩ : syracuseStep 855941 = 160489) (by norm_num)
theorem B1281941 : Blo 566810 1281941 := bbase (se 6 (by rfl) ⟨30045, by rfl⟩ : syracuseStep 1281941 = 60091) (by norm_num)
theorem B855965 : Blo 566810 855965 := bbase (se 3 (by rfl) ⟨160493, by rfl⟩ : syracuseStep 855965 = 320987) (by norm_num)
theorem B2166709 : Blo 566810 2166709 := bbase (se 5 (by rfl) ⟨101564, by rfl⟩ : syracuseStep 2166709 = 203129) (by norm_num)
theorem B855989 : Blo 566810 855989 := bbase (se 5 (by rfl) ⟨40124, by rfl⟩ : syracuseStep 855989 = 80249) (by norm_num)
theorem B856013 : Blo 566810 856013 := bbase (se 3 (by rfl) ⟨160502, by rfl⟩ : syracuseStep 856013 = 321005) (by norm_num)
theorem B1282013 : Blo 566810 1282013 := bbase (se 3 (by rfl) ⟨240377, by rfl⟩ : syracuseStep 1282013 = 480755) (by norm_num)
theorem B856037 : Blo 566810 856037 := bbase (se 4 (by rfl) ⟨80253, by rfl⟩ : syracuseStep 856037 = 160507) (by norm_num)
theorem B856061 : Blo 566810 856061 := bbase (se 3 (by rfl) ⟨160511, by rfl⟩ : syracuseStep 856061 = 321023) (by norm_num)
theorem B856085 : Blo 566810 856085 := bbase (se 6 (by rfl) ⟨20064, by rfl⟩ : syracuseStep 856085 = 40129) (by norm_num)
theorem B1282085 : Blo 566810 1282085 := bbase (se 4 (by rfl) ⟨120195, by rfl⟩ : syracuseStep 1282085 = 240391) (by norm_num)
theorem B856109 : Blo 566810 856109 := bbase (se 3 (by rfl) ⟨160520, by rfl⟩ : syracuseStep 856109 = 321041) (by norm_num)
theorem B856133 : Blo 566810 856133 := bbase (se 4 (by rfl) ⟨80262, by rfl⟩ : syracuseStep 856133 = 160525) (by norm_num)
theorem B1478741 : Blo 566810 1478741 := bbase (se 8 (by rfl) ⟨8664, by rfl⟩ : syracuseStep 1478741 = 17329) (by norm_num)
theorem B856157 : Blo 566810 856157 := bbase (se 3 (by rfl) ⟨160529, by rfl⟩ : syracuseStep 856157 = 321059) (by norm_num)
theorem B1282157 : Blo 566810 1282157 := bbase (se 3 (by rfl) ⟨240404, by rfl⟩ : syracuseStep 1282157 = 480809) (by norm_num)
theorem B856181 : Blo 566810 856181 := bbase (se 5 (by rfl) ⟨40133, by rfl⟩ : syracuseStep 856181 = 80267) (by norm_num)
theorem B856205 : Blo 566810 856205 := bbase (se 3 (by rfl) ⟨160538, by rfl⟩ : syracuseStep 856205 = 321077) (by norm_num)
theorem B1282229 : Blo 566810 1282229 := bbase (se 5 (by rfl) ⟨60104, by rfl⟩ : syracuseStep 1282229 = 120209) (by norm_num)
theorem B2167013 : Blo 566810 2167013 := bbase (se 4 (by rfl) ⟨203157, by rfl⟩ : syracuseStep 2167013 = 406315) (by norm_num)
theorem B1282301 : Blo 566810 1282301 := bbase (se 3 (by rfl) ⟨240431, by rfl⟩ : syracuseStep 1282301 = 480863) (by norm_num)
theorem B2887973 : Blo 566810 2887973 := bbase (se 4 (by rfl) ⟨270747, by rfl⟩ : syracuseStep 2887973 = 541495) (by norm_num)
theorem B5902645 : Blo 566810 5902645 := bbase (se 5 (by rfl) ⟨276686, by rfl⟩ : syracuseStep 5902645 = 553373) (by norm_num)
theorem B1282373 : Blo 566810 1282373 := bbase (se 4 (by rfl) ⟨120222, by rfl⟩ : syracuseStep 1282373 = 240445) (by norm_num)
theorem B1216853 : Blo 566810 1216853 := bbase (se 10 (by rfl) ⟨1782, by rfl⟩ : syracuseStep 1216853 = 3565) (by norm_num)
theorem B1282445 : Blo 566810 1282445 := bbase (se 3 (by rfl) ⟨240458, by rfl⟩ : syracuseStep 1282445 = 480917) (by norm_num)
theorem B1282517 : Blo 566810 1282517 := bbase (se 7 (by rfl) ⟨15029, by rfl⟩ : syracuseStep 1282517 = 30059) (by norm_num)
theorem B1282589 : Blo 566810 1282589 := bbase (se 3 (by rfl) ⟨240485, by rfl⟩ : syracuseStep 1282589 = 480971) (by norm_num)
theorem B1151533 : Blo 566810 1151533 := bbase (se 3 (by rfl) ⟨215912, by rfl⟩ : syracuseStep 1151533 = 431825) (by norm_num)
theorem B1151581 : Blo 566810 1151581 := bbase (se 3 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 1151581 = 431843) (by norm_num)
theorem B1282661 : Blo 566810 1282661 := bbase (se 4 (by rfl) ⟨120249, by rfl⟩ : syracuseStep 1282661 = 240499) (by norm_num)
theorem B1151597 : Blo 566810 1151597 := bbase (se 3 (by rfl) ⟨215924, by rfl⟩ : syracuseStep 1151597 = 431849) (by norm_num)
theorem B1282733 : Blo 566810 1282733 := bbase (se 3 (by rfl) ⟨240512, by rfl⟩ : syracuseStep 1282733 = 481025) (by norm_num)
theorem B2429621 : Blo 566810 2429621 := bbase (se 5 (by rfl) ⟨113888, by rfl⟩ : syracuseStep 2429621 = 227777) (by norm_num)
theorem B1282805 : Blo 566810 1282805 := bbase (se 5 (by rfl) ⟨60131, by rfl⟩ : syracuseStep 1282805 = 120263) (by norm_num)
theorem B1282877 : Blo 566810 1282877 := bbase (se 3 (by rfl) ⟨240539, by rfl⟩ : syracuseStep 1282877 = 481079) (by norm_num)
theorem B1282949 : Blo 566810 1282949 := bbase (se 4 (by rfl) ⟨120276, by rfl⟩ : syracuseStep 1282949 = 240553) (by norm_num)
theorem B1283021 : Blo 566810 1283021 := bbase (se 3 (by rfl) ⟨240566, by rfl⟩ : syracuseStep 1283021 = 481133) (by norm_num)
theorem B1283093 : Blo 566810 1283093 := bbase (se 6 (by rfl) ⟨30072, by rfl⟩ : syracuseStep 1283093 = 60145) (by norm_num)
theorem B1217605 : Blo 566810 1217605 := bbase (se 4 (by rfl) ⟨114150, by rfl⟩ : syracuseStep 1217605 = 228301) (by norm_num)
theorem B1283165 : Blo 566810 1283165 := bbase (se 3 (by rfl) ⟨240593, by rfl⟩ : syracuseStep 1283165 = 481187) (by norm_num)
theorem B1283237 : Blo 566810 1283237 := bbase (se 4 (by rfl) ⟨120303, by rfl⟩ : syracuseStep 1283237 = 240607) (by norm_num)
theorem B1217749 : Blo 566810 1217749 := bbase (se 7 (by rfl) ⟨14270, by rfl⟩ : syracuseStep 1217749 = 28541) (by norm_num)
theorem B1283309 : Blo 566810 1283309 := bbase (se 3 (by rfl) ⟨240620, by rfl⟩ : syracuseStep 1283309 = 481241) (by norm_num)
theorem B1283381 : Blo 566810 1283381 := bbase (se 5 (by rfl) ⟨60158, by rfl⟩ : syracuseStep 1283381 = 120317) (by norm_num)
theorem B1283453 : Blo 566810 1283453 := bbase (se 3 (by rfl) ⟨240647, by rfl⟩ : syracuseStep 1283453 = 481295) (by norm_num)
theorem B1283525 : Blo 566810 1283525 := bbase (se 4 (by rfl) ⟨120330, by rfl⟩ : syracuseStep 1283525 = 240661) (by norm_num)
theorem B1283597 : Blo 566810 1283597 := bbase (se 3 (by rfl) ⟨240674, by rfl⟩ : syracuseStep 1283597 = 481349) (by norm_num)
theorem B2889269 : Blo 566810 2889269 := bbase (se 5 (by rfl) ⟨135434, by rfl⟩ : syracuseStep 2889269 = 270869) (by norm_num)
theorem B1218125 : Blo 566810 1218125 := bbase (se 3 (by rfl) ⟨228398, by rfl⟩ : syracuseStep 1218125 = 456797) (by norm_num)
theorem B1283669 : Blo 566810 1283669 := bbase (se 8 (by rfl) ⟨7521, by rfl⟩ : syracuseStep 1283669 = 15043) (by norm_num)
theorem B1283741 : Blo 566810 1283741 := bbase (se 3 (by rfl) ⟨240701, by rfl⟩ : syracuseStep 1283741 = 481403) (by norm_num)
theorem B1283813 : Blo 566810 1283813 := bbase (se 4 (by rfl) ⟨120357, by rfl⟩ : syracuseStep 1283813 = 240715) (by norm_num)
theorem B1152797 : Blo 566810 1152797 := bbase (se 3 (by rfl) ⟨216149, by rfl⟩ : syracuseStep 1152797 = 432299) (by norm_num)
theorem B1283885 : Blo 566810 1283885 := bbase (se 3 (by rfl) ⟨240728, by rfl⟩ : syracuseStep 1283885 = 481457) (by norm_num)
theorem B2463605 : Blo 566810 2463605 := bbase (se 5 (by rfl) ⟨115481, by rfl⟩ : syracuseStep 2463605 = 230963) (by norm_num)
theorem B1283957 : Blo 566810 1283957 := bbase (se 5 (by rfl) ⟨60185, by rfl⟩ : syracuseStep 1283957 = 120371) (by norm_num)
theorem B1218493 : Blo 566810 1218493 := bbase (se 3 (by rfl) ⟨228467, by rfl⟩ : syracuseStep 1218493 = 456935) (by norm_num)
theorem B1284029 : Blo 566810 1284029 := bbase (se 3 (by rfl) ⟨240755, by rfl⟩ : syracuseStep 1284029 = 481511) (by norm_num)
theorem B1284101 : Blo 566810 1284101 := bbase (se 4 (by rfl) ⟨120384, by rfl⟩ : syracuseStep 1284101 = 240769) (by norm_num)
theorem B1284173 : Blo 566810 1284173 := bbase (se 3 (by rfl) ⟨240782, by rfl⟩ : syracuseStep 1284173 = 481565) (by norm_num)
theorem B956549 : Blo 566810 956549 := bbase (se 4 (by rfl) ⟨89676, by rfl⟩ : syracuseStep 956549 = 179353) (by norm_num)
theorem B1284245 : Blo 566810 1284245 := bbase (se 6 (by rfl) ⟨30099, by rfl⟩ : syracuseStep 1284245 = 60199) (by norm_num)
theorem B1284317 : Blo 566810 1284317 := bbase (se 3 (by rfl) ⟨240809, by rfl⟩ : syracuseStep 1284317 = 481619) (by norm_num)
theorem B956677 : Blo 566810 956677 := bbase (se 4 (by rfl) ⟨89688, by rfl⟩ : syracuseStep 956677 = 179377) (by norm_num)
theorem B956765 : Blo 566810 956765 := bbase (se 3 (by rfl) ⟨179393, by rfl⟩ : syracuseStep 956765 = 358787) (by norm_num)
theorem B2431397 : Blo 566810 2431397 := bbase (se 4 (by rfl) ⟨227943, by rfl⟩ : syracuseStep 2431397 = 455887) (by norm_num)
theorem B1382837 : Blo 566810 1382837 := bbase (se 5 (by rfl) ⟨64820, by rfl⟩ : syracuseStep 1382837 = 129641) (by norm_num)
theorem B956893 : Blo 566810 956893 := bbase (se 3 (by rfl) ⟨179417, by rfl⟩ : syracuseStep 956893 = 358835) (by norm_num)
theorem B2726405 : Blo 566810 2726405 := bbase (se 4 (by rfl) ⟨255600, by rfl⟩ : syracuseStep 2726405 = 511201) (by norm_num)
theorem B956981 : Blo 566810 956981 := bbase (se 5 (by rfl) ⟨44858, by rfl⟩ : syracuseStep 956981 = 89717) (by norm_num)
theorem B1055285 : Blo 566810 1055285 := bbase (se 5 (by rfl) ⟨49466, by rfl⟩ : syracuseStep 1055285 = 98933) (by norm_num)
theorem B3644021 : Blo 566810 3644021 := bbase (se 5 (by rfl) ⟨170813, by rfl⟩ : syracuseStep 3644021 = 341627) (by norm_num)
theorem B957109 : Blo 566810 957109 := bbase (se 5 (by rfl) ⟨44864, by rfl⟩ : syracuseStep 957109 = 89729) (by norm_num)
theorem B2726597 : Blo 566810 2726597 := bbase (se 4 (by rfl) ⟨255618, by rfl⟩ : syracuseStep 2726597 = 511237) (by norm_num)
theorem B1972997 : Blo 566810 1972997 := bbase (se 4 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 1972997 = 369937) (by norm_num)
theorem B957197 : Blo 566810 957197 := bbase (se 3 (by rfl) ⟨179474, by rfl⟩ : syracuseStep 957197 = 358949) (by norm_num)
theorem B957325 : Blo 566810 957325 := bbase (se 3 (by rfl) ⟨179498, by rfl⟩ : syracuseStep 957325 = 358997) (by norm_num)
theorem B957413 : Blo 566810 957413 := bbase (se 4 (by rfl) ⟨89757, by rfl⟩ : syracuseStep 957413 = 179515) (by norm_num)
theorem B957541 : Blo 566810 957541 := bbase (se 4 (by rfl) ⟨89769, by rfl⟩ : syracuseStep 957541 = 179539) (by norm_num)
theorem B957629 : Blo 566810 957629 := bbase (se 3 (by rfl) ⟨179555, by rfl⟩ : syracuseStep 957629 = 359111) (by norm_num)
theorem B957757 : Blo 566810 957757 := bbase (se 3 (by rfl) ⟨179579, by rfl⟩ : syracuseStep 957757 = 359159) (by norm_num)
theorem B7806293 : Blo 566810 7806293 := bbase (se 11 (by rfl) ⟨5717, by rfl⟩ : syracuseStep 7806293 = 11435) (by norm_num)
theorem B2432389 : Blo 566810 2432389 := bbase (se 4 (by rfl) ⟨228036, by rfl⟩ : syracuseStep 2432389 = 456073) (by norm_num)
theorem B957845 : Blo 566810 957845 := bbase (se 6 (by rfl) ⟨22449, by rfl⟩ : syracuseStep 957845 = 44899) (by norm_num)
theorem B957973 : Blo 566810 957973 := bbase (se 6 (by rfl) ⟨22452, by rfl⟩ : syracuseStep 957973 = 44905) (by norm_num)
theorem B4562453 : Blo 566810 4562453 := bbase (se 6 (by rfl) ⟨106932, by rfl⟩ : syracuseStep 4562453 = 213865) (by norm_num)
theorem B958061 : Blo 566810 958061 := bbase (se 3 (by rfl) ⟨179636, by rfl⟩ : syracuseStep 958061 = 359273) (by norm_num)
theorem B2301605 : Blo 566810 2301605 := bbase (se 4 (by rfl) ⟨215775, by rfl⟩ : syracuseStep 2301605 = 431551) (by norm_num)
theorem B2924261 : Blo 566810 2924261 := bbase (se 4 (by rfl) ⟨274149, by rfl⟩ : syracuseStep 2924261 = 548299) (by norm_num)
theorem B958189 : Blo 566810 958189 := bbase (se 3 (by rfl) ⟨179660, by rfl⟩ : syracuseStep 958189 = 359321) (by norm_num)
theorem B3448565 : Blo 566810 3448565 := bbase (se 5 (by rfl) ⟨161651, by rfl⟩ : syracuseStep 3448565 = 323303) (by norm_num)
theorem B958277 : Blo 566810 958277 := bbase (se 4 (by rfl) ⟨89838, by rfl⟩ : syracuseStep 958277 = 179677) (by norm_num)
theorem B958405 : Blo 566810 958405 := bbase (se 4 (by rfl) ⟨89850, by rfl⟩ : syracuseStep 958405 = 179701) (by norm_num)
theorem B958493 : Blo 566810 958493 := bbase (se 3 (by rfl) ⟨179717, by rfl⟩ : syracuseStep 958493 = 359435) (by norm_num)
theorem B958621 : Blo 566810 958621 := bbase (se 3 (by rfl) ⟨179741, by rfl⟩ : syracuseStep 958621 = 359483) (by norm_num)
theorem B4923605 : Blo 566810 4923605 := bbase (se 7 (by rfl) ⟨57698, by rfl⟩ : syracuseStep 4923605 = 115397) (by norm_num)
theorem B1319141 : Blo 566810 1319141 := bbase (se 4 (by rfl) ⟨123669, by rfl⟩ : syracuseStep 1319141 = 247339) (by norm_num)
theorem B958709 : Blo 566810 958709 := bbase (se 5 (by rfl) ⟨44939, by rfl⟩ : syracuseStep 958709 = 89879) (by norm_num)
theorem B958837 : Blo 566810 958837 := bbase (se 5 (by rfl) ⟨44945, by rfl⟩ : syracuseStep 958837 = 89891) (by norm_num)
theorem B958925 : Blo 566810 958925 := bbase (se 3 (by rfl) ⟨179798, by rfl⟩ : syracuseStep 958925 = 359597) (by norm_num)
theorem B1614325 : Blo 566810 1614325 := bbase (se 5 (by rfl) ⟨75671, by rfl⟩ : syracuseStep 1614325 = 151343) (by norm_num)
theorem B959053 : Blo 566810 959053 := bbase (se 3 (by rfl) ⟨179822, by rfl⟩ : syracuseStep 959053 = 359645) (by norm_num)
theorem B926293 : Blo 566810 926293 := bbase (se 8 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 926293 = 10855) (by norm_num)
theorem B1614485 : Blo 566810 1614485 := bbase (se 6 (by rfl) ⟨37839, by rfl⟩ : syracuseStep 1614485 = 75679) (by norm_num)
theorem B959141 : Blo 566810 959141 := bbase (se 4 (by rfl) ⟨89919, by rfl⟩ : syracuseStep 959141 = 179839) (by norm_num)
theorem B12264149 : Blo 566810 12264149 := bbase (se 7 (by rfl) ⟨143720, by rfl⟩ : syracuseStep 12264149 = 287441) (by norm_num)
theorem B959269 : Blo 566810 959269 := bbase (se 4 (by rfl) ⟨89931, by rfl⟩ : syracuseStep 959269 = 179863) (by norm_num)
theorem B959357 : Blo 566810 959357 := bbase (se 3 (by rfl) ⟨179879, by rfl⟩ : syracuseStep 959357 = 359759) (by norm_num)
theorem B1614725 : Blo 566810 1614725 := bbase (se 4 (by rfl) ⟨151380, by rfl⟩ : syracuseStep 1614725 = 302761) (by norm_num)
theorem B959485 : Blo 566810 959485 := bbase (se 3 (by rfl) ⟨179903, by rfl⟩ : syracuseStep 959485 = 359807) (by norm_num)
theorem B1614917 : Blo 566810 1614917 := bbase (se 4 (by rfl) ⟨151398, by rfl⟩ : syracuseStep 1614917 = 302797) (by norm_num)
theorem B959573 : Blo 566810 959573 := bbase (se 8 (by rfl) ⟨5622, by rfl⟩ : syracuseStep 959573 = 11245) (by norm_num)
theorem B1025141 : Blo 566810 1025141 := bbase (se 5 (by rfl) ⟨48053, by rfl⟩ : syracuseStep 1025141 = 96107) (by norm_num)
theorem B959701 : Blo 566810 959701 := bbase (se 7 (by rfl) ⟨11246, by rfl⟩ : syracuseStep 959701 = 22493) (by norm_num)
theorem B2598101 : Blo 566810 2598101 := bbase (se 7 (by rfl) ⟨30446, by rfl⟩ : syracuseStep 2598101 = 60893) (by norm_num)
theorem B959789 : Blo 566810 959789 := bbase (se 3 (by rfl) ⟨179960, by rfl⟩ : syracuseStep 959789 = 359921) (by norm_num)
theorem B959917 : Blo 566810 959917 := bbase (se 3 (by rfl) ⟨179984, by rfl⟩ : syracuseStep 959917 = 359969) (by norm_num)
theorem B2336261 : Blo 566810 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B960005 : Blo 566810 960005 := bbase (se 4 (by rfl) ⟨90000, by rfl⟩ : syracuseStep 960005 = 180001) (by norm_num)
theorem B960133 : Blo 566810 960133 := bbase (se 4 (by rfl) ⟨90012, by rfl⟩ : syracuseStep 960133 = 180025) (by norm_num)
theorem B960221 : Blo 566810 960221 := bbase (se 3 (by rfl) ⟨180041, by rfl⟩ : syracuseStep 960221 = 360083) (by norm_num)
theorem B960349 : Blo 566810 960349 := bbase (se 3 (by rfl) ⟨180065, by rfl⟩ : syracuseStep 960349 = 360131) (by norm_num)
theorem B862093 : Blo 566810 862093 := bbase (se 3 (by rfl) ⟨161642, by rfl⟩ : syracuseStep 862093 = 323285) (by norm_num)
theorem B731045 : Blo 566810 731045 := bbase (se 4 (by rfl) ⟨68535, by rfl⟩ : syracuseStep 731045 = 137071) (by norm_num)
theorem B960437 : Blo 566810 960437 := bbase (se 5 (by rfl) ⟨45020, by rfl⟩ : syracuseStep 960437 = 90041) (by norm_num)
theorem B862165 : Blo 566810 862165 := bbase (se 7 (by rfl) ⟨10103, by rfl⟩ : syracuseStep 862165 = 20207) (by norm_num)
theorem B1615909 : Blo 566810 1615909 := bbase (se 4 (by rfl) ⟨151491, by rfl⟩ : syracuseStep 1615909 = 302983) (by norm_num)
theorem B960565 : Blo 566810 960565 := bbase (se 5 (by rfl) ⟨45026, by rfl⟩ : syracuseStep 960565 = 90053) (by norm_num)
theorem B960653 : Blo 566810 960653 := bbase (se 3 (by rfl) ⟨180122, by rfl⟩ : syracuseStep 960653 = 360245) (by norm_num)
theorem B1943813 : Blo 566810 1943813 := bbase (se 4 (by rfl) ⟨182232, by rfl⟩ : syracuseStep 1943813 = 364465) (by norm_num)
theorem B960781 : Blo 566810 960781 := bbase (se 3 (by rfl) ⟨180146, by rfl⟩ : syracuseStep 960781 = 360293) (by norm_num)
theorem B3451189 : Blo 566810 3451189 := bbase (se 5 (by rfl) ⟨161774, by rfl⟩ : syracuseStep 3451189 = 323549) (by norm_num)
theorem B1091917 : Blo 566810 1091917 := bbase (se 3 (by rfl) ⟨204734, by rfl⟩ : syracuseStep 1091917 = 409469) (by norm_num)
theorem B960869 : Blo 566810 960869 := bbase (se 4 (by rfl) ⟨90081, by rfl⟩ : syracuseStep 960869 = 180163) (by norm_num)
theorem B960997 : Blo 566810 960997 := bbase (se 4 (by rfl) ⟨90093, by rfl⟩ : syracuseStep 960997 = 180187) (by norm_num)
theorem B1092133 : Blo 566810 1092133 := bbase (se 4 (by rfl) ⟨102387, by rfl⟩ : syracuseStep 1092133 = 204775) (by norm_num)
theorem B961085 : Blo 566810 961085 := bbase (se 3 (by rfl) ⟨180203, by rfl⟩ : syracuseStep 961085 = 360407) (by norm_num)
theorem B10693205 : Blo 566810 10693205 := bbase (se 8 (by rfl) ⟨62655, by rfl⟩ : syracuseStep 10693205 = 125311) (by norm_num)
theorem B2108005 : Blo 566810 2108005 := bbase (se 4 (by rfl) ⟨197625, by rfl⟩ : syracuseStep 2108005 = 395251) (by norm_num)
theorem B961213 : Blo 566810 961213 := bbase (se 3 (by rfl) ⟨180227, by rfl⟩ : syracuseStep 961213 = 360455) (by norm_num)
theorem B2730709 : Blo 566810 2730709 := bbase (se 7 (by rfl) ⟨32000, by rfl⟩ : syracuseStep 2730709 = 64001) (by norm_num)
theorem B961301 : Blo 566810 961301 := bbase (se 6 (by rfl) ⟨22530, by rfl⟩ : syracuseStep 961301 = 45061) (by norm_num)
theorem B2960165 : Blo 566810 2960165 := bbase (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) (by norm_num)
theorem B961429 : Blo 566810 961429 := bbase (se 6 (by rfl) ⟨22533, by rfl⟩ : syracuseStep 961429 = 45067) (by norm_num)
theorem B961517 : Blo 566810 961517 := bbase (se 3 (by rfl) ⟨180284, by rfl⟩ : syracuseStep 961517 = 360569) (by norm_num)
theorem B961645 : Blo 566810 961645 := bbase (se 3 (by rfl) ⟨180308, by rfl⟩ : syracuseStep 961645 = 360617) (by norm_num)
theorem B1617013 : Blo 566810 1617013 := bbase (se 5 (by rfl) ⟨75797, by rfl⟩ : syracuseStep 1617013 = 151595) (by norm_num)
theorem B961733 : Blo 566810 961733 := bbase (se 4 (by rfl) ⟨90162, by rfl⟩ : syracuseStep 961733 = 180325) (by norm_num)
theorem B961861 : Blo 566810 961861 := bbase (se 4 (by rfl) ⟨90174, by rfl⟩ : syracuseStep 961861 = 180349) (by norm_num)
theorem B4599125 : Blo 566810 4599125 := bbase (se 11 (by rfl) ⟨3368, by rfl⟩ : syracuseStep 4599125 = 6737) (by norm_num)
theorem B961949 : Blo 566810 961949 := bbase (se 3 (by rfl) ⟨180365, by rfl⟩ : syracuseStep 961949 = 360731) (by norm_num)
theorem B863717 : Blo 566810 863717 := bbase (se 4 (by rfl) ⟨80973, by rfl⟩ : syracuseStep 863717 = 161947) (by norm_num)
theorem B962077 : Blo 566810 962077 := bbase (se 3 (by rfl) ⟨180389, by rfl⟩ : syracuseStep 962077 = 360779) (by norm_num)
theorem B4304501 : Blo 566810 4304501 := bbase (se 5 (by rfl) ⟨201773, by rfl⟩ : syracuseStep 4304501 = 403547) (by norm_num)
theorem B962165 : Blo 566810 962165 := bbase (se 5 (by rfl) ⟨45101, by rfl⟩ : syracuseStep 962165 = 90203) (by norm_num)
theorem B1027765 : Blo 566810 1027765 := bbase (se 5 (by rfl) ⟨48176, by rfl⟩ : syracuseStep 1027765 = 96353) (by norm_num)
theorem B1093349 : Blo 566810 1093349 := bbase (se 4 (by rfl) ⟨102501, by rfl⟩ : syracuseStep 1093349 = 205003) (by norm_num)
theorem B1388261 : Blo 566810 1388261 := bbase (se 4 (by rfl) ⟨130149, by rfl⟩ : syracuseStep 1388261 = 260299) (by norm_num)
theorem B962293 : Blo 566810 962293 := bbase (se 5 (by rfl) ⟨45107, by rfl⟩ : syracuseStep 962293 = 90215) (by norm_num)
theorem B962381 : Blo 566810 962381 := bbase (se 3 (by rfl) ⟨180446, by rfl⟩ : syracuseStep 962381 = 360893) (by norm_num)
theorem B962509 : Blo 566810 962509 := bbase (se 3 (by rfl) ⟨180470, by rfl⟩ : syracuseStep 962509 = 360941) (by norm_num)
theorem B962597 : Blo 566810 962597 := bbase (se 4 (by rfl) ⟨90243, by rfl⟩ : syracuseStep 962597 = 180487) (by norm_num)
theorem B962725 : Blo 566810 962725 := bbase (se 4 (by rfl) ⟨90255, by rfl⟩ : syracuseStep 962725 = 180511) (by norm_num)
theorem B962813 : Blo 566810 962813 := bbase (se 3 (by rfl) ⟨180527, by rfl⟩ : syracuseStep 962813 = 361055) (by norm_num)
theorem B2437397 : Blo 566810 2437397 := bbase (se 6 (by rfl) ⟨57126, by rfl⟩ : syracuseStep 2437397 = 114253) (by norm_num)
theorem B962941 : Blo 566810 962941 := bbase (se 3 (by rfl) ⟨180551, by rfl⟩ : syracuseStep 962941 = 361103) (by norm_num)
theorem B963029 : Blo 566810 963029 := bbase (se 7 (by rfl) ⟨11285, by rfl⟩ : syracuseStep 963029 = 22571) (by norm_num)
theorem B1913381 : Blo 566810 1913381 := bbase (se 4 (by rfl) ⟨179379, by rfl⟩ : syracuseStep 1913381 = 358759) (by norm_num)
theorem B2437685 : Blo 566810 2437685 := bbase (se 5 (by rfl) ⟨114266, by rfl⟩ : syracuseStep 2437685 = 228533) (by norm_num)
theorem B1618517 : Blo 566810 1618517 := bbase (se 8 (by rfl) ⟨9483, by rfl⟩ : syracuseStep 1618517 = 18967) (by norm_num)
theorem B963157 : Blo 566810 963157 := bbase (se 8 (by rfl) ⟨5643, by rfl⟩ : syracuseStep 963157 = 11287) (by norm_num)
theorem B766597 : Blo 566810 766597 := bbase (se 4 (by rfl) ⟨71868, by rfl⟩ : syracuseStep 766597 = 143737) (by norm_num)
theorem B4108981 : Blo 566810 4108981 := bbase (se 5 (by rfl) ⟨192608, by rfl⟩ : syracuseStep 4108981 = 385217) (by norm_num)
theorem B1946389 : Blo 566810 1946389 := bbase (se 6 (by rfl) ⟨45618, by rfl⟩ : syracuseStep 1946389 = 91237) (by norm_num)
theorem B1913813 : Blo 566810 1913813 := bbase (se 7 (by rfl) ⟨22427, by rfl⟩ : syracuseStep 1913813 = 44855) (by norm_num)
theorem B1914245 : Blo 566810 1914245 := bbase (se 4 (by rfl) ⟨179460, by rfl⟩ : syracuseStep 1914245 = 358921) (by norm_num)
theorem B2602405 : Blo 566810 2602405 := bbase (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) (by norm_num)
theorem B2471381 : Blo 566810 2471381 := bbase (se 7 (by rfl) ⟨28961, by rfl⟩ : syracuseStep 2471381 = 57923) (by norm_num)
theorem B1914677 : Blo 566810 1914677 := bbase (se 5 (by rfl) ⟨89750, by rfl⟩ : syracuseStep 1914677 = 179501) (by norm_num)
theorem B1816501 : Blo 566810 1816501 := bbase (se 5 (by rfl) ⟨85148, by rfl⟩ : syracuseStep 1816501 = 170297) (by norm_num)
theorem B767981 : Blo 566810 767981 := bbase (se 3 (by rfl) ⟨143996, by rfl⟩ : syracuseStep 767981 = 287993) (by norm_num)
theorem B1620101 : Blo 566810 1620101 := bbase (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) (by norm_num)
theorem B2734229 : Blo 566810 2734229 := bbase (se 6 (by rfl) ⟨64083, by rfl⟩ : syracuseStep 2734229 = 128167) (by norm_num)
theorem B1915109 : Blo 566810 1915109 := bbase (se 4 (by rfl) ⟨179541, by rfl⟩ : syracuseStep 1915109 = 359083) (by norm_num)
theorem B1227125 : Blo 566810 1227125 := bbase (se 5 (by rfl) ⟨57521, by rfl⟩ : syracuseStep 1227125 = 115043) (by norm_num)
theorem B768413 : Blo 566810 768413 := bbase (se 3 (by rfl) ⟨144077, by rfl⟩ : syracuseStep 768413 = 288155) (by norm_num)
theorem B2603573 : Blo 566810 2603573 := bbase (se 5 (by rfl) ⟨122042, by rfl⟩ : syracuseStep 2603573 = 244085) (by norm_num)
theorem B1915541 : Blo 566810 1915541 := bbase (se 6 (by rfl) ⟨44895, by rfl⟩ : syracuseStep 1915541 = 89791) (by norm_num)
theorem B637681 : Blo 566810 637681 := bbase (se 2 (by rfl) ⟨239130, by rfl⟩ : syracuseStep 637681 = 478261) (by norm_num)
theorem B637717 : Blo 566810 637717 := bbase (se 6 (by rfl) ⟨14946, by rfl⟩ : syracuseStep 637717 = 29893) (by norm_num)
theorem B1620773 : Blo 566810 1620773 := bbase (se 4 (by rfl) ⟨151947, by rfl⟩ : syracuseStep 1620773 = 303895) (by norm_num)
theorem B637753 : Blo 566810 637753 := bbase (se 2 (by rfl) ⟨239157, by rfl⟩ : syracuseStep 637753 = 478315) (by norm_num)
theorem B637789 : Blo 566810 637789 := bbase (se 3 (by rfl) ⟨119585, by rfl⟩ : syracuseStep 637789 = 239171) (by norm_num)
theorem B637825 : Blo 566810 637825 := bbase (se 2 (by rfl) ⟨239184, by rfl⟩ : syracuseStep 637825 = 478369) (by norm_num)
theorem B637861 : Blo 566810 637861 := bbase (se 4 (by rfl) ⟨59799, by rfl⟩ : syracuseStep 637861 = 119599) (by norm_num)
theorem B867269 : Blo 566810 867269 := bbase (se 4 (by rfl) ⟨81306, by rfl⟩ : syracuseStep 867269 = 162613) (by norm_num)
theorem B637897 : Blo 566810 637897 := bbase (se 2 (by rfl) ⟨239211, by rfl⟩ : syracuseStep 637897 = 478423) (by norm_num)
theorem B4864981 : Blo 566810 4864981 := bbase (se 7 (by rfl) ⟨57011, by rfl⟩ : syracuseStep 4864981 = 114023) (by norm_num)
theorem B637933 : Blo 566810 637933 := bbase (se 3 (by rfl) ⟨119612, by rfl⟩ : syracuseStep 637933 = 239225) (by norm_num)
theorem B637969 : Blo 566810 637969 := bbase (se 2 (by rfl) ⟨239238, by rfl⟩ : syracuseStep 637969 = 478477) (by norm_num)
theorem B638005 : Blo 566810 638005 := bbase (se 5 (by rfl) ⟨29906, by rfl⟩ : syracuseStep 638005 = 59813) (by norm_num)
theorem B1915973 : Blo 566810 1915973 := bbase (se 4 (by rfl) ⟨179622, by rfl⟩ : syracuseStep 1915973 = 359245) (by norm_num)
theorem B638041 : Blo 566810 638041 := bbase (se 2 (by rfl) ⟨239265, by rfl⟩ : syracuseStep 638041 = 478531) (by norm_num)
theorem B638077 : Blo 566810 638077 := bbase (se 3 (by rfl) ⟨119639, by rfl⟩ : syracuseStep 638077 = 239279) (by norm_num)
theorem B638113 : Blo 566810 638113 := bbase (se 2 (by rfl) ⟨239292, by rfl⟩ : syracuseStep 638113 = 478585) (by norm_num)
theorem B638149 : Blo 566810 638149 := bbase (se 4 (by rfl) ⟨59826, by rfl⟩ : syracuseStep 638149 = 119653) (by norm_num)
theorem B1621205 : Blo 566810 1621205 := bbase (se 7 (by rfl) ⟨18998, by rfl⟩ : syracuseStep 1621205 = 37997) (by norm_num)
theorem B638185 : Blo 566810 638185 := bbase (se 2 (by rfl) ⟨239319, by rfl⟩ : syracuseStep 638185 = 478639) (by norm_num)
theorem B638221 : Blo 566810 638221 := bbase (se 3 (by rfl) ⟨119666, by rfl⟩ : syracuseStep 638221 = 239333) (by norm_num)
theorem B638257 : Blo 566810 638257 := bbase (se 2 (by rfl) ⟨239346, by rfl⟩ : syracuseStep 638257 = 478693) (by norm_num)
theorem B638293 : Blo 566810 638293 := bbase (se 11 (by rfl) ⟨467, by rfl⟩ : syracuseStep 638293 = 935) (by norm_num)
theorem B2735477 : Blo 566810 2735477 := bbase (se 5 (by rfl) ⟨128225, by rfl⟩ : syracuseStep 2735477 = 256451) (by norm_num)
theorem B638329 : Blo 566810 638329 := bbase (se 2 (by rfl) ⟨239373, by rfl⟩ : syracuseStep 638329 = 478747) (by norm_num)
theorem B638365 : Blo 566810 638365 := bbase (se 3 (by rfl) ⟨119693, by rfl⟩ : syracuseStep 638365 = 239387) (by norm_num)
theorem B867773 : Blo 566810 867773 := bbase (se 3 (by rfl) ⟨162707, by rfl⟩ : syracuseStep 867773 = 325415) (by norm_num)
theorem B638401 : Blo 566810 638401 := bbase (se 2 (by rfl) ⟨239400, by rfl⟩ : syracuseStep 638401 = 478801) (by norm_num)
theorem B1457605 : Blo 566810 1457605 := bbase (se 4 (by rfl) ⟨136650, by rfl⟩ : syracuseStep 1457605 = 273301) (by norm_num)
theorem B8764885 : Blo 566810 8764885 := bbase (se 7 (by rfl) ⟨102713, by rfl⟩ : syracuseStep 8764885 = 205427) (by norm_num)
theorem B638437 : Blo 566810 638437 := bbase (se 4 (by rfl) ⟨59853, by rfl⟩ : syracuseStep 638437 = 119707) (by norm_num)
theorem B5455349 : Blo 566810 5455349 := bbase (se 5 (by rfl) ⟨255719, by rfl⟩ : syracuseStep 5455349 = 511439) (by norm_num)
theorem B1916405 : Blo 566810 1916405 := bbase (se 5 (by rfl) ⟨89831, by rfl⟩ : syracuseStep 1916405 = 179663) (by norm_num)
theorem B638473 : Blo 566810 638473 := bbase (se 2 (by rfl) ⟨239427, by rfl⟩ : syracuseStep 638473 = 478855) (by norm_num)
theorem B638509 : Blo 566810 638509 := bbase (se 3 (by rfl) ⟨119720, by rfl⟩ : syracuseStep 638509 = 239441) (by norm_num)
theorem B605765 : Blo 566810 605765 := bbase (se 4 (by rfl) ⟨56790, by rfl⟩ : syracuseStep 605765 = 113581) (by norm_num)
theorem B638545 : Blo 566810 638545 := bbase (se 2 (by rfl) ⟨239454, by rfl⟩ : syracuseStep 638545 = 478909) (by norm_num)
theorem B1228373 : Blo 566810 1228373 := bbase (se 8 (by rfl) ⟨7197, by rfl⟩ : syracuseStep 1228373 = 14395) (by norm_num)
theorem B638581 : Blo 566810 638581 := bbase (se 5 (by rfl) ⟨29933, by rfl⟩ : syracuseStep 638581 = 59867) (by norm_num)
theorem B638617 : Blo 566810 638617 := bbase (se 2 (by rfl) ⟨239481, by rfl⟩ : syracuseStep 638617 = 478963) (by norm_num)
theorem B638653 : Blo 566810 638653 := bbase (se 3 (by rfl) ⟨119747, by rfl⟩ : syracuseStep 638653 = 239495) (by norm_num)
theorem B638689 : Blo 566810 638689 := bbase (se 2 (by rfl) ⟨239508, by rfl⟩ : syracuseStep 638689 = 479017) (by norm_num)
theorem B769765 : Blo 566810 769765 := bbase (se 4 (by rfl) ⟨72165, by rfl⟩ : syracuseStep 769765 = 144331) (by norm_num)
theorem B2244341 : Blo 566810 2244341 := bbase (se 5 (by rfl) ⟨105203, by rfl⟩ : syracuseStep 2244341 = 210407) (by norm_num)
theorem B638725 : Blo 566810 638725 := bbase (se 4 (by rfl) ⟨59880, by rfl⟩ : syracuseStep 638725 = 119761) (by norm_num)
theorem B638761 : Blo 566810 638761 := bbase (se 2 (by rfl) ⟨239535, by rfl⟩ : syracuseStep 638761 = 479071) (by norm_num)
theorem B638797 : Blo 566810 638797 := bbase (se 3 (by rfl) ⟨119774, by rfl⟩ : syracuseStep 638797 = 239549) (by norm_num)
theorem B638833 : Blo 566810 638833 := bbase (se 2 (by rfl) ⟨239562, by rfl⟩ : syracuseStep 638833 = 479125) (by norm_num)
theorem B638869 : Blo 566810 638869 := bbase (se 6 (by rfl) ⟨14973, by rfl⟩ : syracuseStep 638869 = 29947) (by norm_num)
theorem B1916837 : Blo 566810 1916837 := bbase (se 4 (by rfl) ⟨179703, by rfl⟩ : syracuseStep 1916837 = 359407) (by norm_num)
theorem B638905 : Blo 566810 638905 := bbase (se 2 (by rfl) ⟨239589, by rfl⟩ : syracuseStep 638905 = 479179) (by norm_num)
theorem B1621957 : Blo 566810 1621957 := bbase (se 4 (by rfl) ⟨152058, by rfl⟩ : syracuseStep 1621957 = 304117) (by norm_num)
theorem B638941 : Blo 566810 638941 := bbase (se 3 (by rfl) ⟨119801, by rfl⟩ : syracuseStep 638941 = 239603) (by norm_num)
theorem B770045 : Blo 566810 770045 := bbase (se 3 (by rfl) ⟨144383, by rfl⟩ : syracuseStep 770045 = 288767) (by norm_num)
theorem B606209 : Blo 566810 606209 := bbase (se 2 (by rfl) ⟨227328, by rfl⟩ : syracuseStep 606209 = 454657) (by norm_num)
theorem B638977 : Blo 566810 638977 := bbase (se 2 (by rfl) ⟨239616, by rfl⟩ : syracuseStep 638977 = 479233) (by norm_num)
theorem B639013 : Blo 566810 639013 := bbase (se 4 (by rfl) ⟨59907, by rfl⟩ : syracuseStep 639013 = 119815) (by norm_num)
theorem B639049 : Blo 566810 639049 := bbase (se 2 (by rfl) ⟨239643, by rfl⟩ : syracuseStep 639049 = 479287) (by norm_num)
theorem B639085 : Blo 566810 639085 := bbase (se 3 (by rfl) ⟨119828, by rfl⟩ : syracuseStep 639085 = 239657) (by norm_num)
theorem B639121 : Blo 566810 639121 := bbase (se 2 (by rfl) ⟨239670, by rfl⟩ : syracuseStep 639121 = 479341) (by norm_num)
theorem B639157 : Blo 566810 639157 := bbase (se 5 (by rfl) ⟨29960, by rfl⟩ : syracuseStep 639157 = 59921) (by norm_num)
theorem B639193 : Blo 566810 639193 := bbase (se 2 (by rfl) ⟨239697, by rfl⟩ : syracuseStep 639193 = 479395) (by norm_num)
theorem B606457 : Blo 566810 606457 := bbase (se 2 (by rfl) ⟨227421, by rfl⟩ : syracuseStep 606457 = 454843) (by norm_num)
theorem B639229 : Blo 566810 639229 := bbase (se 3 (by rfl) ⟨119855, by rfl⟩ : syracuseStep 639229 = 239711) (by norm_num)
theorem B639265 : Blo 566810 639265 := bbase (se 2 (by rfl) ⟨239724, by rfl⟩ : syracuseStep 639265 = 479449) (by norm_num)
theorem B639301 : Blo 566810 639301 := bbase (se 4 (by rfl) ⟨59934, by rfl⟩ : syracuseStep 639301 = 119869) (by norm_num)
theorem B1917269 : Blo 566810 1917269 := bbase (se 10 (by rfl) ⟨2808, by rfl⟩ : syracuseStep 1917269 = 5617) (by norm_num)
theorem B639337 : Blo 566810 639337 := bbase (se 2 (by rfl) ⟨239751, by rfl⟩ : syracuseStep 639337 = 479503) (by norm_num)
theorem B3457397 : Blo 566810 3457397 := bbase (se 5 (by rfl) ⟨162065, by rfl⟩ : syracuseStep 3457397 = 324131) (by norm_num)
theorem B639373 : Blo 566810 639373 := bbase (se 3 (by rfl) ⟨119882, by rfl⟩ : syracuseStep 639373 = 239765) (by norm_num)
theorem B639409 : Blo 566810 639409 := bbase (se 2 (by rfl) ⟨239778, by rfl⟩ : syracuseStep 639409 = 479557) (by norm_num)
theorem B639445 : Blo 566810 639445 := bbase (se 7 (by rfl) ⟨7493, by rfl⟩ : syracuseStep 639445 = 14987) (by norm_num)
theorem B639481 : Blo 566810 639481 := bbase (se 2 (by rfl) ⟨239805, by rfl⟩ : syracuseStep 639481 = 479611) (by norm_num)
theorem B639517 : Blo 566810 639517 := bbase (se 3 (by rfl) ⟨119909, by rfl⟩ : syracuseStep 639517 = 239819) (by norm_num)
theorem B639553 : Blo 566810 639553 := bbase (se 2 (by rfl) ⟨239832, by rfl⟩ : syracuseStep 639553 = 479665) (by norm_num)
theorem B2048597 : Blo 566810 2048597 := bbase (se 8 (by rfl) ⟨12003, by rfl⟩ : syracuseStep 2048597 = 24007) (by norm_num)
theorem B639589 : Blo 566810 639589 := bbase (se 4 (by rfl) ⟨59961, by rfl⟩ : syracuseStep 639589 = 119923) (by norm_num)
theorem B639625 : Blo 566810 639625 := bbase (se 2 (by rfl) ⟨239859, by rfl⟩ : syracuseStep 639625 = 479719) (by norm_num)
theorem B606889 : Blo 566810 606889 := bbase (se 2 (by rfl) ⟨227583, by rfl⟩ : syracuseStep 606889 = 455167) (by norm_num)
theorem B639661 : Blo 566810 639661 := bbase (se 3 (by rfl) ⟨119936, by rfl⟩ : syracuseStep 639661 = 239873) (by norm_num)
theorem B639697 : Blo 566810 639697 := bbase (se 2 (by rfl) ⟨239886, by rfl⟩ : syracuseStep 639697 = 479773) (by norm_num)
theorem B606961 : Blo 566810 606961 := bbase (se 2 (by rfl) ⟨227610, by rfl⟩ : syracuseStep 606961 = 455221) (by norm_num)
theorem B639733 : Blo 566810 639733 := bbase (se 5 (by rfl) ⟨29987, by rfl⟩ : syracuseStep 639733 = 59975) (by norm_num)
theorem B1819397 : Blo 566810 1819397 := bbase (se 4 (by rfl) ⟨170568, by rfl⟩ : syracuseStep 1819397 = 341137) (by norm_num)
theorem B1917701 : Blo 566810 1917701 := bbase (se 4 (by rfl) ⟨179784, by rfl⟩ : syracuseStep 1917701 = 359569) (by norm_num)
theorem B639769 : Blo 566810 639769 := bbase (se 2 (by rfl) ⟨239913, by rfl⟩ : syracuseStep 639769 = 479827) (by norm_num)
theorem B639805 : Blo 566810 639805 := bbase (se 3 (by rfl) ⟨119963, by rfl⟩ : syracuseStep 639805 = 239927) (by norm_num)
theorem B639841 : Blo 566810 639841 := bbase (se 2 (by rfl) ⟨239940, by rfl⟩ : syracuseStep 639841 = 479881) (by norm_num)
theorem B639877 : Blo 566810 639877 := bbase (se 4 (by rfl) ⟨59988, by rfl⟩ : syracuseStep 639877 = 119977) (by norm_num)
theorem B4866965 : Blo 566810 4866965 := bbase (se 6 (by rfl) ⟨114069, by rfl⟩ : syracuseStep 4866965 = 228139) (by norm_num)
theorem B639913 : Blo 566810 639913 := bbase (se 2 (by rfl) ⟨239967, by rfl⟩ : syracuseStep 639913 = 479935) (by norm_num)
theorem B639949 : Blo 566810 639949 := bbase (se 3 (by rfl) ⟨119990, by rfl⟩ : syracuseStep 639949 = 239981) (by norm_num)
theorem B639985 : Blo 566810 639985 := bbase (se 2 (by rfl) ⟨239994, by rfl⟩ : syracuseStep 639985 = 479989) (by norm_num)
theorem B1295365 : Blo 566810 1295365 := bbase (se 4 (by rfl) ⟨121440, by rfl⟩ : syracuseStep 1295365 = 242881) (by norm_num)
theorem B640021 : Blo 566810 640021 := bbase (se 6 (by rfl) ⟨15000, by rfl⟩ : syracuseStep 640021 = 30001) (by norm_num)
theorem B640057 : Blo 566810 640057 := bbase (se 2 (by rfl) ⟨240021, by rfl⟩ : syracuseStep 640057 = 480043) (by norm_num)
theorem B1295437 : Blo 566810 1295437 := bbase (se 3 (by rfl) ⟨242894, by rfl⟩ : syracuseStep 1295437 = 485789) (by norm_num)
theorem B640093 : Blo 566810 640093 := bbase (se 3 (by rfl) ⟨120017, by rfl⟩ : syracuseStep 640093 = 240035) (by norm_num)
theorem B607333 : Blo 566810 607333 := bbase (se 4 (by rfl) ⟨56937, by rfl⟩ : syracuseStep 607333 = 113875) (by norm_num)
theorem B640129 : Blo 566810 640129 := bbase (se 2 (by rfl) ⟨240048, by rfl⟩ : syracuseStep 640129 = 480097) (by norm_num)
theorem B640165 : Blo 566810 640165 := bbase (se 4 (by rfl) ⟨60015, by rfl⟩ : syracuseStep 640165 = 120031) (by norm_num)
theorem B1918133 : Blo 566810 1918133 := bbase (se 5 (by rfl) ⟨89912, by rfl⟩ : syracuseStep 1918133 = 179825) (by norm_num)
theorem B640201 : Blo 566810 640201 := bbase (se 2 (by rfl) ⟨240075, by rfl⟩ : syracuseStep 640201 = 480151) (by norm_num)
theorem B640237 : Blo 566810 640237 := bbase (se 3 (by rfl) ⟨120044, by rfl⟩ : syracuseStep 640237 = 240089) (by norm_num)
theorem B640273 : Blo 566810 640273 := bbase (se 2 (by rfl) ⟨240102, by rfl⟩ : syracuseStep 640273 = 480205) (by norm_num)
theorem B640309 : Blo 566810 640309 := bbase (se 5 (by rfl) ⟨30014, by rfl⟩ : syracuseStep 640309 = 60029) (by norm_num)
theorem B640345 : Blo 566810 640345 := bbase (se 2 (by rfl) ⟨240129, by rfl⟩ : syracuseStep 640345 = 480259) (by norm_num)
theorem B640381 : Blo 566810 640381 := bbase (se 3 (by rfl) ⟨120071, by rfl⟩ : syracuseStep 640381 = 240143) (by norm_num)
theorem B640417 : Blo 566810 640417 := bbase (se 2 (by rfl) ⟨240156, by rfl⟩ : syracuseStep 640417 = 480313) (by norm_num)
theorem B640453 : Blo 566810 640453 := bbase (se 4 (by rfl) ⟨60042, by rfl⟩ : syracuseStep 640453 = 120085) (by norm_num)
theorem B607709 : Blo 566810 607709 := bbase (se 3 (by rfl) ⟨113945, by rfl⟩ : syracuseStep 607709 = 227891) (by norm_num)
theorem B640489 : Blo 566810 640489 := bbase (se 2 (by rfl) ⟨240183, by rfl⟩ : syracuseStep 640489 = 480367) (by norm_num)
theorem B640525 : Blo 566810 640525 := bbase (se 3 (by rfl) ⟨120098, by rfl⟩ : syracuseStep 640525 = 240197) (by norm_num)
theorem B607781 : Blo 566810 607781 := bbase (se 4 (by rfl) ⟨56979, by rfl⟩ : syracuseStep 607781 = 113959) (by norm_num)
theorem B640561 : Blo 566810 640561 := bbase (se 2 (by rfl) ⟨240210, by rfl⟩ : syracuseStep 640561 = 480421) (by norm_num)
theorem B575033 : Blo 566810 575033 := bbase (se 2 (by rfl) ⟨215637, by rfl⟩ : syracuseStep 575033 = 431275) (by norm_num)
theorem B640597 : Blo 566810 640597 := bbase (se 8 (by rfl) ⟨3753, by rfl⟩ : syracuseStep 640597 = 7507) (by norm_num)
theorem B1918565 : Blo 566810 1918565 := bbase (se 4 (by rfl) ⟨179865, by rfl⟩ : syracuseStep 1918565 = 359731) (by norm_num)
theorem B640633 : Blo 566810 640633 := bbase (se 2 (by rfl) ⟨240237, by rfl⟩ : syracuseStep 640633 = 480475) (by norm_num)
theorem B640669 : Blo 566810 640669 := bbase (se 3 (by rfl) ⟨120125, by rfl⟩ : syracuseStep 640669 = 240251) (by norm_num)
theorem B640705 : Blo 566810 640705 := bbase (se 2 (by rfl) ⟨240264, by rfl⟩ : syracuseStep 640705 = 480529) (by norm_num)
theorem B607969 : Blo 566810 607969 := bbase (se 2 (by rfl) ⟨227988, by rfl⟩ : syracuseStep 607969 = 455977) (by norm_num)
theorem B640741 : Blo 566810 640741 := bbase (se 4 (by rfl) ⟨60069, by rfl⟩ : syracuseStep 640741 = 120139) (by norm_num)
theorem B640777 : Blo 566810 640777 := bbase (se 2 (by rfl) ⟨240291, by rfl⟩ : syracuseStep 640777 = 480583) (by norm_num)
theorem B640813 : Blo 566810 640813 := bbase (se 3 (by rfl) ⟨120152, by rfl⟩ : syracuseStep 640813 = 240305) (by norm_num)
theorem B640849 : Blo 566810 640849 := bbase (se 2 (by rfl) ⟨240318, by rfl⟩ : syracuseStep 640849 = 480637) (by norm_num)
theorem B2049877 : Blo 566810 2049877 := bbase (se 9 (by rfl) ⟨6005, by rfl⟩ : syracuseStep 2049877 = 12011) (by norm_num)
theorem B640885 : Blo 566810 640885 := bbase (se 5 (by rfl) ⟨30041, by rfl⟩ : syracuseStep 640885 = 60083) (by norm_num)
theorem B608153 : Blo 566810 608153 := bbase (se 2 (by rfl) ⟨228057, by rfl⟩ : syracuseStep 608153 = 456115) (by norm_num)
theorem B640921 : Blo 566810 640921 := bbase (se 2 (by rfl) ⟨240345, by rfl⟩ : syracuseStep 640921 = 480691) (by norm_num)
theorem B640957 : Blo 566810 640957 := bbase (se 3 (by rfl) ⟨120179, by rfl⟩ : syracuseStep 640957 = 240359) (by norm_num)
theorem B640993 : Blo 566810 640993 := bbase (se 2 (by rfl) ⟨240372, by rfl⟩ : syracuseStep 640993 = 480745) (by norm_num)
theorem B5195765 : Blo 566810 5195765 := bbase (se 5 (by rfl) ⟨243551, by rfl⟩ : syracuseStep 5195765 = 487103) (by norm_num)
theorem B641029 : Blo 566810 641029 := bbase (se 4 (by rfl) ⟨60096, by rfl⟩ : syracuseStep 641029 = 120193) (by norm_num)
theorem B1918997 : Blo 566810 1918997 := bbase (se 6 (by rfl) ⟨44976, by rfl⟩ : syracuseStep 1918997 = 89953) (by norm_num)
theorem B641065 : Blo 566810 641065 := bbase (se 2 (by rfl) ⟨240399, by rfl⟩ : syracuseStep 641065 = 480799) (by norm_num)
theorem B2738245 : Blo 566810 2738245 := bbase (se 4 (by rfl) ⟨256710, by rfl⟩ : syracuseStep 2738245 = 513421) (by norm_num)
theorem B641101 : Blo 566810 641101 := bbase (se 3 (by rfl) ⟨120206, by rfl⟩ : syracuseStep 641101 = 240413) (by norm_num)
theorem B641137 : Blo 566810 641137 := bbase (se 2 (by rfl) ⟨240426, by rfl⟩ : syracuseStep 641137 = 480853) (by norm_num)
theorem B641173 : Blo 566810 641173 := bbase (se 6 (by rfl) ⟨15027, by rfl⟩ : syracuseStep 641173 = 30055) (by norm_num)
theorem B641209 : Blo 566810 641209 := bbase (se 2 (by rfl) ⟨240453, by rfl⟩ : syracuseStep 641209 = 480907) (by norm_num)
theorem B641245 : Blo 566810 641245 := bbase (se 3 (by rfl) ⟨120233, by rfl⟩ : syracuseStep 641245 = 240467) (by norm_num)
theorem B641281 : Blo 566810 641281 := bbase (se 2 (by rfl) ⟨240480, by rfl⟩ : syracuseStep 641281 = 480961) (by norm_num)
theorem B641317 : Blo 566810 641317 := bbase (se 4 (by rfl) ⟨60123, by rfl⟩ : syracuseStep 641317 = 120247) (by norm_num)
theorem B641353 : Blo 566810 641353 := bbase (se 2 (by rfl) ⟨240507, by rfl⟩ : syracuseStep 641353 = 481015) (by norm_num)
theorem B641389 : Blo 566810 641389 := bbase (se 3 (by rfl) ⟨120260, by rfl⟩ : syracuseStep 641389 = 240521) (by norm_num)
theorem B641425 : Blo 566810 641425 := bbase (se 2 (by rfl) ⟨240534, by rfl⟩ : syracuseStep 641425 = 481069) (by norm_num)
theorem B641461 : Blo 566810 641461 := bbase (se 5 (by rfl) ⟨30068, by rfl⟩ : syracuseStep 641461 = 60137) (by norm_num)
theorem B3656117 : Blo 566810 3656117 := bbase (se 5 (by rfl) ⟨171380, by rfl⟩ : syracuseStep 3656117 = 342761) (by norm_num)
theorem B1919429 : Blo 566810 1919429 := bbase (se 4 (by rfl) ⟨179946, by rfl⟩ : syracuseStep 1919429 = 359893) (by norm_num)
theorem B641497 : Blo 566810 641497 := bbase (se 2 (by rfl) ⟨240561, by rfl⟩ : syracuseStep 641497 = 481123) (by norm_num)
theorem B641533 : Blo 566810 641533 := bbase (se 3 (by rfl) ⟨120287, by rfl⟩ : syracuseStep 641533 = 240575) (by norm_num)
theorem B641569 : Blo 566810 641569 := bbase (se 2 (by rfl) ⟨240588, by rfl⟩ : syracuseStep 641569 = 481177) (by norm_num)
theorem B2869829 : Blo 566810 2869829 := bbase (se 4 (by rfl) ⟨269046, by rfl⟩ : syracuseStep 2869829 = 538093) (by norm_num)
theorem B641605 : Blo 566810 641605 := bbase (se 4 (by rfl) ⟨60150, by rfl⟩ : syracuseStep 641605 = 120301) (by norm_num)
theorem B1296989 : Blo 566810 1296989 := bbase (se 3 (by rfl) ⟨243185, by rfl⟩ : syracuseStep 1296989 = 486371) (by norm_num)
theorem B641641 : Blo 566810 641641 := bbase (se 2 (by rfl) ⟨240615, by rfl⟩ : syracuseStep 641641 = 481231) (by norm_num)
theorem B608905 : Blo 566810 608905 := bbase (se 2 (by rfl) ⟨228339, by rfl⟩ : syracuseStep 608905 = 456679) (by norm_num)
theorem B641677 : Blo 566810 641677 := bbase (se 3 (by rfl) ⟨120314, by rfl⟩ : syracuseStep 641677 = 240629) (by norm_num)
theorem B641713 : Blo 566810 641713 := bbase (se 2 (by rfl) ⟨240642, by rfl⟩ : syracuseStep 641713 = 481285) (by norm_num)
theorem B608977 : Blo 566810 608977 := bbase (se 2 (by rfl) ⟨228366, by rfl⟩ : syracuseStep 608977 = 456733) (by norm_num)
theorem B641749 : Blo 566810 641749 := bbase (se 7 (by rfl) ⟨7520, by rfl⟩ : syracuseStep 641749 = 15041) (by norm_num)
theorem B1624805 : Blo 566810 1624805 := bbase (se 4 (by rfl) ⟨152325, by rfl⟩ : syracuseStep 1624805 = 304651) (by norm_num)
theorem B576245 : Blo 566810 576245 := bbase (se 5 (by rfl) ⟨27011, by rfl⟩ : syracuseStep 576245 = 54023) (by norm_num)
theorem B641785 : Blo 566810 641785 := bbase (se 2 (by rfl) ⟨240669, by rfl⟩ : syracuseStep 641785 = 481339) (by norm_num)
theorem B641821 : Blo 566810 641821 := bbase (se 3 (by rfl) ⟨120341, by rfl⟩ : syracuseStep 641821 = 240683) (by norm_num)
theorem B641857 : Blo 566810 641857 := bbase (se 2 (by rfl) ⟨240696, by rfl⟩ : syracuseStep 641857 = 481393) (by norm_num)
theorem B641893 : Blo 566810 641893 := bbase (se 4 (by rfl) ⟨60177, by rfl⟩ : syracuseStep 641893 = 120355) (by norm_num)
theorem B1919861 : Blo 566810 1919861 := bbase (se 5 (by rfl) ⟨89993, by rfl⟩ : syracuseStep 1919861 = 179987) (by norm_num)
theorem B609157 : Blo 566810 609157 := bbase (se 4 (by rfl) ⟨57108, by rfl⟩ : syracuseStep 609157 = 114217) (by norm_num)
theorem B641929 : Blo 566810 641929 := bbase (se 2 (by rfl) ⟨240723, by rfl⟩ : syracuseStep 641929 = 481447) (by norm_num)
theorem B641965 : Blo 566810 641965 := bbase (se 3 (by rfl) ⟨120368, by rfl⟩ : syracuseStep 641965 = 240737) (by norm_num)
theorem B642001 : Blo 566810 642001 := bbase (se 2 (by rfl) ⟨240750, by rfl⟩ : syracuseStep 642001 = 481501) (by norm_num)
theorem B1821653 : Blo 566810 1821653 := bbase (se 7 (by rfl) ⟨21347, by rfl⟩ : syracuseStep 1821653 = 42695) (by norm_num)
theorem B642037 : Blo 566810 642037 := bbase (se 5 (by rfl) ⟨30095, by rfl⟩ : syracuseStep 642037 = 60191) (by norm_num)
theorem B642073 : Blo 566810 642073 := bbase (se 2 (by rfl) ⟨240777, by rfl⟩ : syracuseStep 642073 = 481555) (by norm_num)
theorem B642109 : Blo 566810 642109 := bbase (se 3 (by rfl) ⟨120395, by rfl⟩ : syracuseStep 642109 = 240791) (by norm_num)
theorem B576577 : Blo 566810 576577 := bbase (se 2 (by rfl) ⟨216216, by rfl⟩ : syracuseStep 576577 = 432433) (by norm_num)
theorem B642145 : Blo 566810 642145 := bbase (se 2 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 642145 = 481609) (by norm_num)
theorem B3230837 : Blo 566810 3230837 := bbase (se 5 (by rfl) ⟨151445, by rfl⟩ : syracuseStep 3230837 = 302891) (by norm_num)
theorem B8735957 : Blo 566810 8735957 := bbase (se 7 (by rfl) ⟨102374, by rfl⟩ : syracuseStep 8735957 = 204749) (by norm_num)
theorem B4312277 : Blo 566810 4312277 := bbase (se 7 (by rfl) ⟨50534, by rfl⟩ : syracuseStep 4312277 = 101069) (by norm_num)
theorem B1035533 : Blo 566810 1035533 := bbase (se 3 (by rfl) ⟨194162, by rfl⟩ : syracuseStep 1035533 = 388325) (by norm_num)
theorem B1920293 : Blo 566810 1920293 := bbase (se 4 (by rfl) ⟨180027, by rfl⟩ : syracuseStep 1920293 = 360055) (by norm_num)
theorem B2051365 : Blo 566810 2051365 := bbase (se 4 (by rfl) ⟨192315, by rfl⟩ : syracuseStep 2051365 = 384631) (by norm_num)
theorem B576829 : Blo 566810 576829 := bbase (se 3 (by rfl) ⟨108155, by rfl⟩ : syracuseStep 576829 = 216311) (by norm_num)
theorem B3067253 : Blo 566810 3067253 := bbase (se 5 (by rfl) ⟨143777, by rfl⟩ : syracuseStep 3067253 = 287555) (by norm_num)
theorem B1363549 : Blo 566810 1363549 := bbase (se 3 (by rfl) ⟨255665, by rfl⟩ : syracuseStep 1363549 = 511331) (by norm_num)
theorem B577145 : Blo 566810 577145 := bbase (se 2 (by rfl) ⟨216429, by rfl⟩ : syracuseStep 577145 = 432859) (by norm_num)
theorem B970373 : Blo 566810 970373 := bbase (se 4 (by rfl) ⟨90972, by rfl⟩ : syracuseStep 970373 = 181945) (by norm_num)
theorem B1822421 : Blo 566810 1822421 := bbase (se 7 (by rfl) ⟨21356, by rfl⟩ : syracuseStep 1822421 = 42713) (by norm_num)
theorem B1920725 : Blo 566810 1920725 := bbase (se 7 (by rfl) ⟨22508, by rfl⟩ : syracuseStep 1920725 = 45017) (by norm_num)
theorem B2871125 : Blo 566810 2871125 := bbase (se 9 (by rfl) ⟨8411, by rfl⟩ : syracuseStep 2871125 = 16823) (by norm_num)
theorem B1298357 : Blo 566810 1298357 := bbase (se 5 (by rfl) ⟨60860, by rfl⟩ : syracuseStep 1298357 = 121721) (by norm_num)
theorem B1921157 : Blo 566810 1921157 := bbase (se 4 (by rfl) ⟨180108, by rfl⟩ : syracuseStep 1921157 = 360217) (by norm_num)
theorem B1364165 : Blo 566810 1364165 := bbase (se 4 (by rfl) ⟨127890, by rfl⟩ : syracuseStep 1364165 = 255781) (by norm_num)
theorem B3068117 : Blo 566810 3068117 := bbase (se 7 (by rfl) ⟨35954, by rfl⟩ : syracuseStep 3068117 = 71909) (by norm_num)
theorem B1822933 : Blo 566810 1822933 := bbase (se 7 (by rfl) ⟨21362, by rfl⟩ : syracuseStep 1822933 = 42725) (by norm_num)
theorem B3232021 : Blo 566810 3232021 := bbase (se 6 (by rfl) ⟨75750, by rfl⟩ : syracuseStep 3232021 = 151501) (by norm_num)
theorem B807413 : Blo 566810 807413 := bbase (se 5 (by rfl) ⟨37847, by rfl⟩ : syracuseStep 807413 = 75695) (by norm_num)
theorem B1364501 : Blo 566810 1364501 := bbase (se 6 (by rfl) ⟨31980, by rfl⟩ : syracuseStep 1364501 = 63961) (by norm_num)
theorem B1921589 : Blo 566810 1921589 := bbase (se 5 (by rfl) ⟨90074, by rfl⟩ : syracuseStep 1921589 = 180149) (by norm_num)
theorem B578345 : Blo 566810 578345 := bbase (se 2 (by rfl) ⟨216879, by rfl⟩ : syracuseStep 578345 = 433759) (by norm_num)
theorem B1299253 : Blo 566810 1299253 := bbase (se 5 (by rfl) ⟨60902, by rfl⟩ : syracuseStep 1299253 = 121805) (by norm_num)
theorem B1364893 : Blo 566810 1364893 := bbase (se 3 (by rfl) ⟨255917, by rfl⟩ : syracuseStep 1364893 = 511835) (by norm_num)
theorem B1922021 : Blo 566810 1922021 := bbase (se 4 (by rfl) ⟨180189, by rfl⟩ : syracuseStep 1922021 = 360379) (by norm_num)
theorem B2872421 : Blo 566810 2872421 := bbase (se 4 (by rfl) ⟨269289, by rfl⟩ : syracuseStep 2872421 = 538579) (by norm_num)
theorem B808165 : Blo 566810 808165 := bbase (se 4 (by rfl) ⟨75765, by rfl⟩ : syracuseStep 808165 = 151531) (by norm_num)
theorem B1922453 : Blo 566810 1922453 := bbase (se 6 (by rfl) ⟨45057, by rfl⟩ : syracuseStep 1922453 = 90115) (by norm_num)
theorem B1725877 : Blo 566810 1725877 := bbase (se 5 (by rfl) ⟨80900, by rfl⟩ : syracuseStep 1725877 = 161801) (by norm_num)
theorem B2807237 : Blo 566810 2807237 := bbase (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) (by norm_num)
theorem B1922885 : Blo 566810 1922885 := bbase (se 4 (by rfl) ⟨180270, by rfl⟩ : syracuseStep 1922885 = 360541) (by norm_num)
theorem B2053973 : Blo 566810 2053973 := bbase (se 9 (by rfl) ⟨6017, by rfl⟩ : syracuseStep 2053973 = 12035) (by norm_num)
theorem B1464173 : Blo 566810 1464173 := bbase (se 3 (by rfl) ⟨274532, by rfl⟩ : syracuseStep 1464173 = 549065) (by norm_num)
theorem B1824677 : Blo 566810 1824677 := bbase (se 4 (by rfl) ⟨171063, by rfl⟩ : syracuseStep 1824677 = 342127) (by norm_num)
theorem B808957 : Blo 566810 808957 := bbase (se 3 (by rfl) ⟨151679, by rfl⟩ : syracuseStep 808957 = 303359) (by norm_num)
theorem B1824869 : Blo 566810 1824869 := bbase (se 4 (by rfl) ⟨171081, by rfl⟩ : syracuseStep 1824869 = 342163) (by norm_num)
theorem B2742437 : Blo 566810 2742437 := bbase (se 4 (by rfl) ⟨257103, by rfl⟩ : syracuseStep 2742437 = 514207) (by norm_num)
theorem B3234005 : Blo 566810 3234005 := bbase (se 7 (by rfl) ⟨37898, by rfl⟩ : syracuseStep 3234005 = 75797) (by norm_num)
theorem B1923317 : Blo 566810 1923317 := bbase (se 5 (by rfl) ⟨90155, by rfl⟩ : syracuseStep 1923317 = 180311) (by norm_num)
theorem B809293 : Blo 566810 809293 := bbase (se 3 (by rfl) ⟨151742, by rfl⟩ : syracuseStep 809293 = 303485) (by norm_num)
theorem B2873717 : Blo 566810 2873717 := bbase (se 5 (by rfl) ⟨134705, by rfl⟩ : syracuseStep 2873717 = 269411) (by norm_num)
theorem B809509 : Blo 566810 809509 := bbase (se 4 (by rfl) ⟨75891, by rfl⟩ : syracuseStep 809509 = 151783) (by norm_num)
theorem B2775653 : Blo 566810 2775653 := bbase (se 4 (by rfl) ⟨260217, by rfl⟩ : syracuseStep 2775653 = 520435) (by norm_num)
theorem B1923749 : Blo 566810 1923749 := bbase (se 4 (by rfl) ⟨180351, by rfl⟩ : syracuseStep 1923749 = 360703) (by norm_num)
theorem B809885 : Blo 566810 809885 := bbase (se 3 (by rfl) ⟨151853, by rfl⟩ : syracuseStep 809885 = 303707) (by norm_num)
theorem B1924181 : Blo 566810 1924181 := bbase (se 8 (by rfl) ⟨11274, by rfl⟩ : syracuseStep 1924181 = 22549) (by norm_num)
theorem B2153573 : Blo 566810 2153573 := bbase (se 4 (by rfl) ⟨201897, by rfl⟩ : syracuseStep 2153573 = 403795) (by norm_num)
theorem B908405 : Blo 566810 908405 := bbase (se 5 (by rfl) ⟨42581, by rfl⟩ : syracuseStep 908405 = 85163) (by norm_num)
theorem B908437 : Blo 566810 908437 := bbase (se 6 (by rfl) ⟨21291, by rfl⟩ : syracuseStep 908437 = 42583) (by norm_num)
theorem B974069 : Blo 566810 974069 := bbase (se 5 (by rfl) ⟨45659, by rfl⟩ : syracuseStep 974069 = 91319) (by norm_num)
theorem B2055413 : Blo 566810 2055413 := bbase (se 5 (by rfl) ⟨96347, by rfl⟩ : syracuseStep 2055413 = 192695) (by norm_num)
theorem B2153861 : Blo 566810 2153861 := bbase (se 4 (by rfl) ⟨201924, by rfl⟩ : syracuseStep 2153861 = 403849) (by norm_num)
theorem B1924613 : Blo 566810 1924613 := bbase (se 4 (by rfl) ⟨180432, by rfl⟩ : syracuseStep 1924613 = 360865) (by norm_num)
theorem B2875013 : Blo 566810 2875013 := bbase (se 4 (by rfl) ⟨269532, by rfl⟩ : syracuseStep 2875013 = 539065) (by norm_num)
theorem B1925045 : Blo 566810 1925045 := bbase (se 5 (by rfl) ⟨90236, by rfl⟩ : syracuseStep 1925045 = 180473) (by norm_num)
theorem B1368037 : Blo 566810 1368037 := bbase (se 4 (by rfl) ⟨128253, by rfl⟩ : syracuseStep 1368037 = 256507) (by norm_num)
theorem B1368085 : Blo 566810 1368085 := bbase (se 6 (by rfl) ⟨32064, by rfl⟩ : syracuseStep 1368085 = 64129) (by norm_num)
theorem B909365 : Blo 566810 909365 := bbase (se 5 (by rfl) ⟨42626, by rfl⟩ : syracuseStep 909365 = 85253) (by norm_num)
theorem B647281 : Blo 566810 647281 := bbase (se 2 (by rfl) ⟨242730, by rfl⟩ : syracuseStep 647281 = 485461) (by norm_num)
theorem B4153589 : Blo 566810 4153589 := bbase (se 5 (by rfl) ⟨194699, by rfl⟩ : syracuseStep 4153589 = 389399) (by norm_num)
theorem B4940021 : Blo 566810 4940021 := bbase (se 5 (by rfl) ⟨231563, by rfl⟩ : syracuseStep 4940021 = 463127) (by norm_num)
theorem B811309 : Blo 566810 811309 := bbase (se 3 (by rfl) ⟨152120, by rfl⟩ : syracuseStep 811309 = 304241) (by norm_num)
theorem B1925477 : Blo 566810 1925477 := bbase (se 4 (by rfl) ⟨180513, by rfl⟩ : syracuseStep 1925477 = 361027) (by norm_num)
theorem B3236213 : Blo 566810 3236213 := bbase (se 5 (by rfl) ⟨151697, by rfl⟩ : syracuseStep 3236213 = 303395) (by norm_num)
theorem B2155045 : Blo 566810 2155045 := bbase (se 4 (by rfl) ⟨202035, by rfl⟩ : syracuseStep 2155045 = 404071) (by norm_num)
theorem B1368701 : Blo 566810 1368701 := bbase (se 3 (by rfl) ⟨256631, by rfl⟩ : syracuseStep 1368701 = 513263) (by norm_num)
theorem B1401517 : Blo 566810 1401517 := bbase (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) (by norm_num)
theorem B910045 : Blo 566810 910045 := bbase (se 3 (by rfl) ⟨170633, by rfl⟩ : syracuseStep 910045 = 341267) (by norm_num)
theorem B615173 : Blo 566810 615173 := bbase (se 4 (by rfl) ⟨57672, by rfl⟩ : syracuseStep 615173 = 115345) (by norm_num)
theorem B1925909 : Blo 566810 1925909 := bbase (se 6 (by rfl) ⟨45138, by rfl⟩ : syracuseStep 1925909 = 90277) (by norm_num)
theorem B910109 : Blo 566810 910109 := bbase (se 3 (by rfl) ⟨170645, by rfl⟩ : syracuseStep 910109 = 341291) (by norm_num)
theorem B615205 : Blo 566810 615205 := bbase (se 4 (by rfl) ⟨57675, by rfl⟩ : syracuseStep 615205 = 115351) (by norm_num)
theorem B2155349 : Blo 566810 2155349 := bbase (se 9 (by rfl) ⟨6314, by rfl⟩ : syracuseStep 2155349 = 12629) (by norm_num)
theorem B2909029 : Blo 566810 2909029 := bbase (se 4 (by rfl) ⟨272721, by rfl⟩ : syracuseStep 2909029 = 545443) (by norm_num)
theorem B811901 : Blo 566810 811901 := bbase (se 3 (by rfl) ⟨152231, by rfl⟩ : syracuseStep 811901 = 304463) (by norm_num)
theorem B2876309 : Blo 566810 2876309 := bbase (se 6 (by rfl) ⟨67413, by rfl⟩ : syracuseStep 2876309 = 134827) (by norm_num)
theorem B1041349 : Blo 566810 1041349 := bbase (se 4 (by rfl) ⟨97626, by rfl⟩ : syracuseStep 1041349 = 195253) (by norm_num)
theorem B811981 : Blo 566810 811981 := bbase (se 3 (by rfl) ⟨152246, by rfl⟩ : syracuseStep 811981 = 304493) (by norm_num)
theorem B1369045 : Blo 566810 1369045 := bbase (se 7 (by rfl) ⟨16043, by rfl⟩ : syracuseStep 1369045 = 32087) (by norm_num)
theorem B615481 : Blo 566810 615481 := bbase (se 2 (by rfl) ⟨230805, by rfl⟩ : syracuseStep 615481 = 461611) (by norm_num)
theorem B812101 : Blo 566810 812101 := bbase (se 4 (by rfl) ⟨76134, by rfl⟩ : syracuseStep 812101 = 152269) (by norm_num)
theorem B1729637 : Blo 566810 1729637 := bbase (se 4 (by rfl) ⟨162153, by rfl⟩ : syracuseStep 1729637 = 324307) (by norm_num)
theorem B681097 : Blo 566810 681097 := bbase (se 2 (by rfl) ⟨255411, by rfl⟩ : syracuseStep 681097 = 510823) (by norm_num)
theorem B1434773 : Blo 566810 1434773 := bbase (se 6 (by rfl) ⟨33627, by rfl⟩ : syracuseStep 1434773 = 67255) (by norm_num)
theorem B812197 : Blo 566810 812197 := bbase (se 4 (by rfl) ⟨76143, by rfl⟩ : syracuseStep 812197 = 152287) (by norm_num)
theorem B1369277 : Blo 566810 1369277 := bbase (se 3 (by rfl) ⟨256739, by rfl⟩ : syracuseStep 1369277 = 513479) (by norm_num)
theorem B1926341 : Blo 566810 1926341 := bbase (se 4 (by rfl) ⟨180594, by rfl⟩ : syracuseStep 1926341 = 361189) (by norm_num)
theorem B1369469 : Blo 566810 1369469 := bbase (se 3 (by rfl) ⟨256775, by rfl⟩ : syracuseStep 1369469 = 513551) (by norm_num)
theorem B5203349 : Blo 566810 5203349 := bbase (se 6 (by rfl) ⟨121953, by rfl⟩ : syracuseStep 5203349 = 243907) (by norm_num)
theorem B681409 : Blo 566810 681409 := bbase (se 2 (by rfl) ⟨255528, by rfl⟩ : syracuseStep 681409 = 511057) (by norm_num)
theorem B1435117 : Blo 566810 1435117 := bbase (se 3 (by rfl) ⟨269084, by rfl⟩ : syracuseStep 1435117 = 538169) (by norm_num)
theorem B779773 : Blo 566810 779773 := bbase (se 3 (by rfl) ⟨146207, by rfl⟩ : syracuseStep 779773 = 292415) (by norm_num)
theorem B1435229 : Blo 566810 1435229 := bbase (se 3 (by rfl) ⟨269105, by rfl⟩ : syracuseStep 1435229 = 538211) (by norm_num)
theorem B1828469 : Blo 566810 1828469 := bbase (se 5 (by rfl) ⟨85709, by rfl⟩ : syracuseStep 1828469 = 171419) (by norm_num)
theorem B812693 : Blo 566810 812693 := bbase (se 6 (by rfl) ⟨19047, by rfl⟩ : syracuseStep 812693 = 38095) (by norm_num)
theorem B1369757 : Blo 566810 1369757 := bbase (se 3 (by rfl) ⟨256829, by rfl⟩ : syracuseStep 1369757 = 513659) (by norm_num)
theorem B648905 : Blo 566810 648905 := bbase (se 2 (by rfl) ⟨243339, by rfl⟩ : syracuseStep 648905 = 486679) (by norm_num)
theorem B648941 : Blo 566810 648941 := bbase (se 3 (by rfl) ⟨121676, by rfl⟩ : syracuseStep 648941 = 243353) (by norm_num)
theorem B1435421 : Blo 566810 1435421 := bbase (se 3 (by rfl) ⟨269141, by rfl⟩ : syracuseStep 1435421 = 538283) (by norm_num)
theorem B583705 : Blo 566810 583705 := bbase (se 2 (by rfl) ⟨218889, by rfl⟩ : syracuseStep 583705 = 437779) (by norm_num)
theorem B911429 : Blo 566810 911429 := bbase (se 4 (by rfl) ⟨85446, by rfl⟩ : syracuseStep 911429 = 170893) (by norm_num)
theorem B1435765 : Blo 566810 1435765 := bbase (se 5 (by rfl) ⟨67301, by rfl⟩ : syracuseStep 1435765 = 134603) (by norm_num)
theorem B2877605 : Blo 566810 2877605 := bbase (se 4 (by rfl) ⟨269775, by rfl⟩ : syracuseStep 2877605 = 539551) (by norm_num)
theorem B1435877 : Blo 566810 1435877 := bbase (se 4 (by rfl) ⟨134613, by rfl⟩ : syracuseStep 1435877 = 269227) (by norm_num)
theorem B911621 : Blo 566810 911621 := bbase (se 4 (by rfl) ⟨85464, by rfl⟩ : syracuseStep 911621 = 170929) (by norm_num)
theorem B911749 : Blo 566810 911749 := bbase (se 4 (by rfl) ⟨85476, by rfl⟩ : syracuseStep 911749 = 170953) (by norm_num)
theorem B1436069 : Blo 566810 1436069 := bbase (se 4 (by rfl) ⟨134631, by rfl⟩ : syracuseStep 1436069 = 269263) (by norm_num)
theorem B617009 : Blo 566810 617009 := bbase (se 2 (by rfl) ⟨231378, by rfl⟩ : syracuseStep 617009 = 462757) (by norm_num)
theorem B617113 : Blo 566810 617113 := bbase (se 2 (by rfl) ⟨231417, by rfl⟩ : syracuseStep 617113 = 462835) (by norm_num)
theorem B1436413 : Blo 566810 1436413 := bbase (se 3 (by rfl) ⟨269327, by rfl⟩ : syracuseStep 1436413 = 538655) (by norm_num)
theorem B4320053 : Blo 566810 4320053 := bbase (se 5 (by rfl) ⟨202502, by rfl⟩ : syracuseStep 4320053 = 405005) (by norm_num)
theorem B1436525 : Blo 566810 1436525 := bbase (se 3 (by rfl) ⟨269348, by rfl⟩ : syracuseStep 1436525 = 538697) (by norm_num)
theorem B682889 : Blo 566810 682889 := bbase (se 2 (by rfl) ⟨256083, by rfl⟩ : syracuseStep 682889 = 512167) (by norm_num)
theorem B2157461 : Blo 566810 2157461 := bbase (se 6 (by rfl) ⟨50565, by rfl⟩ : syracuseStep 2157461 = 101131) (by norm_num)
theorem B1076141 : Blo 566810 1076141 := bbase (se 3 (by rfl) ⟨201776, by rfl⟩ : syracuseStep 1076141 = 403553) (by norm_num)
theorem B682985 : Blo 566810 682985 := bbase (se 2 (by rfl) ⟨256119, by rfl⟩ : syracuseStep 682985 = 512239) (by norm_num)
theorem B683005 : Blo 566810 683005 := bbase (se 3 (by rfl) ⟨128063, by rfl⟩ : syracuseStep 683005 = 256127) (by norm_num)
theorem B912389 : Blo 566810 912389 := bbase (se 4 (by rfl) ⟨85536, by rfl⟩ : syracuseStep 912389 = 171073) (by norm_num)
theorem B650273 : Blo 566810 650273 := bbase (se 2 (by rfl) ⟨243852, by rfl⟩ : syracuseStep 650273 = 487705) (by norm_num)
theorem B1436717 : Blo 566810 1436717 := bbase (se 3 (by rfl) ⟨269384, by rfl⟩ : syracuseStep 1436717 = 538769) (by norm_num)
theorem B683149 : Blo 566810 683149 := bbase (se 3 (by rfl) ⟨128090, by rfl⟩ : syracuseStep 683149 = 256181) (by norm_num)
theorem B2157749 : Blo 566810 2157749 := bbase (se 5 (by rfl) ⟨101144, by rfl⟩ : syracuseStep 2157749 = 202289) (by norm_num)
theorem B1076429 : Blo 566810 1076429 := bbase (se 3 (by rfl) ⟨201830, by rfl⟩ : syracuseStep 1076429 = 403661) (by norm_num)
theorem B3075317 : Blo 566810 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B1535237 : Blo 566810 1535237 := bbase (se 4 (by rfl) ⟨143928, by rfl⟩ : syracuseStep 1535237 = 287857) (by norm_num)
theorem B1535269 : Blo 566810 1535269 := bbase (se 4 (by rfl) ⟨143931, by rfl⟩ : syracuseStep 1535269 = 287863) (by norm_num)
theorem B748873 : Blo 566810 748873 := bbase (se 2 (by rfl) ⟨280827, by rfl⟩ : syracuseStep 748873 = 561655) (by norm_num)
theorem B1076581 : Blo 566810 1076581 := bbase (se 4 (by rfl) ⟨100929, by rfl⟩ : syracuseStep 1076581 = 201859) (by norm_num)
theorem B1437061 : Blo 566810 1437061 := bbase (se 4 (by rfl) ⟨134724, by rfl⟩ : syracuseStep 1437061 = 269449) (by norm_num)
theorem B2878901 : Blo 566810 2878901 := bbase (se 5 (by rfl) ⟨134948, by rfl⟩ : syracuseStep 2878901 = 269897) (by norm_num)
theorem B912845 : Blo 566810 912845 := bbase (se 3 (by rfl) ⟨171158, by rfl⟩ : syracuseStep 912845 = 342317) (by norm_num)
theorem B1437173 : Blo 566810 1437173 := bbase (se 5 (by rfl) ⟨67367, by rfl⟩ : syracuseStep 1437173 = 134735) (by norm_num)
theorem B1076885 : Blo 566810 1076885 := bbase (se 6 (by rfl) ⟨25239, by rfl⟩ : syracuseStep 1076885 = 50479) (by norm_num)
theorem B913069 : Blo 566810 913069 := bbase (se 3 (by rfl) ⟨171200, by rfl⟩ : syracuseStep 913069 = 342401) (by norm_num)
theorem B1437365 : Blo 566810 1437365 := bbase (se 5 (by rfl) ⟨67376, by rfl⟩ : syracuseStep 1437365 = 134753) (by norm_num)
theorem B1732309 : Blo 566810 1732309 := bbase (se 7 (by rfl) ⟨20300, by rfl⟩ : syracuseStep 1732309 = 40601) (by norm_num)
theorem B913133 : Blo 566810 913133 := bbase (se 3 (by rfl) ⟨171212, by rfl⟩ : syracuseStep 913133 = 342425) (by norm_num)
theorem B913261 : Blo 566810 913261 := bbase (se 3 (by rfl) ⟨171236, by rfl⟩ : syracuseStep 913261 = 342473) (by norm_num)
theorem B1437709 : Blo 566810 1437709 := bbase (se 3 (by rfl) ⟨269570, by rfl⟩ : syracuseStep 1437709 = 539141) (by norm_num)
theorem B1437821 : Blo 566810 1437821 := bbase (se 3 (by rfl) ⟨269591, by rfl⟩ : syracuseStep 1437821 = 539183) (by norm_num)
theorem B4845845 : Blo 566810 4845845 := bbase (se 6 (by rfl) ⟨113574, by rfl⟩ : syracuseStep 4845845 = 227149) (by norm_num)
theorem B1438013 : Blo 566810 1438013 := bbase (se 3 (by rfl) ⟨269627, by rfl⟩ : syracuseStep 1438013 = 539255) (by norm_num)
theorem B2158933 : Blo 566810 2158933 := bbase (se 10 (by rfl) ⟨3162, by rfl⟩ : syracuseStep 2158933 = 6325) (by norm_num)
theorem B1077637 : Blo 566810 1077637 := bbase (se 4 (by rfl) ⟨101028, by rfl⟩ : syracuseStep 1077637 = 202057) (by norm_num)
theorem B4092373 : Blo 566810 4092373 := bbase (se 7 (by rfl) ⟨47957, by rfl⟩ : syracuseStep 4092373 = 95915) (by norm_num)
theorem B1077781 : Blo 566810 1077781 := bbase (se 6 (by rfl) ⟨25260, by rfl⟩ : syracuseStep 1077781 = 50521) (by norm_num)
theorem B717437 : Blo 566810 717437 := bbase (se 3 (by rfl) ⟨134519, by rfl⟩ : syracuseStep 717437 = 269039) (by norm_num)
theorem B2159237 : Blo 566810 2159237 := bbase (se 4 (by rfl) ⟨202428, by rfl⟩ : syracuseStep 2159237 = 404857) (by norm_num)
theorem B1438357 : Blo 566810 1438357 := bbase (se 6 (by rfl) ⟨33711, by rfl⟩ : syracuseStep 1438357 = 67423) (by norm_num)
theorem B717493 : Blo 566810 717493 := bbase (se 5 (by rfl) ⟨33632, by rfl⟩ : syracuseStep 717493 = 67265) (by norm_num)
theorem B1077941 : Blo 566810 1077941 := bbase (se 5 (by rfl) ⟨50528, by rfl⟩ : syracuseStep 1077941 = 101057) (by norm_num)
theorem B2880197 : Blo 566810 2880197 := bbase (se 4 (by rfl) ⟨270018, by rfl⟩ : syracuseStep 2880197 = 540037) (by norm_num)
theorem B1438469 : Blo 566810 1438469 := bbase (se 4 (by rfl) ⟨134856, by rfl⟩ : syracuseStep 1438469 = 269713) (by norm_num)
theorem B717589 : Blo 566810 717589 := bbase (se 6 (by rfl) ⟨16818, by rfl⟩ : syracuseStep 717589 = 33637) (by norm_num)
theorem B1078085 : Blo 566810 1078085 := bbase (se 4 (by rfl) ⟨101070, by rfl⟩ : syracuseStep 1078085 = 202141) (by norm_num)
theorem B684941 : Blo 566810 684941 := bbase (se 3 (by rfl) ⟨128426, by rfl⟩ : syracuseStep 684941 = 256853) (by norm_num)
theorem B717761 : Blo 566810 717761 := bbase (se 2 (by rfl) ⟨269160, by rfl⟩ : syracuseStep 717761 = 538321) (by norm_num)
theorem B1438661 : Blo 566810 1438661 := bbase (se 4 (by rfl) ⟨134874, by rfl⟩ : syracuseStep 1438661 = 269749) (by norm_num)
theorem B717817 : Blo 566810 717817 := bbase (se 2 (by rfl) ⟨269181, by rfl⟩ : syracuseStep 717817 = 538363) (by norm_num)
theorem B2421829 : Blo 566810 2421829 := bbase (se 4 (by rfl) ⟨227046, by rfl⟩ : syracuseStep 2421829 = 454093) (by norm_num)
theorem B717913 : Blo 566810 717913 := bbase (se 2 (by rfl) ⟨269217, by rfl⟩ : syracuseStep 717913 = 538435) (by norm_num)
theorem B1078373 : Blo 566810 1078373 := bbase (se 4 (by rfl) ⟨101097, by rfl⟩ : syracuseStep 1078373 = 202195) (by norm_num)
theorem B685273 : Blo 566810 685273 := bbase (se 2 (by rfl) ⟨256977, by rfl⟩ : syracuseStep 685273 = 513955) (by norm_num)
theorem B1078525 : Blo 566810 1078525 := bbase (se 3 (by rfl) ⟨202223, by rfl⟩ : syracuseStep 1078525 = 404447) (by norm_num)
theorem B718085 : Blo 566810 718085 := bbase (se 4 (by rfl) ⟨67320, by rfl⟩ : syracuseStep 718085 = 134641) (by norm_num)
theorem B1439005 : Blo 566810 1439005 := bbase (se 3 (by rfl) ⟨269813, by rfl⟩ : syracuseStep 1439005 = 539627) (by norm_num)
theorem B718141 : Blo 566810 718141 := bbase (se 3 (by rfl) ⟨134651, by rfl⟩ : syracuseStep 718141 = 269303) (by norm_num)
theorem B685417 : Blo 566810 685417 := bbase (se 2 (by rfl) ⟨257031, by rfl⟩ : syracuseStep 685417 = 514063) (by norm_num)
theorem B1439117 : Blo 566810 1439117 := bbase (se 3 (by rfl) ⟨269834, by rfl⟩ : syracuseStep 1439117 = 539669) (by norm_num)
theorem B718237 : Blo 566810 718237 := bbase (se 3 (by rfl) ⟨134669, by rfl⟩ : syracuseStep 718237 = 269339) (by norm_num)
theorem B1275389 : Blo 566810 1275389 := bbase (se 3 (by rfl) ⟨239135, by rfl⟩ : syracuseStep 1275389 = 478271) (by norm_num)
theorem B1078829 : Blo 566810 1078829 := bbase (se 3 (by rfl) ⟨202280, by rfl⟩ : syracuseStep 1078829 = 404561) (by norm_num)
theorem B1275461 : Blo 566810 1275461 := bbase (se 4 (by rfl) ⟨119574, by rfl⟩ : syracuseStep 1275461 = 239149) (by norm_num)
theorem B718409 : Blo 566810 718409 := bbase (se 2 (by rfl) ⟨269403, by rfl⟩ : syracuseStep 718409 = 538807) (by norm_num)
theorem B1439309 : Blo 566810 1439309 := bbase (se 3 (by rfl) ⟨269870, by rfl⟩ : syracuseStep 1439309 = 539741) (by norm_num)
theorem B718465 : Blo 566810 718465 := bbase (se 2 (by rfl) ⟨269424, by rfl⟩ : syracuseStep 718465 = 538849) (by norm_num)
theorem B1275533 : Blo 566810 1275533 := bbase (se 3 (by rfl) ⟨239162, by rfl⟩ : syracuseStep 1275533 = 478325) (by norm_num)
theorem B1275605 : Blo 566810 1275605 := bbase (se 7 (by rfl) ⟨14948, by rfl⟩ : syracuseStep 1275605 = 29897) (by norm_num)
theorem B718561 : Blo 566810 718561 := bbase (se 2 (by rfl) ⟨269460, by rfl⟩ : syracuseStep 718561 = 538921) (by norm_num)
theorem B1275677 : Blo 566810 1275677 := bbase (se 3 (by rfl) ⟨239189, by rfl⟩ : syracuseStep 1275677 = 478379) (by norm_num)
theorem B1275749 : Blo 566810 1275749 := bbase (se 4 (by rfl) ⟨119601, by rfl⟩ : syracuseStep 1275749 = 239203) (by norm_num)
theorem B718733 : Blo 566810 718733 := bbase (se 3 (by rfl) ⟨134762, by rfl⟩ : syracuseStep 718733 = 269525) (by norm_num)
theorem B1439653 : Blo 566810 1439653 := bbase (se 4 (by rfl) ⟨134967, by rfl⟩ : syracuseStep 1439653 = 269935) (by norm_num)
theorem B1275821 : Blo 566810 1275821 := bbase (se 3 (by rfl) ⟨239216, by rfl⟩ : syracuseStep 1275821 = 478433) (by norm_num)
theorem B718789 : Blo 566810 718789 := bbase (se 4 (by rfl) ⟨67386, by rfl⟩ : syracuseStep 718789 = 134773) (by norm_num)
theorem B2881493 : Blo 566810 2881493 := bbase (se 7 (by rfl) ⟨33767, by rfl⟩ : syracuseStep 2881493 = 67535) (by norm_num)
theorem B1275893 : Blo 566810 1275893 := bbase (se 5 (by rfl) ⟨59807, by rfl⟩ : syracuseStep 1275893 = 119615) (by norm_num)
theorem B1439765 : Blo 566810 1439765 := bbase (se 6 (by rfl) ⟨33744, by rfl⟩ : syracuseStep 1439765 = 67489) (by norm_num)
theorem B718885 : Blo 566810 718885 := bbase (se 4 (by rfl) ⟨67395, by rfl⟩ : syracuseStep 718885 = 134791) (by norm_num)
theorem B4388917 : Blo 566810 4388917 := bbase (se 5 (by rfl) ⟨205730, by rfl⟩ : syracuseStep 4388917 = 411461) (by norm_num)
theorem B1275965 : Blo 566810 1275965 := bbase (se 3 (by rfl) ⟨239243, by rfl⟩ : syracuseStep 1275965 = 478487) (by norm_num)
theorem B1276037 : Blo 566810 1276037 := bbase (se 4 (by rfl) ⟨119628, by rfl⟩ : syracuseStep 1276037 = 239257) (by norm_num)
theorem B1210565 : Blo 566810 1210565 := bbase (se 4 (by rfl) ⟨113490, by rfl⟩ : syracuseStep 1210565 = 226981) (by norm_num)
theorem B1210573 : Blo 566810 1210573 := bbase (se 3 (by rfl) ⟨226982, by rfl⟩ : syracuseStep 1210573 = 453965) (by norm_num)
theorem B1276109 : Blo 566810 1276109 := bbase (se 3 (by rfl) ⟨239270, by rfl⟩ : syracuseStep 1276109 = 478541) (by norm_num)
theorem B719057 : Blo 566810 719057 := bbase (se 2 (by rfl) ⟨269646, by rfl⟩ : syracuseStep 719057 = 539293) (by norm_num)
theorem B1439957 : Blo 566810 1439957 := bbase (se 7 (by rfl) ⟨16874, by rfl⟩ : syracuseStep 1439957 = 33749) (by norm_num)
theorem B719113 : Blo 566810 719113 := bbase (se 2 (by rfl) ⟨269667, by rfl⟩ : syracuseStep 719113 = 539335) (by norm_num)
theorem B1276181 : Blo 566810 1276181 := bbase (se 6 (by rfl) ⟨29910, by rfl⟩ : syracuseStep 1276181 = 59821) (by norm_num)
theorem B2193685 : Blo 566810 2193685 := bbase (se 6 (by rfl) ⟨51414, by rfl⟩ : syracuseStep 2193685 = 102829) (by norm_num)
theorem B1079581 : Blo 566810 1079581 := bbase (se 3 (by rfl) ⟨202421, by rfl⟩ : syracuseStep 1079581 = 404843) (by norm_num)
theorem B850229 : Blo 566810 850229 := bbase (se 5 (by rfl) ⟨39854, by rfl⟩ : syracuseStep 850229 = 79709) (by norm_num)
theorem B850253 : Blo 566810 850253 := bbase (se 3 (by rfl) ⟨159422, by rfl⟩ : syracuseStep 850253 = 318845) (by norm_num)
theorem B1276253 : Blo 566810 1276253 := bbase (se 3 (by rfl) ⟨239297, by rfl⟩ : syracuseStep 1276253 = 478595) (by norm_num)
theorem B850277 : Blo 566810 850277 := bbase (se 4 (by rfl) ⟨79713, by rfl⟩ : syracuseStep 850277 = 159427) (by norm_num)
theorem B719209 : Blo 566810 719209 := bbase (se 2 (by rfl) ⟨269703, by rfl⟩ : syracuseStep 719209 = 539407) (by norm_num)
theorem B850301 : Blo 566810 850301 := bbase (se 3 (by rfl) ⟨159431, by rfl⟩ : syracuseStep 850301 = 318863) (by norm_num)
theorem B850325 : Blo 566810 850325 := bbase (se 6 (by rfl) ⟨19929, by rfl⟩ : syracuseStep 850325 = 39859) (by norm_num)
theorem B1276325 : Blo 566810 1276325 := bbase (se 4 (by rfl) ⟨119655, by rfl⟩ : syracuseStep 1276325 = 239311) (by norm_num)
theorem B850349 : Blo 566810 850349 := bbase (se 3 (by rfl) ⟨159440, by rfl⟩ : syracuseStep 850349 = 318881) (by norm_num)
theorem B1079725 : Blo 566810 1079725 := bbase (se 3 (by rfl) ⟨202448, by rfl⟩ : syracuseStep 1079725 = 404897) (by norm_num)
theorem B850373 : Blo 566810 850373 := bbase (se 4 (by rfl) ⟨79722, by rfl⟩ : syracuseStep 850373 = 159445) (by norm_num)
theorem B850397 : Blo 566810 850397 := bbase (se 3 (by rfl) ⟨159449, by rfl⟩ : syracuseStep 850397 = 318899) (by norm_num)
theorem B1276397 : Blo 566810 1276397 := bbase (se 3 (by rfl) ⟨239324, by rfl⟩ : syracuseStep 1276397 = 478649) (by norm_num)
theorem B850421 : Blo 566810 850421 := bbase (se 5 (by rfl) ⟨39863, by rfl⟩ : syracuseStep 850421 = 79727) (by norm_num)
theorem B1735157 : Blo 566810 1735157 := bbase (se 5 (by rfl) ⟨81335, by rfl⟩ : syracuseStep 1735157 = 162671) (by norm_num)
theorem B850445 : Blo 566810 850445 := bbase (se 3 (by rfl) ⟨159458, by rfl⟩ : syracuseStep 850445 = 318917) (by norm_num)
theorem B2423317 : Blo 566810 2423317 := bbase (se 6 (by rfl) ⟨56796, by rfl⟩ : syracuseStep 2423317 = 113593) (by norm_num)
theorem B719381 : Blo 566810 719381 := bbase (se 6 (by rfl) ⟨16860, by rfl⟩ : syracuseStep 719381 = 33721) (by norm_num)
theorem B850469 : Blo 566810 850469 := bbase (se 4 (by rfl) ⟨79731, by rfl⟩ : syracuseStep 850469 = 159463) (by norm_num)
theorem B2423333 : Blo 566810 2423333 := bbase (se 4 (by rfl) ⟨227187, by rfl⟩ : syracuseStep 2423333 = 454375) (by norm_num)
theorem B1440301 : Blo 566810 1440301 := bbase (se 3 (by rfl) ⟨270056, by rfl⟩ : syracuseStep 1440301 = 540113) (by norm_num)
theorem B1276469 : Blo 566810 1276469 := bbase (se 5 (by rfl) ⟨59834, by rfl⟩ : syracuseStep 1276469 = 119669) (by norm_num)
theorem B850493 : Blo 566810 850493 := bbase (se 3 (by rfl) ⟨159467, by rfl⟩ : syracuseStep 850493 = 318935) (by norm_num)
theorem B719437 : Blo 566810 719437 := bbase (se 3 (by rfl) ⟨134894, by rfl⟩ : syracuseStep 719437 = 269789) (by norm_num)
theorem B1079885 : Blo 566810 1079885 := bbase (se 3 (by rfl) ⟨202478, by rfl⟩ : syracuseStep 1079885 = 404957) (by norm_num)
theorem B850517 : Blo 566810 850517 := bbase (se 8 (by rfl) ⟨4983, by rfl⟩ : syracuseStep 850517 = 9967) (by norm_num)
theorem B3111509 : Blo 566810 3111509 := bbase (se 8 (by rfl) ⟨18231, by rfl⟩ : syracuseStep 3111509 = 36463) (by norm_num)
theorem B850541 : Blo 566810 850541 := bbase (se 3 (by rfl) ⟨159476, by rfl⟩ : syracuseStep 850541 = 318953) (by norm_num)
theorem B1276541 : Blo 566810 1276541 := bbase (se 3 (by rfl) ⟨239351, by rfl⟩ : syracuseStep 1276541 = 478703) (by norm_num)
theorem B850565 : Blo 566810 850565 := bbase (se 4 (by rfl) ⟨79740, by rfl⟩ : syracuseStep 850565 = 159481) (by norm_num)
theorem B850589 : Blo 566810 850589 := bbase (se 3 (by rfl) ⟨159485, by rfl⟩ : syracuseStep 850589 = 318971) (by norm_num)
theorem B1440413 : Blo 566810 1440413 := bbase (se 3 (by rfl) ⟨270077, by rfl⟩ : syracuseStep 1440413 = 540155) (by norm_num)
theorem B719533 : Blo 566810 719533 := bbase (se 3 (by rfl) ⟨134912, by rfl⟩ : syracuseStep 719533 = 269825) (by norm_num)
theorem B850613 : Blo 566810 850613 := bbase (se 5 (by rfl) ⟨39872, by rfl⟩ : syracuseStep 850613 = 79745) (by norm_num)
theorem B1276613 : Blo 566810 1276613 := bbase (se 4 (by rfl) ⟨119682, by rfl⟩ : syracuseStep 1276613 = 239365) (by norm_num)
theorem B2161349 : Blo 566810 2161349 := bbase (se 4 (by rfl) ⟨202626, by rfl⟩ : syracuseStep 2161349 = 405253) (by norm_num)
theorem B850637 : Blo 566810 850637 := bbase (se 3 (by rfl) ⟨159494, by rfl⟩ : syracuseStep 850637 = 318989) (by norm_num)
theorem B1080029 : Blo 566810 1080029 := bbase (se 3 (by rfl) ⟨202505, by rfl⟩ : syracuseStep 1080029 = 405011) (by norm_num)
theorem B850661 : Blo 566810 850661 := bbase (se 4 (by rfl) ⟨79749, by rfl⟩ : syracuseStep 850661 = 159499) (by norm_num)
theorem B850685 : Blo 566810 850685 := bbase (se 3 (by rfl) ⟨159503, by rfl⟩ : syracuseStep 850685 = 319007) (by norm_num)
theorem B1276685 : Blo 566810 1276685 := bbase (se 3 (by rfl) ⟨239378, by rfl⟩ : syracuseStep 1276685 = 478757) (by norm_num)
theorem B850709 : Blo 566810 850709 := bbase (se 6 (by rfl) ⟨19938, by rfl⟩ : syracuseStep 850709 = 39877) (by norm_num)
theorem B850733 : Blo 566810 850733 := bbase (se 3 (by rfl) ⟨159512, by rfl⟩ : syracuseStep 850733 = 319025) (by norm_num)
theorem B850757 : Blo 566810 850757 := bbase (se 4 (by rfl) ⟨79758, by rfl⟩ : syracuseStep 850757 = 159517) (by norm_num)
theorem B1276757 : Blo 566810 1276757 := bbase (se 9 (by rfl) ⟨3740, by rfl⟩ : syracuseStep 1276757 = 7481) (by norm_num)
theorem B719705 : Blo 566810 719705 := bbase (se 2 (by rfl) ⟨269889, by rfl⟩ : syracuseStep 719705 = 539779) (by norm_num)
theorem B850781 : Blo 566810 850781 := bbase (se 3 (by rfl) ⟨159521, by rfl⟩ : syracuseStep 850781 = 319043) (by norm_num)
theorem B1440605 : Blo 566810 1440605 := bbase (se 3 (by rfl) ⟨270113, by rfl⟩ : syracuseStep 1440605 = 540227) (by norm_num)
theorem B850805 : Blo 566810 850805 := bbase (se 5 (by rfl) ⟨39881, by rfl⟩ : syracuseStep 850805 = 79763) (by norm_num)
theorem B850829 : Blo 566810 850829 := bbase (se 3 (by rfl) ⟨159530, by rfl⟩ : syracuseStep 850829 = 319061) (by norm_num)
theorem B719761 : Blo 566810 719761 := bbase (se 2 (by rfl) ⟨269910, by rfl⟩ : syracuseStep 719761 = 539821) (by norm_num)
theorem B1276829 : Blo 566810 1276829 := bbase (se 3 (by rfl) ⟨239405, by rfl⟩ : syracuseStep 1276829 = 478811) (by norm_num)
theorem B850853 : Blo 566810 850853 := bbase (se 4 (by rfl) ⟨79767, by rfl⟩ : syracuseStep 850853 = 159535) (by norm_num)
theorem B850877 : Blo 566810 850877 := bbase (se 3 (by rfl) ⟨159539, by rfl⟩ : syracuseStep 850877 = 319079) (by norm_num)
theorem B850901 : Blo 566810 850901 := bbase (se 7 (by rfl) ⟨9971, by rfl⟩ : syracuseStep 850901 = 19943) (by norm_num)
theorem B818149 : Blo 566810 818149 := bbase (se 4 (by rfl) ⟨76701, by rfl⟩ : syracuseStep 818149 = 153403) (by norm_num)
theorem B1276901 : Blo 566810 1276901 := bbase (se 4 (by rfl) ⟨119709, by rfl⟩ : syracuseStep 1276901 = 239419) (by norm_num)
theorem B2161637 : Blo 566810 2161637 := bbase (se 4 (by rfl) ⟨202653, by rfl⟩ : syracuseStep 2161637 = 405307) (by norm_num)
theorem B850925 : Blo 566810 850925 := bbase (se 3 (by rfl) ⟨159548, by rfl⟩ : syracuseStep 850925 = 319097) (by norm_num)
theorem B719857 : Blo 566810 719857 := bbase (se 2 (by rfl) ⟨269946, by rfl⟩ : syracuseStep 719857 = 539893) (by norm_num)
theorem B1080317 : Blo 566810 1080317 := bbase (se 3 (by rfl) ⟨202559, by rfl⟩ : syracuseStep 1080317 = 405119) (by norm_num)
theorem B850949 : Blo 566810 850949 := bbase (se 4 (by rfl) ⟨79776, by rfl⟩ : syracuseStep 850949 = 159553) (by norm_num)
theorem B850973 : Blo 566810 850973 := bbase (se 3 (by rfl) ⟨159557, by rfl⟩ : syracuseStep 850973 = 319115) (by norm_num)
theorem B1276973 : Blo 566810 1276973 := bbase (se 3 (by rfl) ⟨239432, by rfl⟩ : syracuseStep 1276973 = 478865) (by norm_num)
theorem B850997 : Blo 566810 850997 := bbase (se 5 (by rfl) ⟨39890, by rfl⟩ : syracuseStep 850997 = 79781) (by norm_num)
theorem B818245 : Blo 566810 818245 := bbase (se 4 (by rfl) ⟨76710, by rfl⟩ : syracuseStep 818245 = 153421) (by norm_num)
theorem B851021 : Blo 566810 851021 := bbase (se 3 (by rfl) ⟨159566, by rfl⟩ : syracuseStep 851021 = 319133) (by norm_num)
theorem B851045 : Blo 566810 851045 := bbase (se 4 (by rfl) ⟨79785, by rfl⟩ : syracuseStep 851045 = 159571) (by norm_num)
theorem B1277045 : Blo 566810 1277045 := bbase (se 5 (by rfl) ⟨59861, by rfl⟩ : syracuseStep 1277045 = 119723) (by norm_num)
theorem B851069 : Blo 566810 851069 := bbase (se 3 (by rfl) ⟨159575, by rfl⟩ : syracuseStep 851069 = 319151) (by norm_num)
theorem B851093 : Blo 566810 851093 := bbase (se 6 (by rfl) ⟨19947, by rfl⟩ : syracuseStep 851093 = 39895) (by norm_num)
theorem B1080469 : Blo 566810 1080469 := bbase (se 6 (by rfl) ⟨25323, by rfl⟩ : syracuseStep 1080469 = 50647) (by norm_num)
theorem B720029 : Blo 566810 720029 := bbase (se 3 (by rfl) ⟨135005, by rfl⟩ : syracuseStep 720029 = 270011) (by norm_num)
theorem B851117 : Blo 566810 851117 := bbase (se 3 (by rfl) ⟨159584, by rfl⟩ : syracuseStep 851117 = 319169) (by norm_num)
theorem B4848821 : Blo 566810 4848821 := bbase (se 5 (by rfl) ⟨227288, by rfl⟩ : syracuseStep 4848821 = 454577) (by norm_num)
theorem B1440949 : Blo 566810 1440949 := bbase (se 5 (by rfl) ⟨67544, by rfl⟩ : syracuseStep 1440949 = 135089) (by norm_num)
theorem B1277117 : Blo 566810 1277117 := bbase (se 3 (by rfl) ⟨239459, by rfl⟩ : syracuseStep 1277117 = 478919) (by norm_num)
theorem B851141 : Blo 566810 851141 := bbase (se 4 (by rfl) ⟨79794, by rfl⟩ : syracuseStep 851141 = 159589) (by norm_num)
theorem B720085 : Blo 566810 720085 := bbase (se 7 (by rfl) ⟨8438, by rfl⟩ : syracuseStep 720085 = 16877) (by norm_num)
theorem B851165 : Blo 566810 851165 := bbase (se 3 (by rfl) ⟨159593, by rfl⟩ : syracuseStep 851165 = 319187) (by norm_num)
theorem B2882789 : Blo 566810 2882789 := bbase (se 4 (by rfl) ⟨270261, by rfl⟩ : syracuseStep 2882789 = 540523) (by norm_num)
theorem B851189 : Blo 566810 851189 := bbase (se 5 (by rfl) ⟨39899, by rfl⟩ : syracuseStep 851189 = 79799) (by norm_num)
theorem B1277189 : Blo 566810 1277189 := bbase (se 4 (by rfl) ⟨119736, by rfl⟩ : syracuseStep 1277189 = 239473) (by norm_num)
theorem B851213 : Blo 566810 851213 := bbase (se 3 (by rfl) ⟨159602, by rfl⟩ : syracuseStep 851213 = 319205) (by norm_num)
theorem B851237 : Blo 566810 851237 := bbase (se 4 (by rfl) ⟨79803, by rfl⟩ : syracuseStep 851237 = 159607) (by norm_num)
theorem B1441061 : Blo 566810 1441061 := bbase (se 4 (by rfl) ⟨135099, by rfl⟩ : syracuseStep 1441061 = 270199) (by norm_num)
theorem B1211701 : Blo 566810 1211701 := bbase (se 5 (by rfl) ⟨56798, by rfl⟩ : syracuseStep 1211701 = 113597) (by norm_num)
theorem B720181 : Blo 566810 720181 := bbase (se 5 (by rfl) ⟨33758, by rfl⟩ : syracuseStep 720181 = 67517) (by norm_num)
theorem B851261 : Blo 566810 851261 := bbase (se 3 (by rfl) ⟨159611, by rfl⟩ : syracuseStep 851261 = 319223) (by norm_num)
theorem B1277261 : Blo 566810 1277261 := bbase (se 3 (by rfl) ⟨239486, by rfl⟩ : syracuseStep 1277261 = 478973) (by norm_num)
theorem B851285 : Blo 566810 851285 := bbase (se 11 (by rfl) ⟨623, by rfl⟩ : syracuseStep 851285 = 1247) (by norm_num)
theorem B851309 : Blo 566810 851309 := bbase (se 3 (by rfl) ⟨159620, by rfl⟩ : syracuseStep 851309 = 319241) (by norm_num)
theorem B851333 : Blo 566810 851333 := bbase (se 4 (by rfl) ⟨79812, by rfl⟩ : syracuseStep 851333 = 159625) (by norm_num)
theorem B1277333 : Blo 566810 1277333 := bbase (se 6 (by rfl) ⟨29937, by rfl⟩ : syracuseStep 1277333 = 59875) (by norm_num)
theorem B851357 : Blo 566810 851357 := bbase (se 3 (by rfl) ⟨159629, by rfl⟩ : syracuseStep 851357 = 319259) (by norm_num)
theorem B851381 : Blo 566810 851381 := bbase (se 5 (by rfl) ⟨39908, by rfl⟩ : syracuseStep 851381 = 79817) (by norm_num)
theorem B1080773 : Blo 566810 1080773 := bbase (se 4 (by rfl) ⟨101322, by rfl⟩ : syracuseStep 1080773 = 202645) (by norm_num)
theorem B851405 : Blo 566810 851405 := bbase (se 3 (by rfl) ⟨159638, by rfl⟩ : syracuseStep 851405 = 319277) (by norm_num)
theorem B1277405 : Blo 566810 1277405 := bbase (se 3 (by rfl) ⟨239513, by rfl⟩ : syracuseStep 1277405 = 479027) (by norm_num)
theorem B720353 : Blo 566810 720353 := bbase (se 2 (by rfl) ⟨270132, by rfl⟩ : syracuseStep 720353 = 540265) (by norm_num)
theorem B851429 : Blo 566810 851429 := bbase (se 4 (by rfl) ⟨79821, by rfl⟩ : syracuseStep 851429 = 159643) (by norm_num)
theorem B1441253 : Blo 566810 1441253 := bbase (se 4 (by rfl) ⟨135117, by rfl⟩ : syracuseStep 1441253 = 270235) (by norm_num)
theorem B851453 : Blo 566810 851453 := bbase (se 3 (by rfl) ⟨159647, by rfl⟩ : syracuseStep 851453 = 319295) (by norm_num)
theorem B851477 : Blo 566810 851477 := bbase (se 6 (by rfl) ⟨19956, by rfl⟩ : syracuseStep 851477 = 39913) (by norm_num)
theorem B720409 : Blo 566810 720409 := bbase (se 2 (by rfl) ⟨270153, by rfl⟩ : syracuseStep 720409 = 540307) (by norm_num)
theorem B1277477 : Blo 566810 1277477 := bbase (se 4 (by rfl) ⟨119763, by rfl⟩ : syracuseStep 1277477 = 239527) (by norm_num)
theorem B851501 : Blo 566810 851501 := bbase (se 3 (by rfl) ⟨159656, by rfl⟩ : syracuseStep 851501 = 319313) (by norm_num)
theorem B851525 : Blo 566810 851525 := bbase (se 4 (by rfl) ⟨79830, by rfl⟩ : syracuseStep 851525 = 159661) (by norm_num)
theorem B851549 : Blo 566810 851549 := bbase (se 3 (by rfl) ⟨159665, by rfl⟩ : syracuseStep 851549 = 319331) (by norm_num)
theorem B1277549 : Blo 566810 1277549 := bbase (se 3 (by rfl) ⟨239540, by rfl⟩ : syracuseStep 1277549 = 479081) (by norm_num)
theorem B851573 : Blo 566810 851573 := bbase (se 5 (by rfl) ⟨39917, by rfl⟩ : syracuseStep 851573 = 79835) (by norm_num)
theorem B720505 : Blo 566810 720505 := bbase (se 2 (by rfl) ⟨270189, by rfl⟩ : syracuseStep 720505 = 540379) (by norm_num)
theorem B851597 : Blo 566810 851597 := bbase (se 3 (by rfl) ⟨159674, by rfl⟩ : syracuseStep 851597 = 319349) (by norm_num)
theorem B851621 : Blo 566810 851621 := bbase (se 4 (by rfl) ⟨79839, by rfl⟩ : syracuseStep 851621 = 159679) (by norm_num)
theorem B1212077 : Blo 566810 1212077 := bbase (se 3 (by rfl) ⟨227264, by rfl⟩ : syracuseStep 1212077 = 454529) (by norm_num)
theorem B1277621 : Blo 566810 1277621 := bbase (se 5 (by rfl) ⟨59888, by rfl⟩ : syracuseStep 1277621 = 119777) (by norm_num)
theorem B851645 : Blo 566810 851645 := bbase (se 3 (by rfl) ⟨159683, by rfl⟩ : syracuseStep 851645 = 319367) (by norm_num)
theorem B851669 : Blo 566810 851669 := bbase (se 7 (by rfl) ⟨9980, by rfl⟩ : syracuseStep 851669 = 19961) (by norm_num)
theorem B851693 : Blo 566810 851693 := bbase (se 3 (by rfl) ⟨159692, by rfl⟩ : syracuseStep 851693 = 319385) (by norm_num)
theorem B1277693 : Blo 566810 1277693 := bbase (se 3 (by rfl) ⟨239567, by rfl⟩ : syracuseStep 1277693 = 479135) (by norm_num)
theorem B851717 : Blo 566810 851717 := bbase (se 4 (by rfl) ⟨79848, by rfl⟩ : syracuseStep 851717 = 159697) (by norm_num)
theorem B851741 : Blo 566810 851741 := bbase (se 3 (by rfl) ⟨159701, by rfl⟩ : syracuseStep 851741 = 319403) (by norm_num)
theorem B720677 : Blo 566810 720677 := bbase (se 4 (by rfl) ⟨67563, by rfl⟩ : syracuseStep 720677 = 135127) (by norm_num)
theorem B851765 : Blo 566810 851765 := bbase (se 5 (by rfl) ⟨39926, by rfl⟩ : syracuseStep 851765 = 79853) (by norm_num)
theorem B1441597 : Blo 566810 1441597 := bbase (se 3 (by rfl) ⟨270299, by rfl⟩ : syracuseStep 1441597 = 540599) (by norm_num)
theorem B1277765 : Blo 566810 1277765 := bbase (se 4 (by rfl) ⟨119790, by rfl⟩ : syracuseStep 1277765 = 239581) (by norm_num)
theorem B851789 : Blo 566810 851789 := bbase (se 3 (by rfl) ⟨159710, by rfl⟩ : syracuseStep 851789 = 319421) (by norm_num)
theorem B720733 : Blo 566810 720733 := bbase (se 3 (by rfl) ⟨135137, by rfl⟩ : syracuseStep 720733 = 270275) (by norm_num)
theorem B851813 : Blo 566810 851813 := bbase (se 4 (by rfl) ⟨79857, by rfl⟩ : syracuseStep 851813 = 159715) (by norm_num)
theorem B851837 : Blo 566810 851837 := bbase (se 3 (by rfl) ⟨159719, by rfl⟩ : syracuseStep 851837 = 319439) (by norm_num)
theorem B1277837 : Blo 566810 1277837 := bbase (se 3 (by rfl) ⟨239594, by rfl⟩ : syracuseStep 1277837 = 479189) (by norm_num)
theorem B851861 : Blo 566810 851861 := bbase (se 6 (by rfl) ⟨19965, by rfl⟩ : syracuseStep 851861 = 39931) (by norm_num)
theorem B851885 : Blo 566810 851885 := bbase (se 3 (by rfl) ⟨159728, by rfl⟩ : syracuseStep 851885 = 319457) (by norm_num)
theorem B1441709 : Blo 566810 1441709 := bbase (se 3 (by rfl) ⟨270320, by rfl⟩ : syracuseStep 1441709 = 540641) (by norm_num)
theorem B720829 : Blo 566810 720829 := bbase (se 3 (by rfl) ⟨135155, by rfl⟩ : syracuseStep 720829 = 270311) (by norm_num)
theorem B851909 : Blo 566810 851909 := bbase (se 4 (by rfl) ⟨79866, by rfl⟩ : syracuseStep 851909 = 159733) (by norm_num)
theorem B1277909 : Blo 566810 1277909 := bbase (se 7 (by rfl) ⟨14975, by rfl⟩ : syracuseStep 1277909 = 29951) (by norm_num)
theorem B851933 : Blo 566810 851933 := bbase (se 3 (by rfl) ⟨159737, by rfl⟩ : syracuseStep 851933 = 319475) (by norm_num)
theorem B851957 : Blo 566810 851957 := bbase (se 5 (by rfl) ⟨39935, by rfl⟩ : syracuseStep 851957 = 79871) (by norm_num)
theorem B851969 : Blo 566810 851969 := bstep (se 2 (by rfl) ⟨319488, by rfl⟩ : syracuseStep 851969 = 638977) B638977
theorem B851987 : Blo 566810 851987 := bstep (se 1 (by rfl) ⟨638990, by rfl⟩ : syracuseStep 851987 = 1277981) B1277981
theorem B852017 : Blo 566810 852017 := bstep (se 2 (by rfl) ⟨319506, by rfl⟩ : syracuseStep 852017 = 639013) B639013
theorem B9732149 : Blo 566810 9732149 := bstep (se 5 (by rfl) ⟨456194, by rfl⟩ : syracuseStep 9732149 = 912389) B912389
theorem B852035 : Blo 566810 852035 := bstep (se 1 (by rfl) ⟨639026, by rfl⟩ : syracuseStep 852035 = 1278053) B1278053
theorem B852065 : Blo 566810 852065 := bstep (se 2 (by rfl) ⟨319524, by rfl⟩ : syracuseStep 852065 = 639049) B639049
theorem B852083 : Blo 566810 852083 := bstep (se 1 (by rfl) ⟨639062, by rfl⟩ : syracuseStep 852083 = 1278125) B1278125
theorem B3113093 : Blo 566810 3113093 := bstep (se 4 (by rfl) ⟨291852, by rfl⟩ : syracuseStep 3113093 = 583705) B583705
theorem B2424973 : Blo 566810 2424973 := bstep (se 3 (by rfl) ⟨454682, by rfl⟩ : syracuseStep 2424973 = 909365) B909365
theorem B852113 : Blo 566810 852113 := bstep (se 2 (by rfl) ⟨319542, by rfl⟩ : syracuseStep 852113 = 639085) B639085
theorem B852131 : Blo 566810 852131 := bstep (se 1 (by rfl) ⟨639098, by rfl⟩ : syracuseStep 852131 = 1278197) B1278197
theorem B2883761 : Blo 566810 2883761 := bstep (se 2 (by rfl) ⟨1081410, by rfl⟩ : syracuseStep 2883761 = 2162821) B2162821
theorem B852161 : Blo 566810 852161 := bstep (se 2 (by rfl) ⟨319560, by rfl⟩ : syracuseStep 852161 = 639121) B639121
theorem B1278161 : Blo 566810 1278161 := bstep (se 2 (by rfl) ⟨479310, by rfl⟩ : syracuseStep 1278161 = 958621) B958621
theorem B852179 : Blo 566810 852179 := bstep (se 1 (by rfl) ⟨639134, by rfl⟩ : syracuseStep 852179 = 1278269) B1278269
theorem B1278179 : Blo 566810 1278179 := bstep (se 1 (by rfl) ⟨958634, by rfl⟩ : syracuseStep 1278179 = 1917269) B1917269
theorem B852209 : Blo 566810 852209 := bstep (se 2 (by rfl) ⟨319578, by rfl⟩ : syracuseStep 852209 = 639157) B639157
theorem B1442033 : Blo 566810 1442033 := bstep (se 2 (by rfl) ⟨540762, by rfl⟩ : syracuseStep 1442033 = 1081525) B1081525
theorem B852227 : Blo 566810 852227 := bstep (se 1 (by rfl) ⟨639170, by rfl⟩ : syracuseStep 852227 = 1278341) B1278341
theorem B852257 : Blo 566810 852257 := bstep (se 2 (by rfl) ⟨319596, by rfl⟩ : syracuseStep 852257 = 639193) B639193
theorem B1442083 : Blo 566810 1442083 := bstep (se 1 (by rfl) ⟨1081562, by rfl⟩ : syracuseStep 1442083 = 2163125) B2163125
theorem B852275 : Blo 566810 852275 := bstep (se 1 (by rfl) ⟨639206, by rfl⟩ : syracuseStep 852275 = 1278413) B1278413
theorem B721219 : Blo 566810 721219 := bstep (se 1 (by rfl) ⟨540914, by rfl⟩ : syracuseStep 721219 = 1081829) B1081829
theorem B852305 : Blo 566810 852305 := bstep (se 2 (by rfl) ⟨319614, by rfl⟩ : syracuseStep 852305 = 639229) B639229
theorem B852323 : Blo 566810 852323 := bstep (se 1 (by rfl) ⟨639242, by rfl⟩ : syracuseStep 852323 = 1278485) B1278485
theorem B852353 : Blo 566810 852353 := bstep (se 2 (by rfl) ⟨319632, by rfl⟩ : syracuseStep 852353 = 639265) B639265
theorem B1081745 : Blo 566810 1081745 := bstep (se 2 (by rfl) ⟨405654, by rfl⟩ : syracuseStep 1081745 = 811309) B811309
theorem B852371 : Blo 566810 852371 := bstep (se 1 (by rfl) ⟨639278, by rfl⟩ : syracuseStep 852371 = 1278557) B1278557
theorem B721315 : Blo 566810 721315 := bstep (se 1 (by rfl) ⟨540986, by rfl⟩ : syracuseStep 721315 = 1081973) B1081973
theorem B852401 : Blo 566810 852401 := bstep (se 2 (by rfl) ⟨319650, by rfl⟩ : syracuseStep 852401 = 639301) B639301
theorem B1442225 : Blo 566810 1442225 := bstep (se 2 (by rfl) ⟨540834, by rfl⟩ : syracuseStep 1442225 = 1081669) B1081669
theorem B852419 : Blo 566810 852419 := bstep (se 1 (by rfl) ⟨639314, by rfl⟩ : syracuseStep 852419 = 1278629) B1278629
theorem B852449 : Blo 566810 852449 := bstep (se 2 (by rfl) ⟨319668, by rfl⟩ : syracuseStep 852449 = 639337) B639337
theorem B2425315 : Blo 566810 2425315 := bstep (se 1 (by rfl) ⟨1818986, by rfl⟩ : syracuseStep 2425315 = 3637973) B3637973
theorem B1278449 : Blo 566810 1278449 := bstep (se 2 (by rfl) ⟨479418, by rfl⟩ : syracuseStep 1278449 = 958837) B958837
theorem B852467 : Blo 566810 852467 := bstep (se 1 (by rfl) ⟨639350, by rfl⟩ : syracuseStep 852467 = 1278701) B1278701
theorem B1212931 : Blo 566810 1212931 := bstep (se 1 (by rfl) ⟨909698, by rfl⟩ : syracuseStep 1212931 = 1819397) B1819397
theorem B1278467 : Blo 566810 1278467 := bstep (se 1 (by rfl) ⟨958850, by rfl⟩ : syracuseStep 1278467 = 1917701) B1917701
theorem B852497 : Blo 566810 852497 := bstep (se 2 (by rfl) ⟨319686, by rfl⟩ : syracuseStep 852497 = 639373) B639373
theorem B852515 : Blo 566810 852515 := bstep (se 1 (by rfl) ⟨639386, by rfl⟩ : syracuseStep 852515 = 1278773) B1278773
theorem B852545 : Blo 566810 852545 := bstep (se 2 (by rfl) ⟨319704, by rfl⟩ : syracuseStep 852545 = 639409) B639409
theorem B852563 : Blo 566810 852563 := bstep (se 1 (by rfl) ⟨639422, by rfl⟩ : syracuseStep 852563 = 1278845) B1278845
theorem B3244643 : Blo 566810 3244643 := bstep (se 1 (by rfl) ⟨2433482, by rfl⟩ : syracuseStep 3244643 = 4866965) B4866965
theorem B852593 : Blo 566810 852593 := bstep (se 2 (by rfl) ⟨319722, by rfl⟩ : syracuseStep 852593 = 639445) B639445
theorem B852611 : Blo 566810 852611 := bstep (se 1 (by rfl) ⟨639458, by rfl⟩ : syracuseStep 852611 = 1278917) B1278917
theorem B852641 : Blo 566810 852641 := bstep (se 2 (by rfl) ⟨319740, by rfl⟩ : syracuseStep 852641 = 639481) B639481
theorem B852659 : Blo 566810 852659 := bstep (se 1 (by rfl) ⟨639494, by rfl⟩ : syracuseStep 852659 = 1278989) B1278989
theorem B1966787 : Blo 566810 1966787 := bstep (se 1 (by rfl) ⟨1475090, by rfl⟩ : syracuseStep 1966787 = 2950181) B2950181
theorem B852689 : Blo 566810 852689 := bstep (se 2 (by rfl) ⟨319758, by rfl⟩ : syracuseStep 852689 = 639517) B639517
theorem B852707 : Blo 566810 852707 := bstep (se 1 (by rfl) ⟨639530, by rfl⟩ : syracuseStep 852707 = 1279061) B1279061
theorem B852737 : Blo 566810 852737 := bstep (se 2 (by rfl) ⟨319776, by rfl⟩ : syracuseStep 852737 = 639553) B639553
theorem B1278737 : Blo 566810 1278737 := bstep (se 2 (by rfl) ⟨479526, by rfl⟩ : syracuseStep 1278737 = 959053) B959053
theorem B852755 : Blo 566810 852755 := bstep (se 1 (by rfl) ⟨639566, by rfl⟩ : syracuseStep 852755 = 1279133) B1279133
theorem B1278755 : Blo 566810 1278755 := bstep (se 1 (by rfl) ⟨959066, by rfl⟩ : syracuseStep 1278755 = 1918133) B1918133
theorem B852785 : Blo 566810 852785 := bstep (se 2 (by rfl) ⟨319794, by rfl⟩ : syracuseStep 852785 = 639589) B639589
theorem B852803 : Blo 566810 852803 := bstep (se 1 (by rfl) ⟨639602, by rfl⟩ : syracuseStep 852803 = 1279205) B1279205
theorem B852833 : Blo 566810 852833 := bstep (se 2 (by rfl) ⟨319812, by rfl⟩ : syracuseStep 852833 = 639625) B639625
theorem B852851 : Blo 566810 852851 := bstep (se 1 (by rfl) ⟨639638, by rfl⟩ : syracuseStep 852851 = 1279277) B1279277
theorem B1868689 : Blo 566810 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B852881 : Blo 566810 852881 := bstep (se 2 (by rfl) ⟨319830, by rfl⟩ : syracuseStep 852881 = 639661) B639661
theorem B721811 : Blo 566810 721811 := bstep (se 1 (by rfl) ⟨541358, by rfl⟩ : syracuseStep 721811 = 1082717) B1082717
theorem B852899 : Blo 566810 852899 := bstep (se 1 (by rfl) ⟨639674, by rfl⟩ : syracuseStep 852899 = 1279349) B1279349
theorem B852929 : Blo 566810 852929 := bstep (se 2 (by rfl) ⟨319848, by rfl⟩ : syracuseStep 852929 = 639697) B639697
theorem B1213393 : Blo 566810 1213393 := bstep (se 2 (by rfl) ⟨455022, by rfl⟩ : syracuseStep 1213393 = 910045) B910045
theorem B852947 : Blo 566810 852947 := bstep (se 1 (by rfl) ⟨639710, by rfl⟩ : syracuseStep 852947 = 1279421) B1279421
theorem B4326371 : Blo 566810 4326371 := bstep (se 1 (by rfl) ⟨3244778, by rfl⟩ : syracuseStep 4326371 = 6489557) B6489557
theorem B852977 : Blo 566810 852977 := bstep (se 2 (by rfl) ⟨319866, by rfl⟩ : syracuseStep 852977 = 639733) B639733
theorem B852995 : Blo 566810 852995 := bstep (se 1 (by rfl) ⟨639746, by rfl⟩ : syracuseStep 852995 = 1279493) B1279493
theorem B853025 : Blo 566810 853025 := bstep (se 2 (by rfl) ⟨319884, by rfl⟩ : syracuseStep 853025 = 639769) B639769
theorem B1279025 : Blo 566810 1279025 := bstep (se 2 (by rfl) ⟨479634, by rfl⟩ : syracuseStep 1279025 = 959269) B959269
theorem B853043 : Blo 566810 853043 := bstep (se 1 (by rfl) ⟨639782, by rfl⟩ : syracuseStep 853043 = 1279565) B1279565
theorem B1279043 : Blo 566810 1279043 := bstep (se 1 (by rfl) ⟨959282, by rfl⟩ : syracuseStep 1279043 = 1918565) B1918565
theorem B853073 : Blo 566810 853073 := bstep (se 2 (by rfl) ⟨319902, by rfl⟩ : syracuseStep 853073 = 639805) B639805
theorem B853091 : Blo 566810 853091 := bstep (se 1 (by rfl) ⟨639818, by rfl⟩ : syracuseStep 853091 = 1279637) B1279637
theorem B853121 : Blo 566810 853121 := bstep (se 2 (by rfl) ⟨319920, by rfl⟩ : syracuseStep 853121 = 639841) B639841
theorem B853139 : Blo 566810 853139 := bstep (se 1 (by rfl) ⟨639854, by rfl⟩ : syracuseStep 853139 = 1279709) B1279709
theorem B853169 : Blo 566810 853169 := bstep (se 2 (by rfl) ⟨319938, by rfl⟩ : syracuseStep 853169 = 639877) B639877
theorem B853187 : Blo 566810 853187 := bstep (se 1 (by rfl) ⟨639890, by rfl⟩ : syracuseStep 853187 = 1279781) B1279781
theorem B853217 : Blo 566810 853217 := bstep (se 2 (by rfl) ⟨319956, by rfl⟩ : syracuseStep 853217 = 639913) B639913
theorem B853235 : Blo 566810 853235 := bstep (se 1 (by rfl) ⟨639926, by rfl⟩ : syracuseStep 853235 = 1279853) B1279853
theorem B853265 : Blo 566810 853265 := bstep (se 2 (by rfl) ⟨319974, by rfl⟩ : syracuseStep 853265 = 639949) B639949
theorem B1082641 : Blo 566810 1082641 := bstep (se 2 (by rfl) ⟨405990, by rfl⟩ : syracuseStep 1082641 = 811981) B811981
theorem B853283 : Blo 566810 853283 := bstep (se 1 (by rfl) ⟨639962, by rfl⟩ : syracuseStep 853283 = 1279925) B1279925
theorem B853313 : Blo 566810 853313 := bstep (se 2 (by rfl) ⟨319992, by rfl⟩ : syracuseStep 853313 = 639985) B639985
theorem B1279313 : Blo 566810 1279313 := bstep (se 2 (by rfl) ⟨479742, by rfl⟩ : syracuseStep 1279313 = 959485) B959485
theorem B853331 : Blo 566810 853331 := bstep (se 1 (by rfl) ⟨639998, by rfl⟩ : syracuseStep 853331 = 1279997) B1279997
theorem B1279331 : Blo 566810 1279331 := bstep (se 1 (by rfl) ⟨959498, by rfl⟩ : syracuseStep 1279331 = 1918997) B1918997
theorem B2164067 : Blo 566810 2164067 := bstep (se 1 (by rfl) ⟨1623050, by rfl⟩ : syracuseStep 2164067 = 3246101) B3246101
theorem B853361 : Blo 566810 853361 := bstep (se 2 (by rfl) ⟨320010, by rfl⟩ : syracuseStep 853361 = 640021) B640021
theorem B853379 : Blo 566810 853379 := bstep (se 1 (by rfl) ⟨640034, by rfl⟩ : syracuseStep 853379 = 1280069) B1280069
theorem B1443217 : Blo 566810 1443217 := bstep (se 2 (by rfl) ⟨541206, by rfl⟩ : syracuseStep 1443217 = 1082413) B1082413
theorem B853409 : Blo 566810 853409 := bstep (se 2 (by rfl) ⟨320028, by rfl⟩ : syracuseStep 853409 = 640057) B640057
theorem B1082801 : Blo 566810 1082801 := bstep (se 2 (by rfl) ⟨406050, by rfl⟩ : syracuseStep 1082801 = 812101) B812101
theorem B853427 : Blo 566810 853427 := bstep (se 1 (by rfl) ⟨640070, by rfl⟩ : syracuseStep 853427 = 1280141) B1280141
theorem B11699653 : Blo 566810 11699653 := bstep (se 4 (by rfl) ⟨1096842, by rfl⟩ : syracuseStep 11699653 = 2193685) B2193685
theorem B853457 : Blo 566810 853457 := bstep (se 2 (by rfl) ⟨320046, by rfl⟩ : syracuseStep 853457 = 640093) B640093
theorem B853475 : Blo 566810 853475 := bstep (se 1 (by rfl) ⟨640106, by rfl⟩ : syracuseStep 853475 = 1280213) B1280213
theorem B853505 : Blo 566810 853505 := bstep (se 2 (by rfl) ⟨320064, by rfl⟩ : syracuseStep 853505 = 640129) B640129
theorem B853523 : Blo 566810 853523 := bstep (se 1 (by rfl) ⟨640142, by rfl⟩ : syracuseStep 853523 = 1280285) B1280285
theorem B853553 : Blo 566810 853553 := bstep (se 2 (by rfl) ⟨320082, by rfl⟩ : syracuseStep 853553 = 640165) B640165
theorem B853571 : Blo 566810 853571 := bstep (se 1 (by rfl) ⟨640178, by rfl⟩ : syracuseStep 853571 = 1280357) B1280357
theorem B853601 : Blo 566810 853601 := bstep (se 2 (by rfl) ⟨320100, by rfl⟩ : syracuseStep 853601 = 640201) B640201
theorem B2885219 : Blo 566810 2885219 := bstep (se 1 (by rfl) ⟨2163914, by rfl⟩ : syracuseStep 2885219 = 4327829) B4327829
theorem B1279601 : Blo 566810 1279601 := bstep (se 2 (by rfl) ⟨479850, by rfl⟩ : syracuseStep 1279601 = 959701) B959701
theorem B853619 : Blo 566810 853619 := bstep (se 1 (by rfl) ⟨640214, by rfl⟩ : syracuseStep 853619 = 1280429) B1280429
theorem B1279619 : Blo 566810 1279619 := bstep (se 1 (by rfl) ⟨959714, by rfl⟩ : syracuseStep 1279619 = 1919429) B1919429
theorem B853649 : Blo 566810 853649 := bstep (se 2 (by rfl) ⟨320118, by rfl⟩ : syracuseStep 853649 = 640237) B640237
theorem B853667 : Blo 566810 853667 := bstep (se 1 (by rfl) ⟨640250, by rfl⟩ : syracuseStep 853667 = 1280501) B1280501
theorem B1443491 : Blo 566810 1443491 := bstep (se 1 (by rfl) ⟨1082618, by rfl⟩ : syracuseStep 1443491 = 2165237) B2165237
theorem B853697 : Blo 566810 853697 := bstep (se 2 (by rfl) ⟨320136, by rfl⟩ : syracuseStep 853697 = 640273) B640273
theorem B853715 : Blo 566810 853715 := bstep (se 1 (by rfl) ⟨640286, by rfl⟩ : syracuseStep 853715 = 1280573) B1280573
theorem B853745 : Blo 566810 853745 := bstep (se 2 (by rfl) ⟨320154, by rfl⟩ : syracuseStep 853745 = 640309) B640309
theorem B853763 : Blo 566810 853763 := bstep (se 1 (by rfl) ⟨640322, by rfl⟩ : syracuseStep 853763 = 1280645) B1280645
theorem B853793 : Blo 566810 853793 := bstep (se 2 (by rfl) ⟨320172, by rfl⟩ : syracuseStep 853793 = 640345) B640345
theorem B853811 : Blo 566810 853811 := bstep (se 1 (by rfl) ⟨640358, by rfl⟩ : syracuseStep 853811 = 1280717) B1280717
theorem B1083203 : Blo 566810 1083203 := bstep (se 1 (by rfl) ⟨812402, by rfl⟩ : syracuseStep 1083203 = 1624805) B1624805
theorem B853841 : Blo 566810 853841 := bstep (se 2 (by rfl) ⟨320190, by rfl⟩ : syracuseStep 853841 = 640381) B640381
theorem B853859 : Blo 566810 853859 := bstep (se 1 (by rfl) ⟨640394, by rfl⟩ : syracuseStep 853859 = 1280789) B1280789
theorem B1443683 : Blo 566810 1443683 := bstep (se 1 (by rfl) ⟨1082762, by rfl⟩ : syracuseStep 1443683 = 2165525) B2165525
theorem B853889 : Blo 566810 853889 := bstep (se 2 (by rfl) ⟨320208, by rfl⟩ : syracuseStep 853889 = 640417) B640417
theorem B1279889 : Blo 566810 1279889 := bstep (se 2 (by rfl) ⟨479958, by rfl⟩ : syracuseStep 1279889 = 959917) B959917
theorem B853907 : Blo 566810 853907 := bstep (se 1 (by rfl) ⟨640430, by rfl⟩ : syracuseStep 853907 = 1280861) B1280861
theorem B1279907 : Blo 566810 1279907 := bstep (se 1 (by rfl) ⟨959930, by rfl⟩ : syracuseStep 1279907 = 1919861) B1919861
theorem B853937 : Blo 566810 853937 := bstep (se 2 (by rfl) ⟨320226, by rfl⟩ : syracuseStep 853937 = 640453) B640453
theorem B853955 : Blo 566810 853955 := bstep (se 1 (by rfl) ⟨640466, by rfl⟩ : syracuseStep 853955 = 1280933) B1280933
theorem B853985 : Blo 566810 853985 := bstep (se 2 (by rfl) ⟨320244, by rfl⟩ : syracuseStep 853985 = 640489) B640489
theorem B1214435 : Blo 566810 1214435 := bstep (se 1 (by rfl) ⟨910826, by rfl⟩ : syracuseStep 1214435 = 1821653) B1821653
theorem B854003 : Blo 566810 854003 := bstep (se 1 (by rfl) ⟨640502, by rfl⟩ : syracuseStep 854003 = 1281005) B1281005
theorem B1640461 : Blo 566810 1640461 := bstep (se 3 (by rfl) ⟨307586, by rfl⟩ : syracuseStep 1640461 = 615173) B615173
theorem B854033 : Blo 566810 854033 := bstep (se 2 (by rfl) ⟨320262, by rfl⟩ : syracuseStep 854033 = 640525) B640525
theorem B854051 : Blo 566810 854051 := bstep (se 1 (by rfl) ⟨640538, by rfl⟩ : syracuseStep 854051 = 1281077) B1281077
theorem B854081 : Blo 566810 854081 := bstep (se 2 (by rfl) ⟨320280, by rfl⟩ : syracuseStep 854081 = 640561) B640561
theorem B854099 : Blo 566810 854099 := bstep (se 1 (by rfl) ⟨640574, by rfl⟩ : syracuseStep 854099 = 1281149) B1281149
theorem B1542253 : Blo 566810 1542253 := bstep (se 3 (by rfl) ⟨289172, by rfl⟩ : syracuseStep 1542253 = 578345) B578345
theorem B854129 : Blo 566810 854129 := bstep (se 2 (by rfl) ⟨320298, by rfl⟩ : syracuseStep 854129 = 640597) B640597
theorem B854147 : Blo 566810 854147 := bstep (se 1 (by rfl) ⟨640610, by rfl⟩ : syracuseStep 854147 = 1281221) B1281221
theorem B854177 : Blo 566810 854177 := bstep (se 2 (by rfl) ⟨320316, by rfl⟩ : syracuseStep 854177 = 640633) B640633
theorem B1280177 : Blo 566810 1280177 := bstep (se 2 (by rfl) ⟨480066, by rfl⟩ : syracuseStep 1280177 = 960133) B960133
theorem B690355 : Blo 566810 690355 := bstep (se 1 (by rfl) ⟨517766, by rfl⟩ : syracuseStep 690355 = 1035533) B1035533
theorem B854195 : Blo 566810 854195 := bstep (se 1 (by rfl) ⟨640646, by rfl⟩ : syracuseStep 854195 = 1281293) B1281293
theorem B1280195 : Blo 566810 1280195 := bstep (se 1 (by rfl) ⟨960146, by rfl⟩ : syracuseStep 1280195 = 1920293) B1920293
theorem B854225 : Blo 566810 854225 := bstep (se 2 (by rfl) ⟨320334, by rfl⟩ : syracuseStep 854225 = 640669) B640669
theorem B35064035 : Blo 566810 35064035 := bstep (se 1 (by rfl) ⟨26298026, by rfl⟩ : syracuseStep 35064035 = 52596053) B52596053
theorem B854243 : Blo 566810 854243 := bstep (se 1 (by rfl) ⟨640682, by rfl⟩ : syracuseStep 854243 = 1281365) B1281365
theorem B854273 : Blo 566810 854273 := bstep (se 2 (by rfl) ⟨320352, by rfl⟩ : syracuseStep 854273 = 640705) B640705
theorem B854291 : Blo 566810 854291 := bstep (se 1 (by rfl) ⟨640718, by rfl⟩ : syracuseStep 854291 = 1281437) B1281437
theorem B854321 : Blo 566810 854321 := bstep (se 2 (by rfl) ⟨320370, by rfl⟩ : syracuseStep 854321 = 640741) B640741
theorem B854339 : Blo 566810 854339 := bstep (se 1 (by rfl) ⟨640754, by rfl⟩ : syracuseStep 854339 = 1281509) B1281509
theorem B2165069 : Blo 566810 2165069 := bstep (se 3 (by rfl) ⟨405950, by rfl⟩ : syracuseStep 2165069 = 811901) B811901
theorem B854369 : Blo 566810 854369 := bstep (se 2 (by rfl) ⟨320388, by rfl⟩ : syracuseStep 854369 = 640777) B640777
theorem B854387 : Blo 566810 854387 := bstep (se 1 (by rfl) ⟨640790, by rfl⟩ : syracuseStep 854387 = 1281581) B1281581
theorem B2886029 : Blo 566810 2886029 := bstep (se 3 (by rfl) ⟨541130, by rfl⟩ : syracuseStep 2886029 = 1082261) B1082261
theorem B854417 : Blo 566810 854417 := bstep (se 2 (by rfl) ⟨320406, by rfl⟩ : syracuseStep 854417 = 640813) B640813
theorem B854435 : Blo 566810 854435 := bstep (se 1 (by rfl) ⟨640826, by rfl⟩ : syracuseStep 854435 = 1281653) B1281653
theorem B854465 : Blo 566810 854465 := bstep (se 2 (by rfl) ⟨320424, by rfl⟩ : syracuseStep 854465 = 640849) B640849
theorem B1280465 : Blo 566810 1280465 := bstep (se 2 (by rfl) ⟨480174, by rfl⟩ : syracuseStep 1280465 = 960349) B960349
theorem B854483 : Blo 566810 854483 := bstep (se 1 (by rfl) ⟨640862, by rfl⟩ : syracuseStep 854483 = 1281725) B1281725
theorem B1214947 : Blo 566810 1214947 := bstep (se 1 (by rfl) ⟨911210, by rfl⟩ : syracuseStep 1214947 = 1822421) B1822421
theorem B1280483 : Blo 566810 1280483 := bstep (se 1 (by rfl) ⟨960362, by rfl⟩ : syracuseStep 1280483 = 1920725) B1920725
theorem B854513 : Blo 566810 854513 := bstep (se 2 (by rfl) ⟨320442, by rfl⟩ : syracuseStep 854513 = 640885) B640885
theorem B854531 : Blo 566810 854531 := bstep (se 1 (by rfl) ⟨640898, by rfl⟩ : syracuseStep 854531 = 1281797) B1281797
theorem B1149457 : Blo 566810 1149457 := bstep (se 2 (by rfl) ⟨431046, by rfl⟩ : syracuseStep 1149457 = 862093) B862093
theorem B854561 : Blo 566810 854561 := bstep (se 2 (by rfl) ⟨320460, by rfl⟩ : syracuseStep 854561 = 640921) B640921
theorem B854579 : Blo 566810 854579 := bstep (se 1 (by rfl) ⟨640934, by rfl⟩ : syracuseStep 854579 = 1281869) B1281869
theorem B854609 : Blo 566810 854609 := bstep (se 2 (by rfl) ⟨320478, by rfl⟩ : syracuseStep 854609 = 640957) B640957
theorem B854627 : Blo 566810 854627 := bstep (se 1 (by rfl) ⟨640970, by rfl⟩ : syracuseStep 854627 = 1281941) B1281941
theorem B1149553 : Blo 566810 1149553 := bstep (se 2 (by rfl) ⟨431082, by rfl⟩ : syracuseStep 1149553 = 862165) B862165
theorem B854657 : Blo 566810 854657 := bstep (se 2 (by rfl) ⟨320496, by rfl⟩ : syracuseStep 854657 = 640993) B640993
theorem B854675 : Blo 566810 854675 := bstep (se 1 (by rfl) ⟨641006, by rfl⟩ : syracuseStep 854675 = 1282013) B1282013
theorem B854705 : Blo 566810 854705 := bstep (se 2 (by rfl) ⟨320514, by rfl⟩ : syracuseStep 854705 = 641029) B641029
theorem B854723 : Blo 566810 854723 := bstep (se 1 (by rfl) ⟨641042, by rfl⟩ : syracuseStep 854723 = 1282085) B1282085
theorem B854753 : Blo 566810 854753 := bstep (se 2 (by rfl) ⟨320532, by rfl⟩ : syracuseStep 854753 = 641065) B641065
theorem B1280753 : Blo 566810 1280753 := bstep (se 2 (by rfl) ⟨480282, by rfl⟩ : syracuseStep 1280753 = 960565) B960565
theorem B854771 : Blo 566810 854771 := bstep (se 1 (by rfl) ⟨641078, by rfl⟩ : syracuseStep 854771 = 1282157) B1282157
theorem B1280771 : Blo 566810 1280771 := bstep (se 1 (by rfl) ⟨960578, by rfl⟩ : syracuseStep 1280771 = 1921157) B1921157
theorem B854801 : Blo 566810 854801 := bstep (se 2 (by rfl) ⟨320550, by rfl⟩ : syracuseStep 854801 = 641101) B641101
theorem B1444625 : Blo 566810 1444625 := bstep (se 2 (by rfl) ⟨541734, by rfl⟩ : syracuseStep 1444625 = 1083469) B1083469
theorem B854819 : Blo 566810 854819 := bstep (se 1 (by rfl) ⟨641114, by rfl⟩ : syracuseStep 854819 = 1282229) B1282229
theorem B854849 : Blo 566810 854849 := bstep (se 2 (by rfl) ⟨320568, by rfl⟩ : syracuseStep 854849 = 641137) B641137
theorem B1444675 : Blo 566810 1444675 := bstep (se 1 (by rfl) ⟨1083506, by rfl⟩ : syracuseStep 1444675 = 2167013) B2167013
theorem B854867 : Blo 566810 854867 := bstep (se 1 (by rfl) ⟨641150, by rfl⟩ : syracuseStep 854867 = 1282301) B1282301
theorem B854897 : Blo 566810 854897 := bstep (se 2 (by rfl) ⟨320586, by rfl⟩ : syracuseStep 854897 = 641173) B641173
theorem B854915 : Blo 566810 854915 := bstep (se 1 (by rfl) ⟨641186, by rfl⟩ : syracuseStep 854915 = 1282373) B1282373
theorem B854945 : Blo 566810 854945 := bstep (se 2 (by rfl) ⟨320604, by rfl⟩ : syracuseStep 854945 = 641209) B641209
theorem B854963 : Blo 566810 854963 := bstep (se 1 (by rfl) ⟨641222, by rfl⟩ : syracuseStep 854963 = 1282445) B1282445
theorem B854993 : Blo 566810 854993 := bstep (se 2 (by rfl) ⟨320622, by rfl⟩ : syracuseStep 854993 = 641245) B641245
theorem B1444817 : Blo 566810 1444817 := bstep (se 2 (by rfl) ⟨541806, by rfl⟩ : syracuseStep 1444817 = 1083613) B1083613
theorem B855011 : Blo 566810 855011 := bstep (se 1 (by rfl) ⟨641258, by rfl⟩ : syracuseStep 855011 = 1282517) B1282517
theorem B855041 : Blo 566810 855041 := bstep (se 2 (by rfl) ⟨320640, by rfl⟩ : syracuseStep 855041 = 641281) B641281
theorem B1281041 : Blo 566810 1281041 := bstep (se 2 (by rfl) ⟨480390, by rfl⟩ : syracuseStep 1281041 = 960781) B960781
theorem B855059 : Blo 566810 855059 := bstep (se 1 (by rfl) ⟨641294, by rfl⟩ : syracuseStep 855059 = 1282589) B1282589
theorem B1281059 : Blo 566810 1281059 := bstep (se 1 (by rfl) ⟨960794, by rfl⟩ : syracuseStep 1281059 = 1921589) B1921589
theorem B855089 : Blo 566810 855089 := bstep (se 2 (by rfl) ⟨320658, by rfl⟩ : syracuseStep 855089 = 641317) B641317
theorem B855107 : Blo 566810 855107 := bstep (se 1 (by rfl) ⟨641330, by rfl⟩ : syracuseStep 855107 = 1282661) B1282661
theorem B855137 : Blo 566810 855137 := bstep (se 2 (by rfl) ⟨320676, by rfl⟩ : syracuseStep 855137 = 641353) B641353
theorem B855155 : Blo 566810 855155 := bstep (se 1 (by rfl) ⟨641366, by rfl⟩ : syracuseStep 855155 = 1282733) B1282733
theorem B855185 : Blo 566810 855185 := bstep (se 2 (by rfl) ⟨320694, by rfl⟩ : syracuseStep 855185 = 641389) B641389
theorem B855203 : Blo 566810 855203 := bstep (se 1 (by rfl) ⟨641402, by rfl⟩ : syracuseStep 855203 = 1282805) B1282805
theorem B1215665 : Blo 566810 1215665 := bstep (se 2 (by rfl) ⟨455874, by rfl⟩ : syracuseStep 1215665 = 911749) B911749
theorem B855233 : Blo 566810 855233 := bstep (se 2 (by rfl) ⟨320712, by rfl⟩ : syracuseStep 855233 = 641425) B641425
theorem B855251 : Blo 566810 855251 := bstep (se 1 (by rfl) ⟨641438, by rfl⟩ : syracuseStep 855251 = 1282877) B1282877
theorem B855281 : Blo 566810 855281 := bstep (se 2 (by rfl) ⟨320730, by rfl⟩ : syracuseStep 855281 = 641461) B641461
theorem B855299 : Blo 566810 855299 := bstep (se 1 (by rfl) ⟨641474, by rfl⟩ : syracuseStep 855299 = 1282949) B1282949
theorem B855329 : Blo 566810 855329 := bstep (se 2 (by rfl) ⟨320748, by rfl⟩ : syracuseStep 855329 = 641497) B641497
theorem B1281329 : Blo 566810 1281329 := bstep (se 2 (by rfl) ⟨480498, by rfl⟩ : syracuseStep 1281329 = 960997) B960997
theorem B855347 : Blo 566810 855347 := bstep (se 1 (by rfl) ⟨641510, by rfl⟩ : syracuseStep 855347 = 1283021) B1283021
theorem B1281347 : Blo 566810 1281347 := bstep (se 1 (by rfl) ⟨961010, by rfl⟩ : syracuseStep 1281347 = 1922021) B1922021
theorem B855377 : Blo 566810 855377 := bstep (se 2 (by rfl) ⟨320766, by rfl⟩ : syracuseStep 855377 = 641533) B641533
theorem B855395 : Blo 566810 855395 := bstep (se 1 (by rfl) ⟨641546, by rfl⟩ : syracuseStep 855395 = 1283093) B1283093
theorem B855425 : Blo 566810 855425 := bstep (se 2 (by rfl) ⟨320784, by rfl⟩ : syracuseStep 855425 = 641569) B641569
theorem B855443 : Blo 566810 855443 := bstep (se 1 (by rfl) ⟨641582, by rfl⟩ : syracuseStep 855443 = 1283165) B1283165
theorem B855473 : Blo 566810 855473 := bstep (se 2 (by rfl) ⟨320802, by rfl⟩ : syracuseStep 855473 = 641605) B641605
theorem B855491 : Blo 566810 855491 := bstep (se 1 (by rfl) ⟨641618, by rfl⟩ : syracuseStep 855491 = 1283237) B1283237
theorem B855521 : Blo 566810 855521 := bstep (se 2 (by rfl) ⟨320820, by rfl⟩ : syracuseStep 855521 = 641641) B641641
theorem B855539 : Blo 566810 855539 := bstep (se 1 (by rfl) ⟨641654, by rfl⟩ : syracuseStep 855539 = 1283309) B1283309
theorem B855569 : Blo 566810 855569 := bstep (se 2 (by rfl) ⟨320838, by rfl⟩ : syracuseStep 855569 = 641677) B641677
theorem B822817 : Blo 566810 822817 := bstep (se 2 (by rfl) ⟨308556, by rfl⟩ : syracuseStep 822817 = 617113) B617113
theorem B855587 : Blo 566810 855587 := bstep (se 1 (by rfl) ⟨641690, by rfl⟩ : syracuseStep 855587 = 1283381) B1283381
theorem B855617 : Blo 566810 855617 := bstep (se 2 (by rfl) ⟨320856, by rfl⟩ : syracuseStep 855617 = 641713) B641713
theorem B1281617 : Blo 566810 1281617 := bstep (se 2 (by rfl) ⟨480606, by rfl⟩ : syracuseStep 1281617 = 961213) B961213
theorem B855635 : Blo 566810 855635 := bstep (se 1 (by rfl) ⟨641726, by rfl⟩ : syracuseStep 855635 = 1283453) B1283453
theorem B1281635 : Blo 566810 1281635 := bstep (se 1 (by rfl) ⟨961226, by rfl⟩ : syracuseStep 1281635 = 1922453) B1922453
theorem B3640945 : Blo 566810 3640945 := bstep (se 2 (by rfl) ⟨1365354, by rfl⟩ : syracuseStep 3640945 = 2730709) B2730709
theorem B855665 : Blo 566810 855665 := bstep (se 2 (by rfl) ⟨320874, by rfl⟩ : syracuseStep 855665 = 641749) B641749
theorem B855683 : Blo 566810 855683 := bstep (se 1 (by rfl) ⟨641762, by rfl⟩ : syracuseStep 855683 = 1283525) B1283525
theorem B855713 : Blo 566810 855713 := bstep (se 2 (by rfl) ⟨320892, by rfl⟩ : syracuseStep 855713 = 641785) B641785
theorem B855731 : Blo 566810 855731 := bstep (se 1 (by rfl) ⟨641798, by rfl⟩ : syracuseStep 855731 = 1283597) B1283597
theorem B855761 : Blo 566810 855761 := bstep (se 2 (by rfl) ⟨320910, by rfl⟩ : syracuseStep 855761 = 641821) B641821
theorem B855779 : Blo 566810 855779 := bstep (se 1 (by rfl) ⟨641834, by rfl⟩ : syracuseStep 855779 = 1283669) B1283669
theorem B855809 : Blo 566810 855809 := bstep (se 2 (by rfl) ⟨320928, by rfl⟩ : syracuseStep 855809 = 641857) B641857
theorem B3247877 : Blo 566810 3247877 := bstep (se 4 (by rfl) ⟨304488, by rfl⟩ : syracuseStep 3247877 = 608977) B608977
theorem B855827 : Blo 566810 855827 := bstep (se 1 (by rfl) ⟨641870, by rfl⟩ : syracuseStep 855827 = 1283741) B1283741
theorem B855857 : Blo 566810 855857 := bstep (se 2 (by rfl) ⟨320946, by rfl⟩ : syracuseStep 855857 = 641893) B641893
theorem B855875 : Blo 566810 855875 := bstep (se 1 (by rfl) ⟨641906, by rfl⟩ : syracuseStep 855875 = 1283813) B1283813
theorem B855905 : Blo 566810 855905 := bstep (se 2 (by rfl) ⟨320964, by rfl⟩ : syracuseStep 855905 = 641929) B641929
theorem B1281905 : Blo 566810 1281905 := bstep (se 2 (by rfl) ⟨480714, by rfl⟩ : syracuseStep 1281905 = 961429) B961429
theorem B855923 : Blo 566810 855923 := bstep (se 1 (by rfl) ⟨641942, by rfl⟩ : syracuseStep 855923 = 1283885) B1283885
theorem B1281923 : Blo 566810 1281923 := bstep (se 1 (by rfl) ⟨961442, by rfl⟩ : syracuseStep 1281923 = 1922885) B1922885
theorem B855953 : Blo 566810 855953 := bstep (se 2 (by rfl) ⟨320982, by rfl⟩ : syracuseStep 855953 = 641965) B641965
theorem B1642403 : Blo 566810 1642403 := bstep (se 1 (by rfl) ⟨1231802, by rfl⟩ : syracuseStep 1642403 = 2463605) B2463605
theorem B855971 : Blo 566810 855971 := bstep (se 1 (by rfl) ⟨641978, by rfl⟩ : syracuseStep 855971 = 1283957) B1283957
theorem B856001 : Blo 566810 856001 := bstep (se 2 (by rfl) ⟨321000, by rfl⟩ : syracuseStep 856001 = 642001) B642001
theorem B1216451 : Blo 566810 1216451 := bstep (se 1 (by rfl) ⟨912338, by rfl⟩ : syracuseStep 1216451 = 1824677) B1824677
theorem B856019 : Blo 566810 856019 := bstep (se 1 (by rfl) ⟨642014, by rfl⟩ : syracuseStep 856019 = 1284029) B1284029
theorem B856049 : Blo 566810 856049 := bstep (se 2 (by rfl) ⟨321018, by rfl⟩ : syracuseStep 856049 = 642037) B642037
theorem B856067 : Blo 566810 856067 := bstep (se 1 (by rfl) ⟨642050, by rfl⟩ : syracuseStep 856067 = 1284101) B1284101
theorem B6230029 : Blo 566810 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B856097 : Blo 566810 856097 := bstep (se 2 (by rfl) ⟨321036, by rfl⟩ : syracuseStep 856097 = 642073) B642073
theorem B856115 : Blo 566810 856115 := bstep (se 1 (by rfl) ⟨642086, by rfl⟩ : syracuseStep 856115 = 1284173) B1284173
theorem B856145 : Blo 566810 856145 := bstep (se 2 (by rfl) ⟨321054, by rfl⟩ : syracuseStep 856145 = 642109) B642109
theorem B856163 : Blo 566810 856163 := bstep (se 1 (by rfl) ⟨642122, by rfl⟩ : syracuseStep 856163 = 1284245) B1284245
theorem B856193 : Blo 566810 856193 := bstep (se 2 (by rfl) ⟨321072, by rfl⟩ : syracuseStep 856193 = 642145) B642145
theorem B1282193 : Blo 566810 1282193 := bstep (se 2 (by rfl) ⟨480822, by rfl⟩ : syracuseStep 1282193 = 961645) B961645
theorem B856211 : Blo 566810 856211 := bstep (se 1 (by rfl) ⟨642158, by rfl⟩ : syracuseStep 856211 = 1284317) B1284317
theorem B1282211 : Blo 566810 1282211 := bstep (se 1 (by rfl) ⟨961658, by rfl⟩ : syracuseStep 1282211 = 1923317) B1923317
theorem B3281093 : Blo 566810 3281093 := bstep (se 4 (by rfl) ⟨307602, by rfl⟩ : syracuseStep 3281093 = 615205) B615205
theorem B3248333 : Blo 566810 3248333 := bstep (se 3 (by rfl) ⟨609062, by rfl⟩ : syracuseStep 3248333 = 1218125) B1218125
theorem B2167181 : Blo 566810 2167181 := bstep (se 3 (by rfl) ⟨406346, by rfl⟩ : syracuseStep 2167181 = 812693) B812693
theorem B2429347 : Blo 566810 2429347 := bstep (se 1 (by rfl) ⟨1822010, by rfl⟩ : syracuseStep 2429347 = 3644021) B3644021
theorem B1282481 : Blo 566810 1282481 := bstep (se 2 (by rfl) ⟨480930, by rfl⟩ : syracuseStep 1282481 = 961861) B961861
theorem B1282499 : Blo 566810 1282499 := bstep (se 1 (by rfl) ⟨961874, by rfl⟩ : syracuseStep 1282499 = 1923749) B1923749
theorem B1315331 : Blo 566810 1315331 := bstep (se 1 (by rfl) ⟨986498, by rfl⟩ : syracuseStep 1315331 = 1972997) B1972997
theorem B10359409 : Blo 566810 10359409 := bstep (se 2 (by rfl) ⟨3884778, by rfl⟩ : syracuseStep 10359409 = 7769557) B7769557
theorem B1282769 : Blo 566810 1282769 := bstep (se 2 (by rfl) ⟨481038, by rfl⟩ : syracuseStep 1282769 = 962077) B962077
theorem B1282787 : Blo 566810 1282787 := bstep (se 1 (by rfl) ⟨962090, by rfl⟩ : syracuseStep 1282787 = 1924181) B1924181
theorem B7279429 : Blo 566810 7279429 := bstep (se 4 (by rfl) ⟨682446, by rfl⟩ : syracuseStep 7279429 = 1364893) B1364893
theorem B1217425 : Blo 566810 1217425 := bstep (se 2 (by rfl) ⟨456534, by rfl⟩ : syracuseStep 1217425 = 913069) B913069
theorem B1283057 : Blo 566810 1283057 := bstep (se 2 (by rfl) ⟨481146, by rfl⟩ : syracuseStep 1283057 = 962293) B962293
theorem B1283075 : Blo 566810 1283075 := bstep (se 1 (by rfl) ⟨962306, by rfl⟩ : syracuseStep 1283075 = 1924613) B1924613
theorem B1217681 : Blo 566810 1217681 := bstep (se 2 (by rfl) ⟨456630, by rfl⟩ : syracuseStep 1217681 = 913261) B913261
theorem B2299043 : Blo 566810 2299043 := bstep (se 1 (by rfl) ⟨1724282, by rfl⟩ : syracuseStep 2299043 = 3448565) B3448565
theorem B2888945 : Blo 566810 2888945 := bstep (se 2 (by rfl) ⟨1083354, by rfl⟩ : syracuseStep 2888945 = 2166709) B2166709
theorem B1283345 : Blo 566810 1283345 := bstep (se 2 (by rfl) ⟨481254, by rfl⟩ : syracuseStep 1283345 = 962509) B962509
theorem B1283363 : Blo 566810 1283363 := bstep (se 1 (by rfl) ⟨962522, by rfl⟩ : syracuseStep 1283363 = 1925045) B1925045
theorem B3282403 : Blo 566810 3282403 := bstep (se 1 (by rfl) ⟨2461802, by rfl⟩ : syracuseStep 3282403 = 4923605) B4923605
theorem B1283633 : Blo 566810 1283633 := bstep (se 2 (by rfl) ⟨481362, by rfl⟩ : syracuseStep 1283633 = 962725) B962725
theorem B1283651 : Blo 566810 1283651 := bstep (se 1 (by rfl) ⟨962738, by rfl⟩ : syracuseStep 1283651 = 1925477) B1925477
theorem B2430577 : Blo 566810 2430577 := bstep (se 2 (by rfl) ⟨911466, by rfl⟩ : syracuseStep 2430577 = 1822933) B1822933
theorem B3282565 : Blo 566810 3282565 := bstep (se 4 (by rfl) ⟨307740, by rfl⟩ : syracuseStep 3282565 = 615481) B615481
theorem B7870193 : Blo 566810 7870193 := bstep (se 2 (by rfl) ⟨2951322, by rfl⟩ : syracuseStep 7870193 = 5902645) B5902645
theorem B1283921 : Blo 566810 1283921 := bstep (se 2 (by rfl) ⟨481470, by rfl⟩ : syracuseStep 1283921 = 962941) B962941
theorem B1283939 : Blo 566810 1283939 := bstep (se 1 (by rfl) ⟨962954, by rfl⟩ : syracuseStep 1283939 = 1925909) B1925909
theorem B1153091 : Blo 566810 1153091 := bstep (se 1 (by rfl) ⟨864818, by rfl⟩ : syracuseStep 1153091 = 1729637) B1729637
theorem B956515 : Blo 566810 956515 := bstep (se 1 (by rfl) ⟨717386, by rfl⟩ : syracuseStep 956515 = 1434773) B1434773
theorem B1284209 : Blo 566810 1284209 := bstep (se 2 (by rfl) ⟨481578, by rfl⟩ : syracuseStep 1284209 = 963157) B963157
theorem B1284227 : Blo 566810 1284227 := bstep (se 1 (by rfl) ⟨963170, by rfl⟩ : syracuseStep 1284227 = 1926341) B1926341
theorem B1022129 : Blo 566810 1022129 := bstep (se 2 (by rfl) ⟨383298, by rfl⟩ : syracuseStep 1022129 = 766597) B766597
theorem B4331717 : Blo 566810 4331717 := bstep (se 4 (by rfl) ⟨406098, by rfl⟩ : syracuseStep 4331717 = 812197) B812197
theorem B956657 : Blo 566810 956657 := bstep (se 2 (by rfl) ⟨358746, by rfl⟩ : syracuseStep 956657 = 717493) B717493
theorem B5478641 : Blo 566810 5478641 := bstep (se 2 (by rfl) ⟨2054490, by rfl⟩ : syracuseStep 5478641 = 4108981) B4108981
theorem B956785 : Blo 566810 956785 := bstep (se 2 (by rfl) ⟨358794, by rfl⟩ : syracuseStep 956785 = 717589) B717589
theorem B2595185 : Blo 566810 2595185 := bstep (se 2 (by rfl) ⟨973194, by rfl⟩ : syracuseStep 2595185 = 1946389) B1946389
theorem B956819 : Blo 566810 956819 := bstep (se 1 (by rfl) ⟨717614, by rfl⟩ : syracuseStep 956819 = 1435229) B1435229
theorem B1218979 : Blo 566810 1218979 := bstep (se 1 (by rfl) ⟨914234, by rfl⟩ : syracuseStep 1218979 = 1828469) B1828469
theorem B956947 : Blo 566810 956947 := bstep (se 1 (by rfl) ⟨717710, by rfl⟩ : syracuseStep 956947 = 1435421) B1435421
theorem B957089 : Blo 566810 957089 := bstep (se 2 (by rfl) ⟨358908, by rfl⟩ : syracuseStep 957089 = 717817) B717817
theorem B957217 : Blo 566810 957217 := bstep (se 2 (by rfl) ⟨358956, by rfl⟩ : syracuseStep 957217 = 717913) B717913
theorem B1645357 : Blo 566810 1645357 := bstep (se 3 (by rfl) ⟨308504, by rfl⟩ : syracuseStep 1645357 = 617009) B617009
theorem B957251 : Blo 566810 957251 := bstep (se 1 (by rfl) ⟨717938, by rfl⟩ : syracuseStep 957251 = 1435877) B1435877
theorem B957379 : Blo 566810 957379 := bstep (se 1 (by rfl) ⟨718034, by rfl⟩ : syracuseStep 957379 = 1436069) B1436069
theorem B957521 : Blo 566810 957521 := bstep (se 2 (by rfl) ⟨359070, by rfl⟩ : syracuseStep 957521 = 718141) B718141
theorem B1973443 : Blo 566810 1973443 := bstep (se 1 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 1973443 = 2960165) B2960165
theorem B957649 : Blo 566810 957649 := bstep (se 2 (by rfl) ⟨359118, by rfl⟩ : syracuseStep 957649 = 718237) B718237
theorem B2301169 : Blo 566810 2301169 := bstep (se 2 (by rfl) ⟨862938, by rfl⟩ : syracuseStep 2301169 = 1725877) B1725877
theorem B957683 : Blo 566810 957683 := bstep (se 1 (by rfl) ⟨718262, by rfl⟩ : syracuseStep 957683 = 1436525) B1436525
theorem B957811 : Blo 566810 957811 := bstep (se 1 (by rfl) ⟨718358, by rfl⟩ : syracuseStep 957811 = 1436717) B1436717
theorem B957953 : Blo 566810 957953 := bstep (se 2 (by rfl) ⟨359232, by rfl⟩ : syracuseStep 957953 = 718465) B718465
theorem B1023491 : Blo 566810 1023491 := bstep (se 1 (by rfl) ⟨767618, by rfl⟩ : syracuseStep 1023491 = 1535237) B1535237
theorem B958081 : Blo 566810 958081 := bstep (se 2 (by rfl) ⟨359280, by rfl⟩ : syracuseStep 958081 = 718561) B718561
theorem B958115 : Blo 566810 958115 := bstep (se 1 (by rfl) ⟨718586, by rfl⟩ : syracuseStep 958115 = 1437173) B1437173
theorem B958243 : Blo 566810 958243 := bstep (se 1 (by rfl) ⟨718682, by rfl⟩ : syracuseStep 958243 = 1437365) B1437365
theorem B6922037 : Blo 566810 6922037 := bstep (se 5 (by rfl) ⟨324470, by rfl⟩ : syracuseStep 6922037 = 648941) B648941
theorem B728899 : Blo 566810 728899 := bstep (se 1 (by rfl) ⟨546674, by rfl⟩ : syracuseStep 728899 = 1093349) B1093349
theorem B958385 : Blo 566810 958385 := bstep (se 2 (by rfl) ⟨359394, by rfl⟩ : syracuseStep 958385 = 718789) B718789
theorem B958513 : Blo 566810 958513 := bstep (se 2 (by rfl) ⟨359442, by rfl⟩ : syracuseStep 958513 = 718885) B718885
theorem B958547 : Blo 566810 958547 := bstep (se 1 (by rfl) ⟨718910, by rfl⟩ : syracuseStep 958547 = 1437821) B1437821
theorem B958675 : Blo 566810 958675 := bstep (se 1 (by rfl) ⟨719006, by rfl⟩ : syracuseStep 958675 = 1438013) B1438013
theorem B1614097 : Blo 566810 1614097 := bstep (se 2 (by rfl) ⟨605286, by rfl⟩ : syracuseStep 1614097 = 1210573) B1210573
theorem B958817 : Blo 566810 958817 := bstep (se 2 (by rfl) ⟨359556, by rfl⟩ : syracuseStep 958817 = 719113) B719113
theorem B958945 : Blo 566810 958945 := bstep (se 2 (by rfl) ⟨359604, by rfl⟩ : syracuseStep 958945 = 719209) B719209
theorem B958979 : Blo 566810 958979 := bstep (se 1 (by rfl) ⟨719234, by rfl⟩ : syracuseStep 958979 = 1438469) B1438469
theorem B959107 : Blo 566810 959107 := bstep (se 1 (by rfl) ⟨719330, by rfl⟩ : syracuseStep 959107 = 1438661) B1438661
theorem B5481101 : Blo 566810 5481101 := bstep (se 3 (by rfl) ⟨1027706, by rfl⟩ : syracuseStep 5481101 = 2055413) B2055413
theorem B959249 : Blo 566810 959249 := bstep (se 2 (by rfl) ⟨359718, by rfl⟩ : syracuseStep 959249 = 719437) B719437
theorem B959377 : Blo 566810 959377 := bstep (se 2 (by rfl) ⟨359766, by rfl⟩ : syracuseStep 959377 = 719533) B719533
theorem B959411 : Blo 566810 959411 := bstep (se 1 (by rfl) ⟨719558, by rfl⟩ : syracuseStep 959411 = 1439117) B1439117
theorem B1647587 : Blo 566810 1647587 := bstep (se 1 (by rfl) ⟨1235690, by rfl⟩ : syracuseStep 1647587 = 2471381) B2471381
theorem B959539 : Blo 566810 959539 := bstep (se 1 (by rfl) ⟨719654, by rfl⟩ : syracuseStep 959539 = 1439309) B1439309
theorem B3941453 : Blo 566810 3941453 := bstep (se 3 (by rfl) ⟨739022, by rfl⟩ : syracuseStep 3941453 = 1478045) B1478045
theorem B959681 : Blo 566810 959681 := bstep (se 2 (by rfl) ⟨359880, by rfl⟩ : syracuseStep 959681 = 719761) B719761
theorem B2303245 : Blo 566810 2303245 := bstep (se 3 (by rfl) ⟨431858, by rfl⟩ : syracuseStep 2303245 = 863717) B863717
theorem B1090865 : Blo 566810 1090865 := bstep (se 2 (by rfl) ⟨409074, by rfl⟩ : syracuseStep 1090865 = 818149) B818149
theorem B959809 : Blo 566810 959809 := bstep (se 2 (by rfl) ⟨359928, by rfl⟩ : syracuseStep 959809 = 719857) B719857
theorem B959843 : Blo 566810 959843 := bstep (se 1 (by rfl) ⟨719882, by rfl⟩ : syracuseStep 959843 = 1439765) B1439765
theorem B12166541 : Blo 566810 12166541 := bstep (se 3 (by rfl) ⟨2281226, by rfl⟩ : syracuseStep 12166541 = 4562453) B4562453
theorem B1090993 : Blo 566810 1090993 := bstep (se 2 (by rfl) ⟨409122, by rfl⟩ : syracuseStep 1090993 = 818245) B818245
theorem B959971 : Blo 566810 959971 := bstep (se 1 (by rfl) ⟨719978, by rfl⟩ : syracuseStep 959971 = 1439957) B1439957
theorem B1615373 : Blo 566810 1615373 := bstep (se 3 (by rfl) ⟨302882, by rfl⟩ : syracuseStep 1615373 = 605765) B605765
theorem B566819 : Blo 566810 566819 := bstep (se 1 (by rfl) ⟨425114, by rfl⟩ : syracuseStep 566819 = 850229) B850229
theorem B566835 : Blo 566810 566835 := bstep (se 1 (by rfl) ⟨425126, by rfl⟩ : syracuseStep 566835 = 850253) B850253
theorem B566851 : Blo 566810 566851 := bstep (se 1 (by rfl) ⟨425138, by rfl⟩ : syracuseStep 566851 = 850277) B850277
theorem B566867 : Blo 566810 566867 := bstep (se 1 (by rfl) ⟨425150, by rfl⟩ : syracuseStep 566867 = 850301) B850301
theorem B566883 : Blo 566810 566883 := bstep (se 1 (by rfl) ⟨425162, by rfl⟩ : syracuseStep 566883 = 850325) B850325
theorem B960113 : Blo 566810 960113 := bstep (se 2 (by rfl) ⟨360042, by rfl⟩ : syracuseStep 960113 = 720085) B720085
theorem B566899 : Blo 566810 566899 := bstep (se 1 (by rfl) ⟨425174, by rfl⟩ : syracuseStep 566899 = 850349) B850349
theorem B566915 : Blo 566810 566915 := bstep (se 1 (by rfl) ⟨425186, by rfl⟩ : syracuseStep 566915 = 850373) B850373
theorem B566931 : Blo 566810 566931 := bstep (se 1 (by rfl) ⟨425198, by rfl⟩ : syracuseStep 566931 = 850397) B850397
theorem B566947 : Blo 566810 566947 := bstep (se 1 (by rfl) ⟨425210, by rfl⟩ : syracuseStep 566947 = 850421) B850421
theorem B1156771 : Blo 566810 1156771 := bstep (se 1 (by rfl) ⟨867578, by rfl⟩ : syracuseStep 1156771 = 1735157) B1735157
theorem B566963 : Blo 566810 566963 := bstep (se 1 (by rfl) ⟨425222, by rfl⟩ : syracuseStep 566963 = 850445) B850445
theorem B566979 : Blo 566810 566979 := bstep (se 1 (by rfl) ⟨425234, by rfl⟩ : syracuseStep 566979 = 850469) B850469
theorem B1615555 : Blo 566810 1615555 := bstep (se 1 (by rfl) ⟨1211666, by rfl⟩ : syracuseStep 1615555 = 2423333) B2423333
theorem B566995 : Blo 566810 566995 := bstep (se 1 (by rfl) ⟨425246, by rfl⟩ : syracuseStep 566995 = 850493) B850493
theorem B567011 : Blo 566810 567011 := bstep (se 1 (by rfl) ⟨425258, by rfl⟩ : syracuseStep 567011 = 850517) B850517
theorem B2074339 : Blo 566810 2074339 := bstep (se 1 (by rfl) ⟨1555754, by rfl⟩ : syracuseStep 2074339 = 3111509) B3111509
theorem B1615601 : Blo 566810 1615601 := bstep (se 2 (by rfl) ⟨605850, by rfl⟩ : syracuseStep 1615601 = 1211701) B1211701
theorem B960241 : Blo 566810 960241 := bstep (se 2 (by rfl) ⟨360090, by rfl⟩ : syracuseStep 960241 = 720181) B720181
theorem B567027 : Blo 566810 567027 := bstep (se 1 (by rfl) ⟨425270, by rfl⟩ : syracuseStep 567027 = 850541) B850541
theorem B567043 : Blo 566810 567043 := bstep (se 1 (by rfl) ⟨425282, by rfl⟩ : syracuseStep 567043 = 850565) B850565
theorem B567059 : Blo 566810 567059 := bstep (se 1 (by rfl) ⟨425294, by rfl⟩ : syracuseStep 567059 = 850589) B850589
theorem B960275 : Blo 566810 960275 := bstep (se 1 (by rfl) ⟨720206, by rfl⟩ : syracuseStep 960275 = 1440413) B1440413
theorem B567075 : Blo 566810 567075 := bstep (se 1 (by rfl) ⟨425306, by rfl⟩ : syracuseStep 567075 = 850613) B850613
theorem B567091 : Blo 566810 567091 := bstep (se 1 (by rfl) ⟨425318, by rfl⟩ : syracuseStep 567091 = 850637) B850637
theorem B567107 : Blo 566810 567107 := bstep (se 1 (by rfl) ⟨425330, by rfl⟩ : syracuseStep 567107 = 850661) B850661
theorem B567123 : Blo 566810 567123 := bstep (se 1 (by rfl) ⟨425342, by rfl⟩ : syracuseStep 567123 = 850685) B850685
theorem B567139 : Blo 566810 567139 := bstep (se 1 (by rfl) ⟨425354, by rfl⟩ : syracuseStep 567139 = 850709) B850709
theorem B567155 : Blo 566810 567155 := bstep (se 1 (by rfl) ⟨425366, by rfl⟩ : syracuseStep 567155 = 850733) B850733
theorem B567171 : Blo 566810 567171 := bstep (se 1 (by rfl) ⟨425378, by rfl⟩ : syracuseStep 567171 = 850757) B850757
theorem B567187 : Blo 566810 567187 := bstep (se 1 (by rfl) ⟨425390, by rfl⟩ : syracuseStep 567187 = 850781) B850781
theorem B960403 : Blo 566810 960403 := bstep (se 1 (by rfl) ⟨720302, by rfl⟩ : syracuseStep 960403 = 1440605) B1440605
theorem B567203 : Blo 566810 567203 := bstep (se 1 (by rfl) ⟨425402, by rfl⟩ : syracuseStep 567203 = 850805) B850805
theorem B1943473 : Blo 566810 1943473 := bstep (se 2 (by rfl) ⟨728802, by rfl⟩ : syracuseStep 1943473 = 1457605) B1457605
theorem B567219 : Blo 566810 567219 := bstep (se 1 (by rfl) ⟨425414, by rfl⟩ : syracuseStep 567219 = 850829) B850829
theorem B567235 : Blo 566810 567235 := bstep (se 1 (by rfl) ⟨425426, by rfl⟩ : syracuseStep 567235 = 850853) B850853
theorem B2435021 : Blo 566810 2435021 := bstep (se 3 (by rfl) ⟨456566, by rfl⟩ : syracuseStep 2435021 = 913133) B913133
theorem B567251 : Blo 566810 567251 := bstep (se 1 (by rfl) ⟨425438, by rfl⟩ : syracuseStep 567251 = 850877) B850877
theorem B567267 : Blo 566810 567267 := bstep (se 1 (by rfl) ⟨425450, by rfl⟩ : syracuseStep 567267 = 850901) B850901
theorem B567283 : Blo 566810 567283 := bstep (se 1 (by rfl) ⟨425462, by rfl⟩ : syracuseStep 567283 = 850925) B850925
theorem B567299 : Blo 566810 567299 := bstep (se 1 (by rfl) ⟨425474, by rfl⟩ : syracuseStep 567299 = 850949) B850949
theorem B567315 : Blo 566810 567315 := bstep (se 1 (by rfl) ⟨425486, by rfl⟩ : syracuseStep 567315 = 850973) B850973
theorem B960545 : Blo 566810 960545 := bstep (se 2 (by rfl) ⟨360204, by rfl⟩ : syracuseStep 960545 = 720409) B720409
theorem B567331 : Blo 566810 567331 := bstep (se 1 (by rfl) ⟨425498, by rfl⟩ : syracuseStep 567331 = 850997) B850997
theorem B567347 : Blo 566810 567347 := bstep (se 1 (by rfl) ⟨425510, by rfl⟩ : syracuseStep 567347 = 851021) B851021
theorem B567363 : Blo 566810 567363 := bstep (se 1 (by rfl) ⟨425522, by rfl⟩ : syracuseStep 567363 = 851045) B851045
theorem B567379 : Blo 566810 567379 := bstep (se 1 (by rfl) ⟨425534, by rfl⟩ : syracuseStep 567379 = 851069) B851069
theorem B567395 : Blo 566810 567395 := bstep (se 1 (by rfl) ⟨425546, by rfl⟩ : syracuseStep 567395 = 851093) B851093
theorem B567411 : Blo 566810 567411 := bstep (se 1 (by rfl) ⟨425558, by rfl⟩ : syracuseStep 567411 = 851117) B851117
theorem B567427 : Blo 566810 567427 := bstep (se 1 (by rfl) ⟨425570, by rfl⟩ : syracuseStep 567427 = 851141) B851141
theorem B567443 : Blo 566810 567443 := bstep (se 1 (by rfl) ⟨425582, by rfl⟩ : syracuseStep 567443 = 851165) B851165
theorem B960673 : Blo 566810 960673 := bstep (se 2 (by rfl) ⟨360252, by rfl⟩ : syracuseStep 960673 = 720505) B720505
theorem B567459 : Blo 566810 567459 := bstep (se 1 (by rfl) ⟨425594, by rfl⟩ : syracuseStep 567459 = 851189) B851189
theorem B567475 : Blo 566810 567475 := bstep (se 1 (by rfl) ⟨425606, by rfl⟩ : syracuseStep 567475 = 851213) B851213
theorem B567491 : Blo 566810 567491 := bstep (se 1 (by rfl) ⟨425618, by rfl⟩ : syracuseStep 567491 = 851237) B851237
theorem B960707 : Blo 566810 960707 := bstep (se 1 (by rfl) ⟨720530, by rfl⟩ : syracuseStep 960707 = 1441061) B1441061
theorem B567507 : Blo 566810 567507 := bstep (se 1 (by rfl) ⟨425630, by rfl⟩ : syracuseStep 567507 = 851261) B851261
theorem B567523 : Blo 566810 567523 := bstep (se 1 (by rfl) ⟨425642, by rfl⟩ : syracuseStep 567523 = 851285) B851285
theorem B567539 : Blo 566810 567539 := bstep (se 1 (by rfl) ⟨425654, by rfl⟩ : syracuseStep 567539 = 851309) B851309
theorem B567555 : Blo 566810 567555 := bstep (se 1 (by rfl) ⟨425666, by rfl⟩ : syracuseStep 567555 = 851333) B851333
theorem B567571 : Blo 566810 567571 := bstep (se 1 (by rfl) ⟨425678, by rfl⟩ : syracuseStep 567571 = 851357) B851357
theorem B567587 : Blo 566810 567587 := bstep (se 1 (by rfl) ⟨425690, by rfl⟩ : syracuseStep 567587 = 851381) B851381
theorem B1026353 : Blo 566810 1026353 := bstep (se 2 (by rfl) ⟨384882, by rfl⟩ : syracuseStep 1026353 = 769765) B769765
theorem B567603 : Blo 566810 567603 := bstep (se 1 (by rfl) ⟨425702, by rfl⟩ : syracuseStep 567603 = 851405) B851405
theorem B567619 : Blo 566810 567619 := bstep (se 1 (by rfl) ⟨425714, by rfl⟩ : syracuseStep 567619 = 851429) B851429
theorem B960835 : Blo 566810 960835 := bstep (se 1 (by rfl) ⟨720626, by rfl⟩ : syracuseStep 960835 = 1441253) B1441253
theorem B567635 : Blo 566810 567635 := bstep (se 1 (by rfl) ⟨425726, by rfl⟩ : syracuseStep 567635 = 851453) B851453
theorem B567651 : Blo 566810 567651 := bstep (se 1 (by rfl) ⟨425738, by rfl⟩ : syracuseStep 567651 = 851477) B851477
theorem B567667 : Blo 566810 567667 := bstep (se 1 (by rfl) ⟨425750, by rfl⟩ : syracuseStep 567667 = 851501) B851501
theorem B567683 : Blo 566810 567683 := bstep (se 1 (by rfl) ⟨425762, by rfl⟩ : syracuseStep 567683 = 851525) B851525
theorem B567699 : Blo 566810 567699 := bstep (se 1 (by rfl) ⟨425774, by rfl⟩ : syracuseStep 567699 = 851549) B851549
theorem B567715 : Blo 566810 567715 := bstep (se 1 (by rfl) ⟨425786, by rfl⟩ : syracuseStep 567715 = 851573) B851573
theorem B567731 : Blo 566810 567731 := bstep (se 1 (by rfl) ⟨425798, by rfl⟩ : syracuseStep 567731 = 851597) B851597
theorem B567747 : Blo 566810 567747 := bstep (se 1 (by rfl) ⟨425810, by rfl⟩ : syracuseStep 567747 = 851621) B851621
theorem B960977 : Blo 566810 960977 := bstep (se 2 (by rfl) ⟨360366, by rfl⟩ : syracuseStep 960977 = 720733) B720733
theorem B567763 : Blo 566810 567763 := bstep (se 1 (by rfl) ⟨425822, by rfl⟩ : syracuseStep 567763 = 851645) B851645
theorem B567779 : Blo 566810 567779 := bstep (se 1 (by rfl) ⟨425834, by rfl⟩ : syracuseStep 567779 = 851669) B851669
theorem B567795 : Blo 566810 567795 := bstep (se 1 (by rfl) ⟨425846, by rfl⟩ : syracuseStep 567795 = 851693) B851693
theorem B567811 : Blo 566810 567811 := bstep (se 1 (by rfl) ⟨425858, by rfl⟩ : syracuseStep 567811 = 851717) B851717
theorem B567827 : Blo 566810 567827 := bstep (se 1 (by rfl) ⟨425870, by rfl⟩ : syracuseStep 567827 = 851741) B851741
theorem B567843 : Blo 566810 567843 := bstep (se 1 (by rfl) ⟨425882, by rfl⟩ : syracuseStep 567843 = 851765) B851765
theorem B567859 : Blo 566810 567859 := bstep (se 1 (by rfl) ⟨425894, by rfl⟩ : syracuseStep 567859 = 851789) B851789
theorem B567875 : Blo 566810 567875 := bstep (se 1 (by rfl) ⟨425906, by rfl⟩ : syracuseStep 567875 = 851813) B851813
theorem B961105 : Blo 566810 961105 := bstep (se 2 (by rfl) ⟨360414, by rfl⟩ : syracuseStep 961105 = 720829) B720829
theorem B567891 : Blo 566810 567891 := bstep (se 1 (by rfl) ⟨425918, by rfl⟩ : syracuseStep 567891 = 851837) B851837
theorem B567907 : Blo 566810 567907 := bstep (se 1 (by rfl) ⟨425930, by rfl⟩ : syracuseStep 567907 = 851861) B851861
theorem B567923 : Blo 566810 567923 := bstep (se 1 (by rfl) ⟨425942, by rfl⟩ : syracuseStep 567923 = 851885) B851885
theorem B961139 : Blo 566810 961139 := bstep (se 1 (by rfl) ⟨720854, by rfl⟩ : syracuseStep 961139 = 1441709) B1441709
theorem B567939 : Blo 566810 567939 := bstep (se 1 (by rfl) ⟨425954, by rfl⟩ : syracuseStep 567939 = 851909) B851909
theorem B567955 : Blo 566810 567955 := bstep (se 1 (by rfl) ⟨425966, by rfl⟩ : syracuseStep 567955 = 851933) B851933
theorem B567971 : Blo 566810 567971 := bstep (se 1 (by rfl) ⟨425978, by rfl⟩ : syracuseStep 567971 = 851957) B851957
theorem B567987 : Blo 566810 567987 := bstep (se 1 (by rfl) ⟨425990, by rfl⟩ : syracuseStep 567987 = 851981) B851981
theorem B6466229 : Blo 566810 6466229 := bstep (se 5 (by rfl) ⟨303104, by rfl⟩ : syracuseStep 6466229 = 606209) B606209
theorem B568003 : Blo 566810 568003 := bstep (se 1 (by rfl) ⟨426002, by rfl⟩ : syracuseStep 568003 = 852005) B852005
theorem B568019 : Blo 566810 568019 := bstep (se 1 (by rfl) ⟨426014, by rfl⟩ : syracuseStep 568019 = 852029) B852029
theorem B568035 : Blo 566810 568035 := bstep (se 1 (by rfl) ⟨426026, by rfl⟩ : syracuseStep 568035 = 852053) B852053
theorem B568051 : Blo 566810 568051 := bstep (se 1 (by rfl) ⟨426038, by rfl⟩ : syracuseStep 568051 = 852077) B852077
theorem B961267 : Blo 566810 961267 := bstep (se 1 (by rfl) ⟨720950, by rfl⟩ : syracuseStep 961267 = 1441901) B1441901
theorem B568067 : Blo 566810 568067 := bstep (se 1 (by rfl) ⟨426050, by rfl⟩ : syracuseStep 568067 = 852101) B852101
theorem B568083 : Blo 566810 568083 := bstep (se 1 (by rfl) ⟨426062, by rfl⟩ : syracuseStep 568083 = 852125) B852125
theorem B568099 : Blo 566810 568099 := bstep (se 1 (by rfl) ⟨426074, by rfl⟩ : syracuseStep 568099 = 852149) B852149
theorem B568115 : Blo 566810 568115 := bstep (se 1 (by rfl) ⟨426086, by rfl⟩ : syracuseStep 568115 = 852173) B852173
theorem B568131 : Blo 566810 568131 := bstep (se 1 (by rfl) ⟨426098, by rfl⟩ : syracuseStep 568131 = 852197) B852197
theorem B568147 : Blo 566810 568147 := bstep (se 1 (by rfl) ⟨426110, by rfl⟩ : syracuseStep 568147 = 852221) B852221
theorem B568163 : Blo 566810 568163 := bstep (se 1 (by rfl) ⟨426122, by rfl⟩ : syracuseStep 568163 = 852245) B852245
theorem B568179 : Blo 566810 568179 := bstep (se 1 (by rfl) ⟨426134, by rfl⟩ : syracuseStep 568179 = 852269) B852269
theorem B961409 : Blo 566810 961409 := bstep (se 2 (by rfl) ⟨360528, by rfl⟩ : syracuseStep 961409 = 721057) B721057
theorem B568195 : Blo 566810 568195 := bstep (se 1 (by rfl) ⟨426146, by rfl⟩ : syracuseStep 568195 = 852293) B852293
theorem B568211 : Blo 566810 568211 := bstep (se 1 (by rfl) ⟨426158, by rfl⟩ : syracuseStep 568211 = 852317) B852317
theorem B568227 : Blo 566810 568227 := bstep (se 1 (by rfl) ⟨426170, by rfl⟩ : syracuseStep 568227 = 852341) B852341
theorem B2304931 : Blo 566810 2304931 := bstep (se 1 (by rfl) ⟨1728698, by rfl⟩ : syracuseStep 2304931 = 3457397) B3457397
theorem B568243 : Blo 566810 568243 := bstep (se 1 (by rfl) ⟨426182, by rfl⟩ : syracuseStep 568243 = 852365) B852365
theorem B568259 : Blo 566810 568259 := bstep (se 1 (by rfl) ⟨426194, by rfl⟩ : syracuseStep 568259 = 852389) B852389
theorem B568275 : Blo 566810 568275 := bstep (se 1 (by rfl) ⟨426206, by rfl⟩ : syracuseStep 568275 = 852413) B852413
theorem B568291 : Blo 566810 568291 := bstep (se 1 (by rfl) ⟨426218, by rfl⟩ : syracuseStep 568291 = 852437) B852437
theorem B568307 : Blo 566810 568307 := bstep (se 1 (by rfl) ⟨426230, by rfl⟩ : syracuseStep 568307 = 852461) B852461
theorem B961537 : Blo 566810 961537 := bstep (se 2 (by rfl) ⟨360576, by rfl⟩ : syracuseStep 961537 = 721153) B721153
theorem B568323 : Blo 566810 568323 := bstep (se 1 (by rfl) ⟨426242, by rfl⟩ : syracuseStep 568323 = 852485) B852485
theorem B568339 : Blo 566810 568339 := bstep (se 1 (by rfl) ⟨426254, by rfl⟩ : syracuseStep 568339 = 852509) B852509
theorem B568355 : Blo 566810 568355 := bstep (se 1 (by rfl) ⟨426266, by rfl⟩ : syracuseStep 568355 = 852533) B852533
theorem B961571 : Blo 566810 961571 := bstep (se 1 (by rfl) ⟨721178, by rfl⟩ : syracuseStep 961571 = 1442357) B1442357
theorem B568371 : Blo 566810 568371 := bstep (se 1 (by rfl) ⟨426278, by rfl⟩ : syracuseStep 568371 = 852557) B852557
theorem B568387 : Blo 566810 568387 := bstep (se 1 (by rfl) ⟨426290, by rfl⟩ : syracuseStep 568387 = 852581) B852581
theorem B568403 : Blo 566810 568403 := bstep (se 1 (by rfl) ⟨426302, by rfl⟩ : syracuseStep 568403 = 852605) B852605
theorem B568419 : Blo 566810 568419 := bstep (se 1 (by rfl) ⟨426314, by rfl⟩ : syracuseStep 568419 = 852629) B852629
theorem B568435 : Blo 566810 568435 := bstep (se 1 (by rfl) ⟨426326, by rfl⟩ : syracuseStep 568435 = 852653) B852653
theorem B568451 : Blo 566810 568451 := bstep (se 1 (by rfl) ⟨426338, by rfl⟩ : syracuseStep 568451 = 852677) B852677
theorem B568467 : Blo 566810 568467 := bstep (se 1 (by rfl) ⟨426350, by rfl⟩ : syracuseStep 568467 = 852701) B852701
theorem B1617059 : Blo 566810 1617059 := bstep (se 1 (by rfl) ⟨1212794, by rfl⟩ : syracuseStep 1617059 = 2425589) B2425589
theorem B2731171 : Blo 566810 2731171 := bstep (se 1 (by rfl) ⟨2048378, by rfl⟩ : syracuseStep 2731171 = 4096757) B4096757
theorem B568483 : Blo 566810 568483 := bstep (se 1 (by rfl) ⟨426362, by rfl⟩ : syracuseStep 568483 = 852725) B852725
theorem B961699 : Blo 566810 961699 := bstep (se 1 (by rfl) ⟨721274, by rfl⟩ : syracuseStep 961699 = 1442549) B1442549
theorem B568499 : Blo 566810 568499 := bstep (se 1 (by rfl) ⟨426374, by rfl⟩ : syracuseStep 568499 = 852749) B852749
theorem B568515 : Blo 566810 568515 := bstep (se 1 (by rfl) ⟨426386, by rfl⟩ : syracuseStep 568515 = 852773) B852773
theorem B568531 : Blo 566810 568531 := bstep (se 1 (by rfl) ⟨426398, by rfl⟩ : syracuseStep 568531 = 852797) B852797
theorem B568547 : Blo 566810 568547 := bstep (se 1 (by rfl) ⟨426410, by rfl⟩ : syracuseStep 568547 = 852821) B852821
theorem B568563 : Blo 566810 568563 := bstep (se 1 (by rfl) ⟨426422, by rfl⟩ : syracuseStep 568563 = 852845) B852845
theorem B568579 : Blo 566810 568579 := bstep (se 1 (by rfl) ⟨426434, by rfl⟩ : syracuseStep 568579 = 852869) B852869
theorem B3452165 : Blo 566810 3452165 := bstep (se 4 (by rfl) ⟨323640, by rfl⟩ : syracuseStep 3452165 = 647281) B647281
theorem B568595 : Blo 566810 568595 := bstep (se 1 (by rfl) ⟨426446, by rfl⟩ : syracuseStep 568595 = 852893) B852893
theorem B568611 : Blo 566810 568611 := bstep (se 1 (by rfl) ⟨426458, by rfl⟩ : syracuseStep 568611 = 852917) B852917
theorem B961841 : Blo 566810 961841 := bstep (se 2 (by rfl) ⟨360690, by rfl⟩ : syracuseStep 961841 = 721381) B721381
theorem B568627 : Blo 566810 568627 := bstep (se 1 (by rfl) ⟨426470, by rfl⟩ : syracuseStep 568627 = 852941) B852941
theorem B568643 : Blo 566810 568643 := bstep (se 1 (by rfl) ⟨426482, by rfl⟩ : syracuseStep 568643 = 852965) B852965
theorem B568659 : Blo 566810 568659 := bstep (se 1 (by rfl) ⟨426494, by rfl⟩ : syracuseStep 568659 = 852989) B852989
theorem B568675 : Blo 566810 568675 := bstep (se 1 (by rfl) ⟨426506, by rfl⟩ : syracuseStep 568675 = 853013) B853013
theorem B568691 : Blo 566810 568691 := bstep (se 1 (by rfl) ⟨426518, by rfl⟩ : syracuseStep 568691 = 853037) B853037
theorem B568707 : Blo 566810 568707 := bstep (se 1 (by rfl) ⟨426530, by rfl⟩ : syracuseStep 568707 = 853061) B853061
theorem B568723 : Blo 566810 568723 := bstep (se 1 (by rfl) ⟨426542, by rfl⟩ : syracuseStep 568723 = 853085) B853085
theorem B568739 : Blo 566810 568739 := bstep (se 1 (by rfl) ⟨426554, by rfl⟩ : syracuseStep 568739 = 853109) B853109
theorem B961969 : Blo 566810 961969 := bstep (se 2 (by rfl) ⟨360738, by rfl⟩ : syracuseStep 961969 = 721477) B721477
theorem B568755 : Blo 566810 568755 := bstep (se 1 (by rfl) ⟨426566, by rfl⟩ : syracuseStep 568755 = 853133) B853133
theorem B568771 : Blo 566810 568771 := bstep (se 1 (by rfl) ⟨426578, by rfl⟩ : syracuseStep 568771 = 853157) B853157
theorem B568787 : Blo 566810 568787 := bstep (se 1 (by rfl) ⟨426590, by rfl⟩ : syracuseStep 568787 = 853181) B853181
theorem B962003 : Blo 566810 962003 := bstep (se 1 (by rfl) ⟨721502, by rfl⟩ : syracuseStep 962003 = 1443005) B1443005
theorem B568803 : Blo 566810 568803 := bstep (se 1 (by rfl) ⟨426602, by rfl⟩ : syracuseStep 568803 = 853205) B853205
theorem B3648995 : Blo 566810 3648995 := bstep (se 1 (by rfl) ⟨2736746, by rfl⟩ : syracuseStep 3648995 = 5473493) B5473493
theorem B568819 : Blo 566810 568819 := bstep (se 1 (by rfl) ⟨426614, by rfl⟩ : syracuseStep 568819 = 853229) B853229
theorem B568835 : Blo 566810 568835 := bstep (se 1 (by rfl) ⟨426626, by rfl⟩ : syracuseStep 568835 = 853253) B853253
theorem B568851 : Blo 566810 568851 := bstep (se 1 (by rfl) ⟨426638, by rfl⟩ : syracuseStep 568851 = 853277) B853277
theorem B568867 : Blo 566810 568867 := bstep (se 1 (by rfl) ⟨426650, by rfl⟩ : syracuseStep 568867 = 853301) B853301
theorem B568883 : Blo 566810 568883 := bstep (se 1 (by rfl) ⟨426662, by rfl⟩ : syracuseStep 568883 = 853325) B853325
theorem B15773237 : Blo 566810 15773237 := bstep (se 5 (by rfl) ⟨739370, by rfl⟩ : syracuseStep 15773237 = 1478741) B1478741
theorem B568899 : Blo 566810 568899 := bstep (se 1 (by rfl) ⟨426674, by rfl⟩ : syracuseStep 568899 = 853349) B853349
theorem B568915 : Blo 566810 568915 := bstep (se 1 (by rfl) ⟨426686, by rfl⟩ : syracuseStep 568915 = 853373) B853373
theorem B962131 : Blo 566810 962131 := bstep (se 1 (by rfl) ⟨721598, by rfl⟩ : syracuseStep 962131 = 1443197) B1443197
theorem B568931 : Blo 566810 568931 := bstep (se 1 (by rfl) ⟨426698, by rfl⟩ : syracuseStep 568931 = 853397) B853397
theorem B568947 : Blo 566810 568947 := bstep (se 1 (by rfl) ⟨426710, by rfl⟩ : syracuseStep 568947 = 853421) B853421
theorem B568963 : Blo 566810 568963 := bstep (se 1 (by rfl) ⟨426722, by rfl⟩ : syracuseStep 568963 = 853445) B853445
theorem B568979 : Blo 566810 568979 := bstep (se 1 (by rfl) ⟨426734, by rfl⟩ : syracuseStep 568979 = 853469) B853469
theorem B568995 : Blo 566810 568995 := bstep (se 1 (by rfl) ⟨426746, by rfl⟩ : syracuseStep 568995 = 853493) B853493
theorem B569011 : Blo 566810 569011 := bstep (se 1 (by rfl) ⟨426758, by rfl⟩ : syracuseStep 569011 = 853517) B853517
theorem B569027 : Blo 566810 569027 := bstep (se 1 (by rfl) ⟨426770, by rfl⟩ : syracuseStep 569027 = 853541) B853541
theorem B569043 : Blo 566810 569043 := bstep (se 1 (by rfl) ⟨426782, by rfl⟩ : syracuseStep 569043 = 853565) B853565
theorem B962273 : Blo 566810 962273 := bstep (se 2 (by rfl) ⟨360852, by rfl⟩ : syracuseStep 962273 = 721705) B721705
theorem B569059 : Blo 566810 569059 := bstep (se 1 (by rfl) ⟨426794, by rfl⟩ : syracuseStep 569059 = 853589) B853589
theorem B569075 : Blo 566810 569075 := bstep (se 1 (by rfl) ⟨426806, by rfl⟩ : syracuseStep 569075 = 853613) B853613
theorem B569091 : Blo 566810 569091 := bstep (se 1 (by rfl) ⟨426818, by rfl⟩ : syracuseStep 569091 = 853637) B853637
theorem B569107 : Blo 566810 569107 := bstep (se 1 (by rfl) ⟨426830, by rfl⟩ : syracuseStep 569107 = 853661) B853661
theorem B569123 : Blo 566810 569123 := bstep (se 1 (by rfl) ⟨426842, by rfl⟩ : syracuseStep 569123 = 853685) B853685
theorem B3878705 : Blo 566810 3878705 := bstep (se 2 (by rfl) ⟨1454514, by rfl⟩ : syracuseStep 3878705 = 2909029) B2909029
theorem B569139 : Blo 566810 569139 := bstep (se 1 (by rfl) ⟨426854, by rfl⟩ : syracuseStep 569139 = 853709) B853709
theorem B569155 : Blo 566810 569155 := bstep (se 1 (by rfl) ⟨426866, by rfl⟩ : syracuseStep 569155 = 853733) B853733
theorem B569171 : Blo 566810 569171 := bstep (se 1 (by rfl) ⟨426878, by rfl⟩ : syracuseStep 569171 = 853757) B853757
theorem B962401 : Blo 566810 962401 := bstep (se 2 (by rfl) ⟨360900, by rfl⟩ : syracuseStep 962401 = 721801) B721801
theorem B569187 : Blo 566810 569187 := bstep (se 1 (by rfl) ⟨426890, by rfl⟩ : syracuseStep 569187 = 853781) B853781
theorem B569203 : Blo 566810 569203 := bstep (se 1 (by rfl) ⟨426902, by rfl⟩ : syracuseStep 569203 = 853805) B853805
theorem B569219 : Blo 566810 569219 := bstep (se 1 (by rfl) ⟨426914, by rfl⟩ : syracuseStep 569219 = 853829) B853829
theorem B962435 : Blo 566810 962435 := bstep (se 1 (by rfl) ⟨721826, by rfl⟩ : syracuseStep 962435 = 1443653) B1443653
theorem B569235 : Blo 566810 569235 := bstep (se 1 (by rfl) ⟨426926, by rfl⟩ : syracuseStep 569235 = 853853) B853853
theorem B569251 : Blo 566810 569251 := bstep (se 1 (by rfl) ⟨426938, by rfl⟩ : syracuseStep 569251 = 853877) B853877
theorem B1388465 : Blo 566810 1388465 := bstep (se 2 (by rfl) ⟨520674, by rfl⟩ : syracuseStep 1388465 = 1041349) B1041349
theorem B569267 : Blo 566810 569267 := bstep (se 1 (by rfl) ⟨426950, by rfl⟩ : syracuseStep 569267 = 853901) B853901
theorem B569283 : Blo 566810 569283 := bstep (se 1 (by rfl) ⟨426962, by rfl⟩ : syracuseStep 569283 = 853925) B853925
theorem B569299 : Blo 566810 569299 := bstep (se 1 (by rfl) ⟨426974, by rfl⟩ : syracuseStep 569299 = 853949) B853949
theorem B569315 : Blo 566810 569315 := bstep (se 1 (by rfl) ⟨426986, by rfl⟩ : syracuseStep 569315 = 853973) B853973
theorem B569331 : Blo 566810 569331 := bstep (se 1 (by rfl) ⟨426998, by rfl⟩ : syracuseStep 569331 = 853997) B853997
theorem B569347 : Blo 566810 569347 := bstep (se 1 (by rfl) ⟨427010, by rfl⟩ : syracuseStep 569347 = 854021) B854021
theorem B962563 : Blo 566810 962563 := bstep (se 1 (by rfl) ⟨721922, by rfl⟩ : syracuseStep 962563 = 1443845) B1443845
theorem B569363 : Blo 566810 569363 := bstep (se 1 (by rfl) ⟨427022, by rfl⟩ : syracuseStep 569363 = 854045) B854045
theorem B569379 : Blo 566810 569379 := bstep (se 1 (by rfl) ⟨427034, by rfl⟩ : syracuseStep 569379 = 854069) B854069
theorem B569395 : Blo 566810 569395 := bstep (se 1 (by rfl) ⟨427046, by rfl⟩ : syracuseStep 569395 = 854093) B854093
theorem B569411 : Blo 566810 569411 := bstep (se 1 (by rfl) ⟨427058, by rfl⟩ : syracuseStep 569411 = 854117) B854117
theorem B569427 : Blo 566810 569427 := bstep (se 1 (by rfl) ⟨427070, by rfl⟩ : syracuseStep 569427 = 854141) B854141
theorem B569443 : Blo 566810 569443 := bstep (se 1 (by rfl) ⟨427082, by rfl⟩ : syracuseStep 569443 = 854165) B854165
theorem B569459 : Blo 566810 569459 := bstep (se 1 (by rfl) ⟨427094, by rfl⟩ : syracuseStep 569459 = 854189) B854189
theorem B569475 : Blo 566810 569475 := bstep (se 1 (by rfl) ⟨427106, by rfl⟩ : syracuseStep 569475 = 854213) B854213
theorem B1028227 : Blo 566810 1028227 := bstep (se 1 (by rfl) ⟨771170, by rfl⟩ : syracuseStep 1028227 = 1542341) B1542341
theorem B962705 : Blo 566810 962705 := bstep (se 2 (by rfl) ⟨361014, by rfl⟩ : syracuseStep 962705 = 722029) B722029
theorem B569491 : Blo 566810 569491 := bstep (se 1 (by rfl) ⟨427118, by rfl⟩ : syracuseStep 569491 = 854237) B854237
theorem B569507 : Blo 566810 569507 := bstep (se 1 (by rfl) ⟨427130, by rfl⟩ : syracuseStep 569507 = 854261) B854261
theorem B569523 : Blo 566810 569523 := bstep (se 1 (by rfl) ⟨427142, by rfl⟩ : syracuseStep 569523 = 854285) B854285
theorem B569539 : Blo 566810 569539 := bstep (se 1 (by rfl) ⟨427154, by rfl⟩ : syracuseStep 569539 = 854309) B854309
theorem B569555 : Blo 566810 569555 := bstep (se 1 (by rfl) ⟨427166, by rfl⟩ : syracuseStep 569555 = 854333) B854333
theorem B569571 : Blo 566810 569571 := bstep (se 1 (by rfl) ⟨427178, by rfl⟩ : syracuseStep 569571 = 854357) B854357
theorem B569587 : Blo 566810 569587 := bstep (se 1 (by rfl) ⟨427190, by rfl⟩ : syracuseStep 569587 = 854381) B854381
theorem B569603 : Blo 566810 569603 := bstep (se 1 (by rfl) ⟨427202, by rfl⟩ : syracuseStep 569603 = 854405) B854405
theorem B962833 : Blo 566810 962833 := bstep (se 2 (by rfl) ⟨361062, by rfl⟩ : syracuseStep 962833 = 722125) B722125
theorem B569619 : Blo 566810 569619 := bstep (se 1 (by rfl) ⟨427214, by rfl⟩ : syracuseStep 569619 = 854429) B854429
theorem B569635 : Blo 566810 569635 := bstep (se 1 (by rfl) ⟨427226, by rfl⟩ : syracuseStep 569635 = 854453) B854453
theorem B569651 : Blo 566810 569651 := bstep (se 1 (by rfl) ⟨427238, by rfl⟩ : syracuseStep 569651 = 854477) B854477
theorem B962867 : Blo 566810 962867 := bstep (se 1 (by rfl) ⟨722150, by rfl⟩ : syracuseStep 962867 = 1444301) B1444301
theorem B569667 : Blo 566810 569667 := bstep (se 1 (by rfl) ⟨427250, by rfl⟩ : syracuseStep 569667 = 854501) B854501
theorem B1913165 : Blo 566810 1913165 := bstep (se 3 (by rfl) ⟨358718, by rfl⟩ : syracuseStep 1913165 = 717437) B717437
theorem B569683 : Blo 566810 569683 := bstep (se 1 (by rfl) ⟨427262, by rfl⟩ : syracuseStep 569683 = 854525) B854525
theorem B569699 : Blo 566810 569699 := bstep (se 1 (by rfl) ⟨427274, by rfl⟩ : syracuseStep 569699 = 854549) B854549
theorem B1618289 : Blo 566810 1618289 := bstep (se 2 (by rfl) ⟨606858, by rfl⟩ : syracuseStep 1618289 = 1213717) B1213717
theorem B569715 : Blo 566810 569715 := bstep (se 1 (by rfl) ⟨427286, by rfl⟩ : syracuseStep 569715 = 854573) B854573
theorem B1913219 : Blo 566810 1913219 := bstep (se 1 (by rfl) ⟨1434914, by rfl⟩ : syracuseStep 1913219 = 2869829) B2869829
theorem B569731 : Blo 566810 569731 := bstep (se 1 (by rfl) ⟨427298, by rfl⟩ : syracuseStep 569731 = 854597) B854597
theorem B864659 : Blo 566810 864659 := bstep (se 1 (by rfl) ⟨648494, by rfl⟩ : syracuseStep 864659 = 1296989) B1296989
theorem B569747 : Blo 566810 569747 := bstep (se 1 (by rfl) ⟨427310, by rfl⟩ : syracuseStep 569747 = 854621) B854621
theorem B569763 : Blo 566810 569763 := bstep (se 1 (by rfl) ⟨427322, by rfl⟩ : syracuseStep 569763 = 854645) B854645
theorem B569779 : Blo 566810 569779 := bstep (se 1 (by rfl) ⟨427334, by rfl⟩ : syracuseStep 569779 = 854669) B854669
theorem B962995 : Blo 566810 962995 := bstep (se 1 (by rfl) ⟨722246, by rfl⟩ : syracuseStep 962995 = 1444493) B1444493
theorem B569795 : Blo 566810 569795 := bstep (se 1 (by rfl) ⟨427346, by rfl⟩ : syracuseStep 569795 = 854693) B854693
theorem B569811 : Blo 566810 569811 := bstep (se 1 (by rfl) ⟨427358, by rfl⟩ : syracuseStep 569811 = 854717) B854717
theorem B569827 : Blo 566810 569827 := bstep (se 1 (by rfl) ⟨427370, by rfl⟩ : syracuseStep 569827 = 854741) B854741
theorem B569843 : Blo 566810 569843 := bstep (se 1 (by rfl) ⟨427382, by rfl⟩ : syracuseStep 569843 = 854765) B854765
theorem B569859 : Blo 566810 569859 := bstep (se 1 (by rfl) ⟨427394, by rfl⟩ : syracuseStep 569859 = 854789) B854789
theorem B569875 : Blo 566810 569875 := bstep (se 1 (by rfl) ⟨427406, by rfl⟩ : syracuseStep 569875 = 854813) B854813
theorem B569891 : Blo 566810 569891 := bstep (se 1 (by rfl) ⟨427418, by rfl⟩ : syracuseStep 569891 = 854837) B854837
theorem B569907 : Blo 566810 569907 := bstep (se 1 (by rfl) ⟨427430, by rfl⟩ : syracuseStep 569907 = 854861) B854861
theorem B569923 : Blo 566810 569923 := bstep (se 1 (by rfl) ⟨427442, by rfl⟩ : syracuseStep 569923 = 854885) B854885
theorem B963137 : Blo 566810 963137 := bstep (se 2 (by rfl) ⟨361176, by rfl⟩ : syracuseStep 963137 = 722353) B722353
theorem B569939 : Blo 566810 569939 := bstep (se 1 (by rfl) ⟨427454, by rfl⟩ : syracuseStep 569939 = 854909) B854909
theorem B569955 : Blo 566810 569955 := bstep (se 1 (by rfl) ⟨427466, by rfl⟩ : syracuseStep 569955 = 854933) B854933
theorem B569971 : Blo 566810 569971 := bstep (se 1 (by rfl) ⟨427478, by rfl⟩ : syracuseStep 569971 = 854957) B854957
theorem B569987 : Blo 566810 569987 := bstep (se 1 (by rfl) ⟨427490, by rfl⟩ : syracuseStep 569987 = 854981) B854981
theorem B1913489 : Blo 566810 1913489 := bstep (se 2 (by rfl) ⟨717558, by rfl⟩ : syracuseStep 1913489 = 1435117) B1435117
theorem B570003 : Blo 566810 570003 := bstep (se 1 (by rfl) ⟨427502, by rfl⟩ : syracuseStep 570003 = 855005) B855005
theorem B570019 : Blo 566810 570019 := bstep (se 1 (by rfl) ⟨427514, by rfl⟩ : syracuseStep 570019 = 855029) B855029
theorem B570035 : Blo 566810 570035 := bstep (se 1 (by rfl) ⟨427526, by rfl⟩ : syracuseStep 570035 = 855053) B855053
theorem B570051 : Blo 566810 570051 := bstep (se 1 (by rfl) ⟨427538, by rfl⟩ : syracuseStep 570051 = 855077) B855077
theorem B570067 : Blo 566810 570067 := bstep (se 1 (by rfl) ⟨427550, by rfl⟩ : syracuseStep 570067 = 855101) B855101
theorem B570083 : Blo 566810 570083 := bstep (se 1 (by rfl) ⟨427562, by rfl⟩ : syracuseStep 570083 = 855125) B855125
theorem B570099 : Blo 566810 570099 := bstep (se 1 (by rfl) ⟨427574, by rfl⟩ : syracuseStep 570099 = 855149) B855149
theorem B570115 : Blo 566810 570115 := bstep (se 1 (by rfl) ⟨427586, by rfl⟩ : syracuseStep 570115 = 855173) B855173
theorem B570131 : Blo 566810 570131 := bstep (se 1 (by rfl) ⟨427598, by rfl⟩ : syracuseStep 570131 = 855197) B855197
theorem B44970773 : Blo 566810 44970773 := bstep (se 6 (by rfl) ⟨1054002, by rfl⟩ : syracuseStep 44970773 = 2108005) B2108005
theorem B570147 : Blo 566810 570147 := bstep (se 1 (by rfl) ⟨427610, by rfl⟩ : syracuseStep 570147 = 855221) B855221
theorem B570163 : Blo 566810 570163 := bstep (se 1 (by rfl) ⟨427622, by rfl⟩ : syracuseStep 570163 = 855245) B855245
theorem B570179 : Blo 566810 570179 := bstep (se 1 (by rfl) ⟨427634, by rfl⟩ : syracuseStep 570179 = 855269) B855269
theorem B570195 : Blo 566810 570195 := bstep (se 1 (by rfl) ⟨427646, by rfl⟩ : syracuseStep 570195 = 855293) B855293
theorem B570211 : Blo 566810 570211 := bstep (se 1 (by rfl) ⟨427658, by rfl⟩ : syracuseStep 570211 = 855317) B855317
theorem B570227 : Blo 566810 570227 := bstep (se 1 (by rfl) ⟨427670, by rfl⟩ : syracuseStep 570227 = 855341) B855341
theorem B570243 : Blo 566810 570243 := bstep (se 1 (by rfl) ⟨427682, by rfl⟩ : syracuseStep 570243 = 855365) B855365
theorem B570259 : Blo 566810 570259 := bstep (se 1 (by rfl) ⟨427694, by rfl⟩ : syracuseStep 570259 = 855389) B855389
theorem B2044835 : Blo 566810 2044835 := bstep (se 1 (by rfl) ⟨1533626, by rfl⟩ : syracuseStep 2044835 = 3067253) B3067253
theorem B570275 : Blo 566810 570275 := bstep (se 1 (by rfl) ⟨427706, by rfl⟩ : syracuseStep 570275 = 855413) B855413
theorem B570291 : Blo 566810 570291 := bstep (se 1 (by rfl) ⟨427718, by rfl⟩ : syracuseStep 570291 = 855437) B855437
theorem B570307 : Blo 566810 570307 := bstep (se 1 (by rfl) ⟨427730, by rfl⟩ : syracuseStep 570307 = 855461) B855461
theorem B570323 : Blo 566810 570323 := bstep (se 1 (by rfl) ⟨427742, by rfl⟩ : syracuseStep 570323 = 855485) B855485
theorem B1094627 : Blo 566810 1094627 := bstep (se 1 (by rfl) ⟨820970, by rfl⟩ : syracuseStep 1094627 = 1641941) B1641941
theorem B570339 : Blo 566810 570339 := bstep (se 1 (by rfl) ⟨427754, by rfl⟩ : syracuseStep 570339 = 855509) B855509
theorem B570355 : Blo 566810 570355 := bstep (se 1 (by rfl) ⟨427766, by rfl⟩ : syracuseStep 570355 = 855533) B855533
theorem B570371 : Blo 566810 570371 := bstep (se 1 (by rfl) ⟨427778, by rfl⟩ : syracuseStep 570371 = 855557) B855557
theorem B570387 : Blo 566810 570387 := bstep (se 1 (by rfl) ⟨427790, by rfl⟩ : syracuseStep 570387 = 855581) B855581
theorem B570403 : Blo 566810 570403 := bstep (se 1 (by rfl) ⟨427802, by rfl⟩ : syracuseStep 570403 = 855605) B855605
theorem B570419 : Blo 566810 570419 := bstep (se 1 (by rfl) ⟨427814, by rfl⟩ : syracuseStep 570419 = 855629) B855629
theorem B570435 : Blo 566810 570435 := bstep (se 1 (by rfl) ⟨427826, by rfl⟩ : syracuseStep 570435 = 855653) B855653
theorem B570451 : Blo 566810 570451 := bstep (se 1 (by rfl) ⟨427838, by rfl⟩ : syracuseStep 570451 = 855677) B855677
theorem B570467 : Blo 566810 570467 := bstep (se 1 (by rfl) ⟨427850, by rfl⟩ : syracuseStep 570467 = 855701) B855701
theorem B570483 : Blo 566810 570483 := bstep (se 1 (by rfl) ⟨427862, by rfl⟩ : syracuseStep 570483 = 855725) B855725
theorem B570499 : Blo 566810 570499 := bstep (se 1 (by rfl) ⟨427874, by rfl⟩ : syracuseStep 570499 = 855749) B855749
theorem B570515 : Blo 566810 570515 := bstep (se 1 (by rfl) ⟨427886, by rfl⟩ : syracuseStep 570515 = 855773) B855773
theorem B570531 : Blo 566810 570531 := bstep (se 1 (by rfl) ⟨427898, by rfl⟩ : syracuseStep 570531 = 855797) B855797
theorem B1914029 : Blo 566810 1914029 := bstep (se 3 (by rfl) ⟨358880, by rfl⟩ : syracuseStep 1914029 = 717761) B717761
theorem B570547 : Blo 566810 570547 := bstep (se 1 (by rfl) ⟨427910, by rfl⟩ : syracuseStep 570547 = 855821) B855821
theorem B570563 : Blo 566810 570563 := bstep (se 1 (by rfl) ⟨427922, by rfl⟩ : syracuseStep 570563 = 855845) B855845
theorem B570579 : Blo 566810 570579 := bstep (se 1 (by rfl) ⟨427934, by rfl⟩ : syracuseStep 570579 = 855869) B855869
theorem B1914083 : Blo 566810 1914083 := bstep (se 1 (by rfl) ⟨1435562, by rfl⟩ : syracuseStep 1914083 = 2871125) B2871125
theorem B570595 : Blo 566810 570595 := bstep (se 1 (by rfl) ⟨427946, by rfl⟩ : syracuseStep 570595 = 855893) B855893
theorem B570611 : Blo 566810 570611 := bstep (se 1 (by rfl) ⟨427958, by rfl⟩ : syracuseStep 570611 = 855917) B855917
theorem B570627 : Blo 566810 570627 := bstep (se 1 (by rfl) ⟨427970, by rfl⟩ : syracuseStep 570627 = 855941) B855941
theorem B570643 : Blo 566810 570643 := bstep (se 1 (by rfl) ⟨427982, by rfl⟩ : syracuseStep 570643 = 855965) B855965
theorem B865571 : Blo 566810 865571 := bstep (se 1 (by rfl) ⟨649178, by rfl⟩ : syracuseStep 865571 = 1298357) B1298357
theorem B570659 : Blo 566810 570659 := bstep (se 1 (by rfl) ⟨427994, by rfl⟩ : syracuseStep 570659 = 855989) B855989
theorem B570675 : Blo 566810 570675 := bstep (se 1 (by rfl) ⟨428006, by rfl⟩ : syracuseStep 570675 = 856013) B856013
theorem B570691 : Blo 566810 570691 := bstep (se 1 (by rfl) ⟨428018, by rfl⟩ : syracuseStep 570691 = 856037) B856037
theorem B570707 : Blo 566810 570707 := bstep (se 1 (by rfl) ⟨428030, by rfl⟩ : syracuseStep 570707 = 856061) B856061
theorem B570723 : Blo 566810 570723 := bstep (se 1 (by rfl) ⟨428042, by rfl⟩ : syracuseStep 570723 = 856085) B856085
theorem B570739 : Blo 566810 570739 := bstep (se 1 (by rfl) ⟨428054, by rfl⟩ : syracuseStep 570739 = 856109) B856109
theorem B570755 : Blo 566810 570755 := bstep (se 1 (by rfl) ⟨428066, by rfl⟩ : syracuseStep 570755 = 856133) B856133
theorem B570771 : Blo 566810 570771 := bstep (se 1 (by rfl) ⟨428078, by rfl⟩ : syracuseStep 570771 = 856157) B856157
theorem B570787 : Blo 566810 570787 := bstep (se 1 (by rfl) ⟨428090, by rfl⟩ : syracuseStep 570787 = 856181) B856181
theorem B3650993 : Blo 566810 3650993 := bstep (se 2 (by rfl) ⟨1369122, by rfl⟩ : syracuseStep 3650993 = 2738245) B2738245
theorem B570803 : Blo 566810 570803 := bstep (se 1 (by rfl) ⟨428102, by rfl⟩ : syracuseStep 570803 = 856205) B856205
theorem B2045411 : Blo 566810 2045411 := bstep (se 1 (by rfl) ⟨1534058, by rfl⟩ : syracuseStep 2045411 = 3068117) B3068117
theorem B1914353 : Blo 566810 1914353 := bstep (se 2 (by rfl) ⟨717882, by rfl⟩ : syracuseStep 1914353 = 1435765) B1435765
theorem B4306445 : Blo 566810 4306445 := bstep (se 3 (by rfl) ⟨807458, by rfl⟩ : syracuseStep 4306445 = 1614917) B1614917
theorem B2733709 : Blo 566810 2733709 := bstep (se 3 (by rfl) ⟨512570, by rfl⟩ : syracuseStep 2733709 = 1025141) B1025141
theorem B4601585 : Blo 566810 4601585 := bstep (se 2 (by rfl) ⟨1725594, by rfl⟩ : syracuseStep 4601585 = 3451189) B3451189
theorem B1455889 : Blo 566810 1455889 := bstep (se 2 (by rfl) ⟨545958, by rfl⟩ : syracuseStep 1455889 = 1091917) B1091917
theorem B1619747 : Blo 566810 1619747 := bstep (se 1 (by rfl) ⟨1214810, by rfl⟩ : syracuseStep 1619747 = 2429621) B2429621
theorem B4110193 : Blo 566810 4110193 := bstep (se 2 (by rfl) ⟨1541322, by rfl⟩ : syracuseStep 4110193 = 3082645) B3082645
theorem B1914893 : Blo 566810 1914893 := bstep (se 3 (by rfl) ⟨359042, by rfl⟩ : syracuseStep 1914893 = 718085) B718085
theorem B1914947 : Blo 566810 1914947 := bstep (se 1 (by rfl) ⟨1436210, by rfl⟩ : syracuseStep 1914947 = 2872421) B2872421
theorem B1915217 : Blo 566810 1915217 := bstep (se 2 (by rfl) ⟨718206, by rfl⟩ : syracuseStep 1915217 = 1436413) B1436413
theorem B7485965 : Blo 566810 7485965 := bstep (se 3 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 7485965 = 2807237) B2807237
theorem B1620557 : Blo 566810 1620557 := bstep (se 3 (by rfl) ⟨303854, by rfl⟩ : syracuseStep 1620557 = 607709) B607709
theorem B637699 : Blo 566810 637699 := bstep (se 1 (by rfl) ⟨478274, by rfl⟩ : syracuseStep 637699 = 956549) B956549
theorem B1620749 : Blo 566810 1620749 := bstep (se 3 (by rfl) ⟨303890, by rfl⟩ : syracuseStep 1620749 = 607781) B607781
theorem B1915757 : Blo 566810 1915757 := bstep (se 3 (by rfl) ⟨359204, by rfl⟩ : syracuseStep 1915757 = 718409) B718409
theorem B637843 : Blo 566810 637843 := bstep (se 1 (by rfl) ⟨478382, by rfl⟩ : syracuseStep 637843 = 956765) B956765
theorem B1915811 : Blo 566810 1915811 := bstep (se 1 (by rfl) ⟨1436858, by rfl⟩ : syracuseStep 1915811 = 2873717) B2873717
theorem B1817603 : Blo 566810 1817603 := bstep (se 1 (by rfl) ⟨1363202, by rfl⟩ : syracuseStep 1817603 = 2726405) B2726405
theorem B637987 : Blo 566810 637987 := bstep (se 1 (by rfl) ⟨478490, by rfl⟩ : syracuseStep 637987 = 956981) B956981
theorem B703523 : Blo 566810 703523 := bstep (se 1 (by rfl) ⟨527642, by rfl⟩ : syracuseStep 703523 = 1055285) B1055285
theorem B2047025 : Blo 566810 2047025 := bstep (se 2 (by rfl) ⟨767634, by rfl⟩ : syracuseStep 2047025 = 1535269) B1535269
theorem B2735153 : Blo 566810 2735153 := bstep (se 2 (by rfl) ⟨1025682, by rfl⟩ : syracuseStep 2735153 = 2051365) B2051365
theorem B1850435 : Blo 566810 1850435 := bstep (se 1 (by rfl) ⟨1387826, by rfl⟩ : syracuseStep 1850435 = 2775653) B2775653
theorem B3652685 : Blo 566810 3652685 := bstep (se 3 (by rfl) ⟨684878, by rfl⟩ : syracuseStep 3652685 = 1369757) B1369757
theorem B769105 : Blo 566810 769105 := bstep (se 2 (by rfl) ⟨288414, by rfl⟩ : syracuseStep 769105 = 576829) B576829
theorem B998497 : Blo 566810 998497 := bstep (se 2 (by rfl) ⟨374436, by rfl⟩ : syracuseStep 998497 = 748873) B748873
theorem B1817731 : Blo 566810 1817731 := bstep (se 1 (by rfl) ⟨1363298, by rfl⟩ : syracuseStep 1817731 = 2726597) B2726597
theorem B1916081 : Blo 566810 1916081 := bstep (se 2 (by rfl) ⟨718530, by rfl⟩ : syracuseStep 1916081 = 1437061) B1437061
theorem B638131 : Blo 566810 638131 := bstep (se 1 (by rfl) ⟨478598, by rfl⟩ : syracuseStep 638131 = 957197) B957197
theorem B638275 : Blo 566810 638275 := bstep (se 1 (by rfl) ⟨478706, by rfl⟩ : syracuseStep 638275 = 957413) B957413
theorem B605603 : Blo 566810 605603 := bstep (se 1 (by rfl) ⟨454202, by rfl⟩ : syracuseStep 605603 = 908405) B908405
theorem B1818065 : Blo 566810 1818065 := bstep (se 2 (by rfl) ⟨681774, by rfl⟩ : syracuseStep 1818065 = 1363549) B1363549
theorem B638419 : Blo 566810 638419 := bstep (se 1 (by rfl) ⟨478814, by rfl⟩ : syracuseStep 638419 = 957629) B957629
theorem B638563 : Blo 566810 638563 := bstep (se 1 (by rfl) ⟨478922, by rfl⟩ : syracuseStep 638563 = 957845) B957845
theorem B1916621 : Blo 566810 1916621 := bstep (se 3 (by rfl) ⟨359366, by rfl⟩ : syracuseStep 1916621 = 718733) B718733
theorem B1621741 : Blo 566810 1621741 := bstep (se 3 (by rfl) ⟨304076, by rfl⟩ : syracuseStep 1621741 = 608153) B608153
theorem B638707 : Blo 566810 638707 := bstep (se 1 (by rfl) ⟨479030, by rfl⟩ : syracuseStep 638707 = 958061) B958061
theorem B1916675 : Blo 566810 1916675 := bstep (se 1 (by rfl) ⟨1437506, by rfl⟩ : syracuseStep 1916675 = 2875013) B2875013
theorem B1949453 : Blo 566810 1949453 := bstep (se 3 (by rfl) ⟨365522, by rfl⟩ : syracuseStep 1949453 = 731045) B731045
theorem B1949507 : Blo 566810 1949507 := bstep (se 1 (by rfl) ⟨1462130, by rfl⟩ : syracuseStep 1949507 = 2924261) B2924261
theorem B638851 : Blo 566810 638851 := bstep (se 1 (by rfl) ⟨479138, by rfl⟩ : syracuseStep 638851 = 958277) B958277
theorem B2047949 : Blo 566810 2047949 := bstep (se 3 (by rfl) ⟨383990, by rfl⟩ : syracuseStep 2047949 = 767981) B767981
theorem B1916945 : Blo 566810 1916945 := bstep (se 2 (by rfl) ⟨718854, by rfl⟩ : syracuseStep 1916945 = 1437709) B1437709
theorem B638995 : Blo 566810 638995 := bstep (se 1 (by rfl) ⟨479246, by rfl⟩ : syracuseStep 638995 = 958493) B958493
theorem B639139 : Blo 566810 639139 := bstep (se 1 (by rfl) ⟨479354, by rfl⟩ : syracuseStep 639139 = 958709) B958709
theorem B2769059 : Blo 566810 2769059 := bstep (se 1 (by rfl) ⟨2076794, by rfl⟩ : syracuseStep 2769059 = 4153589) B4153589
theorem B3293347 : Blo 566810 3293347 := bstep (se 1 (by rfl) ⟨2470010, by rfl⟩ : syracuseStep 3293347 = 4940021) B4940021
theorem B4866317 : Blo 566810 4866317 := bstep (se 3 (by rfl) ⟨912434, by rfl⟩ : syracuseStep 4866317 = 1824869) B1824869
theorem B639283 : Blo 566810 639283 := bstep (se 1 (by rfl) ⟨479462, by rfl⟩ : syracuseStep 639283 = 958925) B958925
theorem B4309361 : Blo 566810 4309361 := bstep (se 2 (by rfl) ⟨1616010, by rfl⟩ : syracuseStep 4309361 = 3232021) B3232021
theorem B639427 : Blo 566810 639427 := bstep (se 1 (by rfl) ⟨479570, by rfl⟩ : syracuseStep 639427 = 959141) B959141
theorem B8176099 : Blo 566810 8176099 := bstep (se 1 (by rfl) ⟨6132074, by rfl⟩ : syracuseStep 8176099 = 12264149) B12264149
theorem B3228173 : Blo 566810 3228173 := bstep (se 3 (by rfl) ⟨605282, by rfl⟩ : syracuseStep 3228173 = 1210565) B1210565
theorem B606739 : Blo 566810 606739 := bstep (se 1 (by rfl) ⟨455054, by rfl⟩ : syracuseStep 606739 = 910109) B910109
theorem B1917485 : Blo 566810 1917485 := bstep (se 3 (by rfl) ⟨359528, by rfl⟩ : syracuseStep 1917485 = 719057) B719057
theorem B639571 : Blo 566810 639571 := bstep (se 1 (by rfl) ⟨479678, by rfl⟩ : syracuseStep 639571 = 959357) B959357
theorem B1917539 : Blo 566810 1917539 := bstep (se 1 (by rfl) ⟨1438154, by rfl⟩ : syracuseStep 1917539 = 2876309) B2876309
theorem B5456497 : Blo 566810 5456497 := bstep (se 2 (by rfl) ⟨2046186, by rfl⟩ : syracuseStep 5456497 = 4092373) B4092373
theorem B639715 : Blo 566810 639715 := bstep (se 1 (by rfl) ⟨479786, by rfl⟩ : syracuseStep 639715 = 959573) B959573
theorem B1917809 : Blo 566810 1917809 := bstep (se 2 (by rfl) ⟨719178, by rfl⟩ : syracuseStep 1917809 = 1438357) B1438357
theorem B639859 : Blo 566810 639859 := bstep (se 1 (by rfl) ⟨479894, by rfl⟩ : syracuseStep 639859 = 959789) B959789
theorem B640003 : Blo 566810 640003 := bstep (se 1 (by rfl) ⟨480002, by rfl⟩ : syracuseStep 640003 = 960005) B960005
theorem B2049101 : Blo 566810 2049101 := bstep (se 3 (by rfl) ⟨384206, by rfl⟩ : syracuseStep 2049101 = 768413) B768413
theorem B3687565 : Blo 566810 3687565 := bstep (se 3 (by rfl) ⟨691418, by rfl⟩ : syracuseStep 3687565 = 1382837) B1382837
theorem B9749645 : Blo 566810 9749645 := bstep (se 3 (by rfl) ⟨1828058, by rfl⟩ : syracuseStep 9749645 = 3656117) B3656117
theorem B640147 : Blo 566810 640147 := bstep (se 1 (by rfl) ⟨480110, by rfl⟩ : syracuseStep 640147 = 960221) B960221
theorem B640291 : Blo 566810 640291 := bstep (se 1 (by rfl) ⟨480218, by rfl⟩ : syracuseStep 640291 = 960437) B960437
theorem B607619 : Blo 566810 607619 := bstep (se 1 (by rfl) ⟨455714, by rfl⟩ : syracuseStep 607619 = 911429) B911429
theorem B1918349 : Blo 566810 1918349 := bstep (se 3 (by rfl) ⟨359690, by rfl⟩ : syracuseStep 1918349 = 719381) B719381
theorem B3229105 : Blo 566810 3229105 := bstep (se 2 (by rfl) ⟨1210914, by rfl⟩ : syracuseStep 3229105 = 2421829) B2421829
theorem B1623473 : Blo 566810 1623473 := bstep (se 2 (by rfl) ⟨608802, by rfl⟩ : syracuseStep 1623473 = 1217605) B1217605
theorem B640435 : Blo 566810 640435 := bstep (se 1 (by rfl) ⟨480326, by rfl⟩ : syracuseStep 640435 = 960653) B960653
theorem B1918403 : Blo 566810 1918403 := bstep (se 1 (by rfl) ⟨1438802, by rfl⟩ : syracuseStep 1918403 = 2877605) B2877605
theorem B1295875 : Blo 566810 1295875 := bstep (se 1 (by rfl) ⟨971906, by rfl⟩ : syracuseStep 1295875 = 1943813) B1943813
theorem B607747 : Blo 566810 607747 := bstep (se 1 (by rfl) ⟨455810, by rfl⟩ : syracuseStep 607747 = 911621) B911621
theorem B640579 : Blo 566810 640579 := bstep (se 1 (by rfl) ⟨480434, by rfl⟩ : syracuseStep 640579 = 960869) B960869
theorem B1623665 : Blo 566810 1623665 := bstep (se 2 (by rfl) ⟨608874, by rfl⟩ : syracuseStep 1623665 = 1217749) B1217749
theorem B1918673 : Blo 566810 1918673 := bstep (se 2 (by rfl) ⟨719502, by rfl⟩ : syracuseStep 1918673 = 1439005) B1439005
theorem B640723 : Blo 566810 640723 := bstep (se 1 (by rfl) ⟨480542, by rfl⟩ : syracuseStep 640723 = 961085) B961085
theorem B7128803 : Blo 566810 7128803 := bstep (se 1 (by rfl) ⟨5346602, by rfl⟩ : syracuseStep 7128803 = 10693205) B10693205
theorem B640867 : Blo 566810 640867 := bstep (se 1 (by rfl) ⟨480650, by rfl⟩ : syracuseStep 640867 = 961301) B961301
theorem B641011 : Blo 566810 641011 := bstep (se 1 (by rfl) ⟨480758, by rfl⟩ : syracuseStep 641011 = 961517) B961517
theorem B1755245 : Blo 566810 1755245 := bstep (se 3 (by rfl) ⟨329108, by rfl⟩ : syracuseStep 1755245 = 658217) B658217
theorem B641155 : Blo 566810 641155 := bstep (se 1 (by rfl) ⟨480866, by rfl⟩ : syracuseStep 641155 = 961733) B961733
theorem B2050211 : Blo 566810 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B3066083 : Blo 566810 3066083 := bstep (se 1 (by rfl) ⟨2299562, by rfl⟩ : syracuseStep 3066083 = 4599125) B4599125
theorem B1919213 : Blo 566810 1919213 := bstep (se 3 (by rfl) ⟨359852, by rfl⟩ : syracuseStep 1919213 = 719705) B719705
theorem B641299 : Blo 566810 641299 := bstep (se 1 (by rfl) ⟨480974, by rfl⟩ : syracuseStep 641299 = 961949) B961949
theorem B1919267 : Blo 566810 1919267 := bstep (se 1 (by rfl) ⟨1439450, by rfl⟩ : syracuseStep 1919267 = 2878901) B2878901
theorem B608563 : Blo 566810 608563 := bstep (se 1 (by rfl) ⟨456422, by rfl⟩ : syracuseStep 608563 = 912845) B912845
theorem B1821037 : Blo 566810 1821037 := bstep (se 3 (by rfl) ⟨341444, by rfl⟩ : syracuseStep 1821037 = 682889) B682889
theorem B2869667 : Blo 566810 2869667 := bstep (se 1 (by rfl) ⟨2152250, by rfl⟩ : syracuseStep 2869667 = 4304501) B4304501
theorem B641443 : Blo 566810 641443 := bstep (se 1 (by rfl) ⟨481082, by rfl⟩ : syracuseStep 641443 = 962165) B962165
theorem B1919537 : Blo 566810 1919537 := bstep (se 2 (by rfl) ⟨719826, by rfl⟩ : syracuseStep 1919537 = 1439653) B1439653
theorem B641587 : Blo 566810 641587 := bstep (se 1 (by rfl) ⟨481190, by rfl⟩ : syracuseStep 641587 = 962381) B962381
theorem B1624657 : Blo 566810 1624657 := bstep (se 2 (by rfl) ⟨609246, by rfl⟩ : syracuseStep 1624657 = 1218493) B1218493
theorem B1821293 : Blo 566810 1821293 := bstep (se 3 (by rfl) ⟨341492, by rfl⟩ : syracuseStep 1821293 = 682985) B682985
theorem B641731 : Blo 566810 641731 := bstep (se 1 (by rfl) ⟨481298, by rfl⟩ : syracuseStep 641731 = 962597) B962597
theorem B5851889 : Blo 566810 5851889 := bstep (se 2 (by rfl) ⟨2194458, by rfl⟩ : syracuseStep 5851889 = 4388917) B4388917
theorem B641875 : Blo 566810 641875 := bstep (se 1 (by rfl) ⟨481406, by rfl⟩ : syracuseStep 641875 = 962813) B962813
theorem B3230563 : Blo 566810 3230563 := bstep (se 1 (by rfl) ⟨2422922, by rfl⟩ : syracuseStep 3230563 = 4845845) B4845845
theorem B1624931 : Blo 566810 1624931 := bstep (se 1 (by rfl) ⟨1218698, by rfl⟩ : syracuseStep 1624931 = 2437397) B2437397
theorem B642019 : Blo 566810 642019 := bstep (se 1 (by rfl) ⟨481514, by rfl⟩ : syracuseStep 642019 = 963029) B963029
theorem B1625123 : Blo 566810 1625123 := bstep (se 1 (by rfl) ⟨1218842, by rfl⟩ : syracuseStep 1625123 = 2437685) B2437685
theorem B1920077 : Blo 566810 1920077 := bstep (se 3 (by rfl) ⟨360014, by rfl⟩ : syracuseStep 1920077 = 720029) B720029
theorem B1920131 : Blo 566810 1920131 := bstep (se 1 (by rfl) ⟨1440098, by rfl⟩ : syracuseStep 1920131 = 2880197) B2880197
theorem B2870477 : Blo 566810 2870477 := bstep (se 3 (by rfl) ⟨538214, by rfl⟩ : syracuseStep 2870477 = 1076429) B1076429
theorem B3231089 : Blo 566810 3231089 := bstep (se 2 (by rfl) ⟨1211658, by rfl⟩ : syracuseStep 3231089 = 2423317) B2423317
theorem B1920401 : Blo 566810 1920401 := bstep (se 2 (by rfl) ⟨720150, by rfl⟩ : syracuseStep 1920401 = 1440301) B1440301
theorem B2314061 : Blo 566810 2314061 := bstep (se 3 (by rfl) ⟨433886, by rfl⟩ : syracuseStep 2314061 = 867773) B867773
theorem B1920941 : Blo 566810 1920941 := bstep (se 3 (by rfl) ⟨360176, by rfl⟩ : syracuseStep 1920941 = 720353) B720353
theorem B1920995 : Blo 566810 1920995 := bstep (se 1 (by rfl) ⟨1440746, by rfl⟩ : syracuseStep 1920995 = 2881493) B2881493
theorem B1822819 : Blo 566810 1822819 := bstep (se 1 (by rfl) ⟨1367114, by rfl⟩ : syracuseStep 1822819 = 2734229) B2734229
theorem B1921265 : Blo 566810 1921265 := bstep (se 2 (by rfl) ⟨720474, by rfl⟩ : syracuseStep 1921265 = 1440949) B1440949
theorem B10932677 : Blo 566810 10932677 := bstep (se 4 (by rfl) ⟨1024938, by rfl⟩ : syracuseStep 10932677 = 2049877) B2049877
theorem B11686513 : Blo 566810 11686513 := bstep (se 2 (by rfl) ⟨4382442, by rfl⟩ : syracuseStep 11686513 = 8764885) B8764885
theorem B578179 : Blo 566810 578179 := bstep (se 1 (by rfl) ⟨433634, by rfl⟩ : syracuseStep 578179 = 867269) B867269
theorem B1921805 : Blo 566810 1921805 := bstep (se 3 (by rfl) ⟨360338, by rfl⟩ : syracuseStep 1921805 = 720677) B720677
theorem B3232547 : Blo 566810 3232547 := bstep (se 1 (by rfl) ⟨2424410, by rfl⟩ : syracuseStep 3232547 = 4848821) B4848821
theorem B1921859 : Blo 566810 1921859 := bstep (se 1 (by rfl) ⟨1441394, by rfl⟩ : syracuseStep 1921859 = 2882789) B2882789
theorem B1823651 : Blo 566810 1823651 := bstep (se 1 (by rfl) ⟨1367738, by rfl⟩ : syracuseStep 1823651 = 2735477) B2735477
theorem B1922129 : Blo 566810 1922129 := bstep (se 2 (by rfl) ⟨720798, by rfl⟩ : syracuseStep 1922129 = 1441597) B1441597
theorem B808051 : Blo 566810 808051 := bstep (se 1 (by rfl) ⟨606038, by rfl⟩ : syracuseStep 808051 = 1212077) B1212077
theorem B1496227 : Blo 566810 1496227 := bstep (se 1 (by rfl) ⟨1122170, by rfl⟩ : syracuseStep 1496227 = 2244341) B2244341
theorem B1824049 : Blo 566810 1824049 := bstep (se 2 (by rfl) ⟨684018, by rfl⟩ : syracuseStep 1824049 = 1368037) B1368037
theorem B2053453 : Blo 566810 2053453 := bstep (se 3 (by rfl) ⟨385022, by rfl⟩ : syracuseStep 2053453 = 770045) B770045
theorem B1824113 : Blo 566810 1824113 := bstep (se 2 (by rfl) ⟨684042, by rfl⟩ : syracuseStep 1824113 = 1368085) B1368085
theorem B1922669 : Blo 566810 1922669 := bstep (se 3 (by rfl) ⟨360500, by rfl⟩ : syracuseStep 1922669 = 721001) B721001
theorem B1922723 : Blo 566810 1922723 := bstep (se 1 (by rfl) ⟨1442042, by rfl⟩ : syracuseStep 1922723 = 2884085) B2884085
theorem B1365731 : Blo 566810 1365731 := bstep (se 1 (by rfl) ⟨1024298, by rfl⟩ : syracuseStep 1365731 = 2048597) B2048597
theorem B1464227 : Blo 566810 1464227 := bstep (se 1 (by rfl) ⟨1098170, by rfl⟩ : syracuseStep 1464227 = 2196341) B2196341
theorem B1922993 : Blo 566810 1922993 := bstep (se 2 (by rfl) ⟨721122, by rfl⟩ : syracuseStep 1922993 = 1442245) B1442245
theorem B2152433 : Blo 566810 2152433 := bstep (se 2 (by rfl) ⟨807162, by rfl⟩ : syracuseStep 2152433 = 1614325) B1614325
theorem B2873393 : Blo 566810 2873393 := bstep (se 2 (by rfl) ⟨1077522, by rfl⟩ : syracuseStep 2873393 = 2155045) B2155045
theorem B6477893 : Blo 566810 6477893 := bstep (se 4 (by rfl) ⟨607302, by rfl⟩ : syracuseStep 6477893 = 1214605) B1214605
theorem B1235057 : Blo 566810 1235057 := bstep (se 2 (by rfl) ⟨463146, by rfl⟩ : syracuseStep 1235057 = 926293) B926293
theorem B809185 : Blo 566810 809185 := bstep (se 2 (by rfl) ⟨303444, by rfl⟩ : syracuseStep 809185 = 606889) B606889
theorem B809281 : Blo 566810 809281 := bstep (se 2 (by rfl) ⟨303480, by rfl⟩ : syracuseStep 809281 = 606961) B606961
theorem B1923533 : Blo 566810 1923533 := bstep (se 3 (by rfl) ⟨360662, by rfl⟩ : syracuseStep 1923533 = 721325) B721325
theorem B1923587 : Blo 566810 1923587 := bstep (se 1 (by rfl) ⟨1442690, by rfl⟩ : syracuseStep 1923587 = 2885381) B2885381
theorem B2185805 : Blo 566810 2185805 := bstep (se 3 (by rfl) ⟨409838, by rfl⟩ : syracuseStep 2185805 = 819677) B819677
theorem B3234437 : Blo 566810 3234437 := bstep (se 4 (by rfl) ⟨303228, by rfl⟩ : syracuseStep 3234437 = 606457) B606457
theorem B2153101 : Blo 566810 2153101 := bstep (se 3 (by rfl) ⟨403706, by rfl⟩ : syracuseStep 2153101 = 807413) B807413
theorem B3463843 : Blo 566810 3463843 := bstep (se 1 (by rfl) ⟨2597882, by rfl⟩ : syracuseStep 3463843 = 5195765) B5195765
theorem B1727153 : Blo 566810 1727153 := bstep (se 2 (by rfl) ⟨647682, by rfl⟩ : syracuseStep 1727153 = 1295365) B1295365
theorem B1727249 : Blo 566810 1727249 := bstep (se 2 (by rfl) ⟨647718, by rfl⟩ : syracuseStep 1727249 = 1295437) B1295437
theorem B1923857 : Blo 566810 1923857 := bstep (se 2 (by rfl) ⟨721446, by rfl⟩ : syracuseStep 1923857 = 1442893) B1442893
theorem B809777 : Blo 566810 809777 := bstep (se 2 (by rfl) ⟨303666, by rfl⟩ : syracuseStep 809777 = 607333) B607333
theorem B908129 : Blo 566810 908129 := bstep (se 2 (by rfl) ⟨340548, by rfl⟩ : syracuseStep 908129 = 681097) B681097
theorem B3070925 : Blo 566810 3070925 := bstep (se 3 (by rfl) ⟨575798, by rfl⟩ : syracuseStep 3070925 = 1151597) B1151597
theorem B908545 : Blo 566810 908545 := bstep (se 2 (by rfl) ⟨340704, by rfl⟩ : syracuseStep 908545 = 681409) B681409
theorem B1924397 : Blo 566810 1924397 := bstep (se 3 (by rfl) ⟨360824, by rfl⟩ : syracuseStep 1924397 = 721649) B721649
theorem B1039697 : Blo 566810 1039697 := bstep (se 2 (by rfl) ⟨389886, by rfl⟩ : syracuseStep 1039697 = 779773) B779773
theorem B1924451 : Blo 566810 1924451 := bstep (se 1 (by rfl) ⟨1443338, by rfl⟩ : syracuseStep 1924451 = 2886677) B2886677
theorem B2153891 : Blo 566810 2153891 := bstep (se 1 (by rfl) ⟨1615418, by rfl⟩ : syracuseStep 2153891 = 3230837) B3230837
theorem B5823971 : Blo 566810 5823971 := bstep (se 1 (by rfl) ⟨4367978, by rfl⟩ : syracuseStep 5823971 = 8735957) B8735957
theorem B2874851 : Blo 566810 2874851 := bstep (se 1 (by rfl) ⟨2156138, by rfl⟩ : syracuseStep 2874851 = 4312277) B4312277
theorem B1924721 : Blo 566810 1924721 := bstep (se 2 (by rfl) ⟨721770, by rfl⟩ : syracuseStep 1924721 = 1443541) B1443541
theorem B810643 : Blo 566810 810643 := bstep (se 1 (by rfl) ⟨607982, by rfl⟩ : syracuseStep 810643 = 1215965) B1215965
theorem B810739 : Blo 566810 810739 := bstep (se 1 (by rfl) ⟨608054, by rfl⟩ : syracuseStep 810739 = 1216109) B1216109
theorem B2056049 : Blo 566810 2056049 := bstep (se 2 (by rfl) ⟨771018, by rfl⟩ : syracuseStep 2056049 = 1542037) B1542037
theorem B2154545 : Blo 566810 2154545 := bstep (se 2 (by rfl) ⟨807954, by rfl⟩ : syracuseStep 2154545 = 1615909) B1615909
theorem B909443 : Blo 566810 909443 := bstep (se 1 (by rfl) ⟨682082, by rfl⟩ : syracuseStep 909443 = 1364165) B1364165
theorem B1925261 : Blo 566810 1925261 := bstep (se 3 (by rfl) ⟨360986, by rfl⟩ : syracuseStep 1925261 = 721973) B721973
theorem B1925315 : Blo 566810 1925315 := bstep (se 1 (by rfl) ⟨1443986, by rfl⟩ : syracuseStep 1925315 = 2887973) B2887973
theorem B5824709 : Blo 566810 5824709 := bstep (se 4 (by rfl) ⟨546066, by rfl⟩ : syracuseStep 5824709 = 1092133) B1092133
theorem B811235 : Blo 566810 811235 := bstep (se 1 (by rfl) ⟨608426, by rfl⟩ : syracuseStep 811235 = 1216853) B1216853
theorem B2875661 : Blo 566810 2875661 := bstep (se 3 (by rfl) ⟨539186, by rfl⟩ : syracuseStep 2875661 = 1078373) B1078373
theorem B909667 : Blo 566810 909667 := bstep (se 1 (by rfl) ⟨682250, by rfl⟩ : syracuseStep 909667 = 1364501) B1364501
theorem B1925585 : Blo 566810 1925585 := bstep (se 2 (by rfl) ⟨722094, by rfl⟩ : syracuseStep 1925585 = 1444189) B1444189
theorem B811873 : Blo 566810 811873 := bstep (se 2 (by rfl) ⟨304452, by rfl⟩ : syracuseStep 811873 = 608905) B608905
theorem B1926125 : Blo 566810 1926125 := bstep (se 3 (by rfl) ⟨361148, by rfl⟩ : syracuseStep 1926125 = 722297) B722297
theorem B1926179 : Blo 566810 1926179 := bstep (se 1 (by rfl) ⟨1444634, by rfl⟩ : syracuseStep 1926179 = 2889269) B2889269
theorem B812209 : Blo 566810 812209 := bstep (se 2 (by rfl) ⟨304578, by rfl⟩ : syracuseStep 812209 = 609157) B609157
theorem B1369315 : Blo 566810 1369315 := bstep (se 1 (by rfl) ⟨1026986, by rfl⟩ : syracuseStep 1369315 = 2053973) B2053973
theorem B976115 : Blo 566810 976115 := bstep (se 1 (by rfl) ⟨732086, by rfl⟩ : syracuseStep 976115 = 1464173) B1464173
theorem B1926449 : Blo 566810 1926449 := bstep (se 2 (by rfl) ⟨722418, by rfl⟩ : syracuseStep 1926449 = 1444837) B1444837
theorem B910673 : Blo 566810 910673 := bstep (se 2 (by rfl) ⟨341502, by rfl⟩ : syracuseStep 910673 = 683005) B683005
theorem B1828291 : Blo 566810 1828291 := bstep (se 1 (by rfl) ⟨1371218, by rfl⟩ : syracuseStep 1828291 = 2742437) B2742437
theorem B2156003 : Blo 566810 2156003 := bstep (se 1 (by rfl) ⟨1617002, by rfl⟩ : syracuseStep 2156003 = 3234005) B3234005
theorem B1533421 : Blo 566810 1533421 := bstep (se 3 (by rfl) ⟨287516, by rfl⟩ : syracuseStep 1533421 = 575033) B575033
theorem B2156017 : Blo 566810 2156017 := bstep (se 2 (by rfl) ⟨808506, by rfl⟩ : syracuseStep 2156017 = 1617013) B1617013
theorem B910865 : Blo 566810 910865 := bstep (se 2 (by rfl) ⟨341574, by rfl⟩ : syracuseStep 910865 = 683149) B683149
theorem B1435441 : Blo 566810 1435441 := bstep (se 2 (by rfl) ⟨538290, by rfl⟩ : syracuseStep 1435441 = 1076581) B1076581
theorem B1730413 : Blo 566810 1730413 := bstep (se 3 (by rfl) ⟨324452, by rfl⟩ : syracuseStep 1730413 = 648905) B648905
theorem B13854577 : Blo 566810 13854577 := bstep (se 2 (by rfl) ⟨5195466, by rfl⟩ : syracuseStep 13854577 = 10390933) B10390933
theorem B1435715 : Blo 566810 1435715 := bstep (se 1 (by rfl) ⟨1076786, by rfl⟩ : syracuseStep 1435715 = 2153573) B2153573
theorem B3074125 : Blo 566810 3074125 := bstep (se 3 (by rfl) ⟨576398, by rfl⟩ : syracuseStep 3074125 = 1152797) B1152797
theorem B649379 : Blo 566810 649379 := bstep (se 1 (by rfl) ⟨487034, by rfl⟩ : syracuseStep 649379 = 974069) B974069
theorem B5204195 : Blo 566810 5204195 := bstep (se 1 (by rfl) ⟨3903146, by rfl⟩ : syracuseStep 5204195 = 7806293) B7806293
theorem B1370353 : Blo 566810 1370353 := bstep (se 2 (by rfl) ⟨513882, by rfl⟩ : syracuseStep 1370353 = 1027765) B1027765
theorem B1435907 : Blo 566810 1435907 := bstep (se 1 (by rfl) ⟨1076930, by rfl⟩ : syracuseStep 1435907 = 2153861) B2153861
theorem B1403281 : Blo 566810 1403281 := bstep (se 2 (by rfl) ⟨526230, by rfl⟩ : syracuseStep 1403281 = 1052461) B1052461
theorem B1534403 : Blo 566810 1534403 := bstep (se 1 (by rfl) ⟨1150802, by rfl⟩ : syracuseStep 1534403 = 2301605) B2301605
theorem B7301573 : Blo 566810 7301573 := bstep (se 4 (by rfl) ⟨684522, by rfl⟩ : syracuseStep 7301573 = 1369045) B1369045
theorem B879427 : Blo 566810 879427 := bstep (se 1 (by rfl) ⟨659570, by rfl⟩ : syracuseStep 879427 = 1319141) B1319141
theorem B2157475 : Blo 566810 2157475 := bstep (se 1 (by rfl) ⟨1618106, by rfl⟩ : syracuseStep 2157475 = 3236213) B3236213
theorem B3075077 : Blo 566810 3075077 := bstep (se 4 (by rfl) ⟨288288, by rfl⟩ : syracuseStep 3075077 = 576577) B576577
theorem B912467 : Blo 566810 912467 := bstep (se 1 (by rfl) ⟨684350, by rfl⟩ : syracuseStep 912467 = 1368701) B1368701
theorem B1076323 : Blo 566810 1076323 := bstep (se 1 (by rfl) ⟨807242, by rfl⟩ : syracuseStep 1076323 = 1614485) B1614485
theorem B2878577 : Blo 566810 2878577 := bstep (se 2 (by rfl) ⟨1079466, by rfl⟩ : syracuseStep 2878577 = 2158933) B2158933
theorem B1436849 : Blo 566810 1436849 := bstep (se 2 (by rfl) ⟨538818, by rfl⟩ : syracuseStep 1436849 = 1077637) B1077637
theorem B1436899 : Blo 566810 1436899 := bstep (se 1 (by rfl) ⟨1077674, by rfl⟩ : syracuseStep 1436899 = 2155349) B2155349
theorem B1076483 : Blo 566810 1076483 := bstep (se 1 (by rfl) ⟨807362, by rfl⟩ : syracuseStep 1076483 = 1614725) B1614725
theorem B1437041 : Blo 566810 1437041 := bstep (se 2 (by rfl) ⟨538890, by rfl⟩ : syracuseStep 1437041 = 1077781) B1077781
theorem B1535377 : Blo 566810 1535377 := bstep (se 2 (by rfl) ⟨575766, by rfl⟩ : syracuseStep 1535377 = 1151533) B1151533
theorem B1535441 : Blo 566810 1535441 := bstep (se 2 (by rfl) ⟨575790, by rfl⟩ : syracuseStep 1535441 = 1151581) B1151581
theorem B912851 : Blo 566810 912851 := bstep (se 1 (by rfl) ⟨684638, by rfl⟩ : syracuseStep 912851 = 1369277) B1369277
theorem B1732067 : Blo 566810 1732067 := bstep (se 1 (by rfl) ⟨1299050, by rfl⟩ : syracuseStep 1732067 = 2598101) B2598101
theorem B912979 : Blo 566810 912979 := bstep (se 1 (by rfl) ⟨684734, by rfl⟩ : syracuseStep 912979 = 1369469) B1369469
theorem B3468899 : Blo 566810 3468899 := bstep (se 1 (by rfl) ⟨2601674, by rfl⟩ : syracuseStep 3468899 = 5203349) B5203349
theorem B3272333 : Blo 566810 3272333 := bstep (se 3 (by rfl) ⟨613562, by rfl⟩ : syracuseStep 3272333 = 1227125) B1227125
theorem B1732337 : Blo 566810 1732337 := bstep (se 2 (by rfl) ⟨649626, by rfl⟩ : syracuseStep 1732337 = 1299253) B1299253
theorem B6483725 : Blo 566810 6483725 := bstep (se 3 (by rfl) ⟨1215698, by rfl⟩ : syracuseStep 6483725 = 2431397) B2431397
theorem B913697 : Blo 566810 913697 := bstep (se 2 (by rfl) ⟨342636, by rfl⟩ : syracuseStep 913697 = 685273) B685273
theorem B1077553 : Blo 566810 1077553 := bstep (se 2 (by rfl) ⟨404082, by rfl⟩ : syracuseStep 1077553 = 808165) B808165
theorem B3240269 : Blo 566810 3240269 := bstep (se 3 (by rfl) ⟨607550, by rfl⟩ : syracuseStep 3240269 = 1215101) B1215101
theorem B1438033 : Blo 566810 1438033 := bstep (se 2 (by rfl) ⟨539262, by rfl⟩ : syracuseStep 1438033 = 1078525) B1078525
theorem B913889 : Blo 566810 913889 := bstep (se 2 (by rfl) ⟨342708, by rfl⟩ : syracuseStep 913889 = 685417) B685417
theorem B2880035 : Blo 566810 2880035 := bstep (se 1 (by rfl) ⟨2160026, by rfl⟩ : syracuseStep 2880035 = 4320053) B4320053
theorem B3469873 : Blo 566810 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B1438307 : Blo 566810 1438307 := bstep (se 1 (by rfl) ⟨1078730, by rfl⟩ : syracuseStep 1438307 = 2157461) B2157461
theorem B717427 : Blo 566810 717427 := bstep (se 1 (by rfl) ⟨538070, by rfl⟩ : syracuseStep 717427 = 1076141) B1076141
theorem B1536653 : Blo 566810 1536653 := bstep (se 3 (by rfl) ⟨288122, by rfl⟩ : syracuseStep 1536653 = 576245) B576245
theorem B1438499 : Blo 566810 1438499 := bstep (se 1 (by rfl) ⟨1078874, by rfl⟩ : syracuseStep 1438499 = 2157749) B2157749
theorem B2159693 : Blo 566810 2159693 := bstep (se 3 (by rfl) ⟨404942, by rfl⟩ : syracuseStep 2159693 = 809885) B809885
theorem B717923 : Blo 566810 717923 := bstep (se 1 (by rfl) ⟨538442, by rfl⟩ : syracuseStep 717923 = 1076885) B1076885
theorem B2422001 : Blo 566810 2422001 := bstep (se 2 (by rfl) ⟨908250, by rfl⟩ : syracuseStep 2422001 = 1816501) B1816501
theorem B2880845 : Blo 566810 2880845 := bstep (se 3 (by rfl) ⟨540158, by rfl⟩ : syracuseStep 2880845 = 1080317) B1080317
theorem B1078609 : Blo 566810 1078609 := bstep (se 2 (by rfl) ⟨404478, by rfl⟩ : syracuseStep 1078609 = 808957) B808957
theorem B1734061 : Blo 566810 1734061 := bstep (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) B650273
theorem B1275569 : Blo 566810 1275569 := bstep (se 2 (by rfl) ⟨478338, by rfl⟩ : syracuseStep 1275569 = 956677) B956677
theorem B1275587 : Blo 566810 1275587 := bstep (se 1 (by rfl) ⟨956690, by rfl⟩ : syracuseStep 1275587 = 1913381) B1913381
theorem B1439441 : Blo 566810 1439441 := bstep (se 2 (by rfl) ⟨539790, by rfl⟩ : syracuseStep 1439441 = 1079581) B1079581
theorem B1079011 : Blo 566810 1079011 := bstep (se 1 (by rfl) ⟨809258, by rfl⟩ : syracuseStep 1079011 = 1618517) B1618517
theorem B1439491 : Blo 566810 1439491 := bstep (se 1 (by rfl) ⟨1079618, by rfl⟩ : syracuseStep 1439491 = 2159237) B2159237
theorem B1079057 : Blo 566810 1079057 := bstep (se 2 (by rfl) ⟨404646, by rfl⟩ : syracuseStep 1079057 = 809293) B809293
theorem B718627 : Blo 566810 718627 := bstep (se 1 (by rfl) ⟨538970, by rfl⟩ : syracuseStep 718627 = 1077941) B1077941
theorem B718723 : Blo 566810 718723 := bstep (se 1 (by rfl) ⟨539042, by rfl⟩ : syracuseStep 718723 = 1078085) B1078085
theorem B1439633 : Blo 566810 1439633 := bstep (se 2 (by rfl) ⟨539862, by rfl⟩ : syracuseStep 1439633 = 1079725) B1079725
theorem B1275857 : Blo 566810 1275857 := bstep (se 2 (by rfl) ⟨478446, by rfl⟩ : syracuseStep 1275857 = 956893) B956893
theorem B1275875 : Blo 566810 1275875 := bstep (se 1 (by rfl) ⟨956906, by rfl⟩ : syracuseStep 1275875 = 1913813) B1913813
theorem B1079345 : Blo 566810 1079345 := bstep (se 2 (by rfl) ⟨404754, by rfl⟩ : syracuseStep 1079345 = 809509) B809509
theorem B1276145 : Blo 566810 1276145 := bstep (se 2 (by rfl) ⟨478554, by rfl⟩ : syracuseStep 1276145 = 957109) B957109
theorem B1276163 : Blo 566810 1276163 := bstep (se 1 (by rfl) ⟨957122, by rfl⟩ : syracuseStep 1276163 = 1914245) B1914245
theorem B850241 : Blo 566810 850241 := bstep (se 2 (by rfl) ⟨318840, by rfl⟩ : syracuseStep 850241 = 637681) B637681
theorem B850259 : Blo 566810 850259 := bstep (se 1 (by rfl) ⟨637694, by rfl⟩ : syracuseStep 850259 = 1275389) B1275389
theorem B850289 : Blo 566810 850289 := bstep (se 2 (by rfl) ⟨318858, by rfl⟩ : syracuseStep 850289 = 637717) B637717
theorem B719219 : Blo 566810 719219 := bstep (se 1 (by rfl) ⟨539414, by rfl⟩ : syracuseStep 719219 = 1078829) B1078829
theorem B850307 : Blo 566810 850307 := bstep (se 1 (by rfl) ⟨637730, by rfl⟩ : syracuseStep 850307 = 1275461) B1275461
theorem B850337 : Blo 566810 850337 := bstep (se 2 (by rfl) ⟨318876, by rfl⟩ : syracuseStep 850337 = 637753) B637753
theorem B850355 : Blo 566810 850355 := bstep (se 1 (by rfl) ⟨637766, by rfl⟩ : syracuseStep 850355 = 1275533) B1275533
theorem B9238981 : Blo 566810 9238981 := bstep (se 4 (by rfl) ⟨866154, by rfl⟩ : syracuseStep 9238981 = 1732309) B1732309
theorem B850385 : Blo 566810 850385 := bstep (se 2 (by rfl) ⟨318894, by rfl⟩ : syracuseStep 850385 = 637789) B637789
theorem B850403 : Blo 566810 850403 := bstep (se 1 (by rfl) ⟨637802, by rfl⟩ : syracuseStep 850403 = 1275605) B1275605
theorem B850433 : Blo 566810 850433 := bstep (se 2 (by rfl) ⟨318912, by rfl⟩ : syracuseStep 850433 = 637825) B637825
theorem B3242501 : Blo 566810 3242501 := bstep (se 4 (by rfl) ⟨303984, by rfl⟩ : syracuseStep 3242501 = 607969) B607969
theorem B1276433 : Blo 566810 1276433 := bstep (se 2 (by rfl) ⟨478662, by rfl⟩ : syracuseStep 1276433 = 957325) B957325
theorem B850451 : Blo 566810 850451 := bstep (se 1 (by rfl) ⟨637838, by rfl⟩ : syracuseStep 850451 = 1275677) B1275677
theorem B1276451 : Blo 566810 1276451 := bstep (se 1 (by rfl) ⟨957338, by rfl⟩ : syracuseStep 1276451 = 1914677) B1914677
theorem B850481 : Blo 566810 850481 := bstep (se 2 (by rfl) ⟨318930, by rfl⟩ : syracuseStep 850481 = 637861) B637861
theorem B850499 : Blo 566810 850499 := bstep (se 1 (by rfl) ⟨637874, by rfl⟩ : syracuseStep 850499 = 1275749) B1275749
theorem B850529 : Blo 566810 850529 := bstep (se 2 (by rfl) ⟨318948, by rfl⟩ : syracuseStep 850529 = 637897) B637897
theorem B6486641 : Blo 566810 6486641 := bstep (se 2 (by rfl) ⟨2432490, by rfl⟩ : syracuseStep 6486641 = 4864981) B4864981
theorem B850547 : Blo 566810 850547 := bstep (se 1 (by rfl) ⟨637910, by rfl⟩ : syracuseStep 850547 = 1275821) B1275821
theorem B850577 : Blo 566810 850577 := bstep (se 2 (by rfl) ⟨318966, by rfl⟩ : syracuseStep 850577 = 637933) B637933
theorem B850595 : Blo 566810 850595 := bstep (se 1 (by rfl) ⟨637946, by rfl⟩ : syracuseStep 850595 = 1275893) B1275893
theorem B850625 : Blo 566810 850625 := bstep (se 2 (by rfl) ⟨318984, by rfl⟩ : syracuseStep 850625 = 637969) B637969
theorem B850643 : Blo 566810 850643 := bstep (se 1 (by rfl) ⟨637982, by rfl⟩ : syracuseStep 850643 = 1275965) B1275965
theorem B850673 : Blo 566810 850673 := bstep (se 2 (by rfl) ⟨319002, by rfl⟩ : syracuseStep 850673 = 638005) B638005
theorem B850691 : Blo 566810 850691 := bstep (se 1 (by rfl) ⟨638018, by rfl⟩ : syracuseStep 850691 = 1276037) B1276037
theorem B1080067 : Blo 566810 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B850721 : Blo 566810 850721 := bstep (se 2 (by rfl) ⟨319020, by rfl⟩ : syracuseStep 850721 = 638041) B638041
theorem B1276721 : Blo 566810 1276721 := bstep (se 2 (by rfl) ⟨478770, by rfl⟩ : syracuseStep 1276721 = 957541) B957541
theorem B850739 : Blo 566810 850739 := bstep (se 1 (by rfl) ⟨638054, by rfl⟩ : syracuseStep 850739 = 1276109) B1276109
theorem B7306037 : Blo 566810 7306037 := bstep (se 5 (by rfl) ⟨342470, by rfl⟩ : syracuseStep 7306037 = 684941) B684941
theorem B1276739 : Blo 566810 1276739 := bstep (se 1 (by rfl) ⟨957554, by rfl⟩ : syracuseStep 1276739 = 1915109) B1915109
theorem B850769 : Blo 566810 850769 := bstep (se 2 (by rfl) ⟨319038, by rfl⟩ : syracuseStep 850769 = 638077) B638077
theorem B850787 : Blo 566810 850787 := bstep (se 1 (by rfl) ⟨638090, by rfl⟩ : syracuseStep 850787 = 1276181) B1276181
theorem B1211249 : Blo 566810 1211249 := bstep (se 2 (by rfl) ⟨454218, by rfl⟩ : syracuseStep 1211249 = 908437) B908437
theorem B1440625 : Blo 566810 1440625 := bstep (se 2 (by rfl) ⟨540234, by rfl⟩ : syracuseStep 1440625 = 1080469) B1080469
theorem B850817 : Blo 566810 850817 := bstep (se 2 (by rfl) ⟨319056, by rfl⟩ : syracuseStep 850817 = 638113) B638113
theorem B850835 : Blo 566810 850835 := bstep (se 1 (by rfl) ⟨638126, by rfl⟩ : syracuseStep 850835 = 1276253) B1276253
theorem B850865 : Blo 566810 850865 := bstep (se 2 (by rfl) ⟨319074, by rfl⟩ : syracuseStep 850865 = 638149) B638149
theorem B850883 : Blo 566810 850883 := bstep (se 1 (by rfl) ⟨638162, by rfl⟩ : syracuseStep 850883 = 1276325) B1276325
theorem B850913 : Blo 566810 850913 := bstep (se 2 (by rfl) ⟨319092, by rfl⟩ : syracuseStep 850913 = 638185) B638185
theorem B1539053 : Blo 566810 1539053 := bstep (se 3 (by rfl) ⟨288572, by rfl⟩ : syracuseStep 1539053 = 577145) B577145
theorem B850931 : Blo 566810 850931 := bstep (se 1 (by rfl) ⟨638198, by rfl⟩ : syracuseStep 850931 = 1276397) B1276397
theorem B2587661 : Blo 566810 2587661 := bstep (se 3 (by rfl) ⟨485186, by rfl⟩ : syracuseStep 2587661 = 970373) B970373
theorem B850961 : Blo 566810 850961 := bstep (se 2 (by rfl) ⟨319110, by rfl⟩ : syracuseStep 850961 = 638221) B638221
theorem B850979 : Blo 566810 850979 := bstep (se 1 (by rfl) ⟨638234, by rfl⟩ : syracuseStep 850979 = 1276469) B1276469
theorem B1735715 : Blo 566810 1735715 := bstep (se 1 (by rfl) ⟨1301786, by rfl⟩ : syracuseStep 1735715 = 2603573) B2603573
theorem B719923 : Blo 566810 719923 := bstep (se 1 (by rfl) ⟨539942, by rfl⟩ : syracuseStep 719923 = 1079885) B1079885
theorem B851009 : Blo 566810 851009 := bstep (se 2 (by rfl) ⟨319128, by rfl⟩ : syracuseStep 851009 = 638257) B638257
theorem B1277009 : Blo 566810 1277009 := bstep (se 2 (by rfl) ⟨478878, by rfl⟩ : syracuseStep 1277009 = 957757) B957757
theorem B851027 : Blo 566810 851027 := bstep (se 1 (by rfl) ⟨638270, by rfl⟩ : syracuseStep 851027 = 1276541) B1276541
theorem B1277027 : Blo 566810 1277027 := bstep (se 1 (by rfl) ⟨957770, by rfl⟩ : syracuseStep 1277027 = 1915541) B1915541
theorem B851057 : Blo 566810 851057 := bstep (se 2 (by rfl) ⟨319146, by rfl⟩ : syracuseStep 851057 = 638293) B638293
theorem B851075 : Blo 566810 851075 := bstep (se 1 (by rfl) ⟨638306, by rfl⟩ : syracuseStep 851075 = 1276613) B1276613
theorem B1440899 : Blo 566810 1440899 := bstep (se 1 (by rfl) ⟨1080674, by rfl⟩ : syracuseStep 1440899 = 2161349) B2161349
theorem B720019 : Blo 566810 720019 := bstep (se 1 (by rfl) ⟨540014, by rfl⟩ : syracuseStep 720019 = 1080029) B1080029
theorem B851105 : Blo 566810 851105 := bstep (se 2 (by rfl) ⟨319164, by rfl⟩ : syracuseStep 851105 = 638329) B638329
theorem B3243185 : Blo 566810 3243185 := bstep (se 2 (by rfl) ⟨1216194, by rfl⟩ : syracuseStep 3243185 = 2432389) B2432389
theorem B851123 : Blo 566810 851123 := bstep (se 1 (by rfl) ⟨638342, by rfl⟩ : syracuseStep 851123 = 1276685) B1276685
theorem B1080515 : Blo 566810 1080515 := bstep (se 1 (by rfl) ⟨810386, by rfl⟩ : syracuseStep 1080515 = 1620773) B1620773
theorem B851153 : Blo 566810 851153 := bstep (se 2 (by rfl) ⟨319182, by rfl⟩ : syracuseStep 851153 = 638365) B638365
theorem B55934165 : Blo 566810 55934165 := bstep (se 7 (by rfl) ⟨655478, by rfl⟩ : syracuseStep 55934165 = 1310957) B1310957
theorem B851171 : Blo 566810 851171 := bstep (se 1 (by rfl) ⟨638378, by rfl⟩ : syracuseStep 851171 = 1276757) B1276757
theorem B851201 : Blo 566810 851201 := bstep (se 2 (by rfl) ⟨319200, by rfl⟩ : syracuseStep 851201 = 638401) B638401
theorem B3702029 : Blo 566810 3702029 := bstep (se 3 (by rfl) ⟨694130, by rfl⟩ : syracuseStep 3702029 = 1388261) B1388261
theorem B851219 : Blo 566810 851219 := bstep (se 1 (by rfl) ⟨638414, by rfl⟩ : syracuseStep 851219 = 1276829) B1276829
theorem B851249 : Blo 566810 851249 := bstep (se 2 (by rfl) ⟨319218, by rfl⟩ : syracuseStep 851249 = 638437) B638437
theorem B851267 : Blo 566810 851267 := bstep (se 1 (by rfl) ⟨638450, by rfl⟩ : syracuseStep 851267 = 1276901) B1276901
theorem B1441091 : Blo 566810 1441091 := bstep (se 1 (by rfl) ⟨1080818, by rfl⟩ : syracuseStep 1441091 = 2161637) B2161637
theorem B851297 : Blo 566810 851297 := bstep (se 2 (by rfl) ⟨319236, by rfl⟩ : syracuseStep 851297 = 638473) B638473
theorem B1277297 : Blo 566810 1277297 := bstep (se 2 (by rfl) ⟨478986, by rfl⟩ : syracuseStep 1277297 = 957973) B957973
theorem B851315 : Blo 566810 851315 := bstep (se 1 (by rfl) ⟨638486, by rfl⟩ : syracuseStep 851315 = 1276973) B1276973
theorem B1277315 : Blo 566810 1277315 := bstep (se 1 (by rfl) ⟨957986, by rfl⟩ : syracuseStep 1277315 = 1915973) B1915973
theorem B851345 : Blo 566810 851345 := bstep (se 2 (by rfl) ⟨319254, by rfl⟩ : syracuseStep 851345 = 638509) B638509
theorem B851363 : Blo 566810 851363 := bstep (se 1 (by rfl) ⟨638522, by rfl⟩ : syracuseStep 851363 = 1277045) B1277045
theorem B851393 : Blo 566810 851393 := bstep (se 2 (by rfl) ⟨319272, by rfl⟩ : syracuseStep 851393 = 638545) B638545
theorem B851411 : Blo 566810 851411 := bstep (se 1 (by rfl) ⟨638558, by rfl⟩ : syracuseStep 851411 = 1277117) B1277117
theorem B1080803 : Blo 566810 1080803 := bstep (se 1 (by rfl) ⟨810602, by rfl⟩ : syracuseStep 1080803 = 1621205) B1621205
theorem B851441 : Blo 566810 851441 := bstep (se 2 (by rfl) ⟨319290, by rfl⟩ : syracuseStep 851441 = 638581) B638581
theorem B851459 : Blo 566810 851459 := bstep (se 1 (by rfl) ⟨638594, by rfl⟩ : syracuseStep 851459 = 1277189) B1277189
theorem B851489 : Blo 566810 851489 := bstep (se 2 (by rfl) ⟨319308, by rfl⟩ : syracuseStep 851489 = 638617) B638617
theorem B851507 : Blo 566810 851507 := bstep (se 1 (by rfl) ⟨638630, by rfl⟩ : syracuseStep 851507 = 1277261) B1277261
theorem B851537 : Blo 566810 851537 := bstep (se 2 (by rfl) ⟨319326, by rfl⟩ : syracuseStep 851537 = 638653) B638653
theorem B851555 : Blo 566810 851555 := bstep (se 1 (by rfl) ⟨638666, by rfl⟩ : syracuseStep 851555 = 1277333) B1277333
theorem B851585 : Blo 566810 851585 := bstep (se 2 (by rfl) ⟨319344, by rfl⟩ : syracuseStep 851585 = 638689) B638689
theorem B720515 : Blo 566810 720515 := bstep (se 1 (by rfl) ⟨540386, by rfl⟩ : syracuseStep 720515 = 1080773) B1080773
theorem B1277585 : Blo 566810 1277585 := bstep (se 2 (by rfl) ⟨479094, by rfl⟩ : syracuseStep 1277585 = 958189) B958189
theorem B851603 : Blo 566810 851603 := bstep (se 1 (by rfl) ⟨638702, by rfl⟩ : syracuseStep 851603 = 1277405) B1277405
theorem B3636899 : Blo 566810 3636899 := bstep (se 1 (by rfl) ⟨2727674, by rfl⟩ : syracuseStep 3636899 = 5455349) B5455349
theorem B1277603 : Blo 566810 1277603 := bstep (se 1 (by rfl) ⟨958202, by rfl⟩ : syracuseStep 1277603 = 1916405) B1916405
theorem B851633 : Blo 566810 851633 := bstep (se 2 (by rfl) ⟨319362, by rfl⟩ : syracuseStep 851633 = 638725) B638725
theorem B851651 : Blo 566810 851651 := bstep (se 1 (by rfl) ⟨638738, by rfl⟩ : syracuseStep 851651 = 1277477) B1277477
theorem B851681 : Blo 566810 851681 := bstep (se 2 (by rfl) ⟨319380, by rfl⟩ : syracuseStep 851681 = 638761) B638761
theorem B818915 : Blo 566810 818915 := bstep (se 1 (by rfl) ⟨614186, by rfl⟩ : syracuseStep 818915 = 1228373) B1228373
theorem B851699 : Blo 566810 851699 := bstep (se 1 (by rfl) ⟨638774, by rfl⟩ : syracuseStep 851699 = 1277549) B1277549
theorem B851729 : Blo 566810 851729 := bstep (se 2 (by rfl) ⟨319398, by rfl⟩ : syracuseStep 851729 = 638797) B638797
theorem B851747 : Blo 566810 851747 := bstep (se 1 (by rfl) ⟨638810, by rfl⟩ : syracuseStep 851747 = 1277621) B1277621
theorem B851777 : Blo 566810 851777 := bstep (se 2 (by rfl) ⟨319416, by rfl⟩ : syracuseStep 851777 = 638833) B638833
theorem B851795 : Blo 566810 851795 := bstep (se 1 (by rfl) ⟨638846, by rfl⟩ : syracuseStep 851795 = 1277693) B1277693
theorem B851825 : Blo 566810 851825 := bstep (se 2 (by rfl) ⟨319434, by rfl⟩ : syracuseStep 851825 = 638869) B638869
theorem B851843 : Blo 566810 851843 := bstep (se 1 (by rfl) ⟨638882, by rfl⟩ : syracuseStep 851843 = 1277765) B1277765
theorem B851873 : Blo 566810 851873 := bstep (se 2 (by rfl) ⟨319452, by rfl⟩ : syracuseStep 851873 = 638905) B638905
theorem B1277873 : Blo 566810 1277873 := bstep (se 2 (by rfl) ⟨479202, by rfl⟩ : syracuseStep 1277873 = 958405) B958405
theorem B2162609 : Blo 566810 2162609 := bstep (se 2 (by rfl) ⟨810978, by rfl⟩ : syracuseStep 2162609 = 1621957) B1621957
theorem B851891 : Blo 566810 851891 := bstep (se 1 (by rfl) ⟨638918, by rfl⟩ : syracuseStep 851891 = 1277837) B1277837
theorem B1277891 : Blo 566810 1277891 := bstep (se 1 (by rfl) ⟨958418, by rfl⟩ : syracuseStep 1277891 = 1916837) B1916837
theorem B851921 : Blo 566810 851921 := bstep (se 2 (by rfl) ⟨319470, by rfl⟩ : syracuseStep 851921 = 638941) B638941
theorem B851939 : Blo 566810 851939 := bstep (se 1 (by rfl) ⟨638954, by rfl⟩ : syracuseStep 851939 = 1277909) B1277909
theorem B1277963 : Blo 566810 1277963 := bstep (se 1 (by rfl) ⟨958472, by rfl⟩ : syracuseStep 1277963 = 1916945) B1916945
theorem B851993 : Blo 566810 851993 := bstep (se 2 (by rfl) ⟨319497, by rfl⟩ : syracuseStep 851993 = 638995) B638995
theorem B6488099 : Blo 566810 6488099 := bstep (se 1 (by rfl) ⟨4866074, by rfl⟩ : syracuseStep 6488099 = 9732149) B9732149
theorem B1278017 : Blo 566810 1278017 := bstep (se 2 (by rfl) ⟨479256, by rfl⟩ : syracuseStep 1278017 = 958513) B958513
theorem B852107 : Blo 566810 852107 := bstep (se 1 (by rfl) ⟨639080, by rfl⟩ : syracuseStep 852107 = 1278161) B1278161
theorem B852119 : Blo 566810 852119 := bstep (se 1 (by rfl) ⟨639089, by rfl⟩ : syracuseStep 852119 = 1278179) B1278179
theorem B3244211 : Blo 566810 3244211 := bstep (se 1 (by rfl) ⟨2433158, by rfl⟩ : syracuseStep 3244211 = 4866317) B4866317
theorem B852185 : Blo 566810 852185 := bstep (se 2 (by rfl) ⟨319569, by rfl⟩ : syracuseStep 852185 = 639139) B639139
theorem B4391129 : Blo 566810 4391129 := bstep (se 2 (by rfl) ⟨1646673, by rfl⟩ : syracuseStep 4391129 = 3293347) B3293347
theorem B721163 : Blo 566810 721163 := bstep (se 1 (by rfl) ⟨540872, by rfl⟩ : syracuseStep 721163 = 1081745) B1081745
theorem B1278233 : Blo 566810 1278233 := bstep (se 2 (by rfl) ⟨479337, by rfl⟩ : syracuseStep 1278233 = 958675) B958675
theorem B852299 : Blo 566810 852299 := bstep (se 1 (by rfl) ⟨639224, by rfl⟩ : syracuseStep 852299 = 1278449) B1278449
theorem B852311 : Blo 566810 852311 := bstep (se 1 (by rfl) ⟨639233, by rfl⟩ : syracuseStep 852311 = 1278467) B1278467
theorem B1278323 : Blo 566810 1278323 := bstep (se 1 (by rfl) ⟨958742, by rfl⟩ : syracuseStep 1278323 = 1917485) B1917485
theorem B1278359 : Blo 566810 1278359 := bstep (se 1 (by rfl) ⟨958769, by rfl⟩ : syracuseStep 1278359 = 1917539) B1917539
theorem B2163095 : Blo 566810 2163095 := bstep (se 1 (by rfl) ⟨1622321, by rfl⟩ : syracuseStep 2163095 = 3244643) B3244643
theorem B852377 : Blo 566810 852377 := bstep (se 2 (by rfl) ⟨319641, by rfl⟩ : syracuseStep 852377 = 639283) B639283
theorem B1311191 : Blo 566810 1311191 := bstep (se 1 (by rfl) ⟨983393, by rfl⟩ : syracuseStep 1311191 = 1966787) B1966787
theorem B1212889 : Blo 566810 1212889 := bstep (se 2 (by rfl) ⟨454833, by rfl⟩ : syracuseStep 1212889 = 909667) B909667
theorem B852491 : Blo 566810 852491 := bstep (se 1 (by rfl) ⟨639368, by rfl⟩ : syracuseStep 852491 = 1278737) B1278737
theorem B852503 : Blo 566810 852503 := bstep (se 1 (by rfl) ⟨639377, by rfl⟩ : syracuseStep 852503 = 1278755) B1278755
theorem B1278539 : Blo 566810 1278539 := bstep (se 1 (by rfl) ⟨958904, by rfl⟩ : syracuseStep 1278539 = 1917809) B1917809
theorem B852569 : Blo 566810 852569 := bstep (se 2 (by rfl) ⟨319713, by rfl⟩ : syracuseStep 852569 = 639427) B639427
theorem B2163293 : Blo 566810 2163293 := bstep (se 3 (by rfl) ⟨405617, by rfl⟩ : syracuseStep 2163293 = 811235) B811235
theorem B1278593 : Blo 566810 1278593 := bstep (se 2 (by rfl) ⟨479472, by rfl⟩ : syracuseStep 1278593 = 958945) B958945
theorem B2884247 : Blo 566810 2884247 := bstep (se 1 (by rfl) ⟨2163185, by rfl⟩ : syracuseStep 2884247 = 4326371) B4326371
theorem B852683 : Blo 566810 852683 := bstep (se 1 (by rfl) ⟨639512, by rfl⟩ : syracuseStep 852683 = 1279025) B1279025
theorem B852695 : Blo 566810 852695 := bstep (se 1 (by rfl) ⟨639521, by rfl⟩ : syracuseStep 852695 = 1279043) B1279043
theorem B852761 : Blo 566810 852761 := bstep (se 2 (by rfl) ⟨319785, by rfl⟩ : syracuseStep 852761 = 639571) B639571
theorem B7275329 : Blo 566810 7275329 := bstep (se 2 (by rfl) ⟨2728248, by rfl⟩ : syracuseStep 7275329 = 5456497) B5456497
theorem B1278809 : Blo 566810 1278809 := bstep (se 2 (by rfl) ⟨479553, by rfl⟩ : syracuseStep 1278809 = 959107) B959107
theorem B852875 : Blo 566810 852875 := bstep (se 1 (by rfl) ⟨639656, by rfl⟩ : syracuseStep 852875 = 1279313) B1279313
theorem B852887 : Blo 566810 852887 := bstep (se 1 (by rfl) ⟨639665, by rfl⟩ : syracuseStep 852887 = 1279331) B1279331
theorem B1442711 : Blo 566810 1442711 := bstep (se 1 (by rfl) ⟨1082033, by rfl⟩ : syracuseStep 1442711 = 2164067) B2164067
theorem B1278899 : Blo 566810 1278899 := bstep (se 1 (by rfl) ⟨959174, by rfl⟩ : syracuseStep 1278899 = 1918349) B1918349
theorem B1082315 : Blo 566810 1082315 := bstep (se 1 (by rfl) ⟨811736, by rfl⟩ : syracuseStep 1082315 = 1623473) B1623473
theorem B721867 : Blo 566810 721867 := bstep (se 1 (by rfl) ⟨541400, by rfl⟩ : syracuseStep 721867 = 1082801) B1082801
theorem B1278935 : Blo 566810 1278935 := bstep (se 1 (by rfl) ⟨959201, by rfl⟩ : syracuseStep 1278935 = 1918403) B1918403
theorem B852953 : Blo 566810 852953 := bstep (se 2 (by rfl) ⟨319857, by rfl⟩ : syracuseStep 852953 = 639715) B639715
theorem B853067 : Blo 566810 853067 := bstep (se 1 (by rfl) ⟨639800, by rfl⟩ : syracuseStep 853067 = 1279601) B1279601
theorem B853079 : Blo 566810 853079 := bstep (se 1 (by rfl) ⟨639809, by rfl⟩ : syracuseStep 853079 = 1279619) B1279619
theorem B1082497 : Blo 566810 1082497 := bstep (se 2 (by rfl) ⟨405936, by rfl⟩ : syracuseStep 1082497 = 811873) B811873
theorem B1279115 : Blo 566810 1279115 := bstep (se 1 (by rfl) ⟨959336, by rfl⟩ : syracuseStep 1279115 = 1918673) B1918673
theorem B4752535 : Blo 566810 4752535 := bstep (se 1 (by rfl) ⟨3564401, by rfl⟩ : syracuseStep 4752535 = 7128803) B7128803
theorem B853145 : Blo 566810 853145 := bstep (se 2 (by rfl) ⟨319929, by rfl⟩ : syracuseStep 853145 = 639859) B639859
theorem B13173941 : Blo 566810 13173941 := bstep (se 5 (by rfl) ⟨617528, by rfl⟩ : syracuseStep 13173941 = 1235057) B1235057
theorem B1279169 : Blo 566810 1279169 := bstep (se 2 (by rfl) ⟨479688, by rfl⟩ : syracuseStep 1279169 = 959377) B959377
theorem B722135 : Blo 566810 722135 := bstep (se 1 (by rfl) ⟨541601, by rfl⟩ : syracuseStep 722135 = 1083203) B1083203
theorem B853259 : Blo 566810 853259 := bstep (se 1 (by rfl) ⟨639944, by rfl⟩ : syracuseStep 853259 = 1279889) B1279889
theorem B853271 : Blo 566810 853271 := bstep (se 1 (by rfl) ⟨639953, by rfl⟩ : syracuseStep 853271 = 1279907) B1279907
theorem B853337 : Blo 566810 853337 := bstep (se 2 (by rfl) ⟨320001, by rfl⟩ : syracuseStep 853337 = 640003) B640003
theorem B1279385 : Blo 566810 1279385 := bstep (se 2 (by rfl) ⟨479769, by rfl⟩ : syracuseStep 1279385 = 959539) B959539
theorem B853451 : Blo 566810 853451 := bstep (se 1 (by rfl) ⟨640088, by rfl⟩ : syracuseStep 853451 = 1280177) B1280177
theorem B853463 : Blo 566810 853463 := bstep (se 1 (by rfl) ⟨640097, by rfl⟩ : syracuseStep 853463 = 1280195) B1280195
theorem B1279475 : Blo 566810 1279475 := bstep (se 1 (by rfl) ⟨959606, by rfl⟩ : syracuseStep 1279475 = 1919213) B1919213
theorem B4916753 : Blo 566810 4916753 := bstep (se 2 (by rfl) ⟨1843782, by rfl⟩ : syracuseStep 4916753 = 3687565) B3687565
theorem B1279511 : Blo 566810 1279511 := bstep (se 1 (by rfl) ⟨959633, by rfl⟩ : syracuseStep 1279511 = 1919267) B1919267
theorem B853529 : Blo 566810 853529 := bstep (se 2 (by rfl) ⟨320073, by rfl⟩ : syracuseStep 853529 = 640147) B640147
theorem B1443379 : Blo 566810 1443379 := bstep (se 1 (by rfl) ⟨1082534, by rfl⟩ : syracuseStep 1443379 = 2165069) B2165069
theorem B1082945 : Blo 566810 1082945 := bstep (se 2 (by rfl) ⟨406104, by rfl⟩ : syracuseStep 1082945 = 812209) B812209
theorem B3245669 : Blo 566810 3245669 := bstep (se 4 (by rfl) ⟨304281, by rfl⟩ : syracuseStep 3245669 = 608563) B608563
theorem B853643 : Blo 566810 853643 := bstep (se 1 (by rfl) ⟨640232, by rfl⟩ : syracuseStep 853643 = 1280465) B1280465
theorem B853655 : Blo 566810 853655 := bstep (se 1 (by rfl) ⟨640241, by rfl⟩ : syracuseStep 853655 = 1280483) B1280483
theorem B1443521 : Blo 566810 1443521 := bstep (se 2 (by rfl) ⟨541320, by rfl⟩ : syracuseStep 1443521 = 1082641) B1082641
theorem B1279691 : Blo 566810 1279691 := bstep (se 1 (by rfl) ⟨959768, by rfl⟩ : syracuseStep 1279691 = 1919537) B1919537
theorem B853721 : Blo 566810 853721 := bstep (se 2 (by rfl) ⟨320145, by rfl⟩ : syracuseStep 853721 = 640291) B640291
theorem B1214195 : Blo 566810 1214195 := bstep (se 1 (by rfl) ⟨910646, by rfl⟩ : syracuseStep 1214195 = 1821293) B1821293
theorem B1279745 : Blo 566810 1279745 := bstep (se 2 (by rfl) ⟨479904, by rfl⟩ : syracuseStep 1279745 = 959809) B959809
theorem B853835 : Blo 566810 853835 := bstep (se 1 (by rfl) ⟨640376, by rfl⟩ : syracuseStep 853835 = 1280753) B1280753
theorem B3901259 : Blo 566810 3901259 := bstep (se 1 (by rfl) ⟨2925944, by rfl⟩ : syracuseStep 3901259 = 5851889) B5851889
theorem B853847 : Blo 566810 853847 := bstep (se 1 (by rfl) ⟨640385, by rfl⟩ : syracuseStep 853847 = 1280771) B1280771
theorem B1083287 : Blo 566810 1083287 := bstep (se 1 (by rfl) ⟨812465, by rfl⟩ : syracuseStep 1083287 = 1624931) B1624931
theorem B853913 : Blo 566810 853913 := bstep (se 2 (by rfl) ⟨320217, by rfl⟩ : syracuseStep 853913 = 640435) B640435
theorem B15599537 : Blo 566810 15599537 := bstep (se 2 (by rfl) ⟨5849826, by rfl⟩ : syracuseStep 15599537 = 11699653) B11699653
theorem B1279961 : Blo 566810 1279961 := bstep (se 2 (by rfl) ⟨479985, by rfl⟩ : syracuseStep 1279961 = 959971) B959971
theorem B854027 : Blo 566810 854027 := bstep (se 1 (by rfl) ⟨640520, by rfl⟩ : syracuseStep 854027 = 1281041) B1281041
theorem B854039 : Blo 566810 854039 := bstep (se 1 (by rfl) ⟨640529, by rfl⟩ : syracuseStep 854039 = 1281059) B1281059
theorem B1280051 : Blo 566810 1280051 := bstep (se 1 (by rfl) ⟨960038, by rfl⟩ : syracuseStep 1280051 = 1920077) B1920077
theorem B1280087 : Blo 566810 1280087 := bstep (se 1 (by rfl) ⟨960065, by rfl⟩ : syracuseStep 1280087 = 1920131) B1920131
theorem B854105 : Blo 566810 854105 := bstep (se 2 (by rfl) ⟨320289, by rfl⟩ : syracuseStep 854105 = 640579) B640579
theorem B854219 : Blo 566810 854219 := bstep (se 1 (by rfl) ⟨640664, by rfl⟩ : syracuseStep 854219 = 1281329) B1281329
theorem B854231 : Blo 566810 854231 := bstep (se 1 (by rfl) ⟨640673, by rfl⟩ : syracuseStep 854231 = 1281347) B1281347
theorem B1280267 : Blo 566810 1280267 := bstep (se 1 (by rfl) ⟨960200, by rfl⟩ : syracuseStep 1280267 = 1920401) B1920401
theorem B854297 : Blo 566810 854297 := bstep (se 2 (by rfl) ⟨320361, by rfl⟩ : syracuseStep 854297 = 640723) B640723
theorem B1280321 : Blo 566810 1280321 := bstep (se 2 (by rfl) ⟨480120, by rfl⟩ : syracuseStep 1280321 = 960241) B960241
theorem B854411 : Blo 566810 854411 := bstep (se 1 (by rfl) ⟨640808, by rfl⟩ : syracuseStep 854411 = 1281617) B1281617
theorem B854423 : Blo 566810 854423 := bstep (se 1 (by rfl) ⟨640817, by rfl⟩ : syracuseStep 854423 = 1281635) B1281635
theorem B854489 : Blo 566810 854489 := bstep (se 2 (by rfl) ⟨320433, by rfl⟩ : syracuseStep 854489 = 640867) B640867
theorem B2165251 : Blo 566810 2165251 := bstep (se 1 (by rfl) ⟨1623938, by rfl⟩ : syracuseStep 2165251 = 3247877) B3247877
theorem B1280537 : Blo 566810 1280537 := bstep (se 2 (by rfl) ⟨480201, by rfl⟩ : syracuseStep 1280537 = 960403) B960403
theorem B1542707 : Blo 566810 1542707 := bstep (se 1 (by rfl) ⟨1157030, by rfl⟩ : syracuseStep 1542707 = 2314061) B2314061
theorem B2591297 : Blo 566810 2591297 := bstep (se 2 (by rfl) ⟨971736, by rfl⟩ : syracuseStep 2591297 = 1943473) B1943473
theorem B854603 : Blo 566810 854603 := bstep (se 1 (by rfl) ⟨640952, by rfl⟩ : syracuseStep 854603 = 1281905) B1281905
theorem B854615 : Blo 566810 854615 := bstep (se 1 (by rfl) ⟨640961, by rfl⟩ : syracuseStep 854615 = 1281923) B1281923
theorem B4393565 : Blo 566810 4393565 := bstep (se 3 (by rfl) ⟨823793, by rfl⟩ : syracuseStep 4393565 = 1647587) B1647587
theorem B1280627 : Blo 566810 1280627 := bstep (se 1 (by rfl) ⟨960470, by rfl⟩ : syracuseStep 1280627 = 1920941) B1920941
theorem B1280663 : Blo 566810 1280663 := bstep (se 1 (by rfl) ⟨960497, by rfl⟩ : syracuseStep 1280663 = 1920995) B1920995
theorem B854681 : Blo 566810 854681 := bstep (se 2 (by rfl) ⟨320505, by rfl⟩ : syracuseStep 854681 = 641011) B641011
theorem B854795 : Blo 566810 854795 := bstep (se 1 (by rfl) ⟨641096, by rfl⟩ : syracuseStep 854795 = 1282193) B1282193
theorem B4098833 : Blo 566810 4098833 := bstep (se 2 (by rfl) ⟨1537062, by rfl⟩ : syracuseStep 4098833 = 3074125) B3074125
theorem B854807 : Blo 566810 854807 := bstep (se 1 (by rfl) ⟨641105, by rfl⟩ : syracuseStep 854807 = 1282211) B1282211
theorem B2165555 : Blo 566810 2165555 := bstep (se 1 (by rfl) ⟨1624166, by rfl⟩ : syracuseStep 2165555 = 3248333) B3248333
theorem B1280843 : Blo 566810 1280843 := bstep (se 1 (by rfl) ⟨960632, by rfl⟩ : syracuseStep 1280843 = 1921265) B1921265
theorem B854873 : Blo 566810 854873 := bstep (se 2 (by rfl) ⟨320577, by rfl⟩ : syracuseStep 854873 = 641155) B641155
theorem B1280897 : Blo 566810 1280897 := bstep (se 2 (by rfl) ⟨480336, by rfl⟩ : syracuseStep 1280897 = 960673) B960673
theorem B920473 : Blo 566810 920473 := bstep (se 2 (by rfl) ⟨345177, by rfl⟩ : syracuseStep 920473 = 690355) B690355
theorem B1444787 : Blo 566810 1444787 := bstep (se 1 (by rfl) ⟨1083590, by rfl⟩ : syracuseStep 1444787 = 2167181) B2167181
theorem B854987 : Blo 566810 854987 := bstep (se 1 (by rfl) ⟨641240, by rfl⟩ : syracuseStep 854987 = 1282481) B1282481
theorem B854999 : Blo 566810 854999 := bstep (se 1 (by rfl) ⟨641249, by rfl⟩ : syracuseStep 854999 = 1282499) B1282499
theorem B855065 : Blo 566810 855065 := bstep (se 2 (by rfl) ⟨320649, by rfl⟩ : syracuseStep 855065 = 641299) B641299
theorem B1281113 : Blo 566810 1281113 := bstep (se 2 (by rfl) ⟨480417, by rfl⟩ : syracuseStep 1281113 = 960835) B960835
theorem B855179 : Blo 566810 855179 := bstep (se 1 (by rfl) ⟨641384, by rfl⟩ : syracuseStep 855179 = 1282769) B1282769
theorem B2428049 : Blo 566810 2428049 := bstep (se 2 (by rfl) ⟨910518, by rfl⟩ : syracuseStep 2428049 = 1821037) B1821037
theorem B855191 : Blo 566810 855191 := bstep (se 1 (by rfl) ⟨641393, by rfl⟩ : syracuseStep 855191 = 1282787) B1282787
theorem B1281203 : Blo 566810 1281203 := bstep (se 1 (by rfl) ⟨960902, by rfl⟩ : syracuseStep 1281203 = 1921805) B1921805
theorem B1281239 : Blo 566810 1281239 := bstep (se 1 (by rfl) ⟨960929, by rfl⟩ : syracuseStep 1281239 = 1921859) B1921859
theorem B855257 : Blo 566810 855257 := bstep (se 2 (by rfl) ⟨320721, by rfl⟩ : syracuseStep 855257 = 641443) B641443
theorem B1215767 : Blo 566810 1215767 := bstep (se 1 (by rfl) ⟨911825, by rfl⟩ : syracuseStep 1215767 = 1823651) B1823651
theorem B855371 : Blo 566810 855371 := bstep (se 1 (by rfl) ⟨641528, by rfl⟩ : syracuseStep 855371 = 1283057) B1283057
theorem B855383 : Blo 566810 855383 := bstep (se 1 (by rfl) ⟨641537, by rfl⟩ : syracuseStep 855383 = 1283075) B1283075
theorem B1281419 : Blo 566810 1281419 := bstep (se 1 (by rfl) ⟨961064, by rfl⟩ : syracuseStep 1281419 = 1922129) B1922129
theorem B855449 : Blo 566810 855449 := bstep (se 2 (by rfl) ⟨320793, by rfl⟩ : syracuseStep 855449 = 641587) B641587
theorem B1281473 : Blo 566810 1281473 := bstep (se 2 (by rfl) ⟨480552, by rfl⟩ : syracuseStep 1281473 = 961105) B961105
theorem B2166209 : Blo 566810 2166209 := bstep (se 2 (by rfl) ⟨812328, by rfl⟩ : syracuseStep 2166209 = 1624657) B1624657
theorem B855563 : Blo 566810 855563 := bstep (se 1 (by rfl) ⟨641672, by rfl⟩ : syracuseStep 855563 = 1283345) B1283345
theorem B855575 : Blo 566810 855575 := bstep (se 1 (by rfl) ⟨641681, by rfl⟩ : syracuseStep 855575 = 1283363) B1283363
theorem B1216075 : Blo 566810 1216075 := bstep (se 1 (by rfl) ⟨912056, by rfl⟩ : syracuseStep 1216075 = 1824113) B1824113
theorem B855641 : Blo 566810 855641 := bstep (se 2 (by rfl) ⟨320865, by rfl⟩ : syracuseStep 855641 = 641731) B641731
theorem B1281689 : Blo 566810 1281689 := bstep (se 2 (by rfl) ⟨480633, by rfl⟩ : syracuseStep 1281689 = 961267) B961267
theorem B855755 : Blo 566810 855755 := bstep (se 1 (by rfl) ⟨641816, by rfl⟩ : syracuseStep 855755 = 1283633) B1283633
theorem B855767 : Blo 566810 855767 := bstep (se 1 (by rfl) ⟨641825, by rfl⟩ : syracuseStep 855767 = 1283651) B1283651
theorem B1281779 : Blo 566810 1281779 := bstep (se 1 (by rfl) ⟨961334, by rfl⟩ : syracuseStep 1281779 = 1922669) B1922669
theorem B1281815 : Blo 566810 1281815 := bstep (se 1 (by rfl) ⟨961361, by rfl⟩ : syracuseStep 1281815 = 1922723) B1922723
theorem B855833 : Blo 566810 855833 := bstep (se 2 (by rfl) ⟨320937, by rfl⟩ : syracuseStep 855833 = 641875) B641875
theorem B5246795 : Blo 566810 5246795 := bstep (se 1 (by rfl) ⟨3935096, by rfl⟩ : syracuseStep 5246795 = 7870193) B7870193
theorem B855947 : Blo 566810 855947 := bstep (se 1 (by rfl) ⟨641960, by rfl⟩ : syracuseStep 855947 = 1283921) B1283921
theorem B855959 : Blo 566810 855959 := bstep (se 1 (by rfl) ⟨641969, by rfl⟩ : syracuseStep 855959 = 1283939) B1283939
theorem B1281995 : Blo 566810 1281995 := bstep (se 1 (by rfl) ⟨961496, by rfl⟩ : syracuseStep 1281995 = 1922993) B1922993
theorem B856025 : Blo 566810 856025 := bstep (se 2 (by rfl) ⟨321009, by rfl⟩ : syracuseStep 856025 = 642019) B642019
theorem B1282049 : Blo 566810 1282049 := bstep (se 2 (by rfl) ⟨480768, by rfl⟩ : syracuseStep 1282049 = 961537) B961537
theorem B2428973 : Blo 566810 2428973 := bstep (se 3 (by rfl) ⟨455432, by rfl⟩ : syracuseStep 2428973 = 910865) B910865
theorem B856139 : Blo 566810 856139 := bstep (se 1 (by rfl) ⟨642104, by rfl⟩ : syracuseStep 856139 = 1284209) B1284209
theorem B856151 : Blo 566810 856151 := bstep (se 1 (by rfl) ⟨642113, by rfl⟩ : syracuseStep 856151 = 1284227) B1284227
theorem B2887811 : Blo 566810 2887811 := bstep (se 1 (by rfl) ⟨2165858, by rfl⟩ : syracuseStep 2887811 = 4331717) B4331717
theorem B3641561 : Blo 566810 3641561 := bstep (se 2 (by rfl) ⟨1365585, by rfl⟩ : syracuseStep 3641561 = 2731171) B2731171
theorem B1282265 : Blo 566810 1282265 := bstep (se 2 (by rfl) ⟨480849, by rfl⟩ : syracuseStep 1282265 = 961699) B961699
theorem B4329773 : Blo 566810 4329773 := bstep (se 3 (by rfl) ⟨811832, by rfl⟩ : syracuseStep 4329773 = 1623665) B1623665
theorem B1282355 : Blo 566810 1282355 := bstep (se 1 (by rfl) ⟨961766, by rfl⟩ : syracuseStep 1282355 = 1923533) B1923533
theorem B1282391 : Blo 566810 1282391 := bstep (se 1 (by rfl) ⟨961793, by rfl⟩ : syracuseStep 1282391 = 1923587) B1923587
theorem B1151435 : Blo 566810 1151435 := bstep (se 1 (by rfl) ⟨863576, by rfl⟩ : syracuseStep 1151435 = 1727153) B1727153
theorem B1282571 : Blo 566810 1282571 := bstep (se 1 (by rfl) ⟨961928, by rfl⟩ : syracuseStep 1282571 = 1923857) B1923857
theorem B1282625 : Blo 566810 1282625 := bstep (se 2 (by rfl) ⟨480984, by rfl⟩ : syracuseStep 1282625 = 961969) B961969
theorem B9966341 : Blo 566810 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B1217305 : Blo 566810 1217305 := bstep (se 2 (by rfl) ⟨456489, by rfl⟩ : syracuseStep 1217305 = 912979) B912979
theorem B1282841 : Blo 566810 1282841 := bstep (se 2 (by rfl) ⟨481065, by rfl⟩ : syracuseStep 1282841 = 962131) B962131
theorem B4854593 : Blo 566810 4854593 := bstep (se 2 (by rfl) ⟨1820472, by rfl⟩ : syracuseStep 4854593 = 3640945) B3640945
theorem B1282931 : Blo 566810 1282931 := bstep (se 1 (by rfl) ⟨962198, by rfl⟩ : syracuseStep 1282931 = 1924397) B1924397
theorem B1282967 : Blo 566810 1282967 := bstep (se 1 (by rfl) ⟨962225, by rfl⟩ : syracuseStep 1282967 = 1924451) B1924451
theorem B1283147 : Blo 566810 1283147 := bstep (se 1 (by rfl) ⟨962360, by rfl⟩ : syracuseStep 1283147 = 1924721) B1924721
theorem B1283201 : Blo 566810 1283201 := bstep (se 2 (by rfl) ⟨481200, by rfl⟩ : syracuseStep 1283201 = 962401) B962401
theorem B1283417 : Blo 566810 1283417 := bstep (se 2 (by rfl) ⟨481281, by rfl⟩ : syracuseStep 1283417 = 962563) B962563
theorem B1283507 : Blo 566810 1283507 := bstep (se 1 (by rfl) ⟨962630, by rfl⟩ : syracuseStep 1283507 = 1925261) B1925261
theorem B1283543 : Blo 566810 1283543 := bstep (se 1 (by rfl) ⟨962657, by rfl⟩ : syracuseStep 1283543 = 1925315) B1925315
theorem B2430425 : Blo 566810 2430425 := bstep (se 2 (by rfl) ⟨911409, by rfl⟩ : syracuseStep 2430425 = 1822819) B1822819
theorem B1283723 : Blo 566810 1283723 := bstep (se 1 (by rfl) ⟨962792, by rfl⟩ : syracuseStep 1283723 = 1925585) B1925585
theorem B1283777 : Blo 566810 1283777 := bstep (se 2 (by rfl) ⟨481416, by rfl⟩ : syracuseStep 1283777 = 962833) B962833
theorem B1283993 : Blo 566810 1283993 := bstep (se 2 (by rfl) ⟨481497, by rfl⟩ : syracuseStep 1283993 = 962995) B962995
theorem B1284083 : Blo 566810 1284083 := bstep (se 1 (by rfl) ⟨963062, by rfl⟩ : syracuseStep 1284083 = 1926125) B1926125
theorem B1284119 : Blo 566810 1284119 := bstep (se 1 (by rfl) ⟨963089, by rfl⟩ : syracuseStep 1284119 = 1926179) B1926179
theorem B2627635 : Blo 566810 2627635 := bstep (se 1 (by rfl) ⟨1970726, by rfl⟩ : syracuseStep 2627635 = 3941453) B3941453
theorem B4626497 : Blo 566810 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B956569 : Blo 566810 956569 := bstep (se 2 (by rfl) ⟨358713, by rfl⟩ : syracuseStep 956569 = 717427) B717427
theorem B1284299 : Blo 566810 1284299 := bstep (se 1 (by rfl) ⟨963224, by rfl⟩ : syracuseStep 1284299 = 1926449) B1926449
theorem B9705905 : Blo 566810 9705905 := bstep (se 2 (by rfl) ⟨3639714, by rfl⟩ : syracuseStep 9705905 = 7279429) B7279429
theorem B957143 : Blo 566810 957143 := bstep (se 1 (by rfl) ⟨717857, by rfl⟩ : syracuseStep 957143 = 1435715) B1435715
theorem B957271 : Blo 566810 957271 := bstep (se 1 (by rfl) ⟨717953, by rfl⟩ : syracuseStep 957271 = 1435907) B1435907
theorem B2432065 : Blo 566810 2432065 := bstep (se 2 (by rfl) ⟨912024, by rfl⟩ : syracuseStep 2432065 = 1824049) B1824049
theorem B957899 : Blo 566810 957899 := bstep (se 1 (by rfl) ⟨718424, by rfl⟩ : syracuseStep 957899 = 1436849) B1436849
theorem B2301443 : Blo 566810 2301443 := bstep (se 1 (by rfl) ⟨1726082, by rfl⟩ : syracuseStep 2301443 = 3452165) B3452165
theorem B3644945 : Blo 566810 3644945 := bstep (se 2 (by rfl) ⟨1366854, by rfl⟩ : syracuseStep 3644945 = 2733709) B2733709
theorem B958027 : Blo 566810 958027 := bstep (se 1 (by rfl) ⟨718520, by rfl⟩ : syracuseStep 958027 = 1437041) B1437041
theorem B2432663 : Blo 566810 2432663 := bstep (se 1 (by rfl) ⟨1824497, by rfl⟩ : syracuseStep 2432663 = 3648995) B3648995
theorem B1154711 : Blo 566810 1154711 := bstep (se 1 (by rfl) ⟨866033, by rfl⟩ : syracuseStep 1154711 = 1732067) B1732067
theorem B1941185 : Blo 566810 1941185 := bstep (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) B1455889
theorem B958169 : Blo 566810 958169 := bstep (se 2 (by rfl) ⟨359313, by rfl⟩ : syracuseStep 958169 = 718627) B718627
theorem B5480257 : Blo 566810 5480257 := bstep (se 2 (by rfl) ⟨2055096, by rfl⟩ : syracuseStep 5480257 = 4110193) B4110193
theorem B1154891 : Blo 566810 1154891 := bstep (se 1 (by rfl) ⟨866168, by rfl⟩ : syracuseStep 1154891 = 1732337) B1732337
theorem B958297 : Blo 566810 958297 := bstep (se 2 (by rfl) ⟨359361, by rfl⟩ : syracuseStep 958297 = 718723) B718723
theorem B925643 : Blo 566810 925643 := bstep (se 1 (by rfl) ⟨694232, by rfl⟩ : syracuseStep 925643 = 1388465) B1388465
theorem B1876061 : Blo 566810 1876061 := bstep (se 3 (by rfl) ⟨351761, by rfl⟩ : syracuseStep 1876061 = 703523) B703523
theorem B4333661 : Blo 566810 4333661 := bstep (se 3 (by rfl) ⟨812561, by rfl⟩ : syracuseStep 4333661 = 1625123) B1625123
theorem B4628573 : Blo 566810 4628573 := bstep (se 3 (by rfl) ⟨867857, by rfl⟩ : syracuseStep 4628573 = 1735715) B1735715
theorem B958871 : Blo 566810 958871 := bstep (se 1 (by rfl) ⟨719153, by rfl⟩ : syracuseStep 958871 = 1438307) B1438307
theorem B1024435 : Blo 566810 1024435 := bstep (se 1 (by rfl) ⟨768326, by rfl⟩ : syracuseStep 1024435 = 1536653) B1536653
theorem B958999 : Blo 566810 958999 := bstep (se 1 (by rfl) ⟨719249, by rfl⟩ : syracuseStep 958999 = 1438499) B1438499
theorem B729751 : Blo 566810 729751 := bstep (se 1 (by rfl) ⟨547313, by rfl⟩ : syracuseStep 729751 = 1094627) B1094627
theorem B9872077 : Blo 566810 9872077 := bstep (se 3 (by rfl) ⟨1851014, by rfl⟩ : syracuseStep 9872077 = 3702029) B3702029
theorem B1614667 : Blo 566810 1614667 := bstep (se 1 (by rfl) ⟨1211000, by rfl⟩ : syracuseStep 1614667 = 2422001) B2422001
theorem B6169445 : Blo 566810 6169445 := bstep (se 4 (by rfl) ⟨578385, by rfl⟩ : syracuseStep 6169445 = 1156771) B1156771
theorem B2433995 : Blo 566810 2433995 := bstep (se 1 (by rfl) ⟨1825496, by rfl⟩ : syracuseStep 2433995 = 3650993) B3650993
theorem B1614941 : Blo 566810 1614941 := bstep (se 3 (by rfl) ⟨302801, by rfl⟩ : syracuseStep 1614941 = 605603) B605603
theorem B959627 : Blo 566810 959627 := bstep (se 1 (by rfl) ⟨719720, by rfl⟩ : syracuseStep 959627 = 1439441) B1439441
theorem B959755 : Blo 566810 959755 := bstep (se 1 (by rfl) ⟨719816, by rfl⟩ : syracuseStep 959755 = 1439633) B1439633
theorem B959897 : Blo 566810 959897 := bstep (se 2 (by rfl) ⟨359961, by rfl⟩ : syracuseStep 959897 = 719923) B719923
theorem B1025473 : Blo 566810 1025473 := bstep (se 2 (by rfl) ⟨384552, by rfl⟩ : syracuseStep 1025473 = 769105) B769105
theorem B960025 : Blo 566810 960025 := bstep (se 2 (by rfl) ⟨360009, by rfl⟩ : syracuseStep 960025 = 720019) B720019
theorem B566827 : Blo 566810 566827 := bstep (se 1 (by rfl) ⟨425120, by rfl⟩ : syracuseStep 566827 = 850241) B850241
theorem B566839 : Blo 566810 566839 := bstep (se 1 (by rfl) ⟨425129, by rfl⟩ : syracuseStep 566839 = 850259) B850259
theorem B566859 : Blo 566810 566859 := bstep (se 1 (by rfl) ⟨425144, by rfl⟩ : syracuseStep 566859 = 850289) B850289
theorem B566871 : Blo 566810 566871 := bstep (se 1 (by rfl) ⟨425153, by rfl⟩ : syracuseStep 566871 = 850307) B850307
theorem B2631257 : Blo 566810 2631257 := bstep (se 2 (by rfl) ⟨986721, by rfl⟩ : syracuseStep 2631257 = 1973443) B1973443
theorem B566891 : Blo 566810 566891 := bstep (se 1 (by rfl) ⟨425168, by rfl⟩ : syracuseStep 566891 = 850337) B850337
theorem B566903 : Blo 566810 566903 := bstep (se 1 (by rfl) ⟨425177, by rfl⟩ : syracuseStep 566903 = 850355) B850355
theorem B566923 : Blo 566810 566923 := bstep (se 1 (by rfl) ⟨425192, by rfl⟩ : syracuseStep 566923 = 850385) B850385
theorem B566935 : Blo 566810 566935 := bstep (se 1 (by rfl) ⟨425201, by rfl⟩ : syracuseStep 566935 = 850403) B850403
theorem B566955 : Blo 566810 566955 := bstep (se 1 (by rfl) ⟨425216, by rfl⟩ : syracuseStep 566955 = 850433) B850433
theorem B4990643 : Blo 566810 4990643 := bstep (se 1 (by rfl) ⟨3742982, by rfl⟩ : syracuseStep 4990643 = 7485965) B7485965
theorem B566967 : Blo 566810 566967 := bstep (se 1 (by rfl) ⟨425225, by rfl⟩ : syracuseStep 566967 = 850451) B850451
theorem B566987 : Blo 566810 566987 := bstep (se 1 (by rfl) ⟨425240, by rfl⟩ : syracuseStep 566987 = 850481) B850481
theorem B8726221 : Blo 566810 8726221 := bstep (se 3 (by rfl) ⟨1636166, by rfl⟩ : syracuseStep 8726221 = 3272333) B3272333
theorem B566999 : Blo 566810 566999 := bstep (se 1 (by rfl) ⟨425249, by rfl⟩ : syracuseStep 566999 = 850499) B850499
theorem B567019 : Blo 566810 567019 := bstep (se 1 (by rfl) ⟨425264, by rfl⟩ : syracuseStep 567019 = 850529) B850529
theorem B567031 : Blo 566810 567031 := bstep (se 1 (by rfl) ⟨425273, by rfl⟩ : syracuseStep 567031 = 850547) B850547
theorem B567051 : Blo 566810 567051 := bstep (se 1 (by rfl) ⟨425288, by rfl⟩ : syracuseStep 567051 = 850577) B850577
theorem B567063 : Blo 566810 567063 := bstep (se 1 (by rfl) ⟨425297, by rfl⟩ : syracuseStep 567063 = 850595) B850595
theorem B567083 : Blo 566810 567083 := bstep (se 1 (by rfl) ⟨425312, by rfl⟩ : syracuseStep 567083 = 850625) B850625
theorem B567095 : Blo 566810 567095 := bstep (se 1 (by rfl) ⟨425321, by rfl⟩ : syracuseStep 567095 = 850643) B850643
theorem B567115 : Blo 566810 567115 := bstep (se 1 (by rfl) ⟨425336, by rfl⟩ : syracuseStep 567115 = 850673) B850673
theorem B567127 : Blo 566810 567127 := bstep (se 1 (by rfl) ⟨425345, by rfl⟩ : syracuseStep 567127 = 850691) B850691
theorem B567147 : Blo 566810 567147 := bstep (se 1 (by rfl) ⟨425360, by rfl⟩ : syracuseStep 567147 = 850721) B850721
theorem B567159 : Blo 566810 567159 := bstep (se 1 (by rfl) ⟨425369, by rfl⟩ : syracuseStep 567159 = 850739) B850739
theorem B567179 : Blo 566810 567179 := bstep (se 1 (by rfl) ⟨425384, by rfl⟩ : syracuseStep 567179 = 850769) B850769
theorem B567191 : Blo 566810 567191 := bstep (se 1 (by rfl) ⟨425393, by rfl⟩ : syracuseStep 567191 = 850787) B850787
theorem B567211 : Blo 566810 567211 := bstep (se 1 (by rfl) ⟨425408, by rfl⟩ : syracuseStep 567211 = 850817) B850817
theorem B567223 : Blo 566810 567223 := bstep (se 1 (by rfl) ⟨425417, by rfl⟩ : syracuseStep 567223 = 850835) B850835
theorem B567243 : Blo 566810 567243 := bstep (se 1 (by rfl) ⟨425432, by rfl⟩ : syracuseStep 567243 = 850865) B850865
theorem B567255 : Blo 566810 567255 := bstep (se 1 (by rfl) ⟨425441, by rfl⟩ : syracuseStep 567255 = 850883) B850883
theorem B567275 : Blo 566810 567275 := bstep (se 1 (by rfl) ⟨425456, by rfl⟩ : syracuseStep 567275 = 850913) B850913
theorem B1026035 : Blo 566810 1026035 := bstep (se 1 (by rfl) ⟨769526, by rfl⟩ : syracuseStep 1026035 = 1539053) B1539053
theorem B567287 : Blo 566810 567287 := bstep (se 1 (by rfl) ⟨425465, by rfl⟩ : syracuseStep 567287 = 850931) B850931
theorem B567307 : Blo 566810 567307 := bstep (se 1 (by rfl) ⟨425480, by rfl⟩ : syracuseStep 567307 = 850961) B850961
theorem B567319 : Blo 566810 567319 := bstep (se 1 (by rfl) ⟨425489, by rfl⟩ : syracuseStep 567319 = 850979) B850979
theorem B567339 : Blo 566810 567339 := bstep (se 1 (by rfl) ⟨425504, by rfl⟩ : syracuseStep 567339 = 851009) B851009
theorem B2435123 : Blo 566810 2435123 := bstep (se 1 (by rfl) ⟨1826342, by rfl⟩ : syracuseStep 2435123 = 3652685) B3652685
theorem B567351 : Blo 566810 567351 := bstep (se 1 (by rfl) ⟨425513, by rfl⟩ : syracuseStep 567351 = 851027) B851027
theorem B567371 : Blo 566810 567371 := bstep (se 1 (by rfl) ⟨425528, by rfl⟩ : syracuseStep 567371 = 851057) B851057
theorem B567383 : Blo 566810 567383 := bstep (se 1 (by rfl) ⟨425537, by rfl⟩ : syracuseStep 567383 = 851075) B851075
theorem B960599 : Blo 566810 960599 := bstep (se 1 (by rfl) ⟨720449, by rfl⟩ : syracuseStep 960599 = 1440899) B1440899
theorem B567403 : Blo 566810 567403 := bstep (se 1 (by rfl) ⟨425552, by rfl⟩ : syracuseStep 567403 = 851105) B851105
theorem B567415 : Blo 566810 567415 := bstep (se 1 (by rfl) ⟨425561, by rfl⟩ : syracuseStep 567415 = 851123) B851123
theorem B567435 : Blo 566810 567435 := bstep (se 1 (by rfl) ⟨425576, by rfl⟩ : syracuseStep 567435 = 851153) B851153
theorem B567447 : Blo 566810 567447 := bstep (se 1 (by rfl) ⟨425585, by rfl⟩ : syracuseStep 567447 = 851171) B851171
theorem B567467 : Blo 566810 567467 := bstep (se 1 (by rfl) ⟨425600, by rfl⟩ : syracuseStep 567467 = 851201) B851201
theorem B567479 : Blo 566810 567479 := bstep (se 1 (by rfl) ⟨425609, by rfl⟩ : syracuseStep 567479 = 851219) B851219
theorem B567499 : Blo 566810 567499 := bstep (se 1 (by rfl) ⟨425624, by rfl⟩ : syracuseStep 567499 = 851249) B851249
theorem B567511 : Blo 566810 567511 := bstep (se 1 (by rfl) ⟨425633, by rfl⟩ : syracuseStep 567511 = 851267) B851267
theorem B960727 : Blo 566810 960727 := bstep (se 1 (by rfl) ⟨720545, by rfl⟩ : syracuseStep 960727 = 1441091) B1441091
theorem B567531 : Blo 566810 567531 := bstep (se 1 (by rfl) ⟨425648, by rfl⟩ : syracuseStep 567531 = 851297) B851297
theorem B567543 : Blo 566810 567543 := bstep (se 1 (by rfl) ⟨425657, by rfl⟩ : syracuseStep 567543 = 851315) B851315
theorem B567563 : Blo 566810 567563 := bstep (se 1 (by rfl) ⟨425672, by rfl⟩ : syracuseStep 567563 = 851345) B851345
theorem B567575 : Blo 566810 567575 := bstep (se 1 (by rfl) ⟨425681, by rfl⟩ : syracuseStep 567575 = 851363) B851363
theorem B567595 : Blo 566810 567595 := bstep (se 1 (by rfl) ⟨425696, by rfl⟩ : syracuseStep 567595 = 851393) B851393
theorem B567607 : Blo 566810 567607 := bstep (se 1 (by rfl) ⟨425705, by rfl⟩ : syracuseStep 567607 = 851411) B851411
theorem B567627 : Blo 566810 567627 := bstep (se 1 (by rfl) ⟨425720, by rfl⟩ : syracuseStep 567627 = 851441) B851441
theorem B567639 : Blo 566810 567639 := bstep (se 1 (by rfl) ⟨425729, by rfl⟩ : syracuseStep 567639 = 851459) B851459
theorem B567659 : Blo 566810 567659 := bstep (se 1 (by rfl) ⟨425744, by rfl⟩ : syracuseStep 567659 = 851489) B851489
theorem B567671 : Blo 566810 567671 := bstep (se 1 (by rfl) ⟨425753, by rfl⟩ : syracuseStep 567671 = 851507) B851507
theorem B567691 : Blo 566810 567691 := bstep (se 1 (by rfl) ⟨425768, by rfl⟩ : syracuseStep 567691 = 851537) B851537
theorem B567703 : Blo 566810 567703 := bstep (se 1 (by rfl) ⟨425777, by rfl⟩ : syracuseStep 567703 = 851555) B851555
theorem B567723 : Blo 566810 567723 := bstep (se 1 (by rfl) ⟨425792, by rfl⟩ : syracuseStep 567723 = 851585) B851585
theorem B567735 : Blo 566810 567735 := bstep (se 1 (by rfl) ⟨425801, by rfl⟩ : syracuseStep 567735 = 851603) B851603
theorem B567755 : Blo 566810 567755 := bstep (se 1 (by rfl) ⟨425816, by rfl⟩ : syracuseStep 567755 = 851633) B851633
theorem B567767 : Blo 566810 567767 := bstep (se 1 (by rfl) ⟨425825, by rfl⟩ : syracuseStep 567767 = 851651) B851651
theorem B567787 : Blo 566810 567787 := bstep (se 1 (by rfl) ⟨425840, by rfl⟩ : syracuseStep 567787 = 851681) B851681
theorem B567799 : Blo 566810 567799 := bstep (se 1 (by rfl) ⟨425849, by rfl⟩ : syracuseStep 567799 = 851699) B851699
theorem B567819 : Blo 566810 567819 := bstep (se 1 (by rfl) ⟨425864, by rfl⟩ : syracuseStep 567819 = 851729) B851729
theorem B567831 : Blo 566810 567831 := bstep (se 1 (by rfl) ⟨425873, by rfl⟩ : syracuseStep 567831 = 851747) B851747
theorem B567851 : Blo 566810 567851 := bstep (se 1 (by rfl) ⟨425888, by rfl⟩ : syracuseStep 567851 = 851777) B851777
theorem B567863 : Blo 566810 567863 := bstep (se 1 (by rfl) ⟨425897, by rfl⟩ : syracuseStep 567863 = 851795) B851795
theorem B567883 : Blo 566810 567883 := bstep (se 1 (by rfl) ⟨425912, by rfl⟩ : syracuseStep 567883 = 851825) B851825
theorem B567895 : Blo 566810 567895 := bstep (se 1 (by rfl) ⟨425921, by rfl⟩ : syracuseStep 567895 = 851843) B851843
theorem B567915 : Blo 566810 567915 := bstep (se 1 (by rfl) ⟨425936, by rfl⟩ : syracuseStep 567915 = 851873) B851873
theorem B567927 : Blo 566810 567927 := bstep (se 1 (by rfl) ⟨425945, by rfl⟩ : syracuseStep 567927 = 851891) B851891
theorem B567947 : Blo 566810 567947 := bstep (se 1 (by rfl) ⟨425960, by rfl⟩ : syracuseStep 567947 = 851921) B851921
theorem B567959 : Blo 566810 567959 := bstep (se 1 (by rfl) ⟨425969, by rfl⟩ : syracuseStep 567959 = 851939) B851939
theorem B567979 : Blo 566810 567979 := bstep (se 1 (by rfl) ⟨425984, by rfl⟩ : syracuseStep 567979 = 851969) B851969
theorem B567991 : Blo 566810 567991 := bstep (se 1 (by rfl) ⟨425993, by rfl⟩ : syracuseStep 567991 = 851987) B851987
theorem B568011 : Blo 566810 568011 := bstep (se 1 (by rfl) ⟨426008, by rfl⟩ : syracuseStep 568011 = 852017) B852017
theorem B568023 : Blo 566810 568023 := bstep (se 1 (by rfl) ⟨426017, by rfl⟩ : syracuseStep 568023 = 852035) B852035
theorem B568043 : Blo 566810 568043 := bstep (se 1 (by rfl) ⟨426032, by rfl⟩ : syracuseStep 568043 = 852065) B852065
theorem B568055 : Blo 566810 568055 := bstep (se 1 (by rfl) ⟨426041, by rfl⟩ : syracuseStep 568055 = 852083) B852083
theorem B2075395 : Blo 566810 2075395 := bstep (se 1 (by rfl) ⟨1556546, by rfl⟩ : syracuseStep 2075395 = 3113093) B3113093
theorem B568075 : Blo 566810 568075 := bstep (se 1 (by rfl) ⟨426056, by rfl⟩ : syracuseStep 568075 = 852113) B852113
theorem B568087 : Blo 566810 568087 := bstep (se 1 (by rfl) ⟨426065, by rfl⟩ : syracuseStep 568087 = 852131) B852131
theorem B1846039 : Blo 566810 1846039 := bstep (se 1 (by rfl) ⟨1384529, by rfl⟩ : syracuseStep 1846039 = 2769059) B2769059
theorem B568107 : Blo 566810 568107 := bstep (se 1 (by rfl) ⟨426080, by rfl⟩ : syracuseStep 568107 = 852161) B852161
theorem B27601717 : Blo 566810 27601717 := bstep (se 5 (by rfl) ⟨1293830, by rfl⟩ : syracuseStep 27601717 = 2587661) B2587661
theorem B568119 : Blo 566810 568119 := bstep (se 1 (by rfl) ⟨426089, by rfl⟩ : syracuseStep 568119 = 852179) B852179
theorem B568139 : Blo 566810 568139 := bstep (se 1 (by rfl) ⟨426104, by rfl⟩ : syracuseStep 568139 = 852209) B852209
theorem B961355 : Blo 566810 961355 := bstep (se 1 (by rfl) ⟨721016, by rfl⟩ : syracuseStep 961355 = 1442033) B1442033
theorem B568151 : Blo 566810 568151 := bstep (se 1 (by rfl) ⟨426113, by rfl⟩ : syracuseStep 568151 = 852227) B852227
theorem B568171 : Blo 566810 568171 := bstep (se 1 (by rfl) ⟨426128, by rfl⟩ : syracuseStep 568171 = 852257) B852257
theorem B568183 : Blo 566810 568183 := bstep (se 1 (by rfl) ⟨426137, by rfl⟩ : syracuseStep 568183 = 852275) B852275
theorem B568203 : Blo 566810 568203 := bstep (se 1 (by rfl) ⟨426152, by rfl⟩ : syracuseStep 568203 = 852305) B852305
theorem B568215 : Blo 566810 568215 := bstep (se 1 (by rfl) ⟨426161, by rfl⟩ : syracuseStep 568215 = 852323) B852323
theorem B568235 : Blo 566810 568235 := bstep (se 1 (by rfl) ⟨426176, by rfl⟩ : syracuseStep 568235 = 852353) B852353
theorem B568247 : Blo 566810 568247 := bstep (se 1 (by rfl) ⟨426185, by rfl⟩ : syracuseStep 568247 = 852371) B852371
theorem B568267 : Blo 566810 568267 := bstep (se 1 (by rfl) ⟨426200, by rfl⟩ : syracuseStep 568267 = 852401) B852401
theorem B961483 : Blo 566810 961483 := bstep (se 1 (by rfl) ⟨721112, by rfl⟩ : syracuseStep 961483 = 1442225) B1442225
theorem B568279 : Blo 566810 568279 := bstep (se 1 (by rfl) ⟨426209, by rfl⟩ : syracuseStep 568279 = 852419) B852419
theorem B568299 : Blo 566810 568299 := bstep (se 1 (by rfl) ⟨426224, by rfl⟩ : syracuseStep 568299 = 852449) B852449
theorem B568311 : Blo 566810 568311 := bstep (se 1 (by rfl) ⟨426233, by rfl⟩ : syracuseStep 568311 = 852467) B852467
theorem B568331 : Blo 566810 568331 := bstep (se 1 (by rfl) ⟨426248, by rfl⟩ : syracuseStep 568331 = 852497) B852497
theorem B568343 : Blo 566810 568343 := bstep (se 1 (by rfl) ⟨426257, by rfl⟩ : syracuseStep 568343 = 852515) B852515
theorem B568363 : Blo 566810 568363 := bstep (se 1 (by rfl) ⟨426272, by rfl⟩ : syracuseStep 568363 = 852545) B852545
theorem B568375 : Blo 566810 568375 := bstep (se 1 (by rfl) ⟨426281, by rfl⟩ : syracuseStep 568375 = 852563) B852563
theorem B568395 : Blo 566810 568395 := bstep (se 1 (by rfl) ⟨426296, by rfl⟩ : syracuseStep 568395 = 852593) B852593
theorem B568407 : Blo 566810 568407 := bstep (se 1 (by rfl) ⟨426305, by rfl⟩ : syracuseStep 568407 = 852611) B852611
theorem B961625 : Blo 566810 961625 := bstep (se 2 (by rfl) ⟨360609, by rfl⟩ : syracuseStep 961625 = 721219) B721219
theorem B568427 : Blo 566810 568427 := bstep (se 1 (by rfl) ⟨426320, by rfl⟩ : syracuseStep 568427 = 852641) B852641
theorem B568439 : Blo 566810 568439 := bstep (se 1 (by rfl) ⟨426329, by rfl⟩ : syracuseStep 568439 = 852659) B852659
theorem B568459 : Blo 566810 568459 := bstep (se 1 (by rfl) ⟨426344, by rfl⟩ : syracuseStep 568459 = 852689) B852689
theorem B568471 : Blo 566810 568471 := bstep (se 1 (by rfl) ⟨426353, by rfl⟩ : syracuseStep 568471 = 852707) B852707
theorem B568491 : Blo 566810 568491 := bstep (se 1 (by rfl) ⟨426368, by rfl⟩ : syracuseStep 568491 = 852737) B852737
theorem B568503 : Blo 566810 568503 := bstep (se 1 (by rfl) ⟨426377, by rfl⟩ : syracuseStep 568503 = 852755) B852755
theorem B568523 : Blo 566810 568523 := bstep (se 1 (by rfl) ⟨426392, by rfl⟩ : syracuseStep 568523 = 852785) B852785
theorem B568535 : Blo 566810 568535 := bstep (se 1 (by rfl) ⟨426401, by rfl⟩ : syracuseStep 568535 = 852803) B852803
theorem B961753 : Blo 566810 961753 := bstep (se 2 (by rfl) ⟨360657, by rfl⟩ : syracuseStep 961753 = 721315) B721315
theorem B568555 : Blo 566810 568555 := bstep (se 1 (by rfl) ⟨426416, by rfl⟩ : syracuseStep 568555 = 852833) B852833
theorem B568567 : Blo 566810 568567 := bstep (se 1 (by rfl) ⟨426425, by rfl⟩ : syracuseStep 568567 = 852851) B852851
theorem B568587 : Blo 566810 568587 := bstep (se 1 (by rfl) ⟨426440, by rfl⟩ : syracuseStep 568587 = 852881) B852881
theorem B568599 : Blo 566810 568599 := bstep (se 1 (by rfl) ⟨426449, by rfl⟩ : syracuseStep 568599 = 852899) B852899
theorem B568619 : Blo 566810 568619 := bstep (se 1 (by rfl) ⟨426464, by rfl⟩ : syracuseStep 568619 = 852929) B852929
theorem B568631 : Blo 566810 568631 := bstep (se 1 (by rfl) ⟨426473, by rfl⟩ : syracuseStep 568631 = 852947) B852947
theorem B568651 : Blo 566810 568651 := bstep (se 1 (by rfl) ⟨426488, by rfl⟩ : syracuseStep 568651 = 852977) B852977
theorem B568663 : Blo 566810 568663 := bstep (se 1 (by rfl) ⟨426497, by rfl⟩ : syracuseStep 568663 = 852995) B852995
theorem B1617241 : Blo 566810 1617241 := bstep (se 2 (by rfl) ⟨606465, by rfl⟩ : syracuseStep 1617241 = 1212931) B1212931
theorem B568683 : Blo 566810 568683 := bstep (se 1 (by rfl) ⟨426512, by rfl⟩ : syracuseStep 568683 = 853025) B853025
theorem B568695 : Blo 566810 568695 := bstep (se 1 (by rfl) ⟨426521, by rfl⟩ : syracuseStep 568695 = 853043) B853043
theorem B568715 : Blo 566810 568715 := bstep (se 1 (by rfl) ⟨426536, by rfl⟩ : syracuseStep 568715 = 853073) B853073
theorem B568727 : Blo 566810 568727 := bstep (se 1 (by rfl) ⟨426545, by rfl⟩ : syracuseStep 568727 = 853091) B853091
theorem B568747 : Blo 566810 568747 := bstep (se 1 (by rfl) ⟨426560, by rfl⟩ : syracuseStep 568747 = 853121) B853121
theorem B6499763 : Blo 566810 6499763 := bstep (se 1 (by rfl) ⟨4874822, by rfl⟩ : syracuseStep 6499763 = 9749645) B9749645
theorem B568759 : Blo 566810 568759 := bstep (se 1 (by rfl) ⟨426569, by rfl⟩ : syracuseStep 568759 = 853139) B853139
theorem B568779 : Blo 566810 568779 := bstep (se 1 (by rfl) ⟨426584, by rfl⟩ : syracuseStep 568779 = 853169) B853169
theorem B568791 : Blo 566810 568791 := bstep (se 1 (by rfl) ⟨426593, by rfl⟩ : syracuseStep 568791 = 853187) B853187
theorem B568811 : Blo 566810 568811 := bstep (se 1 (by rfl) ⟨426608, by rfl⟩ : syracuseStep 568811 = 853217) B853217
theorem B568823 : Blo 566810 568823 := bstep (se 1 (by rfl) ⟨426617, by rfl⟩ : syracuseStep 568823 = 853235) B853235
theorem B568843 : Blo 566810 568843 := bstep (se 1 (by rfl) ⟨426632, by rfl⟩ : syracuseStep 568843 = 853265) B853265
theorem B568855 : Blo 566810 568855 := bstep (se 1 (by rfl) ⟨426641, by rfl⟩ : syracuseStep 568855 = 853283) B853283
theorem B568875 : Blo 566810 568875 := bstep (se 1 (by rfl) ⟨426656, by rfl⟩ : syracuseStep 568875 = 853313) B853313
theorem B568887 : Blo 566810 568887 := bstep (se 1 (by rfl) ⟨426665, by rfl⟩ : syracuseStep 568887 = 853331) B853331
theorem B568907 : Blo 566810 568907 := bstep (se 1 (by rfl) ⟨426680, by rfl⟩ : syracuseStep 568907 = 853361) B853361
theorem B568919 : Blo 566810 568919 := bstep (se 1 (by rfl) ⟨426689, by rfl⟩ : syracuseStep 568919 = 853379) B853379
theorem B568939 : Blo 566810 568939 := bstep (se 1 (by rfl) ⟨426704, by rfl⟩ : syracuseStep 568939 = 853409) B853409
theorem B568951 : Blo 566810 568951 := bstep (se 1 (by rfl) ⟨426713, by rfl⟩ : syracuseStep 568951 = 853427) B853427
theorem B568971 : Blo 566810 568971 := bstep (se 1 (by rfl) ⟨426728, by rfl⟩ : syracuseStep 568971 = 853457) B853457
theorem B568983 : Blo 566810 568983 := bstep (se 1 (by rfl) ⟨426737, by rfl⟩ : syracuseStep 568983 = 853475) B853475
theorem B569003 : Blo 566810 569003 := bstep (se 1 (by rfl) ⟨426752, by rfl⟩ : syracuseStep 569003 = 853505) B853505
theorem B569015 : Blo 566810 569015 := bstep (se 1 (by rfl) ⟨426761, by rfl⟩ : syracuseStep 569015 = 853523) B853523
theorem B569035 : Blo 566810 569035 := bstep (se 1 (by rfl) ⟨426776, by rfl⟩ : syracuseStep 569035 = 853553) B853553
theorem B569047 : Blo 566810 569047 := bstep (se 1 (by rfl) ⟨426785, by rfl⟩ : syracuseStep 569047 = 853571) B853571
theorem B569067 : Blo 566810 569067 := bstep (se 1 (by rfl) ⟨426800, by rfl⟩ : syracuseStep 569067 = 853601) B853601
theorem B569079 : Blo 566810 569079 := bstep (se 1 (by rfl) ⟨426809, by rfl⟩ : syracuseStep 569079 = 853619) B853619
theorem B569099 : Blo 566810 569099 := bstep (se 1 (by rfl) ⟨426824, by rfl⟩ : syracuseStep 569099 = 853649) B853649
theorem B569111 : Blo 566810 569111 := bstep (se 1 (by rfl) ⟨426833, by rfl⟩ : syracuseStep 569111 = 853667) B853667
theorem B962327 : Blo 566810 962327 := bstep (se 1 (by rfl) ⟨721745, by rfl⟩ : syracuseStep 962327 = 1443491) B1443491
theorem B569131 : Blo 566810 569131 := bstep (se 1 (by rfl) ⟨426848, by rfl⟩ : syracuseStep 569131 = 853697) B853697
theorem B569143 : Blo 566810 569143 := bstep (se 1 (by rfl) ⟨426857, by rfl⟩ : syracuseStep 569143 = 853715) B853715
theorem B569163 : Blo 566810 569163 := bstep (se 1 (by rfl) ⟨426872, by rfl⟩ : syracuseStep 569163 = 853745) B853745
theorem B569175 : Blo 566810 569175 := bstep (se 1 (by rfl) ⟨426881, by rfl⟩ : syracuseStep 569175 = 853763) B853763
theorem B569195 : Blo 566810 569195 := bstep (se 1 (by rfl) ⟨426896, by rfl⟩ : syracuseStep 569195 = 853793) B853793
theorem B569207 : Blo 566810 569207 := bstep (se 1 (by rfl) ⟨426905, by rfl⟩ : syracuseStep 569207 = 853811) B853811
theorem B569227 : Blo 566810 569227 := bstep (se 1 (by rfl) ⟨426920, by rfl⟩ : syracuseStep 569227 = 853841) B853841
theorem B569239 : Blo 566810 569239 := bstep (se 1 (by rfl) ⟨426929, by rfl⟩ : syracuseStep 569239 = 853859) B853859
theorem B962455 : Blo 566810 962455 := bstep (se 1 (by rfl) ⟨721841, by rfl⟩ : syracuseStep 962455 = 1443683) B1443683
theorem B569259 : Blo 566810 569259 := bstep (se 1 (by rfl) ⟨426944, by rfl⟩ : syracuseStep 569259 = 853889) B853889
theorem B2437037 : Blo 566810 2437037 := bstep (se 3 (by rfl) ⟨456944, by rfl⟩ : syracuseStep 2437037 = 913889) B913889
theorem B569271 : Blo 566810 569271 := bstep (se 1 (by rfl) ⟨426953, by rfl⟩ : syracuseStep 569271 = 853907) B853907
theorem B1617857 : Blo 566810 1617857 := bstep (se 2 (by rfl) ⟨606696, by rfl⟩ : syracuseStep 1617857 = 1213393) B1213393
theorem B569291 : Blo 566810 569291 := bstep (se 1 (by rfl) ⟨426968, by rfl⟩ : syracuseStep 569291 = 853937) B853937
theorem B569303 : Blo 566810 569303 := bstep (se 1 (by rfl) ⟨426977, by rfl⟩ : syracuseStep 569303 = 853955) B853955
theorem B569323 : Blo 566810 569323 := bstep (se 1 (by rfl) ⟨426992, by rfl⟩ : syracuseStep 569323 = 853985) B853985
theorem B569335 : Blo 566810 569335 := bstep (se 1 (by rfl) ⟨427001, by rfl⟩ : syracuseStep 569335 = 854003) B854003
theorem B569355 : Blo 566810 569355 := bstep (se 1 (by rfl) ⟨427016, by rfl⟩ : syracuseStep 569355 = 854033) B854033
theorem B569367 : Blo 566810 569367 := bstep (se 1 (by rfl) ⟨427025, by rfl⟩ : syracuseStep 569367 = 854051) B854051
theorem B569387 : Blo 566810 569387 := bstep (se 1 (by rfl) ⟨427040, by rfl⟩ : syracuseStep 569387 = 854081) B854081
theorem B569399 : Blo 566810 569399 := bstep (se 1 (by rfl) ⟨427049, by rfl⟩ : syracuseStep 569399 = 854099) B854099
theorem B569419 : Blo 566810 569419 := bstep (se 1 (by rfl) ⟨427064, by rfl⟩ : syracuseStep 569419 = 854129) B854129
theorem B569431 : Blo 566810 569431 := bstep (se 1 (by rfl) ⟨427073, by rfl⟩ : syracuseStep 569431 = 854147) B854147
theorem B569451 : Blo 566810 569451 := bstep (se 1 (by rfl) ⟨427088, by rfl⟩ : syracuseStep 569451 = 854177) B854177
theorem B569463 : Blo 566810 569463 := bstep (se 1 (by rfl) ⟨427097, by rfl⟩ : syracuseStep 569463 = 854195) B854195
theorem B569483 : Blo 566810 569483 := bstep (se 1 (by rfl) ⟨427112, by rfl⟩ : syracuseStep 569483 = 854225) B854225
theorem B2044055 : Blo 566810 2044055 := bstep (se 1 (by rfl) ⟨1533041, by rfl⟩ : syracuseStep 2044055 = 3066083) B3066083
theorem B23376023 : Blo 566810 23376023 := bstep (se 1 (by rfl) ⟨17532017, by rfl⟩ : syracuseStep 23376023 = 35064035) B35064035
theorem B569495 : Blo 566810 569495 := bstep (se 1 (by rfl) ⟨427121, by rfl⟩ : syracuseStep 569495 = 854243) B854243
theorem B569515 : Blo 566810 569515 := bstep (se 1 (by rfl) ⟨427136, by rfl⟩ : syracuseStep 569515 = 854273) B854273
theorem B569527 : Blo 566810 569527 := bstep (se 1 (by rfl) ⟨427145, by rfl⟩ : syracuseStep 569527 = 854291) B854291
theorem B569547 : Blo 566810 569547 := bstep (se 1 (by rfl) ⟨427160, by rfl⟩ : syracuseStep 569547 = 854321) B854321
theorem B569559 : Blo 566810 569559 := bstep (se 1 (by rfl) ⟨427169, by rfl⟩ : syracuseStep 569559 = 854339) B854339
theorem B569579 : Blo 566810 569579 := bstep (se 1 (by rfl) ⟨427184, by rfl⟩ : syracuseStep 569579 = 854369) B854369
theorem B569591 : Blo 566810 569591 := bstep (se 1 (by rfl) ⟨427193, by rfl⟩ : syracuseStep 569591 = 854387) B854387
theorem B569611 : Blo 566810 569611 := bstep (se 1 (by rfl) ⟨427208, by rfl⟩ : syracuseStep 569611 = 854417) B854417
theorem B1913111 : Blo 566810 1913111 := bstep (se 1 (by rfl) ⟨1434833, by rfl⟩ : syracuseStep 1913111 = 2869667) B2869667
theorem B569623 : Blo 566810 569623 := bstep (se 1 (by rfl) ⟨427217, by rfl⟩ : syracuseStep 569623 = 854435) B854435
theorem B569643 : Blo 566810 569643 := bstep (se 1 (by rfl) ⟨427232, by rfl⟩ : syracuseStep 569643 = 854465) B854465
theorem B569655 : Blo 566810 569655 := bstep (se 1 (by rfl) ⟨427241, by rfl⟩ : syracuseStep 569655 = 854483) B854483
theorem B569675 : Blo 566810 569675 := bstep (se 1 (by rfl) ⟨427256, by rfl⟩ : syracuseStep 569675 = 854513) B854513
theorem B569687 : Blo 566810 569687 := bstep (se 1 (by rfl) ⟨427265, by rfl⟩ : syracuseStep 569687 = 854531) B854531
theorem B569707 : Blo 566810 569707 := bstep (se 1 (by rfl) ⟨427280, by rfl⟩ : syracuseStep 569707 = 854561) B854561
theorem B569719 : Blo 566810 569719 := bstep (se 1 (by rfl) ⟨427289, by rfl⟩ : syracuseStep 569719 = 854579) B854579
theorem B569739 : Blo 566810 569739 := bstep (se 1 (by rfl) ⟨427304, by rfl⟩ : syracuseStep 569739 = 854609) B854609
theorem B569751 : Blo 566810 569751 := bstep (se 1 (by rfl) ⟨427313, by rfl⟩ : syracuseStep 569751 = 854627) B854627
theorem B569771 : Blo 566810 569771 := bstep (se 1 (by rfl) ⟨427328, by rfl⟩ : syracuseStep 569771 = 854657) B854657
theorem B569783 : Blo 566810 569783 := bstep (se 1 (by rfl) ⟨427337, by rfl⟩ : syracuseStep 569783 = 854675) B854675
theorem B569803 : Blo 566810 569803 := bstep (se 1 (by rfl) ⟨427352, by rfl⟩ : syracuseStep 569803 = 854705) B854705
theorem B569815 : Blo 566810 569815 := bstep (se 1 (by rfl) ⟨427361, by rfl⟩ : syracuseStep 569815 = 854723) B854723
theorem B569835 : Blo 566810 569835 := bstep (se 1 (by rfl) ⟨427376, by rfl⟩ : syracuseStep 569835 = 854753) B854753
theorem B569847 : Blo 566810 569847 := bstep (se 1 (by rfl) ⟨427385, by rfl⟩ : syracuseStep 569847 = 854771) B854771
theorem B569867 : Blo 566810 569867 := bstep (se 1 (by rfl) ⟨427400, by rfl⟩ : syracuseStep 569867 = 854801) B854801
theorem B963083 : Blo 566810 963083 := bstep (se 1 (by rfl) ⟨722312, by rfl⟩ : syracuseStep 963083 = 1444625) B1444625
theorem B569879 : Blo 566810 569879 := bstep (se 1 (by rfl) ⟨427409, by rfl⟩ : syracuseStep 569879 = 854819) B854819
theorem B569899 : Blo 566810 569899 := bstep (se 1 (by rfl) ⟨427424, by rfl⟩ : syracuseStep 569899 = 854849) B854849
theorem B569911 : Blo 566810 569911 := bstep (se 1 (by rfl) ⟨427433, by rfl⟩ : syracuseStep 569911 = 854867) B854867
theorem B1454657 : Blo 566810 1454657 := bstep (se 2 (by rfl) ⟨545496, by rfl⟩ : syracuseStep 1454657 = 1090993) B1090993
theorem B4305473 : Blo 566810 4305473 := bstep (se 2 (by rfl) ⟨1614552, by rfl⟩ : syracuseStep 4305473 = 3229105) B3229105
theorem B569931 : Blo 566810 569931 := bstep (se 1 (by rfl) ⟨427448, by rfl⟩ : syracuseStep 569931 = 854897) B854897
theorem B569943 : Blo 566810 569943 := bstep (se 1 (by rfl) ⟨427457, by rfl⟩ : syracuseStep 569943 = 854915) B854915
theorem B2437721 : Blo 566810 2437721 := bstep (se 2 (by rfl) ⟨914145, by rfl⟩ : syracuseStep 2437721 = 1828291) B1828291
theorem B569963 : Blo 566810 569963 := bstep (se 1 (by rfl) ⟨427472, by rfl⟩ : syracuseStep 569963 = 854945) B854945
theorem B569975 : Blo 566810 569975 := bstep (se 1 (by rfl) ⟨427481, by rfl⟩ : syracuseStep 569975 = 854963) B854963
theorem B569995 : Blo 566810 569995 := bstep (se 1 (by rfl) ⟨427496, by rfl⟩ : syracuseStep 569995 = 854993) B854993
theorem B963211 : Blo 566810 963211 := bstep (se 1 (by rfl) ⟨722408, by rfl⟩ : syracuseStep 963211 = 1444817) B1444817
theorem B2044561 : Blo 566810 2044561 := bstep (se 2 (by rfl) ⟨766710, by rfl⟩ : syracuseStep 2044561 = 1533421) B1533421
theorem B570007 : Blo 566810 570007 := bstep (se 1 (by rfl) ⟨427505, by rfl⟩ : syracuseStep 570007 = 855011) B855011
theorem B570027 : Blo 566810 570027 := bstep (se 1 (by rfl) ⟨427520, by rfl⟩ : syracuseStep 570027 = 855041) B855041
theorem B570039 : Blo 566810 570039 := bstep (se 1 (by rfl) ⟨427529, by rfl⟩ : syracuseStep 570039 = 855059) B855059
theorem B570059 : Blo 566810 570059 := bstep (se 1 (by rfl) ⟨427544, by rfl⟩ : syracuseStep 570059 = 855089) B855089
theorem B570071 : Blo 566810 570071 := bstep (se 1 (by rfl) ⟨427553, by rfl⟩ : syracuseStep 570071 = 855107) B855107
theorem B570091 : Blo 566810 570091 := bstep (se 1 (by rfl) ⟨427568, by rfl⟩ : syracuseStep 570091 = 855137) B855137
theorem B570103 : Blo 566810 570103 := bstep (se 1 (by rfl) ⟨427577, by rfl⟩ : syracuseStep 570103 = 855155) B855155
theorem B7484165 : Blo 566810 7484165 := bstep (se 4 (by rfl) ⟨701640, by rfl⟩ : syracuseStep 7484165 = 1403281) B1403281
theorem B570123 : Blo 566810 570123 := bstep (se 1 (by rfl) ⟨427592, by rfl⟩ : syracuseStep 570123 = 855185) B855185
theorem B570135 : Blo 566810 570135 := bstep (se 1 (by rfl) ⟨427601, by rfl⟩ : syracuseStep 570135 = 855203) B855203
theorem B570155 : Blo 566810 570155 := bstep (se 1 (by rfl) ⟨427616, by rfl⟩ : syracuseStep 570155 = 855233) B855233
theorem B1913651 : Blo 566810 1913651 := bstep (se 1 (by rfl) ⟨1435238, by rfl⟩ : syracuseStep 1913651 = 2870477) B2870477
theorem B570167 : Blo 566810 570167 := bstep (se 1 (by rfl) ⟨427625, by rfl⟩ : syracuseStep 570167 = 855251) B855251
theorem B570187 : Blo 566810 570187 := bstep (se 1 (by rfl) ⟨427640, by rfl⟩ : syracuseStep 570187 = 855281) B855281
theorem B570199 : Blo 566810 570199 := bstep (se 1 (by rfl) ⟨427649, by rfl⟩ : syracuseStep 570199 = 855299) B855299
theorem B6501221 : Blo 566810 6501221 := bstep (se 4 (by rfl) ⟨609489, by rfl⟩ : syracuseStep 6501221 = 1218979) B1218979
theorem B570219 : Blo 566810 570219 := bstep (se 1 (by rfl) ⟨427664, by rfl⟩ : syracuseStep 570219 = 855329) B855329
theorem B570231 : Blo 566810 570231 := bstep (se 1 (by rfl) ⟨427673, by rfl⟩ : syracuseStep 570231 = 855347) B855347
theorem B570251 : Blo 566810 570251 := bstep (se 1 (by rfl) ⟨427688, by rfl⟩ : syracuseStep 570251 = 855377) B855377
theorem B570263 : Blo 566810 570263 := bstep (se 1 (by rfl) ⟨427697, by rfl⟩ : syracuseStep 570263 = 855395) B855395
theorem B570283 : Blo 566810 570283 := bstep (se 1 (by rfl) ⟨427712, by rfl⟩ : syracuseStep 570283 = 855425) B855425
theorem B570295 : Blo 566810 570295 := bstep (se 1 (by rfl) ⟨427721, by rfl⟩ : syracuseStep 570295 = 855443) B855443
theorem B570315 : Blo 566810 570315 := bstep (se 1 (by rfl) ⟨427736, by rfl⟩ : syracuseStep 570315 = 855473) B855473
theorem B570327 : Blo 566810 570327 := bstep (se 1 (by rfl) ⟨427745, by rfl⟩ : syracuseStep 570327 = 855491) B855491
theorem B2765785 : Blo 566810 2765785 := bstep (se 2 (by rfl) ⟨1037169, by rfl⟩ : syracuseStep 2765785 = 2074339) B2074339
theorem B570347 : Blo 566810 570347 := bstep (se 1 (by rfl) ⟨427760, by rfl⟩ : syracuseStep 570347 = 855521) B855521
theorem B570359 : Blo 566810 570359 := bstep (se 1 (by rfl) ⟨427769, by rfl⟩ : syracuseStep 570359 = 855539) B855539
theorem B570379 : Blo 566810 570379 := bstep (se 1 (by rfl) ⟨427784, by rfl⟩ : syracuseStep 570379 = 855569) B855569
theorem B570391 : Blo 566810 570391 := bstep (se 1 (by rfl) ⟨427793, by rfl⟩ : syracuseStep 570391 = 855587) B855587
theorem B570411 : Blo 566810 570411 := bstep (se 1 (by rfl) ⟨427808, by rfl⟩ : syracuseStep 570411 = 855617) B855617
theorem B570423 : Blo 566810 570423 := bstep (se 1 (by rfl) ⟨427817, by rfl⟩ : syracuseStep 570423 = 855635) B855635
theorem B1913921 : Blo 566810 1913921 := bstep (se 2 (by rfl) ⟨717720, by rfl⟩ : syracuseStep 1913921 = 1435441) B1435441
theorem B570443 : Blo 566810 570443 := bstep (se 1 (by rfl) ⟨427832, by rfl⟩ : syracuseStep 570443 = 855665) B855665
theorem B570455 : Blo 566810 570455 := bstep (se 1 (by rfl) ⟨427841, by rfl⟩ : syracuseStep 570455 = 855683) B855683
theorem B570475 : Blo 566810 570475 := bstep (se 1 (by rfl) ⟨427856, by rfl⟩ : syracuseStep 570475 = 855713) B855713
theorem B570487 : Blo 566810 570487 := bstep (se 1 (by rfl) ⟨427865, by rfl⟩ : syracuseStep 570487 = 855731) B855731
theorem B570507 : Blo 566810 570507 := bstep (se 1 (by rfl) ⟨427880, by rfl⟩ : syracuseStep 570507 = 855761) B855761
theorem B2307217 : Blo 566810 2307217 := bstep (se 2 (by rfl) ⟨865206, by rfl⟩ : syracuseStep 2307217 = 1730413) B1730413
theorem B570519 : Blo 566810 570519 := bstep (se 1 (by rfl) ⟨427889, by rfl⟩ : syracuseStep 570519 = 855779) B855779
theorem B570539 : Blo 566810 570539 := bstep (se 1 (by rfl) ⟨427904, by rfl⟩ : syracuseStep 570539 = 855809) B855809
theorem B570551 : Blo 566810 570551 := bstep (se 1 (by rfl) ⟨427913, by rfl⟩ : syracuseStep 570551 = 855827) B855827
theorem B570571 : Blo 566810 570571 := bstep (se 1 (by rfl) ⟨427928, by rfl⟩ : syracuseStep 570571 = 855857) B855857
theorem B570583 : Blo 566810 570583 := bstep (se 1 (by rfl) ⟨427937, by rfl⟩ : syracuseStep 570583 = 855875) B855875
theorem B570603 : Blo 566810 570603 := bstep (se 1 (by rfl) ⟨427952, by rfl⟩ : syracuseStep 570603 = 855905) B855905
theorem B570615 : Blo 566810 570615 := bstep (se 1 (by rfl) ⟨427961, by rfl⟩ : syracuseStep 570615 = 855923) B855923
theorem B570635 : Blo 566810 570635 := bstep (se 1 (by rfl) ⟨427976, by rfl⟩ : syracuseStep 570635 = 855953) B855953
theorem B570647 : Blo 566810 570647 := bstep (se 1 (by rfl) ⟨427985, by rfl⟩ : syracuseStep 570647 = 855971) B855971
theorem B570667 : Blo 566810 570667 := bstep (se 1 (by rfl) ⟨428000, by rfl⟩ : syracuseStep 570667 = 856001) B856001
theorem B570679 : Blo 566810 570679 := bstep (se 1 (by rfl) ⟨428009, by rfl⟩ : syracuseStep 570679 = 856019) B856019
theorem B570699 : Blo 566810 570699 := bstep (se 1 (by rfl) ⟨428024, by rfl⟩ : syracuseStep 570699 = 856049) B856049
theorem B570711 : Blo 566810 570711 := bstep (se 1 (by rfl) ⟨428033, by rfl⟩ : syracuseStep 570711 = 856067) B856067
theorem B570731 : Blo 566810 570731 := bstep (se 1 (by rfl) ⟨428048, by rfl⟩ : syracuseStep 570731 = 856097) B856097
theorem B570743 : Blo 566810 570743 := bstep (se 1 (by rfl) ⟨428057, by rfl⟩ : syracuseStep 570743 = 856115) B856115
theorem B570763 : Blo 566810 570763 := bstep (se 1 (by rfl) ⟨428072, by rfl⟩ : syracuseStep 570763 = 856145) B856145
theorem B570775 : Blo 566810 570775 := bstep (se 1 (by rfl) ⟨428081, by rfl⟩ : syracuseStep 570775 = 856163) B856163
theorem B570795 : Blo 566810 570795 := bstep (se 1 (by rfl) ⟨428096, by rfl⟩ : syracuseStep 570795 = 856193) B856193
theorem B570807 : Blo 566810 570807 := bstep (se 1 (by rfl) ⟨428105, by rfl⟩ : syracuseStep 570807 = 856211) B856211
theorem B1914461 : Blo 566810 1914461 := bstep (se 3 (by rfl) ⟨358961, by rfl⟩ : syracuseStep 1914461 = 717923) B717923
theorem B7288451 : Blo 566810 7288451 := bstep (se 1 (by rfl) ⟨5466338, by rfl⟩ : syracuseStep 7288451 = 10932677) B10932677
theorem B1619929 : Blo 566810 1619929 := bstep (se 2 (by rfl) ⟨607473, by rfl⟩ : syracuseStep 1619929 = 1214947) B1214947
theorem B2308189 : Blo 566810 2308189 := bstep (se 3 (by rfl) ⟨432785, by rfl⟩ : syracuseStep 2308189 = 865571) B865571
theorem B1620317 : Blo 566810 1620317 := bstep (se 3 (by rfl) ⟨303809, by rfl⟩ : syracuseStep 1620317 = 607619) B607619
theorem B4307417 : Blo 566810 4307417 := bstep (se 2 (by rfl) ⟨1615281, by rfl⟩ : syracuseStep 4307417 = 3230563) B3230563
theorem B1915595 : Blo 566810 1915595 := bstep (se 1 (by rfl) ⟨1436696, by rfl⟩ : syracuseStep 1915595 = 2873393) B2873393
theorem B768727 : Blo 566810 768727 := bstep (se 1 (by rfl) ⟨576545, by rfl⟩ : syracuseStep 768727 = 1153091) B1153091
theorem B637771 : Blo 566810 637771 := bstep (se 1 (by rfl) ⟨478328, by rfl⟩ : syracuseStep 637771 = 956657) B956657
theorem B3652427 : Blo 566810 3652427 := bstep (se 1 (by rfl) ⟨2739320, by rfl⟩ : syracuseStep 3652427 = 5478641) B5478641
theorem B637879 : Blo 566810 637879 := bstep (se 1 (by rfl) ⟨478409, by rfl⟩ : syracuseStep 637879 = 956819) B956819
theorem B1915865 : Blo 566810 1915865 := bstep (se 2 (by rfl) ⟨718449, by rfl⟩ : syracuseStep 1915865 = 1436899) B1436899
theorem B1457203 : Blo 566810 1457203 := bstep (se 1 (by rfl) ⟨1092902, by rfl⟩ : syracuseStep 1457203 = 2185805) B2185805
theorem B638059 : Blo 566810 638059 := bstep (se 1 (by rfl) ⟨478544, by rfl⟩ : syracuseStep 638059 = 957089) B957089
theorem B2047169 : Blo 566810 2047169 := bstep (se 2 (by rfl) ⟨767688, by rfl⟩ : syracuseStep 2047169 = 1535377) B1535377
theorem B638167 : Blo 566810 638167 := bstep (se 1 (by rfl) ⟨478625, by rfl⟩ : syracuseStep 638167 = 957251) B957251
theorem B2047283 : Blo 566810 2047283 := bstep (se 1 (by rfl) ⟨1535462, by rfl⟩ : syracuseStep 2047283 = 3070925) B3070925
theorem B638347 : Blo 566810 638347 := bstep (se 1 (by rfl) ⟨478760, by rfl⟩ : syracuseStep 638347 = 957521) B957521
theorem B638455 : Blo 566810 638455 := bstep (se 1 (by rfl) ⟨478841, by rfl⟩ : syracuseStep 638455 = 957683) B957683
theorem B3882647 : Blo 566810 3882647 := bstep (se 1 (by rfl) ⟨2911985, by rfl⟩ : syracuseStep 3882647 = 5823971) B5823971
theorem B1916567 : Blo 566810 1916567 := bstep (se 1 (by rfl) ⟨1437425, by rfl⟩ : syracuseStep 1916567 = 2874851) B2874851
theorem B638635 : Blo 566810 638635 := bstep (se 1 (by rfl) ⟨478976, by rfl⟩ : syracuseStep 638635 = 957953) B957953
theorem B638743 : Blo 566810 638743 := bstep (se 1 (by rfl) ⟨479057, by rfl⟩ : syracuseStep 638743 = 958115) B958115
theorem B638923 : Blo 566810 638923 := bstep (se 1 (by rfl) ⟨479192, by rfl⟩ : syracuseStep 638923 = 958385) B958385
theorem B8306705 : Blo 566810 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B639031 : Blo 566810 639031 := bstep (se 1 (by rfl) ⟨479273, by rfl⟩ : syracuseStep 639031 = 958547) B958547
theorem B606295 : Blo 566810 606295 := bstep (se 1 (by rfl) ⟨454721, by rfl⟩ : syracuseStep 606295 = 909443) B909443
theorem B3883139 : Blo 566810 3883139 := bstep (se 1 (by rfl) ⟨2912354, by rfl⟩ : syracuseStep 3883139 = 5824709) B5824709
theorem B1917107 : Blo 566810 1917107 := bstep (se 1 (by rfl) ⟨1437830, by rfl⟩ : syracuseStep 1917107 = 2875661) B2875661
theorem B639211 : Blo 566810 639211 := bstep (se 1 (by rfl) ⟨479408, by rfl⟩ : syracuseStep 639211 = 958817) B958817
theorem B639319 : Blo 566810 639319 := bstep (se 1 (by rfl) ⟨479489, by rfl⟩ : syracuseStep 639319 = 958979) B958979
theorem B3654067 : Blo 566810 3654067 := bstep (se 1 (by rfl) ⟨2740550, by rfl⟩ : syracuseStep 3654067 = 5481101) B5481101
theorem B1917377 : Blo 566810 1917377 := bstep (se 2 (by rfl) ⟨719016, by rfl⟩ : syracuseStep 1917377 = 1438033) B1438033
theorem B639499 : Blo 566810 639499 := bstep (se 1 (by rfl) ⟨479624, by rfl⟩ : syracuseStep 639499 = 959249) B959249
theorem B639607 : Blo 566810 639607 := bstep (se 1 (by rfl) ⟨479705, by rfl⟩ : syracuseStep 639607 = 959411) B959411
theorem B639787 : Blo 566810 639787 := bstep (se 1 (by rfl) ⟨479840, by rfl⟩ : syracuseStep 639787 = 959681) B959681
theorem B13812545 : Blo 566810 13812545 := bstep (se 2 (by rfl) ⟨5179704, by rfl⟩ : syracuseStep 13812545 = 10359409) B10359409
theorem B15582017 : Blo 566810 15582017 := bstep (se 2 (by rfl) ⟨5843256, by rfl⟩ : syracuseStep 15582017 = 11686513) B11686513
theorem B770905 : Blo 566810 770905 := bstep (se 2 (by rfl) ⟨289089, by rfl⟩ : syracuseStep 770905 = 578179) B578179
theorem B607115 : Blo 566810 607115 := bstep (se 1 (by rfl) ⟨455336, by rfl⟩ : syracuseStep 607115 = 910673) B910673
theorem B639895 : Blo 566810 639895 := bstep (se 1 (by rfl) ⟨479921, by rfl⟩ : syracuseStep 639895 = 959843) B959843
theorem B8111027 : Blo 566810 8111027 := bstep (se 1 (by rfl) ⟨6083270, by rfl⟩ : syracuseStep 8111027 = 12166541) B12166541
theorem B1917917 : Blo 566810 1917917 := bstep (se 3 (by rfl) ⟨359609, by rfl⟩ : syracuseStep 1917917 = 719219) B719219
theorem B640075 : Blo 566810 640075 := bstep (se 1 (by rfl) ⟨480056, by rfl⟩ : syracuseStep 640075 = 960113) B960113
theorem B640183 : Blo 566810 640183 := bstep (se 1 (by rfl) ⟨480137, by rfl⟩ : syracuseStep 640183 = 960275) B960275
theorem B1623233 : Blo 566810 1623233 := bstep (se 2 (by rfl) ⟨608712, by rfl⟩ : syracuseStep 1623233 = 1217425) B1217425
theorem B1623347 : Blo 566810 1623347 := bstep (se 1 (by rfl) ⟨1217510, by rfl⟩ : syracuseStep 1623347 = 2435021) B2435021
theorem B640363 : Blo 566810 640363 := bstep (se 1 (by rfl) ⟨480272, by rfl⟩ : syracuseStep 640363 = 960545) B960545
theorem B640471 : Blo 566810 640471 := bstep (se 1 (by rfl) ⟨480353, by rfl⟩ : syracuseStep 640471 = 960707) B960707
theorem B4867715 : Blo 566810 4867715 := bstep (se 1 (by rfl) ⟨3650786, by rfl⟩ : syracuseStep 4867715 = 7301573) B7301573
theorem B640651 : Blo 566810 640651 := bstep (se 1 (by rfl) ⟨480488, by rfl⟩ : syracuseStep 640651 = 960977) B960977
theorem B640759 : Blo 566810 640759 := bstep (se 1 (by rfl) ⟨480569, by rfl⟩ : syracuseStep 640759 = 961139) B961139
theorem B2737937 : Blo 566810 2737937 := bstep (se 2 (by rfl) ⟨1026726, by rfl⟩ : syracuseStep 2737937 = 2053453) B2053453
theorem B4310819 : Blo 566810 4310819 := bstep (se 1 (by rfl) ⟨3233114, by rfl⟩ : syracuseStep 4310819 = 6466229) B6466229
theorem B2312081 : Blo 566810 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B640939 : Blo 566810 640939 := bstep (se 1 (by rfl) ⟨480704, by rfl⟩ : syracuseStep 640939 = 961409) B961409
theorem B4376537 : Blo 566810 4376537 := bstep (se 2 (by rfl) ⟨1641201, by rfl⟩ : syracuseStep 4376537 = 3282403) B3282403
theorem B2050051 : Blo 566810 2050051 := bstep (se 1 (by rfl) ⟨1537538, by rfl⟩ : syracuseStep 2050051 = 3075077) B3075077
theorem B641047 : Blo 566810 641047 := bstep (se 1 (by rfl) ⟨480785, by rfl⟩ : syracuseStep 641047 = 961571) B961571
theorem B4605997 : Blo 566810 4605997 := bstep (se 3 (by rfl) ⟨863624, by rfl⟩ : syracuseStep 4605997 = 1727249) B1727249
theorem B608311 : Blo 566810 608311 := bstep (se 1 (by rfl) ⟨456233, by rfl⟩ : syracuseStep 608311 = 912467) B912467
theorem B1919051 : Blo 566810 1919051 := bstep (se 1 (by rfl) ⟨1439288, by rfl⟩ : syracuseStep 1919051 = 2878577) B2878577
theorem B4376753 : Blo 566810 4376753 := bstep (se 2 (by rfl) ⟨1641282, by rfl⟩ : syracuseStep 4376753 = 3282565) B3282565
theorem B641227 : Blo 566810 641227 := bstep (se 1 (by rfl) ⟨480920, by rfl⟩ : syracuseStep 641227 = 961841) B961841
theorem B608567 : Blo 566810 608567 := bstep (se 1 (by rfl) ⟨456425, by rfl⟩ : syracuseStep 608567 = 912851) B912851
theorem B641335 : Blo 566810 641335 := bstep (se 1 (by rfl) ⟨481001, by rfl⟩ : syracuseStep 641335 = 962003) B962003
theorem B1919321 : Blo 566810 1919321 := bstep (se 2 (by rfl) ⟨719745, by rfl⟩ : syracuseStep 1919321 = 1439491) B1439491
theorem B2312599 : Blo 566810 2312599 := bstep (se 1 (by rfl) ⟨1734449, by rfl⟩ : syracuseStep 2312599 = 3468899) B3468899
theorem B641515 : Blo 566810 641515 := bstep (se 1 (by rfl) ⟨481136, by rfl⟩ : syracuseStep 641515 = 962273) B962273
theorem B641623 : Blo 566810 641623 := bstep (se 1 (by rfl) ⟨481217, by rfl⟩ : syracuseStep 641623 = 962435) B962435
theorem B641803 : Blo 566810 641803 := bstep (se 1 (by rfl) ⟨481352, by rfl⟩ : syracuseStep 641803 = 962705) B962705
theorem B609131 : Blo 566810 609131 := bstep (se 1 (by rfl) ⟨456848, by rfl⟩ : syracuseStep 609131 = 913697) B913697
theorem B641911 : Blo 566810 641911 := bstep (se 1 (by rfl) ⟨481433, by rfl⟩ : syracuseStep 641911 = 962867) B962867
theorem B576439 : Blo 566810 576439 := bstep (se 1 (by rfl) ⟨432329, by rfl⟩ : syracuseStep 576439 = 864659) B864659
theorem B1920023 : Blo 566810 1920023 := bstep (se 1 (by rfl) ⟨1440017, by rfl⟩ : syracuseStep 1920023 = 2880035) B2880035
theorem B642091 : Blo 566810 642091 := bstep (se 1 (by rfl) ⟨481568, by rfl⟩ : syracuseStep 642091 = 963137) B963137
theorem B1363223 : Blo 566810 1363223 := bstep (se 1 (by rfl) ⟨1022417, by rfl⟩ : syracuseStep 1363223 = 2044835) B2044835
theorem B2870801 : Blo 566810 2870801 := bstep (se 2 (by rfl) ⟨1076550, by rfl⟩ : syracuseStep 2870801 = 2153101) B2153101
theorem B1920563 : Blo 566810 1920563 := bstep (se 1 (by rfl) ⟨1440422, by rfl⟩ : syracuseStep 1920563 = 2880845) B2880845
theorem B1363607 : Blo 566810 1363607 := bstep (se 1 (by rfl) ⟨1022705, by rfl⟩ : syracuseStep 1363607 = 2045411) B2045411
theorem B2870963 : Blo 566810 2870963 := bstep (se 1 (by rfl) ⟨2153222, by rfl⟩ : syracuseStep 2870963 = 4306445) B4306445
theorem B1920833 : Blo 566810 1920833 := bstep (se 2 (by rfl) ⟨720312, by rfl⟩ : syracuseStep 1920833 = 1440625) B1440625
theorem B3067723 : Blo 566810 3067723 := bstep (se 1 (by rfl) ⟨2300792, by rfl⟩ : syracuseStep 3067723 = 4601585) B4601585
theorem B1331329 : Blo 566810 1331329 := bstep (se 2 (by rfl) ⟨499248, by rfl⟩ : syracuseStep 1331329 = 998497) B998497
theorem B3068225 : Blo 566810 3068225 := bstep (se 2 (by rfl) ⟨1150584, by rfl⟩ : syracuseStep 3068225 = 2301169) B2301169
theorem B1921373 : Blo 566810 1921373 := bstep (se 3 (by rfl) ⟨360257, by rfl⟩ : syracuseStep 1921373 = 720515) B720515
theorem B3887461 : Blo 566810 3887461 := bstep (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) B728899
theorem B4870691 : Blo 566810 4870691 := bstep (se 1 (by rfl) ⟨3653018, by rfl⟩ : syracuseStep 4870691 = 7306037) B7306037
theorem B807499 : Blo 566810 807499 := bstep (se 1 (by rfl) ⟨605624, by rfl⟩ : syracuseStep 807499 = 1211249) B1211249
theorem B2183773 : Blo 566810 2183773 := bstep (se 3 (by rfl) ⟨409457, by rfl⟩ : syracuseStep 2183773 = 818915) B818915
theorem B1364683 : Blo 566810 1364683 := bstep (se 1 (by rfl) ⟨1023512, by rfl⟩ : syracuseStep 1364683 = 2047025) B2047025
theorem B1823435 : Blo 566810 1823435 := bstep (se 1 (by rfl) ⟨1367576, by rfl⟩ : syracuseStep 1823435 = 2735153) B2735153
theorem B1233623 : Blo 566810 1233623 := bstep (se 1 (by rfl) ⟨925217, by rfl⟩ : syracuseStep 1233623 = 1850435) B1850435
theorem B10343213 : Blo 566810 10343213 := bstep (se 3 (by rfl) ⟨1939352, by rfl⟩ : syracuseStep 10343213 = 3878705) B3878705
theorem B4379741 : Blo 566810 4379741 := bstep (se 3 (by rfl) ⟨821201, by rfl⟩ : syracuseStep 4379741 = 1642403) B1642403
theorem B1299635 : Blo 566810 1299635 := bstep (se 1 (by rfl) ⟨974726, by rfl⟩ : syracuseStep 1299635 = 1949453) B1949453
theorem B1299671 : Blo 566810 1299671 := bstep (se 1 (by rfl) ⟨974753, by rfl⟩ : syracuseStep 1299671 = 1949507) B1949507
theorem B1365299 : Blo 566810 1365299 := bstep (se 1 (by rfl) ⟨1023974, by rfl⟩ : syracuseStep 1365299 = 2047949) B2047949
theorem B1922507 : Blo 566810 1922507 := bstep (se 1 (by rfl) ⟨1441880, by rfl⟩ : syracuseStep 1922507 = 2883761) B2883761
theorem B3233297 : Blo 566810 3233297 := bstep (se 2 (by rfl) ⟨1212486, by rfl⟩ : syracuseStep 3233297 = 2424973) B2424973
theorem B2872907 : Blo 566810 2872907 := bstep (se 1 (by rfl) ⟨2154680, by rfl⟩ : syracuseStep 2872907 = 4309361) B4309361
theorem B2152115 : Blo 566810 2152115 := bstep (se 1 (by rfl) ⟨1614086, by rfl⟩ : syracuseStep 2152115 = 3228173) B3228173
theorem B2152129 : Blo 566810 2152129 := bstep (se 2 (by rfl) ⟨807048, by rfl⟩ : syracuseStep 2152129 = 1614097) B1614097
theorem B1922777 : Blo 566810 1922777 := bstep (se 2 (by rfl) ⟨721041, by rfl⟩ : syracuseStep 1922777 = 1442083) B1442083
theorem B10901465 : Blo 566810 10901465 := bstep (se 2 (by rfl) ⟨4088049, by rfl⟩ : syracuseStep 10901465 = 8176099) B8176099
theorem B3233753 : Blo 566810 3233753 := bstep (se 2 (by rfl) ⟨1212657, by rfl⟩ : syracuseStep 3233753 = 2425315) B2425315
theorem B808985 : Blo 566810 808985 := bstep (se 2 (by rfl) ⟨303369, by rfl⟩ : syracuseStep 808985 = 606739) B606739
theorem B1366067 : Blo 566810 1366067 := bstep (se 1 (by rfl) ⟨1024550, by rfl⟩ : syracuseStep 1366067 = 2049101) B2049101
theorem B1923479 : Blo 566810 1923479 := bstep (se 1 (by rfl) ⟨1442609, by rfl⟩ : syracuseStep 1923479 = 2885219) B2885219
theorem B809623 : Blo 566810 809623 := bstep (se 1 (by rfl) ⟨607217, by rfl⟩ : syracuseStep 809623 = 1214435) B1214435
theorem B1170163 : Blo 566810 1170163 := bstep (se 1 (by rfl) ⟨877622, by rfl⟩ : syracuseStep 1170163 = 1755245) B1755245
theorem B1366807 : Blo 566810 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B1924019 : Blo 566810 1924019 := bstep (se 1 (by rfl) ⟨1443014, by rfl⟩ : syracuseStep 1924019 = 2886029) B2886029
theorem B1825753 : Blo 566810 1825753 := bstep (se 2 (by rfl) ⟨684657, by rfl⟩ : syracuseStep 1825753 = 1369315) B1369315
theorem B4316165 : Blo 566810 4316165 := bstep (se 4 (by rfl) ⟨404640, by rfl⟩ : syracuseStep 4316165 = 809281) B809281
theorem B3070993 : Blo 566810 3070993 := bstep (se 2 (by rfl) ⟨1151622, by rfl⟩ : syracuseStep 3070993 = 2303245) B2303245
theorem B1924289 : Blo 566810 1924289 := bstep (se 2 (by rfl) ⟨721608, by rfl⟩ : syracuseStep 1924289 = 1443217) B1443217
theorem B2874689 : Blo 566810 2874689 := bstep (se 2 (by rfl) ⟨1078008, by rfl⟩ : syracuseStep 2874689 = 2156017) B2156017
theorem B1727833 : Blo 566810 1727833 := bstep (se 2 (by rfl) ⟨647937, by rfl⟩ : syracuseStep 1727833 = 1295875) B1295875
theorem B810329 : Blo 566810 810329 := bstep (se 2 (by rfl) ⟨303873, by rfl⟩ : syracuseStep 810329 = 607747) B607747
theorem B119922061 : Blo 566810 119922061 := bstep (se 3 (by rfl) ⟨22485386, by rfl⟩ : syracuseStep 119922061 = 44970773) B44970773
theorem B810443 : Blo 566810 810443 := bstep (se 1 (by rfl) ⟨607832, by rfl⟩ : syracuseStep 810443 = 1215665) B1215665
theorem B2154059 : Blo 566810 2154059 := bstep (se 1 (by rfl) ⟨1615544, by rfl⟩ : syracuseStep 2154059 = 3231089) B3231089
theorem B2154073 : Blo 566810 2154073 := bstep (se 2 (by rfl) ⟨807777, by rfl⟩ : syracuseStep 2154073 = 1615555) B1615555
theorem B1924829 : Blo 566810 1924829 := bstep (se 3 (by rfl) ⟨360905, by rfl⟩ : syracuseStep 1924829 = 721811) B721811
theorem B18472769 : Blo 566810 18472769 := bstep (se 2 (by rfl) ⟨6927288, by rfl⟩ : syracuseStep 18472769 = 13854577) B13854577
theorem B810967 : Blo 566810 810967 := bstep (se 1 (by rfl) ⟨608225, by rfl⟩ : syracuseStep 810967 = 1216451) B1216451
theorem B2187281 : Blo 566810 2187281 := bstep (se 2 (by rfl) ⟨820230, by rfl⟩ : syracuseStep 2187281 = 1640461) B1640461
theorem B2187395 : Blo 566810 2187395 := bstep (se 1 (by rfl) ⟨1640546, by rfl⟩ : syracuseStep 2187395 = 3281093) B3281093
theorem B2056337 : Blo 566810 2056337 := bstep (se 2 (by rfl) ⟨771126, by rfl⟩ : syracuseStep 2056337 = 1542253) B1542253
theorem B1827137 : Blo 566810 1827137 := bstep (se 2 (by rfl) ⟨685176, by rfl⟩ : syracuseStep 1827137 = 1370353) B1370353
theorem B876887 : Blo 566810 876887 := bstep (se 1 (by rfl) ⟨657665, by rfl⟩ : syracuseStep 876887 = 1315331) B1315331
theorem B2155031 : Blo 566810 2155031 := bstep (se 1 (by rfl) ⟨1616273, by rfl⟩ : syracuseStep 2155031 = 3232547) B3232547
theorem B1532609 : Blo 566810 1532609 := bstep (se 2 (by rfl) ⟨574728, by rfl⟩ : syracuseStep 1532609 = 1149457) B1149457
theorem B44360405 : Blo 566810 44360405 := bstep (se 7 (by rfl) ⟨519848, by rfl⟩ : syracuseStep 44360405 = 1039697) B1039697
theorem B811787 : Blo 566810 811787 := bstep (se 1 (by rfl) ⟨608840, by rfl⟩ : syracuseStep 811787 = 1217681) B1217681
theorem B1532695 : Blo 566810 1532695 := bstep (se 1 (by rfl) ⟨1149521, by rfl⟩ : syracuseStep 1532695 = 2299043) B2299043
theorem B2908973 : Blo 566810 2908973 := bstep (se 3 (by rfl) ⟨545432, by rfl⟩ : syracuseStep 2908973 = 1090865) B1090865
theorem B1532737 : Blo 566810 1532737 := bstep (se 2 (by rfl) ⟨574776, by rfl⟩ : syracuseStep 1532737 = 1149553) B1149553
theorem B1925963 : Blo 566810 1925963 := bstep (se 1 (by rfl) ⟨1444472, by rfl⟩ : syracuseStep 1925963 = 2888945) B2888945
theorem B1172569 : Blo 566810 1172569 := bstep (se 2 (by rfl) ⟨439713, by rfl⟩ : syracuseStep 1172569 = 879427) B879427
theorem B1926233 : Blo 566810 1926233 := bstep (se 2 (by rfl) ⟨722337, by rfl⟩ : syracuseStep 1926233 = 1444675) B1444675
theorem B910487 : Blo 566810 910487 := bstep (se 1 (by rfl) ⟨682865, by rfl⟩ : syracuseStep 910487 = 1365731) B1365731
theorem B2876633 : Blo 566810 2876633 := bstep (se 2 (by rfl) ⟨1078737, by rfl⟩ : syracuseStep 2876633 = 2157475) B2157475
theorem B3073241 : Blo 566810 3073241 := bstep (se 2 (by rfl) ⟨1152465, by rfl⟩ : syracuseStep 3073241 = 2304931) B2304931
theorem B976151 : Blo 566810 976151 := bstep (se 1 (by rfl) ⟨732113, by rfl⟩ : syracuseStep 976151 = 1464227) B1464227
theorem B1434955 : Blo 566810 1434955 := bstep (se 1 (by rfl) ⟨1076216, by rfl⟩ : syracuseStep 1434955 = 2152433) B2152433
theorem B4318595 : Blo 566810 4318595 := bstep (se 1 (by rfl) ⟨3238946, by rfl⟩ : syracuseStep 4318595 = 6477893) B6477893
theorem B681419 : Blo 566810 681419 := bstep (se 1 (by rfl) ⟨511064, by rfl⟩ : syracuseStep 681419 = 1022129) B1022129
theorem B1435097 : Blo 566810 1435097 := bstep (se 2 (by rfl) ⟨538161, by rfl⟩ : syracuseStep 1435097 = 1076323) B1076323
theorem B1730123 : Blo 566810 1730123 := bstep (se 1 (by rfl) ⟨1297592, by rfl⟩ : syracuseStep 1730123 = 2595185) B2595185
theorem B2156291 : Blo 566810 2156291 := bstep (se 1 (by rfl) ⟨1617218, by rfl⟩ : syracuseStep 2156291 = 3234437) B3234437
theorem B1435927 : Blo 566810 1435927 := bstep (se 1 (by rfl) ⟨1076945, by rfl⟩ : syracuseStep 1435927 = 2153891) B2153891
theorem B682327 : Blo 566810 682327 := bstep (se 1 (by rfl) ⟨511745, by rfl⟩ : syracuseStep 682327 = 1023491) B1023491
theorem B4614691 : Blo 566810 4614691 := bstep (se 1 (by rfl) ⟨3461018, by rfl⟩ : syracuseStep 4614691 = 6922037) B6922037
theorem B1370699 : Blo 566810 1370699 := bstep (se 1 (by rfl) ⟨1028024, by rfl⟩ : syracuseStep 1370699 = 2056049) B2056049
theorem B1436363 : Blo 566810 1436363 := bstep (se 1 (by rfl) ⟨1077272, by rfl⟩ : syracuseStep 1436363 = 2154545) B2154545
theorem B2878253 : Blo 566810 2878253 := bstep (se 3 (by rfl) ⟨539672, by rfl⟩ : syracuseStep 2878253 = 1079345) B1079345
theorem B1370969 : Blo 566810 1370969 := bstep (se 2 (by rfl) ⟨514113, by rfl⟩ : syracuseStep 1370969 = 1028227) B1028227
theorem B1436737 : Blo 566810 1436737 := bstep (se 2 (by rfl) ⟨538776, by rfl⟩ : syracuseStep 1436737 = 1077553) B1077553
theorem B1731677 : Blo 566810 1731677 := bstep (se 3 (by rfl) ⟨324689, by rfl⟩ : syracuseStep 1731677 = 649379) B649379
theorem B3239129 : Blo 566810 3239129 := bstep (se 2 (by rfl) ⟨1214673, by rfl⟩ : syracuseStep 3239129 = 2429347) B2429347
theorem B650743 : Blo 566810 650743 := bstep (se 1 (by rfl) ⟨488057, by rfl⟩ : syracuseStep 650743 = 976115) B976115
theorem B1437335 : Blo 566810 1437335 := bstep (se 1 (by rfl) ⟨1078001, by rfl⟩ : syracuseStep 1437335 = 2156003) B2156003
theorem B1076915 : Blo 566810 1076915 := bstep (se 1 (by rfl) ⟨807686, by rfl⟩ : syracuseStep 1076915 = 1615373) B1615373
theorem B1077067 : Blo 566810 1077067 := bstep (se 1 (by rfl) ⟨807800, by rfl⟩ : syracuseStep 1077067 = 1615601) B1615601
theorem B4091741 : Blo 566810 4091741 := bstep (se 3 (by rfl) ⟨767201, by rfl⟩ : syracuseStep 4091741 = 1534403) B1534403
theorem B3469463 : Blo 566810 3469463 := bstep (se 1 (by rfl) ⟨2602097, by rfl⟩ : syracuseStep 3469463 = 5204195) B5204195
theorem B1077401 : Blo 566810 1077401 := bstep (se 2 (by rfl) ⟨404025, by rfl⟩ : syracuseStep 1077401 = 808051) B808051
theorem B684235 : Blo 566810 684235 := bstep (se 1 (by rfl) ⟨513176, by rfl⟩ : syracuseStep 684235 = 1026353) B1026353
theorem B1994969 : Blo 566810 1994969 := bstep (se 2 (by rfl) ⟨748113, by rfl⟩ : syracuseStep 1994969 = 1496227) B1496227
theorem B1438145 : Blo 566810 1438145 := bstep (se 2 (by rfl) ⟨539304, by rfl⟩ : syracuseStep 1438145 = 1078609) B1078609
theorem B4321997 : Blo 566810 4321997 := bstep (se 3 (by rfl) ⟨810374, by rfl⟩ : syracuseStep 4321997 = 1620749) B1620749
theorem B1078039 : Blo 566810 1078039 := bstep (se 1 (by rfl) ⟨808529, by rfl⟩ : syracuseStep 1078039 = 1617059) B1617059
theorem B2159405 : Blo 566810 2159405 := bstep (se 3 (by rfl) ⟨404888, by rfl⟩ : syracuseStep 2159405 = 809777) B809777
theorem B3240769 : Blo 566810 3240769 := bstep (se 2 (by rfl) ⟨1215288, by rfl⟩ : syracuseStep 3240769 = 2430577) B2430577
theorem B717655 : Blo 566810 717655 := bstep (se 1 (by rfl) ⟨538241, by rfl⟩ : syracuseStep 717655 = 1076483) B1076483
theorem B2421677 : Blo 566810 2421677 := bstep (se 3 (by rfl) ⟨454064, by rfl⟩ : syracuseStep 2421677 = 908129) B908129
theorem B1438681 : Blo 566810 1438681 := bstep (se 2 (by rfl) ⟨539505, by rfl⟩ : syracuseStep 1438681 = 1079011) B1079011
theorem B10515491 : Blo 566810 10515491 := bstep (se 1 (by rfl) ⟨7886618, by rfl⟩ : syracuseStep 10515491 = 15773237) B15773237
theorem B4322483 : Blo 566810 4322483 := bstep (se 1 (by rfl) ⟨3241862, by rfl⟩ : syracuseStep 4322483 = 6483725) B6483725
theorem B1275353 : Blo 566810 1275353 := bstep (se 2 (by rfl) ⟨478257, by rfl⟩ : syracuseStep 1275353 = 956515) B956515
theorem B4388357 : Blo 566810 4388357 := bstep (se 4 (by rfl) ⟨411408, by rfl⟩ : syracuseStep 4388357 = 822817) B822817
theorem B1275443 : Blo 566810 1275443 := bstep (se 1 (by rfl) ⟨956582, by rfl⟩ : syracuseStep 1275443 = 1913165) B1913165
theorem B2160179 : Blo 566810 2160179 := bstep (se 1 (by rfl) ⟨1620134, by rfl⟩ : syracuseStep 2160179 = 3240269) B3240269
theorem B1078859 : Blo 566810 1078859 := bstep (se 1 (by rfl) ⟨809144, by rfl⟩ : syracuseStep 1078859 = 1618289) B1618289
theorem B1275479 : Blo 566810 1275479 := bstep (se 1 (by rfl) ⟨956609, by rfl⟩ : syracuseStep 1275479 = 1913219) B1913219
theorem B1078913 : Blo 566810 1078913 := bstep (se 2 (by rfl) ⟨404592, by rfl⟩ : syracuseStep 1078913 = 809185) B809185
theorem B1275659 : Blo 566810 1275659 := bstep (se 1 (by rfl) ⟨956744, by rfl⟩ : syracuseStep 1275659 = 1913489) B1913489
theorem B1275713 : Blo 566810 1275713 := bstep (se 2 (by rfl) ⟨478392, by rfl⟩ : syracuseStep 1275713 = 956785) B956785
theorem B149157773 : Blo 566810 149157773 := bstep (se 3 (by rfl) ⟨27967082, by rfl⟩ : syracuseStep 149157773 = 55934165) B55934165
theorem B12318641 : Blo 566810 12318641 := bstep (se 2 (by rfl) ⟨4619490, by rfl⟩ : syracuseStep 12318641 = 9238981) B9238981
theorem B1275929 : Blo 566810 1275929 := bstep (se 2 (by rfl) ⟨478473, by rfl⟩ : syracuseStep 1275929 = 956947) B956947
theorem B1439795 : Blo 566810 1439795 := bstep (se 1 (by rfl) ⟨1079846, by rfl⟩ : syracuseStep 1439795 = 2159693) B2159693
theorem B1276019 : Blo 566810 1276019 := bstep (se 1 (by rfl) ⟨957014, by rfl⟩ : syracuseStep 1276019 = 1914029) B1914029
theorem B1276055 : Blo 566810 1276055 := bstep (se 1 (by rfl) ⟨957041, by rfl⟩ : syracuseStep 1276055 = 1914083) B1914083
theorem B4618457 : Blo 566810 4618457 := bstep (se 2 (by rfl) ⟨1731921, by rfl⟩ : syracuseStep 4618457 = 3463843) B3463843
theorem B1276235 : Blo 566810 1276235 := bstep (se 1 (by rfl) ⟨957176, by rfl⟩ : syracuseStep 1276235 = 1914353) B1914353
theorem B850265 : Blo 566810 850265 := bstep (se 2 (by rfl) ⟨318849, by rfl⟩ : syracuseStep 850265 = 637699) B637699
theorem B1440089 : Blo 566810 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B1276289 : Blo 566810 1276289 := bstep (se 2 (by rfl) ⟨478608, by rfl⟩ : syracuseStep 1276289 = 957217) B957217
theorem B2193809 : Blo 566810 2193809 := bstep (se 2 (by rfl) ⟨822678, by rfl⟩ : syracuseStep 2193809 = 1645357) B1645357
theorem B850379 : Blo 566810 850379 := bstep (se 1 (by rfl) ⟨637784, by rfl⟩ : syracuseStep 850379 = 1275569) B1275569
theorem B850391 : Blo 566810 850391 := bstep (se 1 (by rfl) ⟨637793, by rfl⟩ : syracuseStep 850391 = 1275587) B1275587
theorem B719371 : Blo 566810 719371 := bstep (se 1 (by rfl) ⟨539528, by rfl⟩ : syracuseStep 719371 = 1079057) B1079057
theorem B1079831 : Blo 566810 1079831 := bstep (se 1 (by rfl) ⟨809873, by rfl⟩ : syracuseStep 1079831 = 1619747) B1619747
theorem B850457 : Blo 566810 850457 := bstep (se 2 (by rfl) ⟨318921, by rfl⟩ : syracuseStep 850457 = 637843) B637843
theorem B4094509 : Blo 566810 4094509 := bstep (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) B1535441
theorem B1276505 : Blo 566810 1276505 := bstep (se 2 (by rfl) ⟨478689, by rfl⟩ : syracuseStep 1276505 = 957379) B957379
theorem B2882141 : Blo 566810 2882141 := bstep (se 3 (by rfl) ⟨540401, by rfl⟩ : syracuseStep 2882141 = 1080803) B1080803
theorem B4323941 : Blo 566810 4323941 := bstep (se 4 (by rfl) ⟨405369, by rfl⟩ : syracuseStep 4323941 = 810739) B810739
theorem B850571 : Blo 566810 850571 := bstep (se 1 (by rfl) ⟨637928, by rfl⟩ : syracuseStep 850571 = 1275857) B1275857
theorem B850583 : Blo 566810 850583 := bstep (se 1 (by rfl) ⟨637937, by rfl⟩ : syracuseStep 850583 = 1275875) B1275875
theorem B1276595 : Blo 566810 1276595 := bstep (se 1 (by rfl) ⟨957446, by rfl⟩ : syracuseStep 1276595 = 1914893) B1914893
theorem B1276631 : Blo 566810 1276631 := bstep (se 1 (by rfl) ⟨957473, by rfl⟩ : syracuseStep 1276631 = 1914947) B1914947
theorem B850649 : Blo 566810 850649 := bstep (se 2 (by rfl) ⟨318993, by rfl⟩ : syracuseStep 850649 = 637987) B637987
theorem B850763 : Blo 566810 850763 := bstep (se 1 (by rfl) ⟨638072, by rfl⟩ : syracuseStep 850763 = 1276145) B1276145
theorem B850775 : Blo 566810 850775 := bstep (se 1 (by rfl) ⟨638081, by rfl⟩ : syracuseStep 850775 = 1276163) B1276163
theorem B2423641 : Blo 566810 2423641 := bstep (se 2 (by rfl) ⟨908865, by rfl⟩ : syracuseStep 2423641 = 1817731) B1817731
theorem B1276811 : Blo 566810 1276811 := bstep (se 1 (by rfl) ⟨957608, by rfl⟩ : syracuseStep 1276811 = 1915217) B1915217
theorem B850841 : Blo 566810 850841 := bstep (se 2 (by rfl) ⟨319065, by rfl⟩ : syracuseStep 850841 = 638131) B638131
theorem B1276865 : Blo 566810 1276865 := bstep (se 2 (by rfl) ⟨478824, by rfl⟩ : syracuseStep 1276865 = 957649) B957649
theorem B1211393 : Blo 566810 1211393 := bstep (se 2 (by rfl) ⟨454272, by rfl⟩ : syracuseStep 1211393 = 908545) B908545
theorem B2161667 : Blo 566810 2161667 := bstep (se 1 (by rfl) ⟨1621250, by rfl⟩ : syracuseStep 2161667 = 3242501) B3242501
theorem B850955 : Blo 566810 850955 := bstep (se 1 (by rfl) ⟨638216, by rfl⟩ : syracuseStep 850955 = 1276433) B1276433
theorem B850967 : Blo 566810 850967 := bstep (se 1 (by rfl) ⟨638225, by rfl⟩ : syracuseStep 850967 = 1276451) B1276451
theorem B1080371 : Blo 566810 1080371 := bstep (se 1 (by rfl) ⟨810278, by rfl⟩ : syracuseStep 1080371 = 1620557) B1620557
theorem B4324427 : Blo 566810 4324427 := bstep (se 1 (by rfl) ⟨3243320, by rfl⟩ : syracuseStep 4324427 = 6486641) B6486641
theorem B851033 : Blo 566810 851033 := bstep (se 2 (by rfl) ⟨319137, by rfl⟩ : syracuseStep 851033 = 638275) B638275
theorem B1277081 : Blo 566810 1277081 := bstep (se 2 (by rfl) ⟨478905, by rfl⟩ : syracuseStep 1277081 = 957811) B957811
theorem B851147 : Blo 566810 851147 := bstep (se 1 (by rfl) ⟨638360, by rfl⟩ : syracuseStep 851147 = 1276721) B1276721
theorem B851159 : Blo 566810 851159 := bstep (se 1 (by rfl) ⟨638369, by rfl⟩ : syracuseStep 851159 = 1276739) B1276739
theorem B1277171 : Blo 566810 1277171 := bstep (se 1 (by rfl) ⟨957878, by rfl⟩ : syracuseStep 1277171 = 1915757) B1915757
theorem B1277207 : Blo 566810 1277207 := bstep (se 1 (by rfl) ⟨957905, by rfl⟩ : syracuseStep 1277207 = 1915811) B1915811
theorem B851225 : Blo 566810 851225 := bstep (se 2 (by rfl) ⟨319209, by rfl⟩ : syracuseStep 851225 = 638419) B638419
theorem B1211735 : Blo 566810 1211735 := bstep (se 1 (by rfl) ⟨908801, by rfl⟩ : syracuseStep 1211735 = 1817603) B1817603
theorem B851339 : Blo 566810 851339 := bstep (se 1 (by rfl) ⟨638504, by rfl⟩ : syracuseStep 851339 = 1277009) B1277009
theorem B851351 : Blo 566810 851351 := bstep (se 1 (by rfl) ⟨638513, by rfl⟩ : syracuseStep 851351 = 1277027) B1277027
theorem B1277387 : Blo 566810 1277387 := bstep (se 1 (by rfl) ⟨958040, by rfl⟩ : syracuseStep 1277387 = 1916081) B1916081
theorem B2162123 : Blo 566810 2162123 := bstep (se 1 (by rfl) ⟨1621592, by rfl⟩ : syracuseStep 2162123 = 3243185) B3243185
theorem B720343 : Blo 566810 720343 := bstep (se 1 (by rfl) ⟨540257, by rfl⟩ : syracuseStep 720343 = 1080515) B1080515
theorem B851417 : Blo 566810 851417 := bstep (se 2 (by rfl) ⟨319281, by rfl⟩ : syracuseStep 851417 = 638563) B638563
theorem B1277441 : Blo 566810 1277441 := bstep (se 2 (by rfl) ⟨479040, by rfl⟩ : syracuseStep 1277441 = 958081) B958081
theorem B1080857 : Blo 566810 1080857 := bstep (se 2 (by rfl) ⟨405321, by rfl⟩ : syracuseStep 1080857 = 810643) B810643
theorem B851531 : Blo 566810 851531 := bstep (se 1 (by rfl) ⟨638648, by rfl⟩ : syracuseStep 851531 = 1277297) B1277297
theorem B851543 : Blo 566810 851543 := bstep (se 1 (by rfl) ⟨638657, by rfl⟩ : syracuseStep 851543 = 1277315) B1277315
theorem B1212043 : Blo 566810 1212043 := bstep (se 1 (by rfl) ⟨909032, by rfl⟩ : syracuseStep 1212043 = 1818065) B1818065
theorem B2162321 : Blo 566810 2162321 := bstep (se 2 (by rfl) ⟨810870, by rfl⟩ : syracuseStep 2162321 = 1621741) B1621741
theorem B851609 : Blo 566810 851609 := bstep (se 2 (by rfl) ⟨319353, by rfl⟩ : syracuseStep 851609 = 638707) B638707
theorem B1277657 : Blo 566810 1277657 := bstep (se 2 (by rfl) ⟨479121, by rfl⟩ : syracuseStep 1277657 = 958243) B958243
theorem B851723 : Blo 566810 851723 := bstep (se 1 (by rfl) ⟨638792, by rfl⟩ : syracuseStep 851723 = 1277585) B1277585
theorem B2424599 : Blo 566810 2424599 := bstep (se 1 (by rfl) ⟨1818449, by rfl⟩ : syracuseStep 2424599 = 3636899) B3636899
theorem B851735 : Blo 566810 851735 := bstep (se 1 (by rfl) ⟨638801, by rfl⟩ : syracuseStep 851735 = 1277603) B1277603
theorem B1277747 : Blo 566810 1277747 := bstep (se 1 (by rfl) ⟨958310, by rfl⟩ : syracuseStep 1277747 = 1916621) B1916621
theorem B1277783 : Blo 566810 1277783 := bstep (se 1 (by rfl) ⟨958337, by rfl⟩ : syracuseStep 1277783 = 1916675) B1916675
theorem B851801 : Blo 566810 851801 := bstep (se 2 (by rfl) ⟨319425, by rfl⟩ : syracuseStep 851801 = 638851) B638851
theorem B851915 : Blo 566810 851915 := bstep (se 1 (by rfl) ⟨638936, by rfl⟩ : syracuseStep 851915 = 1277873) B1277873
theorem B1441739 : Blo 566810 1441739 := bstep (se 1 (by rfl) ⟨1081304, by rfl⟩ : syracuseStep 1441739 = 2162609) B2162609
theorem B851927 : Blo 566810 851927 := bstep (se 1 (by rfl) ⟨638945, by rfl⟩ : syracuseStep 851927 = 1277891) B1277891
theorem B851975 : Blo 566810 851975 := bstep (se 1 (by rfl) ⟨638981, by rfl⟩ : syracuseStep 851975 = 1277963) B1277963
theorem B5537803 : Blo 566810 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B4325399 : Blo 566810 4325399 := bstep (se 1 (by rfl) ⟨3244049, by rfl⟩ : syracuseStep 4325399 = 6488099) B6488099
theorem B852011 : Blo 566810 852011 := bstep (se 1 (by rfl) ⟨639008, by rfl⟩ : syracuseStep 852011 = 1278017) B1278017
theorem B5832749 : Blo 566810 5832749 := bstep (se 3 (by rfl) ⟨1093640, by rfl⟩ : syracuseStep 5832749 = 2187281) B2187281
theorem B852041 : Blo 566810 852041 := bstep (se 2 (by rfl) ⟨319515, by rfl⟩ : syracuseStep 852041 = 639031) B639031
theorem B2588759 : Blo 566810 2588759 := bstep (se 1 (by rfl) ⟨1941569, by rfl⟩ : syracuseStep 2588759 = 3883139) B3883139
theorem B1278071 : Blo 566810 1278071 := bstep (se 1 (by rfl) ⟨958553, by rfl⟩ : syracuseStep 1278071 = 1917107) B1917107
theorem B2162807 : Blo 566810 2162807 := bstep (se 1 (by rfl) ⟨1622105, by rfl⟩ : syracuseStep 2162807 = 3244211) B3244211
theorem B852155 : Blo 566810 852155 := bstep (se 1 (by rfl) ⟨639116, by rfl⟩ : syracuseStep 852155 = 1278233) B1278233
theorem B852215 : Blo 566810 852215 := bstep (se 1 (by rfl) ⟨639161, by rfl⟩ : syracuseStep 852215 = 1278323) B1278323
theorem B852239 : Blo 566810 852239 := bstep (se 1 (by rfl) ⟨639179, by rfl⟩ : syracuseStep 852239 = 1278359) B1278359
theorem B1442063 : Blo 566810 1442063 := bstep (se 1 (by rfl) ⟨1081547, by rfl⟩ : syracuseStep 1442063 = 2163095) B2163095
theorem B1278251 : Blo 566810 1278251 := bstep (se 1 (by rfl) ⟨958688, by rfl⟩ : syracuseStep 1278251 = 1917377) B1917377
theorem B852281 : Blo 566810 852281 := bstep (se 2 (by rfl) ⟨319605, by rfl⟩ : syracuseStep 852281 = 639211) B639211
theorem B852359 : Blo 566810 852359 := bstep (se 1 (by rfl) ⟨639269, by rfl⟩ : syracuseStep 852359 = 1278539) B1278539
theorem B1442195 : Blo 566810 1442195 := bstep (se 1 (by rfl) ⟨1081646, by rfl⟩ : syracuseStep 1442195 = 2163293) B2163293
theorem B852395 : Blo 566810 852395 := bstep (se 1 (by rfl) ⟨639296, by rfl⟩ : syracuseStep 852395 = 1278593) B1278593
theorem B852425 : Blo 566810 852425 := bstep (se 2 (by rfl) ⟨319659, by rfl⟩ : syracuseStep 852425 = 639319) B639319
theorem B4850219 : Blo 566810 4850219 := bstep (se 1 (by rfl) ⟨3637664, by rfl⟩ : syracuseStep 4850219 = 7275329) B7275329
theorem B9208363 : Blo 566810 9208363 := bstep (se 1 (by rfl) ⟨6906272, by rfl⟩ : syracuseStep 9208363 = 13812545) B13812545
theorem B10388011 : Blo 566810 10388011 := bstep (se 1 (by rfl) ⟨7791008, by rfl⟩ : syracuseStep 10388011 = 15582017) B15582017
theorem B852539 : Blo 566810 852539 := bstep (se 1 (by rfl) ⟨639404, by rfl⟩ : syracuseStep 852539 = 1278809) B1278809
theorem B852599 : Blo 566810 852599 := bstep (se 1 (by rfl) ⟨639449, by rfl⟩ : syracuseStep 852599 = 1278899) B1278899
theorem B721543 : Blo 566810 721543 := bstep (se 1 (by rfl) ⟨541157, by rfl⟩ : syracuseStep 721543 = 1082315) B1082315
theorem B852623 : Blo 566810 852623 := bstep (se 1 (by rfl) ⟨639467, by rfl⟩ : syracuseStep 852623 = 1278935) B1278935
theorem B1278611 : Blo 566810 1278611 := bstep (se 1 (by rfl) ⟨958958, by rfl⟩ : syracuseStep 1278611 = 1917917) B1917917
theorem B852665 : Blo 566810 852665 := bstep (se 2 (by rfl) ⟨319749, by rfl⟩ : syracuseStep 852665 = 639499) B639499
theorem B1278665 : Blo 566810 1278665 := bstep (se 2 (by rfl) ⟨479499, by rfl⟩ : syracuseStep 1278665 = 958999) B958999
theorem B852743 : Blo 566810 852743 := bstep (se 1 (by rfl) ⟨639557, by rfl⟩ : syracuseStep 852743 = 1279115) B1279115
theorem B8782627 : Blo 566810 8782627 := bstep (se 1 (by rfl) ⟨6586970, by rfl⟩ : syracuseStep 8782627 = 13173941) B13173941
theorem B852779 : Blo 566810 852779 := bstep (se 1 (by rfl) ⟨639584, by rfl⟩ : syracuseStep 852779 = 1279169) B1279169
theorem B1082155 : Blo 566810 1082155 := bstep (se 1 (by rfl) ⟨811616, by rfl⟩ : syracuseStep 1082155 = 1623233) B1623233
theorem B852809 : Blo 566810 852809 := bstep (se 2 (by rfl) ⟨319803, by rfl⟩ : syracuseStep 852809 = 639607) B639607
theorem B1082231 : Blo 566810 1082231 := bstep (se 1 (by rfl) ⟨811673, by rfl⟩ : syracuseStep 1082231 = 1623347) B1623347
theorem B852923 : Blo 566810 852923 := bstep (se 1 (by rfl) ⟨639692, by rfl⟩ : syracuseStep 852923 = 1279385) B1279385
theorem B852983 : Blo 566810 852983 := bstep (se 1 (by rfl) ⟨639737, by rfl⟩ : syracuseStep 852983 = 1279475) B1279475
theorem B3277835 : Blo 566810 3277835 := bstep (se 1 (by rfl) ⟨2458376, by rfl⟩ : syracuseStep 3277835 = 4916753) B4916753
theorem B853007 : Blo 566810 853007 := bstep (se 1 (by rfl) ⟨639755, by rfl⟩ : syracuseStep 853007 = 1279511) B1279511
theorem B721963 : Blo 566810 721963 := bstep (se 1 (by rfl) ⟨541472, by rfl⟩ : syracuseStep 721963 = 1082945) B1082945
theorem B853049 : Blo 566810 853049 := bstep (se 2 (by rfl) ⟨319893, by rfl⟩ : syracuseStep 853049 = 639787) B639787
theorem B2163779 : Blo 566810 2163779 := bstep (se 1 (by rfl) ⟨1622834, by rfl⟩ : syracuseStep 2163779 = 3245669) B3245669
theorem B3245143 : Blo 566810 3245143 := bstep (se 1 (by rfl) ⟨2433857, by rfl⟩ : syracuseStep 3245143 = 4867715) B4867715
theorem B853127 : Blo 566810 853127 := bstep (se 1 (by rfl) ⟨639845, by rfl⟩ : syracuseStep 853127 = 1279691) B1279691
theorem B853163 : Blo 566810 853163 := bstep (se 1 (by rfl) ⟨639872, by rfl⟩ : syracuseStep 853163 = 1279745) B1279745
theorem B853193 : Blo 566810 853193 := bstep (se 2 (by rfl) ⟨319947, by rfl⟩ : syracuseStep 853193 = 639895) B639895
theorem B1541387 : Blo 566810 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B722191 : Blo 566810 722191 := bstep (se 1 (by rfl) ⟨541643, by rfl⟩ : syracuseStep 722191 = 1083287) B1083287
theorem B2917691 : Blo 566810 2917691 := bstep (se 1 (by rfl) ⟨2188268, by rfl⟩ : syracuseStep 2917691 = 4376537) B4376537
theorem B853307 : Blo 566810 853307 := bstep (se 1 (by rfl) ⟨639980, by rfl⟩ : syracuseStep 853307 = 1279961) B1279961
theorem B853367 : Blo 566810 853367 := bstep (se 1 (by rfl) ⟨640025, by rfl⟩ : syracuseStep 853367 = 1280051) B1280051
theorem B1279367 : Blo 566810 1279367 := bstep (se 1 (by rfl) ⟨959525, by rfl⟩ : syracuseStep 1279367 = 1919051) B1919051
theorem B853391 : Blo 566810 853391 := bstep (se 1 (by rfl) ⟨640043, by rfl⟩ : syracuseStep 853391 = 1280087) B1280087
theorem B853433 : Blo 566810 853433 := bstep (se 2 (by rfl) ⟨320037, by rfl⟩ : syracuseStep 853433 = 640075) B640075
theorem B2917835 : Blo 566810 2917835 := bstep (se 1 (by rfl) ⟨2188376, by rfl⟩ : syracuseStep 2917835 = 4376753) B4376753
theorem B1443329 : Blo 566810 1443329 := bstep (se 2 (by rfl) ⟨541248, by rfl⟩ : syracuseStep 1443329 = 1082497) B1082497
theorem B853511 : Blo 566810 853511 := bstep (se 1 (by rfl) ⟨640133, by rfl⟩ : syracuseStep 853511 = 1280267) B1280267
theorem B853547 : Blo 566810 853547 := bstep (se 1 (by rfl) ⟨640160, by rfl⟩ : syracuseStep 853547 = 1280321) B1280321
theorem B1279547 : Blo 566810 1279547 := bstep (se 1 (by rfl) ⟨959660, by rfl⟩ : syracuseStep 1279547 = 1919321) B1919321
theorem B853577 : Blo 566810 853577 := bstep (se 2 (by rfl) ⟨320091, by rfl⟩ : syracuseStep 853577 = 640183) B640183
theorem B1279673 : Blo 566810 1279673 := bstep (se 2 (by rfl) ⟨479877, by rfl⟩ : syracuseStep 1279673 = 959755) B959755
theorem B853691 : Blo 566810 853691 := bstep (se 1 (by rfl) ⟨640268, by rfl⟩ : syracuseStep 853691 = 1280537) B1280537
theorem B853751 : Blo 566810 853751 := bstep (se 1 (by rfl) ⟨640313, by rfl⟩ : syracuseStep 853751 = 1280627) B1280627
theorem B853775 : Blo 566810 853775 := bstep (se 1 (by rfl) ⟨640331, by rfl⟩ : syracuseStep 853775 = 1280663) B1280663
theorem B3639077 : Blo 566810 3639077 := bstep (se 4 (by rfl) ⟨341163, by rfl⟩ : syracuseStep 3639077 = 682327) B682327
theorem B853817 : Blo 566810 853817 := bstep (se 2 (by rfl) ⟨320181, by rfl⟩ : syracuseStep 853817 = 640363) B640363
theorem B1443703 : Blo 566810 1443703 := bstep (se 1 (by rfl) ⟨1082777, by rfl⟩ : syracuseStep 1443703 = 2165555) B2165555
theorem B853895 : Blo 566810 853895 := bstep (se 1 (by rfl) ⟨640421, by rfl⟩ : syracuseStep 853895 = 1280843) B1280843
theorem B853931 : Blo 566810 853931 := bstep (se 1 (by rfl) ⟨640448, by rfl⟩ : syracuseStep 853931 = 1280897) B1280897
theorem B853961 : Blo 566810 853961 := bstep (se 2 (by rfl) ⟨320235, by rfl⟩ : syracuseStep 853961 = 640471) B640471
theorem B1280015 : Blo 566810 1280015 := bstep (se 1 (by rfl) ⟨960011, by rfl⟩ : syracuseStep 1280015 = 1920023) B1920023
theorem B2164765 : Blo 566810 2164765 := bstep (se 3 (by rfl) ⟨405893, by rfl⟩ : syracuseStep 2164765 = 811787) B811787
theorem B1280033 : Blo 566810 1280033 := bstep (se 2 (by rfl) ⟨480012, by rfl⟩ : syracuseStep 1280033 = 960025) B960025
theorem B854075 : Blo 566810 854075 := bstep (se 1 (by rfl) ⟨640556, by rfl⟩ : syracuseStep 854075 = 1281113) B1281113
theorem B854135 : Blo 566810 854135 := bstep (se 1 (by rfl) ⟨640601, by rfl⟩ : syracuseStep 854135 = 1281203) B1281203
theorem B854159 : Blo 566810 854159 := bstep (se 1 (by rfl) ⟨640619, by rfl⟩ : syracuseStep 854159 = 1281239) B1281239
theorem B854201 : Blo 566810 854201 := bstep (se 2 (by rfl) ⟨320325, by rfl⟩ : syracuseStep 854201 = 640651) B640651
theorem B854279 : Blo 566810 854279 := bstep (se 1 (by rfl) ⟨640709, by rfl⟩ : syracuseStep 854279 = 1281419) B1281419
theorem B11634961 : Blo 566810 11634961 := bstep (se 2 (by rfl) ⟨4363110, by rfl⟩ : syracuseStep 11634961 = 8726221) B8726221
theorem B854315 : Blo 566810 854315 := bstep (se 1 (by rfl) ⟨640736, by rfl⟩ : syracuseStep 854315 = 1281473) B1281473
theorem B1444139 : Blo 566810 1444139 := bstep (se 1 (by rfl) ⟨1083104, by rfl⟩ : syracuseStep 1444139 = 2166209) B2166209
theorem B854345 : Blo 566810 854345 := bstep (se 2 (by rfl) ⟨320379, by rfl⟩ : syracuseStep 854345 = 640759) B640759
theorem B1280375 : Blo 566810 1280375 := bstep (se 1 (by rfl) ⟨960281, by rfl⟩ : syracuseStep 1280375 = 1920563) B1920563
theorem B854459 : Blo 566810 854459 := bstep (se 1 (by rfl) ⟨640844, by rfl⟩ : syracuseStep 854459 = 1281689) B1281689
theorem B21629405 : Blo 566810 21629405 := bstep (se 3 (by rfl) ⟨4055513, by rfl⟩ : syracuseStep 21629405 = 8111027) B8111027
theorem B854519 : Blo 566810 854519 := bstep (se 1 (by rfl) ⟨640889, by rfl⟩ : syracuseStep 854519 = 1281779) B1281779
theorem B854543 : Blo 566810 854543 := bstep (se 1 (by rfl) ⟨640907, by rfl⟩ : syracuseStep 854543 = 1281815) B1281815
theorem B1280555 : Blo 566810 1280555 := bstep (se 1 (by rfl) ⟨960416, by rfl⟩ : syracuseStep 1280555 = 1920833) B1920833
theorem B854585 : Blo 566810 854585 := bstep (se 2 (by rfl) ⟨320469, by rfl⟩ : syracuseStep 854585 = 640939) B640939
theorem B854663 : Blo 566810 854663 := bstep (se 1 (by rfl) ⟨640997, by rfl⟩ : syracuseStep 854663 = 1281995) B1281995
theorem B854699 : Blo 566810 854699 := bstep (se 1 (by rfl) ⟨641024, by rfl⟩ : syracuseStep 854699 = 1282049) B1282049
theorem B854729 : Blo 566810 854729 := bstep (se 2 (by rfl) ⟨320523, by rfl⟩ : syracuseStep 854729 = 641047) B641047
theorem B2427707 : Blo 566810 2427707 := bstep (se 1 (by rfl) ⟨1820780, by rfl⟩ : syracuseStep 2427707 = 3641561) B3641561
theorem B854843 : Blo 566810 854843 := bstep (se 1 (by rfl) ⟨641132, by rfl⟩ : syracuseStep 854843 = 1282265) B1282265
theorem B2886515 : Blo 566810 2886515 := bstep (se 1 (by rfl) ⟨2164886, by rfl⟩ : syracuseStep 2886515 = 4329773) B4329773
theorem B854903 : Blo 566810 854903 := bstep (se 1 (by rfl) ⟨641177, by rfl⟩ : syracuseStep 854903 = 1282355) B1282355
theorem B854927 : Blo 566810 854927 := bstep (se 1 (by rfl) ⟨641195, by rfl⟩ : syracuseStep 854927 = 1282391) B1282391
theorem B1280915 : Blo 566810 1280915 := bstep (se 1 (by rfl) ⟨960686, by rfl⟩ : syracuseStep 1280915 = 1921373) B1921373
theorem B854969 : Blo 566810 854969 := bstep (se 2 (by rfl) ⟨320613, by rfl⟩ : syracuseStep 854969 = 641227) B641227
theorem B1280969 : Blo 566810 1280969 := bstep (se 2 (by rfl) ⟨480363, by rfl⟩ : syracuseStep 1280969 = 960727) B960727
theorem B855047 : Blo 566810 855047 := bstep (se 1 (by rfl) ⟨641285, by rfl⟩ : syracuseStep 855047 = 1282571) B1282571
theorem B3247127 : Blo 566810 3247127 := bstep (se 1 (by rfl) ⟨2435345, by rfl⟩ : syracuseStep 3247127 = 4870691) B4870691
theorem B855083 : Blo 566810 855083 := bstep (se 1 (by rfl) ⟨641312, by rfl⟩ : syracuseStep 855083 = 1282625) B1282625
theorem B2427965 : Blo 566810 2427965 := bstep (se 3 (by rfl) ⟨455243, by rfl⟩ : syracuseStep 2427965 = 910487) B910487
theorem B855113 : Blo 566810 855113 := bstep (se 2 (by rfl) ⟨320667, by rfl⟩ : syracuseStep 855113 = 641335) B641335
theorem B1215623 : Blo 566810 1215623 := bstep (se 1 (by rfl) ⟨911717, by rfl⟩ : syracuseStep 1215623 = 1823435) B1823435
theorem B822415 : Blo 566810 822415 := bstep (se 1 (by rfl) ⟨616811, by rfl⟩ : syracuseStep 822415 = 1233623) B1233623
theorem B855227 : Blo 566810 855227 := bstep (se 1 (by rfl) ⟨641420, by rfl⟩ : syracuseStep 855227 = 1282841) B1282841
theorem B3083465 : Blo 566810 3083465 := bstep (se 2 (by rfl) ⟨1156299, by rfl⟩ : syracuseStep 3083465 = 2312599) B2312599
theorem B855287 : Blo 566810 855287 := bstep (se 1 (by rfl) ⟨641465, by rfl⟩ : syracuseStep 855287 = 1282931) B1282931
theorem B855311 : Blo 566810 855311 := bstep (se 1 (by rfl) ⟨641483, by rfl⟩ : syracuseStep 855311 = 1282967) B1282967
theorem B855353 : Blo 566810 855353 := bstep (se 2 (by rfl) ⟨320757, by rfl⟩ : syracuseStep 855353 = 641515) B641515
theorem B2887001 : Blo 566810 2887001 := bstep (se 2 (by rfl) ⟨1082625, by rfl⟩ : syracuseStep 2887001 = 2165251) B2165251
theorem B855431 : Blo 566810 855431 := bstep (se 1 (by rfl) ⟨641573, by rfl⟩ : syracuseStep 855431 = 1283147) B1283147
theorem B2919827 : Blo 566810 2919827 := bstep (se 1 (by rfl) ⟨2189870, by rfl⟩ : syracuseStep 2919827 = 4379741) B4379741
theorem B855467 : Blo 566810 855467 := bstep (se 1 (by rfl) ⟨641600, by rfl⟩ : syracuseStep 855467 = 1283201) B1283201
theorem B855497 : Blo 566810 855497 := bstep (se 2 (by rfl) ⟨320811, by rfl⟩ : syracuseStep 855497 = 641623) B641623
theorem B855611 : Blo 566810 855611 := bstep (se 1 (by rfl) ⟨641708, by rfl⟩ : syracuseStep 855611 = 1283417) B1283417
theorem B855671 : Blo 566810 855671 := bstep (se 1 (by rfl) ⟨641753, by rfl⟩ : syracuseStep 855671 = 1283507) B1283507
theorem B1281671 : Blo 566810 1281671 := bstep (se 1 (by rfl) ⟨961253, by rfl⟩ : syracuseStep 1281671 = 1922507) B1922507
theorem B855695 : Blo 566810 855695 := bstep (se 1 (by rfl) ⟨641771, by rfl⟩ : syracuseStep 855695 = 1283543) B1283543
theorem B855737 : Blo 566810 855737 := bstep (se 2 (by rfl) ⟨320901, by rfl⟩ : syracuseStep 855737 = 641803) B641803
theorem B2461385 : Blo 566810 2461385 := bstep (se 2 (by rfl) ⟨923019, by rfl⟩ : syracuseStep 2461385 = 1846039) B1846039
theorem B36802289 : Blo 566810 36802289 := bstep (se 2 (by rfl) ⟨13800858, by rfl⟩ : syracuseStep 36802289 = 27601717) B27601717
theorem B855815 : Blo 566810 855815 := bstep (se 1 (by rfl) ⟨641861, by rfl⟩ : syracuseStep 855815 = 1283723) B1283723
theorem B855851 : Blo 566810 855851 := bstep (se 1 (by rfl) ⟨641888, by rfl⟩ : syracuseStep 855851 = 1283777) B1283777
theorem B1281851 : Blo 566810 1281851 := bstep (se 1 (by rfl) ⟨961388, by rfl⟩ : syracuseStep 1281851 = 1922777) B1922777
theorem B855881 : Blo 566810 855881 := bstep (se 2 (by rfl) ⟨320955, by rfl⟩ : syracuseStep 855881 = 641911) B641911
theorem B1281977 : Blo 566810 1281977 := bstep (se 2 (by rfl) ⟨480741, by rfl⟩ : syracuseStep 1281977 = 961483) B961483
theorem B855995 : Blo 566810 855995 := bstep (se 1 (by rfl) ⟨641996, by rfl⟩ : syracuseStep 855995 = 1283993) B1283993
theorem B856055 : Blo 566810 856055 := bstep (se 1 (by rfl) ⟨642041, by rfl⟩ : syracuseStep 856055 = 1284083) B1284083
theorem B856079 : Blo 566810 856079 := bstep (se 1 (by rfl) ⟨642059, by rfl⟩ : syracuseStep 856079 = 1284119) B1284119
theorem B3084331 : Blo 566810 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B856121 : Blo 566810 856121 := bstep (se 2 (by rfl) ⟨321045, by rfl⟩ : syracuseStep 856121 = 642091) B642091
theorem B856199 : Blo 566810 856199 := bstep (se 1 (by rfl) ⟨642149, by rfl⟩ : syracuseStep 856199 = 1284299) B1284299
theorem B1282319 : Blo 566810 1282319 := bstep (se 1 (by rfl) ⟨961739, by rfl⟩ : syracuseStep 1282319 = 1923479) B1923479
theorem B1282337 : Blo 566810 1282337 := bstep (se 2 (by rfl) ⟨480876, by rfl⟩ : syracuseStep 1282337 = 961753) B961753
theorem B1282679 : Blo 566810 1282679 := bstep (se 1 (by rfl) ⟨962009, by rfl⟩ : syracuseStep 1282679 = 1924019) B1924019
theorem B1282859 : Blo 566810 1282859 := bstep (se 1 (by rfl) ⟨962144, by rfl⟩ : syracuseStep 1282859 = 1924289) B1924289
theorem B2429963 : Blo 566810 2429963 := bstep (se 1 (by rfl) ⟨1822472, by rfl⟩ : syracuseStep 2429963 = 3644945) B3644945
theorem B1283219 : Blo 566810 1283219 := bstep (se 1 (by rfl) ⟨962414, by rfl⟩ : syracuseStep 1283219 = 1924829) B1924829
theorem B1283273 : Blo 566810 1283273 := bstep (se 2 (by rfl) ⟨481227, by rfl⟩ : syracuseStep 1283273 = 962455) B962455
theorem B1250707 : Blo 566810 1250707 := bstep (se 1 (by rfl) ⟨938030, by rfl⟩ : syracuseStep 1250707 = 1876061) B1876061
theorem B2889107 : Blo 566810 2889107 := bstep (se 1 (by rfl) ⟨2166830, by rfl⟩ : syracuseStep 2889107 = 4333661) B4333661
theorem B3085715 : Blo 566810 3085715 := bstep (se 1 (by rfl) ⟨2314286, by rfl⟩ : syracuseStep 3085715 = 4628573) B4628573
theorem B1775105 : Blo 566810 1775105 := bstep (se 2 (by rfl) ⟨665664, by rfl⟩ : syracuseStep 1775105 = 1331329) B1331329
theorem B1218091 : Blo 566810 1218091 := bstep (se 1 (by rfl) ⟨913568, by rfl⟩ : syracuseStep 1218091 = 1827137) B1827137
theorem B1021739 : Blo 566810 1021739 := bstep (se 1 (by rfl) ⟨766304, by rfl⟩ : syracuseStep 1021739 = 1532609) B1532609
theorem B5183281 : Blo 566810 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B1939315 : Blo 566810 1939315 := bstep (se 1 (by rfl) ⟨1454486, by rfl⟩ : syracuseStep 1939315 = 2908973) B2908973
theorem B1283975 : Blo 566810 1283975 := bstep (se 1 (by rfl) ⟨962981, by rfl⟩ : syracuseStep 1283975 = 1925963) B1925963
theorem B1284155 : Blo 566810 1284155 := bstep (se 1 (by rfl) ⟨963116, by rfl⟩ : syracuseStep 1284155 = 1926233) B1926233
theorem B1284281 : Blo 566810 1284281 := bstep (se 2 (by rfl) ⟨481605, by rfl⟩ : syracuseStep 1284281 = 963211) B963211
theorem B2726081 : Blo 566810 2726081 := bstep (se 2 (by rfl) ⟨1022280, by rfl⟩ : syracuseStep 2726081 = 2044561) B2044561
theorem B956731 : Blo 566810 956731 := bstep (se 1 (by rfl) ⟨717548, by rfl⟩ : syracuseStep 956731 = 1435097) B1435097
theorem B1153415 : Blo 566810 1153415 := bstep (se 1 (by rfl) ⟨865061, by rfl⟩ : syracuseStep 1153415 = 1730123) B1730123
theorem B956873 : Blo 566810 956873 := bstep (se 2 (by rfl) ⟨358827, by rfl⟩ : syracuseStep 956873 = 717655) B717655
theorem B957575 : Blo 566810 957575 := bstep (se 1 (by rfl) ⟨718181, by rfl⟩ : syracuseStep 957575 = 1436363) B1436363
theorem B4333175 : Blo 566810 4333175 := bstep (se 1 (by rfl) ⟨3249881, by rfl⟩ : syracuseStep 4333175 = 6499763) B6499763
theorem B958223 : Blo 566810 958223 := bstep (se 1 (by rfl) ⟨718667, by rfl⟩ : syracuseStep 958223 = 1437335) B1437335
theorem B2727827 : Blo 566810 2727827 := bstep (se 1 (by rfl) ⟨2045870, by rfl⟩ : syracuseStep 2727827 = 4091741) B4091741
theorem B958763 : Blo 566810 958763 := bstep (se 1 (by rfl) ⟨719072, by rfl⟩ : syracuseStep 958763 = 1438145) B1438145
theorem B4989443 : Blo 566810 4989443 := bstep (se 1 (by rfl) ⟨3742082, by rfl⟩ : syracuseStep 4989443 = 7484165) B7484165
theorem B4334147 : Blo 566810 4334147 := bstep (se 1 (by rfl) ⟨3250610, by rfl⟩ : syracuseStep 4334147 = 6501221) B6501221
theorem B1614451 : Blo 566810 1614451 := bstep (se 1 (by rfl) ⟨1210838, by rfl⟩ : syracuseStep 1614451 = 2421677) B2421677
theorem B959161 : Blo 566810 959161 := bstep (se 2 (by rfl) ⟨359685, by rfl⟩ : syracuseStep 959161 = 719371) B719371
theorem B1024969 : Blo 566810 1024969 := bstep (se 2 (by rfl) ⟨384363, by rfl⟩ : syracuseStep 1024969 = 768727) B768727
theorem B2925571 : Blo 566810 2925571 := bstep (se 1 (by rfl) ⟨2194178, by rfl⟩ : syracuseStep 2925571 = 4388357) B4388357
theorem B4858967 : Blo 566810 4858967 := bstep (se 1 (by rfl) ⟨3644225, by rfl⟩ : syracuseStep 4858967 = 7288451) B7288451
theorem B12297365 : Blo 566810 12297365 := bstep (se 6 (by rfl) ⟨288219, by rfl⟩ : syracuseStep 12297365 = 576439) B576439
theorem B2434337 : Blo 566810 2434337 := bstep (se 2 (by rfl) ⟨912876, by rfl⟩ : syracuseStep 2434337 = 1825753) B1825753
theorem B959863 : Blo 566810 959863 := bstep (se 1 (by rfl) ⟨719897, by rfl⟩ : syracuseStep 959863 = 1439795) B1439795
theorem B1942937 : Blo 566810 1942937 := bstep (se 2 (by rfl) ⟨728601, by rfl⟩ : syracuseStep 1942937 = 1457203) B1457203
theorem B566843 : Blo 566810 566843 := bstep (se 1 (by rfl) ⟨425132, by rfl⟩ : syracuseStep 566843 = 850265) B850265
theorem B960059 : Blo 566810 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B566919 : Blo 566810 566919 := bstep (se 1 (by rfl) ⟨425189, by rfl⟩ : syracuseStep 566919 = 850379) B850379
theorem B566927 : Blo 566810 566927 := bstep (se 1 (by rfl) ⟨425195, by rfl⟩ : syracuseStep 566927 = 850391) B850391
theorem B566971 : Blo 566810 566971 := bstep (se 1 (by rfl) ⟨425228, by rfl⟩ : syracuseStep 566971 = 850457) B850457
theorem B16361189 : Blo 566810 16361189 := bstep (se 4 (by rfl) ⟨1533861, by rfl⟩ : syracuseStep 16361189 = 3067723) B3067723
theorem B567047 : Blo 566810 567047 := bstep (se 1 (by rfl) ⟨425285, by rfl⟩ : syracuseStep 567047 = 850571) B850571
theorem B567055 : Blo 566810 567055 := bstep (se 1 (by rfl) ⟨425291, by rfl⟩ : syracuseStep 567055 = 850583) B850583
theorem B2303777 : Blo 566810 2303777 := bstep (se 2 (by rfl) ⟨863916, by rfl⟩ : syracuseStep 2303777 = 1727833) B1727833
theorem B567099 : Blo 566810 567099 := bstep (se 1 (by rfl) ⟨425324, by rfl⟩ : syracuseStep 567099 = 850649) B850649
theorem B567175 : Blo 566810 567175 := bstep (se 1 (by rfl) ⟨425381, by rfl⟩ : syracuseStep 567175 = 850763) B850763
theorem B2434951 : Blo 566810 2434951 := bstep (se 1 (by rfl) ⟨1826213, by rfl⟩ : syracuseStep 2434951 = 3652427) B3652427
theorem B567183 : Blo 566810 567183 := bstep (se 1 (by rfl) ⟨425387, by rfl⟩ : syracuseStep 567183 = 850775) B850775
theorem B567227 : Blo 566810 567227 := bstep (se 1 (by rfl) ⟨425420, by rfl⟩ : syracuseStep 567227 = 850841) B850841
theorem B960457 : Blo 566810 960457 := bstep (se 2 (by rfl) ⟨360171, by rfl⟩ : syracuseStep 960457 = 720343) B720343
theorem B567303 : Blo 566810 567303 := bstep (se 1 (by rfl) ⟨425477, by rfl⟩ : syracuseStep 567303 = 850955) B850955
theorem B567311 : Blo 566810 567311 := bstep (se 1 (by rfl) ⟨425483, by rfl⟩ : syracuseStep 567311 = 850967) B850967
theorem B567355 : Blo 566810 567355 := bstep (se 1 (by rfl) ⟨425516, by rfl⟩ : syracuseStep 567355 = 851033) B851033
theorem B567431 : Blo 566810 567431 := bstep (se 1 (by rfl) ⟨425573, by rfl⟩ : syracuseStep 567431 = 851147) B851147
theorem B567439 : Blo 566810 567439 := bstep (se 1 (by rfl) ⟨425579, by rfl⟩ : syracuseStep 567439 = 851159) B851159
theorem B1616057 : Blo 566810 1616057 := bstep (se 2 (by rfl) ⟨606021, by rfl⟩ : syracuseStep 1616057 = 1212043) B1212043
theorem B567483 : Blo 566810 567483 := bstep (se 1 (by rfl) ⟨425612, by rfl⟩ : syracuseStep 567483 = 851225) B851225
theorem B567559 : Blo 566810 567559 := bstep (se 1 (by rfl) ⟨425669, by rfl⟩ : syracuseStep 567559 = 851339) B851339
theorem B567567 : Blo 566810 567567 := bstep (se 1 (by rfl) ⟨425675, by rfl⟩ : syracuseStep 567567 = 851351) B851351
theorem B567611 : Blo 566810 567611 := bstep (se 1 (by rfl) ⟨425708, by rfl⟩ : syracuseStep 567611 = 851417) B851417
theorem B567687 : Blo 566810 567687 := bstep (se 1 (by rfl) ⟨425765, by rfl⟩ : syracuseStep 567687 = 851531) B851531
theorem B567695 : Blo 566810 567695 := bstep (se 1 (by rfl) ⟨425771, by rfl⟩ : syracuseStep 567695 = 851543) B851543
theorem B567739 : Blo 566810 567739 := bstep (se 1 (by rfl) ⟨425804, by rfl⟩ : syracuseStep 567739 = 851609) B851609
theorem B567815 : Blo 566810 567815 := bstep (se 1 (by rfl) ⟨425861, by rfl⟩ : syracuseStep 567815 = 851723) B851723
theorem B1616399 : Blo 566810 1616399 := bstep (se 1 (by rfl) ⟨1212299, by rfl⟩ : syracuseStep 1616399 = 2424599) B2424599
theorem B567823 : Blo 566810 567823 := bstep (se 1 (by rfl) ⟨425867, by rfl⟩ : syracuseStep 567823 = 851735) B851735
theorem B2468381 : Blo 566810 2468381 := bstep (se 3 (by rfl) ⟨462821, by rfl⟩ : syracuseStep 2468381 = 925643) B925643
theorem B567867 : Blo 566810 567867 := bstep (se 1 (by rfl) ⟨425900, by rfl⟩ : syracuseStep 567867 = 851801) B851801
theorem B567943 : Blo 566810 567943 := bstep (se 1 (by rfl) ⟨425957, by rfl⟩ : syracuseStep 567943 = 851915) B851915
theorem B961159 : Blo 566810 961159 := bstep (se 1 (by rfl) ⟨720869, by rfl⟩ : syracuseStep 961159 = 1441739) B1441739
theorem B567951 : Blo 566810 567951 := bstep (se 1 (by rfl) ⟨425963, by rfl⟩ : syracuseStep 567951 = 851927) B851927
theorem B567995 : Blo 566810 567995 := bstep (se 1 (by rfl) ⟨425996, by rfl⟩ : syracuseStep 567995 = 851993) B851993
theorem B568071 : Blo 566810 568071 := bstep (se 1 (by rfl) ⟨426053, by rfl⟩ : syracuseStep 568071 = 852107) B852107
theorem B568079 : Blo 566810 568079 := bstep (se 1 (by rfl) ⟨426059, by rfl⟩ : syracuseStep 568079 = 852119) B852119
theorem B568123 : Blo 566810 568123 := bstep (se 1 (by rfl) ⟨426092, by rfl⟩ : syracuseStep 568123 = 852185) B852185
theorem B568199 : Blo 566810 568199 := bstep (se 1 (by rfl) ⟨426149, by rfl⟩ : syracuseStep 568199 = 852299) B852299
theorem B568207 : Blo 566810 568207 := bstep (se 1 (by rfl) ⟨426155, by rfl⟩ : syracuseStep 568207 = 852311) B852311
theorem B568251 : Blo 566810 568251 := bstep (se 1 (by rfl) ⟨426188, by rfl⟩ : syracuseStep 568251 = 852377) B852377
theorem B568327 : Blo 566810 568327 := bstep (se 1 (by rfl) ⟨426245, by rfl⟩ : syracuseStep 568327 = 852491) B852491
theorem B568335 : Blo 566810 568335 := bstep (se 1 (by rfl) ⟨426251, by rfl⟩ : syracuseStep 568335 = 852503) B852503
theorem B568379 : Blo 566810 568379 := bstep (se 1 (by rfl) ⟨426284, by rfl⟩ : syracuseStep 568379 = 852569) B852569
theorem B568455 : Blo 566810 568455 := bstep (se 1 (by rfl) ⟨426341, by rfl⟩ : syracuseStep 568455 = 852683) B852683
theorem B568463 : Blo 566810 568463 := bstep (se 1 (by rfl) ⟨426347, by rfl⟩ : syracuseStep 568463 = 852695) B852695
theorem B568507 : Blo 566810 568507 := bstep (se 1 (by rfl) ⟨426380, by rfl⟩ : syracuseStep 568507 = 852761) B852761
theorem B11709677 : Blo 566810 11709677 := bstep (se 3 (by rfl) ⟨2195564, by rfl⟩ : syracuseStep 11709677 = 4391129) B4391129
theorem B568583 : Blo 566810 568583 := bstep (se 1 (by rfl) ⟨426437, by rfl⟩ : syracuseStep 568583 = 852875) B852875
theorem B568591 : Blo 566810 568591 := bstep (se 1 (by rfl) ⟨426443, by rfl⟩ : syracuseStep 568591 = 852887) B852887
theorem B961807 : Blo 566810 961807 := bstep (se 1 (by rfl) ⟨721355, by rfl⟩ : syracuseStep 961807 = 1442711) B1442711
theorem B1617185 : Blo 566810 1617185 := bstep (se 2 (by rfl) ⟨606444, by rfl⟩ : syracuseStep 1617185 = 1212889) B1212889
theorem B568635 : Blo 566810 568635 := bstep (se 1 (by rfl) ⟨426476, by rfl⟩ : syracuseStep 568635 = 852953) B852953
theorem B568711 : Blo 566810 568711 := bstep (se 1 (by rfl) ⟨426533, by rfl⟩ : syracuseStep 568711 = 853067) B853067
theorem B568719 : Blo 566810 568719 := bstep (se 1 (by rfl) ⟨426539, by rfl⟩ : syracuseStep 568719 = 853079) B853079
theorem B568763 : Blo 566810 568763 := bstep (se 1 (by rfl) ⟨426572, by rfl⟩ : syracuseStep 568763 = 853145) B853145
theorem B568839 : Blo 566810 568839 := bstep (se 1 (by rfl) ⟨426629, by rfl⟩ : syracuseStep 568839 = 853259) B853259
theorem B568847 : Blo 566810 568847 := bstep (se 1 (by rfl) ⟨426635, by rfl⟩ : syracuseStep 568847 = 853271) B853271
theorem B568891 : Blo 566810 568891 := bstep (se 1 (by rfl) ⟨426668, by rfl⟩ : syracuseStep 568891 = 853337) B853337
theorem B568967 : Blo 566810 568967 := bstep (se 1 (by rfl) ⟨426725, by rfl⟩ : syracuseStep 568967 = 853451) B853451
theorem B568975 : Blo 566810 568975 := bstep (se 1 (by rfl) ⟨426731, by rfl⟩ : syracuseStep 568975 = 853463) B853463
theorem B569019 : Blo 566810 569019 := bstep (se 1 (by rfl) ⟨426764, by rfl⟩ : syracuseStep 569019 = 853529) B853529
theorem B2043593 : Blo 566810 2043593 := bstep (se 2 (by rfl) ⟨766347, by rfl⟩ : syracuseStep 2043593 = 1532695) B1532695
theorem B2043649 : Blo 566810 2043649 := bstep (se 2 (by rfl) ⟨766368, by rfl⟩ : syracuseStep 2043649 = 1532737) B1532737
theorem B569095 : Blo 566810 569095 := bstep (se 1 (by rfl) ⟨426821, by rfl⟩ : syracuseStep 569095 = 853643) B853643
theorem B569103 : Blo 566810 569103 := bstep (se 1 (by rfl) ⟨426827, by rfl⟩ : syracuseStep 569103 = 853655) B853655
theorem B1027873 : Blo 566810 1027873 := bstep (se 2 (by rfl) ⟨385452, by rfl⟩ : syracuseStep 1027873 = 770905) B770905
theorem B962347 : Blo 566810 962347 := bstep (se 1 (by rfl) ⟨721760, by rfl⟩ : syracuseStep 962347 = 1443521) B1443521
theorem B569147 : Blo 566810 569147 := bstep (se 1 (by rfl) ⟨426860, by rfl⟩ : syracuseStep 569147 = 853721) B853721
theorem B569223 : Blo 566810 569223 := bstep (se 1 (by rfl) ⟨426917, by rfl⟩ : syracuseStep 569223 = 853835) B853835
theorem B2600839 : Blo 566810 2600839 := bstep (se 1 (by rfl) ⟨1950629, by rfl⟩ : syracuseStep 2600839 = 3901259) B3901259
theorem B569231 : Blo 566810 569231 := bstep (se 1 (by rfl) ⟨426923, by rfl⟩ : syracuseStep 569231 = 853847) B853847
theorem B962489 : Blo 566810 962489 := bstep (se 2 (by rfl) ⟨360933, by rfl⟩ : syracuseStep 962489 = 721867) B721867
theorem B569275 : Blo 566810 569275 := bstep (se 1 (by rfl) ⟨426956, by rfl⟩ : syracuseStep 569275 = 853913) B853913
theorem B10399691 : Blo 566810 10399691 := bstep (se 1 (by rfl) ⟨7799768, by rfl⟩ : syracuseStep 10399691 = 15599537) B15599537
theorem B569351 : Blo 566810 569351 := bstep (se 1 (by rfl) ⟨427013, by rfl⟩ : syracuseStep 569351 = 854027) B854027
theorem B569359 : Blo 566810 569359 := bstep (se 1 (by rfl) ⟨427019, by rfl⟩ : syracuseStep 569359 = 854039) B854039
theorem B569403 : Blo 566810 569403 := bstep (se 1 (by rfl) ⟨427052, by rfl⟩ : syracuseStep 569403 = 854105) B854105
theorem B569479 : Blo 566810 569479 := bstep (se 1 (by rfl) ⟨427109, by rfl⟩ : syracuseStep 569479 = 854219) B854219
theorem B569487 : Blo 566810 569487 := bstep (se 1 (by rfl) ⟨427115, by rfl⟩ : syracuseStep 569487 = 854231) B854231
theorem B3879085 : Blo 566810 3879085 := bstep (se 3 (by rfl) ⟨727328, by rfl⟩ : syracuseStep 3879085 = 1454657) B1454657
theorem B569531 : Blo 566810 569531 := bstep (se 1 (by rfl) ⟨427148, by rfl⟩ : syracuseStep 569531 = 854297) B854297
theorem B6336713 : Blo 566810 6336713 := bstep (se 2 (by rfl) ⟨2376267, by rfl⟩ : syracuseStep 6336713 = 4752535) B4752535
theorem B569607 : Blo 566810 569607 := bstep (se 1 (by rfl) ⟨427205, by rfl⟩ : syracuseStep 569607 = 854411) B854411
theorem B569615 : Blo 566810 569615 := bstep (se 1 (by rfl) ⟨427211, by rfl⟩ : syracuseStep 569615 = 854423) B854423
theorem B569659 : Blo 566810 569659 := bstep (se 1 (by rfl) ⟨427244, by rfl⟩ : syracuseStep 569659 = 854489) B854489
theorem B1028471 : Blo 566810 1028471 := bstep (se 1 (by rfl) ⟨771353, by rfl⟩ : syracuseStep 1028471 = 1542707) B1542707
theorem B569735 : Blo 566810 569735 := bstep (se 1 (by rfl) ⟨427301, by rfl⟩ : syracuseStep 569735 = 854603) B854603
theorem B569743 : Blo 566810 569743 := bstep (se 1 (by rfl) ⟨427307, by rfl⟩ : syracuseStep 569743 = 854615) B854615
theorem B2929043 : Blo 566810 2929043 := bstep (se 1 (by rfl) ⟨2196782, by rfl⟩ : syracuseStep 2929043 = 4393565) B4393565
theorem B1913273 : Blo 566810 1913273 := bstep (se 2 (by rfl) ⟨717477, by rfl⟩ : syracuseStep 1913273 = 1434955) B1434955
theorem B569787 : Blo 566810 569787 := bstep (se 1 (by rfl) ⟨427340, by rfl⟩ : syracuseStep 569787 = 854681) B854681
theorem B569863 : Blo 566810 569863 := bstep (se 1 (by rfl) ⟨427397, by rfl⟩ : syracuseStep 569863 = 854795) B854795
theorem B2732555 : Blo 566810 2732555 := bstep (se 1 (by rfl) ⟨2049416, by rfl⟩ : syracuseStep 2732555 = 4098833) B4098833
theorem B569871 : Blo 566810 569871 := bstep (se 1 (by rfl) ⟨427403, by rfl⟩ : syracuseStep 569871 = 854807) B854807
theorem B569915 : Blo 566810 569915 := bstep (se 1 (by rfl) ⟨427436, by rfl⟩ : syracuseStep 569915 = 854873) B854873
theorem B963191 : Blo 566810 963191 := bstep (se 1 (by rfl) ⟨722393, by rfl⟩ : syracuseStep 963191 = 1444787) B1444787
theorem B569991 : Blo 566810 569991 := bstep (se 1 (by rfl) ⟨427493, by rfl⟩ : syracuseStep 569991 = 854987) B854987
theorem B569999 : Blo 566810 569999 := bstep (se 1 (by rfl) ⟨427499, by rfl⟩ : syracuseStep 569999 = 854999) B854999
theorem B570043 : Blo 566810 570043 := bstep (se 1 (by rfl) ⟨427532, by rfl⟩ : syracuseStep 570043 = 855065) B855065
theorem B570119 : Blo 566810 570119 := bstep (se 1 (by rfl) ⟨427589, by rfl⟩ : syracuseStep 570119 = 855179) B855179
theorem B1618699 : Blo 566810 1618699 := bstep (se 1 (by rfl) ⟨1214024, by rfl⟩ : syracuseStep 1618699 = 2428049) B2428049
theorem B570127 : Blo 566810 570127 := bstep (se 1 (by rfl) ⟨427595, by rfl⟩ : syracuseStep 570127 = 855191) B855191
theorem B570171 : Blo 566810 570171 := bstep (se 1 (by rfl) ⟨427628, by rfl⟩ : syracuseStep 570171 = 855257) B855257
theorem B570247 : Blo 566810 570247 := bstep (se 1 (by rfl) ⟨427685, by rfl⟩ : syracuseStep 570247 = 855371) B855371
theorem B570255 : Blo 566810 570255 := bstep (se 1 (by rfl) ⟨427691, by rfl⟩ : syracuseStep 570255 = 855383) B855383
theorem B570299 : Blo 566810 570299 := bstep (se 1 (by rfl) ⟨427724, by rfl⟩ : syracuseStep 570299 = 855449) B855449
theorem B570375 : Blo 566810 570375 := bstep (se 1 (by rfl) ⟨427781, by rfl⟩ : syracuseStep 570375 = 855563) B855563
theorem B1913867 : Blo 566810 1913867 := bstep (se 1 (by rfl) ⟨1435400, by rfl⟩ : syracuseStep 1913867 = 2870801) B2870801
theorem B570383 : Blo 566810 570383 := bstep (se 1 (by rfl) ⟨427787, by rfl⟩ : syracuseStep 570383 = 855575) B855575
theorem B1618973 : Blo 566810 1618973 := bstep (se 3 (by rfl) ⟨303557, by rfl⟩ : syracuseStep 1618973 = 607115) B607115
theorem B570427 : Blo 566810 570427 := bstep (se 1 (by rfl) ⟨427820, by rfl⟩ : syracuseStep 570427 = 855641) B855641
theorem B1913975 : Blo 566810 1913975 := bstep (se 1 (by rfl) ⟨1435481, by rfl⟩ : syracuseStep 1913975 = 2870963) B2870963
theorem B570503 : Blo 566810 570503 := bstep (se 1 (by rfl) ⟨427877, by rfl⟩ : syracuseStep 570503 = 855755) B855755
theorem B570511 : Blo 566810 570511 := bstep (se 1 (by rfl) ⟨427883, by rfl⟩ : syracuseStep 570511 = 855767) B855767
theorem B570555 : Blo 566810 570555 := bstep (se 1 (by rfl) ⟨427916, by rfl⟩ : syracuseStep 570555 = 855833) B855833
theorem B570631 : Blo 566810 570631 := bstep (se 1 (by rfl) ⟨427973, by rfl⟩ : syracuseStep 570631 = 855947) B855947
theorem B570639 : Blo 566810 570639 := bstep (se 1 (by rfl) ⟨427979, by rfl⟩ : syracuseStep 570639 = 855959) B855959
theorem B570683 : Blo 566810 570683 := bstep (se 1 (by rfl) ⟨428012, by rfl⟩ : syracuseStep 570683 = 856025) B856025
theorem B2733401 : Blo 566810 2733401 := bstep (se 2 (by rfl) ⟨1025025, by rfl⟩ : syracuseStep 2733401 = 2050051) B2050051
theorem B1619315 : Blo 566810 1619315 := bstep (se 1 (by rfl) ⟨1214486, by rfl⟩ : syracuseStep 1619315 = 2428973) B2428973
theorem B570759 : Blo 566810 570759 := bstep (se 1 (by rfl) ⟨428069, by rfl⟩ : syracuseStep 570759 = 856139) B856139
theorem B570767 : Blo 566810 570767 := bstep (se 1 (by rfl) ⟨428075, by rfl⟩ : syracuseStep 570767 = 856151) B856151
theorem B6141329 : Blo 566810 6141329 := bstep (se 2 (by rfl) ⟨2302998, by rfl⟩ : syracuseStep 6141329 = 4605997) B4605997
theorem B2045483 : Blo 566810 2045483 := bstep (se 1 (by rfl) ⟨1534112, by rfl⟩ : syracuseStep 2045483 = 3068225) B3068225
theorem B1914569 : Blo 566810 1914569 := bstep (se 2 (by rfl) ⟨717963, by rfl⟩ : syracuseStep 1914569 = 1435927) B1435927
theorem B6895475 : Blo 566810 6895475 := bstep (se 1 (by rfl) ⟨5171606, by rfl⟩ : syracuseStep 6895475 = 10343213) B10343213
theorem B866423 : Blo 566810 866423 := bstep (se 1 (by rfl) ⟨649817, by rfl⟩ : syracuseStep 866423 = 1299635) B1299635
theorem B866447 : Blo 566810 866447 := bstep (se 1 (by rfl) ⟨649835, by rfl⟩ : syracuseStep 866447 = 1299671) B1299671
theorem B1620283 : Blo 566810 1620283 := bstep (se 1 (by rfl) ⟨1215212, by rfl⟩ : syracuseStep 1620283 = 2430425) B2430425
theorem B2767193 : Blo 566810 2767193 := bstep (se 2 (by rfl) ⟨1037697, by rfl⟩ : syracuseStep 2767193 = 2075395) B2075395
theorem B1915271 : Blo 566810 1915271 := bstep (se 1 (by rfl) ⟨1436453, by rfl⟩ : syracuseStep 1915271 = 2872907) B2872907
theorem B1817117 : Blo 566810 1817117 := bstep (se 3 (by rfl) ⟨340709, by rfl⟩ : syracuseStep 1817117 = 681419) B681419
theorem B1915649 : Blo 566810 1915649 := bstep (se 2 (by rfl) ⟨718368, by rfl⟩ : syracuseStep 1915649 = 1436737) B1436737
theorem B6470603 : Blo 566810 6470603 := bstep (se 1 (by rfl) ⟨4852952, by rfl⟩ : syracuseStep 6470603 = 9705905) B9705905
theorem B638095 : Blo 566810 638095 := bstep (se 1 (by rfl) ⟨478571, by rfl⟩ : syracuseStep 638095 = 957143) B957143
theorem B1621433 : Blo 566810 1621433 := bstep (se 2 (by rfl) ⟨608037, by rfl⟩ : syracuseStep 1621433 = 1216075) B1216075
theorem B1916459 : Blo 566810 1916459 := bstep (se 1 (by rfl) ⟨1437344, by rfl⟩ : syracuseStep 1916459 = 2874689) B2874689
theorem B638599 : Blo 566810 638599 := bstep (se 1 (by rfl) ⟨478949, by rfl⟩ : syracuseStep 638599 = 957899) B957899
theorem B1621775 : Blo 566810 1621775 := bstep (se 1 (by rfl) ⟨1216331, by rfl⟩ : syracuseStep 1621775 = 2432663) B2432663
theorem B769807 : Blo 566810 769807 := bstep (se 1 (by rfl) ⟨577355, by rfl⟩ : syracuseStep 769807 = 1154711) B1154711
theorem B638779 : Blo 566810 638779 := bstep (se 1 (by rfl) ⟨479084, by rfl⟩ : syracuseStep 638779 = 958169) B958169
theorem B769927 : Blo 566810 769927 := bstep (se 1 (by rfl) ⟨577445, by rfl⟩ : syracuseStep 769927 = 1154891) B1154891
theorem B1458263 : Blo 566810 1458263 := bstep (se 1 (by rfl) ⟨1093697, by rfl⟩ : syracuseStep 1458263 = 2187395) B2187395
theorem B639247 : Blo 566810 639247 := bstep (se 1 (by rfl) ⟨479435, by rfl⟩ : syracuseStep 639247 = 958871) B958871
theorem B29573603 : Blo 566810 29573603 := bstep (se 1 (by rfl) ⟨22180202, by rfl⟩ : syracuseStep 29573603 = 44360405) B44360405
theorem B4112963 : Blo 566810 4112963 := bstep (se 1 (by rfl) ⟨3084722, by rfl⟩ : syracuseStep 4112963 = 6169445) B6169445
theorem B1622663 : Blo 566810 1622663 := bstep (se 1 (by rfl) ⟨1216997, by rfl⟩ : syracuseStep 1622663 = 2433995) B2433995
theorem B639751 : Blo 566810 639751 := bstep (se 1 (by rfl) ⟨479813, by rfl⟩ : syracuseStep 639751 = 959627) B959627
theorem B1917755 : Blo 566810 1917755 := bstep (se 1 (by rfl) ⟨1438316, by rfl⟩ : syracuseStep 1917755 = 2876633) B2876633
theorem B2048827 : Blo 566810 2048827 := bstep (se 1 (by rfl) ⟨1536620, by rfl⟩ : syracuseStep 2048827 = 3073241) B3073241
theorem B1622845 : Blo 566810 1622845 := bstep (se 3 (by rfl) ⟨304283, by rfl⟩ : syracuseStep 1622845 = 608567) B608567
theorem B1819577 : Blo 566810 1819577 := bstep (se 2 (by rfl) ⟨682341, by rfl⟩ : syracuseStep 1819577 = 1364683) B1364683
theorem B639931 : Blo 566810 639931 := bstep (se 1 (by rfl) ⟨479948, by rfl⟩ : syracuseStep 639931 = 959897) B959897
theorem B1623073 : Blo 566810 1623073 := bstep (se 2 (by rfl) ⟨608652, by rfl⟩ : syracuseStep 1623073 = 1217305) B1217305
theorem B5850157 : Blo 566810 5850157 := bstep (se 3 (by rfl) ⟨1096904, by rfl⟩ : syracuseStep 5850157 = 2193809) B2193809
theorem B1754171 : Blo 566810 1754171 := bstep (se 1 (by rfl) ⟨1315628, by rfl⟩ : syracuseStep 1754171 = 2631257) B2631257
theorem B3327095 : Blo 566810 3327095 := bstep (se 1 (by rfl) ⟨2495321, by rfl⟩ : syracuseStep 3327095 = 4990643) B4990643
theorem B3687713 : Blo 566810 3687713 := bstep (se 2 (by rfl) ⟨1382892, by rfl⟩ : syracuseStep 3687713 = 2765785) B2765785
theorem B1918241 : Blo 566810 1918241 := bstep (se 2 (by rfl) ⟨719340, by rfl⟩ : syracuseStep 1918241 = 1438681) B1438681
theorem B1623415 : Blo 566810 1623415 := bstep (se 1 (by rfl) ⟨1217561, by rfl⟩ : syracuseStep 1623415 = 2435123) B2435123
theorem B640399 : Blo 566810 640399 := bstep (se 1 (by rfl) ⟨480299, by rfl⟩ : syracuseStep 640399 = 960599) B960599
theorem B1918835 : Blo 566810 1918835 := bstep (se 1 (by rfl) ⟨1439126, by rfl⟩ : syracuseStep 1918835 = 2878253) B2878253
theorem B640903 : Blo 566810 640903 := bstep (se 1 (by rfl) ⟨480677, by rfl⟩ : syracuseStep 640903 = 961355) B961355
theorem B641083 : Blo 566810 641083 := bstep (se 1 (by rfl) ⟨480812, by rfl⟩ : syracuseStep 641083 = 961625) B961625
theorem B2869505 : Blo 566810 2869505 := bstep (se 2 (by rfl) ⟨1076064, by rfl⟩ : syracuseStep 2869505 = 2152129) B2152129
theorem B1624349 : Blo 566810 1624349 := bstep (se 3 (by rfl) ⟨304565, by rfl⟩ : syracuseStep 1624349 = 609131) B609131
theorem B641551 : Blo 566810 641551 := bstep (se 1 (by rfl) ⟨481163, by rfl⟩ : syracuseStep 641551 = 962327) B962327
theorem B1624691 : Blo 566810 1624691 := bstep (se 1 (by rfl) ⟨1218518, by rfl⟩ : syracuseStep 1624691 = 2437037) B2437037
theorem B3230381 : Blo 566810 3230381 := bstep (se 3 (by rfl) ⟨605696, by rfl⟩ : syracuseStep 3230381 = 1211393) B1211393
theorem B1362703 : Blo 566810 1362703 := bstep (se 1 (by rfl) ⟨1022027, by rfl⟩ : syracuseStep 1362703 = 2044055) B2044055
theorem B15584015 : Blo 566810 15584015 := bstep (se 1 (by rfl) ⟨11688011, by rfl⟩ : syracuseStep 15584015 = 23376023) B23376023
theorem B2312975 : Blo 566810 2312975 := bstep (se 1 (by rfl) ⟨1734731, by rfl⟩ : syracuseStep 2312975 = 3469463) B3469463
theorem B1329979 : Blo 566810 1329979 := bstep (se 1 (by rfl) ⟨997484, by rfl⟩ : syracuseStep 1329979 = 1994969) B1994969
theorem B642055 : Blo 566810 642055 := bstep (se 1 (by rfl) ⟨481541, by rfl⟩ : syracuseStep 642055 = 963083) B963083
theorem B2870315 : Blo 566810 2870315 := bstep (se 1 (by rfl) ⟨2152736, by rfl⟩ : syracuseStep 2870315 = 4305473) B4305473
theorem B1625147 : Blo 566810 1625147 := bstep (se 1 (by rfl) ⟨1218860, by rfl⟩ : syracuseStep 1625147 = 2437721) B2437721
theorem B5459345 : Blo 566810 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B1560217 : Blo 566810 1560217 := bstep (se 2 (by rfl) ⟨585081, by rfl⟩ : syracuseStep 1560217 = 1170163) B1170163
theorem B1822409 : Blo 566810 1822409 := bstep (se 2 (by rfl) ⟨683403, by rfl⟩ : syracuseStep 1822409 = 1366807) B1366807
theorem B3231521 : Blo 566810 3231521 := bstep (se 2 (by rfl) ⟨1211820, by rfl⟩ : syracuseStep 3231521 = 2423641) B2423641
theorem B99438515 : Blo 566810 99438515 := bstep (se 1 (by rfl) ⟨74578886, by rfl⟩ : syracuseStep 99438515 = 149157773) B149157773
theorem B8212427 : Blo 566810 8212427 := bstep (se 1 (by rfl) ⟨6159320, by rfl⟩ : syracuseStep 8212427 = 12318641) B12318641
theorem B2871611 : Blo 566810 2871611 := bstep (se 1 (by rfl) ⟨2153708, by rfl⟩ : syracuseStep 2871611 = 4307417) B4307417
theorem B1921427 : Blo 566810 1921427 := bstep (se 1 (by rfl) ⟨1441070, by rfl⟩ : syracuseStep 1921427 = 2882141) B2882141
theorem B2871773 : Blo 566810 2871773 := bstep (se 3 (by rfl) ⟨538457, by rfl⟩ : syracuseStep 2871773 = 1076915) B1076915
theorem B159896081 : Blo 566810 159896081 := bstep (se 2 (by rfl) ⟨59961030, by rfl⟩ : syracuseStep 159896081 = 119922061) B119922061
theorem B2872097 : Blo 566810 2872097 := bstep (se 2 (by rfl) ⟨1077036, by rfl⟩ : syracuseStep 2872097 = 2154073) B2154073
theorem B1364779 : Blo 566810 1364779 := bstep (se 1 (by rfl) ⟨1023584, by rfl⟩ : syracuseStep 1364779 = 2047169) B2047169
theorem B1364855 : Blo 566810 1364855 := bstep (se 1 (by rfl) ⟨1023641, by rfl⟩ : syracuseStep 1364855 = 2047283) B2047283
theorem B807823 : Blo 566810 807823 := bstep (se 1 (by rfl) ⟨605867, by rfl⟩ : syracuseStep 807823 = 1211735) B1211735
theorem B808393 : Blo 566810 808393 := bstep (se 2 (by rfl) ⟨303147, by rfl⟩ : syracuseStep 808393 = 606295) B606295
theorem B874127 : Blo 566810 874127 := bstep (se 1 (by rfl) ⟨655595, by rfl⟩ : syracuseStep 874127 = 1311191) B1311191
theorem B2873069 : Blo 566810 2873069 := bstep (se 3 (by rfl) ⟨538700, by rfl⟩ : syracuseStep 2873069 = 1077401) B1077401
theorem B1922831 : Blo 566810 1922831 := bstep (se 1 (by rfl) ⟨1442123, by rfl⟩ : syracuseStep 1922831 = 2884247) B2884247
theorem B1365913 : Blo 566810 1365913 := bstep (se 2 (by rfl) ⟨512217, by rfl⟩ : syracuseStep 1365913 = 1024435) B1024435
theorem B4872089 : Blo 566810 4872089 := bstep (se 2 (by rfl) ⟨1827033, by rfl⟩ : syracuseStep 4872089 = 3654067) B3654067
theorem B1923101 : Blo 566810 1923101 := bstep (se 3 (by rfl) ⟨360581, by rfl⟩ : syracuseStep 1923101 = 721163) B721163
theorem B973001 : Blo 566810 973001 := bstep (se 2 (by rfl) ⟨364875, by rfl⟩ : syracuseStep 973001 = 729751) B729751
theorem B13162769 : Blo 566810 13162769 := bstep (se 2 (by rfl) ⟨4936038, by rfl⟩ : syracuseStep 13162769 = 9872077) B9872077
theorem B2152889 : Blo 566810 2152889 := bstep (se 2 (by rfl) ⟨807333, by rfl⟩ : syracuseStep 2152889 = 1614667) B1614667
theorem B1825291 : Blo 566810 1825291 := bstep (se 1 (by rfl) ⟨1368968, by rfl⟩ : syracuseStep 1825291 = 2737937) B2737937
theorem B2873879 : Blo 566810 2873879 := bstep (se 1 (by rfl) ⟨2155409, by rfl⟩ : syracuseStep 2873879 = 4310819) B4310819
theorem B3070493 : Blo 566810 3070493 := bstep (se 3 (by rfl) ⟨575717, by rfl⟩ : syracuseStep 3070493 = 1151435) B1151435
theorem B1563425 : Blo 566810 1563425 := bstep (se 2 (by rfl) ⟨586284, by rfl⟩ : syracuseStep 1563425 = 1172569) B1172569
theorem B1727531 : Blo 566810 1727531 := bstep (se 1 (by rfl) ⟨1295648, by rfl⟩ : syracuseStep 1727531 = 2591297) B2591297
theorem B1367297 : Blo 566810 1367297 := bstep (se 2 (by rfl) ⟨512736, by rfl⟩ : syracuseStep 1367297 = 1025473) B1025473
theorem B1924505 : Blo 566810 1924505 := bstep (se 2 (by rfl) ⟨721689, by rfl⟩ : syracuseStep 1924505 = 1443379) B1443379
theorem B908815 : Blo 566810 908815 := bstep (se 1 (by rfl) ⟨681611, by rfl⟩ : syracuseStep 908815 = 1363223) B1363223
theorem B909071 : Blo 566810 909071 := bstep (se 1 (by rfl) ⟨681803, by rfl⟩ : syracuseStep 909071 = 1363607) B1363607
theorem B3497863 : Blo 566810 3497863 := bstep (se 1 (by rfl) ⟨2623397, by rfl⟩ : syracuseStep 3497863 = 5246795) B5246795
theorem B811081 : Blo 566810 811081 := bstep (se 2 (by rfl) ⟨304155, by rfl⟩ : syracuseStep 811081 = 608311) B608311
theorem B1925207 : Blo 566810 1925207 := bstep (se 1 (by rfl) ⟨1443905, by rfl⟩ : syracuseStep 1925207 = 2887811) B2887811
theorem B6644227 : Blo 566810 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B3236395 : Blo 566810 3236395 := bstep (se 1 (by rfl) ⟨2427296, by rfl⟩ : syracuseStep 3236395 = 4854593) B4854593
theorem B1925693 : Blo 566810 1925693 := bstep (se 3 (by rfl) ⟨361067, by rfl⟩ : syracuseStep 1925693 = 722135) B722135
theorem B6152921 : Blo 566810 6152921 := bstep (se 2 (by rfl) ⟨2307345, by rfl⟩ : syracuseStep 6152921 = 4614691) B4614691
theorem B910199 : Blo 566810 910199 := bstep (se 1 (by rfl) ⟨682649, by rfl⟩ : syracuseStep 910199 = 1365299) B1365299
theorem B2155531 : Blo 566810 2155531 := bstep (se 1 (by rfl) ⟨1616648, by rfl⟩ : syracuseStep 2155531 = 3233297) B3233297
theorem B1434743 : Blo 566810 1434743 := bstep (se 1 (by rfl) ⟨1076057, by rfl⟩ : syracuseStep 1434743 = 2152115) B2152115
theorem B7267643 : Blo 566810 7267643 := bstep (se 1 (by rfl) ⟨5450732, by rfl⟩ : syracuseStep 7267643 = 10901465) B10901465
theorem B2155835 : Blo 566810 2155835 := bstep (se 1 (by rfl) ⟨1616876, by rfl⟩ : syracuseStep 2155835 = 3233753) B3233753
theorem B910711 : Blo 566810 910711 := bstep (se 1 (by rfl) ⟨683033, by rfl⟩ : syracuseStep 910711 = 1366067) B1366067
theorem B2876957 : Blo 566810 2876957 := bstep (se 3 (by rfl) ⟨539429, by rfl⟩ : syracuseStep 2876957 = 1078859) B1078859
theorem B2156321 : Blo 566810 2156321 := bstep (se 2 (by rfl) ⟨808620, by rfl⟩ : syracuseStep 2156321 = 1617241) B1617241
theorem B3237853 : Blo 566810 3237853 := bstep (se 3 (by rfl) ⟨607097, by rfl⟩ : syracuseStep 3237853 = 1214195) B1214195
theorem B2877443 : Blo 566810 2877443 := bstep (se 1 (by rfl) ⟨2158082, by rfl⟩ : syracuseStep 2877443 = 4316165) B4316165
theorem B4909189 : Blo 566810 4909189 := bstep (se 4 (by rfl) ⟨460236, by rfl⟩ : syracuseStep 4909189 = 920473) B920473
theorem B1534295 : Blo 566810 1534295 := bstep (se 1 (by rfl) ⟨1150721, by rfl⟩ : syracuseStep 1534295 = 2301443) B2301443
theorem B1436039 : Blo 566810 1436039 := bstep (se 1 (by rfl) ⟨1077029, by rfl⟩ : syracuseStep 1436039 = 2154059) B2154059
theorem B1436089 : Blo 566810 1436089 := bstep (se 2 (by rfl) ⟨538533, by rfl⟩ : syracuseStep 1436089 = 1077067) B1077067
theorem B12315179 : Blo 566810 12315179 := bstep (se 1 (by rfl) ⟨9236384, by rfl⟩ : syracuseStep 12315179 = 18472769) B18472769
theorem B2157293 : Blo 566810 2157293 := bstep (se 3 (by rfl) ⟨404492, by rfl⟩ : syracuseStep 2157293 = 808985) B808985
theorem B1370891 : Blo 566810 1370891 := bstep (se 1 (by rfl) ⟨1028168, by rfl⟩ : syracuseStep 1370891 = 2056337) B2056337
theorem B584591 : Blo 566810 584591 := bstep (se 1 (by rfl) ⟨438443, by rfl⟩ : syracuseStep 584591 = 876887) B876887
theorem B912313 : Blo 566810 912313 := bstep (se 2 (by rfl) ⟨342117, by rfl⟩ : syracuseStep 912313 = 684235) B684235
theorem B1436687 : Blo 566810 1436687 := bstep (se 1 (by rfl) ⟨1077515, by rfl⟩ : syracuseStep 1436687 = 2155031) B2155031
theorem B1076627 : Blo 566810 1076627 := bstep (se 1 (by rfl) ⟨807470, by rfl⟩ : syracuseStep 1076627 = 1614941) B1614941
theorem B1076665 : Blo 566810 1076665 := bstep (se 2 (by rfl) ⟨403749, by rfl⟩ : syracuseStep 1076665 = 807499) B807499
theorem B2911697 : Blo 566810 2911697 := bstep (se 2 (by rfl) ⟨1091886, by rfl⟩ : syracuseStep 2911697 = 2183773) B2183773
theorem B650767 : Blo 566810 650767 := bstep (se 1 (by rfl) ⟨488075, by rfl⟩ : syracuseStep 650767 = 976151) B976151
theorem B2879063 : Blo 566810 2879063 := bstep (se 1 (by rfl) ⟨2159297, by rfl⟩ : syracuseStep 2879063 = 4318595) B4318595
theorem B1437385 : Blo 566810 1437385 := bstep (se 2 (by rfl) ⟨539019, by rfl⟩ : syracuseStep 1437385 = 1078039) B1078039
theorem B4321025 : Blo 566810 4321025 := bstep (se 2 (by rfl) ⟨1620384, by rfl⟩ : syracuseStep 4321025 = 3240769) B3240769
theorem B1437527 : Blo 566810 1437527 := bstep (se 1 (by rfl) ⟨1078145, by rfl⟩ : syracuseStep 1437527 = 2156291) B2156291
theorem B684023 : Blo 566810 684023 := bstep (se 1 (by rfl) ⟨513017, by rfl⟩ : syracuseStep 684023 = 1026035) B1026035
theorem B2879549 : Blo 566810 2879549 := bstep (se 3 (by rfl) ⟨539915, by rfl⟩ : syracuseStep 2879549 = 1079831) B1079831
theorem B3076289 : Blo 566810 3076289 := bstep (se 2 (by rfl) ⟨1153608, by rfl⟩ : syracuseStep 3076289 = 2307217) B2307217
theorem B913799 : Blo 566810 913799 := bstep (se 1 (by rfl) ⟨685349, by rfl⟩ : syracuseStep 913799 = 1370699) B1370699
theorem B913979 : Blo 566810 913979 := bstep (se 1 (by rfl) ⟨685484, by rfl⟩ : syracuseStep 913979 = 1370969) B1370969
theorem B2159419 : Blo 566810 2159419 := bstep (se 1 (by rfl) ⟨1619564, by rfl⟩ : syracuseStep 2159419 = 3239129) B3239129
theorem B2159905 : Blo 566810 2159905 := bstep (se 2 (by rfl) ⟨809964, by rfl⟩ : syracuseStep 2159905 = 1619929) B1619929
theorem B3470629 : Blo 566810 3470629 := bstep (se 4 (by rfl) ⟨325371, by rfl⟩ : syracuseStep 3470629 = 650743) B650743
theorem B1078571 : Blo 566810 1078571 := bstep (se 1 (by rfl) ⟨808928, by rfl⟩ : syracuseStep 1078571 = 1617857) B1617857
theorem B3503513 : Blo 566810 3503513 := bstep (se 2 (by rfl) ⟨1313817, by rfl⟩ : syracuseStep 3503513 = 2627635) B2627635
theorem B3077585 : Blo 566810 3077585 := bstep (se 2 (by rfl) ⟨1154094, by rfl⟩ : syracuseStep 3077585 = 2308189) B2308189
theorem B1275407 : Blo 566810 1275407 := bstep (se 1 (by rfl) ⟨956555, by rfl⟩ : syracuseStep 1275407 = 1913111) B1913111
theorem B1275425 : Blo 566810 1275425 := bstep (se 2 (by rfl) ⟨478284, by rfl⟩ : syracuseStep 1275425 = 956569) B956569
theorem B4617805 : Blo 566810 4617805 := bstep (se 3 (by rfl) ⟨865838, by rfl⟩ : syracuseStep 4617805 = 1731677) B1731677
theorem B2881331 : Blo 566810 2881331 := bstep (se 1 (by rfl) ⟨2160998, by rfl⟩ : syracuseStep 2881331 = 4321997) B4321997
theorem B1439603 : Blo 566810 1439603 := bstep (se 1 (by rfl) ⟨1079702, by rfl⟩ : syracuseStep 1439603 = 2159405) B2159405
theorem B1275767 : Blo 566810 1275767 := bstep (se 1 (by rfl) ⟨956825, by rfl⟩ : syracuseStep 1275767 = 1913651) B1913651
theorem B7010327 : Blo 566810 7010327 := bstep (se 1 (by rfl) ⟨5257745, by rfl⟩ : syracuseStep 7010327 = 10515491) B10515491
theorem B1275947 : Blo 566810 1275947 := bstep (se 1 (by rfl) ⟨956960, by rfl⟩ : syracuseStep 1275947 = 1913921) B1913921
theorem B3242045 : Blo 566810 3242045 := bstep (se 3 (by rfl) ⟨607883, by rfl⟩ : syracuseStep 3242045 = 1215767) B1215767
theorem B2881655 : Blo 566810 2881655 := bstep (se 1 (by rfl) ⟨2161241, by rfl⟩ : syracuseStep 2881655 = 4322483) B4322483
theorem B1079497 : Blo 566810 1079497 := bstep (se 2 (by rfl) ⟨404811, by rfl⟩ : syracuseStep 1079497 = 809623) B809623
theorem B2160877 : Blo 566810 2160877 := bstep (se 3 (by rfl) ⟨405164, by rfl⟩ : syracuseStep 2160877 = 810329) B810329
theorem B850235 : Blo 566810 850235 := bstep (se 1 (by rfl) ⟨637676, by rfl⟩ : syracuseStep 850235 = 1275353) B1275353
theorem B850295 : Blo 566810 850295 := bstep (se 1 (by rfl) ⟨637721, by rfl⟩ : syracuseStep 850295 = 1275443) B1275443
theorem B1440119 : Blo 566810 1440119 := bstep (se 1 (by rfl) ⟨1080089, by rfl⟩ : syracuseStep 1440119 = 2160179) B2160179
theorem B850319 : Blo 566810 850319 := bstep (se 1 (by rfl) ⟨637739, by rfl⟩ : syracuseStep 850319 = 1275479) B1275479
theorem B1276307 : Blo 566810 1276307 := bstep (se 1 (by rfl) ⟨957230, by rfl⟩ : syracuseStep 1276307 = 1914461) B1914461
theorem B719275 : Blo 566810 719275 := bstep (se 1 (by rfl) ⟨539456, by rfl⟩ : syracuseStep 719275 = 1078913) B1078913
theorem B850361 : Blo 566810 850361 := bstep (se 2 (by rfl) ⟨318885, by rfl⟩ : syracuseStep 850361 = 637771) B637771
theorem B1276361 : Blo 566810 1276361 := bstep (se 2 (by rfl) ⟨478635, by rfl⟩ : syracuseStep 1276361 = 957271) B957271
theorem B850439 : Blo 566810 850439 := bstep (se 1 (by rfl) ⟨637829, by rfl⟩ : syracuseStep 850439 = 1275659) B1275659
theorem B2161181 : Blo 566810 2161181 := bstep (se 3 (by rfl) ⟨405221, by rfl⟩ : syracuseStep 2161181 = 810443) B810443
theorem B850475 : Blo 566810 850475 := bstep (se 1 (by rfl) ⟨637856, by rfl⟩ : syracuseStep 850475 = 1275713) B1275713
theorem B850505 : Blo 566810 850505 := bstep (se 2 (by rfl) ⟨318939, by rfl⟩ : syracuseStep 850505 = 637879) B637879
theorem B850619 : Blo 566810 850619 := bstep (se 1 (by rfl) ⟨637964, by rfl⟩ : syracuseStep 850619 = 1275929) B1275929
theorem B4094657 : Blo 566810 4094657 := bstep (se 2 (by rfl) ⟨1535496, by rfl⟩ : syracuseStep 4094657 = 3070993) B3070993
theorem B850679 : Blo 566810 850679 := bstep (se 1 (by rfl) ⟨638009, by rfl⟩ : syracuseStep 850679 = 1276019) B1276019
theorem B3242753 : Blo 566810 3242753 := bstep (se 2 (by rfl) ⟨1216032, by rfl⟩ : syracuseStep 3242753 = 2432065) B2432065
theorem B850703 : Blo 566810 850703 := bstep (se 1 (by rfl) ⟨638027, by rfl⟩ : syracuseStep 850703 = 1276055) B1276055
theorem B850745 : Blo 566810 850745 := bstep (se 2 (by rfl) ⟨319029, by rfl⟩ : syracuseStep 850745 = 638059) B638059
theorem B3078971 : Blo 566810 3078971 := bstep (se 1 (by rfl) ⟨2309228, by rfl⟩ : syracuseStep 3078971 = 4618457) B4618457
theorem B850823 : Blo 566810 850823 := bstep (se 1 (by rfl) ⟨638117, by rfl⟩ : syracuseStep 850823 = 1276235) B1276235
theorem B1080211 : Blo 566810 1080211 := bstep (se 1 (by rfl) ⟨810158, by rfl⟩ : syracuseStep 1080211 = 1620317) B1620317
theorem B850859 : Blo 566810 850859 := bstep (se 1 (by rfl) ⟨638144, by rfl⟩ : syracuseStep 850859 = 1276289) B1276289
theorem B850889 : Blo 566810 850889 := bstep (se 2 (by rfl) ⟨319083, by rfl⟩ : syracuseStep 850889 = 638167) B638167
theorem B851003 : Blo 566810 851003 := bstep (se 1 (by rfl) ⟨638252, by rfl⟩ : syracuseStep 851003 = 1276505) B1276505
theorem B2882627 : Blo 566810 2882627 := bstep (se 1 (by rfl) ⟨2161970, by rfl⟩ : syracuseStep 2882627 = 4323941) B4323941
theorem B851063 : Blo 566810 851063 := bstep (se 1 (by rfl) ⟨638297, by rfl⟩ : syracuseStep 851063 = 1276595) B1276595
theorem B1277063 : Blo 566810 1277063 := bstep (se 1 (by rfl) ⟨957797, by rfl⟩ : syracuseStep 1277063 = 1915595) B1915595
theorem B851087 : Blo 566810 851087 := bstep (se 1 (by rfl) ⟨638315, by rfl⟩ : syracuseStep 851087 = 1276631) B1276631
theorem B5176493 : Blo 566810 5176493 := bstep (se 3 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 5176493 = 1941185) B1941185
theorem B851129 : Blo 566810 851129 := bstep (se 2 (by rfl) ⟨319173, by rfl⟩ : syracuseStep 851129 = 638347) B638347
theorem B851207 : Blo 566810 851207 := bstep (se 1 (by rfl) ⟨638405, by rfl⟩ : syracuseStep 851207 = 1276811) B1276811
theorem B851243 : Blo 566810 851243 := bstep (se 1 (by rfl) ⟨638432, by rfl⟩ : syracuseStep 851243 = 1276865) B1276865
theorem B1277243 : Blo 566810 1277243 := bstep (se 1 (by rfl) ⟨957932, by rfl⟩ : syracuseStep 1277243 = 1915865) B1915865
theorem B851273 : Blo 566810 851273 := bstep (se 2 (by rfl) ⟨319227, by rfl⟩ : syracuseStep 851273 = 638455) B638455
theorem B1441111 : Blo 566810 1441111 := bstep (se 1 (by rfl) ⟨1080833, by rfl⟩ : syracuseStep 1441111 = 2161667) B2161667
theorem B720247 : Blo 566810 720247 := bstep (se 1 (by rfl) ⟨540185, by rfl⟩ : syracuseStep 720247 = 1080371) B1080371
theorem B2882951 : Blo 566810 2882951 := bstep (se 1 (by rfl) ⟨2162213, by rfl⟩ : syracuseStep 2882951 = 4324427) B4324427
theorem B1277369 : Blo 566810 1277369 := bstep (se 2 (by rfl) ⟨479013, by rfl⟩ : syracuseStep 1277369 = 958027) B958027
theorem B851387 : Blo 566810 851387 := bstep (se 1 (by rfl) ⟨638540, by rfl⟩ : syracuseStep 851387 = 1277081) B1277081
theorem B851447 : Blo 566810 851447 := bstep (se 1 (by rfl) ⟨638585, by rfl⟩ : syracuseStep 851447 = 1277171) B1277171
theorem B851471 : Blo 566810 851471 := bstep (se 1 (by rfl) ⟨638603, by rfl⟩ : syracuseStep 851471 = 1277207) B1277207
theorem B851513 : Blo 566810 851513 := bstep (se 2 (by rfl) ⟨319317, by rfl⟩ : syracuseStep 851513 = 638635) B638635
theorem B851591 : Blo 566810 851591 := bstep (se 1 (by rfl) ⟨638693, by rfl⟩ : syracuseStep 851591 = 1277387) B1277387
theorem B1441415 : Blo 566810 1441415 := bstep (se 1 (by rfl) ⟨1081061, by rfl⟩ : syracuseStep 1441415 = 2162123) B2162123
theorem B851627 : Blo 566810 851627 := bstep (se 1 (by rfl) ⟨638720, by rfl⟩ : syracuseStep 851627 = 1277441) B1277441
theorem B720571 : Blo 566810 720571 := bstep (se 1 (by rfl) ⟨540428, by rfl⟩ : syracuseStep 720571 = 1080857) B1080857
theorem B851657 : Blo 566810 851657 := bstep (se 2 (by rfl) ⟨319371, by rfl⟩ : syracuseStep 851657 = 638743) B638743
theorem B7307009 : Blo 566810 7307009 := bstep (se 2 (by rfl) ⟨2740128, by rfl⟩ : syracuseStep 7307009 = 5480257) B5480257
theorem B1441547 : Blo 566810 1441547 := bstep (se 1 (by rfl) ⟨1081160, by rfl⟩ : syracuseStep 1441547 = 2162321) B2162321
theorem B2588431 : Blo 566810 2588431 := bstep (se 1 (by rfl) ⟨1941323, by rfl⟩ : syracuseStep 2588431 = 3882647) B3882647
theorem B1277711 : Blo 566810 1277711 := bstep (se 1 (by rfl) ⟨958283, by rfl⟩ : syracuseStep 1277711 = 1916567) B1916567
theorem B1277729 : Blo 566810 1277729 := bstep (se 2 (by rfl) ⟨479148, by rfl⟩ : syracuseStep 1277729 = 958297) B958297
theorem B851771 : Blo 566810 851771 := bstep (se 1 (by rfl) ⟨638828, by rfl⟩ : syracuseStep 851771 = 1277657) B1277657
theorem B851831 : Blo 566810 851831 := bstep (se 1 (by rfl) ⟨638873, by rfl⟩ : syracuseStep 851831 = 1277747) B1277747
theorem B851855 : Blo 566810 851855 := bstep (se 1 (by rfl) ⟨638891, by rfl⟩ : syracuseStep 851855 = 1277783) B1277783
theorem B851897 : Blo 566810 851897 := bstep (se 2 (by rfl) ⟨319461, by rfl⟩ : syracuseStep 851897 = 638923) B638923
theorem B1081289 : Blo 566810 1081289 := bstep (se 2 (by rfl) ⟨405483, by rfl⟩ : syracuseStep 1081289 = 810967) B810967
theorem B2883599 : Blo 566810 2883599 := bstep (se 1 (by rfl) ⟨2162699, by rfl⟩ : syracuseStep 2883599 = 4325399) B4325399
theorem B852047 : Blo 566810 852047 := bstep (se 1 (by rfl) ⟨639035, by rfl⟩ : syracuseStep 852047 = 1278071) B1278071
theorem B1441871 : Blo 566810 1441871 := bstep (se 1 (by rfl) ⟨1081403, by rfl⟩ : syracuseStep 1441871 = 2162807) B2162807
theorem B1081441 : Blo 566810 1081441 := bstep (se 2 (by rfl) ⟨405540, by rfl⟩ : syracuseStep 1081441 = 811081) B811081
theorem B852167 : Blo 566810 852167 := bstep (se 1 (by rfl) ⟨639125, by rfl⟩ : syracuseStep 852167 = 1278251) B1278251
theorem B852329 : Blo 566810 852329 := bstep (se 2 (by rfl) ⟨319623, by rfl⟩ : syracuseStep 852329 = 639247) B639247
theorem B1081775 : Blo 566810 1081775 := bstep (se 1 (by rfl) ⟨811331, by rfl⟩ : syracuseStep 1081775 = 1622663) B1622663
theorem B852407 : Blo 566810 852407 := bstep (se 1 (by rfl) ⟨639305, by rfl⟩ : syracuseStep 852407 = 1278611) B1278611
theorem B852443 : Blo 566810 852443 := bstep (se 1 (by rfl) ⟨639332, by rfl⟩ : syracuseStep 852443 = 1278665) B1278665
theorem B1278503 : Blo 566810 1278503 := bstep (se 1 (by rfl) ⟨958877, by rfl⟩ : syracuseStep 1278503 = 1917755) B1917755
theorem B721487 : Blo 566810 721487 := bstep (se 1 (by rfl) ⟨541115, by rfl⟩ : syracuseStep 721487 = 1082231) B1082231
theorem B1213051 : Blo 566810 1213051 := bstep (se 1 (by rfl) ⟨909788, by rfl⟩ : syracuseStep 1213051 = 1819577) B1819577
theorem B1442519 : Blo 566810 1442519 := bstep (se 1 (by rfl) ⟨1081889, by rfl⟩ : syracuseStep 1442519 = 2163779) B2163779
theorem B2458475 : Blo 566810 2458475 := bstep (se 1 (by rfl) ⟨1843856, by rfl⟩ : syracuseStep 2458475 = 3687713) B3687713
theorem B1278827 : Blo 566810 1278827 := bstep (se 1 (by rfl) ⟨959120, by rfl⟩ : syracuseStep 1278827 = 1918241) B1918241
theorem B1278881 : Blo 566810 1278881 := bstep (se 2 (by rfl) ⟨479580, by rfl⟩ : syracuseStep 1278881 = 959161) B959161
theorem B852911 : Blo 566810 852911 := bstep (se 1 (by rfl) ⟨639683, by rfl⟩ : syracuseStep 852911 = 1279367) B1279367
theorem B853001 : Blo 566810 853001 := bstep (se 2 (by rfl) ⟨319875, by rfl⟩ : syracuseStep 853001 = 639751) B639751
theorem B853031 : Blo 566810 853031 := bstep (se 1 (by rfl) ⟨639773, by rfl⟩ : syracuseStep 853031 = 1279547) B1279547
theorem B1442873 : Blo 566810 1442873 := bstep (se 2 (by rfl) ⟨541077, by rfl⟩ : syracuseStep 1442873 = 1082155) B1082155
theorem B2163793 : Blo 566810 2163793 := bstep (se 2 (by rfl) ⟨811422, by rfl⟩ : syracuseStep 2163793 = 1622845) B1622845
theorem B853115 : Blo 566810 853115 := bstep (se 1 (by rfl) ⟨639836, by rfl⟩ : syracuseStep 853115 = 1279673) B1279673
theorem B2426051 : Blo 566810 2426051 := bstep (se 1 (by rfl) ⟨1819538, by rfl⟩ : syracuseStep 2426051 = 3639077) B3639077
theorem B1279223 : Blo 566810 1279223 := bstep (se 1 (by rfl) ⟨959417, by rfl⟩ : syracuseStep 1279223 = 1918835) B1918835
theorem B853241 : Blo 566810 853241 := bstep (se 2 (by rfl) ⟨319965, by rfl⟩ : syracuseStep 853241 = 639931) B639931
theorem B3900761 : Blo 566810 3900761 := bstep (se 2 (by rfl) ⟨1462785, by rfl⟩ : syracuseStep 3900761 = 2925571) B2925571
theorem B13305181 : Blo 566810 13305181 := bstep (se 3 (by rfl) ⟨2494721, by rfl⟩ : syracuseStep 13305181 = 4989443) B4989443
theorem B853343 : Blo 566810 853343 := bstep (se 1 (by rfl) ⟨640007, by rfl⟩ : syracuseStep 853343 = 1280015) B1280015
theorem B853355 : Blo 566810 853355 := bstep (se 1 (by rfl) ⟨640016, by rfl⟩ : syracuseStep 853355 = 1280033) B1280033
theorem B2164097 : Blo 566810 2164097 := bstep (se 2 (by rfl) ⟨811536, by rfl⟩ : syracuseStep 2164097 = 1623073) B1623073
theorem B7800209 : Blo 566810 7800209 := bstep (se 2 (by rfl) ⟨2925078, by rfl⟩ : syracuseStep 7800209 = 5850157) B5850157
theorem B4326857 : Blo 566810 4326857 := bstep (se 2 (by rfl) ⟨1622571, by rfl⟩ : syracuseStep 4326857 = 3245143) B3245143
theorem B1082899 : Blo 566810 1082899 := bstep (se 1 (by rfl) ⟨812174, by rfl⟩ : syracuseStep 1082899 = 1624349) B1624349
theorem B853583 : Blo 566810 853583 := bstep (se 1 (by rfl) ⟨640187, by rfl⟩ : syracuseStep 853583 = 1280375) B1280375
theorem B14419603 : Blo 566810 14419603 := bstep (se 1 (by rfl) ⟨10814702, by rfl⟩ : syracuseStep 14419603 = 21629405) B21629405
theorem B853703 : Blo 566810 853703 := bstep (se 1 (by rfl) ⟨640277, by rfl⟩ : syracuseStep 853703 = 1280555) B1280555
theorem B1083127 : Blo 566810 1083127 := bstep (se 1 (by rfl) ⟨812345, by rfl⟩ : syracuseStep 1083127 = 1624691) B1624691
theorem B1214281 : Blo 566810 1214281 := bstep (se 2 (by rfl) ⟨455355, by rfl⟩ : syracuseStep 1214281 = 910711) B910711
theorem B1279817 : Blo 566810 1279817 := bstep (se 2 (by rfl) ⟨479931, by rfl⟩ : syracuseStep 1279817 = 959863) B959863
theorem B2164553 : Blo 566810 2164553 := bstep (se 2 (by rfl) ⟨811707, by rfl⟩ : syracuseStep 2164553 = 1623415) B1623415
theorem B10389343 : Blo 566810 10389343 := bstep (se 1 (by rfl) ⟨7792007, by rfl⟩ : syracuseStep 10389343 = 15584015) B15584015
theorem B853865 : Blo 566810 853865 := bstep (se 2 (by rfl) ⟨320199, by rfl⟩ : syracuseStep 853865 = 640399) B640399
theorem B853943 : Blo 566810 853943 := bstep (se 1 (by rfl) ⟨640457, by rfl⟩ : syracuseStep 853943 = 1280915) B1280915
theorem B853979 : Blo 566810 853979 := bstep (se 1 (by rfl) ⟨640484, by rfl⟩ : syracuseStep 853979 = 1280969) B1280969
theorem B2164751 : Blo 566810 2164751 := bstep (se 1 (by rfl) ⟨1623563, by rfl⟩ : syracuseStep 2164751 = 3247127) B3247127
theorem B1083431 : Blo 566810 1083431 := bstep (se 1 (by rfl) ⟨812573, by rfl⟩ : syracuseStep 1083431 = 1625147) B1625147
theorem B3639563 : Blo 566810 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B3639613 : Blo 566810 3639613 := bstep (se 3 (by rfl) ⟨682427, by rfl⟩ : syracuseStep 3639613 = 1364855) B1364855
theorem B854447 : Blo 566810 854447 := bstep (se 1 (by rfl) ⟨640835, by rfl⟩ : syracuseStep 854447 = 1281671) B1281671
theorem B1214939 : Blo 566810 1214939 := bstep (se 1 (by rfl) ⟨911204, by rfl⟩ : syracuseStep 1214939 = 1822409) B1822409
theorem B854537 : Blo 566810 854537 := bstep (se 2 (by rfl) ⟨320451, by rfl⟩ : syracuseStep 854537 = 640903) B640903
theorem B3246601 : Blo 566810 3246601 := bstep (se 2 (by rfl) ⟨1217475, by rfl⟩ : syracuseStep 3246601 = 2434951) B2434951
theorem B854567 : Blo 566810 854567 := bstep (se 1 (by rfl) ⟨640925, by rfl⟩ : syracuseStep 854567 = 1281851) B1281851
theorem B1280609 : Blo 566810 1280609 := bstep (se 2 (by rfl) ⟨480228, by rfl⟩ : syracuseStep 1280609 = 960457) B960457
theorem B66292343 : Blo 566810 66292343 := bstep (se 1 (by rfl) ⟨49719257, by rfl⟩ : syracuseStep 66292343 = 99438515) B99438515
theorem B854651 : Blo 566810 854651 := bstep (se 1 (by rfl) ⟨640988, by rfl⟩ : syracuseStep 854651 = 1281977) B1281977
theorem B5474951 : Blo 566810 5474951 := bstep (se 1 (by rfl) ⟨4106213, by rfl⟩ : syracuseStep 5474951 = 8212427) B8212427
theorem B2886353 : Blo 566810 2886353 := bstep (se 2 (by rfl) ⟨1082382, by rfl⟩ : syracuseStep 2886353 = 2164765) B2164765
theorem B854777 : Blo 566810 854777 := bstep (se 2 (by rfl) ⟨320541, by rfl⟩ : syracuseStep 854777 = 641083) B641083
theorem B854879 : Blo 566810 854879 := bstep (se 1 (by rfl) ⟨641159, by rfl⟩ : syracuseStep 854879 = 1282319) B1282319
theorem B854891 : Blo 566810 854891 := bstep (se 1 (by rfl) ⟨641168, by rfl⟩ : syracuseStep 854891 = 1282337) B1282337
theorem B1280951 : Blo 566810 1280951 := bstep (se 1 (by rfl) ⟨960713, by rfl⟩ : syracuseStep 1280951 = 1921427) B1921427
theorem B106597387 : Blo 566810 106597387 := bstep (se 1 (by rfl) ⟨79948040, by rfl⟩ : syracuseStep 106597387 = 159896081) B159896081
theorem B855119 : Blo 566810 855119 := bstep (se 1 (by rfl) ⟨641339, by rfl⟩ : syracuseStep 855119 = 1282679) B1282679
theorem B855239 : Blo 566810 855239 := bstep (se 1 (by rfl) ⟨641429, by rfl⟩ : syracuseStep 855239 = 1282859) B1282859
theorem B855401 : Blo 566810 855401 := bstep (se 2 (by rfl) ⟨320775, by rfl⟩ : syracuseStep 855401 = 641551) B641551
theorem B855479 : Blo 566810 855479 := bstep (se 1 (by rfl) ⟨641609, by rfl⟩ : syracuseStep 855479 = 1283219) B1283219
theorem B855515 : Blo 566810 855515 := bstep (se 1 (by rfl) ⟨641636, by rfl⟩ : syracuseStep 855515 = 1283273) B1283273
theorem B1281545 : Blo 566810 1281545 := bstep (se 2 (by rfl) ⟨480579, by rfl⟩ : syracuseStep 1281545 = 961159) B961159
theorem B1183403 : Blo 566810 1183403 := bstep (se 1 (by rfl) ⟨887552, by rfl⟩ : syracuseStep 1183403 = 1775105) B1775105
theorem B8228573 : Blo 566810 8228573 := bstep (se 3 (by rfl) ⟨1542857, by rfl⟩ : syracuseStep 8228573 = 3085715) B3085715
theorem B1773305 : Blo 566810 1773305 := bstep (se 2 (by rfl) ⟨664989, by rfl⟩ : syracuseStep 1773305 = 1329979) B1329979
theorem B1281887 : Blo 566810 1281887 := bstep (se 1 (by rfl) ⟨961415, by rfl⟩ : syracuseStep 1281887 = 1922831) B1922831
theorem B1216417 : Blo 566810 1216417 := bstep (se 2 (by rfl) ⟨456156, by rfl⟩ : syracuseStep 1216417 = 912313) B912313
theorem B855983 : Blo 566810 855983 := bstep (se 1 (by rfl) ⟨641987, by rfl⟩ : syracuseStep 855983 = 1283975) B1283975
theorem B3248059 : Blo 566810 3248059 := bstep (se 1 (by rfl) ⟨2436044, by rfl⟩ : syracuseStep 3248059 = 4872089) B4872089
theorem B856073 : Blo 566810 856073 := bstep (se 2 (by rfl) ⟨321027, by rfl⟩ : syracuseStep 856073 = 642055) B642055
theorem B1282067 : Blo 566810 1282067 := bstep (se 1 (by rfl) ⟨961550, by rfl⟩ : syracuseStep 1282067 = 1923101) B1923101
theorem B856103 : Blo 566810 856103 := bstep (se 1 (by rfl) ⟨642077, by rfl⟩ : syracuseStep 856103 = 1284155) B1284155
theorem B856187 : Blo 566810 856187 := bstep (se 1 (by rfl) ⟨642140, by rfl⟩ : syracuseStep 856187 = 1284281) B1284281
theorem B1282409 : Blo 566810 1282409 := bstep (se 2 (by rfl) ⟨480903, by rfl⟩ : syracuseStep 1282409 = 961807) B961807
theorem B1151687 : Blo 566810 1151687 := bstep (se 1 (by rfl) ⟨863765, by rfl⟩ : syracuseStep 1151687 = 1727531) B1727531
theorem B2724637 : Blo 566810 2724637 := bstep (se 3 (by rfl) ⟨510869, by rfl⟩ : syracuseStep 2724637 = 1021739) B1021739
theorem B1283003 : Blo 566810 1283003 := bstep (se 1 (by rfl) ⟨962252, by rfl⟩ : syracuseStep 1283003 = 1924505) B1924505
theorem B1283129 : Blo 566810 1283129 := bstep (se 2 (by rfl) ⟨481173, by rfl⟩ : syracuseStep 1283129 = 962347) B962347
theorem B2888783 : Blo 566810 2888783 := bstep (se 1 (by rfl) ⟨2166587, by rfl⟩ : syracuseStep 2888783 = 4333175) B4333175
theorem B1283471 : Blo 566810 1283471 := bstep (se 1 (by rfl) ⟨962603, by rfl⟩ : syracuseStep 1283471 = 1925207) B1925207
theorem B1283795 : Blo 566810 1283795 := bstep (se 1 (by rfl) ⟨962846, by rfl⟩ : syracuseStep 1283795 = 1925693) B1925693
theorem B2889431 : Blo 566810 2889431 := bstep (se 1 (by rfl) ⟨2167073, by rfl⟩ : syracuseStep 2889431 = 4334147) B4334147
theorem B4101947 : Blo 566810 4101947 := bstep (se 1 (by rfl) ⟨3076460, by rfl⟩ : syracuseStep 4101947 = 6152921) B6152921
theorem B956495 : Blo 566810 956495 := bstep (se 1 (by rfl) ⟨717371, by rfl⟩ : syracuseStep 956495 = 1434743) B1434743
theorem B8198243 : Blo 566810 8198243 := bstep (se 1 (by rfl) ⟨6148682, by rfl⟩ : syracuseStep 8198243 = 12297365) B12297365
theorem B1022863 : Blo 566810 1022863 := bstep (se 1 (by rfl) ⟨767147, by rfl⟩ : syracuseStep 1022863 = 1534295) B1534295
theorem B957359 : Blo 566810 957359 := bstep (se 1 (by rfl) ⟨718019, by rfl⟩ : syracuseStep 957359 = 1436039) B1436039
theorem B4627505 : Blo 566810 4627505 := bstep (se 2 (by rfl) ⟨1735314, by rfl⟩ : syracuseStep 4627505 = 3470629) B3470629
theorem B957791 : Blo 566810 957791 := bstep (se 1 (by rfl) ⟨718343, by rfl⟩ : syracuseStep 957791 = 1436687) B1436687
theorem B6167933 : Blo 566810 6167933 := bstep (se 3 (by rfl) ⟨1156487, by rfl⟩ : syracuseStep 6167933 = 2312975) B2312975
theorem B7806451 : Blo 566810 7806451 := bstep (se 1 (by rfl) ⟨5854838, by rfl⟩ : syracuseStep 7806451 = 11709677) B11709677
theorem B1941131 : Blo 566810 1941131 := bstep (se 1 (by rfl) ⟨1455848, by rfl⟩ : syracuseStep 1941131 = 2911697) B2911697
theorem B958351 : Blo 566810 958351 := bstep (se 1 (by rfl) ⟨718763, by rfl⟩ : syracuseStep 958351 = 1437527) B1437527
theorem B959033 : Blo 566810 959033 := bstep (se 2 (by rfl) ⟨359637, by rfl⟩ : syracuseStep 959033 = 719275) B719275
theorem B2433721 : Blo 566810 2433721 := bstep (se 2 (by rfl) ⟨912645, by rfl⟩ : syracuseStep 2433721 = 1825291) B1825291
theorem B2335675 : Blo 566810 2335675 := bstep (se 1 (by rfl) ⟨1751756, by rfl⟩ : syracuseStep 2335675 = 3503513) B3503513
theorem B4596983 : Blo 566810 4596983 := bstep (se 1 (by rfl) ⟨3447737, by rfl⟩ : syracuseStep 4596983 = 6895475) B6895475
theorem B959735 : Blo 566810 959735 := bstep (se 1 (by rfl) ⟨719801, by rfl⟩ : syracuseStep 959735 = 1439603) B1439603
theorem B4105637 : Blo 566810 4105637 := bstep (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) B769807
theorem B6235637 : Blo 566810 6235637 := bstep (se 5 (by rfl) ⟨292295, by rfl⟩ : syracuseStep 6235637 = 584591) B584591
theorem B5481989 : Blo 566810 5481989 := bstep (se 4 (by rfl) ⟨513936, by rfl⟩ : syracuseStep 5481989 = 1027873) B1027873
theorem B566823 : Blo 566810 566823 := bstep (se 1 (by rfl) ⟨425117, by rfl⟩ : syracuseStep 566823 = 850235) B850235
theorem B1844795 : Blo 566810 1844795 := bstep (se 1 (by rfl) ⟨1383596, by rfl⟩ : syracuseStep 1844795 = 2767193) B2767193
theorem B566863 : Blo 566810 566863 := bstep (se 1 (by rfl) ⟨425147, by rfl⟩ : syracuseStep 566863 = 850295) B850295
theorem B960079 : Blo 566810 960079 := bstep (se 1 (by rfl) ⟨720059, by rfl⟩ : syracuseStep 960079 = 1440119) B1440119
theorem B566879 : Blo 566810 566879 := bstep (se 1 (by rfl) ⟨425159, by rfl⟩ : syracuseStep 566879 = 850319) B850319
theorem B566907 : Blo 566810 566907 := bstep (se 1 (by rfl) ⟨425180, by rfl⟩ : syracuseStep 566907 = 850361) B850361
theorem B566959 : Blo 566810 566959 := bstep (se 1 (by rfl) ⟨425219, by rfl⟩ : syracuseStep 566959 = 850439) B850439
theorem B566983 : Blo 566810 566983 := bstep (se 1 (by rfl) ⟨425237, by rfl⟩ : syracuseStep 566983 = 850475) B850475
theorem B567003 : Blo 566810 567003 := bstep (se 1 (by rfl) ⟨425252, by rfl⟩ : syracuseStep 567003 = 850505) B850505
theorem B567079 : Blo 566810 567079 := bstep (se 1 (by rfl) ⟨425309, by rfl⟩ : syracuseStep 567079 = 850619) B850619
theorem B2729771 : Blo 566810 2729771 := bstep (se 1 (by rfl) ⟨2047328, by rfl⟩ : syracuseStep 2729771 = 4094657) B4094657
theorem B960329 : Blo 566810 960329 := bstep (se 2 (by rfl) ⟨360123, by rfl⟩ : syracuseStep 960329 = 720247) B720247
theorem B567119 : Blo 566810 567119 := bstep (se 1 (by rfl) ⟨425339, by rfl⟩ : syracuseStep 567119 = 850679) B850679
theorem B567135 : Blo 566810 567135 := bstep (se 1 (by rfl) ⟨425351, by rfl⟩ : syracuseStep 567135 = 850703) B850703
theorem B6563693 : Blo 566810 6563693 := bstep (se 3 (by rfl) ⟨1230692, by rfl⟩ : syracuseStep 6563693 = 2461385) B2461385
theorem B567163 : Blo 566810 567163 := bstep (se 1 (by rfl) ⟨425372, by rfl⟩ : syracuseStep 567163 = 850745) B850745
theorem B567215 : Blo 566810 567215 := bstep (se 1 (by rfl) ⟨425411, by rfl⟩ : syracuseStep 567215 = 850823) B850823
theorem B567239 : Blo 566810 567239 := bstep (se 1 (by rfl) ⟨425429, by rfl⟩ : syracuseStep 567239 = 850859) B850859
theorem B567259 : Blo 566810 567259 := bstep (se 1 (by rfl) ⟨425444, by rfl⟩ : syracuseStep 567259 = 850889) B850889
theorem B567335 : Blo 566810 567335 := bstep (se 1 (by rfl) ⟨425501, by rfl⟩ : syracuseStep 567335 = 851003) B851003
theorem B567375 : Blo 566810 567375 := bstep (se 1 (by rfl) ⟨425531, by rfl⟩ : syracuseStep 567375 = 851063) B851063
theorem B567391 : Blo 566810 567391 := bstep (se 1 (by rfl) ⟨425543, by rfl⟩ : syracuseStep 567391 = 851087) B851087
theorem B3450995 : Blo 566810 3450995 := bstep (se 1 (by rfl) ⟨2588246, by rfl⟩ : syracuseStep 3450995 = 5176493) B5176493
theorem B567419 : Blo 566810 567419 := bstep (se 1 (by rfl) ⟨425564, by rfl⟩ : syracuseStep 567419 = 851129) B851129
theorem B567471 : Blo 566810 567471 := bstep (se 1 (by rfl) ⟨425603, by rfl⟩ : syracuseStep 567471 = 851207) B851207
theorem B567495 : Blo 566810 567495 := bstep (se 1 (by rfl) ⟨425621, by rfl⟩ : syracuseStep 567495 = 851243) B851243
theorem B567515 : Blo 566810 567515 := bstep (se 1 (by rfl) ⟨425636, by rfl⟩ : syracuseStep 567515 = 851273) B851273
theorem B960761 : Blo 566810 960761 := bstep (se 2 (by rfl) ⟨360285, by rfl⟩ : syracuseStep 960761 = 720571) B720571
theorem B567591 : Blo 566810 567591 := bstep (se 1 (by rfl) ⟨425693, by rfl⟩ : syracuseStep 567591 = 851387) B851387
theorem B567631 : Blo 566810 567631 := bstep (se 1 (by rfl) ⟨425723, by rfl⟩ : syracuseStep 567631 = 851447) B851447
theorem B567647 : Blo 566810 567647 := bstep (se 1 (by rfl) ⟨425735, by rfl⟩ : syracuseStep 567647 = 851471) B851471
theorem B3451241 : Blo 566810 3451241 := bstep (se 2 (by rfl) ⟨1294215, by rfl⟩ : syracuseStep 3451241 = 2588431) B2588431
theorem B567675 : Blo 566810 567675 := bstep (se 1 (by rfl) ⟨425756, by rfl⟩ : syracuseStep 567675 = 851513) B851513
theorem B567727 : Blo 566810 567727 := bstep (se 1 (by rfl) ⟨425795, by rfl⟩ : syracuseStep 567727 = 851591) B851591
theorem B960943 : Blo 566810 960943 := bstep (se 1 (by rfl) ⟨720707, by rfl⟩ : syracuseStep 960943 = 1441415) B1441415
theorem B567751 : Blo 566810 567751 := bstep (se 1 (by rfl) ⟨425813, by rfl⟩ : syracuseStep 567751 = 851627) B851627
theorem B567771 : Blo 566810 567771 := bstep (se 1 (by rfl) ⟨425828, by rfl⟩ : syracuseStep 567771 = 851657) B851657
theorem B961031 : Blo 566810 961031 := bstep (se 1 (by rfl) ⟨720773, by rfl⟩ : syracuseStep 961031 = 1441547) B1441547
theorem B4663817 : Blo 566810 4663817 := bstep (se 2 (by rfl) ⟨1748931, by rfl⟩ : syracuseStep 4663817 = 3497863) B3497863
theorem B1026569 : Blo 566810 1026569 := bstep (se 2 (by rfl) ⟨384963, by rfl⟩ : syracuseStep 1026569 = 769927) B769927
theorem B567847 : Blo 566810 567847 := bstep (se 1 (by rfl) ⟨425885, by rfl⟩ : syracuseStep 567847 = 851771) B851771
theorem B567887 : Blo 566810 567887 := bstep (se 1 (by rfl) ⟨425915, by rfl⟩ : syracuseStep 567887 = 851831) B851831
theorem B567903 : Blo 566810 567903 := bstep (se 1 (by rfl) ⟨425927, by rfl⟩ : syracuseStep 567903 = 851855) B851855
theorem B567931 : Blo 566810 567931 := bstep (se 1 (by rfl) ⟨425948, by rfl⟩ : syracuseStep 567931 = 851897) B851897
theorem B567983 : Blo 566810 567983 := bstep (se 1 (by rfl) ⟨425987, by rfl⟩ : syracuseStep 567983 = 851975) B851975
theorem B7383737 : Blo 566810 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B568007 : Blo 566810 568007 := bstep (se 1 (by rfl) ⟨426005, by rfl⟩ : syracuseStep 568007 = 852011) B852011
theorem B568027 : Blo 566810 568027 := bstep (se 1 (by rfl) ⟨426020, by rfl⟩ : syracuseStep 568027 = 852041) B852041
theorem B568103 : Blo 566810 568103 := bstep (se 1 (by rfl) ⟨426077, by rfl⟩ : syracuseStep 568103 = 852155) B852155
theorem B568143 : Blo 566810 568143 := bstep (se 1 (by rfl) ⟨426107, by rfl⟩ : syracuseStep 568143 = 852215) B852215
theorem B568159 : Blo 566810 568159 := bstep (se 1 (by rfl) ⟨426119, by rfl⟩ : syracuseStep 568159 = 852239) B852239
theorem B961375 : Blo 566810 961375 := bstep (se 1 (by rfl) ⟨721031, by rfl⟩ : syracuseStep 961375 = 1442063) B1442063
theorem B568187 : Blo 566810 568187 := bstep (se 1 (by rfl) ⟨426140, by rfl⟩ : syracuseStep 568187 = 852281) B852281
theorem B568239 : Blo 566810 568239 := bstep (se 1 (by rfl) ⟨426179, by rfl⟩ : syracuseStep 568239 = 852359) B852359
theorem B961463 : Blo 566810 961463 := bstep (se 1 (by rfl) ⟨721097, by rfl⟩ : syracuseStep 961463 = 1442195) B1442195
theorem B568263 : Blo 566810 568263 := bstep (se 1 (by rfl) ⟨426197, by rfl⟩ : syracuseStep 568263 = 852395) B852395
theorem B568283 : Blo 566810 568283 := bstep (se 1 (by rfl) ⟨426212, by rfl⟩ : syracuseStep 568283 = 852425) B852425
theorem B568359 : Blo 566810 568359 := bstep (se 1 (by rfl) ⟨426269, by rfl⟩ : syracuseStep 568359 = 852539) B852539
theorem B568399 : Blo 566810 568399 := bstep (se 1 (by rfl) ⟨426299, by rfl⟩ : syracuseStep 568399 = 852599) B852599
theorem B568415 : Blo 566810 568415 := bstep (se 1 (by rfl) ⟨426311, by rfl⟩ : syracuseStep 568415 = 852623) B852623
theorem B568443 : Blo 566810 568443 := bstep (se 1 (by rfl) ⟨426332, by rfl⟩ : syracuseStep 568443 = 852665) B852665
theorem B568495 : Blo 566810 568495 := bstep (se 1 (by rfl) ⟨426371, by rfl⟩ : syracuseStep 568495 = 852743) B852743
theorem B568519 : Blo 566810 568519 := bstep (se 1 (by rfl) ⟨426389, by rfl⟩ : syracuseStep 568519 = 852779) B852779
theorem B568539 : Blo 566810 568539 := bstep (se 1 (by rfl) ⟨426404, by rfl⟩ : syracuseStep 568539 = 852809) B852809
theorem B568615 : Blo 566810 568615 := bstep (se 1 (by rfl) ⟨426461, by rfl⟩ : syracuseStep 568615 = 852923) B852923
theorem B568655 : Blo 566810 568655 := bstep (se 1 (by rfl) ⟨426491, by rfl⟩ : syracuseStep 568655 = 852983) B852983
theorem B8858969 : Blo 566810 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B568671 : Blo 566810 568671 := bstep (se 1 (by rfl) ⟨426503, by rfl⟩ : syracuseStep 568671 = 853007) B853007
theorem B568699 : Blo 566810 568699 := bstep (se 1 (by rfl) ⟨426524, by rfl⟩ : syracuseStep 568699 = 853049) B853049
theorem B568751 : Blo 566810 568751 := bstep (se 1 (by rfl) ⟨426563, by rfl⟩ : syracuseStep 568751 = 853127) B853127
theorem B568775 : Blo 566810 568775 := bstep (se 1 (by rfl) ⟨426581, by rfl⟩ : syracuseStep 568775 = 853163) B853163
theorem B568795 : Blo 566810 568795 := bstep (se 1 (by rfl) ⟨426596, by rfl⟩ : syracuseStep 568795 = 853193) B853193
theorem B962057 : Blo 566810 962057 := bstep (se 2 (by rfl) ⟨360771, by rfl⟩ : syracuseStep 962057 = 721543) B721543
theorem B1945127 : Blo 566810 1945127 := bstep (se 1 (by rfl) ⟨1458845, by rfl⟩ : syracuseStep 1945127 = 2917691) B2917691
theorem B568871 : Blo 566810 568871 := bstep (se 1 (by rfl) ⟨426653, by rfl⟩ : syracuseStep 568871 = 853307) B853307
theorem B568911 : Blo 566810 568911 := bstep (se 1 (by rfl) ⟨426683, by rfl⟩ : syracuseStep 568911 = 853367) B853367
theorem B568927 : Blo 566810 568927 := bstep (se 1 (by rfl) ⟨426695, by rfl⟩ : syracuseStep 568927 = 853391) B853391
theorem B568955 : Blo 566810 568955 := bstep (se 1 (by rfl) ⟨426716, by rfl⟩ : syracuseStep 568955 = 853433) B853433
theorem B1945223 : Blo 566810 1945223 := bstep (se 1 (by rfl) ⟨1458917, by rfl⟩ : syracuseStep 1945223 = 2917835) B2917835
theorem B962219 : Blo 566810 962219 := bstep (se 1 (by rfl) ⟨721664, by rfl⟩ : syracuseStep 962219 = 1443329) B1443329
theorem B569007 : Blo 566810 569007 := bstep (se 1 (by rfl) ⟨426755, by rfl⟩ : syracuseStep 569007 = 853511) B853511
theorem B2436797 : Blo 566810 2436797 := bstep (se 3 (by rfl) ⟨456899, by rfl⟩ : syracuseStep 2436797 = 913799) B913799
theorem B569031 : Blo 566810 569031 := bstep (se 1 (by rfl) ⟨426773, by rfl⟩ : syracuseStep 569031 = 853547) B853547
theorem B11710169 : Blo 566810 11710169 := bstep (se 2 (by rfl) ⟨4391313, by rfl⟩ : syracuseStep 11710169 = 8782627) B8782627
theorem B569051 : Blo 566810 569051 := bstep (se 1 (by rfl) ⟨426788, by rfl⟩ : syracuseStep 569051 = 853577) B853577
theorem B2731769 : Blo 566810 2731769 := bstep (se 2 (by rfl) ⟨1024413, by rfl⟩ : syracuseStep 2731769 = 2048827) B2048827
theorem B569127 : Blo 566810 569127 := bstep (se 1 (by rfl) ⟨426845, by rfl⟩ : syracuseStep 569127 = 853691) B853691
theorem B569167 : Blo 566810 569167 := bstep (se 1 (by rfl) ⟨426875, by rfl⟩ : syracuseStep 569167 = 853751) B853751
theorem B569183 : Blo 566810 569183 := bstep (se 1 (by rfl) ⟨426887, by rfl⟩ : syracuseStep 569183 = 853775) B853775
theorem B569211 : Blo 566810 569211 := bstep (se 1 (by rfl) ⟨426908, by rfl⟩ : syracuseStep 569211 = 853817) B853817
theorem B569263 : Blo 566810 569263 := bstep (se 1 (by rfl) ⟨426947, by rfl⟩ : syracuseStep 569263 = 853895) B853895
theorem B569287 : Blo 566810 569287 := bstep (se 1 (by rfl) ⟨426965, by rfl⟩ : syracuseStep 569287 = 853931) B853931
theorem B569307 : Blo 566810 569307 := bstep (se 1 (by rfl) ⟨426980, by rfl⟩ : syracuseStep 569307 = 853961) B853961
theorem B569383 : Blo 566810 569383 := bstep (se 1 (by rfl) ⟨427037, by rfl⟩ : syracuseStep 569383 = 854075) B854075
theorem B962617 : Blo 566810 962617 := bstep (se 2 (by rfl) ⟨360981, by rfl⟩ : syracuseStep 962617 = 721963) B721963
theorem B569423 : Blo 566810 569423 := bstep (se 1 (by rfl) ⟨427067, by rfl⟩ : syracuseStep 569423 = 854135) B854135
theorem B569439 : Blo 566810 569439 := bstep (se 1 (by rfl) ⟨427079, by rfl⟩ : syracuseStep 569439 = 854159) B854159
theorem B569467 : Blo 566810 569467 := bstep (se 1 (by rfl) ⟨427100, by rfl⟩ : syracuseStep 569467 = 854201) B854201
theorem B1913003 : Blo 566810 1913003 := bstep (se 1 (by rfl) ⟨1434752, by rfl⟩ : syracuseStep 1913003 = 2869505) B2869505
theorem B569519 : Blo 566810 569519 := bstep (se 1 (by rfl) ⟨427139, by rfl⟩ : syracuseStep 569519 = 854279) B854279
theorem B569543 : Blo 566810 569543 := bstep (se 1 (by rfl) ⟨427157, by rfl⟩ : syracuseStep 569543 = 854315) B854315
theorem B962759 : Blo 566810 962759 := bstep (se 1 (by rfl) ⟨722069, by rfl⟩ : syracuseStep 962759 = 1444139) B1444139
theorem B569563 : Blo 566810 569563 := bstep (se 1 (by rfl) ⟨427172, by rfl⟩ : syracuseStep 569563 = 854345) B854345
theorem B569639 : Blo 566810 569639 := bstep (se 1 (by rfl) ⟨427229, by rfl⟩ : syracuseStep 569639 = 854459) B854459
theorem B569679 : Blo 566810 569679 := bstep (se 1 (by rfl) ⟨427259, by rfl⟩ : syracuseStep 569679 = 854519) B854519
theorem B569695 : Blo 566810 569695 := bstep (se 1 (by rfl) ⟨427271, by rfl⟩ : syracuseStep 569695 = 854543) B854543
theorem B962921 : Blo 566810 962921 := bstep (se 2 (by rfl) ⟨361095, by rfl⟩ : syracuseStep 962921 = 722191) B722191
theorem B569723 : Blo 566810 569723 := bstep (se 1 (by rfl) ⟨427292, by rfl⟩ : syracuseStep 569723 = 854585) B854585
theorem B569775 : Blo 566810 569775 := bstep (se 1 (by rfl) ⟨427331, by rfl⟩ : syracuseStep 569775 = 854663) B854663
theorem B569799 : Blo 566810 569799 := bstep (se 1 (by rfl) ⟨427349, by rfl⟩ : syracuseStep 569799 = 854699) B854699
theorem B569819 : Blo 566810 569819 := bstep (se 1 (by rfl) ⟨427364, by rfl⟩ : syracuseStep 569819 = 854729) B854729
theorem B1618471 : Blo 566810 1618471 := bstep (se 1 (by rfl) ⟨1213853, by rfl⟩ : syracuseStep 1618471 = 2427707) B2427707
theorem B569895 : Blo 566810 569895 := bstep (se 1 (by rfl) ⟨427421, by rfl⟩ : syracuseStep 569895 = 854843) B854843
theorem B569935 : Blo 566810 569935 := bstep (se 1 (by rfl) ⟨427451, by rfl⟩ : syracuseStep 569935 = 854903) B854903
theorem B569951 : Blo 566810 569951 := bstep (se 1 (by rfl) ⟨427463, by rfl⟩ : syracuseStep 569951 = 854927) B854927
theorem B569979 : Blo 566810 569979 := bstep (se 1 (by rfl) ⟨427484, by rfl⟩ : syracuseStep 569979 = 854969) B854969
theorem B570031 : Blo 566810 570031 := bstep (se 1 (by rfl) ⟨427523, by rfl⟩ : syracuseStep 570031 = 855047) B855047
theorem B1913543 : Blo 566810 1913543 := bstep (se 1 (by rfl) ⟨1435157, by rfl⟩ : syracuseStep 1913543 = 2870315) B2870315
theorem B570055 : Blo 566810 570055 := bstep (se 1 (by rfl) ⟨427541, by rfl⟩ : syracuseStep 570055 = 855083) B855083
theorem B1618643 : Blo 566810 1618643 := bstep (se 1 (by rfl) ⟨1213982, by rfl⟩ : syracuseStep 1618643 = 2427965) B2427965
theorem B570075 : Blo 566810 570075 := bstep (se 1 (by rfl) ⟨427556, by rfl⟩ : syracuseStep 570075 = 855113) B855113
theorem B570151 : Blo 566810 570151 := bstep (se 1 (by rfl) ⟨427613, by rfl⟩ : syracuseStep 570151 = 855227) B855227
theorem B570191 : Blo 566810 570191 := bstep (se 1 (by rfl) ⟨427643, by rfl⟩ : syracuseStep 570191 = 855287) B855287
theorem B570207 : Blo 566810 570207 := bstep (se 1 (by rfl) ⟨427655, by rfl⟩ : syracuseStep 570207 = 855311) B855311
theorem B570235 : Blo 566810 570235 := bstep (se 1 (by rfl) ⟨427676, by rfl⟩ : syracuseStep 570235 = 855353) B855353
theorem B570287 : Blo 566810 570287 := bstep (se 1 (by rfl) ⟨427715, by rfl⟩ : syracuseStep 570287 = 855431) B855431
theorem B1946551 : Blo 566810 1946551 := bstep (se 1 (by rfl) ⟨1459913, by rfl⟩ : syracuseStep 1946551 = 2919827) B2919827
theorem B570311 : Blo 566810 570311 := bstep (se 1 (by rfl) ⟨427733, by rfl⟩ : syracuseStep 570311 = 855467) B855467
theorem B570331 : Blo 566810 570331 := bstep (se 1 (by rfl) ⟨427748, by rfl⟩ : syracuseStep 570331 = 855497) B855497
theorem B570407 : Blo 566810 570407 := bstep (se 1 (by rfl) ⟨427805, by rfl⟩ : syracuseStep 570407 = 855611) B855611
theorem B570447 : Blo 566810 570447 := bstep (se 1 (by rfl) ⟨427835, by rfl⟩ : syracuseStep 570447 = 855671) B855671
theorem B570463 : Blo 566810 570463 := bstep (se 1 (by rfl) ⟨427847, by rfl⟩ : syracuseStep 570463 = 855695) B855695
theorem B570491 : Blo 566810 570491 := bstep (se 1 (by rfl) ⟨427868, by rfl⟩ : syracuseStep 570491 = 855737) B855737
theorem B570543 : Blo 566810 570543 := bstep (se 1 (by rfl) ⟨427907, by rfl⟩ : syracuseStep 570543 = 855815) B855815
theorem B570567 : Blo 566810 570567 := bstep (se 1 (by rfl) ⟨427925, by rfl⟩ : syracuseStep 570567 = 855851) B855851
theorem B570587 : Blo 566810 570587 := bstep (se 1 (by rfl) ⟨427940, by rfl⟩ : syracuseStep 570587 = 855881) B855881
theorem B570663 : Blo 566810 570663 := bstep (se 1 (by rfl) ⟨427997, by rfl⟩ : syracuseStep 570663 = 855995) B855995
theorem B570703 : Blo 566810 570703 := bstep (se 1 (by rfl) ⟨428027, by rfl⟩ : syracuseStep 570703 = 856055) B856055
theorem B570719 : Blo 566810 570719 := bstep (se 1 (by rfl) ⟨428039, by rfl⟩ : syracuseStep 570719 = 856079) B856079
theorem B570747 : Blo 566810 570747 := bstep (se 1 (by rfl) ⟨428060, by rfl⟩ : syracuseStep 570747 = 856121) B856121
theorem B570799 : Blo 566810 570799 := bstep (se 1 (by rfl) ⟨428099, by rfl⟩ : syracuseStep 570799 = 856199) B856199
theorem B1914407 : Blo 566810 1914407 := bstep (se 1 (by rfl) ⟨1435805, by rfl⟩ : syracuseStep 1914407 = 2871611) B2871611
theorem B1914515 : Blo 566810 1914515 := bstep (se 1 (by rfl) ⟨1435886, by rfl⟩ : syracuseStep 1914515 = 2871773) B2871773
theorem B15513281 : Blo 566810 15513281 := bstep (se 2 (by rfl) ⟨5817480, by rfl⟩ : syracuseStep 15513281 = 11634961) B11634961
theorem B1914731 : Blo 566810 1914731 := bstep (se 1 (by rfl) ⟨1436048, by rfl⟩ : syracuseStep 1914731 = 2872097) B2872097
theorem B1914785 : Blo 566810 1914785 := bstep (se 2 (by rfl) ⟨718044, by rfl⟩ : syracuseStep 1914785 = 1436089) B1436089
theorem B1619975 : Blo 566810 1619975 := bstep (se 1 (by rfl) ⟨1214981, by rfl⟩ : syracuseStep 1619975 = 2429963) B2429963
theorem B4110365 : Blo 566810 4110365 := bstep (se 3 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 4110365 = 1541387) B1541387
theorem B1816937 : Blo 566810 1816937 := bstep (se 2 (by rfl) ⟨681351, by rfl⟩ : syracuseStep 1816937 = 1362703) B1362703
theorem B1915379 : Blo 566810 1915379 := bstep (se 1 (by rfl) ⟨1436534, by rfl⟩ : syracuseStep 1915379 = 2873069) B2873069
theorem B1817387 : Blo 566810 1817387 := bstep (se 1 (by rfl) ⟨1363040, by rfl⟩ : syracuseStep 1817387 = 2726081) B2726081
theorem B1096553 : Blo 566810 1096553 := bstep (se 2 (by rfl) ⟨411207, by rfl⟩ : syracuseStep 1096553 = 822415) B822415
theorem B768943 : Blo 566810 768943 := bstep (se 1 (by rfl) ⟨576707, by rfl⟩ : syracuseStep 768943 = 1153415) B1153415
theorem B637915 : Blo 566810 637915 := bstep (se 1 (by rfl) ⟨478436, by rfl⟩ : syracuseStep 637915 = 956873) B956873
theorem B1915919 : Blo 566810 1915919 := bstep (se 1 (by rfl) ⟨1436939, by rfl⟩ : syracuseStep 1915919 = 2873879) B2873879
theorem B2046995 : Blo 566810 2046995 := bstep (se 1 (by rfl) ⟨1535246, by rfl⟩ : syracuseStep 2046995 = 3070493) B3070493
theorem B867689 : Blo 566810 867689 := bstep (se 2 (by rfl) ⟨325383, by rfl⟩ : syracuseStep 867689 = 650767) B650767
theorem B4308389 : Blo 566810 4308389 := bstep (se 4 (by rfl) ⟨403911, by rfl⟩ : syracuseStep 4308389 = 807823) B807823
theorem B638383 : Blo 566810 638383 := bstep (se 1 (by rfl) ⟨478787, by rfl⟩ : syracuseStep 638383 = 957575) B957575
theorem B2080289 : Blo 566810 2080289 := bstep (se 2 (by rfl) ⟨780108, by rfl⟩ : syracuseStep 2080289 = 1560217) B1560217
theorem B1916513 : Blo 566810 1916513 := bstep (se 2 (by rfl) ⟨718692, by rfl⟩ : syracuseStep 1916513 = 1437385) B1437385
theorem B606047 : Blo 566810 606047 := bstep (se 1 (by rfl) ⟨454535, by rfl⟩ : syracuseStep 606047 = 909071) B909071
theorem B638815 : Blo 566810 638815 := bstep (se 1 (by rfl) ⟨479111, by rfl⟩ : syracuseStep 638815 = 958223) B958223
theorem B1818551 : Blo 566810 1818551 := bstep (se 1 (by rfl) ⟨1363913, by rfl⟩ : syracuseStep 1818551 = 2727827) B2727827
theorem B4112441 : Blo 566810 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B639175 : Blo 566810 639175 := bstep (se 1 (by rfl) ⟨479381, by rfl⟩ : syracuseStep 639175 = 958763) B958763
theorem B606799 : Blo 566810 606799 := bstep (se 1 (by rfl) ⟨455099, by rfl⟩ : syracuseStep 606799 = 910199) B910199
theorem B1622891 : Blo 566810 1622891 := bstep (se 1 (by rfl) ⟨1217168, by rfl⟩ : syracuseStep 1622891 = 2434337) B2434337
theorem B1295291 : Blo 566810 1295291 := bstep (se 1 (by rfl) ⟨971468, by rfl⟩ : syracuseStep 1295291 = 1942937) B1942937
theorem B1917971 : Blo 566810 1917971 := bstep (se 1 (by rfl) ⟨1438478, by rfl⟩ : syracuseStep 1917971 = 2876957) B2876957
theorem B640039 : Blo 566810 640039 := bstep (se 1 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 640039 = 960059) B960059
theorem B1819705 : Blo 566810 1819705 := bstep (se 2 (by rfl) ⟨682389, by rfl⟩ : syracuseStep 1819705 = 1364779) B1364779
theorem B1918295 : Blo 566810 1918295 := bstep (se 1 (by rfl) ⟨1438721, by rfl⟩ : syracuseStep 1918295 = 2877443) B2877443
theorem B8210119 : Blo 566810 8210119 := bstep (se 1 (by rfl) ⟨6157589, by rfl⟩ : syracuseStep 8210119 = 12315179) B12315179
theorem B1624121 : Blo 566810 1624121 := bstep (se 2 (by rfl) ⟨609045, by rfl⟩ : syracuseStep 1624121 = 1218091) B1218091
theorem B1919375 : Blo 566810 1919375 := bstep (se 1 (by rfl) ⟨1439531, by rfl⟩ : syracuseStep 1919375 = 2879063) B2879063
theorem B1362395 : Blo 566810 1362395 := bstep (se 1 (by rfl) ⟨1021796, by rfl⟩ : syracuseStep 1362395 = 2043593) B2043593
theorem B1821217 : Blo 566810 1821217 := bstep (se 2 (by rfl) ⟨682956, by rfl⟩ : syracuseStep 1821217 = 1365913) B1365913
theorem B641659 : Blo 566810 641659 := bstep (se 1 (by rfl) ⟨481244, by rfl⟩ : syracuseStep 641659 = 962489) B962489
theorem B6933127 : Blo 566810 6933127 := bstep (se 1 (by rfl) ⟨5199845, by rfl⟩ : syracuseStep 6933127 = 10399691) B10399691
theorem B1919699 : Blo 566810 1919699 := bstep (se 1 (by rfl) ⟨1439774, by rfl⟩ : syracuseStep 1919699 = 2879549) B2879549
theorem B2050859 : Blo 566810 2050859 := bstep (se 1 (by rfl) ⟨1538144, by rfl⟩ : syracuseStep 2050859 = 3076289) B3076289
theorem B1952695 : Blo 566810 1952695 := bstep (se 1 (by rfl) ⟨1464521, by rfl⟩ : syracuseStep 1952695 = 2929043) B2929043
theorem B1821703 : Blo 566810 1821703 := bstep (se 1 (by rfl) ⟨1366277, by rfl⟩ : syracuseStep 1821703 = 2732555) B2732555
theorem B609319 : Blo 566810 609319 := bstep (se 1 (by rfl) ⟨456989, by rfl⟩ : syracuseStep 609319 = 913979) B913979
theorem B642127 : Blo 566810 642127 := bstep (se 1 (by rfl) ⟨481595, by rfl⟩ : syracuseStep 642127 = 963191) B963191
theorem B1822267 : Blo 566810 1822267 := bstep (se 1 (by rfl) ⟨1366700, by rfl⟩ : syracuseStep 1822267 = 2733401) B2733401
theorem B2051723 : Blo 566810 2051723 := bstep (se 1 (by rfl) ⟨1538792, by rfl⟩ : syracuseStep 2051723 = 3077585) B3077585
theorem B1363655 : Blo 566810 1363655 := bstep (se 1 (by rfl) ⟨1022741, by rfl⟩ : syracuseStep 1363655 = 2045483) B2045483
theorem B1920887 : Blo 566810 1920887 := bstep (se 1 (by rfl) ⟨1440665, by rfl⟩ : syracuseStep 1920887 = 2881331) B2881331
theorem B10899461 : Blo 566810 10899461 := bstep (se 4 (by rfl) ⟨1021824, by rfl⟩ : syracuseStep 10899461 = 2043649) B2043649
theorem B4673551 : Blo 566810 4673551 := bstep (se 1 (by rfl) ⟨3505163, by rfl⟩ : syracuseStep 4673551 = 7010327) B7010327
theorem B1921103 : Blo 566810 1921103 := bstep (se 1 (by rfl) ⟨1440827, by rfl⟩ : syracuseStep 1921103 = 2881655) B2881655
theorem B577615 : Blo 566810 577615 := bstep (se 1 (by rfl) ⟨433211, by rfl⟩ : syracuseStep 577615 = 866423) B866423
theorem B577631 : Blo 566810 577631 := bstep (se 1 (by rfl) ⟨433223, by rfl⟩ : syracuseStep 577631 = 866447) B866447
theorem B1921481 : Blo 566810 1921481 := bstep (se 2 (by rfl) ⟨720555, by rfl⟩ : syracuseStep 1921481 = 1441111) B1441111
theorem B2052647 : Blo 566810 2052647 := bstep (se 1 (by rfl) ⟨1539485, by rfl⟩ : syracuseStep 2052647 = 3078971) B3078971
theorem B4313735 : Blo 566810 4313735 := bstep (se 1 (by rfl) ⟨3235301, by rfl⟩ : syracuseStep 4313735 = 6470603) B6470603
theorem B1921751 : Blo 566810 1921751 := bstep (se 1 (by rfl) ⟨1441313, by rfl⟩ : syracuseStep 1921751 = 2882627) B2882627
theorem B1921967 : Blo 566810 1921967 := bstep (se 1 (by rfl) ⟨1441475, by rfl⟩ : syracuseStep 1921967 = 2882951) B2882951
theorem B4871339 : Blo 566810 4871339 := bstep (se 1 (by rfl) ⟨3653504, by rfl⟩ : syracuseStep 4871339 = 7307009) B7307009
theorem B1824061 : Blo 566810 1824061 := bstep (se 3 (by rfl) ⟨342011, by rfl⟩ : syracuseStep 1824061 = 684023) B684023
theorem B3888499 : Blo 566810 3888499 := bstep (se 1 (by rfl) ⟨2916374, by rfl⟩ : syracuseStep 3888499 = 5832749) B5832749
theorem B1725839 : Blo 566810 1725839 := bstep (se 1 (by rfl) ⟨1294379, by rfl⟩ : syracuseStep 1725839 = 2588759) B2588759
theorem B972175 : Blo 566810 972175 := bstep (se 1 (by rfl) ⟨729131, by rfl⟩ : syracuseStep 972175 = 1458263) B1458263
theorem B19715735 : Blo 566810 19715735 := bstep (se 1 (by rfl) ⟨14786801, by rfl⟩ : syracuseStep 19715735 = 29573603) B29573603
theorem B3233479 : Blo 566810 3233479 := bstep (se 1 (by rfl) ⟨2425109, by rfl⟩ : syracuseStep 3233479 = 4850219) B4850219
theorem B2741975 : Blo 566810 2741975 := bstep (se 1 (by rfl) ⟨2056481, by rfl⟩ : syracuseStep 2741975 = 4112963) B4112963
theorem B16897901 : Blo 566810 16897901 := bstep (se 3 (by rfl) ⟨3168356, by rfl⟩ : syracuseStep 16897901 = 6336713) B6336713
theorem B2185223 : Blo 566810 2185223 := bstep (se 1 (by rfl) ⟨1638917, by rfl⟩ : syracuseStep 2185223 = 3277835) B3277835
theorem B1169447 : Blo 566810 1169447 := bstep (se 1 (by rfl) ⟨877085, by rfl⟩ : syracuseStep 1169447 = 1754171) B1754171
theorem B12277817 : Blo 566810 12277817 := bstep (se 2 (by rfl) ⟨4604181, by rfl⟩ : syracuseStep 12277817 = 9208363) B9208363
theorem B4315193 : Blo 566810 4315193 := bstep (se 2 (by rfl) ⟨1618197, by rfl⟩ : syracuseStep 4315193 = 3236395) B3236395
theorem B13850681 : Blo 566810 13850681 := bstep (se 2 (by rfl) ⟨5194005, by rfl⟩ : syracuseStep 13850681 = 10388011) B10388011
theorem B2218063 : Blo 566810 2218063 := bstep (se 1 (by rfl) ⟨1663547, by rfl⟩ : syracuseStep 2218063 = 3327095) B3327095
theorem B2152601 : Blo 566810 2152601 := bstep (se 2 (by rfl) ⟨807225, by rfl⟩ : syracuseStep 2152601 = 1614451) B1614451
theorem B2742589 : Blo 566810 2742589 := bstep (se 3 (by rfl) ⟨514235, by rfl⟩ : syracuseStep 2742589 = 1028471) B1028471
theorem B1366625 : Blo 566810 1366625 := bstep (se 2 (by rfl) ⟨512484, by rfl⟩ : syracuseStep 1366625 = 1024969) B1024969
theorem B2874041 : Blo 566810 2874041 := bstep (se 2 (by rfl) ⟨1077765, by rfl⟩ : syracuseStep 2874041 = 2155531) B2155531
theorem B2153587 : Blo 566810 2153587 := bstep (se 1 (by rfl) ⟨1615190, by rfl⟩ : syracuseStep 2153587 = 3230381) B3230381
theorem B1924343 : Blo 566810 1924343 := bstep (se 1 (by rfl) ⟨1443257, by rfl⟩ : syracuseStep 1924343 = 2886515) B2886515
theorem B810415 : Blo 566810 810415 := bstep (se 1 (by rfl) ⟨607811, by rfl⟩ : syracuseStep 810415 = 1215623) B1215623
theorem B1924667 : Blo 566810 1924667 := bstep (se 1 (by rfl) ⟨1443500, by rfl⟩ : syracuseStep 1924667 = 2887001) B2887001
theorem B1924937 : Blo 566810 1924937 := bstep (se 2 (by rfl) ⟨721851, by rfl⟩ : syracuseStep 1924937 = 1443703) B1443703
theorem B24534859 : Blo 566810 24534859 := bstep (se 1 (by rfl) ⟨18401144, by rfl⟩ : syracuseStep 24534859 = 36802289) B36802289
theorem B2154347 : Blo 566810 2154347 := bstep (se 1 (by rfl) ⟨1615760, by rfl⟩ : syracuseStep 2154347 = 3231521) B3231521
theorem B4317137 : Blo 566810 4317137 := bstep (se 2 (by rfl) ⟨1618926, by rfl⟩ : syracuseStep 4317137 = 3237853) B3237853
theorem B6545585 : Blo 566810 6545585 := bstep (se 2 (by rfl) ⟨2454594, by rfl⟩ : syracuseStep 6545585 = 4909189) B4909189
theorem B1926071 : Blo 566810 1926071 := bstep (se 1 (by rfl) ⟨1444553, by rfl⟩ : syracuseStep 1926071 = 2889107) B2889107
theorem B582751 : Blo 566810 582751 := bstep (se 1 (by rfl) ⟨437063, by rfl⟩ : syracuseStep 582751 = 874127) B874127
theorem B648667 : Blo 566810 648667 := bstep (se 1 (by rfl) ⟨486500, by rfl⟩ : syracuseStep 648667 = 973001) B973001
theorem B8775179 : Blo 566810 8775179 := bstep (se 1 (by rfl) ⟨6581384, by rfl⟩ : syracuseStep 8775179 = 13162769) B13162769
theorem B1435259 : Blo 566810 1435259 := bstep (se 1 (by rfl) ⟨1076444, by rfl⟩ : syracuseStep 1435259 = 2152889) B2152889
theorem B1435553 : Blo 566810 1435553 := bstep (se 2 (by rfl) ⟨538332, by rfl⟩ : syracuseStep 1435553 = 1076665) B1076665
theorem B911531 : Blo 566810 911531 := bstep (se 1 (by rfl) ⟨683648, by rfl⟩ : syracuseStep 911531 = 1367297) B1367297
theorem B3467785 : Blo 566810 3467785 := bstep (se 2 (by rfl) ⟨1300419, by rfl⟩ : syracuseStep 3467785 = 2600839) B2600839
theorem B5172113 : Blo 566810 5172113 := bstep (se 2 (by rfl) ⟨1939542, by rfl⟩ : syracuseStep 5172113 = 3879085) B3879085
theorem B3239311 : Blo 566810 3239311 := bstep (se 1 (by rfl) ⟨2429483, by rfl⟩ : syracuseStep 3239311 = 4858967) B4858967
theorem B4845095 : Blo 566810 4845095 := bstep (se 1 (by rfl) ⟨3633821, by rfl⟩ : syracuseStep 4845095 = 7267643) B7267643
theorem B1437223 : Blo 566810 1437223 := bstep (se 1 (by rfl) ⟨1077917, by rfl⟩ : syracuseStep 1437223 = 2155835) B2155835
theorem B2158265 : Blo 566810 2158265 := bstep (se 2 (by rfl) ⟨809349, by rfl⟩ : syracuseStep 2158265 = 1618699) B1618699
theorem B2879225 : Blo 566810 2879225 := bstep (se 2 (by rfl) ⟨1079709, by rfl⟩ : syracuseStep 2879225 = 2159419) B2159419
theorem B10907459 : Blo 566810 10907459 := bstep (se 1 (by rfl) ⟨8180594, by rfl⟩ : syracuseStep 10907459 = 16361189) B16361189
theorem B1437547 : Blo 566810 1437547 := bstep (se 1 (by rfl) ⟨1078160, by rfl⟩ : syracuseStep 1437547 = 2156321) B2156321
theorem B1535851 : Blo 566810 1535851 := bstep (se 1 (by rfl) ⟨1151888, by rfl⟩ : syracuseStep 1535851 = 2303777) B2303777
theorem B6582349 : Blo 566810 6582349 := bstep (se 3 (by rfl) ⟨1234190, by rfl⟩ : syracuseStep 6582349 = 2468381) B2468381
theorem B1077371 : Blo 566810 1077371 := bstep (se 1 (by rfl) ⟨808028, by rfl⟩ : syracuseStep 1077371 = 1616057) B1616057
theorem B1077599 : Blo 566810 1077599 := bstep (se 1 (by rfl) ⟨808199, by rfl⟩ : syracuseStep 1077599 = 1616399) B1616399
theorem B2879873 : Blo 566810 2879873 := bstep (se 2 (by rfl) ⟨1079952, by rfl⟩ : syracuseStep 2879873 = 2159905) B2159905
theorem B1438195 : Blo 566810 1438195 := bstep (se 1 (by rfl) ⟨1078646, by rfl⟩ : syracuseStep 1438195 = 2157293) B2157293
theorem B913927 : Blo 566810 913927 := bstep (se 1 (by rfl) ⟨685445, by rfl⟩ : syracuseStep 913927 = 1370891) B1370891
theorem B1667609 : Blo 566810 1667609 := bstep (se 2 (by rfl) ⟨625353, by rfl⟩ : syracuseStep 1667609 = 1250707) B1250707
theorem B1077857 : Blo 566810 1077857 := bstep (se 2 (by rfl) ⟨404196, by rfl⟩ : syracuseStep 1077857 = 808393) B808393
theorem B6157073 : Blo 566810 6157073 := bstep (se 2 (by rfl) ⟨2308902, by rfl⟩ : syracuseStep 6157073 = 4617805) B4617805
theorem B1078123 : Blo 566810 1078123 := bstep (se 1 (by rfl) ⟨808592, by rfl⟩ : syracuseStep 1078123 = 1617185) B1617185
theorem B717751 : Blo 566810 717751 := bstep (se 1 (by rfl) ⟨538313, by rfl⟩ : syracuseStep 717751 = 1076627) B1076627
theorem B6911041 : Blo 566810 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B2585753 : Blo 566810 2585753 := bstep (se 2 (by rfl) ⟨969657, by rfl⟩ : syracuseStep 2585753 = 1939315) B1939315
theorem B2880683 : Blo 566810 2880683 := bstep (se 1 (by rfl) ⟨2160512, by rfl⟩ : syracuseStep 2880683 = 4321025) B4321025
theorem B1439329 : Blo 566810 1439329 := bstep (se 2 (by rfl) ⟨539748, by rfl⟩ : syracuseStep 1439329 = 1079497) B1079497
theorem B1275515 : Blo 566810 1275515 := bstep (se 1 (by rfl) ⟨956636, by rfl⟩ : syracuseStep 1275515 = 1913273) B1913273
theorem B2881169 : Blo 566810 2881169 := bstep (se 2 (by rfl) ⟨1080438, by rfl⟩ : syracuseStep 2881169 = 2160877) B2160877
theorem B16676533 : Blo 566810 16676533 := bstep (se 5 (by rfl) ⟨781712, by rfl⟩ : syracuseStep 16676533 = 1563425) B1563425
theorem B1275641 : Blo 566810 1275641 := bstep (se 2 (by rfl) ⟨478365, by rfl⟩ : syracuseStep 1275641 = 956731) B956731
theorem B2160377 : Blo 566810 2160377 := bstep (se 2 (by rfl) ⟨810141, by rfl⟩ : syracuseStep 2160377 = 1620283) B1620283
theorem B8222573 : Blo 566810 8222573 := bstep (se 3 (by rfl) ⟨1541732, by rfl⟩ : syracuseStep 8222573 = 3083465) B3083465
theorem B1275911 : Blo 566810 1275911 := bstep (se 1 (by rfl) ⟨956933, by rfl⟩ : syracuseStep 1275911 = 1913867) B1913867
theorem B1079315 : Blo 566810 1079315 := bstep (se 1 (by rfl) ⟨809486, by rfl⟩ : syracuseStep 1079315 = 1618973) B1618973
theorem B1275983 : Blo 566810 1275983 := bstep (se 1 (by rfl) ⟨956987, by rfl⟩ : syracuseStep 1275983 = 1913975) B1913975
theorem B719047 : Blo 566810 719047 := bstep (se 1 (by rfl) ⟨539285, by rfl⟩ : syracuseStep 719047 = 1078571) B1078571
theorem B1079543 : Blo 566810 1079543 := bstep (se 1 (by rfl) ⟨809657, by rfl⟩ : syracuseStep 1079543 = 1619315) B1619315
theorem B4094219 : Blo 566810 4094219 := bstep (se 1 (by rfl) ⟨3070664, by rfl⟩ : syracuseStep 4094219 = 6141329) B6141329
theorem B850271 : Blo 566810 850271 := bstep (se 1 (by rfl) ⟨637703, by rfl⟩ : syracuseStep 850271 = 1275407) B1275407
theorem B850283 : Blo 566810 850283 := bstep (se 1 (by rfl) ⟨637712, by rfl⟩ : syracuseStep 850283 = 1275425) B1275425
theorem B1276379 : Blo 566810 1276379 := bstep (se 1 (by rfl) ⟨957284, by rfl⟩ : syracuseStep 1276379 = 1914569) B1914569
theorem B1440281 : Blo 566810 1440281 := bstep (se 2 (by rfl) ⟨540105, by rfl⟩ : syracuseStep 1440281 = 1080211) B1080211
theorem B850511 : Blo 566810 850511 := bstep (se 1 (by rfl) ⟨637883, by rfl⟩ : syracuseStep 850511 = 1275767) B1275767
theorem B850631 : Blo 566810 850631 := bstep (se 1 (by rfl) ⟨637973, by rfl⟩ : syracuseStep 850631 = 1275947) B1275947
theorem B2161363 : Blo 566810 2161363 := bstep (se 1 (by rfl) ⟨1621022, by rfl⟩ : syracuseStep 2161363 = 3242045) B3242045
theorem B850793 : Blo 566810 850793 := bstep (se 2 (by rfl) ⟨319047, by rfl⟩ : syracuseStep 850793 = 638095) B638095
theorem B1276847 : Blo 566810 1276847 := bstep (se 1 (by rfl) ⟨957635, by rfl⟩ : syracuseStep 1276847 = 1915271) B1915271
theorem B850871 : Blo 566810 850871 := bstep (se 1 (by rfl) ⟨638153, by rfl⟩ : syracuseStep 850871 = 1276307) B1276307
theorem B850907 : Blo 566810 850907 := bstep (se 1 (by rfl) ⟨638180, by rfl⟩ : syracuseStep 850907 = 1276361) B1276361
theorem B1211411 : Blo 566810 1211411 := bstep (se 1 (by rfl) ⟨908558, by rfl⟩ : syracuseStep 1211411 = 1817117) B1817117
theorem B1440787 : Blo 566810 1440787 := bstep (se 1 (by rfl) ⟨1080590, by rfl⟩ : syracuseStep 1440787 = 2161181) B2161181
theorem B1277099 : Blo 566810 1277099 := bstep (se 1 (by rfl) ⟨957824, by rfl⟩ : syracuseStep 1277099 = 1915649) B1915649
theorem B2161835 : Blo 566810 2161835 := bstep (se 1 (by rfl) ⟨1621376, by rfl⟩ : syracuseStep 2161835 = 3242753) B3242753
theorem B1211753 : Blo 566810 1211753 := bstep (se 2 (by rfl) ⟨454407, by rfl⟩ : syracuseStep 1211753 = 908815) B908815
theorem B851375 : Blo 566810 851375 := bstep (se 1 (by rfl) ⟨638531, by rfl⟩ : syracuseStep 851375 = 1277063) B1277063
theorem B851465 : Blo 566810 851465 := bstep (se 2 (by rfl) ⟨319299, by rfl⟩ : syracuseStep 851465 = 638599) B638599
theorem B851495 : Blo 566810 851495 := bstep (se 1 (by rfl) ⟨638621, by rfl⟩ : syracuseStep 851495 = 1277243) B1277243
theorem B851579 : Blo 566810 851579 := bstep (se 1 (by rfl) ⟨638684, by rfl⟩ : syracuseStep 851579 = 1277369) B1277369
theorem B1080955 : Blo 566810 1080955 := bstep (se 1 (by rfl) ⟨810716, by rfl⟩ : syracuseStep 1080955 = 1621433) B1621433
theorem B1277639 : Blo 566810 1277639 := bstep (se 1 (by rfl) ⟨958229, by rfl⟩ : syracuseStep 1277639 = 1916459) B1916459
theorem B851705 : Blo 566810 851705 := bstep (se 2 (by rfl) ⟨319389, by rfl⟩ : syracuseStep 851705 = 638779) B638779
theorem B851807 : Blo 566810 851807 := bstep (se 1 (by rfl) ⟨638855, by rfl⟩ : syracuseStep 851807 = 1277711) B1277711
theorem B1081183 : Blo 566810 1081183 := bstep (se 1 (by rfl) ⟨810887, by rfl⟩ : syracuseStep 1081183 = 1621775) B1621775
theorem B851819 : Blo 566810 851819 := bstep (se 1 (by rfl) ⟨638864, by rfl⟩ : syracuseStep 851819 = 1277729) B1277729
theorem B2883437 : Blo 566810 2883437 := bstep (se 3 (by rfl) ⟨540644, by rfl⟩ : syracuseStep 2883437 = 1081289) B1081289
theorem B1441921 : Blo 566810 1441921 := bstep (se 2 (by rfl) ⟨540720, by rfl⟩ : syracuseStep 1441921 = 1081441) B1081441
theorem B1540349 : Blo 566810 1540349 := bstep (se 3 (by rfl) ⟨288815, by rfl⟩ : syracuseStep 1540349 = 577631) B577631
theorem B852233 : Blo 566810 852233 := bstep (se 2 (by rfl) ⟨319587, by rfl⟩ : syracuseStep 852233 = 639175) B639175
theorem B852335 : Blo 566810 852335 := bstep (se 1 (by rfl) ⟨639251, by rfl⟩ : syracuseStep 852335 = 1278503) B1278503
theorem B1638983 : Blo 566810 1638983 := bstep (se 1 (by rfl) ⟨1229237, by rfl⟩ : syracuseStep 1638983 = 2458475) B2458475
theorem B852551 : Blo 566810 852551 := bstep (se 1 (by rfl) ⟨639413, by rfl⟩ : syracuseStep 852551 = 1278827) B1278827
theorem B1081927 : Blo 566810 1081927 := bstep (se 1 (by rfl) ⟨811445, by rfl⟩ : syracuseStep 1081927 = 1622891) B1622891
theorem B852587 : Blo 566810 852587 := bstep (se 1 (by rfl) ⟨639440, by rfl⟩ : syracuseStep 852587 = 1278881) B1278881
theorem B1278647 : Blo 566810 1278647 := bstep (se 1 (by rfl) ⟨958985, by rfl⟩ : syracuseStep 1278647 = 1917971) B1917971
theorem B852815 : Blo 566810 852815 := bstep (se 1 (by rfl) ⟨639611, by rfl⟩ : syracuseStep 852815 = 1279223) B1279223
theorem B1278863 : Blo 566810 1278863 := bstep (se 1 (by rfl) ⟨959147, by rfl⟩ : syracuseStep 1278863 = 1918295) B1918295
theorem B3244961 : Blo 566810 3244961 := bstep (se 2 (by rfl) ⟨1216860, by rfl⟩ : syracuseStep 3244961 = 2433721) B2433721
theorem B1442731 : Blo 566810 1442731 := bstep (se 1 (by rfl) ⟨1082048, by rfl⟩ : syracuseStep 1442731 = 2164097) B2164097
theorem B2884571 : Blo 566810 2884571 := bstep (se 1 (by rfl) ⟨2163428, by rfl⟩ : syracuseStep 2884571 = 4326857) B4326857
theorem B2884733 : Blo 566810 2884733 := bstep (se 3 (by rfl) ⟨540887, by rfl⟩ : syracuseStep 2884733 = 1081775) B1081775
theorem B853211 : Blo 566810 853211 := bstep (se 1 (by rfl) ⟨639908, by rfl⟩ : syracuseStep 853211 = 1279817) B1279817
theorem B1443035 : Blo 566810 1443035 := bstep (se 1 (by rfl) ⟨1082276, by rfl⟩ : syracuseStep 1443035 = 2164553) B2164553
theorem B3114233 : Blo 566810 3114233 := bstep (se 2 (by rfl) ⟨1167837, by rfl⟩ : syracuseStep 3114233 = 2335675) B2335675
theorem B1443167 : Blo 566810 1443167 := bstep (se 1 (by rfl) ⟨1082375, by rfl⟩ : syracuseStep 1443167 = 2164751) B2164751
theorem B722287 : Blo 566810 722287 := bstep (se 1 (by rfl) ⟨541715, by rfl⟩ : syracuseStep 722287 = 1083431) B1083431
theorem B1082747 : Blo 566810 1082747 := bstep (se 1 (by rfl) ⟨812060, by rfl⟩ : syracuseStep 1082747 = 1624121) B1624121
theorem B853385 : Blo 566810 853385 := bstep (se 2 (by rfl) ⟨320019, by rfl⟩ : syracuseStep 853385 = 640039) B640039
theorem B2426273 : Blo 566810 2426273 := bstep (se 2 (by rfl) ⟨909852, by rfl⟩ : syracuseStep 2426273 = 1819705) B1819705
theorem B2885057 : Blo 566810 2885057 := bstep (se 2 (by rfl) ⟨1081896, by rfl⟩ : syracuseStep 2885057 = 2163793) B2163793
theorem B2426375 : Blo 566810 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B1279583 : Blo 566810 1279583 := bstep (se 1 (by rfl) ⟨959687, by rfl⟩ : syracuseStep 1279583 = 1919375) B1919375
theorem B853739 : Blo 566810 853739 := bstep (se 1 (by rfl) ⟨640304, by rfl⟩ : syracuseStep 853739 = 1280609) B1280609
theorem B1279799 : Blo 566810 1279799 := bstep (se 1 (by rfl) ⟨959849, by rfl⟩ : syracuseStep 1279799 = 1919699) B1919699
theorem B853967 : Blo 566810 853967 := bstep (se 1 (by rfl) ⟨640475, by rfl⟩ : syracuseStep 853967 = 1280951) B1280951
theorem B1443865 : Blo 566810 1443865 := bstep (se 2 (by rfl) ⟨541449, by rfl⟩ : syracuseStep 1443865 = 1082899) B1082899
theorem B1280105 : Blo 566810 1280105 := bstep (se 2 (by rfl) ⟨480039, by rfl⟩ : syracuseStep 1280105 = 960079) B960079
theorem B10946825 : Blo 566810 10946825 := bstep (se 2 (by rfl) ⟨4105059, by rfl⟩ : syracuseStep 10946825 = 8210119) B8210119
theorem B1444169 : Blo 566810 1444169 := bstep (se 2 (by rfl) ⟨541563, by rfl⟩ : syracuseStep 1444169 = 1083127) B1083127
theorem B854363 : Blo 566810 854363 := bstep (se 1 (by rfl) ⟨640772, by rfl⟩ : syracuseStep 854363 = 1281545) B1281545
theorem B788935 : Blo 566810 788935 := bstep (se 1 (by rfl) ⟨591701, by rfl⟩ : syracuseStep 788935 = 1183403) B1183403
theorem B1182203 : Blo 566810 1182203 := bstep (se 1 (by rfl) ⟨886652, by rfl⟩ : syracuseStep 1182203 = 1773305) B1773305
theorem B854591 : Blo 566810 854591 := bstep (se 1 (by rfl) ⟨640943, by rfl⟩ : syracuseStep 854591 = 1281887) B1281887
theorem B1280591 : Blo 566810 1280591 := bstep (se 1 (by rfl) ⟨960443, by rfl⟩ : syracuseStep 1280591 = 1920887) B1920887
theorem B854711 : Blo 566810 854711 := bstep (se 1 (by rfl) ⟨641033, by rfl⟩ : syracuseStep 854711 = 1282067) B1282067
theorem B1280735 : Blo 566810 1280735 := bstep (se 1 (by rfl) ⟨960551, by rfl⟩ : syracuseStep 1280735 = 1921103) B1921103
theorem B854939 : Blo 566810 854939 := bstep (se 1 (by rfl) ⟨641204, by rfl⟩ : syracuseStep 854939 = 1282409) B1282409
theorem B1280987 : Blo 566810 1280987 := bstep (se 1 (by rfl) ⟨960740, by rfl⟩ : syracuseStep 1280987 = 1921481) B1921481
theorem B4852817 : Blo 566810 4852817 := bstep (se 2 (by rfl) ⟨1819806, by rfl⟩ : syracuseStep 4852817 = 3639613) B3639613
theorem B1281167 : Blo 566810 1281167 := bstep (se 1 (by rfl) ⟨960875, by rfl⟩ : syracuseStep 1281167 = 1921751) B1921751
theorem B1281257 : Blo 566810 1281257 := bstep (se 2 (by rfl) ⟨480471, by rfl⟩ : syracuseStep 1281257 = 960943) B960943
theorem B1281311 : Blo 566810 1281311 := bstep (se 1 (by rfl) ⟨960983, by rfl⟩ : syracuseStep 1281311 = 1921967) B1921967
theorem B855335 : Blo 566810 855335 := bstep (se 1 (by rfl) ⟨641501, by rfl⟩ : syracuseStep 855335 = 1283003) B1283003
theorem B4328801 : Blo 566810 4328801 := bstep (se 2 (by rfl) ⟨1623300, by rfl⟩ : syracuseStep 4328801 = 3246601) B3246601
theorem B4623713 : Blo 566810 4623713 := bstep (se 2 (by rfl) ⟨1733892, by rfl⟩ : syracuseStep 4623713 = 3467785) B3467785
theorem B855419 : Blo 566810 855419 := bstep (se 1 (by rfl) ⟨641564, by rfl⟩ : syracuseStep 855419 = 1283129) B1283129
theorem B2428289 : Blo 566810 2428289 := bstep (se 2 (by rfl) ⟨910608, by rfl⟩ : syracuseStep 2428289 = 1821217) B1821217
theorem B3247559 : Blo 566810 3247559 := bstep (se 1 (by rfl) ⟨2435669, by rfl⟩ : syracuseStep 3247559 = 4871339) B4871339
theorem B855545 : Blo 566810 855545 := bstep (se 2 (by rfl) ⟨320829, by rfl⟩ : syracuseStep 855545 = 641659) B641659
theorem B9244169 : Blo 566810 9244169 := bstep (se 2 (by rfl) ⟨3466563, by rfl⟩ : syracuseStep 9244169 = 6933127) B6933127
theorem B1150559 : Blo 566810 1150559 := bstep (se 1 (by rfl) ⟨862919, by rfl⟩ : syracuseStep 1150559 = 1725839) B1725839
theorem B855647 : Blo 566810 855647 := bstep (se 1 (by rfl) ⟨641735, by rfl⟩ : syracuseStep 855647 = 1283471) B1283471
theorem B1281833 : Blo 566810 1281833 := bstep (se 2 (by rfl) ⟨480687, by rfl⟩ : syracuseStep 1281833 = 961375) B961375
theorem B855863 : Blo 566810 855863 := bstep (se 1 (by rfl) ⟨641897, by rfl⟩ : syracuseStep 855863 = 1283795) B1283795
theorem B2428937 : Blo 566810 2428937 := bstep (se 2 (by rfl) ⟨910851, by rfl⟩ : syracuseStep 2428937 = 1821703) B1821703
theorem B856169 : Blo 566810 856169 := bstep (se 2 (by rfl) ⟨321063, by rfl⟩ : syracuseStep 856169 = 642127) B642127
theorem B4919453 : Blo 566810 4919453 := bstep (se 3 (by rfl) ⟨922397, by rfl⟩ : syracuseStep 4919453 = 1844795) B1844795
theorem B3085003 : Blo 566810 3085003 := bstep (se 1 (by rfl) ⟨2313752, by rfl⟩ : syracuseStep 3085003 = 4627505) B4627505
theorem B2429689 : Blo 566810 2429689 := bstep (se 2 (by rfl) ⟨911133, by rfl⟩ : syracuseStep 2429689 = 1822267) B1822267
theorem B1282895 : Blo 566810 1282895 := bstep (se 1 (by rfl) ⟨962171, by rfl⟩ : syracuseStep 1282895 = 1924343) B1924343
theorem B21926861 : Blo 566810 21926861 := bstep (se 3 (by rfl) ⟨4111286, by rfl⟩ : syracuseStep 21926861 = 8222573) B8222573
theorem B45061069 : Blo 566810 45061069 := bstep (se 3 (by rfl) ⟨8448950, by rfl⟩ : syracuseStep 45061069 = 16897901) B16897901
theorem B1283111 : Blo 566810 1283111 := bstep (se 1 (by rfl) ⟨962333, by rfl⟩ : syracuseStep 1283111 = 1924667) B1924667
theorem B1283291 : Blo 566810 1283291 := bstep (se 1 (by rfl) ⟨962468, by rfl⟩ : syracuseStep 1283291 = 1924937) B1924937
theorem B4330745 : Blo 566810 4330745 := bstep (se 2 (by rfl) ⟨1624029, by rfl⟩ : syracuseStep 4330745 = 3248059) B3248059
theorem B6231401 : Blo 566810 6231401 := bstep (se 2 (by rfl) ⟨2336775, by rfl⟩ : syracuseStep 6231401 = 4673551) B4673551
theorem B1283489 : Blo 566810 1283489 := bstep (se 2 (by rfl) ⟨481308, by rfl⟩ : syracuseStep 1283489 = 962617) B962617
theorem B4363723 : Blo 566810 4363723 := bstep (se 1 (by rfl) ⟨3272792, by rfl⟩ : syracuseStep 4363723 = 6545585) B6545585
theorem B36935149 : Blo 566810 36935149 := bstep (se 3 (by rfl) ⟨6925340, by rfl⟩ : syracuseStep 36935149 = 13850681) B13850681
theorem B2430749 : Blo 566810 2430749 := bstep (se 3 (by rfl) ⟨455765, by rfl⟩ : syracuseStep 2430749 = 911531) B911531
theorem B1284047 : Blo 566810 1284047 := bstep (se 1 (by rfl) ⟨963035, by rfl⟩ : syracuseStep 1284047 = 1926071) B1926071
theorem B1218569 : Blo 566810 1218569 := bstep (se 2 (by rfl) ⟨456963, by rfl⟩ : syracuseStep 1218569 = 913927) B913927
theorem B956839 : Blo 566810 956839 := bstep (se 1 (by rfl) ⟨717629, by rfl⟩ : syracuseStep 956839 = 1435259) B1435259
theorem B957001 : Blo 566810 957001 := bstep (se 2 (by rfl) ⟨358875, by rfl⟩ : syracuseStep 957001 = 717751) B717751
theorem B2595401 : Blo 566810 2595401 := bstep (se 2 (by rfl) ⟨973275, by rfl⟩ : syracuseStep 2595401 = 1946551) B1946551
theorem B957035 : Blo 566810 957035 := bstep (se 1 (by rfl) ⟨717776, by rfl⟩ : syracuseStep 957035 = 1435553) B1435553
theorem B2300663 : Blo 566810 2300663 := bstep (se 1 (by rfl) ⟨1725497, by rfl⟩ : syracuseStep 2300663 = 3450995) B3450995
theorem B9214721 : Blo 566810 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B2300827 : Blo 566810 2300827 := bstep (se 1 (by rfl) ⟨1725620, by rfl⟩ : syracuseStep 2300827 = 3451241) B3451241
theorem B2432081 : Blo 566810 2432081 := bstep (se 2 (by rfl) ⟨912030, by rfl⟩ : syracuseStep 2432081 = 1824061) B1824061
theorem B4922491 : Blo 566810 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B5184665 : Blo 566810 5184665 := bstep (se 2 (by rfl) ⟨1944249, by rfl⟩ : syracuseStep 5184665 = 3888499) B3888499
theorem B5905979 : Blo 566810 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B7806779 : Blo 566810 7806779 := bstep (se 1 (by rfl) ⟨5855084, by rfl⟩ : syracuseStep 7806779 = 11710169) B11710169
theorem B2957417 : Blo 566810 2957417 := bstep (se 2 (by rfl) ⟨1109031, by rfl⟩ : syracuseStep 2957417 = 2218063) B2218063
theorem B958729 : Blo 566810 958729 := bstep (se 2 (by rfl) ⟨359523, by rfl⟩ : syracuseStep 958729 = 719047) B719047
theorem B4104715 : Blo 566810 4104715 := bstep (se 1 (by rfl) ⟨3078536, by rfl⟩ : syracuseStep 4104715 = 6157073) B6157073
theorem B88941509 : Blo 566810 88941509 := bstep (se 4 (by rfl) ⟨8338266, by rfl⟩ : syracuseStep 88941509 = 16676533) B16676533
theorem B1025257 : Blo 566810 1025257 := bstep (se 2 (by rfl) ⟨384471, by rfl⟩ : syracuseStep 1025257 = 768943) B768943
theorem B5547437 : Blo 566810 5547437 := bstep (se 3 (by rfl) ⟨1040144, by rfl⟩ : syracuseStep 5547437 = 2080289) B2080289
theorem B2729479 : Blo 566810 2729479 := bstep (se 1 (by rfl) ⟨2047109, by rfl⟩ : syracuseStep 2729479 = 4094219) B4094219
theorem B566847 : Blo 566810 566847 := bstep (se 1 (by rfl) ⟨425135, by rfl⟩ : syracuseStep 566847 = 850271) B850271
theorem B566855 : Blo 566810 566855 := bstep (se 1 (by rfl) ⟨425141, by rfl⟩ : syracuseStep 566855 = 850283) B850283
theorem B960187 : Blo 566810 960187 := bstep (se 1 (by rfl) ⟨720140, by rfl⟩ : syracuseStep 960187 = 1440281) B1440281
theorem B567007 : Blo 566810 567007 := bstep (se 1 (by rfl) ⟨425255, by rfl⟩ : syracuseStep 567007 = 850511) B850511
theorem B567087 : Blo 566810 567087 := bstep (se 1 (by rfl) ⟨425315, by rfl⟩ : syracuseStep 567087 = 850631) B850631
theorem B567195 : Blo 566810 567195 := bstep (se 1 (by rfl) ⟨425396, by rfl⟩ : syracuseStep 567195 = 850793) B850793
theorem B731035 : Blo 566810 731035 := bstep (se 1 (by rfl) ⟨548276, by rfl⟩ : syracuseStep 731035 = 1096553) B1096553
theorem B567247 : Blo 566810 567247 := bstep (se 1 (by rfl) ⟨425435, by rfl⟩ : syracuseStep 567247 = 850871) B850871
theorem B567271 : Blo 566810 567271 := bstep (se 1 (by rfl) ⟨425453, by rfl⟩ : syracuseStep 567271 = 850907) B850907
theorem B1616125 : Blo 566810 1616125 := bstep (se 3 (by rfl) ⟨303023, by rfl⟩ : syracuseStep 1616125 = 606047) B606047
theorem B567583 : Blo 566810 567583 := bstep (se 1 (by rfl) ⟨425687, by rfl⟩ : syracuseStep 567583 = 851375) B851375
theorem B567643 : Blo 566810 567643 := bstep (se 1 (by rfl) ⟨425732, by rfl⟩ : syracuseStep 567643 = 851465) B851465
theorem B567663 : Blo 566810 567663 := bstep (se 1 (by rfl) ⟨425747, by rfl⟩ : syracuseStep 567663 = 851495) B851495
theorem B567719 : Blo 566810 567719 := bstep (se 1 (by rfl) ⟨425789, by rfl⟩ : syracuseStep 567719 = 851579) B851579
theorem B32713145 : Blo 566810 32713145 := bstep (se 2 (by rfl) ⟨12267429, by rfl⟩ : syracuseStep 32713145 = 24534859) B24534859
theorem B567803 : Blo 566810 567803 := bstep (se 1 (by rfl) ⟨425852, by rfl⟩ : syracuseStep 567803 = 851705) B851705
theorem B567871 : Blo 566810 567871 := bstep (se 1 (by rfl) ⟨425903, by rfl⟩ : syracuseStep 567871 = 851807) B851807
theorem B567879 : Blo 566810 567879 := bstep (se 1 (by rfl) ⟨425909, by rfl⟩ : syracuseStep 567879 = 851819) B851819
theorem B568031 : Blo 566810 568031 := bstep (se 1 (by rfl) ⟨426023, by rfl⟩ : syracuseStep 568031 = 852047) B852047
theorem B961247 : Blo 566810 961247 := bstep (se 1 (by rfl) ⟨720935, by rfl⟩ : syracuseStep 961247 = 1441871) B1441871
theorem B568111 : Blo 566810 568111 := bstep (se 1 (by rfl) ⟨426083, by rfl⟩ : syracuseStep 568111 = 852167) B852167
theorem B568219 : Blo 566810 568219 := bstep (se 1 (by rfl) ⟨426164, by rfl⟩ : syracuseStep 568219 = 852329) B852329
theorem B568271 : Blo 566810 568271 := bstep (se 1 (by rfl) ⟨426203, by rfl⟩ : syracuseStep 568271 = 852407) B852407
theorem B568295 : Blo 566810 568295 := bstep (se 1 (by rfl) ⟨426221, by rfl⟩ : syracuseStep 568295 = 852443) B852443
theorem B35105861 : Blo 566810 35105861 := bstep (se 4 (by rfl) ⟨3291174, by rfl⟩ : syracuseStep 35105861 = 6582349) B6582349
theorem B961679 : Blo 566810 961679 := bstep (se 1 (by rfl) ⟨721259, by rfl⟩ : syracuseStep 961679 = 1442519) B1442519
theorem B568607 : Blo 566810 568607 := bstep (se 1 (by rfl) ⟨426455, by rfl⟩ : syracuseStep 568607 = 852911) B852911
theorem B568667 : Blo 566810 568667 := bstep (se 1 (by rfl) ⟨426500, by rfl⟩ : syracuseStep 568667 = 853001) B853001
theorem B568687 : Blo 566810 568687 := bstep (se 1 (by rfl) ⟨426515, by rfl⟩ : syracuseStep 568687 = 853031) B853031
theorem B961915 : Blo 566810 961915 := bstep (se 1 (by rfl) ⟨721436, by rfl⟩ : syracuseStep 961915 = 1442873) B1442873
theorem B568743 : Blo 566810 568743 := bstep (se 1 (by rfl) ⟨426557, by rfl⟩ : syracuseStep 568743 = 853115) B853115
theorem B1617367 : Blo 566810 1617367 := bstep (se 1 (by rfl) ⟨1213025, by rfl⟩ : syracuseStep 1617367 = 2426051) B2426051
theorem B1617401 : Blo 566810 1617401 := bstep (se 2 (by rfl) ⟨606525, by rfl⟩ : syracuseStep 1617401 = 1213051) B1213051
theorem B568827 : Blo 566810 568827 := bstep (se 1 (by rfl) ⟨426620, by rfl⟩ : syracuseStep 568827 = 853241) B853241
theorem B2600507 : Blo 566810 2600507 := bstep (se 1 (by rfl) ⟨1950380, by rfl⟩ : syracuseStep 2600507 = 3900761) B3900761
theorem B568895 : Blo 566810 568895 := bstep (se 1 (by rfl) ⟨426671, by rfl⟩ : syracuseStep 568895 = 853343) B853343
theorem B568903 : Blo 566810 568903 := bstep (se 1 (by rfl) ⟨426677, by rfl⟩ : syracuseStep 568903 = 853355) B853355
theorem B569055 : Blo 566810 569055 := bstep (se 1 (by rfl) ⟨426791, by rfl⟩ : syracuseStep 569055 = 853583) B853583
theorem B569135 : Blo 566810 569135 := bstep (se 1 (by rfl) ⟨426851, by rfl⟩ : syracuseStep 569135 = 853703) B853703
theorem B569243 : Blo 566810 569243 := bstep (se 1 (by rfl) ⟨426932, by rfl⟩ : syracuseStep 569243 = 853865) B853865
theorem B569295 : Blo 566810 569295 := bstep (se 1 (by rfl) ⟨426971, by rfl⟩ : syracuseStep 569295 = 853943) B853943
theorem B569319 : Blo 566810 569319 := bstep (se 1 (by rfl) ⟨426989, by rfl⟩ : syracuseStep 569319 = 853979) B853979
theorem B569631 : Blo 566810 569631 := bstep (se 1 (by rfl) ⟨427223, by rfl⟩ : syracuseStep 569631 = 854447) B854447
theorem B569691 : Blo 566810 569691 := bstep (se 1 (by rfl) ⟨427268, by rfl⟩ : syracuseStep 569691 = 854537) B854537
theorem B569711 : Blo 566810 569711 := bstep (se 1 (by rfl) ⟨427283, by rfl⟩ : syracuseStep 569711 = 854567) B854567
theorem B569767 : Blo 566810 569767 := bstep (se 1 (by rfl) ⟨427325, by rfl⟩ : syracuseStep 569767 = 854651) B854651
theorem B3649967 : Blo 566810 3649967 := bstep (se 1 (by rfl) ⟨2737475, by rfl⟩ : syracuseStep 3649967 = 5474951) B5474951
theorem B17740241 : Blo 566810 17740241 := bstep (se 2 (by rfl) ⟨6652590, by rfl⟩ : syracuseStep 17740241 = 13305181) B13305181
theorem B569851 : Blo 566810 569851 := bstep (se 1 (by rfl) ⟨427388, by rfl⟩ : syracuseStep 569851 = 854777) B854777
theorem B569919 : Blo 566810 569919 := bstep (se 1 (by rfl) ⟨427439, by rfl⟩ : syracuseStep 569919 = 854879) B854879
theorem B569927 : Blo 566810 569927 := bstep (se 1 (by rfl) ⟨427445, by rfl⟩ : syracuseStep 569927 = 854891) B854891
theorem B570079 : Blo 566810 570079 := bstep (se 1 (by rfl) ⟨427559, by rfl⟩ : syracuseStep 570079 = 855119) B855119
theorem B570159 : Blo 566810 570159 := bstep (se 1 (by rfl) ⟨427619, by rfl⟩ : syracuseStep 570159 = 855239) B855239
theorem B570267 : Blo 566810 570267 := bstep (se 1 (by rfl) ⟨427700, by rfl⟩ : syracuseStep 570267 = 855401) B855401
theorem B570319 : Blo 566810 570319 := bstep (se 1 (by rfl) ⟨427739, by rfl⟩ : syracuseStep 570319 = 855479) B855479
theorem B570343 : Blo 566810 570343 := bstep (se 1 (by rfl) ⟨427757, by rfl⟩ : syracuseStep 570343 = 855515) B855515
theorem B1619041 : Blo 566810 1619041 := bstep (se 2 (by rfl) ⟨607140, by rfl⟩ : syracuseStep 1619041 = 1214281) B1214281
theorem B5485715 : Blo 566810 5485715 := bstep (se 1 (by rfl) ⟨4114286, by rfl⟩ : syracuseStep 5485715 = 8228573) B8228573
theorem B3454109 : Blo 566810 3454109 := bstep (se 3 (by rfl) ⟨647645, by rfl⟩ : syracuseStep 3454109 = 1295291) B1295291
theorem B570655 : Blo 566810 570655 := bstep (se 1 (by rfl) ⟨427991, by rfl⟩ : syracuseStep 570655 = 855983) B855983
theorem B570715 : Blo 566810 570715 := bstep (se 1 (by rfl) ⟨428036, by rfl⟩ : syracuseStep 570715 = 856073) B856073
theorem B570735 : Blo 566810 570735 := bstep (se 1 (by rfl) ⟨428051, by rfl⟩ : syracuseStep 570735 = 856103) B856103
theorem B570791 : Blo 566810 570791 := bstep (se 1 (by rfl) ⟨428093, by rfl⟩ : syracuseStep 570791 = 856187) B856187
theorem B767791 : Blo 566810 767791 := bstep (se 1 (by rfl) ⟨575843, by rfl⟩ : syracuseStep 767791 = 1151687) B1151687
theorem B2734631 : Blo 566810 2734631 := bstep (se 1 (by rfl) ⟨2050973, by rfl⟩ : syracuseStep 2734631 = 4101947) B4101947
theorem B2603593 : Blo 566810 2603593 := bstep (se 2 (by rfl) ⟨976347, by rfl⟩ : syracuseStep 2603593 = 1952695) B1952695
theorem B16628365 : Blo 566810 16628365 := bstep (se 3 (by rfl) ⟨3117818, by rfl⟩ : syracuseStep 16628365 = 6235637) B6235637
theorem B637663 : Blo 566810 637663 := bstep (se 1 (by rfl) ⟨478247, by rfl⟩ : syracuseStep 637663 = 956495) B956495
theorem B52575293 : Blo 566810 52575293 := bstep (se 3 (by rfl) ⟨9857867, by rfl⟩ : syracuseStep 52575293 = 19715735) B19715735
theorem B1916027 : Blo 566810 1916027 := bstep (se 1 (by rfl) ⟨1437020, by rfl⟩ : syracuseStep 1916027 = 2874041) B2874041
theorem B638239 : Blo 566810 638239 := bstep (se 1 (by rfl) ⟨478679, by rfl⟩ : syracuseStep 638239 = 957359) B957359
theorem B1916297 : Blo 566810 1916297 := bstep (se 2 (by rfl) ⟨718611, by rfl⟩ : syracuseStep 1916297 = 1437223) B1437223
theorem B638527 : Blo 566810 638527 := bstep (se 1 (by rfl) ⟨478895, by rfl⟩ : syracuseStep 638527 = 957791) B957791
theorem B4111955 : Blo 566810 4111955 := bstep (se 1 (by rfl) ⟨3083966, by rfl⟩ : syracuseStep 4111955 = 6167933) B6167933
theorem B1916729 : Blo 566810 1916729 := bstep (se 2 (by rfl) ⟨718773, by rfl⟩ : syracuseStep 1916729 = 1437547) B1437547
theorem B1621889 : Blo 566810 1621889 := bstep (se 2 (by rfl) ⟨608208, by rfl⟩ : syracuseStep 1621889 = 1216417) B1216417
theorem B770153 : Blo 566810 770153 := bstep (se 2 (by rfl) ⟨288807, by rfl⟩ : syracuseStep 770153 = 577615) B577615
theorem B639355 : Blo 566810 639355 := bstep (se 1 (by rfl) ⟨479516, by rfl⟩ : syracuseStep 639355 = 959033) B959033
theorem B1917593 : Blo 566810 1917593 := bstep (se 2 (by rfl) ⟨719097, by rfl⟩ : syracuseStep 1917593 = 1438195) B1438195
theorem B3064655 : Blo 566810 3064655 := bstep (se 1 (by rfl) ⟨2298491, by rfl⟩ : syracuseStep 3064655 = 4596983) B4596983
theorem B639823 : Blo 566810 639823 := bstep (se 1 (by rfl) ⟨479867, by rfl⟩ : syracuseStep 639823 = 959735) B959735
theorem B2737091 : Blo 566810 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B3654659 : Blo 566810 3654659 := bstep (se 1 (by rfl) ⟨2740994, by rfl⟩ : syracuseStep 3654659 = 5481989) B5481989
theorem B5850119 : Blo 566810 5850119 := bstep (se 1 (by rfl) ⟨4387589, by rfl⟩ : syracuseStep 5850119 = 8775179) B8775179
theorem B1819847 : Blo 566810 1819847 := bstep (se 1 (by rfl) ⟨1364885, by rfl⟩ : syracuseStep 1819847 = 2729771) B2729771
theorem B640219 : Blo 566810 640219 := bstep (se 1 (by rfl) ⟨480164, by rfl⟩ : syracuseStep 640219 = 960329) B960329
theorem B4375795 : Blo 566810 4375795 := bstep (se 1 (by rfl) ⟨3281846, by rfl⟩ : syracuseStep 4375795 = 6563693) B6563693
theorem B640507 : Blo 566810 640507 := bstep (se 1 (by rfl) ⟨480380, by rfl⟩ : syracuseStep 640507 = 960761) B960761
theorem B640687 : Blo 566810 640687 := bstep (se 1 (by rfl) ⟨480515, by rfl⟩ : syracuseStep 640687 = 961031) B961031
theorem B1296233 : Blo 566810 1296233 := bstep (se 2 (by rfl) ⟨486087, by rfl⟩ : syracuseStep 1296233 = 972175) B972175
theorem B640975 : Blo 566810 640975 := bstep (se 1 (by rfl) ⟨480731, by rfl⟩ : syracuseStep 640975 = 961463) B961463
theorem B1919105 : Blo 566810 1919105 := bstep (se 2 (by rfl) ⟨719664, by rfl⟩ : syracuseStep 1919105 = 1439329) B1439329
theorem B4311305 : Blo 566810 4311305 := bstep (se 2 (by rfl) ⟨1616739, by rfl⟩ : syracuseStep 4311305 = 3233479) B3233479
theorem B641371 : Blo 566810 641371 := bstep (se 1 (by rfl) ⟨481028, by rfl⟩ : syracuseStep 641371 = 962057) B962057
theorem B3230063 : Blo 566810 3230063 := bstep (se 1 (by rfl) ⟨2422547, by rfl⟩ : syracuseStep 3230063 = 4845095) B4845095
theorem B1296751 : Blo 566810 1296751 := bstep (se 1 (by rfl) ⟨972563, by rfl⟩ : syracuseStep 1296751 = 1945127) B1945127
theorem B1296815 : Blo 566810 1296815 := bstep (se 1 (by rfl) ⟨972611, by rfl⟩ : syracuseStep 1296815 = 1945223) B1945223
theorem B641479 : Blo 566810 641479 := bstep (se 1 (by rfl) ⟨481109, by rfl⟩ : syracuseStep 641479 = 962219) B962219
theorem B1624531 : Blo 566810 1624531 := bstep (se 1 (by rfl) ⟨1218398, by rfl⟩ : syracuseStep 1624531 = 2436797) B2436797
theorem B3459557 : Blo 566810 3459557 := bstep (se 4 (by rfl) ⟨324333, by rfl⟩ : syracuseStep 3459557 = 648667) B648667
theorem B1821179 : Blo 566810 1821179 := bstep (se 1 (by rfl) ⟨1365884, by rfl⟩ : syracuseStep 1821179 = 2731769) B2731769
theorem B1919483 : Blo 566810 1919483 := bstep (se 1 (by rfl) ⟨1439612, by rfl⟩ : syracuseStep 1919483 = 2879225) B2879225
theorem B641839 : Blo 566810 641839 := bstep (se 1 (by rfl) ⟨481379, by rfl⟩ : syracuseStep 641839 = 962759) B962759
theorem B641947 : Blo 566810 641947 := bstep (se 1 (by rfl) ⟨481460, by rfl⟩ : syracuseStep 641947 = 962921) B962921
theorem B1919915 : Blo 566810 1919915 := bstep (se 1 (by rfl) ⟨1439936, by rfl⟩ : syracuseStep 1919915 = 2879873) B2879873
theorem B3656785 : Blo 566810 3656785 := bstep (se 2 (by rfl) ⟨1371294, by rfl⟩ : syracuseStep 3656785 = 2742589) B2742589
theorem B1723835 : Blo 566810 1723835 := bstep (se 1 (by rfl) ⟨1292876, by rfl⟩ : syracuseStep 1723835 = 2585753) B2585753
theorem B1920455 : Blo 566810 1920455 := bstep (se 1 (by rfl) ⟨1440341, by rfl⟩ : syracuseStep 1920455 = 2880683) B2880683
theorem B1920779 : Blo 566810 1920779 := bstep (se 1 (by rfl) ⟨1440584, by rfl⟩ : syracuseStep 1920779 = 2881169) B2881169
theorem B10342187 : Blo 566810 10342187 := bstep (se 1 (by rfl) ⟨7756640, by rfl⟩ : syracuseStep 10342187 = 15513281) B15513281
theorem B1363817 : Blo 566810 1363817 := bstep (se 2 (by rfl) ⟨511431, by rfl⟩ : syracuseStep 1363817 = 1022863) B1022863
theorem B2740243 : Blo 566810 2740243 := bstep (se 1 (by rfl) ⟨2055182, by rfl⟩ : syracuseStep 2740243 = 4110365) B4110365
theorem B1921049 : Blo 566810 1921049 := bstep (se 2 (by rfl) ⟨720393, by rfl⟩ : syracuseStep 1921049 = 1440787) B1440787
theorem B2871449 : Blo 566810 2871449 := bstep (se 2 (by rfl) ⟨1076793, by rfl⟩ : syracuseStep 2871449 = 2153587) B2153587
theorem B10408601 : Blo 566810 10408601 := bstep (se 2 (by rfl) ⟨3903225, by rfl⟩ : syracuseStep 10408601 = 7806451) B7806451
theorem B807607 : Blo 566810 807607 := bstep (se 1 (by rfl) ⟨605705, by rfl⟩ : syracuseStep 807607 = 1211411) B1211411
theorem B1364663 : Blo 566810 1364663 := bstep (se 1 (by rfl) ⟨1023497, by rfl⟩ : syracuseStep 1364663 = 2046995) B2046995
theorem B807835 : Blo 566810 807835 := bstep (se 1 (by rfl) ⟨605876, by rfl⟩ : syracuseStep 807835 = 1211753) B1211753
theorem B578459 : Blo 566810 578459 := bstep (se 1 (by rfl) ⟨433844, by rfl⟩ : syracuseStep 578459 = 867689) B867689
theorem B2872259 : Blo 566810 2872259 := bstep (se 1 (by rfl) ⟨2154194, by rfl⟩ : syracuseStep 2872259 = 4308389) B4308389
theorem B1922291 : Blo 566810 1922291 := bstep (se 1 (by rfl) ⟨1441718, by rfl⟩ : syracuseStep 1922291 = 2883437) B2883437
theorem B1922399 : Blo 566810 1922399 := bstep (se 1 (by rfl) ⟨1441799, by rfl⟩ : syracuseStep 1922399 = 2883599) B2883599
theorem B2741627 : Blo 566810 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B12474101 : Blo 566810 12474101 := bstep (se 5 (by rfl) ⟨584723, by rfl⟩ : syracuseStep 12474101 = 1169447) B1169447
theorem B809065 : Blo 566810 809065 := bstep (se 2 (by rfl) ⟨303399, by rfl⟩ : syracuseStep 809065 = 606799) B606799
theorem B5200139 : Blo 566810 5200139 := bstep (se 1 (by rfl) ⟨3900104, by rfl⟩ : syracuseStep 5200139 = 7800209) B7800209
theorem B777001 : Blo 566810 777001 := bstep (se 2 (by rfl) ⟨291375, by rfl⟩ : syracuseStep 777001 = 582751) B582751
theorem B1923965 : Blo 566810 1923965 := bstep (se 3 (by rfl) ⟨360743, by rfl⟩ : syracuseStep 1923965 = 721487) B721487
theorem B908263 : Blo 566810 908263 := bstep (se 1 (by rfl) ⟨681197, by rfl⟩ : syracuseStep 908263 = 1362395) B1362395
theorem B44194895 : Blo 566810 44194895 := bstep (se 1 (by rfl) ⟨33146171, by rfl⟩ : syracuseStep 44194895 = 66292343) B66292343
theorem B1924235 : Blo 566810 1924235 := bstep (se 1 (by rfl) ⟨1443176, by rfl⟩ : syracuseStep 1924235 = 2886353) B2886353
theorem B1367815 : Blo 566810 1367815 := bstep (se 1 (by rfl) ⟨1025861, by rfl⟩ : syracuseStep 1367815 = 2051723) B2051723
theorem B13852457 : Blo 566810 13852457 := bstep (se 2 (by rfl) ⟨5194671, by rfl⟩ : syracuseStep 13852457 = 10389343) B10389343
theorem B7266307 : Blo 566810 7266307 := bstep (se 1 (by rfl) ⟨5449730, by rfl⟩ : syracuseStep 7266307 = 10899461) B10899461
theorem B1368431 : Blo 566810 1368431 := bstep (se 1 (by rfl) ⟨1026323, by rfl⟩ : syracuseStep 1368431 = 2052647) B2052647
theorem B2875823 : Blo 566810 2875823 := bstep (se 1 (by rfl) ⟨2156867, by rfl⟩ : syracuseStep 2875823 = 4313735) B4313735
theorem B1925855 : Blo 566810 1925855 := bstep (se 1 (by rfl) ⟨1444391, by rfl⟩ : syracuseStep 1925855 = 2888783) B2888783
theorem B1827983 : Blo 566810 1827983 := bstep (se 1 (by rfl) ⟨1370987, by rfl⟩ : syracuseStep 1827983 = 2741975) B2741975
theorem B1926287 : Blo 566810 1926287 := bstep (se 1 (by rfl) ⟨1444715, by rfl⟩ : syracuseStep 1926287 = 2889431) B2889431
theorem B8185211 : Blo 566810 8185211 := bstep (se 1 (by rfl) ⟨6138908, by rfl⟩ : syracuseStep 8185211 = 12277817) B12277817
theorem B2876795 : Blo 566810 2876795 := bstep (se 1 (by rfl) ⟨2157596, by rfl⟩ : syracuseStep 2876795 = 4315193) B4315193
theorem B812425 : Blo 566810 812425 := bstep (se 2 (by rfl) ⟨304659, by rfl⟩ : syracuseStep 812425 = 609319) B609319
theorem B5465495 : Blo 566810 5465495 := bstep (se 1 (by rfl) ⟨4099121, by rfl⟩ : syracuseStep 5465495 = 8198243) B8198243
theorem B1435067 : Blo 566810 1435067 := bstep (se 1 (by rfl) ⟨1076300, by rfl⟩ : syracuseStep 1435067 = 2152601) B2152601
theorem B911083 : Blo 566810 911083 := bstep (se 1 (by rfl) ⟨683312, by rfl⟩ : syracuseStep 911083 = 1366625) B1366625
theorem B4319081 : Blo 566810 4319081 := bstep (se 2 (by rfl) ⟨1619655, by rfl⟩ : syracuseStep 4319081 = 3239311) B3239311
theorem B1436231 : Blo 566810 1436231 := bstep (se 1 (by rfl) ⟨1077173, by rfl⟩ : syracuseStep 1436231 = 2154347) B2154347
theorem B2878091 : Blo 566810 2878091 := bstep (se 1 (by rfl) ⟨2158568, by rfl⟩ : syracuseStep 2878091 = 4317137) B4317137
theorem B5827261 : Blo 566810 5827261 := bstep (se 3 (by rfl) ⟨1092611, by rfl⟩ : syracuseStep 5827261 = 2185223) B2185223
theorem B568519397 : Blo 566810 568519397 := bstep (se 4 (by rfl) ⟨53298693, by rfl⟩ : syracuseStep 568519397 = 106597387) B106597387
theorem B2157961 : Blo 566810 2157961 := bstep (se 2 (by rfl) ⟨809235, by rfl⟩ : syracuseStep 2157961 = 1618471) B1618471
theorem B3632849 : Blo 566810 3632849 := bstep (se 2 (by rfl) ⟨1362318, by rfl⟩ : syracuseStep 3632849 = 2724637) B2724637
theorem B1437497 : Blo 566810 1437497 := bstep (se 2 (by rfl) ⟨539061, by rfl⟩ : syracuseStep 1437497 = 1078123) B1078123
theorem B3239837 : Blo 566810 3239837 := bstep (se 3 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 3239837 = 1214939) B1214939
theorem B3109211 : Blo 566810 3109211 := bstep (se 1 (by rfl) ⟨2331908, by rfl⟩ : syracuseStep 3109211 = 4663817) B4663817
theorem B684379 : Blo 566810 684379 := bstep (se 1 (by rfl) ⟨513284, by rfl⟩ : syracuseStep 684379 = 1026569) B1026569
theorem B5468957 : Blo 566810 5468957 := bstep (se 3 (by rfl) ⟨1025429, by rfl⟩ : syracuseStep 5468957 = 2050859) B2050859
theorem B13792301 : Blo 566810 13792301 := bstep (se 3 (by rfl) ⟨2586056, by rfl⟩ : syracuseStep 13792301 = 5172113) B5172113
theorem B1438843 : Blo 566810 1438843 := bstep (se 1 (by rfl) ⟨1079132, by rfl⟩ : syracuseStep 1438843 = 2158265) B2158265
theorem B7271639 : Blo 566810 7271639 := bstep (se 1 (by rfl) ⟨5453729, by rfl⟩ : syracuseStep 7271639 = 10907459) B10907459
theorem B718247 : Blo 566810 718247 := bstep (se 1 (by rfl) ⟨538685, by rfl⟩ : syracuseStep 718247 = 1077371) B1077371
theorem B1275335 : Blo 566810 1275335 := bstep (se 1 (by rfl) ⟨956501, by rfl⟩ : syracuseStep 1275335 = 1913003) B1913003
theorem B718399 : Blo 566810 718399 := bstep (se 1 (by rfl) ⟨538799, by rfl⟩ : syracuseStep 718399 = 1077599) B1077599
theorem B1111739 : Blo 566810 1111739 := bstep (se 1 (by rfl) ⟨833804, by rfl⟩ : syracuseStep 1111739 = 1667609) B1667609
theorem B718571 : Blo 566810 718571 := bstep (se 1 (by rfl) ⟨538928, by rfl⟩ : syracuseStep 718571 = 1077857) B1077857
theorem B1275695 : Blo 566810 1275695 := bstep (se 1 (by rfl) ⟨956771, by rfl⟩ : syracuseStep 1275695 = 1913543) B1913543
theorem B1079095 : Blo 566810 1079095 := bstep (se 1 (by rfl) ⟨809321, by rfl⟩ : syracuseStep 1079095 = 1618643) B1618643
theorem B76904549 : Blo 566810 76904549 := bstep (se 4 (by rfl) ⟨7209801, by rfl⟩ : syracuseStep 76904549 = 14419603) B14419603
theorem B2881817 : Blo 566810 2881817 := bstep (se 2 (by rfl) ⟨1080681, by rfl⟩ : syracuseStep 2881817 = 2161363) B2161363
theorem B1276271 : Blo 566810 1276271 := bstep (se 1 (by rfl) ⟨957203, by rfl⟩ : syracuseStep 1276271 = 1914407) B1914407
theorem B850343 : Blo 566810 850343 := bstep (se 1 (by rfl) ⟨637757, by rfl⟩ : syracuseStep 850343 = 1275515) B1275515
theorem B1276343 : Blo 566810 1276343 := bstep (se 1 (by rfl) ⟨957257, by rfl⟩ : syracuseStep 1276343 = 1914515) B1914515
theorem B850427 : Blo 566810 850427 := bstep (se 1 (by rfl) ⟨637820, by rfl⟩ : syracuseStep 850427 = 1275641) B1275641
theorem B1440251 : Blo 566810 1440251 := bstep (se 1 (by rfl) ⟨1080188, by rfl⟩ : syracuseStep 1440251 = 2160377) B2160377
theorem B1276487 : Blo 566810 1276487 := bstep (se 1 (by rfl) ⟨957365, by rfl⟩ : syracuseStep 1276487 = 1914731) B1914731
theorem B1276523 : Blo 566810 1276523 := bstep (se 1 (by rfl) ⟨957392, by rfl⟩ : syracuseStep 1276523 = 1914785) B1914785
theorem B850553 : Blo 566810 850553 := bstep (se 2 (by rfl) ⟨318957, by rfl⟩ : syracuseStep 850553 = 637915) B637915
theorem B850607 : Blo 566810 850607 := bstep (se 1 (by rfl) ⟨637955, by rfl⟩ : syracuseStep 850607 = 1275911) B1275911
theorem B1079983 : Blo 566810 1079983 := bstep (se 1 (by rfl) ⟨809987, by rfl⟩ : syracuseStep 1079983 = 1619975) B1619975
theorem B719543 : Blo 566810 719543 := bstep (se 1 (by rfl) ⟨539657, by rfl⟩ : syracuseStep 719543 = 1079315) B1079315
theorem B850655 : Blo 566810 850655 := bstep (se 1 (by rfl) ⟨637991, by rfl⟩ : syracuseStep 850655 = 1275983) B1275983
theorem B719695 : Blo 566810 719695 := bstep (se 1 (by rfl) ⟨539771, by rfl⟩ : syracuseStep 719695 = 1079543) B1079543
theorem B1211291 : Blo 566810 1211291 := bstep (se 1 (by rfl) ⟨908468, by rfl⟩ : syracuseStep 1211291 = 1816937) B1816937
theorem B850919 : Blo 566810 850919 := bstep (se 1 (by rfl) ⟨638189, by rfl⟩ : syracuseStep 850919 = 1276379) B1276379
theorem B1276919 : Blo 566810 1276919 := bstep (se 1 (by rfl) ⟨957689, by rfl⟩ : syracuseStep 1276919 = 1915379) B1915379
theorem B5176349 : Blo 566810 5176349 := bstep (se 3 (by rfl) ⟨970565, by rfl⟩ : syracuseStep 5176349 = 1941131) B1941131
theorem B3636413 : Blo 566810 3636413 := bstep (se 3 (by rfl) ⟨681827, by rfl⟩ : syracuseStep 3636413 = 1363655) B1363655
theorem B1211591 : Blo 566810 1211591 := bstep (se 1 (by rfl) ⟨908693, by rfl⟩ : syracuseStep 1211591 = 1817387) B1817387
theorem B8191205 : Blo 566810 8191205 := bstep (se 4 (by rfl) ⟨767925, by rfl⟩ : syracuseStep 8191205 = 1535851) B1535851
theorem B851177 : Blo 566810 851177 := bstep (se 2 (by rfl) ⟨319191, by rfl⟩ : syracuseStep 851177 = 638383) B638383
theorem B1080553 : Blo 566810 1080553 := bstep (se 2 (by rfl) ⟨405207, by rfl⟩ : syracuseStep 1080553 = 810415) B810415
theorem B851231 : Blo 566810 851231 := bstep (se 1 (by rfl) ⟨638423, by rfl⟩ : syracuseStep 851231 = 1276847) B1276847
theorem B1277279 : Blo 566810 1277279 := bstep (se 1 (by rfl) ⟨957959, by rfl⟩ : syracuseStep 1277279 = 1915919) B1915919
theorem B851399 : Blo 566810 851399 := bstep (se 1 (by rfl) ⟨638549, by rfl⟩ : syracuseStep 851399 = 1277099) B1277099
theorem B1441223 : Blo 566810 1441223 := bstep (se 1 (by rfl) ⟨1080917, by rfl⟩ : syracuseStep 1441223 = 2161835) B2161835
theorem B1441273 : Blo 566810 1441273 := bstep (se 2 (by rfl) ⟨540477, by rfl⟩ : syracuseStep 1441273 = 1080955) B1080955
theorem B1277675 : Blo 566810 1277675 := bstep (se 1 (by rfl) ⟨958256, by rfl⟩ : syracuseStep 1277675 = 1916513) B1916513
theorem B851753 : Blo 566810 851753 := bstep (se 2 (by rfl) ⟨319407, by rfl⟩ : syracuseStep 851753 = 638815) B638815
theorem B1441577 : Blo 566810 1441577 := bstep (se 2 (by rfl) ⟨540591, by rfl⟩ : syracuseStep 1441577 = 1081183) B1081183
theorem B851759 : Blo 566810 851759 := bstep (se 1 (by rfl) ⟨638819, by rfl⟩ : syracuseStep 851759 = 1277639) B1277639
theorem B4849469 : Blo 566810 4849469 := bstep (se 3 (by rfl) ⟨909275, by rfl⟩ : syracuseStep 4849469 = 1818551) B1818551
theorem B1277801 : Blo 566810 1277801 := bstep (se 2 (by rfl) ⟨479175, by rfl⟩ : syracuseStep 1277801 = 958351) B958351
theorem B1278305 : Blo 566810 1278305 := bstep (se 2 (by rfl) ⟨479364, by rfl⟩ : syracuseStep 1278305 = 958729) B958729
theorem B1278395 : Blo 566810 1278395 := bstep (se 1 (by rfl) ⟨958796, by rfl⟩ : syracuseStep 1278395 = 1917593) B1917593
theorem B852431 : Blo 566810 852431 := bstep (se 1 (by rfl) ⟨639323, by rfl⟩ : syracuseStep 852431 = 1278647) B1278647
theorem B852473 : Blo 566810 852473 := bstep (se 2 (by rfl) ⟨319677, by rfl⟩ : syracuseStep 852473 = 639355) B639355
theorem B852575 : Blo 566810 852575 := bstep (se 1 (by rfl) ⟨639431, by rfl⟩ : syracuseStep 852575 = 1278863) B1278863
theorem B2163307 : Blo 566810 2163307 := bstep (se 1 (by rfl) ⟨1622480, by rfl⟩ : syracuseStep 2163307 = 3244961) B3244961
theorem B3900079 : Blo 566810 3900079 := bstep (se 1 (by rfl) ⟨2925059, by rfl⟩ : syracuseStep 3900079 = 5850119) B5850119
theorem B5472953 : Blo 566810 5472953 := bstep (se 2 (by rfl) ⟨2052357, by rfl⟩ : syracuseStep 5472953 = 4104715) B4104715
theorem B1442569 : Blo 566810 1442569 := bstep (se 2 (by rfl) ⟨540963, by rfl⟩ : syracuseStep 1442569 = 1081927) B1081927
theorem B1213231 : Blo 566810 1213231 := bstep (se 1 (by rfl) ⟨909923, by rfl⟩ : syracuseStep 1213231 = 1819847) B1819847
theorem B853055 : Blo 566810 853055 := bstep (se 1 (by rfl) ⟨639791, by rfl⟩ : syracuseStep 853055 = 1279583) B1279583
theorem B853097 : Blo 566810 853097 := bstep (se 2 (by rfl) ⟨319911, by rfl⟩ : syracuseStep 853097 = 639823) B639823
theorem B853199 : Blo 566810 853199 := bstep (se 1 (by rfl) ⟨639899, by rfl⟩ : syracuseStep 853199 = 1279799) B1279799
theorem B853403 : Blo 566810 853403 := bstep (se 1 (by rfl) ⟨640052, by rfl⟩ : syracuseStep 853403 = 1280105) B1280105
theorem B1279403 : Blo 566810 1279403 := bstep (se 1 (by rfl) ⟨959552, by rfl⟩ : syracuseStep 1279403 = 1919105) B1919105
theorem B853625 : Blo 566810 853625 := bstep (se 2 (by rfl) ⟨320109, by rfl⟩ : syracuseStep 853625 = 640219) B640219
theorem B5834393 : Blo 566810 5834393 := bstep (se 2 (by rfl) ⟨2187897, by rfl⟩ : syracuseStep 5834393 = 4375795) B4375795
theorem B788135 : Blo 566810 788135 := bstep (se 1 (by rfl) ⟨591101, by rfl⟩ : syracuseStep 788135 = 1182203) B1182203
theorem B1214119 : Blo 566810 1214119 := bstep (se 1 (by rfl) ⟨910589, by rfl⟩ : syracuseStep 1214119 = 1821179) B1821179
theorem B1279655 : Blo 566810 1279655 := bstep (se 1 (by rfl) ⟨959741, by rfl⟩ : syracuseStep 1279655 = 1919483) B1919483
theorem B853727 : Blo 566810 853727 := bstep (se 1 (by rfl) ⟨640295, by rfl⟩ : syracuseStep 853727 = 1280591) B1280591
theorem B853823 : Blo 566810 853823 := bstep (se 1 (by rfl) ⟨640367, by rfl⟩ : syracuseStep 853823 = 1280735) B1280735
theorem B1083233 : Blo 566810 1083233 := bstep (se 2 (by rfl) ⟨406212, by rfl⟩ : syracuseStep 1083233 = 812425) B812425
theorem B1279943 : Blo 566810 1279943 := bstep (se 1 (by rfl) ⟨959957, by rfl⟩ : syracuseStep 1279943 = 1919915) B1919915
theorem B853991 : Blo 566810 853991 := bstep (se 1 (by rfl) ⟨640493, by rfl⟩ : syracuseStep 853991 = 1280987) B1280987
theorem B854009 : Blo 566810 854009 := bstep (se 2 (by rfl) ⟨320253, by rfl⟩ : syracuseStep 854009 = 640507) B640507
theorem B3639305 : Blo 566810 3639305 := bstep (se 2 (by rfl) ⟨1364739, by rfl⟩ : syracuseStep 3639305 = 2729479) B2729479
theorem B854111 : Blo 566810 854111 := bstep (se 1 (by rfl) ⟨640583, by rfl⟩ : syracuseStep 854111 = 1281167) B1281167
theorem B854171 : Blo 566810 854171 := bstep (se 1 (by rfl) ⟨640628, by rfl⟩ : syracuseStep 854171 = 1281257) B1281257
theorem B854207 : Blo 566810 854207 := bstep (se 1 (by rfl) ⟨640655, by rfl⟩ : syracuseStep 854207 = 1281311) B1281311
theorem B854249 : Blo 566810 854249 := bstep (se 2 (by rfl) ⟨320343, by rfl⟩ : syracuseStep 854249 = 640687) B640687
theorem B2885867 : Blo 566810 2885867 := bstep (se 1 (by rfl) ⟨2164400, by rfl⟩ : syracuseStep 2885867 = 4328801) B4328801
theorem B3082475 : Blo 566810 3082475 := bstep (se 1 (by rfl) ⟨2311856, by rfl⟩ : syracuseStep 3082475 = 4623713) B4623713
theorem B1280249 : Blo 566810 1280249 := bstep (se 2 (by rfl) ⟨480093, by rfl⟩ : syracuseStep 1280249 = 960187) B960187
theorem B1149223 : Blo 566810 1149223 := bstep (se 1 (by rfl) ⟨861917, by rfl⟩ : syracuseStep 1149223 = 1723835) B1723835
theorem B1280303 : Blo 566810 1280303 := bstep (se 1 (by rfl) ⟨960227, by rfl⟩ : syracuseStep 1280303 = 1920455) B1920455
theorem B2165039 : Blo 566810 2165039 := bstep (se 1 (by rfl) ⟨1623779, by rfl⟩ : syracuseStep 2165039 = 3247559) B3247559
theorem B1214777 : Blo 566810 1214777 := bstep (se 2 (by rfl) ⟨455541, by rfl⟩ : syracuseStep 1214777 = 911083) B911083
theorem B6162779 : Blo 566810 6162779 := bstep (se 1 (by rfl) ⟨4622084, by rfl⟩ : syracuseStep 6162779 = 9244169) B9244169
theorem B1542557 : Blo 566810 1542557 := bstep (se 3 (by rfl) ⟨289229, by rfl⟩ : syracuseStep 1542557 = 578459) B578459
theorem B1280519 : Blo 566810 1280519 := bstep (se 1 (by rfl) ⟨960389, by rfl⟩ : syracuseStep 1280519 = 1920779) B1920779
theorem B854555 : Blo 566810 854555 := bstep (se 1 (by rfl) ⟨640916, by rfl⟩ : syracuseStep 854555 = 1281833) B1281833
theorem B854633 : Blo 566810 854633 := bstep (se 2 (by rfl) ⟨320487, by rfl⟩ : syracuseStep 854633 = 640975) B640975
theorem B1280699 : Blo 566810 1280699 := bstep (se 1 (by rfl) ⟨960524, by rfl⟩ : syracuseStep 1280699 = 1921049) B1921049
theorem B3279635 : Blo 566810 3279635 := bstep (se 1 (by rfl) ⟨2459726, by rfl⟩ : syracuseStep 3279635 = 4919453) B4919453
theorem B855161 : Blo 566810 855161 := bstep (se 2 (by rfl) ⟨320685, by rfl⟩ : syracuseStep 855161 = 641371) B641371
theorem B855263 : Blo 566810 855263 := bstep (se 1 (by rfl) ⟨641447, by rfl⟩ : syracuseStep 855263 = 1282895) B1282895
theorem B1051913 : Blo 566810 1051913 := bstep (se 2 (by rfl) ⟨394467, by rfl⟩ : syracuseStep 1051913 = 788935) B788935
theorem B855305 : Blo 566810 855305 := bstep (se 2 (by rfl) ⟨320739, by rfl⟩ : syracuseStep 855305 = 641479) B641479
theorem B2166041 : Blo 566810 2166041 := bstep (se 2 (by rfl) ⟨812265, by rfl⟩ : syracuseStep 2166041 = 1624531) B1624531
theorem B14617907 : Blo 566810 14617907 := bstep (se 1 (by rfl) ⟨10963430, by rfl⟩ : syracuseStep 14617907 = 21926861) B21926861
theorem B855407 : Blo 566810 855407 := bstep (se 1 (by rfl) ⟨641555, by rfl⟩ : syracuseStep 855407 = 1283111) B1283111
theorem B855527 : Blo 566810 855527 := bstep (se 1 (by rfl) ⟨641645, by rfl⟩ : syracuseStep 855527 = 1283291) B1283291
theorem B1281527 : Blo 566810 1281527 := bstep (se 1 (by rfl) ⟨961145, by rfl⟩ : syracuseStep 1281527 = 1922291) B1922291
theorem B2887163 : Blo 566810 2887163 := bstep (se 1 (by rfl) ⟨2165372, by rfl⟩ : syracuseStep 2887163 = 4330745) B4330745
theorem B1281599 : Blo 566810 1281599 := bstep (se 1 (by rfl) ⟨961199, by rfl⟩ : syracuseStep 1281599 = 1922399) B1922399
theorem B7769681 : Blo 566810 7769681 := bstep (se 2 (by rfl) ⟨2913630, by rfl⟩ : syracuseStep 7769681 = 5827261) B5827261
theorem B855659 : Blo 566810 855659 := bstep (se 1 (by rfl) ⟨641744, by rfl⟩ : syracuseStep 855659 = 1283489) B1283489
theorem B2887325 : Blo 566810 2887325 := bstep (se 3 (by rfl) ⟨541373, by rfl⟩ : syracuseStep 2887325 = 1082747) B1082747
theorem B7311005 : Blo 566810 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B855785 : Blo 566810 855785 := bstep (se 2 (by rfl) ⟨320919, by rfl⟩ : syracuseStep 855785 = 641839) B641839
theorem B855929 : Blo 566810 855929 := bstep (se 2 (by rfl) ⟨320973, by rfl⟩ : syracuseStep 855929 = 641947) B641947
theorem B856031 : Blo 566810 856031 := bstep (se 1 (by rfl) ⟨642023, by rfl⟩ : syracuseStep 856031 = 1284047) B1284047
theorem B13832693 : Blo 566810 13832693 := bstep (se 5 (by rfl) ⟨648407, by rfl⟩ : syracuseStep 13832693 = 1296815) B1296815
theorem B1282553 : Blo 566810 1282553 := bstep (se 2 (by rfl) ⟨480957, by rfl⟩ : syracuseStep 1282553 = 961915) B961915
theorem B1282643 : Blo 566810 1282643 := bstep (se 1 (by rfl) ⟨961982, by rfl⟩ : syracuseStep 1282643 = 1923965) B1923965
theorem B29463263 : Blo 566810 29463263 := bstep (se 1 (by rfl) ⟨22097447, by rfl⟩ : syracuseStep 29463263 = 44194895) B44194895
theorem B1282823 : Blo 566810 1282823 := bstep (se 1 (by rfl) ⟨962117, by rfl⟩ : syracuseStep 1282823 = 1924235) B1924235
theorem B3937319 : Blo 566810 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B3249517 : Blo 566810 3249517 := bstep (se 3 (by rfl) ⟨609284, by rfl⟩ : syracuseStep 3249517 = 1218569) B1218569
theorem B1971611 : Blo 566810 1971611 := bstep (se 1 (by rfl) ⟨1478708, by rfl⟩ : syracuseStep 1971611 = 2957417) B2957417
theorem B1283903 : Blo 566810 1283903 := bstep (se 1 (by rfl) ⟨962927, by rfl⟩ : syracuseStep 1283903 = 1925855) B1925855
theorem B13867037 : Blo 566810 13867037 := bstep (se 3 (by rfl) ⟨2600069, by rfl⟩ : syracuseStep 13867037 = 5200139) B5200139
theorem B1218655 : Blo 566810 1218655 := bstep (se 1 (by rfl) ⟨913991, by rfl⟩ : syracuseStep 1218655 = 1827983) B1827983
theorem B1284191 : Blo 566810 1284191 := bstep (se 1 (by rfl) ⟨963143, by rfl⟩ : syracuseStep 1284191 = 1926287) B1926287
theorem B3643663 : Blo 566810 3643663 := bstep (se 1 (by rfl) ⟨2732747, by rfl⟩ : syracuseStep 3643663 = 5465495) B5465495
theorem B956711 : Blo 566810 956711 := bstep (se 1 (by rfl) ⟨717533, by rfl⟩ : syracuseStep 956711 = 1435067) B1435067
theorem B957487 : Blo 566810 957487 := bstep (se 1 (by rfl) ⟨718115, by rfl⟩ : syracuseStep 957487 = 1436231) B1436231
theorem B6135101 : Blo 566810 6135101 := bstep (se 3 (by rfl) ⟨1150331, by rfl⟩ : syracuseStep 6135101 = 2300663) B2300663
theorem B23403907 : Blo 566810 23403907 := bstep (se 1 (by rfl) ⟨17552930, by rfl⟩ : syracuseStep 23403907 = 35105861) B35105861
theorem B957865 : Blo 566810 957865 := bstep (se 2 (by rfl) ⟨359199, by rfl⟩ : syracuseStep 957865 = 718399) B718399
theorem B23273189 : Blo 566810 23273189 := bstep (se 4 (by rfl) ⟨2181861, by rfl⟩ : syracuseStep 23273189 = 4363723) B4363723
theorem B1023721 : Blo 566810 1023721 := bstep (se 2 (by rfl) ⟨383895, by rfl⟩ : syracuseStep 1023721 = 767791) B767791
theorem B958331 : Blo 566810 958331 := bstep (se 1 (by rfl) ⟨718748, by rfl⟩ : syracuseStep 958331 = 1437497) B1437497
theorem B2072807 : Blo 566810 2072807 := bstep (se 1 (by rfl) ⟨1554605, by rfl⟩ : syracuseStep 2072807 = 3109211) B3109211
theorem B2433311 : Blo 566810 2433311 := bstep (se 1 (by rfl) ⟨1824983, by rfl⟩ : syracuseStep 2433311 = 3649967) B3649967
theorem B3645971 : Blo 566810 3645971 := bstep (se 1 (by rfl) ⟨2734478, by rfl⟩ : syracuseStep 3645971 = 5468957) B5468957
theorem B2302739 : Blo 566810 2302739 := bstep (se 1 (by rfl) ⟨1727054, by rfl⟩ : syracuseStep 2302739 = 3454109) B3454109
theorem B959593 : Blo 566810 959593 := bstep (se 2 (by rfl) ⟨359847, by rfl⟩ : syracuseStep 959593 = 719695) B719695
theorem B6563321 : Blo 566810 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B566895 : Blo 566810 566895 := bstep (se 1 (by rfl) ⟨425171, by rfl⟩ : syracuseStep 566895 = 850343) B850343
theorem B566951 : Blo 566810 566951 := bstep (se 1 (by rfl) ⟨425213, by rfl⟩ : syracuseStep 566951 = 850427) B850427
theorem B960167 : Blo 566810 960167 := bstep (se 1 (by rfl) ⟨720125, by rfl⟩ : syracuseStep 960167 = 1440251) B1440251
theorem B567035 : Blo 566810 567035 := bstep (se 1 (by rfl) ⟨425276, by rfl⟩ : syracuseStep 567035 = 850553) B850553
theorem B567071 : Blo 566810 567071 := bstep (se 1 (by rfl) ⟨425303, by rfl⟩ : syracuseStep 567071 = 850607) B850607
theorem B567103 : Blo 566810 567103 := bstep (se 1 (by rfl) ⟨425327, by rfl⟩ : syracuseStep 567103 = 850655) B850655
theorem B567279 : Blo 566810 567279 := bstep (se 1 (by rfl) ⟨425459, by rfl⟩ : syracuseStep 567279 = 850919) B850919
theorem B3450899 : Blo 566810 3450899 := bstep (se 1 (by rfl) ⟨2588174, by rfl⟩ : syracuseStep 3450899 = 5176349) B5176349
theorem B567451 : Blo 566810 567451 := bstep (se 1 (by rfl) ⟨425588, by rfl⟩ : syracuseStep 567451 = 851177) B851177
theorem B567487 : Blo 566810 567487 := bstep (se 1 (by rfl) ⟨425615, by rfl⟩ : syracuseStep 567487 = 851231) B851231
theorem B567599 : Blo 566810 567599 := bstep (se 1 (by rfl) ⟨425699, by rfl⟩ : syracuseStep 567599 = 851399) B851399
theorem B960815 : Blo 566810 960815 := bstep (se 1 (by rfl) ⟨720611, by rfl⟩ : syracuseStep 960815 = 1441223) B1441223
theorem B567835 : Blo 566810 567835 := bstep (se 1 (by rfl) ⟨425876, by rfl⟩ : syracuseStep 567835 = 851753) B851753
theorem B961051 : Blo 566810 961051 := bstep (se 1 (by rfl) ⟨720788, by rfl⟩ : syracuseStep 961051 = 1441577) B1441577
theorem B567839 : Blo 566810 567839 := bstep (se 1 (by rfl) ⟨425879, by rfl⟩ : syracuseStep 567839 = 851759) B851759
theorem B1026899 : Blo 566810 1026899 := bstep (se 1 (by rfl) ⟨770174, by rfl⟩ : syracuseStep 1026899 = 1540349) B1540349
theorem B568155 : Blo 566810 568155 := bstep (se 1 (by rfl) ⟨426116, by rfl⟩ : syracuseStep 568155 = 852233) B852233
theorem B568223 : Blo 566810 568223 := bstep (se 1 (by rfl) ⟨426167, by rfl⟩ : syracuseStep 568223 = 852335) B852335
theorem B1092655 : Blo 566810 1092655 := bstep (se 1 (by rfl) ⟨819491, by rfl⟩ : syracuseStep 1092655 = 1638983) B1638983
theorem B568367 : Blo 566810 568367 := bstep (se 1 (by rfl) ⟨426275, by rfl⟩ : syracuseStep 568367 = 852551) B852551
theorem B568391 : Blo 566810 568391 := bstep (se 1 (by rfl) ⟨426293, by rfl⟩ : syracuseStep 568391 = 852587) B852587
theorem B2043103 : Blo 566810 2043103 := bstep (se 1 (by rfl) ⟨1532327, by rfl⟩ : syracuseStep 2043103 = 3064655) B3064655
theorem B568543 : Blo 566810 568543 := bstep (se 1 (by rfl) ⟨426407, by rfl⟩ : syracuseStep 568543 = 852815) B852815
theorem B2436439 : Blo 566810 2436439 := bstep (se 1 (by rfl) ⟨1827329, by rfl⟩ : syracuseStep 2436439 = 3654659) B3654659
theorem B568807 : Blo 566810 568807 := bstep (se 1 (by rfl) ⟨426605, by rfl⟩ : syracuseStep 568807 = 853211) B853211
theorem B962023 : Blo 566810 962023 := bstep (se 1 (by rfl) ⟨721517, by rfl⟩ : syracuseStep 962023 = 1443035) B1443035
theorem B2076155 : Blo 566810 2076155 := bstep (se 1 (by rfl) ⟨1557116, by rfl⟩ : syracuseStep 2076155 = 3114233) B3114233
theorem B962111 : Blo 566810 962111 := bstep (se 1 (by rfl) ⟨721583, by rfl⟩ : syracuseStep 962111 = 1443167) B1443167
theorem B568923 : Blo 566810 568923 := bstep (se 1 (by rfl) ⟨426692, by rfl⟩ : syracuseStep 568923 = 853385) B853385
theorem B1617515 : Blo 566810 1617515 := bstep (se 1 (by rfl) ⟨1213136, by rfl⟩ : syracuseStep 1617515 = 2426273) B2426273
theorem B1617583 : Blo 566810 1617583 := bstep (se 1 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 1617583 = 2426375) B2426375
theorem B569159 : Blo 566810 569159 := bstep (se 1 (by rfl) ⟨426869, by rfl⟩ : syracuseStep 569159 = 853739) B853739
theorem B864155 : Blo 566810 864155 := bstep (se 1 (by rfl) ⟨648116, by rfl⟩ : syracuseStep 864155 = 1296233) B1296233
theorem B569311 : Blo 566810 569311 := bstep (se 1 (by rfl) ⟨426983, by rfl⟩ : syracuseStep 569311 = 853967) B853967
theorem B962779 : Blo 566810 962779 := bstep (se 1 (by rfl) ⟨722084, by rfl⟩ : syracuseStep 962779 = 1444169) B1444169
theorem B569575 : Blo 566810 569575 := bstep (se 1 (by rfl) ⟨427181, by rfl⟩ : syracuseStep 569575 = 854363) B854363
theorem B569727 : Blo 566810 569727 := bstep (se 1 (by rfl) ⟨427295, by rfl⟩ : syracuseStep 569727 = 854591) B854591
theorem B569807 : Blo 566810 569807 := bstep (se 1 (by rfl) ⟨427355, by rfl⟩ : syracuseStep 569807 = 854711) B854711
theorem B3650021 : Blo 566810 3650021 := bstep (se 4 (by rfl) ⟨342189, by rfl⟩ : syracuseStep 3650021 = 684379) B684379
theorem B963049 : Blo 566810 963049 := bstep (se 2 (by rfl) ⟨361143, by rfl⟩ : syracuseStep 963049 = 722287) B722287
theorem B569959 : Blo 566810 569959 := bstep (se 1 (by rfl) ⟨427469, by rfl⟩ : syracuseStep 569959 = 854939) B854939
theorem B570223 : Blo 566810 570223 := bstep (se 1 (by rfl) ⟨427667, by rfl⟩ : syracuseStep 570223 = 855335) B855335
theorem B570279 : Blo 566810 570279 := bstep (se 1 (by rfl) ⟨427709, by rfl⟩ : syracuseStep 570279 = 855419) B855419
theorem B1618859 : Blo 566810 1618859 := bstep (se 1 (by rfl) ⟨1214144, by rfl⟩ : syracuseStep 1618859 = 2428289) B2428289
theorem B570363 : Blo 566810 570363 := bstep (se 1 (by rfl) ⟨427772, by rfl⟩ : syracuseStep 570363 = 855545) B855545
theorem B767039 : Blo 566810 767039 := bstep (se 1 (by rfl) ⟨575279, by rfl⟩ : syracuseStep 767039 = 1150559) B1150559
theorem B570431 : Blo 566810 570431 := bstep (se 1 (by rfl) ⟨427823, by rfl⟩ : syracuseStep 570431 = 855647) B855647
theorem B6894791 : Blo 566810 6894791 := bstep (se 1 (by rfl) ⟨5171093, by rfl⟩ : syracuseStep 6894791 = 10342187) B10342187
theorem B570575 : Blo 566810 570575 := bstep (se 1 (by rfl) ⟨427931, by rfl⟩ : syracuseStep 570575 = 855863) B855863
theorem B1619291 : Blo 566810 1619291 := bstep (se 1 (by rfl) ⟨1214468, by rfl⟩ : syracuseStep 1619291 = 2428937) B2428937
theorem B570779 : Blo 566810 570779 := bstep (se 1 (by rfl) ⟨428084, by rfl⟩ : syracuseStep 570779 = 856169) B856169
theorem B1914299 : Blo 566810 1914299 := bstep (se 1 (by rfl) ⟨1435724, by rfl⟩ : syracuseStep 1914299 = 2871449) B2871449
theorem B1914839 : Blo 566810 1914839 := bstep (se 1 (by rfl) ⟨1436129, by rfl⟩ : syracuseStep 1914839 = 2872259) B2872259
theorem B1915325 : Blo 566810 1915325 := bstep (se 3 (by rfl) ⟨359123, by rfl⟩ : syracuseStep 1915325 = 718247) B718247
theorem B1620499 : Blo 566810 1620499 := bstep (se 1 (by rfl) ⟨1215374, by rfl⟩ : syracuseStep 1620499 = 2430749) B2430749
theorem B638023 : Blo 566810 638023 := bstep (se 1 (by rfl) ⟨478517, by rfl⟩ : syracuseStep 638023 = 957035) B957035
theorem B2964637 : Blo 566810 2964637 := bstep (se 3 (by rfl) ⟨555869, by rfl⟩ : syracuseStep 2964637 = 1111739) B1111739
theorem B6143147 : Blo 566810 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B1916189 : Blo 566810 1916189 := bstep (se 3 (by rfl) ⟨359285, by rfl⟩ : syracuseStep 1916189 = 718571) B718571
theorem B1621387 : Blo 566810 1621387 := bstep (se 1 (by rfl) ⟨1216040, by rfl⟩ : syracuseStep 1621387 = 2432081) B2432081
theorem B3456443 : Blo 566810 3456443 := bstep (se 1 (by rfl) ⟨2592332, by rfl⟩ : syracuseStep 3456443 = 5184665) B5184665
theorem B3653657 : Blo 566810 3653657 := bstep (se 2 (by rfl) ⟨1370121, by rfl⟩ : syracuseStep 3653657 = 2740243) B2740243
theorem B1917215 : Blo 566810 1917215 := bstep (se 1 (by rfl) ⟨1437911, by rfl⟩ : syracuseStep 1917215 = 2875823) B2875823
theorem B59294339 : Blo 566810 59294339 := bstep (se 1 (by rfl) ⟨44470754, by rfl⟩ : syracuseStep 59294339 = 88941509) B88941509
theorem B5456807 : Blo 566810 5456807 := bstep (se 1 (by rfl) ⟨4092605, by rfl⟩ : syracuseStep 5456807 = 8185211) B8185211
theorem B1917863 : Blo 566810 1917863 := bstep (se 1 (by rfl) ⟨1438397, by rfl⟩ : syracuseStep 1917863 = 2876795) B2876795
theorem B4113337 : Blo 566810 4113337 := bstep (se 2 (by rfl) ⟨1542501, by rfl⟩ : syracuseStep 4113337 = 3085003) B3085003
theorem B9225485 : Blo 566810 9225485 := bstep (se 3 (by rfl) ⟨1729778, by rfl⟩ : syracuseStep 9225485 = 3459557) B3459557
theorem B60081425 : Blo 566810 60081425 := bstep (se 2 (by rfl) ⟨22530534, by rfl⟩ : syracuseStep 60081425 = 45061069) B45061069
theorem B1918457 : Blo 566810 1918457 := bstep (se 2 (by rfl) ⟨719421, by rfl⟩ : syracuseStep 1918457 = 1438843) B1438843
theorem B21808763 : Blo 566810 21808763 := bstep (se 1 (by rfl) ⟨16356572, by rfl⟩ : syracuseStep 21808763 = 32713145) B32713145
theorem B1918727 : Blo 566810 1918727 := bstep (se 1 (by rfl) ⟨1439045, by rfl⟩ : syracuseStep 1918727 = 2878091) B2878091
theorem B1918781 : Blo 566810 1918781 := bstep (se 3 (by rfl) ⟨359771, by rfl⟩ : syracuseStep 1918781 = 719543) B719543
theorem B640831 : Blo 566810 640831 := bstep (se 1 (by rfl) ⟨480623, by rfl⟩ : syracuseStep 640831 = 961247) B961247
theorem B379012931 : Blo 566810 379012931 := bstep (se 1 (by rfl) ⟨284259698, by rfl⟩ : syracuseStep 379012931 = 568519397) B568519397
theorem B641119 : Blo 566810 641119 := bstep (se 1 (by rfl) ⟨480839, by rfl⟩ : syracuseStep 641119 = 961679) B961679
theorem B9194867 : Blo 566810 9194867 := bstep (se 1 (by rfl) ⟨6896150, by rfl⟩ : syracuseStep 9194867 = 13792301) B13792301
theorem B3657143 : Blo 566810 3657143 := bstep (se 1 (by rfl) ⟨2742857, by rfl⟩ : syracuseStep 3657143 = 5485715) B5485715
theorem B22171153 : Blo 566810 22171153 := bstep (se 2 (by rfl) ⟨8314182, by rfl⟩ : syracuseStep 22171153 = 16628365) B16628365
theorem B1036001 : Blo 566810 1036001 := bstep (se 2 (by rfl) ⟨388500, by rfl⟩ : syracuseStep 1036001 = 777001) B777001
theorem B3067769 : Blo 566810 3067769 := bstep (se 2 (by rfl) ⟨1150413, by rfl⟩ : syracuseStep 3067769 = 2300827) B2300827
theorem B51269699 : Blo 566810 51269699 := bstep (se 1 (by rfl) ⟨38452274, by rfl⟩ : syracuseStep 51269699 = 76904549) B76904549
theorem B1921211 : Blo 566810 1921211 := bstep (se 1 (by rfl) ⟨1440908, by rfl⟩ : syracuseStep 1921211 = 2881817) B2881817
theorem B1823087 : Blo 566810 1823087 := bstep (se 1 (by rfl) ⟨1367315, by rfl⟩ : syracuseStep 1823087 = 2734631) B2734631
theorem B807527 : Blo 566810 807527 := bstep (se 1 (by rfl) ⟨605645, by rfl⟩ : syracuseStep 807527 = 1211291) B1211291
theorem B1921697 : Blo 566810 1921697 := bstep (se 2 (by rfl) ⟨720636, by rfl⟩ : syracuseStep 1921697 = 1441273) B1441273
theorem B35050195 : Blo 566810 35050195 := bstep (se 1 (by rfl) ⟨26287646, by rfl⟩ : syracuseStep 35050195 = 52575293) B52575293
theorem B807727 : Blo 566810 807727 := bstep (se 1 (by rfl) ⟨605795, by rfl⟩ : syracuseStep 807727 = 1211591) B1211591
theorem B5460803 : Blo 566810 5460803 := bstep (se 1 (by rfl) ⟨4095602, by rfl⟩ : syracuseStep 5460803 = 8191205) B8191205
theorem B1823753 : Blo 566810 1823753 := bstep (se 2 (by rfl) ⟨683907, by rfl⟩ : syracuseStep 1823753 = 1367815) B1367815
theorem B2741303 : Blo 566810 2741303 := bstep (se 1 (by rfl) ⟨2055977, by rfl⟩ : syracuseStep 2741303 = 4111955) B4111955
theorem B3232979 : Blo 566810 3232979 := bstep (se 1 (by rfl) ⟨2424734, by rfl⟩ : syracuseStep 3232979 = 4849469) B4849469
theorem B9688409 : Blo 566810 9688409 := bstep (se 2 (by rfl) ⟨3633153, by rfl⟩ : syracuseStep 9688409 = 7266307) B7266307
theorem B1922561 : Blo 566810 1922561 := bstep (se 2 (by rfl) ⟨720960, by rfl⟩ : syracuseStep 1922561 = 1441921) B1441921
theorem B1923047 : Blo 566810 1923047 := bstep (se 1 (by rfl) ⟨1442285, by rfl⟩ : syracuseStep 1923047 = 2884571) B2884571
theorem B1923155 : Blo 566810 1923155 := bstep (se 1 (by rfl) ⟨1442366, by rfl⟩ : syracuseStep 1923155 = 2884733) B2884733
theorem B1923371 : Blo 566810 1923371 := bstep (se 1 (by rfl) ⟨1442528, by rfl⟩ : syracuseStep 1923371 = 2885057) B2885057
theorem B8214965 : Blo 566810 8214965 := bstep (se 5 (by rfl) ⟨385076, by rfl⟩ : syracuseStep 8214965 = 770153) B770153
theorem B1923641 : Blo 566810 1923641 := bstep (se 2 (by rfl) ⟨721365, by rfl⟩ : syracuseStep 1923641 = 1442731) B1442731
theorem B2874203 : Blo 566810 2874203 := bstep (se 1 (by rfl) ⟨2155652, by rfl⟩ : syracuseStep 2874203 = 4311305) B4311305
theorem B7297883 : Blo 566810 7297883 := bstep (se 1 (by rfl) ⟨5473412, by rfl⟩ : syracuseStep 7297883 = 10946825) B10946825
theorem B2153375 : Blo 566810 2153375 := bstep (se 1 (by rfl) ⟨1615031, by rfl⟩ : syracuseStep 2153375 = 3230063) B3230063
theorem B1367009 : Blo 566810 1367009 := bstep (se 2 (by rfl) ⟨512628, by rfl⟩ : syracuseStep 1367009 = 1025257) B1025257
theorem B3235211 : Blo 566810 3235211 := bstep (se 1 (by rfl) ⟨2426408, by rfl⟩ : syracuseStep 3235211 = 4852817) B4852817
theorem B7298909 : Blo 566810 7298909 := bstep (se 3 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 7298909 = 2737091) B2737091
theorem B1925153 : Blo 566810 1925153 := bstep (se 2 (by rfl) ⟨721932, by rfl⟩ : syracuseStep 1925153 = 1443865) B1443865
theorem B2154833 : Blo 566810 2154833 := bstep (se 2 (by rfl) ⟨808062, by rfl⟩ : syracuseStep 2154833 = 1616125) B1616125
theorem B6939067 : Blo 566810 6939067 := bstep (se 1 (by rfl) ⟨5204300, by rfl⟩ : syracuseStep 6939067 = 10408601) B10408601
theorem B909775 : Blo 566810 909775 := bstep (se 1 (by rfl) ⟨682331, by rfl⟩ : syracuseStep 909775 = 1364663) B1364663
theorem B1729001 : Blo 566810 1729001 := bstep (se 2 (by rfl) ⟨648375, by rfl⟩ : syracuseStep 1729001 = 1296751) B1296751
theorem B4154267 : Blo 566810 4154267 := bstep (se 1 (by rfl) ⟨3115700, by rfl⟩ : syracuseStep 4154267 = 6231401) B6231401
theorem B8316067 : Blo 566810 8316067 := bstep (se 1 (by rfl) ⟨6237050, by rfl⟩ : syracuseStep 8316067 = 12474101) B12474101
theorem B4875713 : Blo 566810 4875713 := bstep (se 2 (by rfl) ⟨1828392, by rfl⟩ : syracuseStep 4875713 = 3656785) B3656785
theorem B1730267 : Blo 566810 1730267 := bstep (se 1 (by rfl) ⟨1297700, by rfl⟩ : syracuseStep 1730267 = 2595401) B2595401
theorem B2877281 : Blo 566810 2877281 := bstep (se 2 (by rfl) ⟨1078980, by rfl⟩ : syracuseStep 2877281 = 2157961) B2157961
theorem B2156489 : Blo 566810 2156489 := bstep (se 2 (by rfl) ⟨808683, by rfl⟩ : syracuseStep 2156489 = 1617367) B1617367
theorem B9234971 : Blo 566810 9234971 := bstep (se 1 (by rfl) ⟨6926228, by rfl⟩ : syracuseStep 9234971 = 13852457) B13852457
theorem B4844069 : Blo 566810 4844069 := bstep (se 4 (by rfl) ⟨454131, by rfl⟩ : syracuseStep 4844069 = 908263) B908263
theorem B5204519 : Blo 566810 5204519 := bstep (se 1 (by rfl) ⟨3903389, by rfl⟩ : syracuseStep 5204519 = 7806779) B7806779
theorem B912287 : Blo 566810 912287 := bstep (se 1 (by rfl) ⟨684215, by rfl⟩ : syracuseStep 912287 = 1368431) B1368431
theorem B1076809 : Blo 566810 1076809 := bstep (se 2 (by rfl) ⟨403803, by rfl⟩ : syracuseStep 1076809 = 807607) B807607
theorem B3698291 : Blo 566810 3698291 := bstep (se 1 (by rfl) ⟨2773718, by rfl⟩ : syracuseStep 3698291 = 5547437) B5547437
theorem B3239585 : Blo 566810 3239585 := bstep (se 2 (by rfl) ⟨1214844, by rfl⟩ : syracuseStep 3239585 = 2429689) B2429689
theorem B1077113 : Blo 566810 1077113 := bstep (se 2 (by rfl) ⟨403917, by rfl⟩ : syracuseStep 1077113 = 807835) B807835
theorem B2879387 : Blo 566810 2879387 := bstep (se 1 (by rfl) ⟨2159540, by rfl⟩ : syracuseStep 2879387 = 4319081) B4319081
theorem B2158721 : Blo 566810 2158721 := bstep (se 2 (by rfl) ⟨809520, by rfl⟩ : syracuseStep 2158721 = 1619041) B1619041
theorem B49246865 : Blo 566810 49246865 := bstep (se 2 (by rfl) ⟨18467574, by rfl⟩ : syracuseStep 49246865 = 36935149) B36935149
theorem B1078267 : Blo 566810 1078267 := bstep (se 1 (by rfl) ⟨808700, by rfl⟩ : syracuseStep 1078267 = 1617401) B1617401
theorem B1733671 : Blo 566810 1733671 := bstep (se 1 (by rfl) ⟨1300253, by rfl⟩ : syracuseStep 1733671 = 2600507) B2600507
theorem B1438793 : Blo 566810 1438793 := bstep (se 2 (by rfl) ⟨539547, by rfl⟩ : syracuseStep 1438793 = 1079095) B1079095
theorem B2421899 : Blo 566810 2421899 := bstep (se 1 (by rfl) ⟨1816424, by rfl⟩ : syracuseStep 2421899 = 3632849) B3632849
theorem B2159891 : Blo 566810 2159891 := bstep (se 1 (by rfl) ⟨1619918, by rfl⟩ : syracuseStep 2159891 = 3239837) B3239837
theorem B1078753 : Blo 566810 1078753 := bstep (se 2 (by rfl) ⟨404532, by rfl⟩ : syracuseStep 1078753 = 809065) B809065
theorem B11826827 : Blo 566810 11826827 := bstep (se 1 (by rfl) ⟨8870120, by rfl⟩ : syracuseStep 11826827 = 17740241) B17740241
theorem B1275785 : Blo 566810 1275785 := bstep (se 2 (by rfl) ⟨478419, by rfl⟩ : syracuseStep 1275785 = 956839) B956839
theorem B1276001 : Blo 566810 1276001 := bstep (se 2 (by rfl) ⟨478500, by rfl⟩ : syracuseStep 1276001 = 957001) B957001
theorem B3471457 : Blo 566810 3471457 := bstep (se 2 (by rfl) ⟨1301796, by rfl⟩ : syracuseStep 3471457 = 2603593) B2603593
theorem B4847759 : Blo 566810 4847759 := bstep (se 1 (by rfl) ⟨3635819, by rfl⟩ : syracuseStep 4847759 = 7271639) B7271639
theorem B1439977 : Blo 566810 1439977 := bstep (se 2 (by rfl) ⟨539991, by rfl⟩ : syracuseStep 1439977 = 1079983) B1079983
theorem B850217 : Blo 566810 850217 := bstep (se 2 (by rfl) ⟨318831, by rfl⟩ : syracuseStep 850217 = 637663) B637663
theorem B850223 : Blo 566810 850223 := bstep (se 1 (by rfl) ⟨637667, by rfl⟩ : syracuseStep 850223 = 1275335) B1275335
theorem B850463 : Blo 566810 850463 := bstep (se 1 (by rfl) ⟨637847, by rfl⟩ : syracuseStep 850463 = 1275695) B1275695
theorem B850847 : Blo 566810 850847 := bstep (se 1 (by rfl) ⟨638135, by rfl⟩ : syracuseStep 850847 = 1276271) B1276271
theorem B850895 : Blo 566810 850895 := bstep (se 1 (by rfl) ⟨638171, by rfl⟩ : syracuseStep 850895 = 1276343) B1276343
theorem B1440737 : Blo 566810 1440737 := bstep (se 2 (by rfl) ⟨540276, by rfl⟩ : syracuseStep 1440737 = 1080553) B1080553
theorem B850985 : Blo 566810 850985 := bstep (se 2 (by rfl) ⟨319119, by rfl⟩ : syracuseStep 850985 = 638239) B638239
theorem B850991 : Blo 566810 850991 := bstep (se 1 (by rfl) ⟨638243, by rfl⟩ : syracuseStep 850991 = 1276487) B1276487
theorem B851015 : Blo 566810 851015 := bstep (se 1 (by rfl) ⟨638261, by rfl⟩ : syracuseStep 851015 = 1276523) B1276523
theorem B851279 : Blo 566810 851279 := bstep (se 1 (by rfl) ⟨638459, by rfl⟩ : syracuseStep 851279 = 1276919) B1276919
theorem B1277351 : Blo 566810 1277351 := bstep (se 1 (by rfl) ⟨958013, by rfl⟩ : syracuseStep 1277351 = 1916027) B1916027
theorem B851369 : Blo 566810 851369 := bstep (se 2 (by rfl) ⟨319263, by rfl⟩ : syracuseStep 851369 = 638527) B638527
theorem B2424275 : Blo 566810 2424275 := bstep (se 1 (by rfl) ⟨1818206, by rfl⟩ : syracuseStep 2424275 = 3636413) B3636413
theorem B3898853 : Blo 566810 3898853 := bstep (se 4 (by rfl) ⟨365517, by rfl⟩ : syracuseStep 3898853 = 731035) B731035
theorem B851519 : Blo 566810 851519 := bstep (se 1 (by rfl) ⟨638639, by rfl⟩ : syracuseStep 851519 = 1277279) B1277279
theorem B1277531 : Blo 566810 1277531 := bstep (se 1 (by rfl) ⟨958148, by rfl⟩ : syracuseStep 1277531 = 1916297) B1916297
theorem B3636845 : Blo 566810 3636845 := bstep (se 3 (by rfl) ⟨681908, by rfl⟩ : syracuseStep 3636845 = 1363817) B1363817
theorem B851783 : Blo 566810 851783 := bstep (se 1 (by rfl) ⟨638837, by rfl⟩ : syracuseStep 851783 = 1277675) B1277675
theorem B1277819 : Blo 566810 1277819 := bstep (se 1 (by rfl) ⟨958364, by rfl⟩ : syracuseStep 1277819 = 1916729) B1916729
theorem B851867 : Blo 566810 851867 := bstep (se 1 (by rfl) ⟨638900, by rfl⟩ : syracuseStep 851867 = 1277801) B1277801
theorem B1081259 : Blo 566810 1081259 := bstep (se 1 (by rfl) ⟨810944, by rfl⟩ : syracuseStep 1081259 = 1621889) B1621889
theorem B1278143 : Blo 566810 1278143 := bstep (se 1 (by rfl) ⟨958607, by rfl⟩ : syracuseStep 1278143 = 1917215) B1917215
theorem B852203 : Blo 566810 852203 := bstep (se 1 (by rfl) ⟨639152, by rfl⟩ : syracuseStep 852203 = 1278305) B1278305
theorem B852263 : Blo 566810 852263 := bstep (se 1 (by rfl) ⟨639197, by rfl⟩ : syracuseStep 852263 = 1278395) B1278395
theorem B3637871 : Blo 566810 3637871 := bstep (se 1 (by rfl) ⟨2728403, by rfl⟩ : syracuseStep 3637871 = 5456807) B5456807
theorem B1278575 : Blo 566810 1278575 := bstep (se 1 (by rfl) ⟨958931, by rfl⟩ : syracuseStep 1278575 = 1917863) B1917863
theorem B2884409 : Blo 566810 2884409 := bstep (se 2 (by rfl) ⟨1081653, by rfl⟩ : syracuseStep 2884409 = 2163307) B2163307
theorem B852935 : Blo 566810 852935 := bstep (se 1 (by rfl) ⟨639701, by rfl⟩ : syracuseStep 852935 = 1279403) B1279403
theorem B1278971 : Blo 566810 1278971 := bstep (se 1 (by rfl) ⟨959228, by rfl⟩ : syracuseStep 1278971 = 1918457) B1918457
theorem B853103 : Blo 566810 853103 := bstep (se 1 (by rfl) ⟨639827, by rfl⟩ : syracuseStep 853103 = 1279655) B1279655
theorem B1279151 : Blo 566810 1279151 := bstep (se 1 (by rfl) ⟨959363, by rfl⟩ : syracuseStep 1279151 = 1918727) B1918727
theorem B1279187 : Blo 566810 1279187 := bstep (se 1 (by rfl) ⟨959390, by rfl⟩ : syracuseStep 1279187 = 1918781) B1918781
theorem B252675287 : Blo 566810 252675287 := bstep (se 1 (by rfl) ⟨189506465, by rfl⟩ : syracuseStep 252675287 = 379012931) B379012931
theorem B853295 : Blo 566810 853295 := bstep (se 1 (by rfl) ⟨639971, by rfl⟩ : syracuseStep 853295 = 1279943) B1279943
theorem B2426203 : Blo 566810 2426203 := bstep (se 1 (by rfl) ⟨1819652, by rfl⟩ : syracuseStep 2426203 = 3639305) B3639305
theorem B1279457 : Blo 566810 1279457 := bstep (se 2 (by rfl) ⟨479796, by rfl⟩ : syracuseStep 1279457 = 959593) B959593
theorem B853499 : Blo 566810 853499 := bstep (se 1 (by rfl) ⟨640124, by rfl⟩ : syracuseStep 853499 = 1280249) B1280249
theorem B853535 : Blo 566810 853535 := bstep (se 1 (by rfl) ⟨640151, by rfl⟩ : syracuseStep 853535 = 1280303) B1280303
theorem B1443359 : Blo 566810 1443359 := bstep (se 1 (by rfl) ⟨1082519, by rfl⟩ : syracuseStep 1443359 = 2165039) B2165039
theorem B853679 : Blo 566810 853679 := bstep (se 1 (by rfl) ⟨640259, by rfl⟩ : syracuseStep 853679 = 1280519) B1280519
theorem B853799 : Blo 566810 853799 := bstep (se 1 (by rfl) ⟨640349, by rfl⟩ : syracuseStep 853799 = 1280699) B1280699
theorem B1444027 : Blo 566810 1444027 := bstep (se 1 (by rfl) ⟨1083020, by rfl⟩ : syracuseStep 1444027 = 2166041) B2166041
theorem B6129911 : Blo 566810 6129911 := bstep (se 1 (by rfl) ⟨4597433, by rfl⟩ : syracuseStep 6129911 = 9194867) B9194867
theorem B854351 : Blo 566810 854351 := bstep (se 1 (by rfl) ⟨640763, by rfl⟩ : syracuseStep 854351 = 1281527) B1281527
theorem B854399 : Blo 566810 854399 := bstep (se 1 (by rfl) ⟨640799, by rfl⟩ : syracuseStep 854399 = 1281599) B1281599
theorem B5179787 : Blo 566810 5179787 := bstep (se 1 (by rfl) ⟨3884840, by rfl⟩ : syracuseStep 5179787 = 7769681) B7769681
theorem B11078045 : Blo 566810 11078045 := bstep (se 3 (by rfl) ⟨2077133, by rfl⟩ : syracuseStep 11078045 = 4154267) B4154267
theorem B4852133 : Blo 566810 4852133 := bstep (se 4 (by rfl) ⟨454887, by rfl⟩ : syracuseStep 4852133 = 909775) B909775
theorem B854441 : Blo 566810 854441 := bstep (se 2 (by rfl) ⟨320415, by rfl⟩ : syracuseStep 854441 = 640831) B640831
theorem B1280807 : Blo 566810 1280807 := bstep (se 1 (by rfl) ⟨960605, by rfl⟩ : syracuseStep 1280807 = 1921211) B1921211
theorem B854825 : Blo 566810 854825 := bstep (se 2 (by rfl) ⟨320559, by rfl⟩ : syracuseStep 854825 = 641119) B641119
theorem B855035 : Blo 566810 855035 := bstep (se 1 (by rfl) ⟨641276, by rfl⟩ : syracuseStep 855035 = 1282553) B1282553
theorem B855095 : Blo 566810 855095 := bstep (se 1 (by rfl) ⟨641321, by rfl⟩ : syracuseStep 855095 = 1282643) B1282643
theorem B1281131 : Blo 566810 1281131 := bstep (se 1 (by rfl) ⟨960848, by rfl⟩ : syracuseStep 1281131 = 1921697) B1921697
theorem B855215 : Blo 566810 855215 := bstep (se 1 (by rfl) ⟨641411, by rfl⟩ : syracuseStep 855215 = 1282823) B1282823
theorem B3640535 : Blo 566810 3640535 := bstep (se 1 (by rfl) ⟨2730401, by rfl⟩ : syracuseStep 3640535 = 5460803) B5460803
theorem B2624879 : Blo 566810 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B1281401 : Blo 566810 1281401 := bstep (se 2 (by rfl) ⟨480525, by rfl⟩ : syracuseStep 1281401 = 961051) B961051
theorem B6458939 : Blo 566810 6458939 := bstep (se 1 (by rfl) ⟨4844204, by rfl⟩ : syracuseStep 6458939 = 9688409) B9688409
theorem B1314407 : Blo 566810 1314407 := bstep (se 1 (by rfl) ⟨985805, by rfl⟩ : syracuseStep 1314407 = 1971611) B1971611
theorem B1281707 : Blo 566810 1281707 := bstep (se 1 (by rfl) ⟨961280, by rfl⟩ : syracuseStep 1281707 = 1922561) B1922561
theorem B855935 : Blo 566810 855935 := bstep (se 1 (by rfl) ⟨641951, by rfl⟩ : syracuseStep 855935 = 1283903) B1283903
theorem B1282031 : Blo 566810 1282031 := bstep (se 1 (by rfl) ⟨961523, by rfl⟩ : syracuseStep 1282031 = 1923047) B1923047
theorem B9244691 : Blo 566810 9244691 := bstep (se 1 (by rfl) ⟨6933518, by rfl⟩ : syracuseStep 9244691 = 13867037) B13867037
theorem B1282103 : Blo 566810 1282103 := bstep (se 1 (by rfl) ⟨961577, by rfl⟩ : syracuseStep 1282103 = 1923155) B1923155
theorem B856127 : Blo 566810 856127 := bstep (se 1 (by rfl) ⟨642095, by rfl⟩ : syracuseStep 856127 = 1284191) B1284191
theorem B1282247 : Blo 566810 1282247 := bstep (se 1 (by rfl) ⟨961685, by rfl⟩ : syracuseStep 1282247 = 1923371) B1923371
theorem B5476643 : Blo 566810 5476643 := bstep (se 1 (by rfl) ⟨4107482, by rfl⟩ : syracuseStep 5476643 = 8214965) B8214965
theorem B2724137 : Blo 566810 2724137 := bstep (se 2 (by rfl) ⟨1021551, by rfl⟩ : syracuseStep 2724137 = 2043103) B2043103
theorem B1282427 : Blo 566810 1282427 := bstep (se 1 (by rfl) ⟨961820, by rfl⟩ : syracuseStep 1282427 = 1923641) B1923641
theorem B3248585 : Blo 566810 3248585 := bstep (se 2 (by rfl) ⟨1218219, by rfl⟩ : syracuseStep 3248585 = 2436439) B2436439
theorem B1282697 : Blo 566810 1282697 := bstep (se 2 (by rfl) ⟨481011, by rfl⟩ : syracuseStep 1282697 = 962023) B962023
theorem B29561537 : Blo 566810 29561537 := bstep (se 2 (by rfl) ⟨11085576, by rfl⟩ : syracuseStep 29561537 = 22171153) B22171153
theorem B2888621 : Blo 566810 2888621 := bstep (se 3 (by rfl) ⟨541616, by rfl⟩ : syracuseStep 2888621 = 1083233) B1083233
theorem B1283435 : Blo 566810 1283435 := bstep (se 1 (by rfl) ⟨962576, by rfl⟩ : syracuseStep 1283435 = 1925153) B1925153
theorem B1381871 : Blo 566810 1381871 := bstep (se 1 (by rfl) ⟨1036403, by rfl⟩ : syracuseStep 1381871 = 2072807) B2072807
theorem B1283705 : Blo 566810 1283705 := bstep (se 2 (by rfl) ⟨481389, by rfl⟩ : syracuseStep 1283705 = 962779) B962779
theorem B1152667 : Blo 566810 1152667 := bstep (se 1 (by rfl) ⟨864500, by rfl⟩ : syracuseStep 1152667 = 1729001) B1729001
theorem B2430647 : Blo 566810 2430647 := bstep (se 1 (by rfl) ⟨1822985, by rfl⟩ : syracuseStep 2430647 = 3645971) B3645971
theorem B1284065 : Blo 566810 1284065 := bstep (se 2 (by rfl) ⟨481524, by rfl⟩ : syracuseStep 1284065 = 963049) B963049
theorem B46733593 : Blo 566810 46733593 := bstep (se 2 (by rfl) ⟨17525097, by rfl⟩ : syracuseStep 46733593 = 35050195) B35050195
theorem B3250475 : Blo 566810 3250475 := bstep (se 1 (by rfl) ⟨2437856, by rfl⟩ : syracuseStep 3250475 = 4875713) B4875713
theorem B1153511 : Blo 566810 1153511 := bstep (se 1 (by rfl) ⟨865133, by rfl⟩ : syracuseStep 1153511 = 1730267) B1730267
theorem B2300599 : Blo 566810 2300599 := bstep (se 1 (by rfl) ⟨1725449, by rfl⟩ : syracuseStep 2300599 = 3450899) B3450899
theorem B4332689 : Blo 566810 4332689 := bstep (se 2 (by rfl) ⟨1624758, by rfl⟩ : syracuseStep 4332689 = 3249517) B3249517
theorem B1384103 : Blo 566810 1384103 := bstep (se 1 (by rfl) ⟨1038077, by rfl⟩ : syracuseStep 1384103 = 2076155) B2076155
theorem B2465527 : Blo 566810 2465527 := bstep (se 1 (by rfl) ⟨1849145, by rfl⟩ : syracuseStep 2465527 = 3698291) B3698291
theorem B4628609 : Blo 566810 4628609 := bstep (se 2 (by rfl) ⟨1735728, by rfl⟩ : syracuseStep 4628609 = 3471457) B3471457
theorem B2433347 : Blo 566810 2433347 := bstep (se 1 (by rfl) ⟨1825010, by rfl⟩ : syracuseStep 2433347 = 3650021) B3650021
theorem B4858217 : Blo 566810 4858217 := bstep (se 2 (by rfl) ⟨1821831, by rfl⟩ : syracuseStep 4858217 = 3643663) B3643663
theorem B959195 : Blo 566810 959195 := bstep (se 1 (by rfl) ⟨719396, by rfl⟩ : syracuseStep 959195 = 1438793) B1438793
theorem B1614599 : Blo 566810 1614599 := bstep (se 1 (by rfl) ⟨1210949, by rfl⟩ : syracuseStep 1614599 = 2421899) B2421899
theorem B4596527 : Blo 566810 4596527 := bstep (se 1 (by rfl) ⟨3447395, by rfl⟩ : syracuseStep 4596527 = 6894791) B6894791
theorem B10953589 : Blo 566810 10953589 := bstep (se 5 (by rfl) ⟨513449, by rfl⟩ : syracuseStep 10953589 = 1026899) B1026899
theorem B566811 : Blo 566810 566811 := bstep (se 1 (by rfl) ⟨425108, by rfl⟩ : syracuseStep 566811 = 850217) B850217
theorem B566815 : Blo 566810 566815 := bstep (se 1 (by rfl) ⟨425111, by rfl⟩ : syracuseStep 566815 = 850223) B850223
theorem B566975 : Blo 566810 566975 := bstep (se 1 (by rfl) ⟨425231, by rfl⟩ : syracuseStep 566975 = 850463) B850463
theorem B31205209 : Blo 566810 31205209 := bstep (se 2 (by rfl) ⟨11701953, by rfl⟩ : syracuseStep 31205209 = 23403907) B23403907
theorem B2762669 : Blo 566810 2762669 := bstep (se 3 (by rfl) ⟨518000, by rfl⟩ : syracuseStep 2762669 = 1036001) B1036001
theorem B567231 : Blo 566810 567231 := bstep (se 1 (by rfl) ⟨425423, by rfl⟩ : syracuseStep 567231 = 850847) B850847
theorem B567263 : Blo 566810 567263 := bstep (se 1 (by rfl) ⟨425447, by rfl⟩ : syracuseStep 567263 = 850895) B850895
theorem B960491 : Blo 566810 960491 := bstep (se 1 (by rfl) ⟨720368, by rfl⟩ : syracuseStep 960491 = 1440737) B1440737
theorem B567323 : Blo 566810 567323 := bstep (se 1 (by rfl) ⟨425492, by rfl⟩ : syracuseStep 567323 = 850985) B850985
theorem B567327 : Blo 566810 567327 := bstep (se 1 (by rfl) ⟨425495, by rfl⟩ : syracuseStep 567327 = 850991) B850991
theorem B567343 : Blo 566810 567343 := bstep (se 1 (by rfl) ⟨425507, by rfl⟩ : syracuseStep 567343 = 851015) B851015
theorem B567519 : Blo 566810 567519 := bstep (se 1 (by rfl) ⟨425639, by rfl⟩ : syracuseStep 567519 = 851279) B851279
theorem B567579 : Blo 566810 567579 := bstep (se 1 (by rfl) ⟨425684, by rfl⟩ : syracuseStep 567579 = 851369) B851369
theorem B2304295 : Blo 566810 2304295 := bstep (se 1 (by rfl) ⟨1728221, by rfl⟩ : syracuseStep 2304295 = 3456443) B3456443
theorem B1616183 : Blo 566810 1616183 := bstep (se 1 (by rfl) ⟨1212137, by rfl⟩ : syracuseStep 1616183 = 2424275) B2424275
theorem B2599235 : Blo 566810 2599235 := bstep (se 1 (by rfl) ⟨1949426, by rfl⟩ : syracuseStep 2599235 = 3898853) B3898853
theorem B567679 : Blo 566810 567679 := bstep (se 1 (by rfl) ⟨425759, by rfl⟩ : syracuseStep 567679 = 851519) B851519
theorem B567855 : Blo 566810 567855 := bstep (se 1 (by rfl) ⟨425891, by rfl⟩ : syracuseStep 567855 = 851783) B851783
theorem B567911 : Blo 566810 567911 := bstep (se 1 (by rfl) ⟨425933, by rfl⟩ : syracuseStep 567911 = 851867) B851867
theorem B2435771 : Blo 566810 2435771 := bstep (se 1 (by rfl) ⟨1826828, by rfl⟩ : syracuseStep 2435771 = 3653657) B3653657
theorem B136719197 : Blo 566810 136719197 := bstep (se 3 (by rfl) ⟨25634849, by rfl⟩ : syracuseStep 136719197 = 51269699) B51269699
theorem B568287 : Blo 566810 568287 := bstep (se 1 (by rfl) ⟨426215, by rfl⟩ : syracuseStep 568287 = 852431) B852431
theorem B568315 : Blo 566810 568315 := bstep (se 1 (by rfl) ⟨426236, by rfl⟩ : syracuseStep 568315 = 852473) B852473
theorem B568383 : Blo 566810 568383 := bstep (se 1 (by rfl) ⟨426287, by rfl⟩ : syracuseStep 568383 = 852575) B852575
theorem B39529559 : Blo 566810 39529559 := bstep (se 1 (by rfl) ⟨29647169, by rfl⟩ : syracuseStep 39529559 = 59294339) B59294339
theorem B3648635 : Blo 566810 3648635 := bstep (se 1 (by rfl) ⟨2736476, by rfl⟩ : syracuseStep 3648635 = 5472953) B5472953
theorem B9252089 : Blo 566810 9252089 := bstep (se 2 (by rfl) ⟨3469533, by rfl⟩ : syracuseStep 9252089 = 6939067) B6939067
theorem B568703 : Blo 566810 568703 := bstep (se 1 (by rfl) ⟨426527, by rfl⟩ : syracuseStep 568703 = 853055) B853055
theorem B568731 : Blo 566810 568731 := bstep (se 1 (by rfl) ⟨426548, by rfl⟩ : syracuseStep 568731 = 853097) B853097
theorem B568799 : Blo 566810 568799 := bstep (se 1 (by rfl) ⟨426599, by rfl⟩ : syracuseStep 568799 = 853199) B853199
theorem B40054283 : Blo 566810 40054283 := bstep (se 1 (by rfl) ⟨30040712, by rfl⟩ : syracuseStep 40054283 = 60081425) B60081425
theorem B568935 : Blo 566810 568935 := bstep (se 1 (by rfl) ⟨426701, by rfl⟩ : syracuseStep 568935 = 853403) B853403
theorem B4861565 : Blo 566810 4861565 := bstep (se 3 (by rfl) ⟨911543, by rfl⟩ : syracuseStep 4861565 = 1823087) B1823087
theorem B1617641 : Blo 566810 1617641 := bstep (se 2 (by rfl) ⟨606615, by rfl⟩ : syracuseStep 1617641 = 1213231) B1213231
theorem B569083 : Blo 566810 569083 := bstep (se 1 (by rfl) ⟨426812, by rfl⟩ : syracuseStep 569083 = 853625) B853625
theorem B569151 : Blo 566810 569151 := bstep (se 1 (by rfl) ⟨426863, by rfl⟩ : syracuseStep 569151 = 853727) B853727
theorem B569215 : Blo 566810 569215 := bstep (se 1 (by rfl) ⟨426911, by rfl⟩ : syracuseStep 569215 = 853823) B853823
theorem B5484449 : Blo 566810 5484449 := bstep (se 2 (by rfl) ⟨2056668, by rfl⟩ : syracuseStep 5484449 = 4113337) B4113337
theorem B569327 : Blo 566810 569327 := bstep (se 1 (by rfl) ⟨426995, by rfl⟩ : syracuseStep 569327 = 853991) B853991
theorem B569339 : Blo 566810 569339 := bstep (se 1 (by rfl) ⟨427004, by rfl⟩ : syracuseStep 569339 = 854009) B854009
theorem B569407 : Blo 566810 569407 := bstep (se 1 (by rfl) ⟨427055, by rfl⟩ : syracuseStep 569407 = 854111) B854111
theorem B569447 : Blo 566810 569447 := bstep (se 1 (by rfl) ⟨427085, by rfl⟩ : syracuseStep 569447 = 854171) B854171
theorem B569471 : Blo 566810 569471 := bstep (se 1 (by rfl) ⟨427103, by rfl⟩ : syracuseStep 569471 = 854207) B854207
theorem B569499 : Blo 566810 569499 := bstep (se 1 (by rfl) ⟨427124, by rfl⟩ : syracuseStep 569499 = 854249) B854249
theorem B11088089 : Blo 566810 11088089 := bstep (se 2 (by rfl) ⟨4158033, by rfl⟩ : syracuseStep 11088089 = 8316067) B8316067
theorem B4108519 : Blo 566810 4108519 := bstep (se 1 (by rfl) ⟨3081389, by rfl⟩ : syracuseStep 4108519 = 6162779) B6162779
theorem B1028371 : Blo 566810 1028371 := bstep (se 1 (by rfl) ⟨771278, by rfl⟩ : syracuseStep 1028371 = 1542557) B1542557
theorem B569703 : Blo 566810 569703 := bstep (se 1 (by rfl) ⟨427277, by rfl⟩ : syracuseStep 569703 = 854555) B854555
theorem B569755 : Blo 566810 569755 := bstep (se 1 (by rfl) ⟨427316, by rfl⟩ : syracuseStep 569755 = 854633) B854633
theorem B570107 : Blo 566810 570107 := bstep (se 1 (by rfl) ⟨427580, by rfl⟩ : syracuseStep 570107 = 855161) B855161
theorem B570175 : Blo 566810 570175 := bstep (se 1 (by rfl) ⟨427631, by rfl⟩ : syracuseStep 570175 = 855263) B855263
theorem B570203 : Blo 566810 570203 := bstep (se 1 (by rfl) ⟨427652, by rfl⟩ : syracuseStep 570203 = 855305) B855305
theorem B9745271 : Blo 566810 9745271 := bstep (se 1 (by rfl) ⟨7308953, by rfl⟩ : syracuseStep 9745271 = 14617907) B14617907
theorem B1618825 : Blo 566810 1618825 := bstep (se 2 (by rfl) ⟨607059, by rfl⟩ : syracuseStep 1618825 = 1214119) B1214119
theorem B570271 : Blo 566810 570271 := bstep (se 1 (by rfl) ⟨427703, by rfl⟩ : syracuseStep 570271 = 855407) B855407
theorem B2438095 : Blo 566810 2438095 := bstep (se 1 (by rfl) ⟨1828571, by rfl⟩ : syracuseStep 2438095 = 3657143) B3657143
theorem B570351 : Blo 566810 570351 := bstep (se 1 (by rfl) ⟨427763, by rfl⟩ : syracuseStep 570351 = 855527) B855527
theorem B570439 : Blo 566810 570439 := bstep (se 1 (by rfl) ⟨427829, by rfl⟩ : syracuseStep 570439 = 855659) B855659
theorem B570523 : Blo 566810 570523 := bstep (se 1 (by rfl) ⟨427892, by rfl⟩ : syracuseStep 570523 = 855785) B855785
theorem B2045179 : Blo 566810 2045179 := bstep (se 1 (by rfl) ⟨1533884, by rfl⟩ : syracuseStep 2045179 = 3067769) B3067769
theorem B570619 : Blo 566810 570619 := bstep (se 1 (by rfl) ⟨427964, by rfl⟩ : syracuseStep 570619 = 855929) B855929
theorem B570687 : Blo 566810 570687 := bstep (se 1 (by rfl) ⟨428015, by rfl⟩ : syracuseStep 570687 = 856031) B856031
theorem B4863341 : Blo 566810 4863341 := bstep (se 3 (by rfl) ⟨911876, by rfl⟩ : syracuseStep 4863341 = 1823753) B1823753
theorem B9221795 : Blo 566810 9221795 := bstep (se 1 (by rfl) ⟨6916346, by rfl⟩ : syracuseStep 9221795 = 13832693) B13832693
theorem B19642175 : Blo 566810 19642175 := bstep (se 1 (by rfl) ⟨14731631, by rfl⟩ : syracuseStep 19642175 = 29463263) B29463263
theorem B637807 : Blo 566810 637807 := bstep (se 1 (by rfl) ⟨478355, by rfl⟩ : syracuseStep 637807 = 956711) B956711
theorem B1916135 : Blo 566810 1916135 := bstep (se 1 (by rfl) ⟨1437101, by rfl⟩ : syracuseStep 1916135 = 2874203) B2874203
theorem B4865255 : Blo 566810 4865255 := bstep (se 1 (by rfl) ⟨3648941, by rfl⟩ : syracuseStep 4865255 = 7297883) B7297883
theorem B15515459 : Blo 566810 15515459 := bstep (se 1 (by rfl) ⟨11636594, by rfl⟩ : syracuseStep 15515459 = 23273189) B23273189
theorem B4865939 : Blo 566810 4865939 := bstep (se 1 (by rfl) ⟨3649454, by rfl⟩ : syracuseStep 4865939 = 7298909) B7298909
theorem B638887 : Blo 566810 638887 := bstep (se 1 (by rfl) ⟨479165, by rfl⟩ : syracuseStep 638887 = 958331) B958331
theorem B1622207 : Blo 566810 1622207 := bstep (se 1 (by rfl) ⟨1216655, by rfl⟩ : syracuseStep 1622207 = 2433311) B2433311
theorem B4375547 : Blo 566810 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B640111 : Blo 566810 640111 := bstep (se 1 (by rfl) ⟨480083, by rfl⟩ : syracuseStep 640111 = 960167) B960167
theorem B1918187 : Blo 566810 1918187 := bstep (se 1 (by rfl) ⟨1438640, by rfl⟩ : syracuseStep 1918187 = 2877281) B2877281
theorem B2311561 : Blo 566810 2311561 := bstep (se 2 (by rfl) ⟨866835, by rfl⟩ : syracuseStep 2311561 = 1733671) B1733671
theorem B640543 : Blo 566810 640543 := bstep (se 1 (by rfl) ⟨480407, by rfl⟩ : syracuseStep 640543 = 960815) B960815
theorem B3229379 : Blo 566810 3229379 := bstep (se 1 (by rfl) ⟨2422034, by rfl⟩ : syracuseStep 3229379 = 4844069) B4844069
theorem B8406773 : Blo 566810 8406773 := bstep (se 5 (by rfl) ⟨394067, by rfl⟩ : syracuseStep 8406773 = 788135) B788135
theorem B608191 : Blo 566810 608191 := bstep (se 1 (by rfl) ⟨456143, by rfl⟩ : syracuseStep 608191 = 912287) B912287
theorem B641407 : Blo 566810 641407 := bstep (se 1 (by rfl) ⟨481055, by rfl⟩ : syracuseStep 641407 = 962111) B962111
theorem B576103 : Blo 566810 576103 := bstep (se 1 (by rfl) ⟨432077, by rfl⟩ : syracuseStep 576103 = 864155) B864155
theorem B1919591 : Blo 566810 1919591 := bstep (se 1 (by rfl) ⟨1439693, by rfl⟩ : syracuseStep 1919591 = 2879387) B2879387
theorem B1624873 : Blo 566810 1624873 := bstep (se 2 (by rfl) ⟨609327, by rfl⟩ : syracuseStep 1624873 = 1218655) B1218655
theorem B1919969 : Blo 566810 1919969 := bstep (se 2 (by rfl) ⟨719988, by rfl⟩ : syracuseStep 1919969 = 1439977) B1439977
theorem B2805101 : Blo 566810 2805101 := bstep (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) B1051913
theorem B7884551 : Blo 566810 7884551 := bstep (se 1 (by rfl) ⟨5913413, by rfl⟩ : syracuseStep 7884551 = 11826827) B11826827
theorem B5459845 : Blo 566810 5459845 := bstep (se 4 (by rfl) ⟨511860, by rfl⟩ : syracuseStep 5459845 = 1023721) B1023721
theorem B3231839 : Blo 566810 3231839 := bstep (se 1 (by rfl) ⟨2423879, by rfl⟩ : syracuseStep 3231839 = 4847759) B4847759
theorem B3952849 : Blo 566810 3952849 := bstep (se 2 (by rfl) ⟨1482318, by rfl⟩ : syracuseStep 3952849 = 2964637) B2964637
theorem B8181749 : Blo 566810 8181749 := bstep (se 5 (by rfl) ⟨383519, by rfl⟩ : syracuseStep 8181749 = 767039) B767039
theorem B6150323 : Blo 566810 6150323 := bstep (se 1 (by rfl) ⟨4612742, by rfl⟩ : syracuseStep 6150323 = 9225485) B9225485
theorem B1923425 : Blo 566810 1923425 := bstep (se 2 (by rfl) ⟨721284, by rfl⟩ : syracuseStep 1923425 = 1442569) B1442569
theorem B14539175 : Blo 566810 14539175 := bstep (se 1 (by rfl) ⟨10904381, by rfl⟩ : syracuseStep 14539175 = 21808763) B21808763
theorem B3889595 : Blo 566810 3889595 := bstep (se 1 (by rfl) ⟨2917196, by rfl⟩ : syracuseStep 3889595 = 5834393) B5834393
theorem B1923911 : Blo 566810 1923911 := bstep (se 1 (by rfl) ⟨1442933, by rfl⟩ : syracuseStep 1923911 = 2885867) B2885867
theorem B2054983 : Blo 566810 2054983 := bstep (se 1 (by rfl) ⟨1541237, by rfl⟩ : syracuseStep 2054983 = 3082475) B3082475
theorem B809851 : Blo 566810 809851 := bstep (se 1 (by rfl) ⟨607388, by rfl⟩ : syracuseStep 809851 = 1214777) B1214777
theorem B2153405 : Blo 566810 2153405 := bstep (se 3 (by rfl) ⟨403763, by rfl⟩ : syracuseStep 2153405 = 807527) B807527
theorem B2186423 : Blo 566810 2186423 := bstep (se 1 (by rfl) ⟨1639817, by rfl⟩ : syracuseStep 2186423 = 3279635) B3279635
theorem B1924775 : Blo 566810 1924775 := bstep (se 1 (by rfl) ⟨1443581, by rfl⟩ : syracuseStep 1924775 = 2887163) B2887163
theorem B1924883 : Blo 566810 1924883 := bstep (se 1 (by rfl) ⟨1443662, by rfl⟩ : syracuseStep 1924883 = 2887325) B2887325
theorem B4874003 : Blo 566810 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B1532297 : Blo 566810 1532297 := bstep (se 2 (by rfl) ⟨574611, by rfl⟩ : syracuseStep 1532297 = 1149223) B1149223
theorem B1827535 : Blo 566810 1827535 := bstep (se 1 (by rfl) ⟨1370651, by rfl⟩ : syracuseStep 1827535 = 2741303) B2741303
theorem B2155319 : Blo 566810 2155319 := bstep (se 1 (by rfl) ⟨1616489, by rfl⟩ : syracuseStep 2155319 = 3232979) B3232979
theorem B4318109 : Blo 566810 4318109 := bstep (se 3 (by rfl) ⟨809645, by rfl⟩ : syracuseStep 4318109 = 1619291) B1619291
theorem B20800421 : Blo 566810 20800421 := bstep (se 4 (by rfl) ⟨1950039, by rfl⟩ : syracuseStep 20800421 = 3900079) B3900079
theorem B1435583 : Blo 566810 1435583 := bstep (se 1 (by rfl) ⟨1076687, by rfl⟩ : syracuseStep 1435583 = 2153375) B2153375
theorem B911339 : Blo 566810 911339 := bstep (se 1 (by rfl) ⟨683504, by rfl⟩ : syracuseStep 911339 = 1367009) B1367009
theorem B1435745 : Blo 566810 1435745 := bstep (se 2 (by rfl) ⟨538404, by rfl⟩ : syracuseStep 1435745 = 1076809) B1076809
theorem B4090067 : Blo 566810 4090067 := bstep (se 1 (by rfl) ⟨3067550, by rfl⟩ : syracuseStep 4090067 = 6135101) B6135101
theorem B2156777 : Blo 566810 2156777 := bstep (se 2 (by rfl) ⟨808791, by rfl⟩ : syracuseStep 2156777 = 1617583) B1617583
theorem B2156807 : Blo 566810 2156807 := bstep (se 1 (by rfl) ⟨1617605, by rfl⟩ : syracuseStep 2156807 = 3235211) B3235211
theorem B1436555 : Blo 566810 1436555 := bstep (se 1 (by rfl) ⟨1077416, by rfl⟩ : syracuseStep 1436555 = 2154833) B2154833
theorem B5827493 : Blo 566810 5827493 := bstep (se 4 (by rfl) ⟨546327, by rfl⟩ : syracuseStep 5827493 = 1092655) B1092655
theorem B1535159 : Blo 566810 1535159 := bstep (se 1 (by rfl) ⟨1151369, by rfl⟩ : syracuseStep 1535159 = 2302739) B2302739
theorem B1076969 : Blo 566810 1076969 := bstep (se 2 (by rfl) ⟨403863, by rfl⟩ : syracuseStep 1076969 = 807727) B807727
theorem B1437659 : Blo 566810 1437659 := bstep (se 1 (by rfl) ⟨1078244, by rfl⟩ : syracuseStep 1437659 = 2156489) B2156489
theorem B1437689 : Blo 566810 1437689 := bstep (se 2 (by rfl) ⟨539133, by rfl⟩ : syracuseStep 1437689 = 1078267) B1078267
theorem B6156647 : Blo 566810 6156647 := bstep (se 1 (by rfl) ⟨4617485, by rfl⟩ : syracuseStep 6156647 = 9234971) B9234971
theorem B3469679 : Blo 566810 3469679 := bstep (se 1 (by rfl) ⟨2602259, by rfl⟩ : syracuseStep 3469679 = 5204519) B5204519
theorem B1438337 : Blo 566810 1438337 := bstep (se 2 (by rfl) ⟨539376, by rfl⟩ : syracuseStep 1438337 = 1078753) B1078753
theorem B1078343 : Blo 566810 1078343 := bstep (se 1 (by rfl) ⟨808757, by rfl⟩ : syracuseStep 1078343 = 1617515) B1617515
theorem B2159723 : Blo 566810 2159723 := bstep (se 1 (by rfl) ⟨1619792, by rfl⟩ : syracuseStep 2159723 = 3239585) B3239585
theorem B718075 : Blo 566810 718075 := bstep (se 1 (by rfl) ⟨538556, by rfl⟩ : syracuseStep 718075 = 1077113) B1077113
theorem B1439147 : Blo 566810 1439147 := bstep (se 1 (by rfl) ⟨1079360, by rfl⟩ : syracuseStep 1439147 = 2158721) B2158721
theorem B32831243 : Blo 566810 32831243 := bstep (se 1 (by rfl) ⟨24623432, by rfl⟩ : syracuseStep 32831243 = 49246865) B49246865
theorem B1079239 : Blo 566810 1079239 := bstep (se 1 (by rfl) ⟨809429, by rfl⟩ : syracuseStep 1079239 = 1618859) B1618859
theorem B2160665 : Blo 566810 2160665 := bstep (se 2 (by rfl) ⟨810249, by rfl⟩ : syracuseStep 2160665 = 1620499) B1620499
theorem B1439927 : Blo 566810 1439927 := bstep (se 1 (by rfl) ⟨1079945, by rfl⟩ : syracuseStep 1439927 = 2159891) B2159891
theorem B1276199 : Blo 566810 1276199 := bstep (se 1 (by rfl) ⟨957149, by rfl⟩ : syracuseStep 1276199 = 1914299) B1914299
theorem B850523 : Blo 566810 850523 := bstep (se 1 (by rfl) ⟨637892, by rfl⟩ : syracuseStep 850523 = 1275785) B1275785
theorem B1276559 : Blo 566810 1276559 := bstep (se 1 (by rfl) ⟨957419, by rfl⟩ : syracuseStep 1276559 = 1914839) B1914839
theorem B1276649 : Blo 566810 1276649 := bstep (se 2 (by rfl) ⟨478743, by rfl⟩ : syracuseStep 1276649 = 957487) B957487
theorem B850667 : Blo 566810 850667 := bstep (se 1 (by rfl) ⟨638000, by rfl⟩ : syracuseStep 850667 = 1276001) B1276001
theorem B850697 : Blo 566810 850697 := bstep (se 2 (by rfl) ⟨319011, by rfl⟩ : syracuseStep 850697 = 638023) B638023
theorem B1276883 : Blo 566810 1276883 := bstep (se 1 (by rfl) ⟨957662, by rfl⟩ : syracuseStep 1276883 = 1915325) B1915325
theorem B2161849 : Blo 566810 2161849 := bstep (se 2 (by rfl) ⟨810693, by rfl⟩ : syracuseStep 2161849 = 1621387) B1621387
theorem B1277153 : Blo 566810 1277153 := bstep (se 2 (by rfl) ⟨478932, by rfl⟩ : syracuseStep 1277153 = 957865) B957865
theorem B4095431 : Blo 566810 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B1277459 : Blo 566810 1277459 := bstep (se 1 (by rfl) ⟨958094, by rfl⟩ : syracuseStep 1277459 = 1916189) B1916189
theorem B851567 : Blo 566810 851567 := bstep (se 1 (by rfl) ⟨638675, by rfl⟩ : syracuseStep 851567 = 1277351) B1277351
theorem B851687 : Blo 566810 851687 := bstep (se 1 (by rfl) ⟨638765, by rfl⟩ : syracuseStep 851687 = 1277531) B1277531
theorem B2424563 : Blo 566810 2424563 := bstep (se 1 (by rfl) ⟨1818422, by rfl⟩ : syracuseStep 2424563 = 3636845) B3636845
theorem B851879 : Blo 566810 851879 := bstep (se 1 (by rfl) ⟨638909, by rfl⟩ : syracuseStep 851879 = 1277819) B1277819
theorem B720839 : Blo 566810 720839 := bstep (se 1 (by rfl) ⟨540629, by rfl⟩ : syracuseStep 720839 = 1081259) B1081259
theorem B852095 : Blo 566810 852095 := bstep (se 1 (by rfl) ⟨639071, by rfl⟩ : syracuseStep 852095 = 1278143) B1278143
theorem B2425247 : Blo 566810 2425247 := bstep (se 1 (by rfl) ⟨1818935, by rfl⟩ : syracuseStep 2425247 = 3637871) B3637871
theorem B852383 : Blo 566810 852383 := bstep (se 1 (by rfl) ⟨639287, by rfl⟩ : syracuseStep 852383 = 1278575) B1278575
theorem B4325885 : Blo 566810 4325885 := bstep (se 3 (by rfl) ⟨811103, by rfl⟩ : syracuseStep 4325885 = 1622207) B1622207
theorem B852647 : Blo 566810 852647 := bstep (se 1 (by rfl) ⟨639485, by rfl⟩ : syracuseStep 852647 = 1278971) B1278971
theorem B2917031 : Blo 566810 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B852767 : Blo 566810 852767 := bstep (se 1 (by rfl) ⟨639575, by rfl⟩ : syracuseStep 852767 = 1279151) B1279151
theorem B852791 : Blo 566810 852791 := bstep (se 1 (by rfl) ⟨639593, by rfl⟩ : syracuseStep 852791 = 1279187) B1279187
theorem B1278791 : Blo 566810 1278791 := bstep (se 1 (by rfl) ⟨959093, by rfl⟩ : syracuseStep 1278791 = 1918187) B1918187
theorem B852971 : Blo 566810 852971 := bstep (se 1 (by rfl) ⟨639728, by rfl⟩ : syracuseStep 852971 = 1279457) B1279457
theorem B5604515 : Blo 566810 5604515 := bstep (se 1 (by rfl) ⟨4203386, by rfl⟩ : syracuseStep 5604515 = 8406773) B8406773
theorem B853481 : Blo 566810 853481 := bstep (se 2 (by rfl) ⟨320055, by rfl⟩ : syracuseStep 853481 = 640111) B640111
theorem B12289573 : Blo 566810 12289573 := bstep (se 4 (by rfl) ⟨1152147, by rfl⟩ : syracuseStep 12289573 = 2304295) B2304295
theorem B1279727 : Blo 566810 1279727 := bstep (se 1 (by rfl) ⟨959795, by rfl⟩ : syracuseStep 1279727 = 1919591) B1919591
theorem B853871 : Blo 566810 853871 := bstep (se 1 (by rfl) ⟨640403, by rfl⟩ : syracuseStep 853871 = 1280807) B1280807
theorem B1279979 : Blo 566810 1279979 := bstep (se 1 (by rfl) ⟨959984, by rfl⟩ : syracuseStep 1279979 = 1919969) B1919969
theorem B854057 : Blo 566810 854057 := bstep (se 2 (by rfl) ⟨320271, by rfl⟩ : syracuseStep 854057 = 640543) B640543
theorem B854087 : Blo 566810 854087 := bstep (se 1 (by rfl) ⟨640565, by rfl⟩ : syracuseStep 854087 = 1281131) B1281131
theorem B12257405 : Blo 566810 12257405 := bstep (se 3 (by rfl) ⟨2298263, by rfl⟩ : syracuseStep 12257405 = 4596527) B4596527
theorem B2427023 : Blo 566810 2427023 := bstep (se 1 (by rfl) ⟨1820267, by rfl⟩ : syracuseStep 2427023 = 3640535) B3640535
theorem B1870067 : Blo 566810 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B854267 : Blo 566810 854267 := bstep (se 1 (by rfl) ⟨640700, by rfl⟩ : syracuseStep 854267 = 1281401) B1281401
theorem B854471 : Blo 566810 854471 := bstep (se 1 (by rfl) ⟨640853, by rfl⟩ : syracuseStep 854471 = 1281707) B1281707
theorem B854687 : Blo 566810 854687 := bstep (se 1 (by rfl) ⟨641015, by rfl⟩ : syracuseStep 854687 = 1282031) B1282031
theorem B6163127 : Blo 566810 6163127 := bstep (se 1 (by rfl) ⟨4622345, by rfl⟩ : syracuseStep 6163127 = 9244691) B9244691
theorem B854735 : Blo 566810 854735 := bstep (se 1 (by rfl) ⟨641051, by rfl⟩ : syracuseStep 854735 = 1282103) B1282103
theorem B854831 : Blo 566810 854831 := bstep (se 1 (by rfl) ⟨641123, by rfl⟩ : syracuseStep 854831 = 1282247) B1282247
theorem B854951 : Blo 566810 854951 := bstep (se 1 (by rfl) ⟨641213, by rfl⟩ : syracuseStep 854951 = 1282427) B1282427
theorem B2165723 : Blo 566810 2165723 := bstep (se 1 (by rfl) ⟨1624292, by rfl⟩ : syracuseStep 2165723 = 3248585) B3248585
theorem B855131 : Blo 566810 855131 := bstep (se 1 (by rfl) ⟨641348, by rfl⟩ : syracuseStep 855131 = 1282697) B1282697
theorem B855209 : Blo 566810 855209 := bstep (se 2 (by rfl) ⟨320703, by rfl⟩ : syracuseStep 855209 = 641407) B641407
theorem B855623 : Blo 566810 855623 := bstep (se 1 (by rfl) ⟨641717, by rfl⟩ : syracuseStep 855623 = 1283435) B1283435
theorem B2166497 : Blo 566810 2166497 := bstep (se 2 (by rfl) ⟨812436, by rfl⟩ : syracuseStep 2166497 = 1624873) B1624873
theorem B855803 : Blo 566810 855803 := bstep (se 1 (by rfl) ⟨641852, by rfl⟩ : syracuseStep 855803 = 1283705) B1283705
theorem B856043 : Blo 566810 856043 := bstep (se 1 (by rfl) ⟨642032, by rfl⟩ : syracuseStep 856043 = 1284065) B1284065
theorem B4100215 : Blo 566810 4100215 := bstep (se 1 (by rfl) ⟨3075161, by rfl⟩ : syracuseStep 4100215 = 6150323) B6150323
theorem B2166983 : Blo 566810 2166983 := bstep (se 1 (by rfl) ⟨1625237, by rfl⟩ : syracuseStep 2166983 = 3250475) B3250475
theorem B1282283 : Blo 566810 1282283 := bstep (se 1 (by rfl) ⟨961712, by rfl⟩ : syracuseStep 1282283 = 1923425) B1923425
theorem B2593063 : Blo 566810 2593063 := bstep (se 1 (by rfl) ⟨1944797, by rfl⟩ : syracuseStep 2593063 = 3889595) B3889595
theorem B1282607 : Blo 566810 1282607 := bstep (se 1 (by rfl) ⟨961955, by rfl⟩ : syracuseStep 1282607 = 1923911) B1923911
theorem B2888459 : Blo 566810 2888459 := bstep (se 1 (by rfl) ⟨2166344, by rfl⟩ : syracuseStep 2888459 = 4332689) B4332689
theorem B922735 : Blo 566810 922735 := bstep (se 1 (by rfl) ⟨692051, by rfl⟩ : syracuseStep 922735 = 1384103) B1384103
theorem B1283183 : Blo 566810 1283183 := bstep (se 1 (by rfl) ⟨962387, by rfl⟩ : syracuseStep 1283183 = 1924775) B1924775
theorem B7279793 : Blo 566810 7279793 := bstep (se 2 (by rfl) ⟨2729922, by rfl⟩ : syracuseStep 7279793 = 5459845) B5459845
theorem B1283255 : Blo 566810 1283255 := bstep (se 1 (by rfl) ⟨962441, by rfl⟩ : syracuseStep 1283255 = 1924883) B1924883
theorem B3249335 : Blo 566810 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B3085739 : Blo 566810 3085739 := bstep (se 1 (by rfl) ⟨2314304, by rfl⟩ : syracuseStep 3085739 = 4628609) B4628609
theorem B1021531 : Blo 566810 1021531 := bstep (se 1 (by rfl) ⟨766148, by rfl⟩ : syracuseStep 1021531 = 1532297) B1532297
theorem B5478025 : Blo 566810 5478025 := bstep (se 2 (by rfl) ⟨2054259, by rfl⟩ : syracuseStep 5478025 = 4108519) B4108519
theorem B13866947 : Blo 566810 13866947 := bstep (se 1 (by rfl) ⟨10400210, by rfl⟩ : syracuseStep 13866947 = 20800421) B20800421
theorem B3250793 : Blo 566810 3250793 := bstep (se 2 (by rfl) ⟨1219047, by rfl⟩ : syracuseStep 3250793 = 2438095) B2438095
theorem B1841779 : Blo 566810 1841779 := bstep (se 1 (by rfl) ⟨1381334, by rfl⟩ : syracuseStep 1841779 = 2762669) B2762669
theorem B957055 : Blo 566810 957055 := bstep (se 1 (by rfl) ⟨717791, by rfl⟩ : syracuseStep 957055 = 1435583) B1435583
theorem B957163 : Blo 566810 957163 := bstep (se 1 (by rfl) ⟨717872, by rfl⟩ : syracuseStep 957163 = 1435745) B1435745
theorem B2726711 : Blo 566810 2726711 := bstep (se 1 (by rfl) ⟨2045033, by rfl⟩ : syracuseStep 2726711 = 4090067) B4090067
theorem B957433 : Blo 566810 957433 := bstep (se 2 (by rfl) ⟨359037, by rfl⟩ : syracuseStep 957433 = 718075) B718075
theorem B2726905 : Blo 566810 2726905 := bstep (se 2 (by rfl) ⟨1022589, by rfl⟩ : syracuseStep 2726905 = 2045179) B2045179
theorem B6495389 : Blo 566810 6495389 := bstep (se 3 (by rfl) ⟨1217885, by rfl⟩ : syracuseStep 6495389 = 2435771) B2435771
theorem B957703 : Blo 566810 957703 := bstep (se 1 (by rfl) ⟨718277, by rfl⟩ : syracuseStep 957703 = 1436555) B1436555
theorem B12328325 : Blo 566810 12328325 := bstep (se 4 (by rfl) ⟨1155780, by rfl⟩ : syracuseStep 12328325 = 2311561) B2311561
theorem B26353039 : Blo 566810 26353039 := bstep (se 1 (by rfl) ⟨19764779, by rfl⟩ : syracuseStep 26353039 = 39529559) B39529559
theorem B2432423 : Blo 566810 2432423 := bstep (se 1 (by rfl) ⟨1824317, by rfl⟩ : syracuseStep 2432423 = 3648635) B3648635
theorem B6168059 : Blo 566810 6168059 := bstep (se 1 (by rfl) ⟨4626044, by rfl⟩ : syracuseStep 6168059 = 9252089) B9252089
theorem B958439 : Blo 566810 958439 := bstep (se 1 (by rfl) ⟨718829, by rfl⟩ : syracuseStep 958439 = 1437659) B1437659
theorem B958459 : Blo 566810 958459 := bstep (se 1 (by rfl) ⟨718844, by rfl⟩ : syracuseStep 958459 = 1437689) B1437689
theorem B4104431 : Blo 566810 4104431 := bstep (se 1 (by rfl) ⟨3078323, by rfl⟩ : syracuseStep 4104431 = 6156647) B6156647
theorem B958891 : Blo 566810 958891 := bstep (se 1 (by rfl) ⟨719168, by rfl⟩ : syracuseStep 958891 = 1438337) B1438337
theorem B6496847 : Blo 566810 6496847 := bstep (se 1 (by rfl) ⟨4872635, by rfl⟩ : syracuseStep 6496847 = 9745271) B9745271
theorem B959431 : Blo 566810 959431 := bstep (se 1 (by rfl) ⟨719573, by rfl⟩ : syracuseStep 959431 = 1439147) B1439147
theorem B959951 : Blo 566810 959951 := bstep (se 1 (by rfl) ⟨719963, by rfl⟩ : syracuseStep 959951 = 1439927) B1439927
theorem B567015 : Blo 566810 567015 := bstep (se 1 (by rfl) ⟨425261, by rfl⟩ : syracuseStep 567015 = 850523) B850523
theorem B567111 : Blo 566810 567111 := bstep (se 1 (by rfl) ⟨425333, by rfl⟩ : syracuseStep 567111 = 850667) B850667
theorem B567131 : Blo 566810 567131 := bstep (se 1 (by rfl) ⟨425348, by rfl⟩ : syracuseStep 567131 = 850697) B850697
theorem B2730287 : Blo 566810 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B3287369 : Blo 566810 3287369 := bstep (se 2 (by rfl) ⟨1232763, by rfl⟩ : syracuseStep 3287369 = 2465527) B2465527
theorem B567711 : Blo 566810 567711 := bstep (se 1 (by rfl) ⟨425783, by rfl⟩ : syracuseStep 567711 = 851567) B851567
theorem B567791 : Blo 566810 567791 := bstep (se 1 (by rfl) ⟨425843, by rfl⟩ : syracuseStep 567791 = 851687) B851687
theorem B1616375 : Blo 566810 1616375 := bstep (se 1 (by rfl) ⟨1212281, by rfl⟩ : syracuseStep 1616375 = 2424563) B2424563
theorem B567919 : Blo 566810 567919 := bstep (se 1 (by rfl) ⟨425939, by rfl⟩ : syracuseStep 567919 = 851879) B851879
theorem B568135 : Blo 566810 568135 := bstep (se 1 (by rfl) ⟨426101, by rfl⟩ : syracuseStep 568135 = 852203) B852203
theorem B568175 : Blo 566810 568175 := bstep (se 1 (by rfl) ⟨426131, by rfl⟩ : syracuseStep 568175 = 852263) B852263
theorem B568623 : Blo 566810 568623 := bstep (se 1 (by rfl) ⟨426467, by rfl⟩ : syracuseStep 568623 = 852935) B852935
theorem B568735 : Blo 566810 568735 := bstep (se 1 (by rfl) ⟨426551, by rfl⟩ : syracuseStep 568735 = 853103) B853103
theorem B568863 : Blo 566810 568863 := bstep (se 1 (by rfl) ⟨426647, by rfl⟩ : syracuseStep 568863 = 853295) B853295
theorem B2436713 : Blo 566810 2436713 := bstep (se 2 (by rfl) ⟨913767, by rfl⟩ : syracuseStep 2436713 = 1827535) B1827535
theorem B568999 : Blo 566810 568999 := bstep (se 1 (by rfl) ⟨426749, by rfl⟩ : syracuseStep 568999 = 853499) B853499
theorem B569023 : Blo 566810 569023 := bstep (se 1 (by rfl) ⟨426767, by rfl⟩ : syracuseStep 569023 = 853535) B853535
theorem B962239 : Blo 566810 962239 := bstep (se 1 (by rfl) ⟨721679, by rfl⟩ : syracuseStep 962239 = 1443359) B1443359
theorem B569119 : Blo 566810 569119 := bstep (se 1 (by rfl) ⟨426839, by rfl⟩ : syracuseStep 569119 = 853679) B853679
theorem B569199 : Blo 566810 569199 := bstep (se 1 (by rfl) ⟨426899, by rfl⟩ : syracuseStep 569199 = 853799) B853799
theorem B569567 : Blo 566810 569567 := bstep (se 1 (by rfl) ⟨427175, by rfl⟩ : syracuseStep 569567 = 854351) B854351
theorem B569599 : Blo 566810 569599 := bstep (se 1 (by rfl) ⟨427199, by rfl⟩ : syracuseStep 569599 = 854399) B854399
theorem B3453191 : Blo 566810 3453191 := bstep (se 1 (by rfl) ⟨2589893, by rfl⟩ : syracuseStep 3453191 = 5179787) B5179787
theorem B7385363 : Blo 566810 7385363 := bstep (se 1 (by rfl) ⟨5539022, by rfl⟩ : syracuseStep 7385363 = 11078045) B11078045
theorem B569627 : Blo 566810 569627 := bstep (se 1 (by rfl) ⟨427220, by rfl⟩ : syracuseStep 569627 = 854441) B854441
theorem B569883 : Blo 566810 569883 := bstep (se 1 (by rfl) ⟨427412, by rfl⟩ : syracuseStep 569883 = 854825) B854825
theorem B570023 : Blo 566810 570023 := bstep (se 1 (by rfl) ⟨427517, by rfl⟩ : syracuseStep 570023 = 855035) B855035
theorem B570063 : Blo 566810 570063 := bstep (se 1 (by rfl) ⟨427547, by rfl⟩ : syracuseStep 570063 = 855095) B855095
theorem B570143 : Blo 566810 570143 := bstep (se 1 (by rfl) ⟨427607, by rfl⟩ : syracuseStep 570143 = 855215) B855215
theorem B1749919 : Blo 566810 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B4305959 : Blo 566810 4305959 := bstep (se 1 (by rfl) ⟨3229469, by rfl⟩ : syracuseStep 4305959 = 6458939) B6458939
theorem B570623 : Blo 566810 570623 := bstep (se 1 (by rfl) ⟨427967, by rfl⟩ : syracuseStep 570623 = 855935) B855935
theorem B570751 : Blo 566810 570751 := bstep (se 1 (by rfl) ⟨428063, by rfl⟩ : syracuseStep 570751 = 856127) B856127
theorem B3651095 : Blo 566810 3651095 := bstep (se 1 (by rfl) ⟨2738321, by rfl⟩ : syracuseStep 3651095 = 5476643) B5476643
theorem B1816091 : Blo 566810 1816091 := bstep (se 1 (by rfl) ⟨1362068, by rfl⟩ : syracuseStep 1816091 = 2724137) B2724137
theorem B768137 : Blo 566810 768137 := bstep (se 2 (by rfl) ⟨288051, by rfl⟩ : syracuseStep 768137 = 576103) B576103
theorem B1620431 : Blo 566810 1620431 := bstep (se 1 (by rfl) ⟨1215323, by rfl⟩ : syracuseStep 1620431 = 2430647) B2430647
theorem B3684989 : Blo 566810 3684989 := bstep (se 3 (by rfl) ⟨690935, by rfl⟩ : syracuseStep 3684989 = 1381871) B1381871
theorem B5454499 : Blo 566810 5454499 := bstep (se 1 (by rfl) ⟨4090874, by rfl⟩ : syracuseStep 5454499 = 8181749) B8181749
theorem B769007 : Blo 566810 769007 := bstep (se 1 (by rfl) ⟨576755, by rfl⟩ : syracuseStep 769007 = 1153511) B1153511
theorem B1457615 : Blo 566810 1457615 := bstep (se 1 (by rfl) ⟨1093211, by rfl⟩ : syracuseStep 1457615 = 2186423) B2186423
theorem B1622231 : Blo 566810 1622231 := bstep (se 1 (by rfl) ⟨1216673, by rfl⟩ : syracuseStep 1622231 = 2433347) B2433347
theorem B639463 : Blo 566810 639463 := bstep (se 1 (by rfl) ⟨479597, by rfl⟩ : syracuseStep 639463 = 959195) B959195
theorem B607559 : Blo 566810 607559 := bstep (se 1 (by rfl) ⟨455669, by rfl⟩ : syracuseStep 607559 = 911339) B911339
theorem B640327 : Blo 566810 640327 := bstep (se 1 (by rfl) ⟨480245, by rfl⟩ : syracuseStep 640327 = 960491) B960491
theorem B91146131 : Blo 566810 91146131 := bstep (se 1 (by rfl) ⟨68359598, by rfl⟩ : syracuseStep 91146131 = 136719197) B136719197
theorem B3884995 : Blo 566810 3884995 := bstep (se 1 (by rfl) ⟨2913746, by rfl⟩ : syracuseStep 3884995 = 5827493) B5827493
theorem B3656299 : Blo 566810 3656299 := bstep (se 1 (by rfl) ⟨2742224, by rfl⟩ : syracuseStep 3656299 = 5484449) B5484449
theorem B7392059 : Blo 566810 7392059 := bstep (se 1 (by rfl) ⟨5544044, by rfl⟩ : syracuseStep 7392059 = 11088089) B11088089
theorem B2313119 : Blo 566810 2313119 := bstep (se 1 (by rfl) ⟨1734839, by rfl⟩ : syracuseStep 2313119 = 3469679) B3469679
theorem B62311457 : Blo 566810 62311457 := bstep (se 2 (by rfl) ⟨23366796, by rfl⟩ : syracuseStep 62311457 = 46733593) B46733593
theorem B3067465 : Blo 566810 3067465 := bstep (se 2 (by rfl) ⟨1150299, by rfl⟩ : syracuseStep 3067465 = 2300599) B2300599
theorem B2739977 : Blo 566810 2739977 := bstep (se 2 (by rfl) ⟨1027491, by rfl⟩ : syracuseStep 2739977 = 2054983) B2054983
theorem B6147863 : Blo 566810 6147863 := bstep (se 1 (by rfl) ⟨4610897, by rfl⟩ : syracuseStep 6147863 = 9221795) B9221795
theorem B13094783 : Blo 566810 13094783 := bstep (se 1 (by rfl) ⟨9821087, by rfl⟩ : syracuseStep 13094783 = 19642175) B19642175
theorem B21025469 : Blo 566810 21025469 := bstep (se 3 (by rfl) ⟨3942275, by rfl⟩ : syracuseStep 21025469 = 7884551) B7884551
theorem B1922237 : Blo 566810 1922237 := bstep (se 3 (by rfl) ⟨360419, by rfl⟩ : syracuseStep 1922237 = 720839) B720839
theorem B10343639 : Blo 566810 10343639 := bstep (se 1 (by rfl) ⟨7757729, by rfl⟩ : syracuseStep 10343639 = 15515459) B15515459
theorem B1922939 : Blo 566810 1922939 := bstep (se 1 (by rfl) ⟨1442204, by rfl⟩ : syracuseStep 1922939 = 2884409) B2884409
theorem B168450191 : Blo 566810 168450191 := bstep (se 1 (by rfl) ⟨126337643, by rfl⟩ : syracuseStep 168450191 = 252675287) B252675287
theorem B2152919 : Blo 566810 2152919 := bstep (se 1 (by rfl) ⟨1614689, by rfl⟩ : syracuseStep 2152919 = 3229379) B3229379
theorem B14604785 : Blo 566810 14604785 := bstep (se 2 (by rfl) ⟨5476794, by rfl⟩ : syracuseStep 14604785 = 10953589) B10953589
theorem B4086607 : Blo 566810 4086607 := bstep (se 1 (by rfl) ⟨3064955, by rfl⟩ : syracuseStep 4086607 = 6129911) B6129911
theorem B3234755 : Blo 566810 3234755 := bstep (se 1 (by rfl) ⟨2426066, by rfl⟩ : syracuseStep 3234755 = 4852133) B4852133
theorem B3234937 : Blo 566810 3234937 := bstep (se 2 (by rfl) ⟨1213101, by rfl⟩ : syracuseStep 3234937 = 2426203) B2426203
theorem B78830765 : Blo 566810 78830765 := bstep (se 3 (by rfl) ⟨14780768, by rfl⟩ : syracuseStep 78830765 = 29561537) B29561537
theorem B876271 : Blo 566810 876271 := bstep (se 1 (by rfl) ⟨657203, by rfl⟩ : syracuseStep 876271 = 1314407) B1314407
theorem B41606945 : Blo 566810 41606945 := bstep (se 2 (by rfl) ⟨15602604, by rfl⟩ : syracuseStep 41606945 = 31205209) B31205209
theorem B2154559 : Blo 566810 2154559 := bstep (se 1 (by rfl) ⟨1615919, by rfl⟩ : syracuseStep 2154559 = 3231839) B3231839
theorem B1925369 : Blo 566810 1925369 := bstep (se 2 (by rfl) ⟨722013, by rfl⟩ : syracuseStep 1925369 = 1444027) B1444027
theorem B1925747 : Blo 566810 1925747 := bstep (se 1 (by rfl) ⟨1444310, by rfl⟩ : syracuseStep 1925747 = 2888621) B2888621
theorem B9692783 : Blo 566810 9692783 := bstep (se 1 (by rfl) ⟨7269587, by rfl⟩ : syracuseStep 9692783 = 14539175) B14539175
theorem B1435603 : Blo 566810 1435603 := bstep (se 1 (by rfl) ⟨1076702, by rfl⟩ : syracuseStep 1435603 = 2153405) B2153405
theorem B3238811 : Blo 566810 3238811 := bstep (se 1 (by rfl) ⟨2429108, by rfl⟩ : syracuseStep 3238811 = 4858217) B4858217
theorem B5270465 : Blo 566810 5270465 := bstep (se 2 (by rfl) ⟨1976424, by rfl⟩ : syracuseStep 5270465 = 3952849) B3952849
theorem B1371161 : Blo 566810 1371161 := bstep (se 2 (by rfl) ⟨514185, by rfl⟩ : syracuseStep 1371161 = 1028371) B1028371
theorem B1076399 : Blo 566810 1076399 := bstep (se 1 (by rfl) ⟨807299, by rfl⟩ : syracuseStep 1076399 = 1614599) B1614599
theorem B1436879 : Blo 566810 1436879 := bstep (se 1 (by rfl) ⟨1077659, by rfl⟩ : syracuseStep 1436879 = 2155319) B2155319
theorem B2878739 : Blo 566810 2878739 := bstep (se 1 (by rfl) ⟨2159054, by rfl⟩ : syracuseStep 2878739 = 4318109) B4318109
theorem B2158433 : Blo 566810 2158433 := bstep (se 2 (by rfl) ⟨809412, by rfl⟩ : syracuseStep 2158433 = 1618825) B1618825
theorem B1437851 : Blo 566810 1437851 := bstep (se 1 (by rfl) ⟨1078388, by rfl⟩ : syracuseStep 1437851 = 2156777) B2156777
theorem B1437871 : Blo 566810 1437871 := bstep (se 1 (by rfl) ⟨1078403, by rfl⟩ : syracuseStep 1437871 = 2156807) B2156807
theorem B1077455 : Blo 566810 1077455 := bstep (se 1 (by rfl) ⟨808091, by rfl⟩ : syracuseStep 1077455 = 1616183) B1616183
theorem B1732823 : Blo 566810 1732823 := bstep (se 1 (by rfl) ⟨1299617, by rfl⟩ : syracuseStep 1732823 = 2599235) B2599235
theorem B1536889 : Blo 566810 1536889 := bstep (se 2 (by rfl) ⟨576333, by rfl⟩ : syracuseStep 1536889 = 1152667) B1152667
theorem B26702855 : Blo 566810 26702855 := bstep (se 1 (by rfl) ⟨20027141, by rfl⟩ : syracuseStep 26702855 = 40054283) B40054283
theorem B3241043 : Blo 566810 3241043 := bstep (se 1 (by rfl) ⟨2430782, by rfl⟩ : syracuseStep 3241043 = 4861565) B4861565
theorem B717979 : Blo 566810 717979 := bstep (se 1 (by rfl) ⟨538484, by rfl⟩ : syracuseStep 717979 = 1076969) B1076969
theorem B1078427 : Blo 566810 1078427 := bstep (se 1 (by rfl) ⟨808820, by rfl⟩ : syracuseStep 1078427 = 1617641) B1617641
theorem B1438985 : Blo 566810 1438985 := bstep (se 2 (by rfl) ⟨539619, by rfl⟩ : syracuseStep 1438985 = 1079239) B1079239
theorem B4093757 : Blo 566810 4093757 := bstep (se 3 (by rfl) ⟨767579, by rfl⟩ : syracuseStep 4093757 = 1535159) B1535159
theorem B718895 : Blo 566810 718895 := bstep (se 1 (by rfl) ⟨539171, by rfl⟩ : syracuseStep 718895 = 1078343) B1078343
theorem B1439815 : Blo 566810 1439815 := bstep (se 1 (by rfl) ⟨1079861, by rfl⟩ : syracuseStep 1439815 = 2159723) B2159723
theorem B3242227 : Blo 566810 3242227 := bstep (se 1 (by rfl) ⟨2431670, by rfl⟩ : syracuseStep 3242227 = 4863341) B4863341
theorem B850409 : Blo 566810 850409 := bstep (se 2 (by rfl) ⟨318903, by rfl⟩ : syracuseStep 850409 = 637807) B637807
theorem B1079801 : Blo 566810 1079801 := bstep (se 2 (by rfl) ⟨404925, by rfl⟩ : syracuseStep 1079801 = 809851) B809851
theorem B21887495 : Blo 566810 21887495 := bstep (se 1 (by rfl) ⟨16415621, by rfl⟩ : syracuseStep 21887495 = 32831243) B32831243
theorem B1440443 : Blo 566810 1440443 := bstep (se 1 (by rfl) ⟨1080332, by rfl⟩ : syracuseStep 1440443 = 2160665) B2160665
theorem B850799 : Blo 566810 850799 := bstep (se 1 (by rfl) ⟨638099, by rfl⟩ : syracuseStep 850799 = 1276199) B1276199
theorem B2882465 : Blo 566810 2882465 := bstep (se 2 (by rfl) ⟨1080924, by rfl⟩ : syracuseStep 2882465 = 2161849) B2161849
theorem B851039 : Blo 566810 851039 := bstep (se 1 (by rfl) ⟨638279, by rfl⟩ : syracuseStep 851039 = 1276559) B1276559
theorem B851099 : Blo 566810 851099 := bstep (se 1 (by rfl) ⟨638324, by rfl⟩ : syracuseStep 851099 = 1276649) B1276649
theorem B851255 : Blo 566810 851255 := bstep (se 1 (by rfl) ⟨638441, by rfl⟩ : syracuseStep 851255 = 1276883) B1276883
theorem B851435 : Blo 566810 851435 := bstep (se 1 (by rfl) ⟨638576, by rfl⟩ : syracuseStep 851435 = 1277153) B1277153
theorem B1277423 : Blo 566810 1277423 := bstep (se 1 (by rfl) ⟨958067, by rfl⟩ : syracuseStep 1277423 = 1916135) B1916135
theorem B3243503 : Blo 566810 3243503 := bstep (se 1 (by rfl) ⟨2432627, by rfl⟩ : syracuseStep 3243503 = 4865255) B4865255
theorem B3243685 : Blo 566810 3243685 := bstep (se 4 (by rfl) ⟨304095, by rfl⟩ : syracuseStep 3243685 = 608191) B608191
theorem B851639 : Blo 566810 851639 := bstep (se 1 (by rfl) ⟨638729, by rfl⟩ : syracuseStep 851639 = 1277459) B1277459
theorem B851849 : Blo 566810 851849 := bstep (se 2 (by rfl) ⟨319443, by rfl⟩ : syracuseStep 851849 = 638887) B638887
theorem B3243959 : Blo 566810 3243959 := bstep (se 1 (by rfl) ⟨2432969, by rfl⟩ : syracuseStep 3243959 = 4865939) B4865939
theorem B1081487 : Blo 566810 1081487 := bstep (se 1 (by rfl) ⟨811115, by rfl⟩ : syracuseStep 1081487 = 1622231) B1622231
theorem B2883923 : Blo 566810 2883923 := bstep (se 1 (by rfl) ⟨2162942, by rfl⟩ : syracuseStep 2883923 = 4325885) B4325885
theorem B852527 : Blo 566810 852527 := bstep (se 1 (by rfl) ⟨639395, by rfl⟩ : syracuseStep 852527 = 1278791) B1278791
theorem B1278521 : Blo 566810 1278521 := bstep (se 2 (by rfl) ⟨479445, by rfl⟩ : syracuseStep 1278521 = 958891) B958891
theorem B852617 : Blo 566810 852617 := bstep (se 2 (by rfl) ⟨319731, by rfl⟩ : syracuseStep 852617 = 639463) B639463
theorem B3736343 : Blo 566810 3736343 := bstep (se 1 (by rfl) ⟨2802257, by rfl⟩ : syracuseStep 3736343 = 5604515) B5604515
theorem B853151 : Blo 566810 853151 := bstep (se 1 (by rfl) ⟨639863, by rfl⟩ : syracuseStep 853151 = 1279727) B1279727
theorem B1279241 : Blo 566810 1279241 := bstep (se 2 (by rfl) ⟨479715, by rfl⟩ : syracuseStep 1279241 = 959431) B959431
theorem B853319 : Blo 566810 853319 := bstep (se 1 (by rfl) ⟨639989, by rfl⟩ : syracuseStep 853319 = 1279979) B1279979
theorem B853769 : Blo 566810 853769 := bstep (se 2 (by rfl) ⟨320163, by rfl⟩ : syracuseStep 853769 = 640327) B640327
theorem B1542079 : Blo 566810 1542079 := bstep (se 1 (by rfl) ⟨1156559, by rfl⟩ : syracuseStep 1542079 = 2313119) B2313119
theorem B1443815 : Blo 566810 1443815 := bstep (se 1 (by rfl) ⟨1082861, by rfl⟩ : syracuseStep 1443815 = 2165723) B2165723
theorem B16386097 : Blo 566810 16386097 := bstep (se 2 (by rfl) ⟨6144786, by rfl⟩ : syracuseStep 16386097 = 12289573) B12289573
theorem B1444331 : Blo 566810 1444331 := bstep (se 1 (by rfl) ⟨1083248, by rfl⟩ : syracuseStep 1444331 = 2166497) B2166497
theorem B4098575 : Blo 566810 4098575 := bstep (se 1 (by rfl) ⟨3073931, by rfl⟩ : syracuseStep 4098575 = 6147863) B6147863
theorem B5179993 : Blo 566810 5179993 := bstep (se 2 (by rfl) ⟨1942497, by rfl⟩ : syracuseStep 5179993 = 3884995) B3884995
theorem B1444655 : Blo 566810 1444655 := bstep (se 1 (by rfl) ⟨1083491, by rfl⟩ : syracuseStep 1444655 = 2166983) B2166983
theorem B854855 : Blo 566810 854855 := bstep (se 1 (by rfl) ⟨641141, by rfl⟩ : syracuseStep 854855 = 1282283) B1282283
theorem B855071 : Blo 566810 855071 := bstep (se 1 (by rfl) ⟨641303, by rfl⟩ : syracuseStep 855071 = 1282607) B1282607
theorem B855455 : Blo 566810 855455 := bstep (se 1 (by rfl) ⟨641591, by rfl⟩ : syracuseStep 855455 = 1283183) B1283183
theorem B4853195 : Blo 566810 4853195 := bstep (se 1 (by rfl) ⟨3639896, by rfl⟩ : syracuseStep 4853195 = 7279793) B7279793
theorem B855503 : Blo 566810 855503 := bstep (se 1 (by rfl) ⟨641627, by rfl⟩ : syracuseStep 855503 = 1283255) B1283255
theorem B2166223 : Blo 566810 2166223 := bstep (se 1 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 2166223 = 3249335) B3249335
theorem B1281491 : Blo 566810 1281491 := bstep (se 1 (by rfl) ⟨961118, by rfl⟩ : syracuseStep 1281491 = 1922237) B1922237
theorem B1281959 : Blo 566810 1281959 := bstep (se 1 (by rfl) ⟨961469, by rfl⟩ : syracuseStep 1281959 = 1922939) B1922939
theorem B9244631 : Blo 566810 9244631 := bstep (se 1 (by rfl) ⟨6933473, by rfl⟩ : syracuseStep 9244631 = 13866947) B13866947
theorem B112300127 : Blo 566810 112300127 := bstep (se 1 (by rfl) ⟨84225095, by rfl⟩ : syracuseStep 112300127 = 168450191) B168450191
theorem B9736523 : Blo 566810 9736523 := bstep (se 1 (by rfl) ⟨7302392, by rfl⟩ : syracuseStep 9736523 = 14604785) B14604785
theorem B2167195 : Blo 566810 2167195 := bstep (se 1 (by rfl) ⟨1625396, by rfl⟩ : syracuseStep 2167195 = 3250793) B3250793
theorem B4330259 : Blo 566810 4330259 := bstep (se 1 (by rfl) ⟨3247694, by rfl⟩ : syracuseStep 4330259 = 6495389) B6495389
theorem B1282985 : Blo 566810 1282985 := bstep (se 2 (by rfl) ⟨481119, by rfl⟩ : syracuseStep 1282985 = 962239) B962239
theorem B1283579 : Blo 566810 1283579 := bstep (se 1 (by rfl) ⟨962684, by rfl⟩ : syracuseStep 1283579 = 1925369) B1925369
theorem B4331231 : Blo 566810 4331231 := bstep (se 1 (by rfl) ⟨3248423, by rfl⟩ : syracuseStep 4331231 = 6496847) B6496847
theorem B1283831 : Blo 566810 1283831 := bstep (se 1 (by rfl) ⟨962873, by rfl⟩ : syracuseStep 1283831 = 1925747) B1925747
theorem B4986845 : Blo 566810 4986845 := bstep (se 3 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 4986845 = 1870067) B1870067
theorem B7280765 : Blo 566810 7280765 := bstep (se 3 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 7280765 = 2730287) B2730287
theorem B6461855 : Blo 566810 6461855 := bstep (se 1 (by rfl) ⟨4846391, by rfl⟩ : syracuseStep 6461855 = 9692783) B9692783
theorem B2333225 : Blo 566810 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B957305 : Blo 566810 957305 := bstep (se 2 (by rfl) ⟨358989, by rfl⟩ : syracuseStep 957305 = 717979) B717979
theorem B957919 : Blo 566810 957919 := bstep (se 1 (by rfl) ⟨718439, by rfl⟩ : syracuseStep 957919 = 1436879) B1436879
theorem B958567 : Blo 566810 958567 := bstep (se 1 (by rfl) ⟨718925, by rfl⟩ : syracuseStep 958567 = 1437851) B1437851
theorem B1155215 : Blo 566810 1155215 := bstep (se 1 (by rfl) ⟨866411, by rfl⟩ : syracuseStep 1155215 = 1732823) B1732823
theorem B2302127 : Blo 566810 2302127 := bstep (se 1 (by rfl) ⟨1726595, by rfl⟩ : syracuseStep 2302127 = 3453191) B3453191
theorem B4923575 : Blo 566810 4923575 := bstep (se 1 (by rfl) ⟨3692681, by rfl⟩ : syracuseStep 4923575 = 7385363) B7385363
theorem B17801903 : Blo 566810 17801903 := bstep (se 1 (by rfl) ⟨13351427, by rfl⟩ : syracuseStep 17801903 = 26702855) B26702855
theorem B959323 : Blo 566810 959323 := bstep (se 1 (by rfl) ⟨719492, by rfl⟩ : syracuseStep 959323 = 1438985) B1438985
theorem B2434063 : Blo 566810 2434063 := bstep (se 1 (by rfl) ⟨1825547, by rfl⟩ : syracuseStep 2434063 = 3651095) B3651095
theorem B5448809 : Blo 566810 5448809 := bstep (se 2 (by rfl) ⟨2043303, by rfl⟩ : syracuseStep 5448809 = 4086607) B4086607
theorem B2729171 : Blo 566810 2729171 := bstep (se 1 (by rfl) ⟨2046878, by rfl⟩ : syracuseStep 2729171 = 4093757) B4093757
theorem B566939 : Blo 566810 566939 := bstep (se 1 (by rfl) ⟨425204, by rfl⟩ : syracuseStep 566939 = 850409) B850409
theorem B14591663 : Blo 566810 14591663 := bstep (se 1 (by rfl) ⟨10943747, by rfl⟩ : syracuseStep 14591663 = 21887495) B21887495
theorem B960295 : Blo 566810 960295 := bstep (se 1 (by rfl) ⟨720221, by rfl⟩ : syracuseStep 960295 = 1440443) B1440443
theorem B35137385 : Blo 566810 35137385 := bstep (se 2 (by rfl) ⟨13176519, by rfl⟩ : syracuseStep 35137385 = 26353039) B26353039
theorem B567199 : Blo 566810 567199 := bstep (se 1 (by rfl) ⟨425399, by rfl⟩ : syracuseStep 567199 = 850799) B850799
theorem B567359 : Blo 566810 567359 := bstep (se 1 (by rfl) ⟨425519, by rfl⟩ : syracuseStep 567359 = 851039) B851039
theorem B567399 : Blo 566810 567399 := bstep (se 1 (by rfl) ⟨425549, by rfl⟩ : syracuseStep 567399 = 851099) B851099
theorem B567503 : Blo 566810 567503 := bstep (se 1 (by rfl) ⟨425627, by rfl⟩ : syracuseStep 567503 = 851255) B851255
theorem B567623 : Blo 566810 567623 := bstep (se 1 (by rfl) ⟨425717, by rfl⟩ : syracuseStep 567623 = 851435) B851435
theorem B567759 : Blo 566810 567759 := bstep (se 1 (by rfl) ⟨425819, by rfl⟩ : syracuseStep 567759 = 851639) B851639
theorem B567899 : Blo 566810 567899 := bstep (se 1 (by rfl) ⟨425924, by rfl⟩ : syracuseStep 567899 = 851849) B851849
theorem B568063 : Blo 566810 568063 := bstep (se 1 (by rfl) ⟨426047, by rfl⟩ : syracuseStep 568063 = 852095) B852095
theorem B1616831 : Blo 566810 1616831 := bstep (se 1 (by rfl) ⟨1212623, by rfl⟩ : syracuseStep 1616831 = 2425247) B2425247
theorem B568255 : Blo 566810 568255 := bstep (se 1 (by rfl) ⟨426191, by rfl⟩ : syracuseStep 568255 = 852383) B852383
theorem B568431 : Blo 566810 568431 := bstep (se 1 (by rfl) ⟨426323, by rfl⟩ : syracuseStep 568431 = 852647) B852647
theorem B568511 : Blo 566810 568511 := bstep (se 1 (by rfl) ⟨426383, by rfl⟩ : syracuseStep 568511 = 852767) B852767
theorem B568527 : Blo 566810 568527 := bstep (se 1 (by rfl) ⟨426395, by rfl⟩ : syracuseStep 568527 = 852791) B852791
theorem B568647 : Blo 566810 568647 := bstep (se 1 (by rfl) ⟨426485, by rfl⟩ : syracuseStep 568647 = 852971) B852971
theorem B568987 : Blo 566810 568987 := bstep (se 1 (by rfl) ⟨426740, by rfl⟩ : syracuseStep 568987 = 853481) B853481
theorem B569247 : Blo 566810 569247 := bstep (se 1 (by rfl) ⟨426935, by rfl⟩ : syracuseStep 569247 = 853871) B853871
theorem B60764087 : Blo 566810 60764087 := bstep (se 1 (by rfl) ⟨45573065, by rfl⟩ : syracuseStep 60764087 = 91146131) B91146131
theorem B569371 : Blo 566810 569371 := bstep (se 1 (by rfl) ⟨427028, by rfl⟩ : syracuseStep 569371 = 854057) B854057
theorem B569391 : Blo 566810 569391 := bstep (se 1 (by rfl) ⟨427043, by rfl⟩ : syracuseStep 569391 = 854087) B854087
theorem B8171603 : Blo 566810 8171603 := bstep (se 1 (by rfl) ⟨6128702, by rfl⟩ : syracuseStep 8171603 = 12257405) B12257405
theorem B569511 : Blo 566810 569511 := bstep (se 1 (by rfl) ⟨427133, by rfl⟩ : syracuseStep 569511 = 854267) B854267
theorem B569647 : Blo 566810 569647 := bstep (se 1 (by rfl) ⟨427235, by rfl⟩ : syracuseStep 569647 = 854471) B854471
theorem B7778749 : Blo 566810 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B569791 : Blo 566810 569791 := bstep (se 1 (by rfl) ⟨427343, by rfl⟩ : syracuseStep 569791 = 854687) B854687
theorem B4108751 : Blo 566810 4108751 := bstep (se 1 (by rfl) ⟨3081563, by rfl⟩ : syracuseStep 4108751 = 6163127) B6163127
theorem B569823 : Blo 566810 569823 := bstep (se 1 (by rfl) ⟨427367, by rfl⟩ : syracuseStep 569823 = 854735) B854735
theorem B569887 : Blo 566810 569887 := bstep (se 1 (by rfl) ⟨427415, by rfl⟩ : syracuseStep 569887 = 854831) B854831
theorem B4928039 : Blo 566810 4928039 := bstep (se 1 (by rfl) ⟨3696029, by rfl⟩ : syracuseStep 4928039 = 7392059) B7392059
theorem B569967 : Blo 566810 569967 := bstep (se 1 (by rfl) ⟨427475, by rfl⟩ : syracuseStep 569967 = 854951) B854951
theorem B570087 : Blo 566810 570087 := bstep (se 1 (by rfl) ⟨427565, by rfl⟩ : syracuseStep 570087 = 855131) B855131
theorem B570139 : Blo 566810 570139 := bstep (se 1 (by rfl) ⟨427604, by rfl⟩ : syracuseStep 570139 = 855209) B855209
theorem B570415 : Blo 566810 570415 := bstep (se 1 (by rfl) ⟨427811, by rfl⟩ : syracuseStep 570415 = 855623) B855623
theorem B570535 : Blo 566810 570535 := bstep (se 1 (by rfl) ⟨427901, by rfl⟩ : syracuseStep 570535 = 855803) B855803
theorem B8729855 : Blo 566810 8729855 := bstep (se 1 (by rfl) ⟨6547391, by rfl⟩ : syracuseStep 8729855 = 13094783) B13094783
theorem B1914137 : Blo 566810 1914137 := bstep (se 2 (by rfl) ⟨717801, by rfl⟩ : syracuseStep 1914137 = 1435603) B1435603
theorem B570695 : Blo 566810 570695 := bstep (se 1 (by rfl) ⟨428021, by rfl⟩ : syracuseStep 570695 = 856043) B856043
theorem B1620157 : Blo 566810 1620157 := bstep (se 3 (by rfl) ⟨303779, by rfl⟩ : syracuseStep 1620157 = 607559) B607559
theorem B1817807 : Blo 566810 1817807 := bstep (se 1 (by rfl) ⟨1363355, by rfl⟩ : syracuseStep 1817807 = 2726711) B2726711
theorem B1621615 : Blo 566810 1621615 := bstep (se 1 (by rfl) ⟨1216211, by rfl⟩ : syracuseStep 1621615 = 2432423) B2432423
theorem B4112039 : Blo 566810 4112039 := bstep (se 1 (by rfl) ⟨3084029, by rfl⟩ : syracuseStep 4112039 = 6168059) B6168059
theorem B27737963 : Blo 566810 27737963 := bstep (se 1 (by rfl) ⟨20803472, by rfl⟩ : syracuseStep 27737963 = 41606945) B41606945
theorem B638959 : Blo 566810 638959 := bstep (se 1 (by rfl) ⟨479219, by rfl⟩ : syracuseStep 638959 = 958439) B958439
theorem B1917053 : Blo 566810 1917053 := bstep (se 3 (by rfl) ⟨359447, by rfl⟩ : syracuseStep 1917053 = 718895) B718895
theorem B2736287 : Blo 566810 2736287 := bstep (se 1 (by rfl) ⟨2052215, by rfl⟩ : syracuseStep 2736287 = 4104431) B4104431
theorem B1917161 : Blo 566810 1917161 := bstep (se 2 (by rfl) ⟨718935, by rfl⟩ : syracuseStep 1917161 = 1437871) B1437871
theorem B2048365 : Blo 566810 2048365 := bstep (se 3 (by rfl) ⟨384068, by rfl⟩ : syracuseStep 2048365 = 768137) B768137
theorem B6472061 : Blo 566810 6472061 := bstep (se 3 (by rfl) ⟨1213511, by rfl⟩ : syracuseStep 6472061 = 2427023) B2427023
theorem B3457417 : Blo 566810 3457417 := bstep (se 2 (by rfl) ⟨1296531, by rfl⟩ : syracuseStep 3457417 = 2593063) B2593063
theorem B639967 : Blo 566810 639967 := bstep (se 1 (by rfl) ⟨479975, by rfl⟩ : syracuseStep 639967 = 959951) B959951
theorem B2049185 : Blo 566810 2049185 := bstep (se 2 (by rfl) ⟨768444, by rfl⟩ : syracuseStep 2049185 = 1536889) B1536889
theorem B4310333 : Blo 566810 4310333 := bstep (se 3 (by rfl) ⟨808187, by rfl⟩ : syracuseStep 4310333 = 1616375) B1616375
theorem B1230313 : Blo 566810 1230313 := bstep (se 2 (by rfl) ⟨461367, by rfl⟩ : syracuseStep 1230313 = 922735) B922735
theorem B1362041 : Blo 566810 1362041 := bstep (se 2 (by rfl) ⟨510765, by rfl⟩ : syracuseStep 1362041 = 1021531) B1021531
theorem B1919159 : Blo 566810 1919159 := bstep (se 1 (by rfl) ⟨1439369, by rfl⟩ : syracuseStep 1919159 = 2878739) B2878739
theorem B1624475 : Blo 566810 1624475 := bstep (se 1 (by rfl) ⟨1218356, by rfl⟩ : syracuseStep 1624475 = 2436713) B2436713
theorem B2050685 : Blo 566810 2050685 := bstep (se 3 (by rfl) ⟨384503, by rfl⟩ : syracuseStep 2050685 = 769007) B769007
theorem B1919753 : Blo 566810 1919753 := bstep (se 2 (by rfl) ⟨719907, by rfl⟩ : syracuseStep 1919753 = 1439815) B1439815
theorem B2870639 : Blo 566810 2870639 := bstep (se 1 (by rfl) ⟨2152979, by rfl⟩ : syracuseStep 2870639 = 4305959) B4305959
theorem B3886973 : Blo 566810 3886973 := bstep (se 3 (by rfl) ⟨728807, by rfl⟩ : syracuseStep 3886973 = 1457615) B1457615
theorem B4313249 : Blo 566810 4313249 := bstep (se 2 (by rfl) ⟨1617468, by rfl⟩ : syracuseStep 4313249 = 3234937) B3234937
theorem B1921643 : Blo 566810 1921643 := bstep (se 1 (by rfl) ⟨1441232, by rfl⟩ : syracuseStep 1921643 = 2882465) B2882465
theorem B1168361 : Blo 566810 1168361 := bstep (se 2 (by rfl) ⟨438135, by rfl⟩ : syracuseStep 1168361 = 876271) B876271
theorem B2872745 : Blo 566810 2872745 := bstep (se 2 (by rfl) ⟨1077279, by rfl⟩ : syracuseStep 2872745 = 2154559) B2154559
theorem B41540971 : Blo 566810 41540971 := bstep (se 1 (by rfl) ⟨31155728, by rfl⟩ : syracuseStep 41540971 = 62311457) B62311457
theorem B1826651 : Blo 566810 1826651 := bstep (se 1 (by rfl) ⟨1369988, by rfl⟩ : syracuseStep 1826651 = 2739977) B2739977
theorem B14016979 : Blo 566810 14016979 := bstep (se 1 (by rfl) ⟨10512734, by rfl⟩ : syracuseStep 14016979 = 21025469) B21025469
theorem B1925639 : Blo 566810 1925639 := bstep (se 1 (by rfl) ⟨1444229, by rfl⟩ : syracuseStep 1925639 = 2888459) B2888459
theorem B27583037 : Blo 566810 27583037 := bstep (se 3 (by rfl) ⟨5171819, by rfl⟩ : syracuseStep 27583037 = 10343639) B10343639
theorem B4875065 : Blo 566810 4875065 := bstep (se 2 (by rfl) ⟨1828149, by rfl⟩ : syracuseStep 4875065 = 3656299) B3656299
theorem B2057159 : Blo 566810 2057159 := bstep (se 1 (by rfl) ⟨1542869, by rfl⟩ : syracuseStep 2057159 = 3085739) B3085739
theorem B1435279 : Blo 566810 1435279 := bstep (se 1 (by rfl) ⟨1076459, by rfl⟩ : syracuseStep 1435279 = 2152919) B2152919
theorem B2156503 : Blo 566810 2156503 := bstep (se 1 (by rfl) ⟨1617377, by rfl⟩ : syracuseStep 2156503 = 3234755) B3234755
theorem B4089953 : Blo 566810 4089953 := bstep (se 2 (by rfl) ⟨1533732, by rfl⟩ : syracuseStep 4089953 = 3067465) B3067465
theorem B52553843 : Blo 566810 52553843 := bstep (se 1 (by rfl) ⟨39415382, by rfl⟩ : syracuseStep 52553843 = 78830765) B78830765
theorem B8218883 : Blo 566810 8218883 := bstep (se 1 (by rfl) ⟨6164162, by rfl⟩ : syracuseStep 8218883 = 12328325) B12328325
theorem B5466953 : Blo 566810 5466953 := bstep (se 2 (by rfl) ⟨2050107, by rfl⟩ : syracuseStep 5466953 = 4100215) B4100215
theorem B2191579 : Blo 566810 2191579 := bstep (se 1 (by rfl) ⟨1643684, by rfl⟩ : syracuseStep 2191579 = 3287369) B3287369
theorem B2159207 : Blo 566810 2159207 := bstep (se 1 (by rfl) ⟨1619405, by rfl⟩ : syracuseStep 2159207 = 3238811) B3238811
theorem B914107 : Blo 566810 914107 := bstep (se 1 (by rfl) ⟨685580, by rfl⟩ : syracuseStep 914107 = 1371161) B1371161
theorem B717599 : Blo 566810 717599 := bstep (se 1 (by rfl) ⟨538199, by rfl⟩ : syracuseStep 717599 = 1076399) B1076399
theorem B7304033 : Blo 566810 7304033 := bstep (se 2 (by rfl) ⟨2739012, by rfl⟩ : syracuseStep 7304033 = 5478025) B5478025
theorem B14054573 : Blo 566810 14054573 := bstep (se 3 (by rfl) ⟨2635232, by rfl⟩ : syracuseStep 14054573 = 5270465) B5270465
theorem B1438955 : Blo 566810 1438955 := bstep (se 1 (by rfl) ⟨1079216, by rfl⟩ : syracuseStep 1438955 = 2158433) B2158433
theorem B718303 : Blo 566810 718303 := bstep (se 1 (by rfl) ⟨538727, by rfl⟩ : syracuseStep 718303 = 1077455) B1077455
theorem B4322969 : Blo 566810 4322969 := bstep (se 2 (by rfl) ⟨1621113, by rfl⟩ : syracuseStep 4322969 = 3242227) B3242227
theorem B2160695 : Blo 566810 2160695 := bstep (se 1 (by rfl) ⟨1620521, by rfl⟩ : syracuseStep 2160695 = 3241043) B3241043
theorem B718951 : Blo 566810 718951 := bstep (se 1 (by rfl) ⟨539213, by rfl⟩ : syracuseStep 718951 = 1078427) B1078427
theorem B2455705 : Blo 566810 2455705 := bstep (se 2 (by rfl) ⟨920889, by rfl⟩ : syracuseStep 2455705 = 1841779) B1841779
theorem B1276073 : Blo 566810 1276073 := bstep (se 2 (by rfl) ⟨478527, by rfl⟩ : syracuseStep 1276073 = 957055) B957055
theorem B7272665 : Blo 566810 7272665 := bstep (se 2 (by rfl) ⟨2727249, by rfl⟩ : syracuseStep 7272665 = 5454499) B5454499
theorem B1276217 : Blo 566810 1276217 := bstep (se 2 (by rfl) ⟨478581, by rfl⟩ : syracuseStep 1276217 = 957163) B957163
theorem B1210727 : Blo 566810 1210727 := bstep (se 1 (by rfl) ⟨908045, by rfl⟩ : syracuseStep 1210727 = 1816091) B1816091
theorem B1276577 : Blo 566810 1276577 := bstep (se 2 (by rfl) ⟨478716, by rfl⟩ : syracuseStep 1276577 = 957433) B957433
theorem B3635873 : Blo 566810 3635873 := bstep (se 2 (by rfl) ⟨1363452, by rfl⟩ : syracuseStep 3635873 = 2726905) B2726905
theorem B1080287 : Blo 566810 1080287 := bstep (se 1 (by rfl) ⟨810215, by rfl⟩ : syracuseStep 1080287 = 1620431) B1620431
theorem B719867 : Blo 566810 719867 := bstep (se 1 (by rfl) ⟨539900, by rfl⟩ : syracuseStep 719867 = 1079801) B1079801
theorem B1276937 : Blo 566810 1276937 := bstep (se 2 (by rfl) ⟨478851, by rfl⟩ : syracuseStep 1276937 = 957703) B957703
theorem B2456659 : Blo 566810 2456659 := bstep (se 1 (by rfl) ⟨1842494, by rfl⟩ : syracuseStep 2456659 = 3684989) B3684989
theorem B4324913 : Blo 566810 4324913 := bstep (se 2 (by rfl) ⟨1621842, by rfl⟩ : syracuseStep 4324913 = 3243685) B3243685
theorem B851615 : Blo 566810 851615 := bstep (se 1 (by rfl) ⟨638711, by rfl⟩ : syracuseStep 851615 = 1277423) B1277423
theorem B2162335 : Blo 566810 2162335 := bstep (se 1 (by rfl) ⟨1621751, by rfl⟩ : syracuseStep 2162335 = 3243503) B3243503
theorem B2162639 : Blo 566810 2162639 := bstep (se 1 (by rfl) ⟨1621979, by rfl⟩ : syracuseStep 2162639 = 3243959) B3243959
theorem B1277945 : Blo 566810 1277945 := bstep (se 2 (by rfl) ⟨479229, by rfl⟩ : syracuseStep 1277945 = 958459) B958459
theorem B1278035 : Blo 566810 1278035 := bstep (se 1 (by rfl) ⟨958526, by rfl⟩ : syracuseStep 1278035 = 1917053) B1917053
theorem B720991 : Blo 566810 720991 := bstep (se 1 (by rfl) ⟨540743, by rfl⟩ : syracuseStep 720991 = 1081487) B1081487
theorem B1278089 : Blo 566810 1278089 := bstep (se 2 (by rfl) ⟨479283, by rfl⟩ : syracuseStep 1278089 = 958567) B958567
theorem B1278107 : Blo 566810 1278107 := bstep (se 1 (by rfl) ⟨958580, by rfl⟩ : syracuseStep 1278107 = 1917161) B1917161
theorem B852347 : Blo 566810 852347 := bstep (se 1 (by rfl) ⟨639260, by rfl⟩ : syracuseStep 852347 = 1278521) B1278521
theorem B2490895 : Blo 566810 2490895 := bstep (se 1 (by rfl) ⟨1868171, by rfl⟩ : syracuseStep 2490895 = 3736343) B3736343
theorem B852827 : Blo 566810 852827 := bstep (se 1 (by rfl) ⟨639620, by rfl⟩ : syracuseStep 852827 = 1279241) B1279241
theorem B1279097 : Blo 566810 1279097 := bstep (se 2 (by rfl) ⟨479661, by rfl⟩ : syracuseStep 1279097 = 959323) B959323
theorem B853289 : Blo 566810 853289 := bstep (se 2 (by rfl) ⟨319983, by rfl⟩ : syracuseStep 853289 = 639967) B639967
theorem B3245417 : Blo 566810 3245417 := bstep (se 2 (by rfl) ⟨1217031, by rfl⟩ : syracuseStep 3245417 = 2434063) B2434063
theorem B1279439 : Blo 566810 1279439 := bstep (se 1 (by rfl) ⟨959579, by rfl⟩ : syracuseStep 1279439 = 1919159) B1919159
theorem B1082983 : Blo 566810 1082983 := bstep (se 1 (by rfl) ⟨812237, by rfl⟩ : syracuseStep 1082983 = 1624475) B1624475
theorem B1279835 : Blo 566810 1279835 := bstep (se 1 (by rfl) ⟨959876, by rfl⟩ : syracuseStep 1279835 = 1919753) B1919753
theorem B1640417 : Blo 566810 1640417 := bstep (se 2 (by rfl) ⟨615156, by rfl⟩ : syracuseStep 1640417 = 1230313) B1230313
theorem B854327 : Blo 566810 854327 := bstep (se 1 (by rfl) ⟨640745, by rfl⟩ : syracuseStep 854327 = 1281491) B1281491
theorem B1280393 : Blo 566810 1280393 := bstep (se 2 (by rfl) ⟨480147, by rfl⟩ : syracuseStep 1280393 = 960295) B960295
theorem B2591315 : Blo 566810 2591315 := bstep (se 1 (by rfl) ⟨1943486, by rfl⟩ : syracuseStep 2591315 = 3886973) B3886973
theorem B854639 : Blo 566810 854639 := bstep (se 1 (by rfl) ⟨640979, by rfl⟩ : syracuseStep 854639 = 1281959) B1281959
theorem B6163087 : Blo 566810 6163087 := bstep (se 1 (by rfl) ⟨4622315, by rfl⟩ : syracuseStep 6163087 = 9244631) B9244631
theorem B6491015 : Blo 566810 6491015 := bstep (se 1 (by rfl) ⟨4868261, by rfl⟩ : syracuseStep 6491015 = 9736523) B9736523
theorem B1281095 : Blo 566810 1281095 := bstep (se 1 (by rfl) ⟨960821, by rfl⟩ : syracuseStep 1281095 = 1921643) B1921643
theorem B27626629 : Blo 566810 27626629 := bstep (se 4 (by rfl) ⟨2589996, by rfl⟩ : syracuseStep 27626629 = 5179993) B5179993
theorem B2886839 : Blo 566810 2886839 := bstep (se 1 (by rfl) ⟨2165129, by rfl⟩ : syracuseStep 2886839 = 4330259) B4330259
theorem B7277789 : Blo 566810 7277789 := bstep (se 3 (by rfl) ⟨1364585, by rfl⟩ : syracuseStep 7277789 = 2729171) B2729171
theorem B855323 : Blo 566810 855323 := bstep (se 1 (by rfl) ⟨641492, by rfl⟩ : syracuseStep 855323 = 1282985) B1282985
theorem B855719 : Blo 566810 855719 := bstep (se 1 (by rfl) ⟨641789, by rfl⟩ : syracuseStep 855719 = 1283579) B1283579
theorem B2887487 : Blo 566810 2887487 := bstep (se 1 (by rfl) ⟨2165615, by rfl⟩ : syracuseStep 2887487 = 4331231) B4331231
theorem B855887 : Blo 566810 855887 := bstep (se 1 (by rfl) ⟨641915, by rfl⟩ : syracuseStep 855887 = 1283831) B1283831
theorem B4853843 : Blo 566810 4853843 := bstep (se 1 (by rfl) ⟨3640382, by rfl⟩ : syracuseStep 4853843 = 7280765) B7280765
theorem B2888297 : Blo 566810 2888297 := bstep (se 2 (by rfl) ⟨1083111, by rfl⟩ : syracuseStep 2888297 = 2166223) B2166223
theorem B1217767 : Blo 566810 1217767 := bstep (se 1 (by rfl) ⟨913325, by rfl⟩ : syracuseStep 1217767 = 1826651) B1826651
theorem B3282383 : Blo 566810 3282383 := bstep (se 1 (by rfl) ⟨2461787, by rfl⟩ : syracuseStep 3282383 = 4923575) B4923575
theorem B1283759 : Blo 566810 1283759 := bstep (se 1 (by rfl) ⟨962819, by rfl⟩ : syracuseStep 1283759 = 1925639) B1925639
theorem B18388691 : Blo 566810 18388691 := bstep (se 1 (by rfl) ⟨13791518, by rfl⟩ : syracuseStep 18388691 = 27583037) B27583037
theorem B2889593 : Blo 566810 2889593 := bstep (se 2 (by rfl) ⟨1083597, by rfl⟩ : syracuseStep 2889593 = 2167195) B2167195
theorem B3250043 : Blo 566810 3250043 := bstep (se 1 (by rfl) ⟨2437532, by rfl⟩ : syracuseStep 3250043 = 4875065) B4875065
theorem B1218809 : Blo 566810 1218809 := bstep (se 2 (by rfl) ⟨457053, by rfl⟩ : syracuseStep 1218809 = 914107) B914107
theorem B2726635 : Blo 566810 2726635 := bstep (se 1 (by rfl) ⟨2044976, by rfl⟩ : syracuseStep 2726635 = 4089953) B4089953
theorem B35035895 : Blo 566810 35035895 := bstep (se 1 (by rfl) ⟨26276921, by rfl⟩ : syracuseStep 35035895 = 52553843) B52553843
theorem B5479255 : Blo 566810 5479255 := bstep (se 1 (by rfl) ⟨4109441, by rfl⟩ : syracuseStep 5479255 = 8218883) B8218883
theorem B957737 : Blo 566810 957737 := bstep (se 2 (by rfl) ⟨359151, by rfl⟩ : syracuseStep 957737 = 718303) B718303
theorem B40509391 : Blo 566810 40509391 := bstep (se 1 (by rfl) ⟨30382043, by rfl⟩ : syracuseStep 40509391 = 60764087) B60764087
theorem B5447735 : Blo 566810 5447735 := bstep (se 1 (by rfl) ⟨4085801, by rfl⟩ : syracuseStep 5447735 = 8171603) B8171603
theorem B958601 : Blo 566810 958601 := bstep (se 2 (by rfl) ⟨359475, by rfl⟩ : syracuseStep 958601 = 718951) B718951
theorem B3285359 : Blo 566810 3285359 := bstep (se 1 (by rfl) ⟨2464019, by rfl⟩ : syracuseStep 3285359 = 4928039) B4928039
theorem B959303 : Blo 566810 959303 := bstep (se 1 (by rfl) ⟨719477, by rfl⟩ : syracuseStep 959303 = 1438955) B1438955
theorem B55387961 : Blo 566810 55387961 := bstep (se 2 (by rfl) ⟨20770485, by rfl⟩ : syracuseStep 55387961 = 41540971) B41540971
theorem B567743 : Blo 566810 567743 := bstep (se 1 (by rfl) ⟨425807, by rfl⟩ : syracuseStep 567743 = 851615) B851615
theorem B18491975 : Blo 566810 18491975 := bstep (se 1 (by rfl) ⟨13868981, by rfl⟩ : syracuseStep 18491975 = 27737963) B27737963
theorem B568351 : Blo 566810 568351 := bstep (se 1 (by rfl) ⟨426263, by rfl⟩ : syracuseStep 568351 = 852527) B852527
theorem B568411 : Blo 566810 568411 := bstep (se 1 (by rfl) ⟨426308, by rfl⟩ : syracuseStep 568411 = 852617) B852617
theorem B2731153 : Blo 566810 2731153 := bstep (se 2 (by rfl) ⟨1024182, by rfl⟩ : syracuseStep 2731153 = 2048365) B2048365
theorem B18689305 : Blo 566810 18689305 := bstep (se 2 (by rfl) ⟨7008489, by rfl⟩ : syracuseStep 18689305 = 14016979) B14016979
theorem B568767 : Blo 566810 568767 := bstep (se 1 (by rfl) ⟨426575, by rfl⟩ : syracuseStep 568767 = 853151) B853151
theorem B568879 : Blo 566810 568879 := bstep (se 1 (by rfl) ⟨426659, by rfl⟩ : syracuseStep 568879 = 853319) B853319
theorem B569179 : Blo 566810 569179 := bstep (se 1 (by rfl) ⟨426884, by rfl⟩ : syracuseStep 569179 = 853769) B853769
theorem B962543 : Blo 566810 962543 := bstep (se 1 (by rfl) ⟨721907, by rfl⟩ : syracuseStep 962543 = 1443815) B1443815
theorem B962887 : Blo 566810 962887 := bstep (se 1 (by rfl) ⟨722165, by rfl⟩ : syracuseStep 962887 = 1444331) B1444331
theorem B2732383 : Blo 566810 2732383 := bstep (se 1 (by rfl) ⟨2049287, by rfl⟩ : syracuseStep 2732383 = 4098575) B4098575
theorem B963103 : Blo 566810 963103 := bstep (se 1 (by rfl) ⟨722327, by rfl⟩ : syracuseStep 963103 = 1444655) B1444655
theorem B569903 : Blo 566810 569903 := bstep (se 1 (by rfl) ⟨427427, by rfl⟩ : syracuseStep 569903 = 854855) B854855
theorem B570047 : Blo 566810 570047 := bstep (se 1 (by rfl) ⟨427535, by rfl⟩ : syracuseStep 570047 = 855071) B855071
theorem B1913597 : Blo 566810 1913597 := bstep (se 3 (by rfl) ⟨358799, by rfl⟩ : syracuseStep 1913597 = 717599) B717599
theorem B1913705 : Blo 566810 1913705 := bstep (se 2 (by rfl) ⟨717639, by rfl⟩ : syracuseStep 1913705 = 1435279) B1435279
theorem B1913759 : Blo 566810 1913759 := bstep (se 1 (by rfl) ⟨1435319, by rfl⟩ : syracuseStep 1913759 = 2870639) B2870639
theorem B570303 : Blo 566810 570303 := bstep (se 1 (by rfl) ⟨427727, by rfl⟩ : syracuseStep 570303 = 855455) B855455
theorem B570335 : Blo 566810 570335 := bstep (se 1 (by rfl) ⟨427751, by rfl⟩ : syracuseStep 570335 = 855503) B855503
theorem B1915163 : Blo 566810 1915163 := bstep (se 1 (by rfl) ⟨1436372, by rfl⟩ : syracuseStep 1915163 = 2872745) B2872745
theorem B3324563 : Blo 566810 3324563 := bstep (se 1 (by rfl) ⟨2493422, by rfl⟩ : syracuseStep 3324563 = 4986845) B4986845
theorem B4307903 : Blo 566810 4307903 := bstep (se 1 (by rfl) ⟨3230927, by rfl⟩ : syracuseStep 4307903 = 6461855) B6461855
theorem B638203 : Blo 566810 638203 := bstep (se 1 (by rfl) ⟨478652, by rfl⟩ : syracuseStep 638203 = 957305) B957305
theorem B770143 : Blo 566810 770143 := bstep (se 1 (by rfl) ⟨577607, by rfl⟩ : syracuseStep 770143 = 1155215) B1155215
theorem B10371665 : Blo 566810 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B3228605 : Blo 566810 3228605 := bstep (se 3 (by rfl) ⟨605363, by rfl⟩ : syracuseStep 3228605 = 1210727) B1210727
theorem B1919645 : Blo 566810 1919645 := bstep (se 3 (by rfl) ⟨359933, by rfl⟩ : syracuseStep 1919645 = 719867) B719867
theorem B2739167 : Blo 566810 2739167 := bstep (se 1 (by rfl) ⟨2054375, by rfl⟩ : syracuseStep 2739167 = 4108751) B4108751
theorem B4869355 : Blo 566810 4869355 := bstep (se 1 (by rfl) ⟨3652016, by rfl⟩ : syracuseStep 4869355 = 7304033) B7304033
theorem B5819903 : Blo 566810 5819903 := bstep (se 1 (by rfl) ⟨4364927, by rfl⟩ : syracuseStep 5819903 = 8729855) B8729855
theorem B2741359 : Blo 566810 2741359 := bstep (se 1 (by rfl) ⟨2056019, by rfl⟩ : syracuseStep 2741359 = 4112039) B4112039
theorem B1824191 : Blo 566810 1824191 := bstep (se 1 (by rfl) ⟨1368143, by rfl⟩ : syracuseStep 1824191 = 2736287) B2736287
theorem B1922615 : Blo 566810 1922615 := bstep (se 1 (by rfl) ⟨1441961, by rfl⟩ : syracuseStep 1922615 = 2883923) B2883923
theorem B4314707 : Blo 566810 4314707 := bstep (se 1 (by rfl) ⟨3236030, by rfl⟩ : syracuseStep 4314707 = 6472061) B6472061
theorem B4609889 : Blo 566810 4609889 := bstep (se 2 (by rfl) ⟨1728708, by rfl⟩ : syracuseStep 4609889 = 3457417) B3457417
theorem B2873555 : Blo 566810 2873555 := bstep (se 1 (by rfl) ⟨2155166, by rfl⟩ : syracuseStep 2873555 = 4310333) B4310333
theorem B11688421 : Blo 566810 11688421 := bstep (se 4 (by rfl) ⟨1095789, by rfl⟩ : syracuseStep 11688421 = 2191579) B2191579
theorem B908027 : Blo 566810 908027 := bstep (se 1 (by rfl) ⟨681020, by rfl⟩ : syracuseStep 908027 = 1362041) B1362041
theorem B1367123 : Blo 566810 1367123 := bstep (se 1 (by rfl) ⟨1025342, by rfl⟩ : syracuseStep 1367123 = 2050685) B2050685
theorem B47471741 : Blo 566810 47471741 := bstep (se 3 (by rfl) ⟨8900951, by rfl⟩ : syracuseStep 47471741 = 17801903) B17801903
theorem B3235463 : Blo 566810 3235463 := bstep (se 1 (by rfl) ⟨2426597, by rfl⟩ : syracuseStep 3235463 = 4853195) B4853195
theorem B2056105 : Blo 566810 2056105 := bstep (se 2 (by rfl) ⟨771039, by rfl⟩ : syracuseStep 2056105 = 1542079) B1542079
theorem B2875337 : Blo 566810 2875337 := bstep (se 2 (by rfl) ⟨1078251, by rfl⟩ : syracuseStep 2875337 = 2156503) B2156503
theorem B74866751 : Blo 566810 74866751 := bstep (se 1 (by rfl) ⟨56150063, by rfl⟩ : syracuseStep 74866751 = 112300127) B112300127
theorem B21848129 : Blo 566810 21848129 := bstep (se 2 (by rfl) ⟨8193048, by rfl⟩ : syracuseStep 21848129 = 16386097) B16386097
theorem B2875499 : Blo 566810 2875499 := bstep (se 1 (by rfl) ⟨2156624, by rfl⟩ : syracuseStep 2875499 = 4313249) B4313249
theorem B5464493 : Blo 566810 5464493 := bstep (se 3 (by rfl) ⟨1024592, by rfl⟩ : syracuseStep 5464493 = 2049185) B2049185
theorem B37478861 : Blo 566810 37478861 := bstep (se 3 (by rfl) ⟨7027286, by rfl⟩ : syracuseStep 37478861 = 14054573) B14054573
theorem B778907 : Blo 566810 778907 := bstep (se 1 (by rfl) ⟨584180, by rfl⟩ : syracuseStep 778907 = 1168361) B1168361
theorem B1534751 : Blo 566810 1534751 := bstep (se 1 (by rfl) ⟨1151063, by rfl⟩ : syracuseStep 1534751 = 2302127) B2302127
theorem B13102181 : Blo 566810 13102181 := bstep (se 4 (by rfl) ⟨1228329, by rfl⟩ : syracuseStep 13102181 = 2456659) B2456659
theorem B1371439 : Blo 566810 1371439 := bstep (se 1 (by rfl) ⟨1028579, by rfl⟩ : syracuseStep 1371439 = 2057159) B2057159
theorem B3632539 : Blo 566810 3632539 := bstep (se 1 (by rfl) ⟨2724404, by rfl⟩ : syracuseStep 3632539 = 5448809) B5448809
theorem B9727775 : Blo 566810 9727775 := bstep (se 1 (by rfl) ⟨7295831, by rfl⟩ : syracuseStep 9727775 = 14591663) B14591663
theorem B23424923 : Blo 566810 23424923 := bstep (se 1 (by rfl) ⟨17568692, by rfl⟩ : syracuseStep 23424923 = 35137385) B35137385
theorem B6221933 : Blo 566810 6221933 := bstep (se 3 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 6221933 = 2333225) B2333225
theorem B1077887 : Blo 566810 1077887 := bstep (se 1 (by rfl) ⟨808415, by rfl⟩ : syracuseStep 1077887 = 1616831) B1616831
theorem B14578541 : Blo 566810 14578541 := bstep (se 3 (by rfl) ⟨2733476, by rfl⟩ : syracuseStep 14578541 = 5466953) B5466953
theorem B3274273 : Blo 566810 3274273 := bstep (se 2 (by rfl) ⟨1227852, by rfl⟩ : syracuseStep 3274273 = 2455705) B2455705
theorem B2160209 : Blo 566810 2160209 := bstep (se 2 (by rfl) ⟨810078, by rfl⟩ : syracuseStep 2160209 = 1620157) B1620157
theorem B1439471 : Blo 566810 1439471 := bstep (se 1 (by rfl) ⟨1079603, by rfl⟩ : syracuseStep 1439471 = 2159207) B2159207
theorem B4847485 : Blo 566810 4847485 := bstep (se 3 (by rfl) ⟨908903, by rfl⟩ : syracuseStep 4847485 = 1817807) B1817807
theorem B1276091 : Blo 566810 1276091 := bstep (se 1 (by rfl) ⟨957068, by rfl⟩ : syracuseStep 1276091 = 1914137) B1914137
theorem B2881979 : Blo 566810 2881979 := bstep (se 1 (by rfl) ⟨2161484, by rfl⟩ : syracuseStep 2881979 = 4322969) B4322969
theorem B1440463 : Blo 566810 1440463 := bstep (se 1 (by rfl) ⟨1080347, by rfl⟩ : syracuseStep 1440463 = 2160695) B2160695
theorem B850715 : Blo 566810 850715 := bstep (se 1 (by rfl) ⟨638036, by rfl⟩ : syracuseStep 850715 = 1276073) B1276073
theorem B4848443 : Blo 566810 4848443 := bstep (se 1 (by rfl) ⟨3636332, by rfl⟩ : syracuseStep 4848443 = 7272665) B7272665
theorem B850811 : Blo 566810 850811 := bstep (se 1 (by rfl) ⟨638108, by rfl⟩ : syracuseStep 850811 = 1276217) B1276217
theorem B851051 : Blo 566810 851051 := bstep (se 1 (by rfl) ⟨638288, by rfl⟩ : syracuseStep 851051 = 1276577) B1276577
theorem B2423915 : Blo 566810 2423915 := bstep (se 1 (by rfl) ⟨1817936, by rfl⟩ : syracuseStep 2423915 = 3635873) B3635873
theorem B1277225 : Blo 566810 1277225 := bstep (se 2 (by rfl) ⟨478959, by rfl⟩ : syracuseStep 1277225 = 957919) B957919
theorem B720191 : Blo 566810 720191 := bstep (se 1 (by rfl) ⟨540143, by rfl⟩ : syracuseStep 720191 = 1080287) B1080287
theorem B851291 : Blo 566810 851291 := bstep (se 1 (by rfl) ⟨638468, by rfl⟩ : syracuseStep 851291 = 1276937) B1276937
theorem B2162153 : Blo 566810 2162153 := bstep (se 2 (by rfl) ⟨810807, by rfl⟩ : syracuseStep 2162153 = 1621615) B1621615
theorem B2883113 : Blo 566810 2883113 := bstep (se 2 (by rfl) ⟨1081167, by rfl⟩ : syracuseStep 2883113 = 2162335) B2162335
theorem B2883275 : Blo 566810 2883275 := bstep (se 1 (by rfl) ⟨2162456, by rfl⟩ : syracuseStep 2883275 = 4324913) B4324913
theorem B1441759 : Blo 566810 1441759 := bstep (se 1 (by rfl) ⟨1081319, by rfl⟩ : syracuseStep 1441759 = 2162639) B2162639
theorem B851945 : Blo 566810 851945 := bstep (se 2 (by rfl) ⟨319479, by rfl⟩ : syracuseStep 851945 = 638959) B638959
theorem B851963 : Blo 566810 851963 := bstep (se 1 (by rfl) ⟨638972, by rfl⟩ : syracuseStep 851963 = 1277945) B1277945
theorem B852023 : Blo 566810 852023 := bstep (se 1 (by rfl) ⟨639017, by rfl⟩ : syracuseStep 852023 = 1278035) B1278035
theorem B852059 : Blo 566810 852059 := bstep (se 1 (by rfl) ⟨639044, by rfl⟩ : syracuseStep 852059 = 1278089) B1278089
theorem B852071 : Blo 566810 852071 := bstep (se 1 (by rfl) ⟨639053, by rfl⟩ : syracuseStep 852071 = 1278107) B1278107
theorem B852731 : Blo 566810 852731 := bstep (se 1 (by rfl) ⟨639548, by rfl⟩ : syracuseStep 852731 = 1279097) B1279097
theorem B2163611 : Blo 566810 2163611 := bstep (se 1 (by rfl) ⟨1622708, by rfl⟩ : syracuseStep 2163611 = 3245417) B3245417
theorem B852959 : Blo 566810 852959 := bstep (se 1 (by rfl) ⟨639719, by rfl⟩ : syracuseStep 852959 = 1279439) B1279439
theorem B853223 : Blo 566810 853223 := bstep (se 1 (by rfl) ⟨639917, by rfl⟩ : syracuseStep 853223 = 1279835) B1279835
theorem B27657773 : Blo 566810 27657773 := bstep (se 3 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 27657773 = 10371665) B10371665
theorem B853595 : Blo 566810 853595 := bstep (se 1 (by rfl) ⟨640196, by rfl⟩ : syracuseStep 853595 = 1280393) B1280393
theorem B1279763 : Blo 566810 1279763 := bstep (se 1 (by rfl) ⟨959822, by rfl⟩ : syracuseStep 1279763 = 1919645) B1919645
theorem B4327343 : Blo 566810 4327343 := bstep (se 1 (by rfl) ⟨3245507, by rfl⟩ : syracuseStep 4327343 = 6491015) B6491015
theorem B854063 : Blo 566810 854063 := bstep (se 1 (by rfl) ⟨640547, by rfl⟩ : syracuseStep 854063 = 1281095) B1281095
theorem B1443977 : Blo 566810 1443977 := bstep (se 2 (by rfl) ⟨541491, by rfl⟩ : syracuseStep 1443977 = 1082983) B1082983
theorem B4851859 : Blo 566810 4851859 := bstep (se 1 (by rfl) ⟨3638894, by rfl⟩ : syracuseStep 4851859 = 7277789) B7277789
theorem B1216127 : Blo 566810 1216127 := bstep (se 1 (by rfl) ⟨912095, by rfl⟩ : syracuseStep 1216127 = 1824191) B1824191
theorem B1281743 : Blo 566810 1281743 := bstep (se 1 (by rfl) ⟨961307, by rfl⟩ : syracuseStep 1281743 = 1922615) B1922615
theorem B855839 : Blo 566810 855839 := bstep (se 1 (by rfl) ⟨641879, by rfl⟩ : syracuseStep 855839 = 1283759) B1283759
theorem B12259127 : Blo 566810 12259127 := bstep (se 1 (by rfl) ⟨9194345, by rfl⟩ : syracuseStep 12259127 = 18388691) B18388691
theorem B2166695 : Blo 566810 2166695 := bstep (se 1 (by rfl) ⟨1625021, by rfl⟩ : syracuseStep 2166695 = 3250043) B3250043
theorem B36835505 : Blo 566810 36835505 := bstep (se 2 (by rfl) ⟨13813314, by rfl⟩ : syracuseStep 36835505 = 27626629) B27626629
theorem B3641537 : Blo 566810 3641537 := bstep (se 2 (by rfl) ⟨1365576, by rfl⟩ : syracuseStep 3641537 = 2731153) B2731153
theorem B6492473 : Blo 566810 6492473 := bstep (se 2 (by rfl) ⟨2434677, by rfl⟩ : syracuseStep 6492473 = 4869355) B4869355
theorem B49911167 : Blo 566810 49911167 := bstep (se 1 (by rfl) ⟨37433375, by rfl⟩ : syracuseStep 49911167 = 74866751) B74866751
theorem B3642995 : Blo 566810 3642995 := bstep (se 1 (by rfl) ⟨2732246, by rfl⟩ : syracuseStep 3642995 = 5464493) B5464493
theorem B1283849 : Blo 566810 1283849 := bstep (se 2 (by rfl) ⟨481443, by rfl⟩ : syracuseStep 1283849 = 962887) B962887
theorem B3643177 : Blo 566810 3643177 := bstep (se 2 (by rfl) ⟨1366191, by rfl⟩ : syracuseStep 3643177 = 2732383) B2732383
theorem B1284137 : Blo 566810 1284137 := bstep (se 2 (by rfl) ⟨481551, by rfl⟩ : syracuseStep 1284137 = 963103) B963103
theorem B12327983 : Blo 566810 12327983 := bstep (se 1 (by rfl) ⟨9245987, by rfl⟩ : syracuseStep 12327983 = 18491975) B18491975
theorem B1023167 : Blo 566810 1023167 := bstep (se 1 (by rfl) ⟨767375, by rfl⟩ : syracuseStep 1023167 = 1534751) B1534751
theorem B4365697 : Blo 566810 4365697 := bstep (se 2 (by rfl) ⟨1637136, by rfl⟩ : syracuseStep 4365697 = 3274273) B3274273
theorem B6463313 : Blo 566810 6463313 := bstep (se 2 (by rfl) ⟨2423742, by rfl⟩ : syracuseStep 6463313 = 4847485) B4847485
theorem B3645661 : Blo 566810 3645661 := bstep (se 3 (by rfl) ⟨683561, by rfl⟩ : syracuseStep 3645661 = 1367123) B1367123
theorem B959647 : Blo 566810 959647 := bstep (se 1 (by rfl) ⟨719735, by rfl⟩ : syracuseStep 959647 = 1439471) B1439471
theorem B567143 : Blo 566810 567143 := bstep (se 1 (by rfl) ⟨425357, by rfl⟩ : syracuseStep 567143 = 850715) B850715
theorem B567207 : Blo 566810 567207 := bstep (se 1 (by rfl) ⟨425405, by rfl⟩ : syracuseStep 567207 = 850811) B850811
theorem B567367 : Blo 566810 567367 := bstep (se 1 (by rfl) ⟨425525, by rfl⟩ : syracuseStep 567367 = 851051) B851051
theorem B1615943 : Blo 566810 1615943 := bstep (se 1 (by rfl) ⟨1211957, by rfl⟩ : syracuseStep 1615943 = 2423915) B2423915
theorem B567527 : Blo 566810 567527 := bstep (se 1 (by rfl) ⟨425645, by rfl⟩ : syracuseStep 567527 = 851291) B851291
theorem B62466461 : Blo 566810 62466461 := bstep (se 3 (by rfl) ⟨11712461, by rfl⟩ : syracuseStep 62466461 = 23424923) B23424923
theorem B54012521 : Blo 566810 54012521 := bstep (se 2 (by rfl) ⟨20254695, by rfl⟩ : syracuseStep 54012521 = 40509391) B40509391
theorem B567963 : Blo 566810 567963 := bstep (se 1 (by rfl) ⟨425972, by rfl⟩ : syracuseStep 567963 = 851945) B851945
theorem B567975 : Blo 566810 567975 := bstep (se 1 (by rfl) ⟨425981, by rfl⟩ : syracuseStep 567975 = 851963) B851963
theorem B961321 : Blo 566810 961321 := bstep (se 2 (by rfl) ⟨360495, by rfl⟩ : syracuseStep 961321 = 720991) B720991
theorem B1026857 : Blo 566810 1026857 := bstep (se 2 (by rfl) ⟨385071, by rfl⟩ : syracuseStep 1026857 = 770143) B770143
theorem B568231 : Blo 566810 568231 := bstep (se 1 (by rfl) ⟨426173, by rfl⟩ : syracuseStep 568231 = 852347) B852347
theorem B568551 : Blo 566810 568551 := bstep (se 1 (by rfl) ⟨426413, by rfl⟩ : syracuseStep 568551 = 852827) B852827
theorem B568859 : Blo 566810 568859 := bstep (se 1 (by rfl) ⟨426644, by rfl⟩ : syracuseStep 568859 = 853289) B853289
theorem B569551 : Blo 566810 569551 := bstep (se 1 (by rfl) ⟨427163, by rfl⟩ : syracuseStep 569551 = 854327) B854327
theorem B2077085 : Blo 566810 2077085 := bstep (se 3 (by rfl) ⟨389453, by rfl⟩ : syracuseStep 2077085 = 778907) B778907
theorem B569759 : Blo 566810 569759 := bstep (se 1 (by rfl) ⟨427319, by rfl⟩ : syracuseStep 569759 = 854639) B854639
theorem B570215 : Blo 566810 570215 := bstep (se 1 (by rfl) ⟨427661, by rfl⟩ : syracuseStep 570215 = 855323) B855323
theorem B3879935 : Blo 566810 3879935 := bstep (se 1 (by rfl) ⟨2909951, by rfl⟩ : syracuseStep 3879935 = 5819903) B5819903
theorem B570479 : Blo 566810 570479 := bstep (se 1 (by rfl) ⟨427859, by rfl⟩ : syracuseStep 570479 = 855719) B855719
theorem B570591 : Blo 566810 570591 := bstep (se 1 (by rfl) ⟨427943, by rfl⟩ : syracuseStep 570591 = 855887) B855887
theorem B13284773 : Blo 566810 13284773 := bstep (se 4 (by rfl) ⟨1245447, by rfl⟩ : syracuseStep 13284773 = 2490895) B2490895
theorem B1915703 : Blo 566810 1915703 := bstep (se 1 (by rfl) ⟨1436777, by rfl⟩ : syracuseStep 1915703 = 2873555) B2873555
theorem B24919073 : Blo 566810 24919073 := bstep (se 2 (by rfl) ⟨9344652, by rfl⟩ : syracuseStep 24919073 = 18689305) B18689305
theorem B605351 : Blo 566810 605351 := bstep (se 1 (by rfl) ⟨454013, by rfl⟩ : syracuseStep 605351 = 908027) B908027
theorem B638491 : Blo 566810 638491 := bstep (se 1 (by rfl) ⟨478868, by rfl⟩ : syracuseStep 638491 = 957737) B957737
theorem B4374445 : Blo 566810 4374445 := bstep (se 3 (by rfl) ⟨820208, by rfl⟩ : syracuseStep 4374445 = 1640417) B1640417
theorem B1916891 : Blo 566810 1916891 := bstep (se 1 (by rfl) ⟨1437668, by rfl⟩ : syracuseStep 1916891 = 2875337) B2875337
theorem B14565419 : Blo 566810 14565419 := bstep (se 1 (by rfl) ⟨10924064, by rfl⟩ : syracuseStep 14565419 = 21848129) B21848129
theorem B1916999 : Blo 566810 1916999 := bstep (se 1 (by rfl) ⟨1437749, by rfl⟩ : syracuseStep 1916999 = 2875499) B2875499
theorem B639067 : Blo 566810 639067 := bstep (se 1 (by rfl) ⟨479300, by rfl⟩ : syracuseStep 639067 = 958601) B958601
theorem B24985907 : Blo 566810 24985907 := bstep (se 1 (by rfl) ⟨18739430, by rfl⟩ : syracuseStep 24985907 = 37478861) B37478861
theorem B639535 : Blo 566810 639535 := bstep (se 1 (by rfl) ⟨479651, by rfl⟩ : syracuseStep 639535 = 959303) B959303
theorem B3655145 : Blo 566810 3655145 := bstep (se 2 (by rfl) ⟨1370679, by rfl⟩ : syracuseStep 3655145 = 2741359) B2741359
theorem B1623689 : Blo 566810 1623689 := bstep (se 2 (by rfl) ⟨608883, by rfl⟩ : syracuseStep 1623689 = 1217767) B1217767
theorem B8734787 : Blo 566810 8734787 := bstep (se 1 (by rfl) ⟨6551090, by rfl⟩ : syracuseStep 8734787 = 13102181) B13102181
theorem B641695 : Blo 566810 641695 := bstep (se 1 (by rfl) ⟨481271, by rfl⟩ : syracuseStep 641695 = 962543) B962543
theorem B4147955 : Blo 566810 4147955 := bstep (se 1 (by rfl) ⟨3110966, by rfl⟩ : syracuseStep 4147955 = 6221933) B6221933
theorem B9719027 : Blo 566810 9719027 := bstep (se 1 (by rfl) ⟨7289270, by rfl⟩ : syracuseStep 9719027 = 14578541) B14578541
theorem B15584561 : Blo 566810 15584561 := bstep (se 2 (by rfl) ⟨5844210, by rfl⟩ : syracuseStep 15584561 = 11688421) B11688421
theorem B1920509 : Blo 566810 1920509 := bstep (se 3 (by rfl) ⟨360095, by rfl⟩ : syracuseStep 1920509 = 720191) B720191
theorem B1920617 : Blo 566810 1920617 := bstep (se 2 (by rfl) ⟨720231, by rfl⟩ : syracuseStep 1920617 = 1440463) B1440463
theorem B1921319 : Blo 566810 1921319 := bstep (se 1 (by rfl) ⟨1440989, by rfl⟩ : syracuseStep 1921319 = 2881979) B2881979
theorem B2216375 : Blo 566810 2216375 := bstep (se 1 (by rfl) ⟨1662281, by rfl⟩ : syracuseStep 2216375 = 3324563) B3324563
theorem B3232295 : Blo 566810 3232295 := bstep (se 1 (by rfl) ⟨2424221, by rfl⟩ : syracuseStep 3232295 = 4848443) B4848443
theorem B2871935 : Blo 566810 2871935 := bstep (se 1 (by rfl) ⟨2153951, by rfl⟩ : syracuseStep 2871935 = 4307903) B4307903
theorem B1922075 : Blo 566810 1922075 := bstep (se 1 (by rfl) ⟨1441556, by rfl⟩ : syracuseStep 1922075 = 2883113) B2883113
theorem B1922183 : Blo 566810 1922183 := bstep (se 1 (by rfl) ⟨1441637, by rfl⟩ : syracuseStep 1922183 = 2883275) B2883275
theorem B2741473 : Blo 566810 2741473 := bstep (se 2 (by rfl) ⟨1028052, by rfl⟩ : syracuseStep 2741473 = 2056105) B2056105
theorem B1922345 : Blo 566810 1922345 := bstep (se 2 (by rfl) ⟨720879, by rfl⟩ : syracuseStep 1922345 = 1441759) B1441759
theorem B2152403 : Blo 566810 2152403 := bstep (se 1 (by rfl) ⟨1614302, by rfl⟩ : syracuseStep 2152403 = 3228605) B3228605
theorem B2874365 : Blo 566810 2874365 := bstep (se 3 (by rfl) ⟨538943, by rfl⟩ : syracuseStep 2874365 = 1077887) B1077887
theorem B1727543 : Blo 566810 1727543 := bstep (se 1 (by rfl) ⟨1295657, by rfl⟩ : syracuseStep 1727543 = 2591315) B2591315
theorem B1826111 : Blo 566810 1826111 := bstep (se 1 (by rfl) ⟨1369583, by rfl⟩ : syracuseStep 1826111 = 2739167) B2739167
theorem B1924559 : Blo 566810 1924559 := bstep (se 1 (by rfl) ⟨1443419, by rfl⟩ : syracuseStep 1924559 = 2886839) B2886839
theorem B1924991 : Blo 566810 1924991 := bstep (se 1 (by rfl) ⟨1443743, by rfl⟩ : syracuseStep 1924991 = 2887487) B2887487
theorem B3235895 : Blo 566810 3235895 := bstep (se 1 (by rfl) ⟨2426921, by rfl⟩ : syracuseStep 3235895 = 4853843) B4853843
theorem B1925531 : Blo 566810 1925531 := bstep (se 1 (by rfl) ⟨1444148, by rfl⟩ : syracuseStep 1925531 = 2888297) B2888297
theorem B8217449 : Blo 566810 8217449 := bstep (se 2 (by rfl) ⟨3081543, by rfl⟩ : syracuseStep 8217449 = 6163087) B6163087
theorem B2188255 : Blo 566810 2188255 := bstep (se 1 (by rfl) ⟨1641191, by rfl⟩ : syracuseStep 2188255 = 3282383) B3282383
theorem B2876471 : Blo 566810 2876471 := bstep (se 1 (by rfl) ⟨2157353, by rfl⟩ : syracuseStep 2876471 = 4314707) B4314707
theorem B3073259 : Blo 566810 3073259 := bstep (se 1 (by rfl) ⟨2304944, by rfl⟩ : syracuseStep 3073259 = 4609889) B4609889
theorem B1926395 : Blo 566810 1926395 := bstep (se 1 (by rfl) ⟨1444796, by rfl⟩ : syracuseStep 1926395 = 2889593) B2889593
theorem B812539 : Blo 566810 812539 := bstep (se 1 (by rfl) ⟨609404, by rfl⟩ : syracuseStep 812539 = 1218809) B1218809
theorem B1828585 : Blo 566810 1828585 := bstep (se 2 (by rfl) ⟨685719, by rfl⟩ : syracuseStep 1828585 = 1371439) B1371439
theorem B23357263 : Blo 566810 23357263 := bstep (se 1 (by rfl) ⟨17517947, by rfl⟩ : syracuseStep 23357263 = 35035895) B35035895
theorem B4843385 : Blo 566810 4843385 := bstep (se 2 (by rfl) ⟨1816269, by rfl⟩ : syracuseStep 4843385 = 3632539) B3632539
theorem B31647827 : Blo 566810 31647827 := bstep (se 1 (by rfl) ⟨23735870, by rfl⟩ : syracuseStep 31647827 = 47471741) B47471741
theorem B2156975 : Blo 566810 2156975 := bstep (se 1 (by rfl) ⟨1617731, by rfl⟩ : syracuseStep 2156975 = 3235463) B3235463
theorem B3631823 : Blo 566810 3631823 := bstep (se 1 (by rfl) ⟨2723867, by rfl⟩ : syracuseStep 3631823 = 5447735) B5447735
theorem B2190239 : Blo 566810 2190239 := bstep (se 1 (by rfl) ⟨1642679, by rfl⟩ : syracuseStep 2190239 = 3285359) B3285359
theorem B36925307 : Blo 566810 36925307 := bstep (se 1 (by rfl) ⟨27693980, by rfl⟩ : syracuseStep 36925307 = 55387961) B55387961
theorem B6485183 : Blo 566810 6485183 := bstep (se 1 (by rfl) ⟨4863887, by rfl⟩ : syracuseStep 6485183 = 9727775) B9727775
theorem B1275731 : Blo 566810 1275731 := bstep (se 1 (by rfl) ⟨956798, by rfl⟩ : syracuseStep 1275731 = 1913597) B1913597
theorem B1275803 : Blo 566810 1275803 := bstep (se 1 (by rfl) ⟨956852, by rfl⟩ : syracuseStep 1275803 = 1913705) B1913705
theorem B1275839 : Blo 566810 1275839 := bstep (se 1 (by rfl) ⟨956879, by rfl⟩ : syracuseStep 1275839 = 1913759) B1913759
theorem B3635513 : Blo 566810 3635513 := bstep (se 2 (by rfl) ⟨1363317, by rfl⟩ : syracuseStep 3635513 = 2726635) B2726635
theorem B1440139 : Blo 566810 1440139 := bstep (se 1 (by rfl) ⟨1080104, by rfl⟩ : syracuseStep 1440139 = 2160209) B2160209
theorem B7305673 : Blo 566810 7305673 := bstep (se 2 (by rfl) ⟨2739627, by rfl⟩ : syracuseStep 7305673 = 5479255) B5479255
theorem B850727 : Blo 566810 850727 := bstep (se 1 (by rfl) ⟨638045, by rfl⟩ : syracuseStep 850727 = 1276091) B1276091
theorem B1276775 : Blo 566810 1276775 := bstep (se 1 (by rfl) ⟨957581, by rfl⟩ : syracuseStep 1276775 = 1915163) B1915163
theorem B850937 : Blo 566810 850937 := bstep (se 2 (by rfl) ⟨319101, by rfl⟩ : syracuseStep 850937 = 638203) B638203
theorem B851483 : Blo 566810 851483 := bstep (se 1 (by rfl) ⟨638612, by rfl⟩ : syracuseStep 851483 = 1277225) B1277225
theorem B1441435 : Blo 566810 1441435 := bstep (se 1 (by rfl) ⟨1081076, by rfl⟩ : syracuseStep 1441435 = 2162153) B2162153
theorem B1277999 : Blo 566810 1277999 := bstep (se 1 (by rfl) ⟨958499, by rfl⟩ : syracuseStep 1277999 = 1916999) B1916999
theorem B852089 : Blo 566810 852089 := bstep (se 2 (by rfl) ⟨319533, by rfl⟩ : syracuseStep 852089 = 639067) B639067
theorem B1442407 : Blo 566810 1442407 := bstep (se 1 (by rfl) ⟨1081805, by rfl⟩ : syracuseStep 1442407 = 2163611) B2163611
theorem B852713 : Blo 566810 852713 := bstep (se 2 (by rfl) ⟨319767, by rfl⟩ : syracuseStep 852713 = 639535) B639535
theorem B5538893 : Blo 566810 5538893 := bstep (se 3 (by rfl) ⟨1038542, by rfl⟩ : syracuseStep 5538893 = 2077085) B2077085
theorem B1082459 : Blo 566810 1082459 := bstep (se 1 (by rfl) ⟨811844, by rfl⟩ : syracuseStep 1082459 = 1623689) B1623689
theorem B853175 : Blo 566810 853175 := bstep (se 1 (by rfl) ⟨639881, by rfl⟩ : syracuseStep 853175 = 1279763) B1279763
theorem B2884895 : Blo 566810 2884895 := bstep (se 1 (by rfl) ⟨2163671, by rfl⟩ : syracuseStep 2884895 = 4327343) B4327343
theorem B2917673 : Blo 566810 2917673 := bstep (se 2 (by rfl) ⟨1094127, by rfl⟩ : syracuseStep 2917673 = 2188255) B2188255
theorem B1279529 : Blo 566810 1279529 := bstep (se 2 (by rfl) ⟨479823, by rfl⟩ : syracuseStep 1279529 = 959647) B959647
theorem B1083385 : Blo 566810 1083385 := bstep (se 2 (by rfl) ⟨406269, by rfl⟩ : syracuseStep 1083385 = 812539) B812539
theorem B10389707 : Blo 566810 10389707 := bstep (se 1 (by rfl) ⟨7792280, by rfl⟩ : syracuseStep 10389707 = 15584561) B15584561
theorem B1280339 : Blo 566810 1280339 := bstep (se 1 (by rfl) ⟨960254, by rfl⟩ : syracuseStep 1280339 = 1920509) B1920509
theorem B1280411 : Blo 566810 1280411 := bstep (se 1 (by rfl) ⟨960308, by rfl⟩ : syracuseStep 1280411 = 1920617) B1920617
theorem B854495 : Blo 566810 854495 := bstep (se 1 (by rfl) ⟨640871, by rfl⟩ : syracuseStep 854495 = 1281743) B1281743
theorem B1444463 : Blo 566810 1444463 := bstep (se 1 (by rfl) ⟨1083347, by rfl⟩ : syracuseStep 1444463 = 2166695) B2166695
theorem B2427691 : Blo 566810 2427691 := bstep (se 1 (by rfl) ⟨1820768, by rfl⟩ : syracuseStep 2427691 = 3641537) B3641537
theorem B1280879 : Blo 566810 1280879 := bstep (se 1 (by rfl) ⟨960659, by rfl⟩ : syracuseStep 1280879 = 1921319) B1921319
theorem B4328315 : Blo 566810 4328315 := bstep (se 1 (by rfl) ⟨3246236, by rfl⟩ : syracuseStep 4328315 = 6492473) B6492473
theorem B8195357 : Blo 566810 8195357 := bstep (se 3 (by rfl) ⟨1536629, by rfl⟩ : syracuseStep 8195357 = 3073259) B3073259
theorem B1281383 : Blo 566810 1281383 := bstep (se 1 (by rfl) ⟨961037, by rfl⟩ : syracuseStep 1281383 = 1922075) B1922075
theorem B1281455 : Blo 566810 1281455 := bstep (se 1 (by rfl) ⟨961091, by rfl⟩ : syracuseStep 1281455 = 1922183) B1922183
theorem B1281563 : Blo 566810 1281563 := bstep (se 1 (by rfl) ⟨961172, by rfl⟩ : syracuseStep 1281563 = 1922345) B1922345
theorem B855593 : Blo 566810 855593 := bstep (se 2 (by rfl) ⟨320847, by rfl⟩ : syracuseStep 855593 = 641695) B641695
theorem B1281761 : Blo 566810 1281761 := bstep (se 2 (by rfl) ⟨480660, by rfl⟩ : syracuseStep 1281761 = 961321) B961321
theorem B855899 : Blo 566810 855899 := bstep (se 1 (by rfl) ⟨641924, by rfl⟩ : syracuseStep 855899 = 1283849) B1283849
theorem B856091 : Blo 566810 856091 := bstep (se 1 (by rfl) ⟨642068, by rfl⟩ : syracuseStep 856091 = 1284137) B1284137
theorem B1151695 : Blo 566810 1151695 := bstep (se 1 (by rfl) ⟨863771, by rfl⟩ : syracuseStep 1151695 = 1727543) B1727543
theorem B1283039 : Blo 566810 1283039 := bstep (se 1 (by rfl) ⟨962279, by rfl⟩ : syracuseStep 1283039 = 1924559) B1924559
theorem B1283327 : Blo 566810 1283327 := bstep (se 1 (by rfl) ⟨962495, by rfl⟩ : syracuseStep 1283327 = 1924991) B1924991
theorem B1283687 : Blo 566810 1283687 := bstep (se 1 (by rfl) ⟨962765, by rfl⟩ : syracuseStep 1283687 = 1925531) B1925531
theorem B5478299 : Blo 566810 5478299 := bstep (se 1 (by rfl) ⟨4108724, by rfl⟩ : syracuseStep 5478299 = 8217449) B8217449
theorem B1284263 : Blo 566810 1284263 := bstep (se 1 (by rfl) ⟨963197, by rfl⟩ : syracuseStep 1284263 = 1926395) B1926395
theorem B4857569 : Blo 566810 4857569 := bstep (se 2 (by rfl) ⟨1821588, by rfl⟩ : syracuseStep 4857569 = 3643177) B3643177
theorem B24616871 : Blo 566810 24616871 := bstep (se 1 (by rfl) ⟨18462653, by rfl⟩ : syracuseStep 24616871 = 36925307) B36925307
theorem B1614269 : Blo 566810 1614269 := bstep (se 3 (by rfl) ⟨302675, by rfl⟩ : syracuseStep 1614269 = 605351) B605351
theorem B9740897 : Blo 566810 9740897 := bstep (se 2 (by rfl) ⟨3652836, by rfl⟩ : syracuseStep 9740897 = 7305673) B7305673
theorem B8856515 : Blo 566810 8856515 := bstep (se 1 (by rfl) ⟨6642386, by rfl⟩ : syracuseStep 8856515 = 13284773) B13284773
theorem B567151 : Blo 566810 567151 := bstep (se 1 (by rfl) ⟨425363, by rfl⟩ : syracuseStep 567151 = 850727) B850727
theorem B567291 : Blo 566810 567291 := bstep (se 1 (by rfl) ⟨425468, by rfl⟩ : syracuseStep 567291 = 850937) B850937
theorem B567655 : Blo 566810 567655 := bstep (se 1 (by rfl) ⟨425741, by rfl⟩ : syracuseStep 567655 = 851483) B851483
theorem B9710279 : Blo 566810 9710279 := bstep (se 1 (by rfl) ⟨7282709, by rfl⟩ : syracuseStep 9710279 = 14565419) B14565419
theorem B568015 : Blo 566810 568015 := bstep (se 1 (by rfl) ⟨426011, by rfl⟩ : syracuseStep 568015 = 852023) B852023
theorem B568039 : Blo 566810 568039 := bstep (se 1 (by rfl) ⟨426029, by rfl⟩ : syracuseStep 568039 = 852059) B852059
theorem B568047 : Blo 566810 568047 := bstep (se 1 (by rfl) ⟨426035, by rfl⟩ : syracuseStep 568047 = 852071) B852071
theorem B16657271 : Blo 566810 16657271 := bstep (se 1 (by rfl) ⟨12492953, by rfl⟩ : syracuseStep 16657271 = 24985907) B24985907
theorem B4860881 : Blo 566810 4860881 := bstep (se 2 (by rfl) ⟨1822830, by rfl⟩ : syracuseStep 4860881 = 3645661) B3645661
theorem B568487 : Blo 566810 568487 := bstep (se 1 (by rfl) ⟨426365, by rfl⟩ : syracuseStep 568487 = 852731) B852731
theorem B568639 : Blo 566810 568639 := bstep (se 1 (by rfl) ⟨426479, by rfl⟩ : syracuseStep 568639 = 852959) B852959
theorem B568815 : Blo 566810 568815 := bstep (se 1 (by rfl) ⟨426611, by rfl⟩ : syracuseStep 568815 = 853223) B853223
theorem B2436763 : Blo 566810 2436763 := bstep (se 1 (by rfl) ⟨1827572, by rfl⟩ : syracuseStep 2436763 = 3655145) B3655145
theorem B569063 : Blo 566810 569063 := bstep (se 1 (by rfl) ⟨426797, by rfl⟩ : syracuseStep 569063 = 853595) B853595
theorem B569375 : Blo 566810 569375 := bstep (se 1 (by rfl) ⟨427031, by rfl⟩ : syracuseStep 569375 = 854063) B854063
theorem B962651 : Blo 566810 962651 := bstep (se 1 (by rfl) ⟨721988, by rfl⟩ : syracuseStep 962651 = 1443977) B1443977
theorem B2765303 : Blo 566810 2765303 := bstep (se 1 (by rfl) ⟨2073977, by rfl⟩ : syracuseStep 2765303 = 4147955) B4147955
theorem B2438113 : Blo 566810 2438113 := bstep (se 2 (by rfl) ⟨914292, by rfl⟩ : syracuseStep 2438113 = 1828585) B1828585
theorem B31143017 : Blo 566810 31143017 := bstep (se 2 (by rfl) ⟨11678631, by rfl⟩ : syracuseStep 31143017 = 23357263) B23357263
theorem B570559 : Blo 566810 570559 := bstep (se 1 (by rfl) ⟨427919, by rfl⟩ : syracuseStep 570559 = 855839) B855839
theorem B8172751 : Blo 566810 8172751 := bstep (se 1 (by rfl) ⟨6129563, by rfl⟩ : syracuseStep 8172751 = 12259127) B12259127
theorem B24557003 : Blo 566810 24557003 := bstep (se 1 (by rfl) ⟨18417752, by rfl⟩ : syracuseStep 24557003 = 36835505) B36835505
theorem B6469145 : Blo 566810 6469145 := bstep (se 2 (by rfl) ⟨2425929, by rfl⟩ : syracuseStep 6469145 = 4851859) B4851859
theorem B1914623 : Blo 566810 1914623 := bstep (se 1 (by rfl) ⟨1435967, by rfl⟩ : syracuseStep 1914623 = 2871935) B2871935
theorem B33274111 : Blo 566810 33274111 := bstep (se 1 (by rfl) ⟨24955583, by rfl⟩ : syracuseStep 33274111 = 49911167) B49911167
theorem B9714653 : Blo 566810 9714653 := bstep (se 3 (by rfl) ⟨1821497, by rfl⟩ : syracuseStep 9714653 = 3642995) B3642995
theorem B1916243 : Blo 566810 1916243 := bstep (se 1 (by rfl) ⟨1437182, by rfl⟩ : syracuseStep 1916243 = 2874365) B2874365
theorem B4308875 : Blo 566810 4308875 := bstep (se 1 (by rfl) ⟨3231656, by rfl⟩ : syracuseStep 4308875 = 6463313) B6463313
theorem B1917647 : Blo 566810 1917647 := bstep (se 1 (by rfl) ⟨1438235, by rfl⟩ : syracuseStep 1917647 = 2876471) B2876471
theorem B3228923 : Blo 566810 3228923 := bstep (se 1 (by rfl) ⟨2421692, by rfl⟩ : syracuseStep 3228923 = 4843385) B4843385
theorem B3655297 : Blo 566810 3655297 := bstep (se 2 (by rfl) ⟨1370736, by rfl⟩ : syracuseStep 3655297 = 2741473) B2741473
theorem B1460159 : Blo 566810 1460159 := bstep (se 1 (by rfl) ⟨1095119, by rfl⟩ : syracuseStep 1460159 = 2190239) B2190239
theorem B2738285 : Blo 566810 2738285 := bstep (se 3 (by rfl) ⟨513428, by rfl⟩ : syracuseStep 2738285 = 1026857) B1026857
theorem B1920185 : Blo 566810 1920185 := bstep (se 2 (by rfl) ⟨720069, by rfl⟩ : syracuseStep 1920185 = 1440139) B1440139
theorem B4869629 : Blo 566810 4869629 := bstep (se 3 (by rfl) ⟨913055, by rfl⟩ : syracuseStep 4869629 = 1826111) B1826111
theorem B5820929 : Blo 566810 5820929 := bstep (se 2 (by rfl) ⟨2182848, by rfl⟩ : syracuseStep 5820929 = 4365697) B4365697
theorem B1921913 : Blo 566810 1921913 := bstep (se 2 (by rfl) ⟨720717, by rfl⟩ : syracuseStep 1921913 = 1441435) B1441435
theorem B18438515 : Blo 566810 18438515 := bstep (se 1 (by rfl) ⟨13828886, by rfl⟩ : syracuseStep 18438515 = 27657773) B27657773
theorem B5823191 : Blo 566810 5823191 := bstep (se 1 (by rfl) ⟨4367393, by rfl⟩ : syracuseStep 5823191 = 8734787) B8734787
theorem B6479351 : Blo 566810 6479351 := bstep (se 1 (by rfl) ⟨4859513, by rfl⟩ : syracuseStep 6479351 = 9719027) B9719027
theorem B810751 : Blo 566810 810751 := bstep (se 1 (by rfl) ⟨608063, by rfl⟩ : syracuseStep 810751 = 1216127) B1216127
theorem B2154863 : Blo 566810 2154863 := bstep (se 1 (by rfl) ⟨1616147, by rfl⟩ : syracuseStep 2154863 = 3232295) B3232295
theorem B1434935 : Blo 566810 1434935 := bstep (se 1 (by rfl) ⟨1076201, by rfl⟩ : syracuseStep 1434935 = 2152403) B2152403
theorem B8218655 : Blo 566810 8218655 := bstep (se 1 (by rfl) ⟨6163991, by rfl⟩ : syracuseStep 8218655 = 12327983) B12327983
theorem B682111 : Blo 566810 682111 := bstep (se 1 (by rfl) ⟨511583, by rfl⟩ : syracuseStep 682111 = 1023167) B1023167
theorem B2157263 : Blo 566810 2157263 := bstep (se 1 (by rfl) ⟨1617947, by rfl⟩ : syracuseStep 2157263 = 3235895) B3235895
theorem B1077295 : Blo 566810 1077295 := bstep (se 1 (by rfl) ⟨807971, by rfl⟩ : syracuseStep 1077295 = 1615943) B1615943
theorem B21098551 : Blo 566810 21098551 := bstep (se 1 (by rfl) ⟨15823913, by rfl⟩ : syracuseStep 21098551 = 31647827) B31647827
theorem B41644307 : Blo 566810 41644307 := bstep (se 1 (by rfl) ⟨31233230, by rfl⟩ : syracuseStep 41644307 = 62466461) B62466461
theorem B1437983 : Blo 566810 1437983 := bstep (se 1 (by rfl) ⟨1078487, by rfl⟩ : syracuseStep 1437983 = 2156975) B2156975
theorem B36008347 : Blo 566810 36008347 := bstep (se 1 (by rfl) ⟨27006260, by rfl⟩ : syracuseStep 36008347 = 54012521) B54012521
theorem B2421215 : Blo 566810 2421215 := bstep (se 1 (by rfl) ⟨1815911, by rfl⟩ : syracuseStep 2421215 = 3631823) B3631823
theorem B94565333 : Blo 566810 94565333 := bstep (se 7 (by rfl) ⟨1108187, by rfl⟩ : syracuseStep 94565333 = 2216375) B2216375
theorem B2586623 : Blo 566810 2586623 := bstep (se 1 (by rfl) ⟨1939967, by rfl⟩ : syracuseStep 2586623 = 3879935) B3879935
theorem B4323455 : Blo 566810 4323455 := bstep (se 1 (by rfl) ⟨3242591, by rfl⟩ : syracuseStep 4323455 = 6485183) B6485183
theorem B850487 : Blo 566810 850487 := bstep (se 1 (by rfl) ⟨637865, by rfl⟩ : syracuseStep 850487 = 1275731) B1275731
theorem B850535 : Blo 566810 850535 := bstep (se 1 (by rfl) ⟨637901, by rfl⟩ : syracuseStep 850535 = 1275803) B1275803
theorem B850559 : Blo 566810 850559 := bstep (se 1 (by rfl) ⟨637919, by rfl⟩ : syracuseStep 850559 = 1275839) B1275839
theorem B2423675 : Blo 566810 2423675 := bstep (se 1 (by rfl) ⟨1817756, by rfl⟩ : syracuseStep 2423675 = 3635513) B3635513
theorem B1277135 : Blo 566810 1277135 := bstep (se 1 (by rfl) ⟨957851, by rfl⟩ : syracuseStep 1277135 = 1915703) B1915703
theorem B851183 : Blo 566810 851183 := bstep (se 1 (by rfl) ⟨638387, by rfl⟩ : syracuseStep 851183 = 1276775) B1276775
theorem B16612715 : Blo 566810 16612715 := bstep (se 1 (by rfl) ⟨12459536, by rfl⟩ : syracuseStep 16612715 = 24919073) B24919073
theorem B851321 : Blo 566810 851321 := bstep (se 2 (by rfl) ⟨319245, by rfl⟩ : syracuseStep 851321 = 638491) B638491
theorem B5832593 : Blo 566810 5832593 := bstep (se 2 (by rfl) ⟨2187222, by rfl⟩ : syracuseStep 5832593 = 4374445) B4374445
theorem B1277927 : Blo 566810 1277927 := bstep (se 1 (by rfl) ⟨958445, by rfl⟩ : syracuseStep 1277927 = 1916891) B1916891
theorem B851999 : Blo 566810 851999 := bstep (se 1 (by rfl) ⟨638999, by rfl⟩ : syracuseStep 851999 = 1277999) B1277999
theorem B1278431 : Blo 566810 1278431 := bstep (se 1 (by rfl) ⟨958823, by rfl⟩ : syracuseStep 1278431 = 1917647) B1917647
theorem B721639 : Blo 566810 721639 := bstep (se 1 (by rfl) ⟨541229, by rfl⟩ : syracuseStep 721639 = 1082459) B1082459
theorem B59081525 : Blo 566810 59081525 := bstep (se 5 (by rfl) ⟨2769446, by rfl⟩ : syracuseStep 59081525 = 5538893) B5538893
theorem B853019 : Blo 566810 853019 := bstep (se 1 (by rfl) ⟨639764, by rfl⟩ : syracuseStep 853019 = 1279529) B1279529
theorem B853559 : Blo 566810 853559 := bstep (se 1 (by rfl) ⟨640169, by rfl⟩ : syracuseStep 853559 = 1280339) B1280339
theorem B853607 : Blo 566810 853607 := bstep (se 1 (by rfl) ⟨640205, by rfl⟩ : syracuseStep 853607 = 1280411) B1280411
theorem B853919 : Blo 566810 853919 := bstep (se 1 (by rfl) ⟨640439, by rfl⟩ : syracuseStep 853919 = 1280879) B1280879
theorem B2885543 : Blo 566810 2885543 := bstep (se 1 (by rfl) ⟨2164157, by rfl⟩ : syracuseStep 2885543 = 4328315) B4328315
theorem B1280123 : Blo 566810 1280123 := bstep (se 1 (by rfl) ⟨960092, by rfl⟩ : syracuseStep 1280123 = 1920185) B1920185
theorem B854255 : Blo 566810 854255 := bstep (se 1 (by rfl) ⟨640691, by rfl⟩ : syracuseStep 854255 = 1281383) B1281383
theorem B854303 : Blo 566810 854303 := bstep (se 1 (by rfl) ⟨640727, by rfl⟩ : syracuseStep 854303 = 1281455) B1281455
theorem B3246419 : Blo 566810 3246419 := bstep (se 1 (by rfl) ⟨2434814, by rfl⟩ : syracuseStep 3246419 = 4869629) B4869629
theorem B854375 : Blo 566810 854375 := bstep (se 1 (by rfl) ⟨640781, by rfl⟩ : syracuseStep 854375 = 1281563) B1281563
theorem B854507 : Blo 566810 854507 := bstep (se 1 (by rfl) ⟨640880, by rfl⟩ : syracuseStep 854507 = 1281761) B1281761
theorem B1444513 : Blo 566810 1444513 := bstep (se 2 (by rfl) ⟨541692, by rfl⟩ : syracuseStep 1444513 = 1083385) B1083385
theorem B1281275 : Blo 566810 1281275 := bstep (se 1 (by rfl) ⟨960956, by rfl⟩ : syracuseStep 1281275 = 1921913) B1921913
theorem B855359 : Blo 566810 855359 := bstep (se 1 (by rfl) ⟨641519, by rfl⟩ : syracuseStep 855359 = 1283039) B1283039
theorem B855551 : Blo 566810 855551 := bstep (se 1 (by rfl) ⟨641663, by rfl⟩ : syracuseStep 855551 = 1283327) B1283327
theorem B855791 : Blo 566810 855791 := bstep (se 1 (by rfl) ⟨641843, by rfl⟩ : syracuseStep 855791 = 1283687) B1283687
theorem B856175 : Blo 566810 856175 := bstep (se 1 (by rfl) ⟨642131, by rfl⟩ : syracuseStep 856175 = 1284263) B1284263
theorem B12292343 : Blo 566810 12292343 := bstep (se 1 (by rfl) ⟨9219257, by rfl⟩ : syracuseStep 12292343 = 18438515) B18438515
theorem B3249017 : Blo 566810 3249017 := bstep (se 2 (by rfl) ⟨1218381, by rfl⟩ : syracuseStep 3249017 = 2436763) B2436763
theorem B6493931 : Blo 566810 6493931 := bstep (se 1 (by rfl) ⟨4870448, by rfl⟩ : syracuseStep 6493931 = 9740897) B9740897
theorem B48011129 : Blo 566810 48011129 := bstep (se 2 (by rfl) ⟨18004173, by rfl⟩ : syracuseStep 48011129 = 36008347) B36008347
theorem B5904343 : Blo 566810 5904343 := bstep (se 1 (by rfl) ⟨4428257, by rfl⟩ : syracuseStep 5904343 = 8856515) B8856515
theorem B956623 : Blo 566810 956623 := bstep (se 1 (by rfl) ⟨717467, by rfl⟩ : syracuseStep 956623 = 1434935) B1434935
theorem B3250817 : Blo 566810 3250817 := bstep (se 2 (by rfl) ⟨1219056, by rfl⟩ : syracuseStep 3250817 = 2438113) B2438113
theorem B5479103 : Blo 566810 5479103 := bstep (se 1 (by rfl) ⟨4109327, by rfl⟩ : syracuseStep 5479103 = 8218655) B8218655
theorem B27762871 : Blo 566810 27762871 := bstep (se 1 (by rfl) ⟨20822153, by rfl⟩ : syracuseStep 27762871 = 41644307) B41644307
theorem B958655 : Blo 566810 958655 := bstep (se 1 (by rfl) ⟨718991, by rfl⟩ : syracuseStep 958655 = 1437983) B1437983
theorem B1614143 : Blo 566810 1614143 := bstep (se 1 (by rfl) ⟨1210607, by rfl⟩ : syracuseStep 1614143 = 2421215) B2421215
theorem B1843535 : Blo 566810 1843535 := bstep (se 1 (by rfl) ⟨1382651, by rfl⟩ : syracuseStep 1843535 = 2765303) B2765303
theorem B566991 : Blo 566810 566991 := bstep (se 1 (by rfl) ⟨425243, by rfl⟩ : syracuseStep 566991 = 850487) B850487
theorem B567023 : Blo 566810 567023 := bstep (se 1 (by rfl) ⟨425267, by rfl⟩ : syracuseStep 567023 = 850535) B850535
theorem B567039 : Blo 566810 567039 := bstep (se 1 (by rfl) ⟨425279, by rfl⟩ : syracuseStep 567039 = 850559) B850559
theorem B1615783 : Blo 566810 1615783 := bstep (se 1 (by rfl) ⟨1211837, by rfl⟩ : syracuseStep 1615783 = 2423675) B2423675
theorem B567455 : Blo 566810 567455 := bstep (se 1 (by rfl) ⟨425591, by rfl⟩ : syracuseStep 567455 = 851183) B851183
theorem B567547 : Blo 566810 567547 := bstep (se 1 (by rfl) ⟨425660, by rfl⟩ : syracuseStep 567547 = 851321) B851321
theorem B568059 : Blo 566810 568059 := bstep (se 1 (by rfl) ⟨426044, by rfl⟩ : syracuseStep 568059 = 852089) B852089
theorem B568475 : Blo 566810 568475 := bstep (se 1 (by rfl) ⟨426356, by rfl⟩ : syracuseStep 568475 = 852713) B852713
theorem B568783 : Blo 566810 568783 := bstep (se 1 (by rfl) ⟨426587, by rfl⟩ : syracuseStep 568783 = 853175) B853175
theorem B1945115 : Blo 566810 1945115 := bstep (se 1 (by rfl) ⟨1458836, by rfl⟩ : syracuseStep 1945115 = 2917673) B2917673
theorem B6926471 : Blo 566810 6926471 := bstep (se 1 (by rfl) ⟨5194853, by rfl⟩ : syracuseStep 6926471 = 10389707) B10389707
theorem B569663 : Blo 566810 569663 := bstep (se 1 (by rfl) ⟨427247, by rfl⟩ : syracuseStep 569663 = 854495) B854495
theorem B962975 : Blo 566810 962975 := bstep (se 1 (by rfl) ⟨722231, by rfl⟩ : syracuseStep 962975 = 1444463) B1444463
theorem B570395 : Blo 566810 570395 := bstep (se 1 (by rfl) ⟨427796, by rfl⟩ : syracuseStep 570395 = 855593) B855593
theorem B570599 : Blo 566810 570599 := bstep (se 1 (by rfl) ⟨427949, by rfl⟩ : syracuseStep 570599 = 855899) B855899
theorem B570727 : Blo 566810 570727 := bstep (se 1 (by rfl) ⟨428045, by rfl⟩ : syracuseStep 570727 = 856091) B856091
theorem B3880619 : Blo 566810 3880619 := bstep (se 1 (by rfl) ⟨2910464, by rfl⟩ : syracuseStep 3880619 = 5820929) B5820929
theorem B3652199 : Blo 566810 3652199 := bstep (se 1 (by rfl) ⟨2739149, by rfl⟩ : syracuseStep 3652199 = 5478299) B5478299
theorem B3882127 : Blo 566810 3882127 := bstep (se 1 (by rfl) ⟨2911595, by rfl⟩ : syracuseStep 3882127 = 5823191) B5823191
theorem B28131401 : Blo 566810 28131401 := bstep (se 2 (by rfl) ⟨10549275, by rfl⟩ : syracuseStep 28131401 = 21098551) B21098551
theorem B10897001 : Blo 566810 10897001 := bstep (se 2 (by rfl) ⟨4086375, by rfl⟩ : syracuseStep 10897001 = 8172751) B8172751
theorem B6473519 : Blo 566810 6473519 := bstep (se 1 (by rfl) ⟨4855139, by rfl⟩ : syracuseStep 6473519 = 9710279) B9710279
theorem B641767 : Blo 566810 641767 := bstep (se 1 (by rfl) ⟨481325, by rfl⟩ : syracuseStep 641767 = 962651) B962651
theorem B20762011 : Blo 566810 20762011 := bstep (se 1 (by rfl) ⟨15571508, by rfl⟩ : syracuseStep 20762011 = 31143017) B31143017
theorem B16371335 : Blo 566810 16371335 := bstep (se 1 (by rfl) ⟨12278501, by rfl⟩ : syracuseStep 16371335 = 24557003) B24557003
theorem B4312763 : Blo 566810 4312763 := bstep (se 1 (by rfl) ⟨3234572, by rfl⟩ : syracuseStep 4312763 = 6469145) B6469145
theorem B6476435 : Blo 566810 6476435 := bstep (se 1 (by rfl) ⟨4857326, by rfl⟩ : syracuseStep 6476435 = 9714653) B9714653
theorem B2872583 : Blo 566810 2872583 := bstep (se 1 (by rfl) ⟨2154437, by rfl⟩ : syracuseStep 2872583 = 4308875) B4308875
theorem B3888395 : Blo 566810 3888395 := bstep (se 1 (by rfl) ⟨2916296, by rfl⟩ : syracuseStep 3888395 = 5832593) B5832593
theorem B1923209 : Blo 566810 1923209 := bstep (se 2 (by rfl) ⟨721203, by rfl⟩ : syracuseStep 1923209 = 1442407) B1442407
theorem B2152615 : Blo 566810 2152615 := bstep (se 1 (by rfl) ⟨1614461, by rfl⟩ : syracuseStep 2152615 = 3228923) B3228923
theorem B1923263 : Blo 566810 1923263 := bstep (se 1 (by rfl) ⟨1442447, by rfl⟩ : syracuseStep 1923263 = 2884895) B2884895
theorem B973439 : Blo 566810 973439 := bstep (se 1 (by rfl) ⟨730079, by rfl⟩ : syracuseStep 973439 = 1460159) B1460159
theorem B1825523 : Blo 566810 1825523 := bstep (se 1 (by rfl) ⟨1369142, by rfl⟩ : syracuseStep 1825523 = 2738285) B2738285
theorem B4873729 : Blo 566810 4873729 := bstep (se 2 (by rfl) ⟨1827648, by rfl⟩ : syracuseStep 4873729 = 3655297) B3655297
theorem B5463571 : Blo 566810 5463571 := bstep (se 1 (by rfl) ⟨4097678, by rfl⟩ : syracuseStep 5463571 = 8195357) B8195357
theorem B252174221 : Blo 566810 252174221 := bstep (se 3 (by rfl) ⟨47282666, by rfl⟩ : syracuseStep 252174221 = 94565333) B94565333
theorem B909481 : Blo 566810 909481 := bstep (se 2 (by rfl) ⟨341055, by rfl⟩ : syracuseStep 909481 = 682111) B682111
theorem B3236921 : Blo 566810 3236921 := bstep (se 2 (by rfl) ⟨1213845, by rfl⟩ : syracuseStep 3236921 = 2427691) B2427691
theorem B4319567 : Blo 566810 4319567 := bstep (se 1 (by rfl) ⟨3239675, by rfl⟩ : syracuseStep 4319567 = 6479351) B6479351
theorem B3238379 : Blo 566810 3238379 := bstep (se 1 (by rfl) ⟨2428784, by rfl⟩ : syracuseStep 3238379 = 4857569) B4857569
theorem B16411247 : Blo 566810 16411247 := bstep (se 1 (by rfl) ⟨12308435, by rfl⟩ : syracuseStep 16411247 = 24616871) B24616871
theorem B1436393 : Blo 566810 1436393 := bstep (se 2 (by rfl) ⟨538647, by rfl⟩ : syracuseStep 1436393 = 1077295) B1077295
theorem B1436575 : Blo 566810 1436575 := bstep (se 1 (by rfl) ⟨1077431, by rfl⟩ : syracuseStep 1436575 = 2154863) B2154863
theorem B1076179 : Blo 566810 1076179 := bstep (se 1 (by rfl) ⟨807134, by rfl⟩ : syracuseStep 1076179 = 1614269) B1614269
theorem B1535593 : Blo 566810 1535593 := bstep (se 2 (by rfl) ⟨575847, by rfl⟩ : syracuseStep 1535593 = 1151695) B1151695
theorem B1438175 : Blo 566810 1438175 := bstep (se 1 (by rfl) ⟨1078631, by rfl⟩ : syracuseStep 1438175 = 2157263) B2157263
theorem B11104847 : Blo 566810 11104847 := bstep (se 1 (by rfl) ⟨8328635, by rfl⟩ : syracuseStep 11104847 = 16657271) B16657271
theorem B3240587 : Blo 566810 3240587 := bstep (se 1 (by rfl) ⟨2430440, by rfl⟩ : syracuseStep 3240587 = 4860881) B4860881
theorem B44365481 : Blo 566810 44365481 := bstep (se 2 (by rfl) ⟨16637055, by rfl⟩ : syracuseStep 44365481 = 33274111) B33274111
theorem B1276415 : Blo 566810 1276415 := bstep (se 1 (by rfl) ⟨957311, by rfl⟩ : syracuseStep 1276415 = 1914623) B1914623
theorem B2882303 : Blo 566810 2882303 := bstep (se 1 (by rfl) ⟨2161727, by rfl⟩ : syracuseStep 2882303 = 4323455) B4323455
theorem B851423 : Blo 566810 851423 := bstep (se 1 (by rfl) ⟨638567, by rfl⟩ : syracuseStep 851423 = 1277135) B1277135
theorem B1277495 : Blo 566810 1277495 := bstep (se 1 (by rfl) ⟨958121, by rfl⟩ : syracuseStep 1277495 = 1916243) B1916243
theorem B11075143 : Blo 566810 11075143 := bstep (se 1 (by rfl) ⟨8306357, by rfl⟩ : syracuseStep 11075143 = 16612715) B16612715
theorem B1081001 : Blo 566810 1081001 := bstep (se 2 (by rfl) ⟨405375, by rfl⟩ : syracuseStep 1081001 = 810751) B810751
theorem B851951 : Blo 566810 851951 := bstep (se 1 (by rfl) ⟨638963, by rfl⟩ : syracuseStep 851951 = 1277927) B1277927
theorem B27590645 : Blo 566810 27590645 := bstep (se 5 (by rfl) ⟨1293311, by rfl⟩ : syracuseStep 27590645 = 2586623) B2586623
theorem B1212641 : Blo 566810 1212641 := bstep (se 2 (by rfl) ⟨454740, by rfl⟩ : syracuseStep 1212641 = 909481) B909481
theorem B852287 : Blo 566810 852287 := bstep (se 1 (by rfl) ⟨639215, by rfl⟩ : syracuseStep 852287 = 1278431) B1278431
theorem B39387683 : Blo 566810 39387683 := bstep (se 1 (by rfl) ⟨29540762, by rfl⟩ : syracuseStep 39387683 = 59081525) B59081525
theorem B853415 : Blo 566810 853415 := bstep (se 1 (by rfl) ⟨640061, by rfl⟩ : syracuseStep 853415 = 1280123) B1280123
theorem B2164279 : Blo 566810 2164279 := bstep (se 1 (by rfl) ⟨1623209, by rfl⟩ : syracuseStep 2164279 = 3246419) B3246419
theorem B854183 : Blo 566810 854183 := bstep (se 1 (by rfl) ⟨640637, by rfl⟩ : syracuseStep 854183 = 1281275) B1281275
theorem B10914223 : Blo 566810 10914223 := bstep (se 1 (by rfl) ⟨8185667, by rfl⟩ : syracuseStep 10914223 = 16371335) B16371335
theorem B8194895 : Blo 566810 8194895 := bstep (se 1 (by rfl) ⟨6146171, by rfl⟩ : syracuseStep 8194895 = 12292343) B12292343
theorem B2166011 : Blo 566810 2166011 := bstep (se 1 (by rfl) ⟨1624508, by rfl⟩ : syracuseStep 2166011 = 3249017) B3249017
theorem B2592263 : Blo 566810 2592263 := bstep (se 1 (by rfl) ⟨1944197, by rfl⟩ : syracuseStep 2592263 = 3888395) B3888395
theorem B855689 : Blo 566810 855689 := bstep (se 2 (by rfl) ⟨320883, by rfl⟩ : syracuseStep 855689 = 641767) B641767
theorem B4329287 : Blo 566810 4329287 := bstep (se 1 (by rfl) ⟨3246965, by rfl⟩ : syracuseStep 4329287 = 6493931) B6493931
theorem B1282139 : Blo 566810 1282139 := bstep (se 1 (by rfl) ⟨961604, by rfl⟩ : syracuseStep 1282139 = 1923209) B1923209
theorem B1282175 : Blo 566810 1282175 := bstep (se 1 (by rfl) ⟨961631, by rfl⟩ : syracuseStep 1282175 = 1923263) B1923263
theorem B2167211 : Blo 566810 2167211 := bstep (se 1 (by rfl) ⟨1625408, by rfl⟩ : syracuseStep 2167211 = 3250817) B3250817
theorem B1217015 : Blo 566810 1217015 := bstep (se 1 (by rfl) ⟨912761, by rfl⟩ : syracuseStep 1217015 = 1825523) B1825523
theorem B957595 : Blo 566810 957595 := bstep (se 1 (by rfl) ⟨718196, by rfl⟩ : syracuseStep 957595 = 1436393) B1436393
theorem B958783 : Blo 566810 958783 := bstep (se 1 (by rfl) ⟨719087, by rfl⟩ : syracuseStep 958783 = 1438175) B1438175
theorem B2434799 : Blo 566810 2434799 := bstep (se 1 (by rfl) ⟨1826099, by rfl⟩ : syracuseStep 2434799 = 3652199) B3652199
theorem B6498305 : Blo 566810 6498305 := bstep (se 2 (by rfl) ⟨2436864, by rfl⟩ : syracuseStep 6498305 = 4873729) B4873729
theorem B7284761 : Blo 566810 7284761 := bstep (se 2 (by rfl) ⟨2731785, by rfl⟩ : syracuseStep 7284761 = 5463571) B5463571
theorem B567615 : Blo 566810 567615 := bstep (se 1 (by rfl) ⟨425711, by rfl⟩ : syracuseStep 567615 = 851423) B851423
theorem B567967 : Blo 566810 567967 := bstep (se 1 (by rfl) ⟨425975, by rfl⟩ : syracuseStep 567967 = 851951) B851951
theorem B18393763 : Blo 566810 18393763 := bstep (se 1 (by rfl) ⟨13795322, by rfl⟩ : syracuseStep 18393763 = 27590645) B27590645
theorem B567999 : Blo 566810 567999 := bstep (se 1 (by rfl) ⟨425999, by rfl⟩ : syracuseStep 567999 = 851999) B851999
theorem B18754267 : Blo 566810 18754267 := bstep (se 1 (by rfl) ⟨14065700, by rfl⟩ : syracuseStep 18754267 = 28131401) B28131401
theorem B568679 : Blo 566810 568679 := bstep (se 1 (by rfl) ⟨426509, by rfl⟩ : syracuseStep 568679 = 853019) B853019
theorem B962185 : Blo 566810 962185 := bstep (se 2 (by rfl) ⟨360819, by rfl⟩ : syracuseStep 962185 = 721639) B721639
theorem B569039 : Blo 566810 569039 := bstep (se 1 (by rfl) ⟨426779, by rfl⟩ : syracuseStep 569039 = 853559) B853559
theorem B569071 : Blo 566810 569071 := bstep (se 1 (by rfl) ⟨426803, by rfl⟩ : syracuseStep 569071 = 853607) B853607
theorem B569279 : Blo 566810 569279 := bstep (se 1 (by rfl) ⟨426959, by rfl⟩ : syracuseStep 569279 = 853919) B853919
theorem B569503 : Blo 566810 569503 := bstep (se 1 (by rfl) ⟨427127, by rfl⟩ : syracuseStep 569503 = 854255) B854255
theorem B569535 : Blo 566810 569535 := bstep (se 1 (by rfl) ⟨427151, by rfl⟩ : syracuseStep 569535 = 854303) B854303
theorem B569583 : Blo 566810 569583 := bstep (se 1 (by rfl) ⟨427187, by rfl⟩ : syracuseStep 569583 = 854375) B854375
theorem B569671 : Blo 566810 569671 := bstep (se 1 (by rfl) ⟨427253, by rfl⟩ : syracuseStep 569671 = 854507) B854507
theorem B570239 : Blo 566810 570239 := bstep (se 1 (by rfl) ⟨427679, by rfl⟩ : syracuseStep 570239 = 855359) B855359
theorem B570367 : Blo 566810 570367 := bstep (se 1 (by rfl) ⟨427775, by rfl⟩ : syracuseStep 570367 = 855551) B855551
theorem B570527 : Blo 566810 570527 := bstep (se 1 (by rfl) ⟨427895, by rfl⟩ : syracuseStep 570527 = 855791) B855791
theorem B570783 : Blo 566810 570783 := bstep (se 1 (by rfl) ⟨428087, by rfl⟩ : syracuseStep 570783 = 856175) B856175
theorem B1915055 : Blo 566810 1915055 := bstep (se 1 (by rfl) ⟨1436291, by rfl⟩ : syracuseStep 1915055 = 2872583) B2872583
theorem B1915433 : Blo 566810 1915433 := bstep (se 2 (by rfl) ⟨718287, by rfl⟩ : syracuseStep 1915433 = 1436575) B1436575
theorem B3652735 : Blo 566810 3652735 := bstep (se 1 (by rfl) ⟨2739551, by rfl⟩ : syracuseStep 3652735 = 5479103) B5479103
theorem B2047457 : Blo 566810 2047457 := bstep (se 2 (by rfl) ⟨767796, by rfl⟩ : syracuseStep 2047457 = 1535593) B1535593
theorem B168116147 : Blo 566810 168116147 := bstep (se 1 (by rfl) ⟨126087110, by rfl⟩ : syracuseStep 168116147 = 252174221) B252174221
theorem B639103 : Blo 566810 639103 := bstep (se 1 (by rfl) ⟨479327, by rfl⟩ : syracuseStep 639103 = 958655) B958655
theorem B1229023 : Blo 566810 1229023 := bstep (se 1 (by rfl) ⟨921767, by rfl⟩ : syracuseStep 1229023 = 1843535) B1843535
theorem B1296743 : Blo 566810 1296743 := bstep (se 1 (by rfl) ⟨972557, by rfl⟩ : syracuseStep 1296743 = 1945115) B1945115
theorem B2870153 : Blo 566810 2870153 := bstep (se 2 (by rfl) ⟨1076307, by rfl⟩ : syracuseStep 2870153 = 2152615) B2152615
theorem B641983 : Blo 566810 641983 := bstep (se 1 (by rfl) ⟨481487, by rfl⟩ : syracuseStep 641983 = 962975) B962975
theorem B29576987 : Blo 566810 29576987 := bstep (se 1 (by rfl) ⟨22182740, by rfl⟩ : syracuseStep 29576987 = 44365481) B44365481
theorem B1921535 : Blo 566810 1921535 := bstep (se 1 (by rfl) ⟨1441151, by rfl⟩ : syracuseStep 1921535 = 2882303) B2882303
theorem B14766857 : Blo 566810 14766857 := bstep (se 2 (by rfl) ⟨5537571, by rfl⟩ : syracuseStep 14766857 = 11075143) B11075143
theorem B37017161 : Blo 566810 37017161 := bstep (se 2 (by rfl) ⟨13881435, by rfl⟩ : syracuseStep 37017161 = 27762871) B27762871
theorem B7264667 : Blo 566810 7264667 := bstep (se 1 (by rfl) ⟨5448500, by rfl⟩ : syracuseStep 7264667 = 10897001) B10897001
theorem B4315679 : Blo 566810 4315679 := bstep (se 1 (by rfl) ⟨3236759, by rfl⟩ : syracuseStep 4315679 = 6473519) B6473519
theorem B1923695 : Blo 566810 1923695 := bstep (se 1 (by rfl) ⟨1442771, by rfl⟩ : syracuseStep 1923695 = 2885543) B2885543
theorem B2875175 : Blo 566810 2875175 := bstep (se 1 (by rfl) ⟨2156381, by rfl⟩ : syracuseStep 2875175 = 4312763) B4312763
theorem B2154377 : Blo 566810 2154377 := bstep (se 2 (by rfl) ⟨807891, by rfl⟩ : syracuseStep 2154377 = 1615783) B1615783
theorem B4317623 : Blo 566810 4317623 := bstep (se 1 (by rfl) ⟨3238217, by rfl⟩ : syracuseStep 4317623 = 6476435) B6476435
theorem B1926017 : Blo 566810 1926017 := bstep (se 2 (by rfl) ⟨722256, by rfl⟩ : syracuseStep 1926017 = 1444513) B1444513
theorem B32007419 : Blo 566810 32007419 := bstep (se 1 (by rfl) ⟨24005564, by rfl⟩ : syracuseStep 32007419 = 48011129) B48011129
theorem B1434905 : Blo 566810 1434905 := bstep (se 2 (by rfl) ⟨538089, by rfl⟩ : syracuseStep 1434905 = 1076179) B1076179
theorem B648959 : Blo 566810 648959 := bstep (se 1 (by rfl) ⟨486719, by rfl⟩ : syracuseStep 648959 = 973439) B973439
theorem B27682681 : Blo 566810 27682681 := bstep (se 2 (by rfl) ⟨10381005, by rfl⟩ : syracuseStep 27682681 = 20762011) B20762011
theorem B1076095 : Blo 566810 1076095 := bstep (se 1 (by rfl) ⟨807071, by rfl⟩ : syracuseStep 1076095 = 1614143) B1614143
theorem B2157947 : Blo 566810 2157947 := bstep (se 1 (by rfl) ⟨1618460, by rfl⟩ : syracuseStep 2157947 = 3236921) B3236921
theorem B2879711 : Blo 566810 2879711 := bstep (se 1 (by rfl) ⟨2159783, by rfl⟩ : syracuseStep 2879711 = 4319567) B4319567
theorem B2158919 : Blo 566810 2158919 := bstep (se 1 (by rfl) ⟨1619189, by rfl⟩ : syracuseStep 2158919 = 3238379) B3238379
theorem B10940831 : Blo 566810 10940831 := bstep (se 1 (by rfl) ⟨8205623, by rfl⟩ : syracuseStep 10940831 = 16411247) B16411247
theorem B4617647 : Blo 566810 4617647 := bstep (se 1 (by rfl) ⟨3463235, by rfl⟩ : syracuseStep 4617647 = 6926471) B6926471
theorem B1275497 : Blo 566810 1275497 := bstep (se 2 (by rfl) ⟨478311, by rfl⟩ : syracuseStep 1275497 = 956623) B956623
theorem B7403231 : Blo 566810 7403231 := bstep (se 1 (by rfl) ⟨5552423, by rfl⟩ : syracuseStep 7403231 = 11104847) B11104847
theorem B2160391 : Blo 566810 2160391 := bstep (se 1 (by rfl) ⟨1620293, by rfl⟩ : syracuseStep 2160391 = 3240587) B3240587
theorem B2587079 : Blo 566810 2587079 := bstep (se 1 (by rfl) ⟨1940309, by rfl⟩ : syracuseStep 2587079 = 3880619) B3880619
theorem B5176169 : Blo 566810 5176169 := bstep (se 2 (by rfl) ⟨1941063, by rfl⟩ : syracuseStep 5176169 = 3882127) B3882127
theorem B850943 : Blo 566810 850943 := bstep (se 1 (by rfl) ⟨638207, by rfl⟩ : syracuseStep 850943 = 1276415) B1276415
theorem B851663 : Blo 566810 851663 := bstep (se 1 (by rfl) ⟨638747, by rfl⟩ : syracuseStep 851663 = 1277495) B1277495
theorem B720667 : Blo 566810 720667 := bstep (se 1 (by rfl) ⟨540500, by rfl⟩ : syracuseStep 720667 = 1081001) B1081001
theorem B31489829 : Blo 566810 31489829 := bstep (se 4 (by rfl) ⟨2952171, by rfl⟩ : syracuseStep 31489829 = 5904343) B5904343
theorem B852137 : Blo 566810 852137 := bstep (se 2 (by rfl) ⟨319551, by rfl⟩ : syracuseStep 852137 = 639103) B639103
theorem B1278377 : Blo 566810 1278377 := bstep (se 2 (by rfl) ⟨479391, by rfl⟩ : syracuseStep 1278377 = 958783) B958783
theorem B6554789 : Blo 566810 6554789 := bstep (se 4 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 6554789 = 1229023) B1229023
theorem B2885705 : Blo 566810 2885705 := bstep (se 2 (by rfl) ⟨1082139, by rfl⟩ : syracuseStep 2885705 = 2164279) B2164279
theorem B1444007 : Blo 566810 1444007 := bstep (se 1 (by rfl) ⟨1083005, by rfl⟩ : syracuseStep 1444007 = 2166011) B2166011
theorem B2886191 : Blo 566810 2886191 := bstep (se 1 (by rfl) ⟨2164643, by rfl⟩ : syracuseStep 2886191 = 4329287) B4329287
theorem B854759 : Blo 566810 854759 := bstep (se 1 (by rfl) ⟨641069, by rfl⟩ : syracuseStep 854759 = 1282139) B1282139
theorem B854783 : Blo 566810 854783 := bstep (se 1 (by rfl) ⟨641087, by rfl⟩ : syracuseStep 854783 = 1282175) B1282175
theorem B1444807 : Blo 566810 1444807 := bstep (se 1 (by rfl) ⟨1083605, by rfl⟩ : syracuseStep 1444807 = 2167211) B2167211
theorem B1281023 : Blo 566810 1281023 := bstep (se 1 (by rfl) ⟨960767, by rfl⟩ : syracuseStep 1281023 = 1921535) B1921535
theorem B14552297 : Blo 566810 14552297 := bstep (se 2 (by rfl) ⟨5457111, by rfl⟩ : syracuseStep 14552297 = 10914223) B10914223
theorem B25005689 : Blo 566810 25005689 := bstep (se 2 (by rfl) ⟨9377133, by rfl⟩ : syracuseStep 25005689 = 18754267) B18754267
theorem B24678107 : Blo 566810 24678107 := bstep (se 1 (by rfl) ⟨18508580, by rfl⟩ : syracuseStep 24678107 = 37017161) B37017161
theorem B855977 : Blo 566810 855977 := bstep (se 2 (by rfl) ⟨320991, by rfl⟩ : syracuseStep 855977 = 641983) B641983
theorem B1282463 : Blo 566810 1282463 := bstep (se 1 (by rfl) ⟨961847, by rfl⟩ : syracuseStep 1282463 = 1923695) B1923695
theorem B1282913 : Blo 566810 1282913 := bstep (se 2 (by rfl) ⟨481092, by rfl⟩ : syracuseStep 1282913 = 962185) B962185
theorem B1284011 : Blo 566810 1284011 := bstep (se 1 (by rfl) ⟨963008, by rfl⟩ : syracuseStep 1284011 = 1926017) B1926017
theorem B21338279 : Blo 566810 21338279 := bstep (se 1 (by rfl) ⟨16003709, by rfl⟩ : syracuseStep 21338279 = 32007419) B32007419
theorem B956603 : Blo 566810 956603 := bstep (se 1 (by rfl) ⟨717452, by rfl⟩ : syracuseStep 956603 = 1434905) B1434905
theorem B4332203 : Blo 566810 4332203 := bstep (se 1 (by rfl) ⟨3249152, by rfl⟩ : syracuseStep 4332203 = 6498305) B6498305
theorem B4856507 : Blo 566810 4856507 := bstep (se 1 (by rfl) ⟨3642380, by rfl⟩ : syracuseStep 4856507 = 7284761) B7284761
theorem B3450779 : Blo 566810 3450779 := bstep (se 1 (by rfl) ⟨2588084, by rfl⟩ : syracuseStep 3450779 = 5176169) B5176169
theorem B567295 : Blo 566810 567295 := bstep (se 1 (by rfl) ⟨425471, by rfl⟩ : syracuseStep 567295 = 850943) B850943
theorem B960889 : Blo 566810 960889 := bstep (se 2 (by rfl) ⟨360333, by rfl⟩ : syracuseStep 960889 = 720667) B720667
theorem B567775 : Blo 566810 567775 := bstep (se 1 (by rfl) ⟨425831, by rfl⟩ : syracuseStep 567775 = 851663) B851663
theorem B112077431 : Blo 566810 112077431 := bstep (se 1 (by rfl) ⟨84058073, by rfl⟩ : syracuseStep 112077431 = 168116147) B168116147
theorem B568191 : Blo 566810 568191 := bstep (se 1 (by rfl) ⟨426143, by rfl⟩ : syracuseStep 568191 = 852287) B852287
theorem B26258455 : Blo 566810 26258455 := bstep (se 1 (by rfl) ⟨19693841, by rfl⟩ : syracuseStep 26258455 = 39387683) B39387683
theorem B568943 : Blo 566810 568943 := bstep (se 1 (by rfl) ⟨426707, by rfl⟩ : syracuseStep 568943 = 853415) B853415
theorem B569455 : Blo 566810 569455 := bstep (se 1 (by rfl) ⟨427091, by rfl⟩ : syracuseStep 569455 = 854183) B854183
theorem B1913435 : Blo 566810 1913435 := bstep (se 1 (by rfl) ⟨1435076, by rfl⟩ : syracuseStep 1913435 = 2870153) B2870153
theorem B570459 : Blo 566810 570459 := bstep (se 1 (by rfl) ⟨427844, by rfl⟩ : syracuseStep 570459 = 855689) B855689
theorem B36910241 : Blo 566810 36910241 := bstep (se 2 (by rfl) ⟨13841340, by rfl⟩ : syracuseStep 36910241 = 27682681) B27682681
theorem B9844571 : Blo 566810 9844571 := bstep (se 1 (by rfl) ⟨7383428, by rfl⟩ : syracuseStep 9844571 = 14766857) B14766857
theorem B24525017 : Blo 566810 24525017 := bstep (se 2 (by rfl) ⟨9196881, by rfl⟩ : syracuseStep 24525017 = 18393763) B18393763
theorem B1916783 : Blo 566810 1916783 := bstep (se 1 (by rfl) ⟨1437587, by rfl⟩ : syracuseStep 1916783 = 2875175) B2875175
theorem B3457981 : Blo 566810 3457981 := bstep (se 3 (by rfl) ⟨648371, by rfl⟩ : syracuseStep 3457981 = 1296743) B1296743
theorem B1623199 : Blo 566810 1623199 := bstep (se 1 (by rfl) ⟨1217399, by rfl⟩ : syracuseStep 1623199 = 2434799) B2434799
theorem B6898877 : Blo 566810 6898877 := bstep (se 3 (by rfl) ⟨1293539, by rfl⟩ : syracuseStep 6898877 = 2587079) B2587079
theorem B1919807 : Blo 566810 1919807 := bstep (se 1 (by rfl) ⟨1439855, by rfl⟩ : syracuseStep 1919807 = 2879711) B2879711
theorem B7293887 : Blo 566810 7293887 := bstep (se 1 (by rfl) ⟨5470415, by rfl⟩ : syracuseStep 7293887 = 10940831) B10940831
theorem B4935487 : Blo 566810 4935487 := bstep (se 1 (by rfl) ⟨3701615, by rfl⟩ : syracuseStep 4935487 = 7403231) B7403231
theorem B4870313 : Blo 566810 4870313 := bstep (se 2 (by rfl) ⟨1826367, by rfl⟩ : syracuseStep 4870313 = 3652735) B3652735
theorem B1364971 : Blo 566810 1364971 := bstep (se 1 (by rfl) ⟨1023728, by rfl⟩ : syracuseStep 1364971 = 2047457) B2047457
theorem B20993219 : Blo 566810 20993219 := bstep (se 1 (by rfl) ⟨15744914, by rfl⟩ : syracuseStep 20993219 = 31489829) B31489829
theorem B808427 : Blo 566810 808427 := bstep (se 1 (by rfl) ⟨606320, by rfl⟩ : syracuseStep 808427 = 1212641) B1212641
theorem B5463263 : Blo 566810 5463263 := bstep (se 1 (by rfl) ⟨4097447, by rfl⟩ : syracuseStep 5463263 = 8194895) B8194895
theorem B1728175 : Blo 566810 1728175 := bstep (se 1 (by rfl) ⟨1296131, by rfl⟩ : syracuseStep 1728175 = 2592263) B2592263
theorem B19717991 : Blo 566810 19717991 := bstep (se 1 (by rfl) ⟨14788493, by rfl⟩ : syracuseStep 19717991 = 29576987) B29576987
theorem B811343 : Blo 566810 811343 := bstep (se 1 (by rfl) ⟨608507, by rfl⟩ : syracuseStep 811343 = 1217015) B1217015
theorem B1434793 : Blo 566810 1434793 := bstep (se 2 (by rfl) ⟨538047, by rfl⟩ : syracuseStep 1434793 = 1076095) B1076095
theorem B4843111 : Blo 566810 4843111 := bstep (se 1 (by rfl) ⟨3632333, by rfl⟩ : syracuseStep 4843111 = 7264667) B7264667
theorem B2877119 : Blo 566810 2877119 := bstep (se 1 (by rfl) ⟨2157839, by rfl⟩ : syracuseStep 2877119 = 4315679) B4315679
theorem B1730557 : Blo 566810 1730557 := bstep (se 3 (by rfl) ⟨324479, by rfl⟩ : syracuseStep 1730557 = 648959) B648959
theorem B1436251 : Blo 566810 1436251 := bstep (se 1 (by rfl) ⟨1077188, by rfl⟩ : syracuseStep 1436251 = 2154377) B2154377
theorem B2878415 : Blo 566810 2878415 := bstep (se 1 (by rfl) ⟨2158811, by rfl⟩ : syracuseStep 2878415 = 4317623) B4317623
theorem B1438631 : Blo 566810 1438631 := bstep (se 1 (by rfl) ⟨1078973, by rfl⟩ : syracuseStep 1438631 = 2157947) B2157947
theorem B2880521 : Blo 566810 2880521 := bstep (se 2 (by rfl) ⟨1080195, by rfl⟩ : syracuseStep 2880521 = 2160391) B2160391
theorem B1439279 : Blo 566810 1439279 := bstep (se 1 (by rfl) ⟨1079459, by rfl⟩ : syracuseStep 1439279 = 2158919) B2158919
theorem B3078431 : Blo 566810 3078431 := bstep (se 1 (by rfl) ⟨2308823, by rfl⟩ : syracuseStep 3078431 = 4617647) B4617647
theorem B850331 : Blo 566810 850331 := bstep (se 1 (by rfl) ⟨637748, by rfl⟩ : syracuseStep 850331 = 1275497) B1275497
theorem B1276703 : Blo 566810 1276703 := bstep (se 1 (by rfl) ⟨957527, by rfl⟩ : syracuseStep 1276703 = 1915055) B1915055
theorem B1276793 : Blo 566810 1276793 := bstep (se 2 (by rfl) ⟨478797, by rfl⟩ : syracuseStep 1276793 = 957595) B957595
theorem B1276955 : Blo 566810 1276955 := bstep (se 1 (by rfl) ⟨957716, by rfl⟩ : syracuseStep 1276955 = 1915433) B1915433
theorem B852251 : Blo 566810 852251 := bstep (se 1 (by rfl) ⟨639188, by rfl⟩ : syracuseStep 852251 = 1278377) B1278377
theorem B2163581 : Blo 566810 2163581 := bstep (se 3 (by rfl) ⟨405671, by rfl⟩ : syracuseStep 2163581 = 811343) B811343
theorem B2164265 : Blo 566810 2164265 := bstep (se 2 (by rfl) ⟨811599, by rfl⟩ : syracuseStep 2164265 = 1623199) B1623199
theorem B1279871 : Blo 566810 1279871 := bstep (se 1 (by rfl) ⟨959903, by rfl⟩ : syracuseStep 1279871 = 1919807) B1919807
theorem B854015 : Blo 566810 854015 := bstep (se 1 (by rfl) ⟨640511, by rfl⟩ : syracuseStep 854015 = 1281023) B1281023
theorem B6457481 : Blo 566810 6457481 := bstep (se 2 (by rfl) ⟨2421555, by rfl⟩ : syracuseStep 6457481 = 4843111) B4843111
theorem B9701531 : Blo 566810 9701531 := bstep (se 1 (by rfl) ⟨7276148, by rfl⟩ : syracuseStep 9701531 = 14552297) B14552297
theorem B16452071 : Blo 566810 16452071 := bstep (se 1 (by rfl) ⟨12339053, by rfl⟩ : syracuseStep 16452071 = 24678107) B24678107
theorem B3246875 : Blo 566810 3246875 := bstep (se 1 (by rfl) ⟨2435156, by rfl⟩ : syracuseStep 3246875 = 4870313) B4870313
theorem B854975 : Blo 566810 854975 := bstep (se 1 (by rfl) ⟨641231, by rfl⟩ : syracuseStep 854975 = 1282463) B1282463
theorem B1281185 : Blo 566810 1281185 := bstep (se 2 (by rfl) ⟨480444, by rfl⟩ : syracuseStep 1281185 = 960889) B960889
theorem B855275 : Blo 566810 855275 := bstep (se 1 (by rfl) ⟨641456, by rfl⟩ : syracuseStep 855275 = 1282913) B1282913
theorem B13995479 : Blo 566810 13995479 := bstep (se 1 (by rfl) ⟨10496609, by rfl⟩ : syracuseStep 13995479 = 20993219) B20993219
theorem B856007 : Blo 566810 856007 := bstep (se 1 (by rfl) ⟨642005, by rfl⟩ : syracuseStep 856007 = 1284011) B1284011
theorem B14225519 : Blo 566810 14225519 := bstep (se 1 (by rfl) ⟨10669139, by rfl⟩ : syracuseStep 14225519 = 21338279) B21338279
theorem B2888135 : Blo 566810 2888135 := bstep (se 1 (by rfl) ⟨2166101, by rfl⟩ : syracuseStep 2888135 = 4332203) B4332203
theorem B3642175 : Blo 566810 3642175 := bstep (se 1 (by rfl) ⟨2731631, by rfl⟩ : syracuseStep 3642175 = 5463263) B5463263
theorem B7705637 : Blo 566810 7705637 := bstep (se 4 (by rfl) ⟨722403, by rfl⟩ : syracuseStep 7705637 = 1444807) B1444807
theorem B13145327 : Blo 566810 13145327 := bstep (se 1 (by rfl) ⟨9858995, by rfl⟩ : syracuseStep 13145327 = 19717991) B19717991
theorem B2300519 : Blo 566810 2300519 := bstep (se 1 (by rfl) ⟨1725389, by rfl⟩ : syracuseStep 2300519 = 3450779) B3450779
theorem B74718287 : Blo 566810 74718287 := bstep (se 1 (by rfl) ⟨56038715, by rfl⟩ : syracuseStep 74718287 = 112077431) B112077431
theorem B959087 : Blo 566810 959087 := bstep (se 1 (by rfl) ⟨719315, by rfl⟩ : syracuseStep 959087 = 1438631) B1438631
theorem B959519 : Blo 566810 959519 := bstep (se 1 (by rfl) ⟨719639, by rfl⟩ : syracuseStep 959519 = 1439279) B1439279
theorem B6563047 : Blo 566810 6563047 := bstep (se 1 (by rfl) ⟨4922285, by rfl⟩ : syracuseStep 6563047 = 9844571) B9844571
theorem B566887 : Blo 566810 566887 := bstep (se 1 (by rfl) ⟨425165, by rfl⟩ : syracuseStep 566887 = 850331) B850331
theorem B2304233 : Blo 566810 2304233 := bstep (se 2 (by rfl) ⟨864087, by rfl⟩ : syracuseStep 2304233 = 1728175) B1728175
theorem B568091 : Blo 566810 568091 := bstep (se 1 (by rfl) ⟨426068, by rfl⟩ : syracuseStep 568091 = 852137) B852137
theorem B4369859 : Blo 566810 4369859 := bstep (se 1 (by rfl) ⟨3277394, by rfl⟩ : syracuseStep 4369859 = 6554789) B6554789
theorem B4599251 : Blo 566810 4599251 := bstep (se 1 (by rfl) ⟨3449438, by rfl⟩ : syracuseStep 4599251 = 6898877) B6898877
theorem B962671 : Blo 566810 962671 := bstep (se 1 (by rfl) ⟨722003, by rfl⟩ : syracuseStep 962671 = 1444007) B1444007
theorem B1913057 : Blo 566810 1913057 := bstep (se 2 (by rfl) ⟨717396, by rfl⟩ : syracuseStep 1913057 = 1434793) B1434793
theorem B569839 : Blo 566810 569839 := bstep (se 1 (by rfl) ⟨427379, by rfl⟩ : syracuseStep 569839 = 854759) B854759
theorem B569855 : Blo 566810 569855 := bstep (se 1 (by rfl) ⟨427391, by rfl⟩ : syracuseStep 569855 = 854783) B854783
theorem B4862591 : Blo 566810 4862591 := bstep (se 1 (by rfl) ⟨3646943, by rfl⟩ : syracuseStep 4862591 = 7293887) B7293887
theorem B570651 : Blo 566810 570651 := bstep (se 1 (by rfl) ⟨427988, by rfl⟩ : syracuseStep 570651 = 855977) B855977
theorem B2307409 : Blo 566810 2307409 := bstep (se 2 (by rfl) ⟨865278, by rfl⟩ : syracuseStep 2307409 = 1730557) B1730557
theorem B1915001 : Blo 566810 1915001 := bstep (se 2 (by rfl) ⟨718125, by rfl⟩ : syracuseStep 1915001 = 1436251) B1436251
theorem B35011273 : Blo 566810 35011273 := bstep (se 2 (by rfl) ⟨13129227, by rfl⟩ : syracuseStep 35011273 = 26258455) B26258455
theorem B637735 : Blo 566810 637735 := bstep (se 1 (by rfl) ⟨478301, by rfl⟩ : syracuseStep 637735 = 956603) B956603
theorem B1918079 : Blo 566810 1918079 := bstep (se 1 (by rfl) ⟨1438559, by rfl⟩ : syracuseStep 1918079 = 2877119) B2877119
theorem B1819961 : Blo 566810 1819961 := bstep (se 2 (by rfl) ⟨682485, by rfl⟩ : syracuseStep 1819961 = 1364971) B1364971
theorem B1918943 : Blo 566810 1918943 := bstep (se 1 (by rfl) ⟨1439207, by rfl⟩ : syracuseStep 1918943 = 2878415) B2878415
theorem B1920347 : Blo 566810 1920347 := bstep (se 1 (by rfl) ⟨1440260, by rfl⟩ : syracuseStep 1920347 = 2880521) B2880521
theorem B2052287 : Blo 566810 2052287 := bstep (se 1 (by rfl) ⟨1539215, by rfl⟩ : syracuseStep 2052287 = 3078431) B3078431
theorem B4610641 : Blo 566810 4610641 := bstep (se 2 (by rfl) ⟨1728990, by rfl⟩ : syracuseStep 4610641 = 3457981) B3457981
theorem B1923803 : Blo 566810 1923803 := bstep (se 1 (by rfl) ⟨1442852, by rfl⟩ : syracuseStep 1923803 = 2885705) B2885705
theorem B1924127 : Blo 566810 1924127 := bstep (se 1 (by rfl) ⟨1443095, by rfl⟩ : syracuseStep 1924127 = 2886191) B2886191
theorem B16670459 : Blo 566810 16670459 := bstep (se 1 (by rfl) ⟨12502844, by rfl⟩ : syracuseStep 16670459 = 25005689) B25005689
theorem B2155805 : Blo 566810 2155805 := bstep (se 3 (by rfl) ⟨404213, by rfl⟩ : syracuseStep 2155805 = 808427) B808427
theorem B3237671 : Blo 566810 3237671 := bstep (se 1 (by rfl) ⟨2428253, by rfl⟩ : syracuseStep 3237671 = 4856507) B4856507
theorem B6580649 : Blo 566810 6580649 := bstep (se 2 (by rfl) ⟨2467743, by rfl⟩ : syracuseStep 6580649 = 4935487) B4935487
theorem B1275623 : Blo 566810 1275623 := bstep (se 1 (by rfl) ⟨956717, by rfl⟩ : syracuseStep 1275623 = 1913435) B1913435
theorem B24606827 : Blo 566810 24606827 := bstep (se 1 (by rfl) ⟨18455120, by rfl⟩ : syracuseStep 24606827 = 36910241) B36910241
theorem B16350011 : Blo 566810 16350011 := bstep (se 1 (by rfl) ⟨12262508, by rfl⟩ : syracuseStep 16350011 = 24525017) B24525017
theorem B851135 : Blo 566810 851135 := bstep (se 1 (by rfl) ⟨638351, by rfl⟩ : syracuseStep 851135 = 1276703) B1276703
theorem B851195 : Blo 566810 851195 := bstep (se 1 (by rfl) ⟨638396, by rfl⟩ : syracuseStep 851195 = 1276793) B1276793
theorem B851303 : Blo 566810 851303 := bstep (se 1 (by rfl) ⟨638477, by rfl⟩ : syracuseStep 851303 = 1276955) B1276955
theorem B1277855 : Blo 566810 1277855 := bstep (se 1 (by rfl) ⟨958391, by rfl⟩ : syracuseStep 1277855 = 1916783) B1916783
theorem B1442387 : Blo 566810 1442387 := bstep (se 1 (by rfl) ⟨1081790, by rfl⟩ : syracuseStep 1442387 = 2163581) B2163581
theorem B1278719 : Blo 566810 1278719 := bstep (se 1 (by rfl) ⟨959039, by rfl⟩ : syracuseStep 1278719 = 1918079) B1918079
theorem B1213307 : Blo 566810 1213307 := bstep (se 1 (by rfl) ⟨909980, by rfl⟩ : syracuseStep 1213307 = 1819961) B1819961
theorem B1442843 : Blo 566810 1442843 := bstep (se 1 (by rfl) ⟨1082132, by rfl⟩ : syracuseStep 1442843 = 2164265) B2164265
theorem B853247 : Blo 566810 853247 := bstep (se 1 (by rfl) ⟨639935, by rfl⟩ : syracuseStep 853247 = 1279871) B1279871
theorem B1279295 : Blo 566810 1279295 := bstep (se 1 (by rfl) ⟨959471, by rfl⟩ : syracuseStep 1279295 = 1918943) B1918943
theorem B8750729 : Blo 566810 8750729 := bstep (se 2 (by rfl) ⟨3281523, by rfl⟩ : syracuseStep 8750729 = 6563047) B6563047
theorem B2164583 : Blo 566810 2164583 := bstep (se 1 (by rfl) ⟨1623437, by rfl⟩ : syracuseStep 2164583 = 3246875) B3246875
theorem B854123 : Blo 566810 854123 := bstep (se 1 (by rfl) ⟨640592, by rfl⟩ : syracuseStep 854123 = 1281185) B1281185
theorem B1280231 : Blo 566810 1280231 := bstep (se 1 (by rfl) ⟨960173, by rfl⟩ : syracuseStep 1280231 = 1920347) B1920347
theorem B1282535 : Blo 566810 1282535 := bstep (se 1 (by rfl) ⟨961901, by rfl⟩ : syracuseStep 1282535 = 1923803) B1923803
theorem B1282751 : Blo 566810 1282751 := bstep (se 1 (by rfl) ⟨962063, by rfl⟩ : syracuseStep 1282751 = 1924127) B1924127
theorem B49812191 : Blo 566810 49812191 := bstep (se 1 (by rfl) ⟨37359143, by rfl⟩ : syracuseStep 49812191 = 74718287) B74718287
theorem B1283561 : Blo 566810 1283561 := bstep (se 2 (by rfl) ⟨481335, by rfl⟩ : syracuseStep 1283561 = 962671) B962671
theorem B4856233 : Blo 566810 4856233 := bstep (se 2 (by rfl) ⟨1821087, by rfl⟩ : syracuseStep 4856233 = 3642175) B3642175
theorem B6134717 : Blo 566810 6134717 := bstep (se 3 (by rfl) ⟨1150259, by rfl⟩ : syracuseStep 6134717 = 2300519) B2300519
theorem B567423 : Blo 566810 567423 := bstep (se 1 (by rfl) ⟨425567, by rfl⟩ : syracuseStep 567423 = 851135) B851135
theorem B567463 : Blo 566810 567463 := bstep (se 1 (by rfl) ⟨425597, by rfl⟩ : syracuseStep 567463 = 851195) B851195
theorem B567535 : Blo 566810 567535 := bstep (se 1 (by rfl) ⟨425651, by rfl⟩ : syracuseStep 567535 = 851303) B851303
theorem B568167 : Blo 566810 568167 := bstep (se 1 (by rfl) ⟨426125, by rfl⟩ : syracuseStep 568167 = 852251) B852251
theorem B569343 : Blo 566810 569343 := bstep (se 1 (by rfl) ⟨427007, by rfl⟩ : syracuseStep 569343 = 854015) B854015
theorem B4304987 : Blo 566810 4304987 := bstep (se 1 (by rfl) ⟨3228740, by rfl⟩ : syracuseStep 4304987 = 6457481) B6457481
theorem B6467687 : Blo 566810 6467687 := bstep (se 1 (by rfl) ⟨4850765, by rfl⟩ : syracuseStep 6467687 = 9701531) B9701531
theorem B569983 : Blo 566810 569983 := bstep (se 1 (by rfl) ⟨427487, by rfl⟩ : syracuseStep 569983 = 854975) B854975
theorem B570183 : Blo 566810 570183 := bstep (se 1 (by rfl) ⟨427637, by rfl⟩ : syracuseStep 570183 = 855275) B855275
theorem B570671 : Blo 566810 570671 := bstep (se 1 (by rfl) ⟨428003, by rfl⟩ : syracuseStep 570671 = 856007) B856007
theorem B9483679 : Blo 566810 9483679 := bstep (se 1 (by rfl) ⟨7112759, by rfl⟩ : syracuseStep 9483679 = 14225519) B14225519
theorem B8763551 : Blo 566810 8763551 := bstep (se 1 (by rfl) ⟨6572663, by rfl⟩ : syracuseStep 8763551 = 13145327) B13145327
theorem B639391 : Blo 566810 639391 := bstep (se 1 (by rfl) ⟨479543, by rfl⟩ : syracuseStep 639391 = 959087) B959087
theorem B639679 : Blo 566810 639679 := bstep (se 1 (by rfl) ⟨479759, by rfl⟩ : syracuseStep 639679 = 959519) B959519
theorem B17548397 : Blo 566810 17548397 := bstep (se 3 (by rfl) ⟨3290324, by rfl⟩ : syracuseStep 17548397 = 6580649) B6580649
theorem B12306181 : Blo 566810 12306181 := bstep (se 4 (by rfl) ⟨1153704, by rfl⟩ : syracuseStep 12306181 = 2307409) B2307409
theorem B3066167 : Blo 566810 3066167 := bstep (se 1 (by rfl) ⟨2299625, by rfl⟩ : syracuseStep 3066167 = 4599251) B4599251
theorem B6147521 : Blo 566810 6147521 := bstep (se 2 (by rfl) ⟨2305320, by rfl⟩ : syracuseStep 6147521 = 4610641) B4610641
theorem B46681697 : Blo 566810 46681697 := bstep (se 2 (by rfl) ⟨17505636, by rfl⟩ : syracuseStep 46681697 = 35011273) B35011273
theorem B16404551 : Blo 566810 16404551 := bstep (se 1 (by rfl) ⟨12303413, by rfl⟩ : syracuseStep 16404551 = 24606827) B24606827
theorem B10900007 : Blo 566810 10900007 := bstep (se 1 (by rfl) ⟨8175005, by rfl⟩ : syracuseStep 10900007 = 16350011) B16350011
theorem B44454557 : Blo 566810 44454557 := bstep (se 3 (by rfl) ⟨8335229, by rfl⟩ : syracuseStep 44454557 = 16670459) B16670459
theorem B10968047 : Blo 566810 10968047 := bstep (se 1 (by rfl) ⟨8226035, by rfl⟩ : syracuseStep 10968047 = 16452071) B16452071
theorem B9330319 : Blo 566810 9330319 := bstep (se 1 (by rfl) ⟨6997739, by rfl⟩ : syracuseStep 9330319 = 13995479) B13995479
theorem B1368191 : Blo 566810 1368191 := bstep (se 1 (by rfl) ⟨1026143, by rfl⟩ : syracuseStep 1368191 = 2052287) B2052287
theorem B1925423 : Blo 566810 1925423 := bstep (se 1 (by rfl) ⟨1444067, by rfl⟩ : syracuseStep 1925423 = 2888135) B2888135
theorem B5137091 : Blo 566810 5137091 := bstep (se 1 (by rfl) ⟨3852818, by rfl⟩ : syracuseStep 5137091 = 7705637) B7705637
theorem B1437203 : Blo 566810 1437203 := bstep (se 1 (by rfl) ⟨1077902, by rfl⟩ : syracuseStep 1437203 = 2155805) B2155805
theorem B2158447 : Blo 566810 2158447 := bstep (se 1 (by rfl) ⟨1618835, by rfl⟩ : syracuseStep 2158447 = 3237671) B3237671
theorem B1536155 : Blo 566810 1536155 := bstep (se 1 (by rfl) ⟨1152116, by rfl⟩ : syracuseStep 1536155 = 2304233) B2304233
theorem B2913239 : Blo 566810 2913239 := bstep (se 1 (by rfl) ⟨2184929, by rfl⟩ : syracuseStep 2913239 = 4369859) B4369859
theorem B1275371 : Blo 566810 1275371 := bstep (se 1 (by rfl) ⟨956528, by rfl⟩ : syracuseStep 1275371 = 1913057) B1913057
theorem B3241727 : Blo 566810 3241727 := bstep (se 1 (by rfl) ⟨2431295, by rfl⟩ : syracuseStep 3241727 = 4862591) B4862591
theorem B850313 : Blo 566810 850313 := bstep (se 2 (by rfl) ⟨318867, by rfl⟩ : syracuseStep 850313 = 637735) B637735
theorem B850415 : Blo 566810 850415 := bstep (se 1 (by rfl) ⟨637811, by rfl⟩ : syracuseStep 850415 = 1275623) B1275623
theorem B1276667 : Blo 566810 1276667 := bstep (se 1 (by rfl) ⟨957500, by rfl⟩ : syracuseStep 1276667 = 1915001) B1915001
theorem B851903 : Blo 566810 851903 := bstep (se 1 (by rfl) ⟨638927, by rfl⟩ : syracuseStep 851903 = 1277855) B1277855
theorem B852479 : Blo 566810 852479 := bstep (se 1 (by rfl) ⟨639359, by rfl⟩ : syracuseStep 852479 = 1278719) B1278719
theorem B852521 : Blo 566810 852521 := bstep (se 2 (by rfl) ⟨319695, by rfl⟩ : syracuseStep 852521 = 639391) B639391
theorem B11698931 : Blo 566810 11698931 := bstep (se 1 (by rfl) ⟨8774198, by rfl⟩ : syracuseStep 11698931 = 17548397) B17548397
theorem B852863 : Blo 566810 852863 := bstep (se 1 (by rfl) ⟨639647, by rfl⟩ : syracuseStep 852863 = 1279295) B1279295
theorem B852905 : Blo 566810 852905 := bstep (se 2 (by rfl) ⟨319839, by rfl⟩ : syracuseStep 852905 = 639679) B639679
theorem B5833819 : Blo 566810 5833819 := bstep (se 1 (by rfl) ⟨4375364, by rfl⟩ : syracuseStep 5833819 = 8750729) B8750729
theorem B1443055 : Blo 566810 1443055 := bstep (se 1 (by rfl) ⟨1082291, by rfl⟩ : syracuseStep 1443055 = 2164583) B2164583
theorem B853487 : Blo 566810 853487 := bstep (se 1 (by rfl) ⟨640115, by rfl⟩ : syracuseStep 853487 = 1280231) B1280231
theorem B4098347 : Blo 566810 4098347 := bstep (se 1 (by rfl) ⟨3073760, by rfl⟩ : syracuseStep 4098347 = 6147521) B6147521
theorem B855023 : Blo 566810 855023 := bstep (se 1 (by rfl) ⟨641267, by rfl⟩ : syracuseStep 855023 = 1282535) B1282535
theorem B855167 : Blo 566810 855167 := bstep (se 1 (by rfl) ⟨641375, by rfl⟩ : syracuseStep 855167 = 1282751) B1282751
theorem B855707 : Blo 566810 855707 := bstep (se 1 (by rfl) ⟨641780, by rfl⟩ : syracuseStep 855707 = 1283561) B1283561
theorem B7312031 : Blo 566810 7312031 := bstep (se 1 (by rfl) ⟨5484023, by rfl⟩ : syracuseStep 7312031 = 10968047) B10968047
theorem B1283615 : Blo 566810 1283615 := bstep (se 1 (by rfl) ⟨962711, by rfl⟩ : syracuseStep 1283615 = 1925423) B1925423
theorem B958135 : Blo 566810 958135 := bstep (se 1 (by rfl) ⟨718601, by rfl⟩ : syracuseStep 958135 = 1437203) B1437203
theorem B1024103 : Blo 566810 1024103 := bstep (se 1 (by rfl) ⟨768077, by rfl⟩ : syracuseStep 1024103 = 1536155) B1536155
theorem B1942159 : Blo 566810 1942159 := bstep (se 1 (by rfl) ⟨1456619, by rfl⟩ : syracuseStep 1942159 = 2913239) B2913239
theorem B5842367 : Blo 566810 5842367 := bstep (se 1 (by rfl) ⟨4381775, by rfl⟩ : syracuseStep 5842367 = 8763551) B8763551
theorem B566875 : Blo 566810 566875 := bstep (se 1 (by rfl) ⟨425156, by rfl⟩ : syracuseStep 566875 = 850313) B850313
theorem B566943 : Blo 566810 566943 := bstep (se 1 (by rfl) ⟨425207, by rfl⟩ : syracuseStep 566943 = 850415) B850415
theorem B567935 : Blo 566810 567935 := bstep (se 1 (by rfl) ⟨425951, by rfl⟩ : syracuseStep 567935 = 851903) B851903
theorem B3648509 : Blo 566810 3648509 := bstep (se 3 (by rfl) ⟨684095, by rfl⟩ : syracuseStep 3648509 = 1368191) B1368191
theorem B961591 : Blo 566810 961591 := bstep (se 1 (by rfl) ⟨721193, by rfl⟩ : syracuseStep 961591 = 1442387) B1442387
theorem B961895 : Blo 566810 961895 := bstep (se 1 (by rfl) ⟨721421, by rfl⟩ : syracuseStep 961895 = 1442843) B1442843
theorem B568831 : Blo 566810 568831 := bstep (se 1 (by rfl) ⟨426623, by rfl⟩ : syracuseStep 568831 = 853247) B853247
theorem B569415 : Blo 566810 569415 := bstep (se 1 (by rfl) ⟨427061, by rfl⟩ : syracuseStep 569415 = 854123) B854123
theorem B2044111 : Blo 566810 2044111 := bstep (se 1 (by rfl) ⟨1533083, by rfl⟩ : syracuseStep 2044111 = 3066167) B3066167
theorem B29636371 : Blo 566810 29636371 := bstep (se 1 (by rfl) ⟨22227278, by rfl⟩ : syracuseStep 29636371 = 44454557) B44454557
theorem B33208127 : Blo 566810 33208127 := bstep (se 1 (by rfl) ⟨24906095, by rfl⟩ : syracuseStep 33208127 = 49812191) B49812191
theorem B3424727 : Blo 566810 3424727 := bstep (se 1 (by rfl) ⟨2568545, by rfl⟩ : syracuseStep 3424727 = 5137091) B5137091
theorem B50579621 : Blo 566810 50579621 := bstep (se 4 (by rfl) ⟨4741839, by rfl⟩ : syracuseStep 50579621 = 9483679) B9483679
theorem B2869991 : Blo 566810 2869991 := bstep (se 1 (by rfl) ⟨2152493, by rfl⟩ : syracuseStep 2869991 = 4304987) B4304987
theorem B4311791 : Blo 566810 4311791 := bstep (se 1 (by rfl) ⟨3233843, by rfl⟩ : syracuseStep 4311791 = 6467687) B6467687
theorem B6474977 : Blo 566810 6474977 := bstep (se 2 (by rfl) ⟨2428116, by rfl⟩ : syracuseStep 6474977 = 4856233) B4856233
theorem B49761701 : Blo 566810 49761701 := bstep (se 4 (by rfl) ⟨4665159, by rfl⟩ : syracuseStep 49761701 = 9330319) B9330319
theorem B808871 : Blo 566810 808871 := bstep (se 1 (by rfl) ⟨606653, by rfl⟩ : syracuseStep 808871 = 1213307) B1213307
theorem B16408241 : Blo 566810 16408241 := bstep (se 2 (by rfl) ⟨6153090, by rfl⟩ : syracuseStep 16408241 = 12306181) B12306181
theorem B31121131 : Blo 566810 31121131 := bstep (se 1 (by rfl) ⟨23340848, by rfl⟩ : syracuseStep 31121131 = 46681697) B46681697
theorem B10936367 : Blo 566810 10936367 := bstep (se 1 (by rfl) ⟨8202275, by rfl⟩ : syracuseStep 10936367 = 16404551) B16404551
theorem B7266671 : Blo 566810 7266671 := bstep (se 1 (by rfl) ⟨5450003, by rfl⟩ : syracuseStep 7266671 = 10900007) B10900007
theorem B4089811 : Blo 566810 4089811 := bstep (se 1 (by rfl) ⟨3067358, by rfl⟩ : syracuseStep 4089811 = 6134717) B6134717
theorem B2877929 : Blo 566810 2877929 := bstep (se 2 (by rfl) ⟨1079223, by rfl⟩ : syracuseStep 2877929 = 2158447) B2158447
theorem B850247 : Blo 566810 850247 := bstep (se 1 (by rfl) ⟨637685, by rfl⟩ : syracuseStep 850247 = 1275371) B1275371
theorem B2161151 : Blo 566810 2161151 := bstep (se 1 (by rfl) ⟨1620863, by rfl⟩ : syracuseStep 2161151 = 3241727) B3241727
theorem B851111 : Blo 566810 851111 := bstep (se 1 (by rfl) ⟨638333, by rfl⟩ : syracuseStep 851111 = 1276667) B1276667
theorem B7799287 : Blo 566810 7799287 := bstep (se 1 (by rfl) ⟨5849465, by rfl⟩ : syracuseStep 7799287 = 11698931) B11698931
theorem B2589545 : Blo 566810 2589545 := bstep (se 2 (by rfl) ⟨971079, by rfl⟩ : syracuseStep 2589545 = 1942159) B1942159
theorem B33719747 : Blo 566810 33719747 := bstep (se 1 (by rfl) ⟨25289810, by rfl⟩ : syracuseStep 33719747 = 50579621) B50579621
theorem B855743 : Blo 566810 855743 := bstep (se 1 (by rfl) ⟨641807, by rfl⟩ : syracuseStep 855743 = 1283615) B1283615
theorem B1282121 : Blo 566810 1282121 := bstep (se 2 (by rfl) ⟨480795, by rfl⟩ : syracuseStep 1282121 = 961591) B961591
theorem B2725481 : Blo 566810 2725481 := bstep (se 2 (by rfl) ⟨1022055, by rfl⟩ : syracuseStep 2725481 = 2044111) B2044111
theorem B2432339 : Blo 566810 2432339 := bstep (se 1 (by rfl) ⟨1824254, by rfl⟩ : syracuseStep 2432339 = 3648509) B3648509
theorem B566831 : Blo 566810 566831 := bstep (se 1 (by rfl) ⟨425123, by rfl⟩ : syracuseStep 566831 = 850247) B850247
theorem B567407 : Blo 566810 567407 := bstep (se 1 (by rfl) ⟨425555, by rfl⟩ : syracuseStep 567407 = 851111) B851111
theorem B41494841 : Blo 566810 41494841 := bstep (se 2 (by rfl) ⟨15560565, by rfl⟩ : syracuseStep 41494841 = 31121131) B31121131
theorem B2730941 : Blo 566810 2730941 := bstep (se 3 (by rfl) ⟨512051, by rfl⟩ : syracuseStep 2730941 = 1024103) B1024103
theorem B568319 : Blo 566810 568319 := bstep (se 1 (by rfl) ⟨426239, by rfl⟩ : syracuseStep 568319 = 852479) B852479
theorem B568347 : Blo 566810 568347 := bstep (se 1 (by rfl) ⟨426260, by rfl⟩ : syracuseStep 568347 = 852521) B852521
theorem B568575 : Blo 566810 568575 := bstep (se 1 (by rfl) ⟨426431, by rfl⟩ : syracuseStep 568575 = 852863) B852863
theorem B568603 : Blo 566810 568603 := bstep (se 1 (by rfl) ⟨426452, by rfl⟩ : syracuseStep 568603 = 852905) B852905
theorem B568991 : Blo 566810 568991 := bstep (se 1 (by rfl) ⟨426743, by rfl⟩ : syracuseStep 568991 = 853487) B853487
theorem B7778425 : Blo 566810 7778425 := bstep (se 2 (by rfl) ⟨2916909, by rfl⟩ : syracuseStep 7778425 = 5833819) B5833819
theorem B2732231 : Blo 566810 2732231 := bstep (se 1 (by rfl) ⟨2049173, by rfl⟩ : syracuseStep 2732231 = 4098347) B4098347
theorem B1913327 : Blo 566810 1913327 := bstep (se 1 (by rfl) ⟨1434995, by rfl⟩ : syracuseStep 1913327 = 2869991) B2869991
theorem B570015 : Blo 566810 570015 := bstep (se 1 (by rfl) ⟨427511, by rfl⟩ : syracuseStep 570015 = 855023) B855023
theorem B570111 : Blo 566810 570111 := bstep (se 1 (by rfl) ⟨427583, by rfl⟩ : syracuseStep 570111 = 855167) B855167
theorem B33174467 : Blo 566810 33174467 := bstep (se 1 (by rfl) ⟨24880850, by rfl⟩ : syracuseStep 33174467 = 49761701) B49761701
theorem B570471 : Blo 566810 570471 := bstep (se 1 (by rfl) ⟨427853, by rfl⟩ : syracuseStep 570471 = 855707) B855707
theorem B5453081 : Blo 566810 5453081 := bstep (se 2 (by rfl) ⟨2044905, by rfl⟩ : syracuseStep 5453081 = 4089811) B4089811
theorem B7290911 : Blo 566810 7290911 := bstep (se 1 (by rfl) ⟨5468183, by rfl⟩ : syracuseStep 7290911 = 10936367) B10936367
theorem B1918619 : Blo 566810 1918619 := bstep (se 1 (by rfl) ⟨1438964, by rfl⟩ : syracuseStep 1918619 = 2877929) B2877929
theorem B641263 : Blo 566810 641263 := bstep (se 1 (by rfl) ⟨480947, by rfl⟩ : syracuseStep 641263 = 961895) B961895
theorem B22138751 : Blo 566810 22138751 := bstep (se 1 (by rfl) ⟨16604063, by rfl⟩ : syracuseStep 22138751 = 33208127) B33208127
theorem B9132605 : Blo 566810 9132605 := bstep (se 3 (by rfl) ⟨1712363, by rfl⟩ : syracuseStep 9132605 = 3424727) B3424727
theorem B1924073 : Blo 566810 1924073 := bstep (se 2 (by rfl) ⟨721527, by rfl⟩ : syracuseStep 1924073 = 1443055) B1443055
theorem B2874527 : Blo 566810 2874527 := bstep (se 1 (by rfl) ⟨2155895, by rfl⟩ : syracuseStep 2874527 = 4311791) B4311791
theorem B4316651 : Blo 566810 4316651 := bstep (se 1 (by rfl) ⟨3237488, by rfl⟩ : syracuseStep 4316651 = 6474977) B6474977
theorem B4874687 : Blo 566810 4874687 := bstep (se 1 (by rfl) ⟨3656015, by rfl⟩ : syracuseStep 4874687 = 7312031) B7312031
theorem B2156989 : Blo 566810 2156989 := bstep (se 3 (by rfl) ⟨404435, by rfl⟩ : syracuseStep 2156989 = 808871) B808871
theorem B10938827 : Blo 566810 10938827 := bstep (se 1 (by rfl) ⟨8204120, by rfl⟩ : syracuseStep 10938827 = 16408241) B16408241
theorem B4844447 : Blo 566810 4844447 := bstep (se 1 (by rfl) ⟨3633335, by rfl⟩ : syracuseStep 4844447 = 7266671) B7266671
theorem B3894911 : Blo 566810 3894911 := bstep (se 1 (by rfl) ⟨2921183, by rfl⟩ : syracuseStep 3894911 = 5842367) B5842367
theorem B39515161 : Blo 566810 39515161 := bstep (se 2 (by rfl) ⟨14818185, by rfl⟩ : syracuseStep 39515161 = 29636371) B29636371
theorem B1440767 : Blo 566810 1440767 := bstep (se 1 (by rfl) ⟨1080575, by rfl⟩ : syracuseStep 1440767 = 2161151) B2161151
theorem B1277513 : Blo 566810 1277513 := bstep (se 2 (by rfl) ⟨479067, by rfl⟩ : syracuseStep 1277513 = 958135) B958135
theorem B1279079 : Blo 566810 1279079 := bstep (se 1 (by rfl) ⟨959309, by rfl⟩ : syracuseStep 1279079 = 1918619) B1918619
theorem B854747 : Blo 566810 854747 := bstep (se 1 (by rfl) ⟨641060, by rfl⟩ : syracuseStep 854747 = 1282121) B1282121
theorem B855017 : Blo 566810 855017 := bstep (se 2 (by rfl) ⟨320631, by rfl⟩ : syracuseStep 855017 = 641263) B641263
theorem B89919325 : Blo 566810 89919325 := bstep (se 3 (by rfl) ⟨16859873, by rfl⟩ : syracuseStep 89919325 = 33719747) B33719747
theorem B1282715 : Blo 566810 1282715 := bstep (se 1 (by rfl) ⟨962036, by rfl⟩ : syracuseStep 1282715 = 1924073) B1924073
theorem B3249791 : Blo 566810 3249791 := bstep (se 1 (by rfl) ⟨2437343, by rfl⟩ : syracuseStep 3249791 = 4874687) B4874687
theorem B27663227 : Blo 566810 27663227 := bstep (se 1 (by rfl) ⟨20747420, by rfl⟩ : syracuseStep 27663227 = 41494841) B41494841
theorem B2596607 : Blo 566810 2596607 := bstep (se 1 (by rfl) ⟨1947455, by rfl⟩ : syracuseStep 2596607 = 3894911) B3894911
theorem B960511 : Blo 566810 960511 := bstep (se 1 (by rfl) ⟨720383, by rfl⟩ : syracuseStep 960511 = 1440767) B1440767
theorem B4860607 : Blo 566810 4860607 := bstep (se 1 (by rfl) ⟨3645455, by rfl⟩ : syracuseStep 4860607 = 7290911) B7290911
theorem B10399049 : Blo 566810 10399049 := bstep (se 2 (by rfl) ⟨3899643, by rfl⟩ : syracuseStep 10399049 = 7799287) B7799287
theorem B570495 : Blo 566810 570495 := bstep (se 1 (by rfl) ⟨427871, by rfl⟩ : syracuseStep 570495 = 855743) B855743
theorem B14759167 : Blo 566810 14759167 := bstep (se 1 (by rfl) ⟨11069375, by rfl⟩ : syracuseStep 14759167 = 22138751) B22138751
theorem B1816987 : Blo 566810 1816987 := bstep (se 1 (by rfl) ⟨1362740, by rfl⟩ : syracuseStep 1816987 = 2725481) B2725481
theorem B1916351 : Blo 566810 1916351 := bstep (se 1 (by rfl) ⟨1437263, by rfl⟩ : syracuseStep 1916351 = 2874527) B2874527
theorem B1621559 : Blo 566810 1621559 := bstep (se 1 (by rfl) ⟨1216169, by rfl⟩ : syracuseStep 1621559 = 2432339) B2432339
theorem B10371233 : Blo 566810 10371233 := bstep (se 2 (by rfl) ⟨3889212, by rfl⟩ : syracuseStep 10371233 = 7778425) B7778425
theorem B7292551 : Blo 566810 7292551 := bstep (se 1 (by rfl) ⟨5469413, by rfl⟩ : syracuseStep 7292551 = 10938827) B10938827
theorem B3229631 : Blo 566810 3229631 := bstep (se 1 (by rfl) ⟨2422223, by rfl⟩ : syracuseStep 3229631 = 4844447) B4844447
theorem B1820627 : Blo 566810 1820627 := bstep (se 1 (by rfl) ⟨1365470, by rfl⟩ : syracuseStep 1820627 = 2730941) B2730941
theorem B1821487 : Blo 566810 1821487 := bstep (se 1 (by rfl) ⟨1366115, by rfl⟩ : syracuseStep 1821487 = 2732231) B2732231
theorem B1726363 : Blo 566810 1726363 := bstep (se 1 (by rfl) ⟨1294772, by rfl⟩ : syracuseStep 1726363 = 2589545) B2589545
theorem B2875985 : Blo 566810 2875985 := bstep (se 2 (by rfl) ⟨1078494, by rfl⟩ : syracuseStep 2875985 = 2156989) B2156989
theorem B6088403 : Blo 566810 6088403 := bstep (se 1 (by rfl) ⟨4566302, by rfl⟩ : syracuseStep 6088403 = 9132605) B9132605
theorem B2877767 : Blo 566810 2877767 := bstep (se 1 (by rfl) ⟨2158325, by rfl⟩ : syracuseStep 2877767 = 4316651) B4316651
theorem B52686881 : Blo 566810 52686881 := bstep (se 2 (by rfl) ⟨19757580, by rfl⟩ : syracuseStep 52686881 = 39515161) B39515161
theorem B1275551 : Blo 566810 1275551 := bstep (se 1 (by rfl) ⟨956663, by rfl⟩ : syracuseStep 1275551 = 1913327) B1913327
theorem B22116311 : Blo 566810 22116311 := bstep (se 1 (by rfl) ⟨16587233, by rfl⟩ : syracuseStep 22116311 = 33174467) B33174467
theorem B3635387 : Blo 566810 3635387 := bstep (se 1 (by rfl) ⟨2726540, by rfl⟩ : syracuseStep 3635387 = 5453081) B5453081
theorem B851675 : Blo 566810 851675 := bstep (se 1 (by rfl) ⟨638756, by rfl⟩ : syracuseStep 851675 = 1277513) B1277513
theorem B6914155 : Blo 566810 6914155 := bstep (se 1 (by rfl) ⟨5185616, by rfl⟩ : syracuseStep 6914155 = 10371233) B10371233
theorem B852719 : Blo 566810 852719 := bstep (se 1 (by rfl) ⟨639539, by rfl⟩ : syracuseStep 852719 = 1279079) B1279079
theorem B1213751 : Blo 566810 1213751 := bstep (se 1 (by rfl) ⟨910313, by rfl⟩ : syracuseStep 1213751 = 1820627) B1820627
theorem B1280681 : Blo 566810 1280681 := bstep (se 2 (by rfl) ⟨480255, by rfl⟩ : syracuseStep 1280681 = 960511) B960511
theorem B855143 : Blo 566810 855143 := bstep (se 1 (by rfl) ⟨641357, by rfl⟩ : syracuseStep 855143 = 1282715) B1282715
theorem B2428649 : Blo 566810 2428649 := bstep (se 2 (by rfl) ⟨910743, by rfl⟩ : syracuseStep 2428649 = 1821487) B1821487
theorem B2166527 : Blo 566810 2166527 := bstep (se 1 (by rfl) ⟨1624895, by rfl⟩ : syracuseStep 2166527 = 3249791) B3249791
theorem B479569733 : Blo 566810 479569733 := bstep (se 4 (by rfl) ⟨44959662, by rfl⟩ : syracuseStep 479569733 = 89919325) B89919325
theorem B567783 : Blo 566810 567783 := bstep (se 1 (by rfl) ⟨425837, by rfl⟩ : syracuseStep 567783 = 851675) B851675
theorem B569831 : Blo 566810 569831 := bstep (se 1 (by rfl) ⟨427373, by rfl⟩ : syracuseStep 569831 = 854747) B854747
theorem B570011 : Blo 566810 570011 := bstep (se 1 (by rfl) ⟨427508, by rfl⟩ : syracuseStep 570011 = 855017) B855017
theorem B16235741 : Blo 566810 16235741 := bstep (se 3 (by rfl) ⟨3044201, by rfl⟩ : syracuseStep 16235741 = 6088403) B6088403
theorem B1917323 : Blo 566810 1917323 := bstep (se 1 (by rfl) ⟨1437992, by rfl⟩ : syracuseStep 1917323 = 2875985) B2875985
theorem B1918511 : Blo 566810 1918511 := bstep (se 1 (by rfl) ⟨1438883, by rfl⟩ : syracuseStep 1918511 = 2877767) B2877767
theorem B19678889 : Blo 566810 19678889 := bstep (se 2 (by rfl) ⟨7379583, by rfl⟩ : syracuseStep 19678889 = 14759167) B14759167
theorem B6932699 : Blo 566810 6932699 := bstep (se 1 (by rfl) ⟨5199524, by rfl⟩ : syracuseStep 6932699 = 10399049) B10399049
theorem B2153087 : Blo 566810 2153087 := bstep (se 1 (by rfl) ⟨1614815, by rfl⟩ : syracuseStep 2153087 = 3229631) B3229631
theorem B9723401 : Blo 566810 9723401 := bstep (se 2 (by rfl) ⟨3646275, by rfl⟩ : syracuseStep 9723401 = 7292551) B7292551
theorem B6480809 : Blo 566810 6480809 := bstep (se 2 (by rfl) ⟨2430303, by rfl⟩ : syracuseStep 6480809 = 4860607) B4860607
theorem B18442151 : Blo 566810 18442151 := bstep (se 1 (by rfl) ⟨13831613, by rfl⟩ : syracuseStep 18442151 = 27663227) B27663227
theorem B1731071 : Blo 566810 1731071 := bstep (se 1 (by rfl) ⟨1298303, by rfl⟩ : syracuseStep 1731071 = 2596607) B2596607
theorem B35124587 : Blo 566810 35124587 := bstep (se 1 (by rfl) ⟨26343440, by rfl⟩ : syracuseStep 35124587 = 52686881) B52686881
theorem B2422649 : Blo 566810 2422649 := bstep (se 2 (by rfl) ⟨908493, by rfl⟩ : syracuseStep 2422649 = 1816987) B1816987
theorem B850367 : Blo 566810 850367 := bstep (se 1 (by rfl) ⟨637775, by rfl⟩ : syracuseStep 850367 = 1275551) B1275551
theorem B14744207 : Blo 566810 14744207 := bstep (se 1 (by rfl) ⟨11058155, by rfl⟩ : syracuseStep 14744207 = 22116311) B22116311
theorem B2423591 : Blo 566810 2423591 := bstep (se 1 (by rfl) ⟨1817693, by rfl⟩ : syracuseStep 2423591 = 3635387) B3635387
theorem B9207269 : Blo 566810 9207269 := bstep (se 4 (by rfl) ⟨863181, by rfl⟩ : syracuseStep 9207269 = 1726363) B1726363
theorem B1277567 : Blo 566810 1277567 := bstep (se 1 (by rfl) ⟨958175, by rfl⟩ : syracuseStep 1277567 = 1916351) B1916351
theorem B1081039 : Blo 566810 1081039 := bstep (se 1 (by rfl) ⟨810779, by rfl⟩ : syracuseStep 1081039 = 1621559) B1621559
theorem B1278215 : Blo 566810 1278215 := bstep (se 1 (by rfl) ⟨958661, by rfl⟩ : syracuseStep 1278215 = 1917323) B1917323
theorem B1279007 : Blo 566810 1279007 := bstep (se 1 (by rfl) ⟨959255, by rfl⟩ : syracuseStep 1279007 = 1918511) B1918511
theorem B4621799 : Blo 566810 4621799 := bstep (se 1 (by rfl) ⟨3466349, by rfl⟩ : syracuseStep 4621799 = 6932699) B6932699
theorem B853787 : Blo 566810 853787 := bstep (se 1 (by rfl) ⟨640340, by rfl⟩ : syracuseStep 853787 = 1280681) B1280681
theorem B1444351 : Blo 566810 1444351 := bstep (se 1 (by rfl) ⟨1083263, by rfl⟩ : syracuseStep 1444351 = 2166527) B2166527
theorem B6460397 : Blo 566810 6460397 := bstep (se 3 (by rfl) ⟨1211324, by rfl⟩ : syracuseStep 6460397 = 2422649) B2422649
theorem B12294767 : Blo 566810 12294767 := bstep (se 1 (by rfl) ⟨9221075, by rfl⟩ : syracuseStep 12294767 = 18442151) B18442151
theorem B43295309 : Blo 566810 43295309 := bstep (se 3 (by rfl) ⟨8117870, by rfl⟩ : syracuseStep 43295309 = 16235741) B16235741
theorem B566911 : Blo 566810 566911 := bstep (se 1 (by rfl) ⟨425183, by rfl⟩ : syracuseStep 566911 = 850367) B850367
theorem B1615727 : Blo 566810 1615727 := bstep (se 1 (by rfl) ⟨1211795, by rfl⟩ : syracuseStep 1615727 = 2423591) B2423591
theorem B6138179 : Blo 566810 6138179 := bstep (se 1 (by rfl) ⟨4603634, by rfl⟩ : syracuseStep 6138179 = 9207269) B9207269
theorem B9218873 : Blo 566810 9218873 := bstep (se 2 (by rfl) ⟨3457077, by rfl⟩ : syracuseStep 9218873 = 6914155) B6914155
theorem B568479 : Blo 566810 568479 := bstep (se 1 (by rfl) ⟨426359, by rfl⟩ : syracuseStep 568479 = 852719) B852719
theorem B13119259 : Blo 566810 13119259 := bstep (se 1 (by rfl) ⟨9839444, by rfl⟩ : syracuseStep 13119259 = 19678889) B19678889
theorem B570095 : Blo 566810 570095 := bstep (se 1 (by rfl) ⟨427571, by rfl⟩ : syracuseStep 570095 = 855143) B855143
theorem B1619099 : Blo 566810 1619099 := bstep (se 1 (by rfl) ⟨1214324, by rfl⟩ : syracuseStep 1619099 = 2428649) B2428649
theorem B23416391 : Blo 566810 23416391 := bstep (se 1 (by rfl) ⟨17562293, by rfl⟩ : syracuseStep 23416391 = 35124587) B35124587
theorem B3236669 : Blo 566810 3236669 := bstep (se 3 (by rfl) ⟨606875, by rfl⟩ : syracuseStep 3236669 = 1213751) B1213751
theorem B1435391 : Blo 566810 1435391 := bstep (se 1 (by rfl) ⟨1076543, by rfl⟩ : syracuseStep 1435391 = 2153087) B2153087
theorem B6482267 : Blo 566810 6482267 := bstep (se 1 (by rfl) ⟨4861700, by rfl⟩ : syracuseStep 6482267 = 9723401) B9723401
theorem B4320539 : Blo 566810 4320539 := bstep (se 1 (by rfl) ⟨3240404, by rfl⟩ : syracuseStep 4320539 = 6480809) B6480809
theorem B319713155 : Blo 566810 319713155 := bstep (se 1 (by rfl) ⟨239784866, by rfl⟩ : syracuseStep 319713155 = 479569733) B479569733
theorem B4616189 : Blo 566810 4616189 := bstep (se 3 (by rfl) ⟨865535, by rfl⟩ : syracuseStep 4616189 = 1731071) B1731071
theorem B9829471 : Blo 566810 9829471 := bstep (se 1 (by rfl) ⟨7372103, by rfl⟩ : syracuseStep 9829471 = 14744207) B14744207
theorem B1441385 : Blo 566810 1441385 := bstep (se 2 (by rfl) ⟨540519, by rfl⟩ : syracuseStep 1441385 = 1081039) B1081039
theorem B851711 : Blo 566810 851711 := bstep (se 1 (by rfl) ⟨638783, by rfl⟩ : syracuseStep 851711 = 1277567) B1277567
theorem B852143 : Blo 566810 852143 := bstep (se 1 (by rfl) ⟨639107, by rfl⟩ : syracuseStep 852143 = 1278215) B1278215
theorem B852671 : Blo 566810 852671 := bstep (se 1 (by rfl) ⟨639503, by rfl⟩ : syracuseStep 852671 = 1279007) B1279007
theorem B3081199 : Blo 566810 3081199 := bstep (se 1 (by rfl) ⟨2310899, by rfl⟩ : syracuseStep 3081199 = 4621799) B4621799
theorem B8196511 : Blo 566810 8196511 := bstep (se 1 (by rfl) ⟨6147383, by rfl⟩ : syracuseStep 8196511 = 12294767) B12294767
theorem B956927 : Blo 566810 956927 := bstep (se 1 (by rfl) ⟨717695, by rfl⟩ : syracuseStep 956927 = 1435391) B1435391
theorem B960923 : Blo 566810 960923 := bstep (se 1 (by rfl) ⟨720692, by rfl⟩ : syracuseStep 960923 = 1441385) B1441385
theorem B567807 : Blo 566810 567807 := bstep (se 1 (by rfl) ⟨425855, by rfl⟩ : syracuseStep 567807 = 851711) B851711
theorem B569191 : Blo 566810 569191 := bstep (se 1 (by rfl) ⟨426893, by rfl⟩ : syracuseStep 569191 = 853787) B853787
theorem B15610927 : Blo 566810 15610927 := bstep (se 1 (by rfl) ⟨11708195, by rfl⟩ : syracuseStep 15610927 = 23416391) B23416391
theorem B4306931 : Blo 566810 4306931 := bstep (se 1 (by rfl) ⟨3230198, by rfl⟩ : syracuseStep 4306931 = 6460397) B6460397
theorem B6145915 : Blo 566810 6145915 := bstep (se 1 (by rfl) ⟨4609436, by rfl⟩ : syracuseStep 6145915 = 9218873) B9218873
theorem B213142103 : Blo 566810 213142103 := bstep (se 1 (by rfl) ⟨159856577, by rfl⟩ : syracuseStep 213142103 = 319713155) B319713155
theorem B1925801 : Blo 566810 1925801 := bstep (se 2 (by rfl) ⟨722175, by rfl⟩ : syracuseStep 1925801 = 1444351) B1444351
theorem B17492345 : Blo 566810 17492345 := bstep (se 2 (by rfl) ⟨6559629, by rfl⟩ : syracuseStep 17492345 = 13119259) B13119259
theorem B28863539 : Blo 566810 28863539 := bstep (se 1 (by rfl) ⟨21647654, by rfl⟩ : syracuseStep 28863539 = 43295309) B43295309
theorem B2157779 : Blo 566810 2157779 := bstep (se 1 (by rfl) ⟨1618334, by rfl⟩ : syracuseStep 2157779 = 3236669) B3236669
theorem B1077151 : Blo 566810 1077151 := bstep (se 1 (by rfl) ⟨807863, by rfl⟩ : syracuseStep 1077151 = 1615727) B1615727
theorem B4092119 : Blo 566810 4092119 := bstep (se 1 (by rfl) ⟨3069089, by rfl⟩ : syracuseStep 4092119 = 6138179) B6138179
theorem B4321511 : Blo 566810 4321511 := bstep (se 1 (by rfl) ⟨3241133, by rfl⟩ : syracuseStep 4321511 = 6482267) B6482267
theorem B2880359 : Blo 566810 2880359 := bstep (se 1 (by rfl) ⟨2160269, by rfl⟩ : syracuseStep 2880359 = 4320539) B4320539
theorem B3077459 : Blo 566810 3077459 := bstep (se 1 (by rfl) ⟨2308094, by rfl⟩ : syracuseStep 3077459 = 4616189) B4616189
theorem B1079399 : Blo 566810 1079399 := bstep (se 1 (by rfl) ⟨809549, by rfl⟩ : syracuseStep 1079399 = 1619099) B1619099
theorem B13105961 : Blo 566810 13105961 := bstep (se 2 (by rfl) ⟨4914735, by rfl⟩ : syracuseStep 13105961 = 9829471) B9829471
theorem B8194553 : Blo 566810 8194553 := bstep (se 2 (by rfl) ⟨3072957, by rfl⟩ : syracuseStep 8194553 = 6145915) B6145915
theorem B1283867 : Blo 566810 1283867 := bstep (se 1 (by rfl) ⟨962900, by rfl⟩ : syracuseStep 1283867 = 1925801) B1925801
theorem B20814569 : Blo 566810 20814569 := bstep (se 2 (by rfl) ⟨7805463, by rfl⟩ : syracuseStep 20814569 = 15610927) B15610927
theorem B19242359 : Blo 566810 19242359 := bstep (se 1 (by rfl) ⟨14431769, by rfl⟩ : syracuseStep 19242359 = 28863539) B28863539
theorem B2728079 : Blo 566810 2728079 := bstep (se 1 (by rfl) ⟨2046059, by rfl⟩ : syracuseStep 2728079 = 4092119) B4092119
theorem B568095 : Blo 566810 568095 := bstep (se 1 (by rfl) ⟨426071, by rfl⟩ : syracuseStep 568095 = 852143) B852143
theorem B568447 : Blo 566810 568447 := bstep (se 1 (by rfl) ⟨426335, by rfl⟩ : syracuseStep 568447 = 852671) B852671
theorem B4108265 : Blo 566810 4108265 := bstep (se 2 (by rfl) ⟨1540599, by rfl⟩ : syracuseStep 4108265 = 3081199) B3081199
theorem B142094735 : Blo 566810 142094735 := bstep (se 1 (by rfl) ⟨106571051, by rfl⟩ : syracuseStep 142094735 = 213142103) B213142103
theorem B637951 : Blo 566810 637951 := bstep (se 1 (by rfl) ⟨478463, by rfl⟩ : syracuseStep 637951 = 956927) B956927
theorem B10928681 : Blo 566810 10928681 := bstep (se 2 (by rfl) ⟨4098255, by rfl⟩ : syracuseStep 10928681 = 8196511) B8196511
theorem B640615 : Blo 566810 640615 := bstep (se 1 (by rfl) ⟨480461, by rfl⟩ : syracuseStep 640615 = 960923) B960923
theorem B1920239 : Blo 566810 1920239 := bstep (se 1 (by rfl) ⟨1440179, by rfl⟩ : syracuseStep 1920239 = 2880359) B2880359
theorem B2051639 : Blo 566810 2051639 := bstep (se 1 (by rfl) ⟨1538729, by rfl⟩ : syracuseStep 2051639 = 3077459) B3077459
theorem B2871287 : Blo 566810 2871287 := bstep (se 1 (by rfl) ⟨2153465, by rfl⟩ : syracuseStep 2871287 = 4306931) B4306931
theorem B8737307 : Blo 566810 8737307 := bstep (se 1 (by rfl) ⟨6552980, by rfl⟩ : syracuseStep 8737307 = 13105961) B13105961
theorem B1436201 : Blo 566810 1436201 := bstep (se 2 (by rfl) ⟨538575, by rfl⟩ : syracuseStep 1436201 = 1077151) B1077151
theorem B11661563 : Blo 566810 11661563 := bstep (se 1 (by rfl) ⟨8746172, by rfl⟩ : syracuseStep 11661563 = 17492345) B17492345
theorem B1438519 : Blo 566810 1438519 := bstep (se 1 (by rfl) ⟨1078889, by rfl⟩ : syracuseStep 1438519 = 2157779) B2157779
theorem B2881007 : Blo 566810 2881007 := bstep (se 1 (by rfl) ⟨2160755, by rfl⟩ : syracuseStep 2881007 = 4321511) B4321511
theorem B719599 : Blo 566810 719599 := bstep (se 1 (by rfl) ⟨539699, by rfl⟩ : syracuseStep 719599 = 1079399) B1079399
theorem B854153 : Blo 566810 854153 := bstep (se 2 (by rfl) ⟨320307, by rfl⟩ : syracuseStep 854153 = 640615) B640615
theorem B1280159 : Blo 566810 1280159 := bstep (se 1 (by rfl) ⟨960119, by rfl⟩ : syracuseStep 1280159 = 1920239) B1920239
theorem B855911 : Blo 566810 855911 := bstep (se 1 (by rfl) ⟨641933, by rfl⟩ : syracuseStep 855911 = 1283867) B1283867
theorem B957467 : Blo 566810 957467 := bstep (se 1 (by rfl) ⟨718100, by rfl⟩ : syracuseStep 957467 = 1436201) B1436201
theorem B7774375 : Blo 566810 7774375 := bstep (se 1 (by rfl) ⟨5830781, by rfl⟩ : syracuseStep 7774375 = 11661563) B11661563
theorem B959465 : Blo 566810 959465 := bstep (se 2 (by rfl) ⟨359799, by rfl⟩ : syracuseStep 959465 = 719599) B719599
theorem B7285787 : Blo 566810 7285787 := bstep (se 1 (by rfl) ⟨5464340, by rfl⟩ : syracuseStep 7285787 = 10928681) B10928681
theorem B1914191 : Blo 566810 1914191 := bstep (se 1 (by rfl) ⟨1435643, by rfl⟩ : syracuseStep 1914191 = 2871287) B2871287
theorem B13876379 : Blo 566810 13876379 := bstep (se 1 (by rfl) ⟨10407284, by rfl⟩ : syracuseStep 13876379 = 20814569) B20814569
theorem B12828239 : Blo 566810 12828239 := bstep (se 1 (by rfl) ⟨9621179, by rfl⟩ : syracuseStep 12828239 = 19242359) B19242359
theorem B1818719 : Blo 566810 1818719 := bstep (se 1 (by rfl) ⟨1364039, by rfl⟩ : syracuseStep 1818719 = 2728079) B2728079
theorem B1918025 : Blo 566810 1918025 := bstep (se 2 (by rfl) ⟨719259, by rfl⟩ : syracuseStep 1918025 = 1438519) B1438519
theorem B2738843 : Blo 566810 2738843 := bstep (se 1 (by rfl) ⟨2054132, by rfl⟩ : syracuseStep 2738843 = 4108265) B4108265
theorem B1920671 : Blo 566810 1920671 := bstep (se 1 (by rfl) ⟨1440503, by rfl⟩ : syracuseStep 1920671 = 2881007) B2881007
theorem B5463035 : Blo 566810 5463035 := bstep (se 1 (by rfl) ⟨4097276, by rfl⟩ : syracuseStep 5463035 = 8194553) B8194553
theorem B1367759 : Blo 566810 1367759 := bstep (se 1 (by rfl) ⟨1025819, by rfl⟩ : syracuseStep 1367759 = 2051639) B2051639
theorem B5824871 : Blo 566810 5824871 := bstep (se 1 (by rfl) ⟨4368653, by rfl⟩ : syracuseStep 5824871 = 8737307) B8737307
theorem B94729823 : Blo 566810 94729823 := bstep (se 1 (by rfl) ⟨71047367, by rfl⟩ : syracuseStep 94729823 = 142094735) B142094735
theorem B850601 : Blo 566810 850601 := bstep (se 2 (by rfl) ⟨318975, by rfl⟩ : syracuseStep 850601 = 637951) B637951
theorem B1212479 : Blo 566810 1212479 := bstep (se 1 (by rfl) ⟨909359, by rfl⟩ : syracuseStep 1212479 = 1818719) B1818719
theorem B1278683 : Blo 566810 1278683 := bstep (se 1 (by rfl) ⟨959012, by rfl⟩ : syracuseStep 1278683 = 1918025) B1918025
theorem B853439 : Blo 566810 853439 := bstep (se 1 (by rfl) ⟨640079, by rfl⟩ : syracuseStep 853439 = 1280159) B1280159
theorem B1280447 : Blo 566810 1280447 := bstep (se 1 (by rfl) ⟨960335, by rfl⟩ : syracuseStep 1280447 = 1920671) B1920671
theorem B3642023 : Blo 566810 3642023 := bstep (se 1 (by rfl) ⟨2731517, by rfl⟩ : syracuseStep 3642023 = 5463035) B5463035
theorem B4857191 : Blo 566810 4857191 := bstep (se 1 (by rfl) ⟨3642893, by rfl⟩ : syracuseStep 4857191 = 7285787) B7285787
theorem B63153215 : Blo 566810 63153215 := bstep (se 1 (by rfl) ⟨47364911, by rfl⟩ : syracuseStep 63153215 = 94729823) B94729823
theorem B567067 : Blo 566810 567067 := bstep (se 1 (by rfl) ⟨425300, by rfl⟩ : syracuseStep 567067 = 850601) B850601
theorem B9250919 : Blo 566810 9250919 := bstep (se 1 (by rfl) ⟨6938189, by rfl⟩ : syracuseStep 9250919 = 13876379) B13876379
theorem B10365833 : Blo 566810 10365833 := bstep (se 2 (by rfl) ⟨3887187, by rfl⟩ : syracuseStep 10365833 = 7774375) B7774375
theorem B569435 : Blo 566810 569435 := bstep (se 1 (by rfl) ⟨427076, by rfl⟩ : syracuseStep 569435 = 854153) B854153
theorem B570607 : Blo 566810 570607 := bstep (se 1 (by rfl) ⟨427955, by rfl⟩ : syracuseStep 570607 = 855911) B855911
theorem B638311 : Blo 566810 638311 := bstep (se 1 (by rfl) ⟨478733, by rfl⟩ : syracuseStep 638311 = 957467) B957467
theorem B3883247 : Blo 566810 3883247 := bstep (se 1 (by rfl) ⟨2912435, by rfl⟩ : syracuseStep 3883247 = 5824871) B5824871
theorem B639643 : Blo 566810 639643 := bstep (se 1 (by rfl) ⟨479732, by rfl⟩ : syracuseStep 639643 = 959465) B959465
theorem B1825895 : Blo 566810 1825895 := bstep (se 1 (by rfl) ⟨1369421, by rfl⟩ : syracuseStep 1825895 = 2738843) B2738843
theorem B911839 : Blo 566810 911839 := bstep (se 1 (by rfl) ⟨683879, by rfl⟩ : syracuseStep 911839 = 1367759) B1367759
theorem B1276127 : Blo 566810 1276127 := bstep (se 1 (by rfl) ⟨957095, by rfl⟩ : syracuseStep 1276127 = 1914191) B1914191
theorem B8552159 : Blo 566810 8552159 := bstep (se 1 (by rfl) ⟨6414119, by rfl⟩ : syracuseStep 8552159 = 12828239) B12828239
theorem B2588831 : Blo 566810 2588831 := bstep (se 1 (by rfl) ⟨1941623, by rfl⟩ : syracuseStep 2588831 = 3883247) B3883247
theorem B852455 : Blo 566810 852455 := bstep (se 1 (by rfl) ⟨639341, by rfl⟩ : syracuseStep 852455 = 1278683) B1278683
theorem B852857 : Blo 566810 852857 := bstep (se 2 (by rfl) ⟨319821, by rfl⟩ : syracuseStep 852857 = 639643) B639643
theorem B853631 : Blo 566810 853631 := bstep (se 1 (by rfl) ⟨640223, by rfl⟩ : syracuseStep 853631 = 1280447) B1280447
theorem B2428015 : Blo 566810 2428015 := bstep (se 1 (by rfl) ⟨1821011, by rfl⟩ : syracuseStep 2428015 = 3642023) B3642023
theorem B1215785 : Blo 566810 1215785 := bstep (se 2 (by rfl) ⟨455919, by rfl⟩ : syracuseStep 1215785 = 911839) B911839
theorem B1217263 : Blo 566810 1217263 := bstep (se 1 (by rfl) ⟨912947, by rfl⟩ : syracuseStep 1217263 = 1825895) B1825895
theorem B6167279 : Blo 566810 6167279 := bstep (se 1 (by rfl) ⟨4625459, by rfl⟩ : syracuseStep 6167279 = 9250919) B9250919
theorem B568959 : Blo 566810 568959 := bstep (se 1 (by rfl) ⟨426719, by rfl⟩ : syracuseStep 568959 = 853439) B853439
theorem B808319 : Blo 566810 808319 := bstep (se 1 (by rfl) ⟨606239, by rfl⟩ : syracuseStep 808319 = 1212479) B1212479
theorem B3238127 : Blo 566810 3238127 := bstep (se 1 (by rfl) ⟨2428595, by rfl⟩ : syracuseStep 3238127 = 4857191) B4857191
theorem B42102143 : Blo 566810 42102143 := bstep (se 1 (by rfl) ⟨31576607, by rfl⟩ : syracuseStep 42102143 = 63153215) B63153215
theorem B6910555 : Blo 566810 6910555 := bstep (se 1 (by rfl) ⟨5182916, by rfl⟩ : syracuseStep 6910555 = 10365833) B10365833
theorem B850751 : Blo 566810 850751 := bstep (se 1 (by rfl) ⟨638063, by rfl⟩ : syracuseStep 850751 = 1276127) B1276127
theorem B851081 : Blo 566810 851081 := bstep (se 2 (by rfl) ⟨319155, by rfl⟩ : syracuseStep 851081 = 638311) B638311
theorem B5701439 : Blo 566810 5701439 := bstep (se 1 (by rfl) ⟨4276079, by rfl⟩ : syracuseStep 5701439 = 8552159) B8552159
theorem B9214073 : Blo 566810 9214073 := bstep (se 2 (by rfl) ⟨3455277, by rfl⟩ : syracuseStep 9214073 = 6910555) B6910555
theorem B567167 : Blo 566810 567167 := bstep (se 1 (by rfl) ⟨425375, by rfl⟩ : syracuseStep 567167 = 850751) B850751
theorem B567387 : Blo 566810 567387 := bstep (se 1 (by rfl) ⟨425540, by rfl⟩ : syracuseStep 567387 = 851081) B851081
theorem B568303 : Blo 566810 568303 := bstep (se 1 (by rfl) ⟨426227, by rfl⟩ : syracuseStep 568303 = 852455) B852455
theorem B568571 : Blo 566810 568571 := bstep (se 1 (by rfl) ⟨426428, by rfl⟩ : syracuseStep 568571 = 852857) B852857
theorem B569087 : Blo 566810 569087 := bstep (se 1 (by rfl) ⟨426815, by rfl⟩ : syracuseStep 569087 = 853631) B853631
theorem B4111519 : Blo 566810 4111519 := bstep (se 1 (by rfl) ⟨3083639, by rfl⟩ : syracuseStep 4111519 = 6167279) B6167279
theorem B1623017 : Blo 566810 1623017 := bstep (se 2 (by rfl) ⟨608631, by rfl⟩ : syracuseStep 1623017 = 1217263) B1217263
theorem B28068095 : Blo 566810 28068095 := bstep (se 1 (by rfl) ⟨21051071, by rfl⟩ : syracuseStep 28068095 = 42102143) B42102143
theorem B1725887 : Blo 566810 1725887 := bstep (se 1 (by rfl) ⟨1294415, by rfl⟩ : syracuseStep 1725887 = 2588831) B2588831
theorem B810523 : Blo 566810 810523 := bstep (se 1 (by rfl) ⟨607892, by rfl⟩ : syracuseStep 810523 = 1215785) B1215785
theorem B2155517 : Blo 566810 2155517 := bstep (se 3 (by rfl) ⟨404159, by rfl⟩ : syracuseStep 2155517 = 808319) B808319
theorem B3237353 : Blo 566810 3237353 := bstep (se 2 (by rfl) ⟨1214007, by rfl⟩ : syracuseStep 3237353 = 2428015) B2428015
theorem B2158751 : Blo 566810 2158751 := bstep (se 1 (by rfl) ⟨1619063, by rfl⟩ : syracuseStep 2158751 = 3238127) B3238127
theorem B15203837 : Blo 566810 15203837 := bstep (se 3 (by rfl) ⟨2850719, by rfl⟩ : syracuseStep 15203837 = 5701439) B5701439
theorem B1082011 : Blo 566810 1082011 := bstep (se 1 (by rfl) ⟨811508, by rfl⟩ : syracuseStep 1082011 = 1623017) B1623017
theorem B18712063 : Blo 566810 18712063 := bstep (se 1 (by rfl) ⟨14034047, by rfl⟩ : syracuseStep 18712063 = 28068095) B28068095
theorem B5482025 : Blo 566810 5482025 := bstep (se 2 (by rfl) ⟨2055759, by rfl⟩ : syracuseStep 5482025 = 4111519) B4111519
theorem B10135891 : Blo 566810 10135891 := bstep (se 1 (by rfl) ⟨7601918, by rfl⟩ : syracuseStep 10135891 = 15203837) B15203837
theorem B4602365 : Blo 566810 4602365 := bstep (se 3 (by rfl) ⟨862943, by rfl⟩ : syracuseStep 4602365 = 1725887) B1725887
theorem B6142715 : Blo 566810 6142715 := bstep (se 1 (by rfl) ⟨4607036, by rfl⟩ : syracuseStep 6142715 = 9214073) B9214073
theorem B1437011 : Blo 566810 1437011 := bstep (se 1 (by rfl) ⟨1077758, by rfl⟩ : syracuseStep 1437011 = 2155517) B2155517
theorem B2158235 : Blo 566810 2158235 := bstep (se 1 (by rfl) ⟨1618676, by rfl⟩ : syracuseStep 2158235 = 3237353) B3237353
theorem B1439167 : Blo 566810 1439167 := bstep (se 1 (by rfl) ⟨1079375, by rfl⟩ : syracuseStep 1439167 = 2158751) B2158751
theorem B1080697 : Blo 566810 1080697 := bstep (se 2 (by rfl) ⟨405261, by rfl⟩ : syracuseStep 1080697 = 810523) B810523
theorem B1442681 : Blo 566810 1442681 := bstep (se 2 (by rfl) ⟨541005, by rfl⟩ : syracuseStep 1442681 = 1082011) B1082011
theorem B958007 : Blo 566810 958007 := bstep (se 1 (by rfl) ⟨718505, by rfl⟩ : syracuseStep 958007 = 1437011) B1437011
theorem B24949417 : Blo 566810 24949417 := bstep (se 2 (by rfl) ⟨9356031, by rfl⟩ : syracuseStep 24949417 = 18712063) B18712063
theorem B13514521 : Blo 566810 13514521 := bstep (se 2 (by rfl) ⟨5067945, by rfl⟩ : syracuseStep 13514521 = 10135891) B10135891
theorem B3654683 : Blo 566810 3654683 := bstep (se 1 (by rfl) ⟨2741012, by rfl⟩ : syracuseStep 3654683 = 5482025) B5482025
theorem B1918889 : Blo 566810 1918889 := bstep (se 2 (by rfl) ⟨719583, by rfl⟩ : syracuseStep 1918889 = 1439167) B1439167
theorem B3068243 : Blo 566810 3068243 := bstep (se 1 (by rfl) ⟨2301182, by rfl⟩ : syracuseStep 3068243 = 4602365) B4602365
theorem B1438823 : Blo 566810 1438823 := bstep (se 1 (by rfl) ⟨1079117, by rfl⟩ : syracuseStep 1438823 = 2158235) B2158235
theorem B1440929 : Blo 566810 1440929 := bstep (se 2 (by rfl) ⟨540348, by rfl⟩ : syracuseStep 1440929 = 1080697) B1080697
theorem B4095143 : Blo 566810 4095143 := bstep (se 1 (by rfl) ⟨3071357, by rfl⟩ : syracuseStep 4095143 = 6142715) B6142715
theorem B1279259 : Blo 566810 1279259 := bstep (se 1 (by rfl) ⟨959444, by rfl⟩ : syracuseStep 1279259 = 1918889) B1918889
theorem B33265889 : Blo 566810 33265889 := bstep (se 2 (by rfl) ⟨12474708, by rfl⟩ : syracuseStep 33265889 = 24949417) B24949417
theorem B959215 : Blo 566810 959215 := bstep (se 1 (by rfl) ⟨719411, by rfl⟩ : syracuseStep 959215 = 1438823) B1438823
theorem B960619 : Blo 566810 960619 := bstep (se 1 (by rfl) ⟨720464, by rfl⟩ : syracuseStep 960619 = 1440929) B1440929
theorem B2730095 : Blo 566810 2730095 := bstep (se 1 (by rfl) ⟨2047571, by rfl⟩ : syracuseStep 2730095 = 4095143) B4095143
theorem B961787 : Blo 566810 961787 := bstep (se 1 (by rfl) ⟨721340, by rfl⟩ : syracuseStep 961787 = 1442681) B1442681
theorem B2436455 : Blo 566810 2436455 := bstep (se 1 (by rfl) ⟨1827341, by rfl⟩ : syracuseStep 2436455 = 3654683) B3654683
theorem B2045495 : Blo 566810 2045495 := bstep (se 1 (by rfl) ⟨1534121, by rfl⟩ : syracuseStep 2045495 = 3068243) B3068243
theorem B638671 : Blo 566810 638671 := bstep (se 1 (by rfl) ⟨479003, by rfl⟩ : syracuseStep 638671 = 958007) B958007
theorem B18019361 : Blo 566810 18019361 := bstep (se 2 (by rfl) ⟨6757260, by rfl⟩ : syracuseStep 18019361 = 13514521) B13514521
theorem B852839 : Blo 566810 852839 := bstep (se 1 (by rfl) ⟨639629, by rfl⟩ : syracuseStep 852839 = 1279259) B1279259
theorem B1278953 : Blo 566810 1278953 := bstep (se 2 (by rfl) ⟨479607, by rfl⟩ : syracuseStep 1278953 = 959215) B959215
theorem B1280825 : Blo 566810 1280825 := bstep (se 2 (by rfl) ⟨480309, by rfl⟩ : syracuseStep 1280825 = 960619) B960619
theorem B1820063 : Blo 566810 1820063 := bstep (se 1 (by rfl) ⟨1365047, by rfl⟩ : syracuseStep 1820063 = 2730095) B2730095
theorem B641191 : Blo 566810 641191 := bstep (se 1 (by rfl) ⟨480893, by rfl⟩ : syracuseStep 641191 = 961787) B961787
theorem B1624303 : Blo 566810 1624303 := bstep (se 1 (by rfl) ⟨1218227, by rfl⟩ : syracuseStep 1624303 = 2436455) B2436455
theorem B12012907 : Blo 566810 12012907 := bstep (se 1 (by rfl) ⟨9009680, by rfl⟩ : syracuseStep 12012907 = 18019361) B18019361
theorem B1363663 : Blo 566810 1363663 := bstep (se 1 (by rfl) ⟨1022747, by rfl⟩ : syracuseStep 1363663 = 2045495) B2045495
theorem B22177259 : Blo 566810 22177259 := bstep (se 1 (by rfl) ⟨16632944, by rfl⟩ : syracuseStep 22177259 = 33265889) B33265889
theorem B851561 : Blo 566810 851561 := bstep (se 2 (by rfl) ⟨319335, by rfl⟩ : syracuseStep 851561 = 638671) B638671
theorem B852635 : Blo 566810 852635 := bstep (se 1 (by rfl) ⟨639476, by rfl⟩ : syracuseStep 852635 = 1278953) B1278953
theorem B1213375 : Blo 566810 1213375 := bstep (se 1 (by rfl) ⟨910031, by rfl⟩ : syracuseStep 1213375 = 1820063) B1820063
theorem B853883 : Blo 566810 853883 := bstep (se 1 (by rfl) ⟨640412, by rfl⟩ : syracuseStep 853883 = 1280825) B1280825
theorem B854921 : Blo 566810 854921 := bstep (se 2 (by rfl) ⟨320595, by rfl⟩ : syracuseStep 854921 = 641191) B641191
theorem B2165737 : Blo 566810 2165737 := bstep (se 2 (by rfl) ⟨812151, by rfl⟩ : syracuseStep 2165737 = 1624303) B1624303
theorem B14784839 : Blo 566810 14784839 := bstep (se 1 (by rfl) ⟨11088629, by rfl⟩ : syracuseStep 14784839 = 22177259) B22177259
theorem B567707 : Blo 566810 567707 := bstep (se 1 (by rfl) ⟨425780, by rfl⟩ : syracuseStep 567707 = 851561) B851561
theorem B568559 : Blo 566810 568559 := bstep (se 1 (by rfl) ⟨426419, by rfl⟩ : syracuseStep 568559 = 852839) B852839
theorem B1818217 : Blo 566810 1818217 := bstep (se 2 (by rfl) ⟨681831, by rfl⟩ : syracuseStep 1818217 = 1363663) B1363663
theorem B16017209 : Blo 566810 16017209 := bstep (se 2 (by rfl) ⟨6006453, by rfl⟩ : syracuseStep 16017209 = 12012907) B12012907
theorem B2887649 : Blo 566810 2887649 := bstep (se 2 (by rfl) ⟨1082868, by rfl⟩ : syracuseStep 2887649 = 2165737) B2165737
theorem B568423 : Blo 566810 568423 := bstep (se 1 (by rfl) ⟨426317, by rfl⟩ : syracuseStep 568423 = 852635) B852635
theorem B569255 : Blo 566810 569255 := bstep (se 1 (by rfl) ⟨426941, by rfl⟩ : syracuseStep 569255 = 853883) B853883
theorem B1617833 : Blo 566810 1617833 := bstep (se 2 (by rfl) ⟨606687, by rfl⟩ : syracuseStep 1617833 = 1213375) B1213375
theorem B569947 : Blo 566810 569947 := bstep (se 1 (by rfl) ⟨427460, by rfl⟩ : syracuseStep 569947 = 854921) B854921
theorem B9856559 : Blo 566810 9856559 := bstep (se 1 (by rfl) ⟨7392419, by rfl⟩ : syracuseStep 9856559 = 14784839) B14784839
theorem B10678139 : Blo 566810 10678139 := bstep (se 1 (by rfl) ⟨8008604, by rfl⟩ : syracuseStep 10678139 = 16017209) B16017209
theorem B9697157 : Blo 566810 9697157 := bstep (se 4 (by rfl) ⟨909108, by rfl⟩ : syracuseStep 9697157 = 1818217) B1818217
theorem B7118759 : Blo 566810 7118759 := bstep (se 1 (by rfl) ⟨5339069, by rfl⟩ : syracuseStep 7118759 = 10678139) B10678139
theorem B6464771 : Blo 566810 6464771 := bstep (se 1 (by rfl) ⟨4848578, by rfl⟩ : syracuseStep 6464771 = 9697157) B9697157
theorem B6571039 : Blo 566810 6571039 := bstep (se 1 (by rfl) ⟨4928279, by rfl⟩ : syracuseStep 6571039 = 9856559) B9856559
theorem B4314221 : Blo 566810 4314221 := bstep (se 3 (by rfl) ⟨808916, by rfl⟩ : syracuseStep 4314221 = 1617833) B1617833
theorem B1925099 : Blo 566810 1925099 := bstep (se 1 (by rfl) ⟨1443824, by rfl⟩ : syracuseStep 1925099 = 2887649) B2887649
theorem B1283399 : Blo 566810 1283399 := bstep (se 1 (by rfl) ⟨962549, by rfl⟩ : syracuseStep 1283399 = 1925099) B1925099
theorem B18983357 : Blo 566810 18983357 := bstep (se 3 (by rfl) ⟨3559379, by rfl⟩ : syracuseStep 18983357 = 7118759) B7118759
theorem B8761385 : Blo 566810 8761385 := bstep (se 2 (by rfl) ⟨3285519, by rfl⟩ : syracuseStep 8761385 = 6571039) B6571039
theorem B4309847 : Blo 566810 4309847 := bstep (se 1 (by rfl) ⟨3232385, by rfl⟩ : syracuseStep 4309847 = 6464771) B6464771
theorem B2876147 : Blo 566810 2876147 := bstep (se 1 (by rfl) ⟨2157110, by rfl⟩ : syracuseStep 2876147 = 4314221) B4314221
theorem B855599 : Blo 566810 855599 := bstep (se 1 (by rfl) ⟨641699, by rfl⟩ : syracuseStep 855599 = 1283399) B1283399
theorem B12655571 : Blo 566810 12655571 := bstep (se 1 (by rfl) ⟨9491678, by rfl⟩ : syracuseStep 12655571 = 18983357) B18983357
theorem B5840923 : Blo 566810 5840923 := bstep (se 1 (by rfl) ⟨4380692, by rfl⟩ : syracuseStep 5840923 = 8761385) B8761385
theorem B1917431 : Blo 566810 1917431 := bstep (se 1 (by rfl) ⟨1438073, by rfl⟩ : syracuseStep 1917431 = 2876147) B2876147
theorem B2873231 : Blo 566810 2873231 := bstep (se 1 (by rfl) ⟨2154923, by rfl⟩ : syracuseStep 2873231 = 4309847) B4309847
theorem B1278287 : Blo 566810 1278287 := bstep (se 1 (by rfl) ⟨958715, by rfl⟩ : syracuseStep 1278287 = 1917431) B1917431
theorem B570399 : Blo 566810 570399 := bstep (se 1 (by rfl) ⟨427799, by rfl⟩ : syracuseStep 570399 = 855599) B855599
theorem B1915487 : Blo 566810 1915487 := bstep (se 1 (by rfl) ⟨1436615, by rfl⟩ : syracuseStep 1915487 = 2873231) B2873231
theorem B134992757 : Blo 566810 134992757 := bstep (se 5 (by rfl) ⟨6327785, by rfl⟩ : syracuseStep 134992757 = 12655571) B12655571
theorem B7787897 : Blo 566810 7787897 := bstep (se 2 (by rfl) ⟨2920461, by rfl⟩ : syracuseStep 7787897 = 5840923) B5840923
theorem B852191 : Blo 566810 852191 := bstep (se 1 (by rfl) ⟨639143, by rfl⟩ : syracuseStep 852191 = 1278287) B1278287
theorem B89995171 : Blo 566810 89995171 := bstep (se 1 (by rfl) ⟨67496378, by rfl⟩ : syracuseStep 89995171 = 134992757) B134992757
theorem B5191931 : Blo 566810 5191931 := bstep (se 1 (by rfl) ⟨3893948, by rfl⟩ : syracuseStep 5191931 = 7787897) B7787897
theorem B1276991 : Blo 566810 1276991 := bstep (se 1 (by rfl) ⟨957743, by rfl⟩ : syracuseStep 1276991 = 1915487) B1915487
theorem B568127 : Blo 566810 568127 := bstep (se 1 (by rfl) ⟨426095, by rfl⟩ : syracuseStep 568127 = 852191) B852191
theorem B3461287 : Blo 566810 3461287 := bstep (se 1 (by rfl) ⟨2595965, by rfl⟩ : syracuseStep 3461287 = 5191931) B5191931
theorem B119993561 : Blo 566810 119993561 := bstep (se 2 (by rfl) ⟨44997585, by rfl⟩ : syracuseStep 119993561 = 89995171) B89995171
theorem B851327 : Blo 566810 851327 := bstep (se 1 (by rfl) ⟨638495, by rfl⟩ : syracuseStep 851327 = 1276991) B1276991
theorem B79995707 : Blo 566810 79995707 := bstep (se 1 (by rfl) ⟨59996780, by rfl⟩ : syracuseStep 79995707 = 119993561) B119993561
theorem B567551 : Blo 566810 567551 := bstep (se 1 (by rfl) ⟨425663, by rfl⟩ : syracuseStep 567551 = 851327) B851327
theorem B4615049 : Blo 566810 4615049 := bstep (se 2 (by rfl) ⟨1730643, by rfl⟩ : syracuseStep 4615049 = 3461287) B3461287
theorem B53330471 : Blo 566810 53330471 := bstep (se 1 (by rfl) ⟨39997853, by rfl⟩ : syracuseStep 53330471 = 79995707) B79995707
theorem B3076699 : Blo 566810 3076699 := bstep (se 1 (by rfl) ⟨2307524, by rfl⟩ : syracuseStep 3076699 = 4615049) B4615049
theorem B35553647 : Blo 566810 35553647 := bstep (se 1 (by rfl) ⟨26665235, by rfl⟩ : syracuseStep 35553647 = 53330471) B53330471
theorem B4102265 : Blo 566810 4102265 := bstep (se 2 (by rfl) ⟨1538349, by rfl⟩ : syracuseStep 4102265 = 3076699) B3076699
theorem B23702431 : Blo 566810 23702431 := bstep (se 1 (by rfl) ⟨17776823, by rfl⟩ : syracuseStep 23702431 = 35553647) B35553647
theorem B10939373 : Blo 566810 10939373 := bstep (se 3 (by rfl) ⟨2051132, by rfl⟩ : syracuseStep 10939373 = 4102265) B4102265
theorem B31603241 : Blo 566810 31603241 := bstep (se 2 (by rfl) ⟨11851215, by rfl⟩ : syracuseStep 31603241 = 23702431) B23702431
theorem B7292915 : Blo 566810 7292915 := bstep (se 1 (by rfl) ⟨5469686, by rfl⟩ : syracuseStep 7292915 = 10939373) B10939373
theorem B4861943 : Blo 566810 4861943 := bstep (se 1 (by rfl) ⟨3646457, by rfl⟩ : syracuseStep 4861943 = 7292915) B7292915
theorem B84275309 : Blo 566810 84275309 := bstep (se 3 (by rfl) ⟨15801620, by rfl⟩ : syracuseStep 84275309 = 31603241) B31603241
theorem B56183539 : Blo 566810 56183539 := bstep (se 1 (by rfl) ⟨42137654, by rfl⟩ : syracuseStep 56183539 = 84275309) B84275309
theorem B3241295 : Blo 566810 3241295 := bstep (se 1 (by rfl) ⟨2430971, by rfl⟩ : syracuseStep 3241295 = 4861943) B4861943
theorem B74911385 : Blo 566810 74911385 := bstep (se 2 (by rfl) ⟨28091769, by rfl⟩ : syracuseStep 74911385 = 56183539) B56183539
theorem B2160863 : Blo 566810 2160863 := bstep (se 1 (by rfl) ⟨1620647, by rfl⟩ : syracuseStep 2160863 = 3241295) B3241295
theorem B49940923 : Blo 566810 49940923 := bstep (se 1 (by rfl) ⟨37455692, by rfl⟩ : syracuseStep 49940923 = 74911385) B74911385
theorem B1440575 : Blo 566810 1440575 := bstep (se 1 (by rfl) ⟨1080431, by rfl⟩ : syracuseStep 1440575 = 2160863) B2160863
theorem B66587897 : Blo 566810 66587897 := bstep (se 2 (by rfl) ⟨24970461, by rfl⟩ : syracuseStep 66587897 = 49940923) B49940923
theorem B960383 : Blo 566810 960383 := bstep (se 1 (by rfl) ⟨720287, by rfl⟩ : syracuseStep 960383 = 1440575) B1440575
theorem B640255 : Blo 566810 640255 := bstep (se 1 (by rfl) ⟨480191, by rfl⟩ : syracuseStep 640255 = 960383) B960383
theorem B44391931 : Blo 566810 44391931 := bstep (se 1 (by rfl) ⟨33293948, by rfl⟩ : syracuseStep 44391931 = 66587897) B66587897
theorem B853673 : Blo 566810 853673 := bstep (se 2 (by rfl) ⟨320127, by rfl⟩ : syracuseStep 853673 = 640255) B640255
theorem B236756965 : Blo 566810 236756965 := bstep (se 4 (by rfl) ⟨22195965, by rfl⟩ : syracuseStep 236756965 = 44391931) B44391931
theorem B569115 : Blo 566810 569115 := bstep (se 1 (by rfl) ⟨426836, by rfl⟩ : syracuseStep 569115 = 853673) B853673
theorem B315675953 : Blo 566810 315675953 := bstep (se 2 (by rfl) ⟨118378482, by rfl⟩ : syracuseStep 315675953 = 236756965) B236756965
theorem B210450635 : Blo 566810 210450635 := bstep (se 1 (by rfl) ⟨157837976, by rfl⟩ : syracuseStep 210450635 = 315675953) B315675953
theorem B140300423 : Blo 566810 140300423 := bstep (se 1 (by rfl) ⟨105225317, by rfl⟩ : syracuseStep 140300423 = 210450635) B210450635
theorem B93533615 : Blo 566810 93533615 := bstep (se 1 (by rfl) ⟨70150211, by rfl⟩ : syracuseStep 93533615 = 140300423) B140300423
theorem B62355743 : Blo 566810 62355743 := bstep (se 1 (by rfl) ⟨46766807, by rfl⟩ : syracuseStep 62355743 = 93533615) B93533615
theorem B41570495 : Blo 566810 41570495 := bstep (se 1 (by rfl) ⟨31177871, by rfl⟩ : syracuseStep 41570495 = 62355743) B62355743
theorem B27713663 : Blo 566810 27713663 := bstep (se 1 (by rfl) ⟨20785247, by rfl⟩ : syracuseStep 27713663 = 41570495) B41570495
theorem B18475775 : Blo 566810 18475775 := bstep (se 1 (by rfl) ⟨13856831, by rfl⟩ : syracuseStep 18475775 = 27713663) B27713663
theorem B12317183 : Blo 566810 12317183 := bstep (se 1 (by rfl) ⟨9237887, by rfl⟩ : syracuseStep 12317183 = 18475775) B18475775
theorem B8211455 : Blo 566810 8211455 := bstep (se 1 (by rfl) ⟨6158591, by rfl⟩ : syracuseStep 8211455 = 12317183) B12317183
theorem B5474303 : Blo 566810 5474303 := bstep (se 1 (by rfl) ⟨4105727, by rfl⟩ : syracuseStep 5474303 = 8211455) B8211455
theorem B3649535 : Blo 566810 3649535 := bstep (se 1 (by rfl) ⟨2737151, by rfl⟩ : syracuseStep 3649535 = 5474303) B5474303
theorem B2433023 : Blo 566810 2433023 := bstep (se 1 (by rfl) ⟨1824767, by rfl⟩ : syracuseStep 2433023 = 3649535) B3649535
theorem B1622015 : Blo 566810 1622015 := bstep (se 1 (by rfl) ⟨1216511, by rfl⟩ : syracuseStep 1622015 = 2433023) B2433023
theorem B1081343 : Blo 566810 1081343 := bstep (se 1 (by rfl) ⟨811007, by rfl⟩ : syracuseStep 1081343 = 1622015) B1622015
theorem B720895 : Blo 566810 720895 := bstep (se 1 (by rfl) ⟨540671, by rfl⟩ : syracuseStep 720895 = 1081343) B1081343
theorem B961193 : Blo 566810 961193 := bstep (se 2 (by rfl) ⟨360447, by rfl⟩ : syracuseStep 961193 = 720895) B720895
theorem B640795 : Blo 566810 640795 := bstep (se 1 (by rfl) ⟨480596, by rfl⟩ : syracuseStep 640795 = 961193) B961193
theorem B854393 : Blo 566810 854393 := bstep (se 2 (by rfl) ⟨320397, by rfl⟩ : syracuseStep 854393 = 640795) B640795
theorem B569595 : Blo 566810 569595 := bstep (se 1 (by rfl) ⟨427196, by rfl⟩ : syracuseStep 569595 = 854393) B854393

theorem C0 (j : ℕ) (h1 : 141702 ≤ j) (h2 : j ≤ 142401) : Blo 566810 (4 * j + 3) := by
  interval_cases j
  · exact B566811
  · exact B566815
  · exact B566819
  · exact B566823
  · exact B566827
  · exact B566831
  · exact B566835
  · exact B566839
  · exact B566843
  · exact B566847
  · exact B566851
  · exact B566855
  · exact B566859
  · exact B566863
  · exact B566867
  · exact B566871
  · exact B566875
  · exact B566879
  · exact B566883
  · exact B566887
  · exact B566891
  · exact B566895
  · exact B566899
  · exact B566903
  · exact B566907
  · exact B566911
  · exact B566915
  · exact B566919
  · exact B566923
  · exact B566927
  · exact B566931
  · exact B566935
  · exact B566939
  · exact B566943
  · exact B566947
  · exact B566951
  · exact B566955
  · exact B566959
  · exact B566963
  · exact B566967
  · exact B566971
  · exact B566975
  · exact B566979
  · exact B566983
  · exact B566987
  · exact B566991
  · exact B566995
  · exact B566999
  · exact B567003
  · exact B567007
  · exact B567011
  · exact B567015
  · exact B567019
  · exact B567023
  · exact B567027
  · exact B567031
  · exact B567035
  · exact B567039
  · exact B567043
  · exact B567047
  · exact B567051
  · exact B567055
  · exact B567059
  · exact B567063
  · exact B567067
  · exact B567071
  · exact B567075
  · exact B567079
  · exact B567083
  · exact B567087
  · exact B567091
  · exact B567095
  · exact B567099
  · exact B567103
  · exact B567107
  · exact B567111
  · exact B567115
  · exact B567119
  · exact B567123
  · exact B567127
  · exact B567131
  · exact B567135
  · exact B567139
  · exact B567143
  · exact B567147
  · exact B567151
  · exact B567155
  · exact B567159
  · exact B567163
  · exact B567167
  · exact B567171
  · exact B567175
  · exact B567179
  · exact B567183
  · exact B567187
  · exact B567191
  · exact B567195
  · exact B567199
  · exact B567203
  · exact B567207
  · exact B567211
  · exact B567215
  · exact B567219
  · exact B567223
  · exact B567227
  · exact B567231
  · exact B567235
  · exact B567239
  · exact B567243
  · exact B567247
  · exact B567251
  · exact B567255
  · exact B567259
  · exact B567263
  · exact B567267
  · exact B567271
  · exact B567275
  · exact B567279
  · exact B567283
  · exact B567287
  · exact B567291
  · exact B567295
  · exact B567299
  · exact B567303
  · exact B567307
  · exact B567311
  · exact B567315
  · exact B567319
  · exact B567323
  · exact B567327
  · exact B567331
  · exact B567335
  · exact B567339
  · exact B567343
  · exact B567347
  · exact B567351
  · exact B567355
  · exact B567359
  · exact B567363
  · exact B567367
  · exact B567371
  · exact B567375
  · exact B567379
  · exact B567383
  · exact B567387
  · exact B567391
  · exact B567395
  · exact B567399
  · exact B567403
  · exact B567407
  · exact B567411
  · exact B567415
  · exact B567419
  · exact B567423
  · exact B567427
  · exact B567431
  · exact B567435
  · exact B567439
  · exact B567443
  · exact B567447
  · exact B567451
  · exact B567455
  · exact B567459
  · exact B567463
  · exact B567467
  · exact B567471
  · exact B567475
  · exact B567479
  · exact B567483
  · exact B567487
  · exact B567491
  · exact B567495
  · exact B567499
  · exact B567503
  · exact B567507
  · exact B567511
  · exact B567515
  · exact B567519
  · exact B567523
  · exact B567527
  · exact B567531
  · exact B567535
  · exact B567539
  · exact B567543
  · exact B567547
  · exact B567551
  · exact B567555
  · exact B567559
  · exact B567563
  · exact B567567
  · exact B567571
  · exact B567575
  · exact B567579
  · exact B567583
  · exact B567587
  · exact B567591
  · exact B567595
  · exact B567599
  · exact B567603
  · exact B567607
  · exact B567611
  · exact B567615
  · exact B567619
  · exact B567623
  · exact B567627
  · exact B567631
  · exact B567635
  · exact B567639
  · exact B567643
  · exact B567647
  · exact B567651
  · exact B567655
  · exact B567659
  · exact B567663
  · exact B567667
  · exact B567671
  · exact B567675
  · exact B567679
  · exact B567683
  · exact B567687
  · exact B567691
  · exact B567695
  · exact B567699
  · exact B567703
  · exact B567707
  · exact B567711
  · exact B567715
  · exact B567719
  · exact B567723
  · exact B567727
  · exact B567731
  · exact B567735
  · exact B567739
  · exact B567743
  · exact B567747
  · exact B567751
  · exact B567755
  · exact B567759
  · exact B567763
  · exact B567767
  · exact B567771
  · exact B567775
  · exact B567779
  · exact B567783
  · exact B567787
  · exact B567791
  · exact B567795
  · exact B567799
  · exact B567803
  · exact B567807
  · exact B567811
  · exact B567815
  · exact B567819
  · exact B567823
  · exact B567827
  · exact B567831
  · exact B567835
  · exact B567839
  · exact B567843
  · exact B567847
  · exact B567851
  · exact B567855
  · exact B567859
  · exact B567863
  · exact B567867
  · exact B567871
  · exact B567875
  · exact B567879
  · exact B567883
  · exact B567887
  · exact B567891
  · exact B567895
  · exact B567899
  · exact B567903
  · exact B567907
  · exact B567911
  · exact B567915
  · exact B567919
  · exact B567923
  · exact B567927
  · exact B567931
  · exact B567935
  · exact B567939
  · exact B567943
  · exact B567947
  · exact B567951
  · exact B567955
  · exact B567959
  · exact B567963
  · exact B567967
  · exact B567971
  · exact B567975
  · exact B567979
  · exact B567983
  · exact B567987
  · exact B567991
  · exact B567995
  · exact B567999
  · exact B568003
  · exact B568007
  · exact B568011
  · exact B568015
  · exact B568019
  · exact B568023
  · exact B568027
  · exact B568031
  · exact B568035
  · exact B568039
  · exact B568043
  · exact B568047
  · exact B568051
  · exact B568055
  · exact B568059
  · exact B568063
  · exact B568067
  · exact B568071
  · exact B568075
  · exact B568079
  · exact B568083
  · exact B568087
  · exact B568091
  · exact B568095
  · exact B568099
  · exact B568103
  · exact B568107
  · exact B568111
  · exact B568115
  · exact B568119
  · exact B568123
  · exact B568127
  · exact B568131
  · exact B568135
  · exact B568139
  · exact B568143
  · exact B568147
  · exact B568151
  · exact B568155
  · exact B568159
  · exact B568163
  · exact B568167
  · exact B568171
  · exact B568175
  · exact B568179
  · exact B568183
  · exact B568187
  · exact B568191
  · exact B568195
  · exact B568199
  · exact B568203
  · exact B568207
  · exact B568211
  · exact B568215
  · exact B568219
  · exact B568223
  · exact B568227
  · exact B568231
  · exact B568235
  · exact B568239
  · exact B568243
  · exact B568247
  · exact B568251
  · exact B568255
  · exact B568259
  · exact B568263
  · exact B568267
  · exact B568271
  · exact B568275
  · exact B568279
  · exact B568283
  · exact B568287
  · exact B568291
  · exact B568295
  · exact B568299
  · exact B568303
  · exact B568307
  · exact B568311
  · exact B568315
  · exact B568319
  · exact B568323
  · exact B568327
  · exact B568331
  · exact B568335
  · exact B568339
  · exact B568343
  · exact B568347
  · exact B568351
  · exact B568355
  · exact B568359
  · exact B568363
  · exact B568367
  · exact B568371
  · exact B568375
  · exact B568379
  · exact B568383
  · exact B568387
  · exact B568391
  · exact B568395
  · exact B568399
  · exact B568403
  · exact B568407
  · exact B568411
  · exact B568415
  · exact B568419
  · exact B568423
  · exact B568427
  · exact B568431
  · exact B568435
  · exact B568439
  · exact B568443
  · exact B568447
  · exact B568451
  · exact B568455
  · exact B568459
  · exact B568463
  · exact B568467
  · exact B568471
  · exact B568475
  · exact B568479
  · exact B568483
  · exact B568487
  · exact B568491
  · exact B568495
  · exact B568499
  · exact B568503
  · exact B568507
  · exact B568511
  · exact B568515
  · exact B568519
  · exact B568523
  · exact B568527
  · exact B568531
  · exact B568535
  · exact B568539
  · exact B568543
  · exact B568547
  · exact B568551
  · exact B568555
  · exact B568559
  · exact B568563
  · exact B568567
  · exact B568571
  · exact B568575
  · exact B568579
  · exact B568583
  · exact B568587
  · exact B568591
  · exact B568595
  · exact B568599
  · exact B568603
  · exact B568607
  · exact B568611
  · exact B568615
  · exact B568619
  · exact B568623
  · exact B568627
  · exact B568631
  · exact B568635
  · exact B568639
  · exact B568643
  · exact B568647
  · exact B568651
  · exact B568655
  · exact B568659
  · exact B568663
  · exact B568667
  · exact B568671
  · exact B568675
  · exact B568679
  · exact B568683
  · exact B568687
  · exact B568691
  · exact B568695
  · exact B568699
  · exact B568703
  · exact B568707
  · exact B568711
  · exact B568715
  · exact B568719
  · exact B568723
  · exact B568727
  · exact B568731
  · exact B568735
  · exact B568739
  · exact B568743
  · exact B568747
  · exact B568751
  · exact B568755
  · exact B568759
  · exact B568763
  · exact B568767
  · exact B568771
  · exact B568775
  · exact B568779
  · exact B568783
  · exact B568787
  · exact B568791
  · exact B568795
  · exact B568799
  · exact B568803
  · exact B568807
  · exact B568811
  · exact B568815
  · exact B568819
  · exact B568823
  · exact B568827
  · exact B568831
  · exact B568835
  · exact B568839
  · exact B568843
  · exact B568847
  · exact B568851
  · exact B568855
  · exact B568859
  · exact B568863
  · exact B568867
  · exact B568871
  · exact B568875
  · exact B568879
  · exact B568883
  · exact B568887
  · exact B568891
  · exact B568895
  · exact B568899
  · exact B568903
  · exact B568907
  · exact B568911
  · exact B568915
  · exact B568919
  · exact B568923
  · exact B568927
  · exact B568931
  · exact B568935
  · exact B568939
  · exact B568943
  · exact B568947
  · exact B568951
  · exact B568955
  · exact B568959
  · exact B568963
  · exact B568967
  · exact B568971
  · exact B568975
  · exact B568979
  · exact B568983
  · exact B568987
  · exact B568991
  · exact B568995
  · exact B568999
  · exact B569003
  · exact B569007
  · exact B569011
  · exact B569015
  · exact B569019
  · exact B569023
  · exact B569027
  · exact B569031
  · exact B569035
  · exact B569039
  · exact B569043
  · exact B569047
  · exact B569051
  · exact B569055
  · exact B569059
  · exact B569063
  · exact B569067
  · exact B569071
  · exact B569075
  · exact B569079
  · exact B569083
  · exact B569087
  · exact B569091
  · exact B569095
  · exact B569099
  · exact B569103
  · exact B569107
  · exact B569111
  · exact B569115
  · exact B569119
  · exact B569123
  · exact B569127
  · exact B569131
  · exact B569135
  · exact B569139
  · exact B569143
  · exact B569147
  · exact B569151
  · exact B569155
  · exact B569159
  · exact B569163
  · exact B569167
  · exact B569171
  · exact B569175
  · exact B569179
  · exact B569183
  · exact B569187
  · exact B569191
  · exact B569195
  · exact B569199
  · exact B569203
  · exact B569207
  · exact B569211
  · exact B569215
  · exact B569219
  · exact B569223
  · exact B569227
  · exact B569231
  · exact B569235
  · exact B569239
  · exact B569243
  · exact B569247
  · exact B569251
  · exact B569255
  · exact B569259
  · exact B569263
  · exact B569267
  · exact B569271
  · exact B569275
  · exact B569279
  · exact B569283
  · exact B569287
  · exact B569291
  · exact B569295
  · exact B569299
  · exact B569303
  · exact B569307
  · exact B569311
  · exact B569315
  · exact B569319
  · exact B569323
  · exact B569327
  · exact B569331
  · exact B569335
  · exact B569339
  · exact B569343
  · exact B569347
  · exact B569351
  · exact B569355
  · exact B569359
  · exact B569363
  · exact B569367
  · exact B569371
  · exact B569375
  · exact B569379
  · exact B569383
  · exact B569387
  · exact B569391
  · exact B569395
  · exact B569399
  · exact B569403
  · exact B569407
  · exact B569411
  · exact B569415
  · exact B569419
  · exact B569423
  · exact B569427
  · exact B569431
  · exact B569435
  · exact B569439
  · exact B569443
  · exact B569447
  · exact B569451
  · exact B569455
  · exact B569459
  · exact B569463
  · exact B569467
  · exact B569471
  · exact B569475
  · exact B569479
  · exact B569483
  · exact B569487
  · exact B569491
  · exact B569495
  · exact B569499
  · exact B569503
  · exact B569507
  · exact B569511
  · exact B569515
  · exact B569519
  · exact B569523
  · exact B569527
  · exact B569531
  · exact B569535
  · exact B569539
  · exact B569543
  · exact B569547
  · exact B569551
  · exact B569555
  · exact B569559
  · exact B569563
  · exact B569567
  · exact B569571
  · exact B569575
  · exact B569579
  · exact B569583
  · exact B569587
  · exact B569591
  · exact B569595
  · exact B569599
  · exact B569603
  · exact B569607

theorem C1 (j : ℕ) (h1 : 142402 ≤ j) (h2 : j ≤ 142701) : Blo 566810 (4 * j + 3) := by
  interval_cases j
  · exact B569611
  · exact B569615
  · exact B569619
  · exact B569623
  · exact B569627
  · exact B569631
  · exact B569635
  · exact B569639
  · exact B569643
  · exact B569647
  · exact B569651
  · exact B569655
  · exact B569659
  · exact B569663
  · exact B569667
  · exact B569671
  · exact B569675
  · exact B569679
  · exact B569683
  · exact B569687
  · exact B569691
  · exact B569695
  · exact B569699
  · exact B569703
  · exact B569707
  · exact B569711
  · exact B569715
  · exact B569719
  · exact B569723
  · exact B569727
  · exact B569731
  · exact B569735
  · exact B569739
  · exact B569743
  · exact B569747
  · exact B569751
  · exact B569755
  · exact B569759
  · exact B569763
  · exact B569767
  · exact B569771
  · exact B569775
  · exact B569779
  · exact B569783
  · exact B569787
  · exact B569791
  · exact B569795
  · exact B569799
  · exact B569803
  · exact B569807
  · exact B569811
  · exact B569815
  · exact B569819
  · exact B569823
  · exact B569827
  · exact B569831
  · exact B569835
  · exact B569839
  · exact B569843
  · exact B569847
  · exact B569851
  · exact B569855
  · exact B569859
  · exact B569863
  · exact B569867
  · exact B569871
  · exact B569875
  · exact B569879
  · exact B569883
  · exact B569887
  · exact B569891
  · exact B569895
  · exact B569899
  · exact B569903
  · exact B569907
  · exact B569911
  · exact B569915
  · exact B569919
  · exact B569923
  · exact B569927
  · exact B569931
  · exact B569935
  · exact B569939
  · exact B569943
  · exact B569947
  · exact B569951
  · exact B569955
  · exact B569959
  · exact B569963
  · exact B569967
  · exact B569971
  · exact B569975
  · exact B569979
  · exact B569983
  · exact B569987
  · exact B569991
  · exact B569995
  · exact B569999
  · exact B570003
  · exact B570007
  · exact B570011
  · exact B570015
  · exact B570019
  · exact B570023
  · exact B570027
  · exact B570031
  · exact B570035
  · exact B570039
  · exact B570043
  · exact B570047
  · exact B570051
  · exact B570055
  · exact B570059
  · exact B570063
  · exact B570067
  · exact B570071
  · exact B570075
  · exact B570079
  · exact B570083
  · exact B570087
  · exact B570091
  · exact B570095
  · exact B570099
  · exact B570103
  · exact B570107
  · exact B570111
  · exact B570115
  · exact B570119
  · exact B570123
  · exact B570127
  · exact B570131
  · exact B570135
  · exact B570139
  · exact B570143
  · exact B570147
  · exact B570151
  · exact B570155
  · exact B570159
  · exact B570163
  · exact B570167
  · exact B570171
  · exact B570175
  · exact B570179
  · exact B570183
  · exact B570187
  · exact B570191
  · exact B570195
  · exact B570199
  · exact B570203
  · exact B570207
  · exact B570211
  · exact B570215
  · exact B570219
  · exact B570223
  · exact B570227
  · exact B570231
  · exact B570235
  · exact B570239
  · exact B570243
  · exact B570247
  · exact B570251
  · exact B570255
  · exact B570259
  · exact B570263
  · exact B570267
  · exact B570271
  · exact B570275
  · exact B570279
  · exact B570283
  · exact B570287
  · exact B570291
  · exact B570295
  · exact B570299
  · exact B570303
  · exact B570307
  · exact B570311
  · exact B570315
  · exact B570319
  · exact B570323
  · exact B570327
  · exact B570331
  · exact B570335
  · exact B570339
  · exact B570343
  · exact B570347
  · exact B570351
  · exact B570355
  · exact B570359
  · exact B570363
  · exact B570367
  · exact B570371
  · exact B570375
  · exact B570379
  · exact B570383
  · exact B570387
  · exact B570391
  · exact B570395
  · exact B570399
  · exact B570403
  · exact B570407
  · exact B570411
  · exact B570415
  · exact B570419
  · exact B570423
  · exact B570427
  · exact B570431
  · exact B570435
  · exact B570439
  · exact B570443
  · exact B570447
  · exact B570451
  · exact B570455
  · exact B570459
  · exact B570463
  · exact B570467
  · exact B570471
  · exact B570475
  · exact B570479
  · exact B570483
  · exact B570487
  · exact B570491
  · exact B570495
  · exact B570499
  · exact B570503
  · exact B570507
  · exact B570511
  · exact B570515
  · exact B570519
  · exact B570523
  · exact B570527
  · exact B570531
  · exact B570535
  · exact B570539
  · exact B570543
  · exact B570547
  · exact B570551
  · exact B570555
  · exact B570559
  · exact B570563
  · exact B570567
  · exact B570571
  · exact B570575
  · exact B570579
  · exact B570583
  · exact B570587
  · exact B570591
  · exact B570595
  · exact B570599
  · exact B570603
  · exact B570607
  · exact B570611
  · exact B570615
  · exact B570619
  · exact B570623
  · exact B570627
  · exact B570631
  · exact B570635
  · exact B570639
  · exact B570643
  · exact B570647
  · exact B570651
  · exact B570655
  · exact B570659
  · exact B570663
  · exact B570667
  · exact B570671
  · exact B570675
  · exact B570679
  · exact B570683
  · exact B570687
  · exact B570691
  · exact B570695
  · exact B570699
  · exact B570703
  · exact B570707
  · exact B570711
  · exact B570715
  · exact B570719
  · exact B570723
  · exact B570727
  · exact B570731
  · exact B570735
  · exact B570739
  · exact B570743
  · exact B570747
  · exact B570751
  · exact B570755
  · exact B570759
  · exact B570763
  · exact B570767
  · exact B570771
  · exact B570775
  · exact B570779
  · exact B570783
  · exact B570787
  · exact B570791
  · exact B570795
  · exact B570799
  · exact B570803
  · exact B570807

theorem solution (m : ℕ) (hlo : 566810 ≤ m) (hhi : m ≤ 570810) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 141702 ≤ j := by omega
    have hj2 : j ≤ 142701 := by omega
    have hb : Blo 566810 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 142402 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
