-- Prove2me | solution 1 for syracuse_descends_range_1705053_1707053
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:26:43.661991+00:00
-- url     : https://prove2.me/submissions/1402874b-df32-452d-8fe8-c4d117dcd587

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


theorem B14573621 : Blo 1705053 14573621 := bbase (se 5 (by rfl) ⟨683138, by rfl⟩ : syracuseStep 14573621 = 1366277) (by norm_num)
theorem B3457093 : Blo 1705053 3457093 := bbase (se 4 (by rfl) ⟨324102, by rfl⟩ : syracuseStep 3457093 = 648205) (by norm_num)
theorem B8634437 : Blo 1705053 8634437 := bbase (se 4 (by rfl) ⟨809478, by rfl⟩ : syracuseStep 8634437 = 1618957) (by norm_num)
theorem B5759045 : Blo 1705053 5759045 := bbase (se 4 (by rfl) ⟨539910, by rfl⟩ : syracuseStep 5759045 = 1079821) (by norm_num)
theorem B3645661 : Blo 1705053 3645661 := bbase (se 3 (by rfl) ⟨683561, by rfl⟩ : syracuseStep 3645661 = 1367123) (by norm_num)
theorem B4317421 : Blo 1705053 4317421 := bbase (se 3 (by rfl) ⟨809516, by rfl⟩ : syracuseStep 4317421 = 1619033) (by norm_num)
theorem B4153589 : Blo 1705053 4153589 := bbase (se 5 (by rfl) ⟨194699, by rfl⟩ : syracuseStep 4153589 = 389399) (by norm_num)
theorem B9716021 : Blo 1705053 9716021 := bbase (se 5 (by rfl) ⟨455438, by rfl⟩ : syracuseStep 9716021 = 910877) (by norm_num)
theorem B4317533 : Blo 1705053 4317533 := bbase (se 3 (by rfl) ⟨809537, by rfl⟩ : syracuseStep 4317533 = 1619075) (by norm_num)
theorem B2769365 : Blo 1705053 2769365 := bbase (se 7 (by rfl) ⟨32453, by rfl⟩ : syracuseStep 2769365 = 64907) (by norm_num)
theorem B7283189 : Blo 1705053 7283189 := bbase (se 5 (by rfl) ⟨341399, by rfl⟩ : syracuseStep 7283189 = 682799) (by norm_num)
theorem B5759477 : Blo 1705053 5759477 := bbase (se 5 (by rfl) ⟨269975, by rfl⟩ : syracuseStep 5759477 = 539951) (by norm_num)
theorem B4317725 : Blo 1705053 4317725 := bbase (se 3 (by rfl) ⟨809573, by rfl⟩ : syracuseStep 4317725 = 1619147) (by norm_num)
theorem B7995941 : Blo 1705053 7995941 := bbase (se 4 (by rfl) ⟨749619, by rfl⟩ : syracuseStep 7995941 = 1499239) (by norm_num)
theorem B3326557 : Blo 1705053 3326557 := bbase (se 3 (by rfl) ⟨623729, by rfl⟩ : syracuseStep 3326557 = 1247459) (by norm_num)
theorem B4858501 : Blo 1705053 4858501 := bbase (se 4 (by rfl) ⟨455484, by rfl⟩ : syracuseStep 4858501 = 910969) (by norm_num)
theorem B2048657 : Blo 1705053 2048657 := bbase (se 2 (by rfl) ⟨768246, by rfl⟩ : syracuseStep 2048657 = 1536493) (by norm_num)
theorem B4154053 : Blo 1705053 4154053 := bbase (se 4 (by rfl) ⟨389442, by rfl⟩ : syracuseStep 4154053 = 778885) (by norm_num)
theorem B7283429 : Blo 1705053 7283429 := bbase (se 4 (by rfl) ⟨682821, by rfl⟩ : syracuseStep 7283429 = 1365643) (by norm_num)
theorem B5464853 : Blo 1705053 5464853 := bbase (se 6 (by rfl) ⟨128082, by rfl⟩ : syracuseStep 5464853 = 256165) (by norm_num)
theorem B8201045 : Blo 1705053 8201045 := bbase (se 9 (by rfl) ⟨24026, by rfl⟩ : syracuseStep 8201045 = 48053) (by norm_num)
theorem B2106205 : Blo 1705053 2106205 := bbase (se 3 (by rfl) ⟨394913, by rfl⟩ : syracuseStep 2106205 = 789827) (by norm_num)
theorem B4318069 : Blo 1705053 4318069 := bbase (se 5 (by rfl) ⟨202409, by rfl⟩ : syracuseStep 4318069 = 404819) (by norm_num)
theorem B4096901 : Blo 1705053 4096901 := bbase (se 4 (by rfl) ⟨384084, by rfl⟩ : syracuseStep 4096901 = 768169) (by norm_num)
theorem B4096909 : Blo 1705053 4096909 := bbase (se 3 (by rfl) ⟨768170, by rfl⟩ : syracuseStep 4096909 = 1536341) (by norm_num)
theorem B5759909 : Blo 1705053 5759909 := bbase (se 4 (by rfl) ⟨539991, by rfl⟩ : syracuseStep 5759909 = 1079983) (by norm_num)
theorem B2048989 : Blo 1705053 2048989 := bbase (se 3 (by rfl) ⟨384185, by rfl⟩ : syracuseStep 2048989 = 768371) (by norm_num)
theorem B4318181 : Blo 1705053 4318181 := bbase (se 4 (by rfl) ⟨404829, by rfl⟩ : syracuseStep 4318181 = 809659) (by norm_num)
theorem B6480917 : Blo 1705053 6480917 := bbase (se 6 (by rfl) ⟨151896, by rfl⟩ : syracuseStep 6480917 = 303793) (by norm_num)
theorem B3458189 : Blo 1705053 3458189 := bbase (se 3 (by rfl) ⟨648410, by rfl⟩ : syracuseStep 3458189 = 1296821) (by norm_num)
theorem B4318373 : Blo 1705053 4318373 := bbase (se 4 (by rfl) ⟨404847, by rfl⟩ : syracuseStep 4318373 = 809695) (by norm_num)
theorem B1918201 : Blo 1705053 1918201 := bbase (se 2 (by rfl) ⟨719325, by rfl⟩ : syracuseStep 1918201 = 1438651) (by norm_num)
theorem B1918237 : Blo 1705053 1918237 := bbase (se 3 (by rfl) ⟨359669, by rfl⟩ : syracuseStep 1918237 = 719339) (by norm_num)
theorem B6481205 : Blo 1705053 6481205 := bbase (se 5 (by rfl) ⟨303806, by rfl⟩ : syracuseStep 6481205 = 607613) (by norm_num)
theorem B1918273 : Blo 1705053 1918273 := bbase (se 2 (by rfl) ⟨719352, by rfl⟩ : syracuseStep 1918273 = 1438705) (by norm_num)
theorem B1729873 : Blo 1705053 1729873 := bbase (se 2 (by rfl) ⟨648702, by rfl⟩ : syracuseStep 1729873 = 1297405) (by norm_num)
theorem B8635733 : Blo 1705053 8635733 := bbase (se 12 (by rfl) ⟨3162, by rfl⟩ : syracuseStep 8635733 = 6325) (by norm_num)
theorem B5760341 : Blo 1705053 5760341 := bbase (se 12 (by rfl) ⟨2109, by rfl⟩ : syracuseStep 5760341 = 4219) (by norm_num)
theorem B1918309 : Blo 1705053 1918309 := bbase (se 4 (by rfl) ⟨179841, by rfl⟩ : syracuseStep 1918309 = 359683) (by norm_num)
theorem B1918345 : Blo 1705053 1918345 := bbase (se 2 (by rfl) ⟨719379, by rfl⟩ : syracuseStep 1918345 = 1438759) (by norm_num)
theorem B1918381 : Blo 1705053 1918381 := bbase (se 3 (by rfl) ⟨359696, by rfl⟩ : syracuseStep 1918381 = 719393) (by norm_num)
theorem B1918417 : Blo 1705053 1918417 := bbase (se 2 (by rfl) ⟨719406, by rfl⟩ : syracuseStep 1918417 = 1438813) (by norm_num)
theorem B9717205 : Blo 1705053 9717205 := bbase (se 7 (by rfl) ⟨113873, by rfl⟩ : syracuseStep 9717205 = 227747) (by norm_num)
theorem B1918453 : Blo 1705053 1918453 := bbase (se 5 (by rfl) ⟨89927, by rfl⟩ : syracuseStep 1918453 = 179855) (by norm_num)
theorem B6235637 : Blo 1705053 6235637 := bbase (se 5 (by rfl) ⟨292295, by rfl⟩ : syracuseStep 6235637 = 584591) (by norm_num)
theorem B4318717 : Blo 1705053 4318717 := bbase (se 3 (by rfl) ⟨809759, by rfl⟩ : syracuseStep 4318717 = 1619519) (by norm_num)
theorem B2336261 : Blo 1705053 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B1918489 : Blo 1705053 1918489 := bbase (se 2 (by rfl) ⟨719433, by rfl⟩ : syracuseStep 1918489 = 1438867) (by norm_num)
theorem B3237421 : Blo 1705053 3237421 := bbase (se 3 (by rfl) ⟨607016, by rfl⟩ : syracuseStep 3237421 = 1214033) (by norm_num)
theorem B1918525 : Blo 1705053 1918525 := bbase (se 3 (by rfl) ⟨359723, by rfl⟩ : syracuseStep 1918525 = 719447) (by norm_num)
theorem B1918561 : Blo 1705053 1918561 := bbase (se 2 (by rfl) ⟨719460, by rfl⟩ : syracuseStep 1918561 = 1438921) (by norm_num)
theorem B4318829 : Blo 1705053 4318829 := bbase (se 3 (by rfl) ⟨809780, by rfl⟩ : syracuseStep 4318829 = 1619561) (by norm_num)
theorem B1918597 : Blo 1705053 1918597 := bbase (se 4 (by rfl) ⟨179868, by rfl⟩ : syracuseStep 1918597 = 359737) (by norm_num)
theorem B2557589 : Blo 1705053 2557589 := bbase (se 6 (by rfl) ⟨59943, by rfl⟩ : syracuseStep 2557589 = 119887) (by norm_num)
theorem B1918633 : Blo 1705053 1918633 := bbase (se 2 (by rfl) ⟨719487, by rfl⟩ : syracuseStep 1918633 = 1438975) (by norm_num)
theorem B2557613 : Blo 1705053 2557613 := bbase (se 3 (by rfl) ⟨479552, by rfl⟩ : syracuseStep 2557613 = 959105) (by norm_num)
theorem B4097717 : Blo 1705053 4097717 := bbase (se 5 (by rfl) ⟨192080, by rfl⟩ : syracuseStep 4097717 = 384161) (by norm_num)
theorem B3237565 : Blo 1705053 3237565 := bbase (se 3 (by rfl) ⟨607043, by rfl⟩ : syracuseStep 3237565 = 1214087) (by norm_num)
theorem B2557637 : Blo 1705053 2557637 := bbase (se 4 (by rfl) ⟨239778, by rfl⟩ : syracuseStep 2557637 = 479557) (by norm_num)
theorem B1918669 : Blo 1705053 1918669 := bbase (se 3 (by rfl) ⟨359750, by rfl⟩ : syracuseStep 1918669 = 719501) (by norm_num)
theorem B4859605 : Blo 1705053 4859605 := bbase (se 7 (by rfl) ⟨56948, by rfl⟩ : syracuseStep 4859605 = 113897) (by norm_num)
theorem B59926229 : Blo 1705053 59926229 := bbase (se 7 (by rfl) ⟨702260, by rfl⟩ : syracuseStep 59926229 = 1404521) (by norm_num)
theorem B2557661 : Blo 1705053 2557661 := bbase (se 3 (by rfl) ⟨479561, by rfl⟩ : syracuseStep 2557661 = 959123) (by norm_num)
theorem B2918125 : Blo 1705053 2918125 := bbase (se 3 (by rfl) ⟨547148, by rfl⟩ : syracuseStep 2918125 = 1094297) (by norm_num)
theorem B1918705 : Blo 1705053 1918705 := bbase (se 2 (by rfl) ⟨719514, by rfl⟩ : syracuseStep 1918705 = 1439029) (by norm_num)
theorem B2557685 : Blo 1705053 2557685 := bbase (se 5 (by rfl) ⟨119891, by rfl⟩ : syracuseStep 2557685 = 239783) (by norm_num)
theorem B5760773 : Blo 1705053 5760773 := bbase (se 4 (by rfl) ⟨540072, by rfl⟩ : syracuseStep 5760773 = 1080145) (by norm_num)
theorem B2557709 : Blo 1705053 2557709 := bbase (se 3 (by rfl) ⟨479570, by rfl⟩ : syracuseStep 2557709 = 959141) (by norm_num)
theorem B1918741 : Blo 1705053 1918741 := bbase (se 6 (by rfl) ⟨44970, by rfl⟩ : syracuseStep 1918741 = 89941) (by norm_num)
theorem B2557733 : Blo 1705053 2557733 := bbase (se 4 (by rfl) ⟨239787, by rfl⟩ : syracuseStep 2557733 = 479575) (by norm_num)
theorem B4319021 : Blo 1705053 4319021 := bbase (se 3 (by rfl) ⟨809816, by rfl⟩ : syracuseStep 4319021 = 1619633) (by norm_num)
theorem B1918777 : Blo 1705053 1918777 := bbase (se 2 (by rfl) ⟨719541, by rfl⟩ : syracuseStep 1918777 = 1439083) (by norm_num)
theorem B2557757 : Blo 1705053 2557757 := bbase (se 3 (by rfl) ⟨479579, by rfl⟩ : syracuseStep 2557757 = 959159) (by norm_num)
theorem B2557781 : Blo 1705053 2557781 := bbase (se 9 (by rfl) ⟨7493, by rfl⟩ : syracuseStep 2557781 = 14987) (by norm_num)
theorem B2049877 : Blo 1705053 2049877 := bbase (se 9 (by rfl) ⟨6005, by rfl⟩ : syracuseStep 2049877 = 12011) (by norm_num)
theorem B3237725 : Blo 1705053 3237725 := bbase (se 3 (by rfl) ⟨607073, by rfl⟩ : syracuseStep 3237725 = 1214147) (by norm_num)
theorem B1918813 : Blo 1705053 1918813 := bbase (se 3 (by rfl) ⟨359777, by rfl⟩ : syracuseStep 1918813 = 719555) (by norm_num)
theorem B2557805 : Blo 1705053 2557805 := bbase (se 3 (by rfl) ⟨479588, by rfl⟩ : syracuseStep 2557805 = 959177) (by norm_num)
theorem B3073909 : Blo 1705053 3073909 := bbase (se 5 (by rfl) ⟨144089, by rfl⟩ : syracuseStep 3073909 = 288179) (by norm_num)
theorem B1918849 : Blo 1705053 1918849 := bbase (se 2 (by rfl) ⟨719568, by rfl⟩ : syracuseStep 1918849 = 1439137) (by norm_num)
theorem B2557829 : Blo 1705053 2557829 := bbase (se 4 (by rfl) ⟨239796, by rfl⟩ : syracuseStep 2557829 = 479593) (by norm_num)
theorem B2557853 : Blo 1705053 2557853 := bbase (se 3 (by rfl) ⟨479597, by rfl⟩ : syracuseStep 2557853 = 959195) (by norm_num)
theorem B2877349 : Blo 1705053 2877349 := bbase (se 4 (by rfl) ⟨269751, by rfl⟩ : syracuseStep 2877349 = 539503) (by norm_num)
theorem B1918885 : Blo 1705053 1918885 := bbase (se 4 (by rfl) ⟨179895, by rfl⟩ : syracuseStep 1918885 = 359791) (by norm_num)
theorem B2557877 : Blo 1705053 2557877 := bbase (se 5 (by rfl) ⟨119900, by rfl⟩ : syracuseStep 2557877 = 239801) (by norm_num)
theorem B1918921 : Blo 1705053 1918921 := bbase (se 2 (by rfl) ⟨719595, by rfl⟩ : syracuseStep 1918921 = 1439191) (by norm_num)
theorem B2557901 : Blo 1705053 2557901 := bbase (se 3 (by rfl) ⟨479606, by rfl⟩ : syracuseStep 2557901 = 959213) (by norm_num)
theorem B2557925 : Blo 1705053 2557925 := bbase (se 4 (by rfl) ⟨239805, by rfl⟩ : syracuseStep 2557925 = 479611) (by norm_num)
theorem B3237869 : Blo 1705053 3237869 := bbase (se 3 (by rfl) ⟨607100, by rfl⟩ : syracuseStep 3237869 = 1214201) (by norm_num)
theorem B1918957 : Blo 1705053 1918957 := bbase (se 3 (by rfl) ⟨359804, by rfl⟩ : syracuseStep 1918957 = 719609) (by norm_num)
theorem B2557949 : Blo 1705053 2557949 := bbase (se 3 (by rfl) ⟨479615, by rfl⟩ : syracuseStep 2557949 = 959231) (by norm_num)
theorem B2877437 : Blo 1705053 2877437 := bbase (se 3 (by rfl) ⟨539519, by rfl⟩ : syracuseStep 2877437 = 1079039) (by norm_num)
theorem B1918993 : Blo 1705053 1918993 := bbase (se 2 (by rfl) ⟨719622, by rfl⟩ : syracuseStep 1918993 = 1439245) (by norm_num)
theorem B13125653 : Blo 1705053 13125653 := bbase (se 6 (by rfl) ⟨307632, by rfl⟩ : syracuseStep 13125653 = 615265) (by norm_num)
theorem B2557973 : Blo 1705053 2557973 := bbase (se 6 (by rfl) ⟨59952, by rfl⟩ : syracuseStep 2557973 = 119905) (by norm_num)
theorem B5466133 : Blo 1705053 5466133 := bbase (se 6 (by rfl) ⟨128112, by rfl⟩ : syracuseStep 5466133 = 256225) (by norm_num)
theorem B2557997 : Blo 1705053 2557997 := bbase (se 3 (by rfl) ⟨479624, by rfl⟩ : syracuseStep 2557997 = 959249) (by norm_num)
theorem B1919029 : Blo 1705053 1919029 := bbase (se 5 (by rfl) ⟨89954, by rfl⟩ : syracuseStep 1919029 = 179909) (by norm_num)
theorem B2558021 : Blo 1705053 2558021 := bbase (se 4 (by rfl) ⟨239814, by rfl⟩ : syracuseStep 2558021 = 479629) (by norm_num)
theorem B1919065 : Blo 1705053 1919065 := bbase (se 2 (by rfl) ⟨719649, by rfl⟩ : syracuseStep 1919065 = 1439299) (by norm_num)
theorem B2558045 : Blo 1705053 2558045 := bbase (se 3 (by rfl) ⟨479633, by rfl⟩ : syracuseStep 2558045 = 959267) (by norm_num)
theorem B2558069 : Blo 1705053 2558069 := bbase (se 5 (by rfl) ⟨119909, by rfl⟩ : syracuseStep 2558069 = 239819) (by norm_num)
theorem B2877565 : Blo 1705053 2877565 := bbase (se 3 (by rfl) ⟨539543, by rfl⟩ : syracuseStep 2877565 = 1079087) (by norm_num)
theorem B1919101 : Blo 1705053 1919101 := bbase (se 3 (by rfl) ⟨359831, by rfl⟩ : syracuseStep 1919101 = 719663) (by norm_num)
theorem B4319365 : Blo 1705053 4319365 := bbase (se 4 (by rfl) ⟨404940, by rfl⟩ : syracuseStep 4319365 = 809881) (by norm_num)
theorem B2558093 : Blo 1705053 2558093 := bbase (se 3 (by rfl) ⟨479642, by rfl⟩ : syracuseStep 2558093 = 959285) (by norm_num)
theorem B1919137 : Blo 1705053 1919137 := bbase (se 2 (by rfl) ⟨719676, by rfl⟩ : syracuseStep 1919137 = 1439353) (by norm_num)
theorem B2558117 : Blo 1705053 2558117 := bbase (se 4 (by rfl) ⟨239823, by rfl⟩ : syracuseStep 2558117 = 479647) (by norm_num)
theorem B5761205 : Blo 1705053 5761205 := bbase (se 5 (by rfl) ⟨270056, by rfl⟩ : syracuseStep 5761205 = 540113) (by norm_num)
theorem B2558141 : Blo 1705053 2558141 := bbase (se 3 (by rfl) ⟨479651, by rfl⟩ : syracuseStep 2558141 = 959303) (by norm_num)
theorem B1919173 : Blo 1705053 1919173 := bbase (se 4 (by rfl) ⟨179922, by rfl⟩ : syracuseStep 1919173 = 359845) (by norm_num)
theorem B2877653 : Blo 1705053 2877653 := bbase (se 7 (by rfl) ⟨33722, by rfl⟩ : syracuseStep 2877653 = 67445) (by norm_num)
theorem B2558165 : Blo 1705053 2558165 := bbase (se 7 (by rfl) ⟨29978, by rfl⟩ : syracuseStep 2558165 = 59957) (by norm_num)
theorem B1919209 : Blo 1705053 1919209 := bbase (se 2 (by rfl) ⟨719703, by rfl⟩ : syracuseStep 1919209 = 1439407) (by norm_num)
theorem B2558189 : Blo 1705053 2558189 := bbase (se 3 (by rfl) ⟨479660, by rfl⟩ : syracuseStep 2558189 = 959321) (by norm_num)
theorem B1820917 : Blo 1705053 1820917 := bbase (se 5 (by rfl) ⟨85355, by rfl⟩ : syracuseStep 1820917 = 170711) (by norm_num)
theorem B4319477 : Blo 1705053 4319477 := bbase (se 5 (by rfl) ⟨202475, by rfl⟩ : syracuseStep 4319477 = 404951) (by norm_num)
theorem B2558213 : Blo 1705053 2558213 := bbase (se 4 (by rfl) ⟨239832, by rfl⟩ : syracuseStep 2558213 = 479665) (by norm_num)
theorem B3238157 : Blo 1705053 3238157 := bbase (se 3 (by rfl) ⟨607154, by rfl⟩ : syracuseStep 3238157 = 1214309) (by norm_num)
theorem B1919245 : Blo 1705053 1919245 := bbase (se 3 (by rfl) ⟨359858, by rfl⟩ : syracuseStep 1919245 = 719717) (by norm_num)
theorem B2558237 : Blo 1705053 2558237 := bbase (se 3 (by rfl) ⟨479669, by rfl⟩ : syracuseStep 2558237 = 959339) (by norm_num)
theorem B1919281 : Blo 1705053 1919281 := bbase (se 2 (by rfl) ⟨719730, by rfl⟩ : syracuseStep 1919281 = 1439461) (by norm_num)
theorem B2558261 : Blo 1705053 2558261 := bbase (se 5 (by rfl) ⟨119918, by rfl⟩ : syracuseStep 2558261 = 239837) (by norm_num)
theorem B2558285 : Blo 1705053 2558285 := bbase (se 3 (by rfl) ⟨479678, by rfl⟩ : syracuseStep 2558285 = 959357) (by norm_num)
theorem B2877781 : Blo 1705053 2877781 := bbase (se 10 (by rfl) ⟨4215, by rfl⟩ : syracuseStep 2877781 = 8431) (by norm_num)
theorem B1919317 : Blo 1705053 1919317 := bbase (se 10 (by rfl) ⟨2811, by rfl⟩ : syracuseStep 1919317 = 5623) (by norm_num)
theorem B2558309 : Blo 1705053 2558309 := bbase (se 4 (by rfl) ⟨239841, by rfl⟩ : syracuseStep 2558309 = 479683) (by norm_num)
theorem B1919353 : Blo 1705053 1919353 := bbase (se 2 (by rfl) ⟨719757, by rfl⟩ : syracuseStep 1919353 = 1439515) (by norm_num)
theorem B2558333 : Blo 1705053 2558333 := bbase (se 3 (by rfl) ⟨479687, by rfl⟩ : syracuseStep 2558333 = 959375) (by norm_num)
theorem B8751509 : Blo 1705053 8751509 := bbase (se 6 (by rfl) ⟨205113, by rfl⟩ : syracuseStep 8751509 = 410227) (by norm_num)
theorem B2558357 : Blo 1705053 2558357 := bbase (se 6 (by rfl) ⟨59961, by rfl⟩ : syracuseStep 2558357 = 119923) (by norm_num)
theorem B1919389 : Blo 1705053 1919389 := bbase (se 3 (by rfl) ⟨359885, by rfl⟩ : syracuseStep 1919389 = 719771) (by norm_num)
theorem B3238309 : Blo 1705053 3238309 := bbase (se 4 (by rfl) ⟨303591, by rfl⟩ : syracuseStep 3238309 = 607183) (by norm_num)
theorem B2877869 : Blo 1705053 2877869 := bbase (se 3 (by rfl) ⟨539600, by rfl⟩ : syracuseStep 2877869 = 1079201) (by norm_num)
theorem B2558381 : Blo 1705053 2558381 := bbase (se 3 (by rfl) ⟨479696, by rfl⟩ : syracuseStep 2558381 = 959393) (by norm_num)
theorem B4319669 : Blo 1705053 4319669 := bbase (se 5 (by rfl) ⟨202484, by rfl⟩ : syracuseStep 4319669 = 404969) (by norm_num)
theorem B1919425 : Blo 1705053 1919425 := bbase (se 2 (by rfl) ⟨719784, by rfl⟩ : syracuseStep 1919425 = 1439569) (by norm_num)
theorem B2558405 : Blo 1705053 2558405 := bbase (se 4 (by rfl) ⟨239850, by rfl⟩ : syracuseStep 2558405 = 479701) (by norm_num)
theorem B2558429 : Blo 1705053 2558429 := bbase (se 3 (by rfl) ⟨479705, by rfl⟩ : syracuseStep 2558429 = 959411) (by norm_num)
theorem B1919461 : Blo 1705053 1919461 := bbase (se 4 (by rfl) ⟨179949, by rfl⟩ : syracuseStep 1919461 = 359899) (by norm_num)
theorem B6146549 : Blo 1705053 6146549 := bbase (se 5 (by rfl) ⟨288119, by rfl⟩ : syracuseStep 6146549 = 576239) (by norm_num)
theorem B2558453 : Blo 1705053 2558453 := bbase (se 5 (by rfl) ⟨119927, by rfl⟩ : syracuseStep 2558453 = 239855) (by norm_num)
theorem B1919497 : Blo 1705053 1919497 := bbase (se 2 (by rfl) ⟨719811, by rfl⟩ : syracuseStep 1919497 = 1439623) (by norm_num)
theorem B3836429 : Blo 1705053 3836429 := bbase (se 3 (by rfl) ⟨719330, by rfl⟩ : syracuseStep 3836429 = 1438661) (by norm_num)
theorem B2558477 : Blo 1705053 2558477 := bbase (se 3 (by rfl) ⟨479714, by rfl⟩ : syracuseStep 2558477 = 959429) (by norm_num)
theorem B2558501 : Blo 1705053 2558501 := bbase (se 4 (by rfl) ⟨239859, by rfl⟩ : syracuseStep 2558501 = 479719) (by norm_num)
theorem B2877997 : Blo 1705053 2877997 := bbase (se 3 (by rfl) ⟨539624, by rfl⟩ : syracuseStep 2877997 = 1079249) (by norm_num)
theorem B1919533 : Blo 1705053 1919533 := bbase (se 3 (by rfl) ⟨359912, by rfl⟩ : syracuseStep 1919533 = 719825) (by norm_num)
theorem B2558525 : Blo 1705053 2558525 := bbase (se 3 (by rfl) ⟨479723, by rfl⟩ : syracuseStep 2558525 = 959447) (by norm_num)
theorem B1919569 : Blo 1705053 1919569 := bbase (se 2 (by rfl) ⟨719838, by rfl⟩ : syracuseStep 1919569 = 1439677) (by norm_num)
theorem B3836501 : Blo 1705053 3836501 := bbase (se 8 (by rfl) ⟨22479, by rfl⟩ : syracuseStep 3836501 = 44959) (by norm_num)
theorem B2558549 : Blo 1705053 2558549 := bbase (se 8 (by rfl) ⟨14991, by rfl⟩ : syracuseStep 2558549 = 29983) (by norm_num)
theorem B8637029 : Blo 1705053 8637029 := bbase (se 4 (by rfl) ⟨809721, by rfl⟩ : syracuseStep 8637029 = 1619443) (by norm_num)
theorem B2558573 : Blo 1705053 2558573 := bbase (se 3 (by rfl) ⟨479732, by rfl⟩ : syracuseStep 2558573 = 959465) (by norm_num)
theorem B1919605 : Blo 1705053 1919605 := bbase (se 5 (by rfl) ⟨89981, by rfl⟩ : syracuseStep 1919605 = 179963) (by norm_num)
theorem B2878085 : Blo 1705053 2878085 := bbase (se 4 (by rfl) ⟨269820, by rfl⟩ : syracuseStep 2878085 = 539641) (by norm_num)
theorem B2558597 : Blo 1705053 2558597 := bbase (se 4 (by rfl) ⟨239868, by rfl⟩ : syracuseStep 2558597 = 479737) (by norm_num)
theorem B16403093 : Blo 1705053 16403093 := bbase (se 6 (by rfl) ⟨384447, by rfl⟩ : syracuseStep 16403093 = 768895) (by norm_num)
theorem B1919641 : Blo 1705053 1919641 := bbase (se 2 (by rfl) ⟨719865, by rfl⟩ : syracuseStep 1919641 = 1439731) (by norm_num)
theorem B3836573 : Blo 1705053 3836573 := bbase (se 3 (by rfl) ⟨719357, by rfl⟩ : syracuseStep 3836573 = 1438715) (by norm_num)
theorem B2558621 : Blo 1705053 2558621 := bbase (se 3 (by rfl) ⟨479741, by rfl⟩ : syracuseStep 2558621 = 959483) (by norm_num)
theorem B2558645 : Blo 1705053 2558645 := bbase (se 5 (by rfl) ⟨119936, by rfl⟩ : syracuseStep 2558645 = 239873) (by norm_num)
theorem B1919677 : Blo 1705053 1919677 := bbase (se 3 (by rfl) ⟨359939, by rfl⟩ : syracuseStep 1919677 = 719879) (by norm_num)
theorem B2558669 : Blo 1705053 2558669 := bbase (se 3 (by rfl) ⟨479750, by rfl⟩ : syracuseStep 2558669 = 959501) (by norm_num)
theorem B3238613 : Blo 1705053 3238613 := bbase (se 7 (by rfl) ⟨37952, by rfl⟩ : syracuseStep 3238613 = 75905) (by norm_num)
theorem B7785173 : Blo 1705053 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B1919713 : Blo 1705053 1919713 := bbase (se 2 (by rfl) ⟨719892, by rfl⟩ : syracuseStep 1919713 = 1439785) (by norm_num)
theorem B3836645 : Blo 1705053 3836645 := bbase (se 4 (by rfl) ⟨359685, by rfl⟩ : syracuseStep 3836645 = 719371) (by norm_num)
theorem B2558693 : Blo 1705053 2558693 := bbase (se 4 (by rfl) ⟨239877, by rfl⟩ : syracuseStep 2558693 = 479755) (by norm_num)
theorem B2558717 : Blo 1705053 2558717 := bbase (se 3 (by rfl) ⟨479759, by rfl⟩ : syracuseStep 2558717 = 959519) (by norm_num)
theorem B2878213 : Blo 1705053 2878213 := bbase (se 4 (by rfl) ⟨269832, by rfl⟩ : syracuseStep 2878213 = 539665) (by norm_num)
theorem B1919749 : Blo 1705053 1919749 := bbase (se 4 (by rfl) ⟨179976, by rfl⟩ : syracuseStep 1919749 = 359953) (by norm_num)
theorem B4320013 : Blo 1705053 4320013 := bbase (se 3 (by rfl) ⟨810002, by rfl⟩ : syracuseStep 4320013 = 1620005) (by norm_num)
theorem B2558741 : Blo 1705053 2558741 := bbase (se 6 (by rfl) ⟨59970, by rfl⟩ : syracuseStep 2558741 = 119941) (by norm_num)
theorem B8203045 : Blo 1705053 8203045 := bbase (se 4 (by rfl) ⟨769035, by rfl⟩ : syracuseStep 8203045 = 1538071) (by norm_num)
theorem B1919785 : Blo 1705053 1919785 := bbase (se 2 (by rfl) ⟨719919, by rfl⟩ : syracuseStep 1919785 = 1439839) (by norm_num)
theorem B3836717 : Blo 1705053 3836717 := bbase (se 3 (by rfl) ⟨719384, by rfl⟩ : syracuseStep 3836717 = 1438769) (by norm_num)
theorem B2558765 : Blo 1705053 2558765 := bbase (se 3 (by rfl) ⟨479768, by rfl⟩ : syracuseStep 2558765 = 959537) (by norm_num)
theorem B2558789 : Blo 1705053 2558789 := bbase (se 4 (by rfl) ⟨239886, by rfl⟩ : syracuseStep 2558789 = 479773) (by norm_num)
theorem B1919821 : Blo 1705053 1919821 := bbase (se 3 (by rfl) ⟨359966, by rfl⟩ : syracuseStep 1919821 = 719933) (by norm_num)
theorem B2878301 : Blo 1705053 2878301 := bbase (se 3 (by rfl) ⟨539681, by rfl⟩ : syracuseStep 2878301 = 1079363) (by norm_num)
theorem B2558813 : Blo 1705053 2558813 := bbase (se 3 (by rfl) ⟨479777, by rfl⟩ : syracuseStep 2558813 = 959555) (by norm_num)
theorem B1919857 : Blo 1705053 1919857 := bbase (se 2 (by rfl) ⟨719946, by rfl⟩ : syracuseStep 1919857 = 1439893) (by norm_num)
theorem B3836789 : Blo 1705053 3836789 := bbase (se 5 (by rfl) ⟨179849, by rfl⟩ : syracuseStep 3836789 = 359699) (by norm_num)
theorem B6474613 : Blo 1705053 6474613 := bbase (se 5 (by rfl) ⟨303497, by rfl⟩ : syracuseStep 6474613 = 606995) (by norm_num)
theorem B2558837 : Blo 1705053 2558837 := bbase (se 5 (by rfl) ⟨119945, by rfl⟩ : syracuseStep 2558837 = 239891) (by norm_num)
theorem B4320125 : Blo 1705053 4320125 := bbase (se 3 (by rfl) ⟨810023, by rfl⟩ : syracuseStep 4320125 = 1620047) (by norm_num)
theorem B2558861 : Blo 1705053 2558861 := bbase (se 3 (by rfl) ⟨479786, by rfl⟩ : syracuseStep 2558861 = 959573) (by norm_num)
theorem B1919893 : Blo 1705053 1919893 := bbase (se 6 (by rfl) ⟨44997, by rfl⟩ : syracuseStep 1919893 = 89995) (by norm_num)
theorem B2558885 : Blo 1705053 2558885 := bbase (se 4 (by rfl) ⟨239895, by rfl⟩ : syracuseStep 2558885 = 479791) (by norm_num)
theorem B3074989 : Blo 1705053 3074989 := bbase (se 3 (by rfl) ⟨576560, by rfl⟩ : syracuseStep 3074989 = 1153121) (by norm_num)
theorem B1919929 : Blo 1705053 1919929 := bbase (se 2 (by rfl) ⟨719973, by rfl⟩ : syracuseStep 1919929 = 1439947) (by norm_num)
theorem B3836861 : Blo 1705053 3836861 := bbase (se 3 (by rfl) ⟨719411, by rfl⟩ : syracuseStep 3836861 = 1438823) (by norm_num)
theorem B2558909 : Blo 1705053 2558909 := bbase (se 3 (by rfl) ⟨479795, by rfl⟩ : syracuseStep 2558909 = 959591) (by norm_num)
theorem B7285717 : Blo 1705053 7285717 := bbase (se 7 (by rfl) ⟨85379, by rfl⟩ : syracuseStep 7285717 = 170759) (by norm_num)
theorem B2558933 : Blo 1705053 2558933 := bbase (se 7 (by rfl) ⟨29987, by rfl⟩ : syracuseStep 2558933 = 59975) (by norm_num)
theorem B14576597 : Blo 1705053 14576597 := bbase (se 7 (by rfl) ⟨170819, by rfl⟩ : syracuseStep 14576597 = 341639) (by norm_num)
theorem B2878429 : Blo 1705053 2878429 := bbase (se 3 (by rfl) ⟨539705, by rfl⟩ : syracuseStep 2878429 = 1079411) (by norm_num)
theorem B1919965 : Blo 1705053 1919965 := bbase (se 3 (by rfl) ⟨359993, by rfl⟩ : syracuseStep 1919965 = 719987) (by norm_num)
theorem B2558957 : Blo 1705053 2558957 := bbase (se 3 (by rfl) ⟨479804, by rfl⟩ : syracuseStep 2558957 = 959609) (by norm_num)
theorem B1920001 : Blo 1705053 1920001 := bbase (se 2 (by rfl) ⟨720000, by rfl⟩ : syracuseStep 1920001 = 1440001) (by norm_num)
theorem B3836933 : Blo 1705053 3836933 := bbase (se 4 (by rfl) ⟨359712, by rfl⟩ : syracuseStep 3836933 = 719425) (by norm_num)
theorem B2558981 : Blo 1705053 2558981 := bbase (se 4 (by rfl) ⟨239904, by rfl⟩ : syracuseStep 2558981 = 479809) (by norm_num)
theorem B3075077 : Blo 1705053 3075077 := bbase (se 4 (by rfl) ⟨288288, by rfl⟩ : syracuseStep 3075077 = 576577) (by norm_num)
theorem B2559005 : Blo 1705053 2559005 := bbase (se 3 (by rfl) ⟨479813, by rfl⟩ : syracuseStep 2559005 = 959627) (by norm_num)
theorem B1920037 : Blo 1705053 1920037 := bbase (se 4 (by rfl) ⟨180003, by rfl⟩ : syracuseStep 1920037 = 360007) (by norm_num)
theorem B1821737 : Blo 1705053 1821737 := bbase (se 2 (by rfl) ⟨683151, by rfl⟩ : syracuseStep 1821737 = 1366303) (by norm_num)
theorem B2878517 : Blo 1705053 2878517 := bbase (se 5 (by rfl) ⟨134930, by rfl⟩ : syracuseStep 2878517 = 269861) (by norm_num)
theorem B2559029 : Blo 1705053 2559029 := bbase (se 5 (by rfl) ⟨119954, by rfl⟩ : syracuseStep 2559029 = 239909) (by norm_num)
theorem B3075133 : Blo 1705053 3075133 := bbase (se 3 (by rfl) ⟨576587, by rfl⟩ : syracuseStep 3075133 = 1153175) (by norm_num)
theorem B4320317 : Blo 1705053 4320317 := bbase (se 3 (by rfl) ⟨810059, by rfl⟩ : syracuseStep 4320317 = 1620119) (by norm_num)
theorem B1920073 : Blo 1705053 1920073 := bbase (se 2 (by rfl) ⟨720027, by rfl⟩ : syracuseStep 1920073 = 1440055) (by norm_num)
theorem B3837005 : Blo 1705053 3837005 := bbase (se 3 (by rfl) ⟨719438, by rfl⟩ : syracuseStep 3837005 = 1438877) (by norm_num)
theorem B2559053 : Blo 1705053 2559053 := bbase (se 3 (by rfl) ⟨479822, by rfl⟩ : syracuseStep 2559053 = 959645) (by norm_num)
theorem B1944661 : Blo 1705053 1944661 := bbase (se 8 (by rfl) ⟨11394, by rfl⟩ : syracuseStep 1944661 = 22789) (by norm_num)
theorem B2559077 : Blo 1705053 2559077 := bbase (se 4 (by rfl) ⟨239913, by rfl⟩ : syracuseStep 2559077 = 479827) (by norm_num)
theorem B1920109 : Blo 1705053 1920109 := bbase (se 3 (by rfl) ⟨360020, by rfl⟩ : syracuseStep 1920109 = 720041) (by norm_num)
theorem B2559101 : Blo 1705053 2559101 := bbase (se 3 (by rfl) ⟨479831, by rfl⟩ : syracuseStep 2559101 = 959663) (by norm_num)
theorem B1920145 : Blo 1705053 1920145 := bbase (se 2 (by rfl) ⟨720054, by rfl⟩ : syracuseStep 1920145 = 1440109) (by norm_num)
theorem B3837077 : Blo 1705053 3837077 := bbase (se 6 (by rfl) ⟨89931, by rfl⟩ : syracuseStep 3837077 = 179863) (by norm_num)
theorem B2559125 : Blo 1705053 2559125 := bbase (se 6 (by rfl) ⟨59979, by rfl⟩ : syracuseStep 2559125 = 119959) (by norm_num)
theorem B6474917 : Blo 1705053 6474917 := bbase (se 4 (by rfl) ⟨607023, by rfl⟩ : syracuseStep 6474917 = 1214047) (by norm_num)
theorem B2559149 : Blo 1705053 2559149 := bbase (se 3 (by rfl) ⟨479840, by rfl⟩ : syracuseStep 2559149 = 959681) (by norm_num)
theorem B2878645 : Blo 1705053 2878645 := bbase (se 5 (by rfl) ⟨134936, by rfl⟩ : syracuseStep 2878645 = 269873) (by norm_num)
theorem B1920181 : Blo 1705053 1920181 := bbase (se 5 (by rfl) ⟨90008, by rfl⟩ : syracuseStep 1920181 = 180017) (by norm_num)
theorem B2559173 : Blo 1705053 2559173 := bbase (se 4 (by rfl) ⟨239922, by rfl⟩ : syracuseStep 2559173 = 479845) (by norm_num)
theorem B1920217 : Blo 1705053 1920217 := bbase (se 2 (by rfl) ⟨720081, by rfl⟩ : syracuseStep 1920217 = 1440163) (by norm_num)
theorem B3837149 : Blo 1705053 3837149 := bbase (se 3 (by rfl) ⟨719465, by rfl⟩ : syracuseStep 3837149 = 1438931) (by norm_num)
theorem B2559197 : Blo 1705053 2559197 := bbase (se 3 (by rfl) ⟨479849, by rfl⟩ : syracuseStep 2559197 = 959699) (by norm_num)
theorem B2559221 : Blo 1705053 2559221 := bbase (se 5 (by rfl) ⟨119963, by rfl⟩ : syracuseStep 2559221 = 239927) (by norm_num)
theorem B2428157 : Blo 1705053 2428157 := bbase (se 3 (by rfl) ⟨455279, by rfl⟩ : syracuseStep 2428157 = 910559) (by norm_num)
theorem B1920253 : Blo 1705053 1920253 := bbase (se 3 (by rfl) ⟨360047, by rfl⟩ : syracuseStep 1920253 = 720095) (by norm_num)
theorem B2878733 : Blo 1705053 2878733 := bbase (se 3 (by rfl) ⟨539762, by rfl⟩ : syracuseStep 2878733 = 1079525) (by norm_num)
theorem B2559245 : Blo 1705053 2559245 := bbase (se 3 (by rfl) ⟨479858, by rfl⟩ : syracuseStep 2559245 = 959717) (by norm_num)
theorem B1920289 : Blo 1705053 1920289 := bbase (se 2 (by rfl) ⟨720108, by rfl⟩ : syracuseStep 1920289 = 1440217) (by norm_num)
theorem B3837221 : Blo 1705053 3837221 := bbase (se 4 (by rfl) ⟨359739, by rfl⟩ : syracuseStep 3837221 = 719479) (by norm_num)
theorem B6917413 : Blo 1705053 6917413 := bbase (se 4 (by rfl) ⟨648507, by rfl⟩ : syracuseStep 6917413 = 1297015) (by norm_num)
theorem B2559269 : Blo 1705053 2559269 := bbase (se 4 (by rfl) ⟨239931, by rfl⟩ : syracuseStep 2559269 = 479863) (by norm_num)
theorem B2305333 : Blo 1705053 2305333 := bbase (se 5 (by rfl) ⟨108062, by rfl⟩ : syracuseStep 2305333 = 216125) (by norm_num)
theorem B2559293 : Blo 1705053 2559293 := bbase (se 3 (by rfl) ⟨479867, by rfl⟩ : syracuseStep 2559293 = 959735) (by norm_num)
theorem B1920325 : Blo 1705053 1920325 := bbase (se 4 (by rfl) ⟨180030, by rfl⟩ : syracuseStep 1920325 = 360061) (by norm_num)
theorem B2559317 : Blo 1705053 2559317 := bbase (se 11 (by rfl) ⟨1874, by rfl⟩ : syracuseStep 2559317 = 3749) (by norm_num)
theorem B5467493 : Blo 1705053 5467493 := bbase (se 4 (by rfl) ⟨512577, by rfl⟩ : syracuseStep 5467493 = 1025155) (by norm_num)
theorem B1920361 : Blo 1705053 1920361 := bbase (se 2 (by rfl) ⟨720135, by rfl⟩ : syracuseStep 1920361 = 1440271) (by norm_num)
theorem B2461037 : Blo 1705053 2461037 := bbase (se 3 (by rfl) ⟨461444, by rfl⟩ : syracuseStep 2461037 = 922889) (by norm_num)
theorem B3837293 : Blo 1705053 3837293 := bbase (se 3 (by rfl) ⟨719492, by rfl⟩ : syracuseStep 3837293 = 1438985) (by norm_num)
theorem B2559341 : Blo 1705053 2559341 := bbase (se 3 (by rfl) ⟨479876, by rfl⟩ : syracuseStep 2559341 = 959753) (by norm_num)
theorem B2559365 : Blo 1705053 2559365 := bbase (se 4 (by rfl) ⟨239940, by rfl⟩ : syracuseStep 2559365 = 479881) (by norm_num)
theorem B2878861 : Blo 1705053 2878861 := bbase (se 3 (by rfl) ⟨539786, by rfl⟩ : syracuseStep 2878861 = 1079573) (by norm_num)
theorem B1920397 : Blo 1705053 1920397 := bbase (se 3 (by rfl) ⟨360074, by rfl⟩ : syracuseStep 1920397 = 720149) (by norm_num)
theorem B9719189 : Blo 1705053 9719189 := bbase (se 6 (by rfl) ⟨227793, by rfl⟩ : syracuseStep 9719189 = 455587) (by norm_num)
theorem B4320661 : Blo 1705053 4320661 := bbase (se 6 (by rfl) ⟨101265, by rfl⟩ : syracuseStep 4320661 = 202531) (by norm_num)
theorem B2731421 : Blo 1705053 2731421 := bbase (se 3 (by rfl) ⟨512141, by rfl⟩ : syracuseStep 2731421 = 1024283) (by norm_num)
theorem B2559389 : Blo 1705053 2559389 := bbase (se 3 (by rfl) ⟨479885, by rfl⟩ : syracuseStep 2559389 = 959771) (by norm_num)
theorem B2157997 : Blo 1705053 2157997 := bbase (se 3 (by rfl) ⟨404624, by rfl⟩ : syracuseStep 2157997 = 809249) (by norm_num)
theorem B1920433 : Blo 1705053 1920433 := bbase (se 2 (by rfl) ⟨720162, by rfl⟩ : syracuseStep 1920433 = 1440325) (by norm_num)
theorem B8195509 : Blo 1705053 8195509 := bbase (se 5 (by rfl) ⟨384164, by rfl⟩ : syracuseStep 8195509 = 768329) (by norm_num)
theorem B3837365 : Blo 1705053 3837365 := bbase (se 5 (by rfl) ⟨179876, by rfl⟩ : syracuseStep 3837365 = 359753) (by norm_num)
theorem B6917557 : Blo 1705053 6917557 := bbase (se 5 (by rfl) ⟨324260, by rfl⟩ : syracuseStep 6917557 = 648521) (by norm_num)
theorem B2559413 : Blo 1705053 2559413 := bbase (se 5 (by rfl) ⟨119972, by rfl⟩ : syracuseStep 2559413 = 239945) (by norm_num)
theorem B3239365 : Blo 1705053 3239365 := bbase (se 4 (by rfl) ⟨303690, by rfl⟩ : syracuseStep 3239365 = 607381) (by norm_num)
theorem B2559437 : Blo 1705053 2559437 := bbase (se 3 (by rfl) ⟨479894, by rfl⟩ : syracuseStep 2559437 = 959789) (by norm_num)
theorem B2878949 : Blo 1705053 2878949 := bbase (se 4 (by rfl) ⟨269901, by rfl⟩ : syracuseStep 2878949 = 539803) (by norm_num)
theorem B2559461 : Blo 1705053 2559461 := bbase (se 4 (by rfl) ⟨239949, by rfl⟩ : syracuseStep 2559461 = 479899) (by norm_num)
theorem B1822181 : Blo 1705053 1822181 := bbase (se 4 (by rfl) ⟨170829, by rfl⟩ : syracuseStep 1822181 = 341659) (by norm_num)
theorem B5467621 : Blo 1705053 5467621 := bbase (se 4 (by rfl) ⟨512589, by rfl⟩ : syracuseStep 5467621 = 1025179) (by norm_num)
theorem B3837437 : Blo 1705053 3837437 := bbase (se 3 (by rfl) ⟨719519, by rfl⟩ : syracuseStep 3837437 = 1439039) (by norm_num)
theorem B2559485 : Blo 1705053 2559485 := bbase (se 3 (by rfl) ⟨479903, by rfl⟩ : syracuseStep 2559485 = 959807) (by norm_num)
theorem B4320773 : Blo 1705053 4320773 := bbase (se 4 (by rfl) ⟨405072, by rfl⟩ : syracuseStep 4320773 = 810145) (by norm_num)
theorem B2158093 : Blo 1705053 2158093 := bbase (se 3 (by rfl) ⟨404642, by rfl⟩ : syracuseStep 2158093 = 809285) (by norm_num)
theorem B2559509 : Blo 1705053 2559509 := bbase (se 6 (by rfl) ⟨59988, by rfl⟩ : syracuseStep 2559509 = 119977) (by norm_num)
theorem B2559533 : Blo 1705053 2559533 := bbase (se 3 (by rfl) ⟨479912, by rfl⟩ : syracuseStep 2559533 = 959825) (by norm_num)
theorem B3837509 : Blo 1705053 3837509 := bbase (se 4 (by rfl) ⟨359766, by rfl⟩ : syracuseStep 3837509 = 719533) (by norm_num)
theorem B2559557 : Blo 1705053 2559557 := bbase (se 4 (by rfl) ⟨239958, by rfl⟩ : syracuseStep 2559557 = 479917) (by norm_num)
theorem B3239509 : Blo 1705053 3239509 := bbase (se 8 (by rfl) ⟨18981, by rfl⟩ : syracuseStep 3239509 = 37963) (by norm_num)
theorem B2559581 : Blo 1705053 2559581 := bbase (se 3 (by rfl) ⟨479921, by rfl⟩ : syracuseStep 2559581 = 959843) (by norm_num)
theorem B2879077 : Blo 1705053 2879077 := bbase (se 4 (by rfl) ⟨269913, by rfl⟩ : syracuseStep 2879077 = 539827) (by norm_num)
theorem B2559605 : Blo 1705053 2559605 := bbase (se 5 (by rfl) ⟨119981, by rfl⟩ : syracuseStep 2559605 = 239963) (by norm_num)
theorem B3837581 : Blo 1705053 3837581 := bbase (se 3 (by rfl) ⟨719546, by rfl⟩ : syracuseStep 3837581 = 1439093) (by norm_num)
theorem B2559629 : Blo 1705053 2559629 := bbase (se 3 (by rfl) ⟨479930, by rfl⟩ : syracuseStep 2559629 = 959861) (by norm_num)
theorem B2559653 : Blo 1705053 2559653 := bbase (se 4 (by rfl) ⟨239967, by rfl⟩ : syracuseStep 2559653 = 479935) (by norm_num)
theorem B2158265 : Blo 1705053 2158265 := bbase (se 2 (by rfl) ⟨809349, by rfl⟩ : syracuseStep 2158265 = 1618699) (by norm_num)
theorem B2879165 : Blo 1705053 2879165 := bbase (se 3 (by rfl) ⟨539843, by rfl⟩ : syracuseStep 2879165 = 1079687) (by norm_num)
theorem B2559677 : Blo 1705053 2559677 := bbase (se 3 (by rfl) ⟨479939, by rfl⟩ : syracuseStep 2559677 = 959879) (by norm_num)
theorem B4320965 : Blo 1705053 4320965 := bbase (se 4 (by rfl) ⟨405090, by rfl⟩ : syracuseStep 4320965 = 810181) (by norm_num)
theorem B3837653 : Blo 1705053 3837653 := bbase (se 7 (by rfl) ⟨44972, by rfl⟩ : syracuseStep 3837653 = 89945) (by norm_num)
theorem B2559701 : Blo 1705053 2559701 := bbase (se 7 (by rfl) ⟨29996, by rfl⟩ : syracuseStep 2559701 = 59993) (by norm_num)
theorem B1822429 : Blo 1705053 1822429 := bbase (se 3 (by rfl) ⟨341705, by rfl⟩ : syracuseStep 1822429 = 683411) (by norm_num)
theorem B5467877 : Blo 1705053 5467877 := bbase (se 4 (by rfl) ⟨512613, by rfl⟩ : syracuseStep 5467877 = 1025227) (by norm_num)
theorem B2559725 : Blo 1705053 2559725 := bbase (se 3 (by rfl) ⟨479948, by rfl⟩ : syracuseStep 2559725 = 959897) (by norm_num)
theorem B2158321 : Blo 1705053 2158321 := bbase (se 2 (by rfl) ⟨809370, by rfl⟩ : syracuseStep 2158321 = 1618741) (by norm_num)
theorem B3239669 : Blo 1705053 3239669 := bbase (se 5 (by rfl) ⟨151859, by rfl⟩ : syracuseStep 3239669 = 303719) (by norm_num)
theorem B2559749 : Blo 1705053 2559749 := bbase (se 4 (by rfl) ⟨239976, by rfl⟩ : syracuseStep 2559749 = 479953) (by norm_num)
theorem B3837725 : Blo 1705053 3837725 := bbase (se 3 (by rfl) ⟨719573, by rfl⟩ : syracuseStep 3837725 = 1439147) (by norm_num)
theorem B2559773 : Blo 1705053 2559773 := bbase (se 3 (by rfl) ⟨479957, by rfl⟩ : syracuseStep 2559773 = 959915) (by norm_num)
theorem B2428709 : Blo 1705053 2428709 := bbase (se 4 (by rfl) ⟨227691, by rfl⟩ : syracuseStep 2428709 = 455383) (by norm_num)
theorem B4378421 : Blo 1705053 4378421 := bbase (se 5 (by rfl) ⟨205238, by rfl⟩ : syracuseStep 4378421 = 410477) (by norm_num)
theorem B2559797 : Blo 1705053 2559797 := bbase (se 5 (by rfl) ⟨119990, by rfl⟩ : syracuseStep 2559797 = 239981) (by norm_num)
theorem B2879293 : Blo 1705053 2879293 := bbase (se 3 (by rfl) ⟨539867, by rfl⟩ : syracuseStep 2879293 = 1079735) (by norm_num)
theorem B2559821 : Blo 1705053 2559821 := bbase (se 3 (by rfl) ⟨479966, by rfl⟩ : syracuseStep 2559821 = 959933) (by norm_num)
theorem B2158417 : Blo 1705053 2158417 := bbase (se 2 (by rfl) ⟨809406, by rfl⟩ : syracuseStep 2158417 = 1618813) (by norm_num)
theorem B5754725 : Blo 1705053 5754725 := bbase (se 4 (by rfl) ⟨539505, by rfl⟩ : syracuseStep 5754725 = 1079011) (by norm_num)
theorem B3837797 : Blo 1705053 3837797 := bbase (se 4 (by rfl) ⟨359793, by rfl⟩ : syracuseStep 3837797 = 719587) (by norm_num)
theorem B2559845 : Blo 1705053 2559845 := bbase (se 4 (by rfl) ⟨239985, by rfl⟩ : syracuseStep 2559845 = 479971) (by norm_num)
theorem B8638325 : Blo 1705053 8638325 := bbase (se 5 (by rfl) ⟨404921, by rfl⟩ : syracuseStep 8638325 = 809843) (by norm_num)
theorem B2559869 : Blo 1705053 2559869 := bbase (se 3 (by rfl) ⟨479975, by rfl⟩ : syracuseStep 2559869 = 959951) (by norm_num)
theorem B3239813 : Blo 1705053 3239813 := bbase (se 4 (by rfl) ⟨303732, by rfl⟩ : syracuseStep 3239813 = 607465) (by norm_num)
theorem B2879381 : Blo 1705053 2879381 := bbase (se 6 (by rfl) ⟨67485, by rfl⟩ : syracuseStep 2879381 = 134971) (by norm_num)
theorem B2559893 : Blo 1705053 2559893 := bbase (se 6 (by rfl) ⟨59997, by rfl⟩ : syracuseStep 2559893 = 119995) (by norm_num)
theorem B3837869 : Blo 1705053 3837869 := bbase (se 3 (by rfl) ⟨719600, by rfl⟩ : syracuseStep 3837869 = 1439201) (by norm_num)
theorem B2559917 : Blo 1705053 2559917 := bbase (se 3 (by rfl) ⟨479984, by rfl⟩ : syracuseStep 2559917 = 959969) (by norm_num)
theorem B2559941 : Blo 1705053 2559941 := bbase (se 4 (by rfl) ⟨239994, by rfl⟩ : syracuseStep 2559941 = 479989) (by norm_num)
theorem B2559965 : Blo 1705053 2559965 := bbase (se 3 (by rfl) ⟨479993, by rfl⟩ : syracuseStep 2559965 = 959987) (by norm_num)
theorem B7786469 : Blo 1705053 7786469 := bbase (se 4 (by rfl) ⟨729981, by rfl⟩ : syracuseStep 7786469 = 1459963) (by norm_num)
theorem B3837941 : Blo 1705053 3837941 := bbase (se 5 (by rfl) ⟨179903, by rfl⟩ : syracuseStep 3837941 = 359807) (by norm_num)
theorem B2559989 : Blo 1705053 2559989 := bbase (se 5 (by rfl) ⟨119999, by rfl⟩ : syracuseStep 2559989 = 239999) (by norm_num)
theorem B2158589 : Blo 1705053 2158589 := bbase (se 3 (by rfl) ⟨404735, by rfl⟩ : syracuseStep 2158589 = 809471) (by norm_num)
theorem B1945609 : Blo 1705053 1945609 := bbase (se 2 (by rfl) ⟨729603, by rfl⟩ : syracuseStep 1945609 = 1459207) (by norm_num)
theorem B2560013 : Blo 1705053 2560013 := bbase (se 3 (by rfl) ⟨480002, by rfl⟩ : syracuseStep 2560013 = 960005) (by norm_num)
theorem B10932245 : Blo 1705053 10932245 := bbase (se 6 (by rfl) ⟨256224, by rfl⟩ : syracuseStep 10932245 = 512449) (by norm_num)
theorem B2879509 : Blo 1705053 2879509 := bbase (se 6 (by rfl) ⟨67488, by rfl⟩ : syracuseStep 2879509 = 134977) (by norm_num)
theorem B6148133 : Blo 1705053 6148133 := bbase (se 4 (by rfl) ⟨576387, by rfl⟩ : syracuseStep 6148133 = 1152775) (by norm_num)
theorem B2560037 : Blo 1705053 2560037 := bbase (se 4 (by rfl) ⟨240003, by rfl⟩ : syracuseStep 2560037 = 480007) (by norm_num)
theorem B2158645 : Blo 1705053 2158645 := bbase (se 5 (by rfl) ⟨101186, by rfl⟩ : syracuseStep 2158645 = 202373) (by norm_num)
theorem B3838013 : Blo 1705053 3838013 := bbase (se 3 (by rfl) ⟨719627, by rfl⟩ : syracuseStep 3838013 = 1439255) (by norm_num)
theorem B2560061 : Blo 1705053 2560061 := bbase (se 3 (by rfl) ⟨480011, by rfl⟩ : syracuseStep 2560061 = 960023) (by norm_num)
theorem B24588373 : Blo 1705053 24588373 := bbase (se 8 (by rfl) ⟨144072, by rfl⟩ : syracuseStep 24588373 = 288145) (by norm_num)
theorem B2560085 : Blo 1705053 2560085 := bbase (se 8 (by rfl) ⟨15000, by rfl⟩ : syracuseStep 2560085 = 30001) (by norm_num)
theorem B2879597 : Blo 1705053 2879597 := bbase (se 3 (by rfl) ⟨539924, by rfl⟩ : syracuseStep 2879597 = 1079849) (by norm_num)
theorem B2560109 : Blo 1705053 2560109 := bbase (se 3 (by rfl) ⟨480020, by rfl⟩ : syracuseStep 2560109 = 960041) (by norm_num)
theorem B3838085 : Blo 1705053 3838085 := bbase (se 4 (by rfl) ⟨359820, by rfl⟩ : syracuseStep 3838085 = 719641) (by norm_num)
theorem B2560133 : Blo 1705053 2560133 := bbase (se 4 (by rfl) ⟨240012, by rfl⟩ : syracuseStep 2560133 = 480025) (by norm_num)
theorem B1822861 : Blo 1705053 1822861 := bbase (se 3 (by rfl) ⟨341786, by rfl⟩ : syracuseStep 1822861 = 683573) (by norm_num)
theorem B2158741 : Blo 1705053 2158741 := bbase (se 6 (by rfl) ⟨50595, by rfl⟩ : syracuseStep 2158741 = 101191) (by norm_num)
theorem B2560157 : Blo 1705053 2560157 := bbase (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) (by norm_num)
theorem B3240101 : Blo 1705053 3240101 := bbase (se 4 (by rfl) ⟨303759, by rfl⟩ : syracuseStep 3240101 = 607519) (by norm_num)
theorem B2560181 : Blo 1705053 2560181 := bbase (se 5 (by rfl) ⟨120008, by rfl⟩ : syracuseStep 2560181 = 240017) (by norm_num)
theorem B2732221 : Blo 1705053 2732221 := bbase (se 3 (by rfl) ⟨512291, by rfl⟩ : syracuseStep 2732221 = 1024583) (by norm_num)
theorem B2306237 : Blo 1705053 2306237 := bbase (se 3 (by rfl) ⟨432419, by rfl⟩ : syracuseStep 2306237 = 864839) (by norm_num)
theorem B2592965 : Blo 1705053 2592965 := bbase (se 4 (by rfl) ⟨243090, by rfl⟩ : syracuseStep 2592965 = 486181) (by norm_num)
theorem B3838157 : Blo 1705053 3838157 := bbase (se 3 (by rfl) ⟨719654, by rfl⟩ : syracuseStep 3838157 = 1439309) (by norm_num)
theorem B2560205 : Blo 1705053 2560205 := bbase (se 3 (by rfl) ⟨480038, by rfl⟩ : syracuseStep 2560205 = 960077) (by norm_num)
theorem B2560229 : Blo 1705053 2560229 := bbase (se 4 (by rfl) ⟨240021, by rfl⟩ : syracuseStep 2560229 = 480043) (by norm_num)
theorem B2879725 : Blo 1705053 2879725 := bbase (se 3 (by rfl) ⟨539948, by rfl⟩ : syracuseStep 2879725 = 1079897) (by norm_num)
theorem B2560253 : Blo 1705053 2560253 := bbase (se 3 (by rfl) ⟨480047, by rfl⟩ : syracuseStep 2560253 = 960095) (by norm_num)
theorem B5755157 : Blo 1705053 5755157 := bbase (se 6 (by rfl) ⟨134886, by rfl⟩ : syracuseStep 5755157 = 269773) (by norm_num)
theorem B3838229 : Blo 1705053 3838229 := bbase (se 6 (by rfl) ⟨89958, by rfl⟩ : syracuseStep 3838229 = 179917) (by norm_num)
theorem B2560277 : Blo 1705053 2560277 := bbase (se 6 (by rfl) ⟨60006, by rfl⟩ : syracuseStep 2560277 = 120013) (by norm_num)
theorem B2560301 : Blo 1705053 2560301 := bbase (se 3 (by rfl) ⟨480056, by rfl⟩ : syracuseStep 2560301 = 960113) (by norm_num)
theorem B3240253 : Blo 1705053 3240253 := bbase (se 3 (by rfl) ⟨607547, by rfl⟩ : syracuseStep 3240253 = 1215095) (by norm_num)
theorem B2158913 : Blo 1705053 2158913 := bbase (se 2 (by rfl) ⟨809592, by rfl⟩ : syracuseStep 2158913 = 1619185) (by norm_num)
theorem B2879813 : Blo 1705053 2879813 := bbase (se 4 (by rfl) ⟨269982, by rfl⟩ : syracuseStep 2879813 = 539965) (by norm_num)
theorem B2560325 : Blo 1705053 2560325 := bbase (se 4 (by rfl) ⟨240030, by rfl⟩ : syracuseStep 2560325 = 480061) (by norm_num)
theorem B27660629 : Blo 1705053 27660629 := bbase (se 10 (by rfl) ⟨40518, by rfl⟩ : syracuseStep 27660629 = 81037) (by norm_num)
theorem B3838301 : Blo 1705053 3838301 := bbase (se 3 (by rfl) ⟨719681, by rfl⟩ : syracuseStep 3838301 = 1439363) (by norm_num)
theorem B2560349 : Blo 1705053 2560349 := bbase (se 3 (by rfl) ⟨480065, by rfl⟩ : syracuseStep 2560349 = 960131) (by norm_num)
theorem B2560373 : Blo 1705053 2560373 := bbase (se 5 (by rfl) ⟨120017, by rfl⟩ : syracuseStep 2560373 = 240035) (by norm_num)
theorem B2158969 : Blo 1705053 2158969 := bbase (se 2 (by rfl) ⟨809613, by rfl⟩ : syracuseStep 2158969 = 1619227) (by norm_num)
theorem B4100485 : Blo 1705053 4100485 := bbase (se 4 (by rfl) ⟨384420, by rfl⟩ : syracuseStep 4100485 = 768841) (by norm_num)
theorem B2560397 : Blo 1705053 2560397 := bbase (se 3 (by rfl) ⟨480074, by rfl⟩ : syracuseStep 2560397 = 960149) (by norm_num)
theorem B2077085 : Blo 1705053 2077085 := bbase (se 3 (by rfl) ⟨389453, by rfl⟩ : syracuseStep 2077085 = 778907) (by norm_num)
theorem B3117469 : Blo 1705053 3117469 := bbase (se 3 (by rfl) ⟨584525, by rfl⟩ : syracuseStep 3117469 = 1169051) (by norm_num)
theorem B3641765 : Blo 1705053 3641765 := bbase (se 4 (by rfl) ⟨341415, by rfl⟩ : syracuseStep 3641765 = 682831) (by norm_num)
theorem B3838373 : Blo 1705053 3838373 := bbase (se 4 (by rfl) ⟨359847, by rfl⟩ : syracuseStep 3838373 = 719695) (by norm_num)
theorem B7287205 : Blo 1705053 7287205 := bbase (se 4 (by rfl) ⟨683175, by rfl⟩ : syracuseStep 7287205 = 1366351) (by norm_num)
theorem B2560421 : Blo 1705053 2560421 := bbase (se 4 (by rfl) ⟨240039, by rfl⟩ : syracuseStep 2560421 = 480079) (by norm_num)
theorem B7287221 : Blo 1705053 7287221 := bbase (se 5 (by rfl) ⟨341588, by rfl⟩ : syracuseStep 7287221 = 683177) (by norm_num)
theorem B2560445 : Blo 1705053 2560445 := bbase (se 3 (by rfl) ⟨480083, by rfl⟩ : syracuseStep 2560445 = 960167) (by norm_num)
theorem B2879941 : Blo 1705053 2879941 := bbase (se 4 (by rfl) ⟨269994, by rfl⟩ : syracuseStep 2879941 = 539989) (by norm_num)
theorem B2560469 : Blo 1705053 2560469 := bbase (se 7 (by rfl) ⟨30005, by rfl⟩ : syracuseStep 2560469 = 60011) (by norm_num)
theorem B2159065 : Blo 1705053 2159065 := bbase (se 2 (by rfl) ⟨809649, by rfl⟩ : syracuseStep 2159065 = 1619299) (by norm_num)
theorem B3838445 : Blo 1705053 3838445 := bbase (se 3 (by rfl) ⟨719708, by rfl⟩ : syracuseStep 3838445 = 1439417) (by norm_num)
theorem B2560493 : Blo 1705053 2560493 := bbase (se 3 (by rfl) ⟨480092, by rfl⟩ : syracuseStep 2560493 = 960185) (by norm_num)
theorem B2560517 : Blo 1705053 2560517 := bbase (se 4 (by rfl) ⟨240048, by rfl⟩ : syracuseStep 2560517 = 480097) (by norm_num)
theorem B2429461 : Blo 1705053 2429461 := bbase (se 6 (by rfl) ⟨56940, by rfl⟩ : syracuseStep 2429461 = 113881) (by norm_num)
theorem B2880029 : Blo 1705053 2880029 := bbase (se 3 (by rfl) ⟨540005, by rfl⟩ : syracuseStep 2880029 = 1080011) (by norm_num)
theorem B2560541 : Blo 1705053 2560541 := bbase (se 3 (by rfl) ⟨480101, by rfl⟩ : syracuseStep 2560541 = 960203) (by norm_num)
theorem B3838517 : Blo 1705053 3838517 := bbase (se 5 (by rfl) ⟨179930, by rfl⟩ : syracuseStep 3838517 = 359861) (by norm_num)
theorem B2560565 : Blo 1705053 2560565 := bbase (se 5 (by rfl) ⟨120026, by rfl⟩ : syracuseStep 2560565 = 240053) (by norm_num)
theorem B3240557 : Blo 1705053 3240557 := bbase (se 3 (by rfl) ⟨607604, by rfl⟩ : syracuseStep 3240557 = 1215209) (by norm_num)
theorem B3838589 : Blo 1705053 3838589 := bbase (se 3 (by rfl) ⟨719735, by rfl⟩ : syracuseStep 3838589 = 1439471) (by norm_num)
theorem B2159237 : Blo 1705053 2159237 := bbase (se 4 (by rfl) ⟨202428, by rfl⟩ : syracuseStep 2159237 = 404857) (by norm_num)
theorem B3642005 : Blo 1705053 3642005 := bbase (se 6 (by rfl) ⟨85359, by rfl⟩ : syracuseStep 3642005 = 170719) (by norm_num)
theorem B2880157 : Blo 1705053 2880157 := bbase (se 3 (by rfl) ⟨540029, by rfl⟩ : syracuseStep 2880157 = 1080059) (by norm_num)
theorem B2159293 : Blo 1705053 2159293 := bbase (se 3 (by rfl) ⟨404867, by rfl⟩ : syracuseStep 2159293 = 809735) (by norm_num)
theorem B5755589 : Blo 1705053 5755589 := bbase (se 4 (by rfl) ⟨539586, by rfl⟩ : syracuseStep 5755589 = 1079173) (by norm_num)
theorem B3838661 : Blo 1705053 3838661 := bbase (se 4 (by rfl) ⟨359874, by rfl⟩ : syracuseStep 3838661 = 719749) (by norm_num)
theorem B2732773 : Blo 1705053 2732773 := bbase (se 4 (by rfl) ⟨256197, by rfl⟩ : syracuseStep 2732773 = 512395) (by norm_num)
theorem B2880245 : Blo 1705053 2880245 := bbase (se 5 (by rfl) ⟨135011, by rfl⟩ : syracuseStep 2880245 = 270023) (by norm_num)
theorem B3838733 : Blo 1705053 3838733 := bbase (se 3 (by rfl) ⟨719762, by rfl⟩ : syracuseStep 3838733 = 1439525) (by norm_num)
theorem B2159389 : Blo 1705053 2159389 := bbase (se 3 (by rfl) ⟨404885, by rfl⟩ : syracuseStep 2159389 = 809771) (by norm_num)
theorem B10924885 : Blo 1705053 10924885 := bbase (se 9 (by rfl) ⟨32006, by rfl⟩ : syracuseStep 10924885 = 64013) (by norm_num)
theorem B3838805 : Blo 1705053 3838805 := bbase (se 9 (by rfl) ⟨11246, by rfl⟩ : syracuseStep 3838805 = 22493) (by norm_num)
theorem B2880373 : Blo 1705053 2880373 := bbase (se 5 (by rfl) ⟨135017, by rfl⟩ : syracuseStep 2880373 = 270035) (by norm_num)
theorem B4101005 : Blo 1705053 4101005 := bbase (se 3 (by rfl) ⟨768938, by rfl⟩ : syracuseStep 4101005 = 1537877) (by norm_num)
theorem B3838877 : Blo 1705053 3838877 := bbase (se 3 (by rfl) ⟨719789, by rfl⟩ : syracuseStep 3838877 = 1439579) (by norm_num)
theorem B2159561 : Blo 1705053 2159561 := bbase (se 2 (by rfl) ⟨809835, by rfl⟩ : syracuseStep 2159561 = 1619671) (by norm_num)
theorem B2880461 : Blo 1705053 2880461 := bbase (se 3 (by rfl) ⟨540086, by rfl⟩ : syracuseStep 2880461 = 1080173) (by norm_num)
theorem B2593757 : Blo 1705053 2593757 := bbase (se 3 (by rfl) ⟨486329, by rfl⟩ : syracuseStep 2593757 = 972659) (by norm_num)
theorem B3838949 : Blo 1705053 3838949 := bbase (se 4 (by rfl) ⟨359901, by rfl⟩ : syracuseStep 3838949 = 719803) (by norm_num)
theorem B2733029 : Blo 1705053 2733029 := bbase (se 4 (by rfl) ⟨256221, by rfl⟩ : syracuseStep 2733029 = 512443) (by norm_num)
theorem B4101101 : Blo 1705053 4101101 := bbase (se 3 (by rfl) ⟨768956, by rfl⟩ : syracuseStep 4101101 = 1537913) (by norm_num)
theorem B2159617 : Blo 1705053 2159617 := bbase (se 2 (by rfl) ⟨809856, by rfl⟩ : syracuseStep 2159617 = 1619713) (by norm_num)
theorem B3839021 : Blo 1705053 3839021 := bbase (se 3 (by rfl) ⟨719816, by rfl⟩ : syracuseStep 3839021 = 1439633) (by norm_num)
theorem B2880589 : Blo 1705053 2880589 := bbase (se 3 (by rfl) ⟨540110, by rfl⟩ : syracuseStep 2880589 = 1080221) (by norm_num)
theorem B2593885 : Blo 1705053 2593885 := bbase (se 3 (by rfl) ⟨486353, by rfl⟩ : syracuseStep 2593885 = 972707) (by norm_num)
theorem B2159713 : Blo 1705053 2159713 := bbase (se 2 (by rfl) ⟨809892, by rfl⟩ : syracuseStep 2159713 = 1619785) (by norm_num)
theorem B5756021 : Blo 1705053 5756021 := bbase (se 5 (by rfl) ⟨269813, by rfl⟩ : syracuseStep 5756021 = 539627) (by norm_num)
theorem B3839093 : Blo 1705053 3839093 := bbase (se 5 (by rfl) ⟨179957, by rfl⟩ : syracuseStep 3839093 = 359915) (by norm_num)
theorem B7885957 : Blo 1705053 7885957 := bbase (se 4 (by rfl) ⟨739308, by rfl⟩ : syracuseStep 7885957 = 1478617) (by norm_num)
theorem B8639621 : Blo 1705053 8639621 := bbase (se 4 (by rfl) ⟨809964, by rfl⟩ : syracuseStep 8639621 = 1619929) (by norm_num)
theorem B3642509 : Blo 1705053 3642509 := bbase (se 3 (by rfl) ⟨682970, by rfl⟩ : syracuseStep 3642509 = 1365941) (by norm_num)
theorem B3642517 : Blo 1705053 3642517 := bbase (se 6 (by rfl) ⟨85371, by rfl⟩ : syracuseStep 3642517 = 170743) (by norm_num)
theorem B3839165 : Blo 1705053 3839165 := bbase (se 3 (by rfl) ⟨719843, by rfl⟩ : syracuseStep 3839165 = 1439687) (by norm_num)
theorem B6477029 : Blo 1705053 6477029 := bbase (se 4 (by rfl) ⟨607221, by rfl⟩ : syracuseStep 6477029 = 1214443) (by norm_num)
theorem B3839237 : Blo 1705053 3839237 := bbase (se 4 (by rfl) ⟨359928, by rfl⟩ : syracuseStep 3839237 = 719857) (by norm_num)
theorem B2159885 : Blo 1705053 2159885 := bbase (se 3 (by rfl) ⟨404978, by rfl⟩ : syracuseStep 2159885 = 809957) (by norm_num)
theorem B2430253 : Blo 1705053 2430253 := bbase (se 3 (by rfl) ⟨455672, by rfl⟩ : syracuseStep 2430253 = 911345) (by norm_num)
theorem B2159941 : Blo 1705053 2159941 := bbase (se 4 (by rfl) ⟨202494, by rfl⟩ : syracuseStep 2159941 = 404989) (by norm_num)
theorem B4437325 : Blo 1705053 4437325 := bbase (se 3 (by rfl) ⟨831998, by rfl⟩ : syracuseStep 4437325 = 1663997) (by norm_num)
theorem B3839309 : Blo 1705053 3839309 := bbase (se 3 (by rfl) ⟨719870, by rfl⟩ : syracuseStep 3839309 = 1439741) (by norm_num)
theorem B3839381 : Blo 1705053 3839381 := bbase (se 6 (by rfl) ⟨89985, by rfl⟩ : syracuseStep 3839381 = 179971) (by norm_num)
theorem B2160037 : Blo 1705053 2160037 := bbase (se 4 (by rfl) ⟨202503, by rfl⟩ : syracuseStep 2160037 = 405007) (by norm_num)
theorem B3839453 : Blo 1705053 3839453 := bbase (se 3 (by rfl) ⟨719897, by rfl⟩ : syracuseStep 3839453 = 1439795) (by norm_num)
theorem B6477317 : Blo 1705053 6477317 := bbase (se 4 (by rfl) ⟨607248, by rfl⟩ : syracuseStep 6477317 = 1214497) (by norm_num)
theorem B8631845 : Blo 1705053 8631845 := bbase (se 4 (by rfl) ⟨809235, by rfl⟩ : syracuseStep 8631845 = 1618471) (by norm_num)
theorem B5756453 : Blo 1705053 5756453 := bbase (se 4 (by rfl) ⟨539667, by rfl⟩ : syracuseStep 5756453 = 1079335) (by norm_num)
theorem B3839525 : Blo 1705053 3839525 := bbase (se 4 (by rfl) ⟨359955, by rfl⟩ : syracuseStep 3839525 = 719911) (by norm_num)
theorem B9721397 : Blo 1705053 9721397 := bbase (se 5 (by rfl) ⟨455690, by rfl⟩ : syracuseStep 9721397 = 911381) (by norm_num)
theorem B2160209 : Blo 1705053 2160209 := bbase (se 2 (by rfl) ⟨810078, by rfl⟩ : syracuseStep 2160209 = 1620157) (by norm_num)
theorem B3839597 : Blo 1705053 3839597 := bbase (se 3 (by rfl) ⟨719924, by rfl⟩ : syracuseStep 3839597 = 1439849) (by norm_num)
theorem B2160265 : Blo 1705053 2160265 := bbase (se 2 (by rfl) ⟨810099, by rfl⟩ : syracuseStep 2160265 = 1620199) (by norm_num)
theorem B5060245 : Blo 1705053 5060245 := bbase (se 6 (by rfl) ⟨118599, by rfl⟩ : syracuseStep 5060245 = 237199) (by norm_num)
theorem B2733733 : Blo 1705053 2733733 := bbase (se 4 (by rfl) ⟨256287, by rfl⟩ : syracuseStep 2733733 = 512575) (by norm_num)
theorem B3839669 : Blo 1705053 3839669 := bbase (se 5 (by rfl) ⟨179984, by rfl⟩ : syracuseStep 3839669 = 359969) (by norm_num)
theorem B2160361 : Blo 1705053 2160361 := bbase (se 2 (by rfl) ⟨810135, by rfl⟩ : syracuseStep 2160361 = 1620271) (by norm_num)
theorem B3839741 : Blo 1705053 3839741 := bbase (se 3 (by rfl) ⟨719951, by rfl⟩ : syracuseStep 3839741 = 1439903) (by norm_num)
theorem B3839813 : Blo 1705053 3839813 := bbase (se 4 (by rfl) ⟨359982, by rfl⟩ : syracuseStep 3839813 = 719965) (by norm_num)
theorem B3839885 : Blo 1705053 3839885 := bbase (se 3 (by rfl) ⟨719978, by rfl⟩ : syracuseStep 3839885 = 1439957) (by norm_num)
theorem B4855733 : Blo 1705053 4855733 := bbase (se 5 (by rfl) ⟨227612, by rfl⟩ : syracuseStep 4855733 = 455225) (by norm_num)
theorem B5756885 : Blo 1705053 5756885 := bbase (se 7 (by rfl) ⟨67463, by rfl⟩ : syracuseStep 5756885 = 134927) (by norm_num)
theorem B3839957 : Blo 1705053 3839957 := bbase (se 7 (by rfl) ⟨44999, by rfl⟩ : syracuseStep 3839957 = 89999) (by norm_num)
theorem B1972237 : Blo 1705053 1972237 := bbase (se 3 (by rfl) ⟨369794, by rfl⟩ : syracuseStep 1972237 = 739589) (by norm_num)
theorem B3840029 : Blo 1705053 3840029 := bbase (se 3 (by rfl) ⟨720005, by rfl⟩ : syracuseStep 3840029 = 1440011) (by norm_num)
theorem B2734157 : Blo 1705053 2734157 := bbase (se 3 (by rfl) ⟨512654, by rfl⟩ : syracuseStep 2734157 = 1025309) (by norm_num)
theorem B3840101 : Blo 1705053 3840101 := bbase (se 4 (by rfl) ⟨360009, by rfl⟩ : syracuseStep 3840101 = 720019) (by norm_num)
theorem B17315989 : Blo 1705053 17315989 := bbase (se 6 (by rfl) ⟨405843, by rfl⟩ : syracuseStep 17315989 = 811687) (by norm_num)
theorem B3283109 : Blo 1705053 3283109 := bbase (se 4 (by rfl) ⟨307791, by rfl⟩ : syracuseStep 3283109 = 615583) (by norm_num)
theorem B3840173 : Blo 1705053 3840173 := bbase (se 3 (by rfl) ⟨720032, by rfl⟩ : syracuseStep 3840173 = 1440065) (by norm_num)
theorem B62290133 : Blo 1705053 62290133 := bbase (se 7 (by rfl) ⟨729962, by rfl⟩ : syracuseStep 62290133 = 1459925) (by norm_num)
theorem B2595053 : Blo 1705053 2595053 := bbase (se 3 (by rfl) ⟨486572, by rfl⟩ : syracuseStep 2595053 = 973145) (by norm_num)
theorem B3840245 : Blo 1705053 3840245 := bbase (se 5 (by rfl) ⟨180011, by rfl⟩ : syracuseStep 3840245 = 360023) (by norm_num)
theorem B3643645 : Blo 1705053 3643645 := bbase (se 3 (by rfl) ⟨683183, by rfl⟩ : syracuseStep 3643645 = 1366367) (by norm_num)
theorem B3840317 : Blo 1705053 3840317 := bbase (se 3 (by rfl) ⟨720059, by rfl⟩ : syracuseStep 3840317 = 1440119) (by norm_num)
theorem B4921685 : Blo 1705053 4921685 := bbase (se 10 (by rfl) ⟨7209, by rfl⟩ : syracuseStep 4921685 = 14419) (by norm_num)
theorem B5757317 : Blo 1705053 5757317 := bbase (se 4 (by rfl) ⟨539748, by rfl⟩ : syracuseStep 5757317 = 1079497) (by norm_num)
theorem B3840389 : Blo 1705053 3840389 := bbase (se 4 (by rfl) ⟨360036, by rfl⟩ : syracuseStep 3840389 = 720073) (by norm_num)
theorem B8640917 : Blo 1705053 8640917 := bbase (se 6 (by rfl) ⟨202521, by rfl⟩ : syracuseStep 8640917 = 405043) (by norm_num)
theorem B3840461 : Blo 1705053 3840461 := bbase (se 3 (by rfl) ⟨720086, by rfl⟩ : syracuseStep 3840461 = 1440173) (by norm_num)
theorem B3840533 : Blo 1705053 3840533 := bbase (se 6 (by rfl) ⟨90012, by rfl⟩ : syracuseStep 3840533 = 180025) (by norm_num)
theorem B2595349 : Blo 1705053 2595349 := bbase (se 6 (by rfl) ⟨60828, by rfl⟩ : syracuseStep 2595349 = 121657) (by norm_num)
theorem B3840605 : Blo 1705053 3840605 := bbase (se 3 (by rfl) ⟨720113, by rfl⟩ : syracuseStep 3840605 = 1440227) (by norm_num)
theorem B3644021 : Blo 1705053 3644021 := bbase (se 5 (by rfl) ⟨170813, by rfl⟩ : syracuseStep 3644021 = 341627) (by norm_num)
theorem B7289477 : Blo 1705053 7289477 := bbase (se 4 (by rfl) ⟨683388, by rfl⟩ : syracuseStep 7289477 = 1366777) (by norm_num)
theorem B6478501 : Blo 1705053 6478501 := bbase (se 4 (by rfl) ⟨607359, by rfl⟩ : syracuseStep 6478501 = 1214719) (by norm_num)
theorem B3840677 : Blo 1705053 3840677 := bbase (se 4 (by rfl) ⟨360063, by rfl⟩ : syracuseStep 3840677 = 720127) (by norm_num)
theorem B3840749 : Blo 1705053 3840749 := bbase (se 3 (by rfl) ⟨720140, by rfl⟩ : syracuseStep 3840749 = 1440281) (by norm_num)
theorem B8633141 : Blo 1705053 8633141 := bbase (se 5 (by rfl) ⟨404678, by rfl⟩ : syracuseStep 8633141 = 809357) (by norm_num)
theorem B5757749 : Blo 1705053 5757749 := bbase (se 5 (by rfl) ⟨269894, by rfl⟩ : syracuseStep 5757749 = 539789) (by norm_num)
theorem B3840821 : Blo 1705053 3840821 := bbase (se 5 (by rfl) ⟨180038, by rfl⟩ : syracuseStep 3840821 = 360077) (by norm_num)
theorem B13130581 : Blo 1705053 13130581 := bbase (se 9 (by rfl) ⟨38468, by rfl⟩ : syracuseStep 13130581 = 76937) (by norm_num)
theorem B3283877 : Blo 1705053 3283877 := bbase (se 4 (by rfl) ⟨307863, by rfl⟩ : syracuseStep 3283877 = 615727) (by norm_num)
theorem B6478805 : Blo 1705053 6478805 := bbase (se 7 (by rfl) ⟨75923, by rfl⟩ : syracuseStep 6478805 = 151847) (by norm_num)
theorem B4316125 : Blo 1705053 4316125 := bbase (se 3 (by rfl) ⟨809273, by rfl⟩ : syracuseStep 4316125 = 1618547) (by norm_num)
theorem B3890197 : Blo 1705053 3890197 := bbase (se 6 (by rfl) ⟨91176, by rfl⟩ : syracuseStep 3890197 = 182353) (by norm_num)
theorem B4316237 : Blo 1705053 4316237 := bbase (se 3 (by rfl) ⟨809294, by rfl⟩ : syracuseStep 4316237 = 1618589) (by norm_num)
theorem B4856917 : Blo 1705053 4856917 := bbase (se 8 (by rfl) ⟨28458, by rfl⟩ : syracuseStep 4856917 = 56917) (by norm_num)
theorem B3505237 : Blo 1705053 3505237 := bbase (se 8 (by rfl) ⟨20538, by rfl⟩ : syracuseStep 3505237 = 41077) (by norm_num)
theorem B10935445 : Blo 1705053 10935445 := bbase (se 6 (by rfl) ⟨256299, by rfl⟩ : syracuseStep 10935445 = 512599) (by norm_num)
theorem B5758181 : Blo 1705053 5758181 := bbase (se 4 (by rfl) ⟨539829, by rfl⟩ : syracuseStep 5758181 = 1079659) (by norm_num)
theorem B4857077 : Blo 1705053 4857077 := bbase (se 5 (by rfl) ⟨227675, by rfl⟩ : syracuseStep 4857077 = 455351) (by norm_num)
theorem B4316429 : Blo 1705053 4316429 := bbase (se 3 (by rfl) ⟨809330, by rfl⟩ : syracuseStep 4316429 = 1618661) (by norm_num)
theorem B6151477 : Blo 1705053 6151477 := bbase (se 5 (by rfl) ⟨288350, by rfl⟩ : syracuseStep 6151477 = 576701) (by norm_num)
theorem B6151621 : Blo 1705053 6151621 := bbase (se 4 (by rfl) ⟨576714, by rfl⟩ : syracuseStep 6151621 = 1153429) (by norm_num)
theorem B12959189 : Blo 1705053 12959189 := bbase (se 7 (by rfl) ⟨151865, by rfl⟩ : syracuseStep 12959189 = 303731) (by norm_num)
theorem B4857317 : Blo 1705053 4857317 := bbase (se 4 (by rfl) ⟨455373, by rfl⟩ : syracuseStep 4857317 = 910747) (by norm_num)
theorem B8199701 : Blo 1705053 8199701 := bbase (se 6 (by rfl) ⟨192180, by rfl⟩ : syracuseStep 8199701 = 384361) (by norm_num)
theorem B4439573 : Blo 1705053 4439573 := bbase (se 6 (by rfl) ⟨104052, by rfl⟩ : syracuseStep 4439573 = 208105) (by norm_num)
theorem B4316773 : Blo 1705053 4316773 := bbase (se 4 (by rfl) ⟨404697, by rfl⟩ : syracuseStep 4316773 = 809395) (by norm_num)
theorem B1752697 : Blo 1705053 1752697 := bbase (se 2 (by rfl) ⟨657261, by rfl⟩ : syracuseStep 1752697 = 1314523) (by norm_num)
theorem B5758613 : Blo 1705053 5758613 := bbase (se 6 (by rfl) ⟨134967, by rfl⟩ : syracuseStep 5758613 = 269935) (by norm_num)
theorem B8756885 : Blo 1705053 8756885 := bbase (se 6 (by rfl) ⟨205239, by rfl⟩ : syracuseStep 8756885 = 410479) (by norm_num)
theorem B4857509 : Blo 1705053 4857509 := bbase (se 4 (by rfl) ⟨455391, by rfl⟩ : syracuseStep 4857509 = 910783) (by norm_num)
theorem B4316885 : Blo 1705053 4316885 := bbase (se 7 (by rfl) ⟨50588, by rfl⟩ : syracuseStep 4316885 = 101177) (by norm_num)
theorem B6913829 : Blo 1705053 6913829 := bbase (se 4 (by rfl) ⟨648171, by rfl⟩ : syracuseStep 6913829 = 1296343) (by norm_num)
theorem B3890981 : Blo 1705053 3890981 := bbase (se 4 (by rfl) ⟨364779, by rfl⟩ : syracuseStep 3890981 = 729559) (by norm_num)
theorem B12951413 : Blo 1705053 12951413 := bbase (se 5 (by rfl) ⟨607097, by rfl⟩ : syracuseStep 12951413 = 1214195) (by norm_num)
theorem B16400245 : Blo 1705053 16400245 := bbase (se 5 (by rfl) ⟨768761, by rfl⟩ : syracuseStep 16400245 = 1537523) (by norm_num)
theorem B4317077 : Blo 1705053 4317077 := bbase (se 6 (by rfl) ⟨101181, by rfl⟩ : syracuseStep 4317077 = 202363) (by norm_num)
theorem B31113173 : Blo 1705053 31113173 := bbase (se 7 (by rfl) ⟨364607, by rfl⟩ : syracuseStep 31113173 = 729215) (by norm_num)
theorem B2629649 : Blo 1705053 2629649 := bstep (se 2 (by rfl) ⟨986118, by rfl⟩ : syracuseStep 2629649 = 1972237) B1972237
theorem B9715747 : Blo 1705053 9715747 := bstep (se 1 (by rfl) ⟨7286810, by rfl⟩ : syracuseStep 9715747 = 14573621) B14573621
theorem B4857965 : Blo 1705053 4857965 := bstep (se 3 (by rfl) ⟨910868, by rfl⟩ : syracuseStep 4857965 = 1821737) B1821737
theorem B32784497 : Blo 1705053 32784497 := bstep (se 2 (by rfl) ⟨12294186, by rfl⟩ : syracuseStep 32784497 = 24588373) B24588373
theorem B2769059 : Blo 1705053 2769059 := bstep (se 1 (by rfl) ⟨2076794, by rfl⟩ : syracuseStep 2769059 = 4153589) B4153589
theorem B5759153 : Blo 1705053 5759153 := bstep (se 2 (by rfl) ⟨2159682, by rfl⟩ : syracuseStep 5759153 = 4319365) B4319365
theorem B18440419 : Blo 1705053 18440419 := bstep (se 1 (by rfl) ⟨13830314, by rfl⟩ : syracuseStep 18440419 = 27660629) B27660629
theorem B4858147 : Blo 1705053 4858147 := bstep (se 1 (by rfl) ⟨3643610, by rfl⟩ : syracuseStep 4858147 = 7287221) B7287221
theorem B4858193 : Blo 1705053 4858193 := bstep (se 2 (by rfl) ⟨1821822, by rfl⟩ : syracuseStep 4858193 = 3643645) B3643645
theorem B18694597 : Blo 1705053 18694597 := bstep (se 4 (by rfl) ⟨1752618, by rfl⟩ : syracuseStep 18694597 = 3505237) B3505237
theorem B6914573 : Blo 1705053 6914573 := bstep (se 3 (by rfl) ⟨1296482, by rfl⟩ : syracuseStep 6914573 = 2592965) B2592965
theorem B4317745 : Blo 1705053 4317745 := bstep (se 2 (by rfl) ⟨1619154, by rfl⟩ : syracuseStep 4317745 = 3238309) B3238309
theorem B9716273 : Blo 1705053 9716273 := bstep (se 2 (by rfl) ⟨3643602, by rfl⟩ : syracuseStep 9716273 = 7287205) B7287205
theorem B9347717 : Blo 1705053 9347717 := bstep (se 4 (by rfl) ⟨876348, by rfl⟩ : syracuseStep 9347717 = 1752697) B1752697
theorem B1729171 : Blo 1705053 1729171 := bstep (se 1 (by rfl) ⟨1296878, by rfl⟩ : syracuseStep 1729171 = 2593757) B2593757
theorem B8635085 : Blo 1705053 8635085 := bstep (se 3 (by rfl) ⟨1619078, by rfl⟩ : syracuseStep 8635085 = 3238157) B3238157
theorem B5759693 : Blo 1705053 5759693 := bstep (se 3 (by rfl) ⟨1079942, by rfl⟩ : syracuseStep 5759693 = 2159885) B2159885
theorem B5759747 : Blo 1705053 5759747 := bstep (se 1 (by rfl) ⟨4319810, by rfl⟩ : syracuseStep 5759747 = 8639621) B8639621
theorem B4318019 : Blo 1705053 4318019 := bstep (se 1 (by rfl) ⟨3238514, by rfl⟩ : syracuseStep 4318019 = 6477029) B6477029
theorem B5538737 : Blo 1705053 5538737 := bstep (se 2 (by rfl) ⟨2077026, by rfl⟩ : syracuseStep 5538737 = 4154053) B4154053
theorem B6562765 : Blo 1705053 6562765 := bstep (se 3 (by rfl) ⟨1230518, by rfl⟩ : syracuseStep 6562765 = 2461037) B2461037
theorem B4318211 : Blo 1705053 4318211 := bstep (se 1 (by rfl) ⟨3238658, by rfl⟩ : syracuseStep 4318211 = 6477317) B6477317
theorem B5760017 : Blo 1705053 5760017 := bstep (se 2 (by rfl) ⟨2160006, by rfl⟩ : syracuseStep 5760017 = 4320013) B4320013
theorem B6480931 : Blo 1705053 6480931 := bstep (se 1 (by rfl) ⟨4860698, by rfl⟩ : syracuseStep 6480931 = 9721397) B9721397
theorem B10937393 : Blo 1705053 10937393 := bstep (se 2 (by rfl) ⟨4101522, by rfl⟩ : syracuseStep 10937393 = 8203045) B8203045
theorem B7283789 : Blo 1705053 7283789 := bstep (se 3 (by rfl) ⟨1365710, by rfl⟩ : syracuseStep 7283789 = 2731421) B2731421
theorem B5538893 : Blo 1705053 5538893 := bstep (se 3 (by rfl) ⟨1038542, by rfl⟩ : syracuseStep 5538893 = 2077085) B2077085
theorem B1705059 : Blo 1705053 1705059 := bstep (se 1 (by rfl) ⟨1278794, by rfl⟩ : syracuseStep 1705059 = 2557589) B2557589
theorem B14566513 : Blo 1705053 14566513 := bstep (se 2 (by rfl) ⟨5462442, by rfl⟩ : syracuseStep 14566513 = 10924885) B10924885
theorem B17507441 : Blo 1705053 17507441 := bstep (se 2 (by rfl) ⟨6565290, by rfl⟩ : syracuseStep 17507441 = 13130581) B13130581
theorem B1705075 : Blo 1705053 1705075 := bstep (se 1 (by rfl) ⟨1278806, by rfl⟩ : syracuseStep 1705075 = 2557613) B2557613
theorem B1705091 : Blo 1705053 1705091 := bstep (se 1 (by rfl) ⟨1278818, by rfl⟩ : syracuseStep 1705091 = 2557637) B2557637
theorem B1705107 : Blo 1705053 1705107 := bstep (se 1 (by rfl) ⟨1278830, by rfl⟩ : syracuseStep 1705107 = 2557661) B2557661
theorem B1705123 : Blo 1705053 1705123 := bstep (se 1 (by rfl) ⟨1278842, by rfl⟩ : syracuseStep 1705123 = 2557685) B2557685
theorem B1705139 : Blo 1705053 1705139 := bstep (se 1 (by rfl) ⟨1278854, by rfl⟩ : syracuseStep 1705139 = 2557709) B2557709
theorem B1705155 : Blo 1705053 1705155 := bstep (se 1 (by rfl) ⟨1278866, by rfl⟩ : syracuseStep 1705155 = 2557733) B2557733
theorem B1705171 : Blo 1705053 1705171 := bstep (se 1 (by rfl) ⟨1278878, by rfl⟩ : syracuseStep 1705171 = 2557757) B2557757
theorem B1705187 : Blo 1705053 1705187 := bstep (se 1 (by rfl) ⟨1278890, by rfl⟩ : syracuseStep 1705187 = 2557781) B2557781
theorem B1705203 : Blo 1705053 1705203 := bstep (se 1 (by rfl) ⟨1278902, by rfl⟩ : syracuseStep 1705203 = 2557805) B2557805
theorem B1705219 : Blo 1705053 1705219 := bstep (se 1 (by rfl) ⟨1278914, by rfl⟩ : syracuseStep 1705219 = 2557829) B2557829
theorem B1705235 : Blo 1705053 1705235 := bstep (se 1 (by rfl) ⟨1278926, by rfl⟩ : syracuseStep 1705235 = 2557853) B2557853
theorem B3237155 : Blo 1705053 3237155 := bstep (se 1 (by rfl) ⟨2427866, by rfl⟩ : syracuseStep 3237155 = 4855733) B4855733
theorem B1705251 : Blo 1705053 1705251 := bstep (se 1 (by rfl) ⟨1278938, by rfl⟩ : syracuseStep 1705251 = 2557877) B2557877
theorem B1705267 : Blo 1705053 1705267 := bstep (se 1 (by rfl) ⟨1278950, by rfl⟩ : syracuseStep 1705267 = 2557901) B2557901
theorem B1705283 : Blo 1705053 1705283 := bstep (se 1 (by rfl) ⟨1278962, by rfl⟩ : syracuseStep 1705283 = 2557925) B2557925
theorem B1918291 : Blo 1705053 1918291 := bstep (se 1 (by rfl) ⟨1438718, by rfl⟩ : syracuseStep 1918291 = 2877437) B2877437
theorem B1705299 : Blo 1705053 1705299 := bstep (se 1 (by rfl) ⟨1278974, by rfl⟩ : syracuseStep 1705299 = 2557949) B2557949
theorem B8750435 : Blo 1705053 8750435 := bstep (se 1 (by rfl) ⟨6562826, by rfl⟩ : syracuseStep 8750435 = 13125653) B13125653
theorem B1705315 : Blo 1705053 1705315 := bstep (se 1 (by rfl) ⟨1278986, by rfl⟩ : syracuseStep 1705315 = 2557973) B2557973
theorem B5186929 : Blo 1705053 5186929 := bstep (se 2 (by rfl) ⟨1945098, by rfl⟩ : syracuseStep 5186929 = 3890197) B3890197
theorem B1705331 : Blo 1705053 1705331 := bstep (se 1 (by rfl) ⟨1278998, by rfl⟩ : syracuseStep 1705331 = 2557997) B2557997
theorem B1705347 : Blo 1705053 1705347 := bstep (se 1 (by rfl) ⟨1279010, by rfl⟩ : syracuseStep 1705347 = 2558021) B2558021
theorem B1705363 : Blo 1705053 1705363 := bstep (se 1 (by rfl) ⟨1279022, by rfl⟩ : syracuseStep 1705363 = 2558045) B2558045
theorem B1705379 : Blo 1705053 1705379 := bstep (se 1 (by rfl) ⟨1279034, by rfl⟩ : syracuseStep 1705379 = 2558069) B2558069
theorem B1705395 : Blo 1705053 1705395 := bstep (se 1 (by rfl) ⟨1279046, by rfl⟩ : syracuseStep 1705395 = 2558093) B2558093
theorem B1705411 : Blo 1705053 1705411 := bstep (se 1 (by rfl) ⟨1279058, by rfl⟩ : syracuseStep 1705411 = 2558117) B2558117
theorem B2188739 : Blo 1705053 2188739 := bstep (se 1 (by rfl) ⟨1641554, by rfl⟩ : syracuseStep 2188739 = 3283109) B3283109
theorem B3458513 : Blo 1705053 3458513 := bstep (se 2 (by rfl) ⟨1296942, by rfl⟩ : syracuseStep 3458513 = 2593885) B2593885
theorem B1705427 : Blo 1705053 1705427 := bstep (se 1 (by rfl) ⟨1279070, by rfl⟩ : syracuseStep 1705427 = 2558141) B2558141
theorem B1918435 : Blo 1705053 1918435 := bstep (se 1 (by rfl) ⟨1438826, by rfl⟩ : syracuseStep 1918435 = 2877653) B2877653
theorem B1705443 : Blo 1705053 1705443 := bstep (se 1 (by rfl) ⟨1279082, by rfl⟩ : syracuseStep 1705443 = 2558165) B2558165
theorem B41526755 : Blo 1705053 41526755 := bstep (se 1 (by rfl) ⟨31145066, by rfl⟩ : syracuseStep 41526755 = 62290133) B62290133
theorem B1705459 : Blo 1705053 1705459 := bstep (se 1 (by rfl) ⟨1279094, by rfl⟩ : syracuseStep 1705459 = 2558189) B2558189
theorem B1730035 : Blo 1705053 1730035 := bstep (se 1 (by rfl) ⟨1297526, by rfl⟩ : syracuseStep 1730035 = 2595053) B2595053
theorem B1705475 : Blo 1705053 1705475 := bstep (se 1 (by rfl) ⟨1279106, by rfl⟩ : syracuseStep 1705475 = 2558213) B2558213
theorem B1705491 : Blo 1705053 1705491 := bstep (se 1 (by rfl) ⟨1279118, by rfl⟩ : syracuseStep 1705491 = 2558237) B2558237
theorem B1705507 : Blo 1705053 1705507 := bstep (se 1 (by rfl) ⟨1279130, by rfl⟩ : syracuseStep 1705507 = 2558261) B2558261
theorem B5760557 : Blo 1705053 5760557 := bstep (se 3 (by rfl) ⟨1080104, by rfl⟩ : syracuseStep 5760557 = 2160209) B2160209
theorem B1705523 : Blo 1705053 1705523 := bstep (se 1 (by rfl) ⟨1279142, by rfl⟩ : syracuseStep 1705523 = 2558285) B2558285
theorem B1705539 : Blo 1705053 1705539 := bstep (se 1 (by rfl) ⟨1279154, by rfl⟩ : syracuseStep 1705539 = 2558309) B2558309
theorem B1705555 : Blo 1705053 1705555 := bstep (se 1 (by rfl) ⟨1279166, by rfl⟩ : syracuseStep 1705555 = 2558333) B2558333
theorem B5834339 : Blo 1705053 5834339 := bstep (se 1 (by rfl) ⟨4375754, by rfl⟩ : syracuseStep 5834339 = 8751509) B8751509
theorem B1705571 : Blo 1705053 1705571 := bstep (se 1 (by rfl) ⟨1279178, by rfl⟩ : syracuseStep 1705571 = 2558357) B2558357
theorem B5760611 : Blo 1705053 5760611 := bstep (se 1 (by rfl) ⟨4320458, by rfl⟩ : syracuseStep 5760611 = 8640917) B8640917
theorem B1918579 : Blo 1705053 1918579 := bstep (se 1 (by rfl) ⟨1438934, by rfl⟩ : syracuseStep 1918579 = 2877869) B2877869
theorem B1705587 : Blo 1705053 1705587 := bstep (se 1 (by rfl) ⟨1279190, by rfl⟩ : syracuseStep 1705587 = 2558381) B2558381
theorem B1705603 : Blo 1705053 1705603 := bstep (se 1 (by rfl) ⟨1279202, by rfl⟩ : syracuseStep 1705603 = 2558405) B2558405
theorem B1705619 : Blo 1705053 1705619 := bstep (se 1 (by rfl) ⟨1279214, by rfl⟩ : syracuseStep 1705619 = 2558429) B2558429
theorem B2557601 : Blo 1705053 2557601 := bstep (se 2 (by rfl) ⟨959100, by rfl⟩ : syracuseStep 2557601 = 1918201) B1918201
theorem B4097699 : Blo 1705053 4097699 := bstep (se 1 (by rfl) ⟨3073274, by rfl⟩ : syracuseStep 4097699 = 6146549) B6146549
theorem B1705635 : Blo 1705053 1705635 := bstep (se 1 (by rfl) ⟨1279226, by rfl⟩ : syracuseStep 1705635 = 2558453) B2558453
theorem B2557619 : Blo 1705053 2557619 := bstep (se 1 (by rfl) ⟨1918214, by rfl⟩ : syracuseStep 2557619 = 3836429) B3836429
theorem B1705651 : Blo 1705053 1705651 := bstep (se 1 (by rfl) ⟨1279238, by rfl⟩ : syracuseStep 1705651 = 2558477) B2558477
theorem B1705667 : Blo 1705053 1705667 := bstep (se 1 (by rfl) ⟨1279250, by rfl⟩ : syracuseStep 1705667 = 2558501) B2558501
theorem B2557649 : Blo 1705053 2557649 := bstep (se 2 (by rfl) ⟨959118, by rfl⟩ : syracuseStep 2557649 = 1918237) B1918237
theorem B1705683 : Blo 1705053 1705683 := bstep (se 1 (by rfl) ⟨1279262, by rfl⟩ : syracuseStep 1705683 = 2558525) B2558525
theorem B2557667 : Blo 1705053 2557667 := bstep (se 1 (by rfl) ⟨1918250, by rfl⟩ : syracuseStep 2557667 = 3836501) B3836501
theorem B1705699 : Blo 1705053 1705699 := bstep (se 1 (by rfl) ⟨1279274, by rfl⟩ : syracuseStep 1705699 = 2558549) B2558549
theorem B8201969 : Blo 1705053 8201969 := bstep (se 2 (by rfl) ⟨3075738, by rfl⟩ : syracuseStep 8201969 = 6151477) B6151477
theorem B1705715 : Blo 1705053 1705715 := bstep (se 1 (by rfl) ⟨1279286, by rfl⟩ : syracuseStep 1705715 = 2558573) B2558573
theorem B2557697 : Blo 1705053 2557697 := bstep (se 2 (by rfl) ⟨959136, by rfl⟩ : syracuseStep 2557697 = 1918273) B1918273
theorem B1918723 : Blo 1705053 1918723 := bstep (se 1 (by rfl) ⟨1439042, by rfl⟩ : syracuseStep 1918723 = 2878085) B2878085
theorem B1705731 : Blo 1705053 1705731 := bstep (se 1 (by rfl) ⟨1279298, by rfl⟩ : syracuseStep 1705731 = 2558597) B2558597
theorem B4859651 : Blo 1705053 4859651 := bstep (se 1 (by rfl) ⟨3644738, by rfl⟩ : syracuseStep 4859651 = 7289477) B7289477
theorem B12953357 : Blo 1705053 12953357 := bstep (se 3 (by rfl) ⟨2428754, by rfl⟩ : syracuseStep 12953357 = 4857509) B4857509
theorem B5916433 : Blo 1705053 5916433 := bstep (se 2 (by rfl) ⟨2218662, by rfl⟩ : syracuseStep 5916433 = 4437325) B4437325
theorem B2557715 : Blo 1705053 2557715 := bstep (se 1 (by rfl) ⟨1918286, by rfl⟩ : syracuseStep 2557715 = 3836573) B3836573
theorem B1705747 : Blo 1705053 1705747 := bstep (se 1 (by rfl) ⟨1279310, by rfl⟩ : syracuseStep 1705747 = 2558621) B2558621
theorem B1705763 : Blo 1705053 1705763 := bstep (se 1 (by rfl) ⟨1279322, by rfl⟩ : syracuseStep 1705763 = 2558645) B2558645
theorem B2557745 : Blo 1705053 2557745 := bstep (se 2 (by rfl) ⟨959154, by rfl⟩ : syracuseStep 2557745 = 1918309) B1918309
theorem B1705779 : Blo 1705053 1705779 := bstep (se 1 (by rfl) ⟨1279334, by rfl⟩ : syracuseStep 1705779 = 2558669) B2558669
theorem B2557763 : Blo 1705053 2557763 := bstep (se 1 (by rfl) ⟨1918322, by rfl⟩ : syracuseStep 2557763 = 3836645) B3836645
theorem B1705795 : Blo 1705053 1705795 := bstep (se 1 (by rfl) ⟨1279346, by rfl⟩ : syracuseStep 1705795 = 2558693) B2558693
theorem B11233093 : Blo 1705053 11233093 := bstep (se 4 (by rfl) ⟨1053102, by rfl⟩ : syracuseStep 11233093 = 2106205) B2106205
theorem B1705811 : Blo 1705053 1705811 := bstep (se 1 (by rfl) ⟨1279358, by rfl⟩ : syracuseStep 1705811 = 2558717) B2558717
theorem B2557793 : Blo 1705053 2557793 := bstep (se 2 (by rfl) ⟨959172, by rfl⟩ : syracuseStep 2557793 = 1918345) B1918345
theorem B1705827 : Blo 1705053 1705827 := bstep (se 1 (by rfl) ⟨1279370, by rfl⟩ : syracuseStep 1705827 = 2558741) B2558741
theorem B5760881 : Blo 1705053 5760881 := bstep (se 2 (by rfl) ⟨2160330, by rfl⟩ : syracuseStep 5760881 = 4320661) B4320661
theorem B2557811 : Blo 1705053 2557811 := bstep (se 1 (by rfl) ⟨1918358, by rfl⟩ : syracuseStep 2557811 = 3836717) B3836717
theorem B1705843 : Blo 1705053 1705843 := bstep (se 1 (by rfl) ⟨1279382, by rfl⟩ : syracuseStep 1705843 = 2558765) B2558765
theorem B1705859 : Blo 1705053 1705859 := bstep (se 1 (by rfl) ⟨1279394, by rfl⟩ : syracuseStep 1705859 = 2558789) B2558789
theorem B2877329 : Blo 1705053 2877329 := bstep (se 2 (by rfl) ⟨1078998, by rfl⟩ : syracuseStep 2877329 = 2157997) B2157997
theorem B2557841 : Blo 1705053 2557841 := bstep (se 2 (by rfl) ⟨959190, by rfl⟩ : syracuseStep 2557841 = 1918381) B1918381
theorem B1918867 : Blo 1705053 1918867 := bstep (se 1 (by rfl) ⟨1439150, by rfl⟩ : syracuseStep 1918867 = 2878301) B2878301
theorem B1705875 : Blo 1705053 1705875 := bstep (se 1 (by rfl) ⟨1279406, by rfl⟩ : syracuseStep 1705875 = 2558813) B2558813
theorem B1705891 : Blo 1705053 1705891 := bstep (se 1 (by rfl) ⟨1279418, by rfl⟩ : syracuseStep 1705891 = 2558837) B2558837
theorem B2557859 : Blo 1705053 2557859 := bstep (se 1 (by rfl) ⟨1918394, by rfl⟩ : syracuseStep 2557859 = 3836789) B3836789
theorem B4319153 : Blo 1705053 4319153 := bstep (se 2 (by rfl) ⟨1619682, by rfl⟩ : syracuseStep 4319153 = 3239365) B3239365
theorem B1705907 : Blo 1705053 1705907 := bstep (se 1 (by rfl) ⟨1279430, by rfl⟩ : syracuseStep 1705907 = 2558861) B2558861
theorem B8202161 : Blo 1705053 8202161 := bstep (se 2 (by rfl) ⟨3075810, by rfl⟩ : syracuseStep 8202161 = 6151621) B6151621
theorem B2557889 : Blo 1705053 2557889 := bstep (se 2 (by rfl) ⟨959208, by rfl⟩ : syracuseStep 2557889 = 1918417) B1918417
theorem B1705923 : Blo 1705053 1705923 := bstep (se 1 (by rfl) ⟨1279442, by rfl⟩ : syracuseStep 1705923 = 2558885) B2558885
theorem B2189251 : Blo 1705053 2189251 := bstep (se 1 (by rfl) ⟨1641938, by rfl⟩ : syracuseStep 2189251 = 3283877) B3283877
theorem B2557907 : Blo 1705053 2557907 := bstep (se 1 (by rfl) ⟨1918430, by rfl⟩ : syracuseStep 2557907 = 3836861) B3836861
theorem B1705939 : Blo 1705053 1705939 := bstep (se 1 (by rfl) ⟨1279454, by rfl⟩ : syracuseStep 1705939 = 2558909) B2558909
theorem B1705955 : Blo 1705053 1705955 := bstep (se 1 (by rfl) ⟨1279466, by rfl⟩ : syracuseStep 1705955 = 2558933) B2558933
theorem B9717731 : Blo 1705053 9717731 := bstep (se 1 (by rfl) ⟨7288298, by rfl⟩ : syracuseStep 9717731 = 14576597) B14576597
theorem B4319203 : Blo 1705053 4319203 := bstep (se 1 (by rfl) ⟨3239402, by rfl⟩ : syracuseStep 4319203 = 6478805) B6478805
theorem B2557937 : Blo 1705053 2557937 := bstep (se 2 (by rfl) ⟨959226, by rfl⟩ : syracuseStep 2557937 = 1918453) B1918453
theorem B1705971 : Blo 1705053 1705971 := bstep (se 1 (by rfl) ⟨1279478, by rfl⟩ : syracuseStep 1705971 = 2558957) B2558957
theorem B2557955 : Blo 1705053 2557955 := bstep (se 1 (by rfl) ⟨1918466, by rfl⟩ : syracuseStep 2557955 = 3836933) B3836933
theorem B1705987 : Blo 1705053 1705987 := bstep (se 1 (by rfl) ⟨1279490, by rfl⟩ : syracuseStep 1705987 = 2558981) B2558981
theorem B2050051 : Blo 1705053 2050051 := bstep (se 1 (by rfl) ⟨1537538, by rfl⟩ : syracuseStep 2050051 = 3075077) B3075077
theorem B2877457 : Blo 1705053 2877457 := bstep (se 2 (by rfl) ⟨1079046, by rfl⟩ : syracuseStep 2877457 = 2158093) B2158093
theorem B1706003 : Blo 1705053 1706003 := bstep (se 1 (by rfl) ⟨1279502, by rfl⟩ : syracuseStep 1706003 = 2559005) B2559005
theorem B2557985 : Blo 1705053 2557985 := bstep (se 2 (by rfl) ⟨959244, by rfl⟩ : syracuseStep 2557985 = 1918489) B1918489
theorem B1919011 : Blo 1705053 1919011 := bstep (se 1 (by rfl) ⟨1439258, by rfl⟩ : syracuseStep 1919011 = 2878517) B2878517
theorem B1706019 : Blo 1705053 1706019 := bstep (se 1 (by rfl) ⟨1279514, by rfl⟩ : syracuseStep 1706019 = 2559029) B2559029
theorem B2877491 : Blo 1705053 2877491 := bstep (se 1 (by rfl) ⟨2158118, by rfl⟩ : syracuseStep 2877491 = 4316237) B4316237
theorem B2558003 : Blo 1705053 2558003 := bstep (se 1 (by rfl) ⟨1918502, by rfl⟩ : syracuseStep 2558003 = 3837005) B3837005
theorem B1706035 : Blo 1705053 1706035 := bstep (se 1 (by rfl) ⟨1279526, by rfl⟩ : syracuseStep 1706035 = 2559053) B2559053
theorem B1706051 : Blo 1705053 1706051 := bstep (se 1 (by rfl) ⟨1279538, by rfl⟩ : syracuseStep 1706051 = 2559077) B2559077
theorem B21850181 : Blo 1705053 21850181 := bstep (se 4 (by rfl) ⟨2048454, by rfl⟩ : syracuseStep 21850181 = 4096909) B4096909
theorem B2558033 : Blo 1705053 2558033 := bstep (se 2 (by rfl) ⟨959262, by rfl⟩ : syracuseStep 2558033 = 1918525) B1918525
theorem B1706067 : Blo 1705053 1706067 := bstep (se 1 (by rfl) ⟨1279550, by rfl⟩ : syracuseStep 1706067 = 2559101) B2559101
theorem B2558051 : Blo 1705053 2558051 := bstep (se 1 (by rfl) ⟨1918538, by rfl⟩ : syracuseStep 2558051 = 3837077) B3837077
theorem B1706083 : Blo 1705053 1706083 := bstep (se 1 (by rfl) ⟨1279562, by rfl⟩ : syracuseStep 1706083 = 2559125) B2559125
theorem B4319345 : Blo 1705053 4319345 := bstep (se 2 (by rfl) ⟨1619754, by rfl⟩ : syracuseStep 4319345 = 3239509) B3239509
theorem B1706099 : Blo 1705053 1706099 := bstep (se 1 (by rfl) ⟨1279574, by rfl⟩ : syracuseStep 1706099 = 2559149) B2559149
theorem B2558081 : Blo 1705053 2558081 := bstep (se 2 (by rfl) ⟨959280, by rfl⟩ : syracuseStep 2558081 = 1918561) B1918561
theorem B1706115 : Blo 1705053 1706115 := bstep (se 1 (by rfl) ⟨1279586, by rfl⟩ : syracuseStep 1706115 = 2559173) B2559173
theorem B2558099 : Blo 1705053 2558099 := bstep (se 1 (by rfl) ⟨1918574, by rfl⟩ : syracuseStep 2558099 = 3837149) B3837149
theorem B1706131 : Blo 1705053 1706131 := bstep (se 1 (by rfl) ⟨1279598, by rfl⟩ : syracuseStep 1706131 = 2559197) B2559197
theorem B3238051 : Blo 1705053 3238051 := bstep (se 1 (by rfl) ⟨2428538, by rfl⟩ : syracuseStep 3238051 = 4857077) B4857077
theorem B1706147 : Blo 1705053 1706147 := bstep (se 1 (by rfl) ⟨1279610, by rfl⟩ : syracuseStep 1706147 = 2559221) B2559221
theorem B2558129 : Blo 1705053 2558129 := bstep (se 2 (by rfl) ⟨959298, by rfl⟩ : syracuseStep 2558129 = 1918597) B1918597
theorem B2877619 : Blo 1705053 2877619 := bstep (se 1 (by rfl) ⟨2158214, by rfl⟩ : syracuseStep 2877619 = 4316429) B4316429
theorem B1919155 : Blo 1705053 1919155 := bstep (se 1 (by rfl) ⟨1439366, by rfl⟩ : syracuseStep 1919155 = 2878733) B2878733
theorem B1706163 : Blo 1705053 1706163 := bstep (se 1 (by rfl) ⟨1279622, by rfl⟩ : syracuseStep 1706163 = 2559245) B2559245
theorem B2558147 : Blo 1705053 2558147 := bstep (se 1 (by rfl) ⟨1918610, by rfl⟩ : syracuseStep 2558147 = 3837221) B3837221
theorem B1706179 : Blo 1705053 1706179 := bstep (se 1 (by rfl) ⟨1279634, by rfl⟩ : syracuseStep 1706179 = 2559269) B2559269
theorem B1706195 : Blo 1705053 1706195 := bstep (se 1 (by rfl) ⟨1279646, by rfl⟩ : syracuseStep 1706195 = 2559293) B2559293
theorem B2558177 : Blo 1705053 2558177 := bstep (se 2 (by rfl) ⟨959316, by rfl⟩ : syracuseStep 2558177 = 1918633) B1918633
theorem B1706211 : Blo 1705053 1706211 := bstep (se 1 (by rfl) ⟨1279658, by rfl⟩ : syracuseStep 1706211 = 2559317) B2559317
theorem B2558195 : Blo 1705053 2558195 := bstep (se 1 (by rfl) ⟨1918646, by rfl⟩ : syracuseStep 2558195 = 3837293) B3837293
theorem B1706227 : Blo 1705053 1706227 := bstep (se 1 (by rfl) ⟨1279670, by rfl⟩ : syracuseStep 1706227 = 2559341) B2559341
theorem B1706243 : Blo 1705053 1706243 := bstep (se 1 (by rfl) ⟨1279682, by rfl⟩ : syracuseStep 1706243 = 2559365) B2559365
theorem B2558225 : Blo 1705053 2558225 := bstep (se 2 (by rfl) ⟨959334, by rfl⟩ : syracuseStep 2558225 = 1918669) B1918669
theorem B1706259 : Blo 1705053 1706259 := bstep (se 1 (by rfl) ⟨1279694, by rfl⟩ : syracuseStep 1706259 = 2559389) B2559389
theorem B2558243 : Blo 1705053 2558243 := bstep (se 1 (by rfl) ⟨1918682, by rfl⟩ : syracuseStep 2558243 = 3837365) B3837365
theorem B1706275 : Blo 1705053 1706275 := bstep (se 1 (by rfl) ⟨1279706, by rfl⟩ : syracuseStep 1706275 = 2559413) B2559413
theorem B1706291 : Blo 1705053 1706291 := bstep (se 1 (by rfl) ⟨1279718, by rfl⟩ : syracuseStep 1706291 = 2559437) B2559437
theorem B2877761 : Blo 1705053 2877761 := bstep (se 2 (by rfl) ⟨1079160, by rfl⟩ : syracuseStep 2877761 = 2158321) B2158321
theorem B2558273 : Blo 1705053 2558273 := bstep (se 2 (by rfl) ⟨959352, by rfl⟩ : syracuseStep 2558273 = 1918705) B1918705
theorem B3238211 : Blo 1705053 3238211 := bstep (se 1 (by rfl) ⟨2428658, by rfl⟩ : syracuseStep 3238211 = 4857317) B4857317
theorem B1919299 : Blo 1705053 1919299 := bstep (se 1 (by rfl) ⟨1439474, by rfl⟩ : syracuseStep 1919299 = 2878949) B2878949
theorem B1706307 : Blo 1705053 1706307 := bstep (se 1 (by rfl) ⟨1279730, by rfl⟩ : syracuseStep 1706307 = 2559461) B2559461
theorem B2558291 : Blo 1705053 2558291 := bstep (se 1 (by rfl) ⟨1918718, by rfl⟩ : syracuseStep 2558291 = 3837437) B3837437
theorem B1706323 : Blo 1705053 1706323 := bstep (se 1 (by rfl) ⟨1279742, by rfl⟩ : syracuseStep 1706323 = 2559485) B2559485
theorem B1706339 : Blo 1705053 1706339 := bstep (se 1 (by rfl) ⟨1279754, by rfl⟩ : syracuseStep 1706339 = 2559509) B2559509
theorem B5466467 : Blo 1705053 5466467 := bstep (se 1 (by rfl) ⟨4099850, by rfl⟩ : syracuseStep 5466467 = 8199701) B8199701
theorem B2959715 : Blo 1705053 2959715 := bstep (se 1 (by rfl) ⟨2219786, by rfl⟩ : syracuseStep 2959715 = 4439573) B4439573
theorem B2558321 : Blo 1705053 2558321 := bstep (se 2 (by rfl) ⟨959370, by rfl⟩ : syracuseStep 2558321 = 1918741) B1918741
theorem B1706355 : Blo 1705053 1706355 := bstep (se 1 (by rfl) ⟨1279766, by rfl⟩ : syracuseStep 1706355 = 2559533) B2559533
theorem B2558339 : Blo 1705053 2558339 := bstep (se 1 (by rfl) ⟨1918754, by rfl⟩ : syracuseStep 2558339 = 3837509) B3837509
theorem B1706371 : Blo 1705053 1706371 := bstep (se 1 (by rfl) ⟨1279778, by rfl⟩ : syracuseStep 1706371 = 2559557) B2559557
theorem B1706387 : Blo 1705053 1706387 := bstep (se 1 (by rfl) ⟨1279790, by rfl⟩ : syracuseStep 1706387 = 2559581) B2559581
theorem B2558369 : Blo 1705053 2558369 := bstep (se 2 (by rfl) ⟨959388, by rfl⟩ : syracuseStep 2558369 = 1918777) B1918777
theorem B1706403 : Blo 1705053 1706403 := bstep (se 1 (by rfl) ⟨1279802, by rfl⟩ : syracuseStep 1706403 = 2559605) B2559605
theorem B2558387 : Blo 1705053 2558387 := bstep (se 1 (by rfl) ⟨1918790, by rfl⟩ : syracuseStep 2558387 = 3837581) B3837581
theorem B1706419 : Blo 1705053 1706419 := bstep (se 1 (by rfl) ⟨1279814, by rfl⟩ : syracuseStep 1706419 = 2559629) B2559629
theorem B2877889 : Blo 1705053 2877889 := bstep (se 2 (by rfl) ⟨1079208, by rfl⟩ : syracuseStep 2877889 = 2158417) B2158417
theorem B1706435 : Blo 1705053 1706435 := bstep (se 1 (by rfl) ⟨1279826, by rfl⟩ : syracuseStep 1706435 = 2559653) B2559653
theorem B2558417 : Blo 1705053 2558417 := bstep (se 2 (by rfl) ⟨959406, by rfl⟩ : syracuseStep 2558417 = 1918813) B1918813
theorem B1919443 : Blo 1705053 1919443 := bstep (se 1 (by rfl) ⟨1439582, by rfl⟩ : syracuseStep 1919443 = 2879165) B2879165
theorem B1706451 : Blo 1705053 1706451 := bstep (se 1 (by rfl) ⟨1279838, by rfl⟩ : syracuseStep 1706451 = 2559677) B2559677
theorem B2877923 : Blo 1705053 2877923 := bstep (se 1 (by rfl) ⟨2158442, by rfl⟩ : syracuseStep 2877923 = 4316885) B4316885
theorem B2558435 : Blo 1705053 2558435 := bstep (se 1 (by rfl) ⟨1918826, by rfl⟩ : syracuseStep 2558435 = 3837653) B3837653
theorem B1706467 : Blo 1705053 1706467 := bstep (se 1 (by rfl) ⟨1279850, by rfl⟩ : syracuseStep 1706467 = 2559701) B2559701
theorem B4098545 : Blo 1705053 4098545 := bstep (se 2 (by rfl) ⟨1536954, by rfl⟩ : syracuseStep 4098545 = 3073909) B3073909
theorem B21866993 : Blo 1705053 21866993 := bstep (se 2 (by rfl) ⟨8200122, by rfl⟩ : syracuseStep 21866993 = 16400245) B16400245
theorem B1706483 : Blo 1705053 1706483 := bstep (se 1 (by rfl) ⟨1279862, by rfl⟩ : syracuseStep 1706483 = 2559725) B2559725
theorem B2558465 : Blo 1705053 2558465 := bstep (se 2 (by rfl) ⟨959424, by rfl⟩ : syracuseStep 2558465 = 1918849) B1918849
theorem B1706499 : Blo 1705053 1706499 := bstep (se 1 (by rfl) ⟨1279874, by rfl⟩ : syracuseStep 1706499 = 2559749) B2559749
theorem B2558483 : Blo 1705053 2558483 := bstep (se 1 (by rfl) ⟨1918862, by rfl⟩ : syracuseStep 2558483 = 3837725) B3837725
theorem B1706515 : Blo 1705053 1706515 := bstep (se 1 (by rfl) ⟨1279886, by rfl⟩ : syracuseStep 1706515 = 2559773) B2559773
theorem B2918947 : Blo 1705053 2918947 := bstep (se 1 (by rfl) ⟨2189210, by rfl⟩ : syracuseStep 2918947 = 4378421) B4378421
theorem B1706531 : Blo 1705053 1706531 := bstep (se 1 (by rfl) ⟨1279898, by rfl⟩ : syracuseStep 1706531 = 2559797) B2559797
theorem B3836465 : Blo 1705053 3836465 := bstep (se 2 (by rfl) ⟨1438674, by rfl⟩ : syracuseStep 3836465 = 2877349) B2877349
theorem B2558513 : Blo 1705053 2558513 := bstep (se 2 (by rfl) ⟨959442, by rfl⟩ : syracuseStep 2558513 = 1918885) B1918885
theorem B1706547 : Blo 1705053 1706547 := bstep (se 1 (by rfl) ⟨1279910, by rfl⟩ : syracuseStep 1706547 = 2559821) B2559821
theorem B3836483 : Blo 1705053 3836483 := bstep (se 1 (by rfl) ⟨2877362, by rfl⟩ : syracuseStep 3836483 = 5754725) B5754725
theorem B2558531 : Blo 1705053 2558531 := bstep (se 1 (by rfl) ⟨1918898, by rfl⟩ : syracuseStep 2558531 = 3837797) B3837797
theorem B1706563 : Blo 1705053 1706563 := bstep (se 1 (by rfl) ⟨1279922, by rfl⟩ : syracuseStep 1706563 = 2559845) B2559845
theorem B1706579 : Blo 1705053 1706579 := bstep (se 1 (by rfl) ⟨1279934, by rfl⟩ : syracuseStep 1706579 = 2559869) B2559869
theorem B2558561 : Blo 1705053 2558561 := bstep (se 2 (by rfl) ⟨959460, by rfl⟩ : syracuseStep 2558561 = 1918921) B1918921
theorem B2878051 : Blo 1705053 2878051 := bstep (se 1 (by rfl) ⟨2158538, by rfl⟩ : syracuseStep 2878051 = 4317077) B4317077
theorem B1919587 : Blo 1705053 1919587 := bstep (se 1 (by rfl) ⟨1439690, by rfl⟩ : syracuseStep 1919587 = 2879381) B2879381
theorem B1706595 : Blo 1705053 1706595 := bstep (se 1 (by rfl) ⟨1279946, by rfl⟩ : syracuseStep 1706595 = 2559893) B2559893
theorem B2558579 : Blo 1705053 2558579 := bstep (se 1 (by rfl) ⟨1918934, by rfl⟩ : syracuseStep 2558579 = 3837869) B3837869
theorem B1706611 : Blo 1705053 1706611 := bstep (se 1 (by rfl) ⟨1279958, by rfl⟩ : syracuseStep 1706611 = 2559917) B2559917
theorem B1706627 : Blo 1705053 1706627 := bstep (se 1 (by rfl) ⟨1279970, by rfl⟩ : syracuseStep 1706627 = 2559941) B2559941
theorem B2558609 : Blo 1705053 2558609 := bstep (se 2 (by rfl) ⟨959478, by rfl⟩ : syracuseStep 2558609 = 1918957) B1918957
theorem B1706643 : Blo 1705053 1706643 := bstep (se 1 (by rfl) ⟨1279982, by rfl⟩ : syracuseStep 1706643 = 2559965) B2559965
theorem B2558627 : Blo 1705053 2558627 := bstep (se 1 (by rfl) ⟨1918970, by rfl⟩ : syracuseStep 2558627 = 3837941) B3837941
theorem B1706659 : Blo 1705053 1706659 := bstep (se 1 (by rfl) ⟨1279994, by rfl⟩ : syracuseStep 1706659 = 2559989) B2559989
theorem B1706675 : Blo 1705053 1706675 := bstep (se 1 (by rfl) ⟨1280006, by rfl⟩ : syracuseStep 1706675 = 2560013) B2560013
theorem B2558657 : Blo 1705053 2558657 := bstep (se 2 (by rfl) ⟨959496, by rfl⟩ : syracuseStep 2558657 = 1918993) B1918993
theorem B4098755 : Blo 1705053 4098755 := bstep (se 1 (by rfl) ⟨3074066, by rfl⟩ : syracuseStep 4098755 = 6148133) B6148133
theorem B1706691 : Blo 1705053 1706691 := bstep (se 1 (by rfl) ⟨1280018, by rfl⟩ : syracuseStep 1706691 = 2560037) B2560037
theorem B2558675 : Blo 1705053 2558675 := bstep (se 1 (by rfl) ⟨1919006, by rfl⟩ : syracuseStep 2558675 = 3838013) B3838013
theorem B1706707 : Blo 1705053 1706707 := bstep (se 1 (by rfl) ⟨1280030, by rfl⟩ : syracuseStep 1706707 = 2560061) B2560061
theorem B1706723 : Blo 1705053 1706723 := bstep (se 1 (by rfl) ⟨1280042, by rfl⟩ : syracuseStep 1706723 = 2560085) B2560085
theorem B2878193 : Blo 1705053 2878193 := bstep (se 2 (by rfl) ⟨1079322, by rfl⟩ : syracuseStep 2878193 = 2158645) B2158645
theorem B2558705 : Blo 1705053 2558705 := bstep (se 2 (by rfl) ⟨959514, by rfl⟩ : syracuseStep 2558705 = 1919029) B1919029
theorem B1919731 : Blo 1705053 1919731 := bstep (se 1 (by rfl) ⟨1439798, by rfl⟩ : syracuseStep 1919731 = 2879597) B2879597
theorem B1706739 : Blo 1705053 1706739 := bstep (se 1 (by rfl) ⟨1280054, by rfl⟩ : syracuseStep 1706739 = 2560109) B2560109
theorem B2558723 : Blo 1705053 2558723 := bstep (se 1 (by rfl) ⟨1919042, by rfl⟩ : syracuseStep 2558723 = 3838085) B3838085
theorem B1706755 : Blo 1705053 1706755 := bstep (se 1 (by rfl) ⟨1280066, by rfl⟩ : syracuseStep 1706755 = 2560133) B2560133
theorem B1706771 : Blo 1705053 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B2558753 : Blo 1705053 2558753 := bstep (se 2 (by rfl) ⟨959532, by rfl⟩ : syracuseStep 2558753 = 1919065) B1919065
theorem B1706787 : Blo 1705053 1706787 := bstep (se 1 (by rfl) ⟨1280090, by rfl⟩ : syracuseStep 1706787 = 2560181) B2560181
theorem B2558771 : Blo 1705053 2558771 := bstep (se 1 (by rfl) ⟨1919078, by rfl⟩ : syracuseStep 2558771 = 3838157) B3838157
theorem B1706803 : Blo 1705053 1706803 := bstep (se 1 (by rfl) ⟨1280102, by rfl⟩ : syracuseStep 1706803 = 2560205) B2560205
theorem B1706819 : Blo 1705053 1706819 := bstep (se 1 (by rfl) ⟨1280114, by rfl⟩ : syracuseStep 1706819 = 2560229) B2560229
theorem B3836753 : Blo 1705053 3836753 := bstep (se 2 (by rfl) ⟨1438782, by rfl⟩ : syracuseStep 3836753 = 2877565) B2877565
theorem B2558801 : Blo 1705053 2558801 := bstep (se 2 (by rfl) ⟨959550, by rfl⟩ : syracuseStep 2558801 = 1919101) B1919101
theorem B1706835 : Blo 1705053 1706835 := bstep (se 1 (by rfl) ⟨1280126, by rfl⟩ : syracuseStep 1706835 = 2560253) B2560253
theorem B3836771 : Blo 1705053 3836771 := bstep (se 1 (by rfl) ⟨2877578, by rfl⟩ : syracuseStep 3836771 = 5755157) B5755157
theorem B2558819 : Blo 1705053 2558819 := bstep (se 1 (by rfl) ⟨1919114, by rfl⟩ : syracuseStep 2558819 = 3838229) B3838229
theorem B1706851 : Blo 1705053 1706851 := bstep (se 1 (by rfl) ⟨1280138, by rfl⟩ : syracuseStep 1706851 = 2560277) B2560277
theorem B2878321 : Blo 1705053 2878321 := bstep (se 2 (by rfl) ⟨1079370, by rfl⟩ : syracuseStep 2878321 = 2158741) B2158741
theorem B1706867 : Blo 1705053 1706867 := bstep (se 1 (by rfl) ⟨1280150, by rfl⟩ : syracuseStep 1706867 = 2560301) B2560301
theorem B2558849 : Blo 1705053 2558849 := bstep (se 2 (by rfl) ⟨959568, by rfl⟩ : syracuseStep 2558849 = 1919137) B1919137
theorem B1919875 : Blo 1705053 1919875 := bstep (se 1 (by rfl) ⟨1439906, by rfl⟩ : syracuseStep 1919875 = 2879813) B2879813
theorem B1706883 : Blo 1705053 1706883 := bstep (se 1 (by rfl) ⟨1280162, by rfl⟩ : syracuseStep 1706883 = 2560325) B2560325
theorem B2878355 : Blo 1705053 2878355 := bstep (se 1 (by rfl) ⟨2158766, by rfl⟩ : syracuseStep 2878355 = 4317533) B4317533
theorem B2558867 : Blo 1705053 2558867 := bstep (se 1 (by rfl) ⟨1919150, by rfl⟩ : syracuseStep 2558867 = 3838301) B3838301
theorem B1706899 : Blo 1705053 1706899 := bstep (se 1 (by rfl) ⟨1280174, by rfl⟩ : syracuseStep 1706899 = 2560349) B2560349
theorem B1706915 : Blo 1705053 1706915 := bstep (se 1 (by rfl) ⟨1280186, by rfl⟩ : syracuseStep 1706915 = 2560373) B2560373
theorem B2558897 : Blo 1705053 2558897 := bstep (se 2 (by rfl) ⟨959586, by rfl⟩ : syracuseStep 2558897 = 1919173) B1919173
theorem B1706931 : Blo 1705053 1706931 := bstep (se 1 (by rfl) ⟨1280198, by rfl⟩ : syracuseStep 1706931 = 2560397) B2560397
theorem B2558915 : Blo 1705053 2558915 := bstep (se 1 (by rfl) ⟨1919186, by rfl⟩ : syracuseStep 2558915 = 3838373) B3838373
theorem B1706947 : Blo 1705053 1706947 := bstep (se 1 (by rfl) ⟨1280210, by rfl⟩ : syracuseStep 1706947 = 2560421) B2560421
theorem B4860881 : Blo 1705053 4860881 := bstep (se 2 (by rfl) ⟨1822830, by rfl⟩ : syracuseStep 4860881 = 3645661) B3645661
theorem B1706963 : Blo 1705053 1706963 := bstep (se 1 (by rfl) ⟨1280222, by rfl⟩ : syracuseStep 1706963 = 2560445) B2560445
theorem B2558945 : Blo 1705053 2558945 := bstep (se 2 (by rfl) ⟨959604, by rfl⟩ : syracuseStep 2558945 = 1919209) B1919209
theorem B1846243 : Blo 1705053 1846243 := bstep (se 1 (by rfl) ⟨1384682, by rfl⟩ : syracuseStep 1846243 = 2769365) B2769365
theorem B1706979 : Blo 1705053 1706979 := bstep (se 1 (by rfl) ⟨1280234, by rfl⟩ : syracuseStep 1706979 = 2560469) B2560469
theorem B2427889 : Blo 1705053 2427889 := bstep (se 2 (by rfl) ⟨910458, by rfl⟩ : syracuseStep 2427889 = 1820917) B1820917
theorem B2558963 : Blo 1705053 2558963 := bstep (se 1 (by rfl) ⟨1919222, by rfl⟩ : syracuseStep 2558963 = 3838445) B3838445
theorem B1706995 : Blo 1705053 1706995 := bstep (se 1 (by rfl) ⟨1280246, by rfl⟩ : syracuseStep 1706995 = 2560493) B2560493
theorem B1707011 : Blo 1705053 1707011 := bstep (se 1 (by rfl) ⟨1280258, by rfl⟩ : syracuseStep 1707011 = 2560517) B2560517
theorem B2558993 : Blo 1705053 2558993 := bstep (se 2 (by rfl) ⟨959622, by rfl⟩ : syracuseStep 2558993 = 1919245) B1919245
theorem B2878483 : Blo 1705053 2878483 := bstep (se 1 (by rfl) ⟨2158862, by rfl⟩ : syracuseStep 2878483 = 4317725) B4317725
theorem B1920019 : Blo 1705053 1920019 := bstep (se 1 (by rfl) ⟨1440014, by rfl⟩ : syracuseStep 1920019 = 2880029) B2880029
theorem B1707027 : Blo 1705053 1707027 := bstep (se 1 (by rfl) ⟨1280270, by rfl⟩ : syracuseStep 1707027 = 2560541) B2560541
theorem B2559011 : Blo 1705053 2559011 := bstep (se 1 (by rfl) ⟨1919258, by rfl⟩ : syracuseStep 2559011 = 3838517) B3838517
theorem B1707043 : Blo 1705053 1707043 := bstep (se 1 (by rfl) ⟨1280282, by rfl⟩ : syracuseStep 1707043 = 2560565) B2560565
theorem B2559041 : Blo 1705053 2559041 := bstep (se 2 (by rfl) ⟨959640, by rfl⟩ : syracuseStep 2559041 = 1919281) B1919281
theorem B4320337 : Blo 1705053 4320337 := bstep (se 2 (by rfl) ⟨1620126, by rfl⟩ : syracuseStep 4320337 = 3240253) B3240253
theorem B2559059 : Blo 1705053 2559059 := bstep (se 1 (by rfl) ⟨1919294, by rfl⟩ : syracuseStep 2559059 = 3838589) B3838589
theorem B2428003 : Blo 1705053 2428003 := bstep (se 1 (by rfl) ⟨1821002, by rfl⟩ : syracuseStep 2428003 = 3642005) B3642005
theorem B3837041 : Blo 1705053 3837041 := bstep (se 2 (by rfl) ⟨1438890, by rfl⟩ : syracuseStep 3837041 = 2877781) B2877781
theorem B2559089 : Blo 1705053 2559089 := bstep (se 2 (by rfl) ⟨959658, by rfl⟩ : syracuseStep 2559089 = 1919317) B1919317
theorem B3837059 : Blo 1705053 3837059 := bstep (se 1 (by rfl) ⟨2877794, by rfl⟩ : syracuseStep 3837059 = 5755589) B5755589
theorem B2559107 : Blo 1705053 2559107 := bstep (se 1 (by rfl) ⟨1919330, by rfl⟩ : syracuseStep 2559107 = 3838661) B3838661
theorem B2878625 : Blo 1705053 2878625 := bstep (se 2 (by rfl) ⟨1079484, by rfl⟩ : syracuseStep 2878625 = 2158969) B2158969
theorem B2559137 : Blo 1705053 2559137 := bstep (se 2 (by rfl) ⟨959676, by rfl⟩ : syracuseStep 2559137 = 1919353) B1919353
theorem B1920163 : Blo 1705053 1920163 := bstep (se 1 (by rfl) ⟨1440122, by rfl⟩ : syracuseStep 1920163 = 2880245) B2880245
theorem B5467313 : Blo 1705053 5467313 := bstep (se 2 (by rfl) ⟨2050242, by rfl⟩ : syracuseStep 5467313 = 4100485) B4100485
theorem B2559155 : Blo 1705053 2559155 := bstep (se 1 (by rfl) ⟨1919366, by rfl⟩ : syracuseStep 2559155 = 3838733) B3838733
theorem B2559185 : Blo 1705053 2559185 := bstep (se 2 (by rfl) ⟨959694, by rfl⟩ : syracuseStep 2559185 = 1919389) B1919389
theorem B4156625 : Blo 1705053 4156625 := bstep (se 2 (by rfl) ⟨1558734, by rfl⟩ : syracuseStep 4156625 = 3117469) B3117469
theorem B2559203 : Blo 1705053 2559203 := bstep (se 1 (by rfl) ⟨1919402, by rfl⟩ : syracuseStep 2559203 = 3838805) B3838805
theorem B2559233 : Blo 1705053 2559233 := bstep (se 2 (by rfl) ⟨959712, by rfl⟩ : syracuseStep 2559233 = 1919425) B1919425
theorem B2731267 : Blo 1705053 2731267 := bstep (se 1 (by rfl) ⟨2048450, by rfl⟩ : syracuseStep 2731267 = 4096901) B4096901
theorem B2559251 : Blo 1705053 2559251 := bstep (se 1 (by rfl) ⟨1919438, by rfl⟩ : syracuseStep 2559251 = 3838877) B3838877
theorem B2878753 : Blo 1705053 2878753 := bstep (se 2 (by rfl) ⟨1079532, by rfl⟩ : syracuseStep 2878753 = 2159065) B2159065
theorem B2559281 : Blo 1705053 2559281 := bstep (se 2 (by rfl) ⟨959730, by rfl⟩ : syracuseStep 2559281 = 1919461) B1919461
theorem B1920307 : Blo 1705053 1920307 := bstep (se 1 (by rfl) ⟨1440230, by rfl⟩ : syracuseStep 1920307 = 2880461) B2880461
theorem B2878787 : Blo 1705053 2878787 := bstep (se 1 (by rfl) ⟨2159090, by rfl⟩ : syracuseStep 2878787 = 4318181) B4318181
theorem B2559299 : Blo 1705053 2559299 := bstep (se 1 (by rfl) ⟨1919474, by rfl⟩ : syracuseStep 2559299 = 3838949) B3838949
theorem B1822019 : Blo 1705053 1822019 := bstep (se 1 (by rfl) ⟨1366514, by rfl⟩ : syracuseStep 1822019 = 2733029) B2733029
theorem B6475085 : Blo 1705053 6475085 := bstep (se 3 (by rfl) ⟨1214078, by rfl⟩ : syracuseStep 6475085 = 2428157) B2428157
theorem B2559329 : Blo 1705053 2559329 := bstep (se 2 (by rfl) ⟨959748, by rfl⟩ : syracuseStep 2559329 = 1919497) B1919497
theorem B4320611 : Blo 1705053 4320611 := bstep (se 1 (by rfl) ⟨3240458, by rfl⟩ : syracuseStep 4320611 = 6480917) B6480917
theorem B3239281 : Blo 1705053 3239281 := bstep (se 2 (by rfl) ⟨1214730, by rfl⟩ : syracuseStep 3239281 = 2429461) B2429461
theorem B3460465 : Blo 1705053 3460465 := bstep (se 2 (by rfl) ⟨1297674, by rfl⟩ : syracuseStep 3460465 = 2595349) B2595349
theorem B2559347 : Blo 1705053 2559347 := bstep (se 1 (by rfl) ⟨1919510, by rfl⟩ : syracuseStep 2559347 = 3839021) B3839021
theorem B3837329 : Blo 1705053 3837329 := bstep (se 2 (by rfl) ⟨1438998, by rfl⟩ : syracuseStep 3837329 = 2877997) B2877997
theorem B2559377 : Blo 1705053 2559377 := bstep (se 2 (by rfl) ⟨959766, by rfl⟩ : syracuseStep 2559377 = 1919533) B1919533
theorem B3837347 : Blo 1705053 3837347 := bstep (se 1 (by rfl) ⟨2878010, by rfl⟩ : syracuseStep 3837347 = 5756021) B5756021
theorem B2559395 : Blo 1705053 2559395 := bstep (se 1 (by rfl) ⟨1919546, by rfl⟩ : syracuseStep 2559395 = 3839093) B3839093
theorem B2305459 : Blo 1705053 2305459 := bstep (se 1 (by rfl) ⟨1729094, by rfl⟩ : syracuseStep 2305459 = 3458189) B3458189
theorem B2559425 : Blo 1705053 2559425 := bstep (se 2 (by rfl) ⟨959784, by rfl⟩ : syracuseStep 2559425 = 1919569) B1919569
theorem B2878915 : Blo 1705053 2878915 := bstep (se 1 (by rfl) ⟨2159186, by rfl⟩ : syracuseStep 2878915 = 4318373) B4318373
theorem B4435409 : Blo 1705053 4435409 := bstep (se 2 (by rfl) ⟨1663278, by rfl⟩ : syracuseStep 4435409 = 3326557) B3326557
theorem B2559443 : Blo 1705053 2559443 := bstep (se 1 (by rfl) ⟨1919582, by rfl⟩ : syracuseStep 2559443 = 3839165) B3839165
theorem B2559473 : Blo 1705053 2559473 := bstep (se 2 (by rfl) ⟨959802, by rfl⟩ : syracuseStep 2559473 = 1919605) B1919605
theorem B2559491 : Blo 1705053 2559491 := bstep (se 1 (by rfl) ⟨1919618, by rfl⟩ : syracuseStep 2559491 = 3839237) B3839237
theorem B2559521 : Blo 1705053 2559521 := bstep (se 2 (by rfl) ⟨959820, by rfl⟩ : syracuseStep 2559521 = 1919641) B1919641
theorem B4320803 : Blo 1705053 4320803 := bstep (se 1 (by rfl) ⟨3240602, by rfl⟩ : syracuseStep 4320803 = 6481205) B6481205
theorem B8638001 : Blo 1705053 8638001 := bstep (se 2 (by rfl) ⟨3239250, by rfl⟩ : syracuseStep 8638001 = 6478501) B6478501
theorem B2559539 : Blo 1705053 2559539 := bstep (se 1 (by rfl) ⟨1919654, by rfl⟩ : syracuseStep 2559539 = 3839309) B3839309
theorem B2879057 : Blo 1705053 2879057 := bstep (se 2 (by rfl) ⟨1079646, by rfl⟩ : syracuseStep 2879057 = 2159293) B2159293
theorem B2559569 : Blo 1705053 2559569 := bstep (se 2 (by rfl) ⟨959838, by rfl⟩ : syracuseStep 2559569 = 1919677) B1919677
theorem B2559587 : Blo 1705053 2559587 := bstep (se 1 (by rfl) ⟨1919690, by rfl⟩ : syracuseStep 2559587 = 3839381) B3839381
theorem B2559617 : Blo 1705053 2559617 := bstep (se 2 (by rfl) ⟨959856, by rfl⟩ : syracuseStep 2559617 = 1919713) B1919713
theorem B2559635 : Blo 1705053 2559635 := bstep (se 1 (by rfl) ⟨1919726, by rfl⟩ : syracuseStep 2559635 = 3839453) B3839453
theorem B3837617 : Blo 1705053 3837617 := bstep (se 2 (by rfl) ⟨1439106, by rfl⟩ : syracuseStep 3837617 = 2878213) B2878213
theorem B2559665 : Blo 1705053 2559665 := bstep (se 2 (by rfl) ⟨959874, by rfl⟩ : syracuseStep 2559665 = 1919749) B1919749
theorem B5754563 : Blo 1705053 5754563 := bstep (se 1 (by rfl) ⟨4315922, by rfl⟩ : syracuseStep 5754563 = 8631845) B8631845
theorem B3837635 : Blo 1705053 3837635 := bstep (se 1 (by rfl) ⟨2878226, by rfl⟩ : syracuseStep 3837635 = 5756453) B5756453
theorem B2559683 : Blo 1705053 2559683 := bstep (se 1 (by rfl) ⟨1919762, by rfl⟩ : syracuseStep 2559683 = 3839525) B3839525
theorem B2879185 : Blo 1705053 2879185 := bstep (se 2 (by rfl) ⟨1079694, by rfl⟩ : syracuseStep 2879185 = 2159389) B2159389
theorem B2559713 : Blo 1705053 2559713 := bstep (se 2 (by rfl) ⟨959892, by rfl⟩ : syracuseStep 2559713 = 1919785) B1919785
theorem B2879219 : Blo 1705053 2879219 := bstep (se 1 (by rfl) ⟨2159414, by rfl⟩ : syracuseStep 2879219 = 4318829) B4318829
theorem B2559731 : Blo 1705053 2559731 := bstep (se 1 (by rfl) ⟨1919798, by rfl⟩ : syracuseStep 2559731 = 3839597) B3839597
theorem B9711373 : Blo 1705053 9711373 := bstep (se 3 (by rfl) ⟨1820882, by rfl⟩ : syracuseStep 9711373 = 3641765) B3641765
theorem B2559761 : Blo 1705053 2559761 := bstep (se 2 (by rfl) ⟨959910, by rfl⟩ : syracuseStep 2559761 = 1919821) B1919821
theorem B2731811 : Blo 1705053 2731811 := bstep (se 1 (by rfl) ⟨2048858, by rfl⟩ : syracuseStep 2731811 = 4097717) B4097717
theorem B2559779 : Blo 1705053 2559779 := bstep (se 1 (by rfl) ⟨1919834, by rfl⟩ : syracuseStep 2559779 = 3839669) B3839669
theorem B2559809 : Blo 1705053 2559809 := bstep (se 2 (by rfl) ⟨959928, by rfl⟩ : syracuseStep 2559809 = 1919857) B1919857
theorem B9719621 : Blo 1705053 9719621 := bstep (se 4 (by rfl) ⟨911214, by rfl⟩ : syracuseStep 9719621 = 1822429) B1822429
theorem B2559827 : Blo 1705053 2559827 := bstep (se 1 (by rfl) ⟨1919870, by rfl⟩ : syracuseStep 2559827 = 3839741) B3839741
theorem B2559857 : Blo 1705053 2559857 := bstep (se 2 (by rfl) ⟨959946, by rfl⟩ : syracuseStep 2559857 = 1919893) B1919893
theorem B2879347 : Blo 1705053 2879347 := bstep (se 1 (by rfl) ⟨2159510, by rfl⟩ : syracuseStep 2879347 = 4319021) B4319021
theorem B2559875 : Blo 1705053 2559875 := bstep (se 1 (by rfl) ⟨1919906, by rfl⟩ : syracuseStep 2559875 = 3839813) B3839813
theorem B4099985 : Blo 1705053 4099985 := bstep (se 2 (by rfl) ⟨1537494, by rfl⟩ : syracuseStep 4099985 = 3074989) B3074989
theorem B2158483 : Blo 1705053 2158483 := bstep (se 1 (by rfl) ⟨1618862, by rfl⟩ : syracuseStep 2158483 = 3237725) B3237725
theorem B2559905 : Blo 1705053 2559905 := bstep (se 2 (by rfl) ⟨959964, by rfl⟩ : syracuseStep 2559905 = 1919929) B1919929
theorem B2559923 : Blo 1705053 2559923 := bstep (se 1 (by rfl) ⟨1919942, by rfl⟩ : syracuseStep 2559923 = 3839885) B3839885
theorem B5754833 : Blo 1705053 5754833 := bstep (se 2 (by rfl) ⟨2158062, by rfl⟩ : syracuseStep 5754833 = 4316125) B4316125
theorem B2731985 : Blo 1705053 2731985 := bstep (se 2 (by rfl) ⟨1024494, by rfl⟩ : syracuseStep 2731985 = 2048989) B2048989
theorem B3837905 : Blo 1705053 3837905 := bstep (se 2 (by rfl) ⟨1439214, by rfl⟩ : syracuseStep 3837905 = 2878429) B2878429
theorem B2559953 : Blo 1705053 2559953 := bstep (se 2 (by rfl) ⟨959982, by rfl⟩ : syracuseStep 2559953 = 1919965) B1919965
theorem B3837923 : Blo 1705053 3837923 := bstep (se 1 (by rfl) ⟨2878442, by rfl⟩ : syracuseStep 3837923 = 5756885) B5756885
theorem B2559971 : Blo 1705053 2559971 := bstep (se 1 (by rfl) ⟨1919978, by rfl⟩ : syracuseStep 2559971 = 3839957) B3839957
theorem B2158579 : Blo 1705053 2158579 := bstep (se 1 (by rfl) ⟨1618934, by rfl⟩ : syracuseStep 2158579 = 3237869) B3237869
theorem B2879489 : Blo 1705053 2879489 := bstep (se 2 (by rfl) ⟨1079808, by rfl⟩ : syracuseStep 2879489 = 2159617) B2159617
theorem B2560001 : Blo 1705053 2560001 := bstep (se 2 (by rfl) ⟨960000, by rfl⟩ : syracuseStep 2560001 = 1920001) B1920001
theorem B6230029 : Blo 1705053 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B2560019 : Blo 1705053 2560019 := bstep (se 1 (by rfl) ⟨1920014, by rfl⟩ : syracuseStep 2560019 = 3840029) B3840029
theorem B2560049 : Blo 1705053 2560049 := bstep (se 2 (by rfl) ⟨960018, by rfl⟩ : syracuseStep 2560049 = 1920037) B1920037
theorem B1822771 : Blo 1705053 1822771 := bstep (se 1 (by rfl) ⟨1367078, by rfl⟩ : syracuseStep 1822771 = 2734157) B2734157
theorem B2560067 : Blo 1705053 2560067 := bstep (se 1 (by rfl) ⟨1920050, by rfl⟩ : syracuseStep 2560067 = 3840101) B3840101
theorem B4100177 : Blo 1705053 4100177 := bstep (se 2 (by rfl) ⟨1537566, by rfl⟩ : syracuseStep 4100177 = 3075133) B3075133
theorem B2560097 : Blo 1705053 2560097 := bstep (se 2 (by rfl) ⟨960036, by rfl⟩ : syracuseStep 2560097 = 1920073) B1920073
theorem B2592881 : Blo 1705053 2592881 := bstep (se 2 (by rfl) ⟨972330, by rfl⟩ : syracuseStep 2592881 = 1944661) B1944661
theorem B6475889 : Blo 1705053 6475889 := bstep (se 2 (by rfl) ⟨2428458, by rfl⟩ : syracuseStep 6475889 = 4856917) B4856917
theorem B2560115 : Blo 1705053 2560115 := bstep (se 1 (by rfl) ⟨1920086, by rfl⟩ : syracuseStep 2560115 = 3840173) B3840173
theorem B2879617 : Blo 1705053 2879617 := bstep (se 2 (by rfl) ⟨1079856, by rfl⟩ : syracuseStep 2879617 = 2159713) B2159713
theorem B2560145 : Blo 1705053 2560145 := bstep (se 2 (by rfl) ⟨960054, by rfl⟩ : syracuseStep 2560145 = 1920109) B1920109
theorem B2879651 : Blo 1705053 2879651 := bstep (se 1 (by rfl) ⟨2159738, by rfl⟩ : syracuseStep 2879651 = 4319477) B4319477
theorem B2560163 : Blo 1705053 2560163 := bstep (se 1 (by rfl) ⟨1920122, by rfl⟩ : syracuseStep 2560163 = 3840245) B3840245
theorem B10514609 : Blo 1705053 10514609 := bstep (se 2 (by rfl) ⟨3942978, by rfl⟩ : syracuseStep 10514609 = 7885957) B7885957
theorem B2560193 : Blo 1705053 2560193 := bstep (se 2 (by rfl) ⟨960072, by rfl⟩ : syracuseStep 2560193 = 1920145) B1920145
theorem B2560211 : Blo 1705053 2560211 := bstep (se 1 (by rfl) ⟨1920158, by rfl⟩ : syracuseStep 2560211 = 3840317) B3840317
theorem B3281123 : Blo 1705053 3281123 := bstep (se 1 (by rfl) ⟨2460842, by rfl⟩ : syracuseStep 3281123 = 4921685) B4921685
theorem B3838193 : Blo 1705053 3838193 := bstep (se 2 (by rfl) ⟨1439322, by rfl⟩ : syracuseStep 3838193 = 2878645) B2878645
theorem B2560241 : Blo 1705053 2560241 := bstep (se 2 (by rfl) ⟨960090, by rfl⟩ : syracuseStep 2560241 = 1920181) B1920181
theorem B3838211 : Blo 1705053 3838211 := bstep (se 1 (by rfl) ⟨2878658, by rfl⟩ : syracuseStep 3838211 = 5757317) B5757317
theorem B2560259 : Blo 1705053 2560259 := bstep (se 1 (by rfl) ⟨1920194, by rfl⟩ : syracuseStep 2560259 = 3840389) B3840389
theorem B2560289 : Blo 1705053 2560289 := bstep (se 2 (by rfl) ⟨960108, by rfl⟩ : syracuseStep 2560289 = 1920217) B1920217
theorem B2879779 : Blo 1705053 2879779 := bstep (se 1 (by rfl) ⟨2159834, by rfl⟩ : syracuseStep 2879779 = 4319669) B4319669
theorem B2560307 : Blo 1705053 2560307 := bstep (se 1 (by rfl) ⟨1920230, by rfl⟩ : syracuseStep 2560307 = 3840461) B3840461
theorem B2560337 : Blo 1705053 2560337 := bstep (se 2 (by rfl) ⟨960126, by rfl⟩ : syracuseStep 2560337 = 1920253) B1920253
theorem B2560355 : Blo 1705053 2560355 := bstep (se 1 (by rfl) ⟨1920266, by rfl⟩ : syracuseStep 2560355 = 3840533) B3840533
theorem B2560385 : Blo 1705053 2560385 := bstep (se 2 (by rfl) ⟨960144, by rfl⟩ : syracuseStep 2560385 = 1920289) B1920289
theorem B3240337 : Blo 1705053 3240337 := bstep (se 2 (by rfl) ⟨1215126, by rfl⟩ : syracuseStep 3240337 = 2430253) B2430253
theorem B2560403 : Blo 1705053 2560403 := bstep (se 1 (by rfl) ⟨1920302, by rfl⟩ : syracuseStep 2560403 = 3840605) B3840605
theorem B2429347 : Blo 1705053 2429347 := bstep (se 1 (by rfl) ⟨1822010, by rfl⟩ : syracuseStep 2429347 = 3644021) B3644021
theorem B2879921 : Blo 1705053 2879921 := bstep (se 2 (by rfl) ⟨1079970, by rfl⟩ : syracuseStep 2879921 = 2159941) B2159941
theorem B2560433 : Blo 1705053 2560433 := bstep (se 2 (by rfl) ⟨960162, by rfl⟩ : syracuseStep 2560433 = 1920325) B1920325
theorem B2306497 : Blo 1705053 2306497 := bstep (se 2 (by rfl) ⟨864936, by rfl⟩ : syracuseStep 2306497 = 1729873) B1729873
theorem B2560451 : Blo 1705053 2560451 := bstep (se 1 (by rfl) ⟨1920338, by rfl⟩ : syracuseStep 2560451 = 3840677) B3840677
theorem B10932677 : Blo 1705053 10932677 := bstep (se 4 (by rfl) ⟨1024938, by rfl⟩ : syracuseStep 10932677 = 2049877) B2049877
theorem B2560481 : Blo 1705053 2560481 := bstep (se 2 (by rfl) ⟨960180, by rfl⟩ : syracuseStep 2560481 = 1920361) B1920361
theorem B2159075 : Blo 1705053 2159075 := bstep (se 1 (by rfl) ⟨1619306, by rfl⟩ : syracuseStep 2159075 = 3238613) B3238613
theorem B5190115 : Blo 1705053 5190115 := bstep (se 1 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 5190115 = 7785173) B7785173
theorem B5755373 : Blo 1705053 5755373 := bstep (se 3 (by rfl) ⟨1079132, by rfl⟩ : syracuseStep 5755373 = 2158265) B2158265
theorem B2560499 : Blo 1705053 2560499 := bstep (se 1 (by rfl) ⟨1920374, by rfl⟩ : syracuseStep 2560499 = 3840749) B3840749
theorem B3838481 : Blo 1705053 3838481 := bstep (se 2 (by rfl) ⟨1439430, by rfl⟩ : syracuseStep 3838481 = 2878861) B2878861
theorem B2560529 : Blo 1705053 2560529 := bstep (se 2 (by rfl) ⟨960198, by rfl⟩ : syracuseStep 2560529 = 1920397) B1920397
theorem B5755427 : Blo 1705053 5755427 := bstep (se 1 (by rfl) ⟨4316570, by rfl⟩ : syracuseStep 5755427 = 8633141) B8633141
theorem B3838499 : Blo 1705053 3838499 := bstep (se 1 (by rfl) ⟨2878874, by rfl⟩ : syracuseStep 3838499 = 5757749) B5757749
theorem B2560547 : Blo 1705053 2560547 := bstep (se 1 (by rfl) ⟨1920410, by rfl⟩ : syracuseStep 2560547 = 3840821) B3840821
theorem B2880049 : Blo 1705053 2880049 := bstep (se 2 (by rfl) ⟨1080018, by rfl⟩ : syracuseStep 2880049 = 2160037) B2160037
theorem B2560577 : Blo 1705053 2560577 := bstep (se 2 (by rfl) ⟨960216, by rfl⟩ : syracuseStep 2560577 = 1920433) B1920433
theorem B2880083 : Blo 1705053 2880083 := bstep (se 1 (by rfl) ⟨2160062, by rfl⟩ : syracuseStep 2880083 = 4320125) B4320125
theorem B12956273 : Blo 1705053 12956273 := bstep (se 2 (by rfl) ⟨4858602, by rfl⟩ : syracuseStep 12956273 = 9717205) B9717205
theorem B2880211 : Blo 1705053 2880211 := bstep (se 1 (by rfl) ⟨2160158, by rfl⟩ : syracuseStep 2880211 = 4320317) B4320317
theorem B6476557 : Blo 1705053 6476557 := bstep (se 3 (by rfl) ⟨1214354, by rfl⟩ : syracuseStep 6476557 = 2428709) B2428709
theorem B5755697 : Blo 1705053 5755697 := bstep (se 2 (by rfl) ⟨2158386, by rfl⟩ : syracuseStep 5755697 = 4316773) B4316773
theorem B3838769 : Blo 1705053 3838769 := bstep (se 2 (by rfl) ⟨1439538, by rfl⟩ : syracuseStep 3838769 = 2879077) B2879077
theorem B3838787 : Blo 1705053 3838787 := bstep (se 1 (by rfl) ⟨2879090, by rfl⟩ : syracuseStep 3838787 = 5758181) B5758181
theorem B2880353 : Blo 1705053 2880353 := bstep (se 2 (by rfl) ⟨1080132, by rfl⟩ : syracuseStep 2880353 = 2160265) B2160265
theorem B6746993 : Blo 1705053 6746993 := bstep (se 2 (by rfl) ⟨2530122, by rfl⟩ : syracuseStep 6746993 = 5060245) B5060245
theorem B21869453 : Blo 1705053 21869453 := bstep (se 3 (by rfl) ⟨4100522, by rfl⟩ : syracuseStep 21869453 = 8201045) B8201045
theorem B43709381 : Blo 1705053 43709381 := bstep (se 4 (by rfl) ⟨4097754, by rfl⟩ : syracuseStep 43709381 = 8195509) B8195509
theorem B2880481 : Blo 1705053 2880481 := bstep (se 2 (by rfl) ⟨1080180, by rfl⟩ : syracuseStep 2880481 = 2160361) B2160361
theorem B8639459 : Blo 1705053 8639459 := bstep (se 1 (by rfl) ⟨6479594, by rfl⟩ : syracuseStep 8639459 = 12959189) B12959189
theorem B2880515 : Blo 1705053 2880515 := bstep (se 1 (by rfl) ⟨2160386, by rfl⟩ : syracuseStep 2880515 = 4320773) B4320773
theorem B19436597 : Blo 1705053 19436597 := bstep (se 5 (by rfl) ⟨911090, by rfl⟩ : syracuseStep 19436597 = 1822181) B1822181
theorem B3839057 : Blo 1705053 3839057 := bstep (se 2 (by rfl) ⟨1439646, by rfl⟩ : syracuseStep 3839057 = 2879293) B2879293
theorem B3839075 : Blo 1705053 3839075 := bstep (se 1 (by rfl) ⟨2879306, by rfl⟩ : syracuseStep 3839075 = 5758613) B5758613
theorem B5837923 : Blo 1705053 5837923 := bstep (se 1 (by rfl) ⟨4378442, by rfl⟩ : syracuseStep 5837923 = 8756885) B8756885
theorem B2880643 : Blo 1705053 2880643 := bstep (se 1 (by rfl) ⟨2160482, by rfl⟩ : syracuseStep 2880643 = 4320965) B4320965
theorem B2159779 : Blo 1705053 2159779 := bstep (se 1 (by rfl) ⟨1619834, by rfl⟩ : syracuseStep 2159779 = 3239669) B3239669
theorem B4609219 : Blo 1705053 4609219 := bstep (se 1 (by rfl) ⟨3456914, by rfl⟩ : syracuseStep 4609219 = 6913829) B6913829
theorem B2593987 : Blo 1705053 2593987 := bstep (se 1 (by rfl) ⟨1945490, by rfl⟩ : syracuseStep 2593987 = 3890981) B3890981
theorem B2159875 : Blo 1705053 2159875 := bstep (se 1 (by rfl) ⟨1619906, by rfl⟩ : syracuseStep 2159875 = 3239813) B3239813
theorem B5190979 : Blo 1705053 5190979 := bstep (se 1 (by rfl) ⟨3893234, by rfl⟩ : syracuseStep 5190979 = 7786469) B7786469
theorem B5756237 : Blo 1705053 5756237 := bstep (se 3 (by rfl) ⟨1079294, by rfl⟩ : syracuseStep 5756237 = 2158589) B2158589
theorem B7288163 : Blo 1705053 7288163 := bstep (se 1 (by rfl) ⟨5466122, by rfl⟩ : syracuseStep 7288163 = 10932245) B10932245
theorem B3839345 : Blo 1705053 3839345 := bstep (se 2 (by rfl) ⟨1439754, by rfl⟩ : syracuseStep 3839345 = 2879509) B2879509
theorem B5756291 : Blo 1705053 5756291 := bstep (se 1 (by rfl) ⟨4317218, by rfl⟩ : syracuseStep 5756291 = 8634437) B8634437
theorem B3839363 : Blo 1705053 3839363 := bstep (se 1 (by rfl) ⟨2879522, by rfl⟩ : syracuseStep 3839363 = 5759045) B5759045
theorem B10376581 : Blo 1705053 10376581 := bstep (se 4 (by rfl) ⟨972804, by rfl⟩ : syracuseStep 10376581 = 1945609) B1945609
theorem B4609457 : Blo 1705053 4609457 := bstep (se 2 (by rfl) ⟨1728546, by rfl⟩ : syracuseStep 4609457 = 3457093) B3457093
theorem B29152709 : Blo 1705053 29152709 := bstep (se 4 (by rfl) ⟨2733066, by rfl⟩ : syracuseStep 29152709 = 5466133) B5466133
theorem B2430481 : Blo 1705053 2430481 := bstep (se 2 (by rfl) ⟨911430, by rfl⟩ : syracuseStep 2430481 = 1822861) B1822861
theorem B6477347 : Blo 1705053 6477347 := bstep (se 1 (by rfl) ⟨4858010, by rfl⟩ : syracuseStep 6477347 = 9716021) B9716021
theorem B5756561 : Blo 1705053 5756561 := bstep (se 2 (by rfl) ⟨2158710, by rfl⟩ : syracuseStep 5756561 = 4317421) B4317421
theorem B3839633 : Blo 1705053 3839633 := bstep (se 2 (by rfl) ⟨1439862, by rfl⟩ : syracuseStep 3839633 = 2879725) B2879725
theorem B4855459 : Blo 1705053 4855459 := bstep (se 1 (by rfl) ⟨3641594, by rfl⟩ : syracuseStep 4855459 = 7283189) B7283189
theorem B3839651 : Blo 1705053 3839651 := bstep (se 1 (by rfl) ⟨2879738, by rfl⟩ : syracuseStep 3839651 = 5759477) B5759477
theorem B5330627 : Blo 1705053 5330627 := bstep (se 1 (by rfl) ⟨3997970, by rfl⟩ : syracuseStep 5330627 = 7995941) B7995941
theorem B9713357 : Blo 1705053 9713357 := bstep (se 3 (by rfl) ⟨1821254, by rfl⟩ : syracuseStep 9713357 = 3642509) B3642509
theorem B2160371 : Blo 1705053 2160371 := bstep (se 1 (by rfl) ⟨1620278, by rfl⟩ : syracuseStep 2160371 = 3240557) B3240557
theorem B8640269 : Blo 1705053 8640269 := bstep (se 3 (by rfl) ⟨1620050, by rfl⟩ : syracuseStep 8640269 = 3240101) B3240101
theorem B369407765 : Blo 1705053 369407765 := bstep (se 6 (by rfl) ⟨8657994, by rfl⟩ : syracuseStep 369407765 = 17315989) B17315989
theorem B4855619 : Blo 1705053 4855619 := bstep (se 1 (by rfl) ⟨3641714, by rfl⟩ : syracuseStep 4855619 = 7283429) B7283429
theorem B6149965 : Blo 1705053 6149965 := bstep (se 3 (by rfl) ⟨1153118, by rfl⟩ : syracuseStep 6149965 = 2306237) B2306237
theorem B3643235 : Blo 1705053 3643235 := bstep (se 1 (by rfl) ⟨2732426, by rfl⟩ : syracuseStep 3643235 = 5464853) B5464853
theorem B3839921 : Blo 1705053 3839921 := bstep (se 2 (by rfl) ⟨1439970, by rfl⟩ : syracuseStep 3839921 = 2879941) B2879941
theorem B2734003 : Blo 1705053 2734003 := bstep (se 1 (by rfl) ⟨2050502, by rfl⟩ : syracuseStep 2734003 = 4101005) B4101005
theorem B3839939 : Blo 1705053 3839939 := bstep (se 1 (by rfl) ⟨2879954, by rfl⟩ : syracuseStep 3839939 = 5759909) B5759909
theorem B2734067 : Blo 1705053 2734067 := bstep (se 1 (by rfl) ⟨2050550, by rfl⟩ : syracuseStep 2734067 = 4101101) B4101101
theorem B5757101 : Blo 1705053 5757101 := bstep (se 3 (by rfl) ⟨1079456, by rfl⟩ : syracuseStep 5757101 = 2158913) B2158913
theorem B6478001 : Blo 1705053 6478001 := bstep (se 2 (by rfl) ⟨2429250, by rfl⟩ : syracuseStep 6478001 = 4858501) B4858501
theorem B14579909 : Blo 1705053 14579909 := bstep (se 4 (by rfl) ⟨1366866, by rfl⟩ : syracuseStep 14579909 = 2733733) B2733733
theorem B3840209 : Blo 1705053 3840209 := bstep (se 2 (by rfl) ⟨1440078, by rfl⟩ : syracuseStep 3840209 = 2880157) B2880157
theorem B5757155 : Blo 1705053 5757155 := bstep (se 1 (by rfl) ⟨4317866, by rfl⟩ : syracuseStep 5757155 = 8635733) B8635733
theorem B3840227 : Blo 1705053 3840227 := bstep (se 1 (by rfl) ⟨2880170, by rfl⟩ : syracuseStep 3840227 = 5760341) B5760341
theorem B3643697 : Blo 1705053 3643697 := bstep (se 2 (by rfl) ⟨1366386, by rfl⟩ : syracuseStep 3643697 = 2732773) B2732773
theorem B14571845 : Blo 1705053 14571845 := bstep (se 4 (by rfl) ⟨1366110, by rfl⟩ : syracuseStep 14571845 = 2732221) B2732221
theorem B39950819 : Blo 1705053 39950819 := bstep (se 1 (by rfl) ⟨29963114, by rfl⟩ : syracuseStep 39950819 = 59926229) B59926229
theorem B8632817 : Blo 1705053 8632817 := bstep (se 2 (by rfl) ⟨3237306, by rfl⟩ : syracuseStep 8632817 = 6474613) B6474613
theorem B5757425 : Blo 1705053 5757425 := bstep (se 2 (by rfl) ⟨2159034, by rfl⟩ : syracuseStep 5757425 = 4318069) B4318069
theorem B3840497 : Blo 1705053 3840497 := bstep (se 2 (by rfl) ⟨1440186, by rfl⟩ : syracuseStep 3840497 = 2880373) B2880373
theorem B3840515 : Blo 1705053 3840515 := bstep (se 1 (by rfl) ⟨2880386, by rfl⟩ : syracuseStep 3840515 = 5760773) B5760773
theorem B15563333 : Blo 1705053 15563333 := bstep (se 4 (by rfl) ⟨1459062, by rfl⟩ : syracuseStep 15563333 = 2918125) B2918125
theorem B9714289 : Blo 1705053 9714289 := bstep (se 2 (by rfl) ⟨3642858, by rfl⟩ : syracuseStep 9714289 = 7285717) B7285717
theorem B16628365 : Blo 1705053 16628365 := bstep (se 3 (by rfl) ⟨3117818, by rfl⟩ : syracuseStep 16628365 = 6235637) B6235637
theorem B3840785 : Blo 1705053 3840785 := bstep (se 2 (by rfl) ⟨1440294, by rfl⟩ : syracuseStep 3840785 = 2880589) B2880589
theorem B3840803 : Blo 1705053 3840803 := bstep (se 1 (by rfl) ⟨2880602, by rfl⟩ : syracuseStep 3840803 = 5761205) B5761205
theorem B4856689 : Blo 1705053 4856689 := bstep (se 2 (by rfl) ⟨1821258, by rfl⟩ : syracuseStep 4856689 = 3642517) B3642517
theorem B14580593 : Blo 1705053 14580593 := bstep (se 2 (by rfl) ⟨5467722, by rfl⟩ : syracuseStep 14580593 = 10935445) B10935445
theorem B12295109 : Blo 1705053 12295109 := bstep (se 4 (by rfl) ⟨1152666, by rfl⟩ : syracuseStep 12295109 = 2305333) B2305333
theorem B5757965 : Blo 1705053 5757965 := bstep (se 3 (by rfl) ⟨1079618, by rfl⟩ : syracuseStep 5757965 = 2159237) B2159237
theorem B5463085 : Blo 1705053 5463085 := bstep (se 3 (by rfl) ⟨1024328, by rfl⟩ : syracuseStep 5463085 = 2048657) B2048657
theorem B9223217 : Blo 1705053 9223217 := bstep (se 2 (by rfl) ⟨3458706, by rfl⟩ : syracuseStep 9223217 = 6917413) B6917413
theorem B5758019 : Blo 1705053 5758019 := bstep (se 1 (by rfl) ⟨4318514, by rfl⟩ : syracuseStep 5758019 = 8637029) B8637029
theorem B10935395 : Blo 1705053 10935395 := bstep (se 1 (by rfl) ⟨8201546, by rfl⟩ : syracuseStep 10935395 = 16403093) B16403093
theorem B9223409 : Blo 1705053 9223409 := bstep (se 2 (by rfl) ⟨3458778, by rfl⟩ : syracuseStep 9223409 = 6917557) B6917557
theorem B7290161 : Blo 1705053 7290161 := bstep (se 2 (by rfl) ⟨2733810, by rfl⟩ : syracuseStep 7290161 = 5467621) B5467621
theorem B5758289 : Blo 1705053 5758289 := bstep (se 2 (by rfl) ⟨2159358, by rfl⟩ : syracuseStep 5758289 = 4318717) B4318717
theorem B4316561 : Blo 1705053 4316561 := bstep (se 2 (by rfl) ⟨1618710, by rfl⟩ : syracuseStep 4316561 = 3237421) B3237421
theorem B4316611 : Blo 1705053 4316611 := bstep (se 1 (by rfl) ⟨3237458, by rfl⟩ : syracuseStep 4316611 = 6474917) B6474917
theorem B3644995 : Blo 1705053 3644995 := bstep (se 1 (by rfl) ⟨2733746, by rfl⟩ : syracuseStep 3644995 = 5467493) B5467493
theorem B4316753 : Blo 1705053 4316753 := bstep (se 2 (by rfl) ⟨1618782, by rfl⟩ : syracuseStep 4316753 = 3237565) B3237565
theorem B6479459 : Blo 1705053 6479459 := bstep (se 1 (by rfl) ⟨4859594, by rfl⟩ : syracuseStep 6479459 = 9719189) B9719189
theorem B6479473 : Blo 1705053 6479473 := bstep (se 2 (by rfl) ⟨2429802, by rfl⟩ : syracuseStep 6479473 = 4859605) B4859605
theorem B3645251 : Blo 1705053 3645251 := bstep (se 1 (by rfl) ⟨2733938, by rfl⟩ : syracuseStep 3645251 = 5467877) B5467877
theorem B5758829 : Blo 1705053 5758829 := bstep (se 3 (by rfl) ⟨1079780, by rfl⟩ : syracuseStep 5758829 = 2159561) B2159561
theorem B82968461 : Blo 1705053 82968461 := bstep (se 3 (by rfl) ⟨15556586, by rfl⟩ : syracuseStep 82968461 = 31113173) B31113173
theorem B8634275 : Blo 1705053 8634275 := bstep (se 1 (by rfl) ⟨6475706, by rfl⟩ : syracuseStep 8634275 = 12951413) B12951413
theorem B5758883 : Blo 1705053 5758883 := bstep (se 1 (by rfl) ⟨4319162, by rfl⟩ : syracuseStep 5758883 = 8638325) B8638325
theorem B1753099 : Blo 1705053 1753099 := bstep (se 1 (by rfl) ⟨1314824, by rfl⟩ : syracuseStep 1753099 = 2629649) B2629649
theorem B8306705 : Blo 1705053 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B1728587 : Blo 1705053 1728587 := bstep (se 1 (by rfl) ⟨1296440, by rfl⟩ : syracuseStep 1728587 = 2592881) B2592881
theorem B4317259 : Blo 1705053 4317259 := bstep (se 1 (by rfl) ⟨3237944, by rfl⟩ : syracuseStep 4317259 = 6475889) B6475889
theorem B21856331 : Blo 1705053 21856331 := bstep (se 1 (by rfl) ⟨16392248, by rfl⟩ : syracuseStep 21856331 = 32784497) B32784497
theorem B2187415 : Blo 1705053 2187415 := bstep (se 1 (by rfl) ⟨1640561, by rfl⟩ : syracuseStep 2187415 = 3281123) B3281123
theorem B4317401 : Blo 1705053 4317401 := bstep (se 2 (by rfl) ⟨1619025, by rfl⟩ : syracuseStep 4317401 = 3238051) B3238051
theorem B4497995 : Blo 1705053 4497995 := bstep (se 1 (by rfl) ⟨3373496, by rfl⟩ : syracuseStep 4497995 = 6746993) B6746993
theorem B29139587 : Blo 1705053 29139587 := bstep (se 1 (by rfl) ⟨21854690, by rfl⟩ : syracuseStep 29139587 = 43709381) B43709381
theorem B5759639 : Blo 1705053 5759639 := bstep (se 1 (by rfl) ⟨4319729, by rfl⟩ : syracuseStep 5759639 = 8639459) B8639459
theorem B7291595 : Blo 1705053 7291595 := bstep (se 1 (by rfl) ⟨5468696, by rfl⟩ : syracuseStep 7291595 = 10937393) B10937393
theorem B189244117 : Blo 1705053 189244117 := bstep (se 7 (by rfl) ⟨2217704, by rfl⟩ : syracuseStep 189244117 = 4435409) B4435409
theorem B3891929 : Blo 1705053 3891929 := bstep (se 2 (by rfl) ⟨1459473, by rfl⟩ : syracuseStep 3891929 = 2918947) B2918947
theorem B59081525 : Blo 1705053 59081525 := bstep (se 5 (by rfl) ⟨2769446, by rfl⟩ : syracuseStep 59081525 = 5538893) B5538893
theorem B12952385 : Blo 1705053 12952385 := bstep (se 2 (by rfl) ⟨4857144, by rfl⟩ : syracuseStep 12952385 = 9714289) B9714289
theorem B4858717 : Blo 1705053 4858717 := bstep (se 3 (by rfl) ⟨911009, by rfl⟩ : syracuseStep 4858717 = 1822019) B1822019
theorem B4858775 : Blo 1705053 4858775 := bstep (se 1 (by rfl) ⟨3644081, by rfl⟩ : syracuseStep 4858775 = 7288163) B7288163
theorem B3072971 : Blo 1705053 3072971 := bstep (se 1 (by rfl) ⟨2304728, by rfl⟩ : syracuseStep 3072971 = 4609457) B4609457
theorem B8635409 : Blo 1705053 8635409 := bstep (se 2 (by rfl) ⟨3238278, by rfl⟩ : syracuseStep 8635409 = 6476557) B6476557
theorem B4318231 : Blo 1705053 4318231 := bstep (se 1 (by rfl) ⟨3238673, by rfl⟩ : syracuseStep 4318231 = 6477347) B6477347
theorem B1705067 : Blo 1705053 1705067 := bstep (se 1 (by rfl) ⟨1278800, by rfl⟩ : syracuseStep 1705067 = 2557601) B2557601
theorem B1705079 : Blo 1705053 1705079 := bstep (se 1 (by rfl) ⟨1278809, by rfl⟩ : syracuseStep 1705079 = 2557619) B2557619
theorem B1705099 : Blo 1705053 1705099 := bstep (se 1 (by rfl) ⟨1278824, by rfl⟩ : syracuseStep 1705099 = 2557649) B2557649
theorem B1705111 : Blo 1705053 1705111 := bstep (se 1 (by rfl) ⟨1278833, by rfl⟩ : syracuseStep 1705111 = 2557667) B2557667
theorem B1705131 : Blo 1705053 1705131 := bstep (se 1 (by rfl) ⟨1278848, by rfl⟩ : syracuseStep 1705131 = 2557697) B2557697
theorem B8635571 : Blo 1705053 8635571 := bstep (se 1 (by rfl) ⟨6476678, by rfl⟩ : syracuseStep 8635571 = 12953357) B12953357
theorem B5760179 : Blo 1705053 5760179 := bstep (se 1 (by rfl) ⟨4320134, by rfl⟩ : syracuseStep 5760179 = 8640269) B8640269
theorem B1705143 : Blo 1705053 1705143 := bstep (se 1 (by rfl) ⟨1278857, by rfl⟩ : syracuseStep 1705143 = 2557715) B2557715
theorem B1705163 : Blo 1705053 1705163 := bstep (se 1 (by rfl) ⟨1278872, by rfl⟩ : syracuseStep 1705163 = 2557745) B2557745
theorem B3237079 : Blo 1705053 3237079 := bstep (se 1 (by rfl) ⟨2427809, by rfl⟩ : syracuseStep 3237079 = 4855619) B4855619
theorem B1705175 : Blo 1705053 1705175 := bstep (se 1 (by rfl) ⟨1278881, by rfl⟩ : syracuseStep 1705175 = 2557763) B2557763
theorem B1705195 : Blo 1705053 1705195 := bstep (se 1 (by rfl) ⟨1278896, by rfl⟩ : syracuseStep 1705195 = 2557793) B2557793
theorem B1705207 : Blo 1705053 1705207 := bstep (se 1 (by rfl) ⟨1278905, by rfl⟩ : syracuseStep 1705207 = 2557811) B2557811
theorem B1918219 : Blo 1705053 1918219 := bstep (se 1 (by rfl) ⟨1438664, by rfl⟩ : syracuseStep 1918219 = 2877329) B2877329
theorem B1705227 : Blo 1705053 1705227 := bstep (se 1 (by rfl) ⟨1278920, by rfl⟩ : syracuseStep 1705227 = 2557841) B2557841
theorem B8750353 : Blo 1705053 8750353 := bstep (se 2 (by rfl) ⟨3281382, by rfl⟩ : syracuseStep 8750353 = 6562765) B6562765
theorem B1705239 : Blo 1705053 1705239 := bstep (se 1 (by rfl) ⟨1278929, by rfl⟩ : syracuseStep 1705239 = 2557859) B2557859
theorem B1705259 : Blo 1705053 1705259 := bstep (se 1 (by rfl) ⟨1278944, by rfl⟩ : syracuseStep 1705259 = 2557889) B2557889
theorem B1705271 : Blo 1705053 1705271 := bstep (se 1 (by rfl) ⟨1278953, by rfl⟩ : syracuseStep 1705271 = 2557907) B2557907
theorem B3237185 : Blo 1705053 3237185 := bstep (se 2 (by rfl) ⟨1213944, by rfl⟩ : syracuseStep 3237185 = 2427889) B2427889
theorem B1705291 : Blo 1705053 1705291 := bstep (se 1 (by rfl) ⟨1278968, by rfl⟩ : syracuseStep 1705291 = 2557937) B2557937
theorem B1705303 : Blo 1705053 1705303 := bstep (se 1 (by rfl) ⟨1278977, by rfl⟩ : syracuseStep 1705303 = 2557955) B2557955
theorem B1705323 : Blo 1705053 1705323 := bstep (se 1 (by rfl) ⟨1278992, by rfl⟩ : syracuseStep 1705323 = 2557985) B2557985
theorem B1918327 : Blo 1705053 1918327 := bstep (se 1 (by rfl) ⟨1438745, by rfl⟩ : syracuseStep 1918327 = 2877491) B2877491
theorem B1705335 : Blo 1705053 1705335 := bstep (se 1 (by rfl) ⟨1279001, by rfl⟩ : syracuseStep 1705335 = 2558003) B2558003
theorem B14566787 : Blo 1705053 14566787 := bstep (se 1 (by rfl) ⟨10925090, by rfl⟩ : syracuseStep 14566787 = 21850181) B21850181
theorem B1705355 : Blo 1705053 1705355 := bstep (se 1 (by rfl) ⟨1279016, by rfl⟩ : syracuseStep 1705355 = 2558033) B2558033
theorem B7284113 : Blo 1705053 7284113 := bstep (se 2 (by rfl) ⟨2731542, by rfl⟩ : syracuseStep 7284113 = 5463085) B5463085
theorem B1705367 : Blo 1705053 1705367 := bstep (se 1 (by rfl) ⟨1279025, by rfl⟩ : syracuseStep 1705367 = 2558051) B2558051
theorem B1705387 : Blo 1705053 1705387 := bstep (se 1 (by rfl) ⟨1279040, by rfl⟩ : syracuseStep 1705387 = 2558081) B2558081
theorem B1705399 : Blo 1705053 1705399 := bstep (se 1 (by rfl) ⟨1279049, by rfl⟩ : syracuseStep 1705399 = 2558099) B2558099
theorem B5760449 : Blo 1705053 5760449 := bstep (se 2 (by rfl) ⟨2160168, by rfl⟩ : syracuseStep 5760449 = 4320337) B4320337
theorem B1705419 : Blo 1705053 1705419 := bstep (se 1 (by rfl) ⟨1279064, by rfl⟩ : syracuseStep 1705419 = 2558129) B2558129
theorem B4318667 : Blo 1705053 4318667 := bstep (se 1 (by rfl) ⟨3239000, by rfl⟩ : syracuseStep 4318667 = 6478001) B6478001
theorem B1705431 : Blo 1705053 1705431 := bstep (se 1 (by rfl) ⟨1279073, by rfl⟩ : syracuseStep 1705431 = 2558147) B2558147
theorem B3237337 : Blo 1705053 3237337 := bstep (se 2 (by rfl) ⟨1214001, by rfl⟩ : syracuseStep 3237337 = 2428003) B2428003
theorem B1705451 : Blo 1705053 1705451 := bstep (se 1 (by rfl) ⟨1279088, by rfl⟩ : syracuseStep 1705451 = 2558177) B2558177
theorem B1705463 : Blo 1705053 1705463 := bstep (se 1 (by rfl) ⟨1279097, by rfl⟩ : syracuseStep 1705463 = 2558195) B2558195
theorem B1705483 : Blo 1705053 1705483 := bstep (se 1 (by rfl) ⟨1279112, by rfl⟩ : syracuseStep 1705483 = 2558225) B2558225
theorem B41502221 : Blo 1705053 41502221 := bstep (se 3 (by rfl) ⟨7781666, by rfl⟩ : syracuseStep 41502221 = 15563333) B15563333
theorem B1705495 : Blo 1705053 1705495 := bstep (se 1 (by rfl) ⟨1279121, by rfl⟩ : syracuseStep 1705495 = 2558243) B2558243
theorem B1918507 : Blo 1705053 1918507 := bstep (se 1 (by rfl) ⟨1438880, by rfl⟩ : syracuseStep 1918507 = 2877761) B2877761
theorem B1705515 : Blo 1705053 1705515 := bstep (se 1 (by rfl) ⟨1279136, by rfl⟩ : syracuseStep 1705515 = 2558273) B2558273
theorem B1705527 : Blo 1705053 1705527 := bstep (se 1 (by rfl) ⟨1279145, by rfl⟩ : syracuseStep 1705527 = 2558291) B2558291
theorem B1705547 : Blo 1705053 1705547 := bstep (se 1 (by rfl) ⟨1279160, by rfl⟩ : syracuseStep 1705547 = 2558321) B2558321
theorem B1705559 : Blo 1705053 1705559 := bstep (se 1 (by rfl) ⟨1279169, by rfl⟩ : syracuseStep 1705559 = 2558339) B2558339
theorem B6145625 : Blo 1705053 6145625 := bstep (se 2 (by rfl) ⟨2304609, by rfl⟩ : syracuseStep 6145625 = 4609219) B4609219
theorem B1705579 : Blo 1705053 1705579 := bstep (se 1 (by rfl) ⟨1279184, by rfl⟩ : syracuseStep 1705579 = 2558369) B2558369
theorem B1705591 : Blo 1705053 1705591 := bstep (se 1 (by rfl) ⟨1279193, by rfl⟩ : syracuseStep 1705591 = 2558387) B2558387
theorem B1705611 : Blo 1705053 1705611 := bstep (se 1 (by rfl) ⟨1279208, by rfl⟩ : syracuseStep 1705611 = 2558417) B2558417
theorem B1918615 : Blo 1705053 1918615 := bstep (se 1 (by rfl) ⟨1438961, by rfl⟩ : syracuseStep 1918615 = 2877923) B2877923
theorem B1705623 : Blo 1705053 1705623 := bstep (se 1 (by rfl) ⟨1279217, by rfl⟩ : syracuseStep 1705623 = 2558435) B2558435
theorem B26633879 : Blo 1705053 26633879 := bstep (se 1 (by rfl) ⟨19975409, by rfl⟩ : syracuseStep 26633879 = 39950819) B39950819
theorem B1705643 : Blo 1705053 1705643 := bstep (se 1 (by rfl) ⟨1279232, by rfl⟩ : syracuseStep 1705643 = 2558465) B2558465
theorem B1705655 : Blo 1705053 1705655 := bstep (se 1 (by rfl) ⟨1279241, by rfl⟩ : syracuseStep 1705655 = 2558483) B2558483
theorem B2557643 : Blo 1705053 2557643 := bstep (se 1 (by rfl) ⟨1918232, by rfl⟩ : syracuseStep 2557643 = 3836465) B3836465
theorem B1705675 : Blo 1705053 1705675 := bstep (se 1 (by rfl) ⟨1279256, by rfl⟩ : syracuseStep 1705675 = 2558513) B2558513
theorem B2557655 : Blo 1705053 2557655 := bstep (se 1 (by rfl) ⟨1918241, by rfl⟩ : syracuseStep 2557655 = 3836483) B3836483
theorem B1705687 : Blo 1705053 1705687 := bstep (se 1 (by rfl) ⟨1279265, by rfl⟩ : syracuseStep 1705687 = 2558531) B2558531
theorem B1705707 : Blo 1705053 1705707 := bstep (se 1 (by rfl) ⟨1279280, by rfl⟩ : syracuseStep 1705707 = 2558561) B2558561
theorem B1705719 : Blo 1705053 1705719 := bstep (se 1 (by rfl) ⟨1279289, by rfl⟩ : syracuseStep 1705719 = 2558579) B2558579
theorem B1705739 : Blo 1705053 1705739 := bstep (se 1 (by rfl) ⟨1279304, by rfl⟩ : syracuseStep 1705739 = 2558609) B2558609
theorem B1705751 : Blo 1705053 1705751 := bstep (se 1 (by rfl) ⟨1279313, by rfl⟩ : syracuseStep 1705751 = 2558627) B2558627
theorem B2557721 : Blo 1705053 2557721 := bstep (se 2 (by rfl) ⟨959145, by rfl⟩ : syracuseStep 2557721 = 1918291) B1918291
theorem B1705771 : Blo 1705053 1705771 := bstep (se 1 (by rfl) ⟨1279328, by rfl⟩ : syracuseStep 1705771 = 2558657) B2558657
theorem B1705783 : Blo 1705053 1705783 := bstep (se 1 (by rfl) ⟨1279337, by rfl⟩ : syracuseStep 1705783 = 2558675) B2558675
theorem B6915905 : Blo 1705053 6915905 := bstep (se 2 (by rfl) ⟨2593464, by rfl⟩ : syracuseStep 6915905 = 5186929) B5186929
theorem B4319041 : Blo 1705053 4319041 := bstep (se 2 (by rfl) ⟨1619640, by rfl⟩ : syracuseStep 4319041 = 3239281) B3239281
theorem B1918795 : Blo 1705053 1918795 := bstep (se 1 (by rfl) ⟨1439096, by rfl⟩ : syracuseStep 1918795 = 2878193) B2878193
theorem B1705803 : Blo 1705053 1705803 := bstep (se 1 (by rfl) ⟨1279352, by rfl⟩ : syracuseStep 1705803 = 2558705) B2558705
theorem B1705815 : Blo 1705053 1705815 := bstep (se 1 (by rfl) ⟨1279361, by rfl⟩ : syracuseStep 1705815 = 2558723) B2558723
theorem B1705835 : Blo 1705053 1705835 := bstep (se 1 (by rfl) ⟨1279376, by rfl⟩ : syracuseStep 1705835 = 2558753) B2558753
theorem B1705847 : Blo 1705053 1705847 := bstep (se 1 (by rfl) ⟨1279385, by rfl⟩ : syracuseStep 1705847 = 2558771) B2558771
theorem B2557835 : Blo 1705053 2557835 := bstep (se 1 (by rfl) ⟨1918376, by rfl⟩ : syracuseStep 2557835 = 3836753) B3836753
theorem B1705867 : Blo 1705053 1705867 := bstep (se 1 (by rfl) ⟨1279400, by rfl⟩ : syracuseStep 1705867 = 2558801) B2558801
theorem B2557847 : Blo 1705053 2557847 := bstep (se 1 (by rfl) ⟨1918385, by rfl⟩ : syracuseStep 2557847 = 3836771) B3836771
theorem B1705879 : Blo 1705053 1705879 := bstep (se 1 (by rfl) ⟨1279409, by rfl⟩ : syracuseStep 1705879 = 2558819) B2558819
theorem B3073945 : Blo 1705053 3073945 := bstep (se 2 (by rfl) ⟨1152729, by rfl⟩ : syracuseStep 3073945 = 2305459) B2305459
theorem B1705899 : Blo 1705053 1705899 := bstep (se 1 (by rfl) ⟨1279424, by rfl⟩ : syracuseStep 1705899 = 2558849) B2558849
theorem B1918903 : Blo 1705053 1918903 := bstep (se 1 (by rfl) ⟨1439177, by rfl⟩ : syracuseStep 1918903 = 2878355) B2878355
theorem B1705911 : Blo 1705053 1705911 := bstep (se 1 (by rfl) ⟨1279433, by rfl⟩ : syracuseStep 1705911 = 2558867) B2558867
theorem B1705931 : Blo 1705053 1705931 := bstep (se 1 (by rfl) ⟨1279448, by rfl⟩ : syracuseStep 1705931 = 2558897) B2558897
theorem B1705943 : Blo 1705053 1705943 := bstep (se 1 (by rfl) ⟨1279457, by rfl⟩ : syracuseStep 1705943 = 2558915) B2558915
theorem B2557913 : Blo 1705053 2557913 := bstep (se 2 (by rfl) ⟨959217, by rfl⟩ : syracuseStep 2557913 = 1918435) B1918435
theorem B5760989 : Blo 1705053 5760989 := bstep (se 3 (by rfl) ⟨1080185, by rfl⟩ : syracuseStep 5760989 = 2160371) B2160371
theorem B1705963 : Blo 1705053 1705963 := bstep (se 1 (by rfl) ⟨1279472, by rfl⟩ : syracuseStep 1705963 = 2558945) B2558945
theorem B1705975 : Blo 1705053 1705975 := bstep (se 1 (by rfl) ⟨1279481, by rfl⟩ : syracuseStep 1705975 = 2558963) B2558963
theorem B1705995 : Blo 1705053 1705995 := bstep (se 1 (by rfl) ⟨1279496, by rfl⟩ : syracuseStep 1705995 = 2558993) B2558993
theorem B1706007 : Blo 1705053 1706007 := bstep (se 1 (by rfl) ⟨1279505, by rfl⟩ : syracuseStep 1706007 = 2559011) B2559011
theorem B1706027 : Blo 1705053 1706027 := bstep (se 1 (by rfl) ⟨1279520, by rfl⟩ : syracuseStep 1706027 = 2559041) B2559041
theorem B1706039 : Blo 1705053 1706039 := bstep (se 1 (by rfl) ⟨1279529, by rfl⟩ : syracuseStep 1706039 = 2559059) B2559059
theorem B2558027 : Blo 1705053 2558027 := bstep (se 1 (by rfl) ⟨1918520, by rfl⟩ : syracuseStep 2558027 = 3837041) B3837041
theorem B1706059 : Blo 1705053 1706059 := bstep (se 1 (by rfl) ⟨1279544, by rfl⟩ : syracuseStep 1706059 = 2559089) B2559089
theorem B2558039 : Blo 1705053 2558039 := bstep (se 1 (by rfl) ⟨1918529, by rfl⟩ : syracuseStep 2558039 = 3837059) B3837059
theorem B1706071 : Blo 1705053 1706071 := bstep (se 1 (by rfl) ⟨1279553, by rfl⟩ : syracuseStep 1706071 = 2559107) B2559107
theorem B4859993 : Blo 1705053 4859993 := bstep (se 2 (by rfl) ⟨1822497, by rfl⟩ : syracuseStep 4859993 = 3644995) B3644995
theorem B7284829 : Blo 1705053 7284829 := bstep (se 3 (by rfl) ⟨1365905, by rfl⟩ : syracuseStep 7284829 = 2731811) B2731811
theorem B1919083 : Blo 1705053 1919083 := bstep (se 1 (by rfl) ⟨1439312, by rfl⟩ : syracuseStep 1919083 = 2878625) B2878625
theorem B1706091 : Blo 1705053 1706091 := bstep (se 1 (by rfl) ⟨1279568, by rfl⟩ : syracuseStep 1706091 = 2559137) B2559137
theorem B1706103 : Blo 1705053 1706103 := bstep (se 1 (by rfl) ⟨1279577, by rfl⟩ : syracuseStep 1706103 = 2559155) B2559155
theorem B1706123 : Blo 1705053 1706123 := bstep (se 1 (by rfl) ⟨1279592, by rfl⟩ : syracuseStep 1706123 = 2559185) B2559185
theorem B2771083 : Blo 1705053 2771083 := bstep (se 1 (by rfl) ⟨2078312, by rfl⟩ : syracuseStep 2771083 = 4156625) B4156625
theorem B1706135 : Blo 1705053 1706135 := bstep (se 1 (by rfl) ⟨1279601, by rfl⟩ : syracuseStep 1706135 = 2559203) B2559203
theorem B2558105 : Blo 1705053 2558105 := bstep (se 2 (by rfl) ⟨959289, by rfl⟩ : syracuseStep 2558105 = 1918579) B1918579
theorem B1706155 : Blo 1705053 1706155 := bstep (se 1 (by rfl) ⟨1279616, by rfl⟩ : syracuseStep 1706155 = 2559233) B2559233
theorem B1706167 : Blo 1705053 1706167 := bstep (se 1 (by rfl) ⟨1279625, by rfl⟩ : syracuseStep 1706167 = 2559251) B2559251
theorem B1706187 : Blo 1705053 1706187 := bstep (se 1 (by rfl) ⟨1279640, by rfl⟩ : syracuseStep 1706187 = 2559281) B2559281
theorem B4860107 : Blo 1705053 4860107 := bstep (se 1 (by rfl) ⟨3645080, by rfl⟩ : syracuseStep 4860107 = 7290161) B7290161
theorem B1919191 : Blo 1705053 1919191 := bstep (se 1 (by rfl) ⟨1439393, by rfl⟩ : syracuseStep 1919191 = 2878787) B2878787
theorem B1706199 : Blo 1705053 1706199 := bstep (se 1 (by rfl) ⟨1279649, by rfl⟩ : syracuseStep 1706199 = 2559299) B2559299
theorem B6473945 : Blo 1705053 6473945 := bstep (se 2 (by rfl) ⟨2427729, by rfl⟩ : syracuseStep 6473945 = 4855459) B4855459
theorem B1706219 : Blo 1705053 1706219 := bstep (se 1 (by rfl) ⟨1279664, by rfl⟩ : syracuseStep 1706219 = 2559329) B2559329
theorem B1706231 : Blo 1705053 1706231 := bstep (se 1 (by rfl) ⟨1279673, by rfl⟩ : syracuseStep 1706231 = 2559347) B2559347
theorem B2877707 : Blo 1705053 2877707 := bstep (se 1 (by rfl) ⟨2158280, by rfl⟩ : syracuseStep 2877707 = 4316561) B4316561
theorem B2558219 : Blo 1705053 2558219 := bstep (se 1 (by rfl) ⟨1918664, by rfl⟩ : syracuseStep 2558219 = 3837329) B3837329
theorem B1706251 : Blo 1705053 1706251 := bstep (se 1 (by rfl) ⟨1279688, by rfl⟩ : syracuseStep 1706251 = 2559377) B2559377
theorem B2558231 : Blo 1705053 2558231 := bstep (se 1 (by rfl) ⟨1918673, by rfl⟩ : syracuseStep 2558231 = 3837347) B3837347
theorem B1706263 : Blo 1705053 1706263 := bstep (se 1 (by rfl) ⟨1279697, by rfl⟩ : syracuseStep 1706263 = 2559395) B2559395
theorem B1706283 : Blo 1705053 1706283 := bstep (se 1 (by rfl) ⟨1279712, by rfl⟩ : syracuseStep 1706283 = 2559425) B2559425
theorem B1706295 : Blo 1705053 1706295 := bstep (se 1 (by rfl) ⟨1279721, by rfl⟩ : syracuseStep 1706295 = 2559443) B2559443
theorem B1706315 : Blo 1705053 1706315 := bstep (se 1 (by rfl) ⟨1279736, by rfl⟩ : syracuseStep 1706315 = 2559473) B2559473
theorem B1706327 : Blo 1705053 1706327 := bstep (se 1 (by rfl) ⟨1279745, by rfl⟩ : syracuseStep 1706327 = 2559491) B2559491
theorem B2558297 : Blo 1705053 2558297 := bstep (se 2 (by rfl) ⟨959361, by rfl⟩ : syracuseStep 2558297 = 1918723) B1918723
theorem B1706347 : Blo 1705053 1706347 := bstep (se 1 (by rfl) ⟨1279760, by rfl⟩ : syracuseStep 1706347 = 2559521) B2559521
theorem B1706359 : Blo 1705053 1706359 := bstep (se 1 (by rfl) ⟨1279769, by rfl⟩ : syracuseStep 1706359 = 2559539) B2559539
theorem B2877835 : Blo 1705053 2877835 := bstep (se 1 (by rfl) ⟨2158376, by rfl⟩ : syracuseStep 2877835 = 4316753) B4316753
theorem B1919371 : Blo 1705053 1919371 := bstep (se 1 (by rfl) ⟨1439528, by rfl⟩ : syracuseStep 1919371 = 2879057) B2879057
theorem B1706379 : Blo 1705053 1706379 := bstep (se 1 (by rfl) ⟨1279784, by rfl⟩ : syracuseStep 1706379 = 2559569) B2559569
theorem B1706391 : Blo 1705053 1706391 := bstep (se 1 (by rfl) ⟨1279793, by rfl⟩ : syracuseStep 1706391 = 2559587) B2559587
theorem B4319639 : Blo 1705053 4319639 := bstep (se 1 (by rfl) ⟨3239729, by rfl⟩ : syracuseStep 4319639 = 6479459) B6479459
theorem B1706411 : Blo 1705053 1706411 := bstep (se 1 (by rfl) ⟨1279808, by rfl⟩ : syracuseStep 1706411 = 2559617) B2559617
theorem B14977457 : Blo 1705053 14977457 := bstep (se 2 (by rfl) ⟨5616546, by rfl⟩ : syracuseStep 14977457 = 11233093) B11233093
theorem B1706423 : Blo 1705053 1706423 := bstep (se 1 (by rfl) ⟨1279817, by rfl⟩ : syracuseStep 1706423 = 2559635) B2559635
theorem B2558411 : Blo 1705053 2558411 := bstep (se 1 (by rfl) ⟨1918808, by rfl⟩ : syracuseStep 2558411 = 3837617) B3837617
theorem B1706443 : Blo 1705053 1706443 := bstep (se 1 (by rfl) ⟨1279832, by rfl⟩ : syracuseStep 1706443 = 2559665) B2559665
theorem B3836375 : Blo 1705053 3836375 := bstep (se 1 (by rfl) ⟨2877281, by rfl⟩ : syracuseStep 3836375 = 5754563) B5754563
theorem B2558423 : Blo 1705053 2558423 := bstep (se 1 (by rfl) ⟨1918817, by rfl⟩ : syracuseStep 2558423 = 3837635) B3837635
theorem B1706455 : Blo 1705053 1706455 := bstep (se 1 (by rfl) ⟨1279841, by rfl⟩ : syracuseStep 1706455 = 2559683) B2559683
theorem B1706475 : Blo 1705053 1706475 := bstep (se 1 (by rfl) ⟨1279856, by rfl⟩ : syracuseStep 1706475 = 2559713) B2559713
theorem B1919479 : Blo 1705053 1919479 := bstep (se 1 (by rfl) ⟨1439609, by rfl⟩ : syracuseStep 1919479 = 2879219) B2879219
theorem B1706487 : Blo 1705053 1706487 := bstep (se 1 (by rfl) ⟨1279865, by rfl⟩ : syracuseStep 1706487 = 2559731) B2559731
theorem B1706507 : Blo 1705053 1706507 := bstep (se 1 (by rfl) ⟨1279880, by rfl⟩ : syracuseStep 1706507 = 2559761) B2559761
theorem B32786957 : Blo 1705053 32786957 := bstep (se 3 (by rfl) ⟨6147554, by rfl⟩ : syracuseStep 32786957 = 12295109) B12295109
theorem B1706519 : Blo 1705053 1706519 := bstep (se 1 (by rfl) ⟨1279889, by rfl⟩ : syracuseStep 1706519 = 2559779) B2559779
theorem B2877977 : Blo 1705053 2877977 := bstep (se 2 (by rfl) ⟨1079241, by rfl⟩ : syracuseStep 2877977 = 2158483) B2158483
theorem B2558489 : Blo 1705053 2558489 := bstep (se 2 (by rfl) ⟨959433, by rfl⟩ : syracuseStep 2558489 = 1918867) B1918867
theorem B1706539 : Blo 1705053 1706539 := bstep (se 1 (by rfl) ⟨1279904, by rfl⟩ : syracuseStep 1706539 = 2559809) B2559809
theorem B1706551 : Blo 1705053 1706551 := bstep (se 1 (by rfl) ⟨1279913, by rfl⟩ : syracuseStep 1706551 = 2559827) B2559827
theorem B1706571 : Blo 1705053 1706571 := bstep (se 1 (by rfl) ⟨1279928, by rfl⟩ : syracuseStep 1706571 = 2559857) B2559857
theorem B1706583 : Blo 1705053 1706583 := bstep (se 1 (by rfl) ⟨1279937, by rfl⟩ : syracuseStep 1706583 = 2559875) B2559875
theorem B2919001 : Blo 1705053 2919001 := bstep (se 2 (by rfl) ⟨1094625, by rfl⟩ : syracuseStep 2919001 = 2189251) B2189251
theorem B1706603 : Blo 1705053 1706603 := bstep (se 1 (by rfl) ⟨1279952, by rfl⟩ : syracuseStep 1706603 = 2559905) B2559905
theorem B1706615 : Blo 1705053 1706615 := bstep (se 1 (by rfl) ⟨1279961, by rfl⟩ : syracuseStep 1706615 = 2559923) B2559923
theorem B3836555 : Blo 1705053 3836555 := bstep (se 1 (by rfl) ⟨2877416, by rfl⟩ : syracuseStep 3836555 = 5754833) B5754833
theorem B1821323 : Blo 1705053 1821323 := bstep (se 1 (by rfl) ⟨1365992, by rfl⟩ : syracuseStep 1821323 = 2731985) B2731985
theorem B2558603 : Blo 1705053 2558603 := bstep (se 1 (by rfl) ⟨1918952, by rfl⟩ : syracuseStep 2558603 = 3837905) B3837905
theorem B1706635 : Blo 1705053 1706635 := bstep (se 1 (by rfl) ⟨1279976, by rfl⟩ : syracuseStep 1706635 = 2559953) B2559953
theorem B2558615 : Blo 1705053 2558615 := bstep (se 1 (by rfl) ⟨1918961, by rfl⟩ : syracuseStep 2558615 = 3837923) B3837923
theorem B1706647 : Blo 1705053 1706647 := bstep (se 1 (by rfl) ⟨1279985, by rfl⟩ : syracuseStep 1706647 = 2559971) B2559971
theorem B2878105 : Blo 1705053 2878105 := bstep (se 2 (by rfl) ⟨1079289, by rfl⟩ : syracuseStep 2878105 = 2158579) B2158579
theorem B1919659 : Blo 1705053 1919659 := bstep (se 1 (by rfl) ⟨1439744, by rfl⟩ : syracuseStep 1919659 = 2879489) B2879489
theorem B1706667 : Blo 1705053 1706667 := bstep (se 1 (by rfl) ⟨1280000, by rfl⟩ : syracuseStep 1706667 = 2560001) B2560001
theorem B1706679 : Blo 1705053 1706679 := bstep (se 1 (by rfl) ⟨1280009, by rfl⟩ : syracuseStep 1706679 = 2560019) B2560019
theorem B3836609 : Blo 1705053 3836609 := bstep (se 2 (by rfl) ⟨1438728, by rfl⟩ : syracuseStep 3836609 = 2877457) B2877457
theorem B1706699 : Blo 1705053 1706699 := bstep (se 1 (by rfl) ⟨1280024, by rfl⟩ : syracuseStep 1706699 = 2560049) B2560049
theorem B1706711 : Blo 1705053 1706711 := bstep (se 1 (by rfl) ⟨1280033, by rfl⟩ : syracuseStep 1706711 = 2560067) B2560067
theorem B2558681 : Blo 1705053 2558681 := bstep (se 2 (by rfl) ⟨959505, by rfl⟩ : syracuseStep 2558681 = 1919011) B1919011
theorem B12954329 : Blo 1705053 12954329 := bstep (se 2 (by rfl) ⟨4857873, by rfl⟩ : syracuseStep 12954329 = 9715747) B9715747
theorem B1706731 : Blo 1705053 1706731 := bstep (se 1 (by rfl) ⟨1280048, by rfl⟩ : syracuseStep 1706731 = 2560097) B2560097
theorem B3238643 : Blo 1705053 3238643 := bstep (se 1 (by rfl) ⟨2428982, by rfl⟩ : syracuseStep 3238643 = 4857965) B4857965
theorem B1706743 : Blo 1705053 1706743 := bstep (se 1 (by rfl) ⟨1280057, by rfl⟩ : syracuseStep 1706743 = 2560115) B2560115
theorem B1706763 : Blo 1705053 1706763 := bstep (se 1 (by rfl) ⟨1280072, by rfl⟩ : syracuseStep 1706763 = 2560145) B2560145
theorem B1846039 : Blo 1705053 1846039 := bstep (se 1 (by rfl) ⟨1384529, by rfl⟩ : syracuseStep 1846039 = 2769059) B2769059
theorem B1919767 : Blo 1705053 1919767 := bstep (se 1 (by rfl) ⟨1439825, by rfl⟩ : syracuseStep 1919767 = 2879651) B2879651
theorem B1706775 : Blo 1705053 1706775 := bstep (se 1 (by rfl) ⟨1280081, by rfl⟩ : syracuseStep 1706775 = 2560163) B2560163
theorem B1706795 : Blo 1705053 1706795 := bstep (se 1 (by rfl) ⟨1280096, by rfl⟩ : syracuseStep 1706795 = 2560193) B2560193
theorem B1706807 : Blo 1705053 1706807 := bstep (se 1 (by rfl) ⟨1280105, by rfl⟩ : syracuseStep 1706807 = 2560211) B2560211
theorem B2558795 : Blo 1705053 2558795 := bstep (se 1 (by rfl) ⟨1919096, by rfl⟩ : syracuseStep 2558795 = 3838193) B3838193
theorem B1706827 : Blo 1705053 1706827 := bstep (se 1 (by rfl) ⟨1280120, by rfl⟩ : syracuseStep 1706827 = 2560241) B2560241
theorem B2558807 : Blo 1705053 2558807 := bstep (se 1 (by rfl) ⟨1919105, by rfl⟩ : syracuseStep 2558807 = 3838211) B3838211
theorem B1706839 : Blo 1705053 1706839 := bstep (se 1 (by rfl) ⟨1280129, by rfl⟩ : syracuseStep 1706839 = 2560259) B2560259
theorem B1706859 : Blo 1705053 1706859 := bstep (se 1 (by rfl) ⟨1280144, by rfl⟩ : syracuseStep 1706859 = 2560289) B2560289
theorem B1706871 : Blo 1705053 1706871 := bstep (se 1 (by rfl) ⟨1280153, by rfl⟩ : syracuseStep 1706871 = 2560307) B2560307
theorem B3238795 : Blo 1705053 3238795 := bstep (se 1 (by rfl) ⟨2429096, by rfl⟩ : syracuseStep 3238795 = 4858193) B4858193
theorem B1706891 : Blo 1705053 1706891 := bstep (se 1 (by rfl) ⟨1280168, by rfl⟩ : syracuseStep 1706891 = 2560337) B2560337
theorem B1706903 : Blo 1705053 1706903 := bstep (se 1 (by rfl) ⟨1280177, by rfl⟩ : syracuseStep 1706903 = 2560355) B2560355
theorem B3836825 : Blo 1705053 3836825 := bstep (se 2 (by rfl) ⟨1438809, by rfl⟩ : syracuseStep 3836825 = 2877619) B2877619
theorem B2558873 : Blo 1705053 2558873 := bstep (se 2 (by rfl) ⟨959577, by rfl⟩ : syracuseStep 2558873 = 1919155) B1919155
theorem B1706923 : Blo 1705053 1706923 := bstep (se 1 (by rfl) ⟨1280192, by rfl⟩ : syracuseStep 1706923 = 2560385) B2560385
theorem B1706935 : Blo 1705053 1706935 := bstep (se 1 (by rfl) ⟨1280201, by rfl⟩ : syracuseStep 1706935 = 2560403) B2560403
theorem B1919947 : Blo 1705053 1919947 := bstep (se 1 (by rfl) ⟨1439960, by rfl⟩ : syracuseStep 1919947 = 2879921) B2879921
theorem B1706955 : Blo 1705053 1706955 := bstep (se 1 (by rfl) ⟨1280216, by rfl⟩ : syracuseStep 1706955 = 2560433) B2560433
theorem B1706967 : Blo 1705053 1706967 := bstep (se 1 (by rfl) ⟨1280225, by rfl⟩ : syracuseStep 1706967 = 2560451) B2560451
theorem B24587225 : Blo 1705053 24587225 := bstep (se 2 (by rfl) ⟨9220209, by rfl⟩ : syracuseStep 24587225 = 18440419) B18440419
theorem B1706987 : Blo 1705053 1706987 := bstep (se 1 (by rfl) ⟨1280240, by rfl⟩ : syracuseStep 1706987 = 2560481) B2560481
theorem B3836915 : Blo 1705053 3836915 := bstep (se 1 (by rfl) ⟨2877686, by rfl⟩ : syracuseStep 3836915 = 5755373) B5755373
theorem B1706999 : Blo 1705053 1706999 := bstep (se 1 (by rfl) ⟨1280249, by rfl⟩ : syracuseStep 1706999 = 2560499) B2560499
theorem B2558987 : Blo 1705053 2558987 := bstep (se 1 (by rfl) ⟨1919240, by rfl⟩ : syracuseStep 2558987 = 3838481) B3838481
theorem B1707019 : Blo 1705053 1707019 := bstep (se 1 (by rfl) ⟨1280264, by rfl⟩ : syracuseStep 1707019 = 2560529) B2560529
theorem B3836951 : Blo 1705053 3836951 := bstep (se 1 (by rfl) ⟨2877713, by rfl⟩ : syracuseStep 3836951 = 5755427) B5755427
theorem B2558999 : Blo 1705053 2558999 := bstep (se 1 (by rfl) ⟨1919249, by rfl⟩ : syracuseStep 2558999 = 3838499) B3838499
theorem B1707031 : Blo 1705053 1707031 := bstep (se 1 (by rfl) ⟨1280273, by rfl⟩ : syracuseStep 1707031 = 2560547) B2560547
theorem B1707051 : Blo 1705053 1707051 := bstep (se 1 (by rfl) ⟨1280288, by rfl⟩ : syracuseStep 1707051 = 2560577) B2560577
theorem B1920055 : Blo 1705053 1920055 := bstep (se 1 (by rfl) ⟨1440041, by rfl⟩ : syracuseStep 1920055 = 2880083) B2880083
theorem B8637515 : Blo 1705053 8637515 := bstep (se 1 (by rfl) ⟨6478136, by rfl⟩ : syracuseStep 8637515 = 12956273) B12956273
theorem B2559065 : Blo 1705053 2559065 := bstep (se 2 (by rfl) ⟨959649, by rfl⟩ : syracuseStep 2559065 = 1919299) B1919299
theorem B4320449 : Blo 1705053 4320449 := bstep (se 2 (by rfl) ⟨1620168, by rfl⟩ : syracuseStep 4320449 = 3240337) B3240337
theorem B3837131 : Blo 1705053 3837131 := bstep (se 1 (by rfl) ⟨2877848, by rfl⟩ : syracuseStep 3837131 = 5755697) B5755697
theorem B2559179 : Blo 1705053 2559179 := bstep (se 1 (by rfl) ⟨1919384, by rfl⟩ : syracuseStep 2559179 = 3838769) B3838769
theorem B2878679 : Blo 1705053 2878679 := bstep (se 1 (by rfl) ⟨2159009, by rfl⟩ : syracuseStep 2878679 = 4318019) B4318019
theorem B2559191 : Blo 1705053 2559191 := bstep (se 1 (by rfl) ⟨1919393, by rfl⟩ : syracuseStep 2559191 = 3838787) B3838787
theorem B3239129 : Blo 1705053 3239129 := bstep (se 2 (by rfl) ⟨1214673, by rfl⟩ : syracuseStep 3239129 = 2429347) B2429347
theorem B1920235 : Blo 1705053 1920235 := bstep (se 1 (by rfl) ⟨1440176, by rfl⟩ : syracuseStep 1920235 = 2880353) B2880353
theorem B3837185 : Blo 1705053 3837185 := bstep (se 2 (by rfl) ⟨1438944, by rfl⟩ : syracuseStep 3837185 = 2877889) B2877889
theorem B3075329 : Blo 1705053 3075329 := bstep (se 2 (by rfl) ⟨1153248, by rfl⟩ : syracuseStep 3075329 = 2306497) B2306497
theorem B2559257 : Blo 1705053 2559257 := bstep (se 2 (by rfl) ⟨959721, by rfl⟩ : syracuseStep 2559257 = 1919443) B1919443
theorem B2878807 : Blo 1705053 2878807 := bstep (se 1 (by rfl) ⟨2159105, by rfl⟩ : syracuseStep 2878807 = 4318211) B4318211
theorem B1920343 : Blo 1705053 1920343 := bstep (se 1 (by rfl) ⟨1440257, by rfl⟩ : syracuseStep 1920343 = 2880515) B2880515
theorem B2559371 : Blo 1705053 2559371 := bstep (se 1 (by rfl) ⟨1919528, by rfl⟩ : syracuseStep 2559371 = 3839057) B3839057
theorem B2559383 : Blo 1705053 2559383 := bstep (se 1 (by rfl) ⟨1919537, by rfl⟩ : syracuseStep 2559383 = 3839075) B3839075
theorem B3837401 : Blo 1705053 3837401 := bstep (se 2 (by rfl) ⟨1439025, by rfl⟩ : syracuseStep 3837401 = 2878051) B2878051
theorem B2559449 : Blo 1705053 2559449 := bstep (se 2 (by rfl) ⟨959793, by rfl⟩ : syracuseStep 2559449 = 1919587) B1919587
theorem B22171153 : Blo 1705053 22171153 := bstep (se 2 (by rfl) ⟨8314182, by rfl⟩ : syracuseStep 22171153 = 16628365) B16628365
theorem B2158103 : Blo 1705053 2158103 := bstep (se 1 (by rfl) ⟨1618577, by rfl⟩ : syracuseStep 2158103 = 3237155) B3237155
theorem B3837491 : Blo 1705053 3837491 := bstep (se 1 (by rfl) ⟨2878118, by rfl⟩ : syracuseStep 3837491 = 5756237) B5756237
theorem B2559563 : Blo 1705053 2559563 := bstep (se 1 (by rfl) ⟨1919672, by rfl⟩ : syracuseStep 2559563 = 3839345) B3839345
theorem B3837527 : Blo 1705053 3837527 := bstep (se 1 (by rfl) ⟨2878145, by rfl⟩ : syracuseStep 3837527 = 5756291) B5756291
theorem B2559575 : Blo 1705053 2559575 := bstep (se 1 (by rfl) ⟨1919681, by rfl⟩ : syracuseStep 2559575 = 3839363) B3839363
theorem B23334493 : Blo 1705053 23334493 := bstep (se 3 (by rfl) ⟨4375217, by rfl⟩ : syracuseStep 23334493 = 8750435) B8750435
theorem B14577245 : Blo 1705053 14577245 := bstep (se 3 (by rfl) ⟨2733233, by rfl⟩ : syracuseStep 14577245 = 5466467) B5466467
theorem B19435139 : Blo 1705053 19435139 := bstep (se 1 (by rfl) ⟨14576354, by rfl⟩ : syracuseStep 19435139 = 29152709) B29152709
theorem B2305675 : Blo 1705053 2305675 := bstep (se 1 (by rfl) ⟨1729256, by rfl⟩ : syracuseStep 2305675 = 3458513) B3458513
theorem B27684503 : Blo 1705053 27684503 := bstep (se 1 (by rfl) ⟨20763377, by rfl⟩ : syracuseStep 27684503 = 41526755) B41526755
theorem B2559641 : Blo 1705053 2559641 := bstep (se 2 (by rfl) ⟨959865, by rfl⟩ : syracuseStep 2559641 = 1919731) B1919731
theorem B3837707 : Blo 1705053 3837707 := bstep (se 1 (by rfl) ⟨2878280, by rfl⟩ : syracuseStep 3837707 = 5756561) B5756561
theorem B2559755 : Blo 1705053 2559755 := bstep (se 1 (by rfl) ⟨1919816, by rfl⟩ : syracuseStep 2559755 = 3839633) B3839633
theorem B2731799 : Blo 1705053 2731799 := bstep (se 1 (by rfl) ⟨2048849, by rfl⟩ : syracuseStep 2731799 = 4097699) B4097699
theorem B2559767 : Blo 1705053 2559767 := bstep (se 1 (by rfl) ⟨1919825, by rfl⟩ : syracuseStep 2559767 = 3839651) B3839651
theorem B6475571 : Blo 1705053 6475571 := bstep (se 1 (by rfl) ⟨4856678, by rfl⟩ : syracuseStep 6475571 = 9713357) B9713357
theorem B6475585 : Blo 1705053 6475585 := bstep (se 2 (by rfl) ⟨2428344, by rfl⟩ : syracuseStep 6475585 = 4856689) B4856689
theorem B3837761 : Blo 1705053 3837761 := bstep (se 2 (by rfl) ⟨1439160, by rfl⟩ : syracuseStep 3837761 = 2878321) B2878321
theorem B5467979 : Blo 1705053 5467979 := bstep (se 1 (by rfl) ⟨4100984, by rfl⟩ : syracuseStep 5467979 = 8201969) B8201969
theorem B3239767 : Blo 1705053 3239767 := bstep (se 1 (by rfl) ⟨2429825, by rfl⟩ : syracuseStep 3239767 = 4859651) B4859651
theorem B2559833 : Blo 1705053 2559833 := bstep (se 2 (by rfl) ⟨959937, by rfl⟩ : syracuseStep 2559833 = 1919875) B1919875
theorem B5836637 : Blo 1705053 5836637 := bstep (se 3 (by rfl) ⟨1094369, by rfl⟩ : syracuseStep 5836637 = 2188739) B2188739
theorem B246271843 : Blo 1705053 246271843 := bstep (se 1 (by rfl) ⟨184703882, by rfl⟩ : syracuseStep 246271843 = 369407765) B369407765
theorem B2428823 : Blo 1705053 2428823 := bstep (se 1 (by rfl) ⟨1821617, by rfl⟩ : syracuseStep 2428823 = 3643235) B3643235
theorem B2879435 : Blo 1705053 2879435 := bstep (se 1 (by rfl) ⟨2159576, by rfl⟩ : syracuseStep 2879435 = 4319153) B4319153
theorem B2559947 : Blo 1705053 2559947 := bstep (se 1 (by rfl) ⟨1919960, by rfl⟩ : syracuseStep 2559947 = 3839921) B3839921
theorem B2559959 : Blo 1705053 2559959 := bstep (se 1 (by rfl) ⟨1919969, by rfl⟩ : syracuseStep 2559959 = 3839939) B3839939
theorem B2461657 : Blo 1705053 2461657 := bstep (se 2 (by rfl) ⟨923121, by rfl⟩ : syracuseStep 2461657 = 1846243) B1846243
theorem B1822711 : Blo 1705053 1822711 := bstep (se 1 (by rfl) ⟨1367033, by rfl⟩ : syracuseStep 1822711 = 2734067) B2734067
theorem B3837977 : Blo 1705053 3837977 := bstep (se 2 (by rfl) ⟨1439241, by rfl⟩ : syracuseStep 3837977 = 2878483) B2878483
theorem B2560025 : Blo 1705053 2560025 := bstep (se 2 (by rfl) ⟨960009, by rfl⟩ : syracuseStep 2560025 = 1920019) B1920019
theorem B2879563 : Blo 1705053 2879563 := bstep (se 1 (by rfl) ⟨2159672, by rfl⟩ : syracuseStep 2879563 = 4319345) B4319345
theorem B504868949 : Blo 1705053 504868949 := bstep (se 8 (by rfl) ⟨2958216, by rfl⟩ : syracuseStep 504868949 = 5916433) B5916433
theorem B3838067 : Blo 1705053 3838067 := bstep (se 1 (by rfl) ⟨2878550, by rfl⟩ : syracuseStep 3838067 = 5757101) B5757101
theorem B9719939 : Blo 1705053 9719939 := bstep (se 1 (by rfl) ⟨7289954, by rfl⟩ : syracuseStep 9719939 = 14579909) B14579909
theorem B2560139 : Blo 1705053 2560139 := bstep (se 1 (by rfl) ⟨1920104, by rfl⟩ : syracuseStep 2560139 = 3840209) B3840209
theorem B3838103 : Blo 1705053 3838103 := bstep (se 1 (by rfl) ⟨2878577, by rfl⟩ : syracuseStep 3838103 = 5757155) B5757155
theorem B2560151 : Blo 1705053 2560151 := bstep (se 1 (by rfl) ⟨1920113, by rfl⟩ : syracuseStep 2560151 = 3840227) B3840227
theorem B2429131 : Blo 1705053 2429131 := bstep (se 1 (by rfl) ⟨1821848, by rfl⟩ : syracuseStep 2429131 = 3643697) B3643697
theorem B2158807 : Blo 1705053 2158807 := bstep (se 1 (by rfl) ⟨1619105, by rfl⟩ : syracuseStep 2158807 = 3238211) B3238211
theorem B2879705 : Blo 1705053 2879705 := bstep (se 2 (by rfl) ⟨1079889, by rfl⟩ : syracuseStep 2879705 = 2159779) B2159779
theorem B2560217 : Blo 1705053 2560217 := bstep (se 2 (by rfl) ⟨960081, by rfl⟩ : syracuseStep 2560217 = 1920163) B1920163
theorem B5755211 : Blo 1705053 5755211 := bstep (se 1 (by rfl) ⟨4316408, by rfl⟩ : syracuseStep 5755211 = 8632817) B8632817
theorem B2732363 : Blo 1705053 2732363 := bstep (se 1 (by rfl) ⟨2049272, by rfl⟩ : syracuseStep 2732363 = 4098545) B4098545
theorem B3838283 : Blo 1705053 3838283 := bstep (se 1 (by rfl) ⟨2878712, by rfl⟩ : syracuseStep 3838283 = 5757425) B5757425
theorem B14577995 : Blo 1705053 14577995 := bstep (se 1 (by rfl) ⟨10933496, by rfl⟩ : syracuseStep 14577995 = 21866993) B21866993
theorem B2560331 : Blo 1705053 2560331 := bstep (se 1 (by rfl) ⟨1920248, by rfl⟩ : syracuseStep 2560331 = 3840497) B3840497
theorem B2560343 : Blo 1705053 2560343 := bstep (se 1 (by rfl) ⟨1920257, by rfl⟩ : syracuseStep 2560343 = 3840515) B3840515
theorem B3641689 : Blo 1705053 3641689 := bstep (se 2 (by rfl) ⟨1365633, by rfl⟩ : syracuseStep 3641689 = 2731267) B2731267
theorem B2879833 : Blo 1705053 2879833 := bstep (se 2 (by rfl) ⟨1079937, by rfl⟩ : syracuseStep 2879833 = 2159875) B2159875
theorem B3838337 : Blo 1705053 3838337 := bstep (se 2 (by rfl) ⟨1439376, by rfl⟩ : syracuseStep 3838337 = 2878753) B2878753
theorem B2560409 : Blo 1705053 2560409 := bstep (se 2 (by rfl) ⟨960153, by rfl⟩ : syracuseStep 2560409 = 1920307) B1920307
theorem B2732503 : Blo 1705053 2732503 := bstep (se 1 (by rfl) ⟨2049377, by rfl⟩ : syracuseStep 2732503 = 4098755) B4098755
theorem B2560523 : Blo 1705053 2560523 := bstep (se 1 (by rfl) ⟨1920392, by rfl⟩ : syracuseStep 2560523 = 3840785) B3840785
theorem B2560535 : Blo 1705053 2560535 := bstep (se 1 (by rfl) ⟨1920401, by rfl⟩ : syracuseStep 2560535 = 3840803) B3840803
theorem B9720395 : Blo 1705053 9720395 := bstep (se 1 (by rfl) ⟨7290296, by rfl⟩ : syracuseStep 9720395 = 14580593) B14580593
theorem B5755481 : Blo 1705053 5755481 := bstep (se 2 (by rfl) ⟨2158305, by rfl⟩ : syracuseStep 5755481 = 4316611) B4316611
theorem B3838553 : Blo 1705053 3838553 := bstep (se 2 (by rfl) ⟨1439457, by rfl⟩ : syracuseStep 3838553 = 2878915) B2878915
theorem B3240587 : Blo 1705053 3240587 := bstep (se 1 (by rfl) ⟨2430440, by rfl⟩ : syracuseStep 3240587 = 4860881) B4860881
theorem B2306713 : Blo 1705053 2306713 := bstep (se 2 (by rfl) ⟨865017, by rfl⟩ : syracuseStep 2306713 = 1730035) B1730035
theorem B3838643 : Blo 1705053 3838643 := bstep (se 1 (by rfl) ⟨2878982, by rfl⟩ : syracuseStep 3838643 = 5757965) B5757965
theorem B3240641 : Blo 1705053 3240641 := bstep (se 2 (by rfl) ⟨1215240, by rfl⟩ : syracuseStep 3240641 = 2430481) B2430481
theorem B6148811 : Blo 1705053 6148811 := bstep (se 1 (by rfl) ⟨4611608, by rfl⟩ : syracuseStep 6148811 = 9223217) B9223217
theorem B3838679 : Blo 1705053 3838679 := bstep (se 1 (by rfl) ⟨2879009, by rfl⟩ : syracuseStep 3838679 = 5758019) B5758019
theorem B8639297 : Blo 1705053 8639297 := bstep (se 2 (by rfl) ⟨3239736, by rfl⟩ : syracuseStep 8639297 = 6479473) B6479473
theorem B6148939 : Blo 1705053 6148939 := bstep (se 1 (by rfl) ⟨4611704, by rfl⟩ : syracuseStep 6148939 = 9223409) B9223409
theorem B3838859 : Blo 1705053 3838859 := bstep (se 1 (by rfl) ⟨2879144, by rfl⟩ : syracuseStep 3838859 = 5758289) B5758289
theorem B2880407 : Blo 1705053 2880407 := bstep (se 1 (by rfl) ⟨2160305, by rfl⟩ : syracuseStep 2880407 = 4320611) B4320611
theorem B3838913 : Blo 1705053 3838913 := bstep (se 2 (by rfl) ⟨1439592, by rfl⟩ : syracuseStep 3838913 = 2879185) B2879185
theorem B12948497 : Blo 1705053 12948497 := bstep (se 2 (by rfl) ⟨4855686, by rfl⟩ : syracuseStep 12948497 = 9711373) B9711373
theorem B2880535 : Blo 1705053 2880535 := bstep (se 1 (by rfl) ⟨2160401, by rfl⟩ : syracuseStep 2880535 = 4320803) B4320803
theorem B3839129 : Blo 1705053 3839129 := bstep (se 2 (by rfl) ⟨1439673, by rfl⟩ : syracuseStep 3839129 = 2879347) B2879347
theorem B2430167 : Blo 1705053 2430167 := bstep (se 1 (by rfl) ⟨1822625, by rfl⟩ : syracuseStep 2430167 = 3645251) B3645251
theorem B3839219 : Blo 1705053 3839219 := bstep (se 1 (by rfl) ⟨2879414, by rfl⟩ : syracuseStep 3839219 = 5758829) B5758829
theorem B2733323 : Blo 1705053 2733323 := bstep (se 1 (by rfl) ⟨2049992, by rfl⟩ : syracuseStep 2733323 = 4099985) B4099985
theorem B5756183 : Blo 1705053 5756183 := bstep (se 1 (by rfl) ⟨4317137, by rfl⟩ : syracuseStep 5756183 = 8634275) B8634275
theorem B3839255 : Blo 1705053 3839255 := bstep (se 1 (by rfl) ⟨2879441, by rfl⟩ : syracuseStep 3839255 = 5758883) B5758883
theorem B2733401 : Blo 1705053 2733401 := bstep (se 2 (by rfl) ⟨1025025, by rfl⟩ : syracuseStep 2733401 = 2050051) B2050051
theorem B2430361 : Blo 1705053 2430361 := bstep (se 2 (by rfl) ⟨911385, by rfl⟩ : syracuseStep 2430361 = 1822771) B1822771
theorem B7009739 : Blo 1705053 7009739 := bstep (se 1 (by rfl) ⟨5257304, by rfl⟩ : syracuseStep 7009739 = 10514609) B10514609
theorem B3839435 : Blo 1705053 3839435 := bstep (se 1 (by rfl) ⟨2879576, by rfl⟩ : syracuseStep 3839435 = 5759153) B5759153
theorem B3839489 : Blo 1705053 3839489 := bstep (se 2 (by rfl) ⟨1439808, by rfl⟩ : syracuseStep 3839489 = 2879617) B2879617
theorem B10933805 : Blo 1705053 10933805 := bstep (se 3 (by rfl) ⟨2050088, by rfl⟩ : syracuseStep 10933805 = 4100177) B4100177
theorem B7288451 : Blo 1705053 7288451 := bstep (se 1 (by rfl) ⟨5466338, by rfl⟩ : syracuseStep 7288451 = 10932677) B10932677
theorem B4609715 : Blo 1705053 4609715 := bstep (se 1 (by rfl) ⟨3457286, by rfl⟩ : syracuseStep 4609715 = 6914573) B6914573
theorem B6477515 : Blo 1705053 6477515 := bstep (se 1 (by rfl) ⟨4858136, by rfl⟩ : syracuseStep 6477515 = 9716273) B9716273
theorem B6477529 : Blo 1705053 6477529 := bstep (se 2 (by rfl) ⟨2429073, by rfl⟩ : syracuseStep 6477529 = 4858147) B4858147
theorem B3839705 : Blo 1705053 3839705 := bstep (se 2 (by rfl) ⟨1439889, by rfl⟩ : syracuseStep 3839705 = 2879779) B2879779
theorem B6231811 : Blo 1705053 6231811 := bstep (se 1 (by rfl) ⟨4673858, by rfl⟩ : syracuseStep 6231811 = 9347717) B9347717
theorem B5756723 : Blo 1705053 5756723 := bstep (se 1 (by rfl) ⟨4317542, by rfl⟩ : syracuseStep 5756723 = 8635085) B8635085
theorem B3839795 : Blo 1705053 3839795 := bstep (se 1 (by rfl) ⟨2879846, by rfl⟩ : syracuseStep 3839795 = 5759693) B5759693
theorem B3839831 : Blo 1705053 3839831 := bstep (se 1 (by rfl) ⟨2879873, by rfl⟩ : syracuseStep 3839831 = 5759747) B5759747
theorem B31135589 : Blo 1705053 31135589 := bstep (se 4 (by rfl) ⟨2918961, by rfl⟩ : syracuseStep 31135589 = 5837923) B5837923
theorem B24926129 : Blo 1705053 24926129 := bstep (se 2 (by rfl) ⟨9347298, by rfl⟩ : syracuseStep 24926129 = 18694597) B18694597
theorem B14579635 : Blo 1705053 14579635 := bstep (se 1 (by rfl) ⟨10934726, by rfl⟩ : syracuseStep 14579635 = 21869453) B21869453
theorem B6920153 : Blo 1705053 6920153 := bstep (se 2 (by rfl) ⟨2595057, by rfl⟩ : syracuseStep 6920153 = 5190115) B5190115
theorem B3840011 : Blo 1705053 3840011 := bstep (se 1 (by rfl) ⟨2880008, by rfl⟩ : syracuseStep 3840011 = 5760017) B5760017
theorem B12957731 : Blo 1705053 12957731 := bstep (se 1 (by rfl) ⟨9718298, by rfl⟩ : syracuseStep 12957731 = 19436597) B19436597
theorem B4855859 : Blo 1705053 4855859 := bstep (se 1 (by rfl) ⟨3641894, by rfl⟩ : syracuseStep 4855859 = 7283789) B7283789
theorem B5756993 : Blo 1705053 5756993 := bstep (se 2 (by rfl) ⟨2158872, by rfl⟩ : syracuseStep 5756993 = 4317745) B4317745
theorem B3840065 : Blo 1705053 3840065 := bstep (se 2 (by rfl) ⟨1440024, by rfl⟩ : syracuseStep 3840065 = 2880049) B2880049
theorem B11671627 : Blo 1705053 11671627 := bstep (se 1 (by rfl) ⟨8753720, by rfl⟩ : syracuseStep 11671627 = 17507441) B17507441
theorem B9222245 : Blo 1705053 9222245 := bstep (se 4 (by rfl) ⟨864585, by rfl⟩ : syracuseStep 9222245 = 1729171) B1729171
theorem B3840281 : Blo 1705053 3840281 := bstep (se 2 (by rfl) ⟨1440105, by rfl⟩ : syracuseStep 3840281 = 2880211) B2880211
theorem B13834597 : Blo 1705053 13834597 := bstep (se 4 (by rfl) ⟨1296993, by rfl⟩ : syracuseStep 13834597 = 2593987) B2593987
theorem B3840371 : Blo 1705053 3840371 := bstep (se 1 (by rfl) ⟨2880278, by rfl⟩ : syracuseStep 3840371 = 5760557) B5760557
theorem B3889559 : Blo 1705053 3889559 := bstep (se 1 (by rfl) ⟨2917169, by rfl⟩ : syracuseStep 3889559 = 5834339) B5834339
theorem B3840407 : Blo 1705053 3840407 := bstep (se 1 (by rfl) ⟨2880305, by rfl⟩ : syracuseStep 3840407 = 5760611) B5760611
theorem B3840587 : Blo 1705053 3840587 := bstep (se 1 (by rfl) ⟨2880440, by rfl⟩ : syracuseStep 3840587 = 5760881) B5760881
theorem B5757533 : Blo 1705053 5757533 := bstep (se 3 (by rfl) ⟨1079537, by rfl⟩ : syracuseStep 5757533 = 2159075) B2159075
theorem B3840641 : Blo 1705053 3840641 := bstep (se 2 (by rfl) ⟨1440240, by rfl⟩ : syracuseStep 3840641 = 2880481) B2880481
theorem B6478487 : Blo 1705053 6478487 := bstep (se 1 (by rfl) ⟨4858865, by rfl⟩ : syracuseStep 6478487 = 9717731) B9717731
theorem B8641241 : Blo 1705053 8641241 := bstep (se 2 (by rfl) ⟨3240465, by rfl⟩ : syracuseStep 8641241 = 6480931) B6480931
theorem B19422017 : Blo 1705053 19422017 := bstep (se 2 (by rfl) ⟨7283256, by rfl⟩ : syracuseStep 19422017 = 14566513) B14566513
theorem B3840857 : Blo 1705053 3840857 := bstep (se 2 (by rfl) ⟨1440321, by rfl⟩ : syracuseStep 3840857 = 2880643) B2880643
theorem B9714563 : Blo 1705053 9714563 := bstep (se 1 (by rfl) ⟨7285922, by rfl⟩ : syracuseStep 9714563 = 14571845) B14571845
theorem B1973143 : Blo 1705053 1973143 := bstep (se 1 (by rfl) ⟨1479857, by rfl⟩ : syracuseStep 1973143 = 2959715) B2959715
theorem B6921305 : Blo 1705053 6921305 := bstep (se 2 (by rfl) ⟨2595489, by rfl⟩ : syracuseStep 6921305 = 5190979) B5190979
theorem B13835441 : Blo 1705053 13835441 := bstep (se 2 (by rfl) ⟨5188290, by rfl⟩ : syracuseStep 13835441 = 10376581) B10376581
theorem B18455813 : Blo 1705053 18455813 := bstep (se 4 (by rfl) ⟨1730232, by rfl⟩ : syracuseStep 18455813 = 3460465) B3460465
theorem B56860021 : Blo 1705053 56860021 := bstep (se 5 (by rfl) ⟨2665313, by rfl⟩ : syracuseStep 56860021 = 5330627) B5330627
theorem B7290263 : Blo 1705053 7290263 := bstep (se 1 (by rfl) ⟨5467697, by rfl⟩ : syracuseStep 7290263 = 10935395) B10935395
theorem B3644875 : Blo 1705053 3644875 := bstep (se 1 (by rfl) ⟨2733656, by rfl⟩ : syracuseStep 3644875 = 5467313) B5467313
theorem B4316723 : Blo 1705053 4316723 := bstep (se 1 (by rfl) ⟨3237542, by rfl⟩ : syracuseStep 4316723 = 6475085) B6475085
theorem B5758667 : Blo 1705053 5758667 := bstep (se 1 (by rfl) ⟨4319000, by rfl⟩ : syracuseStep 5758667 = 8638001) B8638001
theorem B8199953 : Blo 1705053 8199953 := bstep (se 2 (by rfl) ⟨3074982, by rfl⟩ : syracuseStep 8199953 = 6149965) B6149965
theorem B14769965 : Blo 1705053 14769965 := bstep (se 3 (by rfl) ⟨2769368, by rfl⟩ : syracuseStep 14769965 = 5538737) B5538737
theorem B21872429 : Blo 1705053 21872429 := bstep (se 3 (by rfl) ⟨4101080, by rfl⟩ : syracuseStep 21872429 = 8202161) B8202161
theorem B6479747 : Blo 1705053 6479747 := bstep (se 1 (by rfl) ⟨4859810, by rfl⟩ : syracuseStep 6479747 = 9719621) B9719621
theorem B3645337 : Blo 1705053 3645337 := bstep (se 2 (by rfl) ⟨1367001, by rfl⟩ : syracuseStep 3645337 = 2734003) B2734003
theorem B55312307 : Blo 1705053 55312307 := bstep (se 1 (by rfl) ⟨41484230, by rfl⟩ : syracuseStep 55312307 = 82968461) B82968461
theorem B5758937 : Blo 1705053 5758937 := bstep (se 2 (by rfl) ⟨2159601, by rfl⟩ : syracuseStep 5758937 = 4319203) B4319203
theorem B5537803 : Blo 1705053 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B6479959 : Blo 1705053 6479959 := bstep (se 1 (by rfl) ⟨4859969, by rfl⟩ : syracuseStep 6479959 = 9719939) B9719939
theorem B3694777 : Blo 1705053 3694777 := bstep (se 2 (by rfl) ⟨1385541, by rfl⟩ : syracuseStep 3694777 = 2771083) B2771083
theorem B2916553 : Blo 1705053 2916553 := bstep (se 2 (by rfl) ⟨1093707, by rfl⟩ : syracuseStep 2916553 = 2187415) B2187415
theorem B2998663 : Blo 1705053 2998663 := bstep (se 1 (by rfl) ⟨2248997, by rfl⟩ : syracuseStep 2998663 = 4497995) B4497995
theorem B6480263 : Blo 1705053 6480263 := bstep (se 1 (by rfl) ⟨4860197, by rfl⟩ : syracuseStep 6480263 = 9720395) B9720395
theorem B39387683 : Blo 1705053 39387683 := bstep (se 1 (by rfl) ⟨29540762, by rfl⟩ : syracuseStep 39387683 = 59081525) B59081525
theorem B8634923 : Blo 1705053 8634923 := bstep (se 1 (by rfl) ⟨6476192, by rfl⟩ : syracuseStep 8634923 = 12952385) B12952385
theorem B5759531 : Blo 1705053 5759531 := bstep (se 1 (by rfl) ⟨4319648, by rfl⟩ : syracuseStep 5759531 = 8639297) B8639297
theorem B6480445 : Blo 1705053 6480445 := bstep (se 3 (by rfl) ⟨1215083, by rfl⟩ : syracuseStep 6480445 = 2430167) B2430167
theorem B2048647 : Blo 1705053 2048647 := bstep (se 1 (by rfl) ⟨1536485, by rfl⟩ : syracuseStep 2048647 = 3072971) B3072971
theorem B12296933 : Blo 1705053 12296933 := bstep (se 4 (by rfl) ⟨1152837, by rfl⟩ : syracuseStep 12296933 = 2305675) B2305675
theorem B3892001 : Blo 1705053 3892001 := bstep (se 2 (by rfl) ⟨1459500, by rfl⟩ : syracuseStep 3892001 = 2919001) B2919001
theorem B4097083 : Blo 1705053 4097083 := bstep (se 1 (by rfl) ⟨3072812, by rfl⟩ : syracuseStep 4097083 = 6145625) B6145625
theorem B10372157 : Blo 1705053 10372157 := bstep (se 3 (by rfl) ⟨1944779, by rfl⟩ : syracuseStep 10372157 = 3889559) B3889559
theorem B4858967 : Blo 1705053 4858967 := bstep (se 1 (by rfl) ⟨3644225, by rfl⟩ : syracuseStep 4858967 = 7288451) B7288451
theorem B1705095 : Blo 1705053 1705095 := bstep (se 1 (by rfl) ⟨1278821, by rfl⟩ : syracuseStep 1705095 = 2557643) B2557643
theorem B4318343 : Blo 1705053 4318343 := bstep (se 1 (by rfl) ⟨3238757, by rfl⟩ : syracuseStep 4318343 = 6477515) B6477515
theorem B1705103 : Blo 1705053 1705103 := bstep (se 1 (by rfl) ⟨1278827, by rfl⟩ : syracuseStep 1705103 = 2557655) B2557655
theorem B4318393 : Blo 1705053 4318393 := bstep (se 2 (by rfl) ⟨1619397, by rfl⟩ : syracuseStep 4318393 = 3238795) B3238795
theorem B1705147 : Blo 1705053 1705147 := bstep (se 1 (by rfl) ⟨1278860, by rfl⟩ : syracuseStep 1705147 = 2557721) B2557721
theorem B1705223 : Blo 1705053 1705223 := bstep (se 1 (by rfl) ⟨1278917, by rfl⟩ : syracuseStep 1705223 = 2557835) B2557835
theorem B1705231 : Blo 1705053 1705231 := bstep (se 1 (by rfl) ⟨1278923, by rfl⟩ : syracuseStep 1705231 = 2557847) B2557847
theorem B1705275 : Blo 1705053 1705275 := bstep (se 1 (by rfl) ⟨1278956, by rfl⟩ : syracuseStep 1705275 = 2557913) B2557913
theorem B4613435 : Blo 1705053 4613435 := bstep (se 1 (by rfl) ⟨3460076, by rfl⟩ : syracuseStep 4613435 = 6920153) B6920153
theorem B3237239 : Blo 1705053 3237239 := bstep (se 1 (by rfl) ⟨2427929, by rfl⟩ : syracuseStep 3237239 = 4855859) B4855859
theorem B1705351 : Blo 1705053 1705351 := bstep (se 1 (by rfl) ⟨1279013, by rfl⟩ : syracuseStep 1705351 = 2558027) B2558027
theorem B1705359 : Blo 1705053 1705359 := bstep (se 1 (by rfl) ⟨1279019, by rfl⟩ : syracuseStep 1705359 = 2558039) B2558039
theorem B1705403 : Blo 1705053 1705403 := bstep (se 1 (by rfl) ⟨1279052, by rfl⟩ : syracuseStep 1705403 = 2558105) B2558105
theorem B1918471 : Blo 1705053 1918471 := bstep (se 1 (by rfl) ⟨1438853, by rfl⟩ : syracuseStep 1918471 = 2877707) B2877707
theorem B1705479 : Blo 1705053 1705479 := bstep (se 1 (by rfl) ⟨1279109, by rfl⟩ : syracuseStep 1705479 = 2558219) B2558219
theorem B1705487 : Blo 1705053 1705487 := bstep (se 1 (by rfl) ⟨1279115, by rfl⟩ : syracuseStep 1705487 = 2558231) B2558231
theorem B1705531 : Blo 1705053 1705531 := bstep (se 1 (by rfl) ⟨1279148, by rfl⟩ : syracuseStep 1705531 = 2558297) B2558297
theorem B1705607 : Blo 1705053 1705607 := bstep (se 1 (by rfl) ⟨1279205, by rfl⟩ : syracuseStep 1705607 = 2558411) B2558411
theorem B2557583 : Blo 1705053 2557583 := bstep (se 1 (by rfl) ⟨1918187, by rfl⟩ : syracuseStep 2557583 = 3836375) B3836375
theorem B1705615 : Blo 1705053 1705615 := bstep (se 1 (by rfl) ⟨1279211, by rfl⟩ : syracuseStep 1705615 = 2558423) B2558423
theorem B21857971 : Blo 1705053 21857971 := bstep (se 1 (by rfl) ⟨16393478, by rfl⟩ : syracuseStep 21857971 = 32786957) B32786957
theorem B2557625 : Blo 1705053 2557625 := bstep (se 2 (by rfl) ⟨959109, by rfl⟩ : syracuseStep 2557625 = 1918219) B1918219
theorem B1918651 : Blo 1705053 1918651 := bstep (se 1 (by rfl) ⟨1438988, by rfl⟩ : syracuseStep 1918651 = 2877977) B2877977
theorem B1705659 : Blo 1705053 1705659 := bstep (se 1 (by rfl) ⟨1279244, by rfl⟩ : syracuseStep 1705659 = 2558489) B2558489
theorem B11667137 : Blo 1705053 11667137 := bstep (se 2 (by rfl) ⟨4375176, by rfl⟩ : syracuseStep 11667137 = 8750353) B8750353
theorem B2557703 : Blo 1705053 2557703 := bstep (se 1 (by rfl) ⟨1918277, by rfl⟩ : syracuseStep 2557703 = 3836555) B3836555
theorem B1705735 : Blo 1705053 1705735 := bstep (se 1 (by rfl) ⟨1279301, by rfl⟩ : syracuseStep 1705735 = 2558603) B2558603
theorem B1705743 : Blo 1705053 1705743 := bstep (se 1 (by rfl) ⟨1279307, by rfl⟩ : syracuseStep 1705743 = 2558615) B2558615
theorem B4318991 : Blo 1705053 4318991 := bstep (se 1 (by rfl) ⟨3239243, by rfl⟩ : syracuseStep 4318991 = 6478487) B6478487
theorem B2557739 : Blo 1705053 2557739 := bstep (se 1 (by rfl) ⟨1918304, by rfl⟩ : syracuseStep 2557739 = 3836609) B3836609
theorem B1705787 : Blo 1705053 1705787 := bstep (se 1 (by rfl) ⟨1279340, by rfl⟩ : syracuseStep 1705787 = 2558681) B2558681
theorem B8636219 : Blo 1705053 8636219 := bstep (se 1 (by rfl) ⟨6477164, by rfl⟩ : syracuseStep 8636219 = 12954329) B12954329
theorem B5760827 : Blo 1705053 5760827 := bstep (se 1 (by rfl) ⟨4320620, by rfl⟩ : syracuseStep 5760827 = 8641241) B8641241
theorem B2557769 : Blo 1705053 2557769 := bstep (se 2 (by rfl) ⟨959163, by rfl⟩ : syracuseStep 2557769 = 1918327) B1918327
theorem B1705863 : Blo 1705053 1705863 := bstep (se 1 (by rfl) ⟨1279397, by rfl⟩ : syracuseStep 1705863 = 2558795) B2558795
theorem B1705871 : Blo 1705053 1705871 := bstep (se 1 (by rfl) ⟨1279403, by rfl⟩ : syracuseStep 1705871 = 2558807) B2558807
theorem B4859833 : Blo 1705053 4859833 := bstep (se 2 (by rfl) ⟨1822437, by rfl⟩ : syracuseStep 4859833 = 3644875) B3644875
theorem B2557883 : Blo 1705053 2557883 := bstep (se 1 (by rfl) ⟨1918412, by rfl⟩ : syracuseStep 2557883 = 3836825) B3836825
theorem B1705915 : Blo 1705053 1705915 := bstep (se 1 (by rfl) ⟨1279436, by rfl⟩ : syracuseStep 1705915 = 2558873) B2558873
theorem B303253445 : Blo 1705053 303253445 := bstep (se 4 (by rfl) ⟨28430010, by rfl⟩ : syracuseStep 303253445 = 56860021) B56860021
theorem B8636381 : Blo 1705053 8636381 := bstep (se 3 (by rfl) ⟨1619321, by rfl⟩ : syracuseStep 8636381 = 3238643) B3238643
theorem B2557943 : Blo 1705053 2557943 := bstep (se 1 (by rfl) ⟨1918457, by rfl⟩ : syracuseStep 2557943 = 3836915) B3836915
theorem B1705991 : Blo 1705053 1705991 := bstep (se 1 (by rfl) ⟨1279493, by rfl⟩ : syracuseStep 1705991 = 2558987) B2558987
theorem B2557967 : Blo 1705053 2557967 := bstep (se 1 (by rfl) ⟨1918475, by rfl⟩ : syracuseStep 2557967 = 3836951) B3836951
theorem B1705999 : Blo 1705053 1705999 := bstep (se 1 (by rfl) ⟨1279499, by rfl⟩ : syracuseStep 1705999 = 2558999) B2558999
theorem B2558009 : Blo 1705053 2558009 := bstep (se 2 (by rfl) ⟨959253, by rfl⟩ : syracuseStep 2558009 = 1918507) B1918507
theorem B1706043 : Blo 1705053 1706043 := bstep (se 1 (by rfl) ⟨1279532, by rfl⟩ : syracuseStep 1706043 = 2559065) B2559065
theorem B4614203 : Blo 1705053 4614203 := bstep (se 1 (by rfl) ⟨3460652, by rfl⟩ : syracuseStep 4614203 = 6921305) B6921305
theorem B2558087 : Blo 1705053 2558087 := bstep (se 1 (by rfl) ⟨1918565, by rfl⟩ : syracuseStep 2558087 = 3837131) B3837131
theorem B1706119 : Blo 1705053 1706119 := bstep (se 1 (by rfl) ⟨1279589, by rfl⟩ : syracuseStep 1706119 = 2559179) B2559179
theorem B1919119 : Blo 1705053 1919119 := bstep (se 1 (by rfl) ⟨1439339, by rfl⟩ : syracuseStep 1919119 = 2878679) B2878679
theorem B1706127 : Blo 1705053 1706127 := bstep (se 1 (by rfl) ⟨1279595, by rfl⟩ : syracuseStep 1706127 = 2559191) B2559191
theorem B2558123 : Blo 1705053 2558123 := bstep (se 1 (by rfl) ⟨1918592, by rfl⟩ : syracuseStep 2558123 = 3837185) B3837185
theorem B2050219 : Blo 1705053 2050219 := bstep (se 1 (by rfl) ⟨1537664, by rfl⟩ : syracuseStep 2050219 = 3075329) B3075329
theorem B1706171 : Blo 1705053 1706171 := bstep (se 1 (by rfl) ⟨1279628, by rfl⟩ : syracuseStep 1706171 = 2559257) B2559257
theorem B2558153 : Blo 1705053 2558153 := bstep (se 2 (by rfl) ⟨959307, by rfl⟩ : syracuseStep 2558153 = 1918615) B1918615
theorem B1706247 : Blo 1705053 1706247 := bstep (se 1 (by rfl) ⟨1279685, by rfl⟩ : syracuseStep 1706247 = 2559371) B2559371
theorem B1706255 : Blo 1705053 1706255 := bstep (se 1 (by rfl) ⟨1279691, by rfl⟩ : syracuseStep 1706255 = 2559383) B2559383
theorem B4860175 : Blo 1705053 4860175 := bstep (se 1 (by rfl) ⟨3645131, by rfl⟩ : syracuseStep 4860175 = 7290263) B7290263
theorem B8636705 : Blo 1705053 8636705 := bstep (se 2 (by rfl) ⟨3238764, by rfl⟩ : syracuseStep 8636705 = 6477529) B6477529
theorem B2558267 : Blo 1705053 2558267 := bstep (se 1 (by rfl) ⟨1918700, by rfl⟩ : syracuseStep 2558267 = 3837401) B3837401
theorem B1706299 : Blo 1705053 1706299 := bstep (se 1 (by rfl) ⟨1279724, by rfl⟩ : syracuseStep 1706299 = 2559449) B2559449
theorem B8309081 : Blo 1705053 8309081 := bstep (se 2 (by rfl) ⟨3115905, by rfl⟩ : syracuseStep 8309081 = 6231811) B6231811
theorem B2877815 : Blo 1705053 2877815 := bstep (se 1 (by rfl) ⟨2158361, by rfl⟩ : syracuseStep 2877815 = 4316723) B4316723
theorem B2558327 : Blo 1705053 2558327 := bstep (se 1 (by rfl) ⟨1918745, by rfl⟩ : syracuseStep 2558327 = 3837491) B3837491
theorem B1706375 : Blo 1705053 1706375 := bstep (se 1 (by rfl) ⟨1279781, by rfl⟩ : syracuseStep 1706375 = 2559563) B2559563
theorem B2558351 : Blo 1705053 2558351 := bstep (se 1 (by rfl) ⟨1918763, by rfl⟩ : syracuseStep 2558351 = 3837527) B3837527
theorem B1706383 : Blo 1705053 1706383 := bstep (se 1 (by rfl) ⟨1279787, by rfl⟩ : syracuseStep 1706383 = 2559575) B2559575
theorem B9718163 : Blo 1705053 9718163 := bstep (se 1 (by rfl) ⟨7288622, by rfl⟩ : syracuseStep 9718163 = 14577245) B14577245
theorem B2558393 : Blo 1705053 2558393 := bstep (se 2 (by rfl) ⟨959397, by rfl⟩ : syracuseStep 2558393 = 1918795) B1918795
theorem B1706427 : Blo 1705053 1706427 := bstep (se 1 (by rfl) ⟨1279820, by rfl⟩ : syracuseStep 1706427 = 2559641) B2559641
theorem B4319689 : Blo 1705053 4319689 := bstep (se 2 (by rfl) ⟨1619883, by rfl⟩ : syracuseStep 4319689 = 3239767) B3239767
theorem B328362457 : Blo 1705053 328362457 := bstep (se 2 (by rfl) ⟨123135921, by rfl⟩ : syracuseStep 328362457 = 246271843) B246271843
theorem B2558471 : Blo 1705053 2558471 := bstep (se 1 (by rfl) ⟨1918853, by rfl⟩ : syracuseStep 2558471 = 3837707) B3837707
theorem B1706503 : Blo 1705053 1706503 := bstep (se 1 (by rfl) ⟨1279877, by rfl⟩ : syracuseStep 1706503 = 2559755) B2559755
theorem B5466635 : Blo 1705053 5466635 := bstep (se 1 (by rfl) ⟨4099976, by rfl⟩ : syracuseStep 5466635 = 8199953) B8199953
theorem B1821199 : Blo 1705053 1821199 := bstep (se 1 (by rfl) ⟨1365899, by rfl⟩ : syracuseStep 1821199 = 2731799) B2731799
theorem B1706511 : Blo 1705053 1706511 := bstep (se 1 (by rfl) ⟨1279883, by rfl⟩ : syracuseStep 1706511 = 2559767) B2559767
theorem B4098593 : Blo 1705053 4098593 := bstep (se 2 (by rfl) ⟨1536972, by rfl⟩ : syracuseStep 4098593 = 3073945) B3073945
theorem B4860449 : Blo 1705053 4860449 := bstep (se 2 (by rfl) ⟨1822668, by rfl⟩ : syracuseStep 4860449 = 3645337) B3645337
theorem B2558507 : Blo 1705053 2558507 := bstep (se 1 (by rfl) ⟨1918880, by rfl⟩ : syracuseStep 2558507 = 3837761) B3837761
theorem B1706555 : Blo 1705053 1706555 := bstep (se 1 (by rfl) ⟨1279916, by rfl⟩ : syracuseStep 1706555 = 2559833) B2559833
theorem B2558537 : Blo 1705053 2558537 := bstep (se 2 (by rfl) ⟨959451, by rfl⟩ : syracuseStep 2558537 = 1918903) B1918903
theorem B4319831 : Blo 1705053 4319831 := bstep (se 1 (by rfl) ⟨3239873, by rfl⟩ : syracuseStep 4319831 = 6479747) B6479747
theorem B36874871 : Blo 1705053 36874871 := bstep (se 1 (by rfl) ⟨27656153, by rfl⟩ : syracuseStep 36874871 = 55312307) B55312307
theorem B1919623 : Blo 1705053 1919623 := bstep (se 1 (by rfl) ⟨1439717, by rfl⟩ : syracuseStep 1919623 = 2879435) B2879435
theorem B1706631 : Blo 1705053 1706631 := bstep (se 1 (by rfl) ⟨1279973, by rfl⟩ : syracuseStep 1706631 = 2559947) B2559947
theorem B1706639 : Blo 1705053 1706639 := bstep (se 1 (by rfl) ⟨1279979, by rfl⟩ : syracuseStep 1706639 = 2559959) B2559959
theorem B2558651 : Blo 1705053 2558651 := bstep (se 1 (by rfl) ⟨1918988, by rfl⟩ : syracuseStep 2558651 = 3837977) B3837977
theorem B1706683 : Blo 1705053 1706683 := bstep (se 1 (by rfl) ⟨1280012, by rfl⟩ : syracuseStep 1706683 = 2560025) B2560025
theorem B336579299 : Blo 1705053 336579299 := bstep (se 1 (by rfl) ⟨252434474, by rfl⟩ : syracuseStep 336579299 = 504868949) B504868949
theorem B9349861 : Blo 1705053 9349861 := bstep (se 4 (by rfl) ⟨876549, by rfl⟩ : syracuseStep 9349861 = 1753099) B1753099
theorem B2558711 : Blo 1705053 2558711 := bstep (se 1 (by rfl) ⟨1919033, by rfl⟩ : syracuseStep 2558711 = 3838067) B3838067
theorem B1706759 : Blo 1705053 1706759 := bstep (se 1 (by rfl) ⟨1280069, by rfl⟩ : syracuseStep 1706759 = 2560139) B2560139
theorem B2558735 : Blo 1705053 2558735 := bstep (se 1 (by rfl) ⟨1919051, by rfl⟩ : syracuseStep 2558735 = 3838103) B3838103
theorem B1706767 : Blo 1705053 1706767 := bstep (se 1 (by rfl) ⟨1280075, by rfl⟩ : syracuseStep 1706767 = 2560151) B2560151
theorem B2558777 : Blo 1705053 2558777 := bstep (se 2 (by rfl) ⟨959541, by rfl⟩ : syracuseStep 2558777 = 1919083) B1919083
theorem B2878267 : Blo 1705053 2878267 := bstep (se 1 (by rfl) ⟨2158700, by rfl⟩ : syracuseStep 2878267 = 4317401) B4317401
theorem B1919803 : Blo 1705053 1919803 := bstep (se 1 (by rfl) ⟨1439852, by rfl⟩ : syracuseStep 1919803 = 2879705) B2879705
theorem B1706811 : Blo 1705053 1706811 := bstep (se 1 (by rfl) ⟨1280108, by rfl⟩ : syracuseStep 1706811 = 2560217) B2560217
theorem B3836807 : Blo 1705053 3836807 := bstep (se 1 (by rfl) ⟨2877605, by rfl⟩ : syracuseStep 3836807 = 5755211) B5755211
theorem B1821575 : Blo 1705053 1821575 := bstep (se 1 (by rfl) ⟨1366181, by rfl⟩ : syracuseStep 1821575 = 2732363) B2732363
theorem B2558855 : Blo 1705053 2558855 := bstep (se 1 (by rfl) ⟨1919141, by rfl⟩ : syracuseStep 2558855 = 3838283) B3838283
theorem B9718663 : Blo 1705053 9718663 := bstep (se 1 (by rfl) ⟨7288997, by rfl⟩ : syracuseStep 9718663 = 14577995) B14577995
theorem B1706887 : Blo 1705053 1706887 := bstep (se 1 (by rfl) ⟨1280165, by rfl⟩ : syracuseStep 1706887 = 2560331) B2560331
theorem B1706895 : Blo 1705053 1706895 := bstep (se 1 (by rfl) ⟨1280171, by rfl⟩ : syracuseStep 1706895 = 2560343) B2560343
theorem B2558891 : Blo 1705053 2558891 := bstep (se 1 (by rfl) ⟨1919168, by rfl⟩ : syracuseStep 2558891 = 3838337) B3838337
theorem B3238841 : Blo 1705053 3238841 := bstep (se 2 (by rfl) ⟨1214565, by rfl⟩ : syracuseStep 3238841 = 2429131) B2429131
theorem B1706939 : Blo 1705053 1706939 := bstep (se 1 (by rfl) ⟨1280204, by rfl⟩ : syracuseStep 1706939 = 2560409) B2560409
theorem B2878409 : Blo 1705053 2878409 := bstep (se 2 (by rfl) ⟨1079403, by rfl⟩ : syracuseStep 2878409 = 2158807) B2158807
theorem B2558921 : Blo 1705053 2558921 := bstep (se 2 (by rfl) ⟨959595, by rfl⟩ : syracuseStep 2558921 = 1919191) B1919191
theorem B1707015 : Blo 1705053 1707015 := bstep (se 1 (by rfl) ⟨1280261, by rfl⟩ : syracuseStep 1707015 = 2560523) B2560523
theorem B1707023 : Blo 1705053 1707023 := bstep (se 1 (by rfl) ⟨1280267, by rfl⟩ : syracuseStep 1707023 = 2560535) B2560535
theorem B3836987 : Blo 1705053 3836987 := bstep (se 1 (by rfl) ⟨2877740, by rfl⟩ : syracuseStep 3836987 = 5755481) B5755481
theorem B2559035 : Blo 1705053 2559035 := bstep (se 1 (by rfl) ⟨1919276, by rfl⟩ : syracuseStep 2559035 = 3838553) B3838553
theorem B19426391 : Blo 1705053 19426391 := bstep (se 1 (by rfl) ⟨14569793, by rfl⟩ : syracuseStep 19426391 = 29139587) B29139587
theorem B2559095 : Blo 1705053 2559095 := bstep (se 1 (by rfl) ⟨1919321, by rfl⟩ : syracuseStep 2559095 = 3838643) B3838643
theorem B4861063 : Blo 1705053 4861063 := bstep (se 1 (by rfl) ⟨3645797, by rfl⟩ : syracuseStep 4861063 = 7291595) B7291595
theorem B2559119 : Blo 1705053 2559119 := bstep (se 1 (by rfl) ⟨1919339, by rfl⟩ : syracuseStep 2559119 = 3838679) B3838679
theorem B3837113 : Blo 1705053 3837113 := bstep (se 2 (by rfl) ⟨1438917, by rfl⟩ : syracuseStep 3837113 = 2877835) B2877835
theorem B2559161 : Blo 1705053 2559161 := bstep (se 2 (by rfl) ⟨959685, by rfl⟩ : syracuseStep 2559161 = 1919371) B1919371
theorem B8637677 : Blo 1705053 8637677 := bstep (se 3 (by rfl) ⟨1619564, by rfl⟩ : syracuseStep 8637677 = 3239129) B3239129
theorem B2559239 : Blo 1705053 2559239 := bstep (se 1 (by rfl) ⟨1919429, by rfl⟩ : syracuseStep 2559239 = 3838859) B3838859
theorem B3239183 : Blo 1705053 3239183 := bstep (se 1 (by rfl) ⟨2429387, by rfl⟩ : syracuseStep 3239183 = 4858775) B4858775
theorem B1920271 : Blo 1705053 1920271 := bstep (se 1 (by rfl) ⟨1440203, by rfl⟩ : syracuseStep 1920271 = 2880407) B2880407
theorem B2559275 : Blo 1705053 2559275 := bstep (se 1 (by rfl) ⟨1919456, by rfl⟩ : syracuseStep 2559275 = 3838913) B3838913
theorem B2559305 : Blo 1705053 2559305 := bstep (se 2 (by rfl) ⟨959739, by rfl⟩ : syracuseStep 2559305 = 1919479) B1919479
theorem B2559419 : Blo 1705053 2559419 := bstep (se 1 (by rfl) ⟨1919564, by rfl⟩ : syracuseStep 2559419 = 3839129) B3839129
theorem B2559479 : Blo 1705053 2559479 := bstep (se 1 (by rfl) ⟨1919609, by rfl⟩ : syracuseStep 2559479 = 3839219) B3839219
theorem B3837455 : Blo 1705053 3837455 := bstep (se 1 (by rfl) ⟨2878091, by rfl⟩ : syracuseStep 3837455 = 5756183) B5756183
theorem B2559503 : Blo 1705053 2559503 := bstep (se 1 (by rfl) ⟨1919627, by rfl⟩ : syracuseStep 2559503 = 3839255) B3839255
theorem B3837473 : Blo 1705053 3837473 := bstep (se 2 (by rfl) ⟨1439052, by rfl⟩ : syracuseStep 3837473 = 2878105) B2878105
theorem B3075617 : Blo 1705053 3075617 := bstep (se 2 (by rfl) ⟨1153356, by rfl⟩ : syracuseStep 3075617 = 2306713) B2306713
theorem B2559545 : Blo 1705053 2559545 := bstep (se 2 (by rfl) ⟨959829, by rfl⟩ : syracuseStep 2559545 = 1919659) B1919659
theorem B1822267 : Blo 1705053 1822267 := bstep (se 1 (by rfl) ⟨1366700, by rfl⟩ : syracuseStep 1822267 = 2733401) B2733401
theorem B9711191 : Blo 1705053 9711191 := bstep (se 1 (by rfl) ⟨7283393, by rfl⟩ : syracuseStep 9711191 = 14566787) B14566787
theorem B4673159 : Blo 1705053 4673159 := bstep (se 1 (by rfl) ⟨3504869, by rfl⟩ : syracuseStep 4673159 = 7009739) B7009739
theorem B2879111 : Blo 1705053 2879111 := bstep (se 1 (by rfl) ⟨2159333, by rfl⟩ : syracuseStep 2879111 = 4318667) B4318667
theorem B2559623 : Blo 1705053 2559623 := bstep (se 1 (by rfl) ⟨1919717, by rfl⟩ : syracuseStep 2559623 = 3839435) B3839435
theorem B2559659 : Blo 1705053 2559659 := bstep (se 1 (by rfl) ⟨1919744, by rfl⟩ : syracuseStep 2559659 = 3839489) B3839489
theorem B27668147 : Blo 1705053 27668147 := bstep (se 1 (by rfl) ⟨20751110, by rfl⟩ : syracuseStep 27668147 = 41502221) B41502221
theorem B2461385 : Blo 1705053 2461385 := bstep (se 2 (by rfl) ⟨923019, by rfl⟩ : syracuseStep 2461385 = 1846039) B1846039
theorem B2559689 : Blo 1705053 2559689 := bstep (se 2 (by rfl) ⟨959883, by rfl⟩ : syracuseStep 2559689 = 1919767) B1919767
theorem B17755919 : Blo 1705053 17755919 := bstep (se 1 (by rfl) ⟨13316939, by rfl⟩ : syracuseStep 17755919 = 26633879) B26633879
theorem B2559803 : Blo 1705053 2559803 := bstep (se 1 (by rfl) ⟨1919852, by rfl⟩ : syracuseStep 2559803 = 3839705) B3839705
theorem B3837815 : Blo 1705053 3837815 := bstep (se 1 (by rfl) ⟨2878361, by rfl⟩ : syracuseStep 3837815 = 5756723) B5756723
theorem B2559863 : Blo 1705053 2559863 := bstep (se 1 (by rfl) ⟨1919897, by rfl⟩ : syracuseStep 2559863 = 3839795) B3839795
theorem B2559887 : Blo 1705053 2559887 := bstep (se 1 (by rfl) ⟨1919915, by rfl⟩ : syracuseStep 2559887 = 3839831) B3839831
theorem B2559929 : Blo 1705053 2559929 := bstep (se 2 (by rfl) ⟨959973, by rfl⟩ : syracuseStep 2559929 = 1919947) B1919947
theorem B16617419 : Blo 1705053 16617419 := bstep (se 1 (by rfl) ⟨12463064, by rfl⟩ : syracuseStep 16617419 = 24926129) B24926129
theorem B2560007 : Blo 1705053 2560007 := bstep (se 1 (by rfl) ⟨1920005, by rfl⟩ : syracuseStep 2560007 = 3840011) B3840011
theorem B8638487 : Blo 1705053 8638487 := bstep (se 1 (by rfl) ⟨6478865, by rfl⟩ : syracuseStep 8638487 = 12957731) B12957731
theorem B3837995 : Blo 1705053 3837995 := bstep (se 1 (by rfl) ⟨2878496, by rfl⟩ : syracuseStep 3837995 = 5756993) B5756993
theorem B2560043 : Blo 1705053 2560043 := bstep (se 1 (by rfl) ⟨1920032, by rfl⟩ : syracuseStep 2560043 = 3840065) B3840065
theorem B3239995 : Blo 1705053 3239995 := bstep (se 1 (by rfl) ⟨2429996, by rfl⟩ : syracuseStep 3239995 = 4859993) B4859993
theorem B5754941 : Blo 1705053 5754941 := bstep (se 3 (by rfl) ⟨1079051, by rfl⟩ : syracuseStep 5754941 = 2158103) B2158103
theorem B6148163 : Blo 1705053 6148163 := bstep (se 1 (by rfl) ⟨4611122, by rfl⟩ : syracuseStep 6148163 = 9222245) B9222245
theorem B2560073 : Blo 1705053 2560073 := bstep (se 2 (by rfl) ⟨960027, by rfl⟩ : syracuseStep 2560073 = 1920055) B1920055
theorem B3240071 : Blo 1705053 3240071 := bstep (se 1 (by rfl) ⟨2430053, by rfl⟩ : syracuseStep 3240071 = 4860107) B4860107
theorem B2560187 : Blo 1705053 2560187 := bstep (se 1 (by rfl) ⟨1920140, by rfl⟩ : syracuseStep 2560187 = 3840281) B3840281
theorem B2560247 : Blo 1705053 2560247 := bstep (se 1 (by rfl) ⟨1920185, by rfl⟩ : syracuseStep 2560247 = 3840371) B3840371
theorem B2879759 : Blo 1705053 2879759 := bstep (se 1 (by rfl) ⟨2159819, by rfl⟩ : syracuseStep 2879759 = 4319639) B4319639
theorem B2560271 : Blo 1705053 2560271 := bstep (se 1 (by rfl) ⟨1920203, by rfl⟩ : syracuseStep 2560271 = 3840407) B3840407
theorem B2560313 : Blo 1705053 2560313 := bstep (se 2 (by rfl) ⟨960117, by rfl⟩ : syracuseStep 2560313 = 1920235) B1920235
theorem B2560391 : Blo 1705053 2560391 := bstep (se 1 (by rfl) ⟨1920293, by rfl⟩ : syracuseStep 2560391 = 3840587) B3840587
theorem B3838355 : Blo 1705053 3838355 := bstep (se 1 (by rfl) ⟨2878766, by rfl⟩ : syracuseStep 3838355 = 5757533) B5757533
theorem B2560427 : Blo 1705053 2560427 := bstep (se 1 (by rfl) ⟨1920320, by rfl⟩ : syracuseStep 2560427 = 3840641) B3840641
theorem B3838409 : Blo 1705053 3838409 := bstep (se 2 (by rfl) ⟨1439403, by rfl⟩ : syracuseStep 3838409 = 2878807) B2878807
theorem B2560457 : Blo 1705053 2560457 := bstep (se 2 (by rfl) ⟨960171, by rfl⟩ : syracuseStep 2560457 = 1920343) B1920343
theorem B12292573 : Blo 1705053 12292573 := bstep (se 3 (by rfl) ⟨2304857, by rfl⟩ : syracuseStep 12292573 = 4609715) B4609715
theorem B16396829 : Blo 1705053 16396829 := bstep (se 3 (by rfl) ⟨3074405, by rfl⟩ : syracuseStep 16396829 = 6148811) B6148811
theorem B3240481 : Blo 1705053 3240481 := bstep (se 2 (by rfl) ⟨1215180, by rfl⟩ : syracuseStep 3240481 = 2430361) B2430361
theorem B12948011 : Blo 1705053 12948011 := bstep (se 1 (by rfl) ⟨9711008, by rfl⟩ : syracuseStep 12948011 = 19422017) B19422017
theorem B2560571 : Blo 1705053 2560571 := bstep (se 1 (by rfl) ⟨1920428, by rfl⟩ : syracuseStep 2560571 = 3840857) B3840857
theorem B6476375 : Blo 1705053 6476375 := bstep (se 1 (by rfl) ⟨4857281, by rfl⟩ : syracuseStep 6476375 = 9714563) B9714563
theorem B29561537 : Blo 1705053 29561537 := bstep (se 2 (by rfl) ⟨11085576, by rfl⟩ : syracuseStep 29561537 = 22171153) B22171153
theorem B10523429 : Blo 1705053 10523429 := bstep (se 4 (by rfl) ⟨986571, by rfl⟩ : syracuseStep 10523429 = 1973143) B1973143
theorem B2880299 : Blo 1705053 2880299 := bstep (se 1 (by rfl) ⟨2160224, by rfl⟩ : syracuseStep 2880299 = 4320449) B4320449
theorem B6476861 : Blo 1705053 6476861 := bstep (se 3 (by rfl) ⟨1214411, by rfl⟩ : syracuseStep 6476861 = 2428823) B2428823
theorem B12956759 : Blo 1705053 12956759 := bstep (se 1 (by rfl) ⟨9717569, by rfl⟩ : syracuseStep 12956759 = 19435139) B19435139
theorem B3839111 : Blo 1705053 3839111 := bstep (se 1 (by rfl) ⟨2879333, by rfl⟩ : syracuseStep 3839111 = 5758667) B5758667
theorem B3282209 : Blo 1705053 3282209 := bstep (se 2 (by rfl) ⟨1230828, by rfl⟩ : syracuseStep 3282209 = 2461657) B2461657
theorem B3839291 : Blo 1705053 3839291 := bstep (se 1 (by rfl) ⟨2879468, by rfl⟩ : syracuseStep 3839291 = 5758937) B5758937
theorem B2430281 : Blo 1705053 2430281 := bstep (se 2 (by rfl) ⟨911355, by rfl⟩ : syracuseStep 2430281 = 1822711) B1822711
theorem B14570887 : Blo 1705053 14570887 := bstep (se 1 (by rfl) ⟨10928165, by rfl⟩ : syracuseStep 14570887 = 21856331) B21856331
theorem B5756345 : Blo 1705053 5756345 := bstep (se 2 (by rfl) ⟨2158629, by rfl⟩ : syracuseStep 5756345 = 4317259) B4317259
theorem B15562169 : Blo 1705053 15562169 := bstep (se 2 (by rfl) ⟨5835813, by rfl⟩ : syracuseStep 15562169 = 11671627) B11671627
theorem B3839417 : Blo 1705053 3839417 := bstep (se 2 (by rfl) ⟨1439781, by rfl⟩ : syracuseStep 3839417 = 2879563) B2879563
theorem B9713105 : Blo 1705053 9713105 := bstep (se 2 (by rfl) ⟨3642414, by rfl⟩ : syracuseStep 9713105 = 7284829) B7284829
theorem B4609565 : Blo 1705053 4609565 := bstep (se 3 (by rfl) ⟨864293, by rfl⟩ : syracuseStep 4609565 = 1728587) B1728587
theorem B3839759 : Blo 1705053 3839759 := bstep (se 1 (by rfl) ⟨2879819, by rfl⟩ : syracuseStep 3839759 = 5759639) B5759639
theorem B4855585 : Blo 1705053 4855585 := bstep (se 2 (by rfl) ⟨1820844, by rfl⟩ : syracuseStep 4855585 = 3641689) B3641689
theorem B3839777 : Blo 1705053 3839777 := bstep (se 2 (by rfl) ⟨1439916, by rfl⟩ : syracuseStep 3839777 = 2879833) B2879833
theorem B2160427 : Blo 1705053 2160427 := bstep (se 1 (by rfl) ⟨1620320, by rfl⟩ : syracuseStep 2160427 = 3240641) B3240641
theorem B18446129 : Blo 1705053 18446129 := bstep (se 2 (by rfl) ⟨6917298, by rfl⟩ : syracuseStep 18446129 = 13834597) B13834597
theorem B3643337 : Blo 1705053 3643337 := bstep (se 2 (by rfl) ⟨1366251, by rfl⟩ : syracuseStep 3643337 = 2732503) B2732503
theorem B8632331 : Blo 1705053 8632331 := bstep (se 1 (by rfl) ⟨6474248, by rfl⟩ : syracuseStep 8632331 = 12948497) B12948497
theorem B5756939 : Blo 1705053 5756939 := bstep (se 1 (by rfl) ⟨4317704, by rfl⟩ : syracuseStep 5756939 = 8635409) B8635409
theorem B7288861 : Blo 1705053 7288861 := bstep (se 3 (by rfl) ⟨1366661, by rfl⟩ : syracuseStep 7288861 = 2733323) B2733323
theorem B5757047 : Blo 1705053 5757047 := bstep (se 1 (by rfl) ⟨4317785, by rfl⟩ : syracuseStep 5757047 = 8635571) B8635571
theorem B3840119 : Blo 1705053 3840119 := bstep (se 1 (by rfl) ⟨2880089, by rfl⟩ : syracuseStep 3840119 = 5760179) B5760179
theorem B8632493 : Blo 1705053 8632493 := bstep (se 3 (by rfl) ⟨1618592, by rfl⟩ : syracuseStep 8632493 = 3237185) B3237185
theorem B4856075 : Blo 1705053 4856075 := bstep (se 1 (by rfl) ⟨3642056, by rfl⟩ : syracuseStep 4856075 = 7284113) B7284113
theorem B3840299 : Blo 1705053 3840299 := bstep (se 1 (by rfl) ⟨2880224, by rfl⟩ : syracuseStep 3840299 = 5760449) B5760449
theorem B7289203 : Blo 1705053 7289203 := bstep (se 1 (by rfl) ⟨5466902, by rfl⟩ : syracuseStep 7289203 = 10933805) B10933805
theorem B8198585 : Blo 1705053 8198585 := bstep (se 2 (by rfl) ⟨3074469, by rfl⟩ : syracuseStep 8198585 = 6148939) B6148939
theorem B1009301957 : Blo 1705053 1009301957 := bstep (se 4 (by rfl) ⟨94622058, by rfl⟩ : syracuseStep 1009301957 = 189244117) B189244117
theorem B6478289 : Blo 1705053 6478289 := bstep (se 2 (by rfl) ⟨2429358, by rfl⟩ : syracuseStep 6478289 = 4858717) B4858717
theorem B4610603 : Blo 1705053 4610603 := bstep (se 1 (by rfl) ⟨3457952, by rfl⟩ : syracuseStep 4610603 = 6915905) B6915905
theorem B20757059 : Blo 1705053 20757059 := bstep (se 1 (by rfl) ⟨15567794, by rfl⟩ : syracuseStep 20757059 = 31135589) B31135589
theorem B3840659 : Blo 1705053 3840659 := bstep (se 1 (by rfl) ⟨2880494, by rfl⟩ : syracuseStep 3840659 = 5760989) B5760989
theorem B5757641 : Blo 1705053 5757641 := bstep (se 2 (by rfl) ⟨2159115, by rfl⟩ : syracuseStep 5757641 = 4318231) B4318231
theorem B3840713 : Blo 1705053 3840713 := bstep (se 2 (by rfl) ⟨1440267, by rfl⟩ : syracuseStep 3840713 = 2880535) B2880535
theorem B4315963 : Blo 1705053 4315963 := bstep (se 1 (by rfl) ⟨3236972, by rfl⟩ : syracuseStep 4315963 = 6473945) B6473945
theorem B4316105 : Blo 1705053 4316105 := bstep (se 2 (by rfl) ⟨1618539, by rfl⟩ : syracuseStep 4316105 = 3237079) B3237079
theorem B9984971 : Blo 1705053 9984971 := bstep (se 1 (by rfl) ⟨7488728, by rfl⟩ : syracuseStep 9984971 = 14977457) B14977457
theorem B4856861 : Blo 1705053 4856861 := bstep (se 3 (by rfl) ⟨910661, by rfl⟩ : syracuseStep 4856861 = 1821323) B1821323
theorem B8641565 : Blo 1705053 8641565 := bstep (se 3 (by rfl) ⟨1620293, by rfl⟩ : syracuseStep 8641565 = 3240587) B3240587
theorem B10378477 : Blo 1705053 10378477 := bstep (se 3 (by rfl) ⟨1945964, by rfl⟩ : syracuseStep 10378477 = 3891929) B3891929
theorem B4316449 : Blo 1705053 4316449 := bstep (se 2 (by rfl) ⟨1618668, by rfl⟩ : syracuseStep 4316449 = 3237337) B3237337
theorem B16391483 : Blo 1705053 16391483 := bstep (se 1 (by rfl) ⟨12293612, by rfl⟩ : syracuseStep 16391483 = 24587225) B24587225
theorem B5758343 : Blo 1705053 5758343 := bstep (se 1 (by rfl) ⟨4318757, by rfl⟩ : syracuseStep 5758343 = 8637515) B8637515
theorem B9223627 : Blo 1705053 9223627 := bstep (se 1 (by rfl) ⟨6917720, by rfl⟩ : syracuseStep 9223627 = 13835441) B13835441
theorem B39386573 : Blo 1705053 39386573 := bstep (se 3 (by rfl) ⟨7384982, by rfl⟩ : syracuseStep 39386573 = 14769965) B14769965
theorem B31112657 : Blo 1705053 31112657 := bstep (se 2 (by rfl) ⟨11667246, by rfl⟩ : syracuseStep 31112657 = 23334493) B23334493
theorem B12303875 : Blo 1705053 12303875 := bstep (se 1 (by rfl) ⟨9227906, by rfl⟩ : syracuseStep 12303875 = 18455813) B18455813
theorem B8634113 : Blo 1705053 8634113 := bstep (se 2 (by rfl) ⟨3237792, by rfl⟩ : syracuseStep 8634113 = 6475585) B6475585
theorem B5758721 : Blo 1705053 5758721 := bstep (se 2 (by rfl) ⟨2159520, by rfl⟩ : syracuseStep 5758721 = 4319041) B4319041
theorem B18456335 : Blo 1705053 18456335 := bstep (se 1 (by rfl) ⟨13842251, by rfl⟩ : syracuseStep 18456335 = 27684503) B27684503
theorem B14581619 : Blo 1705053 14581619 := bstep (se 1 (by rfl) ⟨10936214, by rfl⟩ : syracuseStep 14581619 = 21872429) B21872429
theorem B4317047 : Blo 1705053 4317047 := bstep (se 1 (by rfl) ⟨3237785, by rfl⟩ : syracuseStep 4317047 = 6475571) B6475571
theorem B3645319 : Blo 1705053 3645319 := bstep (se 1 (by rfl) ⟨2733989, by rfl⟩ : syracuseStep 3645319 = 5467979) B5467979
theorem B3891091 : Blo 1705053 3891091 := bstep (se 1 (by rfl) ⟨2918318, by rfl⟩ : syracuseStep 3891091 = 5836637) B5836637
theorem B19439513 : Blo 1705053 19439513 := bstep (se 2 (by rfl) ⟨7289817, by rfl⟩ : syracuseStep 19439513 = 14579635) B14579635
theorem B5758991 : Blo 1705053 5758991 := bstep (se 1 (by rfl) ⟨4319243, by rfl⟩ : syracuseStep 5758991 = 8638487) B8638487
theorem B63971477 : Blo 1705053 63971477 := bstep (se 6 (by rfl) ⟨1499331, by rfl⟩ : syracuseStep 63971477 = 2998663) B2998663
theorem B12304541 : Blo 1705053 12304541 := bstep (se 3 (by rfl) ⟨2307101, by rfl⟩ : syracuseStep 12304541 = 4614203) B4614203
theorem B6480233 : Blo 1705053 6480233 := bstep (se 2 (by rfl) ⟨2430087, by rfl⟩ : syracuseStep 6480233 = 4860175) B4860175
theorem B4317583 : Blo 1705053 4317583 := bstep (se 1 (by rfl) ⟨3238187, by rfl⟩ : syracuseStep 4317583 = 6476375) B6476375
theorem B5759585 : Blo 1705053 5759585 := bstep (se 2 (by rfl) ⟨2159844, by rfl⟩ : syracuseStep 5759585 = 4319689) B4319689
theorem B6914771 : Blo 1705053 6914771 := bstep (se 1 (by rfl) ⟨5186078, by rfl⟩ : syracuseStep 6914771 = 10372157) B10372157
theorem B4317907 : Blo 1705053 4317907 := bstep (se 1 (by rfl) ⟨3238430, by rfl⟩ : syracuseStep 4317907 = 6476861) B6476861
theorem B2188139 : Blo 1705053 2188139 := bstep (se 1 (by rfl) ⟨1641104, by rfl⟩ : syracuseStep 2188139 = 3282209) B3282209
theorem B6480749 : Blo 1705053 6480749 := bstep (se 3 (by rfl) ⟨1215140, by rfl⟩ : syracuseStep 6480749 = 2430281) B2430281
theorem B3073043 : Blo 1705053 3073043 := bstep (se 1 (by rfl) ⟨2304782, by rfl⟩ : syracuseStep 3073043 = 4609565) B4609565
theorem B1705055 : Blo 1705053 1705055 := bstep (se 1 (by rfl) ⟨1278791, by rfl⟩ : syracuseStep 1705055 = 2557583) B2557583
theorem B1705083 : Blo 1705053 1705083 := bstep (se 1 (by rfl) ⟨1278812, by rfl⟩ : syracuseStep 1705083 = 2557625) B2557625
theorem B1705135 : Blo 1705053 1705135 := bstep (se 1 (by rfl) ⟨1278851, by rfl⟩ : syracuseStep 1705135 = 2557703) B2557703
theorem B1705159 : Blo 1705053 1705159 := bstep (se 1 (by rfl) ⟨1278869, by rfl⟩ : syracuseStep 1705159 = 2557739) B2557739
theorem B12297419 : Blo 1705053 12297419 := bstep (se 1 (by rfl) ⟨9223064, by rfl⟩ : syracuseStep 12297419 = 18446129) B18446129
theorem B1705179 : Blo 1705053 1705179 := bstep (se 1 (by rfl) ⟨1278884, by rfl⟩ : syracuseStep 1705179 = 2557769) B2557769
theorem B1705255 : Blo 1705053 1705255 := bstep (se 1 (by rfl) ⟨1278941, by rfl⟩ : syracuseStep 1705255 = 2557883) B2557883
theorem B1705295 : Blo 1705053 1705295 := bstep (se 1 (by rfl) ⟨1278971, by rfl⟩ : syracuseStep 1705295 = 2557943) B2557943
theorem B1705311 : Blo 1705053 1705311 := bstep (se 1 (by rfl) ⟨1278983, by rfl⟩ : syracuseStep 1705311 = 2557967) B2557967
theorem B1705339 : Blo 1705053 1705339 := bstep (se 1 (by rfl) ⟨1279004, by rfl⟩ : syracuseStep 1705339 = 2558009) B2558009
theorem B8201645 : Blo 1705053 8201645 := bstep (se 3 (by rfl) ⟨1537808, by rfl⟩ : syracuseStep 8201645 = 3075617) B3075617
theorem B1705391 : Blo 1705053 1705391 := bstep (se 1 (by rfl) ⟨1279043, by rfl⟩ : syracuseStep 1705391 = 2558087) B2558087
theorem B1705415 : Blo 1705053 1705415 := bstep (se 1 (by rfl) ⟨1279061, by rfl⟩ : syracuseStep 1705415 = 2558123) B2558123
theorem B1705435 : Blo 1705053 1705435 := bstep (se 1 (by rfl) ⟨1279076, by rfl⟩ : syracuseStep 1705435 = 2558153) B2558153
theorem B3237383 : Blo 1705053 3237383 := bstep (se 1 (by rfl) ⟨2428037, by rfl⟩ : syracuseStep 3237383 = 4856075) B4856075
theorem B6481417 : Blo 1705053 6481417 := bstep (se 2 (by rfl) ⟨2430531, by rfl⟩ : syracuseStep 6481417 = 4861063) B4861063
theorem B1705511 : Blo 1705053 1705511 := bstep (se 1 (by rfl) ⟨1279133, by rfl⟩ : syracuseStep 1705511 = 2558267) B2558267
theorem B5539387 : Blo 1705053 5539387 := bstep (se 1 (by rfl) ⟨4154540, by rfl⟩ : syracuseStep 5539387 = 8309081) B8309081
theorem B1918543 : Blo 1705053 1918543 := bstep (se 1 (by rfl) ⟨1438907, by rfl⟩ : syracuseStep 1918543 = 2877815) B2877815
theorem B1705551 : Blo 1705053 1705551 := bstep (se 1 (by rfl) ⟨1279163, by rfl⟩ : syracuseStep 1705551 = 2558327) B2558327
theorem B1705567 : Blo 1705053 1705567 := bstep (se 1 (by rfl) ⟨1279175, by rfl⟩ : syracuseStep 1705567 = 2558351) B2558351
theorem B1705595 : Blo 1705053 1705595 := bstep (se 1 (by rfl) ⟨1279196, by rfl⟩ : syracuseStep 1705595 = 2558393) B2558393
theorem B5465723 : Blo 1705053 5465723 := bstep (se 1 (by rfl) ⟨4099292, by rfl⟩ : syracuseStep 5465723 = 8198585) B8198585
theorem B672867971 : Blo 1705053 672867971 := bstep (se 1 (by rfl) ⟨504650978, by rfl⟩ : syracuseStep 672867971 = 1009301957) B1009301957
theorem B4318859 : Blo 1705053 4318859 := bstep (se 1 (by rfl) ⟨3239144, by rfl⟩ : syracuseStep 4318859 = 6478289) B6478289
theorem B13837969 : Blo 1705053 13837969 := bstep (se 2 (by rfl) ⟨5189238, by rfl⟩ : syracuseStep 13837969 = 10378477) B10378477
theorem B1705647 : Blo 1705053 1705647 := bstep (se 1 (by rfl) ⟨1279235, by rfl⟩ : syracuseStep 1705647 = 2558471) B2558471
theorem B1705671 : Blo 1705053 1705671 := bstep (se 1 (by rfl) ⟨1279253, by rfl⟩ : syracuseStep 1705671 = 2558507) B2558507
theorem B3073735 : Blo 1705053 3073735 := bstep (se 1 (by rfl) ⟨2305301, by rfl⟩ : syracuseStep 3073735 = 4610603) B4610603
theorem B13838039 : Blo 1705053 13838039 := bstep (se 1 (by rfl) ⟨10378529, by rfl⟩ : syracuseStep 13838039 = 20757059) B20757059
theorem B1705691 : Blo 1705053 1705691 := bstep (se 1 (by rfl) ⟨1279268, by rfl⟩ : syracuseStep 1705691 = 2558537) B2558537
theorem B1705767 : Blo 1705053 1705767 := bstep (se 1 (by rfl) ⟨1279325, by rfl⟩ : syracuseStep 1705767 = 2558651) B2558651
theorem B1705807 : Blo 1705053 1705807 := bstep (se 1 (by rfl) ⟨1279355, by rfl⟩ : syracuseStep 1705807 = 2558711) B2558711
theorem B1705823 : Blo 1705053 1705823 := bstep (se 1 (by rfl) ⟨1279367, by rfl⟩ : syracuseStep 1705823 = 2558735) B2558735
theorem B6563693 : Blo 1705053 6563693 := bstep (se 3 (by rfl) ⟨1230692, by rfl⟩ : syracuseStep 6563693 = 2461385) B2461385
theorem B1705851 : Blo 1705053 1705851 := bstep (se 1 (by rfl) ⟨1279388, by rfl⟩ : syracuseStep 1705851 = 2558777) B2558777
theorem B2557871 : Blo 1705053 2557871 := bstep (se 1 (by rfl) ⟨1918403, by rfl⟩ : syracuseStep 2557871 = 3836807) B3836807
theorem B1705903 : Blo 1705053 1705903 := bstep (se 1 (by rfl) ⟨1279427, by rfl⟩ : syracuseStep 1705903 = 2558855) B2558855
theorem B12298169 : Blo 1705053 12298169 := bstep (se 2 (by rfl) ⟨4611813, by rfl⟩ : syracuseStep 12298169 = 9223627) B9223627
theorem B1705927 : Blo 1705053 1705927 := bstep (se 1 (by rfl) ⟨1279445, by rfl⟩ : syracuseStep 1705927 = 2558891) B2558891
theorem B2877403 : Blo 1705053 2877403 := bstep (se 1 (by rfl) ⟨2158052, by rfl⟩ : syracuseStep 2877403 = 4316105) B4316105
theorem B1918939 : Blo 1705053 1918939 := bstep (se 1 (by rfl) ⟨1439204, by rfl⟩ : syracuseStep 1918939 = 2878409) B2878409
theorem B1705947 : Blo 1705053 1705947 := bstep (se 1 (by rfl) ⟨1279460, by rfl⟩ : syracuseStep 1705947 = 2558921) B2558921
theorem B2557961 : Blo 1705053 2557961 := bstep (se 2 (by rfl) ⟨959235, by rfl⟩ : syracuseStep 2557961 = 1918471) B1918471
theorem B3237907 : Blo 1705053 3237907 := bstep (se 1 (by rfl) ⟨2428430, by rfl⟩ : syracuseStep 3237907 = 4856861) B4856861
theorem B5761043 : Blo 1705053 5761043 := bstep (se 1 (by rfl) ⟨4320782, by rfl⟩ : syracuseStep 5761043 = 8641565) B8641565
theorem B2557991 : Blo 1705053 2557991 := bstep (se 1 (by rfl) ⟨1918493, by rfl⟩ : syracuseStep 2557991 = 3836987) B3836987
theorem B1706023 : Blo 1705053 1706023 := bstep (se 1 (by rfl) ⟨1279517, by rfl⟩ : syracuseStep 1706023 = 2559035) B2559035
theorem B1706063 : Blo 1705053 1706063 := bstep (se 1 (by rfl) ⟨1279547, by rfl⟩ : syracuseStep 1706063 = 2559095) B2559095
theorem B1706079 : Blo 1705053 1706079 := bstep (se 1 (by rfl) ⟨1279559, by rfl⟩ : syracuseStep 1706079 = 2559119) B2559119
theorem B2558075 : Blo 1705053 2558075 := bstep (se 1 (by rfl) ⟨1918556, by rfl⟩ : syracuseStep 2558075 = 3837113) B3837113
theorem B1706107 : Blo 1705053 1706107 := bstep (se 1 (by rfl) ⟨1279580, by rfl⟩ : syracuseStep 1706107 = 2559161) B2559161
theorem B1706159 : Blo 1705053 1706159 := bstep (se 1 (by rfl) ⟨1279619, by rfl⟩ : syracuseStep 1706159 = 2559239) B2559239
theorem B1706183 : Blo 1705053 1706183 := bstep (se 1 (by rfl) ⟨1279637, by rfl⟩ : syracuseStep 1706183 = 2559275) B2559275
theorem B1706203 : Blo 1705053 1706203 := bstep (se 1 (by rfl) ⟨1279652, by rfl⟩ : syracuseStep 1706203 = 2559305) B2559305
theorem B2558201 : Blo 1705053 2558201 := bstep (se 2 (by rfl) ⟨959325, by rfl⟩ : syracuseStep 2558201 = 1918651) B1918651
theorem B1706279 : Blo 1705053 1706279 := bstep (se 1 (by rfl) ⟨1279709, by rfl⟩ : syracuseStep 1706279 = 2559419) B2559419
theorem B26257715 : Blo 1705053 26257715 := bstep (se 1 (by rfl) ⟨19693286, by rfl⟩ : syracuseStep 26257715 = 39386573) B39386573
theorem B1706319 : Blo 1705053 1706319 := bstep (se 1 (by rfl) ⟨1279739, by rfl⟩ : syracuseStep 1706319 = 2559479) B2559479
theorem B8202583 : Blo 1705053 8202583 := bstep (se 1 (by rfl) ⟨6151937, by rfl⟩ : syracuseStep 8202583 = 12303875) B12303875
theorem B2558303 : Blo 1705053 2558303 := bstep (se 1 (by rfl) ⟨1918727, by rfl⟩ : syracuseStep 2558303 = 3837455) B3837455
theorem B1706335 : Blo 1705053 1706335 := bstep (se 1 (by rfl) ⟨1279751, by rfl⟩ : syracuseStep 1706335 = 2559503) B2559503
theorem B2558315 : Blo 1705053 2558315 := bstep (se 1 (by rfl) ⟨1918736, by rfl⟩ : syracuseStep 2558315 = 3837473) B3837473
theorem B1706363 : Blo 1705053 1706363 := bstep (se 1 (by rfl) ⟨1279772, by rfl⟩ : syracuseStep 1706363 = 2559545) B2559545
theorem B6474113 : Blo 1705053 6474113 := bstep (se 2 (by rfl) ⟨2427792, by rfl⟩ : syracuseStep 6474113 = 4855585) B4855585
theorem B6474127 : Blo 1705053 6474127 := bstep (se 1 (by rfl) ⟨4855595, by rfl⟩ : syracuseStep 6474127 = 9711191) B9711191
theorem B3115439 : Blo 1705053 3115439 := bstep (se 1 (by rfl) ⟨2336579, by rfl⟩ : syracuseStep 3115439 = 4673159) B4673159
theorem B1919407 : Blo 1705053 1919407 := bstep (se 1 (by rfl) ⟨1439555, by rfl⟩ : syracuseStep 1919407 = 2879111) B2879111
theorem B1706415 : Blo 1705053 1706415 := bstep (se 1 (by rfl) ⟨1279811, by rfl⟩ : syracuseStep 1706415 = 2559623) B2559623
theorem B1706439 : Blo 1705053 1706439 := bstep (se 1 (by rfl) ⟨1279829, by rfl⟩ : syracuseStep 1706439 = 2559659) B2559659
theorem B1706459 : Blo 1705053 1706459 := bstep (se 1 (by rfl) ⟨1279844, by rfl⟩ : syracuseStep 1706459 = 2559689) B2559689
theorem B4860425 : Blo 1705053 4860425 := bstep (se 2 (by rfl) ⟨1822659, by rfl⟩ : syracuseStep 4860425 = 3645319) B3645319
theorem B5188121 : Blo 1705053 5188121 := bstep (se 2 (by rfl) ⟨1945545, by rfl⟩ : syracuseStep 5188121 = 3891091) B3891091
theorem B26626589 : Blo 1705053 26626589 := bstep (se 3 (by rfl) ⟨4992485, by rfl⟩ : syracuseStep 26626589 = 9984971) B9984971
theorem B1706535 : Blo 1705053 1706535 := bstep (se 1 (by rfl) ⟨1279901, by rfl⟩ : syracuseStep 1706535 = 2559803) B2559803
theorem B2878031 : Blo 1705053 2878031 := bstep (se 1 (by rfl) ⟨2158523, by rfl⟩ : syracuseStep 2878031 = 4317047) B4317047
theorem B2558543 : Blo 1705053 2558543 := bstep (se 1 (by rfl) ⟨1918907, by rfl⟩ : syracuseStep 2558543 = 3837815) B3837815
theorem B1706575 : Blo 1705053 1706575 := bstep (se 1 (by rfl) ⟨1279931, by rfl⟩ : syracuseStep 1706575 = 2559863) B2559863
theorem B1706591 : Blo 1705053 1706591 := bstep (se 1 (by rfl) ⟨1279943, by rfl⟩ : syracuseStep 1706591 = 2559887) B2559887
theorem B1706619 : Blo 1705053 1706619 := bstep (se 1 (by rfl) ⟨1279964, by rfl⟩ : syracuseStep 1706619 = 2559929) B2559929
theorem B11078279 : Blo 1705053 11078279 := bstep (se 1 (by rfl) ⟨8308709, by rfl⟩ : syracuseStep 11078279 = 16617419) B16617419
theorem B1706671 : Blo 1705053 1706671 := bstep (se 1 (by rfl) ⟨1280003, by rfl⟩ : syracuseStep 1706671 = 2560007) B2560007
theorem B7383737 : Blo 1705053 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B2558663 : Blo 1705053 2558663 := bstep (se 1 (by rfl) ⟨1918997, by rfl⟩ : syracuseStep 2558663 = 3837995) B3837995
theorem B1706695 : Blo 1705053 1706695 := bstep (se 1 (by rfl) ⟨1280021, by rfl⟩ : syracuseStep 1706695 = 2560043) B2560043
theorem B9718481 : Blo 1705053 9718481 := bstep (se 2 (by rfl) ⟨3644430, by rfl⟩ : syracuseStep 9718481 = 7288861) B7288861
theorem B3836627 : Blo 1705053 3836627 := bstep (se 1 (by rfl) ⟨2877470, by rfl⟩ : syracuseStep 3836627 = 5754941) B5754941
theorem B4098775 : Blo 1705053 4098775 := bstep (se 1 (by rfl) ⟨3074081, by rfl⟩ : syracuseStep 4098775 = 6148163) B6148163
theorem B1706715 : Blo 1705053 1706715 := bstep (se 1 (by rfl) ⟨1280036, by rfl⟩ : syracuseStep 1706715 = 2560073) B2560073
theorem B4319993 : Blo 1705053 4319993 := bstep (se 2 (by rfl) ⟨1619997, by rfl⟩ : syracuseStep 4319993 = 3239995) B3239995
theorem B1706791 : Blo 1705053 1706791 := bstep (se 1 (by rfl) ⟨1280093, by rfl⟩ : syracuseStep 1706791 = 2560187) B2560187
theorem B1706831 : Blo 1705053 1706831 := bstep (se 1 (by rfl) ⟨1280123, by rfl⟩ : syracuseStep 1706831 = 2560247) B2560247
theorem B1919839 : Blo 1705053 1919839 := bstep (se 1 (by rfl) ⟨1439879, by rfl⟩ : syracuseStep 1919839 = 2879759) B2879759
theorem B1706847 : Blo 1705053 1706847 := bstep (se 1 (by rfl) ⟨1280135, by rfl⟩ : syracuseStep 1706847 = 2560271) B2560271
theorem B2558825 : Blo 1705053 2558825 := bstep (se 2 (by rfl) ⟨959559, by rfl⟩ : syracuseStep 2558825 = 1919119) B1919119
theorem B1706875 : Blo 1705053 1706875 := bstep (se 1 (by rfl) ⟨1280156, by rfl⟩ : syracuseStep 1706875 = 2560313) B2560313
theorem B4320175 : Blo 1705053 4320175 := bstep (se 1 (by rfl) ⟨3240131, by rfl⟩ : syracuseStep 4320175 = 6480263) B6480263
theorem B1706927 : Blo 1705053 1706927 := bstep (se 1 (by rfl) ⟨1280195, by rfl⟩ : syracuseStep 1706927 = 2560391) B2560391
theorem B2558903 : Blo 1705053 2558903 := bstep (se 1 (by rfl) ⟨1919177, by rfl⟩ : syracuseStep 2558903 = 3838355) B3838355
theorem B1706951 : Blo 1705053 1706951 := bstep (se 1 (by rfl) ⟨1280213, by rfl⟩ : syracuseStep 1706951 = 2560427) B2560427
theorem B2558939 : Blo 1705053 2558939 := bstep (se 1 (by rfl) ⟨1919204, by rfl⟩ : syracuseStep 2558939 = 3838409) B3838409
theorem B1706971 : Blo 1705053 1706971 := bstep (se 1 (by rfl) ⟨1280228, by rfl⟩ : syracuseStep 1706971 = 2560457) B2560457
theorem B10931219 : Blo 1705053 10931219 := bstep (se 1 (by rfl) ⟨8198414, by rfl⟩ : syracuseStep 10931219 = 16396829) B16396829
theorem B26258455 : Blo 1705053 26258455 := bstep (se 1 (by rfl) ⟨19693841, by rfl⟩ : syracuseStep 26258455 = 39387683) B39387683
theorem B1707047 : Blo 1705053 1707047 := bstep (se 1 (by rfl) ⟨1280285, by rfl⟩ : syracuseStep 1707047 = 2560571) B2560571
theorem B9718937 : Blo 1705053 9718937 := bstep (se 2 (by rfl) ⟨3644601, by rfl⟩ : syracuseStep 9718937 = 7289203) B7289203
theorem B7015619 : Blo 1705053 7015619 := bstep (se 1 (by rfl) ⟨5261714, by rfl⟩ : syracuseStep 7015619 = 10523429) B10523429
theorem B1920199 : Blo 1705053 1920199 := bstep (se 1 (by rfl) ⟨1440149, by rfl⟩ : syracuseStep 1920199 = 2880299) B2880299
theorem B437816609 : Blo 1705053 437816609 := bstep (se 2 (by rfl) ⟨164181228, by rfl⟩ : syracuseStep 437816609 = 328362457) B328362457
theorem B2428265 : Blo 1705053 2428265 := bstep (se 2 (by rfl) ⟨910599, by rfl⟩ : syracuseStep 2428265 = 1821199) B1821199
theorem B4320641 : Blo 1705053 4320641 := bstep (se 2 (by rfl) ⟨1620240, by rfl⟩ : syracuseStep 4320641 = 3240481) B3240481
theorem B8637839 : Blo 1705053 8637839 := bstep (se 1 (by rfl) ⟨6478379, by rfl⟩ : syracuseStep 8637839 = 12956759) B12956759
theorem B2878895 : Blo 1705053 2878895 := bstep (se 1 (by rfl) ⟨2159171, by rfl⟩ : syracuseStep 2878895 = 4318343) B4318343
theorem B2559407 : Blo 1705053 2559407 := bstep (se 1 (by rfl) ⟨1919555, by rfl⟩ : syracuseStep 2559407 = 3839111) B3839111
theorem B2731529 : Blo 1705053 2731529 := bstep (se 2 (by rfl) ⟨1024323, by rfl⟩ : syracuseStep 2731529 = 2048647) B2048647
theorem B2559497 : Blo 1705053 2559497 := bstep (se 2 (by rfl) ⟨959811, by rfl⟩ : syracuseStep 2559497 = 1919623) B1919623
theorem B2559527 : Blo 1705053 2559527 := bstep (se 1 (by rfl) ⟨1919645, by rfl⟩ : syracuseStep 2559527 = 3839291) B3839291
theorem B3075623 : Blo 1705053 3075623 := bstep (se 1 (by rfl) ⟨2306717, by rfl⟩ : syracuseStep 3075623 = 4613435) B4613435
theorem B2158159 : Blo 1705053 2158159 := bstep (se 1 (by rfl) ⟨1618619, by rfl⟩ : syracuseStep 2158159 = 3237239) B3237239
theorem B3837563 : Blo 1705053 3837563 := bstep (se 1 (by rfl) ⟨2878172, by rfl⟩ : syracuseStep 3837563 = 5756345) B5756345
theorem B10374779 : Blo 1705053 10374779 := bstep (se 1 (by rfl) ⟨7781084, by rfl⟩ : syracuseStep 10374779 = 15562169) B15562169
theorem B2559611 : Blo 1705053 2559611 := bstep (se 1 (by rfl) ⟨1919708, by rfl⟩ : syracuseStep 2559611 = 3839417) B3839417
theorem B6475403 : Blo 1705053 6475403 := bstep (se 1 (by rfl) ⟨4856552, by rfl⟩ : syracuseStep 6475403 = 9713105) B9713105
theorem B5754617 : Blo 1705053 5754617 := bstep (se 2 (by rfl) ⟨2157981, by rfl⟩ : syracuseStep 5754617 = 4315963) B4315963
theorem B3837689 : Blo 1705053 3837689 := bstep (se 2 (by rfl) ⟨1439133, by rfl⟩ : syracuseStep 3837689 = 2878267) B2878267
theorem B2559737 : Blo 1705053 2559737 := bstep (se 2 (by rfl) ⟨959901, by rfl⟩ : syracuseStep 2559737 = 1919803) B1919803
theorem B2879327 : Blo 1705053 2879327 := bstep (se 1 (by rfl) ⟨2159495, by rfl⟩ : syracuseStep 2879327 = 4318991) B4318991
theorem B2559839 : Blo 1705053 2559839 := bstep (se 1 (by rfl) ⟨1919879, by rfl⟩ : syracuseStep 2559839 = 3839759) B3839759
theorem B2559851 : Blo 1705053 2559851 := bstep (se 1 (by rfl) ⟨1919888, by rfl⟩ : syracuseStep 2559851 = 3839777) B3839777
theorem B5754887 : Blo 1705053 5754887 := bstep (se 1 (by rfl) ⟨4316165, by rfl⟩ : syracuseStep 5754887 = 8632331) B8632331
theorem B3837959 : Blo 1705053 3837959 := bstep (se 1 (by rfl) ⟨2878469, by rfl⟩ : syracuseStep 3837959 = 5756939) B5756939
theorem B3838031 : Blo 1705053 3838031 := bstep (se 1 (by rfl) ⟨2878523, by rfl⟩ : syracuseStep 3838031 = 5757047) B5757047
theorem B2560079 : Blo 1705053 2560079 := bstep (se 1 (by rfl) ⟨1920059, by rfl⟩ : syracuseStep 2560079 = 3840119) B3840119
theorem B5754995 : Blo 1705053 5754995 := bstep (se 1 (by rfl) ⟨4316246, by rfl⟩ : syracuseStep 5754995 = 8632493) B8632493
theorem B2560199 : Blo 1705053 2560199 := bstep (se 1 (by rfl) ⟨1920149, by rfl⟩ : syracuseStep 2560199 = 3840299) B3840299
theorem B2560361 : Blo 1705053 2560361 := bstep (se 2 (by rfl) ⟨960135, by rfl⟩ : syracuseStep 2560361 = 1920271) B1920271
theorem B2732395 : Blo 1705053 2732395 := bstep (se 1 (by rfl) ⟨2049296, by rfl⟩ : syracuseStep 2732395 = 4098593) B4098593
theorem B3240299 : Blo 1705053 3240299 := bstep (se 1 (by rfl) ⟨2430224, by rfl⟩ : syracuseStep 3240299 = 4860449) B4860449
theorem B5755265 : Blo 1705053 5755265 := bstep (se 2 (by rfl) ⟨2158224, by rfl⟩ : syracuseStep 5755265 = 4316449) B4316449
theorem B2879887 : Blo 1705053 2879887 := bstep (se 1 (by rfl) ⟨2159915, by rfl⟩ : syracuseStep 2879887 = 4319831) B4319831
theorem B2560439 : Blo 1705053 2560439 := bstep (se 1 (by rfl) ⟨1920329, by rfl⟩ : syracuseStep 2560439 = 3840659) B3840659
theorem B3838427 : Blo 1705053 3838427 := bstep (se 1 (by rfl) ⟨2878820, by rfl⟩ : syracuseStep 3838427 = 5757641) B5757641
theorem B2560475 : Blo 1705053 2560475 := bstep (se 1 (by rfl) ⟨1920356, by rfl⟩ : syracuseStep 2560475 = 3840713) B3840713
theorem B73781725 : Blo 1705053 73781725 := bstep (se 3 (by rfl) ⟨13834073, by rfl⟩ : syracuseStep 73781725 = 27668147) B27668147
theorem B19427849 : Blo 1705053 19427849 := bstep (se 2 (by rfl) ⟨7285443, by rfl⟩ : syracuseStep 19427849 = 14570887) B14570887
theorem B2159227 : Blo 1705053 2159227 := bstep (se 1 (by rfl) ⟨1619420, by rfl⟩ : syracuseStep 2159227 = 3238841) B3238841
theorem B2429689 : Blo 1705053 2429689 := bstep (se 2 (by rfl) ⟨911133, by rfl⟩ : syracuseStep 2429689 = 1822267) B1822267
theorem B2159455 : Blo 1705053 2159455 := bstep (se 1 (by rfl) ⟨1619591, by rfl⟩ : syracuseStep 2159455 = 3239183) B3239183
theorem B29143961 : Blo 1705053 29143961 := bstep (se 2 (by rfl) ⟨10928985, by rfl⟩ : syracuseStep 29143961 = 21857971) B21857971
theorem B3838895 : Blo 1705053 3838895 := bstep (se 1 (by rfl) ⟨2879171, by rfl⟩ : syracuseStep 3838895 = 5758343) B5758343
theorem B2880569 : Blo 1705053 2880569 := bstep (se 2 (by rfl) ⟨1080213, by rfl⟩ : syracuseStep 2880569 = 2160427) B2160427
theorem B5756075 : Blo 1705053 5756075 := bstep (se 1 (by rfl) ⟨4317056, by rfl⟩ : syracuseStep 5756075 = 8634113) B8634113
theorem B3839147 : Blo 1705053 3839147 := bstep (se 1 (by rfl) ⟨2879360, by rfl⟩ : syracuseStep 3839147 = 5758721) B5758721
theorem B9721079 : Blo 1705053 9721079 := bstep (se 1 (by rfl) ⟨7290809, by rfl⟩ : syracuseStep 9721079 = 14581619) B14581619
theorem B2160047 : Blo 1705053 2160047 := bstep (se 1 (by rfl) ⟨1620035, by rfl⟩ : syracuseStep 2160047 = 3240071) B3240071
theorem B8639945 : Blo 1705053 8639945 := bstep (se 2 (by rfl) ⟨3239979, by rfl⟩ : syracuseStep 8639945 = 6479959) B6479959
theorem B2733625 : Blo 1705053 2733625 := bstep (se 2 (by rfl) ⟨1025109, by rfl⟩ : syracuseStep 2733625 = 2050219) B2050219
theorem B12957245 : Blo 1705053 12957245 := bstep (se 3 (by rfl) ⟨2429483, by rfl⟩ : syracuseStep 12957245 = 4858967) B4858967
theorem B3888737 : Blo 1705053 3888737 := bstep (se 2 (by rfl) ⟨1458276, by rfl⟩ : syracuseStep 3888737 = 2916553) B2916553
theorem B41514677 : Blo 1705053 41514677 := bstep (se 5 (by rfl) ⟨1946000, by rfl⟩ : syracuseStep 41514677 = 3892001) B3892001
theorem B8632007 : Blo 1705053 8632007 := bstep (se 1 (by rfl) ⟨6474005, by rfl⟩ : syracuseStep 8632007 = 12948011) B12948011
theorem B5756615 : Blo 1705053 5756615 := bstep (se 1 (by rfl) ⟨4317461, by rfl⟩ : syracuseStep 5756615 = 8634923) B8634923
theorem B3839687 : Blo 1705053 3839687 := bstep (se 1 (by rfl) ⟨2879765, by rfl⟩ : syracuseStep 3839687 = 5759531) B5759531
theorem B8197955 : Blo 1705053 8197955 := bstep (se 1 (by rfl) ⟨6148466, by rfl⟩ : syracuseStep 8197955 = 12296933) B12296933
theorem B16390097 : Blo 1705053 16390097 := bstep (se 2 (by rfl) ⟨6146286, by rfl⟩ : syracuseStep 16390097 = 12292573) B12292573
theorem B8640593 : Blo 1705053 8640593 := bstep (se 2 (by rfl) ⟨3240222, by rfl⟩ : syracuseStep 8640593 = 6480445) B6480445
theorem B12466481 : Blo 1705053 12466481 := bstep (se 2 (by rfl) ⟨4674930, by rfl⟩ : syracuseStep 12466481 = 9349861) B9349861
theorem B12958217 : Blo 1705053 12958217 := bstep (se 2 (by rfl) ⟨4859331, by rfl⟩ : syracuseStep 12958217 = 9718663) B9718663
theorem B78821909 : Blo 1705053 78821909 := bstep (se 6 (by rfl) ⟨1847388, by rfl⟩ : syracuseStep 78821909 = 3694777) B3694777
theorem B5757479 : Blo 1705053 5757479 := bstep (se 1 (by rfl) ⟨4318109, by rfl⟩ : syracuseStep 5757479 = 8636219) B8636219
theorem B3840551 : Blo 1705053 3840551 := bstep (se 1 (by rfl) ⟨2880413, by rfl⟩ : syracuseStep 3840551 = 5760827) B5760827
theorem B202168963 : Blo 1705053 202168963 := bstep (se 1 (by rfl) ⟨151626722, by rfl⟩ : syracuseStep 202168963 = 303253445) B303253445
theorem B5757587 : Blo 1705053 5757587 := bstep (se 1 (by rfl) ⟨4318190, by rfl⟩ : syracuseStep 5757587 = 8636381) B8636381
theorem B5462777 : Blo 1705053 5462777 := bstep (se 2 (by rfl) ⟨2048541, by rfl⟩ : syracuseStep 5462777 = 4097083) B4097083
theorem B5757803 : Blo 1705053 5757803 := bstep (se 1 (by rfl) ⟨4318352, by rfl⟩ : syracuseStep 5757803 = 8636705) B8636705
theorem B5757857 : Blo 1705053 5757857 := bstep (se 2 (by rfl) ⟨2159196, by rfl⟩ : syracuseStep 5757857 = 4318393) B4318393
theorem B6478775 : Blo 1705053 6478775 := bstep (se 1 (by rfl) ⟨4859081, by rfl⟩ : syracuseStep 6478775 = 9718163) B9718163
theorem B3644423 : Blo 1705053 3644423 := bstep (se 1 (by rfl) ⟨2733317, by rfl⟩ : syracuseStep 3644423 = 5466635) B5466635
theorem B24583247 : Blo 1705053 24583247 := bstep (se 1 (by rfl) ⟨18437435, by rfl⟩ : syracuseStep 24583247 = 36874871) B36874871
theorem B224386199 : Blo 1705053 224386199 := bstep (se 1 (by rfl) ⟨168289649, by rfl⟩ : syracuseStep 224386199 = 336579299) B336579299
theorem B31112365 : Blo 1705053 31112365 := bstep (se 3 (by rfl) ⟨5833568, by rfl⟩ : syracuseStep 31112365 = 11667137) B11667137
theorem B78830765 : Blo 1705053 78830765 := bstep (se 3 (by rfl) ⟨14780768, by rfl⟩ : syracuseStep 78830765 = 29561537) B29561537
theorem B12950927 : Blo 1705053 12950927 := bstep (se 1 (by rfl) ⟨9713195, by rfl⟩ : syracuseStep 12950927 = 19426391) B19426391
theorem B5758451 : Blo 1705053 5758451 := bstep (se 1 (by rfl) ⟨4318838, by rfl⟩ : syracuseStep 5758451 = 8637677) B8637677
theorem B10927655 : Blo 1705053 10927655 := bstep (se 1 (by rfl) ⟨8195741, by rfl⟩ : syracuseStep 10927655 = 16391483) B16391483
theorem B20741771 : Blo 1705053 20741771 := bstep (se 1 (by rfl) ⟨15556328, by rfl⟩ : syracuseStep 20741771 = 31112657) B31112657
theorem B4857533 : Blo 1705053 4857533 := bstep (se 3 (by rfl) ⟨910787, by rfl⟩ : syracuseStep 4857533 = 1821575) B1821575
theorem B11837279 : Blo 1705053 11837279 := bstep (se 1 (by rfl) ⟨8877959, by rfl⟩ : syracuseStep 11837279 = 17755919) B17755919
theorem B12304223 : Blo 1705053 12304223 := bstep (se 1 (by rfl) ⟨9228167, by rfl⟩ : syracuseStep 12304223 = 18456335) B18456335
theorem B9715565 : Blo 1705053 9715565 := bstep (se 3 (by rfl) ⟨1821668, by rfl⟩ : syracuseStep 9715565 = 3643337) B3643337
theorem B6479777 : Blo 1705053 6479777 := bstep (se 2 (by rfl) ⟨2429916, by rfl⟩ : syracuseStep 6479777 = 4859833) B4859833
theorem B12959675 : Blo 1705053 12959675 := bstep (se 1 (by rfl) ⟨9719756, by rfl⟩ : syracuseStep 12959675 = 19439513) B19439513
theorem B4317209 : Blo 1705053 4317209 := bstep (se 2 (by rfl) ⟨1618953, by rfl⟩ : syracuseStep 4317209 = 3237907) B3237907
theorem B42647651 : Blo 1705053 42647651 := bstep (se 1 (by rfl) ⟨31985738, by rfl⟩ : syracuseStep 42647651 = 63971477) B63971477
theorem B12951899 : Blo 1705053 12951899 := bstep (se 1 (by rfl) ⟨9713924, by rfl⟩ : syracuseStep 12951899 = 19427849) B19427849
theorem B10936777 : Blo 1705053 10936777 := bstep (se 2 (by rfl) ⟨4101291, by rfl⟩ : syracuseStep 10936777 = 8202583) B8202583
theorem B2048695 : Blo 1705053 2048695 := bstep (se 1 (by rfl) ⟨1536521, by rfl⟩ : syracuseStep 2048695 = 3073043) B3073043
theorem B33243949 : Blo 1705053 33243949 := bstep (se 3 (by rfl) ⟨6233240, by rfl⟩ : syracuseStep 33243949 = 12466481) B12466481
theorem B6480719 : Blo 1705053 6480719 := bstep (se 1 (by rfl) ⟨4860539, by rfl⟩ : syracuseStep 6480719 = 9721079) B9721079
theorem B269558617 : Blo 1705053 269558617 := bstep (se 2 (by rfl) ⟨101084481, by rfl⟩ : syracuseStep 269558617 = 202168963) B202168963
theorem B5465033 : Blo 1705053 5465033 := bstep (se 2 (by rfl) ⟨2049387, by rfl⟩ : syracuseStep 5465033 = 4098775) B4098775
theorem B5759963 : Blo 1705053 5759963 := bstep (se 1 (by rfl) ⟨4319972, by rfl⟩ : syracuseStep 5759963 = 8639945) B8639945
theorem B448578647 : Blo 1705053 448578647 := bstep (se 1 (by rfl) ⟨336433985, by rfl⟩ : syracuseStep 448578647 = 672867971) B672867971
theorem B5760125 : Blo 1705053 5760125 := bstep (se 3 (by rfl) ⟨1080023, by rfl⟩ : syracuseStep 5760125 = 2160047) B2160047
theorem B9225359 : Blo 1705053 9225359 := bstep (se 1 (by rfl) ⟨6919019, by rfl⟩ : syracuseStep 9225359 = 13838039) B13838039
theorem B5465303 : Blo 1705053 5465303 := bstep (se 1 (by rfl) ⟨4098977, by rfl⟩ : syracuseStep 5465303 = 8197955) B8197955
theorem B5760233 : Blo 1705053 5760233 := bstep (se 2 (by rfl) ⟨2160087, by rfl⟩ : syracuseStep 5760233 = 4320175) B4320175
theorem B4375795 : Blo 1705053 4375795 := bstep (se 1 (by rfl) ⟨3281846, by rfl⟩ : syracuseStep 4375795 = 6563693) B6563693
theorem B1705247 : Blo 1705053 1705247 := bstep (se 1 (by rfl) ⟨1278935, by rfl⟩ : syracuseStep 1705247 = 2557871) B2557871
theorem B1705307 : Blo 1705053 1705307 := bstep (se 1 (by rfl) ⟨1278980, by rfl⟩ : syracuseStep 1705307 = 2557961) B2557961
theorem B7284077 : Blo 1705053 7284077 := bstep (se 3 (by rfl) ⟨1365764, by rfl⟩ : syracuseStep 7284077 = 2731529) B2731529
theorem B12961133 : Blo 1705053 12961133 := bstep (se 3 (by rfl) ⟨2430212, by rfl⟩ : syracuseStep 12961133 = 4860425) B4860425
theorem B1705327 : Blo 1705053 1705327 := bstep (se 1 (by rfl) ⟨1278995, by rfl⟩ : syracuseStep 1705327 = 2557991) B2557991
theorem B5760395 : Blo 1705053 5760395 := bstep (se 1 (by rfl) ⟨4320296, by rfl⟩ : syracuseStep 5760395 = 8640593) B8640593
theorem B1705383 : Blo 1705053 1705383 := bstep (se 1 (by rfl) ⟨1279037, by rfl⟩ : syracuseStep 1705383 = 2558075) B2558075
theorem B1705467 : Blo 1705053 1705467 := bstep (se 1 (by rfl) ⟨1279100, by rfl⟩ : syracuseStep 1705467 = 2558201) B2558201
theorem B1705535 : Blo 1705053 1705535 := bstep (se 1 (by rfl) ⟨1279151, by rfl⟩ : syracuseStep 1705535 = 2558303) B2558303
theorem B1705543 : Blo 1705053 1705543 := bstep (se 1 (by rfl) ⟨1279157, by rfl⟩ : syracuseStep 1705543 = 2558315) B2558315
theorem B14575261 : Blo 1705053 14575261 := bstep (se 3 (by rfl) ⟨2732861, by rfl⟩ : syracuseStep 14575261 = 5465723) B5465723
theorem B3458747 : Blo 1705053 3458747 := bstep (se 1 (by rfl) ⟨2594060, by rfl⟩ : syracuseStep 3458747 = 5188121) B5188121
theorem B1918687 : Blo 1705053 1918687 := bstep (se 1 (by rfl) ⟨1439015, by rfl⟩ : syracuseStep 1918687 = 2878031) B2878031
theorem B1705695 : Blo 1705053 1705695 := bstep (se 1 (by rfl) ⟨1279271, by rfl⟩ : syracuseStep 1705695 = 2558543) B2558543
theorem B1705775 : Blo 1705053 1705775 := bstep (se 1 (by rfl) ⟨1279331, by rfl⟩ : syracuseStep 1705775 = 2558663) B2558663
theorem B2557751 : Blo 1705053 2557751 := bstep (se 1 (by rfl) ⟨1918313, by rfl⟩ : syracuseStep 2557751 = 3836627) B3836627
theorem B1705883 : Blo 1705053 1705883 := bstep (se 1 (by rfl) ⟨1279412, by rfl⟩ : syracuseStep 1705883 = 2558825) B2558825
theorem B1705935 : Blo 1705053 1705935 := bstep (se 1 (by rfl) ⟨1279451, by rfl⟩ : syracuseStep 1705935 = 2558903) B2558903
theorem B4319183 : Blo 1705053 4319183 := bstep (se 1 (by rfl) ⟨3239387, by rfl⟩ : syracuseStep 4319183 = 6478775) B6478775
theorem B1705959 : Blo 1705053 1705959 := bstep (se 1 (by rfl) ⟨1279469, by rfl⟩ : syracuseStep 1705959 = 2558939) B2558939
theorem B2877545 : Blo 1705053 2877545 := bstep (se 2 (by rfl) ⟨1079079, by rfl⟩ : syracuseStep 2877545 = 2158159) B2158159
theorem B2558057 : Blo 1705053 2558057 := bstep (se 2 (by rfl) ⟨959271, by rfl⟩ : syracuseStep 2558057 = 1918543) B1918543
theorem B52553843 : Blo 1705053 52553843 := bstep (se 1 (by rfl) ⟨39415382, by rfl⟩ : syracuseStep 52553843 = 78830765) B78830765
theorem B18450625 : Blo 1705053 18450625 := bstep (se 2 (by rfl) ⟨6918984, by rfl⟩ : syracuseStep 18450625 = 13837969) B13837969
theorem B4098313 : Blo 1705053 4098313 := bstep (se 2 (by rfl) ⟨1536867, by rfl⟩ : syracuseStep 4098313 = 3073735) B3073735
theorem B5835037 : Blo 1705053 5835037 := bstep (se 3 (by rfl) ⟨1094069, by rfl⟩ : syracuseStep 5835037 = 2188139) B2188139
theorem B1919263 : Blo 1705053 1919263 := bstep (se 1 (by rfl) ⟨1439447, by rfl⟩ : syracuseStep 1919263 = 2878895) B2878895
theorem B1706271 : Blo 1705053 1706271 := bstep (se 1 (by rfl) ⟨1279703, by rfl⟩ : syracuseStep 1706271 = 2559407) B2559407
theorem B1706331 : Blo 1705053 1706331 := bstep (se 1 (by rfl) ⟨1279748, by rfl⟩ : syracuseStep 1706331 = 2559497) B2559497
theorem B7285103 : Blo 1705053 7285103 := bstep (se 1 (by rfl) ⟨5463827, by rfl⟩ : syracuseStep 7285103 = 10927655) B10927655
theorem B1706351 : Blo 1705053 1706351 := bstep (se 1 (by rfl) ⟨1279763, by rfl⟩ : syracuseStep 1706351 = 2559527) B2559527
theorem B2050415 : Blo 1705053 2050415 := bstep (se 1 (by rfl) ⟨1537811, by rfl⟩ : syracuseStep 2050415 = 3075623) B3075623
theorem B2558375 : Blo 1705053 2558375 := bstep (se 1 (by rfl) ⟨1918781, by rfl⟩ : syracuseStep 2558375 = 3837563) B3837563
theorem B6916519 : Blo 1705053 6916519 := bstep (se 1 (by rfl) ⟨5187389, by rfl⟩ : syracuseStep 6916519 = 10374779) B10374779
theorem B1706407 : Blo 1705053 1706407 := bstep (se 1 (by rfl) ⟨1279805, by rfl⟩ : syracuseStep 1706407 = 2559611) B2559611
theorem B3238355 : Blo 1705053 3238355 := bstep (se 1 (by rfl) ⟨2428766, by rfl⟩ : syracuseStep 3238355 = 4857533) B4857533
theorem B3836411 : Blo 1705053 3836411 := bstep (se 1 (by rfl) ⟨2877308, by rfl⟩ : syracuseStep 3836411 = 5754617) B5754617
theorem B2558459 : Blo 1705053 2558459 := bstep (se 1 (by rfl) ⟨1918844, by rfl⟩ : syracuseStep 2558459 = 3837689) B3837689
theorem B1706491 : Blo 1705053 1706491 := bstep (se 1 (by rfl) ⟨1279868, by rfl⟩ : syracuseStep 1706491 = 2559737) B2559737
theorem B1919551 : Blo 1705053 1919551 := bstep (se 1 (by rfl) ⟨1439663, by rfl⟩ : syracuseStep 1919551 = 2879327) B2879327
theorem B1706559 : Blo 1705053 1706559 := bstep (se 1 (by rfl) ⟨1279919, by rfl⟩ : syracuseStep 1706559 = 2559839) B2559839
theorem B7891519 : Blo 1705053 7891519 := bstep (se 1 (by rfl) ⟨5918639, by rfl⟩ : syracuseStep 7891519 = 11837279) B11837279
theorem B8202815 : Blo 1705053 8202815 := bstep (se 1 (by rfl) ⟨6152111, by rfl⟩ : syracuseStep 8202815 = 12304223) B12304223
theorem B1706567 : Blo 1705053 1706567 := bstep (se 1 (by rfl) ⟨1279925, by rfl⟩ : syracuseStep 1706567 = 2559851) B2559851
theorem B4319851 : Blo 1705053 4319851 := bstep (se 1 (by rfl) ⟨3239888, by rfl⟩ : syracuseStep 4319851 = 6479777) B6479777
theorem B3836537 : Blo 1705053 3836537 := bstep (se 2 (by rfl) ⟨1438701, by rfl⟩ : syracuseStep 3836537 = 2877403) B2877403
theorem B2558585 : Blo 1705053 2558585 := bstep (se 2 (by rfl) ⟨959469, by rfl⟩ : syracuseStep 2558585 = 1918939) B1918939
theorem B3836591 : Blo 1705053 3836591 := bstep (se 1 (by rfl) ⟨2877443, by rfl⟩ : syracuseStep 3836591 = 5754887) B5754887
theorem B2558639 : Blo 1705053 2558639 := bstep (se 1 (by rfl) ⟨1918979, by rfl⟩ : syracuseStep 2558639 = 3837959) B3837959
theorem B2558687 : Blo 1705053 2558687 := bstep (se 1 (by rfl) ⟨1919015, by rfl⟩ : syracuseStep 2558687 = 3838031) B3838031
theorem B1706719 : Blo 1705053 1706719 := bstep (se 1 (by rfl) ⟨1280039, by rfl⟩ : syracuseStep 1706719 = 2560079) B2560079
theorem B3836663 : Blo 1705053 3836663 := bstep (se 1 (by rfl) ⟨2877497, by rfl⟩ : syracuseStep 3836663 = 5754995) B5754995
theorem B8203027 : Blo 1705053 8203027 := bstep (se 1 (by rfl) ⟨6152270, by rfl⟩ : syracuseStep 8203027 = 12304541) B12304541
theorem B1706799 : Blo 1705053 1706799 := bstep (se 1 (by rfl) ⟨1280099, by rfl⟩ : syracuseStep 1706799 = 2560199) B2560199
theorem B4320155 : Blo 1705053 4320155 := bstep (se 1 (by rfl) ⟨3240116, by rfl⟩ : syracuseStep 4320155 = 6480233) B6480233
theorem B1706907 : Blo 1705053 1706907 := bstep (se 1 (by rfl) ⟨1280180, by rfl⟩ : syracuseStep 1706907 = 2560361) B2560361
theorem B3836843 : Blo 1705053 3836843 := bstep (se 1 (by rfl) ⟨2877632, by rfl⟩ : syracuseStep 3836843 = 5755265) B5755265
theorem B1706959 : Blo 1705053 1706959 := bstep (se 1 (by rfl) ⟨1280219, by rfl⟩ : syracuseStep 1706959 = 2560439) B2560439
theorem B2558951 : Blo 1705053 2558951 := bstep (se 1 (by rfl) ⟨1919213, by rfl⟩ : syracuseStep 2558951 = 3838427) B3838427
theorem B1706983 : Blo 1705053 1706983 := bstep (se 1 (by rfl) ⟨1280237, by rfl⟩ : syracuseStep 1706983 = 2560475) B2560475
theorem B2559209 : Blo 1705053 2559209 := bstep (se 2 (by rfl) ⟨959703, by rfl⟩ : syracuseStep 2559209 = 1919407) B1919407
theorem B4320499 : Blo 1705053 4320499 := bstep (se 1 (by rfl) ⟨3240374, by rfl⟩ : syracuseStep 4320499 = 6480749) B6480749
theorem B2559263 : Blo 1705053 2559263 := bstep (se 1 (by rfl) ⟨1919447, by rfl⟩ : syracuseStep 2559263 = 3838895) B3838895
theorem B1920379 : Blo 1705053 1920379 := bstep (se 1 (by rfl) ⟨1440284, by rfl⟩ : syracuseStep 1920379 = 2880569) B2880569
theorem B3837383 : Blo 1705053 3837383 := bstep (se 1 (by rfl) ⟨2878037, by rfl⟩ : syracuseStep 3837383 = 5756075) B5756075
theorem B2559431 : Blo 1705053 2559431 := bstep (se 1 (by rfl) ⟨1919573, by rfl⟩ : syracuseStep 2559431 = 3839147) B3839147
theorem B2878969 : Blo 1705053 2878969 := bstep (se 2 (by rfl) ⟨1079613, by rfl⟩ : syracuseStep 2878969 = 2159227) B2159227
theorem B6475373 : Blo 1705053 6475373 := bstep (se 3 (by rfl) ⟨1214132, by rfl⟩ : syracuseStep 6475373 = 2428265) B2428265
theorem B5467763 : Blo 1705053 5467763 := bstep (se 1 (by rfl) ⟨4100822, by rfl⟩ : syracuseStep 5467763 = 8201645) B8201645
theorem B3239585 : Blo 1705053 3239585 := bstep (se 2 (by rfl) ⟨1214844, by rfl⟩ : syracuseStep 3239585 = 2429689) B2429689
theorem B2158255 : Blo 1705053 2158255 := bstep (se 1 (by rfl) ⟨1618691, by rfl⟩ : syracuseStep 2158255 = 3237383) B3237383
theorem B8638163 : Blo 1705053 8638163 := bstep (se 1 (by rfl) ⟨6478622, by rfl⟩ : syracuseStep 8638163 = 12957245) B12957245
theorem B2592491 : Blo 1705053 2592491 := bstep (se 1 (by rfl) ⟨1944368, by rfl⟩ : syracuseStep 2592491 = 3888737) B3888737
theorem B2879239 : Blo 1705053 2879239 := bstep (se 1 (by rfl) ⟨2159429, by rfl⟩ : syracuseStep 2879239 = 4318859) B4318859
theorem B27676451 : Blo 1705053 27676451 := bstep (se 1 (by rfl) ⟨20757338, by rfl⟩ : syracuseStep 27676451 = 41514677) B41514677
theorem B2879273 : Blo 1705053 2879273 := bstep (se 2 (by rfl) ⟨1079727, by rfl⟩ : syracuseStep 2879273 = 2159455) B2159455
theorem B2559785 : Blo 1705053 2559785 := bstep (se 2 (by rfl) ⟨959919, by rfl⟩ : syracuseStep 2559785 = 1919839) B1919839
theorem B5754671 : Blo 1705053 5754671 := bstep (se 1 (by rfl) ⟨4316003, by rfl⟩ : syracuseStep 5754671 = 8632007) B8632007
theorem B3837743 : Blo 1705053 3837743 := bstep (se 1 (by rfl) ⟨2878307, by rfl⟩ : syracuseStep 3837743 = 5756615) B5756615
theorem B2559791 : Blo 1705053 2559791 := bstep (se 1 (by rfl) ⟨1919843, by rfl⟩ : syracuseStep 2559791 = 3839687) B3839687
theorem B2560265 : Blo 1705053 2560265 := bstep (se 2 (by rfl) ⟨960099, by rfl⟩ : syracuseStep 2560265 = 1920199) B1920199
theorem B2076959 : Blo 1705053 2076959 := bstep (se 1 (by rfl) ⟨1557719, by rfl⟩ : syracuseStep 2076959 = 3115439) B3115439
theorem B8638811 : Blo 1705053 8638811 := bstep (se 1 (by rfl) ⟨6479108, by rfl⟩ : syracuseStep 8638811 = 12958217) B12958217
theorem B52547939 : Blo 1705053 52547939 := bstep (se 1 (by rfl) ⟨39410954, by rfl⟩ : syracuseStep 52547939 = 78821909) B78821909
theorem B3838319 : Blo 1705053 3838319 := bstep (se 1 (by rfl) ⟨2878739, by rfl⟩ : syracuseStep 3838319 = 5757479) B5757479
theorem B2560367 : Blo 1705053 2560367 := bstep (se 1 (by rfl) ⟨1920275, by rfl⟩ : syracuseStep 2560367 = 3840551) B3840551
theorem B7385519 : Blo 1705053 7385519 := bstep (se 1 (by rfl) ⟨5539139, by rfl⟩ : syracuseStep 7385519 = 11078279) B11078279
theorem B3838391 : Blo 1705053 3838391 := bstep (se 1 (by rfl) ⟨2878793, by rfl⟩ : syracuseStep 3838391 = 5757587) B5757587
theorem B3641851 : Blo 1705053 3641851 := bstep (se 1 (by rfl) ⟨2731388, by rfl⟩ : syracuseStep 3641851 = 5462777) B5462777
theorem B2879995 : Blo 1705053 2879995 := bstep (se 1 (by rfl) ⟨2159996, by rfl⟩ : syracuseStep 2879995 = 4319993) B4319993
theorem B3838535 : Blo 1705053 3838535 := bstep (se 1 (by rfl) ⟨2878901, by rfl⟩ : syracuseStep 3838535 = 5757803) B5757803
theorem B3838571 : Blo 1705053 3838571 := bstep (se 1 (by rfl) ⟨2878928, by rfl⟩ : syracuseStep 3838571 = 5757857) B5757857
theorem B2429615 : Blo 1705053 2429615 := bstep (se 1 (by rfl) ⟨1822211, by rfl⟩ : syracuseStep 2429615 = 3644423) B3644423
theorem B7287479 : Blo 1705053 7287479 := bstep (se 1 (by rfl) ⟨5465609, by rfl⟩ : syracuseStep 7287479 = 10931219) B10931219
theorem B16388831 : Blo 1705053 16388831 := bstep (se 1 (by rfl) ⟨12291623, by rfl⟩ : syracuseStep 16388831 = 24583247) B24583247
theorem B7385849 : Blo 1705053 7385849 := bstep (se 2 (by rfl) ⟨2769693, by rfl⟩ : syracuseStep 7385849 = 5539387) B5539387
theorem B149590799 : Blo 1705053 149590799 := bstep (se 1 (by rfl) ⟨112193099, by rfl⟩ : syracuseStep 149590799 = 224386199) B224386199
theorem B291877739 : Blo 1705053 291877739 := bstep (se 1 (by rfl) ⟨218908304, by rfl⟩ : syracuseStep 291877739 = 437816609) B437816609
theorem B2880427 : Blo 1705053 2880427 := bstep (se 1 (by rfl) ⟨2160320, by rfl⟩ : syracuseStep 2880427 = 4320641) B4320641
theorem B3838967 : Blo 1705053 3838967 := bstep (se 1 (by rfl) ⟨2879225, by rfl⟩ : syracuseStep 3838967 = 5758451) B5758451
theorem B6477043 : Blo 1705053 6477043 := bstep (se 1 (by rfl) ⟨4857782, by rfl⟩ : syracuseStep 6477043 = 9715565) B9715565
theorem B8639783 : Blo 1705053 8639783 := bstep (se 1 (by rfl) ⟨6479837, by rfl⟩ : syracuseStep 8639783 = 12959675) B12959675
theorem B3839327 : Blo 1705053 3839327 := bstep (se 1 (by rfl) ⟨2879495, by rfl⟩ : syracuseStep 3839327 = 5758991) B5758991
theorem B2160199 : Blo 1705053 2160199 := bstep (se 1 (by rfl) ⟨1620149, by rfl⟩ : syracuseStep 2160199 = 3240299) B3240299
theorem B3839723 : Blo 1705053 3839723 := bstep (se 1 (by rfl) ⟨2879792, by rfl⟩ : syracuseStep 3839723 = 5759585) B5759585
theorem B4609847 : Blo 1705053 4609847 := bstep (se 1 (by rfl) ⟨3457385, by rfl⟩ : syracuseStep 4609847 = 6914771) B6914771
theorem B3643193 : Blo 1705053 3643193 := bstep (se 2 (by rfl) ⟨1366197, by rfl⟩ : syracuseStep 3643193 = 2732395) B2732395
theorem B18708317 : Blo 1705053 18708317 := bstep (se 3 (by rfl) ⟨3507809, by rfl⟩ : syracuseStep 18708317 = 7015619) B7015619
theorem B8632169 : Blo 1705053 8632169 := bstep (se 2 (by rfl) ⟨3237063, by rfl⟩ : syracuseStep 8632169 = 6474127) B6474127
theorem B5756777 : Blo 1705053 5756777 := bstep (se 2 (by rfl) ⟨2158791, by rfl⟩ : syracuseStep 5756777 = 4317583) B4317583
theorem B3839849 : Blo 1705053 3839849 := bstep (se 2 (by rfl) ⟨1439943, by rfl⟩ : syracuseStep 3839849 = 2879887) B2879887
theorem B19429307 : Blo 1705053 19429307 := bstep (se 1 (by rfl) ⟨14571980, by rfl⟩ : syracuseStep 19429307 = 29143961) B29143961
theorem B98375633 : Blo 1705053 98375633 := bstep (se 2 (by rfl) ⟨36890862, by rfl⟩ : syracuseStep 98375633 = 73781725) B73781725
theorem B8198279 : Blo 1705053 8198279 := bstep (se 1 (by rfl) ⟨6148709, by rfl⟩ : syracuseStep 8198279 = 12297419) B12297419
theorem B5757209 : Blo 1705053 5757209 := bstep (se 2 (by rfl) ⟨2158953, by rfl⟩ : syracuseStep 5757209 = 4317907) B4317907
theorem B8198779 : Blo 1705053 8198779 := bstep (se 1 (by rfl) ⟨6149084, by rfl⟩ : syracuseStep 8198779 = 12298169) B12298169
theorem B10926731 : Blo 1705053 10926731 := bstep (se 1 (by rfl) ⟨8195048, by rfl⟩ : syracuseStep 10926731 = 16390097) B16390097
theorem B3840695 : Blo 1705053 3840695 := bstep (se 1 (by rfl) ⟨2880521, by rfl⟩ : syracuseStep 3840695 = 5761043) B5761043
theorem B35011273 : Blo 1705053 35011273 := bstep (se 2 (by rfl) ⟨13129227, by rfl⟩ : syracuseStep 35011273 = 26258455) B26258455
theorem B17505143 : Blo 1705053 17505143 := bstep (se 1 (by rfl) ⟨13128857, by rfl⟩ : syracuseStep 17505143 = 26257715) B26257715
theorem B41483153 : Blo 1705053 41483153 := bstep (se 2 (by rfl) ⟨15556182, by rfl⟩ : syracuseStep 41483153 = 31112365) B31112365
theorem B4316075 : Blo 1705053 4316075 := bstep (se 1 (by rfl) ⟨3237056, by rfl⟩ : syracuseStep 4316075 = 6474113) B6474113
theorem B17751059 : Blo 1705053 17751059 := bstep (se 1 (by rfl) ⟨13313294, by rfl⟩ : syracuseStep 17751059 = 26626589) B26626589
theorem B4922491 : Blo 1705053 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B6478987 : Blo 1705053 6478987 := bstep (se 1 (by rfl) ⟨4859240, by rfl⟩ : syracuseStep 6478987 = 9718481) B9718481
theorem B8641889 : Blo 1705053 8641889 := bstep (se 2 (by rfl) ⟨3240708, by rfl⟩ : syracuseStep 8641889 = 6481417) B6481417
theorem B3644833 : Blo 1705053 3644833 := bstep (se 2 (by rfl) ⟨1366812, by rfl⟩ : syracuseStep 3644833 = 2733625) B2733625
theorem B6479291 : Blo 1705053 6479291 := bstep (se 1 (by rfl) ⟨4859468, by rfl⟩ : syracuseStep 6479291 = 9718937) B9718937
theorem B8633951 : Blo 1705053 8633951 := bstep (se 1 (by rfl) ⟨6475463, by rfl⟩ : syracuseStep 8633951 = 12950927) B12950927
theorem B5758559 : Blo 1705053 5758559 := bstep (se 1 (by rfl) ⟨4318919, by rfl⟩ : syracuseStep 5758559 = 8637839) B8637839
theorem B13827847 : Blo 1705053 13827847 := bstep (se 1 (by rfl) ⟨10370885, by rfl⟩ : syracuseStep 13827847 = 20741771) B20741771
theorem B4316935 : Blo 1705053 4316935 := bstep (se 1 (by rfl) ⟨3237701, by rfl⟩ : syracuseStep 4316935 = 6475403) B6475403
theorem B8634599 : Blo 1705053 8634599 := bstep (se 1 (by rfl) ⟨6475949, by rfl⟩ : syracuseStep 8634599 = 12951899) B12951899
theorem B5759207 : Blo 1705053 5759207 := bstep (se 1 (by rfl) ⟨4319405, by rfl⟩ : syracuseStep 5759207 = 8638811) B8638811
theorem B24600833 : Blo 1705053 24600833 := bstep (se 2 (by rfl) ⟨9225312, by rfl⟩ : syracuseStep 24600833 = 18450625) B18450625
theorem B5464417 : Blo 1705053 5464417 := bstep (se 2 (by rfl) ⟨2049156, by rfl⟩ : syracuseStep 5464417 = 4098313) B4098313
theorem B4858319 : Blo 1705053 4858319 := bstep (se 1 (by rfl) ⟨3643739, by rfl⟩ : syracuseStep 4858319 = 7287479) B7287479
theorem B4923899 : Blo 1705053 4923899 := bstep (se 1 (by rfl) ⟨3692924, by rfl⟩ : syracuseStep 4923899 = 7385849) B7385849
theorem B194585159 : Blo 1705053 194585159 := bstep (se 1 (by rfl) ⟨145938869, by rfl⟩ : syracuseStep 194585159 = 291877739) B291877739
theorem B14582369 : Blo 1705053 14582369 := bstep (se 2 (by rfl) ⟨5468388, by rfl⟩ : syracuseStep 14582369 = 10936777) B10936777
theorem B5538557 : Blo 1705053 5538557 := bstep (se 3 (by rfl) ⟨1038479, by rfl⟩ : syracuseStep 5538557 = 2076959) B2076959
theorem B5759801 : Blo 1705053 5759801 := bstep (se 2 (by rfl) ⟨2159925, by rfl⟩ : syracuseStep 5759801 = 4319851) B4319851
theorem B5759855 : Blo 1705053 5759855 := bstep (se 1 (by rfl) ⟨4319891, by rfl⟩ : syracuseStep 5759855 = 8639783) B8639783
theorem B10937369 : Blo 1705053 10937369 := bstep (se 2 (by rfl) ⟨4101513, by rfl⟩ : syracuseStep 10937369 = 8203027) B8203027
theorem B19694717 : Blo 1705053 19694717 := bstep (se 3 (by rfl) ⟨3692759, by rfl⟩ : syracuseStep 19694717 = 7385519) B7385519
theorem B1705167 : Blo 1705053 1705167 := bstep (se 1 (by rfl) ⟨1278875, by rfl⟩ : syracuseStep 1705167 = 2557751) B2557751
theorem B3073231 : Blo 1705053 3073231 := bstep (se 1 (by rfl) ⟨2304923, by rfl⟩ : syracuseStep 3073231 = 4609847) B4609847
theorem B12952871 : Blo 1705053 12952871 := bstep (se 1 (by rfl) ⟨9714653, by rfl⟩ : syracuseStep 12952871 = 19429307) B19429307
theorem B1918363 : Blo 1705053 1918363 := bstep (se 1 (by rfl) ⟨1438772, by rfl⟩ : syracuseStep 1918363 = 2877545) B2877545
theorem B1705371 : Blo 1705053 1705371 := bstep (se 1 (by rfl) ⟨1279028, by rfl⟩ : syracuseStep 1705371 = 2558057) B2558057
theorem B5465519 : Blo 1705053 5465519 := bstep (se 1 (by rfl) ⟨4099139, by rfl⟩ : syracuseStep 5465519 = 8198279) B8198279
theorem B6563321 : Blo 1705053 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B177301061 : Blo 1705053 177301061 := bstep (se 4 (by rfl) ⟨16621974, by rfl⟩ : syracuseStep 177301061 = 33243949) B33243949
theorem B1705583 : Blo 1705053 1705583 := bstep (se 1 (by rfl) ⟨1279187, by rfl⟩ : syracuseStep 1705583 = 2558375) B2558375
theorem B5834393 : Blo 1705053 5834393 := bstep (se 2 (by rfl) ⟨2187897, by rfl⟩ : syracuseStep 5834393 = 4375795) B4375795
theorem B8636057 : Blo 1705053 8636057 := bstep (se 2 (by rfl) ⟨3238521, by rfl⟩ : syracuseStep 8636057 = 6477043) B6477043
theorem B5760665 : Blo 1705053 5760665 := bstep (se 2 (by rfl) ⟨2160249, by rfl⟩ : syracuseStep 5760665 = 4320499) B4320499
theorem B2557607 : Blo 1705053 2557607 := bstep (se 1 (by rfl) ⟨1918205, by rfl⟩ : syracuseStep 2557607 = 3836411) B3836411
theorem B1705639 : Blo 1705053 1705639 := bstep (se 1 (by rfl) ⟨1279229, by rfl⟩ : syracuseStep 1705639 = 2558459) B2558459
theorem B2557691 : Blo 1705053 2557691 := bstep (se 1 (by rfl) ⟨1918268, by rfl⟩ : syracuseStep 2557691 = 3836537) B3836537
theorem B1705723 : Blo 1705053 1705723 := bstep (se 1 (by rfl) ⟨1279292, by rfl⟩ : syracuseStep 1705723 = 2558585) B2558585
theorem B7284487 : Blo 1705053 7284487 := bstep (se 1 (by rfl) ⟨5463365, by rfl⟩ : syracuseStep 7284487 = 10926731) B10926731
theorem B2557727 : Blo 1705053 2557727 := bstep (se 1 (by rfl) ⟨1918295, by rfl⟩ : syracuseStep 2557727 = 3836591) B3836591
theorem B1705759 : Blo 1705053 1705759 := bstep (se 1 (by rfl) ⟨1279319, by rfl⟩ : syracuseStep 1705759 = 2558639) B2558639
theorem B1705791 : Blo 1705053 1705791 := bstep (se 1 (by rfl) ⟨1279343, by rfl⟩ : syracuseStep 1705791 = 2558687) B2558687
theorem B2557775 : Blo 1705053 2557775 := bstep (se 1 (by rfl) ⟨1918331, by rfl⟩ : syracuseStep 2557775 = 3836663) B3836663
theorem B4859777 : Blo 1705053 4859777 := bstep (se 2 (by rfl) ⟨1822416, by rfl⟩ : syracuseStep 4859777 = 3644833) B3644833
theorem B2877383 : Blo 1705053 2877383 := bstep (se 1 (by rfl) ⟨2158037, by rfl⟩ : syracuseStep 2877383 = 4316075) B4316075
theorem B2557895 : Blo 1705053 2557895 := bstep (se 1 (by rfl) ⟨1918421, by rfl⟩ : syracuseStep 2557895 = 3836843) B3836843
theorem B1705967 : Blo 1705053 1705967 := bstep (se 1 (by rfl) ⟨1279475, by rfl⟩ : syracuseStep 1705967 = 2558951) B2558951
theorem B73803869 : Blo 1705053 73803869 := bstep (se 3 (by rfl) ⟨13838225, by rfl⟩ : syracuseStep 73803869 = 27676451) B27676451
theorem B1706139 : Blo 1705053 1706139 := bstep (se 1 (by rfl) ⟨1279604, by rfl⟩ : syracuseStep 1706139 = 2559209) B2559209
theorem B1706175 : Blo 1705053 1706175 := bstep (se 1 (by rfl) ⟨1279631, by rfl⟩ : syracuseStep 1706175 = 2559263) B2559263
theorem B19433681 : Blo 1705053 19433681 := bstep (se 2 (by rfl) ⟨7287630, by rfl⟩ : syracuseStep 19433681 = 14575261) B14575261
theorem B2877673 : Blo 1705053 2877673 := bstep (se 2 (by rfl) ⟨1079127, by rfl⟩ : syracuseStep 2877673 = 2158255) B2158255
theorem B5761259 : Blo 1705053 5761259 := bstep (se 1 (by rfl) ⟨4320944, by rfl⟩ : syracuseStep 5761259 = 8641889) B8641889
theorem B4319527 : Blo 1705053 4319527 := bstep (se 1 (by rfl) ⟨3239645, by rfl⟩ : syracuseStep 4319527 = 6479291) B6479291
theorem B2558249 : Blo 1705053 2558249 := bstep (se 2 (by rfl) ⟨959343, by rfl⟩ : syracuseStep 2558249 = 1918687) B1918687
theorem B2558255 : Blo 1705053 2558255 := bstep (se 1 (by rfl) ⟨1918691, by rfl⟩ : syracuseStep 2558255 = 3837383) B3837383
theorem B1706287 : Blo 1705053 1706287 := bstep (se 1 (by rfl) ⟨1279715, by rfl⟩ : syracuseStep 1706287 = 2559431) B2559431
theorem B1919515 : Blo 1705053 1919515 := bstep (se 1 (by rfl) ⟨1439636, by rfl⟩ : syracuseStep 1919515 = 2879273) B2879273
theorem B1706523 : Blo 1705053 1706523 := bstep (se 1 (by rfl) ⟨1279892, by rfl⟩ : syracuseStep 1706523 = 2559785) B2559785
theorem B3836447 : Blo 1705053 3836447 := bstep (se 1 (by rfl) ⟨2877335, by rfl⟩ : syracuseStep 3836447 = 5754671) B5754671
theorem B2558495 : Blo 1705053 2558495 := bstep (se 1 (by rfl) ⟨1918871, by rfl⟩ : syracuseStep 2558495 = 3837743) B3837743
theorem B1706527 : Blo 1705053 1706527 := bstep (se 1 (by rfl) ⟨1279895, by rfl⟩ : syracuseStep 1706527 = 2559791) B2559791
theorem B2878139 : Blo 1705053 2878139 := bstep (se 1 (by rfl) ⟨2158604, by rfl⟩ : syracuseStep 2878139 = 4317209) B4317209
theorem B1706843 : Blo 1705053 1706843 := bstep (se 1 (by rfl) ⟨1280132, by rfl⟩ : syracuseStep 1706843 = 2560265) B2560265
theorem B35031959 : Blo 1705053 35031959 := bstep (se 1 (by rfl) ⟨26273969, by rfl⟩ : syracuseStep 35031959 = 52547939) B52547939
theorem B2558879 : Blo 1705053 2558879 := bstep (se 1 (by rfl) ⟨1919159, by rfl⟩ : syracuseStep 2558879 = 3838319) B3838319
theorem B1706911 : Blo 1705053 1706911 := bstep (se 1 (by rfl) ⟨1280183, by rfl⟩ : syracuseStep 1706911 = 2560367) B2560367
theorem B2558927 : Blo 1705053 2558927 := bstep (se 1 (by rfl) ⟨1919195, by rfl⟩ : syracuseStep 2558927 = 3838391) B3838391
theorem B2559017 : Blo 1705053 2559017 := bstep (se 2 (by rfl) ⟨959631, by rfl⟩ : syracuseStep 2559017 = 1919263) B1919263
theorem B2559023 : Blo 1705053 2559023 := bstep (se 1 (by rfl) ⟨1919267, by rfl⟩ : syracuseStep 2559023 = 3838535) B3838535
theorem B2559047 : Blo 1705053 2559047 := bstep (se 1 (by rfl) ⟨1919285, by rfl⟩ : syracuseStep 2559047 = 3838571) B3838571
theorem B4320479 : Blo 1705053 4320479 := bstep (se 1 (by rfl) ⟨3240359, by rfl⟩ : syracuseStep 4320479 = 6480719) B6480719
theorem B2559311 : Blo 1705053 2559311 := bstep (se 1 (by rfl) ⟨1919483, by rfl⟩ : syracuseStep 2559311 = 3838967) B3838967
theorem B299052431 : Blo 1705053 299052431 := bstep (se 1 (by rfl) ⟨224289323, by rfl⟩ : syracuseStep 299052431 = 448578647) B448578647
theorem B2559401 : Blo 1705053 2559401 := bstep (se 2 (by rfl) ⟨959775, by rfl⟩ : syracuseStep 2559401 = 1919551) B1919551
theorem B10522025 : Blo 1705053 10522025 := bstep (se 2 (by rfl) ⟨3945759, by rfl⟩ : syracuseStep 10522025 = 7891519) B7891519
theorem B10931705 : Blo 1705053 10931705 := bstep (se 2 (by rfl) ⟨4099389, by rfl⟩ : syracuseStep 10931705 = 8198779) B8198779
theorem B2559551 : Blo 1705053 2559551 := bstep (se 1 (by rfl) ⟨1919663, by rfl⟩ : syracuseStep 2559551 = 3839327) B3839327
theorem B46681697 : Blo 1705053 46681697 := bstep (se 2 (by rfl) ⟨17505636, by rfl⟩ : syracuseStep 46681697 = 35011273) B35011273
theorem B359411489 : Blo 1705053 359411489 := bstep (se 2 (by rfl) ⟨134779308, by rfl⟩ : syracuseStep 359411489 = 269558617) B269558617
theorem B2305831 : Blo 1705053 2305831 := bstep (se 1 (by rfl) ⟨1729373, by rfl⟩ : syracuseStep 2305831 = 3458747) B3458747
theorem B2559815 : Blo 1705053 2559815 := bstep (se 1 (by rfl) ⟨1919861, by rfl⟩ : syracuseStep 2559815 = 3839723) B3839723
theorem B2428795 : Blo 1705053 2428795 := bstep (se 1 (by rfl) ⟨1821596, by rfl⟩ : syracuseStep 2428795 = 3643193) B3643193
theorem B12472211 : Blo 1705053 12472211 := bstep (se 1 (by rfl) ⟨9354158, by rfl⟩ : syracuseStep 12472211 = 18708317) B18708317
theorem B5754779 : Blo 1705053 5754779 := bstep (se 1 (by rfl) ⟨4316084, by rfl⟩ : syracuseStep 5754779 = 8632169) B8632169
theorem B3837851 : Blo 1705053 3837851 := bstep (se 1 (by rfl) ⟨2878388, by rfl⟩ : syracuseStep 3837851 = 5756777) B5756777
theorem B2559899 : Blo 1705053 2559899 := bstep (se 1 (by rfl) ⟨1919924, by rfl⟩ : syracuseStep 2559899 = 3839849) B3839849
theorem B2879455 : Blo 1705053 2879455 := bstep (se 1 (by rfl) ⟨2159591, by rfl⟩ : syracuseStep 2879455 = 4319183) B4319183
theorem B8638649 : Blo 1705053 8638649 := bstep (se 2 (by rfl) ⟨3239493, by rfl⟩ : syracuseStep 8638649 = 6478987) B6478987
theorem B3838139 : Blo 1705053 3838139 := bstep (se 1 (by rfl) ⟨2878604, by rfl⟩ : syracuseStep 3838139 = 5757209) B5757209
theorem B2158903 : Blo 1705053 2158903 := bstep (se 1 (by rfl) ⟨1619177, by rfl⟩ : syracuseStep 2158903 = 3238355) B3238355
theorem B5468543 : Blo 1705053 5468543 := bstep (se 1 (by rfl) ⟨4101407, by rfl⟩ : syracuseStep 5468543 = 8202815) B8202815
theorem B2560463 : Blo 1705053 2560463 := bstep (se 1 (by rfl) ⟨1920347, by rfl⟩ : syracuseStep 2560463 = 3840695) B3840695
theorem B2560505 : Blo 1705053 2560505 := bstep (se 2 (by rfl) ⟨960189, by rfl⟩ : syracuseStep 2560505 = 1920379) B1920379
theorem B11670095 : Blo 1705053 11670095 := bstep (se 1 (by rfl) ⟨8752571, by rfl⟩ : syracuseStep 11670095 = 17505143) B17505143
theorem B2880103 : Blo 1705053 2880103 := bstep (se 1 (by rfl) ⟨2160077, by rfl⟩ : syracuseStep 2880103 = 4320155) B4320155
theorem B3838625 : Blo 1705053 3838625 := bstep (se 2 (by rfl) ⟨1439484, by rfl⟩ : syracuseStep 3838625 = 2878969) B2878969
theorem B11834039 : Blo 1705053 11834039 := bstep (se 1 (by rfl) ⟨8875529, by rfl⟩ : syracuseStep 11834039 = 17751059) B17751059
theorem B2880265 : Blo 1705053 2880265 := bstep (se 2 (by rfl) ⟨1080099, by rfl⟩ : syracuseStep 2880265 = 2160199) B2160199
theorem B18437129 : Blo 1705053 18437129 := bstep (se 2 (by rfl) ⟨6913923, by rfl⟩ : syracuseStep 18437129 = 13827847) B13827847
theorem B5755913 : Blo 1705053 5755913 := bstep (se 2 (by rfl) ⟨2158467, by rfl⟩ : syracuseStep 5755913 = 4316935) B4316935
theorem B3838985 : Blo 1705053 3838985 := bstep (se 2 (by rfl) ⟨1439619, by rfl⟩ : syracuseStep 3838985 = 2879239) B2879239
theorem B5755967 : Blo 1705053 5755967 := bstep (se 1 (by rfl) ⟨4316975, by rfl⟩ : syracuseStep 5755967 = 8633951) B8633951
theorem B3839039 : Blo 1705053 3839039 := bstep (se 1 (by rfl) ⟨2879279, by rfl⟩ : syracuseStep 3839039 = 5758559) B5758559
theorem B2159723 : Blo 1705053 2159723 := bstep (se 1 (by rfl) ⟨1619792, by rfl⟩ : syracuseStep 2159723 = 3239585) B3239585
theorem B28431767 : Blo 1705053 28431767 := bstep (se 1 (by rfl) ⟨21323825, by rfl⟩ : syracuseStep 28431767 = 42647651) B42647651
theorem B7780049 : Blo 1705053 7780049 := bstep (se 2 (by rfl) ⟨2917518, by rfl⟩ : syracuseStep 7780049 = 5835037) B5835037
theorem B10925887 : Blo 1705053 10925887 := bstep (se 1 (by rfl) ⟨8194415, by rfl⟩ : syracuseStep 10925887 = 16388831) B16388831
theorem B99727199 : Blo 1705053 99727199 := bstep (se 1 (by rfl) ⟨74795399, by rfl⟩ : syracuseStep 99727199 = 149590799) B149590799
theorem B9222025 : Blo 1705053 9222025 := bstep (se 2 (by rfl) ⟨3458259, by rfl⟩ : syracuseStep 9222025 = 6916519) B6916519
theorem B3643355 : Blo 1705053 3643355 := bstep (se 1 (by rfl) ⟨2732516, by rfl⟩ : syracuseStep 3643355 = 5465033) B5465033
theorem B3839975 : Blo 1705053 3839975 := bstep (se 1 (by rfl) ⟨2879981, by rfl⟩ : syracuseStep 3839975 = 5759963) B5759963
theorem B4855801 : Blo 1705053 4855801 := bstep (se 2 (by rfl) ⟨1820925, by rfl⟩ : syracuseStep 4855801 = 3641851) B3641851
theorem B3839993 : Blo 1705053 3839993 := bstep (se 2 (by rfl) ⟨1439997, by rfl⟩ : syracuseStep 3839993 = 2879995) B2879995
theorem B3840083 : Blo 1705053 3840083 := bstep (se 1 (by rfl) ⟨2880062, by rfl⟩ : syracuseStep 3840083 = 5760125) B5760125
theorem B6150239 : Blo 1705053 6150239 := bstep (se 1 (by rfl) ⟨4612679, by rfl⟩ : syracuseStep 6150239 = 9225359) B9225359
theorem B3643535 : Blo 1705053 3643535 := bstep (se 1 (by rfl) ⟨2732651, by rfl⟩ : syracuseStep 3643535 = 5465303) B5465303
theorem B3840155 : Blo 1705053 3840155 := bstep (se 1 (by rfl) ⟨2880116, by rfl⟩ : syracuseStep 3840155 = 5760233) B5760233
theorem B4856051 : Blo 1705053 4856051 := bstep (se 1 (by rfl) ⟨3642038, by rfl⟩ : syracuseStep 4856051 = 7284077) B7284077
theorem B8640755 : Blo 1705053 8640755 := bstep (se 1 (by rfl) ⟨6480566, by rfl⟩ : syracuseStep 8640755 = 12961133) B12961133
theorem B3840263 : Blo 1705053 3840263 := bstep (se 1 (by rfl) ⟨2880197, by rfl⟩ : syracuseStep 3840263 = 5760395) B5760395
theorem B10926373 : Blo 1705053 10926373 := bstep (se 4 (by rfl) ⟨1024347, by rfl⟩ : syracuseStep 10926373 = 2048695) B2048695
theorem B21871093 : Blo 1705053 21871093 := bstep (se 5 (by rfl) ⟨1025207, by rfl⟩ : syracuseStep 21871093 = 2050415) B2050415
theorem B3840569 : Blo 1705053 3840569 := bstep (se 2 (by rfl) ⟨1440213, by rfl⟩ : syracuseStep 3840569 = 2880427) B2880427
theorem B65583755 : Blo 1705053 65583755 := bstep (se 1 (by rfl) ⟨49187816, by rfl⟩ : syracuseStep 65583755 = 98375633) B98375633
theorem B35035895 : Blo 1705053 35035895 := bstep (se 1 (by rfl) ⟨26276921, by rfl⟩ : syracuseStep 35035895 = 52553843) B52553843
theorem B4856735 : Blo 1705053 4856735 := bstep (se 1 (by rfl) ⟨3642551, by rfl⟩ : syracuseStep 4856735 = 7285103) B7285103
theorem B6478973 : Blo 1705053 6478973 := bstep (se 3 (by rfl) ⟨1214807, by rfl⟩ : syracuseStep 6478973 = 2429615) B2429615
theorem B27655435 : Blo 1705053 27655435 := bstep (se 1 (by rfl) ⟨20741576, by rfl⟩ : syracuseStep 27655435 = 41483153) B41483153
theorem B6913309 : Blo 1705053 6913309 := bstep (se 3 (by rfl) ⟨1296245, by rfl⟩ : syracuseStep 6913309 = 2592491) B2592491
theorem B4316915 : Blo 1705053 4316915 := bstep (se 1 (by rfl) ⟨3237686, by rfl⟩ : syracuseStep 4316915 = 6475373) B6475373
theorem B3645175 : Blo 1705053 3645175 := bstep (se 1 (by rfl) ⟨2733881, by rfl⟩ : syracuseStep 3645175 = 5467763) B5467763
theorem B5758775 : Blo 1705053 5758775 := bstep (se 1 (by rfl) ⟨4319081, by rfl⟩ : syracuseStep 5758775 = 8638163) B8638163
theorem B5759099 : Blo 1705053 5759099 := bstep (se 1 (by rfl) ⟨4319324, by rfl⟩ : syracuseStep 5759099 = 8638649) B8638649
theorem B16400555 : Blo 1705053 16400555 := bstep (se 1 (by rfl) ⟨12300416, by rfl⟩ : syracuseStep 16400555 = 24600833) B24600833
theorem B3645695 : Blo 1705053 3645695 := bstep (se 1 (by rfl) ⟨2734271, by rfl⟩ : syracuseStep 3645695 = 5468543) B5468543
theorem B5759261 : Blo 1705053 5759261 := bstep (se 3 (by rfl) ⟨1079861, by rfl⟩ : syracuseStep 5759261 = 2159723) B2159723
theorem B5759369 : Blo 1705053 5759369 := bstep (se 2 (by rfl) ⟨2159763, by rfl⟩ : syracuseStep 5759369 = 4319527) B4319527
theorem B7889359 : Blo 1705053 7889359 := bstep (se 1 (by rfl) ⟨5917019, by rfl⟩ : syracuseStep 7889359 = 11834039) B11834039
theorem B7291579 : Blo 1705053 7291579 := bstep (se 1 (by rfl) ⟨5468684, by rfl⟩ : syracuseStep 7291579 = 10937369) B10937369
theorem B8635247 : Blo 1705053 8635247 := bstep (se 1 (by rfl) ⟨6476435, by rfl⟩ : syracuseStep 8635247 = 12952871) B12952871
theorem B4375547 : Blo 1705053 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B75818045 : Blo 1705053 75818045 := bstep (se 3 (by rfl) ⟨14215883, by rfl⟩ : syracuseStep 75818045 = 28431767) B28431767
theorem B1705071 : Blo 1705053 1705071 := bstep (se 1 (by rfl) ⟨1278803, by rfl⟩ : syracuseStep 1705071 = 2557607) B2557607
theorem B5186699 : Blo 1705053 5186699 := bstep (se 1 (by rfl) ⟨3890024, by rfl⟩ : syracuseStep 5186699 = 7780049) B7780049
theorem B1705127 : Blo 1705053 1705127 := bstep (se 1 (by rfl) ⟨1278845, by rfl⟩ : syracuseStep 1705127 = 2557691) B2557691
theorem B1705151 : Blo 1705053 1705151 := bstep (se 1 (by rfl) ⟨1278863, by rfl⟩ : syracuseStep 1705151 = 2557727) B2557727
theorem B1705183 : Blo 1705053 1705183 := bstep (se 1 (by rfl) ⟨1278887, by rfl⟩ : syracuseStep 1705183 = 2557775) B2557775
theorem B1918255 : Blo 1705053 1918255 := bstep (se 1 (by rfl) ⟨1438691, by rfl⟩ : syracuseStep 1918255 = 2877383) B2877383
theorem B1705263 : Blo 1705053 1705263 := bstep (se 1 (by rfl) ⟨1278947, by rfl⟩ : syracuseStep 1705263 = 2557895) B2557895
theorem B49202579 : Blo 1705053 49202579 := bstep (se 1 (by rfl) ⟨36901934, by rfl⟩ : syracuseStep 49202579 = 73803869) B73803869
theorem B7014683 : Blo 1705053 7014683 := bstep (se 1 (by rfl) ⟨5261012, by rfl⟩ : syracuseStep 7014683 = 10522025) B10522025
theorem B5760503 : Blo 1705053 5760503 := bstep (se 1 (by rfl) ⟨4320377, by rfl⟩ : syracuseStep 5760503 = 8640755) B8640755
theorem B1705499 : Blo 1705053 1705499 := bstep (se 1 (by rfl) ⟨1279124, by rfl⟩ : syracuseStep 1705499 = 2558249) B2558249
theorem B1705503 : Blo 1705053 1705503 := bstep (se 1 (by rfl) ⟨1279127, by rfl⟩ : syracuseStep 1705503 = 2558255) B2558255
theorem B4097641 : Blo 1705053 4097641 := bstep (se 2 (by rfl) ⟨1536615, by rfl⟩ : syracuseStep 4097641 = 3073231) B3073231
theorem B36873913 : Blo 1705053 36873913 := bstep (se 2 (by rfl) ⟨13827717, by rfl⟩ : syracuseStep 36873913 = 27655435) B27655435
theorem B2557631 : Blo 1705053 2557631 := bstep (se 1 (by rfl) ⟨1918223, by rfl⟩ : syracuseStep 2557631 = 3836447) B3836447
theorem B1705663 : Blo 1705053 1705663 := bstep (se 1 (by rfl) ⟨1279247, by rfl⟩ : syracuseStep 1705663 = 2558495) B2558495
theorem B9217745 : Blo 1705053 9217745 := bstep (se 2 (by rfl) ⟨3456654, by rfl⟩ : syracuseStep 9217745 = 6913309) B6913309
theorem B43722503 : Blo 1705053 43722503 := bstep (se 1 (by rfl) ⟨32791877, by rfl⟩ : syracuseStep 43722503 = 65583755) B65583755
theorem B1918759 : Blo 1705053 1918759 := bstep (se 1 (by rfl) ⟨1439069, by rfl⟩ : syracuseStep 1918759 = 2878139) B2878139
theorem B23357263 : Blo 1705053 23357263 := bstep (se 1 (by rfl) ⟨17517947, by rfl⟩ : syracuseStep 23357263 = 35035895) B35035895
theorem B2557817 : Blo 1705053 2557817 := bstep (se 2 (by rfl) ⟨959181, by rfl⟩ : syracuseStep 2557817 = 1918363) B1918363
theorem B3237823 : Blo 1705053 3237823 := bstep (se 1 (by rfl) ⟨2428367, by rfl⟩ : syracuseStep 3237823 = 4856735) B4856735
theorem B1705919 : Blo 1705053 1705919 := bstep (se 1 (by rfl) ⟨1279439, by rfl⟩ : syracuseStep 1705919 = 2558879) B2558879
theorem B1705951 : Blo 1705053 1705951 := bstep (se 1 (by rfl) ⟨1279463, by rfl⟩ : syracuseStep 1705951 = 2558927) B2558927
theorem B1706011 : Blo 1705053 1706011 := bstep (se 1 (by rfl) ⟨1279508, by rfl⟩ : syracuseStep 1706011 = 2559017) B2559017
theorem B1706015 : Blo 1705053 1706015 := bstep (se 1 (by rfl) ⟨1279511, by rfl⟩ : syracuseStep 1706015 = 2559023) B2559023
theorem B1706031 : Blo 1705053 1706031 := bstep (se 1 (by rfl) ⟨1279523, by rfl⟩ : syracuseStep 1706031 = 2559047) B2559047
theorem B4319315 : Blo 1705053 4319315 := bstep (se 1 (by rfl) ⟨3239486, by rfl⟩ : syracuseStep 4319315 = 6478973) B6478973
theorem B1706207 : Blo 1705053 1706207 := bstep (se 1 (by rfl) ⟨1279655, by rfl⟩ : syracuseStep 1706207 = 2559311) B2559311
theorem B1706267 : Blo 1705053 1706267 := bstep (se 1 (by rfl) ⟨1279700, by rfl⟩ : syracuseStep 1706267 = 2559401) B2559401
theorem B4860233 : Blo 1705053 4860233 := bstep (se 2 (by rfl) ⟨1822587, by rfl⟩ : syracuseStep 4860233 = 3645175) B3645175
theorem B1706367 : Blo 1705053 1706367 := bstep (se 1 (by rfl) ⟨1279775, by rfl⟩ : syracuseStep 1706367 = 2559551) B2559551
theorem B3074441 : Blo 1705053 3074441 := bstep (se 2 (by rfl) ⟨1152915, by rfl⟩ : syracuseStep 3074441 = 2305831) B2305831
theorem B14567849 : Blo 1705053 14567849 := bstep (se 2 (by rfl) ⟨5462943, by rfl⟩ : syracuseStep 14567849 = 10925887) B10925887
theorem B2877943 : Blo 1705053 2877943 := bstep (se 1 (by rfl) ⟨2158457, by rfl⟩ : syracuseStep 2877943 = 4316915) B4316915
theorem B3238393 : Blo 1705053 3238393 := bstep (se 2 (by rfl) ⟨1214397, by rfl⟩ : syracuseStep 3238393 = 2428795) B2428795
theorem B1706543 : Blo 1705053 1706543 := bstep (se 1 (by rfl) ⟨1279907, by rfl⟩ : syracuseStep 1706543 = 2559815) B2559815
theorem B3836519 : Blo 1705053 3836519 := bstep (se 1 (by rfl) ⟨2877389, by rfl⟩ : syracuseStep 3836519 = 5754779) B5754779
theorem B2558567 : Blo 1705053 2558567 := bstep (se 1 (by rfl) ⟨1918925, by rfl⟩ : syracuseStep 2558567 = 3837851) B3837851
theorem B1706599 : Blo 1705053 1706599 := bstep (se 1 (by rfl) ⟨1279949, by rfl⟩ : syracuseStep 1706599 = 2559899) B2559899
theorem B6474401 : Blo 1705053 6474401 := bstep (se 2 (by rfl) ⟨2427900, by rfl⟩ : syracuseStep 6474401 = 4855801) B4855801
theorem B2558759 : Blo 1705053 2558759 := bstep (se 1 (by rfl) ⟨1919069, by rfl⟩ : syracuseStep 2558759 = 3838139) B3838139
theorem B3238879 : Blo 1705053 3238879 := bstep (se 1 (by rfl) ⟨2429159, by rfl⟩ : syracuseStep 3238879 = 4858319) B4858319
theorem B1706975 : Blo 1705053 1706975 := bstep (se 1 (by rfl) ⟨1280231, by rfl⟩ : syracuseStep 1706975 = 2560463) B2560463
theorem B3836897 : Blo 1705053 3836897 := bstep (se 2 (by rfl) ⟨1438836, by rfl⟩ : syracuseStep 3836897 = 2877673) B2877673
theorem B1707003 : Blo 1705053 1707003 := bstep (se 1 (by rfl) ⟨1280252, by rfl⟩ : syracuseStep 1707003 = 2560505) B2560505
theorem B14568497 : Blo 1705053 14568497 := bstep (se 2 (by rfl) ⟨5463186, by rfl⟩ : syracuseStep 14568497 = 10926373) B10926373
theorem B129723439 : Blo 1705053 129723439 := bstep (se 1 (by rfl) ⟨97292579, by rfl⟩ : syracuseStep 129723439 = 194585159) B194585159
theorem B2878537 : Blo 1705053 2878537 := bstep (se 2 (by rfl) ⟨1079451, by rfl⟩ : syracuseStep 2878537 = 2158903) B2158903
theorem B2559083 : Blo 1705053 2559083 := bstep (se 1 (by rfl) ⟨1919312, by rfl⟩ : syracuseStep 2559083 = 3838625) B3838625
theorem B7285889 : Blo 1705053 7285889 := bstep (se 2 (by rfl) ⟨2732208, by rfl⟩ : syracuseStep 7285889 = 5464417) B5464417
theorem B12291419 : Blo 1705053 12291419 := bstep (se 1 (by rfl) ⟨9218564, by rfl⟩ : syracuseStep 12291419 = 18437129) B18437129
theorem B3837275 : Blo 1705053 3837275 := bstep (se 1 (by rfl) ⟨2877956, by rfl⟩ : syracuseStep 3837275 = 5755913) B5755913
theorem B2559323 : Blo 1705053 2559323 := bstep (se 1 (by rfl) ⟨1919492, by rfl⟩ : syracuseStep 2559323 = 3838985) B3838985
theorem B2559353 : Blo 1705053 2559353 := bstep (se 2 (by rfl) ⟨959757, by rfl⟩ : syracuseStep 2559353 = 1919515) B1919515
theorem B3837311 : Blo 1705053 3837311 := bstep (se 1 (by rfl) ⟨2877983, by rfl⟩ : syracuseStep 3837311 = 5755967) B5755967
theorem B2559359 : Blo 1705053 2559359 := bstep (se 1 (by rfl) ⟨1919519, by rfl⟩ : syracuseStep 2559359 = 3839039) B3839039
theorem B3239851 : Blo 1705053 3239851 := bstep (se 1 (by rfl) ⟨2429888, by rfl⟩ : syracuseStep 3239851 = 4859777) B4859777
theorem B2428903 : Blo 1705053 2428903 := bstep (se 1 (by rfl) ⟨1821677, by rfl⟩ : syracuseStep 2428903 = 3643355) B3643355
theorem B2559983 : Blo 1705053 2559983 := bstep (se 1 (by rfl) ⟨1919987, by rfl⟩ : syracuseStep 2559983 = 3839975) B3839975
theorem B2559995 : Blo 1705053 2559995 := bstep (se 1 (by rfl) ⟨1919996, by rfl⟩ : syracuseStep 2559995 = 3839993) B3839993
theorem B2560055 : Blo 1705053 2560055 := bstep (se 1 (by rfl) ⟨1920041, by rfl⟩ : syracuseStep 2560055 = 3840083) B3840083
theorem B4100159 : Blo 1705053 4100159 := bstep (se 1 (by rfl) ⟨3075119, by rfl⟩ : syracuseStep 4100159 = 6150239) B6150239
theorem B2429023 : Blo 1705053 2429023 := bstep (se 1 (by rfl) ⟨1821767, by rfl⟩ : syracuseStep 2429023 = 3643535) B3643535
theorem B2560103 : Blo 1705053 2560103 := bstep (se 1 (by rfl) ⟨1920077, by rfl⟩ : syracuseStep 2560103 = 3840155) B3840155
theorem B12955787 : Blo 1705053 12955787 := bstep (se 1 (by rfl) ⟨9716840, by rfl⟩ : syracuseStep 12955787 = 19433681) B19433681
theorem B2560175 : Blo 1705053 2560175 := bstep (se 1 (by rfl) ⟨1920131, by rfl⟩ : syracuseStep 2560175 = 3840263) B3840263
theorem B2560379 : Blo 1705053 2560379 := bstep (se 1 (by rfl) ⟨1920284, by rfl⟩ : syracuseStep 2560379 = 3840569) B3840569
theorem B2880319 : Blo 1705053 2880319 := bstep (se 1 (by rfl) ⟨2160239, by rfl⟩ : syracuseStep 2880319 = 4320479) B4320479
theorem B7287803 : Blo 1705053 7287803 := bstep (se 1 (by rfl) ⟨5465852, by rfl⟩ : syracuseStep 7287803 = 10931705) B10931705
theorem B9712649 : Blo 1705053 9712649 := bstep (se 2 (by rfl) ⟨3642243, by rfl⟩ : syracuseStep 9712649 = 7284487) B7284487
theorem B3839183 : Blo 1705053 3839183 := bstep (se 1 (by rfl) ⟨2879387, by rfl⟩ : syracuseStep 3839183 = 5758775) B5758775
theorem B3839273 : Blo 1705053 3839273 := bstep (se 2 (by rfl) ⟨1439727, by rfl⟩ : syracuseStep 3839273 = 2879455) B2879455
theorem B5756399 : Blo 1705053 5756399 := bstep (se 1 (by rfl) ⟨4317299, by rfl⟩ : syracuseStep 5756399 = 8634599) B8634599
theorem B3839471 : Blo 1705053 3839471 := bstep (se 1 (by rfl) ⟨2879603, by rfl⟩ : syracuseStep 3839471 = 5759207) B5759207
theorem B3282599 : Blo 1705053 3282599 := bstep (se 1 (by rfl) ⟨2461949, by rfl⟩ : syracuseStep 3282599 = 4923899) B4923899
theorem B7780063 : Blo 1705053 7780063 := bstep (se 1 (by rfl) ⟨5835047, by rfl⟩ : syracuseStep 7780063 = 11670095) B11670095
theorem B9721579 : Blo 1705053 9721579 := bstep (se 1 (by rfl) ⟨7291184, by rfl⟩ : syracuseStep 9721579 = 14582369) B14582369
theorem B3839867 : Blo 1705053 3839867 := bstep (se 1 (by rfl) ⟨2879900, by rfl⟩ : syracuseStep 3839867 = 5759801) B5759801
theorem B3839903 : Blo 1705053 3839903 := bstep (se 1 (by rfl) ⟨2879927, by rfl⟩ : syracuseStep 3839903 = 5759855) B5759855
theorem B12949469 : Blo 1705053 12949469 := bstep (se 3 (by rfl) ⟨2428025, by rfl⟩ : syracuseStep 12949469 = 4856051) B4856051
theorem B29161457 : Blo 1705053 29161457 := bstep (se 2 (by rfl) ⟨10935546, by rfl⟩ : syracuseStep 29161457 = 21871093) B21871093
theorem B13129811 : Blo 1705053 13129811 := bstep (se 1 (by rfl) ⟨9847358, by rfl⟩ : syracuseStep 13129811 = 19694717) B19694717
theorem B3840137 : Blo 1705053 3840137 := bstep (se 2 (by rfl) ⟨1440051, by rfl⟩ : syracuseStep 3840137 = 2880103) B2880103
theorem B3643679 : Blo 1705053 3643679 := bstep (se 1 (by rfl) ⟨2732759, by rfl⟩ : syracuseStep 3643679 = 5465519) B5465519
theorem B3840353 : Blo 1705053 3840353 := bstep (se 2 (by rfl) ⟨1440132, by rfl⟩ : syracuseStep 3840353 = 2880265) B2880265
theorem B118200707 : Blo 1705053 118200707 := bstep (se 1 (by rfl) ⟨88650530, by rfl⟩ : syracuseStep 118200707 = 177301061) B177301061
theorem B3889595 : Blo 1705053 3889595 := bstep (se 1 (by rfl) ⟨2917196, by rfl⟩ : syracuseStep 3889595 = 5834393) B5834393
theorem B5757371 : Blo 1705053 5757371 := bstep (se 1 (by rfl) ⟨4318028, by rfl⟩ : syracuseStep 5757371 = 8636057) B8636057
theorem B3840443 : Blo 1705053 3840443 := bstep (se 1 (by rfl) ⟨2880332, by rfl⟩ : syracuseStep 3840443 = 5760665) B5760665
theorem B66484799 : Blo 1705053 66484799 := bstep (se 1 (by rfl) ⟨49863599, by rfl⟩ : syracuseStep 66484799 = 99727199) B99727199
theorem B3840839 : Blo 1705053 3840839 := bstep (se 1 (by rfl) ⟨2880629, by rfl⟩ : syracuseStep 3840839 = 5761259) B5761259
theorem B23354639 : Blo 1705053 23354639 := bstep (se 1 (by rfl) ⟨17515979, by rfl⟩ : syracuseStep 23354639 = 35031959) B35031959
theorem B14769485 : Blo 1705053 14769485 := bstep (se 3 (by rfl) ⟨2769278, by rfl⟩ : syracuseStep 14769485 = 5538557) B5538557
theorem B199368287 : Blo 1705053 199368287 := bstep (se 1 (by rfl) ⟨149526215, by rfl⟩ : syracuseStep 199368287 = 299052431) B299052431
theorem B31121131 : Blo 1705053 31121131 := bstep (se 1 (by rfl) ⟨23340848, by rfl⟩ : syracuseStep 31121131 = 46681697) B46681697
theorem B12296033 : Blo 1705053 12296033 := bstep (se 2 (by rfl) ⟨4611012, by rfl⟩ : syracuseStep 12296033 = 9222025) B9222025
theorem B239607659 : Blo 1705053 239607659 := bstep (se 1 (by rfl) ⟨179705744, by rfl⟩ : syracuseStep 239607659 = 359411489) B359411489
theorem B8314807 : Blo 1705053 8314807 := bstep (se 1 (by rfl) ⟨6236105, by rfl⟩ : syracuseStep 8314807 = 12472211) B12472211
theorem B10519145 : Blo 1705053 10519145 := bstep (se 2 (by rfl) ⟨3944679, by rfl⟩ : syracuseStep 10519145 = 7889359) B7889359
theorem B4317857 : Blo 1705053 4317857 := bstep (se 2 (by rfl) ⟨1619196, by rfl⟩ : syracuseStep 4317857 = 3238393) B3238393
theorem B2917031 : Blo 1705053 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B4858535 : Blo 1705053 4858535 := bstep (se 1 (by rfl) ⟨3643901, by rfl⟩ : syracuseStep 4858535 = 7287803) B7287803
theorem B3457799 : Blo 1705053 3457799 := bstep (se 1 (by rfl) ⟨2593349, by rfl⟩ : syracuseStep 3457799 = 5186699) B5186699
theorem B32801719 : Blo 1705053 32801719 := bstep (se 1 (by rfl) ⟨24601289, by rfl⟩ : syracuseStep 32801719 = 49202579) B49202579
theorem B1705087 : Blo 1705053 1705087 := bstep (se 1 (by rfl) ⟨1278815, by rfl⟩ : syracuseStep 1705087 = 2557631) B2557631
theorem B6145163 : Blo 1705053 6145163 := bstep (se 1 (by rfl) ⟨4608872, by rfl⟩ : syracuseStep 6145163 = 9217745) B9217745
theorem B29148335 : Blo 1705053 29148335 := bstep (se 1 (by rfl) ⟨21861251, by rfl⟩ : syracuseStep 29148335 = 43722503) B43722503
theorem B1705211 : Blo 1705053 1705211 := bstep (se 1 (by rfl) ⟨1278908, by rfl⟩ : syracuseStep 1705211 = 2557817) B2557817
theorem B4318505 : Blo 1705053 4318505 := bstep (se 2 (by rfl) ⟨1619439, by rfl⟩ : syracuseStep 4318505 = 3238879) B3238879
theorem B19440971 : Blo 1705053 19440971 := bstep (se 1 (by rfl) ⟨14580728, by rfl⟩ : syracuseStep 19440971 = 29161457) B29161457
theorem B78800471 : Blo 1705053 78800471 := bstep (se 1 (by rfl) ⟨59100353, by rfl⟩ : syracuseStep 78800471 = 118200707) B118200707
theorem B2557673 : Blo 1705053 2557673 := bstep (se 2 (by rfl) ⟨959127, by rfl⟩ : syracuseStep 2557673 = 1918255) B1918255
theorem B2557679 : Blo 1705053 2557679 := bstep (se 1 (by rfl) ⟨1918259, by rfl⟩ : syracuseStep 2557679 = 3836519) B3836519
theorem B1705711 : Blo 1705053 1705711 := bstep (se 1 (by rfl) ⟨1279283, by rfl⟩ : syracuseStep 1705711 = 2558567) B2558567
theorem B1705839 : Blo 1705053 1705839 := bstep (se 1 (by rfl) ⟨1279379, by rfl⟩ : syracuseStep 1705839 = 2558759) B2558759
theorem B2557931 : Blo 1705053 2557931 := bstep (se 1 (by rfl) ⟨1918448, by rfl⟩ : syracuseStep 2557931 = 3836897) B3836897
theorem B1706055 : Blo 1705053 1706055 := bstep (se 1 (by rfl) ⟨1279541, by rfl⟩ : syracuseStep 1706055 = 2559083) B2559083
theorem B8194279 : Blo 1705053 8194279 := bstep (se 1 (by rfl) ⟨6145709, by rfl⟩ : syracuseStep 8194279 = 12291419) B12291419
theorem B2558183 : Blo 1705053 2558183 := bstep (se 1 (by rfl) ⟨1918637, by rfl⟩ : syracuseStep 2558183 = 3837275) B3837275
theorem B1706215 : Blo 1705053 1706215 := bstep (se 1 (by rfl) ⟨1279661, by rfl⟩ : syracuseStep 1706215 = 2559323) B2559323
theorem B1706235 : Blo 1705053 1706235 := bstep (se 1 (by rfl) ⟨1279676, by rfl⟩ : syracuseStep 1706235 = 2559353) B2559353
theorem B2558207 : Blo 1705053 2558207 := bstep (se 1 (by rfl) ⟨1918655, by rfl⟩ : syracuseStep 2558207 = 3837311) B3837311
theorem B1706239 : Blo 1705053 1706239 := bstep (se 1 (by rfl) ⟨1279679, by rfl⟩ : syracuseStep 1706239 = 2559359) B2559359
theorem B10373417 : Blo 1705053 10373417 := bstep (se 2 (by rfl) ⟨3890031, by rfl⟩ : syracuseStep 10373417 = 7780063) B7780063
theorem B41494841 : Blo 1705053 41494841 := bstep (se 2 (by rfl) ⟨15560565, by rfl⟩ : syracuseStep 41494841 = 31121131) B31121131
theorem B12962105 : Blo 1705053 12962105 := bstep (se 2 (by rfl) ⟨4860789, by rfl⟩ : syracuseStep 12962105 = 9721579) B9721579
theorem B2558345 : Blo 1705053 2558345 := bstep (se 2 (by rfl) ⟨959379, by rfl⟩ : syracuseStep 2558345 = 1918759) B1918759
theorem B4319801 : Blo 1705053 4319801 := bstep (se 2 (by rfl) ⟨1619925, by rfl⟩ : syracuseStep 4319801 = 3239851) B3239851
theorem B159738439 : Blo 1705053 159738439 := bstep (se 1 (by rfl) ⟨119803829, by rfl⟩ : syracuseStep 159738439 = 239607659) B239607659
theorem B11086409 : Blo 1705053 11086409 := bstep (se 2 (by rfl) ⟨4157403, by rfl⟩ : syracuseStep 11086409 = 8314807) B8314807
theorem B3238537 : Blo 1705053 3238537 := bstep (se 2 (by rfl) ⟨1214451, by rfl⟩ : syracuseStep 3238537 = 2428903) B2428903
theorem B1706655 : Blo 1705053 1706655 := bstep (se 1 (by rfl) ⟨1279991, by rfl⟩ : syracuseStep 1706655 = 2559983) B2559983
theorem B1706663 : Blo 1705053 1706663 := bstep (se 1 (by rfl) ⟨1279997, by rfl⟩ : syracuseStep 1706663 = 2559995) B2559995
theorem B1706703 : Blo 1705053 1706703 := bstep (se 1 (by rfl) ⟨1280027, by rfl⟩ : syracuseStep 1706703 = 2560055) B2560055
theorem B1706735 : Blo 1705053 1706735 := bstep (se 1 (by rfl) ⟨1280051, by rfl⟩ : syracuseStep 1706735 = 2560103) B2560103
theorem B8637191 : Blo 1705053 8637191 := bstep (se 1 (by rfl) ⟨6477893, by rfl⟩ : syracuseStep 8637191 = 12955787) B12955787
theorem B1706783 : Blo 1705053 1706783 := bstep (se 1 (by rfl) ⟨1280087, by rfl⟩ : syracuseStep 1706783 = 2560175) B2560175
theorem B3238697 : Blo 1705053 3238697 := bstep (se 2 (by rfl) ⟨1214511, by rfl⟩ : syracuseStep 3238697 = 2429023) B2429023
theorem B202181453 : Blo 1705053 202181453 := bstep (se 3 (by rfl) ⟨37909022, by rfl⟩ : syracuseStep 202181453 = 75818045) B75818045
theorem B1706919 : Blo 1705053 1706919 := bstep (se 1 (by rfl) ⟨1280189, by rfl⟩ : syracuseStep 1706919 = 2560379) B2560379
theorem B3837257 : Blo 1705053 3837257 := bstep (se 2 (by rfl) ⟨1438971, by rfl⟩ : syracuseStep 3837257 = 2877943) B2877943
theorem B6475099 : Blo 1705053 6475099 := bstep (se 1 (by rfl) ⟨4856324, by rfl⟩ : syracuseStep 6475099 = 9712649) B9712649
theorem B2559455 : Blo 1705053 2559455 := bstep (se 1 (by rfl) ⟨1919591, by rfl⟩ : syracuseStep 2559455 = 3839183) B3839183
theorem B2559515 : Blo 1705053 2559515 := bstep (se 1 (by rfl) ⟨1919636, by rfl⟩ : syracuseStep 2559515 = 3839273) B3839273
theorem B3837599 : Blo 1705053 3837599 := bstep (se 1 (by rfl) ⟨2878199, by rfl⟩ : syracuseStep 3837599 = 5756399) B5756399
theorem B2559647 : Blo 1705053 2559647 := bstep (se 1 (by rfl) ⟨1919735, by rfl⟩ : syracuseStep 2559647 = 3839471) B3839471
theorem B2559911 : Blo 1705053 2559911 := bstep (se 1 (by rfl) ⟨1919933, by rfl⟩ : syracuseStep 2559911 = 3839867) B3839867
theorem B2559935 : Blo 1705053 2559935 := bstep (se 1 (by rfl) ⟨1919951, by rfl⟩ : syracuseStep 2559935 = 3839903) B3839903
theorem B8753207 : Blo 1705053 8753207 := bstep (se 1 (by rfl) ⟨6564905, by rfl⟩ : syracuseStep 8753207 = 13129811) B13129811
theorem B2879543 : Blo 1705053 2879543 := bstep (se 1 (by rfl) ⟨2159657, by rfl⟩ : syracuseStep 2879543 = 4319315) B4319315
theorem B2560091 : Blo 1705053 2560091 := bstep (se 1 (by rfl) ⟨1920068, by rfl⟩ : syracuseStep 2560091 = 3840137) B3840137
theorem B3838049 : Blo 1705053 3838049 := bstep (se 2 (by rfl) ⟨1439268, by rfl⟩ : syracuseStep 3838049 = 2878537) B2878537
theorem B2429119 : Blo 1705053 2429119 := bstep (se 1 (by rfl) ⟨1821839, by rfl⟩ : syracuseStep 2429119 = 3643679) B3643679
theorem B3240155 : Blo 1705053 3240155 := bstep (se 1 (by rfl) ⟨2430116, by rfl⟩ : syracuseStep 3240155 = 4860233) B4860233
theorem B2560235 : Blo 1705053 2560235 := bstep (se 1 (by rfl) ⟨1920176, by rfl⟩ : syracuseStep 2560235 = 3840353) B3840353
theorem B9711899 : Blo 1705053 9711899 := bstep (se 1 (by rfl) ⟨7283924, by rfl⟩ : syracuseStep 9711899 = 14567849) B14567849
theorem B2593063 : Blo 1705053 2593063 := bstep (se 1 (by rfl) ⟨1944797, by rfl⟩ : syracuseStep 2593063 = 3889595) B3889595
theorem B3838247 : Blo 1705053 3838247 := bstep (se 1 (by rfl) ⟨2878685, by rfl⟩ : syracuseStep 3838247 = 5757371) B5757371
theorem B2560295 : Blo 1705053 2560295 := bstep (se 1 (by rfl) ⟨1920221, by rfl⟩ : syracuseStep 2560295 = 3840443) B3840443
theorem B44323199 : Blo 1705053 44323199 := bstep (se 1 (by rfl) ⟨33242399, by rfl⟩ : syracuseStep 44323199 = 66484799) B66484799
theorem B8753597 : Blo 1705053 8753597 := bstep (se 3 (by rfl) ⟨1641299, by rfl⟩ : syracuseStep 8753597 = 3282599) B3282599
theorem B2560559 : Blo 1705053 2560559 := bstep (se 1 (by rfl) ⟨1920419, by rfl⟩ : syracuseStep 2560559 = 3840839) B3840839
theorem B9712331 : Blo 1705053 9712331 := bstep (se 1 (by rfl) ⟨7284248, by rfl⟩ : syracuseStep 9712331 = 14568497) B14568497
theorem B15569759 : Blo 1705053 15569759 := bstep (se 1 (by rfl) ⟨11677319, by rfl⟩ : syracuseStep 15569759 = 23354639) B23354639
theorem B49165217 : Blo 1705053 49165217 := bstep (se 2 (by rfl) ⟨18436956, by rfl⟩ : syracuseStep 49165217 = 36873913) B36873913
theorem B132912191 : Blo 1705053 132912191 := bstep (se 1 (by rfl) ⟨99684143, by rfl⟩ : syracuseStep 132912191 = 199368287) B199368287
theorem B31143017 : Blo 1705053 31143017 := bstep (se 2 (by rfl) ⟨11678631, by rfl⟩ : syracuseStep 31143017 = 23357263) B23357263
theorem B8197355 : Blo 1705053 8197355 := bstep (se 1 (by rfl) ⟨6148016, by rfl⟩ : syracuseStep 8197355 = 12296033) B12296033
theorem B2733439 : Blo 1705053 2733439 := bstep (se 1 (by rfl) ⟨2050079, by rfl⟩ : syracuseStep 2733439 = 4100159) B4100159
theorem B3839399 : Blo 1705053 3839399 := bstep (se 1 (by rfl) ⟨2879549, by rfl⟩ : syracuseStep 3839399 = 5759099) B5759099
theorem B10933703 : Blo 1705053 10933703 := bstep (se 1 (by rfl) ⟨8200277, by rfl⟩ : syracuseStep 10933703 = 16400555) B16400555
theorem B3839507 : Blo 1705053 3839507 := bstep (se 1 (by rfl) ⟨2879630, by rfl⟩ : syracuseStep 3839507 = 5759261) B5759261
theorem B3839579 : Blo 1705053 3839579 := bstep (se 1 (by rfl) ⟨2879684, by rfl⟩ : syracuseStep 3839579 = 5759369) B5759369
theorem B5756831 : Blo 1705053 5756831 := bstep (se 1 (by rfl) ⟨4317623, by rfl⟩ : syracuseStep 5756831 = 8635247) B8635247
theorem B9721853 : Blo 1705053 9721853 := bstep (se 3 (by rfl) ⟨1822847, by rfl⟩ : syracuseStep 9721853 = 3645695) B3645695
theorem B9722105 : Blo 1705053 9722105 := bstep (se 2 (by rfl) ⟨3645789, by rfl⟩ : syracuseStep 9722105 = 7291579) B7291579
theorem B3840335 : Blo 1705053 3840335 := bstep (se 1 (by rfl) ⟨2880251, by rfl⟩ : syracuseStep 3840335 = 5760503) B5760503
theorem B8198509 : Blo 1705053 8198509 := bstep (se 3 (by rfl) ⟨1537220, by rfl⟩ : syracuseStep 8198509 = 3074441) B3074441
theorem B3840425 : Blo 1705053 3840425 := bstep (se 2 (by rfl) ⟨1440159, by rfl⟩ : syracuseStep 3840425 = 2880319) B2880319
theorem B8632979 : Blo 1705053 8632979 := bstep (se 1 (by rfl) ⟨6474734, by rfl⟩ : syracuseStep 8632979 = 12949469) B12949469
theorem B172964585 : Blo 1705053 172964585 := bstep (se 2 (by rfl) ⟨64861719, by rfl⟩ : syracuseStep 172964585 = 129723439) B129723439
theorem B4676455 : Blo 1705053 4676455 := bstep (se 1 (by rfl) ⟨3507341, by rfl⟩ : syracuseStep 4676455 = 7014683) B7014683
theorem B4316267 : Blo 1705053 4316267 := bstep (se 1 (by rfl) ⟨3237200, by rfl⟩ : syracuseStep 4316267 = 6474401) B6474401
theorem B4857259 : Blo 1705053 4857259 := bstep (se 1 (by rfl) ⟨3642944, by rfl⟩ : syracuseStep 4857259 = 7285889) B7285889
theorem B5463521 : Blo 1705053 5463521 := bstep (se 2 (by rfl) ⟨2048820, by rfl⟩ : syracuseStep 5463521 = 4097641) B4097641
theorem B9846323 : Blo 1705053 9846323 := bstep (se 1 (by rfl) ⟨7384742, by rfl⟩ : syracuseStep 9846323 = 14769485) B14769485
theorem B4317097 : Blo 1705053 4317097 := bstep (se 2 (by rfl) ⟨1618911, by rfl⟩ : syracuseStep 4317097 = 3237823) B3237823
theorem B29548799 : Blo 1705053 29548799 := bstep (se 1 (by rfl) ⟨22161599, by rfl⟩ : syracuseStep 29548799 = 44323199) B44323199
theorem B3457417 : Blo 1705053 3457417 := bstep (se 2 (by rfl) ⟨1296531, by rfl⟩ : syracuseStep 3457417 = 2593063) B2593063
theorem B7012763 : Blo 1705053 7012763 := bstep (se 1 (by rfl) ⟨5259572, by rfl⟩ : syracuseStep 7012763 = 10519145) B10519145
theorem B10379839 : Blo 1705053 10379839 := bstep (se 1 (by rfl) ⟨7784879, by rfl⟩ : syracuseStep 10379839 = 15569759) B15569759
theorem B32776811 : Blo 1705053 32776811 := bstep (se 1 (by rfl) ⟨24582608, by rfl⟩ : syracuseStep 32776811 = 49165217) B49165217
theorem B4096775 : Blo 1705053 4096775 := bstep (se 1 (by rfl) ⟨3072581, by rfl⟩ : syracuseStep 4096775 = 6145163) B6145163
theorem B212984585 : Blo 1705053 212984585 := bstep (se 2 (by rfl) ⟨79869219, by rfl⟩ : syracuseStep 212984585 = 159738439) B159738439
theorem B19432223 : Blo 1705053 19432223 := bstep (se 1 (by rfl) ⟨14574167, by rfl⟩ : syracuseStep 19432223 = 29148335) B29148335
theorem B5464903 : Blo 1705053 5464903 := bstep (se 1 (by rfl) ⟨4098677, by rfl⟩ : syracuseStep 5464903 = 8197355) B8197355
theorem B4318049 : Blo 1705053 4318049 := bstep (se 2 (by rfl) ⟨1619268, by rfl⟩ : syracuseStep 4318049 = 3238537) B3238537
theorem B12960647 : Blo 1705053 12960647 := bstep (se 1 (by rfl) ⟨9720485, by rfl⟩ : syracuseStep 12960647 = 19440971) B19440971
theorem B6235273 : Blo 1705053 6235273 := bstep (se 2 (by rfl) ⟨2338227, by rfl⟩ : syracuseStep 6235273 = 4676455) B4676455
theorem B1705115 : Blo 1705053 1705115 := bstep (se 1 (by rfl) ⟨1278836, by rfl⟩ : syracuseStep 1705115 = 2557673) B2557673
theorem B1705119 : Blo 1705053 1705119 := bstep (se 1 (by rfl) ⟨1278839, by rfl⟩ : syracuseStep 1705119 = 2557679) B2557679
theorem B1705287 : Blo 1705053 1705287 := bstep (se 1 (by rfl) ⟨1278965, by rfl⟩ : syracuseStep 1705287 = 2557931) B2557931
theorem B6481235 : Blo 1705053 6481235 := bstep (se 1 (by rfl) ⟨4860926, by rfl⟩ : syracuseStep 6481235 = 9721853) B9721853
theorem B1705455 : Blo 1705053 1705455 := bstep (se 1 (by rfl) ⟨1279091, by rfl⟩ : syracuseStep 1705455 = 2558183) B2558183
theorem B6481403 : Blo 1705053 6481403 := bstep (se 1 (by rfl) ⟨4861052, by rfl⟩ : syracuseStep 6481403 = 9722105) B9722105
theorem B1705471 : Blo 1705053 1705471 := bstep (se 1 (by rfl) ⟨1279103, by rfl⟩ : syracuseStep 1705471 = 2558207) B2558207
theorem B6915611 : Blo 1705053 6915611 := bstep (se 1 (by rfl) ⟨5186708, by rfl⟩ : syracuseStep 6915611 = 10373417) B10373417
theorem B1705563 : Blo 1705053 1705563 := bstep (se 1 (by rfl) ⟨1279172, by rfl⟩ : syracuseStep 1705563 = 2558345) B2558345
theorem B7390939 : Blo 1705053 7390939 := bstep (se 1 (by rfl) ⟨5543204, by rfl⟩ : syracuseStep 7390939 = 11086409) B11086409
theorem B2877511 : Blo 1705053 2877511 := bstep (se 1 (by rfl) ⟨2158133, by rfl⟩ : syracuseStep 2877511 = 4316267) B4316267
theorem B2558171 : Blo 1705053 2558171 := bstep (se 1 (by rfl) ⟨1918628, by rfl⟩ : syracuseStep 2558171 = 3837257) B3837257
theorem B1706303 : Blo 1705053 1706303 := bstep (se 1 (by rfl) ⟨1279727, by rfl⟩ : syracuseStep 1706303 = 2559455) B2559455
theorem B1706343 : Blo 1705053 1706343 := bstep (se 1 (by rfl) ⟨1279757, by rfl⟩ : syracuseStep 1706343 = 2559515) B2559515
theorem B6564215 : Blo 1705053 6564215 := bstep (se 1 (by rfl) ⟨4923161, by rfl⟩ : syracuseStep 6564215 = 9846323) B9846323
theorem B2558399 : Blo 1705053 2558399 := bstep (se 1 (by rfl) ⟨1918799, by rfl⟩ : syracuseStep 2558399 = 3837599) B3837599
theorem B1706431 : Blo 1705053 1706431 := bstep (se 1 (by rfl) ⟨1279823, by rfl⟩ : syracuseStep 1706431 = 2559647) B2559647
theorem B1706607 : Blo 1705053 1706607 := bstep (se 1 (by rfl) ⟨1279955, by rfl⟩ : syracuseStep 1706607 = 2559911) B2559911
theorem B1706623 : Blo 1705053 1706623 := bstep (se 1 (by rfl) ⟨1279967, by rfl⟩ : syracuseStep 1706623 = 2559935) B2559935
theorem B1919695 : Blo 1705053 1919695 := bstep (se 1 (by rfl) ⟨1439771, by rfl⟩ : syracuseStep 1919695 = 2879543) B2879543
theorem B1706727 : Blo 1705053 1706727 := bstep (se 1 (by rfl) ⟨1280045, by rfl⟩ : syracuseStep 1706727 = 2560091) B2560091
theorem B2558699 : Blo 1705053 2558699 := bstep (se 1 (by rfl) ⟨1919024, by rfl⟩ : syracuseStep 2558699 = 3838049) B3838049
theorem B1706823 : Blo 1705053 1706823 := bstep (se 1 (by rfl) ⟨1280117, by rfl⟩ : syracuseStep 1706823 = 2560235) B2560235
theorem B6474599 : Blo 1705053 6474599 := bstep (se 1 (by rfl) ⟨4855949, by rfl⟩ : syracuseStep 6474599 = 9711899) B9711899
theorem B2558831 : Blo 1705053 2558831 := bstep (se 1 (by rfl) ⟨1919123, by rfl⟩ : syracuseStep 2558831 = 3838247) B3838247
theorem B1706863 : Blo 1705053 1706863 := bstep (se 1 (by rfl) ⟨1280147, by rfl⟩ : syracuseStep 1706863 = 2560295) B2560295
theorem B5835731 : Blo 1705053 5835731 := bstep (se 1 (by rfl) ⟨4376798, by rfl⟩ : syracuseStep 5835731 = 8753597) B8753597
theorem B1707039 : Blo 1705053 1707039 := bstep (se 1 (by rfl) ⟨1280279, by rfl⟩ : syracuseStep 1707039 = 2560559) B2560559
theorem B2878571 : Blo 1705053 2878571 := bstep (se 1 (by rfl) ⟨2158928, by rfl⟩ : syracuseStep 2878571 = 4317857) B4317857
theorem B3239023 : Blo 1705053 3239023 := bstep (se 1 (by rfl) ⟨2429267, by rfl⟩ : syracuseStep 3239023 = 4858535) B4858535
theorem B6474887 : Blo 1705053 6474887 := bstep (se 1 (by rfl) ⟨4856165, by rfl⟩ : syracuseStep 6474887 = 9712331) B9712331
theorem B10931345 : Blo 1705053 10931345 := bstep (se 2 (by rfl) ⟨4099254, by rfl⟩ : syracuseStep 10931345 = 8198509) B8198509
theorem B2305199 : Blo 1705053 2305199 := bstep (se 1 (by rfl) ⟨1728899, by rfl⟩ : syracuseStep 2305199 = 3457799) B3457799
theorem B93367541 : Blo 1705053 93367541 := bstep (se 5 (by rfl) ⟨4376603, by rfl⟩ : syracuseStep 93367541 = 8753207) B8753207
theorem B88608127 : Blo 1705053 88608127 := bstep (se 1 (by rfl) ⟨66456095, by rfl⟩ : syracuseStep 88608127 = 132912191) B132912191
theorem B20762011 : Blo 1705053 20762011 := bstep (se 1 (by rfl) ⟨15571508, by rfl⟩ : syracuseStep 20762011 = 31143017) B31143017
theorem B2879003 : Blo 1705053 2879003 := bstep (se 1 (by rfl) ⟨2159252, by rfl⟩ : syracuseStep 2879003 = 4318505) B4318505
theorem B2559599 : Blo 1705053 2559599 := bstep (se 1 (by rfl) ⟨1919699, by rfl⟩ : syracuseStep 2559599 = 3839399) B3839399
theorem B12955301 : Blo 1705053 12955301 := bstep (se 4 (by rfl) ⟨1214559, by rfl⟩ : syracuseStep 12955301 = 2429119) B2429119
theorem B2559671 : Blo 1705053 2559671 := bstep (se 1 (by rfl) ⟨1919753, by rfl⟩ : syracuseStep 2559671 = 3839507) B3839507
theorem B2559719 : Blo 1705053 2559719 := bstep (se 1 (by rfl) ⟨1919789, by rfl⟩ : syracuseStep 2559719 = 3839579) B3839579
theorem B3837887 : Blo 1705053 3837887 := bstep (se 1 (by rfl) ⟨2878415, by rfl⟩ : syracuseStep 3837887 = 5756831) B5756831
theorem B2560223 : Blo 1705053 2560223 := bstep (se 1 (by rfl) ⟨1920167, by rfl⟩ : syracuseStep 2560223 = 3840335) B3840335
theorem B2560283 : Blo 1705053 2560283 := bstep (se 1 (by rfl) ⟨1920212, by rfl⟩ : syracuseStep 2560283 = 3840425) B3840425
theorem B2879867 : Blo 1705053 2879867 := bstep (se 1 (by rfl) ⟨2159900, by rfl⟩ : syracuseStep 2879867 = 4319801) B4319801
theorem B5755319 : Blo 1705053 5755319 := bstep (se 1 (by rfl) ⟨4316489, by rfl⟩ : syracuseStep 5755319 = 8632979) B8632979
theorem B7778749 : Blo 1705053 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B2159131 : Blo 1705053 2159131 := bstep (se 1 (by rfl) ⟨1619348, by rfl⟩ : syracuseStep 2159131 = 3238697) B3238697
theorem B134787635 : Blo 1705053 134787635 := bstep (se 1 (by rfl) ⟨101090726, by rfl⟩ : syracuseStep 134787635 = 202181453) B202181453
theorem B6476345 : Blo 1705053 6476345 := bstep (se 2 (by rfl) ⟨2428629, by rfl⟩ : syracuseStep 6476345 = 4857259) B4857259
theorem B461238893 : Blo 1705053 461238893 := bstep (se 3 (by rfl) ⟨86482292, by rfl⟩ : syracuseStep 461238893 = 172964585) B172964585
theorem B3642347 : Blo 1705053 3642347 := bstep (se 1 (by rfl) ⟨2731760, by rfl⟩ : syracuseStep 3642347 = 5463521) B5463521
theorem B5756129 : Blo 1705053 5756129 := bstep (se 2 (by rfl) ⟨2158548, by rfl⟩ : syracuseStep 5756129 = 4317097) B4317097
theorem B2160103 : Blo 1705053 2160103 := bstep (se 1 (by rfl) ⟨1620077, by rfl⟩ : syracuseStep 2160103 = 3240155) B3240155
theorem B10925705 : Blo 1705053 10925705 := bstep (se 2 (by rfl) ⟨4097139, by rfl⟩ : syracuseStep 10925705 = 8194279) B8194279
theorem B7289135 : Blo 1705053 7289135 := bstep (se 1 (by rfl) ⟨5466851, by rfl⟩ : syracuseStep 7289135 = 10933703) B10933703
theorem B52533647 : Blo 1705053 52533647 := bstep (se 1 (by rfl) ⟨39400235, by rfl⟩ : syracuseStep 52533647 = 78800471) B78800471
theorem B43735625 : Blo 1705053 43735625 := bstep (se 2 (by rfl) ⟨16400859, by rfl⟩ : syracuseStep 43735625 = 32801719) B32801719
theorem B27663227 : Blo 1705053 27663227 := bstep (se 1 (by rfl) ⟨20747420, by rfl⟩ : syracuseStep 27663227 = 41494841) B41494841
theorem B8641403 : Blo 1705053 8641403 := bstep (se 1 (by rfl) ⟨6481052, by rfl⟩ : syracuseStep 8641403 = 12962105) B12962105
theorem B8633465 : Blo 1705053 8633465 := bstep (se 2 (by rfl) ⟨3237549, by rfl⟩ : syracuseStep 8633465 = 6475099) B6475099
theorem B3644585 : Blo 1705053 3644585 := bstep (se 2 (by rfl) ⟨1366719, by rfl⟩ : syracuseStep 3644585 = 2733439) B2733439
theorem B5758127 : Blo 1705053 5758127 := bstep (se 1 (by rfl) ⟨4318595, by rfl⟩ : syracuseStep 5758127 = 8637191) B8637191
theorem B89858423 : Blo 1705053 89858423 := bstep (se 1 (by rfl) ⟨67393817, by rfl⟩ : syracuseStep 89858423 = 134787635) B134787635
theorem B4317563 : Blo 1705053 4317563 := bstep (se 1 (by rfl) ⟨3238172, by rfl⟩ : syracuseStep 4317563 = 6476345) B6476345
theorem B10371665 : Blo 1705053 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B1705447 : Blo 1705053 1705447 := bstep (se 1 (by rfl) ⟨1279085, by rfl⟩ : syracuseStep 1705447 = 2558171) B2558171
theorem B4318697 : Blo 1705053 4318697 := bstep (se 2 (by rfl) ⟨1619511, by rfl⟩ : syracuseStep 4318697 = 3239023) B3239023
theorem B4859423 : Blo 1705053 4859423 := bstep (se 1 (by rfl) ⟨3644567, by rfl⟩ : syracuseStep 4859423 = 7289135) B7289135
theorem B4376143 : Blo 1705053 4376143 := bstep (se 1 (by rfl) ⟨3282107, by rfl⟩ : syracuseStep 4376143 = 6564215) B6564215
theorem B35022431 : Blo 1705053 35022431 := bstep (se 1 (by rfl) ⟨26266823, by rfl⟩ : syracuseStep 35022431 = 52533647) B52533647
theorem B1705599 : Blo 1705053 1705599 := bstep (se 1 (by rfl) ⟨1279199, by rfl⟩ : syracuseStep 1705599 = 2558399) B2558399
theorem B29157083 : Blo 1705053 29157083 := bstep (se 1 (by rfl) ⟨21867812, by rfl⟩ : syracuseStep 29157083 = 43735625) B43735625
theorem B1705799 : Blo 1705053 1705799 := bstep (se 1 (by rfl) ⟨1279349, by rfl⟩ : syracuseStep 1705799 = 2558699) B2558699
theorem B27682681 : Blo 1705053 27682681 := bstep (se 2 (by rfl) ⟨10381005, by rfl⟩ : syracuseStep 27682681 = 20762011) B20762011
theorem B1705887 : Blo 1705053 1705887 := bstep (se 1 (by rfl) ⟨1279415, by rfl⟩ : syracuseStep 1705887 = 2558831) B2558831
theorem B18442151 : Blo 1705053 18442151 := bstep (se 1 (by rfl) ⟨13831613, by rfl⟩ : syracuseStep 18442151 = 27663227) B27663227
theorem B5760935 : Blo 1705053 5760935 := bstep (se 1 (by rfl) ⟨4320701, by rfl⟩ : syracuseStep 5760935 = 8641403) B8641403
theorem B1919047 : Blo 1705053 1919047 := bstep (se 1 (by rfl) ⟨1439285, by rfl⟩ : syracuseStep 1919047 = 2878571) B2878571
theorem B62245027 : Blo 1705053 62245027 := bstep (se 1 (by rfl) ⟨46683770, by rfl⟩ : syracuseStep 62245027 = 93367541) B93367541
theorem B1919335 : Blo 1705053 1919335 := bstep (se 1 (by rfl) ⟨1439501, by rfl⟩ : syracuseStep 1919335 = 2879003) B2879003
theorem B1706399 : Blo 1705053 1706399 := bstep (se 1 (by rfl) ⟨1279799, by rfl⟩ : syracuseStep 1706399 = 2559599) B2559599
theorem B8636867 : Blo 1705053 8636867 := bstep (se 1 (by rfl) ⟨6477650, by rfl⟩ : syracuseStep 8636867 = 12955301) B12955301
theorem B1706447 : Blo 1705053 1706447 := bstep (se 1 (by rfl) ⟨1279835, by rfl⟩ : syracuseStep 1706447 = 2559671) B2559671
theorem B1706479 : Blo 1705053 1706479 := bstep (se 1 (by rfl) ⟨1279859, by rfl⟩ : syracuseStep 1706479 = 2559719) B2559719
theorem B2558591 : Blo 1705053 2558591 := bstep (se 1 (by rfl) ⟨1918943, by rfl⟩ : syracuseStep 2558591 = 3837887) B3837887
theorem B3836681 : Blo 1705053 3836681 := bstep (se 2 (by rfl) ⟨1438755, by rfl⟩ : syracuseStep 3836681 = 2877511) B2877511
theorem B1706815 : Blo 1705053 1706815 := bstep (se 1 (by rfl) ⟨1280111, by rfl⟩ : syracuseStep 1706815 = 2560223) B2560223
theorem B1706855 : Blo 1705053 1706855 := bstep (se 1 (by rfl) ⟨1280141, by rfl⟩ : syracuseStep 1706855 = 2560283) B2560283
theorem B1919911 : Blo 1705053 1919911 := bstep (se 1 (by rfl) ⟨1439933, by rfl⟩ : syracuseStep 1919911 = 2879867) B2879867
theorem B3836879 : Blo 1705053 3836879 := bstep (se 1 (by rfl) ⟨2877659, by rfl⟩ : syracuseStep 3836879 = 5755319) B5755319
theorem B21851207 : Blo 1705053 21851207 := bstep (se 1 (by rfl) ⟨16388405, by rfl⟩ : syracuseStep 21851207 = 32776811) B32776811
theorem B6147197 : Blo 1705053 6147197 := bstep (se 3 (by rfl) ⟨1152599, by rfl⟩ : syracuseStep 6147197 = 2305199) B2305199
theorem B12954815 : Blo 1705053 12954815 := bstep (se 1 (by rfl) ⟨9716111, by rfl⟩ : syracuseStep 12954815 = 19432223) B19432223
theorem B2878699 : Blo 1705053 2878699 := bstep (se 1 (by rfl) ⟨2159024, by rfl⟩ : syracuseStep 2878699 = 4318049) B4318049
theorem B2428231 : Blo 1705053 2428231 := bstep (se 1 (by rfl) ⟨1821173, by rfl⟩ : syracuseStep 2428231 = 3642347) B3642347
theorem B2878841 : Blo 1705053 2878841 := bstep (se 2 (by rfl) ⟨1079565, by rfl⟩ : syracuseStep 2878841 = 2159131) B2159131
theorem B13839785 : Blo 1705053 13839785 := bstep (se 2 (by rfl) ⟨5189919, by rfl⟩ : syracuseStep 13839785 = 10379839) B10379839
theorem B3837419 : Blo 1705053 3837419 := bstep (se 1 (by rfl) ⟨2878064, by rfl⟩ : syracuseStep 3837419 = 5756129) B5756129
theorem B4320823 : Blo 1705053 4320823 := bstep (se 1 (by rfl) ⟨3240617, by rfl⟩ : syracuseStep 4320823 = 6481235) B6481235
theorem B2559593 : Blo 1705053 2559593 := bstep (se 2 (by rfl) ⟨959847, by rfl⟩ : syracuseStep 2559593 = 1919695) B1919695
theorem B4320935 : Blo 1705053 4320935 := bstep (se 1 (by rfl) ⟨3240701, by rfl⟩ : syracuseStep 4320935 = 6481403) B6481403
theorem B7286537 : Blo 1705053 7286537 := bstep (se 2 (by rfl) ⟨2732451, by rfl⟩ : syracuseStep 7286537 = 5464903) B5464903
theorem B29135213 : Blo 1705053 29135213 := bstep (se 3 (by rfl) ⟨5462852, by rfl⟩ : syracuseStep 29135213 = 10925705) B10925705
theorem B2880137 : Blo 1705053 2880137 := bstep (se 2 (by rfl) ⟨1080051, by rfl⟩ : syracuseStep 2880137 = 2160103) B2160103
theorem B10924733 : Blo 1705053 10924733 := bstep (se 3 (by rfl) ⟨2048387, by rfl⟩ : syracuseStep 10924733 = 4096775) B4096775
theorem B5755643 : Blo 1705053 5755643 := bstep (se 1 (by rfl) ⟨4316732, by rfl⟩ : syracuseStep 5755643 = 8633465) B8633465
theorem B7287563 : Blo 1705053 7287563 := bstep (se 1 (by rfl) ⟨5465672, by rfl⟩ : syracuseStep 7287563 = 10931345) B10931345
theorem B2429723 : Blo 1705053 2429723 := bstep (se 1 (by rfl) ⟨1822292, by rfl⟩ : syracuseStep 2429723 = 3644585) B3644585
theorem B3838751 : Blo 1705053 3838751 := bstep (se 1 (by rfl) ⟨2879063, by rfl⟩ : syracuseStep 3838751 = 5758127) B5758127
theorem B62247797 : Blo 1705053 62247797 := bstep (se 5 (by rfl) ⟨2917865, by rfl⟩ : syracuseStep 62247797 = 5835731) B5835731
theorem B19699199 : Blo 1705053 19699199 := bstep (se 1 (by rfl) ⟨14774399, by rfl⟩ : syracuseStep 19699199 = 29548799) B29548799
theorem B4675175 : Blo 1705053 4675175 := bstep (se 1 (by rfl) ⟨3506381, by rfl⟩ : syracuseStep 4675175 = 7012763) B7012763
theorem B307492595 : Blo 1705053 307492595 := bstep (se 1 (by rfl) ⟨230619446, by rfl⟩ : syracuseStep 307492595 = 461238893) B461238893
theorem B141989723 : Blo 1705053 141989723 := bstep (se 1 (by rfl) ⟨106492292, by rfl⟩ : syracuseStep 141989723 = 212984585) B212984585
theorem B4609889 : Blo 1705053 4609889 := bstep (se 2 (by rfl) ⟨1728708, by rfl⟩ : syracuseStep 4609889 = 3457417) B3457417
theorem B8640431 : Blo 1705053 8640431 := bstep (se 1 (by rfl) ⟨6480323, by rfl⟩ : syracuseStep 8640431 = 12960647) B12960647
theorem B4610407 : Blo 1705053 4610407 := bstep (se 1 (by rfl) ⟨3457805, by rfl⟩ : syracuseStep 4610407 = 6915611) B6915611
theorem B8313697 : Blo 1705053 8313697 := bstep (se 2 (by rfl) ⟨3117636, by rfl⟩ : syracuseStep 8313697 = 6235273) B6235273
theorem B118144169 : Blo 1705053 118144169 := bstep (se 2 (by rfl) ⟨44304063, by rfl⟩ : syracuseStep 118144169 = 88608127) B88608127
theorem B4316399 : Blo 1705053 4316399 := bstep (se 1 (by rfl) ⟨3237299, by rfl⟩ : syracuseStep 4316399 = 6474599) B6474599
theorem B4316591 : Blo 1705053 4316591 := bstep (se 1 (by rfl) ⟨3237443, by rfl⟩ : syracuseStep 4316591 = 6474887) B6474887
theorem B9854585 : Blo 1705053 9854585 := bstep (se 2 (by rfl) ⟨3695469, by rfl⟩ : syracuseStep 9854585 = 7390939) B7390939
theorem B82993369 : Blo 1705053 82993369 := bstep (se 2 (by rfl) ⟨31122513, by rfl⟩ : syracuseStep 82993369 = 62245027) B62245027
theorem B19423475 : Blo 1705053 19423475 := bstep (se 1 (by rfl) ⟨14567606, by rfl⟩ : syracuseStep 19423475 = 29135213) B29135213
theorem B7283155 : Blo 1705053 7283155 := bstep (se 1 (by rfl) ⟨5462366, by rfl⟩ : syracuseStep 7283155 = 10924733) B10924733
theorem B4858375 : Blo 1705053 4858375 := bstep (se 1 (by rfl) ⟨3643781, by rfl⟩ : syracuseStep 4858375 = 7287563) B7287563
theorem B13132799 : Blo 1705053 13132799 := bstep (se 1 (by rfl) ⟨9849599, by rfl⟩ : syracuseStep 13132799 = 19699199) B19699199
theorem B23348287 : Blo 1705053 23348287 := bstep (se 1 (by rfl) ⟨17511215, by rfl⟩ : syracuseStep 23348287 = 35022431) B35022431
theorem B94659815 : Blo 1705053 94659815 := bstep (se 1 (by rfl) ⟨70994861, by rfl⟩ : syracuseStep 94659815 = 141989723) B141989723
theorem B3073259 : Blo 1705053 3073259 := bstep (se 1 (by rfl) ⟨2304944, by rfl⟩ : syracuseStep 3073259 = 4609889) B4609889
theorem B5760287 : Blo 1705053 5760287 := bstep (se 1 (by rfl) ⟨4320215, by rfl⟩ : syracuseStep 5760287 = 8640431) B8640431
theorem B27657773 : Blo 1705053 27657773 := bstep (se 3 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 27657773 = 10371665) B10371665
theorem B1705727 : Blo 1705053 1705727 := bstep (se 1 (by rfl) ⟨1279295, by rfl⟩ : syracuseStep 1705727 = 2558591) B2558591
theorem B3237641 : Blo 1705053 3237641 := bstep (se 2 (by rfl) ⟨1214115, by rfl⟩ : syracuseStep 3237641 = 2428231) B2428231
theorem B2557787 : Blo 1705053 2557787 := bstep (se 1 (by rfl) ⟨1918340, by rfl⟩ : syracuseStep 2557787 = 3836681) B3836681
theorem B2557919 : Blo 1705053 2557919 := bstep (se 1 (by rfl) ⟨1918439, by rfl⟩ : syracuseStep 2557919 = 3836879) B3836879
theorem B14567471 : Blo 1705053 14567471 := bstep (se 1 (by rfl) ⟨10925603, by rfl⟩ : syracuseStep 14567471 = 21851207) B21851207
theorem B5761097 : Blo 1705053 5761097 := bstep (se 2 (by rfl) ⟨2160411, by rfl⟩ : syracuseStep 5761097 = 4320823) B4320823
theorem B4098131 : Blo 1705053 4098131 := bstep (se 1 (by rfl) ⟨3073598, by rfl⟩ : syracuseStep 4098131 = 6147197) B6147197
theorem B5834857 : Blo 1705053 5834857 := bstep (se 2 (by rfl) ⟨2188071, by rfl⟩ : syracuseStep 5834857 = 4376143) B4376143
theorem B8636543 : Blo 1705053 8636543 := bstep (se 1 (by rfl) ⟨6477407, by rfl⟩ : syracuseStep 8636543 = 12954815) B12954815
theorem B2877599 : Blo 1705053 2877599 := bstep (se 1 (by rfl) ⟨2158199, by rfl⟩ : syracuseStep 2877599 = 4316399) B4316399
theorem B1919227 : Blo 1705053 1919227 := bstep (se 1 (by rfl) ⟨1439420, by rfl⟩ : syracuseStep 1919227 = 2878841) B2878841
theorem B9226523 : Blo 1705053 9226523 := bstep (se 1 (by rfl) ⟨6919892, by rfl⟩ : syracuseStep 9226523 = 13839785) B13839785
theorem B2877727 : Blo 1705053 2877727 := bstep (se 1 (by rfl) ⟨2158295, by rfl⟩ : syracuseStep 2877727 = 4316591) B4316591
theorem B2558279 : Blo 1705053 2558279 := bstep (se 1 (by rfl) ⟨1918709, by rfl⟩ : syracuseStep 2558279 = 3837419) B3837419
theorem B1706395 : Blo 1705053 1706395 := bstep (se 1 (by rfl) ⟨1279796, by rfl⟩ : syracuseStep 1706395 = 2559593) B2559593
theorem B2558729 : Blo 1705053 2558729 := bstep (se 2 (by rfl) ⟨959523, by rfl⟩ : syracuseStep 2558729 = 1919047) B1919047
theorem B2878375 : Blo 1705053 2878375 := bstep (se 1 (by rfl) ⟨2158781, by rfl⟩ : syracuseStep 2878375 = 4317563) B4317563
theorem B1920091 : Blo 1705053 1920091 := bstep (se 1 (by rfl) ⟨1440068, by rfl⟩ : syracuseStep 1920091 = 2880137) B2880137
theorem B6147209 : Blo 1705053 6147209 := bstep (se 2 (by rfl) ⟨2305203, by rfl⟩ : syracuseStep 6147209 = 4610407) B4610407
theorem B2559113 : Blo 1705053 2559113 := bstep (se 2 (by rfl) ⟨959667, by rfl⟩ : syracuseStep 2559113 = 1919335) B1919335
theorem B3837095 : Blo 1705053 3837095 := bstep (se 1 (by rfl) ⟨2877821, by rfl⟩ : syracuseStep 3837095 = 5755643) B5755643
theorem B2559167 : Blo 1705053 2559167 := bstep (se 1 (by rfl) ⟨1919375, by rfl⟩ : syracuseStep 2559167 = 3838751) B3838751
theorem B2879131 : Blo 1705053 2879131 := bstep (se 1 (by rfl) ⟨2159348, by rfl⟩ : syracuseStep 2879131 = 4318697) B4318697
theorem B3239615 : Blo 1705053 3239615 := bstep (se 1 (by rfl) ⟨2429711, by rfl⟩ : syracuseStep 3239615 = 4859423) B4859423
theorem B3116783 : Blo 1705053 3116783 := bstep (se 1 (by rfl) ⟨2337587, by rfl⟩ : syracuseStep 3116783 = 4675175) B4675175
theorem B2559881 : Blo 1705053 2559881 := bstep (se 2 (by rfl) ⟨959955, by rfl⟩ : syracuseStep 2559881 = 1919911) B1919911
theorem B3838265 : Blo 1705053 3838265 := bstep (se 2 (by rfl) ⟨1439349, by rfl⟩ : syracuseStep 3838265 = 2878699) B2878699
theorem B44339717 : Blo 1705053 44339717 := bstep (se 4 (by rfl) ⟨4156848, by rfl⟩ : syracuseStep 44339717 = 8313697) B8313697
theorem B78762779 : Blo 1705053 78762779 := bstep (se 1 (by rfl) ⟨59072084, by rfl⟩ : syracuseStep 78762779 = 118144169) B118144169
theorem B2880623 : Blo 1705053 2880623 := bstep (se 1 (by rfl) ⟨2160467, by rfl⟩ : syracuseStep 2880623 = 4320935) B4320935
theorem B36910241 : Blo 1705053 36910241 := bstep (se 2 (by rfl) ⟨13841340, by rfl⟩ : syracuseStep 36910241 = 27682681) B27682681
theorem B41498531 : Blo 1705053 41498531 := bstep (se 1 (by rfl) ⟨31123898, by rfl⟩ : syracuseStep 41498531 = 62247797) B62247797
theorem B239622461 : Blo 1705053 239622461 := bstep (se 3 (by rfl) ⟨44929211, by rfl⟩ : syracuseStep 239622461 = 89858423) B89858423
theorem B19438055 : Blo 1705053 19438055 := bstep (se 1 (by rfl) ⟨14578541, by rfl⟩ : syracuseStep 19438055 = 29157083) B29157083
theorem B204995063 : Blo 1705053 204995063 := bstep (se 1 (by rfl) ⟨153746297, by rfl⟩ : syracuseStep 204995063 = 307492595) B307492595
theorem B12294767 : Blo 1705053 12294767 := bstep (se 1 (by rfl) ⟨9221075, by rfl⟩ : syracuseStep 12294767 = 18442151) B18442151
theorem B3840623 : Blo 1705053 3840623 := bstep (se 1 (by rfl) ⟨2880467, by rfl⟩ : syracuseStep 3840623 = 5760935) B5760935
theorem B5757911 : Blo 1705053 5757911 := bstep (se 1 (by rfl) ⟨4318433, by rfl⟩ : syracuseStep 5757911 = 8636867) B8636867
theorem B19430765 : Blo 1705053 19430765 := bstep (se 3 (by rfl) ⟨3643268, by rfl⟩ : syracuseStep 19430765 = 7286537) B7286537
theorem B6479261 : Blo 1705053 6479261 := bstep (se 3 (by rfl) ⟨1214861, by rfl⟩ : syracuseStep 6479261 = 2429723) B2429723
theorem B6569723 : Blo 1705053 6569723 := bstep (se 1 (by rfl) ⟨4927292, by rfl⟩ : syracuseStep 6569723 = 9854585) B9854585
theorem B110657825 : Blo 1705053 110657825 := bstep (se 2 (by rfl) ⟨41496684, by rfl⟩ : syracuseStep 110657825 = 82993369) B82993369
theorem B16392557 : Blo 1705053 16392557 := bstep (se 3 (by rfl) ⟨3073604, by rfl⟩ : syracuseStep 16392557 = 6147209) B6147209
theorem B1705191 : Blo 1705053 1705191 := bstep (se 1 (by rfl) ⟨1278893, by rfl⟩ : syracuseStep 1705191 = 2557787) B2557787
theorem B27665687 : Blo 1705053 27665687 := bstep (se 1 (by rfl) ⟨20749265, by rfl⟩ : syracuseStep 27665687 = 41498531) B41498531
theorem B1705279 : Blo 1705053 1705279 := bstep (se 1 (by rfl) ⟨1278959, by rfl⟩ : syracuseStep 1705279 = 2557919) B2557919
theorem B31131049 : Blo 1705053 31131049 := bstep (se 2 (by rfl) ⟨11674143, by rfl⟩ : syracuseStep 31131049 = 23348287) B23348287
theorem B1918399 : Blo 1705053 1918399 := bstep (se 1 (by rfl) ⟨1438799, by rfl⟩ : syracuseStep 1918399 = 2877599) B2877599
theorem B1705519 : Blo 1705053 1705519 := bstep (se 1 (by rfl) ⟨1279139, by rfl⟩ : syracuseStep 1705519 = 2558279) B2558279
theorem B1705819 : Blo 1705053 1705819 := bstep (se 1 (by rfl) ⟨1279364, by rfl⟩ : syracuseStep 1705819 = 2558729) B2558729
theorem B1706075 : Blo 1705053 1706075 := bstep (se 1 (by rfl) ⟨1279556, by rfl⟩ : syracuseStep 1706075 = 2559113) B2559113
theorem B2558063 : Blo 1705053 2558063 := bstep (se 1 (by rfl) ⟨1918547, by rfl⟩ : syracuseStep 2558063 = 3837095) B3837095
theorem B1706111 : Blo 1705053 1706111 := bstep (se 1 (by rfl) ⟨1279583, by rfl⟩ : syracuseStep 1706111 = 2559167) B2559167
theorem B12953843 : Blo 1705053 12953843 := bstep (se 1 (by rfl) ⟨9715382, by rfl⟩ : syracuseStep 12953843 = 19430765) B19430765
theorem B4319507 : Blo 1705053 4319507 := bstep (se 1 (by rfl) ⟨3239630, by rfl⟩ : syracuseStep 4319507 = 6479261) B6479261
theorem B1706587 : Blo 1705053 1706587 := bstep (se 1 (by rfl) ⟨1279940, by rfl⟩ : syracuseStep 1706587 = 2559881) B2559881
theorem B2558843 : Blo 1705053 2558843 := bstep (se 1 (by rfl) ⟨1919132, by rfl⟩ : syracuseStep 2558843 = 3838265) B3838265
theorem B2558969 : Blo 1705053 2558969 := bstep (se 2 (by rfl) ⟨959613, by rfl⟩ : syracuseStep 2558969 = 1919227) B1919227
theorem B29559811 : Blo 1705053 29559811 := bstep (se 1 (by rfl) ⟨22169858, by rfl⟩ : syracuseStep 29559811 = 44339717) B44339717
theorem B3836969 : Blo 1705053 3836969 := bstep (se 2 (by rfl) ⟨1438863, by rfl⟩ : syracuseStep 3836969 = 2877727) B2877727
theorem B9710873 : Blo 1705053 9710873 := bstep (se 2 (by rfl) ⟨3641577, by rfl⟩ : syracuseStep 9710873 = 7283155) B7283155
theorem B8195357 : Blo 1705053 8195357 := bstep (se 3 (by rfl) ⟨1536629, by rfl⟩ : syracuseStep 8195357 = 3073259) B3073259
theorem B1920415 : Blo 1705053 1920415 := bstep (se 1 (by rfl) ⟨1440311, by rfl⟩ : syracuseStep 1920415 = 2880623) B2880623
theorem B63106543 : Blo 1705053 63106543 := bstep (se 1 (by rfl) ⟨47329907, by rfl⟩ : syracuseStep 63106543 = 94659815) B94659815
theorem B2158427 : Blo 1705053 2158427 := bstep (se 1 (by rfl) ⟨1618820, by rfl⟩ : syracuseStep 2158427 = 3237641) B3237641
theorem B3837833 : Blo 1705053 3837833 := bstep (se 2 (by rfl) ⟨1439187, by rfl⟩ : syracuseStep 3837833 = 2878375) B2878375
theorem B9711647 : Blo 1705053 9711647 := bstep (se 1 (by rfl) ⟨7283735, by rfl⟩ : syracuseStep 9711647 = 14567471) B14567471
theorem B2732087 : Blo 1705053 2732087 := bstep (se 1 (by rfl) ⟨2049065, by rfl⟩ : syracuseStep 2732087 = 4098131) B4098131
theorem B2560121 : Blo 1705053 2560121 := bstep (se 2 (by rfl) ⟨960045, by rfl⟩ : syracuseStep 2560121 = 1920091) B1920091
theorem B159748307 : Blo 1705053 159748307 := bstep (se 1 (by rfl) ⟨119811230, by rfl⟩ : syracuseStep 159748307 = 239622461) B239622461
theorem B136663375 : Blo 1705053 136663375 := bstep (se 1 (by rfl) ⟨102497531, by rfl⟩ : syracuseStep 136663375 = 204995063) B204995063
theorem B8196511 : Blo 1705053 8196511 := bstep (se 1 (by rfl) ⟨6147383, by rfl⟩ : syracuseStep 8196511 = 12294767) B12294767
theorem B2560415 : Blo 1705053 2560415 := bstep (se 1 (by rfl) ⟨1920311, by rfl⟩ : syracuseStep 2560415 = 3840623) B3840623
theorem B8638973 : Blo 1705053 8638973 := bstep (se 3 (by rfl) ⟨1619807, by rfl⟩ : syracuseStep 8638973 = 3239615) B3239615
theorem B3838607 : Blo 1705053 3838607 := bstep (se 1 (by rfl) ⟨2878955, by rfl⟩ : syracuseStep 3838607 = 5757911) B5757911
theorem B3838841 : Blo 1705053 3838841 := bstep (se 2 (by rfl) ⟨1439565, by rfl⟩ : syracuseStep 3838841 = 2879131) B2879131
theorem B2077855 : Blo 1705053 2077855 := bstep (se 1 (by rfl) ⟨1558391, by rfl⟩ : syracuseStep 2077855 = 3116783) B3116783
theorem B4379815 : Blo 1705053 4379815 := bstep (se 1 (by rfl) ⟨3284861, by rfl⟩ : syracuseStep 4379815 = 6569723) B6569723
theorem B7779809 : Blo 1705053 7779809 := bstep (se 2 (by rfl) ⟨2917428, by rfl⟩ : syracuseStep 7779809 = 5834857) B5834857
theorem B12948983 : Blo 1705053 12948983 := bstep (se 1 (by rfl) ⟨9711737, by rfl⟩ : syracuseStep 12948983 = 19423475) B19423475
theorem B52508519 : Blo 1705053 52508519 := bstep (se 1 (by rfl) ⟨39381389, by rfl⟩ : syracuseStep 52508519 = 78762779) B78762779
theorem B8755199 : Blo 1705053 8755199 := bstep (se 1 (by rfl) ⟨6566399, by rfl⟩ : syracuseStep 8755199 = 13132799) B13132799
theorem B6477833 : Blo 1705053 6477833 := bstep (se 2 (by rfl) ⟨2429187, by rfl⟩ : syracuseStep 6477833 = 4858375) B4858375
theorem B24606827 : Blo 1705053 24606827 := bstep (se 1 (by rfl) ⟨18455120, by rfl⟩ : syracuseStep 24606827 = 36910241) B36910241
theorem B3840191 : Blo 1705053 3840191 := bstep (se 1 (by rfl) ⟨2880143, by rfl⟩ : syracuseStep 3840191 = 5760287) B5760287
theorem B18438515 : Blo 1705053 18438515 := bstep (se 1 (by rfl) ⟨13828886, by rfl⟩ : syracuseStep 18438515 = 27657773) B27657773
theorem B3840731 : Blo 1705053 3840731 := bstep (se 1 (by rfl) ⟨2880548, by rfl⟩ : syracuseStep 3840731 = 5761097) B5761097
theorem B5757695 : Blo 1705053 5757695 := bstep (se 1 (by rfl) ⟨4318271, by rfl⟩ : syracuseStep 5757695 = 8636543) B8636543
theorem B6151015 : Blo 1705053 6151015 := bstep (se 1 (by rfl) ⟨4613261, by rfl⟩ : syracuseStep 6151015 = 9226523) B9226523
theorem B12958703 : Blo 1705053 12958703 := bstep (se 1 (by rfl) ⟨9719027, by rfl⟩ : syracuseStep 12958703 = 19438055) B19438055
theorem B10928371 : Blo 1705053 10928371 := bstep (se 1 (by rfl) ⟨8196278, by rfl⟩ : syracuseStep 10928371 = 16392557) B16392557
theorem B5759315 : Blo 1705053 5759315 := bstep (se 1 (by rfl) ⟨4319486, by rfl⟩ : syracuseStep 5759315 = 8638973) B8638973
theorem B10928681 : Blo 1705053 10928681 := bstep (se 2 (by rfl) ⟨4098255, by rfl⟩ : syracuseStep 10928681 = 8196511) B8196511
theorem B44327573 : Blo 1705053 44327573 := bstep (se 6 (by rfl) ⟨1038927, by rfl⟩ : syracuseStep 44327573 = 2077855) B2077855
theorem B5186539 : Blo 1705053 5186539 := bstep (se 1 (by rfl) ⟨3889904, by rfl⟩ : syracuseStep 5186539 = 7779809) B7779809
theorem B8201353 : Blo 1705053 8201353 := bstep (se 2 (by rfl) ⟨3075507, by rfl⟩ : syracuseStep 8201353 = 6151015) B6151015
theorem B35005679 : Blo 1705053 35005679 := bstep (se 1 (by rfl) ⟨26254259, by rfl⟩ : syracuseStep 35005679 = 52508519) B52508519
theorem B39413081 : Blo 1705053 39413081 := bstep (se 2 (by rfl) ⟨14779905, by rfl⟩ : syracuseStep 39413081 = 29559811) B29559811
theorem B4318555 : Blo 1705053 4318555 := bstep (se 1 (by rfl) ⟨3238916, by rfl⟩ : syracuseStep 4318555 = 6477833) B6477833
theorem B1705375 : Blo 1705053 1705375 := bstep (se 1 (by rfl) ⟨1279031, by rfl⟩ : syracuseStep 1705375 = 2558063) B2558063
theorem B8635895 : Blo 1705053 8635895 := bstep (se 1 (by rfl) ⟨6476921, by rfl⟩ : syracuseStep 8635895 = 12953843) B12953843
theorem B1705895 : Blo 1705053 1705895 := bstep (se 1 (by rfl) ⟨1279421, by rfl⟩ : syracuseStep 1705895 = 2558843) B2558843
theorem B2557865 : Blo 1705053 2557865 := bstep (se 2 (by rfl) ⟨959199, by rfl⟩ : syracuseStep 2557865 = 1918399) B1918399
theorem B1705979 : Blo 1705053 1705979 := bstep (se 1 (by rfl) ⟨1279484, by rfl⟩ : syracuseStep 1705979 = 2558969) B2558969
theorem B2557979 : Blo 1705053 2557979 := bstep (se 1 (by rfl) ⟨1918484, by rfl⟩ : syracuseStep 2557979 = 3836969) B3836969
theorem B6473915 : Blo 1705053 6473915 := bstep (se 1 (by rfl) ⟨4855436, by rfl⟩ : syracuseStep 6473915 = 9710873) B9710873
theorem B2558555 : Blo 1705053 2558555 := bstep (se 1 (by rfl) ⟨1918916, by rfl⟩ : syracuseStep 2558555 = 3837833) B3837833
theorem B6474431 : Blo 1705053 6474431 := bstep (se 1 (by rfl) ⟨4855823, by rfl⟩ : syracuseStep 6474431 = 9711647) B9711647
theorem B1706747 : Blo 1705053 1706747 := bstep (se 1 (by rfl) ⟨1280060, by rfl⟩ : syracuseStep 1706747 = 2560121) B2560121
theorem B106498871 : Blo 1705053 106498871 := bstep (se 1 (by rfl) ⟨79874153, by rfl⟩ : syracuseStep 106498871 = 159748307) B159748307
theorem B7285565 : Blo 1705053 7285565 := bstep (se 3 (by rfl) ⟨1366043, by rfl⟩ : syracuseStep 7285565 = 2732087) B2732087
theorem B73771883 : Blo 1705053 73771883 := bstep (se 1 (by rfl) ⟨55328912, by rfl⟩ : syracuseStep 73771883 = 110657825) B110657825
theorem B1706943 : Blo 1705053 1706943 := bstep (se 1 (by rfl) ⟨1280207, by rfl⟩ : syracuseStep 1706943 = 2560415) B2560415
theorem B2559071 : Blo 1705053 2559071 := bstep (se 1 (by rfl) ⟨1919303, by rfl⟩ : syracuseStep 2559071 = 3838607) B3838607
theorem B182217833 : Blo 1705053 182217833 := bstep (se 2 (by rfl) ⟨68331687, by rfl⟩ : syracuseStep 182217833 = 136663375) B136663375
theorem B2559227 : Blo 1705053 2559227 := bstep (se 1 (by rfl) ⟨1919420, by rfl⟩ : syracuseStep 2559227 = 3838841) B3838841
theorem B18443791 : Blo 1705053 18443791 := bstep (se 1 (by rfl) ⟨13832843, by rfl⟩ : syracuseStep 18443791 = 27665687) B27665687
theorem B23359013 : Blo 1705053 23359013 := bstep (se 4 (by rfl) ⟨2189907, by rfl⟩ : syracuseStep 23359013 = 4379815) B4379815
theorem B5836799 : Blo 1705053 5836799 := bstep (se 1 (by rfl) ⟨4377599, by rfl⟩ : syracuseStep 5836799 = 8755199) B8755199
theorem B16404551 : Blo 1705053 16404551 := bstep (se 1 (by rfl) ⟨12303413, by rfl⟩ : syracuseStep 16404551 = 24606827) B24606827
theorem B2560127 : Blo 1705053 2560127 := bstep (se 1 (by rfl) ⟨1920095, by rfl⟩ : syracuseStep 2560127 = 3840191) B3840191
theorem B2879671 : Blo 1705053 2879671 := bstep (se 1 (by rfl) ⟨2159753, by rfl⟩ : syracuseStep 2879671 = 4319507) B4319507
theorem B12292343 : Blo 1705053 12292343 := bstep (se 1 (by rfl) ⟨9219257, by rfl⟩ : syracuseStep 12292343 = 18438515) B18438515
theorem B2560487 : Blo 1705053 2560487 := bstep (se 1 (by rfl) ⟨1920365, by rfl⟩ : syracuseStep 2560487 = 3840731) B3840731
theorem B3838463 : Blo 1705053 3838463 := bstep (se 1 (by rfl) ⟨2878847, by rfl⟩ : syracuseStep 3838463 = 5757695) B5757695
theorem B2560553 : Blo 1705053 2560553 := bstep (se 2 (by rfl) ⟨960207, by rfl⟩ : syracuseStep 2560553 = 1920415) B1920415
theorem B8639135 : Blo 1705053 8639135 := bstep (se 1 (by rfl) ⟨6479351, by rfl⟩ : syracuseStep 8639135 = 12958703) B12958703
theorem B5755805 : Blo 1705053 5755805 := bstep (se 3 (by rfl) ⟨1079213, by rfl⟩ : syracuseStep 5755805 = 2158427) B2158427
theorem B8632655 : Blo 1705053 8632655 := bstep (se 1 (by rfl) ⟨6474491, by rfl⟩ : syracuseStep 8632655 = 12948983) B12948983
theorem B41508065 : Blo 1705053 41508065 := bstep (se 2 (by rfl) ⟨15565524, by rfl⟩ : syracuseStep 41508065 = 31131049) B31131049
theorem B5463571 : Blo 1705053 5463571 := bstep (se 1 (by rfl) ⟨4097678, by rfl⟩ : syracuseStep 5463571 = 8195357) B8195357
theorem B336568229 : Blo 1705053 336568229 := bstep (se 4 (by rfl) ⟨31553271, by rfl⟩ : syracuseStep 336568229 = 63106543) B63106543
theorem B10936367 : Blo 1705053 10936367 := bstep (se 1 (by rfl) ⟨8202275, by rfl⟩ : syracuseStep 10936367 = 16404551) B16404551
theorem B5759423 : Blo 1705053 5759423 := bstep (se 1 (by rfl) ⟨4319567, by rfl⟩ : syracuseStep 5759423 = 8639135) B8639135
theorem B1705243 : Blo 1705053 1705243 := bstep (se 1 (by rfl) ⟨1278932, by rfl⟩ : syracuseStep 1705243 = 2557865) B2557865
theorem B6915385 : Blo 1705053 6915385 := bstep (se 2 (by rfl) ⟨2593269, by rfl⟩ : syracuseStep 6915385 = 5186539) B5186539
theorem B1705319 : Blo 1705053 1705319 := bstep (se 1 (by rfl) ⟨1278989, by rfl⟩ : syracuseStep 1705319 = 2557979) B2557979
theorem B1705703 : Blo 1705053 1705703 := bstep (se 1 (by rfl) ⟨1279277, by rfl⟩ : syracuseStep 1705703 = 2558555) B2558555
theorem B7284761 : Blo 1705053 7284761 := bstep (se 2 (by rfl) ⟨2731785, by rfl⟩ : syracuseStep 7284761 = 5463571) B5463571
theorem B1706047 : Blo 1705053 1706047 := bstep (se 1 (by rfl) ⟨1279535, by rfl⟩ : syracuseStep 1706047 = 2559071) B2559071
theorem B1706151 : Blo 1705053 1706151 := bstep (se 1 (by rfl) ⟨1279613, by rfl⟩ : syracuseStep 1706151 = 2559227) B2559227
theorem B1706751 : Blo 1705053 1706751 := bstep (se 1 (by rfl) ⟨1280063, by rfl⟩ : syracuseStep 1706751 = 2560127) B2560127
theorem B8194895 : Blo 1705053 8194895 := bstep (se 1 (by rfl) ⟨6146171, by rfl⟩ : syracuseStep 8194895 = 12292343) B12292343
theorem B1706991 : Blo 1705053 1706991 := bstep (se 1 (by rfl) ⟨1280243, by rfl⟩ : syracuseStep 1706991 = 2560487) B2560487
theorem B2558975 : Blo 1705053 2558975 := bstep (se 1 (by rfl) ⟨1919231, by rfl⟩ : syracuseStep 2558975 = 3838463) B3838463
theorem B7285787 : Blo 1705053 7285787 := bstep (se 1 (by rfl) ⟨5464340, by rfl⟩ : syracuseStep 7285787 = 10928681) B10928681
theorem B1707035 : Blo 1705053 1707035 := bstep (se 1 (by rfl) ⟨1280276, by rfl⟩ : syracuseStep 1707035 = 2560553) B2560553
theorem B29551715 : Blo 1705053 29551715 := bstep (se 1 (by rfl) ⟨22163786, by rfl⟩ : syracuseStep 29551715 = 44327573) B44327573
theorem B3837203 : Blo 1705053 3837203 := bstep (se 1 (by rfl) ⟨2877902, by rfl⟩ : syracuseStep 3837203 = 5755805) B5755805
theorem B5755103 : Blo 1705053 5755103 := bstep (se 1 (by rfl) ⟨4316327, by rfl⟩ : syracuseStep 5755103 = 8632655) B8632655
theorem B49181255 : Blo 1705053 49181255 := bstep (se 1 (by rfl) ⟨36885941, by rfl⟩ : syracuseStep 49181255 = 73771883) B73771883
theorem B3839543 : Blo 1705053 3839543 := bstep (se 1 (by rfl) ⟨2879657, by rfl⟩ : syracuseStep 3839543 = 5759315) B5759315
theorem B3839561 : Blo 1705053 3839561 := bstep (se 2 (by rfl) ⟨1439835, by rfl⟩ : syracuseStep 3839561 = 2879671) B2879671
theorem B14571161 : Blo 1705053 14571161 := bstep (se 2 (by rfl) ⟨5464185, by rfl⟩ : syracuseStep 14571161 = 10928371) B10928371
theorem B23337119 : Blo 1705053 23337119 := bstep (se 1 (by rfl) ⟨17502839, by rfl⟩ : syracuseStep 23337119 = 35005679) B35005679
theorem B105101549 : Blo 1705053 105101549 := bstep (se 3 (by rfl) ⟨19706540, by rfl⟩ : syracuseStep 105101549 = 39413081) B39413081
theorem B5757263 : Blo 1705053 5757263 := bstep (se 1 (by rfl) ⟨4317947, by rfl⟩ : syracuseStep 5757263 = 8635895) B8635895
theorem B4315943 : Blo 1705053 4315943 := bstep (se 1 (by rfl) ⟨3236957, by rfl⟩ : syracuseStep 4315943 = 6473915) B6473915
theorem B10935137 : Blo 1705053 10935137 := bstep (se 2 (by rfl) ⟨4100676, by rfl⟩ : syracuseStep 10935137 = 8201353) B8201353
theorem B5758073 : Blo 1705053 5758073 := bstep (se 2 (by rfl) ⟨2159277, by rfl⟩ : syracuseStep 5758073 = 4318555) B4318555
theorem B4316287 : Blo 1705053 4316287 := bstep (se 1 (by rfl) ⟨3237215, by rfl⟩ : syracuseStep 4316287 = 6474431) B6474431
theorem B70999247 : Blo 1705053 70999247 := bstep (se 1 (by rfl) ⟨53249435, by rfl⟩ : syracuseStep 70999247 = 106498871) B106498871
theorem B4857043 : Blo 1705053 4857043 := bstep (se 1 (by rfl) ⟨3642782, by rfl⟩ : syracuseStep 4857043 = 7285565) B7285565
theorem B24591721 : Blo 1705053 24591721 := bstep (se 2 (by rfl) ⟨9221895, by rfl⟩ : syracuseStep 24591721 = 18443791) B18443791
theorem B121478555 : Blo 1705053 121478555 := bstep (se 1 (by rfl) ⟨91108916, by rfl⟩ : syracuseStep 121478555 = 182217833) B182217833
theorem B27672043 : Blo 1705053 27672043 := bstep (se 1 (by rfl) ⟨20754032, by rfl⟩ : syracuseStep 27672043 = 41508065) B41508065
theorem B15572675 : Blo 1705053 15572675 := bstep (se 1 (by rfl) ⟨11679506, by rfl⟩ : syracuseStep 15572675 = 23359013) B23359013
theorem B224378819 : Blo 1705053 224378819 := bstep (se 1 (by rfl) ⟨168284114, by rfl⟩ : syracuseStep 224378819 = 336568229) B336568229
theorem B3891199 : Blo 1705053 3891199 := bstep (se 1 (by rfl) ⟨2918399, by rfl⟩ : syracuseStep 3891199 = 5836799) B5836799
theorem B7290911 : Blo 1705053 7290911 := bstep (se 1 (by rfl) ⟨5468183, by rfl⟩ : syracuseStep 7290911 = 10936367) B10936367
theorem B15558079 : Blo 1705053 15558079 := bstep (se 1 (by rfl) ⟨11668559, by rfl⟩ : syracuseStep 15558079 = 23337119) B23337119
theorem B70067699 : Blo 1705053 70067699 := bstep (se 1 (by rfl) ⟨52550774, by rfl⟩ : syracuseStep 70067699 = 105101549) B105101549
theorem B41527133 : Blo 1705053 41527133 := bstep (se 3 (by rfl) ⟨7786337, by rfl⟩ : syracuseStep 41527133 = 15572675) B15572675
theorem B2877295 : Blo 1705053 2877295 := bstep (se 1 (by rfl) ⟨2157971, by rfl⟩ : syracuseStep 2877295 = 4315943) B4315943
theorem B1705983 : Blo 1705053 1705983 := bstep (se 1 (by rfl) ⟨1279487, by rfl⟩ : syracuseStep 1705983 = 2558975) B2558975
theorem B2558135 : Blo 1705053 2558135 := bstep (se 1 (by rfl) ⟨1918601, by rfl⟩ : syracuseStep 2558135 = 3837203) B3837203
theorem B5188265 : Blo 1705053 5188265 := bstep (se 2 (by rfl) ⟨1945599, by rfl⟩ : syracuseStep 5188265 = 3891199) B3891199
theorem B3836735 : Blo 1705053 3836735 := bstep (se 1 (by rfl) ⟨2877551, by rfl⟩ : syracuseStep 3836735 = 5755103) B5755103
theorem B32787503 : Blo 1705053 32787503 := bstep (se 1 (by rfl) ⟨24590627, by rfl⟩ : syracuseStep 32787503 = 49181255) B49181255
theorem B2559695 : Blo 1705053 2559695 := bstep (se 1 (by rfl) ⟨1919771, by rfl⟩ : syracuseStep 2559695 = 3839543) B3839543
theorem B2559707 : Blo 1705053 2559707 := bstep (se 1 (by rfl) ⟨1919780, by rfl⟩ : syracuseStep 2559707 = 3839561) B3839561
theorem B5755049 : Blo 1705053 5755049 := bstep (se 2 (by rfl) ⟨2158143, by rfl⟩ : syracuseStep 5755049 = 4316287) B4316287
theorem B3838175 : Blo 1705053 3838175 := bstep (se 1 (by rfl) ⟨2878631, by rfl⟩ : syracuseStep 3838175 = 5757263) B5757263
theorem B6476057 : Blo 1705053 6476057 := bstep (se 2 (by rfl) ⟨2428521, by rfl⟩ : syracuseStep 6476057 = 4857043) B4857043
theorem B9220513 : Blo 1705053 9220513 := bstep (se 2 (by rfl) ⟨3457692, by rfl⟩ : syracuseStep 9220513 = 6915385) B6915385
theorem B32788961 : Blo 1705053 32788961 := bstep (se 2 (by rfl) ⟨12295860, by rfl⟩ : syracuseStep 32788961 = 24591721) B24591721
theorem B3838715 : Blo 1705053 3838715 := bstep (se 1 (by rfl) ⟨2879036, by rfl⟩ : syracuseStep 3838715 = 5758073) B5758073
theorem B3839615 : Blo 1705053 3839615 := bstep (se 1 (by rfl) ⟨2879711, by rfl⟩ : syracuseStep 3839615 = 5759423) B5759423
theorem B9714107 : Blo 1705053 9714107 := bstep (se 1 (by rfl) ⟨7285580, by rfl⟩ : syracuseStep 9714107 = 14571161) B14571161
theorem B4856507 : Blo 1705053 4856507 := bstep (se 1 (by rfl) ⟨3642380, by rfl⟩ : syracuseStep 4856507 = 7284761) B7284761
theorem B5463263 : Blo 1705053 5463263 := bstep (se 1 (by rfl) ⟨4097447, by rfl⟩ : syracuseStep 5463263 = 8194895) B8194895
theorem B7290091 : Blo 1705053 7290091 := bstep (se 1 (by rfl) ⟨5467568, by rfl⟩ : syracuseStep 7290091 = 10935137) B10935137
theorem B36896057 : Blo 1705053 36896057 := bstep (se 2 (by rfl) ⟨13836021, by rfl⟩ : syracuseStep 36896057 = 27672043) B27672043
theorem B4857191 : Blo 1705053 4857191 := bstep (se 1 (by rfl) ⟨3642893, by rfl⟩ : syracuseStep 4857191 = 7285787) B7285787
theorem B19701143 : Blo 1705053 19701143 := bstep (se 1 (by rfl) ⟨14775857, by rfl⟩ : syracuseStep 19701143 = 29551715) B29551715
theorem B47332831 : Blo 1705053 47332831 := bstep (se 1 (by rfl) ⟨35499623, by rfl⟩ : syracuseStep 47332831 = 70999247) B70999247
theorem B80985703 : Blo 1705053 80985703 := bstep (se 1 (by rfl) ⟨60739277, by rfl⟩ : syracuseStep 80985703 = 121478555) B121478555
theorem B149585879 : Blo 1705053 149585879 := bstep (se 1 (by rfl) ⟨112189409, by rfl⟩ : syracuseStep 149585879 = 224378819) B224378819
theorem B4317371 : Blo 1705053 4317371 := bstep (se 1 (by rfl) ⟨3238028, by rfl⟩ : syracuseStep 4317371 = 6476057) B6476057
theorem B46711799 : Blo 1705053 46711799 := bstep (se 1 (by rfl) ⟨35033849, by rfl⟩ : syracuseStep 46711799 = 70067699) B70067699
theorem B1705423 : Blo 1705053 1705423 := bstep (se 1 (by rfl) ⟨1279067, by rfl⟩ : syracuseStep 1705423 = 2558135) B2558135
theorem B3458843 : Blo 1705053 3458843 := bstep (se 1 (by rfl) ⟨2594132, by rfl⟩ : syracuseStep 3458843 = 5188265) B5188265
theorem B3237671 : Blo 1705053 3237671 := bstep (se 1 (by rfl) ⟨2428253, by rfl⟩ : syracuseStep 3237671 = 4856507) B4856507
theorem B2557823 : Blo 1705053 2557823 := bstep (se 1 (by rfl) ⟨1918367, by rfl⟩ : syracuseStep 2557823 = 3836735) B3836735
theorem B20744105 : Blo 1705053 20744105 := bstep (se 2 (by rfl) ⟨7779039, by rfl⟩ : syracuseStep 20744105 = 15558079) B15558079
theorem B21858335 : Blo 1705053 21858335 := bstep (se 1 (by rfl) ⟨16393751, by rfl⟩ : syracuseStep 21858335 = 32787503) B32787503
theorem B107980937 : Blo 1705053 107980937 := bstep (se 2 (by rfl) ⟨40492851, by rfl⟩ : syracuseStep 107980937 = 80985703) B80985703
theorem B3238127 : Blo 1705053 3238127 := bstep (se 1 (by rfl) ⟨2428595, by rfl⟩ : syracuseStep 3238127 = 4857191) B4857191
theorem B13134095 : Blo 1705053 13134095 := bstep (se 1 (by rfl) ⟨9850571, by rfl⟩ : syracuseStep 13134095 = 19701143) B19701143
theorem B1706463 : Blo 1705053 1706463 := bstep (se 1 (by rfl) ⟨1279847, by rfl⟩ : syracuseStep 1706463 = 2559695) B2559695
theorem B1706471 : Blo 1705053 1706471 := bstep (se 1 (by rfl) ⟨1279853, by rfl⟩ : syracuseStep 1706471 = 2559707) B2559707
theorem B3836393 : Blo 1705053 3836393 := bstep (se 2 (by rfl) ⟨1438647, by rfl⟩ : syracuseStep 3836393 = 2877295) B2877295
theorem B398895677 : Blo 1705053 398895677 := bstep (se 3 (by rfl) ⟨74792939, by rfl⟩ : syracuseStep 398895677 = 149585879) B149585879
theorem B19442429 : Blo 1705053 19442429 := bstep (se 3 (by rfl) ⟨3645455, by rfl⟩ : syracuseStep 19442429 = 7290911) B7290911
theorem B3836699 : Blo 1705053 3836699 := bstep (se 1 (by rfl) ⟨2877524, by rfl⟩ : syracuseStep 3836699 = 5755049) B5755049
theorem B2558783 : Blo 1705053 2558783 := bstep (se 1 (by rfl) ⟨1919087, by rfl⟩ : syracuseStep 2558783 = 3838175) B3838175
theorem B21859307 : Blo 1705053 21859307 := bstep (se 1 (by rfl) ⟨16394480, by rfl⟩ : syracuseStep 21859307 = 32788961) B32788961
theorem B2559143 : Blo 1705053 2559143 := bstep (se 1 (by rfl) ⟨1919357, by rfl⟩ : syracuseStep 2559143 = 3838715) B3838715
theorem B2559743 : Blo 1705053 2559743 := bstep (se 1 (by rfl) ⟨1919807, by rfl⟩ : syracuseStep 2559743 = 3839615) B3839615
theorem B27684755 : Blo 1705053 27684755 := bstep (se 1 (by rfl) ⟨20763566, by rfl⟩ : syracuseStep 27684755 = 41527133) B41527133
theorem B6476071 : Blo 1705053 6476071 := bstep (se 1 (by rfl) ⟨4857053, by rfl⟩ : syracuseStep 6476071 = 9714107) B9714107
theorem B9720121 : Blo 1705053 9720121 := bstep (se 2 (by rfl) ⟨3645045, by rfl⟩ : syracuseStep 9720121 = 7290091) B7290091
theorem B3642175 : Blo 1705053 3642175 := bstep (se 1 (by rfl) ⟨2731631, by rfl⟩ : syracuseStep 3642175 = 5463263) B5463263
theorem B24597371 : Blo 1705053 24597371 := bstep (se 1 (by rfl) ⟨18448028, by rfl⟩ : syracuseStep 24597371 = 36896057) B36896057
theorem B12294017 : Blo 1705053 12294017 := bstep (se 2 (by rfl) ⟨4610256, by rfl⟩ : syracuseStep 12294017 = 9220513) B9220513
theorem B63110441 : Blo 1705053 63110441 := bstep (se 2 (by rfl) ⟨23666415, by rfl⟩ : syracuseStep 63110441 = 47332831) B47332831
theorem B8634761 : Blo 1705053 8634761 := bstep (se 2 (by rfl) ⟨3238035, by rfl⟩ : syracuseStep 8634761 = 6476071) B6476071
theorem B12960161 : Blo 1705053 12960161 := bstep (se 2 (by rfl) ⟨4860060, by rfl⟩ : syracuseStep 12960161 = 9720121) B9720121
theorem B1705215 : Blo 1705053 1705215 := bstep (se 1 (by rfl) ⟨1278911, by rfl⟩ : syracuseStep 1705215 = 2557823) B2557823
theorem B2557595 : Blo 1705053 2557595 := bstep (se 1 (by rfl) ⟨1918196, by rfl⟩ : syracuseStep 2557595 = 3836393) B3836393
theorem B19424933 : Blo 1705053 19424933 := bstep (se 4 (by rfl) ⟨1821087, by rfl⟩ : syracuseStep 19424933 = 3642175) B3642175
theorem B265930451 : Blo 1705053 265930451 := bstep (se 1 (by rfl) ⟨199447838, by rfl⟩ : syracuseStep 265930451 = 398895677) B398895677
theorem B12961619 : Blo 1705053 12961619 := bstep (se 1 (by rfl) ⟨9721214, by rfl⟩ : syracuseStep 12961619 = 19442429) B19442429
theorem B2557799 : Blo 1705053 2557799 := bstep (se 1 (by rfl) ⟨1918349, by rfl⟩ : syracuseStep 2557799 = 3836699) B3836699
theorem B1705855 : Blo 1705053 1705855 := bstep (se 1 (by rfl) ⟨1279391, by rfl⟩ : syracuseStep 1705855 = 2558783) B2558783
theorem B1706095 : Blo 1705053 1706095 := bstep (se 1 (by rfl) ⟨1279571, by rfl⟩ : syracuseStep 1706095 = 2559143) B2559143
theorem B1706495 : Blo 1705053 1706495 := bstep (se 1 (by rfl) ⟨1279871, by rfl⟩ : syracuseStep 1706495 = 2559743) B2559743
theorem B2878247 : Blo 1705053 2878247 := bstep (se 1 (by rfl) ⟨2158685, by rfl⟩ : syracuseStep 2878247 = 4317371) B4317371
theorem B31141199 : Blo 1705053 31141199 := bstep (se 1 (by rfl) ⟨23355899, by rfl⟩ : syracuseStep 31141199 = 46711799) B46711799
theorem B8196011 : Blo 1705053 8196011 := bstep (se 1 (by rfl) ⟨6147008, by rfl⟩ : syracuseStep 8196011 = 12294017) B12294017
theorem B71987291 : Blo 1705053 71987291 := bstep (se 1 (by rfl) ⟨53990468, by rfl⟩ : syracuseStep 71987291 = 107980937) B107980937
theorem B2158751 : Blo 1705053 2158751 := bstep (se 1 (by rfl) ⟨1619063, by rfl⟩ : syracuseStep 2158751 = 3238127) B3238127
theorem B55317613 : Blo 1705053 55317613 := bstep (se 3 (by rfl) ⟨10372052, by rfl⟩ : syracuseStep 55317613 = 20744105) B20744105
theorem B36894325 : Blo 1705053 36894325 := bstep (se 5 (by rfl) ⟨1729421, by rfl⟩ : syracuseStep 36894325 = 3458843) B3458843
theorem B16398247 : Blo 1705053 16398247 := bstep (se 1 (by rfl) ⟨12298685, by rfl⟩ : syracuseStep 16398247 = 24597371) B24597371
theorem B14572223 : Blo 1705053 14572223 := bstep (se 1 (by rfl) ⟨10929167, by rfl⟩ : syracuseStep 14572223 = 21858335) B21858335
theorem B8756063 : Blo 1705053 8756063 := bstep (se 1 (by rfl) ⟨6567047, by rfl⟩ : syracuseStep 8756063 = 13134095) B13134095
theorem B14572871 : Blo 1705053 14572871 := bstep (se 1 (by rfl) ⟨10929653, by rfl⟩ : syracuseStep 14572871 = 21859307) B21859307
theorem B8633789 : Blo 1705053 8633789 := bstep (se 3 (by rfl) ⟨1618835, by rfl⟩ : syracuseStep 8633789 = 3237671) B3237671
theorem B42073627 : Blo 1705053 42073627 := bstep (se 1 (by rfl) ⟨31555220, by rfl⟩ : syracuseStep 42073627 = 63110441) B63110441
theorem B18456503 : Blo 1705053 18456503 := bstep (se 1 (by rfl) ⟨13842377, by rfl⟩ : syracuseStep 18456503 = 27684755) B27684755
theorem B1705063 : Blo 1705053 1705063 := bstep (se 1 (by rfl) ⟨1278797, by rfl⟩ : syracuseStep 1705063 = 2557595) B2557595
theorem B1705199 : Blo 1705053 1705199 := bstep (se 1 (by rfl) ⟨1278899, by rfl⟩ : syracuseStep 1705199 = 2557799) B2557799
theorem B1918831 : Blo 1705053 1918831 := bstep (se 1 (by rfl) ⟨1439123, by rfl⟩ : syracuseStep 1918831 = 2878247) B2878247
theorem B20760799 : Blo 1705053 20760799 := bstep (se 1 (by rfl) ⟨15570599, by rfl⟩ : syracuseStep 20760799 = 31141199) B31141199
theorem B47991527 : Blo 1705053 47991527 := bstep (se 1 (by rfl) ⟨35993645, by rfl⟩ : syracuseStep 47991527 = 71987291) B71987291
theorem B177286967 : Blo 1705053 177286967 := bstep (se 1 (by rfl) ⟨132965225, by rfl⟩ : syracuseStep 177286967 = 265930451) B265930451
theorem B73756817 : Blo 1705053 73756817 := bstep (se 2 (by rfl) ⟨27658806, by rfl⟩ : syracuseStep 73756817 = 55317613) B55317613
theorem B5837375 : Blo 1705053 5837375 := bstep (se 1 (by rfl) ⟨4378031, by rfl⟩ : syracuseStep 5837375 = 8756063) B8756063
theorem B5755859 : Blo 1705053 5755859 := bstep (se 1 (by rfl) ⟨4316894, by rfl⟩ : syracuseStep 5755859 = 8633789) B8633789
theorem B5756507 : Blo 1705053 5756507 := bstep (se 1 (by rfl) ⟨4317380, by rfl⟩ : syracuseStep 5756507 = 8634761) B8634761
theorem B8640107 : Blo 1705053 8640107 := bstep (se 1 (by rfl) ⟨6480080, by rfl⟩ : syracuseStep 8640107 = 12960161) B12960161
theorem B5756669 : Blo 1705053 5756669 := bstep (se 3 (by rfl) ⟨1079375, by rfl⟩ : syracuseStep 5756669 = 2158751) B2158751
theorem B12949955 : Blo 1705053 12949955 := bstep (se 1 (by rfl) ⟨9712466, by rfl⟩ : syracuseStep 12949955 = 19424933) B19424933
theorem B8641079 : Blo 1705053 8641079 := bstep (se 1 (by rfl) ⟨6480809, by rfl⟩ : syracuseStep 8641079 = 12961619) B12961619
theorem B9714815 : Blo 1705053 9714815 := bstep (se 1 (by rfl) ⟨7286111, by rfl⟩ : syracuseStep 9714815 = 14572223) B14572223
theorem B56098169 : Blo 1705053 56098169 := bstep (se 2 (by rfl) ⟨21036813, by rfl⟩ : syracuseStep 56098169 = 42073627) B42073627
theorem B49192433 : Blo 1705053 49192433 := bstep (se 2 (by rfl) ⟨18447162, by rfl⟩ : syracuseStep 49192433 = 36894325) B36894325
theorem B9715247 : Blo 1705053 9715247 := bstep (se 1 (by rfl) ⟨7286435, by rfl⟩ : syracuseStep 9715247 = 14572871) B14572871
theorem B49217341 : Blo 1705053 49217341 := bstep (se 3 (by rfl) ⟨9228251, by rfl⟩ : syracuseStep 49217341 = 18456503) B18456503
theorem B21864329 : Blo 1705053 21864329 := bstep (se 2 (by rfl) ⟨8199123, by rfl⟩ : syracuseStep 21864329 = 16398247) B16398247
theorem B5464007 : Blo 1705053 5464007 := bstep (se 1 (by rfl) ⟨4098005, by rfl⟩ : syracuseStep 5464007 = 8196011) B8196011
theorem B27681065 : Blo 1705053 27681065 := bstep (se 2 (by rfl) ⟨10380399, by rfl⟩ : syracuseStep 27681065 = 20760799) B20760799
theorem B5760719 : Blo 1705053 5760719 := bstep (se 1 (by rfl) ⟨4320539, by rfl⟩ : syracuseStep 5760719 = 8641079) B8641079
theorem B3891583 : Blo 1705053 3891583 := bstep (se 1 (by rfl) ⟨2918687, by rfl⟩ : syracuseStep 3891583 = 5837375) B5837375
theorem B5760071 : Blo 1705053 5760071 := bstep (se 1 (by rfl) ⟨4320053, by rfl⟩ : syracuseStep 5760071 = 8640107) B8640107
theorem B37398779 : Blo 1705053 37398779 := bstep (se 1 (by rfl) ⟨28049084, by rfl⟩ : syracuseStep 37398779 = 56098169) B56098169
theorem B32794955 : Blo 1705053 32794955 := bstep (se 1 (by rfl) ⟨24596216, by rfl⟩ : syracuseStep 32794955 = 49192433) B49192433
theorem B2558441 : Blo 1705053 2558441 := bstep (se 2 (by rfl) ⟨959415, by rfl⟩ : syracuseStep 2558441 = 1918831) B1918831
theorem B14576219 : Blo 1705053 14576219 := bstep (se 1 (by rfl) ⟨10932164, by rfl⟩ : syracuseStep 14576219 = 21864329) B21864329
theorem B49171211 : Blo 1705053 49171211 := bstep (se 1 (by rfl) ⟨36878408, by rfl⟩ : syracuseStep 49171211 = 73756817) B73756817
theorem B3837239 : Blo 1705053 3837239 := bstep (se 1 (by rfl) ⟨2877929, by rfl⟩ : syracuseStep 3837239 = 5755859) B5755859
theorem B3837671 : Blo 1705053 3837671 := bstep (se 1 (by rfl) ⟨2878253, by rfl⟩ : syracuseStep 3837671 = 5756507) B5756507
theorem B3837779 : Blo 1705053 3837779 := bstep (se 1 (by rfl) ⟨2878334, by rfl⟩ : syracuseStep 3837779 = 5756669) B5756669
theorem B31994351 : Blo 1705053 31994351 := bstep (se 1 (by rfl) ⟨23995763, by rfl⟩ : syracuseStep 31994351 = 47991527) B47991527
theorem B6476543 : Blo 1705053 6476543 := bstep (se 1 (by rfl) ⟨4857407, by rfl⟩ : syracuseStep 6476543 = 9714815) B9714815
theorem B6476831 : Blo 1705053 6476831 := bstep (se 1 (by rfl) ⟨4857623, by rfl⟩ : syracuseStep 6476831 = 9715247) B9715247
theorem B65623121 : Blo 1705053 65623121 := bstep (se 2 (by rfl) ⟨24608670, by rfl⟩ : syracuseStep 65623121 = 49217341) B49217341
theorem B118191311 : Blo 1705053 118191311 := bstep (se 1 (by rfl) ⟨88643483, by rfl⟩ : syracuseStep 118191311 = 177286967) B177286967
theorem B3642671 : Blo 1705053 3642671 := bstep (se 1 (by rfl) ⟨2732003, by rfl⟩ : syracuseStep 3642671 = 5464007) B5464007
theorem B8633303 : Blo 1705053 8633303 := bstep (se 1 (by rfl) ⟨6474977, by rfl⟩ : syracuseStep 8633303 = 12949955) B12949955
theorem B4317695 : Blo 1705053 4317695 := bstep (se 1 (by rfl) ⟨3238271, by rfl⟩ : syracuseStep 4317695 = 6476543) B6476543
theorem B4317887 : Blo 1705053 4317887 := bstep (se 1 (by rfl) ⟨3238415, by rfl⟩ : syracuseStep 4317887 = 6476831) B6476831
theorem B1705627 : Blo 1705053 1705627 := bstep (se 1 (by rfl) ⟨1279220, by rfl⟩ : syracuseStep 1705627 = 2558441) B2558441
theorem B9717479 : Blo 1705053 9717479 := bstep (se 1 (by rfl) ⟨7288109, by rfl⟩ : syracuseStep 9717479 = 14576219) B14576219
theorem B2558159 : Blo 1705053 2558159 := bstep (se 1 (by rfl) ⟨1918619, by rfl⟩ : syracuseStep 2558159 = 3837239) B3837239
theorem B2558447 : Blo 1705053 2558447 := bstep (se 1 (by rfl) ⟨1918835, by rfl⟩ : syracuseStep 2558447 = 3837671) B3837671
theorem B2558519 : Blo 1705053 2558519 := bstep (se 1 (by rfl) ⟨1918889, by rfl⟩ : syracuseStep 2558519 = 3837779) B3837779
theorem B43748747 : Blo 1705053 43748747 := bstep (se 1 (by rfl) ⟨32811560, by rfl⟩ : syracuseStep 43748747 = 65623121) B65623121
theorem B78794207 : Blo 1705053 78794207 := bstep (se 1 (by rfl) ⟨59095655, by rfl⟩ : syracuseStep 78794207 = 118191311) B118191311
theorem B24932519 : Blo 1705053 24932519 := bstep (se 1 (by rfl) ⟨18699389, by rfl⟩ : syracuseStep 24932519 = 37398779) B37398779
theorem B32780807 : Blo 1705053 32780807 := bstep (se 1 (by rfl) ⟨24585605, by rfl⟩ : syracuseStep 32780807 = 49171211) B49171211
theorem B5755535 : Blo 1705053 5755535 := bstep (se 1 (by rfl) ⟨4316651, by rfl⟩ : syracuseStep 5755535 = 8633303) B8633303
theorem B20755109 : Blo 1705053 20755109 := bstep (se 4 (by rfl) ⟨1945791, by rfl⟩ : syracuseStep 20755109 = 3891583) B3891583
theorem B18454043 : Blo 1705053 18454043 := bstep (se 1 (by rfl) ⟨13840532, by rfl⟩ : syracuseStep 18454043 = 27681065) B27681065
theorem B21329567 : Blo 1705053 21329567 := bstep (se 1 (by rfl) ⟨15997175, by rfl⟩ : syracuseStep 21329567 = 31994351) B31994351
theorem B3840047 : Blo 1705053 3840047 := bstep (se 1 (by rfl) ⟨2880035, by rfl⟩ : syracuseStep 3840047 = 5760071) B5760071
theorem B9713789 : Blo 1705053 9713789 := bstep (se 3 (by rfl) ⟨1821335, by rfl⟩ : syracuseStep 9713789 = 3642671) B3642671
theorem B3840479 : Blo 1705053 3840479 := bstep (se 1 (by rfl) ⟨2880359, by rfl⟩ : syracuseStep 3840479 = 5760719) B5760719
theorem B21863303 : Blo 1705053 21863303 := bstep (se 1 (by rfl) ⟨16397477, by rfl⟩ : syracuseStep 21863303 = 32794955) B32794955
theorem B16621679 : Blo 1705053 16621679 := bstep (se 1 (by rfl) ⟨12466259, by rfl⟩ : syracuseStep 16621679 = 24932519) B24932519
theorem B13836739 : Blo 1705053 13836739 := bstep (se 1 (by rfl) ⟨10377554, by rfl⟩ : syracuseStep 13836739 = 20755109) B20755109
theorem B1705439 : Blo 1705053 1705439 := bstep (se 1 (by rfl) ⟨1279079, by rfl⟩ : syracuseStep 1705439 = 2558159) B2558159
theorem B1705631 : Blo 1705053 1705631 := bstep (se 1 (by rfl) ⟨1279223, by rfl⟩ : syracuseStep 1705631 = 2558447) B2558447
theorem B1705679 : Blo 1705053 1705679 := bstep (se 1 (by rfl) ⟨1279259, by rfl⟩ : syracuseStep 1705679 = 2558519) B2558519
theorem B14575535 : Blo 1705053 14575535 := bstep (se 1 (by rfl) ⟨10931651, by rfl⟩ : syracuseStep 14575535 = 21863303) B21863303
theorem B29165831 : Blo 1705053 29165831 := bstep (se 1 (by rfl) ⟨21874373, by rfl⟩ : syracuseStep 29165831 = 43748747) B43748747
theorem B52529471 : Blo 1705053 52529471 := bstep (se 1 (by rfl) ⟨39397103, by rfl⟩ : syracuseStep 52529471 = 78794207) B78794207
theorem B2878463 : Blo 1705053 2878463 := bstep (se 1 (by rfl) ⟨2158847, by rfl⟩ : syracuseStep 2878463 = 4317695) B4317695
theorem B3837023 : Blo 1705053 3837023 := bstep (se 1 (by rfl) ⟨2877767, by rfl⟩ : syracuseStep 3837023 = 5755535) B5755535
theorem B2878591 : Blo 1705053 2878591 := bstep (se 1 (by rfl) ⟨2158943, by rfl⟩ : syracuseStep 2878591 = 4317887) B4317887
theorem B2560031 : Blo 1705053 2560031 := bstep (se 1 (by rfl) ⟨1920023, by rfl⟩ : syracuseStep 2560031 = 3840047) B3840047
theorem B6475859 : Blo 1705053 6475859 := bstep (se 1 (by rfl) ⟨4856894, by rfl⟩ : syracuseStep 6475859 = 9713789) B9713789
theorem B2560319 : Blo 1705053 2560319 := bstep (se 1 (by rfl) ⟨1920239, by rfl⟩ : syracuseStep 2560319 = 3840479) B3840479
theorem B21853871 : Blo 1705053 21853871 := bstep (se 1 (by rfl) ⟨16390403, by rfl⟩ : syracuseStep 21853871 = 32780807) B32780807
theorem B12302695 : Blo 1705053 12302695 := bstep (se 1 (by rfl) ⟨9227021, by rfl⟩ : syracuseStep 12302695 = 18454043) B18454043
theorem B14219711 : Blo 1705053 14219711 := bstep (se 1 (by rfl) ⟨10664783, by rfl⟩ : syracuseStep 14219711 = 21329567) B21329567
theorem B6478319 : Blo 1705053 6478319 := bstep (se 1 (by rfl) ⟨4858739, by rfl⟩ : syracuseStep 6478319 = 9717479) B9717479
theorem B4317239 : Blo 1705053 4317239 := bstep (se 1 (by rfl) ⟨3237929, by rfl⟩ : syracuseStep 4317239 = 6475859) B6475859
theorem B18448985 : Blo 1705053 18448985 := bstep (se 2 (by rfl) ⟨6918369, by rfl⟩ : syracuseStep 18448985 = 13836739) B13836739
theorem B9717023 : Blo 1705053 9717023 := bstep (se 1 (by rfl) ⟨7287767, by rfl⟩ : syracuseStep 9717023 = 14575535) B14575535
theorem B9479807 : Blo 1705053 9479807 := bstep (se 1 (by rfl) ⟨7109855, by rfl⟩ : syracuseStep 9479807 = 14219711) B14219711
theorem B4318879 : Blo 1705053 4318879 := bstep (se 1 (by rfl) ⟨3239159, by rfl⟩ : syracuseStep 4318879 = 6478319) B6478319
theorem B1918975 : Blo 1705053 1918975 := bstep (se 1 (by rfl) ⟨1439231, by rfl⟩ : syracuseStep 1918975 = 2878463) B2878463
theorem B2558015 : Blo 1705053 2558015 := bstep (se 1 (by rfl) ⟨1918511, by rfl⟩ : syracuseStep 2558015 = 3837023) B3837023
theorem B1706687 : Blo 1705053 1706687 := bstep (se 1 (by rfl) ⟨1280015, by rfl⟩ : syracuseStep 1706687 = 2560031) B2560031
theorem B1706879 : Blo 1705053 1706879 := bstep (se 1 (by rfl) ⟨1280159, by rfl⟩ : syracuseStep 1706879 = 2560319) B2560319
theorem B16403593 : Blo 1705053 16403593 := bstep (se 2 (by rfl) ⟨6151347, by rfl⟩ : syracuseStep 16403593 = 12302695) B12302695
theorem B14569247 : Blo 1705053 14569247 := bstep (se 1 (by rfl) ⟨10926935, by rfl⟩ : syracuseStep 14569247 = 21853871) B21853871
theorem B3838121 : Blo 1705053 3838121 := bstep (se 2 (by rfl) ⟨1439295, by rfl⟩ : syracuseStep 3838121 = 2878591) B2878591
theorem B19443887 : Blo 1705053 19443887 := bstep (se 1 (by rfl) ⟨14582915, by rfl⟩ : syracuseStep 19443887 = 29165831) B29165831
theorem B11081119 : Blo 1705053 11081119 := bstep (se 1 (by rfl) ⟨8310839, by rfl⟩ : syracuseStep 11081119 = 16621679) B16621679
theorem B35019647 : Blo 1705053 35019647 := bstep (se 1 (by rfl) ⟨26264735, by rfl⟩ : syracuseStep 35019647 = 52529471) B52529471
theorem B1705343 : Blo 1705053 1705343 := bstep (se 1 (by rfl) ⟨1279007, by rfl⟩ : syracuseStep 1705343 = 2558015) B2558015
theorem B2558633 : Blo 1705053 2558633 := bstep (se 2 (by rfl) ⟨959487, by rfl⟩ : syracuseStep 2558633 = 1918975) B1918975
theorem B2878159 : Blo 1705053 2878159 := bstep (se 1 (by rfl) ⟨2158619, by rfl⟩ : syracuseStep 2878159 = 4317239) B4317239
theorem B2558747 : Blo 1705053 2558747 := bstep (se 1 (by rfl) ⟨1919060, by rfl⟩ : syracuseStep 2558747 = 3838121) B3838121
theorem B12962591 : Blo 1705053 12962591 := bstep (se 1 (by rfl) ⟨9721943, by rfl⟩ : syracuseStep 12962591 = 19443887) B19443887
theorem B12299323 : Blo 1705053 12299323 := bstep (se 1 (by rfl) ⟨9224492, by rfl⟩ : syracuseStep 12299323 = 18448985) B18448985
theorem B6319871 : Blo 1705053 6319871 := bstep (se 1 (by rfl) ⟨4739903, by rfl⟩ : syracuseStep 6319871 = 9479807) B9479807
theorem B14774825 : Blo 1705053 14774825 := bstep (se 2 (by rfl) ⟨5540559, by rfl⟩ : syracuseStep 14774825 = 11081119) B11081119
theorem B9712831 : Blo 1705053 9712831 := bstep (se 1 (by rfl) ⟨7284623, by rfl⟩ : syracuseStep 9712831 = 14569247) B14569247
theorem B6478015 : Blo 1705053 6478015 := bstep (se 1 (by rfl) ⟨4858511, by rfl⟩ : syracuseStep 6478015 = 9717023) B9717023
theorem B21871457 : Blo 1705053 21871457 := bstep (se 2 (by rfl) ⟨8201796, by rfl⟩ : syracuseStep 21871457 = 16403593) B16403593
theorem B23346431 : Blo 1705053 23346431 := bstep (se 1 (by rfl) ⟨17509823, by rfl⟩ : syracuseStep 23346431 = 35019647) B35019647
theorem B5758505 : Blo 1705053 5758505 := bstep (se 2 (by rfl) ⟨2159439, by rfl⟩ : syracuseStep 5758505 = 4318879) B4318879
theorem B1705755 : Blo 1705053 1705755 := bstep (se 1 (by rfl) ⟨1279316, by rfl⟩ : syracuseStep 1705755 = 2558633) B2558633
theorem B1705831 : Blo 1705053 1705831 := bstep (se 1 (by rfl) ⟨1279373, by rfl⟩ : syracuseStep 1705831 = 2558747) B2558747
theorem B4213247 : Blo 1705053 4213247 := bstep (se 1 (by rfl) ⟨3159935, by rfl⟩ : syracuseStep 4213247 = 6319871) B6319871
theorem B8637353 : Blo 1705053 8637353 := bstep (se 2 (by rfl) ⟨3239007, by rfl⟩ : syracuseStep 8637353 = 6478015) B6478015
theorem B9849883 : Blo 1705053 9849883 := bstep (se 1 (by rfl) ⟨7387412, by rfl⟩ : syracuseStep 9849883 = 14774825) B14774825
theorem B3837545 : Blo 1705053 3837545 := bstep (se 2 (by rfl) ⟨1439079, by rfl⟩ : syracuseStep 3837545 = 2878159) B2878159
theorem B3839003 : Blo 1705053 3839003 := bstep (se 1 (by rfl) ⟨2879252, by rfl⟩ : syracuseStep 3839003 = 5758505) B5758505
theorem B16399097 : Blo 1705053 16399097 := bstep (se 2 (by rfl) ⟨6149661, by rfl⟩ : syracuseStep 16399097 = 12299323) B12299323
theorem B12950441 : Blo 1705053 12950441 := bstep (se 2 (by rfl) ⟨4856415, by rfl⟩ : syracuseStep 12950441 = 9712831) B9712831
theorem B8641727 : Blo 1705053 8641727 := bstep (se 1 (by rfl) ⟨6481295, by rfl⟩ : syracuseStep 8641727 = 12962591) B12962591
theorem B14580971 : Blo 1705053 14580971 := bstep (se 1 (by rfl) ⟨10935728, by rfl⟩ : syracuseStep 14580971 = 21871457) B21871457
theorem B15564287 : Blo 1705053 15564287 := bstep (se 1 (by rfl) ⟨11673215, by rfl⟩ : syracuseStep 15564287 = 23346431) B23346431
theorem B13133177 : Blo 1705053 13133177 := bstep (se 2 (by rfl) ⟨4924941, by rfl⟩ : syracuseStep 13133177 = 9849883) B9849883
theorem B5761151 : Blo 1705053 5761151 := bstep (se 1 (by rfl) ⟨4320863, by rfl⟩ : syracuseStep 5761151 = 8641727) B8641727
theorem B2558363 : Blo 1705053 2558363 := bstep (se 1 (by rfl) ⟨1918772, by rfl⟩ : syracuseStep 2558363 = 3837545) B3837545
theorem B2559335 : Blo 1705053 2559335 := bstep (se 1 (by rfl) ⟨1919501, by rfl⟩ : syracuseStep 2559335 = 3839003) B3839003
theorem B10932731 : Blo 1705053 10932731 := bstep (se 1 (by rfl) ⟨8199548, by rfl⟩ : syracuseStep 10932731 = 16399097) B16399097
theorem B9720647 : Blo 1705053 9720647 := bstep (se 1 (by rfl) ⟨7290485, by rfl⟩ : syracuseStep 9720647 = 14580971) B14580971
theorem B10376191 : Blo 1705053 10376191 := bstep (se 1 (by rfl) ⟨7782143, by rfl⟩ : syracuseStep 10376191 = 15564287) B15564287
theorem B8633627 : Blo 1705053 8633627 := bstep (se 1 (by rfl) ⟨6475220, by rfl⟩ : syracuseStep 8633627 = 12950441) B12950441
theorem B5758235 : Blo 1705053 5758235 := bstep (se 1 (by rfl) ⟨4318676, by rfl⟩ : syracuseStep 5758235 = 8637353) B8637353
theorem B44941301 : Blo 1705053 44941301 := bstep (se 5 (by rfl) ⟨2106623, by rfl⟩ : syracuseStep 44941301 = 4213247) B4213247
theorem B6480431 : Blo 1705053 6480431 := bstep (se 1 (by rfl) ⟨4860323, by rfl⟩ : syracuseStep 6480431 = 9720647) B9720647
theorem B1705575 : Blo 1705053 1705575 := bstep (se 1 (by rfl) ⟨1279181, by rfl⟩ : syracuseStep 1705575 = 2558363) B2558363
theorem B1706223 : Blo 1705053 1706223 := bstep (se 1 (by rfl) ⟨1279667, by rfl⟩ : syracuseStep 1706223 = 2559335) B2559335
theorem B29960867 : Blo 1705053 29960867 := bstep (se 1 (by rfl) ⟨22470650, by rfl⟩ : syracuseStep 29960867 = 44941301) B44941301
theorem B5755751 : Blo 1705053 5755751 := bstep (se 1 (by rfl) ⟨4316813, by rfl⟩ : syracuseStep 5755751 = 8633627) B8633627
theorem B3838823 : Blo 1705053 3838823 := bstep (se 1 (by rfl) ⟨2879117, by rfl⟩ : syracuseStep 3838823 = 5758235) B5758235
theorem B7288487 : Blo 1705053 7288487 := bstep (se 1 (by rfl) ⟨5466365, by rfl⟩ : syracuseStep 7288487 = 10932731) B10932731
theorem B8755451 : Blo 1705053 8755451 := bstep (se 1 (by rfl) ⟨6566588, by rfl⟩ : syracuseStep 8755451 = 13133177) B13133177
theorem B13834921 : Blo 1705053 13834921 := bstep (se 2 (by rfl) ⟨5188095, by rfl⟩ : syracuseStep 13834921 = 10376191) B10376191
theorem B3840767 : Blo 1705053 3840767 := bstep (se 1 (by rfl) ⟨2880575, by rfl⟩ : syracuseStep 3840767 = 5761151) B5761151
theorem B4858991 : Blo 1705053 4858991 := bstep (se 1 (by rfl) ⟨3644243, by rfl⟩ : syracuseStep 4858991 = 7288487) B7288487
theorem B4320287 : Blo 1705053 4320287 := bstep (se 1 (by rfl) ⟨3240215, by rfl⟩ : syracuseStep 4320287 = 6480431) B6480431
theorem B3837167 : Blo 1705053 3837167 := bstep (se 1 (by rfl) ⟨2877875, by rfl⟩ : syracuseStep 3837167 = 5755751) B5755751
theorem B2559215 : Blo 1705053 2559215 := bstep (se 1 (by rfl) ⟨1919411, by rfl⟩ : syracuseStep 2559215 = 3838823) B3838823
theorem B5836967 : Blo 1705053 5836967 := bstep (se 1 (by rfl) ⟨4377725, by rfl⟩ : syracuseStep 5836967 = 8755451) B8755451
theorem B2560511 : Blo 1705053 2560511 := bstep (se 1 (by rfl) ⟨1920383, by rfl⟩ : syracuseStep 2560511 = 3840767) B3840767
theorem B18446561 : Blo 1705053 18446561 := bstep (se 2 (by rfl) ⟨6917460, by rfl⟩ : syracuseStep 18446561 = 13834921) B13834921
theorem B79895645 : Blo 1705053 79895645 := bstep (se 3 (by rfl) ⟨14980433, by rfl⟩ : syracuseStep 79895645 = 29960867) B29960867
theorem B3891311 : Blo 1705053 3891311 := bstep (se 1 (by rfl) ⟨2918483, by rfl⟩ : syracuseStep 3891311 = 5836967) B5836967
theorem B12297707 : Blo 1705053 12297707 := bstep (se 1 (by rfl) ⟨9223280, by rfl⟩ : syracuseStep 12297707 = 18446561) B18446561
theorem B2558111 : Blo 1705053 2558111 := bstep (se 1 (by rfl) ⟨1918583, by rfl⟩ : syracuseStep 2558111 = 3837167) B3837167
theorem B1706143 : Blo 1705053 1706143 := bstep (se 1 (by rfl) ⟨1279607, by rfl⟩ : syracuseStep 1706143 = 2559215) B2559215
theorem B1707007 : Blo 1705053 1707007 := bstep (se 1 (by rfl) ⟨1280255, by rfl⟩ : syracuseStep 1707007 = 2560511) B2560511
theorem B3239327 : Blo 1705053 3239327 := bstep (se 1 (by rfl) ⟨2429495, by rfl⟩ : syracuseStep 3239327 = 4858991) B4858991
theorem B2880191 : Blo 1705053 2880191 := bstep (se 1 (by rfl) ⟨2160143, by rfl⟩ : syracuseStep 2880191 = 4320287) B4320287
theorem B53263763 : Blo 1705053 53263763 := bstep (se 1 (by rfl) ⟨39947822, by rfl⟩ : syracuseStep 53263763 = 79895645) B79895645
theorem B1705407 : Blo 1705053 1705407 := bstep (se 1 (by rfl) ⟨1279055, by rfl⟩ : syracuseStep 1705407 = 2558111) B2558111
theorem B1920127 : Blo 1705053 1920127 := bstep (se 1 (by rfl) ⟨1440095, by rfl⟩ : syracuseStep 1920127 = 2880191) B2880191
theorem B35509175 : Blo 1705053 35509175 := bstep (se 1 (by rfl) ⟨26631881, by rfl⟩ : syracuseStep 35509175 = 53263763) B53263763
theorem B2159551 : Blo 1705053 2159551 := bstep (se 1 (by rfl) ⟨1619663, by rfl⟩ : syracuseStep 2159551 = 3239327) B3239327
theorem B2594207 : Blo 1705053 2594207 := bstep (se 1 (by rfl) ⟨1945655, by rfl⟩ : syracuseStep 2594207 = 3891311) B3891311
theorem B8198471 : Blo 1705053 8198471 := bstep (se 1 (by rfl) ⟨6148853, by rfl⟩ : syracuseStep 8198471 = 12297707) B12297707
theorem B5465647 : Blo 1705053 5465647 := bstep (se 1 (by rfl) ⟨4099235, by rfl⟩ : syracuseStep 5465647 = 8198471) B8198471
theorem B6917885 : Blo 1705053 6917885 := bstep (se 3 (by rfl) ⟨1297103, by rfl⟩ : syracuseStep 6917885 = 2594207) B2594207
theorem B2879401 : Blo 1705053 2879401 := bstep (se 2 (by rfl) ⟨1079775, by rfl⟩ : syracuseStep 2879401 = 2159551) B2159551
theorem B2560169 : Blo 1705053 2560169 := bstep (se 2 (by rfl) ⟨960063, by rfl⟩ : syracuseStep 2560169 = 1920127) B1920127
theorem B23672783 : Blo 1705053 23672783 := bstep (se 1 (by rfl) ⟨17754587, by rfl⟩ : syracuseStep 23672783 = 35509175) B35509175
theorem B1706779 : Blo 1705053 1706779 := bstep (se 1 (by rfl) ⟨1280084, by rfl⟩ : syracuseStep 1706779 = 2560169) B2560169
theorem B7287529 : Blo 1705053 7287529 := bstep (se 2 (by rfl) ⟨2732823, by rfl⟩ : syracuseStep 7287529 = 5465647) B5465647
theorem B3839201 : Blo 1705053 3839201 := bstep (se 2 (by rfl) ⟨1439700, by rfl⟩ : syracuseStep 3839201 = 2879401) B2879401
theorem B4611923 : Blo 1705053 4611923 := bstep (se 1 (by rfl) ⟨3458942, by rfl⟩ : syracuseStep 4611923 = 6917885) B6917885
theorem B63127421 : Blo 1705053 63127421 := bstep (se 3 (by rfl) ⟨11836391, by rfl⟩ : syracuseStep 63127421 = 23672783) B23672783
theorem B9716705 : Blo 1705053 9716705 := bstep (se 2 (by rfl) ⟨3643764, by rfl⟩ : syracuseStep 9716705 = 7287529) B7287529
theorem B3074615 : Blo 1705053 3074615 := bstep (se 1 (by rfl) ⟨2305961, by rfl⟩ : syracuseStep 3074615 = 4611923) B4611923
theorem B42084947 : Blo 1705053 42084947 := bstep (se 1 (by rfl) ⟨31563710, by rfl⟩ : syracuseStep 42084947 = 63127421) B63127421
theorem B2559467 : Blo 1705053 2559467 := bstep (se 1 (by rfl) ⟨1919600, by rfl⟩ : syracuseStep 2559467 = 3839201) B3839201
theorem B2049743 : Blo 1705053 2049743 := bstep (se 1 (by rfl) ⟨1537307, by rfl⟩ : syracuseStep 2049743 = 3074615) B3074615
theorem B1706311 : Blo 1705053 1706311 := bstep (se 1 (by rfl) ⟨1279733, by rfl⟩ : syracuseStep 1706311 = 2559467) B2559467
theorem B6477803 : Blo 1705053 6477803 := bstep (se 1 (by rfl) ⟨4858352, by rfl⟩ : syracuseStep 6477803 = 9716705) B9716705
theorem B28056631 : Blo 1705053 28056631 := bstep (se 1 (by rfl) ⟨21042473, by rfl⟩ : syracuseStep 28056631 = 42084947) B42084947
theorem B4318535 : Blo 1705053 4318535 := bstep (se 1 (by rfl) ⟨3238901, by rfl⟩ : syracuseStep 4318535 = 6477803) B6477803
theorem B5465981 : Blo 1705053 5465981 := bstep (se 3 (by rfl) ⟨1024871, by rfl⟩ : syracuseStep 5465981 = 2049743) B2049743
theorem B37408841 : Blo 1705053 37408841 := bstep (se 2 (by rfl) ⟨14028315, by rfl⟩ : syracuseStep 37408841 = 28056631) B28056631
theorem B24939227 : Blo 1705053 24939227 := bstep (se 1 (by rfl) ⟨18704420, by rfl⟩ : syracuseStep 24939227 = 37408841) B37408841
theorem B2879023 : Blo 1705053 2879023 := bstep (se 1 (by rfl) ⟨2159267, by rfl⟩ : syracuseStep 2879023 = 4318535) B4318535
theorem B3643987 : Blo 1705053 3643987 := bstep (se 1 (by rfl) ⟨2732990, by rfl⟩ : syracuseStep 3643987 = 5465981) B5465981
theorem B4858649 : Blo 1705053 4858649 := bstep (se 2 (by rfl) ⟨1821993, by rfl⟩ : syracuseStep 4858649 = 3643987) B3643987
theorem B16626151 : Blo 1705053 16626151 := bstep (se 1 (by rfl) ⟨12469613, by rfl⟩ : syracuseStep 16626151 = 24939227) B24939227
theorem B3838697 : Blo 1705053 3838697 := bstep (se 2 (by rfl) ⟨1439511, by rfl⟩ : syracuseStep 3838697 = 2879023) B2879023
theorem B88672805 : Blo 1705053 88672805 := bstep (se 4 (by rfl) ⟨8313075, by rfl⟩ : syracuseStep 88672805 = 16626151) B16626151
theorem B2559131 : Blo 1705053 2559131 := bstep (se 1 (by rfl) ⟨1919348, by rfl⟩ : syracuseStep 2559131 = 3838697) B3838697
theorem B3239099 : Blo 1705053 3239099 := bstep (se 1 (by rfl) ⟨2429324, by rfl⟩ : syracuseStep 3239099 = 4858649) B4858649
theorem B59115203 : Blo 1705053 59115203 := bstep (se 1 (by rfl) ⟨44336402, by rfl⟩ : syracuseStep 59115203 = 88672805) B88672805
theorem B1706087 : Blo 1705053 1706087 := bstep (se 1 (by rfl) ⟨1279565, by rfl⟩ : syracuseStep 1706087 = 2559131) B2559131
theorem B2159399 : Blo 1705053 2159399 := bstep (se 1 (by rfl) ⟨1619549, by rfl⟩ : syracuseStep 2159399 = 3239099) B3239099
theorem B39410135 : Blo 1705053 39410135 := bstep (se 1 (by rfl) ⟨29557601, by rfl⟩ : syracuseStep 39410135 = 59115203) B59115203
theorem B5758397 : Blo 1705053 5758397 := bstep (se 3 (by rfl) ⟨1079699, by rfl⟩ : syracuseStep 5758397 = 2159399) B2159399
theorem B26273423 : Blo 1705053 26273423 := bstep (se 1 (by rfl) ⟨19705067, by rfl⟩ : syracuseStep 26273423 = 39410135) B39410135
theorem B3838931 : Blo 1705053 3838931 := bstep (se 1 (by rfl) ⟨2879198, by rfl⟩ : syracuseStep 3838931 = 5758397) B5758397
theorem B17515615 : Blo 1705053 17515615 := bstep (se 1 (by rfl) ⟨13136711, by rfl⟩ : syracuseStep 17515615 = 26273423) B26273423
theorem B2559287 : Blo 1705053 2559287 := bstep (se 1 (by rfl) ⟨1919465, by rfl⟩ : syracuseStep 2559287 = 3838931) B3838931
theorem B1706191 : Blo 1705053 1706191 := bstep (se 1 (by rfl) ⟨1279643, by rfl⟩ : syracuseStep 1706191 = 2559287) B2559287
theorem B23354153 : Blo 1705053 23354153 := bstep (se 2 (by rfl) ⟨8757807, by rfl⟩ : syracuseStep 23354153 = 17515615) B17515615
theorem B15569435 : Blo 1705053 15569435 := bstep (se 1 (by rfl) ⟨11677076, by rfl⟩ : syracuseStep 15569435 = 23354153) B23354153
theorem B10379623 : Blo 1705053 10379623 := bstep (se 1 (by rfl) ⟨7784717, by rfl⟩ : syracuseStep 10379623 = 15569435) B15569435
theorem B13839497 : Blo 1705053 13839497 := bstep (se 2 (by rfl) ⟨5189811, by rfl⟩ : syracuseStep 13839497 = 10379623) B10379623
theorem B9226331 : Blo 1705053 9226331 := bstep (se 1 (by rfl) ⟨6919748, by rfl⟩ : syracuseStep 9226331 = 13839497) B13839497
theorem B6150887 : Blo 1705053 6150887 := bstep (se 1 (by rfl) ⟨4613165, by rfl⟩ : syracuseStep 6150887 = 9226331) B9226331
theorem B4100591 : Blo 1705053 4100591 := bstep (se 1 (by rfl) ⟨3075443, by rfl⟩ : syracuseStep 4100591 = 6150887) B6150887
theorem B10934909 : Blo 1705053 10934909 := bstep (se 3 (by rfl) ⟨2050295, by rfl⟩ : syracuseStep 10934909 = 4100591) B4100591
theorem B7289939 : Blo 1705053 7289939 := bstep (se 1 (by rfl) ⟨5467454, by rfl⟩ : syracuseStep 7289939 = 10934909) B10934909
theorem B4859959 : Blo 1705053 4859959 := bstep (se 1 (by rfl) ⟨3644969, by rfl⟩ : syracuseStep 4859959 = 7289939) B7289939
theorem B6479945 : Blo 1705053 6479945 := bstep (se 2 (by rfl) ⟨2429979, by rfl⟩ : syracuseStep 6479945 = 4859959) B4859959
theorem B4319963 : Blo 1705053 4319963 := bstep (se 1 (by rfl) ⟨3239972, by rfl⟩ : syracuseStep 4319963 = 6479945) B6479945
theorem B2879975 : Blo 1705053 2879975 := bstep (se 1 (by rfl) ⟨2159981, by rfl⟩ : syracuseStep 2879975 = 4319963) B4319963
theorem B1919983 : Blo 1705053 1919983 := bstep (se 1 (by rfl) ⟨1439987, by rfl⟩ : syracuseStep 1919983 = 2879975) B2879975
theorem B2559977 : Blo 1705053 2559977 := bstep (se 2 (by rfl) ⟨959991, by rfl⟩ : syracuseStep 2559977 = 1919983) B1919983
theorem B1706651 : Blo 1705053 1706651 := bstep (se 1 (by rfl) ⟨1279988, by rfl⟩ : syracuseStep 1706651 = 2559977) B2559977

theorem C0 (j : ℕ) (h1 : 426263 ≤ j) (h2 : j ≤ 426762) : Blo 1705053 (4 * j + 3) := by
  interval_cases j
  · exact B1705055
  · exact B1705059
  · exact B1705063
  · exact B1705067
  · exact B1705071
  · exact B1705075
  · exact B1705079
  · exact B1705083
  · exact B1705087
  · exact B1705091
  · exact B1705095
  · exact B1705099
  · exact B1705103
  · exact B1705107
  · exact B1705111
  · exact B1705115
  · exact B1705119
  · exact B1705123
  · exact B1705127
  · exact B1705131
  · exact B1705135
  · exact B1705139
  · exact B1705143
  · exact B1705147
  · exact B1705151
  · exact B1705155
  · exact B1705159
  · exact B1705163
  · exact B1705167
  · exact B1705171
  · exact B1705175
  · exact B1705179
  · exact B1705183
  · exact B1705187
  · exact B1705191
  · exact B1705195
  · exact B1705199
  · exact B1705203
  · exact B1705207
  · exact B1705211
  · exact B1705215
  · exact B1705219
  · exact B1705223
  · exact B1705227
  · exact B1705231
  · exact B1705235
  · exact B1705239
  · exact B1705243
  · exact B1705247
  · exact B1705251
  · exact B1705255
  · exact B1705259
  · exact B1705263
  · exact B1705267
  · exact B1705271
  · exact B1705275
  · exact B1705279
  · exact B1705283
  · exact B1705287
  · exact B1705291
  · exact B1705295
  · exact B1705299
  · exact B1705303
  · exact B1705307
  · exact B1705311
  · exact B1705315
  · exact B1705319
  · exact B1705323
  · exact B1705327
  · exact B1705331
  · exact B1705335
  · exact B1705339
  · exact B1705343
  · exact B1705347
  · exact B1705351
  · exact B1705355
  · exact B1705359
  · exact B1705363
  · exact B1705367
  · exact B1705371
  · exact B1705375
  · exact B1705379
  · exact B1705383
  · exact B1705387
  · exact B1705391
  · exact B1705395
  · exact B1705399
  · exact B1705403
  · exact B1705407
  · exact B1705411
  · exact B1705415
  · exact B1705419
  · exact B1705423
  · exact B1705427
  · exact B1705431
  · exact B1705435
  · exact B1705439
  · exact B1705443
  · exact B1705447
  · exact B1705451
  · exact B1705455
  · exact B1705459
  · exact B1705463
  · exact B1705467
  · exact B1705471
  · exact B1705475
  · exact B1705479
  · exact B1705483
  · exact B1705487
  · exact B1705491
  · exact B1705495
  · exact B1705499
  · exact B1705503
  · exact B1705507
  · exact B1705511
  · exact B1705515
  · exact B1705519
  · exact B1705523
  · exact B1705527
  · exact B1705531
  · exact B1705535
  · exact B1705539
  · exact B1705543
  · exact B1705547
  · exact B1705551
  · exact B1705555
  · exact B1705559
  · exact B1705563
  · exact B1705567
  · exact B1705571
  · exact B1705575
  · exact B1705579
  · exact B1705583
  · exact B1705587
  · exact B1705591
  · exact B1705595
  · exact B1705599
  · exact B1705603
  · exact B1705607
  · exact B1705611
  · exact B1705615
  · exact B1705619
  · exact B1705623
  · exact B1705627
  · exact B1705631
  · exact B1705635
  · exact B1705639
  · exact B1705643
  · exact B1705647
  · exact B1705651
  · exact B1705655
  · exact B1705659
  · exact B1705663
  · exact B1705667
  · exact B1705671
  · exact B1705675
  · exact B1705679
  · exact B1705683
  · exact B1705687
  · exact B1705691
  · exact B1705695
  · exact B1705699
  · exact B1705703
  · exact B1705707
  · exact B1705711
  · exact B1705715
  · exact B1705719
  · exact B1705723
  · exact B1705727
  · exact B1705731
  · exact B1705735
  · exact B1705739
  · exact B1705743
  · exact B1705747
  · exact B1705751
  · exact B1705755
  · exact B1705759
  · exact B1705763
  · exact B1705767
  · exact B1705771
  · exact B1705775
  · exact B1705779
  · exact B1705783
  · exact B1705787
  · exact B1705791
  · exact B1705795
  · exact B1705799
  · exact B1705803
  · exact B1705807
  · exact B1705811
  · exact B1705815
  · exact B1705819
  · exact B1705823
  · exact B1705827
  · exact B1705831
  · exact B1705835
  · exact B1705839
  · exact B1705843
  · exact B1705847
  · exact B1705851
  · exact B1705855
  · exact B1705859
  · exact B1705863
  · exact B1705867
  · exact B1705871
  · exact B1705875
  · exact B1705879
  · exact B1705883
  · exact B1705887
  · exact B1705891
  · exact B1705895
  · exact B1705899
  · exact B1705903
  · exact B1705907
  · exact B1705911
  · exact B1705915
  · exact B1705919
  · exact B1705923
  · exact B1705927
  · exact B1705931
  · exact B1705935
  · exact B1705939
  · exact B1705943
  · exact B1705947
  · exact B1705951
  · exact B1705955
  · exact B1705959
  · exact B1705963
  · exact B1705967
  · exact B1705971
  · exact B1705975
  · exact B1705979
  · exact B1705983
  · exact B1705987
  · exact B1705991
  · exact B1705995
  · exact B1705999
  · exact B1706003
  · exact B1706007
  · exact B1706011
  · exact B1706015
  · exact B1706019
  · exact B1706023
  · exact B1706027
  · exact B1706031
  · exact B1706035
  · exact B1706039
  · exact B1706043
  · exact B1706047
  · exact B1706051
  · exact B1706055
  · exact B1706059
  · exact B1706063
  · exact B1706067
  · exact B1706071
  · exact B1706075
  · exact B1706079
  · exact B1706083
  · exact B1706087
  · exact B1706091
  · exact B1706095
  · exact B1706099
  · exact B1706103
  · exact B1706107
  · exact B1706111
  · exact B1706115
  · exact B1706119
  · exact B1706123
  · exact B1706127
  · exact B1706131
  · exact B1706135
  · exact B1706139
  · exact B1706143
  · exact B1706147
  · exact B1706151
  · exact B1706155
  · exact B1706159
  · exact B1706163
  · exact B1706167
  · exact B1706171
  · exact B1706175
  · exact B1706179
  · exact B1706183
  · exact B1706187
  · exact B1706191
  · exact B1706195
  · exact B1706199
  · exact B1706203
  · exact B1706207
  · exact B1706211
  · exact B1706215
  · exact B1706219
  · exact B1706223
  · exact B1706227
  · exact B1706231
  · exact B1706235
  · exact B1706239
  · exact B1706243
  · exact B1706247
  · exact B1706251
  · exact B1706255
  · exact B1706259
  · exact B1706263
  · exact B1706267
  · exact B1706271
  · exact B1706275
  · exact B1706279
  · exact B1706283
  · exact B1706287
  · exact B1706291
  · exact B1706295
  · exact B1706299
  · exact B1706303
  · exact B1706307
  · exact B1706311
  · exact B1706315
  · exact B1706319
  · exact B1706323
  · exact B1706327
  · exact B1706331
  · exact B1706335
  · exact B1706339
  · exact B1706343
  · exact B1706347
  · exact B1706351
  · exact B1706355
  · exact B1706359
  · exact B1706363
  · exact B1706367
  · exact B1706371
  · exact B1706375
  · exact B1706379
  · exact B1706383
  · exact B1706387
  · exact B1706391
  · exact B1706395
  · exact B1706399
  · exact B1706403
  · exact B1706407
  · exact B1706411
  · exact B1706415
  · exact B1706419
  · exact B1706423
  · exact B1706427
  · exact B1706431
  · exact B1706435
  · exact B1706439
  · exact B1706443
  · exact B1706447
  · exact B1706451
  · exact B1706455
  · exact B1706459
  · exact B1706463
  · exact B1706467
  · exact B1706471
  · exact B1706475
  · exact B1706479
  · exact B1706483
  · exact B1706487
  · exact B1706491
  · exact B1706495
  · exact B1706499
  · exact B1706503
  · exact B1706507
  · exact B1706511
  · exact B1706515
  · exact B1706519
  · exact B1706523
  · exact B1706527
  · exact B1706531
  · exact B1706535
  · exact B1706539
  · exact B1706543
  · exact B1706547
  · exact B1706551
  · exact B1706555
  · exact B1706559
  · exact B1706563
  · exact B1706567
  · exact B1706571
  · exact B1706575
  · exact B1706579
  · exact B1706583
  · exact B1706587
  · exact B1706591
  · exact B1706595
  · exact B1706599
  · exact B1706603
  · exact B1706607
  · exact B1706611
  · exact B1706615
  · exact B1706619
  · exact B1706623
  · exact B1706627
  · exact B1706631
  · exact B1706635
  · exact B1706639
  · exact B1706643
  · exact B1706647
  · exact B1706651
  · exact B1706655
  · exact B1706659
  · exact B1706663
  · exact B1706667
  · exact B1706671
  · exact B1706675
  · exact B1706679
  · exact B1706683
  · exact B1706687
  · exact B1706691
  · exact B1706695
  · exact B1706699
  · exact B1706703
  · exact B1706707
  · exact B1706711
  · exact B1706715
  · exact B1706719
  · exact B1706723
  · exact B1706727
  · exact B1706731
  · exact B1706735
  · exact B1706739
  · exact B1706743
  · exact B1706747
  · exact B1706751
  · exact B1706755
  · exact B1706759
  · exact B1706763
  · exact B1706767
  · exact B1706771
  · exact B1706775
  · exact B1706779
  · exact B1706783
  · exact B1706787
  · exact B1706791
  · exact B1706795
  · exact B1706799
  · exact B1706803
  · exact B1706807
  · exact B1706811
  · exact B1706815
  · exact B1706819
  · exact B1706823
  · exact B1706827
  · exact B1706831
  · exact B1706835
  · exact B1706839
  · exact B1706843
  · exact B1706847
  · exact B1706851
  · exact B1706855
  · exact B1706859
  · exact B1706863
  · exact B1706867
  · exact B1706871
  · exact B1706875
  · exact B1706879
  · exact B1706883
  · exact B1706887
  · exact B1706891
  · exact B1706895
  · exact B1706899
  · exact B1706903
  · exact B1706907
  · exact B1706911
  · exact B1706915
  · exact B1706919
  · exact B1706923
  · exact B1706927
  · exact B1706931
  · exact B1706935
  · exact B1706939
  · exact B1706943
  · exact B1706947
  · exact B1706951
  · exact B1706955
  · exact B1706959
  · exact B1706963
  · exact B1706967
  · exact B1706971
  · exact B1706975
  · exact B1706979
  · exact B1706983
  · exact B1706987
  · exact B1706991
  · exact B1706995
  · exact B1706999
  · exact B1707003
  · exact B1707007
  · exact B1707011
  · exact B1707015
  · exact B1707019
  · exact B1707023
  · exact B1707027
  · exact B1707031
  · exact B1707035
  · exact B1707039
  · exact B1707043
  · exact B1707047
  · exact B1707051

theorem solution (m : ℕ) (hlo : 1705053 ≤ m) (hhi : m ≤ 1707053) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 426263 ≤ j := by omega
    have hj2 : j ≤ 426762 := by omega
    have hb : Blo 1705053 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
