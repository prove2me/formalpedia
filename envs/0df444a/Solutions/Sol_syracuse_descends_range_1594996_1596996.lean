-- Prove2me | solution 1 for syracuse_descends_range_1594996_1596996
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:09:15.66249+00:00
-- url     : https://prove2.me/submissions/ea99317e-4f25-40c6-ab93-97ee7c541e0e

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


theorem B4096021 : Blo 1594996 4096021 := bbase (se 6 (by rfl) ⟨96000, by rfl⟩ : syracuseStep 4096021 = 192001) (by norm_num)
theorem B2555965 : Blo 1594996 2555965 := bbase (se 3 (by rfl) ⟨479243, by rfl⟩ : syracuseStep 2555965 = 958487) (by norm_num)
theorem B4096061 : Blo 1594996 4096061 := bbase (se 3 (by rfl) ⟨768011, by rfl⟩ : syracuseStep 4096061 = 1536023) (by norm_num)
theorem B3457093 : Blo 1594996 3457093 := bbase (se 4 (by rfl) ⟨324102, by rfl⟩ : syracuseStep 3457093 = 648205) (by norm_num)
theorem B4038781 : Blo 1594996 4038781 := bbase (se 3 (by rfl) ⟨757271, by rfl⟩ : syracuseStep 4038781 = 1514543) (by norm_num)
theorem B1917065 : Blo 1594996 1917065 := bbase (se 2 (by rfl) ⟨718899, by rfl⟩ : syracuseStep 1917065 = 1437799) (by norm_num)
theorem B2556125 : Blo 1594996 2556125 := bbase (se 3 (by rfl) ⟨479273, by rfl⟩ : syracuseStep 2556125 = 958547) (by norm_num)
theorem B1704169 : Blo 1594996 1704169 := bbase (se 2 (by rfl) ⟨639063, by rfl⟩ : syracuseStep 1704169 = 1278127) (by norm_num)
theorem B4038893 : Blo 1594996 4038893 := bbase (se 3 (by rfl) ⟨757292, by rfl⟩ : syracuseStep 4038893 = 1514585) (by norm_num)
theorem B3031357 : Blo 1594996 3031357 := bbase (se 3 (by rfl) ⟨568379, by rfl⟩ : syracuseStep 3031357 = 1136759) (by norm_num)
theorem B1794397 : Blo 1594996 1794397 := bbase (se 3 (by rfl) ⟨336449, by rfl⟩ : syracuseStep 1794397 = 672899) (by norm_num)
theorem B1818985 : Blo 1594996 1818985 := bbase (se 2 (by rfl) ⟨682119, by rfl⟩ : syracuseStep 1818985 = 1364239) (by norm_num)
theorem B1794433 : Blo 1594996 1794433 := bbase (se 2 (by rfl) ⟨672912, by rfl⟩ : syracuseStep 1794433 = 1345825) (by norm_num)
theorem B2302349 : Blo 1594996 2302349 := bbase (se 3 (by rfl) ⟨431690, by rfl⟩ : syracuseStep 2302349 = 863381) (by norm_num)
theorem B6062485 : Blo 1594996 6062485 := bbase (se 6 (by rfl) ⟨142089, by rfl⟩ : syracuseStep 6062485 = 284179) (by norm_num)
theorem B1794469 : Blo 1594996 1794469 := bbase (se 4 (by rfl) ⟨168231, by rfl⟩ : syracuseStep 1794469 = 336463) (by norm_num)
theorem B4039085 : Blo 1594996 4039085 := bbase (se 3 (by rfl) ⟨757328, by rfl⟩ : syracuseStep 4039085 = 1514657) (by norm_num)
theorem B2425277 : Blo 1594996 2425277 := bbase (se 3 (by rfl) ⟨454739, by rfl⟩ : syracuseStep 2425277 = 909479) (by norm_num)
theorem B1917373 : Blo 1594996 1917373 := bbase (se 3 (by rfl) ⟨359507, by rfl⟩ : syracuseStep 1917373 = 719015) (by norm_num)
theorem B2392517 : Blo 1594996 2392517 := bbase (se 4 (by rfl) ⟨224298, by rfl⟩ : syracuseStep 2392517 = 448597) (by norm_num)
theorem B1794505 : Blo 1594996 1794505 := bbase (se 2 (by rfl) ⟨672939, by rfl⟩ : syracuseStep 1794505 = 1345879) (by norm_num)
theorem B3031501 : Blo 1594996 3031501 := bbase (se 3 (by rfl) ⟨568406, by rfl⟩ : syracuseStep 3031501 = 1136813) (by norm_num)
theorem B1917401 : Blo 1594996 1917401 := bbase (se 2 (by rfl) ⟨719025, by rfl⟩ : syracuseStep 1917401 = 1438051) (by norm_num)
theorem B2392541 : Blo 1594996 2392541 := bbase (se 3 (by rfl) ⟨448601, by rfl⟩ : syracuseStep 2392541 = 897203) (by norm_num)
theorem B1794541 : Blo 1594996 1794541 := bbase (se 3 (by rfl) ⟨336476, by rfl⟩ : syracuseStep 1794541 = 672953) (by norm_num)
theorem B2392565 : Blo 1594996 2392565 := bbase (se 5 (by rfl) ⟨112151, by rfl⟩ : syracuseStep 2392565 = 224303) (by norm_num)
theorem B3408389 : Blo 1594996 3408389 := bbase (se 4 (by rfl) ⟨319536, by rfl⟩ : syracuseStep 3408389 = 639073) (by norm_num)
theorem B2392589 : Blo 1594996 2392589 := bbase (se 3 (by rfl) ⟨448610, by rfl⟩ : syracuseStep 2392589 = 897221) (by norm_num)
theorem B1794577 : Blo 1594996 1794577 := bbase (se 2 (by rfl) ⟨672966, by rfl⟩ : syracuseStep 1794577 = 1345933) (by norm_num)
theorem B11502101 : Blo 1594996 11502101 := bbase (se 6 (by rfl) ⟨269580, by rfl⟩ : syracuseStep 11502101 = 539161) (by norm_num)
theorem B5112341 : Blo 1594996 5112341 := bbase (se 6 (by rfl) ⟨119820, by rfl⟩ : syracuseStep 5112341 = 239641) (by norm_num)
theorem B2392613 : Blo 1594996 2392613 := bbase (se 4 (by rfl) ⟨224307, by rfl⟩ : syracuseStep 2392613 = 448615) (by norm_num)
theorem B1794613 : Blo 1594996 1794613 := bbase (se 5 (by rfl) ⟨84122, by rfl⟩ : syracuseStep 1794613 = 168245) (by norm_num)
theorem B2392637 : Blo 1594996 2392637 := bbase (se 3 (by rfl) ⟨448619, by rfl⟩ : syracuseStep 2392637 = 897239) (by norm_num)
theorem B2728517 : Blo 1594996 2728517 := bbase (se 4 (by rfl) ⟨255798, by rfl⟩ : syracuseStep 2728517 = 511597) (by norm_num)
theorem B2392661 : Blo 1594996 2392661 := bbase (se 8 (by rfl) ⟨14019, by rfl⟩ : syracuseStep 2392661 = 28039) (by norm_num)
theorem B1794649 : Blo 1594996 1794649 := bbase (se 2 (by rfl) ⟨672993, by rfl⟩ : syracuseStep 1794649 = 1345987) (by norm_num)
theorem B2392685 : Blo 1594996 2392685 := bbase (se 3 (by rfl) ⟨448628, by rfl⟩ : syracuseStep 2392685 = 897257) (by norm_num)
theorem B3031661 : Blo 1594996 3031661 := bbase (se 3 (by rfl) ⟨568436, by rfl⟩ : syracuseStep 3031661 = 1136873) (by norm_num)
theorem B1794685 : Blo 1594996 1794685 := bbase (se 3 (by rfl) ⟨336503, by rfl⟩ : syracuseStep 1794685 = 673007) (by norm_num)
theorem B2392709 : Blo 1594996 2392709 := bbase (se 4 (by rfl) ⟨224316, by rfl⟩ : syracuseStep 2392709 = 448633) (by norm_num)
theorem B3588749 : Blo 1594996 3588749 := bbase (se 3 (by rfl) ⟨672890, by rfl⟩ : syracuseStep 3588749 = 1345781) (by norm_num)
theorem B2392733 : Blo 1594996 2392733 := bbase (se 3 (by rfl) ⟨448637, by rfl⟩ : syracuseStep 2392733 = 897275) (by norm_num)
theorem B1794721 : Blo 1594996 1794721 := bbase (se 2 (by rfl) ⟨673020, by rfl⟩ : syracuseStep 1794721 = 1346041) (by norm_num)
theorem B1704613 : Blo 1594996 1704613 := bbase (se 4 (by rfl) ⟨159807, by rfl⟩ : syracuseStep 1704613 = 319615) (by norm_num)
theorem B2392757 : Blo 1594996 2392757 := bbase (se 5 (by rfl) ⟨112160, by rfl⟩ : syracuseStep 2392757 = 224321) (by norm_num)
theorem B1794757 : Blo 1594996 1794757 := bbase (se 4 (by rfl) ⟨168258, by rfl⟩ : syracuseStep 1794757 = 336517) (by norm_num)
theorem B6062789 : Blo 1594996 6062789 := bbase (se 4 (by rfl) ⟨568386, by rfl⟩ : syracuseStep 6062789 = 1136773) (by norm_num)
theorem B2392781 : Blo 1594996 2392781 := bbase (se 3 (by rfl) ⟨448646, by rfl⟩ : syracuseStep 2392781 = 897293) (by norm_num)
theorem B3588821 : Blo 1594996 3588821 := bbase (se 7 (by rfl) ⟨42056, by rfl⟩ : syracuseStep 3588821 = 84113) (by norm_num)
theorem B6816469 : Blo 1594996 6816469 := bbase (se 7 (by rfl) ⟨79880, by rfl⟩ : syracuseStep 6816469 = 159761) (by norm_num)
theorem B1704673 : Blo 1594996 1704673 := bbase (se 2 (by rfl) ⟨639252, by rfl⟩ : syracuseStep 1704673 = 1278505) (by norm_num)
theorem B2392805 : Blo 1594996 2392805 := bbase (se 4 (by rfl) ⟨224325, by rfl⟩ : syracuseStep 2392805 = 448651) (by norm_num)
theorem B1794793 : Blo 1594996 1794793 := bbase (se 2 (by rfl) ⟨673047, by rfl⟩ : syracuseStep 1794793 = 1346095) (by norm_num)
theorem B2392829 : Blo 1594996 2392829 := bbase (se 3 (by rfl) ⟨448655, by rfl⟩ : syracuseStep 2392829 = 897311) (by norm_num)
theorem B3408637 : Blo 1594996 3408637 := bbase (se 3 (by rfl) ⟨639119, by rfl⟩ : syracuseStep 3408637 = 1278239) (by norm_num)
theorem B4039429 : Blo 1594996 4039429 := bbase (se 4 (by rfl) ⟨378696, by rfl⟩ : syracuseStep 4039429 = 757393) (by norm_num)
theorem B1794829 : Blo 1594996 1794829 := bbase (se 3 (by rfl) ⟨336530, by rfl⟩ : syracuseStep 1794829 = 673061) (by norm_num)
theorem B1819409 : Blo 1594996 1819409 := bbase (se 2 (by rfl) ⟨682278, by rfl⟩ : syracuseStep 1819409 = 1364557) (by norm_num)
theorem B2392853 : Blo 1594996 2392853 := bbase (se 6 (by rfl) ⟨56082, by rfl⟩ : syracuseStep 2392853 = 112165) (by norm_num)
theorem B3588893 : Blo 1594996 3588893 := bbase (se 3 (by rfl) ⟨672917, by rfl⟩ : syracuseStep 3588893 = 1345835) (by norm_num)
theorem B2392877 : Blo 1594996 2392877 := bbase (se 3 (by rfl) ⟨448664, by rfl⟩ : syracuseStep 2392877 = 897329) (by norm_num)
theorem B1794865 : Blo 1594996 1794865 := bbase (se 2 (by rfl) ⟨673074, by rfl⟩ : syracuseStep 1794865 = 1346149) (by norm_num)
theorem B15344437 : Blo 1594996 15344437 := bbase (se 5 (by rfl) ⟨719270, by rfl⟩ : syracuseStep 15344437 = 1438541) (by norm_num)
theorem B2392901 : Blo 1594996 2392901 := bbase (se 4 (by rfl) ⟨224334, by rfl⟩ : syracuseStep 2392901 = 448669) (by norm_num)
theorem B1794901 : Blo 1594996 1794901 := bbase (se 9 (by rfl) ⟨5258, by rfl⟩ : syracuseStep 1794901 = 10517) (by norm_num)
theorem B2392925 : Blo 1594996 2392925 := bbase (se 3 (by rfl) ⟨448673, by rfl⟩ : syracuseStep 2392925 = 897347) (by norm_num)
theorem B3588965 : Blo 1594996 3588965 := bbase (se 4 (by rfl) ⟨336465, by rfl⟩ : syracuseStep 3588965 = 672931) (by norm_num)
theorem B2392949 : Blo 1594996 2392949 := bbase (se 5 (by rfl) ⟨112169, by rfl⟩ : syracuseStep 2392949 = 224339) (by norm_num)
theorem B4039541 : Blo 1594996 4039541 := bbase (se 5 (by rfl) ⟨189353, by rfl⟩ : syracuseStep 4039541 = 378707) (by norm_num)
theorem B1794937 : Blo 1594996 1794937 := bbase (se 2 (by rfl) ⟨673101, by rfl⟩ : syracuseStep 1794937 = 1346203) (by norm_num)
theorem B5751685 : Blo 1594996 5751685 := bbase (se 4 (by rfl) ⟨539220, by rfl⟩ : syracuseStep 5751685 = 1078441) (by norm_num)
theorem B2392973 : Blo 1594996 2392973 := bbase (se 3 (by rfl) ⟨448682, by rfl⟩ : syracuseStep 2392973 = 897365) (by norm_num)
theorem B1794973 : Blo 1594996 1794973 := bbase (se 3 (by rfl) ⟨336557, by rfl⟩ : syracuseStep 1794973 = 673115) (by norm_num)
theorem B2392997 : Blo 1594996 2392997 := bbase (se 4 (by rfl) ⟨224343, by rfl⟩ : syracuseStep 2392997 = 448687) (by norm_num)
theorem B3589037 : Blo 1594996 3589037 := bbase (se 3 (by rfl) ⟨672944, by rfl⟩ : syracuseStep 3589037 = 1345889) (by norm_num)
theorem B2393021 : Blo 1594996 2393021 := bbase (se 3 (by rfl) ⟨448691, by rfl⟩ : syracuseStep 2393021 = 897383) (by norm_num)
theorem B1795009 : Blo 1594996 1795009 := bbase (se 2 (by rfl) ⟨673128, by rfl⟩ : syracuseStep 1795009 = 1346257) (by norm_num)
theorem B1917901 : Blo 1594996 1917901 := bbase (se 3 (by rfl) ⟨359606, by rfl⟩ : syracuseStep 1917901 = 719213) (by norm_num)
theorem B2393045 : Blo 1594996 2393045 := bbase (se 7 (by rfl) ⟨28043, by rfl⟩ : syracuseStep 2393045 = 56087) (by norm_num)
theorem B1795045 : Blo 1594996 1795045 := bbase (se 4 (by rfl) ⟨168285, by rfl⟩ : syracuseStep 1795045 = 336571) (by norm_num)
theorem B2393069 : Blo 1594996 2393069 := bbase (se 3 (by rfl) ⟨448700, by rfl⟩ : syracuseStep 2393069 = 897401) (by norm_num)
theorem B3589109 : Blo 1594996 3589109 := bbase (se 5 (by rfl) ⟨168239, by rfl⟩ : syracuseStep 3589109 = 336479) (by norm_num)
theorem B3638261 : Blo 1594996 3638261 := bbase (se 5 (by rfl) ⟨170543, by rfl⟩ : syracuseStep 3638261 = 341087) (by norm_num)
theorem B2393093 : Blo 1594996 2393093 := bbase (se 4 (by rfl) ⟨224352, by rfl⟩ : syracuseStep 2393093 = 448705) (by norm_num)
theorem B1795081 : Blo 1594996 1795081 := bbase (se 2 (by rfl) ⟨673155, by rfl⟩ : syracuseStep 1795081 = 1346311) (by norm_num)
theorem B2393117 : Blo 1594996 2393117 := bbase (se 3 (by rfl) ⟨448709, by rfl⟩ : syracuseStep 2393117 = 897419) (by norm_num)
theorem B1704989 : Blo 1594996 1704989 := bbase (se 3 (by rfl) ⟨319685, by rfl⟩ : syracuseStep 1704989 = 639371) (by norm_num)
theorem B5383205 : Blo 1594996 5383205 := bbase (se 4 (by rfl) ⟨504675, by rfl⟩ : syracuseStep 5383205 = 1009351) (by norm_num)
theorem B1795117 : Blo 1594996 1795117 := bbase (se 3 (by rfl) ⟨336584, by rfl⟩ : syracuseStep 1795117 = 673169) (by norm_num)
theorem B2393141 : Blo 1594996 2393141 := bbase (se 5 (by rfl) ⟨112178, by rfl⟩ : syracuseStep 2393141 = 224357) (by norm_num)
theorem B4039733 : Blo 1594996 4039733 := bbase (se 5 (by rfl) ⟨189362, by rfl⟩ : syracuseStep 4039733 = 378725) (by norm_num)
theorem B3589181 : Blo 1594996 3589181 := bbase (se 3 (by rfl) ⟨672971, by rfl⟩ : syracuseStep 3589181 = 1345943) (by norm_num)
theorem B2393165 : Blo 1594996 2393165 := bbase (se 3 (by rfl) ⟨448718, by rfl⟩ : syracuseStep 2393165 = 897437) (by norm_num)
theorem B1795153 : Blo 1594996 1795153 := bbase (se 2 (by rfl) ⟨673182, by rfl⟩ : syracuseStep 1795153 = 1346365) (by norm_num)
theorem B2393189 : Blo 1594996 2393189 := bbase (se 4 (by rfl) ⟨224361, by rfl⟩ : syracuseStep 2393189 = 448723) (by norm_num)
theorem B8078453 : Blo 1594996 8078453 := bbase (se 5 (by rfl) ⟨378677, by rfl⟩ : syracuseStep 8078453 = 757355) (by norm_num)
theorem B1795189 : Blo 1594996 1795189 := bbase (se 5 (by rfl) ⟨84149, by rfl⟩ : syracuseStep 1795189 = 168299) (by norm_num)
theorem B2393213 : Blo 1594996 2393213 := bbase (se 3 (by rfl) ⟨448727, by rfl⟩ : syracuseStep 2393213 = 897455) (by norm_num)
theorem B2425981 : Blo 1594996 2425981 := bbase (se 3 (by rfl) ⟨454871, by rfl⟩ : syracuseStep 2425981 = 909743) (by norm_num)
theorem B3589253 : Blo 1594996 3589253 := bbase (se 4 (by rfl) ⟨336492, by rfl⟩ : syracuseStep 3589253 = 672985) (by norm_num)
theorem B2393237 : Blo 1594996 2393237 := bbase (se 6 (by rfl) ⟨56091, by rfl⟩ : syracuseStep 2393237 = 112183) (by norm_num)
theorem B1795225 : Blo 1594996 1795225 := bbase (se 2 (by rfl) ⟨673209, by rfl⟩ : syracuseStep 1795225 = 1346419) (by norm_num)
theorem B2393261 : Blo 1594996 2393261 := bbase (se 3 (by rfl) ⟨448736, by rfl⟩ : syracuseStep 2393261 = 897473) (by norm_num)
theorem B1795261 : Blo 1594996 1795261 := bbase (se 3 (by rfl) ⟨336611, by rfl⟩ : syracuseStep 1795261 = 673223) (by norm_num)
theorem B2393285 : Blo 1594996 2393285 := bbase (se 4 (by rfl) ⟨224370, by rfl⟩ : syracuseStep 2393285 = 448741) (by norm_num)
theorem B3589325 : Blo 1594996 3589325 := bbase (se 3 (by rfl) ⟨672998, by rfl⟩ : syracuseStep 3589325 = 1345997) (by norm_num)
theorem B9086165 : Blo 1594996 9086165 := bbase (se 7 (by rfl) ⟨106478, by rfl⟩ : syracuseStep 9086165 = 212957) (by norm_num)
theorem B2393309 : Blo 1594996 2393309 := bbase (se 3 (by rfl) ⟨448745, by rfl⟩ : syracuseStep 2393309 = 897491) (by norm_num)
theorem B1795297 : Blo 1594996 1795297 := bbase (se 2 (by rfl) ⟨673236, by rfl⟩ : syracuseStep 1795297 = 1346473) (by norm_num)
theorem B5833957 : Blo 1594996 5833957 := bbase (se 4 (by rfl) ⟨546933, by rfl⟩ : syracuseStep 5833957 = 1093867) (by norm_num)
theorem B2393333 : Blo 1594996 2393333 := bbase (se 5 (by rfl) ⟨112187, by rfl⟩ : syracuseStep 2393333 = 224375) (by norm_num)
theorem B3409141 : Blo 1594996 3409141 := bbase (se 5 (by rfl) ⟨159803, by rfl⟩ : syracuseStep 3409141 = 319607) (by norm_num)
theorem B1795333 : Blo 1594996 1795333 := bbase (se 4 (by rfl) ⟨168312, by rfl⟩ : syracuseStep 1795333 = 336625) (by norm_num)
theorem B2393357 : Blo 1594996 2393357 := bbase (se 3 (by rfl) ⟨448754, by rfl⟩ : syracuseStep 2393357 = 897509) (by norm_num)
theorem B3589397 : Blo 1594996 3589397 := bbase (se 6 (by rfl) ⟨84126, by rfl⟩ : syracuseStep 3589397 = 168253) (by norm_num)
theorem B2393381 : Blo 1594996 2393381 := bbase (se 4 (by rfl) ⟨224379, by rfl⟩ : syracuseStep 2393381 = 448759) (by norm_num)
theorem B1795369 : Blo 1594996 1795369 := bbase (se 2 (by rfl) ⟨673263, by rfl⟩ : syracuseStep 1795369 = 1346527) (by norm_num)
theorem B2393405 : Blo 1594996 2393405 := bbase (se 3 (by rfl) ⟨448763, by rfl⟩ : syracuseStep 2393405 = 897527) (by norm_num)
theorem B2557253 : Blo 1594996 2557253 := bbase (se 4 (by rfl) ⟨239742, by rfl⟩ : syracuseStep 2557253 = 479485) (by norm_num)
theorem B1795405 : Blo 1594996 1795405 := bbase (se 3 (by rfl) ⟨336638, by rfl⟩ : syracuseStep 1795405 = 673277) (by norm_num)
theorem B2393429 : Blo 1594996 2393429 := bbase (se 12 (by rfl) ⟨876, by rfl⟩ : syracuseStep 2393429 = 1753) (by norm_num)
theorem B3589469 : Blo 1594996 3589469 := bbase (se 3 (by rfl) ⟨673025, by rfl⟩ : syracuseStep 3589469 = 1346051) (by norm_num)
theorem B2393453 : Blo 1594996 2393453 := bbase (se 3 (by rfl) ⟨448772, by rfl⟩ : syracuseStep 2393453 = 897545) (by norm_num)
theorem B1795441 : Blo 1594996 1795441 := bbase (se 2 (by rfl) ⟨673290, by rfl⟩ : syracuseStep 1795441 = 1346581) (by norm_num)
theorem B2876789 : Blo 1594996 2876789 := bbase (se 5 (by rfl) ⟨134849, by rfl⟩ : syracuseStep 2876789 = 269699) (by norm_num)
theorem B2336125 : Blo 1594996 2336125 := bbase (se 3 (by rfl) ⟨438023, by rfl⟩ : syracuseStep 2336125 = 876047) (by norm_num)
theorem B2393477 : Blo 1594996 2393477 := bbase (se 4 (by rfl) ⟨224388, by rfl⟩ : syracuseStep 2393477 = 448777) (by norm_num)
theorem B4040077 : Blo 1594996 4040077 := bbase (se 3 (by rfl) ⟨757514, by rfl⟩ : syracuseStep 4040077 = 1515029) (by norm_num)
theorem B1795477 : Blo 1594996 1795477 := bbase (se 6 (by rfl) ⟨42081, by rfl⟩ : syracuseStep 1795477 = 84163) (by norm_num)
theorem B2393501 : Blo 1594996 2393501 := bbase (se 3 (by rfl) ⟨448781, by rfl⟩ : syracuseStep 2393501 = 897563) (by norm_num)
theorem B3589541 : Blo 1594996 3589541 := bbase (se 4 (by rfl) ⟨336519, by rfl⟩ : syracuseStep 3589541 = 673039) (by norm_num)
theorem B2876845 : Blo 1594996 2876845 := bbase (se 3 (by rfl) ⟨539408, by rfl⟩ : syracuseStep 2876845 = 1078817) (by norm_num)
theorem B2393525 : Blo 1594996 2393525 := bbase (se 5 (by rfl) ⟨112196, by rfl⟩ : syracuseStep 2393525 = 224393) (by norm_num)
theorem B1795513 : Blo 1594996 1795513 := bbase (se 2 (by rfl) ⟨673317, by rfl⟩ : syracuseStep 1795513 = 1346635) (by norm_num)
theorem B2393549 : Blo 1594996 2393549 := bbase (se 3 (by rfl) ⟨448790, by rfl⟩ : syracuseStep 2393549 = 897581) (by norm_num)
theorem B5383637 : Blo 1594996 5383637 := bbase (se 7 (by rfl) ⟨63089, by rfl⟩ : syracuseStep 5383637 = 126179) (by norm_num)
theorem B1795549 : Blo 1594996 1795549 := bbase (se 3 (by rfl) ⟨336665, by rfl⟩ : syracuseStep 1795549 = 673331) (by norm_num)
theorem B2393573 : Blo 1594996 2393573 := bbase (se 4 (by rfl) ⟨224397, by rfl⟩ : syracuseStep 2393573 = 448795) (by norm_num)
theorem B3589613 : Blo 1594996 3589613 := bbase (se 3 (by rfl) ⟨673052, by rfl⟩ : syracuseStep 3589613 = 1346105) (by norm_num)
theorem B2393597 : Blo 1594996 2393597 := bbase (se 3 (by rfl) ⟨448799, by rfl⟩ : syracuseStep 2393597 = 897599) (by norm_num)
theorem B4040189 : Blo 1594996 4040189 := bbase (se 3 (by rfl) ⟨757535, by rfl⟩ : syracuseStep 4040189 = 1515071) (by norm_num)
theorem B1795585 : Blo 1594996 1795585 := bbase (se 2 (by rfl) ⟨673344, by rfl⟩ : syracuseStep 1795585 = 1346689) (by norm_num)
theorem B2336261 : Blo 1594996 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B2393621 : Blo 1594996 2393621 := bbase (se 6 (by rfl) ⟨56100, by rfl⟩ : syracuseStep 2393621 = 112201) (by norm_num)
theorem B1795621 : Blo 1594996 1795621 := bbase (se 4 (by rfl) ⟨168339, by rfl⟩ : syracuseStep 1795621 = 336679) (by norm_num)
theorem B2393645 : Blo 1594996 2393645 := bbase (se 3 (by rfl) ⟨448808, by rfl⟩ : syracuseStep 2393645 = 897617) (by norm_num)
theorem B3589685 : Blo 1594996 3589685 := bbase (se 5 (by rfl) ⟨168266, by rfl⟩ : syracuseStep 3589685 = 336533) (by norm_num)
theorem B2393669 : Blo 1594996 2393669 := bbase (se 4 (by rfl) ⟨224406, by rfl⟩ : syracuseStep 2393669 = 448813) (by norm_num)
theorem B1795657 : Blo 1594996 1795657 := bbase (se 2 (by rfl) ⟨673371, by rfl⟩ : syracuseStep 1795657 = 1346743) (by norm_num)
theorem B2393693 : Blo 1594996 2393693 := bbase (se 3 (by rfl) ⟨448817, by rfl⟩ : syracuseStep 2393693 = 897635) (by norm_num)
theorem B1795693 : Blo 1594996 1795693 := bbase (se 3 (by rfl) ⟨336692, by rfl⟩ : syracuseStep 1795693 = 673385) (by norm_num)
theorem B2393717 : Blo 1594996 2393717 := bbase (se 5 (by rfl) ⟨112205, by rfl⟩ : syracuseStep 2393717 = 224411) (by norm_num)
theorem B3589757 : Blo 1594996 3589757 := bbase (se 3 (by rfl) ⟨673079, by rfl⟩ : syracuseStep 3589757 = 1346159) (by norm_num)
theorem B2393741 : Blo 1594996 2393741 := bbase (se 3 (by rfl) ⟨448826, by rfl⟩ : syracuseStep 2393741 = 897653) (by norm_num)
theorem B1795729 : Blo 1594996 1795729 := bbase (se 2 (by rfl) ⟨673398, by rfl⟩ : syracuseStep 1795729 = 1346797) (by norm_num)
theorem B2393765 : Blo 1594996 2393765 := bbase (se 4 (by rfl) ⟨224415, by rfl⟩ : syracuseStep 2393765 = 448831) (by norm_num)
theorem B1795765 : Blo 1594996 1795765 := bbase (se 5 (by rfl) ⟨84176, by rfl⟩ : syracuseStep 1795765 = 168353) (by norm_num)
theorem B2393789 : Blo 1594996 2393789 := bbase (se 3 (by rfl) ⟨448835, by rfl⟩ : syracuseStep 2393789 = 897671) (by norm_num)
theorem B4040381 : Blo 1594996 4040381 := bbase (se 3 (by rfl) ⟨757571, by rfl⟩ : syracuseStep 4040381 = 1515143) (by norm_num)
theorem B3589829 : Blo 1594996 3589829 := bbase (se 4 (by rfl) ⟨336546, by rfl⟩ : syracuseStep 3589829 = 673093) (by norm_num)
theorem B2393813 : Blo 1594996 2393813 := bbase (se 7 (by rfl) ⟨28052, by rfl⟩ : syracuseStep 2393813 = 56105) (by norm_num)
theorem B1795801 : Blo 1594996 1795801 := bbase (se 2 (by rfl) ⟨673425, by rfl⟩ : syracuseStep 1795801 = 1346851) (by norm_num)
theorem B2393837 : Blo 1594996 2393837 := bbase (se 3 (by rfl) ⟨448844, by rfl⟩ : syracuseStep 2393837 = 897689) (by norm_num)
theorem B1795837 : Blo 1594996 1795837 := bbase (se 3 (by rfl) ⟨336719, by rfl⟩ : syracuseStep 1795837 = 673439) (by norm_num)
theorem B2393861 : Blo 1594996 2393861 := bbase (se 4 (by rfl) ⟨224424, by rfl⟩ : syracuseStep 2393861 = 448849) (by norm_num)
theorem B3589901 : Blo 1594996 3589901 := bbase (se 3 (by rfl) ⟨673106, by rfl⟩ : syracuseStep 3589901 = 1346213) (by norm_num)
theorem B2393885 : Blo 1594996 2393885 := bbase (se 3 (by rfl) ⟨448853, by rfl⟩ : syracuseStep 2393885 = 897707) (by norm_num)
theorem B1795873 : Blo 1594996 1795873 := bbase (se 2 (by rfl) ⟨673452, by rfl⟩ : syracuseStep 1795873 = 1346905) (by norm_num)
theorem B2393909 : Blo 1594996 2393909 := bbase (se 5 (by rfl) ⟨112214, by rfl⟩ : syracuseStep 2393909 = 224429) (by norm_num)
theorem B1795909 : Blo 1594996 1795909 := bbase (se 4 (by rfl) ⟨168366, by rfl⟩ : syracuseStep 1795909 = 336733) (by norm_num)
theorem B2557765 : Blo 1594996 2557765 := bbase (se 4 (by rfl) ⟨239790, by rfl⟩ : syracuseStep 2557765 = 479581) (by norm_num)
theorem B2393933 : Blo 1594996 2393933 := bbase (se 3 (by rfl) ⟨448862, by rfl⟩ : syracuseStep 2393933 = 897725) (by norm_num)
theorem B3589973 : Blo 1594996 3589973 := bbase (se 9 (by rfl) ⟨10517, by rfl⟩ : syracuseStep 3589973 = 21035) (by norm_num)
theorem B5113685 : Blo 1594996 5113685 := bbase (se 9 (by rfl) ⟨14981, by rfl⟩ : syracuseStep 5113685 = 29963) (by norm_num)
theorem B2393957 : Blo 1594996 2393957 := bbase (se 4 (by rfl) ⟨224433, by rfl⟩ : syracuseStep 2393957 = 448867) (by norm_num)
theorem B1795945 : Blo 1594996 1795945 := bbase (se 2 (by rfl) ⟨673479, by rfl⟩ : syracuseStep 1795945 = 1346959) (by norm_num)
theorem B2393981 : Blo 1594996 2393981 := bbase (se 3 (by rfl) ⟨448871, by rfl⟩ : syracuseStep 2393981 = 897743) (by norm_num)
theorem B5384069 : Blo 1594996 5384069 := bbase (se 4 (by rfl) ⟨504756, by rfl⟩ : syracuseStep 5384069 = 1009513) (by norm_num)
theorem B1795981 : Blo 1594996 1795981 := bbase (se 3 (by rfl) ⟨336746, by rfl⟩ : syracuseStep 1795981 = 673493) (by norm_num)
theorem B2394005 : Blo 1594996 2394005 := bbase (se 6 (by rfl) ⟨56109, by rfl⟩ : syracuseStep 2394005 = 112219) (by norm_num)
theorem B3590045 : Blo 1594996 3590045 := bbase (se 3 (by rfl) ⟨673133, by rfl⟩ : syracuseStep 3590045 = 1346267) (by norm_num)
theorem B2394029 : Blo 1594996 2394029 := bbase (se 3 (by rfl) ⟨448880, by rfl⟩ : syracuseStep 2394029 = 897761) (by norm_num)
theorem B1796017 : Blo 1594996 1796017 := bbase (se 2 (by rfl) ⟨673506, by rfl⟩ : syracuseStep 1796017 = 1347013) (by norm_num)
theorem B2394053 : Blo 1594996 2394053 := bbase (se 4 (by rfl) ⟨224442, by rfl⟩ : syracuseStep 2394053 = 448885) (by norm_num)
theorem B1796053 : Blo 1594996 1796053 := bbase (se 7 (by rfl) ⟨21047, by rfl⟩ : syracuseStep 1796053 = 42095) (by norm_num)
theorem B2394077 : Blo 1594996 2394077 := bbase (se 3 (by rfl) ⟨448889, by rfl⟩ : syracuseStep 2394077 = 897779) (by norm_num)
theorem B3590117 : Blo 1594996 3590117 := bbase (se 4 (by rfl) ⟨336573, by rfl⟩ : syracuseStep 3590117 = 673147) (by norm_num)
theorem B2394101 : Blo 1594996 2394101 := bbase (se 5 (by rfl) ⟨112223, by rfl⟩ : syracuseStep 2394101 = 224447) (by norm_num)
theorem B1796089 : Blo 1594996 1796089 := bbase (se 2 (by rfl) ⟨673533, by rfl⟩ : syracuseStep 1796089 = 1347067) (by norm_num)
theorem B2271245 : Blo 1594996 2271245 := bbase (se 3 (by rfl) ⟨425858, by rfl⟩ : syracuseStep 2271245 = 851717) (by norm_num)
theorem B2394125 : Blo 1594996 2394125 := bbase (se 3 (by rfl) ⟨448898, by rfl⟩ : syracuseStep 2394125 = 897797) (by norm_num)
theorem B4040725 : Blo 1594996 4040725 := bbase (se 6 (by rfl) ⟨94704, by rfl⟩ : syracuseStep 4040725 = 189409) (by norm_num)
theorem B1796125 : Blo 1594996 1796125 := bbase (se 3 (by rfl) ⟨336773, by rfl⟩ : syracuseStep 1796125 = 673547) (by norm_num)
theorem B2394149 : Blo 1594996 2394149 := bbase (se 4 (by rfl) ⟨224451, by rfl⟩ : syracuseStep 2394149 = 448903) (by norm_num)
theorem B3590189 : Blo 1594996 3590189 := bbase (se 3 (by rfl) ⟨673160, by rfl⟩ : syracuseStep 3590189 = 1346321) (by norm_num)
theorem B2394173 : Blo 1594996 2394173 := bbase (se 3 (by rfl) ⟨448907, by rfl⟩ : syracuseStep 2394173 = 897815) (by norm_num)
theorem B1796161 : Blo 1594996 1796161 := bbase (se 2 (by rfl) ⟨673560, by rfl⟩ : syracuseStep 1796161 = 1347121) (by norm_num)
theorem B2394197 : Blo 1594996 2394197 := bbase (se 8 (by rfl) ⟨14028, by rfl⟩ : syracuseStep 2394197 = 28057) (by norm_num)
theorem B1796197 : Blo 1594996 1796197 := bbase (se 4 (by rfl) ⟨168393, by rfl⟩ : syracuseStep 1796197 = 336787) (by norm_num)
theorem B2394221 : Blo 1594996 2394221 := bbase (se 3 (by rfl) ⟨448916, by rfl⟩ : syracuseStep 2394221 = 897833) (by norm_num)
theorem B3410029 : Blo 1594996 3410029 := bbase (se 3 (by rfl) ⟨639380, by rfl⟩ : syracuseStep 3410029 = 1278761) (by norm_num)
theorem B3590261 : Blo 1594996 3590261 := bbase (se 5 (by rfl) ⟨168293, by rfl⟩ : syracuseStep 3590261 = 336587) (by norm_num)
theorem B2394245 : Blo 1594996 2394245 := bbase (se 4 (by rfl) ⟨224460, by rfl⟩ : syracuseStep 2394245 = 448921) (by norm_num)
theorem B4040837 : Blo 1594996 4040837 := bbase (se 4 (by rfl) ⟨378828, by rfl⟩ : syracuseStep 4040837 = 757657) (by norm_num)
theorem B1796233 : Blo 1594996 1796233 := bbase (se 2 (by rfl) ⟨673587, by rfl⟩ : syracuseStep 1796233 = 1347175) (by norm_num)
theorem B2394269 : Blo 1594996 2394269 := bbase (se 3 (by rfl) ⟨448925, by rfl⟩ : syracuseStep 2394269 = 897851) (by norm_num)
theorem B1820837 : Blo 1594996 1820837 := bbase (se 4 (by rfl) ⟨170703, by rfl⟩ : syracuseStep 1820837 = 341407) (by norm_num)
theorem B1796269 : Blo 1594996 1796269 := bbase (se 3 (by rfl) ⟨336800, by rfl⟩ : syracuseStep 1796269 = 673601) (by norm_num)
theorem B2394293 : Blo 1594996 2394293 := bbase (se 5 (by rfl) ⟨112232, by rfl⟩ : syracuseStep 2394293 = 224465) (by norm_num)
theorem B3590333 : Blo 1594996 3590333 := bbase (se 3 (by rfl) ⟨673187, by rfl⟩ : syracuseStep 3590333 = 1346375) (by norm_num)
theorem B3836101 : Blo 1594996 3836101 := bbase (se 4 (by rfl) ⟨359634, by rfl⟩ : syracuseStep 3836101 = 719269) (by norm_num)
theorem B2394317 : Blo 1594996 2394317 := bbase (se 3 (by rfl) ⟨448934, by rfl⟩ : syracuseStep 2394317 = 897869) (by norm_num)
theorem B1796305 : Blo 1594996 1796305 := bbase (se 2 (by rfl) ⟨673614, by rfl⟩ : syracuseStep 1796305 = 1347229) (by norm_num)
theorem B2427101 : Blo 1594996 2427101 := bbase (se 3 (by rfl) ⟨455081, by rfl⟩ : syracuseStep 2427101 = 910163) (by norm_num)
theorem B2394341 : Blo 1594996 2394341 := bbase (se 4 (by rfl) ⟨224469, by rfl⟩ : syracuseStep 2394341 = 448939) (by norm_num)
theorem B1796341 : Blo 1594996 1796341 := bbase (se 5 (by rfl) ⟨84203, by rfl⟩ : syracuseStep 1796341 = 168407) (by norm_num)
theorem B2394365 : Blo 1594996 2394365 := bbase (se 3 (by rfl) ⟨448943, by rfl⟩ : syracuseStep 2394365 = 897887) (by norm_num)
theorem B3590405 : Blo 1594996 3590405 := bbase (se 4 (by rfl) ⟨336600, by rfl⟩ : syracuseStep 3590405 = 673201) (by norm_num)
theorem B2394389 : Blo 1594996 2394389 := bbase (se 6 (by rfl) ⟨56118, by rfl⟩ : syracuseStep 2394389 = 112237) (by norm_num)
theorem B1796377 : Blo 1594996 1796377 := bbase (se 2 (by rfl) ⟨673641, by rfl⟩ : syracuseStep 1796377 = 1347283) (by norm_num)
theorem B2394413 : Blo 1594996 2394413 := bbase (se 3 (by rfl) ⟨448952, by rfl⟩ : syracuseStep 2394413 = 897905) (by norm_num)
theorem B5384501 : Blo 1594996 5384501 := bbase (se 5 (by rfl) ⟨252398, by rfl⟩ : syracuseStep 5384501 = 504797) (by norm_num)
theorem B1796413 : Blo 1594996 1796413 := bbase (se 3 (by rfl) ⟨336827, by rfl⟩ : syracuseStep 1796413 = 673655) (by norm_num)
theorem B2394437 : Blo 1594996 2394437 := bbase (se 4 (by rfl) ⟨224478, by rfl⟩ : syracuseStep 2394437 = 448957) (by norm_num)
theorem B4041029 : Blo 1594996 4041029 := bbase (se 4 (by rfl) ⟨378846, by rfl⟩ : syracuseStep 4041029 = 757693) (by norm_num)
theorem B3590477 : Blo 1594996 3590477 := bbase (se 3 (by rfl) ⟨673214, by rfl⟩ : syracuseStep 3590477 = 1346429) (by norm_num)
theorem B3639629 : Blo 1594996 3639629 := bbase (se 3 (by rfl) ⟨682430, by rfl⟩ : syracuseStep 3639629 = 1364861) (by norm_num)
theorem B2394461 : Blo 1594996 2394461 := bbase (se 3 (by rfl) ⟨448961, by rfl⟩ : syracuseStep 2394461 = 897923) (by norm_num)
theorem B1796449 : Blo 1594996 1796449 := bbase (se 2 (by rfl) ⟨673668, by rfl⟩ : syracuseStep 1796449 = 1347337) (by norm_num)
theorem B1845605 : Blo 1594996 1845605 := bbase (se 4 (by rfl) ⟨173025, by rfl⟩ : syracuseStep 1845605 = 346051) (by norm_num)
theorem B9087349 : Blo 1594996 9087349 := bbase (se 5 (by rfl) ⟨425969, by rfl⟩ : syracuseStep 9087349 = 851939) (by norm_num)
theorem B2394485 : Blo 1594996 2394485 := bbase (se 5 (by rfl) ⟨112241, by rfl⟩ : syracuseStep 2394485 = 224483) (by norm_num)
theorem B8079749 : Blo 1594996 8079749 := bbase (se 4 (by rfl) ⟨757476, by rfl⟩ : syracuseStep 8079749 = 1514953) (by norm_num)
theorem B1796485 : Blo 1594996 1796485 := bbase (se 4 (by rfl) ⟨168420, by rfl⟩ : syracuseStep 1796485 = 336841) (by norm_num)
theorem B2394509 : Blo 1594996 2394509 := bbase (se 3 (by rfl) ⟨448970, by rfl⟩ : syracuseStep 2394509 = 897941) (by norm_num)
theorem B3590549 : Blo 1594996 3590549 := bbase (se 6 (by rfl) ⟨84153, by rfl⟩ : syracuseStep 3590549 = 168307) (by norm_num)
theorem B2460061 : Blo 1594996 2460061 := bbase (se 3 (by rfl) ⟨461261, by rfl⟩ : syracuseStep 2460061 = 922523) (by norm_num)
theorem B2394533 : Blo 1594996 2394533 := bbase (se 4 (by rfl) ⟨224487, by rfl⟩ : syracuseStep 2394533 = 448975) (by norm_num)
theorem B1796521 : Blo 1594996 1796521 := bbase (se 2 (by rfl) ⟨673695, by rfl⟩ : syracuseStep 1796521 = 1347391) (by norm_num)
theorem B2075069 : Blo 1594996 2075069 := bbase (se 3 (by rfl) ⟨389075, by rfl⟩ : syracuseStep 2075069 = 778151) (by norm_num)
theorem B2394557 : Blo 1594996 2394557 := bbase (se 3 (by rfl) ⟨448979, by rfl⟩ : syracuseStep 2394557 = 897959) (by norm_num)
theorem B1796557 : Blo 1594996 1796557 := bbase (se 3 (by rfl) ⟨336854, by rfl⟩ : syracuseStep 1796557 = 673709) (by norm_num)
theorem B2394581 : Blo 1594996 2394581 := bbase (se 7 (by rfl) ⟨28061, by rfl⟩ : syracuseStep 2394581 = 56123) (by norm_num)
theorem B3590621 : Blo 1594996 3590621 := bbase (se 3 (by rfl) ⟨673241, by rfl⟩ : syracuseStep 3590621 = 1346483) (by norm_num)
theorem B2394605 : Blo 1594996 2394605 := bbase (se 3 (by rfl) ⟨448988, by rfl⟩ : syracuseStep 2394605 = 897977) (by norm_num)
theorem B1796593 : Blo 1594996 1796593 := bbase (se 2 (by rfl) ⟨673722, by rfl⟩ : syracuseStep 1796593 = 1347445) (by norm_num)
theorem B3885565 : Blo 1594996 3885565 := bbase (se 3 (by rfl) ⟨728543, by rfl⟩ : syracuseStep 3885565 = 1457087) (by norm_num)
theorem B2394629 : Blo 1594996 2394629 := bbase (se 4 (by rfl) ⟨224496, by rfl⟩ : syracuseStep 2394629 = 448993) (by norm_num)
theorem B2394653 : Blo 1594996 2394653 := bbase (se 3 (by rfl) ⟨448997, by rfl⟩ : syracuseStep 2394653 = 897995) (by norm_num)
theorem B3590693 : Blo 1594996 3590693 := bbase (se 4 (by rfl) ⟨336627, by rfl⟩ : syracuseStep 3590693 = 673255) (by norm_num)
theorem B2394677 : Blo 1594996 2394677 := bbase (se 5 (by rfl) ⟨112250, by rfl⟩ : syracuseStep 2394677 = 224501) (by norm_num)
theorem B2394701 : Blo 1594996 2394701 := bbase (se 3 (by rfl) ⟨449006, by rfl⟩ : syracuseStep 2394701 = 898013) (by norm_num)
theorem B1944157 : Blo 1594996 1944157 := bbase (se 3 (by rfl) ⟨364529, by rfl⟩ : syracuseStep 1944157 = 729059) (by norm_num)
theorem B3410525 : Blo 1594996 3410525 := bbase (se 3 (by rfl) ⟨639473, by rfl⟩ : syracuseStep 3410525 = 1278947) (by norm_num)
theorem B2394725 : Blo 1594996 2394725 := bbase (se 4 (by rfl) ⟨224505, by rfl⟩ : syracuseStep 2394725 = 449011) (by norm_num)
theorem B3590765 : Blo 1594996 3590765 := bbase (se 3 (by rfl) ⟨673268, by rfl⟩ : syracuseStep 3590765 = 1346537) (by norm_num)
theorem B2394749 : Blo 1594996 2394749 := bbase (se 3 (by rfl) ⟨449015, by rfl⟩ : syracuseStep 2394749 = 898031) (by norm_num)
theorem B2394773 : Blo 1594996 2394773 := bbase (se 6 (by rfl) ⟨56127, by rfl⟩ : syracuseStep 2394773 = 112255) (by norm_num)
theorem B4041373 : Blo 1594996 4041373 := bbase (se 3 (by rfl) ⟨757757, by rfl⟩ : syracuseStep 4041373 = 1515515) (by norm_num)
theorem B2394797 : Blo 1594996 2394797 := bbase (se 3 (by rfl) ⟨449024, by rfl⟩ : syracuseStep 2394797 = 898049) (by norm_num)
theorem B3590837 : Blo 1594996 3590837 := bbase (se 5 (by rfl) ⟨168320, by rfl⟩ : syracuseStep 3590837 = 336641) (by norm_num)
theorem B2394821 : Blo 1594996 2394821 := bbase (se 4 (by rfl) ⟨224514, by rfl⟩ : syracuseStep 2394821 = 449029) (by norm_num)
theorem B2394845 : Blo 1594996 2394845 := bbase (se 3 (by rfl) ⟨449033, by rfl⟩ : syracuseStep 2394845 = 898067) (by norm_num)
theorem B5384933 : Blo 1594996 5384933 := bbase (se 4 (by rfl) ⟨504837, by rfl⟩ : syracuseStep 5384933 = 1009675) (by norm_num)
theorem B2394869 : Blo 1594996 2394869 := bbase (se 5 (by rfl) ⟨112259, by rfl⟩ : syracuseStep 2394869 = 224519) (by norm_num)
theorem B3885821 : Blo 1594996 3885821 := bbase (se 3 (by rfl) ⟨728591, by rfl⟩ : syracuseStep 3885821 = 1457183) (by norm_num)
theorem B2271997 : Blo 1594996 2271997 := bbase (se 3 (by rfl) ⟨425999, by rfl⟩ : syracuseStep 2271997 = 851999) (by norm_num)
theorem B3590909 : Blo 1594996 3590909 := bbase (se 3 (by rfl) ⟨673295, by rfl⟩ : syracuseStep 3590909 = 1346591) (by norm_num)
theorem B2394893 : Blo 1594996 2394893 := bbase (se 3 (by rfl) ⟨449042, by rfl⟩ : syracuseStep 2394893 = 898085) (by norm_num)
theorem B4041485 : Blo 1594996 4041485 := bbase (se 3 (by rfl) ⟨757778, by rfl⟩ : syracuseStep 4041485 = 1515557) (by norm_num)
theorem B2394917 : Blo 1594996 2394917 := bbase (se 4 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 2394917 = 449047) (by norm_num)
theorem B3836717 : Blo 1594996 3836717 := bbase (se 3 (by rfl) ⟨719384, by rfl⟩ : syracuseStep 3836717 = 1438769) (by norm_num)
theorem B2304821 : Blo 1594996 2304821 := bbase (se 5 (by rfl) ⟨108038, by rfl⟩ : syracuseStep 2304821 = 216077) (by norm_num)
theorem B2394941 : Blo 1594996 2394941 := bbase (se 3 (by rfl) ⟨449051, by rfl⟩ : syracuseStep 2394941 = 898103) (by norm_num)
theorem B3590981 : Blo 1594996 3590981 := bbase (se 4 (by rfl) ⟨336654, by rfl⟩ : syracuseStep 3590981 = 673309) (by norm_num)
theorem B3640133 : Blo 1594996 3640133 := bbase (se 4 (by rfl) ⟨341262, by rfl⟩ : syracuseStep 3640133 = 682525) (by norm_num)
theorem B2394965 : Blo 1594996 2394965 := bbase (se 9 (by rfl) ⟨7016, by rfl⟩ : syracuseStep 2394965 = 14033) (by norm_num)
theorem B2394989 : Blo 1594996 2394989 := bbase (se 3 (by rfl) ⟨449060, by rfl⟩ : syracuseStep 2394989 = 898121) (by norm_num)
theorem B10226549 : Blo 1594996 10226549 := bbase (se 5 (by rfl) ⟨479369, by rfl⟩ : syracuseStep 10226549 = 958739) (by norm_num)
theorem B2395013 : Blo 1594996 2395013 := bbase (se 4 (by rfl) ⟨224532, by rfl⟩ : syracuseStep 2395013 = 449065) (by norm_num)
theorem B3591053 : Blo 1594996 3591053 := bbase (se 3 (by rfl) ⟨673322, by rfl⟩ : syracuseStep 3591053 = 1346645) (by norm_num)
theorem B2395037 : Blo 1594996 2395037 := bbase (se 3 (by rfl) ⟨449069, by rfl⟩ : syracuseStep 2395037 = 898139) (by norm_num)
theorem B2395061 : Blo 1594996 2395061 := bbase (se 5 (by rfl) ⟨112268, by rfl⟩ : syracuseStep 2395061 = 224537) (by norm_num)
theorem B12127157 : Blo 1594996 12127157 := bbase (se 5 (by rfl) ⟨568460, by rfl⟩ : syracuseStep 12127157 = 1136921) (by norm_num)
theorem B2157509 : Blo 1594996 2157509 := bbase (se 4 (by rfl) ⟨202266, by rfl⟩ : syracuseStep 2157509 = 404533) (by norm_num)
theorem B4041677 : Blo 1594996 4041677 := bbase (se 3 (by rfl) ⟨757814, by rfl⟩ : syracuseStep 4041677 = 1515629) (by norm_num)
theorem B2395085 : Blo 1594996 2395085 := bbase (se 3 (by rfl) ⟨449078, by rfl⟩ : syracuseStep 2395085 = 898157) (by norm_num)
theorem B3591125 : Blo 1594996 3591125 := bbase (se 7 (by rfl) ⟨42083, by rfl⟩ : syracuseStep 3591125 = 84167) (by norm_num)
theorem B2395109 : Blo 1594996 2395109 := bbase (se 4 (by rfl) ⟨224541, by rfl⟩ : syracuseStep 2395109 = 449083) (by norm_num)
theorem B3836917 : Blo 1594996 3836917 := bbase (se 5 (by rfl) ⟨179855, by rfl⟩ : syracuseStep 3836917 = 359711) (by norm_num)
theorem B2395133 : Blo 1594996 2395133 := bbase (se 3 (by rfl) ⟨449087, by rfl⟩ : syracuseStep 2395133 = 898175) (by norm_num)
theorem B2395157 : Blo 1594996 2395157 := bbase (se 6 (by rfl) ⟨56136, by rfl⟩ : syracuseStep 2395157 = 112273) (by norm_num)
theorem B3591197 : Blo 1594996 3591197 := bbase (se 3 (by rfl) ⟨673349, by rfl⟩ : syracuseStep 3591197 = 1346699) (by norm_num)
theorem B2395181 : Blo 1594996 2395181 := bbase (se 3 (by rfl) ⟨449096, by rfl⟩ : syracuseStep 2395181 = 898193) (by norm_num)
theorem B2395205 : Blo 1594996 2395205 := bbase (se 4 (by rfl) ⟨224550, by rfl⟩ : syracuseStep 2395205 = 449101) (by norm_num)
theorem B2395229 : Blo 1594996 2395229 := bbase (se 3 (by rfl) ⟨449105, by rfl⟩ : syracuseStep 2395229 = 898211) (by norm_num)
theorem B3591269 : Blo 1594996 3591269 := bbase (se 4 (by rfl) ⟨336681, by rfl⟩ : syracuseStep 3591269 = 673363) (by norm_num)
theorem B2395253 : Blo 1594996 2395253 := bbase (se 5 (by rfl) ⟨112277, by rfl⟩ : syracuseStep 2395253 = 224555) (by norm_num)
theorem B2395277 : Blo 1594996 2395277 := bbase (se 3 (by rfl) ⟨449114, by rfl⟩ : syracuseStep 2395277 = 898229) (by norm_num)
theorem B5385365 : Blo 1594996 5385365 := bbase (se 6 (by rfl) ⟨126219, by rfl⟩ : syracuseStep 5385365 = 252439) (by norm_num)
theorem B6057125 : Blo 1594996 6057125 := bbase (se 4 (by rfl) ⟨567855, by rfl⟩ : syracuseStep 6057125 = 1135711) (by norm_num)
theorem B2395301 : Blo 1594996 2395301 := bbase (se 4 (by rfl) ⟨224559, by rfl⟩ : syracuseStep 2395301 = 449119) (by norm_num)
theorem B3591341 : Blo 1594996 3591341 := bbase (se 3 (by rfl) ⟨673376, by rfl⟩ : syracuseStep 3591341 = 1346753) (by norm_num)
theorem B2395325 : Blo 1594996 2395325 := bbase (se 3 (by rfl) ⟨449123, by rfl⟩ : syracuseStep 2395325 = 898247) (by norm_num)
theorem B2395349 : Blo 1594996 2395349 := bbase (se 7 (by rfl) ⟨28070, by rfl⟩ : syracuseStep 2395349 = 56141) (by norm_num)
theorem B3370205 : Blo 1594996 3370205 := bbase (se 3 (by rfl) ⟨631913, by rfl⟩ : syracuseStep 3370205 = 1263827) (by norm_num)
theorem B2731229 : Blo 1594996 2731229 := bbase (se 3 (by rfl) ⟨512105, by rfl⟩ : syracuseStep 2731229 = 1024211) (by norm_num)
theorem B5115109 : Blo 1594996 5115109 := bbase (se 4 (by rfl) ⟨479541, by rfl⟩ : syracuseStep 5115109 = 959083) (by norm_num)
theorem B2395373 : Blo 1594996 2395373 := bbase (se 3 (by rfl) ⟨449132, by rfl⟩ : syracuseStep 2395373 = 898265) (by norm_num)
theorem B3591413 : Blo 1594996 3591413 := bbase (se 5 (by rfl) ⟨168347, by rfl⟩ : syracuseStep 3591413 = 336695) (by norm_num)
theorem B2395397 : Blo 1594996 2395397 := bbase (se 4 (by rfl) ⟨224568, by rfl⟩ : syracuseStep 2395397 = 449137) (by norm_num)
theorem B2395421 : Blo 1594996 2395421 := bbase (se 3 (by rfl) ⟨449141, by rfl⟩ : syracuseStep 2395421 = 898283) (by norm_num)
theorem B4042021 : Blo 1594996 4042021 := bbase (se 4 (by rfl) ⟨378939, by rfl⟩ : syracuseStep 4042021 = 757879) (by norm_num)
theorem B2395445 : Blo 1594996 2395445 := bbase (se 5 (by rfl) ⟨112286, by rfl⟩ : syracuseStep 2395445 = 224573) (by norm_num)
theorem B3591485 : Blo 1594996 3591485 := bbase (se 3 (by rfl) ⟨673403, by rfl⟩ : syracuseStep 3591485 = 1346807) (by norm_num)
theorem B2395469 : Blo 1594996 2395469 := bbase (se 3 (by rfl) ⟨449150, by rfl⟩ : syracuseStep 2395469 = 898301) (by norm_num)
theorem B12119381 : Blo 1594996 12119381 := bbase (se 11 (by rfl) ⟨8876, by rfl⟩ : syracuseStep 12119381 = 17753) (by norm_num)
theorem B2395493 : Blo 1594996 2395493 := bbase (se 4 (by rfl) ⟨224577, by rfl⟩ : syracuseStep 2395493 = 449155) (by norm_num)
theorem B2018677 : Blo 1594996 2018677 := bbase (se 5 (by rfl) ⟨94625, by rfl⟩ : syracuseStep 2018677 = 189251) (by norm_num)
theorem B3591557 : Blo 1594996 3591557 := bbase (se 4 (by rfl) ⟨336708, by rfl⟩ : syracuseStep 3591557 = 673417) (by norm_num)
theorem B4042133 : Blo 1594996 4042133 := bbase (se 6 (by rfl) ⟨94737, by rfl⟩ : syracuseStep 4042133 = 189475) (by norm_num)
theorem B6057413 : Blo 1594996 6057413 := bbase (se 4 (by rfl) ⟨567882, by rfl⟩ : syracuseStep 6057413 = 1135765) (by norm_num)
theorem B3591629 : Blo 1594996 3591629 := bbase (se 3 (by rfl) ⟨673430, by rfl⟩ : syracuseStep 3591629 = 1346861) (by norm_num)
theorem B2018773 : Blo 1594996 2018773 := bbase (se 7 (by rfl) ⟨23657, by rfl⟩ : syracuseStep 2018773 = 47315) (by norm_num)
theorem B6467077 : Blo 1594996 6467077 := bbase (se 4 (by rfl) ⟨606288, by rfl⟩ : syracuseStep 6467077 = 1212577) (by norm_num)
theorem B4312597 : Blo 1594996 4312597 := bbase (se 6 (by rfl) ⟨101076, by rfl⟩ : syracuseStep 4312597 = 202153) (by norm_num)
theorem B2272789 : Blo 1594996 2272789 := bbase (se 6 (by rfl) ⟨53268, by rfl⟩ : syracuseStep 2272789 = 106537) (by norm_num)
theorem B3591701 : Blo 1594996 3591701 := bbase (se 6 (by rfl) ⟨84180, by rfl⟩ : syracuseStep 3591701 = 168361) (by norm_num)
theorem B13635125 : Blo 1594996 13635125 := bbase (se 5 (by rfl) ⟨639146, by rfl⟩ : syracuseStep 13635125 = 1278293) (by norm_num)
theorem B5385797 : Blo 1594996 5385797 := bbase (se 4 (by rfl) ⟨504918, by rfl⟩ : syracuseStep 5385797 = 1009837) (by norm_num)
theorem B4042325 : Blo 1594996 4042325 := bbase (se 8 (by rfl) ⟨23685, by rfl⟩ : syracuseStep 4042325 = 47371) (by norm_num)
theorem B3591773 : Blo 1594996 3591773 := bbase (se 3 (by rfl) ⟨673457, by rfl⟩ : syracuseStep 3591773 = 1346915) (by norm_num)
theorem B2018945 : Blo 1594996 2018945 := bbase (se 2 (by rfl) ⟨757104, by rfl⟩ : syracuseStep 2018945 = 1514209) (by norm_num)
theorem B6819461 : Blo 1594996 6819461 := bbase (se 4 (by rfl) ⟨639324, by rfl⟩ : syracuseStep 6819461 = 1278649) (by norm_num)
theorem B8081045 : Blo 1594996 8081045 := bbase (se 6 (by rfl) ⟨189399, by rfl⟩ : syracuseStep 8081045 = 378799) (by norm_num)
theorem B3591845 : Blo 1594996 3591845 := bbase (se 4 (by rfl) ⟨336735, by rfl⟩ : syracuseStep 3591845 = 673471) (by norm_num)
theorem B13627061 : Blo 1594996 13627061 := bbase (se 5 (by rfl) ⟨638768, by rfl⟩ : syracuseStep 13627061 = 1277537) (by norm_num)
theorem B2019001 : Blo 1594996 2019001 := bbase (se 2 (by rfl) ⟨757125, by rfl⟩ : syracuseStep 2019001 = 1514251) (by norm_num)
theorem B4542149 : Blo 1594996 4542149 := bbase (se 4 (by rfl) ⟨425826, by rfl⟩ : syracuseStep 4542149 = 851653) (by norm_num)
theorem B25882325 : Blo 1594996 25882325 := bbase (se 7 (by rfl) ⟨303308, by rfl⟩ : syracuseStep 25882325 = 606617) (by norm_num)
theorem B3591917 : Blo 1594996 3591917 := bbase (se 3 (by rfl) ⟨673484, by rfl⟩ : syracuseStep 3591917 = 1346969) (by norm_num)
theorem B2019097 : Blo 1594996 2019097 := bbase (se 2 (by rfl) ⟨757161, by rfl⟩ : syracuseStep 2019097 = 1514323) (by norm_num)
theorem B3591989 : Blo 1594996 3591989 := bbase (se 5 (by rfl) ⟨168374, by rfl⟩ : syracuseStep 3591989 = 336749) (by norm_num)
theorem B2273125 : Blo 1594996 2273125 := bbase (se 4 (by rfl) ⟨213105, by rfl⟩ : syracuseStep 2273125 = 426211) (by norm_num)
theorem B3592061 : Blo 1594996 3592061 := bbase (se 3 (by rfl) ⟨673511, by rfl⟩ : syracuseStep 3592061 = 1347023) (by norm_num)
theorem B4542389 : Blo 1594996 4542389 := bbase (se 5 (by rfl) ⟨212924, by rfl⟩ : syracuseStep 4542389 = 425849) (by norm_num)
theorem B2019269 : Blo 1594996 2019269 := bbase (se 4 (by rfl) ⟨189306, by rfl⟩ : syracuseStep 2019269 = 378613) (by norm_num)
theorem B3592133 : Blo 1594996 3592133 := bbase (se 4 (by rfl) ⟨336762, by rfl⟩ : syracuseStep 3592133 = 673525) (by norm_num)
theorem B5386229 : Blo 1594996 5386229 := bbase (se 5 (by rfl) ⟨252479, by rfl⟩ : syracuseStep 5386229 = 504959) (by norm_num)
theorem B1617913 : Blo 1594996 1617913 := bbase (se 2 (by rfl) ⟨606717, by rfl⟩ : syracuseStep 1617913 = 1213435) (by norm_num)
theorem B2019325 : Blo 1594996 2019325 := bbase (se 3 (by rfl) ⟨378623, by rfl⟩ : syracuseStep 2019325 = 757247) (by norm_num)
theorem B3592205 : Blo 1594996 3592205 := bbase (se 3 (by rfl) ⟨673538, by rfl⟩ : syracuseStep 3592205 = 1347077) (by norm_num)
theorem B1617937 : Blo 1594996 1617937 := bbase (se 2 (by rfl) ⟨606726, by rfl⟩ : syracuseStep 1617937 = 1213453) (by norm_num)
theorem B2273341 : Blo 1594996 2273341 := bbase (se 3 (by rfl) ⟨426251, by rfl⟩ : syracuseStep 2273341 = 852503) (by norm_num)
theorem B3592277 : Blo 1594996 3592277 := bbase (se 8 (by rfl) ⟨21048, by rfl⟩ : syracuseStep 3592277 = 42097) (by norm_num)
theorem B2019421 : Blo 1594996 2019421 := bbase (se 3 (by rfl) ⟨378641, by rfl⟩ : syracuseStep 2019421 = 757283) (by norm_num)
theorem B4542581 : Blo 1594996 4542581 := bbase (se 5 (by rfl) ⟨212933, by rfl⟩ : syracuseStep 4542581 = 425867) (by norm_num)
theorem B3592349 : Blo 1594996 3592349 := bbase (se 3 (by rfl) ⟨673565, by rfl⟩ : syracuseStep 3592349 = 1347131) (by norm_num)
theorem B7671989 : Blo 1594996 7671989 := bbase (se 5 (by rfl) ⟨359624, by rfl⟩ : syracuseStep 7671989 = 719249) (by norm_num)
theorem B9703637 : Blo 1594996 9703637 := bbase (se 7 (by rfl) ⟨113714, by rfl⟩ : syracuseStep 9703637 = 227429) (by norm_num)
theorem B3592421 : Blo 1594996 3592421 := bbase (se 4 (by rfl) ⟨336789, by rfl⟩ : syracuseStep 3592421 = 673579) (by norm_num)
theorem B1618165 : Blo 1594996 1618165 := bbase (se 5 (by rfl) ⟨75851, by rfl⟩ : syracuseStep 1618165 = 151703) (by norm_num)
theorem B2019593 : Blo 1594996 2019593 := bbase (se 2 (by rfl) ⟨757347, by rfl⟩ : syracuseStep 2019593 = 1514695) (by norm_num)
theorem B3592493 : Blo 1594996 3592493 := bbase (se 3 (by rfl) ⟨673592, by rfl⟩ : syracuseStep 3592493 = 1347185) (by norm_num)
theorem B9089333 : Blo 1594996 9089333 := bbase (se 5 (by rfl) ⟨426062, by rfl⟩ : syracuseStep 9089333 = 852125) (by norm_num)
theorem B2019649 : Blo 1594996 2019649 := bbase (se 2 (by rfl) ⟨757368, by rfl⟩ : syracuseStep 2019649 = 1514737) (by norm_num)
theorem B3592565 : Blo 1594996 3592565 := bbase (se 5 (by rfl) ⟨168401, by rfl⟩ : syracuseStep 3592565 = 336803) (by norm_num)
theorem B18428309 : Blo 1594996 18428309 := bbase (se 6 (by rfl) ⟨431913, by rfl⟩ : syracuseStep 18428309 = 863827) (by norm_num)
theorem B3453341 : Blo 1594996 3453341 := bbase (se 3 (by rfl) ⟨647501, by rfl⟩ : syracuseStep 3453341 = 1295003) (by norm_num)
theorem B2019745 : Blo 1594996 2019745 := bbase (se 2 (by rfl) ⟨757404, by rfl⟩ : syracuseStep 2019745 = 1514809) (by norm_num)
theorem B5386661 : Blo 1594996 5386661 := bbase (se 4 (by rfl) ⟨504999, by rfl⟩ : syracuseStep 5386661 = 1009999) (by norm_num)
theorem B2273717 : Blo 1594996 2273717 := bbase (se 5 (by rfl) ⟨106580, by rfl⟩ : syracuseStep 2273717 = 213161) (by norm_num)
theorem B3592637 : Blo 1594996 3592637 := bbase (se 3 (by rfl) ⟨673619, by rfl⟩ : syracuseStep 3592637 = 1347239) (by norm_num)
theorem B27652565 : Blo 1594996 27652565 := bbase (se 7 (by rfl) ⟨324053, by rfl⟩ : syracuseStep 27652565 = 648107) (by norm_num)
theorem B2691589 : Blo 1594996 2691589 := bbase (se 4 (by rfl) ⟨252336, by rfl⟩ : syracuseStep 2691589 = 504673) (by norm_num)
theorem B3592709 : Blo 1594996 3592709 := bbase (se 4 (by rfl) ⟨336816, by rfl⟩ : syracuseStep 3592709 = 673633) (by norm_num)
theorem B7672373 : Blo 1594996 7672373 := bbase (se 5 (by rfl) ⟨359642, by rfl⟩ : syracuseStep 7672373 = 719285) (by norm_num)
theorem B2019917 : Blo 1594996 2019917 := bbase (se 3 (by rfl) ⟨378734, by rfl⟩ : syracuseStep 2019917 = 757469) (by norm_num)
theorem B3592781 : Blo 1594996 3592781 := bbase (se 3 (by rfl) ⟨673646, by rfl⟩ : syracuseStep 3592781 = 1347293) (by norm_num)
theorem B2691677 : Blo 1594996 2691677 := bbase (se 3 (by rfl) ⟨504689, by rfl⟩ : syracuseStep 2691677 = 1009379) (by norm_num)
theorem B6058597 : Blo 1594996 6058597 := bbase (se 4 (by rfl) ⟨567993, by rfl⟩ : syracuseStep 6058597 = 1135987) (by norm_num)
theorem B6820469 : Blo 1594996 6820469 := bbase (se 5 (by rfl) ⟨319709, by rfl⟩ : syracuseStep 6820469 = 639419) (by norm_num)
theorem B2019973 : Blo 1594996 2019973 := bbase (se 4 (by rfl) ⟨189372, by rfl⟩ : syracuseStep 2019973 = 378745) (by norm_num)
theorem B3592853 : Blo 1594996 3592853 := bbase (se 6 (by rfl) ⟨84207, by rfl⟩ : syracuseStep 3592853 = 168415) (by norm_num)
theorem B4149949 : Blo 1594996 4149949 := bbase (se 3 (by rfl) ⟨778115, by rfl⟩ : syracuseStep 4149949 = 1556231) (by norm_num)
theorem B2691805 : Blo 1594996 2691805 := bbase (se 3 (by rfl) ⟨504713, by rfl⟩ : syracuseStep 2691805 = 1009427) (by norm_num)
theorem B3592925 : Blo 1594996 3592925 := bbase (se 3 (by rfl) ⟨673673, by rfl⟩ : syracuseStep 3592925 = 1347347) (by norm_num)
theorem B2020069 : Blo 1594996 2020069 := bbase (se 4 (by rfl) ⟨189381, by rfl⟩ : syracuseStep 2020069 = 378763) (by norm_num)
theorem B3592997 : Blo 1594996 3592997 := bbase (se 4 (by rfl) ⟨336843, by rfl⟩ : syracuseStep 3592997 = 673687) (by norm_num)
theorem B2691893 : Blo 1594996 2691893 := bbase (se 5 (by rfl) ⟨126182, by rfl⟩ : syracuseStep 2691893 = 252365) (by norm_num)
theorem B5387093 : Blo 1594996 5387093 := bbase (se 9 (by rfl) ⟨15782, by rfl⟩ : syracuseStep 5387093 = 31565) (by norm_num)
theorem B3593069 : Blo 1594996 3593069 := bbase (se 3 (by rfl) ⟨673700, by rfl⟩ : syracuseStep 3593069 = 1347401) (by norm_num)
theorem B3642221 : Blo 1594996 3642221 := bbase (se 3 (by rfl) ⟨682916, by rfl⟩ : syracuseStep 3642221 = 1365833) (by norm_num)
theorem B2020241 : Blo 1594996 2020241 := bbase (se 2 (by rfl) ⟨757590, by rfl⟩ : syracuseStep 2020241 = 1515181) (by norm_num)
theorem B6058901 : Blo 1594996 6058901 := bbase (se 6 (by rfl) ⟨142005, by rfl⟩ : syracuseStep 6058901 = 284011) (by norm_num)
theorem B8082341 : Blo 1594996 8082341 := bbase (se 4 (by rfl) ⟨757719, by rfl⟩ : syracuseStep 8082341 = 1515439) (by norm_num)
theorem B2692021 : Blo 1594996 2692021 := bbase (se 5 (by rfl) ⟨126188, by rfl⟩ : syracuseStep 2692021 = 252377) (by norm_num)
theorem B3593141 : Blo 1594996 3593141 := bbase (se 5 (by rfl) ⟨168428, by rfl⟩ : syracuseStep 3593141 = 336857) (by norm_num)
theorem B2020297 : Blo 1594996 2020297 := bbase (se 2 (by rfl) ⟨757611, by rfl⟩ : syracuseStep 2020297 = 1515223) (by norm_num)
theorem B3593213 : Blo 1594996 3593213 := bbase (se 3 (by rfl) ⟨673727, by rfl⟩ : syracuseStep 3593213 = 1347455) (by norm_num)
theorem B2692109 : Blo 1594996 2692109 := bbase (se 3 (by rfl) ⟨504770, by rfl⟩ : syracuseStep 2692109 = 1009541) (by norm_num)
theorem B2020393 : Blo 1594996 2020393 := bbase (se 2 (by rfl) ⟨757647, by rfl⟩ : syracuseStep 2020393 = 1515295) (by norm_num)
theorem B4543573 : Blo 1594996 4543573 := bbase (se 8 (by rfl) ⟨26622, by rfl⟩ : syracuseStep 4543573 = 53245) (by norm_num)
theorem B2692237 : Blo 1594996 2692237 := bbase (se 3 (by rfl) ⟨504794, by rfl⟩ : syracuseStep 2692237 = 1009589) (by norm_num)
theorem B2020565 : Blo 1594996 2020565 := bbase (se 7 (by rfl) ⟨23678, by rfl⟩ : syracuseStep 2020565 = 47357) (by norm_num)
theorem B2692325 : Blo 1594996 2692325 := bbase (se 4 (by rfl) ⟨252405, by rfl⟩ : syracuseStep 2692325 = 504811) (by norm_num)
theorem B3028205 : Blo 1594996 3028205 := bbase (se 3 (by rfl) ⟨567788, by rfl⟩ : syracuseStep 3028205 = 1135577) (by norm_num)
theorem B5387525 : Blo 1594996 5387525 := bbase (se 4 (by rfl) ⟨505080, by rfl⟩ : syracuseStep 5387525 = 1010161) (by norm_num)
theorem B2020621 : Blo 1594996 2020621 := bbase (se 3 (by rfl) ⟨378866, by rfl⟩ : syracuseStep 2020621 = 757733) (by norm_num)
theorem B15365429 : Blo 1594996 15365429 := bbase (se 5 (by rfl) ⟨720254, by rfl⟩ : syracuseStep 15365429 = 1440509) (by norm_num)
theorem B4150613 : Blo 1594996 4150613 := bbase (se 17 (by rfl) ⟨47, by rfl⟩ : syracuseStep 4150613 = 95) (by norm_num)
theorem B3888469 : Blo 1594996 3888469 := bbase (se 17 (by rfl) ⟨44, by rfl⟩ : syracuseStep 3888469 = 89) (by norm_num)
theorem B2692453 : Blo 1594996 2692453 := bbase (se 4 (by rfl) ⟨252417, by rfl⟩ : syracuseStep 2692453 = 504835) (by norm_num)
theorem B2020717 : Blo 1594996 2020717 := bbase (se 3 (by rfl) ⟨378884, by rfl⟩ : syracuseStep 2020717 = 757769) (by norm_num)
theorem B3028357 : Blo 1594996 3028357 := bbase (se 4 (by rfl) ⟨283908, by rfl⟩ : syracuseStep 3028357 = 567817) (by norm_num)
theorem B2692541 : Blo 1594996 2692541 := bbase (se 3 (by rfl) ⟨504851, by rfl⟩ : syracuseStep 2692541 = 1009703) (by norm_num)
theorem B6813173 : Blo 1594996 6813173 := bbase (se 5 (by rfl) ⟨319367, by rfl⟩ : syracuseStep 6813173 = 638735) (by norm_num)
theorem B2020889 : Blo 1594996 2020889 := bbase (se 2 (by rfl) ⟨757833, by rfl⟩ : syracuseStep 2020889 = 1515667) (by norm_num)
theorem B2692669 : Blo 1594996 2692669 := bbase (se 3 (by rfl) ⟨504875, by rfl⟩ : syracuseStep 2692669 = 1009751) (by norm_num)
theorem B2020945 : Blo 1594996 2020945 := bbase (se 2 (by rfl) ⟨757854, by rfl⟩ : syracuseStep 2020945 = 1515709) (by norm_num)
theorem B2692757 : Blo 1594996 2692757 := bbase (se 6 (by rfl) ⟨63111, by rfl⟩ : syracuseStep 2692757 = 126223) (by norm_num)
theorem B2021041 : Blo 1594996 2021041 := bbase (se 2 (by rfl) ⟨757890, by rfl⟩ : syracuseStep 2021041 = 1515781) (by norm_num)
theorem B3028661 : Blo 1594996 3028661 := bbase (se 5 (by rfl) ⟨141968, by rfl⟩ : syracuseStep 3028661 = 283937) (by norm_num)
theorem B5387957 : Blo 1594996 5387957 := bbase (se 5 (by rfl) ⟨252560, by rfl⟩ : syracuseStep 5387957 = 505121) (by norm_num)
theorem B2692885 : Blo 1594996 2692885 := bbase (se 6 (by rfl) ⟨63114, by rfl⟩ : syracuseStep 2692885 = 126229) (by norm_num)
theorem B3323701 : Blo 1594996 3323701 := bbase (se 5 (by rfl) ⟨155798, by rfl⟩ : syracuseStep 3323701 = 311597) (by norm_num)
theorem B2692973 : Blo 1594996 2692973 := bbase (se 3 (by rfl) ⟨504932, by rfl⟩ : syracuseStep 2692973 = 1009865) (by norm_num)
theorem B4855685 : Blo 1594996 4855685 := bbase (se 4 (by rfl) ⟨455220, by rfl⟩ : syracuseStep 4855685 = 910441) (by norm_num)
theorem B12285845 : Blo 1594996 12285845 := bbase (se 6 (by rfl) ⟨287949, by rfl⟩ : syracuseStep 12285845 = 575899) (by norm_num)
theorem B39376853 : Blo 1594996 39376853 := bbase (se 7 (by rfl) ⟨461447, by rfl⟩ : syracuseStep 39376853 = 922895) (by norm_num)
theorem B2693101 : Blo 1594996 2693101 := bbase (se 3 (by rfl) ⟨504956, by rfl⟩ : syracuseStep 2693101 = 1009913) (by norm_num)
theorem B2693189 : Blo 1594996 2693189 := bbase (se 4 (by rfl) ⟨252486, by rfl⟩ : syracuseStep 2693189 = 504973) (by norm_num)
theorem B5388389 : Blo 1594996 5388389 := bbase (se 4 (by rfl) ⟨505161, by rfl⟩ : syracuseStep 5388389 = 1010323) (by norm_num)
theorem B4544677 : Blo 1594996 4544677 := bbase (se 4 (by rfl) ⟨426063, by rfl⟩ : syracuseStep 4544677 = 852127) (by norm_num)
theorem B8083637 : Blo 1594996 8083637 := bbase (se 5 (by rfl) ⟨378920, by rfl⟩ : syracuseStep 8083637 = 757841) (by norm_num)
theorem B2693317 : Blo 1594996 2693317 := bbase (se 4 (by rfl) ⟨252498, by rfl⟩ : syracuseStep 2693317 = 504997) (by norm_num)
theorem B2693405 : Blo 1594996 2693405 := bbase (se 3 (by rfl) ⟨505013, by rfl⟩ : syracuseStep 2693405 = 1010027) (by norm_num)
theorem B2046265 : Blo 1594996 2046265 := bbase (se 2 (by rfl) ⟨767349, by rfl⟩ : syracuseStep 2046265 = 1534699) (by norm_num)
theorem B8624501 : Blo 1594996 8624501 := bbase (se 5 (by rfl) ⟨404273, by rfl⟩ : syracuseStep 8624501 = 808547) (by norm_num)
theorem B2693533 : Blo 1594996 2693533 := bbase (se 3 (by rfl) ⟨505037, by rfl⟩ : syracuseStep 2693533 = 1010075) (by norm_num)
theorem B3029413 : Blo 1594996 3029413 := bbase (se 4 (by rfl) ⟨284007, by rfl⟩ : syracuseStep 3029413 = 568015) (by norm_num)
theorem B9091541 : Blo 1594996 9091541 := bbase (se 7 (by rfl) ⟨106541, by rfl⟩ : syracuseStep 9091541 = 213083) (by norm_num)
theorem B2103769 : Blo 1594996 2103769 := bbase (se 2 (by rfl) ⟨788913, by rfl⟩ : syracuseStep 2103769 = 1577827) (by norm_num)
theorem B2693621 : Blo 1594996 2693621 := bbase (se 5 (by rfl) ⟨126263, by rfl⟩ : syracuseStep 2693621 = 252527) (by norm_num)
theorem B5388821 : Blo 1594996 5388821 := bbase (se 6 (by rfl) ⟨126300, by rfl⟩ : syracuseStep 5388821 = 252601) (by norm_num)
theorem B3029557 : Blo 1594996 3029557 := bbase (se 5 (by rfl) ⟨142010, by rfl⟩ : syracuseStep 3029557 = 284021) (by norm_num)
theorem B8075861 : Blo 1594996 8075861 := bbase (se 8 (by rfl) ⟨47319, by rfl⟩ : syracuseStep 8075861 = 94639) (by norm_num)
theorem B2693749 : Blo 1594996 2693749 := bbase (se 5 (by rfl) ⟨126269, by rfl⟩ : syracuseStep 2693749 = 252539) (by norm_num)
theorem B2046605 : Blo 1594996 2046605 := bbase (se 3 (by rfl) ⟨383738, by rfl⟩ : syracuseStep 2046605 = 767477) (by norm_num)
theorem B10230421 : Blo 1594996 10230421 := bbase (se 6 (by rfl) ⟨239775, by rfl⟩ : syracuseStep 10230421 = 479551) (by norm_num)
theorem B2693837 : Blo 1594996 2693837 := bbase (se 3 (by rfl) ⟨505094, by rfl⟩ : syracuseStep 2693837 = 1010189) (by norm_num)
theorem B3029717 : Blo 1594996 3029717 := bbase (se 7 (by rfl) ⟨35504, by rfl⟩ : syracuseStep 3029717 = 71009) (by norm_num)
theorem B2046713 : Blo 1594996 2046713 := bbase (se 2 (by rfl) ⟨767517, by rfl⟩ : syracuseStep 2046713 = 1535035) (by norm_num)
theorem B8190725 : Blo 1594996 8190725 := bbase (se 4 (by rfl) ⟨767880, by rfl⟩ : syracuseStep 8190725 = 1535761) (by norm_num)
theorem B2693965 : Blo 1594996 2693965 := bbase (se 3 (by rfl) ⟨505118, by rfl⟩ : syracuseStep 2693965 = 1010237) (by norm_num)
theorem B3029861 : Blo 1594996 3029861 := bbase (se 4 (by rfl) ⟨284049, by rfl⟩ : syracuseStep 3029861 = 568099) (by norm_num)
theorem B4037485 : Blo 1594996 4037485 := bbase (se 3 (by rfl) ⟨757028, by rfl⟩ : syracuseStep 4037485 = 1514057) (by norm_num)
theorem B2694053 : Blo 1594996 2694053 := bbase (se 4 (by rfl) ⟨252567, by rfl⟩ : syracuseStep 2694053 = 505135) (by norm_num)
theorem B5389253 : Blo 1594996 5389253 := bbase (se 4 (by rfl) ⟨505242, by rfl⟩ : syracuseStep 5389253 = 1010485) (by norm_num)
theorem B6061013 : Blo 1594996 6061013 := bbase (se 7 (by rfl) ⟨71027, by rfl⟩ : syracuseStep 6061013 = 142055) (by norm_num)
theorem B4037597 : Blo 1594996 4037597 := bbase (se 3 (by rfl) ⟨757049, by rfl⟩ : syracuseStep 4037597 = 1514099) (by norm_num)
theorem B1727525 : Blo 1594996 1727525 := bbase (se 4 (by rfl) ⟨161955, by rfl⟩ : syracuseStep 1727525 = 323911) (by norm_num)
theorem B2694181 : Blo 1594996 2694181 := bbase (se 4 (by rfl) ⟨252579, by rfl⟩ : syracuseStep 2694181 = 505159) (by norm_num)
theorem B2554997 : Blo 1594996 2554997 := bbase (se 5 (by rfl) ⟨119765, by rfl⟩ : syracuseStep 2554997 = 239531) (by norm_num)
theorem B3832957 : Blo 1594996 3832957 := bbase (se 3 (by rfl) ⟨718679, by rfl⟩ : syracuseStep 3832957 = 1437359) (by norm_num)
theorem B2694269 : Blo 1594996 2694269 := bbase (se 3 (by rfl) ⟨505175, by rfl⟩ : syracuseStep 2694269 = 1010351) (by norm_num)
theorem B3030149 : Blo 1594996 3030149 := bbase (se 4 (by rfl) ⟨284076, by rfl⟩ : syracuseStep 3030149 = 568153) (by norm_num)
theorem B3406997 : Blo 1594996 3406997 := bbase (se 6 (by rfl) ⟨79851, by rfl⟩ : syracuseStep 3406997 = 159703) (by norm_num)
theorem B4037789 : Blo 1594996 4037789 := bbase (se 3 (by rfl) ⟨757085, by rfl⟩ : syracuseStep 4037789 = 1514171) (by norm_num)
theorem B6061301 : Blo 1594996 6061301 := bbase (se 5 (by rfl) ⟨284123, by rfl⟩ : syracuseStep 6061301 = 568247) (by norm_num)
theorem B2694397 : Blo 1594996 2694397 := bbase (se 3 (by rfl) ⟨505199, by rfl⟩ : syracuseStep 2694397 = 1010399) (by norm_num)
theorem B3030301 : Blo 1594996 3030301 := bbase (se 3 (by rfl) ⟨568181, by rfl⟩ : syracuseStep 3030301 = 1136363) (by norm_num)
theorem B3407141 : Blo 1594996 3407141 := bbase (se 4 (by rfl) ⟨319419, by rfl⟩ : syracuseStep 3407141 = 638839) (by norm_num)
theorem B2694485 : Blo 1594996 2694485 := bbase (se 11 (by rfl) ⟨1973, by rfl⟩ : syracuseStep 2694485 = 3947) (by norm_num)
theorem B3833189 : Blo 1594996 3833189 := bbase (se 4 (by rfl) ⟨359361, by rfl⟩ : syracuseStep 3833189 = 718723) (by norm_num)
theorem B5389685 : Blo 1594996 5389685 := bbase (se 5 (by rfl) ⟨252641, by rfl⟩ : syracuseStep 5389685 = 505283) (by norm_num)
theorem B4095397 : Blo 1594996 4095397 := bbase (se 4 (by rfl) ⟨383943, by rfl⟩ : syracuseStep 4095397 = 767887) (by norm_num)
theorem B2694613 : Blo 1594996 2694613 := bbase (se 7 (by rfl) ⟨31577, by rfl⟩ : syracuseStep 2694613 = 63155) (by norm_num)
theorem B4038133 : Blo 1594996 4038133 := bbase (se 5 (by rfl) ⟨189287, by rfl⟩ : syracuseStep 4038133 = 378575) (by norm_num)
theorem B3833333 : Blo 1594996 3833333 := bbase (se 5 (by rfl) ⟨179687, by rfl⟩ : syracuseStep 3833333 = 359375) (by norm_num)
theorem B3833381 : Blo 1594996 3833381 := bbase (se 4 (by rfl) ⟨359379, by rfl⟩ : syracuseStep 3833381 = 718759) (by norm_num)
theorem B2694701 : Blo 1594996 2694701 := bbase (se 3 (by rfl) ⟨505256, by rfl⟩ : syracuseStep 2694701 = 1010513) (by norm_num)
theorem B1703477 : Blo 1594996 1703477 := bbase (se 5 (by rfl) ⟨79850, by rfl⟩ : syracuseStep 1703477 = 159701) (by norm_num)
theorem B3030605 : Blo 1594996 3030605 := bbase (se 3 (by rfl) ⟨568238, by rfl⟩ : syracuseStep 3030605 = 1136477) (by norm_num)
theorem B4038245 : Blo 1594996 4038245 := bbase (se 4 (by rfl) ⟨378585, by rfl⟩ : syracuseStep 4038245 = 757171) (by norm_num)
theorem B5111429 : Blo 1594996 5111429 := bbase (se 4 (by rfl) ⟨479196, by rfl⟩ : syracuseStep 5111429 = 958393) (by norm_num)
theorem B4546181 : Blo 1594996 4546181 := bbase (se 4 (by rfl) ⟨426204, by rfl⟩ : syracuseStep 4546181 = 852409) (by norm_num)
theorem B3407501 : Blo 1594996 3407501 := bbase (se 3 (by rfl) ⟨638906, by rfl⟩ : syracuseStep 3407501 = 1277813) (by norm_num)
theorem B2694829 : Blo 1594996 2694829 := bbase (se 3 (by rfl) ⟨505280, by rfl⟩ : syracuseStep 2694829 = 1010561) (by norm_num)
theorem B2694917 : Blo 1594996 2694917 := bbase (se 4 (by rfl) ⟨252648, by rfl⟩ : syracuseStep 2694917 = 505297) (by norm_num)
theorem B4038437 : Blo 1594996 4038437 := bbase (se 4 (by rfl) ⟨378603, by rfl⟩ : syracuseStep 4038437 = 757207) (by norm_num)
theorem B7282469 : Blo 1594996 7282469 := bbase (se 4 (by rfl) ⟨682731, by rfl⟩ : syracuseStep 7282469 = 1365463) (by norm_num)
theorem B8625973 : Blo 1594996 8625973 := bbase (se 5 (by rfl) ⟨404342, by rfl⟩ : syracuseStep 8625973 = 808685) (by norm_num)
theorem B3833669 : Blo 1594996 3833669 := bbase (se 4 (by rfl) ⟨359406, by rfl⟩ : syracuseStep 3833669 = 718813) (by norm_num)
theorem B20455253 : Blo 1594996 20455253 := bbase (se 9 (by rfl) ⟨59927, by rfl⟩ : syracuseStep 20455253 = 119855) (by norm_num)
theorem B8077157 : Blo 1594996 8077157 := bbase (se 4 (by rfl) ⟨757233, by rfl⟩ : syracuseStep 8077157 = 1514467) (by norm_num)
theorem B2555869 : Blo 1594996 2555869 := bbase (se 3 (by rfl) ⟨479225, by rfl⟩ : syracuseStep 2555869 = 958451) (by norm_num)
theorem B1703921 : Blo 1594996 1703921 := bbase (se 2 (by rfl) ⟨638970, by rfl⟩ : syracuseStep 1703921 = 1277941) (by norm_num)
theorem B2875381 : Blo 1594996 2875381 := bbase (se 5 (by rfl) ⟨134783, by rfl⟩ : syracuseStep 2875381 = 269567) (by norm_num)
theorem B87367733 : Blo 1594996 87367733 := bstep (se 5 (by rfl) ⟨4095362, by rfl⟩ : syracuseStep 87367733 = 8190725) B8190725
theorem B4546637 : Blo 1594996 4546637 := bstep (se 3 (by rfl) ⟨852494, by rfl⟩ : syracuseStep 4546637 = 1704989) B1704989
theorem B3031121 : Blo 1594996 3031121 := bstep (se 2 (by rfl) ⟨1136670, by rfl⟩ : syracuseStep 3031121 = 2273341) B2273341
theorem B4546705 : Blo 1594996 4546705 := bstep (se 2 (by rfl) ⟨1705014, by rfl⟩ : syracuseStep 4546705 = 3410029) B3410029
theorem B1704083 : Blo 1594996 1704083 := bstep (se 1 (by rfl) ⟨1278062, by rfl⟩ : syracuseStep 1704083 = 2556125) B2556125
theorem B13631813 : Blo 1594996 13631813 := bstep (se 4 (by rfl) ⟨1277982, by rfl⟩ : syracuseStep 13631813 = 2555965) B2555965
theorem B7668067 : Blo 1594996 7668067 := bstep (se 1 (by rfl) ⟨5751050, by rfl⟩ : syracuseStep 7668067 = 11502101) B11502101
theorem B3408227 : Blo 1594996 3408227 := bstep (se 1 (by rfl) ⟨2556170, by rfl⟩ : syracuseStep 3408227 = 5112341) B5112341
theorem B5112173 : Blo 1594996 5112173 := bstep (se 3 (by rfl) ⟨958532, by rfl⟩ : syracuseStep 5112173 = 1917065) B1917065
theorem B1794451 : Blo 1594996 1794451 := bstep (se 1 (by rfl) ⟨1345838, by rfl⟩ : syracuseStep 1794451 = 2691677) B2691677
theorem B4546979 : Blo 1594996 4546979 := bstep (se 1 (by rfl) ⟨3410234, by rfl⟩ : syracuseStep 4546979 = 6820469) B6820469
theorem B2392499 : Blo 1594996 2392499 := bstep (se 1 (by rfl) ⟨1794374, by rfl⟩ : syracuseStep 2392499 = 3588749) B3588749
theorem B2392529 : Blo 1594996 2392529 := bstep (se 2 (by rfl) ⟨897198, by rfl⟩ : syracuseStep 2392529 = 1794397) B1794397
theorem B2425313 : Blo 1594996 2425313 := bstep (se 2 (by rfl) ⟨909492, by rfl⟩ : syracuseStep 2425313 = 1818985) B1818985
theorem B2392547 : Blo 1594996 2392547 := bstep (se 1 (by rfl) ⟨1794410, by rfl⟩ : syracuseStep 2392547 = 3588821) B3588821
theorem B12116465 : Blo 1594996 12116465 := bstep (se 2 (by rfl) ⟨4543674, by rfl⟩ : syracuseStep 12116465 = 9087349) B9087349
theorem B2392577 : Blo 1594996 2392577 := bstep (se 2 (by rfl) ⟨897216, by rfl⟩ : syracuseStep 2392577 = 1794433) B1794433
theorem B2392595 : Blo 1594996 2392595 := bstep (se 1 (by rfl) ⟨1794446, by rfl⟩ : syracuseStep 2392595 = 3588893) B3588893
theorem B1794595 : Blo 1594996 1794595 := bstep (se 1 (by rfl) ⟨1345946, by rfl⟩ : syracuseStep 1794595 = 2691893) B2691893
theorem B2392625 : Blo 1594996 2392625 := bstep (se 2 (by rfl) ⟨897234, by rfl⟩ : syracuseStep 2392625 = 1794469) B1794469
theorem B4039217 : Blo 1594996 4039217 := bstep (se 2 (by rfl) ⟨1514706, by rfl⟩ : syracuseStep 4039217 = 3029413) B3029413
theorem B2392643 : Blo 1594996 2392643 := bstep (se 1 (by rfl) ⟨1794482, by rfl⟩ : syracuseStep 2392643 = 3588965) B3588965
theorem B8987213 : Blo 1594996 8987213 := bstep (se 3 (by rfl) ⟨1685102, by rfl⟩ : syracuseStep 8987213 = 3370205) B3370205
theorem B2556497 : Blo 1594996 2556497 := bstep (se 2 (by rfl) ⟨958686, by rfl⟩ : syracuseStep 2556497 = 1917373) B1917373
theorem B2392673 : Blo 1594996 2392673 := bstep (se 2 (by rfl) ⟨897252, by rfl⟩ : syracuseStep 2392673 = 1794505) B1794505
theorem B4039267 : Blo 1594996 4039267 := bstep (se 1 (by rfl) ⟨3029450, by rfl⟩ : syracuseStep 4039267 = 6058901) B6058901
theorem B2392691 : Blo 1594996 2392691 := bstep (se 1 (by rfl) ⟨1794518, by rfl⟩ : syracuseStep 2392691 = 3589037) B3589037
theorem B2392721 : Blo 1594996 2392721 := bstep (se 2 (by rfl) ⟨897270, by rfl⟩ : syracuseStep 2392721 = 1794541) B1794541
theorem B2392739 : Blo 1594996 2392739 := bstep (se 1 (by rfl) ⟨1794554, by rfl⟩ : syracuseStep 2392739 = 3589109) B3589109
theorem B2425507 : Blo 1594996 2425507 := bstep (se 1 (by rfl) ⟨1819130, by rfl⟩ : syracuseStep 2425507 = 3638261) B3638261
theorem B3588785 : Blo 1594996 3588785 := bstep (se 2 (by rfl) ⟨1345794, by rfl⟩ : syracuseStep 3588785 = 2691589) B2691589
theorem B1794739 : Blo 1594996 1794739 := bstep (se 1 (by rfl) ⟨1346054, by rfl⟩ : syracuseStep 1794739 = 2692109) B2692109
theorem B2392769 : Blo 1594996 2392769 := bstep (se 2 (by rfl) ⟨897288, by rfl⟩ : syracuseStep 2392769 = 1794577) B1794577
theorem B3588803 : Blo 1594996 3588803 := bstep (se 1 (by rfl) ⟨2691602, by rfl⟩ : syracuseStep 3588803 = 5383205) B5383205
theorem B2392787 : Blo 1594996 2392787 := bstep (se 1 (by rfl) ⟨1794590, by rfl⟩ : syracuseStep 2392787 = 3589181) B3589181
theorem B2392817 : Blo 1594996 2392817 := bstep (se 2 (by rfl) ⟨897306, by rfl⟩ : syracuseStep 2392817 = 1794613) B1794613
theorem B4039409 : Blo 1594996 4039409 := bstep (se 2 (by rfl) ⟨1514778, by rfl⟩ : syracuseStep 4039409 = 3029557) B3029557
theorem B2392835 : Blo 1594996 2392835 := bstep (se 1 (by rfl) ⟨1794626, by rfl⟩ : syracuseStep 2392835 = 3589253) B3589253
theorem B9085709 : Blo 1594996 9085709 := bstep (se 3 (by rfl) ⟨1703570, by rfl⟩ : syracuseStep 9085709 = 3407141) B3407141
theorem B2392865 : Blo 1594996 2392865 := bstep (se 2 (by rfl) ⟨897324, by rfl⟩ : syracuseStep 2392865 = 1794649) B1794649
theorem B8078129 : Blo 1594996 8078129 := bstep (se 2 (by rfl) ⟨3029298, by rfl⟩ : syracuseStep 8078129 = 6058597) B6058597
theorem B2392883 : Blo 1594996 2392883 := bstep (se 1 (by rfl) ⟨1794662, by rfl⟩ : syracuseStep 2392883 = 3589325) B3589325
theorem B1794883 : Blo 1594996 1794883 := bstep (se 1 (by rfl) ⟨1346162, by rfl⟩ : syracuseStep 1794883 = 2692325) B2692325
theorem B2392913 : Blo 1594996 2392913 := bstep (se 2 (by rfl) ⟨897342, by rfl⟩ : syracuseStep 2392913 = 1794685) B1794685
theorem B2392931 : Blo 1594996 2392931 := bstep (se 1 (by rfl) ⟨1794698, by rfl⟩ : syracuseStep 2392931 = 3589397) B3589397
theorem B13640561 : Blo 1594996 13640561 := bstep (se 2 (by rfl) ⟨5115210, by rfl⟩ : syracuseStep 13640561 = 10230421) B10230421
theorem B2392961 : Blo 1594996 2392961 := bstep (se 2 (by rfl) ⟨897360, by rfl⟩ : syracuseStep 2392961 = 1794721) B1794721
theorem B1704835 : Blo 1594996 1704835 := bstep (se 1 (by rfl) ⟨1278626, by rfl⟩ : syracuseStep 1704835 = 2557253) B2557253
theorem B11068301 : Blo 1594996 11068301 := bstep (se 3 (by rfl) ⟨2075306, by rfl⟩ : syracuseStep 11068301 = 4150613) B4150613
theorem B2392979 : Blo 1594996 2392979 := bstep (se 1 (by rfl) ⟨1794734, by rfl⟩ : syracuseStep 2392979 = 3589469) B3589469
theorem B1917859 : Blo 1594996 1917859 := bstep (se 1 (by rfl) ⟨1438394, by rfl⟩ : syracuseStep 1917859 = 2876789) B2876789
theorem B2393009 : Blo 1594996 2393009 := bstep (se 2 (by rfl) ⟨897378, by rfl⟩ : syracuseStep 2393009 = 1794757) B1794757
theorem B2393027 : Blo 1594996 2393027 := bstep (se 1 (by rfl) ⟨1794770, by rfl⟩ : syracuseStep 2393027 = 3589541) B3589541
theorem B3589073 : Blo 1594996 3589073 := bstep (se 2 (by rfl) ⟨1345902, by rfl⟩ : syracuseStep 3589073 = 2691805) B2691805
theorem B1795027 : Blo 1594996 1795027 := bstep (se 1 (by rfl) ⟨1346270, by rfl⟩ : syracuseStep 1795027 = 2692541) B2692541
theorem B2393057 : Blo 1594996 2393057 := bstep (se 2 (by rfl) ⟨897396, by rfl⟩ : syracuseStep 2393057 = 1794793) B1794793
theorem B3589091 : Blo 1594996 3589091 := bstep (se 1 (by rfl) ⟨2691818, by rfl⟩ : syracuseStep 3589091 = 5383637) B5383637
theorem B2393075 : Blo 1594996 2393075 := bstep (se 1 (by rfl) ⟨1794806, by rfl⟩ : syracuseStep 2393075 = 3589613) B3589613
theorem B2393105 : Blo 1594996 2393105 := bstep (se 2 (by rfl) ⟨897414, by rfl⟩ : syracuseStep 2393105 = 1794829) B1794829
theorem B2393123 : Blo 1594996 2393123 := bstep (se 1 (by rfl) ⟨1794842, by rfl⟩ : syracuseStep 2393123 = 3589685) B3589685
theorem B2393153 : Blo 1594996 2393153 := bstep (se 2 (by rfl) ⟨897432, by rfl⟩ : syracuseStep 2393153 = 1794865) B1794865
theorem B9208909 : Blo 1594996 9208909 := bstep (se 3 (by rfl) ⟨1726670, by rfl⟩ : syracuseStep 9208909 = 3453341) B3453341
theorem B2393171 : Blo 1594996 2393171 := bstep (se 1 (by rfl) ⟨1794878, by rfl⟩ : syracuseStep 2393171 = 3589757) B3589757
theorem B1795171 : Blo 1594996 1795171 := bstep (se 1 (by rfl) ⟨1346378, by rfl⟩ : syracuseStep 1795171 = 2692757) B2692757
theorem B2393201 : Blo 1594996 2393201 := bstep (se 2 (by rfl) ⟨897450, by rfl⟩ : syracuseStep 2393201 = 1794901) B1794901
theorem B2393219 : Blo 1594996 2393219 := bstep (se 1 (by rfl) ⟨1794914, by rfl⟩ : syracuseStep 2393219 = 3589829) B3589829
theorem B6063245 : Blo 1594996 6063245 := bstep (se 3 (by rfl) ⟨1136858, by rfl⟩ : syracuseStep 6063245 = 2273717) B2273717
theorem B5383313 : Blo 1594996 5383313 := bstep (se 2 (by rfl) ⟨2018742, by rfl⟩ : syracuseStep 5383313 = 4037485) B4037485
theorem B2393249 : Blo 1594996 2393249 := bstep (se 2 (by rfl) ⟨897468, by rfl⟩ : syracuseStep 2393249 = 1794937) B1794937
theorem B7668913 : Blo 1594996 7668913 := bstep (se 2 (by rfl) ⟨2875842, by rfl⟩ : syracuseStep 7668913 = 5751685) B5751685
theorem B2393267 : Blo 1594996 2393267 := bstep (se 1 (by rfl) ⟨1794950, by rfl⟩ : syracuseStep 2393267 = 3589901) B3589901
theorem B2393297 : Blo 1594996 2393297 := bstep (se 2 (by rfl) ⟨897486, by rfl⟩ : syracuseStep 2393297 = 1794973) B1794973
theorem B2393315 : Blo 1594996 2393315 := bstep (se 1 (by rfl) ⟨1794986, by rfl⟩ : syracuseStep 2393315 = 3589973) B3589973
theorem B3409123 : Blo 1594996 3409123 := bstep (se 1 (by rfl) ⟨2556842, by rfl⟩ : syracuseStep 3409123 = 5113685) B5113685
theorem B3589361 : Blo 1594996 3589361 := bstep (se 2 (by rfl) ⟨1346010, by rfl⟩ : syracuseStep 3589361 = 2692021) B2692021
theorem B1795315 : Blo 1594996 1795315 := bstep (se 1 (by rfl) ⟨1346486, by rfl⟩ : syracuseStep 1795315 = 2692973) B2692973
theorem B2393345 : Blo 1594996 2393345 := bstep (se 2 (by rfl) ⟨897504, by rfl⟩ : syracuseStep 2393345 = 1795009) B1795009
theorem B3589379 : Blo 1594996 3589379 := bstep (se 1 (by rfl) ⟨2692034, by rfl⟩ : syracuseStep 3589379 = 5384069) B5384069
theorem B2393363 : Blo 1594996 2393363 := bstep (se 1 (by rfl) ⟨1795022, by rfl⟩ : syracuseStep 2393363 = 3590045) B3590045
theorem B2393393 : Blo 1594996 2393393 := bstep (se 2 (by rfl) ⟨897522, by rfl⟩ : syracuseStep 2393393 = 1795045) B1795045
theorem B2393411 : Blo 1594996 2393411 := bstep (se 1 (by rfl) ⟨1795058, by rfl⟩ : syracuseStep 2393411 = 3590117) B3590117
theorem B2393441 : Blo 1594996 2393441 := bstep (se 2 (by rfl) ⟨897540, by rfl⟩ : syracuseStep 2393441 = 1795081) B1795081
theorem B2393459 : Blo 1594996 2393459 := bstep (se 1 (by rfl) ⟨1795094, by rfl⟩ : syracuseStep 2393459 = 3590189) B3590189
theorem B1795459 : Blo 1594996 1795459 := bstep (se 1 (by rfl) ⟨1346594, by rfl⟩ : syracuseStep 1795459 = 2693189) B2693189
theorem B2393489 : Blo 1594996 2393489 := bstep (se 2 (by rfl) ⟨897558, by rfl⟩ : syracuseStep 2393489 = 1795117) B1795117
theorem B2393507 : Blo 1594996 2393507 := bstep (se 1 (by rfl) ⟨1795130, by rfl⟩ : syracuseStep 2393507 = 3590261) B3590261
theorem B2393537 : Blo 1594996 2393537 := bstep (se 2 (by rfl) ⟨897576, by rfl⟩ : syracuseStep 2393537 = 1795153) B1795153
theorem B2393555 : Blo 1594996 2393555 := bstep (se 1 (by rfl) ⟨1795166, by rfl⟩ : syracuseStep 2393555 = 3590333) B3590333
theorem B2393585 : Blo 1594996 2393585 := bstep (se 2 (by rfl) ⟨897594, by rfl⟩ : syracuseStep 2393585 = 1795189) B1795189
theorem B2393603 : Blo 1594996 2393603 := bstep (se 1 (by rfl) ⟨1795202, by rfl⟩ : syracuseStep 2393603 = 3590405) B3590405
theorem B3589649 : Blo 1594996 3589649 := bstep (se 2 (by rfl) ⟨1346118, by rfl⟩ : syracuseStep 3589649 = 2692237) B2692237
theorem B1795603 : Blo 1594996 1795603 := bstep (se 1 (by rfl) ⟨1346702, by rfl⟩ : syracuseStep 1795603 = 2693405) B2693405
theorem B2393633 : Blo 1594996 2393633 := bstep (se 2 (by rfl) ⟨897612, by rfl⟩ : syracuseStep 2393633 = 1795225) B1795225
theorem B3589667 : Blo 1594996 3589667 := bstep (se 1 (by rfl) ⟨2692250, by rfl⟩ : syracuseStep 3589667 = 5384501) B5384501
theorem B2393651 : Blo 1594996 2393651 := bstep (se 1 (by rfl) ⟨1795238, by rfl⟩ : syracuseStep 2393651 = 3590477) B3590477
theorem B2426419 : Blo 1594996 2426419 := bstep (se 1 (by rfl) ⟨1819814, by rfl⟩ : syracuseStep 2426419 = 3639629) B3639629
theorem B2393681 : Blo 1594996 2393681 := bstep (se 2 (by rfl) ⟨897630, by rfl⟩ : syracuseStep 2393681 = 1795261) B1795261
theorem B2393699 : Blo 1594996 2393699 := bstep (se 1 (by rfl) ⟨1795274, by rfl⟩ : syracuseStep 2393699 = 3590549) B3590549
theorem B2393729 : Blo 1594996 2393729 := bstep (se 2 (by rfl) ⟨897648, by rfl⟩ : syracuseStep 2393729 = 1795297) B1795297
theorem B10913413 : Blo 1594996 10913413 := bstep (se 4 (by rfl) ⟨1023132, by rfl⟩ : syracuseStep 10913413 = 2046265) B2046265
theorem B2393747 : Blo 1594996 2393747 := bstep (se 1 (by rfl) ⟨1795310, by rfl⟩ : syracuseStep 2393747 = 3590621) B3590621
theorem B1795747 : Blo 1594996 1795747 := bstep (se 1 (by rfl) ⟨1346810, by rfl⟩ : syracuseStep 1795747 = 2693621) B2693621
theorem B5383853 : Blo 1594996 5383853 := bstep (se 3 (by rfl) ⟨1009472, by rfl⟩ : syracuseStep 5383853 = 2018945) B2018945
theorem B2393777 : Blo 1594996 2393777 := bstep (se 2 (by rfl) ⟨897666, by rfl⟩ : syracuseStep 2393777 = 1795333) B1795333
theorem B2393795 : Blo 1594996 2393795 := bstep (se 1 (by rfl) ⟨1795346, by rfl⟩ : syracuseStep 2393795 = 3590693) B3590693
theorem B5457613 : Blo 1594996 5457613 := bstep (se 3 (by rfl) ⟨1023302, by rfl⟩ : syracuseStep 5457613 = 2046605) B2046605
theorem B4040401 : Blo 1594996 4040401 := bstep (se 2 (by rfl) ⟨1515150, by rfl⟩ : syracuseStep 4040401 = 3030301) B3030301
theorem B2393825 : Blo 1594996 2393825 := bstep (se 2 (by rfl) ⟨897684, by rfl⟩ : syracuseStep 2393825 = 1795369) B1795369
theorem B5383907 : Blo 1594996 5383907 := bstep (se 1 (by rfl) ⟨4037930, by rfl⟩ : syracuseStep 5383907 = 8075861) B8075861
theorem B2393843 : Blo 1594996 2393843 := bstep (se 1 (by rfl) ⟨1795382, by rfl⟩ : syracuseStep 2393843 = 3590765) B3590765
theorem B2393873 : Blo 1594996 2393873 := bstep (se 2 (by rfl) ⟨897702, by rfl⟩ : syracuseStep 2393873 = 1795405) B1795405
theorem B2393891 : Blo 1594996 2393891 := bstep (se 1 (by rfl) ⟨1795418, by rfl⟩ : syracuseStep 2393891 = 3590837) B3590837
theorem B3589937 : Blo 1594996 3589937 := bstep (se 2 (by rfl) ⟨1346226, by rfl⟩ : syracuseStep 3589937 = 2692453) B2692453
theorem B1795891 : Blo 1594996 1795891 := bstep (se 1 (by rfl) ⟨1346918, by rfl⟩ : syracuseStep 1795891 = 2693837) B2693837
theorem B2393921 : Blo 1594996 2393921 := bstep (se 2 (by rfl) ⟨897720, by rfl⟩ : syracuseStep 2393921 = 1795441) B1795441
theorem B3589955 : Blo 1594996 3589955 := bstep (se 1 (by rfl) ⟨2692466, by rfl⟩ : syracuseStep 3589955 = 5384933) B5384933
theorem B3114833 : Blo 1594996 3114833 := bstep (se 2 (by rfl) ⟨1168062, by rfl⟩ : syracuseStep 3114833 = 2336125) B2336125
theorem B2590547 : Blo 1594996 2590547 := bstep (se 1 (by rfl) ⟨1942910, by rfl⟩ : syracuseStep 2590547 = 3885821) B3885821
theorem B2393939 : Blo 1594996 2393939 := bstep (se 1 (by rfl) ⟨1795454, by rfl⟩ : syracuseStep 2393939 = 3590909) B3590909
theorem B2393969 : Blo 1594996 2393969 := bstep (se 2 (by rfl) ⟨897738, by rfl⟩ : syracuseStep 2393969 = 1795477) B1795477
theorem B2557811 : Blo 1594996 2557811 := bstep (se 1 (by rfl) ⟨1918358, by rfl⟩ : syracuseStep 2557811 = 3836717) B3836717
theorem B2393987 : Blo 1594996 2393987 := bstep (se 1 (by rfl) ⟨1795490, by rfl⟩ : syracuseStep 2393987 = 3590981) B3590981
theorem B2426755 : Blo 1594996 2426755 := bstep (se 1 (by rfl) ⟨1820066, by rfl⟩ : syracuseStep 2426755 = 3640133) B3640133
theorem B3835793 : Blo 1594996 3835793 := bstep (se 2 (by rfl) ⟨1438422, by rfl⟩ : syracuseStep 3835793 = 2876845) B2876845
theorem B2394017 : Blo 1594996 2394017 := bstep (se 2 (by rfl) ⟨897756, by rfl⟩ : syracuseStep 2394017 = 1795513) B1795513
theorem B6817699 : Blo 1594996 6817699 := bstep (se 1 (by rfl) ⟨5113274, by rfl⟩ : syracuseStep 6817699 = 10226549) B10226549
theorem B2394035 : Blo 1594996 2394035 := bstep (se 1 (by rfl) ⟨1795526, by rfl⟩ : syracuseStep 2394035 = 3591053) B3591053
theorem B1796035 : Blo 1594996 1796035 := bstep (se 1 (by rfl) ⟨1347026, by rfl⟩ : syracuseStep 1796035 = 2694053) B2694053
theorem B2394065 : Blo 1594996 2394065 := bstep (se 2 (by rfl) ⟨897774, by rfl⟩ : syracuseStep 2394065 = 1795549) B1795549
theorem B2394083 : Blo 1594996 2394083 := bstep (se 1 (by rfl) ⟨1795562, by rfl⟩ : syracuseStep 2394083 = 3591125) B3591125
theorem B4040675 : Blo 1594996 4040675 := bstep (se 1 (by rfl) ⟨3030506, by rfl⟩ : syracuseStep 4040675 = 6061013) B6061013
theorem B5384177 : Blo 1594996 5384177 := bstep (se 2 (by rfl) ⟨2019066, by rfl⟩ : syracuseStep 5384177 = 4038133) B4038133
theorem B2394113 : Blo 1594996 2394113 := bstep (se 2 (by rfl) ⟨897792, by rfl⟩ : syracuseStep 2394113 = 1795585) B1795585
theorem B2394131 : Blo 1594996 2394131 := bstep (se 1 (by rfl) ⟨1795598, by rfl⟩ : syracuseStep 2394131 = 3591197) B3591197
theorem B4851757 : Blo 1594996 4851757 := bstep (se 3 (by rfl) ⟨909704, by rfl⟩ : syracuseStep 4851757 = 1819409) B1819409
theorem B2394161 : Blo 1594996 2394161 := bstep (se 2 (by rfl) ⟨897810, by rfl⟩ : syracuseStep 2394161 = 1795621) B1795621
theorem B2394179 : Blo 1594996 2394179 := bstep (se 1 (by rfl) ⟨1795634, by rfl⟩ : syracuseStep 2394179 = 3591269) B3591269
theorem B3590225 : Blo 1594996 3590225 := bstep (se 2 (by rfl) ⟨1346334, by rfl⟩ : syracuseStep 3590225 = 2692669) B2692669
theorem B1796179 : Blo 1594996 1796179 := bstep (se 1 (by rfl) ⟨1347134, by rfl⟩ : syracuseStep 1796179 = 2694269) B2694269
theorem B2394209 : Blo 1594996 2394209 := bstep (se 2 (by rfl) ⟨897828, by rfl⟩ : syracuseStep 2394209 = 1795657) B1795657
theorem B2271331 : Blo 1594996 2271331 := bstep (se 1 (by rfl) ⟨1703498, by rfl⟩ : syracuseStep 2271331 = 3406997) B3406997
theorem B3590243 : Blo 1594996 3590243 := bstep (se 1 (by rfl) ⟨2692682, by rfl⟩ : syracuseStep 3590243 = 5385365) B5385365
theorem B2394227 : Blo 1594996 2394227 := bstep (se 1 (by rfl) ⟨1795670, by rfl⟩ : syracuseStep 2394227 = 3591341) B3591341
theorem B6146189 : Blo 1594996 6146189 := bstep (se 3 (by rfl) ⟨1152410, by rfl⟩ : syracuseStep 6146189 = 2304821) B2304821
theorem B2394257 : Blo 1594996 2394257 := bstep (se 2 (by rfl) ⟨897846, by rfl⟩ : syracuseStep 2394257 = 1795693) B1795693
theorem B1820819 : Blo 1594996 1820819 := bstep (se 1 (by rfl) ⟨1365614, by rfl⟩ : syracuseStep 1820819 = 2731229) B2731229
theorem B2394275 : Blo 1594996 2394275 := bstep (se 1 (by rfl) ⟨1795706, by rfl⟩ : syracuseStep 2394275 = 3591413) B3591413
theorem B4040867 : Blo 1594996 4040867 := bstep (se 1 (by rfl) ⟨3030650, by rfl⟩ : syracuseStep 4040867 = 6061301) B6061301
theorem B2394305 : Blo 1594996 2394305 := bstep (se 2 (by rfl) ⟨897864, by rfl⟩ : syracuseStep 2394305 = 1795729) B1795729
theorem B2394323 : Blo 1594996 2394323 := bstep (se 1 (by rfl) ⟨1795742, by rfl⟩ : syracuseStep 2394323 = 3591485) B3591485
theorem B655591637 : Blo 1594996 655591637 := bstep (se 7 (by rfl) ⟨7682714, by rfl⟩ : syracuseStep 655591637 = 15365429) B15365429
theorem B8079587 : Blo 1594996 8079587 := bstep (se 1 (by rfl) ⟨6059690, by rfl⟩ : syracuseStep 8079587 = 12119381) B12119381
theorem B1796323 : Blo 1594996 1796323 := bstep (se 1 (by rfl) ⟨1347242, by rfl⟩ : syracuseStep 1796323 = 2694485) B2694485
theorem B2394353 : Blo 1594996 2394353 := bstep (se 2 (by rfl) ⟨897882, by rfl⟩ : syracuseStep 2394353 = 1795765) B1795765
theorem B2394371 : Blo 1594996 2394371 := bstep (se 1 (by rfl) ⟨1795778, by rfl⟩ : syracuseStep 2394371 = 3591557) B3591557
theorem B2394401 : Blo 1594996 2394401 := bstep (se 2 (by rfl) ⟨897900, by rfl⟩ : syracuseStep 2394401 = 1795801) B1795801
theorem B2394419 : Blo 1594996 2394419 := bstep (se 1 (by rfl) ⟨1795814, by rfl⟩ : syracuseStep 2394419 = 3591629) B3591629
theorem B2394449 : Blo 1594996 2394449 := bstep (se 2 (by rfl) ⟨897918, by rfl⟩ : syracuseStep 2394449 = 1795837) B1795837
theorem B2394467 : Blo 1594996 2394467 := bstep (se 1 (by rfl) ⟨1795850, by rfl⟩ : syracuseStep 2394467 = 3591701) B3591701
theorem B3590513 : Blo 1594996 3590513 := bstep (se 2 (by rfl) ⟨1346442, by rfl⟩ : syracuseStep 3590513 = 2692885) B2692885
theorem B1796467 : Blo 1594996 1796467 := bstep (se 1 (by rfl) ⟨1347350, by rfl⟩ : syracuseStep 1796467 = 2694701) B2694701
theorem B2394497 : Blo 1594996 2394497 := bstep (se 2 (by rfl) ⟨897936, by rfl⟩ : syracuseStep 2394497 = 1795873) B1795873
theorem B3590531 : Blo 1594996 3590531 := bstep (se 1 (by rfl) ⟨2692898, by rfl⟩ : syracuseStep 3590531 = 5385797) B5385797
theorem B2394515 : Blo 1594996 2394515 := bstep (se 1 (by rfl) ⟨1795886, by rfl⟩ : syracuseStep 2394515 = 3591773) B3591773
theorem B2394545 : Blo 1594996 2394545 := bstep (se 2 (by rfl) ⟨897954, by rfl⟩ : syracuseStep 2394545 = 1795909) B1795909
theorem B3410353 : Blo 1594996 3410353 := bstep (se 2 (by rfl) ⟨1278882, by rfl⟩ : syracuseStep 3410353 = 2557765) B2557765
theorem B2271667 : Blo 1594996 2271667 := bstep (se 1 (by rfl) ⟨1703750, by rfl⟩ : syracuseStep 2271667 = 3407501) B3407501
theorem B2394563 : Blo 1594996 2394563 := bstep (se 1 (by rfl) ⟨1795922, by rfl⟩ : syracuseStep 2394563 = 3591845) B3591845
theorem B2394593 : Blo 1594996 2394593 := bstep (se 2 (by rfl) ⟨897972, by rfl⟩ : syracuseStep 2394593 = 1795945) B1795945
theorem B17254883 : Blo 1594996 17254883 := bstep (se 1 (by rfl) ⟨12941162, by rfl⟩ : syracuseStep 17254883 = 25882325) B25882325
theorem B2394611 : Blo 1594996 2394611 := bstep (se 1 (by rfl) ⟨1795958, by rfl⟩ : syracuseStep 2394611 = 3591917) B3591917
theorem B1796611 : Blo 1594996 1796611 := bstep (se 1 (by rfl) ⟨1347458, by rfl⟩ : syracuseStep 1796611 = 2694917) B2694917
theorem B5384717 : Blo 1594996 5384717 := bstep (se 3 (by rfl) ⟨1009634, by rfl⟩ : syracuseStep 5384717 = 2019269) B2019269
theorem B5753357 : Blo 1594996 5753357 := bstep (se 3 (by rfl) ⟨1078754, by rfl⟩ : syracuseStep 5753357 = 2157509) B2157509
theorem B2394641 : Blo 1594996 2394641 := bstep (se 2 (by rfl) ⟨897990, by rfl⟩ : syracuseStep 2394641 = 1795981) B1795981
theorem B2394659 : Blo 1594996 2394659 := bstep (se 1 (by rfl) ⟨1795994, by rfl⟩ : syracuseStep 2394659 = 3591989) B3591989
theorem B2394689 : Blo 1594996 2394689 := bstep (se 2 (by rfl) ⟨898008, by rfl⟩ : syracuseStep 2394689 = 1796017) B1796017
theorem B5384771 : Blo 1594996 5384771 := bstep (se 1 (by rfl) ⟨4038578, by rfl⟩ : syracuseStep 5384771 = 8077157) B8077157
theorem B2394707 : Blo 1594996 2394707 := bstep (se 1 (by rfl) ⟨1796030, by rfl⟩ : syracuseStep 2394707 = 3592061) B3592061
theorem B2394737 : Blo 1594996 2394737 := bstep (se 2 (by rfl) ⟨898026, by rfl⟩ : syracuseStep 2394737 = 1796053) B1796053
theorem B2394755 : Blo 1594996 2394755 := bstep (se 1 (by rfl) ⟨1796066, by rfl⟩ : syracuseStep 2394755 = 3592133) B3592133
theorem B8628869 : Blo 1594996 8628869 := bstep (se 4 (by rfl) ⟨808956, by rfl⟩ : syracuseStep 8628869 = 1617913) B1617913
theorem B3590801 : Blo 1594996 3590801 := bstep (se 2 (by rfl) ⟨1346550, by rfl⟩ : syracuseStep 3590801 = 2693101) B2693101
theorem B2394785 : Blo 1594996 2394785 := bstep (se 2 (by rfl) ⟨898044, by rfl⟩ : syracuseStep 2394785 = 1796089) B1796089
theorem B3590819 : Blo 1594996 3590819 := bstep (se 1 (by rfl) ⟨2693114, by rfl⟩ : syracuseStep 3590819 = 5386229) B5386229
theorem B2394803 : Blo 1594996 2394803 := bstep (se 1 (by rfl) ⟨1796102, by rfl⟩ : syracuseStep 2394803 = 3592205) B3592205
theorem B6056653 : Blo 1594996 6056653 := bstep (se 3 (by rfl) ⟨1135622, by rfl⟩ : syracuseStep 6056653 = 2271245) B2271245
theorem B2394833 : Blo 1594996 2394833 := bstep (se 2 (by rfl) ⟨898062, by rfl⟩ : syracuseStep 2394833 = 1796125) B1796125
theorem B2730707 : Blo 1594996 2730707 := bstep (se 1 (by rfl) ⟨2048030, by rfl⟩ : syracuseStep 2730707 = 4096061) B4096061
theorem B2394851 : Blo 1594996 2394851 := bstep (se 1 (by rfl) ⟨1796138, by rfl⟩ : syracuseStep 2394851 = 3592277) B3592277
theorem B2394881 : Blo 1594996 2394881 := bstep (se 2 (by rfl) ⟨898080, by rfl⟩ : syracuseStep 2394881 = 1796161) B1796161
theorem B8628997 : Blo 1594996 8628997 := bstep (se 4 (by rfl) ⟨808968, by rfl⟩ : syracuseStep 8628997 = 1617937) B1617937
theorem B4606733 : Blo 1594996 4606733 := bstep (se 3 (by rfl) ⟨863762, by rfl⟩ : syracuseStep 4606733 = 1727525) B1727525
theorem B2394899 : Blo 1594996 2394899 := bstep (se 1 (by rfl) ⟨1796174, by rfl⟩ : syracuseStep 2394899 = 3592349) B3592349
theorem B5114659 : Blo 1594996 5114659 := bstep (se 1 (by rfl) ⟨3835994, by rfl⟩ : syracuseStep 5114659 = 7671989) B7671989
theorem B2394929 : Blo 1594996 2394929 := bstep (se 2 (by rfl) ⟨898098, by rfl⟩ : syracuseStep 2394929 = 1796197) B1796197
theorem B2394947 : Blo 1594996 2394947 := bstep (se 1 (by rfl) ⟨1796210, by rfl⟩ : syracuseStep 2394947 = 3592421) B3592421
theorem B5385041 : Blo 1594996 5385041 := bstep (se 2 (by rfl) ⟨2019390, by rfl⟩ : syracuseStep 5385041 = 4038781) B4038781
theorem B2394977 : Blo 1594996 2394977 := bstep (se 2 (by rfl) ⟨898116, by rfl⟩ : syracuseStep 2394977 = 1796233) B1796233
theorem B2394995 : Blo 1594996 2394995 := bstep (se 1 (by rfl) ⟨1796246, by rfl⟩ : syracuseStep 2394995 = 3592493) B3592493
theorem B2395025 : Blo 1594996 2395025 := bstep (se 2 (by rfl) ⟨898134, by rfl⟩ : syracuseStep 2395025 = 1796269) B1796269
theorem B2395043 : Blo 1594996 2395043 := bstep (se 1 (by rfl) ⟨1796282, by rfl⟩ : syracuseStep 2395043 = 3592565) B3592565
theorem B3591089 : Blo 1594996 3591089 := bstep (se 2 (by rfl) ⟨1346658, by rfl⟩ : syracuseStep 3591089 = 2693317) B2693317
theorem B5114801 : Blo 1594996 5114801 := bstep (se 2 (by rfl) ⟨1918050, by rfl⟩ : syracuseStep 5114801 = 3836101) B3836101
theorem B2395073 : Blo 1594996 2395073 := bstep (se 2 (by rfl) ⟨898152, by rfl⟩ : syracuseStep 2395073 = 1796305) B1796305
theorem B3591107 : Blo 1594996 3591107 := bstep (se 1 (by rfl) ⟨2693330, by rfl⟩ : syracuseStep 3591107 = 5386661) B5386661
theorem B1616851 : Blo 1594996 1616851 := bstep (se 1 (by rfl) ⟨1212638, by rfl⟩ : syracuseStep 1616851 = 2425277) B2425277
theorem B2395091 : Blo 1594996 2395091 := bstep (se 1 (by rfl) ⟨1796318, by rfl⟩ : syracuseStep 2395091 = 3592637) B3592637
theorem B2272225 : Blo 1594996 2272225 := bstep (se 2 (by rfl) ⟨852084, by rfl⟩ : syracuseStep 2272225 = 1704169) B1704169
theorem B18435043 : Blo 1594996 18435043 := bstep (se 1 (by rfl) ⟨13826282, by rfl⟩ : syracuseStep 18435043 = 27652565) B27652565
theorem B2157553 : Blo 1594996 2157553 := bstep (se 2 (by rfl) ⟨809082, by rfl⟩ : syracuseStep 2157553 = 1618165) B1618165
theorem B2395121 : Blo 1594996 2395121 := bstep (se 2 (by rfl) ⟨898170, by rfl⟩ : syracuseStep 2395121 = 1796341) B1796341
theorem B2272259 : Blo 1594996 2272259 := bstep (se 1 (by rfl) ⟨1704194, by rfl⟩ : syracuseStep 2272259 = 3408389) B3408389
theorem B2395139 : Blo 1594996 2395139 := bstep (se 1 (by rfl) ⟨1796354, by rfl⟩ : syracuseStep 2395139 = 3592709) B3592709
theorem B8080397 : Blo 1594996 8080397 := bstep (se 3 (by rfl) ⟨1515074, by rfl⟩ : syracuseStep 8080397 = 3030149) B3030149
theorem B2395169 : Blo 1594996 2395169 := bstep (se 2 (by rfl) ⟨898188, by rfl⟩ : syracuseStep 2395169 = 1796377) B1796377
theorem B5114915 : Blo 1594996 5114915 := bstep (se 1 (by rfl) ⟨3836186, by rfl⟩ : syracuseStep 5114915 = 7672373) B7672373
theorem B2395187 : Blo 1594996 2395187 := bstep (se 1 (by rfl) ⟨1796390, by rfl⟩ : syracuseStep 2395187 = 3592781) B3592781
theorem B4041809 : Blo 1594996 4041809 := bstep (se 2 (by rfl) ⟨1515678, by rfl⟩ : syracuseStep 4041809 = 3031357) B3031357
theorem B2395217 : Blo 1594996 2395217 := bstep (se 2 (by rfl) ⟨898206, by rfl⟩ : syracuseStep 2395217 = 1796413) B1796413
theorem B2395235 : Blo 1594996 2395235 := bstep (se 1 (by rfl) ⟨1796426, by rfl⟩ : syracuseStep 2395235 = 3592853) B3592853
theorem B2395265 : Blo 1594996 2395265 := bstep (se 2 (by rfl) ⟨898224, by rfl⟩ : syracuseStep 2395265 = 1796449) B1796449
theorem B4041859 : Blo 1594996 4041859 := bstep (se 1 (by rfl) ⟨3031394, by rfl⟩ : syracuseStep 4041859 = 6062789) B6062789
theorem B2395283 : Blo 1594996 2395283 := bstep (se 1 (by rfl) ⟨1796462, by rfl⟩ : syracuseStep 2395283 = 3592925) B3592925
theorem B2395313 : Blo 1594996 2395313 := bstep (se 2 (by rfl) ⟨898242, by rfl⟩ : syracuseStep 2395313 = 1796485) B1796485
theorem B2395331 : Blo 1594996 2395331 := bstep (se 1 (by rfl) ⟨1796498, by rfl⟩ : syracuseStep 2395331 = 3592997) B3592997
theorem B3591377 : Blo 1594996 3591377 := bstep (se 2 (by rfl) ⟨1346766, by rfl⟩ : syracuseStep 3591377 = 2693533) B2693533
theorem B3280081 : Blo 1594996 3280081 := bstep (se 2 (by rfl) ⟨1230030, by rfl⟩ : syracuseStep 3280081 = 2460061) B2460061
theorem B2395361 : Blo 1594996 2395361 := bstep (se 2 (by rfl) ⟨898260, by rfl⟩ : syracuseStep 2395361 = 1796521) B1796521
theorem B3591395 : Blo 1594996 3591395 := bstep (se 1 (by rfl) ⟨2693546, by rfl⟩ : syracuseStep 3591395 = 5387093) B5387093
theorem B2395379 : Blo 1594996 2395379 := bstep (se 1 (by rfl) ⟨1796534, by rfl⟩ : syracuseStep 2395379 = 3593069) B3593069
theorem B2428147 : Blo 1594996 2428147 := bstep (se 1 (by rfl) ⟨1821110, by rfl⟩ : syracuseStep 2428147 = 3642221) B3642221
theorem B4042001 : Blo 1594996 4042001 := bstep (se 2 (by rfl) ⟨1515750, by rfl⟩ : syracuseStep 4042001 = 3031501) B3031501
theorem B2395409 : Blo 1594996 2395409 := bstep (se 2 (by rfl) ⟨898278, by rfl⟩ : syracuseStep 2395409 = 1796557) B1796557
theorem B2395427 : Blo 1594996 2395427 := bstep (se 1 (by rfl) ⟨1796570, by rfl⟩ : syracuseStep 2395427 = 3593141) B3593141
theorem B2395457 : Blo 1594996 2395457 := bstep (se 2 (by rfl) ⟨898296, by rfl⟩ : syracuseStep 2395457 = 1796593) B1796593
theorem B5180753 : Blo 1594996 5180753 := bstep (se 2 (by rfl) ⟨1942782, by rfl⟩ : syracuseStep 5180753 = 3885565) B3885565
theorem B2395475 : Blo 1594996 2395475 := bstep (se 1 (by rfl) ⟨1796606, by rfl⟩ : syracuseStep 2395475 = 3593213) B3593213
theorem B5385581 : Blo 1594996 5385581 := bstep (se 3 (by rfl) ⟨1009796, by rfl⟩ : syracuseStep 5385581 = 2019593) B2019593
theorem B5385635 : Blo 1594996 5385635 := bstep (se 1 (by rfl) ⟨4039226, by rfl⟩ : syracuseStep 5385635 = 8078453) B8078453
theorem B2592209 : Blo 1594996 2592209 := bstep (se 2 (by rfl) ⟨972078, by rfl⟩ : syracuseStep 2592209 = 1944157) B1944157
theorem B6057443 : Blo 1594996 6057443 := bstep (se 1 (by rfl) ⟨4543082, by rfl⟩ : syracuseStep 6057443 = 9086165) B9086165
theorem B3591665 : Blo 1594996 3591665 := bstep (se 2 (by rfl) ⟨1346874, by rfl⟩ : syracuseStep 3591665 = 2693749) B2693749
theorem B3591683 : Blo 1594996 3591683 := bstep (se 1 (by rfl) ⟨2693762, by rfl⟩ : syracuseStep 3591683 = 5387525) B5387525
theorem B2272817 : Blo 1594996 2272817 := bstep (se 2 (by rfl) ⟨852306, by rfl⟩ : syracuseStep 2272817 = 1704613) B1704613
theorem B5533265 : Blo 1594996 5533265 := bstep (se 2 (by rfl) ⟨2074974, by rfl⟩ : syracuseStep 5533265 = 4149949) B4149949
theorem B9088625 : Blo 1594996 9088625 := bstep (se 2 (by rfl) ⟨3408234, by rfl⟩ : syracuseStep 9088625 = 6816469) B6816469
theorem B2272897 : Blo 1594996 2272897 := bstep (se 2 (by rfl) ⟨852336, by rfl⟩ : syracuseStep 2272897 = 1704673) B1704673
theorem B4542115 : Blo 1594996 4542115 := bstep (se 1 (by rfl) ⟨3406586, by rfl⟩ : syracuseStep 4542115 = 6813173) B6813173
theorem B5385905 : Blo 1594996 5385905 := bstep (se 2 (by rfl) ⟨2019714, by rfl⟩ : syracuseStep 5385905 = 4039429) B4039429
theorem B20459249 : Blo 1594996 20459249 := bstep (se 2 (by rfl) ⟨7672218, by rfl⟩ : syracuseStep 20459249 = 15344437) B15344437
theorem B3591953 : Blo 1594996 3591953 := bstep (se 2 (by rfl) ⟨1346982, by rfl⟩ : syracuseStep 3591953 = 2693965) B2693965
theorem B2019107 : Blo 1594996 2019107 := bstep (se 1 (by rfl) ⟨1514330, by rfl⟩ : syracuseStep 2019107 = 3028661) B3028661
theorem B3591971 : Blo 1594996 3591971 := bstep (se 1 (by rfl) ⟨2693978, by rfl⟩ : syracuseStep 3591971 = 5387957) B5387957
theorem B5533517 : Blo 1594996 5533517 := bstep (se 3 (by rfl) ⟨1037534, by rfl⟩ : syracuseStep 5533517 = 2075069) B2075069
theorem B26251235 : Blo 1594996 26251235 := bstep (se 1 (by rfl) ⟨19688426, by rfl⟩ : syracuseStep 26251235 = 39376853) B39376853
theorem B5115889 : Blo 1594996 5115889 := bstep (se 2 (by rfl) ⟨1918458, by rfl⟩ : syracuseStep 5115889 = 3836917) B3836917
theorem B6230029 : Blo 1594996 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B3592241 : Blo 1594996 3592241 := bstep (se 2 (by rfl) ⟨1347090, by rfl⟩ : syracuseStep 3592241 = 2694181) B2694181
theorem B3592259 : Blo 1594996 3592259 := bstep (se 1 (by rfl) ⟨2694194, by rfl⟩ : syracuseStep 3592259 = 5388389) B5388389
theorem B6058097 : Blo 1594996 6058097 := bstep (se 2 (by rfl) ⟨2271786, by rfl⟩ : syracuseStep 6058097 = 4543573) B4543573
theorem B4542605 : Blo 1594996 4542605 := bstep (se 3 (by rfl) ⟨851738, by rfl⟩ : syracuseStep 4542605 = 1703477) B1703477
theorem B1618067 : Blo 1594996 1618067 := bstep (se 1 (by rfl) ⟨1213550, by rfl⟩ : syracuseStep 1618067 = 2427101) B2427101
theorem B5386445 : Blo 1594996 5386445 := bstep (se 3 (by rfl) ⟨1009958, by rfl⟩ : syracuseStep 5386445 = 2019917) B2019917
theorem B5386499 : Blo 1594996 5386499 := bstep (se 1 (by rfl) ⟨4039874, by rfl⟩ : syracuseStep 5386499 = 8079749) B8079749
theorem B6820145 : Blo 1594996 6820145 := bstep (se 2 (by rfl) ⟨2557554, by rfl⟩ : syracuseStep 6820145 = 5115109) B5115109
theorem B7778609 : Blo 1594996 7778609 := bstep (se 2 (by rfl) ⟨2916978, by rfl⟩ : syracuseStep 7778609 = 5833957) B5833957
theorem B3592529 : Blo 1594996 3592529 := bstep (se 2 (by rfl) ⟨1347198, by rfl⟩ : syracuseStep 3592529 = 2694397) B2694397
theorem B3592547 : Blo 1594996 3592547 := bstep (se 1 (by rfl) ⟨2694410, by rfl⟩ : syracuseStep 3592547 = 5388821) B5388821
theorem B2273683 : Blo 1594996 2273683 := bstep (se 1 (by rfl) ⟨1705262, by rfl⟩ : syracuseStep 2273683 = 3410525) B3410525
theorem B20738501 : Blo 1594996 20738501 := bstep (se 4 (by rfl) ⟨1944234, by rfl⟩ : syracuseStep 20738501 = 3888469) B3888469
theorem B2019811 : Blo 1594996 2019811 := bstep (se 1 (by rfl) ⟨1514858, by rfl⟩ : syracuseStep 2019811 = 3029717) B3029717
theorem B2691569 : Blo 1594996 2691569 := bstep (se 2 (by rfl) ⟨1009338, by rfl⟩ : syracuseStep 2691569 = 2018677) B2018677
theorem B5386769 : Blo 1594996 5386769 := bstep (se 2 (by rfl) ⟨2020038, by rfl⟩ : syracuseStep 5386769 = 4040077) B4040077
theorem B5460529 : Blo 1594996 5460529 := bstep (se 2 (by rfl) ⟨2047698, by rfl⟩ : syracuseStep 5460529 = 4095397) B4095397
theorem B2019907 : Blo 1594996 2019907 := bstep (se 1 (by rfl) ⟨1514930, by rfl⟩ : syracuseStep 2019907 = 3029861) B3029861
theorem B2691697 : Blo 1594996 2691697 := bstep (se 2 (by rfl) ⟨1009386, by rfl⟩ : syracuseStep 2691697 = 2018773) B2018773
theorem B3592817 : Blo 1594996 3592817 := bstep (se 2 (by rfl) ⟨1347306, by rfl⟩ : syracuseStep 3592817 = 2694613) B2694613
theorem B3592835 : Blo 1594996 3592835 := bstep (se 1 (by rfl) ⟨2694626, by rfl⟩ : syracuseStep 3592835 = 5389253) B5389253
theorem B2691731 : Blo 1594996 2691731 := bstep (se 1 (by rfl) ⟨2018798, by rfl⟩ : syracuseStep 2691731 = 4037597) B4037597
theorem B8622769 : Blo 1594996 8622769 := bstep (se 2 (by rfl) ⟨3233538, by rfl⟩ : syracuseStep 8622769 = 6467077) B6467077
theorem B2691859 : Blo 1594996 2691859 := bstep (se 1 (by rfl) ⟨2018894, by rfl⟩ : syracuseStep 2691859 = 4037789) B4037789
theorem B3593105 : Blo 1594996 3593105 := bstep (se 2 (by rfl) ⟨1347414, by rfl⟩ : syracuseStep 3593105 = 2694829) B2694829
theorem B2692001 : Blo 1594996 2692001 := bstep (se 2 (by rfl) ⟨1009500, by rfl⟩ : syracuseStep 2692001 = 2019001) B2019001
theorem B3593123 : Blo 1594996 3593123 := bstep (se 1 (by rfl) ⟨2694842, by rfl⟩ : syracuseStep 3593123 = 5389685) B5389685
theorem B20452277 : Blo 1594996 20452277 := bstep (se 5 (by rfl) ⟨958700, by rfl⟩ : syracuseStep 20452277 = 1917401) B1917401
theorem B12948493 : Blo 1594996 12948493 := bstep (se 3 (by rfl) ⟨2427842, by rfl⟩ : syracuseStep 12948493 = 4855685) B4855685
theorem B2692129 : Blo 1594996 2692129 := bstep (se 2 (by rfl) ⟨1009548, by rfl⟩ : syracuseStep 2692129 = 2019097) B2019097
theorem B9090083 : Blo 1594996 9090083 := bstep (se 1 (by rfl) ⟨6817562, by rfl⟩ : syracuseStep 9090083 = 13635125) B13635125
theorem B5387309 : Blo 1594996 5387309 := bstep (se 3 (by rfl) ⟨1010120, by rfl⟩ : syracuseStep 5387309 = 2020241) B2020241
theorem B2020403 : Blo 1594996 2020403 := bstep (se 1 (by rfl) ⟨1515302, by rfl⟩ : syracuseStep 2020403 = 3030605) B3030605
theorem B2692163 : Blo 1594996 2692163 := bstep (se 1 (by rfl) ⟨2019122, by rfl⟩ : syracuseStep 2692163 = 4038245) B4038245
theorem B10228805 : Blo 1594996 10228805 := bstep (se 4 (by rfl) ⟨958950, by rfl⟩ : syracuseStep 10228805 = 1917901) B1917901
theorem B5387363 : Blo 1594996 5387363 := bstep (se 1 (by rfl) ⟨4040522, by rfl⟩ : syracuseStep 5387363 = 8081045) B8081045
theorem B3028099 : Blo 1594996 3028099 := bstep (se 1 (by rfl) ⟨2271074, by rfl⟩ : syracuseStep 3028099 = 4542149) B4542149
theorem B11220101 : Blo 1594996 11220101 := bstep (se 4 (by rfl) ⟨1051884, by rfl⟩ : syracuseStep 11220101 = 2103769) B2103769
theorem B2692291 : Blo 1594996 2692291 := bstep (se 1 (by rfl) ⟨2019218, by rfl⟩ : syracuseStep 2692291 = 4038437) B4038437
theorem B4854979 : Blo 1594996 4854979 := bstep (se 1 (by rfl) ⟨3641234, by rfl⟩ : syracuseStep 4854979 = 7282469) B7282469
theorem B13636835 : Blo 1594996 13636835 := bstep (se 1 (by rfl) ⟨10227626, by rfl⟩ : syracuseStep 13636835 = 20455253) B20455253
theorem B51754261 : Blo 1594996 51754261 := bstep (se 6 (by rfl) ⟨1212990, by rfl⟩ : syracuseStep 51754261 = 2425981) B2425981
theorem B3028259 : Blo 1594996 3028259 := bstep (se 1 (by rfl) ⟨2271194, by rfl⟩ : syracuseStep 3028259 = 4542389) B4542389
theorem B4543789 : Blo 1594996 4543789 := bstep (se 3 (by rfl) ⟨851960, by rfl⟩ : syracuseStep 4543789 = 1703921) B1703921
theorem B2692433 : Blo 1594996 2692433 := bstep (se 2 (by rfl) ⟨1009662, by rfl⟩ : syracuseStep 2692433 = 2019325) B2019325
theorem B5387633 : Blo 1594996 5387633 := bstep (se 2 (by rfl) ⟨2020362, by rfl⟩ : syracuseStep 5387633 = 4040725) B4040725
theorem B5461361 : Blo 1594996 5461361 := bstep (se 2 (by rfl) ⟨2048010, by rfl⟩ : syracuseStep 5461361 = 4096021) B4096021
theorem B4609457 : Blo 1594996 4609457 := bstep (se 2 (by rfl) ⟨1728546, by rfl⟩ : syracuseStep 4609457 = 3457093) B3457093
theorem B2692561 : Blo 1594996 2692561 := bstep (se 2 (by rfl) ⟨1009710, by rfl⟩ : syracuseStep 2692561 = 2019421) B2019421
theorem B6469091 : Blo 1594996 6469091 := bstep (se 1 (by rfl) ⟨4851818, by rfl⟩ : syracuseStep 6469091 = 9703637) B9703637
theorem B2692595 : Blo 1594996 2692595 := bstep (se 1 (by rfl) ⟨2019446, by rfl⟩ : syracuseStep 2692595 = 4038893) B4038893
theorem B6059555 : Blo 1594996 6059555 := bstep (se 1 (by rfl) ⟨4544666, by rfl⟩ : syracuseStep 6059555 = 9089333) B9089333
theorem B6059569 : Blo 1594996 6059569 := bstep (se 2 (by rfl) ⟨2272338, by rfl⟩ : syracuseStep 6059569 = 4544677) B4544677
theorem B12285539 : Blo 1594996 12285539 := bstep (se 1 (by rfl) ⟨9214154, by rfl⟩ : syracuseStep 12285539 = 18428309) B18428309
theorem B2692723 : Blo 1594996 2692723 := bstep (se 1 (by rfl) ⟨2019542, by rfl⟩ : syracuseStep 2692723 = 4039085) B4039085
theorem B1595011 : Blo 1594996 1595011 := bstep (se 1 (by rfl) ⟨1196258, by rfl⟩ : syracuseStep 1595011 = 2392517) B2392517
theorem B6813325 : Blo 1594996 6813325 := bstep (se 3 (by rfl) ⟨1277498, by rfl⟩ : syracuseStep 6813325 = 2554997) B2554997
theorem B12113549 : Blo 1594996 12113549 := bstep (se 3 (by rfl) ⟨2271290, by rfl⟩ : syracuseStep 12113549 = 4542581) B4542581
theorem B1595027 : Blo 1594996 1595027 := bstep (se 1 (by rfl) ⟨1196270, by rfl⟩ : syracuseStep 1595027 = 2392541) B2392541
theorem B1595043 : Blo 1594996 1595043 := bstep (se 1 (by rfl) ⟨1196282, by rfl⟩ : syracuseStep 1595043 = 2392565) B2392565
theorem B1595059 : Blo 1594996 1595059 := bstep (se 1 (by rfl) ⟨1196294, by rfl⟩ : syracuseStep 1595059 = 2392589) B2392589
theorem B1595075 : Blo 1594996 1595075 := bstep (se 1 (by rfl) ⟨1196306, by rfl⟩ : syracuseStep 1595075 = 2392613) B2392613
theorem B1595091 : Blo 1594996 1595091 := bstep (se 1 (by rfl) ⟨1196318, by rfl⟩ : syracuseStep 1595091 = 2392637) B2392637
theorem B1595107 : Blo 1594996 1595107 := bstep (se 1 (by rfl) ⟨1196330, by rfl⟩ : syracuseStep 1595107 = 2392661) B2392661
theorem B1595123 : Blo 1594996 1595123 := bstep (se 1 (by rfl) ⟨1196342, by rfl⟩ : syracuseStep 1595123 = 2392685) B2392685
theorem B2021107 : Blo 1594996 2021107 := bstep (se 1 (by rfl) ⟨1515830, by rfl⟩ : syracuseStep 2021107 = 3031661) B3031661
theorem B2692865 : Blo 1594996 2692865 := bstep (se 2 (by rfl) ⟨1009824, by rfl⟩ : syracuseStep 2692865 = 2019649) B2019649
theorem B1595139 : Blo 1594996 1595139 := bstep (se 1 (by rfl) ⟨1196354, by rfl⟩ : syracuseStep 1595139 = 2392709) B2392709
theorem B4855565 : Blo 1594996 4855565 := bstep (se 3 (by rfl) ⟨910418, by rfl⟩ : syracuseStep 4855565 = 1820837) B1820837
theorem B1595155 : Blo 1594996 1595155 := bstep (se 1 (by rfl) ⟨1196366, by rfl⟩ : syracuseStep 1595155 = 2392733) B2392733
theorem B1595171 : Blo 1594996 1595171 := bstep (se 1 (by rfl) ⟨1196378, by rfl⟩ : syracuseStep 1595171 = 2392757) B2392757
theorem B1595187 : Blo 1594996 1595187 := bstep (se 1 (by rfl) ⟨1196390, by rfl⟩ : syracuseStep 1595187 = 2392781) B2392781
theorem B1595203 : Blo 1594996 1595203 := bstep (se 1 (by rfl) ⟨1196402, by rfl⟩ : syracuseStep 1595203 = 2392805) B2392805
theorem B1595219 : Blo 1594996 1595219 := bstep (se 1 (by rfl) ⟨1196414, by rfl⟩ : syracuseStep 1595219 = 2392829) B2392829
theorem B1595235 : Blo 1594996 1595235 := bstep (se 1 (by rfl) ⟨1196426, by rfl⟩ : syracuseStep 1595235 = 2392853) B2392853
theorem B8083313 : Blo 1594996 8083313 := bstep (se 2 (by rfl) ⟨3031242, by rfl⟩ : syracuseStep 8083313 = 6062485) B6062485
theorem B1595251 : Blo 1594996 1595251 := bstep (se 1 (by rfl) ⟨1196438, by rfl⟩ : syracuseStep 1595251 = 2392877) B2392877
theorem B2692993 : Blo 1594996 2692993 := bstep (se 2 (by rfl) ⟨1009872, by rfl⟩ : syracuseStep 2692993 = 2019745) B2019745
theorem B1595267 : Blo 1594996 1595267 := bstep (se 1 (by rfl) ⟨1196450, by rfl⟩ : syracuseStep 1595267 = 2392901) B2392901
theorem B5388173 : Blo 1594996 5388173 := bstep (se 3 (by rfl) ⟨1010282, by rfl⟩ : syracuseStep 5388173 = 2020565) B2020565
theorem B1595283 : Blo 1594996 1595283 := bstep (se 1 (by rfl) ⟨1196462, by rfl⟩ : syracuseStep 1595283 = 2392925) B2392925
theorem B1595299 : Blo 1594996 1595299 := bstep (se 1 (by rfl) ⟨1196474, by rfl⟩ : syracuseStep 1595299 = 2392949) B2392949
theorem B2693027 : Blo 1594996 2693027 := bstep (se 1 (by rfl) ⟨2019770, by rfl⟩ : syracuseStep 2693027 = 4039541) B4039541
theorem B1595315 : Blo 1594996 1595315 := bstep (se 1 (by rfl) ⟨1196486, by rfl⟩ : syracuseStep 1595315 = 2392973) B2392973
theorem B1595331 : Blo 1594996 1595331 := bstep (se 1 (by rfl) ⟨1196498, by rfl⟩ : syracuseStep 1595331 = 2392997) B2392997
theorem B5388227 : Blo 1594996 5388227 := bstep (se 1 (by rfl) ⟨4041170, by rfl⟩ : syracuseStep 5388227 = 8082341) B8082341
theorem B8075213 : Blo 1594996 8075213 := bstep (se 3 (by rfl) ⟨1514102, by rfl⟩ : syracuseStep 8075213 = 3028205) B3028205
theorem B1595347 : Blo 1594996 1595347 := bstep (se 1 (by rfl) ⟨1196510, by rfl⟩ : syracuseStep 1595347 = 2393021) B2393021
theorem B1595363 : Blo 1594996 1595363 := bstep (se 1 (by rfl) ⟨1196522, by rfl⟩ : syracuseStep 1595363 = 2393045) B2393045
theorem B1595379 : Blo 1594996 1595379 := bstep (se 1 (by rfl) ⟨1196534, by rfl⟩ : syracuseStep 1595379 = 2393069) B2393069
theorem B1595395 : Blo 1594996 1595395 := bstep (se 1 (by rfl) ⟨1196546, by rfl⟩ : syracuseStep 1595395 = 2393093) B2393093
theorem B1595411 : Blo 1594996 1595411 := bstep (se 1 (by rfl) ⟨1196558, by rfl⟩ : syracuseStep 1595411 = 2393117) B2393117
theorem B1595427 : Blo 1594996 1595427 := bstep (se 1 (by rfl) ⟨1196570, by rfl⟩ : syracuseStep 1595427 = 2393141) B2393141
theorem B2693155 : Blo 1594996 2693155 := bstep (se 1 (by rfl) ⟨2019866, by rfl⟩ : syracuseStep 2693155 = 4039733) B4039733
theorem B1595443 : Blo 1594996 1595443 := bstep (se 1 (by rfl) ⟨1196582, by rfl⟩ : syracuseStep 1595443 = 2393165) B2393165
theorem B29104181 : Blo 1594996 29104181 := bstep (se 5 (by rfl) ⟨1364258, by rfl⟩ : syracuseStep 29104181 = 2728517) B2728517
theorem B1595459 : Blo 1594996 1595459 := bstep (se 1 (by rfl) ⟨1196594, by rfl⟩ : syracuseStep 1595459 = 2393189) B2393189
theorem B1595475 : Blo 1594996 1595475 := bstep (se 1 (by rfl) ⟨1196606, by rfl⟩ : syracuseStep 1595475 = 2393213) B2393213
theorem B1595491 : Blo 1594996 1595491 := bstep (se 1 (by rfl) ⟨1196618, by rfl⟩ : syracuseStep 1595491 = 2393237) B2393237
theorem B1595507 : Blo 1594996 1595507 := bstep (se 1 (by rfl) ⟨1196630, by rfl⟩ : syracuseStep 1595507 = 2393261) B2393261
theorem B1595523 : Blo 1594996 1595523 := bstep (se 1 (by rfl) ⟨1196642, by rfl⟩ : syracuseStep 1595523 = 2393285) B2393285
theorem B1595539 : Blo 1594996 1595539 := bstep (se 1 (by rfl) ⟨1196654, by rfl⟩ : syracuseStep 1595539 = 2393309) B2393309
theorem B1595555 : Blo 1594996 1595555 := bstep (se 1 (by rfl) ⟨1196666, by rfl⟩ : syracuseStep 1595555 = 2393333) B2393333
theorem B2693297 : Blo 1594996 2693297 := bstep (se 2 (by rfl) ⟨1009986, by rfl⟩ : syracuseStep 2693297 = 2019973) B2019973
theorem B1595571 : Blo 1594996 1595571 := bstep (se 1 (by rfl) ⟨1196678, by rfl⟩ : syracuseStep 1595571 = 2393357) B2393357
theorem B1595587 : Blo 1594996 1595587 := bstep (se 1 (by rfl) ⟨1196690, by rfl⟩ : syracuseStep 1595587 = 2393381) B2393381
theorem B5388497 : Blo 1594996 5388497 := bstep (se 2 (by rfl) ⟨2020686, by rfl⟩ : syracuseStep 5388497 = 4041373) B4041373
theorem B1595603 : Blo 1594996 1595603 := bstep (se 1 (by rfl) ⟨1196702, by rfl⟩ : syracuseStep 1595603 = 2393405) B2393405
theorem B1595619 : Blo 1594996 1595619 := bstep (se 1 (by rfl) ⟨1196714, by rfl⟩ : syracuseStep 1595619 = 2393429) B2393429
theorem B1595635 : Blo 1594996 1595635 := bstep (se 1 (by rfl) ⟨1196726, by rfl⟩ : syracuseStep 1595635 = 2393453) B2393453
theorem B1595651 : Blo 1594996 1595651 := bstep (se 1 (by rfl) ⟨1196738, by rfl⟩ : syracuseStep 1595651 = 2393477) B2393477
theorem B4921613 : Blo 1594996 4921613 := bstep (se 3 (by rfl) ⟨922802, by rfl⟩ : syracuseStep 4921613 = 1845605) B1845605
theorem B1595667 : Blo 1594996 1595667 := bstep (se 1 (by rfl) ⟨1196750, by rfl⟩ : syracuseStep 1595667 = 2393501) B2393501
theorem B1595683 : Blo 1594996 1595683 := bstep (se 1 (by rfl) ⟨1196762, by rfl⟩ : syracuseStep 1595683 = 2393525) B2393525
theorem B2693425 : Blo 1594996 2693425 := bstep (se 2 (by rfl) ⟨1010034, by rfl⟩ : syracuseStep 2693425 = 2020069) B2020069
theorem B1595699 : Blo 1594996 1595699 := bstep (se 1 (by rfl) ⟨1196774, by rfl⟩ : syracuseStep 1595699 = 2393549) B2393549
theorem B1595715 : Blo 1594996 1595715 := bstep (se 1 (by rfl) ⟨1196786, by rfl⟩ : syracuseStep 1595715 = 2393573) B2393573
theorem B3029329 : Blo 1594996 3029329 := bstep (se 2 (by rfl) ⟨1135998, by rfl⟩ : syracuseStep 3029329 = 2271997) B2271997
theorem B4544849 : Blo 1594996 4544849 := bstep (se 2 (by rfl) ⟨1704318, by rfl⟩ : syracuseStep 4544849 = 3408637) B3408637
theorem B1595731 : Blo 1594996 1595731 := bstep (se 1 (by rfl) ⟨1196798, by rfl⟩ : syracuseStep 1595731 = 2393597) B2393597
theorem B2693459 : Blo 1594996 2693459 := bstep (se 1 (by rfl) ⟨2020094, by rfl⟩ : syracuseStep 2693459 = 4040189) B4040189
theorem B1595747 : Blo 1594996 1595747 := bstep (se 1 (by rfl) ⟨1196810, by rfl⟩ : syracuseStep 1595747 = 2393621) B2393621
theorem B1595763 : Blo 1594996 1595763 := bstep (se 1 (by rfl) ⟨1196822, by rfl⟩ : syracuseStep 1595763 = 2393645) B2393645
theorem B1595779 : Blo 1594996 1595779 := bstep (se 1 (by rfl) ⟨1196834, by rfl⟩ : syracuseStep 1595779 = 2393669) B2393669
theorem B1595795 : Blo 1594996 1595795 := bstep (se 1 (by rfl) ⟨1196846, by rfl⟩ : syracuseStep 1595795 = 2393693) B2393693
theorem B1595811 : Blo 1594996 1595811 := bstep (se 1 (by rfl) ⟨1196858, by rfl⟩ : syracuseStep 1595811 = 2393717) B2393717
theorem B1595827 : Blo 1594996 1595827 := bstep (se 1 (by rfl) ⟨1196870, by rfl⟩ : syracuseStep 1595827 = 2393741) B2393741
theorem B1595843 : Blo 1594996 1595843 := bstep (se 1 (by rfl) ⟨1196882, by rfl⟩ : syracuseStep 1595843 = 2393765) B2393765
theorem B1595859 : Blo 1594996 1595859 := bstep (se 1 (by rfl) ⟨1196894, by rfl⟩ : syracuseStep 1595859 = 2393789) B2393789
theorem B2693587 : Blo 1594996 2693587 := bstep (se 1 (by rfl) ⟨2020190, by rfl⟩ : syracuseStep 2693587 = 4040381) B4040381
theorem B1595875 : Blo 1594996 1595875 := bstep (se 1 (by rfl) ⟨1196906, by rfl⟩ : syracuseStep 1595875 = 2393813) B2393813
theorem B1595891 : Blo 1594996 1595891 := bstep (se 1 (by rfl) ⟨1196918, by rfl⟩ : syracuseStep 1595891 = 2393837) B2393837
theorem B1595907 : Blo 1594996 1595907 := bstep (se 1 (by rfl) ⟨1196930, by rfl⟩ : syracuseStep 1595907 = 2393861) B2393861
theorem B1595923 : Blo 1594996 1595923 := bstep (se 1 (by rfl) ⟨1196942, by rfl⟩ : syracuseStep 1595923 = 2393885) B2393885
theorem B1595939 : Blo 1594996 1595939 := bstep (se 1 (by rfl) ⟨1196954, by rfl⟩ : syracuseStep 1595939 = 2393909) B2393909
theorem B1595955 : Blo 1594996 1595955 := bstep (se 1 (by rfl) ⟨1196966, by rfl⟩ : syracuseStep 1595955 = 2393933) B2393933
theorem B1595971 : Blo 1594996 1595971 := bstep (se 1 (by rfl) ⟨1196978, by rfl⟩ : syracuseStep 1595971 = 2393957) B2393957
theorem B1595987 : Blo 1594996 1595987 := bstep (se 1 (by rfl) ⟨1196990, by rfl⟩ : syracuseStep 1595987 = 2393981) B2393981
theorem B2693729 : Blo 1594996 2693729 := bstep (se 2 (by rfl) ⟨1010148, by rfl⟩ : syracuseStep 2693729 = 2020297) B2020297
theorem B1596003 : Blo 1594996 1596003 := bstep (se 1 (by rfl) ⟨1197002, by rfl⟩ : syracuseStep 1596003 = 2394005) B2394005
theorem B8190563 : Blo 1594996 8190563 := bstep (se 1 (by rfl) ⟨6142922, by rfl⟩ : syracuseStep 8190563 = 12285845) B12285845
theorem B1596019 : Blo 1594996 1596019 := bstep (se 1 (by rfl) ⟨1197014, by rfl⟩ : syracuseStep 1596019 = 2394029) B2394029
theorem B1596035 : Blo 1594996 1596035 := bstep (se 1 (by rfl) ⟨1197026, by rfl⟩ : syracuseStep 1596035 = 2394053) B2394053
theorem B1596051 : Blo 1594996 1596051 := bstep (se 1 (by rfl) ⟨1197038, by rfl⟩ : syracuseStep 1596051 = 2394077) B2394077
theorem B1596067 : Blo 1594996 1596067 := bstep (se 1 (by rfl) ⟨1197050, by rfl⟩ : syracuseStep 1596067 = 2394101) B2394101
theorem B1596083 : Blo 1594996 1596083 := bstep (se 1 (by rfl) ⟨1197062, by rfl⟩ : syracuseStep 1596083 = 2394125) B2394125
theorem B1596099 : Blo 1594996 1596099 := bstep (se 1 (by rfl) ⟨1197074, by rfl⟩ : syracuseStep 1596099 = 2394149) B2394149
theorem B1596115 : Blo 1594996 1596115 := bstep (se 1 (by rfl) ⟨1197086, by rfl⟩ : syracuseStep 1596115 = 2394173) B2394173
theorem B2693857 : Blo 1594996 2693857 := bstep (se 2 (by rfl) ⟨1010196, by rfl⟩ : syracuseStep 2693857 = 2020393) B2020393
theorem B1596131 : Blo 1594996 1596131 := bstep (se 1 (by rfl) ⟨1197098, by rfl⟩ : syracuseStep 1596131 = 2394197) B2394197
theorem B5389037 : Blo 1594996 5389037 := bstep (se 3 (by rfl) ⟨1010444, by rfl⟩ : syracuseStep 5389037 = 2020889) B2020889
theorem B1596147 : Blo 1594996 1596147 := bstep (se 1 (by rfl) ⟨1197110, by rfl⟩ : syracuseStep 1596147 = 2394221) B2394221
theorem B1596163 : Blo 1594996 1596163 := bstep (se 1 (by rfl) ⟨1197122, by rfl⟩ : syracuseStep 1596163 = 2394245) B2394245
theorem B2693891 : Blo 1594996 2693891 := bstep (se 1 (by rfl) ⟨2020418, by rfl⟩ : syracuseStep 2693891 = 4040837) B4040837
theorem B1596179 : Blo 1594996 1596179 := bstep (se 1 (by rfl) ⟨1197134, by rfl⟩ : syracuseStep 1596179 = 2394269) B2394269
theorem B1596195 : Blo 1594996 1596195 := bstep (se 1 (by rfl) ⟨1197146, by rfl⟩ : syracuseStep 1596195 = 2394293) B2394293
theorem B5389091 : Blo 1594996 5389091 := bstep (se 1 (by rfl) ⟨4041818, by rfl⟩ : syracuseStep 5389091 = 8083637) B8083637
theorem B1596211 : Blo 1594996 1596211 := bstep (se 1 (by rfl) ⟨1197158, by rfl⟩ : syracuseStep 1596211 = 2394317) B2394317
theorem B24558389 : Blo 1594996 24558389 := bstep (se 5 (by rfl) ⟨1151174, by rfl⟩ : syracuseStep 24558389 = 2302349) B2302349
theorem B1596227 : Blo 1594996 1596227 := bstep (se 1 (by rfl) ⟨1197170, by rfl⟩ : syracuseStep 1596227 = 2394341) B2394341
theorem B5110609 : Blo 1594996 5110609 := bstep (se 2 (by rfl) ⟨1916478, by rfl⟩ : syracuseStep 5110609 = 3832957) B3832957
theorem B1596243 : Blo 1594996 1596243 := bstep (se 1 (by rfl) ⟨1197182, by rfl⟩ : syracuseStep 1596243 = 2394365) B2394365
theorem B1596259 : Blo 1594996 1596259 := bstep (se 1 (by rfl) ⟨1197194, by rfl⟩ : syracuseStep 1596259 = 2394389) B2394389
theorem B1596275 : Blo 1594996 1596275 := bstep (se 1 (by rfl) ⟨1197206, by rfl⟩ : syracuseStep 1596275 = 2394413) B2394413
theorem B1596291 : Blo 1594996 1596291 := bstep (se 1 (by rfl) ⟨1197218, by rfl⟩ : syracuseStep 1596291 = 2394437) B2394437
theorem B2694019 : Blo 1594996 2694019 := bstep (se 1 (by rfl) ⟨2020514, by rfl⟩ : syracuseStep 2694019 = 4041029) B4041029
theorem B1596307 : Blo 1594996 1596307 := bstep (se 1 (by rfl) ⟨1197230, by rfl⟩ : syracuseStep 1596307 = 2394461) B2394461
theorem B5749667 : Blo 1594996 5749667 := bstep (se 1 (by rfl) ⟨4312250, by rfl⟩ : syracuseStep 5749667 = 8624501) B8624501
theorem B1596323 : Blo 1594996 1596323 := bstep (se 1 (by rfl) ⟨1197242, by rfl⟩ : syracuseStep 1596323 = 2394485) B2394485
theorem B1596339 : Blo 1594996 1596339 := bstep (se 1 (by rfl) ⟨1197254, by rfl⟩ : syracuseStep 1596339 = 2394509) B2394509
theorem B1596355 : Blo 1594996 1596355 := bstep (se 1 (by rfl) ⟨1197266, by rfl⟩ : syracuseStep 1596355 = 2394533) B2394533
theorem B1596371 : Blo 1594996 1596371 := bstep (se 1 (by rfl) ⟨1197278, by rfl⟩ : syracuseStep 1596371 = 2394557) B2394557
theorem B6061027 : Blo 1594996 6061027 := bstep (se 1 (by rfl) ⟨4545770, by rfl⟩ : syracuseStep 6061027 = 9091541) B9091541
theorem B1596387 : Blo 1594996 1596387 := bstep (se 1 (by rfl) ⟨1197290, by rfl⟩ : syracuseStep 1596387 = 2394581) B2394581
theorem B4545521 : Blo 1594996 4545521 := bstep (se 2 (by rfl) ⟨1704570, by rfl⟩ : syracuseStep 4545521 = 3409141) B3409141
theorem B1596403 : Blo 1594996 1596403 := bstep (se 1 (by rfl) ⟨1197302, by rfl⟩ : syracuseStep 1596403 = 2394605) B2394605
theorem B1596419 : Blo 1594996 1596419 := bstep (se 1 (by rfl) ⟨1197314, by rfl⟩ : syracuseStep 1596419 = 2394629) B2394629
theorem B13630477 : Blo 1594996 13630477 := bstep (se 3 (by rfl) ⟨2555714, by rfl⟩ : syracuseStep 13630477 = 5111429) B5111429
theorem B2694161 : Blo 1594996 2694161 := bstep (se 2 (by rfl) ⟨1010310, by rfl⟩ : syracuseStep 2694161 = 2020621) B2020621
theorem B1596435 : Blo 1594996 1596435 := bstep (se 1 (by rfl) ⟨1197326, by rfl⟩ : syracuseStep 1596435 = 2394653) B2394653
theorem B1596451 : Blo 1594996 1596451 := bstep (se 1 (by rfl) ⟨1197338, by rfl⟩ : syracuseStep 1596451 = 2394677) B2394677
theorem B5389361 : Blo 1594996 5389361 := bstep (se 2 (by rfl) ⟨2021010, by rfl⟩ : syracuseStep 5389361 = 4042021) B4042021
theorem B1596467 : Blo 1594996 1596467 := bstep (se 1 (by rfl) ⟨1197350, by rfl⟩ : syracuseStep 1596467 = 2394701) B2394701
theorem B1596483 : Blo 1594996 1596483 := bstep (se 1 (by rfl) ⟨1197362, by rfl⟩ : syracuseStep 1596483 = 2394725) B2394725
theorem B1596499 : Blo 1594996 1596499 := bstep (se 1 (by rfl) ⟨1197374, by rfl⟩ : syracuseStep 1596499 = 2394749) B2394749
theorem B1596515 : Blo 1594996 1596515 := bstep (se 1 (by rfl) ⟨1197386, by rfl⟩ : syracuseStep 1596515 = 2394773) B2394773
theorem B1596531 : Blo 1594996 1596531 := bstep (se 1 (by rfl) ⟨1197398, by rfl⟩ : syracuseStep 1596531 = 2394797) B2394797
theorem B1596547 : Blo 1594996 1596547 := bstep (se 1 (by rfl) ⟨1197410, by rfl⟩ : syracuseStep 1596547 = 2394821) B2394821
theorem B2694289 : Blo 1594996 2694289 := bstep (se 2 (by rfl) ⟨1010358, by rfl⟩ : syracuseStep 2694289 = 2020717) B2020717
theorem B1596563 : Blo 1594996 1596563 := bstep (se 1 (by rfl) ⟨1197422, by rfl⟩ : syracuseStep 1596563 = 2394845) B2394845
theorem B1596579 : Blo 1594996 1596579 := bstep (se 1 (by rfl) ⟨1197434, by rfl⟩ : syracuseStep 1596579 = 2394869) B2394869
theorem B4037809 : Blo 1594996 4037809 := bstep (se 2 (by rfl) ⟨1514178, by rfl⟩ : syracuseStep 4037809 = 3028357) B3028357
theorem B1596595 : Blo 1594996 1596595 := bstep (se 1 (by rfl) ⟨1197446, by rfl⟩ : syracuseStep 1596595 = 2394893) B2394893
theorem B2694323 : Blo 1594996 2694323 := bstep (se 1 (by rfl) ⟨2020742, by rfl⟩ : syracuseStep 2694323 = 4041485) B4041485
theorem B1596611 : Blo 1594996 1596611 := bstep (se 1 (by rfl) ⟨1197458, by rfl⟩ : syracuseStep 1596611 = 2394917) B2394917
theorem B1596627 : Blo 1594996 1596627 := bstep (se 1 (by rfl) ⟨1197470, by rfl⟩ : syracuseStep 1596627 = 2394941) B2394941
theorem B1596643 : Blo 1594996 1596643 := bstep (se 1 (by rfl) ⟨1197482, by rfl⟩ : syracuseStep 1596643 = 2394965) B2394965
theorem B1596659 : Blo 1594996 1596659 := bstep (se 1 (by rfl) ⟨1197494, by rfl⟩ : syracuseStep 1596659 = 2394989) B2394989
theorem B1596675 : Blo 1594996 1596675 := bstep (se 1 (by rfl) ⟨1197506, by rfl⟩ : syracuseStep 1596675 = 2395013) B2395013
theorem B1596691 : Blo 1594996 1596691 := bstep (se 1 (by rfl) ⟨1197518, by rfl⟩ : syracuseStep 1596691 = 2395037) B2395037
theorem B1596707 : Blo 1594996 1596707 := bstep (se 1 (by rfl) ⟨1197530, by rfl⟩ : syracuseStep 1596707 = 2395061) B2395061
theorem B8084771 : Blo 1594996 8084771 := bstep (se 1 (by rfl) ⟨6063578, by rfl⟩ : syracuseStep 8084771 = 12127157) B12127157
theorem B2694451 : Blo 1594996 2694451 := bstep (se 1 (by rfl) ⟨2020838, by rfl⟩ : syracuseStep 2694451 = 4041677) B4041677
theorem B1596723 : Blo 1594996 1596723 := bstep (se 1 (by rfl) ⟨1197542, by rfl⟩ : syracuseStep 1596723 = 2395085) B2395085
theorem B1596739 : Blo 1594996 1596739 := bstep (se 1 (by rfl) ⟨1197554, by rfl⟩ : syracuseStep 1596739 = 2395109) B2395109
theorem B1596755 : Blo 1594996 1596755 := bstep (se 1 (by rfl) ⟨1197566, by rfl⟩ : syracuseStep 1596755 = 2395133) B2395133
theorem B1596771 : Blo 1594996 1596771 := bstep (se 1 (by rfl) ⟨1197578, by rfl⟩ : syracuseStep 1596771 = 2395157) B2395157
theorem B5750129 : Blo 1594996 5750129 := bstep (se 2 (by rfl) ⟨2156298, by rfl⟩ : syracuseStep 5750129 = 4312597) B4312597
theorem B3030385 : Blo 1594996 3030385 := bstep (se 2 (by rfl) ⟨1136394, by rfl⟩ : syracuseStep 3030385 = 2272789) B2272789
theorem B1596787 : Blo 1594996 1596787 := bstep (se 1 (by rfl) ⟨1197590, by rfl⟩ : syracuseStep 1596787 = 2395181) B2395181
theorem B1596803 : Blo 1594996 1596803 := bstep (se 1 (by rfl) ⟨1197602, by rfl⟩ : syracuseStep 1596803 = 2395205) B2395205
theorem B1596819 : Blo 1594996 1596819 := bstep (se 1 (by rfl) ⟨1197614, by rfl⟩ : syracuseStep 1596819 = 2395229) B2395229
theorem B1596835 : Blo 1594996 1596835 := bstep (se 1 (by rfl) ⟨1197626, by rfl⟩ : syracuseStep 1596835 = 2395253) B2395253
theorem B1596851 : Blo 1594996 1596851 := bstep (se 1 (by rfl) ⟨1197638, by rfl⟩ : syracuseStep 1596851 = 2395277) B2395277
theorem B2694593 : Blo 1594996 2694593 := bstep (se 2 (by rfl) ⟨1010472, by rfl⟩ : syracuseStep 2694593 = 2020945) B2020945
theorem B4038083 : Blo 1594996 4038083 := bstep (se 1 (by rfl) ⟨3028562, by rfl⟩ : syracuseStep 4038083 = 6057125) B6057125
theorem B1596867 : Blo 1594996 1596867 := bstep (se 1 (by rfl) ⟨1197650, by rfl⟩ : syracuseStep 1596867 = 2395301) B2395301
theorem B1596883 : Blo 1594996 1596883 := bstep (se 1 (by rfl) ⟨1197662, by rfl⟩ : syracuseStep 1596883 = 2395325) B2395325
theorem B1596899 : Blo 1594996 1596899 := bstep (se 1 (by rfl) ⟨1197674, by rfl⟩ : syracuseStep 1596899 = 2395349) B2395349
theorem B1596915 : Blo 1594996 1596915 := bstep (se 1 (by rfl) ⟨1197686, by rfl⟩ : syracuseStep 1596915 = 2395373) B2395373
theorem B1596931 : Blo 1594996 1596931 := bstep (se 1 (by rfl) ⟨1197698, by rfl⟩ : syracuseStep 1596931 = 2395397) B2395397
theorem B10223117 : Blo 1594996 10223117 := bstep (se 3 (by rfl) ⟨1916834, by rfl⟩ : syracuseStep 10223117 = 3833669) B3833669
theorem B1596947 : Blo 1594996 1596947 := bstep (se 1 (by rfl) ⟨1197710, by rfl⟩ : syracuseStep 1596947 = 2395421) B2395421
theorem B1596963 : Blo 1594996 1596963 := bstep (se 1 (by rfl) ⟨1197722, by rfl⟩ : syracuseStep 1596963 = 2395445) B2395445
theorem B1596979 : Blo 1594996 1596979 := bstep (se 1 (by rfl) ⟨1197734, by rfl⟩ : syracuseStep 1596979 = 2395469) B2395469
theorem B2694721 : Blo 1594996 2694721 := bstep (se 2 (by rfl) ⟨1010520, by rfl⟩ : syracuseStep 2694721 = 2021041) B2021041
theorem B2555459 : Blo 1594996 2555459 := bstep (se 1 (by rfl) ⟨1916594, by rfl⟩ : syracuseStep 2555459 = 3833189) B3833189
theorem B1596995 : Blo 1594996 1596995 := bstep (se 1 (by rfl) ⟨1197746, by rfl⟩ : syracuseStep 1596995 = 2395493) B2395493
theorem B2694755 : Blo 1594996 2694755 := bstep (se 1 (by rfl) ⟨2021066, by rfl⟩ : syracuseStep 2694755 = 4042133) B4042133
theorem B4038275 : Blo 1594996 4038275 := bstep (se 1 (by rfl) ⟨3028706, by rfl⟩ : syracuseStep 4038275 = 6057413) B6057413
theorem B2555555 : Blo 1594996 2555555 := bstep (se 1 (by rfl) ⟨1916666, by rfl⟩ : syracuseStep 2555555 = 3833333) B3833333
theorem B2555587 : Blo 1594996 2555587 := bstep (se 1 (by rfl) ⟨1916690, by rfl⟩ : syracuseStep 2555587 = 3833381) B3833381
theorem B2694883 : Blo 1594996 2694883 := bstep (se 1 (by rfl) ⟨2021162, by rfl⟩ : syracuseStep 2694883 = 4042325) B4042325
theorem B11501297 : Blo 1594996 11501297 := bstep (se 2 (by rfl) ⟨4312986, by rfl⟩ : syracuseStep 11501297 = 8625973) B8625973
theorem B4431601 : Blo 1594996 4431601 := bstep (se 2 (by rfl) ⟨1661850, by rfl⟩ : syracuseStep 4431601 = 3323701) B3323701
theorem B3030787 : Blo 1594996 3030787 := bstep (se 1 (by rfl) ⟨2273090, by rfl⟩ : syracuseStep 3030787 = 4546181) B4546181
theorem B4546307 : Blo 1594996 4546307 := bstep (se 1 (by rfl) ⟨3409730, by rfl⟩ : syracuseStep 4546307 = 6819461) B6819461
theorem B9084707 : Blo 1594996 9084707 := bstep (se 1 (by rfl) ⟨6813530, by rfl⟩ : syracuseStep 9084707 = 13627061) B13627061
theorem B3030833 : Blo 1594996 3030833 := bstep (se 2 (by rfl) ⟨1136562, by rfl⟩ : syracuseStep 3030833 = 2273125) B2273125
theorem B21831605 : Blo 1594996 21831605 := bstep (se 5 (by rfl) ⟨1023356, by rfl⟩ : syracuseStep 21831605 = 2046713) B2046713
theorem B15335365 : Blo 1594996 15335365 := bstep (se 4 (by rfl) ⟨1437690, by rfl⟩ : syracuseStep 15335365 = 2875381) B2875381
theorem B3407825 : Blo 1594996 3407825 := bstep (se 2 (by rfl) ⟨1277934, by rfl⟩ : syracuseStep 3407825 = 2555869) B2555869
theorem B8306705 : Blo 1594996 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B58245155 : Blo 1594996 58245155 := bstep (se 1 (by rfl) ⟨43683866, by rfl⟩ : syracuseStep 58245155 = 87367733) B87367733
theorem B3031091 : Blo 1594996 3031091 := bstep (se 1 (by rfl) ⟨2273318, by rfl⟩ : syracuseStep 3031091 = 4546637) B4546637
theorem B4038731 : Blo 1594996 4038731 := bstep (se 1 (by rfl) ⟨3029048, by rfl⟩ : syracuseStep 4038731 = 6058097) B6058097
theorem B6062273 : Blo 1594996 6062273 := bstep (se 2 (by rfl) ⟨2273352, by rfl⟩ : syracuseStep 6062273 = 4546705) B4546705
theorem B4546763 : Blo 1594996 4546763 := bstep (se 1 (by rfl) ⟨3410072, by rfl⟩ : syracuseStep 4546763 = 6820145) B6820145
theorem B5185739 : Blo 1594996 5185739 := bstep (se 1 (by rfl) ⟨3889304, by rfl⟩ : syracuseStep 5185739 = 7778609) B7778609
theorem B3031319 : Blo 1594996 3031319 := bstep (se 1 (by rfl) ⟨2273489, by rfl⟩ : syracuseStep 3031319 = 4546979) B4546979
theorem B1794379 : Blo 1594996 1794379 := bstep (se 1 (by rfl) ⟨1345784, by rfl⟩ : syracuseStep 1794379 = 2691569) B2691569
theorem B8077643 : Blo 1594996 8077643 := bstep (se 1 (by rfl) ⟨6058232, by rfl⟩ : syracuseStep 8077643 = 12116465) B12116465
theorem B1704331 : Blo 1594996 1704331 := bstep (se 1 (by rfl) ⟨1278248, by rfl⟩ : syracuseStep 1704331 = 2556497) B2556497
theorem B1794487 : Blo 1594996 1794487 := bstep (se 1 (by rfl) ⟨1345865, by rfl⟩ : syracuseStep 1794487 = 2691731) B2691731
theorem B4039105 : Blo 1594996 4039105 := bstep (se 2 (by rfl) ⟨1514664, by rfl⟩ : syracuseStep 4039105 = 3029329) B3029329
theorem B2392523 : Blo 1594996 2392523 := bstep (se 1 (by rfl) ⟨1794392, by rfl⟩ : syracuseStep 2392523 = 3588785) B3588785
theorem B2392535 : Blo 1594996 2392535 := bstep (se 1 (by rfl) ⟨1794401, by rfl⟩ : syracuseStep 2392535 = 3588803) B3588803
theorem B10224089 : Blo 1594996 10224089 := bstep (se 2 (by rfl) ⟨3834033, by rfl⟩ : syracuseStep 10224089 = 7668067) B7668067
theorem B2392601 : Blo 1594996 2392601 := bstep (se 2 (by rfl) ⟨897225, by rfl⟩ : syracuseStep 2392601 = 1794451) B1794451
theorem B3031577 : Blo 1594996 3031577 := bstep (se 2 (by rfl) ⟨1136841, by rfl⟩ : syracuseStep 3031577 = 2273683) B2273683
theorem B9093707 : Blo 1594996 9093707 := bstep (se 1 (by rfl) ⟨6820280, by rfl⟩ : syracuseStep 9093707 = 13640561) B13640561
theorem B1794667 : Blo 1594996 1794667 := bstep (se 1 (by rfl) ⟨1346000, by rfl⟩ : syracuseStep 1794667 = 2692001) B2692001
theorem B2392715 : Blo 1594996 2392715 := bstep (se 1 (by rfl) ⟨1794536, by rfl⟩ : syracuseStep 2392715 = 3589073) B3589073
theorem B2392727 : Blo 1594996 2392727 := bstep (se 1 (by rfl) ⟨1794545, by rfl⟩ : syracuseStep 2392727 = 3589091) B3589091
theorem B1794775 : Blo 1594996 1794775 := bstep (se 1 (by rfl) ⟨1346081, by rfl⟩ : syracuseStep 1794775 = 2692163) B2692163
theorem B2392793 : Blo 1594996 2392793 := bstep (se 2 (by rfl) ⟨897297, by rfl⟩ : syracuseStep 2392793 = 1794595) B1794595
theorem B7480067 : Blo 1594996 7480067 := bstep (se 1 (by rfl) ⟨5610050, by rfl⟩ : syracuseStep 7480067 = 11220101) B11220101
theorem B3588875 : Blo 1594996 3588875 := bstep (se 1 (by rfl) ⟨2691656, by rfl⟩ : syracuseStep 3588875 = 5383313) B5383313
theorem B3588929 : Blo 1594996 3588929 := bstep (se 2 (by rfl) ⟨1345848, by rfl⟩ : syracuseStep 3588929 = 2691697) B2691697
theorem B2392907 : Blo 1594996 2392907 := bstep (se 1 (by rfl) ⟨1794680, by rfl⟩ : syracuseStep 2392907 = 3589361) B3589361
theorem B2392919 : Blo 1594996 2392919 := bstep (se 1 (by rfl) ⟨1794689, by rfl⟩ : syracuseStep 2392919 = 3589379) B3589379
theorem B12936037 : Blo 1594996 12936037 := bstep (se 4 (by rfl) ⟨1212753, by rfl⟩ : syracuseStep 12936037 = 2425507) B2425507
theorem B1794955 : Blo 1594996 1794955 := bstep (se 1 (by rfl) ⟨1346216, by rfl⟩ : syracuseStep 1794955 = 2692433) B2692433
theorem B2392985 : Blo 1594996 2392985 := bstep (se 2 (by rfl) ⟨897369, by rfl⟩ : syracuseStep 2392985 = 1794739) B1794739
theorem B3072971 : Blo 1594996 3072971 := bstep (se 1 (by rfl) ⟨2304728, by rfl⟩ : syracuseStep 3072971 = 4609457) B4609457
theorem B13632461 : Blo 1594996 13632461 := bstep (se 3 (by rfl) ⟨2556086, by rfl⟩ : syracuseStep 13632461 = 5112173) B5112173
theorem B1795063 : Blo 1594996 1795063 := bstep (se 1 (by rfl) ⟨1346297, by rfl⟩ : syracuseStep 1795063 = 2692595) B2692595
theorem B2393099 : Blo 1594996 2393099 := bstep (se 1 (by rfl) ⟨1794824, by rfl⟩ : syracuseStep 2393099 = 3589649) B3589649
theorem B2393111 : Blo 1594996 2393111 := bstep (se 1 (by rfl) ⟨1794833, by rfl⟩ : syracuseStep 2393111 = 3589667) B3589667
theorem B4039703 : Blo 1594996 4039703 := bstep (se 1 (by rfl) ⟨3029777, by rfl⟩ : syracuseStep 4039703 = 6059555) B6059555
theorem B3589145 : Blo 1594996 3589145 := bstep (se 2 (by rfl) ⟨1345929, by rfl⟩ : syracuseStep 3589145 = 2691859) B2691859
theorem B2393177 : Blo 1594996 2393177 := bstep (se 2 (by rfl) ⟨897441, by rfl⟩ : syracuseStep 2393177 = 1794883) B1794883
theorem B3589235 : Blo 1594996 3589235 := bstep (se 1 (by rfl) ⟨2691926, by rfl⟩ : syracuseStep 3589235 = 5383853) B5383853
theorem B3589271 : Blo 1594996 3589271 := bstep (se 1 (by rfl) ⟨2691953, by rfl⟩ : syracuseStep 3589271 = 5383907) B5383907
theorem B1795243 : Blo 1594996 1795243 := bstep (se 1 (by rfl) ⟨1346432, by rfl⟩ : syracuseStep 1795243 = 2692865) B2692865
theorem B3237043 : Blo 1594996 3237043 := bstep (se 1 (by rfl) ⟨2427782, by rfl⟩ : syracuseStep 3237043 = 4855565) B4855565
theorem B2393291 : Blo 1594996 2393291 := bstep (se 1 (by rfl) ⟨1794968, by rfl⟩ : syracuseStep 2393291 = 3589937) B3589937
theorem B2393303 : Blo 1594996 2393303 := bstep (se 1 (by rfl) ⟨1794977, by rfl⟩ : syracuseStep 2393303 = 3589955) B3589955
theorem B2557145 : Blo 1594996 2557145 := bstep (se 2 (by rfl) ⟨958929, by rfl⟩ : syracuseStep 2557145 = 1917859) B1917859
theorem B1705207 : Blo 1594996 1705207 := bstep (se 1 (by rfl) ⟨1278905, by rfl⟩ : syracuseStep 1705207 = 2557811) B2557811
theorem B1795351 : Blo 1594996 1795351 := bstep (se 1 (by rfl) ⟨1346513, by rfl⟩ : syracuseStep 1795351 = 2693027) B2693027
theorem B2393369 : Blo 1594996 2393369 := bstep (se 2 (by rfl) ⟨897513, by rfl⟩ : syracuseStep 2393369 = 1795027) B1795027
theorem B5383475 : Blo 1594996 5383475 := bstep (se 1 (by rfl) ⟨4037606, by rfl⟩ : syracuseStep 5383475 = 8075213) B8075213
theorem B2876737 : Blo 1594996 2876737 := bstep (se 2 (by rfl) ⟨1078776, by rfl⟩ : syracuseStep 2876737 = 2157553) B2157553
theorem B3589451 : Blo 1594996 3589451 := bstep (se 1 (by rfl) ⟨2692088, by rfl⟩ : syracuseStep 3589451 = 5384177) B5384177
theorem B3589505 : Blo 1594996 3589505 := bstep (se 2 (by rfl) ⟨1346064, by rfl⟩ : syracuseStep 3589505 = 2692129) B2692129
theorem B2393483 : Blo 1594996 2393483 := bstep (se 1 (by rfl) ⟨1795112, by rfl⟩ : syracuseStep 2393483 = 3590225) B3590225
theorem B2393495 : Blo 1594996 2393495 := bstep (se 1 (by rfl) ⟨1795121, by rfl⟩ : syracuseStep 2393495 = 3590243) B3590243
theorem B4097459 : Blo 1594996 4097459 := bstep (se 1 (by rfl) ⟨3073094, by rfl⟩ : syracuseStep 4097459 = 6146189) B6146189
theorem B1795531 : Blo 1594996 1795531 := bstep (se 1 (by rfl) ⟨1346648, by rfl⟩ : syracuseStep 1795531 = 2693297) B2693297
theorem B2393561 : Blo 1594996 2393561 := bstep (se 2 (by rfl) ⟨897585, by rfl⟩ : syracuseStep 2393561 = 1795171) B1795171
theorem B437061091 : Blo 1594996 437061091 := bstep (se 1 (by rfl) ⟨327795818, by rfl⟩ : syracuseStep 437061091 = 655591637) B655591637
theorem B1795639 : Blo 1594996 1795639 := bstep (se 1 (by rfl) ⟨1346729, by rfl⟩ : syracuseStep 1795639 = 2693459) B2693459
theorem B5383745 : Blo 1594996 5383745 := bstep (se 2 (by rfl) ⟨2018904, by rfl⟩ : syracuseStep 5383745 = 4037809) B4037809
theorem B10225217 : Blo 1594996 10225217 := bstep (se 2 (by rfl) ⟨3834456, by rfl⟩ : syracuseStep 10225217 = 7668913) B7668913
theorem B2393675 : Blo 1594996 2393675 := bstep (se 1 (by rfl) ⟨1795256, by rfl⟩ : syracuseStep 2393675 = 3590513) B3590513
theorem B2393687 : Blo 1594996 2393687 := bstep (se 1 (by rfl) ⟨1795265, by rfl⟩ : syracuseStep 2393687 = 3590531) B3590531
theorem B3589721 : Blo 1594996 3589721 := bstep (se 2 (by rfl) ⟨1346145, by rfl⟩ : syracuseStep 3589721 = 2692291) B2692291
theorem B6473305 : Blo 1594996 6473305 := bstep (se 2 (by rfl) ⟨2427489, by rfl⟩ : syracuseStep 6473305 = 4854979) B4854979
theorem B21841501 : Blo 1594996 21841501 := bstep (se 3 (by rfl) ⟨4095281, by rfl⟩ : syracuseStep 21841501 = 8190563) B8190563
theorem B11503255 : Blo 1594996 11503255 := bstep (se 1 (by rfl) ⟨8627441, by rfl⟩ : syracuseStep 11503255 = 17254883) B17254883
theorem B2393753 : Blo 1594996 2393753 := bstep (se 2 (by rfl) ⟨897657, by rfl⟩ : syracuseStep 2393753 = 1795315) B1795315
theorem B3589811 : Blo 1594996 3589811 := bstep (se 1 (by rfl) ⟨2692358, by rfl⟩ : syracuseStep 3589811 = 5384717) B5384717
theorem B3835571 : Blo 1594996 3835571 := bstep (se 1 (by rfl) ⟨2876678, by rfl⟩ : syracuseStep 3835571 = 5753357) B5753357
theorem B3589847 : Blo 1594996 3589847 := bstep (se 1 (by rfl) ⟨2692385, by rfl⟩ : syracuseStep 3589847 = 5384771) B5384771
theorem B1795819 : Blo 1594996 1795819 := bstep (se 1 (by rfl) ⟨1346864, by rfl⟩ : syracuseStep 1795819 = 2693729) B2693729
theorem B2393867 : Blo 1594996 2393867 := bstep (se 1 (by rfl) ⟨1795400, by rfl⟩ : syracuseStep 2393867 = 3590801) B3590801
theorem B2393879 : Blo 1594996 2393879 := bstep (se 1 (by rfl) ⟨1795409, by rfl⟩ : syracuseStep 2393879 = 3590819) B3590819
theorem B1820471 : Blo 1594996 1820471 := bstep (se 1 (by rfl) ⟨1365353, by rfl⟩ : syracuseStep 1820471 = 2730707) B2730707
theorem B4040513 : Blo 1594996 4040513 := bstep (se 2 (by rfl) ⟨1515192, by rfl⟩ : syracuseStep 4040513 = 3030385) B3030385
theorem B2393945 : Blo 1594996 2393945 := bstep (se 2 (by rfl) ⟨897729, by rfl⟩ : syracuseStep 2393945 = 1795459) B1795459
theorem B1795927 : Blo 1594996 1795927 := bstep (se 1 (by rfl) ⟨1346945, by rfl⟩ : syracuseStep 1795927 = 2693891) B2693891
theorem B3590027 : Blo 1594996 3590027 := bstep (se 1 (by rfl) ⟨2692520, by rfl⟩ : syracuseStep 3590027 = 5385041) B5385041
theorem B3590081 : Blo 1594996 3590081 := bstep (se 2 (by rfl) ⟨1346280, by rfl⟩ : syracuseStep 3590081 = 2692561) B2692561
theorem B2394059 : Blo 1594996 2394059 := bstep (se 1 (by rfl) ⟨1795544, by rfl⟩ : syracuseStep 2394059 = 3591089) B3591089
theorem B3409867 : Blo 1594996 3409867 := bstep (se 1 (by rfl) ⟨2557400, by rfl⟩ : syracuseStep 3409867 = 5114801) B5114801
theorem B2394071 : Blo 1594996 2394071 := bstep (se 1 (by rfl) ⟨1795553, by rfl⟩ : syracuseStep 2394071 = 3591107) B3591107
theorem B1796107 : Blo 1594996 1796107 := bstep (se 1 (by rfl) ⟨1347080, by rfl⟩ : syracuseStep 1796107 = 2694161) B2694161
theorem B3409943 : Blo 1594996 3409943 := bstep (se 1 (by rfl) ⟨2557457, by rfl⟩ : syracuseStep 3409943 = 5114915) B5114915
theorem B2394137 : Blo 1594996 2394137 := bstep (se 2 (by rfl) ⟨897801, by rfl⟩ : syracuseStep 2394137 = 1795603) B1795603
theorem B8079425 : Blo 1594996 8079425 := bstep (se 2 (by rfl) ⟨3029784, by rfl⟩ : syracuseStep 8079425 = 6059569) B6059569
theorem B5384285 : Blo 1594996 5384285 := bstep (se 3 (by rfl) ⟨1009553, by rfl⟩ : syracuseStep 5384285 = 2019107) B2019107
theorem B1796215 : Blo 1594996 1796215 := bstep (se 1 (by rfl) ⟨1347161, by rfl⟩ : syracuseStep 1796215 = 2694323) B2694323
theorem B2394251 : Blo 1594996 2394251 := bstep (se 1 (by rfl) ⟨1795688, by rfl⟩ : syracuseStep 2394251 = 3591377) B3591377
theorem B2394263 : Blo 1594996 2394263 := bstep (se 1 (by rfl) ⟨1795697, by rfl⟩ : syracuseStep 2394263 = 3591395) B3591395
theorem B3590297 : Blo 1594996 3590297 := bstep (se 2 (by rfl) ⟨1346361, by rfl⟩ : syracuseStep 3590297 = 2692723) B2692723
theorem B14551217 : Blo 1594996 14551217 := bstep (se 2 (by rfl) ⟨5456706, by rfl⟩ : syracuseStep 14551217 = 10913413) B10913413
theorem B6056153 : Blo 1594996 6056153 := bstep (se 2 (by rfl) ⟨2271057, by rfl⟩ : syracuseStep 6056153 = 4542115) B4542115
theorem B2394329 : Blo 1594996 2394329 := bstep (se 2 (by rfl) ⟨897873, by rfl⟩ : syracuseStep 2394329 = 1795747) B1795747
theorem B6908125 : Blo 1594996 6908125 := bstep (se 3 (by rfl) ⟨1295273, by rfl⟩ : syracuseStep 6908125 = 2590547) B2590547
theorem B3590387 : Blo 1594996 3590387 := bstep (se 1 (by rfl) ⟨2692790, by rfl⟩ : syracuseStep 3590387 = 5385581) B5385581
theorem B18188549 : Blo 1594996 18188549 := bstep (se 4 (by rfl) ⟨1705176, by rfl⟩ : syracuseStep 18188549 = 3410353) B3410353
theorem B7276817 : Blo 1594996 7276817 := bstep (se 2 (by rfl) ⟨2728806, by rfl⟩ : syracuseStep 7276817 = 5457613) B5457613
theorem B3590423 : Blo 1594996 3590423 := bstep (se 1 (by rfl) ⟨2692817, by rfl⟩ : syracuseStep 3590423 = 5385635) B5385635
theorem B1796395 : Blo 1594996 1796395 := bstep (se 1 (by rfl) ⟨1347296, by rfl⟩ : syracuseStep 1796395 = 2694593) B2694593
theorem B5908801 : Blo 1594996 5908801 := bstep (se 2 (by rfl) ⟨2215800, by rfl⟩ : syracuseStep 5908801 = 4431601) B4431601
theorem B2394443 : Blo 1594996 2394443 := bstep (se 1 (by rfl) ⟨1795832, by rfl⟩ : syracuseStep 2394443 = 3591665) B3591665
theorem B2394455 : Blo 1594996 2394455 := bstep (se 1 (by rfl) ⟨1795841, by rfl⟩ : syracuseStep 2394455 = 3591683) B3591683
theorem B4041049 : Blo 1594996 4041049 := bstep (se 2 (by rfl) ⟨1515393, by rfl⟩ : syracuseStep 4041049 = 3030787) B3030787
theorem B3688843 : Blo 1594996 3688843 := bstep (se 1 (by rfl) ⟨2766632, by rfl⟩ : syracuseStep 3688843 = 5533265) B5533265
theorem B1796503 : Blo 1594996 1796503 := bstep (se 1 (by rfl) ⟨1347377, by rfl⟩ : syracuseStep 1796503 = 2694755) B2694755
theorem B2394521 : Blo 1594996 2394521 := bstep (se 2 (by rfl) ⟨897945, by rfl⟩ : syracuseStep 2394521 = 1795891) B1795891
theorem B3590603 : Blo 1594996 3590603 := bstep (se 1 (by rfl) ⟨2692952, by rfl⟩ : syracuseStep 3590603 = 5385905) B5385905
theorem B3590657 : Blo 1594996 3590657 := bstep (se 2 (by rfl) ⟨1346496, by rfl⟩ : syracuseStep 3590657 = 2692993) B2692993
theorem B2394635 : Blo 1594996 2394635 := bstep (se 1 (by rfl) ⟨1795976, by rfl⟩ : syracuseStep 2394635 = 3591953) B3591953
theorem B6056471 : Blo 1594996 6056471 := bstep (se 1 (by rfl) ⟨4542353, by rfl⟩ : syracuseStep 6056471 = 9084707) B9084707
theorem B2394647 : Blo 1594996 2394647 := bstep (se 1 (by rfl) ⟨1795985, by rfl⟩ : syracuseStep 2394647 = 3591971) B3591971
theorem B3689011 : Blo 1594996 3689011 := bstep (se 1 (by rfl) ⟨2766758, by rfl⟩ : syracuseStep 3689011 = 5533517) B5533517
theorem B2394713 : Blo 1594996 2394713 := bstep (se 2 (by rfl) ⟨898017, by rfl⟩ : syracuseStep 2394713 = 1796035) B1796035
theorem B2271883 : Blo 1594996 2271883 := bstep (se 1 (by rfl) ⟨1703912, by rfl⟩ : syracuseStep 2271883 = 3407825) B3407825
theorem B17500823 : Blo 1594996 17500823 := bstep (se 1 (by rfl) ⟨13125617, by rfl⟩ : syracuseStep 17500823 = 26251235) B26251235
theorem B2394827 : Blo 1594996 2394827 := bstep (se 1 (by rfl) ⟨1796120, by rfl⟩ : syracuseStep 2394827 = 3592241) B3592241
theorem B2394839 : Blo 1594996 2394839 := bstep (se 1 (by rfl) ⟨1796129, by rfl⟩ : syracuseStep 2394839 = 3592259) B3592259
theorem B3590873 : Blo 1594996 3590873 := bstep (se 2 (by rfl) ⟨1346577, by rfl⟩ : syracuseStep 3590873 = 2693155) B2693155
theorem B2394905 : Blo 1594996 2394905 := bstep (se 2 (by rfl) ⟨898089, by rfl⟩ : syracuseStep 2394905 = 1796179) B1796179
theorem B3590963 : Blo 1594996 3590963 := bstep (se 1 (by rfl) ⟨2693222, by rfl⟩ : syracuseStep 3590963 = 5386445) B5386445
theorem B3590999 : Blo 1594996 3590999 := bstep (se 1 (by rfl) ⟨2693249, by rfl⟩ : syracuseStep 3590999 = 5386499) B5386499
theorem B9087875 : Blo 1594996 9087875 := bstep (se 1 (by rfl) ⟨6815906, by rfl⟩ : syracuseStep 9087875 = 13631813) B13631813
theorem B2395019 : Blo 1594996 2395019 := bstep (se 1 (by rfl) ⟨1796264, by rfl⟩ : syracuseStep 2395019 = 3592529) B3592529
theorem B2272151 : Blo 1594996 2272151 := bstep (se 1 (by rfl) ⟨1704113, by rfl⟩ : syracuseStep 2272151 = 3408227) B3408227
theorem B2395031 : Blo 1594996 2395031 := bstep (se 1 (by rfl) ⟨1796273, by rfl⟩ : syracuseStep 2395031 = 3592547) B3592547
theorem B2395097 : Blo 1594996 2395097 := bstep (se 2 (by rfl) ⟨898161, by rfl⟩ : syracuseStep 2395097 = 1796323) B1796323
theorem B3591179 : Blo 1594996 3591179 := bstep (se 1 (by rfl) ⟨2693384, by rfl⟩ : syracuseStep 3591179 = 5386769) B5386769
theorem B5991475 : Blo 1594996 5991475 := bstep (se 1 (by rfl) ⟨4493606, by rfl⟩ : syracuseStep 5991475 = 8987213) B8987213
theorem B3591233 : Blo 1594996 3591233 := bstep (se 2 (by rfl) ⟨1346712, by rfl⟩ : syracuseStep 3591233 = 2693425) B2693425
theorem B49114181 : Blo 1594996 49114181 := bstep (se 4 (by rfl) ⟨4604454, by rfl⟩ : syracuseStep 49114181 = 9208909) B9208909
theorem B2395211 : Blo 1594996 2395211 := bstep (se 1 (by rfl) ⟨1796408, by rfl⟩ : syracuseStep 2395211 = 3592817) B3592817
theorem B2395223 : Blo 1594996 2395223 := bstep (se 1 (by rfl) ⟨1796417, by rfl⟩ : syracuseStep 2395223 = 3592835) B3592835
theorem B2395289 : Blo 1594996 2395289 := bstep (se 2 (by rfl) ⟨898233, by rfl⟩ : syracuseStep 2395289 = 1796467) B1796467
theorem B6057139 : Blo 1594996 6057139 := bstep (se 1 (by rfl) ⟨4542854, by rfl⟩ : syracuseStep 6057139 = 9085709) B9085709
theorem B5385419 : Blo 1594996 5385419 := bstep (se 1 (by rfl) ⟨4039064, by rfl⟩ : syracuseStep 5385419 = 8078129) B8078129
theorem B2395403 : Blo 1594996 2395403 := bstep (se 1 (by rfl) ⟨1796552, by rfl⟩ : syracuseStep 2395403 = 3593105) B3593105
theorem B2395415 : Blo 1594996 2395415 := bstep (se 1 (by rfl) ⟨1796561, by rfl⟩ : syracuseStep 2395415 = 3593123) B3593123
theorem B3591449 : Blo 1594996 3591449 := bstep (se 2 (by rfl) ⟨1346793, by rfl⟩ : syracuseStep 3591449 = 2693587) B2693587
theorem B13634851 : Blo 1594996 13634851 := bstep (se 1 (by rfl) ⟨10226138, by rfl⟩ : syracuseStep 13634851 = 20452277) B20452277
theorem B2395481 : Blo 1594996 2395481 := bstep (se 2 (by rfl) ⟨898305, by rfl⟩ : syracuseStep 2395481 = 1796611) B1796611
theorem B3591539 : Blo 1594996 3591539 := bstep (se 1 (by rfl) ⟨2693654, by rfl⟩ : syracuseStep 3591539 = 5387309) B5387309
theorem B6819203 : Blo 1594996 6819203 := bstep (se 1 (by rfl) ⟨5114402, by rfl⟩ : syracuseStep 6819203 = 10228805) B10228805
theorem B3591575 : Blo 1594996 3591575 := bstep (se 1 (by rfl) ⟨2693681, by rfl⟩ : syracuseStep 3591575 = 5387363) B5387363
theorem B4042163 : Blo 1594996 4042163 := bstep (se 1 (by rfl) ⟨3031622, by rfl⟩ : syracuseStep 4042163 = 6063245) B6063245
theorem B5385689 : Blo 1594996 5385689 := bstep (se 2 (by rfl) ⟨2019633, by rfl⟩ : syracuseStep 5385689 = 4039267) B4039267
theorem B2018839 : Blo 1594996 2018839 := bstep (se 1 (by rfl) ⟨1514129, by rfl⟩ : syracuseStep 2018839 = 3028259) B3028259
theorem B11497025 : Blo 1594996 11497025 := bstep (se 2 (by rfl) ⟨4311384, by rfl⟩ : syracuseStep 11497025 = 8622769) B8622769
theorem B3591755 : Blo 1594996 3591755 := bstep (se 1 (by rfl) ⟨2693816, by rfl⟩ : syracuseStep 3591755 = 5387633) B5387633
theorem B3640907 : Blo 1594996 3640907 := bstep (se 1 (by rfl) ⟨2730680, by rfl⟩ : syracuseStep 3640907 = 5461361) B5461361
theorem B3591809 : Blo 1594996 3591809 := bstep (se 2 (by rfl) ⟨1346928, by rfl⟩ : syracuseStep 3591809 = 2693857) B2693857
theorem B4312727 : Blo 1594996 4312727 := bstep (se 1 (by rfl) ⟨3234545, by rfl⟩ : syracuseStep 4312727 = 6469091) B6469091
theorem B11505329 : Blo 1594996 11505329 := bstep (se 2 (by rfl) ⟨4314498, by rfl⟩ : syracuseStep 11505329 = 8628997) B8628997
theorem B6819545 : Blo 1594996 6819545 := bstep (se 2 (by rfl) ⟨2557329, by rfl⟩ : syracuseStep 6819545 = 5114659) B5114659
theorem B3592025 : Blo 1594996 3592025 := bstep (se 2 (by rfl) ⟨1347009, by rfl⟩ : syracuseStep 3592025 = 2694019) B2694019
theorem B2273113 : Blo 1594996 2273113 := bstep (se 2 (by rfl) ⟨852417, by rfl⟩ : syracuseStep 2273113 = 1704835) B1704835
theorem B6467501 : Blo 1594996 6467501 := bstep (se 3 (by rfl) ⟨1212656, by rfl⟩ : syracuseStep 6467501 = 2425313) B2425313
theorem B3592115 : Blo 1594996 3592115 := bstep (se 1 (by rfl) ⟨2694086, by rfl⟩ : syracuseStep 3592115 = 5388173) B5388173
theorem B3592151 : Blo 1594996 3592151 := bstep (se 1 (by rfl) ⟨2694113, by rfl⟩ : syracuseStep 3592151 = 5388227) B5388227
theorem B8081369 : Blo 1594996 8081369 := bstep (se 2 (by rfl) ⟨3030513, by rfl⟩ : syracuseStep 8081369 = 6061027) B6061027
theorem B18173969 : Blo 1594996 18173969 := bstep (se 2 (by rfl) ⟨6815238, by rfl⟩ : syracuseStep 18173969 = 13630477) B13630477
theorem B17264657 : Blo 1594996 17264657 := bstep (se 2 (by rfl) ⟨6474246, by rfl⟩ : syracuseStep 17264657 = 12948493) B12948493
theorem B19402787 : Blo 1594996 19402787 := bstep (se 1 (by rfl) ⟨14552090, by rfl⟩ : syracuseStep 19402787 = 29104181) B29104181
theorem B3592331 : Blo 1594996 3592331 := bstep (se 1 (by rfl) ⟨2694248, by rfl⟩ : syracuseStep 3592331 = 5388497) B5388497
theorem B5386391 : Blo 1594996 5386391 := bstep (se 1 (by rfl) ⟨4039793, by rfl⟩ : syracuseStep 5386391 = 8079587) B8079587
theorem B3281075 : Blo 1594996 3281075 := bstep (se 1 (by rfl) ⟨2460806, by rfl⟩ : syracuseStep 3281075 = 4921613) B4921613
theorem B3592385 : Blo 1594996 3592385 := bstep (se 2 (by rfl) ⟨1347144, by rfl⟩ : syracuseStep 3592385 = 2694289) B2694289
theorem B69005681 : Blo 1594996 69005681 := bstep (se 2 (by rfl) ⟨25877130, by rfl⟩ : syracuseStep 69005681 = 51754261) B51754261
theorem B6058385 : Blo 1594996 6058385 := bstep (se 2 (by rfl) ⟨2271894, by rfl⟩ : syracuseStep 6058385 = 4543789) B4543789
theorem B3592601 : Blo 1594996 3592601 := bstep (se 2 (by rfl) ⟨1347225, by rfl⟩ : syracuseStep 3592601 = 2694451) B2694451
theorem B3592691 : Blo 1594996 3592691 := bstep (se 1 (by rfl) ⟨2694518, by rfl⟩ : syracuseStep 3592691 = 5389037) B5389037
theorem B3592727 : Blo 1594996 3592727 := bstep (se 1 (by rfl) ⟨2694545, by rfl⟩ : syracuseStep 3592727 = 5389091) B5389091
theorem B16372259 : Blo 1594996 16372259 := bstep (se 1 (by rfl) ⟨12279194, by rfl⟩ : syracuseStep 16372259 = 24558389) B24558389
theorem B5386931 : Blo 1594996 5386931 := bstep (se 1 (by rfl) ⟨4040198, by rfl⟩ : syracuseStep 5386931 = 8080397) B8080397
theorem B3592907 : Blo 1594996 3592907 := bstep (se 1 (by rfl) ⟨2694680, by rfl⟩ : syracuseStep 3592907 = 5389361) B5389361
theorem B12284621 : Blo 1594996 12284621 := bstep (se 3 (by rfl) ⟨2303366, by rfl⟩ : syracuseStep 12284621 = 4606733) B4606733
theorem B3592961 : Blo 1594996 3592961 := bstep (se 2 (by rfl) ⟨1347360, by rfl⟩ : syracuseStep 3592961 = 2694721) B2694721
theorem B3453835 : Blo 1594996 3453835 := bstep (se 1 (by rfl) ⟨2590376, by rfl⟩ : syracuseStep 3453835 = 5180753) B5180753
theorem B5387201 : Blo 1594996 5387201 := bstep (se 2 (by rfl) ⟨2020200, by rfl⟩ : syracuseStep 5387201 = 4040401) B4040401
theorem B2692055 : Blo 1594996 2692055 := bstep (se 1 (by rfl) ⟨2019041, by rfl⟩ : syracuseStep 2692055 = 4038083) B4038083
theorem B3593177 : Blo 1594996 3593177 := bstep (se 2 (by rfl) ⟨1347441, by rfl⟩ : syracuseStep 3593177 = 2694883) B2694883
theorem B10228781 : Blo 1594996 10228781 := bstep (se 3 (by rfl) ⟨1917896, by rfl⟩ : syracuseStep 10228781 = 3835793) B3835793
theorem B6059083 : Blo 1594996 6059083 := bstep (se 1 (by rfl) ⟨4544312, by rfl⟩ : syracuseStep 6059083 = 9088625) B9088625
theorem B2692183 : Blo 1594996 2692183 := bstep (se 1 (by rfl) ⟨2019137, by rfl⟩ : syracuseStep 2692183 = 4038275) B4038275
theorem B8623205 : Blo 1594996 8623205 := bstep (se 4 (by rfl) ⟨808425, by rfl⟩ : syracuseStep 8623205 = 1616851) B1616851
theorem B2020555 : Blo 1594996 2020555 := bstep (se 1 (by rfl) ⟨1515416, by rfl⟩ : syracuseStep 2020555 = 3030833) B3030833
theorem B9090265 : Blo 1594996 9090265 := bstep (se 2 (by rfl) ⟨3408849, by rfl⟩ : syracuseStep 9090265 = 6817699) B6817699
theorem B14554403 : Blo 1594996 14554403 := bstep (se 1 (by rfl) ⟨10915802, by rfl⟩ : syracuseStep 14554403 = 21831605) B21831605
theorem B6821185 : Blo 1594996 6821185 := bstep (se 2 (by rfl) ⟨2557944, by rfl⟩ : syracuseStep 6821185 = 5115889) B5115889
theorem B6059357 : Blo 1594996 6059357 := bstep (se 3 (by rfl) ⟨1136129, by rfl⟩ : syracuseStep 6059357 = 2272259) B2272259
theorem B3028403 : Blo 1594996 3028403 := bstep (se 1 (by rfl) ⟨2271302, by rfl⟩ : syracuseStep 3028403 = 4542605) B4542605
theorem B3028441 : Blo 1594996 3028441 := bstep (se 2 (by rfl) ⟨1135665, by rfl⟩ : syracuseStep 3028441 = 2271331) B2271331
theorem B5387741 : Blo 1594996 5387741 := bstep (se 3 (by rfl) ⟨1010201, by rfl⟩ : syracuseStep 5387741 = 2020403) B2020403
theorem B8082989 : Blo 1594996 8082989 := bstep (se 3 (by rfl) ⟨1515560, by rfl⟩ : syracuseStep 8082989 = 3031121) B3031121
theorem B25876037 : Blo 1594996 25876037 := bstep (se 4 (by rfl) ⟨2425878, by rfl⟩ : syracuseStep 25876037 = 4851757) B4851757
theorem B12940901 : Blo 1594996 12940901 := bstep (se 4 (by rfl) ⟨1213209, by rfl⟩ : syracuseStep 12940901 = 2426419) B2426419
theorem B1594999 : Blo 1594996 1594999 := bstep (se 1 (by rfl) ⟨1196249, by rfl⟩ : syracuseStep 1594999 = 2392499) B2392499
theorem B13825667 : Blo 1594996 13825667 := bstep (se 1 (by rfl) ⟨10369250, by rfl⟩ : syracuseStep 13825667 = 20738501) B20738501
theorem B1595019 : Blo 1594996 1595019 := bstep (se 1 (by rfl) ⟨1196264, by rfl⟩ : syracuseStep 1595019 = 2392529) B2392529
theorem B1595031 : Blo 1594996 1595031 := bstep (se 1 (by rfl) ⟨1196273, by rfl⟩ : syracuseStep 1595031 = 2392547) B2392547
theorem B1595051 : Blo 1594996 1595051 := bstep (se 1 (by rfl) ⟨1196288, by rfl⟩ : syracuseStep 1595051 = 2392577) B2392577
theorem B1595063 : Blo 1594996 1595063 := bstep (se 1 (by rfl) ⟨1196297, by rfl⟩ : syracuseStep 1595063 = 2392595) B2392595
theorem B1595083 : Blo 1594996 1595083 := bstep (se 1 (by rfl) ⟨1196312, by rfl⟩ : syracuseStep 1595083 = 2392625) B2392625
theorem B2692811 : Blo 1594996 2692811 := bstep (se 1 (by rfl) ⟨2019608, by rfl⟩ : syracuseStep 2692811 = 4039217) B4039217
theorem B1595095 : Blo 1594996 1595095 := bstep (se 1 (by rfl) ⟨1196321, by rfl⟩ : syracuseStep 1595095 = 2392643) B2392643
theorem B4314845 : Blo 1594996 4314845 := bstep (se 3 (by rfl) ⟨809033, by rfl⟩ : syracuseStep 4314845 = 1618067) B1618067
theorem B4855517 : Blo 1594996 4855517 := bstep (se 3 (by rfl) ⟨910409, by rfl⟩ : syracuseStep 4855517 = 1820819) B1820819
theorem B1595115 : Blo 1594996 1595115 := bstep (se 1 (by rfl) ⟨1196336, by rfl⟩ : syracuseStep 1595115 = 2392673) B2392673
theorem B1595127 : Blo 1594996 1595127 := bstep (se 1 (by rfl) ⟨1196345, by rfl⟩ : syracuseStep 1595127 = 2392691) B2392691
theorem B1595147 : Blo 1594996 1595147 := bstep (se 1 (by rfl) ⟨1196360, by rfl⟩ : syracuseStep 1595147 = 2392721) B2392721
theorem B1595159 : Blo 1594996 1595159 := bstep (se 1 (by rfl) ⟨1196369, by rfl⟩ : syracuseStep 1595159 = 2392739) B2392739
theorem B1595179 : Blo 1594996 1595179 := bstep (se 1 (by rfl) ⟨1196384, by rfl⟩ : syracuseStep 1595179 = 2392769) B2392769
theorem B1595191 : Blo 1594996 1595191 := bstep (se 1 (by rfl) ⟨1196393, by rfl⟩ : syracuseStep 1595191 = 2392787) B2392787
theorem B1595211 : Blo 1594996 1595211 := bstep (se 1 (by rfl) ⟨1196408, by rfl⟩ : syracuseStep 1595211 = 2392817) B2392817
theorem B2692939 : Blo 1594996 2692939 := bstep (se 1 (by rfl) ⟨2019704, by rfl⟩ : syracuseStep 2692939 = 4039409) B4039409
theorem B1595223 : Blo 1594996 1595223 := bstep (se 1 (by rfl) ⟨1196417, by rfl⟩ : syracuseStep 1595223 = 2392835) B2392835
theorem B1595243 : Blo 1594996 1595243 := bstep (se 1 (by rfl) ⟨1196432, by rfl⟩ : syracuseStep 1595243 = 2392865) B2392865
theorem B1595255 : Blo 1594996 1595255 := bstep (se 1 (by rfl) ⟨1196441, by rfl⟩ : syracuseStep 1595255 = 2392883) B2392883
theorem B1595275 : Blo 1594996 1595275 := bstep (se 1 (by rfl) ⟨1196456, by rfl⟩ : syracuseStep 1595275 = 2392913) B2392913
theorem B1595287 : Blo 1594996 1595287 := bstep (se 1 (by rfl) ⟨1196465, by rfl⟩ : syracuseStep 1595287 = 2392931) B2392931
theorem B3028889 : Blo 1594996 3028889 := bstep (se 2 (by rfl) ⟨1135833, by rfl⟩ : syracuseStep 3028889 = 2271667) B2271667
theorem B1595307 : Blo 1594996 1595307 := bstep (se 1 (by rfl) ⟨1196480, by rfl⟩ : syracuseStep 1595307 = 2392961) B2392961
theorem B7378867 : Blo 1594996 7378867 := bstep (se 1 (by rfl) ⟨5534150, by rfl⟩ : syracuseStep 7378867 = 11068301) B11068301
theorem B1595319 : Blo 1594996 1595319 := bstep (se 1 (by rfl) ⟨1196489, by rfl⟩ : syracuseStep 1595319 = 2392979) B2392979
theorem B1595339 : Blo 1594996 1595339 := bstep (se 1 (by rfl) ⟨1196504, by rfl⟩ : syracuseStep 1595339 = 2393009) B2393009
theorem B1595351 : Blo 1594996 1595351 := bstep (se 1 (by rfl) ⟨1196513, by rfl⟩ : syracuseStep 1595351 = 2393027) B2393027
theorem B2693081 : Blo 1594996 2693081 := bstep (se 2 (by rfl) ⟨1009905, by rfl⟩ : syracuseStep 2693081 = 2019811) B2019811
theorem B1595371 : Blo 1594996 1595371 := bstep (se 1 (by rfl) ⟨1196528, by rfl⟩ : syracuseStep 1595371 = 2393057) B2393057
theorem B1595383 : Blo 1594996 1595383 := bstep (se 1 (by rfl) ⟨1196537, by rfl⟩ : syracuseStep 1595383 = 2393075) B2393075
theorem B1595403 : Blo 1594996 1595403 := bstep (se 1 (by rfl) ⟨1196552, by rfl⟩ : syracuseStep 1595403 = 2393105) B2393105
theorem B1595415 : Blo 1594996 1595415 := bstep (se 1 (by rfl) ⟨1196561, by rfl⟩ : syracuseStep 1595415 = 2393123) B2393123
theorem B6060055 : Blo 1594996 6060055 := bstep (se 1 (by rfl) ⟨4545041, by rfl⟩ : syracuseStep 6060055 = 9090083) B9090083
theorem B1595435 : Blo 1594996 1595435 := bstep (se 1 (by rfl) ⟨1196576, by rfl⟩ : syracuseStep 1595435 = 2393153) B2393153
theorem B1595447 : Blo 1594996 1595447 := bstep (se 1 (by rfl) ⟨1196585, by rfl⟩ : syracuseStep 1595447 = 2393171) B2393171
theorem B7280705 : Blo 1594996 7280705 := bstep (se 2 (by rfl) ⟨2730264, by rfl⟩ : syracuseStep 7280705 = 5460529) B5460529
theorem B1595467 : Blo 1594996 1595467 := bstep (se 1 (by rfl) ⟨1196600, by rfl⟩ : syracuseStep 1595467 = 2393201) B2393201
theorem B1595479 : Blo 1594996 1595479 := bstep (se 1 (by rfl) ⟨1196609, by rfl⟩ : syracuseStep 1595479 = 2393219) B2393219
theorem B2693209 : Blo 1594996 2693209 := bstep (se 2 (by rfl) ⟨1009953, by rfl⟩ : syracuseStep 2693209 = 2019907) B2019907
theorem B1595499 : Blo 1594996 1595499 := bstep (se 1 (by rfl) ⟨1196624, by rfl⟩ : syracuseStep 1595499 = 2393249) B2393249
theorem B1595511 : Blo 1594996 1595511 := bstep (se 1 (by rfl) ⟨1196633, by rfl⟩ : syracuseStep 1595511 = 2393267) B2393267
theorem B1595531 : Blo 1594996 1595531 := bstep (se 1 (by rfl) ⟨1196648, by rfl⟩ : syracuseStep 1595531 = 2393297) B2393297
theorem B1595543 : Blo 1594996 1595543 := bstep (se 1 (by rfl) ⟨1196657, by rfl⟩ : syracuseStep 1595543 = 2393315) B2393315
theorem B9091223 : Blo 1594996 9091223 := bstep (se 1 (by rfl) ⟨6818417, by rfl⟩ : syracuseStep 9091223 = 13636835) B13636835
theorem B1595563 : Blo 1594996 1595563 := bstep (se 1 (by rfl) ⟨1196672, by rfl⟩ : syracuseStep 1595563 = 2393345) B2393345
theorem B1595575 : Blo 1594996 1595575 := bstep (se 1 (by rfl) ⟨1196681, by rfl⟩ : syracuseStep 1595575 = 2393363) B2393363
theorem B1595595 : Blo 1594996 1595595 := bstep (se 1 (by rfl) ⟨1196696, by rfl⟩ : syracuseStep 1595595 = 2393393) B2393393
theorem B1595607 : Blo 1594996 1595607 := bstep (se 1 (by rfl) ⟨1196705, by rfl⟩ : syracuseStep 1595607 = 2393411) B2393411
theorem B1595627 : Blo 1594996 1595627 := bstep (se 1 (by rfl) ⟨1196720, by rfl⟩ : syracuseStep 1595627 = 2393441) B2393441
theorem B1595639 : Blo 1594996 1595639 := bstep (se 1 (by rfl) ⟨1196729, by rfl⟩ : syracuseStep 1595639 = 2393459) B2393459
theorem B1595659 : Blo 1594996 1595659 := bstep (se 1 (by rfl) ⟨1196744, by rfl⟩ : syracuseStep 1595659 = 2393489) B2393489
theorem B8075537 : Blo 1594996 8075537 := bstep (se 2 (by rfl) ⟨3028326, by rfl⟩ : syracuseStep 8075537 = 6056653) B6056653
theorem B1595671 : Blo 1594996 1595671 := bstep (se 1 (by rfl) ⟨1196753, by rfl⟩ : syracuseStep 1595671 = 2393507) B2393507
theorem B1595691 : Blo 1594996 1595691 := bstep (se 1 (by rfl) ⟨1196768, by rfl⟩ : syracuseStep 1595691 = 2393537) B2393537
theorem B1595703 : Blo 1594996 1595703 := bstep (se 1 (by rfl) ⟨1196777, by rfl⟩ : syracuseStep 1595703 = 2393555) B2393555
theorem B1595723 : Blo 1594996 1595723 := bstep (se 1 (by rfl) ⟨1196792, by rfl⟩ : syracuseStep 1595723 = 2393585) B2393585
theorem B1595735 : Blo 1594996 1595735 := bstep (se 1 (by rfl) ⟨1196801, by rfl⟩ : syracuseStep 1595735 = 2393603) B2393603
theorem B1595755 : Blo 1594996 1595755 := bstep (se 1 (by rfl) ⟨1196816, by rfl⟩ : syracuseStep 1595755 = 2393633) B2393633
theorem B1595767 : Blo 1594996 1595767 := bstep (se 1 (by rfl) ⟨1196825, by rfl⟩ : syracuseStep 1595767 = 2393651) B2393651
theorem B1595787 : Blo 1594996 1595787 := bstep (se 1 (by rfl) ⟨1196840, by rfl⟩ : syracuseStep 1595787 = 2393681) B2393681
theorem B1595799 : Blo 1594996 1595799 := bstep (se 1 (by rfl) ⟨1196849, by rfl⟩ : syracuseStep 1595799 = 2393699) B2393699
theorem B8190359 : Blo 1594996 8190359 := bstep (se 1 (by rfl) ⟨6142769, by rfl⟩ : syracuseStep 8190359 = 12285539) B12285539
theorem B1595819 : Blo 1594996 1595819 := bstep (se 1 (by rfl) ⟨1196864, by rfl⟩ : syracuseStep 1595819 = 2393729) B2393729
theorem B8075699 : Blo 1594996 8075699 := bstep (se 1 (by rfl) ⟨6056774, by rfl⟩ : syracuseStep 8075699 = 12113549) B12113549
theorem B1595831 : Blo 1594996 1595831 := bstep (se 1 (by rfl) ⟨1196873, by rfl⟩ : syracuseStep 1595831 = 2393747) B2393747
theorem B6814145 : Blo 1594996 6814145 := bstep (se 2 (by rfl) ⟨2555304, by rfl⟩ : syracuseStep 6814145 = 5110609) B5110609
theorem B1595851 : Blo 1594996 1595851 := bstep (se 1 (by rfl) ⟨1196888, by rfl⟩ : syracuseStep 1595851 = 2393777) B2393777
theorem B1595863 : Blo 1594996 1595863 := bstep (se 1 (by rfl) ⟨1196897, by rfl⟩ : syracuseStep 1595863 = 2393795) B2393795
theorem B1595883 : Blo 1594996 1595883 := bstep (se 1 (by rfl) ⟨1196912, by rfl⟩ : syracuseStep 1595883 = 2393825) B2393825
theorem B1595895 : Blo 1594996 1595895 := bstep (se 1 (by rfl) ⟨1196921, by rfl⟩ : syracuseStep 1595895 = 2393843) B2393843
theorem B1595915 : Blo 1594996 1595915 := bstep (se 1 (by rfl) ⟨1196936, by rfl⟩ : syracuseStep 1595915 = 2393873) B2393873
theorem B1595927 : Blo 1594996 1595927 := bstep (se 1 (by rfl) ⟨1196945, by rfl⟩ : syracuseStep 1595927 = 2393891) B2393891
theorem B1595947 : Blo 1594996 1595947 := bstep (se 1 (by rfl) ⟨1196960, by rfl⟩ : syracuseStep 1595947 = 2393921) B2393921
theorem B1595959 : Blo 1594996 1595959 := bstep (se 1 (by rfl) ⟨1196969, by rfl⟩ : syracuseStep 1595959 = 2393939) B2393939
theorem B1595979 : Blo 1594996 1595979 := bstep (se 1 (by rfl) ⟨1196984, by rfl⟩ : syracuseStep 1595979 = 2393969) B2393969
theorem B5388875 : Blo 1594996 5388875 := bstep (se 1 (by rfl) ⟨4041656, by rfl⟩ : syracuseStep 5388875 = 8083313) B8083313
theorem B1595991 : Blo 1594996 1595991 := bstep (se 1 (by rfl) ⟨1196993, by rfl⟩ : syracuseStep 1595991 = 2393987) B2393987
theorem B12950117 : Blo 1594996 12950117 := bstep (se 4 (by rfl) ⟨1214073, by rfl⟩ : syracuseStep 12950117 = 2428147) B2428147
theorem B1596011 : Blo 1594996 1596011 := bstep (se 1 (by rfl) ⟨1197008, by rfl⟩ : syracuseStep 1596011 = 2394017) B2394017
theorem B1596023 : Blo 1594996 1596023 := bstep (se 1 (by rfl) ⟨1197017, by rfl⟩ : syracuseStep 1596023 = 2394035) B2394035
theorem B3029633 : Blo 1594996 3029633 := bstep (se 2 (by rfl) ⟨1136112, by rfl⟩ : syracuseStep 3029633 = 2272225) B2272225
theorem B1596043 : Blo 1594996 1596043 := bstep (se 1 (by rfl) ⟨1197032, by rfl⟩ : syracuseStep 1596043 = 2394065) B2394065
theorem B1596055 : Blo 1594996 1596055 := bstep (se 1 (by rfl) ⟨1197041, by rfl⟩ : syracuseStep 1596055 = 2394083) B2394083
theorem B2693783 : Blo 1594996 2693783 := bstep (se 1 (by rfl) ⟨2020337, by rfl⟩ : syracuseStep 2693783 = 4040675) B4040675
theorem B1596075 : Blo 1594996 1596075 := bstep (se 1 (by rfl) ⟨1197056, by rfl⟩ : syracuseStep 1596075 = 2394113) B2394113
theorem B1596087 : Blo 1594996 1596087 := bstep (se 1 (by rfl) ⟨1197065, by rfl⟩ : syracuseStep 1596087 = 2394131) B2394131
theorem B1596107 : Blo 1594996 1596107 := bstep (se 1 (by rfl) ⟨1197080, by rfl⟩ : syracuseStep 1596107 = 2394161) B2394161
theorem B1596119 : Blo 1594996 1596119 := bstep (se 1 (by rfl) ⟨1197089, by rfl⟩ : syracuseStep 1596119 = 2394179) B2394179
theorem B1596139 : Blo 1594996 1596139 := bstep (se 1 (by rfl) ⟨1197104, by rfl⟩ : syracuseStep 1596139 = 2394209) B2394209
theorem B1596151 : Blo 1594996 1596151 := bstep (se 1 (by rfl) ⟨1197113, by rfl⟩ : syracuseStep 1596151 = 2394227) B2394227
theorem B1596171 : Blo 1594996 1596171 := bstep (se 1 (by rfl) ⟨1197128, by rfl⟩ : syracuseStep 1596171 = 2394257) B2394257
theorem B1596183 : Blo 1594996 1596183 := bstep (se 1 (by rfl) ⟨1197137, by rfl⟩ : syracuseStep 1596183 = 2394275) B2394275
theorem B2693911 : Blo 1594996 2693911 := bstep (se 1 (by rfl) ⟨2020433, by rfl⟩ : syracuseStep 2693911 = 4040867) B4040867
theorem B1596203 : Blo 1594996 1596203 := bstep (se 1 (by rfl) ⟨1197152, by rfl⟩ : syracuseStep 1596203 = 2394305) B2394305
theorem B6060845 : Blo 1594996 6060845 := bstep (se 3 (by rfl) ⟨1136408, by rfl⟩ : syracuseStep 6060845 = 2272817) B2272817
theorem B1596215 : Blo 1594996 1596215 := bstep (se 1 (by rfl) ⟨1197161, by rfl⟩ : syracuseStep 1596215 = 2394323) B2394323
theorem B1596235 : Blo 1594996 1596235 := bstep (se 1 (by rfl) ⟨1197176, by rfl⟩ : syracuseStep 1596235 = 2394353) B2394353
theorem B1596247 : Blo 1594996 1596247 := bstep (se 1 (by rfl) ⟨1197185, by rfl⟩ : syracuseStep 1596247 = 2394371) B2394371
theorem B4037465 : Blo 1594996 4037465 := bstep (se 2 (by rfl) ⟨1514049, by rfl⟩ : syracuseStep 4037465 = 3028099) B3028099
theorem B5389145 : Blo 1594996 5389145 := bstep (se 2 (by rfl) ⟨2020929, by rfl⟩ : syracuseStep 5389145 = 4041859) B4041859
theorem B1596267 : Blo 1594996 1596267 := bstep (se 1 (by rfl) ⟨1197200, by rfl⟩ : syracuseStep 1596267 = 2394401) B2394401
theorem B18176885 : Blo 1594996 18176885 := bstep (se 5 (by rfl) ⟨852041, by rfl⟩ : syracuseStep 18176885 = 1704083) B1704083
theorem B1596279 : Blo 1594996 1596279 := bstep (se 1 (by rfl) ⟨1197209, by rfl⟩ : syracuseStep 1596279 = 2394419) B2394419
theorem B3029899 : Blo 1594996 3029899 := bstep (se 1 (by rfl) ⟨2272424, by rfl⟩ : syracuseStep 3029899 = 4544849) B4544849
theorem B1596299 : Blo 1594996 1596299 := bstep (se 1 (by rfl) ⟨1197224, by rfl⟩ : syracuseStep 1596299 = 2394449) B2394449
theorem B1596311 : Blo 1594996 1596311 := bstep (se 1 (by rfl) ⟨1197233, by rfl⟩ : syracuseStep 1596311 = 2394467) B2394467
theorem B1596331 : Blo 1594996 1596331 := bstep (se 1 (by rfl) ⟨1197248, by rfl⟩ : syracuseStep 1596331 = 2394497) B2394497
theorem B1596343 : Blo 1594996 1596343 := bstep (se 1 (by rfl) ⟨1197257, by rfl⟩ : syracuseStep 1596343 = 2394515) B2394515
theorem B4373441 : Blo 1594996 4373441 := bstep (se 2 (by rfl) ⟨1640040, by rfl⟩ : syracuseStep 4373441 = 3280081) B3280081
theorem B1596363 : Blo 1594996 1596363 := bstep (se 1 (by rfl) ⟨1197272, by rfl⟩ : syracuseStep 1596363 = 2394545) B2394545
theorem B1596375 : Blo 1594996 1596375 := bstep (se 1 (by rfl) ⟨1197281, by rfl⟩ : syracuseStep 1596375 = 2394563) B2394563
theorem B4545497 : Blo 1594996 4545497 := bstep (se 2 (by rfl) ⟨1704561, by rfl⟩ : syracuseStep 4545497 = 3409123) B3409123
theorem B1596395 : Blo 1594996 1596395 := bstep (se 1 (by rfl) ⟨1197296, by rfl⟩ : syracuseStep 1596395 = 2394593) B2394593
theorem B1596407 : Blo 1594996 1596407 := bstep (se 1 (by rfl) ⟨1197305, by rfl⟩ : syracuseStep 1596407 = 2394611) B2394611
theorem B1596427 : Blo 1594996 1596427 := bstep (se 1 (by rfl) ⟨1197320, by rfl⟩ : syracuseStep 1596427 = 2394641) B2394641
theorem B23010317 : Blo 1594996 23010317 := bstep (se 3 (by rfl) ⟨4314434, by rfl⟩ : syracuseStep 23010317 = 8628869) B8628869
theorem B1596439 : Blo 1594996 1596439 := bstep (se 1 (by rfl) ⟨1197329, by rfl⟩ : syracuseStep 1596439 = 2394659) B2394659
theorem B1596459 : Blo 1594996 1596459 := bstep (se 1 (by rfl) ⟨1197344, by rfl⟩ : syracuseStep 1596459 = 2394689) B2394689
theorem B1596471 : Blo 1594996 1596471 := bstep (se 1 (by rfl) ⟨1197353, by rfl⟩ : syracuseStep 1596471 = 2394707) B2394707
theorem B1596491 : Blo 1594996 1596491 := bstep (se 1 (by rfl) ⟨1197368, by rfl⟩ : syracuseStep 1596491 = 2394737) B2394737
theorem B1596503 : Blo 1594996 1596503 := bstep (se 1 (by rfl) ⟨1197377, by rfl⟩ : syracuseStep 1596503 = 2394755) B2394755
theorem B6814813 : Blo 1594996 6814813 := bstep (se 3 (by rfl) ⟨1277777, by rfl⟩ : syracuseStep 6814813 = 2555555) B2555555
theorem B1596523 : Blo 1594996 1596523 := bstep (se 1 (by rfl) ⟨1197392, by rfl⟩ : syracuseStep 1596523 = 2394785) B2394785
theorem B1596535 : Blo 1594996 1596535 := bstep (se 1 (by rfl) ⟨1197401, by rfl⟩ : syracuseStep 1596535 = 2394803) B2394803
theorem B1596555 : Blo 1594996 1596555 := bstep (se 1 (by rfl) ⟨1197416, by rfl⟩ : syracuseStep 1596555 = 2394833) B2394833
theorem B1596567 : Blo 1594996 1596567 := bstep (se 1 (by rfl) ⟨1197425, by rfl⟩ : syracuseStep 1596567 = 2394851) B2394851
theorem B1596587 : Blo 1594996 1596587 := bstep (se 1 (by rfl) ⟨1197440, by rfl⟩ : syracuseStep 1596587 = 2394881) B2394881
theorem B1596599 : Blo 1594996 1596599 := bstep (se 1 (by rfl) ⟨1197449, by rfl⟩ : syracuseStep 1596599 = 2394899) B2394899
theorem B1596619 : Blo 1594996 1596619 := bstep (se 1 (by rfl) ⟨1197464, by rfl⟩ : syracuseStep 1596619 = 2394929) B2394929
theorem B1596631 : Blo 1594996 1596631 := bstep (se 1 (by rfl) ⟨1197473, by rfl⟩ : syracuseStep 1596631 = 2394947) B2394947
theorem B1596651 : Blo 1594996 1596651 := bstep (se 1 (by rfl) ⟨1197488, by rfl⟩ : syracuseStep 1596651 = 2394977) B2394977
theorem B1596663 : Blo 1594996 1596663 := bstep (se 1 (by rfl) ⟨1197497, by rfl⟩ : syracuseStep 1596663 = 2394995) B2394995
theorem B1596683 : Blo 1594996 1596683 := bstep (se 1 (by rfl) ⟨1197512, by rfl⟩ : syracuseStep 1596683 = 2395025) B2395025
theorem B3833111 : Blo 1594996 3833111 := bstep (se 1 (by rfl) ⟨2874833, by rfl⟩ : syracuseStep 3833111 = 5749667) B5749667
theorem B1596695 : Blo 1594996 1596695 := bstep (se 1 (by rfl) ⟨1197521, by rfl⟩ : syracuseStep 1596695 = 2395043) B2395043
theorem B1596715 : Blo 1594996 1596715 := bstep (se 1 (by rfl) ⟨1197536, by rfl⟩ : syracuseStep 1596715 = 2395073) B2395073
theorem B1596727 : Blo 1594996 1596727 := bstep (se 1 (by rfl) ⟨1197545, by rfl⟩ : syracuseStep 1596727 = 2395091) B2395091
theorem B3030347 : Blo 1594996 3030347 := bstep (se 1 (by rfl) ⟨2272760, by rfl⟩ : syracuseStep 3030347 = 4545521) B4545521
theorem B1596747 : Blo 1594996 1596747 := bstep (se 1 (by rfl) ⟨1197560, by rfl⟩ : syracuseStep 1596747 = 2395121) B2395121
theorem B1596759 : Blo 1594996 1596759 := bstep (se 1 (by rfl) ⟨1197569, by rfl⟩ : syracuseStep 1596759 = 2395139) B2395139
theorem B1596779 : Blo 1594996 1596779 := bstep (se 1 (by rfl) ⟨1197584, by rfl⟩ : syracuseStep 1596779 = 2395169) B2395169
theorem B1596791 : Blo 1594996 1596791 := bstep (se 1 (by rfl) ⟨1197593, by rfl⟩ : syracuseStep 1596791 = 2395187) B2395187
theorem B2694539 : Blo 1594996 2694539 := bstep (se 1 (by rfl) ⟨2020904, by rfl⟩ : syracuseStep 2694539 = 4041809) B4041809
theorem B1596811 : Blo 1594996 1596811 := bstep (se 1 (by rfl) ⟨1197608, by rfl⟩ : syracuseStep 1596811 = 2395217) B2395217
theorem B1596823 : Blo 1594996 1596823 := bstep (se 1 (by rfl) ⟨1197617, by rfl⟩ : syracuseStep 1596823 = 2395235) B2395235
theorem B1596843 : Blo 1594996 1596843 := bstep (se 1 (by rfl) ⟨1197632, by rfl⟩ : syracuseStep 1596843 = 2395265) B2395265
theorem B1596855 : Blo 1594996 1596855 := bstep (se 1 (by rfl) ⟨1197641, by rfl⟩ : syracuseStep 1596855 = 2395283) B2395283
theorem B1596875 : Blo 1594996 1596875 := bstep (se 1 (by rfl) ⟨1197656, by rfl⟩ : syracuseStep 1596875 = 2395313) B2395313
theorem B1596887 : Blo 1594996 1596887 := bstep (se 1 (by rfl) ⟨1197665, by rfl⟩ : syracuseStep 1596887 = 2395331) B2395331
theorem B1596907 : Blo 1594996 1596907 := bstep (se 1 (by rfl) ⟨1197680, by rfl⟩ : syracuseStep 1596907 = 2395361) B2395361
theorem B1596919 : Blo 1594996 1596919 := bstep (se 1 (by rfl) ⟨1197689, by rfl⟩ : syracuseStep 1596919 = 2395379) B2395379
theorem B3030529 : Blo 1594996 3030529 := bstep (se 2 (by rfl) ⟨1136448, by rfl⟩ : syracuseStep 3030529 = 2272897) B2272897
theorem B2694667 : Blo 1594996 2694667 := bstep (se 1 (by rfl) ⟨2021000, by rfl⟩ : syracuseStep 2694667 = 4042001) B4042001
theorem B1596939 : Blo 1594996 1596939 := bstep (se 1 (by rfl) ⟨1197704, by rfl⟩ : syracuseStep 1596939 = 2395409) B2395409
theorem B9084433 : Blo 1594996 9084433 := bstep (se 2 (by rfl) ⟨3406662, by rfl⟩ : syracuseStep 9084433 = 6813325) B6813325
theorem B1596951 : Blo 1594996 1596951 := bstep (se 1 (by rfl) ⟨1197713, by rfl⟩ : syracuseStep 1596951 = 2395427) B2395427
theorem B5389847 : Blo 1594996 5389847 := bstep (se 1 (by rfl) ⟨4042385, by rfl⟩ : syracuseStep 5389847 = 8084771) B8084771
theorem B1596971 : Blo 1594996 1596971 := bstep (se 1 (by rfl) ⟨1197728, by rfl⟩ : syracuseStep 1596971 = 2395457) B2395457
theorem B8306221 : Blo 1594996 8306221 := bstep (se 3 (by rfl) ⟨1557416, by rfl⟩ : syracuseStep 8306221 = 3114833) B3114833
theorem B1596983 : Blo 1594996 1596983 := bstep (se 1 (by rfl) ⟨1197737, by rfl⟩ : syracuseStep 1596983 = 2395475) B2395475
theorem B3833419 : Blo 1594996 3833419 := bstep (se 1 (by rfl) ⟨2875064, by rfl⟩ : syracuseStep 3833419 = 5750129) B5750129
theorem B3407449 : Blo 1594996 3407449 := bstep (se 2 (by rfl) ⟨1277793, by rfl⟩ : syracuseStep 3407449 = 2555587) B2555587
theorem B1728139 : Blo 1594996 1728139 := bstep (se 1 (by rfl) ⟨1296104, by rfl⟩ : syracuseStep 1728139 = 2592209) B2592209
theorem B4038295 : Blo 1594996 4038295 := bstep (se 1 (by rfl) ⟨3028721, by rfl⟩ : syracuseStep 4038295 = 6057443) B6057443
theorem B2694809 : Blo 1594996 2694809 := bstep (se 2 (by rfl) ⟨1010553, by rfl⟩ : syracuseStep 2694809 = 2021107) B2021107
theorem B6815411 : Blo 1594996 6815411 := bstep (se 1 (by rfl) ⟨5111558, by rfl⟩ : syracuseStep 6815411 = 10223117) B10223117
theorem B1703639 : Blo 1594996 1703639 := bstep (se 1 (by rfl) ⟨1277729, by rfl⟩ : syracuseStep 1703639 = 2555459) B2555459
theorem B7667531 : Blo 1594996 7667531 := bstep (se 1 (by rfl) ⟨5750648, by rfl⟩ : syracuseStep 7667531 = 11501297) B11501297
theorem B13639499 : Blo 1594996 13639499 := bstep (se 1 (by rfl) ⟨10229624, by rfl⟩ : syracuseStep 13639499 = 20459249) B20459249
theorem B3030871 : Blo 1594996 3030871 := bstep (se 1 (by rfl) ⟨2273153, by rfl⟩ : syracuseStep 3030871 = 4546307) B4546307
theorem B3235673 : Blo 1594996 3235673 := bstep (se 2 (by rfl) ⟨1213377, by rfl⟩ : syracuseStep 3235673 = 2426755) B2426755
theorem B98320229 : Blo 1594996 98320229 := bstep (se 4 (by rfl) ⟨9217521, by rfl⟩ : syracuseStep 98320229 = 18435043) B18435043
theorem B20447153 : Blo 1594996 20447153 := bstep (se 2 (by rfl) ⟨7667682, by rfl⟩ : syracuseStep 20447153 = 15335365) B15335365
theorem B12115979 : Blo 1594996 12115979 := bstep (se 1 (by rfl) ⟨9086984, by rfl⟩ : syracuseStep 12115979 = 18173969) B18173969
theorem B11509771 : Blo 1594996 11509771 := bstep (se 1 (by rfl) ⟨8632328, by rfl⟩ : syracuseStep 11509771 = 17264657) B17264657
theorem B5537803 : Blo 1594996 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B38830103 : Blo 1594996 38830103 := bstep (se 1 (by rfl) ⟨29122577, by rfl⟩ : syracuseStep 38830103 = 58245155) B58245155
theorem B9093181 : Blo 1594996 9093181 := bstep (se 3 (by rfl) ⟨1704971, by rfl⟩ : syracuseStep 9093181 = 3409943) B3409943
theorem B51740765 : Blo 1594996 51740765 := bstep (se 3 (by rfl) ⟨9701393, by rfl⟩ : syracuseStep 51740765 = 19402787) B19402787
theorem B2187383 : Blo 1594996 2187383 := bstep (se 1 (by rfl) ⟨1640537, by rfl⟩ : syracuseStep 2187383 = 3281075) B3281075
theorem B3031175 : Blo 1594996 3031175 := bstep (se 1 (by rfl) ⟨2273381, by rfl⟩ : syracuseStep 3031175 = 4546763) B4546763
theorem B4038923 : Blo 1594996 4038923 := bstep (se 1 (by rfl) ⟨3029192, by rfl⟩ : syracuseStep 4038923 = 6058385) B6058385
theorem B6816059 : Blo 1594996 6816059 := bstep (se 1 (by rfl) ⟨5112044, by rfl⟩ : syracuseStep 6816059 = 10224089) B10224089
theorem B6062471 : Blo 1594996 6062471 := bstep (se 1 (by rfl) ⟨4546853, by rfl⟩ : syracuseStep 6062471 = 9093707) B9093707
theorem B2392505 : Blo 1594996 2392505 := bstep (se 2 (by rfl) ⟨897189, by rfl⟩ : syracuseStep 2392505 = 1794379) B1794379
theorem B2392583 : Blo 1594996 2392583 := bstep (se 1 (by rfl) ⟨1794437, by rfl⟩ : syracuseStep 2392583 = 3588875) B3588875
theorem B13828637 : Blo 1594996 13828637 := bstep (se 3 (by rfl) ⟨2592869, by rfl⟩ : syracuseStep 13828637 = 5185739) B5185739
theorem B2392619 : Blo 1594996 2392619 := bstep (se 1 (by rfl) ⟨1794464, by rfl⟩ : syracuseStep 2392619 = 3588929) B3588929
theorem B2392649 : Blo 1594996 2392649 := bstep (se 2 (by rfl) ⟨897243, by rfl⟩ : syracuseStep 2392649 = 1794487) B1794487
theorem B2048647 : Blo 1594996 2048647 := bstep (se 1 (by rfl) ⟨1536485, by rfl⟩ : syracuseStep 2048647 = 3072971) B3072971
theorem B1794703 : Blo 1594996 1794703 := bstep (se 1 (by rfl) ⟨1346027, by rfl⟩ : syracuseStep 1794703 = 2692055) B2692055
theorem B2392763 : Blo 1594996 2392763 := bstep (se 1 (by rfl) ⟨1794572, by rfl⟩ : syracuseStep 2392763 = 3589145) B3589145
theorem B2392823 : Blo 1594996 2392823 := bstep (se 1 (by rfl) ⟨1794617, by rfl⟩ : syracuseStep 2392823 = 3589235) B3589235
theorem B2392847 : Blo 1594996 2392847 := bstep (se 1 (by rfl) ⟨1794635, by rfl⟩ : syracuseStep 2392847 = 3589271) B3589271
theorem B2392889 : Blo 1594996 2392889 := bstep (se 2 (by rfl) ⟨897333, by rfl⟩ : syracuseStep 2392889 = 1794667) B1794667
theorem B1704763 : Blo 1594996 1704763 := bstep (se 1 (by rfl) ⟨1278572, by rfl⟩ : syracuseStep 1704763 = 2557145) B2557145
theorem B3588983 : Blo 1594996 3588983 := bstep (se 1 (by rfl) ⟨2691737, by rfl⟩ : syracuseStep 3588983 = 5383475) B5383475
theorem B2392967 : Blo 1594996 2392967 := bstep (se 1 (by rfl) ⟨1794725, by rfl⟩ : syracuseStep 2392967 = 3589451) B3589451
theorem B4039571 : Blo 1594996 4039571 := bstep (se 1 (by rfl) ⟨3029678, by rfl⟩ : syracuseStep 4039571 = 6059357) B6059357
theorem B2393003 : Blo 1594996 2393003 := bstep (se 1 (by rfl) ⟨1794752, by rfl⟩ : syracuseStep 2393003 = 3589505) B3589505
theorem B2393033 : Blo 1594996 2393033 := bstep (se 2 (by rfl) ⟨897387, by rfl⟩ : syracuseStep 2393033 = 1794775) B1794775
theorem B3589163 : Blo 1594996 3589163 := bstep (se 1 (by rfl) ⟨2691872, by rfl⟩ : syracuseStep 3589163 = 5383745) B5383745
theorem B6816811 : Blo 1594996 6816811 := bstep (se 1 (by rfl) ⟨5112608, by rfl⟩ : syracuseStep 6816811 = 10225217) B10225217
theorem B2393147 : Blo 1594996 2393147 := bstep (se 1 (by rfl) ⟨1794860, by rfl⟩ : syracuseStep 2393147 = 3589721) B3589721
theorem B8627267 : Blo 1594996 8627267 := bstep (se 1 (by rfl) ⟨6470450, by rfl⟩ : syracuseStep 8627267 = 12940901) B12940901
theorem B2393207 : Blo 1594996 2393207 := bstep (se 1 (by rfl) ⟨1794905, by rfl⟩ : syracuseStep 2393207 = 3589811) B3589811
theorem B1795207 : Blo 1594996 1795207 := bstep (se 1 (by rfl) ⟨1346405, by rfl⟩ : syracuseStep 1795207 = 2692811) B2692811
theorem B2393231 : Blo 1594996 2393231 := bstep (se 1 (by rfl) ⟨1794923, by rfl⟩ : syracuseStep 2393231 = 3589847) B3589847
theorem B2876563 : Blo 1594996 2876563 := bstep (se 1 (by rfl) ⟨2157422, by rfl⟩ : syracuseStep 2876563 = 4314845) B4314845
theorem B3237011 : Blo 1594996 3237011 := bstep (se 1 (by rfl) ⟨2427758, by rfl⟩ : syracuseStep 3237011 = 4855517) B4855517
theorem B18171053 : Blo 1594996 18171053 := bstep (se 3 (by rfl) ⟨3407072, by rfl⟩ : syracuseStep 18171053 = 6814145) B6814145
theorem B4605113 : Blo 1594996 4605113 := bstep (se 2 (by rfl) ⟨1726917, by rfl⟩ : syracuseStep 4605113 = 3453835) B3453835
theorem B2393273 : Blo 1594996 2393273 := bstep (se 2 (by rfl) ⟨897477, by rfl⟩ : syracuseStep 2393273 = 1794955) B1794955
theorem B4039865 : Blo 1594996 4039865 := bstep (se 2 (by rfl) ⟨1514949, by rfl⟩ : syracuseStep 4039865 = 3029899) B3029899
theorem B2393351 : Blo 1594996 2393351 := bstep (se 1 (by rfl) ⟨1795013, by rfl⟩ : syracuseStep 2393351 = 3590027) B3590027
theorem B2393387 : Blo 1594996 2393387 := bstep (se 1 (by rfl) ⟨1795040, by rfl⟩ : syracuseStep 2393387 = 3590081) B3590081
theorem B1795387 : Blo 1594996 1795387 := bstep (se 1 (by rfl) ⟨1346540, by rfl⟩ : syracuseStep 1795387 = 2693081) B2693081
theorem B2393417 : Blo 1594996 2393417 := bstep (se 2 (by rfl) ⟨897531, by rfl⟩ : syracuseStep 2393417 = 1795063) B1795063
theorem B3589523 : Blo 1594996 3589523 := bstep (se 1 (by rfl) ⟨2692142, by rfl⟩ : syracuseStep 3589523 = 5384285) B5384285
theorem B7988633 : Blo 1594996 7988633 := bstep (se 2 (by rfl) ⟨2995737, by rfl⟩ : syracuseStep 7988633 = 5991475) B5991475
theorem B8078777 : Blo 1594996 8078777 := bstep (se 2 (by rfl) ⟨3029541, by rfl⟩ : syracuseStep 8078777 = 6059083) B6059083
theorem B2393531 : Blo 1594996 2393531 := bstep (se 1 (by rfl) ⟨1795148, by rfl⟩ : syracuseStep 2393531 = 3590297) B3590297
theorem B3589577 : Blo 1594996 3589577 := bstep (se 2 (by rfl) ⟨1346091, by rfl⟩ : syracuseStep 3589577 = 2692183) B2692183
theorem B9700811 : Blo 1594996 9700811 := bstep (se 1 (by rfl) ⟨7275608, by rfl⟩ : syracuseStep 9700811 = 14551217) B14551217
theorem B9086417 : Blo 1594996 9086417 := bstep (se 2 (by rfl) ⟨3407406, by rfl⟩ : syracuseStep 9086417 = 6814813) B6814813
theorem B2393591 : Blo 1594996 2393591 := bstep (se 1 (by rfl) ⟨1795193, by rfl⟩ : syracuseStep 2393591 = 3590387) B3590387
theorem B12125699 : Blo 1594996 12125699 := bstep (se 1 (by rfl) ⟨9094274, by rfl⟩ : syracuseStep 12125699 = 18188549) B18188549
theorem B5383691 : Blo 1594996 5383691 := bstep (se 1 (by rfl) ⟨4037768, by rfl⟩ : syracuseStep 5383691 = 8075537) B8075537
theorem B4851211 : Blo 1594996 4851211 := bstep (se 1 (by rfl) ⟨3638408, by rfl⟩ : syracuseStep 4851211 = 7276817) B7276817
theorem B2393615 : Blo 1594996 2393615 := bstep (se 1 (by rfl) ⟨1795211, by rfl⟩ : syracuseStep 2393615 = 3590423) B3590423
theorem B9709085 : Blo 1594996 9709085 := bstep (se 3 (by rfl) ⟨1820453, by rfl⟩ : syracuseStep 9709085 = 3640907) B3640907
theorem B2393657 : Blo 1594996 2393657 := bstep (se 2 (by rfl) ⟨897621, by rfl⟩ : syracuseStep 2393657 = 1795243) B1795243
theorem B5383799 : Blo 1594996 5383799 := bstep (se 1 (by rfl) ⟨4037849, by rfl⟩ : syracuseStep 5383799 = 8075699) B8075699
theorem B2393735 : Blo 1594996 2393735 := bstep (se 1 (by rfl) ⟨1795301, by rfl⟩ : syracuseStep 2393735 = 3590603) B3590603
theorem B2393771 : Blo 1594996 2393771 := bstep (se 1 (by rfl) ⟨1795328, by rfl⟩ : syracuseStep 2393771 = 3590657) B3590657
theorem B2393801 : Blo 1594996 2393801 := bstep (se 2 (by rfl) ⟨897675, by rfl⟩ : syracuseStep 2393801 = 1795351) B1795351
theorem B18179801 : Blo 1594996 18179801 := bstep (se 2 (by rfl) ⟨6817425, by rfl⟩ : syracuseStep 18179801 = 13634851) B13634851
theorem B3835649 : Blo 1594996 3835649 := bstep (se 2 (by rfl) ⟨1438368, by rfl⟩ : syracuseStep 3835649 = 2876737) B2876737
theorem B9094913 : Blo 1594996 9094913 := bstep (se 2 (by rfl) ⟨3410592, by rfl⟩ : syracuseStep 9094913 = 6821185) B6821185
theorem B1795855 : Blo 1594996 1795855 := bstep (se 1 (by rfl) ⟨1346891, by rfl⟩ : syracuseStep 1795855 = 2693783) B2693783
theorem B11667215 : Blo 1594996 11667215 := bstep (se 1 (by rfl) ⟨8750411, by rfl⟩ : syracuseStep 11667215 = 17500823) B17500823
theorem B2393915 : Blo 1594996 2393915 := bstep (se 1 (by rfl) ⟨1795436, by rfl⟩ : syracuseStep 2393915 = 3590873) B3590873
theorem B4040563 : Blo 1594996 4040563 := bstep (se 1 (by rfl) ⟨3030422, by rfl⟩ : syracuseStep 4040563 = 6060845) B6060845
theorem B2393975 : Blo 1594996 2393975 := bstep (se 1 (by rfl) ⟨1795481, by rfl⟩ : syracuseStep 2393975 = 3590963) B3590963
theorem B2393999 : Blo 1594996 2393999 := bstep (se 1 (by rfl) ⟨1795499, by rfl⟩ : syracuseStep 2393999 = 3590999) B3590999
theorem B12117923 : Blo 1594996 12117923 := bstep (se 1 (by rfl) ⟨9088442, by rfl⟩ : syracuseStep 12117923 = 18176885) B18176885
theorem B2394041 : Blo 1594996 2394041 := bstep (se 2 (by rfl) ⟨897765, by rfl⟩ : syracuseStep 2394041 = 1795531) B1795531
theorem B582748121 : Blo 1594996 582748121 := bstep (se 2 (by rfl) ⟨218530545, by rfl⟩ : syracuseStep 582748121 = 437061091) B437061091
theorem B4040705 : Blo 1594996 4040705 := bstep (se 2 (by rfl) ⟨1515264, by rfl⟩ : syracuseStep 4040705 = 3030529) B3030529
theorem B2394119 : Blo 1594996 2394119 := bstep (se 1 (by rfl) ⟨1795589, by rfl⟩ : syracuseStep 2394119 = 3591179) B3591179
theorem B2394155 : Blo 1594996 2394155 := bstep (se 1 (by rfl) ⟨1795616, by rfl⟩ : syracuseStep 2394155 = 3591233) B3591233
theorem B2394185 : Blo 1594996 2394185 := bstep (se 2 (by rfl) ⟨897819, by rfl⟩ : syracuseStep 2394185 = 1795639) B1795639
theorem B3590279 : Blo 1594996 3590279 := bstep (se 1 (by rfl) ⟨2692709, by rfl⟩ : syracuseStep 3590279 = 5385419) B5385419
theorem B2304185 : Blo 1594996 2304185 := bstep (se 2 (by rfl) ⟨864069, by rfl⟩ : syracuseStep 2304185 = 1728139) B1728139
theorem B2394299 : Blo 1594996 2394299 := bstep (se 1 (by rfl) ⟨1795724, by rfl⟩ : syracuseStep 2394299 = 3591449) B3591449
theorem B5384393 : Blo 1594996 5384393 := bstep (se 2 (by rfl) ⟨2019147, by rfl⟩ : syracuseStep 5384393 = 4038295) B4038295
theorem B15337673 : Blo 1594996 15337673 := bstep (se 2 (by rfl) ⟨5751627, by rfl⟩ : syracuseStep 15337673 = 11503255) B11503255
theorem B2394359 : Blo 1594996 2394359 := bstep (se 1 (by rfl) ⟨1795769, by rfl⟩ : syracuseStep 2394359 = 3591539) B3591539
theorem B1796359 : Blo 1594996 1796359 := bstep (se 1 (by rfl) ⟨1347269, by rfl⟩ : syracuseStep 1796359 = 2694539) B2694539
theorem B2394383 : Blo 1594996 2394383 := bstep (se 1 (by rfl) ⟨1795787, by rfl⟩ : syracuseStep 2394383 = 3591575) B3591575
theorem B2394425 : Blo 1594996 2394425 := bstep (se 2 (by rfl) ⟨897909, by rfl⟩ : syracuseStep 2394425 = 1795819) B1795819
theorem B3590459 : Blo 1594996 3590459 := bstep (se 1 (by rfl) ⟨2692844, by rfl⟩ : syracuseStep 3590459 = 5385689) B5385689
theorem B2394503 : Blo 1594996 2394503 := bstep (se 1 (by rfl) ⟨1795877, by rfl⟩ : syracuseStep 2394503 = 3591755) B3591755
theorem B2394539 : Blo 1594996 2394539 := bstep (se 1 (by rfl) ⟨1795904, by rfl⟩ : syracuseStep 2394539 = 3591809) B3591809
theorem B3590585 : Blo 1594996 3590585 := bstep (se 2 (by rfl) ⟨1346469, by rfl⟩ : syracuseStep 3590585 = 2692939) B2692939
theorem B1796539 : Blo 1594996 1796539 := bstep (se 1 (by rfl) ⟨1347404, by rfl⟩ : syracuseStep 1796539 = 2694809) B2694809
theorem B2394569 : Blo 1594996 2394569 := bstep (se 2 (by rfl) ⟨897963, by rfl⟩ : syracuseStep 2394569 = 1795927) B1795927
theorem B4041161 : Blo 1594996 4041161 := bstep (se 2 (by rfl) ⟨1515435, by rfl⟩ : syracuseStep 4041161 = 3030871) B3030871
theorem B7670219 : Blo 1594996 7670219 := bstep (se 1 (by rfl) ⟨5752664, by rfl⟩ : syracuseStep 7670219 = 11505329) B11505329
theorem B2157115 : Blo 1594996 2157115 := bstep (se 1 (by rfl) ⟨1617836, by rfl⟩ : syracuseStep 2157115 = 3235673) B3235673
theorem B2394683 : Blo 1594996 2394683 := bstep (se 1 (by rfl) ⟨1796012, by rfl⟩ : syracuseStep 2394683 = 3592025) B3592025
theorem B65546819 : Blo 1594996 65546819 := bstep (se 1 (by rfl) ⟨49160114, by rfl⟩ : syracuseStep 65546819 = 98320229) B98320229
theorem B4311667 : Blo 1594996 4311667 := bstep (se 1 (by rfl) ⟨3233750, by rfl⟩ : syracuseStep 4311667 = 6467501) B6467501
theorem B2394743 : Blo 1594996 2394743 := bstep (se 1 (by rfl) ⟨1796057, by rfl⟩ : syracuseStep 2394743 = 3592115) B3592115
theorem B2394767 : Blo 1594996 2394767 := bstep (se 1 (by rfl) ⟨1796075, by rfl⟩ : syracuseStep 2394767 = 3592151) B3592151
theorem B2394809 : Blo 1594996 2394809 := bstep (se 2 (by rfl) ⟨898053, by rfl⟩ : syracuseStep 2394809 = 1796107) B1796107
theorem B8080073 : Blo 1594996 8080073 := bstep (se 2 (by rfl) ⟨3030027, by rfl⟩ : syracuseStep 8080073 = 6060055) B6060055
theorem B2394887 : Blo 1594996 2394887 := bstep (se 1 (by rfl) ⟨1796165, by rfl⟩ : syracuseStep 2394887 = 3592331) B3592331
theorem B3590927 : Blo 1594996 3590927 := bstep (se 1 (by rfl) ⟨2693195, by rfl⟩ : syracuseStep 3590927 = 5386391) B5386391
theorem B3590945 : Blo 1594996 3590945 := bstep (se 2 (by rfl) ⟨1346604, by rfl⟩ : syracuseStep 3590945 = 2693209) B2693209
theorem B2394923 : Blo 1594996 2394923 := bstep (se 1 (by rfl) ⟨1796192, by rfl⟩ : syracuseStep 2394923 = 3592385) B3592385
theorem B4041515 : Blo 1594996 4041515 := bstep (se 1 (by rfl) ⟨3031136, by rfl⟩ : syracuseStep 4041515 = 6062273) B6062273
theorem B2394953 : Blo 1594996 2394953 := bstep (se 2 (by rfl) ⟨898107, by rfl⟩ : syracuseStep 2394953 = 1796215) B1796215
theorem B5385095 : Blo 1594996 5385095 := bstep (se 1 (by rfl) ⟨4038821, by rfl⟩ : syracuseStep 5385095 = 8077643) B8077643
theorem B2395067 : Blo 1594996 2395067 := bstep (se 1 (by rfl) ⟨1796300, by rfl⟩ : syracuseStep 2395067 = 3592601) B3592601
theorem B9210833 : Blo 1594996 9210833 := bstep (se 2 (by rfl) ⟨3454062, by rfl⟩ : syracuseStep 9210833 = 6908125) B6908125
theorem B2395127 : Blo 1594996 2395127 := bstep (se 1 (by rfl) ⟨1796345, by rfl⟩ : syracuseStep 2395127 = 3592691) B3592691
theorem B2395151 : Blo 1594996 2395151 := bstep (se 1 (by rfl) ⟨1796363, by rfl⟩ : syracuseStep 2395151 = 3592727) B3592727
theorem B10914839 : Blo 1594996 10914839 := bstep (se 1 (by rfl) ⟨8186129, by rfl⟩ : syracuseStep 10914839 = 16372259) B16372259
theorem B2395193 : Blo 1594996 2395193 := bstep (se 2 (by rfl) ⟨898197, by rfl⟩ : syracuseStep 2395193 = 1796395) B1796395
theorem B3591287 : Blo 1594996 3591287 := bstep (se 1 (by rfl) ⟨2693465, by rfl⟩ : syracuseStep 3591287 = 5386931) B5386931
theorem B2395271 : Blo 1594996 2395271 := bstep (se 1 (by rfl) ⟨1796453, by rfl⟩ : syracuseStep 2395271 = 3592907) B3592907
theorem B2395307 : Blo 1594996 2395307 := bstep (se 1 (by rfl) ⟨1796480, by rfl⟩ : syracuseStep 2395307 = 3592961) B3592961
theorem B4918457 : Blo 1594996 4918457 := bstep (se 2 (by rfl) ⟨1844421, by rfl⟩ : syracuseStep 4918457 = 3688843) B3688843
theorem B2395337 : Blo 1594996 2395337 := bstep (se 2 (by rfl) ⟨898251, by rfl⟩ : syracuseStep 2395337 = 1796503) B1796503
theorem B5385473 : Blo 1594996 5385473 := bstep (se 2 (by rfl) ⟨2019552, by rfl⟩ : syracuseStep 5385473 = 4039105) B4039105
theorem B3591467 : Blo 1594996 3591467 := bstep (se 1 (by rfl) ⟨2693600, by rfl⟩ : syracuseStep 3591467 = 5387201) B5387201
theorem B9088307 : Blo 1594996 9088307 := bstep (se 1 (by rfl) ⟨6816230, by rfl⟩ : syracuseStep 9088307 = 13632461) B13632461
theorem B2395451 : Blo 1594996 2395451 := bstep (se 1 (by rfl) ⟨1796588, by rfl⟩ : syracuseStep 2395451 = 3593177) B3593177
theorem B6819187 : Blo 1594996 6819187 := bstep (se 1 (by rfl) ⟨5114390, by rfl⟩ : syracuseStep 6819187 = 10228781) B10228781
theorem B4918681 : Blo 1594996 4918681 := bstep (se 2 (by rfl) ⟨1844505, by rfl⟩ : syracuseStep 4918681 = 3689011) B3689011
theorem B9702935 : Blo 1594996 9702935 := bstep (se 1 (by rfl) ⟨7277201, by rfl⟩ : syracuseStep 9702935 = 14554403) B14554403
theorem B2018935 : Blo 1594996 2018935 := bstep (se 1 (by rfl) ⟨1514201, by rfl⟩ : syracuseStep 2018935 = 3028403) B3028403
theorem B2731639 : Blo 1594996 2731639 := bstep (se 1 (by rfl) ⟨2048729, by rfl⟩ : syracuseStep 2731639 = 4097459) B4097459
theorem B3591827 : Blo 1594996 3591827 := bstep (se 1 (by rfl) ⟨2693870, by rfl⟩ : syracuseStep 3591827 = 5387741) B5387741
theorem B3591881 : Blo 1594996 3591881 := bstep (se 2 (by rfl) ⟨1346955, by rfl⟩ : syracuseStep 3591881 = 2693911) B2693911
theorem B17248049 : Blo 1594996 17248049 := bstep (se 2 (by rfl) ⟨6468018, by rfl⟩ : syracuseStep 17248049 = 12936037) B12936037
theorem B2019259 : Blo 1594996 2019259 := bstep (se 1 (by rfl) ⟨1514444, by rfl⟩ : syracuseStep 2019259 = 3028889) B3028889
theorem B5386283 : Blo 1594996 5386283 := bstep (se 1 (by rfl) ⟨4039712, by rfl⟩ : syracuseStep 5386283 = 8079425) B8079425
theorem B4853803 : Blo 1594996 4853803 := bstep (se 1 (by rfl) ⟨3640352, by rfl⟩ : syracuseStep 4853803 = 7280705) B7280705
theorem B30658733 : Blo 1594996 30658733 := bstep (se 3 (by rfl) ⟨5748512, by rfl⟩ : syracuseStep 30658733 = 11497025) B11497025
theorem B5460239 : Blo 1594996 5460239 := bstep (se 1 (by rfl) ⟨4095179, by rfl⟩ : syracuseStep 5460239 = 8190359) B8190359
theorem B12120353 : Blo 1594996 12120353 := bstep (se 2 (by rfl) ⟨4545132, by rfl⟩ : syracuseStep 12120353 = 9090265) B9090265
theorem B2273609 : Blo 1594996 2273609 := bstep (se 2 (by rfl) ⟨852603, by rfl⟩ : syracuseStep 2273609 = 1705207) B1705207
theorem B36868445 : Blo 1594996 36868445 := bstep (se 3 (by rfl) ⟨6912833, by rfl⟩ : syracuseStep 36868445 = 13825667) B13825667
theorem B3592583 : Blo 1594996 3592583 := bstep (se 1 (by rfl) ⟨2694437, by rfl⟩ : syracuseStep 3592583 = 5388875) B5388875
theorem B2019755 : Blo 1594996 2019755 := bstep (se 1 (by rfl) ⟨1514816, by rfl⟩ : syracuseStep 2019755 = 3029633) B3029633
theorem B10228189 : Blo 1594996 10228189 := bstep (se 3 (by rfl) ⟨1917785, by rfl⟩ : syracuseStep 10228189 = 3835571) B3835571
theorem B2691643 : Blo 1594996 2691643 := bstep (se 1 (by rfl) ⟨2018732, by rfl⟩ : syracuseStep 2691643 = 4037465) B4037465
theorem B3592763 : Blo 1594996 3592763 := bstep (se 1 (by rfl) ⟨2694572, by rfl⟩ : syracuseStep 3592763 = 5389145) B5389145
theorem B4543037 : Blo 1594996 4543037 := bstep (se 3 (by rfl) ⟨851819, by rfl⟩ : syracuseStep 4543037 = 1703639) B1703639
theorem B6058583 : Blo 1594996 6058583 := bstep (se 1 (by rfl) ⟨4543937, by rfl⟩ : syracuseStep 6058583 = 9087875) B9087875
theorem B15340211 : Blo 1594996 15340211 := bstep (se 1 (by rfl) ⟨11505158, by rfl⟩ : syracuseStep 15340211 = 23010317) B23010317
theorem B3592889 : Blo 1594996 3592889 := bstep (se 2 (by rfl) ⟨1347333, by rfl⟩ : syracuseStep 3592889 = 2694667) B2694667
theorem B12112577 : Blo 1594996 12112577 := bstep (se 2 (by rfl) ⟨4542216, by rfl⟩ : syracuseStep 12112577 = 9084433) B9084433
theorem B2691785 : Blo 1594996 2691785 := bstep (se 2 (by rfl) ⟨1009419, by rfl⟩ : syracuseStep 2691785 = 2018839) B2018839
theorem B9089765 : Blo 1594996 9089765 := bstep (se 4 (by rfl) ⟨852165, by rfl⟩ : syracuseStep 9089765 = 1704331) B1704331
theorem B4543265 : Blo 1594996 4543265 := bstep (se 2 (by rfl) ⟨1703724, by rfl⟩ : syracuseStep 4543265 = 3407449) B3407449
theorem B8631073 : Blo 1594996 8631073 := bstep (se 2 (by rfl) ⟨3236652, by rfl⟩ : syracuseStep 8631073 = 6473305) B6473305
theorem B4854589 : Blo 1594996 4854589 := bstep (se 3 (by rfl) ⟨910235, by rfl⟩ : syracuseStep 4854589 = 1820471) B1820471
theorem B2020231 : Blo 1594996 2020231 := bstep (se 1 (by rfl) ⟨1515173, by rfl⟩ : syracuseStep 2020231 = 3030347) B3030347
theorem B3593231 : Blo 1594996 3593231 := bstep (se 1 (by rfl) ⟨2694923, by rfl⟩ : syracuseStep 3593231 = 5389847) B5389847
theorem B6059069 : Blo 1594996 6059069 := bstep (se 3 (by rfl) ⟨1136075, by rfl⟩ : syracuseStep 6059069 = 2272151) B2272151
theorem B4543607 : Blo 1594996 4543607 := bstep (se 1 (by rfl) ⟨3407705, by rfl⟩ : syracuseStep 4543607 = 6815411) B6815411
theorem B12121325 : Blo 1594996 12121325 := bstep (se 3 (by rfl) ⟨2272748, by rfl⟩ : syracuseStep 12121325 = 4545497) B4545497
theorem B5387579 : Blo 1594996 5387579 := bstep (se 1 (by rfl) ⟨4040684, by rfl⟩ : syracuseStep 5387579 = 8081369) B8081369
theorem B79787381 : Blo 1594996 79787381 := bstep (se 5 (by rfl) ⟨3740033, by rfl⟩ : syracuseStep 79787381 = 7480067) B7480067
theorem B2020727 : Blo 1594996 2020727 := bstep (se 1 (by rfl) ⟨1515545, by rfl⟩ : syracuseStep 2020727 = 3031091) B3031091
theorem B2692487 : Blo 1594996 2692487 := bstep (se 1 (by rfl) ⟨2019365, by rfl⟩ : syracuseStep 2692487 = 4038731) B4038731
theorem B2020879 : Blo 1594996 2020879 := bstep (se 1 (by rfl) ⟨1515659, by rfl⟩ : syracuseStep 2020879 = 3031319) B3031319
theorem B46003787 : Blo 1594996 46003787 := bstep (se 1 (by rfl) ⟨34502840, by rfl⟩ : syracuseStep 46003787 = 69005681) B69005681
theorem B1595015 : Blo 1594996 1595015 := bstep (se 1 (by rfl) ⟨1196261, by rfl⟩ : syracuseStep 1595015 = 2392523) B2392523
theorem B1595023 : Blo 1594996 1595023 := bstep (se 1 (by rfl) ⟨1196267, by rfl⟩ : syracuseStep 1595023 = 2392535) B2392535
theorem B1595067 : Blo 1594996 1595067 := bstep (se 1 (by rfl) ⟨1196300, by rfl⟩ : syracuseStep 1595067 = 2392601) B2392601
theorem B2021051 : Blo 1594996 2021051 := bstep (se 1 (by rfl) ⟨1515788, by rfl⟩ : syracuseStep 2021051 = 3031577) B3031577
theorem B7878401 : Blo 1594996 7878401 := bstep (se 2 (by rfl) ⟨2954400, by rfl⟩ : syracuseStep 7878401 = 5908801) B5908801
theorem B1595143 : Blo 1594996 1595143 := bstep (se 1 (by rfl) ⟨1196357, by rfl⟩ : syracuseStep 1595143 = 2392715) B2392715
theorem B1595151 : Blo 1594996 1595151 := bstep (se 1 (by rfl) ⟨1196363, by rfl⟩ : syracuseStep 1595151 = 2392727) B2392727
theorem B5388065 : Blo 1594996 5388065 := bstep (se 2 (by rfl) ⟨2020524, by rfl⟩ : syracuseStep 5388065 = 4041049) B4041049
theorem B8189747 : Blo 1594996 8189747 := bstep (se 1 (by rfl) ⟨6142310, by rfl⟩ : syracuseStep 8189747 = 12284621) B12284621
theorem B1595195 : Blo 1594996 1595195 := bstep (se 1 (by rfl) ⟨1196396, by rfl⟩ : syracuseStep 1595195 = 2392793) B2392793
theorem B1595271 : Blo 1594996 1595271 := bstep (se 1 (by rfl) ⟨1196453, by rfl⟩ : syracuseStep 1595271 = 2392907) B2392907
theorem B1595279 : Blo 1594996 1595279 := bstep (se 1 (by rfl) ⟨1196459, by rfl⟩ : syracuseStep 1595279 = 2392919) B2392919
theorem B1595323 : Blo 1594996 1595323 := bstep (se 1 (by rfl) ⟨1196492, by rfl⟩ : syracuseStep 1595323 = 2392985) B2392985
theorem B1595399 : Blo 1594996 1595399 := bstep (se 1 (by rfl) ⟨1196549, by rfl⟩ : syracuseStep 1595399 = 2393099) B2393099
theorem B1595407 : Blo 1594996 1595407 := bstep (se 1 (by rfl) ⟨1196555, by rfl⟩ : syracuseStep 1595407 = 2393111) B2393111
theorem B2693135 : Blo 1594996 2693135 := bstep (se 1 (by rfl) ⟨2019851, by rfl⟩ : syracuseStep 2693135 = 4039703) B4039703
theorem B1595451 : Blo 1594996 1595451 := bstep (se 1 (by rfl) ⟨1196588, by rfl⟩ : syracuseStep 1595451 = 2393177) B2393177
theorem B5748803 : Blo 1594996 5748803 := bstep (se 1 (by rfl) ⟨4311602, by rfl⟩ : syracuseStep 5748803 = 8623205) B8623205
theorem B1595527 : Blo 1594996 1595527 := bstep (se 1 (by rfl) ⟨1196645, by rfl⟩ : syracuseStep 1595527 = 2393291) B2393291
theorem B1595535 : Blo 1594996 1595535 := bstep (se 1 (by rfl) ⟨1196651, by rfl⟩ : syracuseStep 1595535 = 2393303) B2393303
theorem B3029177 : Blo 1594996 3029177 := bstep (se 2 (by rfl) ⟨1135941, by rfl⟩ : syracuseStep 3029177 = 2271883) B2271883
theorem B1595579 : Blo 1594996 1595579 := bstep (se 1 (by rfl) ⟨1196684, by rfl⟩ : syracuseStep 1595579 = 2393369) B2393369
theorem B1595655 : Blo 1594996 1595655 := bstep (se 1 (by rfl) ⟨1196741, by rfl⟩ : syracuseStep 1595655 = 2393483) B2393483
theorem B1595663 : Blo 1594996 1595663 := bstep (se 1 (by rfl) ⟨1196747, by rfl⟩ : syracuseStep 1595663 = 2393495) B2393495
theorem B1595707 : Blo 1594996 1595707 := bstep (se 1 (by rfl) ⟨1196780, by rfl⟩ : syracuseStep 1595707 = 2393561) B2393561
theorem B5388659 : Blo 1594996 5388659 := bstep (se 1 (by rfl) ⟨4041494, by rfl⟩ : syracuseStep 5388659 = 8082989) B8082989
theorem B17250691 : Blo 1594996 17250691 := bstep (se 1 (by rfl) ⟨12938018, by rfl⟩ : syracuseStep 17250691 = 25876037) B25876037
theorem B1595783 : Blo 1594996 1595783 := bstep (se 1 (by rfl) ⟨1196837, by rfl⟩ : syracuseStep 1595783 = 2393675) B2393675
theorem B1595791 : Blo 1594996 1595791 := bstep (se 1 (by rfl) ⟨1196843, by rfl⟩ : syracuseStep 1595791 = 2393687) B2393687
theorem B1595835 : Blo 1594996 1595835 := bstep (se 1 (by rfl) ⟨1196876, by rfl⟩ : syracuseStep 1595835 = 2393753) B2393753
theorem B1595911 : Blo 1594996 1595911 := bstep (se 1 (by rfl) ⟨1196933, by rfl⟩ : syracuseStep 1595911 = 2393867) B2393867
theorem B1595919 : Blo 1594996 1595919 := bstep (se 1 (by rfl) ⟨1196939, by rfl⟩ : syracuseStep 1595919 = 2393879) B2393879
theorem B2693675 : Blo 1594996 2693675 := bstep (se 1 (by rfl) ⟨2020256, by rfl⟩ : syracuseStep 2693675 = 4040513) B4040513
theorem B1595963 : Blo 1594996 1595963 := bstep (se 1 (by rfl) ⟨1196972, by rfl⟩ : syracuseStep 1595963 = 2393945) B2393945
theorem B1596039 : Blo 1594996 1596039 := bstep (se 1 (by rfl) ⟨1197029, by rfl⟩ : syracuseStep 1596039 = 2394059) B2394059
theorem B1596047 : Blo 1594996 1596047 := bstep (se 1 (by rfl) ⟨1197035, by rfl⟩ : syracuseStep 1596047 = 2394071) B2394071
theorem B1596091 : Blo 1594996 1596091 := bstep (se 1 (by rfl) ⟨1197068, by rfl⟩ : syracuseStep 1596091 = 2394137) B2394137
theorem B1596167 : Blo 1594996 1596167 := bstep (se 1 (by rfl) ⟨1197125, by rfl⟩ : syracuseStep 1596167 = 2394251) B2394251
theorem B1596175 : Blo 1594996 1596175 := bstep (se 1 (by rfl) ⟨1197131, by rfl⟩ : syracuseStep 1596175 = 2394263) B2394263
theorem B6060815 : Blo 1594996 6060815 := bstep (se 1 (by rfl) ⟨4545611, by rfl⟩ : syracuseStep 6060815 = 9091223) B9091223
theorem B4037435 : Blo 1594996 4037435 := bstep (se 1 (by rfl) ⟨3028076, by rfl⟩ : syracuseStep 4037435 = 6056153) B6056153
theorem B1596219 : Blo 1594996 1596219 := bstep (se 1 (by rfl) ⟨1197164, by rfl⟩ : syracuseStep 1596219 = 2394329) B2394329
theorem B1596295 : Blo 1594996 1596295 := bstep (se 1 (by rfl) ⟨1197221, by rfl⟩ : syracuseStep 1596295 = 2394443) B2394443
theorem B1596303 : Blo 1594996 1596303 := bstep (se 1 (by rfl) ⟨1197227, by rfl⟩ : syracuseStep 1596303 = 2394455) B2394455
theorem B8076185 : Blo 1594996 8076185 := bstep (se 2 (by rfl) ⟨3028569, by rfl⟩ : syracuseStep 8076185 = 6057139) B6057139
theorem B4316057 : Blo 1594996 4316057 := bstep (se 2 (by rfl) ⟨1618521, by rfl⟩ : syracuseStep 4316057 = 3237043) B3237043
theorem B2694073 : Blo 1594996 2694073 := bstep (se 2 (by rfl) ⟨1010277, by rfl⟩ : syracuseStep 2694073 = 2020555) B2020555
theorem B1596347 : Blo 1594996 1596347 := bstep (se 1 (by rfl) ⟨1197260, by rfl⟩ : syracuseStep 1596347 = 2394521) B2394521
theorem B1596423 : Blo 1594996 1596423 := bstep (se 1 (by rfl) ⟨1197317, by rfl⟩ : syracuseStep 1596423 = 2394635) B2394635
theorem B4037647 : Blo 1594996 4037647 := bstep (se 1 (by rfl) ⟨3028235, by rfl⟩ : syracuseStep 4037647 = 6056471) B6056471
theorem B1596431 : Blo 1594996 1596431 := bstep (se 1 (by rfl) ⟨1197323, by rfl⟩ : syracuseStep 1596431 = 2394647) B2394647
theorem B1596475 : Blo 1594996 1596475 := bstep (se 1 (by rfl) ⟨1197356, by rfl⟩ : syracuseStep 1596475 = 2394713) B2394713
theorem B8633411 : Blo 1594996 8633411 := bstep (se 1 (by rfl) ⟨6475058, by rfl⟩ : syracuseStep 8633411 = 12950117) B12950117
theorem B12123269 : Blo 1594996 12123269 := bstep (se 4 (by rfl) ⟨1136556, by rfl⟩ : syracuseStep 12123269 = 2273113) B2273113
theorem B1596551 : Blo 1594996 1596551 := bstep (se 1 (by rfl) ⟨1197413, by rfl⟩ : syracuseStep 1596551 = 2394827) B2394827
theorem B1596559 : Blo 1594996 1596559 := bstep (se 1 (by rfl) ⟨1197419, by rfl⟩ : syracuseStep 1596559 = 2394839) B2394839
theorem B1596603 : Blo 1594996 1596603 := bstep (se 1 (by rfl) ⟨1197452, by rfl⟩ : syracuseStep 1596603 = 2394905) B2394905
theorem B1596679 : Blo 1594996 1596679 := bstep (se 1 (by rfl) ⟨1197509, by rfl⟩ : syracuseStep 1596679 = 2395019) B2395019
theorem B1596687 : Blo 1594996 1596687 := bstep (se 1 (by rfl) ⟨1197515, by rfl⟩ : syracuseStep 1596687 = 2395031) B2395031
theorem B4037921 : Blo 1594996 4037921 := bstep (se 2 (by rfl) ⟨1514220, by rfl⟩ : syracuseStep 4037921 = 3028441) B3028441
theorem B2915627 : Blo 1594996 2915627 := bstep (se 1 (by rfl) ⟨2186720, by rfl⟩ : syracuseStep 2915627 = 4373441) B4373441
theorem B1596731 : Blo 1594996 1596731 := bstep (se 1 (by rfl) ⟨1197548, by rfl⟩ : syracuseStep 1596731 = 2395097) B2395097
theorem B32742787 : Blo 1594996 32742787 := bstep (se 1 (by rfl) ⟨24557090, by rfl⟩ : syracuseStep 32742787 = 49114181) B49114181
theorem B1596807 : Blo 1594996 1596807 := bstep (se 1 (by rfl) ⟨1197605, by rfl⟩ : syracuseStep 1596807 = 2395211) B2395211
theorem B1596815 : Blo 1594996 1596815 := bstep (se 1 (by rfl) ⟨1197611, by rfl⟩ : syracuseStep 1596815 = 2395223) B2395223
theorem B11074961 : Blo 1594996 11074961 := bstep (se 2 (by rfl) ⟨4153110, by rfl⟩ : syracuseStep 11074961 = 8306221) B8306221
theorem B5111225 : Blo 1594996 5111225 := bstep (se 2 (by rfl) ⟨1916709, by rfl⟩ : syracuseStep 5111225 = 3833419) B3833419
theorem B1596859 : Blo 1594996 1596859 := bstep (se 1 (by rfl) ⟨1197644, by rfl⟩ : syracuseStep 1596859 = 2395289) B2395289
theorem B29122001 : Blo 1594996 29122001 := bstep (se 2 (by rfl) ⟨10920750, by rfl⟩ : syracuseStep 29122001 = 21841501) B21841501
theorem B1596935 : Blo 1594996 1596935 := bstep (se 1 (by rfl) ⟨1197701, by rfl⟩ : syracuseStep 1596935 = 2395403) B2395403
theorem B2555407 : Blo 1594996 2555407 := bstep (se 1 (by rfl) ⟨1916555, by rfl⟩ : syracuseStep 2555407 = 3833111) B3833111
theorem B1596943 : Blo 1594996 1596943 := bstep (se 1 (by rfl) ⟨1197707, by rfl⟩ : syracuseStep 1596943 = 2395415) B2395415
theorem B1596987 : Blo 1594996 1596987 := bstep (se 1 (by rfl) ⟨1197740, by rfl⟩ : syracuseStep 1596987 = 2395481) B2395481
theorem B4546135 : Blo 1594996 4546135 := bstep (se 1 (by rfl) ⟨3409601, by rfl⟩ : syracuseStep 4546135 = 6819203) B6819203
theorem B39353957 : Blo 1594996 39353957 := bstep (se 4 (by rfl) ⟨3689433, by rfl⟩ : syracuseStep 39353957 = 7378867) B7378867
theorem B2694775 : Blo 1594996 2694775 := bstep (se 1 (by rfl) ⟨2021081, by rfl⟩ : syracuseStep 2694775 = 4042163) B4042163
theorem B2875151 : Blo 1594996 2875151 := bstep (se 1 (by rfl) ⟨2156363, by rfl⟩ : syracuseStep 2875151 = 4312727) B4312727
theorem B4546363 : Blo 1594996 4546363 := bstep (se 1 (by rfl) ⟨3409772, by rfl⟩ : syracuseStep 4546363 = 6819545) B6819545
theorem B5111687 : Blo 1594996 5111687 := bstep (se 1 (by rfl) ⟨3833765, by rfl⟩ : syracuseStep 5111687 = 7667531) B7667531
theorem B9092999 : Blo 1594996 9092999 := bstep (se 1 (by rfl) ⟨6819749, by rfl⟩ : syracuseStep 9092999 = 13639499) B13639499
theorem B4546489 : Blo 1594996 4546489 := bstep (se 2 (by rfl) ⟨1704933, by rfl⟩ : syracuseStep 4546489 = 3409867) B3409867
theorem B13631435 : Blo 1594996 13631435 := bstep (se 1 (by rfl) ⟨10223576, by rfl⟩ : syracuseStep 13631435 = 20447153) B20447153
theorem B8077319 : Blo 1594996 8077319 := bstep (se 1 (by rfl) ⟨6057989, by rfl⟩ : syracuseStep 8077319 = 12115979) B12115979
theorem B25886735 : Blo 1594996 25886735 := bstep (se 1 (by rfl) ⟨19415051, by rfl⟩ : syracuseStep 25886735 = 38830103) B38830103
theorem B6471737 : Blo 1594996 6471737 := bstep (se 2 (by rfl) ⟨2426901, by rfl⟩ : syracuseStep 6471737 = 4853803) B4853803
theorem B12124241 : Blo 1594996 12124241 := bstep (se 2 (by rfl) ⟨4546590, by rfl⟩ : syracuseStep 12124241 = 9093181) B9093181
theorem B20439155 : Blo 1594996 20439155 := bstep (se 1 (by rfl) ⟨15329366, by rfl⟩ : syracuseStep 20439155 = 30658733) B30658733
theorem B5833021 : Blo 1594996 5833021 := bstep (se 3 (by rfl) ⟨1093691, by rfl⟩ : syracuseStep 5833021 = 2187383) B2187383
theorem B4039055 : Blo 1594996 4039055 := bstep (se 1 (by rfl) ⟨3029291, by rfl⟩ : syracuseStep 4039055 = 6058583) B6058583
theorem B1794523 : Blo 1594996 1794523 := bstep (se 1 (by rfl) ⟨1345892, by rfl⟩ : syracuseStep 1794523 = 2691785) B2691785
theorem B8077805 : Blo 1594996 8077805 := bstep (se 3 (by rfl) ⟨1514588, by rfl⟩ : syracuseStep 8077805 = 3029177) B3029177
theorem B6144493 : Blo 1594996 6144493 := bstep (se 3 (by rfl) ⟨1152092, by rfl⟩ : syracuseStep 6144493 = 2304185) B2304185
theorem B2392655 : Blo 1594996 2392655 := bstep (se 1 (by rfl) ⟨1794491, by rfl⟩ : syracuseStep 2392655 = 3588983) B3588983
theorem B2392775 : Blo 1594996 2392775 := bstep (se 1 (by rfl) ⟨1794581, by rfl⟩ : syracuseStep 2392775 = 3589163) B3589163
theorem B4039379 : Blo 1594996 4039379 := bstep (se 1 (by rfl) ⟨3029534, by rfl⟩ : syracuseStep 4039379 = 6059069) B6059069
theorem B3588857 : Blo 1594996 3588857 := bstep (se 2 (by rfl) ⟨1345821, by rfl⟩ : syracuseStep 3588857 = 2691643) B2691643
theorem B2876153 : Blo 1594996 2876153 := bstep (se 2 (by rfl) ⟨1078557, by rfl⟩ : syracuseStep 2876153 = 2157115) B2157115
theorem B2392937 : Blo 1594996 2392937 := bstep (se 2 (by rfl) ⟨897351, by rfl⟩ : syracuseStep 2392937 = 1794703) B1794703
theorem B6062957 : Blo 1594996 6062957 := bstep (se 3 (by rfl) ⟨1136804, by rfl⟩ : syracuseStep 6062957 = 2273609) B2273609
theorem B1794991 : Blo 1594996 1794991 := bstep (se 1 (by rfl) ⟨1346243, by rfl⟩ : syracuseStep 1794991 = 2692487) B2692487
theorem B2393015 : Blo 1594996 2393015 := bstep (se 1 (by rfl) ⟨1794761, by rfl⟩ : syracuseStep 2393015 = 3589523) B3589523
theorem B5325755 : Blo 1594996 5325755 := bstep (se 1 (by rfl) ⟨3994316, by rfl⟩ : syracuseStep 5325755 = 7988633) B7988633
theorem B2393051 : Blo 1594996 2393051 := bstep (se 1 (by rfl) ⟨1794788, by rfl⟩ : syracuseStep 2393051 = 3589577) B3589577
theorem B3589127 : Blo 1594996 3589127 := bstep (se 1 (by rfl) ⟨2691845, by rfl⟩ : syracuseStep 3589127 = 5383691) B5383691
theorem B6472723 : Blo 1594996 6472723 := bstep (se 1 (by rfl) ⟨4854542, by rfl⟩ : syracuseStep 6472723 = 9709085) B9709085
theorem B3589199 : Blo 1594996 3589199 := bstep (se 1 (by rfl) ⟨2691899, by rfl⟩ : syracuseStep 3589199 = 5383799) B5383799
theorem B5252267 : Blo 1594996 5252267 := bstep (se 1 (by rfl) ⟨3939200, by rfl⟩ : syracuseStep 5252267 = 7878401) B7878401
theorem B2557099 : Blo 1594996 2557099 := bstep (se 1 (by rfl) ⟨1917824, by rfl⟩ : syracuseStep 2557099 = 3835649) B3835649
theorem B6063275 : Blo 1594996 6063275 := bstep (se 1 (by rfl) ⟨4547456, by rfl⟩ : syracuseStep 6063275 = 9094913) B9094913
theorem B103564565 : Blo 1594996 103564565 := bstep (se 6 (by rfl) ⟨2427294, by rfl⟩ : syracuseStep 103564565 = 4854589) B4854589
theorem B8078615 : Blo 1594996 8078615 := bstep (se 1 (by rfl) ⟨6058961, by rfl⟩ : syracuseStep 8078615 = 12117923) B12117923
theorem B388498747 : Blo 1594996 388498747 := bstep (se 1 (by rfl) ⟨291374060, by rfl⟩ : syracuseStep 388498747 = 582748121) B582748121
theorem B1795423 : Blo 1594996 1795423 := bstep (se 1 (by rfl) ⟨1346567, by rfl⟩ : syracuseStep 1795423 = 2693135) B2693135
theorem B5383529 : Blo 1594996 5383529 := bstep (se 2 (by rfl) ⟨2018823, by rfl⟩ : syracuseStep 5383529 = 4037647) B4037647
theorem B2393519 : Blo 1594996 2393519 := bstep (se 1 (by rfl) ⟨1795139, by rfl⟩ : syracuseStep 2393519 = 3590279) B3590279
theorem B3589595 : Blo 1594996 3589595 := bstep (se 1 (by rfl) ⟨2692196, by rfl⟩ : syracuseStep 3589595 = 5384393) B5384393
theorem B10225115 : Blo 1594996 10225115 := bstep (se 1 (by rfl) ⟨7668836, by rfl⟩ : syracuseStep 10225115 = 15337673) B15337673
theorem B2393609 : Blo 1594996 2393609 := bstep (se 2 (by rfl) ⟨897603, by rfl⟩ : syracuseStep 2393609 = 1795207) B1795207
theorem B2393639 : Blo 1594996 2393639 := bstep (se 1 (by rfl) ⟨1795229, by rfl⟩ : syracuseStep 2393639 = 3590459) B3590459
theorem B2393723 : Blo 1594996 2393723 := bstep (se 1 (by rfl) ⟨1795292, by rfl⟩ : syracuseStep 2393723 = 3590585) B3590585
theorem B1795783 : Blo 1594996 1795783 := bstep (se 1 (by rfl) ⟨1346837, by rfl⟩ : syracuseStep 1795783 = 2693675) B2693675
theorem B43697879 : Blo 1594996 43697879 := bstep (se 1 (by rfl) ⟨32773409, by rfl⟩ : syracuseStep 43697879 = 65546819) B65546819
theorem B2393849 : Blo 1594996 2393849 := bstep (se 2 (by rfl) ⟨897693, by rfl⟩ : syracuseStep 2393849 = 1795387) B1795387
theorem B43657049 : Blo 1594996 43657049 := bstep (se 2 (by rfl) ⟨16371393, by rfl⟩ : syracuseStep 43657049 = 32742787) B32742787
theorem B2393951 : Blo 1594996 2393951 := bstep (se 1 (by rfl) ⟨1795463, by rfl⟩ : syracuseStep 2393951 = 3590927) B3590927
theorem B4040543 : Blo 1594996 4040543 := bstep (se 1 (by rfl) ⟨3030407, by rfl⟩ : syracuseStep 4040543 = 6060815) B6060815
theorem B2393963 : Blo 1594996 2393963 := bstep (se 1 (by rfl) ⟨1795472, by rfl⟩ : syracuseStep 2393963 = 3590945) B3590945
theorem B3590063 : Blo 1594996 3590063 := bstep (se 1 (by rfl) ⟨2692547, by rfl⟩ : syracuseStep 3590063 = 5385095) B5385095
theorem B5384123 : Blo 1594996 5384123 := bstep (se 1 (by rfl) ⟨4038092, by rfl⟩ : syracuseStep 5384123 = 8076185) B8076185
theorem B2877371 : Blo 1594996 2877371 := bstep (se 1 (by rfl) ⟨2158028, by rfl⟩ : syracuseStep 2877371 = 4316057) B4316057
theorem B7276559 : Blo 1594996 7276559 := bstep (se 1 (by rfl) ⟨5457419, by rfl⟩ : syracuseStep 7276559 = 10914839) B10914839
theorem B2394191 : Blo 1594996 2394191 := bstep (se 1 (by rfl) ⟨1795643, by rfl⟩ : syracuseStep 2394191 = 3591287) B3591287
theorem B3278971 : Blo 1594996 3278971 := bstep (se 1 (by rfl) ⟨2459228, by rfl⟩ : syracuseStep 3278971 = 4918457) B4918457
theorem B3590315 : Blo 1594996 3590315 := bstep (se 1 (by rfl) ⟨2692736, by rfl⟩ : syracuseStep 3590315 = 5385473) B5385473
theorem B2394311 : Blo 1594996 2394311 := bstep (se 1 (by rfl) ⟨1795733, by rfl⟩ : syracuseStep 2394311 = 3591467) B3591467
theorem B7383307 : Blo 1594996 7383307 := bstep (se 1 (by rfl) ⟨5537480, by rfl⟩ : syracuseStep 7383307 = 11074961) B11074961
theorem B2394473 : Blo 1594996 2394473 := bstep (se 2 (by rfl) ⟨897927, by rfl⟩ : syracuseStep 2394473 = 1795855) B1795855
theorem B2394551 : Blo 1594996 2394551 := bstep (se 1 (by rfl) ⟨1795913, by rfl⟩ : syracuseStep 2394551 = 3591827) B3591827
theorem B2394587 : Blo 1594996 2394587 := bstep (se 1 (by rfl) ⟨1795940, by rfl⟩ : syracuseStep 2394587 = 3591881) B3591881
theorem B9087623 : Blo 1594996 9087623 := bstep (se 1 (by rfl) ⟨6815717, by rfl⟩ : syracuseStep 9087623 = 13631435) B13631435
theorem B15346361 : Blo 1594996 15346361 := bstep (se 2 (by rfl) ⟨5754885, by rfl⟩ : syracuseStep 15346361 = 11509771) B11509771
theorem B7383737 : Blo 1594996 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B3590855 : Blo 1594996 3590855 := bstep (se 1 (by rfl) ⟨2693141, by rfl⟩ : syracuseStep 3590855 = 5386283) B5386283
theorem B23006045 : Blo 1594996 23006045 := bstep (se 3 (by rfl) ⟨4313633, by rfl⟩ : syracuseStep 23006045 = 8627267) B8627267
theorem B3640159 : Blo 1594996 3640159 := bstep (se 1 (by rfl) ⟨2730119, by rfl⟩ : syracuseStep 3640159 = 5460239) B5460239
theorem B8080235 : Blo 1594996 8080235 := bstep (se 1 (by rfl) ⟨6060176, by rfl⟩ : syracuseStep 8080235 = 12120353) B12120353
theorem B24578963 : Blo 1594996 24578963 := bstep (se 1 (by rfl) ⟨18434222, by rfl⟩ : syracuseStep 24578963 = 36868445) B36868445
theorem B4041647 : Blo 1594996 4041647 := bstep (se 1 (by rfl) ⟨3031235, by rfl⟩ : syracuseStep 4041647 = 6062471) B6062471
theorem B2395055 : Blo 1594996 2395055 := bstep (se 1 (by rfl) ⟨1796291, by rfl⟩ : syracuseStep 2395055 = 3592583) B3592583
theorem B2395145 : Blo 1594996 2395145 := bstep (se 2 (by rfl) ⟨898179, by rfl⟩ : syracuseStep 2395145 = 1796359) B1796359
theorem B9219091 : Blo 1594996 9219091 := bstep (se 1 (by rfl) ⟨6914318, by rfl⟩ : syracuseStep 9219091 = 13828637) B13828637
theorem B2395175 : Blo 1594996 2395175 := bstep (se 1 (by rfl) ⟨1796381, by rfl⟩ : syracuseStep 2395175 = 3592763) B3592763
theorem B31100021 : Blo 1594996 31100021 := bstep (se 5 (by rfl) ⟨1457813, by rfl⟩ : syracuseStep 31100021 = 2915627) B2915627
theorem B10226807 : Blo 1594996 10226807 := bstep (se 1 (by rfl) ⟨7670105, by rfl⟩ : syracuseStep 10226807 = 15340211) B15340211
theorem B2395259 : Blo 1594996 2395259 := bstep (se 1 (by rfl) ⟨1796444, by rfl⟩ : syracuseStep 2395259 = 3592889) B3592889
theorem B2395385 : Blo 1594996 2395385 := bstep (se 2 (by rfl) ⟨898269, by rfl⟩ : syracuseStep 2395385 = 1796539) B1796539
theorem B2395487 : Blo 1594996 2395487 := bstep (se 1 (by rfl) ⟨1796615, by rfl⟩ : syracuseStep 2395487 = 3593231) B3593231
theorem B2158007 : Blo 1594996 2158007 := bstep (se 1 (by rfl) ⟨1618505, by rfl⟩ : syracuseStep 2158007 = 3237011) B3237011
theorem B8080883 : Blo 1594996 8080883 := bstep (se 1 (by rfl) ⟨6060662, by rfl⟩ : syracuseStep 8080883 = 12121325) B12121325
theorem B2731529 : Blo 1594996 2731529 := bstep (se 2 (by rfl) ⟨1024323, by rfl⟩ : syracuseStep 2731529 = 2048647) B2048647
theorem B3591719 : Blo 1594996 3591719 := bstep (se 1 (by rfl) ⟨2693789, by rfl⟩ : syracuseStep 3591719 = 5387579) B5387579
theorem B5385851 : Blo 1594996 5385851 := bstep (se 1 (by rfl) ⟨4039388, by rfl⟩ : syracuseStep 5385851 = 8078777) B8078777
theorem B6467207 : Blo 1594996 6467207 := bstep (se 1 (by rfl) ⟨4850405, by rfl⟩ : syracuseStep 6467207 = 9700811) B9700811
theorem B6057611 : Blo 1594996 6057611 := bstep (se 1 (by rfl) ⟨4543208, by rfl⟩ : syracuseStep 6057611 = 9086417) B9086417
theorem B212766349 : Blo 1594996 212766349 := bstep (se 3 (by rfl) ⟨39893690, by rfl⟩ : syracuseStep 212766349 = 79787381) B79787381
theorem B2273017 : Blo 1594996 2273017 := bstep (se 2 (by rfl) ⟨852381, by rfl⟩ : syracuseStep 2273017 = 1704763) B1704763
theorem B5386013 : Blo 1594996 5386013 := bstep (se 3 (by rfl) ⟨1009877, by rfl⟩ : syracuseStep 5386013 = 2019755) B2019755
theorem B12119867 : Blo 1594996 12119867 := bstep (se 1 (by rfl) ⟨9089900, by rfl⟩ : syracuseStep 12119867 = 18179801) B18179801
theorem B7778143 : Blo 1594996 7778143 := bstep (se 1 (by rfl) ⟨5833607, by rfl⟩ : syracuseStep 7778143 = 11667215) B11667215
theorem B3592043 : Blo 1594996 3592043 := bstep (se 1 (by rfl) ⟨2694032, by rfl⟩ : syracuseStep 3592043 = 5388065) B5388065
theorem B5459831 : Blo 1594996 5459831 := bstep (se 1 (by rfl) ⟨4094873, by rfl⟩ : syracuseStep 5459831 = 8189747) B8189747
theorem B3592097 : Blo 1594996 3592097 := bstep (se 2 (by rfl) ⟨1347036, by rfl⟩ : syracuseStep 3592097 = 2694073) B2694073
theorem B9089081 : Blo 1594996 9089081 := bstep (se 2 (by rfl) ⟨3408405, by rfl⟩ : syracuseStep 9089081 = 6816811) B6816811
theorem B3592439 : Blo 1594996 3592439 := bstep (se 1 (by rfl) ⟨2694329, by rfl⟩ : syracuseStep 3592439 = 5388659) B5388659
theorem B5386715 : Blo 1594996 5386715 := bstep (se 1 (by rfl) ⟨4040036, by rfl⟩ : syracuseStep 5386715 = 8080073) B8080073
theorem B6558241 : Blo 1594996 6558241 := bstep (se 2 (by rfl) ⟨2459340, by rfl⟩ : syracuseStep 6558241 = 4918681) B4918681
theorem B2691623 : Blo 1594996 2691623 := bstep (se 1 (by rfl) ⟨2018717, by rfl⟩ : syracuseStep 2691623 = 4037435) B4037435
theorem B6140555 : Blo 1594996 6140555 := bstep (se 1 (by rfl) ⟨4605416, by rfl⟩ : syracuseStep 6140555 = 9210833) B9210833
theorem B6468281 : Blo 1594996 6468281 := bstep (se 2 (by rfl) ⟨2425605, by rfl⟩ : syracuseStep 6468281 = 4851211) B4851211
theorem B5755607 : Blo 1594996 5755607 := bstep (se 1 (by rfl) ⟨4316705, by rfl⟩ : syracuseStep 5755607 = 8633411) B8633411
theorem B8082179 : Blo 1594996 8082179 := bstep (se 1 (by rfl) ⟨6061634, by rfl⟩ : syracuseStep 8082179 = 12123269) B12123269
theorem B2691913 : Blo 1594996 2691913 := bstep (se 2 (by rfl) ⟨1009467, by rfl⟩ : syracuseStep 2691913 = 2018935) B2018935
theorem B3593033 : Blo 1594996 3593033 := bstep (se 2 (by rfl) ⟨1347387, by rfl⟩ : syracuseStep 3593033 = 2694775) B2694775
theorem B3642185 : Blo 1594996 3642185 := bstep (se 2 (by rfl) ⟨1365819, by rfl⟩ : syracuseStep 3642185 = 2731639) B2731639
theorem B2691947 : Blo 1594996 2691947 := bstep (se 1 (by rfl) ⟨2018960, by rfl⟩ : syracuseStep 2691947 = 4037921) B4037921
theorem B6058871 : Blo 1594996 6058871 := bstep (se 1 (by rfl) ⟨4544153, by rfl⟩ : syracuseStep 6058871 = 9088307) B9088307
theorem B6468623 : Blo 1594996 6468623 := bstep (se 1 (by rfl) ⟨4851467, by rfl⟩ : syracuseStep 6468623 = 9702935) B9702935
theorem B26235971 : Blo 1594996 26235971 := bstep (se 1 (by rfl) ⟨19676978, by rfl⟩ : syracuseStep 26235971 = 39353957) B39353957
theorem B5387417 : Blo 1594996 5387417 := bstep (se 2 (by rfl) ⟨2020281, by rfl⟩ : syracuseStep 5387417 = 4040563) B4040563
theorem B11498699 : Blo 1594996 11498699 := bstep (se 1 (by rfl) ⟨8624024, by rfl⟩ : syracuseStep 11498699 = 17248049) B17248049
theorem B2692345 : Blo 1594996 2692345 := bstep (se 2 (by rfl) ⟨1009629, by rfl⟩ : syracuseStep 2692345 = 2019259) B2019259
theorem B34493843 : Blo 1594996 34493843 := bstep (se 1 (by rfl) ⟨25870382, by rfl⟩ : syracuseStep 34493843 = 51740765) B51740765
theorem B13628837 : Blo 1594996 13628837 := bstep (se 4 (by rfl) ⟨1277703, by rfl⟩ : syracuseStep 13628837 = 2555407) B2555407
theorem B2020783 : Blo 1594996 2020783 := bstep (se 1 (by rfl) ⟨1515587, by rfl⟩ : syracuseStep 2020783 = 3031175) B3031175
theorem B2692615 : Blo 1594996 2692615 := bstep (se 1 (by rfl) ⟨2019461, by rfl⟩ : syracuseStep 2692615 = 4038923) B4038923
theorem B4544039 : Blo 1594996 4544039 := bstep (se 1 (by rfl) ⟨3408029, by rfl⟩ : syracuseStep 4544039 = 6816059) B6816059
theorem B1595003 : Blo 1594996 1595003 := bstep (se 1 (by rfl) ⟨1196252, by rfl⟩ : syracuseStep 1595003 = 2392505) B2392505
theorem B1595055 : Blo 1594996 1595055 := bstep (se 1 (by rfl) ⟨1196291, by rfl⟩ : syracuseStep 1595055 = 2392583) B2392583
theorem B1595079 : Blo 1594996 1595079 := bstep (se 1 (by rfl) ⟨1196309, by rfl⟩ : syracuseStep 1595079 = 2392619) B2392619
theorem B3028691 : Blo 1594996 3028691 := bstep (se 1 (by rfl) ⟨2271518, by rfl⟩ : syracuseStep 3028691 = 4543037) B4543037
theorem B1595099 : Blo 1594996 1595099 := bstep (se 1 (by rfl) ⟨1196324, by rfl⟩ : syracuseStep 1595099 = 2392649) B2392649
theorem B1595175 : Blo 1594996 1595175 := bstep (se 1 (by rfl) ⟨1196381, by rfl⟩ : syracuseStep 1595175 = 2392763) B2392763
theorem B8075051 : Blo 1594996 8075051 := bstep (se 1 (by rfl) ⟨6056288, by rfl⟩ : syracuseStep 8075051 = 12112577) B12112577
theorem B6059843 : Blo 1594996 6059843 := bstep (se 1 (by rfl) ⟨4544882, by rfl⟩ : syracuseStep 6059843 = 9089765) B9089765
theorem B1595215 : Blo 1594996 1595215 := bstep (se 1 (by rfl) ⟨1196411, by rfl⟩ : syracuseStep 1595215 = 2392823) B2392823
theorem B23000921 : Blo 1594996 23000921 := bstep (se 2 (by rfl) ⟨8625345, by rfl⟩ : syracuseStep 23000921 = 17250691) B17250691
theorem B1595231 : Blo 1594996 1595231 := bstep (se 1 (by rfl) ⟨1196423, by rfl⟩ : syracuseStep 1595231 = 2392847) B2392847
theorem B3028843 : Blo 1594996 3028843 := bstep (se 1 (by rfl) ⟨2271632, by rfl⟩ : syracuseStep 3028843 = 4543265) B4543265
theorem B1595259 : Blo 1594996 1595259 := bstep (se 1 (by rfl) ⟨1196444, by rfl⟩ : syracuseStep 1595259 = 2392889) B2392889
theorem B1595311 : Blo 1594996 1595311 := bstep (se 1 (by rfl) ⟨1196483, by rfl⟩ : syracuseStep 1595311 = 2392967) B2392967
theorem B2693047 : Blo 1594996 2693047 := bstep (se 1 (by rfl) ⟨2019785, by rfl⟩ : syracuseStep 2693047 = 4039571) B4039571
theorem B1595335 : Blo 1594996 1595335 := bstep (se 1 (by rfl) ⟨1196501, by rfl⟩ : syracuseStep 1595335 = 2393003) B2393003
theorem B13637585 : Blo 1594996 13637585 := bstep (se 2 (by rfl) ⟨5114094, by rfl⟩ : syracuseStep 13637585 = 10228189) B10228189
theorem B1595355 : Blo 1594996 1595355 := bstep (se 1 (by rfl) ⟨1196516, by rfl⟩ : syracuseStep 1595355 = 2393033) B2393033
theorem B1595431 : Blo 1594996 1595431 := bstep (se 1 (by rfl) ⟨1196573, by rfl⟩ : syracuseStep 1595431 = 2393147) B2393147
theorem B1595471 : Blo 1594996 1595471 := bstep (se 1 (by rfl) ⟨1196603, by rfl⟩ : syracuseStep 1595471 = 2393207) B2393207
theorem B3029071 : Blo 1594996 3029071 := bstep (se 1 (by rfl) ⟨2271803, by rfl⟩ : syracuseStep 3029071 = 4543607) B4543607
theorem B1595487 : Blo 1594996 1595487 := bstep (se 1 (by rfl) ⟨1196615, by rfl⟩ : syracuseStep 1595487 = 2393231) B2393231
theorem B15341669 : Blo 1594996 15341669 := bstep (se 4 (by rfl) ⟨1438281, by rfl⟩ : syracuseStep 15341669 = 2876563) B2876563
theorem B12114035 : Blo 1594996 12114035 := bstep (se 1 (by rfl) ⟨9085526, by rfl⟩ : syracuseStep 12114035 = 18171053) B18171053
theorem B3070075 : Blo 1594996 3070075 := bstep (se 1 (by rfl) ⟨2302556, by rfl⟩ : syracuseStep 3070075 = 4605113) B4605113
theorem B1595515 : Blo 1594996 1595515 := bstep (se 1 (by rfl) ⟨1196636, by rfl⟩ : syracuseStep 1595515 = 2393273) B2393273
theorem B2693243 : Blo 1594996 2693243 := bstep (se 1 (by rfl) ⟨2019932, by rfl⟩ : syracuseStep 2693243 = 4039865) B4039865
theorem B5748889 : Blo 1594996 5748889 := bstep (se 2 (by rfl) ⟨2155833, by rfl⟩ : syracuseStep 5748889 = 4311667) B4311667
theorem B1595567 : Blo 1594996 1595567 := bstep (se 1 (by rfl) ⟨1196675, by rfl⟩ : syracuseStep 1595567 = 2393351) B2393351
theorem B1595591 : Blo 1594996 1595591 := bstep (se 1 (by rfl) ⟨1196693, by rfl⟩ : syracuseStep 1595591 = 2393387) B2393387
theorem B1595611 : Blo 1594996 1595611 := bstep (se 1 (by rfl) ⟨1196708, by rfl⟩ : syracuseStep 1595611 = 2393417) B2393417
theorem B1595687 : Blo 1594996 1595687 := bstep (se 1 (by rfl) ⟨1196765, by rfl⟩ : syracuseStep 1595687 = 2393531) B2393531
theorem B5388605 : Blo 1594996 5388605 := bstep (se 3 (by rfl) ⟨1010363, by rfl⟩ : syracuseStep 5388605 = 2020727) B2020727
theorem B1595727 : Blo 1594996 1595727 := bstep (se 1 (by rfl) ⟨1196795, by rfl⟩ : syracuseStep 1595727 = 2393591) B2393591
theorem B8083799 : Blo 1594996 8083799 := bstep (se 1 (by rfl) ⟨6062849, by rfl⟩ : syracuseStep 8083799 = 12125699) B12125699
theorem B1595743 : Blo 1594996 1595743 := bstep (se 1 (by rfl) ⟨1196807, by rfl⟩ : syracuseStep 1595743 = 2393615) B2393615
theorem B1595771 : Blo 1594996 1595771 := bstep (se 1 (by rfl) ⟨1196828, by rfl⟩ : syracuseStep 1595771 = 2393657) B2393657
theorem B11508097 : Blo 1594996 11508097 := bstep (se 2 (by rfl) ⟨4315536, by rfl⟩ : syracuseStep 11508097 = 8631073) B8631073
theorem B30669191 : Blo 1594996 30669191 := bstep (se 1 (by rfl) ⟨23001893, by rfl⟩ : syracuseStep 30669191 = 46003787) B46003787
theorem B1595823 : Blo 1594996 1595823 := bstep (se 1 (by rfl) ⟨1196867, by rfl⟩ : syracuseStep 1595823 = 2393735) B2393735
theorem B1595847 : Blo 1594996 1595847 := bstep (se 1 (by rfl) ⟨1196885, by rfl⟩ : syracuseStep 1595847 = 2393771) B2393771
theorem B1595867 : Blo 1594996 1595867 := bstep (se 1 (by rfl) ⟨1196900, by rfl⟩ : syracuseStep 1595867 = 2393801) B2393801
theorem B2693641 : Blo 1594996 2693641 := bstep (se 2 (by rfl) ⟨1010115, by rfl⟩ : syracuseStep 2693641 = 2020231) B2020231
theorem B20453917 : Blo 1594996 20453917 := bstep (se 3 (by rfl) ⟨3835109, by rfl⟩ : syracuseStep 20453917 = 7670219) B7670219
theorem B1595943 : Blo 1594996 1595943 := bstep (se 1 (by rfl) ⟨1196957, by rfl⟩ : syracuseStep 1595943 = 2393915) B2393915
theorem B1595983 : Blo 1594996 1595983 := bstep (se 1 (by rfl) ⟨1196987, by rfl⟩ : syracuseStep 1595983 = 2393975) B2393975
theorem B1595999 : Blo 1594996 1595999 := bstep (se 1 (by rfl) ⟨1196999, by rfl⟩ : syracuseStep 1595999 = 2393999) B2393999
theorem B1596027 : Blo 1594996 1596027 := bstep (se 1 (by rfl) ⟨1197020, by rfl⟩ : syracuseStep 1596027 = 2394041) B2394041
theorem B2693803 : Blo 1594996 2693803 := bstep (se 1 (by rfl) ⟨2020352, by rfl⟩ : syracuseStep 2693803 = 4040705) B4040705
theorem B1596079 : Blo 1594996 1596079 := bstep (se 1 (by rfl) ⟨1197059, by rfl⟩ : syracuseStep 1596079 = 2394119) B2394119
theorem B1596103 : Blo 1594996 1596103 := bstep (se 1 (by rfl) ⟨1197077, by rfl⟩ : syracuseStep 1596103 = 2394155) B2394155
theorem B3832535 : Blo 1594996 3832535 := bstep (se 1 (by rfl) ⟨2874401, by rfl⟩ : syracuseStep 3832535 = 5748803) B5748803
theorem B1596123 : Blo 1594996 1596123 := bstep (se 1 (by rfl) ⟨1197092, by rfl⟩ : syracuseStep 1596123 = 2394185) B2394185
theorem B1596199 : Blo 1594996 1596199 := bstep (se 1 (by rfl) ⟨1197149, by rfl⟩ : syracuseStep 1596199 = 2394299) B2394299
theorem B1596239 : Blo 1594996 1596239 := bstep (se 1 (by rfl) ⟨1197179, by rfl⟩ : syracuseStep 1596239 = 2394359) B2394359
theorem B1596255 : Blo 1594996 1596255 := bstep (se 1 (by rfl) ⟨1197191, by rfl⟩ : syracuseStep 1596255 = 2394383) B2394383
theorem B1596283 : Blo 1594996 1596283 := bstep (se 1 (by rfl) ⟨1197212, by rfl⟩ : syracuseStep 1596283 = 2394425) B2394425
theorem B1596335 : Blo 1594996 1596335 := bstep (se 1 (by rfl) ⟨1197251, by rfl⟩ : syracuseStep 1596335 = 2394503) B2394503
theorem B1596359 : Blo 1594996 1596359 := bstep (se 1 (by rfl) ⟨1197269, by rfl⟩ : syracuseStep 1596359 = 2394539) B2394539
theorem B1596379 : Blo 1594996 1596379 := bstep (se 1 (by rfl) ⟨1197284, by rfl⟩ : syracuseStep 1596379 = 2394569) B2394569
theorem B2694107 : Blo 1594996 2694107 := bstep (se 1 (by rfl) ⟨2020580, by rfl⟩ : syracuseStep 2694107 = 4041161) B4041161
theorem B1596455 : Blo 1594996 1596455 := bstep (se 1 (by rfl) ⟨1197341, by rfl⟩ : syracuseStep 1596455 = 2394683) B2394683
theorem B1596495 : Blo 1594996 1596495 := bstep (se 1 (by rfl) ⟨1197371, by rfl⟩ : syracuseStep 1596495 = 2394743) B2394743
theorem B1596511 : Blo 1594996 1596511 := bstep (se 1 (by rfl) ⟨1197383, by rfl⟩ : syracuseStep 1596511 = 2394767) B2394767
theorem B1596539 : Blo 1594996 1596539 := bstep (se 1 (by rfl) ⟨1197404, by rfl⟩ : syracuseStep 1596539 = 2394809) B2394809
theorem B9092249 : Blo 1594996 9092249 := bstep (se 2 (by rfl) ⟨3409593, by rfl⟩ : syracuseStep 9092249 = 6819187) B6819187
theorem B5389469 : Blo 1594996 5389469 := bstep (se 3 (by rfl) ⟨1010525, by rfl⟩ : syracuseStep 5389469 = 2021051) B2021051
theorem B1596591 : Blo 1594996 1596591 := bstep (se 1 (by rfl) ⟨1197443, by rfl⟩ : syracuseStep 1596591 = 2394887) B2394887
theorem B1596615 : Blo 1594996 1596615 := bstep (se 1 (by rfl) ⟨1197461, by rfl⟩ : syracuseStep 1596615 = 2394923) B2394923
theorem B2694343 : Blo 1594996 2694343 := bstep (se 1 (by rfl) ⟨2020757, by rfl⟩ : syracuseStep 2694343 = 4041515) B4041515
theorem B1596635 : Blo 1594996 1596635 := bstep (se 1 (by rfl) ⟨1197476, by rfl⟩ : syracuseStep 1596635 = 2394953) B2394953
theorem B1596711 : Blo 1594996 1596711 := bstep (se 1 (by rfl) ⟨1197533, by rfl⟩ : syracuseStep 1596711 = 2395067) B2395067
theorem B1596751 : Blo 1594996 1596751 := bstep (se 1 (by rfl) ⟨1197563, by rfl⟩ : syracuseStep 1596751 = 2395127) B2395127
theorem B1596767 : Blo 1594996 1596767 := bstep (se 1 (by rfl) ⟨1197575, by rfl⟩ : syracuseStep 1596767 = 2395151) B2395151
theorem B2694505 : Blo 1594996 2694505 := bstep (se 2 (by rfl) ⟨1010439, by rfl⟩ : syracuseStep 2694505 = 2020879) B2020879
theorem B1596795 : Blo 1594996 1596795 := bstep (se 1 (by rfl) ⟨1197596, by rfl⟩ : syracuseStep 1596795 = 2395193) B2395193
theorem B1596847 : Blo 1594996 1596847 := bstep (se 1 (by rfl) ⟨1197635, by rfl⟩ : syracuseStep 1596847 = 2395271) B2395271
theorem B1596871 : Blo 1594996 1596871 := bstep (se 1 (by rfl) ⟨1197653, by rfl⟩ : syracuseStep 1596871 = 2395307) B2395307
theorem B6061513 : Blo 1594996 6061513 := bstep (se 2 (by rfl) ⟨2273067, by rfl⟩ : syracuseStep 6061513 = 4546135) B4546135
theorem B1596891 : Blo 1594996 1596891 := bstep (se 1 (by rfl) ⟨1197668, by rfl⟩ : syracuseStep 1596891 = 2395337) B2395337
theorem B1596967 : Blo 1594996 1596967 := bstep (se 1 (by rfl) ⟨1197725, by rfl⟩ : syracuseStep 1596967 = 2395451) B2395451
theorem B3407483 : Blo 1594996 3407483 := bstep (se 1 (by rfl) ⟨2555612, by rfl⟩ : syracuseStep 3407483 = 5111225) B5111225
theorem B19414667 : Blo 1594996 19414667 := bstep (se 1 (by rfl) ⟨14561000, by rfl⟩ : syracuseStep 19414667 = 29122001) B29122001
theorem B6061817 : Blo 1594996 6061817 := bstep (se 2 (by rfl) ⟨2273181, by rfl⟩ : syracuseStep 6061817 = 4546363) B4546363
theorem B1916767 : Blo 1594996 1916767 := bstep (se 1 (by rfl) ⟨1437575, by rfl⟩ : syracuseStep 1916767 = 2875151) B2875151
theorem B6061985 : Blo 1594996 6061985 := bstep (se 2 (by rfl) ⟨2273244, by rfl⟩ : syracuseStep 6061985 = 4546489) B4546489
theorem B3407791 : Blo 1594996 3407791 := bstep (se 1 (by rfl) ⟨2555843, by rfl⟩ : syracuseStep 3407791 = 5111687) B5111687
theorem B6061999 : Blo 1594996 6061999 := bstep (se 1 (by rfl) ⟨4546499, by rfl⟩ : syracuseStep 6061999 = 9092999) B9092999
theorem B4038761 : Blo 1594996 4038761 := bstep (se 2 (by rfl) ⟨1514535, by rfl⟩ : syracuseStep 4038761 = 3029071) B3029071
theorem B1794415 : Blo 1594996 1794415 := bstep (se 1 (by rfl) ⟨1345811, by rfl⟩ : syracuseStep 1794415 = 2691623) B2691623
theorem B2392571 : Blo 1594996 2392571 := bstep (se 1 (by rfl) ⟨1794428, by rfl⟩ : syracuseStep 2392571 = 3588857) B3588857
theorem B15344129 : Blo 1594996 15344129 := bstep (se 2 (by rfl) ⟨5754048, by rfl⟩ : syracuseStep 15344129 = 11508097) B11508097
theorem B30663197 : Blo 1594996 30663197 := bstep (se 3 (by rfl) ⟨5749349, by rfl⟩ : syracuseStep 30663197 = 11498699) B11498699
theorem B1794631 : Blo 1594996 1794631 := bstep (se 1 (by rfl) ⟨1345973, by rfl⟩ : syracuseStep 1794631 = 2691947) B2691947
theorem B4039247 : Blo 1594996 4039247 := bstep (se 1 (by rfl) ⟨3029435, by rfl⟩ : syracuseStep 4039247 = 6058871) B6058871
theorem B2392697 : Blo 1594996 2392697 := bstep (se 2 (by rfl) ⟨897261, by rfl⟩ : syracuseStep 2392697 = 1794523) B1794523
theorem B8192657 : Blo 1594996 8192657 := bstep (se 2 (by rfl) ⟨3072246, by rfl⟩ : syracuseStep 8192657 = 6144493) B6144493
theorem B2392751 : Blo 1594996 2392751 := bstep (se 1 (by rfl) ⟨1794563, by rfl⟩ : syracuseStep 2392751 = 3589127) B3589127
theorem B27271889 : Blo 1594996 27271889 := bstep (se 2 (by rfl) ⟨10226958, by rfl⟩ : syracuseStep 27271889 = 20453917) B20453917
theorem B17490647 : Blo 1594996 17490647 := bstep (se 1 (by rfl) ⟨13117985, by rfl⟩ : syracuseStep 17490647 = 26235971) B26235971
theorem B2392799 : Blo 1594996 2392799 := bstep (se 1 (by rfl) ⟨1794599, by rfl⟩ : syracuseStep 2392799 = 3589199) B3589199
theorem B69043043 : Blo 1594996 69043043 := bstep (se 1 (by rfl) ⟨51782282, by rfl⟩ : syracuseStep 69043043 = 103564565) B103564565
theorem B3589019 : Blo 1594996 3589019 := bstep (se 1 (by rfl) ⟨2691764, by rfl⟩ : syracuseStep 3589019 = 5383529) B5383529
theorem B22995895 : Blo 1594996 22995895 := bstep (se 1 (by rfl) ⟨17246921, by rfl⟩ : syracuseStep 22995895 = 34493843) B34493843
theorem B9085891 : Blo 1594996 9085891 := bstep (se 1 (by rfl) ⟨6814418, by rfl⟩ : syracuseStep 9085891 = 13628837) B13628837
theorem B2393063 : Blo 1594996 2393063 := bstep (se 1 (by rfl) ⟨1794797, by rfl⟩ : syracuseStep 2393063 = 3589595) B3589595
theorem B6816743 : Blo 1594996 6816743 := bstep (se 1 (by rfl) ⟨5112557, by rfl⟩ : syracuseStep 6816743 = 10225115) B10225115
theorem B3589217 : Blo 1594996 3589217 := bstep (se 2 (by rfl) ⟨1345956, by rfl⟩ : syracuseStep 3589217 = 2691913) B2691913
theorem B29131919 : Blo 1594996 29131919 := bstep (se 1 (by rfl) ⟨21848939, by rfl⟩ : syracuseStep 29131919 = 43697879) B43697879
theorem B5383367 : Blo 1594996 5383367 := bstep (se 1 (by rfl) ⟨4037525, by rfl⟩ : syracuseStep 5383367 = 8075051) B8075051
theorem B4039895 : Blo 1594996 4039895 := bstep (se 1 (by rfl) ⟨3029921, by rfl⟩ : syracuseStep 4039895 = 6059843) B6059843
theorem B2393321 : Blo 1594996 2393321 := bstep (se 2 (by rfl) ⟨897495, by rfl⟩ : syracuseStep 2393321 = 1794991) B1794991
theorem B2393375 : Blo 1594996 2393375 := bstep (se 1 (by rfl) ⟨1795031, by rfl⟩ : syracuseStep 2393375 = 3590063) B3590063
theorem B3589415 : Blo 1594996 3589415 := bstep (se 1 (by rfl) ⟨2692061, by rfl⟩ : syracuseStep 3589415 = 5384123) B5384123
theorem B1918247 : Blo 1594996 1918247 := bstep (se 1 (by rfl) ⟨1438685, by rfl⟩ : syracuseStep 1918247 = 2877371) B2877371
theorem B7284077 : Blo 1594996 7284077 := bstep (se 3 (by rfl) ⟨1365764, by rfl⟩ : syracuseStep 7284077 = 2731529) B2731529
theorem B1795495 : Blo 1594996 1795495 := bstep (se 1 (by rfl) ⟨1346621, by rfl⟩ : syracuseStep 1795495 = 2693243) B2693243
theorem B12117437 : Blo 1594996 12117437 := bstep (se 3 (by rfl) ⟨2272019, by rfl⟩ : syracuseStep 12117437 = 4544039) B4544039
theorem B2393543 : Blo 1594996 2393543 := bstep (se 1 (by rfl) ⟨1795157, by rfl⟩ : syracuseStep 2393543 = 3590315) B3590315
theorem B3409465 : Blo 1594996 3409465 := bstep (se 2 (by rfl) ⟨1278549, by rfl⟩ : syracuseStep 3409465 = 2557099) B2557099
theorem B3589793 : Blo 1594996 3589793 := bstep (se 2 (by rfl) ⟨1346172, by rfl⟩ : syracuseStep 3589793 = 2692345) B2692345
theorem B17245885 : Blo 1594996 17245885 := bstep (se 3 (by rfl) ⟨3233603, by rfl⟩ : syracuseStep 17245885 = 6467207) B6467207
theorem B517998329 : Blo 1594996 517998329 := bstep (se 2 (by rfl) ⟨194249373, by rfl⟩ : syracuseStep 517998329 = 388498747) B388498747
theorem B2393897 : Blo 1594996 2393897 := bstep (se 2 (by rfl) ⟨897711, by rfl⟩ : syracuseStep 2393897 = 1795423) B1795423
theorem B2393903 : Blo 1594996 2393903 := bstep (se 1 (by rfl) ⟨1795427, by rfl⟩ : syracuseStep 2393903 = 3590855) B3590855
theorem B15337363 : Blo 1594996 15337363 := bstep (se 1 (by rfl) ⟨11503022, by rfl⟩ : syracuseStep 15337363 = 23006045) B23006045
theorem B16385975 : Blo 1594996 16385975 := bstep (se 1 (by rfl) ⟨12289481, by rfl⟩ : syracuseStep 16385975 = 24578963) B24578963
theorem B1796071 : Blo 1594996 1796071 := bstep (se 1 (by rfl) ⟨1347053, by rfl⟩ : syracuseStep 1796071 = 2694107) B2694107
theorem B7669741 : Blo 1594996 7669741 := bstep (se 3 (by rfl) ⟨1438076, by rfl⟩ : syracuseStep 7669741 = 2876153) B2876153
theorem B3590153 : Blo 1594996 3590153 := bstep (se 2 (by rfl) ⟨1346307, by rfl⟩ : syracuseStep 3590153 = 2692615) B2692615
theorem B6817871 : Blo 1594996 6817871 := bstep (se 1 (by rfl) ⟨5113403, by rfl⟩ : syracuseStep 6817871 = 10226807) B10226807
theorem B2394377 : Blo 1594996 2394377 := bstep (se 2 (by rfl) ⟨897891, by rfl⟩ : syracuseStep 2394377 = 1795783) B1795783
theorem B2394479 : Blo 1594996 2394479 := bstep (se 1 (by rfl) ⟨1795859, by rfl⟩ : syracuseStep 2394479 = 3591719) B3591719
theorem B2271655 : Blo 1594996 2271655 := bstep (se 1 (by rfl) ⟨1703741, by rfl⟩ : syracuseStep 2271655 = 3407483) B3407483
theorem B3590567 : Blo 1594996 3590567 := bstep (se 1 (by rfl) ⟨2692925, by rfl⟩ : syracuseStep 3590567 = 5385851) B5385851
theorem B4041211 : Blo 1594996 4041211 := bstep (se 1 (by rfl) ⟨3030908, by rfl⟩ : syracuseStep 4041211 = 6061817) B6061817
theorem B3590675 : Blo 1594996 3590675 := bstep (se 1 (by rfl) ⟨2693006, by rfl⟩ : syracuseStep 3590675 = 5386013) B5386013
theorem B8079911 : Blo 1594996 8079911 := bstep (se 1 (by rfl) ⟨6059933, by rfl⟩ : syracuseStep 8079911 = 12119867) B12119867
theorem B2394695 : Blo 1594996 2394695 := bstep (se 1 (by rfl) ⟨1796021, by rfl⟩ : syracuseStep 2394695 = 3592043) B3592043
theorem B3590729 : Blo 1594996 3590729 := bstep (se 2 (by rfl) ⟨1346523, by rfl⟩ : syracuseStep 3590729 = 2693047) B2693047
theorem B3639887 : Blo 1594996 3639887 := bstep (se 1 (by rfl) ⟨2729915, by rfl⟩ : syracuseStep 3639887 = 5459831) B5459831
theorem B2394731 : Blo 1594996 2394731 := bstep (se 1 (by rfl) ⟨1796048, by rfl⟩ : syracuseStep 2394731 = 3592097) B3592097
theorem B4041323 : Blo 1594996 4041323 := bstep (se 1 (by rfl) ⟨3030992, by rfl⟩ : syracuseStep 4041323 = 6061985) B6061985
theorem B5384879 : Blo 1594996 5384879 := bstep (se 1 (by rfl) ⟨4038659, by rfl⟩ : syracuseStep 5384879 = 8077319) B8077319
theorem B13626103 : Blo 1594996 13626103 := bstep (se 1 (by rfl) ⟨10219577, by rfl⟩ : syracuseStep 13626103 = 20439155) B20439155
theorem B2394959 : Blo 1594996 2394959 := bstep (se 1 (by rfl) ⟨1796219, by rfl⟩ : syracuseStep 2394959 = 3592439) B3592439
theorem B3591143 : Blo 1594996 3591143 := bstep (se 1 (by rfl) ⟨2693357, by rfl⟩ : syracuseStep 3591143 = 5386715) B5386715
theorem B5385203 : Blo 1594996 5385203 := bstep (se 1 (by rfl) ⟨4038902, by rfl⟩ : syracuseStep 5385203 = 8077805) B8077805
theorem B7777361 : Blo 1594996 7777361 := bstep (se 2 (by rfl) ⟨2916510, by rfl⟩ : syracuseStep 7777361 = 5833021) B5833021
theorem B4312187 : Blo 1594996 4312187 := bstep (se 1 (by rfl) ⟨3234140, by rfl⟩ : syracuseStep 4312187 = 6468281) B6468281
theorem B3837071 : Blo 1594996 3837071 := bstep (se 1 (by rfl) ⟨2877803, by rfl⟩ : syracuseStep 3837071 = 5755607) B5755607
theorem B2395355 : Blo 1594996 2395355 := bstep (se 1 (by rfl) ⟨1796516, by rfl⟩ : syracuseStep 2395355 = 3593033) B3593033
theorem B2428123 : Blo 1594996 2428123 := bstep (se 1 (by rfl) ⟨1821092, by rfl⟩ : syracuseStep 2428123 = 3642185) B3642185
theorem B4041971 : Blo 1594996 4041971 := bstep (se 1 (by rfl) ⟨3031478, by rfl⟩ : syracuseStep 4041971 = 6062957) B6062957
theorem B4312415 : Blo 1594996 4312415 := bstep (se 1 (by rfl) ⟨3234311, by rfl⟩ : syracuseStep 4312415 = 6468623) B6468623
theorem B3591521 : Blo 1594996 3591521 := bstep (se 2 (by rfl) ⟨1346820, by rfl⟩ : syracuseStep 3591521 = 2693641) B2693641
theorem B8744321 : Blo 1594996 8744321 := bstep (se 2 (by rfl) ⟨3279120, by rfl⟩ : syracuseStep 8744321 = 6558241) B6558241
theorem B3591611 : Blo 1594996 3591611 := bstep (se 1 (by rfl) ⟨2693708, by rfl⟩ : syracuseStep 3591611 = 5387417) B5387417
theorem B3501511 : Blo 1594996 3501511 := bstep (se 1 (by rfl) ⟨2626133, by rfl⟩ : syracuseStep 3501511 = 5252267) B5252267
theorem B4042183 : Blo 1594996 4042183 := bstep (se 1 (by rfl) ⟨3031637, by rfl⟩ : syracuseStep 4042183 = 6063275) B6063275
theorem B5385743 : Blo 1594996 5385743 := bstep (se 1 (by rfl) ⟨4039307, by rfl⟩ : syracuseStep 5385743 = 8078615) B8078615
theorem B3591737 : Blo 1594996 3591737 := bstep (se 2 (by rfl) ⟨1346901, by rfl⟩ : syracuseStep 3591737 = 2693803) B2693803
theorem B5754685 : Blo 1594996 5754685 := bstep (se 3 (by rfl) ⟨1079003, by rfl⟩ : syracuseStep 5754685 = 2158007) B2158007
theorem B8630297 : Blo 1594996 8630297 := bstep (se 2 (by rfl) ⟨3236361, by rfl⟩ : syracuseStep 8630297 = 6472723) B6472723
theorem B12292121 : Blo 1594996 12292121 := bstep (se 2 (by rfl) ⟨4609545, by rfl⟩ : syracuseStep 12292121 = 9219091) B9219091
theorem B10227779 : Blo 1594996 10227779 := bstep (se 1 (by rfl) ⟨7670834, by rfl⟩ : syracuseStep 10227779 = 15341669) B15341669
theorem B3592403 : Blo 1594996 3592403 := bstep (se 1 (by rfl) ⟨2694302, by rfl⟩ : syracuseStep 3592403 = 5388605) B5388605
theorem B3592457 : Blo 1594996 3592457 := bstep (se 2 (by rfl) ⟨1347171, by rfl⟩ : syracuseStep 3592457 = 2694343) B2694343
theorem B6058415 : Blo 1594996 6058415 := bstep (se 1 (by rfl) ⟨4543811, by rfl⟩ : syracuseStep 6058415 = 9087623) B9087623
theorem B3592673 : Blo 1594996 3592673 := bstep (se 2 (by rfl) ⟨1347252, by rfl⟩ : syracuseStep 3592673 = 2694505) B2694505
theorem B10220093 : Blo 1594996 10220093 := bstep (se 3 (by rfl) ⟨1916267, by rfl⟩ : syracuseStep 10220093 = 3832535) B3832535
theorem B5386823 : Blo 1594996 5386823 := bstep (se 1 (by rfl) ⟨4040117, by rfl⟩ : syracuseStep 5386823 = 8080235) B8080235
theorem B8082017 : Blo 1594996 8082017 := bstep (se 2 (by rfl) ⟨3030756, by rfl⟩ : syracuseStep 8082017 = 6061513) B6061513
theorem B3592979 : Blo 1594996 3592979 := bstep (se 1 (by rfl) ⟨2694734, by rfl⟩ : syracuseStep 3592979 = 5389469) B5389469
theorem B5387255 : Blo 1594996 5387255 := bstep (se 1 (by rfl) ⟨4040441, by rfl⟩ : syracuseStep 5387255 = 8080883) B8080883
theorem B14202013 : Blo 1594996 14202013 := bstep (se 3 (by rfl) ⟨2662877, by rfl⟩ : syracuseStep 14202013 = 5325755) B5325755
theorem B4543721 : Blo 1594996 4543721 := bstep (se 2 (by rfl) ⟨1703895, by rfl⟩ : syracuseStep 4543721 = 3407791) B3407791
theorem B8082665 : Blo 1594996 8082665 := bstep (se 2 (by rfl) ⟨3030999, by rfl⟩ : syracuseStep 8082665 = 6061999) B6061999
theorem B17257823 : Blo 1594996 17257823 := bstep (se 1 (by rfl) ⟨12943367, by rfl⟩ : syracuseStep 17257823 = 25886735) B25886735
theorem B6059387 : Blo 1594996 6059387 := bstep (se 1 (by rfl) ⟨4544540, by rfl⟩ : syracuseStep 6059387 = 9089081) B9089081
theorem B4314491 : Blo 1594996 4314491 := bstep (se 1 (by rfl) ⟨3235868, by rfl⟩ : syracuseStep 4314491 = 6471737) B6471737
theorem B19404157 : Blo 1594996 19404157 := bstep (se 3 (by rfl) ⟨3638279, by rfl⟩ : syracuseStep 19404157 = 7276559) B7276559
theorem B8082827 : Blo 1594996 8082827 := bstep (se 1 (by rfl) ⟨6062120, by rfl⟩ : syracuseStep 8082827 = 12124241) B12124241
theorem B4093433 : Blo 1594996 4093433 := bstep (se 2 (by rfl) ⟨1535037, by rfl⟩ : syracuseStep 4093433 = 3070075) B3070075
theorem B4371961 : Blo 1594996 4371961 := bstep (se 2 (by rfl) ⟨1639485, by rfl⟩ : syracuseStep 4371961 = 3278971) B3278971
theorem B7665185 : Blo 1594996 7665185 := bstep (se 2 (by rfl) ⟨2874444, by rfl⟩ : syracuseStep 7665185 = 5748889) B5748889
theorem B2692703 : Blo 1594996 2692703 := bstep (se 1 (by rfl) ⟨2019527, by rfl⟩ : syracuseStep 2692703 = 4039055) B4039055
theorem B9844409 : Blo 1594996 9844409 := bstep (se 2 (by rfl) ⟨3691653, by rfl⟩ : syracuseStep 9844409 = 7383307) B7383307
theorem B1595103 : Blo 1594996 1595103 := bstep (se 1 (by rfl) ⟨1196327, by rfl⟩ : syracuseStep 1595103 = 2392655) B2392655
theorem B4093703 : Blo 1594996 4093703 := bstep (se 1 (by rfl) ⟨3070277, by rfl⟩ : syracuseStep 4093703 = 6140555) B6140555
theorem B1595183 : Blo 1594996 1595183 := bstep (se 1 (by rfl) ⟨1196387, by rfl⟩ : syracuseStep 1595183 = 2392775) B2392775
theorem B2692919 : Blo 1594996 2692919 := bstep (se 1 (by rfl) ⟨2019689, by rfl⟩ : syracuseStep 2692919 = 4039379) B4039379
theorem B5388119 : Blo 1594996 5388119 := bstep (se 1 (by rfl) ⟨4041089, by rfl⟩ : syracuseStep 5388119 = 8082179) B8082179
theorem B1595291 : Blo 1594996 1595291 := bstep (se 1 (by rfl) ⟨1196468, by rfl⟩ : syracuseStep 1595291 = 2392937) B2392937
theorem B1595343 : Blo 1594996 1595343 := bstep (se 1 (by rfl) ⟨1196507, by rfl⟩ : syracuseStep 1595343 = 2393015) B2393015
theorem B1595367 : Blo 1594996 1595367 := bstep (se 1 (by rfl) ⟨1196525, by rfl⟩ : syracuseStep 1595367 = 2393051) B2393051
theorem B1595679 : Blo 1594996 1595679 := bstep (se 1 (by rfl) ⟨1196759, by rfl⟩ : syracuseStep 1595679 = 2393519) B2393519
theorem B1595739 : Blo 1594996 1595739 := bstep (se 1 (by rfl) ⟨1196804, by rfl⟩ : syracuseStep 1595739 = 2393609) B2393609
theorem B1595759 : Blo 1594996 1595759 := bstep (se 1 (by rfl) ⟨1196819, by rfl⟩ : syracuseStep 1595759 = 2393639) B2393639
theorem B1595815 : Blo 1594996 1595815 := bstep (se 1 (by rfl) ⟨1196861, by rfl⟩ : syracuseStep 1595815 = 2393723) B2393723
theorem B1595899 : Blo 1594996 1595899 := bstep (se 1 (by rfl) ⟨1196924, by rfl⟩ : syracuseStep 1595899 = 2393849) B2393849
theorem B29104699 : Blo 1594996 29104699 := bstep (se 1 (by rfl) ⟨21828524, by rfl⟩ : syracuseStep 29104699 = 43657049) B43657049
theorem B15333947 : Blo 1594996 15333947 := bstep (se 1 (by rfl) ⟨11500460, by rfl⟩ : syracuseStep 15333947 = 23000921) B23000921
theorem B1595967 : Blo 1594996 1595967 := bstep (se 1 (by rfl) ⟨1196975, by rfl⟩ : syracuseStep 1595967 = 2393951) B2393951
theorem B2693695 : Blo 1594996 2693695 := bstep (se 1 (by rfl) ⟨2020271, by rfl⟩ : syracuseStep 2693695 = 4040543) B4040543
theorem B1595975 : Blo 1594996 1595975 := bstep (se 1 (by rfl) ⟨1196981, by rfl⟩ : syracuseStep 1595975 = 2393963) B2393963
theorem B9091723 : Blo 1594996 9091723 := bstep (se 1 (by rfl) ⟨6818792, by rfl⟩ : syracuseStep 9091723 = 13637585) B13637585
theorem B1596127 : Blo 1594996 1596127 := bstep (se 1 (by rfl) ⟨1197095, by rfl⟩ : syracuseStep 1596127 = 2394191) B2394191
theorem B8076023 : Blo 1594996 8076023 := bstep (se 1 (by rfl) ⟨6057017, by rfl⟩ : syracuseStep 8076023 = 12114035) B12114035
theorem B1596207 : Blo 1594996 1596207 := bstep (se 1 (by rfl) ⟨1197155, by rfl⟩ : syracuseStep 1596207 = 2394311) B2394311
theorem B5389199 : Blo 1594996 5389199 := bstep (se 1 (by rfl) ⟨4041899, by rfl⟩ : syracuseStep 5389199 = 8083799) B8083799
theorem B1596315 : Blo 1594996 1596315 := bstep (se 1 (by rfl) ⟨1197236, by rfl⟩ : syracuseStep 1596315 = 2394473) B2394473
theorem B20446127 : Blo 1594996 20446127 := bstep (se 1 (by rfl) ⟨15334595, by rfl⟩ : syracuseStep 20446127 = 30669191) B30669191
theorem B1596367 : Blo 1594996 1596367 := bstep (se 1 (by rfl) ⟨1197275, by rfl⟩ : syracuseStep 1596367 = 2394551) B2394551
theorem B1596391 : Blo 1594996 1596391 := bstep (se 1 (by rfl) ⟨1197293, by rfl⟩ : syracuseStep 1596391 = 2394587) B2394587
theorem B10230907 : Blo 1594996 10230907 := bstep (se 1 (by rfl) ⟨7673180, by rfl⟩ : syracuseStep 10230907 = 15346361) B15346361
theorem B4922491 : Blo 1594996 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B10222757 : Blo 1594996 10222757 := bstep (se 4 (by rfl) ⟨958383, by rfl⟩ : syracuseStep 10222757 = 1916767) B1916767
theorem B19414181 : Blo 1594996 19414181 := bstep (se 4 (by rfl) ⟨1820079, by rfl⟩ : syracuseStep 19414181 = 3640159) B3640159
theorem B8076509 : Blo 1594996 8076509 := bstep (se 3 (by rfl) ⟨1514345, by rfl⟩ : syracuseStep 8076509 = 3028691) B3028691
theorem B2694377 : Blo 1594996 2694377 := bstep (se 2 (by rfl) ⟨1010391, by rfl⟩ : syracuseStep 2694377 = 2020783) B2020783
theorem B2694431 : Blo 1594996 2694431 := bstep (se 1 (by rfl) ⟨2020823, by rfl⟩ : syracuseStep 2694431 = 4041647) B4041647
theorem B1596703 : Blo 1594996 1596703 := bstep (se 1 (by rfl) ⟨1197527, by rfl⟩ : syracuseStep 1596703 = 2395055) B2395055
theorem B1596763 : Blo 1594996 1596763 := bstep (se 1 (by rfl) ⟨1197572, by rfl⟩ : syracuseStep 1596763 = 2395145) B2395145
theorem B1596783 : Blo 1594996 1596783 := bstep (se 1 (by rfl) ⟨1197587, by rfl⟩ : syracuseStep 1596783 = 2395175) B2395175
theorem B20733347 : Blo 1594996 20733347 := bstep (se 1 (by rfl) ⟨15550010, by rfl⟩ : syracuseStep 20733347 = 31100021) B31100021
theorem B1596839 : Blo 1594996 1596839 := bstep (se 1 (by rfl) ⟨1197629, by rfl⟩ : syracuseStep 1596839 = 2395259) B2395259
theorem B6061499 : Blo 1594996 6061499 := bstep (se 1 (by rfl) ⟨4546124, by rfl⟩ : syracuseStep 6061499 = 9092249) B9092249
theorem B1596923 : Blo 1594996 1596923 := bstep (se 1 (by rfl) ⟨1197692, by rfl⟩ : syracuseStep 1596923 = 2395385) B2395385
theorem B283688465 : Blo 1594996 283688465 := bstep (se 2 (by rfl) ⟨106383174, by rfl⟩ : syracuseStep 283688465 = 212766349) B212766349
theorem B1596991 : Blo 1594996 1596991 := bstep (se 1 (by rfl) ⟨1197743, by rfl⟩ : syracuseStep 1596991 = 2395487) B2395487
theorem B3030689 : Blo 1594996 3030689 := bstep (se 2 (by rfl) ⟨1136508, by rfl⟩ : syracuseStep 3030689 = 2273017) B2273017
theorem B4038407 : Blo 1594996 4038407 := bstep (se 1 (by rfl) ⟨3028805, by rfl⟩ : syracuseStep 4038407 = 6057611) B6057611
theorem B12943111 : Blo 1594996 12943111 := bstep (se 1 (by rfl) ⟨9707333, by rfl⟩ : syracuseStep 12943111 = 19414667) B19414667
theorem B10370857 : Blo 1594996 10370857 := bstep (se 2 (by rfl) ⟨3889071, by rfl⟩ : syracuseStep 10370857 = 7778143) B7778143
theorem B4038457 : Blo 1594996 4038457 := bstep (se 2 (by rfl) ⟨1514421, by rfl⟩ : syracuseStep 4038457 = 3028843) B3028843
theorem B4038943 : Blo 1594996 4038943 := bstep (se 1 (by rfl) ⟨3029207, by rfl⟩ : syracuseStep 4038943 = 6058415) B6058415
theorem B10232189 : Blo 1594996 10232189 := bstep (se 3 (by rfl) ⟨1918535, by rfl⟩ : syracuseStep 10232189 = 3837071) B3837071
theorem B2392553 : Blo 1594996 2392553 := bstep (se 2 (by rfl) ⟨897207, by rfl⟩ : syracuseStep 2392553 = 1794415) B1794415
theorem B2392679 : Blo 1594996 2392679 := bstep (se 1 (by rfl) ⟨1794509, by rfl⟩ : syracuseStep 2392679 = 3589019) B3589019
theorem B2392811 : Blo 1594996 2392811 := bstep (se 1 (by rfl) ⟨1794608, by rfl⟩ : syracuseStep 2392811 = 3589217) B3589217
theorem B38806265 : Blo 1594996 38806265 := bstep (se 2 (by rfl) ⟨14552349, by rfl⟩ : syracuseStep 38806265 = 29104699) B29104699
theorem B2392841 : Blo 1594996 2392841 := bstep (se 2 (by rfl) ⟨897315, by rfl⟩ : syracuseStep 2392841 = 1794631) B1794631
theorem B3588911 : Blo 1594996 3588911 := bstep (se 1 (by rfl) ⟨2691683, by rfl⟩ : syracuseStep 3588911 = 5383367) B5383367
theorem B2392943 : Blo 1594996 2392943 := bstep (se 1 (by rfl) ⟨1794707, by rfl⟩ : syracuseStep 2392943 = 3589415) B3589415
theorem B4039591 : Blo 1594996 4039591 := bstep (se 1 (by rfl) ⟨3029693, by rfl⟩ : syracuseStep 4039591 = 6059387) B6059387
theorem B2876327 : Blo 1594996 2876327 := bstep (se 1 (by rfl) ⟨2157245, by rfl⟩ : syracuseStep 2876327 = 4314491) B4314491
theorem B8078291 : Blo 1594996 8078291 := bstep (se 1 (by rfl) ⟨6058718, by rfl⟩ : syracuseStep 8078291 = 12117437) B12117437
theorem B2728955 : Blo 1594996 2728955 := bstep (se 1 (by rfl) ⟨2046716, by rfl⟩ : syracuseStep 2728955 = 4093433) B4093433
theorem B1795135 : Blo 1594996 1795135 := bstep (se 1 (by rfl) ⟨1346351, by rfl⟩ : syracuseStep 1795135 = 2692703) B2692703
theorem B55288925 : Blo 1594996 55288925 := bstep (se 3 (by rfl) ⟨10366673, by rfl⟩ : syracuseStep 55288925 = 20733347) B20733347
theorem B2393195 : Blo 1594996 2393195 := bstep (se 1 (by rfl) ⟨1794896, by rfl⟩ : syracuseStep 2393195 = 3589793) B3589793
theorem B6562939 : Blo 1594996 6562939 := bstep (se 1 (by rfl) ⟨4922204, by rfl⟩ : syracuseStep 6562939 = 9844409) B9844409
theorem B2729135 : Blo 1594996 2729135 := bstep (se 1 (by rfl) ⟨2046851, by rfl⟩ : syracuseStep 2729135 = 4093703) B4093703
theorem B1795279 : Blo 1594996 1795279 := bstep (se 1 (by rfl) ⟨1346459, by rfl⟩ : syracuseStep 1795279 = 2692919) B2692919
theorem B2393435 : Blo 1594996 2393435 := bstep (se 1 (by rfl) ⟨1795076, by rfl⟩ : syracuseStep 2393435 = 3590153) B3590153
theorem B13641209 : Blo 1594996 13641209 := bstep (se 2 (by rfl) ⟨5115453, by rfl⟩ : syracuseStep 13641209 = 10230907) B10230907
theorem B6563321 : Blo 1594996 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B2393711 : Blo 1594996 2393711 := bstep (se 1 (by rfl) ⟨1795283, by rfl⟩ : syracuseStep 2393711 = 3590567) B3590567
theorem B3237497 : Blo 1594996 3237497 := bstep (se 2 (by rfl) ⟨1214061, by rfl⟩ : syracuseStep 3237497 = 2428123) B2428123
theorem B2393783 : Blo 1594996 2393783 := bstep (se 1 (by rfl) ⟨1795337, by rfl⟩ : syracuseStep 2393783 = 3590675) B3590675
theorem B2393819 : Blo 1594996 2393819 := bstep (se 1 (by rfl) ⟨1795364, by rfl⟩ : syracuseStep 2393819 = 3590729) B3590729
theorem B2426591 : Blo 1594996 2426591 := bstep (se 1 (by rfl) ⟨1819943, by rfl⟩ : syracuseStep 2426591 = 3639887) B3639887
theorem B3589919 : Blo 1594996 3589919 := bstep (se 1 (by rfl) ⟨2692439, by rfl⟩ : syracuseStep 3589919 = 5384879) B5384879
theorem B5384015 : Blo 1594996 5384015 := bstep (se 1 (by rfl) ⟨4038011, by rfl⟩ : syracuseStep 5384015 = 8076023) B8076023
theorem B25872209 : Blo 1594996 25872209 := bstep (se 2 (by rfl) ⟨9702078, by rfl⟩ : syracuseStep 25872209 = 19404157) B19404157
theorem B2393993 : Blo 1594996 2393993 := bstep (se 2 (by rfl) ⟨897747, by rfl⟩ : syracuseStep 2393993 = 1795495) B1795495
theorem B2394095 : Blo 1594996 2394095 := bstep (se 1 (by rfl) ⟨1795571, by rfl⟩ : syracuseStep 2394095 = 3591143) B3591143
theorem B3590135 : Blo 1594996 3590135 := bstep (se 1 (by rfl) ⟨2692601, by rfl⟩ : syracuseStep 3590135 = 5385203) B5385203
theorem B5384339 : Blo 1594996 5384339 := bstep (se 1 (by rfl) ⟨4038254, by rfl⟩ : syracuseStep 5384339 = 8076509) B8076509
theorem B1796251 : Blo 1594996 1796251 := bstep (se 1 (by rfl) ⟨1347188, by rfl⟩ : syracuseStep 1796251 = 2694377) B2694377
theorem B1796287 : Blo 1594996 1796287 := bstep (se 1 (by rfl) ⟨1347215, by rfl⟩ : syracuseStep 1796287 = 2694431) B2694431
theorem B2394347 : Blo 1594996 2394347 := bstep (se 1 (by rfl) ⟨1795760, by rfl⟩ : syracuseStep 2394347 = 3591521) B3591521
theorem B2394407 : Blo 1594996 2394407 := bstep (se 1 (by rfl) ⟨1795805, by rfl⟩ : syracuseStep 2394407 = 3591611) B3591611
theorem B4040999 : Blo 1594996 4040999 := bstep (se 1 (by rfl) ⟨3030749, by rfl⟩ : syracuseStep 4040999 = 6061499) B6061499
theorem B3590495 : Blo 1594996 3590495 := bstep (se 1 (by rfl) ⟨2692871, by rfl⟩ : syracuseStep 3590495 = 5385743) B5385743
theorem B2394491 : Blo 1594996 2394491 := bstep (se 1 (by rfl) ⟨1795868, by rfl⟩ : syracuseStep 2394491 = 3591737) B3591737
theorem B5384609 : Blo 1594996 5384609 := bstep (se 2 (by rfl) ⟨2019228, by rfl⟩ : syracuseStep 5384609 = 4038457) B4038457
theorem B20449817 : Blo 1594996 20449817 := bstep (se 2 (by rfl) ⟨7668681, by rfl⟩ : syracuseStep 20449817 = 15337363) B15337363
theorem B2394761 : Blo 1594996 2394761 := bstep (se 2 (by rfl) ⟨898035, by rfl⟩ : syracuseStep 2394761 = 1796071) B1796071
theorem B10226321 : Blo 1594996 10226321 := bstep (se 2 (by rfl) ⟨3834870, by rfl⟩ : syracuseStep 10226321 = 7669741) B7669741
theorem B5753531 : Blo 1594996 5753531 := bstep (se 1 (by rfl) ⟨4315148, by rfl⟩ : syracuseStep 5753531 = 8630297) B8630297
theorem B6818519 : Blo 1594996 6818519 := bstep (se 1 (by rfl) ⟨5113889, by rfl⟩ : syracuseStep 6818519 = 10227779) B10227779
theorem B32778989 : Blo 1594996 32778989 := bstep (se 3 (by rfl) ⟨6146060, by rfl⟩ : syracuseStep 32778989 = 12292121) B12292121
theorem B2394935 : Blo 1594996 2394935 := bstep (se 1 (by rfl) ⟨1796201, by rfl⟩ : syracuseStep 2394935 = 3592403) B3592403
theorem B2394971 : Blo 1594996 2394971 := bstep (se 1 (by rfl) ⟨1796228, by rfl⟩ : syracuseStep 2394971 = 3592457) B3592457
theorem B2395115 : Blo 1594996 2395115 := bstep (se 1 (by rfl) ⟨1796336, by rfl⟩ : syracuseStep 2395115 = 3592673) B3592673
theorem B20442131 : Blo 1594996 20442131 := bstep (se 1 (by rfl) ⟨15331598, by rfl⟩ : syracuseStep 20442131 = 30663197) B30663197
theorem B3591215 : Blo 1594996 3591215 := bstep (se 1 (by rfl) ⟨2693411, by rfl⟩ : syracuseStep 3591215 = 5386823) B5386823
theorem B18181259 : Blo 1594996 18181259 := bstep (se 1 (by rfl) ⟨13635944, by rfl⟩ : syracuseStep 18181259 = 27271889) B27271889
theorem B11660431 : Blo 1594996 11660431 := bstep (se 1 (by rfl) ⟨8745323, by rfl⟩ : syracuseStep 11660431 = 17490647) B17490647
theorem B2395319 : Blo 1594996 2395319 := bstep (se 1 (by rfl) ⟨1796489, by rfl⟩ : syracuseStep 2395319 = 3592979) B3592979
theorem B3591503 : Blo 1594996 3591503 := bstep (se 1 (by rfl) ⟨2693627, by rfl⟩ : syracuseStep 3591503 = 5387255) B5387255
theorem B3591593 : Blo 1594996 3591593 := bstep (se 2 (by rfl) ⟨1346847, by rfl⟩ : syracuseStep 3591593 = 2693695) B2693695
theorem B5115325 : Blo 1594996 5115325 := bstep (se 3 (by rfl) ⟨959123, by rfl⟩ : syracuseStep 5115325 = 1918247) B1918247
theorem B11505215 : Blo 1594996 11505215 := bstep (se 1 (by rfl) ⟨8628911, by rfl⟩ : syracuseStep 11505215 = 17257823) B17257823
theorem B23318189 : Blo 1594996 23318189 := bstep (se 3 (by rfl) ⟨4372160, by rfl⟩ : syracuseStep 23318189 = 8744321) B8744321
theorem B3592079 : Blo 1594996 3592079 := bstep (se 1 (by rfl) ⟨2694059, by rfl⟩ : syracuseStep 3592079 = 5388119) B5388119
theorem B10923983 : Blo 1594996 10923983 := bstep (se 1 (by rfl) ⟨8192987, by rfl⟩ : syracuseStep 10923983 = 16385975) B16385975
theorem B756502573 : Blo 1594996 756502573 := bstep (se 3 (by rfl) ⟨141844232, by rfl⟩ : syracuseStep 756502573 = 283688465) B283688465
theorem B18936017 : Blo 1594996 18936017 := bstep (se 2 (by rfl) ⟨7101006, by rfl⟩ : syracuseStep 18936017 = 14202013) B14202013
theorem B5386607 : Blo 1594996 5386607 := bstep (se 1 (by rfl) ⟨4039955, by rfl⟩ : syracuseStep 5386607 = 8079911) B8079911
theorem B3592799 : Blo 1594996 3592799 := bstep (se 1 (by rfl) ⟨2694599, by rfl⟩ : syracuseStep 3592799 = 5389199) B5389199
theorem B5829281 : Blo 1594996 5829281 := bstep (se 2 (by rfl) ⟨2185980, by rfl⟩ : syracuseStep 5829281 = 4371961) B4371961
theorem B17257481 : Blo 1594996 17257481 := bstep (se 2 (by rfl) ⟨6471555, by rfl⟩ : syracuseStep 17257481 = 12943111) B12943111
theorem B18674725 : Blo 1594996 18674725 := bstep (se 4 (by rfl) ⟨1750755, by rfl⟩ : syracuseStep 18674725 = 3501511) B3501511
theorem B7672913 : Blo 1594996 7672913 := bstep (se 2 (by rfl) ⟨2877342, by rfl⟩ : syracuseStep 7672913 = 5754685) B5754685
theorem B2020459 : Blo 1594996 2020459 := bstep (se 1 (by rfl) ⟨1515344, by rfl⟩ : syracuseStep 2020459 = 3030689) B3030689
theorem B2692271 : Blo 1594996 2692271 := bstep (se 1 (by rfl) ⟨2019203, by rfl⟩ : syracuseStep 2692271 = 4038407) B4038407
theorem B2692507 : Blo 1594996 2692507 := bstep (se 1 (by rfl) ⟨2019380, by rfl⟩ : syracuseStep 2692507 = 4038761) B4038761
theorem B20739629 : Blo 1594996 20739629 := bstep (se 3 (by rfl) ⟨3888680, by rfl⟩ : syracuseStep 20739629 = 7777361) B7777361
theorem B1595047 : Blo 1594996 1595047 := bstep (se 1 (by rfl) ⟨1196285, by rfl⟩ : syracuseStep 1595047 = 2392571) B2392571
theorem B10229419 : Blo 1594996 10229419 := bstep (se 1 (by rfl) ⟨7672064, by rfl⟩ : syracuseStep 10229419 = 15344129) B15344129
theorem B6813395 : Blo 1594996 6813395 := bstep (se 1 (by rfl) ⟨5110046, by rfl⟩ : syracuseStep 6813395 = 10220093) B10220093
theorem B2692831 : Blo 1594996 2692831 := bstep (se 1 (by rfl) ⟨2019623, by rfl⟩ : syracuseStep 2692831 = 4039247) B4039247
theorem B5388011 : Blo 1594996 5388011 := bstep (se 1 (by rfl) ⟨4041008, by rfl⟩ : syracuseStep 5388011 = 8082017) B8082017
theorem B1595131 : Blo 1594996 1595131 := bstep (se 1 (by rfl) ⟨1196348, by rfl⟩ : syracuseStep 1595131 = 2392697) B2392697
theorem B5461771 : Blo 1594996 5461771 := bstep (se 1 (by rfl) ⟨4096328, by rfl⟩ : syracuseStep 5461771 = 8192657) B8192657
theorem B1595167 : Blo 1594996 1595167 := bstep (se 1 (by rfl) ⟨1196375, by rfl⟩ : syracuseStep 1595167 = 2392751) B2392751
theorem B1595199 : Blo 1594996 1595199 := bstep (se 1 (by rfl) ⟨1196399, by rfl⟩ : syracuseStep 1595199 = 2392799) B2392799
theorem B46028695 : Blo 1594996 46028695 := bstep (se 1 (by rfl) ⟨34521521, by rfl⟩ : syracuseStep 46028695 = 69043043) B69043043
theorem B1595375 : Blo 1594996 1595375 := bstep (se 1 (by rfl) ⟨1196531, by rfl⟩ : syracuseStep 1595375 = 2393063) B2393063
theorem B4544495 : Blo 1594996 4544495 := bstep (se 1 (by rfl) ⟨3408371, by rfl⟩ : syracuseStep 4544495 = 6816743) B6816743
theorem B5388281 : Blo 1594996 5388281 := bstep (se 2 (by rfl) ⟨2020605, by rfl⟩ : syracuseStep 5388281 = 4041211) B4041211
theorem B19421279 : Blo 1594996 19421279 := bstep (se 1 (by rfl) ⟨14565959, by rfl⟩ : syracuseStep 19421279 = 29131919) B29131919
theorem B2693263 : Blo 1594996 2693263 := bstep (se 1 (by rfl) ⟨2019947, by rfl⟩ : syracuseStep 2693263 = 4039895) B4039895
theorem B1595547 : Blo 1594996 1595547 := bstep (se 1 (by rfl) ⟨1196660, by rfl⟩ : syracuseStep 1595547 = 2393321) B2393321
theorem B3029147 : Blo 1594996 3029147 := bstep (se 1 (by rfl) ⟨2271860, by rfl⟩ : syracuseStep 3029147 = 4543721) B4543721
theorem B5388443 : Blo 1594996 5388443 := bstep (se 1 (by rfl) ⟨4041332, by rfl⟩ : syracuseStep 5388443 = 8082665) B8082665
theorem B12122297 : Blo 1594996 12122297 := bstep (se 2 (by rfl) ⟨4545861, by rfl⟩ : syracuseStep 12122297 = 9091723) B9091723
theorem B1595583 : Blo 1594996 1595583 := bstep (se 1 (by rfl) ⟨1196687, by rfl⟩ : syracuseStep 1595583 = 2393375) B2393375
theorem B4856051 : Blo 1594996 4856051 := bstep (se 1 (by rfl) ⟨3642038, by rfl⟩ : syracuseStep 4856051 = 7284077) B7284077
theorem B5388551 : Blo 1594996 5388551 := bstep (se 1 (by rfl) ⟨4041413, by rfl⟩ : syracuseStep 5388551 = 8082827) B8082827
theorem B1595695 : Blo 1594996 1595695 := bstep (se 1 (by rfl) ⟨1196771, by rfl⟩ : syracuseStep 1595695 = 2393543) B2393543
theorem B18168137 : Blo 1594996 18168137 := bstep (se 2 (by rfl) ⟨6813051, by rfl⟩ : syracuseStep 18168137 = 13626103) B13626103
theorem B5110123 : Blo 1594996 5110123 := bstep (se 1 (by rfl) ⟨3832592, by rfl⟩ : syracuseStep 5110123 = 7665185) B7665185
theorem B345332219 : Blo 1594996 345332219 := bstep (se 1 (by rfl) ⟨258999164, by rfl⟩ : syracuseStep 345332219 = 517998329) B517998329
theorem B1595931 : Blo 1594996 1595931 := bstep (se 1 (by rfl) ⟨1196948, by rfl⟩ : syracuseStep 1595931 = 2393897) B2393897
theorem B1595935 : Blo 1594996 1595935 := bstep (se 1 (by rfl) ⟨1196951, by rfl⟩ : syracuseStep 1595935 = 2393903) B2393903
theorem B30661193 : Blo 1594996 30661193 := bstep (se 2 (by rfl) ⟨11497947, by rfl⟩ : syracuseStep 30661193 = 22995895) B22995895
theorem B12114521 : Blo 1594996 12114521 := bstep (se 2 (by rfl) ⟨4542945, by rfl⟩ : syracuseStep 12114521 = 9085891) B9085891
theorem B4545247 : Blo 1594996 4545247 := bstep (se 1 (by rfl) ⟨3408935, by rfl⟩ : syracuseStep 4545247 = 6817871) B6817871
theorem B1596251 : Blo 1594996 1596251 := bstep (se 1 (by rfl) ⟨1197188, by rfl⟩ : syracuseStep 1596251 = 2394377) B2394377
theorem B1596319 : Blo 1594996 1596319 := bstep (se 1 (by rfl) ⟨1197239, by rfl⟩ : syracuseStep 1596319 = 2394479) B2394479
theorem B10222631 : Blo 1594996 10222631 := bstep (se 1 (by rfl) ⟨7666973, by rfl⟩ : syracuseStep 10222631 = 15333947) B15333947
theorem B1596463 : Blo 1594996 1596463 := bstep (se 1 (by rfl) ⟨1197347, by rfl⟩ : syracuseStep 1596463 = 2394695) B2394695
theorem B1596487 : Blo 1594996 1596487 := bstep (se 1 (by rfl) ⟨1197365, by rfl⟩ : syracuseStep 1596487 = 2394731) B2394731
theorem B2694215 : Blo 1594996 2694215 := bstep (se 1 (by rfl) ⟨2020661, by rfl⟩ : syracuseStep 2694215 = 4041323) B4041323
theorem B1596639 : Blo 1594996 1596639 := bstep (se 1 (by rfl) ⟨1197479, by rfl⟩ : syracuseStep 1596639 = 2394959) B2394959
theorem B5389577 : Blo 1594996 5389577 := bstep (se 2 (by rfl) ⟨2021091, by rfl⟩ : syracuseStep 5389577 = 4042183) B4042183
theorem B13630751 : Blo 1594996 13630751 := bstep (se 1 (by rfl) ⟨10223063, by rfl⟩ : syracuseStep 13630751 = 20446127) B20446127
theorem B4545953 : Blo 1594996 4545953 := bstep (se 2 (by rfl) ⟨1704732, by rfl⟩ : syracuseStep 4545953 = 3409465) B3409465
theorem B2874791 : Blo 1594996 2874791 := bstep (se 1 (by rfl) ⟨2156093, by rfl⟩ : syracuseStep 2874791 = 4312187) B4312187
theorem B6815171 : Blo 1594996 6815171 := bstep (se 1 (by rfl) ⟨5111378, by rfl⟩ : syracuseStep 6815171 = 10222757) B10222757
theorem B12942787 : Blo 1594996 12942787 := bstep (se 1 (by rfl) ⟨9707090, by rfl⟩ : syracuseStep 12942787 = 19414181) B19414181
theorem B1596903 : Blo 1594996 1596903 := bstep (se 1 (by rfl) ⟨1197677, by rfl⟩ : syracuseStep 1596903 = 2395355) B2395355
theorem B2694647 : Blo 1594996 2694647 := bstep (se 1 (by rfl) ⟨2020985, by rfl⟩ : syracuseStep 2694647 = 4041971) B4041971
theorem B12115493 : Blo 1594996 12115493 := bstep (se 4 (by rfl) ⟨1135827, by rfl⟩ : syracuseStep 12115493 = 2271655) B2271655
theorem B2874943 : Blo 1594996 2874943 := bstep (se 1 (by rfl) ⟨2156207, by rfl⟩ : syracuseStep 2874943 = 4312415) B4312415
theorem B22994513 : Blo 1594996 22994513 := bstep (se 2 (by rfl) ⟨8622942, by rfl⟩ : syracuseStep 22994513 = 17245885) B17245885
theorem B13827809 : Blo 1594996 13827809 := bstep (se 2 (by rfl) ⟨5185428, by rfl⟩ : syracuseStep 13827809 = 10370857) B10370857
theorem B12624011 : Blo 1594996 12624011 := bstep (se 1 (by rfl) ⟨9468008, by rfl⟩ : syracuseStep 12624011 = 18936017) B18936017
theorem B25870843 : Blo 1594996 25870843 := bstep (se 1 (by rfl) ⟨19403132, by rfl⟩ : syracuseStep 25870843 = 38806265) B38806265
theorem B2392607 : Blo 1594996 2392607 := bstep (se 1 (by rfl) ⟨1794455, by rfl⟩ : syracuseStep 2392607 = 3588911) B3588911
theorem B1917551 : Blo 1594996 1917551 := bstep (se 1 (by rfl) ⟨1438163, by rfl⟩ : syracuseStep 1917551 = 2876327) B2876327
theorem B1794847 : Blo 1594996 1794847 := bstep (se 1 (by rfl) ⟨1346135, by rfl⟩ : syracuseStep 1794847 = 2692271) B2692271
theorem B1819423 : Blo 1594996 1819423 := bstep (se 1 (by rfl) ⟨1364567, by rfl⟩ : syracuseStep 1819423 = 2729135) B2729135
theorem B9094139 : Blo 1594996 9094139 := bstep (se 1 (by rfl) ⟨6820604, by rfl⟩ : syracuseStep 9094139 = 13641209) B13641209
theorem B4375547 : Blo 1594996 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B2393279 : Blo 1594996 2393279 := bstep (se 1 (by rfl) ⟨1794959, by rfl⟩ : syracuseStep 2393279 = 3589919) B3589919
theorem B3589343 : Blo 1594996 3589343 := bstep (se 1 (by rfl) ⟨2692007, by rfl⟩ : syracuseStep 3589343 = 5384015) B5384015
theorem B2393423 : Blo 1594996 2393423 := bstep (se 1 (by rfl) ⟨1795067, by rfl⟩ : syracuseStep 2393423 = 3590135) B3590135
theorem B2393513 : Blo 1594996 2393513 := bstep (se 2 (by rfl) ⟨897567, by rfl⟩ : syracuseStep 2393513 = 1795135) B1795135
theorem B3589559 : Blo 1594996 3589559 := bstep (se 1 (by rfl) ⟨2692169, by rfl⟩ : syracuseStep 3589559 = 5384339) B5384339
theorem B8750585 : Blo 1594996 8750585 := bstep (se 2 (by rfl) ⟨3281469, by rfl⟩ : syracuseStep 8750585 = 6562939) B6562939
theorem B2393663 : Blo 1594996 2393663 := bstep (se 1 (by rfl) ⟨1795247, by rfl⟩ : syracuseStep 2393663 = 3590495) B3590495
theorem B2393705 : Blo 1594996 2393705 := bstep (se 2 (by rfl) ⟨897639, by rfl⟩ : syracuseStep 2393705 = 1795279) B1795279
theorem B3589739 : Blo 1594996 3589739 := bstep (se 1 (by rfl) ⟨2692304, by rfl⟩ : syracuseStep 3589739 = 5384609) B5384609
theorem B13633211 : Blo 1594996 13633211 := bstep (se 1 (by rfl) ⟨10224908, by rfl⟩ : syracuseStep 13633211 = 20449817) B20449817
theorem B20440795 : Blo 1594996 20440795 := bstep (se 1 (by rfl) ⟨15330596, by rfl⟩ : syracuseStep 20440795 = 30661193) B30661193
theorem B6817547 : Blo 1594996 6817547 := bstep (se 1 (by rfl) ⟨5113160, by rfl⟩ : syracuseStep 6817547 = 10226321) B10226321
theorem B3835687 : Blo 1594996 3835687 := bstep (se 1 (by rfl) ⟨2876765, by rfl⟩ : syracuseStep 3835687 = 5753531) B5753531
theorem B3590009 : Blo 1594996 3590009 := bstep (se 2 (by rfl) ⟨1346253, by rfl⟩ : syracuseStep 3590009 = 2692507) B2692507
theorem B2394143 : Blo 1594996 2394143 := bstep (se 1 (by rfl) ⟨1795607, by rfl⟩ : syracuseStep 2394143 = 3591215) B3591215
theorem B1796143 : Blo 1594996 1796143 := bstep (se 1 (by rfl) ⟨1347107, by rfl⟩ : syracuseStep 1796143 = 2694215) B2694215
theorem B9087167 : Blo 1594996 9087167 := bstep (se 1 (by rfl) ⟨6815375, by rfl⟩ : syracuseStep 9087167 = 13630751) B13630751
theorem B2394335 : Blo 1594996 2394335 := bstep (se 1 (by rfl) ⟨1795751, by rfl⟩ : syracuseStep 2394335 = 3591503) B3591503
theorem B2394395 : Blo 1594996 2394395 := bstep (se 1 (by rfl) ⟨1795796, by rfl⟩ : syracuseStep 2394395 = 3591593) B3591593
theorem B3590441 : Blo 1594996 3590441 := bstep (se 2 (by rfl) ⟨1346415, by rfl⟩ : syracuseStep 3590441 = 2692831) B2692831
theorem B1796431 : Blo 1594996 1796431 := bstep (se 1 (by rfl) ⟨1347323, by rfl⟩ : syracuseStep 1796431 = 2694647) B2694647
theorem B7670143 : Blo 1594996 7670143 := bstep (se 1 (by rfl) ⟨5752607, by rfl⟩ : syracuseStep 7670143 = 11505215) B11505215
theorem B15329675 : Blo 1594996 15329675 := bstep (se 1 (by rfl) ⟨11497256, by rfl⟩ : syracuseStep 15329675 = 22994513) B22994513
theorem B9218539 : Blo 1594996 9218539 := bstep (se 1 (by rfl) ⟨6913904, by rfl⟩ : syracuseStep 9218539 = 13827809) B13827809
theorem B2394719 : Blo 1594996 2394719 := bstep (se 1 (by rfl) ⟨1796039, by rfl⟩ : syracuseStep 2394719 = 3592079) B3592079
theorem B7277213 : Blo 1594996 7277213 := bstep (se 3 (by rfl) ⟨1364477, by rfl⟩ : syracuseStep 7277213 = 2728955) B2728955
theorem B3591017 : Blo 1594996 3591017 := bstep (se 2 (by rfl) ⟨1346631, by rfl⟩ : syracuseStep 3591017 = 2693263) B2693263
theorem B2395001 : Blo 1594996 2395001 := bstep (se 2 (by rfl) ⟨898125, by rfl⟩ : syracuseStep 2395001 = 1796251) B1796251
theorem B3591071 : Blo 1594996 3591071 := bstep (se 1 (by rfl) ⟨2693303, by rfl⟩ : syracuseStep 3591071 = 5386607) B5386607
theorem B2395049 : Blo 1594996 2395049 := bstep (se 2 (by rfl) ⟨898143, by rfl⟩ : syracuseStep 2395049 = 1796287) B1796287
theorem B5385257 : Blo 1594996 5385257 := bstep (se 2 (by rfl) ⟨2019471, by rfl⟩ : syracuseStep 5385257 = 4038943) B4038943
theorem B2395199 : Blo 1594996 2395199 := bstep (se 1 (by rfl) ⟨1796399, by rfl⟩ : syracuseStep 2395199 = 3592799) B3592799
theorem B3886187 : Blo 1594996 3886187 := bstep (se 1 (by rfl) ⟨2914640, by rfl⟩ : syracuseStep 3886187 = 5829281) B5829281
theorem B5385527 : Blo 1594996 5385527 := bstep (se 1 (by rfl) ⟨4039145, by rfl⟩ : syracuseStep 5385527 = 8078291) B8078291
theorem B11504987 : Blo 1594996 11504987 := bstep (se 1 (by rfl) ⟨8628740, by rfl⟩ : syracuseStep 11504987 = 17257481) B17257481
theorem B5115275 : Blo 1594996 5115275 := bstep (se 1 (by rfl) ⟨3836456, by rfl⟩ : syracuseStep 5115275 = 7672913) B7672913
theorem B36859283 : Blo 1594996 36859283 := bstep (se 1 (by rfl) ⟨27644462, by rfl⟩ : syracuseStep 36859283 = 55288925) B55288925
theorem B2158331 : Blo 1594996 2158331 := bstep (se 1 (by rfl) ⟨1618748, by rfl⟩ : syracuseStep 2158331 = 3237497) B3237497
theorem B4542263 : Blo 1594996 4542263 := bstep (se 1 (by rfl) ⟨3406697, by rfl⟩ : syracuseStep 4542263 = 6813395) B6813395
theorem B1617727 : Blo 1594996 1617727 := bstep (se 1 (by rfl) ⟨1213295, by rfl⟩ : syracuseStep 1617727 = 2426591) B2426591
theorem B3592007 : Blo 1594996 3592007 := bstep (se 1 (by rfl) ⟨2694005, by rfl⟩ : syracuseStep 3592007 = 5388011) B5388011
theorem B5386121 : Blo 1594996 5386121 := bstep (se 2 (by rfl) ⟨2019795, by rfl⟩ : syracuseStep 5386121 = 4039591) B4039591
theorem B17248139 : Blo 1594996 17248139 := bstep (se 1 (by rfl) ⟨12936104, by rfl⟩ : syracuseStep 17248139 = 25872209) B25872209
theorem B3592187 : Blo 1594996 3592187 := bstep (se 1 (by rfl) ⟨2694140, by rfl⟩ : syracuseStep 3592187 = 5388281) B5388281
theorem B24899633 : Blo 1594996 24899633 := bstep (se 2 (by rfl) ⟨9337362, by rfl⟩ : syracuseStep 24899633 = 18674725) B18674725
theorem B12947519 : Blo 1594996 12947519 := bstep (se 1 (by rfl) ⟨9710639, by rfl⟩ : syracuseStep 12947519 = 19421279) B19421279
theorem B2019431 : Blo 1594996 2019431 := bstep (se 1 (by rfl) ⟨1514573, by rfl⟩ : syracuseStep 2019431 = 3029147) B3029147
theorem B3592295 : Blo 1594996 3592295 := bstep (se 1 (by rfl) ⟨2694221, by rfl⟩ : syracuseStep 3592295 = 5388443) B5388443
theorem B8081531 : Blo 1594996 8081531 := bstep (se 1 (by rfl) ⟨6061148, by rfl⟩ : syracuseStep 8081531 = 12122297) B12122297
theorem B3592367 : Blo 1594996 3592367 := bstep (se 1 (by rfl) ⟨2694275, by rfl⟩ : syracuseStep 3592367 = 5388551) B5388551
theorem B12112091 : Blo 1594996 12112091 := bstep (se 1 (by rfl) ⟨9084068, by rfl⟩ : syracuseStep 12112091 = 18168137) B18168137
theorem B21852659 : Blo 1594996 21852659 := bstep (se 1 (by rfl) ⟨16389494, by rfl⟩ : syracuseStep 21852659 = 32778989) B32778989
theorem B18182717 : Blo 1594996 18182717 := bstep (se 3 (by rfl) ⟨3409259, by rfl⟩ : syracuseStep 18182717 = 6818519) B6818519
theorem B6820433 : Blo 1594996 6820433 := bstep (se 2 (by rfl) ⟨2557662, by rfl⟩ : syracuseStep 6820433 = 5115325) B5115325
theorem B17257049 : Blo 1594996 17257049 := bstep (se 2 (by rfl) ⟨6471393, by rfl⟩ : syracuseStep 17257049 = 12942787) B12942787
theorem B13628087 : Blo 1594996 13628087 := bstep (se 1 (by rfl) ⟨10221065, by rfl⟩ : syracuseStep 13628087 = 20442131) B20442131
theorem B12120839 : Blo 1594996 12120839 := bstep (se 1 (by rfl) ⟨9090629, by rfl⟩ : syracuseStep 12120839 = 18181259) B18181259
theorem B3593051 : Blo 1594996 3593051 := bstep (se 1 (by rfl) ⟨2694788, by rfl⟩ : syracuseStep 3593051 = 5389577) B5389577
theorem B4543447 : Blo 1594996 4543447 := bstep (se 1 (by rfl) ⟨3407585, by rfl⟩ : syracuseStep 4543447 = 6815171) B6815171
theorem B15545459 : Blo 1594996 15545459 := bstep (se 1 (by rfl) ⟨11659094, by rfl⟩ : syracuseStep 15545459 = 23318189) B23318189
theorem B61371593 : Blo 1594996 61371593 := bstep (se 2 (by rfl) ⟨23014347, by rfl⟩ : syracuseStep 61371593 = 46028695) B46028695
theorem B1008670097 : Blo 1594996 1008670097 := bstep (se 2 (by rfl) ⟨378251286, by rfl⟩ : syracuseStep 1008670097 = 756502573) B756502573
theorem B6821459 : Blo 1594996 6821459 := bstep (se 1 (by rfl) ⟨5116094, by rfl⟩ : syracuseStep 6821459 = 10232189) B10232189
theorem B1595035 : Blo 1594996 1595035 := bstep (se 1 (by rfl) ⟨1196276, by rfl⟩ : syracuseStep 1595035 = 2392553) B2392553
theorem B1595119 : Blo 1594996 1595119 := bstep (se 1 (by rfl) ⟨1196339, by rfl⟩ : syracuseStep 1595119 = 2392679) B2392679
theorem B6813497 : Blo 1594996 6813497 := bstep (se 2 (by rfl) ⟨2555061, by rfl⟩ : syracuseStep 6813497 = 5110123) B5110123
theorem B1595207 : Blo 1594996 1595207 := bstep (se 1 (by rfl) ⟨1196405, by rfl⟩ : syracuseStep 1595207 = 2392811) B2392811
theorem B1595227 : Blo 1594996 1595227 := bstep (se 1 (by rfl) ⟨1196420, by rfl⟩ : syracuseStep 1595227 = 2392841) B2392841
theorem B1595295 : Blo 1594996 1595295 := bstep (se 1 (by rfl) ⟨1196471, by rfl⟩ : syracuseStep 1595295 = 2392943) B2392943
theorem B12949469 : Blo 1594996 12949469 := bstep (se 3 (by rfl) ⟨2428025, by rfl⟩ : syracuseStep 12949469 = 4856051) B4856051
theorem B1595463 : Blo 1594996 1595463 := bstep (se 1 (by rfl) ⟨1196597, by rfl⟩ : syracuseStep 1595463 = 2393195) B2393195
theorem B1595623 : Blo 1594996 1595623 := bstep (se 1 (by rfl) ⟨1196717, by rfl⟩ : syracuseStep 1595623 = 2393435) B2393435
theorem B6060329 : Blo 1594996 6060329 := bstep (se 2 (by rfl) ⟨2272623, by rfl⟩ : syracuseStep 6060329 = 4545247) B4545247
theorem B13826419 : Blo 1594996 13826419 := bstep (se 1 (by rfl) ⟨10369814, by rfl⟩ : syracuseStep 13826419 = 20739629) B20739629
theorem B1595807 : Blo 1594996 1595807 := bstep (se 1 (by rfl) ⟨1196855, by rfl⟩ : syracuseStep 1595807 = 2393711) B2393711
theorem B7666109 : Blo 1594996 7666109 := bstep (se 3 (by rfl) ⟨1437395, by rfl⟩ : syracuseStep 7666109 = 2874791) B2874791
theorem B1595855 : Blo 1594996 1595855 := bstep (se 1 (by rfl) ⟨1196891, by rfl⟩ : syracuseStep 1595855 = 2393783) B2393783
theorem B1595879 : Blo 1594996 1595879 := bstep (se 1 (by rfl) ⟨1196909, by rfl⟩ : syracuseStep 1595879 = 2393819) B2393819
theorem B1595995 : Blo 1594996 1595995 := bstep (se 1 (by rfl) ⟨1196996, by rfl⟩ : syracuseStep 1595995 = 2393993) B2393993
theorem B920885917 : Blo 1594996 920885917 := bstep (se 3 (by rfl) ⟨172666109, by rfl⟩ : syracuseStep 920885917 = 345332219) B345332219
theorem B3029663 : Blo 1594996 3029663 := bstep (se 1 (by rfl) ⟨2272247, by rfl⟩ : syracuseStep 3029663 = 4544495) B4544495
theorem B1596063 : Blo 1594996 1596063 := bstep (se 1 (by rfl) ⟨1197047, by rfl⟩ : syracuseStep 1596063 = 2394095) B2394095
theorem B2693945 : Blo 1594996 2693945 := bstep (se 2 (by rfl) ⟨1010229, by rfl⟩ : syracuseStep 2693945 = 2020459) B2020459
theorem B1596231 : Blo 1594996 1596231 := bstep (se 1 (by rfl) ⟨1197173, by rfl⟩ : syracuseStep 1596231 = 2394347) B2394347
theorem B15547241 : Blo 1594996 15547241 := bstep (se 2 (by rfl) ⟨5830215, by rfl⟩ : syracuseStep 15547241 = 11660431) B11660431
theorem B1596271 : Blo 1594996 1596271 := bstep (se 1 (by rfl) ⟨1197203, by rfl⟩ : syracuseStep 1596271 = 2394407) B2394407
theorem B2693999 : Blo 1594996 2693999 := bstep (se 1 (by rfl) ⟨2020499, by rfl⟩ : syracuseStep 2693999 = 4040999) B4040999
theorem B1596327 : Blo 1594996 1596327 := bstep (se 1 (by rfl) ⟨1197245, by rfl⟩ : syracuseStep 1596327 = 2394491) B2394491
theorem B8076347 : Blo 1594996 8076347 := bstep (se 1 (by rfl) ⟨6057260, by rfl⟩ : syracuseStep 8076347 = 12114521) B12114521
theorem B1596507 : Blo 1594996 1596507 := bstep (se 1 (by rfl) ⟨1197380, by rfl⟩ : syracuseStep 1596507 = 2394761) B2394761
theorem B1596623 : Blo 1594996 1596623 := bstep (se 1 (by rfl) ⟨1197467, by rfl⟩ : syracuseStep 1596623 = 2394935) B2394935
theorem B1596647 : Blo 1594996 1596647 := bstep (se 1 (by rfl) ⟨1197485, by rfl⟩ : syracuseStep 1596647 = 2394971) B2394971
theorem B1596743 : Blo 1594996 1596743 := bstep (se 1 (by rfl) ⟨1197557, by rfl⟩ : syracuseStep 1596743 = 2395115) B2395115
theorem B6815087 : Blo 1594996 6815087 := bstep (se 1 (by rfl) ⟨5111315, by rfl⟩ : syracuseStep 6815087 = 10222631) B10222631
theorem B3833257 : Blo 1594996 3833257 := bstep (se 2 (by rfl) ⟨1437471, by rfl⟩ : syracuseStep 3833257 = 2874943) B2874943
theorem B1596879 : Blo 1594996 1596879 := bstep (se 1 (by rfl) ⟨1197659, by rfl⟩ : syracuseStep 1596879 = 2395319) B2395319
theorem B13639225 : Blo 1594996 13639225 := bstep (se 2 (by rfl) ⟨5114709, by rfl⟩ : syracuseStep 13639225 = 10229419) B10229419
theorem B3030635 : Blo 1594996 3030635 := bstep (se 1 (by rfl) ⟨2272976, by rfl⟩ : syracuseStep 3030635 = 4545953) B4545953
theorem B7282361 : Blo 1594996 7282361 := bstep (se 2 (by rfl) ⟨2730885, by rfl⟩ : syracuseStep 7282361 = 5461771) B5461771
theorem B8076995 : Blo 1594996 8076995 := bstep (se 1 (by rfl) ⟨6057746, by rfl⟩ : syracuseStep 8076995 = 12115493) B12115493
theorem B7282655 : Blo 1594996 7282655 := bstep (se 1 (by rfl) ⟨5461991, by rfl⟩ : syracuseStep 7282655 = 10923983) B10923983
theorem B4546955 : Blo 1594996 4546955 := bstep (se 1 (by rfl) ⟨3410216, by rfl⟩ : syracuseStep 4546955 = 6820433) B6820433
theorem B9085391 : Blo 1594996 9085391 := bstep (se 1 (by rfl) ⟨6814043, by rfl⟩ : syracuseStep 9085391 = 13628087) B13628087
theorem B6062759 : Blo 1594996 6062759 := bstep (se 1 (by rfl) ⟨4547069, by rfl⟩ : syracuseStep 6062759 = 9094139) B9094139
theorem B2917031 : Blo 1594996 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B10363639 : Blo 1594996 10363639 := bstep (se 1 (by rfl) ⟨7772729, by rfl⟩ : syracuseStep 10363639 = 15545459) B15545459
theorem B2392895 : Blo 1594996 2392895 := bstep (se 1 (by rfl) ⟨1794671, by rfl⟩ : syracuseStep 2392895 = 3589343) B3589343
theorem B2393039 : Blo 1594996 2393039 := bstep (se 1 (by rfl) ⟨1794779, by rfl⟩ : syracuseStep 2393039 = 3589559) B3589559
theorem B5833723 : Blo 1594996 5833723 := bstep (se 1 (by rfl) ⟨4375292, by rfl⟩ : syracuseStep 5833723 = 8750585) B8750585
theorem B2393129 : Blo 1594996 2393129 := bstep (se 2 (by rfl) ⟨897423, by rfl⟩ : syracuseStep 2393129 = 1794847) B1794847
theorem B2425897 : Blo 1594996 2425897 := bstep (se 2 (by rfl) ⟨909711, by rfl⟩ : syracuseStep 2425897 = 1819423) B1819423
theorem B4547639 : Blo 1594996 4547639 := bstep (se 1 (by rfl) ⟨3410729, by rfl⟩ : syracuseStep 4547639 = 6821459) B6821459
theorem B2393159 : Blo 1594996 2393159 := bstep (se 1 (by rfl) ⟨1794869, by rfl⟩ : syracuseStep 2393159 = 3589739) B3589739
theorem B41452661 : Blo 1594996 41452661 := bstep (se 5 (by rfl) ⟨1943093, by rfl⟩ : syracuseStep 41452661 = 3886187) B3886187
theorem B2393339 : Blo 1594996 2393339 := bstep (se 1 (by rfl) ⟨1795004, by rfl⟩ : syracuseStep 2393339 = 3590009) B3590009
theorem B2393627 : Blo 1594996 2393627 := bstep (se 1 (by rfl) ⟨1795220, by rfl⟩ : syracuseStep 2393627 = 3590441) B3590441
theorem B4040219 : Blo 1594996 4040219 := bstep (se 1 (by rfl) ⟨3030164, by rfl⟩ : syracuseStep 4040219 = 6060329) B6060329
theorem B5113469 : Blo 1594996 5113469 := bstep (se 3 (by rfl) ⟨958775, by rfl⟩ : syracuseStep 5113469 = 1917551) B1917551
theorem B8079101 : Blo 1594996 8079101 := bstep (se 3 (by rfl) ⟨1514831, by rfl⟩ : syracuseStep 8079101 = 3029663) B3029663
theorem B1795963 : Blo 1594996 1795963 := bstep (se 1 (by rfl) ⟨1346972, by rfl⟩ : syracuseStep 1795963 = 2693945) B2693945
theorem B2394011 : Blo 1594996 2394011 := bstep (se 1 (by rfl) ⟨1795508, by rfl⟩ : syracuseStep 2394011 = 3591017) B3591017
theorem B1795999 : Blo 1594996 1795999 := bstep (se 1 (by rfl) ⟨1346999, by rfl⟩ : syracuseStep 1795999 = 2693999) B2693999
theorem B2394047 : Blo 1594996 2394047 := bstep (se 1 (by rfl) ⟨1795535, by rfl⟩ : syracuseStep 2394047 = 3591071) B3591071
theorem B3590171 : Blo 1594996 3590171 := bstep (se 1 (by rfl) ⟨2692628, by rfl⟩ : syracuseStep 3590171 = 5385257) B5385257
theorem B5384231 : Blo 1594996 5384231 := bstep (se 1 (by rfl) ⟨4038173, by rfl⟩ : syracuseStep 5384231 = 8076347) B8076347
theorem B3590351 : Blo 1594996 3590351 := bstep (se 1 (by rfl) ⟨2692763, by rfl⟩ : syracuseStep 3590351 = 5385527) B5385527
theorem B7669991 : Blo 1594996 7669991 := bstep (se 1 (by rfl) ⟨5752493, by rfl⟩ : syracuseStep 7669991 = 11504987) B11504987
theorem B3410183 : Blo 1594996 3410183 := bstep (se 1 (by rfl) ⟨2557637, by rfl⟩ : syracuseStep 3410183 = 5115275) B5115275
theorem B5114249 : Blo 1594996 5114249 := bstep (se 2 (by rfl) ⟨1917843, by rfl⟩ : syracuseStep 5114249 = 3835687) B3835687
theorem B2156969 : Blo 1594996 2156969 := bstep (se 2 (by rfl) ⟨808863, by rfl⟩ : syracuseStep 2156969 = 1617727) B1617727
theorem B5384663 : Blo 1594996 5384663 := bstep (se 1 (by rfl) ⟨4038497, by rfl⟩ : syracuseStep 5384663 = 8076995) B8076995
theorem B2394671 : Blo 1594996 2394671 := bstep (se 1 (by rfl) ⟨1796003, by rfl⟩ : syracuseStep 2394671 = 3592007) B3592007
theorem B3590747 : Blo 1594996 3590747 := bstep (se 1 (by rfl) ⟨2693060, by rfl⟩ : syracuseStep 3590747 = 5386121) B5386121
theorem B2394791 : Blo 1594996 2394791 := bstep (se 1 (by rfl) ⟨1796093, by rfl⟩ : syracuseStep 2394791 = 3592187) B3592187
theorem B16599755 : Blo 1594996 16599755 := bstep (se 1 (by rfl) ⟨12449816, by rfl⟩ : syracuseStep 16599755 = 24899633) B24899633
theorem B2394857 : Blo 1594996 2394857 := bstep (se 2 (by rfl) ⟨898071, by rfl⟩ : syracuseStep 2394857 = 1796143) B1796143
theorem B2394863 : Blo 1594996 2394863 := bstep (se 1 (by rfl) ⟨1796147, by rfl⟩ : syracuseStep 2394863 = 3592295) B3592295
theorem B8416007 : Blo 1594996 8416007 := bstep (se 1 (by rfl) ⟨6312005, by rfl⟩ : syracuseStep 8416007 = 12624011) B12624011
theorem B2394911 : Blo 1594996 2394911 := bstep (se 1 (by rfl) ⟨1796183, by rfl⟩ : syracuseStep 2394911 = 3592367) B3592367
theorem B5385149 : Blo 1594996 5385149 := bstep (se 3 (by rfl) ⟨1009715, by rfl⟩ : syracuseStep 5385149 = 2019431) B2019431
theorem B14568439 : Blo 1594996 14568439 := bstep (se 1 (by rfl) ⟨10926329, by rfl⟩ : syracuseStep 14568439 = 21852659) B21852659
theorem B11504699 : Blo 1594996 11504699 := bstep (se 1 (by rfl) ⟨8628524, by rfl⟩ : syracuseStep 11504699 = 17257049) B17257049
theorem B2395241 : Blo 1594996 2395241 := bstep (se 2 (by rfl) ⟨898215, by rfl⟩ : syracuseStep 2395241 = 1796431) B1796431
theorem B10226857 : Blo 1594996 10226857 := bstep (se 2 (by rfl) ⟨3835071, by rfl⟩ : syracuseStep 10226857 = 7670143) B7670143
theorem B8080559 : Blo 1594996 8080559 := bstep (se 1 (by rfl) ⟨6060419, by rfl⟩ : syracuseStep 8080559 = 12120839) B12120839
theorem B2395367 : Blo 1594996 2395367 := bstep (se 1 (by rfl) ⟨1796525, by rfl⟩ : syracuseStep 2395367 = 3593051) B3593051
theorem B12291385 : Blo 1594996 12291385 := bstep (se 2 (by rfl) ⟨4609269, by rfl⟩ : syracuseStep 12291385 = 9218539) B9218539
theorem B40914395 : Blo 1594996 40914395 := bstep (se 1 (by rfl) ⟨30685796, by rfl⟩ : syracuseStep 40914395 = 61371593) B61371593
theorem B9088807 : Blo 1594996 9088807 := bstep (se 1 (by rfl) ⟨6816605, by rfl⟩ : syracuseStep 9088807 = 13633211) B13633211
theorem B4542331 : Blo 1594996 4542331 := bstep (se 1 (by rfl) ⟨3406748, by rfl⟩ : syracuseStep 4542331 = 6813497) B6813497
theorem B6057929 : Blo 1594996 6057929 := bstep (se 2 (by rfl) ⟨2271723, by rfl⟩ : syracuseStep 6057929 = 4543447) B4543447
theorem B6058111 : Blo 1594996 6058111 := bstep (se 1 (by rfl) ⟨4543583, by rfl⟩ : syracuseStep 6058111 = 9087167) B9087167
theorem B10219783 : Blo 1594996 10219783 := bstep (se 1 (by rfl) ⟨7664837, by rfl⟩ : syracuseStep 10219783 = 15329675) B15329675
theorem B8081693 : Blo 1594996 8081693 := bstep (se 3 (by rfl) ⟨1515317, by rfl⟩ : syracuseStep 8081693 = 3030635) B3030635
theorem B73740901 : Blo 1594996 73740901 := bstep (se 4 (by rfl) ⟨6913209, by rfl⟩ : syracuseStep 73740901 = 13826419) B13826419
theorem B5755549 : Blo 1594996 5755549 := bstep (se 3 (by rfl) ⟨1079165, by rfl⟩ : syracuseStep 5755549 = 2158331) B2158331
theorem B4543391 : Blo 1594996 4543391 := bstep (se 1 (by rfl) ⟨3407543, by rfl⟩ : syracuseStep 4543391 = 6815087) B6815087
theorem B24572855 : Blo 1594996 24572855 := bstep (se 1 (by rfl) ⟨18429641, by rfl⟩ : syracuseStep 24572855 = 36859283) B36859283
theorem B4854907 : Blo 1594996 4854907 := bstep (se 1 (by rfl) ⟨3641180, by rfl⟩ : syracuseStep 4854907 = 7282361) B7282361
theorem B3028175 : Blo 1594996 3028175 := bstep (se 1 (by rfl) ⟨2271131, by rfl⟩ : syracuseStep 3028175 = 4542263) B4542263
theorem B11498759 : Blo 1594996 11498759 := bstep (se 1 (by rfl) ⟨8624069, by rfl⟩ : syracuseStep 11498759 = 17248139) B17248139
theorem B4855103 : Blo 1594996 4855103 := bstep (se 1 (by rfl) ⟨3641327, by rfl⟩ : syracuseStep 4855103 = 7282655) B7282655
theorem B8631679 : Blo 1594996 8631679 := bstep (se 1 (by rfl) ⟨6473759, by rfl⟩ : syracuseStep 8631679 = 12947519) B12947519
theorem B5387687 : Blo 1594996 5387687 := bstep (se 1 (by rfl) ⟨4040765, by rfl⟩ : syracuseStep 5387687 = 8081531) B8081531
theorem B8074727 : Blo 1594996 8074727 := bstep (se 1 (by rfl) ⟨6056045, by rfl⟩ : syracuseStep 8074727 = 12112091) B12112091
theorem B1595071 : Blo 1594996 1595071 := bstep (se 1 (by rfl) ⟨1196303, by rfl⟩ : syracuseStep 1595071 = 2392607) B2392607
theorem B12121811 : Blo 1594996 12121811 := bstep (se 1 (by rfl) ⟨9091358, by rfl⟩ : syracuseStep 12121811 = 18182717) B18182717
theorem B34494457 : Blo 1594996 34494457 := bstep (se 2 (by rfl) ⟨12935421, by rfl⟩ : syracuseStep 34494457 = 25870843) B25870843
theorem B1595519 : Blo 1594996 1595519 := bstep (se 1 (by rfl) ⟨1196639, by rfl⟩ : syracuseStep 1595519 = 2393279) B2393279
theorem B1227847889 : Blo 1594996 1227847889 := bstep (se 2 (by rfl) ⟨460442958, by rfl⟩ : syracuseStep 1227847889 = 920885917) B920885917
theorem B1595615 : Blo 1594996 1595615 := bstep (se 1 (by rfl) ⟨1196711, by rfl⟩ : syracuseStep 1595615 = 2393423) B2393423
theorem B672446731 : Blo 1594996 672446731 := bstep (se 1 (by rfl) ⟨504335048, by rfl⟩ : syracuseStep 672446731 = 1008670097) B1008670097
theorem B1595675 : Blo 1594996 1595675 := bstep (se 1 (by rfl) ⟨1196756, by rfl⟩ : syracuseStep 1595675 = 2393513) B2393513
theorem B1595775 : Blo 1594996 1595775 := bstep (se 1 (by rfl) ⟨1196831, by rfl⟩ : syracuseStep 1595775 = 2393663) B2393663
theorem B1595803 : Blo 1594996 1595803 := bstep (se 1 (by rfl) ⟨1196852, by rfl⟩ : syracuseStep 1595803 = 2393705) B2393705
theorem B4545031 : Blo 1594996 4545031 := bstep (se 1 (by rfl) ⟨3408773, by rfl⟩ : syracuseStep 4545031 = 6817547) B6817547
theorem B8632979 : Blo 1594996 8632979 := bstep (se 1 (by rfl) ⟨6474734, by rfl⟩ : syracuseStep 8632979 = 12949469) B12949469
theorem B1596095 : Blo 1594996 1596095 := bstep (se 1 (by rfl) ⟨1197071, by rfl⟩ : syracuseStep 1596095 = 2394143) B2394143
theorem B1596223 : Blo 1594996 1596223 := bstep (se 1 (by rfl) ⟨1197167, by rfl⟩ : syracuseStep 1596223 = 2394335) B2394335
theorem B1596263 : Blo 1594996 1596263 := bstep (se 1 (by rfl) ⟨1197197, by rfl⟩ : syracuseStep 1596263 = 2394395) B2394395
theorem B5110739 : Blo 1594996 5110739 := bstep (se 1 (by rfl) ⟨3833054, by rfl⟩ : syracuseStep 5110739 = 7666109) B7666109
theorem B1596479 : Blo 1594996 1596479 := bstep (se 1 (by rfl) ⟨1197359, by rfl⟩ : syracuseStep 1596479 = 2394719) B2394719
theorem B19405901 : Blo 1594996 19405901 := bstep (se 3 (by rfl) ⟨3638606, by rfl⟩ : syracuseStep 19405901 = 7277213) B7277213
theorem B5111009 : Blo 1594996 5111009 := bstep (se 2 (by rfl) ⟨1916628, by rfl⟩ : syracuseStep 5111009 = 3833257) B3833257
theorem B1596667 : Blo 1594996 1596667 := bstep (se 1 (by rfl) ⟨1197500, by rfl⟩ : syracuseStep 1596667 = 2395001) B2395001
theorem B1596699 : Blo 1594996 1596699 := bstep (se 1 (by rfl) ⟨1197524, by rfl⟩ : syracuseStep 1596699 = 2395049) B2395049
theorem B1596799 : Blo 1594996 1596799 := bstep (se 1 (by rfl) ⟨1197599, by rfl⟩ : syracuseStep 1596799 = 2395199) B2395199
theorem B18185633 : Blo 1594996 18185633 := bstep (se 2 (by rfl) ⟨6819612, by rfl⟩ : syracuseStep 18185633 = 13639225) B13639225
theorem B41459309 : Blo 1594996 41459309 := bstep (se 3 (by rfl) ⟨7773620, by rfl⟩ : syracuseStep 41459309 = 15547241) B15547241
theorem B27254393 : Blo 1594996 27254393 := bstep (se 2 (by rfl) ⟨10220397, by rfl⟩ : syracuseStep 27254393 = 20440795) B20440795
theorem B8077481 : Blo 1594996 8077481 := bstep (se 2 (by rfl) ⟨3029055, by rfl⟩ : syracuseStep 8077481 = 6058111) B6058111
theorem B3031759 : Blo 1594996 3031759 := bstep (se 1 (by rfl) ⟨2273819, by rfl⟩ : syracuseStep 3031759 = 4547639) B4547639
theorem B98321201 : Blo 1594996 98321201 := bstep (se 2 (by rfl) ⟨36870450, by rfl⟩ : syracuseStep 98321201 = 73740901) B73740901
theorem B3236735 : Blo 1594996 3236735 := bstep (se 1 (by rfl) ⟨2427551, by rfl⟩ : syracuseStep 3236735 = 4855103) B4855103
theorem B5383151 : Blo 1594996 5383151 := bstep (se 1 (by rfl) ⟨4037363, by rfl⟩ : syracuseStep 5383151 = 8074727) B8074727
theorem B12125213 : Blo 1594996 12125213 := bstep (se 3 (by rfl) ⟨2273477, by rfl⟩ : syracuseStep 12125213 = 4546955) B4546955
theorem B3408979 : Blo 1594996 3408979 := bstep (se 1 (by rfl) ⟨2556734, by rfl⟩ : syracuseStep 3408979 = 5113469) B5113469
theorem B5751917 : Blo 1594996 5751917 := bstep (se 3 (by rfl) ⟨1078484, by rfl⟩ : syracuseStep 5751917 = 2156969) B2156969
theorem B19424585 : Blo 1594996 19424585 := bstep (se 2 (by rfl) ⟨7284219, by rfl⟩ : syracuseStep 19424585 = 14568439) B14568439
theorem B2393447 : Blo 1594996 2393447 := bstep (se 1 (by rfl) ⟨1795085, by rfl⟩ : syracuseStep 2393447 = 3590171) B3590171
theorem B3589487 : Blo 1594996 3589487 := bstep (se 1 (by rfl) ⟨2692115, by rfl⟩ : syracuseStep 3589487 = 5384231) B5384231
theorem B2393567 : Blo 1594996 2393567 := bstep (se 1 (by rfl) ⟨1795175, by rfl⟩ : syracuseStep 2393567 = 3590351) B3590351
theorem B5113327 : Blo 1594996 5113327 := bstep (se 1 (by rfl) ⟨3834995, by rfl⟩ : syracuseStep 5113327 = 7669991) B7669991
theorem B6473209 : Blo 1594996 6473209 := bstep (se 2 (by rfl) ⟨2427453, by rfl⟩ : syracuseStep 6473209 = 4854907) B4854907
theorem B3409499 : Blo 1594996 3409499 := bstep (se 1 (by rfl) ⟨2557124, by rfl⟩ : syracuseStep 3409499 = 5114249) B5114249
theorem B3589775 : Blo 1594996 3589775 := bstep (se 1 (by rfl) ⟨2692331, by rfl⟩ : syracuseStep 3589775 = 5384663) B5384663
theorem B2393831 : Blo 1594996 2393831 := bstep (se 1 (by rfl) ⟨1795373, by rfl⟩ : syracuseStep 2393831 = 3590747) B3590747
theorem B3590099 : Blo 1594996 3590099 := bstep (se 1 (by rfl) ⟨2692574, by rfl⟩ : syracuseStep 3590099 = 5385149) B5385149
theorem B7669799 : Blo 1594996 7669799 := bstep (se 1 (by rfl) ⟨5752349, by rfl⟩ : syracuseStep 7669799 = 11504699) B11504699
theorem B12937267 : Blo 1594996 12937267 := bstep (se 1 (by rfl) ⟨9702950, by rfl⟩ : syracuseStep 12937267 = 19405901) B19405901
theorem B12118409 : Blo 1594996 12118409 := bstep (se 2 (by rfl) ⟨4544403, by rfl⟩ : syracuseStep 12118409 = 9088807) B9088807
theorem B6056441 : Blo 1594996 6056441 := bstep (se 2 (by rfl) ⟨2271165, by rfl⟩ : syracuseStep 6056441 = 4542331) B4542331
theorem B2394617 : Blo 1594996 2394617 := bstep (se 2 (by rfl) ⟨897981, by rfl⟩ : syracuseStep 2394617 = 1795963) B1795963
theorem B2394665 : Blo 1594996 2394665 := bstep (se 2 (by rfl) ⟨897999, by rfl⟩ : syracuseStep 2394665 = 1795999) B1795999
theorem B45992609 : Blo 1594996 45992609 := bstep (se 2 (by rfl) ⟨17247228, by rfl⟩ : syracuseStep 45992609 = 34494457) B34494457
theorem B6056927 : Blo 1594996 6056927 := bstep (se 1 (by rfl) ⟨4542695, by rfl⟩ : syracuseStep 6056927 = 9085391) B9085391
theorem B13626377 : Blo 1594996 13626377 := bstep (se 2 (by rfl) ⟨5109891, by rfl⟩ : syracuseStep 13626377 = 10219783) B10219783
theorem B4041839 : Blo 1594996 4041839 := bstep (se 1 (by rfl) ⟨3031379, by rfl⟩ : syracuseStep 4041839 = 6062759) B6062759
theorem B27635107 : Blo 1594996 27635107 := bstep (se 1 (by rfl) ⟨20726330, by rfl⟩ : syracuseStep 27635107 = 41452661) B41452661
theorem B2018783 : Blo 1594996 2018783 := bstep (se 1 (by rfl) ⟨1514087, by rfl⟩ : syracuseStep 2018783 = 3028175) B3028175
theorem B3591791 : Blo 1594996 3591791 := bstep (se 1 (by rfl) ⟨2693843, by rfl⟩ : syracuseStep 3591791 = 5387687) B5387687
theorem B8081207 : Blo 1594996 8081207 := bstep (se 1 (by rfl) ⟨6060905, by rfl⟩ : syracuseStep 8081207 = 12121811) B12121811
theorem B5386067 : Blo 1594996 5386067 := bstep (se 1 (by rfl) ⟨4039550, by rfl⟩ : syracuseStep 5386067 = 8079101) B8079101
theorem B7778297 : Blo 1594996 7778297 := bstep (se 2 (by rfl) ⟨2916861, by rfl⟩ : syracuseStep 7778297 = 5833723) B5833723
theorem B818565259 : Blo 1594996 818565259 := bstep (se 1 (by rfl) ⟨613923944, by rfl⟩ : syracuseStep 818565259 = 1227847889) B1227847889
theorem B2273455 : Blo 1594996 2273455 := bstep (se 1 (by rfl) ⟨1705091, by rfl⟩ : syracuseStep 2273455 = 3410183) B3410183
theorem B13635809 : Blo 1594996 13635809 := bstep (se 2 (by rfl) ⟨5113428, by rfl⟩ : syracuseStep 13635809 = 10226857) B10226857
theorem B16388513 : Blo 1594996 16388513 := bstep (se 2 (by rfl) ⟨6145692, by rfl⟩ : syracuseStep 16388513 = 12291385) B12291385
theorem B5755319 : Blo 1594996 5755319 := bstep (se 1 (by rfl) ⟨4316489, by rfl⟩ : syracuseStep 5755319 = 8632979) B8632979
theorem B7778749 : Blo 1594996 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B5387039 : Blo 1594996 5387039 := bstep (se 1 (by rfl) ⟨4040279, by rfl⟩ : syracuseStep 5387039 = 8080559) B8080559
theorem B27276263 : Blo 1594996 27276263 := bstep (se 1 (by rfl) ⟨20457197, by rfl⟩ : syracuseStep 27276263 = 40914395) B40914395
theorem B5387795 : Blo 1594996 5387795 := bstep (se 1 (by rfl) ⟨4040846, by rfl⟩ : syracuseStep 5387795 = 8081693) B8081693
theorem B896595641 : Blo 1594996 896595641 := bstep (se 2 (by rfl) ⟨336223365, by rfl⟩ : syracuseStep 896595641 = 672446731) B672446731
theorem B1595263 : Blo 1594996 1595263 := bstep (se 1 (by rfl) ⟨1196447, by rfl⟩ : syracuseStep 1595263 = 2392895) B2392895
theorem B3028927 : Blo 1594996 3028927 := bstep (se 1 (by rfl) ⟨2271695, by rfl⟩ : syracuseStep 3028927 = 4543391) B4543391
theorem B1595359 : Blo 1594996 1595359 := bstep (se 1 (by rfl) ⟨1196519, by rfl⟩ : syracuseStep 1595359 = 2393039) B2393039
theorem B6060041 : Blo 1594996 6060041 := bstep (se 2 (by rfl) ⟨2272515, by rfl⟩ : syracuseStep 6060041 = 4545031) B4545031
theorem B1595419 : Blo 1594996 1595419 := bstep (se 1 (by rfl) ⟨1196564, by rfl⟩ : syracuseStep 1595419 = 2393129) B2393129
theorem B1595439 : Blo 1594996 1595439 := bstep (se 1 (by rfl) ⟨1196579, by rfl⟩ : syracuseStep 1595439 = 2393159) B2393159
theorem B1595559 : Blo 1594996 1595559 := bstep (se 1 (by rfl) ⟨1196669, by rfl⟩ : syracuseStep 1595559 = 2393339) B2393339
theorem B7665839 : Blo 1594996 7665839 := bstep (se 1 (by rfl) ⟨5749379, by rfl⟩ : syracuseStep 7665839 = 11498759) B11498759
theorem B7674065 : Blo 1594996 7674065 := bstep (se 2 (by rfl) ⟨2877774, by rfl⟩ : syracuseStep 7674065 = 5755549) B5755549
theorem B13818185 : Blo 1594996 13818185 := bstep (se 2 (by rfl) ⟨5181819, by rfl⟩ : syracuseStep 13818185 = 10363639) B10363639
theorem B1595751 : Blo 1594996 1595751 := bstep (se 1 (by rfl) ⟨1196813, by rfl⟩ : syracuseStep 1595751 = 2393627) B2393627
theorem B2693479 : Blo 1594996 2693479 := bstep (se 1 (by rfl) ⟨2020109, by rfl⟩ : syracuseStep 2693479 = 4040219) B4040219
theorem B1596007 : Blo 1594996 1596007 := bstep (se 1 (by rfl) ⟨1197005, by rfl⟩ : syracuseStep 1596007 = 2394011) B2394011
theorem B1596031 : Blo 1594996 1596031 := bstep (se 1 (by rfl) ⟨1197023, by rfl⟩ : syracuseStep 1596031 = 2394047) B2394047
theorem B3234529 : Blo 1594996 3234529 := bstep (se 2 (by rfl) ⟨1212948, by rfl⟩ : syracuseStep 3234529 = 2425897) B2425897
theorem B1596447 : Blo 1594996 1596447 := bstep (se 1 (by rfl) ⟨1197335, by rfl⟩ : syracuseStep 1596447 = 2394671) B2394671
theorem B1596527 : Blo 1594996 1596527 := bstep (se 1 (by rfl) ⟨1197395, by rfl⟩ : syracuseStep 1596527 = 2394791) B2394791
theorem B11066503 : Blo 1594996 11066503 := bstep (se 1 (by rfl) ⟨8299877, by rfl⟩ : syracuseStep 11066503 = 16599755) B16599755
theorem B1596571 : Blo 1594996 1596571 := bstep (se 1 (by rfl) ⟨1197428, by rfl⟩ : syracuseStep 1596571 = 2394857) B2394857
theorem B1596575 : Blo 1594996 1596575 := bstep (se 1 (by rfl) ⟨1197431, by rfl⟩ : syracuseStep 1596575 = 2394863) B2394863
theorem B11508905 : Blo 1594996 11508905 := bstep (se 2 (by rfl) ⟨4315839, by rfl⟩ : syracuseStep 11508905 = 8631679) B8631679
theorem B5610671 : Blo 1594996 5610671 := bstep (se 1 (by rfl) ⟨4208003, by rfl⟩ : syracuseStep 5610671 = 8416007) B8416007
theorem B1596607 : Blo 1594996 1596607 := bstep (se 1 (by rfl) ⟨1197455, by rfl⟩ : syracuseStep 1596607 = 2394911) B2394911
theorem B3407159 : Blo 1594996 3407159 := bstep (se 1 (by rfl) ⟨2555369, by rfl⟩ : syracuseStep 3407159 = 5110739) B5110739
theorem B1596827 : Blo 1594996 1596827 := bstep (se 1 (by rfl) ⟨1197620, by rfl⟩ : syracuseStep 1596827 = 2395241) B2395241
theorem B3407339 : Blo 1594996 3407339 := bstep (se 1 (by rfl) ⟨2555504, by rfl⟩ : syracuseStep 3407339 = 5111009) B5111009
theorem B1596911 : Blo 1594996 1596911 := bstep (se 1 (by rfl) ⟨1197683, by rfl⟩ : syracuseStep 1596911 = 2395367) B2395367
theorem B12123755 : Blo 1594996 12123755 := bstep (se 1 (by rfl) ⟨9092816, by rfl⟩ : syracuseStep 12123755 = 18185633) B18185633
theorem B27639539 : Blo 1594996 27639539 := bstep (se 1 (by rfl) ⟨20729654, by rfl⟩ : syracuseStep 27639539 = 41459309) B41459309
theorem B18169595 : Blo 1594996 18169595 := bstep (se 1 (by rfl) ⟨13627196, by rfl⟩ : syracuseStep 18169595 = 27254393) B27254393
theorem B65527613 : Blo 1594996 65527613 := bstep (se 3 (by rfl) ⟨12286427, by rfl⟩ : syracuseStep 65527613 = 24572855) B24572855
theorem B4038619 : Blo 1594996 4038619 := bstep (se 1 (by rfl) ⟨3028964, by rfl⟩ : syracuseStep 4038619 = 6057929) B6057929
theorem B1091420345 : Blo 1594996 1091420345 := bstep (se 2 (by rfl) ⟨409282629, by rfl⟩ : syracuseStep 1091420345 = 818565259) B818565259
theorem B3031273 : Blo 1594996 3031273 := bstep (se 2 (by rfl) ⟨1136727, by rfl⟩ : syracuseStep 3031273 = 2273455) B2273455
theorem B10371665 : Blo 1594996 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B3588767 : Blo 1594996 3588767 := bstep (se 1 (by rfl) ⟨2691575, by rfl⟩ : syracuseStep 3588767 = 5383151) B5383151
theorem B3834611 : Blo 1594996 3834611 := bstep (se 1 (by rfl) ⟨2875958, by rfl⟩ : syracuseStep 3834611 = 5751917) B5751917
theorem B2392991 : Blo 1594996 2392991 := bstep (se 1 (by rfl) ⟨1794743, by rfl⟩ : syracuseStep 2392991 = 3589487) B3589487
theorem B2393183 : Blo 1594996 2393183 := bstep (se 1 (by rfl) ⟨1794887, by rfl⟩ : syracuseStep 2393183 = 3589775) B3589775
theorem B597730427 : Blo 1594996 597730427 := bstep (se 1 (by rfl) ⟨448297820, by rfl⟩ : syracuseStep 597730427 = 896595641) B896595641
theorem B5383421 : Blo 1594996 5383421 := bstep (se 3 (by rfl) ⟨1009391, by rfl⟩ : syracuseStep 5383421 = 2018783) B2018783
theorem B2393399 : Blo 1594996 2393399 := bstep (se 1 (by rfl) ⟨1795049, by rfl⟩ : syracuseStep 2393399 = 3590099) B3590099
theorem B4040027 : Blo 1594996 4040027 := bstep (se 1 (by rfl) ⟨3030020, by rfl⟩ : syracuseStep 4040027 = 6060041) B6060041
theorem B5113199 : Blo 1594996 5113199 := bstep (se 1 (by rfl) ⟨3834899, by rfl⟩ : syracuseStep 5113199 = 7669799) B7669799
theorem B14755337 : Blo 1594996 14755337 := bstep (se 2 (by rfl) ⟨5533251, by rfl⟩ : syracuseStep 14755337 = 11066503) B11066503
theorem B8078939 : Blo 1594996 8078939 := bstep (se 1 (by rfl) ⟨6059204, by rfl⟩ : syracuseStep 8078939 = 12118409) B12118409
theorem B6817769 : Blo 1594996 6817769 := bstep (se 2 (by rfl) ⟨2556663, by rfl⟩ : syracuseStep 6817769 = 5113327) B5113327
theorem B2271439 : Blo 1594996 2271439 := bstep (se 1 (by rfl) ⟨1703579, by rfl⟩ : syracuseStep 2271439 = 3407159) B3407159
theorem B2271559 : Blo 1594996 2271559 := bstep (se 1 (by rfl) ⟨1703669, by rfl⟩ : syracuseStep 2271559 = 3407339) B3407339
theorem B2394527 : Blo 1594996 2394527 := bstep (se 1 (by rfl) ⟨1795895, by rfl⟩ : syracuseStep 2394527 = 3591791) B3591791
theorem B18426359 : Blo 1594996 18426359 := bstep (se 1 (by rfl) ⟨13819769, by rfl⟩ : syracuseStep 18426359 = 27639539) B27639539
theorem B3590711 : Blo 1594996 3590711 := bstep (se 1 (by rfl) ⟨2693033, by rfl⟩ : syracuseStep 3590711 = 5386067) B5386067
theorem B5384825 : Blo 1594996 5384825 := bstep (se 2 (by rfl) ⟨2019309, by rfl⟩ : syracuseStep 5384825 = 4038619) B4038619
theorem B5384987 : Blo 1594996 5384987 := bstep (se 1 (by rfl) ⟨4038740, by rfl⟩ : syracuseStep 5384987 = 8077481) B8077481
theorem B3836879 : Blo 1594996 3836879 := bstep (se 1 (by rfl) ⟨2877659, by rfl⟩ : syracuseStep 3836879 = 5755319) B5755319
theorem B30690413 : Blo 1594996 30690413 := bstep (se 3 (by rfl) ⟨5754452, by rfl⟩ : syracuseStep 30690413 = 11508905) B11508905
theorem B3591305 : Blo 1594996 3591305 := bstep (se 2 (by rfl) ⟨1346739, by rfl⟩ : syracuseStep 3591305 = 2693479) B2693479
theorem B3591359 : Blo 1594996 3591359 := bstep (se 1 (by rfl) ⟨2693519, by rfl⟩ : syracuseStep 3591359 = 5387039) B5387039
theorem B65547467 : Blo 1594996 65547467 := bstep (se 1 (by rfl) ⟨49160600, by rfl⟩ : syracuseStep 65547467 = 98321201) B98321201
theorem B2157823 : Blo 1594996 2157823 := bstep (se 1 (by rfl) ⟨1618367, by rfl⟩ : syracuseStep 2157823 = 3236735) B3236735
theorem B4042345 : Blo 1594996 4042345 := bstep (se 2 (by rfl) ⟨1515879, by rfl⟩ : syracuseStep 4042345 = 3031759) B3031759
theorem B4312705 : Blo 1594996 4312705 := bstep (se 2 (by rfl) ⟨1617264, by rfl⟩ : syracuseStep 4312705 = 3234529) B3234529
theorem B3591863 : Blo 1594996 3591863 := bstep (se 1 (by rfl) ⟨2693897, by rfl⟩ : syracuseStep 3591863 = 5387795) B5387795
theorem B5116043 : Blo 1594996 5116043 := bstep (se 1 (by rfl) ⟨3837032, by rfl⟩ : syracuseStep 5116043 = 7674065) B7674065
theorem B9212123 : Blo 1594996 9212123 := bstep (se 1 (by rfl) ⟨6909092, by rfl⟩ : syracuseStep 9212123 = 13818185) B13818185
theorem B8630945 : Blo 1594996 8630945 := bstep (se 2 (by rfl) ⟨3236604, by rfl⟩ : syracuseStep 8630945 = 6473209) B6473209
theorem B3740447 : Blo 1594996 3740447 := bstep (se 1 (by rfl) ⟨2805335, by rfl⟩ : syracuseStep 3740447 = 5610671) B5610671
theorem B8082503 : Blo 1594996 8082503 := bstep (se 1 (by rfl) ⟨6061877, by rfl⟩ : syracuseStep 8082503 = 12123755) B12123755
theorem B12113063 : Blo 1594996 12113063 := bstep (se 1 (by rfl) ⟨9084797, by rfl⟩ : syracuseStep 12113063 = 18169595) B18169595
theorem B5387471 : Blo 1594996 5387471 := bstep (se 1 (by rfl) ⟨4040603, by rfl⟩ : syracuseStep 5387471 = 8081207) B8081207
theorem B43685075 : Blo 1594996 43685075 := bstep (se 1 (by rfl) ⟨32763806, by rfl⟩ : syracuseStep 43685075 = 65527613) B65527613
theorem B17249689 : Blo 1594996 17249689 := bstep (se 2 (by rfl) ⟨6468633, by rfl⟩ : syracuseStep 17249689 = 12937267) B12937267
theorem B9090539 : Blo 1594996 9090539 := bstep (se 1 (by rfl) ⟨6817904, by rfl⟩ : syracuseStep 9090539 = 13635809) B13635809
theorem B10925675 : Blo 1594996 10925675 := bstep (se 1 (by rfl) ⟨8194256, by rfl⟩ : syracuseStep 10925675 = 16388513) B16388513
theorem B18184175 : Blo 1594996 18184175 := bstep (se 1 (by rfl) ⟨13638131, by rfl⟩ : syracuseStep 18184175 = 27276263) B27276263
theorem B8083475 : Blo 1594996 8083475 := bstep (se 1 (by rfl) ⟨6062606, by rfl⟩ : syracuseStep 8083475 = 12125213) B12125213
theorem B12949723 : Blo 1594996 12949723 := bstep (se 1 (by rfl) ⟨9712292, by rfl⟩ : syracuseStep 12949723 = 19424585) B19424585
theorem B1595631 : Blo 1594996 1595631 := bstep (se 1 (by rfl) ⟨1196723, by rfl⟩ : syracuseStep 1595631 = 2393447) B2393447
theorem B1595711 : Blo 1594996 1595711 := bstep (se 1 (by rfl) ⟨1196783, by rfl⟩ : syracuseStep 1595711 = 2393567) B2393567
theorem B1595887 : Blo 1594996 1595887 := bstep (se 1 (by rfl) ⟨1196915, by rfl⟩ : syracuseStep 1595887 = 2393831) B2393831
theorem B4545305 : Blo 1594996 4545305 := bstep (se 2 (by rfl) ⟨1704489, by rfl⟩ : syracuseStep 4545305 = 3408979) B3408979
theorem B5110559 : Blo 1594996 5110559 := bstep (se 1 (by rfl) ⟨3832919, by rfl⟩ : syracuseStep 5110559 = 7665839) B7665839
theorem B9091997 : Blo 1594996 9091997 := bstep (se 3 (by rfl) ⟨1704749, by rfl⟩ : syracuseStep 9091997 = 3409499) B3409499
theorem B4037627 : Blo 1594996 4037627 := bstep (se 1 (by rfl) ⟨3028220, by rfl⟩ : syracuseStep 4037627 = 6056441) B6056441
theorem B1596411 : Blo 1594996 1596411 := bstep (se 1 (by rfl) ⟨1197308, by rfl⟩ : syracuseStep 1596411 = 2394617) B2394617
theorem B1596443 : Blo 1594996 1596443 := bstep (se 1 (by rfl) ⟨1197332, by rfl⟩ : syracuseStep 1596443 = 2394665) B2394665
theorem B30661739 : Blo 1594996 30661739 := bstep (se 1 (by rfl) ⟨22996304, by rfl⟩ : syracuseStep 30661739 = 45992609) B45992609
theorem B36846809 : Blo 1594996 36846809 := bstep (se 2 (by rfl) ⟨13817553, by rfl⟩ : syracuseStep 36846809 = 27635107) B27635107
theorem B4037951 : Blo 1594996 4037951 := bstep (se 1 (by rfl) ⟨3028463, by rfl⟩ : syracuseStep 4037951 = 6056927) B6056927
theorem B9084251 : Blo 1594996 9084251 := bstep (se 1 (by rfl) ⟨6813188, by rfl⟩ : syracuseStep 9084251 = 13626377) B13626377
theorem B2694559 : Blo 1594996 2694559 := bstep (se 1 (by rfl) ⟨2020919, by rfl⟩ : syracuseStep 2694559 = 4041839) B4041839
theorem B4038569 : Blo 1594996 4038569 := bstep (se 2 (by rfl) ⟨1514463, by rfl⟩ : syracuseStep 4038569 = 3028927) B3028927
theorem B5185531 : Blo 1594996 5185531 := bstep (se 1 (by rfl) ⟨3889148, by rfl⟩ : syracuseStep 5185531 = 7778297) B7778297
theorem B727613563 : Blo 1594996 727613563 := bstep (se 1 (by rfl) ⟨545710172, by rfl⟩ : syracuseStep 727613563 = 1091420345) B1091420345
theorem B6914443 : Blo 1594996 6914443 := bstep (se 1 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 6914443 = 10371665) B10371665
theorem B2392511 : Blo 1594996 2392511 := bstep (se 1 (by rfl) ⟨1794383, by rfl⟩ : syracuseStep 2392511 = 3588767) B3588767
theorem B2556407 : Blo 1594996 2556407 := bstep (se 1 (by rfl) ⟨1917305, by rfl⟩ : syracuseStep 2556407 = 3834611) B3834611
theorem B29123383 : Blo 1594996 29123383 := bstep (se 1 (by rfl) ⟨21842537, by rfl⟩ : syracuseStep 29123383 = 43685075) B43685075
theorem B3588947 : Blo 1594996 3588947 := bstep (se 1 (by rfl) ⟨2691710, by rfl⟩ : syracuseStep 3588947 = 5383421) B5383421
theorem B3408799 : Blo 1594996 3408799 := bstep (se 1 (by rfl) ⟨2556599, by rfl⟩ : syracuseStep 3408799 = 5113199) B5113199
theorem B7283783 : Blo 1594996 7283783 := bstep (se 1 (by rfl) ⟨5462837, by rfl⟩ : syracuseStep 7283783 = 10925675) B10925675
theorem B2393807 : Blo 1594996 2393807 := bstep (se 1 (by rfl) ⟨1795355, by rfl⟩ : syracuseStep 2393807 = 3590711) B3590711
theorem B3589883 : Blo 1594996 3589883 := bstep (se 1 (by rfl) ⟨2692412, by rfl⟩ : syracuseStep 3589883 = 5384825) B5384825
theorem B3589991 : Blo 1594996 3589991 := bstep (se 1 (by rfl) ⟨2692493, by rfl⟩ : syracuseStep 3589991 = 5384987) B5384987
theorem B2557919 : Blo 1594996 2557919 := bstep (se 1 (by rfl) ⟨1918439, by rfl⟩ : syracuseStep 2557919 = 3836879) B3836879
theorem B20441159 : Blo 1594996 20441159 := bstep (se 1 (by rfl) ⟨15330869, by rfl⟩ : syracuseStep 20441159 = 30661739) B30661739
theorem B2394203 : Blo 1594996 2394203 := bstep (se 1 (by rfl) ⟨1795652, by rfl⟩ : syracuseStep 2394203 = 3591305) B3591305
theorem B2394239 : Blo 1594996 2394239 := bstep (se 1 (by rfl) ⟨1795679, by rfl⟩ : syracuseStep 2394239 = 3591359) B3591359
theorem B91998341 : Blo 1594996 91998341 := bstep (se 4 (by rfl) ⟨8624844, by rfl⟩ : syracuseStep 91998341 = 17249689) B17249689
theorem B43698311 : Blo 1594996 43698311 := bstep (se 1 (by rfl) ⟨32773733, by rfl⟩ : syracuseStep 43698311 = 65547467) B65547467
theorem B6056167 : Blo 1594996 6056167 := bstep (se 1 (by rfl) ⟨4542125, by rfl⟩ : syracuseStep 6056167 = 9084251) B9084251
theorem B2394575 : Blo 1594996 2394575 := bstep (se 1 (by rfl) ⟨1795931, by rfl⟩ : syracuseStep 2394575 = 3591863) B3591863
theorem B3410695 : Blo 1594996 3410695 := bstep (se 1 (by rfl) ⟨2558021, by rfl⟩ : syracuseStep 3410695 = 5116043) B5116043
theorem B4041697 : Blo 1594996 4041697 := bstep (se 2 (by rfl) ⟨1515636, by rfl⟩ : syracuseStep 4041697 = 3031273) B3031273
theorem B5753963 : Blo 1594996 5753963 := bstep (se 1 (by rfl) ⟨4315472, by rfl⟩ : syracuseStep 5753963 = 8630945) B8630945
theorem B2493631 : Blo 1594996 2493631 := bstep (se 1 (by rfl) ⟨1870223, by rfl⟩ : syracuseStep 2493631 = 3740447) B3740447
theorem B398486951 : Blo 1594996 398486951 := bstep (se 1 (by rfl) ⟨298865213, by rfl⟩ : syracuseStep 398486951 = 597730427) B597730427
theorem B3591647 : Blo 1594996 3591647 := bstep (se 1 (by rfl) ⟨2693735, by rfl⟩ : syracuseStep 3591647 = 5387471) B5387471
theorem B5385959 : Blo 1594996 5385959 := bstep (se 1 (by rfl) ⟨4039469, by rfl⟩ : syracuseStep 5385959 = 8078939) B8078939
theorem B12284239 : Blo 1594996 12284239 := bstep (se 1 (by rfl) ⟨9213179, by rfl⟩ : syracuseStep 12284239 = 18426359) B18426359
theorem B3592745 : Blo 1594996 3592745 := bstep (se 2 (by rfl) ⟨1347279, by rfl⟩ : syracuseStep 3592745 = 2694559) B2694559
theorem B2691751 : Blo 1594996 2691751 := bstep (se 1 (by rfl) ⟨2018813, by rfl⟩ : syracuseStep 2691751 = 4037627) B4037627
theorem B20460275 : Blo 1594996 20460275 := bstep (se 1 (by rfl) ⟨15345206, by rfl⟩ : syracuseStep 20460275 = 30690413) B30690413
theorem B24564539 : Blo 1594996 24564539 := bstep (se 1 (by rfl) ⟨18423404, by rfl⟩ : syracuseStep 24564539 = 36846809) B36846809
theorem B2691967 : Blo 1594996 2691967 := bstep (se 1 (by rfl) ⟨2018975, by rfl⟩ : syracuseStep 2691967 = 4037951) B4037951
theorem B2692379 : Blo 1594996 2692379 := bstep (se 1 (by rfl) ⟨2019284, by rfl⟩ : syracuseStep 2692379 = 4038569) B4038569
theorem B6141415 : Blo 1594996 6141415 := bstep (se 1 (by rfl) ⟨4606061, by rfl⟩ : syracuseStep 6141415 = 9212123) B9212123
theorem B3028585 : Blo 1594996 3028585 := bstep (se 2 (by rfl) ⟨1135719, by rfl⟩ : syracuseStep 3028585 = 2271439) B2271439
theorem B17266297 : Blo 1594996 17266297 := bstep (se 2 (by rfl) ⟨6474861, by rfl⟩ : syracuseStep 17266297 = 12949723) B12949723
theorem B3028745 : Blo 1594996 3028745 := bstep (se 2 (by rfl) ⟨1135779, by rfl⟩ : syracuseStep 3028745 = 2271559) B2271559
theorem B1595327 : Blo 1594996 1595327 := bstep (se 1 (by rfl) ⟨1196495, by rfl⟩ : syracuseStep 1595327 = 2392991) B2392991
theorem B5388335 : Blo 1594996 5388335 := bstep (se 1 (by rfl) ⟨4041251, by rfl⟩ : syracuseStep 5388335 = 8082503) B8082503
theorem B1595455 : Blo 1594996 1595455 := bstep (se 1 (by rfl) ⟨1196591, by rfl⟩ : syracuseStep 1595455 = 2393183) B2393183
theorem B8075375 : Blo 1594996 8075375 := bstep (se 1 (by rfl) ⟨6056531, by rfl⟩ : syracuseStep 8075375 = 12113063) B12113063
theorem B1595599 : Blo 1594996 1595599 := bstep (se 1 (by rfl) ⟨1196699, by rfl⟩ : syracuseStep 1595599 = 2393399) B2393399
theorem B2693351 : Blo 1594996 2693351 := bstep (se 1 (by rfl) ⟨2020013, by rfl⟩ : syracuseStep 2693351 = 4040027) B4040027
theorem B6060359 : Blo 1594996 6060359 := bstep (se 1 (by rfl) ⟨4545269, by rfl⟩ : syracuseStep 6060359 = 9090539) B9090539
theorem B9836891 : Blo 1594996 9836891 := bstep (se 1 (by rfl) ⟨7377668, by rfl⟩ : syracuseStep 9836891 = 14755337) B14755337
theorem B4545179 : Blo 1594996 4545179 := bstep (se 1 (by rfl) ⟨3408884, by rfl⟩ : syracuseStep 4545179 = 6817769) B6817769
theorem B12122783 : Blo 1594996 12122783 := bstep (se 1 (by rfl) ⟨9092087, by rfl⟩ : syracuseStep 12122783 = 18184175) B18184175
theorem B11508389 : Blo 1594996 11508389 := bstep (se 4 (by rfl) ⟨1078911, by rfl⟩ : syracuseStep 11508389 = 2157823) B2157823
theorem B5388983 : Blo 1594996 5388983 := bstep (se 1 (by rfl) ⟨4041737, by rfl⟩ : syracuseStep 5388983 = 8083475) B8083475
theorem B1596351 : Blo 1594996 1596351 := bstep (se 1 (by rfl) ⟨1197263, by rfl⟩ : syracuseStep 1596351 = 2394527) B2394527
theorem B3030203 : Blo 1594996 3030203 := bstep (se 1 (by rfl) ⟨2272652, by rfl⟩ : syracuseStep 3030203 = 4545305) B4545305
theorem B3407039 : Blo 1594996 3407039 := bstep (se 1 (by rfl) ⟨2555279, by rfl⟩ : syracuseStep 3407039 = 5110559) B5110559
theorem B6061331 : Blo 1594996 6061331 := bstep (se 1 (by rfl) ⟨4545998, by rfl⟩ : syracuseStep 6061331 = 9091997) B9091997
theorem B5389793 : Blo 1594996 5389793 := bstep (se 2 (by rfl) ⟨2021172, by rfl⟩ : syracuseStep 5389793 = 4042345) B4042345
theorem B5750273 : Blo 1594996 5750273 := bstep (se 2 (by rfl) ⟨2156352, by rfl⟩ : syracuseStep 5750273 = 4312705) B4312705
theorem B6914041 : Blo 1594996 6914041 := bstep (se 2 (by rfl) ⟨2592765, by rfl⟩ : syracuseStep 6914041 = 5185531) B5185531
theorem B19423421 : Blo 1594996 19423421 := bstep (se 3 (by rfl) ⟨3641891, by rfl⟩ : syracuseStep 19423421 = 7283783) B7283783
theorem B15343901 : Blo 1594996 15343901 := bstep (se 3 (by rfl) ⟨2876981, by rfl⟩ : syracuseStep 15343901 = 5753963) B5753963
theorem B13640183 : Blo 1594996 13640183 := bstep (se 1 (by rfl) ⟨10230137, by rfl⟩ : syracuseStep 13640183 = 20460275) B20460275
theorem B16376359 : Blo 1594996 16376359 := bstep (se 1 (by rfl) ⟨12282269, by rfl⟩ : syracuseStep 16376359 = 24564539) B24564539
theorem B2392631 : Blo 1594996 2392631 := bstep (se 1 (by rfl) ⟨1794473, by rfl⟩ : syracuseStep 2392631 = 3588947) B3588947
theorem B1794919 : Blo 1594996 1794919 := bstep (se 1 (by rfl) ⟨1346189, by rfl⟩ : syracuseStep 1794919 = 2692379) B2692379
theorem B3589001 : Blo 1594996 3589001 := bstep (se 2 (by rfl) ⟨1345875, by rfl⟩ : syracuseStep 3589001 = 2691751) B2691751
theorem B4547593 : Blo 1594996 4547593 := bstep (se 2 (by rfl) ⟨1705347, by rfl⟩ : syracuseStep 4547593 = 3410695) B3410695
theorem B38831177 : Blo 1594996 38831177 := bstep (se 2 (by rfl) ⟨14561691, by rfl⟩ : syracuseStep 38831177 = 29123383) B29123383
theorem B2393255 : Blo 1594996 2393255 := bstep (se 1 (by rfl) ⟨1794941, by rfl⟩ : syracuseStep 2393255 = 3589883) B3589883
theorem B3589289 : Blo 1594996 3589289 := bstep (se 2 (by rfl) ⟨1345983, by rfl⟩ : syracuseStep 3589289 = 2691967) B2691967
theorem B2393327 : Blo 1594996 2393327 := bstep (se 1 (by rfl) ⟨1794995, by rfl⟩ : syracuseStep 2393327 = 3589991) B3589991
theorem B6817085 : Blo 1594996 6817085 := bstep (se 3 (by rfl) ⟨1278203, by rfl⟩ : syracuseStep 6817085 = 2556407) B2556407
theorem B5383583 : Blo 1594996 5383583 := bstep (se 1 (by rfl) ⟨4037687, by rfl⟩ : syracuseStep 5383583 = 8075375) B8075375
theorem B29132207 : Blo 1594996 29132207 := bstep (se 1 (by rfl) ⟨21849155, by rfl⟩ : syracuseStep 29132207 = 43698311) B43698311
theorem B1795567 : Blo 1594996 1795567 := bstep (se 1 (by rfl) ⟨1346675, by rfl⟩ : syracuseStep 1795567 = 2693351) B2693351
theorem B4040239 : Blo 1594996 4040239 := bstep (se 1 (by rfl) ⟨3030179, by rfl⟩ : syracuseStep 4040239 = 6060359) B6060359
theorem B2271359 : Blo 1594996 2271359 := bstep (se 1 (by rfl) ⟨1703519, by rfl⟩ : syracuseStep 2271359 = 3407039) B3407039
theorem B23021729 : Blo 1594996 23021729 := bstep (se 2 (by rfl) ⟨8633148, by rfl⟩ : syracuseStep 23021729 = 17266297) B17266297
theorem B4040887 : Blo 1594996 4040887 := bstep (se 1 (by rfl) ⟨3030665, by rfl⟩ : syracuseStep 4040887 = 6061331) B6061331
theorem B2394431 : Blo 1594996 2394431 := bstep (se 1 (by rfl) ⟨1795823, by rfl⟩ : syracuseStep 2394431 = 3591647) B3591647
theorem B3590639 : Blo 1594996 3590639 := bstep (se 1 (by rfl) ⟨2692979, by rfl⟩ : syracuseStep 3590639 = 5385959) B5385959
theorem B36874885 : Blo 1594996 36874885 := bstep (se 4 (by rfl) ⟨3457020, by rfl⟩ : syracuseStep 36874885 = 6914041) B6914041
theorem B2395163 : Blo 1594996 2395163 := bstep (se 1 (by rfl) ⟨1796372, by rfl⟩ : syracuseStep 2395163 = 3592745) B3592745
theorem B16378985 : Blo 1594996 16378985 := bstep (se 2 (by rfl) ⟨6142119, by rfl⟩ : syracuseStep 16378985 = 12284239) B12284239
theorem B9219257 : Blo 1594996 9219257 := bstep (se 2 (by rfl) ⟨3457221, by rfl⟩ : syracuseStep 9219257 = 6914443) B6914443
theorem B13299365 : Blo 1594996 13299365 := bstep (se 4 (by rfl) ⟨1246815, by rfl⟩ : syracuseStep 13299365 = 2493631) B2493631
theorem B2019163 : Blo 1594996 2019163 := bstep (se 1 (by rfl) ⟨1514372, by rfl⟩ : syracuseStep 2019163 = 3028745) B3028745
theorem B3592223 : Blo 1594996 3592223 := bstep (se 1 (by rfl) ⟨2694167, by rfl⟩ : syracuseStep 3592223 = 5388335) B5388335
theorem B13627439 : Blo 1594996 13627439 := bstep (se 1 (by rfl) ⟨10220579, by rfl⟩ : syracuseStep 13627439 = 20441159) B20441159
theorem B6557927 : Blo 1594996 6557927 := bstep (se 1 (by rfl) ⟨4918445, by rfl⟩ : syracuseStep 6557927 = 9836891) B9836891
theorem B8081855 : Blo 1594996 8081855 := bstep (se 1 (by rfl) ⟨6061391, by rfl⟩ : syracuseStep 8081855 = 12122783) B12122783
theorem B7672259 : Blo 1594996 7672259 := bstep (se 1 (by rfl) ⟨5754194, by rfl⟩ : syracuseStep 7672259 = 11508389) B11508389
theorem B3592655 : Blo 1594996 3592655 := bstep (se 1 (by rfl) ⟨2694491, by rfl⟩ : syracuseStep 3592655 = 5388983) B5388983
theorem B8188553 : Blo 1594996 8188553 := bstep (se 2 (by rfl) ⟨3070707, by rfl⟩ : syracuseStep 8188553 = 6141415) B6141415
theorem B2020135 : Blo 1594996 2020135 := bstep (se 1 (by rfl) ⟨1515101, by rfl⟩ : syracuseStep 2020135 = 3030203) B3030203
theorem B3593195 : Blo 1594996 3593195 := bstep (se 1 (by rfl) ⟨2694896, by rfl⟩ : syracuseStep 3593195 = 5389793) B5389793
theorem B6821117 : Blo 1594996 6821117 := bstep (se 3 (by rfl) ⟨1278959, by rfl⟩ : syracuseStep 6821117 = 2557919) B2557919
theorem B970151417 : Blo 1594996 970151417 := bstep (se 2 (by rfl) ⟨363806781, by rfl⟩ : syracuseStep 970151417 = 727613563) B727613563
theorem B1595007 : Blo 1594996 1595007 := bstep (se 1 (by rfl) ⟨1196255, by rfl⟩ : syracuseStep 1595007 = 2392511) B2392511
theorem B8074889 : Blo 1594996 8074889 := bstep (se 2 (by rfl) ⟨3028083, by rfl⟩ : syracuseStep 8074889 = 6056167) B6056167
theorem B1595871 : Blo 1594996 1595871 := bstep (se 1 (by rfl) ⟨1196903, by rfl⟩ : syracuseStep 1595871 = 2393807) B2393807
theorem B4545065 : Blo 1594996 4545065 := bstep (se 2 (by rfl) ⟨1704399, by rfl⟩ : syracuseStep 4545065 = 3408799) B3408799
theorem B5388929 : Blo 1594996 5388929 := bstep (se 2 (by rfl) ⟨2020848, by rfl⟩ : syracuseStep 5388929 = 4041697) B4041697
theorem B1596135 : Blo 1594996 1596135 := bstep (se 1 (by rfl) ⟨1197101, by rfl⟩ : syracuseStep 1596135 = 2394203) B2394203
theorem B1596159 : Blo 1594996 1596159 := bstep (se 1 (by rfl) ⟨1197119, by rfl⟩ : syracuseStep 1596159 = 2394239) B2394239
theorem B61332227 : Blo 1594996 61332227 := bstep (se 1 (by rfl) ⟨45999170, by rfl⟩ : syracuseStep 61332227 = 91998341) B91998341
theorem B1596383 : Blo 1594996 1596383 := bstep (se 1 (by rfl) ⟨1197287, by rfl⟩ : syracuseStep 1596383 = 2394575) B2394575
theorem B3030119 : Blo 1594996 3030119 := bstep (se 1 (by rfl) ⟨2272589, by rfl⟩ : syracuseStep 3030119 = 4545179) B4545179
theorem B4038113 : Blo 1594996 4038113 := bstep (se 2 (by rfl) ⟨1514292, by rfl⟩ : syracuseStep 4038113 = 3028585) B3028585
theorem B265657967 : Blo 1594996 265657967 := bstep (se 1 (by rfl) ⟨199243475, by rfl⟩ : syracuseStep 265657967 = 398486951) B398486951
theorem B3833515 : Blo 1594996 3833515 := bstep (se 1 (by rfl) ⟨2875136, by rfl⟩ : syracuseStep 3833515 = 5750273) B5750273
theorem B9084959 : Blo 1594996 9084959 := bstep (se 1 (by rfl) ⟨6813719, by rfl⟩ : syracuseStep 9084959 = 13627439) B13627439
theorem B9093455 : Blo 1594996 9093455 := bstep (se 1 (by rfl) ⟨6820091, by rfl⟩ : syracuseStep 9093455 = 13640183) B13640183
theorem B2392667 : Blo 1594996 2392667 := bstep (se 1 (by rfl) ⟨1794500, by rfl⟩ : syracuseStep 2392667 = 3589001) B3589001
theorem B25887451 : Blo 1594996 25887451 := bstep (se 1 (by rfl) ⟨19415588, by rfl⟩ : syracuseStep 25887451 = 38831177) B38831177
theorem B2392859 : Blo 1594996 2392859 := bstep (se 1 (by rfl) ⟨1794644, by rfl⟩ : syracuseStep 2392859 = 3589289) B3589289
theorem B4547411 : Blo 1594996 4547411 := bstep (se 1 (by rfl) ⟨3410558, by rfl⟩ : syracuseStep 4547411 = 6821117) B6821117
theorem B3589055 : Blo 1594996 3589055 := bstep (se 1 (by rfl) ⟨2691791, by rfl⟩ : syracuseStep 3589055 = 5383583) B5383583
theorem B646767611 : Blo 1594996 646767611 := bstep (se 1 (by rfl) ⟨485075708, by rfl⟩ : syracuseStep 646767611 = 970151417) B970151417
theorem B5383259 : Blo 1594996 5383259 := bstep (se 1 (by rfl) ⟨4037444, by rfl⟩ : syracuseStep 5383259 = 8074889) B8074889
theorem B2393225 : Blo 1594996 2393225 := bstep (se 2 (by rfl) ⟨897459, by rfl⟩ : syracuseStep 2393225 = 1794919) B1794919
theorem B6063457 : Blo 1594996 6063457 := bstep (se 2 (by rfl) ⟨2273796, by rfl⟩ : syracuseStep 6063457 = 4547593) B4547593
theorem B2393759 : Blo 1594996 2393759 := bstep (se 1 (by rfl) ⟨1795319, by rfl⟩ : syracuseStep 2393759 = 3590639) B3590639
theorem B35464973 : Blo 1594996 35464973 := bstep (se 3 (by rfl) ⟨6649682, by rfl⟩ : syracuseStep 35464973 = 13299365) B13299365
theorem B40888151 : Blo 1594996 40888151 := bstep (se 1 (by rfl) ⟨30666113, by rfl⟩ : syracuseStep 40888151 = 61332227) B61332227
theorem B2394089 : Blo 1594996 2394089 := bstep (se 2 (by rfl) ⟨897783, by rfl⟩ : syracuseStep 2394089 = 1795567) B1795567
theorem B6146171 : Blo 1594996 6146171 := bstep (se 1 (by rfl) ⟨4609628, by rfl⟩ : syracuseStep 6146171 = 9219257) B9219257
theorem B177105311 : Blo 1594996 177105311 := bstep (se 1 (by rfl) ⟨132828983, by rfl⟩ : syracuseStep 177105311 = 265657967) B265657967
theorem B2394815 : Blo 1594996 2394815 := bstep (se 1 (by rfl) ⟨1796111, by rfl⟩ : syracuseStep 2394815 = 3592223) B3592223
theorem B5114839 : Blo 1594996 5114839 := bstep (se 1 (by rfl) ⟨3836129, by rfl⟩ : syracuseStep 5114839 = 7672259) B7672259
theorem B2395103 : Blo 1594996 2395103 := bstep (se 1 (by rfl) ⟨1796327, by rfl⟩ : syracuseStep 2395103 = 3592655) B3592655
theorem B6056957 : Blo 1594996 6056957 := bstep (se 3 (by rfl) ⟨1135679, by rfl⟩ : syracuseStep 6056957 = 2271359) B2271359
theorem B5459035 : Blo 1594996 5459035 := bstep (se 1 (by rfl) ⟨4094276, by rfl⟩ : syracuseStep 5459035 = 8188553) B8188553
theorem B2395463 : Blo 1594996 2395463 := bstep (se 1 (by rfl) ⟨1796597, by rfl⟩ : syracuseStep 2395463 = 3593195) B3593195
theorem B21835145 : Blo 1594996 21835145 := bstep (se 2 (by rfl) ⟨8188179, by rfl⟩ : syracuseStep 21835145 = 16376359) B16376359
theorem B15347819 : Blo 1594996 15347819 := bstep (se 1 (by rfl) ⟨11510864, by rfl⟩ : syracuseStep 15347819 = 23021729) B23021729
theorem B3592619 : Blo 1594996 3592619 := bstep (se 1 (by rfl) ⟨2694464, by rfl⟩ : syracuseStep 3592619 = 5388929) B5388929
theorem B5386985 : Blo 1594996 5386985 := bstep (se 2 (by rfl) ⟨2020119, by rfl⟩ : syracuseStep 5386985 = 4040239) B4040239
theorem B2020079 : Blo 1594996 2020079 := bstep (se 1 (by rfl) ⟨1515059, by rfl⟩ : syracuseStep 2020079 = 3030119) B3030119
theorem B2692075 : Blo 1594996 2692075 := bstep (se 1 (by rfl) ⟨2019056, by rfl⟩ : syracuseStep 2692075 = 4038113) B4038113
theorem B2692217 : Blo 1594996 2692217 := bstep (se 2 (by rfl) ⟨1009581, by rfl⟩ : syracuseStep 2692217 = 2019163) B2019163
theorem B12948947 : Blo 1594996 12948947 := bstep (se 1 (by rfl) ⟨9711710, by rfl⟩ : syracuseStep 12948947 = 19423421) B19423421
theorem B10229267 : Blo 1594996 10229267 := bstep (se 1 (by rfl) ⟨7671950, by rfl⟩ : syracuseStep 10229267 = 15343901) B15343901
theorem B5387849 : Blo 1594996 5387849 := bstep (se 2 (by rfl) ⟨2020443, by rfl⟩ : syracuseStep 5387849 = 4040887) B4040887
theorem B5387903 : Blo 1594996 5387903 := bstep (se 1 (by rfl) ⟨4040927, by rfl⟩ : syracuseStep 5387903 = 8081855) B8081855
theorem B1595087 : Blo 1594996 1595087 := bstep (se 1 (by rfl) ⟨1196315, by rfl⟩ : syracuseStep 1595087 = 2392631) B2392631
theorem B17487805 : Blo 1594996 17487805 := bstep (se 3 (by rfl) ⟨3278963, by rfl⟩ : syracuseStep 17487805 = 6557927) B6557927
theorem B1595503 : Blo 1594996 1595503 := bstep (se 1 (by rfl) ⟨1196627, by rfl⟩ : syracuseStep 1595503 = 2393255) B2393255
theorem B1595551 : Blo 1594996 1595551 := bstep (se 1 (by rfl) ⟨1196663, by rfl⟩ : syracuseStep 1595551 = 2393327) B2393327
theorem B49166513 : Blo 1594996 49166513 := bstep (se 2 (by rfl) ⟨18437442, by rfl⟩ : syracuseStep 49166513 = 36874885) B36874885
theorem B4544723 : Blo 1594996 4544723 := bstep (se 1 (by rfl) ⟨3408542, by rfl⟩ : syracuseStep 4544723 = 6817085) B6817085
theorem B19421471 : Blo 1594996 19421471 := bstep (se 1 (by rfl) ⟨14566103, by rfl⟩ : syracuseStep 19421471 = 29132207) B29132207
theorem B2693513 : Blo 1594996 2693513 := bstep (se 2 (by rfl) ⟨1010067, by rfl⟩ : syracuseStep 2693513 = 2020135) B2020135
theorem B1596287 : Blo 1594996 1596287 := bstep (se 1 (by rfl) ⟨1197215, by rfl⟩ : syracuseStep 1596287 = 2394431) B2394431
theorem B3030043 : Blo 1594996 3030043 := bstep (se 1 (by rfl) ⟨2272532, by rfl⟩ : syracuseStep 3030043 = 4545065) B4545065
theorem B1596775 : Blo 1594996 1596775 := bstep (se 1 (by rfl) ⟨1197581, by rfl⟩ : syracuseStep 1596775 = 2395163) B2395163
theorem B10919323 : Blo 1594996 10919323 := bstep (se 1 (by rfl) ⟨8189492, by rfl⟩ : syracuseStep 10919323 = 16378985) B16378985
theorem B5111353 : Blo 1594996 5111353 := bstep (se 2 (by rfl) ⟨1916757, by rfl⟩ : syracuseStep 5111353 = 3833515) B3833515
theorem B6062303 : Blo 1594996 6062303 := bstep (se 1 (by rfl) ⟨4546727, by rfl⟩ : syracuseStep 6062303 = 9093455) B9093455
theorem B40927517 : Blo 1594996 40927517 := bstep (se 3 (by rfl) ⟨7673909, by rfl⟩ : syracuseStep 40927517 = 15347819) B15347819
theorem B3031607 : Blo 1594996 3031607 := bstep (se 1 (by rfl) ⟨2273705, by rfl⟩ : syracuseStep 3031607 = 4547411) B4547411
theorem B2392703 : Blo 1594996 2392703 := bstep (se 1 (by rfl) ⟨1794527, by rfl⟩ : syracuseStep 2392703 = 3589055) B3589055
theorem B431178407 : Blo 1594996 431178407 := bstep (se 1 (by rfl) ⟨323383805, by rfl⟩ : syracuseStep 431178407 = 646767611) B646767611
theorem B3588839 : Blo 1594996 3588839 := bstep (se 1 (by rfl) ⟨2691629, by rfl⟩ : syracuseStep 3588839 = 5383259) B5383259
theorem B1794811 : Blo 1594996 1794811 := bstep (se 1 (by rfl) ⟨1346108, by rfl⟩ : syracuseStep 1794811 = 2692217) B2692217
theorem B51790589 : Blo 1594996 51790589 := bstep (se 3 (by rfl) ⟨9710735, by rfl⟩ : syracuseStep 51790589 = 19421471) B19421471
theorem B3589433 : Blo 1594996 3589433 := bstep (se 2 (by rfl) ⟨1346037, by rfl⟩ : syracuseStep 3589433 = 2692075) B2692075
theorem B4040057 : Blo 1594996 4040057 := bstep (se 2 (by rfl) ⟨1515021, by rfl⟩ : syracuseStep 4040057 = 3030043) B3030043
theorem B4097447 : Blo 1594996 4097447 := bstep (se 1 (by rfl) ⟨3073085, by rfl⟩ : syracuseStep 4097447 = 6146171) B6146171
theorem B32777675 : Blo 1594996 32777675 := bstep (se 1 (by rfl) ⟨24583256, by rfl⟩ : syracuseStep 32777675 = 49166513) B49166513
theorem B1795675 : Blo 1594996 1795675 := bstep (se 1 (by rfl) ⟨1346756, by rfl⟩ : syracuseStep 1795675 = 2693513) B2693513
theorem B14559097 : Blo 1594996 14559097 := bstep (se 2 (by rfl) ⟨5459661, by rfl⟩ : syracuseStep 14559097 = 10919323) B10919323
theorem B23317073 : Blo 1594996 23317073 := bstep (se 2 (by rfl) ⟨8743902, by rfl⟩ : syracuseStep 23317073 = 17487805) B17487805
theorem B6056639 : Blo 1594996 6056639 := bstep (se 1 (by rfl) ⟨4542479, by rfl⟩ : syracuseStep 6056639 = 9084959) B9084959
theorem B2395079 : Blo 1594996 2395079 := bstep (se 1 (by rfl) ⟨1796309, by rfl⟩ : syracuseStep 2395079 = 3592619) B3592619
theorem B3591323 : Blo 1594996 3591323 := bstep (se 1 (by rfl) ⟨2693492, by rfl⟩ : syracuseStep 3591323 = 5386985) B5386985
theorem B34516601 : Blo 1594996 34516601 := bstep (se 2 (by rfl) ⟨12943725, by rfl⟩ : syracuseStep 34516601 = 25887451) B25887451
theorem B6819511 : Blo 1594996 6819511 := bstep (se 1 (by rfl) ⟨5114633, by rfl⟩ : syracuseStep 6819511 = 10229267) B10229267
theorem B3591899 : Blo 1594996 3591899 := bstep (se 1 (by rfl) ⟨2693924, by rfl⟩ : syracuseStep 3591899 = 5387849) B5387849
theorem B3591935 : Blo 1594996 3591935 := bstep (se 1 (by rfl) ⟨2693951, by rfl⟩ : syracuseStep 3591935 = 5387903) B5387903
theorem B27258767 : Blo 1594996 27258767 := bstep (se 1 (by rfl) ⟨20444075, by rfl⟩ : syracuseStep 27258767 = 40888151) B40888151
theorem B6819785 : Blo 1594996 6819785 := bstep (se 2 (by rfl) ⟨2557419, by rfl⟩ : syracuseStep 6819785 = 5114839) B5114839
theorem B7278713 : Blo 1594996 7278713 := bstep (se 2 (by rfl) ⟨2729517, by rfl⟩ : syracuseStep 7278713 = 5459035) B5459035
theorem B5386877 : Blo 1594996 5386877 := bstep (se 3 (by rfl) ⟨1010039, by rfl⟩ : syracuseStep 5386877 = 2020079) B2020079
theorem B94573261 : Blo 1594996 94573261 := bstep (se 3 (by rfl) ⟨17732486, by rfl⟩ : syracuseStep 94573261 = 35464973) B35464973
theorem B1595111 : Blo 1594996 1595111 := bstep (se 1 (by rfl) ⟨1196333, by rfl⟩ : syracuseStep 1595111 = 2392667) B2392667
theorem B1595239 : Blo 1594996 1595239 := bstep (se 1 (by rfl) ⟨1196429, by rfl⟩ : syracuseStep 1595239 = 2392859) B2392859
theorem B1595483 : Blo 1594996 1595483 := bstep (se 1 (by rfl) ⟨1196612, by rfl⟩ : syracuseStep 1595483 = 2393225) B2393225
theorem B8632631 : Blo 1594996 8632631 := bstep (se 1 (by rfl) ⟨6474473, by rfl⟩ : syracuseStep 8632631 = 12948947) B12948947
theorem B1595839 : Blo 1594996 1595839 := bstep (se 1 (by rfl) ⟨1196879, by rfl⟩ : syracuseStep 1595839 = 2393759) B2393759
theorem B1596059 : Blo 1594996 1596059 := bstep (se 1 (by rfl) ⟨1197044, by rfl⟩ : syracuseStep 1596059 = 2394089) B2394089
theorem B3029815 : Blo 1594996 3029815 := bstep (se 1 (by rfl) ⟨2272361, by rfl⟩ : syracuseStep 3029815 = 4544723) B4544723
theorem B118070207 : Blo 1594996 118070207 := bstep (se 1 (by rfl) ⟨88552655, by rfl⟩ : syracuseStep 118070207 = 177105311) B177105311
theorem B1596543 : Blo 1594996 1596543 := bstep (se 1 (by rfl) ⟨1197407, by rfl⟩ : syracuseStep 1596543 = 2394815) B2394815
theorem B8084609 : Blo 1594996 8084609 := bstep (se 2 (by rfl) ⟨3031728, by rfl⟩ : syracuseStep 8084609 = 6063457) B6063457
theorem B1596735 : Blo 1594996 1596735 := bstep (se 1 (by rfl) ⟨1197551, by rfl⟩ : syracuseStep 1596735 = 2395103) B2395103
theorem B4037971 : Blo 1594996 4037971 := bstep (se 1 (by rfl) ⟨3028478, by rfl⟩ : syracuseStep 4037971 = 6056957) B6056957
theorem B6815137 : Blo 1594996 6815137 := bstep (se 2 (by rfl) ⟨2555676, by rfl⟩ : syracuseStep 6815137 = 5111353) B5111353
theorem B1596975 : Blo 1594996 1596975 := bstep (se 1 (by rfl) ⟨1197731, by rfl⟩ : syracuseStep 1596975 = 2395463) B2395463
theorem B14556763 : Blo 1594996 14556763 := bstep (se 1 (by rfl) ⟨10917572, by rfl⟩ : syracuseStep 14556763 = 21835145) B21835145
theorem B2392559 : Blo 1594996 2392559 := bstep (se 1 (by rfl) ⟨1794419, by rfl⟩ : syracuseStep 2392559 = 3588839) B3588839
theorem B2392955 : Blo 1594996 2392955 := bstep (se 1 (by rfl) ⟨1794716, by rfl⟩ : syracuseStep 2392955 = 3589433) B3589433
theorem B2393081 : Blo 1594996 2393081 := bstep (se 2 (by rfl) ⟨897405, by rfl⟩ : syracuseStep 2393081 = 1794811) B1794811
theorem B4039753 : Blo 1594996 4039753 := bstep (se 2 (by rfl) ⟨1514907, by rfl⟩ : syracuseStep 4039753 = 3029815) B3029815
theorem B43706101 : Blo 1594996 43706101 := bstep (se 5 (by rfl) ⟨2048723, by rfl⟩ : syracuseStep 43706101 = 4097447) B4097447
theorem B5383961 : Blo 1594996 5383961 := bstep (se 2 (by rfl) ⟨2018985, by rfl⟩ : syracuseStep 5383961 = 4037971) B4037971
theorem B9086849 : Blo 1594996 9086849 := bstep (se 2 (by rfl) ⟨3407568, by rfl⟩ : syracuseStep 9086849 = 6815137) B6815137
theorem B2394215 : Blo 1594996 2394215 := bstep (se 1 (by rfl) ⟨1795661, by rfl⟩ : syracuseStep 2394215 = 3591323) B3591323
theorem B19409017 : Blo 1594996 19409017 := bstep (se 2 (by rfl) ⟨7278381, by rfl⟩ : syracuseStep 19409017 = 14556763) B14556763
theorem B2394233 : Blo 1594996 2394233 := bstep (se 2 (by rfl) ⟨897837, by rfl⟩ : syracuseStep 2394233 = 1795675) B1795675
theorem B2394599 : Blo 1594996 2394599 := bstep (se 1 (by rfl) ⟨1795949, by rfl⟩ : syracuseStep 2394599 = 3591899) B3591899
theorem B2394623 : Blo 1594996 2394623 := bstep (se 1 (by rfl) ⟨1795967, by rfl⟩ : syracuseStep 2394623 = 3591935) B3591935
theorem B18172511 : Blo 1594996 18172511 := bstep (se 1 (by rfl) ⟨13629383, by rfl⟩ : syracuseStep 18172511 = 27258767) B27258767
theorem B4852475 : Blo 1594996 4852475 := bstep (se 1 (by rfl) ⟨3639356, by rfl⟩ : syracuseStep 4852475 = 7278713) B7278713
theorem B4041535 : Blo 1594996 4041535 := bstep (se 1 (by rfl) ⟨3031151, by rfl⟩ : syracuseStep 4041535 = 6062303) B6062303
theorem B3591251 : Blo 1594996 3591251 := bstep (se 1 (by rfl) ⟨2693438, by rfl⟩ : syracuseStep 3591251 = 5386877) B5386877
theorem B287452271 : Blo 1594996 287452271 := bstep (se 1 (by rfl) ⟨215589203, by rfl⟩ : syracuseStep 287452271 = 431178407) B431178407
theorem B21851783 : Blo 1594996 21851783 := bstep (se 1 (by rfl) ⟨16388837, by rfl⟩ : syracuseStep 21851783 = 32777675) B32777675
theorem B5755087 : Blo 1594996 5755087 := bstep (se 1 (by rfl) ⟨4316315, by rfl⟩ : syracuseStep 5755087 = 8632631) B8632631
theorem B15544715 : Blo 1594996 15544715 := bstep (se 1 (by rfl) ⟨11658536, by rfl⟩ : syracuseStep 15544715 = 23317073) B23317073
theorem B78713471 : Blo 1594996 78713471 := bstep (se 1 (by rfl) ⟨59035103, by rfl⟩ : syracuseStep 78713471 = 118070207) B118070207
theorem B19412129 : Blo 1594996 19412129 := bstep (se 2 (by rfl) ⟨7279548, by rfl⟩ : syracuseStep 19412129 = 14559097) B14559097
theorem B27285011 : Blo 1594996 27285011 := bstep (se 1 (by rfl) ⟨20463758, by rfl⟩ : syracuseStep 27285011 = 40927517) B40927517
theorem B1595135 : Blo 1594996 1595135 := bstep (se 1 (by rfl) ⟨1196351, by rfl⟩ : syracuseStep 1595135 = 2392703) B2392703
theorem B34527059 : Blo 1594996 34527059 := bstep (se 1 (by rfl) ⟨25895294, by rfl⟩ : syracuseStep 34527059 = 51790589) B51790589
theorem B2693371 : Blo 1594996 2693371 := bstep (se 1 (by rfl) ⟨2020028, by rfl⟩ : syracuseStep 2693371 = 4040057) B4040057
theorem B126097681 : Blo 1594996 126097681 := bstep (se 2 (by rfl) ⟨47286630, by rfl⟩ : syracuseStep 126097681 = 94573261) B94573261
theorem B8084285 : Blo 1594996 8084285 := bstep (se 3 (by rfl) ⟨1515803, by rfl⟩ : syracuseStep 8084285 = 3031607) B3031607
theorem B4037759 : Blo 1594996 4037759 := bstep (se 1 (by rfl) ⟨3028319, by rfl⟩ : syracuseStep 4037759 = 6056639) B6056639
theorem B1596719 : Blo 1594996 1596719 := bstep (se 1 (by rfl) ⟨1197539, by rfl⟩ : syracuseStep 1596719 = 2395079) B2395079
theorem B5389739 : Blo 1594996 5389739 := bstep (se 1 (by rfl) ⟨4042304, by rfl⟩ : syracuseStep 5389739 = 8084609) B8084609
theorem B9092681 : Blo 1594996 9092681 := bstep (se 2 (by rfl) ⟨3409755, by rfl⟩ : syracuseStep 9092681 = 6819511) B6819511
theorem B23011067 : Blo 1594996 23011067 := bstep (se 1 (by rfl) ⟨17258300, by rfl⟩ : syracuseStep 23011067 = 34516601) B34516601
theorem B4546523 : Blo 1594996 4546523 := bstep (se 1 (by rfl) ⟨3409892, by rfl⟩ : syracuseStep 4546523 = 6819785) B6819785
theorem B25878689 : Blo 1594996 25878689 := bstep (se 2 (by rfl) ⟨9704508, by rfl⟩ : syracuseStep 25878689 = 19409017) B19409017
theorem B41452573 : Blo 1594996 41452573 := bstep (se 3 (by rfl) ⟨7772357, by rfl⟩ : syracuseStep 41452573 = 15544715) B15544715
theorem B3589307 : Blo 1594996 3589307 := bstep (se 1 (by rfl) ⟨2691980, by rfl⟩ : syracuseStep 3589307 = 5383961) B5383961
theorem B2394167 : Blo 1594996 2394167 := bstep (se 1 (by rfl) ⟨1795625, by rfl⟩ : syracuseStep 2394167 = 3591251) B3591251
theorem B14567855 : Blo 1594996 14567855 := bstep (se 1 (by rfl) ⟨10925891, by rfl⟩ : syracuseStep 14567855 = 21851783) B21851783
theorem B3591161 : Blo 1594996 3591161 := bstep (se 2 (by rfl) ⟨1346685, by rfl⟩ : syracuseStep 3591161 = 2693371) B2693371
theorem B18190007 : Blo 1594996 18190007 := bstep (se 1 (by rfl) ⟨13642505, by rfl⟩ : syracuseStep 18190007 = 27285011) B27285011
theorem B6057899 : Blo 1594996 6057899 := bstep (se 1 (by rfl) ⟨4543424, by rfl⟩ : syracuseStep 6057899 = 9086849) B9086849
theorem B5386337 : Blo 1594996 5386337 := bstep (se 2 (by rfl) ⟨2019876, by rfl⟩ : syracuseStep 5386337 = 4039753) B4039753
theorem B2691839 : Blo 1594996 2691839 := bstep (se 1 (by rfl) ⟨2018879, by rfl⟩ : syracuseStep 2691839 = 4037759) B4037759
theorem B3593159 : Blo 1594996 3593159 := bstep (se 1 (by rfl) ⟨2694869, by rfl⟩ : syracuseStep 3593159 = 5389739) B5389739
theorem B58274801 : Blo 1594996 58274801 := bstep (se 2 (by rfl) ⟨21853050, by rfl⟩ : syracuseStep 58274801 = 43706101) B43706101
theorem B15340711 : Blo 1594996 15340711 := bstep (se 1 (by rfl) ⟨11505533, by rfl⟩ : syracuseStep 15340711 = 23011067) B23011067
theorem B7673449 : Blo 1594996 7673449 := bstep (se 2 (by rfl) ⟨2877543, by rfl⟩ : syracuseStep 7673449 = 5755087) B5755087
theorem B766539389 : Blo 1594996 766539389 := bstep (se 3 (by rfl) ⟨143726135, by rfl⟩ : syracuseStep 766539389 = 287452271) B287452271
theorem B1595039 : Blo 1594996 1595039 := bstep (se 1 (by rfl) ⟨1196279, by rfl⟩ : syracuseStep 1595039 = 2392559) B2392559
theorem B168130241 : Blo 1594996 168130241 := bstep (se 2 (by rfl) ⟨63048840, by rfl⟩ : syracuseStep 168130241 = 126097681) B126097681
theorem B1595303 : Blo 1594996 1595303 := bstep (se 1 (by rfl) ⟨1196477, by rfl⟩ : syracuseStep 1595303 = 2392955) B2392955
theorem B1595387 : Blo 1594996 1595387 := bstep (se 1 (by rfl) ⟨1196540, by rfl⟩ : syracuseStep 1595387 = 2393081) B2393081
theorem B12941419 : Blo 1594996 12941419 := bstep (se 1 (by rfl) ⟨9706064, by rfl⟩ : syracuseStep 12941419 = 19412129) B19412129
theorem B5388713 : Blo 1594996 5388713 := bstep (se 2 (by rfl) ⟨2020767, by rfl⟩ : syracuseStep 5388713 = 4041535) B4041535
theorem B23018039 : Blo 1594996 23018039 := bstep (se 1 (by rfl) ⟨17263529, by rfl⟩ : syracuseStep 23018039 = 34527059) B34527059
theorem B1596143 : Blo 1594996 1596143 := bstep (se 1 (by rfl) ⟨1197107, by rfl⟩ : syracuseStep 1596143 = 2394215) B2394215
theorem B1596155 : Blo 1594996 1596155 := bstep (se 1 (by rfl) ⟨1197116, by rfl⟩ : syracuseStep 1596155 = 2394233) B2394233
theorem B1596399 : Blo 1594996 1596399 := bstep (se 1 (by rfl) ⟨1197299, by rfl⟩ : syracuseStep 1596399 = 2394599) B2394599
theorem B209902589 : Blo 1594996 209902589 := bstep (se 3 (by rfl) ⟨39356735, by rfl⟩ : syracuseStep 209902589 = 78713471) B78713471
theorem B1596415 : Blo 1594996 1596415 := bstep (se 1 (by rfl) ⟨1197311, by rfl⟩ : syracuseStep 1596415 = 2394623) B2394623
theorem B12115007 : Blo 1594996 12115007 := bstep (se 1 (by rfl) ⟨9086255, by rfl⟩ : syracuseStep 12115007 = 18172511) B18172511
theorem B3234983 : Blo 1594996 3234983 := bstep (se 1 (by rfl) ⟨2426237, by rfl⟩ : syracuseStep 3234983 = 4852475) B4852475
theorem B5389523 : Blo 1594996 5389523 := bstep (se 1 (by rfl) ⟨4042142, by rfl⟩ : syracuseStep 5389523 = 8084285) B8084285
theorem B6061787 : Blo 1594996 6061787 := bstep (se 1 (by rfl) ⟨4546340, by rfl⟩ : syracuseStep 6061787 = 9092681) B9092681
theorem B3031015 : Blo 1594996 3031015 := bstep (se 1 (by rfl) ⟨2273261, by rfl⟩ : syracuseStep 3031015 = 4546523) B4546523
theorem B17252459 : Blo 1594996 17252459 := bstep (se 1 (by rfl) ⟨12939344, by rfl⟩ : syracuseStep 17252459 = 25878689) B25878689
theorem B1794559 : Blo 1594996 1794559 := bstep (se 1 (by rfl) ⟨1345919, by rfl⟩ : syracuseStep 1794559 = 2691839) B2691839
theorem B2392871 : Blo 1594996 2392871 := bstep (se 1 (by rfl) ⟨1794653, by rfl⟩ : syracuseStep 2392871 = 3589307) B3589307
theorem B511026259 : Blo 1594996 511026259 := bstep (se 1 (by rfl) ⟨383269694, by rfl⟩ : syracuseStep 511026259 = 766539389) B766539389
theorem B38847613 : Blo 1594996 38847613 := bstep (se 3 (by rfl) ⟨7283927, by rfl⟩ : syracuseStep 38847613 = 14567855) B14567855
theorem B15345359 : Blo 1594996 15345359 := bstep (se 1 (by rfl) ⟨11509019, by rfl⟩ : syracuseStep 15345359 = 23018039) B23018039
theorem B34506485 : Blo 1594996 34506485 := bstep (se 5 (by rfl) ⟨1617491, by rfl⟩ : syracuseStep 34506485 = 3234983) B3234983
theorem B2394107 : Blo 1594996 2394107 := bstep (se 1 (by rfl) ⟨1795580, by rfl⟩ : syracuseStep 2394107 = 3591161) B3591161
theorem B12126671 : Blo 1594996 12126671 := bstep (se 1 (by rfl) ⟨9095003, by rfl⟩ : syracuseStep 12126671 = 18190007) B18190007
theorem B4041191 : Blo 1594996 4041191 := bstep (se 1 (by rfl) ⟨3030893, by rfl⟩ : syracuseStep 4041191 = 6061787) B6061787
theorem B4041353 : Blo 1594996 4041353 := bstep (se 2 (by rfl) ⟨1515507, by rfl⟩ : syracuseStep 4041353 = 3031015) B3031015
theorem B3590891 : Blo 1594996 3590891 := bstep (se 1 (by rfl) ⟨2693168, by rfl⟩ : syracuseStep 3590891 = 5386337) B5386337
theorem B17255225 : Blo 1594996 17255225 := bstep (se 2 (by rfl) ⟨6470709, by rfl⟩ : syracuseStep 17255225 = 12941419) B12941419
theorem B2395439 : Blo 1594996 2395439 := bstep (se 1 (by rfl) ⟨1796579, by rfl⟩ : syracuseStep 2395439 = 3593159) B3593159
theorem B38849867 : Blo 1594996 38849867 := bstep (se 1 (by rfl) ⟨29137400, by rfl⟩ : syracuseStep 38849867 = 58274801) B58274801
theorem B112086827 : Blo 1594996 112086827 := bstep (se 1 (by rfl) ⟨84065120, by rfl⟩ : syracuseStep 112086827 = 168130241) B168130241
theorem B3592475 : Blo 1594996 3592475 := bstep (se 1 (by rfl) ⟨2694356, by rfl⟩ : syracuseStep 3592475 = 5388713) B5388713
theorem B3593015 : Blo 1594996 3593015 := bstep (se 1 (by rfl) ⟨2694761, by rfl⟩ : syracuseStep 3593015 = 5389523) B5389523
theorem B1596111 : Blo 1594996 1596111 := bstep (se 1 (by rfl) ⟨1197083, by rfl⟩ : syracuseStep 1596111 = 2394167) B2394167
theorem B55270097 : Blo 1594996 55270097 := bstep (se 2 (by rfl) ⟨20726286, by rfl⟩ : syracuseStep 55270097 = 41452573) B41452573
theorem B20454281 : Blo 1594996 20454281 := bstep (se 2 (by rfl) ⟨7670355, by rfl⟩ : syracuseStep 20454281 = 15340711) B15340711
theorem B139935059 : Blo 1594996 139935059 := bstep (se 1 (by rfl) ⟨104951294, by rfl⟩ : syracuseStep 139935059 = 209902589) B209902589
theorem B8076671 : Blo 1594996 8076671 := bstep (se 1 (by rfl) ⟨6057503, by rfl⟩ : syracuseStep 8076671 = 12115007) B12115007
theorem B10231265 : Blo 1594996 10231265 := bstep (se 2 (by rfl) ⟨3836724, by rfl⟩ : syracuseStep 10231265 = 7673449) B7673449
theorem B4038599 : Blo 1594996 4038599 := bstep (se 1 (by rfl) ⟨3028949, by rfl⟩ : syracuseStep 4038599 = 6057899) B6057899
theorem B11501639 : Blo 1594996 11501639 := bstep (se 1 (by rfl) ⟨8626229, by rfl⟩ : syracuseStep 11501639 = 17252459) B17252459
theorem B2392745 : Blo 1594996 2392745 := bstep (se 2 (by rfl) ⟨897279, by rfl⟩ : syracuseStep 2392745 = 1794559) B1794559
theorem B23004323 : Blo 1594996 23004323 := bstep (se 1 (by rfl) ⟨17253242, by rfl⟩ : syracuseStep 23004323 = 34506485) B34506485
theorem B2393927 : Blo 1594996 2393927 := bstep (se 1 (by rfl) ⟨1795445, by rfl⟩ : syracuseStep 2393927 = 3590891) B3590891
theorem B5384447 : Blo 1594996 5384447 := bstep (se 1 (by rfl) ⟨4038335, by rfl⟩ : syracuseStep 5384447 = 8076671) B8076671
theorem B2394983 : Blo 1594996 2394983 := bstep (se 1 (by rfl) ⟨1796237, by rfl⟩ : syracuseStep 2394983 = 3592475) B3592475
theorem B2395343 : Blo 1594996 2395343 := bstep (se 1 (by rfl) ⟨1796507, by rfl⟩ : syracuseStep 2395343 = 3593015) B3593015
theorem B13636187 : Blo 1594996 13636187 := bstep (se 1 (by rfl) ⟨10227140, by rfl⟩ : syracuseStep 13636187 = 20454281) B20454281
theorem B25899911 : Blo 1594996 25899911 := bstep (se 1 (by rfl) ⟨19424933, by rfl⟩ : syracuseStep 25899911 = 38849867) B38849867
theorem B6820843 : Blo 1594996 6820843 := bstep (se 1 (by rfl) ⟨5115632, by rfl⟩ : syracuseStep 6820843 = 10231265) B10231265
theorem B74724551 : Blo 1594996 74724551 := bstep (se 1 (by rfl) ⟨56043413, by rfl⟩ : syracuseStep 74724551 = 112086827) B112086827
theorem B2692399 : Blo 1594996 2692399 := bstep (se 1 (by rfl) ⟨2019299, by rfl⟩ : syracuseStep 2692399 = 4038599) B4038599
theorem B1595247 : Blo 1594996 1595247 := bstep (se 1 (by rfl) ⟨1196435, by rfl⟩ : syracuseStep 1595247 = 2392871) B2392871
theorem B10230239 : Blo 1594996 10230239 := bstep (se 1 (by rfl) ⟨7672679, by rfl⟩ : syracuseStep 10230239 = 15345359) B15345359
theorem B1596071 : Blo 1594996 1596071 := bstep (se 1 (by rfl) ⟨1197053, by rfl⟩ : syracuseStep 1596071 = 2394107) B2394107
theorem B681368345 : Blo 1594996 681368345 := bstep (se 2 (by rfl) ⟨255513129, by rfl⟩ : syracuseStep 681368345 = 511026259) B511026259
theorem B51796817 : Blo 1594996 51796817 := bstep (se 2 (by rfl) ⟨19423806, by rfl⟩ : syracuseStep 51796817 = 38847613) B38847613
theorem B8084447 : Blo 1594996 8084447 := bstep (se 1 (by rfl) ⟨6063335, by rfl⟩ : syracuseStep 8084447 = 12126671) B12126671
theorem B2694127 : Blo 1594996 2694127 := bstep (se 1 (by rfl) ⟨2020595, by rfl⟩ : syracuseStep 2694127 = 4041191) B4041191
theorem B2694235 : Blo 1594996 2694235 := bstep (se 1 (by rfl) ⟨2020676, by rfl⟩ : syracuseStep 2694235 = 4041353) B4041353
theorem B36846731 : Blo 1594996 36846731 := bstep (se 1 (by rfl) ⟨27635048, by rfl⟩ : syracuseStep 36846731 = 55270097) B55270097
theorem B46013933 : Blo 1594996 46013933 := bstep (se 3 (by rfl) ⟨8627612, by rfl⟩ : syracuseStep 46013933 = 17255225) B17255225
theorem B1596959 : Blo 1594996 1596959 := bstep (se 1 (by rfl) ⟨1197719, by rfl⟩ : syracuseStep 1596959 = 2395439) B2395439
theorem B93290039 : Blo 1594996 93290039 := bstep (se 1 (by rfl) ⟨69967529, by rfl⟩ : syracuseStep 93290039 = 139935059) B139935059
theorem B7667759 : Blo 1594996 7667759 := bstep (se 1 (by rfl) ⟨5750819, by rfl⟩ : syracuseStep 7667759 = 11501639) B11501639
theorem B15336215 : Blo 1594996 15336215 := bstep (se 1 (by rfl) ⟨11502161, by rfl⟩ : syracuseStep 15336215 = 23004323) B23004323
theorem B49816367 : Blo 1594996 49816367 := bstep (se 1 (by rfl) ⟨37362275, by rfl⟩ : syracuseStep 49816367 = 74724551) B74724551
theorem B27280637 : Blo 1594996 27280637 := bstep (se 3 (by rfl) ⟨5115119, by rfl⟩ : syracuseStep 27280637 = 10230239) B10230239
theorem B9094457 : Blo 1594996 9094457 := bstep (se 2 (by rfl) ⟨3410421, by rfl⟩ : syracuseStep 9094457 = 6820843) B6820843
theorem B3589631 : Blo 1594996 3589631 := bstep (se 1 (by rfl) ⟨2692223, by rfl⟩ : syracuseStep 3589631 = 5384447) B5384447
theorem B3589865 : Blo 1594996 3589865 := bstep (se 2 (by rfl) ⟨1346199, by rfl⟩ : syracuseStep 3589865 = 2692399) B2692399
theorem B34531211 : Blo 1594996 34531211 := bstep (se 1 (by rfl) ⟨25898408, by rfl⟩ : syracuseStep 34531211 = 51796817) B51796817
theorem B3592169 : Blo 1594996 3592169 := bstep (se 2 (by rfl) ⟨1347063, by rfl⟩ : syracuseStep 3592169 = 2694127) B2694127
theorem B3592313 : Blo 1594996 3592313 := bstep (se 2 (by rfl) ⟨1347117, by rfl⟩ : syracuseStep 3592313 = 2694235) B2694235
theorem B24564487 : Blo 1594996 24564487 := bstep (se 1 (by rfl) ⟨18423365, by rfl⟩ : syracuseStep 24564487 = 36846731) B36846731
theorem B30675955 : Blo 1594996 30675955 := bstep (se 1 (by rfl) ⟨23006966, by rfl⟩ : syracuseStep 30675955 = 46013933) B46013933
theorem B9090791 : Blo 1594996 9090791 := bstep (se 1 (by rfl) ⟨6818093, by rfl⟩ : syracuseStep 9090791 = 13636187) B13636187
theorem B1595163 : Blo 1594996 1595163 := bstep (se 1 (by rfl) ⟨1196372, by rfl⟩ : syracuseStep 1595163 = 2392745) B2392745
theorem B17266607 : Blo 1594996 17266607 := bstep (se 1 (by rfl) ⟨12949955, by rfl⟩ : syracuseStep 17266607 = 25899911) B25899911
theorem B1595951 : Blo 1594996 1595951 := bstep (se 1 (by rfl) ⟨1196963, by rfl⟩ : syracuseStep 1595951 = 2393927) B2393927
theorem B454245563 : Blo 1594996 454245563 := bstep (se 1 (by rfl) ⟨340684172, by rfl⟩ : syracuseStep 454245563 = 681368345) B681368345
theorem B1596655 : Blo 1594996 1596655 := bstep (se 1 (by rfl) ⟨1197491, by rfl⟩ : syracuseStep 1596655 = 2394983) B2394983
theorem B5389631 : Blo 1594996 5389631 := bstep (se 1 (by rfl) ⟨4042223, by rfl⟩ : syracuseStep 5389631 = 8084447) B8084447
theorem B1596895 : Blo 1594996 1596895 := bstep (se 1 (by rfl) ⟨1197671, by rfl⟩ : syracuseStep 1596895 = 2395343) B2395343
theorem B62193359 : Blo 1594996 62193359 := bstep (se 1 (by rfl) ⟨46645019, by rfl⟩ : syracuseStep 62193359 = 93290039) B93290039
theorem B5111839 : Blo 1594996 5111839 := bstep (se 1 (by rfl) ⟨3833879, by rfl⟩ : syracuseStep 5111839 = 7667759) B7667759
theorem B10224143 : Blo 1594996 10224143 := bstep (se 1 (by rfl) ⟨7668107, by rfl⟩ : syracuseStep 10224143 = 15336215) B15336215
theorem B33210911 : Blo 1594996 33210911 := bstep (se 1 (by rfl) ⟨24908183, by rfl⟩ : syracuseStep 33210911 = 49816367) B49816367
theorem B18187091 : Blo 1594996 18187091 := bstep (se 1 (by rfl) ⟨13640318, by rfl⟩ : syracuseStep 18187091 = 27280637) B27280637
theorem B6062971 : Blo 1594996 6062971 := bstep (se 1 (by rfl) ⟨4547228, by rfl⟩ : syracuseStep 6062971 = 9094457) B9094457
theorem B2393087 : Blo 1594996 2393087 := bstep (se 1 (by rfl) ⟨1794815, by rfl⟩ : syracuseStep 2393087 = 3589631) B3589631
theorem B32752649 : Blo 1594996 32752649 := bstep (se 2 (by rfl) ⟨12282243, by rfl⟩ : syracuseStep 32752649 = 24564487) B24564487
theorem B2393243 : Blo 1594996 2393243 := bstep (se 1 (by rfl) ⟨1794932, by rfl⟩ : syracuseStep 2393243 = 3589865) B3589865
theorem B23020807 : Blo 1594996 23020807 := bstep (se 1 (by rfl) ⟨17265605, by rfl⟩ : syracuseStep 23020807 = 34531211) B34531211
theorem B11511071 : Blo 1594996 11511071 := bstep (se 1 (by rfl) ⟨8633303, by rfl⟩ : syracuseStep 11511071 = 17266607) B17266607
theorem B41462239 : Blo 1594996 41462239 := bstep (se 1 (by rfl) ⟨31096679, by rfl⟩ : syracuseStep 41462239 = 62193359) B62193359
theorem B2394779 : Blo 1594996 2394779 := bstep (se 1 (by rfl) ⟨1796084, by rfl⟩ : syracuseStep 2394779 = 3592169) B3592169
theorem B2394875 : Blo 1594996 2394875 := bstep (se 1 (by rfl) ⟨1796156, by rfl⟩ : syracuseStep 2394875 = 3592313) B3592313
theorem B302830375 : Blo 1594996 302830375 := bstep (se 1 (by rfl) ⟨227122781, by rfl⟩ : syracuseStep 302830375 = 454245563) B454245563
theorem B3593087 : Blo 1594996 3593087 := bstep (se 1 (by rfl) ⟨2694815, by rfl⟩ : syracuseStep 3593087 = 5389631) B5389631
theorem B6060527 : Blo 1594996 6060527 := bstep (se 1 (by rfl) ⟨4545395, by rfl⟩ : syracuseStep 6060527 = 9090791) B9090791
theorem B40901273 : Blo 1594996 40901273 := bstep (se 2 (by rfl) ⟨15337977, by rfl⟩ : syracuseStep 40901273 = 30675955) B30675955
theorem B27263141 : Blo 1594996 27263141 := bstep (se 4 (by rfl) ⟨2555919, by rfl⟩ : syracuseStep 27263141 = 5111839) B5111839
theorem B6816095 : Blo 1594996 6816095 := bstep (se 1 (by rfl) ⟨5112071, by rfl⟩ : syracuseStep 6816095 = 10224143) B10224143
theorem B12124727 : Blo 1594996 12124727 := bstep (se 1 (by rfl) ⟨9093545, by rfl⟩ : syracuseStep 12124727 = 18187091) B18187091
theorem B4040351 : Blo 1594996 4040351 := bstep (se 1 (by rfl) ⟨3030263, by rfl⟩ : syracuseStep 4040351 = 6060527) B6060527
theorem B2395391 : Blo 1594996 2395391 := bstep (se 1 (by rfl) ⟨1796543, by rfl⟩ : syracuseStep 2395391 = 3593087) B3593087
theorem B55282985 : Blo 1594996 55282985 := bstep (se 2 (by rfl) ⟨20731119, by rfl⟩ : syracuseStep 55282985 = 41462239) B41462239
theorem B21835099 : Blo 1594996 21835099 := bstep (se 1 (by rfl) ⟨16376324, by rfl⟩ : syracuseStep 21835099 = 32752649) B32752649
theorem B27267515 : Blo 1594996 27267515 := bstep (se 1 (by rfl) ⟨20450636, by rfl⟩ : syracuseStep 27267515 = 40901273) B40901273
theorem B1595391 : Blo 1594996 1595391 := bstep (se 1 (by rfl) ⟨1196543, by rfl⟩ : syracuseStep 1595391 = 2393087) B2393087
theorem B1595495 : Blo 1594996 1595495 := bstep (se 1 (by rfl) ⟨1196621, by rfl⟩ : syracuseStep 1595495 = 2393243) B2393243
theorem B7674047 : Blo 1594996 7674047 := bstep (se 1 (by rfl) ⟨5755535, by rfl⟩ : syracuseStep 7674047 = 11511071) B11511071
theorem B403773833 : Blo 1594996 403773833 := bstep (se 2 (by rfl) ⟨151415187, by rfl⟩ : syracuseStep 403773833 = 302830375) B302830375
theorem B8083961 : Blo 1594996 8083961 := bstep (se 2 (by rfl) ⟨3031485, by rfl⟩ : syracuseStep 8083961 = 6062971) B6062971
theorem B88562429 : Blo 1594996 88562429 := bstep (se 3 (by rfl) ⟨16605455, by rfl⟩ : syracuseStep 88562429 = 33210911) B33210911
theorem B30694409 : Blo 1594996 30694409 := bstep (se 2 (by rfl) ⟨11510403, by rfl⟩ : syracuseStep 30694409 = 23020807) B23020807
theorem B1596519 : Blo 1594996 1596519 := bstep (se 1 (by rfl) ⟨1197389, by rfl⟩ : syracuseStep 1596519 = 2394779) B2394779
theorem B1596583 : Blo 1594996 1596583 := bstep (se 1 (by rfl) ⟨1197437, by rfl⟩ : syracuseStep 1596583 = 2394875) B2394875
theorem B18178343 : Blo 1594996 18178343 := bstep (se 1 (by rfl) ⟨13633757, by rfl⟩ : syracuseStep 18178343 = 27267515) B27267515
theorem B59041619 : Blo 1594996 59041619 := bstep (se 1 (by rfl) ⟨44281214, by rfl⟩ : syracuseStep 59041619 = 88562429) B88562429
theorem B5116031 : Blo 1594996 5116031 := bstep (se 1 (by rfl) ⟨3837023, by rfl⟩ : syracuseStep 5116031 = 7674047) B7674047
theorem B18175427 : Blo 1594996 18175427 := bstep (se 1 (by rfl) ⟨13631570, by rfl⟩ : syracuseStep 18175427 = 27263141) B27263141
theorem B4544063 : Blo 1594996 4544063 := bstep (se 1 (by rfl) ⟨3408047, by rfl⟩ : syracuseStep 4544063 = 6816095) B6816095
theorem B8083151 : Blo 1594996 8083151 := bstep (se 1 (by rfl) ⟨6062363, by rfl⟩ : syracuseStep 8083151 = 12124727) B12124727
theorem B1076730221 : Blo 1594996 1076730221 := bstep (se 3 (by rfl) ⟨201886916, by rfl⟩ : syracuseStep 1076730221 = 403773833) B403773833
theorem B2693567 : Blo 1594996 2693567 := bstep (se 1 (by rfl) ⟨2020175, by rfl⟩ : syracuseStep 2693567 = 4040351) B4040351
theorem B5389307 : Blo 1594996 5389307 := bstep (se 1 (by rfl) ⟨4041980, by rfl⟩ : syracuseStep 5389307 = 8083961) B8083961
theorem B29113465 : Blo 1594996 29113465 := bstep (se 2 (by rfl) ⟨10917549, by rfl⟩ : syracuseStep 29113465 = 21835099) B21835099
theorem B20462939 : Blo 1594996 20462939 := bstep (se 1 (by rfl) ⟨15347204, by rfl⟩ : syracuseStep 20462939 = 30694409) B30694409
theorem B1596927 : Blo 1594996 1596927 := bstep (se 1 (by rfl) ⟨1197695, by rfl⟩ : syracuseStep 1596927 = 2395391) B2395391
theorem B36855323 : Blo 1594996 36855323 := bstep (se 1 (by rfl) ⟨27641492, by rfl⟩ : syracuseStep 36855323 = 55282985) B55282985
theorem B12116951 : Blo 1594996 12116951 := bstep (se 1 (by rfl) ⟨9087713, by rfl⟩ : syracuseStep 12116951 = 18175427) B18175427
theorem B1795711 : Blo 1594996 1795711 := bstep (se 1 (by rfl) ⟨1346783, by rfl⟩ : syracuseStep 1795711 = 2693567) B2693567
theorem B13641959 : Blo 1594996 13641959 := bstep (se 1 (by rfl) ⟨10231469, by rfl⟩ : syracuseStep 13641959 = 20462939) B20462939
theorem B24570215 : Blo 1594996 24570215 := bstep (se 1 (by rfl) ⟨18427661, by rfl⟩ : syracuseStep 24570215 = 36855323) B36855323
theorem B3410687 : Blo 1594996 3410687 := bstep (se 1 (by rfl) ⟨2558015, by rfl⟩ : syracuseStep 3410687 = 5116031) B5116031
theorem B12118895 : Blo 1594996 12118895 := bstep (se 1 (by rfl) ⟨9089171, by rfl⟩ : syracuseStep 12118895 = 18178343) B18178343
theorem B38817953 : Blo 1594996 38817953 := bstep (se 2 (by rfl) ⟨14556732, by rfl⟩ : syracuseStep 38817953 = 29113465) B29113465
theorem B717820147 : Blo 1594996 717820147 := bstep (se 1 (by rfl) ⟨538365110, by rfl⟩ : syracuseStep 717820147 = 1076730221) B1076730221
theorem B3592871 : Blo 1594996 3592871 := bstep (se 1 (by rfl) ⟨2694653, by rfl⟩ : syracuseStep 3592871 = 5389307) B5389307
theorem B3029375 : Blo 1594996 3029375 := bstep (se 1 (by rfl) ⟨2272031, by rfl⟩ : syracuseStep 3029375 = 4544063) B4544063
theorem B5388767 : Blo 1594996 5388767 := bstep (se 1 (by rfl) ⟨4041575, by rfl⟩ : syracuseStep 5388767 = 8083151) B8083151
theorem B39361079 : Blo 1594996 39361079 := bstep (se 1 (by rfl) ⟨29520809, by rfl⟩ : syracuseStep 39361079 = 59041619) B59041619
theorem B25878635 : Blo 1594996 25878635 := bstep (se 1 (by rfl) ⟨19408976, by rfl⟩ : syracuseStep 25878635 = 38817953) B38817953
theorem B8077967 : Blo 1594996 8077967 := bstep (se 1 (by rfl) ⟨6058475, by rfl⟩ : syracuseStep 8077967 = 12116951) B12116951
theorem B9094639 : Blo 1594996 9094639 := bstep (se 1 (by rfl) ⟨6820979, by rfl⟩ : syracuseStep 9094639 = 13641959) B13641959
theorem B26240719 : Blo 1594996 26240719 := bstep (se 1 (by rfl) ⟨19680539, by rfl⟩ : syracuseStep 26240719 = 39361079) B39361079
theorem B8079263 : Blo 1594996 8079263 := bstep (se 1 (by rfl) ⟨6059447, by rfl⟩ : syracuseStep 8079263 = 12118895) B12118895
theorem B9095165 : Blo 1594996 9095165 := bstep (se 3 (by rfl) ⟨1705343, by rfl⟩ : syracuseStep 9095165 = 3410687) B3410687
theorem B2394281 : Blo 1594996 2394281 := bstep (se 2 (by rfl) ⟨897855, by rfl⟩ : syracuseStep 2394281 = 1795711) B1795711
theorem B2395247 : Blo 1594996 2395247 := bstep (se 1 (by rfl) ⟨1796435, by rfl⟩ : syracuseStep 2395247 = 3592871) B3592871
theorem B16380143 : Blo 1594996 16380143 := bstep (se 1 (by rfl) ⟨12285107, by rfl⟩ : syracuseStep 16380143 = 24570215) B24570215
theorem B2019583 : Blo 1594996 2019583 := bstep (se 1 (by rfl) ⟨1514687, by rfl⟩ : syracuseStep 2019583 = 3029375) B3029375
theorem B3592511 : Blo 1594996 3592511 := bstep (se 1 (by rfl) ⟨2694383, by rfl⟩ : syracuseStep 3592511 = 5388767) B5388767
theorem B957093529 : Blo 1594996 957093529 := bstep (se 2 (by rfl) ⟨358910073, by rfl⟩ : syracuseStep 957093529 = 717820147) B717820147
theorem B17252423 : Blo 1594996 17252423 := bstep (se 1 (by rfl) ⟨12939317, by rfl⟩ : syracuseStep 17252423 = 25878635) B25878635
theorem B10920095 : Blo 1594996 10920095 := bstep (se 1 (by rfl) ⟨8190071, by rfl⟩ : syracuseStep 10920095 = 16380143) B16380143
theorem B6063443 : Blo 1594996 6063443 := bstep (se 1 (by rfl) ⟨4547582, by rfl⟩ : syracuseStep 6063443 = 9095165) B9095165
theorem B12126185 : Blo 1594996 12126185 := bstep (se 2 (by rfl) ⟨4547319, by rfl⟩ : syracuseStep 12126185 = 9094639) B9094639
theorem B2395007 : Blo 1594996 2395007 := bstep (se 1 (by rfl) ⟨1796255, by rfl⟩ : syracuseStep 2395007 = 3592511) B3592511
theorem B5385311 : Blo 1594996 5385311 := bstep (se 1 (by rfl) ⟨4038983, by rfl⟩ : syracuseStep 5385311 = 8077967) B8077967
theorem B5386175 : Blo 1594996 5386175 := bstep (se 1 (by rfl) ⟨4039631, by rfl⟩ : syracuseStep 5386175 = 8079263) B8079263
theorem B2692777 : Blo 1594996 2692777 := bstep (se 2 (by rfl) ⟨1009791, by rfl⟩ : syracuseStep 2692777 = 2019583) B2019583
theorem B1596187 : Blo 1594996 1596187 := bstep (se 1 (by rfl) ⟨1197140, by rfl⟩ : syracuseStep 1596187 = 2394281) B2394281
theorem B1596831 : Blo 1594996 1596831 := bstep (se 1 (by rfl) ⟨1197623, by rfl⟩ : syracuseStep 1596831 = 2395247) B2395247
theorem B1276124705 : Blo 1594996 1276124705 := bstep (se 2 (by rfl) ⟨478546764, by rfl⟩ : syracuseStep 1276124705 = 957093529) B957093529
theorem B34987625 : Blo 1594996 34987625 := bstep (se 2 (by rfl) ⟨13120359, by rfl⟩ : syracuseStep 34987625 = 26240719) B26240719
theorem B11501615 : Blo 1594996 11501615 := bstep (se 1 (by rfl) ⟨8626211, by rfl⟩ : syracuseStep 11501615 = 17252423) B17252423
theorem B3590207 : Blo 1594996 3590207 := bstep (se 1 (by rfl) ⟨2692655, by rfl⟩ : syracuseStep 3590207 = 5385311) B5385311
theorem B3590369 : Blo 1594996 3590369 := bstep (se 2 (by rfl) ⟨1346388, by rfl⟩ : syracuseStep 3590369 = 2692777) B2692777
theorem B850749803 : Blo 1594996 850749803 := bstep (se 1 (by rfl) ⟨638062352, by rfl⟩ : syracuseStep 850749803 = 1276124705) B1276124705
theorem B23325083 : Blo 1594996 23325083 := bstep (se 1 (by rfl) ⟨17493812, by rfl⟩ : syracuseStep 23325083 = 34987625) B34987625
theorem B3590783 : Blo 1594996 3590783 := bstep (se 1 (by rfl) ⟨2693087, by rfl⟩ : syracuseStep 3590783 = 5386175) B5386175
theorem B4042295 : Blo 1594996 4042295 := bstep (se 1 (by rfl) ⟨3031721, by rfl⟩ : syracuseStep 4042295 = 6063443) B6063443
theorem B7280063 : Blo 1594996 7280063 := bstep (se 1 (by rfl) ⟨5460047, by rfl⟩ : syracuseStep 7280063 = 10920095) B10920095
theorem B8084123 : Blo 1594996 8084123 := bstep (se 1 (by rfl) ⟨6063092, by rfl⟩ : syracuseStep 8084123 = 12126185) B12126185
theorem B1596671 : Blo 1594996 1596671 := bstep (se 1 (by rfl) ⟨1197503, by rfl⟩ : syracuseStep 1596671 = 2395007) B2395007
theorem B7667743 : Blo 1594996 7667743 := bstep (se 1 (by rfl) ⟨5750807, by rfl⟩ : syracuseStep 7667743 = 11501615) B11501615
theorem B2393471 : Blo 1594996 2393471 := bstep (se 1 (by rfl) ⟨1795103, by rfl⟩ : syracuseStep 2393471 = 3590207) B3590207
theorem B2393579 : Blo 1594996 2393579 := bstep (se 1 (by rfl) ⟨1795184, by rfl⟩ : syracuseStep 2393579 = 3590369) B3590369
theorem B567166535 : Blo 1594996 567166535 := bstep (se 1 (by rfl) ⟨425374901, by rfl⟩ : syracuseStep 567166535 = 850749803) B850749803
theorem B15550055 : Blo 1594996 15550055 := bstep (se 1 (by rfl) ⟨11662541, by rfl⟩ : syracuseStep 15550055 = 23325083) B23325083
theorem B2393855 : Blo 1594996 2393855 := bstep (se 1 (by rfl) ⟨1795391, by rfl⟩ : syracuseStep 2393855 = 3590783) B3590783
theorem B4853375 : Blo 1594996 4853375 := bstep (se 1 (by rfl) ⟨3640031, by rfl⟩ : syracuseStep 4853375 = 7280063) B7280063
theorem B5389415 : Blo 1594996 5389415 := bstep (se 1 (by rfl) ⟨4042061, by rfl⟩ : syracuseStep 5389415 = 8084123) B8084123
theorem B2694863 : Blo 1594996 2694863 := bstep (se 1 (by rfl) ⟨2021147, by rfl⟩ : syracuseStep 2694863 = 4042295) B4042295
theorem B10223657 : Blo 1594996 10223657 := bstep (se 2 (by rfl) ⟨3833871, by rfl⟩ : syracuseStep 10223657 = 7667743) B7667743
theorem B378111023 : Blo 1594996 378111023 := bstep (se 1 (by rfl) ⟨283583267, by rfl⟩ : syracuseStep 378111023 = 567166535) B567166535
theorem B1796575 : Blo 1594996 1796575 := bstep (se 1 (by rfl) ⟨1347431, by rfl⟩ : syracuseStep 1796575 = 2694863) B2694863
theorem B10366703 : Blo 1594996 10366703 := bstep (se 1 (by rfl) ⟨7775027, by rfl⟩ : syracuseStep 10366703 = 15550055) B15550055
theorem B3592943 : Blo 1594996 3592943 := bstep (se 1 (by rfl) ⟨2694707, by rfl⟩ : syracuseStep 3592943 = 5389415) B5389415
theorem B1595647 : Blo 1594996 1595647 := bstep (se 1 (by rfl) ⟨1196735, by rfl⟩ : syracuseStep 1595647 = 2393471) B2393471
theorem B1595719 : Blo 1594996 1595719 := bstep (se 1 (by rfl) ⟨1196789, by rfl⟩ : syracuseStep 1595719 = 2393579) B2393579
theorem B1595903 : Blo 1594996 1595903 := bstep (se 1 (by rfl) ⟨1196927, by rfl⟩ : syracuseStep 1595903 = 2393855) B2393855
theorem B3235583 : Blo 1594996 3235583 := bstep (se 1 (by rfl) ⟨2426687, by rfl⟩ : syracuseStep 3235583 = 4853375) B4853375
theorem B6815771 : Blo 1594996 6815771 := bstep (se 1 (by rfl) ⟨5111828, by rfl⟩ : syracuseStep 6815771 = 10223657) B10223657
theorem B8628221 : Blo 1594996 8628221 := bstep (se 3 (by rfl) ⟨1617791, by rfl⟩ : syracuseStep 8628221 = 3235583) B3235583
theorem B2395295 : Blo 1594996 2395295 := bstep (se 1 (by rfl) ⟨1796471, by rfl⟩ : syracuseStep 2395295 = 3592943) B3592943
theorem B2395433 : Blo 1594996 2395433 := bstep (se 2 (by rfl) ⟨898287, by rfl⟩ : syracuseStep 2395433 = 1796575) B1796575
theorem B6911135 : Blo 1594996 6911135 := bstep (se 1 (by rfl) ⟨5183351, by rfl⟩ : syracuseStep 6911135 = 10366703) B10366703
theorem B252074015 : Blo 1594996 252074015 := bstep (se 1 (by rfl) ⟨189055511, by rfl⟩ : syracuseStep 252074015 = 378111023) B378111023
theorem B5752147 : Blo 1594996 5752147 := bstep (se 1 (by rfl) ⟨4314110, by rfl⟩ : syracuseStep 5752147 = 8628221) B8628221
theorem B4607423 : Blo 1594996 4607423 := bstep (se 1 (by rfl) ⟨3455567, by rfl⟩ : syracuseStep 4607423 = 6911135) B6911135
theorem B4543847 : Blo 1594996 4543847 := bstep (se 1 (by rfl) ⟨3407885, by rfl⟩ : syracuseStep 4543847 = 6815771) B6815771
theorem B168049343 : Blo 1594996 168049343 := bstep (se 1 (by rfl) ⟨126037007, by rfl⟩ : syracuseStep 168049343 = 252074015) B252074015
theorem B1596863 : Blo 1594996 1596863 := bstep (se 1 (by rfl) ⟨1197647, by rfl⟩ : syracuseStep 1596863 = 2395295) B2395295
theorem B1596955 : Blo 1594996 1596955 := bstep (se 1 (by rfl) ⟨1197716, by rfl⟩ : syracuseStep 1596955 = 2395433) B2395433
theorem B7669529 : Blo 1594996 7669529 := bstep (se 2 (by rfl) ⟨2876073, by rfl⟩ : syracuseStep 7669529 = 5752147) B5752147
theorem B3029231 : Blo 1594996 3029231 := bstep (se 1 (by rfl) ⟨2271923, by rfl⟩ : syracuseStep 3029231 = 4543847) B4543847
theorem B112032895 : Blo 1594996 112032895 := bstep (se 1 (by rfl) ⟨84024671, by rfl⟩ : syracuseStep 112032895 = 168049343) B168049343
theorem B3071615 : Blo 1594996 3071615 := bstep (se 1 (by rfl) ⟨2303711, by rfl⟩ : syracuseStep 3071615 = 4607423) B4607423
theorem B5113019 : Blo 1594996 5113019 := bstep (se 1 (by rfl) ⟨3834764, by rfl⟩ : syracuseStep 5113019 = 7669529) B7669529
theorem B2019487 : Blo 1594996 2019487 := bstep (se 1 (by rfl) ⟨1514615, by rfl⟩ : syracuseStep 2019487 = 3029231) B3029231
theorem B149377193 : Blo 1594996 149377193 := bstep (se 2 (by rfl) ⟨56016447, by rfl⟩ : syracuseStep 149377193 = 112032895) B112032895
theorem B8190973 : Blo 1594996 8190973 := bstep (se 3 (by rfl) ⟨1535807, by rfl⟩ : syracuseStep 8190973 = 3071615) B3071615
theorem B3408679 : Blo 1594996 3408679 := bstep (se 1 (by rfl) ⟨2556509, by rfl⟩ : syracuseStep 3408679 = 5113019) B5113019
theorem B99584795 : Blo 1594996 99584795 := bstep (se 1 (by rfl) ⟨74688596, by rfl⟩ : syracuseStep 99584795 = 149377193) B149377193
theorem B43685189 : Blo 1594996 43685189 := bstep (se 4 (by rfl) ⟨4095486, by rfl⟩ : syracuseStep 43685189 = 8190973) B8190973
theorem B2692649 : Blo 1594996 2692649 := bstep (se 2 (by rfl) ⟨1009743, by rfl⟩ : syracuseStep 2692649 = 2019487) B2019487
theorem B29123459 : Blo 1594996 29123459 := bstep (se 1 (by rfl) ⟨21842594, by rfl⟩ : syracuseStep 29123459 = 43685189) B43685189
theorem B1795099 : Blo 1594996 1795099 := bstep (se 1 (by rfl) ⟨1346324, by rfl⟩ : syracuseStep 1795099 = 2692649) B2692649
theorem B66389863 : Blo 1594996 66389863 := bstep (se 1 (by rfl) ⟨49792397, by rfl⟩ : syracuseStep 66389863 = 99584795) B99584795
theorem B4544905 : Blo 1594996 4544905 := bstep (se 2 (by rfl) ⟨1704339, by rfl⟩ : syracuseStep 4544905 = 3408679) B3408679
theorem B19415639 : Blo 1594996 19415639 := bstep (se 1 (by rfl) ⟨14561729, by rfl⟩ : syracuseStep 19415639 = 29123459) B29123459
theorem B2393465 : Blo 1594996 2393465 := bstep (se 2 (by rfl) ⟨897549, by rfl⟩ : syracuseStep 2393465 = 1795099) B1795099
theorem B88519817 : Blo 1594996 88519817 := bstep (se 2 (by rfl) ⟨33194931, by rfl⟩ : syracuseStep 88519817 = 66389863) B66389863
theorem B6059873 : Blo 1594996 6059873 := bstep (se 2 (by rfl) ⟨2272452, by rfl⟩ : syracuseStep 6059873 = 4544905) B4544905
theorem B12943759 : Blo 1594996 12943759 := bstep (se 1 (by rfl) ⟨9707819, by rfl⟩ : syracuseStep 12943759 = 19415639) B19415639
theorem B4039915 : Blo 1594996 4039915 := bstep (se 1 (by rfl) ⟨3029936, by rfl⟩ : syracuseStep 4039915 = 6059873) B6059873
theorem B59013211 : Blo 1594996 59013211 := bstep (se 1 (by rfl) ⟨44259908, by rfl⟩ : syracuseStep 59013211 = 88519817) B88519817
theorem B1595643 : Blo 1594996 1595643 := bstep (se 1 (by rfl) ⟨1196732, by rfl⟩ : syracuseStep 1595643 = 2393465) B2393465
theorem B78684281 : Blo 1594996 78684281 := bstep (se 2 (by rfl) ⟨29506605, by rfl⟩ : syracuseStep 78684281 = 59013211) B59013211
theorem B5386553 : Blo 1594996 5386553 := bstep (se 2 (by rfl) ⟨2019957, by rfl⟩ : syracuseStep 5386553 = 4039915) B4039915
theorem B17258345 : Blo 1594996 17258345 := bstep (se 2 (by rfl) ⟨6471879, by rfl⟩ : syracuseStep 17258345 = 12943759) B12943759
theorem B52456187 : Blo 1594996 52456187 := bstep (se 1 (by rfl) ⟨39342140, by rfl⟩ : syracuseStep 52456187 = 78684281) B78684281
theorem B3591035 : Blo 1594996 3591035 := bstep (se 1 (by rfl) ⟨2693276, by rfl⟩ : syracuseStep 3591035 = 5386553) B5386553
theorem B11505563 : Blo 1594996 11505563 := bstep (se 1 (by rfl) ⟨8629172, by rfl⟩ : syracuseStep 11505563 = 17258345) B17258345
theorem B2394023 : Blo 1594996 2394023 := bstep (se 1 (by rfl) ⟨1795517, by rfl⟩ : syracuseStep 2394023 = 3591035) B3591035
theorem B7670375 : Blo 1594996 7670375 := bstep (se 1 (by rfl) ⟨5752781, by rfl⟩ : syracuseStep 7670375 = 11505563) B11505563
theorem B34970791 : Blo 1594996 34970791 := bstep (se 1 (by rfl) ⟨26228093, by rfl⟩ : syracuseStep 34970791 = 52456187) B52456187
theorem B5113583 : Blo 1594996 5113583 := bstep (se 1 (by rfl) ⟨3835187, by rfl⟩ : syracuseStep 5113583 = 7670375) B7670375
theorem B1596015 : Blo 1594996 1596015 := bstep (se 1 (by rfl) ⟨1197011, by rfl⟩ : syracuseStep 1596015 = 2394023) B2394023
theorem B46627721 : Blo 1594996 46627721 := bstep (se 2 (by rfl) ⟨17485395, by rfl⟩ : syracuseStep 46627721 = 34970791) B34970791
theorem B3409055 : Blo 1594996 3409055 := bstep (se 1 (by rfl) ⟨2556791, by rfl⟩ : syracuseStep 3409055 = 5113583) B5113583
theorem B31085147 : Blo 1594996 31085147 := bstep (se 1 (by rfl) ⟨23313860, by rfl⟩ : syracuseStep 31085147 = 46627721) B46627721
theorem B2272703 : Blo 1594996 2272703 := bstep (se 1 (by rfl) ⟨1704527, by rfl⟩ : syracuseStep 2272703 = 3409055) B3409055
theorem B82893725 : Blo 1594996 82893725 := bstep (se 3 (by rfl) ⟨15542573, by rfl⟩ : syracuseStep 82893725 = 31085147) B31085147
theorem B6060541 : Blo 1594996 6060541 := bstep (se 3 (by rfl) ⟨1136351, by rfl⟩ : syracuseStep 6060541 = 2272703) B2272703
theorem B55262483 : Blo 1594996 55262483 := bstep (se 1 (by rfl) ⟨41446862, by rfl⟩ : syracuseStep 55262483 = 82893725) B82893725
theorem B36841655 : Blo 1594996 36841655 := bstep (se 1 (by rfl) ⟨27631241, by rfl⟩ : syracuseStep 36841655 = 55262483) B55262483
theorem B8080721 : Blo 1594996 8080721 := bstep (se 2 (by rfl) ⟨3030270, by rfl⟩ : syracuseStep 8080721 = 6060541) B6060541
theorem B24561103 : Blo 1594996 24561103 := bstep (se 1 (by rfl) ⟨18420827, by rfl⟩ : syracuseStep 24561103 = 36841655) B36841655
theorem B5387147 : Blo 1594996 5387147 := bstep (se 1 (by rfl) ⟨4040360, by rfl⟩ : syracuseStep 5387147 = 8080721) B8080721
theorem B3591431 : Blo 1594996 3591431 := bstep (se 1 (by rfl) ⟨2693573, by rfl⟩ : syracuseStep 3591431 = 5387147) B5387147
theorem B32748137 : Blo 1594996 32748137 := bstep (se 2 (by rfl) ⟨12280551, by rfl⟩ : syracuseStep 32748137 = 24561103) B24561103
theorem B21832091 : Blo 1594996 21832091 := bstep (se 1 (by rfl) ⟨16374068, by rfl⟩ : syracuseStep 21832091 = 32748137) B32748137
theorem B2394287 : Blo 1594996 2394287 := bstep (se 1 (by rfl) ⟨1795715, by rfl⟩ : syracuseStep 2394287 = 3591431) B3591431
theorem B14554727 : Blo 1594996 14554727 := bstep (se 1 (by rfl) ⟨10916045, by rfl⟩ : syracuseStep 14554727 = 21832091) B21832091
theorem B1596191 : Blo 1594996 1596191 := bstep (se 1 (by rfl) ⟨1197143, by rfl⟩ : syracuseStep 1596191 = 2394287) B2394287
theorem B9703151 : Blo 1594996 9703151 := bstep (se 1 (by rfl) ⟨7277363, by rfl⟩ : syracuseStep 9703151 = 14554727) B14554727
theorem B6468767 : Blo 1594996 6468767 := bstep (se 1 (by rfl) ⟨4851575, by rfl⟩ : syracuseStep 6468767 = 9703151) B9703151
theorem B4312511 : Blo 1594996 4312511 := bstep (se 1 (by rfl) ⟨3234383, by rfl⟩ : syracuseStep 4312511 = 6468767) B6468767
theorem B2875007 : Blo 1594996 2875007 := bstep (se 1 (by rfl) ⟨2156255, by rfl⟩ : syracuseStep 2875007 = 4312511) B4312511
theorem B1916671 : Blo 1594996 1916671 := bstep (se 1 (by rfl) ⟨1437503, by rfl⟩ : syracuseStep 1916671 = 2875007) B2875007
theorem B2555561 : Blo 1594996 2555561 := bstep (se 2 (by rfl) ⟨958335, by rfl⟩ : syracuseStep 2555561 = 1916671) B1916671
theorem B6814829 : Blo 1594996 6814829 := bstep (se 3 (by rfl) ⟨1277780, by rfl⟩ : syracuseStep 6814829 = 2555561) B2555561
theorem B4543219 : Blo 1594996 4543219 := bstep (se 1 (by rfl) ⟨3407414, by rfl⟩ : syracuseStep 4543219 = 6814829) B6814829
theorem B6057625 : Blo 1594996 6057625 := bstep (se 2 (by rfl) ⟨2271609, by rfl⟩ : syracuseStep 6057625 = 4543219) B4543219
theorem B8076833 : Blo 1594996 8076833 := bstep (se 2 (by rfl) ⟨3028812, by rfl⟩ : syracuseStep 8076833 = 6057625) B6057625
theorem B5384555 : Blo 1594996 5384555 := bstep (se 1 (by rfl) ⟨4038416, by rfl⟩ : syracuseStep 5384555 = 8076833) B8076833
theorem B3589703 : Blo 1594996 3589703 := bstep (se 1 (by rfl) ⟨2692277, by rfl⟩ : syracuseStep 3589703 = 5384555) B5384555
theorem B2393135 : Blo 1594996 2393135 := bstep (se 1 (by rfl) ⟨1794851, by rfl⟩ : syracuseStep 2393135 = 3589703) B3589703
theorem B1595423 : Blo 1594996 1595423 := bstep (se 1 (by rfl) ⟨1196567, by rfl⟩ : syracuseStep 1595423 = 2393135) B2393135

theorem C0 (j : ℕ) (h1 : 398749 ≤ j) (h2 : j ≤ 399248) : Blo 1594996 (4 * j + 3) := by
  interval_cases j
  · exact B1594999
  · exact B1595003
  · exact B1595007
  · exact B1595011
  · exact B1595015
  · exact B1595019
  · exact B1595023
  · exact B1595027
  · exact B1595031
  · exact B1595035
  · exact B1595039
  · exact B1595043
  · exact B1595047
  · exact B1595051
  · exact B1595055
  · exact B1595059
  · exact B1595063
  · exact B1595067
  · exact B1595071
  · exact B1595075
  · exact B1595079
  · exact B1595083
  · exact B1595087
  · exact B1595091
  · exact B1595095
  · exact B1595099
  · exact B1595103
  · exact B1595107
  · exact B1595111
  · exact B1595115
  · exact B1595119
  · exact B1595123
  · exact B1595127
  · exact B1595131
  · exact B1595135
  · exact B1595139
  · exact B1595143
  · exact B1595147
  · exact B1595151
  · exact B1595155
  · exact B1595159
  · exact B1595163
  · exact B1595167
  · exact B1595171
  · exact B1595175
  · exact B1595179
  · exact B1595183
  · exact B1595187
  · exact B1595191
  · exact B1595195
  · exact B1595199
  · exact B1595203
  · exact B1595207
  · exact B1595211
  · exact B1595215
  · exact B1595219
  · exact B1595223
  · exact B1595227
  · exact B1595231
  · exact B1595235
  · exact B1595239
  · exact B1595243
  · exact B1595247
  · exact B1595251
  · exact B1595255
  · exact B1595259
  · exact B1595263
  · exact B1595267
  · exact B1595271
  · exact B1595275
  · exact B1595279
  · exact B1595283
  · exact B1595287
  · exact B1595291
  · exact B1595295
  · exact B1595299
  · exact B1595303
  · exact B1595307
  · exact B1595311
  · exact B1595315
  · exact B1595319
  · exact B1595323
  · exact B1595327
  · exact B1595331
  · exact B1595335
  · exact B1595339
  · exact B1595343
  · exact B1595347
  · exact B1595351
  · exact B1595355
  · exact B1595359
  · exact B1595363
  · exact B1595367
  · exact B1595371
  · exact B1595375
  · exact B1595379
  · exact B1595383
  · exact B1595387
  · exact B1595391
  · exact B1595395
  · exact B1595399
  · exact B1595403
  · exact B1595407
  · exact B1595411
  · exact B1595415
  · exact B1595419
  · exact B1595423
  · exact B1595427
  · exact B1595431
  · exact B1595435
  · exact B1595439
  · exact B1595443
  · exact B1595447
  · exact B1595451
  · exact B1595455
  · exact B1595459
  · exact B1595463
  · exact B1595467
  · exact B1595471
  · exact B1595475
  · exact B1595479
  · exact B1595483
  · exact B1595487
  · exact B1595491
  · exact B1595495
  · exact B1595499
  · exact B1595503
  · exact B1595507
  · exact B1595511
  · exact B1595515
  · exact B1595519
  · exact B1595523
  · exact B1595527
  · exact B1595531
  · exact B1595535
  · exact B1595539
  · exact B1595543
  · exact B1595547
  · exact B1595551
  · exact B1595555
  · exact B1595559
  · exact B1595563
  · exact B1595567
  · exact B1595571
  · exact B1595575
  · exact B1595579
  · exact B1595583
  · exact B1595587
  · exact B1595591
  · exact B1595595
  · exact B1595599
  · exact B1595603
  · exact B1595607
  · exact B1595611
  · exact B1595615
  · exact B1595619
  · exact B1595623
  · exact B1595627
  · exact B1595631
  · exact B1595635
  · exact B1595639
  · exact B1595643
  · exact B1595647
  · exact B1595651
  · exact B1595655
  · exact B1595659
  · exact B1595663
  · exact B1595667
  · exact B1595671
  · exact B1595675
  · exact B1595679
  · exact B1595683
  · exact B1595687
  · exact B1595691
  · exact B1595695
  · exact B1595699
  · exact B1595703
  · exact B1595707
  · exact B1595711
  · exact B1595715
  · exact B1595719
  · exact B1595723
  · exact B1595727
  · exact B1595731
  · exact B1595735
  · exact B1595739
  · exact B1595743
  · exact B1595747
  · exact B1595751
  · exact B1595755
  · exact B1595759
  · exact B1595763
  · exact B1595767
  · exact B1595771
  · exact B1595775
  · exact B1595779
  · exact B1595783
  · exact B1595787
  · exact B1595791
  · exact B1595795
  · exact B1595799
  · exact B1595803
  · exact B1595807
  · exact B1595811
  · exact B1595815
  · exact B1595819
  · exact B1595823
  · exact B1595827
  · exact B1595831
  · exact B1595835
  · exact B1595839
  · exact B1595843
  · exact B1595847
  · exact B1595851
  · exact B1595855
  · exact B1595859
  · exact B1595863
  · exact B1595867
  · exact B1595871
  · exact B1595875
  · exact B1595879
  · exact B1595883
  · exact B1595887
  · exact B1595891
  · exact B1595895
  · exact B1595899
  · exact B1595903
  · exact B1595907
  · exact B1595911
  · exact B1595915
  · exact B1595919
  · exact B1595923
  · exact B1595927
  · exact B1595931
  · exact B1595935
  · exact B1595939
  · exact B1595943
  · exact B1595947
  · exact B1595951
  · exact B1595955
  · exact B1595959
  · exact B1595963
  · exact B1595967
  · exact B1595971
  · exact B1595975
  · exact B1595979
  · exact B1595983
  · exact B1595987
  · exact B1595991
  · exact B1595995
  · exact B1595999
  · exact B1596003
  · exact B1596007
  · exact B1596011
  · exact B1596015
  · exact B1596019
  · exact B1596023
  · exact B1596027
  · exact B1596031
  · exact B1596035
  · exact B1596039
  · exact B1596043
  · exact B1596047
  · exact B1596051
  · exact B1596055
  · exact B1596059
  · exact B1596063
  · exact B1596067
  · exact B1596071
  · exact B1596075
  · exact B1596079
  · exact B1596083
  · exact B1596087
  · exact B1596091
  · exact B1596095
  · exact B1596099
  · exact B1596103
  · exact B1596107
  · exact B1596111
  · exact B1596115
  · exact B1596119
  · exact B1596123
  · exact B1596127
  · exact B1596131
  · exact B1596135
  · exact B1596139
  · exact B1596143
  · exact B1596147
  · exact B1596151
  · exact B1596155
  · exact B1596159
  · exact B1596163
  · exact B1596167
  · exact B1596171
  · exact B1596175
  · exact B1596179
  · exact B1596183
  · exact B1596187
  · exact B1596191
  · exact B1596195
  · exact B1596199
  · exact B1596203
  · exact B1596207
  · exact B1596211
  · exact B1596215
  · exact B1596219
  · exact B1596223
  · exact B1596227
  · exact B1596231
  · exact B1596235
  · exact B1596239
  · exact B1596243
  · exact B1596247
  · exact B1596251
  · exact B1596255
  · exact B1596259
  · exact B1596263
  · exact B1596267
  · exact B1596271
  · exact B1596275
  · exact B1596279
  · exact B1596283
  · exact B1596287
  · exact B1596291
  · exact B1596295
  · exact B1596299
  · exact B1596303
  · exact B1596307
  · exact B1596311
  · exact B1596315
  · exact B1596319
  · exact B1596323
  · exact B1596327
  · exact B1596331
  · exact B1596335
  · exact B1596339
  · exact B1596343
  · exact B1596347
  · exact B1596351
  · exact B1596355
  · exact B1596359
  · exact B1596363
  · exact B1596367
  · exact B1596371
  · exact B1596375
  · exact B1596379
  · exact B1596383
  · exact B1596387
  · exact B1596391
  · exact B1596395
  · exact B1596399
  · exact B1596403
  · exact B1596407
  · exact B1596411
  · exact B1596415
  · exact B1596419
  · exact B1596423
  · exact B1596427
  · exact B1596431
  · exact B1596435
  · exact B1596439
  · exact B1596443
  · exact B1596447
  · exact B1596451
  · exact B1596455
  · exact B1596459
  · exact B1596463
  · exact B1596467
  · exact B1596471
  · exact B1596475
  · exact B1596479
  · exact B1596483
  · exact B1596487
  · exact B1596491
  · exact B1596495
  · exact B1596499
  · exact B1596503
  · exact B1596507
  · exact B1596511
  · exact B1596515
  · exact B1596519
  · exact B1596523
  · exact B1596527
  · exact B1596531
  · exact B1596535
  · exact B1596539
  · exact B1596543
  · exact B1596547
  · exact B1596551
  · exact B1596555
  · exact B1596559
  · exact B1596563
  · exact B1596567
  · exact B1596571
  · exact B1596575
  · exact B1596579
  · exact B1596583
  · exact B1596587
  · exact B1596591
  · exact B1596595
  · exact B1596599
  · exact B1596603
  · exact B1596607
  · exact B1596611
  · exact B1596615
  · exact B1596619
  · exact B1596623
  · exact B1596627
  · exact B1596631
  · exact B1596635
  · exact B1596639
  · exact B1596643
  · exact B1596647
  · exact B1596651
  · exact B1596655
  · exact B1596659
  · exact B1596663
  · exact B1596667
  · exact B1596671
  · exact B1596675
  · exact B1596679
  · exact B1596683
  · exact B1596687
  · exact B1596691
  · exact B1596695
  · exact B1596699
  · exact B1596703
  · exact B1596707
  · exact B1596711
  · exact B1596715
  · exact B1596719
  · exact B1596723
  · exact B1596727
  · exact B1596731
  · exact B1596735
  · exact B1596739
  · exact B1596743
  · exact B1596747
  · exact B1596751
  · exact B1596755
  · exact B1596759
  · exact B1596763
  · exact B1596767
  · exact B1596771
  · exact B1596775
  · exact B1596779
  · exact B1596783
  · exact B1596787
  · exact B1596791
  · exact B1596795
  · exact B1596799
  · exact B1596803
  · exact B1596807
  · exact B1596811
  · exact B1596815
  · exact B1596819
  · exact B1596823
  · exact B1596827
  · exact B1596831
  · exact B1596835
  · exact B1596839
  · exact B1596843
  · exact B1596847
  · exact B1596851
  · exact B1596855
  · exact B1596859
  · exact B1596863
  · exact B1596867
  · exact B1596871
  · exact B1596875
  · exact B1596879
  · exact B1596883
  · exact B1596887
  · exact B1596891
  · exact B1596895
  · exact B1596899
  · exact B1596903
  · exact B1596907
  · exact B1596911
  · exact B1596915
  · exact B1596919
  · exact B1596923
  · exact B1596927
  · exact B1596931
  · exact B1596935
  · exact B1596939
  · exact B1596943
  · exact B1596947
  · exact B1596951
  · exact B1596955
  · exact B1596959
  · exact B1596963
  · exact B1596967
  · exact B1596971
  · exact B1596975
  · exact B1596979
  · exact B1596983
  · exact B1596987
  · exact B1596991
  · exact B1596995

theorem solution (m : ℕ) (hlo : 1594996 ≤ m) (hhi : m ≤ 1596996) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 398749 ≤ j := by omega
    have hj2 : j ≤ 399248 := by omega
    have hb : Blo 1594996 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
