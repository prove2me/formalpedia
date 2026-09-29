-- Prove2me | solution 1 for syracuse_descends_range_1644021_1646021
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:16:42.4922+00:00
-- url     : https://prove2.me/submissions/80e6c42f-f5c6-4ef0-8056-a6a66de1bf46

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


theorem B3702797 : Blo 1644021 3702797 := bbase (se 3 (by rfl) ⟨694274, by rfl⟩ : syracuseStep 3702797 = 1388549) (by norm_num)
theorem B4161557 : Blo 1644021 4161557 := bbase (se 6 (by rfl) ⟨97536, by rfl⟩ : syracuseStep 4161557 = 195073) (by norm_num)
theorem B3006485 : Blo 1644021 3006485 := bbase (se 6 (by rfl) ⟨70464, by rfl⟩ : syracuseStep 3006485 = 140929) (by norm_num)
theorem B1851421 : Blo 1644021 1851421 := bbase (se 3 (by rfl) ⟨347141, by rfl⟩ : syracuseStep 1851421 = 694283) (by norm_num)
theorem B2777125 : Blo 1644021 2777125 := bbase (se 4 (by rfl) ⟨260355, by rfl⟩ : syracuseStep 2777125 = 520711) (by norm_num)
theorem B2080829 : Blo 1644021 2080829 := bbase (se 3 (by rfl) ⟨390155, by rfl⟩ : syracuseStep 2080829 = 780311) (by norm_num)
theorem B1851457 : Blo 1644021 1851457 := bbase (se 2 (by rfl) ⟨694296, by rfl⟩ : syracuseStep 1851457 = 1388593) (by norm_num)
theorem B3121229 : Blo 1644021 3121229 := bbase (se 3 (by rfl) ⟨585230, by rfl⟩ : syracuseStep 3121229 = 1170461) (by norm_num)
theorem B3702869 : Blo 1644021 3702869 := bbase (se 8 (by rfl) ⟨21696, by rfl⟩ : syracuseStep 3702869 = 43393) (by norm_num)
theorem B5554277 : Blo 1644021 5554277 := bbase (se 4 (by rfl) ⟨520713, by rfl⟩ : syracuseStep 5554277 = 1041427) (by norm_num)
theorem B1851493 : Blo 1644021 1851493 := bbase (se 4 (by rfl) ⟨173577, by rfl⟩ : syracuseStep 1851493 = 347155) (by norm_num)
theorem B2080885 : Blo 1644021 2080885 := bbase (se 5 (by rfl) ⟨97541, by rfl⟩ : syracuseStep 2080885 = 195083) (by norm_num)
theorem B2777213 : Blo 1644021 2777213 := bbase (se 3 (by rfl) ⟨520727, by rfl⟩ : syracuseStep 2777213 = 1041455) (by norm_num)
theorem B1851529 : Blo 1644021 1851529 := bbase (se 2 (by rfl) ⟨694323, by rfl⟩ : syracuseStep 1851529 = 1388647) (by norm_num)
theorem B1876117 : Blo 1644021 1876117 := bbase (se 6 (by rfl) ⟨43971, by rfl⟩ : syracuseStep 1876117 = 87943) (by norm_num)
theorem B3702941 : Blo 1644021 3702941 := bbase (se 3 (by rfl) ⟨694301, by rfl⟩ : syracuseStep 3702941 = 1388603) (by norm_num)
theorem B1851565 : Blo 1644021 1851565 := bbase (se 3 (by rfl) ⟨347168, by rfl⟩ : syracuseStep 1851565 = 694337) (by norm_num)
theorem B2343109 : Blo 1644021 2343109 := bbase (se 4 (by rfl) ⟨219666, by rfl⟩ : syracuseStep 2343109 = 439333) (by norm_num)
theorem B1851601 : Blo 1644021 1851601 := bbase (se 2 (by rfl) ⟨694350, by rfl⟩ : syracuseStep 1851601 = 1388701) (by norm_num)
theorem B2080981 : Blo 1644021 2080981 := bbase (se 7 (by rfl) ⟨24386, by rfl⟩ : syracuseStep 2080981 = 48773) (by norm_num)
theorem B3703013 : Blo 1644021 3703013 := bbase (se 4 (by rfl) ⟨347157, by rfl⟩ : syracuseStep 3703013 = 694315) (by norm_num)
theorem B12484853 : Blo 1644021 12484853 := bbase (se 5 (by rfl) ⟨585227, by rfl⟩ : syracuseStep 12484853 = 1170455) (by norm_num)
theorem B1851637 : Blo 1644021 1851637 := bbase (se 5 (by rfl) ⟨86795, by rfl⟩ : syracuseStep 1851637 = 173591) (by norm_num)
theorem B2777341 : Blo 1644021 2777341 := bbase (se 3 (by rfl) ⟨520751, by rfl⟩ : syracuseStep 2777341 = 1041503) (by norm_num)
theorem B2466053 : Blo 1644021 2466053 := bbase (se 4 (by rfl) ⟨231192, by rfl⟩ : syracuseStep 2466053 = 462385) (by norm_num)
theorem B2138393 : Blo 1644021 2138393 := bbase (se 2 (by rfl) ⟨801897, by rfl⟩ : syracuseStep 2138393 = 1603795) (by norm_num)
theorem B1851673 : Blo 1644021 1851673 := bbase (se 2 (by rfl) ⟨694377, by rfl⟩ : syracuseStep 1851673 = 1388755) (by norm_num)
theorem B2466077 : Blo 1644021 2466077 := bbase (se 3 (by rfl) ⟨462389, by rfl⟩ : syracuseStep 2466077 = 924779) (by norm_num)
theorem B3703085 : Blo 1644021 3703085 := bbase (se 3 (by rfl) ⟨694328, by rfl⟩ : syracuseStep 3703085 = 1388657) (by norm_num)
theorem B2466101 : Blo 1644021 2466101 := bbase (se 5 (by rfl) ⟨115598, by rfl⟩ : syracuseStep 2466101 = 231197) (by norm_num)
theorem B1851709 : Blo 1644021 1851709 := bbase (se 3 (by rfl) ⟨347195, by rfl⟩ : syracuseStep 1851709 = 694391) (by norm_num)
theorem B8323397 : Blo 1644021 8323397 := bbase (se 4 (by rfl) ⟨780318, by rfl⟩ : syracuseStep 8323397 = 1560637) (by norm_num)
theorem B7119173 : Blo 1644021 7119173 := bbase (se 4 (by rfl) ⟨667422, by rfl⟩ : syracuseStep 7119173 = 1334845) (by norm_num)
theorem B3752261 : Blo 1644021 3752261 := bbase (se 4 (by rfl) ⟨351774, by rfl⟩ : syracuseStep 3752261 = 703549) (by norm_num)
theorem B4686149 : Blo 1644021 4686149 := bbase (se 4 (by rfl) ⟨439326, by rfl⟩ : syracuseStep 4686149 = 878653) (by norm_num)
theorem B2466125 : Blo 1644021 2466125 := bbase (se 3 (by rfl) ⟨462398, by rfl⟩ : syracuseStep 2466125 = 924797) (by norm_num)
theorem B2777429 : Blo 1644021 2777429 := bbase (se 10 (by rfl) ⟨4068, by rfl⟩ : syracuseStep 2777429 = 8137) (by norm_num)
theorem B1851745 : Blo 1644021 1851745 := bbase (se 2 (by rfl) ⟨694404, by rfl⟩ : syracuseStep 1851745 = 1388809) (by norm_num)
theorem B2466149 : Blo 1644021 2466149 := bbase (se 4 (by rfl) ⟨231201, by rfl⟩ : syracuseStep 2466149 = 462403) (by norm_num)
theorem B4161901 : Blo 1644021 4161901 := bbase (se 3 (by rfl) ⟨780356, by rfl⟩ : syracuseStep 4161901 = 1560713) (by norm_num)
theorem B3121517 : Blo 1644021 3121517 := bbase (se 3 (by rfl) ⟨585284, by rfl⟩ : syracuseStep 3121517 = 1170569) (by norm_num)
theorem B3703157 : Blo 1644021 3703157 := bbase (se 5 (by rfl) ⟨173585, by rfl⟩ : syracuseStep 3703157 = 347171) (by norm_num)
theorem B2466173 : Blo 1644021 2466173 := bbase (se 3 (by rfl) ⟨462407, by rfl⟩ : syracuseStep 2466173 = 924815) (by norm_num)
theorem B2081153 : Blo 1644021 2081153 := bbase (se 2 (by rfl) ⟨780432, by rfl⟩ : syracuseStep 2081153 = 1560865) (by norm_num)
theorem B2466197 : Blo 1644021 2466197 := bbase (se 6 (by rfl) ⟨57801, by rfl⟩ : syracuseStep 2466197 = 115603) (by norm_num)
theorem B2343325 : Blo 1644021 2343325 := bbase (se 3 (by rfl) ⟨439373, by rfl⟩ : syracuseStep 2343325 = 878747) (by norm_num)
theorem B2466221 : Blo 1644021 2466221 := bbase (se 3 (by rfl) ⟨462416, by rfl⟩ : syracuseStep 2466221 = 924833) (by norm_num)
theorem B8896949 : Blo 1644021 8896949 := bbase (se 5 (by rfl) ⟨417044, by rfl⟩ : syracuseStep 8896949 = 834089) (by norm_num)
theorem B2081209 : Blo 1644021 2081209 := bbase (se 2 (by rfl) ⟨780453, by rfl⟩ : syracuseStep 2081209 = 1560907) (by norm_num)
theorem B3703229 : Blo 1644021 3703229 := bbase (se 3 (by rfl) ⟨694355, by rfl⟩ : syracuseStep 3703229 = 1388711) (by norm_num)
theorem B2466245 : Blo 1644021 2466245 := bbase (se 4 (by rfl) ⟨231210, by rfl⟩ : syracuseStep 2466245 = 462421) (by norm_num)
theorem B2777557 : Blo 1644021 2777557 := bbase (se 7 (by rfl) ⟨32549, by rfl⟩ : syracuseStep 2777557 = 65099) (by norm_num)
theorem B2466269 : Blo 1644021 2466269 := bbase (se 3 (by rfl) ⟨462425, by rfl⟩ : syracuseStep 2466269 = 924851) (by norm_num)
theorem B4162013 : Blo 1644021 4162013 := bbase (se 3 (by rfl) ⟨780377, by rfl⟩ : syracuseStep 4162013 = 1560755) (by norm_num)
theorem B2466293 : Blo 1644021 2466293 := bbase (se 5 (by rfl) ⟨115607, by rfl⟩ : syracuseStep 2466293 = 231215) (by norm_num)
theorem B5071349 : Blo 1644021 5071349 := bbase (se 5 (by rfl) ⟨237719, by rfl⟩ : syracuseStep 5071349 = 475439) (by norm_num)
theorem B3121669 : Blo 1644021 3121669 := bbase (se 4 (by rfl) ⟨292656, by rfl⟩ : syracuseStep 3121669 = 585313) (by norm_num)
theorem B3703301 : Blo 1644021 3703301 := bbase (se 4 (by rfl) ⟨347184, by rfl⟩ : syracuseStep 3703301 = 694369) (by norm_num)
theorem B2466317 : Blo 1644021 2466317 := bbase (se 3 (by rfl) ⟨462434, by rfl⟩ : syracuseStep 2466317 = 924869) (by norm_num)
theorem B5554709 : Blo 1644021 5554709 := bbase (se 6 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 5554709 = 260377) (by norm_num)
theorem B2081305 : Blo 1644021 2081305 := bbase (se 2 (by rfl) ⟨780489, by rfl⟩ : syracuseStep 2081305 = 1560979) (by norm_num)
theorem B2466341 : Blo 1644021 2466341 := bbase (se 4 (by rfl) ⟨231219, by rfl⟩ : syracuseStep 2466341 = 462439) (by norm_num)
theorem B6668837 : Blo 1644021 6668837 := bbase (se 4 (by rfl) ⟨625203, by rfl⟩ : syracuseStep 6668837 = 1250407) (by norm_num)
theorem B2777645 : Blo 1644021 2777645 := bbase (se 3 (by rfl) ⟨520808, by rfl⟩ : syracuseStep 2777645 = 1041617) (by norm_num)
theorem B2466365 : Blo 1644021 2466365 := bbase (se 3 (by rfl) ⟨462443, by rfl⟩ : syracuseStep 2466365 = 924887) (by norm_num)
theorem B3703373 : Blo 1644021 3703373 := bbase (se 3 (by rfl) ⟨694382, by rfl⟩ : syracuseStep 3703373 = 1388765) (by norm_num)
theorem B2466389 : Blo 1644021 2466389 := bbase (se 8 (by rfl) ⟨14451, by rfl⟩ : syracuseStep 2466389 = 28903) (by norm_num)
theorem B8438357 : Blo 1644021 8438357 := bbase (se 8 (by rfl) ⟨49443, by rfl⟩ : syracuseStep 8438357 = 98887) (by norm_num)
theorem B2966117 : Blo 1644021 2966117 := bbase (se 4 (by rfl) ⟨278073, by rfl⟩ : syracuseStep 2966117 = 556147) (by norm_num)
theorem B2466413 : Blo 1644021 2466413 := bbase (se 3 (by rfl) ⟨462452, by rfl⟩ : syracuseStep 2466413 = 924905) (by norm_num)
theorem B10543733 : Blo 1644021 10543733 := bbase (se 5 (by rfl) ⟨494237, by rfl⟩ : syracuseStep 10543733 = 988475) (by norm_num)
theorem B8897141 : Blo 1644021 8897141 := bbase (se 5 (by rfl) ⟨417053, by rfl⟩ : syracuseStep 8897141 = 834107) (by norm_num)
theorem B3515005 : Blo 1644021 3515005 := bbase (se 3 (by rfl) ⟨659063, by rfl⟩ : syracuseStep 3515005 = 1318127) (by norm_num)
theorem B2466437 : Blo 1644021 2466437 := bbase (se 4 (by rfl) ⟨231228, by rfl⟩ : syracuseStep 2466437 = 462457) (by norm_num)
theorem B3703445 : Blo 1644021 3703445 := bbase (se 6 (by rfl) ⟨86799, by rfl⟩ : syracuseStep 3703445 = 173599) (by norm_num)
theorem B2466461 : Blo 1644021 2466461 := bbase (se 3 (by rfl) ⟨462461, by rfl⟩ : syracuseStep 2466461 = 924923) (by norm_num)
theorem B4162205 : Blo 1644021 4162205 := bbase (se 3 (by rfl) ⟨780413, by rfl⟩ : syracuseStep 4162205 = 1560827) (by norm_num)
theorem B7029413 : Blo 1644021 7029413 := bbase (se 4 (by rfl) ⟨659007, by rfl⟩ : syracuseStep 7029413 = 1318015) (by norm_num)
theorem B2466485 : Blo 1644021 2466485 := bbase (se 5 (by rfl) ⟨115616, by rfl⟩ : syracuseStep 2466485 = 231233) (by norm_num)
theorem B2081477 : Blo 1644021 2081477 := bbase (se 4 (by rfl) ⟨195138, by rfl⟩ : syracuseStep 2081477 = 390277) (by norm_num)
theorem B2466509 : Blo 1644021 2466509 := bbase (se 3 (by rfl) ⟨462470, by rfl⟩ : syracuseStep 2466509 = 924941) (by norm_num)
theorem B3703517 : Blo 1644021 3703517 := bbase (se 3 (by rfl) ⟨694409, by rfl⟩ : syracuseStep 3703517 = 1388819) (by norm_num)
theorem B2466533 : Blo 1644021 2466533 := bbase (se 4 (by rfl) ⟨231237, by rfl⟩ : syracuseStep 2466533 = 462475) (by norm_num)
theorem B2466557 : Blo 1644021 2466557 := bbase (se 3 (by rfl) ⟨462479, by rfl⟩ : syracuseStep 2466557 = 924959) (by norm_num)
theorem B2081533 : Blo 1644021 2081533 := bbase (se 3 (by rfl) ⟨390287, by rfl⟩ : syracuseStep 2081533 = 780575) (by norm_num)
theorem B2466581 : Blo 1644021 2466581 := bbase (se 6 (by rfl) ⟨57810, by rfl⟩ : syracuseStep 2466581 = 115621) (by norm_num)
theorem B2466605 : Blo 1644021 2466605 := bbase (se 3 (by rfl) ⟨462488, by rfl⟩ : syracuseStep 2466605 = 924977) (by norm_num)
theorem B3121973 : Blo 1644021 3121973 := bbase (se 5 (by rfl) ⟨146342, by rfl⟩ : syracuseStep 3121973 = 292685) (by norm_num)
theorem B1975105 : Blo 1644021 1975105 := bbase (se 2 (by rfl) ⟨740664, by rfl⟩ : syracuseStep 1975105 = 1481329) (by norm_num)
theorem B2466629 : Blo 1644021 2466629 := bbase (se 4 (by rfl) ⟨231246, by rfl⟩ : syracuseStep 2466629 = 462493) (by norm_num)
theorem B2671429 : Blo 1644021 2671429 := bbase (se 4 (by rfl) ⟨250446, by rfl⟩ : syracuseStep 2671429 = 500893) (by norm_num)
theorem B2466653 : Blo 1644021 2466653 := bbase (se 3 (by rfl) ⟨462497, by rfl⟩ : syracuseStep 2466653 = 924995) (by norm_num)
theorem B2081629 : Blo 1644021 2081629 := bbase (se 3 (by rfl) ⟨390305, by rfl⟩ : syracuseStep 2081629 = 780611) (by norm_num)
theorem B2466677 : Blo 1644021 2466677 := bbase (se 5 (by rfl) ⟨115625, by rfl⟩ : syracuseStep 2466677 = 231251) (by norm_num)
theorem B2466701 : Blo 1644021 2466701 := bbase (se 3 (by rfl) ⟨462506, by rfl⟩ : syracuseStep 2466701 = 925013) (by norm_num)
theorem B2466725 : Blo 1644021 2466725 := bbase (se 4 (by rfl) ⟨231255, by rfl⟩ : syracuseStep 2466725 = 462511) (by norm_num)
theorem B2466749 : Blo 1644021 2466749 := bbase (se 3 (by rfl) ⟨462515, by rfl⟩ : syracuseStep 2466749 = 925031) (by norm_num)
theorem B5555141 : Blo 1644021 5555141 := bbase (se 4 (by rfl) ⟨520794, by rfl⟩ : syracuseStep 5555141 = 1041589) (by norm_num)
theorem B2466773 : Blo 1644021 2466773 := bbase (se 7 (by rfl) ⟨28907, by rfl⟩ : syracuseStep 2466773 = 57815) (by norm_num)
theorem B4219877 : Blo 1644021 4219877 := bbase (se 4 (by rfl) ⟨395613, by rfl⟩ : syracuseStep 4219877 = 791227) (by norm_num)
theorem B2466797 : Blo 1644021 2466797 := bbase (se 3 (by rfl) ⟨462524, by rfl⟩ : syracuseStep 2466797 = 925049) (by norm_num)
theorem B4162549 : Blo 1644021 4162549 := bbase (se 5 (by rfl) ⟨195119, by rfl⟩ : syracuseStep 4162549 = 390239) (by norm_num)
theorem B10003445 : Blo 1644021 10003445 := bbase (se 5 (by rfl) ⟨468911, by rfl⟩ : syracuseStep 10003445 = 937823) (by norm_num)
theorem B1975297 : Blo 1644021 1975297 := bbase (se 2 (by rfl) ⟨740736, by rfl⟩ : syracuseStep 1975297 = 1481473) (by norm_num)
theorem B2466821 : Blo 1644021 2466821 := bbase (se 4 (by rfl) ⟨231264, by rfl⟩ : syracuseStep 2466821 = 462529) (by norm_num)
theorem B2081801 : Blo 1644021 2081801 := bbase (se 2 (by rfl) ⟨780675, by rfl⟩ : syracuseStep 2081801 = 1561351) (by norm_num)
theorem B2466845 : Blo 1644021 2466845 := bbase (se 3 (by rfl) ⟨462533, by rfl⟩ : syracuseStep 2466845 = 925067) (by norm_num)
theorem B2466869 : Blo 1644021 2466869 := bbase (se 5 (by rfl) ⟨115634, by rfl⟩ : syracuseStep 2466869 = 231269) (by norm_num)
theorem B2081857 : Blo 1644021 2081857 := bbase (se 2 (by rfl) ⟨780696, by rfl⟩ : syracuseStep 2081857 = 1561393) (by norm_num)
theorem B2466893 : Blo 1644021 2466893 := bbase (se 3 (by rfl) ⟨462542, by rfl⟩ : syracuseStep 2466893 = 925085) (by norm_num)
theorem B4162661 : Blo 1644021 4162661 := bbase (se 4 (by rfl) ⟨390249, by rfl⟩ : syracuseStep 4162661 = 780499) (by norm_num)
theorem B2466917 : Blo 1644021 2466917 := bbase (se 4 (by rfl) ⟨231273, by rfl⟩ : syracuseStep 2466917 = 462547) (by norm_num)
theorem B2466941 : Blo 1644021 2466941 := bbase (se 3 (by rfl) ⟨462551, by rfl⟩ : syracuseStep 2466941 = 925103) (by norm_num)
theorem B2466965 : Blo 1644021 2466965 := bbase (se 6 (by rfl) ⟨57819, by rfl⟩ : syracuseStep 2466965 = 115639) (by norm_num)
theorem B2081953 : Blo 1644021 2081953 := bbase (se 2 (by rfl) ⟨780732, by rfl⟩ : syracuseStep 2081953 = 1561465) (by norm_num)
theorem B2466989 : Blo 1644021 2466989 := bbase (se 3 (by rfl) ⟨462560, by rfl⟩ : syracuseStep 2466989 = 925121) (by norm_num)
theorem B8332469 : Blo 1644021 8332469 := bbase (se 5 (by rfl) ⟨390584, by rfl⟩ : syracuseStep 8332469 = 781169) (by norm_num)
theorem B2467013 : Blo 1644021 2467013 := bbase (se 4 (by rfl) ⟨231282, by rfl⟩ : syracuseStep 2467013 = 462565) (by norm_num)
theorem B2467037 : Blo 1644021 2467037 := bbase (se 3 (by rfl) ⟨462569, by rfl⟩ : syracuseStep 2467037 = 925139) (by norm_num)
theorem B2467061 : Blo 1644021 2467061 := bbase (se 5 (by rfl) ⟨115643, by rfl⟩ : syracuseStep 2467061 = 231287) (by norm_num)
theorem B2467085 : Blo 1644021 2467085 := bbase (se 3 (by rfl) ⟨462578, by rfl⟩ : syracuseStep 2467085 = 925157) (by norm_num)
theorem B4162853 : Blo 1644021 4162853 := bbase (se 4 (by rfl) ⟨390267, by rfl⟩ : syracuseStep 4162853 = 780535) (by norm_num)
theorem B2467109 : Blo 1644021 2467109 := bbase (se 4 (by rfl) ⟨231291, by rfl⟩ : syracuseStep 2467109 = 462583) (by norm_num)
theorem B2467133 : Blo 1644021 2467133 := bbase (se 3 (by rfl) ⟨462587, by rfl⟩ : syracuseStep 2467133 = 925175) (by norm_num)
theorem B2082125 : Blo 1644021 2082125 := bbase (se 3 (by rfl) ⟨390398, by rfl⟩ : syracuseStep 2082125 = 780797) (by norm_num)
theorem B2467157 : Blo 1644021 2467157 := bbase (se 12 (by rfl) ⟨903, by rfl⟩ : syracuseStep 2467157 = 1807) (by norm_num)
theorem B2467181 : Blo 1644021 2467181 := bbase (se 3 (by rfl) ⟨462596, by rfl⟩ : syracuseStep 2467181 = 925193) (by norm_num)
theorem B2467205 : Blo 1644021 2467205 := bbase (se 4 (by rfl) ⟨231300, by rfl⟩ : syracuseStep 2467205 = 462601) (by norm_num)
theorem B2082181 : Blo 1644021 2082181 := bbase (se 4 (by rfl) ⟨195204, by rfl⟩ : syracuseStep 2082181 = 390409) (by norm_num)
theorem B2467229 : Blo 1644021 2467229 := bbase (se 3 (by rfl) ⟨462605, by rfl⟩ : syracuseStep 2467229 = 925211) (by norm_num)
theorem B6243749 : Blo 1644021 6243749 := bbase (se 4 (by rfl) ⟨585351, by rfl⟩ : syracuseStep 6243749 = 1170703) (by norm_num)
theorem B2467253 : Blo 1644021 2467253 := bbase (se 5 (by rfl) ⟨115652, by rfl⟩ : syracuseStep 2467253 = 231305) (by norm_num)
theorem B6333877 : Blo 1644021 6333877 := bbase (se 5 (by rfl) ⟨296900, by rfl⟩ : syracuseStep 6333877 = 593801) (by norm_num)
theorem B2467277 : Blo 1644021 2467277 := bbase (se 3 (by rfl) ⟨462614, by rfl⟩ : syracuseStep 2467277 = 925229) (by norm_num)
theorem B21661141 : Blo 1644021 21661141 := bbase (se 7 (by rfl) ⟨253841, by rfl⟩ : syracuseStep 21661141 = 507683) (by norm_num)
theorem B2467301 : Blo 1644021 2467301 := bbase (se 4 (by rfl) ⟨231309, by rfl⟩ : syracuseStep 2467301 = 462619) (by norm_num)
theorem B4220389 : Blo 1644021 4220389 := bbase (se 4 (by rfl) ⟨395661, by rfl⟩ : syracuseStep 4220389 = 791323) (by norm_num)
theorem B2082277 : Blo 1644021 2082277 := bbase (se 4 (by rfl) ⟨195213, by rfl⟩ : syracuseStep 2082277 = 390427) (by norm_num)
theorem B2467325 : Blo 1644021 2467325 := bbase (se 3 (by rfl) ⟨462623, by rfl⟩ : syracuseStep 2467325 = 925247) (by norm_num)
theorem B2254349 : Blo 1644021 2254349 := bbase (se 3 (by rfl) ⟨422690, by rfl⟩ : syracuseStep 2254349 = 845381) (by norm_num)
theorem B2467349 : Blo 1644021 2467349 := bbase (se 6 (by rfl) ⟨57828, by rfl⟩ : syracuseStep 2467349 = 115657) (by norm_num)
theorem B3122725 : Blo 1644021 3122725 := bbase (se 4 (by rfl) ⟨292755, by rfl⟩ : syracuseStep 3122725 = 585511) (by norm_num)
theorem B2467373 : Blo 1644021 2467373 := bbase (se 3 (by rfl) ⟨462632, by rfl⟩ : syracuseStep 2467373 = 925265) (by norm_num)
theorem B2467397 : Blo 1644021 2467397 := bbase (se 4 (by rfl) ⟨231318, by rfl⟩ : syracuseStep 2467397 = 462637) (by norm_num)
theorem B8324693 : Blo 1644021 8324693 := bbase (se 8 (by rfl) ⟨48777, by rfl⟩ : syracuseStep 8324693 = 97555) (by norm_num)
theorem B2467421 : Blo 1644021 2467421 := bbase (se 3 (by rfl) ⟨462641, by rfl⟩ : syracuseStep 2467421 = 925283) (by norm_num)
theorem B2467445 : Blo 1644021 2467445 := bbase (se 5 (by rfl) ⟨115661, by rfl⟩ : syracuseStep 2467445 = 231323) (by norm_num)
theorem B4163197 : Blo 1644021 4163197 := bbase (se 3 (by rfl) ⟨780599, by rfl⟩ : syracuseStep 4163197 = 1561199) (by norm_num)
theorem B2467469 : Blo 1644021 2467469 := bbase (se 3 (by rfl) ⟨462650, by rfl⟩ : syracuseStep 2467469 = 925301) (by norm_num)
theorem B2082449 : Blo 1644021 2082449 := bbase (se 2 (by rfl) ⟨780918, by rfl⟩ : syracuseStep 2082449 = 1561837) (by norm_num)
theorem B7030421 : Blo 1644021 7030421 := bbase (se 6 (by rfl) ⟨164775, by rfl⟩ : syracuseStep 7030421 = 329551) (by norm_num)
theorem B2467493 : Blo 1644021 2467493 := bbase (se 4 (by rfl) ⟨231327, by rfl⟩ : syracuseStep 2467493 = 462655) (by norm_num)
theorem B3122869 : Blo 1644021 3122869 := bbase (se 5 (by rfl) ⟨146384, by rfl⟩ : syracuseStep 3122869 = 292769) (by norm_num)
theorem B2467517 : Blo 1644021 2467517 := bbase (se 3 (by rfl) ⟨462659, by rfl⟩ : syracuseStep 2467517 = 925319) (by norm_num)
theorem B6244037 : Blo 1644021 6244037 := bbase (se 4 (by rfl) ⟨585378, by rfl⟩ : syracuseStep 6244037 = 1170757) (by norm_num)
theorem B2082505 : Blo 1644021 2082505 := bbase (se 2 (by rfl) ⟨780939, by rfl⟩ : syracuseStep 2082505 = 1561879) (by norm_num)
theorem B2467541 : Blo 1644021 2467541 := bbase (se 7 (by rfl) ⟨28916, by rfl⟩ : syracuseStep 2467541 = 57833) (by norm_num)
theorem B4163309 : Blo 1644021 4163309 := bbase (se 3 (by rfl) ⟨780620, by rfl⟩ : syracuseStep 4163309 = 1561241) (by norm_num)
theorem B2467565 : Blo 1644021 2467565 := bbase (se 3 (by rfl) ⟨462668, by rfl⟩ : syracuseStep 2467565 = 925337) (by norm_num)
theorem B2139889 : Blo 1644021 2139889 := bbase (se 2 (by rfl) ⟨802458, by rfl⟩ : syracuseStep 2139889 = 1604917) (by norm_num)
theorem B2467589 : Blo 1644021 2467589 := bbase (se 4 (by rfl) ⟨231336, by rfl⟩ : syracuseStep 2467589 = 462673) (by norm_num)
theorem B4007693 : Blo 1644021 4007693 := bbase (se 3 (by rfl) ⟨751442, by rfl⟩ : syracuseStep 4007693 = 1502885) (by norm_num)
theorem B2467613 : Blo 1644021 2467613 := bbase (se 3 (by rfl) ⟨462677, by rfl⟩ : syracuseStep 2467613 = 925355) (by norm_num)
theorem B2082601 : Blo 1644021 2082601 := bbase (se 2 (by rfl) ⟨780975, by rfl⟩ : syracuseStep 2082601 = 1561951) (by norm_num)
theorem B2467637 : Blo 1644021 2467637 := bbase (se 5 (by rfl) ⟨115670, by rfl⟩ : syracuseStep 2467637 = 231341) (by norm_num)
theorem B2467661 : Blo 1644021 2467661 := bbase (se 3 (by rfl) ⟨462686, by rfl⟩ : syracuseStep 2467661 = 925373) (by norm_num)
theorem B3123029 : Blo 1644021 3123029 := bbase (se 9 (by rfl) ⟨9149, by rfl⟩ : syracuseStep 3123029 = 18299) (by norm_num)
theorem B2467685 : Blo 1644021 2467685 := bbase (se 4 (by rfl) ⟨231345, by rfl⟩ : syracuseStep 2467685 = 462691) (by norm_num)
theorem B1976177 : Blo 1644021 1976177 := bbase (se 2 (by rfl) ⟨741066, by rfl⟩ : syracuseStep 1976177 = 1482133) (by norm_num)
theorem B2467709 : Blo 1644021 2467709 := bbase (se 3 (by rfl) ⟨462695, by rfl⟩ : syracuseStep 2467709 = 925391) (by norm_num)
theorem B2467733 : Blo 1644021 2467733 := bbase (se 6 (by rfl) ⟨57837, by rfl⟩ : syracuseStep 2467733 = 115675) (by norm_num)
theorem B4163501 : Blo 1644021 4163501 := bbase (se 3 (by rfl) ⟨780656, by rfl⟩ : syracuseStep 4163501 = 1561313) (by norm_num)
theorem B2467757 : Blo 1644021 2467757 := bbase (se 3 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 2467757 = 925409) (by norm_num)
theorem B2467781 : Blo 1644021 2467781 := bbase (se 4 (by rfl) ⟨231354, by rfl⟩ : syracuseStep 2467781 = 462709) (by norm_num)
theorem B30418901 : Blo 1644021 30418901 := bbase (se 7 (by rfl) ⟨356471, by rfl⟩ : syracuseStep 30418901 = 712943) (by norm_num)
theorem B2082773 : Blo 1644021 2082773 := bbase (se 7 (by rfl) ⟨24407, by rfl⟩ : syracuseStep 2082773 = 48815) (by norm_num)
theorem B2467805 : Blo 1644021 2467805 := bbase (se 3 (by rfl) ⟨462713, by rfl⟩ : syracuseStep 2467805 = 925427) (by norm_num)
theorem B3123173 : Blo 1644021 3123173 := bbase (se 4 (by rfl) ⟨292797, by rfl⟩ : syracuseStep 3123173 = 585595) (by norm_num)
theorem B2467829 : Blo 1644021 2467829 := bbase (se 5 (by rfl) ⟨115679, by rfl⟩ : syracuseStep 2467829 = 231359) (by norm_num)
theorem B2500613 : Blo 1644021 2500613 := bbase (se 4 (by rfl) ⟨234432, by rfl⟩ : syracuseStep 2500613 = 468865) (by norm_num)
theorem B2467853 : Blo 1644021 2467853 := bbase (se 3 (by rfl) ⟨462722, by rfl⟩ : syracuseStep 2467853 = 925445) (by norm_num)
theorem B2082829 : Blo 1644021 2082829 := bbase (se 3 (by rfl) ⟨390530, by rfl⟩ : syracuseStep 2082829 = 781061) (by norm_num)
theorem B2467877 : Blo 1644021 2467877 := bbase (se 4 (by rfl) ⟨231363, by rfl⟩ : syracuseStep 2467877 = 462727) (by norm_num)
theorem B2467901 : Blo 1644021 2467901 := bbase (se 3 (by rfl) ⟨462731, by rfl⟩ : syracuseStep 2467901 = 925463) (by norm_num)
theorem B2467925 : Blo 1644021 2467925 := bbase (se 8 (by rfl) ⟨14460, by rfl⟩ : syracuseStep 2467925 = 28921) (by norm_num)
theorem B2467949 : Blo 1644021 2467949 := bbase (se 3 (by rfl) ⟨462740, by rfl⟩ : syracuseStep 2467949 = 925481) (by norm_num)
theorem B2082925 : Blo 1644021 2082925 := bbase (se 3 (by rfl) ⟨390548, by rfl⟩ : syracuseStep 2082925 = 781097) (by norm_num)
theorem B5269637 : Blo 1644021 5269637 := bbase (se 4 (by rfl) ⟨494028, by rfl⟩ : syracuseStep 5269637 = 988057) (by norm_num)
theorem B2467973 : Blo 1644021 2467973 := bbase (se 4 (by rfl) ⟨231372, by rfl⟩ : syracuseStep 2467973 = 462745) (by norm_num)
theorem B2467997 : Blo 1644021 2467997 := bbase (se 3 (by rfl) ⟨462749, by rfl⟩ : syracuseStep 2467997 = 925499) (by norm_num)
theorem B2468021 : Blo 1644021 2468021 := bbase (se 5 (by rfl) ⟨115688, by rfl⟩ : syracuseStep 2468021 = 231377) (by norm_num)
theorem B2468045 : Blo 1644021 2468045 := bbase (se 3 (by rfl) ⟨462758, by rfl⟩ : syracuseStep 2468045 = 925517) (by norm_num)
theorem B2468069 : Blo 1644021 2468069 := bbase (se 4 (by rfl) ⟨231381, by rfl⟩ : syracuseStep 2468069 = 462763) (by norm_num)
theorem B2468093 : Blo 1644021 2468093 := bbase (se 3 (by rfl) ⟨462767, by rfl⟩ : syracuseStep 2468093 = 925535) (by norm_num)
theorem B4163845 : Blo 1644021 4163845 := bbase (se 4 (by rfl) ⟨390360, by rfl⟩ : syracuseStep 4163845 = 780721) (by norm_num)
theorem B3123461 : Blo 1644021 3123461 := bbase (se 4 (by rfl) ⟨292824, by rfl⟩ : syracuseStep 3123461 = 585649) (by norm_num)
theorem B2468117 : Blo 1644021 2468117 := bbase (se 6 (by rfl) ⟨57846, by rfl⟩ : syracuseStep 2468117 = 115693) (by norm_num)
theorem B2083097 : Blo 1644021 2083097 := bbase (se 2 (by rfl) ⟨781161, by rfl⟩ : syracuseStep 2083097 = 1562323) (by norm_num)
theorem B2812205 : Blo 1644021 2812205 := bbase (se 3 (by rfl) ⟨527288, by rfl⟩ : syracuseStep 2812205 = 1054577) (by norm_num)
theorem B2468141 : Blo 1644021 2468141 := bbase (se 3 (by rfl) ⟨462776, by rfl⟩ : syracuseStep 2468141 = 925553) (by norm_num)
theorem B2468165 : Blo 1644021 2468165 := bbase (se 4 (by rfl) ⟨231390, by rfl⟩ : syracuseStep 2468165 = 462781) (by norm_num)
theorem B2083153 : Blo 1644021 2083153 := bbase (se 2 (by rfl) ⟨781182, by rfl⟩ : syracuseStep 2083153 = 1562365) (by norm_num)
theorem B34212181 : Blo 1644021 34212181 := bbase (se 10 (by rfl) ⟨50115, by rfl⟩ : syracuseStep 34212181 = 100231) (by norm_num)
theorem B2468189 : Blo 1644021 2468189 := bbase (se 3 (by rfl) ⟨462785, by rfl⟩ : syracuseStep 2468189 = 925571) (by norm_num)
theorem B1976681 : Blo 1644021 1976681 := bbase (se 2 (by rfl) ⟨741255, by rfl⟩ : syracuseStep 1976681 = 1482511) (by norm_num)
theorem B3336557 : Blo 1644021 3336557 := bbase (se 3 (by rfl) ⟨625604, by rfl⟩ : syracuseStep 3336557 = 1251209) (by norm_num)
theorem B4163957 : Blo 1644021 4163957 := bbase (se 5 (by rfl) ⟨195185, by rfl⟩ : syracuseStep 4163957 = 390371) (by norm_num)
theorem B2468213 : Blo 1644021 2468213 := bbase (se 5 (by rfl) ⟨115697, by rfl⟩ : syracuseStep 2468213 = 231395) (by norm_num)
theorem B2468237 : Blo 1644021 2468237 := bbase (se 3 (by rfl) ⟨462794, by rfl⟩ : syracuseStep 2468237 = 925589) (by norm_num)
theorem B1976729 : Blo 1644021 1976729 := bbase (se 2 (by rfl) ⟨741273, by rfl⟩ : syracuseStep 1976729 = 1482547) (by norm_num)
theorem B3123613 : Blo 1644021 3123613 := bbase (se 3 (by rfl) ⟨585677, by rfl⟩ : syracuseStep 3123613 = 1171355) (by norm_num)
theorem B2468261 : Blo 1644021 2468261 := bbase (se 4 (by rfl) ⟨231399, by rfl⟩ : syracuseStep 2468261 = 462799) (by norm_num)
theorem B2468285 : Blo 1644021 2468285 := bbase (se 3 (by rfl) ⟨462803, by rfl⟩ : syracuseStep 2468285 = 925607) (by norm_num)
theorem B2468309 : Blo 1644021 2468309 := bbase (se 7 (by rfl) ⟨28925, by rfl⟩ : syracuseStep 2468309 = 57851) (by norm_num)
theorem B2468333 : Blo 1644021 2468333 := bbase (se 3 (by rfl) ⟨462812, by rfl⟩ : syracuseStep 2468333 = 925625) (by norm_num)
theorem B2468357 : Blo 1644021 2468357 := bbase (se 4 (by rfl) ⟨231408, by rfl⟩ : syracuseStep 2468357 = 462817) (by norm_num)
theorem B2812429 : Blo 1644021 2812429 := bbase (se 3 (by rfl) ⟨527330, by rfl⟩ : syracuseStep 2812429 = 1054661) (by norm_num)
theorem B7023125 : Blo 1644021 7023125 := bbase (se 6 (by rfl) ⟨164604, by rfl⟩ : syracuseStep 7023125 = 329209) (by norm_num)
theorem B2468381 : Blo 1644021 2468381 := bbase (se 3 (by rfl) ⟨462821, by rfl⟩ : syracuseStep 2468381 = 925643) (by norm_num)
theorem B4164149 : Blo 1644021 4164149 := bbase (se 5 (by rfl) ⟨195194, by rfl⟩ : syracuseStep 4164149 = 390389) (by norm_num)
theorem B2468405 : Blo 1644021 2468405 := bbase (se 5 (by rfl) ⟨115706, by rfl⟩ : syracuseStep 2468405 = 231413) (by norm_num)
theorem B1755713 : Blo 1644021 1755713 := bbase (se 2 (by rfl) ⟨658392, by rfl⟩ : syracuseStep 1755713 = 1316785) (by norm_num)
theorem B2468429 : Blo 1644021 2468429 := bbase (se 3 (by rfl) ⟨462830, by rfl⟩ : syracuseStep 2468429 = 925661) (by norm_num)
theorem B9366101 : Blo 1644021 9366101 := bbase (se 8 (by rfl) ⟨54879, by rfl⟩ : syracuseStep 9366101 = 109759) (by norm_num)
theorem B2468453 : Blo 1644021 2468453 := bbase (se 4 (by rfl) ⟨231417, by rfl⟩ : syracuseStep 2468453 = 462835) (by norm_num)
theorem B5548661 : Blo 1644021 5548661 := bbase (se 5 (by rfl) ⟨260093, by rfl⟩ : syracuseStep 5548661 = 520187) (by norm_num)
theorem B2468477 : Blo 1644021 2468477 := bbase (se 3 (by rfl) ⟨462839, by rfl⟩ : syracuseStep 2468477 = 925679) (by norm_num)
theorem B2468501 : Blo 1644021 2468501 := bbase (se 6 (by rfl) ⟨57855, by rfl⟩ : syracuseStep 2468501 = 115711) (by norm_num)
theorem B1976989 : Blo 1644021 1976989 := bbase (se 3 (by rfl) ⟨370685, by rfl⟩ : syracuseStep 1976989 = 741371) (by norm_num)
theorem B2468525 : Blo 1644021 2468525 := bbase (se 3 (by rfl) ⟨462848, by rfl⟩ : syracuseStep 2468525 = 925697) (by norm_num)
theorem B2468549 : Blo 1644021 2468549 := bbase (se 4 (by rfl) ⟨231426, by rfl⟩ : syracuseStep 2468549 = 462853) (by norm_num)
theorem B3123917 : Blo 1644021 3123917 := bbase (se 3 (by rfl) ⟨585734, by rfl⟩ : syracuseStep 3123917 = 1171469) (by norm_num)
theorem B10537685 : Blo 1644021 10537685 := bbase (se 7 (by rfl) ⟨123488, by rfl⟩ : syracuseStep 10537685 = 246977) (by norm_num)
theorem B2468573 : Blo 1644021 2468573 := bbase (se 3 (by rfl) ⟨462857, by rfl⟩ : syracuseStep 2468573 = 925715) (by norm_num)
theorem B2468597 : Blo 1644021 2468597 := bbase (se 5 (by rfl) ⟨115715, by rfl⟩ : syracuseStep 2468597 = 231431) (by norm_num)
theorem B2468621 : Blo 1644021 2468621 := bbase (se 3 (by rfl) ⟨462866, by rfl⟩ : syracuseStep 2468621 = 925733) (by norm_num)
theorem B2468645 : Blo 1644021 2468645 := bbase (se 4 (by rfl) ⟨231435, by rfl⟩ : syracuseStep 2468645 = 462871) (by norm_num)
theorem B1755965 : Blo 1644021 1755965 := bbase (se 3 (by rfl) ⟨329243, by rfl⟩ : syracuseStep 1755965 = 658487) (by norm_num)
theorem B2468669 : Blo 1644021 2468669 := bbase (se 3 (by rfl) ⟨462875, by rfl⟩ : syracuseStep 2468669 = 925751) (by norm_num)
theorem B2468693 : Blo 1644021 2468693 := bbase (se 9 (by rfl) ⟨7232, by rfl⟩ : syracuseStep 2468693 = 14465) (by norm_num)
theorem B8325989 : Blo 1644021 8325989 := bbase (se 4 (by rfl) ⟨780561, by rfl⟩ : syracuseStep 8325989 = 1561123) (by norm_num)
theorem B6245221 : Blo 1644021 6245221 := bbase (se 4 (by rfl) ⟨585489, by rfl⟩ : syracuseStep 6245221 = 1170979) (by norm_num)
theorem B2468717 : Blo 1644021 2468717 := bbase (se 3 (by rfl) ⟨462884, by rfl⟩ : syracuseStep 2468717 = 925769) (by norm_num)
theorem B2468741 : Blo 1644021 2468741 := bbase (se 4 (by rfl) ⟨231444, by rfl⟩ : syracuseStep 2468741 = 462889) (by norm_num)
theorem B4164493 : Blo 1644021 4164493 := bbase (se 3 (by rfl) ⟨780842, by rfl⟩ : syracuseStep 4164493 = 1561685) (by norm_num)
theorem B3951517 : Blo 1644021 3951517 := bbase (se 3 (by rfl) ⟨740909, by rfl⟩ : syracuseStep 3951517 = 1481819) (by norm_num)
theorem B2468765 : Blo 1644021 2468765 := bbase (se 3 (by rfl) ⟨462893, by rfl⟩ : syracuseStep 2468765 = 925787) (by norm_num)
theorem B1977253 : Blo 1644021 1977253 := bbase (se 4 (by rfl) ⟨185367, by rfl⟩ : syracuseStep 1977253 = 370735) (by norm_num)
theorem B1805225 : Blo 1644021 1805225 := bbase (se 2 (by rfl) ⟨676959, by rfl⟩ : syracuseStep 1805225 = 1353919) (by norm_num)
theorem B2468789 : Blo 1644021 2468789 := bbase (se 5 (by rfl) ⟨115724, by rfl⟩ : syracuseStep 2468789 = 231449) (by norm_num)
theorem B2468813 : Blo 1644021 2468813 := bbase (se 3 (by rfl) ⟨462902, by rfl⟩ : syracuseStep 2468813 = 925805) (by norm_num)
theorem B5000165 : Blo 1644021 5000165 := bbase (se 4 (by rfl) ⟨468765, by rfl⟩ : syracuseStep 5000165 = 937531) (by norm_num)
theorem B2468837 : Blo 1644021 2468837 := bbase (se 4 (by rfl) ⟨231453, by rfl⟩ : syracuseStep 2468837 = 462907) (by norm_num)
theorem B3951613 : Blo 1644021 3951613 := bbase (se 3 (by rfl) ⟨740927, by rfl⟩ : syracuseStep 3951613 = 1481855) (by norm_num)
theorem B4164605 : Blo 1644021 4164605 := bbase (se 3 (by rfl) ⟨780863, by rfl⟩ : syracuseStep 4164605 = 1561727) (by norm_num)
theorem B2468861 : Blo 1644021 2468861 := bbase (se 3 (by rfl) ⟨462911, by rfl⟩ : syracuseStep 2468861 = 925823) (by norm_num)
theorem B2468885 : Blo 1644021 2468885 := bbase (se 6 (by rfl) ⟨57864, by rfl⟩ : syracuseStep 2468885 = 115729) (by norm_num)
theorem B1977373 : Blo 1644021 1977373 := bbase (se 3 (by rfl) ⟨370757, by rfl⟩ : syracuseStep 1977373 = 741515) (by norm_num)
theorem B5549093 : Blo 1644021 5549093 := bbase (se 4 (by rfl) ⟨520227, by rfl⟩ : syracuseStep 5549093 = 1040455) (by norm_num)
theorem B2468909 : Blo 1644021 2468909 := bbase (se 3 (by rfl) ⟨462920, by rfl⟩ : syracuseStep 2468909 = 925841) (by norm_num)
theorem B2468933 : Blo 1644021 2468933 := bbase (se 4 (by rfl) ⟨231462, by rfl⟩ : syracuseStep 2468933 = 462925) (by norm_num)
theorem B8891477 : Blo 1644021 8891477 := bbase (se 8 (by rfl) ⟨52098, by rfl⟩ : syracuseStep 8891477 = 104197) (by norm_num)
theorem B3165277 : Blo 1644021 3165277 := bbase (se 3 (by rfl) ⟨593489, by rfl⟩ : syracuseStep 3165277 = 1186979) (by norm_num)
theorem B2468957 : Blo 1644021 2468957 := bbase (se 3 (by rfl) ⟨462929, by rfl⟩ : syracuseStep 2468957 = 925859) (by norm_num)
theorem B2468981 : Blo 1644021 2468981 := bbase (se 5 (by rfl) ⟨115733, by rfl⟩ : syracuseStep 2468981 = 231467) (by norm_num)
theorem B2469005 : Blo 1644021 2469005 := bbase (se 3 (by rfl) ⟨462938, by rfl⟩ : syracuseStep 2469005 = 925877) (by norm_num)
theorem B6245525 : Blo 1644021 6245525 := bbase (se 6 (by rfl) ⟨146379, by rfl⟩ : syracuseStep 6245525 = 292759) (by norm_num)
theorem B2469029 : Blo 1644021 2469029 := bbase (se 4 (by rfl) ⟨231471, by rfl⟩ : syracuseStep 2469029 = 462943) (by norm_num)
theorem B4164797 : Blo 1644021 4164797 := bbase (se 3 (by rfl) ⟨780899, by rfl⟩ : syracuseStep 4164797 = 1561799) (by norm_num)
theorem B42134741 : Blo 1644021 42134741 := bbase (se 7 (by rfl) ⟨493766, by rfl⟩ : syracuseStep 42134741 = 987533) (by norm_num)
theorem B1756409 : Blo 1644021 1756409 := bbase (se 2 (by rfl) ⟨658653, by rfl⟩ : syracuseStep 1756409 = 1317307) (by norm_num)
theorem B6761861 : Blo 1644021 6761861 := bbase (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) (by norm_num)
theorem B5270933 : Blo 1644021 5270933 := bbase (se 6 (by rfl) ⟨123537, by rfl⟩ : syracuseStep 5270933 = 247075) (by norm_num)
theorem B3124669 : Blo 1644021 3124669 := bbase (se 3 (by rfl) ⟨585875, by rfl⟩ : syracuseStep 3124669 = 1171751) (by norm_num)
theorem B5549525 : Blo 1644021 5549525 := bbase (se 7 (by rfl) ⟨65033, by rfl⟩ : syracuseStep 5549525 = 130067) (by norm_num)
theorem B1756657 : Blo 1644021 1756657 := bbase (se 2 (by rfl) ⟨658746, by rfl⟩ : syracuseStep 1756657 = 1317493) (by norm_num)
theorem B4165141 : Blo 1644021 4165141 := bbase (se 6 (by rfl) ⟨97620, by rfl⟩ : syracuseStep 4165141 = 195241) (by norm_num)
theorem B3124813 : Blo 1644021 3124813 := bbase (se 3 (by rfl) ⟨585902, by rfl⟩ : syracuseStep 3124813 = 1171805) (by norm_num)
theorem B4165253 : Blo 1644021 4165253 := bbase (se 4 (by rfl) ⟨390492, by rfl⟩ : syracuseStep 4165253 = 780985) (by norm_num)
theorem B9367285 : Blo 1644021 9367285 := bbase (se 5 (by rfl) ⟨439091, by rfl⟩ : syracuseStep 9367285 = 878183) (by norm_num)
theorem B7909109 : Blo 1644021 7909109 := bbase (se 5 (by rfl) ⟨370739, by rfl⟩ : syracuseStep 7909109 = 741479) (by norm_num)
theorem B28503829 : Blo 1644021 28503829 := bbase (se 6 (by rfl) ⟨668058, by rfl⟩ : syracuseStep 28503829 = 1336117) (by norm_num)
theorem B7499557 : Blo 1644021 7499557 := bbase (se 4 (by rfl) ⟨703083, by rfl⟩ : syracuseStep 7499557 = 1406167) (by norm_num)
theorem B4165445 : Blo 1644021 4165445 := bbase (se 4 (by rfl) ⟨390510, by rfl⟩ : syracuseStep 4165445 = 781021) (by norm_num)
theorem B2813797 : Blo 1644021 2813797 := bbase (se 4 (by rfl) ⟨263793, by rfl⟩ : syracuseStep 2813797 = 527587) (by norm_num)
theorem B5549957 : Blo 1644021 5549957 := bbase (se 4 (by rfl) ⟨520308, by rfl⟩ : syracuseStep 5549957 = 1040617) (by norm_num)
theorem B1666981 : Blo 1644021 1666981 := bbase (se 4 (by rfl) ⟨156279, by rfl⟩ : syracuseStep 1666981 = 312559) (by norm_num)
theorem B1757101 : Blo 1644021 1757101 := bbase (se 3 (by rfl) ⟨329456, by rfl⟩ : syracuseStep 1757101 = 658913) (by norm_num)
theorem B1781677 : Blo 1644021 1781677 := bbase (se 3 (by rfl) ⟨334064, by rfl⟩ : syracuseStep 1781677 = 668129) (by norm_num)
theorem B1757161 : Blo 1644021 1757161 := bbase (se 2 (by rfl) ⟨658935, by rfl⟩ : syracuseStep 1757161 = 1317871) (by norm_num)
theorem B21082133 : Blo 1644021 21082133 := bbase (se 6 (by rfl) ⟨494112, by rfl⟩ : syracuseStep 21082133 = 988225) (by norm_num)
theorem B3952709 : Blo 1644021 3952709 := bbase (se 4 (by rfl) ⟨370566, by rfl⟩ : syracuseStep 3952709 = 741133) (by norm_num)
theorem B8327285 : Blo 1644021 8327285 := bbase (se 5 (by rfl) ⟨390341, by rfl⟩ : syracuseStep 8327285 = 780683) (by norm_num)
theorem B4165789 : Blo 1644021 4165789 := bbase (se 3 (by rfl) ⟨781085, by rfl⟩ : syracuseStep 4165789 = 1562171) (by norm_num)
theorem B7901381 : Blo 1644021 7901381 := bbase (se 4 (by rfl) ⟨740754, by rfl⟩ : syracuseStep 7901381 = 1481509) (by norm_num)
theorem B4681957 : Blo 1644021 4681957 := bbase (se 4 (by rfl) ⟨438933, by rfl⟩ : syracuseStep 4681957 = 877867) (by norm_num)
theorem B4165901 : Blo 1644021 4165901 := bbase (se 3 (by rfl) ⟨781106, by rfl⟩ : syracuseStep 4165901 = 1562213) (by norm_num)
theorem B1757477 : Blo 1644021 1757477 := bbase (se 4 (by rfl) ⟨164763, by rfl⟩ : syracuseStep 1757477 = 329527) (by norm_num)
theorem B5550389 : Blo 1644021 5550389 := bbase (se 5 (by rfl) ⟨260174, by rfl⟩ : syracuseStep 5550389 = 520349) (by norm_num)
theorem B3699053 : Blo 1644021 3699053 := bbase (se 3 (by rfl) ⟨693572, by rfl⟩ : syracuseStep 3699053 = 1387145) (by norm_num)
theorem B4682117 : Blo 1644021 4682117 := bbase (se 4 (by rfl) ⟨438948, by rfl⟩ : syracuseStep 4682117 = 877897) (by norm_num)
theorem B3699125 : Blo 1644021 3699125 := bbase (se 5 (by rfl) ⟨173396, by rfl⟩ : syracuseStep 3699125 = 346793) (by norm_num)
theorem B4166093 : Blo 1644021 4166093 := bbase (se 3 (by rfl) ⟨781142, by rfl⟩ : syracuseStep 4166093 = 1562285) (by norm_num)
theorem B3699197 : Blo 1644021 3699197 := bbase (se 3 (by rfl) ⟨693599, by rfl⟩ : syracuseStep 3699197 = 1387199) (by norm_num)
theorem B2634293 : Blo 1644021 2634293 := bbase (se 5 (by rfl) ⟨123482, by rfl⟩ : syracuseStep 2634293 = 246965) (by norm_num)
theorem B3699269 : Blo 1644021 3699269 := bbase (se 4 (by rfl) ⟨346806, by rfl⟩ : syracuseStep 3699269 = 693613) (by norm_num)
theorem B3379781 : Blo 1644021 3379781 := bbase (se 4 (by rfl) ⟨316854, by rfl⟩ : syracuseStep 3379781 = 633709) (by norm_num)
theorem B4682357 : Blo 1644021 4682357 := bbase (se 5 (by rfl) ⟨219485, by rfl⟩ : syracuseStep 4682357 = 438971) (by norm_num)
theorem B3699341 : Blo 1644021 3699341 := bbase (se 3 (by rfl) ⟨693626, by rfl⟩ : syracuseStep 3699341 = 1387253) (by norm_num)
theorem B3166877 : Blo 1644021 3166877 := bbase (se 3 (by rfl) ⟨593789, by rfl⟩ : syracuseStep 3166877 = 1187579) (by norm_num)
theorem B3961541 : Blo 1644021 3961541 := bbase (se 4 (by rfl) ⟨371394, by rfl⟩ : syracuseStep 3961541 = 742789) (by norm_num)
theorem B3699413 : Blo 1644021 3699413 := bbase (se 7 (by rfl) ⟨43352, by rfl⟩ : syracuseStep 3699413 = 86705) (by norm_num)
theorem B5550821 : Blo 1644021 5550821 := bbase (se 4 (by rfl) ⟨520389, by rfl⟩ : syracuseStep 5550821 = 1040779) (by norm_num)
theorem B3699485 : Blo 1644021 3699485 := bbase (se 3 (by rfl) ⟨693653, by rfl⟩ : syracuseStep 3699485 = 1387307) (by norm_num)
theorem B4166437 : Blo 1644021 4166437 := bbase (se 4 (by rfl) ⟨390603, by rfl⟩ : syracuseStep 4166437 = 781207) (by norm_num)
theorem B4682549 : Blo 1644021 4682549 := bbase (se 5 (by rfl) ⟨219494, by rfl⟩ : syracuseStep 4682549 = 438989) (by norm_num)
theorem B3699557 : Blo 1644021 3699557 := bbase (se 4 (by rfl) ⟨346833, by rfl⟩ : syracuseStep 3699557 = 693667) (by norm_num)
theorem B3003253 : Blo 1644021 3003253 := bbase (se 5 (by rfl) ⟨140777, by rfl⟩ : syracuseStep 3003253 = 281555) (by norm_num)
theorem B8893333 : Blo 1644021 8893333 := bbase (se 6 (by rfl) ⟨208437, by rfl⟩ : syracuseStep 8893333 = 416875) (by norm_num)
theorem B3699629 : Blo 1644021 3699629 := bbase (se 3 (by rfl) ⟨693680, by rfl⟩ : syracuseStep 3699629 = 1387361) (by norm_num)
theorem B5927909 : Blo 1644021 5927909 := bbase (se 4 (by rfl) ⟨555741, by rfl⟩ : syracuseStep 5927909 = 1111483) (by norm_num)
theorem B3699701 : Blo 1644021 3699701 := bbase (se 5 (by rfl) ⟨173423, by rfl⟩ : syracuseStep 3699701 = 346847) (by norm_num)
theorem B3953669 : Blo 1644021 3953669 := bbase (se 4 (by rfl) ⟨370656, by rfl⟩ : syracuseStep 3953669 = 741313) (by norm_num)
theorem B1668125 : Blo 1644021 1668125 := bbase (se 3 (by rfl) ⟨312773, by rfl⟩ : syracuseStep 1668125 = 625547) (by norm_num)
theorem B1668133 : Blo 1644021 1668133 := bbase (se 4 (by rfl) ⟨156387, by rfl⟩ : syracuseStep 1668133 = 312775) (by norm_num)
theorem B3699773 : Blo 1644021 3699773 := bbase (se 3 (by rfl) ⟨693707, by rfl⟩ : syracuseStep 3699773 = 1387415) (by norm_num)
theorem B3699845 : Blo 1644021 3699845 := bbase (se 4 (by rfl) ⟨346860, by rfl⟩ : syracuseStep 3699845 = 693721) (by norm_num)
theorem B5551253 : Blo 1644021 5551253 := bbase (se 6 (by rfl) ⟨130107, by rfl⟩ : syracuseStep 5551253 = 260215) (by norm_num)
theorem B3699917 : Blo 1644021 3699917 := bbase (se 3 (by rfl) ⟨693734, by rfl⟩ : syracuseStep 3699917 = 1387469) (by norm_num)
theorem B6247637 : Blo 1644021 6247637 := bbase (se 7 (by rfl) ⟨73214, by rfl⟩ : syracuseStep 6247637 = 146429) (by norm_num)
theorem B5272789 : Blo 1644021 5272789 := bbase (se 7 (by rfl) ⟨61790, by rfl⟩ : syracuseStep 5272789 = 123581) (by norm_num)
theorem B3699989 : Blo 1644021 3699989 := bbase (se 6 (by rfl) ⟨86718, by rfl⟩ : syracuseStep 3699989 = 173437) (by norm_num)
theorem B2774317 : Blo 1644021 2774317 := bbase (se 3 (by rfl) ⟨520184, by rfl⟩ : syracuseStep 2774317 = 1040369) (by norm_num)
theorem B2110801 : Blo 1644021 2110801 := bbase (se 2 (by rfl) ⟨791550, by rfl⟩ : syracuseStep 2110801 = 1583101) (by norm_num)
theorem B3700061 : Blo 1644021 3700061 := bbase (se 3 (by rfl) ⟨693761, by rfl⟩ : syracuseStep 3700061 = 1387523) (by norm_num)
theorem B2774405 : Blo 1644021 2774405 := bbase (se 4 (by rfl) ⟨260100, by rfl⟩ : syracuseStep 2774405 = 520201) (by norm_num)
theorem B8328581 : Blo 1644021 8328581 := bbase (se 4 (by rfl) ⟨780804, by rfl⟩ : syracuseStep 8328581 = 1561609) (by norm_num)
theorem B3700133 : Blo 1644021 3700133 := bbase (se 4 (by rfl) ⟨346887, by rfl⟩ : syracuseStep 3700133 = 693775) (by norm_num)
theorem B2635229 : Blo 1644021 2635229 := bbase (se 3 (by rfl) ⟨494105, by rfl⟩ : syracuseStep 2635229 = 988211) (by norm_num)
theorem B3700205 : Blo 1644021 3700205 := bbase (se 3 (by rfl) ⟨693788, by rfl⟩ : syracuseStep 3700205 = 1387577) (by norm_num)
theorem B6247925 : Blo 1644021 6247925 := bbase (se 5 (by rfl) ⟨292871, by rfl⟩ : syracuseStep 6247925 = 585743) (by norm_num)
theorem B2774533 : Blo 1644021 2774533 := bbase (se 4 (by rfl) ⟨260112, by rfl⟩ : syracuseStep 2774533 = 520225) (by norm_num)
theorem B2283061 : Blo 1644021 2283061 := bbase (se 5 (by rfl) ⟨107018, by rfl⟩ : syracuseStep 2283061 = 214037) (by norm_num)
theorem B3700277 : Blo 1644021 3700277 := bbase (se 5 (by rfl) ⟨173450, by rfl⟩ : syracuseStep 3700277 = 346901) (by norm_num)
theorem B11859509 : Blo 1644021 11859509 := bbase (se 5 (by rfl) ⟨555914, by rfl⟩ : syracuseStep 11859509 = 1111829) (by norm_num)
theorem B5551685 : Blo 1644021 5551685 := bbase (se 4 (by rfl) ⟨520470, by rfl⟩ : syracuseStep 5551685 = 1040941) (by norm_num)
theorem B2774621 : Blo 1644021 2774621 := bbase (se 3 (by rfl) ⟨520241, by rfl⟩ : syracuseStep 2774621 = 1040483) (by norm_num)
theorem B14055029 : Blo 1644021 14055029 := bbase (se 5 (by rfl) ⟨658829, by rfl⟩ : syracuseStep 14055029 = 1317659) (by norm_num)
theorem B3700349 : Blo 1644021 3700349 := bbase (se 3 (by rfl) ⟨693815, by rfl⟩ : syracuseStep 3700349 = 1387631) (by norm_num)
theorem B3511973 : Blo 1644021 3511973 := bbase (se 4 (by rfl) ⟨329247, by rfl⟩ : syracuseStep 3511973 = 658495) (by norm_num)
theorem B9369269 : Blo 1644021 9369269 := bbase (se 5 (by rfl) ⟨439184, by rfl⟩ : syracuseStep 9369269 = 878369) (by norm_num)
theorem B3700421 : Blo 1644021 3700421 := bbase (se 4 (by rfl) ⟨346914, by rfl⟩ : syracuseStep 3700421 = 693829) (by norm_num)
theorem B2774749 : Blo 1644021 2774749 := bbase (se 3 (by rfl) ⟨520265, by rfl⟩ : syracuseStep 2774749 = 1040531) (by norm_num)
theorem B14046965 : Blo 1644021 14046965 := bbase (se 5 (by rfl) ⟨658451, by rfl⟩ : syracuseStep 14046965 = 1316903) (by norm_num)
theorem B7026421 : Blo 1644021 7026421 := bbase (se 5 (by rfl) ⟨329363, by rfl⟩ : syracuseStep 7026421 = 658727) (by norm_num)
theorem B3700493 : Blo 1644021 3700493 := bbase (se 3 (by rfl) ⟨693842, by rfl⟩ : syracuseStep 3700493 = 1387685) (by norm_num)
theorem B4683541 : Blo 1644021 4683541 := bbase (se 6 (by rfl) ⟨109770, by rfl⟩ : syracuseStep 4683541 = 219541) (by norm_num)
theorem B2774837 : Blo 1644021 2774837 := bbase (se 5 (by rfl) ⟨130070, by rfl⟩ : syracuseStep 2774837 = 260141) (by norm_num)
theorem B3512117 : Blo 1644021 3512117 := bbase (se 5 (by rfl) ⟨164630, by rfl⟩ : syracuseStep 3512117 = 329261) (by norm_num)
theorem B8017717 : Blo 1644021 8017717 := bbase (se 5 (by rfl) ⟨375830, by rfl⟩ : syracuseStep 8017717 = 751661) (by norm_num)
theorem B3700565 : Blo 1644021 3700565 := bbase (se 9 (by rfl) ⟨10841, by rfl⟩ : syracuseStep 3700565 = 21683) (by norm_num)
theorem B4446053 : Blo 1644021 4446053 := bbase (se 4 (by rfl) ⟨416817, by rfl⟩ : syracuseStep 4446053 = 833635) (by norm_num)
theorem B6420325 : Blo 1644021 6420325 := bbase (se 4 (by rfl) ⟨601905, by rfl⟩ : syracuseStep 6420325 = 1203811) (by norm_num)
theorem B3700637 : Blo 1644021 3700637 := bbase (se 3 (by rfl) ⟨693869, by rfl⟩ : syracuseStep 3700637 = 1387739) (by norm_num)
theorem B2774965 : Blo 1644021 2774965 := bbase (se 5 (by rfl) ⟨130076, by rfl⟩ : syracuseStep 2774965 = 260153) (by norm_num)
theorem B3700709 : Blo 1644021 3700709 := bbase (se 4 (by rfl) ⟨346941, by rfl⟩ : syracuseStep 3700709 = 693883) (by norm_num)
theorem B5625845 : Blo 1644021 5625845 := bbase (se 5 (by rfl) ⟨263711, by rfl⟩ : syracuseStep 5625845 = 527423) (by norm_num)
theorem B5552117 : Blo 1644021 5552117 := bbase (se 5 (by rfl) ⟨260255, by rfl⟩ : syracuseStep 5552117 = 520511) (by norm_num)
theorem B2775053 : Blo 1644021 2775053 := bbase (se 3 (by rfl) ⟨520322, by rfl⟩ : syracuseStep 2775053 = 1040645) (by norm_num)
theorem B3700781 : Blo 1644021 3700781 := bbase (se 3 (by rfl) ⟨693896, by rfl⟩ : syracuseStep 3700781 = 1387793) (by norm_num)
theorem B2635877 : Blo 1644021 2635877 := bbase (se 4 (by rfl) ⟨247113, by rfl⟩ : syracuseStep 2635877 = 494227) (by norm_num)
theorem B3700853 : Blo 1644021 3700853 := bbase (se 5 (by rfl) ⟨173477, by rfl⟩ : syracuseStep 3700853 = 346955) (by norm_num)
theorem B2775181 : Blo 1644021 2775181 := bbase (se 3 (by rfl) ⟨520346, by rfl⟩ : syracuseStep 2775181 = 1040693) (by norm_num)
theorem B3512477 : Blo 1644021 3512477 := bbase (se 3 (by rfl) ⟨658589, by rfl⟩ : syracuseStep 3512477 = 1317179) (by norm_num)
theorem B3700925 : Blo 1644021 3700925 := bbase (se 3 (by rfl) ⟨693923, by rfl⟩ : syracuseStep 3700925 = 1387847) (by norm_num)
theorem B1849549 : Blo 1644021 1849549 := bbase (se 3 (by rfl) ⟨346790, by rfl⟩ : syracuseStep 1849549 = 693581) (by norm_num)
theorem B17832149 : Blo 1644021 17832149 := bbase (se 7 (by rfl) ⟨208970, by rfl⟩ : syracuseStep 17832149 = 417941) (by norm_num)
theorem B2775269 : Blo 1644021 2775269 := bbase (se 4 (by rfl) ⟨260181, by rfl⟩ : syracuseStep 2775269 = 520363) (by norm_num)
theorem B1849585 : Blo 1644021 1849585 := bbase (se 2 (by rfl) ⟨693594, by rfl⟩ : syracuseStep 1849585 = 1387189) (by norm_num)
theorem B3700997 : Blo 1644021 3700997 := bbase (se 4 (by rfl) ⟨346968, by rfl⟩ : syracuseStep 3700997 = 693937) (by norm_num)
theorem B1849621 : Blo 1644021 1849621 := bbase (se 6 (by rfl) ⟨43350, by rfl⟩ : syracuseStep 1849621 = 86701) (by norm_num)
theorem B1849657 : Blo 1644021 1849657 := bbase (se 2 (by rfl) ⟨693621, by rfl⟩ : syracuseStep 1849657 = 1387243) (by norm_num)
theorem B3701069 : Blo 1644021 3701069 := bbase (se 3 (by rfl) ⟨693950, by rfl⟩ : syracuseStep 3701069 = 1387901) (by norm_num)
theorem B1849693 : Blo 1644021 1849693 := bbase (se 3 (by rfl) ⟨346817, by rfl⟩ : syracuseStep 1849693 = 693635) (by norm_num)
theorem B2775397 : Blo 1644021 2775397 := bbase (se 4 (by rfl) ⟨260193, by rfl⟩ : syracuseStep 2775397 = 520387) (by norm_num)
theorem B2341229 : Blo 1644021 2341229 := bbase (se 3 (by rfl) ⟨438980, by rfl⟩ : syracuseStep 2341229 = 877961) (by norm_num)
theorem B4446581 : Blo 1644021 4446581 := bbase (se 5 (by rfl) ⟨208433, by rfl⟩ : syracuseStep 4446581 = 416867) (by norm_num)
theorem B1849729 : Blo 1644021 1849729 := bbase (se 2 (by rfl) ⟨693648, by rfl⟩ : syracuseStep 1849729 = 1387297) (by norm_num)
theorem B3701141 : Blo 1644021 3701141 := bbase (se 6 (by rfl) ⟨86745, by rfl⟩ : syracuseStep 3701141 = 173491) (by norm_num)
theorem B5003669 : Blo 1644021 5003669 := bbase (se 6 (by rfl) ⟨117273, by rfl⟩ : syracuseStep 5003669 = 234547) (by norm_num)
theorem B1849765 : Blo 1644021 1849765 := bbase (se 4 (by rfl) ⟨173415, by rfl⟩ : syracuseStep 1849765 = 346831) (by norm_num)
theorem B5552549 : Blo 1644021 5552549 := bbase (se 4 (by rfl) ⟨520551, by rfl⟩ : syracuseStep 5552549 = 1041103) (by norm_num)
theorem B2775485 : Blo 1644021 2775485 := bbase (se 3 (by rfl) ⟨520403, by rfl⟩ : syracuseStep 2775485 = 1040807) (by norm_num)
theorem B1849801 : Blo 1644021 1849801 := bbase (se 2 (by rfl) ⟨693675, by rfl⟩ : syracuseStep 1849801 = 1387351) (by norm_num)
theorem B3701213 : Blo 1644021 3701213 := bbase (se 3 (by rfl) ⟨693977, by rfl⟩ : syracuseStep 3701213 = 1387955) (by norm_num)
theorem B1849837 : Blo 1644021 1849837 := bbase (se 3 (by rfl) ⟨346844, by rfl⟩ : syracuseStep 1849837 = 693689) (by norm_num)
theorem B1849873 : Blo 1644021 1849873 := bbase (se 2 (by rfl) ⟨693702, by rfl⟩ : syracuseStep 1849873 = 1387405) (by norm_num)
theorem B3701285 : Blo 1644021 3701285 := bbase (se 4 (by rfl) ⟨346995, by rfl⟩ : syracuseStep 3701285 = 693991) (by norm_num)
theorem B1849909 : Blo 1644021 1849909 := bbase (se 5 (by rfl) ⟨86714, by rfl⟩ : syracuseStep 1849909 = 173429) (by norm_num)
theorem B2775613 : Blo 1644021 2775613 := bbase (se 3 (by rfl) ⟨520427, by rfl⟩ : syracuseStep 2775613 = 1040855) (by norm_num)
theorem B1849945 : Blo 1644021 1849945 := bbase (se 2 (by rfl) ⟨693729, by rfl⟩ : syracuseStep 1849945 = 1387459) (by norm_num)
theorem B3750509 : Blo 1644021 3750509 := bbase (se 3 (by rfl) ⟨703220, by rfl⟩ : syracuseStep 3750509 = 1406441) (by norm_num)
theorem B3701357 : Blo 1644021 3701357 := bbase (se 3 (by rfl) ⟨694004, by rfl⟩ : syracuseStep 3701357 = 1388009) (by norm_num)
theorem B1849981 : Blo 1644021 1849981 := bbase (se 3 (by rfl) ⟨346871, by rfl⟩ : syracuseStep 1849981 = 693743) (by norm_num)
theorem B2775701 : Blo 1644021 2775701 := bbase (se 6 (by rfl) ⟨65055, by rfl⟩ : syracuseStep 2775701 = 130111) (by norm_num)
theorem B8329877 : Blo 1644021 8329877 := bbase (se 6 (by rfl) ⟨195231, by rfl⟩ : syracuseStep 8329877 = 390463) (by norm_num)
theorem B6249109 : Blo 1644021 6249109 := bbase (se 6 (by rfl) ⟨146463, by rfl⟩ : syracuseStep 6249109 = 292927) (by norm_num)
theorem B1850017 : Blo 1644021 1850017 := bbase (se 2 (by rfl) ⟨693756, by rfl⟩ : syracuseStep 1850017 = 1387513) (by norm_num)
theorem B3701429 : Blo 1644021 3701429 := bbase (se 5 (by rfl) ⟨173504, by rfl⟩ : syracuseStep 3701429 = 347009) (by norm_num)
theorem B1850053 : Blo 1644021 1850053 := bbase (se 4 (by rfl) ⟨173442, by rfl⟩ : syracuseStep 1850053 = 346885) (by norm_num)
theorem B1850089 : Blo 1644021 1850089 := bbase (se 2 (by rfl) ⟨693783, by rfl⟩ : syracuseStep 1850089 = 1387567) (by norm_num)
theorem B3750637 : Blo 1644021 3750637 := bbase (se 3 (by rfl) ⟨703244, by rfl⟩ : syracuseStep 3750637 = 1406489) (by norm_num)
theorem B3701501 : Blo 1644021 3701501 := bbase (se 3 (by rfl) ⟨694031, by rfl⟩ : syracuseStep 3701501 = 1388063) (by norm_num)
theorem B1850125 : Blo 1644021 1850125 := bbase (se 3 (by rfl) ⟨346898, by rfl⟩ : syracuseStep 1850125 = 693797) (by norm_num)
theorem B2775829 : Blo 1644021 2775829 := bbase (se 6 (by rfl) ⟨65058, by rfl⟩ : syracuseStep 2775829 = 130117) (by norm_num)
theorem B8010533 : Blo 1644021 8010533 := bbase (se 4 (by rfl) ⟨750987, by rfl⟩ : syracuseStep 8010533 = 1501975) (by norm_num)
theorem B1850161 : Blo 1644021 1850161 := bbase (se 2 (by rfl) ⟨693810, by rfl⟩ : syracuseStep 1850161 = 1387621) (by norm_num)
theorem B3701573 : Blo 1644021 3701573 := bbase (se 4 (by rfl) ⟨347022, by rfl⟩ : syracuseStep 3701573 = 694045) (by norm_num)
theorem B1850197 : Blo 1644021 1850197 := bbase (se 9 (by rfl) ⟨5420, by rfl⟩ : syracuseStep 1850197 = 10841) (by norm_num)
theorem B5552981 : Blo 1644021 5552981 := bbase (se 9 (by rfl) ⟨16268, by rfl⟩ : syracuseStep 5552981 = 32537) (by norm_num)
theorem B4684645 : Blo 1644021 4684645 := bbase (se 4 (by rfl) ⟨439185, by rfl⟩ : syracuseStep 4684645 = 878371) (by norm_num)
theorem B2775917 : Blo 1644021 2775917 := bbase (se 3 (by rfl) ⟨520484, by rfl⟩ : syracuseStep 2775917 = 1040969) (by norm_num)
theorem B1850233 : Blo 1644021 1850233 := bbase (se 2 (by rfl) ⟨693837, by rfl⟩ : syracuseStep 1850233 = 1387675) (by norm_num)
theorem B3701645 : Blo 1644021 3701645 := bbase (se 3 (by rfl) ⟨694058, by rfl⟩ : syracuseStep 3701645 = 1388117) (by norm_num)
theorem B1850269 : Blo 1644021 1850269 := bbase (se 3 (by rfl) ⟨346925, by rfl⟩ : syracuseStep 1850269 = 693851) (by norm_num)
theorem B1850305 : Blo 1644021 1850305 := bbase (se 2 (by rfl) ⟨693864, by rfl⟩ : syracuseStep 1850305 = 1387729) (by norm_num)
theorem B6249413 : Blo 1644021 6249413 := bbase (se 4 (by rfl) ⟨585882, by rfl⟩ : syracuseStep 6249413 = 1171765) (by norm_num)
theorem B3701717 : Blo 1644021 3701717 := bbase (se 7 (by rfl) ⟨43379, by rfl⟩ : syracuseStep 3701717 = 86759) (by norm_num)
theorem B1850341 : Blo 1644021 1850341 := bbase (se 4 (by rfl) ⟨173469, by rfl⟩ : syracuseStep 1850341 = 346939) (by norm_num)
theorem B2776045 : Blo 1644021 2776045 := bbase (se 3 (by rfl) ⟨520508, by rfl⟩ : syracuseStep 2776045 = 1041017) (by norm_num)
theorem B1850377 : Blo 1644021 1850377 := bbase (se 2 (by rfl) ⟨693891, by rfl⟩ : syracuseStep 1850377 = 1387783) (by norm_num)
theorem B3513365 : Blo 1644021 3513365 := bbase (se 6 (by rfl) ⟨82344, by rfl⟩ : syracuseStep 3513365 = 164689) (by norm_num)
theorem B3701789 : Blo 1644021 3701789 := bbase (se 3 (by rfl) ⟨694085, by rfl⟩ : syracuseStep 3701789 = 1388171) (by norm_num)
theorem B1850413 : Blo 1644021 1850413 := bbase (se 3 (by rfl) ⟨346952, by rfl⟩ : syracuseStep 1850413 = 693905) (by norm_num)
theorem B2776133 : Blo 1644021 2776133 := bbase (se 4 (by rfl) ⟨260262, by rfl⟩ : syracuseStep 2776133 = 520525) (by norm_num)
theorem B1850449 : Blo 1644021 1850449 := bbase (se 2 (by rfl) ⟨693918, by rfl⟩ : syracuseStep 1850449 = 1387837) (by norm_num)
theorem B2341981 : Blo 1644021 2341981 := bbase (se 3 (by rfl) ⟨439121, by rfl⟩ : syracuseStep 2341981 = 878243) (by norm_num)
theorem B3701861 : Blo 1644021 3701861 := bbase (se 4 (by rfl) ⟨347049, by rfl⟩ : syracuseStep 3701861 = 694099) (by norm_num)
theorem B1850485 : Blo 1644021 1850485 := bbase (se 5 (by rfl) ⟨86741, by rfl⟩ : syracuseStep 1850485 = 173483) (by norm_num)
theorem B1850521 : Blo 1644021 1850521 := bbase (se 2 (by rfl) ⟨693945, by rfl⟩ : syracuseStep 1850521 = 1387891) (by norm_num)
theorem B3701933 : Blo 1644021 3701933 := bbase (se 3 (by rfl) ⟨694112, by rfl⟩ : syracuseStep 3701933 = 1388225) (by norm_num)
theorem B1850557 : Blo 1644021 1850557 := bbase (se 3 (by rfl) ⟨346979, by rfl⟩ : syracuseStep 1850557 = 693959) (by norm_num)
theorem B2776261 : Blo 1644021 2776261 := bbase (se 4 (by rfl) ⟨260274, by rfl⟩ : syracuseStep 2776261 = 520549) (by norm_num)
theorem B1850593 : Blo 1644021 1850593 := bbase (se 2 (by rfl) ⟨693972, by rfl⟩ : syracuseStep 1850593 = 1387945) (by norm_num)
theorem B1875181 : Blo 1644021 1875181 := bbase (se 3 (by rfl) ⟨351596, by rfl⟩ : syracuseStep 1875181 = 703193) (by norm_num)
theorem B3702005 : Blo 1644021 3702005 := bbase (se 5 (by rfl) ⟨173531, by rfl⟩ : syracuseStep 3702005 = 347063) (by norm_num)
theorem B1850629 : Blo 1644021 1850629 := bbase (se 4 (by rfl) ⟨173496, by rfl⟩ : syracuseStep 1850629 = 346993) (by norm_num)
theorem B5553413 : Blo 1644021 5553413 := bbase (se 4 (by rfl) ⟨520632, by rfl⟩ : syracuseStep 5553413 = 1041265) (by norm_num)
theorem B3513613 : Blo 1644021 3513613 := bbase (se 3 (by rfl) ⟨658802, by rfl⟩ : syracuseStep 3513613 = 1317605) (by norm_num)
theorem B2776349 : Blo 1644021 2776349 := bbase (se 3 (by rfl) ⟨520565, by rfl⟩ : syracuseStep 2776349 = 1041131) (by norm_num)
theorem B1850665 : Blo 1644021 1850665 := bbase (se 2 (by rfl) ⟨693999, by rfl⟩ : syracuseStep 1850665 = 1387999) (by norm_num)
theorem B3702077 : Blo 1644021 3702077 := bbase (se 3 (by rfl) ⟨694139, by rfl⟩ : syracuseStep 3702077 = 1388279) (by norm_num)
theorem B1850701 : Blo 1644021 1850701 := bbase (se 3 (by rfl) ⟨347006, by rfl⟩ : syracuseStep 1850701 = 694013) (by norm_num)
theorem B1850737 : Blo 1644021 1850737 := bbase (se 2 (by rfl) ⟨694026, by rfl⟩ : syracuseStep 1850737 = 1388053) (by norm_num)
theorem B3751285 : Blo 1644021 3751285 := bbase (se 5 (by rfl) ⟨175841, by rfl⟩ : syracuseStep 3751285 = 351683) (by norm_num)
theorem B3702149 : Blo 1644021 3702149 := bbase (se 4 (by rfl) ⟨347076, by rfl⟩ : syracuseStep 3702149 = 694153) (by norm_num)
theorem B1850773 : Blo 1644021 1850773 := bbase (se 6 (by rfl) ⟨43377, by rfl⟩ : syracuseStep 1850773 = 86755) (by norm_num)
theorem B2776477 : Blo 1644021 2776477 := bbase (se 3 (by rfl) ⟨520589, by rfl⟩ : syracuseStep 2776477 = 1041179) (by norm_num)
theorem B1850809 : Blo 1644021 1850809 := bbase (se 2 (by rfl) ⟨694053, by rfl⟩ : syracuseStep 1850809 = 1388107) (by norm_num)
theorem B3702221 : Blo 1644021 3702221 := bbase (se 3 (by rfl) ⟨694166, by rfl⟩ : syracuseStep 3702221 = 1388333) (by norm_num)
theorem B1850845 : Blo 1644021 1850845 := bbase (se 3 (by rfl) ⟨347033, by rfl⟩ : syracuseStep 1850845 = 694067) (by norm_num)
theorem B2776565 : Blo 1644021 2776565 := bbase (se 5 (by rfl) ⟨130151, by rfl⟩ : syracuseStep 2776565 = 260303) (by norm_num)
theorem B1850881 : Blo 1644021 1850881 := bbase (se 2 (by rfl) ⟨694080, by rfl⟩ : syracuseStep 1850881 = 1388161) (by norm_num)
theorem B3702293 : Blo 1644021 3702293 := bbase (se 6 (by rfl) ⟨86772, by rfl⟩ : syracuseStep 3702293 = 173545) (by norm_num)
theorem B1850917 : Blo 1644021 1850917 := bbase (se 4 (by rfl) ⟨173523, by rfl⟩ : syracuseStep 1850917 = 347047) (by norm_num)
theorem B1850953 : Blo 1644021 1850953 := bbase (se 2 (by rfl) ⟨694107, by rfl⟩ : syracuseStep 1850953 = 1388215) (by norm_num)
theorem B3702365 : Blo 1644021 3702365 := bbase (se 3 (by rfl) ⟨694193, by rfl⟩ : syracuseStep 3702365 = 1388387) (by norm_num)
theorem B1850989 : Blo 1644021 1850989 := bbase (se 3 (by rfl) ⟨347060, by rfl⟩ : syracuseStep 1850989 = 694121) (by norm_num)
theorem B2776693 : Blo 1644021 2776693 := bbase (se 5 (by rfl) ⟨130157, by rfl⟩ : syracuseStep 2776693 = 260315) (by norm_num)
theorem B1851025 : Blo 1644021 1851025 := bbase (se 2 (by rfl) ⟨694134, by rfl⟩ : syracuseStep 1851025 = 1388269) (by norm_num)
theorem B2670229 : Blo 1644021 2670229 := bbase (se 6 (by rfl) ⟨62583, by rfl⟩ : syracuseStep 2670229 = 125167) (by norm_num)
theorem B3702437 : Blo 1644021 3702437 := bbase (se 4 (by rfl) ⟨347103, by rfl⟩ : syracuseStep 3702437 = 694207) (by norm_num)
theorem B1851061 : Blo 1644021 1851061 := bbase (se 5 (by rfl) ⟨86768, by rfl⟩ : syracuseStep 1851061 = 173537) (by norm_num)
theorem B5553845 : Blo 1644021 5553845 := bbase (se 5 (by rfl) ⟨260336, by rfl⟩ : syracuseStep 5553845 = 520673) (by norm_num)
theorem B2776781 : Blo 1644021 2776781 := bbase (se 3 (by rfl) ⟨520646, by rfl⟩ : syracuseStep 2776781 = 1041293) (by norm_num)
theorem B1851097 : Blo 1644021 1851097 := bbase (se 2 (by rfl) ⟨694161, by rfl⟩ : syracuseStep 1851097 = 1388323) (by norm_num)
theorem B3702509 : Blo 1644021 3702509 := bbase (se 3 (by rfl) ⟨694220, by rfl⟩ : syracuseStep 3702509 = 1388441) (by norm_num)
theorem B1851133 : Blo 1644021 1851133 := bbase (se 3 (by rfl) ⟨347087, by rfl⟩ : syracuseStep 1851133 = 694175) (by norm_num)
theorem B3514117 : Blo 1644021 3514117 := bbase (se 4 (by rfl) ⟨329448, by rfl⟩ : syracuseStep 3514117 = 658897) (by norm_num)
theorem B1851169 : Blo 1644021 1851169 := bbase (se 2 (by rfl) ⟨694188, by rfl⟩ : syracuseStep 1851169 = 1388377) (by norm_num)
theorem B3702581 : Blo 1644021 3702581 := bbase (se 5 (by rfl) ⟨173558, by rfl⟩ : syracuseStep 3702581 = 347117) (by norm_num)
theorem B1851205 : Blo 1644021 1851205 := bbase (se 4 (by rfl) ⟨173550, by rfl⟩ : syracuseStep 1851205 = 347101) (by norm_num)
theorem B2776909 : Blo 1644021 2776909 := bbase (se 3 (by rfl) ⟨520670, by rfl⟩ : syracuseStep 2776909 = 1041341) (by norm_num)
theorem B1875793 : Blo 1644021 1875793 := bbase (se 2 (by rfl) ⟨703422, by rfl⟩ : syracuseStep 1875793 = 1406845) (by norm_num)
theorem B7905109 : Blo 1644021 7905109 := bbase (se 9 (by rfl) ⟨23159, by rfl⟩ : syracuseStep 7905109 = 46319) (by norm_num)
theorem B12492629 : Blo 1644021 12492629 := bbase (se 9 (by rfl) ⟨36599, by rfl⟩ : syracuseStep 12492629 = 73199) (by norm_num)
theorem B9371477 : Blo 1644021 9371477 := bbase (se 9 (by rfl) ⟨27455, by rfl⟩ : syracuseStep 9371477 = 54911) (by norm_num)
theorem B5930837 : Blo 1644021 5930837 := bbase (se 9 (by rfl) ⟨17375, by rfl⟩ : syracuseStep 5930837 = 34751) (by norm_num)
theorem B1851241 : Blo 1644021 1851241 := bbase (se 2 (by rfl) ⟨694215, by rfl⟩ : syracuseStep 1851241 = 1388431) (by norm_num)
theorem B2342773 : Blo 1644021 2342773 := bbase (se 5 (by rfl) ⟨109817, by rfl⟩ : syracuseStep 2342773 = 219635) (by norm_num)
theorem B3702653 : Blo 1644021 3702653 := bbase (se 3 (by rfl) ⟨694247, by rfl⟩ : syracuseStep 3702653 = 1388495) (by norm_num)
theorem B1851277 : Blo 1644021 1851277 := bbase (se 3 (by rfl) ⟨347114, by rfl⟩ : syracuseStep 1851277 = 694229) (by norm_num)
theorem B2776997 : Blo 1644021 2776997 := bbase (se 4 (by rfl) ⟨260343, by rfl⟩ : syracuseStep 2776997 = 520687) (by norm_num)
theorem B8331173 : Blo 1644021 8331173 := bbase (se 4 (by rfl) ⟨781047, by rfl⟩ : syracuseStep 8331173 = 1562095) (by norm_num)
theorem B3334061 : Blo 1644021 3334061 := bbase (se 3 (by rfl) ⟨625136, by rfl⟩ : syracuseStep 3334061 = 1250273) (by norm_num)
theorem B1851313 : Blo 1644021 1851313 := bbase (se 2 (by rfl) ⟨694242, by rfl⟩ : syracuseStep 1851313 = 1388485) (by norm_num)
theorem B3121085 : Blo 1644021 3121085 := bbase (se 3 (by rfl) ⟨585203, by rfl⟩ : syracuseStep 3121085 = 1170407) (by norm_num)
theorem B3702725 : Blo 1644021 3702725 := bbase (se 4 (by rfl) ⟨347130, by rfl⟩ : syracuseStep 3702725 = 694261) (by norm_num)
theorem B1851349 : Blo 1644021 1851349 := bbase (se 7 (by rfl) ⟨21695, by rfl⟩ : syracuseStep 1851349 = 43391) (by norm_num)
theorem B1851385 : Blo 1644021 1851385 := bbase (se 2 (by rfl) ⟨694269, by rfl⟩ : syracuseStep 1851385 = 1388539) (by norm_num)
theorem B10543117 : Blo 1644021 10543117 := bstep (se 3 (by rfl) ⟨1976834, by rfl⟩ : syracuseStep 10543117 = 3953669) B3953669
theorem B2777105 : Blo 1644021 2777105 := bstep (se 2 (by rfl) ⟨1041414, by rfl⟩ : syracuseStep 2777105 = 2082829) B2082829
theorem B3702833 : Blo 1644021 3702833 := bstep (se 2 (by rfl) ⟨1388562, by rfl⟩ : syracuseStep 3702833 = 2777125) B2777125
theorem B2080819 : Blo 1644021 2080819 := bstep (se 1 (by rfl) ⟨1560614, by rfl⟩ : syracuseStep 2080819 = 3121229) B3121229
theorem B3702851 : Blo 1644021 3702851 := bstep (se 1 (by rfl) ⟨2777138, by rfl⟩ : syracuseStep 3702851 = 5554277) B5554277
theorem B4448333 : Blo 1644021 4448333 := bstep (se 3 (by rfl) ⟨834062, by rfl⟩ : syracuseStep 4448333 = 1668125) B1668125
theorem B1851475 : Blo 1644021 1851475 := bstep (se 1 (by rfl) ⟨1388606, by rfl⟩ : syracuseStep 1851475 = 2777213) B2777213
theorem B5267587 : Blo 1644021 5267587 := bstep (se 1 (by rfl) ⟨3950690, by rfl⟩ : syracuseStep 5267587 = 7901381) B7901381
theorem B2777233 : Blo 1644021 2777233 := bstep (se 2 (by rfl) ⟨1041462, by rfl⟩ : syracuseStep 2777233 = 2082925) B2082925
theorem B8323235 : Blo 1644021 8323235 := bstep (se 1 (by rfl) ⟨6242426, by rfl⟩ : syracuseStep 8323235 = 12484853) B12484853
theorem B2777267 : Blo 1644021 2777267 := bstep (se 1 (by rfl) ⟨2082950, by rfl⟩ : syracuseStep 2777267 = 4165901) B4165901
theorem B8896709 : Blo 1644021 8896709 := bstep (se 4 (by rfl) ⟨834066, by rfl⟩ : syracuseStep 8896709 = 1668133) B1668133
theorem B5554385 : Blo 1644021 5554385 := bstep (se 2 (by rfl) ⟨2082894, by rfl⟩ : syracuseStep 5554385 = 4165789) B4165789
theorem B1851619 : Blo 1644021 1851619 := bstep (se 1 (by rfl) ⟨1388714, by rfl⟩ : syracuseStep 1851619 = 2777429) B2777429
theorem B2466035 : Blo 1644021 2466035 := bstep (se 1 (by rfl) ⟨1849526, by rfl⟩ : syracuseStep 2466035 = 3699053) B3699053
theorem B3121411 : Blo 1644021 3121411 := bstep (se 1 (by rfl) ⟨2341058, by rfl⟩ : syracuseStep 3121411 = 4682117) B4682117
theorem B2466065 : Blo 1644021 2466065 := bstep (se 2 (by rfl) ⟨924774, by rfl⟩ : syracuseStep 2466065 = 1849549) B1849549
theorem B2466083 : Blo 1644021 2466083 := bstep (se 1 (by rfl) ⟨1849562, by rfl⟩ : syracuseStep 2466083 = 3699125) B3699125
theorem B5931299 : Blo 1644021 5931299 := bstep (se 1 (by rfl) ⟨4448474, by rfl⟩ : syracuseStep 5931299 = 8896949) B8896949
theorem B6242609 : Blo 1644021 6242609 := bstep (se 2 (by rfl) ⟨2340978, by rfl⟩ : syracuseStep 6242609 = 4681957) B4681957
theorem B2777395 : Blo 1644021 2777395 := bstep (se 1 (by rfl) ⟨2083046, by rfl⟩ : syracuseStep 2777395 = 4166093) B4166093
theorem B2466113 : Blo 1644021 2466113 := bstep (se 2 (by rfl) ⟨924792, by rfl⟩ : syracuseStep 2466113 = 1849585) B1849585
theorem B3703121 : Blo 1644021 3703121 := bstep (se 2 (by rfl) ⟨1388670, by rfl⟩ : syracuseStep 3703121 = 2777341) B2777341
theorem B2466131 : Blo 1644021 2466131 := bstep (se 1 (by rfl) ⟨1849598, by rfl⟩ : syracuseStep 2466131 = 3699197) B3699197
theorem B3703139 : Blo 1644021 3703139 := bstep (se 1 (by rfl) ⟨2777354, by rfl⟩ : syracuseStep 3703139 = 5554709) B5554709
theorem B2466161 : Blo 1644021 2466161 := bstep (se 2 (by rfl) ⟨924810, by rfl⟩ : syracuseStep 2466161 = 1849621) B1849621
theorem B1851763 : Blo 1644021 1851763 := bstep (se 1 (by rfl) ⟨1388822, by rfl⟩ : syracuseStep 1851763 = 2777645) B2777645
theorem B2466179 : Blo 1644021 2466179 := bstep (se 1 (by rfl) ⟨1849634, by rfl⟩ : syracuseStep 2466179 = 3699269) B3699269
theorem B2253187 : Blo 1644021 2253187 := bstep (se 1 (by rfl) ⟨1689890, by rfl⟩ : syracuseStep 2253187 = 3379781) B3379781
theorem B2466209 : Blo 1644021 2466209 := bstep (se 2 (by rfl) ⟨924828, by rfl⟩ : syracuseStep 2466209 = 1849657) B1849657
theorem B3121571 : Blo 1644021 3121571 := bstep (se 1 (by rfl) ⟨2341178, by rfl⟩ : syracuseStep 3121571 = 4682357) B4682357
theorem B7029155 : Blo 1644021 7029155 := bstep (se 1 (by rfl) ⟨5271866, by rfl⟩ : syracuseStep 7029155 = 10543733) B10543733
theorem B5931427 : Blo 1644021 5931427 := bstep (se 1 (by rfl) ⟨4448570, by rfl⟩ : syracuseStep 5931427 = 8897141) B8897141
theorem B2466227 : Blo 1644021 2466227 := bstep (se 1 (by rfl) ⟨1849670, by rfl⟩ : syracuseStep 2466227 = 3699341) B3699341
theorem B2777537 : Blo 1644021 2777537 := bstep (se 2 (by rfl) ⟨1041576, by rfl⟩ : syracuseStep 2777537 = 2083153) B2083153
theorem B4686275 : Blo 1644021 4686275 := bstep (se 1 (by rfl) ⟨3514706, by rfl⟩ : syracuseStep 4686275 = 7029413) B7029413
theorem B2466257 : Blo 1644021 2466257 := bstep (se 2 (by rfl) ⟨924846, by rfl⟩ : syracuseStep 2466257 = 1849693) B1849693
theorem B2466275 : Blo 1644021 2466275 := bstep (se 1 (by rfl) ⟨1849706, by rfl⟩ : syracuseStep 2466275 = 3699413) B3699413
theorem B2466305 : Blo 1644021 2466305 := bstep (se 2 (by rfl) ⟨924864, by rfl⟩ : syracuseStep 2466305 = 1849729) B1849729
theorem B2466323 : Blo 1644021 2466323 := bstep (se 1 (by rfl) ⟨1849742, by rfl⟩ : syracuseStep 2466323 = 3699485) B3699485
theorem B2081315 : Blo 1644021 2081315 := bstep (se 1 (by rfl) ⟨1560986, by rfl⟩ : syracuseStep 2081315 = 3121973) B3121973
theorem B2466353 : Blo 1644021 2466353 := bstep (se 2 (by rfl) ⟨924882, by rfl⟩ : syracuseStep 2466353 = 1849765) B1849765
theorem B2466371 : Blo 1644021 2466371 := bstep (se 1 (by rfl) ⟨1849778, by rfl⟩ : syracuseStep 2466371 = 3699557) B3699557
theorem B2466401 : Blo 1644021 2466401 := bstep (se 2 (by rfl) ⟨924900, by rfl⟩ : syracuseStep 2466401 = 1849801) B1849801
theorem B3703409 : Blo 1644021 3703409 := bstep (se 2 (by rfl) ⟨1388778, by rfl⟩ : syracuseStep 3703409 = 2777557) B2777557
theorem B2466419 : Blo 1644021 2466419 := bstep (se 1 (by rfl) ⟨1849814, by rfl⟩ : syracuseStep 2466419 = 3699629) B3699629
theorem B3703427 : Blo 1644021 3703427 := bstep (se 1 (by rfl) ⟨2777570, by rfl⟩ : syracuseStep 3703427 = 5555141) B5555141
theorem B2466449 : Blo 1644021 2466449 := bstep (se 2 (by rfl) ⟨924918, by rfl⟩ : syracuseStep 2466449 = 1849837) B1849837
theorem B2466467 : Blo 1644021 2466467 := bstep (se 1 (by rfl) ⟨1849850, by rfl⟩ : syracuseStep 2466467 = 3699701) B3699701
theorem B6668963 : Blo 1644021 6668963 := bstep (se 1 (by rfl) ⟨5001722, by rfl⟩ : syracuseStep 6668963 = 10003445) B10003445
theorem B4162225 : Blo 1644021 4162225 := bstep (se 2 (by rfl) ⟨1560834, by rfl⟩ : syracuseStep 4162225 = 3121669) B3121669
theorem B2466497 : Blo 1644021 2466497 := bstep (se 2 (by rfl) ⟨924936, by rfl⟩ : syracuseStep 2466497 = 1849873) B1849873
theorem B2466515 : Blo 1644021 2466515 := bstep (se 1 (by rfl) ⟨1849886, by rfl⟩ : syracuseStep 2466515 = 3699773) B3699773
theorem B5702381 : Blo 1644021 5702381 := bstep (se 3 (by rfl) ⟨1069196, by rfl⟩ : syracuseStep 5702381 = 2138393) B2138393
theorem B5554925 : Blo 1644021 5554925 := bstep (se 3 (by rfl) ⟨1041548, by rfl⟩ : syracuseStep 5554925 = 2083097) B2083097
theorem B2466545 : Blo 1644021 2466545 := bstep (se 2 (by rfl) ⟨924954, by rfl⟩ : syracuseStep 2466545 = 1849909) B1849909
theorem B2466563 : Blo 1644021 2466563 := bstep (se 1 (by rfl) ⟨1849922, by rfl⟩ : syracuseStep 2466563 = 3699845) B3699845
theorem B4686605 : Blo 1644021 4686605 := bstep (se 3 (by rfl) ⟨878738, by rfl⟩ : syracuseStep 4686605 = 1757477) B1757477
theorem B2466593 : Blo 1644021 2466593 := bstep (se 2 (by rfl) ⟨924972, by rfl⟩ : syracuseStep 2466593 = 1849945) B1849945
theorem B5554979 : Blo 1644021 5554979 := bstep (se 1 (by rfl) ⟨4166234, by rfl⟩ : syracuseStep 5554979 = 8332469) B8332469
theorem B2466611 : Blo 1644021 2466611 := bstep (se 1 (by rfl) ⟨1849958, by rfl⟩ : syracuseStep 2466611 = 3699917) B3699917
theorem B2466641 : Blo 1644021 2466641 := bstep (se 2 (by rfl) ⟨924990, by rfl⟩ : syracuseStep 2466641 = 1849981) B1849981
theorem B4686673 : Blo 1644021 4686673 := bstep (se 2 (by rfl) ⟨1757502, by rfl⟩ : syracuseStep 4686673 = 3515005) B3515005
theorem B2466659 : Blo 1644021 2466659 := bstep (se 1 (by rfl) ⟨1849994, by rfl⟩ : syracuseStep 2466659 = 3699989) B3699989
theorem B8332145 : Blo 1644021 8332145 := bstep (se 2 (by rfl) ⟨3124554, by rfl⟩ : syracuseStep 8332145 = 6249109) B6249109
theorem B2466689 : Blo 1644021 2466689 := bstep (se 2 (by rfl) ⟨925008, by rfl⟩ : syracuseStep 2466689 = 1850017) B1850017
theorem B2466707 : Blo 1644021 2466707 := bstep (se 1 (by rfl) ⟨1850030, by rfl⟩ : syracuseStep 2466707 = 3700061) B3700061
theorem B2466737 : Blo 1644021 2466737 := bstep (se 2 (by rfl) ⟨925026, by rfl⟩ : syracuseStep 2466737 = 1850053) B1850053
theorem B4162499 : Blo 1644021 4162499 := bstep (se 1 (by rfl) ⟨3121874, by rfl⟩ : syracuseStep 4162499 = 6243749) B6243749
theorem B2466755 : Blo 1644021 2466755 := bstep (se 1 (by rfl) ⟨1850066, by rfl⟩ : syracuseStep 2466755 = 3700133) B3700133
theorem B8324045 : Blo 1644021 8324045 := bstep (se 3 (by rfl) ⟨1560758, by rfl⟩ : syracuseStep 8324045 = 3121517) B3121517
theorem B6243277 : Blo 1644021 6243277 := bstep (se 3 (by rfl) ⟨1170614, by rfl⟩ : syracuseStep 6243277 = 2341229) B2341229
theorem B2466785 : Blo 1644021 2466785 := bstep (se 2 (by rfl) ⟨925044, by rfl⟩ : syracuseStep 2466785 = 1850089) B1850089
theorem B2466803 : Blo 1644021 2466803 := bstep (se 1 (by rfl) ⟨1850102, by rfl⟩ : syracuseStep 2466803 = 3700205) B3700205
theorem B2466833 : Blo 1644021 2466833 := bstep (se 2 (by rfl) ⟨925062, by rfl⟩ : syracuseStep 2466833 = 1850125) B1850125
theorem B2466851 : Blo 1644021 2466851 := bstep (se 1 (by rfl) ⟨1850138, by rfl⟩ : syracuseStep 2466851 = 3700277) B3700277
theorem B7906339 : Blo 1644021 7906339 := bstep (se 1 (by rfl) ⟨5929754, by rfl⟩ : syracuseStep 7906339 = 11859509) B11859509
theorem B5555249 : Blo 1644021 5555249 := bstep (se 2 (by rfl) ⟨2083218, by rfl⟩ : syracuseStep 5555249 = 4166437) B4166437
theorem B2466881 : Blo 1644021 2466881 := bstep (se 2 (by rfl) ⟨925080, by rfl⟩ : syracuseStep 2466881 = 1850161) B1850161
theorem B2466899 : Blo 1644021 2466899 := bstep (se 1 (by rfl) ⟨1850174, by rfl⟩ : syracuseStep 2466899 = 3700349) B3700349
theorem B4686947 : Blo 1644021 4686947 := bstep (se 1 (by rfl) ⟨3515210, by rfl⟩ : syracuseStep 4686947 = 7030421) B7030421
theorem B2466929 : Blo 1644021 2466929 := bstep (se 2 (by rfl) ⟨925098, by rfl⟩ : syracuseStep 2466929 = 1850197) B1850197
theorem B4162691 : Blo 1644021 4162691 := bstep (se 1 (by rfl) ⟨3122018, by rfl⟩ : syracuseStep 4162691 = 6244037) B6244037
theorem B2466947 : Blo 1644021 2466947 := bstep (se 1 (by rfl) ⟨1850210, by rfl⟩ : syracuseStep 2466947 = 3700421) B3700421
theorem B2466977 : Blo 1644021 2466977 := bstep (se 2 (by rfl) ⟨925116, by rfl⟩ : syracuseStep 2466977 = 1850233) B1850233
theorem B9364643 : Blo 1644021 9364643 := bstep (se 1 (by rfl) ⟨7023482, by rfl⟩ : syracuseStep 9364643 = 14046965) B14046965
theorem B2466995 : Blo 1644021 2466995 := bstep (se 1 (by rfl) ⟨1850246, by rfl⟩ : syracuseStep 2466995 = 3700493) B3700493
theorem B2671795 : Blo 1644021 2671795 := bstep (se 1 (by rfl) ⟨2003846, by rfl⟩ : syracuseStep 2671795 = 4007693) B4007693
theorem B5268689 : Blo 1644021 5268689 := bstep (se 2 (by rfl) ⟨1975758, by rfl⟩ : syracuseStep 5268689 = 3951517) B3951517
theorem B2467025 : Blo 1644021 2467025 := bstep (se 2 (by rfl) ⟨925134, by rfl⟩ : syracuseStep 2467025 = 1850269) B1850269
theorem B2467043 : Blo 1644021 2467043 := bstep (se 1 (by rfl) ⟨1850282, by rfl⟩ : syracuseStep 2467043 = 3700565) B3700565
theorem B2082019 : Blo 1644021 2082019 := bstep (se 1 (by rfl) ⟨1561514, by rfl⟩ : syracuseStep 2082019 = 3123029) B3123029
theorem B2467073 : Blo 1644021 2467073 := bstep (se 2 (by rfl) ⟨925152, by rfl⟩ : syracuseStep 2467073 = 1850305) B1850305
theorem B2467091 : Blo 1644021 2467091 := bstep (se 1 (by rfl) ⟨1850318, by rfl⟩ : syracuseStep 2467091 = 3700637) B3700637
theorem B2467121 : Blo 1644021 2467121 := bstep (se 2 (by rfl) ⟨925170, by rfl⟩ : syracuseStep 2467121 = 1850341) B1850341
theorem B2467139 : Blo 1644021 2467139 := bstep (se 1 (by rfl) ⟨1850354, by rfl⟩ : syracuseStep 2467139 = 3700709) B3700709
theorem B2082115 : Blo 1644021 2082115 := bstep (se 1 (by rfl) ⟨1561586, by rfl⟩ : syracuseStep 2082115 = 3123173) B3123173
theorem B5268817 : Blo 1644021 5268817 := bstep (se 2 (by rfl) ⟨1975806, by rfl⟩ : syracuseStep 5268817 = 3951613) B3951613
theorem B2467169 : Blo 1644021 2467169 := bstep (se 2 (by rfl) ⟨925188, by rfl⟩ : syracuseStep 2467169 = 1850377) B1850377
theorem B2467187 : Blo 1644021 2467187 := bstep (se 1 (by rfl) ⟨1850390, by rfl⟩ : syracuseStep 2467187 = 3700781) B3700781
theorem B2467217 : Blo 1644021 2467217 := bstep (se 2 (by rfl) ⟨925206, by rfl⟩ : syracuseStep 2467217 = 1850413) B1850413
theorem B2467235 : Blo 1644021 2467235 := bstep (se 1 (by rfl) ⟨1850426, by rfl⟩ : syracuseStep 2467235 = 3700853) B3700853
theorem B2467265 : Blo 1644021 2467265 := bstep (se 2 (by rfl) ⟨925224, by rfl⟩ : syracuseStep 2467265 = 1850449) B1850449
theorem B152020421 : Blo 1644021 152020421 := bstep (se 4 (by rfl) ⟨14251914, by rfl⟩ : syracuseStep 152020421 = 28503829) B28503829
theorem B3122641 : Blo 1644021 3122641 := bstep (se 2 (by rfl) ⟨1170990, by rfl⟩ : syracuseStep 3122641 = 2341981) B2341981
theorem B4220369 : Blo 1644021 4220369 := bstep (se 2 (by rfl) ⟨1582638, by rfl⟩ : syracuseStep 4220369 = 3165277) B3165277
theorem B2467283 : Blo 1644021 2467283 := bstep (se 1 (by rfl) ⟨1850462, by rfl⟩ : syracuseStep 2467283 = 3700925) B3700925
theorem B11888099 : Blo 1644021 11888099 := bstep (se 1 (by rfl) ⟨8916074, by rfl⟩ : syracuseStep 11888099 = 17832149) B17832149
theorem B2467313 : Blo 1644021 2467313 := bstep (se 2 (by rfl) ⟨925242, by rfl⟩ : syracuseStep 2467313 = 1850485) B1850485
theorem B2467331 : Blo 1644021 2467331 := bstep (se 1 (by rfl) ⟨1850498, by rfl⟩ : syracuseStep 2467331 = 3700997) B3700997
theorem B2467361 : Blo 1644021 2467361 := bstep (se 2 (by rfl) ⟨925260, by rfl⟩ : syracuseStep 2467361 = 1850521) B1850521
theorem B2467379 : Blo 1644021 2467379 := bstep (se 1 (by rfl) ⟨1850534, by rfl⟩ : syracuseStep 2467379 = 3701069) B3701069
theorem B2467409 : Blo 1644021 2467409 := bstep (se 2 (by rfl) ⟨925278, by rfl⟩ : syracuseStep 2467409 = 1850557) B1850557
theorem B2467427 : Blo 1644021 2467427 := bstep (se 1 (by rfl) ⟨1850570, by rfl⟩ : syracuseStep 2467427 = 3701141) B3701141
theorem B3335779 : Blo 1644021 3335779 := bstep (se 1 (by rfl) ⟨2501834, by rfl⟩ : syracuseStep 3335779 = 5003669) B5003669
theorem B7030385 : Blo 1644021 7030385 := bstep (se 2 (by rfl) ⟨2636394, by rfl⟩ : syracuseStep 7030385 = 5272789) B5272789
theorem B2467457 : Blo 1644021 2467457 := bstep (se 2 (by rfl) ⟨925296, by rfl⟩ : syracuseStep 2467457 = 1850593) B1850593
theorem B2500241 : Blo 1644021 2500241 := bstep (se 2 (by rfl) ⟨937590, by rfl⟩ : syracuseStep 2500241 = 1875181) B1875181
theorem B2467475 : Blo 1644021 2467475 := bstep (se 1 (by rfl) ⟨1850606, by rfl⟩ : syracuseStep 2467475 = 3701213) B3701213
theorem B2467505 : Blo 1644021 2467505 := bstep (se 2 (by rfl) ⟨925314, by rfl⟩ : syracuseStep 2467505 = 1850629) B1850629
theorem B2467523 : Blo 1644021 2467523 := bstep (se 1 (by rfl) ⟨1850642, by rfl⟩ : syracuseStep 2467523 = 3701285) B3701285
theorem B2467553 : Blo 1644021 2467553 := bstep (se 2 (by rfl) ⟨925332, by rfl⟩ : syracuseStep 2467553 = 1850665) B1850665
theorem B6244067 : Blo 1644021 6244067 := bstep (se 1 (by rfl) ⟨4683050, by rfl⟩ : syracuseStep 6244067 = 9366101) B9366101
theorem B2467571 : Blo 1644021 2467571 := bstep (se 1 (by rfl) ⟨1850678, by rfl⟩ : syracuseStep 2467571 = 3701357) B3701357
theorem B2467601 : Blo 1644021 2467601 := bstep (se 2 (by rfl) ⟨925350, by rfl⟩ : syracuseStep 2467601 = 1850701) B1850701
theorem B2467619 : Blo 1644021 2467619 := bstep (se 1 (by rfl) ⟨1850714, by rfl⟩ : syracuseStep 2467619 = 3701429) B3701429
theorem B2082611 : Blo 1644021 2082611 := bstep (se 1 (by rfl) ⟨1561958, by rfl⟩ : syracuseStep 2082611 = 3123917) B3123917
theorem B2467649 : Blo 1644021 2467649 := bstep (se 2 (by rfl) ⟨925368, by rfl⟩ : syracuseStep 2467649 = 1850737) B1850737
theorem B2467667 : Blo 1644021 2467667 := bstep (se 1 (by rfl) ⟨1850750, by rfl⟩ : syracuseStep 2467667 = 3701501) B3701501
theorem B2467697 : Blo 1644021 2467697 := bstep (se 2 (by rfl) ⟨925386, by rfl⟩ : syracuseStep 2467697 = 1850773) B1850773
theorem B2467715 : Blo 1644021 2467715 := bstep (se 1 (by rfl) ⟨1850786, by rfl⟩ : syracuseStep 2467715 = 3701573) B3701573
theorem B2467745 : Blo 1644021 2467745 := bstep (se 2 (by rfl) ⟨925404, by rfl⟩ : syracuseStep 2467745 = 1850809) B1850809
theorem B2467763 : Blo 1644021 2467763 := bstep (se 1 (by rfl) ⟨1850822, by rfl⟩ : syracuseStep 2467763 = 3701645) B3701645
theorem B16017349 : Blo 1644021 16017349 := bstep (se 4 (by rfl) ⟨1501626, by rfl⟩ : syracuseStep 16017349 = 3003253) B3003253
theorem B2467793 : Blo 1644021 2467793 := bstep (se 2 (by rfl) ⟨925422, by rfl⟩ : syracuseStep 2467793 = 1850845) B1850845
theorem B2467811 : Blo 1644021 2467811 := bstep (se 1 (by rfl) ⟨1850858, by rfl⟩ : syracuseStep 2467811 = 3701717) B3701717
theorem B2467841 : Blo 1644021 2467841 := bstep (se 2 (by rfl) ⟨925440, by rfl⟩ : syracuseStep 2467841 = 1850881) B1850881
theorem B2467859 : Blo 1644021 2467859 := bstep (se 1 (by rfl) ⟨1850894, by rfl⟩ : syracuseStep 2467859 = 3701789) B3701789
theorem B4163633 : Blo 1644021 4163633 := bstep (se 2 (by rfl) ⟨1561362, by rfl⟩ : syracuseStep 4163633 = 3122725) B3122725
theorem B2467889 : Blo 1644021 2467889 := bstep (se 2 (by rfl) ⟨925458, by rfl⟩ : syracuseStep 2467889 = 1850917) B1850917
theorem B2467907 : Blo 1644021 2467907 := bstep (se 1 (by rfl) ⟨1850930, by rfl⟩ : syracuseStep 2467907 = 3701861) B3701861
theorem B2467937 : Blo 1644021 2467937 := bstep (se 2 (by rfl) ⟨925476, by rfl⟩ : syracuseStep 2467937 = 1850953) B1850953
theorem B4163683 : Blo 1644021 4163683 := bstep (se 1 (by rfl) ⟨3122762, by rfl⟩ : syracuseStep 4163683 = 6245525) B6245525
theorem B2467955 : Blo 1644021 2467955 := bstep (se 1 (by rfl) ⟨1850966, by rfl⟩ : syracuseStep 2467955 = 3701933) B3701933
theorem B12486797 : Blo 1644021 12486797 := bstep (se 3 (by rfl) ⟨2341274, by rfl⟩ : syracuseStep 12486797 = 4682549) B4682549
theorem B9365645 : Blo 1644021 9365645 := bstep (se 3 (by rfl) ⟨1756058, by rfl⟩ : syracuseStep 9365645 = 3512117) B3512117
theorem B2467985 : Blo 1644021 2467985 := bstep (se 2 (by rfl) ⟨925494, by rfl⟩ : syracuseStep 2467985 = 1850989) B1850989
theorem B2468003 : Blo 1644021 2468003 := bstep (se 1 (by rfl) ⟨1851002, by rfl⟩ : syracuseStep 2468003 = 3702005) B3702005
theorem B2468033 : Blo 1644021 2468033 := bstep (se 2 (by rfl) ⟨925512, by rfl⟩ : syracuseStep 2468033 = 1851025) B1851025
theorem B8890565 : Blo 1644021 8890565 := bstep (se 4 (by rfl) ⟨833490, by rfl⟩ : syracuseStep 8890565 = 1666981) B1666981
theorem B10545349 : Blo 1644021 10545349 := bstep (se 4 (by rfl) ⟨988626, by rfl⟩ : syracuseStep 10545349 = 1977253) B1977253
theorem B2468051 : Blo 1644021 2468051 := bstep (se 1 (by rfl) ⟨1851038, by rfl⟩ : syracuseStep 2468051 = 3702077) B3702077
theorem B4163825 : Blo 1644021 4163825 := bstep (se 2 (by rfl) ⟨1561434, by rfl⟩ : syracuseStep 4163825 = 3122869) B3122869
theorem B2468081 : Blo 1644021 2468081 := bstep (se 2 (by rfl) ⟨925530, by rfl⟩ : syracuseStep 2468081 = 1851061) B1851061
theorem B4507907 : Blo 1644021 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B2468099 : Blo 1644021 2468099 := bstep (se 1 (by rfl) ⟨1851074, by rfl⟩ : syracuseStep 2468099 = 3702149) B3702149
theorem B2468129 : Blo 1644021 2468129 := bstep (se 2 (by rfl) ⟨925548, by rfl⟩ : syracuseStep 2468129 = 1851097) B1851097
theorem B5269805 : Blo 1644021 5269805 := bstep (se 3 (by rfl) ⟨988088, by rfl⟩ : syracuseStep 5269805 = 1976177) B1976177
theorem B2468147 : Blo 1644021 2468147 := bstep (se 1 (by rfl) ⟨1851110, by rfl⟩ : syracuseStep 2468147 = 3702221) B3702221
theorem B2853185 : Blo 1644021 2853185 := bstep (se 2 (by rfl) ⟨1069944, by rfl⟩ : syracuseStep 2853185 = 2139889) B2139889
theorem B2468177 : Blo 1644021 2468177 := bstep (se 2 (by rfl) ⟨925566, by rfl⟩ : syracuseStep 2468177 = 1851133) B1851133
theorem B2468195 : Blo 1644021 2468195 := bstep (se 1 (by rfl) ⟨1851146, by rfl⟩ : syracuseStep 2468195 = 3702293) B3702293
theorem B6244721 : Blo 1644021 6244721 := bstep (se 2 (by rfl) ⟨2341770, by rfl⟩ : syracuseStep 6244721 = 4683541) B4683541
theorem B2468225 : Blo 1644021 2468225 := bstep (se 2 (by rfl) ⟨925584, by rfl⟩ : syracuseStep 2468225 = 1851169) B1851169
theorem B2468243 : Blo 1644021 2468243 := bstep (se 1 (by rfl) ⟨1851182, by rfl⟩ : syracuseStep 2468243 = 3702365) B3702365
theorem B2468273 : Blo 1644021 2468273 := bstep (se 2 (by rfl) ⟨925602, by rfl⟩ : syracuseStep 2468273 = 1851205) B1851205
theorem B2501057 : Blo 1644021 2501057 := bstep (se 2 (by rfl) ⟨937896, by rfl⟩ : syracuseStep 2501057 = 1875793) B1875793
theorem B2468291 : Blo 1644021 2468291 := bstep (se 1 (by rfl) ⟨1851218, by rfl⟩ : syracuseStep 2468291 = 3702437) B3702437
theorem B8890829 : Blo 1644021 8890829 := bstep (se 3 (by rfl) ⟨1667030, by rfl⟩ : syracuseStep 8890829 = 3334061) B3334061
theorem B2468321 : Blo 1644021 2468321 := bstep (se 2 (by rfl) ⟨925620, by rfl⟩ : syracuseStep 2468321 = 1851241) B1851241
theorem B3123697 : Blo 1644021 3123697 := bstep (se 2 (by rfl) ⟨1171386, by rfl⟩ : syracuseStep 3123697 = 2342773) B2342773
theorem B2468339 : Blo 1644021 2468339 := bstep (se 1 (by rfl) ⟨1851254, by rfl⟩ : syracuseStep 2468339 = 3702509) B3702509
theorem B2468369 : Blo 1644021 2468369 := bstep (se 2 (by rfl) ⟨925638, by rfl⟩ : syracuseStep 2468369 = 1851277) B1851277
theorem B2468387 : Blo 1644021 2468387 := bstep (se 1 (by rfl) ⟨1851290, by rfl⟩ : syracuseStep 2468387 = 3702581) B3702581
theorem B2468417 : Blo 1644021 2468417 := bstep (se 2 (by rfl) ⟨925656, by rfl⟩ : syracuseStep 2468417 = 1851313) B1851313
theorem B2468435 : Blo 1644021 2468435 := bstep (se 1 (by rfl) ⟨1851326, by rfl⟩ : syracuseStep 2468435 = 3702653) B3702653
theorem B2468465 : Blo 1644021 2468465 := bstep (se 2 (by rfl) ⟨925674, by rfl⟩ : syracuseStep 2468465 = 1851349) B1851349
theorem B2468483 : Blo 1644021 2468483 := bstep (se 1 (by rfl) ⟨1851362, by rfl⟩ : syracuseStep 2468483 = 3702725) B3702725
theorem B2468513 : Blo 1644021 2468513 := bstep (se 2 (by rfl) ⟨925692, by rfl⟩ : syracuseStep 2468513 = 1851385) B1851385
theorem B2468531 : Blo 1644021 2468531 := bstep (se 1 (by rfl) ⟨1851398, by rfl⟩ : syracuseStep 2468531 = 3702797) B3702797
theorem B2468561 : Blo 1644021 2468561 := bstep (se 2 (by rfl) ⟨925710, by rfl⟩ : syracuseStep 2468561 = 1851421) B1851421
theorem B2468579 : Blo 1644021 2468579 := bstep (se 1 (by rfl) ⟨1851434, by rfl⟩ : syracuseStep 2468579 = 3702869) B3702869
theorem B2468609 : Blo 1644021 2468609 := bstep (se 2 (by rfl) ⟨925728, by rfl⟩ : syracuseStep 2468609 = 1851457) B1851457
theorem B2468627 : Blo 1644021 2468627 := bstep (se 1 (by rfl) ⟨1851470, by rfl⟩ : syracuseStep 2468627 = 3702941) B3702941
theorem B2468657 : Blo 1644021 2468657 := bstep (se 2 (by rfl) ⟨925746, by rfl⟩ : syracuseStep 2468657 = 1851493) B1851493
theorem B2468675 : Blo 1644021 2468675 := bstep (se 1 (by rfl) ⟨1851506, by rfl⟩ : syracuseStep 2468675 = 3703013) B3703013
theorem B5548877 : Blo 1644021 5548877 := bstep (se 3 (by rfl) ⟨1040414, by rfl⟩ : syracuseStep 5548877 = 2080829) B2080829
theorem B2468705 : Blo 1644021 2468705 := bstep (se 2 (by rfl) ⟨925764, by rfl⟩ : syracuseStep 2468705 = 1851529) B1851529
theorem B2501489 : Blo 1644021 2501489 := bstep (se 2 (by rfl) ⟨938058, by rfl⟩ : syracuseStep 2501489 = 1876117) B1876117
theorem B2468723 : Blo 1644021 2468723 := bstep (se 1 (by rfl) ⟨1851542, by rfl⟩ : syracuseStep 2468723 = 3703085) B3703085
theorem B5548931 : Blo 1644021 5548931 := bstep (se 1 (by rfl) ⟨4161698, by rfl⟩ : syracuseStep 5548931 = 8323397) B8323397
theorem B4746115 : Blo 1644021 4746115 := bstep (se 1 (by rfl) ⟨3559586, by rfl⟩ : syracuseStep 4746115 = 7119173) B7119173
theorem B2501507 : Blo 1644021 2501507 := bstep (se 1 (by rfl) ⟨1876130, by rfl⟩ : syracuseStep 2501507 = 3752261) B3752261
theorem B3124099 : Blo 1644021 3124099 := bstep (se 1 (by rfl) ⟨2343074, by rfl⟩ : syracuseStep 3124099 = 4686149) B4686149
theorem B2468753 : Blo 1644021 2468753 := bstep (se 2 (by rfl) ⟨925782, by rfl⟩ : syracuseStep 2468753 = 1851565) B1851565
theorem B2468771 : Blo 1644021 2468771 := bstep (se 1 (by rfl) ⟨1851578, by rfl⟩ : syracuseStep 2468771 = 3703157) B3703157
theorem B3124145 : Blo 1644021 3124145 := bstep (se 2 (by rfl) ⟨1171554, by rfl⟩ : syracuseStep 3124145 = 2343109) B2343109
theorem B2468801 : Blo 1644021 2468801 := bstep (se 2 (by rfl) ⟨925800, by rfl⟩ : syracuseStep 2468801 = 1851601) B1851601
theorem B2468819 : Blo 1644021 2468819 := bstep (se 1 (by rfl) ⟨1851614, by rfl⟩ : syracuseStep 2468819 = 3703229) B3703229
theorem B2468849 : Blo 1644021 2468849 := bstep (se 2 (by rfl) ⟨925818, by rfl⟩ : syracuseStep 2468849 = 1851637) B1851637
theorem B2468867 : Blo 1644021 2468867 := bstep (se 1 (by rfl) ⟨1851650, by rfl⟩ : syracuseStep 2468867 = 3703301) B3703301
theorem B14052365 : Blo 1644021 14052365 := bstep (se 3 (by rfl) ⟨2634818, by rfl⟩ : syracuseStep 14052365 = 5269637) B5269637
theorem B2468897 : Blo 1644021 2468897 := bstep (se 2 (by rfl) ⟨925836, by rfl⟩ : syracuseStep 2468897 = 1851673) B1851673
theorem B2468915 : Blo 1644021 2468915 := bstep (se 1 (by rfl) ⟨1851686, by rfl⟩ : syracuseStep 2468915 = 3703373) B3703373
theorem B2468945 : Blo 1644021 2468945 := bstep (se 2 (by rfl) ⟨925854, by rfl⟩ : syracuseStep 2468945 = 1851709) B1851709
theorem B2468963 : Blo 1644021 2468963 := bstep (se 1 (by rfl) ⟨1851722, by rfl⟩ : syracuseStep 2468963 = 3703445) B3703445
theorem B45616241 : Blo 1644021 45616241 := bstep (se 2 (by rfl) ⟨17106090, by rfl⟩ : syracuseStep 45616241 = 34212181) B34212181
theorem B2468993 : Blo 1644021 2468993 := bstep (se 2 (by rfl) ⟨925872, by rfl⟩ : syracuseStep 2468993 = 1851745) B1851745
theorem B2641027 : Blo 1644021 2641027 := bstep (se 1 (by rfl) ⟨1980770, by rfl⟩ : syracuseStep 2641027 = 3961541) B3961541
theorem B5549201 : Blo 1644021 5549201 := bstep (se 2 (by rfl) ⟨2080950, by rfl⟩ : syracuseStep 5549201 = 4161901) B4161901
theorem B2469011 : Blo 1644021 2469011 := bstep (se 1 (by rfl) ⟨1851758, by rfl⟩ : syracuseStep 2469011 = 3703517) B3703517
theorem B4164817 : Blo 1644021 4164817 := bstep (se 2 (by rfl) ⟨1561806, by rfl⟩ : syracuseStep 4164817 = 3123613) B3123613
theorem B3124433 : Blo 1644021 3124433 := bstep (se 2 (by rfl) ⟨1171662, by rfl⟩ : syracuseStep 3124433 = 2343325) B2343325
theorem B14241221 : Blo 1644021 14241221 := bstep (se 4 (by rfl) ⟨1335114, by rfl⟩ : syracuseStep 14241221 = 2670229) B2670229
theorem B7499213 : Blo 1644021 7499213 := bstep (se 3 (by rfl) ⟨1406102, by rfl⟩ : syracuseStep 7499213 = 2812205) B2812205
theorem B4165091 : Blo 1644021 4165091 := bstep (se 1 (by rfl) ⟨3123818, by rfl⟩ : syracuseStep 4165091 = 6247637) B6247637
theorem B5271149 : Blo 1644021 5271149 := bstep (se 3 (by rfl) ⟨988340, by rfl⟩ : syracuseStep 5271149 = 1976681) B1976681
theorem B11857549 : Blo 1644021 11857549 := bstep (se 3 (by rfl) ⟨2223290, by rfl⟩ : syracuseStep 11857549 = 4446581) B4446581
theorem B5000849 : Blo 1644021 5000849 := bstep (se 2 (by rfl) ⟨1875318, by rfl⟩ : syracuseStep 5000849 = 3750637) B3750637
theorem B1756819 : Blo 1644021 1756819 := bstep (se 1 (by rfl) ⟨1317614, by rfl⟩ : syracuseStep 1756819 = 2635229) B2635229
theorem B4165283 : Blo 1644021 4165283 := bstep (se 1 (by rfl) ⟨3123962, by rfl⟩ : syracuseStep 4165283 = 6247925) B6247925
theorem B5549741 : Blo 1644021 5549741 := bstep (se 3 (by rfl) ⟨1040576, by rfl⟩ : syracuseStep 5549741 = 2081153) B2081153
theorem B5549795 : Blo 1644021 5549795 := bstep (se 1 (by rfl) ⟨4162346, by rfl⟩ : syracuseStep 5549795 = 8324693) B8324693
theorem B2633473 : Blo 1644021 2633473 := bstep (se 2 (by rfl) ⟨987552, by rfl⟩ : syracuseStep 2633473 = 1975105) B1975105
theorem B6246179 : Blo 1644021 6246179 := bstep (se 1 (by rfl) ⟨4684634, by rfl⟩ : syracuseStep 6246179 = 9369269) B9369269
theorem B8326961 : Blo 1644021 8326961 := bstep (se 2 (by rfl) ⟨3122610, by rfl⟩ : syracuseStep 8326961 = 6245221) B6245221
theorem B6246193 : Blo 1644021 6246193 := bstep (se 2 (by rfl) ⟨2342322, by rfl⟩ : syracuseStep 6246193 = 4684645) B4684645
theorem B35589941 : Blo 1644021 35589941 := bstep (se 5 (by rfl) ⟨1668278, by rfl⟩ : syracuseStep 35589941 = 3336557) B3336557
theorem B20279267 : Blo 1644021 20279267 := bstep (se 1 (by rfl) ⟨15209450, by rfl⟩ : syracuseStep 20279267 = 30418901) B30418901
theorem B5550065 : Blo 1644021 5550065 := bstep (se 2 (by rfl) ⟨2081274, by rfl⟩ : syracuseStep 5550065 = 4162549) B4162549
theorem B2633729 : Blo 1644021 2633729 := bstep (se 2 (by rfl) ⟨987648, by rfl⟩ : syracuseStep 2633729 = 1975297) B1975297
theorem B1667075 : Blo 1644021 1667075 := bstep (se 1 (by rfl) ⟨1250306, by rfl⟩ : syracuseStep 1667075 = 2500613) B2500613
theorem B1757251 : Blo 1644021 1757251 := bstep (se 1 (by rfl) ⟨1317938, by rfl⟩ : syracuseStep 1757251 = 2635877) B2635877
theorem B7024781 : Blo 1644021 7024781 := bstep (se 3 (by rfl) ⟨1317146, by rfl⟩ : syracuseStep 7024781 = 2634293) B2634293
theorem B4681901 : Blo 1644021 4681901 := bstep (se 3 (by rfl) ⟨877856, by rfl⟩ : syracuseStep 4681901 = 1755713) B1755713
theorem B7909645 : Blo 1644021 7909645 := bstep (se 3 (by rfl) ⟨1483058, by rfl⟩ : syracuseStep 7909645 = 2966117) B2966117
theorem B4682083 : Blo 1644021 4682083 := bstep (se 1 (by rfl) ⟨3511562, by rfl⟩ : syracuseStep 4682083 = 7023125) B7023125
theorem B3699089 : Blo 1644021 3699089 := bstep (se 2 (by rfl) ⟨1387158, by rfl⟩ : syracuseStep 3699089 = 2774317) B2774317
theorem B3699107 : Blo 1644021 3699107 := bstep (se 1 (by rfl) ⟨2774330, by rfl⟩ : syracuseStep 3699107 = 5548661) B5548661
theorem B2814401 : Blo 1644021 2814401 := bstep (se 2 (by rfl) ⟨1055400, by rfl⟩ : syracuseStep 2814401 = 2110801) B2110801
theorem B7025123 : Blo 1644021 7025123 := bstep (se 1 (by rfl) ⟨5268842, by rfl⟩ : syracuseStep 7025123 = 10537685) B10537685
theorem B5001713 : Blo 1644021 5001713 := bstep (se 2 (by rfl) ⟨1875642, by rfl⟩ : syracuseStep 5001713 = 3751285) B3751285
theorem B5550605 : Blo 1644021 5550605 := bstep (se 3 (by rfl) ⟨1040738, by rfl⟩ : syracuseStep 5550605 = 2081477) B2081477
theorem B5550659 : Blo 1644021 5550659 := bstep (se 1 (by rfl) ⟨4162994, by rfl⟩ : syracuseStep 5550659 = 8325989) B8325989
theorem B4166225 : Blo 1644021 4166225 := bstep (se 2 (by rfl) ⟨1562334, by rfl⟩ : syracuseStep 4166225 = 3124669) B3124669
theorem B28881521 : Blo 1644021 28881521 := bstep (se 2 (by rfl) ⟨10830570, by rfl⟩ : syracuseStep 28881521 = 21661141) B21661141
theorem B4166275 : Blo 1644021 4166275 := bstep (se 1 (by rfl) ⟨3124706, by rfl⟩ : syracuseStep 4166275 = 6249413) B6249413
theorem B3699377 : Blo 1644021 3699377 := bstep (se 2 (by rfl) ⟨1387266, by rfl⟩ : syracuseStep 3699377 = 2774533) B2774533
theorem B3699395 : Blo 1644021 3699395 := bstep (se 1 (by rfl) ⟨2774546, by rfl⟩ : syracuseStep 3699395 = 5549093) B5549093
theorem B5927651 : Blo 1644021 5927651 := bstep (se 1 (by rfl) ⟨4445738, by rfl⟩ : syracuseStep 5927651 = 8891477) B8891477
theorem B3044081 : Blo 1644021 3044081 := bstep (se 2 (by rfl) ⟨1141530, by rfl⟩ : syracuseStep 3044081 = 2283061) B2283061
theorem B21361421 : Blo 1644021 21361421 := bstep (se 3 (by rfl) ⟨4005266, by rfl⟩ : syracuseStep 21361421 = 8010533) B8010533
theorem B4166417 : Blo 1644021 4166417 := bstep (se 2 (by rfl) ⟨1562406, by rfl⟩ : syracuseStep 4166417 = 3124813) B3124813
theorem B4682573 : Blo 1644021 4682573 := bstep (se 3 (by rfl) ⟨877982, by rfl⟩ : syracuseStep 4682573 = 1755965) B1755965
theorem B5550929 : Blo 1644021 5550929 := bstep (se 2 (by rfl) ⟨2081598, by rfl⟩ : syracuseStep 5550929 = 4163197) B4163197
theorem B3699665 : Blo 1644021 3699665 := bstep (se 2 (by rfl) ⟨1387374, by rfl⟩ : syracuseStep 3699665 = 2774749) B2774749
theorem B3699683 : Blo 1644021 3699683 := bstep (se 1 (by rfl) ⟨2774762, by rfl⟩ : syracuseStep 3699683 = 5549525) B5549525
theorem B12489713 : Blo 1644021 12489713 := bstep (se 2 (by rfl) ⟨4683642, by rfl⟩ : syracuseStep 12489713 = 9367285) B9367285
theorem B9368561 : Blo 1644021 9368561 := bstep (se 2 (by rfl) ⟨3513210, by rfl⟩ : syracuseStep 9368561 = 7026421) B7026421
theorem B9999409 : Blo 1644021 9999409 := bstep (se 2 (by rfl) ⟨3749778, by rfl⟩ : syracuseStep 9999409 = 7499557) B7499557
theorem B4813933 : Blo 1644021 4813933 := bstep (se 3 (by rfl) ⟨902612, by rfl⟩ : syracuseStep 4813933 = 1805225) B1805225
theorem B10540145 : Blo 1644021 10540145 := bstep (se 2 (by rfl) ⟨3952554, by rfl⟩ : syracuseStep 10540145 = 7905109) B7905109
theorem B5272739 : Blo 1644021 5272739 := bstep (se 1 (by rfl) ⟨3954554, by rfl⟩ : syracuseStep 5272739 = 7909109) B7909109
theorem B22508741 : Blo 1644021 22508741 := bstep (se 4 (by rfl) ⟨2110194, by rfl⟩ : syracuseStep 22508741 = 4220389) B4220389
theorem B8328419 : Blo 1644021 8328419 := bstep (se 1 (by rfl) ⟨6246314, by rfl⟩ : syracuseStep 8328419 = 12492629) B12492629
theorem B6247651 : Blo 1644021 6247651 := bstep (se 1 (by rfl) ⟨4685738, by rfl⟩ : syracuseStep 6247651 = 9371477) B9371477
theorem B3953891 : Blo 1644021 3953891 := bstep (se 1 (by rfl) ⟨2965418, by rfl⟩ : syracuseStep 3953891 = 5930837) B5930837
theorem B3699953 : Blo 1644021 3699953 := bstep (se 2 (by rfl) ⟨1387482, by rfl⟩ : syracuseStep 3699953 = 2774965) B2774965
theorem B3699971 : Blo 1644021 3699971 := bstep (se 1 (by rfl) ⟨2774978, by rfl⟩ : syracuseStep 3699971 = 5549957) B5549957
theorem B11253005 : Blo 1644021 11253005 := bstep (se 3 (by rfl) ⟨2109938, by rfl⟩ : syracuseStep 11253005 = 4219877) B4219877
theorem B15807757 : Blo 1644021 15807757 := bstep (se 3 (by rfl) ⟨2963954, by rfl⟩ : syracuseStep 15807757 = 5927909) B5927909
theorem B2774371 : Blo 1644021 2774371 := bstep (se 1 (by rfl) ⟨2080778, by rfl⟩ : syracuseStep 2774371 = 4161557) B4161557
theorem B14054755 : Blo 1644021 14054755 := bstep (se 1 (by rfl) ⟨10541066, by rfl⟩ : syracuseStep 14054755 = 21082133) B21082133
theorem B2004323 : Blo 1644021 2004323 := bstep (se 1 (by rfl) ⟨1503242, by rfl⟩ : syracuseStep 2004323 = 3006485) B3006485
theorem B5551469 : Blo 1644021 5551469 := bstep (se 3 (by rfl) ⟨1040900, by rfl⟩ : syracuseStep 5551469 = 2081801) B2081801
theorem B2635139 : Blo 1644021 2635139 := bstep (se 1 (by rfl) ⟨1976354, by rfl⟩ : syracuseStep 2635139 = 3952709) B3952709
theorem B5551523 : Blo 1644021 5551523 := bstep (se 1 (by rfl) ⟨4163642, by rfl⟩ : syracuseStep 5551523 = 8327285) B8327285
theorem B2774513 : Blo 1644021 2774513 := bstep (se 2 (by rfl) ⟨1040442, by rfl⟩ : syracuseStep 2774513 = 2080885) B2080885
theorem B1644035 : Blo 1644021 1644035 := bstep (se 1 (by rfl) ⟨1233026, by rfl⟩ : syracuseStep 1644035 = 2466053) B2466053
theorem B3700241 : Blo 1644021 3700241 := bstep (se 2 (by rfl) ⟨1387590, by rfl⟩ : syracuseStep 3700241 = 2775181) B2775181
theorem B1644051 : Blo 1644021 1644051 := bstep (se 1 (by rfl) ⟨1233038, by rfl⟩ : syracuseStep 1644051 = 2466077) B2466077
theorem B1644067 : Blo 1644021 1644067 := bstep (se 1 (by rfl) ⟨1233050, by rfl⟩ : syracuseStep 1644067 = 2466101) B2466101
theorem B3700259 : Blo 1644021 3700259 := bstep (se 1 (by rfl) ⟨2775194, by rfl⟩ : syracuseStep 3700259 = 5550389) B5550389
theorem B1644083 : Blo 1644021 1644083 := bstep (se 1 (by rfl) ⟨1233062, by rfl⟩ : syracuseStep 1644083 = 2466125) B2466125
theorem B1644099 : Blo 1644021 1644099 := bstep (se 1 (by rfl) ⟨1233074, by rfl⟩ : syracuseStep 1644099 = 2466149) B2466149
theorem B1644115 : Blo 1644021 1644115 := bstep (se 1 (by rfl) ⟨1233086, by rfl⟩ : syracuseStep 1644115 = 2466173) B2466173
theorem B1644131 : Blo 1644021 1644131 := bstep (se 1 (by rfl) ⟨1233098, by rfl⟩ : syracuseStep 1644131 = 2466197) B2466197
theorem B2774641 : Blo 1644021 2774641 := bstep (se 2 (by rfl) ⟨1040490, by rfl⟩ : syracuseStep 2774641 = 2080981) B2080981
theorem B1644147 : Blo 1644021 1644147 := bstep (se 1 (by rfl) ⟨1233110, by rfl⟩ : syracuseStep 1644147 = 2466221) B2466221
theorem B1644163 : Blo 1644021 1644163 := bstep (se 1 (by rfl) ⟨1233122, by rfl⟩ : syracuseStep 1644163 = 2466245) B2466245
theorem B1644179 : Blo 1644021 1644179 := bstep (se 1 (by rfl) ⟨1233134, by rfl⟩ : syracuseStep 1644179 = 2466269) B2466269
theorem B2774675 : Blo 1644021 2774675 := bstep (se 1 (by rfl) ⟨2081006, by rfl⟩ : syracuseStep 2774675 = 4162013) B4162013
theorem B1644195 : Blo 1644021 1644195 := bstep (se 1 (by rfl) ⟨1233146, by rfl⟩ : syracuseStep 1644195 = 2466293) B2466293
theorem B5551793 : Blo 1644021 5551793 := bstep (se 2 (by rfl) ⟨2081922, by rfl⟩ : syracuseStep 5551793 = 4163845) B4163845
theorem B1644211 : Blo 1644021 1644211 := bstep (se 1 (by rfl) ⟨1233158, by rfl⟩ : syracuseStep 1644211 = 2466317) B2466317
theorem B1644227 : Blo 1644021 1644227 := bstep (se 1 (by rfl) ⟨1233170, by rfl⟩ : syracuseStep 1644227 = 2466341) B2466341
theorem B4445891 : Blo 1644021 4445891 := bstep (se 1 (by rfl) ⟨3334418, by rfl⟩ : syracuseStep 4445891 = 6668837) B6668837
theorem B1644243 : Blo 1644021 1644243 := bstep (se 1 (by rfl) ⟨1233182, by rfl⟩ : syracuseStep 1644243 = 2466365) B2466365
theorem B1644259 : Blo 1644021 1644259 := bstep (se 1 (by rfl) ⟨1233194, by rfl⟩ : syracuseStep 1644259 = 2466389) B2466389
theorem B1644275 : Blo 1644021 1644275 := bstep (se 1 (by rfl) ⟨1233206, by rfl⟩ : syracuseStep 1644275 = 2466413) B2466413
theorem B1644291 : Blo 1644021 1644291 := bstep (se 1 (by rfl) ⟨1233218, by rfl⟩ : syracuseStep 1644291 = 2466437) B2466437
theorem B1644307 : Blo 1644021 1644307 := bstep (se 1 (by rfl) ⟨1233230, by rfl⟩ : syracuseStep 1644307 = 2466461) B2466461
theorem B2774803 : Blo 1644021 2774803 := bstep (se 1 (by rfl) ⟨2081102, by rfl⟩ : syracuseStep 2774803 = 4162205) B4162205
theorem B1644323 : Blo 1644021 1644323 := bstep (se 1 (by rfl) ⟨1233242, by rfl⟩ : syracuseStep 1644323 = 2466485) B2466485
theorem B3700529 : Blo 1644021 3700529 := bstep (se 2 (by rfl) ⟨1387698, by rfl⟩ : syracuseStep 3700529 = 2775397) B2775397
theorem B1644339 : Blo 1644021 1644339 := bstep (se 1 (by rfl) ⟨1233254, by rfl⟩ : syracuseStep 1644339 = 2466509) B2466509
theorem B1644355 : Blo 1644021 1644355 := bstep (se 1 (by rfl) ⟨1233266, by rfl⟩ : syracuseStep 1644355 = 2466533) B2466533
theorem B3700547 : Blo 1644021 3700547 := bstep (se 1 (by rfl) ⟨2775410, by rfl⟩ : syracuseStep 3700547 = 5550821) B5550821
theorem B1644371 : Blo 1644021 1644371 := bstep (se 1 (by rfl) ⟨1233278, by rfl⟩ : syracuseStep 1644371 = 2466557) B2466557
theorem B1644387 : Blo 1644021 1644387 := bstep (se 1 (by rfl) ⟨1233290, by rfl⟩ : syracuseStep 1644387 = 2466581) B2466581
theorem B1644403 : Blo 1644021 1644403 := bstep (se 1 (by rfl) ⟨1233302, by rfl⟩ : syracuseStep 1644403 = 2466605) B2466605
theorem B1644419 : Blo 1644021 1644419 := bstep (se 1 (by rfl) ⟨1233314, by rfl⟩ : syracuseStep 1644419 = 2466629) B2466629
theorem B1644435 : Blo 1644021 1644435 := bstep (se 1 (by rfl) ⟨1233326, by rfl⟩ : syracuseStep 1644435 = 2466653) B2466653
theorem B2774945 : Blo 1644021 2774945 := bstep (se 2 (by rfl) ⟨1040604, by rfl⟩ : syracuseStep 2774945 = 2081209) B2081209
theorem B1644451 : Blo 1644021 1644451 := bstep (se 1 (by rfl) ⟨1233338, by rfl⟩ : syracuseStep 1644451 = 2466677) B2466677
theorem B1644467 : Blo 1644021 1644467 := bstep (se 1 (by rfl) ⟨1233350, by rfl⟩ : syracuseStep 1644467 = 2466701) B2466701
theorem B1644483 : Blo 1644021 1644483 := bstep (se 1 (by rfl) ⟨1233362, by rfl⟩ : syracuseStep 1644483 = 2466725) B2466725
theorem B1644499 : Blo 1644021 1644499 := bstep (se 1 (by rfl) ⟨1233374, by rfl⟩ : syracuseStep 1644499 = 2466749) B2466749
theorem B1644515 : Blo 1644021 1644515 := bstep (se 1 (by rfl) ⟨1233386, by rfl⟩ : syracuseStep 1644515 = 2466773) B2466773
theorem B4683757 : Blo 1644021 4683757 := bstep (se 3 (by rfl) ⟨878204, by rfl⟩ : syracuseStep 4683757 = 1756409) B1756409
theorem B1644531 : Blo 1644021 1644531 := bstep (se 1 (by rfl) ⟨1233398, by rfl⟩ : syracuseStep 1644531 = 2466797) B2466797
theorem B1644547 : Blo 1644021 1644547 := bstep (se 1 (by rfl) ⟨1233410, by rfl⟩ : syracuseStep 1644547 = 2466821) B2466821
theorem B8329229 : Blo 1644021 8329229 := bstep (se 3 (by rfl) ⟨1561730, by rfl⟩ : syracuseStep 8329229 = 3123461) B3123461
theorem B3749905 : Blo 1644021 3749905 := bstep (se 2 (by rfl) ⟨1406214, by rfl⟩ : syracuseStep 3749905 = 2812429) B2812429
theorem B1644563 : Blo 1644021 1644563 := bstep (se 1 (by rfl) ⟨1233422, by rfl⟩ : syracuseStep 1644563 = 2466845) B2466845
theorem B2775073 : Blo 1644021 2775073 := bstep (se 2 (by rfl) ⟨1040652, by rfl⟩ : syracuseStep 2775073 = 2081305) B2081305
theorem B1644579 : Blo 1644021 1644579 := bstep (se 1 (by rfl) ⟨1233434, by rfl⟩ : syracuseStep 1644579 = 2466869) B2466869
theorem B1644595 : Blo 1644021 1644595 := bstep (se 1 (by rfl) ⟨1233446, by rfl⟩ : syracuseStep 1644595 = 2466893) B2466893
theorem B2775107 : Blo 1644021 2775107 := bstep (se 1 (by rfl) ⟨2081330, by rfl⟩ : syracuseStep 2775107 = 4162661) B4162661
theorem B1644611 : Blo 1644021 1644611 := bstep (se 1 (by rfl) ⟨1233458, by rfl⟩ : syracuseStep 1644611 = 2466917) B2466917
theorem B3700817 : Blo 1644021 3700817 := bstep (se 2 (by rfl) ⟨1387806, by rfl⟩ : syracuseStep 3700817 = 2775613) B2775613
theorem B1644627 : Blo 1644021 1644627 := bstep (se 1 (by rfl) ⟨1233470, by rfl⟩ : syracuseStep 1644627 = 2466941) B2466941
theorem B1644643 : Blo 1644021 1644643 := bstep (se 1 (by rfl) ⟨1233482, by rfl⟩ : syracuseStep 1644643 = 2466965) B2466965
theorem B3700835 : Blo 1644021 3700835 := bstep (se 1 (by rfl) ⟨2775626, by rfl⟩ : syracuseStep 3700835 = 5551253) B5551253
theorem B1644659 : Blo 1644021 1644659 := bstep (se 1 (by rfl) ⟨1233494, by rfl⟩ : syracuseStep 1644659 = 2466989) B2466989
theorem B1644675 : Blo 1644021 1644675 := bstep (se 1 (by rfl) ⟨1233506, by rfl⟩ : syracuseStep 1644675 = 2467013) B2467013
theorem B1644691 : Blo 1644021 1644691 := bstep (se 1 (by rfl) ⟨1233518, by rfl⟩ : syracuseStep 1644691 = 2467037) B2467037
theorem B1644707 : Blo 1644021 1644707 := bstep (se 1 (by rfl) ⟨1233530, by rfl⟩ : syracuseStep 1644707 = 2467061) B2467061
theorem B1644723 : Blo 1644021 1644723 := bstep (se 1 (by rfl) ⟨1233542, by rfl⟩ : syracuseStep 1644723 = 2467085) B2467085
theorem B2775235 : Blo 1644021 2775235 := bstep (se 1 (by rfl) ⟨2081426, by rfl⟩ : syracuseStep 2775235 = 4162853) B4162853
theorem B1644739 : Blo 1644021 1644739 := bstep (se 1 (by rfl) ⟨1233554, by rfl⟩ : syracuseStep 1644739 = 2467109) B2467109
theorem B5552333 : Blo 1644021 5552333 := bstep (se 3 (by rfl) ⟨1041062, by rfl⟩ : syracuseStep 5552333 = 2082125) B2082125
theorem B2635985 : Blo 1644021 2635985 := bstep (se 2 (by rfl) ⟨988494, by rfl⟩ : syracuseStep 2635985 = 1976989) B1976989
theorem B1644755 : Blo 1644021 1644755 := bstep (se 1 (by rfl) ⟨1233566, by rfl⟩ : syracuseStep 1644755 = 2467133) B2467133
theorem B1644771 : Blo 1644021 1644771 := bstep (se 1 (by rfl) ⟨1233578, by rfl⟩ : syracuseStep 1644771 = 2467157) B2467157
theorem B1644787 : Blo 1644021 1644787 := bstep (se 1 (by rfl) ⟨1233590, by rfl⟩ : syracuseStep 1644787 = 2467181) B2467181
theorem B1849603 : Blo 1644021 1849603 := bstep (se 1 (by rfl) ⟨1387202, by rfl⟩ : syracuseStep 1849603 = 2774405) B2774405
theorem B1644803 : Blo 1644021 1644803 := bstep (se 1 (by rfl) ⟨1233602, by rfl⟩ : syracuseStep 1644803 = 2467205) B2467205
theorem B5552387 : Blo 1644021 5552387 := bstep (se 1 (by rfl) ⟨4164290, by rfl⟩ : syracuseStep 5552387 = 8328581) B8328581
theorem B1644819 : Blo 1644021 1644819 := bstep (se 1 (by rfl) ⟨1233614, by rfl⟩ : syracuseStep 1644819 = 2467229) B2467229
theorem B1644835 : Blo 1644021 1644835 := bstep (se 1 (by rfl) ⟨1233626, by rfl⟩ : syracuseStep 1644835 = 2467253) B2467253
theorem B1644851 : Blo 1644021 1644851 := bstep (se 1 (by rfl) ⟨1233638, by rfl⟩ : syracuseStep 1644851 = 2467277) B2467277
theorem B1644867 : Blo 1644021 1644867 := bstep (se 1 (by rfl) ⟨1233650, by rfl⟩ : syracuseStep 1644867 = 2467301) B2467301
theorem B2775377 : Blo 1644021 2775377 := bstep (se 2 (by rfl) ⟨1040766, by rfl⟩ : syracuseStep 2775377 = 2081533) B2081533
theorem B1644883 : Blo 1644021 1644883 := bstep (se 1 (by rfl) ⟨1233662, by rfl⟩ : syracuseStep 1644883 = 2467325) B2467325
theorem B1644899 : Blo 1644021 1644899 := bstep (se 1 (by rfl) ⟨1233674, by rfl⟩ : syracuseStep 1644899 = 2467349) B2467349
theorem B3701105 : Blo 1644021 3701105 := bstep (se 2 (by rfl) ⟨1387914, by rfl⟩ : syracuseStep 3701105 = 2775829) B2775829
theorem B1644915 : Blo 1644021 1644915 := bstep (se 1 (by rfl) ⟨1233686, by rfl⟩ : syracuseStep 1644915 = 2467373) B2467373
theorem B1644931 : Blo 1644021 1644931 := bstep (se 1 (by rfl) ⟨1233698, by rfl⟩ : syracuseStep 1644931 = 2467397) B2467397
theorem B3701123 : Blo 1644021 3701123 := bstep (se 1 (by rfl) ⟨2775842, by rfl⟩ : syracuseStep 3701123 = 5551685) B5551685
theorem B1849747 : Blo 1644021 1849747 := bstep (se 1 (by rfl) ⟨1387310, by rfl⟩ : syracuseStep 1849747 = 2774621) B2774621
theorem B1644947 : Blo 1644021 1644947 := bstep (se 1 (by rfl) ⟨1233710, by rfl⟩ : syracuseStep 1644947 = 2467421) B2467421
theorem B1644963 : Blo 1644021 1644963 := bstep (se 1 (by rfl) ⟨1233722, by rfl⟩ : syracuseStep 1644963 = 2467445) B2467445
theorem B9370019 : Blo 1644021 9370019 := bstep (se 1 (by rfl) ⟨7027514, by rfl⟩ : syracuseStep 9370019 = 14055029) B14055029
theorem B3561905 : Blo 1644021 3561905 := bstep (se 2 (by rfl) ⟨1335714, by rfl⟩ : syracuseStep 3561905 = 2671429) B2671429
theorem B1644979 : Blo 1644021 1644979 := bstep (se 1 (by rfl) ⟨1233734, by rfl⟩ : syracuseStep 1644979 = 2467469) B2467469
theorem B2341315 : Blo 1644021 2341315 := bstep (se 1 (by rfl) ⟨1755986, by rfl⟩ : syracuseStep 2341315 = 3511973) B3511973
theorem B1644995 : Blo 1644021 1644995 := bstep (se 1 (by rfl) ⟨1233746, by rfl⟩ : syracuseStep 1644995 = 2467493) B2467493
theorem B2775505 : Blo 1644021 2775505 := bstep (se 2 (by rfl) ⟨1040814, by rfl⟩ : syracuseStep 2775505 = 2081629) B2081629
theorem B1645011 : Blo 1644021 1645011 := bstep (se 1 (by rfl) ⟨1233758, by rfl⟩ : syracuseStep 1645011 = 2467517) B2467517
theorem B1645027 : Blo 1644021 1645027 := bstep (se 1 (by rfl) ⟨1233770, by rfl⟩ : syracuseStep 1645027 = 2467541) B2467541
theorem B2775539 : Blo 1644021 2775539 := bstep (se 1 (by rfl) ⟨2081654, by rfl⟩ : syracuseStep 2775539 = 4163309) B4163309
theorem B1645043 : Blo 1644021 1645043 := bstep (se 1 (by rfl) ⟨1233782, by rfl⟩ : syracuseStep 1645043 = 2467565) B2467565
theorem B1645059 : Blo 1644021 1645059 := bstep (se 1 (by rfl) ⟨1233794, by rfl⟩ : syracuseStep 1645059 = 2467589) B2467589
theorem B5552657 : Blo 1644021 5552657 := bstep (se 2 (by rfl) ⟨2082246, by rfl⟩ : syracuseStep 5552657 = 4164493) B4164493
theorem B1645075 : Blo 1644021 1645075 := bstep (se 1 (by rfl) ⟨1233806, by rfl⟩ : syracuseStep 1645075 = 2467613) B2467613
theorem B1849891 : Blo 1644021 1849891 := bstep (se 1 (by rfl) ⟨1387418, by rfl⟩ : syracuseStep 1849891 = 2774837) B2774837
theorem B1645091 : Blo 1644021 1645091 := bstep (se 1 (by rfl) ⟨1233818, by rfl⟩ : syracuseStep 1645091 = 2467637) B2467637
theorem B1645107 : Blo 1644021 1645107 := bstep (se 1 (by rfl) ⟨1233830, by rfl⟩ : syracuseStep 1645107 = 2467661) B2467661
theorem B2964035 : Blo 1644021 2964035 := bstep (se 1 (by rfl) ⟨2223026, by rfl⟩ : syracuseStep 2964035 = 4446053) B4446053
theorem B1645123 : Blo 1644021 1645123 := bstep (se 1 (by rfl) ⟨1233842, by rfl⟩ : syracuseStep 1645123 = 2467685) B2467685
theorem B1645139 : Blo 1644021 1645139 := bstep (se 1 (by rfl) ⟨1233854, by rfl⟩ : syracuseStep 1645139 = 2467709) B2467709
theorem B1645155 : Blo 1644021 1645155 := bstep (se 1 (by rfl) ⟨1233866, by rfl⟩ : syracuseStep 1645155 = 2467733) B2467733
theorem B2775667 : Blo 1644021 2775667 := bstep (se 1 (by rfl) ⟨2081750, by rfl⟩ : syracuseStep 2775667 = 4163501) B4163501
theorem B1645171 : Blo 1644021 1645171 := bstep (se 1 (by rfl) ⟨1233878, by rfl⟩ : syracuseStep 1645171 = 2467757) B2467757
theorem B1645187 : Blo 1644021 1645187 := bstep (se 1 (by rfl) ⟨1233890, by rfl⟩ : syracuseStep 1645187 = 2467781) B2467781
theorem B13523597 : Blo 1644021 13523597 := bstep (se 3 (by rfl) ⟨2535674, by rfl⟩ : syracuseStep 13523597 = 5071349) B5071349
theorem B3701393 : Blo 1644021 3701393 := bstep (se 2 (by rfl) ⟨1388022, by rfl⟩ : syracuseStep 3701393 = 2776045) B2776045
theorem B1645203 : Blo 1644021 1645203 := bstep (se 1 (by rfl) ⟨1233902, by rfl⟩ : syracuseStep 1645203 = 2467805) B2467805
theorem B3750563 : Blo 1644021 3750563 := bstep (se 1 (by rfl) ⟨2812922, by rfl⟩ : syracuseStep 3750563 = 5625845) B5625845
theorem B3701411 : Blo 1644021 3701411 := bstep (se 1 (by rfl) ⟨2776058, by rfl⟩ : syracuseStep 3701411 = 5552117) B5552117
theorem B1645219 : Blo 1644021 1645219 := bstep (se 1 (by rfl) ⟨1233914, by rfl⟩ : syracuseStep 1645219 = 2467829) B2467829
theorem B1850035 : Blo 1644021 1850035 := bstep (se 1 (by rfl) ⟨1387526, by rfl⟩ : syracuseStep 1850035 = 2775053) B2775053
theorem B1645235 : Blo 1644021 1645235 := bstep (se 1 (by rfl) ⟨1233926, by rfl⟩ : syracuseStep 1645235 = 2467853) B2467853
theorem B1645251 : Blo 1644021 1645251 := bstep (se 1 (by rfl) ⟨1233938, by rfl⟩ : syracuseStep 1645251 = 2467877) B2467877
theorem B6011597 : Blo 1644021 6011597 := bstep (se 3 (by rfl) ⟨1127174, by rfl⟩ : syracuseStep 6011597 = 2254349) B2254349
theorem B2636497 : Blo 1644021 2636497 := bstep (se 2 (by rfl) ⟨988686, by rfl⟩ : syracuseStep 2636497 = 1977373) B1977373
theorem B1645267 : Blo 1644021 1645267 := bstep (se 1 (by rfl) ⟨1233950, by rfl⟩ : syracuseStep 1645267 = 2467901) B2467901
theorem B1645283 : Blo 1644021 1645283 := bstep (se 1 (by rfl) ⟨1233962, by rfl⟩ : syracuseStep 1645283 = 2467925) B2467925
theorem B1645299 : Blo 1644021 1645299 := bstep (se 1 (by rfl) ⟨1233974, by rfl⟩ : syracuseStep 1645299 = 2467949) B2467949
theorem B2775809 : Blo 1644021 2775809 := bstep (se 2 (by rfl) ⟨1040928, by rfl⟩ : syracuseStep 2775809 = 2081857) B2081857
theorem B1645315 : Blo 1644021 1645315 := bstep (se 1 (by rfl) ⟨1233986, by rfl⟩ : syracuseStep 1645315 = 2467973) B2467973
theorem B2341651 : Blo 1644021 2341651 := bstep (se 1 (by rfl) ⟨1756238, by rfl⟩ : syracuseStep 2341651 = 3512477) B3512477
theorem B1645331 : Blo 1644021 1645331 := bstep (se 1 (by rfl) ⟨1233998, by rfl⟩ : syracuseStep 1645331 = 2467997) B2467997
theorem B1645347 : Blo 1644021 1645347 := bstep (se 1 (by rfl) ⟨1234010, by rfl⟩ : syracuseStep 1645347 = 2468021) B2468021
theorem B1645363 : Blo 1644021 1645363 := bstep (se 1 (by rfl) ⟨1234022, by rfl⟩ : syracuseStep 1645363 = 2468045) B2468045
theorem B1850179 : Blo 1644021 1850179 := bstep (se 1 (by rfl) ⟨1387634, by rfl⟩ : syracuseStep 1850179 = 2775269) B2775269
theorem B1645379 : Blo 1644021 1645379 := bstep (se 1 (by rfl) ⟨1234034, by rfl⟩ : syracuseStep 1645379 = 2468069) B2468069
theorem B1645395 : Blo 1644021 1645395 := bstep (se 1 (by rfl) ⟨1234046, by rfl⟩ : syracuseStep 1645395 = 2468093) B2468093
theorem B1645411 : Blo 1644021 1645411 := bstep (se 1 (by rfl) ⟨1234058, by rfl⟩ : syracuseStep 1645411 = 2468117) B2468117
theorem B1645427 : Blo 1644021 1645427 := bstep (se 1 (by rfl) ⟨1234070, by rfl⟩ : syracuseStep 1645427 = 2468141) B2468141
theorem B2775937 : Blo 1644021 2775937 := bstep (se 2 (by rfl) ⟨1040976, by rfl⟩ : syracuseStep 2775937 = 2081953) B2081953
theorem B1645443 : Blo 1644021 1645443 := bstep (se 1 (by rfl) ⟨1234082, by rfl⟩ : syracuseStep 1645443 = 2468165) B2468165
theorem B22502285 : Blo 1644021 22502285 := bstep (se 3 (by rfl) ⟨4219178, by rfl⟩ : syracuseStep 22502285 = 8438357) B8438357
theorem B1645459 : Blo 1644021 1645459 := bstep (se 1 (by rfl) ⟨1234094, by rfl⟩ : syracuseStep 1645459 = 2468189) B2468189
theorem B2775971 : Blo 1644021 2775971 := bstep (se 1 (by rfl) ⟨2081978, by rfl⟩ : syracuseStep 2775971 = 4163957) B4163957
theorem B1645475 : Blo 1644021 1645475 := bstep (se 1 (by rfl) ⟨1234106, by rfl⟩ : syracuseStep 1645475 = 2468213) B2468213
theorem B3701681 : Blo 1644021 3701681 := bstep (se 2 (by rfl) ⟨1388130, by rfl⟩ : syracuseStep 3701681 = 2776261) B2776261
theorem B1645491 : Blo 1644021 1645491 := bstep (se 1 (by rfl) ⟨1234118, by rfl⟩ : syracuseStep 1645491 = 2468237) B2468237
theorem B21085109 : Blo 1644021 21085109 := bstep (se 5 (by rfl) ⟨988364, by rfl⟩ : syracuseStep 21085109 = 1976729) B1976729
theorem B3701699 : Blo 1644021 3701699 := bstep (se 1 (by rfl) ⟨2776274, by rfl⟩ : syracuseStep 3701699 = 5552549) B5552549
theorem B1645507 : Blo 1644021 1645507 := bstep (se 1 (by rfl) ⟨1234130, by rfl⟩ : syracuseStep 1645507 = 2468261) B2468261
theorem B10001357 : Blo 1644021 10001357 := bstep (se 3 (by rfl) ⟨1875254, by rfl⟩ : syracuseStep 10001357 = 3750509) B3750509
theorem B1850323 : Blo 1644021 1850323 := bstep (se 1 (by rfl) ⟨1387742, by rfl⟩ : syracuseStep 1850323 = 2775485) B2775485
theorem B1645523 : Blo 1644021 1645523 := bstep (se 1 (by rfl) ⟨1234142, by rfl⟩ : syracuseStep 1645523 = 2468285) B2468285
theorem B1645539 : Blo 1644021 1645539 := bstep (se 1 (by rfl) ⟨1234154, by rfl⟩ : syracuseStep 1645539 = 2468309) B2468309
theorem B1645555 : Blo 1644021 1645555 := bstep (se 1 (by rfl) ⟨1234166, by rfl⟩ : syracuseStep 1645555 = 2468333) B2468333
theorem B1645571 : Blo 1644021 1645571 := bstep (se 1 (by rfl) ⟨1234178, by rfl⟩ : syracuseStep 1645571 = 2468357) B2468357
theorem B4684817 : Blo 1644021 4684817 := bstep (se 2 (by rfl) ⟨1756806, by rfl⟩ : syracuseStep 4684817 = 3513613) B3513613
theorem B1645587 : Blo 1644021 1645587 := bstep (se 1 (by rfl) ⟨1234190, by rfl⟩ : syracuseStep 1645587 = 2468381) B2468381
theorem B2776099 : Blo 1644021 2776099 := bstep (se 1 (by rfl) ⟨2082074, by rfl⟩ : syracuseStep 2776099 = 4164149) B4164149
theorem B1645603 : Blo 1644021 1645603 := bstep (se 1 (by rfl) ⟨1234202, by rfl⟩ : syracuseStep 1645603 = 2468405) B2468405
theorem B5553197 : Blo 1644021 5553197 := bstep (se 3 (by rfl) ⟨1041224, by rfl⟩ : syracuseStep 5553197 = 2082449) B2082449
theorem B1645619 : Blo 1644021 1645619 := bstep (se 1 (by rfl) ⟨1234214, by rfl⟩ : syracuseStep 1645619 = 2468429) B2468429
theorem B1645635 : Blo 1644021 1645635 := bstep (se 1 (by rfl) ⟨1234226, by rfl⟩ : syracuseStep 1645635 = 2468453) B2468453
theorem B8445005 : Blo 1644021 8445005 := bstep (se 3 (by rfl) ⟨1583438, by rfl⟩ : syracuseStep 8445005 = 3166877) B3166877
theorem B1645651 : Blo 1644021 1645651 := bstep (se 1 (by rfl) ⟨1234238, by rfl⟩ : syracuseStep 1645651 = 2468477) B2468477
theorem B1850467 : Blo 1644021 1850467 := bstep (se 1 (by rfl) ⟨1387850, by rfl⟩ : syracuseStep 1850467 = 2775701) B2775701
theorem B5553251 : Blo 1644021 5553251 := bstep (se 1 (by rfl) ⟨4164938, by rfl⟩ : syracuseStep 5553251 = 8329877) B8329877
theorem B1645667 : Blo 1644021 1645667 := bstep (se 1 (by rfl) ⟨1234250, by rfl⟩ : syracuseStep 1645667 = 2468501) B2468501
theorem B1645683 : Blo 1644021 1645683 := bstep (se 1 (by rfl) ⟨1234262, by rfl⟩ : syracuseStep 1645683 = 2468525) B2468525
theorem B1645699 : Blo 1644021 1645699 := bstep (se 1 (by rfl) ⟨1234274, by rfl⟩ : syracuseStep 1645699 = 2468549) B2468549
theorem B1645715 : Blo 1644021 1645715 := bstep (se 1 (by rfl) ⟨1234286, by rfl⟩ : syracuseStep 1645715 = 2468573) B2468573
theorem B1645731 : Blo 1644021 1645731 := bstep (se 1 (by rfl) ⟨1234298, by rfl⟩ : syracuseStep 1645731 = 2468597) B2468597
theorem B2776241 : Blo 1644021 2776241 := bstep (se 2 (by rfl) ⟨1041090, by rfl⟩ : syracuseStep 2776241 = 2082181) B2082181
theorem B1645747 : Blo 1644021 1645747 := bstep (se 1 (by rfl) ⟨1234310, by rfl⟩ : syracuseStep 1645747 = 2468621) B2468621
theorem B1645763 : Blo 1644021 1645763 := bstep (se 1 (by rfl) ⟨1234322, by rfl⟩ : syracuseStep 1645763 = 2468645) B2468645
theorem B15006917 : Blo 1644021 15006917 := bstep (se 4 (by rfl) ⟨1406898, by rfl⟩ : syracuseStep 15006917 = 2813797) B2813797
theorem B3701969 : Blo 1644021 3701969 := bstep (se 2 (by rfl) ⟨1388238, by rfl⟩ : syracuseStep 3701969 = 2776477) B2776477
theorem B1645779 : Blo 1644021 1645779 := bstep (se 1 (by rfl) ⟨1234334, by rfl⟩ : syracuseStep 1645779 = 2468669) B2468669
theorem B3701987 : Blo 1644021 3701987 := bstep (se 1 (by rfl) ⟨2776490, by rfl⟩ : syracuseStep 3701987 = 5552981) B5552981
theorem B1645795 : Blo 1644021 1645795 := bstep (se 1 (by rfl) ⟨1234346, by rfl⟩ : syracuseStep 1645795 = 2468693) B2468693
theorem B8445169 : Blo 1644021 8445169 := bstep (se 2 (by rfl) ⟨3166938, by rfl⟩ : syracuseStep 8445169 = 6333877) B6333877
theorem B1850611 : Blo 1644021 1850611 := bstep (se 1 (by rfl) ⟨1387958, by rfl⟩ : syracuseStep 1850611 = 2775917) B2775917
theorem B1645811 : Blo 1644021 1645811 := bstep (se 1 (by rfl) ⟨1234358, by rfl⟩ : syracuseStep 1645811 = 2468717) B2468717
theorem B1645827 : Blo 1644021 1645827 := bstep (se 1 (by rfl) ⟨1234370, by rfl⟩ : syracuseStep 1645827 = 2468741) B2468741
theorem B1645843 : Blo 1644021 1645843 := bstep (se 1 (by rfl) ⟨1234382, by rfl⟩ : syracuseStep 1645843 = 2468765) B2468765
theorem B1645859 : Blo 1644021 1645859 := bstep (se 1 (by rfl) ⟨1234394, by rfl⟩ : syracuseStep 1645859 = 2468789) B2468789
theorem B2776369 : Blo 1644021 2776369 := bstep (se 2 (by rfl) ⟨1041138, by rfl⟩ : syracuseStep 2776369 = 2082277) B2082277
theorem B1645875 : Blo 1644021 1645875 := bstep (se 1 (by rfl) ⟨1234406, by rfl⟩ : syracuseStep 1645875 = 2468813) B2468813
theorem B2342209 : Blo 1644021 2342209 := bstep (se 2 (by rfl) ⟨878328, by rfl⟩ : syracuseStep 2342209 = 1756657) B1756657
theorem B3333443 : Blo 1644021 3333443 := bstep (se 1 (by rfl) ⟨2500082, by rfl⟩ : syracuseStep 3333443 = 5000165) B5000165
theorem B1645891 : Blo 1644021 1645891 := bstep (se 1 (by rfl) ⟨1234418, by rfl⟩ : syracuseStep 1645891 = 2468837) B2468837
theorem B2776403 : Blo 1644021 2776403 := bstep (se 1 (by rfl) ⟨2082302, by rfl⟩ : syracuseStep 2776403 = 4164605) B4164605
theorem B1645907 : Blo 1644021 1645907 := bstep (se 1 (by rfl) ⟨1234430, by rfl⟩ : syracuseStep 1645907 = 2468861) B2468861
theorem B2342243 : Blo 1644021 2342243 := bstep (se 1 (by rfl) ⟨1756682, by rfl⟩ : syracuseStep 2342243 = 3513365) B3513365
theorem B1645923 : Blo 1644021 1645923 := bstep (se 1 (by rfl) ⟨1234442, by rfl⟩ : syracuseStep 1645923 = 2468885) B2468885
theorem B5553521 : Blo 1644021 5553521 := bstep (se 2 (by rfl) ⟨2082570, by rfl⟩ : syracuseStep 5553521 = 4165141) B4165141
theorem B1645939 : Blo 1644021 1645939 := bstep (se 1 (by rfl) ⟨1234454, by rfl⟩ : syracuseStep 1645939 = 2468909) B2468909
theorem B1850755 : Blo 1644021 1850755 := bstep (se 1 (by rfl) ⟨1388066, by rfl⟩ : syracuseStep 1850755 = 2776133) B2776133
theorem B1645955 : Blo 1644021 1645955 := bstep (se 1 (by rfl) ⟨1234466, by rfl⟩ : syracuseStep 1645955 = 2468933) B2468933
theorem B1645971 : Blo 1644021 1645971 := bstep (se 1 (by rfl) ⟨1234478, by rfl⟩ : syracuseStep 1645971 = 2468957) B2468957
theorem B1645987 : Blo 1644021 1645987 := bstep (se 1 (by rfl) ⟨1234490, by rfl⟩ : syracuseStep 1645987 = 2468981) B2468981
theorem B1646003 : Blo 1644021 1646003 := bstep (se 1 (by rfl) ⟨1234502, by rfl⟩ : syracuseStep 1646003 = 2469005) B2469005
theorem B1646019 : Blo 1644021 1646019 := bstep (se 1 (by rfl) ⟨1234514, by rfl⟩ : syracuseStep 1646019 = 2469029) B2469029
theorem B47431109 : Blo 1644021 47431109 := bstep (se 4 (by rfl) ⟨4446666, by rfl⟩ : syracuseStep 47431109 = 8893333) B8893333
theorem B2776531 : Blo 1644021 2776531 := bstep (se 1 (by rfl) ⟨2082398, by rfl⟩ : syracuseStep 2776531 = 4164797) B4164797
theorem B28089827 : Blo 1644021 28089827 := bstep (se 1 (by rfl) ⟨21067370, by rfl⟩ : syracuseStep 28089827 = 42134741) B42134741
theorem B3702257 : Blo 1644021 3702257 := bstep (se 2 (by rfl) ⟨1388346, by rfl⟩ : syracuseStep 3702257 = 2776693) B2776693
theorem B3702275 : Blo 1644021 3702275 := bstep (se 1 (by rfl) ⟨2776706, by rfl⟩ : syracuseStep 3702275 = 5553413) B5553413
theorem B1850899 : Blo 1644021 1850899 := bstep (se 1 (by rfl) ⟨1388174, by rfl⟩ : syracuseStep 1850899 = 2776349) B2776349
theorem B2776673 : Blo 1644021 2776673 := bstep (se 2 (by rfl) ⟨1041252, by rfl⟩ : syracuseStep 2776673 = 2082505) B2082505
theorem B3513955 : Blo 1644021 3513955 := bstep (se 1 (by rfl) ⟨2635466, by rfl⟩ : syracuseStep 3513955 = 5270933) B5270933
theorem B1851043 : Blo 1644021 1851043 := bstep (se 1 (by rfl) ⟨1388282, by rfl⟩ : syracuseStep 1851043 = 2776565) B2776565
theorem B4685489 : Blo 1644021 4685489 := bstep (se 2 (by rfl) ⟨1757058, by rfl⟩ : syracuseStep 4685489 = 3514117) B3514117
theorem B2776801 : Blo 1644021 2776801 := bstep (se 2 (by rfl) ⟨1041300, by rfl⟩ : syracuseStep 2776801 = 2082601) B2082601
theorem B10690289 : Blo 1644021 10690289 := bstep (se 2 (by rfl) ⟨4008858, by rfl⟩ : syracuseStep 10690289 = 8017717) B8017717
theorem B2776835 : Blo 1644021 2776835 := bstep (se 1 (by rfl) ⟨2082626, by rfl⟩ : syracuseStep 2776835 = 4165253) B4165253
theorem B3702545 : Blo 1644021 3702545 := bstep (se 2 (by rfl) ⟨1388454, by rfl⟩ : syracuseStep 3702545 = 2776909) B2776909
theorem B3702563 : Blo 1644021 3702563 := bstep (se 1 (by rfl) ⟨2776922, by rfl⟩ : syracuseStep 3702563 = 5553845) B5553845
theorem B8560433 : Blo 1644021 8560433 := bstep (se 2 (by rfl) ⟨3210162, by rfl⟩ : syracuseStep 8560433 = 6420325) B6420325
theorem B1851187 : Blo 1644021 1851187 := bstep (se 1 (by rfl) ⟨1388390, by rfl⟩ : syracuseStep 1851187 = 2776781) B2776781
theorem B2776963 : Blo 1644021 2776963 := bstep (se 1 (by rfl) ⟨2082722, by rfl⟩ : syracuseStep 2776963 = 4165445) B4165445
theorem B5554061 : Blo 1644021 5554061 := bstep (se 3 (by rfl) ⟨1041386, by rfl⟩ : syracuseStep 5554061 = 2082773) B2082773
theorem B2342801 : Blo 1644021 2342801 := bstep (se 2 (by rfl) ⟨878550, by rfl⟩ : syracuseStep 2342801 = 1757101) B1757101
theorem B2375569 : Blo 1644021 2375569 := bstep (se 2 (by rfl) ⟨890838, by rfl⟩ : syracuseStep 2375569 = 1781677) B1781677
theorem B1851331 : Blo 1644021 1851331 := bstep (se 1 (by rfl) ⟨1388498, by rfl⟩ : syracuseStep 1851331 = 2776997) B2776997
theorem B5554115 : Blo 1644021 5554115 := bstep (se 1 (by rfl) ⟨4165586, by rfl⟩ : syracuseStep 5554115 = 8331173) B8331173
theorem B2080723 : Blo 1644021 2080723 := bstep (se 1 (by rfl) ⟨1560542, by rfl⟩ : syracuseStep 2080723 = 3121085) B3121085
theorem B2342881 : Blo 1644021 2342881 := bstep (se 2 (by rfl) ⟨878580, by rfl⟩ : syracuseStep 2342881 = 1757161) B1757161
theorem B1851403 : Blo 1644021 1851403 := bstep (se 1 (by rfl) ⟨1388552, by rfl⟩ : syracuseStep 1851403 = 2777105) B2777105
theorem B14057489 : Blo 1644021 14057489 := bstep (se 2 (by rfl) ⟨5271558, by rfl⟩ : syracuseStep 14057489 = 10543117) B10543117
theorem B2965555 : Blo 1644021 2965555 := bstep (se 1 (by rfl) ⟨2224166, by rfl⟩ : syracuseStep 2965555 = 4448333) B4448333
theorem B2343001 : Blo 1644021 2343001 := bstep (se 2 (by rfl) ⟨878625, by rfl⟩ : syracuseStep 2343001 = 1757251) B1757251
theorem B3121267 : Blo 1644021 3121267 := bstep (se 1 (by rfl) ⟨2340950, by rfl⟩ : syracuseStep 3121267 = 4681901) B4681901
theorem B1851511 : Blo 1644021 1851511 := bstep (se 1 (by rfl) ⟨1388633, by rfl⟩ : syracuseStep 1851511 = 2777267) B2777267
theorem B5931139 : Blo 1644021 5931139 := bstep (se 1 (by rfl) ⟨4448354, by rfl⟩ : syracuseStep 5931139 = 8896709) B8896709
theorem B3702923 : Blo 1644021 3702923 := bstep (se 1 (by rfl) ⟨2777192, by rfl⟩ : syracuseStep 3702923 = 5554385) B5554385
theorem B3702977 : Blo 1644021 3702977 := bstep (se 2 (by rfl) ⟨1388616, by rfl⟩ : syracuseStep 3702977 = 2777233) B2777233
theorem B4161739 : Blo 1644021 4161739 := bstep (se 1 (by rfl) ⟨3121304, by rfl⟩ : syracuseStep 4161739 = 6242609) B6242609
theorem B2466059 : Blo 1644021 2466059 := bstep (se 1 (by rfl) ⟨1849544, by rfl⟩ : syracuseStep 2466059 = 3699089) B3699089
theorem B2466071 : Blo 1644021 2466071 := bstep (se 1 (by rfl) ⟨1849553, by rfl⟩ : syracuseStep 2466071 = 3699107) B3699107
theorem B2081047 : Blo 1644021 2081047 := bstep (se 1 (by rfl) ⟨1560785, by rfl⟩ : syracuseStep 2081047 = 3121571) B3121571
theorem B4686103 : Blo 1644021 4686103 := bstep (se 1 (by rfl) ⟨3514577, by rfl⟩ : syracuseStep 4686103 = 7029155) B7029155
theorem B1876267 : Blo 1644021 1876267 := bstep (se 1 (by rfl) ⟨1407200, by rfl⟩ : syracuseStep 1876267 = 2814401) B2814401
theorem B1851691 : Blo 1644021 1851691 := bstep (se 1 (by rfl) ⟨1388768, by rfl⟩ : syracuseStep 1851691 = 2777537) B2777537
theorem B121643309 : Blo 1644021 121643309 := bstep (se 3 (by rfl) ⟨22808120, by rfl⟩ : syracuseStep 121643309 = 45616241) B45616241
theorem B3334475 : Blo 1644021 3334475 := bstep (se 1 (by rfl) ⟨2500856, by rfl⟩ : syracuseStep 3334475 = 5001713) B5001713
theorem B2466137 : Blo 1644021 2466137 := bstep (se 2 (by rfl) ⟨924801, by rfl⟩ : syracuseStep 2466137 = 1849603) B1849603
theorem B4161881 : Blo 1644021 4161881 := bstep (se 2 (by rfl) ⟨1560705, by rfl⟩ : syracuseStep 4161881 = 3121411) B3121411
theorem B2777483 : Blo 1644021 2777483 := bstep (se 1 (by rfl) ⟨2083112, by rfl⟩ : syracuseStep 2777483 = 4166225) B4166225
theorem B3703193 : Blo 1644021 3703193 := bstep (se 2 (by rfl) ⟨1388697, by rfl⟩ : syracuseStep 3703193 = 2777395) B2777395
theorem B2466251 : Blo 1644021 2466251 := bstep (se 1 (by rfl) ⟨1849688, by rfl⟩ : syracuseStep 2466251 = 3699377) B3699377
theorem B2466263 : Blo 1644021 2466263 := bstep (se 1 (by rfl) ⟨1849697, by rfl⟩ : syracuseStep 2466263 = 3699395) B3699395
theorem B6242777 : Blo 1644021 6242777 := bstep (se 2 (by rfl) ⟨2341041, by rfl⟩ : syracuseStep 6242777 = 4682083) B4682083
theorem B3801587 : Blo 1644021 3801587 := bstep (se 1 (by rfl) ⟨2851190, by rfl⟩ : syracuseStep 3801587 = 5702381) B5702381
theorem B3703283 : Blo 1644021 3703283 := bstep (se 1 (by rfl) ⟨2777462, by rfl⟩ : syracuseStep 3703283 = 5554925) B5554925
theorem B2777611 : Blo 1644021 2777611 := bstep (se 1 (by rfl) ⟨2083208, by rfl⟩ : syracuseStep 2777611 = 4166417) B4166417
theorem B40018445 : Blo 1644021 40018445 := bstep (se 3 (by rfl) ⟨7503458, by rfl⟩ : syracuseStep 40018445 = 15006917) B15006917
theorem B3703319 : Blo 1644021 3703319 := bstep (se 1 (by rfl) ⟨2777489, by rfl⟩ : syracuseStep 3703319 = 5554979) B5554979
theorem B2466329 : Blo 1644021 2466329 := bstep (se 2 (by rfl) ⟨924873, by rfl⟩ : syracuseStep 2466329 = 1849747) B1849747
theorem B8331821 : Blo 1644021 8331821 := bstep (se 3 (by rfl) ⟨1562216, by rfl⟩ : syracuseStep 8331821 = 3124433) B3124433
theorem B3121715 : Blo 1644021 3121715 := bstep (se 1 (by rfl) ⟨2341286, by rfl⟩ : syracuseStep 3121715 = 4682573) B4682573
theorem B5554763 : Blo 1644021 5554763 := bstep (se 1 (by rfl) ⟨4166072, by rfl⟩ : syracuseStep 5554763 = 8332145) B8332145
theorem B3121753 : Blo 1644021 3121753 := bstep (se 2 (by rfl) ⟨1170657, by rfl⟩ : syracuseStep 3121753 = 2341315) B2341315
theorem B10543709 : Blo 1644021 10543709 := bstep (se 3 (by rfl) ⟨1976945, by rfl⟩ : syracuseStep 10543709 = 3953891) B3953891
theorem B2466443 : Blo 1644021 2466443 := bstep (se 1 (by rfl) ⟨1849832, by rfl⟩ : syracuseStep 2466443 = 3699665) B3699665
theorem B2466455 : Blo 1644021 2466455 := bstep (se 1 (by rfl) ⟨1849841, by rfl⟩ : syracuseStep 2466455 = 3699683) B3699683
theorem B3703499 : Blo 1644021 3703499 := bstep (se 1 (by rfl) ⟨2777624, by rfl⟩ : syracuseStep 3703499 = 5555249) B5555249
theorem B2466521 : Blo 1644021 2466521 := bstep (se 2 (by rfl) ⟨924945, by rfl⟩ : syracuseStep 2466521 = 1849891) B1849891
theorem B6243095 : Blo 1644021 6243095 := bstep (se 1 (by rfl) ⟨4682321, by rfl⟩ : syracuseStep 6243095 = 9364643) B9364643
theorem B3515159 : Blo 1644021 3515159 := bstep (se 1 (by rfl) ⟨2636369, by rfl⟩ : syracuseStep 3515159 = 5272739) B5272739
theorem B2466635 : Blo 1644021 2466635 := bstep (se 1 (by rfl) ⟨1849976, by rfl⟩ : syracuseStep 2466635 = 3699953) B3699953
theorem B2466647 : Blo 1644021 2466647 := bstep (se 1 (by rfl) ⟨1849985, by rfl⟩ : syracuseStep 2466647 = 3699971) B3699971
theorem B5555033 : Blo 1644021 5555033 := bstep (se 2 (by rfl) ⟨2083137, by rfl⟩ : syracuseStep 5555033 = 4166275) B4166275
theorem B2466713 : Blo 1644021 2466713 := bstep (se 2 (by rfl) ⟨925017, by rfl⟩ : syracuseStep 2466713 = 1850035) B1850035
theorem B3515329 : Blo 1644021 3515329 := bstep (se 2 (by rfl) ⟨1318248, by rfl⟩ : syracuseStep 3515329 = 2636497) B2636497
theorem B2466827 : Blo 1644021 2466827 := bstep (se 1 (by rfl) ⟨1850120, by rfl⟩ : syracuseStep 2466827 = 3700241) B3700241
theorem B2466839 : Blo 1644021 2466839 := bstep (se 1 (by rfl) ⟨1850129, by rfl⟩ : syracuseStep 2466839 = 3700259) B3700259
theorem B3122201 : Blo 1644021 3122201 := bstep (se 2 (by rfl) ⟨1170825, by rfl⟩ : syracuseStep 3122201 = 2341651) B2341651
theorem B4686923 : Blo 1644021 4686923 := bstep (se 1 (by rfl) ⟨3515192, by rfl⟩ : syracuseStep 4686923 = 7030385) B7030385
theorem B2466905 : Blo 1644021 2466905 := bstep (se 2 (by rfl) ⟨925089, by rfl⟩ : syracuseStep 2466905 = 1850179) B1850179
theorem B4162711 : Blo 1644021 4162711 := bstep (se 1 (by rfl) ⟨3122033, by rfl⟩ : syracuseStep 4162711 = 6244067) B6244067
theorem B6669485 : Blo 1644021 6669485 := bstep (se 3 (by rfl) ⟨1250528, by rfl⟩ : syracuseStep 6669485 = 2501057) B2501057
theorem B2467019 : Blo 1644021 2467019 := bstep (se 1 (by rfl) ⟨1850264, by rfl⟩ : syracuseStep 2467019 = 3700529) B3700529
theorem B2467031 : Blo 1644021 2467031 := bstep (se 1 (by rfl) ⟨1850273, by rfl⟩ : syracuseStep 2467031 = 3700547) B3700547
theorem B8324369 : Blo 1644021 8324369 := bstep (se 2 (by rfl) ⟨3121638, by rfl⟩ : syracuseStep 8324369 = 6243277) B6243277
theorem B2467097 : Blo 1644021 2467097 := bstep (se 2 (by rfl) ⟨925161, by rfl⟩ : syracuseStep 2467097 = 1850323) B1850323
theorem B2467211 : Blo 1644021 2467211 := bstep (se 1 (by rfl) ⟨1850408, by rfl⟩ : syracuseStep 2467211 = 3700817) B3700817
theorem B2467223 : Blo 1644021 2467223 := bstep (se 1 (by rfl) ⟨1850417, by rfl⟩ : syracuseStep 2467223 = 3700835) B3700835
theorem B8324531 : Blo 1644021 8324531 := bstep (se 1 (by rfl) ⟨6243398, by rfl⟩ : syracuseStep 8324531 = 12486797) B12486797
theorem B6243763 : Blo 1644021 6243763 := bstep (se 1 (by rfl) ⟨4682822, by rfl⟩ : syracuseStep 6243763 = 9365645) B9365645
theorem B2467289 : Blo 1644021 2467289 := bstep (se 2 (by rfl) ⟨925233, by rfl⟩ : syracuseStep 2467289 = 1850467) B1850467
theorem B4163147 : Blo 1644021 4163147 := bstep (se 1 (by rfl) ⟨3122360, by rfl⟩ : syracuseStep 4163147 = 6244721) B6244721
theorem B2467403 : Blo 1644021 2467403 := bstep (se 1 (by rfl) ⟨1850552, by rfl⟩ : syracuseStep 2467403 = 3701105) B3701105
theorem B2467415 : Blo 1644021 2467415 := bstep (se 1 (by rfl) ⟨1850561, by rfl⟩ : syracuseStep 2467415 = 3701123) B3701123
theorem B2467481 : Blo 1644021 2467481 := bstep (se 2 (by rfl) ⟨925305, by rfl⟩ : syracuseStep 2467481 = 1850611) B1850611
theorem B1976023 : Blo 1644021 1976023 := bstep (se 1 (by rfl) ⟨1482017, by rfl⟩ : syracuseStep 1976023 = 2964035) B2964035
theorem B3122945 : Blo 1644021 3122945 := bstep (se 2 (by rfl) ⟨1171104, by rfl⟩ : syracuseStep 3122945 = 2342209) B2342209
theorem B2467595 : Blo 1644021 2467595 := bstep (se 1 (by rfl) ⟨1850696, by rfl⟩ : syracuseStep 2467595 = 3701393) B3701393
theorem B2467607 : Blo 1644021 2467607 := bstep (se 1 (by rfl) ⟨1850705, by rfl⟩ : syracuseStep 2467607 = 3701411) B3701411
theorem B4007731 : Blo 1644021 4007731 := bstep (se 1 (by rfl) ⟨3005798, by rfl⟩ : syracuseStep 4007731 = 6011597) B6011597
theorem B2467673 : Blo 1644021 2467673 := bstep (se 2 (by rfl) ⟨925377, by rfl⟩ : syracuseStep 2467673 = 1850755) B1850755
theorem B15001523 : Blo 1644021 15001523 := bstep (se 1 (by rfl) ⟨11251142, by rfl⟩ : syracuseStep 15001523 = 22502285) B22502285
theorem B4163521 : Blo 1644021 4163521 := bstep (se 2 (by rfl) ⟨1561320, by rfl⟩ : syracuseStep 4163521 = 3122641) B3122641
theorem B2467787 : Blo 1644021 2467787 := bstep (se 1 (by rfl) ⟨1850840, by rfl⟩ : syracuseStep 2467787 = 3701681) B3701681
theorem B2082763 : Blo 1644021 2082763 := bstep (se 1 (by rfl) ⟨1562072, by rfl⟩ : syracuseStep 2082763 = 3124145) B3124145
theorem B2467799 : Blo 1644021 2467799 := bstep (se 1 (by rfl) ⟨1850849, by rfl⟩ : syracuseStep 2467799 = 3701699) B3701699
theorem B3123211 : Blo 1644021 3123211 := bstep (se 1 (by rfl) ⟨2342408, by rfl⟩ : syracuseStep 3123211 = 4684817) B4684817
theorem B2467865 : Blo 1644021 2467865 := bstep (se 2 (by rfl) ⟨925449, by rfl⟩ : syracuseStep 2467865 = 1850899) B1850899
theorem B5630003 : Blo 1644021 5630003 := bstep (se 1 (by rfl) ⟨4222502, by rfl⟩ : syracuseStep 5630003 = 8445005) B8445005
theorem B94832693 : Blo 1644021 94832693 := bstep (se 5 (by rfl) ⟨4445282, by rfl⟩ : syracuseStep 94832693 = 8890565) B8890565
theorem B2467979 : Blo 1644021 2467979 := bstep (se 1 (by rfl) ⟨1850984, by rfl⟩ : syracuseStep 2467979 = 3701969) B3701969
theorem B2467991 : Blo 1644021 2467991 := bstep (se 1 (by rfl) ⟨1850993, by rfl⟩ : syracuseStep 2467991 = 3701987) B3701987
theorem B2468057 : Blo 1644021 2468057 := bstep (se 2 (by rfl) ⟨925521, by rfl⟩ : syracuseStep 2468057 = 1851043) B1851043
theorem B4999475 : Blo 1644021 4999475 := bstep (se 1 (by rfl) ⟨3749606, by rfl⟩ : syracuseStep 4999475 = 7499213) B7499213
theorem B2468171 : Blo 1644021 2468171 := bstep (se 1 (by rfl) ⟨1851128, by rfl⟩ : syracuseStep 2468171 = 3702257) B3702257
theorem B2468183 : Blo 1644021 2468183 := bstep (se 1 (by rfl) ⟨1851137, by rfl⟩ : syracuseStep 2468183 = 3702275) B3702275
theorem B2468249 : Blo 1644021 2468249 := bstep (se 2 (by rfl) ⟨925593, by rfl⟩ : syracuseStep 2468249 = 1851187) B1851187
theorem B3123659 : Blo 1644021 3123659 := bstep (se 1 (by rfl) ⟨2342744, by rfl⟩ : syracuseStep 3123659 = 4685489) B4685489
theorem B2468363 : Blo 1644021 2468363 := bstep (se 1 (by rfl) ⟨1851272, by rfl⟩ : syracuseStep 2468363 = 3702545) B3702545
theorem B4164119 : Blo 1644021 4164119 := bstep (se 1 (by rfl) ⟨3123089, by rfl⟩ : syracuseStep 4164119 = 6246179) B6246179
theorem B2468375 : Blo 1644021 2468375 := bstep (se 1 (by rfl) ⟨1851281, by rfl⟩ : syracuseStep 2468375 = 3702563) B3702563
theorem B23726627 : Blo 1644021 23726627 := bstep (se 1 (by rfl) ⟨17794970, by rfl⟩ : syracuseStep 23726627 = 35589941) B35589941
theorem B2468441 : Blo 1644021 2468441 := bstep (se 2 (by rfl) ⟨925665, by rfl⟩ : syracuseStep 2468441 = 1851331) B1851331
theorem B3123841 : Blo 1644021 3123841 := bstep (se 2 (by rfl) ⟨1171440, by rfl⟩ : syracuseStep 3123841 = 2342881) B2342881
theorem B6245009 : Blo 1644021 6245009 := bstep (se 2 (by rfl) ⟨2341878, by rfl⟩ : syracuseStep 6245009 = 4683757) B4683757
theorem B13519511 : Blo 1644021 13519511 := bstep (se 1 (by rfl) ⟨10139633, by rfl⟩ : syracuseStep 13519511 = 20279267) B20279267
theorem B7023277 : Blo 1644021 7023277 := bstep (se 3 (by rfl) ⟨1316864, by rfl⟩ : syracuseStep 7023277 = 2633729) B2633729
theorem B2468555 : Blo 1644021 2468555 := bstep (se 1 (by rfl) ⟨1851416, by rfl⟩ : syracuseStep 2468555 = 3702833) B3702833
theorem B2468567 : Blo 1644021 2468567 := bstep (se 1 (by rfl) ⟨1851425, by rfl⟩ : syracuseStep 2468567 = 3702851) B3702851
theorem B19999493 : Blo 1644021 19999493 := bstep (se 4 (by rfl) ⟨1874952, by rfl⟩ : syracuseStep 19999493 = 3749905) B3749905
theorem B5548823 : Blo 1644021 5548823 := bstep (se 1 (by rfl) ⟨4161617, by rfl⟩ : syracuseStep 5548823 = 8323235) B8323235
theorem B2468633 : Blo 1644021 2468633 := bstep (se 2 (by rfl) ⟨925737, by rfl⟩ : syracuseStep 2468633 = 1851475) B1851475
theorem B7023449 : Blo 1644021 7023449 := bstep (se 2 (by rfl) ⟨2633793, by rfl⟩ : syracuseStep 7023449 = 5267587) B5267587
theorem B2468747 : Blo 1644021 2468747 := bstep (se 1 (by rfl) ⟨1851560, by rfl⟩ : syracuseStep 2468747 = 3703121) B3703121
theorem B2468759 : Blo 1644021 2468759 := bstep (se 1 (by rfl) ⟨1851569, by rfl⟩ : syracuseStep 2468759 = 3703139) B3703139
theorem B14060465 : Blo 1644021 14060465 := bstep (se 2 (by rfl) ⟨5272674, by rfl⟩ : syracuseStep 14060465 = 10545349) B10545349
theorem B3124183 : Blo 1644021 3124183 := bstep (se 1 (by rfl) ⟨2343137, by rfl⟩ : syracuseStep 3124183 = 4686275) B4686275
theorem B2468825 : Blo 1644021 2468825 := bstep (se 2 (by rfl) ⟨925809, by rfl⟩ : syracuseStep 2468825 = 1851619) B1851619
theorem B10546193 : Blo 1644021 10546193 := bstep (se 2 (by rfl) ⟨3954822, by rfl⟩ : syracuseStep 10546193 = 7909645) B7909645
theorem B19254347 : Blo 1644021 19254347 := bstep (se 1 (by rfl) ⟨14440760, by rfl⟩ : syracuseStep 19254347 = 28881521) B28881521
theorem B2468939 : Blo 1644021 2468939 := bstep (se 1 (by rfl) ⟨1851704, by rfl⟩ : syracuseStep 2468939 = 3703409) B3703409
theorem B2468951 : Blo 1644021 2468951 := bstep (se 1 (by rfl) ⟨1851713, by rfl⟩ : syracuseStep 2468951 = 3703427) B3703427
theorem B3951767 : Blo 1644021 3951767 := bstep (se 1 (by rfl) ⟨2963825, by rfl⟩ : syracuseStep 3951767 = 5927651) B5927651
theorem B2469017 : Blo 1644021 2469017 := bstep (se 2 (by rfl) ⟨925881, by rfl⟩ : syracuseStep 2469017 = 1851763) B1851763
theorem B14240947 : Blo 1644021 14240947 := bstep (se 1 (by rfl) ⟨10680710, by rfl⟩ : syracuseStep 14240947 = 21361421) B21361421
theorem B3124403 : Blo 1644021 3124403 := bstep (se 1 (by rfl) ⟨2343302, by rfl⟩ : syracuseStep 3124403 = 4686605) B4686605
theorem B7908569 : Blo 1644021 7908569 := bstep (se 2 (by rfl) ⟨2965713, by rfl⟩ : syracuseStep 7908569 = 5931427) B5931427
theorem B5549363 : Blo 1644021 5549363 := bstep (se 1 (by rfl) ⟨4162022, by rfl⟩ : syracuseStep 5549363 = 8324045) B8324045
theorem B4164929 : Blo 1644021 4164929 := bstep (se 2 (by rfl) ⟨1561848, by rfl⟩ : syracuseStep 4164929 = 3123697) B3123697
theorem B8326475 : Blo 1644021 8326475 := bstep (se 1 (by rfl) ⟨6244856, by rfl⟩ : syracuseStep 8326475 = 12489713) B12489713
theorem B6245707 : Blo 1644021 6245707 := bstep (se 1 (by rfl) ⟨4684280, by rfl⟩ : syracuseStep 6245707 = 9368561) B9368561
theorem B12021085 : Blo 1644021 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B35556725 : Blo 1644021 35556725 := bstep (se 5 (by rfl) ⟨1666721, by rfl⟩ : syracuseStep 35556725 = 3333443) B3333443
theorem B3124631 : Blo 1644021 3124631 := bstep (se 1 (by rfl) ⟨2343473, by rfl⟩ : syracuseStep 3124631 = 4686947) B4686947
theorem B5549633 : Blo 1644021 5549633 := bstep (se 2 (by rfl) ⟨2081112, by rfl⟩ : syracuseStep 5549633 = 4162225) B4162225
theorem B6245981 : Blo 1644021 6245981 := bstep (se 3 (by rfl) ⟨1171121, by rfl⟩ : syracuseStep 6245981 = 2342243) B2342243
theorem B5344861 : Blo 1644021 5344861 := bstep (se 3 (by rfl) ⟨1002161, by rfl⟩ : syracuseStep 5344861 = 2004323) B2004323
theorem B101346947 : Blo 1644021 101346947 := bstep (se 1 (by rfl) ⟨76010210, by rfl⟩ : syracuseStep 101346947 = 152020421) B152020421
theorem B2813579 : Blo 1644021 2813579 := bstep (se 1 (by rfl) ⟨2110184, by rfl⟩ : syracuseStep 2813579 = 4220369) B4220369
theorem B7925399 : Blo 1644021 7925399 := bstep (se 1 (by rfl) ⟨5944049, by rfl⟩ : syracuseStep 7925399 = 11888099) B11888099
theorem B9498413 : Blo 1644021 9498413 := bstep (se 3 (by rfl) ⟨1780952, by rfl⟩ : syracuseStep 9498413 = 3561905) B3561905
theorem B6328153 : Blo 1644021 6328153 := bstep (se 2 (by rfl) ⟨2373057, by rfl⟩ : syracuseStep 6328153 = 4746115) B4746115
theorem B4165465 : Blo 1644021 4165465 := bstep (se 2 (by rfl) ⟨1562049, by rfl⟩ : syracuseStep 4165465 = 3124099) B3124099
theorem B13332545 : Blo 1644021 13332545 := bstep (se 2 (by rfl) ⟨4999704, by rfl⟩ : syracuseStep 13332545 = 9999409) B9999409
theorem B5550173 : Blo 1644021 5550173 := bstep (se 3 (by rfl) ⟨1040657, by rfl⟩ : syracuseStep 5550173 = 2081315) B2081315
theorem B1757323 : Blo 1644021 1757323 := bstep (se 1 (by rfl) ⟨1317992, by rfl⟩ : syracuseStep 1757323 = 2635985) B2635985
theorem B6418577 : Blo 1644021 6418577 := bstep (se 2 (by rfl) ⟨2406966, by rfl⟩ : syracuseStep 6418577 = 4813933) B4813933
theorem B6246679 : Blo 1644021 6246679 := bstep (se 1 (by rfl) ⟨4685009, by rfl⟩ : syracuseStep 6246679 = 9370019) B9370019
theorem B5927219 : Blo 1644021 5927219 := bstep (se 1 (by rfl) ⟨4445414, by rfl⟩ : syracuseStep 5927219 = 8890829) B8890829
theorem B11260225 : Blo 1644021 11260225 := bstep (se 2 (by rfl) ⟨4222584, by rfl⟩ : syracuseStep 11260225 = 8445169) B8445169
theorem B9015731 : Blo 1644021 9015731 := bstep (se 1 (by rfl) ⟨6761798, by rfl⟩ : syracuseStep 9015731 = 13523597) B13523597
theorem B7025089 : Blo 1644021 7025089 := bstep (se 2 (by rfl) ⟨2634408, by rfl⟩ : syracuseStep 7025089 = 5268817) B5268817
theorem B3699161 : Blo 1644021 3699161 := bstep (se 2 (by rfl) ⟨1387185, by rfl⟩ : syracuseStep 3699161 = 2774371) B2774371
theorem B18739673 : Blo 1644021 18739673 := bstep (se 2 (by rfl) ⟨7027377, by rfl⟩ : syracuseStep 18739673 = 14054755) B14054755
theorem B3699251 : Blo 1644021 3699251 := bstep (se 1 (by rfl) ⟨2774438, by rfl⟩ : syracuseStep 3699251 = 5548877) B5548877
theorem B1667659 : Blo 1644021 1667659 := bstep (se 1 (by rfl) ⟨1250744, by rfl⟩ : syracuseStep 1667659 = 2501489) B2501489
theorem B3699287 : Blo 1644021 3699287 := bstep (se 1 (by rfl) ⟨2774465, by rfl⟩ : syracuseStep 3699287 = 5548931) B5548931
theorem B1667671 : Blo 1644021 1667671 := bstep (se 1 (by rfl) ⟨1250753, by rfl⟩ : syracuseStep 1667671 = 2501507) B2501507
theorem B9368243 : Blo 1644021 9368243 := bstep (se 1 (by rfl) ⟨7026182, by rfl⟩ : syracuseStep 9368243 = 14052365) B14052365
theorem B12669701 : Blo 1644021 12669701 := bstep (se 4 (by rfl) ⟨1187784, by rfl⟩ : syracuseStep 12669701 = 2375569) B2375569
theorem B3699467 : Blo 1644021 3699467 := bstep (se 1 (by rfl) ⟨2774600, by rfl⟩ : syracuseStep 3699467 = 5549201) B5549201
theorem B3699521 : Blo 1644021 3699521 := bstep (se 2 (by rfl) ⟨1387320, by rfl⟩ : syracuseStep 3699521 = 2774641) B2774641
theorem B3511297 : Blo 1644021 3511297 := bstep (se 2 (by rfl) ⟨1316736, by rfl⟩ : syracuseStep 3511297 = 2633473) B2633473
theorem B3699737 : Blo 1644021 3699737 := bstep (se 2 (by rfl) ⟨1387401, by rfl⟩ : syracuseStep 3699737 = 2774803) B2774803
theorem B6247469 : Blo 1644021 6247469 := bstep (se 3 (by rfl) ⟨1171400, by rfl⟩ : syracuseStep 6247469 = 2342801) B2342801
theorem B8328257 : Blo 1644021 8328257 := bstep (se 2 (by rfl) ⟨3123096, by rfl⟩ : syracuseStep 8328257 = 6246193) B6246193
theorem B3699827 : Blo 1644021 3699827 := bstep (se 1 (by rfl) ⟨2774870, by rfl⟩ : syracuseStep 3699827 = 5549741) B5549741
theorem B3699863 : Blo 1644021 3699863 := bstep (se 1 (by rfl) ⟨2774897, by rfl⟩ : syracuseStep 3699863 = 5549795) B5549795
theorem B5551307 : Blo 1644021 5551307 := bstep (se 1 (by rfl) ⟨4163480, by rfl⟩ : syracuseStep 5551307 = 8326961) B8326961
theorem B5706955 : Blo 1644021 5706955 := bstep (se 1 (by rfl) ⟨4280216, by rfl⟩ : syracuseStep 5706955 = 8560433) B8560433
theorem B2774297 : Blo 1644021 2774297 := bstep (se 2 (by rfl) ⟨1040361, by rfl⟩ : syracuseStep 2774297 = 2080723) B2080723
theorem B3700043 : Blo 1644021 3700043 := bstep (se 1 (by rfl) ⟨2775032, by rfl⟩ : syracuseStep 3700043 = 5550065) B5550065
theorem B4445533 : Blo 1644021 4445533 := bstep (se 3 (by rfl) ⟨833537, by rfl⟩ : syracuseStep 4445533 = 1667075) B1667075
theorem B3700097 : Blo 1644021 3700097 := bstep (se 2 (by rfl) ⟨1387536, by rfl⟩ : syracuseStep 3700097 = 2775073) B2775073
theorem B2774425 : Blo 1644021 2774425 := bstep (se 2 (by rfl) ⟨1040409, by rfl⟩ : syracuseStep 2774425 = 2080819) B2080819
theorem B4683187 : Blo 1644021 4683187 := bstep (se 1 (by rfl) ⟨3512390, by rfl⟩ : syracuseStep 4683187 = 7024781) B7024781
theorem B5551577 : Blo 1644021 5551577 := bstep (se 2 (by rfl) ⟨2081841, by rfl⟩ : syracuseStep 5551577 = 4163683) B4163683
theorem B1644023 : Blo 1644021 1644023 := bstep (se 1 (by rfl) ⟨1233017, by rfl⟩ : syracuseStep 1644023 = 2466035) B2466035
theorem B1644043 : Blo 1644021 1644043 := bstep (se 1 (by rfl) ⟨1233032, by rfl⟩ : syracuseStep 1644043 = 2466065) B2466065
theorem B1644055 : Blo 1644021 1644055 := bstep (se 1 (by rfl) ⟨1233041, by rfl⟩ : syracuseStep 1644055 = 2466083) B2466083
theorem B3954199 : Blo 1644021 3954199 := bstep (se 1 (by rfl) ⟨2965649, by rfl⟩ : syracuseStep 3954199 = 5931299) B5931299
theorem B1644075 : Blo 1644021 1644075 := bstep (se 1 (by rfl) ⟨1233056, by rfl⟩ : syracuseStep 1644075 = 2466113) B2466113
theorem B1644087 : Blo 1644021 1644087 := bstep (se 1 (by rfl) ⟨1233065, by rfl⟩ : syracuseStep 1644087 = 2466131) B2466131
theorem B1644107 : Blo 1644021 1644107 := bstep (se 1 (by rfl) ⟨1233080, by rfl⟩ : syracuseStep 1644107 = 2466161) B2466161
theorem B1644119 : Blo 1644021 1644119 := bstep (se 1 (by rfl) ⟨1233089, by rfl⟩ : syracuseStep 1644119 = 2466179) B2466179
theorem B3700313 : Blo 1644021 3700313 := bstep (se 2 (by rfl) ⟨1387617, by rfl⟩ : syracuseStep 3700313 = 2775235) B2775235
theorem B1644139 : Blo 1644021 1644139 := bstep (se 1 (by rfl) ⟨1233104, by rfl⟩ : syracuseStep 1644139 = 2466209) B2466209
theorem B1644151 : Blo 1644021 1644151 := bstep (se 1 (by rfl) ⟨1233113, by rfl⟩ : syracuseStep 1644151 = 2466227) B2466227
theorem B1644171 : Blo 1644021 1644171 := bstep (se 1 (by rfl) ⟨1233128, by rfl⟩ : syracuseStep 1644171 = 2466257) B2466257
theorem B1644183 : Blo 1644021 1644183 := bstep (se 1 (by rfl) ⟨1233137, by rfl⟩ : syracuseStep 1644183 = 2466275) B2466275
theorem B4683415 : Blo 1644021 4683415 := bstep (se 1 (by rfl) ⟨3512561, by rfl⟩ : syracuseStep 4683415 = 7025123) B7025123
theorem B1644203 : Blo 1644021 1644203 := bstep (se 1 (by rfl) ⟨1233152, by rfl⟩ : syracuseStep 1644203 = 2466305) B2466305
theorem B3700403 : Blo 1644021 3700403 := bstep (se 1 (by rfl) ⟨2775302, by rfl⟩ : syracuseStep 3700403 = 5550605) B5550605
theorem B1644215 : Blo 1644021 1644215 := bstep (se 1 (by rfl) ⟨1233161, by rfl⟩ : syracuseStep 1644215 = 2466323) B2466323
theorem B1644235 : Blo 1644021 1644235 := bstep (se 1 (by rfl) ⟨1233176, by rfl⟩ : syracuseStep 1644235 = 2466353) B2466353
theorem B1644247 : Blo 1644021 1644247 := bstep (se 1 (by rfl) ⟨1233185, by rfl⟩ : syracuseStep 1644247 = 2466371) B2466371
theorem B3700439 : Blo 1644021 3700439 := bstep (se 1 (by rfl) ⟨2775329, by rfl⟩ : syracuseStep 3700439 = 5550659) B5550659
theorem B1644267 : Blo 1644021 1644267 := bstep (se 1 (by rfl) ⟨1233200, by rfl⟩ : syracuseStep 1644267 = 2466401) B2466401
theorem B1644279 : Blo 1644021 1644279 := bstep (se 1 (by rfl) ⟨1233209, by rfl⟩ : syracuseStep 1644279 = 2466419) B2466419
theorem B1644299 : Blo 1644021 1644299 := bstep (se 1 (by rfl) ⟨1233224, by rfl⟩ : syracuseStep 1644299 = 2466449) B2466449
theorem B1644311 : Blo 1644021 1644311 := bstep (se 1 (by rfl) ⟨1233233, by rfl⟩ : syracuseStep 1644311 = 2466467) B2466467
theorem B4445975 : Blo 1644021 4445975 := bstep (se 1 (by rfl) ⟨3334481, by rfl⟩ : syracuseStep 4445975 = 6668963) B6668963
theorem B1644331 : Blo 1644021 1644331 := bstep (se 1 (by rfl) ⟨1233248, by rfl⟩ : syracuseStep 1644331 = 2466497) B2466497
theorem B1644343 : Blo 1644021 1644343 := bstep (se 1 (by rfl) ⟨1233257, by rfl⟩ : syracuseStep 1644343 = 2466515) B2466515
theorem B1644363 : Blo 1644021 1644363 := bstep (se 1 (by rfl) ⟨1233272, by rfl⟩ : syracuseStep 1644363 = 2466545) B2466545
theorem B1644375 : Blo 1644021 1644375 := bstep (se 1 (by rfl) ⟨1233281, by rfl⟩ : syracuseStep 1644375 = 2466563) B2466563
theorem B1644395 : Blo 1644021 1644395 := bstep (se 1 (by rfl) ⟨1233296, by rfl⟩ : syracuseStep 1644395 = 2466593) B2466593
theorem B1644407 : Blo 1644021 1644407 := bstep (se 1 (by rfl) ⟨1233305, by rfl⟩ : syracuseStep 1644407 = 2466611) B2466611
theorem B1644427 : Blo 1644021 1644427 := bstep (se 1 (by rfl) ⟨1233320, by rfl⟩ : syracuseStep 1644427 = 2466641) B2466641
theorem B3700619 : Blo 1644021 3700619 := bstep (se 1 (by rfl) ⟨2775464, by rfl⟩ : syracuseStep 3700619 = 5550929) B5550929
theorem B1644439 : Blo 1644021 1644439 := bstep (se 1 (by rfl) ⟨1233329, by rfl⟩ : syracuseStep 1644439 = 2466659) B2466659
theorem B1644459 : Blo 1644021 1644459 := bstep (se 1 (by rfl) ⟨1233344, by rfl⟩ : syracuseStep 1644459 = 2466689) B2466689
theorem B1644471 : Blo 1644021 1644471 := bstep (se 1 (by rfl) ⟨1233353, by rfl⟩ : syracuseStep 1644471 = 2466707) B2466707
theorem B3700673 : Blo 1644021 3700673 := bstep (se 2 (by rfl) ⟨1387752, by rfl⟩ : syracuseStep 3700673 = 2775505) B2775505
theorem B1644491 : Blo 1644021 1644491 := bstep (se 1 (by rfl) ⟨1233368, by rfl⟩ : syracuseStep 1644491 = 2466737) B2466737
theorem B2774999 : Blo 1644021 2774999 := bstep (se 1 (by rfl) ⟨2081249, by rfl⟩ : syracuseStep 2774999 = 4162499) B4162499
theorem B1644503 : Blo 1644021 1644503 := bstep (se 1 (by rfl) ⟨1233377, by rfl⟩ : syracuseStep 1644503 = 2466755) B2466755
theorem B1644523 : Blo 1644021 1644523 := bstep (se 1 (by rfl) ⟨1233392, by rfl⟩ : syracuseStep 1644523 = 2466785) B2466785
theorem B1644535 : Blo 1644021 1644535 := bstep (se 1 (by rfl) ⟨1233401, by rfl⟩ : syracuseStep 1644535 = 2466803) B2466803
theorem B1644555 : Blo 1644021 1644555 := bstep (se 1 (by rfl) ⟨1233416, by rfl⟩ : syracuseStep 1644555 = 2466833) B2466833
theorem B1644567 : Blo 1644021 1644567 := bstep (se 1 (by rfl) ⟨1233425, by rfl⟩ : syracuseStep 1644567 = 2466851) B2466851
theorem B1644587 : Blo 1644021 1644587 := bstep (se 1 (by rfl) ⟨1233440, by rfl⟩ : syracuseStep 1644587 = 2466881) B2466881
theorem B1644599 : Blo 1644021 1644599 := bstep (se 1 (by rfl) ⟨1233449, by rfl⟩ : syracuseStep 1644599 = 2466899) B2466899
theorem B1644619 : Blo 1644021 1644619 := bstep (se 1 (by rfl) ⟨1233464, by rfl⟩ : syracuseStep 1644619 = 2466929) B2466929
theorem B7026763 : Blo 1644021 7026763 := bstep (se 1 (by rfl) ⟨5270072, by rfl⟩ : syracuseStep 7026763 = 10540145) B10540145
theorem B2775127 : Blo 1644021 2775127 := bstep (se 1 (by rfl) ⟨2081345, by rfl⟩ : syracuseStep 2775127 = 4162691) B4162691
theorem B1644631 : Blo 1644021 1644631 := bstep (se 1 (by rfl) ⟨1233473, by rfl⟩ : syracuseStep 1644631 = 2466947) B2466947
theorem B9369701 : Blo 1644021 9369701 := bstep (se 4 (by rfl) ⟨878409, by rfl⟩ : syracuseStep 9369701 = 1756819) B1756819
theorem B1644651 : Blo 1644021 1644651 := bstep (se 1 (by rfl) ⟨1233488, by rfl⟩ : syracuseStep 1644651 = 2466977) B2466977
theorem B1644663 : Blo 1644021 1644663 := bstep (se 1 (by rfl) ⟨1233497, by rfl⟩ : syracuseStep 1644663 = 2466995) B2466995
theorem B15005827 : Blo 1644021 15005827 := bstep (se 1 (by rfl) ⟨11254370, by rfl⟩ : syracuseStep 15005827 = 22508741) B22508741
theorem B3512459 : Blo 1644021 3512459 := bstep (se 1 (by rfl) ⟨2634344, by rfl⟩ : syracuseStep 3512459 = 5268689) B5268689
theorem B1644683 : Blo 1644021 1644683 := bstep (se 1 (by rfl) ⟨1233512, by rfl⟩ : syracuseStep 1644683 = 2467025) B2467025
theorem B1644695 : Blo 1644021 1644695 := bstep (se 1 (by rfl) ⟨1233521, by rfl⟩ : syracuseStep 1644695 = 2467043) B2467043
theorem B5552279 : Blo 1644021 5552279 := bstep (se 1 (by rfl) ⟨4164209, by rfl⟩ : syracuseStep 5552279 = 8328419) B8328419
theorem B3700889 : Blo 1644021 3700889 := bstep (se 2 (by rfl) ⟨1387833, by rfl⟩ : syracuseStep 3700889 = 2775667) B2775667
theorem B1644715 : Blo 1644021 1644715 := bstep (se 1 (by rfl) ⟨1233536, by rfl⟩ : syracuseStep 1644715 = 2467073) B2467073
theorem B7608493 : Blo 1644021 7608493 := bstep (se 3 (by rfl) ⟨1426592, by rfl⟩ : syracuseStep 7608493 = 2853185) B2853185
theorem B7502003 : Blo 1644021 7502003 := bstep (se 1 (by rfl) ⟨5626502, by rfl⟩ : syracuseStep 7502003 = 11253005) B11253005
theorem B1644727 : Blo 1644021 1644727 := bstep (se 1 (by rfl) ⟨1233545, by rfl⟩ : syracuseStep 1644727 = 2467091) B2467091
theorem B1644747 : Blo 1644021 1644747 := bstep (se 1 (by rfl) ⟨1233560, by rfl⟩ : syracuseStep 1644747 = 2467121) B2467121
theorem B1644759 : Blo 1644021 1644759 := bstep (se 1 (by rfl) ⟨1233569, by rfl⟩ : syracuseStep 1644759 = 2467139) B2467139
theorem B1644779 : Blo 1644021 1644779 := bstep (se 1 (by rfl) ⟨1233584, by rfl⟩ : syracuseStep 1644779 = 2467169) B2467169
theorem B3700979 : Blo 1644021 3700979 := bstep (se 1 (by rfl) ⟨2775734, by rfl⟩ : syracuseStep 3700979 = 5551469) B5551469
theorem B1644791 : Blo 1644021 1644791 := bstep (se 1 (by rfl) ⟨1233593, by rfl⟩ : syracuseStep 1644791 = 2467187) B2467187
theorem B1644811 : Blo 1644021 1644811 := bstep (se 1 (by rfl) ⟨1233608, by rfl⟩ : syracuseStep 1644811 = 2467217) B2467217
theorem B1644823 : Blo 1644021 1644823 := bstep (se 1 (by rfl) ⟨1233617, by rfl⟩ : syracuseStep 1644823 = 2467235) B2467235
theorem B3701015 : Blo 1644021 3701015 := bstep (se 1 (by rfl) ⟨2775761, by rfl⟩ : syracuseStep 3701015 = 5551523) B5551523
theorem B1644843 : Blo 1644021 1644843 := bstep (se 1 (by rfl) ⟨1233632, by rfl⟩ : syracuseStep 1644843 = 2467265) B2467265
theorem B1644855 : Blo 1644021 1644855 := bstep (se 1 (by rfl) ⟨1233641, by rfl⟩ : syracuseStep 1644855 = 2467283) B2467283
theorem B1849675 : Blo 1644021 1849675 := bstep (se 1 (by rfl) ⟨1387256, by rfl⟩ : syracuseStep 1849675 = 2774513) B2774513
theorem B1644875 : Blo 1644021 1644875 := bstep (se 1 (by rfl) ⟨1233656, by rfl⟩ : syracuseStep 1644875 = 2467313) B2467313
theorem B1644887 : Blo 1644021 1644887 := bstep (se 1 (by rfl) ⟨1233665, by rfl⟩ : syracuseStep 1644887 = 2467331) B2467331
theorem B7027037 : Blo 1644021 7027037 := bstep (se 3 (by rfl) ⟨1317569, by rfl⟩ : syracuseStep 7027037 = 2635139) B2635139
theorem B1644907 : Blo 1644021 1644907 := bstep (se 1 (by rfl) ⟨1233680, by rfl⟩ : syracuseStep 1644907 = 2467361) B2467361
theorem B1644919 : Blo 1644021 1644919 := bstep (se 1 (by rfl) ⟨1233689, by rfl⟩ : syracuseStep 1644919 = 2467379) B2467379
theorem B1644939 : Blo 1644021 1644939 := bstep (se 1 (by rfl) ⟨1233704, by rfl⟩ : syracuseStep 1644939 = 2467409) B2467409
theorem B1644951 : Blo 1644021 1644951 := bstep (se 1 (by rfl) ⟨1233713, by rfl⟩ : syracuseStep 1644951 = 2467427) B2467427
theorem B1644971 : Blo 1644021 1644971 := bstep (se 1 (by rfl) ⟨1233728, by rfl⟩ : syracuseStep 1644971 = 2467457) B2467457
theorem B1849783 : Blo 1644021 1849783 := bstep (se 1 (by rfl) ⟨1387337, by rfl⟩ : syracuseStep 1849783 = 2774675) B2774675
theorem B1644983 : Blo 1644021 1644983 := bstep (se 1 (by rfl) ⟨1233737, by rfl⟩ : syracuseStep 1644983 = 2467475) B2467475
theorem B6248897 : Blo 1644021 6248897 := bstep (se 2 (by rfl) ⟨2343336, by rfl⟩ : syracuseStep 6248897 = 4686673) B4686673
theorem B3701195 : Blo 1644021 3701195 := bstep (se 1 (by rfl) ⟨2775896, by rfl⟩ : syracuseStep 3701195 = 5551793) B5551793
theorem B1645003 : Blo 1644021 1645003 := bstep (se 1 (by rfl) ⟨1233752, by rfl⟩ : syracuseStep 1645003 = 2467505) B2467505
theorem B2963927 : Blo 1644021 2963927 := bstep (se 1 (by rfl) ⟨2222945, by rfl⟩ : syracuseStep 2963927 = 4445891) B4445891
theorem B1645015 : Blo 1644021 1645015 := bstep (se 1 (by rfl) ⟨1233761, by rfl⟩ : syracuseStep 1645015 = 2467523) B2467523
theorem B1645035 : Blo 1644021 1645035 := bstep (se 1 (by rfl) ⟨1233776, by rfl⟩ : syracuseStep 1645035 = 2467553) B2467553
theorem B1645047 : Blo 1644021 1645047 := bstep (se 1 (by rfl) ⟨1233785, by rfl⟩ : syracuseStep 1645047 = 2467571) B2467571
theorem B3701249 : Blo 1644021 3701249 := bstep (se 2 (by rfl) ⟨1387968, by rfl⟩ : syracuseStep 3701249 = 2775937) B2775937
theorem B1645067 : Blo 1644021 1645067 := bstep (se 1 (by rfl) ⟨1233800, by rfl⟩ : syracuseStep 1645067 = 2467601) B2467601
theorem B1645079 : Blo 1644021 1645079 := bstep (se 1 (by rfl) ⟨1233809, by rfl⟩ : syracuseStep 1645079 = 2467619) B2467619
theorem B1645099 : Blo 1644021 1645099 := bstep (se 1 (by rfl) ⟨1233824, by rfl⟩ : syracuseStep 1645099 = 2467649) B2467649
theorem B1645111 : Blo 1644021 1645111 := bstep (se 1 (by rfl) ⟨1233833, by rfl⟩ : syracuseStep 1645111 = 2467667) B2467667
theorem B1645131 : Blo 1644021 1645131 := bstep (se 1 (by rfl) ⟨1233848, by rfl⟩ : syracuseStep 1645131 = 2467697) B2467697
theorem B1645143 : Blo 1644021 1645143 := bstep (se 1 (by rfl) ⟨1233857, by rfl⟩ : syracuseStep 1645143 = 2467715) B2467715
theorem B1849963 : Blo 1644021 1849963 := bstep (se 1 (by rfl) ⟨1387472, by rfl⟩ : syracuseStep 1849963 = 2774945) B2774945
theorem B1645163 : Blo 1644021 1645163 := bstep (se 1 (by rfl) ⟨1233872, by rfl⟩ : syracuseStep 1645163 = 2467745) B2467745
theorem B1645175 : Blo 1644021 1645175 := bstep (se 1 (by rfl) ⟨1233881, by rfl⟩ : syracuseStep 1645175 = 2467763) B2467763
theorem B1645195 : Blo 1644021 1645195 := bstep (se 1 (by rfl) ⟨1233896, by rfl⟩ : syracuseStep 1645195 = 2467793) B2467793
theorem B1645207 : Blo 1644021 1645207 := bstep (se 1 (by rfl) ⟨1233905, by rfl⟩ : syracuseStep 1645207 = 2467811) B2467811
theorem B1645227 : Blo 1644021 1645227 := bstep (se 1 (by rfl) ⟨1233920, by rfl⟩ : syracuseStep 1645227 = 2467841) B2467841
theorem B5552819 : Blo 1644021 5552819 := bstep (se 1 (by rfl) ⟨4164614, by rfl⟩ : syracuseStep 5552819 = 8329229) B8329229
theorem B1645239 : Blo 1644021 1645239 := bstep (se 1 (by rfl) ⟨1233929, by rfl⟩ : syracuseStep 1645239 = 2467859) B2467859
theorem B2775755 : Blo 1644021 2775755 := bstep (se 1 (by rfl) ⟨2081816, by rfl⟩ : syracuseStep 2775755 = 4163633) B4163633
theorem B1645259 : Blo 1644021 1645259 := bstep (se 1 (by rfl) ⟨1233944, by rfl⟩ : syracuseStep 1645259 = 2467889) B2467889
theorem B1850071 : Blo 1644021 1850071 := bstep (se 1 (by rfl) ⟨1387553, by rfl⟩ : syracuseStep 1850071 = 2775107) B2775107
theorem B1645271 : Blo 1644021 1645271 := bstep (se 1 (by rfl) ⟨1233953, by rfl⟩ : syracuseStep 1645271 = 2467907) B2467907
theorem B3701465 : Blo 1644021 3701465 := bstep (se 2 (by rfl) ⟨1388049, by rfl⟩ : syracuseStep 3701465 = 2776099) B2776099
theorem B10541785 : Blo 1644021 10541785 := bstep (se 2 (by rfl) ⟨3953169, by rfl⟩ : syracuseStep 10541785 = 7906339) B7906339
theorem B1645291 : Blo 1644021 1645291 := bstep (se 1 (by rfl) ⟨1233968, by rfl⟩ : syracuseStep 1645291 = 2467937) B2467937
theorem B1645303 : Blo 1644021 1645303 := bstep (se 1 (by rfl) ⟨1233977, by rfl⟩ : syracuseStep 1645303 = 2467955) B2467955
theorem B1645323 : Blo 1644021 1645323 := bstep (se 1 (by rfl) ⟨1233992, by rfl⟩ : syracuseStep 1645323 = 2467985) B2467985
theorem B1645335 : Blo 1644021 1645335 := bstep (se 1 (by rfl) ⟨1234001, by rfl⟩ : syracuseStep 1645335 = 2468003) B2468003
theorem B1645355 : Blo 1644021 1645355 := bstep (se 1 (by rfl) ⟨1234016, by rfl⟩ : syracuseStep 1645355 = 2468033) B2468033
theorem B3701555 : Blo 1644021 3701555 := bstep (se 1 (by rfl) ⟨2776166, by rfl⟩ : syracuseStep 3701555 = 5552333) B5552333
theorem B1645367 : Blo 1644021 1645367 := bstep (se 1 (by rfl) ⟨1234025, by rfl⟩ : syracuseStep 1645367 = 2468051) B2468051
theorem B2775883 : Blo 1644021 2775883 := bstep (se 1 (by rfl) ⟨2081912, by rfl⟩ : syracuseStep 2775883 = 4163825) B4163825
theorem B1645387 : Blo 1644021 1645387 := bstep (se 1 (by rfl) ⟨1234040, by rfl⟩ : syracuseStep 1645387 = 2468081) B2468081
theorem B3701591 : Blo 1644021 3701591 := bstep (se 1 (by rfl) ⟨2776193, by rfl⟩ : syracuseStep 3701591 = 5552387) B5552387
theorem B1645399 : Blo 1644021 1645399 := bstep (se 1 (by rfl) ⟨1234049, by rfl⟩ : syracuseStep 1645399 = 2468099) B2468099
theorem B3521369 : Blo 1644021 3521369 := bstep (se 2 (by rfl) ⟨1320513, by rfl⟩ : syracuseStep 3521369 = 2641027) B2641027
theorem B1645419 : Blo 1644021 1645419 := bstep (se 1 (by rfl) ⟨1234064, by rfl⟩ : syracuseStep 1645419 = 2468129) B2468129
theorem B3513203 : Blo 1644021 3513203 := bstep (se 1 (by rfl) ⟨2634902, by rfl⟩ : syracuseStep 3513203 = 5269805) B5269805
theorem B1645431 : Blo 1644021 1645431 := bstep (se 1 (by rfl) ⟨1234073, by rfl⟩ : syracuseStep 1645431 = 2468147) B2468147
theorem B1850251 : Blo 1644021 1850251 := bstep (se 1 (by rfl) ⟨1387688, by rfl⟩ : syracuseStep 1850251 = 2775377) B2775377
theorem B1645451 : Blo 1644021 1645451 := bstep (se 1 (by rfl) ⟨1234088, by rfl⟩ : syracuseStep 1645451 = 2468177) B2468177
theorem B1645463 : Blo 1644021 1645463 := bstep (se 1 (by rfl) ⟨1234097, by rfl⟩ : syracuseStep 1645463 = 2468195) B2468195
theorem B3562393 : Blo 1644021 3562393 := bstep (se 2 (by rfl) ⟨1335897, by rfl⟩ : syracuseStep 3562393 = 2671795) B2671795
theorem B1645483 : Blo 1644021 1645483 := bstep (se 1 (by rfl) ⟨1234112, by rfl⟩ : syracuseStep 1645483 = 2468225) B2468225
theorem B1645495 : Blo 1644021 1645495 := bstep (se 1 (by rfl) ⟨1234121, by rfl⟩ : syracuseStep 1645495 = 2468243) B2468243
theorem B5553089 : Blo 1644021 5553089 := bstep (se 2 (by rfl) ⟨2082408, by rfl⟩ : syracuseStep 5553089 = 4164817) B4164817
theorem B1645515 : Blo 1644021 1645515 := bstep (se 1 (by rfl) ⟨1234136, by rfl⟩ : syracuseStep 1645515 = 2468273) B2468273
theorem B1645527 : Blo 1644021 1645527 := bstep (se 1 (by rfl) ⟨1234145, by rfl⟩ : syracuseStep 1645527 = 2468291) B2468291
theorem B2776025 : Blo 1644021 2776025 := bstep (se 2 (by rfl) ⟨1041009, by rfl⟩ : syracuseStep 2776025 = 2082019) B2082019
theorem B8330201 : Blo 1644021 8330201 := bstep (se 2 (by rfl) ⟨3123825, by rfl⟩ : syracuseStep 8330201 = 6247651) B6247651
theorem B1645547 : Blo 1644021 1645547 := bstep (se 1 (by rfl) ⟨1234160, by rfl⟩ : syracuseStep 1645547 = 2468321) B2468321
theorem B1850359 : Blo 1644021 1850359 := bstep (se 1 (by rfl) ⟨1387769, by rfl⟩ : syracuseStep 1850359 = 2775539) B2775539
theorem B1645559 : Blo 1644021 1645559 := bstep (se 1 (by rfl) ⟨1234169, by rfl⟩ : syracuseStep 1645559 = 2468339) B2468339
theorem B3701771 : Blo 1644021 3701771 := bstep (se 1 (by rfl) ⟨2776328, by rfl⟩ : syracuseStep 3701771 = 5552657) B5552657
theorem B1645579 : Blo 1644021 1645579 := bstep (se 1 (by rfl) ⟨1234184, by rfl⟩ : syracuseStep 1645579 = 2468369) B2468369
theorem B21077009 : Blo 1644021 21077009 := bstep (se 2 (by rfl) ⟨7903878, by rfl⟩ : syracuseStep 21077009 = 15807757) B15807757
theorem B1645591 : Blo 1644021 1645591 := bstep (se 1 (by rfl) ⟨1234193, by rfl⟩ : syracuseStep 1645591 = 2468387) B2468387
theorem B1645611 : Blo 1644021 1645611 := bstep (se 1 (by rfl) ⟨1234208, by rfl⟩ : syracuseStep 1645611 = 2468417) B2468417
theorem B6667309 : Blo 1644021 6667309 := bstep (se 3 (by rfl) ⟨1250120, by rfl⟩ : syracuseStep 6667309 = 2500241) B2500241
theorem B1645623 : Blo 1644021 1645623 := bstep (se 1 (by rfl) ⟨1234217, by rfl⟩ : syracuseStep 1645623 = 2468435) B2468435
theorem B3701825 : Blo 1644021 3701825 := bstep (se 2 (by rfl) ⟨1388184, by rfl⟩ : syracuseStep 3701825 = 2776369) B2776369
theorem B1645643 : Blo 1644021 1645643 := bstep (se 1 (by rfl) ⟨1234232, by rfl⟩ : syracuseStep 1645643 = 2468465) B2468465
theorem B1645655 : Blo 1644021 1645655 := bstep (se 1 (by rfl) ⟨1234241, by rfl⟩ : syracuseStep 1645655 = 2468483) B2468483
theorem B2776153 : Blo 1644021 2776153 := bstep (se 2 (by rfl) ⟨1041057, by rfl⟩ : syracuseStep 2776153 = 2082115) B2082115
theorem B10001501 : Blo 1644021 10001501 := bstep (se 3 (by rfl) ⟨1875281, by rfl⟩ : syracuseStep 10001501 = 3750563) B3750563
theorem B1645675 : Blo 1644021 1645675 := bstep (se 1 (by rfl) ⟨1234256, by rfl⟩ : syracuseStep 1645675 = 2468513) B2468513
theorem B1645687 : Blo 1644021 1645687 := bstep (se 1 (by rfl) ⟨1234265, by rfl⟩ : syracuseStep 1645687 = 2468531) B2468531
theorem B1645707 : Blo 1644021 1645707 := bstep (se 1 (by rfl) ⟨1234280, by rfl⟩ : syracuseStep 1645707 = 2468561) B2468561
theorem B1645719 : Blo 1644021 1645719 := bstep (se 1 (by rfl) ⟨1234289, by rfl⟩ : syracuseStep 1645719 = 2468579) B2468579
theorem B1850539 : Blo 1644021 1850539 := bstep (se 1 (by rfl) ⟨1387904, by rfl⟩ : syracuseStep 1850539 = 2775809) B2775809
theorem B1645739 : Blo 1644021 1645739 := bstep (se 1 (by rfl) ⟨1234304, by rfl⟩ : syracuseStep 1645739 = 2468609) B2468609
theorem B1645751 : Blo 1644021 1645751 := bstep (se 1 (by rfl) ⟨1234313, by rfl⟩ : syracuseStep 1645751 = 2468627) B2468627
theorem B1645771 : Blo 1644021 1645771 := bstep (se 1 (by rfl) ⟨1234328, by rfl⟩ : syracuseStep 1645771 = 2468657) B2468657
theorem B1645783 : Blo 1644021 1645783 := bstep (se 1 (by rfl) ⟨1234337, by rfl⟩ : syracuseStep 1645783 = 2468675) B2468675
theorem B1645803 : Blo 1644021 1645803 := bstep (se 1 (by rfl) ⟨1234352, by rfl⟩ : syracuseStep 1645803 = 2468705) B2468705
theorem B1645815 : Blo 1644021 1645815 := bstep (se 1 (by rfl) ⟨1234361, by rfl⟩ : syracuseStep 1645815 = 2468723) B2468723
theorem B1645835 : Blo 1644021 1645835 := bstep (se 1 (by rfl) ⟨1234376, by rfl⟩ : syracuseStep 1645835 = 2468753) B2468753
theorem B1850647 : Blo 1644021 1850647 := bstep (se 1 (by rfl) ⟨1387985, by rfl⟩ : syracuseStep 1850647 = 2775971) B2775971
theorem B1645847 : Blo 1644021 1645847 := bstep (se 1 (by rfl) ⟨1234385, by rfl⟩ : syracuseStep 1645847 = 2468771) B2468771
theorem B3702041 : Blo 1644021 3702041 := bstep (se 2 (by rfl) ⟨1388265, by rfl⟩ : syracuseStep 3702041 = 2776531) B2776531
theorem B14056739 : Blo 1644021 14056739 := bstep (se 1 (by rfl) ⟨10542554, by rfl⟩ : syracuseStep 14056739 = 21085109) B21085109
theorem B1645867 : Blo 1644021 1645867 := bstep (se 1 (by rfl) ⟨1234400, by rfl⟩ : syracuseStep 1645867 = 2468801) B2468801
theorem B8117549 : Blo 1644021 8117549 := bstep (se 3 (by rfl) ⟨1522040, by rfl⟩ : syracuseStep 8117549 = 3044081) B3044081
theorem B6667571 : Blo 1644021 6667571 := bstep (se 1 (by rfl) ⟨5000678, by rfl⟩ : syracuseStep 6667571 = 10001357) B10001357
theorem B1645879 : Blo 1644021 1645879 := bstep (se 1 (by rfl) ⟨1234409, by rfl⟩ : syracuseStep 1645879 = 2468819) B2468819
theorem B1645899 : Blo 1644021 1645899 := bstep (se 1 (by rfl) ⟨1234424, by rfl⟩ : syracuseStep 1645899 = 2468849) B2468849
theorem B1645911 : Blo 1644021 1645911 := bstep (se 1 (by rfl) ⟨1234433, by rfl⟩ : syracuseStep 1645911 = 2468867) B2468867
theorem B12016997 : Blo 1644021 12016997 := bstep (se 4 (by rfl) ⟨1126593, by rfl⟩ : syracuseStep 12016997 = 2253187) B2253187
theorem B1645931 : Blo 1644021 1645931 := bstep (se 1 (by rfl) ⟨1234448, by rfl⟩ : syracuseStep 1645931 = 2468897) B2468897
theorem B3702131 : Blo 1644021 3702131 := bstep (se 1 (by rfl) ⟨2776598, by rfl⟩ : syracuseStep 3702131 = 5553197) B5553197
theorem B1645943 : Blo 1644021 1645943 := bstep (se 1 (by rfl) ⟨1234457, by rfl⟩ : syracuseStep 1645943 = 2468915) B2468915
theorem B1645963 : Blo 1644021 1645963 := bstep (se 1 (by rfl) ⟨1234472, by rfl⟩ : syracuseStep 1645963 = 2468945) B2468945
theorem B3702167 : Blo 1644021 3702167 := bstep (se 1 (by rfl) ⟨2776625, by rfl⟩ : syracuseStep 3702167 = 5553251) B5553251
theorem B1645975 : Blo 1644021 1645975 := bstep (se 1 (by rfl) ⟨1234481, by rfl⟩ : syracuseStep 1645975 = 2468963) B2468963
theorem B1645995 : Blo 1644021 1645995 := bstep (se 1 (by rfl) ⟨1234496, by rfl⟩ : syracuseStep 1645995 = 2468993) B2468993
theorem B1646007 : Blo 1644021 1646007 := bstep (se 1 (by rfl) ⟨1234505, by rfl⟩ : syracuseStep 1646007 = 2469011) B2469011
theorem B1850827 : Blo 1644021 1850827 := bstep (se 1 (by rfl) ⟨1388120, by rfl⟩ : syracuseStep 1850827 = 2776241) B2776241
theorem B4685273 : Blo 1644021 4685273 := bstep (se 2 (by rfl) ⟨1756977, by rfl⟩ : syracuseStep 4685273 = 3513955) B3513955
theorem B4447705 : Blo 1644021 4447705 := bstep (se 2 (by rfl) ⟨1667889, by rfl⟩ : syracuseStep 4447705 = 3335779) B3335779
theorem B5553629 : Blo 1644021 5553629 := bstep (se 3 (by rfl) ⟨1041305, by rfl⟩ : syracuseStep 5553629 = 2082611) B2082611
theorem B15810065 : Blo 1644021 15810065 := bstep (se 2 (by rfl) ⟨5928774, by rfl⟩ : syracuseStep 15810065 = 11857549) B11857549
theorem B1850935 : Blo 1644021 1850935 := bstep (se 1 (by rfl) ⟨1388201, by rfl⟩ : syracuseStep 1850935 = 2776403) B2776403
theorem B3702347 : Blo 1644021 3702347 := bstep (se 1 (by rfl) ⟨2776760, by rfl⟩ : syracuseStep 3702347 = 5553521) B5553521
theorem B3702401 : Blo 1644021 3702401 := bstep (se 2 (by rfl) ⟨1388400, by rfl⟩ : syracuseStep 3702401 = 2776801) B2776801
theorem B9494147 : Blo 1644021 9494147 := bstep (se 1 (by rfl) ⟨7120610, by rfl⟩ : syracuseStep 9494147 = 14241221) B14241221
theorem B31620739 : Blo 1644021 31620739 := bstep (se 1 (by rfl) ⟨23715554, by rfl⟩ : syracuseStep 31620739 = 47431109) B47431109
theorem B18726551 : Blo 1644021 18726551 := bstep (se 1 (by rfl) ⟨14044913, by rfl⟩ : syracuseStep 18726551 = 28089827) B28089827
theorem B2776727 : Blo 1644021 2776727 := bstep (se 1 (by rfl) ⟨2082545, by rfl⟩ : syracuseStep 2776727 = 4165091) B4165091
theorem B1851115 : Blo 1644021 1851115 := bstep (se 1 (by rfl) ⟨1388336, by rfl⟩ : syracuseStep 1851115 = 2776673) B2776673
theorem B3514099 : Blo 1644021 3514099 := bstep (se 1 (by rfl) ⟨2635574, by rfl⟩ : syracuseStep 3514099 = 5271149) B5271149
theorem B3333899 : Blo 1644021 3333899 := bstep (se 1 (by rfl) ⟨2500424, by rfl⟩ : syracuseStep 3333899 = 5000849) B5000849
theorem B2776855 : Blo 1644021 2776855 := bstep (se 1 (by rfl) ⟨2082641, by rfl⟩ : syracuseStep 2776855 = 4165283) B4165283
theorem B7126859 : Blo 1644021 7126859 := bstep (se 1 (by rfl) ⟨5345144, by rfl⟩ : syracuseStep 7126859 = 10690289) B10690289
theorem B1851223 : Blo 1644021 1851223 := bstep (se 1 (by rfl) ⟨1388417, by rfl⟩ : syracuseStep 1851223 = 2776835) B2776835
theorem B3702617 : Blo 1644021 3702617 := bstep (se 2 (by rfl) ⟨1388481, by rfl⟩ : syracuseStep 3702617 = 2776963) B2776963
theorem B21356465 : Blo 1644021 21356465 := bstep (se 2 (by rfl) ⟨8008674, by rfl⟩ : syracuseStep 21356465 = 16017349) B16017349
theorem B3702707 : Blo 1644021 3702707 := bstep (se 1 (by rfl) ⟨2777030, by rfl⟩ : syracuseStep 3702707 = 5554061) B5554061
theorem B3702743 : Blo 1644021 3702743 := bstep (se 1 (by rfl) ⟨2777057, by rfl⟩ : syracuseStep 3702743 = 5554115) B5554115
theorem B9371659 : Blo 1644021 9371659 := bstep (se 1 (by rfl) ⟨7028744, by rfl⟩ : syracuseStep 9371659 = 14057489) B14057489
theorem B8888363 : Blo 1644021 8888363 := bstep (se 1 (by rfl) ⟨6666272, by rfl⟩ : syracuseStep 8888363 = 13332545) B13332545
theorem B4161689 : Blo 1644021 4161689 := bstep (se 2 (by rfl) ⟨1560633, by rfl⟩ : syracuseStep 4161689 = 3121267) B3121267
theorem B2343097 : Blo 1644021 2343097 := bstep (se 2 (by rfl) ⟨878661, by rfl⟩ : syracuseStep 2343097 = 1757323) B1757323
theorem B1851655 : Blo 1644021 1851655 := bstep (se 1 (by rfl) ⟨1388741, by rfl⟩ : syracuseStep 1851655 = 2777483) B2777483
theorem B2466107 : Blo 1644021 2466107 := bstep (se 1 (by rfl) ⟨1849580, by rfl⟩ : syracuseStep 2466107 = 3699161) B3699161
theorem B4161851 : Blo 1644021 4161851 := bstep (se 1 (by rfl) ⟨3121388, by rfl⟩ : syracuseStep 4161851 = 6242777) B6242777
theorem B12493115 : Blo 1644021 12493115 := bstep (se 1 (by rfl) ⟨9369836, by rfl⟩ : syracuseStep 12493115 = 18739673) B18739673
theorem B5554547 : Blo 1644021 5554547 := bstep (se 1 (by rfl) ⟨4165910, by rfl⟩ : syracuseStep 5554547 = 8331821) B8331821
theorem B2466167 : Blo 1644021 2466167 := bstep (se 1 (by rfl) ⟨1849625, by rfl⟩ : syracuseStep 2466167 = 3699251) B3699251
theorem B2081143 : Blo 1644021 2081143 := bstep (se 1 (by rfl) ⟨1560857, by rfl⟩ : syracuseStep 2081143 = 3121715) B3121715
theorem B3703175 : Blo 1644021 3703175 := bstep (se 1 (by rfl) ⟨2777381, by rfl⟩ : syracuseStep 3703175 = 5554763) B5554763
theorem B2466191 : Blo 1644021 2466191 := bstep (se 1 (by rfl) ⟨1849643, by rfl⟩ : syracuseStep 2466191 = 3699287) B3699287
theorem B7029139 : Blo 1644021 7029139 := bstep (se 1 (by rfl) ⟨5271854, by rfl⟩ : syracuseStep 7029139 = 10543709) B10543709
theorem B2466233 : Blo 1644021 2466233 := bstep (se 2 (by rfl) ⟨924837, by rfl⟩ : syracuseStep 2466233 = 1849675) B1849675
theorem B2466311 : Blo 1644021 2466311 := bstep (se 1 (by rfl) ⟨1849733, by rfl⟩ : syracuseStep 2466311 = 3699467) B3699467
theorem B4162063 : Blo 1644021 4162063 := bstep (se 1 (by rfl) ⟨3121547, by rfl⟩ : syracuseStep 4162063 = 6243095) B6243095
theorem B2343439 : Blo 1644021 2343439 := bstep (se 1 (by rfl) ⟨1757579, by rfl⟩ : syracuseStep 2343439 = 3515159) B3515159
theorem B2466347 : Blo 1644021 2466347 := bstep (se 1 (by rfl) ⟨1849760, by rfl⟩ : syracuseStep 2466347 = 3699521) B3699521
theorem B3703355 : Blo 1644021 3703355 := bstep (se 1 (by rfl) ⟨2777516, by rfl⟩ : syracuseStep 3703355 = 5555033) B5555033
theorem B2466377 : Blo 1644021 2466377 := bstep (se 2 (by rfl) ⟨924891, by rfl⟩ : syracuseStep 2466377 = 1849783) B1849783
theorem B3703481 : Blo 1644021 3703481 := bstep (se 2 (by rfl) ⟨1388805, by rfl⟩ : syracuseStep 3703481 = 2777611) B2777611
theorem B2466491 : Blo 1644021 2466491 := bstep (se 1 (by rfl) ⟨1849868, by rfl⟩ : syracuseStep 2466491 = 3699737) B3699737
theorem B2081467 : Blo 1644021 2081467 := bstep (se 1 (by rfl) ⟨1561100, by rfl⟩ : syracuseStep 2081467 = 3122201) B3122201
theorem B2466551 : Blo 1644021 2466551 := bstep (se 1 (by rfl) ⟨1849913, by rfl⟩ : syracuseStep 2466551 = 3699827) B3699827
theorem B2466575 : Blo 1644021 2466575 := bstep (se 1 (by rfl) ⟨1849931, by rfl⟩ : syracuseStep 2466575 = 3699863) B3699863
theorem B4162337 : Blo 1644021 4162337 := bstep (se 2 (by rfl) ⟨1560876, by rfl⟩ : syracuseStep 4162337 = 3121753) B3121753
theorem B2466617 : Blo 1644021 2466617 := bstep (se 2 (by rfl) ⟨924981, by rfl⟩ : syracuseStep 2466617 = 1849963) B1849963
theorem B2466695 : Blo 1644021 2466695 := bstep (se 1 (by rfl) ⟨1850021, by rfl⟩ : syracuseStep 2466695 = 3700043) B3700043
theorem B9364369 : Blo 1644021 9364369 := bstep (se 2 (by rfl) ⟨3511638, by rfl⟩ : syracuseStep 9364369 = 7023277) B7023277
theorem B2466731 : Blo 1644021 2466731 := bstep (se 1 (by rfl) ⟨1850048, by rfl⟩ : syracuseStep 2466731 = 3700097) B3700097
theorem B2466761 : Blo 1644021 2466761 := bstep (se 2 (by rfl) ⟨925035, by rfl⟩ : syracuseStep 2466761 = 1850071) B1850071
theorem B2466875 : Blo 1644021 2466875 := bstep (se 1 (by rfl) ⟨1850156, by rfl⟩ : syracuseStep 2466875 = 3700313) B3700313
theorem B2466935 : Blo 1644021 2466935 := bstep (se 1 (by rfl) ⟨1850201, by rfl⟩ : syracuseStep 2466935 = 3700403) B3700403
theorem B2466959 : Blo 1644021 2466959 := bstep (se 1 (by rfl) ⟨1850219, by rfl⟩ : syracuseStep 2466959 = 3700439) B3700439
theorem B2081963 : Blo 1644021 2081963 := bstep (se 1 (by rfl) ⟨1561472, by rfl⟩ : syracuseStep 2081963 = 3122945) B3122945
theorem B2467001 : Blo 1644021 2467001 := bstep (se 2 (by rfl) ⟨925125, by rfl⟩ : syracuseStep 2467001 = 1850251) B1850251
theorem B2467079 : Blo 1644021 2467079 := bstep (se 1 (by rfl) ⟨1850309, by rfl⟩ : syracuseStep 2467079 = 3700619) B3700619
theorem B2467115 : Blo 1644021 2467115 := bstep (se 1 (by rfl) ⟨1850336, by rfl⟩ : syracuseStep 2467115 = 3700673) B3700673
theorem B2467145 : Blo 1644021 2467145 := bstep (se 2 (by rfl) ⟨925179, by rfl⟩ : syracuseStep 2467145 = 1850359) B1850359
theorem B3753335 : Blo 1644021 3753335 := bstep (se 1 (by rfl) ⟨2815001, by rfl⟩ : syracuseStep 3753335 = 5630003) B5630003
theorem B8889745 : Blo 1644021 8889745 := bstep (se 2 (by rfl) ⟨3333654, by rfl⟩ : syracuseStep 8889745 = 6667309) B6667309
theorem B2467259 : Blo 1644021 2467259 := bstep (se 1 (by rfl) ⟨1850444, by rfl⟩ : syracuseStep 2467259 = 3700889) B3700889
theorem B2467319 : Blo 1644021 2467319 := bstep (se 1 (by rfl) ⟨1850489, by rfl⟩ : syracuseStep 2467319 = 3700979) B3700979
theorem B2467343 : Blo 1644021 2467343 := bstep (se 1 (by rfl) ⟨1850507, by rfl⟩ : syracuseStep 2467343 = 3701015) B3701015
theorem B2467385 : Blo 1644021 2467385 := bstep (se 2 (by rfl) ⟨925269, by rfl⟩ : syracuseStep 2467385 = 1850539) B1850539
theorem B2467463 : Blo 1644021 2467463 := bstep (se 1 (by rfl) ⟨1850597, by rfl⟩ : syracuseStep 2467463 = 3701195) B3701195
theorem B2082439 : Blo 1644021 2082439 := bstep (se 1 (by rfl) ⟨1561829, by rfl⟩ : syracuseStep 2082439 = 3123659) B3123659
theorem B1975951 : Blo 1644021 1975951 := bstep (se 1 (by rfl) ⟨1481963, by rfl⟩ : syracuseStep 1975951 = 2963927) B2963927
theorem B2467499 : Blo 1644021 2467499 := bstep (se 1 (by rfl) ⟨1850624, by rfl⟩ : syracuseStep 2467499 = 3701249) B3701249
theorem B2467529 : Blo 1644021 2467529 := bstep (se 2 (by rfl) ⟨925323, by rfl⟩ : syracuseStep 2467529 = 1850647) B1850647
theorem B4163339 : Blo 1644021 4163339 := bstep (se 1 (by rfl) ⟨3122504, by rfl⟩ : syracuseStep 4163339 = 6245009) B6245009
theorem B9013007 : Blo 1644021 9013007 := bstep (se 1 (by rfl) ⟨6759755, by rfl⟩ : syracuseStep 9013007 = 13519511) B13519511
theorem B2467643 : Blo 1644021 2467643 := bstep (se 1 (by rfl) ⟨1850732, by rfl⟩ : syracuseStep 2467643 = 3701465) B3701465
theorem B23709509 : Blo 1644021 23709509 := bstep (se 4 (by rfl) ⟨2222766, by rfl⟩ : syracuseStep 23709509 = 4445533) B4445533
theorem B2467703 : Blo 1644021 2467703 := bstep (se 1 (by rfl) ⟨1850777, by rfl⟩ : syracuseStep 2467703 = 3701555) B3701555
theorem B2467727 : Blo 1644021 2467727 := bstep (se 1 (by rfl) ⟨1850795, by rfl⟩ : syracuseStep 2467727 = 3701591) B3701591
theorem B8325017 : Blo 1644021 8325017 := bstep (se 2 (by rfl) ⟨3121881, by rfl⟩ : syracuseStep 8325017 = 6243763) B6243763
theorem B6244249 : Blo 1644021 6244249 := bstep (se 2 (by rfl) ⟨2341593, by rfl⟩ : syracuseStep 6244249 = 4683187) B4683187
theorem B2467769 : Blo 1644021 2467769 := bstep (se 2 (by rfl) ⟨925413, by rfl⟩ : syracuseStep 2467769 = 1850827) B1850827
theorem B9373643 : Blo 1644021 9373643 := bstep (se 1 (by rfl) ⟨7030232, by rfl⟩ : syracuseStep 9373643 = 14060465) B14060465
theorem B2467847 : Blo 1644021 2467847 := bstep (se 1 (by rfl) ⟨1850885, by rfl⟩ : syracuseStep 2467847 = 3701771) B3701771
theorem B14051339 : Blo 1644021 14051339 := bstep (se 1 (by rfl) ⟨10538504, by rfl⟩ : syracuseStep 14051339 = 21077009) B21077009
theorem B33785869 : Blo 1644021 33785869 := bstep (se 3 (by rfl) ⟨6334850, by rfl⟩ : syracuseStep 33785869 = 12669701) B12669701
theorem B7030795 : Blo 1644021 7030795 := bstep (se 1 (by rfl) ⟨5273096, by rfl⟩ : syracuseStep 7030795 = 10546193) B10546193
theorem B8890397 : Blo 1644021 8890397 := bstep (se 3 (by rfl) ⟨1666949, by rfl⟩ : syracuseStep 8890397 = 3333899) B3333899
theorem B2467883 : Blo 1644021 2467883 := bstep (se 1 (by rfl) ⟨1850912, by rfl⟩ : syracuseStep 2467883 = 3701825) B3701825
theorem B11855933 : Blo 1644021 11855933 := bstep (se 3 (by rfl) ⟨2222987, by rfl⟩ : syracuseStep 11855933 = 4445975) B4445975
theorem B2467913 : Blo 1644021 2467913 := bstep (se 2 (by rfl) ⟨925467, by rfl⟩ : syracuseStep 2467913 = 1850935) B1850935
theorem B2082935 : Blo 1644021 2082935 := bstep (se 1 (by rfl) ⟨1562201, by rfl⟩ : syracuseStep 2082935 = 3124403) B3124403
theorem B2468027 : Blo 1644021 2468027 := bstep (se 1 (by rfl) ⟨1851020, by rfl⟩ : syracuseStep 2468027 = 3702041) B3702041
theorem B6244553 : Blo 1644021 6244553 := bstep (se 2 (by rfl) ⟨2341707, by rfl⟩ : syracuseStep 6244553 = 4683415) B4683415
theorem B2468087 : Blo 1644021 2468087 := bstep (se 1 (by rfl) ⟨1851065, by rfl⟩ : syracuseStep 2468087 = 3702131) B3702131
theorem B2468111 : Blo 1644021 2468111 := bstep (se 1 (by rfl) ⟨1851083, by rfl⟩ : syracuseStep 2468111 = 3702167) B3702167
theorem B2083087 : Blo 1644021 2083087 := bstep (se 1 (by rfl) ⟨1562315, by rfl⟩ : syracuseStep 2083087 = 3124631) B3124631
theorem B2468153 : Blo 1644021 2468153 := bstep (se 2 (by rfl) ⟨925557, by rfl⟩ : syracuseStep 2468153 = 1851115) B1851115
theorem B3123515 : Blo 1644021 3123515 := bstep (se 1 (by rfl) ⟨2342636, by rfl⟩ : syracuseStep 3123515 = 4685273) B4685273
theorem B2468231 : Blo 1644021 2468231 := bstep (se 1 (by rfl) ⟨1851173, by rfl⟩ : syracuseStep 2468231 = 3702347) B3702347
theorem B4163987 : Blo 1644021 4163987 := bstep (se 1 (by rfl) ⟨3122990, by rfl⟩ : syracuseStep 4163987 = 6245981) B6245981
theorem B5343641 : Blo 1644021 5343641 := bstep (se 2 (by rfl) ⟨2003865, by rfl⟩ : syracuseStep 5343641 = 4007731) B4007731
theorem B2468267 : Blo 1644021 2468267 := bstep (se 1 (by rfl) ⟨1851200, by rfl⟩ : syracuseStep 2468267 = 3702401) B3702401
theorem B2468297 : Blo 1644021 2468297 := bstep (se 2 (by rfl) ⟨925611, by rfl⟩ : syracuseStep 2468297 = 1851223) B1851223
theorem B2468411 : Blo 1644021 2468411 := bstep (se 1 (by rfl) ⟨1851308, by rfl⟩ : syracuseStep 2468411 = 3702617) B3702617
theorem B2468471 : Blo 1644021 2468471 := bstep (se 1 (by rfl) ⟨1851353, by rfl⟩ : syracuseStep 2468471 = 3702707) B3702707
theorem B2468495 : Blo 1644021 2468495 := bstep (se 1 (by rfl) ⟨1851371, by rfl⟩ : syracuseStep 2468495 = 3702743) B3702743
theorem B4164281 : Blo 1644021 4164281 := bstep (se 2 (by rfl) ⟨1561605, by rfl⟩ : syracuseStep 4164281 = 3123211) B3123211
theorem B2468537 : Blo 1644021 2468537 := bstep (se 2 (by rfl) ⟨925701, by rfl⟩ : syracuseStep 2468537 = 1851403) B1851403
theorem B2468615 : Blo 1644021 2468615 := bstep (se 1 (by rfl) ⟨1851461, by rfl⟩ : syracuseStep 2468615 = 3702923) B3702923
theorem B4279051 : Blo 1644021 4279051 := bstep (se 1 (by rfl) ⟨3209288, by rfl⟩ : syracuseStep 4279051 = 6418577) B6418577
theorem B3124001 : Blo 1644021 3124001 := bstep (se 2 (by rfl) ⟨1171500, by rfl⟩ : syracuseStep 3124001 = 2343001) B2343001
theorem B2468651 : Blo 1644021 2468651 := bstep (se 1 (by rfl) ⟨1851488, by rfl⟩ : syracuseStep 2468651 = 3702977) B3702977
theorem B2468681 : Blo 1644021 2468681 := bstep (se 2 (by rfl) ⟨925755, by rfl⟩ : syracuseStep 2468681 = 1851511) B1851511
theorem B7908185 : Blo 1644021 7908185 := bstep (se 2 (by rfl) ⟨2965569, by rfl⟩ : syracuseStep 7908185 = 5931139) B5931139
theorem B81095539 : Blo 1644021 81095539 := bstep (se 1 (by rfl) ⟨60821654, by rfl⟩ : syracuseStep 81095539 = 121643309) B121643309
theorem B3951479 : Blo 1644021 3951479 := bstep (se 1 (by rfl) ⟨2963609, by rfl⟩ : syracuseStep 3951479 = 5927219) B5927219
theorem B2222983 : Blo 1644021 2222983 := bstep (se 1 (by rfl) ⟨1667237, by rfl⟩ : syracuseStep 2222983 = 3334475) B3334475
theorem B5548985 : Blo 1644021 5548985 := bstep (se 2 (by rfl) ⟨2080869, by rfl⟩ : syracuseStep 5548985 = 4161739) B4161739
theorem B2468795 : Blo 1644021 2468795 := bstep (se 1 (by rfl) ⟨1851596, by rfl⟩ : syracuseStep 2468795 = 3703193) B3703193
theorem B2468855 : Blo 1644021 2468855 := bstep (se 1 (by rfl) ⟨1851641, by rfl⟩ : syracuseStep 2468855 = 3703283) B3703283
theorem B2468879 : Blo 1644021 2468879 := bstep (se 1 (by rfl) ⟨1851659, by rfl⟩ : syracuseStep 2468879 = 3703319) B3703319
theorem B2501689 : Blo 1644021 2501689 := bstep (se 2 (by rfl) ⟨938133, by rfl⟩ : syracuseStep 2501689 = 1876267) B1876267
theorem B2468921 : Blo 1644021 2468921 := bstep (se 2 (by rfl) ⟨925845, by rfl⟩ : syracuseStep 2468921 = 1851691) B1851691
theorem B10538045 : Blo 1644021 10538045 := bstep (se 3 (by rfl) ⟨1975883, by rfl⟩ : syracuseStep 10538045 = 3951767) B3951767
theorem B6245495 : Blo 1644021 6245495 := bstep (se 1 (by rfl) ⟨4684121, by rfl⟩ : syracuseStep 6245495 = 9368243) B9368243
theorem B2468999 : Blo 1644021 2468999 := bstep (se 1 (by rfl) ⟨1851749, by rfl⟩ : syracuseStep 2468999 = 3703499) B3703499
theorem B9366785 : Blo 1644021 9366785 := bstep (se 2 (by rfl) ⟨3512544, by rfl⟩ : syracuseStep 9366785 = 7025089) B7025089
theorem B80031077 : Blo 1644021 80031077 := bstep (se 4 (by rfl) ⟨7502913, by rfl⟩ : syracuseStep 80031077 = 15005827) B15005827
theorem B4164979 : Blo 1644021 4164979 := bstep (se 1 (by rfl) ⟨3123734, by rfl⟩ : syracuseStep 4164979 = 6247469) B6247469
theorem B2223545 : Blo 1644021 2223545 := bstep (se 2 (by rfl) ⟨833829, by rfl⟩ : syracuseStep 2223545 = 1667659) B1667659
theorem B4165121 : Blo 1644021 4165121 := bstep (se 2 (by rfl) ⟨1561920, by rfl⟩ : syracuseStep 4165121 = 3123841) B3123841
theorem B5549579 : Blo 1644021 5549579 := bstep (se 1 (by rfl) ⟨4162184, by rfl⟩ : syracuseStep 5549579 = 8324369) B8324369
theorem B40578629 : Blo 1644021 40578629 := bstep (se 4 (by rfl) ⟨3804246, by rfl⟩ : syracuseStep 40578629 = 7608493) B7608493
theorem B5549687 : Blo 1644021 5549687 := bstep (se 1 (by rfl) ⟨4162265, by rfl⟩ : syracuseStep 5549687 = 8324531) B8324531
theorem B150245077 : Blo 1644021 150245077 := bstep (se 7 (by rfl) ⟨1760684, by rfl⟩ : syracuseStep 150245077 = 3521369) B3521369
theorem B30437093 : Blo 1644021 30437093 := bstep (se 4 (by rfl) ⟨2853477, by rfl⟩ : syracuseStep 30437093 = 5706955) B5706955
theorem B4165577 : Blo 1644021 4165577 := bstep (se 2 (by rfl) ⟨1562091, by rfl⟩ : syracuseStep 4165577 = 3124183) B3124183
theorem B10137565 : Blo 1644021 10137565 := bstep (se 3 (by rfl) ⟨1900793, by rfl⟩ : syracuseStep 10137565 = 3801587) B3801587
theorem B4681729 : Blo 1644021 4681729 := bstep (se 2 (by rfl) ⟨1755648, by rfl⟩ : syracuseStep 4681729 = 3511297) B3511297
theorem B63221795 : Blo 1644021 63221795 := bstep (se 1 (by rfl) ⟨47416346, by rfl⟩ : syracuseStep 63221795 = 94832693) B94832693
theorem B6246467 : Blo 1644021 6246467 := bstep (se 1 (by rfl) ⟨4684850, by rfl⟩ : syracuseStep 6246467 = 9369701) B9369701
theorem B5001335 : Blo 1644021 5001335 := bstep (se 1 (by rfl) ⟨3751001, by rfl⟩ : syracuseStep 5001335 = 7502003) B7502003
theorem B5550281 : Blo 1644021 5550281 := bstep (se 2 (by rfl) ⟨2081355, by rfl⟩ : syracuseStep 5550281 = 4162711) B4162711
theorem B84537589 : Blo 1644021 84537589 := bstep (se 5 (by rfl) ⟨3962699, by rfl⟩ : syracuseStep 84537589 = 7925399) B7925399
theorem B4165931 : Blo 1644021 4165931 := bstep (se 1 (by rfl) ⟨3124448, by rfl⟩ : syracuseStep 4165931 = 6248897) B6248897
theorem B8327609 : Blo 1644021 8327609 := bstep (se 2 (by rfl) ⟨3122853, by rfl⟩ : syracuseStep 8327609 = 6245707) B6245707
theorem B16028113 : Blo 1644021 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B13332995 : Blo 1644021 13332995 := bstep (se 1 (by rfl) ⟨9999746, by rfl⟩ : syracuseStep 13332995 = 19999493) B19999493
theorem B3699215 : Blo 1644021 3699215 := bstep (se 1 (by rfl) ⟨2774411, by rfl⟩ : syracuseStep 3699215 = 5548823) B5548823
theorem B3699233 : Blo 1644021 3699233 := bstep (se 2 (by rfl) ⟨1387212, by rfl⟩ : syracuseStep 3699233 = 2774425) B2774425
theorem B4682299 : Blo 1644021 4682299 := bstep (se 1 (by rfl) ⟨3511724, by rfl⟩ : syracuseStep 4682299 = 7023449) B7023449
theorem B5272265 : Blo 1644021 5272265 := bstep (se 2 (by rfl) ⟨1977099, by rfl⟩ : syracuseStep 5272265 = 3954199) B3954199
theorem B5272379 : Blo 1644021 5272379 := bstep (se 1 (by rfl) ⟨3954284, by rfl⟩ : syracuseStep 5272379 = 7908569) B7908569
theorem B42160985 : Blo 1644021 42160985 := bstep (se 2 (by rfl) ⟨15810369, by rfl⟩ : syracuseStep 42160985 = 31620739) B31620739
theorem B5411699 : Blo 1644021 5411699 := bstep (se 1 (by rfl) ⟨4058774, by rfl⟩ : syracuseStep 5411699 = 8117549) B8117549
theorem B3699575 : Blo 1644021 3699575 := bstep (se 1 (by rfl) ⟨2774681, by rfl⟩ : syracuseStep 3699575 = 5549363) B5549363
theorem B4445047 : Blo 1644021 4445047 := bstep (se 1 (by rfl) ⟨3333785, by rfl⟩ : syracuseStep 4445047 = 6667571) B6667571
theorem B5550983 : Blo 1644021 5550983 := bstep (se 1 (by rfl) ⟨4163237, by rfl⟩ : syracuseStep 5550983 = 8326475) B8326475
theorem B23704483 : Blo 1644021 23704483 := bstep (se 1 (by rfl) ⟨17778362, by rfl⟩ : syracuseStep 23704483 = 35556725) B35556725
theorem B2634697 : Blo 1644021 2634697 := bstep (se 2 (by rfl) ⟨988011, by rfl⟩ : syracuseStep 2634697 = 1976023) B1976023
theorem B18748421 : Blo 1644021 18748421 := bstep (se 4 (by rfl) ⟨1757664, by rfl⟩ : syracuseStep 18748421 = 3515329) B3515329
theorem B10540043 : Blo 1644021 10540043 := bstep (se 1 (by rfl) ⟨7905032, by rfl⟩ : syracuseStep 10540043 = 15810065) B15810065
theorem B3699755 : Blo 1644021 3699755 := bstep (se 1 (by rfl) ⟨2774816, by rfl⟩ : syracuseStep 3699755 = 5549633) B5549633
theorem B6329431 : Blo 1644021 6329431 := bstep (se 1 (by rfl) ⟨4747073, by rfl⟩ : syracuseStep 6329431 = 9494147) B9494147
theorem B67564631 : Blo 1644021 67564631 := bstep (se 1 (by rfl) ⟨50673473, by rfl⟩ : syracuseStep 67564631 = 101346947) B101346947
theorem B5551361 : Blo 1644021 5551361 := bstep (se 2 (by rfl) ⟨2081760, by rfl⟩ : syracuseStep 5551361 = 4163521) B4163521
theorem B3700115 : Blo 1644021 3700115 := bstep (se 1 (by rfl) ⟨2775086, by rfl⟩ : syracuseStep 3700115 = 5550173) B5550173
theorem B9369017 : Blo 1644021 9369017 := bstep (se 2 (by rfl) ⟨3513381, by rfl⟩ : syracuseStep 9369017 = 7026763) B7026763
theorem B3700169 : Blo 1644021 3700169 := bstep (se 2 (by rfl) ⟨1387563, by rfl⟩ : syracuseStep 3700169 = 2775127) B2775127
theorem B1644039 : Blo 1644021 1644039 := bstep (se 1 (by rfl) ⟨1233029, by rfl⟩ : syracuseStep 1644039 = 2466059) B2466059
theorem B1644047 : Blo 1644021 1644047 := bstep (se 1 (by rfl) ⟨1233035, by rfl⟩ : syracuseStep 1644047 = 2466071) B2466071
theorem B12498461 : Blo 1644021 12498461 := bstep (se 3 (by rfl) ⟨2343461, by rfl⟩ : syracuseStep 12498461 = 4686923) B4686923
theorem B1644091 : Blo 1644021 1644091 := bstep (se 1 (by rfl) ⟨1233068, by rfl⟩ : syracuseStep 1644091 = 2466137) B2466137
theorem B2774587 : Blo 1644021 2774587 := bstep (se 1 (by rfl) ⟨2080940, by rfl⟩ : syracuseStep 2774587 = 4161881) B4161881
theorem B15816293 : Blo 1644021 15816293 := bstep (se 4 (by rfl) ⟨1482777, by rfl⟩ : syracuseStep 15816293 = 2965555) B2965555
theorem B6010487 : Blo 1644021 6010487 := bstep (se 1 (by rfl) ⟨4507865, by rfl⟩ : syracuseStep 6010487 = 9015731) B9015731
theorem B1644167 : Blo 1644021 1644167 := bstep (se 1 (by rfl) ⟨1233125, by rfl⟩ : syracuseStep 1644167 = 2466251) B2466251
theorem B1644175 : Blo 1644021 1644175 := bstep (se 1 (by rfl) ⟨1233131, by rfl⟩ : syracuseStep 1644175 = 2466263) B2466263
theorem B26678963 : Blo 1644021 26678963 := bstep (se 1 (by rfl) ⟨20009222, by rfl⟩ : syracuseStep 26678963 = 40018445) B40018445
theorem B1644219 : Blo 1644021 1644219 := bstep (se 1 (by rfl) ⟨1233164, by rfl⟩ : syracuseStep 1644219 = 2466329) B2466329
theorem B2774729 : Blo 1644021 2774729 := bstep (se 2 (by rfl) ⟨1040523, by rfl⟩ : syracuseStep 2774729 = 2081047) B2081047
theorem B8328905 : Blo 1644021 8328905 := bstep (se 2 (by rfl) ⟨3123339, by rfl⟩ : syracuseStep 8328905 = 6246679) B6246679
theorem B6248137 : Blo 1644021 6248137 := bstep (se 2 (by rfl) ⟨2343051, by rfl⟩ : syracuseStep 6248137 = 4686103) B4686103
theorem B15013633 : Blo 1644021 15013633 := bstep (se 2 (by rfl) ⟨5630112, by rfl⟩ : syracuseStep 15013633 = 11260225) B11260225
theorem B1644295 : Blo 1644021 1644295 := bstep (se 1 (by rfl) ⟨1233221, by rfl⟩ : syracuseStep 1644295 = 2466443) B2466443
theorem B1644303 : Blo 1644021 1644303 := bstep (se 1 (by rfl) ⟨1233227, by rfl⟩ : syracuseStep 1644303 = 2466455) B2466455
theorem B8894245 : Blo 1644021 8894245 := bstep (se 4 (by rfl) ⟨833835, by rfl⟩ : syracuseStep 8894245 = 1667671) B1667671
theorem B1644347 : Blo 1644021 1644347 := bstep (se 1 (by rfl) ⟨1233260, by rfl⟩ : syracuseStep 1644347 = 2466521) B2466521
theorem B1644423 : Blo 1644021 1644423 := bstep (se 1 (by rfl) ⟨1233317, by rfl⟩ : syracuseStep 1644423 = 2466635) B2466635
theorem B1644431 : Blo 1644021 1644431 := bstep (se 1 (by rfl) ⟨1233323, by rfl⟩ : syracuseStep 1644431 = 2466647) B2466647
theorem B1644475 : Blo 1644021 1644475 := bstep (se 1 (by rfl) ⟨1233356, by rfl⟩ : syracuseStep 1644475 = 2466713) B2466713
theorem B1644551 : Blo 1644021 1644551 := bstep (se 1 (by rfl) ⟨1233413, by rfl⟩ : syracuseStep 1644551 = 2466827) B2466827
theorem B1644559 : Blo 1644021 1644559 := bstep (se 1 (by rfl) ⟨1233419, by rfl⟩ : syracuseStep 1644559 = 2466839) B2466839
theorem B5552171 : Blo 1644021 5552171 := bstep (se 1 (by rfl) ⟨4164128, by rfl⟩ : syracuseStep 5552171 = 8328257) B8328257
theorem B1644603 : Blo 1644021 1644603 := bstep (se 1 (by rfl) ⟨1233452, by rfl⟩ : syracuseStep 1644603 = 2466905) B2466905
theorem B4446323 : Blo 1644021 4446323 := bstep (se 1 (by rfl) ⟨3334742, by rfl⟩ : syracuseStep 4446323 = 6669485) B6669485
theorem B1644679 : Blo 1644021 1644679 := bstep (se 1 (by rfl) ⟨1233509, by rfl⟩ : syracuseStep 1644679 = 2467019) B2467019
theorem B3700871 : Blo 1644021 3700871 := bstep (se 1 (by rfl) ⟨2775653, by rfl⟩ : syracuseStep 3700871 = 5551307) B5551307
theorem B1644687 : Blo 1644021 1644687 := bstep (se 1 (by rfl) ⟨1233515, by rfl⟩ : syracuseStep 1644687 = 2467031) B2467031
theorem B1849531 : Blo 1644021 1849531 := bstep (se 1 (by rfl) ⟨1387148, by rfl⟩ : syracuseStep 1849531 = 2774297) B2774297
theorem B1644731 : Blo 1644021 1644731 := bstep (se 1 (by rfl) ⟨1233548, by rfl⟩ : syracuseStep 1644731 = 2467097) B2467097
theorem B1644807 : Blo 1644021 1644807 := bstep (se 1 (by rfl) ⟨1233605, by rfl⟩ : syracuseStep 1644807 = 2467211) B2467211
theorem B1644815 : Blo 1644021 1644815 := bstep (se 1 (by rfl) ⟨1233611, by rfl⟩ : syracuseStep 1644815 = 2467223) B2467223
theorem B14055713 : Blo 1644021 14055713 := bstep (se 2 (by rfl) ⟨5270892, by rfl⟩ : syracuseStep 14055713 = 10541785) B10541785
theorem B1644859 : Blo 1644021 1644859 := bstep (se 1 (by rfl) ⟨1233644, by rfl⟩ : syracuseStep 1644859 = 2467289) B2467289
theorem B3701051 : Blo 1644021 3701051 := bstep (se 1 (by rfl) ⟨2775788, by rfl⟩ : syracuseStep 3701051 = 5551577) B5551577
theorem B2775431 : Blo 1644021 2775431 := bstep (se 1 (by rfl) ⟨2081573, by rfl⟩ : syracuseStep 2775431 = 4163147) B4163147
theorem B1644935 : Blo 1644021 1644935 := bstep (se 1 (by rfl) ⟨1233701, by rfl⟩ : syracuseStep 1644935 = 2467403) B2467403
theorem B1644943 : Blo 1644021 1644943 := bstep (se 1 (by rfl) ⟨1233707, by rfl⟩ : syracuseStep 1644943 = 2467415) B2467415
theorem B3701177 : Blo 1644021 3701177 := bstep (se 2 (by rfl) ⟨1387941, by rfl⟩ : syracuseStep 3701177 = 2775883) B2775883
theorem B1644987 : Blo 1644021 1644987 := bstep (se 1 (by rfl) ⟨1233740, by rfl⟩ : syracuseStep 1644987 = 2467481) B2467481
theorem B1645063 : Blo 1644021 1645063 := bstep (se 1 (by rfl) ⟨1233797, by rfl⟩ : syracuseStep 1645063 = 2467595) B2467595
theorem B1645071 : Blo 1644021 1645071 := bstep (se 1 (by rfl) ⟨1233803, by rfl⟩ : syracuseStep 1645071 = 2467607) B2467607
theorem B4749857 : Blo 1644021 4749857 := bstep (se 2 (by rfl) ⟨1781196, by rfl⟩ : syracuseStep 4749857 = 3562393) B3562393
theorem B1645115 : Blo 1644021 1645115 := bstep (se 1 (by rfl) ⟨1233836, by rfl⟩ : syracuseStep 1645115 = 2467673) B2467673
theorem B10001015 : Blo 1644021 10001015 := bstep (se 1 (by rfl) ⟨7500761, by rfl⟩ : syracuseStep 10001015 = 15001523) B15001523
theorem B1645191 : Blo 1644021 1645191 := bstep (se 1 (by rfl) ⟨1233893, by rfl⟩ : syracuseStep 1645191 = 2467787) B2467787
theorem B1849999 : Blo 1644021 1849999 := bstep (se 1 (by rfl) ⟨1387499, by rfl⟩ : syracuseStep 1849999 = 2774999) B2774999
theorem B1645199 : Blo 1644021 1645199 := bstep (se 1 (by rfl) ⟨1233899, by rfl⟩ : syracuseStep 1645199 = 2467799) B2467799
theorem B1645243 : Blo 1644021 1645243 := bstep (se 1 (by rfl) ⟨1233932, by rfl⟩ : syracuseStep 1645243 = 2467865) B2467865
theorem B2341639 : Blo 1644021 2341639 := bstep (se 1 (by rfl) ⟨1756229, by rfl⟩ : syracuseStep 2341639 = 3512459) B3512459
theorem B1645319 : Blo 1644021 1645319 := bstep (se 1 (by rfl) ⟨1233989, by rfl⟩ : syracuseStep 1645319 = 2467979) B2467979
theorem B3701519 : Blo 1644021 3701519 := bstep (se 1 (by rfl) ⟨2776139, by rfl⟩ : syracuseStep 3701519 = 5552279) B5552279
theorem B1645327 : Blo 1644021 1645327 := bstep (se 1 (by rfl) ⟨1233995, by rfl⟩ : syracuseStep 1645327 = 2467991) B2467991
theorem B3701537 : Blo 1644021 3701537 := bstep (se 2 (by rfl) ⟨1388076, by rfl⟩ : syracuseStep 3701537 = 2776153) B2776153
theorem B1645371 : Blo 1644021 1645371 := bstep (se 1 (by rfl) ⟨1234028, by rfl⟩ : syracuseStep 1645371 = 2468057) B2468057
theorem B3332983 : Blo 1644021 3332983 := bstep (se 1 (by rfl) ⟨2499737, by rfl⟩ : syracuseStep 3332983 = 4999475) B4999475
theorem B1645447 : Blo 1644021 1645447 := bstep (se 1 (by rfl) ⟨1234085, by rfl⟩ : syracuseStep 1645447 = 2468171) B2468171
theorem B1645455 : Blo 1644021 1645455 := bstep (se 1 (by rfl) ⟨1234091, by rfl⟩ : syracuseStep 1645455 = 2468183) B2468183
theorem B4684691 : Blo 1644021 4684691 := bstep (se 1 (by rfl) ⟨3513518, by rfl⟩ : syracuseStep 4684691 = 7027037) B7027037
theorem B18987929 : Blo 1644021 18987929 := bstep (se 2 (by rfl) ⟨7120473, by rfl⟩ : syracuseStep 18987929 = 14240947) B14240947
theorem B1645499 : Blo 1644021 1645499 := bstep (se 1 (by rfl) ⟨1234124, by rfl⟩ : syracuseStep 1645499 = 2468249) B2468249
theorem B1645575 : Blo 1644021 1645575 := bstep (se 1 (by rfl) ⟨1234181, by rfl⟩ : syracuseStep 1645575 = 2468363) B2468363
theorem B2776079 : Blo 1644021 2776079 := bstep (se 1 (by rfl) ⟨2082059, by rfl⟩ : syracuseStep 2776079 = 4164119) B4164119
theorem B1645583 : Blo 1644021 1645583 := bstep (se 1 (by rfl) ⟨1234187, by rfl⟩ : syracuseStep 1645583 = 2468375) B2468375
theorem B15817751 : Blo 1644021 15817751 := bstep (se 1 (by rfl) ⟨11863313, by rfl⟩ : syracuseStep 15817751 = 23726627) B23726627
theorem B1645627 : Blo 1644021 1645627 := bstep (se 1 (by rfl) ⟨1234220, by rfl⟩ : syracuseStep 1645627 = 2468441) B2468441
theorem B3701879 : Blo 1644021 3701879 := bstep (se 1 (by rfl) ⟨2776409, by rfl⟩ : syracuseStep 3701879 = 5552819) B5552819
theorem B1850503 : Blo 1644021 1850503 := bstep (se 1 (by rfl) ⟨1387877, by rfl⟩ : syracuseStep 1850503 = 2775755) B2775755
theorem B1645703 : Blo 1644021 1645703 := bstep (se 1 (by rfl) ⟨1234277, by rfl⟩ : syracuseStep 1645703 = 2468555) B2468555
theorem B1645711 : Blo 1644021 1645711 := bstep (se 1 (by rfl) ⟨1234283, by rfl⟩ : syracuseStep 1645711 = 2468567) B2468567
theorem B1645755 : Blo 1644021 1645755 := bstep (se 1 (by rfl) ⟨1234316, by rfl⟩ : syracuseStep 1645755 = 2468633) B2468633
theorem B2342135 : Blo 1644021 2342135 := bstep (se 1 (by rfl) ⟨1756601, by rfl⟩ : syracuseStep 2342135 = 3513203) B3513203
theorem B1645831 : Blo 1644021 1645831 := bstep (se 1 (by rfl) ⟨1234373, by rfl⟩ : syracuseStep 1645831 = 2468747) B2468747
theorem B1645839 : Blo 1644021 1645839 := bstep (se 1 (by rfl) ⟨1234379, by rfl⟩ : syracuseStep 1645839 = 2468759) B2468759
theorem B5930273 : Blo 1644021 5930273 := bstep (se 2 (by rfl) ⟨2223852, by rfl⟩ : syracuseStep 5930273 = 4447705) B4447705
theorem B3702059 : Blo 1644021 3702059 := bstep (se 1 (by rfl) ⟨2776544, by rfl⟩ : syracuseStep 3702059 = 5553089) B5553089
theorem B1850683 : Blo 1644021 1850683 := bstep (se 1 (by rfl) ⟨1388012, by rfl⟩ : syracuseStep 1850683 = 2776025) B2776025
theorem B5553467 : Blo 1644021 5553467 := bstep (se 1 (by rfl) ⟨4165100, by rfl⟩ : syracuseStep 5553467 = 8330201) B8330201
theorem B1645883 : Blo 1644021 1645883 := bstep (se 1 (by rfl) ⟨1234412, by rfl⟩ : syracuseStep 1645883 = 2468825) B2468825
theorem B12836231 : Blo 1644021 12836231 := bstep (se 1 (by rfl) ⟨9627173, by rfl⟩ : syracuseStep 12836231 = 19254347) B19254347
theorem B1645959 : Blo 1644021 1645959 := bstep (se 1 (by rfl) ⟨1234469, by rfl⟩ : syracuseStep 1645959 = 2468939) B2468939
theorem B1645967 : Blo 1644021 1645967 := bstep (se 1 (by rfl) ⟨1234475, by rfl⟩ : syracuseStep 1645967 = 2468951) B2468951
theorem B6667667 : Blo 1644021 6667667 := bstep (se 1 (by rfl) ⟨5000750, by rfl⟩ : syracuseStep 6667667 = 10001501) B10001501
theorem B1646011 : Blo 1644021 1646011 := bstep (se 1 (by rfl) ⟨1234508, by rfl⟩ : syracuseStep 1646011 = 2469017) B2469017
theorem B7126481 : Blo 1644021 7126481 := bstep (se 2 (by rfl) ⟨2672430, by rfl⟩ : syracuseStep 7126481 = 5344861) B5344861
theorem B9371159 : Blo 1644021 9371159 := bstep (se 1 (by rfl) ⟨7028369, by rfl⟩ : syracuseStep 9371159 = 14056739) B14056739
theorem B2776619 : Blo 1644021 2776619 := bstep (se 1 (by rfl) ⟨2082464, by rfl⟩ : syracuseStep 2776619 = 4164929) B4164929
theorem B8011331 : Blo 1644021 8011331 := bstep (se 1 (by rfl) ⟨6008498, by rfl⟩ : syracuseStep 8011331 = 12016997) B12016997
theorem B3702419 : Blo 1644021 3702419 := bstep (se 1 (by rfl) ⟨2776814, by rfl⟩ : syracuseStep 3702419 = 5553629) B5553629
theorem B4685465 : Blo 1644021 4685465 := bstep (se 2 (by rfl) ⟨1757049, by rfl⟩ : syracuseStep 4685465 = 3514099) B3514099
theorem B3702473 : Blo 1644021 3702473 := bstep (se 2 (by rfl) ⟨1388427, by rfl⟩ : syracuseStep 3702473 = 2776855) B2776855
theorem B1875719 : Blo 1644021 1875719 := bstep (se 1 (by rfl) ⟨1406789, by rfl⟩ : syracuseStep 1875719 = 2813579) B2813579
theorem B12484367 : Blo 1644021 12484367 := bstep (se 1 (by rfl) ⟨9363275, by rfl⟩ : syracuseStep 12484367 = 18726551) B18726551
theorem B1851151 : Blo 1644021 1851151 := bstep (se 1 (by rfl) ⟨1388363, by rfl⟩ : syracuseStep 1851151 = 2776727) B2776727
theorem B8437537 : Blo 1644021 8437537 := bstep (se 2 (by rfl) ⟨3164076, by rfl⟩ : syracuseStep 8437537 = 6328153) B6328153
theorem B5553953 : Blo 1644021 5553953 := bstep (se 2 (by rfl) ⟨2082732, by rfl⟩ : syracuseStep 5553953 = 4165465) B4165465
theorem B56950573 : Blo 1644021 56950573 := bstep (se 3 (by rfl) ⟨10678232, by rfl⟩ : syracuseStep 56950573 = 21356465) B21356465
theorem B6332275 : Blo 1644021 6332275 := bstep (se 1 (by rfl) ⟨4749206, by rfl⟩ : syracuseStep 6332275 = 9498413) B9498413
theorem B4751239 : Blo 1644021 4751239 := bstep (se 1 (by rfl) ⟨3563429, by rfl⟩ : syracuseStep 4751239 = 7126859) B7126859
theorem B2777017 : Blo 1644021 2777017 := bstep (se 2 (by rfl) ⟨1041381, by rfl⟩ : syracuseStep 2777017 = 2082763) B2082763
theorem B6242305 : Blo 1644021 6242305 := bstep (se 2 (by rfl) ⟨2340864, by rfl⟩ : syracuseStep 6242305 = 4681729) B4681729
theorem B45047825 : Blo 1644021 45047825 := bstep (se 2 (by rfl) ⟨16892934, by rfl⟩ : syracuseStep 45047825 = 33785869) B33785869
theorem B42147863 : Blo 1644021 42147863 := bstep (se 1 (by rfl) ⟨31610897, by rfl⟩ : syracuseStep 42147863 = 63221795) B63221795
theorem B3334223 : Blo 1644021 3334223 := bstep (se 1 (by rfl) ⟨2500667, by rfl⟩ : syracuseStep 3334223 = 5001335) B5001335
theorem B2777287 : Blo 1644021 2777287 := bstep (se 1 (by rfl) ⟨2082965, by rfl⟩ : syracuseStep 2777287 = 4165931) B4165931
theorem B3703031 : Blo 1644021 3703031 := bstep (se 1 (by rfl) ⟨2777273, by rfl⟩ : syracuseStep 3703031 = 5554547) B5554547
theorem B2466041 : Blo 1644021 2466041 := bstep (se 2 (by rfl) ⟨924765, by rfl⟩ : syracuseStep 2466041 = 1849531) B1849531
theorem B5554493 : Blo 1644021 5554493 := bstep (se 3 (by rfl) ⟨1041467, by rfl⟩ : syracuseStep 5554493 = 2082935) B2082935
theorem B8888663 : Blo 1644021 8888663 := bstep (se 1 (by rfl) ⟨6666497, by rfl⟩ : syracuseStep 8888663 = 13332995) B13332995
theorem B2466143 : Blo 1644021 2466143 := bstep (se 1 (by rfl) ⟨1849607, by rfl⟩ : syracuseStep 2466143 = 3699215) B3699215
theorem B2777449 : Blo 1644021 2777449 := bstep (se 2 (by rfl) ⟨1041543, by rfl⟩ : syracuseStep 2777449 = 2083087) B2083087
theorem B2466155 : Blo 1644021 2466155 := bstep (se 1 (by rfl) ⟨1849616, by rfl⟩ : syracuseStep 2466155 = 3699233) B3699233
theorem B3514843 : Blo 1644021 3514843 := bstep (se 1 (by rfl) ⟨2636132, by rfl⟩ : syracuseStep 3514843 = 5272265) B5272265
theorem B9372185 : Blo 1644021 9372185 := bstep (se 2 (by rfl) ⟨3514569, by rfl⟩ : syracuseStep 9372185 = 7029139) B7029139
theorem B3514919 : Blo 1644021 3514919 := bstep (se 1 (by rfl) ⟨2636189, by rfl⟩ : syracuseStep 3514919 = 5272379) B5272379
theorem B28107323 : Blo 1644021 28107323 := bstep (se 1 (by rfl) ⟨21080492, by rfl⟩ : syracuseStep 28107323 = 42160985) B42160985
theorem B2466383 : Blo 1644021 2466383 := bstep (se 1 (by rfl) ⟨1849787, by rfl⟩ : syracuseStep 2466383 = 3699575) B3699575
theorem B2466503 : Blo 1644021 2466503 := bstep (se 1 (by rfl) ⟨1849877, by rfl⟩ : syracuseStep 2466503 = 3699755) B3699755
theorem B6243065 : Blo 1644021 6243065 := bstep (se 2 (by rfl) ⟨2341149, by rfl⟩ : syracuseStep 6243065 = 4682299) B4682299
theorem B2466665 : Blo 1644021 2466665 := bstep (se 2 (by rfl) ⟨924999, by rfl⟩ : syracuseStep 2466665 = 1849999) B1849999
theorem B2466743 : Blo 1644021 2466743 := bstep (se 1 (by rfl) ⟨1850057, by rfl⟩ : syracuseStep 2466743 = 3700115) B3700115
theorem B2466779 : Blo 1644021 2466779 := bstep (se 1 (by rfl) ⟨1850084, by rfl⟩ : syracuseStep 2466779 = 3700169) B3700169
theorem B8332307 : Blo 1644021 8332307 := bstep (se 1 (by rfl) ⟨6249230, by rfl⟩ : syracuseStep 8332307 = 12498461) B12498461
theorem B10544195 : Blo 1644021 10544195 := bstep (se 1 (by rfl) ⟨7908146, by rfl⟩ : syracuseStep 10544195 = 15816293) B15816293
theorem B4006991 : Blo 1644021 4006991 := bstep (se 1 (by rfl) ⟨3005243, by rfl⟩ : syracuseStep 4006991 = 6010487) B6010487
theorem B17785975 : Blo 1644021 17785975 := bstep (se 1 (by rfl) ⟨13339481, by rfl⟩ : syracuseStep 17785975 = 26678963) B26678963
theorem B108127385 : Blo 1644021 108127385 := bstep (se 2 (by rfl) ⟨40547769, by rfl⟩ : syracuseStep 108127385 = 81095539) B81095539
theorem B12485825 : Blo 1644021 12485825 := bstep (se 2 (by rfl) ⟨4682184, by rfl⟩ : syracuseStep 12485825 = 9364369) B9364369
theorem B31605977 : Blo 1644021 31605977 := bstep (se 2 (by rfl) ⟨11852241, by rfl⟩ : syracuseStep 31605977 = 23704483) B23704483
theorem B3335585 : Blo 1644021 3335585 := bstep (se 2 (by rfl) ⟨1250844, by rfl⟩ : syracuseStep 3335585 = 2501689) B2501689
theorem B2467247 : Blo 1644021 2467247 := bstep (se 1 (by rfl) ⟨1850435, by rfl⟩ : syracuseStep 2467247 = 3700871) B3700871
theorem B8439241 : Blo 1644021 8439241 := bstep (se 2 (by rfl) ⟨3164715, by rfl⟩ : syracuseStep 8439241 = 6329431) B6329431
theorem B4163035 : Blo 1644021 4163035 := bstep (se 1 (by rfl) ⟨3122276, by rfl⟩ : syracuseStep 4163035 = 6244553) B6244553
theorem B2467337 : Blo 1644021 2467337 := bstep (se 2 (by rfl) ⟨925251, by rfl⟩ : syracuseStep 2467337 = 1850503) B1850503
theorem B108209677 : Blo 1644021 108209677 := bstep (se 3 (by rfl) ⟨20289314, by rfl⟩ : syracuseStep 108209677 = 40578629) B40578629
theorem B2467367 : Blo 1644021 2467367 := bstep (se 1 (by rfl) ⟨1850525, by rfl⟩ : syracuseStep 2467367 = 3701051) B3701051
theorem B2082343 : Blo 1644021 2082343 := bstep (se 1 (by rfl) ⟨1561757, by rfl⟩ : syracuseStep 2082343 = 3123515) B3123515
theorem B2467451 : Blo 1644021 2467451 := bstep (se 1 (by rfl) ⟨1850588, by rfl⟩ : syracuseStep 2467451 = 3701177) B3701177
theorem B12494573 : Blo 1644021 12494573 := bstep (se 3 (by rfl) ⟨2342732, by rfl⟩ : syracuseStep 12494573 = 4685465) B4685465
theorem B2467577 : Blo 1644021 2467577 := bstep (se 2 (by rfl) ⟨925341, by rfl⟩ : syracuseStep 2467577 = 1850683) B1850683
theorem B2467679 : Blo 1644021 2467679 := bstep (se 1 (by rfl) ⟨1850759, by rfl⟩ : syracuseStep 2467679 = 3701519) B3701519
theorem B2467691 : Blo 1644021 2467691 := bstep (se 1 (by rfl) ⟨1850768, by rfl⟩ : syracuseStep 2467691 = 3701537) B3701537
theorem B2082667 : Blo 1644021 2082667 := bstep (se 1 (by rfl) ⟨1562000, by rfl⟩ : syracuseStep 2082667 = 3124001) B3124001
theorem B3123127 : Blo 1644021 3123127 := bstep (se 1 (by rfl) ⟨2342345, by rfl⟩ : syracuseStep 3123127 = 4684691) B4684691
theorem B12658619 : Blo 1644021 12658619 := bstep (se 1 (by rfl) ⟨9493964, by rfl⟩ : syracuseStep 12658619 = 18987929) B18987929
theorem B10545167 : Blo 1644021 10545167 := bstep (se 1 (by rfl) ⟨7908875, by rfl⟩ : syracuseStep 10545167 = 15817751) B15817751
theorem B11855909 : Blo 1644021 11855909 := bstep (se 4 (by rfl) ⟨1111491, by rfl⟩ : syracuseStep 11855909 = 2222983) B2222983
theorem B4163663 : Blo 1644021 4163663 := bstep (se 1 (by rfl) ⟨3122747, by rfl⟩ : syracuseStep 4163663 = 6245495) B6245495
theorem B2467919 : Blo 1644021 2467919 := bstep (se 1 (by rfl) ⟨1850939, by rfl⟩ : syracuseStep 2467919 = 3701879) B3701879
theorem B6244523 : Blo 1644021 6244523 := bstep (se 1 (by rfl) ⟨4683392, by rfl⟩ : syracuseStep 6244523 = 9366785) B9366785
theorem B2468039 : Blo 1644021 2468039 := bstep (se 1 (by rfl) ⟨1851029, by rfl⟩ : syracuseStep 2468039 = 3702059) B3702059
theorem B2468201 : Blo 1644021 2468201 := bstep (se 2 (by rfl) ⟨925575, by rfl⟩ : syracuseStep 2468201 = 1851151) B1851151
theorem B11250049 : Blo 1644021 11250049 := bstep (se 2 (by rfl) ⟨4218768, by rfl⟩ : syracuseStep 11250049 = 8437537) B8437537
theorem B14051717 : Blo 1644021 14051717 := bstep (se 4 (by rfl) ⟨1317348, by rfl⟩ : syracuseStep 14051717 = 2634697) B2634697
theorem B75934097 : Blo 1644021 75934097 := bstep (se 2 (by rfl) ⟨28475286, by rfl⟩ : syracuseStep 75934097 = 56950573) B56950573
theorem B2468279 : Blo 1644021 2468279 := bstep (se 1 (by rfl) ⟨1851209, by rfl⟩ : syracuseStep 2468279 = 3702419) B3702419
theorem B2468315 : Blo 1644021 2468315 := bstep (se 1 (by rfl) ⟨1851236, by rfl⟩ : syracuseStep 2468315 = 3702473) B3702473
theorem B6334985 : Blo 1644021 6334985 := bstep (se 2 (by rfl) ⟨2375619, by rfl⟩ : syracuseStep 6334985 = 4751239) B4751239
theorem B8325665 : Blo 1644021 8325665 := bstep (se 2 (by rfl) ⟨3122124, by rfl⟩ : syracuseStep 8325665 = 6244249) B6244249
theorem B12495545 : Blo 1644021 12495545 := bstep (se 2 (by rfl) ⟨4685829, by rfl⟩ : syracuseStep 12495545 = 9371659) B9371659
theorem B9374393 : Blo 1644021 9374393 := bstep (se 2 (by rfl) ⟨3515397, by rfl⟩ : syracuseStep 9374393 = 7030795) B7030795
theorem B5925575 : Blo 1644021 5925575 := bstep (se 1 (by rfl) ⟨4444181, by rfl⟩ : syracuseStep 5925575 = 8888363) B8888363
theorem B4164311 : Blo 1644021 4164311 := bstep (se 1 (by rfl) ⟨3123233, by rfl⟩ : syracuseStep 4164311 = 6246467) B6246467
theorem B2468783 : Blo 1644021 2468783 := bstep (se 1 (by rfl) ⟨1851587, by rfl⟩ : syracuseStep 2468783 = 3703175) B3703175
theorem B112716785 : Blo 1644021 112716785 := bstep (se 2 (by rfl) ⟨42268794, by rfl⟩ : syracuseStep 112716785 = 84537589) B84537589
theorem B2468873 : Blo 1644021 2468873 := bstep (se 2 (by rfl) ⟨925827, by rfl⟩ : syracuseStep 2468873 = 1851655) B1851655
theorem B2468903 : Blo 1644021 2468903 := bstep (se 1 (by rfl) ⟨1851677, by rfl⟩ : syracuseStep 2468903 = 3703355) B3703355
theorem B2468987 : Blo 1644021 2468987 := bstep (se 1 (by rfl) ⟨1851740, by rfl⟩ : syracuseStep 2468987 = 3703481) B3703481
theorem B3607799 : Blo 1644021 3607799 := bstep (se 1 (by rfl) ⟨2705849, by rfl⟩ : syracuseStep 3607799 = 5411699) B5411699
theorem B6245693 : Blo 1644021 6245693 := bstep (se 3 (by rfl) ⟨1171067, by rfl⟩ : syracuseStep 6245693 = 2342135) B2342135
theorem B5549417 : Blo 1644021 5549417 := bstep (se 2 (by rfl) ⟨2081031, by rfl⟩ : syracuseStep 5549417 = 4162063) B4162063
theorem B3124585 : Blo 1644021 3124585 := bstep (se 2 (by rfl) ⟨1171719, by rfl⟩ : syracuseStep 3124585 = 2343439) B2343439
theorem B45043087 : Blo 1644021 45043087 := bstep (se 1 (by rfl) ⟨33782315, by rfl⟩ : syracuseStep 45043087 = 67564631) B67564631
theorem B15814061 : Blo 1644021 15814061 := bstep (se 3 (by rfl) ⟨2965136, by rfl⟩ : syracuseStep 15814061 = 5930273) B5930273
theorem B6246011 : Blo 1644021 6246011 := bstep (se 1 (by rfl) ⟨4684508, by rfl⟩ : syracuseStep 6246011 = 9369017) B9369017
theorem B12496517 : Blo 1644021 12496517 := bstep (se 4 (by rfl) ⟨1171548, by rfl⟩ : syracuseStep 12496517 = 2343097) B2343097
theorem B5705401 : Blo 1644021 5705401 := bstep (se 2 (by rfl) ⟨2139525, by rfl⟩ : syracuseStep 5705401 = 4279051) B4279051
theorem B4443977 : Blo 1644021 4443977 := bstep (se 2 (by rfl) ⟨1666491, by rfl⟩ : syracuseStep 4443977 = 3332983) B3332983
theorem B5926729 : Blo 1644021 5926729 := bstep (se 2 (by rfl) ⟨2222523, by rfl⟩ : syracuseStep 5926729 = 4445047) B4445047
theorem B6008671 : Blo 1644021 6008671 := bstep (se 1 (by rfl) ⟨4506503, by rfl⟩ : syracuseStep 6008671 = 9013007) B9013007
theorem B15806339 : Blo 1644021 15806339 := bstep (se 1 (by rfl) ⟨11854754, by rfl⟩ : syracuseStep 15806339 = 23709509) B23709509
theorem B5550011 : Blo 1644021 5550011 := bstep (se 1 (by rfl) ⟨4162508, by rfl⟩ : syracuseStep 5550011 = 8325017) B8325017
theorem B9367559 : Blo 1644021 9367559 := bstep (se 1 (by rfl) ⟨7025669, by rfl⟩ : syracuseStep 9367559 = 14051339) B14051339
theorem B5926931 : Blo 1644021 5926931 := bstep (se 1 (by rfl) ⟨4445198, by rfl⟩ : syracuseStep 5926931 = 8890397) B8890397
theorem B12488741 : Blo 1644021 12488741 := bstep (se 4 (by rfl) ⟨1170819, by rfl⟩ : syracuseStep 12488741 = 2341639) B2341639
theorem B3166571 : Blo 1644021 3166571 := bstep (se 1 (by rfl) ⟨2374928, by rfl⟩ : syracuseStep 3166571 = 4749857) B4749857
theorem B5272123 : Blo 1644021 5272123 := bstep (se 1 (by rfl) ⟨3954092, by rfl⟩ : syracuseStep 5272123 = 7908185) B7908185
theorem B2634319 : Blo 1644021 2634319 := bstep (se 1 (by rfl) ⟨1975739, by rfl⟩ : syracuseStep 2634319 = 3951479) B3951479
theorem B33772133 : Blo 1644021 33772133 := bstep (se 4 (by rfl) ⟨3166137, by rfl⟩ : syracuseStep 33772133 = 6332275) B6332275
theorem B3699323 : Blo 1644021 3699323 := bstep (se 1 (by rfl) ⟨2774492, by rfl⟩ : syracuseStep 3699323 = 5548985) B5548985
theorem B5001917 : Blo 1644021 5001917 := bstep (se 3 (by rfl) ⟨937859, by rfl⟩ : syracuseStep 5001917 = 1875719) B1875719
theorem B7025363 : Blo 1644021 7025363 := bstep (se 1 (by rfl) ⟨5269022, by rfl⟩ : syracuseStep 7025363 = 10538045) B10538045
theorem B3699449 : Blo 1644021 3699449 := bstep (se 2 (by rfl) ⟨1387293, by rfl⟩ : syracuseStep 3699449 = 2774587) B2774587
theorem B2634601 : Blo 1644021 2634601 := bstep (se 2 (by rfl) ⟨987975, by rfl⟩ : syracuseStep 2634601 = 1975951) B1975951
theorem B8557487 : Blo 1644021 8557487 := bstep (se 1 (by rfl) ⟨6418115, by rfl⟩ : syracuseStep 8557487 = 12836231) B12836231
theorem B4445111 : Blo 1644021 4445111 := bstep (se 1 (by rfl) ⟨3333833, by rfl⟩ : syracuseStep 4445111 = 6667667) B6667667
theorem B20018177 : Blo 1644021 20018177 := bstep (se 2 (by rfl) ⟨7506816, by rfl⟩ : syracuseStep 20018177 = 15013633) B15013633
theorem B3699719 : Blo 1644021 3699719 := bstep (se 1 (by rfl) ⟨2774789, by rfl⟩ : syracuseStep 3699719 = 5549579) B5549579
theorem B6247439 : Blo 1644021 6247439 := bstep (se 1 (by rfl) ⟨4685579, by rfl⟩ : syracuseStep 6247439 = 9371159) B9371159
theorem B11858993 : Blo 1644021 11858993 := bstep (se 2 (by rfl) ⟨4447122, by rfl⟩ : syracuseStep 11858993 = 8894245) B8894245
theorem B3699791 : Blo 1644021 3699791 := bstep (se 1 (by rfl) ⟨2774843, by rfl⟩ : syracuseStep 3699791 = 5549687) B5549687
theorem B2774459 : Blo 1644021 2774459 := bstep (se 1 (by rfl) ⟨2080844, by rfl⟩ : syracuseStep 2774459 = 4161689) B4161689
theorem B3700187 : Blo 1644021 3700187 := bstep (se 1 (by rfl) ⟨2775140, by rfl⟩ : syracuseStep 3700187 = 5550281) B5550281
theorem B1644071 : Blo 1644021 1644071 := bstep (se 1 (by rfl) ⟨1233053, by rfl⟩ : syracuseStep 1644071 = 2466107) B2466107
theorem B2774567 : Blo 1644021 2774567 := bstep (se 1 (by rfl) ⟨2080925, by rfl⟩ : syracuseStep 2774567 = 4161851) B4161851
theorem B8328743 : Blo 1644021 8328743 := bstep (se 1 (by rfl) ⟨6246557, by rfl⟩ : syracuseStep 8328743 = 12493115) B12493115
theorem B1644111 : Blo 1644021 1644111 := bstep (se 1 (by rfl) ⟨1233083, by rfl⟩ : syracuseStep 1644111 = 2466167) B2466167
theorem B1644127 : Blo 1644021 1644127 := bstep (se 1 (by rfl) ⟨1233095, by rfl⟩ : syracuseStep 1644127 = 2466191) B2466191
theorem B1644155 : Blo 1644021 1644155 := bstep (se 1 (by rfl) ⟨1233116, by rfl⟩ : syracuseStep 1644155 = 2466233) B2466233
theorem B5551739 : Blo 1644021 5551739 := bstep (se 1 (by rfl) ⟨4163804, by rfl⟩ : syracuseStep 5551739 = 8327609) B8327609
theorem B1644207 : Blo 1644021 1644207 := bstep (se 1 (by rfl) ⟨1233155, by rfl⟩ : syracuseStep 1644207 = 2466311) B2466311
theorem B1644231 : Blo 1644021 1644231 := bstep (se 1 (by rfl) ⟨1233173, by rfl⟩ : syracuseStep 1644231 = 2466347) B2466347
theorem B1644251 : Blo 1644021 1644251 := bstep (se 1 (by rfl) ⟨1233188, by rfl⟩ : syracuseStep 1644251 = 2466377) B2466377
theorem B5551901 : Blo 1644021 5551901 := bstep (se 3 (by rfl) ⟨1040981, by rfl⟩ : syracuseStep 5551901 = 2081963) B2081963
theorem B1644327 : Blo 1644021 1644327 := bstep (se 1 (by rfl) ⟨1233245, by rfl⟩ : syracuseStep 1644327 = 2466491) B2466491
theorem B2774857 : Blo 1644021 2774857 := bstep (se 2 (by rfl) ⟨1040571, by rfl⟩ : syracuseStep 2774857 = 2081143) B2081143
theorem B1644367 : Blo 1644021 1644367 := bstep (se 1 (by rfl) ⟨1233275, by rfl⟩ : syracuseStep 1644367 = 2466551) B2466551
theorem B1644383 : Blo 1644021 1644383 := bstep (se 1 (by rfl) ⟨1233287, by rfl⟩ : syracuseStep 1644383 = 2466575) B2466575
theorem B2774891 : Blo 1644021 2774891 := bstep (se 1 (by rfl) ⟨2081168, by rfl⟩ : syracuseStep 2774891 = 4162337) B4162337
theorem B1644411 : Blo 1644021 1644411 := bstep (se 1 (by rfl) ⟨1233308, by rfl⟩ : syracuseStep 1644411 = 2466617) B2466617
theorem B1644463 : Blo 1644021 1644463 := bstep (se 1 (by rfl) ⟨1233347, by rfl⟩ : syracuseStep 1644463 = 2466695) B2466695
theorem B3700655 : Blo 1644021 3700655 := bstep (se 1 (by rfl) ⟨2775491, by rfl⟩ : syracuseStep 3700655 = 5550983) B5550983
theorem B21370817 : Blo 1644021 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B1644487 : Blo 1644021 1644487 := bstep (se 1 (by rfl) ⟨1233365, by rfl⟩ : syracuseStep 1644487 = 2466731) B2466731
theorem B1644507 : Blo 1644021 1644507 := bstep (se 1 (by rfl) ⟨1233380, by rfl⟩ : syracuseStep 1644507 = 2466761) B2466761
theorem B12498947 : Blo 1644021 12498947 := bstep (se 1 (by rfl) ⟨9374210, by rfl⟩ : syracuseStep 12498947 = 18748421) B18748421
theorem B7026695 : Blo 1644021 7026695 := bstep (se 1 (by rfl) ⟨5270021, by rfl⟩ : syracuseStep 7026695 = 10540043) B10540043
theorem B1644583 : Blo 1644021 1644583 := bstep (se 1 (by rfl) ⟨1233437, by rfl⟩ : syracuseStep 1644583 = 2466875) B2466875
theorem B1644623 : Blo 1644021 1644623 := bstep (se 1 (by rfl) ⟨1233467, by rfl⟩ : syracuseStep 1644623 = 2466935) B2466935
theorem B1644639 : Blo 1644021 1644639 := bstep (se 1 (by rfl) ⟨1233479, by rfl⟩ : syracuseStep 1644639 = 2466959) B2466959
theorem B1644667 : Blo 1644021 1644667 := bstep (se 1 (by rfl) ⟨1233500, by rfl⟩ : syracuseStep 1644667 = 2467001) B2467001
theorem B3700907 : Blo 1644021 3700907 := bstep (se 1 (by rfl) ⟨2775680, by rfl⟩ : syracuseStep 3700907 = 5551361) B5551361
theorem B1644719 : Blo 1644021 1644719 := bstep (se 1 (by rfl) ⟨1233539, by rfl⟩ : syracuseStep 1644719 = 2467079) B2467079
theorem B1644743 : Blo 1644021 1644743 := bstep (se 1 (by rfl) ⟨1233557, by rfl⟩ : syracuseStep 1644743 = 2467115) B2467115
theorem B1644763 : Blo 1644021 1644763 := bstep (se 1 (by rfl) ⟨1233572, by rfl⟩ : syracuseStep 1644763 = 2467145) B2467145
theorem B2775289 : Blo 1644021 2775289 := bstep (se 2 (by rfl) ⟨1040733, by rfl⟩ : syracuseStep 2775289 = 2081467) B2081467
theorem B1644839 : Blo 1644021 1644839 := bstep (se 1 (by rfl) ⟨1233629, by rfl⟩ : syracuseStep 1644839 = 2467259) B2467259
theorem B10008893 : Blo 1644021 10008893 := bstep (se 3 (by rfl) ⟨1876667, by rfl⟩ : syracuseStep 10008893 = 3753335) B3753335
theorem B1644879 : Blo 1644021 1644879 := bstep (se 1 (by rfl) ⟨1233659, by rfl⟩ : syracuseStep 1644879 = 2467319) B2467319
theorem B1644895 : Blo 1644021 1644895 := bstep (se 1 (by rfl) ⟨1233671, by rfl⟩ : syracuseStep 1644895 = 2467343) B2467343
theorem B1644923 : Blo 1644021 1644923 := bstep (se 1 (by rfl) ⟨1233692, by rfl⟩ : syracuseStep 1644923 = 2467385) B2467385
theorem B1644975 : Blo 1644021 1644975 := bstep (se 1 (by rfl) ⟨1233731, by rfl⟩ : syracuseStep 1644975 = 2467463) B2467463
theorem B1644999 : Blo 1644021 1644999 := bstep (se 1 (by rfl) ⟨1233749, by rfl⟩ : syracuseStep 1644999 = 2467499) B2467499
theorem B1849819 : Blo 1644021 1849819 := bstep (se 1 (by rfl) ⟨1387364, by rfl⟩ : syracuseStep 1849819 = 2774729) B2774729
theorem B1645019 : Blo 1644021 1645019 := bstep (se 1 (by rfl) ⟨1233764, by rfl⟩ : syracuseStep 1645019 = 2467529) B2467529
theorem B5552603 : Blo 1644021 5552603 := bstep (se 1 (by rfl) ⟨4164452, by rfl⟩ : syracuseStep 5552603 = 8328905) B8328905
theorem B5929453 : Blo 1644021 5929453 := bstep (se 3 (by rfl) ⟨1111772, by rfl⟩ : syracuseStep 5929453 = 2223545) B2223545
theorem B2775559 : Blo 1644021 2775559 := bstep (se 1 (by rfl) ⟨2081669, by rfl⟩ : syracuseStep 2775559 = 4163339) B4163339
theorem B1645095 : Blo 1644021 1645095 := bstep (se 1 (by rfl) ⟨1233821, by rfl⟩ : syracuseStep 1645095 = 2467643) B2467643
theorem B1645135 : Blo 1644021 1645135 := bstep (se 1 (by rfl) ⟨1233851, by rfl⟩ : syracuseStep 1645135 = 2467703) B2467703
theorem B1645151 : Blo 1644021 1645151 := bstep (se 1 (by rfl) ⟨1233863, by rfl⟩ : syracuseStep 1645151 = 2467727) B2467727
theorem B1645179 : Blo 1644021 1645179 := bstep (se 1 (by rfl) ⟨1233884, by rfl⟩ : syracuseStep 1645179 = 2467769) B2467769
theorem B6249095 : Blo 1644021 6249095 := bstep (se 1 (by rfl) ⟨4686821, by rfl⟩ : syracuseStep 6249095 = 9373643) B9373643
theorem B1645231 : Blo 1644021 1645231 := bstep (se 1 (by rfl) ⟨1233923, by rfl⟩ : syracuseStep 1645231 = 2467847) B2467847
theorem B3701447 : Blo 1644021 3701447 := bstep (se 1 (by rfl) ⟨2776085, by rfl⟩ : syracuseStep 3701447 = 5552171) B5552171
theorem B1645255 : Blo 1644021 1645255 := bstep (se 1 (by rfl) ⟨1233941, by rfl⟩ : syracuseStep 1645255 = 2467883) B2467883
theorem B7903955 : Blo 1644021 7903955 := bstep (se 1 (by rfl) ⟨5927966, by rfl⟩ : syracuseStep 7903955 = 11855933) B11855933
theorem B1645275 : Blo 1644021 1645275 := bstep (se 1 (by rfl) ⟨1233956, by rfl⟩ : syracuseStep 1645275 = 2467913) B2467913
theorem B2964215 : Blo 1644021 2964215 := bstep (se 1 (by rfl) ⟨2223161, by rfl⟩ : syracuseStep 2964215 = 4446323) B4446323
theorem B1645351 : Blo 1644021 1645351 := bstep (se 1 (by rfl) ⟨1234013, by rfl⟩ : syracuseStep 1645351 = 2468027) B2468027
theorem B1645391 : Blo 1644021 1645391 := bstep (se 1 (by rfl) ⟨1234043, by rfl⟩ : syracuseStep 1645391 = 2468087) B2468087
theorem B1645407 : Blo 1644021 1645407 := bstep (se 1 (by rfl) ⟨1234055, by rfl⟩ : syracuseStep 1645407 = 2468111) B2468111
theorem B9370475 : Blo 1644021 9370475 := bstep (se 1 (by rfl) ⟨7027856, by rfl⟩ : syracuseStep 9370475 = 14055713) B14055713
theorem B1645435 : Blo 1644021 1645435 := bstep (se 1 (by rfl) ⟨1234076, by rfl⟩ : syracuseStep 1645435 = 2468153) B2468153
theorem B1850287 : Blo 1644021 1850287 := bstep (se 1 (by rfl) ⟨1387715, by rfl⟩ : syracuseStep 1850287 = 2775431) B2775431
theorem B1645487 : Blo 1644021 1645487 := bstep (se 1 (by rfl) ⟨1234115, by rfl⟩ : syracuseStep 1645487 = 2468231) B2468231
theorem B2775991 : Blo 1644021 2775991 := bstep (se 1 (by rfl) ⟨2081993, by rfl⟩ : syracuseStep 2775991 = 4163987) B4163987
theorem B3562427 : Blo 1644021 3562427 := bstep (se 1 (by rfl) ⟨2671820, by rfl⟩ : syracuseStep 3562427 = 5343641) B5343641
theorem B1645511 : Blo 1644021 1645511 := bstep (se 1 (by rfl) ⟨1234133, by rfl⟩ : syracuseStep 1645511 = 2468267) B2468267
theorem B1645531 : Blo 1644021 1645531 := bstep (se 1 (by rfl) ⟨1234148, by rfl⟩ : syracuseStep 1645531 = 2468297) B2468297
theorem B1645607 : Blo 1644021 1645607 := bstep (se 1 (by rfl) ⟨1234205, by rfl⟩ : syracuseStep 1645607 = 2468411) B2468411
theorem B6667343 : Blo 1644021 6667343 := bstep (se 1 (by rfl) ⟨5000507, by rfl⟩ : syracuseStep 6667343 = 10001015) B10001015
theorem B1645647 : Blo 1644021 1645647 := bstep (se 1 (by rfl) ⟨1234235, by rfl⟩ : syracuseStep 1645647 = 2468471) B2468471
theorem B1645663 : Blo 1644021 1645663 := bstep (se 1 (by rfl) ⟨1234247, by rfl⟩ : syracuseStep 1645663 = 2468495) B2468495
theorem B2776187 : Blo 1644021 2776187 := bstep (se 1 (by rfl) ⟨2082140, by rfl⟩ : syracuseStep 2776187 = 4164281) B4164281
theorem B1645691 : Blo 1644021 1645691 := bstep (se 1 (by rfl) ⟨1234268, by rfl⟩ : syracuseStep 1645691 = 2468537) B2468537
theorem B5553305 : Blo 1644021 5553305 := bstep (se 2 (by rfl) ⟨2082489, by rfl⟩ : syracuseStep 5553305 = 4164979) B4164979
theorem B1645743 : Blo 1644021 1645743 := bstep (se 1 (by rfl) ⟨1234307, by rfl⟩ : syracuseStep 1645743 = 2468615) B2468615
theorem B11852993 : Blo 1644021 11852993 := bstep (se 2 (by rfl) ⟨4444872, by rfl⟩ : syracuseStep 11852993 = 8889745) B8889745
theorem B1645767 : Blo 1644021 1645767 := bstep (se 1 (by rfl) ⟨1234325, by rfl⟩ : syracuseStep 1645767 = 2468651) B2468651
theorem B1645787 : Blo 1644021 1645787 := bstep (se 1 (by rfl) ⟨1234340, by rfl⟩ : syracuseStep 1645787 = 2468681) B2468681
theorem B81165581 : Blo 1644021 81165581 := bstep (se 3 (by rfl) ⟨15218546, by rfl⟩ : syracuseStep 81165581 = 30437093) B30437093
theorem B1645863 : Blo 1644021 1645863 := bstep (se 1 (by rfl) ⟨1234397, by rfl⟩ : syracuseStep 1645863 = 2468795) B2468795
theorem B1645903 : Blo 1644021 1645903 := bstep (se 1 (by rfl) ⟨1234427, by rfl⟩ : syracuseStep 1645903 = 2468855) B2468855
theorem B1850719 : Blo 1644021 1850719 := bstep (se 1 (by rfl) ⟨1388039, by rfl⟩ : syracuseStep 1850719 = 2776079) B2776079
theorem B1645919 : Blo 1644021 1645919 := bstep (se 1 (by rfl) ⟨1234439, by rfl⟩ : syracuseStep 1645919 = 2468879) B2468879
theorem B1645947 : Blo 1644021 1645947 := bstep (se 1 (by rfl) ⟨1234460, by rfl⟩ : syracuseStep 1645947 = 2468921) B2468921
theorem B1645999 : Blo 1644021 1645999 := bstep (se 1 (by rfl) ⟨1234499, by rfl⟩ : syracuseStep 1645999 = 2468999) B2468999
theorem B2776585 : Blo 1644021 2776585 := bstep (se 2 (by rfl) ⟨1041219, by rfl⟩ : syracuseStep 2776585 = 2082439) B2082439
theorem B3702311 : Blo 1644021 3702311 := bstep (se 1 (by rfl) ⟨2776733, by rfl⟩ : syracuseStep 3702311 = 5553467) B5553467
theorem B53354051 : Blo 1644021 53354051 := bstep (se 1 (by rfl) ⟨40015538, by rfl⟩ : syracuseStep 53354051 = 80031077) B80031077
theorem B8330849 : Blo 1644021 8330849 := bstep (se 2 (by rfl) ⟨3124068, by rfl⟩ : syracuseStep 8330849 = 6248137) B6248137
theorem B200326769 : Blo 1644021 200326769 := bstep (se 2 (by rfl) ⟨75122538, by rfl⟩ : syracuseStep 200326769 = 150245077) B150245077
theorem B4750987 : Blo 1644021 4750987 := bstep (se 1 (by rfl) ⟨3563240, by rfl⟩ : syracuseStep 4750987 = 7126481) B7126481
theorem B2776747 : Blo 1644021 2776747 := bstep (se 1 (by rfl) ⟨2082560, by rfl⟩ : syracuseStep 2776747 = 4165121) B4165121
theorem B1851079 : Blo 1644021 1851079 := bstep (se 1 (by rfl) ⟨1388309, by rfl⟩ : syracuseStep 1851079 = 2776619) B2776619
theorem B5340887 : Blo 1644021 5340887 := bstep (se 1 (by rfl) ⟨4005665, by rfl⟩ : syracuseStep 5340887 = 8011331) B8011331
theorem B8322911 : Blo 1644021 8322911 := bstep (se 1 (by rfl) ⟨6242183, by rfl⟩ : syracuseStep 8322911 = 12484367) B12484367
theorem B3702635 : Blo 1644021 3702635 := bstep (se 1 (by rfl) ⟨2776976, by rfl⟩ : syracuseStep 3702635 = 5553953) B5553953
theorem B3702689 : Blo 1644021 3702689 := bstep (se 2 (by rfl) ⟨1388508, by rfl⟩ : syracuseStep 3702689 = 2777017) B2777017
theorem B13516753 : Blo 1644021 13516753 := bstep (se 2 (by rfl) ⟨5068782, by rfl⟩ : syracuseStep 13516753 = 10137565) B10137565
theorem B2777051 : Blo 1644021 2777051 := bstep (se 1 (by rfl) ⟨2082788, by rfl⟩ : syracuseStep 2777051 = 4165577) B4165577
theorem B8323073 : Blo 1644021 8323073 := bstep (se 2 (by rfl) ⟨3121152, by rfl⟩ : syracuseStep 8323073 = 6242305) B6242305
theorem B28098575 : Blo 1644021 28098575 := bstep (se 1 (by rfl) ⟨21073931, by rfl⟩ : syracuseStep 28098575 = 42147863) B42147863
theorem B30031883 : Blo 1644021 30031883 := bstep (se 1 (by rfl) ⟨22523912, by rfl⟩ : syracuseStep 30031883 = 45047825) B45047825
theorem B3702995 : Blo 1644021 3702995 := bstep (se 1 (by rfl) ⟨2777246, by rfl⟩ : syracuseStep 3702995 = 5554493) B5554493
theorem B3703049 : Blo 1644021 3703049 := bstep (se 2 (by rfl) ⟨1388643, by rfl⟩ : syracuseStep 3703049 = 2777287) B2777287
theorem B2466215 : Blo 1644021 2466215 := bstep (se 1 (by rfl) ⟨1849661, by rfl⟩ : syracuseStep 2466215 = 3699323) B3699323
theorem B3703265 : Blo 1644021 3703265 := bstep (se 2 (by rfl) ⟨1388724, by rfl⟩ : syracuseStep 3703265 = 2777449) B2777449
theorem B2466299 : Blo 1644021 2466299 := bstep (se 1 (by rfl) ⟨1849724, by rfl⟩ : syracuseStep 2466299 = 3699449) B3699449
theorem B4162043 : Blo 1644021 4162043 := bstep (se 1 (by rfl) ⟨3121532, by rfl⟩ : syracuseStep 4162043 = 6243065) B6243065
theorem B15000065 : Blo 1644021 15000065 := bstep (se 2 (by rfl) ⟨5625024, by rfl⟩ : syracuseStep 15000065 = 11250049) B11250049
theorem B2466425 : Blo 1644021 2466425 := bstep (se 2 (by rfl) ⟨924909, by rfl⟩ : syracuseStep 2466425 = 1849819) B1849819
theorem B4686457 : Blo 1644021 4686457 := bstep (se 2 (by rfl) ⟨1757421, by rfl⟩ : syracuseStep 4686457 = 3514843) B3514843
theorem B7905937 : Blo 1644021 7905937 := bstep (se 2 (by rfl) ⟨2964726, by rfl⟩ : syracuseStep 7905937 = 5929453) B5929453
theorem B13345451 : Blo 1644021 13345451 := bstep (se 1 (by rfl) ⟨10009088, by rfl⟩ : syracuseStep 13345451 = 20018177) B20018177
theorem B2466479 : Blo 1644021 2466479 := bstep (se 1 (by rfl) ⟨1849859, by rfl⟩ : syracuseStep 2466479 = 3699719) B3699719
theorem B5554871 : Blo 1644021 5554871 := bstep (se 1 (by rfl) ⟨4166153, by rfl⟩ : syracuseStep 5554871 = 8332307) B8332307
theorem B7905995 : Blo 1644021 7905995 := bstep (se 1 (by rfl) ⟨5929496, by rfl⟩ : syracuseStep 7905995 = 11858993) B11858993
theorem B7029463 : Blo 1644021 7029463 := bstep (se 1 (by rfl) ⟨5272097, by rfl⟩ : syracuseStep 7029463 = 10544195) B10544195
theorem B2466527 : Blo 1644021 2466527 := bstep (se 1 (by rfl) ⟨1849895, by rfl⟩ : syracuseStep 2466527 = 3699791) B3699791
theorem B2671327 : Blo 1644021 2671327 := bstep (se 1 (by rfl) ⟨2003495, by rfl⟩ : syracuseStep 2671327 = 4006991) B4006991
theorem B7029497 : Blo 1644021 7029497 := bstep (se 2 (by rfl) ⟨2636061, by rfl⟩ : syracuseStep 7029497 = 5272123) B5272123
theorem B8323883 : Blo 1644021 8323883 := bstep (se 1 (by rfl) ⟨6242912, by rfl⟩ : syracuseStep 8323883 = 12485825) B12485825
theorem B21070651 : Blo 1644021 21070651 := bstep (se 1 (by rfl) ⟨15802988, by rfl⟩ : syracuseStep 21070651 = 31605977) B31605977
theorem B26690381 : Blo 1644021 26690381 := bstep (se 3 (by rfl) ⟨5004446, by rfl⟩ : syracuseStep 26690381 = 10008893) B10008893
theorem B2466791 : Blo 1644021 2466791 := bstep (se 1 (by rfl) ⟨1850093, by rfl⟩ : syracuseStep 2466791 = 3700187) B3700187
theorem B2467049 : Blo 1644021 2467049 := bstep (se 2 (by rfl) ⟨925143, by rfl⟩ : syracuseStep 2467049 = 1850287) B1850287
theorem B2467103 : Blo 1644021 2467103 := bstep (se 1 (by rfl) ⟨1850327, by rfl⟩ : syracuseStep 2467103 = 3700655) B3700655
theorem B8439079 : Blo 1644021 8439079 := bstep (se 1 (by rfl) ⟨6329309, by rfl⟩ : syracuseStep 8439079 = 12658619) B12658619
theorem B8332631 : Blo 1644021 8332631 := bstep (se 1 (by rfl) ⟨6249473, by rfl⟩ : syracuseStep 8332631 = 12498947) B12498947
theorem B9373117 : Blo 1644021 9373117 := bstep (se 3 (by rfl) ⟨1757459, by rfl⟩ : syracuseStep 9373117 = 3514919) B3514919
theorem B4163015 : Blo 1644021 4163015 := bstep (se 1 (by rfl) ⟨3122261, by rfl⟩ : syracuseStep 4163015 = 6244523) B6244523
theorem B2467271 : Blo 1644021 2467271 := bstep (se 1 (by rfl) ⟨1850453, by rfl⟩ : syracuseStep 2467271 = 3700907) B3700907
theorem B2467625 : Blo 1644021 2467625 := bstep (se 2 (by rfl) ⟨925359, by rfl⟩ : syracuseStep 2467625 = 1850719) B1850719
theorem B3950383 : Blo 1644021 3950383 := bstep (se 1 (by rfl) ⟨2962787, by rfl⟩ : syracuseStep 3950383 = 5925575) B5925575
theorem B2467631 : Blo 1644021 2467631 := bstep (se 1 (by rfl) ⟨1850723, by rfl⟩ : syracuseStep 2467631 = 3701447) B3701447
theorem B5269303 : Blo 1644021 5269303 := bstep (se 1 (by rfl) ⟨3951977, by rfl⟩ : syracuseStep 5269303 = 7903955) B7903955
theorem B13338445 : Blo 1644021 13338445 := bstep (se 3 (by rfl) ⟨2500958, by rfl⟩ : syracuseStep 13338445 = 5001917) B5001917
theorem B1976143 : Blo 1644021 1976143 := bstep (se 1 (by rfl) ⟨1482107, by rfl⟩ : syracuseStep 1976143 = 2964215) B2964215
theorem B60057449 : Blo 1644021 60057449 := bstep (se 2 (by rfl) ⟨22521543, by rfl⟩ : syracuseStep 60057449 = 45043087) B45043087
theorem B144279569 : Blo 1644021 144279569 := bstep (se 2 (by rfl) ⟨54104838, by rfl⟩ : syracuseStep 144279569 = 108209677) B108209677
theorem B54110387 : Blo 1644021 54110387 := bstep (se 1 (by rfl) ⟨40582790, by rfl⟩ : syracuseStep 54110387 = 81165581) B81165581
theorem B6334649 : Blo 1644021 6334649 := bstep (se 2 (by rfl) ⟨2375493, by rfl⟩ : syracuseStep 6334649 = 4750987) B4750987
theorem B4163795 : Blo 1644021 4163795 := bstep (se 1 (by rfl) ⟨3122846, by rfl⟩ : syracuseStep 4163795 = 6245693) B6245693
theorem B2468105 : Blo 1644021 2468105 := bstep (se 2 (by rfl) ⟨925539, by rfl⟩ : syracuseStep 2468105 = 1851079) B1851079
theorem B2468207 : Blo 1644021 2468207 := bstep (se 1 (by rfl) ⟨1851155, by rfl⟩ : syracuseStep 2468207 = 3702311) B3702311
theorem B4164007 : Blo 1644021 4164007 := bstep (se 1 (by rfl) ⟨3123005, by rfl⟩ : syracuseStep 4164007 = 6246011) B6246011
theorem B5548607 : Blo 1644021 5548607 := bstep (se 1 (by rfl) ⟨4161455, by rfl⟩ : syracuseStep 5548607 = 8322911) B8322911
theorem B2468423 : Blo 1644021 2468423 := bstep (se 1 (by rfl) ⟨1851317, by rfl⟩ : syracuseStep 2468423 = 3702635) B3702635
theorem B4164169 : Blo 1644021 4164169 := bstep (se 2 (by rfl) ⟨1561563, by rfl⟩ : syracuseStep 4164169 = 3123127) B3123127
theorem B10537559 : Blo 1644021 10537559 := bstep (se 1 (by rfl) ⟨7903169, by rfl⟩ : syracuseStep 10537559 = 15806339) B15806339
theorem B2468459 : Blo 1644021 2468459 := bstep (se 1 (by rfl) ⟨1851344, by rfl⟩ : syracuseStep 2468459 = 3702689) B3702689
theorem B6245039 : Blo 1644021 6245039 := bstep (se 1 (by rfl) ⟨4683779, by rfl⟩ : syracuseStep 6245039 = 9367559) B9367559
theorem B3951287 : Blo 1644021 3951287 := bstep (se 1 (by rfl) ⟨2963465, by rfl⟩ : syracuseStep 3951287 = 5926931) B5926931
theorem B8325827 : Blo 1644021 8325827 := bstep (se 1 (by rfl) ⟨6244370, by rfl⟩ : syracuseStep 8325827 = 12488741) B12488741
theorem B2222815 : Blo 1644021 2222815 := bstep (se 1 (by rfl) ⟨1667111, by rfl⟩ : syracuseStep 2222815 = 3334223) B3334223
theorem B2468687 : Blo 1644021 2468687 := bstep (se 1 (by rfl) ⟨1851515, by rfl⟩ : syracuseStep 2468687 = 3703031) B3703031
theorem B18738215 : Blo 1644021 18738215 := bstep (se 1 (by rfl) ⟨14053661, by rfl⟩ : syracuseStep 18738215 = 28107323) B28107323
theorem B22514755 : Blo 1644021 22514755 := bstep (se 1 (by rfl) ⟨16886066, by rfl⟩ : syracuseStep 22514755 = 33772133) B33772133
theorem B31607981 : Blo 1644021 31607981 := bstep (se 3 (by rfl) ⟨5926496, by rfl⟩ : syracuseStep 31607981 = 11852993) B11852993
theorem B5704991 : Blo 1644021 5704991 := bstep (se 1 (by rfl) ⟨4278743, by rfl⟩ : syracuseStep 5704991 = 8557487) B8557487
theorem B9620797 : Blo 1644021 9620797 := bstep (se 3 (by rfl) ⟨1803899, by rfl⟩ : syracuseStep 9620797 = 3607799) B3607799
theorem B4164959 : Blo 1644021 4164959 := bstep (se 1 (by rfl) ⟨3123719, by rfl⟩ : syracuseStep 4164959 = 6247439) B6247439
theorem B72084923 : Blo 1644021 72084923 := bstep (se 1 (by rfl) ⟨54063692, by rfl⟩ : syracuseStep 72084923 = 108127385) B108127385
theorem B23703101 : Blo 1644021 23703101 := bstep (se 3 (by rfl) ⟨4444331, by rfl⟩ : syracuseStep 23703101 = 8888663) B8888663
theorem B9367811 : Blo 1644021 9367811 := bstep (se 1 (by rfl) ⟨7025858, by rfl⟩ : syracuseStep 9367811 = 14051717) B14051717
theorem B50622731 : Blo 1644021 50622731 := bstep (se 1 (by rfl) ⟨37967048, by rfl⟩ : syracuseStep 50622731 = 75934097) B75934097
theorem B4223323 : Blo 1644021 4223323 := bstep (se 1 (by rfl) ⟨3167492, by rfl⟩ : syracuseStep 4223323 = 6334985) B6334985
theorem B5550443 : Blo 1644021 5550443 := bstep (se 1 (by rfl) ⟨4162832, by rfl⟩ : syracuseStep 5550443 = 8325665) B8325665
theorem B4166063 : Blo 1644021 4166063 := bstep (se 1 (by rfl) ⟨3124547, by rfl⟩ : syracuseStep 4166063 = 6249095) B6249095
theorem B4166113 : Blo 1644021 4166113 := bstep (se 2 (by rfl) ⟨1562292, by rfl⟩ : syracuseStep 4166113 = 3124585) B3124585
theorem B6246983 : Blo 1644021 6246983 := bstep (se 1 (by rfl) ⟨4685237, by rfl⟩ : syracuseStep 6246983 = 9370475) B9370475
theorem B11252321 : Blo 1644021 11252321 := bstep (se 2 (by rfl) ⟨4219620, by rfl⟩ : syracuseStep 11252321 = 8439241) B8439241
theorem B5550713 : Blo 1644021 5550713 := bstep (se 2 (by rfl) ⟨2081517, by rfl⟩ : syracuseStep 5550713 = 4163035) B4163035
theorem B4444895 : Blo 1644021 4444895 := bstep (se 1 (by rfl) ⟨3333671, by rfl⟩ : syracuseStep 4444895 = 6667343) B6667343
theorem B3699611 : Blo 1644021 3699611 := bstep (se 1 (by rfl) ⟨2774708, by rfl⟩ : syracuseStep 3699611 = 5549417) B5549417
theorem B7607201 : Blo 1644021 7607201 := bstep (se 2 (by rfl) ⟨2852700, by rfl⟩ : syracuseStep 7607201 = 5705401) B5705401
theorem B133551179 : Blo 1644021 133551179 := bstep (se 1 (by rfl) ⟨100163384, by rfl⟩ : syracuseStep 133551179 = 200326769) B200326769
theorem B3699809 : Blo 1644021 3699809 := bstep (se 2 (by rfl) ⟨1387428, by rfl⟩ : syracuseStep 3699809 = 2774857) B2774857
theorem B7902305 : Blo 1644021 7902305 := bstep (se 2 (by rfl) ⟨2963364, by rfl⟩ : syracuseStep 7902305 = 5926729) B5926729
theorem B3560591 : Blo 1644021 3560591 := bstep (se 1 (by rfl) ⟨2670443, by rfl⟩ : syracuseStep 3560591 = 5340887) B5340887
theorem B9499805 : Blo 1644021 9499805 := bstep (se 3 (by rfl) ⟨1781213, by rfl⟩ : syracuseStep 9499805 = 3562427) B3562427
theorem B56988845 : Blo 1644021 56988845 := bstep (se 3 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 56988845 = 21370817) B21370817
theorem B2962651 : Blo 1644021 2962651 := bstep (se 1 (by rfl) ⟨2221988, by rfl⟩ : syracuseStep 2962651 = 4443977) B4443977
theorem B3700007 : Blo 1644021 3700007 := bstep (se 1 (by rfl) ⟨2775005, by rfl⟩ : syracuseStep 3700007 = 5550011) B5550011
theorem B28120445 : Blo 1644021 28120445 := bstep (se 3 (by rfl) ⟨5272583, by rfl⟩ : syracuseStep 28120445 = 10545167) B10545167
theorem B1644027 : Blo 1644021 1644027 := bstep (se 1 (by rfl) ⟨1233020, by rfl⟩ : syracuseStep 1644027 = 2466041) B2466041
theorem B1644095 : Blo 1644021 1644095 := bstep (se 1 (by rfl) ⟨1233071, by rfl⟩ : syracuseStep 1644095 = 2466143) B2466143
theorem B1644103 : Blo 1644021 1644103 := bstep (se 1 (by rfl) ⟨1233077, by rfl⟩ : syracuseStep 1644103 = 2466155) B2466155
theorem B3700385 : Blo 1644021 3700385 := bstep (se 2 (by rfl) ⟨1387644, by rfl⟩ : syracuseStep 3700385 = 2775289) B2775289
theorem B6248123 : Blo 1644021 6248123 := bstep (se 1 (by rfl) ⟨4686092, by rfl⟩ : syracuseStep 6248123 = 9372185) B9372185
theorem B1644255 : Blo 1644021 1644255 := bstep (se 1 (by rfl) ⟨1233191, by rfl⟩ : syracuseStep 1644255 = 2466383) B2466383
theorem B1644335 : Blo 1644021 1644335 := bstep (se 1 (by rfl) ⟨1233251, by rfl⟩ : syracuseStep 1644335 = 2466503) B2466503
theorem B4683575 : Blo 1644021 4683575 := bstep (se 1 (by rfl) ⟨3512681, by rfl⟩ : syracuseStep 4683575 = 7025363) B7025363
theorem B1644443 : Blo 1644021 1644443 := bstep (se 1 (by rfl) ⟨1233332, by rfl⟩ : syracuseStep 1644443 = 2466665) B2466665
theorem B2963407 : Blo 1644021 2963407 := bstep (se 1 (by rfl) ⟨2222555, by rfl⟩ : syracuseStep 2963407 = 4445111) B4445111
theorem B1644495 : Blo 1644021 1644495 := bstep (se 1 (by rfl) ⟨1233371, by rfl⟩ : syracuseStep 1644495 = 2466743) B2466743
theorem B1644519 : Blo 1644021 1644519 := bstep (se 1 (by rfl) ⟨1233389, by rfl⟩ : syracuseStep 1644519 = 2466779) B2466779
theorem B3700745 : Blo 1644021 3700745 := bstep (se 2 (by rfl) ⟨1387779, by rfl⟩ : syracuseStep 3700745 = 2775559) B2775559
theorem B3512425 : Blo 1644021 3512425 := bstep (se 2 (by rfl) ⟨1317159, by rfl⟩ : syracuseStep 3512425 = 2634319) B2634319
theorem B1644831 : Blo 1644021 1644831 := bstep (se 1 (by rfl) ⟨1233623, by rfl⟩ : syracuseStep 1644831 = 2467247) B2467247
theorem B8444189 : Blo 1644021 8444189 := bstep (se 3 (by rfl) ⟨1583285, by rfl⟩ : syracuseStep 8444189 = 3166571) B3166571
theorem B1849639 : Blo 1644021 1849639 := bstep (se 1 (by rfl) ⟨1387229, by rfl⟩ : syracuseStep 1849639 = 2774459) B2774459
theorem B1644891 : Blo 1644021 1644891 := bstep (se 1 (by rfl) ⟨1233668, by rfl⟩ : syracuseStep 1644891 = 2467337) B2467337
theorem B1849711 : Blo 1644021 1849711 := bstep (se 1 (by rfl) ⟨1387283, by rfl⟩ : syracuseStep 1849711 = 2774567) B2774567
theorem B1644911 : Blo 1644021 1644911 := bstep (se 1 (by rfl) ⟨1233683, by rfl⟩ : syracuseStep 1644911 = 2467367) B2467367
theorem B5552495 : Blo 1644021 5552495 := bstep (se 1 (by rfl) ⟨4164371, by rfl⟩ : syracuseStep 5552495 = 8328743) B8328743
theorem B3701159 : Blo 1644021 3701159 := bstep (se 1 (by rfl) ⟨2775869, by rfl⟩ : syracuseStep 3701159 = 5551739) B5551739
theorem B1644967 : Blo 1644021 1644967 := bstep (se 1 (by rfl) ⟨1233725, by rfl⟩ : syracuseStep 1644967 = 2467451) B2467451
theorem B8894893 : Blo 1644021 8894893 := bstep (se 3 (by rfl) ⟨1667792, by rfl⟩ : syracuseStep 8894893 = 3335585) B3335585
theorem B3512801 : Blo 1644021 3512801 := bstep (se 2 (by rfl) ⟨1317300, by rfl⟩ : syracuseStep 3512801 = 2634601) B2634601
theorem B8329715 : Blo 1644021 8329715 := bstep (se 1 (by rfl) ⟨6247286, by rfl⟩ : syracuseStep 8329715 = 12494573) B12494573
theorem B1645051 : Blo 1644021 1645051 := bstep (se 1 (by rfl) ⟨1233788, by rfl⟩ : syracuseStep 1645051 = 2467577) B2467577
theorem B3701267 : Blo 1644021 3701267 := bstep (se 1 (by rfl) ⟨2775950, by rfl⟩ : syracuseStep 3701267 = 5551901) B5551901
theorem B1645119 : Blo 1644021 1645119 := bstep (se 1 (by rfl) ⟨1233839, by rfl⟩ : syracuseStep 1645119 = 2467679) B2467679
theorem B1849927 : Blo 1644021 1849927 := bstep (se 1 (by rfl) ⟨1387445, by rfl⟩ : syracuseStep 1849927 = 2774891) B2774891
theorem B1645127 : Blo 1644021 1645127 := bstep (se 1 (by rfl) ⟨1233845, by rfl⟩ : syracuseStep 1645127 = 2467691) B2467691
theorem B3701321 : Blo 1644021 3701321 := bstep (se 2 (by rfl) ⟨1387995, by rfl⟩ : syracuseStep 3701321 = 2775991) B2775991
theorem B4684463 : Blo 1644021 4684463 := bstep (se 1 (by rfl) ⟨3513347, by rfl⟩ : syracuseStep 4684463 = 7026695) B7026695
theorem B7903939 : Blo 1644021 7903939 := bstep (se 1 (by rfl) ⟨5927954, by rfl⟩ : syracuseStep 7903939 = 11855909) B11855909
theorem B2775775 : Blo 1644021 2775775 := bstep (se 1 (by rfl) ⟨2081831, by rfl⟩ : syracuseStep 2775775 = 4163663) B4163663
theorem B1645279 : Blo 1644021 1645279 := bstep (se 1 (by rfl) ⟨1233959, by rfl⟩ : syracuseStep 1645279 = 2467919) B2467919
theorem B1645359 : Blo 1644021 1645359 := bstep (se 1 (by rfl) ⟨1234019, by rfl⟩ : syracuseStep 1645359 = 2468039) B2468039
theorem B23714633 : Blo 1644021 23714633 := bstep (se 2 (by rfl) ⟨8892987, by rfl⟩ : syracuseStep 23714633 = 17785975) B17785975
theorem B1645467 : Blo 1644021 1645467 := bstep (se 1 (by rfl) ⟨1234100, by rfl⟩ : syracuseStep 1645467 = 2468201) B2468201
theorem B1645519 : Blo 1644021 1645519 := bstep (se 1 (by rfl) ⟨1234139, by rfl⟩ : syracuseStep 1645519 = 2468279) B2468279
theorem B3701735 : Blo 1644021 3701735 := bstep (se 1 (by rfl) ⟨2776301, by rfl⟩ : syracuseStep 3701735 = 5552603) B5552603
theorem B1645543 : Blo 1644021 1645543 := bstep (se 1 (by rfl) ⟨1234157, by rfl⟩ : syracuseStep 1645543 = 2468315) B2468315
theorem B8330363 : Blo 1644021 8330363 := bstep (se 1 (by rfl) ⟨6247772, by rfl⟩ : syracuseStep 8330363 = 12495545) B12495545
theorem B6249595 : Blo 1644021 6249595 := bstep (se 1 (by rfl) ⟨4687196, by rfl⟩ : syracuseStep 6249595 = 9374393) B9374393
theorem B2776207 : Blo 1644021 2776207 := bstep (se 1 (by rfl) ⟨2082155, by rfl⟩ : syracuseStep 2776207 = 4164311) B4164311
theorem B32046245 : Blo 1644021 32046245 := bstep (se 4 (by rfl) ⟨3004335, by rfl⟩ : syracuseStep 32046245 = 6008671) B6008671
theorem B1645855 : Blo 1644021 1645855 := bstep (se 1 (by rfl) ⟨1234391, by rfl⟩ : syracuseStep 1645855 = 2468783) B2468783
theorem B75144523 : Blo 1644021 75144523 := bstep (se 1 (by rfl) ⟨56358392, by rfl⟩ : syracuseStep 75144523 = 112716785) B112716785
theorem B1645915 : Blo 1644021 1645915 := bstep (se 1 (by rfl) ⟨1234436, by rfl⟩ : syracuseStep 1645915 = 2468873) B2468873
theorem B3702113 : Blo 1644021 3702113 := bstep (se 2 (by rfl) ⟨1388292, by rfl⟩ : syracuseStep 3702113 = 2776585) B2776585
theorem B1645935 : Blo 1644021 1645935 := bstep (se 1 (by rfl) ⟨1234451, by rfl⟩ : syracuseStep 1645935 = 2468903) B2468903
theorem B2776457 : Blo 1644021 2776457 := bstep (se 2 (by rfl) ⟨1041171, by rfl⟩ : syracuseStep 2776457 = 2082343) B2082343
theorem B1850791 : Blo 1644021 1850791 := bstep (se 1 (by rfl) ⟨1388093, by rfl⟩ : syracuseStep 1850791 = 2776187) B2776187
theorem B1645991 : Blo 1644021 1645991 := bstep (se 1 (by rfl) ⟨1234493, by rfl⟩ : syracuseStep 1645991 = 2468987) B2468987
theorem B3702203 : Blo 1644021 3702203 := bstep (se 1 (by rfl) ⟨2776652, by rfl⟩ : syracuseStep 3702203 = 5553305) B5553305
theorem B3702329 : Blo 1644021 3702329 := bstep (se 2 (by rfl) ⟨1388373, by rfl⟩ : syracuseStep 3702329 = 2776747) B2776747
theorem B10542707 : Blo 1644021 10542707 := bstep (se 1 (by rfl) ⟨7907030, by rfl⟩ : syracuseStep 10542707 = 15814061) B15814061
theorem B35569367 : Blo 1644021 35569367 := bstep (se 1 (by rfl) ⟨26677025, by rfl⟩ : syracuseStep 35569367 = 53354051) B53354051
theorem B5553899 : Blo 1644021 5553899 := bstep (se 1 (by rfl) ⟨4165424, by rfl⟩ : syracuseStep 5553899 = 8330849) B8330849
theorem B8331011 : Blo 1644021 8331011 := bstep (se 1 (by rfl) ⟨6248258, by rfl⟩ : syracuseStep 8331011 = 12496517) B12496517
theorem B2776889 : Blo 1644021 2776889 := bstep (se 2 (by rfl) ⟨1041333, by rfl⟩ : syracuseStep 2776889 = 2082667) B2082667
theorem B18022337 : Blo 1644021 18022337 := bstep (se 2 (by rfl) ⟨6758376, by rfl⟩ : syracuseStep 18022337 = 13516753) B13516753
theorem B1851367 : Blo 1644021 1851367 := bstep (se 1 (by rfl) ⟨1388525, by rfl⟩ : syracuseStep 1851367 = 2777051) B2777051
theorem B20021255 : Blo 1644021 20021255 := bstep (se 1 (by rfl) ⟨15015941, by rfl⟩ : syracuseStep 20021255 = 30031883) B30031883
theorem B2777375 : Blo 1644021 2777375 := bstep (se 1 (by rfl) ⟨2083031, by rfl⟩ : syracuseStep 2777375 = 4166063) B4166063
theorem B2466185 : Blo 1644021 2466185 := bstep (se 2 (by rfl) ⟨924819, by rfl⟩ : syracuseStep 2466185 = 1849639) B1849639
theorem B8896967 : Blo 1644021 8896967 := bstep (se 1 (by rfl) ⟨6672725, by rfl⟩ : syracuseStep 8896967 = 13345451) B13345451
theorem B3703247 : Blo 1644021 3703247 := bstep (se 1 (by rfl) ⟨2777435, by rfl⟩ : syracuseStep 3703247 = 5554871) B5554871
theorem B144294365 : Blo 1644021 144294365 := bstep (se 3 (by rfl) ⟨27055193, by rfl⟩ : syracuseStep 144294365 = 54110387) B54110387
theorem B2466281 : Blo 1644021 2466281 := bstep (se 2 (by rfl) ⟨924855, by rfl⟩ : syracuseStep 2466281 = 1849711) B1849711
theorem B4686331 : Blo 1644021 4686331 := bstep (se 1 (by rfl) ⟨3514748, by rfl⟩ : syracuseStep 4686331 = 7029497) B7029497
theorem B17793587 : Blo 1644021 17793587 := bstep (se 1 (by rfl) ⟨13345190, by rfl⟩ : syracuseStep 17793587 = 26690381) B26690381
theorem B2466407 : Blo 1644021 2466407 := bstep (se 1 (by rfl) ⟨1849805, by rfl⟩ : syracuseStep 2466407 = 3699611) B3699611
theorem B5554817 : Blo 1644021 5554817 := bstep (se 2 (by rfl) ⟨2083056, by rfl⟩ : syracuseStep 5554817 = 4166113) B4166113
theorem B2466539 : Blo 1644021 2466539 := bstep (se 1 (by rfl) ⟨1849904, by rfl⟩ : syracuseStep 2466539 = 3699809) B3699809
theorem B5268203 : Blo 1644021 5268203 := bstep (se 1 (by rfl) ⟨3951152, by rfl⟩ : syracuseStep 5268203 = 7902305) B7902305
theorem B2466569 : Blo 1644021 2466569 := bstep (se 2 (by rfl) ⟨924963, by rfl⟩ : syracuseStep 2466569 = 1849927) B1849927
theorem B6333203 : Blo 1644021 6333203 := bstep (se 1 (by rfl) ⟨4749902, by rfl⟩ : syracuseStep 6333203 = 9499805) B9499805
theorem B2466671 : Blo 1644021 2466671 := bstep (se 1 (by rfl) ⟨1850003, by rfl⟩ : syracuseStep 2466671 = 3700007) B3700007
theorem B5555087 : Blo 1644021 5555087 := bstep (se 1 (by rfl) ⟨4166315, by rfl⟩ : syracuseStep 5555087 = 8332631) B8332631
theorem B9372617 : Blo 1644021 9372617 := bstep (se 2 (by rfl) ⟨3514731, by rfl⟩ : syracuseStep 9372617 = 7029463) B7029463
theorem B2466923 : Blo 1644021 2466923 := bstep (se 1 (by rfl) ⟨1850192, by rfl⟩ : syracuseStep 2466923 = 3700385) B3700385
theorem B3122383 : Blo 1644021 3122383 := bstep (se 1 (by rfl) ⟨2341787, by rfl⟩ : syracuseStep 3122383 = 4683575) B4683575
theorem B2467163 : Blo 1644021 2467163 := bstep (se 1 (by rfl) ⟨1850372, by rfl⟩ : syracuseStep 2467163 = 3700745) B3700745
theorem B8332793 : Blo 1644021 8332793 := bstep (se 2 (by rfl) ⟨3124797, by rfl⟩ : syracuseStep 8332793 = 6249595) B6249595
theorem B5629459 : Blo 1644021 5629459 := bstep (se 1 (by rfl) ⟨4222094, by rfl⟩ : syracuseStep 5629459 = 8444189) B8444189
theorem B2467439 : Blo 1644021 2467439 := bstep (se 1 (by rfl) ⟨1850579, by rfl⟩ : syracuseStep 2467439 = 3701159) B3701159
theorem B3950201 : Blo 1644021 3950201 := bstep (se 2 (by rfl) ⟨1481325, by rfl⟩ : syracuseStep 3950201 = 2962651) B2962651
theorem B2467511 : Blo 1644021 2467511 := bstep (se 1 (by rfl) ⟨1850633, by rfl⟩ : syracuseStep 2467511 = 3701267) B3701267
theorem B2467547 : Blo 1644021 2467547 := bstep (se 1 (by rfl) ⟨1850660, by rfl⟩ : syracuseStep 2467547 = 3701321) B3701321
theorem B4163359 : Blo 1644021 4163359 := bstep (se 1 (by rfl) ⟨3122519, by rfl⟩ : syracuseStep 4163359 = 6245039) B6245039
theorem B3122975 : Blo 1644021 3122975 := bstep (se 1 (by rfl) ⟨2342231, by rfl⟩ : syracuseStep 3122975 = 4684463) B4684463
theorem B2467721 : Blo 1644021 2467721 := bstep (se 2 (by rfl) ⟨925395, by rfl⟩ : syracuseStep 2467721 = 1850791) B1850791
theorem B2467823 : Blo 1644021 2467823 := bstep (se 1 (by rfl) ⟨1850867, by rfl⟩ : syracuseStep 2467823 = 3701735) B3701735
theorem B21071987 : Blo 1644021 21071987 := bstep (se 1 (by rfl) ⟨15803990, by rfl⟩ : syracuseStep 21071987 = 31607981) B31607981
theorem B3803327 : Blo 1644021 3803327 := bstep (se 1 (by rfl) ⟨2852495, by rfl⟩ : syracuseStep 3803327 = 5704991) B5704991
theorem B2468075 : Blo 1644021 2468075 := bstep (se 1 (by rfl) ⟨1851056, by rfl⟩ : syracuseStep 2468075 = 3702113) B3702113
theorem B48056615 : Blo 1644021 48056615 := bstep (se 1 (by rfl) ⟨36042461, by rfl⟩ : syracuseStep 48056615 = 72084923) B72084923
theorem B2468135 : Blo 1644021 2468135 := bstep (se 1 (by rfl) ⟨1851101, by rfl⟩ : syracuseStep 2468135 = 3702203) B3702203
theorem B2468219 : Blo 1644021 2468219 := bstep (se 1 (by rfl) ⟨1851164, by rfl⟩ : syracuseStep 2468219 = 3702329) B3702329
theorem B20285869 : Blo 1644021 20285869 := bstep (se 3 (by rfl) ⟨3803600, by rfl⟩ : syracuseStep 20285869 = 7607201) B7607201
theorem B3951209 : Blo 1644021 3951209 := bstep (se 2 (by rfl) ⟨1481703, by rfl⟩ : syracuseStep 3951209 = 2963407) B2963407
theorem B2468489 : Blo 1644021 2468489 := bstep (se 2 (by rfl) ⟨925683, by rfl⟩ : syracuseStep 2468489 = 1851367) B1851367
theorem B5548715 : Blo 1644021 5548715 := bstep (se 1 (by rfl) ⟨4161536, by rfl⟩ : syracuseStep 5548715 = 8323073) B8323073
theorem B2468663 : Blo 1644021 2468663 := bstep (se 1 (by rfl) ⟨1851497, by rfl⟩ : syracuseStep 2468663 = 3702995) B3702995
theorem B6245207 : Blo 1644021 6245207 := bstep (se 1 (by rfl) ⟨4683905, by rfl⟩ : syracuseStep 6245207 = 9367811) B9367811
theorem B2468699 : Blo 1644021 2468699 := bstep (se 1 (by rfl) ⟨1851524, by rfl⟩ : syracuseStep 2468699 = 3703049) B3703049
theorem B2468843 : Blo 1644021 2468843 := bstep (se 1 (by rfl) ⟨1851632, by rfl⟩ : syracuseStep 2468843 = 3703265) B3703265
theorem B4164655 : Blo 1644021 4164655 := bstep (se 1 (by rfl) ⟨3123491, by rfl⟩ : syracuseStep 4164655 = 6246983) B6246983
theorem B5270663 : Blo 1644021 5270663 := bstep (se 1 (by rfl) ⟨3952997, by rfl⟩ : syracuseStep 5270663 = 7905995) B7905995
theorem B5549255 : Blo 1644021 5549255 := bstep (se 1 (by rfl) ⟨4161941, by rfl⟩ : syracuseStep 5549255 = 8323883) B8323883
theorem B89034119 : Blo 1644021 89034119 := bstep (se 1 (by rfl) ⟨66775589, by rfl⟩ : syracuseStep 89034119 = 133551179) B133551179
theorem B18746963 : Blo 1644021 18746963 := bstep (se 1 (by rfl) ⟨14060222, by rfl⟩ : syracuseStep 18746963 = 28120445) B28120445
theorem B10538585 : Blo 1644021 10538585 := bstep (se 2 (by rfl) ⟨3951969, by rfl⟩ : syracuseStep 10538585 = 7903939) B7903939
theorem B28094201 : Blo 1644021 28094201 := bstep (se 2 (by rfl) ⟨10535325, by rfl⟩ : syracuseStep 28094201 = 21070651) B21070651
theorem B4165415 : Blo 1644021 4165415 := bstep (se 1 (by rfl) ⟨3124061, by rfl⟩ : syracuseStep 4165415 = 6248123) B6248123
theorem B40038299 : Blo 1644021 40038299 := bstep (se 1 (by rfl) ⟨30028724, by rfl⟩ : syracuseStep 40038299 = 60057449) B60057449
theorem B96186379 : Blo 1644021 96186379 := bstep (se 1 (by rfl) ⟨72139784, by rfl⟩ : syracuseStep 96186379 = 144279569) B144279569
theorem B30019673 : Blo 1644021 30019673 := bstep (se 2 (by rfl) ⟨11257377, by rfl⟩ : syracuseStep 30019673 = 22514755) B22514755
theorem B4223099 : Blo 1644021 4223099 := bstep (se 1 (by rfl) ⟨3167324, by rfl⟩ : syracuseStep 4223099 = 6334649) B6334649
theorem B28102949 : Blo 1644021 28102949 := bstep (se 4 (by rfl) ⟨2634651, by rfl⟩ : syracuseStep 28102949 = 5269303) B5269303
theorem B3699071 : Blo 1644021 3699071 := bstep (se 1 (by rfl) ⟨2774303, by rfl⟩ : syracuseStep 3699071 = 5548607) B5548607
theorem B11252105 : Blo 1644021 11252105 := bstep (se 2 (by rfl) ⟨4219539, by rfl⟩ : syracuseStep 11252105 = 8439079) B8439079
theorem B7025039 : Blo 1644021 7025039 := bstep (se 1 (by rfl) ⟨5268779, by rfl⟩ : syracuseStep 7025039 = 10537559) B10537559
theorem B100192697 : Blo 1644021 100192697 := bstep (se 2 (by rfl) ⟨37572261, by rfl⟩ : syracuseStep 100192697 = 75144523) B75144523
theorem B2634191 : Blo 1644021 2634191 := bstep (se 1 (by rfl) ⟨1975643, by rfl⟩ : syracuseStep 2634191 = 3951287) B3951287
theorem B5550551 : Blo 1644021 5550551 := bstep (se 1 (by rfl) ⟨4162913, by rfl⟩ : syracuseStep 5550551 = 8325827) B8325827
theorem B22524389 : Blo 1644021 22524389 := bstep (se 4 (by rfl) ⟨2111661, by rfl⟩ : syracuseStep 22524389 = 4223323) B4223323
theorem B12497489 : Blo 1644021 12497489 := bstep (se 2 (by rfl) ⟨4686558, by rfl⟩ : syracuseStep 12497489 = 9373117) B9373117
theorem B2634857 : Blo 1644021 2634857 := bstep (se 2 (by rfl) ⟨988071, by rfl⟩ : syracuseStep 2634857 = 1976143) B1976143
theorem B23712911 : Blo 1644021 23712911 := bstep (se 1 (by rfl) ⟨17784683, by rfl⟩ : syracuseStep 23712911 = 35569367) B35569367
theorem B12014891 : Blo 1644021 12014891 := bstep (se 1 (by rfl) ⟨9011168, by rfl⟩ : syracuseStep 12014891 = 18022337) B18022337
theorem B18732383 : Blo 1644021 18732383 := bstep (se 1 (by rfl) ⟨14049287, by rfl⟩ : syracuseStep 18732383 = 28098575) B28098575
theorem B4683233 : Blo 1644021 4683233 := bstep (se 2 (by rfl) ⟨1756212, by rfl⟩ : syracuseStep 4683233 = 3512425) B3512425
theorem B33748487 : Blo 1644021 33748487 := bstep (se 1 (by rfl) ⟨25311365, by rfl⟩ : syracuseStep 33748487 = 50622731) B50622731
theorem B3700295 : Blo 1644021 3700295 := bstep (se 1 (by rfl) ⟨2775221, by rfl⟩ : syracuseStep 3700295 = 5550443) B5550443
theorem B1644143 : Blo 1644021 1644143 := bstep (se 1 (by rfl) ⟨1233107, by rfl⟩ : syracuseStep 1644143 = 2466215) B2466215
theorem B1644199 : Blo 1644021 1644199 := bstep (se 1 (by rfl) ⟨1233149, by rfl⟩ : syracuseStep 1644199 = 2466299) B2466299
theorem B2774695 : Blo 1644021 2774695 := bstep (se 1 (by rfl) ⟨2081021, by rfl⟩ : syracuseStep 2774695 = 4162043) B4162043
theorem B10000043 : Blo 1644021 10000043 := bstep (se 1 (by rfl) ⟨7500032, by rfl⟩ : syracuseStep 10000043 = 15000065) B15000065
theorem B7501547 : Blo 1644021 7501547 := bstep (se 1 (by rfl) ⟨5626160, by rfl⟩ : syracuseStep 7501547 = 11252321) B11252321
theorem B1644283 : Blo 1644021 1644283 := bstep (se 1 (by rfl) ⟨1233212, by rfl⟩ : syracuseStep 1644283 = 2466425) B2466425
theorem B3700475 : Blo 1644021 3700475 := bstep (se 1 (by rfl) ⟨2775356, by rfl⟩ : syracuseStep 3700475 = 5550713) B5550713
theorem B1644319 : Blo 1644021 1644319 := bstep (se 1 (by rfl) ⟨1233239, by rfl⟩ : syracuseStep 1644319 = 2466479) B2466479
theorem B1644351 : Blo 1644021 1644351 := bstep (se 1 (by rfl) ⟨1233263, by rfl⟩ : syracuseStep 1644351 = 2466527) B2466527
theorem B5552009 : Blo 1644021 5552009 := bstep (se 2 (by rfl) ⟨2082003, by rfl⟩ : syracuseStep 5552009 = 4164007) B4164007
theorem B11859857 : Blo 1644021 11859857 := bstep (se 2 (by rfl) ⟨4447446, by rfl⟩ : syracuseStep 11859857 = 8894893) B8894893
theorem B1644527 : Blo 1644021 1644527 := bstep (se 1 (by rfl) ⟨1233395, by rfl⟩ : syracuseStep 1644527 = 2466791) B2466791
theorem B2373727 : Blo 1644021 2373727 := bstep (se 1 (by rfl) ⟨1780295, by rfl⟩ : syracuseStep 2373727 = 3560591) B3560591
theorem B5552225 : Blo 1644021 5552225 := bstep (se 2 (by rfl) ⟨2082084, by rfl⟩ : syracuseStep 5552225 = 4164169) B4164169
theorem B37992563 : Blo 1644021 37992563 := bstep (se 1 (by rfl) ⟨28494422, by rfl⟩ : syracuseStep 37992563 = 56988845) B56988845
theorem B1644699 : Blo 1644021 1644699 := bstep (se 1 (by rfl) ⟨1233524, by rfl⟩ : syracuseStep 1644699 = 2467049) B2467049
theorem B6248609 : Blo 1644021 6248609 := bstep (se 2 (by rfl) ⟨2343228, by rfl⟩ : syracuseStep 6248609 = 4686457) B4686457
theorem B1644735 : Blo 1644021 1644735 := bstep (se 1 (by rfl) ⟨1233551, by rfl⟩ : syracuseStep 1644735 = 2467103) B2467103
theorem B10541249 : Blo 1644021 10541249 := bstep (se 2 (by rfl) ⟨3952968, by rfl⟩ : syracuseStep 10541249 = 7905937) B7905937
theorem B2963753 : Blo 1644021 2963753 := bstep (se 2 (by rfl) ⟨1111407, by rfl⟩ : syracuseStep 2963753 = 2222815) B2222815
theorem B3701033 : Blo 1644021 3701033 := bstep (se 2 (by rfl) ⟨1387887, by rfl⟩ : syracuseStep 3701033 = 2775775) B2775775
theorem B3561769 : Blo 1644021 3561769 := bstep (se 2 (by rfl) ⟨1335663, by rfl⟩ : syracuseStep 3561769 = 2671327) B2671327
theorem B2775343 : Blo 1644021 2775343 := bstep (se 1 (by rfl) ⟨2081507, by rfl⟩ : syracuseStep 2775343 = 4163015) B4163015
theorem B1644847 : Blo 1644021 1644847 := bstep (se 1 (by rfl) ⟨1233635, by rfl⟩ : syracuseStep 1644847 = 2467271) B2467271
theorem B1645083 : Blo 1644021 1645083 := bstep (se 1 (by rfl) ⟨1233812, by rfl⟩ : syracuseStep 1645083 = 2467625) B2467625
theorem B1645087 : Blo 1644021 1645087 := bstep (se 1 (by rfl) ⟨1233815, by rfl⟩ : syracuseStep 1645087 = 2467631) B2467631
theorem B2775863 : Blo 1644021 2775863 := bstep (se 1 (by rfl) ⟨2081897, by rfl⟩ : syracuseStep 2775863 = 4163795) B4163795
theorem B1645403 : Blo 1644021 1645403 := bstep (se 1 (by rfl) ⟨1234052, by rfl⟩ : syracuseStep 1645403 = 2468105) B2468105
theorem B3701609 : Blo 1644021 3701609 := bstep (se 2 (by rfl) ⟨1388103, by rfl⟩ : syracuseStep 3701609 = 2776207) B2776207
theorem B3701663 : Blo 1644021 3701663 := bstep (se 1 (by rfl) ⟨2776247, by rfl⟩ : syracuseStep 3701663 = 5552495) B5552495
theorem B1645471 : Blo 1644021 1645471 := bstep (se 1 (by rfl) ⟨1234103, by rfl⟩ : syracuseStep 1645471 = 2468207) B2468207
theorem B2341867 : Blo 1644021 2341867 := bstep (se 1 (by rfl) ⟨1756400, by rfl⟩ : syracuseStep 2341867 = 3512801) B3512801
theorem B5553143 : Blo 1644021 5553143 := bstep (se 1 (by rfl) ⟨4164857, by rfl⟩ : syracuseStep 5553143 = 8329715) B8329715
theorem B1645615 : Blo 1644021 1645615 := bstep (se 1 (by rfl) ⟨1234211, by rfl⟩ : syracuseStep 1645615 = 2468423) B2468423
theorem B1645639 : Blo 1644021 1645639 := bstep (se 1 (by rfl) ⟨1234229, by rfl⟩ : syracuseStep 1645639 = 2468459) B2468459
theorem B12827729 : Blo 1644021 12827729 := bstep (se 2 (by rfl) ⟨4810398, by rfl⟩ : syracuseStep 12827729 = 9620797) B9620797
theorem B15809755 : Blo 1644021 15809755 := bstep (se 1 (by rfl) ⟨11857316, by rfl⟩ : syracuseStep 15809755 = 23714633) B23714633
theorem B1645791 : Blo 1644021 1645791 := bstep (se 1 (by rfl) ⟨1234343, by rfl⟩ : syracuseStep 1645791 = 2468687) B2468687
theorem B11853053 : Blo 1644021 11853053 := bstep (se 3 (by rfl) ⟨2222447, by rfl⟩ : syracuseStep 11853053 = 4444895) B4444895
theorem B12492143 : Blo 1644021 12492143 := bstep (se 1 (by rfl) ⟨9369107, by rfl⟩ : syracuseStep 12492143 = 18738215) B18738215
theorem B5553575 : Blo 1644021 5553575 := bstep (se 1 (by rfl) ⟨4165181, by rfl⟩ : syracuseStep 5553575 = 8330363) B8330363
theorem B21364163 : Blo 1644021 21364163 := bstep (se 1 (by rfl) ⟨16023122, by rfl⟩ : syracuseStep 21364163 = 32046245) B32046245
theorem B2776639 : Blo 1644021 2776639 := bstep (se 1 (by rfl) ⟨2082479, by rfl⟩ : syracuseStep 2776639 = 4164959) B4164959
theorem B1850971 : Blo 1644021 1850971 := bstep (se 1 (by rfl) ⟨1388228, by rfl⟩ : syracuseStep 1850971 = 2776457) B2776457
theorem B15802067 : Blo 1644021 15802067 := bstep (se 1 (by rfl) ⟨11851550, by rfl⟩ : syracuseStep 15802067 = 23703101) B23703101
theorem B5267177 : Blo 1644021 5267177 := bstep (se 2 (by rfl) ⟨1975191, by rfl⟩ : syracuseStep 5267177 = 3950383) B3950383
theorem B7028471 : Blo 1644021 7028471 := bstep (se 1 (by rfl) ⟨5271353, by rfl⟩ : syracuseStep 7028471 = 10542707) B10542707
theorem B17784593 : Blo 1644021 17784593 := bstep (se 2 (by rfl) ⟨6669222, by rfl⟩ : syracuseStep 17784593 = 13338445) B13338445
theorem B3702599 : Blo 1644021 3702599 := bstep (se 1 (by rfl) ⟨2776949, by rfl⟩ : syracuseStep 3702599 = 5553899) B5553899
theorem B5554007 : Blo 1644021 5554007 := bstep (se 1 (by rfl) ⟨4165505, by rfl⟩ : syracuseStep 5554007 = 8331011) B8331011
theorem B1851259 : Blo 1644021 1851259 := bstep (se 1 (by rfl) ⟨1388444, by rfl⟩ : syracuseStep 1851259 = 2776889) B2776889
theorem B20013115 : Blo 1644021 20013115 := bstep (se 1 (by rfl) ⟨15009836, by rfl⟩ : syracuseStep 20013115 = 30019673) B30019673
theorem B1851583 : Blo 1644021 1851583 := bstep (se 1 (by rfl) ⟨1388687, by rfl⟩ : syracuseStep 1851583 = 2777375) B2777375
theorem B18735299 : Blo 1644021 18735299 := bstep (se 1 (by rfl) ⟨14051474, by rfl⟩ : syracuseStep 18735299 = 28102949) B28102949
theorem B2466047 : Blo 1644021 2466047 := bstep (se 1 (by rfl) ⟨1849535, by rfl⟩ : syracuseStep 2466047 = 3699071) B3699071
theorem B5931311 : Blo 1644021 5931311 := bstep (se 1 (by rfl) ⟨4448483, by rfl⟩ : syracuseStep 5931311 = 8896967) B8896967
theorem B15016259 : Blo 1644021 15016259 := bstep (se 1 (by rfl) ⟨11262194, by rfl⟩ : syracuseStep 15016259 = 22524389) B22524389
theorem B11862391 : Blo 1644021 11862391 := bstep (se 1 (by rfl) ⟨8896793, by rfl⟩ : syracuseStep 11862391 = 17793587) B17793587
theorem B8331659 : Blo 1644021 8331659 := bstep (se 1 (by rfl) ⟨6248744, by rfl⟩ : syracuseStep 8331659 = 12497489) B12497489
theorem B3703211 : Blo 1644021 3703211 := bstep (se 1 (by rfl) ⟨2777408, by rfl⟩ : syracuseStep 3703211 = 5554817) B5554817
theorem B3703391 : Blo 1644021 3703391 := bstep (se 1 (by rfl) ⟨2777543, by rfl⟩ : syracuseStep 3703391 = 5555087) B5555087
theorem B3122155 : Blo 1644021 3122155 := bstep (se 1 (by rfl) ⟨2341616, by rfl⟩ : syracuseStep 3122155 = 4683233) B4683233
theorem B5555195 : Blo 1644021 5555195 := bstep (se 1 (by rfl) ⟨4166396, by rfl⟩ : syracuseStep 5555195 = 8332793) B8332793
theorem B2466863 : Blo 1644021 2466863 := bstep (se 1 (by rfl) ⟨1850147, by rfl⟩ : syracuseStep 2466863 = 3700295) B3700295
theorem B2466983 : Blo 1644021 2466983 := bstep (se 1 (by rfl) ⟨1850237, by rfl⟩ : syracuseStep 2466983 = 3700475) B3700475
theorem B7906571 : Blo 1644021 7906571 := bstep (se 1 (by rfl) ⟨5929928, by rfl⟩ : syracuseStep 7906571 = 11859857) B11859857
theorem B3122489 : Blo 1644021 3122489 := bstep (se 2 (by rfl) ⟨1170933, by rfl⟩ : syracuseStep 3122489 = 2341867) B2341867
theorem B1975835 : Blo 1644021 1975835 := bstep (se 1 (by rfl) ⟨1481876, by rfl⟩ : syracuseStep 1975835 = 2963753) B2963753
theorem B2467355 : Blo 1644021 2467355 := bstep (se 1 (by rfl) ⟨1850516, by rfl⟩ : syracuseStep 2467355 = 3701033) B3701033
theorem B4163177 : Blo 1644021 4163177 := bstep (se 2 (by rfl) ⟨1561191, by rfl⟩ : syracuseStep 4163177 = 3122383) B3122383
theorem B21079673 : Blo 1644021 21079673 := bstep (se 2 (by rfl) ⟨7904877, by rfl⟩ : syracuseStep 21079673 = 15809755) B15809755
theorem B4163471 : Blo 1644021 4163471 := bstep (se 1 (by rfl) ⟨3122603, by rfl⟩ : syracuseStep 4163471 = 6245207) B6245207
theorem B2467739 : Blo 1644021 2467739 := bstep (se 1 (by rfl) ⟨1850804, by rfl⟩ : syracuseStep 2467739 = 3701609) B3701609
theorem B2467775 : Blo 1644021 2467775 := bstep (se 1 (by rfl) ⟨1850831, by rfl⟩ : syracuseStep 2467775 = 3701663) B3701663
theorem B7505945 : Blo 1644021 7505945 := bstep (se 2 (by rfl) ⟨2814729, by rfl⟩ : syracuseStep 7505945 = 5629459) B5629459
theorem B2467961 : Blo 1644021 2467961 := bstep (se 2 (by rfl) ⟨925485, by rfl⟩ : syracuseStep 2467961 = 1850971) B1850971
theorem B2468345 : Blo 1644021 2468345 := bstep (se 2 (by rfl) ⟨925629, by rfl⟩ : syracuseStep 2468345 = 1851259) B1851259
theorem B18729467 : Blo 1644021 18729467 := bstep (se 1 (by rfl) ⟨14047100, by rfl⟩ : syracuseStep 18729467 = 28094201) B28094201
theorem B11856395 : Blo 1644021 11856395 := bstep (se 1 (by rfl) ⟨8892296, by rfl⟩ : syracuseStep 11856395 = 17784593) B17784593
theorem B2468399 : Blo 1644021 2468399 := bstep (se 1 (by rfl) ⟨1851299, by rfl⟩ : syracuseStep 2468399 = 3702599) B3702599
theorem B26692199 : Blo 1644021 26692199 := bstep (se 1 (by rfl) ⟨20019149, by rfl⟩ : syracuseStep 26692199 = 40038299) B40038299
theorem B13347503 : Blo 1644021 13347503 := bstep (se 1 (by rfl) ⟨10010627, by rfl⟩ : syracuseStep 13347503 = 20021255) B20021255
theorem B128248505 : Blo 1644021 128248505 := bstep (se 2 (by rfl) ⟨48093189, by rfl⟩ : syracuseStep 128248505 = 96186379) B96186379
theorem B3164969 : Blo 1644021 3164969 := bstep (se 2 (by rfl) ⟨1186863, by rfl⟩ : syracuseStep 3164969 = 2373727) B2373727
theorem B1756127 : Blo 1644021 1756127 := bstep (se 1 (by rfl) ⟨1317095, by rfl⟩ : syracuseStep 1756127 = 2634191) B2634191
theorem B2468831 : Blo 1644021 2468831 := bstep (se 1 (by rfl) ⟨1851623, by rfl⟩ : syracuseStep 2468831 = 3703247) B3703247
theorem B4222135 : Blo 1644021 4222135 := bstep (se 1 (by rfl) ⟨3166601, by rfl⟩ : syracuseStep 4222135 = 6333203) B6333203
theorem B1756571 : Blo 1644021 1756571 := bstep (se 1 (by rfl) ⟨1317428, by rfl⟩ : syracuseStep 1756571 = 2634857) B2634857
theorem B12488255 : Blo 1644021 12488255 := bstep (se 1 (by rfl) ⟨9366191, by rfl⟩ : syracuseStep 12488255 = 18732383) B18732383
theorem B22498991 : Blo 1644021 22498991 := bstep (se 1 (by rfl) ⟨16874243, by rfl⟩ : syracuseStep 22498991 = 33748487) B33748487
theorem B2633467 : Blo 1644021 2633467 := bstep (se 1 (by rfl) ⟨1975100, by rfl⟩ : syracuseStep 2633467 = 3950201) B3950201
theorem B5001031 : Blo 1644021 5001031 := bstep (se 1 (by rfl) ⟨3750773, by rfl⟩ : syracuseStep 5001031 = 7501547) B7501547
theorem B4165739 : Blo 1644021 4165739 := bstep (se 1 (by rfl) ⟨3124304, by rfl⟩ : syracuseStep 4165739 = 6248609) B6248609
theorem B2535551 : Blo 1644021 2535551 := bstep (se 1 (by rfl) ⟨1901663, by rfl⟩ : syracuseStep 2535551 = 3803327) B3803327
theorem B2634139 : Blo 1644021 2634139 := bstep (se 1 (by rfl) ⟨1975604, by rfl⟩ : syracuseStep 2634139 = 3951209) B3951209
theorem B3699143 : Blo 1644021 3699143 := bstep (se 1 (by rfl) ⟨2774357, by rfl⟩ : syracuseStep 3699143 = 5548715) B5548715
theorem B8327933 : Blo 1644021 8327933 := bstep (se 3 (by rfl) ⟨1561487, by rfl⟩ : syracuseStep 8327933 = 3122975) B3122975
theorem B3699503 : Blo 1644021 3699503 := bstep (se 1 (by rfl) ⟨2774627, by rfl⟩ : syracuseStep 3699503 = 5549255) B5549255
theorem B7902035 : Blo 1644021 7902035 := bstep (se 1 (by rfl) ⟨5926526, by rfl⟩ : syracuseStep 7902035 = 11853053) B11853053
theorem B3699593 : Blo 1644021 3699593 := bstep (se 2 (by rfl) ⟨1387347, by rfl⟩ : syracuseStep 3699593 = 2774695) B2774695
theorem B8328095 : Blo 1644021 8328095 := bstep (se 1 (by rfl) ⟨6246071, by rfl⟩ : syracuseStep 8328095 = 12492143) B12492143
theorem B59356079 : Blo 1644021 59356079 := bstep (se 1 (by rfl) ⟨44517059, by rfl⟩ : syracuseStep 59356079 = 89034119) B89034119
theorem B14242775 : Blo 1644021 14242775 := bstep (se 1 (by rfl) ⟨10682081, by rfl⟩ : syracuseStep 14242775 = 21364163) B21364163
theorem B5551145 : Blo 1644021 5551145 := bstep (se 2 (by rfl) ⟨2081679, by rfl⟩ : syracuseStep 5551145 = 4163359) B4163359
theorem B12497975 : Blo 1644021 12497975 := bstep (se 1 (by rfl) ⟨9373481, by rfl⟩ : syracuseStep 12497975 = 18746963) B18746963
theorem B7025723 : Blo 1644021 7025723 := bstep (se 1 (by rfl) ⟨5269292, by rfl⟩ : syracuseStep 7025723 = 10538585) B10538585
theorem B3511451 : Blo 1644021 3511451 := bstep (se 1 (by rfl) ⟨2633588, by rfl⟩ : syracuseStep 3511451 = 5267177) B5267177
theorem B2815399 : Blo 1644021 2815399 := bstep (se 1 (by rfl) ⟨2111549, by rfl⟩ : syracuseStep 2815399 = 4223099) B4223099
theorem B34207277 : Blo 1644021 34207277 := bstep (se 3 (by rfl) ⟨6413864, by rfl⟩ : syracuseStep 34207277 = 12827729) B12827729
theorem B1644123 : Blo 1644021 1644123 := bstep (se 1 (by rfl) ⟨1233092, by rfl⟩ : syracuseStep 1644123 = 2466185) B2466185
theorem B7501403 : Blo 1644021 7501403 := bstep (se 1 (by rfl) ⟨5626052, by rfl⟩ : syracuseStep 7501403 = 11252105) B11252105
theorem B4683359 : Blo 1644021 4683359 := bstep (se 1 (by rfl) ⟨3512519, by rfl⟩ : syracuseStep 4683359 = 7025039) B7025039
theorem B66795131 : Blo 1644021 66795131 := bstep (se 1 (by rfl) ⟨50096348, by rfl⟩ : syracuseStep 66795131 = 100192697) B100192697
theorem B3700367 : Blo 1644021 3700367 := bstep (se 1 (by rfl) ⟨2775275, by rfl⟩ : syracuseStep 3700367 = 5550551) B5550551
theorem B96196243 : Blo 1644021 96196243 := bstep (se 1 (by rfl) ⟨72147182, by rfl⟩ : syracuseStep 96196243 = 144294365) B144294365
theorem B1644187 : Blo 1644021 1644187 := bstep (se 1 (by rfl) ⟨1233140, by rfl⟩ : syracuseStep 1644187 = 2466281) B2466281
theorem B4749025 : Blo 1644021 4749025 := bstep (se 2 (by rfl) ⟨1780884, by rfl⟩ : syracuseStep 4749025 = 3561769) B3561769
theorem B3700457 : Blo 1644021 3700457 := bstep (se 2 (by rfl) ⟨1387671, by rfl⟩ : syracuseStep 3700457 = 2775343) B2775343
theorem B1644271 : Blo 1644021 1644271 := bstep (se 1 (by rfl) ⟨1233203, by rfl⟩ : syracuseStep 1644271 = 2466407) B2466407
theorem B1644359 : Blo 1644021 1644359 := bstep (se 1 (by rfl) ⟨1233269, by rfl⟩ : syracuseStep 1644359 = 2466539) B2466539
theorem B3512135 : Blo 1644021 3512135 := bstep (se 1 (by rfl) ⟨2634101, by rfl⟩ : syracuseStep 3512135 = 5268203) B5268203
theorem B1644379 : Blo 1644021 1644379 := bstep (se 1 (by rfl) ⟨1233284, by rfl⟩ : syracuseStep 1644379 = 2466569) B2466569
theorem B27047825 : Blo 1644021 27047825 := bstep (se 2 (by rfl) ⟨10142934, by rfl⟩ : syracuseStep 27047825 = 20285869) B20285869
theorem B1644447 : Blo 1644021 1644447 := bstep (se 1 (by rfl) ⟨1233335, by rfl⟩ : syracuseStep 1644447 = 2466671) B2466671
theorem B6248411 : Blo 1644021 6248411 := bstep (se 1 (by rfl) ⟨4686308, by rfl⟩ : syracuseStep 6248411 = 9372617) B9372617
theorem B6248441 : Blo 1644021 6248441 := bstep (se 2 (by rfl) ⟨2343165, by rfl⟩ : syracuseStep 6248441 = 4686331) B4686331
theorem B1644615 : Blo 1644021 1644615 := bstep (se 1 (by rfl) ⟨1233461, by rfl⟩ : syracuseStep 1644615 = 2466923) B2466923
theorem B15808607 : Blo 1644021 15808607 := bstep (se 1 (by rfl) ⟨11856455, by rfl⟩ : syracuseStep 15808607 = 23712911) B23712911
theorem B8009927 : Blo 1644021 8009927 := bstep (se 1 (by rfl) ⟨6007445, by rfl⟩ : syracuseStep 8009927 = 12014891) B12014891
theorem B1644775 : Blo 1644021 1644775 := bstep (se 1 (by rfl) ⟨1233581, by rfl⟩ : syracuseStep 1644775 = 2467163) B2467163
theorem B1644959 : Blo 1644021 1644959 := bstep (se 1 (by rfl) ⟨1233719, by rfl⟩ : syracuseStep 1644959 = 2467439) B2467439
theorem B6666695 : Blo 1644021 6666695 := bstep (se 1 (by rfl) ⟨5000021, by rfl⟩ : syracuseStep 6666695 = 10000043) B10000043
theorem B1645007 : Blo 1644021 1645007 := bstep (se 1 (by rfl) ⟨1233755, by rfl⟩ : syracuseStep 1645007 = 2467511) B2467511
theorem B1645031 : Blo 1644021 1645031 := bstep (se 1 (by rfl) ⟨1233773, by rfl⟩ : syracuseStep 1645031 = 2467547) B2467547
theorem B3701339 : Blo 1644021 3701339 := bstep (se 1 (by rfl) ⟨2776004, by rfl⟩ : syracuseStep 3701339 = 5552009) B5552009
theorem B1645147 : Blo 1644021 1645147 := bstep (se 1 (by rfl) ⟨1233860, by rfl⟩ : syracuseStep 1645147 = 2467721) B2467721
theorem B1645215 : Blo 1644021 1645215 := bstep (se 1 (by rfl) ⟨1233911, by rfl⟩ : syracuseStep 1645215 = 2467823) B2467823
theorem B5552873 : Blo 1644021 5552873 := bstep (se 2 (by rfl) ⟨2082327, by rfl⟩ : syracuseStep 5552873 = 4164655) B4164655
theorem B3701483 : Blo 1644021 3701483 := bstep (se 1 (by rfl) ⟨2776112, by rfl⟩ : syracuseStep 3701483 = 5552225) B5552225
theorem B14047991 : Blo 1644021 14047991 := bstep (se 1 (by rfl) ⟨10535993, by rfl⟩ : syracuseStep 14047991 = 21071987) B21071987
theorem B25328375 : Blo 1644021 25328375 := bstep (se 1 (by rfl) ⟨18996281, by rfl⟩ : syracuseStep 25328375 = 37992563) B37992563
theorem B7027499 : Blo 1644021 7027499 := bstep (se 1 (by rfl) ⟨5270624, by rfl⟩ : syracuseStep 7027499 = 10541249) B10541249
theorem B1645383 : Blo 1644021 1645383 := bstep (se 1 (by rfl) ⟨1234037, by rfl⟩ : syracuseStep 1645383 = 2468075) B2468075
theorem B32037743 : Blo 1644021 32037743 := bstep (se 1 (by rfl) ⟨24028307, by rfl⟩ : syracuseStep 32037743 = 48056615) B48056615
theorem B1645423 : Blo 1644021 1645423 := bstep (se 1 (by rfl) ⟨1234067, by rfl⟩ : syracuseStep 1645423 = 2468135) B2468135
theorem B1645479 : Blo 1644021 1645479 := bstep (se 1 (by rfl) ⟨1234109, by rfl⟩ : syracuseStep 1645479 = 2468219) B2468219
theorem B1645659 : Blo 1644021 1645659 := bstep (se 1 (by rfl) ⟨1234244, by rfl⟩ : syracuseStep 1645659 = 2468489) B2468489
theorem B1850575 : Blo 1644021 1850575 := bstep (se 1 (by rfl) ⟨1387931, by rfl⟩ : syracuseStep 1850575 = 2775863) B2775863
theorem B1645775 : Blo 1644021 1645775 := bstep (se 1 (by rfl) ⟨1234331, by rfl⟩ : syracuseStep 1645775 = 2468663) B2468663
theorem B1645799 : Blo 1644021 1645799 := bstep (se 1 (by rfl) ⟨1234349, by rfl⟩ : syracuseStep 1645799 = 2468699) B2468699
theorem B18742589 : Blo 1644021 18742589 := bstep (se 3 (by rfl) ⟨3514235, by rfl⟩ : syracuseStep 18742589 = 7028471) B7028471
theorem B1645895 : Blo 1644021 1645895 := bstep (se 1 (by rfl) ⟨1234421, by rfl⟩ : syracuseStep 1645895 = 2468843) B2468843
theorem B3702095 : Blo 1644021 3702095 := bstep (se 1 (by rfl) ⟨2776571, by rfl⟩ : syracuseStep 3702095 = 5553143) B5553143
theorem B3702185 : Blo 1644021 3702185 := bstep (se 2 (by rfl) ⟨1388319, by rfl⟩ : syracuseStep 3702185 = 2776639) B2776639
theorem B3513775 : Blo 1644021 3513775 := bstep (se 1 (by rfl) ⟨2635331, by rfl⟩ : syracuseStep 3513775 = 5270663) B5270663
theorem B3702383 : Blo 1644021 3702383 := bstep (se 1 (by rfl) ⟨2776787, by rfl⟩ : syracuseStep 3702383 = 5553575) B5553575
theorem B10534711 : Blo 1644021 10534711 := bstep (se 1 (by rfl) ⟨7901033, by rfl⟩ : syracuseStep 10534711 = 15802067) B15802067
theorem B2776943 : Blo 1644021 2776943 := bstep (se 1 (by rfl) ⟨2082707, by rfl⟩ : syracuseStep 2776943 = 4165415) B4165415
theorem B3702671 : Blo 1644021 3702671 := bstep (se 1 (by rfl) ⟨2777003, by rfl⟩ : syracuseStep 3702671 = 5554007) B5554007
theorem B2777159 : Blo 1644021 2777159 := bstep (se 1 (by rfl) ⟨2082869, by rfl⟩ : syracuseStep 2777159 = 4165739) B4165739
theorem B10010839 : Blo 1644021 10010839 := bstep (se 1 (by rfl) ⟨7508129, by rfl⟩ : syracuseStep 10010839 = 15016259) B15016259
theorem B5554439 : Blo 1644021 5554439 := bstep (se 1 (by rfl) ⟨4165829, by rfl⟩ : syracuseStep 5554439 = 8331659) B8331659
theorem B2466095 : Blo 1644021 2466095 := bstep (se 1 (by rfl) ⟨1849571, by rfl⟩ : syracuseStep 2466095 = 3699143) B3699143
theorem B9363869 : Blo 1644021 9363869 := bstep (se 3 (by rfl) ⟨1755725, by rfl⟩ : syracuseStep 9363869 = 3511451) B3511451
theorem B2466335 : Blo 1644021 2466335 := bstep (se 1 (by rfl) ⟨1849751, by rfl⟩ : syracuseStep 2466335 = 3699503) B3699503
theorem B5268023 : Blo 1644021 5268023 := bstep (se 1 (by rfl) ⟨3951017, by rfl⟩ : syracuseStep 5268023 = 7902035) B7902035
theorem B2466395 : Blo 1644021 2466395 := bstep (se 1 (by rfl) ⟨1849796, by rfl⟩ : syracuseStep 2466395 = 3699593) B3699593
theorem B3703463 : Blo 1644021 3703463 := bstep (se 1 (by rfl) ⟨2777597, by rfl⟩ : syracuseStep 3703463 = 5555195) B5555195
theorem B8331983 : Blo 1644021 8331983 := bstep (se 1 (by rfl) ⟨6248987, by rfl⟩ : syracuseStep 8331983 = 12497975) B12497975
theorem B3122239 : Blo 1644021 3122239 := bstep (se 1 (by rfl) ⟨2341679, by rfl⟩ : syracuseStep 3122239 = 4683359) B4683359
theorem B2466911 : Blo 1644021 2466911 := bstep (se 1 (by rfl) ⟨1850183, by rfl⟩ : syracuseStep 2466911 = 3700367) B3700367
theorem B2466971 : Blo 1644021 2466971 := bstep (se 1 (by rfl) ⟨1850228, by rfl⟩ : syracuseStep 2466971 = 3700457) B3700457
theorem B4162873 : Blo 1644021 4162873 := bstep (se 2 (by rfl) ⟨1561077, by rfl⟩ : syracuseStep 4162873 = 3122155) B3122155
theorem B5268893 : Blo 1644021 5268893 := bstep (se 3 (by rfl) ⟨987917, by rfl⟩ : syracuseStep 5268893 = 1975835) B1975835
theorem B91219405 : Blo 1644021 91219405 := bstep (se 3 (by rfl) ⟨17103638, by rfl⟩ : syracuseStep 91219405 = 34207277) B34207277
theorem B5629513 : Blo 1644021 5629513 := bstep (se 2 (by rfl) ⟨2111067, by rfl⟩ : syracuseStep 5629513 = 4222135) B4222135
theorem B2467433 : Blo 1644021 2467433 := bstep (se 2 (by rfl) ⟨925287, by rfl⟩ : syracuseStep 2467433 = 1850575) B1850575
theorem B18736757 : Blo 1644021 18736757 := bstep (se 5 (by rfl) ⟨878285, by rfl⟩ : syracuseStep 18736757 = 1756571) B1756571
theorem B178120349 : Blo 1644021 178120349 := bstep (se 3 (by rfl) ⟨33397565, by rfl⟩ : syracuseStep 178120349 = 66795131) B66795131
theorem B12486311 : Blo 1644021 12486311 := bstep (se 1 (by rfl) ⟨9364733, by rfl⟩ : syracuseStep 12486311 = 18729467) B18729467
theorem B2467559 : Blo 1644021 2467559 := bstep (se 1 (by rfl) ⟨1850669, by rfl⟩ : syracuseStep 2467559 = 3701339) B3701339
theorem B17794799 : Blo 1644021 17794799 := bstep (se 1 (by rfl) ⟨13346099, by rfl⟩ : syracuseStep 17794799 = 26692199) B26692199
theorem B8898335 : Blo 1644021 8898335 := bstep (se 1 (by rfl) ⟨6673751, by rfl⟩ : syracuseStep 8898335 = 13347503) B13347503
theorem B2467655 : Blo 1644021 2467655 := bstep (se 1 (by rfl) ⟨1850741, by rfl⟩ : syracuseStep 2467655 = 3701483) B3701483
theorem B9365327 : Blo 1644021 9365327 := bstep (se 1 (by rfl) ⟨7023995, by rfl⟩ : syracuseStep 9365327 = 14047991) B14047991
theorem B16885583 : Blo 1644021 16885583 := bstep (se 1 (by rfl) ⟨12664187, by rfl⟩ : syracuseStep 16885583 = 25328375) B25328375
theorem B3753865 : Blo 1644021 3753865 := bstep (se 2 (by rfl) ⟨1407699, by rfl⟩ : syracuseStep 3753865 = 2815399) B2815399
theorem B21358495 : Blo 1644021 21358495 := bstep (se 1 (by rfl) ⟨16018871, by rfl⟩ : syracuseStep 21358495 = 32037743) B32037743
theorem B2532526037 : Blo 1644021 2532526037 := bstep (se 7 (by rfl) ⟨29678039, by rfl⟩ : syracuseStep 2532526037 = 59356079) B59356079
theorem B12495059 : Blo 1644021 12495059 := bstep (se 1 (by rfl) ⟨9371294, by rfl⟩ : syracuseStep 12495059 = 18742589) B18742589
theorem B2468063 : Blo 1644021 2468063 := bstep (se 1 (by rfl) ⟨1851047, by rfl⟩ : syracuseStep 2468063 = 3702095) B3702095
theorem B2468123 : Blo 1644021 2468123 := bstep (se 1 (by rfl) ⟨1851092, by rfl⟩ : syracuseStep 2468123 = 3702185) B3702185
theorem B8325503 : Blo 1644021 8325503 := bstep (se 1 (by rfl) ⟨6244127, by rfl⟩ : syracuseStep 8325503 = 12488255) B12488255
theorem B2468255 : Blo 1644021 2468255 := bstep (se 1 (by rfl) ⟨1851191, by rfl⟩ : syracuseStep 2468255 = 3702383) B3702383
theorem B37980733 : Blo 1644021 37980733 := bstep (se 3 (by rfl) ⟨7121387, by rfl⟩ : syracuseStep 37980733 = 14242775) B14242775
theorem B2468447 : Blo 1644021 2468447 := bstep (se 1 (by rfl) ⟨1851335, by rfl⟩ : syracuseStep 2468447 = 3702671) B3702671
theorem B26684153 : Blo 1644021 26684153 := bstep (se 2 (by rfl) ⟨10006557, by rfl⟩ : syracuseStep 26684153 = 20013115) B20013115
theorem B1690367 : Blo 1644021 1690367 := bstep (se 1 (by rfl) ⟨1267775, by rfl⟩ : syracuseStep 1690367 = 2535551) B2535551
theorem B2468777 : Blo 1644021 2468777 := bstep (se 2 (by rfl) ⟨925791, by rfl⟩ : syracuseStep 2468777 = 1851583) B1851583
theorem B2468807 : Blo 1644021 2468807 := bstep (se 1 (by rfl) ⟨1851605, by rfl⟩ : syracuseStep 2468807 = 3703211) B3703211
theorem B2468927 : Blo 1644021 2468927 := bstep (se 1 (by rfl) ⟨1851695, by rfl⟩ : syracuseStep 2468927 = 3703391) B3703391
theorem B8326637 : Blo 1644021 8326637 := bstep (se 3 (by rfl) ⟨1561244, by rfl⟩ : syracuseStep 8326637 = 3122489) B3122489
theorem B5271047 : Blo 1644021 5271047 := bstep (se 1 (by rfl) ⟨3953285, by rfl⟩ : syracuseStep 5271047 = 7906571) B7906571
theorem B5000935 : Blo 1644021 5000935 := bstep (se 1 (by rfl) ⟨3750701, by rfl⟩ : syracuseStep 5000935 = 7501403) B7501403
theorem B14053115 : Blo 1644021 14053115 := bstep (se 1 (by rfl) ⟨10539836, by rfl⟩ : syracuseStep 14053115 = 21079673) B21079673
theorem B4165607 : Blo 1644021 4165607 := bstep (se 1 (by rfl) ⟨3124205, by rfl⟩ : syracuseStep 4165607 = 6248411) B6248411
theorem B4165627 : Blo 1644021 4165627 := bstep (se 1 (by rfl) ⟨3124220, by rfl⟩ : syracuseStep 4165627 = 6248441) B6248441
theorem B10539071 : Blo 1644021 10539071 := bstep (se 1 (by rfl) ⟨7904303, by rfl⟩ : syracuseStep 10539071 = 15808607) B15808607
theorem B288510133 : Blo 1644021 288510133 := bstep (se 5 (by rfl) ⟨13523912, by rfl⟩ : syracuseStep 288510133 = 27047825) B27047825
theorem B4444463 : Blo 1644021 4444463 := bstep (se 1 (by rfl) ⟨3333347, by rfl⟩ : syracuseStep 4444463 = 6666695) B6666695
theorem B2109979 : Blo 1644021 2109979 := bstep (se 1 (by rfl) ⟨1582484, by rfl⟩ : syracuseStep 2109979 = 3164969) B3164969
theorem B3511289 : Blo 1644021 3511289 := bstep (se 2 (by rfl) ⟨1316733, by rfl⟩ : syracuseStep 3511289 = 2633467) B2633467
theorem B14046281 : Blo 1644021 14046281 := bstep (se 2 (by rfl) ⟨5267355, by rfl⟩ : syracuseStep 14046281 = 10534711) B10534711
theorem B4683005 : Blo 1644021 4683005 := bstep (se 3 (by rfl) ⟨878063, by rfl⟩ : syracuseStep 4683005 = 1756127) B1756127
theorem B12490199 : Blo 1644021 12490199 := bstep (se 1 (by rfl) ⟨9367649, by rfl⟩ : syracuseStep 12490199 = 18735299) B18735299
theorem B1644031 : Blo 1644021 1644031 := bstep (se 1 (by rfl) ⟨1233023, by rfl⟩ : syracuseStep 1644031 = 2466047) B2466047
theorem B15816521 : Blo 1644021 15816521 := bstep (se 2 (by rfl) ⟨5931195, by rfl⟩ : syracuseStep 15816521 = 11862391) B11862391
theorem B5551955 : Blo 1644021 5551955 := bstep (se 1 (by rfl) ⟨4163966, by rfl⟩ : syracuseStep 5551955 = 8327933) B8327933
theorem B5552063 : Blo 1644021 5552063 := bstep (se 1 (by rfl) ⟨4164047, by rfl⟩ : syracuseStep 5552063 = 8328095) B8328095
theorem B3700763 : Blo 1644021 3700763 := bstep (se 1 (by rfl) ⟨2775572, by rfl⟩ : syracuseStep 3700763 = 5551145) B5551145
theorem B1644575 : Blo 1644021 1644575 := bstep (se 1 (by rfl) ⟨1233431, by rfl⟩ : syracuseStep 1644575 = 2466863) B2466863
theorem B4683815 : Blo 1644021 4683815 := bstep (se 1 (by rfl) ⟨3512861, by rfl⟩ : syracuseStep 4683815 = 7025723) B7025723
theorem B1644655 : Blo 1644021 1644655 := bstep (se 1 (by rfl) ⟨1233491, by rfl⟩ : syracuseStep 1644655 = 2466983) B2466983
theorem B15816829 : Blo 1644021 15816829 := bstep (se 3 (by rfl) ⟨2965655, by rfl⟩ : syracuseStep 15816829 = 5931311) B5931311
theorem B1644903 : Blo 1644021 1644903 := bstep (se 1 (by rfl) ⟨1233677, by rfl⟩ : syracuseStep 1644903 = 2467355) B2467355
theorem B2775451 : Blo 1644021 2775451 := bstep (se 1 (by rfl) ⟨2081588, by rfl⟩ : syracuseStep 2775451 = 4163177) B4163177
theorem B2341423 : Blo 1644021 2341423 := bstep (se 1 (by rfl) ⟨1756067, by rfl⟩ : syracuseStep 2341423 = 3512135) B3512135
theorem B2775647 : Blo 1644021 2775647 := bstep (se 1 (by rfl) ⟨2081735, by rfl⟩ : syracuseStep 2775647 = 4163471) B4163471
theorem B1645159 : Blo 1644021 1645159 := bstep (se 1 (by rfl) ⟨1233869, by rfl⟩ : syracuseStep 1645159 = 2467739) B2467739
theorem B1645183 : Blo 1644021 1645183 := bstep (se 1 (by rfl) ⟨1233887, by rfl⟩ : syracuseStep 1645183 = 2467775) B2467775
theorem B5003963 : Blo 1644021 5003963 := bstep (se 1 (by rfl) ⟨3752972, by rfl⟩ : syracuseStep 5003963 = 7505945) B7505945
theorem B1645307 : Blo 1644021 1645307 := bstep (se 1 (by rfl) ⟨1233980, by rfl⟩ : syracuseStep 1645307 = 2467961) B2467961
theorem B5339951 : Blo 1644021 5339951 := bstep (se 1 (by rfl) ⟨4004963, by rfl⟩ : syracuseStep 5339951 = 8009927) B8009927
theorem B1645563 : Blo 1644021 1645563 := bstep (se 1 (by rfl) ⟨1234172, by rfl⟩ : syracuseStep 1645563 = 2468345) B2468345
theorem B7904263 : Blo 1644021 7904263 := bstep (se 1 (by rfl) ⟨5928197, by rfl⟩ : syracuseStep 7904263 = 11856395) B11856395
theorem B1645599 : Blo 1644021 1645599 := bstep (se 1 (by rfl) ⟨1234199, by rfl⟩ : syracuseStep 1645599 = 2468399) B2468399
theorem B85499003 : Blo 1644021 85499003 := bstep (se 1 (by rfl) ⟨64124252, by rfl⟩ : syracuseStep 85499003 = 128248505) B128248505
theorem B3701915 : Blo 1644021 3701915 := bstep (se 1 (by rfl) ⟨2776436, by rfl⟩ : syracuseStep 3701915 = 5552873) B5552873
theorem B4684999 : Blo 1644021 4684999 := bstep (se 1 (by rfl) ⟨3513749, by rfl⟩ : syracuseStep 4684999 = 7027499) B7027499
theorem B4685033 : Blo 1644021 4685033 := bstep (se 2 (by rfl) ⟨1756887, by rfl⟩ : syracuseStep 4685033 = 3513775) B3513775
theorem B1645887 : Blo 1644021 1645887 := bstep (se 1 (by rfl) ⟨1234415, by rfl⟩ : syracuseStep 1645887 = 2468831) B2468831
theorem B14048741 : Blo 1644021 14048741 := bstep (se 4 (by rfl) ⟨1317069, by rfl⟩ : syracuseStep 14048741 = 2634139) B2634139
theorem B128261657 : Blo 1644021 128261657 := bstep (se 2 (by rfl) ⟨48098121, by rfl⟩ : syracuseStep 128261657 = 96196243) B96196243
theorem B6332033 : Blo 1644021 6332033 := bstep (se 2 (by rfl) ⟨2374512, by rfl⟩ : syracuseStep 6332033 = 4749025) B4749025
theorem B6668041 : Blo 1644021 6668041 := bstep (se 2 (by rfl) ⟨2500515, by rfl⟩ : syracuseStep 6668041 = 5001031) B5001031
theorem B14999327 : Blo 1644021 14999327 := bstep (se 1 (by rfl) ⟨11249495, by rfl⟩ : syracuseStep 14999327 = 22498991) B22498991
theorem B1851295 : Blo 1644021 1851295 := bstep (se 1 (by rfl) ⟨1388471, by rfl⟩ : syracuseStep 1851295 = 2776943) B2776943
theorem B1851439 : Blo 1644021 1851439 := bstep (se 1 (by rfl) ⟨1388579, by rfl⟩ : syracuseStep 1851439 = 2777159) B2777159
theorem B3702959 : Blo 1644021 3702959 := bstep (se 1 (by rfl) ⟨2777219, by rfl⟩ : syracuseStep 3702959 = 5554439) B5554439
theorem B384680177 : Blo 1644021 384680177 := bstep (se 2 (by rfl) ⟨144255066, by rfl⟩ : syracuseStep 384680177 = 288510133) B288510133
theorem B6242579 : Blo 1644021 6242579 := bstep (se 1 (by rfl) ⟨4681934, by rfl⟩ : syracuseStep 6242579 = 9363869) B9363869
theorem B5554655 : Blo 1644021 5554655 := bstep (se 1 (by rfl) ⟨4165991, by rfl⟩ : syracuseStep 5554655 = 8331983) B8331983
theorem B9364187 : Blo 1644021 9364187 := bstep (se 1 (by rfl) ⟨7023140, by rfl⟩ : syracuseStep 9364187 = 14046281) B14046281
theorem B3121897 : Blo 1644021 3121897 := bstep (se 2 (by rfl) ⟨1170711, by rfl⟩ : syracuseStep 3121897 = 2341423) B2341423
theorem B3122003 : Blo 1644021 3122003 := bstep (se 1 (by rfl) ⟨2341502, by rfl⟩ : syracuseStep 3122003 = 4683005) B4683005
theorem B14050381 : Blo 1644021 14050381 := bstep (se 3 (by rfl) ⟨2634446, by rfl⟩ : syracuseStep 14050381 = 5268893) B5268893
theorem B8324207 : Blo 1644021 8324207 := bstep (se 1 (by rfl) ⟨6243155, by rfl⟩ : syracuseStep 8324207 = 12486311) B12486311
theorem B11863199 : Blo 1644021 11863199 := bstep (se 1 (by rfl) ⟨8897399, by rfl⟩ : syracuseStep 11863199 = 17794799) B17794799
theorem B5932223 : Blo 1644021 5932223 := bstep (se 1 (by rfl) ⟨4449167, by rfl⟩ : syracuseStep 5932223 = 8898335) B8898335
theorem B10544347 : Blo 1644021 10544347 := bstep (se 1 (by rfl) ⟨7908260, by rfl⟩ : syracuseStep 10544347 = 15816521) B15816521
theorem B6243551 : Blo 1644021 6243551 := bstep (se 1 (by rfl) ⟨4682663, by rfl⟩ : syracuseStep 6243551 = 9365327) B9365327
theorem B11257055 : Blo 1644021 11257055 := bstep (se 1 (by rfl) ⟨8442791, by rfl⟩ : syracuseStep 11257055 = 16885583) B16885583
theorem B2467175 : Blo 1644021 2467175 := bstep (se 1 (by rfl) ⟨1850381, by rfl⟩ : syracuseStep 2467175 = 3700763) B3700763
theorem B3122543 : Blo 1644021 3122543 := bstep (se 1 (by rfl) ⟨2341907, by rfl⟩ : syracuseStep 3122543 = 4683815) B4683815
theorem B4162985 : Blo 1644021 4162985 := bstep (se 2 (by rfl) ⟨1561119, by rfl⟩ : syracuseStep 4162985 = 3122239) B3122239
theorem B5554169 : Blo 1644021 5554169 := bstep (se 2 (by rfl) ⟨2082813, by rfl⟩ : syracuseStep 5554169 = 4165627) B4165627
theorem B3335975 : Blo 1644021 3335975 := bstep (se 1 (by rfl) ⟨2501981, by rfl⟩ : syracuseStep 3335975 = 5003963) B5003963
theorem B4507645 : Blo 1644021 4507645 := bstep (se 3 (by rfl) ⟨845183, by rfl⟩ : syracuseStep 4507645 = 1690367) B1690367
theorem B7506017 : Blo 1644021 7506017 := bstep (se 2 (by rfl) ⟨2814756, by rfl⟩ : syracuseStep 7506017 = 5629513) B5629513
theorem B2467943 : Blo 1644021 2467943 := bstep (se 1 (by rfl) ⟨1850957, by rfl⟩ : syracuseStep 2467943 = 3701915) B3701915
theorem B3123355 : Blo 1644021 3123355 := bstep (se 1 (by rfl) ⟨2342516, by rfl⟩ : syracuseStep 3123355 = 4685033) B4685033
theorem B9365827 : Blo 1644021 9365827 := bstep (se 1 (by rfl) ⟨7024370, by rfl⟩ : syracuseStep 9365827 = 14048741) B14048741
theorem B8890721 : Blo 1644021 8890721 := bstep (se 2 (by rfl) ⟨3334020, by rfl⟩ : syracuseStep 8890721 = 6668041) B6668041
theorem B4221355 : Blo 1644021 4221355 := bstep (se 1 (by rfl) ⟨3166016, by rfl⟩ : syracuseStep 4221355 = 6332033) B6332033
theorem B28477993 : Blo 1644021 28477993 := bstep (se 2 (by rfl) ⟨10679247, by rfl⟩ : syracuseStep 28477993 = 21358495) B21358495
theorem B2468393 : Blo 1644021 2468393 := bstep (se 2 (by rfl) ⟨925647, by rfl⟩ : syracuseStep 2468393 = 1851295) B1851295
theorem B21089105 : Blo 1644021 21089105 := bstep (se 2 (by rfl) ⟨7908414, by rfl⟩ : syracuseStep 21089105 = 15816829) B15816829
theorem B13347785 : Blo 1644021 13347785 := bstep (se 2 (by rfl) ⟨5005419, by rfl⟩ : syracuseStep 13347785 = 10010839) B10010839
theorem B2468975 : Blo 1644021 2468975 := bstep (se 1 (by rfl) ⟨1851731, by rfl⟩ : syracuseStep 2468975 = 3703463) B3703463
theorem B2813305 : Blo 1644021 2813305 := bstep (se 2 (by rfl) ⟨1054989, by rfl⟩ : syracuseStep 2813305 = 2109979) B2109979
theorem B8326799 : Blo 1644021 8326799 := bstep (se 1 (by rfl) ⟨6245099, by rfl⟩ : syracuseStep 8326799 = 12490199) B12490199
theorem B118746899 : Blo 1644021 118746899 := bstep (se 1 (by rfl) ⟨89060174, by rfl⟩ : syracuseStep 118746899 = 178120349) B178120349
theorem B1688350691 : Blo 1644021 1688350691 := bstep (se 1 (by rfl) ⟨1266263018, by rfl⟩ : syracuseStep 1688350691 = 2532526037) B2532526037
theorem B10539017 : Blo 1644021 10539017 := bstep (se 2 (by rfl) ⟨3952131, by rfl⟩ : syracuseStep 10539017 = 7904263) B7904263
theorem B5550335 : Blo 1644021 5550335 := bstep (se 1 (by rfl) ⟨4162751, by rfl⟩ : syracuseStep 5550335 = 8325503) B8325503
theorem B6246665 : Blo 1644021 6246665 := bstep (se 2 (by rfl) ⟨2342499, by rfl⟩ : syracuseStep 6246665 = 4684999) B4684999
theorem B5550497 : Blo 1644021 5550497 := bstep (se 2 (by rfl) ⟨2081436, by rfl⟩ : syracuseStep 5550497 = 4162873) B4162873
theorem B17789435 : Blo 1644021 17789435 := bstep (se 1 (by rfl) ⟨13342076, by rfl⟩ : syracuseStep 17789435 = 26684153) B26684153
theorem B3559967 : Blo 1644021 3559967 := bstep (se 1 (by rfl) ⟨2669975, by rfl⟩ : syracuseStep 3559967 = 5339951) B5339951
theorem B5551091 : Blo 1644021 5551091 := bstep (se 1 (by rfl) ⟨4163318, by rfl⟩ : syracuseStep 5551091 = 8326637) B8326637
theorem B9368743 : Blo 1644021 9368743 := bstep (se 1 (by rfl) ⟨7026557, by rfl⟩ : syracuseStep 9368743 = 14053115) B14053115
theorem B9999551 : Blo 1644021 9999551 := bstep (se 1 (by rfl) ⟨7499663, by rfl⟩ : syracuseStep 9999551 = 14999327) B14999327
theorem B7026047 : Blo 1644021 7026047 := bstep (se 1 (by rfl) ⟨5269535, by rfl⟩ : syracuseStep 7026047 = 10539071) B10539071
theorem B1644063 : Blo 1644021 1644063 := bstep (se 1 (by rfl) ⟨1233047, by rfl⟩ : syracuseStep 1644063 = 2466095) B2466095
theorem B2962975 : Blo 1644021 2962975 := bstep (se 1 (by rfl) ⟨2222231, by rfl⟩ : syracuseStep 2962975 = 4444463) B4444463
theorem B227997341 : Blo 1644021 227997341 := bstep (se 3 (by rfl) ⟨42749501, by rfl⟩ : syracuseStep 227997341 = 85499003) B85499003
theorem B1644223 : Blo 1644021 1644223 := bstep (se 1 (by rfl) ⟨1233167, by rfl⟩ : syracuseStep 1644223 = 2466335) B2466335
theorem B3512015 : Blo 1644021 3512015 := bstep (se 1 (by rfl) ⟨2634011, by rfl⟩ : syracuseStep 3512015 = 5268023) B5268023
theorem B1644263 : Blo 1644021 1644263 := bstep (se 1 (by rfl) ⟨1233197, by rfl⟩ : syracuseStep 1644263 = 2466395) B2466395
theorem B3700601 : Blo 1644021 3700601 := bstep (se 2 (by rfl) ⟨1387725, by rfl⟩ : syracuseStep 3700601 = 2775451) B2775451
theorem B1644607 : Blo 1644021 1644607 := bstep (se 1 (by rfl) ⟨1233455, by rfl⟩ : syracuseStep 1644607 = 2466911) B2466911
theorem B50640977 : Blo 1644021 50640977 := bstep (se 2 (by rfl) ⟨18990366, by rfl⟩ : syracuseStep 50640977 = 37980733) B37980733
theorem B1644647 : Blo 1644021 1644647 := bstep (se 1 (by rfl) ⟨1233485, by rfl⟩ : syracuseStep 1644647 = 2466971) B2466971
theorem B1644955 : Blo 1644021 1644955 := bstep (se 1 (by rfl) ⟨1233716, by rfl⟩ : syracuseStep 1644955 = 2467433) B2467433
theorem B12491171 : Blo 1644021 12491171 := bstep (se 1 (by rfl) ⟨9368378, by rfl⟩ : syracuseStep 12491171 = 18736757) B18736757
theorem B1645039 : Blo 1644021 1645039 := bstep (se 1 (by rfl) ⟨1233779, by rfl⟩ : syracuseStep 1645039 = 2467559) B2467559
theorem B1645103 : Blo 1644021 1645103 := bstep (se 1 (by rfl) ⟨1233827, by rfl⟩ : syracuseStep 1645103 = 2467655) B2467655
theorem B3701303 : Blo 1644021 3701303 := bstep (se 1 (by rfl) ⟨2775977, by rfl⟩ : syracuseStep 3701303 = 5551955) B5551955
theorem B3701375 : Blo 1644021 3701375 := bstep (se 1 (by rfl) ⟨2776031, by rfl⟩ : syracuseStep 3701375 = 5552063) B5552063
theorem B8330039 : Blo 1644021 8330039 := bstep (se 1 (by rfl) ⟨6247529, by rfl⟩ : syracuseStep 8330039 = 12495059) B12495059
theorem B1645375 : Blo 1644021 1645375 := bstep (se 1 (by rfl) ⟨1234031, by rfl⟩ : syracuseStep 1645375 = 2468063) B2468063
theorem B1645415 : Blo 1644021 1645415 := bstep (se 1 (by rfl) ⟨1234061, by rfl⟩ : syracuseStep 1645415 = 2468123) B2468123
theorem B1645503 : Blo 1644021 1645503 := bstep (se 1 (by rfl) ⟨1234127, by rfl⟩ : syracuseStep 1645503 = 2468255) B2468255
theorem B1850431 : Blo 1644021 1850431 := bstep (se 1 (by rfl) ⟨1387823, by rfl⟩ : syracuseStep 1850431 = 2775647) B2775647
theorem B1645631 : Blo 1644021 1645631 := bstep (se 1 (by rfl) ⟨1234223, by rfl⟩ : syracuseStep 1645631 = 2468447) B2468447
theorem B121625873 : Blo 1644021 121625873 := bstep (se 2 (by rfl) ⟨45609702, by rfl⟩ : syracuseStep 121625873 = 91219405) B91219405
theorem B1645851 : Blo 1644021 1645851 := bstep (se 1 (by rfl) ⟨1234388, by rfl⟩ : syracuseStep 1645851 = 2468777) B2468777
theorem B1645871 : Blo 1644021 1645871 := bstep (se 1 (by rfl) ⟨1234403, by rfl⟩ : syracuseStep 1645871 = 2468807) B2468807
theorem B1645951 : Blo 1644021 1645951 := bstep (se 1 (by rfl) ⟨1234463, by rfl⟩ : syracuseStep 1645951 = 2468927) B2468927
theorem B6667913 : Blo 1644021 6667913 := bstep (se 2 (by rfl) ⟨2500467, by rfl⟩ : syracuseStep 6667913 = 5000935) B5000935
theorem B3514031 : Blo 1644021 3514031 := bstep (se 1 (by rfl) ⟨2635523, by rfl⟩ : syracuseStep 3514031 = 5271047) B5271047
theorem B85507771 : Blo 1644021 85507771 := bstep (se 1 (by rfl) ⟨64130828, by rfl⟩ : syracuseStep 85507771 = 128261657) B128261657
theorem B5005153 : Blo 1644021 5005153 := bstep (se 2 (by rfl) ⟨1876932, by rfl⟩ : syracuseStep 5005153 = 3753865) B3753865
theorem B9363437 : Blo 1644021 9363437 := bstep (se 3 (by rfl) ⟨1755644, by rfl⟩ : syracuseStep 9363437 = 3511289) B3511289
theorem B2777071 : Blo 1644021 2777071 := bstep (se 1 (by rfl) ⟨2082803, by rfl⟩ : syracuseStep 2777071 = 4165607) B4165607
theorem B4161719 : Blo 1644021 4161719 := bstep (se 1 (by rfl) ⟨3121289, by rfl⟩ : syracuseStep 4161719 = 6242579) B6242579
theorem B3703103 : Blo 1644021 3703103 := bstep (se 1 (by rfl) ⟨2777327, by rfl⟩ : syracuseStep 3703103 = 5554655) B5554655
theorem B6242791 : Blo 1644021 6242791 := bstep (se 1 (by rfl) ⟨4682093, by rfl⟩ : syracuseStep 6242791 = 9364187) B9364187
theorem B26665469 : Blo 1644021 26665469 := bstep (se 3 (by rfl) ⟨4999775, by rfl⟩ : syracuseStep 26665469 = 9999551) B9999551
theorem B5628473 : Blo 1644021 5628473 := bstep (se 2 (by rfl) ⟨2110677, by rfl⟩ : syracuseStep 5628473 = 4221355) B4221355
theorem B37970657 : Blo 1644021 37970657 := bstep (se 2 (by rfl) ⟨14238996, by rfl⟩ : syracuseStep 37970657 = 28477993) B28477993
theorem B4162367 : Blo 1644021 4162367 := bstep (se 1 (by rfl) ⟨3121775, by rfl⟩ : syracuseStep 4162367 = 6243551) B6243551
theorem B7504703 : Blo 1644021 7504703 := bstep (se 1 (by rfl) ⟨5628527, by rfl⟩ : syracuseStep 7504703 = 11257055) B11257055
theorem B2081695 : Blo 1644021 2081695 := bstep (se 1 (by rfl) ⟨1561271, by rfl⟩ : syracuseStep 2081695 = 3122543) B3122543
theorem B4162529 : Blo 1644021 4162529 := bstep (se 2 (by rfl) ⟨1560948, by rfl⟩ : syracuseStep 4162529 = 3121897) B3121897
theorem B2467067 : Blo 1644021 2467067 := bstep (se 1 (by rfl) ⟨1850300, by rfl⟩ : syracuseStep 2467067 = 3700601) B3700601
theorem B33760651 : Blo 1644021 33760651 := bstep (se 1 (by rfl) ⟨25320488, by rfl⟩ : syracuseStep 33760651 = 50640977) B50640977
theorem B2467241 : Blo 1644021 2467241 := bstep (se 2 (by rfl) ⟨925215, by rfl⟩ : syracuseStep 2467241 = 1850431) B1850431
theorem B14059129 : Blo 1644021 14059129 := bstep (se 2 (by rfl) ⟨5272173, by rfl⟩ : syracuseStep 14059129 = 10544347) B10544347
theorem B2467535 : Blo 1644021 2467535 := bstep (se 1 (by rfl) ⟨1850651, by rfl⟩ : syracuseStep 2467535 = 3701303) B3701303
theorem B2467583 : Blo 1644021 2467583 := bstep (se 1 (by rfl) ⟨1850687, by rfl⟩ : syracuseStep 2467583 = 3701375) B3701375
theorem B14059403 : Blo 1644021 14059403 := bstep (se 1 (by rfl) ⟨10544552, by rfl⟩ : syracuseStep 14059403 = 21089105) B21089105
theorem B3950633 : Blo 1644021 3950633 := bstep (se 2 (by rfl) ⟨1481487, by rfl⟩ : syracuseStep 3950633 = 2962975) B2962975
theorem B8325341 : Blo 1644021 8325341 := bstep (se 3 (by rfl) ⟨1561001, by rfl⟩ : syracuseStep 8325341 = 3122003) B3122003
theorem B114010361 : Blo 1644021 114010361 := bstep (se 2 (by rfl) ⟨42753885, by rfl⟩ : syracuseStep 114010361 = 85507771) B85507771
theorem B1125567127 : Blo 1644021 1125567127 := bstep (se 1 (by rfl) ⟨844175345, by rfl⟩ : syracuseStep 1125567127 = 1688350691) B1688350691
theorem B2468585 : Blo 1644021 2468585 := bstep (se 2 (by rfl) ⟨925719, by rfl⟩ : syracuseStep 2468585 = 1851439) B1851439
theorem B2468639 : Blo 1644021 2468639 := bstep (se 1 (by rfl) ⟨1851479, by rfl⟩ : syracuseStep 2468639 = 3702959) B3702959
theorem B256453451 : Blo 1644021 256453451 := bstep (se 1 (by rfl) ⟨192340088, by rfl⟩ : syracuseStep 256453451 = 384680177) B384680177
theorem B4164443 : Blo 1644021 4164443 := bstep (se 1 (by rfl) ⟨3123332, by rfl⟩ : syracuseStep 4164443 = 6246665) B6246665
theorem B4164473 : Blo 1644021 4164473 := bstep (se 2 (by rfl) ⟨1561677, by rfl⟩ : syracuseStep 4164473 = 3123355) B3123355
theorem B12487769 : Blo 1644021 12487769 := bstep (se 2 (by rfl) ⟨4682913, by rfl⟩ : syracuseStep 12487769 = 9365827) B9365827
theorem B5549471 : Blo 1644021 5549471 := bstep (se 1 (by rfl) ⟨4162103, by rfl⟩ : syracuseStep 5549471 = 8324207) B8324207
theorem B151998227 : Blo 1644021 151998227 := bstep (se 1 (by rfl) ⟨113998670, by rfl⟩ : syracuseStep 151998227 = 227997341) B227997341
theorem B2223983 : Blo 1644021 2223983 := bstep (se 1 (by rfl) ⟨1667987, by rfl⟩ : syracuseStep 2223983 = 3335975) B3335975
theorem B5927147 : Blo 1644021 5927147 := bstep (se 1 (by rfl) ⟨4445360, by rfl⟩ : syracuseStep 5927147 = 8890721) B8890721
theorem B8327447 : Blo 1644021 8327447 := bstep (se 1 (by rfl) ⟨6245585, by rfl⟩ : syracuseStep 8327447 = 12491171) B12491171
theorem B4445275 : Blo 1644021 4445275 := bstep (se 1 (by rfl) ⟨3333956, by rfl⟩ : syracuseStep 4445275 = 6667913) B6667913
theorem B5551199 : Blo 1644021 5551199 := bstep (se 1 (by rfl) ⟨4163399, by rfl⟩ : syracuseStep 5551199 = 8326799) B8326799
theorem B6673537 : Blo 1644021 6673537 := bstep (se 2 (by rfl) ⟨2502576, by rfl⟩ : syracuseStep 6673537 = 5005153) B5005153
theorem B79164599 : Blo 1644021 79164599 := bstep (se 1 (by rfl) ⟨59373449, by rfl⟩ : syracuseStep 79164599 = 118746899) B118746899
theorem B6010193 : Blo 1644021 6010193 := bstep (se 2 (by rfl) ⟨2253822, by rfl⟩ : syracuseStep 6010193 = 4507645) B4507645
theorem B7026011 : Blo 1644021 7026011 := bstep (se 1 (by rfl) ⟨5269508, by rfl⟩ : syracuseStep 7026011 = 10539017) B10539017
theorem B3700223 : Blo 1644021 3700223 := bstep (se 1 (by rfl) ⟨2775167, by rfl⟩ : syracuseStep 3700223 = 5550335) B5550335
theorem B3700331 : Blo 1644021 3700331 := bstep (se 1 (by rfl) ⟨2775248, by rfl⟩ : syracuseStep 3700331 = 5550497) B5550497
theorem B11859623 : Blo 1644021 11859623 := bstep (se 1 (by rfl) ⟨8894717, by rfl⟩ : syracuseStep 11859623 = 17789435) B17789435
theorem B2373311 : Blo 1644021 2373311 := bstep (se 1 (by rfl) ⟨1779983, by rfl⟩ : syracuseStep 2373311 = 3559967) B3559967
theorem B31635197 : Blo 1644021 31635197 := bstep (se 3 (by rfl) ⟨5931599, by rfl⟩ : syracuseStep 31635197 = 11863199) B11863199
theorem B3700727 : Blo 1644021 3700727 := bstep (se 1 (by rfl) ⟨2775545, by rfl⟩ : syracuseStep 3700727 = 5551091) B5551091
theorem B3954815 : Blo 1644021 3954815 := bstep (se 1 (by rfl) ⟨2966111, by rfl⟩ : syracuseStep 3954815 = 5932223) B5932223
theorem B1644783 : Blo 1644021 1644783 := bstep (se 1 (by rfl) ⟨1233587, by rfl⟩ : syracuseStep 1644783 = 2467175) B2467175
theorem B4684031 : Blo 1644021 4684031 := bstep (se 1 (by rfl) ⟨3513023, by rfl⟩ : syracuseStep 4684031 = 7026047) B7026047
theorem B2775323 : Blo 1644021 2775323 := bstep (se 1 (by rfl) ⟨2081492, by rfl⟩ : syracuseStep 2775323 = 4162985) B4162985
theorem B2341343 : Blo 1644021 2341343 := bstep (se 1 (by rfl) ⟨1756007, by rfl⟩ : syracuseStep 2341343 = 3512015) B3512015
theorem B5004011 : Blo 1644021 5004011 := bstep (se 1 (by rfl) ⟨3753008, by rfl⟩ : syracuseStep 5004011 = 7506017) B7506017
theorem B1645295 : Blo 1644021 1645295 := bstep (se 1 (by rfl) ⟨1233971, by rfl⟩ : syracuseStep 1645295 = 2467943) B2467943
theorem B18733841 : Blo 1644021 18733841 := bstep (se 2 (by rfl) ⟨7025190, by rfl⟩ : syracuseStep 18733841 = 14050381) B14050381
theorem B12491657 : Blo 1644021 12491657 := bstep (se 2 (by rfl) ⟨4684371, by rfl⟩ : syracuseStep 12491657 = 9368743) B9368743
theorem B1645595 : Blo 1644021 1645595 := bstep (se 1 (by rfl) ⟨1234196, by rfl⟩ : syracuseStep 1645595 = 2468393) B2468393
theorem B3751073 : Blo 1644021 3751073 := bstep (se 2 (by rfl) ⟨1406652, by rfl⟩ : syracuseStep 3751073 = 2813305) B2813305
theorem B5553359 : Blo 1644021 5553359 := bstep (se 1 (by rfl) ⟨4165019, by rfl⟩ : syracuseStep 5553359 = 8330039) B8330039
theorem B1645983 : Blo 1644021 1645983 := bstep (se 1 (by rfl) ⟨1234487, by rfl⟩ : syracuseStep 1645983 = 2468975) B2468975
theorem B81083915 : Blo 1644021 81083915 := bstep (se 1 (by rfl) ⟨60812936, by rfl⟩ : syracuseStep 81083915 = 121625873) B121625873
theorem B2342687 : Blo 1644021 2342687 := bstep (se 1 (by rfl) ⟨1757015, by rfl⟩ : syracuseStep 2342687 = 3514031) B3514031
theorem B35594093 : Blo 1644021 35594093 := bstep (se 3 (by rfl) ⟨6673892, by rfl⟩ : syracuseStep 35594093 = 13347785) B13347785
theorem B3702761 : Blo 1644021 3702761 := bstep (se 2 (by rfl) ⟨1388535, by rfl⟩ : syracuseStep 3702761 = 2777071) B2777071
theorem B6242291 : Blo 1644021 6242291 := bstep (se 1 (by rfl) ⟨4681718, by rfl⟩ : syracuseStep 6242291 = 9363437) B9363437
theorem B3702779 : Blo 1644021 3702779 := bstep (se 1 (by rfl) ⟨2777084, by rfl⟩ : syracuseStep 3702779 = 5554169) B5554169
theorem B10535021 : Blo 1644021 10535021 := bstep (se 3 (by rfl) ⟨1975316, by rfl⟩ : syracuseStep 10535021 = 3950633) B3950633
theorem B17776979 : Blo 1644021 17776979 := bstep (se 1 (by rfl) ⟨13332734, by rfl⟩ : syracuseStep 17776979 = 26665469) B26665469
theorem B3752315 : Blo 1644021 3752315 := bstep (se 1 (by rfl) ⟨2814236, by rfl⟩ : syracuseStep 3752315 = 5628473) B5628473
theorem B25313771 : Blo 1644021 25313771 := bstep (se 1 (by rfl) ⟨18985328, by rfl⟩ : syracuseStep 25313771 = 37970657) B37970657
theorem B8323721 : Blo 1644021 8323721 := bstep (se 2 (by rfl) ⟨3121395, by rfl⟩ : syracuseStep 8323721 = 6242791) B6242791
theorem B4006795 : Blo 1644021 4006795 := bstep (se 1 (by rfl) ⟨3005096, by rfl⟩ : syracuseStep 4006795 = 6010193) B6010193
theorem B2466815 : Blo 1644021 2466815 := bstep (se 1 (by rfl) ⟨1850111, by rfl⟩ : syracuseStep 2466815 = 3700223) B3700223
theorem B2466887 : Blo 1644021 2466887 := bstep (se 1 (by rfl) ⟨1850165, by rfl⟩ : syracuseStep 2466887 = 3700331) B3700331
theorem B7906415 : Blo 1644021 7906415 := bstep (se 1 (by rfl) ⟨5929811, by rfl⟩ : syracuseStep 7906415 = 11859623) B11859623
theorem B6243581 : Blo 1644021 6243581 := bstep (se 3 (by rfl) ⟨1170671, by rfl⟩ : syracuseStep 6243581 = 2341343) B2341343
theorem B9372935 : Blo 1644021 9372935 := bstep (se 1 (by rfl) ⟨7029701, by rfl⟩ : syracuseStep 9372935 = 14059403) B14059403
theorem B2467151 : Blo 1644021 2467151 := bstep (se 1 (by rfl) ⟨1850363, by rfl⟩ : syracuseStep 2467151 = 3700727) B3700727
theorem B76006907 : Blo 1644021 76006907 := bstep (se 1 (by rfl) ⟨57005180, by rfl⟩ : syracuseStep 76006907 = 114010361) B114010361
theorem B3122687 : Blo 1644021 3122687 := bstep (se 1 (by rfl) ⟨2342015, by rfl⟩ : syracuseStep 3122687 = 4684031) B4684031
theorem B8898049 : Blo 1644021 8898049 := bstep (se 2 (by rfl) ⟨3336768, by rfl⟩ : syracuseStep 8898049 = 6673537) B6673537
theorem B3336007 : Blo 1644021 3336007 := bstep (se 1 (by rfl) ⟨2502005, by rfl⟩ : syracuseStep 3336007 = 5004011) B5004011
theorem B170968967 : Blo 1644021 170968967 := bstep (se 1 (by rfl) ⟨128226725, by rfl⟩ : syracuseStep 170968967 = 256453451) B256453451
theorem B8325179 : Blo 1644021 8325179 := bstep (se 1 (by rfl) ⟨6243884, by rfl⟩ : syracuseStep 8325179 = 12487769) B12487769
theorem B2500715 : Blo 1644021 2500715 := bstep (se 1 (by rfl) ⟨1875536, by rfl⟩ : syracuseStep 2500715 = 3751073) B3751073
theorem B18745505 : Blo 1644021 18745505 := bstep (se 2 (by rfl) ⟨7029564, by rfl⟩ : syracuseStep 18745505 = 14059129) B14059129
theorem B2468507 : Blo 1644021 2468507 := bstep (se 1 (by rfl) ⟨1851380, by rfl⟩ : syracuseStep 2468507 = 3702761) B3702761
theorem B2468519 : Blo 1644021 2468519 := bstep (se 1 (by rfl) ⟨1851389, by rfl⟩ : syracuseStep 2468519 = 3702779) B3702779
theorem B3951431 : Blo 1644021 3951431 := bstep (se 1 (by rfl) ⟨2963573, by rfl⟩ : syracuseStep 3951431 = 5927147) B5927147
theorem B2468735 : Blo 1644021 2468735 := bstep (se 1 (by rfl) ⟨1851551, by rfl⟩ : syracuseStep 2468735 = 3703103) B3703103
theorem B21090131 : Blo 1644021 21090131 := bstep (se 1 (by rfl) ⟨15817598, by rfl⟩ : syracuseStep 21090131 = 31635197) B31635197
theorem B5927033 : Blo 1644021 5927033 := bstep (se 2 (by rfl) ⟨2222637, by rfl⟩ : syracuseStep 5927033 = 4445275) B4445275
theorem B5550227 : Blo 1644021 5550227 := bstep (se 1 (by rfl) ⟨4162670, by rfl⟩ : syracuseStep 5550227 = 8325341) B8325341
theorem B6328829 : Blo 1644021 6328829 := bstep (se 3 (by rfl) ⟨1186655, by rfl⟩ : syracuseStep 6328829 = 2373311) B2373311
theorem B12489227 : Blo 1644021 12489227 := bstep (se 1 (by rfl) ⟨9366920, by rfl⟩ : syracuseStep 12489227 = 18733841) B18733841
theorem B8327771 : Blo 1644021 8327771 := bstep (se 1 (by rfl) ⟨6245828, by rfl⟩ : syracuseStep 8327771 = 12491657) B12491657
theorem B6247165 : Blo 1644021 6247165 := bstep (se 3 (by rfl) ⟨1171343, by rfl⟩ : syracuseStep 6247165 = 2342687) B2342687
theorem B3699647 : Blo 1644021 3699647 := bstep (se 1 (by rfl) ⟨2774735, by rfl⟩ : syracuseStep 3699647 = 5549471) B5549471
theorem B54055943 : Blo 1644021 54055943 := bstep (se 1 (by rfl) ⟨40541957, by rfl⟩ : syracuseStep 54055943 = 81083915) B81083915
theorem B101332151 : Blo 1644021 101332151 := bstep (se 1 (by rfl) ⟨75999113, by rfl⟩ : syracuseStep 101332151 = 151998227) B151998227
theorem B23729395 : Blo 1644021 23729395 := bstep (se 1 (by rfl) ⟨17797046, by rfl⟩ : syracuseStep 23729395 = 35594093) B35594093
theorem B2774479 : Blo 1644021 2774479 := bstep (se 1 (by rfl) ⟨2080859, by rfl⟩ : syracuseStep 2774479 = 4161719) B4161719
theorem B5551631 : Blo 1644021 5551631 := bstep (se 1 (by rfl) ⟨4163723, by rfl⟩ : syracuseStep 5551631 = 8327447) B8327447
theorem B211105597 : Blo 1644021 211105597 := bstep (se 3 (by rfl) ⟨39582299, by rfl⟩ : syracuseStep 211105597 = 79164599) B79164599
theorem B2774911 : Blo 1644021 2774911 := bstep (se 1 (by rfl) ⟨2081183, by rfl⟩ : syracuseStep 2774911 = 4162367) B4162367
theorem B5003135 : Blo 1644021 5003135 := bstep (se 1 (by rfl) ⟨3752351, by rfl⟩ : syracuseStep 5003135 = 7504703) B7504703
theorem B2775019 : Blo 1644021 2775019 := bstep (se 1 (by rfl) ⟨2081264, by rfl⟩ : syracuseStep 2775019 = 4162529) B4162529
theorem B3700799 : Blo 1644021 3700799 := bstep (se 1 (by rfl) ⟨2775599, by rfl⟩ : syracuseStep 3700799 = 5551199) B5551199
theorem B1644711 : Blo 1644021 1644711 := bstep (se 1 (by rfl) ⟨1233533, by rfl⟩ : syracuseStep 1644711 = 2467067) B2467067
theorem B1500756169 : Blo 1644021 1500756169 := bstep (se 2 (by rfl) ⟨562783563, by rfl⟩ : syracuseStep 1500756169 = 1125567127) B1125567127
theorem B4684007 : Blo 1644021 4684007 := bstep (se 1 (by rfl) ⟨3513005, by rfl⟩ : syracuseStep 4684007 = 7026011) B7026011
theorem B1644827 : Blo 1644021 1644827 := bstep (se 1 (by rfl) ⟨1233620, by rfl⟩ : syracuseStep 1644827 = 2467241) B2467241
theorem B1645023 : Blo 1644021 1645023 := bstep (se 1 (by rfl) ⟨1233767, by rfl⟩ : syracuseStep 1645023 = 2467535) B2467535
theorem B1645055 : Blo 1644021 1645055 := bstep (se 1 (by rfl) ⟨1233791, by rfl⟩ : syracuseStep 1645055 = 2467583) B2467583
theorem B2775593 : Blo 1644021 2775593 := bstep (se 2 (by rfl) ⟨1040847, by rfl⟩ : syracuseStep 2775593 = 2081695) B2081695
theorem B2636543 : Blo 1644021 2636543 := bstep (se 1 (by rfl) ⟨1977407, by rfl⟩ : syracuseStep 2636543 = 3954815) B3954815
theorem B1850215 : Blo 1644021 1850215 := bstep (se 1 (by rfl) ⟨1387661, by rfl⟩ : syracuseStep 1850215 = 2775323) B2775323
theorem B1645723 : Blo 1644021 1645723 := bstep (se 1 (by rfl) ⟨1234292, by rfl⟩ : syracuseStep 1645723 = 2468585) B2468585
theorem B45014201 : Blo 1644021 45014201 := bstep (se 2 (by rfl) ⟨16880325, by rfl⟩ : syracuseStep 45014201 = 33760651) B33760651
theorem B1645759 : Blo 1644021 1645759 := bstep (se 1 (by rfl) ⟨1234319, by rfl⟩ : syracuseStep 1645759 = 2468639) B2468639
theorem B2776295 : Blo 1644021 2776295 := bstep (se 1 (by rfl) ⟨2082221, by rfl⟩ : syracuseStep 2776295 = 4164443) B4164443
theorem B2776315 : Blo 1644021 2776315 := bstep (se 1 (by rfl) ⟨2082236, by rfl⟩ : syracuseStep 2776315 = 4164473) B4164473
theorem B3702239 : Blo 1644021 3702239 := bstep (se 1 (by rfl) ⟨2776679, by rfl⟩ : syracuseStep 3702239 = 5553359) B5553359
theorem B5930621 : Blo 1644021 5930621 := bstep (se 3 (by rfl) ⟨1111991, by rfl⟩ : syracuseStep 5930621 = 2223983) B2223983
theorem B4161527 : Blo 1644021 4161527 := bstep (se 1 (by rfl) ⟨3121145, by rfl⟩ : syracuseStep 4161527 = 6242291) B6242291
theorem B6668573 : Blo 1644021 6668573 := bstep (se 3 (by rfl) ⟨1250357, by rfl⟩ : syracuseStep 6668573 = 2500715) B2500715
theorem B16875847 : Blo 1644021 16875847 := bstep (se 1 (by rfl) ⟨12656885, by rfl⟩ : syracuseStep 16875847 = 25313771) B25313771
theorem B4219219 : Blo 1644021 4219219 := bstep (se 1 (by rfl) ⟨3164414, by rfl⟩ : syracuseStep 4219219 = 6328829) B6328829
theorem B2466431 : Blo 1644021 2466431 := bstep (se 1 (by rfl) ⟨1849823, by rfl⟩ : syracuseStep 2466431 = 3699647) B3699647
theorem B36037295 : Blo 1644021 36037295 := bstep (se 1 (by rfl) ⟨27027971, by rfl⟩ : syracuseStep 36037295 = 54055943) B54055943
theorem B4162387 : Blo 1644021 4162387 := bstep (se 1 (by rfl) ⟨3121790, by rfl⟩ : syracuseStep 4162387 = 6243581) B6243581
theorem B2081791 : Blo 1644021 2081791 := bstep (se 1 (by rfl) ⟨1561343, by rfl⟩ : syracuseStep 2081791 = 3122687) B3122687
theorem B2466953 : Blo 1644021 2466953 := bstep (se 2 (by rfl) ⟨925107, by rfl⟩ : syracuseStep 2466953 = 1850215) B1850215
theorem B5342393 : Blo 1644021 5342393 := bstep (se 2 (by rfl) ⟨2003397, by rfl⟩ : syracuseStep 5342393 = 4006795) B4006795
theorem B3335423 : Blo 1644021 3335423 := bstep (se 1 (by rfl) ⟨2501567, by rfl⟩ : syracuseStep 3335423 = 5003135) B5003135
theorem B2467199 : Blo 1644021 2467199 := bstep (se 1 (by rfl) ⟨1850399, by rfl⟩ : syracuseStep 2467199 = 3700799) B3700799
theorem B31639193 : Blo 1644021 31639193 := bstep (se 2 (by rfl) ⟨11864697, by rfl⟩ : syracuseStep 31639193 = 23729395) B23729395
theorem B11864065 : Blo 1644021 11864065 := bstep (se 2 (by rfl) ⟨4449024, by rfl⟩ : syracuseStep 11864065 = 8898049) B8898049
theorem B30009467 : Blo 1644021 30009467 := bstep (se 1 (by rfl) ⟨22507100, by rfl⟩ : syracuseStep 30009467 = 45014201) B45014201
theorem B2468159 : Blo 1644021 2468159 := bstep (se 1 (by rfl) ⟨1851119, by rfl⟩ : syracuseStep 2468159 = 3702239) B3702239
theorem B14060087 : Blo 1644021 14060087 := bstep (se 1 (by rfl) ⟨10545065, by rfl⟩ : syracuseStep 14060087 = 21090131) B21090131
theorem B7023347 : Blo 1644021 7023347 := bstep (se 1 (by rfl) ⟨5267510, by rfl⟩ : syracuseStep 7023347 = 10535021) B10535021
theorem B3951355 : Blo 1644021 3951355 := bstep (se 1 (by rfl) ⟨2963516, by rfl⟩ : syracuseStep 3951355 = 5927033) B5927033
theorem B2501543 : Blo 1644021 2501543 := bstep (se 1 (by rfl) ⟨1876157, by rfl⟩ : syracuseStep 2501543 = 3752315) B3752315
theorem B8326151 : Blo 1644021 8326151 := bstep (se 1 (by rfl) ⟨6244613, by rfl⟩ : syracuseStep 8326151 = 12489227) B12489227
theorem B5549147 : Blo 1644021 5549147 := bstep (se 1 (by rfl) ⟨4161860, by rfl⟩ : syracuseStep 5549147 = 8323721) B8323721
theorem B67554767 : Blo 1644021 67554767 := bstep (se 1 (by rfl) ⟨50666075, by rfl⟩ : syracuseStep 67554767 = 101332151) B101332151
theorem B50671271 : Blo 1644021 50671271 := bstep (se 1 (by rfl) ⟨38003453, by rfl⟩ : syracuseStep 50671271 = 76006907) B76006907
theorem B113979311 : Blo 1644021 113979311 := bstep (se 1 (by rfl) ⟨85484483, by rfl⟩ : syracuseStep 113979311 = 170968967) B170968967
theorem B5550119 : Blo 1644021 5550119 := bstep (se 1 (by rfl) ⟨4162589, by rfl⟩ : syracuseStep 5550119 = 8325179) B8325179
theorem B12497003 : Blo 1644021 12497003 := bstep (se 1 (by rfl) ⟨9372752, by rfl⟩ : syracuseStep 12497003 = 18745505) B18745505
theorem B1757695 : Blo 1644021 1757695 := bstep (se 1 (by rfl) ⟨1318271, by rfl⟩ : syracuseStep 1757695 = 2636543) B2636543
theorem B2634287 : Blo 1644021 2634287 := bstep (se 1 (by rfl) ⟨1975715, by rfl⟩ : syracuseStep 2634287 = 3951431) B3951431
theorem B3699305 : Blo 1644021 3699305 := bstep (se 2 (by rfl) ⟨1387239, by rfl⟩ : syracuseStep 3699305 = 2774479) B2774479
theorem B281474129 : Blo 1644021 281474129 := bstep (se 2 (by rfl) ⟨105552798, by rfl⟩ : syracuseStep 281474129 = 211105597) B211105597
theorem B3953747 : Blo 1644021 3953747 := bstep (se 1 (by rfl) ⟨2965310, by rfl⟩ : syracuseStep 3953747 = 5930621) B5930621
theorem B3699881 : Blo 1644021 3699881 := bstep (se 2 (by rfl) ⟨1387455, by rfl⟩ : syracuseStep 3699881 = 2774911) B2774911
theorem B3700025 : Blo 1644021 3700025 := bstep (se 2 (by rfl) ⟨1387509, by rfl⟩ : syracuseStep 3700025 = 2775019) B2775019
theorem B2774351 : Blo 1644021 2774351 := bstep (se 1 (by rfl) ⟨2080763, by rfl⟩ : syracuseStep 2774351 = 4161527) B4161527
theorem B3700151 : Blo 1644021 3700151 := bstep (se 1 (by rfl) ⟨2775113, by rfl⟩ : syracuseStep 3700151 = 5550227) B5550227
theorem B11851319 : Blo 1644021 11851319 := bstep (se 1 (by rfl) ⟨8888489, by rfl⟩ : syracuseStep 11851319 = 17776979) B17776979
theorem B2001008225 : Blo 1644021 2001008225 := bstep (se 2 (by rfl) ⟨750378084, by rfl⟩ : syracuseStep 2001008225 = 1500756169) B1500756169
theorem B21083773 : Blo 1644021 21083773 := bstep (se 3 (by rfl) ⟨3953207, by rfl⟩ : syracuseStep 21083773 = 7906415) B7906415
theorem B5551847 : Blo 1644021 5551847 := bstep (se 1 (by rfl) ⟨4163885, by rfl⟩ : syracuseStep 5551847 = 8327771) B8327771
theorem B12490685 : Blo 1644021 12490685 := bstep (se 3 (by rfl) ⟨2342003, by rfl⟩ : syracuseStep 12490685 = 4684007) B4684007
theorem B1644543 : Blo 1644021 1644543 := bstep (se 1 (by rfl) ⟨1233407, by rfl⟩ : syracuseStep 1644543 = 2466815) B2466815
theorem B1644591 : Blo 1644021 1644591 := bstep (se 1 (by rfl) ⟨1233443, by rfl⟩ : syracuseStep 1644591 = 2466887) B2466887
theorem B6248623 : Blo 1644021 6248623 := bstep (se 1 (by rfl) ⟨4686467, by rfl⟩ : syracuseStep 6248623 = 9372935) B9372935
theorem B1644767 : Blo 1644021 1644767 := bstep (se 1 (by rfl) ⟨1233575, by rfl⟩ : syracuseStep 1644767 = 2467151) B2467151
theorem B8329553 : Blo 1644021 8329553 := bstep (se 2 (by rfl) ⟨3123582, by rfl⟩ : syracuseStep 8329553 = 6247165) B6247165
theorem B3701087 : Blo 1644021 3701087 := bstep (se 1 (by rfl) ⟨2775815, by rfl⟩ : syracuseStep 3701087 = 5551631) B5551631
theorem B3701753 : Blo 1644021 3701753 := bstep (se 2 (by rfl) ⟨1388157, by rfl⟩ : syracuseStep 3701753 = 2776315) B2776315
theorem B1850395 : Blo 1644021 1850395 := bstep (se 1 (by rfl) ⟨1387796, by rfl⟩ : syracuseStep 1850395 = 2775593) B2775593
theorem B1645671 : Blo 1644021 1645671 := bstep (se 1 (by rfl) ⟨1234253, by rfl⟩ : syracuseStep 1645671 = 2468507) B2468507
theorem B1645679 : Blo 1644021 1645679 := bstep (se 1 (by rfl) ⟨1234259, by rfl⟩ : syracuseStep 1645679 = 2468519) B2468519
theorem B1645823 : Blo 1644021 1645823 := bstep (se 1 (by rfl) ⟨1234367, by rfl⟩ : syracuseStep 1645823 = 2468735) B2468735
theorem B1850863 : Blo 1644021 1850863 := bstep (se 1 (by rfl) ⟨1388147, by rfl⟩ : syracuseStep 1850863 = 2776295) B2776295
theorem B4448009 : Blo 1644021 4448009 := bstep (se 2 (by rfl) ⟨1668003, by rfl⟩ : syracuseStep 4448009 = 3336007) B3336007
theorem B15818753 : Blo 1644021 15818753 := bstep (se 2 (by rfl) ⟨5932032, by rfl⟩ : syracuseStep 15818753 = 11864065) B11864065
theorem B8331335 : Blo 1644021 8331335 := bstep (se 1 (by rfl) ⟨6248501, by rfl⟩ : syracuseStep 8331335 = 12497003) B12497003
theorem B8331497 : Blo 1644021 8331497 := bstep (se 2 (by rfl) ⟨3124311, by rfl⟩ : syracuseStep 8331497 = 6248623) B6248623
theorem B71131445 : Blo 1644021 71131445 := bstep (se 5 (by rfl) ⟨3334286, by rfl⟩ : syracuseStep 71131445 = 6668573) B6668573
theorem B2466203 : Blo 1644021 2466203 := bstep (se 1 (by rfl) ⟨1849652, by rfl⟩ : syracuseStep 2466203 = 3699305) B3699305
theorem B14246381 : Blo 1644021 14246381 := bstep (se 3 (by rfl) ⟨2671196, by rfl⟩ : syracuseStep 14246381 = 5342393) B5342393
theorem B2343593 : Blo 1644021 2343593 := bstep (se 2 (by rfl) ⟨878847, by rfl⟩ : syracuseStep 2343593 = 1757695) B1757695
theorem B2466587 : Blo 1644021 2466587 := bstep (se 1 (by rfl) ⟨1849940, by rfl⟩ : syracuseStep 2466587 = 3699881) B3699881
theorem B2466683 : Blo 1644021 2466683 := bstep (se 1 (by rfl) ⟨1850012, by rfl⟩ : syracuseStep 2466683 = 3700025) B3700025
theorem B2466767 : Blo 1644021 2466767 := bstep (se 1 (by rfl) ⟨1850075, by rfl⟩ : syracuseStep 2466767 = 3700151) B3700151
theorem B5268473 : Blo 1644021 5268473 := bstep (se 2 (by rfl) ⟨1975677, by rfl⟩ : syracuseStep 5268473 = 3951355) B3951355
theorem B2467193 : Blo 1644021 2467193 := bstep (se 2 (by rfl) ⟨925197, by rfl⟩ : syracuseStep 2467193 = 1850395) B1850395
theorem B20006311 : Blo 1644021 20006311 := bstep (se 1 (by rfl) ⟨15004733, by rfl⟩ : syracuseStep 20006311 = 30009467) B30009467
theorem B2467391 : Blo 1644021 2467391 := bstep (se 1 (by rfl) ⟨1850543, by rfl⟩ : syracuseStep 2467391 = 3701087) B3701087
theorem B9373391 : Blo 1644021 9373391 := bstep (se 1 (by rfl) ⟨7030043, by rfl⟩ : syracuseStep 9373391 = 14060087) B14060087
theorem B2467817 : Blo 1644021 2467817 := bstep (se 2 (by rfl) ⟨925431, by rfl⟩ : syracuseStep 2467817 = 1850863) B1850863
theorem B2467835 : Blo 1644021 2467835 := bstep (se 1 (by rfl) ⟨1850876, by rfl⟩ : syracuseStep 2467835 = 3701753) B3701753
theorem B6670781 : Blo 1644021 6670781 := bstep (se 3 (by rfl) ⟨1250771, by rfl⟩ : syracuseStep 6670781 = 2501543) B2501543
theorem B187649419 : Blo 1644021 187649419 := bstep (se 1 (by rfl) ⟨140737064, by rfl⟩ : syracuseStep 187649419 = 281474129) B281474129
theorem B1334005483 : Blo 1644021 1334005483 := bstep (se 1 (by rfl) ⟨1000504112, by rfl⟩ : syracuseStep 1334005483 = 2001008225) B2001008225
theorem B5549849 : Blo 1644021 5549849 := bstep (se 2 (by rfl) ⟨2081193, by rfl⟩ : syracuseStep 5549849 = 4162387) B4162387
theorem B180146045 : Blo 1644021 180146045 := bstep (se 3 (by rfl) ⟨33777383, by rfl⟩ : syracuseStep 180146045 = 67554767) B67554767
theorem B8327123 : Blo 1644021 8327123 := bstep (se 1 (by rfl) ⟨6245342, by rfl⟩ : syracuseStep 8327123 = 12490685) B12490685
theorem B7024765 : Blo 1644021 7024765 := bstep (se 3 (by rfl) ⟨1317143, by rfl⟩ : syracuseStep 7024765 = 2634287) B2634287
theorem B4682231 : Blo 1644021 4682231 := bstep (se 1 (by rfl) ⟨3511673, by rfl⟩ : syracuseStep 4682231 = 7023347) B7023347
theorem B5550767 : Blo 1644021 5550767 := bstep (se 1 (by rfl) ⟨4163075, by rfl⟩ : syracuseStep 5550767 = 8326151) B8326151
theorem B3699431 : Blo 1644021 3699431 := bstep (se 1 (by rfl) ⟨2774573, by rfl⟩ : syracuseStep 3699431 = 5549147) B5549147
theorem B28111697 : Blo 1644021 28111697 := bstep (se 2 (by rfl) ⟨10541886, by rfl⟩ : syracuseStep 28111697 = 21083773) B21083773
theorem B33780847 : Blo 1644021 33780847 := bstep (se 1 (by rfl) ⟨25335635, by rfl⟩ : syracuseStep 33780847 = 50671271) B50671271
theorem B75986207 : Blo 1644021 75986207 := bstep (se 1 (by rfl) ⟨56989655, by rfl⟩ : syracuseStep 75986207 = 113979311) B113979311
theorem B3700079 : Blo 1644021 3700079 := bstep (se 1 (by rfl) ⟨2775059, by rfl⟩ : syracuseStep 3700079 = 5550119) B5550119
theorem B1644287 : Blo 1644021 1644287 := bstep (se 1 (by rfl) ⟨1233215, by rfl⟩ : syracuseStep 1644287 = 2466431) B2466431
theorem B5625625 : Blo 1644021 5625625 := bstep (se 2 (by rfl) ⟨2109609, by rfl⟩ : syracuseStep 5625625 = 4219219) B4219219
theorem B24024863 : Blo 1644021 24024863 := bstep (se 1 (by rfl) ⟨18018647, by rfl⟩ : syracuseStep 24024863 = 36037295) B36037295
theorem B8894461 : Blo 1644021 8894461 := bstep (se 3 (by rfl) ⟨1667711, by rfl⟩ : syracuseStep 8894461 = 3335423) B3335423
theorem B2635831 : Blo 1644021 2635831 := bstep (se 1 (by rfl) ⟨1976873, by rfl⟩ : syracuseStep 2635831 = 3953747) B3953747
theorem B1644635 : Blo 1644021 1644635 := bstep (se 1 (by rfl) ⟨1233476, by rfl⟩ : syracuseStep 1644635 = 2466953) B2466953
theorem B1849567 : Blo 1644021 1849567 := bstep (se 1 (by rfl) ⟨1387175, by rfl⟩ : syracuseStep 1849567 = 2774351) B2774351
theorem B1644799 : Blo 1644021 1644799 := bstep (se 1 (by rfl) ⟨1233599, by rfl⟩ : syracuseStep 1644799 = 2467199) B2467199
theorem B21092795 : Blo 1644021 21092795 := bstep (se 1 (by rfl) ⟨15819596, by rfl⟩ : syracuseStep 21092795 = 31639193) B31639193
theorem B3701231 : Blo 1644021 3701231 := bstep (se 1 (by rfl) ⟨2775923, by rfl⟩ : syracuseStep 3701231 = 5551847) B5551847
theorem B2775721 : Blo 1644021 2775721 := bstep (se 2 (by rfl) ⟨1040895, by rfl⟩ : syracuseStep 2775721 = 2081791) B2081791
theorem B31603517 : Blo 1644021 31603517 := bstep (se 3 (by rfl) ⟨5925659, by rfl⟩ : syracuseStep 31603517 = 11851319) B11851319
theorem B1645439 : Blo 1644021 1645439 := bstep (se 1 (by rfl) ⟨1234079, by rfl⟩ : syracuseStep 1645439 = 2468159) B2468159
theorem B5553035 : Blo 1644021 5553035 := bstep (se 1 (by rfl) ⟨4164776, by rfl⟩ : syracuseStep 5553035 = 8329553) B8329553
theorem B90004517 : Blo 1644021 90004517 := bstep (se 4 (by rfl) ⟨8437923, by rfl⟩ : syracuseStep 90004517 = 16875847) B16875847
theorem B2965339 : Blo 1644021 2965339 := bstep (se 1 (by rfl) ⟨2224004, by rfl⟩ : syracuseStep 2965339 = 4448009) B4448009
theorem B5554223 : Blo 1644021 5554223 := bstep (se 1 (by rfl) ⟨4165667, by rfl⟩ : syracuseStep 5554223 = 8331335) B8331335
theorem B3514441 : Blo 1644021 3514441 := bstep (se 2 (by rfl) ⟨1317915, by rfl⟩ : syracuseStep 3514441 = 2635831) B2635831
theorem B5554331 : Blo 1644021 5554331 := bstep (se 1 (by rfl) ⟨4165748, by rfl⟩ : syracuseStep 5554331 = 8331497) B8331497
theorem B2466089 : Blo 1644021 2466089 := bstep (se 2 (by rfl) ⟨924783, by rfl⟩ : syracuseStep 2466089 = 1849567) B1849567
theorem B3121487 : Blo 1644021 3121487 := bstep (se 1 (by rfl) ⟨2341115, by rfl⟩ : syracuseStep 3121487 = 4682231) B4682231
theorem B2466287 : Blo 1644021 2466287 := bstep (se 1 (by rfl) ⟨1849715, by rfl⟩ : syracuseStep 2466287 = 3699431) B3699431
theorem B2466719 : Blo 1644021 2466719 := bstep (se 1 (by rfl) ⟨1850039, by rfl⟩ : syracuseStep 2466719 = 3700079) B3700079
theorem B16016575 : Blo 1644021 16016575 := bstep (se 1 (by rfl) ⟨12012431, by rfl⟩ : syracuseStep 16016575 = 24024863) B24024863
theorem B45041129 : Blo 1644021 45041129 := bstep (se 2 (by rfl) ⟨16890423, by rfl⟩ : syracuseStep 45041129 = 33780847) B33780847
theorem B2467487 : Blo 1644021 2467487 := bstep (se 1 (by rfl) ⟨1850615, by rfl⟩ : syracuseStep 2467487 = 3701231) B3701231
theorem B26675081 : Blo 1644021 26675081 := bstep (se 2 (by rfl) ⟨10003155, by rfl⟩ : syracuseStep 26675081 = 20006311) B20006311
theorem B1778673977 : Blo 1644021 1778673977 := bstep (se 2 (by rfl) ⟨667002741, by rfl⟩ : syracuseStep 1778673977 = 1334005483) B1334005483
theorem B120097363 : Blo 1644021 120097363 := bstep (se 1 (by rfl) ⟨90073022, by rfl⟩ : syracuseStep 120097363 = 180146045) B180146045
theorem B10545835 : Blo 1644021 10545835 := bstep (se 1 (by rfl) ⟨7909376, by rfl⟩ : syracuseStep 10545835 = 15818753) B15818753
theorem B9366353 : Blo 1644021 9366353 := bstep (se 2 (by rfl) ⟨3512382, by rfl⟩ : syracuseStep 9366353 = 7024765) B7024765
theorem B9497587 : Blo 1644021 9497587 := bstep (se 1 (by rfl) ⟨7123190, by rfl⟩ : syracuseStep 9497587 = 14246381) B14246381
theorem B14061863 : Blo 1644021 14061863 := bstep (se 1 (by rfl) ⟨10546397, by rfl⟩ : syracuseStep 14061863 = 21092795) B21092795
theorem B60003011 : Blo 1644021 60003011 := bstep (se 1 (by rfl) ⟨45002258, by rfl⟩ : syracuseStep 60003011 = 90004517) B90004517
theorem B7500833 : Blo 1644021 7500833 := bstep (se 2 (by rfl) ⟨2812812, by rfl⟩ : syracuseStep 7500833 = 5625625) B5625625
theorem B3953785 : Blo 1644021 3953785 := bstep (se 2 (by rfl) ⟨1482669, by rfl⟩ : syracuseStep 3953785 = 2965339) B2965339
theorem B3699899 : Blo 1644021 3699899 := bstep (se 1 (by rfl) ⟨2774924, by rfl⟩ : syracuseStep 3699899 = 5549849) B5549849
theorem B5551415 : Blo 1644021 5551415 := bstep (se 1 (by rfl) ⟨4163561, by rfl⟩ : syracuseStep 5551415 = 8327123) B8327123
theorem B11859281 : Blo 1644021 11859281 := bstep (se 2 (by rfl) ⟨4447230, by rfl⟩ : syracuseStep 11859281 = 8894461) B8894461
theorem B47420963 : Blo 1644021 47420963 := bstep (se 1 (by rfl) ⟨35565722, by rfl⟩ : syracuseStep 47420963 = 71131445) B71131445
theorem B1644135 : Blo 1644021 1644135 := bstep (se 1 (by rfl) ⟨1233101, by rfl⟩ : syracuseStep 1644135 = 2466203) B2466203
theorem B3700511 : Blo 1644021 3700511 := bstep (se 1 (by rfl) ⟨2775383, by rfl⟩ : syracuseStep 3700511 = 5550767) B5550767
theorem B1644391 : Blo 1644021 1644391 := bstep (se 1 (by rfl) ⟨1233293, by rfl⟩ : syracuseStep 1644391 = 2466587) B2466587
theorem B18741131 : Blo 1644021 18741131 := bstep (se 1 (by rfl) ⟨14055848, by rfl⟩ : syracuseStep 18741131 = 28111697) B28111697
theorem B1644455 : Blo 1644021 1644455 := bstep (se 1 (by rfl) ⟨1233341, by rfl⟩ : syracuseStep 1644455 = 2466683) B2466683
theorem B1644511 : Blo 1644021 1644511 := bstep (se 1 (by rfl) ⟨1233383, by rfl⟩ : syracuseStep 1644511 = 2466767) B2466767
theorem B3512315 : Blo 1644021 3512315 := bstep (se 1 (by rfl) ⟨2634236, by rfl⟩ : syracuseStep 3512315 = 5268473) B5268473
theorem B50657471 : Blo 1644021 50657471 := bstep (se 1 (by rfl) ⟨37993103, by rfl⟩ : syracuseStep 50657471 = 75986207) B75986207
theorem B3700961 : Blo 1644021 3700961 := bstep (se 2 (by rfl) ⟨1387860, by rfl⟩ : syracuseStep 3700961 = 2775721) B2775721
theorem B1644795 : Blo 1644021 1644795 := bstep (se 1 (by rfl) ⟨1233596, by rfl⟩ : syracuseStep 1644795 = 2467193) B2467193
theorem B1644927 : Blo 1644021 1644927 := bstep (se 1 (by rfl) ⟨1233695, by rfl⟩ : syracuseStep 1644927 = 2467391) B2467391
theorem B6248927 : Blo 1644021 6248927 := bstep (se 1 (by rfl) ⟨4686695, by rfl⟩ : syracuseStep 6248927 = 9373391) B9373391
theorem B1645211 : Blo 1644021 1645211 := bstep (se 1 (by rfl) ⟨1233908, by rfl⟩ : syracuseStep 1645211 = 2467817) B2467817
theorem B1645223 : Blo 1644021 1645223 := bstep (se 1 (by rfl) ⟨1233917, by rfl⟩ : syracuseStep 1645223 = 2467835) B2467835
theorem B4447187 : Blo 1644021 4447187 := bstep (se 1 (by rfl) ⟨3335390, by rfl⟩ : syracuseStep 4447187 = 6670781) B6670781
theorem B6249581 : Blo 1644021 6249581 := bstep (se 3 (by rfl) ⟨1171796, by rfl⟩ : syracuseStep 6249581 = 2343593) B2343593
theorem B250199225 : Blo 1644021 250199225 := bstep (se 2 (by rfl) ⟨93824709, by rfl⟩ : syracuseStep 250199225 = 187649419) B187649419
theorem B21069011 : Blo 1644021 21069011 := bstep (se 1 (by rfl) ⟨15801758, by rfl⟩ : syracuseStep 21069011 = 31603517) B31603517
theorem B3702023 : Blo 1644021 3702023 := bstep (se 1 (by rfl) ⟨2776517, by rfl⟩ : syracuseStep 3702023 = 5553035) B5553035
theorem B3702815 : Blo 1644021 3702815 := bstep (se 1 (by rfl) ⟨2777111, by rfl⟩ : syracuseStep 3702815 = 5554223) B5554223
theorem B4685921 : Blo 1644021 4685921 := bstep (se 2 (by rfl) ⟨1757220, by rfl⟩ : syracuseStep 4685921 = 3514441) B3514441
theorem B3702887 : Blo 1644021 3702887 := bstep (se 1 (by rfl) ⟨2777165, by rfl⟩ : syracuseStep 3702887 = 5554331) B5554331
theorem B2080991 : Blo 1644021 2080991 := bstep (se 1 (by rfl) ⟨1560743, by rfl⟩ : syracuseStep 2080991 = 3121487) B3121487
theorem B40002007 : Blo 1644021 40002007 := bstep (se 1 (by rfl) ⟨30001505, by rfl⟩ : syracuseStep 40002007 = 60003011) B60003011
theorem B160129817 : Blo 1644021 160129817 := bstep (se 2 (by rfl) ⟨60048681, by rfl⟩ : syracuseStep 160129817 = 120097363) B120097363
theorem B2466599 : Blo 1644021 2466599 := bstep (se 1 (by rfl) ⟨1849949, by rfl⟩ : syracuseStep 2466599 = 3699899) B3699899
theorem B7906187 : Blo 1644021 7906187 := bstep (se 1 (by rfl) ⟨5929640, by rfl⟩ : syracuseStep 7906187 = 11859281) B11859281
theorem B31613975 : Blo 1644021 31613975 := bstep (se 1 (by rfl) ⟨23710481, by rfl⟩ : syracuseStep 31613975 = 47420963) B47420963
theorem B2467007 : Blo 1644021 2467007 := bstep (se 1 (by rfl) ⟨1850255, by rfl⟩ : syracuseStep 2467007 = 3700511) B3700511
theorem B12494087 : Blo 1644021 12494087 := bstep (se 1 (by rfl) ⟨9370565, by rfl⟩ : syracuseStep 12494087 = 18741131) B18741131
theorem B2467307 : Blo 1644021 2467307 := bstep (se 1 (by rfl) ⟨1850480, by rfl⟩ : syracuseStep 2467307 = 3700961) B3700961
theorem B6244235 : Blo 1644021 6244235 := bstep (se 1 (by rfl) ⟨4683176, by rfl⟩ : syracuseStep 6244235 = 9366353) B9366353
theorem B166799483 : Blo 1644021 166799483 := bstep (se 1 (by rfl) ⟨125099612, by rfl⟩ : syracuseStep 166799483 = 250199225) B250199225
theorem B2468015 : Blo 1644021 2468015 := bstep (se 1 (by rfl) ⟨1851011, by rfl⟩ : syracuseStep 2468015 = 3702023) B3702023
theorem B9374575 : Blo 1644021 9374575 := bstep (se 1 (by rfl) ⟨7030931, by rfl⟩ : syracuseStep 9374575 = 14061863) B14061863
theorem B5000555 : Blo 1644021 5000555 := bstep (se 1 (by rfl) ⟨3750416, by rfl⟩ : syracuseStep 5000555 = 7500833) B7500833
theorem B14061113 : Blo 1644021 14061113 := bstep (se 2 (by rfl) ⟨5272917, by rfl⟩ : syracuseStep 14061113 = 10545835) B10545835
theorem B30027419 : Blo 1644021 30027419 := bstep (se 1 (by rfl) ⟨22520564, by rfl⟩ : syracuseStep 30027419 = 45041129) B45041129
theorem B33771647 : Blo 1644021 33771647 := bstep (se 1 (by rfl) ⟨25328735, by rfl⟩ : syracuseStep 33771647 = 50657471) B50657471
theorem B5271713 : Blo 1644021 5271713 := bstep (se 2 (by rfl) ⟨1976892, by rfl⟩ : syracuseStep 5271713 = 3953785) B3953785
theorem B4165951 : Blo 1644021 4165951 := bstep (se 1 (by rfl) ⟨3124463, by rfl⟩ : syracuseStep 4165951 = 6248927) B6248927
theorem B4166387 : Blo 1644021 4166387 := bstep (se 1 (by rfl) ⟨3124790, by rfl⟩ : syracuseStep 4166387 = 6249581) B6249581
theorem B14046007 : Blo 1644021 14046007 := bstep (se 1 (by rfl) ⟨10534505, by rfl⟩ : syracuseStep 14046007 = 21069011) B21069011
theorem B1644059 : Blo 1644021 1644059 := bstep (se 1 (by rfl) ⟨1233044, by rfl⟩ : syracuseStep 1644059 = 2466089) B2466089
theorem B1644191 : Blo 1644021 1644191 := bstep (se 1 (by rfl) ⟨1233143, by rfl⟩ : syracuseStep 1644191 = 2466287) B2466287
theorem B1644479 : Blo 1644021 1644479 := bstep (se 1 (by rfl) ⟨1233359, by rfl⟩ : syracuseStep 1644479 = 2466719) B2466719
theorem B3700943 : Blo 1644021 3700943 := bstep (se 1 (by rfl) ⟨2775707, by rfl⟩ : syracuseStep 3700943 = 5551415) B5551415
theorem B1644991 : Blo 1644021 1644991 := bstep (se 1 (by rfl) ⟨1233743, by rfl⟩ : syracuseStep 1644991 = 2467487) B2467487
theorem B17783387 : Blo 1644021 17783387 := bstep (se 1 (by rfl) ⟨13337540, by rfl⟩ : syracuseStep 17783387 = 26675081) B26675081
theorem B12663449 : Blo 1644021 12663449 := bstep (se 2 (by rfl) ⟨4748793, by rfl⟩ : syracuseStep 12663449 = 9497587) B9497587
theorem B2341543 : Blo 1644021 2341543 := bstep (se 1 (by rfl) ⟨1756157, by rfl⟩ : syracuseStep 2341543 = 3512315) B3512315
theorem B1185782651 : Blo 1644021 1185782651 := bstep (se 1 (by rfl) ⟨889336988, by rfl⟩ : syracuseStep 1185782651 = 1778673977) B1778673977
theorem B21355433 : Blo 1644021 21355433 := bstep (se 2 (by rfl) ⟨8008287, by rfl⟩ : syracuseStep 21355433 = 16016575) B16016575
theorem B2964791 : Blo 1644021 2964791 := bstep (se 1 (by rfl) ⟨2223593, by rfl⟩ : syracuseStep 2964791 = 4447187) B4447187
theorem B3514475 : Blo 1644021 3514475 := bstep (se 1 (by rfl) ⟨2635856, by rfl⟩ : syracuseStep 3514475 = 5271713) B5271713
theorem B5554601 : Blo 1644021 5554601 := bstep (se 2 (by rfl) ⟨2082975, by rfl⟩ : syracuseStep 5554601 = 4165951) B4165951
theorem B2777591 : Blo 1644021 2777591 := bstep (se 1 (by rfl) ⟨2083193, by rfl⟩ : syracuseStep 2777591 = 4166387) B4166387
theorem B3122057 : Blo 1644021 3122057 := bstep (se 2 (by rfl) ⟨1170771, by rfl⟩ : syracuseStep 3122057 = 2341543) B2341543
theorem B18728009 : Blo 1644021 18728009 := bstep (se 2 (by rfl) ⟨7023003, by rfl⟩ : syracuseStep 18728009 = 14046007) B14046007
theorem B4162823 : Blo 1644021 4162823 := bstep (se 1 (by rfl) ⟨3122117, by rfl⟩ : syracuseStep 4162823 = 6244235) B6244235
theorem B111199655 : Blo 1644021 111199655 := bstep (se 1 (by rfl) ⟨83399741, by rfl⟩ : syracuseStep 111199655 = 166799483) B166799483
theorem B2467295 : Blo 1644021 2467295 := bstep (se 1 (by rfl) ⟨1850471, by rfl⟩ : syracuseStep 2467295 = 3700943) B3700943
theorem B11855591 : Blo 1644021 11855591 := bstep (se 1 (by rfl) ⟨8891693, by rfl⟩ : syracuseStep 11855591 = 17783387) B17783387
theorem B790521767 : Blo 1644021 790521767 := bstep (se 1 (by rfl) ⟨592891325, by rfl⟩ : syracuseStep 790521767 = 1185782651) B1185782651
theorem B1976527 : Blo 1644021 1976527 := bstep (se 1 (by rfl) ⟨1482395, by rfl⟩ : syracuseStep 1976527 = 2964791) B2964791
theorem B9374075 : Blo 1644021 9374075 := bstep (se 1 (by rfl) ⟨7030556, by rfl⟩ : syracuseStep 9374075 = 14061113) B14061113
theorem B2468543 : Blo 1644021 2468543 := bstep (se 1 (by rfl) ⟨1851407, by rfl⟩ : syracuseStep 2468543 = 3702815) B3702815
theorem B3123947 : Blo 1644021 3123947 := bstep (se 1 (by rfl) ⟨2342960, by rfl⟩ : syracuseStep 3123947 = 4685921) B4685921
theorem B2468591 : Blo 1644021 2468591 := bstep (se 1 (by rfl) ⟨1851443, by rfl⟩ : syracuseStep 2468591 = 3702887) B3702887
theorem B22514431 : Blo 1644021 22514431 := bstep (se 1 (by rfl) ⟨16885823, by rfl⟩ : syracuseStep 22514431 = 33771647) B33771647
theorem B106753211 : Blo 1644021 106753211 := bstep (se 1 (by rfl) ⟨80064908, by rfl⟩ : syracuseStep 106753211 = 160129817) B160129817
theorem B5549309 : Blo 1644021 5549309 := bstep (se 3 (by rfl) ⟨1040495, by rfl⟩ : syracuseStep 5549309 = 2080991) B2080991
theorem B5270791 : Blo 1644021 5270791 := bstep (se 1 (by rfl) ⟨3953093, by rfl⟩ : syracuseStep 5270791 = 7906187) B7906187
theorem B8442299 : Blo 1644021 8442299 := bstep (se 1 (by rfl) ⟨6331724, by rfl⟩ : syracuseStep 8442299 = 12663449) B12663449
theorem B20018279 : Blo 1644021 20018279 := bstep (se 1 (by rfl) ⟨15013709, by rfl⟩ : syracuseStep 20018279 = 30027419) B30027419
theorem B1644399 : Blo 1644021 1644399 := bstep (se 1 (by rfl) ⟨1233299, by rfl⟩ : syracuseStep 1644399 = 2466599) B2466599
theorem B53336009 : Blo 1644021 53336009 := bstep (se 2 (by rfl) ⟨20001003, by rfl⟩ : syracuseStep 53336009 = 40002007) B40002007
theorem B21075983 : Blo 1644021 21075983 := bstep (se 1 (by rfl) ⟨15806987, by rfl⟩ : syracuseStep 21075983 = 31613975) B31613975
theorem B1644671 : Blo 1644021 1644671 := bstep (se 1 (by rfl) ⟨1233503, by rfl⟩ : syracuseStep 1644671 = 2467007) B2467007
theorem B8329391 : Blo 1644021 8329391 := bstep (se 1 (by rfl) ⟨6247043, by rfl⟩ : syracuseStep 8329391 = 12494087) B12494087
theorem B13334813 : Blo 1644021 13334813 := bstep (se 3 (by rfl) ⟨2500277, by rfl⟩ : syracuseStep 13334813 = 5000555) B5000555
theorem B1644871 : Blo 1644021 1644871 := bstep (se 1 (by rfl) ⟨1233653, by rfl⟩ : syracuseStep 1644871 = 2467307) B2467307
theorem B12499433 : Blo 1644021 12499433 := bstep (se 2 (by rfl) ⟨4687287, by rfl⟩ : syracuseStep 12499433 = 9374575) B9374575
theorem B1645343 : Blo 1644021 1645343 := bstep (se 1 (by rfl) ⟨1234007, by rfl⟩ : syracuseStep 1645343 = 2468015) B2468015
theorem B14236955 : Blo 1644021 14236955 := bstep (se 1 (by rfl) ⟨10677716, by rfl⟩ : syracuseStep 14236955 = 21355433) B21355433
theorem B3703067 : Blo 1644021 3703067 := bstep (se 1 (by rfl) ⟨2777300, by rfl⟩ : syracuseStep 3703067 = 5554601) B5554601
theorem B9371933 : Blo 1644021 9371933 := bstep (se 3 (by rfl) ⟨1757237, by rfl⟩ : syracuseStep 9371933 = 3514475) B3514475
theorem B5628199 : Blo 1644021 5628199 := bstep (se 1 (by rfl) ⟨4221149, by rfl⟩ : syracuseStep 5628199 = 8442299) B8442299
theorem B1851727 : Blo 1644021 1851727 := bstep (se 1 (by rfl) ⟨1388795, by rfl⟩ : syracuseStep 1851727 = 2777591) B2777591
theorem B2081371 : Blo 1644021 2081371 := bstep (se 1 (by rfl) ⟨1561028, by rfl⟩ : syracuseStep 2081371 = 3122057) B3122057
theorem B12485339 : Blo 1644021 12485339 := bstep (se 1 (by rfl) ⟨9364004, by rfl⟩ : syracuseStep 12485339 = 18728009) B18728009
theorem B13345519 : Blo 1644021 13345519 := bstep (se 1 (by rfl) ⟨10009139, by rfl⟩ : syracuseStep 13345519 = 20018279) B20018279
theorem B14050655 : Blo 1644021 14050655 := bstep (se 1 (by rfl) ⟨10537991, by rfl⟩ : syracuseStep 14050655 = 21075983) B21075983
theorem B8889875 : Blo 1644021 8889875 := bstep (se 1 (by rfl) ⟨6667406, by rfl⟩ : syracuseStep 8889875 = 13334813) B13334813
theorem B8332955 : Blo 1644021 8332955 := bstep (se 1 (by rfl) ⟨6249716, by rfl⟩ : syracuseStep 8332955 = 12499433) B12499433
theorem B30019241 : Blo 1644021 30019241 := bstep (se 2 (by rfl) ⟨11257215, by rfl⟩ : syracuseStep 30019241 = 22514431) B22514431
theorem B35557339 : Blo 1644021 35557339 := bstep (se 1 (by rfl) ⟨26668004, by rfl⟩ : syracuseStep 35557339 = 53336009) B53336009
theorem B71168807 : Blo 1644021 71168807 := bstep (se 1 (by rfl) ⟨53376605, by rfl⟩ : syracuseStep 71168807 = 106753211) B106753211
theorem B3699539 : Blo 1644021 3699539 := bstep (se 1 (by rfl) ⟨2774654, by rfl⟩ : syracuseStep 3699539 = 5549309) B5549309
theorem B9491303 : Blo 1644021 9491303 := bstep (se 1 (by rfl) ⟨7118477, by rfl⟩ : syracuseStep 9491303 = 14236955) B14236955
theorem B2775215 : Blo 1644021 2775215 := bstep (se 1 (by rfl) ⟨2081411, by rfl⟩ : syracuseStep 2775215 = 4162823) B4162823
theorem B1644863 : Blo 1644021 1644863 := bstep (se 1 (by rfl) ⟨1233647, by rfl⟩ : syracuseStep 1644863 = 2467295) B2467295
theorem B10541477 : Blo 1644021 10541477 := bstep (se 4 (by rfl) ⟨988263, by rfl⟩ : syracuseStep 10541477 = 1976527) B1976527
theorem B296532413 : Blo 1644021 296532413 := bstep (se 3 (by rfl) ⟨55599827, by rfl⟩ : syracuseStep 296532413 = 111199655) B111199655
theorem B7903727 : Blo 1644021 7903727 := bstep (se 1 (by rfl) ⟨5927795, by rfl⟩ : syracuseStep 7903727 = 11855591) B11855591
theorem B527014511 : Blo 1644021 527014511 := bstep (se 1 (by rfl) ⟨395260883, by rfl⟩ : syracuseStep 527014511 = 790521767) B790521767
theorem B5552927 : Blo 1644021 5552927 := bstep (se 1 (by rfl) ⟨4164695, by rfl⟩ : syracuseStep 5552927 = 8329391) B8329391
theorem B6249383 : Blo 1644021 6249383 := bstep (se 1 (by rfl) ⟨4687037, by rfl⟩ : syracuseStep 6249383 = 9374075) B9374075
theorem B7027721 : Blo 1644021 7027721 := bstep (se 2 (by rfl) ⟨2635395, by rfl⟩ : syracuseStep 7027721 = 5270791) B5270791
theorem B1645695 : Blo 1644021 1645695 := bstep (se 1 (by rfl) ⟨1234271, by rfl⟩ : syracuseStep 1645695 = 2468543) B2468543
theorem B1645727 : Blo 1644021 1645727 := bstep (se 1 (by rfl) ⟨1234295, by rfl⟩ : syracuseStep 1645727 = 2468591) B2468591
theorem B8330525 : Blo 1644021 8330525 := bstep (se 3 (by rfl) ⟨1561973, by rfl⟩ : syracuseStep 8330525 = 3123947) B3123947
theorem B7504265 : Blo 1644021 7504265 := bstep (se 2 (by rfl) ⟨2814099, by rfl⟩ : syracuseStep 7504265 = 5628199) B5628199
theorem B8323559 : Blo 1644021 8323559 := bstep (se 1 (by rfl) ⟨6242669, by rfl⟩ : syracuseStep 8323559 = 12485339) B12485339
theorem B2466359 : Blo 1644021 2466359 := bstep (se 1 (by rfl) ⟨1849769, by rfl⟩ : syracuseStep 2466359 = 3699539) B3699539
theorem B17794025 : Blo 1644021 17794025 := bstep (se 2 (by rfl) ⟨6672759, by rfl⟩ : syracuseStep 17794025 = 13345519) B13345519
theorem B5555303 : Blo 1644021 5555303 := bstep (se 1 (by rfl) ⟨4166477, by rfl⟩ : syracuseStep 5555303 = 8332955) B8332955
theorem B5269151 : Blo 1644021 5269151 := bstep (se 1 (by rfl) ⟨3951863, by rfl⟩ : syracuseStep 5269151 = 7903727) B7903727
theorem B47409785 : Blo 1644021 47409785 := bstep (se 2 (by rfl) ⟨17778669, by rfl⟩ : syracuseStep 47409785 = 35557339) B35557339
theorem B2468711 : Blo 1644021 2468711 := bstep (se 1 (by rfl) ⟨1851533, by rfl⟩ : syracuseStep 2468711 = 3703067) B3703067
theorem B2468969 : Blo 1644021 2468969 := bstep (se 2 (by rfl) ⟨925863, by rfl⟩ : syracuseStep 2468969 = 1851727) B1851727
theorem B9367103 : Blo 1644021 9367103 := bstep (se 1 (by rfl) ⟨7025327, by rfl⟩ : syracuseStep 9367103 = 14050655) B14050655
theorem B5926583 : Blo 1644021 5926583 := bstep (se 1 (by rfl) ⟨4444937, by rfl⟩ : syracuseStep 5926583 = 8889875) B8889875
theorem B351343007 : Blo 1644021 351343007 := bstep (se 1 (by rfl) ⟨263507255, by rfl⟩ : syracuseStep 351343007 = 527014511) B527014511
theorem B4166255 : Blo 1644021 4166255 := bstep (se 1 (by rfl) ⟨3124691, by rfl⟩ : syracuseStep 4166255 = 6249383) B6249383
theorem B25310141 : Blo 1644021 25310141 := bstep (se 3 (by rfl) ⟨4745651, by rfl⟩ : syracuseStep 25310141 = 9491303) B9491303
theorem B6247955 : Blo 1644021 6247955 := bstep (se 1 (by rfl) ⟨4685966, by rfl⟩ : syracuseStep 6247955 = 9371933) B9371933
theorem B47445871 : Blo 1644021 47445871 := bstep (se 1 (by rfl) ⟨35584403, by rfl⟩ : syracuseStep 47445871 = 71168807) B71168807
theorem B2775161 : Blo 1644021 2775161 := bstep (se 2 (by rfl) ⟨1040685, by rfl⟩ : syracuseStep 2775161 = 2081371) B2081371
theorem B1850143 : Blo 1644021 1850143 := bstep (se 1 (by rfl) ⟨1387607, by rfl⟩ : syracuseStep 1850143 = 2775215) B2775215
theorem B7027651 : Blo 1644021 7027651 := bstep (se 1 (by rfl) ⟨5270738, by rfl⟩ : syracuseStep 7027651 = 10541477) B10541477
theorem B197688275 : Blo 1644021 197688275 := bstep (se 1 (by rfl) ⟨148266206, by rfl⟩ : syracuseStep 197688275 = 296532413) B296532413
theorem B3701951 : Blo 1644021 3701951 := bstep (se 1 (by rfl) ⟨2776463, by rfl⟩ : syracuseStep 3701951 = 5552927) B5552927
theorem B4685147 : Blo 1644021 4685147 := bstep (se 1 (by rfl) ⟨3513860, by rfl⟩ : syracuseStep 4685147 = 7027721) B7027721
theorem B5553683 : Blo 1644021 5553683 := bstep (se 1 (by rfl) ⟨4165262, by rfl⟩ : syracuseStep 5553683 = 8330525) B8330525
theorem B20012827 : Blo 1644021 20012827 := bstep (se 1 (by rfl) ⟨15009620, by rfl⟩ : syracuseStep 20012827 = 30019241) B30019241
theorem B2777503 : Blo 1644021 2777503 := bstep (se 1 (by rfl) ⟨2083127, by rfl⟩ : syracuseStep 2777503 = 4166255) B4166255
theorem B11862683 : Blo 1644021 11862683 := bstep (se 1 (by rfl) ⟨8897012, by rfl⟩ : syracuseStep 11862683 = 17794025) B17794025
theorem B3703535 : Blo 1644021 3703535 := bstep (se 1 (by rfl) ⟨2777651, by rfl⟩ : syracuseStep 3703535 = 5555303) B5555303
theorem B2466857 : Blo 1644021 2466857 := bstep (se 2 (by rfl) ⟨925071, by rfl⟩ : syracuseStep 2466857 = 1850143) B1850143
theorem B31606523 : Blo 1644021 31606523 := bstep (se 1 (by rfl) ⟨23704892, by rfl⟩ : syracuseStep 31606523 = 47409785) B47409785
theorem B2467967 : Blo 1644021 2467967 := bstep (se 1 (by rfl) ⟨1850975, by rfl⟩ : syracuseStep 2467967 = 3701951) B3701951
theorem B3123431 : Blo 1644021 3123431 := bstep (se 1 (by rfl) ⟨2342573, by rfl⟩ : syracuseStep 3123431 = 4685147) B4685147
theorem B26683769 : Blo 1644021 26683769 := bstep (se 2 (by rfl) ⟨10006413, by rfl⟩ : syracuseStep 26683769 = 20012827) B20012827
theorem B6244735 : Blo 1644021 6244735 := bstep (se 1 (by rfl) ⟨4683551, by rfl⟩ : syracuseStep 6244735 = 9367103) B9367103
theorem B3951055 : Blo 1644021 3951055 := bstep (se 1 (by rfl) ⟨2963291, by rfl⟩ : syracuseStep 3951055 = 5926583) B5926583
theorem B63261161 : Blo 1644021 63261161 := bstep (se 2 (by rfl) ⟨23722935, by rfl⟩ : syracuseStep 63261161 = 47445871) B47445871
theorem B234228671 : Blo 1644021 234228671 := bstep (se 1 (by rfl) ⟨175671503, by rfl⟩ : syracuseStep 234228671 = 351343007) B351343007
theorem B5549039 : Blo 1644021 5549039 := bstep (se 1 (by rfl) ⟨4161779, by rfl⟩ : syracuseStep 5549039 = 8323559) B8323559
theorem B4165303 : Blo 1644021 4165303 := bstep (se 1 (by rfl) ⟨3123977, by rfl⟩ : syracuseStep 4165303 = 6247955) B6247955
theorem B5002843 : Blo 1644021 5002843 := bstep (se 1 (by rfl) ⟨3752132, by rfl⟩ : syracuseStep 5002843 = 7504265) B7504265
theorem B1644239 : Blo 1644021 1644239 := bstep (se 1 (by rfl) ⟨1233179, by rfl⟩ : syracuseStep 1644239 = 2466359) B2466359
theorem B16873427 : Blo 1644021 16873427 := bstep (se 1 (by rfl) ⟨12655070, by rfl⟩ : syracuseStep 16873427 = 25310141) B25310141
theorem B3512767 : Blo 1644021 3512767 := bstep (se 1 (by rfl) ⟨2634575, by rfl⟩ : syracuseStep 3512767 = 5269151) B5269151
theorem B9370201 : Blo 1644021 9370201 := bstep (se 2 (by rfl) ⟨3513825, by rfl⟩ : syracuseStep 9370201 = 7027651) B7027651
theorem B1850107 : Blo 1644021 1850107 := bstep (se 1 (by rfl) ⟨1387580, by rfl⟩ : syracuseStep 1850107 = 2775161) B2775161
theorem B1645807 : Blo 1644021 1645807 := bstep (se 1 (by rfl) ⟨1234355, by rfl⟩ : syracuseStep 1645807 = 2468711) B2468711
theorem B131792183 : Blo 1644021 131792183 := bstep (se 1 (by rfl) ⟨98844137, by rfl⟩ : syracuseStep 131792183 = 197688275) B197688275
theorem B1645979 : Blo 1644021 1645979 := bstep (se 1 (by rfl) ⟨1234484, by rfl⟩ : syracuseStep 1645979 = 2468969) B2468969
theorem B3702455 : Blo 1644021 3702455 := bstep (se 1 (by rfl) ⟨2776841, by rfl⟩ : syracuseStep 3702455 = 5553683) B5553683
theorem B3703337 : Blo 1644021 3703337 := bstep (se 2 (by rfl) ⟨1388751, by rfl⟩ : syracuseStep 3703337 = 2777503) B2777503
theorem B5268073 : Blo 1644021 5268073 := bstep (se 2 (by rfl) ⟨1975527, by rfl⟩ : syracuseStep 5268073 = 3951055) B3951055
theorem B12493601 : Blo 1644021 12493601 := bstep (se 2 (by rfl) ⟨4685100, by rfl⟩ : syracuseStep 12493601 = 9370201) B9370201
theorem B2466809 : Blo 1644021 2466809 := bstep (se 2 (by rfl) ⟨925053, by rfl⟩ : syracuseStep 2466809 = 1850107) B1850107
theorem B21071015 : Blo 1644021 21071015 := bstep (se 1 (by rfl) ⟨15803261, by rfl⟩ : syracuseStep 21071015 = 31606523) B31606523
theorem B11248951 : Blo 1644021 11248951 := bstep (se 1 (by rfl) ⟨8436713, by rfl⟩ : syracuseStep 11248951 = 16873427) B16873427
theorem B2082287 : Blo 1644021 2082287 := bstep (se 1 (by rfl) ⟨1561715, by rfl⟩ : syracuseStep 2082287 = 3123431) B3123431
theorem B42174107 : Blo 1644021 42174107 := bstep (se 1 (by rfl) ⟨31630580, by rfl⟩ : syracuseStep 42174107 = 63261161) B63261161
theorem B6670457 : Blo 1644021 6670457 := bstep (se 2 (by rfl) ⟨2501421, by rfl⟩ : syracuseStep 6670457 = 5002843) B5002843
theorem B87861455 : Blo 1644021 87861455 := bstep (se 1 (by rfl) ⟨65896091, by rfl⟩ : syracuseStep 87861455 = 131792183) B131792183
theorem B2468303 : Blo 1644021 2468303 := bstep (se 1 (by rfl) ⟨1851227, by rfl⟩ : syracuseStep 2468303 = 3702455) B3702455
theorem B7908455 : Blo 1644021 7908455 := bstep (se 1 (by rfl) ⟨5931341, by rfl⟩ : syracuseStep 7908455 = 11862683) B11862683
theorem B2469023 : Blo 1644021 2469023 := bstep (se 1 (by rfl) ⟨1851767, by rfl⟩ : syracuseStep 2469023 = 3703535) B3703535
theorem B8326313 : Blo 1644021 8326313 := bstep (se 2 (by rfl) ⟨3122367, by rfl⟩ : syracuseStep 8326313 = 6244735) B6244735
theorem B17789179 : Blo 1644021 17789179 := bstep (se 1 (by rfl) ⟨13341884, by rfl⟩ : syracuseStep 17789179 = 26683769) B26683769
theorem B156152447 : Blo 1644021 156152447 := bstep (se 1 (by rfl) ⟨117114335, by rfl⟩ : syracuseStep 156152447 = 234228671) B234228671
theorem B3699359 : Blo 1644021 3699359 := bstep (se 1 (by rfl) ⟨2774519, by rfl⟩ : syracuseStep 3699359 = 5549039) B5549039
theorem B4683689 : Blo 1644021 4683689 := bstep (se 2 (by rfl) ⟨1756383, by rfl⟩ : syracuseStep 4683689 = 3512767) B3512767
theorem B1644571 : Blo 1644021 1644571 := bstep (se 1 (by rfl) ⟨1233428, by rfl⟩ : syracuseStep 1644571 = 2466857) B2466857
theorem B1645311 : Blo 1644021 1645311 := bstep (se 1 (by rfl) ⟨1233983, by rfl⟩ : syracuseStep 1645311 = 2467967) B2467967
theorem B5553737 : Blo 1644021 5553737 := bstep (se 2 (by rfl) ⟨2082651, by rfl⟩ : syracuseStep 5553737 = 4165303) B4165303
theorem B2466239 : Blo 1644021 2466239 := bstep (se 1 (by rfl) ⟨1849679, by rfl⟩ : syracuseStep 2466239 = 3699359) B3699359
theorem B28116071 : Blo 1644021 28116071 := bstep (se 1 (by rfl) ⟨21087053, by rfl⟩ : syracuseStep 28116071 = 42174107) B42174107
theorem B3122459 : Blo 1644021 3122459 := bstep (se 1 (by rfl) ⟨2341844, by rfl⟩ : syracuseStep 3122459 = 4683689) B4683689
theorem B58574303 : Blo 1644021 58574303 := bstep (se 1 (by rfl) ⟨43930727, by rfl⟩ : syracuseStep 58574303 = 87861455) B87861455
theorem B23718905 : Blo 1644021 23718905 := bstep (se 2 (by rfl) ⟨8894589, by rfl⟩ : syracuseStep 23718905 = 17789179) B17789179
theorem B2468891 : Blo 1644021 2468891 := bstep (se 1 (by rfl) ⟨1851668, by rfl⟩ : syracuseStep 2468891 = 3703337) B3703337
theorem B7024097 : Blo 1644021 7024097 := bstep (se 2 (by rfl) ⟨2634036, by rfl⟩ : syracuseStep 7024097 = 5268073) B5268073
theorem B5272303 : Blo 1644021 5272303 := bstep (se 1 (by rfl) ⟨3954227, by rfl⟩ : syracuseStep 5272303 = 7908455) B7908455
theorem B5550875 : Blo 1644021 5550875 := bstep (se 1 (by rfl) ⟨4163156, by rfl⟩ : syracuseStep 5550875 = 8326313) B8326313
theorem B104101631 : Blo 1644021 104101631 := bstep (se 1 (by rfl) ⟨78076223, by rfl⟩ : syracuseStep 104101631 = 156152447) B156152447
theorem B8329067 : Blo 1644021 8329067 := bstep (se 1 (by rfl) ⟨6246800, by rfl⟩ : syracuseStep 8329067 = 12493601) B12493601
theorem B1644539 : Blo 1644021 1644539 := bstep (se 1 (by rfl) ⟨1233404, by rfl⟩ : syracuseStep 1644539 = 2466809) B2466809
theorem B14047343 : Blo 1644021 14047343 := bstep (se 1 (by rfl) ⟨10535507, by rfl⟩ : syracuseStep 14047343 = 21071015) B21071015
theorem B5552765 : Blo 1644021 5552765 := bstep (se 3 (by rfl) ⟨1041143, by rfl⟩ : syracuseStep 5552765 = 2082287) B2082287
theorem B4446971 : Blo 1644021 4446971 := bstep (se 1 (by rfl) ⟨3335228, by rfl⟩ : syracuseStep 4446971 = 6670457) B6670457
theorem B1645535 : Blo 1644021 1645535 := bstep (se 1 (by rfl) ⟨1234151, by rfl⟩ : syracuseStep 1645535 = 2468303) B2468303
theorem B14998601 : Blo 1644021 14998601 := bstep (se 2 (by rfl) ⟨5624475, by rfl⟩ : syracuseStep 14998601 = 11248951) B11248951
theorem B1646015 : Blo 1644021 1646015 := bstep (se 1 (by rfl) ⟨1234511, by rfl⟩ : syracuseStep 1646015 = 2469023) B2469023
theorem B3702491 : Blo 1644021 3702491 := bstep (se 1 (by rfl) ⟨2776868, by rfl⟩ : syracuseStep 3702491 = 5553737) B5553737
theorem B18744047 : Blo 1644021 18744047 := bstep (se 1 (by rfl) ⟨14058035, by rfl⟩ : syracuseStep 18744047 = 28116071) B28116071
theorem B2081639 : Blo 1644021 2081639 := bstep (se 1 (by rfl) ⟨1561229, by rfl⟩ : syracuseStep 2081639 = 3122459) B3122459
theorem B7029737 : Blo 1644021 7029737 := bstep (se 2 (by rfl) ⟨2636151, by rfl⟩ : syracuseStep 7029737 = 5272303) B5272303
theorem B9364895 : Blo 1644021 9364895 := bstep (se 1 (by rfl) ⟨7023671, by rfl⟩ : syracuseStep 9364895 = 14047343) B14047343
theorem B15812603 : Blo 1644021 15812603 := bstep (se 1 (by rfl) ⟨11859452, by rfl⟩ : syracuseStep 15812603 = 23718905) B23718905
theorem B2468327 : Blo 1644021 2468327 := bstep (se 1 (by rfl) ⟨1851245, by rfl⟩ : syracuseStep 2468327 = 3702491) B3702491
theorem B18730925 : Blo 1644021 18730925 := bstep (se 3 (by rfl) ⟨3512048, by rfl⟩ : syracuseStep 18730925 = 7024097) B7024097
theorem B9999067 : Blo 1644021 9999067 := bstep (se 1 (by rfl) ⟨7499300, by rfl⟩ : syracuseStep 9999067 = 14998601) B14998601
theorem B1644159 : Blo 1644021 1644159 := bstep (se 1 (by rfl) ⟨1233119, by rfl⟩ : syracuseStep 1644159 = 2466239) B2466239
theorem B3700583 : Blo 1644021 3700583 := bstep (se 1 (by rfl) ⟨2775437, by rfl⟩ : syracuseStep 3700583 = 5550875) B5550875
theorem B39049535 : Blo 1644021 39049535 := bstep (se 1 (by rfl) ⟨29287151, by rfl⟩ : syracuseStep 39049535 = 58574303) B58574303
theorem B69401087 : Blo 1644021 69401087 := bstep (se 1 (by rfl) ⟨52050815, by rfl⟩ : syracuseStep 69401087 = 104101631) B104101631
theorem B5552711 : Blo 1644021 5552711 := bstep (se 1 (by rfl) ⟨4164533, by rfl⟩ : syracuseStep 5552711 = 8329067) B8329067
theorem B3701843 : Blo 1644021 3701843 := bstep (se 1 (by rfl) ⟨2776382, by rfl⟩ : syracuseStep 3701843 = 5552765) B5552765
theorem B2964647 : Blo 1644021 2964647 := bstep (se 1 (by rfl) ⟨2223485, by rfl⟩ : syracuseStep 2964647 = 4446971) B4446971
theorem B1645927 : Blo 1644021 1645927 := bstep (se 1 (by rfl) ⟨1234445, by rfl⟩ : syracuseStep 1645927 = 2468891) B2468891
theorem B7905725 : Blo 1644021 7905725 := bstep (se 3 (by rfl) ⟨1482323, by rfl⟩ : syracuseStep 7905725 = 2964647) B2964647
theorem B4686491 : Blo 1644021 4686491 := bstep (se 1 (by rfl) ⟨3514868, by rfl⟩ : syracuseStep 4686491 = 7029737) B7029737
theorem B6243263 : Blo 1644021 6243263 := bstep (se 1 (by rfl) ⟨4682447, by rfl⟩ : syracuseStep 6243263 = 9364895) B9364895
theorem B2467055 : Blo 1644021 2467055 := bstep (se 1 (by rfl) ⟨1850291, by rfl⟩ : syracuseStep 2467055 = 3700583) B3700583
theorem B2467895 : Blo 1644021 2467895 := bstep (se 1 (by rfl) ⟨1850921, by rfl⟩ : syracuseStep 2467895 = 3701843) B3701843
theorem B12487283 : Blo 1644021 12487283 := bstep (se 1 (by rfl) ⟨9365462, by rfl⟩ : syracuseStep 12487283 = 18730925) B18730925
theorem B12496031 : Blo 1644021 12496031 := bstep (se 1 (by rfl) ⟨9372023, by rfl⟩ : syracuseStep 12496031 = 18744047) B18744047
theorem B13332089 : Blo 1644021 13332089 := bstep (se 2 (by rfl) ⟨4999533, by rfl⟩ : syracuseStep 13332089 = 9999067) B9999067
theorem B5551037 : Blo 1644021 5551037 := bstep (se 3 (by rfl) ⟨1040819, by rfl⟩ : syracuseStep 5551037 = 2081639) B2081639
theorem B10541735 : Blo 1644021 10541735 := bstep (se 1 (by rfl) ⟨7906301, by rfl⟩ : syracuseStep 10541735 = 15812603) B15812603
theorem B26033023 : Blo 1644021 26033023 := bstep (se 1 (by rfl) ⟨19524767, by rfl⟩ : syracuseStep 26033023 = 39049535) B39049535
theorem B1645551 : Blo 1644021 1645551 := bstep (se 1 (by rfl) ⟨1234163, by rfl⟩ : syracuseStep 1645551 = 2468327) B2468327
theorem B46267391 : Blo 1644021 46267391 := bstep (se 1 (by rfl) ⟨34700543, by rfl⟩ : syracuseStep 46267391 = 69401087) B69401087
theorem B3701807 : Blo 1644021 3701807 := bstep (se 1 (by rfl) ⟨2776355, by rfl⟩ : syracuseStep 3701807 = 5552711) B5552711
theorem B4162175 : Blo 1644021 4162175 := bstep (se 1 (by rfl) ⟨3121631, by rfl⟩ : syracuseStep 4162175 = 6243263) B6243263
theorem B34710697 : Blo 1644021 34710697 := bstep (se 2 (by rfl) ⟨13016511, by rfl⟩ : syracuseStep 34710697 = 26033023) B26033023
theorem B8324855 : Blo 1644021 8324855 := bstep (se 1 (by rfl) ⟨6243641, by rfl⟩ : syracuseStep 8324855 = 12487283) B12487283
theorem B30844927 : Blo 1644021 30844927 := bstep (se 1 (by rfl) ⟨23133695, by rfl⟩ : syracuseStep 30844927 = 46267391) B46267391
theorem B2467871 : Blo 1644021 2467871 := bstep (se 1 (by rfl) ⟨1850903, by rfl⟩ : syracuseStep 2467871 = 3701807) B3701807
theorem B5270483 : Blo 1644021 5270483 := bstep (se 1 (by rfl) ⟨3952862, by rfl⟩ : syracuseStep 5270483 = 7905725) B7905725
theorem B3124327 : Blo 1644021 3124327 := bstep (se 1 (by rfl) ⟨2343245, by rfl⟩ : syracuseStep 3124327 = 4686491) B4686491
theorem B3700691 : Blo 1644021 3700691 := bstep (se 1 (by rfl) ⟨2775518, by rfl⟩ : syracuseStep 3700691 = 5551037) B5551037
theorem B1644703 : Blo 1644021 1644703 := bstep (se 1 (by rfl) ⟨1233527, by rfl⟩ : syracuseStep 1644703 = 2467055) B2467055
theorem B1645263 : Blo 1644021 1645263 := bstep (se 1 (by rfl) ⟨1233947, by rfl⟩ : syracuseStep 1645263 = 2467895) B2467895
theorem B7027823 : Blo 1644021 7027823 := bstep (se 1 (by rfl) ⟨5270867, by rfl⟩ : syracuseStep 7027823 = 10541735) B10541735
theorem B8330687 : Blo 1644021 8330687 := bstep (se 1 (by rfl) ⟨6248015, by rfl⟩ : syracuseStep 8330687 = 12496031) B12496031
theorem B8888059 : Blo 1644021 8888059 := bstep (se 1 (by rfl) ⟨6666044, by rfl⟩ : syracuseStep 8888059 = 13332089) B13332089
theorem B2467127 : Blo 1644021 2467127 := bstep (se 1 (by rfl) ⟨1850345, by rfl⟩ : syracuseStep 2467127 = 3700691) B3700691
theorem B164506277 : Blo 1644021 164506277 := bstep (se 4 (by rfl) ⟨15422463, by rfl⟩ : syracuseStep 164506277 = 30844927) B30844927
theorem B5549903 : Blo 1644021 5549903 := bstep (se 1 (by rfl) ⟨4162427, by rfl⟩ : syracuseStep 5549903 = 8324855) B8324855
theorem B4165769 : Blo 1644021 4165769 := bstep (se 2 (by rfl) ⟨1562163, by rfl⟩ : syracuseStep 4165769 = 3124327) B3124327
theorem B46280929 : Blo 1644021 46280929 := bstep (se 2 (by rfl) ⟨17355348, by rfl⟩ : syracuseStep 46280929 = 34710697) B34710697
theorem B11850745 : Blo 1644021 11850745 := bstep (se 2 (by rfl) ⟨4444029, by rfl⟩ : syracuseStep 11850745 = 8888059) B8888059
theorem B2774783 : Blo 1644021 2774783 := bstep (se 1 (by rfl) ⟨2081087, by rfl⟩ : syracuseStep 2774783 = 4162175) B4162175
theorem B1645247 : Blo 1644021 1645247 := bstep (se 1 (by rfl) ⟨1233935, by rfl⟩ : syracuseStep 1645247 = 2467871) B2467871
theorem B3513655 : Blo 1644021 3513655 := bstep (se 1 (by rfl) ⟨2635241, by rfl⟩ : syracuseStep 3513655 = 5270483) B5270483
theorem B4685215 : Blo 1644021 4685215 := bstep (se 1 (by rfl) ⟨3513911, by rfl⟩ : syracuseStep 4685215 = 7027823) B7027823
theorem B5553791 : Blo 1644021 5553791 := bstep (se 1 (by rfl) ⟨4165343, by rfl⟩ : syracuseStep 5553791 = 8330687) B8330687
theorem B2777179 : Blo 1644021 2777179 := bstep (se 1 (by rfl) ⟨2082884, by rfl⟩ : syracuseStep 2777179 = 4165769) B4165769
theorem B109670851 : Blo 1644021 109670851 := bstep (se 1 (by rfl) ⟨82253138, by rfl⟩ : syracuseStep 109670851 = 164506277) B164506277
theorem B6246953 : Blo 1644021 6246953 := bstep (se 2 (by rfl) ⟨2342607, by rfl⟩ : syracuseStep 6246953 = 4685215) B4685215
theorem B3699935 : Blo 1644021 3699935 := bstep (se 1 (by rfl) ⟨2774951, by rfl⟩ : syracuseStep 3699935 = 5549903) B5549903
theorem B61707905 : Blo 1644021 61707905 := bstep (se 2 (by rfl) ⟨23140464, by rfl⟩ : syracuseStep 61707905 = 46280929) B46280929
theorem B1644751 : Blo 1644021 1644751 := bstep (se 1 (by rfl) ⟨1233563, by rfl⟩ : syracuseStep 1644751 = 2467127) B2467127
theorem B1849855 : Blo 1644021 1849855 := bstep (se 1 (by rfl) ⟨1387391, by rfl⟩ : syracuseStep 1849855 = 2774783) B2774783
theorem B15800993 : Blo 1644021 15800993 := bstep (se 2 (by rfl) ⟨5925372, by rfl⟩ : syracuseStep 15800993 = 11850745) B11850745
theorem B4684873 : Blo 1644021 4684873 := bstep (se 2 (by rfl) ⟨1756827, by rfl⟩ : syracuseStep 4684873 = 3513655) B3513655
theorem B3702527 : Blo 1644021 3702527 := bstep (se 1 (by rfl) ⟨2776895, by rfl⟩ : syracuseStep 3702527 = 5553791) B5553791
theorem B3702905 : Blo 1644021 3702905 := bstep (se 2 (by rfl) ⟨1388589, by rfl⟩ : syracuseStep 3702905 = 2777179) B2777179
theorem B2466473 : Blo 1644021 2466473 := bstep (se 2 (by rfl) ⟨924927, by rfl⟩ : syracuseStep 2466473 = 1849855) B1849855
theorem B2466623 : Blo 1644021 2466623 := bstep (se 1 (by rfl) ⟨1849967, by rfl⟩ : syracuseStep 2466623 = 3699935) B3699935
theorem B584911205 : Blo 1644021 584911205 := bstep (se 4 (by rfl) ⟨54835425, by rfl⟩ : syracuseStep 584911205 = 109670851) B109670851
theorem B2468351 : Blo 1644021 2468351 := bstep (se 1 (by rfl) ⟨1851263, by rfl⟩ : syracuseStep 2468351 = 3702527) B3702527
theorem B4164635 : Blo 1644021 4164635 := bstep (se 1 (by rfl) ⟨3123476, by rfl⟩ : syracuseStep 4164635 = 6246953) B6246953
theorem B6246497 : Blo 1644021 6246497 := bstep (se 2 (by rfl) ⟨2342436, by rfl⟩ : syracuseStep 6246497 = 4684873) B4684873
theorem B41138603 : Blo 1644021 41138603 := bstep (se 1 (by rfl) ⟨30853952, by rfl⟩ : syracuseStep 41138603 = 61707905) B61707905
theorem B10533995 : Blo 1644021 10533995 := bstep (se 1 (by rfl) ⟨7900496, by rfl⟩ : syracuseStep 10533995 = 15800993) B15800993
theorem B389940803 : Blo 1644021 389940803 := bstep (se 1 (by rfl) ⟨292455602, by rfl⟩ : syracuseStep 389940803 = 584911205) B584911205
theorem B7022663 : Blo 1644021 7022663 := bstep (se 1 (by rfl) ⟨5266997, by rfl⟩ : syracuseStep 7022663 = 10533995) B10533995
theorem B4164331 : Blo 1644021 4164331 := bstep (se 1 (by rfl) ⟨3123248, by rfl⟩ : syracuseStep 4164331 = 6246497) B6246497
theorem B2468603 : Blo 1644021 2468603 := bstep (se 1 (by rfl) ⟨1851452, by rfl⟩ : syracuseStep 2468603 = 3702905) B3702905
theorem B1644315 : Blo 1644021 1644315 := bstep (se 1 (by rfl) ⟨1233236, by rfl⟩ : syracuseStep 1644315 = 2466473) B2466473
theorem B1644415 : Blo 1644021 1644415 := bstep (se 1 (by rfl) ⟨1233311, by rfl⟩ : syracuseStep 1644415 = 2466623) B2466623
theorem B27425735 : Blo 1644021 27425735 := bstep (se 1 (by rfl) ⟨20569301, by rfl⟩ : syracuseStep 27425735 = 41138603) B41138603
theorem B1645567 : Blo 1644021 1645567 := bstep (se 1 (by rfl) ⟨1234175, by rfl⟩ : syracuseStep 1645567 = 2468351) B2468351
theorem B2776423 : Blo 1644021 2776423 := bstep (se 1 (by rfl) ⟨2082317, by rfl⟩ : syracuseStep 2776423 = 4164635) B4164635
theorem B259960535 : Blo 1644021 259960535 := bstep (se 1 (by rfl) ⟨194970401, by rfl⟩ : syracuseStep 259960535 = 389940803) B389940803
theorem B4681775 : Blo 1644021 4681775 := bstep (se 1 (by rfl) ⟨3511331, by rfl⟩ : syracuseStep 4681775 = 7022663) B7022663
theorem B5552441 : Blo 1644021 5552441 := bstep (se 2 (by rfl) ⟨2082165, by rfl⟩ : syracuseStep 5552441 = 4164331) B4164331
theorem B3701897 : Blo 1644021 3701897 := bstep (se 2 (by rfl) ⟨1388211, by rfl⟩ : syracuseStep 3701897 = 2776423) B2776423
theorem B1645735 : Blo 1644021 1645735 := bstep (se 1 (by rfl) ⟨1234301, by rfl⟩ : syracuseStep 1645735 = 2468603) B2468603
theorem B18283823 : Blo 1644021 18283823 := bstep (se 1 (by rfl) ⟨13712867, by rfl⟩ : syracuseStep 18283823 = 27425735) B27425735
theorem B3121183 : Blo 1644021 3121183 := bstep (se 1 (by rfl) ⟨2340887, by rfl⟩ : syracuseStep 3121183 = 4681775) B4681775
theorem B2467931 : Blo 1644021 2467931 := bstep (se 1 (by rfl) ⟨1850948, by rfl⟩ : syracuseStep 2467931 = 3701897) B3701897
theorem B173307023 : Blo 1644021 173307023 := bstep (se 1 (by rfl) ⟨129980267, by rfl⟩ : syracuseStep 173307023 = 259960535) B259960535
theorem B3701627 : Blo 1644021 3701627 := bstep (se 1 (by rfl) ⟨2776220, by rfl⟩ : syracuseStep 3701627 = 5552441) B5552441
theorem B12189215 : Blo 1644021 12189215 := bstep (se 1 (by rfl) ⟨9141911, by rfl⟩ : syracuseStep 12189215 = 18283823) B18283823
theorem B4161577 : Blo 1644021 4161577 := bstep (se 2 (by rfl) ⟨1560591, by rfl⟩ : syracuseStep 4161577 = 3121183) B3121183
theorem B2467751 : Blo 1644021 2467751 := bstep (se 1 (by rfl) ⟨1850813, by rfl⟩ : syracuseStep 2467751 = 3701627) B3701627
theorem B115538015 : Blo 1644021 115538015 := bstep (se 1 (by rfl) ⟨86653511, by rfl⟩ : syracuseStep 115538015 = 173307023) B173307023
theorem B1645287 : Blo 1644021 1645287 := bstep (se 1 (by rfl) ⟨1233965, by rfl⟩ : syracuseStep 1645287 = 2467931) B2467931
theorem B8126143 : Blo 1644021 8126143 := bstep (se 1 (by rfl) ⟨6094607, by rfl⟩ : syracuseStep 8126143 = 12189215) B12189215
theorem B5548769 : Blo 1644021 5548769 := bstep (se 2 (by rfl) ⟨2080788, by rfl⟩ : syracuseStep 5548769 = 4161577) B4161577
theorem B43339429 : Blo 1644021 43339429 := bstep (se 4 (by rfl) ⟨4063071, by rfl⟩ : syracuseStep 43339429 = 8126143) B8126143
theorem B77025343 : Blo 1644021 77025343 := bstep (se 1 (by rfl) ⟨57769007, by rfl⟩ : syracuseStep 77025343 = 115538015) B115538015
theorem B1645167 : Blo 1644021 1645167 := bstep (se 1 (by rfl) ⟨1233875, by rfl⟩ : syracuseStep 1645167 = 2467751) B2467751
theorem B3699179 : Blo 1644021 3699179 := bstep (se 1 (by rfl) ⟨2774384, by rfl⟩ : syracuseStep 3699179 = 5548769) B5548769
theorem B102700457 : Blo 1644021 102700457 := bstep (se 2 (by rfl) ⟨38512671, by rfl⟩ : syracuseStep 102700457 = 77025343) B77025343
theorem B57785905 : Blo 1644021 57785905 := bstep (se 2 (by rfl) ⟨21669714, by rfl⟩ : syracuseStep 57785905 = 43339429) B43339429
theorem B308191493 : Blo 1644021 308191493 := bstep (se 4 (by rfl) ⟨28892952, by rfl⟩ : syracuseStep 308191493 = 57785905) B57785905
theorem B2466119 : Blo 1644021 2466119 := bstep (se 1 (by rfl) ⟨1849589, by rfl⟩ : syracuseStep 2466119 = 3699179) B3699179
theorem B68466971 : Blo 1644021 68466971 := bstep (se 1 (by rfl) ⟨51350228, by rfl⟩ : syracuseStep 68466971 = 102700457) B102700457
theorem B205460995 : Blo 1644021 205460995 := bstep (se 1 (by rfl) ⟨154095746, by rfl⟩ : syracuseStep 205460995 = 308191493) B308191493
theorem B1644079 : Blo 1644021 1644079 := bstep (se 1 (by rfl) ⟨1233059, by rfl⟩ : syracuseStep 1644079 = 2466119) B2466119
theorem B45644647 : Blo 1644021 45644647 := bstep (se 1 (by rfl) ⟨34233485, by rfl⟩ : syracuseStep 45644647 = 68466971) B68466971
theorem B60859529 : Blo 1644021 60859529 := bstep (se 2 (by rfl) ⟨22822323, by rfl⟩ : syracuseStep 60859529 = 45644647) B45644647
theorem B273947993 : Blo 1644021 273947993 := bstep (se 2 (by rfl) ⟨102730497, by rfl⟩ : syracuseStep 273947993 = 205460995) B205460995
theorem B40573019 : Blo 1644021 40573019 := bstep (se 1 (by rfl) ⟨30429764, by rfl⟩ : syracuseStep 40573019 = 60859529) B60859529
theorem B182631995 : Blo 1644021 182631995 := bstep (se 1 (by rfl) ⟨136973996, by rfl⟩ : syracuseStep 182631995 = 273947993) B273947993
theorem B108194717 : Blo 1644021 108194717 := bstep (se 3 (by rfl) ⟨20286509, by rfl⟩ : syracuseStep 108194717 = 40573019) B40573019
theorem B121754663 : Blo 1644021 121754663 := bstep (se 1 (by rfl) ⟨91315997, by rfl⟩ : syracuseStep 121754663 = 182631995) B182631995
theorem B81169775 : Blo 1644021 81169775 := bstep (se 1 (by rfl) ⟨60877331, by rfl⟩ : syracuseStep 81169775 = 121754663) B121754663
theorem B288519245 : Blo 1644021 288519245 := bstep (se 3 (by rfl) ⟨54097358, by rfl⟩ : syracuseStep 288519245 = 108194717) B108194717
theorem B54113183 : Blo 1644021 54113183 := bstep (se 1 (by rfl) ⟨40584887, by rfl⟩ : syracuseStep 54113183 = 81169775) B81169775
theorem B192346163 : Blo 1644021 192346163 := bstep (se 1 (by rfl) ⟨144259622, by rfl⟩ : syracuseStep 192346163 = 288519245) B288519245
theorem B128230775 : Blo 1644021 128230775 := bstep (se 1 (by rfl) ⟨96173081, by rfl⟩ : syracuseStep 128230775 = 192346163) B192346163
theorem B36075455 : Blo 1644021 36075455 := bstep (se 1 (by rfl) ⟨27056591, by rfl⟩ : syracuseStep 36075455 = 54113183) B54113183
theorem B85487183 : Blo 1644021 85487183 := bstep (se 1 (by rfl) ⟨64115387, by rfl⟩ : syracuseStep 85487183 = 128230775) B128230775
theorem B24050303 : Blo 1644021 24050303 := bstep (se 1 (by rfl) ⟨18037727, by rfl⟩ : syracuseStep 24050303 = 36075455) B36075455
theorem B16033535 : Blo 1644021 16033535 := bstep (se 1 (by rfl) ⟨12025151, by rfl⟩ : syracuseStep 16033535 = 24050303) B24050303
theorem B56991455 : Blo 1644021 56991455 := bstep (se 1 (by rfl) ⟨42743591, by rfl⟩ : syracuseStep 56991455 = 85487183) B85487183
theorem B10689023 : Blo 1644021 10689023 := bstep (se 1 (by rfl) ⟨8016767, by rfl⟩ : syracuseStep 10689023 = 16033535) B16033535
theorem B37994303 : Blo 1644021 37994303 := bstep (se 1 (by rfl) ⟨28495727, by rfl⟩ : syracuseStep 37994303 = 56991455) B56991455
theorem B28504061 : Blo 1644021 28504061 := bstep (se 3 (by rfl) ⟨5344511, by rfl⟩ : syracuseStep 28504061 = 10689023) B10689023
theorem B101318141 : Blo 1644021 101318141 := bstep (se 3 (by rfl) ⟨18997151, by rfl⟩ : syracuseStep 101318141 = 37994303) B37994303
theorem B67545427 : Blo 1644021 67545427 := bstep (se 1 (by rfl) ⟨50659070, by rfl⟩ : syracuseStep 67545427 = 101318141) B101318141
theorem B19002707 : Blo 1644021 19002707 := bstep (se 1 (by rfl) ⟨14252030, by rfl⟩ : syracuseStep 19002707 = 28504061) B28504061
theorem B12668471 : Blo 1644021 12668471 := bstep (se 1 (by rfl) ⟨9501353, by rfl⟩ : syracuseStep 12668471 = 19002707) B19002707
theorem B90060569 : Blo 1644021 90060569 := bstep (se 2 (by rfl) ⟨33772713, by rfl⟩ : syracuseStep 90060569 = 67545427) B67545427
theorem B60040379 : Blo 1644021 60040379 := bstep (se 1 (by rfl) ⟨45030284, by rfl⟩ : syracuseStep 60040379 = 90060569) B90060569
theorem B8445647 : Blo 1644021 8445647 := bstep (se 1 (by rfl) ⟨6334235, by rfl⟩ : syracuseStep 8445647 = 12668471) B12668471
theorem B40026919 : Blo 1644021 40026919 := bstep (se 1 (by rfl) ⟨30020189, by rfl⟩ : syracuseStep 40026919 = 60040379) B60040379
theorem B22521725 : Blo 1644021 22521725 := bstep (se 3 (by rfl) ⟨4222823, by rfl⟩ : syracuseStep 22521725 = 8445647) B8445647
theorem B53369225 : Blo 1644021 53369225 := bstep (se 2 (by rfl) ⟨20013459, by rfl⟩ : syracuseStep 53369225 = 40026919) B40026919
theorem B15014483 : Blo 1644021 15014483 := bstep (se 1 (by rfl) ⟨11260862, by rfl⟩ : syracuseStep 15014483 = 22521725) B22521725
theorem B35579483 : Blo 1644021 35579483 := bstep (se 1 (by rfl) ⟨26684612, by rfl⟩ : syracuseStep 35579483 = 53369225) B53369225
theorem B10009655 : Blo 1644021 10009655 := bstep (se 1 (by rfl) ⟨7507241, by rfl⟩ : syracuseStep 10009655 = 15014483) B15014483
theorem B23719655 : Blo 1644021 23719655 := bstep (se 1 (by rfl) ⟨17789741, by rfl⟩ : syracuseStep 23719655 = 35579483) B35579483
theorem B6673103 : Blo 1644021 6673103 := bstep (se 1 (by rfl) ⟨5004827, by rfl⟩ : syracuseStep 6673103 = 10009655) B10009655
theorem B4448735 : Blo 1644021 4448735 := bstep (se 1 (by rfl) ⟨3336551, by rfl⟩ : syracuseStep 4448735 = 6673103) B6673103
theorem B15813103 : Blo 1644021 15813103 := bstep (se 1 (by rfl) ⟨11859827, by rfl⟩ : syracuseStep 15813103 = 23719655) B23719655
theorem B2965823 : Blo 1644021 2965823 := bstep (se 1 (by rfl) ⟨2224367, by rfl⟩ : syracuseStep 2965823 = 4448735) B4448735
theorem B21084137 : Blo 1644021 21084137 := bstep (se 2 (by rfl) ⟨7906551, by rfl⟩ : syracuseStep 21084137 = 15813103) B15813103
theorem B1977215 : Blo 1644021 1977215 := bstep (se 1 (by rfl) ⟨1482911, by rfl⟩ : syracuseStep 1977215 = 2965823) B2965823
theorem B14056091 : Blo 1644021 14056091 := bstep (se 1 (by rfl) ⟨10542068, by rfl⟩ : syracuseStep 14056091 = 21084137) B21084137
theorem B5272573 : Blo 1644021 5272573 := bstep (se 3 (by rfl) ⟨988607, by rfl⟩ : syracuseStep 5272573 = 1977215) B1977215
theorem B9370727 : Blo 1644021 9370727 := bstep (se 1 (by rfl) ⟨7028045, by rfl⟩ : syracuseStep 9370727 = 14056091) B14056091
theorem B7030097 : Blo 1644021 7030097 := bstep (se 2 (by rfl) ⟨2636286, by rfl⟩ : syracuseStep 7030097 = 5272573) B5272573
theorem B6247151 : Blo 1644021 6247151 := bstep (se 1 (by rfl) ⟨4685363, by rfl⟩ : syracuseStep 6247151 = 9370727) B9370727
theorem B4686731 : Blo 1644021 4686731 := bstep (se 1 (by rfl) ⟨3515048, by rfl⟩ : syracuseStep 4686731 = 7030097) B7030097
theorem B4164767 : Blo 1644021 4164767 := bstep (se 1 (by rfl) ⟨3123575, by rfl⟩ : syracuseStep 4164767 = 6247151) B6247151
theorem B3124487 : Blo 1644021 3124487 := bstep (se 1 (by rfl) ⟨2343365, by rfl⟩ : syracuseStep 3124487 = 4686731) B4686731
theorem B2776511 : Blo 1644021 2776511 := bstep (se 1 (by rfl) ⟨2082383, by rfl⟩ : syracuseStep 2776511 = 4164767) B4164767
theorem B2082991 : Blo 1644021 2082991 := bstep (se 1 (by rfl) ⟨1562243, by rfl⟩ : syracuseStep 2082991 = 3124487) B3124487
theorem B1851007 : Blo 1644021 1851007 := bstep (se 1 (by rfl) ⟨1388255, by rfl⟩ : syracuseStep 1851007 = 2776511) B2776511
theorem B2777321 : Blo 1644021 2777321 := bstep (se 2 (by rfl) ⟨1041495, by rfl⟩ : syracuseStep 2777321 = 2082991) B2082991
theorem B2468009 : Blo 1644021 2468009 := bstep (se 2 (by rfl) ⟨925503, by rfl⟩ : syracuseStep 2468009 = 1851007) B1851007
theorem B1851547 : Blo 1644021 1851547 := bstep (se 1 (by rfl) ⟨1388660, by rfl⟩ : syracuseStep 1851547 = 2777321) B2777321
theorem B1645339 : Blo 1644021 1645339 := bstep (se 1 (by rfl) ⟨1234004, by rfl⟩ : syracuseStep 1645339 = 2468009) B2468009
theorem B2468729 : Blo 1644021 2468729 := bstep (se 2 (by rfl) ⟨925773, by rfl⟩ : syracuseStep 2468729 = 1851547) B1851547
theorem B1645819 : Blo 1644021 1645819 := bstep (se 1 (by rfl) ⟨1234364, by rfl⟩ : syracuseStep 1645819 = 2468729) B2468729

theorem C0 (j : ℕ) (h1 : 411005 ≤ j) (h2 : j ≤ 411504) : Blo 1644021 (4 * j + 3) := by
  interval_cases j
  · exact B1644023
  · exact B1644027
  · exact B1644031
  · exact B1644035
  · exact B1644039
  · exact B1644043
  · exact B1644047
  · exact B1644051
  · exact B1644055
  · exact B1644059
  · exact B1644063
  · exact B1644067
  · exact B1644071
  · exact B1644075
  · exact B1644079
  · exact B1644083
  · exact B1644087
  · exact B1644091
  · exact B1644095
  · exact B1644099
  · exact B1644103
  · exact B1644107
  · exact B1644111
  · exact B1644115
  · exact B1644119
  · exact B1644123
  · exact B1644127
  · exact B1644131
  · exact B1644135
  · exact B1644139
  · exact B1644143
  · exact B1644147
  · exact B1644151
  · exact B1644155
  · exact B1644159
  · exact B1644163
  · exact B1644167
  · exact B1644171
  · exact B1644175
  · exact B1644179
  · exact B1644183
  · exact B1644187
  · exact B1644191
  · exact B1644195
  · exact B1644199
  · exact B1644203
  · exact B1644207
  · exact B1644211
  · exact B1644215
  · exact B1644219
  · exact B1644223
  · exact B1644227
  · exact B1644231
  · exact B1644235
  · exact B1644239
  · exact B1644243
  · exact B1644247
  · exact B1644251
  · exact B1644255
  · exact B1644259
  · exact B1644263
  · exact B1644267
  · exact B1644271
  · exact B1644275
  · exact B1644279
  · exact B1644283
  · exact B1644287
  · exact B1644291
  · exact B1644295
  · exact B1644299
  · exact B1644303
  · exact B1644307
  · exact B1644311
  · exact B1644315
  · exact B1644319
  · exact B1644323
  · exact B1644327
  · exact B1644331
  · exact B1644335
  · exact B1644339
  · exact B1644343
  · exact B1644347
  · exact B1644351
  · exact B1644355
  · exact B1644359
  · exact B1644363
  · exact B1644367
  · exact B1644371
  · exact B1644375
  · exact B1644379
  · exact B1644383
  · exact B1644387
  · exact B1644391
  · exact B1644395
  · exact B1644399
  · exact B1644403
  · exact B1644407
  · exact B1644411
  · exact B1644415
  · exact B1644419
  · exact B1644423
  · exact B1644427
  · exact B1644431
  · exact B1644435
  · exact B1644439
  · exact B1644443
  · exact B1644447
  · exact B1644451
  · exact B1644455
  · exact B1644459
  · exact B1644463
  · exact B1644467
  · exact B1644471
  · exact B1644475
  · exact B1644479
  · exact B1644483
  · exact B1644487
  · exact B1644491
  · exact B1644495
  · exact B1644499
  · exact B1644503
  · exact B1644507
  · exact B1644511
  · exact B1644515
  · exact B1644519
  · exact B1644523
  · exact B1644527
  · exact B1644531
  · exact B1644535
  · exact B1644539
  · exact B1644543
  · exact B1644547
  · exact B1644551
  · exact B1644555
  · exact B1644559
  · exact B1644563
  · exact B1644567
  · exact B1644571
  · exact B1644575
  · exact B1644579
  · exact B1644583
  · exact B1644587
  · exact B1644591
  · exact B1644595
  · exact B1644599
  · exact B1644603
  · exact B1644607
  · exact B1644611
  · exact B1644615
  · exact B1644619
  · exact B1644623
  · exact B1644627
  · exact B1644631
  · exact B1644635
  · exact B1644639
  · exact B1644643
  · exact B1644647
  · exact B1644651
  · exact B1644655
  · exact B1644659
  · exact B1644663
  · exact B1644667
  · exact B1644671
  · exact B1644675
  · exact B1644679
  · exact B1644683
  · exact B1644687
  · exact B1644691
  · exact B1644695
  · exact B1644699
  · exact B1644703
  · exact B1644707
  · exact B1644711
  · exact B1644715
  · exact B1644719
  · exact B1644723
  · exact B1644727
  · exact B1644731
  · exact B1644735
  · exact B1644739
  · exact B1644743
  · exact B1644747
  · exact B1644751
  · exact B1644755
  · exact B1644759
  · exact B1644763
  · exact B1644767
  · exact B1644771
  · exact B1644775
  · exact B1644779
  · exact B1644783
  · exact B1644787
  · exact B1644791
  · exact B1644795
  · exact B1644799
  · exact B1644803
  · exact B1644807
  · exact B1644811
  · exact B1644815
  · exact B1644819
  · exact B1644823
  · exact B1644827
  · exact B1644831
  · exact B1644835
  · exact B1644839
  · exact B1644843
  · exact B1644847
  · exact B1644851
  · exact B1644855
  · exact B1644859
  · exact B1644863
  · exact B1644867
  · exact B1644871
  · exact B1644875
  · exact B1644879
  · exact B1644883
  · exact B1644887
  · exact B1644891
  · exact B1644895
  · exact B1644899
  · exact B1644903
  · exact B1644907
  · exact B1644911
  · exact B1644915
  · exact B1644919
  · exact B1644923
  · exact B1644927
  · exact B1644931
  · exact B1644935
  · exact B1644939
  · exact B1644943
  · exact B1644947
  · exact B1644951
  · exact B1644955
  · exact B1644959
  · exact B1644963
  · exact B1644967
  · exact B1644971
  · exact B1644975
  · exact B1644979
  · exact B1644983
  · exact B1644987
  · exact B1644991
  · exact B1644995
  · exact B1644999
  · exact B1645003
  · exact B1645007
  · exact B1645011
  · exact B1645015
  · exact B1645019
  · exact B1645023
  · exact B1645027
  · exact B1645031
  · exact B1645035
  · exact B1645039
  · exact B1645043
  · exact B1645047
  · exact B1645051
  · exact B1645055
  · exact B1645059
  · exact B1645063
  · exact B1645067
  · exact B1645071
  · exact B1645075
  · exact B1645079
  · exact B1645083
  · exact B1645087
  · exact B1645091
  · exact B1645095
  · exact B1645099
  · exact B1645103
  · exact B1645107
  · exact B1645111
  · exact B1645115
  · exact B1645119
  · exact B1645123
  · exact B1645127
  · exact B1645131
  · exact B1645135
  · exact B1645139
  · exact B1645143
  · exact B1645147
  · exact B1645151
  · exact B1645155
  · exact B1645159
  · exact B1645163
  · exact B1645167
  · exact B1645171
  · exact B1645175
  · exact B1645179
  · exact B1645183
  · exact B1645187
  · exact B1645191
  · exact B1645195
  · exact B1645199
  · exact B1645203
  · exact B1645207
  · exact B1645211
  · exact B1645215
  · exact B1645219
  · exact B1645223
  · exact B1645227
  · exact B1645231
  · exact B1645235
  · exact B1645239
  · exact B1645243
  · exact B1645247
  · exact B1645251
  · exact B1645255
  · exact B1645259
  · exact B1645263
  · exact B1645267
  · exact B1645271
  · exact B1645275
  · exact B1645279
  · exact B1645283
  · exact B1645287
  · exact B1645291
  · exact B1645295
  · exact B1645299
  · exact B1645303
  · exact B1645307
  · exact B1645311
  · exact B1645315
  · exact B1645319
  · exact B1645323
  · exact B1645327
  · exact B1645331
  · exact B1645335
  · exact B1645339
  · exact B1645343
  · exact B1645347
  · exact B1645351
  · exact B1645355
  · exact B1645359
  · exact B1645363
  · exact B1645367
  · exact B1645371
  · exact B1645375
  · exact B1645379
  · exact B1645383
  · exact B1645387
  · exact B1645391
  · exact B1645395
  · exact B1645399
  · exact B1645403
  · exact B1645407
  · exact B1645411
  · exact B1645415
  · exact B1645419
  · exact B1645423
  · exact B1645427
  · exact B1645431
  · exact B1645435
  · exact B1645439
  · exact B1645443
  · exact B1645447
  · exact B1645451
  · exact B1645455
  · exact B1645459
  · exact B1645463
  · exact B1645467
  · exact B1645471
  · exact B1645475
  · exact B1645479
  · exact B1645483
  · exact B1645487
  · exact B1645491
  · exact B1645495
  · exact B1645499
  · exact B1645503
  · exact B1645507
  · exact B1645511
  · exact B1645515
  · exact B1645519
  · exact B1645523
  · exact B1645527
  · exact B1645531
  · exact B1645535
  · exact B1645539
  · exact B1645543
  · exact B1645547
  · exact B1645551
  · exact B1645555
  · exact B1645559
  · exact B1645563
  · exact B1645567
  · exact B1645571
  · exact B1645575
  · exact B1645579
  · exact B1645583
  · exact B1645587
  · exact B1645591
  · exact B1645595
  · exact B1645599
  · exact B1645603
  · exact B1645607
  · exact B1645611
  · exact B1645615
  · exact B1645619
  · exact B1645623
  · exact B1645627
  · exact B1645631
  · exact B1645635
  · exact B1645639
  · exact B1645643
  · exact B1645647
  · exact B1645651
  · exact B1645655
  · exact B1645659
  · exact B1645663
  · exact B1645667
  · exact B1645671
  · exact B1645675
  · exact B1645679
  · exact B1645683
  · exact B1645687
  · exact B1645691
  · exact B1645695
  · exact B1645699
  · exact B1645703
  · exact B1645707
  · exact B1645711
  · exact B1645715
  · exact B1645719
  · exact B1645723
  · exact B1645727
  · exact B1645731
  · exact B1645735
  · exact B1645739
  · exact B1645743
  · exact B1645747
  · exact B1645751
  · exact B1645755
  · exact B1645759
  · exact B1645763
  · exact B1645767
  · exact B1645771
  · exact B1645775
  · exact B1645779
  · exact B1645783
  · exact B1645787
  · exact B1645791
  · exact B1645795
  · exact B1645799
  · exact B1645803
  · exact B1645807
  · exact B1645811
  · exact B1645815
  · exact B1645819
  · exact B1645823
  · exact B1645827
  · exact B1645831
  · exact B1645835
  · exact B1645839
  · exact B1645843
  · exact B1645847
  · exact B1645851
  · exact B1645855
  · exact B1645859
  · exact B1645863
  · exact B1645867
  · exact B1645871
  · exact B1645875
  · exact B1645879
  · exact B1645883
  · exact B1645887
  · exact B1645891
  · exact B1645895
  · exact B1645899
  · exact B1645903
  · exact B1645907
  · exact B1645911
  · exact B1645915
  · exact B1645919
  · exact B1645923
  · exact B1645927
  · exact B1645931
  · exact B1645935
  · exact B1645939
  · exact B1645943
  · exact B1645947
  · exact B1645951
  · exact B1645955
  · exact B1645959
  · exact B1645963
  · exact B1645967
  · exact B1645971
  · exact B1645975
  · exact B1645979
  · exact B1645983
  · exact B1645987
  · exact B1645991
  · exact B1645995
  · exact B1645999
  · exact B1646003
  · exact B1646007
  · exact B1646011
  · exact B1646015
  · exact B1646019

theorem solution (m : ℕ) (hlo : 1644021 ≤ m) (hhi : m ≤ 1646021) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 411005 ≤ j := by omega
    have hj2 : j ≤ 411504 := by omega
    have hb : Blo 1644021 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
