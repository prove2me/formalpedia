-- Prove2me | solution 1 for syracuse_descends_range_1695548_1697548
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:24:52.34938+00:00
-- url     : https://prove2.me/submissions/ac681756-1109-4db7-8ff3-819c20280f85

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


theorem B5726213 : Blo 1695548 5726213 := bbase (se 4 (by rfl) ⟨536832, by rfl⟩ : syracuseStep 5726213 = 1073665) (by norm_num)
theorem B3817493 : Blo 1695548 3817493 := bbase (se 6 (by rfl) ⟨89472, by rfl⟩ : syracuseStep 3817493 = 178945) (by norm_num)
theorem B2146333 : Blo 1695548 2146333 := bbase (se 3 (by rfl) ⟨402437, by rfl⟩ : syracuseStep 2146333 = 804875) (by norm_num)
theorem B1908769 : Blo 1695548 1908769 := bbase (se 2 (by rfl) ⟨715788, by rfl⟩ : syracuseStep 1908769 = 1431577) (by norm_num)
theorem B1908805 : Blo 1695548 1908805 := bbase (se 4 (by rfl) ⟨178950, by rfl⟩ : syracuseStep 1908805 = 357901) (by norm_num)
theorem B3817565 : Blo 1695548 3817565 := bbase (se 3 (by rfl) ⟨715793, by rfl⟩ : syracuseStep 3817565 = 1431587) (by norm_num)
theorem B1908841 : Blo 1695548 1908841 := bbase (se 2 (by rfl) ⟨715815, by rfl⟩ : syracuseStep 1908841 = 1431631) (by norm_num)
theorem B2146429 : Blo 1695548 2146429 := bbase (se 3 (by rfl) ⟨402455, by rfl⟩ : syracuseStep 2146429 = 804911) (by norm_num)
theorem B1908877 : Blo 1695548 1908877 := bbase (se 3 (by rfl) ⟨357914, by rfl⟩ : syracuseStep 1908877 = 715829) (by norm_num)
theorem B3055781 : Blo 1695548 3055781 := bbase (se 4 (by rfl) ⟨286479, by rfl⟩ : syracuseStep 3055781 = 572959) (by norm_num)
theorem B3817637 : Blo 1695548 3817637 := bbase (se 4 (by rfl) ⟨357903, by rfl⟩ : syracuseStep 3817637 = 715807) (by norm_num)
theorem B1908913 : Blo 1695548 1908913 := bbase (se 2 (by rfl) ⟨715842, by rfl⟩ : syracuseStep 1908913 = 1431685) (by norm_num)
theorem B4292797 : Blo 1695548 4292797 := bbase (se 3 (by rfl) ⟨804899, by rfl⟩ : syracuseStep 4292797 = 1609799) (by norm_num)
theorem B16302293 : Blo 1695548 16302293 := bbase (se 7 (by rfl) ⟨191042, by rfl⟩ : syracuseStep 16302293 = 382085) (by norm_num)
theorem B1908949 : Blo 1695548 1908949 := bbase (se 7 (by rfl) ⟨22370, by rfl⟩ : syracuseStep 1908949 = 44741) (by norm_num)
theorem B2941157 : Blo 1695548 2941157 := bbase (se 4 (by rfl) ⟨275733, by rfl⟩ : syracuseStep 2941157 = 551467) (by norm_num)
theorem B3817709 : Blo 1695548 3817709 := bbase (se 3 (by rfl) ⟨715820, by rfl⟩ : syracuseStep 3817709 = 1431641) (by norm_num)
theorem B1908985 : Blo 1695548 1908985 := bbase (se 2 (by rfl) ⟨715869, by rfl⟩ : syracuseStep 1908985 = 1431739) (by norm_num)
theorem B1909021 : Blo 1695548 1909021 := bbase (se 3 (by rfl) ⟨357941, by rfl⟩ : syracuseStep 1909021 = 715883) (by norm_num)
theorem B2146601 : Blo 1695548 2146601 := bbase (se 2 (by rfl) ⟨804975, by rfl⟩ : syracuseStep 2146601 = 1609951) (by norm_num)
theorem B4292909 : Blo 1695548 4292909 := bbase (se 3 (by rfl) ⟨804920, by rfl⟩ : syracuseStep 4292909 = 1609841) (by norm_num)
theorem B3817781 : Blo 1695548 3817781 := bbase (se 5 (by rfl) ⟨178958, by rfl⟩ : syracuseStep 3817781 = 357917) (by norm_num)
theorem B4833589 : Blo 1695548 4833589 := bbase (se 5 (by rfl) ⟨226574, by rfl⟩ : syracuseStep 4833589 = 453149) (by norm_num)
theorem B2580797 : Blo 1695548 2580797 := bbase (se 3 (by rfl) ⟨483899, by rfl⟩ : syracuseStep 2580797 = 967799) (by norm_num)
theorem B1909057 : Blo 1695548 1909057 := bbase (se 2 (by rfl) ⟨715896, by rfl⟩ : syracuseStep 1909057 = 1431793) (by norm_num)
theorem B2146657 : Blo 1695548 2146657 := bbase (se 2 (by rfl) ⟨804996, by rfl⟩ : syracuseStep 2146657 = 1609993) (by norm_num)
theorem B1909093 : Blo 1695548 1909093 := bbase (se 4 (by rfl) ⟨178977, by rfl⟩ : syracuseStep 1909093 = 357955) (by norm_num)
theorem B3817853 : Blo 1695548 3817853 := bbase (se 3 (by rfl) ⟨715847, by rfl⟩ : syracuseStep 3817853 = 1431695) (by norm_num)
theorem B1909129 : Blo 1695548 1909129 := bbase (se 2 (by rfl) ⟨715923, by rfl⟩ : syracuseStep 1909129 = 1431847) (by norm_num)
theorem B1909165 : Blo 1695548 1909165 := bbase (se 3 (by rfl) ⟨357968, by rfl⟩ : syracuseStep 1909165 = 715937) (by norm_num)
theorem B5726645 : Blo 1695548 5726645 := bbase (se 5 (by rfl) ⟨268436, by rfl⟩ : syracuseStep 5726645 = 536873) (by norm_num)
theorem B2146753 : Blo 1695548 2146753 := bbase (se 2 (by rfl) ⟨805032, by rfl⟩ : syracuseStep 2146753 = 1610065) (by norm_num)
theorem B3056069 : Blo 1695548 3056069 := bbase (se 4 (by rfl) ⟨286506, by rfl⟩ : syracuseStep 3056069 = 573013) (by norm_num)
theorem B3817925 : Blo 1695548 3817925 := bbase (se 4 (by rfl) ⟨357930, by rfl⟩ : syracuseStep 3817925 = 715861) (by norm_num)
theorem B1909201 : Blo 1695548 1909201 := bbase (se 2 (by rfl) ⟨715950, by rfl⟩ : syracuseStep 1909201 = 1431901) (by norm_num)
theorem B3219925 : Blo 1695548 3219925 := bbase (se 7 (by rfl) ⟨37733, by rfl⟩ : syracuseStep 3219925 = 75467) (by norm_num)
theorem B4833749 : Blo 1695548 4833749 := bbase (se 7 (by rfl) ⟨56645, by rfl⟩ : syracuseStep 4833749 = 113291) (by norm_num)
theorem B4293101 : Blo 1695548 4293101 := bbase (se 3 (by rfl) ⟨804956, by rfl⟩ : syracuseStep 4293101 = 1609913) (by norm_num)
theorem B3621365 : Blo 1695548 3621365 := bbase (se 5 (by rfl) ⟨169751, by rfl⟩ : syracuseStep 3621365 = 339503) (by norm_num)
theorem B1909237 : Blo 1695548 1909237 := bbase (se 5 (by rfl) ⟨89495, by rfl⟩ : syracuseStep 1909237 = 178991) (by norm_num)
theorem B3817997 : Blo 1695548 3817997 := bbase (se 3 (by rfl) ⟨715874, by rfl⟩ : syracuseStep 3817997 = 1431749) (by norm_num)
theorem B1909273 : Blo 1695548 1909273 := bbase (se 2 (by rfl) ⟨715977, by rfl⟩ : syracuseStep 1909273 = 1431955) (by norm_num)
theorem B2581021 : Blo 1695548 2581021 := bbase (se 3 (by rfl) ⟨483941, by rfl⟩ : syracuseStep 2581021 = 967883) (by norm_num)
theorem B13754933 : Blo 1695548 13754933 := bbase (se 5 (by rfl) ⟨644762, by rfl⟩ : syracuseStep 13754933 = 1289525) (by norm_num)
theorem B1909309 : Blo 1695548 1909309 := bbase (se 3 (by rfl) ⟨357995, by rfl⟩ : syracuseStep 1909309 = 715991) (by norm_num)
theorem B3818069 : Blo 1695548 3818069 := bbase (se 8 (by rfl) ⟨22371, by rfl⟩ : syracuseStep 3818069 = 44743) (by norm_num)
theorem B1811041 : Blo 1695548 1811041 := bbase (se 2 (by rfl) ⟨679140, by rfl⟩ : syracuseStep 1811041 = 1358281) (by norm_num)
theorem B1909345 : Blo 1695548 1909345 := bbase (se 2 (by rfl) ⟨716004, by rfl⟩ : syracuseStep 1909345 = 1432009) (by norm_num)
theorem B3220069 : Blo 1695548 3220069 := bbase (se 4 (by rfl) ⟨301881, by rfl⟩ : syracuseStep 3220069 = 603763) (by norm_num)
theorem B3621485 : Blo 1695548 3621485 := bbase (se 3 (by rfl) ⟨679028, by rfl⟩ : syracuseStep 3621485 = 1358057) (by norm_num)
theorem B2146925 : Blo 1695548 2146925 := bbase (se 3 (by rfl) ⟨402548, by rfl⟩ : syracuseStep 2146925 = 805097) (by norm_num)
theorem B1909381 : Blo 1695548 1909381 := bbase (se 4 (by rfl) ⟨179004, by rfl⟩ : syracuseStep 1909381 = 358009) (by norm_num)
theorem B3818141 : Blo 1695548 3818141 := bbase (se 3 (by rfl) ⟨715901, by rfl⟩ : syracuseStep 3818141 = 1431803) (by norm_num)
theorem B2146981 : Blo 1695548 2146981 := bbase (se 4 (by rfl) ⟨201279, by rfl⟩ : syracuseStep 2146981 = 402559) (by norm_num)
theorem B1909417 : Blo 1695548 1909417 := bbase (se 2 (by rfl) ⟨716031, by rfl⟩ : syracuseStep 1909417 = 1432063) (by norm_num)
theorem B6439621 : Blo 1695548 6439621 := bbase (se 4 (by rfl) ⟨603714, by rfl⟩ : syracuseStep 6439621 = 1207429) (by norm_num)
theorem B4833989 : Blo 1695548 4833989 := bbase (se 4 (by rfl) ⟨453186, by rfl⟩ : syracuseStep 4833989 = 906373) (by norm_num)
theorem B1909453 : Blo 1695548 1909453 := bbase (se 3 (by rfl) ⟨358022, by rfl⟩ : syracuseStep 1909453 = 716045) (by norm_num)
theorem B1811161 : Blo 1695548 1811161 := bbase (se 2 (by rfl) ⟨679185, by rfl⟩ : syracuseStep 1811161 = 1358371) (by norm_num)
theorem B3818213 : Blo 1695548 3818213 := bbase (se 4 (by rfl) ⟨357957, by rfl⟩ : syracuseStep 3818213 = 715915) (by norm_num)
theorem B1909489 : Blo 1695548 1909489 := bbase (se 2 (by rfl) ⟨716058, by rfl⟩ : syracuseStep 1909489 = 1432117) (by norm_num)
theorem B3220229 : Blo 1695548 3220229 := bbase (se 4 (by rfl) ⟨301896, by rfl⟩ : syracuseStep 3220229 = 603793) (by norm_num)
theorem B2147077 : Blo 1695548 2147077 := bbase (se 4 (by rfl) ⟨201288, by rfl⟩ : syracuseStep 2147077 = 402577) (by norm_num)
theorem B1909525 : Blo 1695548 1909525 := bbase (se 6 (by rfl) ⟨44754, by rfl⟩ : syracuseStep 1909525 = 89509) (by norm_num)
theorem B7250725 : Blo 1695548 7250725 := bbase (se 4 (by rfl) ⟨679755, by rfl⟩ : syracuseStep 7250725 = 1359511) (by norm_num)
theorem B3818285 : Blo 1695548 3818285 := bbase (se 3 (by rfl) ⟨715928, by rfl⟩ : syracuseStep 3818285 = 1431857) (by norm_num)
theorem B1909561 : Blo 1695548 1909561 := bbase (se 2 (by rfl) ⟨716085, by rfl⟩ : syracuseStep 1909561 = 1432171) (by norm_num)
theorem B4293445 : Blo 1695548 4293445 := bbase (se 4 (by rfl) ⟨402510, by rfl⟩ : syracuseStep 4293445 = 805021) (by norm_num)
theorem B1909597 : Blo 1695548 1909597 := bbase (se 3 (by rfl) ⟨358049, by rfl⟩ : syracuseStep 1909597 = 716099) (by norm_num)
theorem B5727077 : Blo 1695548 5727077 := bbase (se 4 (by rfl) ⟨536913, by rfl⟩ : syracuseStep 5727077 = 1073827) (by norm_num)
theorem B12223349 : Blo 1695548 12223349 := bbase (se 5 (by rfl) ⟨572969, by rfl⟩ : syracuseStep 12223349 = 1145939) (by norm_num)
theorem B3818357 : Blo 1695548 3818357 := bbase (se 5 (by rfl) ⟨178985, by rfl⟩ : syracuseStep 3818357 = 357971) (by norm_num)
theorem B1909633 : Blo 1695548 1909633 := bbase (se 2 (by rfl) ⟨716112, by rfl⟩ : syracuseStep 1909633 = 1432225) (by norm_num)
theorem B3220373 : Blo 1695548 3220373 := bbase (se 6 (by rfl) ⟨75477, by rfl⟩ : syracuseStep 3220373 = 150955) (by norm_num)
theorem B1909669 : Blo 1695548 1909669 := bbase (se 4 (by rfl) ⟨179031, by rfl⟩ : syracuseStep 1909669 = 358063) (by norm_num)
theorem B2147249 : Blo 1695548 2147249 := bbase (se 2 (by rfl) ⟨805218, by rfl⟩ : syracuseStep 2147249 = 1610437) (by norm_num)
theorem B4293557 : Blo 1695548 4293557 := bbase (se 5 (by rfl) ⟨201260, by rfl⟩ : syracuseStep 4293557 = 402521) (by norm_num)
theorem B3818429 : Blo 1695548 3818429 := bbase (se 3 (by rfl) ⟨715955, by rfl⟩ : syracuseStep 3818429 = 1431911) (by norm_num)
theorem B1909705 : Blo 1695548 1909705 := bbase (se 2 (by rfl) ⟨716139, by rfl⟩ : syracuseStep 1909705 = 1432279) (by norm_num)
theorem B1811413 : Blo 1695548 1811413 := bbase (se 7 (by rfl) ⟨21227, by rfl⟩ : syracuseStep 1811413 = 42455) (by norm_num)
theorem B1811417 : Blo 1695548 1811417 := bbase (se 2 (by rfl) ⟨679281, by rfl⟩ : syracuseStep 1811417 = 1358563) (by norm_num)
theorem B6972389 : Blo 1695548 6972389 := bbase (se 4 (by rfl) ⟨653661, by rfl⟩ : syracuseStep 6972389 = 1307323) (by norm_num)
theorem B2147305 : Blo 1695548 2147305 := bbase (se 2 (by rfl) ⟨805239, by rfl⟩ : syracuseStep 2147305 = 1610479) (by norm_num)
theorem B1909741 : Blo 1695548 1909741 := bbase (se 3 (by rfl) ⟨358076, by rfl⟩ : syracuseStep 1909741 = 716153) (by norm_num)
theorem B6439925 : Blo 1695548 6439925 := bbase (se 5 (by rfl) ⟨301871, by rfl⟩ : syracuseStep 6439925 = 603743) (by norm_num)
theorem B3818501 : Blo 1695548 3818501 := bbase (se 4 (by rfl) ⟨357984, by rfl⟩ : syracuseStep 3818501 = 715969) (by norm_num)
theorem B2147401 : Blo 1695548 2147401 := bbase (se 2 (by rfl) ⟨805275, by rfl⟩ : syracuseStep 2147401 = 1610551) (by norm_num)
theorem B3818573 : Blo 1695548 3818573 := bbase (se 3 (by rfl) ⟨715982, by rfl⟩ : syracuseStep 3818573 = 1431965) (by norm_num)
theorem B7742549 : Blo 1695548 7742549 := bbase (se 8 (by rfl) ⟨45366, by rfl⟩ : syracuseStep 7742549 = 90733) (by norm_num)
theorem B4293749 : Blo 1695548 4293749 := bbase (se 5 (by rfl) ⟨201269, by rfl⟩ : syracuseStep 4293749 = 402539) (by norm_num)
theorem B3818645 : Blo 1695548 3818645 := bbase (se 6 (by rfl) ⟨89499, by rfl⟩ : syracuseStep 3818645 = 178999) (by norm_num)
theorem B3220661 : Blo 1695548 3220661 := bbase (se 5 (by rfl) ⟨150968, by rfl⟩ : syracuseStep 3220661 = 301937) (by norm_num)
theorem B3818717 : Blo 1695548 3818717 := bbase (se 3 (by rfl) ⟨716009, by rfl⟩ : syracuseStep 3818717 = 1432019) (by norm_num)
theorem B3622117 : Blo 1695548 3622117 := bbase (se 4 (by rfl) ⟨339573, by rfl⟩ : syracuseStep 3622117 = 679147) (by norm_num)
theorem B8586485 : Blo 1695548 8586485 := bbase (se 5 (by rfl) ⟨402491, by rfl⟩ : syracuseStep 8586485 = 804983) (by norm_num)
theorem B2147573 : Blo 1695548 2147573 := bbase (se 5 (by rfl) ⟨100667, by rfl⟩ : syracuseStep 2147573 = 201335) (by norm_num)
theorem B5727509 : Blo 1695548 5727509 := bbase (se 6 (by rfl) ⟨134238, by rfl⟩ : syracuseStep 5727509 = 268477) (by norm_num)
theorem B3818789 : Blo 1695548 3818789 := bbase (se 4 (by rfl) ⟨358011, by rfl⟩ : syracuseStep 3818789 = 716023) (by norm_num)
theorem B2147629 : Blo 1695548 2147629 := bbase (se 3 (by rfl) ⟨402680, by rfl⟩ : syracuseStep 2147629 = 805361) (by norm_num)
theorem B3220813 : Blo 1695548 3220813 := bbase (se 3 (by rfl) ⟨603902, by rfl⟩ : syracuseStep 3220813 = 1207805) (by norm_num)
theorem B6112597 : Blo 1695548 6112597 := bbase (se 12 (by rfl) ⟨2238, by rfl⟩ : syracuseStep 6112597 = 4477) (by norm_num)
theorem B4351325 : Blo 1695548 4351325 := bbase (se 3 (by rfl) ⟨815873, by rfl⟩ : syracuseStep 4351325 = 1631747) (by norm_num)
theorem B3818861 : Blo 1695548 3818861 := bbase (se 3 (by rfl) ⟨716036, by rfl⟩ : syracuseStep 3818861 = 1432073) (by norm_num)
theorem B2147725 : Blo 1695548 2147725 := bbase (se 3 (by rfl) ⟨402698, by rfl⟩ : syracuseStep 2147725 = 805397) (by norm_num)
theorem B5432741 : Blo 1695548 5432741 := bbase (se 4 (by rfl) ⟨509319, by rfl⟩ : syracuseStep 5432741 = 1018639) (by norm_num)
theorem B11019701 : Blo 1695548 11019701 := bbase (se 5 (by rfl) ⟨516548, by rfl⟩ : syracuseStep 11019701 = 1033097) (by norm_num)
theorem B10872245 : Blo 1695548 10872245 := bbase (se 5 (by rfl) ⟨509636, by rfl⟩ : syracuseStep 10872245 = 1019273) (by norm_num)
theorem B3818933 : Blo 1695548 3818933 := bbase (se 5 (by rfl) ⟨179012, by rfl⟩ : syracuseStep 3818933 = 358025) (by norm_num)
theorem B4294093 : Blo 1695548 4294093 := bbase (se 3 (by rfl) ⟨805142, by rfl⟩ : syracuseStep 4294093 = 1610285) (by norm_num)
theorem B2942453 : Blo 1695548 2942453 := bbase (se 5 (by rfl) ⟨137927, by rfl⟩ : syracuseStep 2942453 = 275855) (by norm_num)
theorem B3819005 : Blo 1695548 3819005 := bbase (se 3 (by rfl) ⟨716063, by rfl⟩ : syracuseStep 3819005 = 1432127) (by norm_num)
theorem B1811981 : Blo 1695548 1811981 := bbase (se 3 (by rfl) ⟨339746, by rfl⟩ : syracuseStep 1811981 = 679493) (by norm_num)
theorem B2147897 : Blo 1695548 2147897 := bbase (se 2 (by rfl) ⟨805461, by rfl⟩ : syracuseStep 2147897 = 1610923) (by norm_num)
theorem B4294205 : Blo 1695548 4294205 := bbase (se 3 (by rfl) ⟨805163, by rfl⟩ : syracuseStep 4294205 = 1610327) (by norm_num)
theorem B3057221 : Blo 1695548 3057221 := bbase (se 4 (by rfl) ⟨286614, by rfl⟩ : syracuseStep 3057221 = 573229) (by norm_num)
theorem B3819077 : Blo 1695548 3819077 := bbase (se 4 (by rfl) ⟨358038, by rfl⟩ : syracuseStep 3819077 = 716077) (by norm_num)
theorem B4130381 : Blo 1695548 4130381 := bbase (se 3 (by rfl) ⟨774446, by rfl⟩ : syracuseStep 4130381 = 1548893) (by norm_num)
theorem B2147953 : Blo 1695548 2147953 := bbase (se 2 (by rfl) ⟨805482, by rfl⟩ : syracuseStep 2147953 = 1610965) (by norm_num)
theorem B3221117 : Blo 1695548 3221117 := bbase (se 3 (by rfl) ⟨603959, by rfl⟩ : syracuseStep 3221117 = 1207919) (by norm_num)
theorem B3819149 : Blo 1695548 3819149 := bbase (se 3 (by rfl) ⟨716090, by rfl⟩ : syracuseStep 3819149 = 1432181) (by norm_num)
theorem B3057301 : Blo 1695548 3057301 := bbase (se 6 (by rfl) ⟨71655, by rfl⟩ : syracuseStep 3057301 = 143311) (by norm_num)
theorem B5727941 : Blo 1695548 5727941 := bbase (se 4 (by rfl) ⟨536994, by rfl⟩ : syracuseStep 5727941 = 1073989) (by norm_num)
theorem B1812169 : Blo 1695548 1812169 := bbase (se 2 (by rfl) ⟨679563, by rfl⟩ : syracuseStep 1812169 = 1359127) (by norm_num)
theorem B2148049 : Blo 1695548 2148049 := bbase (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) (by norm_num)
theorem B3819221 : Blo 1695548 3819221 := bbase (se 7 (by rfl) ⟨44756, by rfl⟩ : syracuseStep 3819221 = 89513) (by norm_num)
theorem B9176789 : Blo 1695548 9176789 := bbase (se 7 (by rfl) ⟨107540, by rfl⟩ : syracuseStep 9176789 = 215081) (by norm_num)
theorem B4294397 : Blo 1695548 4294397 := bbase (se 3 (by rfl) ⟨805199, by rfl⟩ : syracuseStep 4294397 = 1610399) (by norm_num)
theorem B3819293 : Blo 1695548 3819293 := bbase (se 3 (by rfl) ⟨716117, by rfl⟩ : syracuseStep 3819293 = 1432235) (by norm_num)
theorem B7341893 : Blo 1695548 7341893 := bbase (se 4 (by rfl) ⟨688302, by rfl⟩ : syracuseStep 7341893 = 1376605) (by norm_num)
theorem B3819365 : Blo 1695548 3819365 := bbase (se 4 (by rfl) ⟨358065, by rfl⟩ : syracuseStep 3819365 = 716131) (by norm_num)
theorem B2148221 : Blo 1695548 2148221 := bbase (se 3 (by rfl) ⟨402791, by rfl⟩ : syracuseStep 2148221 = 805583) (by norm_num)
theorem B3819437 : Blo 1695548 3819437 := bbase (se 3 (by rfl) ⟨716144, by rfl⟩ : syracuseStep 3819437 = 1432289) (by norm_num)
theorem B2148277 : Blo 1695548 2148277 := bbase (se 5 (by rfl) ⟨100700, by rfl⟩ : syracuseStep 2148277 = 201401) (by norm_num)
theorem B15468533 : Blo 1695548 15468533 := bbase (se 5 (by rfl) ⟨725087, by rfl⟩ : syracuseStep 15468533 = 1450175) (by norm_num)
theorem B5801989 : Blo 1695548 5801989 := bbase (se 4 (by rfl) ⟨543936, by rfl⟩ : syracuseStep 5801989 = 1087873) (by norm_num)
theorem B2148373 : Blo 1695548 2148373 := bbase (se 6 (by rfl) ⟨50352, by rfl⟩ : syracuseStep 2148373 = 100705) (by norm_num)
theorem B6113333 : Blo 1695548 6113333 := bbase (se 5 (by rfl) ⟨286562, by rfl⟩ : syracuseStep 6113333 = 573125) (by norm_num)
theorem B4294741 : Blo 1695548 4294741 := bbase (se 8 (by rfl) ⟨25164, by rfl⟩ : syracuseStep 4294741 = 50329) (by norm_num)
theorem B3623005 : Blo 1695548 3623005 := bbase (se 3 (by rfl) ⟨679313, by rfl⟩ : syracuseStep 3623005 = 1358627) (by norm_num)
theorem B5728373 : Blo 1695548 5728373 := bbase (se 5 (by rfl) ⟨268517, by rfl⟩ : syracuseStep 5728373 = 537035) (by norm_num)
theorem B29386901 : Blo 1695548 29386901 := bbase (se 6 (by rfl) ⟨688755, by rfl⟩ : syracuseStep 29386901 = 1377511) (by norm_num)
theorem B4294853 : Blo 1695548 4294853 := bbase (se 4 (by rfl) ⟨402642, by rfl⟩ : syracuseStep 4294853 = 805285) (by norm_num)
theorem B3623125 : Blo 1695548 3623125 := bbase (se 7 (by rfl) ⟨42458, by rfl⟩ : syracuseStep 3623125 = 84917) (by norm_num)
theorem B2861365 : Blo 1695548 2861365 := bbase (se 5 (by rfl) ⟨134126, by rfl⟩ : syracuseStep 2861365 = 268253) (by norm_num)
theorem B3869005 : Blo 1695548 3869005 := bbase (se 3 (by rfl) ⟨725438, by rfl⟩ : syracuseStep 3869005 = 1450877) (by norm_num)
theorem B3221869 : Blo 1695548 3221869 := bbase (se 3 (by rfl) ⟨604100, by rfl⟩ : syracuseStep 3221869 = 1208201) (by norm_num)
theorem B4295045 : Blo 1695548 4295045 := bbase (se 4 (by rfl) ⟨402660, by rfl⟩ : syracuseStep 4295045 = 805321) (by norm_num)
theorem B2861453 : Blo 1695548 2861453 := bbase (se 3 (by rfl) ⟨536522, by rfl⟩ : syracuseStep 2861453 = 1073045) (by norm_num)
theorem B8702405 : Blo 1695548 8702405 := bbase (se 4 (by rfl) ⟨815850, by rfl⟩ : syracuseStep 8702405 = 1631701) (by norm_num)
theorem B3623381 : Blo 1695548 3623381 := bbase (se 7 (by rfl) ⟨42461, by rfl⟩ : syracuseStep 3623381 = 84923) (by norm_num)
theorem B2615765 : Blo 1695548 2615765 := bbase (se 7 (by rfl) ⟨30653, by rfl⟩ : syracuseStep 2615765 = 61307) (by norm_num)
theorem B3222013 : Blo 1695548 3222013 := bbase (se 3 (by rfl) ⟨604127, by rfl⟩ : syracuseStep 3222013 = 1208255) (by norm_num)
theorem B4073989 : Blo 1695548 4073989 := bbase (se 4 (by rfl) ⟨381936, by rfl⟩ : syracuseStep 4073989 = 763873) (by norm_num)
theorem B8587781 : Blo 1695548 8587781 := bbase (se 4 (by rfl) ⟨805104, by rfl⟩ : syracuseStep 8587781 = 1610209) (by norm_num)
theorem B2861581 : Blo 1695548 2861581 := bbase (se 3 (by rfl) ⟨536546, by rfl⟩ : syracuseStep 2861581 = 1073093) (by norm_num)
theorem B5728805 : Blo 1695548 5728805 := bbase (se 4 (by rfl) ⟨537075, by rfl⟩ : syracuseStep 5728805 = 1074151) (by norm_num)
theorem B4352557 : Blo 1695548 4352557 := bbase (se 3 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 4352557 = 1632209) (by norm_num)
theorem B28977749 : Blo 1695548 28977749 := bbase (se 8 (by rfl) ⟨169791, by rfl⟩ : syracuseStep 28977749 = 339583) (by norm_num)
theorem B2861669 : Blo 1695548 2861669 := bbase (se 4 (by rfl) ⟨268281, by rfl⟩ : syracuseStep 2861669 = 536563) (by norm_num)
theorem B3222173 : Blo 1695548 3222173 := bbase (se 3 (by rfl) ⟨604157, by rfl⟩ : syracuseStep 3222173 = 1208315) (by norm_num)
theorem B3058381 : Blo 1695548 3058381 := bbase (se 3 (by rfl) ⟨573446, by rfl⟩ : syracuseStep 3058381 = 1146893) (by norm_num)
theorem B4295389 : Blo 1695548 4295389 := bbase (se 3 (by rfl) ⟨805385, by rfl⟩ : syracuseStep 4295389 = 1610771) (by norm_num)
theorem B2861797 : Blo 1695548 2861797 := bbase (se 4 (by rfl) ⟨268293, by rfl⟩ : syracuseStep 2861797 = 536587) (by norm_num)
theorem B3058469 : Blo 1695548 3058469 := bbase (se 4 (by rfl) ⟨286731, by rfl⟩ : syracuseStep 3058469 = 573463) (by norm_num)
theorem B3222317 : Blo 1695548 3222317 := bbase (se 3 (by rfl) ⟨604184, by rfl⟩ : syracuseStep 3222317 = 1208369) (by norm_num)
theorem B2861885 : Blo 1695548 2861885 := bbase (se 3 (by rfl) ⟨536603, by rfl⟩ : syracuseStep 2861885 = 1073207) (by norm_num)
theorem B4295501 : Blo 1695548 4295501 := bbase (se 3 (by rfl) ⟨805406, by rfl⟩ : syracuseStep 4295501 = 1610813) (by norm_num)
theorem B3869525 : Blo 1695548 3869525 := bbase (se 9 (by rfl) ⟨11336, by rfl⟩ : syracuseStep 3869525 = 22673) (by norm_num)
theorem B9661301 : Blo 1695548 9661301 := bbase (se 5 (by rfl) ⟨452873, by rfl⟩ : syracuseStep 9661301 = 905747) (by norm_num)
theorem B3263365 : Blo 1695548 3263365 := bbase (se 4 (by rfl) ⟨305940, by rfl⟩ : syracuseStep 3263365 = 611881) (by norm_num)
theorem B3672973 : Blo 1695548 3672973 := bbase (se 3 (by rfl) ⟨688682, by rfl⟩ : syracuseStep 3672973 = 1377365) (by norm_num)
theorem B2862013 : Blo 1695548 2862013 := bbase (se 3 (by rfl) ⟨536627, by rfl⟩ : syracuseStep 2862013 = 1073255) (by norm_num)
theorem B8063957 : Blo 1695548 8063957 := bbase (se 7 (by rfl) ⟨94499, by rfl⟩ : syracuseStep 8063957 = 188999) (by norm_num)
theorem B4295693 : Blo 1695548 4295693 := bbase (se 3 (by rfl) ⟨805442, by rfl⟩ : syracuseStep 4295693 = 1610885) (by norm_num)
theorem B2862101 : Blo 1695548 2862101 := bbase (se 6 (by rfl) ⟨67080, by rfl⟩ : syracuseStep 2862101 = 134161) (by norm_num)
theorem B6442037 : Blo 1695548 6442037 := bbase (se 5 (by rfl) ⟨301970, by rfl⟩ : syracuseStep 6442037 = 603941) (by norm_num)
theorem B3222605 : Blo 1695548 3222605 := bbase (se 3 (by rfl) ⟨604238, by rfl⟩ : syracuseStep 3222605 = 1208477) (by norm_num)
theorem B12889205 : Blo 1695548 12889205 := bbase (se 5 (by rfl) ⟨604181, by rfl⟩ : syracuseStep 12889205 = 1208363) (by norm_num)
theorem B19319957 : Blo 1695548 19319957 := bbase (se 6 (by rfl) ⟨452811, by rfl⟩ : syracuseStep 19319957 = 905623) (by norm_num)
theorem B2862229 : Blo 1695548 2862229 := bbase (se 6 (by rfl) ⟨67083, by rfl⟩ : syracuseStep 2862229 = 134167) (by norm_num)
theorem B4828373 : Blo 1695548 4828373 := bbase (se 7 (by rfl) ⟨56582, by rfl⟩ : syracuseStep 4828373 = 113165) (by norm_num)
theorem B2862317 : Blo 1695548 2862317 := bbase (se 3 (by rfl) ⟨536684, by rfl⟩ : syracuseStep 2862317 = 1073369) (by norm_num)
theorem B3058973 : Blo 1695548 3058973 := bbase (se 3 (by rfl) ⟨573557, by rfl⟩ : syracuseStep 3058973 = 1147115) (by norm_num)
theorem B5434661 : Blo 1695548 5434661 := bbase (se 4 (by rfl) ⟨509499, by rfl⟩ : syracuseStep 5434661 = 1018999) (by norm_num)
theorem B3624269 : Blo 1695548 3624269 := bbase (se 3 (by rfl) ⟨679550, by rfl⟩ : syracuseStep 3624269 = 1359101) (by norm_num)
theorem B6442325 : Blo 1695548 6442325 := bbase (se 11 (by rfl) ⟨4718, by rfl⟩ : syracuseStep 6442325 = 9437) (by norm_num)
theorem B4296037 : Blo 1695548 4296037 := bbase (se 4 (by rfl) ⟨402753, by rfl⟩ : syracuseStep 4296037 = 805507) (by norm_num)
theorem B2862445 : Blo 1695548 2862445 := bbase (se 3 (by rfl) ⟨536708, by rfl⟩ : syracuseStep 2862445 = 1073417) (by norm_num)
theorem B2862533 : Blo 1695548 2862533 := bbase (se 4 (by rfl) ⟨268362, by rfl⟩ : syracuseStep 2862533 = 536725) (by norm_num)
theorem B4132309 : Blo 1695548 4132309 := bbase (se 7 (by rfl) ⟨48425, by rfl⟩ : syracuseStep 4132309 = 96851) (by norm_num)
theorem B4296149 : Blo 1695548 4296149 := bbase (se 7 (by rfl) ⟨50345, by rfl⟩ : syracuseStep 4296149 = 100691) (by norm_num)
theorem B12881429 : Blo 1695548 12881429 := bbase (se 6 (by rfl) ⟨301908, by rfl⟩ : syracuseStep 12881429 = 603817) (by norm_num)
theorem B3624509 : Blo 1695548 3624509 := bbase (se 3 (by rfl) ⟨679595, by rfl⟩ : syracuseStep 3624509 = 1359191) (by norm_num)
theorem B2862661 : Blo 1695548 2862661 := bbase (se 4 (by rfl) ⟨268374, by rfl⟩ : syracuseStep 2862661 = 536749) (by norm_num)
theorem B4828805 : Blo 1695548 4828805 := bbase (se 4 (by rfl) ⟨452700, by rfl⟩ : syracuseStep 4828805 = 905401) (by norm_num)
theorem B4296341 : Blo 1695548 4296341 := bbase (se 6 (by rfl) ⟨100695, by rfl⟩ : syracuseStep 4296341 = 201391) (by norm_num)
theorem B2862749 : Blo 1695548 2862749 := bbase (se 3 (by rfl) ⟨536765, by rfl⟩ : syracuseStep 2862749 = 1073531) (by norm_num)
theorem B2543333 : Blo 1695548 2543333 := bbase (se 4 (by rfl) ⟨238437, by rfl⟩ : syracuseStep 2543333 = 476875) (by norm_num)
theorem B2543357 : Blo 1695548 2543357 := bbase (se 3 (by rfl) ⟨476879, by rfl⟩ : syracuseStep 2543357 = 953759) (by norm_num)
theorem B2543381 : Blo 1695548 2543381 := bbase (se 6 (by rfl) ⟨59610, by rfl⟩ : syracuseStep 2543381 = 119221) (by norm_num)
theorem B8589077 : Blo 1695548 8589077 := bbase (se 6 (by rfl) ⟨201306, by rfl⟩ : syracuseStep 8589077 = 402613) (by norm_num)
theorem B2862877 : Blo 1695548 2862877 := bbase (se 3 (by rfl) ⟨536789, by rfl⟩ : syracuseStep 2862877 = 1073579) (by norm_num)
theorem B2543405 : Blo 1695548 2543405 := bbase (se 3 (by rfl) ⟨476888, by rfl⟩ : syracuseStep 2543405 = 953777) (by norm_num)
theorem B5508917 : Blo 1695548 5508917 := bbase (se 5 (by rfl) ⟨258230, by rfl⟩ : syracuseStep 5508917 = 516461) (by norm_num)
theorem B2543429 : Blo 1695548 2543429 := bbase (se 4 (by rfl) ⟨238446, by rfl⟩ : syracuseStep 2543429 = 476893) (by norm_num)
theorem B2543453 : Blo 1695548 2543453 := bbase (se 3 (by rfl) ⟨476897, by rfl⟩ : syracuseStep 2543453 = 953795) (by norm_num)
theorem B4075373 : Blo 1695548 4075373 := bbase (se 3 (by rfl) ⟨764132, by rfl⟩ : syracuseStep 4075373 = 1528265) (by norm_num)
theorem B2543477 : Blo 1695548 2543477 := bbase (se 5 (by rfl) ⟨119225, by rfl⟩ : syracuseStep 2543477 = 238451) (by norm_num)
theorem B4075381 : Blo 1695548 4075381 := bbase (se 5 (by rfl) ⟨191033, by rfl⟩ : syracuseStep 4075381 = 382067) (by norm_num)
theorem B2862965 : Blo 1695548 2862965 := bbase (se 5 (by rfl) ⟨134201, by rfl⟩ : syracuseStep 2862965 = 268403) (by norm_num)
theorem B2543501 : Blo 1695548 2543501 := bbase (se 3 (by rfl) ⟨476906, by rfl⟩ : syracuseStep 2543501 = 953813) (by norm_num)
theorem B2543525 : Blo 1695548 2543525 := bbase (se 4 (by rfl) ⟨238455, by rfl⟩ : syracuseStep 2543525 = 476911) (by norm_num)
theorem B2543549 : Blo 1695548 2543549 := bbase (se 3 (by rfl) ⟨476915, by rfl⟩ : syracuseStep 2543549 = 953831) (by norm_num)
theorem B2543573 : Blo 1695548 2543573 := bbase (se 7 (by rfl) ⟨29807, by rfl⟩ : syracuseStep 2543573 = 59615) (by norm_num)
theorem B2543597 : Blo 1695548 2543597 := bbase (se 3 (by rfl) ⟨476924, by rfl⟩ : syracuseStep 2543597 = 953849) (by norm_num)
theorem B4296685 : Blo 1695548 4296685 := bbase (se 3 (by rfl) ⟨805628, by rfl⟩ : syracuseStep 4296685 = 1611257) (by norm_num)
theorem B2863093 : Blo 1695548 2863093 := bbase (se 5 (by rfl) ⟨134207, by rfl⟩ : syracuseStep 2863093 = 268415) (by norm_num)
theorem B2543621 : Blo 1695548 2543621 := bbase (se 4 (by rfl) ⟨238464, by rfl⟩ : syracuseStep 2543621 = 476929) (by norm_num)
theorem B2543645 : Blo 1695548 2543645 := bbase (se 3 (by rfl) ⟨476933, by rfl⟩ : syracuseStep 2543645 = 953867) (by norm_num)
theorem B2543669 : Blo 1695548 2543669 := bbase (se 5 (by rfl) ⟨119234, by rfl⟩ : syracuseStep 2543669 = 238469) (by norm_num)
theorem B3625013 : Blo 1695548 3625013 := bbase (se 5 (by rfl) ⟨169922, by rfl⟩ : syracuseStep 3625013 = 339845) (by norm_num)
theorem B3625021 : Blo 1695548 3625021 := bbase (se 3 (by rfl) ⟨679691, by rfl⟩ : syracuseStep 3625021 = 1359383) (by norm_num)
theorem B2543693 : Blo 1695548 2543693 := bbase (se 3 (by rfl) ⟨476942, by rfl⟩ : syracuseStep 2543693 = 953885) (by norm_num)
theorem B2863181 : Blo 1695548 2863181 := bbase (se 3 (by rfl) ⟨536846, by rfl⟩ : syracuseStep 2863181 = 1073693) (by norm_num)
theorem B4296797 : Blo 1695548 4296797 := bbase (se 3 (by rfl) ⟨805649, by rfl⟩ : syracuseStep 4296797 = 1611299) (by norm_num)
theorem B2543717 : Blo 1695548 2543717 := bbase (se 4 (by rfl) ⟨238473, by rfl⟩ : syracuseStep 2543717 = 476947) (by norm_num)
theorem B2543741 : Blo 1695548 2543741 := bbase (se 3 (by rfl) ⟨476951, by rfl⟩ : syracuseStep 2543741 = 953903) (by norm_num)
theorem B2543765 : Blo 1695548 2543765 := bbase (se 6 (by rfl) ⟨59619, by rfl⟩ : syracuseStep 2543765 = 119239) (by norm_num)
theorem B2543789 : Blo 1695548 2543789 := bbase (se 3 (by rfl) ⟨476960, by rfl⟩ : syracuseStep 2543789 = 953921) (by norm_num)
theorem B2543813 : Blo 1695548 2543813 := bbase (se 4 (by rfl) ⟨238482, by rfl⟩ : syracuseStep 2543813 = 476965) (by norm_num)
theorem B2863309 : Blo 1695548 2863309 := bbase (se 3 (by rfl) ⟨536870, by rfl⟩ : syracuseStep 2863309 = 1073741) (by norm_num)
theorem B2543837 : Blo 1695548 2543837 := bbase (se 3 (by rfl) ⟨476969, by rfl⟩ : syracuseStep 2543837 = 953939) (by norm_num)
theorem B2543861 : Blo 1695548 2543861 := bbase (se 5 (by rfl) ⟨119243, by rfl⟩ : syracuseStep 2543861 = 238487) (by norm_num)
theorem B2543885 : Blo 1695548 2543885 := bbase (se 3 (by rfl) ⟨476978, by rfl⟩ : syracuseStep 2543885 = 953957) (by norm_num)
theorem B2543909 : Blo 1695548 2543909 := bbase (se 4 (by rfl) ⟨238491, by rfl⟩ : syracuseStep 2543909 = 476983) (by norm_num)
theorem B2863397 : Blo 1695548 2863397 := bbase (se 4 (by rfl) ⟨268443, by rfl⟩ : syracuseStep 2863397 = 536887) (by norm_num)
theorem B2543933 : Blo 1695548 2543933 := bbase (se 3 (by rfl) ⟨476987, by rfl⟩ : syracuseStep 2543933 = 953975) (by norm_num)
theorem B2543957 : Blo 1695548 2543957 := bbase (se 10 (by rfl) ⟨3726, by rfl⟩ : syracuseStep 2543957 = 7453) (by norm_num)
theorem B2543981 : Blo 1695548 2543981 := bbase (se 3 (by rfl) ⟨476996, by rfl⟩ : syracuseStep 2543981 = 953993) (by norm_num)
theorem B4829557 : Blo 1695548 4829557 := bbase (se 5 (by rfl) ⟨226385, by rfl⟩ : syracuseStep 4829557 = 452771) (by norm_num)
theorem B2544005 : Blo 1695548 2544005 := bbase (se 4 (by rfl) ⟨238500, by rfl⟩ : syracuseStep 2544005 = 477001) (by norm_num)
theorem B2544029 : Blo 1695548 2544029 := bbase (se 3 (by rfl) ⟨477005, by rfl⟩ : syracuseStep 2544029 = 954011) (by norm_num)
theorem B2863525 : Blo 1695548 2863525 := bbase (se 4 (by rfl) ⟨268455, by rfl⟩ : syracuseStep 2863525 = 536911) (by norm_num)
theorem B4354469 : Blo 1695548 4354469 := bbase (se 4 (by rfl) ⟨408231, by rfl⟩ : syracuseStep 4354469 = 816463) (by norm_num)
theorem B2544053 : Blo 1695548 2544053 := bbase (se 5 (by rfl) ⟨119252, by rfl⟩ : syracuseStep 2544053 = 238505) (by norm_num)
theorem B2544077 : Blo 1695548 2544077 := bbase (se 3 (by rfl) ⟨477014, by rfl⟩ : syracuseStep 2544077 = 954029) (by norm_num)
theorem B2544101 : Blo 1695548 2544101 := bbase (se 4 (by rfl) ⟨238509, by rfl⟩ : syracuseStep 2544101 = 477019) (by norm_num)
theorem B6443509 : Blo 1695548 6443509 := bbase (se 5 (by rfl) ⟨302039, by rfl⟩ : syracuseStep 6443509 = 604079) (by norm_num)
theorem B2544125 : Blo 1695548 2544125 := bbase (se 3 (by rfl) ⟨477023, by rfl⟩ : syracuseStep 2544125 = 954047) (by norm_num)
theorem B2863613 : Blo 1695548 2863613 := bbase (se 3 (by rfl) ⟨536927, by rfl⟩ : syracuseStep 2863613 = 1073855) (by norm_num)
theorem B2544149 : Blo 1695548 2544149 := bbase (se 6 (by rfl) ⟨59628, by rfl⟩ : syracuseStep 2544149 = 119257) (by norm_num)
theorem B2544173 : Blo 1695548 2544173 := bbase (se 3 (by rfl) ⟨477032, by rfl⟩ : syracuseStep 2544173 = 954065) (by norm_num)
theorem B2716229 : Blo 1695548 2716229 := bbase (se 4 (by rfl) ⟨254646, by rfl⟩ : syracuseStep 2716229 = 509293) (by norm_num)
theorem B2544197 : Blo 1695548 2544197 := bbase (se 4 (by rfl) ⟨238518, by rfl⟩ : syracuseStep 2544197 = 477037) (by norm_num)
theorem B7246421 : Blo 1695548 7246421 := bbase (se 8 (by rfl) ⟨42459, by rfl⟩ : syracuseStep 7246421 = 84919) (by norm_num)
theorem B2544221 : Blo 1695548 2544221 := bbase (se 3 (by rfl) ⟨477041, by rfl⟩ : syracuseStep 2544221 = 954083) (by norm_num)
theorem B2544245 : Blo 1695548 2544245 := bbase (se 5 (by rfl) ⟨119261, by rfl⟩ : syracuseStep 2544245 = 238523) (by norm_num)
theorem B2863741 : Blo 1695548 2863741 := bbase (se 3 (by rfl) ⟨536951, by rfl⟩ : syracuseStep 2863741 = 1073903) (by norm_num)
theorem B5722757 : Blo 1695548 5722757 := bbase (se 4 (by rfl) ⟨536508, by rfl⟩ : syracuseStep 5722757 = 1073017) (by norm_num)
theorem B3265157 : Blo 1695548 3265157 := bbase (se 4 (by rfl) ⟨306108, by rfl⟩ : syracuseStep 3265157 = 612217) (by norm_num)
theorem B2544269 : Blo 1695548 2544269 := bbase (se 3 (by rfl) ⟨477050, by rfl⟩ : syracuseStep 2544269 = 954101) (by norm_num)
theorem B11604629 : Blo 1695548 11604629 := bbase (se 6 (by rfl) ⟨271983, by rfl⟩ : syracuseStep 11604629 = 543967) (by norm_num)
theorem B2544293 : Blo 1695548 2544293 := bbase (se 4 (by rfl) ⟨238527, by rfl⟩ : syracuseStep 2544293 = 477055) (by norm_num)
theorem B5436085 : Blo 1695548 5436085 := bbase (se 5 (by rfl) ⟨254816, by rfl⟩ : syracuseStep 5436085 = 509633) (by norm_num)
theorem B2544317 : Blo 1695548 2544317 := bbase (se 3 (by rfl) ⟨477059, by rfl⟩ : syracuseStep 2544317 = 954119) (by norm_num)
theorem B2716357 : Blo 1695548 2716357 := bbase (se 4 (by rfl) ⟨254658, by rfl⟩ : syracuseStep 2716357 = 509317) (by norm_num)
theorem B2544341 : Blo 1695548 2544341 := bbase (se 7 (by rfl) ⟨29816, by rfl⟩ : syracuseStep 2544341 = 59633) (by norm_num)
theorem B2863829 : Blo 1695548 2863829 := bbase (se 7 (by rfl) ⟨33560, by rfl⟩ : syracuseStep 2863829 = 67121) (by norm_num)
theorem B2544365 : Blo 1695548 2544365 := bbase (se 3 (by rfl) ⟨477068, by rfl⟩ : syracuseStep 2544365 = 954137) (by norm_num)
theorem B2716421 : Blo 1695548 2716421 := bbase (se 4 (by rfl) ⟨254664, by rfl⟩ : syracuseStep 2716421 = 509329) (by norm_num)
theorem B2544389 : Blo 1695548 2544389 := bbase (se 4 (by rfl) ⟨238536, by rfl⟩ : syracuseStep 2544389 = 477073) (by norm_num)
theorem B2544413 : Blo 1695548 2544413 := bbase (se 3 (by rfl) ⟨477077, by rfl⟩ : syracuseStep 2544413 = 954155) (by norm_num)
theorem B6443813 : Blo 1695548 6443813 := bbase (se 4 (by rfl) ⟨604107, by rfl⟩ : syracuseStep 6443813 = 1208215) (by norm_num)
theorem B2544437 : Blo 1695548 2544437 := bbase (se 5 (by rfl) ⟨119270, by rfl⟩ : syracuseStep 2544437 = 238541) (by norm_num)
theorem B2544461 : Blo 1695548 2544461 := bbase (se 3 (by rfl) ⟨477086, by rfl⟩ : syracuseStep 2544461 = 954173) (by norm_num)
theorem B2863957 : Blo 1695548 2863957 := bbase (se 9 (by rfl) ⟨8390, by rfl⟩ : syracuseStep 2863957 = 16781) (by norm_num)
theorem B3674965 : Blo 1695548 3674965 := bbase (se 9 (by rfl) ⟨10766, by rfl⟩ : syracuseStep 3674965 = 21533) (by norm_num)
theorem B4076381 : Blo 1695548 4076381 := bbase (se 3 (by rfl) ⟨764321, by rfl⟩ : syracuseStep 4076381 = 1528643) (by norm_num)
theorem B2544485 : Blo 1695548 2544485 := bbase (se 4 (by rfl) ⟨238545, by rfl⟩ : syracuseStep 2544485 = 477091) (by norm_num)
theorem B4412269 : Blo 1695548 4412269 := bbase (se 3 (by rfl) ⟨827300, by rfl⟩ : syracuseStep 4412269 = 1654601) (by norm_num)
theorem B2544509 : Blo 1695548 2544509 := bbase (se 3 (by rfl) ⟨477095, by rfl⟩ : syracuseStep 2544509 = 954191) (by norm_num)
theorem B2544533 : Blo 1695548 2544533 := bbase (se 6 (by rfl) ⟨59637, by rfl⟩ : syracuseStep 2544533 = 119275) (by norm_num)
theorem B2544557 : Blo 1695548 2544557 := bbase (se 3 (by rfl) ⟨477104, by rfl⟩ : syracuseStep 2544557 = 954209) (by norm_num)
theorem B2864045 : Blo 1695548 2864045 := bbase (se 3 (by rfl) ⟨537008, by rfl⟩ : syracuseStep 2864045 = 1074017) (by norm_num)
theorem B3314621 : Blo 1695548 3314621 := bbase (se 3 (by rfl) ⟨621491, by rfl⟩ : syracuseStep 3314621 = 1242983) (by norm_num)
theorem B2544581 : Blo 1695548 2544581 := bbase (se 4 (by rfl) ⟨238554, by rfl⟩ : syracuseStep 2544581 = 477109) (by norm_num)
theorem B2544605 : Blo 1695548 2544605 := bbase (se 3 (by rfl) ⟨477113, by rfl⟩ : syracuseStep 2544605 = 954227) (by norm_num)
theorem B2544629 : Blo 1695548 2544629 := bbase (se 5 (by rfl) ⟨119279, by rfl⟩ : syracuseStep 2544629 = 238559) (by norm_num)
theorem B13063157 : Blo 1695548 13063157 := bbase (se 5 (by rfl) ⟨612335, by rfl⟩ : syracuseStep 13063157 = 1224671) (by norm_num)
theorem B2544653 : Blo 1695548 2544653 := bbase (se 3 (by rfl) ⟨477122, by rfl⟩ : syracuseStep 2544653 = 954245) (by norm_num)
theorem B2544677 : Blo 1695548 2544677 := bbase (se 4 (by rfl) ⟨238563, by rfl⟩ : syracuseStep 2544677 = 477127) (by norm_num)
theorem B8590373 : Blo 1695548 8590373 := bbase (se 4 (by rfl) ⟨805347, by rfl⟩ : syracuseStep 8590373 = 1610695) (by norm_num)
theorem B2864173 : Blo 1695548 2864173 := bbase (se 3 (by rfl) ⟨537032, by rfl⟩ : syracuseStep 2864173 = 1074065) (by norm_num)
theorem B5723189 : Blo 1695548 5723189 := bbase (se 5 (by rfl) ⟨268274, by rfl⟩ : syracuseStep 5723189 = 536549) (by norm_num)
theorem B2544701 : Blo 1695548 2544701 := bbase (se 3 (by rfl) ⟨477131, by rfl⟩ : syracuseStep 2544701 = 954263) (by norm_num)
theorem B2544725 : Blo 1695548 2544725 := bbase (se 8 (by rfl) ⟨14910, by rfl⟩ : syracuseStep 2544725 = 29821) (by norm_num)
theorem B2544749 : Blo 1695548 2544749 := bbase (se 3 (by rfl) ⟨477140, by rfl⟩ : syracuseStep 2544749 = 954281) (by norm_num)
theorem B5436533 : Blo 1695548 5436533 := bbase (se 5 (by rfl) ⟨254837, by rfl⟩ : syracuseStep 5436533 = 509675) (by norm_num)
theorem B2544773 : Blo 1695548 2544773 := bbase (se 4 (by rfl) ⟨238572, by rfl⟩ : syracuseStep 2544773 = 477145) (by norm_num)
theorem B2864261 : Blo 1695548 2864261 := bbase (se 4 (by rfl) ⟨268524, by rfl⟩ : syracuseStep 2864261 = 537049) (by norm_num)
theorem B2544797 : Blo 1695548 2544797 := bbase (se 3 (by rfl) ⟨477149, by rfl⟩ : syracuseStep 2544797 = 954299) (by norm_num)
theorem B2544821 : Blo 1695548 2544821 := bbase (se 5 (by rfl) ⟨119288, by rfl⟩ : syracuseStep 2544821 = 238577) (by norm_num)
theorem B2544845 : Blo 1695548 2544845 := bbase (se 3 (by rfl) ⟨477158, by rfl⟩ : syracuseStep 2544845 = 954317) (by norm_num)
theorem B2544869 : Blo 1695548 2544869 := bbase (se 4 (by rfl) ⟨238581, by rfl⟩ : syracuseStep 2544869 = 477163) (by norm_num)
theorem B2544893 : Blo 1695548 2544893 := bbase (se 3 (by rfl) ⟨477167, by rfl⟩ : syracuseStep 2544893 = 954335) (by norm_num)
theorem B2864389 : Blo 1695548 2864389 := bbase (se 4 (by rfl) ⟨268536, by rfl⟩ : syracuseStep 2864389 = 537073) (by norm_num)
theorem B2544917 : Blo 1695548 2544917 := bbase (se 6 (by rfl) ⟨59646, by rfl⟩ : syracuseStep 2544917 = 119293) (by norm_num)
theorem B2037037 : Blo 1695548 2037037 := bbase (se 3 (by rfl) ⟨381944, by rfl⟩ : syracuseStep 2037037 = 763889) (by norm_num)
theorem B2544941 : Blo 1695548 2544941 := bbase (se 3 (by rfl) ⟨477176, by rfl⟩ : syracuseStep 2544941 = 954353) (by norm_num)
theorem B2544965 : Blo 1695548 2544965 := bbase (se 4 (by rfl) ⟨238590, by rfl⟩ : syracuseStep 2544965 = 477181) (by norm_num)
theorem B2544989 : Blo 1695548 2544989 := bbase (se 3 (by rfl) ⟨477185, by rfl⟩ : syracuseStep 2544989 = 954371) (by norm_num)
theorem B2864477 : Blo 1695548 2864477 := bbase (se 3 (by rfl) ⟨537089, by rfl⟩ : syracuseStep 2864477 = 1074179) (by norm_num)
theorem B2545013 : Blo 1695548 2545013 := bbase (se 5 (by rfl) ⟨119297, by rfl⟩ : syracuseStep 2545013 = 238595) (by norm_num)
theorem B2545037 : Blo 1695548 2545037 := bbase (se 3 (by rfl) ⟨477194, by rfl⟩ : syracuseStep 2545037 = 954389) (by norm_num)
theorem B2545061 : Blo 1695548 2545061 := bbase (se 4 (by rfl) ⟨238599, by rfl⟩ : syracuseStep 2545061 = 477199) (by norm_num)
theorem B2545085 : Blo 1695548 2545085 := bbase (se 3 (by rfl) ⟨477203, by rfl⟩ : syracuseStep 2545085 = 954407) (by norm_num)
theorem B2545109 : Blo 1695548 2545109 := bbase (se 7 (by rfl) ⟨29825, by rfl⟩ : syracuseStep 2545109 = 59651) (by norm_num)
theorem B2864605 : Blo 1695548 2864605 := bbase (se 3 (by rfl) ⟨537113, by rfl⟩ : syracuseStep 2864605 = 1074227) (by norm_num)
theorem B5723621 : Blo 1695548 5723621 := bbase (se 4 (by rfl) ⟨536589, by rfl⟩ : syracuseStep 5723621 = 1073179) (by norm_num)
theorem B8156645 : Blo 1695548 8156645 := bbase (se 4 (by rfl) ⟨764685, by rfl⟩ : syracuseStep 8156645 = 1529371) (by norm_num)
theorem B2545133 : Blo 1695548 2545133 := bbase (se 3 (by rfl) ⟨477212, by rfl⟩ : syracuseStep 2545133 = 954425) (by norm_num)
theorem B2545157 : Blo 1695548 2545157 := bbase (se 4 (by rfl) ⟨238608, by rfl⟩ : syracuseStep 2545157 = 477217) (by norm_num)
theorem B5805589 : Blo 1695548 5805589 := bbase (se 6 (by rfl) ⟨136068, by rfl⟩ : syracuseStep 5805589 = 272137) (by norm_num)
theorem B2545181 : Blo 1695548 2545181 := bbase (se 3 (by rfl) ⟨477221, by rfl⟩ : syracuseStep 2545181 = 954443) (by norm_num)
theorem B2545205 : Blo 1695548 2545205 := bbase (se 5 (by rfl) ⟨119306, by rfl⟩ : syracuseStep 2545205 = 238613) (by norm_num)
theorem B2545229 : Blo 1695548 2545229 := bbase (se 3 (by rfl) ⟨477230, by rfl⟩ : syracuseStep 2545229 = 954461) (by norm_num)
theorem B4077149 : Blo 1695548 4077149 := bbase (se 3 (by rfl) ⟨764465, by rfl⟩ : syracuseStep 4077149 = 1528931) (by norm_num)
theorem B6968933 : Blo 1695548 6968933 := bbase (se 4 (by rfl) ⟨653337, by rfl⟩ : syracuseStep 6968933 = 1306675) (by norm_num)
theorem B2545253 : Blo 1695548 2545253 := bbase (se 4 (by rfl) ⟨238617, by rfl⟩ : syracuseStep 2545253 = 477235) (by norm_num)
theorem B2545277 : Blo 1695548 2545277 := bbase (se 3 (by rfl) ⟨477239, by rfl⟩ : syracuseStep 2545277 = 954479) (by norm_num)
theorem B3815045 : Blo 1695548 3815045 := bbase (se 4 (by rfl) ⟨357660, by rfl⟩ : syracuseStep 3815045 = 715321) (by norm_num)
theorem B2545301 : Blo 1695548 2545301 := bbase (se 6 (by rfl) ⟨59655, by rfl⟩ : syracuseStep 2545301 = 119311) (by norm_num)
theorem B2545325 : Blo 1695548 2545325 := bbase (se 3 (by rfl) ⟨477248, by rfl⟩ : syracuseStep 2545325 = 954497) (by norm_num)
theorem B2545349 : Blo 1695548 2545349 := bbase (se 4 (by rfl) ⟨238626, by rfl⟩ : syracuseStep 2545349 = 477253) (by norm_num)
theorem B3815117 : Blo 1695548 3815117 := bbase (se 3 (by rfl) ⟨715334, by rfl⟩ : syracuseStep 3815117 = 1430669) (by norm_num)
theorem B2545373 : Blo 1695548 2545373 := bbase (se 3 (by rfl) ⟨477257, by rfl⟩ : syracuseStep 2545373 = 954515) (by norm_num)
theorem B2545397 : Blo 1695548 2545397 := bbase (se 5 (by rfl) ⟨119315, by rfl⟩ : syracuseStep 2545397 = 238631) (by norm_num)
theorem B2545421 : Blo 1695548 2545421 := bbase (se 3 (by rfl) ⟨477266, by rfl⟩ : syracuseStep 2545421 = 954533) (by norm_num)
theorem B3815189 : Blo 1695548 3815189 := bbase (se 6 (by rfl) ⟨89418, by rfl⟩ : syracuseStep 3815189 = 178837) (by norm_num)
theorem B2545445 : Blo 1695548 2545445 := bbase (se 4 (by rfl) ⟨238635, by rfl⟩ : syracuseStep 2545445 = 477271) (by norm_num)
theorem B2545469 : Blo 1695548 2545469 := bbase (se 3 (by rfl) ⟨477275, by rfl⟩ : syracuseStep 2545469 = 954551) (by norm_num)
theorem B2545493 : Blo 1695548 2545493 := bbase (se 9 (by rfl) ⟨7457, by rfl⟩ : syracuseStep 2545493 = 14915) (by norm_num)
theorem B3815261 : Blo 1695548 3815261 := bbase (se 3 (by rfl) ⟨715361, by rfl⟩ : syracuseStep 3815261 = 1430723) (by norm_num)
theorem B2791277 : Blo 1695548 2791277 := bbase (se 3 (by rfl) ⟨523364, by rfl⟩ : syracuseStep 2791277 = 1046729) (by norm_num)
theorem B2545517 : Blo 1695548 2545517 := bbase (se 3 (by rfl) ⟨477284, by rfl⟩ : syracuseStep 2545517 = 954569) (by norm_num)
theorem B2291581 : Blo 1695548 2291581 := bbase (se 3 (by rfl) ⟨429671, by rfl⟩ : syracuseStep 2291581 = 859343) (by norm_num)
theorem B2545541 : Blo 1695548 2545541 := bbase (se 4 (by rfl) ⟨238644, by rfl⟩ : syracuseStep 2545541 = 477289) (by norm_num)
theorem B5724053 : Blo 1695548 5724053 := bbase (se 6 (by rfl) ⟨134157, by rfl⟩ : syracuseStep 5724053 = 268315) (by norm_num)
theorem B2545565 : Blo 1695548 2545565 := bbase (se 3 (by rfl) ⟨477293, by rfl⟩ : syracuseStep 2545565 = 954587) (by norm_num)
theorem B3815333 : Blo 1695548 3815333 := bbase (se 4 (by rfl) ⟨357687, by rfl⟩ : syracuseStep 3815333 = 715375) (by norm_num)
theorem B8148917 : Blo 1695548 8148917 := bbase (se 5 (by rfl) ⟨381980, by rfl⟩ : syracuseStep 8148917 = 763961) (by norm_num)
theorem B2545589 : Blo 1695548 2545589 := bbase (se 5 (by rfl) ⟨119324, by rfl⟩ : syracuseStep 2545589 = 238649) (by norm_num)
theorem B2545613 : Blo 1695548 2545613 := bbase (se 3 (by rfl) ⟨477302, by rfl⟩ : syracuseStep 2545613 = 954605) (by norm_num)
theorem B12228565 : Blo 1695548 12228565 := bbase (se 7 (by rfl) ⟨143303, by rfl⟩ : syracuseStep 12228565 = 286607) (by norm_num)
theorem B5806037 : Blo 1695548 5806037 := bbase (se 7 (by rfl) ⟨68039, by rfl⟩ : syracuseStep 5806037 = 136079) (by norm_num)
theorem B2545637 : Blo 1695548 2545637 := bbase (se 4 (by rfl) ⟨238653, by rfl⟩ : syracuseStep 2545637 = 477307) (by norm_num)
theorem B3815405 : Blo 1695548 3815405 := bbase (se 3 (by rfl) ⟨715388, by rfl⟩ : syracuseStep 3815405 = 1430777) (by norm_num)
theorem B2545661 : Blo 1695548 2545661 := bbase (se 3 (by rfl) ⟨477311, by rfl⟩ : syracuseStep 2545661 = 954623) (by norm_num)
theorem B2545685 : Blo 1695548 2545685 := bbase (se 6 (by rfl) ⟨59664, by rfl⟩ : syracuseStep 2545685 = 119329) (by norm_num)
theorem B2717741 : Blo 1695548 2717741 := bbase (se 3 (by rfl) ⟨509576, by rfl⟩ : syracuseStep 2717741 = 1019153) (by norm_num)
theorem B2545709 : Blo 1695548 2545709 := bbase (se 3 (by rfl) ⟨477320, by rfl⟩ : syracuseStep 2545709 = 954641) (by norm_num)
theorem B3815477 : Blo 1695548 3815477 := bbase (se 5 (by rfl) ⟨178850, by rfl⟩ : syracuseStep 3815477 = 357701) (by norm_num)
theorem B2545733 : Blo 1695548 2545733 := bbase (se 4 (by rfl) ⟨238662, by rfl⟩ : syracuseStep 2545733 = 477325) (by norm_num)
theorem B2545757 : Blo 1695548 2545757 := bbase (se 3 (by rfl) ⟨477329, by rfl⟩ : syracuseStep 2545757 = 954659) (by norm_num)
theorem B3922021 : Blo 1695548 3922021 := bbase (se 4 (by rfl) ⟨367689, by rfl⟩ : syracuseStep 3922021 = 735379) (by norm_num)
theorem B2545781 : Blo 1695548 2545781 := bbase (se 5 (by rfl) ⟨119333, by rfl⟩ : syracuseStep 2545781 = 238667) (by norm_num)
theorem B3815549 : Blo 1695548 3815549 := bbase (se 3 (by rfl) ⟨715415, by rfl⟩ : syracuseStep 3815549 = 1430831) (by norm_num)
theorem B2545805 : Blo 1695548 2545805 := bbase (se 3 (by rfl) ⟨477338, by rfl⟩ : syracuseStep 2545805 = 954677) (by norm_num)
theorem B2037917 : Blo 1695548 2037917 := bbase (se 3 (by rfl) ⟨382109, by rfl⟩ : syracuseStep 2037917 = 764219) (by norm_num)
theorem B2545829 : Blo 1695548 2545829 := bbase (se 4 (by rfl) ⟨238671, by rfl⟩ : syracuseStep 2545829 = 477343) (by norm_num)
theorem B2717869 : Blo 1695548 2717869 := bbase (se 3 (by rfl) ⟨509600, by rfl⟩ : syracuseStep 2717869 = 1019201) (by norm_num)
theorem B2545853 : Blo 1695548 2545853 := bbase (se 3 (by rfl) ⟨477347, by rfl⟩ : syracuseStep 2545853 = 954695) (by norm_num)
theorem B3815621 : Blo 1695548 3815621 := bbase (se 4 (by rfl) ⟨357714, by rfl⟩ : syracuseStep 3815621 = 715429) (by norm_num)
theorem B3438797 : Blo 1695548 3438797 := bbase (se 3 (by rfl) ⟨644774, by rfl⟩ : syracuseStep 3438797 = 1289549) (by norm_num)
theorem B2545877 : Blo 1695548 2545877 := bbase (se 7 (by rfl) ⟨29834, by rfl⟩ : syracuseStep 2545877 = 59669) (by norm_num)
theorem B2545901 : Blo 1695548 2545901 := bbase (se 3 (by rfl) ⟨477356, by rfl⟩ : syracuseStep 2545901 = 954713) (by norm_num)
theorem B2545925 : Blo 1695548 2545925 := bbase (se 4 (by rfl) ⟨238680, by rfl⟩ : syracuseStep 2545925 = 477361) (by norm_num)
theorem B3815693 : Blo 1695548 3815693 := bbase (se 3 (by rfl) ⟨715442, by rfl⟩ : syracuseStep 3815693 = 1430885) (by norm_num)
theorem B6199573 : Blo 1695548 6199573 := bbase (se 6 (by rfl) ⟨145302, by rfl⟩ : syracuseStep 6199573 = 290605) (by norm_num)
theorem B2545949 : Blo 1695548 2545949 := bbase (se 3 (by rfl) ⟨477365, by rfl⟩ : syracuseStep 2545949 = 954731) (by norm_num)
theorem B2292013 : Blo 1695548 2292013 := bbase (se 3 (by rfl) ⟨429752, by rfl⟩ : syracuseStep 2292013 = 859505) (by norm_num)
theorem B8591669 : Blo 1695548 8591669 := bbase (se 5 (by rfl) ⟨402734, by rfl⟩ : syracuseStep 8591669 = 805469) (by norm_num)
theorem B2545973 : Blo 1695548 2545973 := bbase (se 5 (by rfl) ⟨119342, by rfl⟩ : syracuseStep 2545973 = 238685) (by norm_num)
theorem B5724485 : Blo 1695548 5724485 := bbase (se 4 (by rfl) ⟨536670, by rfl⟩ : syracuseStep 5724485 = 1073341) (by norm_num)
theorem B7248197 : Blo 1695548 7248197 := bbase (se 4 (by rfl) ⟨679518, by rfl⟩ : syracuseStep 7248197 = 1359037) (by norm_num)
theorem B2545997 : Blo 1695548 2545997 := bbase (se 3 (by rfl) ⟨477374, by rfl⟩ : syracuseStep 2545997 = 954749) (by norm_num)
theorem B3815765 : Blo 1695548 3815765 := bbase (se 10 (by rfl) ⟨5589, by rfl⟩ : syracuseStep 3815765 = 11179) (by norm_num)
theorem B2546021 : Blo 1695548 2546021 := bbase (se 4 (by rfl) ⟨238689, by rfl⟩ : syracuseStep 2546021 = 477379) (by norm_num)
theorem B2546045 : Blo 1695548 2546045 := bbase (se 3 (by rfl) ⟨477383, by rfl⟩ : syracuseStep 2546045 = 954767) (by norm_num)
theorem B2546069 : Blo 1695548 2546069 := bbase (se 6 (by rfl) ⟨59673, by rfl⟩ : syracuseStep 2546069 = 119347) (by norm_num)
theorem B3815837 : Blo 1695548 3815837 := bbase (se 3 (by rfl) ⟨715469, by rfl⟩ : syracuseStep 3815837 = 1430939) (by norm_num)
theorem B2546093 : Blo 1695548 2546093 := bbase (se 3 (by rfl) ⟨477392, by rfl⟩ : syracuseStep 2546093 = 954785) (by norm_num)
theorem B2546117 : Blo 1695548 2546117 := bbase (se 4 (by rfl) ⟨238698, by rfl⟩ : syracuseStep 2546117 = 477397) (by norm_num)
theorem B2038225 : Blo 1695548 2038225 := bbase (se 2 (by rfl) ⟨764334, by rfl⟩ : syracuseStep 2038225 = 1528669) (by norm_num)
theorem B2292181 : Blo 1695548 2292181 := bbase (se 7 (by rfl) ⟨26861, by rfl⟩ : syracuseStep 2292181 = 53723) (by norm_num)
theorem B2546141 : Blo 1695548 2546141 := bbase (se 3 (by rfl) ⟨477401, by rfl⟩ : syracuseStep 2546141 = 954803) (by norm_num)
theorem B3815909 : Blo 1695548 3815909 := bbase (se 4 (by rfl) ⟨357741, by rfl⟩ : syracuseStep 3815909 = 715483) (by norm_num)
theorem B2546165 : Blo 1695548 2546165 := bbase (se 5 (by rfl) ⟨119351, by rfl⟩ : syracuseStep 2546165 = 238703) (by norm_num)
theorem B2415109 : Blo 1695548 2415109 := bbase (se 4 (by rfl) ⟨226416, by rfl⟩ : syracuseStep 2415109 = 452833) (by norm_num)
theorem B2546189 : Blo 1695548 2546189 := bbase (se 3 (by rfl) ⟨477410, by rfl⟩ : syracuseStep 2546189 = 954821) (by norm_num)
theorem B2546213 : Blo 1695548 2546213 := bbase (se 4 (by rfl) ⟨238707, by rfl⟩ : syracuseStep 2546213 = 477415) (by norm_num)
theorem B3815981 : Blo 1695548 3815981 := bbase (se 3 (by rfl) ⟨715496, by rfl⟩ : syracuseStep 3815981 = 1430993) (by norm_num)
theorem B7248437 : Blo 1695548 7248437 := bbase (se 5 (by rfl) ⟨339770, by rfl⟩ : syracuseStep 7248437 = 679541) (by norm_num)
theorem B2546237 : Blo 1695548 2546237 := bbase (se 3 (by rfl) ⟨477419, by rfl⟩ : syracuseStep 2546237 = 954839) (by norm_num)
theorem B2546261 : Blo 1695548 2546261 := bbase (se 8 (by rfl) ⟨14919, by rfl⟩ : syracuseStep 2546261 = 29839) (by norm_num)
theorem B2546285 : Blo 1695548 2546285 := bbase (se 3 (by rfl) ⟨477428, by rfl⟩ : syracuseStep 2546285 = 954857) (by norm_num)
theorem B3816053 : Blo 1695548 3816053 := bbase (se 5 (by rfl) ⟨178877, by rfl⟩ : syracuseStep 3816053 = 357755) (by norm_num)
theorem B2546309 : Blo 1695548 2546309 := bbase (se 4 (by rfl) ⟨238716, by rfl⟩ : syracuseStep 2546309 = 477433) (by norm_num)
theorem B1718929 : Blo 1695548 1718929 := bbase (se 2 (by rfl) ⟨644598, by rfl⟩ : syracuseStep 1718929 = 1289197) (by norm_num)
theorem B3816125 : Blo 1695548 3816125 := bbase (se 3 (by rfl) ⟨715523, by rfl⟩ : syracuseStep 3816125 = 1431047) (by norm_num)
theorem B8583893 : Blo 1695548 8583893 := bbase (se 7 (by rfl) ⟨100592, by rfl⟩ : syracuseStep 8583893 = 201185) (by norm_num)
theorem B2292445 : Blo 1695548 2292445 := bbase (se 3 (by rfl) ⟨429833, by rfl⟩ : syracuseStep 2292445 = 859667) (by norm_num)
theorem B5724917 : Blo 1695548 5724917 := bbase (se 5 (by rfl) ⟨268355, by rfl⟩ : syracuseStep 5724917 = 536711) (by norm_num)
theorem B3816197 : Blo 1695548 3816197 := bbase (se 4 (by rfl) ⟨357768, by rfl⟩ : syracuseStep 3816197 = 715537) (by norm_num)
theorem B1907509 : Blo 1695548 1907509 := bbase (se 5 (by rfl) ⟨89414, by rfl⟩ : syracuseStep 1907509 = 178829) (by norm_num)
theorem B3816269 : Blo 1695548 3816269 := bbase (se 3 (by rfl) ⟨715550, by rfl⟩ : syracuseStep 3816269 = 1431101) (by norm_num)
theorem B2038609 : Blo 1695548 2038609 := bbase (se 2 (by rfl) ⟨764478, by rfl⟩ : syracuseStep 2038609 = 1528957) (by norm_num)
theorem B2038613 : Blo 1695548 2038613 := bbase (se 9 (by rfl) ⟨5972, by rfl⟩ : syracuseStep 2038613 = 11945) (by norm_num)
theorem B1907545 : Blo 1695548 1907545 := bbase (se 2 (by rfl) ⟨715329, by rfl⟩ : syracuseStep 1907545 = 1430659) (by norm_num)
theorem B1907581 : Blo 1695548 1907581 := bbase (se 3 (by rfl) ⟨357671, by rfl⟩ : syracuseStep 1907581 = 715343) (by norm_num)
theorem B3816341 : Blo 1695548 3816341 := bbase (se 6 (by rfl) ⟨89445, by rfl⟩ : syracuseStep 3816341 = 178891) (by norm_num)
theorem B1907617 : Blo 1695548 1907617 := bbase (se 2 (by rfl) ⟨715356, by rfl⟩ : syracuseStep 1907617 = 1430713) (by norm_num)
theorem B4414397 : Blo 1695548 4414397 := bbase (se 3 (by rfl) ⟨827699, by rfl⟩ : syracuseStep 4414397 = 1655399) (by norm_num)
theorem B1907653 : Blo 1695548 1907653 := bbase (se 4 (by rfl) ⟨178842, by rfl⟩ : syracuseStep 1907653 = 357685) (by norm_num)
theorem B2718677 : Blo 1695548 2718677 := bbase (se 7 (by rfl) ⟨31859, by rfl⟩ : syracuseStep 2718677 = 63719) (by norm_num)
theorem B3816413 : Blo 1695548 3816413 := bbase (se 3 (by rfl) ⟨715577, by rfl⟩ : syracuseStep 3816413 = 1431155) (by norm_num)
theorem B1907689 : Blo 1695548 1907689 := bbase (se 2 (by rfl) ⟨715383, by rfl⟩ : syracuseStep 1907689 = 1430767) (by norm_num)
theorem B1907725 : Blo 1695548 1907725 := bbase (se 3 (by rfl) ⟨357698, by rfl⟩ : syracuseStep 1907725 = 715397) (by norm_num)
theorem B3816485 : Blo 1695548 3816485 := bbase (se 4 (by rfl) ⟨357795, by rfl⟩ : syracuseStep 3816485 = 715591) (by norm_num)
theorem B1907761 : Blo 1695548 1907761 := bbase (se 2 (by rfl) ⟨715410, by rfl⟩ : syracuseStep 1907761 = 1430821) (by norm_num)
theorem B1907797 : Blo 1695548 1907797 := bbase (se 8 (by rfl) ⟨11178, by rfl⟩ : syracuseStep 1907797 = 22357) (by norm_num)
theorem B2415701 : Blo 1695548 2415701 := bbase (se 8 (by rfl) ⟨14154, by rfl⟩ : syracuseStep 2415701 = 28309) (by norm_num)
theorem B3816557 : Blo 1695548 3816557 := bbase (se 3 (by rfl) ⟨715604, by rfl⟩ : syracuseStep 3816557 = 1431209) (by norm_num)
theorem B1907833 : Blo 1695548 1907833 := bbase (se 2 (by rfl) ⟨715437, by rfl⟩ : syracuseStep 1907833 = 1430875) (by norm_num)
theorem B6200453 : Blo 1695548 6200453 := bbase (se 4 (by rfl) ⟨581292, by rfl⟩ : syracuseStep 6200453 = 1162585) (by norm_num)
theorem B4586645 : Blo 1695548 4586645 := bbase (se 6 (by rfl) ⟨107499, by rfl⟩ : syracuseStep 4586645 = 214999) (by norm_num)
theorem B4832405 : Blo 1695548 4832405 := bbase (se 6 (by rfl) ⟨113259, by rfl⟩ : syracuseStep 4832405 = 226519) (by norm_num)
theorem B1907869 : Blo 1695548 1907869 := bbase (se 3 (by rfl) ⟨357725, by rfl⟩ : syracuseStep 1907869 = 715451) (by norm_num)
theorem B5725349 : Blo 1695548 5725349 := bbase (se 4 (by rfl) ⟨536751, by rfl⟩ : syracuseStep 5725349 = 1073503) (by norm_num)
theorem B2415781 : Blo 1695548 2415781 := bbase (se 4 (by rfl) ⟨226479, by rfl⟩ : syracuseStep 2415781 = 452959) (by norm_num)
theorem B3816629 : Blo 1695548 3816629 := bbase (se 5 (by rfl) ⟨178904, by rfl⟩ : syracuseStep 3816629 = 357809) (by norm_num)
theorem B1907905 : Blo 1695548 1907905 := bbase (se 2 (by rfl) ⟨715464, by rfl⟩ : syracuseStep 1907905 = 1430929) (by norm_num)
theorem B1907941 : Blo 1695548 1907941 := bbase (se 4 (by rfl) ⟨178869, by rfl⟩ : syracuseStep 1907941 = 357739) (by norm_num)
theorem B2039017 : Blo 1695548 2039017 := bbase (se 2 (by rfl) ⟨764631, by rfl⟩ : syracuseStep 2039017 = 1529263) (by norm_num)
theorem B2718965 : Blo 1695548 2718965 := bbase (se 5 (by rfl) ⟨127451, by rfl⟩ : syracuseStep 2718965 = 254903) (by norm_num)
theorem B3816701 : Blo 1695548 3816701 := bbase (se 3 (by rfl) ⟨715631, by rfl⟩ : syracuseStep 3816701 = 1431263) (by norm_num)
theorem B6438149 : Blo 1695548 6438149 := bbase (se 4 (by rfl) ⟨603576, by rfl⟩ : syracuseStep 6438149 = 1207153) (by norm_num)
theorem B1907977 : Blo 1695548 1907977 := bbase (se 2 (by rfl) ⟨715491, by rfl⟩ : syracuseStep 1907977 = 1430983) (by norm_num)
theorem B2415901 : Blo 1695548 2415901 := bbase (se 3 (by rfl) ⟨452981, by rfl⟩ : syracuseStep 2415901 = 905963) (by norm_num)
theorem B1908013 : Blo 1695548 1908013 := bbase (se 3 (by rfl) ⟨357752, by rfl⟩ : syracuseStep 1908013 = 715505) (by norm_num)
theorem B2235701 : Blo 1695548 2235701 := bbase (se 5 (by rfl) ⟨104798, by rfl⟩ : syracuseStep 2235701 = 209597) (by norm_num)
theorem B8150341 : Blo 1695548 8150341 := bbase (se 4 (by rfl) ⟨764094, by rfl⟩ : syracuseStep 8150341 = 1528189) (by norm_num)
theorem B3816773 : Blo 1695548 3816773 := bbase (se 4 (by rfl) ⟨357822, by rfl⟩ : syracuseStep 3816773 = 715645) (by norm_num)
theorem B1908049 : Blo 1695548 1908049 := bbase (se 2 (by rfl) ⟨715518, by rfl⟩ : syracuseStep 1908049 = 1431037) (by norm_num)
theorem B41278805 : Blo 1695548 41278805 := bbase (se 11 (by rfl) ⟨30233, by rfl⟩ : syracuseStep 41278805 = 60467) (by norm_num)
theorem B1908085 : Blo 1695548 1908085 := bbase (se 5 (by rfl) ⟨89441, by rfl⟩ : syracuseStep 1908085 = 178883) (by norm_num)
theorem B2415997 : Blo 1695548 2415997 := bbase (se 3 (by rfl) ⟨452999, by rfl⟩ : syracuseStep 2415997 = 905999) (by norm_num)
theorem B3816845 : Blo 1695548 3816845 := bbase (se 3 (by rfl) ⟨715658, by rfl⟩ : syracuseStep 3816845 = 1431317) (by norm_num)
theorem B1908121 : Blo 1695548 1908121 := bbase (se 2 (by rfl) ⟨715545, by rfl⟩ : syracuseStep 1908121 = 1431091) (by norm_num)
theorem B1908157 : Blo 1695548 1908157 := bbase (se 3 (by rfl) ⟨357779, by rfl⟩ : syracuseStep 1908157 = 715559) (by norm_num)
theorem B6880709 : Blo 1695548 6880709 := bbase (se 4 (by rfl) ⟨645066, by rfl⟩ : syracuseStep 6880709 = 1290133) (by norm_num)
theorem B3816917 : Blo 1695548 3816917 := bbase (se 7 (by rfl) ⟨44729, by rfl⟩ : syracuseStep 3816917 = 89459) (by norm_num)
theorem B1908193 : Blo 1695548 1908193 := bbase (se 2 (by rfl) ⟨715572, by rfl⟩ : syracuseStep 1908193 = 1431145) (by norm_num)
theorem B1908229 : Blo 1695548 1908229 := bbase (se 4 (by rfl) ⟨178896, by rfl⟩ : syracuseStep 1908229 = 357793) (by norm_num)
theorem B3816989 : Blo 1695548 3816989 := bbase (se 3 (by rfl) ⟨715685, by rfl⟩ : syracuseStep 3816989 = 1431371) (by norm_num)
theorem B6438437 : Blo 1695548 6438437 := bbase (se 4 (by rfl) ⟨603603, by rfl⟩ : syracuseStep 6438437 = 1207207) (by norm_num)
theorem B1908265 : Blo 1695548 1908265 := bbase (se 2 (by rfl) ⟨715599, by rfl⟩ : syracuseStep 1908265 = 1431199) (by norm_num)
theorem B4292149 : Blo 1695548 4292149 := bbase (se 5 (by rfl) ⟨201194, by rfl⟩ : syracuseStep 4292149 = 402389) (by norm_num)
theorem B8592965 : Blo 1695548 8592965 := bbase (se 4 (by rfl) ⟨805590, by rfl⟩ : syracuseStep 8592965 = 1611181) (by norm_num)
theorem B1908301 : Blo 1695548 1908301 := bbase (se 3 (by rfl) ⟨357806, by rfl⟩ : syracuseStep 1908301 = 715613) (by norm_num)
theorem B5725781 : Blo 1695548 5725781 := bbase (se 8 (by rfl) ⟨33549, by rfl⟩ : syracuseStep 5725781 = 67099) (by norm_num)
theorem B3817061 : Blo 1695548 3817061 := bbase (se 4 (by rfl) ⟨357849, by rfl⟩ : syracuseStep 3817061 = 715699) (by norm_num)
theorem B1908337 : Blo 1695548 1908337 := bbase (se 2 (by rfl) ⟨715626, by rfl⟩ : syracuseStep 1908337 = 1431253) (by norm_num)
theorem B1908373 : Blo 1695548 1908373 := bbase (se 6 (by rfl) ⟨44727, by rfl⟩ : syracuseStep 1908373 = 89455) (by norm_num)
theorem B2145953 : Blo 1695548 2145953 := bbase (se 2 (by rfl) ⟨804732, by rfl⟩ : syracuseStep 2145953 = 1609465) (by norm_num)
theorem B4292261 : Blo 1695548 4292261 := bbase (se 4 (by rfl) ⟨402399, by rfl⟩ : syracuseStep 4292261 = 804799) (by norm_num)
theorem B3817133 : Blo 1695548 3817133 := bbase (se 3 (by rfl) ⟨715712, by rfl⟩ : syracuseStep 3817133 = 1431425) (by norm_num)
theorem B1908409 : Blo 1695548 1908409 := bbase (se 2 (by rfl) ⟨715653, by rfl⟩ : syracuseStep 1908409 = 1431307) (by norm_num)
theorem B2146009 : Blo 1695548 2146009 := bbase (se 2 (by rfl) ⟨804753, by rfl⟩ : syracuseStep 2146009 = 1609507) (by norm_num)
theorem B1908445 : Blo 1695548 1908445 := bbase (se 3 (by rfl) ⟨357833, by rfl⟩ : syracuseStep 1908445 = 715667) (by norm_num)
theorem B3219173 : Blo 1695548 3219173 := bbase (se 4 (by rfl) ⟨301797, by rfl⟩ : syracuseStep 3219173 = 603595) (by norm_num)
theorem B3817205 : Blo 1695548 3817205 := bbase (se 5 (by rfl) ⟨178931, by rfl⟩ : syracuseStep 3817205 = 357863) (by norm_num)
theorem B1908481 : Blo 1695548 1908481 := bbase (se 2 (by rfl) ⟨715680, by rfl⟩ : syracuseStep 1908481 = 1431361) (by norm_num)
theorem B1908517 : Blo 1695548 1908517 := bbase (se 4 (by rfl) ⟨178923, by rfl⟩ : syracuseStep 1908517 = 357847) (by norm_num)
theorem B2146105 : Blo 1695548 2146105 := bbase (se 2 (by rfl) ⟨804789, by rfl⟩ : syracuseStep 2146105 = 1609579) (by norm_num)
theorem B3817277 : Blo 1695548 3817277 := bbase (se 3 (by rfl) ⟨715739, by rfl⟩ : syracuseStep 3817277 = 1431479) (by norm_num)
theorem B1908553 : Blo 1695548 1908553 := bbase (se 2 (by rfl) ⟨715707, by rfl⟩ : syracuseStep 1908553 = 1431415) (by norm_num)
theorem B3923797 : Blo 1695548 3923797 := bbase (se 9 (by rfl) ⟨11495, by rfl⟩ : syracuseStep 3923797 = 22991) (by norm_num)
theorem B4292453 : Blo 1695548 4292453 := bbase (se 4 (by rfl) ⟨402417, by rfl⟩ : syracuseStep 4292453 = 804835) (by norm_num)
theorem B3440485 : Blo 1695548 3440485 := bbase (se 4 (by rfl) ⟨322545, by rfl⟩ : syracuseStep 3440485 = 645091) (by norm_num)
theorem B1908589 : Blo 1695548 1908589 := bbase (se 3 (by rfl) ⟨357860, by rfl⟩ : syracuseStep 1908589 = 715721) (by norm_num)
theorem B2416493 : Blo 1695548 2416493 := bbase (se 3 (by rfl) ⟨453092, by rfl⟩ : syracuseStep 2416493 = 906185) (by norm_num)
theorem B3817349 : Blo 1695548 3817349 := bbase (se 4 (by rfl) ⟨357876, by rfl⟩ : syracuseStep 3817349 = 715753) (by norm_num)
theorem B1908625 : Blo 1695548 1908625 := bbase (se 2 (by rfl) ⟨715734, by rfl⟩ : syracuseStep 1908625 = 1431469) (by norm_num)
theorem B1908661 : Blo 1695548 1908661 := bbase (se 5 (by rfl) ⟨89468, by rfl⟩ : syracuseStep 1908661 = 178937) (by norm_num)
theorem B3817421 : Blo 1695548 3817421 := bbase (se 3 (by rfl) ⟨715766, by rfl⟩ : syracuseStep 3817421 = 1431533) (by norm_num)
theorem B1908697 : Blo 1695548 1908697 := bbase (se 2 (by rfl) ⟨715761, by rfl⟩ : syracuseStep 1908697 = 1431523) (by norm_num)
theorem B2146277 : Blo 1695548 2146277 := bbase (se 4 (by rfl) ⟨201213, by rfl⟩ : syracuseStep 2146277 = 402427) (by norm_num)
theorem B8585189 : Blo 1695548 8585189 := bbase (se 4 (by rfl) ⟨804861, by rfl⟩ : syracuseStep 8585189 = 1609723) (by norm_num)
theorem B1908733 : Blo 1695548 1908733 := bbase (se 3 (by rfl) ⟨357887, by rfl⟩ : syracuseStep 1908733 = 715775) (by norm_num)
theorem B1695747 : Blo 1695548 1695747 := bstep (se 1 (by rfl) ⟨1271810, by rfl⟩ : syracuseStep 1695747 = 2543621) B2543621
theorem B3817475 : Blo 1695548 3817475 := bstep (se 1 (by rfl) ⟨2863106, by rfl⟩ : syracuseStep 3817475 = 5726213) B5726213
theorem B1695763 : Blo 1695548 1695763 := bstep (se 1 (by rfl) ⟨1271822, by rfl⟩ : syracuseStep 1695763 = 2543645) B2543645
theorem B1695779 : Blo 1695548 1695779 := bstep (se 1 (by rfl) ⟨1271834, by rfl⟩ : syracuseStep 1695779 = 2543669) B2543669
theorem B1695795 : Blo 1695548 1695795 := bstep (se 1 (by rfl) ⟨1271846, by rfl⟩ : syracuseStep 1695795 = 2543693) B2543693
theorem B1908787 : Blo 1695548 1908787 := bstep (se 1 (by rfl) ⟨1431590, by rfl⟩ : syracuseStep 1908787 = 2863181) B2863181
theorem B1695811 : Blo 1695548 1695811 := bstep (se 1 (by rfl) ⟨1271858, by rfl⟩ : syracuseStep 1695811 = 2543717) B2543717
theorem B4833361 : Blo 1695548 4833361 := bstep (se 2 (by rfl) ⟨1812510, by rfl⟩ : syracuseStep 4833361 = 3625021) B3625021
theorem B1695827 : Blo 1695548 1695827 := bstep (se 1 (by rfl) ⟨1271870, by rfl⟩ : syracuseStep 1695827 = 2543741) B2543741
theorem B1695843 : Blo 1695548 1695843 := bstep (se 1 (by rfl) ⟨1271882, by rfl⟩ : syracuseStep 1695843 = 2543765) B2543765
theorem B5726321 : Blo 1695548 5726321 := bstep (se 2 (by rfl) ⟨2147370, by rfl⟩ : syracuseStep 5726321 = 4294741) B4294741
theorem B1695859 : Blo 1695548 1695859 := bstep (se 1 (by rfl) ⟨1271894, by rfl⟩ : syracuseStep 1695859 = 2543789) B2543789
theorem B1695875 : Blo 1695548 1695875 := bstep (se 1 (by rfl) ⟨1271906, by rfl⟩ : syracuseStep 1695875 = 2543813) B2543813
theorem B9666701 : Blo 1695548 9666701 := bstep (se 3 (by rfl) ⟨1812506, by rfl⟩ : syracuseStep 9666701 = 3625013) B3625013
theorem B1695891 : Blo 1695548 1695891 := bstep (se 1 (by rfl) ⟨1271918, by rfl⟩ : syracuseStep 1695891 = 2543837) B2543837
theorem B1695907 : Blo 1695548 1695907 := bstep (se 1 (by rfl) ⟨1271930, by rfl⟩ : syracuseStep 1695907 = 2543861) B2543861
theorem B1695923 : Blo 1695548 1695923 := bstep (se 1 (by rfl) ⟨1271942, by rfl⟩ : syracuseStep 1695923 = 2543885) B2543885
theorem B1695939 : Blo 1695548 1695939 := bstep (se 1 (by rfl) ⟨1271954, by rfl⟩ : syracuseStep 1695939 = 2543909) B2543909
theorem B1908931 : Blo 1695548 1908931 := bstep (se 1 (by rfl) ⟨1431698, by rfl⟩ : syracuseStep 1908931 = 2863397) B2863397
theorem B8593613 : Blo 1695548 8593613 := bstep (se 3 (by rfl) ⟨1611302, by rfl⟩ : syracuseStep 8593613 = 3222605) B3222605
theorem B1695955 : Blo 1695548 1695955 := bstep (se 1 (by rfl) ⟨1271966, by rfl⟩ : syracuseStep 1695955 = 2543933) B2543933
theorem B1720531 : Blo 1695548 1720531 := bstep (se 1 (by rfl) ⟨1290398, by rfl⟩ : syracuseStep 1720531 = 2580797) B2580797
theorem B1695971 : Blo 1695548 1695971 := bstep (se 1 (by rfl) ⟨1271978, by rfl⟩ : syracuseStep 1695971 = 2543957) B2543957
theorem B1695987 : Blo 1695548 1695987 := bstep (se 1 (by rfl) ⟨1271990, by rfl⟩ : syracuseStep 1695987 = 2543981) B2543981
theorem B1696003 : Blo 1695548 1696003 := bstep (se 1 (by rfl) ⟨1272002, by rfl⟩ : syracuseStep 1696003 = 2544005) B2544005
theorem B3817745 : Blo 1695548 3817745 := bstep (se 2 (by rfl) ⟨1431654, by rfl⟩ : syracuseStep 3817745 = 2863309) B2863309
theorem B1696019 : Blo 1695548 1696019 := bstep (se 1 (by rfl) ⟨1272014, by rfl⟩ : syracuseStep 1696019 = 2544029) B2544029
theorem B1696035 : Blo 1695548 1696035 := bstep (se 1 (by rfl) ⟨1272026, by rfl⟩ : syracuseStep 1696035 = 2544053) B2544053
theorem B3817763 : Blo 1695548 3817763 := bstep (se 1 (by rfl) ⟨2863322, by rfl⟩ : syracuseStep 3817763 = 5726645) B5726645
theorem B1696051 : Blo 1695548 1696051 := bstep (se 1 (by rfl) ⟨1272038, by rfl⟩ : syracuseStep 1696051 = 2544077) B2544077
theorem B1696067 : Blo 1695548 1696067 := bstep (se 1 (by rfl) ⟨1272050, by rfl⟩ : syracuseStep 1696067 = 2544101) B2544101
theorem B1696083 : Blo 1695548 1696083 := bstep (se 1 (by rfl) ⟨1272062, by rfl⟩ : syracuseStep 1696083 = 2544125) B2544125
theorem B1909075 : Blo 1695548 1909075 := bstep (se 1 (by rfl) ⟨1431806, by rfl⟩ : syracuseStep 1909075 = 2863613) B2863613
theorem B1696099 : Blo 1695548 1696099 := bstep (se 1 (by rfl) ⟨1272074, by rfl⟩ : syracuseStep 1696099 = 2544149) B2544149
theorem B8266097 : Blo 1695548 8266097 := bstep (se 2 (by rfl) ⟨3099786, by rfl⟩ : syracuseStep 8266097 = 6199573) B6199573
theorem B1696115 : Blo 1695548 1696115 := bstep (se 1 (by rfl) ⟨1272086, by rfl⟩ : syracuseStep 1696115 = 2544173) B2544173
theorem B1810819 : Blo 1695548 1810819 := bstep (se 1 (by rfl) ⟨1358114, by rfl⟩ : syracuseStep 1810819 = 2716229) B2716229
theorem B1696131 : Blo 1695548 1696131 := bstep (se 1 (by rfl) ⟨1272098, by rfl⟩ : syracuseStep 1696131 = 2544197) B2544197
theorem B3056017 : Blo 1695548 3056017 := bstep (se 2 (by rfl) ⟨1146006, by rfl⟩ : syracuseStep 3056017 = 2292013) B2292013
theorem B1696147 : Blo 1695548 1696147 := bstep (se 1 (by rfl) ⟨1272110, by rfl⟩ : syracuseStep 1696147 = 2544221) B2544221
theorem B1696163 : Blo 1695548 1696163 := bstep (se 1 (by rfl) ⟨1272122, by rfl⟩ : syracuseStep 1696163 = 2544245) B2544245
theorem B1696179 : Blo 1695548 1696179 := bstep (se 1 (by rfl) ⟨1272134, by rfl⟩ : syracuseStep 1696179 = 2544269) B2544269
theorem B1696195 : Blo 1695548 1696195 := bstep (se 1 (by rfl) ⟨1272146, by rfl⟩ : syracuseStep 1696195 = 2544293) B2544293
theorem B1696211 : Blo 1695548 1696211 := bstep (se 1 (by rfl) ⟨1272158, by rfl⟩ : syracuseStep 1696211 = 2544317) B2544317
theorem B1696227 : Blo 1695548 1696227 := bstep (se 1 (by rfl) ⟨1272170, by rfl⟩ : syracuseStep 1696227 = 2544341) B2544341
theorem B1909219 : Blo 1695548 1909219 := bstep (se 1 (by rfl) ⟨1431914, by rfl⟩ : syracuseStep 1909219 = 2863829) B2863829
theorem B6439409 : Blo 1695548 6439409 := bstep (se 2 (by rfl) ⟨2414778, by rfl⟩ : syracuseStep 6439409 = 4829557) B4829557
theorem B1696243 : Blo 1695548 1696243 := bstep (se 1 (by rfl) ⟨1272182, by rfl⟩ : syracuseStep 1696243 = 2544365) B2544365
theorem B2146819 : Blo 1695548 2146819 := bstep (se 1 (by rfl) ⟨1610114, by rfl⟩ : syracuseStep 2146819 = 3220229) B3220229
theorem B1696259 : Blo 1695548 1696259 := bstep (se 1 (by rfl) ⟨1272194, by rfl⟩ : syracuseStep 1696259 = 2544389) B2544389
theorem B9658885 : Blo 1695548 9658885 := bstep (se 4 (by rfl) ⟨905520, by rfl⟩ : syracuseStep 9658885 = 1811041) B1811041
theorem B1696275 : Blo 1695548 1696275 := bstep (se 1 (by rfl) ⟨1272206, by rfl⟩ : syracuseStep 1696275 = 2544413) B2544413
theorem B1696291 : Blo 1695548 1696291 := bstep (se 1 (by rfl) ⟨1272218, by rfl⟩ : syracuseStep 1696291 = 2544437) B2544437
theorem B3818033 : Blo 1695548 3818033 := bstep (se 2 (by rfl) ⟨1431762, by rfl⟩ : syracuseStep 3818033 = 2863525) B2863525
theorem B1696307 : Blo 1695548 1696307 := bstep (se 1 (by rfl) ⟨1272230, by rfl⟩ : syracuseStep 1696307 = 2544461) B2544461
theorem B1696323 : Blo 1695548 1696323 := bstep (se 1 (by rfl) ⟨1272242, by rfl⟩ : syracuseStep 1696323 = 2544485) B2544485
theorem B3818051 : Blo 1695548 3818051 := bstep (se 1 (by rfl) ⟨2863538, by rfl⟩ : syracuseStep 3818051 = 5727077) B5727077
theorem B1696339 : Blo 1695548 1696339 := bstep (se 1 (by rfl) ⟨1272254, by rfl⟩ : syracuseStep 1696339 = 2544509) B2544509
theorem B2146915 : Blo 1695548 2146915 := bstep (se 1 (by rfl) ⟨1610186, by rfl⟩ : syracuseStep 2146915 = 3220373) B3220373
theorem B1696355 : Blo 1695548 1696355 := bstep (se 1 (by rfl) ⟨1272266, by rfl⟩ : syracuseStep 1696355 = 2544533) B2544533
theorem B4293233 : Blo 1695548 4293233 := bstep (se 2 (by rfl) ⟨1609962, by rfl⟩ : syracuseStep 4293233 = 3219925) B3219925
theorem B1696371 : Blo 1695548 1696371 := bstep (se 1 (by rfl) ⟨1272278, by rfl⟩ : syracuseStep 1696371 = 2544557) B2544557
theorem B1909363 : Blo 1695548 1909363 := bstep (se 1 (by rfl) ⟨1432022, by rfl⟩ : syracuseStep 1909363 = 2864045) B2864045
theorem B1696387 : Blo 1695548 1696387 := bstep (se 1 (by rfl) ⟨1272290, by rfl⟩ : syracuseStep 1696387 = 2544581) B2544581
theorem B5726861 : Blo 1695548 5726861 := bstep (se 3 (by rfl) ⟨1073786, by rfl⟩ : syracuseStep 5726861 = 2147573) B2147573
theorem B7250573 : Blo 1695548 7250573 := bstep (se 3 (by rfl) ⟨1359482, by rfl⟩ : syracuseStep 7250573 = 2718965) B2718965
theorem B1696403 : Blo 1695548 1696403 := bstep (se 1 (by rfl) ⟨1272302, by rfl⟩ : syracuseStep 1696403 = 2544605) B2544605
theorem B4293283 : Blo 1695548 4293283 := bstep (se 1 (by rfl) ⟨3219962, by rfl⟩ : syracuseStep 4293283 = 6439925) B6439925
theorem B1696419 : Blo 1695548 1696419 := bstep (se 1 (by rfl) ⟨1272314, by rfl⟩ : syracuseStep 1696419 = 2544629) B2544629
theorem B8708771 : Blo 1695548 8708771 := bstep (se 1 (by rfl) ⟨6531578, by rfl⟩ : syracuseStep 8708771 = 13063157) B13063157
theorem B5431985 : Blo 1695548 5431985 := bstep (se 2 (by rfl) ⟨2036994, by rfl⟩ : syracuseStep 5431985 = 4073989) B4073989
theorem B3220145 : Blo 1695548 3220145 := bstep (se 2 (by rfl) ⟨1207554, by rfl⟩ : syracuseStep 3220145 = 2415109) B2415109
theorem B1696435 : Blo 1695548 1696435 := bstep (se 1 (by rfl) ⟨1272326, by rfl⟩ : syracuseStep 1696435 = 2544653) B2544653
theorem B1696451 : Blo 1695548 1696451 := bstep (se 1 (by rfl) ⟨1272338, by rfl⟩ : syracuseStep 1696451 = 2544677) B2544677
theorem B5726915 : Blo 1695548 5726915 := bstep (se 1 (by rfl) ⟨4295186, by rfl⟩ : syracuseStep 5726915 = 8590373) B8590373
theorem B3441361 : Blo 1695548 3441361 := bstep (se 2 (by rfl) ⟨1290510, by rfl⟩ : syracuseStep 3441361 = 2581021) B2581021
theorem B1696467 : Blo 1695548 1696467 := bstep (se 1 (by rfl) ⟨1272350, by rfl⟩ : syracuseStep 1696467 = 2544701) B2544701
theorem B1696483 : Blo 1695548 1696483 := bstep (se 1 (by rfl) ⟨1272362, by rfl⟩ : syracuseStep 1696483 = 2544725) B2544725
theorem B5161699 : Blo 1695548 5161699 := bstep (se 1 (by rfl) ⟨3871274, by rfl⟩ : syracuseStep 5161699 = 7742549) B7742549
theorem B1696499 : Blo 1695548 1696499 := bstep (se 1 (by rfl) ⟨1272374, by rfl⟩ : syracuseStep 1696499 = 2544749) B2544749
theorem B1696515 : Blo 1695548 1696515 := bstep (se 1 (by rfl) ⟨1272386, by rfl⟩ : syracuseStep 1696515 = 2544773) B2544773
theorem B1909507 : Blo 1695548 1909507 := bstep (se 1 (by rfl) ⟨1432130, by rfl⟩ : syracuseStep 1909507 = 2864261) B2864261
theorem B14492429 : Blo 1695548 14492429 := bstep (se 3 (by rfl) ⟨2717330, by rfl⟩ : syracuseStep 14492429 = 5434661) B5434661
theorem B1696531 : Blo 1695548 1696531 := bstep (se 1 (by rfl) ⟨1272398, by rfl⟩ : syracuseStep 1696531 = 2544797) B2544797
theorem B1696547 : Blo 1695548 1696547 := bstep (se 1 (by rfl) ⟨1272410, by rfl⟩ : syracuseStep 1696547 = 2544821) B2544821
theorem B4293425 : Blo 1695548 4293425 := bstep (se 2 (by rfl) ⟨1610034, by rfl⟩ : syracuseStep 4293425 = 3220069) B3220069
theorem B1696563 : Blo 1695548 1696563 := bstep (se 1 (by rfl) ⟨1272422, by rfl⟩ : syracuseStep 1696563 = 2544845) B2544845
theorem B1696579 : Blo 1695548 1696579 := bstep (se 1 (by rfl) ⟨1272434, by rfl⟩ : syracuseStep 1696579 = 2544869) B2544869
theorem B3818321 : Blo 1695548 3818321 := bstep (se 2 (by rfl) ⟨1431870, by rfl⟩ : syracuseStep 3818321 = 2863741) B2863741
theorem B1696595 : Blo 1695548 1696595 := bstep (se 1 (by rfl) ⟨1272446, by rfl⟩ : syracuseStep 1696595 = 2544893) B2544893
theorem B1696611 : Blo 1695548 1696611 := bstep (se 1 (by rfl) ⟨1272458, by rfl⟩ : syracuseStep 1696611 = 2544917) B2544917
theorem B3818339 : Blo 1695548 3818339 := bstep (se 1 (by rfl) ⟨2863754, by rfl⟩ : syracuseStep 3818339 = 5727509) B5727509
theorem B1696627 : Blo 1695548 1696627 := bstep (se 1 (by rfl) ⟨1272470, by rfl⟩ : syracuseStep 1696627 = 2544941) B2544941
theorem B1696643 : Blo 1695548 1696643 := bstep (se 1 (by rfl) ⟨1272482, by rfl⟩ : syracuseStep 1696643 = 2544965) B2544965
theorem B1696659 : Blo 1695548 1696659 := bstep (se 1 (by rfl) ⟨1272494, by rfl⟩ : syracuseStep 1696659 = 2544989) B2544989
theorem B1909651 : Blo 1695548 1909651 := bstep (se 1 (by rfl) ⟨1432238, by rfl⟩ : syracuseStep 1909651 = 2864477) B2864477
theorem B1696675 : Blo 1695548 1696675 := bstep (se 1 (by rfl) ⟨1272506, by rfl⟩ : syracuseStep 1696675 = 2545013) B2545013
theorem B3621809 : Blo 1695548 3621809 := bstep (se 2 (by rfl) ⟨1358178, by rfl⟩ : syracuseStep 3621809 = 2716357) B2716357
theorem B8586161 : Blo 1695548 8586161 := bstep (se 2 (by rfl) ⟨3219810, by rfl⟩ : syracuseStep 8586161 = 6439621) B6439621
theorem B1696691 : Blo 1695548 1696691 := bstep (se 1 (by rfl) ⟨1272518, by rfl⟩ : syracuseStep 1696691 = 2545037) B2545037
theorem B3621827 : Blo 1695548 3621827 := bstep (se 1 (by rfl) ⟨2716370, by rfl⟩ : syracuseStep 3621827 = 5432741) B5432741
theorem B1696707 : Blo 1695548 1696707 := bstep (se 1 (by rfl) ⟨1272530, by rfl⟩ : syracuseStep 1696707 = 2545061) B2545061
theorem B5727185 : Blo 1695548 5727185 := bstep (se 2 (by rfl) ⟨2147694, by rfl⟩ : syracuseStep 5727185 = 4295389) B4295389
theorem B1696723 : Blo 1695548 1696723 := bstep (se 1 (by rfl) ⟨1272542, by rfl⟩ : syracuseStep 1696723 = 2545085) B2545085
theorem B1696739 : Blo 1695548 1696739 := bstep (se 1 (by rfl) ⟨1272554, by rfl⟩ : syracuseStep 1696739 = 2545109) B2545109
theorem B1696755 : Blo 1695548 1696755 := bstep (se 1 (by rfl) ⟨1272566, by rfl⟩ : syracuseStep 1696755 = 2545133) B2545133
theorem B1696771 : Blo 1695548 1696771 := bstep (se 1 (by rfl) ⟨1272578, by rfl⟩ : syracuseStep 1696771 = 2545157) B2545157
theorem B1696787 : Blo 1695548 1696787 := bstep (se 1 (by rfl) ⟨1272590, by rfl⟩ : syracuseStep 1696787 = 2545181) B2545181
theorem B1696803 : Blo 1695548 1696803 := bstep (se 1 (by rfl) ⟨1272602, by rfl⟩ : syracuseStep 1696803 = 2545205) B2545205
theorem B9667633 : Blo 1695548 9667633 := bstep (se 2 (by rfl) ⟨3625362, by rfl⟩ : syracuseStep 9667633 = 7250725) B7250725
theorem B2753587 : Blo 1695548 2753587 := bstep (se 1 (by rfl) ⟨2065190, by rfl⟩ : syracuseStep 2753587 = 4130381) B4130381
theorem B1696819 : Blo 1695548 1696819 := bstep (se 1 (by rfl) ⟨1272614, by rfl⟩ : syracuseStep 1696819 = 2545229) B2545229
theorem B4645955 : Blo 1695548 4645955 := bstep (se 1 (by rfl) ⟨3484466, by rfl⟩ : syracuseStep 4645955 = 6968933) B6968933
theorem B1696835 : Blo 1695548 1696835 := bstep (se 1 (by rfl) ⟨1272626, by rfl⟩ : syracuseStep 1696835 = 2545253) B2545253
theorem B16311365 : Blo 1695548 16311365 := bstep (se 4 (by rfl) ⟨1529190, by rfl⟩ : syracuseStep 16311365 = 3058381) B3058381
theorem B2147411 : Blo 1695548 2147411 := bstep (se 1 (by rfl) ⟨1610558, by rfl⟩ : syracuseStep 2147411 = 3221117) B3221117
theorem B1696851 : Blo 1695548 1696851 := bstep (se 1 (by rfl) ⟨1272638, by rfl⟩ : syracuseStep 1696851 = 2545277) B2545277
theorem B1696867 : Blo 1695548 1696867 := bstep (se 1 (by rfl) ⟨1272650, by rfl⟩ : syracuseStep 1696867 = 2545301) B2545301
theorem B3818609 : Blo 1695548 3818609 := bstep (se 2 (by rfl) ⟨1431978, by rfl⟩ : syracuseStep 3818609 = 2863957) B2863957
theorem B4899953 : Blo 1695548 4899953 := bstep (se 2 (by rfl) ⟨1837482, by rfl⟩ : syracuseStep 4899953 = 3674965) B3674965
theorem B1696883 : Blo 1695548 1696883 := bstep (se 1 (by rfl) ⟨1272662, by rfl⟩ : syracuseStep 1696883 = 2545325) B2545325
theorem B1696899 : Blo 1695548 1696899 := bstep (se 1 (by rfl) ⟨1272674, by rfl⟩ : syracuseStep 1696899 = 2545349) B2545349
theorem B3818627 : Blo 1695548 3818627 := bstep (se 1 (by rfl) ⟨2863970, by rfl⟩ : syracuseStep 3818627 = 5727941) B5727941
theorem B5883025 : Blo 1695548 5883025 := bstep (se 2 (by rfl) ⟨2206134, by rfl⟩ : syracuseStep 5883025 = 4412269) B4412269
theorem B1696915 : Blo 1695548 1696915 := bstep (se 1 (by rfl) ⟨1272686, by rfl⟩ : syracuseStep 1696915 = 2545373) B2545373
theorem B1696931 : Blo 1695548 1696931 := bstep (se 1 (by rfl) ⟨1272698, by rfl⟩ : syracuseStep 1696931 = 2545397) B2545397
theorem B4351153 : Blo 1695548 4351153 := bstep (se 2 (by rfl) ⟨1631682, by rfl⟩ : syracuseStep 4351153 = 3263365) B3263365
theorem B1696947 : Blo 1695548 1696947 := bstep (se 1 (by rfl) ⟨1272710, by rfl⟩ : syracuseStep 1696947 = 2545421) B2545421
theorem B1696963 : Blo 1695548 1696963 := bstep (se 1 (by rfl) ⟨1272722, by rfl⟩ : syracuseStep 1696963 = 2545445) B2545445
theorem B1696979 : Blo 1695548 1696979 := bstep (se 1 (by rfl) ⟨1272734, by rfl⟩ : syracuseStep 1696979 = 2545469) B2545469
theorem B1696995 : Blo 1695548 1696995 := bstep (se 1 (by rfl) ⟨1272746, by rfl⟩ : syracuseStep 1696995 = 2545493) B2545493
theorem B1860851 : Blo 1695548 1860851 := bstep (se 1 (by rfl) ⟨1395638, by rfl⟩ : syracuseStep 1860851 = 2791277) B2791277
theorem B1697011 : Blo 1695548 1697011 := bstep (se 1 (by rfl) ⟨1272758, by rfl⟩ : syracuseStep 1697011 = 2545517) B2545517
theorem B1697027 : Blo 1695548 1697027 := bstep (se 1 (by rfl) ⟨1272770, by rfl⟩ : syracuseStep 1697027 = 2545541) B2545541
theorem B1697043 : Blo 1695548 1697043 := bstep (se 1 (by rfl) ⟨1272782, by rfl⟩ : syracuseStep 1697043 = 2545565) B2545565
theorem B5432611 : Blo 1695548 5432611 := bstep (se 1 (by rfl) ⟨4074458, by rfl⟩ : syracuseStep 5432611 = 8148917) B8148917
theorem B1697059 : Blo 1695548 1697059 := bstep (se 1 (by rfl) ⟨1272794, by rfl⟩ : syracuseStep 1697059 = 2545589) B2545589
theorem B1697075 : Blo 1695548 1697075 := bstep (se 1 (by rfl) ⟨1272806, by rfl⟩ : syracuseStep 1697075 = 2545613) B2545613
theorem B1697091 : Blo 1695548 1697091 := bstep (se 1 (by rfl) ⟨1272818, by rfl⟩ : syracuseStep 1697091 = 2545637) B2545637
theorem B1697107 : Blo 1695548 1697107 := bstep (se 1 (by rfl) ⟨1272830, by rfl⟩ : syracuseStep 1697107 = 2545661) B2545661
theorem B1697123 : Blo 1695548 1697123 := bstep (se 1 (by rfl) ⟨1272842, by rfl⟩ : syracuseStep 1697123 = 2545685) B2545685
theorem B1811827 : Blo 1695548 1811827 := bstep (se 1 (by rfl) ⟨1358870, by rfl⟩ : syracuseStep 1811827 = 2717741) B2717741
theorem B1697139 : Blo 1695548 1697139 := bstep (se 1 (by rfl) ⟨1272854, by rfl⟩ : syracuseStep 1697139 = 2545709) B2545709
theorem B1697155 : Blo 1695548 1697155 := bstep (se 1 (by rfl) ⟨1272866, by rfl⟩ : syracuseStep 1697155 = 2545733) B2545733
theorem B3818897 : Blo 1695548 3818897 := bstep (se 2 (by rfl) ⟨1432086, by rfl⟩ : syracuseStep 3818897 = 2864173) B2864173
theorem B1697171 : Blo 1695548 1697171 := bstep (se 1 (by rfl) ⟨1272878, by rfl⟩ : syracuseStep 1697171 = 2545757) B2545757
theorem B1697187 : Blo 1695548 1697187 := bstep (se 1 (by rfl) ⟨1272890, by rfl⟩ : syracuseStep 1697187 = 2545781) B2545781
theorem B3818915 : Blo 1695548 3818915 := bstep (se 1 (by rfl) ⟨2864186, by rfl⟩ : syracuseStep 3818915 = 5728373) B5728373
theorem B1697203 : Blo 1695548 1697203 := bstep (se 1 (by rfl) ⟨1272902, by rfl⟩ : syracuseStep 1697203 = 2545805) B2545805
theorem B1697219 : Blo 1695548 1697219 := bstep (se 1 (by rfl) ⟨1272914, by rfl⟩ : syracuseStep 1697219 = 2545829) B2545829
theorem B1697235 : Blo 1695548 1697235 := bstep (se 1 (by rfl) ⟨1272926, by rfl⟩ : syracuseStep 1697235 = 2545853) B2545853
theorem B1697251 : Blo 1695548 1697251 := bstep (se 1 (by rfl) ⟨1272938, by rfl⟩ : syracuseStep 1697251 = 2545877) B2545877
theorem B5727725 : Blo 1695548 5727725 := bstep (se 3 (by rfl) ⟨1073948, by rfl⟩ : syracuseStep 5727725 = 2147897) B2147897
theorem B1697267 : Blo 1695548 1697267 := bstep (se 1 (by rfl) ⟨1272950, by rfl⟩ : syracuseStep 1697267 = 2545901) B2545901
theorem B1697283 : Blo 1695548 1697283 := bstep (se 1 (by rfl) ⟨1272962, by rfl⟩ : syracuseStep 1697283 = 2545925) B2545925
theorem B8152589 : Blo 1695548 8152589 := bstep (se 3 (by rfl) ⟨1528610, by rfl⟩ : syracuseStep 8152589 = 3057221) B3057221
theorem B1697299 : Blo 1695548 1697299 := bstep (se 1 (by rfl) ⟨1272974, by rfl⟩ : syracuseStep 1697299 = 2545949) B2545949
theorem B5727779 : Blo 1695548 5727779 := bstep (se 1 (by rfl) ⟨4295834, by rfl⟩ : syracuseStep 5727779 = 8591669) B8591669
theorem B1697315 : Blo 1695548 1697315 := bstep (se 1 (by rfl) ⟨1272986, by rfl⟩ : syracuseStep 1697315 = 2545973) B2545973
theorem B3221041 : Blo 1695548 3221041 := bstep (se 2 (by rfl) ⟨1207890, by rfl⟩ : syracuseStep 3221041 = 2415781) B2415781
theorem B1697331 : Blo 1695548 1697331 := bstep (se 1 (by rfl) ⟨1272998, by rfl⟩ : syracuseStep 1697331 = 2545997) B2545997
theorem B1697347 : Blo 1695548 1697347 := bstep (se 1 (by rfl) ⟨1273010, by rfl⟩ : syracuseStep 1697347 = 2546021) B2546021
theorem B10872397 : Blo 1695548 10872397 := bstep (se 3 (by rfl) ⟨2038574, by rfl⟩ : syracuseStep 10872397 = 4077149) B4077149
theorem B1697363 : Blo 1695548 1697363 := bstep (se 1 (by rfl) ⟨1273022, by rfl⟩ : syracuseStep 1697363 = 2546045) B2546045
theorem B1697379 : Blo 1695548 1697379 := bstep (se 1 (by rfl) ⟨1273034, by rfl⟩ : syracuseStep 1697379 = 2546069) B2546069
theorem B1697395 : Blo 1695548 1697395 := bstep (se 1 (by rfl) ⟨1273046, by rfl⟩ : syracuseStep 1697395 = 2546093) B2546093
theorem B5801603 : Blo 1695548 5801603 := bstep (se 1 (by rfl) ⟨4351202, by rfl⟩ : syracuseStep 5801603 = 8702405) B8702405
theorem B1697411 : Blo 1695548 1697411 := bstep (se 1 (by rfl) ⟨1273058, by rfl⟩ : syracuseStep 1697411 = 2546117) B2546117
theorem B1697427 : Blo 1695548 1697427 := bstep (se 1 (by rfl) ⟨1273070, by rfl⟩ : syracuseStep 1697427 = 2546141) B2546141
theorem B1697443 : Blo 1695548 1697443 := bstep (se 1 (by rfl) ⟨1273082, by rfl⟩ : syracuseStep 1697443 = 2546165) B2546165
theorem B3819185 : Blo 1695548 3819185 := bstep (se 2 (by rfl) ⟨1432194, by rfl⟩ : syracuseStep 3819185 = 2864389) B2864389
theorem B1697459 : Blo 1695548 1697459 := bstep (se 1 (by rfl) ⟨1273094, by rfl⟩ : syracuseStep 1697459 = 2546189) B2546189
theorem B3819203 : Blo 1695548 3819203 := bstep (se 1 (by rfl) ⟨2864402, by rfl⟩ : syracuseStep 3819203 = 5728805) B5728805
theorem B1697475 : Blo 1695548 1697475 := bstep (se 1 (by rfl) ⟨1273106, by rfl⟩ : syracuseStep 1697475 = 2546213) B2546213
theorem B3221201 : Blo 1695548 3221201 := bstep (se 2 (by rfl) ⟨1207950, by rfl⟩ : syracuseStep 3221201 = 2415901) B2415901
theorem B1697491 : Blo 1695548 1697491 := bstep (se 1 (by rfl) ⟨1273118, by rfl⟩ : syracuseStep 1697491 = 2546237) B2546237
theorem B19318499 : Blo 1695548 19318499 := bstep (se 1 (by rfl) ⟨14488874, by rfl⟩ : syracuseStep 19318499 = 28977749) B28977749
theorem B1697507 : Blo 1695548 1697507 := bstep (se 1 (by rfl) ⟨1273130, by rfl⟩ : syracuseStep 1697507 = 2546261) B2546261
theorem B1697523 : Blo 1695548 1697523 := bstep (se 1 (by rfl) ⟨1273142, by rfl⟩ : syracuseStep 1697523 = 2546285) B2546285
theorem B1697539 : Blo 1695548 1697539 := bstep (se 1 (by rfl) ⟨1273154, by rfl⟩ : syracuseStep 1697539 = 2546309) B2546309
theorem B4294417 : Blo 1695548 4294417 := bstep (se 2 (by rfl) ⟨1610406, by rfl⟩ : syracuseStep 4294417 = 3220813) B3220813
theorem B2148115 : Blo 1695548 2148115 := bstep (se 1 (by rfl) ⟨1611086, by rfl⟩ : syracuseStep 2148115 = 3222173) B3222173
theorem B5728049 : Blo 1695548 5728049 := bstep (se 2 (by rfl) ⟨2148018, by rfl⟩ : syracuseStep 5728049 = 4296037) B4296037
theorem B2148211 : Blo 1695548 2148211 := bstep (se 1 (by rfl) ⟨1611158, by rfl⟩ : syracuseStep 2148211 = 3222317) B3222317
theorem B6440867 : Blo 1695548 6440867 := bstep (se 1 (by rfl) ⟨4830650, by rfl⟩ : syracuseStep 6440867 = 9661301) B9661301
theorem B3819473 : Blo 1695548 3819473 := bstep (se 2 (by rfl) ⟨1432302, by rfl⟩ : syracuseStep 3819473 = 2864605) B2864605
theorem B1812451 : Blo 1695548 1812451 := bstep (se 1 (by rfl) ⟨1359338, by rfl⟩ : syracuseStep 1812451 = 2718677) B2718677
theorem B5375971 : Blo 1695548 5375971 := bstep (se 1 (by rfl) ⟨4031978, by rfl⟩ : syracuseStep 5375971 = 8063957) B8063957
theorem B7243789 : Blo 1695548 7243789 := bstep (se 3 (by rfl) ⟨1358210, by rfl⟩ : syracuseStep 7243789 = 2716421) B2716421
theorem B4294691 : Blo 1695548 4294691 := bstep (se 1 (by rfl) ⟨3221018, by rfl⟩ : syracuseStep 4294691 = 6442037) B6442037
theorem B12879971 : Blo 1695548 12879971 := bstep (se 1 (by rfl) ⟨9659978, by rfl⟩ : syracuseStep 12879971 = 19319957) B19319957
theorem B3057763 : Blo 1695548 3057763 := bstep (se 1 (by rfl) ⟨2293322, by rfl⟩ : syracuseStep 3057763 = 4586645) B4586645
theorem B3221603 : Blo 1695548 3221603 := bstep (se 1 (by rfl) ⟨2416202, by rfl⟩ : syracuseStep 3221603 = 4832405) B4832405
theorem B4294883 : Blo 1695548 4294883 := bstep (se 1 (by rfl) ⟨3221162, by rfl⟩ : syracuseStep 4294883 = 6442325) B6442325
theorem B27519203 : Blo 1695548 27519203 := bstep (se 1 (by rfl) ⟨20639402, by rfl⟩ : syracuseStep 27519203 = 41278805) B41278805
theorem B2861345 : Blo 1695548 2861345 := bstep (se 2 (by rfl) ⟨1073004, by rfl⟩ : syracuseStep 2861345 = 2146009) B2146009
theorem B5728589 : Blo 1695548 5728589 := bstep (se 3 (by rfl) ⟨1074110, by rfl⟩ : syracuseStep 5728589 = 2148221) B2148221
theorem B8587619 : Blo 1695548 8587619 := bstep (se 1 (by rfl) ⟨6440714, by rfl⟩ : syracuseStep 8587619 = 12881429) B12881429
theorem B5728643 : Blo 1695548 5728643 := bstep (se 1 (by rfl) ⟨4296482, by rfl⟩ : syracuseStep 5728643 = 8592965) B8592965
theorem B2861473 : Blo 1695548 2861473 := bstep (se 2 (by rfl) ⟨1073052, by rfl⟩ : syracuseStep 2861473 = 2146105) B2146105
theorem B2861507 : Blo 1695548 2861507 := bstep (se 1 (by rfl) ⟨2146130, by rfl⟩ : syracuseStep 2861507 = 4292261) B4292261
theorem B12224965 : Blo 1695548 12224965 := bstep (se 4 (by rfl) ⟨1146090, by rfl⟩ : syracuseStep 12224965 = 2292181) B2292181
theorem B9660869 : Blo 1695548 9660869 := bstep (se 4 (by rfl) ⟨905706, by rfl⟩ : syracuseStep 9660869 = 1811413) B1811413
theorem B5433841 : Blo 1695548 5433841 := bstep (se 2 (by rfl) ⟨2037690, by rfl⟩ : syracuseStep 5433841 = 4075381) B4075381
theorem B3672611 : Blo 1695548 3672611 := bstep (se 1 (by rfl) ⟨2754458, by rfl⟩ : syracuseStep 3672611 = 5508917) B5508917
theorem B2861635 : Blo 1695548 2861635 := bstep (se 1 (by rfl) ⟨2146226, by rfl⟩ : syracuseStep 2861635 = 4292453) B4292453
theorem B16304753 : Blo 1695548 16304753 := bstep (se 2 (by rfl) ⟨6114282, by rfl⟩ : syracuseStep 16304753 = 12228565) B12228565
theorem B5728913 : Blo 1695548 5728913 := bstep (se 2 (by rfl) ⟨2148342, by rfl⟩ : syracuseStep 5728913 = 4296685) B4296685
theorem B7735985 : Blo 1695548 7735985 := bstep (se 2 (by rfl) ⟨2900994, by rfl⟩ : syracuseStep 7735985 = 5801989) B5801989
theorem B2861777 : Blo 1695548 2861777 := bstep (se 2 (by rfl) ⟨1073166, by rfl⟩ : syracuseStep 2861777 = 2146333) B2146333
theorem B5229361 : Blo 1695548 5229361 := bstep (se 2 (by rfl) ⟨1961010, by rfl⟩ : syracuseStep 5229361 = 3922021) B3922021
theorem B1960771 : Blo 1695548 1960771 := bstep (se 1 (by rfl) ⟨1470578, by rfl⟩ : syracuseStep 1960771 = 2941157) B2941157
theorem B2861905 : Blo 1695548 2861905 := bstep (se 2 (by rfl) ⟨1073214, by rfl⟩ : syracuseStep 2861905 = 2146429) B2146429
theorem B2861939 : Blo 1695548 2861939 := bstep (se 1 (by rfl) ⟨2146454, by rfl⟩ : syracuseStep 2861939 = 4292909) B4292909
theorem B6441869 : Blo 1695548 6441869 := bstep (se 3 (by rfl) ⟨1207850, by rfl⟩ : syracuseStep 6441869 = 2415701) B2415701
theorem B3623825 : Blo 1695548 3623825 := bstep (se 2 (by rfl) ⟨1358934, by rfl⟩ : syracuseStep 3623825 = 2717869) B2717869
theorem B2902979 : Blo 1695548 2902979 := bstep (se 1 (by rfl) ⟨2177234, by rfl⟩ : syracuseStep 2902979 = 4354469) B4354469
theorem B3222499 : Blo 1695548 3222499 := bstep (se 1 (by rfl) ⟨2416874, by rfl⟩ : syracuseStep 3222499 = 4833749) B4833749
theorem B2862067 : Blo 1695548 2862067 := bstep (se 1 (by rfl) ⟨2146550, by rfl⟩ : syracuseStep 2862067 = 4293101) B4293101
theorem B9169955 : Blo 1695548 9169955 := bstep (se 1 (by rfl) ⟨6877466, by rfl⟩ : syracuseStep 9169955 = 13754933) B13754933
theorem B5434445 : Blo 1695548 5434445 := bstep (se 3 (by rfl) ⟨1018958, by rfl⟩ : syracuseStep 5434445 = 2037917) B2037917
theorem B7736419 : Blo 1695548 7736419 := bstep (se 1 (by rfl) ⟨5802314, by rfl⟩ : syracuseStep 7736419 = 11604629) B11604629
theorem B2862209 : Blo 1695548 2862209 := bstep (se 2 (by rfl) ⟨1073328, by rfl⟩ : syracuseStep 2862209 = 2146657) B2146657
theorem B3222659 : Blo 1695548 3222659 := bstep (se 1 (by rfl) ⟨2416994, by rfl⟩ : syracuseStep 3222659 = 4833989) B4833989
theorem B8588429 : Blo 1695548 8588429 := bstep (se 3 (by rfl) ⟨1610330, by rfl⟩ : syracuseStep 8588429 = 3220661) B3220661
theorem B4295825 : Blo 1695548 4295825 := bstep (se 2 (by rfl) ⟨1610934, by rfl⟩ : syracuseStep 4295825 = 3221869) B3221869
theorem B4295875 : Blo 1695548 4295875 := bstep (se 1 (by rfl) ⟨3221906, by rfl⟩ : syracuseStep 4295875 = 6443813) B6443813
theorem B2862337 : Blo 1695548 2862337 := bstep (se 2 (by rfl) ⟨1073376, by rfl⟩ : syracuseStep 2862337 = 2146753) B2146753
theorem B2862371 : Blo 1695548 2862371 := bstep (se 1 (by rfl) ⟨2146778, by rfl⟩ : syracuseStep 2862371 = 4293557) B4293557
theorem B4648259 : Blo 1695548 4648259 := bstep (se 1 (by rfl) ⟨3486194, by rfl⟩ : syracuseStep 4648259 = 6972389) B6972389
theorem B4296017 : Blo 1695548 4296017 := bstep (se 2 (by rfl) ⟨1611006, by rfl⟩ : syracuseStep 4296017 = 3222013) B3222013
theorem B5803409 : Blo 1695548 5803409 := bstep (se 2 (by rfl) ⟨2176278, by rfl⟩ : syracuseStep 5803409 = 4352557) B4352557
theorem B2862499 : Blo 1695548 2862499 := bstep (se 1 (by rfl) ⟨2146874, by rfl⟩ : syracuseStep 2862499 = 4293749) B4293749
theorem B3624355 : Blo 1695548 3624355 := bstep (se 1 (by rfl) ⟨2718266, by rfl⟩ : syracuseStep 3624355 = 5436533) B5436533
theorem B2862641 : Blo 1695548 2862641 := bstep (se 2 (by rfl) ⟨1073490, by rfl⟩ : syracuseStep 2862641 = 2146981) B2146981
theorem B21745205 : Blo 1695548 21745205 := bstep (se 5 (by rfl) ⟨1019306, by rfl⟩ : syracuseStep 21745205 = 2038613) B2038613
theorem B1961635 : Blo 1695548 1961635 := bstep (se 1 (by rfl) ⟨1471226, by rfl⟩ : syracuseStep 1961635 = 2942453) B2942453
theorem B2862769 : Blo 1695548 2862769 := bstep (se 2 (by rfl) ⟨1073538, by rfl⟩ : syracuseStep 2862769 = 2147077) B2147077
theorem B2862803 : Blo 1695548 2862803 := bstep (se 1 (by rfl) ⟨2147102, by rfl⟩ : syracuseStep 2862803 = 4294205) B4294205
theorem B2543345 : Blo 1695548 2543345 := bstep (se 2 (by rfl) ⟨953754, by rfl⟩ : syracuseStep 2543345 = 1907509) B1907509
theorem B2543363 : Blo 1695548 2543363 := bstep (se 1 (by rfl) ⟨1907522, by rfl⟩ : syracuseStep 2543363 = 3815045) B3815045
theorem B2543393 : Blo 1695548 2543393 := bstep (se 2 (by rfl) ⟨953772, by rfl⟩ : syracuseStep 2543393 = 1907545) B1907545
theorem B2543411 : Blo 1695548 2543411 := bstep (se 1 (by rfl) ⟨1907558, by rfl⟩ : syracuseStep 2543411 = 3815117) B3815117
theorem B12226373 : Blo 1695548 12226373 := bstep (se 4 (by rfl) ⟨1146222, by rfl⟩ : syracuseStep 12226373 = 2292445) B2292445
theorem B2543441 : Blo 1695548 2543441 := bstep (se 2 (by rfl) ⟨953790, by rfl⟩ : syracuseStep 2543441 = 1907581) B1907581
theorem B2862931 : Blo 1695548 2862931 := bstep (se 1 (by rfl) ⟨2147198, by rfl⟩ : syracuseStep 2862931 = 4294397) B4294397
theorem B2543459 : Blo 1695548 2543459 := bstep (se 1 (by rfl) ⟨1907594, by rfl⟩ : syracuseStep 2543459 = 3815189) B3815189
theorem B2543489 : Blo 1695548 2543489 := bstep (se 2 (by rfl) ⟨953808, by rfl⟩ : syracuseStep 2543489 = 1907617) B1907617
theorem B4894595 : Blo 1695548 4894595 := bstep (se 1 (by rfl) ⟨3670946, by rfl⟩ : syracuseStep 4894595 = 7341893) B7341893
theorem B2543507 : Blo 1695548 2543507 := bstep (se 1 (by rfl) ⟨1907630, by rfl⟩ : syracuseStep 2543507 = 3815261) B3815261
theorem B2543537 : Blo 1695548 2543537 := bstep (se 2 (by rfl) ⟨953826, by rfl⟩ : syracuseStep 2543537 = 1907653) B1907653
theorem B2543555 : Blo 1695548 2543555 := bstep (se 1 (by rfl) ⟨1907666, by rfl⟩ : syracuseStep 2543555 = 3815333) B3815333
theorem B2543585 : Blo 1695548 2543585 := bstep (se 2 (by rfl) ⟨953844, by rfl⟩ : syracuseStep 2543585 = 1907689) B1907689
theorem B2863073 : Blo 1695548 2863073 := bstep (se 2 (by rfl) ⟨1073652, by rfl⟩ : syracuseStep 2863073 = 2147305) B2147305
theorem B2543603 : Blo 1695548 2543603 := bstep (se 1 (by rfl) ⟨1907702, by rfl⟩ : syracuseStep 2543603 = 3815405) B3815405
theorem B2543633 : Blo 1695548 2543633 := bstep (se 2 (by rfl) ⟨953862, by rfl⟩ : syracuseStep 2543633 = 1907725) B1907725
theorem B2543651 : Blo 1695548 2543651 := bstep (se 1 (by rfl) ⟨1907738, by rfl⟩ : syracuseStep 2543651 = 3815477) B3815477
theorem B4075555 : Blo 1695548 4075555 := bstep (se 1 (by rfl) ⟨3056666, by rfl⟩ : syracuseStep 4075555 = 6113333) B6113333
theorem B2543681 : Blo 1695548 2543681 := bstep (se 2 (by rfl) ⟨953880, by rfl⟩ : syracuseStep 2543681 = 1907761) B1907761
theorem B2543699 : Blo 1695548 2543699 := bstep (se 1 (by rfl) ⟨1907774, by rfl⟩ : syracuseStep 2543699 = 3815549) B3815549
theorem B2863201 : Blo 1695548 2863201 := bstep (se 2 (by rfl) ⟨1073700, by rfl⟩ : syracuseStep 2863201 = 2147401) B2147401
theorem B19591267 : Blo 1695548 19591267 := bstep (se 1 (by rfl) ⟨14693450, by rfl⟩ : syracuseStep 19591267 = 29386901) B29386901
theorem B2543729 : Blo 1695548 2543729 := bstep (se 2 (by rfl) ⟨953898, by rfl⟩ : syracuseStep 2543729 = 1907797) B1907797
theorem B2543747 : Blo 1695548 2543747 := bstep (se 1 (by rfl) ⟨1907810, by rfl⟩ : syracuseStep 2543747 = 3815621) B3815621
theorem B2863235 : Blo 1695548 2863235 := bstep (se 1 (by rfl) ⟨2147426, by rfl⟩ : syracuseStep 2863235 = 4294853) B4294853
theorem B2543777 : Blo 1695548 2543777 := bstep (se 2 (by rfl) ⟨953916, by rfl⟩ : syracuseStep 2543777 = 1907833) B1907833
theorem B2543795 : Blo 1695548 2543795 := bstep (se 1 (by rfl) ⟨1907846, by rfl⟩ : syracuseStep 2543795 = 3815693) B3815693
theorem B2543825 : Blo 1695548 2543825 := bstep (se 2 (by rfl) ⟨953934, by rfl⟩ : syracuseStep 2543825 = 1907869) B1907869
theorem B2543843 : Blo 1695548 2543843 := bstep (se 1 (by rfl) ⟨1907882, by rfl⟩ : syracuseStep 2543843 = 3815765) B3815765
theorem B2543873 : Blo 1695548 2543873 := bstep (se 2 (by rfl) ⟨953952, by rfl⟩ : syracuseStep 2543873 = 1907905) B1907905
theorem B2863363 : Blo 1695548 2863363 := bstep (se 1 (by rfl) ⟨2147522, by rfl⟩ : syracuseStep 2863363 = 4295045) B4295045
theorem B2543891 : Blo 1695548 2543891 := bstep (se 1 (by rfl) ⟨1907918, by rfl⟩ : syracuseStep 2543891 = 3815837) B3815837
theorem B2543921 : Blo 1695548 2543921 := bstep (se 2 (by rfl) ⟨953970, by rfl⟩ : syracuseStep 2543921 = 1907941) B1907941
theorem B4829489 : Blo 1695548 4829489 := bstep (se 2 (by rfl) ⟨1811058, by rfl⟩ : syracuseStep 4829489 = 3622117) B3622117
theorem B2543939 : Blo 1695548 2543939 := bstep (se 1 (by rfl) ⟨1907954, by rfl⟩ : syracuseStep 2543939 = 3815909) B3815909
theorem B2543969 : Blo 1695548 2543969 := bstep (se 2 (by rfl) ⟨953988, by rfl⟩ : syracuseStep 2543969 = 1907977) B1907977
theorem B2543987 : Blo 1695548 2543987 := bstep (se 1 (by rfl) ⟨1907990, by rfl⟩ : syracuseStep 2543987 = 3815981) B3815981
theorem B2716049 : Blo 1695548 2716049 := bstep (se 2 (by rfl) ⟨1018518, by rfl⟩ : syracuseStep 2716049 = 2037037) B2037037
theorem B2544017 : Blo 1695548 2544017 := bstep (se 2 (by rfl) ⟨954006, by rfl⟩ : syracuseStep 2544017 = 1908013) B1908013
theorem B2863505 : Blo 1695548 2863505 := bstep (se 2 (by rfl) ⟨1073814, by rfl⟩ : syracuseStep 2863505 = 2147629) B2147629
theorem B2544035 : Blo 1695548 2544035 := bstep (se 1 (by rfl) ⟨1908026, by rfl⟩ : syracuseStep 2544035 = 3816053) B3816053
theorem B5722541 : Blo 1695548 5722541 := bstep (se 3 (by rfl) ⟨1072976, by rfl⟩ : syracuseStep 5722541 = 2145953) B2145953
theorem B10867121 : Blo 1695548 10867121 := bstep (se 2 (by rfl) ⟨4075170, by rfl⟩ : syracuseStep 10867121 = 8150341) B8150341
theorem B2544065 : Blo 1695548 2544065 := bstep (se 2 (by rfl) ⟨954024, by rfl⟩ : syracuseStep 2544065 = 1908049) B1908049
theorem B2544083 : Blo 1695548 2544083 := bstep (se 1 (by rfl) ⟨1908062, by rfl⟩ : syracuseStep 2544083 = 3816125) B3816125
theorem B5722595 : Blo 1695548 5722595 := bstep (se 1 (by rfl) ⟨4291946, by rfl⟩ : syracuseStep 5722595 = 8583893) B8583893
theorem B2544113 : Blo 1695548 2544113 := bstep (se 2 (by rfl) ⟨954042, by rfl⟩ : syracuseStep 2544113 = 1908085) B1908085
theorem B2544131 : Blo 1695548 2544131 := bstep (se 1 (by rfl) ⟨1908098, by rfl⟩ : syracuseStep 2544131 = 3816197) B3816197
theorem B2863633 : Blo 1695548 2863633 := bstep (se 2 (by rfl) ⟨1073862, by rfl⟩ : syracuseStep 2863633 = 2147725) B2147725
theorem B2544161 : Blo 1695548 2544161 := bstep (se 2 (by rfl) ⟨954060, by rfl⟩ : syracuseStep 2544161 = 1908121) B1908121
theorem B2544179 : Blo 1695548 2544179 := bstep (se 1 (by rfl) ⟨1908134, by rfl⟩ : syracuseStep 2544179 = 3816269) B3816269
theorem B2863667 : Blo 1695548 2863667 := bstep (se 1 (by rfl) ⟨2147750, by rfl⟩ : syracuseStep 2863667 = 4295501) B4295501
theorem B2544209 : Blo 1695548 2544209 := bstep (se 2 (by rfl) ⟨954078, by rfl⟩ : syracuseStep 2544209 = 1908157) B1908157
theorem B2544227 : Blo 1695548 2544227 := bstep (se 1 (by rfl) ⟨1908170, by rfl⟩ : syracuseStep 2544227 = 3816341) B3816341
theorem B5509745 : Blo 1695548 5509745 := bstep (se 2 (by rfl) ⟨2066154, by rfl⟩ : syracuseStep 5509745 = 4132309) B4132309
theorem B2544257 : Blo 1695548 2544257 := bstep (se 2 (by rfl) ⟨954096, by rfl⟩ : syracuseStep 2544257 = 1908193) B1908193
theorem B2544275 : Blo 1695548 2544275 := bstep (se 1 (by rfl) ⟨1908206, by rfl⟩ : syracuseStep 2544275 = 3816413) B3816413
theorem B2544305 : Blo 1695548 2544305 := bstep (se 2 (by rfl) ⟨954114, by rfl⟩ : syracuseStep 2544305 = 1908229) B1908229
theorem B2863795 : Blo 1695548 2863795 := bstep (se 1 (by rfl) ⟨2147846, by rfl⟩ : syracuseStep 2863795 = 4295693) B4295693
theorem B2544323 : Blo 1695548 2544323 := bstep (se 1 (by rfl) ⟨1908242, by rfl⟩ : syracuseStep 2544323 = 3816485) B3816485
theorem B2544353 : Blo 1695548 2544353 := bstep (se 2 (by rfl) ⟨954132, by rfl⟩ : syracuseStep 2544353 = 1908265) B1908265
theorem B5722865 : Blo 1695548 5722865 := bstep (se 2 (by rfl) ⟨2146074, by rfl⟩ : syracuseStep 5722865 = 4292149) B4292149
theorem B2544371 : Blo 1695548 2544371 := bstep (se 1 (by rfl) ⟨1908278, by rfl⟩ : syracuseStep 2544371 = 3816557) B3816557
theorem B4133635 : Blo 1695548 4133635 := bstep (se 1 (by rfl) ⟨3100226, by rfl⟩ : syracuseStep 4133635 = 6200453) B6200453
theorem B2544401 : Blo 1695548 2544401 := bstep (se 2 (by rfl) ⟨954150, by rfl⟩ : syracuseStep 2544401 = 1908301) B1908301
theorem B2544419 : Blo 1695548 2544419 := bstep (se 1 (by rfl) ⟨1908314, by rfl⟩ : syracuseStep 2544419 = 3816629) B3816629
theorem B36680501 : Blo 1695548 36680501 := bstep (se 5 (by rfl) ⟨1719398, by rfl⟩ : syracuseStep 36680501 = 3438797) B3438797
theorem B2544449 : Blo 1695548 2544449 := bstep (se 2 (by rfl) ⟨954168, by rfl⟩ : syracuseStep 2544449 = 1908337) B1908337
theorem B2863937 : Blo 1695548 2863937 := bstep (se 2 (by rfl) ⟨1073976, by rfl⟩ : syracuseStep 2863937 = 2147953) B2147953
theorem B2544467 : Blo 1695548 2544467 := bstep (se 1 (by rfl) ⟨1908350, by rfl⟩ : syracuseStep 2544467 = 3816701) B3816701
theorem B2544497 : Blo 1695548 2544497 := bstep (se 2 (by rfl) ⟨954186, by rfl⟩ : syracuseStep 2544497 = 1908373) B1908373
theorem B4076401 : Blo 1695548 4076401 := bstep (se 2 (by rfl) ⟨1528650, by rfl⟩ : syracuseStep 4076401 = 3057301) B3057301
theorem B2544515 : Blo 1695548 2544515 := bstep (se 1 (by rfl) ⟨1908386, by rfl⟩ : syracuseStep 2544515 = 3816773) B3816773
theorem B2544545 : Blo 1695548 2544545 := bstep (se 2 (by rfl) ⟨954204, by rfl⟩ : syracuseStep 2544545 = 1908409) B1908409
theorem B2544563 : Blo 1695548 2544563 := bstep (se 1 (by rfl) ⟨1908422, by rfl⟩ : syracuseStep 2544563 = 3816845) B3816845
theorem B2864065 : Blo 1695548 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B6443981 : Blo 1695548 6443981 := bstep (se 3 (by rfl) ⟨1208246, by rfl⟩ : syracuseStep 6443981 = 2416493) B2416493
theorem B2544593 : Blo 1695548 2544593 := bstep (se 2 (by rfl) ⟨954222, by rfl⟩ : syracuseStep 2544593 = 1908445) B1908445
theorem B2544611 : Blo 1695548 2544611 := bstep (se 1 (by rfl) ⟨1908458, by rfl⟩ : syracuseStep 2544611 = 3816917) B3816917
theorem B2864099 : Blo 1695548 2864099 := bstep (se 1 (by rfl) ⟨2148074, by rfl⟩ : syracuseStep 2864099 = 4296149) B4296149
theorem B2544641 : Blo 1695548 2544641 := bstep (se 2 (by rfl) ⟨954240, by rfl⟩ : syracuseStep 2544641 = 1908481) B1908481
theorem B2544659 : Blo 1695548 2544659 := bstep (se 1 (by rfl) ⟨1908494, by rfl⟩ : syracuseStep 2544659 = 3816989) B3816989
theorem B2544689 : Blo 1695548 2544689 := bstep (se 2 (by rfl) ⟨954258, by rfl⟩ : syracuseStep 2544689 = 1908517) B1908517
theorem B2544707 : Blo 1695548 2544707 := bstep (se 1 (by rfl) ⟨1908530, by rfl⟩ : syracuseStep 2544707 = 3817061) B3817061
theorem B2544737 : Blo 1695548 2544737 := bstep (se 2 (by rfl) ⟨954276, by rfl⟩ : syracuseStep 2544737 = 1908553) B1908553
theorem B2864227 : Blo 1695548 2864227 := bstep (se 1 (by rfl) ⟨2148170, by rfl⟩ : syracuseStep 2864227 = 4296341) B4296341
theorem B5231729 : Blo 1695548 5231729 := bstep (se 2 (by rfl) ⟨1961898, by rfl⟩ : syracuseStep 5231729 = 3923797) B3923797
theorem B2544755 : Blo 1695548 2544755 := bstep (se 1 (by rfl) ⟨1908566, by rfl⟩ : syracuseStep 2544755 = 3817133) B3817133
theorem B2544785 : Blo 1695548 2544785 := bstep (se 2 (by rfl) ⟨954294, by rfl⟩ : syracuseStep 2544785 = 1908589) B1908589
theorem B2544803 : Blo 1695548 2544803 := bstep (se 1 (by rfl) ⟨1908602, by rfl⟩ : syracuseStep 2544803 = 3817205) B3817205
theorem B2544833 : Blo 1695548 2544833 := bstep (se 2 (by rfl) ⟨954312, by rfl⟩ : syracuseStep 2544833 = 1908625) B1908625
theorem B2544851 : Blo 1695548 2544851 := bstep (se 1 (by rfl) ⟨1908638, by rfl⟩ : syracuseStep 2544851 = 3817277) B3817277
theorem B4830445 : Blo 1695548 4830445 := bstep (se 3 (by rfl) ⟨905708, by rfl⟩ : syracuseStep 4830445 = 1811417) B1811417
theorem B2544881 : Blo 1695548 2544881 := bstep (se 2 (by rfl) ⟨954330, by rfl⟩ : syracuseStep 2544881 = 1908661) B1908661
theorem B2864369 : Blo 1695548 2864369 := bstep (se 2 (by rfl) ⟨1074138, by rfl⟩ : syracuseStep 2864369 = 2148277) B2148277
theorem B2716915 : Blo 1695548 2716915 := bstep (se 1 (by rfl) ⟨2037686, by rfl⟩ : syracuseStep 2716915 = 4075373) B4075373
theorem B2544899 : Blo 1695548 2544899 := bstep (se 1 (by rfl) ⟨1908674, by rfl⟩ : syracuseStep 2544899 = 3817349) B3817349
theorem B5723405 : Blo 1695548 5723405 := bstep (se 3 (by rfl) ⟨1073138, by rfl⟩ : syracuseStep 5723405 = 2146277) B2146277
theorem B2544929 : Blo 1695548 2544929 := bstep (se 2 (by rfl) ⟨954348, by rfl⟩ : syracuseStep 2544929 = 1908697) B1908697
theorem B2544947 : Blo 1695548 2544947 := bstep (se 1 (by rfl) ⟨1908710, by rfl⟩ : syracuseStep 2544947 = 3817421) B3817421
theorem B5723459 : Blo 1695548 5723459 := bstep (se 1 (by rfl) ⟨4292594, by rfl⟩ : syracuseStep 5723459 = 8585189) B8585189
theorem B2544977 : Blo 1695548 2544977 := bstep (se 2 (by rfl) ⟨954366, by rfl⟩ : syracuseStep 2544977 = 1908733) B1908733
theorem B2544995 : Blo 1695548 2544995 := bstep (se 1 (by rfl) ⟨1908746, by rfl⟩ : syracuseStep 2544995 = 3817493) B3817493
theorem B2864497 : Blo 1695548 2864497 := bstep (se 2 (by rfl) ⟨1074186, by rfl⟩ : syracuseStep 2864497 = 2148373) B2148373
theorem B2545025 : Blo 1695548 2545025 := bstep (se 2 (by rfl) ⟨954384, by rfl⟩ : syracuseStep 2545025 = 1908769) B1908769
theorem B2545043 : Blo 1695548 2545043 := bstep (se 1 (by rfl) ⟨1908782, by rfl⟩ : syracuseStep 2545043 = 3817565) B3817565
theorem B2864531 : Blo 1695548 2864531 := bstep (se 1 (by rfl) ⟨2148398, by rfl⟩ : syracuseStep 2864531 = 4296797) B4296797
theorem B2545073 : Blo 1695548 2545073 := bstep (se 2 (by rfl) ⟨954402, by rfl⟩ : syracuseStep 2545073 = 1908805) B1908805
theorem B2037187 : Blo 1695548 2037187 := bstep (se 1 (by rfl) ⟨1527890, by rfl⟩ : syracuseStep 2037187 = 3055781) B3055781
theorem B2545091 : Blo 1695548 2545091 := bstep (se 1 (by rfl) ⟨1908818, by rfl⟩ : syracuseStep 2545091 = 3817637) B3817637
theorem B4830673 : Blo 1695548 4830673 := bstep (se 2 (by rfl) ⟨1811502, by rfl⟩ : syracuseStep 4830673 = 3623005) B3623005
theorem B2545121 : Blo 1695548 2545121 := bstep (se 2 (by rfl) ⟨954420, by rfl⟩ : syracuseStep 2545121 = 1908841) B1908841
theorem B10868195 : Blo 1695548 10868195 := bstep (se 1 (by rfl) ⟨8151146, by rfl⟩ : syracuseStep 10868195 = 16302293) B16302293
theorem B2545139 : Blo 1695548 2545139 := bstep (se 1 (by rfl) ⟨1908854, by rfl⟩ : syracuseStep 2545139 = 3817709) B3817709
theorem B2545169 : Blo 1695548 2545169 := bstep (se 2 (by rfl) ⟨954438, by rfl⟩ : syracuseStep 2545169 = 1908877) B1908877
theorem B2545187 : Blo 1695548 2545187 := bstep (se 1 (by rfl) ⟨1908890, by rfl⟩ : syracuseStep 2545187 = 3817781) B3817781
theorem B2545217 : Blo 1695548 2545217 := bstep (se 2 (by rfl) ⟨954456, by rfl⟩ : syracuseStep 2545217 = 1908913) B1908913
theorem B5723729 : Blo 1695548 5723729 := bstep (se 2 (by rfl) ⟨2146398, by rfl⟩ : syracuseStep 5723729 = 4292797) B4292797
theorem B2545235 : Blo 1695548 2545235 := bstep (se 1 (by rfl) ⟨1908926, by rfl⟩ : syracuseStep 2545235 = 3817853) B3817853
theorem B4830833 : Blo 1695548 4830833 := bstep (se 2 (by rfl) ⟨1811562, by rfl⟩ : syracuseStep 4830833 = 3623125) B3623125
theorem B2545265 : Blo 1695548 2545265 := bstep (se 2 (by rfl) ⟨954474, by rfl⟩ : syracuseStep 2545265 = 1908949) B1908949
theorem B2037379 : Blo 1695548 2037379 := bstep (se 1 (by rfl) ⟨1528034, by rfl⟩ : syracuseStep 2037379 = 3056069) B3056069
theorem B2545283 : Blo 1695548 2545283 := bstep (se 1 (by rfl) ⟨1908962, by rfl⟩ : syracuseStep 2545283 = 3817925) B3817925
theorem B2545313 : Blo 1695548 2545313 := bstep (se 2 (by rfl) ⟨954492, by rfl⟩ : syracuseStep 2545313 = 1908985) B1908985
theorem B2414243 : Blo 1695548 2414243 := bstep (se 1 (by rfl) ⟨1810682, by rfl⟩ : syracuseStep 2414243 = 3621365) B3621365
theorem B2545331 : Blo 1695548 2545331 := bstep (se 1 (by rfl) ⟨1908998, by rfl⟩ : syracuseStep 2545331 = 3817997) B3817997
theorem B2545361 : Blo 1695548 2545361 := bstep (se 2 (by rfl) ⟨954510, by rfl⟩ : syracuseStep 2545361 = 1909021) B1909021
theorem B4830947 : Blo 1695548 4830947 := bstep (se 1 (by rfl) ⟨3623210, by rfl⟩ : syracuseStep 4830947 = 7246421) B7246421
theorem B2545379 : Blo 1695548 2545379 := bstep (se 1 (by rfl) ⟨1909034, by rfl⟩ : syracuseStep 2545379 = 3818069) B3818069
theorem B3815153 : Blo 1695548 3815153 := bstep (se 2 (by rfl) ⟨1430682, by rfl⟩ : syracuseStep 3815153 = 2861365) B2861365
theorem B6444785 : Blo 1695548 6444785 := bstep (se 2 (by rfl) ⟨2416794, by rfl⟩ : syracuseStep 6444785 = 4833589) B4833589
theorem B2414323 : Blo 1695548 2414323 := bstep (se 1 (by rfl) ⟨1810742, by rfl⟩ : syracuseStep 2414323 = 3621485) B3621485
theorem B2545409 : Blo 1695548 2545409 := bstep (se 2 (by rfl) ⟨954528, by rfl⟩ : syracuseStep 2545409 = 1909057) B1909057
theorem B3815171 : Blo 1695548 3815171 := bstep (se 1 (by rfl) ⟨2861378, by rfl⟩ : syracuseStep 3815171 = 5722757) B5722757
theorem B5158673 : Blo 1695548 5158673 := bstep (se 2 (by rfl) ⟨1934502, by rfl⟩ : syracuseStep 5158673 = 3869005) B3869005
theorem B2545427 : Blo 1695548 2545427 := bstep (se 1 (by rfl) ⟨1909070, by rfl⟩ : syracuseStep 2545427 = 3818141) B3818141
theorem B2545457 : Blo 1695548 2545457 := bstep (se 2 (by rfl) ⟨954546, by rfl⟩ : syracuseStep 2545457 = 1909093) B1909093
theorem B2545475 : Blo 1695548 2545475 := bstep (se 1 (by rfl) ⟨1909106, by rfl⟩ : syracuseStep 2545475 = 3818213) B3818213
theorem B2545505 : Blo 1695548 2545505 := bstep (se 2 (by rfl) ⟨954564, by rfl⟩ : syracuseStep 2545505 = 1909129) B1909129
theorem B2545523 : Blo 1695548 2545523 := bstep (se 1 (by rfl) ⟨1909142, by rfl⟩ : syracuseStep 2545523 = 3818285) B3818285
theorem B2545553 : Blo 1695548 2545553 := bstep (se 2 (by rfl) ⟨954582, by rfl⟩ : syracuseStep 2545553 = 1909165) B1909165
theorem B2717587 : Blo 1695548 2717587 := bstep (se 1 (by rfl) ⟨2038190, by rfl⟩ : syracuseStep 2717587 = 4076381) B4076381
theorem B8148899 : Blo 1695548 8148899 := bstep (se 1 (by rfl) ⟨6111674, by rfl⟩ : syracuseStep 8148899 = 12223349) B12223349
theorem B2545571 : Blo 1695548 2545571 := bstep (se 1 (by rfl) ⟨1909178, by rfl⟩ : syracuseStep 2545571 = 3818357) B3818357
theorem B2717633 : Blo 1695548 2717633 := bstep (se 2 (by rfl) ⟨1019112, by rfl⟩ : syracuseStep 2717633 = 2038225) B2038225
theorem B2545601 : Blo 1695548 2545601 := bstep (se 2 (by rfl) ⟨954600, by rfl⟩ : syracuseStep 2545601 = 1909201) B1909201
theorem B2209747 : Blo 1695548 2209747 := bstep (se 1 (by rfl) ⟨1657310, by rfl⟩ : syracuseStep 2209747 = 3314621) B3314621
theorem B2545619 : Blo 1695548 2545619 := bstep (se 1 (by rfl) ⟨1909214, by rfl⟩ : syracuseStep 2545619 = 3818429) B3818429
theorem B8591345 : Blo 1695548 8591345 := bstep (se 2 (by rfl) ⟨3221754, by rfl⟩ : syracuseStep 8591345 = 6443509) B6443509
theorem B2545649 : Blo 1695548 2545649 := bstep (se 2 (by rfl) ⟨954618, by rfl⟩ : syracuseStep 2545649 = 1909237) B1909237
theorem B2545667 : Blo 1695548 2545667 := bstep (se 1 (by rfl) ⟨1909250, by rfl⟩ : syracuseStep 2545667 = 3818501) B3818501
theorem B3815441 : Blo 1695548 3815441 := bstep (se 2 (by rfl) ⟨1430790, by rfl⟩ : syracuseStep 3815441 = 2861581) B2861581
theorem B2545697 : Blo 1695548 2545697 := bstep (se 2 (by rfl) ⟨954636, by rfl⟩ : syracuseStep 2545697 = 1909273) B1909273
theorem B3815459 : Blo 1695548 3815459 := bstep (se 1 (by rfl) ⟨2861594, by rfl⟩ : syracuseStep 3815459 = 5723189) B5723189
theorem B2545715 : Blo 1695548 2545715 := bstep (se 1 (by rfl) ⟨1909286, by rfl⟩ : syracuseStep 2545715 = 3818573) B3818573
theorem B2545745 : Blo 1695548 2545745 := bstep (se 2 (by rfl) ⟨954654, by rfl⟩ : syracuseStep 2545745 = 1909309) B1909309
theorem B2545763 : Blo 1695548 2545763 := bstep (se 1 (by rfl) ⟨1909322, by rfl⟩ : syracuseStep 2545763 = 3818645) B3818645
theorem B5724269 : Blo 1695548 5724269 := bstep (se 3 (by rfl) ⟨1073300, by rfl⟩ : syracuseStep 5724269 = 2146601) B2146601
theorem B2545793 : Blo 1695548 2545793 := bstep (se 2 (by rfl) ⟨954672, by rfl⟩ : syracuseStep 2545793 = 1909345) B1909345
theorem B5961869 : Blo 1695548 5961869 := bstep (se 3 (by rfl) ⟨1117850, by rfl⟩ : syracuseStep 5961869 = 2235701) B2235701
theorem B2545811 : Blo 1695548 2545811 := bstep (se 1 (by rfl) ⟨1909358, by rfl⟩ : syracuseStep 2545811 = 3818717) B3818717
theorem B5724323 : Blo 1695548 5724323 := bstep (se 1 (by rfl) ⟨4293242, by rfl⟩ : syracuseStep 5724323 = 8586485) B8586485
theorem B2545841 : Blo 1695548 2545841 := bstep (se 2 (by rfl) ⟨954690, by rfl⟩ : syracuseStep 2545841 = 1909381) B1909381
theorem B2291905 : Blo 1695548 2291905 := bstep (se 2 (by rfl) ⟨859464, by rfl⟩ : syracuseStep 2291905 = 1718929) B1718929
theorem B2545859 : Blo 1695548 2545859 := bstep (se 1 (by rfl) ⟨1909394, by rfl⟩ : syracuseStep 2545859 = 3818789) B3818789
theorem B9664717 : Blo 1695548 9664717 := bstep (se 3 (by rfl) ⟨1812134, by rfl⟩ : syracuseStep 9664717 = 3624269) B3624269
theorem B2545889 : Blo 1695548 2545889 := bstep (se 2 (by rfl) ⟨954708, by rfl⟩ : syracuseStep 2545889 = 1909417) B1909417
theorem B7248113 : Blo 1695548 7248113 := bstep (se 2 (by rfl) ⟨2718042, by rfl⟩ : syracuseStep 7248113 = 5436085) B5436085
theorem B2545907 : Blo 1695548 2545907 := bstep (se 1 (by rfl) ⟨1909430, by rfl⟩ : syracuseStep 2545907 = 3818861) B3818861
theorem B2545937 : Blo 1695548 2545937 := bstep (se 2 (by rfl) ⟨954726, by rfl⟩ : syracuseStep 2545937 = 1909453) B1909453
theorem B2414881 : Blo 1695548 2414881 := bstep (se 2 (by rfl) ⟨905580, by rfl⟩ : syracuseStep 2414881 = 1811161) B1811161
theorem B7346467 : Blo 1695548 7346467 := bstep (se 1 (by rfl) ⟨5509850, by rfl⟩ : syracuseStep 7346467 = 11019701) B11019701
theorem B7248163 : Blo 1695548 7248163 := bstep (se 1 (by rfl) ⟨5436122, by rfl⟩ : syracuseStep 7248163 = 10872245) B10872245
theorem B2545955 : Blo 1695548 2545955 := bstep (se 1 (by rfl) ⟨1909466, by rfl⟩ : syracuseStep 2545955 = 3818933) B3818933
theorem B3815729 : Blo 1695548 3815729 := bstep (se 2 (by rfl) ⟨1430898, by rfl⟩ : syracuseStep 3815729 = 2861797) B2861797
theorem B46414133 : Blo 1695548 46414133 := bstep (se 5 (by rfl) ⟨2175662, by rfl⟩ : syracuseStep 46414133 = 4351325) B4351325
theorem B2545985 : Blo 1695548 2545985 := bstep (se 2 (by rfl) ⟨954744, by rfl⟩ : syracuseStep 2545985 = 1909489) B1909489
theorem B3815747 : Blo 1695548 3815747 := bstep (se 1 (by rfl) ⟨2861810, by rfl⟩ : syracuseStep 3815747 = 5723621) B5723621
theorem B5437763 : Blo 1695548 5437763 := bstep (se 1 (by rfl) ⟨4078322, by rfl⟩ : syracuseStep 5437763 = 8156645) B8156645
theorem B2546003 : Blo 1695548 2546003 := bstep (se 1 (by rfl) ⟨1909502, by rfl⟩ : syracuseStep 2546003 = 3819005) B3819005
theorem B2546033 : Blo 1695548 2546033 := bstep (se 2 (by rfl) ⟨954762, by rfl⟩ : syracuseStep 2546033 = 1909525) B1909525
theorem B2546051 : Blo 1695548 2546051 := bstep (se 1 (by rfl) ⟨1909538, by rfl⟩ : syracuseStep 2546051 = 3819077) B3819077
theorem B2546081 : Blo 1695548 2546081 := bstep (se 2 (by rfl) ⟨954780, by rfl⟩ : syracuseStep 2546081 = 1909561) B1909561
theorem B5724593 : Blo 1695548 5724593 := bstep (se 2 (by rfl) ⟨2146722, by rfl⟩ : syracuseStep 5724593 = 4293445) B4293445
theorem B2546099 : Blo 1695548 2546099 := bstep (se 1 (by rfl) ⟨1909574, by rfl⟩ : syracuseStep 2546099 = 3819149) B3819149
theorem B2718145 : Blo 1695548 2718145 := bstep (se 2 (by rfl) ⟨1019304, by rfl⟩ : syracuseStep 2718145 = 2038609) B2038609
theorem B2546129 : Blo 1695548 2546129 := bstep (se 2 (by rfl) ⟨954798, by rfl⟩ : syracuseStep 2546129 = 1909597) B1909597
theorem B2546147 : Blo 1695548 2546147 := bstep (se 1 (by rfl) ⟨1909610, by rfl⟩ : syracuseStep 2546147 = 3819221) B3819221
theorem B6117859 : Blo 1695548 6117859 := bstep (se 1 (by rfl) ⟨4588394, by rfl⟩ : syracuseStep 6117859 = 9176789) B9176789
theorem B2546177 : Blo 1695548 2546177 := bstep (se 2 (by rfl) ⟨954816, by rfl⟩ : syracuseStep 2546177 = 1909633) B1909633
theorem B4897297 : Blo 1695548 4897297 := bstep (se 2 (by rfl) ⟨1836486, by rfl⟩ : syracuseStep 4897297 = 3672973) B3672973
theorem B2546195 : Blo 1695548 2546195 := bstep (se 1 (by rfl) ⟨1909646, by rfl⟩ : syracuseStep 2546195 = 3819293) B3819293
theorem B2546225 : Blo 1695548 2546225 := bstep (se 2 (by rfl) ⟨954834, by rfl⟩ : syracuseStep 2546225 = 1909669) B1909669
theorem B2546243 : Blo 1695548 2546243 := bstep (se 1 (by rfl) ⟨1909682, by rfl⟩ : syracuseStep 2546243 = 3819365) B3819365
theorem B3816017 : Blo 1695548 3816017 := bstep (se 2 (by rfl) ⟨1431006, by rfl⟩ : syracuseStep 3816017 = 2862013) B2862013
theorem B2546273 : Blo 1695548 2546273 := bstep (se 2 (by rfl) ⟨954852, by rfl⟩ : syracuseStep 2546273 = 1909705) B1909705
theorem B3816035 : Blo 1695548 3816035 := bstep (se 1 (by rfl) ⟨2862026, by rfl⟩ : syracuseStep 3816035 = 5724053) B5724053
theorem B2546291 : Blo 1695548 2546291 := bstep (se 1 (by rfl) ⟨1909718, by rfl⟩ : syracuseStep 2546291 = 3819437) B3819437
theorem B2546321 : Blo 1695548 2546321 := bstep (se 2 (by rfl) ⟨954870, by rfl⟩ : syracuseStep 2546321 = 1909741) B1909741
theorem B10312355 : Blo 1695548 10312355 := bstep (se 1 (by rfl) ⟨7734266, by rfl⟩ : syracuseStep 10312355 = 15468533) B15468533
theorem B4831949 : Blo 1695548 4831949 := bstep (se 3 (by rfl) ⟨905990, by rfl⟩ : syracuseStep 4831949 = 1811981) B1811981
theorem B3816305 : Blo 1695548 3816305 := bstep (se 2 (by rfl) ⟨1431114, by rfl⟩ : syracuseStep 3816305 = 2862229) B2862229
theorem B3816323 : Blo 1695548 3816323 := bstep (se 1 (by rfl) ⟨2862242, by rfl⟩ : syracuseStep 3816323 = 5724485) B5724485
theorem B4832131 : Blo 1695548 4832131 := bstep (se 1 (by rfl) ⟨3624098, by rfl⟩ : syracuseStep 4832131 = 7248197) B7248197
theorem B1907635 : Blo 1695548 1907635 := bstep (se 1 (by rfl) ⟨1430726, by rfl⟩ : syracuseStep 1907635 = 2861453) B2861453
theorem B5725133 : Blo 1695548 5725133 := bstep (se 3 (by rfl) ⟨1073462, by rfl⟩ : syracuseStep 5725133 = 2146925) B2146925
theorem B2718689 : Blo 1695548 2718689 := bstep (se 2 (by rfl) ⟨1019508, by rfl⟩ : syracuseStep 2718689 = 2039017) B2039017
theorem B2415587 : Blo 1695548 2415587 := bstep (se 1 (by rfl) ⟨1811690, by rfl⟩ : syracuseStep 2415587 = 3623381) B3623381
theorem B5725187 : Blo 1695548 5725187 := bstep (se 1 (by rfl) ⟨4293890, by rfl⟩ : syracuseStep 5725187 = 8587781) B8587781
theorem B8707085 : Blo 1695548 8707085 := bstep (se 3 (by rfl) ⟨1632578, by rfl⟩ : syracuseStep 8707085 = 3265157) B3265157
theorem B4832291 : Blo 1695548 4832291 := bstep (se 1 (by rfl) ⟨3624218, by rfl⟩ : syracuseStep 4832291 = 7248437) B7248437
theorem B1907779 : Blo 1695548 1907779 := bstep (se 1 (by rfl) ⟨1430834, by rfl⟩ : syracuseStep 1907779 = 2861669) B2861669
theorem B8150129 : Blo 1695548 8150129 := bstep (se 2 (by rfl) ⟨3056298, by rfl⟩ : syracuseStep 8150129 = 6112597) B6112597
theorem B3816593 : Blo 1695548 3816593 := bstep (se 2 (by rfl) ⟨1431222, by rfl⟩ : syracuseStep 3816593 = 2862445) B2862445
theorem B3816611 : Blo 1695548 3816611 := bstep (se 1 (by rfl) ⟨2862458, by rfl⟩ : syracuseStep 3816611 = 5724917) B5724917
theorem B2038979 : Blo 1695548 2038979 := bstep (se 1 (by rfl) ⟨1529234, by rfl⟩ : syracuseStep 2038979 = 3058469) B3058469
theorem B1907923 : Blo 1695548 1907923 := bstep (se 1 (by rfl) ⟨1430942, by rfl⟩ : syracuseStep 1907923 = 2861885) B2861885
theorem B2579683 : Blo 1695548 2579683 := bstep (se 1 (by rfl) ⟨1934762, by rfl⟩ : syracuseStep 2579683 = 3869525) B3869525
theorem B5725457 : Blo 1695548 5725457 := bstep (se 2 (by rfl) ⟨2147046, by rfl⟩ : syracuseStep 5725457 = 4294093) B4294093
theorem B12885317 : Blo 1695548 12885317 := bstep (se 4 (by rfl) ⟨1207998, by rfl⟩ : syracuseStep 12885317 = 2415997) B2415997
theorem B1908067 : Blo 1695548 1908067 := bstep (se 1 (by rfl) ⟨1431050, by rfl⟩ : syracuseStep 1908067 = 2862101) B2862101
theorem B7740785 : Blo 1695548 7740785 := bstep (se 2 (by rfl) ⟨2902794, by rfl⟩ : syracuseStep 7740785 = 5805589) B5805589
theorem B8592803 : Blo 1695548 8592803 := bstep (se 1 (by rfl) ⟨6444602, by rfl⟩ : syracuseStep 8592803 = 12889205) B12889205
theorem B3816881 : Blo 1695548 3816881 := bstep (se 2 (by rfl) ⟨1431330, by rfl⟩ : syracuseStep 3816881 = 2862661) B2862661
theorem B3816899 : Blo 1695548 3816899 := bstep (se 1 (by rfl) ⟨2862674, by rfl⟩ : syracuseStep 3816899 = 5725349) B5725349
theorem B3218915 : Blo 1695548 3218915 := bstep (se 1 (by rfl) ⟨2414186, by rfl⟩ : syracuseStep 3218915 = 4828373) B4828373
theorem B1908211 : Blo 1695548 1908211 := bstep (se 1 (by rfl) ⟨1431158, by rfl⟩ : syracuseStep 1908211 = 2862317) B2862317
theorem B4292099 : Blo 1695548 4292099 := bstep (se 1 (by rfl) ⟨3219074, by rfl⟩ : syracuseStep 4292099 = 6438149) B6438149
theorem B2039315 : Blo 1695548 2039315 := bstep (se 1 (by rfl) ⟨1529486, by rfl⟩ : syracuseStep 2039315 = 3058973) B3058973
theorem B27901493 : Blo 1695548 27901493 := bstep (se 5 (by rfl) ⟨1307882, by rfl⟩ : syracuseStep 27901493 = 2615765) B2615765
theorem B2416225 : Blo 1695548 2416225 := bstep (se 2 (by rfl) ⟨906084, by rfl⟩ : syracuseStep 2416225 = 1812169) B1812169
theorem B1908355 : Blo 1695548 1908355 := bstep (se 1 (by rfl) ⟨1431266, by rfl⟩ : syracuseStep 1908355 = 2862533) B2862533
theorem B4587139 : Blo 1695548 4587139 := bstep (se 1 (by rfl) ⟨3440354, by rfl⟩ : syracuseStep 4587139 = 6880709) B6880709
theorem B4292291 : Blo 1695548 4292291 := bstep (se 1 (by rfl) ⟨3219218, by rfl⟩ : syracuseStep 4292291 = 6438437) B6438437
theorem B3817169 : Blo 1695548 3817169 := bstep (se 2 (by rfl) ⟨1431438, by rfl⟩ : syracuseStep 3817169 = 2862877) B2862877
theorem B2416339 : Blo 1695548 2416339 := bstep (se 1 (by rfl) ⟨1812254, by rfl⟩ : syracuseStep 2416339 = 3624509) B3624509
theorem B3817187 : Blo 1695548 3817187 := bstep (se 1 (by rfl) ⟨2862890, by rfl⟩ : syracuseStep 3817187 = 5725781) B5725781
theorem B3219203 : Blo 1695548 3219203 := bstep (se 1 (by rfl) ⟨2414402, by rfl⟩ : syracuseStep 3219203 = 4828805) B4828805
theorem B1908499 : Blo 1695548 1908499 := bstep (se 1 (by rfl) ⟨1431374, by rfl⟩ : syracuseStep 1908499 = 2862749) B2862749
theorem B5725997 : Blo 1695548 5725997 := bstep (se 3 (by rfl) ⟨1073624, by rfl⟩ : syracuseStep 5725997 = 2147249) B2147249
theorem B4587313 : Blo 1695548 4587313 := bstep (se 2 (by rfl) ⟨1720242, by rfl⟩ : syracuseStep 4587313 = 3440485) B3440485
theorem B1695555 : Blo 1695548 1695555 := bstep (se 1 (by rfl) ⟨1271666, by rfl⟩ : syracuseStep 1695555 = 2543333) B2543333
theorem B2146115 : Blo 1695548 2146115 := bstep (se 1 (by rfl) ⟨1609586, by rfl⟩ : syracuseStep 2146115 = 3219173) B3219173
theorem B11771725 : Blo 1695548 11771725 := bstep (se 3 (by rfl) ⟨2207198, by rfl⟩ : syracuseStep 11771725 = 4414397) B4414397
theorem B3055441 : Blo 1695548 3055441 := bstep (se 2 (by rfl) ⟨1145790, by rfl⟩ : syracuseStep 3055441 = 2291581) B2291581
theorem B1695571 : Blo 1695548 1695571 := bstep (se 1 (by rfl) ⟨1271678, by rfl⟩ : syracuseStep 1695571 = 2543357) B2543357
theorem B1695587 : Blo 1695548 1695587 := bstep (se 1 (by rfl) ⟨1271690, by rfl⟩ : syracuseStep 1695587 = 2543381) B2543381
theorem B5726051 : Blo 1695548 5726051 := bstep (se 1 (by rfl) ⟨4294538, by rfl⟩ : syracuseStep 5726051 = 8589077) B8589077
theorem B1695603 : Blo 1695548 1695603 := bstep (se 1 (by rfl) ⟨1271702, by rfl⟩ : syracuseStep 1695603 = 2543405) B2543405
theorem B1695619 : Blo 1695548 1695619 := bstep (se 1 (by rfl) ⟨1271714, by rfl⟩ : syracuseStep 1695619 = 2543429) B2543429
theorem B15482765 : Blo 1695548 15482765 := bstep (se 3 (by rfl) ⟨2903018, by rfl⟩ : syracuseStep 15482765 = 5806037) B5806037
theorem B1695635 : Blo 1695548 1695635 := bstep (se 1 (by rfl) ⟨1271726, by rfl⟩ : syracuseStep 1695635 = 2543453) B2543453
theorem B1695651 : Blo 1695548 1695651 := bstep (se 1 (by rfl) ⟨1271738, by rfl⟩ : syracuseStep 1695651 = 2543477) B2543477
theorem B1908643 : Blo 1695548 1908643 := bstep (se 1 (by rfl) ⟨1431482, by rfl⟩ : syracuseStep 1908643 = 2862965) B2862965
theorem B1695667 : Blo 1695548 1695667 := bstep (se 1 (by rfl) ⟨1271750, by rfl⟩ : syracuseStep 1695667 = 2543501) B2543501
theorem B1695683 : Blo 1695548 1695683 := bstep (se 1 (by rfl) ⟨1271762, by rfl⟩ : syracuseStep 1695683 = 2543525) B2543525
theorem B1695699 : Blo 1695548 1695699 := bstep (se 1 (by rfl) ⟨1271774, by rfl⟩ : syracuseStep 1695699 = 2543549) B2543549
theorem B1695715 : Blo 1695548 1695715 := bstep (se 1 (by rfl) ⟨1271786, by rfl⟩ : syracuseStep 1695715 = 2543573) B2543573
theorem B3817457 : Blo 1695548 3817457 := bstep (se 2 (by rfl) ⟨1431546, by rfl⟩ : syracuseStep 3817457 = 2863093) B2863093
theorem B1695731 : Blo 1695548 1695731 := bstep (se 1 (by rfl) ⟨1271798, by rfl⟩ : syracuseStep 1695731 = 2543597) B2543597
theorem B1695755 : Blo 1695548 1695755 := bstep (se 1 (by rfl) ⟨1271816, by rfl⟩ : syracuseStep 1695755 = 2543633) B2543633
theorem B9658385 : Blo 1695548 9658385 := bstep (se 2 (by rfl) ⟨3621894, by rfl⟩ : syracuseStep 9658385 = 7243789) B7243789
theorem B1695767 : Blo 1695548 1695767 := bstep (se 1 (by rfl) ⟨1271825, by rfl⟩ : syracuseStep 1695767 = 2543651) B2543651
theorem B1695787 : Blo 1695548 1695787 := bstep (se 1 (by rfl) ⟨1271840, by rfl⟩ : syracuseStep 1695787 = 2543681) B2543681
theorem B1695799 : Blo 1695548 1695799 := bstep (se 1 (by rfl) ⟨1271849, by rfl⟩ : syracuseStep 1695799 = 2543699) B2543699
theorem B1695819 : Blo 1695548 1695819 := bstep (se 1 (by rfl) ⟨1271864, by rfl⟩ : syracuseStep 1695819 = 2543729) B2543729
theorem B3817547 : Blo 1695548 3817547 := bstep (se 1 (by rfl) ⟨2863160, by rfl⟩ : syracuseStep 3817547 = 5726321) B5726321
theorem B1695831 : Blo 1695548 1695831 := bstep (se 1 (by rfl) ⟨1271873, by rfl⟩ : syracuseStep 1695831 = 2543747) B2543747
theorem B1908823 : Blo 1695548 1908823 := bstep (se 1 (by rfl) ⟨1431617, by rfl⟩ : syracuseStep 1908823 = 2863235) B2863235
theorem B1695851 : Blo 1695548 1695851 := bstep (se 1 (by rfl) ⟨1271888, by rfl⟩ : syracuseStep 1695851 = 2543777) B2543777
theorem B1695863 : Blo 1695548 1695863 := bstep (se 1 (by rfl) ⟨1271897, by rfl⟩ : syracuseStep 1695863 = 2543795) B2543795
theorem B3817601 : Blo 1695548 3817601 := bstep (se 2 (by rfl) ⟨1431600, by rfl⟩ : syracuseStep 3817601 = 2863201) B2863201
theorem B1695883 : Blo 1695548 1695883 := bstep (se 1 (by rfl) ⟨1271912, by rfl⟩ : syracuseStep 1695883 = 2543825) B2543825
theorem B1695895 : Blo 1695548 1695895 := bstep (se 1 (by rfl) ⟨1271921, by rfl⟩ : syracuseStep 1695895 = 2543843) B2543843
theorem B1695915 : Blo 1695548 1695915 := bstep (se 1 (by rfl) ⟨1271936, by rfl⟩ : syracuseStep 1695915 = 2543873) B2543873
theorem B1695927 : Blo 1695548 1695927 := bstep (se 1 (by rfl) ⟨1271945, by rfl⟩ : syracuseStep 1695927 = 2543891) B2543891
theorem B1695947 : Blo 1695548 1695947 := bstep (se 1 (by rfl) ⟨1271960, by rfl⟩ : syracuseStep 1695947 = 2543921) B2543921
theorem B3219659 : Blo 1695548 3219659 := bstep (se 1 (by rfl) ⟨2414744, by rfl⟩ : syracuseStep 3219659 = 4829489) B4829489
theorem B1695959 : Blo 1695548 1695959 := bstep (se 1 (by rfl) ⟨1271969, by rfl⟩ : syracuseStep 1695959 = 2543939) B2543939
theorem B5726429 : Blo 1695548 5726429 := bstep (se 3 (by rfl) ⟨1073705, by rfl⟩ : syracuseStep 5726429 = 2147411) B2147411
theorem B1695979 : Blo 1695548 1695979 := bstep (se 1 (by rfl) ⟨1271984, by rfl⟩ : syracuseStep 1695979 = 2543969) B2543969
theorem B1695991 : Blo 1695548 1695991 := bstep (se 1 (by rfl) ⟨1271993, by rfl⟩ : syracuseStep 1695991 = 2543987) B2543987
theorem B1696011 : Blo 1695548 1696011 := bstep (se 1 (by rfl) ⟨1272008, by rfl⟩ : syracuseStep 1696011 = 2544017) B2544017
theorem B1909003 : Blo 1695548 1909003 := bstep (se 1 (by rfl) ⟨1431752, by rfl⟩ : syracuseStep 1909003 = 2863505) B2863505
theorem B12886289 : Blo 1695548 12886289 := bstep (se 2 (by rfl) ⟨4832358, by rfl⟩ : syracuseStep 12886289 = 9664717) B9664717
theorem B1696023 : Blo 1695548 1696023 := bstep (se 1 (by rfl) ⟨1272017, by rfl⟩ : syracuseStep 1696023 = 2544035) B2544035
theorem B1696043 : Blo 1695548 1696043 := bstep (se 1 (by rfl) ⟨1272032, by rfl⟩ : syracuseStep 1696043 = 2544065) B2544065
theorem B13951277 : Blo 1695548 13951277 := bstep (se 3 (by rfl) ⟨2615864, by rfl⟩ : syracuseStep 13951277 = 5231729) B5231729
theorem B13066541 : Blo 1695548 13066541 := bstep (se 3 (by rfl) ⟨2449976, by rfl⟩ : syracuseStep 13066541 = 4899953) B4899953
theorem B1696055 : Blo 1695548 1696055 := bstep (se 1 (by rfl) ⟨1272041, by rfl⟩ : syracuseStep 1696055 = 2544083) B2544083
theorem B4292939 : Blo 1695548 4292939 := bstep (se 1 (by rfl) ⟨3219704, by rfl⟩ : syracuseStep 4292939 = 6439409) B6439409
theorem B1696075 : Blo 1695548 1696075 := bstep (se 1 (by rfl) ⟨1272056, by rfl⟩ : syracuseStep 1696075 = 2544113) B2544113
theorem B1696087 : Blo 1695548 1696087 := bstep (se 1 (by rfl) ⟨1272065, by rfl⟩ : syracuseStep 1696087 = 2544131) B2544131
theorem B3817817 : Blo 1695548 3817817 := bstep (se 2 (by rfl) ⟨1431681, by rfl⟩ : syracuseStep 3817817 = 2863363) B2863363
theorem B1696107 : Blo 1695548 1696107 := bstep (se 1 (by rfl) ⟨1272080, by rfl⟩ : syracuseStep 1696107 = 2544161) B2544161
theorem B1696119 : Blo 1695548 1696119 := bstep (se 1 (by rfl) ⟨1272089, by rfl⟩ : syracuseStep 1696119 = 2544179) B2544179
theorem B1909111 : Blo 1695548 1909111 := bstep (se 1 (by rfl) ⟨1431833, by rfl⟩ : syracuseStep 1909111 = 2863667) B2863667
theorem B3219841 : Blo 1695548 3219841 := bstep (se 2 (by rfl) ⟨1207440, by rfl⟩ : syracuseStep 3219841 = 2414881) B2414881
theorem B1696139 : Blo 1695548 1696139 := bstep (se 1 (by rfl) ⟨1272104, by rfl⟩ : syracuseStep 1696139 = 2544209) B2544209
theorem B1696151 : Blo 1695548 1696151 := bstep (se 1 (by rfl) ⟨1272113, by rfl⟩ : syracuseStep 1696151 = 2544227) B2544227
theorem B1696171 : Blo 1695548 1696171 := bstep (se 1 (by rfl) ⟨1272128, by rfl⟩ : syracuseStep 1696171 = 2544257) B2544257
theorem B3817907 : Blo 1695548 3817907 := bstep (se 1 (by rfl) ⟨2863430, by rfl⟩ : syracuseStep 3817907 = 5726861) B5726861
theorem B4833715 : Blo 1695548 4833715 := bstep (se 1 (by rfl) ⟨3625286, by rfl⟩ : syracuseStep 4833715 = 7250573) B7250573
theorem B1696183 : Blo 1695548 1696183 := bstep (se 1 (by rfl) ⟨1272137, by rfl⟩ : syracuseStep 1696183 = 2544275) B2544275
theorem B3621323 : Blo 1695548 3621323 := bstep (se 1 (by rfl) ⟨2715992, by rfl⟩ : syracuseStep 3621323 = 5431985) B5431985
theorem B1696203 : Blo 1695548 1696203 := bstep (se 1 (by rfl) ⟨1272152, by rfl⟩ : syracuseStep 1696203 = 2544305) B2544305
theorem B2146763 : Blo 1695548 2146763 := bstep (se 1 (by rfl) ⟨1610072, by rfl⟩ : syracuseStep 2146763 = 3220145) B3220145
theorem B1696215 : Blo 1695548 1696215 := bstep (se 1 (by rfl) ⟨1272161, by rfl⟩ : syracuseStep 1696215 = 2544323) B2544323
theorem B3817943 : Blo 1695548 3817943 := bstep (se 1 (by rfl) ⟨2863457, by rfl⟩ : syracuseStep 3817943 = 5726915) B5726915
theorem B1696235 : Blo 1695548 1696235 := bstep (se 1 (by rfl) ⟨1272176, by rfl⟩ : syracuseStep 1696235 = 2544353) B2544353
theorem B1696247 : Blo 1695548 1696247 := bstep (se 1 (by rfl) ⟨1272185, by rfl⟩ : syracuseStep 1696247 = 2544371) B2544371
theorem B1696267 : Blo 1695548 1696267 := bstep (se 1 (by rfl) ⟨1272200, by rfl⟩ : syracuseStep 1696267 = 2544401) B2544401
theorem B1696279 : Blo 1695548 1696279 := bstep (se 1 (by rfl) ⟨1272209, by rfl⟩ : syracuseStep 1696279 = 2544419) B2544419
theorem B24453667 : Blo 1695548 24453667 := bstep (se 1 (by rfl) ⟨18340250, by rfl⟩ : syracuseStep 24453667 = 36680501) B36680501
theorem B1696299 : Blo 1695548 1696299 := bstep (se 1 (by rfl) ⟨1272224, by rfl⟩ : syracuseStep 1696299 = 2544449) B2544449
theorem B1909291 : Blo 1695548 1909291 := bstep (se 1 (by rfl) ⟨1431968, by rfl⟩ : syracuseStep 1909291 = 2863937) B2863937
theorem B1696311 : Blo 1695548 1696311 := bstep (se 1 (by rfl) ⟨1272233, by rfl⟩ : syracuseStep 1696311 = 2544467) B2544467
theorem B1696331 : Blo 1695548 1696331 := bstep (se 1 (by rfl) ⟨1272248, by rfl⟩ : syracuseStep 1696331 = 2544497) B2544497
theorem B1696343 : Blo 1695548 1696343 := bstep (se 1 (by rfl) ⟨1272257, by rfl⟩ : syracuseStep 1696343 = 2544515) B2544515
theorem B1696363 : Blo 1695548 1696363 := bstep (se 1 (by rfl) ⟨1272272, by rfl⟩ : syracuseStep 1696363 = 2544545) B2544545
theorem B1696375 : Blo 1695548 1696375 := bstep (se 1 (by rfl) ⟨1272281, by rfl⟩ : syracuseStep 1696375 = 2544563) B2544563
theorem B1696395 : Blo 1695548 1696395 := bstep (se 1 (by rfl) ⟨1272296, by rfl⟩ : syracuseStep 1696395 = 2544593) B2544593
theorem B3818123 : Blo 1695548 3818123 := bstep (se 1 (by rfl) ⟨2863592, by rfl⟩ : syracuseStep 3818123 = 5727185) B5727185
theorem B1696407 : Blo 1695548 1696407 := bstep (se 1 (by rfl) ⟨1272305, by rfl⟩ : syracuseStep 1696407 = 2544611) B2544611
theorem B1909399 : Blo 1695548 1909399 := bstep (se 1 (by rfl) ⟨1432049, by rfl⟩ : syracuseStep 1909399 = 2864099) B2864099
theorem B1696427 : Blo 1695548 1696427 := bstep (se 1 (by rfl) ⟨1272320, by rfl⟩ : syracuseStep 1696427 = 2544641) B2544641
theorem B12878513 : Blo 1695548 12878513 := bstep (se 2 (by rfl) ⟨4829442, by rfl⟩ : syracuseStep 12878513 = 9658885) B9658885
theorem B1696439 : Blo 1695548 1696439 := bstep (se 1 (by rfl) ⟨1272329, by rfl⟩ : syracuseStep 1696439 = 2544659) B2544659
theorem B6529729 : Blo 1695548 6529729 := bstep (se 2 (by rfl) ⟨2448648, by rfl⟩ : syracuseStep 6529729 = 4897297) B4897297
theorem B3818177 : Blo 1695548 3818177 := bstep (se 2 (by rfl) ⟨1431816, by rfl⟩ : syracuseStep 3818177 = 2863633) B2863633
theorem B1696459 : Blo 1695548 1696459 := bstep (se 1 (by rfl) ⟨1272344, by rfl⟩ : syracuseStep 1696459 = 2544689) B2544689
theorem B1696471 : Blo 1695548 1696471 := bstep (se 1 (by rfl) ⟨1272353, by rfl⟩ : syracuseStep 1696471 = 2544707) B2544707
theorem B1696491 : Blo 1695548 1696491 := bstep (se 1 (by rfl) ⟨1272368, by rfl⟩ : syracuseStep 1696491 = 2544737) B2544737
theorem B1696503 : Blo 1695548 1696503 := bstep (se 1 (by rfl) ⟨1272377, by rfl⟩ : syracuseStep 1696503 = 2544755) B2544755
theorem B1696523 : Blo 1695548 1696523 := bstep (se 1 (by rfl) ⟨1272392, by rfl⟩ : syracuseStep 1696523 = 2544785) B2544785
theorem B1696535 : Blo 1695548 1696535 := bstep (se 1 (by rfl) ⟨1272401, by rfl⟩ : syracuseStep 1696535 = 2544803) B2544803
theorem B1696555 : Blo 1695548 1696555 := bstep (se 1 (by rfl) ⟨1272416, by rfl⟩ : syracuseStep 1696555 = 2544833) B2544833
theorem B1696567 : Blo 1695548 1696567 := bstep (se 1 (by rfl) ⟨1272425, by rfl⟩ : syracuseStep 1696567 = 2544851) B2544851
theorem B1696587 : Blo 1695548 1696587 := bstep (se 1 (by rfl) ⟨1272440, by rfl⟩ : syracuseStep 1696587 = 2544881) B2544881
theorem B1909579 : Blo 1695548 1909579 := bstep (se 1 (by rfl) ⟨1432184, by rfl⟩ : syracuseStep 1909579 = 2864369) B2864369
theorem B1696599 : Blo 1695548 1696599 := bstep (se 1 (by rfl) ⟨1272449, by rfl⟩ : syracuseStep 1696599 = 2544899) B2544899
theorem B1696619 : Blo 1695548 1696619 := bstep (se 1 (by rfl) ⟨1272464, by rfl⟩ : syracuseStep 1696619 = 2544929) B2544929
theorem B1696631 : Blo 1695548 1696631 := bstep (se 1 (by rfl) ⟨1272473, by rfl⟩ : syracuseStep 1696631 = 2544947) B2544947
theorem B1696651 : Blo 1695548 1696651 := bstep (se 1 (by rfl) ⟨1272488, by rfl⟩ : syracuseStep 1696651 = 2544977) B2544977
theorem B1696663 : Blo 1695548 1696663 := bstep (se 1 (by rfl) ⟨1272497, by rfl⟩ : syracuseStep 1696663 = 2544995) B2544995
theorem B3818393 : Blo 1695548 3818393 := bstep (se 2 (by rfl) ⟨1431897, by rfl⟩ : syracuseStep 3818393 = 2863795) B2863795
theorem B1696683 : Blo 1695548 1696683 := bstep (se 1 (by rfl) ⟨1272512, by rfl⟩ : syracuseStep 1696683 = 2545025) B2545025
theorem B1696695 : Blo 1695548 1696695 := bstep (se 1 (by rfl) ⟨1272521, by rfl⟩ : syracuseStep 1696695 = 2545043) B2545043
theorem B1909687 : Blo 1695548 1909687 := bstep (se 1 (by rfl) ⟨1432265, by rfl⟩ : syracuseStep 1909687 = 2864531) B2864531
theorem B4588481 : Blo 1695548 4588481 := bstep (se 2 (by rfl) ⟨1720680, by rfl⟩ : syracuseStep 4588481 = 3441361) B3441361
theorem B1696715 : Blo 1695548 1696715 := bstep (se 1 (by rfl) ⟨1272536, by rfl⟩ : syracuseStep 1696715 = 2545073) B2545073
theorem B1696727 : Blo 1695548 1696727 := bstep (se 1 (by rfl) ⟨1272545, by rfl⟩ : syracuseStep 1696727 = 2545091) B2545091
theorem B6882265 : Blo 1695548 6882265 := bstep (se 2 (by rfl) ⟨2580849, by rfl⟩ : syracuseStep 6882265 = 5161699) B5161699
theorem B1696747 : Blo 1695548 1696747 := bstep (se 1 (by rfl) ⟨1272560, by rfl⟩ : syracuseStep 1696747 = 2545121) B2545121
theorem B3818483 : Blo 1695548 3818483 := bstep (se 1 (by rfl) ⟨2863862, by rfl⟩ : syracuseStep 3818483 = 5727725) B5727725
theorem B1696759 : Blo 1695548 1696759 := bstep (se 1 (by rfl) ⟨1272569, by rfl⟩ : syracuseStep 1696759 = 2545139) B2545139
theorem B12223493 : Blo 1695548 12223493 := bstep (se 4 (by rfl) ⟨1145952, by rfl⟩ : syracuseStep 12223493 = 2291905) B2291905
theorem B1696779 : Blo 1695548 1696779 := bstep (se 1 (by rfl) ⟨1272584, by rfl⟩ : syracuseStep 1696779 = 2545169) B2545169
theorem B1696791 : Blo 1695548 1696791 := bstep (se 1 (by rfl) ⟨1272593, by rfl⟩ : syracuseStep 1696791 = 2545187) B2545187
theorem B3818519 : Blo 1695548 3818519 := bstep (se 1 (by rfl) ⟨2863889, by rfl⟩ : syracuseStep 3818519 = 5727779) B5727779
theorem B1696811 : Blo 1695548 1696811 := bstep (se 1 (by rfl) ⟨1272608, by rfl⟩ : syracuseStep 1696811 = 2545217) B2545217
theorem B7242797 : Blo 1695548 7242797 := bstep (se 3 (by rfl) ⟨1358024, by rfl⟩ : syracuseStep 7242797 = 2716049) B2716049
theorem B1696823 : Blo 1695548 1696823 := bstep (se 1 (by rfl) ⟨1272617, by rfl⟩ : syracuseStep 1696823 = 2545235) B2545235
theorem B6972481 : Blo 1695548 6972481 := bstep (se 2 (by rfl) ⟨2614680, by rfl⟩ : syracuseStep 6972481 = 5229361) B5229361
theorem B3220555 : Blo 1695548 3220555 := bstep (se 1 (by rfl) ⟨2415416, by rfl⟩ : syracuseStep 3220555 = 4830833) B4830833
theorem B1696843 : Blo 1695548 1696843 := bstep (se 1 (by rfl) ⟨1272632, by rfl⟩ : syracuseStep 1696843 = 2545265) B2545265
theorem B1696855 : Blo 1695548 1696855 := bstep (se 1 (by rfl) ⟨1272641, by rfl⟩ : syracuseStep 1696855 = 2545283) B2545283
theorem B2614361 : Blo 1695548 2614361 := bstep (se 2 (by rfl) ⟨980385, by rfl⟩ : syracuseStep 2614361 = 1960771) B1960771
theorem B9176165 : Blo 1695548 9176165 := bstep (se 4 (by rfl) ⟨860265, by rfl⟩ : syracuseStep 9176165 = 1720531) B1720531
theorem B1696875 : Blo 1695548 1696875 := bstep (se 1 (by rfl) ⟨1272656, by rfl⟩ : syracuseStep 1696875 = 2545313) B2545313
theorem B1696887 : Blo 1695548 1696887 := bstep (se 1 (by rfl) ⟨1272665, by rfl⟩ : syracuseStep 1696887 = 2545331) B2545331
theorem B2147467 : Blo 1695548 2147467 := bstep (se 1 (by rfl) ⟨1610600, by rfl⟩ : syracuseStep 2147467 = 3221201) B3221201
theorem B1696907 : Blo 1695548 1696907 := bstep (se 1 (by rfl) ⟨1272680, by rfl⟩ : syracuseStep 1696907 = 2545361) B2545361
theorem B12878999 : Blo 1695548 12878999 := bstep (se 1 (by rfl) ⟨9659249, by rfl⟩ : syracuseStep 12878999 = 19318499) B19318499
theorem B3220631 : Blo 1695548 3220631 := bstep (se 1 (by rfl) ⟨2415473, by rfl⟩ : syracuseStep 3220631 = 4830947) B4830947
theorem B1696919 : Blo 1695548 1696919 := bstep (se 1 (by rfl) ⟨1272689, by rfl⟩ : syracuseStep 1696919 = 2545379) B2545379
theorem B1696939 : Blo 1695548 1696939 := bstep (se 1 (by rfl) ⟨1272704, by rfl⟩ : syracuseStep 1696939 = 2545409) B2545409
theorem B1696951 : Blo 1695548 1696951 := bstep (se 1 (by rfl) ⟨1272713, by rfl⟩ : syracuseStep 1696951 = 2545427) B2545427
theorem B1696971 : Blo 1695548 1696971 := bstep (se 1 (by rfl) ⟨1272728, by rfl⟩ : syracuseStep 1696971 = 2545457) B2545457
theorem B3818699 : Blo 1695548 3818699 := bstep (se 1 (by rfl) ⟨2864024, by rfl⟩ : syracuseStep 3818699 = 5728049) B5728049
theorem B1696983 : Blo 1695548 1696983 := bstep (se 1 (by rfl) ⟨1272737, by rfl⟩ : syracuseStep 1696983 = 2545475) B2545475
theorem B1697003 : Blo 1695548 1697003 := bstep (se 1 (by rfl) ⟨1272752, by rfl⟩ : syracuseStep 1697003 = 2545505) B2545505
theorem B1697015 : Blo 1695548 1697015 := bstep (se 1 (by rfl) ⟨1272761, by rfl⟩ : syracuseStep 1697015 = 2545523) B2545523
theorem B3818753 : Blo 1695548 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B1697035 : Blo 1695548 1697035 := bstep (se 1 (by rfl) ⟨1272776, by rfl⟩ : syracuseStep 1697035 = 2545553) B2545553
theorem B5432599 : Blo 1695548 5432599 := bstep (se 1 (by rfl) ⟨4074449, by rfl⟩ : syracuseStep 5432599 = 8148899) B8148899
theorem B4293911 : Blo 1695548 4293911 := bstep (se 1 (by rfl) ⟨3220433, by rfl⟩ : syracuseStep 4293911 = 6440867) B6440867
theorem B1697047 : Blo 1695548 1697047 := bstep (se 1 (by rfl) ⟨1272785, by rfl⟩ : syracuseStep 1697047 = 2545571) B2545571
theorem B1811755 : Blo 1695548 1811755 := bstep (se 1 (by rfl) ⟨1358816, by rfl⟩ : syracuseStep 1811755 = 2717633) B2717633
theorem B1697067 : Blo 1695548 1697067 := bstep (se 1 (by rfl) ⟨1272800, by rfl⟩ : syracuseStep 1697067 = 2545601) B2545601
theorem B1697079 : Blo 1695548 1697079 := bstep (se 1 (by rfl) ⟨1272809, by rfl⟩ : syracuseStep 1697079 = 2545619) B2545619
theorem B5727563 : Blo 1695548 5727563 := bstep (se 1 (by rfl) ⟨4295672, by rfl⟩ : syracuseStep 5727563 = 8591345) B8591345
theorem B1697099 : Blo 1695548 1697099 := bstep (se 1 (by rfl) ⟨1272824, by rfl⟩ : syracuseStep 1697099 = 2545649) B2545649
theorem B1697111 : Blo 1695548 1697111 := bstep (se 1 (by rfl) ⟨1272833, by rfl⟩ : syracuseStep 1697111 = 2545667) B2545667
theorem B22046053 : Blo 1695548 22046053 := bstep (se 4 (by rfl) ⟨2066817, by rfl⟩ : syracuseStep 22046053 = 4133635) B4133635
theorem B1697131 : Blo 1695548 1697131 := bstep (se 1 (by rfl) ⟨1272848, by rfl⟩ : syracuseStep 1697131 = 2545697) B2545697
theorem B1697143 : Blo 1695548 1697143 := bstep (se 1 (by rfl) ⟨1272857, by rfl⟩ : syracuseStep 1697143 = 2545715) B2545715
theorem B1697163 : Blo 1695548 1697163 := bstep (se 1 (by rfl) ⟨1272872, by rfl⟩ : syracuseStep 1697163 = 2545745) B2545745
theorem B8586647 : Blo 1695548 8586647 := bstep (se 1 (by rfl) ⟨6439985, by rfl⟩ : syracuseStep 8586647 = 12879971) B12879971
theorem B3671449 : Blo 1695548 3671449 := bstep (se 2 (by rfl) ⟨1376793, by rfl⟩ : syracuseStep 3671449 = 2753587) B2753587
theorem B2147735 : Blo 1695548 2147735 := bstep (se 1 (by rfl) ⟨1610801, by rfl⟩ : syracuseStep 2147735 = 3221603) B3221603
theorem B1697175 : Blo 1695548 1697175 := bstep (se 1 (by rfl) ⟨1272881, by rfl⟩ : syracuseStep 1697175 = 2545763) B2545763
theorem B1697195 : Blo 1695548 1697195 := bstep (se 1 (by rfl) ⟨1272896, by rfl⟩ : syracuseStep 1697195 = 2545793) B2545793
theorem B3974579 : Blo 1695548 3974579 := bstep (se 1 (by rfl) ⟨2980934, by rfl⟩ : syracuseStep 3974579 = 5961869) B5961869
theorem B1697207 : Blo 1695548 1697207 := bstep (se 1 (by rfl) ⟨1272905, by rfl⟩ : syracuseStep 1697207 = 2545811) B2545811
theorem B1697227 : Blo 1695548 1697227 := bstep (se 1 (by rfl) ⟨1272920, by rfl⟩ : syracuseStep 1697227 = 2545841) B2545841
theorem B1697239 : Blo 1695548 1697239 := bstep (se 1 (by rfl) ⟨1272929, by rfl⟩ : syracuseStep 1697239 = 2545859) B2545859
theorem B10315225 : Blo 1695548 10315225 := bstep (se 2 (by rfl) ⟨3868209, by rfl⟩ : syracuseStep 10315225 = 7736419) B7736419
theorem B3818969 : Blo 1695548 3818969 := bstep (se 2 (by rfl) ⟨1432113, by rfl⟩ : syracuseStep 3818969 = 2864227) B2864227
theorem B1697259 : Blo 1695548 1697259 := bstep (se 1 (by rfl) ⟨1272944, by rfl⟩ : syracuseStep 1697259 = 2545889) B2545889
theorem B1697271 : Blo 1695548 1697271 := bstep (se 1 (by rfl) ⟨1272953, by rfl⟩ : syracuseStep 1697271 = 2545907) B2545907
theorem B1697291 : Blo 1695548 1697291 := bstep (se 1 (by rfl) ⟨1272968, by rfl⟩ : syracuseStep 1697291 = 2545937) B2545937
theorem B1697303 : Blo 1695548 1697303 := bstep (se 1 (by rfl) ⟨1272977, by rfl⟩ : syracuseStep 1697303 = 2545955) B2545955
theorem B30942755 : Blo 1695548 30942755 := bstep (se 1 (by rfl) ⟨23207066, by rfl⟩ : syracuseStep 30942755 = 46414133) B46414133
theorem B1697323 : Blo 1695548 1697323 := bstep (se 1 (by rfl) ⟨1272992, by rfl⟩ : syracuseStep 1697323 = 2545985) B2545985
theorem B3819059 : Blo 1695548 3819059 := bstep (se 1 (by rfl) ⟨2864294, by rfl⟩ : syracuseStep 3819059 = 5728589) B5728589
theorem B1697335 : Blo 1695548 1697335 := bstep (se 1 (by rfl) ⟨1273001, by rfl⟩ : syracuseStep 1697335 = 2546003) B2546003
theorem B5801537 : Blo 1695548 5801537 := bstep (se 2 (by rfl) ⟨2175576, by rfl⟩ : syracuseStep 5801537 = 4351153) B4351153
theorem B1697355 : Blo 1695548 1697355 := bstep (se 1 (by rfl) ⟨1273016, by rfl⟩ : syracuseStep 1697355 = 2546033) B2546033
theorem B188565077 : Blo 1695548 188565077 := bstep (se 8 (by rfl) ⟨1104873, by rfl⟩ : syracuseStep 188565077 = 2209747) B2209747
theorem B1697367 : Blo 1695548 1697367 := bstep (se 1 (by rfl) ⟨1273025, by rfl⟩ : syracuseStep 1697367 = 2546051) B2546051
theorem B3819095 : Blo 1695548 3819095 := bstep (se 1 (by rfl) ⟨2864321, by rfl⟩ : syracuseStep 3819095 = 5728643) B5728643
theorem B5727833 : Blo 1695548 5727833 := bstep (se 2 (by rfl) ⟨2147937, by rfl⟩ : syracuseStep 5727833 = 4295875) B4295875
theorem B1697387 : Blo 1695548 1697387 := bstep (se 1 (by rfl) ⟨1273040, by rfl⟩ : syracuseStep 1697387 = 2546081) B2546081
theorem B1697399 : Blo 1695548 1697399 := bstep (se 1 (by rfl) ⟨1273049, by rfl⟩ : syracuseStep 1697399 = 2546099) B2546099
theorem B6440579 : Blo 1695548 6440579 := bstep (se 1 (by rfl) ⟨4830434, by rfl⟩ : syracuseStep 6440579 = 9660869) B9660869
theorem B1697419 : Blo 1695548 1697419 := bstep (se 1 (by rfl) ⟨1273064, by rfl⟩ : syracuseStep 1697419 = 2546129) B2546129
theorem B6440593 : Blo 1695548 6440593 := bstep (se 2 (by rfl) ⟨2415222, by rfl⟩ : syracuseStep 6440593 = 4830445) B4830445
theorem B1697431 : Blo 1695548 1697431 := bstep (se 1 (by rfl) ⟨1273073, by rfl⟩ : syracuseStep 1697431 = 2546147) B2546147
theorem B3622553 : Blo 1695548 3622553 := bstep (se 2 (by rfl) ⟨1358457, by rfl⟩ : syracuseStep 3622553 = 2716915) B2716915
theorem B1697451 : Blo 1695548 1697451 := bstep (se 1 (by rfl) ⟨1273088, by rfl⟩ : syracuseStep 1697451 = 2546177) B2546177
theorem B1697463 : Blo 1695548 1697463 := bstep (se 1 (by rfl) ⟨1273097, by rfl⟩ : syracuseStep 1697463 = 2546195) B2546195
theorem B1697483 : Blo 1695548 1697483 := bstep (se 1 (by rfl) ⟨1273112, by rfl⟩ : syracuseStep 1697483 = 2546225) B2546225
theorem B1697495 : Blo 1695548 1697495 := bstep (se 1 (by rfl) ⟨1273121, by rfl⟩ : syracuseStep 1697495 = 2546243) B2546243
theorem B7243481 : Blo 1695548 7243481 := bstep (se 2 (by rfl) ⟨2716305, by rfl⟩ : syracuseStep 7243481 = 5432611) B5432611
theorem B1697515 : Blo 1695548 1697515 := bstep (se 1 (by rfl) ⟨1273136, by rfl⟩ : syracuseStep 1697515 = 2546273) B2546273
theorem B1697527 : Blo 1695548 1697527 := bstep (se 1 (by rfl) ⟨1273145, by rfl⟩ : syracuseStep 1697527 = 2546291) B2546291
theorem B3819275 : Blo 1695548 3819275 := bstep (se 1 (by rfl) ⟨2864456, by rfl⟩ : syracuseStep 3819275 = 5728913) B5728913
theorem B1697547 : Blo 1695548 1697547 := bstep (se 1 (by rfl) ⟨1273160, by rfl⟩ : syracuseStep 1697547 = 2546321) B2546321
theorem B6874903 : Blo 1695548 6874903 := bstep (se 1 (by rfl) ⟨5156177, by rfl⟩ : syracuseStep 6874903 = 10312355) B10312355
theorem B3221299 : Blo 1695548 3221299 := bstep (se 1 (by rfl) ⟨2415974, by rfl⟩ : syracuseStep 3221299 = 4831949) B4831949
theorem B3819329 : Blo 1695548 3819329 := bstep (se 2 (by rfl) ⟨1432248, by rfl⟩ : syracuseStep 3819329 = 2864497) B2864497
theorem B4294579 : Blo 1695548 4294579 := bstep (se 1 (by rfl) ⟨3220934, by rfl⟩ : syracuseStep 4294579 = 6441869) B6441869
theorem B6440897 : Blo 1695548 6440897 := bstep (se 2 (by rfl) ⟨2415336, by rfl⟩ : syracuseStep 6440897 = 4830673) B4830673
theorem B1935319 : Blo 1695548 1935319 := bstep (se 1 (by rfl) ⟨1451489, by rfl⟩ : syracuseStep 1935319 = 2902979) B2902979
theorem B6113303 : Blo 1695548 6113303 := bstep (se 1 (by rfl) ⟨4584977, by rfl⟩ : syracuseStep 6113303 = 9169955) B9169955
theorem B3221527 : Blo 1695548 3221527 := bstep (se 1 (by rfl) ⟨2416145, by rfl⟩ : syracuseStep 3221527 = 4832291) B4832291
theorem B3622963 : Blo 1695548 3622963 := bstep (se 1 (by rfl) ⟨2717222, by rfl⟩ : syracuseStep 3622963 = 5434445) B5434445
theorem B4294721 : Blo 1695548 4294721 := bstep (se 2 (by rfl) ⟨1610520, by rfl⟩ : syracuseStep 4294721 = 3221041) B3221041
theorem B5433419 : Blo 1695548 5433419 := bstep (se 1 (by rfl) ⟨4075064, by rfl⟩ : syracuseStep 5433419 = 8150129) B8150129
theorem B2148439 : Blo 1695548 2148439 := bstep (se 1 (by rfl) ⟨1611329, by rfl⟩ : syracuseStep 2148439 = 3222659) B3222659
theorem B3221633 : Blo 1695548 3221633 := bstep (se 2 (by rfl) ⟨1208112, by rfl⟩ : syracuseStep 3221633 = 2416225) B2416225
theorem B3098839 : Blo 1695548 3098839 := bstep (se 1 (by rfl) ⟨2324129, by rfl⟩ : syracuseStep 3098839 = 4648259) B4648259
theorem B2615513 : Blo 1695548 2615513 := bstep (se 2 (by rfl) ⟨980817, by rfl⟩ : syracuseStep 2615513 = 1961635) B1961635
theorem B3868939 : Blo 1695548 3868939 := bstep (se 1 (by rfl) ⟨2901704, by rfl⟩ : syracuseStep 3868939 = 5803409) B5803409
theorem B5728535 : Blo 1695548 5728535 := bstep (se 1 (by rfl) ⟨4296401, by rfl⟩ : syracuseStep 5728535 = 8592803) B8592803
theorem B3221785 : Blo 1695548 3221785 := bstep (se 2 (by rfl) ⟨1208169, by rfl⟩ : syracuseStep 3221785 = 2416339) B2416339
theorem B2861399 : Blo 1695548 2861399 := bstep (se 1 (by rfl) ⟨2146049, by rfl⟩ : syracuseStep 2861399 = 4292099) B4292099
theorem B4073921 : Blo 1695548 4073921 := bstep (se 2 (by rfl) ⟨1527720, by rfl⟩ : syracuseStep 4073921 = 3055441) B3055441
theorem B2861527 : Blo 1695548 2861527 := bstep (se 1 (by rfl) ⟨2146145, by rfl⟩ : syracuseStep 2861527 = 4292291) B4292291
theorem B3623449 : Blo 1695548 3623449 := bstep (se 2 (by rfl) ⟨1358793, by rfl⟩ : syracuseStep 3623449 = 2717587) B2717587
theorem B3263063 : Blo 1695548 3263063 := bstep (se 1 (by rfl) ⟨2447297, by rfl⟩ : syracuseStep 3263063 = 4894595) B4894595
theorem B6441565 : Blo 1695548 6441565 := bstep (se 3 (by rfl) ⟨1207793, by rfl⟩ : syracuseStep 6441565 = 2415587) B2415587
theorem B5434073 : Blo 1695548 5434073 := bstep (se 2 (by rfl) ⟨2037777, by rfl⟩ : syracuseStep 5434073 = 4075555) B4075555
theorem B5729075 : Blo 1695548 5729075 := bstep (se 1 (by rfl) ⟨4296806, by rfl⟩ : syracuseStep 5729075 = 8593613) B8593613
theorem B12389213 : Blo 1695548 12389213 := bstep (se 3 (by rfl) ⟨2322977, by rfl⟩ : syracuseStep 12389213 = 4645955) B4645955
theorem B7244747 : Blo 1695548 7244747 := bstep (se 1 (by rfl) ⟨5433560, by rfl⟩ : syracuseStep 7244747 = 10867121) B10867121
theorem B2862155 : Blo 1695548 2862155 := bstep (se 1 (by rfl) ⟨2146616, by rfl⟩ : syracuseStep 2862155 = 4293233) B4293233
theorem B3673163 : Blo 1695548 3673163 := bstep (se 1 (by rfl) ⟨2754872, by rfl⟩ : syracuseStep 3673163 = 5509745) B5509745
theorem B9661619 : Blo 1695548 9661619 := bstep (se 1 (by rfl) ⟨7246214, by rfl⟩ : syracuseStep 9661619 = 14492429) B14492429
theorem B4074689 : Blo 1695548 4074689 := bstep (se 2 (by rfl) ⟨1528008, by rfl⟩ : syracuseStep 4074689 = 3056017) B3056017
theorem B2862283 : Blo 1695548 2862283 := bstep (se 1 (by rfl) ⟨2146712, by rfl⟩ : syracuseStep 2862283 = 4293425) B4293425
theorem B3624193 : Blo 1695548 3624193 := bstep (se 2 (by rfl) ⟨1359072, by rfl⟩ : syracuseStep 3624193 = 2718145) B2718145
theorem B4295987 : Blo 1695548 4295987 := bstep (se 1 (by rfl) ⟨3221990, by rfl⟩ : syracuseStep 4295987 = 6443981) B6443981
theorem B7245121 : Blo 1695548 7245121 := bstep (se 2 (by rfl) ⟨2716920, by rfl⟩ : syracuseStep 7245121 = 5433841) B5433841
theorem B2862425 : Blo 1695548 2862425 := bstep (se 2 (by rfl) ⟨1073409, by rfl⟩ : syracuseStep 2862425 = 2146819) B2146819
theorem B10874243 : Blo 1695548 10874243 := bstep (se 1 (by rfl) ⟨8155682, by rfl⟩ : syracuseStep 10874243 = 16311365) B16311365
theorem B2862553 : Blo 1695548 2862553 := bstep (se 2 (by rfl) ⟨1073457, by rfl⟩ : syracuseStep 2862553 = 2146915) B2146915
theorem B7245463 : Blo 1695548 7245463 := bstep (se 1 (by rfl) ⟨5434097, by rfl⟩ : syracuseStep 7245463 = 10868195) B10868195
theorem B5435201 : Blo 1695548 5435201 := bstep (se 2 (by rfl) ⟨2038200, by rfl⟩ : syracuseStep 5435201 = 4076401) B4076401
theorem B2543435 : Blo 1695548 2543435 := bstep (se 1 (by rfl) ⟨1907576, by rfl⟩ : syracuseStep 2543435 = 3815153) B3815153
theorem B4296523 : Blo 1695548 4296523 := bstep (se 1 (by rfl) ⟨3222392, by rfl⟩ : syracuseStep 4296523 = 6444785) B6444785
theorem B2543447 : Blo 1695548 2543447 := bstep (se 1 (by rfl) ⟨1907585, by rfl⟩ : syracuseStep 2543447 = 3815171) B3815171
theorem B6442841 : Blo 1695548 6442841 := bstep (se 2 (by rfl) ⟨2416065, by rfl⟩ : syracuseStep 6442841 = 4832131) B4832131
theorem B2543513 : Blo 1695548 2543513 := bstep (se 2 (by rfl) ⟨953817, by rfl⟩ : syracuseStep 2543513 = 1907635) B1907635
theorem B4296665 : Blo 1695548 4296665 := bstep (se 2 (by rfl) ⟨1611249, by rfl⟩ : syracuseStep 4296665 = 3222499) B3222499
theorem B2543627 : Blo 1695548 2543627 := bstep (se 1 (by rfl) ⟨1907720, by rfl⟩ : syracuseStep 2543627 = 3815441) B3815441
theorem B2543639 : Blo 1695548 2543639 := bstep (se 1 (by rfl) ⟨1907729, by rfl⟩ : syracuseStep 2543639 = 3815459) B3815459
theorem B2863127 : Blo 1695548 2863127 := bstep (se 1 (by rfl) ⟨2147345, by rfl⟩ : syracuseStep 2863127 = 4294691) B4294691
theorem B12890177 : Blo 1695548 12890177 := bstep (se 2 (by rfl) ⟨4833816, by rfl⟩ : syracuseStep 12890177 = 9667633) B9667633
theorem B2543705 : Blo 1695548 2543705 := bstep (se 2 (by rfl) ⟨953889, by rfl⟩ : syracuseStep 2543705 = 1907779) B1907779
theorem B2863255 : Blo 1695548 2863255 := bstep (se 1 (by rfl) ⟨2147441, by rfl⟩ : syracuseStep 2863255 = 4294883) B4294883
theorem B18346135 : Blo 1695548 18346135 := bstep (se 1 (by rfl) ⟨13759601, by rfl⟩ : syracuseStep 18346135 = 27519203) B27519203
theorem B7844033 : Blo 1695548 7844033 := bstep (se 2 (by rfl) ⟨2941512, by rfl⟩ : syracuseStep 7844033 = 5883025) B5883025
theorem B2543819 : Blo 1695548 2543819 := bstep (se 1 (by rfl) ⟨1907864, by rfl⟩ : syracuseStep 2543819 = 3815729) B3815729
theorem B2543831 : Blo 1695548 2543831 := bstep (se 1 (by rfl) ⟨1907873, by rfl⟩ : syracuseStep 2543831 = 3815747) B3815747
theorem B3625175 : Blo 1695548 3625175 := bstep (se 1 (by rfl) ⟨2718881, by rfl⟩ : syracuseStep 3625175 = 5437763) B5437763
theorem B2543897 : Blo 1695548 2543897 := bstep (se 2 (by rfl) ⟨953961, by rfl⟩ : syracuseStep 2543897 = 1907923) B1907923
theorem B15470941 : Blo 1695548 15470941 := bstep (se 3 (by rfl) ⟨2900801, by rfl⟩ : syracuseStep 15470941 = 5801603) B5801603
theorem B2544011 : Blo 1695548 2544011 := bstep (se 1 (by rfl) ⟨1908008, by rfl⟩ : syracuseStep 2544011 = 3816017) B3816017
theorem B2544023 : Blo 1695548 2544023 := bstep (se 1 (by rfl) ⟨1908017, by rfl⟩ : syracuseStep 2544023 = 3816035) B3816035
theorem B5157323 : Blo 1695548 5157323 := bstep (se 1 (by rfl) ⟨3867992, by rfl⟩ : syracuseStep 5157323 = 7735985) B7735985
theorem B2544089 : Blo 1695548 2544089 := bstep (se 2 (by rfl) ⟨954033, by rfl⟩ : syracuseStep 2544089 = 1908067) B1908067
theorem B2544203 : Blo 1695548 2544203 := bstep (se 1 (by rfl) ⟨1908152, by rfl⟩ : syracuseStep 2544203 = 3816305) B3816305
theorem B2544215 : Blo 1695548 2544215 := bstep (se 1 (by rfl) ⟨1908161, by rfl⟩ : syracuseStep 2544215 = 3816323) B3816323
theorem B2716249 : Blo 1695548 2716249 := bstep (se 2 (by rfl) ⟨1018593, by rfl⟩ : syracuseStep 2716249 = 2037187) B2037187
theorem B9663077 : Blo 1695548 9663077 := bstep (se 4 (by rfl) ⟨905913, by rfl⟩ : syracuseStep 9663077 = 1811827) B1811827
theorem B2544281 : Blo 1695548 2544281 := bstep (se 2 (by rfl) ⟨954105, by rfl⟩ : syracuseStep 2544281 = 1908211) B1908211
theorem B5804723 : Blo 1695548 5804723 := bstep (se 1 (by rfl) ⟨4353542, by rfl⟩ : syracuseStep 5804723 = 8707085) B8707085
theorem B2544395 : Blo 1695548 2544395 := bstep (se 1 (by rfl) ⟨1908296, by rfl⟩ : syracuseStep 2544395 = 3816593) B3816593
theorem B2863883 : Blo 1695548 2863883 := bstep (se 1 (by rfl) ⟨2147912, by rfl⟩ : syracuseStep 2863883 = 4295825) B4295825
theorem B14496529 : Blo 1695548 14496529 := bstep (se 2 (by rfl) ⟨5436198, by rfl⟩ : syracuseStep 14496529 = 10872397) B10872397
theorem B2544407 : Blo 1695548 2544407 := bstep (se 1 (by rfl) ⟨1908305, by rfl⟩ : syracuseStep 2544407 = 3816611) B3816611
theorem B2716505 : Blo 1695548 2716505 := bstep (se 2 (by rfl) ⟨1018689, by rfl⟩ : syracuseStep 2716505 = 2037379) B2037379
theorem B2544473 : Blo 1695548 2544473 := bstep (se 2 (by rfl) ⟨954177, by rfl⟩ : syracuseStep 2544473 = 1908355) B1908355
theorem B6116185 : Blo 1695548 6116185 := bstep (se 2 (by rfl) ⟨2293569, by rfl⟩ : syracuseStep 6116185 = 4587139) B4587139
theorem B5722973 : Blo 1695548 5722973 := bstep (se 3 (by rfl) ⟨1073057, by rfl⟩ : syracuseStep 5722973 = 2146115) B2146115
theorem B8590211 : Blo 1695548 8590211 := bstep (se 1 (by rfl) ⟨6442658, by rfl⟩ : syracuseStep 8590211 = 12885317) B12885317
theorem B2864011 : Blo 1695548 2864011 := bstep (se 1 (by rfl) ⟨2148008, by rfl⟩ : syracuseStep 2864011 = 4296017) B4296017
theorem B2544587 : Blo 1695548 2544587 := bstep (se 1 (by rfl) ⟨1908440, by rfl⟩ : syracuseStep 2544587 = 3816881) B3816881
theorem B2544599 : Blo 1695548 2544599 := bstep (se 1 (by rfl) ⟨1908449, by rfl⟩ : syracuseStep 2544599 = 3816899) B3816899
theorem B2544665 : Blo 1695548 2544665 := bstep (se 2 (by rfl) ⟨954249, by rfl⟩ : syracuseStep 2544665 = 1908499) B1908499
theorem B2864153 : Blo 1695548 2864153 := bstep (se 2 (by rfl) ⟨1074057, by rfl⟩ : syracuseStep 2864153 = 2148115) B2148115
theorem B14496803 : Blo 1695548 14496803 := bstep (se 1 (by rfl) ⟨10872602, by rfl⟩ : syracuseStep 14496803 = 21745205) B21745205
theorem B18600995 : Blo 1695548 18600995 := bstep (se 1 (by rfl) ⟨13950746, by rfl⟩ : syracuseStep 18600995 = 27901493) B27901493
theorem B9663533 : Blo 1695548 9663533 := bstep (se 3 (by rfl) ⟨1811912, by rfl⟩ : syracuseStep 9663533 = 3623825) B3623825
theorem B6116417 : Blo 1695548 6116417 := bstep (se 2 (by rfl) ⟨2293656, by rfl⟩ : syracuseStep 6116417 = 4587313) B4587313
theorem B2544779 : Blo 1695548 2544779 := bstep (se 1 (by rfl) ⟨1908584, by rfl⟩ : syracuseStep 2544779 = 3817169) B3817169
theorem B2544791 : Blo 1695548 2544791 := bstep (se 1 (by rfl) ⟨1908593, by rfl⟩ : syracuseStep 2544791 = 3817187) B3817187
theorem B2864281 : Blo 1695548 2864281 := bstep (se 2 (by rfl) ⟨1074105, by rfl⟩ : syracuseStep 2864281 = 2148211) B2148211
theorem B2544857 : Blo 1695548 2544857 := bstep (se 2 (by rfl) ⟨954321, by rfl⟩ : syracuseStep 2544857 = 1908643) B1908643
theorem B2544971 : Blo 1695548 2544971 := bstep (se 1 (by rfl) ⟨1908728, by rfl⟩ : syracuseStep 2544971 = 3817457) B3817457
theorem B2544983 : Blo 1695548 2544983 := bstep (se 1 (by rfl) ⟨1908737, by rfl⟩ : syracuseStep 2544983 = 3817475) B3817475
theorem B2545049 : Blo 1695548 2545049 := bstep (se 2 (by rfl) ⟨954393, by rfl⟩ : syracuseStep 2545049 = 1908787) B1908787
theorem B6444467 : Blo 1695548 6444467 := bstep (se 1 (by rfl) ⟨4833350, by rfl⟩ : syracuseStep 6444467 = 9666701) B9666701
theorem B6444481 : Blo 1695548 6444481 := bstep (se 2 (by rfl) ⟨2416680, by rfl⟩ : syracuseStep 6444481 = 4833361) B4833361
theorem B26121689 : Blo 1695548 26121689 := bstep (se 2 (by rfl) ⟨9795633, by rfl⟩ : syracuseStep 26121689 = 19591267) B19591267
theorem B4077017 : Blo 1695548 4077017 := bstep (se 2 (by rfl) ⟨1528881, by rfl⟩ : syracuseStep 4077017 = 3057763) B3057763
theorem B2545163 : Blo 1695548 2545163 := bstep (se 1 (by rfl) ⟨1908872, by rfl⟩ : syracuseStep 2545163 = 3817745) B3817745
theorem B2545175 : Blo 1695548 2545175 := bstep (se 1 (by rfl) ⟨1908881, by rfl⟩ : syracuseStep 2545175 = 3817763) B3817763
theorem B2545241 : Blo 1695548 2545241 := bstep (se 2 (by rfl) ⟨954465, by rfl⟩ : syracuseStep 2545241 = 1908931) B1908931
theorem B3815027 : Blo 1695548 3815027 := bstep (se 1 (by rfl) ⟨2861270, by rfl⟩ : syracuseStep 3815027 = 5722541) B5722541
theorem B3815063 : Blo 1695548 3815063 := bstep (se 1 (by rfl) ⟨2861297, by rfl⟩ : syracuseStep 3815063 = 5722595) B5722595
theorem B2545355 : Blo 1695548 2545355 := bstep (se 1 (by rfl) ⟨1909016, by rfl⟩ : syracuseStep 2545355 = 3818033) B3818033
theorem B2545367 : Blo 1695548 2545367 := bstep (se 1 (by rfl) ⟨1909025, by rfl⟩ : syracuseStep 2545367 = 3818051) B3818051
theorem B9795289 : Blo 1695548 9795289 := bstep (se 2 (by rfl) ⟨3673233, by rfl⟩ : syracuseStep 9795289 = 7346467) B7346467
theorem B9664217 : Blo 1695548 9664217 := bstep (se 2 (by rfl) ⟨3624081, by rfl⟩ : syracuseStep 9664217 = 7248163) B7248163
theorem B5805847 : Blo 1695548 5805847 := bstep (se 1 (by rfl) ⟨4354385, by rfl⟩ : syracuseStep 5805847 = 8708771) B8708771
theorem B2545433 : Blo 1695548 2545433 := bstep (se 2 (by rfl) ⟨954537, by rfl⟩ : syracuseStep 2545433 = 1909075) B1909075
theorem B3815243 : Blo 1695548 3815243 := bstep (se 1 (by rfl) ⟨2861432, by rfl⟩ : syracuseStep 3815243 = 5722865) B5722865
theorem B5437277 : Blo 1695548 5437277 := bstep (se 3 (by rfl) ⟨1019489, by rfl⟩ : syracuseStep 5437277 = 2038979) B2038979
theorem B3815297 : Blo 1695548 3815297 := bstep (se 2 (by rfl) ⟨1430736, by rfl⟩ : syracuseStep 3815297 = 2861473) B2861473
theorem B2545547 : Blo 1695548 2545547 := bstep (se 1 (by rfl) ⟨1909160, by rfl⟩ : syracuseStep 2545547 = 3818321) B3818321
theorem B2545559 : Blo 1695548 2545559 := bstep (se 1 (by rfl) ⟨1909169, by rfl⟩ : syracuseStep 2545559 = 3818339) B3818339
theorem B16299953 : Blo 1695548 16299953 := bstep (se 2 (by rfl) ⟨6112482, by rfl⟩ : syracuseStep 16299953 = 12224965) B12224965
theorem B2414539 : Blo 1695548 2414539 := bstep (se 1 (by rfl) ⟨1810904, by rfl⟩ : syracuseStep 2414539 = 3621809) B3621809
theorem B5724107 : Blo 1695548 5724107 := bstep (se 1 (by rfl) ⟨4293080, by rfl⟩ : syracuseStep 5724107 = 8586161) B8586161
theorem B2414551 : Blo 1695548 2414551 := bstep (se 1 (by rfl) ⟨1810913, by rfl⟩ : syracuseStep 2414551 = 3621827) B3621827
theorem B2545625 : Blo 1695548 2545625 := bstep (se 2 (by rfl) ⟨954609, by rfl⟩ : syracuseStep 2545625 = 1909219) B1909219
theorem B8157145 : Blo 1695548 8157145 := bstep (se 2 (by rfl) ⟨3058929, by rfl⟩ : syracuseStep 8157145 = 6117859) B6117859
theorem B4962269 : Blo 1695548 4962269 := bstep (se 3 (by rfl) ⟨930425, by rfl⟩ : syracuseStep 4962269 = 1860851) B1860851
theorem B2545739 : Blo 1695548 2545739 := bstep (se 1 (by rfl) ⟨1909304, by rfl⟩ : syracuseStep 2545739 = 3818609) B3818609
theorem B2545751 : Blo 1695548 2545751 := bstep (se 1 (by rfl) ⟨1909313, by rfl⟩ : syracuseStep 2545751 = 3818627) B3818627
theorem B3815513 : Blo 1695548 3815513 := bstep (se 2 (by rfl) ⟨1430817, by rfl⟩ : syracuseStep 3815513 = 2861635) B2861635
theorem B2545817 : Blo 1695548 2545817 := bstep (se 2 (by rfl) ⟨954681, by rfl⟩ : syracuseStep 2545817 = 1909363) B1909363
theorem B3815603 : Blo 1695548 3815603 := bstep (se 1 (by rfl) ⟨2861702, by rfl⟩ : syracuseStep 3815603 = 5723405) B5723405
theorem B3815639 : Blo 1695548 3815639 := bstep (se 1 (by rfl) ⟨2861729, by rfl⟩ : syracuseStep 3815639 = 5723459) B5723459
theorem B5724377 : Blo 1695548 5724377 := bstep (se 2 (by rfl) ⟨2146641, by rfl⟩ : syracuseStep 5724377 = 4293283) B4293283
theorem B2545931 : Blo 1695548 2545931 := bstep (se 1 (by rfl) ⟨1909448, by rfl⟩ : syracuseStep 2545931 = 3818897) B3818897
theorem B2545943 : Blo 1695548 2545943 := bstep (se 1 (by rfl) ⟨1909457, by rfl⟩ : syracuseStep 2545943 = 3818915) B3818915
theorem B22042925 : Blo 1695548 22042925 := bstep (se 3 (by rfl) ⟨4133048, by rfl⟩ : syracuseStep 22042925 = 8266097) B8266097
theorem B2546009 : Blo 1695548 2546009 := bstep (se 2 (by rfl) ⟨954753, by rfl⟩ : syracuseStep 2546009 = 1909507) B1909507
theorem B3815819 : Blo 1695548 3815819 := bstep (se 1 (by rfl) ⟨2861864, by rfl⟩ : syracuseStep 3815819 = 5723729) B5723729
theorem B3815873 : Blo 1695548 3815873 := bstep (se 2 (by rfl) ⟨1430952, by rfl⟩ : syracuseStep 3815873 = 2861905) B2861905
theorem B2546123 : Blo 1695548 2546123 := bstep (se 1 (by rfl) ⟨1909592, by rfl⟩ : syracuseStep 2546123 = 3819185) B3819185
theorem B2546135 : Blo 1695548 2546135 := bstep (se 1 (by rfl) ⟨1909601, by rfl⟩ : syracuseStep 2546135 = 3819203) B3819203
theorem B3439115 : Blo 1695548 3439115 := bstep (se 1 (by rfl) ⟨2579336, by rfl⟩ : syracuseStep 3439115 = 5158673) B5158673
theorem B2546201 : Blo 1695548 2546201 := bstep (se 2 (by rfl) ⟨954825, by rfl⟩ : syracuseStep 2546201 = 1909651) B1909651
theorem B2546315 : Blo 1695548 2546315 := bstep (se 1 (by rfl) ⟨1909736, by rfl⟩ : syracuseStep 2546315 = 3819473) B3819473
theorem B3816089 : Blo 1695548 3816089 := bstep (se 2 (by rfl) ⟨1431033, by rfl⟩ : syracuseStep 3816089 = 2862067) B2862067
theorem B21740237 : Blo 1695548 21740237 := bstep (se 3 (by rfl) ⟨4076294, by rfl⟩ : syracuseStep 21740237 = 8152589) B8152589
theorem B5438173 : Blo 1695548 5438173 := bstep (se 3 (by rfl) ⟨1019657, by rfl⟩ : syracuseStep 5438173 = 2039315) B2039315
theorem B3816179 : Blo 1695548 3816179 := bstep (se 1 (by rfl) ⟨2862134, by rfl⟩ : syracuseStep 3816179 = 5724269) B5724269
theorem B3816215 : Blo 1695548 3816215 := bstep (se 1 (by rfl) ⟨2862161, by rfl⟩ : syracuseStep 3816215 = 5724323) B5724323
theorem B4832075 : Blo 1695548 4832075 := bstep (se 1 (by rfl) ⟨3624056, by rfl⟩ : syracuseStep 4832075 = 7248113) B7248113
theorem B1907563 : Blo 1695548 1907563 := bstep (se 1 (by rfl) ⟨1430672, by rfl⟩ : syracuseStep 1907563 = 2861345) B2861345
theorem B5725079 : Blo 1695548 5725079 := bstep (se 1 (by rfl) ⟨4293809, by rfl⟩ : syracuseStep 5725079 = 8587619) B8587619
theorem B3816395 : Blo 1695548 3816395 := bstep (se 1 (by rfl) ⟨2862296, by rfl⟩ : syracuseStep 3816395 = 5724593) B5724593
theorem B1907671 : Blo 1695548 1907671 := bstep (se 1 (by rfl) ⟨1430753, by rfl⟩ : syracuseStep 1907671 = 2861507) B2861507
theorem B3439577 : Blo 1695548 3439577 := bstep (se 2 (by rfl) ⟨1289841, by rfl⟩ : syracuseStep 3439577 = 2579683) B2579683
theorem B3816449 : Blo 1695548 3816449 := bstep (se 2 (by rfl) ⟨1431168, by rfl⟩ : syracuseStep 3816449 = 2862337) B2862337
theorem B2448407 : Blo 1695548 2448407 := bstep (se 1 (by rfl) ⟨1836305, by rfl⟩ : syracuseStep 2448407 = 3672611) B3672611
theorem B10869835 : Blo 1695548 10869835 := bstep (se 1 (by rfl) ⟨8152376, by rfl⟩ : syracuseStep 10869835 = 16304753) B16304753
theorem B6437981 : Blo 1695548 6437981 := bstep (se 3 (by rfl) ⟨1207121, by rfl⟩ : syracuseStep 6437981 = 2414243) B2414243
theorem B1907851 : Blo 1695548 1907851 := bstep (se 1 (by rfl) ⟨1430888, by rfl⟩ : syracuseStep 1907851 = 2861777) B2861777
theorem B3816665 : Blo 1695548 3816665 := bstep (se 2 (by rfl) ⟨1431249, by rfl⟩ : syracuseStep 3816665 = 2862499) B2862499
theorem B4832473 : Blo 1695548 4832473 := bstep (se 2 (by rfl) ⟨1812177, by rfl⟩ : syracuseStep 4832473 = 3624355) B3624355
theorem B1907959 : Blo 1695548 1907959 := bstep (se 1 (by rfl) ⟨1430969, by rfl⟩ : syracuseStep 1907959 = 2861939) B2861939
theorem B3816755 : Blo 1695548 3816755 := bstep (se 1 (by rfl) ⟨2862566, by rfl⟩ : syracuseStep 3816755 = 5725133) B5725133
theorem B3816791 : Blo 1695548 3816791 := bstep (se 1 (by rfl) ⟨2862593, by rfl⟩ : syracuseStep 3816791 = 5725187) B5725187
theorem B8584541 : Blo 1695548 8584541 := bstep (se 3 (by rfl) ⟨1609601, by rfl⟩ : syracuseStep 8584541 = 3219203) B3219203
theorem B9657701 : Blo 1695548 9657701 := bstep (se 4 (by rfl) ⟨905409, by rfl⟩ : syracuseStep 9657701 = 1810819) B1810819
theorem B1908139 : Blo 1695548 1908139 := bstep (se 1 (by rfl) ⟨1431104, by rfl⟩ : syracuseStep 1908139 = 2862209) B2862209
theorem B5725619 : Blo 1695548 5725619 := bstep (se 1 (by rfl) ⟨4294214, by rfl⟩ : syracuseStep 5725619 = 8588429) B8588429
theorem B3816971 : Blo 1695548 3816971 := bstep (se 1 (by rfl) ⟨2862728, by rfl⟩ : syracuseStep 3816971 = 5725457) B5725457
theorem B1908247 : Blo 1695548 1908247 := bstep (se 1 (by rfl) ⟨1431185, by rfl⟩ : syracuseStep 1908247 = 2862371) B2862371
theorem B3817025 : Blo 1695548 3817025 := bstep (se 2 (by rfl) ⟨1431384, by rfl⟩ : syracuseStep 3817025 = 2862769) B2862769
theorem B5160523 : Blo 1695548 5160523 := bstep (se 1 (by rfl) ⟨3870392, by rfl⟩ : syracuseStep 5160523 = 7740785) B7740785
theorem B2145943 : Blo 1695548 2145943 := bstep (se 1 (by rfl) ⟨1609457, by rfl⟩ : syracuseStep 2145943 = 3218915) B3218915
theorem B3219097 : Blo 1695548 3219097 := bstep (se 2 (by rfl) ⟨1207161, by rfl⟩ : syracuseStep 3219097 = 2414323) B2414323
theorem B5725889 : Blo 1695548 5725889 := bstep (se 2 (by rfl) ⟨2147208, by rfl⟩ : syracuseStep 5725889 = 4294417) B4294417
theorem B1908427 : Blo 1695548 1908427 := bstep (se 1 (by rfl) ⟨1431320, by rfl⟩ : syracuseStep 1908427 = 2862641) B2862641
theorem B15695633 : Blo 1695548 15695633 := bstep (se 2 (by rfl) ⟨5885862, by rfl⟩ : syracuseStep 15695633 = 11771725) B11771725
theorem B3817241 : Blo 1695548 3817241 := bstep (se 2 (by rfl) ⟨1431465, by rfl⟩ : syracuseStep 3817241 = 2862931) B2862931
theorem B1908535 : Blo 1695548 1908535 := bstep (se 1 (by rfl) ⟨1431401, by rfl⟩ : syracuseStep 1908535 = 2862803) B2862803
theorem B1695563 : Blo 1695548 1695563 := bstep (se 1 (by rfl) ⟨1271672, by rfl⟩ : syracuseStep 1695563 = 2543345) B2543345
theorem B1695575 : Blo 1695548 1695575 := bstep (se 1 (by rfl) ⟨1271681, by rfl⟩ : syracuseStep 1695575 = 2543363) B2543363
theorem B1695595 : Blo 1695548 1695595 := bstep (se 1 (by rfl) ⟨1271696, by rfl⟩ : syracuseStep 1695595 = 2543393) B2543393
theorem B3817331 : Blo 1695548 3817331 := bstep (se 1 (by rfl) ⟨2862998, by rfl⟩ : syracuseStep 3817331 = 5725997) B5725997
theorem B1695607 : Blo 1695548 1695607 := bstep (se 1 (by rfl) ⟨1271705, by rfl⟩ : syracuseStep 1695607 = 2543411) B2543411
theorem B8150915 : Blo 1695548 8150915 := bstep (se 1 (by rfl) ⟨6113186, by rfl⟩ : syracuseStep 8150915 = 12226373) B12226373
theorem B1695627 : Blo 1695548 1695627 := bstep (se 1 (by rfl) ⟨1271720, by rfl⟩ : syracuseStep 1695627 = 2543441) B2543441
theorem B1695639 : Blo 1695548 1695639 := bstep (se 1 (by rfl) ⟨1271729, by rfl⟩ : syracuseStep 1695639 = 2543459) B2543459
theorem B3817367 : Blo 1695548 3817367 := bstep (se 1 (by rfl) ⟨2863025, by rfl⟩ : syracuseStep 3817367 = 5726051) B5726051
theorem B1695659 : Blo 1695548 1695659 := bstep (se 1 (by rfl) ⟨1271744, by rfl⟩ : syracuseStep 1695659 = 2543489) B2543489
theorem B7249837 : Blo 1695548 7249837 := bstep (se 3 (by rfl) ⟨1359344, by rfl⟩ : syracuseStep 7249837 = 2718689) B2718689
theorem B10321843 : Blo 1695548 10321843 := bstep (se 1 (by rfl) ⟨7741382, by rfl⟩ : syracuseStep 10321843 = 15482765) B15482765
theorem B1695671 : Blo 1695548 1695671 := bstep (se 1 (by rfl) ⟨1271753, by rfl⟩ : syracuseStep 1695671 = 2543507) B2543507
theorem B1695691 : Blo 1695548 1695691 := bstep (se 1 (by rfl) ⟨1271768, by rfl⟩ : syracuseStep 1695691 = 2543537) B2543537
theorem B1695703 : Blo 1695548 1695703 := bstep (se 1 (by rfl) ⟨1271777, by rfl⟩ : syracuseStep 1695703 = 2543555) B2543555
theorem B2416601 : Blo 1695548 2416601 := bstep (se 2 (by rfl) ⟨906225, by rfl⟩ : syracuseStep 2416601 = 1812451) B1812451
theorem B7167961 : Blo 1695548 7167961 := bstep (se 2 (by rfl) ⟨2687985, by rfl⟩ : syracuseStep 7167961 = 5375971) B5375971
theorem B1695723 : Blo 1695548 1695723 := bstep (se 1 (by rfl) ⟨1271792, by rfl⟩ : syracuseStep 1695723 = 2543585) B2543585
theorem B1908715 : Blo 1695548 1908715 := bstep (se 1 (by rfl) ⟨1431536, by rfl⟩ : syracuseStep 1908715 = 2863073) B2863073
theorem B1695735 : Blo 1695548 1695735 := bstep (se 1 (by rfl) ⟨1271801, by rfl⟩ : syracuseStep 1695735 = 2543603) B2543603
theorem B1695751 : Blo 1695548 1695751 := bstep (se 1 (by rfl) ⟨1271813, by rfl⟩ : syracuseStep 1695751 = 2543627) B2543627
theorem B6438923 : Blo 1695548 6438923 := bstep (se 1 (by rfl) ⟨4829192, by rfl⟩ : syracuseStep 6438923 = 9658385) B9658385
theorem B1695759 : Blo 1695548 1695759 := bstep (se 1 (by rfl) ⟨1271819, by rfl⟩ : syracuseStep 1695759 = 2543639) B2543639
theorem B1908751 : Blo 1695548 1908751 := bstep (se 1 (by rfl) ⟨1431563, by rfl⟩ : syracuseStep 1908751 = 2863127) B2863127
theorem B8593451 : Blo 1695548 8593451 := bstep (se 1 (by rfl) ⟨6445088, by rfl⟩ : syracuseStep 8593451 = 12890177) B12890177
theorem B1695803 : Blo 1695548 1695803 := bstep (se 1 (by rfl) ⟨1271852, by rfl⟩ : syracuseStep 1695803 = 2543705) B2543705
theorem B6529085 : Blo 1695548 6529085 := bstep (se 3 (by rfl) ⟨1224203, by rfl⟩ : syracuseStep 6529085 = 2448407) B2448407
theorem B1695879 : Blo 1695548 1695879 := bstep (se 1 (by rfl) ⟨1271909, by rfl⟩ : syracuseStep 1695879 = 2543819) B2543819
theorem B2146439 : Blo 1695548 2146439 := bstep (se 1 (by rfl) ⟨1609829, by rfl⟩ : syracuseStep 2146439 = 3219659) B3219659
theorem B1695887 : Blo 1695548 1695887 := bstep (se 1 (by rfl) ⟨1271915, by rfl⟩ : syracuseStep 1695887 = 2543831) B2543831
theorem B3817619 : Blo 1695548 3817619 := bstep (se 1 (by rfl) ⟨2863214, by rfl⟩ : syracuseStep 3817619 = 5726429) B5726429
theorem B1695931 : Blo 1695548 1695931 := bstep (se 1 (by rfl) ⟨1271948, by rfl⟩ : syracuseStep 1695931 = 2543897) B2543897
theorem B3817673 : Blo 1695548 3817673 := bstep (se 2 (by rfl) ⟨1431627, by rfl⟩ : syracuseStep 3817673 = 2863255) B2863255
theorem B24461513 : Blo 1695548 24461513 := bstep (se 2 (by rfl) ⟨9173067, by rfl⟩ : syracuseStep 24461513 = 18346135) B18346135
theorem B6971629 : Blo 1695548 6971629 := bstep (se 3 (by rfl) ⟨1307180, by rfl⟩ : syracuseStep 6971629 = 2614361) B2614361
theorem B1696007 : Blo 1695548 1696007 := bstep (se 1 (by rfl) ⟨1272005, by rfl⟩ : syracuseStep 1696007 = 2544011) B2544011
theorem B1696015 : Blo 1695548 1696015 := bstep (se 1 (by rfl) ⟨1272011, by rfl⟩ : syracuseStep 1696015 = 2544023) B2544023
theorem B1696059 : Blo 1695548 1696059 := bstep (se 1 (by rfl) ⟨1272044, by rfl⟩ : syracuseStep 1696059 = 2544089) B2544089
theorem B1696135 : Blo 1695548 1696135 := bstep (se 1 (by rfl) ⟨1272101, by rfl⟩ : syracuseStep 1696135 = 2544203) B2544203
theorem B1696143 : Blo 1695548 1696143 := bstep (se 1 (by rfl) ⟨1272107, by rfl⟩ : syracuseStep 1696143 = 2544215) B2544215
theorem B1696187 : Blo 1695548 1696187 := bstep (se 1 (by rfl) ⟨1272140, by rfl⟩ : syracuseStep 1696187 = 2544281) B2544281
theorem B8585675 : Blo 1695548 8585675 := bstep (se 1 (by rfl) ⟨6439256, by rfl⟩ : syracuseStep 8585675 = 12878513) B12878513
theorem B20627921 : Blo 1695548 20627921 := bstep (se 2 (by rfl) ⟨7735470, by rfl⟩ : syracuseStep 20627921 = 15470941) B15470941
theorem B4293121 : Blo 1695548 4293121 := bstep (se 2 (by rfl) ⟨1609920, by rfl⟩ : syracuseStep 4293121 = 3219841) B3219841
theorem B1696263 : Blo 1695548 1696263 := bstep (se 1 (by rfl) ⟨1272197, by rfl⟩ : syracuseStep 1696263 = 2544395) B2544395
theorem B1909255 : Blo 1695548 1909255 := bstep (se 1 (by rfl) ⟨1431941, by rfl⟩ : syracuseStep 1909255 = 2863883) B2863883
theorem B1696271 : Blo 1695548 1696271 := bstep (se 1 (by rfl) ⟨1272203, by rfl⟩ : syracuseStep 1696271 = 2544407) B2544407
theorem B1811003 : Blo 1695548 1811003 := bstep (se 1 (by rfl) ⟨1358252, by rfl⟩ : syracuseStep 1811003 = 2716505) B2716505
theorem B1696315 : Blo 1695548 1696315 := bstep (se 1 (by rfl) ⟨1272236, by rfl⟩ : syracuseStep 1696315 = 2544473) B2544473
theorem B9667133 : Blo 1695548 9667133 := bstep (se 3 (by rfl) ⟨1812587, by rfl⟩ : syracuseStep 9667133 = 3625175) B3625175
theorem B5726807 : Blo 1695548 5726807 := bstep (se 1 (by rfl) ⟨4295105, by rfl⟩ : syracuseStep 5726807 = 8590211) B8590211
theorem B1696391 : Blo 1695548 1696391 := bstep (se 1 (by rfl) ⟨1272293, by rfl⟩ : syracuseStep 1696391 = 2544587) B2544587
theorem B1696399 : Blo 1695548 1696399 := bstep (se 1 (by rfl) ⟨1272299, by rfl⟩ : syracuseStep 1696399 = 2544599) B2544599
theorem B1696443 : Blo 1695548 1696443 := bstep (se 1 (by rfl) ⟨1272332, by rfl⟩ : syracuseStep 1696443 = 2544665) B2544665
theorem B1909435 : Blo 1695548 1909435 := bstep (se 1 (by rfl) ⟨1432076, by rfl⟩ : syracuseStep 1909435 = 2864153) B2864153
theorem B32604889 : Blo 1695548 32604889 := bstep (se 2 (by rfl) ⟨12226833, by rfl⟩ : syracuseStep 32604889 = 24453667) B24453667
theorem B1696519 : Blo 1695548 1696519 := bstep (se 1 (by rfl) ⟨1272389, by rfl⟩ : syracuseStep 1696519 = 2544779) B2544779
theorem B8585999 : Blo 1695548 8585999 := bstep (se 1 (by rfl) ⟨6439499, by rfl⟩ : syracuseStep 8585999 = 12878999) B12878999
theorem B2147087 : Blo 1695548 2147087 := bstep (se 1 (by rfl) ⟨1610315, by rfl⟩ : syracuseStep 2147087 = 3220631) B3220631
theorem B1696527 : Blo 1695548 1696527 := bstep (se 1 (by rfl) ⟨1272395, by rfl⟩ : syracuseStep 1696527 = 2544791) B2544791
theorem B3621665 : Blo 1695548 3621665 := bstep (se 2 (by rfl) ⟨1358124, by rfl⟩ : syracuseStep 3621665 = 2716249) B2716249
theorem B1696571 : Blo 1695548 1696571 := bstep (se 1 (by rfl) ⟨1272428, by rfl⟩ : syracuseStep 1696571 = 2544857) B2544857
theorem B1696647 : Blo 1695548 1696647 := bstep (se 1 (by rfl) ⟨1272485, by rfl⟩ : syracuseStep 1696647 = 2544971) B2544971
theorem B3818375 : Blo 1695548 3818375 := bstep (se 1 (by rfl) ⟨2863781, by rfl⟩ : syracuseStep 3818375 = 5727563) B5727563
theorem B1696655 : Blo 1695548 1696655 := bstep (se 1 (by rfl) ⟨1272491, by rfl⟩ : syracuseStep 1696655 = 2544983) B2544983
theorem B1696699 : Blo 1695548 1696699 := bstep (se 1 (by rfl) ⟨1272524, by rfl⟩ : syracuseStep 1696699 = 2545049) B2545049
theorem B7250897 : Blo 1695548 7250897 := bstep (se 2 (by rfl) ⟨2719086, by rfl⟩ : syracuseStep 7250897 = 5438173) B5438173
theorem B1696775 : Blo 1695548 1696775 := bstep (se 1 (by rfl) ⟨1272581, by rfl⟩ : syracuseStep 1696775 = 2545163) B2545163
theorem B1696783 : Blo 1695548 1696783 := bstep (se 1 (by rfl) ⟨1272587, by rfl⟩ : syracuseStep 1696783 = 2545175) B2545175
theorem B20628503 : Blo 1695548 20628503 := bstep (se 1 (by rfl) ⟨15471377, by rfl⟩ : syracuseStep 20628503 = 30942755) B30942755
theorem B3867691 : Blo 1695548 3867691 := bstep (se 1 (by rfl) ⟨2900768, by rfl⟩ : syracuseStep 3867691 = 5801537) B5801537
theorem B1696827 : Blo 1695548 1696827 := bstep (se 1 (by rfl) ⟨1272620, by rfl⟩ : syracuseStep 1696827 = 2545241) B2545241
theorem B3818555 : Blo 1695548 3818555 := bstep (se 1 (by rfl) ⟨2863916, by rfl⟩ : syracuseStep 3818555 = 5727833) B5727833
theorem B5727293 : Blo 1695548 5727293 := bstep (se 3 (by rfl) ⟨1073867, by rfl⟩ : syracuseStep 5727293 = 2147735) B2147735
theorem B4293719 : Blo 1695548 4293719 := bstep (se 1 (by rfl) ⟨3220289, by rfl⟩ : syracuseStep 4293719 = 6440579) B6440579
theorem B1696903 : Blo 1695548 1696903 := bstep (se 1 (by rfl) ⟨1272677, by rfl⟩ : syracuseStep 1696903 = 2545355) B2545355
theorem B1696911 : Blo 1695548 1696911 := bstep (se 1 (by rfl) ⟨1272683, by rfl⟩ : syracuseStep 1696911 = 2545367) B2545367
theorem B3818681 : Blo 1695548 3818681 := bstep (se 2 (by rfl) ⟨1432005, by rfl⟩ : syracuseStep 3818681 = 2864011) B2864011
theorem B1696955 : Blo 1695548 1696955 := bstep (se 1 (by rfl) ⟨1272716, by rfl⟩ : syracuseStep 1696955 = 2545433) B2545433
theorem B1697031 : Blo 1695548 1697031 := bstep (se 1 (by rfl) ⟨1272773, by rfl⟩ : syracuseStep 1697031 = 2545547) B2545547
theorem B1697039 : Blo 1695548 1697039 := bstep (se 1 (by rfl) ⟨1272779, by rfl⟩ : syracuseStep 1697039 = 2545559) B2545559
theorem B4293931 : Blo 1695548 4293931 := bstep (se 1 (by rfl) ⟨3220448, by rfl⟩ : syracuseStep 4293931 = 6440897) B6440897
theorem B1697083 : Blo 1695548 1697083 := bstep (se 1 (by rfl) ⟨1272812, by rfl⟩ : syracuseStep 1697083 = 2545625) B2545625
theorem B1697159 : Blo 1695548 1697159 := bstep (se 1 (by rfl) ⟨1272869, by rfl⟩ : syracuseStep 1697159 = 2545739) B2545739
theorem B1697167 : Blo 1695548 1697167 := bstep (se 1 (by rfl) ⟨1272875, by rfl⟩ : syracuseStep 1697167 = 2545751) B2545751
theorem B4294073 : Blo 1695548 4294073 := bstep (se 2 (by rfl) ⟨1610277, by rfl⟩ : syracuseStep 4294073 = 3220555) B3220555
theorem B14493113 : Blo 1695548 14493113 := bstep (se 2 (by rfl) ⟨5434917, by rfl⟩ : syracuseStep 14493113 = 10869835) B10869835
theorem B1697211 : Blo 1695548 1697211 := bstep (se 1 (by rfl) ⟨1272908, by rfl⟩ : syracuseStep 1697211 = 2545817) B2545817
theorem B1697287 : Blo 1695548 1697287 := bstep (se 1 (by rfl) ⟨1272965, by rfl⟩ : syracuseStep 1697287 = 2545931) B2545931
theorem B1697295 : Blo 1695548 1697295 := bstep (se 1 (by rfl) ⟨1272971, by rfl⟩ : syracuseStep 1697295 = 2545943) B2545943
theorem B3819023 : Blo 1695548 3819023 := bstep (se 1 (by rfl) ⟨2864267, by rfl⟩ : syracuseStep 3819023 = 5728535) B5728535
theorem B3819041 : Blo 1695548 3819041 := bstep (se 2 (by rfl) ⟨1432140, by rfl⟩ : syracuseStep 3819041 = 2864281) B2864281
theorem B1697339 : Blo 1695548 1697339 := bstep (se 1 (by rfl) ⟨1273004, by rfl⟩ : syracuseStep 1697339 = 2546009) B2546009
theorem B8701501 : Blo 1695548 8701501 := bstep (se 3 (by rfl) ⟨1631531, by rfl⟩ : syracuseStep 8701501 = 3263063) B3263063
theorem B1697415 : Blo 1695548 1697415 := bstep (se 1 (by rfl) ⟨1273061, by rfl⟩ : syracuseStep 1697415 = 2546123) B2546123
theorem B1697423 : Blo 1695548 1697423 := bstep (se 1 (by rfl) ⟨1273067, by rfl⟩ : syracuseStep 1697423 = 2546135) B2546135
theorem B1697467 : Blo 1695548 1697467 := bstep (se 1 (by rfl) ⟨1273100, by rfl⟩ : syracuseStep 1697467 = 2546201) B2546201
theorem B7243465 : Blo 1695548 7243465 := bstep (se 2 (by rfl) ⟨2716299, by rfl⟩ : syracuseStep 7243465 = 5432599) B5432599
theorem B9660161 : Blo 1695548 9660161 := bstep (se 2 (by rfl) ⟨3622560, by rfl⟩ : syracuseStep 9660161 = 7245121) B7245121
theorem B1697543 : Blo 1695548 1697543 := bstep (se 1 (by rfl) ⟨1273157, by rfl⟩ : syracuseStep 1697543 = 2546315) B2546315
theorem B29394737 : Blo 1695548 29394737 := bstep (se 2 (by rfl) ⟨11023026, by rfl⟩ : syracuseStep 29394737 = 22046053) B22046053
theorem B14493491 : Blo 1695548 14493491 := bstep (se 1 (by rfl) ⟨10870118, by rfl⟩ : syracuseStep 14493491 = 21740237) B21740237
theorem B3622715 : Blo 1695548 3622715 := bstep (se 1 (by rfl) ⟨2717036, by rfl⟩ : syracuseStep 3622715 = 5434073) B5434073
theorem B3819383 : Blo 1695548 3819383 := bstep (se 1 (by rfl) ⟨2864537, by rfl⟩ : syracuseStep 3819383 = 5729075) B5729075
theorem B3221383 : Blo 1695548 3221383 := bstep (se 1 (by rfl) ⟨2416037, by rfl⟩ : syracuseStep 3221383 = 4832075) B4832075
theorem B6441079 : Blo 1695548 6441079 := bstep (se 1 (by rfl) ⟨4830809, by rfl⟩ : syracuseStep 6441079 = 9661619) B9661619
theorem B19581061 : Blo 1695548 19581061 := bstep (se 4 (by rfl) ⟨1835724, by rfl⟩ : syracuseStep 19581061 = 3671449) B3671449
theorem B8587457 : Blo 1695548 8587457 := bstep (se 2 (by rfl) ⟨3220296, by rfl⟩ : syracuseStep 8587457 = 6440593) B6440593
theorem B2861257 : Blo 1695548 2861257 := bstep (se 2 (by rfl) ⟨1072971, by rfl⟩ : syracuseStep 2861257 = 2145943) B2145943
theorem B9660617 : Blo 1695548 9660617 := bstep (se 2 (by rfl) ⟨3622731, by rfl⟩ : syracuseStep 9660617 = 7245463) B7245463
theorem B13060385 : Blo 1695548 13060385 := bstep (se 2 (by rfl) ⟨4897644, by rfl⟩ : syracuseStep 13060385 = 9795289) B9795289
theorem B21735773 : Blo 1695548 21735773 := bstep (se 3 (by rfl) ⟨4075457, by rfl⟩ : syracuseStep 21735773 = 8150915) B8150915
theorem B4295065 : Blo 1695548 4295065 := bstep (se 2 (by rfl) ⟨1610649, by rfl⟩ : syracuseStep 4295065 = 3221299) B3221299
theorem B5728697 : Blo 1695548 5728697 := bstep (se 2 (by rfl) ⟨2148261, by rfl⟩ : syracuseStep 5728697 = 4296523) B4296523
theorem B10463755 : Blo 1695548 10463755 := bstep (se 1 (by rfl) ⟨7847816, by rfl⟩ : syracuseStep 10463755 = 15695633) B15695633
theorem B3623467 : Blo 1695548 3623467 := bstep (se 1 (by rfl) ⟨2717600, by rfl⟩ : syracuseStep 3623467 = 5435201) B5435201
theorem B4295227 : Blo 1695548 4295227 := bstep (se 1 (by rfl) ⟨3221420, by rfl⟩ : syracuseStep 4295227 = 6442841) B6442841
theorem B13232717 : Blo 1695548 13232717 := bstep (se 3 (by rfl) ⟨2481134, by rfl⟩ : syracuseStep 13232717 = 4962269) B4962269
theorem B4295369 : Blo 1695548 4295369 := bstep (se 2 (by rfl) ⟨1610763, by rfl⟩ : syracuseStep 4295369 = 3221527) B3221527
theorem B5229355 : Blo 1695548 5229355 := bstep (se 1 (by rfl) ⟨3922016, by rfl⟩ : syracuseStep 5229355 = 7844033) B7844033
theorem B9300851 : Blo 1695548 9300851 := bstep (se 1 (by rfl) ⟨6975638, by rfl⟩ : syracuseStep 9300851 = 13951277) B13951277
theorem B8711027 : Blo 1695548 8711027 := bstep (se 1 (by rfl) ⟨6533270, by rfl⟩ : syracuseStep 8711027 = 13066541) B13066541
theorem B2861959 : Blo 1695548 2861959 := bstep (se 1 (by rfl) ⟨2146469, by rfl⟩ : syracuseStep 2861959 = 4292939) B4292939
theorem B4131785 : Blo 1695548 4131785 := bstep (se 2 (by rfl) ⟨1549419, by rfl⟩ : syracuseStep 4131785 = 3098839) B3098839
theorem B4295713 : Blo 1695548 4295713 := bstep (se 2 (by rfl) ⟨1610892, by rfl⟩ : syracuseStep 4295713 = 3221785) B3221785
theorem B6442051 : Blo 1695548 6442051 := bstep (se 1 (by rfl) ⟨4831538, by rfl⟩ : syracuseStep 6442051 = 9663077) B9663077
theorem B3058987 : Blo 1695548 3058987 := bstep (se 1 (by rfl) ⟨2294240, by rfl⟩ : syracuseStep 3058987 = 4588481) B4588481
theorem B6442355 : Blo 1695548 6442355 := bstep (se 1 (by rfl) ⟨4831766, by rfl⟩ : syracuseStep 6442355 = 9663533) B9663533
theorem B8588753 : Blo 1695548 8588753 := bstep (se 2 (by rfl) ⟨3220782, by rfl⟩ : syracuseStep 8588753 = 6441565) B6441565
theorem B2862607 : Blo 1695548 2862607 := bstep (se 1 (by rfl) ⟨2146955, by rfl⟩ : syracuseStep 2862607 = 4293911) B4293911
theorem B2649719 : Blo 1695548 2649719 := bstep (se 1 (by rfl) ⟨1987289, by rfl⟩ : syracuseStep 2649719 = 3974579) B3974579
theorem B4296311 : Blo 1695548 4296311 := bstep (se 1 (by rfl) ⟨3222233, by rfl⟩ : syracuseStep 4296311 = 6444467) B6444467
theorem B19328705 : Blo 1695548 19328705 := bstep (se 2 (by rfl) ⟨7248264, by rfl⟩ : syracuseStep 19328705 = 14496529) B14496529
theorem B125710051 : Blo 1695548 125710051 := bstep (se 1 (by rfl) ⟨94282538, by rfl⟩ : syracuseStep 125710051 = 188565077) B188565077
theorem B2543351 : Blo 1695548 2543351 := bstep (se 1 (by rfl) ⟨1907513, by rfl⟩ : syracuseStep 2543351 = 3815027) B3815027
theorem B2543375 : Blo 1695548 2543375 := bstep (se 1 (by rfl) ⟨1907531, by rfl⟩ : syracuseStep 2543375 = 3815063) B3815063
theorem B8154913 : Blo 1695548 8154913 := bstep (se 2 (by rfl) ⟨3058092, by rfl⟩ : syracuseStep 8154913 = 6116185) B6116185
theorem B2543417 : Blo 1695548 2543417 := bstep (se 2 (by rfl) ⟨953781, by rfl⟩ : syracuseStep 2543417 = 1907563) B1907563
theorem B4828987 : Blo 1695548 4828987 := bstep (se 1 (by rfl) ⟨3621740, by rfl⟩ : syracuseStep 4828987 = 7243481) B7243481
theorem B6442811 : Blo 1695548 6442811 := bstep (se 1 (by rfl) ⟨4832108, by rfl⟩ : syracuseStep 6442811 = 9664217) B9664217
theorem B2543495 : Blo 1695548 2543495 := bstep (se 1 (by rfl) ⟨1907621, by rfl⟩ : syracuseStep 2543495 = 3815243) B3815243
theorem B3624851 : Blo 1695548 3624851 := bstep (se 1 (by rfl) ⟨2718638, by rfl⟩ : syracuseStep 3624851 = 5437277) B5437277
theorem B2543531 : Blo 1695548 2543531 := bstep (se 1 (by rfl) ⟨1907648, by rfl⟩ : syracuseStep 2543531 = 3815297) B3815297
theorem B2543561 : Blo 1695548 2543561 := bstep (se 2 (by rfl) ⟨953835, by rfl⟩ : syracuseStep 2543561 = 1907671) B1907671
theorem B10866635 : Blo 1695548 10866635 := bstep (se 1 (by rfl) ⟨8149976, by rfl⟩ : syracuseStep 10866635 = 16299953) B16299953
theorem B4075535 : Blo 1695548 4075535 := bstep (se 1 (by rfl) ⟨3056651, by rfl⟩ : syracuseStep 4075535 = 6113303) B6113303
theorem B2863147 : Blo 1695548 2863147 := bstep (se 1 (by rfl) ⟨2147360, by rfl⟩ : syracuseStep 2863147 = 4294721) B4294721
theorem B2543675 : Blo 1695548 2543675 := bstep (se 1 (by rfl) ⟨1907756, by rfl⟩ : syracuseStep 2543675 = 3815513) B3815513
theorem B2543735 : Blo 1695548 2543735 := bstep (se 1 (by rfl) ⟨1907801, by rfl⟩ : syracuseStep 2543735 = 3815603) B3815603
theorem B2543759 : Blo 1695548 2543759 := bstep (se 1 (by rfl) ⟨1907819, by rfl⟩ : syracuseStep 2543759 = 3815639) B3815639
theorem B2543801 : Blo 1695548 2543801 := bstep (se 2 (by rfl) ⟨953925, by rfl⟩ : syracuseStep 2543801 = 1907851) B1907851
theorem B2863289 : Blo 1695548 2863289 := bstep (se 2 (by rfl) ⟨1073733, by rfl⟩ : syracuseStep 2863289 = 2147467) B2147467
theorem B2543879 : Blo 1695548 2543879 := bstep (se 1 (by rfl) ⟨1907909, by rfl⟩ : syracuseStep 2543879 = 3815819) B3815819
theorem B6443297 : Blo 1695548 6443297 := bstep (se 2 (by rfl) ⟨2416236, by rfl⟩ : syracuseStep 6443297 = 4832473) B4832473
theorem B2715947 : Blo 1695548 2715947 := bstep (se 1 (by rfl) ⟨2036960, by rfl⟩ : syracuseStep 2715947 = 4073921) B4073921
theorem B2543915 : Blo 1695548 2543915 := bstep (se 1 (by rfl) ⟨1907936, by rfl⟩ : syracuseStep 2543915 = 3815873) B3815873
theorem B2543945 : Blo 1695548 2543945 := bstep (se 2 (by rfl) ⟨953979, by rfl⟩ : syracuseStep 2543945 = 1907959) B1907959
theorem B2544059 : Blo 1695548 2544059 := bstep (se 1 (by rfl) ⟨1908044, by rfl⟩ : syracuseStep 2544059 = 3816089) B3816089
theorem B15479261 : Blo 1695548 15479261 := bstep (se 3 (by rfl) ⟨2902361, by rfl⟩ : syracuseStep 15479261 = 5804723) B5804723
theorem B2544119 : Blo 1695548 2544119 := bstep (se 1 (by rfl) ⟨1908089, by rfl⟩ : syracuseStep 2544119 = 3816179) B3816179
theorem B2544143 : Blo 1695548 2544143 := bstep (se 1 (by rfl) ⟨1908107, by rfl⟩ : syracuseStep 2544143 = 3816215) B3816215
theorem B2544185 : Blo 1695548 2544185 := bstep (se 2 (by rfl) ⟨954069, by rfl⟩ : syracuseStep 2544185 = 1908139) B1908139
theorem B4829831 : Blo 1695548 4829831 := bstep (se 1 (by rfl) ⟨3622373, by rfl⟩ : syracuseStep 4829831 = 7244747) B7244747
theorem B2544263 : Blo 1695548 2544263 := bstep (se 1 (by rfl) ⟨1908197, by rfl⟩ : syracuseStep 2544263 = 3816395) B3816395
theorem B2544299 : Blo 1695548 2544299 := bstep (se 1 (by rfl) ⟨1908224, by rfl⟩ : syracuseStep 2544299 = 3816449) B3816449
theorem B2544329 : Blo 1695548 2544329 := bstep (se 2 (by rfl) ⟨954123, by rfl⟩ : syracuseStep 2544329 = 1908247) B1908247
theorem B2716459 : Blo 1695548 2716459 := bstep (se 1 (by rfl) ⟨2037344, by rfl⟩ : syracuseStep 2716459 = 4074689) B4074689
theorem B2544443 : Blo 1695548 2544443 := bstep (se 1 (by rfl) ⟨1908332, by rfl⟩ : syracuseStep 2544443 = 3816665) B3816665
theorem B2544503 : Blo 1695548 2544503 := bstep (se 1 (by rfl) ⟨1908377, by rfl⟩ : syracuseStep 2544503 = 3816755) B3816755
theorem B2863991 : Blo 1695548 2863991 := bstep (se 1 (by rfl) ⟨2147993, by rfl⟩ : syracuseStep 2863991 = 4295987) B4295987
theorem B2544527 : Blo 1695548 2544527 := bstep (se 1 (by rfl) ⟨1908395, by rfl⟩ : syracuseStep 2544527 = 3816791) B3816791
theorem B5723027 : Blo 1695548 5723027 := bstep (se 1 (by rfl) ⟨4292270, by rfl⟩ : syracuseStep 5723027 = 8584541) B8584541
theorem B27898805 : Blo 1695548 27898805 := bstep (se 5 (by rfl) ⟨1307756, by rfl⟩ : syracuseStep 27898805 = 2615513) B2615513
theorem B2544569 : Blo 1695548 2544569 := bstep (se 2 (by rfl) ⟨954213, by rfl⟩ : syracuseStep 2544569 = 1908427) B1908427
theorem B2544647 : Blo 1695548 2544647 := bstep (se 1 (by rfl) ⟨1908485, by rfl⟩ : syracuseStep 2544647 = 3816971) B3816971
theorem B2544683 : Blo 1695548 2544683 := bstep (se 1 (by rfl) ⟨1908512, by rfl⟩ : syracuseStep 2544683 = 3817025) B3817025
theorem B2544713 : Blo 1695548 2544713 := bstep (se 2 (by rfl) ⟨954267, by rfl⟩ : syracuseStep 2544713 = 1908535) B1908535
theorem B36705413 : Blo 1695548 36705413 := bstep (se 4 (by rfl) ⟨3441132, by rfl⟩ : syracuseStep 36705413 = 6882265) B6882265
theorem B2544827 : Blo 1695548 2544827 := bstep (se 1 (by rfl) ⟨1908620, by rfl⟩ : syracuseStep 2544827 = 3817241) B3817241
theorem B6444269 : Blo 1695548 6444269 := bstep (se 3 (by rfl) ⟨1208300, by rfl⟩ : syracuseStep 6444269 = 2416601) B2416601
theorem B2544887 : Blo 1695548 2544887 := bstep (se 1 (by rfl) ⟨1908665, by rfl⟩ : syracuseStep 2544887 = 3817331) B3817331
theorem B2544911 : Blo 1695548 2544911 := bstep (se 1 (by rfl) ⟨1908683, by rfl⟩ : syracuseStep 2544911 = 3817367) B3817367
theorem B9557281 : Blo 1695548 9557281 := bstep (se 2 (by rfl) ⟨3583980, by rfl⟩ : syracuseStep 9557281 = 7167961) B7167961
theorem B10876193 : Blo 1695548 10876193 := bstep (se 2 (by rfl) ⟨4078572, by rfl⟩ : syracuseStep 10876193 = 8157145) B8157145
theorem B2544953 : Blo 1695548 2544953 := bstep (se 2 (by rfl) ⟨954357, by rfl⟩ : syracuseStep 2544953 = 1908715) B1908715
theorem B2864443 : Blo 1695548 2864443 := bstep (se 1 (by rfl) ⟨2148332, by rfl⟩ : syracuseStep 2864443 = 4296665) B4296665
theorem B2545031 : Blo 1695548 2545031 := bstep (se 1 (by rfl) ⟨1908773, by rfl⟩ : syracuseStep 2545031 = 3817547) B3817547
theorem B4830617 : Blo 1695548 4830617 := bstep (se 2 (by rfl) ⟨1811481, by rfl⟩ : syracuseStep 4830617 = 3622963) B3622963
theorem B2545067 : Blo 1695548 2545067 := bstep (se 1 (by rfl) ⟨1908800, by rfl⟩ : syracuseStep 2545067 = 3817601) B3817601
theorem B2545097 : Blo 1695548 2545097 := bstep (se 2 (by rfl) ⟨954411, by rfl⟩ : syracuseStep 2545097 = 1908823) B1908823
theorem B2864585 : Blo 1695548 2864585 := bstep (se 2 (by rfl) ⟨1074219, by rfl⟩ : syracuseStep 2864585 = 2148439) B2148439
theorem B19314125 : Blo 1695548 19314125 := bstep (se 3 (by rfl) ⟨3621398, by rfl⟩ : syracuseStep 19314125 = 7242797) B7242797
theorem B8590859 : Blo 1695548 8590859 := bstep (se 1 (by rfl) ⟨6443144, by rfl⟩ : syracuseStep 8590859 = 12886289) B12886289
theorem B14489117 : Blo 1695548 14489117 := bstep (se 3 (by rfl) ⟨2716709, by rfl⟩ : syracuseStep 14489117 = 5433419) B5433419
theorem B2545211 : Blo 1695548 2545211 := bstep (se 1 (by rfl) ⟨1908908, by rfl⟩ : syracuseStep 2545211 = 3817817) B3817817
theorem B2545271 : Blo 1695548 2545271 := bstep (se 1 (by rfl) ⟨1908953, by rfl⟩ : syracuseStep 2545271 = 3817907) B3817907
theorem B2414215 : Blo 1695548 2414215 := bstep (se 1 (by rfl) ⟨1810661, by rfl⟩ : syracuseStep 2414215 = 3621323) B3621323
theorem B3438215 : Blo 1695548 3438215 := bstep (se 1 (by rfl) ⟨2578661, by rfl⟩ : syracuseStep 3438215 = 5157323) B5157323
theorem B2545295 : Blo 1695548 2545295 := bstep (se 1 (by rfl) ⟨1908971, by rfl⟩ : syracuseStep 2545295 = 3817943) B3817943
theorem B8591021 : Blo 1695548 8591021 := bstep (se 3 (by rfl) ⟨1610816, by rfl⟩ : syracuseStep 8591021 = 3221633) B3221633
theorem B5158585 : Blo 1695548 5158585 := bstep (se 2 (by rfl) ⟨1934469, by rfl⟩ : syracuseStep 5158585 = 3868939) B3868939
theorem B2545337 : Blo 1695548 2545337 := bstep (se 2 (by rfl) ⟨954501, by rfl⟩ : syracuseStep 2545337 = 1909003) B1909003
theorem B2545415 : Blo 1695548 2545415 := bstep (se 1 (by rfl) ⟨1909061, by rfl⟩ : syracuseStep 2545415 = 3818123) B3818123
theorem B2545451 : Blo 1695548 2545451 := bstep (se 1 (by rfl) ⟨1909088, by rfl⟩ : syracuseStep 2545451 = 3818177) B3818177
theorem B2545481 : Blo 1695548 2545481 := bstep (se 2 (by rfl) ⟨954555, by rfl⟩ : syracuseStep 2545481 = 1909111) B1909111
theorem B3815315 : Blo 1695548 3815315 := bstep (se 1 (by rfl) ⟨2861486, by rfl⟩ : syracuseStep 3815315 = 5722973) B5722973
theorem B6444953 : Blo 1695548 6444953 := bstep (se 2 (by rfl) ⟨2416857, by rfl⟩ : syracuseStep 6444953 = 4833715) B4833715
theorem B2545595 : Blo 1695548 2545595 := bstep (se 1 (by rfl) ⟨1909196, by rfl⟩ : syracuseStep 2545595 = 3818393) B3818393
theorem B3815369 : Blo 1695548 3815369 := bstep (se 2 (by rfl) ⟨1430763, by rfl⟩ : syracuseStep 3815369 = 2861527) B2861527
theorem B2545655 : Blo 1695548 2545655 := bstep (se 1 (by rfl) ⟨1909241, by rfl⟩ : syracuseStep 2545655 = 3818483) B3818483
theorem B8148995 : Blo 1695548 8148995 := bstep (se 1 (by rfl) ⟨6111746, by rfl⟩ : syracuseStep 8148995 = 12223493) B12223493
theorem B2545679 : Blo 1695548 2545679 := bstep (se 1 (by rfl) ⟨1909259, by rfl⟩ : syracuseStep 2545679 = 3818519) B3818519
theorem B9664535 : Blo 1695548 9664535 := bstep (se 1 (by rfl) ⟨7248401, by rfl⟩ : syracuseStep 9664535 = 14496803) B14496803
theorem B12400663 : Blo 1695548 12400663 := bstep (se 1 (by rfl) ⟨9300497, by rfl⟩ : syracuseStep 12400663 = 18600995) B18600995
theorem B4831265 : Blo 1695548 4831265 := bstep (se 2 (by rfl) ⟨1811724, by rfl⟩ : syracuseStep 4831265 = 3623449) B3623449
theorem B4077611 : Blo 1695548 4077611 := bstep (se 1 (by rfl) ⟨3058208, by rfl⟩ : syracuseStep 4077611 = 6116417) B6116417
theorem B2545721 : Blo 1695548 2545721 := bstep (se 2 (by rfl) ⟨954645, by rfl⟩ : syracuseStep 2545721 = 1909291) B1909291
theorem B6117443 : Blo 1695548 6117443 := bstep (se 1 (by rfl) ⟨4588082, by rfl⟩ : syracuseStep 6117443 = 9176165) B9176165
theorem B2545799 : Blo 1695548 2545799 := bstep (se 1 (by rfl) ⟨1909349, by rfl⟩ : syracuseStep 2545799 = 3818699) B3818699
theorem B2545835 : Blo 1695548 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B2545865 : Blo 1695548 2545865 := bstep (se 2 (by rfl) ⟨954699, by rfl⟩ : syracuseStep 2545865 = 1909399) B1909399
theorem B8706305 : Blo 1695548 8706305 := bstep (se 2 (by rfl) ⟨3264864, by rfl⟩ : syracuseStep 8706305 = 6529729) B6529729
theorem B5724431 : Blo 1695548 5724431 := bstep (se 1 (by rfl) ⟨4293323, by rfl⟩ : syracuseStep 5724431 = 8586647) B8586647
theorem B17414459 : Blo 1695548 17414459 := bstep (se 1 (by rfl) ⟨13060844, by rfl⟩ : syracuseStep 17414459 = 26121689) B26121689
theorem B2718011 : Blo 1695548 2718011 := bstep (se 1 (by rfl) ⟨2038508, by rfl⟩ : syracuseStep 2718011 = 4077017) B4077017
theorem B2545979 : Blo 1695548 2545979 := bstep (se 1 (by rfl) ⟨1909484, by rfl⟩ : syracuseStep 2545979 = 3818969) B3818969
theorem B2546039 : Blo 1695548 2546039 := bstep (se 1 (by rfl) ⟨1909529, by rfl⟩ : syracuseStep 2546039 = 3819059) B3819059
theorem B2546063 : Blo 1695548 2546063 := bstep (se 1 (by rfl) ⟨1909547, by rfl⟩ : syracuseStep 2546063 = 3819095) B3819095
theorem B2546105 : Blo 1695548 2546105 := bstep (se 2 (by rfl) ⟨954789, by rfl⟩ : syracuseStep 2546105 = 1909579) B1909579
theorem B2415035 : Blo 1695548 2415035 := bstep (se 1 (by rfl) ⟨1811276, by rfl⟩ : syracuseStep 2415035 = 3622553) B3622553
theorem B2546183 : Blo 1695548 2546183 := bstep (se 1 (by rfl) ⟨1909637, by rfl⟩ : syracuseStep 2546183 = 3819275) B3819275
theorem B5724701 : Blo 1695548 5724701 := bstep (se 3 (by rfl) ⟨1073381, by rfl⟩ : syracuseStep 5724701 = 2146763) B2146763
theorem B2546219 : Blo 1695548 2546219 := bstep (se 1 (by rfl) ⟨1909664, by rfl⟩ : syracuseStep 2546219 = 3819329) B3819329
theorem B2546249 : Blo 1695548 2546249 := bstep (se 2 (by rfl) ⟨954843, by rfl⟩ : syracuseStep 2546249 = 1909687) B1909687
theorem B3816071 : Blo 1695548 3816071 := bstep (se 1 (by rfl) ⟨2862053, by rfl⟩ : syracuseStep 3816071 = 5724107) B5724107
theorem B9296641 : Blo 1695548 9296641 := bstep (se 2 (by rfl) ⟨3486240, by rfl⟩ : syracuseStep 9296641 = 6972481) B6972481
theorem B30964517 : Blo 1695548 30964517 := bstep (se 4 (by rfl) ⟨2902923, by rfl⟩ : syracuseStep 30964517 = 5805847) B5805847
theorem B3816251 : Blo 1695548 3816251 := bstep (se 1 (by rfl) ⟨2862188, by rfl⟩ : syracuseStep 3816251 = 5724377) B5724377
theorem B14695283 : Blo 1695548 14695283 := bstep (se 1 (by rfl) ⟨11021462, by rfl⟩ : syracuseStep 14695283 = 22042925) B22042925
theorem B1907599 : Blo 1695548 1907599 := bstep (se 1 (by rfl) ⟨1430699, by rfl⟩ : syracuseStep 1907599 = 2861399) B2861399
theorem B3816377 : Blo 1695548 3816377 := bstep (se 2 (by rfl) ⟨1431141, by rfl⟩ : syracuseStep 3816377 = 2862283) B2862283
theorem B4832257 : Blo 1695548 4832257 := bstep (se 2 (by rfl) ⟨1812096, by rfl⟩ : syracuseStep 4832257 = 3624193) B3624193
theorem B2292743 : Blo 1695548 2292743 := bstep (se 1 (by rfl) ⟨1719557, by rfl⟩ : syracuseStep 2292743 = 3439115) B3439115
theorem B2415673 : Blo 1695548 2415673 := bstep (se 2 (by rfl) ⟨905877, by rfl⟩ : syracuseStep 2415673 = 1811755) B1811755
theorem B8592641 : Blo 1695548 8592641 := bstep (se 2 (by rfl) ⟨3222240, by rfl⟩ : syracuseStep 8592641 = 6444481) B6444481
theorem B3816719 : Blo 1695548 3816719 := bstep (se 1 (by rfl) ⟨2862539, by rfl⟩ : syracuseStep 3816719 = 5725079) B5725079
theorem B13753633 : Blo 1695548 13753633 := bstep (se 2 (by rfl) ⟨5157612, by rfl⟩ : syracuseStep 13753633 = 10315225) B10315225
theorem B3816737 : Blo 1695548 3816737 := bstep (se 2 (by rfl) ⟨1431276, by rfl⟩ : syracuseStep 3816737 = 2862553) B2862553
theorem B2293051 : Blo 1695548 2293051 := bstep (se 1 (by rfl) ⟨1719788, by rfl⟩ : syracuseStep 2293051 = 3439577) B3439577
theorem B1908103 : Blo 1695548 1908103 := bstep (se 1 (by rfl) ⟨1431077, by rfl⟩ : syracuseStep 1908103 = 2862155) B2862155
theorem B2448775 : Blo 1695548 2448775 := bstep (se 1 (by rfl) ⟨1836581, by rfl⟩ : syracuseStep 2448775 = 3673163) B3673163
theorem B4291987 : Blo 1695548 4291987 := bstep (se 1 (by rfl) ⟨3218990, by rfl⟩ : syracuseStep 4291987 = 6437981) B6437981
theorem B6880697 : Blo 1695548 6880697 := bstep (se 2 (by rfl) ⟨2580261, by rfl⟩ : syracuseStep 6880697 = 5160523) B5160523
theorem B4292129 : Blo 1695548 4292129 := bstep (se 2 (by rfl) ⟨1609548, by rfl⟩ : syracuseStep 4292129 = 3219097) B3219097
theorem B1908283 : Blo 1695548 1908283 := bstep (se 1 (by rfl) ⟨1431212, by rfl⟩ : syracuseStep 1908283 = 2862425) B2862425
theorem B6438467 : Blo 1695548 6438467 := bstep (se 1 (by rfl) ⟨4828850, by rfl⟩ : syracuseStep 6438467 = 9657701) B9657701
theorem B33037901 : Blo 1695548 33037901 := bstep (se 3 (by rfl) ⟨6194606, by rfl⟩ : syracuseStep 33037901 = 12389213) B12389213
theorem B7249495 : Blo 1695548 7249495 := bstep (se 1 (by rfl) ⟨5437121, by rfl⟩ : syracuseStep 7249495 = 10874243) B10874243
theorem B3817079 : Blo 1695548 3817079 := bstep (se 1 (by rfl) ⟨2862809, by rfl⟩ : syracuseStep 3817079 = 5725619) B5725619
theorem B9166537 : Blo 1695548 9166537 := bstep (se 2 (by rfl) ⟨3437451, by rfl⟩ : syracuseStep 9166537 = 6874903) B6874903
theorem B12877541 : Blo 1695548 12877541 := bstep (se 4 (by rfl) ⟨1207269, by rfl⟩ : syracuseStep 12877541 = 2414539) B2414539
theorem B3817259 : Blo 1695548 3817259 := bstep (se 1 (by rfl) ⟨2862944, by rfl⟩ : syracuseStep 3817259 = 5725889) B5725889
theorem B1695623 : Blo 1695548 1695623 := bstep (se 1 (by rfl) ⟨1271717, by rfl⟩ : syracuseStep 1695623 = 2543435) B2543435
theorem B1695631 : Blo 1695548 1695631 := bstep (se 1 (by rfl) ⟨1271723, by rfl⟩ : syracuseStep 1695631 = 2543447) B2543447
theorem B9666449 : Blo 1695548 9666449 := bstep (se 2 (by rfl) ⟨3624918, by rfl⟩ : syracuseStep 9666449 = 7249837) B7249837
theorem B5726105 : Blo 1695548 5726105 := bstep (se 2 (by rfl) ⟨2147289, by rfl⟩ : syracuseStep 5726105 = 4294579) B4294579
theorem B13762457 : Blo 1695548 13762457 := bstep (se 2 (by rfl) ⟨5160921, by rfl⟩ : syracuseStep 13762457 = 10321843) B10321843
theorem B1695675 : Blo 1695548 1695675 := bstep (se 1 (by rfl) ⟨1271756, by rfl⟩ : syracuseStep 1695675 = 2543513) B2543513
theorem B3219401 : Blo 1695548 3219401 := bstep (se 2 (by rfl) ⟨1207275, by rfl⟩ : syracuseStep 3219401 = 2414551) B2414551
theorem B2580425 : Blo 1695548 2580425 := bstep (se 2 (by rfl) ⟨967659, by rfl⟩ : syracuseStep 2580425 = 1935319) B1935319
theorem B4292615 : Blo 1695548 4292615 := bstep (se 1 (by rfl) ⟨3219461, by rfl⟩ : syracuseStep 4292615 = 6438923) B6438923
theorem B1695783 : Blo 1695548 1695783 := bstep (se 1 (by rfl) ⟨1271837, by rfl⟩ : syracuseStep 1695783 = 2543675) B2543675
theorem B3817529 : Blo 1695548 3817529 := bstep (se 2 (by rfl) ⟨1431573, by rfl⟩ : syracuseStep 3817529 = 2863147) B2863147
theorem B1695823 : Blo 1695548 1695823 := bstep (se 1 (by rfl) ⟨1271867, by rfl⟩ : syracuseStep 1695823 = 2543735) B2543735
theorem B1695839 : Blo 1695548 1695839 := bstep (se 1 (by rfl) ⟨1271879, by rfl⟩ : syracuseStep 1695839 = 2543759) B2543759
theorem B1695867 : Blo 1695548 1695867 := bstep (se 1 (by rfl) ⟨1271900, by rfl⟩ : syracuseStep 1695867 = 2543801) B2543801
theorem B1908859 : Blo 1695548 1908859 := bstep (se 1 (by rfl) ⟨1431644, by rfl⟩ : syracuseStep 1908859 = 2863289) B2863289
theorem B1695919 : Blo 1695548 1695919 := bstep (se 1 (by rfl) ⟨1271939, by rfl⟩ : syracuseStep 1695919 = 2543879) B2543879
theorem B26108081 : Blo 1695548 26108081 := bstep (se 2 (by rfl) ⟨9790530, by rfl⟩ : syracuseStep 26108081 = 19581061) B19581061
theorem B1810631 : Blo 1695548 1810631 := bstep (se 1 (by rfl) ⟨1357973, by rfl⟩ : syracuseStep 1810631 = 2715947) B2715947
theorem B1695943 : Blo 1695548 1695943 := bstep (se 1 (by rfl) ⟨1271957, by rfl⟩ : syracuseStep 1695943 = 2543915) B2543915
theorem B1695963 : Blo 1695548 1695963 := bstep (se 1 (by rfl) ⟨1271972, by rfl⟩ : syracuseStep 1695963 = 2543945) B2543945
theorem B1696039 : Blo 1695548 1696039 := bstep (se 1 (by rfl) ⟨1272029, by rfl⟩ : syracuseStep 1696039 = 2544059) B2544059
theorem B1696079 : Blo 1695548 1696079 := bstep (se 1 (by rfl) ⟨1272059, by rfl⟩ : syracuseStep 1696079 = 2544119) B2544119
theorem B1696095 : Blo 1695548 1696095 := bstep (se 1 (by rfl) ⟨1272071, by rfl⟩ : syracuseStep 1696095 = 2544143) B2544143
theorem B1696123 : Blo 1695548 1696123 := bstep (se 1 (by rfl) ⟨1272092, by rfl⟩ : syracuseStep 1696123 = 2544185) B2544185
theorem B3817871 : Blo 1695548 3817871 := bstep (se 1 (by rfl) ⟨2863403, by rfl⟩ : syracuseStep 3817871 = 5726807) B5726807
theorem B3219887 : Blo 1695548 3219887 := bstep (se 1 (by rfl) ⟨2414915, by rfl⟩ : syracuseStep 3219887 = 4829831) B4829831
theorem B1696175 : Blo 1695548 1696175 := bstep (se 1 (by rfl) ⟨1272131, by rfl⟩ : syracuseStep 1696175 = 2544263) B2544263
theorem B1696199 : Blo 1695548 1696199 := bstep (se 1 (by rfl) ⟨1272149, by rfl⟩ : syracuseStep 1696199 = 2544299) B2544299
theorem B1696219 : Blo 1695548 1696219 := bstep (se 1 (by rfl) ⟨1272164, by rfl⟩ : syracuseStep 1696219 = 2544329) B2544329
theorem B5726753 : Blo 1695548 5726753 := bstep (se 2 (by rfl) ⟨2147532, by rfl⟩ : syracuseStep 5726753 = 4295065) B4295065
theorem B1696295 : Blo 1695548 1696295 := bstep (se 1 (by rfl) ⟨1272221, by rfl⟩ : syracuseStep 1696295 = 2544443) B2544443
theorem B1696335 : Blo 1695548 1696335 := bstep (se 1 (by rfl) ⟨1272251, by rfl⟩ : syracuseStep 1696335 = 2544503) B2544503
theorem B1909327 : Blo 1695548 1909327 := bstep (se 1 (by rfl) ⟨1431995, by rfl⟩ : syracuseStep 1909327 = 2863991) B2863991
theorem B1696351 : Blo 1695548 1696351 := bstep (se 1 (by rfl) ⟨1272263, by rfl⟩ : syracuseStep 1696351 = 2544527) B2544527
theorem B1696379 : Blo 1695548 1696379 := bstep (se 1 (by rfl) ⟨1272284, by rfl⟩ : syracuseStep 1696379 = 2544569) B2544569
theorem B4833931 : Blo 1695548 4833931 := bstep (se 1 (by rfl) ⟨3625448, by rfl⟩ : syracuseStep 4833931 = 7250897) B7250897
theorem B23216813 : Blo 1695548 23216813 := bstep (se 3 (by rfl) ⟨4353152, by rfl⟩ : syracuseStep 23216813 = 8706305) B8706305
theorem B1696431 : Blo 1695548 1696431 := bstep (se 1 (by rfl) ⟨1272323, by rfl⟩ : syracuseStep 1696431 = 2544647) B2544647
theorem B13951673 : Blo 1695548 13951673 := bstep (se 2 (by rfl) ⟨5231877, by rfl⟩ : syracuseStep 13951673 = 10463755) B10463755
theorem B1696455 : Blo 1695548 1696455 := bstep (se 1 (by rfl) ⟨1272341, by rfl⟩ : syracuseStep 1696455 = 2544683) B2544683
theorem B3818195 : Blo 1695548 3818195 := bstep (se 1 (by rfl) ⟨2863646, by rfl⟩ : syracuseStep 3818195 = 5727293) B5727293
theorem B1696475 : Blo 1695548 1696475 := bstep (se 1 (by rfl) ⟨1272356, by rfl⟩ : syracuseStep 1696475 = 2544713) B2544713
theorem B5726969 : Blo 1695548 5726969 := bstep (se 2 (by rfl) ⟨2147613, by rfl⟩ : syracuseStep 5726969 = 4295227) B4295227
theorem B24470275 : Blo 1695548 24470275 := bstep (se 1 (by rfl) ⟨18352706, by rfl⟩ : syracuseStep 24470275 = 36705413) B36705413
theorem B1696551 : Blo 1695548 1696551 := bstep (se 1 (by rfl) ⟨1272413, by rfl⟩ : syracuseStep 1696551 = 2544827) B2544827
theorem B1696591 : Blo 1695548 1696591 := bstep (se 1 (by rfl) ⟨1272443, by rfl⟩ : syracuseStep 1696591 = 2544887) B2544887
theorem B1696607 : Blo 1695548 1696607 := bstep (se 1 (by rfl) ⟨1272455, by rfl⟩ : syracuseStep 1696607 = 2544911) B2544911
theorem B7250795 : Blo 1695548 7250795 := bstep (se 1 (by rfl) ⟨5438096, by rfl⟩ : syracuseStep 7250795 = 10876193) B10876193
theorem B1696635 : Blo 1695548 1696635 := bstep (se 1 (by rfl) ⟨1272476, by rfl⟩ : syracuseStep 1696635 = 2544953) B2544953
theorem B1696687 : Blo 1695548 1696687 := bstep (se 1 (by rfl) ⟨1272515, by rfl⟩ : syracuseStep 1696687 = 2545031) B2545031
theorem B3220411 : Blo 1695548 3220411 := bstep (se 1 (by rfl) ⟨2415308, by rfl⟩ : syracuseStep 3220411 = 4830617) B4830617
theorem B1696711 : Blo 1695548 1696711 := bstep (se 1 (by rfl) ⟨1272533, by rfl⟩ : syracuseStep 1696711 = 2545067) B2545067
theorem B1696731 : Blo 1695548 1696731 := bstep (se 1 (by rfl) ⟨1272548, by rfl⟩ : syracuseStep 1696731 = 2545097) B2545097
theorem B1909723 : Blo 1695548 1909723 := bstep (se 1 (by rfl) ⟨1432292, by rfl⟩ : syracuseStep 1909723 = 2864585) B2864585
theorem B12395521 : Blo 1695548 12395521 := bstep (se 2 (by rfl) ⟨4648320, by rfl⟩ : syracuseStep 12395521 = 9296641) B9296641
theorem B5727239 : Blo 1695548 5727239 := bstep (se 1 (by rfl) ⟨4295429, by rfl⟩ : syracuseStep 5727239 = 8590859) B8590859
theorem B9659411 : Blo 1695548 9659411 := bstep (se 1 (by rfl) ⟨7244558, by rfl⟩ : syracuseStep 9659411 = 14489117) B14489117
theorem B1696807 : Blo 1695548 1696807 := bstep (se 1 (by rfl) ⟨1272605, by rfl⟩ : syracuseStep 1696807 = 2545211) B2545211
theorem B6972473 : Blo 1695548 6972473 := bstep (se 2 (by rfl) ⟨2614677, by rfl⟩ : syracuseStep 6972473 = 5229355) B5229355
theorem B1696847 : Blo 1695548 1696847 := bstep (se 1 (by rfl) ⟨1272635, by rfl⟩ : syracuseStep 1696847 = 2545271) B2545271
theorem B1696863 : Blo 1695548 1696863 := bstep (se 1 (by rfl) ⟨1272647, by rfl⟩ : syracuseStep 1696863 = 2545295) B2545295
theorem B5727347 : Blo 1695548 5727347 := bstep (se 1 (by rfl) ⟨4295510, by rfl⟩ : syracuseStep 5727347 = 8591021) B8591021
theorem B1696891 : Blo 1695548 1696891 := bstep (se 1 (by rfl) ⟨1272668, by rfl⟩ : syracuseStep 1696891 = 2545337) B2545337
theorem B6440093 : Blo 1695548 6440093 := bstep (se 3 (by rfl) ⟨1207517, by rfl⟩ : syracuseStep 6440093 = 2415035) B2415035
theorem B6440107 : Blo 1695548 6440107 := bstep (se 1 (by rfl) ⟨4830080, by rfl⟩ : syracuseStep 6440107 = 9660161) B9660161
theorem B1696943 : Blo 1695548 1696943 := bstep (se 1 (by rfl) ⟨1272707, by rfl⟩ : syracuseStep 1696943 = 2545415) B2545415
theorem B1696967 : Blo 1695548 1696967 := bstep (se 1 (by rfl) ⟨1272725, by rfl⟩ : syracuseStep 1696967 = 2545451) B2545451
theorem B19596491 : Blo 1695548 19596491 := bstep (se 1 (by rfl) ⟨14697368, by rfl⟩ : syracuseStep 19596491 = 29394737) B29394737
theorem B1696987 : Blo 1695548 1696987 := bstep (se 1 (by rfl) ⟨1272740, by rfl⟩ : syracuseStep 1696987 = 2545481) B2545481
theorem B1697063 : Blo 1695548 1697063 := bstep (se 1 (by rfl) ⟨1272797, by rfl⟩ : syracuseStep 1697063 = 2545595) B2545595
theorem B1697103 : Blo 1695548 1697103 := bstep (se 1 (by rfl) ⟨1272827, by rfl⟩ : syracuseStep 1697103 = 2545655) B2545655
theorem B5432663 : Blo 1695548 5432663 := bstep (se 1 (by rfl) ⟨4074497, by rfl⟩ : syracuseStep 5432663 = 8148995) B8148995
theorem B1697119 : Blo 1695548 1697119 := bstep (se 1 (by rfl) ⟨1272839, by rfl⟩ : syracuseStep 1697119 = 2545679) B2545679
theorem B1697147 : Blo 1695548 1697147 := bstep (se 1 (by rfl) ⟨1272860, by rfl⟩ : syracuseStep 1697147 = 2545721) B2545721
theorem B5727617 : Blo 1695548 5727617 := bstep (se 2 (by rfl) ⟨2147856, by rfl⟩ : syracuseStep 5727617 = 4295713) B4295713
theorem B3220897 : Blo 1695548 3220897 := bstep (se 2 (by rfl) ⟨1207836, by rfl⟩ : syracuseStep 3220897 = 2415673) B2415673
theorem B1697199 : Blo 1695548 1697199 := bstep (se 1 (by rfl) ⟨1272899, by rfl⟩ : syracuseStep 1697199 = 2545799) B2545799
theorem B1697223 : Blo 1695548 1697223 := bstep (se 1 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 1697223 = 2545835) B2545835
theorem B6440411 : Blo 1695548 6440411 := bstep (se 1 (by rfl) ⟨4830308, by rfl⟩ : syracuseStep 6440411 = 9660617) B9660617
theorem B1697243 : Blo 1695548 1697243 := bstep (se 1 (by rfl) ⟨1272932, by rfl⟩ : syracuseStep 1697243 = 2545865) B2545865
theorem B11609639 : Blo 1695548 11609639 := bstep (se 1 (by rfl) ⟨8707229, by rfl⟩ : syracuseStep 11609639 = 17414459) B17414459
theorem B1812007 : Blo 1695548 1812007 := bstep (se 1 (by rfl) ⟨1359005, by rfl⟩ : syracuseStep 1812007 = 2718011) B2718011
theorem B1697319 : Blo 1695548 1697319 := bstep (se 1 (by rfl) ⟨1272989, by rfl⟩ : syracuseStep 1697319 = 2545979) B2545979
theorem B1697359 : Blo 1695548 1697359 := bstep (se 1 (by rfl) ⟨1273019, by rfl⟩ : syracuseStep 1697359 = 2546039) B2546039
theorem B1697375 : Blo 1695548 1697375 := bstep (se 1 (by rfl) ⟨1273031, by rfl⟩ : syracuseStep 1697375 = 2546063) B2546063
theorem B3819131 : Blo 1695548 3819131 := bstep (se 1 (by rfl) ⟨2864348, by rfl⟩ : syracuseStep 3819131 = 5728697) B5728697
theorem B1697403 : Blo 1695548 1697403 := bstep (se 1 (by rfl) ⟨1273052, by rfl⟩ : syracuseStep 1697403 = 2546105) B2546105
theorem B1697455 : Blo 1695548 1697455 := bstep (se 1 (by rfl) ⟨1273091, by rfl⟩ : syracuseStep 1697455 = 2546183) B2546183
theorem B1697479 : Blo 1695548 1697479 := bstep (se 1 (by rfl) ⟨1273109, by rfl⟩ : syracuseStep 1697479 = 2546219) B2546219
theorem B1697499 : Blo 1695548 1697499 := bstep (se 1 (by rfl) ⟨1273124, by rfl⟩ : syracuseStep 1697499 = 2546249) B2546249
theorem B3057401 : Blo 1695548 3057401 := bstep (se 2 (by rfl) ⟨1146525, by rfl⟩ : syracuseStep 3057401 = 2293051) B2293051
theorem B3819257 : Blo 1695548 3819257 := bstep (se 2 (by rfl) ⟨1432221, by rfl⟩ : syracuseStep 3819257 = 2864443) B2864443
theorem B2754523 : Blo 1695548 2754523 := bstep (se 1 (by rfl) ⟨2065892, by rfl⟩ : syracuseStep 2754523 = 4131785) B4131785
theorem B13060133 : Blo 1695548 13060133 := bstep (se 4 (by rfl) ⟨1224387, by rfl⟩ : syracuseStep 13060133 = 2448775) B2448775
theorem B11602001 : Blo 1695548 11602001 := bstep (se 2 (by rfl) ⟨4350750, by rfl⟩ : syracuseStep 11602001 = 8701501) B8701501
theorem B5728427 : Blo 1695548 5728427 := bstep (se 1 (by rfl) ⟨4296320, by rfl⟩ : syracuseStep 5728427 = 8592641) B8592641
theorem B4294903 : Blo 1695548 4294903 := bstep (se 1 (by rfl) ⟨3221177, by rfl⟩ : syracuseStep 4294903 = 6442355) B6442355
theorem B2861419 : Blo 1695548 2861419 := bstep (se 1 (by rfl) ⟨2146064, by rfl⟩ : syracuseStep 2861419 = 4292129) B4292129
theorem B10873217 : Blo 1695548 10873217 := bstep (se 2 (by rfl) ⟨4077456, by rfl⟩ : syracuseStep 10873217 = 8154913) B8154913
theorem B4295177 : Blo 1695548 4295177 := bstep (se 2 (by rfl) ⟨1610691, by rfl⟩ : syracuseStep 4295177 = 3221383) B3221383
theorem B4295207 : Blo 1695548 4295207 := bstep (se 1 (by rfl) ⟨3221405, by rfl⟩ : syracuseStep 4295207 = 6442811) B6442811
theorem B7244423 : Blo 1695548 7244423 := bstep (se 1 (by rfl) ⟨5433317, by rfl⟩ : syracuseStep 7244423 = 10866635) B10866635
theorem B6113981 : Blo 1695548 6113981 := bstep (se 3 (by rfl) ⟨1146371, by rfl⟩ : syracuseStep 6113981 = 2292743) B2292743
theorem B5728967 : Blo 1695548 5728967 := bstep (se 1 (by rfl) ⟨4296725, by rfl⟩ : syracuseStep 5728967 = 8593451) B8593451
theorem B16534217 : Blo 1695548 16534217 := bstep (se 2 (by rfl) ⟨6200331, by rfl⟩ : syracuseStep 16534217 = 12400663) B12400663
theorem B4352723 : Blo 1695548 4352723 := bstep (se 1 (by rfl) ⟨3264542, by rfl⟩ : syracuseStep 4352723 = 6529085) B6529085
theorem B8588105 : Blo 1695548 8588105 := bstep (se 2 (by rfl) ⟨3220539, by rfl⟩ : syracuseStep 8588105 = 6441079) B6441079
theorem B4295531 : Blo 1695548 4295531 := bstep (se 1 (by rfl) ⟨3221648, by rfl⟩ : syracuseStep 4295531 = 6443297) B6443297
theorem B18599203 : Blo 1695548 18599203 := bstep (se 1 (by rfl) ⟨13949402, by rfl⟩ : syracuseStep 18599203 = 27898805) B27898805
theorem B2862479 : Blo 1695548 2862479 := bstep (se 1 (by rfl) ⟨2146859, by rfl⟩ : syracuseStep 2862479 = 4293719) B4293719
theorem B4296179 : Blo 1695548 4296179 := bstep (se 1 (by rfl) ⟨3222134, by rfl⟩ : syracuseStep 4296179 = 6444269) B6444269
theorem B2862715 : Blo 1695548 2862715 := bstep (se 1 (by rfl) ⟨2147036, by rfl⟩ : syracuseStep 2862715 = 4294073) B4294073
theorem B9662075 : Blo 1695548 9662075 := bstep (se 1 (by rfl) ⟨7246556, by rfl⟩ : syracuseStep 9662075 = 14493113) B14493113
theorem B27512453 : Blo 1695548 27512453 := bstep (se 4 (by rfl) ⟨2579292, by rfl⟩ : syracuseStep 27512453 = 5158585) B5158585
theorem B2543465 : Blo 1695548 2543465 := bstep (se 2 (by rfl) ⟨953799, by rfl⟩ : syracuseStep 2543465 = 1907599) B1907599
theorem B9662327 : Blo 1695548 9662327 := bstep (se 1 (by rfl) ⟨7246745, by rfl⟩ : syracuseStep 9662327 = 14493491) B14493491
theorem B2543543 : Blo 1695548 2543543 := bstep (se 1 (by rfl) ⟨1907657, by rfl⟩ : syracuseStep 2543543 = 3815315) B3815315
theorem B4296635 : Blo 1695548 4296635 := bstep (se 1 (by rfl) ⟨3222476, by rfl⟩ : syracuseStep 4296635 = 6444953) B6444953
theorem B2543579 : Blo 1695548 2543579 := bstep (se 1 (by rfl) ⟨1907684, by rfl⟩ : syracuseStep 2543579 = 3815369) B3815369
theorem B6443009 : Blo 1695548 6443009 := bstep (se 2 (by rfl) ⟨2416128, by rfl⟩ : syracuseStep 6443009 = 4832257) B4832257
theorem B6443023 : Blo 1695548 6443023 := bstep (se 1 (by rfl) ⟨4832267, by rfl⟩ : syracuseStep 6443023 = 9664535) B9664535
theorem B5156921 : Blo 1695548 5156921 := bstep (se 2 (by rfl) ⟨1933845, by rfl⟩ : syracuseStep 5156921 = 3867691) B3867691
theorem B8589401 : Blo 1695548 8589401 := bstep (se 2 (by rfl) ⟨3221025, by rfl⟩ : syracuseStep 8589401 = 6442051) B6442051
theorem B4829341 : Blo 1695548 4829341 := bstep (se 3 (by rfl) ⟨905501, by rfl⟩ : syracuseStep 4829341 = 1811003) B1811003
theorem B14487781 : Blo 1695548 14487781 := bstep (se 4 (by rfl) ⟨1358229, by rfl⟩ : syracuseStep 14487781 = 2716459) B2716459
theorem B7065917 : Blo 1695548 7065917 := bstep (se 3 (by rfl) ⟨1324859, by rfl⟩ : syracuseStep 7065917 = 2649719) B2649719
theorem B18338177 : Blo 1695548 18338177 := bstep (se 2 (by rfl) ⟨6876816, by rfl⟩ : syracuseStep 18338177 = 13753633) B13753633
theorem B12743041 : Blo 1695548 12743041 := bstep (se 2 (by rfl) ⟨4778640, by rfl⟩ : syracuseStep 12743041 = 9557281) B9557281
theorem B2544047 : Blo 1695548 2544047 := bstep (se 1 (by rfl) ⟨1908035, by rfl⟩ : syracuseStep 2544047 = 3816071) B3816071
theorem B2863579 : Blo 1695548 2863579 := bstep (se 1 (by rfl) ⟨2147684, by rfl⟩ : syracuseStep 2863579 = 4295369) B4295369
theorem B2544137 : Blo 1695548 2544137 := bstep (se 2 (by rfl) ⟨954051, by rfl⟩ : syracuseStep 2544137 = 1908103) B1908103
theorem B5722649 : Blo 1695548 5722649 := bstep (se 2 (by rfl) ⟨2145993, by rfl⟩ : syracuseStep 5722649 = 4291987) B4291987
theorem B2544167 : Blo 1695548 2544167 := bstep (se 1 (by rfl) ⟨1908125, by rfl⟩ : syracuseStep 2544167 = 3816251) B3816251
theorem B2544251 : Blo 1695548 2544251 := bstep (se 1 (by rfl) ⟨1908188, by rfl⟩ : syracuseStep 2544251 = 3816377) B3816377
theorem B2544377 : Blo 1695548 2544377 := bstep (se 2 (by rfl) ⟨954141, by rfl⟩ : syracuseStep 2544377 = 1908283) B1908283
theorem B2544479 : Blo 1695548 2544479 := bstep (se 1 (by rfl) ⟨1908359, by rfl⟩ : syracuseStep 2544479 = 3816719) B3816719
theorem B2544491 : Blo 1695548 2544491 := bstep (se 1 (by rfl) ⟨1908368, by rfl⟩ : syracuseStep 2544491 = 3816737) B3816737
theorem B167613401 : Blo 1695548 167613401 := bstep (se 2 (by rfl) ⟨62855025, by rfl⟩ : syracuseStep 167613401 = 125710051) B125710051
theorem B22025267 : Blo 1695548 22025267 := bstep (se 1 (by rfl) ⟨16518950, by rfl⟩ : syracuseStep 22025267 = 33037901) B33037901
theorem B2544719 : Blo 1695548 2544719 := bstep (se 1 (by rfl) ⟨1908539, by rfl⟩ : syracuseStep 2544719 = 3817079) B3817079
theorem B2864207 : Blo 1695548 2864207 := bstep (se 1 (by rfl) ⟨2148155, by rfl⟩ : syracuseStep 2864207 = 4296311) B4296311
theorem B2544839 : Blo 1695548 2544839 := bstep (se 1 (by rfl) ⟨1908629, by rfl⟩ : syracuseStep 2544839 = 3817259) B3817259
theorem B6444299 : Blo 1695548 6444299 := bstep (se 1 (by rfl) ⟨4833224, by rfl⟩ : syracuseStep 6444299 = 9666449) B9666449
theorem B2545001 : Blo 1695548 2545001 := bstep (se 2 (by rfl) ⟨954375, by rfl⟩ : syracuseStep 2545001 = 1908751) B1908751
theorem B10868093 : Blo 1695548 10868093 := bstep (se 3 (by rfl) ⟨2037767, by rfl⟩ : syracuseStep 10868093 = 4075535) B4075535
theorem B12883373 : Blo 1695548 12883373 := bstep (se 3 (by rfl) ⟨2415632, by rfl⟩ : syracuseStep 12883373 = 4831265) B4831265
theorem B2545079 : Blo 1695548 2545079 := bstep (se 1 (by rfl) ⟨1908809, by rfl⟩ : syracuseStep 2545079 = 3817619) B3817619
theorem B2545115 : Blo 1695548 2545115 := bstep (se 1 (by rfl) ⟨1908836, by rfl⟩ : syracuseStep 2545115 = 3817673) B3817673
theorem B16307675 : Blo 1695548 16307675 := bstep (se 1 (by rfl) ⟨12230756, by rfl⟩ : syracuseStep 16307675 = 24461513) B24461513
theorem B3815009 : Blo 1695548 3815009 := bstep (se 2 (by rfl) ⟨1430628, by rfl⟩ : syracuseStep 3815009 = 2861257) B2861257
theorem B5723783 : Blo 1695548 5723783 := bstep (se 1 (by rfl) ⟨4292837, by rfl⟩ : syracuseStep 5723783 = 8585675) B8585675
theorem B13751947 : Blo 1695548 13751947 := bstep (se 1 (by rfl) ⟨10313960, by rfl⟩ : syracuseStep 13751947 = 20627921) B20627921
theorem B9295505 : Blo 1695548 9295505 := bstep (se 2 (by rfl) ⟨3485814, by rfl⟩ : syracuseStep 9295505 = 6971629) B6971629
theorem B10319507 : Blo 1695548 10319507 := bstep (se 1 (by rfl) ⟨7739630, by rfl⟩ : syracuseStep 10319507 = 15479261) B15479261
theorem B5723837 : Blo 1695548 5723837 := bstep (se 3 (by rfl) ⟨1073219, by rfl⟩ : syracuseStep 5723837 = 2146439) B2146439
theorem B6444755 : Blo 1695548 6444755 := bstep (se 1 (by rfl) ⟨4833566, by rfl⟩ : syracuseStep 6444755 = 9667133) B9667133
theorem B5723999 : Blo 1695548 5723999 := bstep (se 1 (by rfl) ⟨4292999, by rfl⟩ : syracuseStep 5723999 = 8585999) B8585999
theorem B2414443 : Blo 1695548 2414443 := bstep (se 1 (by rfl) ⟨1810832, by rfl⟩ : syracuseStep 2414443 = 3621665) B3621665
theorem B2545583 : Blo 1695548 2545583 := bstep (se 1 (by rfl) ⟨1909187, by rfl⟩ : syracuseStep 2545583 = 3818375) B3818375
theorem B3815351 : Blo 1695548 3815351 := bstep (se 1 (by rfl) ⟨2861513, by rfl⟩ : syracuseStep 3815351 = 5723027) B5723027
theorem B5724161 : Blo 1695548 5724161 := bstep (se 2 (by rfl) ⟨2146560, by rfl⟩ : syracuseStep 5724161 = 4293121) B4293121
theorem B2545673 : Blo 1695548 2545673 := bstep (se 2 (by rfl) ⟨954627, by rfl⟩ : syracuseStep 2545673 = 1909255) B1909255
theorem B13752335 : Blo 1695548 13752335 := bstep (se 1 (by rfl) ⟨10314251, by rfl⟩ : syracuseStep 13752335 = 20628503) B20628503
theorem B2545703 : Blo 1695548 2545703 := bstep (se 1 (by rfl) ⟨1909277, by rfl⟩ : syracuseStep 2545703 = 3818555) B3818555
theorem B4831289 : Blo 1695548 4831289 := bstep (se 2 (by rfl) ⟨1811733, by rfl⟩ : syracuseStep 4831289 = 3623467) B3623467
theorem B2545787 : Blo 1695548 2545787 := bstep (se 1 (by rfl) ⟨1909340, by rfl⟩ : syracuseStep 2545787 = 3818681) B3818681
theorem B2545913 : Blo 1695548 2545913 := bstep (se 2 (by rfl) ⟨954717, by rfl⟩ : syracuseStep 2545913 = 1909435) B1909435
theorem B43473185 : Blo 1695548 43473185 := bstep (se 2 (by rfl) ⟨16302444, by rfl⟩ : syracuseStep 43473185 = 32604889) B32604889
theorem B12876083 : Blo 1695548 12876083 := bstep (se 1 (by rfl) ⟨9657062, by rfl⟩ : syracuseStep 12876083 = 19314125) B19314125
theorem B2546015 : Blo 1695548 2546015 := bstep (se 1 (by rfl) ⟨1909511, by rfl⟩ : syracuseStep 2546015 = 3819023) B3819023
theorem B2546027 : Blo 1695548 2546027 := bstep (se 1 (by rfl) ⟨1909520, by rfl⟩ : syracuseStep 2546027 = 3819041) B3819041
theorem B48888197 : Blo 1695548 48888197 := bstep (se 4 (by rfl) ⟨4583268, by rfl⟩ : syracuseStep 48888197 = 9166537) B9166537
theorem B2292143 : Blo 1695548 2292143 := bstep (se 1 (by rfl) ⟨1719107, by rfl⟩ : syracuseStep 2292143 = 3438215) B3438215
theorem B3815945 : Blo 1695548 3815945 := bstep (se 2 (by rfl) ⟨1430979, by rfl⟩ : syracuseStep 3815945 = 2861959) B2861959
theorem B2415143 : Blo 1695548 2415143 := bstep (se 1 (by rfl) ⟨1811357, by rfl⟩ : syracuseStep 2415143 = 3622715) B3622715
theorem B2546255 : Blo 1695548 2546255 := bstep (se 1 (by rfl) ⟨1909691, by rfl⟩ : syracuseStep 2546255 = 3819383) B3819383
theorem B2718407 : Blo 1695548 2718407 := bstep (se 1 (by rfl) ⟨2038805, by rfl⟩ : syracuseStep 2718407 = 4077611) B4077611
theorem B4078295 : Blo 1695548 4078295 := bstep (se 1 (by rfl) ⟨3058721, by rfl⟩ : syracuseStep 4078295 = 6117443) B6117443
theorem B5724971 : Blo 1695548 5724971 := bstep (se 1 (by rfl) ⟨4293728, by rfl⟩ : syracuseStep 5724971 = 8587457) B8587457
theorem B3816287 : Blo 1695548 3816287 := bstep (se 1 (by rfl) ⟨2862215, by rfl⟩ : syracuseStep 3816287 = 5724431) B5724431
theorem B8706923 : Blo 1695548 8706923 := bstep (se 1 (by rfl) ⟨6530192, by rfl⟩ : syracuseStep 8706923 = 13060385) B13060385
theorem B14490515 : Blo 1695548 14490515 := bstep (se 1 (by rfl) ⟨10867886, by rfl⟩ : syracuseStep 14490515 = 21735773) B21735773
theorem B3816467 : Blo 1695548 3816467 := bstep (se 1 (by rfl) ⟨2862350, by rfl⟩ : syracuseStep 3816467 = 5724701) B5724701
theorem B8821811 : Blo 1695548 8821811 := bstep (se 1 (by rfl) ⟨6616358, by rfl⟩ : syracuseStep 8821811 = 13232717) B13232717
theorem B5725241 : Blo 1695548 5725241 := bstep (se 2 (by rfl) ⟨2146965, by rfl⟩ : syracuseStep 5725241 = 4293931) B4293931
theorem B4078649 : Blo 1695548 4078649 := bstep (se 2 (by rfl) ⟨1529493, by rfl⟩ : syracuseStep 4078649 = 3058987) B3058987
theorem B20643011 : Blo 1695548 20643011 := bstep (se 1 (by rfl) ⟨15482258, by rfl⟩ : syracuseStep 20643011 = 30964517) B30964517
theorem B9796855 : Blo 1695548 9796855 := bstep (se 1 (by rfl) ⟨7347641, by rfl⟩ : syracuseStep 9796855 = 14695283) B14695283
theorem B6200567 : Blo 1695548 6200567 := bstep (se 1 (by rfl) ⟨4650425, by rfl⟩ : syracuseStep 6200567 = 9300851) B9300851
theorem B5807351 : Blo 1695548 5807351 := bstep (se 1 (by rfl) ⟨4355513, by rfl⟩ : syracuseStep 5807351 = 8711027) B8711027
theorem B3816809 : Blo 1695548 3816809 := bstep (se 2 (by rfl) ⟨1431303, by rfl⟩ : syracuseStep 3816809 = 2862607) B2862607
theorem B5725565 : Blo 1695548 5725565 := bstep (se 3 (by rfl) ⟨1073543, by rfl⟩ : syracuseStep 5725565 = 2147087) B2147087
theorem B9665993 : Blo 1695548 9665993 := bstep (se 2 (by rfl) ⟨3624747, by rfl⟩ : syracuseStep 9665993 = 7249495) B7249495
theorem B3218953 : Blo 1695548 3218953 := bstep (se 2 (by rfl) ⟨1207107, by rfl⟩ : syracuseStep 3218953 = 2414215) B2414215
theorem B9657953 : Blo 1695548 9657953 := bstep (se 2 (by rfl) ⟨3621732, by rfl⟩ : syracuseStep 9657953 = 7243465) B7243465
theorem B4587131 : Blo 1695548 4587131 := bstep (se 1 (by rfl) ⟨3440348, by rfl⟩ : syracuseStep 4587131 = 6880697) B6880697
theorem B5725835 : Blo 1695548 5725835 := bstep (se 1 (by rfl) ⟨4294376, by rfl⟩ : syracuseStep 5725835 = 8588753) B8588753
theorem B4292311 : Blo 1695548 4292311 := bstep (se 1 (by rfl) ⟨3219233, by rfl⟩ : syracuseStep 4292311 = 6438467) B6438467
theorem B6438649 : Blo 1695548 6438649 := bstep (se 2 (by rfl) ⟨2414493, by rfl⟩ : syracuseStep 6438649 = 4828987) B4828987
theorem B12885803 : Blo 1695548 12885803 := bstep (se 1 (by rfl) ⟨9664352, by rfl⟩ : syracuseStep 12885803 = 19328705) B19328705
theorem B8585027 : Blo 1695548 8585027 := bstep (se 1 (by rfl) ⟨6438770, by rfl⟩ : syracuseStep 8585027 = 12877541) B12877541
theorem B1695567 : Blo 1695548 1695567 := bstep (se 1 (by rfl) ⟨1271675, by rfl⟩ : syracuseStep 1695567 = 2543351) B2543351
theorem B1695583 : Blo 1695548 1695583 := bstep (se 1 (by rfl) ⟨1271687, by rfl⟩ : syracuseStep 1695583 = 2543375) B2543375
theorem B1695611 : Blo 1695548 1695611 := bstep (se 1 (by rfl) ⟨1271708, by rfl⟩ : syracuseStep 1695611 = 2543417) B2543417
theorem B1695663 : Blo 1695548 1695663 := bstep (se 1 (by rfl) ⟨1271747, by rfl⟩ : syracuseStep 1695663 = 2543495) B2543495
theorem B2416567 : Blo 1695548 2416567 := bstep (se 1 (by rfl) ⟨1812425, by rfl⟩ : syracuseStep 2416567 = 3624851) B3624851
theorem B3817403 : Blo 1695548 3817403 := bstep (se 1 (by rfl) ⟨2863052, by rfl⟩ : syracuseStep 3817403 = 5726105) B5726105
theorem B9174971 : Blo 1695548 9174971 := bstep (se 1 (by rfl) ⟨6881228, by rfl⟩ : syracuseStep 9174971 = 13762457) B13762457
theorem B1695687 : Blo 1695548 1695687 := bstep (se 1 (by rfl) ⟨1271765, by rfl⟩ : syracuseStep 1695687 = 2543531) B2543531
theorem B1695707 : Blo 1695548 1695707 := bstep (se 1 (by rfl) ⟨1271780, by rfl⟩ : syracuseStep 1695707 = 2543561) B2543561
theorem B2146267 : Blo 1695548 2146267 := bstep (se 1 (by rfl) ⟨1609700, by rfl⟩ : syracuseStep 2146267 = 3219401) B3219401
theorem B1720283 : Blo 1695548 1720283 := bstep (se 1 (by rfl) ⟨1290212, by rfl⟩ : syracuseStep 1720283 = 2580425) B2580425
theorem B5726267 : Blo 1695548 5726267 := bstep (se 1 (by rfl) ⟨4294700, by rfl⟩ : syracuseStep 5726267 = 8589401) B8589401
theorem B6439121 : Blo 1695548 6439121 := bstep (se 2 (by rfl) ⟨2414670, by rfl⟩ : syracuseStep 6439121 = 4829341) B4829341
theorem B4710611 : Blo 1695548 4710611 := bstep (se 1 (by rfl) ⟨3532958, by rfl⟩ : syracuseStep 4710611 = 7065917) B7065917
theorem B1696031 : Blo 1695548 1696031 := bstep (se 1 (by rfl) ⟨1272023, by rfl⟩ : syracuseStep 1696031 = 2544047) B2544047
theorem B2146591 : Blo 1695548 2146591 := bstep (se 1 (by rfl) ⟨1609943, by rfl⟩ : syracuseStep 2146591 = 3219887) B3219887
theorem B19317041 : Blo 1695548 19317041 := bstep (se 2 (by rfl) ⟨7243890, by rfl⟩ : syracuseStep 19317041 = 14487781) B14487781
theorem B5726537 : Blo 1695548 5726537 := bstep (se 2 (by rfl) ⟨2147451, by rfl⟩ : syracuseStep 5726537 = 4294903) B4294903
theorem B1696091 : Blo 1695548 1696091 := bstep (se 1 (by rfl) ⟨1272068, by rfl⟩ : syracuseStep 1696091 = 2544137) B2544137
theorem B3817835 : Blo 1695548 3817835 := bstep (se 1 (by rfl) ⟨2863376, by rfl⟩ : syracuseStep 3817835 = 5726753) B5726753
theorem B1696111 : Blo 1695548 1696111 := bstep (se 1 (by rfl) ⟨1272083, by rfl⟩ : syracuseStep 1696111 = 2544167) B2544167
theorem B1696167 : Blo 1695548 1696167 := bstep (se 1 (by rfl) ⟨1272125, by rfl⟩ : syracuseStep 1696167 = 2544251) B2544251
theorem B1696251 : Blo 1695548 1696251 := bstep (se 1 (by rfl) ⟨1272188, by rfl⟩ : syracuseStep 1696251 = 2544377) B2544377
theorem B3817979 : Blo 1695548 3817979 := bstep (se 1 (by rfl) ⟨2863484, by rfl⟩ : syracuseStep 3817979 = 5726969) B5726969
theorem B16990721 : Blo 1695548 16990721 := bstep (se 2 (by rfl) ⟨6371520, by rfl⟩ : syracuseStep 16990721 = 12743041) B12743041
theorem B1696319 : Blo 1695548 1696319 := bstep (se 1 (by rfl) ⟨1272239, by rfl⟩ : syracuseStep 1696319 = 2544479) B2544479
theorem B1696327 : Blo 1695548 1696327 := bstep (se 1 (by rfl) ⟨1272245, by rfl⟩ : syracuseStep 1696327 = 2544491) B2544491
theorem B4833863 : Blo 1695548 4833863 := bstep (se 1 (by rfl) ⟨3625397, by rfl⟩ : syracuseStep 4833863 = 7250795) B7250795
theorem B3818105 : Blo 1695548 3818105 := bstep (se 2 (by rfl) ⟨1431789, by rfl⟩ : syracuseStep 3818105 = 2863579) B2863579
theorem B3818159 : Blo 1695548 3818159 := bstep (se 1 (by rfl) ⟨2863619, by rfl⟩ : syracuseStep 3818159 = 5727239) B5727239
theorem B6439607 : Blo 1695548 6439607 := bstep (se 1 (by rfl) ⟨4829705, by rfl⟩ : syracuseStep 6439607 = 9659411) B9659411
theorem B1696479 : Blo 1695548 1696479 := bstep (se 1 (by rfl) ⟨1272359, by rfl⟩ : syracuseStep 1696479 = 2544719) B2544719
theorem B1909471 : Blo 1695548 1909471 := bstep (se 1 (by rfl) ⟨1432103, by rfl⟩ : syracuseStep 1909471 = 2864207) B2864207
theorem B3818231 : Blo 1695548 3818231 := bstep (se 1 (by rfl) ⟨2863673, by rfl⟩ : syracuseStep 3818231 = 5727347) B5727347
theorem B4293395 : Blo 1695548 4293395 := bstep (se 1 (by rfl) ⟨3220046, by rfl⟩ : syracuseStep 4293395 = 6440093) B6440093
theorem B1696559 : Blo 1695548 1696559 := bstep (se 1 (by rfl) ⟨1272419, by rfl⟩ : syracuseStep 1696559 = 2544839) B2544839
theorem B3621775 : Blo 1695548 3621775 := bstep (se 1 (by rfl) ⟨2716331, by rfl⟩ : syracuseStep 3621775 = 5432663) B5432663
theorem B1696667 : Blo 1695548 1696667 := bstep (se 1 (by rfl) ⟨1272500, by rfl⟩ : syracuseStep 1696667 = 2545001) B2545001
theorem B3818411 : Blo 1695548 3818411 := bstep (se 1 (by rfl) ⟨2863808, by rfl⟩ : syracuseStep 3818411 = 5727617) B5727617
theorem B1696719 : Blo 1695548 1696719 := bstep (se 1 (by rfl) ⟨1272539, by rfl⟩ : syracuseStep 1696719 = 2545079) B2545079
theorem B4293607 : Blo 1695548 4293607 := bstep (se 1 (by rfl) ⟨3220205, by rfl⟩ : syracuseStep 4293607 = 6440411) B6440411
theorem B1696743 : Blo 1695548 1696743 := bstep (se 1 (by rfl) ⟨1272557, by rfl⟩ : syracuseStep 1696743 = 2545115) B2545115
theorem B10871783 : Blo 1695548 10871783 := bstep (se 1 (by rfl) ⟨8153837, by rfl⟩ : syracuseStep 10871783 = 16307675) B16307675
theorem B6112381 : Blo 1695548 6112381 := bstep (se 3 (by rfl) ⟨1146071, by rfl⟩ : syracuseStep 6112381 = 2292143) B2292143
theorem B4293881 : Blo 1695548 4293881 := bstep (se 2 (by rfl) ⟨1610205, by rfl⟩ : syracuseStep 4293881 = 3220411) B3220411
theorem B1697055 : Blo 1695548 1697055 := bstep (se 1 (by rfl) ⟨1272791, by rfl⟩ : syracuseStep 1697055 = 2545583) B2545583
theorem B1697115 : Blo 1695548 1697115 := bstep (se 1 (by rfl) ⟨1272836, by rfl⟩ : syracuseStep 1697115 = 2545673) B2545673
theorem B9168223 : Blo 1695548 9168223 := bstep (se 1 (by rfl) ⟨6876167, by rfl⟩ : syracuseStep 9168223 = 13752335) B13752335
theorem B1697135 : Blo 1695548 1697135 := bstep (se 1 (by rfl) ⟨1272851, by rfl⟩ : syracuseStep 1697135 = 2545703) B2545703
theorem B3220859 : Blo 1695548 3220859 := bstep (se 1 (by rfl) ⟨2415644, by rfl⟩ : syracuseStep 3220859 = 4831289) B4831289
theorem B1697191 : Blo 1695548 1697191 := bstep (se 1 (by rfl) ⟨1272893, by rfl⟩ : syracuseStep 1697191 = 2545787) B2545787
theorem B6440381 : Blo 1695548 6440381 := bstep (se 3 (by rfl) ⟨1207571, by rfl⟩ : syracuseStep 6440381 = 2415143) B2415143
theorem B3818951 : Blo 1695548 3818951 := bstep (se 1 (by rfl) ⟨2864213, by rfl⟩ : syracuseStep 3818951 = 5728427) B5728427
theorem B1697275 : Blo 1695548 1697275 := bstep (se 1 (by rfl) ⟨1272956, by rfl⟩ : syracuseStep 1697275 = 2545913) B2545913
theorem B8586809 : Blo 1695548 8586809 := bstep (se 2 (by rfl) ⟨3220053, by rfl⟩ : syracuseStep 8586809 = 6440107) B6440107
theorem B1697343 : Blo 1695548 1697343 := bstep (se 1 (by rfl) ⟨1273007, by rfl⟩ : syracuseStep 1697343 = 2546015) B2546015
theorem B1697351 : Blo 1695548 1697351 := bstep (se 1 (by rfl) ⟨1273013, by rfl⟩ : syracuseStep 1697351 = 2546027) B2546027
theorem B1697503 : Blo 1695548 1697503 := bstep (se 1 (by rfl) ⟨1273127, by rfl⟩ : syracuseStep 1697503 = 2546255) B2546255
theorem B3819311 : Blo 1695548 3819311 := bstep (se 1 (by rfl) ⟨2864483, by rfl⟩ : syracuseStep 3819311 = 5728967) B5728967
theorem B2901815 : Blo 1695548 2901815 := bstep (se 1 (by rfl) ⟨2176361, by rfl⟩ : syracuseStep 2901815 = 4352723) B4352723
theorem B16303949 : Blo 1695548 16303949 := bstep (se 3 (by rfl) ⟨3056990, by rfl⟩ : syracuseStep 16303949 = 6113981) B6113981
theorem B44091245 : Blo 1695548 44091245 := bstep (se 3 (by rfl) ⟨8267108, by rfl⟩ : syracuseStep 44091245 = 16534217) B16534217
theorem B4294529 : Blo 1695548 4294529 := bstep (se 2 (by rfl) ⟨1610448, by rfl⟩ : syracuseStep 4294529 = 3220897) B3220897
theorem B9660343 : Blo 1695548 9660343 := bstep (se 1 (by rfl) ⟨7245257, by rfl⟩ : syracuseStep 9660343 = 14490515) B14490515
theorem B18335929 : Blo 1695548 18335929 := bstep (se 2 (by rfl) ⟨6875973, by rfl⟩ : syracuseStep 18335929 = 13751947) B13751947
theorem B6441383 : Blo 1695548 6441383 := bstep (se 1 (by rfl) ⟨4831037, by rfl⟩ : syracuseStep 6441383 = 9662075) B9662075
theorem B3058087 : Blo 1695548 3058087 := bstep (se 1 (by rfl) ⟨2293565, by rfl⟩ : syracuseStep 3058087 = 4587131) B4587131
theorem B3222089 : Blo 1695548 3222089 := bstep (se 2 (by rfl) ⟨1208283, by rfl⟩ : syracuseStep 3222089 = 2416567) B2416567
theorem B6441551 : Blo 1695548 6441551 := bstep (se 1 (by rfl) ⟨4831163, by rfl⟩ : syracuseStep 6441551 = 9662327) B9662327
theorem B2861689 : Blo 1695548 2861689 := bstep (se 2 (by rfl) ⟨1073133, by rfl⟩ : syracuseStep 2861689 = 2146267) B2146267
theorem B3672697 : Blo 1695548 3672697 := bstep (se 2 (by rfl) ⟨1377261, by rfl⟩ : syracuseStep 3672697 = 2754523) B2754523
theorem B4295339 : Blo 1695548 4295339 := bstep (se 1 (by rfl) ⟨3221504, by rfl⟩ : syracuseStep 4295339 = 6443009) B6443009
theorem B2861743 : Blo 1695548 2861743 := bstep (se 1 (by rfl) ⟨2146307, by rfl⟩ : syracuseStep 2861743 = 4292615) B4292615
theorem B12225451 : Blo 1695548 12225451 := bstep (se 1 (by rfl) ⟨9169088, by rfl⟩ : syracuseStep 12225451 = 18338177) B18338177
theorem B15477875 : Blo 1695548 15477875 := bstep (se 1 (by rfl) ⟨11608406, by rfl⟩ : syracuseStep 15477875 = 23216813) B23216813
theorem B9301115 : Blo 1695548 9301115 := bstep (se 1 (by rfl) ⟨6975836, by rfl⟩ : syracuseStep 9301115 = 13951673) B13951673
theorem B4828349 : Blo 1695548 4828349 := bstep (se 3 (by rfl) ⟨905315, by rfl⟩ : syracuseStep 4828349 = 1810631) B1810631
theorem B111742267 : Blo 1695548 111742267 := bstep (se 1 (by rfl) ⟨83806700, by rfl⟩ : syracuseStep 111742267 = 167613401) B167613401
theorem B14683511 : Blo 1695548 14683511 := bstep (se 1 (by rfl) ⟨11012633, by rfl⟩ : syracuseStep 14683511 = 22025267) B22025267
theorem B4648315 : Blo 1695548 4648315 := bstep (se 1 (by rfl) ⟨3486236, by rfl⟩ : syracuseStep 4648315 = 6972473) B6972473
theorem B4296199 : Blo 1695548 4296199 := bstep (se 1 (by rfl) ⟨3222149, by rfl⟩ : syracuseStep 4296199 = 6444299) B6444299
theorem B7245395 : Blo 1695548 7245395 := bstep (se 1 (by rfl) ⟨5434046, by rfl⟩ : syracuseStep 7245395 = 10868093) B10868093
theorem B8588915 : Blo 1695548 8588915 := bstep (se 1 (by rfl) ⟨6441686, by rfl⟩ : syracuseStep 8588915 = 12883373) B12883373
theorem B28995245 : Blo 1695548 28995245 := bstep (se 3 (by rfl) ⟨5436608, by rfl⟩ : syracuseStep 28995245 = 10873217) B10873217
theorem B2543339 : Blo 1695548 2543339 := bstep (se 1 (by rfl) ⟨1907504, by rfl⟩ : syracuseStep 2543339 = 3815009) B3815009
theorem B6197003 : Blo 1695548 6197003 := bstep (se 1 (by rfl) ⟨4647752, by rfl⟩ : syracuseStep 6197003 = 9295505) B9295505
theorem B4296503 : Blo 1695548 4296503 := bstep (se 1 (by rfl) ⟨3222377, by rfl⟩ : syracuseStep 4296503 = 6444755) B6444755
theorem B2543567 : Blo 1695548 2543567 := bstep (se 1 (by rfl) ⟨1907675, by rfl⟩ : syracuseStep 2543567 = 3815351) B3815351
theorem B16527361 : Blo 1695548 16527361 := bstep (se 2 (by rfl) ⟨6197760, by rfl⟩ : syracuseStep 16527361 = 12395521) B12395521
theorem B32592131 : Blo 1695548 32592131 := bstep (se 1 (by rfl) ⟨24444098, by rfl⟩ : syracuseStep 32592131 = 48888197) B48888197
theorem B13062473 : Blo 1695548 13062473 := bstep (se 2 (by rfl) ⟨4898427, by rfl⟩ : syracuseStep 13062473 = 9796855) B9796855
theorem B2543963 : Blo 1695548 2543963 := bstep (se 1 (by rfl) ⟨1907972, by rfl⟩ : syracuseStep 2543963 = 3815945) B3815945
theorem B2863451 : Blo 1695548 2863451 := bstep (se 1 (by rfl) ⟨2147588, by rfl⟩ : syracuseStep 2863451 = 4295177) B4295177
theorem B2863471 : Blo 1695548 2863471 := bstep (se 1 (by rfl) ⟨2147603, by rfl⟩ : syracuseStep 2863471 = 4295207) B4295207
theorem B4829615 : Blo 1695548 4829615 := bstep (se 1 (by rfl) ⟨3622211, by rfl⟩ : syracuseStep 4829615 = 7244423) B7244423
theorem B2544191 : Blo 1695548 2544191 := bstep (se 1 (by rfl) ⟨1908143, by rfl⟩ : syracuseStep 2544191 = 3816287) B3816287
theorem B5804615 : Blo 1695548 5804615 := bstep (se 1 (by rfl) ⟨4353461, by rfl⟩ : syracuseStep 5804615 = 8706923) B8706923
theorem B2863687 : Blo 1695548 2863687 := bstep (se 1 (by rfl) ⟨2147765, by rfl⟩ : syracuseStep 2863687 = 4295531) B4295531
theorem B2544311 : Blo 1695548 2544311 := bstep (se 1 (by rfl) ⟨1908233, by rfl⟩ : syracuseStep 2544311 = 3816467) B3816467
theorem B4133711 : Blo 1695548 4133711 := bstep (se 1 (by rfl) ⟨3100283, by rfl⟩ : syracuseStep 4133711 = 6200567) B6200567
theorem B3871567 : Blo 1695548 3871567 := bstep (se 1 (by rfl) ⟨2903675, by rfl⟩ : syracuseStep 3871567 = 5807351) B5807351
theorem B2544539 : Blo 1695548 2544539 := bstep (se 1 (by rfl) ⟨1908404, by rfl⟩ : syracuseStep 2544539 = 3816809) B3816809
theorem B5723081 : Blo 1695548 5723081 := bstep (se 2 (by rfl) ⟨2146155, by rfl⟩ : syracuseStep 5723081 = 4292311) B4292311
theorem B6443995 : Blo 1695548 6443995 := bstep (se 1 (by rfl) ⟨4832996, by rfl⟩ : syracuseStep 6443995 = 9665993) B9665993
theorem B2864119 : Blo 1695548 2864119 := bstep (se 1 (by rfl) ⟨2148089, by rfl⟩ : syracuseStep 2864119 = 4296179) B4296179
theorem B8590535 : Blo 1695548 8590535 := bstep (se 1 (by rfl) ⟨6442901, by rfl⟩ : syracuseStep 8590535 = 12885803) B12885803
theorem B5723351 : Blo 1695548 5723351 := bstep (se 1 (by rfl) ⟨4292513, by rfl⟩ : syracuseStep 5723351 = 8585027) B8585027
theorem B2544935 : Blo 1695548 2544935 := bstep (se 1 (by rfl) ⟨1908701, by rfl⟩ : syracuseStep 2544935 = 3817403) B3817403
theorem B6116647 : Blo 1695548 6116647 := bstep (se 1 (by rfl) ⟨4587485, by rfl⟩ : syracuseStep 6116647 = 9174971) B9174971
theorem B2864423 : Blo 1695548 2864423 := bstep (se 1 (by rfl) ⟨2148317, by rfl⟩ : syracuseStep 2864423 = 4296635) B4296635
theorem B8590697 : Blo 1695548 8590697 := bstep (se 2 (by rfl) ⟨3221511, by rfl⟩ : syracuseStep 8590697 = 6443023) B6443023
theorem B3437947 : Blo 1695548 3437947 := bstep (se 1 (by rfl) ⟨2578460, by rfl⟩ : syracuseStep 3437947 = 5156921) B5156921
theorem B2545019 : Blo 1695548 2545019 := bstep (se 1 (by rfl) ⟨1908764, by rfl⟩ : syracuseStep 2545019 = 3817529) B3817529
theorem B17405387 : Blo 1695548 17405387 := bstep (se 1 (by rfl) ⟨13054040, by rfl⟩ : syracuseStep 17405387 = 26108081) B26108081
theorem B23524829 : Blo 1695548 23524829 := bstep (se 3 (by rfl) ⟨4410905, by rfl⟩ : syracuseStep 23524829 = 8821811) B8821811
theorem B2545145 : Blo 1695548 2545145 := bstep (se 2 (by rfl) ⟨954429, by rfl⟩ : syracuseStep 2545145 = 1908859) B1908859
theorem B30938669 : Blo 1695548 30938669 := bstep (se 3 (by rfl) ⟨5801000, by rfl⟩ : syracuseStep 30938669 = 11602001) B11602001
theorem B2545247 : Blo 1695548 2545247 := bstep (se 1 (by rfl) ⟨1908935, by rfl⟩ : syracuseStep 2545247 = 3817871) B3817871
theorem B3815099 : Blo 1695548 3815099 := bstep (se 1 (by rfl) ⟨2861324, by rfl⟩ : syracuseStep 3815099 = 5722649) B5722649
theorem B2545463 : Blo 1695548 2545463 := bstep (se 1 (by rfl) ⟨1909097, by rfl⟩ : syracuseStep 2545463 = 3818195) B3818195
theorem B3815225 : Blo 1695548 3815225 := bstep (se 2 (by rfl) ⟨1430709, by rfl⟩ : syracuseStep 3815225 = 2861419) B2861419
theorem B2545769 : Blo 1695548 2545769 := bstep (se 2 (by rfl) ⟨954663, by rfl⟩ : syracuseStep 2545769 = 1909327) B1909327
theorem B13064327 : Blo 1695548 13064327 := bstep (se 1 (by rfl) ⟨9798245, by rfl⟩ : syracuseStep 13064327 = 19596491) B19596491
theorem B6445241 : Blo 1695548 6445241 := bstep (se 2 (by rfl) ⟨2416965, by rfl⟩ : syracuseStep 6445241 = 4833931) B4833931
theorem B32627033 : Blo 1695548 32627033 := bstep (se 2 (by rfl) ⟨12235137, by rfl⟩ : syracuseStep 32627033 = 24470275) B24470275
theorem B7739759 : Blo 1695548 7739759 := bstep (se 1 (by rfl) ⟨5804819, by rfl⟩ : syracuseStep 7739759 = 11609639) B11609639
theorem B2546087 : Blo 1695548 2546087 := bstep (se 1 (by rfl) ⟨1909565, by rfl⟩ : syracuseStep 2546087 = 3819131) B3819131
theorem B3815855 : Blo 1695548 3815855 := bstep (se 1 (by rfl) ⟨2861891, by rfl⟩ : syracuseStep 3815855 = 5723783) B5723783
theorem B6879671 : Blo 1695548 6879671 := bstep (se 1 (by rfl) ⟨5159753, by rfl⟩ : syracuseStep 6879671 = 10319507) B10319507
theorem B3815891 : Blo 1695548 3815891 := bstep (se 1 (by rfl) ⟨2861918, by rfl⟩ : syracuseStep 3815891 = 5723837) B5723837
theorem B2038267 : Blo 1695548 2038267 := bstep (se 1 (by rfl) ⟨1528700, by rfl⟩ : syracuseStep 2038267 = 3057401) B3057401
theorem B2546171 : Blo 1695548 2546171 := bstep (se 1 (by rfl) ⟨1909628, by rfl⟩ : syracuseStep 2546171 = 3819257) B3819257
theorem B3815999 : Blo 1695548 3815999 := bstep (se 1 (by rfl) ⟨2861999, by rfl⟩ : syracuseStep 3815999 = 5723999) B5723999
theorem B2546297 : Blo 1695548 2546297 := bstep (se 2 (by rfl) ⟨954861, by rfl⟩ : syracuseStep 2546297 = 1909723) B1909723
theorem B3816107 : Blo 1695548 3816107 := bstep (se 1 (by rfl) ⟨2862080, by rfl⟩ : syracuseStep 3816107 = 5724161) B5724161
theorem B8706755 : Blo 1695548 8706755 := bstep (se 1 (by rfl) ⟨6530066, by rfl⟩ : syracuseStep 8706755 = 13060133) B13060133
theorem B99195749 : Blo 1695548 99195749 := bstep (se 4 (by rfl) ⟨9299601, by rfl⟩ : syracuseStep 99195749 = 18599203) B18599203
theorem B28982123 : Blo 1695548 28982123 := bstep (se 1 (by rfl) ⟨21736592, by rfl⟩ : syracuseStep 28982123 = 43473185) B43473185
theorem B8584055 : Blo 1695548 8584055 := bstep (se 1 (by rfl) ⟨6438041, by rfl⟩ : syracuseStep 8584055 = 12876083) B12876083
theorem B2718863 : Blo 1695548 2718863 := bstep (se 1 (by rfl) ⟨2039147, by rfl⟩ : syracuseStep 2718863 = 4078295) B4078295
theorem B7249085 : Blo 1695548 7249085 := bstep (se 3 (by rfl) ⟨1359203, by rfl⟩ : syracuseStep 7249085 = 2718407) B2718407
theorem B3816647 : Blo 1695548 3816647 := bstep (se 1 (by rfl) ⟨2862485, by rfl⟩ : syracuseStep 3816647 = 5724971) B5724971
theorem B5725403 : Blo 1695548 5725403 := bstep (se 1 (by rfl) ⟨4294052, by rfl⟩ : syracuseStep 5725403 = 8588105) B8588105
theorem B4291937 : Blo 1695548 4291937 := bstep (se 2 (by rfl) ⟨1609476, by rfl⟩ : syracuseStep 4291937 = 3218953) B3218953
theorem B3816827 : Blo 1695548 3816827 := bstep (se 1 (by rfl) ⟨2862620, by rfl⟩ : syracuseStep 3816827 = 5725241) B5725241
theorem B2719099 : Blo 1695548 2719099 := bstep (se 1 (by rfl) ⟨2039324, by rfl⟩ : syracuseStep 2719099 = 4078649) B4078649
theorem B2416009 : Blo 1695548 2416009 := bstep (se 2 (by rfl) ⟨906003, by rfl⟩ : syracuseStep 2416009 = 1812007) B1812007
theorem B13762007 : Blo 1695548 13762007 := bstep (se 1 (by rfl) ⟨10321505, by rfl⟩ : syracuseStep 13762007 = 20643011) B20643011
theorem B3816953 : Blo 1695548 3816953 := bstep (se 2 (by rfl) ⟨1431357, by rfl⟩ : syracuseStep 3816953 = 2862715) B2862715
theorem B3817043 : Blo 1695548 3817043 := bstep (se 1 (by rfl) ⟨2862782, by rfl⟩ : syracuseStep 3817043 = 5725565) B5725565
theorem B1908319 : Blo 1695548 1908319 := bstep (se 1 (by rfl) ⟨1431239, by rfl⟩ : syracuseStep 1908319 = 2862479) B2862479
theorem B8584865 : Blo 1695548 8584865 := bstep (se 2 (by rfl) ⟨3219324, by rfl⟩ : syracuseStep 8584865 = 6438649) B6438649
theorem B6438635 : Blo 1695548 6438635 := bstep (se 1 (by rfl) ⟨4828976, by rfl⟩ : syracuseStep 6438635 = 9657953) B9657953
theorem B18341635 : Blo 1695548 18341635 := bstep (se 1 (by rfl) ⟨13756226, by rfl⟩ : syracuseStep 18341635 = 27512453) B27512453
theorem B3817223 : Blo 1695548 3817223 := bstep (se 1 (by rfl) ⟨2862917, by rfl⟩ : syracuseStep 3817223 = 5725835) B5725835
theorem B3219257 : Blo 1695548 3219257 := bstep (se 2 (by rfl) ⟨1207221, by rfl⟩ : syracuseStep 3219257 = 2414443) B2414443
theorem B1695643 : Blo 1695548 1695643 := bstep (se 1 (by rfl) ⟨1271732, by rfl⟩ : syracuseStep 1695643 = 2543465) B2543465
theorem B4587421 : Blo 1695548 4587421 := bstep (se 3 (by rfl) ⟨860141, by rfl⟩ : syracuseStep 4587421 = 1720283) B1720283
theorem B1695695 : Blo 1695548 1695695 := bstep (se 1 (by rfl) ⟨1271771, by rfl⟩ : syracuseStep 1695695 = 2543543) B2543543
theorem B1695719 : Blo 1695548 1695719 := bstep (se 1 (by rfl) ⟨1271789, by rfl⟩ : syracuseStep 1695719 = 2543579) B2543579
theorem B22036481 : Blo 1695548 22036481 := bstep (se 2 (by rfl) ⟨8263680, by rfl⟩ : syracuseStep 22036481 = 16527361) B16527361
theorem B3817511 : Blo 1695548 3817511 := bstep (se 1 (by rfl) ⟨2863133, by rfl⟩ : syracuseStep 3817511 = 5726267) B5726267
theorem B4292747 : Blo 1695548 4292747 := bstep (se 1 (by rfl) ⟨3219560, by rfl⟩ : syracuseStep 4292747 = 6439121) B6439121
theorem B12878027 : Blo 1695548 12878027 := bstep (se 1 (by rfl) ⟨9658520, by rfl⟩ : syracuseStep 12878027 = 19317041) B19317041
theorem B3817691 : Blo 1695548 3817691 := bstep (se 1 (by rfl) ⟨2863268, by rfl⟩ : syracuseStep 3817691 = 5726537) B5726537
theorem B8708315 : Blo 1695548 8708315 := bstep (se 1 (by rfl) ⟨6531236, by rfl⟩ : syracuseStep 8708315 = 13062473) B13062473
theorem B1695975 : Blo 1695548 1695975 := bstep (se 1 (by rfl) ⟨1271981, by rfl⟩ : syracuseStep 1695975 = 2543963) B2543963
theorem B1908967 : Blo 1695548 1908967 := bstep (se 1 (by rfl) ⟨1431725, by rfl⟩ : syracuseStep 1908967 = 2863451) B2863451
theorem B3219743 : Blo 1695548 3219743 := bstep (se 1 (by rfl) ⟨2414807, by rfl⟩ : syracuseStep 3219743 = 4829615) B4829615
theorem B1696127 : Blo 1695548 1696127 := bstep (se 1 (by rfl) ⟨1272095, by rfl⟩ : syracuseStep 1696127 = 2544191) B2544191
theorem B4293071 : Blo 1695548 4293071 := bstep (se 1 (by rfl) ⟨3219803, by rfl⟩ : syracuseStep 4293071 = 6439607) B6439607
theorem B1696207 : Blo 1695548 1696207 := bstep (se 1 (by rfl) ⟨1272155, by rfl⟩ : syracuseStep 1696207 = 2544311) B2544311
theorem B3817961 : Blo 1695548 3817961 := bstep (se 2 (by rfl) ⟨1431735, by rfl⟩ : syracuseStep 3817961 = 2863471) B2863471
theorem B1696359 : Blo 1695548 1696359 := bstep (se 1 (by rfl) ⟨1272269, by rfl⟩ : syracuseStep 1696359 = 2544539) B2544539
theorem B3818249 : Blo 1695548 3818249 := bstep (se 2 (by rfl) ⟨1431843, by rfl⟩ : syracuseStep 3818249 = 2863687) B2863687
theorem B5727023 : Blo 1695548 5727023 := bstep (se 1 (by rfl) ⟨4295267, by rfl⟩ : syracuseStep 5727023 = 8590535) B8590535
theorem B1696623 : Blo 1695548 1696623 := bstep (se 1 (by rfl) ⟨1272467, by rfl⟩ : syracuseStep 1696623 = 2544935) B2544935
theorem B1909615 : Blo 1695548 1909615 := bstep (se 1 (by rfl) ⟨1432211, by rfl⟩ : syracuseStep 1909615 = 2864423) B2864423
theorem B5727131 : Blo 1695548 5727131 := bstep (se 1 (by rfl) ⟨4295348, by rfl⟩ : syracuseStep 5727131 = 8590697) B8590697
theorem B2147239 : Blo 1695548 2147239 := bstep (se 1 (by rfl) ⟨1610429, by rfl⟩ : syracuseStep 2147239 = 3220859) B3220859
theorem B1696679 : Blo 1695548 1696679 := bstep (se 1 (by rfl) ⟨1272509, by rfl⟩ : syracuseStep 1696679 = 2545019) B2545019
theorem B4293587 : Blo 1695548 4293587 := bstep (se 1 (by rfl) ⟨3220190, by rfl⟩ : syracuseStep 4293587 = 6440381) B6440381
theorem B1696763 : Blo 1695548 1696763 := bstep (se 1 (by rfl) ⟨1272572, by rfl⟩ : syracuseStep 1696763 = 2545145) B2545145
theorem B1696831 : Blo 1695548 1696831 := bstep (se 1 (by rfl) ⟨1272623, by rfl⟩ : syracuseStep 1696831 = 2545247) B2545247
theorem B5162089 : Blo 1695548 5162089 := bstep (se 2 (by rfl) ⟨1935783, by rfl⟩ : syracuseStep 5162089 = 3871567) B3871567
theorem B1934543 : Blo 1695548 1934543 := bstep (se 1 (by rfl) ⟨1450907, by rfl⟩ : syracuseStep 1934543 = 2901815) B2901815
theorem B1696975 : Blo 1695548 1696975 := bstep (se 1 (by rfl) ⟨1272731, by rfl⟩ : syracuseStep 1696975 = 2545463) B2545463
theorem B29394163 : Blo 1695548 29394163 := bstep (se 1 (by rfl) ⟨22045622, by rfl⟩ : syracuseStep 29394163 = 44091245) B44091245
theorem B3818825 : Blo 1695548 3818825 := bstep (se 2 (by rfl) ⟨1432059, by rfl⟩ : syracuseStep 3818825 = 2864119) B2864119
theorem B1697179 : Blo 1695548 1697179 := bstep (se 1 (by rfl) ⟨1272884, by rfl⟩ : syracuseStep 1697179 = 2545769) B2545769
theorem B8709551 : Blo 1695548 8709551 := bstep (se 1 (by rfl) ⟨6532163, by rfl⟩ : syracuseStep 8709551 = 13064327) B13064327
theorem B21751355 : Blo 1695548 21751355 := bstep (se 1 (by rfl) ⟨16313516, by rfl⟩ : syracuseStep 21751355 = 32627033) B32627033
theorem B4294255 : Blo 1695548 4294255 := bstep (se 1 (by rfl) ⟨3220691, by rfl⟩ : syracuseStep 4294255 = 6441383) B6441383
theorem B1697391 : Blo 1695548 1697391 := bstep (se 1 (by rfl) ⟨1273043, by rfl⟩ : syracuseStep 1697391 = 2546087) B2546087
theorem B1697447 : Blo 1695548 1697447 := bstep (se 1 (by rfl) ⟨1273085, by rfl⟩ : syracuseStep 1697447 = 2546171) B2546171
theorem B2148059 : Blo 1695548 2148059 := bstep (se 1 (by rfl) ⟨1611044, by rfl⟩ : syracuseStep 2148059 = 3222089) B3222089
theorem B4294367 : Blo 1695548 4294367 := bstep (se 1 (by rfl) ⟨3220775, by rfl⟩ : syracuseStep 4294367 = 6441551) B6441551
theorem B148989689 : Blo 1695548 148989689 := bstep (se 2 (by rfl) ⟨55871133, by rfl⟩ : syracuseStep 148989689 = 111742267) B111742267
theorem B1697531 : Blo 1695548 1697531 := bstep (se 1 (by rfl) ⟨1273148, by rfl⟩ : syracuseStep 1697531 = 2546297) B2546297
theorem B12224297 : Blo 1695548 12224297 := bstep (se 2 (by rfl) ⟨4584111, by rfl⟩ : syracuseStep 12224297 = 9168223) B9168223
theorem B3221345 : Blo 1695548 3221345 := bstep (se 2 (by rfl) ⟨1208004, by rfl⟩ : syracuseStep 3221345 = 2416009) B2416009
theorem B18335717 : Blo 1695548 18335717 := bstep (se 4 (by rfl) ⟨1718973, by rfl⟩ : syracuseStep 18335717 = 3437947) B3437947
theorem B14501861 : Blo 1695548 14501861 := bstep (se 4 (by rfl) ⟨1359549, by rfl⟩ : syracuseStep 14501861 = 2719099) B2719099
theorem B5728265 : Blo 1695548 5728265 := bstep (se 2 (by rfl) ⟨2148099, by rfl⟩ : syracuseStep 5728265 = 4296199) B4296199
theorem B1812575 : Blo 1695548 1812575 := bstep (se 1 (by rfl) ⟨1359431, by rfl⟩ : syracuseStep 1812575 = 2718863) B2718863
theorem B2861291 : Blo 1695548 2861291 := bstep (se 1 (by rfl) ⟨2145968, by rfl⟩ : syracuseStep 2861291 = 4291937) B4291937
theorem B24455513 : Blo 1695548 24455513 := bstep (se 2 (by rfl) ⟨9170817, by rfl⟩ : syracuseStep 24455513 = 18341635) B18341635
theorem B4131335 : Blo 1695548 4131335 := bstep (se 1 (by rfl) ⟨3098501, by rfl⟩ : syracuseStep 4131335 = 6197003) B6197003
theorem B12880457 : Blo 1695548 12880457 := bstep (se 2 (by rfl) ⟨4830171, by rfl⟩ : syracuseStep 12880457 = 9660343) B9660343
theorem B3140407 : Blo 1695548 3140407 := bstep (se 1 (by rfl) ⟨2355305, by rfl⟩ : syracuseStep 3140407 = 4710611) B4710611
theorem B21728087 : Blo 1695548 21728087 := bstep (se 1 (by rfl) ⟨16296065, by rfl⟩ : syracuseStep 21728087 = 32592131) B32592131
theorem B24447905 : Blo 1695548 24447905 := bstep (se 2 (by rfl) ⟨9167964, by rfl⟩ : syracuseStep 24447905 = 18335929) B18335929
theorem B2862121 : Blo 1695548 2862121 := bstep (se 2 (by rfl) ⟨1073295, by rfl⟩ : syracuseStep 2862121 = 2146591) B2146591
theorem B3869743 : Blo 1695548 3869743 := bstep (se 1 (by rfl) ⟨2902307, by rfl⟩ : syracuseStep 3869743 = 5804615) B5804615
theorem B3222575 : Blo 1695548 3222575 := bstep (se 1 (by rfl) ⟨2416931, by rfl⟩ : syracuseStep 3222575 = 4833863) B4833863
theorem B2862263 : Blo 1695548 2862263 := bstep (se 1 (by rfl) ⟨2146697, by rfl⟩ : syracuseStep 2862263 = 4293395) B4293395
theorem B2862587 : Blo 1695548 2862587 := bstep (se 1 (by rfl) ⟨2146940, by rfl⟩ : syracuseStep 2862587 = 4293881) B4293881
theorem B20639357 : Blo 1695548 20639357 := bstep (se 3 (by rfl) ⟨3869879, by rfl⟩ : syracuseStep 20639357 = 7739759) B7739759
theorem B11603591 : Blo 1695548 11603591 := bstep (se 1 (by rfl) ⟨8702693, by rfl⟩ : syracuseStep 11603591 = 17405387) B17405387
theorem B15683219 : Blo 1695548 15683219 := bstep (se 1 (by rfl) ⟨11762414, by rfl⟩ : syracuseStep 15683219 = 23524829) B23524829
theorem B2543399 : Blo 1695548 2543399 := bstep (se 1 (by rfl) ⟨1907549, by rfl⟩ : syracuseStep 2543399 = 3815099) B3815099
theorem B4829033 : Blo 1695548 4829033 := bstep (se 2 (by rfl) ⟨1810887, by rfl⟩ : syracuseStep 4829033 = 3621775) B3621775
theorem B2543483 : Blo 1695548 2543483 := bstep (se 1 (by rfl) ⟨1907612, by rfl⟩ : syracuseStep 2543483 = 3815225) B3815225
theorem B2863019 : Blo 1695548 2863019 := bstep (se 1 (by rfl) ⟨2147264, by rfl⟩ : syracuseStep 2863019 = 4294529) B4294529
theorem B4296827 : Blo 1695548 4296827 := bstep (se 1 (by rfl) ⟨3222620, by rfl⟩ : syracuseStep 4296827 = 6445241) B6445241
theorem B2543903 : Blo 1695548 2543903 := bstep (se 1 (by rfl) ⟨1907927, by rfl⟩ : syracuseStep 2543903 = 3815855) B3815855
theorem B2543927 : Blo 1695548 2543927 := bstep (se 1 (by rfl) ⟨1907945, by rfl⟩ : syracuseStep 2543927 = 3815891) B3815891
theorem B2543999 : Blo 1695548 2543999 := bstep (se 1 (by rfl) ⟨1907999, by rfl⟩ : syracuseStep 2543999 = 3815999) B3815999
theorem B8155529 : Blo 1695548 8155529 := bstep (se 2 (by rfl) ⟨3058323, by rfl⟩ : syracuseStep 8155529 = 6116647) B6116647
theorem B2544071 : Blo 1695548 2544071 := bstep (se 1 (by rfl) ⟨1908053, by rfl⟩ : syracuseStep 2544071 = 3816107) B3816107
theorem B2863559 : Blo 1695548 2863559 := bstep (se 1 (by rfl) ⟨2147669, by rfl⟩ : syracuseStep 2863559 = 4295339) B4295339
theorem B5804503 : Blo 1695548 5804503 := bstep (se 1 (by rfl) ⟨4353377, by rfl⟩ : syracuseStep 5804503 = 8706755) B8706755
theorem B6197753 : Blo 1695548 6197753 := bstep (se 2 (by rfl) ⟨2324157, by rfl⟩ : syracuseStep 6197753 = 4648315) B4648315
theorem B66130499 : Blo 1695548 66130499 := bstep (se 1 (by rfl) ⟨49597874, by rfl⟩ : syracuseStep 66130499 = 99195749) B99195749
theorem B19321415 : Blo 1695548 19321415 := bstep (se 1 (by rfl) ⟨14491061, by rfl⟩ : syracuseStep 19321415 = 28982123) B28982123
theorem B5722703 : Blo 1695548 5722703 := bstep (se 1 (by rfl) ⟨4292027, by rfl⟩ : syracuseStep 5722703 = 8584055) B8584055
theorem B10318583 : Blo 1695548 10318583 := bstep (se 1 (by rfl) ⟨7738937, by rfl⟩ : syracuseStep 10318583 = 15477875) B15477875
theorem B2544425 : Blo 1695548 2544425 := bstep (se 2 (by rfl) ⟨954159, by rfl⟩ : syracuseStep 2544425 = 1908319) B1908319
theorem B2544431 : Blo 1695548 2544431 := bstep (se 1 (by rfl) ⟨1908323, by rfl⟩ : syracuseStep 2544431 = 3816647) B3816647
theorem B11023229 : Blo 1695548 11023229 := bstep (se 3 (by rfl) ⟨2066855, by rfl⟩ : syracuseStep 11023229 = 4133711) B4133711
theorem B2544551 : Blo 1695548 2544551 := bstep (se 1 (by rfl) ⟨1908413, by rfl⟩ : syracuseStep 2544551 = 3816827) B3816827
theorem B2544635 : Blo 1695548 2544635 := bstep (se 1 (by rfl) ⟨1908476, by rfl⟩ : syracuseStep 2544635 = 3816953) B3816953
theorem B4830263 : Blo 1695548 4830263 := bstep (se 1 (by rfl) ⟨3622697, by rfl⟩ : syracuseStep 4830263 = 7245395) B7245395
theorem B2544695 : Blo 1695548 2544695 := bstep (se 1 (by rfl) ⟨1908521, by rfl⟩ : syracuseStep 2544695 = 3817043) B3817043
theorem B5723243 : Blo 1695548 5723243 := bstep (se 1 (by rfl) ⟨4292432, by rfl⟩ : syracuseStep 5723243 = 8584865) B8584865
theorem B19330163 : Blo 1695548 19330163 := bstep (se 1 (by rfl) ⟨14497622, by rfl⟩ : syracuseStep 19330163 = 28995245) B28995245
theorem B2544815 : Blo 1695548 2544815 := bstep (se 1 (by rfl) ⟨1908611, by rfl⟩ : syracuseStep 2544815 = 3817223) B3817223
theorem B2864335 : Blo 1695548 2864335 := bstep (se 1 (by rfl) ⟨2148251, by rfl⟩ : syracuseStep 2864335 = 4296503) B4296503
theorem B6116561 : Blo 1695548 6116561 := bstep (se 2 (by rfl) ⟨2293710, by rfl⟩ : syracuseStep 6116561 = 4587421) B4587421
theorem B2545223 : Blo 1695548 2545223 := bstep (se 1 (by rfl) ⟨1908917, by rfl⟩ : syracuseStep 2545223 = 3817835) B3817835
theorem B24802973 : Blo 1695548 24802973 := bstep (se 3 (by rfl) ⟨4650557, by rfl⟩ : syracuseStep 24802973 = 9301115) B9301115
theorem B2545319 : Blo 1695548 2545319 := bstep (se 1 (by rfl) ⟨1908989, by rfl⟩ : syracuseStep 2545319 = 3817979) B3817979
theorem B11327147 : Blo 1695548 11327147 := bstep (se 1 (by rfl) ⟨8495360, by rfl⟩ : syracuseStep 11327147 = 16990721) B16990721
theorem B2545403 : Blo 1695548 2545403 := bstep (se 1 (by rfl) ⟨1909052, by rfl⟩ : syracuseStep 2545403 = 3818105) B3818105
theorem B2545439 : Blo 1695548 2545439 := bstep (se 1 (by rfl) ⟨1909079, by rfl⟩ : syracuseStep 2545439 = 3818159) B3818159
theorem B12875597 : Blo 1695548 12875597 := bstep (se 3 (by rfl) ⟨2414174, by rfl⟩ : syracuseStep 12875597 = 4828349) B4828349
theorem B2545487 : Blo 1695548 2545487 := bstep (se 1 (by rfl) ⟨1909115, by rfl⟩ : syracuseStep 2545487 = 3818231) B3818231
theorem B4077449 : Blo 1695548 4077449 := bstep (se 2 (by rfl) ⟨1529043, by rfl⟩ : syracuseStep 4077449 = 3058087) B3058087
theorem B2545607 : Blo 1695548 2545607 := bstep (se 1 (by rfl) ⟨1909205, by rfl⟩ : syracuseStep 2545607 = 3818411) B3818411
theorem B3815387 : Blo 1695548 3815387 := bstep (se 1 (by rfl) ⟨2861540, by rfl⟩ : syracuseStep 3815387 = 5723081) B5723081
theorem B7247855 : Blo 1695548 7247855 := bstep (se 1 (by rfl) ⟨5435891, by rfl⟩ : syracuseStep 7247855 = 10871783) B10871783
theorem B3815567 : Blo 1695548 3815567 := bstep (se 1 (by rfl) ⟨2861675, by rfl⟩ : syracuseStep 3815567 = 5723351) B5723351
theorem B3815585 : Blo 1695548 3815585 := bstep (se 2 (by rfl) ⟨1430844, by rfl⟩ : syracuseStep 3815585 = 2861689) B2861689
theorem B4896929 : Blo 1695548 4896929 := bstep (se 2 (by rfl) ⟨1836348, by rfl⟩ : syracuseStep 4896929 = 3672697) B3672697
theorem B3815657 : Blo 1695548 3815657 := bstep (se 2 (by rfl) ⟨1430871, by rfl⟩ : syracuseStep 3815657 = 2861743) B2861743
theorem B2545961 : Blo 1695548 2545961 := bstep (se 2 (by rfl) ⟨954735, by rfl⟩ : syracuseStep 2545961 = 1909471) B1909471
theorem B2545967 : Blo 1695548 2545967 := bstep (se 1 (by rfl) ⟨1909475, by rfl⟩ : syracuseStep 2545967 = 3818951) B3818951
theorem B20625779 : Blo 1695548 20625779 := bstep (se 1 (by rfl) ⟨15469334, by rfl⟩ : syracuseStep 20625779 = 30938669) B30938669
theorem B5724539 : Blo 1695548 5724539 := bstep (se 1 (by rfl) ⟨4293404, by rfl⟩ : syracuseStep 5724539 = 8586809) B8586809
theorem B2546207 : Blo 1695548 2546207 := bstep (se 1 (by rfl) ⟨1909655, by rfl⟩ : syracuseStep 2546207 = 3819311) B3819311
theorem B10869299 : Blo 1695548 10869299 := bstep (se 1 (by rfl) ⟨8151974, by rfl⟩ : syracuseStep 10869299 = 16303949) B16303949
theorem B16300601 : Blo 1695548 16300601 := bstep (se 2 (by rfl) ⟨6112725, by rfl⟩ : syracuseStep 16300601 = 12225451) B12225451
theorem B8591993 : Blo 1695548 8591993 := bstep (se 2 (by rfl) ⟨3221997, by rfl⟩ : syracuseStep 8591993 = 6443995) B6443995
theorem B5724809 : Blo 1695548 5724809 := bstep (se 2 (by rfl) ⟨2146803, by rfl⟩ : syracuseStep 5724809 = 4293607) B4293607
theorem B8149841 : Blo 1695548 8149841 := bstep (se 2 (by rfl) ⟨3056190, by rfl⟩ : syracuseStep 8149841 = 6112381) B6112381
theorem B4586447 : Blo 1695548 4586447 := bstep (se 1 (by rfl) ⟨3439835, by rfl⟩ : syracuseStep 4586447 = 6879671) B6879671
theorem B4832723 : Blo 1695548 4832723 := bstep (se 1 (by rfl) ⟨3624542, by rfl⟩ : syracuseStep 4832723 = 7249085) B7249085
theorem B3816935 : Blo 1695548 3816935 := bstep (se 1 (by rfl) ⟨2862701, by rfl⟩ : syracuseStep 3816935 = 5725403) B5725403
theorem B9789007 : Blo 1695548 9789007 := bstep (se 1 (by rfl) ⟨7341755, by rfl⟩ : syracuseStep 9789007 = 14683511) B14683511
theorem B9174671 : Blo 1695548 9174671 := bstep (se 1 (by rfl) ⟨6881003, by rfl⟩ : syracuseStep 9174671 = 13762007) B13762007
theorem B5725943 : Blo 1695548 5725943 := bstep (se 1 (by rfl) ⟨4294457, by rfl⟩ : syracuseStep 5725943 = 8588915) B8588915
theorem B1695559 : Blo 1695548 1695559 := bstep (se 1 (by rfl) ⟨1271669, by rfl⟩ : syracuseStep 1695559 = 2543339) B2543339
theorem B4292423 : Blo 1695548 4292423 := bstep (se 1 (by rfl) ⟨3219317, by rfl⟩ : syracuseStep 4292423 = 6438635) B6438635
theorem B2146171 : Blo 1695548 2146171 := bstep (se 1 (by rfl) ⟨1609628, by rfl⟩ : syracuseStep 2146171 = 3219257) B3219257
theorem B1695711 : Blo 1695548 1695711 := bstep (se 1 (by rfl) ⟨1271783, by rfl⟩ : syracuseStep 1695711 = 2543567) B2543567
theorem B10870757 : Blo 1695548 10870757 := bstep (se 4 (by rfl) ⟨1019133, by rfl⟩ : syracuseStep 10870757 = 2038267) B2038267
theorem B8585351 : Blo 1695548 8585351 := bstep (se 1 (by rfl) ⟨6439013, by rfl⟩ : syracuseStep 8585351 = 12878027) B12878027
theorem B1695935 : Blo 1695548 1695935 := bstep (se 1 (by rfl) ⟨1271951, by rfl⟩ : syracuseStep 1695935 = 2543903) B2543903
theorem B2146495 : Blo 1695548 2146495 := bstep (se 1 (by rfl) ⟨1609871, by rfl⟩ : syracuseStep 2146495 = 3219743) B3219743
theorem B1695951 : Blo 1695548 1695951 := bstep (se 1 (by rfl) ⟨1271963, by rfl⟩ : syracuseStep 1695951 = 2543927) B2543927
theorem B4833533 : Blo 1695548 4833533 := bstep (se 3 (by rfl) ⟨906287, by rfl⟩ : syracuseStep 4833533 = 1812575) B1812575
theorem B1695999 : Blo 1695548 1695999 := bstep (se 1 (by rfl) ⟨1271999, by rfl⟩ : syracuseStep 1695999 = 2543999) B2543999
theorem B1696047 : Blo 1695548 1696047 := bstep (se 1 (by rfl) ⟨1272035, by rfl⟩ : syracuseStep 1696047 = 2544071) B2544071
theorem B1909039 : Blo 1695548 1909039 := bstep (se 1 (by rfl) ⟨1431779, by rfl⟩ : syracuseStep 1909039 = 2863559) B2863559
theorem B1696283 : Blo 1695548 1696283 := bstep (se 1 (by rfl) ⟨1272212, by rfl⟩ : syracuseStep 1696283 = 2544425) B2544425
theorem B1696287 : Blo 1695548 1696287 := bstep (se 1 (by rfl) ⟨1272215, by rfl⟩ : syracuseStep 1696287 = 2544431) B2544431
theorem B3818015 : Blo 1695548 3818015 := bstep (se 1 (by rfl) ⟨2863511, by rfl⟩ : syracuseStep 3818015 = 5727023) B5727023
theorem B7348819 : Blo 1695548 7348819 := bstep (se 1 (by rfl) ⟨5511614, by rfl⟩ : syracuseStep 7348819 = 11023229) B11023229
theorem B3818087 : Blo 1695548 3818087 := bstep (se 1 (by rfl) ⟨2863565, by rfl⟩ : syracuseStep 3818087 = 5727131) B5727131
theorem B1696367 : Blo 1695548 1696367 := bstep (se 1 (by rfl) ⟨1272275, by rfl⟩ : syracuseStep 1696367 = 2544551) B2544551
theorem B1696423 : Blo 1695548 1696423 := bstep (se 1 (by rfl) ⟨1272317, by rfl⟩ : syracuseStep 1696423 = 2544635) B2544635
theorem B3220175 : Blo 1695548 3220175 := bstep (se 1 (by rfl) ⟨2415131, by rfl⟩ : syracuseStep 3220175 = 4830263) B4830263
theorem B1696463 : Blo 1695548 1696463 := bstep (se 1 (by rfl) ⟨1272347, by rfl⟩ : syracuseStep 1696463 = 2544695) B2544695
theorem B12886775 : Blo 1695548 12886775 := bstep (se 1 (by rfl) ⟨9665081, by rfl⟩ : syracuseStep 12886775 = 19330163) B19330163
theorem B1696543 : Blo 1695548 1696543 := bstep (se 1 (by rfl) ⟨1272407, by rfl⟩ : syracuseStep 1696543 = 2544815) B2544815
theorem B14500903 : Blo 1695548 14500903 := bstep (se 1 (by rfl) ⟨10875677, by rfl⟩ : syracuseStep 14500903 = 21751355) B21751355
theorem B1696815 : Blo 1695548 1696815 := bstep (se 1 (by rfl) ⟨1272611, by rfl⟩ : syracuseStep 1696815 = 2545223) B2545223
theorem B4187209 : Blo 1695548 4187209 := bstep (se 2 (by rfl) ⟨1570203, by rfl⟩ : syracuseStep 4187209 = 3140407) B3140407
theorem B1696879 : Blo 1695548 1696879 := bstep (se 1 (by rfl) ⟨1272659, by rfl⟩ : syracuseStep 1696879 = 2545319) B2545319
theorem B1696935 : Blo 1695548 1696935 := bstep (se 1 (by rfl) ⟨1272701, by rfl⟩ : syracuseStep 1696935 = 2545403) B2545403
theorem B1696959 : Blo 1695548 1696959 := bstep (se 1 (by rfl) ⟨1272719, by rfl⟩ : syracuseStep 1696959 = 2545439) B2545439
theorem B12887261 : Blo 1695548 12887261 := bstep (se 3 (by rfl) ⟨2416361, by rfl⟩ : syracuseStep 12887261 = 4832723) B4832723
theorem B1696991 : Blo 1695548 1696991 := bstep (se 1 (by rfl) ⟨1272743, by rfl⟩ : syracuseStep 1696991 = 2545487) B2545487
theorem B2147563 : Blo 1695548 2147563 := bstep (se 1 (by rfl) ⟨1610672, by rfl⟩ : syracuseStep 2147563 = 3221345) B3221345
theorem B1697071 : Blo 1695548 1697071 := bstep (se 1 (by rfl) ⟨1272803, by rfl⟩ : syracuseStep 1697071 = 2545607) B2545607
theorem B12223811 : Blo 1695548 12223811 := bstep (se 1 (by rfl) ⟨9167858, by rfl⟩ : syracuseStep 12223811 = 18335717) B18335717
theorem B9667907 : Blo 1695548 9667907 := bstep (se 1 (by rfl) ⟨7250930, by rfl⟩ : syracuseStep 9667907 = 14501861) B14501861
theorem B3818843 : Blo 1695548 3818843 := bstep (se 1 (by rfl) ⟨2864132, by rfl⟩ : syracuseStep 3818843 = 5728265) B5728265
theorem B6882785 : Blo 1695548 6882785 := bstep (se 2 (by rfl) ⟨2581044, by rfl⟩ : syracuseStep 6882785 = 5162089) B5162089
theorem B1697307 : Blo 1695548 1697307 := bstep (se 1 (by rfl) ⟨1272980, by rfl⟩ : syracuseStep 1697307 = 2545961) B2545961
theorem B1697311 : Blo 1695548 1697311 := bstep (se 1 (by rfl) ⟨1272983, by rfl⟩ : syracuseStep 1697311 = 2545967) B2545967
theorem B16303675 : Blo 1695548 16303675 := bstep (se 1 (by rfl) ⟨12227756, by rfl⟩ : syracuseStep 16303675 = 24455513) B24455513
theorem B3819113 : Blo 1695548 3819113 := bstep (se 2 (by rfl) ⟨1432167, by rfl⟩ : syracuseStep 3819113 = 2864335) B2864335
theorem B39192217 : Blo 1695548 39192217 := bstep (se 2 (by rfl) ⟨14697081, by rfl⟩ : syracuseStep 39192217 = 29394163) B29394163
theorem B2754223 : Blo 1695548 2754223 := bstep (se 1 (by rfl) ⟨2065667, by rfl⟩ : syracuseStep 2754223 = 4131335) B4131335
theorem B1697471 : Blo 1695548 1697471 := bstep (se 1 (by rfl) ⟨1273103, by rfl⟩ : syracuseStep 1697471 = 2546207) B2546207
theorem B8586971 : Blo 1695548 8586971 := bstep (se 1 (by rfl) ⟨6440228, by rfl⟩ : syracuseStep 8586971 = 12880457) B12880457
theorem B5727995 : Blo 1695548 5727995 := bstep (se 1 (by rfl) ⟨4295996, by rfl⟩ : syracuseStep 5727995 = 8591993) B8591993
theorem B5433227 : Blo 1695548 5433227 := bstep (se 1 (by rfl) ⟨4074920, by rfl⟩ : syracuseStep 5433227 = 8149841) B8149841
theorem B14485391 : Blo 1695548 14485391 := bstep (se 1 (by rfl) ⟨10864043, by rfl⟩ : syracuseStep 14485391 = 21728087) B21728087
theorem B5728157 : Blo 1695548 5728157 := bstep (se 3 (by rfl) ⟨1074029, by rfl⟩ : syracuseStep 5728157 = 2148059) B2148059
theorem B3057631 : Blo 1695548 3057631 := bstep (se 1 (by rfl) ⟨2293223, by rfl⟩ : syracuseStep 3057631 = 4586447) B4586447
theorem B2148383 : Blo 1695548 2148383 := bstep (se 1 (by rfl) ⟨1611287, by rfl⟩ : syracuseStep 2148383 = 3222575) B3222575
theorem B13052009 : Blo 1695548 13052009 := bstep (se 2 (by rfl) ⟨4894503, by rfl⟩ : syracuseStep 13052009 = 9789007) B9789007
theorem B32598125 : Blo 1695548 32598125 := bstep (se 3 (by rfl) ⟨6112148, by rfl⟩ : syracuseStep 32598125 = 12224297) B12224297
theorem B7735727 : Blo 1695548 7735727 := bstep (se 1 (by rfl) ⟨5801795, by rfl⟩ : syracuseStep 7735727 = 11603591) B11603591
theorem B10455479 : Blo 1695548 10455479 := bstep (se 1 (by rfl) ⟨7841609, by rfl⟩ : syracuseStep 10455479 = 15683219) B15683219
theorem B2861561 : Blo 1695548 2861561 := bstep (se 2 (by rfl) ⟨1073085, by rfl⟩ : syracuseStep 2861561 = 2146171) B2146171
theorem B2861615 : Blo 1695548 2861615 := bstep (se 1 (by rfl) ⟨2146211, by rfl⟩ : syracuseStep 2861615 = 4292423) B4292423
theorem B14690987 : Blo 1695548 14690987 := bstep (se 1 (by rfl) ⟨11018240, by rfl⟩ : syracuseStep 14690987 = 22036481) B22036481
theorem B2861831 : Blo 1695548 2861831 := bstep (se 1 (by rfl) ⟨2146373, by rfl⟩ : syracuseStep 2861831 = 4292747) B4292747
theorem B2862047 : Blo 1695548 2862047 := bstep (se 1 (by rfl) ⟨2146535, by rfl⟩ : syracuseStep 2862047 = 4293071) B4293071
theorem B12880943 : Blo 1695548 12880943 := bstep (se 1 (by rfl) ⟨9660707, by rfl⟩ : syracuseStep 12880943 = 19321415) B19321415
theorem B2862391 : Blo 1695548 2862391 := bstep (se 1 (by rfl) ⟨2146793, by rfl⟩ : syracuseStep 2862391 = 4293587) B4293587
theorem B16535315 : Blo 1695548 16535315 := bstep (se 1 (by rfl) ⟨12401486, by rfl⟩ : syracuseStep 16535315 = 24802973) B24802973
theorem B2862911 : Blo 1695548 2862911 := bstep (se 1 (by rfl) ⟨2147183, by rfl⟩ : syracuseStep 2862911 = 4294367) B4294367
theorem B2862985 : Blo 1695548 2862985 := bstep (se 2 (by rfl) ⟨1073619, by rfl⟩ : syracuseStep 2862985 = 2147239) B2147239
theorem B2543591 : Blo 1695548 2543591 := bstep (se 1 (by rfl) ⟨1907693, by rfl⟩ : syracuseStep 2543591 = 3815387) B3815387
theorem B16527341 : Blo 1695548 16527341 := bstep (se 3 (by rfl) ⟨3098876, by rfl⟩ : syracuseStep 16527341 = 6197753) B6197753
theorem B2543711 : Blo 1695548 2543711 := bstep (se 1 (by rfl) ⟨1907783, by rfl⟩ : syracuseStep 2543711 = 3815567) B3815567
theorem B2543723 : Blo 1695548 2543723 := bstep (se 1 (by rfl) ⟨1907792, by rfl⟩ : syracuseStep 2543723 = 3815585) B3815585
theorem B3264619 : Blo 1695548 3264619 := bstep (se 1 (by rfl) ⟨2448464, by rfl⟩ : syracuseStep 3264619 = 4896929) B4896929
theorem B2543771 : Blo 1695548 2543771 := bstep (se 1 (by rfl) ⟨1907828, by rfl⟩ : syracuseStep 2543771 = 3815657) B3815657
theorem B13750519 : Blo 1695548 13750519 := bstep (se 1 (by rfl) ⟨10312889, by rfl⟩ : syracuseStep 13750519 = 20625779) B20625779
theorem B7246199 : Blo 1695548 7246199 := bstep (se 1 (by rfl) ⟨5434649, by rfl⟩ : syracuseStep 7246199 = 10869299) B10869299
theorem B10867067 : Blo 1695548 10867067 := bstep (se 1 (by rfl) ⟨8150300, by rfl⟩ : syracuseStep 10867067 = 16300601) B16300601
theorem B16298603 : Blo 1695548 16298603 := bstep (se 1 (by rfl) ⟨12223952, by rfl⟩ : syracuseStep 16298603 = 24447905) B24447905
theorem B2544623 : Blo 1695548 2544623 := bstep (se 1 (by rfl) ⟨1908467, by rfl⟩ : syracuseStep 2544623 = 3816935) B3816935
theorem B13759571 : Blo 1695548 13759571 := bstep (se 1 (by rfl) ⟨10319678, by rfl⟩ : syracuseStep 13759571 = 20639357) B20639357
theorem B6116447 : Blo 1695548 6116447 := bstep (se 1 (by rfl) ⟨4587335, by rfl⟩ : syracuseStep 6116447 = 9174671) B9174671
theorem B7247171 : Blo 1695548 7247171 := bstep (se 1 (by rfl) ⟨5435378, by rfl⟩ : syracuseStep 7247171 = 10870757) B10870757
theorem B2545007 : Blo 1695548 2545007 := bstep (se 1 (by rfl) ⟨1908755, by rfl⟩ : syracuseStep 2545007 = 3817511) B3817511
theorem B2864551 : Blo 1695548 2864551 := bstep (se 1 (by rfl) ⟨2148413, by rfl⟩ : syracuseStep 2864551 = 4296827) B4296827
theorem B2545127 : Blo 1695548 2545127 := bstep (se 1 (by rfl) ⟨1908845, by rfl⟩ : syracuseStep 2545127 = 3817691) B3817691
theorem B5437019 : Blo 1695548 5437019 := bstep (se 1 (by rfl) ⟨4077764, by rfl⟩ : syracuseStep 5437019 = 8155529) B8155529
theorem B2545289 : Blo 1695548 2545289 := bstep (se 2 (by rfl) ⟨954483, by rfl⟩ : syracuseStep 2545289 = 1908967) B1908967
theorem B2545307 : Blo 1695548 2545307 := bstep (se 1 (by rfl) ⟨1908980, by rfl⟩ : syracuseStep 2545307 = 3817961) B3817961
theorem B44086999 : Blo 1695548 44086999 := bstep (se 1 (by rfl) ⟨33065249, by rfl⟩ : syracuseStep 44086999 = 66130499) B66130499
theorem B3815135 : Blo 1695548 3815135 := bstep (se 1 (by rfl) ⟨2861351, by rfl⟩ : syracuseStep 3815135 = 5722703) B5722703
theorem B6879055 : Blo 1695548 6879055 := bstep (se 1 (by rfl) ⟨5159291, by rfl⟩ : syracuseStep 6879055 = 10318583) B10318583
theorem B2545499 : Blo 1695548 2545499 := bstep (se 1 (by rfl) ⟨1909124, by rfl⟩ : syracuseStep 2545499 = 3818249) B3818249
theorem B5158781 : Blo 1695548 5158781 := bstep (se 3 (by rfl) ⟨967271, by rfl⟩ : syracuseStep 5158781 = 1934543) B1934543
theorem B3815495 : Blo 1695548 3815495 := bstep (se 1 (by rfl) ⟨2861621, by rfl⟩ : syracuseStep 3815495 = 5723243) B5723243
theorem B4077707 : Blo 1695548 4077707 := bstep (se 1 (by rfl) ⟨3058280, by rfl⟩ : syracuseStep 4077707 = 6116561) B6116561
theorem B2545883 : Blo 1695548 2545883 := bstep (se 1 (by rfl) ⟨1909412, by rfl⟩ : syracuseStep 2545883 = 3818825) B3818825
theorem B5806367 : Blo 1695548 5806367 := bstep (se 1 (by rfl) ⟨4354775, by rfl⟩ : syracuseStep 5806367 = 8709551) B8709551
theorem B7551431 : Blo 1695548 7551431 := bstep (se 1 (by rfl) ⟨5663573, by rfl⟩ : syracuseStep 7551431 = 11327147) B11327147
theorem B2546153 : Blo 1695548 2546153 := bstep (se 2 (by rfl) ⟨954807, by rfl⟩ : syracuseStep 2546153 = 1909615) B1909615
theorem B99326459 : Blo 1695548 99326459 := bstep (se 1 (by rfl) ⟨74494844, by rfl⟩ : syracuseStep 99326459 = 148989689) B148989689
theorem B8583731 : Blo 1695548 8583731 := bstep (se 1 (by rfl) ⟨6437798, by rfl⟩ : syracuseStep 8583731 = 12875597) B12875597
theorem B2718299 : Blo 1695548 2718299 := bstep (se 1 (by rfl) ⟨2038724, by rfl⟩ : syracuseStep 2718299 = 4077449) B4077449
theorem B4831903 : Blo 1695548 4831903 := bstep (se 1 (by rfl) ⟨3623927, by rfl⟩ : syracuseStep 4831903 = 7247855) B7247855
theorem B3816161 : Blo 1695548 3816161 := bstep (se 2 (by rfl) ⟨1431060, by rfl⟩ : syracuseStep 3816161 = 2862121) B2862121
theorem B5159657 : Blo 1695548 5159657 := bstep (se 2 (by rfl) ⟨1934871, by rfl⟩ : syracuseStep 5159657 = 3869743) B3869743
theorem B1907527 : Blo 1695548 1907527 := bstep (se 1 (by rfl) ⟨1430645, by rfl⟩ : syracuseStep 1907527 = 2861291) B2861291
theorem B3816359 : Blo 1695548 3816359 := bstep (se 1 (by rfl) ⟨2862269, by rfl⟩ : syracuseStep 3816359 = 5724539) B5724539
theorem B3816539 : Blo 1695548 3816539 := bstep (se 1 (by rfl) ⟨2862404, by rfl⟩ : syracuseStep 3816539 = 5724809) B5724809
theorem B123829397 : Blo 1695548 123829397 := bstep (se 6 (by rfl) ⟨2902251, by rfl⟩ : syracuseStep 123829397 = 5804503) B5804503
theorem B1908175 : Blo 1695548 1908175 := bstep (se 1 (by rfl) ⟨1431131, by rfl⟩ : syracuseStep 1908175 = 2862263) B2862263
theorem B5725673 : Blo 1695548 5725673 := bstep (se 2 (by rfl) ⟨2147127, by rfl⟩ : syracuseStep 5725673 = 4294255) B4294255
theorem B92888693 : Blo 1695548 92888693 := bstep (se 5 (by rfl) ⟨4354157, by rfl⟩ : syracuseStep 92888693 = 8708315) B8708315
theorem B1908391 : Blo 1695548 1908391 := bstep (se 1 (by rfl) ⟨1431293, by rfl⟩ : syracuseStep 1908391 = 2862587) B2862587
theorem B3817295 : Blo 1695548 3817295 := bstep (se 1 (by rfl) ⟨2862971, by rfl⟩ : syracuseStep 3817295 = 5725943) B5725943
theorem B1695599 : Blo 1695548 1695599 := bstep (se 1 (by rfl) ⟨1271699, by rfl⟩ : syracuseStep 1695599 = 2543399) B2543399
theorem B3219355 : Blo 1695548 3219355 := bstep (se 1 (by rfl) ⟨2414516, by rfl⟩ : syracuseStep 3219355 = 4829033) B4829033
theorem B1695655 : Blo 1695548 1695655 := bstep (se 1 (by rfl) ⟨1271741, by rfl⟩ : syracuseStep 1695655 = 2543483) B2543483
theorem B1908679 : Blo 1695548 1908679 := bstep (se 1 (by rfl) ⟨1431509, by rfl⟩ : syracuseStep 1908679 = 2863019) B2863019
theorem B1695807 : Blo 1695548 1695807 := bstep (se 1 (by rfl) ⟨1271855, by rfl⟩ : syracuseStep 1695807 = 2543711) B2543711
theorem B1695815 : Blo 1695548 1695815 := bstep (se 1 (by rfl) ⟨1271861, by rfl⟩ : syracuseStep 1695815 = 2543723) B2543723
theorem B1695847 : Blo 1695548 1695847 := bstep (se 1 (by rfl) ⟨1271885, by rfl⟩ : syracuseStep 1695847 = 2543771) B2543771
theorem B36692189 : Blo 1695548 36692189 := bstep (se 3 (by rfl) ⟨6879785, by rfl⟩ : syracuseStep 36692189 = 13759571) B13759571
theorem B18334025 : Blo 1695548 18334025 := bstep (se 2 (by rfl) ⟨6875259, by rfl⟩ : syracuseStep 18334025 = 13750519) B13750519
theorem B1696415 : Blo 1695548 1696415 := bstep (se 1 (by rfl) ⟨1272311, by rfl⟩ : syracuseStep 1696415 = 2544623) B2544623
theorem B9798425 : Blo 1695548 9798425 := bstep (se 2 (by rfl) ⟨3674409, by rfl⟩ : syracuseStep 9798425 = 7348819) B7348819
theorem B19325789 : Blo 1695548 19325789 := bstep (se 3 (by rfl) ⟨3623585, by rfl⟩ : syracuseStep 19325789 = 7247171) B7247171
theorem B1696671 : Blo 1695548 1696671 := bstep (se 1 (by rfl) ⟨1272503, by rfl⟩ : syracuseStep 1696671 = 2545007) B2545007
theorem B14689189 : Blo 1695548 14689189 := bstep (se 4 (by rfl) ⟨1377111, by rfl⟩ : syracuseStep 14689189 = 2754223) B2754223
theorem B4588523 : Blo 1695548 4588523 := bstep (se 1 (by rfl) ⟨3441392, by rfl⟩ : syracuseStep 4588523 = 6882785) B6882785
theorem B1696751 : Blo 1695548 1696751 := bstep (se 1 (by rfl) ⟨1272563, by rfl⟩ : syracuseStep 1696751 = 2545127) B2545127
theorem B1696859 : Blo 1695548 1696859 := bstep (se 1 (by rfl) ⟨1272644, by rfl⟩ : syracuseStep 1696859 = 2545289) B2545289
theorem B1696871 : Blo 1695548 1696871 := bstep (se 1 (by rfl) ⟨1272653, by rfl⟩ : syracuseStep 1696871 = 2545307) B2545307
theorem B3818663 : Blo 1695548 3818663 := bstep (se 1 (by rfl) ⟨2863997, by rfl⟩ : syracuseStep 3818663 = 5727995) B5727995
theorem B1696999 : Blo 1695548 1696999 := bstep (se 1 (by rfl) ⟨1272749, by rfl⟩ : syracuseStep 1696999 = 2545499) B2545499
theorem B3622151 : Blo 1695548 3622151 := bstep (se 1 (by rfl) ⟨2716613, by rfl⟩ : syracuseStep 3622151 = 5433227) B5433227
theorem B3818771 : Blo 1695548 3818771 := bstep (se 1 (by rfl) ⟨2864078, by rfl⟩ : syracuseStep 3818771 = 5728157) B5728157
theorem B19334537 : Blo 1695548 19334537 := bstep (se 2 (by rfl) ⟨7250451, by rfl⟩ : syracuseStep 19334537 = 14500903) B14500903
theorem B8701339 : Blo 1695548 8701339 := bstep (se 1 (by rfl) ⟨6526004, by rfl⟩ : syracuseStep 8701339 = 13052009) B13052009
theorem B1697255 : Blo 1695548 1697255 := bstep (se 1 (by rfl) ⟨1272941, by rfl⟩ : syracuseStep 1697255 = 2545883) B2545883
theorem B1697435 : Blo 1695548 1697435 := bstep (se 1 (by rfl) ⟨1273076, by rfl⟩ : syracuseStep 1697435 = 2546153) B2546153
theorem B8587133 : Blo 1695548 8587133 := bstep (se 3 (by rfl) ⟨1610087, by rfl⟩ : syracuseStep 8587133 = 3220175) B3220175
theorem B3819401 : Blo 1695548 3819401 := bstep (se 2 (by rfl) ⟨1432275, by rfl⟩ : syracuseStep 3819401 = 2864551) B2864551
theorem B8587295 : Blo 1695548 8587295 := bstep (se 1 (by rfl) ⟨6440471, by rfl⟩ : syracuseStep 8587295 = 12880943) B12880943
theorem B82552931 : Blo 1695548 82552931 := bstep (se 1 (by rfl) ⟨61914698, by rfl⟩ : syracuseStep 82552931 = 123829397) B123829397
theorem B61925795 : Blo 1695548 61925795 := bstep (se 1 (by rfl) ⟨46444346, by rfl⟩ : syracuseStep 61925795 = 92888693) B92888693
theorem B5729021 : Blo 1695548 5729021 := bstep (se 3 (by rfl) ⟨1074191, by rfl⟩ : syracuseStep 5729021 = 2148383) B2148383
theorem B4352825 : Blo 1695548 4352825 := bstep (se 2 (by rfl) ⟨1632309, by rfl⟩ : syracuseStep 4352825 = 3264619) B3264619
theorem B3222355 : Blo 1695548 3222355 := bstep (se 1 (by rfl) ⟨2416766, by rfl⟩ : syracuseStep 3222355 = 4833533) B4833533
theorem B7244711 : Blo 1695548 7244711 := bstep (se 1 (by rfl) ⟨5433533, by rfl⟩ : syracuseStep 7244711 = 10867067) B10867067
theorem B2861993 : Blo 1695548 2861993 := bstep (se 2 (by rfl) ⟨1073247, by rfl⟩ : syracuseStep 2861993 = 2146495) B2146495
theorem B10873885 : Blo 1695548 10873885 := bstep (se 3 (by rfl) ⟨2038853, by rfl⟩ : syracuseStep 10873885 = 4077707) B4077707
theorem B10865735 : Blo 1695548 10865735 := bstep (se 1 (by rfl) ⟨8149301, by rfl⟩ : syracuseStep 10865735 = 16298603) B16298603
theorem B6442537 : Blo 1695548 6442537 := bstep (se 2 (by rfl) ⟨2415951, by rfl⟩ : syracuseStep 6442537 = 4831903) B4831903
theorem B3624679 : Blo 1695548 3624679 := bstep (se 1 (by rfl) ⟨2718509, by rfl⟩ : syracuseStep 3624679 = 5437019) B5437019
theorem B2543369 : Blo 1695548 2543369 := bstep (se 2 (by rfl) ⟨953763, by rfl⟩ : syracuseStep 2543369 = 1907527) B1907527
theorem B2543423 : Blo 1695548 2543423 := bstep (se 1 (by rfl) ⟨1907567, by rfl⟩ : syracuseStep 2543423 = 3815135) B3815135
theorem B2543663 : Blo 1695548 2543663 := bstep (se 1 (by rfl) ⟨1907747, by rfl⟩ : syracuseStep 2543663 = 3815495) B3815495
theorem B5582945 : Blo 1695548 5582945 := bstep (se 2 (by rfl) ⟨2093604, by rfl⟩ : syracuseStep 5582945 = 4187209) B4187209
theorem B3870911 : Blo 1695548 3870911 := bstep (se 1 (by rfl) ⟨2903183, by rfl⟩ : syracuseStep 3870911 = 5806367) B5806367
theorem B5157151 : Blo 1695548 5157151 := bstep (se 1 (by rfl) ⟨3867863, by rfl⟩ : syracuseStep 5157151 = 7735727) B7735727
theorem B5034287 : Blo 1695548 5034287 := bstep (se 1 (by rfl) ⟨3775715, by rfl⟩ : syracuseStep 5034287 = 7551431) B7551431
theorem B2863417 : Blo 1695548 2863417 := bstep (se 2 (by rfl) ⟨1073781, by rfl⟩ : syracuseStep 2863417 = 2147563) B2147563
theorem B5722487 : Blo 1695548 5722487 := bstep (se 1 (by rfl) ⟨4291865, by rfl⟩ : syracuseStep 5722487 = 8583731) B8583731
theorem B9793991 : Blo 1695548 9793991 := bstep (se 1 (by rfl) ⟨7345493, by rfl⟩ : syracuseStep 9793991 = 14690987) B14690987
theorem B2544107 : Blo 1695548 2544107 := bstep (se 1 (by rfl) ⟨1908080, by rfl⟩ : syracuseStep 2544107 = 3816161) B3816161
theorem B2544233 : Blo 1695548 2544233 := bstep (se 2 (by rfl) ⟨954087, by rfl⟩ : syracuseStep 2544233 = 1908175) B1908175
theorem B13759085 : Blo 1695548 13759085 := bstep (se 3 (by rfl) ⟨2579828, by rfl⟩ : syracuseStep 13759085 = 5159657) B5159657
theorem B2544239 : Blo 1695548 2544239 := bstep (se 1 (by rfl) ⟨1908179, by rfl⟩ : syracuseStep 2544239 = 3816359) B3816359
theorem B65229461 : Blo 1695548 65229461 := bstep (se 6 (by rfl) ⟨1528815, by rfl⟩ : syracuseStep 65229461 = 3057631) B3057631
theorem B2544359 : Blo 1695548 2544359 := bstep (se 1 (by rfl) ⟨1908269, by rfl⟩ : syracuseStep 2544359 = 3816539) B3816539
theorem B21738233 : Blo 1695548 21738233 := bstep (se 2 (by rfl) ⟨8151837, by rfl⟩ : syracuseStep 21738233 = 16303675) B16303675
theorem B2544521 : Blo 1695548 2544521 := bstep (se 2 (by rfl) ⟨954195, by rfl⟩ : syracuseStep 2544521 = 1908391) B1908391
theorem B58782665 : Blo 1695548 58782665 := bstep (se 2 (by rfl) ⟨22043499, by rfl⟩ : syracuseStep 58782665 = 44086999) B44086999
theorem B9172073 : Blo 1695548 9172073 := bstep (se 2 (by rfl) ⟨3439527, by rfl⟩ : syracuseStep 9172073 = 6879055) B6879055
theorem B11023543 : Blo 1695548 11023543 := bstep (se 1 (by rfl) ⟨8267657, by rfl⟩ : syracuseStep 11023543 = 16535315) B16535315
theorem B2544863 : Blo 1695548 2544863 := bstep (se 1 (by rfl) ⟨1908647, by rfl⟩ : syracuseStep 2544863 = 3817295) B3817295
theorem B2544905 : Blo 1695548 2544905 := bstep (se 2 (by rfl) ⟨954339, by rfl⟩ : syracuseStep 2544905 = 1908679) B1908679
theorem B5723567 : Blo 1695548 5723567 := bstep (se 1 (by rfl) ⟨4292675, by rfl⟩ : syracuseStep 5723567 = 8585351) B8585351
theorem B4830799 : Blo 1695548 4830799 := bstep (se 1 (by rfl) ⟨3623099, by rfl⟩ : syracuseStep 4830799 = 7246199) B7246199
theorem B2545343 : Blo 1695548 2545343 := bstep (se 1 (by rfl) ⟨1909007, by rfl⟩ : syracuseStep 2545343 = 3818015) B3818015
theorem B2545385 : Blo 1695548 2545385 := bstep (se 2 (by rfl) ⟨954519, by rfl⟩ : syracuseStep 2545385 = 1909039) B1909039
theorem B2545391 : Blo 1695548 2545391 := bstep (se 1 (by rfl) ⟨1909043, by rfl⟩ : syracuseStep 2545391 = 3818087) B3818087
theorem B8591183 : Blo 1695548 8591183 := bstep (se 1 (by rfl) ⟨6443387, by rfl⟩ : syracuseStep 8591183 = 12886775) B12886775
theorem B4077631 : Blo 1695548 4077631 := bstep (se 1 (by rfl) ⟨3058223, by rfl⟩ : syracuseStep 4077631 = 6116447) B6116447
theorem B209025157 : Blo 1695548 209025157 := bstep (se 4 (by rfl) ⟨19596108, by rfl⟩ : syracuseStep 209025157 = 39192217) B39192217
theorem B8591507 : Blo 1695548 8591507 := bstep (se 1 (by rfl) ⟨6443630, by rfl⟩ : syracuseStep 8591507 = 12887261) B12887261
theorem B8149207 : Blo 1695548 8149207 := bstep (se 1 (by rfl) ⟨6111905, by rfl⟩ : syracuseStep 8149207 = 12223811) B12223811
theorem B6445271 : Blo 1695548 6445271 := bstep (se 1 (by rfl) ⟨4833953, by rfl⟩ : syracuseStep 6445271 = 9667907) B9667907
theorem B2545895 : Blo 1695548 2545895 := bstep (se 1 (by rfl) ⟨1909421, by rfl⟩ : syracuseStep 2545895 = 3818843) B3818843
theorem B2546075 : Blo 1695548 2546075 := bstep (se 1 (by rfl) ⟨1909556, by rfl⟩ : syracuseStep 2546075 = 3819113) B3819113
theorem B5724647 : Blo 1695548 5724647 := bstep (se 1 (by rfl) ⟨4293485, by rfl⟩ : syracuseStep 5724647 = 8586971) B8586971
theorem B3439187 : Blo 1695548 3439187 := bstep (se 1 (by rfl) ⟨2579390, by rfl⟩ : syracuseStep 3439187 = 5158781) B5158781
theorem B9656927 : Blo 1695548 9656927 := bstep (se 1 (by rfl) ⟨7242695, by rfl⟩ : syracuseStep 9656927 = 14485391) B14485391
theorem B264870557 : Blo 1695548 264870557 := bstep (se 3 (by rfl) ⟨49663229, by rfl⟩ : syracuseStep 264870557 = 99326459) B99326459
theorem B21732083 : Blo 1695548 21732083 := bstep (se 1 (by rfl) ⟨16299062, by rfl⟩ : syracuseStep 21732083 = 32598125) B32598125
theorem B7248797 : Blo 1695548 7248797 := bstep (se 3 (by rfl) ⟨1359149, by rfl⟩ : syracuseStep 7248797 = 2718299) B2718299
theorem B6970319 : Blo 1695548 6970319 := bstep (se 1 (by rfl) ⟨5227739, by rfl⟩ : syracuseStep 6970319 = 10455479) B10455479
theorem B1907707 : Blo 1695548 1907707 := bstep (se 1 (by rfl) ⟨1430780, by rfl⟩ : syracuseStep 1907707 = 2861561) B2861561
theorem B1907743 : Blo 1695548 1907743 := bstep (se 1 (by rfl) ⟨1430807, by rfl⟩ : syracuseStep 1907743 = 2861615) B2861615
theorem B3816521 : Blo 1695548 3816521 := bstep (se 2 (by rfl) ⟨1431195, by rfl⟩ : syracuseStep 3816521 = 2862391) B2862391
theorem B1907887 : Blo 1695548 1907887 := bstep (se 1 (by rfl) ⟨1430915, by rfl⟩ : syracuseStep 1907887 = 2861831) B2861831
theorem B1908031 : Blo 1695548 1908031 := bstep (se 1 (by rfl) ⟨1431023, by rfl⟩ : syracuseStep 1908031 = 2862047) B2862047
theorem B3817115 : Blo 1695548 3817115 := bstep (se 1 (by rfl) ⟨2862836, by rfl⟩ : syracuseStep 3817115 = 5725673) B5725673
theorem B3817313 : Blo 1695548 3817313 := bstep (se 2 (by rfl) ⟨1431492, by rfl⟩ : syracuseStep 3817313 = 2862985) B2862985
theorem B4292473 : Blo 1695548 4292473 := bstep (se 2 (by rfl) ⟨1609677, by rfl⟩ : syracuseStep 4292473 = 3219355) B3219355
theorem B1908607 : Blo 1695548 1908607 := bstep (se 1 (by rfl) ⟨1431455, by rfl⟩ : syracuseStep 1908607 = 2862911) B2862911
theorem B1695727 : Blo 1695548 1695727 := bstep (se 1 (by rfl) ⟨1271795, by rfl⟩ : syracuseStep 1695727 = 2543591) B2543591
theorem B11018227 : Blo 1695548 11018227 := bstep (se 1 (by rfl) ⟨8263670, by rfl⟩ : syracuseStep 11018227 = 16527341) B16527341
theorem B1695775 : Blo 1695548 1695775 := bstep (se 1 (by rfl) ⟨1271831, by rfl⟩ : syracuseStep 1695775 = 2543663) B2543663
theorem B2580607 : Blo 1695548 2580607 := bstep (se 1 (by rfl) ⟨1935455, by rfl⟩ : syracuseStep 2580607 = 3870911) B3870911
theorem B24461459 : Blo 1695548 24461459 := bstep (se 1 (by rfl) ⟨18346094, by rfl⟩ : syracuseStep 24461459 = 36692189) B36692189
theorem B278700209 : Blo 1695548 278700209 := bstep (se 2 (by rfl) ⟨104512578, by rfl⟩ : syracuseStep 278700209 = 209025157) B209025157
theorem B12222683 : Blo 1695548 12222683 := bstep (se 1 (by rfl) ⟨9167012, by rfl⟩ : syracuseStep 12222683 = 18334025) B18334025
theorem B1696071 : Blo 1695548 1696071 := bstep (se 1 (by rfl) ⟨1272053, by rfl⟩ : syracuseStep 1696071 = 2544107) B2544107
theorem B1696155 : Blo 1695548 1696155 := bstep (se 1 (by rfl) ⟨1272116, by rfl⟩ : syracuseStep 1696155 = 2544233) B2544233
theorem B1696159 : Blo 1695548 1696159 := bstep (se 1 (by rfl) ⟨1272119, by rfl⟩ : syracuseStep 1696159 = 2544239) B2544239
theorem B3817889 : Blo 1695548 3817889 := bstep (se 2 (by rfl) ⟨1431708, by rfl⟩ : syracuseStep 3817889 = 2863417) B2863417
theorem B1696239 : Blo 1695548 1696239 := bstep (se 1 (by rfl) ⟨1272179, by rfl⟩ : syracuseStep 1696239 = 2544359) B2544359
theorem B14492155 : Blo 1695548 14492155 := bstep (se 1 (by rfl) ⟨10869116, by rfl⟩ : syracuseStep 14492155 = 21738233) B21738233
theorem B1696347 : Blo 1695548 1696347 := bstep (se 1 (by rfl) ⟨1272260, by rfl⟩ : syracuseStep 1696347 = 2544521) B2544521
theorem B1696575 : Blo 1695548 1696575 := bstep (se 1 (by rfl) ⟨1272431, by rfl⟩ : syracuseStep 1696575 = 2544863) B2544863
theorem B1696603 : Blo 1695548 1696603 := bstep (se 1 (by rfl) ⟨1272452, by rfl⟩ : syracuseStep 1696603 = 2544905) B2544905
theorem B1696895 : Blo 1695548 1696895 := bstep (se 1 (by rfl) ⟨1272671, by rfl⟩ : syracuseStep 1696895 = 2545343) B2545343
theorem B1696923 : Blo 1695548 1696923 := bstep (se 1 (by rfl) ⟨1272692, by rfl⟩ : syracuseStep 1696923 = 2545385) B2545385
theorem B1696927 : Blo 1695548 1696927 := bstep (se 1 (by rfl) ⟨1272695, by rfl⟩ : syracuseStep 1696927 = 2545391) B2545391
theorem B26117309 : Blo 1695548 26117309 := bstep (se 3 (by rfl) ⟨4896995, by rfl⟩ : syracuseStep 26117309 = 9793991) B9793991
theorem B5727455 : Blo 1695548 5727455 := bstep (se 1 (by rfl) ⟨4295591, by rfl⟩ : syracuseStep 5727455 = 8591183) B8591183
theorem B55035287 : Blo 1695548 55035287 := bstep (se 1 (by rfl) ⟨41276465, by rfl⟩ : syracuseStep 55035287 = 82552931) B82552931
theorem B5727671 : Blo 1695548 5727671 := bstep (se 1 (by rfl) ⟨4295753, by rfl⟩ : syracuseStep 5727671 = 8591507) B8591507
theorem B1697263 : Blo 1695548 1697263 := bstep (se 1 (by rfl) ⟨1272947, by rfl⟩ : syracuseStep 1697263 = 2545895) B2545895
theorem B14698057 : Blo 1695548 14698057 := bstep (se 2 (by rfl) ⟨5511771, by rfl⟩ : syracuseStep 14698057 = 11023543) B11023543
theorem B1697383 : Blo 1695548 1697383 := bstep (se 1 (by rfl) ⟨1273037, by rfl⟩ : syracuseStep 1697383 = 2546075) B2546075
theorem B176580371 : Blo 1695548 176580371 := bstep (se 1 (by rfl) ⟨132435278, by rfl⟩ : syracuseStep 176580371 = 264870557) B264870557
theorem B3819347 : Blo 1695548 3819347 := bstep (se 1 (by rfl) ⟨2864510, by rfl⟩ : syracuseStep 3819347 = 5729021) B5729021
theorem B11601785 : Blo 1695548 11601785 := bstep (se 2 (by rfl) ⟨4350669, by rfl⟩ : syracuseStep 11601785 = 8701339) B8701339
theorem B4646879 : Blo 1695548 4646879 := bstep (se 1 (by rfl) ⟨3485159, by rfl⟩ : syracuseStep 4646879 = 6970319) B6970319
theorem B7243823 : Blo 1695548 7243823 := bstep (se 1 (by rfl) ⟨5432867, by rfl⟩ : syracuseStep 7243823 = 10865735) B10865735
theorem B6441065 : Blo 1695548 6441065 := bstep (se 2 (by rfl) ⟨2415399, by rfl⟩ : syracuseStep 6441065 = 4830799) B4830799
theorem B14690969 : Blo 1695548 14690969 := bstep (se 2 (by rfl) ⟨5509113, by rfl⟩ : syracuseStep 14690969 = 11018227) B11018227
theorem B3721963 : Blo 1695548 3721963 := bstep (se 1 (by rfl) ⟨2791472, by rfl⟩ : syracuseStep 3721963 = 5582945) B5582945
theorem B10865609 : Blo 1695548 10865609 := bstep (se 2 (by rfl) ⟨4074603, by rfl⟩ : syracuseStep 10865609 = 8149207) B8149207
theorem B43486307 : Blo 1695548 43486307 := bstep (se 1 (by rfl) ⟨32614730, by rfl⟩ : syracuseStep 43486307 = 65229461) B65229461
theorem B6532283 : Blo 1695548 6532283 := bstep (se 1 (by rfl) ⟨4899212, by rfl⟩ : syracuseStep 6532283 = 9798425) B9798425
theorem B3059015 : Blo 1695548 3059015 := bstep (se 1 (by rfl) ⟨2294261, by rfl⟩ : syracuseStep 3059015 = 4588523) B4588523
theorem B12889691 : Blo 1695548 12889691 := bstep (se 1 (by rfl) ⟨9667268, by rfl⟩ : syracuseStep 12889691 = 19334537) B19334537
theorem B4296473 : Blo 1695548 4296473 := bstep (se 2 (by rfl) ⟨1611177, by rfl⟩ : syracuseStep 4296473 = 3222355) B3222355
theorem B2543609 : Blo 1695548 2543609 := bstep (se 2 (by rfl) ⟨953853, by rfl⟩ : syracuseStep 2543609 = 1907707) B1907707
theorem B2543657 : Blo 1695548 2543657 := bstep (se 2 (by rfl) ⟨953871, by rfl⟩ : syracuseStep 2543657 = 1907743) B1907743
theorem B4296847 : Blo 1695548 4296847 := bstep (se 1 (by rfl) ⟨3222635, by rfl⟩ : syracuseStep 4296847 = 6445271) B6445271
theorem B27504805 : Blo 1695548 27504805 := bstep (se 4 (by rfl) ⟨2578575, by rfl⟩ : syracuseStep 27504805 = 5157151) B5157151
theorem B2543849 : Blo 1695548 2543849 := bstep (se 2 (by rfl) ⟨953943, by rfl⟩ : syracuseStep 2543849 = 1907887) B1907887
theorem B41283863 : Blo 1695548 41283863 := bstep (se 1 (by rfl) ⟨30962897, by rfl⟩ : syracuseStep 41283863 = 61925795) B61925795
theorem B2544041 : Blo 1695548 2544041 := bstep (se 2 (by rfl) ⟨954015, by rfl⟩ : syracuseStep 2544041 = 1908031) B1908031
theorem B14488055 : Blo 1695548 14488055 := bstep (se 1 (by rfl) ⟨10866041, by rfl⟩ : syracuseStep 14488055 = 21732083) B21732083
theorem B4829807 : Blo 1695548 4829807 := bstep (se 1 (by rfl) ⟨3622355, by rfl⟩ : syracuseStep 4829807 = 7244711) B7244711
theorem B2544347 : Blo 1695548 2544347 := bstep (se 1 (by rfl) ⟨1908260, by rfl⟩ : syracuseStep 2544347 = 3816521) B3816521
theorem B8590049 : Blo 1695548 8590049 := bstep (se 2 (by rfl) ⟨3221268, by rfl⟩ : syracuseStep 8590049 = 6442537) B6442537
theorem B2544743 : Blo 1695548 2544743 := bstep (se 1 (by rfl) ⟨1908557, by rfl⟩ : syracuseStep 2544743 = 3817115) B3817115
theorem B5723297 : Blo 1695548 5723297 := bstep (se 2 (by rfl) ⟨2146236, by rfl⟩ : syracuseStep 5723297 = 4292473) B4292473
theorem B2544809 : Blo 1695548 2544809 := bstep (se 2 (by rfl) ⟨954303, by rfl⟩ : syracuseStep 2544809 = 1908607) B1908607
theorem B2544875 : Blo 1695548 2544875 := bstep (se 1 (by rfl) ⟨1908656, by rfl⟩ : syracuseStep 2544875 = 3817313) B3817313
theorem B5436841 : Blo 1695548 5436841 := bstep (se 2 (by rfl) ⟨2038815, by rfl⟩ : syracuseStep 5436841 = 4077631) B4077631
theorem B3356191 : Blo 1695548 3356191 := bstep (se 1 (by rfl) ⟨2517143, by rfl⟩ : syracuseStep 3356191 = 5034287) B5034287
theorem B3814991 : Blo 1695548 3814991 := bstep (se 1 (by rfl) ⟨2861243, by rfl⟩ : syracuseStep 3814991 = 5722487) B5722487
theorem B24458861 : Blo 1695548 24458861 := bstep (se 3 (by rfl) ⟨4586036, by rfl⟩ : syracuseStep 24458861 = 9172073) B9172073
theorem B9172723 : Blo 1695548 9172723 := bstep (se 1 (by rfl) ⟨6879542, by rfl⟩ : syracuseStep 9172723 = 13759085) B13759085
theorem B12883859 : Blo 1695548 12883859 := bstep (se 1 (by rfl) ⟨9662894, by rfl⟩ : syracuseStep 12883859 = 19325789) B19325789
theorem B39188443 : Blo 1695548 39188443 := bstep (se 1 (by rfl) ⟨29391332, by rfl⟩ : syracuseStep 39188443 = 58782665) B58782665
theorem B2545775 : Blo 1695548 2545775 := bstep (se 1 (by rfl) ⟨1909331, by rfl⟩ : syracuseStep 2545775 = 3818663) B3818663
theorem B2414767 : Blo 1695548 2414767 := bstep (se 1 (by rfl) ⟨1811075, by rfl⟩ : syracuseStep 2414767 = 3622151) B3622151
theorem B2545847 : Blo 1695548 2545847 := bstep (se 1 (by rfl) ⟨1909385, by rfl⟩ : syracuseStep 2545847 = 3818771) B3818771
theorem B3815711 : Blo 1695548 3815711 := bstep (se 1 (by rfl) ⟨2861783, by rfl⟩ : syracuseStep 3815711 = 5723567) B5723567
theorem B19331621 : Blo 1695548 19331621 := bstep (se 4 (by rfl) ⟨1812339, by rfl⟩ : syracuseStep 19331621 = 3624679) B3624679
theorem B19585585 : Blo 1695548 19585585 := bstep (se 2 (by rfl) ⟨7344594, by rfl⟩ : syracuseStep 19585585 = 14689189) B14689189
theorem B5724755 : Blo 1695548 5724755 := bstep (se 1 (by rfl) ⟨4293566, by rfl⟩ : syracuseStep 5724755 = 8587133) B8587133
theorem B2546267 : Blo 1695548 2546267 := bstep (se 1 (by rfl) ⟨1909700, by rfl⟩ : syracuseStep 2546267 = 3819401) B3819401
theorem B5724863 : Blo 1695548 5724863 := bstep (se 1 (by rfl) ⟨4293647, by rfl⟩ : syracuseStep 5724863 = 8587295) B8587295
theorem B14498513 : Blo 1695548 14498513 := bstep (se 2 (by rfl) ⟨5436942, by rfl⟩ : syracuseStep 14498513 = 10873885) B10873885
theorem B3816431 : Blo 1695548 3816431 := bstep (se 1 (by rfl) ⟨2862323, by rfl⟩ : syracuseStep 3816431 = 5724647) B5724647
theorem B2292791 : Blo 1695548 2292791 := bstep (se 1 (by rfl) ⟨1719593, by rfl⟩ : syracuseStep 2292791 = 3439187) B3439187
theorem B6437951 : Blo 1695548 6437951 := bstep (se 1 (by rfl) ⟨4828463, by rfl⟩ : syracuseStep 6437951 = 9656927) B9656927
theorem B4832531 : Blo 1695548 4832531 := bstep (se 1 (by rfl) ⟨3624398, by rfl⟩ : syracuseStep 4832531 = 7248797) B7248797
theorem B1907995 : Blo 1695548 1907995 := bstep (se 1 (by rfl) ⟨1430996, by rfl⟩ : syracuseStep 1907995 = 2861993) B2861993
theorem B11607533 : Blo 1695548 11607533 := bstep (se 3 (by rfl) ⟨2176412, by rfl⟩ : syracuseStep 11607533 = 4352825) B4352825
theorem B1695579 : Blo 1695548 1695579 := bstep (se 1 (by rfl) ⟨1271684, by rfl⟩ : syracuseStep 1695579 = 2543369) B2543369
theorem B1695615 : Blo 1695548 1695615 := bstep (se 1 (by rfl) ⟨1271711, by rfl⟩ : syracuseStep 1695615 = 2543423) B2543423
theorem B1695771 : Blo 1695548 1695771 := bstep (se 1 (by rfl) ⟨1271828, by rfl⟩ : syracuseStep 1695771 = 2543657) B2543657
theorem B1695899 : Blo 1695548 1695899 := bstep (se 1 (by rfl) ⟨1271924, by rfl⟩ : syracuseStep 1695899 = 2543849) B2543849
theorem B3440809 : Blo 1695548 3440809 := bstep (se 2 (by rfl) ⟨1290303, by rfl⟩ : syracuseStep 3440809 = 2580607) B2580607
theorem B3219689 : Blo 1695548 3219689 := bstep (se 2 (by rfl) ⟨1207383, by rfl⟩ : syracuseStep 3219689 = 2414767) B2414767
theorem B1696027 : Blo 1695548 1696027 := bstep (se 1 (by rfl) ⟨1272020, by rfl⟩ : syracuseStep 1696027 = 2544041) B2544041
theorem B9658703 : Blo 1695548 9658703 := bstep (se 1 (by rfl) ⟨7244027, by rfl⟩ : syracuseStep 9658703 = 14488055) B14488055
theorem B1696231 : Blo 1695548 1696231 := bstep (se 1 (by rfl) ⟨1272173, by rfl⟩ : syracuseStep 1696231 = 2544347) B2544347
theorem B5726699 : Blo 1695548 5726699 := bstep (se 1 (by rfl) ⟨4295024, by rfl⟩ : syracuseStep 5726699 = 8590049) B8590049
theorem B1696495 : Blo 1695548 1696495 := bstep (se 1 (by rfl) ⟨1272371, by rfl⟩ : syracuseStep 1696495 = 2544743) B2544743
theorem B32629493 : Blo 1695548 32629493 := bstep (se 5 (by rfl) ⟨1529507, by rfl⟩ : syracuseStep 32629493 = 3059015) B3059015
theorem B1696539 : Blo 1695548 1696539 := bstep (se 1 (by rfl) ⟨1272404, by rfl⟩ : syracuseStep 1696539 = 2544809) B2544809
theorem B3818303 : Blo 1695548 3818303 := bstep (se 1 (by rfl) ⟨2863727, by rfl⟩ : syracuseStep 3818303 = 5727455) B5727455
theorem B1696583 : Blo 1695548 1696583 := bstep (se 1 (by rfl) ⟨1272437, by rfl⟩ : syracuseStep 1696583 = 2544875) B2544875
theorem B3818447 : Blo 1695548 3818447 := bstep (se 1 (by rfl) ⟨2863835, by rfl⟩ : syracuseStep 3818447 = 5727671) B5727671
theorem B7734523 : Blo 1695548 7734523 := bstep (se 1 (by rfl) ⟨5800892, by rfl⟩ : syracuseStep 7734523 = 11601785) B11601785
theorem B3097919 : Blo 1695548 3097919 := bstep (se 1 (by rfl) ⟨2323439, by rfl⟩ : syracuseStep 3097919 = 4646879) B4646879
theorem B4294043 : Blo 1695548 4294043 := bstep (se 1 (by rfl) ⟨3220532, by rfl⟩ : syracuseStep 4294043 = 6441065) B6441065
theorem B1697183 : Blo 1695548 1697183 := bstep (se 1 (by rfl) ⟨1272887, by rfl⟩ : syracuseStep 1697183 = 2545775) B2545775
theorem B1697231 : Blo 1695548 1697231 := bstep (se 1 (by rfl) ⟨1272923, by rfl⟩ : syracuseStep 1697231 = 2545847) B2545847
theorem B12879485 : Blo 1695548 12879485 := bstep (se 3 (by rfl) ⟨2414903, by rfl⟩ : syracuseStep 12879485 = 4829807) B4829807
theorem B12887747 : Blo 1695548 12887747 := bstep (se 1 (by rfl) ⟨9665810, by rfl⟩ : syracuseStep 12887747 = 19331621) B19331621
theorem B1697511 : Blo 1695548 1697511 := bstep (se 1 (by rfl) ⟨1273133, by rfl⟩ : syracuseStep 1697511 = 2546267) B2546267
theorem B7243739 : Blo 1695548 7243739 := bstep (se 1 (by rfl) ⟨5432804, by rfl⟩ : syracuseStep 7243739 = 10865609) B10865609
theorem B4474921 : Blo 1695548 4474921 := bstep (se 2 (by rfl) ⟨1678095, by rfl⟩ : syracuseStep 4474921 = 3356191) B3356191
theorem B19597409 : Blo 1695548 19597409 := bstep (se 2 (by rfl) ⟨7349028, by rfl⟩ : syracuseStep 19597409 = 14698057) B14698057
theorem B3221687 : Blo 1695548 3221687 := bstep (se 1 (by rfl) ⟨2416265, by rfl⟩ : syracuseStep 3221687 = 4832531) B4832531
theorem B52251257 : Blo 1695548 52251257 := bstep (se 2 (by rfl) ⟨19594221, by rfl⟩ : syracuseStep 52251257 = 39188443) B39188443
theorem B5729129 : Blo 1695548 5729129 := bstep (se 2 (by rfl) ⟨2148423, by rfl⟩ : syracuseStep 5729129 = 4296847) B4296847
theorem B17419421 : Blo 1695548 17419421 := bstep (se 3 (by rfl) ⟨3266141, by rfl⟩ : syracuseStep 17419421 = 6532283) B6532283
theorem B24456437 : Blo 1695548 24456437 := bstep (se 5 (by rfl) ⟨1146395, by rfl⟩ : syracuseStep 24456437 = 2292791) B2292791
theorem B17411539 : Blo 1695548 17411539 := bstep (se 1 (by rfl) ⟨13058654, by rfl⟩ : syracuseStep 17411539 = 26117309) B26117309
theorem B2543327 : Blo 1695548 2543327 := bstep (se 1 (by rfl) ⟨1907495, by rfl⟩ : syracuseStep 2543327 = 3814991) B3814991
theorem B1695739 : Blo 1695548 1695739 := bstep (se 1 (by rfl) ⟨1271804, by rfl⟩ : syracuseStep 1695739 = 2543609) B2543609
theorem B16305907 : Blo 1695548 16305907 := bstep (se 1 (by rfl) ⟨12229430, by rfl⟩ : syracuseStep 16305907 = 24458861) B24458861
theorem B8589239 : Blo 1695548 8589239 := bstep (se 1 (by rfl) ⟨6441929, by rfl⟩ : syracuseStep 8589239 = 12883859) B12883859
theorem B4829215 : Blo 1695548 4829215 := bstep (se 1 (by rfl) ⟨3621911, by rfl⟩ : syracuseStep 4829215 = 7243823) B7243823
theorem B2543807 : Blo 1695548 2543807 := bstep (se 1 (by rfl) ⟨1907855, by rfl⟩ : syracuseStep 2543807 = 3815711) B3815711
theorem B2543993 : Blo 1695548 2543993 := bstep (se 2 (by rfl) ⟨953997, by rfl⟩ : syracuseStep 2543993 = 1907995) B1907995
theorem B9793979 : Blo 1695548 9793979 := bstep (se 1 (by rfl) ⟨7345484, by rfl⟩ : syracuseStep 9793979 = 14690969) B14690969
theorem B2544287 : Blo 1695548 2544287 := bstep (se 1 (by rfl) ⟨1908215, by rfl⟩ : syracuseStep 2544287 = 3816431) B3816431
theorem B470880989 : Blo 1695548 470880989 := bstep (se 3 (by rfl) ⟨88290185, by rfl⟩ : syracuseStep 470880989 = 176580371) B176580371
theorem B7738355 : Blo 1695548 7738355 := bstep (se 1 (by rfl) ⟨5803766, by rfl⟩ : syracuseStep 7738355 = 11607533) B11607533
theorem B2864315 : Blo 1695548 2864315 := bstep (se 1 (by rfl) ⟨2148236, by rfl⟩ : syracuseStep 2864315 = 4296473) B4296473
theorem B16307639 : Blo 1695548 16307639 := bstep (se 1 (by rfl) ⟨12230729, by rfl⟩ : syracuseStep 16307639 = 24461459) B24461459
theorem B185800139 : Blo 1695548 185800139 := bstep (se 1 (by rfl) ⟨139350104, by rfl⟩ : syracuseStep 185800139 = 278700209) B278700209
theorem B8148455 : Blo 1695548 8148455 := bstep (se 1 (by rfl) ⟨6111341, by rfl⟩ : syracuseStep 8148455 = 12222683) B12222683
theorem B27522575 : Blo 1695548 27522575 := bstep (se 1 (by rfl) ⟨20641931, by rfl⟩ : syracuseStep 27522575 = 41283863) B41283863
theorem B36673073 : Blo 1695548 36673073 := bstep (se 2 (by rfl) ⟨13752402, by rfl⟩ : syracuseStep 36673073 = 27504805) B27504805
theorem B2545259 : Blo 1695548 2545259 := bstep (se 1 (by rfl) ⟨1908944, by rfl⟩ : syracuseStep 2545259 = 3817889) B3817889
theorem B19322873 : Blo 1695548 19322873 := bstep (se 2 (by rfl) ⟨7246077, by rfl⟩ : syracuseStep 19322873 = 14492155) B14492155
theorem B26114113 : Blo 1695548 26114113 := bstep (se 2 (by rfl) ⟨9792792, by rfl⟩ : syracuseStep 26114113 = 19585585) B19585585
theorem B3815531 : Blo 1695548 3815531 := bstep (se 1 (by rfl) ⟨2861648, by rfl⟩ : syracuseStep 3815531 = 5723297) B5723297
theorem B36690191 : Blo 1695548 36690191 := bstep (se 1 (by rfl) ⟨27517643, by rfl⟩ : syracuseStep 36690191 = 55035287) B55035287
theorem B4962617 : Blo 1695548 4962617 := bstep (se 2 (by rfl) ⟨1860981, by rfl⟩ : syracuseStep 4962617 = 3721963) B3721963
theorem B2546231 : Blo 1695548 2546231 := bstep (se 1 (by rfl) ⟨1909673, by rfl⟩ : syracuseStep 2546231 = 3819347) B3819347
theorem B3816503 : Blo 1695548 3816503 := bstep (se 1 (by rfl) ⟨2862377, by rfl⟩ : syracuseStep 3816503 = 5724755) B5724755
theorem B3816575 : Blo 1695548 3816575 := bstep (se 1 (by rfl) ⟨2862431, by rfl⟩ : syracuseStep 3816575 = 5724863) B5724863
theorem B9665675 : Blo 1695548 9665675 := bstep (se 1 (by rfl) ⟨7249256, by rfl⟩ : syracuseStep 9665675 = 14498513) B14498513
theorem B7249121 : Blo 1695548 7249121 := bstep (se 2 (by rfl) ⟨2718420, by rfl⟩ : syracuseStep 7249121 = 5436841) B5436841
theorem B4291967 : Blo 1695548 4291967 := bstep (se 1 (by rfl) ⟨3218975, by rfl⟩ : syracuseStep 4291967 = 6437951) B6437951
theorem B28990871 : Blo 1695548 28990871 := bstep (se 1 (by rfl) ⟨21743153, by rfl⟩ : syracuseStep 28990871 = 43486307) B43486307
theorem B12230297 : Blo 1695548 12230297 := bstep (se 2 (by rfl) ⟨4586361, by rfl⟩ : syracuseStep 12230297 = 9172723) B9172723
theorem B8593127 : Blo 1695548 8593127 := bstep (se 1 (by rfl) ⟨6444845, by rfl⟩ : syracuseStep 8593127 = 12889691) B12889691
theorem B6438953 : Blo 1695548 6438953 := bstep (se 2 (by rfl) ⟨2414607, by rfl⟩ : syracuseStep 6438953 = 4829215) B4829215
theorem B1695871 : Blo 1695548 1695871 := bstep (se 1 (by rfl) ⟨1271903, by rfl⟩ : syracuseStep 1695871 = 2543807) B2543807
theorem B6439135 : Blo 1695548 6439135 := bstep (se 1 (by rfl) ⟨4829351, by rfl⟩ : syracuseStep 6439135 = 9658703) B9658703
theorem B1695995 : Blo 1695548 1695995 := bstep (se 1 (by rfl) ⟨1271996, by rfl⟩ : syracuseStep 1695995 = 2543993) B2543993
theorem B6529319 : Blo 1695548 6529319 := bstep (se 1 (by rfl) ⟨4896989, by rfl⟩ : syracuseStep 6529319 = 9793979) B9793979
theorem B3817799 : Blo 1695548 3817799 := bstep (se 1 (by rfl) ⟨2863349, by rfl⟩ : syracuseStep 3817799 = 5726699) B5726699
theorem B1696191 : Blo 1695548 1696191 := bstep (se 1 (by rfl) ⟨1272143, by rfl⟩ : syracuseStep 1696191 = 2544287) B2544287
theorem B8585837 : Blo 1695548 8585837 := bstep (se 3 (by rfl) ⟨1609844, by rfl⟩ : syracuseStep 8585837 = 3219689) B3219689
theorem B1909543 : Blo 1695548 1909543 := bstep (se 1 (by rfl) ⟨1432157, by rfl⟩ : syracuseStep 1909543 = 2864315) B2864315
theorem B2065279 : Blo 1695548 2065279 := bstep (se 1 (by rfl) ⟨1548959, by rfl⟩ : syracuseStep 2065279 = 3097919) B3097919
theorem B18350981 : Blo 1695548 18350981 := bstep (se 4 (by rfl) ⟨1720404, by rfl⟩ : syracuseStep 18350981 = 3440809) B3440809
theorem B10871759 : Blo 1695548 10871759 := bstep (se 1 (by rfl) ⟨8153819, by rfl⟩ : syracuseStep 10871759 = 16307639) B16307639
theorem B5432303 : Blo 1695548 5432303 := bstep (se 1 (by rfl) ⟨4074227, by rfl⟩ : syracuseStep 5432303 = 8148455) B8148455
theorem B1696839 : Blo 1695548 1696839 := bstep (se 1 (by rfl) ⟨1272629, by rfl⟩ : syracuseStep 1696839 = 2545259) B2545259
theorem B8586323 : Blo 1695548 8586323 := bstep (se 1 (by rfl) ⟨6439742, by rfl⟩ : syracuseStep 8586323 = 12879485) B12879485
theorem B2147791 : Blo 1695548 2147791 := bstep (se 1 (by rfl) ⟨1610843, by rfl⟩ : syracuseStep 2147791 = 3221687) B3221687
theorem B1697487 : Blo 1695548 1697487 := bstep (se 1 (by rfl) ⟨1273115, by rfl⟩ : syracuseStep 1697487 = 2546231) B2546231
theorem B34834171 : Blo 1695548 34834171 := bstep (se 1 (by rfl) ⟨26125628, by rfl⟩ : syracuseStep 34834171 = 52251257) B52251257
theorem B3819419 : Blo 1695548 3819419 := bstep (se 1 (by rfl) ⟨2864564, by rfl⟩ : syracuseStep 3819419 = 5729129) B5729129
theorem B16304291 : Blo 1695548 16304291 := bstep (se 1 (by rfl) ⟨12228218, by rfl⟩ : syracuseStep 16304291 = 24456437) B24456437
theorem B2861311 : Blo 1695548 2861311 := bstep (se 1 (by rfl) ⟨2145983, by rfl⟩ : syracuseStep 2861311 = 4291967) B4291967
theorem B19327247 : Blo 1695548 19327247 := bstep (se 1 (by rfl) ⟨14495435, by rfl⟩ : syracuseStep 19327247 = 28990871) B28990871
theorem B8153531 : Blo 1695548 8153531 := bstep (se 1 (by rfl) ⟨6115148, by rfl⟩ : syracuseStep 8153531 = 12230297) B12230297
theorem B5728751 : Blo 1695548 5728751 := bstep (se 1 (by rfl) ⟨4296563, by rfl⟩ : syracuseStep 5728751 = 8593127) B8593127
theorem B5966561 : Blo 1695548 5966561 := bstep (se 2 (by rfl) ⟨2237460, by rfl⟩ : syracuseStep 5966561 = 4474921) B4474921
theorem B34818817 : Blo 1695548 34818817 := bstep (se 2 (by rfl) ⟨13057056, by rfl⟩ : syracuseStep 34818817 = 26114113) B26114113
theorem B46451789 : Blo 1695548 46451789 := bstep (se 3 (by rfl) ⟨8709710, by rfl⟩ : syracuseStep 46451789 = 17419421) B17419421
theorem B313920659 : Blo 1695548 313920659 := bstep (se 1 (by rfl) ⟨235440494, by rfl⟩ : syracuseStep 313920659 = 470880989) B470880989
theorem B21752995 : Blo 1695548 21752995 := bstep (se 1 (by rfl) ⟨16314746, by rfl⟩ : syracuseStep 21752995 = 32629493) B32629493
theorem B2862695 : Blo 1695548 2862695 := bstep (se 1 (by rfl) ⟨2147021, by rfl⟩ : syracuseStep 2862695 = 4294043) B4294043
theorem B123866759 : Blo 1695548 123866759 := bstep (se 1 (by rfl) ⟨92900069, by rfl⟩ : syracuseStep 123866759 = 185800139) B185800139
theorem B24448715 : Blo 1695548 24448715 := bstep (se 1 (by rfl) ⟨18336536, by rfl⟩ : syracuseStep 24448715 = 36673073) B36673073
theorem B4829159 : Blo 1695548 4829159 := bstep (se 1 (by rfl) ⟨3621869, by rfl⟩ : syracuseStep 4829159 = 7243739) B7243739
theorem B12881915 : Blo 1695548 12881915 := bstep (se 1 (by rfl) ⟨9661436, by rfl⟩ : syracuseStep 12881915 = 19322873) B19322873
theorem B2543687 : Blo 1695548 2543687 := bstep (se 1 (by rfl) ⟨1907765, by rfl⟩ : syracuseStep 2543687 = 3815531) B3815531
theorem B2544335 : Blo 1695548 2544335 := bstep (se 1 (by rfl) ⟨1908251, by rfl⟩ : syracuseStep 2544335 = 3816503) B3816503
theorem B2544383 : Blo 1695548 2544383 := bstep (se 1 (by rfl) ⟨1908287, by rfl⟩ : syracuseStep 2544383 = 3816575) B3816575
theorem B6443783 : Blo 1695548 6443783 := bstep (se 1 (by rfl) ⟨4832837, by rfl⟩ : syracuseStep 6443783 = 9665675) B9665675
theorem B2545535 : Blo 1695548 2545535 := bstep (se 1 (by rfl) ⟨1909151, by rfl⟩ : syracuseStep 2545535 = 3818303) B3818303
theorem B2545631 : Blo 1695548 2545631 := bstep (se 1 (by rfl) ⟨1909223, by rfl⟩ : syracuseStep 2545631 = 3818447) B3818447
theorem B5158903 : Blo 1695548 5158903 := bstep (se 1 (by rfl) ⟨3869177, by rfl⟩ : syracuseStep 5158903 = 7738355) B7738355
theorem B18348383 : Blo 1695548 18348383 := bstep (se 1 (by rfl) ⟨13761287, by rfl⟩ : syracuseStep 18348383 = 27522575) B27522575
theorem B8591831 : Blo 1695548 8591831 := bstep (se 1 (by rfl) ⟨6443873, by rfl⟩ : syracuseStep 8591831 = 12887747) B12887747
theorem B13064939 : Blo 1695548 13064939 := bstep (se 1 (by rfl) ⟨9798704, by rfl⟩ : syracuseStep 13064939 = 19597409) B19597409
theorem B24460127 : Blo 1695548 24460127 := bstep (se 1 (by rfl) ⟨18345095, by rfl⟩ : syracuseStep 24460127 = 36690191) B36690191
theorem B3308411 : Blo 1695548 3308411 := bstep (se 1 (by rfl) ⟨2481308, by rfl⟩ : syracuseStep 3308411 = 4962617) B4962617
theorem B10312697 : Blo 1695548 10312697 := bstep (se 2 (by rfl) ⟨3867261, by rfl⟩ : syracuseStep 10312697 = 7734523) B7734523
theorem B23215385 : Blo 1695548 23215385 := bstep (se 2 (by rfl) ⟨8705769, by rfl⟩ : syracuseStep 23215385 = 17411539) B17411539
theorem B4832747 : Blo 1695548 4832747 := bstep (se 1 (by rfl) ⟨3624560, by rfl⟩ : syracuseStep 4832747 = 7249121) B7249121
theorem B21741209 : Blo 1695548 21741209 := bstep (se 2 (by rfl) ⟨8152953, by rfl⟩ : syracuseStep 21741209 = 16305907) B16305907
theorem B1695551 : Blo 1695548 1695551 := bstep (se 1 (by rfl) ⟨1271663, by rfl⟩ : syracuseStep 1695551 = 2543327) B2543327
theorem B5726159 : Blo 1695548 5726159 := bstep (se 1 (by rfl) ⟨4294619, by rfl⟩ : syracuseStep 5726159 = 8589239) B8589239
theorem B4292635 : Blo 1695548 4292635 := bstep (se 1 (by rfl) ⟨3219476, by rfl⟩ : syracuseStep 4292635 = 6438953) B6438953
theorem B1695791 : Blo 1695548 1695791 := bstep (se 1 (by rfl) ⟨1271843, by rfl⟩ : syracuseStep 1695791 = 2543687) B2543687
theorem B8585513 : Blo 1695548 8585513 := bstep (se 2 (by rfl) ⟨3219567, by rfl⟩ : syracuseStep 8585513 = 6439135) B6439135
theorem B1696223 : Blo 1695548 1696223 := bstep (se 1 (by rfl) ⟨1272167, by rfl⟩ : syracuseStep 1696223 = 2544335) B2544335
theorem B1696255 : Blo 1695548 1696255 := bstep (se 1 (by rfl) ⟨1272191, by rfl⟩ : syracuseStep 1696255 = 2544383) B2544383
theorem B46425089 : Blo 1695548 46425089 := bstep (se 2 (by rfl) ⟨17409408, by rfl⟩ : syracuseStep 46425089 = 34818817) B34818817
theorem B2753705 : Blo 1695548 2753705 := bstep (se 2 (by rfl) ⟨1032639, by rfl⟩ : syracuseStep 2753705 = 2065279) B2065279
theorem B1697023 : Blo 1695548 1697023 := bstep (se 1 (by rfl) ⟨1272767, by rfl⟩ : syracuseStep 1697023 = 2545535) B2545535
theorem B1697087 : Blo 1695548 1697087 := bstep (se 1 (by rfl) ⟨1272815, by rfl⟩ : syracuseStep 1697087 = 2545631) B2545631
theorem B5727887 : Blo 1695548 5727887 := bstep (se 1 (by rfl) ⟨4295915, by rfl⟩ : syracuseStep 5727887 = 8591831) B8591831
theorem B3819167 : Blo 1695548 3819167 := bstep (se 1 (by rfl) ⟨2864375, by rfl⟩ : syracuseStep 3819167 = 5728751) B5728751
theorem B8709959 : Blo 1695548 8709959 := bstep (se 1 (by rfl) ⟨6532469, by rfl⟩ : syracuseStep 8709959 = 13064939) B13064939
theorem B2205607 : Blo 1695548 2205607 := bstep (se 1 (by rfl) ⟨1654205, by rfl⟩ : syracuseStep 2205607 = 3308411) B3308411
theorem B6875131 : Blo 1695548 6875131 := bstep (se 1 (by rfl) ⟨5156348, by rfl⟩ : syracuseStep 6875131 = 10312697) B10312697
theorem B30967859 : Blo 1695548 30967859 := bstep (se 1 (by rfl) ⟨23225894, by rfl⟩ : syracuseStep 30967859 = 46451789) B46451789
theorem B15476923 : Blo 1695548 15476923 := bstep (se 1 (by rfl) ⟨11607692, by rfl⟩ : syracuseStep 15476923 = 23215385) B23215385
theorem B3221831 : Blo 1695548 3221831 := bstep (se 1 (by rfl) ⟨2416373, by rfl⟩ : syracuseStep 3221831 = 4832747) B4832747
theorem B82577839 : Blo 1695548 82577839 := bstep (se 1 (by rfl) ⟨61933379, by rfl⟩ : syracuseStep 82577839 = 123866759) B123866759
theorem B14494139 : Blo 1695548 14494139 := bstep (se 1 (by rfl) ⟨10870604, by rfl⟩ : syracuseStep 14494139 = 21741209) B21741209
theorem B14486141 : Blo 1695548 14486141 := bstep (se 3 (by rfl) ⟨2716151, by rfl⟩ : syracuseStep 14486141 = 5432303) B5432303
theorem B8587943 : Blo 1695548 8587943 := bstep (se 1 (by rfl) ⟨6440957, by rfl⟩ : syracuseStep 8587943 = 12881915) B12881915
theorem B4352879 : Blo 1695548 4352879 := bstep (se 1 (by rfl) ⟨3264659, by rfl⟩ : syracuseStep 4352879 = 6529319) B6529319
theorem B4295855 : Blo 1695548 4295855 := bstep (se 1 (by rfl) ⟨3221891, by rfl⟩ : syracuseStep 4295855 = 6443783) B6443783
theorem B12233987 : Blo 1695548 12233987 := bstep (se 1 (by rfl) ⟨9175490, by rfl⟩ : syracuseStep 12233987 = 18350981) B18350981
theorem B29003993 : Blo 1695548 29003993 := bstep (se 2 (by rfl) ⟨10876497, by rfl⟩ : syracuseStep 29003993 = 21752995) B21752995
theorem B5435687 : Blo 1695548 5435687 := bstep (se 1 (by rfl) ⟨4076765, by rfl⟩ : syracuseStep 5435687 = 8153531) B8153531
theorem B3977707 : Blo 1695548 3977707 := bstep (se 1 (by rfl) ⟨2983280, by rfl⟩ : syracuseStep 3977707 = 5966561) B5966561
theorem B16306751 : Blo 1695548 16306751 := bstep (se 1 (by rfl) ⟨12230063, by rfl⟩ : syracuseStep 16306751 = 24460127) B24460127
theorem B2863721 : Blo 1695548 2863721 := bstep (se 2 (by rfl) ⟨1073895, by rfl⟩ : syracuseStep 2863721 = 2147791) B2147791
theorem B46445561 : Blo 1695548 46445561 := bstep (se 2 (by rfl) ⟨17417085, by rfl⟩ : syracuseStep 46445561 = 34834171) B34834171
theorem B16299143 : Blo 1695548 16299143 := bstep (se 1 (by rfl) ⟨12224357, by rfl⟩ : syracuseStep 16299143 = 24448715) B24448715
theorem B6878537 : Blo 1695548 6878537 := bstep (se 2 (by rfl) ⟨2579451, by rfl⟩ : syracuseStep 6878537 = 5158903) B5158903
theorem B2545199 : Blo 1695548 2545199 := bstep (se 1 (by rfl) ⟨1908899, by rfl⟩ : syracuseStep 2545199 = 3817799) B3817799
theorem B3815081 : Blo 1695548 3815081 := bstep (se 2 (by rfl) ⟨1430655, by rfl⟩ : syracuseStep 3815081 = 2861311) B2861311
theorem B5723891 : Blo 1695548 5723891 := bstep (se 1 (by rfl) ⟨4292918, by rfl⟩ : syracuseStep 5723891 = 8585837) B8585837
theorem B7247839 : Blo 1695548 7247839 := bstep (se 1 (by rfl) ⟨5435879, by rfl⟩ : syracuseStep 7247839 = 10871759) B10871759
theorem B5724215 : Blo 1695548 5724215 := bstep (se 1 (by rfl) ⟨4293161, by rfl⟩ : syracuseStep 5724215 = 8586323) B8586323
theorem B48929021 : Blo 1695548 48929021 := bstep (se 3 (by rfl) ⟨9174191, by rfl⟩ : syracuseStep 48929021 = 18348383) B18348383
theorem B2546057 : Blo 1695548 2546057 := bstep (se 2 (by rfl) ⟨954771, by rfl⟩ : syracuseStep 2546057 = 1909543) B1909543
theorem B2546279 : Blo 1695548 2546279 := bstep (se 1 (by rfl) ⟨1909709, by rfl⟩ : syracuseStep 2546279 = 3819419) B3819419
theorem B10869527 : Blo 1695548 10869527 := bstep (se 1 (by rfl) ⟨8152145, by rfl⟩ : syracuseStep 10869527 = 16304291) B16304291
theorem B12884831 : Blo 1695548 12884831 := bstep (se 1 (by rfl) ⟨9663623, by rfl⟩ : syracuseStep 12884831 = 19327247) B19327247
theorem B209280439 : Blo 1695548 209280439 := bstep (se 1 (by rfl) ⟨156960329, by rfl⟩ : syracuseStep 209280439 = 313920659) B313920659
theorem B1908463 : Blo 1695548 1908463 := bstep (se 1 (by rfl) ⟨1431347, by rfl⟩ : syracuseStep 1908463 = 2862695) B2862695
theorem B3817439 : Blo 1695548 3817439 := bstep (se 1 (by rfl) ⟨2863079, by rfl⟩ : syracuseStep 3817439 = 5726159) B5726159
theorem B3219439 : Blo 1695548 3219439 := bstep (se 1 (by rfl) ⟨2414579, by rfl⟩ : syracuseStep 3219439 = 4829159) B4829159
theorem B20635897 : Blo 1695548 20635897 := bstep (se 2 (by rfl) ⟨7738461, by rfl⟩ : syracuseStep 20635897 = 15476923) B15476923
theorem B10871167 : Blo 1695548 10871167 := bstep (se 1 (by rfl) ⟨8153375, by rfl⟩ : syracuseStep 10871167 = 16306751) B16306751
theorem B1909147 : Blo 1695548 1909147 := bstep (se 1 (by rfl) ⟨1431860, by rfl⟩ : syracuseStep 1909147 = 2863721) B2863721
theorem B30950059 : Blo 1695548 30950059 := bstep (se 1 (by rfl) ⟨23212544, by rfl⟩ : syracuseStep 30950059 = 46425089) B46425089
theorem B1835803 : Blo 1695548 1835803 := bstep (se 1 (by rfl) ⟨1376852, by rfl⟩ : syracuseStep 1835803 = 2753705) B2753705
theorem B1696799 : Blo 1695548 1696799 := bstep (se 1 (by rfl) ⟨1272599, by rfl⟩ : syracuseStep 1696799 = 2545199) B2545199
theorem B3818591 : Blo 1695548 3818591 := bstep (se 1 (by rfl) ⟨2863943, by rfl⟩ : syracuseStep 3818591 = 5727887) B5727887
theorem B20645239 : Blo 1695548 20645239 := bstep (se 1 (by rfl) ⟨15483929, by rfl⟩ : syracuseStep 20645239 = 30967859) B30967859
theorem B2147887 : Blo 1695548 2147887 := bstep (se 1 (by rfl) ⟨1610915, by rfl⟩ : syracuseStep 2147887 = 3221831) B3221831
theorem B1697371 : Blo 1695548 1697371 := bstep (se 1 (by rfl) ⟨1273028, by rfl⟩ : syracuseStep 1697371 = 2546057) B2546057
theorem B1697519 : Blo 1695548 1697519 := bstep (se 1 (by rfl) ⟨1273139, by rfl⟩ : syracuseStep 1697519 = 2546279) B2546279
theorem B2901919 : Blo 1695548 2901919 := bstep (se 1 (by rfl) ⟨2176439, by rfl⟩ : syracuseStep 2901919 = 4352879) B4352879
theorem B19335995 : Blo 1695548 19335995 := bstep (se 1 (by rfl) ⟨14501996, by rfl⟩ : syracuseStep 19335995 = 29003993) B29003993
theorem B3623791 : Blo 1695548 3623791 := bstep (se 1 (by rfl) ⟨2717843, by rfl⟩ : syracuseStep 3623791 = 5435687) B5435687
theorem B110103785 : Blo 1695548 110103785 := bstep (se 2 (by rfl) ⟨41288919, by rfl⟩ : syracuseStep 110103785 = 82577839) B82577839
theorem B5303609 : Blo 1695548 5303609 := bstep (se 2 (by rfl) ⟨1988853, by rfl⟩ : syracuseStep 5303609 = 3977707) B3977707
theorem B10866095 : Blo 1695548 10866095 := bstep (se 1 (by rfl) ⟨8149571, by rfl⟩ : syracuseStep 10866095 = 16299143) B16299143
theorem B2543387 : Blo 1695548 2543387 := bstep (se 1 (by rfl) ⟨1907540, by rfl⟩ : syracuseStep 2543387 = 3815081) B3815081
theorem B9662759 : Blo 1695548 9662759 := bstep (se 1 (by rfl) ⟨7247069, by rfl⟩ : syracuseStep 9662759 = 14494139) B14494139
theorem B7246351 : Blo 1695548 7246351 := bstep (se 1 (by rfl) ⟨5434763, by rfl⟩ : syracuseStep 7246351 = 10869527) B10869527
theorem B8589887 : Blo 1695548 8589887 := bstep (se 1 (by rfl) ⟨6442415, by rfl⟩ : syracuseStep 8589887 = 12884831) B12884831
theorem B279040585 : Blo 1695548 279040585 := bstep (se 2 (by rfl) ⟨104640219, by rfl⟩ : syracuseStep 279040585 = 209280439) B209280439
theorem B2863903 : Blo 1695548 2863903 := bstep (se 1 (by rfl) ⟨2147927, by rfl⟩ : syracuseStep 2863903 = 4295855) B4295855
theorem B8155991 : Blo 1695548 8155991 := bstep (se 1 (by rfl) ⟨6116993, by rfl⟩ : syracuseStep 8155991 = 12233987) B12233987
theorem B2544617 : Blo 1695548 2544617 := bstep (se 2 (by rfl) ⟨954231, by rfl⟩ : syracuseStep 2544617 = 1908463) B1908463
theorem B9663785 : Blo 1695548 9663785 := bstep (se 2 (by rfl) ⟨3623919, by rfl⟩ : syracuseStep 9663785 = 7247839) B7247839
theorem B2544959 : Blo 1695548 2544959 := bstep (se 1 (by rfl) ⟨1908719, by rfl⟩ : syracuseStep 2544959 = 3817439) B3817439
theorem B5723513 : Blo 1695548 5723513 := bstep (se 2 (by rfl) ⟨2146317, by rfl⟩ : syracuseStep 5723513 = 4292635) B4292635
theorem B5723675 : Blo 1695548 5723675 := bstep (se 1 (by rfl) ⟨4292756, by rfl⟩ : syracuseStep 5723675 = 8585513) B8585513
theorem B30963707 : Blo 1695548 30963707 := bstep (se 1 (by rfl) ⟨23222780, by rfl⟩ : syracuseStep 30963707 = 46445561) B46445561
theorem B4585691 : Blo 1695548 4585691 := bstep (se 1 (by rfl) ⟨3439268, by rfl⟩ : syracuseStep 4585691 = 6878537) B6878537
theorem B2546111 : Blo 1695548 2546111 := bstep (se 1 (by rfl) ⟨1909583, by rfl⟩ : syracuseStep 2546111 = 3819167) B3819167
theorem B3815927 : Blo 1695548 3815927 := bstep (se 1 (by rfl) ⟨2861945, by rfl⟩ : syracuseStep 3815927 = 5723891) B5723891
theorem B5806639 : Blo 1695548 5806639 := bstep (se 1 (by rfl) ⟨4354979, by rfl⟩ : syracuseStep 5806639 = 8709959) B8709959
theorem B3816143 : Blo 1695548 3816143 := bstep (se 1 (by rfl) ⟨2862107, by rfl⟩ : syracuseStep 3816143 = 5724215) B5724215
theorem B32619347 : Blo 1695548 32619347 := bstep (se 1 (by rfl) ⟨24464510, by rfl⟩ : syracuseStep 32619347 = 48929021) B48929021
theorem B9657427 : Blo 1695548 9657427 := bstep (se 1 (by rfl) ⟨7243070, by rfl⟩ : syracuseStep 9657427 = 14486141) B14486141
theorem B5725295 : Blo 1695548 5725295 := bstep (se 1 (by rfl) ⟨4293971, by rfl⟩ : syracuseStep 5725295 = 8587943) B8587943
theorem B2940809 : Blo 1695548 2940809 := bstep (se 2 (by rfl) ⟨1102803, by rfl⟩ : syracuseStep 2940809 = 2205607) B2205607
theorem B4292585 : Blo 1695548 4292585 := bstep (se 2 (by rfl) ⟨1609719, by rfl⟩ : syracuseStep 4292585 = 3219439) B3219439
theorem B9166841 : Blo 1695548 9166841 := bstep (se 2 (by rfl) ⟨3437565, by rfl⟩ : syracuseStep 9166841 = 6875131) B6875131
theorem B5726591 : Blo 1695548 5726591 := bstep (se 1 (by rfl) ⟨4294943, by rfl⟩ : syracuseStep 5726591 = 8589887) B8589887
theorem B1696411 : Blo 1695548 1696411 := bstep (se 1 (by rfl) ⟨1272308, by rfl⟩ : syracuseStep 1696411 = 2544617) B2544617
theorem B7742185 : Blo 1695548 7742185 := bstep (se 2 (by rfl) ⟨2903319, by rfl⟩ : syracuseStep 7742185 = 5806639) B5806639
theorem B1696639 : Blo 1695548 1696639 := bstep (se 1 (by rfl) ⟨1272479, by rfl⟩ : syracuseStep 1696639 = 2544959) B2544959
theorem B3818537 : Blo 1695548 3818537 := bstep (se 2 (by rfl) ⟨1431951, by rfl⟩ : syracuseStep 3818537 = 2863903) B2863903
theorem B31368629 : Blo 1695548 31368629 := bstep (se 5 (by rfl) ⟨1470404, by rfl⟩ : syracuseStep 31368629 = 2940809) B2940809
theorem B9790949 : Blo 1695548 9790949 := bstep (se 4 (by rfl) ⟨917901, by rfl⟩ : syracuseStep 9790949 = 1835803) B1835803
theorem B1697407 : Blo 1695548 1697407 := bstep (se 1 (by rfl) ⟨1273055, by rfl⟩ : syracuseStep 1697407 = 2546111) B2546111
theorem B27526985 : Blo 1695548 27526985 := bstep (se 2 (by rfl) ⟨10322619, by rfl⟩ : syracuseStep 27526985 = 20645239) B20645239
theorem B73402523 : Blo 1695548 73402523 := bstep (se 1 (by rfl) ⟨55051892, by rfl⟩ : syracuseStep 73402523 = 110103785) B110103785
theorem B7244063 : Blo 1695548 7244063 := bstep (se 1 (by rfl) ⟨5433047, by rfl⟩ : syracuseStep 7244063 = 10866095) B10866095
theorem B3869225 : Blo 1695548 3869225 := bstep (se 2 (by rfl) ⟨1450959, by rfl⟩ : syracuseStep 3869225 = 2901919) B2901919
theorem B2861723 : Blo 1695548 2861723 := bstep (se 1 (by rfl) ⟨2146292, by rfl⟩ : syracuseStep 2861723 = 4292585) B4292585
theorem B6441839 : Blo 1695548 6441839 := bstep (se 1 (by rfl) ⟨4831379, by rfl⟩ : syracuseStep 6441839 = 9662759) B9662759
theorem B14494889 : Blo 1695548 14494889 := bstep (se 2 (by rfl) ⟨5435583, by rfl⟩ : syracuseStep 14494889 = 10871167) B10871167
theorem B9661801 : Blo 1695548 9661801 := bstep (se 2 (by rfl) ⟨3623175, by rfl⟩ : syracuseStep 9661801 = 7246351) B7246351
theorem B6442523 : Blo 1695548 6442523 := bstep (se 1 (by rfl) ⟨4831892, by rfl⟩ : syracuseStep 6442523 = 9663785) B9663785
theorem B41266745 : Blo 1695548 41266745 := bstep (se 2 (by rfl) ⟨15475029, by rfl⟩ : syracuseStep 41266745 = 30950059) B30950059
theorem B2543951 : Blo 1695548 2543951 := bstep (se 1 (by rfl) ⟨1907963, by rfl⟩ : syracuseStep 2543951 = 3815927) B3815927
theorem B2544095 : Blo 1695548 2544095 := bstep (se 1 (by rfl) ⟨1908071, by rfl⟩ : syracuseStep 2544095 = 3816143) B3816143
theorem B12890663 : Blo 1695548 12890663 := bstep (se 1 (by rfl) ⟨9667997, by rfl⟩ : syracuseStep 12890663 = 19335995) B19335995
theorem B21746231 : Blo 1695548 21746231 := bstep (se 1 (by rfl) ⟨16309673, by rfl⟩ : syracuseStep 21746231 = 32619347) B32619347
theorem B2863849 : Blo 1695548 2863849 := bstep (se 2 (by rfl) ⟨1073943, by rfl⟩ : syracuseStep 2863849 = 2147887) B2147887
theorem B3535739 : Blo 1695548 3535739 := bstep (se 1 (by rfl) ⟨2651804, by rfl⟩ : syracuseStep 3535739 = 5303609) B5303609
theorem B27514529 : Blo 1695548 27514529 := bstep (se 2 (by rfl) ⟨10317948, by rfl⟩ : syracuseStep 27514529 = 20635897) B20635897
theorem B2545529 : Blo 1695548 2545529 := bstep (se 2 (by rfl) ⟨954573, by rfl⟩ : syracuseStep 2545529 = 1909147) B1909147
theorem B5437327 : Blo 1695548 5437327 := bstep (se 1 (by rfl) ⟨4077995, by rfl⟩ : syracuseStep 5437327 = 8155991) B8155991
theorem B12228509 : Blo 1695548 12228509 := bstep (se 3 (by rfl) ⟨2292845, by rfl⟩ : syracuseStep 12228509 = 4585691) B4585691
theorem B2545727 : Blo 1695548 2545727 := bstep (se 1 (by rfl) ⟨1909295, by rfl⟩ : syracuseStep 2545727 = 3818591) B3818591
theorem B372054113 : Blo 1695548 372054113 := bstep (se 2 (by rfl) ⟨139520292, by rfl⟩ : syracuseStep 372054113 = 279040585) B279040585
theorem B3815675 : Blo 1695548 3815675 := bstep (se 1 (by rfl) ⟨2861756, by rfl⟩ : syracuseStep 3815675 = 5723513) B5723513
theorem B3815783 : Blo 1695548 3815783 := bstep (se 1 (by rfl) ⟨2861837, by rfl⟩ : syracuseStep 3815783 = 5723675) B5723675
theorem B4831721 : Blo 1695548 4831721 := bstep (se 2 (by rfl) ⟨1811895, by rfl⟩ : syracuseStep 4831721 = 3623791) B3623791
theorem B20642471 : Blo 1695548 20642471 := bstep (se 1 (by rfl) ⟨15481853, by rfl⟩ : syracuseStep 20642471 = 30963707) B30963707
theorem B12876569 : Blo 1695548 12876569 := bstep (se 2 (by rfl) ⟨4828713, by rfl⟩ : syracuseStep 12876569 = 9657427) B9657427
theorem B3816863 : Blo 1695548 3816863 := bstep (se 1 (by rfl) ⟨2862647, by rfl⟩ : syracuseStep 3816863 = 5725295) B5725295
theorem B1695591 : Blo 1695548 1695591 := bstep (se 1 (by rfl) ⟨1271693, by rfl⟩ : syracuseStep 1695591 = 2543387) B2543387
theorem B6111227 : Blo 1695548 6111227 := bstep (se 1 (by rfl) ⟨4583420, by rfl⟩ : syracuseStep 6111227 = 9166841) B9166841
theorem B1695967 : Blo 1695548 1695967 := bstep (se 1 (by rfl) ⟨1271975, by rfl⟩ : syracuseStep 1695967 = 2543951) B2543951
theorem B3817727 : Blo 1695548 3817727 := bstep (se 1 (by rfl) ⟨2863295, by rfl⟩ : syracuseStep 3817727 = 5726591) B5726591
theorem B1696063 : Blo 1695548 1696063 := bstep (se 1 (by rfl) ⟨1272047, by rfl⟩ : syracuseStep 1696063 = 2544095) B2544095
theorem B8593775 : Blo 1695548 8593775 := bstep (se 1 (by rfl) ⟨6445331, by rfl⟩ : syracuseStep 8593775 = 12890663) B12890663
theorem B3818465 : Blo 1695548 3818465 := bstep (se 2 (by rfl) ⟨1431924, by rfl⟩ : syracuseStep 3818465 = 2863849) B2863849
theorem B18343019 : Blo 1695548 18343019 := bstep (se 1 (by rfl) ⟨13757264, by rfl⟩ : syracuseStep 18343019 = 27514529) B27514529
theorem B18351323 : Blo 1695548 18351323 := bstep (se 1 (by rfl) ⟨13763492, by rfl⟩ : syracuseStep 18351323 = 27526985) B27526985
theorem B1697019 : Blo 1695548 1697019 := bstep (se 1 (by rfl) ⟨1272764, by rfl⟩ : syracuseStep 1697019 = 2545529) B2545529
theorem B8152339 : Blo 1695548 8152339 := bstep (se 1 (by rfl) ⟨6114254, by rfl⟩ : syracuseStep 8152339 = 12228509) B12228509
theorem B1697151 : Blo 1695548 1697151 := bstep (se 1 (by rfl) ⟨1272863, by rfl⟩ : syracuseStep 1697151 = 2545727) B2545727
theorem B3221147 : Blo 1695548 3221147 := bstep (se 1 (by rfl) ⟨2415860, by rfl⟩ : syracuseStep 3221147 = 4831721) B4831721
theorem B4294559 : Blo 1695548 4294559 := bstep (se 1 (by rfl) ⟨3220919, by rfl⟩ : syracuseStep 4294559 = 6441839) B6441839
theorem B4295015 : Blo 1695548 4295015 := bstep (se 1 (by rfl) ⟨3221261, by rfl⟩ : syracuseStep 4295015 = 6442523) B6442523
theorem B27511163 : Blo 1695548 27511163 := bstep (se 1 (by rfl) ⟨20633372, by rfl⟩ : syracuseStep 27511163 = 41266745) B41266745
theorem B4074151 : Blo 1695548 4074151 := bstep (se 1 (by rfl) ⟨3055613, by rfl⟩ : syracuseStep 4074151 = 6111227) B6111227
theorem B41291653 : Blo 1695548 41291653 := bstep (se 4 (by rfl) ⟨3871092, by rfl⟩ : syracuseStep 41291653 = 7742185) B7742185
theorem B48935015 : Blo 1695548 48935015 := bstep (se 1 (by rfl) ⟨36701261, by rfl⟩ : syracuseStep 48935015 = 73402523) B73402523
theorem B2543783 : Blo 1695548 2543783 := bstep (se 1 (by rfl) ⟨1907837, by rfl⟩ : syracuseStep 2543783 = 3815675) B3815675
theorem B4829375 : Blo 1695548 4829375 := bstep (se 1 (by rfl) ⟨3622031, by rfl⟩ : syracuseStep 4829375 = 7244063) B7244063
theorem B2543855 : Blo 1695548 2543855 := bstep (se 1 (by rfl) ⟨1907891, by rfl⟩ : syracuseStep 2543855 = 3815783) B3815783
theorem B12882401 : Blo 1695548 12882401 := bstep (se 2 (by rfl) ⟨4830900, by rfl⟩ : syracuseStep 12882401 = 9661801) B9661801
theorem B9663259 : Blo 1695548 9663259 := bstep (se 1 (by rfl) ⟨7247444, by rfl⟩ : syracuseStep 9663259 = 14494889) B14494889
theorem B2544575 : Blo 1695548 2544575 := bstep (se 1 (by rfl) ⟨1908431, by rfl⟩ : syracuseStep 2544575 = 3816863) B3816863
theorem B14497487 : Blo 1695548 14497487 := bstep (se 1 (by rfl) ⟨10873115, by rfl⟩ : syracuseStep 14497487 = 21746231) B21746231
theorem B2357159 : Blo 1695548 2357159 := bstep (se 1 (by rfl) ⟨1767869, by rfl⟩ : syracuseStep 2357159 = 3535739) B3535739
theorem B2545691 : Blo 1695548 2545691 := bstep (se 1 (by rfl) ⟨1909268, by rfl⟩ : syracuseStep 2545691 = 3818537) B3818537
theorem B20912419 : Blo 1695548 20912419 := bstep (se 1 (by rfl) ⟨15684314, by rfl⟩ : syracuseStep 20912419 = 31368629) B31368629
theorem B6527299 : Blo 1695548 6527299 := bstep (se 1 (by rfl) ⟨4895474, by rfl⟩ : syracuseStep 6527299 = 9790949) B9790949
theorem B248036075 : Blo 1695548 248036075 := bstep (se 1 (by rfl) ⟨186027056, by rfl⟩ : syracuseStep 248036075 = 372054113) B372054113
theorem B2579483 : Blo 1695548 2579483 := bstep (se 1 (by rfl) ⟨1934612, by rfl⟩ : syracuseStep 2579483 = 3869225) B3869225
theorem B1907815 : Blo 1695548 1907815 := bstep (se 1 (by rfl) ⟨1430861, by rfl⟩ : syracuseStep 1907815 = 2861723) B2861723
theorem B13761647 : Blo 1695548 13761647 := bstep (se 1 (by rfl) ⟨10321235, by rfl⟩ : syracuseStep 13761647 = 20642471) B20642471
theorem B8584379 : Blo 1695548 8584379 := bstep (se 1 (by rfl) ⟨6438284, by rfl⟩ : syracuseStep 8584379 = 12876569) B12876569
theorem B7249769 : Blo 1695548 7249769 := bstep (se 2 (by rfl) ⟨2718663, by rfl⟩ : syracuseStep 7249769 = 5437327) B5437327
theorem B1695855 : Blo 1695548 1695855 := bstep (se 1 (by rfl) ⟨1271891, by rfl⟩ : syracuseStep 1695855 = 2543783) B2543783
theorem B3219583 : Blo 1695548 3219583 := bstep (se 1 (by rfl) ⟨2414687, by rfl⟩ : syracuseStep 3219583 = 4829375) B4829375
theorem B1695903 : Blo 1695548 1695903 := bstep (se 1 (by rfl) ⟨1271927, by rfl⟩ : syracuseStep 1695903 = 2543855) B2543855
theorem B1696383 : Blo 1695548 1696383 := bstep (se 1 (by rfl) ⟨1272287, by rfl⟩ : syracuseStep 1696383 = 2544575) B2544575
theorem B5432201 : Blo 1695548 5432201 := bstep (se 2 (by rfl) ⟨2037075, by rfl⟩ : syracuseStep 5432201 = 4074151) B4074151
theorem B1697127 : Blo 1695548 1697127 := bstep (se 1 (by rfl) ⟨1272845, by rfl⟩ : syracuseStep 1697127 = 2545691) B2545691
theorem B165357383 : Blo 1695548 165357383 := bstep (se 1 (by rfl) ⟨124018037, by rfl⟩ : syracuseStep 165357383 = 248036075) B248036075
theorem B6285757 : Blo 1695548 6285757 := bstep (se 3 (by rfl) ⟨1178579, by rfl⟩ : syracuseStep 6285757 = 2357159) B2357159
theorem B32623343 : Blo 1695548 32623343 := bstep (se 1 (by rfl) ⟨24467507, by rfl⟩ : syracuseStep 32623343 = 48935015) B48935015
theorem B5729183 : Blo 1695548 5729183 := bstep (se 1 (by rfl) ⟨4296887, by rfl⟩ : syracuseStep 5729183 = 8593775) B8593775
theorem B8588267 : Blo 1695548 8588267 := bstep (se 1 (by rfl) ⟨6441200, by rfl⟩ : syracuseStep 8588267 = 12882401) B12882401
theorem B8703065 : Blo 1695548 8703065 := bstep (se 2 (by rfl) ⟨3263649, by rfl⟩ : syracuseStep 8703065 = 6527299) B6527299
theorem B12234215 : Blo 1695548 12234215 := bstep (se 1 (by rfl) ⟨9175661, by rfl⟩ : syracuseStep 12234215 = 18351323) B18351323
theorem B2863039 : Blo 1695548 2863039 := bstep (se 1 (by rfl) ⟨2147279, by rfl⟩ : syracuseStep 2863039 = 4294559) B4294559
theorem B2543753 : Blo 1695548 2543753 := bstep (se 2 (by rfl) ⟨953907, by rfl⟩ : syracuseStep 2543753 = 1907815) B1907815
theorem B2863343 : Blo 1695548 2863343 := bstep (se 1 (by rfl) ⟨2147507, by rfl⟩ : syracuseStep 2863343 = 4295015) B4295015
theorem B8589725 : Blo 1695548 8589725 := bstep (se 3 (by rfl) ⟨1610573, by rfl⟩ : syracuseStep 8589725 = 3221147) B3221147
theorem B5722919 : Blo 1695548 5722919 := bstep (se 1 (by rfl) ⟨4292189, by rfl⟩ : syracuseStep 5722919 = 8584379) B8584379
theorem B55055537 : Blo 1695548 55055537 := bstep (se 2 (by rfl) ⟨20645826, by rfl⟩ : syracuseStep 55055537 = 41291653) B41291653
theorem B6878621 : Blo 1695548 6878621 := bstep (se 3 (by rfl) ⟨1289741, by rfl⟩ : syracuseStep 6878621 = 2579483) B2579483
theorem B2545151 : Blo 1695548 2545151 := bstep (se 1 (by rfl) ⟨1908863, by rfl⟩ : syracuseStep 2545151 = 3817727) B3817727
theorem B27883225 : Blo 1695548 27883225 := bstep (se 2 (by rfl) ⟨10456209, by rfl⟩ : syracuseStep 27883225 = 20912419) B20912419
theorem B2545643 : Blo 1695548 2545643 := bstep (se 1 (by rfl) ⟨1909232, by rfl⟩ : syracuseStep 2545643 = 3818465) B3818465
theorem B12228679 : Blo 1695548 12228679 := bstep (se 1 (by rfl) ⟨9171509, by rfl⟩ : syracuseStep 12228679 = 18343019) B18343019
theorem B12884345 : Blo 1695548 12884345 := bstep (se 2 (by rfl) ⟨4831629, by rfl⟩ : syracuseStep 12884345 = 9663259) B9663259
theorem B9664991 : Blo 1695548 9664991 := bstep (se 1 (by rfl) ⟨7248743, by rfl⟩ : syracuseStep 9664991 = 14497487) B14497487
theorem B18340775 : Blo 1695548 18340775 := bstep (se 1 (by rfl) ⟨13755581, by rfl⟩ : syracuseStep 18340775 = 27511163) B27511163
theorem B10869785 : Blo 1695548 10869785 := bstep (se 2 (by rfl) ⟨4076169, by rfl⟩ : syracuseStep 10869785 = 8152339) B8152339
theorem B9174431 : Blo 1695548 9174431 := bstep (se 1 (by rfl) ⟨6880823, by rfl⟩ : syracuseStep 9174431 = 13761647) B13761647
theorem B4833179 : Blo 1695548 4833179 := bstep (se 1 (by rfl) ⟨3624884, by rfl⟩ : syracuseStep 4833179 = 7249769) B7249769
theorem B1695835 : Blo 1695548 1695835 := bstep (se 1 (by rfl) ⟨1271876, by rfl⟩ : syracuseStep 1695835 = 2543753) B2543753
theorem B1908895 : Blo 1695548 1908895 := bstep (se 1 (by rfl) ⟨1431671, by rfl⟩ : syracuseStep 1908895 = 2863343) B2863343
theorem B4292777 : Blo 1695548 4292777 := bstep (se 2 (by rfl) ⟨1609791, by rfl⟩ : syracuseStep 4292777 = 3219583) B3219583
theorem B5726483 : Blo 1695548 5726483 := bstep (se 1 (by rfl) ⟨4294862, by rfl⟩ : syracuseStep 5726483 = 8589725) B8589725
theorem B8381009 : Blo 1695548 8381009 := bstep (se 2 (by rfl) ⟨3142878, by rfl⟩ : syracuseStep 8381009 = 6285757) B6285757
theorem B3621467 : Blo 1695548 3621467 := bstep (se 1 (by rfl) ⟨2716100, by rfl⟩ : syracuseStep 3621467 = 5432201) B5432201
theorem B1696767 : Blo 1695548 1696767 := bstep (se 1 (by rfl) ⟨1272575, by rfl⟩ : syracuseStep 1696767 = 2545151) B2545151
theorem B1697095 : Blo 1695548 1697095 := bstep (se 1 (by rfl) ⟨1272821, by rfl⟩ : syracuseStep 1697095 = 2545643) B2545643
theorem B3819455 : Blo 1695548 3819455 := bstep (se 1 (by rfl) ⟨2864591, by rfl⟩ : syracuseStep 3819455 = 5729183) B5729183
theorem B5802043 : Blo 1695548 5802043 := bstep (se 1 (by rfl) ⟨4351532, by rfl⟩ : syracuseStep 5802043 = 8703065) B8703065
theorem B440953021 : Blo 1695548 440953021 := bstep (se 3 (by rfl) ⟨82678691, by rfl⟩ : syracuseStep 440953021 = 165357383) B165357383
theorem B37177633 : Blo 1695548 37177633 := bstep (se 2 (by rfl) ⟨13941612, by rfl⟩ : syracuseStep 37177633 = 27883225) B27883225
theorem B3222119 : Blo 1695548 3222119 := bstep (se 1 (by rfl) ⟨2416589, by rfl⟩ : syracuseStep 3222119 = 4833179) B4833179
theorem B16304905 : Blo 1695548 16304905 := bstep (se 2 (by rfl) ⟨6114339, by rfl⟩ : syracuseStep 16304905 = 12228679) B12228679
theorem B36703691 : Blo 1695548 36703691 := bstep (se 1 (by rfl) ⟨27527768, by rfl⟩ : syracuseStep 36703691 = 55055537) B55055537
theorem B24465149 : Blo 1695548 24465149 := bstep (se 3 (by rfl) ⟨4587215, by rfl⟩ : syracuseStep 24465149 = 9174431) B9174431
theorem B8589563 : Blo 1695548 8589563 := bstep (se 1 (by rfl) ⟨6442172, by rfl⟩ : syracuseStep 8589563 = 12884345) B12884345
theorem B6443327 : Blo 1695548 6443327 := bstep (se 1 (by rfl) ⟨4832495, by rfl⟩ : syracuseStep 6443327 = 9664991) B9664991
theorem B12227183 : Blo 1695548 12227183 := bstep (se 1 (by rfl) ⟨9170387, by rfl⟩ : syracuseStep 12227183 = 18340775) B18340775
theorem B7246523 : Blo 1695548 7246523 := bstep (se 1 (by rfl) ⟨5434892, by rfl⟩ : syracuseStep 7246523 = 10869785) B10869785
theorem B8156143 : Blo 1695548 8156143 := bstep (se 1 (by rfl) ⟨6117107, by rfl⟩ : syracuseStep 8156143 = 12234215) B12234215
theorem B3815279 : Blo 1695548 3815279 := bstep (se 1 (by rfl) ⟨2861459, by rfl⟩ : syracuseStep 3815279 = 5722919) B5722919
theorem B4585747 : Blo 1695548 4585747 := bstep (se 1 (by rfl) ⟨3439310, by rfl⟩ : syracuseStep 4585747 = 6878621) B6878621
theorem B21748895 : Blo 1695548 21748895 := bstep (se 1 (by rfl) ⟨16311671, by rfl⟩ : syracuseStep 21748895 = 32623343) B32623343
theorem B5725511 : Blo 1695548 5725511 := bstep (se 1 (by rfl) ⟨4294133, by rfl⟩ : syracuseStep 5725511 = 8588267) B8588267
theorem B3817385 : Blo 1695548 3817385 := bstep (se 2 (by rfl) ⟨1431519, by rfl⟩ : syracuseStep 3817385 = 2863039) B2863039
theorem B5726375 : Blo 1695548 5726375 := bstep (se 1 (by rfl) ⟨4294781, by rfl⟩ : syracuseStep 5726375 = 8589563) B8589563
theorem B3817655 : Blo 1695548 3817655 := bstep (se 1 (by rfl) ⟨2863241, by rfl⟩ : syracuseStep 3817655 = 5726483) B5726483
theorem B49570177 : Blo 1695548 49570177 := bstep (se 2 (by rfl) ⟨18588816, by rfl⟩ : syracuseStep 49570177 = 37177633) B37177633
theorem B8151455 : Blo 1695548 8151455 := bstep (se 1 (by rfl) ⟨6113591, by rfl⟩ : syracuseStep 8151455 = 12227183) B12227183
theorem B22349357 : Blo 1695548 22349357 := bstep (se 3 (by rfl) ⟨4190504, by rfl⟩ : syracuseStep 22349357 = 8381009) B8381009
theorem B7736057 : Blo 1695548 7736057 := bstep (se 2 (by rfl) ⟨2901021, by rfl⟩ : syracuseStep 7736057 = 5802043) B5802043
theorem B2861851 : Blo 1695548 2861851 := bstep (se 1 (by rfl) ⟨2146388, by rfl⟩ : syracuseStep 2861851 = 4292777) B4292777
theorem B4295551 : Blo 1695548 4295551 := bstep (se 1 (by rfl) ⟨3221663, by rfl⟩ : syracuseStep 4295551 = 6443327) B6443327
theorem B6114329 : Blo 1695548 6114329 := bstep (se 2 (by rfl) ⟨2292873, by rfl⟩ : syracuseStep 6114329 = 4585747) B4585747
theorem B2543519 : Blo 1695548 2543519 := bstep (se 1 (by rfl) ⟨1907639, by rfl⟩ : syracuseStep 2543519 = 3815279) B3815279
theorem B2544923 : Blo 1695548 2544923 := bstep (se 1 (by rfl) ⟨1908692, by rfl⟩ : syracuseStep 2544923 = 3817385) B3817385
theorem B2545193 : Blo 1695548 2545193 := bstep (se 2 (by rfl) ⟨954447, by rfl⟩ : syracuseStep 2545193 = 1908895) B1908895
theorem B587937361 : Blo 1695548 587937361 := bstep (se 2 (by rfl) ⟨220476510, by rfl⟩ : syracuseStep 587937361 = 440953021) B440953021
theorem B4831015 : Blo 1695548 4831015 := bstep (se 1 (by rfl) ⟨3623261, by rfl⟩ : syracuseStep 4831015 = 7246523) B7246523
theorem B21739873 : Blo 1695548 21739873 := bstep (se 2 (by rfl) ⟨8152452, by rfl⟩ : syracuseStep 21739873 = 16304905) B16304905
theorem B2546303 : Blo 1695548 2546303 := bstep (se 1 (by rfl) ⟨1909727, by rfl⟩ : syracuseStep 2546303 = 3819455) B3819455
theorem B9657245 : Blo 1695548 9657245 := bstep (se 3 (by rfl) ⟨1810733, by rfl⟩ : syracuseStep 9657245 = 3621467) B3621467
theorem B8592317 : Blo 1695548 8592317 := bstep (se 3 (by rfl) ⟨1611059, by rfl⟩ : syracuseStep 8592317 = 3222119) B3222119
theorem B14499263 : Blo 1695548 14499263 := bstep (se 1 (by rfl) ⟨10874447, by rfl⟩ : syracuseStep 14499263 = 21748895) B21748895
theorem B3817007 : Blo 1695548 3817007 := bstep (se 1 (by rfl) ⟨2862755, by rfl⟩ : syracuseStep 3817007 = 5725511) B5725511
theorem B24469127 : Blo 1695548 24469127 := bstep (se 1 (by rfl) ⟨18351845, by rfl⟩ : syracuseStep 24469127 = 36703691) B36703691
theorem B16310099 : Blo 1695548 16310099 := bstep (se 1 (by rfl) ⟨12232574, by rfl⟩ : syracuseStep 16310099 = 24465149) B24465149
theorem B43499429 : Blo 1695548 43499429 := bstep (se 4 (by rfl) ⟨4078071, by rfl⟩ : syracuseStep 43499429 = 8156143) B8156143
theorem B3817583 : Blo 1695548 3817583 := bstep (se 1 (by rfl) ⟨2863187, by rfl⟩ : syracuseStep 3817583 = 5726375) B5726375
theorem B66093569 : Blo 1695548 66093569 := bstep (se 2 (by rfl) ⟨24785088, by rfl⟩ : syracuseStep 66093569 = 49570177) B49570177
theorem B1696615 : Blo 1695548 1696615 := bstep (se 1 (by rfl) ⟨1272461, by rfl⟩ : syracuseStep 1696615 = 2544923) B2544923
theorem B1696795 : Blo 1695548 1696795 := bstep (se 1 (by rfl) ⟨1272596, by rfl⟩ : syracuseStep 1696795 = 2545193) B2545193
theorem B5727401 : Blo 1695548 5727401 := bstep (se 2 (by rfl) ⟨2147775, by rfl⟩ : syracuseStep 5727401 = 4295551) B4295551
theorem B1697535 : Blo 1695548 1697535 := bstep (se 1 (by rfl) ⟨1273151, by rfl⟩ : syracuseStep 1697535 = 2546303) B2546303
theorem B5728211 : Blo 1695548 5728211 := bstep (se 1 (by rfl) ⟨4296158, by rfl⟩ : syracuseStep 5728211 = 8592317) B8592317
theorem B6441353 : Blo 1695548 6441353 := bstep (se 2 (by rfl) ⟨2415507, by rfl⟩ : syracuseStep 6441353 = 4831015) B4831015
theorem B16312751 : Blo 1695548 16312751 := bstep (se 1 (by rfl) ⟨12234563, by rfl⟩ : syracuseStep 16312751 = 24469127) B24469127
theorem B10873399 : Blo 1695548 10873399 := bstep (se 1 (by rfl) ⟨8155049, by rfl⟩ : syracuseStep 10873399 = 16310099) B16310099
theorem B5434303 : Blo 1695548 5434303 := bstep (se 1 (by rfl) ⟨4075727, by rfl⟩ : syracuseStep 5434303 = 8151455) B8151455
theorem B28986497 : Blo 1695548 28986497 := bstep (se 2 (by rfl) ⟨10869936, by rfl⟩ : syracuseStep 28986497 = 21739873) B21739873
theorem B5157371 : Blo 1695548 5157371 := bstep (se 1 (by rfl) ⟨3868028, by rfl⟩ : syracuseStep 5157371 = 7736057) B7736057
theorem B4076219 : Blo 1695548 4076219 := bstep (se 1 (by rfl) ⟨3057164, by rfl⟩ : syracuseStep 4076219 = 6114329) B6114329
theorem B2544671 : Blo 1695548 2544671 := bstep (se 1 (by rfl) ⟨1908503, by rfl⟩ : syracuseStep 2544671 = 3817007) B3817007
theorem B2545103 : Blo 1695548 2545103 := bstep (se 1 (by rfl) ⟨1908827, by rfl⟩ : syracuseStep 2545103 = 3817655) B3817655
theorem B14899571 : Blo 1695548 14899571 := bstep (se 1 (by rfl) ⟨11174678, by rfl⟩ : syracuseStep 14899571 = 22349357) B22349357
theorem B3815801 : Blo 1695548 3815801 := bstep (se 2 (by rfl) ⟨1430925, by rfl⟩ : syracuseStep 3815801 = 2861851) B2861851
theorem B6438163 : Blo 1695548 6438163 := bstep (se 1 (by rfl) ⟨4828622, by rfl⟩ : syracuseStep 6438163 = 9657245) B9657245
theorem B783916481 : Blo 1695548 783916481 := bstep (se 2 (by rfl) ⟨293968680, by rfl⟩ : syracuseStep 783916481 = 587937361) B587937361
theorem B9666175 : Blo 1695548 9666175 := bstep (se 1 (by rfl) ⟨7249631, by rfl⟩ : syracuseStep 9666175 = 14499263) B14499263
theorem B1695679 : Blo 1695548 1695679 := bstep (se 1 (by rfl) ⟨1271759, by rfl⟩ : syracuseStep 1695679 = 2543519) B2543519
theorem B28999619 : Blo 1695548 28999619 := bstep (se 1 (by rfl) ⟨21749714, by rfl⟩ : syracuseStep 28999619 = 43499429) B43499429
theorem B1696447 : Blo 1695548 1696447 := bstep (se 1 (by rfl) ⟨1272335, by rfl⟩ : syracuseStep 1696447 = 2544671) B2544671
theorem B3818267 : Blo 1695548 3818267 := bstep (se 1 (by rfl) ⟨2863700, by rfl⟩ : syracuseStep 3818267 = 5727401) B5727401
theorem B1696735 : Blo 1695548 1696735 := bstep (se 1 (by rfl) ⟨1272551, by rfl⟩ : syracuseStep 1696735 = 2545103) B2545103
theorem B3818807 : Blo 1695548 3818807 := bstep (se 1 (by rfl) ⟨2864105, by rfl⟩ : syracuseStep 3818807 = 5728211) B5728211
theorem B4294235 : Blo 1695548 4294235 := bstep (se 1 (by rfl) ⟨3220676, by rfl⟩ : syracuseStep 4294235 = 6441353) B6441353
theorem B12888233 : Blo 1695548 12888233 := bstep (se 2 (by rfl) ⟨4833087, by rfl⟩ : syracuseStep 12888233 = 9666175) B9666175
theorem B522610987 : Blo 1695548 522610987 := bstep (se 1 (by rfl) ⟨391958240, by rfl⟩ : syracuseStep 522610987 = 783916481) B783916481
theorem B7245737 : Blo 1695548 7245737 := bstep (se 2 (by rfl) ⟨2717151, by rfl⟩ : syracuseStep 7245737 = 5434303) B5434303
theorem B9933047 : Blo 1695548 9933047 := bstep (se 1 (by rfl) ⟨7449785, by rfl⟩ : syracuseStep 9933047 = 14899571) B14899571
theorem B2543867 : Blo 1695548 2543867 := bstep (se 1 (by rfl) ⟨1907900, by rfl⟩ : syracuseStep 2543867 = 3815801) B3815801
theorem B10875167 : Blo 1695548 10875167 := bstep (se 1 (by rfl) ⟨8156375, by rfl⟩ : syracuseStep 10875167 = 16312751) B16312751
theorem B2545055 : Blo 1695548 2545055 := bstep (se 1 (by rfl) ⟨1908791, by rfl⟩ : syracuseStep 2545055 = 3817583) B3817583
theorem B3438247 : Blo 1695548 3438247 := bstep (se 1 (by rfl) ⟨2578685, by rfl⟩ : syracuseStep 3438247 = 5157371) B5157371
theorem B44062379 : Blo 1695548 44062379 := bstep (se 1 (by rfl) ⟨33046784, by rfl⟩ : syracuseStep 44062379 = 66093569) B66093569
theorem B2717479 : Blo 1695548 2717479 := bstep (se 1 (by rfl) ⟨2038109, by rfl⟩ : syracuseStep 2717479 = 4076219) B4076219
theorem B14497865 : Blo 1695548 14497865 := bstep (se 2 (by rfl) ⟨5436699, by rfl⟩ : syracuseStep 14497865 = 10873399) B10873399
theorem B8584217 : Blo 1695548 8584217 := bstep (se 2 (by rfl) ⟨3219081, by rfl⟩ : syracuseStep 8584217 = 6438163) B6438163
theorem B19324331 : Blo 1695548 19324331 := bstep (se 1 (by rfl) ⟨14493248, by rfl⟩ : syracuseStep 19324331 = 28986497) B28986497
theorem B19333079 : Blo 1695548 19333079 := bstep (se 1 (by rfl) ⟨14499809, by rfl⟩ : syracuseStep 19333079 = 28999619) B28999619
theorem B1695911 : Blo 1695548 1695911 := bstep (se 1 (by rfl) ⟨1271933, by rfl⟩ : syracuseStep 1695911 = 2543867) B2543867
theorem B7250111 : Blo 1695548 7250111 := bstep (se 1 (by rfl) ⟨5437583, by rfl⟩ : syracuseStep 7250111 = 10875167) B10875167
theorem B1696703 : Blo 1695548 1696703 := bstep (se 1 (by rfl) ⟨1272527, by rfl⟩ : syracuseStep 1696703 = 2545055) B2545055
theorem B3623305 : Blo 1695548 3623305 := bstep (se 2 (by rfl) ⟨1358739, by rfl⟩ : syracuseStep 3623305 = 2717479) B2717479
theorem B12888719 : Blo 1695548 12888719 := bstep (se 1 (by rfl) ⟨9666539, by rfl⟩ : syracuseStep 12888719 = 19333079) B19333079
theorem B6622031 : Blo 1695548 6622031 := bstep (se 1 (by rfl) ⟨4966523, by rfl⟩ : syracuseStep 6622031 = 9933047) B9933047
theorem B696814649 : Blo 1695548 696814649 := bstep (se 2 (by rfl) ⟨261305493, by rfl⟩ : syracuseStep 696814649 = 522610987) B522610987
theorem B2862823 : Blo 1695548 2862823 := bstep (se 1 (by rfl) ⟨2147117, by rfl⟩ : syracuseStep 2862823 = 4294235) B4294235
theorem B5722811 : Blo 1695548 5722811 := bstep (se 1 (by rfl) ⟨4292108, by rfl⟩ : syracuseStep 5722811 = 8584217) B8584217
theorem B4584329 : Blo 1695548 4584329 := bstep (se 2 (by rfl) ⟨1719123, by rfl⟩ : syracuseStep 4584329 = 3438247) B3438247
theorem B12882887 : Blo 1695548 12882887 := bstep (se 1 (by rfl) ⟨9662165, by rfl⟩ : syracuseStep 12882887 = 19324331) B19324331
theorem B4830491 : Blo 1695548 4830491 := bstep (se 1 (by rfl) ⟨3622868, by rfl⟩ : syracuseStep 4830491 = 7245737) B7245737
theorem B2545511 : Blo 1695548 2545511 := bstep (se 1 (by rfl) ⟨1909133, by rfl⟩ : syracuseStep 2545511 = 3818267) B3818267
theorem B2545871 : Blo 1695548 2545871 := bstep (se 1 (by rfl) ⟨1909403, by rfl⟩ : syracuseStep 2545871 = 3818807) B3818807
theorem B29374919 : Blo 1695548 29374919 := bstep (se 1 (by rfl) ⟨22031189, by rfl⟩ : syracuseStep 29374919 = 44062379) B44062379
theorem B9665243 : Blo 1695548 9665243 := bstep (se 1 (by rfl) ⟨7248932, by rfl⟩ : syracuseStep 9665243 = 14497865) B14497865
theorem B8592155 : Blo 1695548 8592155 := bstep (se 1 (by rfl) ⟨6444116, by rfl⟩ : syracuseStep 8592155 = 12888233) B12888233
theorem B4833407 : Blo 1695548 4833407 := bstep (se 1 (by rfl) ⟨3625055, by rfl⟩ : syracuseStep 4833407 = 7250111) B7250111
theorem B3056219 : Blo 1695548 3056219 := bstep (se 1 (by rfl) ⟨2292164, by rfl⟩ : syracuseStep 3056219 = 4584329) B4584329
theorem B3220327 : Blo 1695548 3220327 := bstep (se 1 (by rfl) ⟨2415245, by rfl⟩ : syracuseStep 3220327 = 4830491) B4830491
theorem B1697007 : Blo 1695548 1697007 := bstep (se 1 (by rfl) ⟨1272755, by rfl⟩ : syracuseStep 1697007 = 2545511) B2545511
theorem B1697247 : Blo 1695548 1697247 := bstep (se 1 (by rfl) ⟨1272935, by rfl⟩ : syracuseStep 1697247 = 2545871) B2545871
theorem B5728103 : Blo 1695548 5728103 := bstep (se 1 (by rfl) ⟨4296077, by rfl⟩ : syracuseStep 5728103 = 8592155) B8592155
theorem B8588591 : Blo 1695548 8588591 := bstep (se 1 (by rfl) ⟨6441443, by rfl⟩ : syracuseStep 8588591 = 12882887) B12882887
theorem B19583279 : Blo 1695548 19583279 := bstep (se 1 (by rfl) ⟨14687459, by rfl⟩ : syracuseStep 19583279 = 29374919) B29374919
theorem B6443495 : Blo 1695548 6443495 := bstep (se 1 (by rfl) ⟨4832621, by rfl⟩ : syracuseStep 6443495 = 9665243) B9665243
theorem B17658749 : Blo 1695548 17658749 := bstep (se 3 (by rfl) ⟨3311015, by rfl⟩ : syracuseStep 17658749 = 6622031) B6622031
theorem B3815207 : Blo 1695548 3815207 := bstep (se 1 (by rfl) ⟨2861405, by rfl⟩ : syracuseStep 3815207 = 5722811) B5722811
theorem B4831073 : Blo 1695548 4831073 := bstep (se 2 (by rfl) ⟨1811652, by rfl⟩ : syracuseStep 4831073 = 3623305) B3623305
theorem B8592479 : Blo 1695548 8592479 := bstep (se 1 (by rfl) ⟨6444359, by rfl⟩ : syracuseStep 8592479 = 12888719) B12888719
theorem B464543099 : Blo 1695548 464543099 := bstep (se 1 (by rfl) ⟨348407324, by rfl⟩ : syracuseStep 464543099 = 696814649) B696814649
theorem B3817097 : Blo 1695548 3817097 := bstep (se 2 (by rfl) ⟨1431411, by rfl⟩ : syracuseStep 3817097 = 2862823) B2862823
theorem B4293769 : Blo 1695548 4293769 := bstep (se 2 (by rfl) ⟨1610163, by rfl⟩ : syracuseStep 4293769 = 3220327) B3220327
theorem B3220715 : Blo 1695548 3220715 := bstep (se 1 (by rfl) ⟨2415536, by rfl⟩ : syracuseStep 3220715 = 4831073) B4831073
theorem B3818735 : Blo 1695548 3818735 := bstep (se 1 (by rfl) ⟨2864051, by rfl⟩ : syracuseStep 3818735 = 5728103) B5728103
theorem B5728319 : Blo 1695548 5728319 := bstep (se 1 (by rfl) ⟨4296239, by rfl⟩ : syracuseStep 5728319 = 8592479) B8592479
theorem B47089997 : Blo 1695548 47089997 := bstep (se 3 (by rfl) ⟨8829374, by rfl⟩ : syracuseStep 47089997 = 17658749) B17658749
theorem B3222271 : Blo 1695548 3222271 := bstep (se 1 (by rfl) ⟨2416703, by rfl⟩ : syracuseStep 3222271 = 4833407) B4833407
theorem B4295663 : Blo 1695548 4295663 := bstep (se 1 (by rfl) ⟨3221747, by rfl⟩ : syracuseStep 4295663 = 6443495) B6443495
theorem B2543471 : Blo 1695548 2543471 := bstep (se 1 (by rfl) ⟨1907603, by rfl⟩ : syracuseStep 2543471 = 3815207) B3815207
theorem B309695399 : Blo 1695548 309695399 := bstep (se 1 (by rfl) ⟨232271549, by rfl⟩ : syracuseStep 309695399 = 464543099) B464543099
theorem B2544731 : Blo 1695548 2544731 := bstep (se 1 (by rfl) ⟨1908548, by rfl⟩ : syracuseStep 2544731 = 3817097) B3817097
theorem B13055519 : Blo 1695548 13055519 := bstep (se 1 (by rfl) ⟨9791639, by rfl⟩ : syracuseStep 13055519 = 19583279) B19583279
theorem B2037479 : Blo 1695548 2037479 := bstep (se 1 (by rfl) ⟨1528109, by rfl⟩ : syracuseStep 2037479 = 3056219) B3056219
theorem B5725727 : Blo 1695548 5725727 := bstep (se 1 (by rfl) ⟨4294295, by rfl⟩ : syracuseStep 5725727 = 8588591) B8588591
theorem B206463599 : Blo 1695548 206463599 := bstep (se 1 (by rfl) ⟨154847699, by rfl⟩ : syracuseStep 206463599 = 309695399) B309695399
theorem B1696487 : Blo 1695548 1696487 := bstep (se 1 (by rfl) ⟨1272365, by rfl⟩ : syracuseStep 1696487 = 2544731) B2544731
theorem B2147143 : Blo 1695548 2147143 := bstep (se 1 (by rfl) ⟨1610357, by rfl⟩ : syracuseStep 2147143 = 3220715) B3220715
theorem B3818879 : Blo 1695548 3818879 := bstep (se 1 (by rfl) ⟨2864159, by rfl⟩ : syracuseStep 3818879 = 5728319) B5728319
theorem B31393331 : Blo 1695548 31393331 := bstep (se 1 (by rfl) ⟨23544998, by rfl⟩ : syracuseStep 31393331 = 47089997) B47089997
theorem B4296361 : Blo 1695548 4296361 := bstep (se 2 (by rfl) ⟨1611135, by rfl⟩ : syracuseStep 4296361 = 3222271) B3222271
theorem B2863775 : Blo 1695548 2863775 := bstep (se 1 (by rfl) ⟨2147831, by rfl⟩ : syracuseStep 2863775 = 4295663) B4295663
theorem B2545823 : Blo 1695548 2545823 := bstep (se 1 (by rfl) ⟨1909367, by rfl⟩ : syracuseStep 2545823 = 3818735) B3818735
theorem B34814717 : Blo 1695548 34814717 := bstep (se 3 (by rfl) ⟨6527759, by rfl⟩ : syracuseStep 34814717 = 13055519) B13055519
theorem B5725025 : Blo 1695548 5725025 := bstep (se 2 (by rfl) ⟨2146884, by rfl⟩ : syracuseStep 5725025 = 4293769) B4293769
theorem B3817151 : Blo 1695548 3817151 := bstep (se 1 (by rfl) ⟨2862863, by rfl⟩ : syracuseStep 3817151 = 5725727) B5725727
theorem B21733109 : Blo 1695548 21733109 := bstep (se 5 (by rfl) ⟨1018739, by rfl⟩ : syracuseStep 21733109 = 2037479) B2037479
theorem B1695647 : Blo 1695548 1695647 := bstep (se 1 (by rfl) ⟨1271735, by rfl⟩ : syracuseStep 1695647 = 2543471) B2543471
theorem B137642399 : Blo 1695548 137642399 := bstep (se 1 (by rfl) ⟨103231799, by rfl⟩ : syracuseStep 137642399 = 206463599) B206463599
theorem B1909183 : Blo 1695548 1909183 := bstep (se 1 (by rfl) ⟨1431887, by rfl⟩ : syracuseStep 1909183 = 2863775) B2863775
theorem B1697215 : Blo 1695548 1697215 := bstep (se 1 (by rfl) ⟨1272911, by rfl⟩ : syracuseStep 1697215 = 2545823) B2545823
theorem B23209811 : Blo 1695548 23209811 := bstep (se 1 (by rfl) ⟨17407358, by rfl⟩ : syracuseStep 23209811 = 34814717) B34814717
theorem B5728481 : Blo 1695548 5728481 := bstep (se 2 (by rfl) ⟨2148180, by rfl⟩ : syracuseStep 5728481 = 4296361) B4296361
theorem B2862857 : Blo 1695548 2862857 := bstep (se 2 (by rfl) ⟨1073571, by rfl⟩ : syracuseStep 2862857 = 2147143) B2147143
theorem B2544767 : Blo 1695548 2544767 := bstep (se 1 (by rfl) ⟨1908575, by rfl⟩ : syracuseStep 2544767 = 3817151) B3817151
theorem B14488739 : Blo 1695548 14488739 := bstep (se 1 (by rfl) ⟨10866554, by rfl⟩ : syracuseStep 14488739 = 21733109) B21733109
theorem B2545919 : Blo 1695548 2545919 := bstep (se 1 (by rfl) ⟨1909439, by rfl⟩ : syracuseStep 2545919 = 3818879) B3818879
theorem B20928887 : Blo 1695548 20928887 := bstep (se 1 (by rfl) ⟨15696665, by rfl⟩ : syracuseStep 20928887 = 31393331) B31393331
theorem B3816683 : Blo 1695548 3816683 := bstep (se 1 (by rfl) ⟨2862512, by rfl⟩ : syracuseStep 3816683 = 5725025) B5725025
theorem B1696511 : Blo 1695548 1696511 := bstep (se 1 (by rfl) ⟨1272383, by rfl⟩ : syracuseStep 1696511 = 2544767) B2544767
theorem B9659159 : Blo 1695548 9659159 := bstep (se 1 (by rfl) ⟨7244369, by rfl⟩ : syracuseStep 9659159 = 14488739) B14488739
theorem B3818987 : Blo 1695548 3818987 := bstep (se 1 (by rfl) ⟨2864240, by rfl⟩ : syracuseStep 3818987 = 5728481) B5728481
theorem B1697279 : Blo 1695548 1697279 := bstep (se 1 (by rfl) ⟨1272959, by rfl⟩ : syracuseStep 1697279 = 2545919) B2545919
theorem B13952591 : Blo 1695548 13952591 := bstep (se 1 (by rfl) ⟨10464443, by rfl⟩ : syracuseStep 13952591 = 20928887) B20928887
theorem B91761599 : Blo 1695548 91761599 := bstep (se 1 (by rfl) ⟨68821199, by rfl⟩ : syracuseStep 91761599 = 137642399) B137642399
theorem B2544455 : Blo 1695548 2544455 := bstep (se 1 (by rfl) ⟨1908341, by rfl⟩ : syracuseStep 2544455 = 3816683) B3816683
theorem B2545577 : Blo 1695548 2545577 := bstep (se 2 (by rfl) ⟨954591, by rfl⟩ : syracuseStep 2545577 = 1909183) B1909183
theorem B15473207 : Blo 1695548 15473207 := bstep (se 1 (by rfl) ⟨11604905, by rfl⟩ : syracuseStep 15473207 = 23209811) B23209811
theorem B1908571 : Blo 1695548 1908571 := bstep (se 1 (by rfl) ⟨1431428, by rfl⟩ : syracuseStep 1908571 = 2862857) B2862857
theorem B6439439 : Blo 1695548 6439439 := bstep (se 1 (by rfl) ⟨4829579, by rfl⟩ : syracuseStep 6439439 = 9659159) B9659159
theorem B1696303 : Blo 1695548 1696303 := bstep (se 1 (by rfl) ⟨1272227, by rfl⟩ : syracuseStep 1696303 = 2544455) B2544455
theorem B1697051 : Blo 1695548 1697051 := bstep (se 1 (by rfl) ⟨1272788, by rfl⟩ : syracuseStep 1697051 = 2545577) B2545577
theorem B10315471 : Blo 1695548 10315471 := bstep (se 1 (by rfl) ⟨7736603, by rfl⟩ : syracuseStep 10315471 = 15473207) B15473207
theorem B9301727 : Blo 1695548 9301727 := bstep (se 1 (by rfl) ⟨6976295, by rfl⟩ : syracuseStep 9301727 = 13952591) B13952591
theorem B61174399 : Blo 1695548 61174399 := bstep (se 1 (by rfl) ⟨45880799, by rfl⟩ : syracuseStep 61174399 = 91761599) B91761599
theorem B2544761 : Blo 1695548 2544761 := bstep (se 2 (by rfl) ⟨954285, by rfl⟩ : syracuseStep 2544761 = 1908571) B1908571
theorem B2545991 : Blo 1695548 2545991 := bstep (se 1 (by rfl) ⟨1909493, by rfl⟩ : syracuseStep 2545991 = 3818987) B3818987
theorem B4292959 : Blo 1695548 4292959 := bstep (se 1 (by rfl) ⟨3219719, by rfl⟩ : syracuseStep 4292959 = 6439439) B6439439
theorem B1696507 : Blo 1695548 1696507 := bstep (se 1 (by rfl) ⟨1272380, by rfl⟩ : syracuseStep 1696507 = 2544761) B2544761
theorem B1697327 : Blo 1695548 1697327 := bstep (se 1 (by rfl) ⟨1272995, by rfl⟩ : syracuseStep 1697327 = 2545991) B2545991
theorem B81565865 : Blo 1695548 81565865 := bstep (se 2 (by rfl) ⟨30587199, by rfl⟩ : syracuseStep 81565865 = 61174399) B61174399
theorem B24804605 : Blo 1695548 24804605 := bstep (se 3 (by rfl) ⟨4650863, by rfl⟩ : syracuseStep 24804605 = 9301727) B9301727
theorem B13753961 : Blo 1695548 13753961 := bstep (se 2 (by rfl) ⟨5157735, by rfl⟩ : syracuseStep 13753961 = 10315471) B10315471
theorem B9169307 : Blo 1695548 9169307 := bstep (se 1 (by rfl) ⟨6876980, by rfl⟩ : syracuseStep 9169307 = 13753961) B13753961
theorem B16536403 : Blo 1695548 16536403 := bstep (se 1 (by rfl) ⟨12402302, by rfl⟩ : syracuseStep 16536403 = 24804605) B24804605
theorem B5723945 : Blo 1695548 5723945 := bstep (se 2 (by rfl) ⟨2146479, by rfl⟩ : syracuseStep 5723945 = 4292959) B4292959
theorem B54377243 : Blo 1695548 54377243 := bstep (se 1 (by rfl) ⟨40782932, by rfl⟩ : syracuseStep 54377243 = 81565865) B81565865
theorem B6112871 : Blo 1695548 6112871 := bstep (se 1 (by rfl) ⟨4584653, by rfl⟩ : syracuseStep 6112871 = 9169307) B9169307
theorem B36251495 : Blo 1695548 36251495 := bstep (se 1 (by rfl) ⟨27188621, by rfl⟩ : syracuseStep 36251495 = 54377243) B54377243
theorem B22048537 : Blo 1695548 22048537 := bstep (se 2 (by rfl) ⟨8268201, by rfl⟩ : syracuseStep 22048537 = 16536403) B16536403
theorem B3815963 : Blo 1695548 3815963 := bstep (se 1 (by rfl) ⟨2861972, by rfl⟩ : syracuseStep 3815963 = 5723945) B5723945
theorem B24167663 : Blo 1695548 24167663 := bstep (se 1 (by rfl) ⟨18125747, by rfl⟩ : syracuseStep 24167663 = 36251495) B36251495
theorem B4075247 : Blo 1695548 4075247 := bstep (se 1 (by rfl) ⟨3056435, by rfl⟩ : syracuseStep 4075247 = 6112871) B6112871
theorem B2543975 : Blo 1695548 2543975 := bstep (se 1 (by rfl) ⟨1907981, by rfl⟩ : syracuseStep 2543975 = 3815963) B3815963
theorem B29398049 : Blo 1695548 29398049 := bstep (se 2 (by rfl) ⟨11024268, by rfl⟩ : syracuseStep 29398049 = 22048537) B22048537
theorem B1695983 : Blo 1695548 1695983 := bstep (se 1 (by rfl) ⟨1271987, by rfl⟩ : syracuseStep 1695983 = 2543975) B2543975
theorem B19598699 : Blo 1695548 19598699 := bstep (se 1 (by rfl) ⟨14699024, by rfl⟩ : syracuseStep 19598699 = 29398049) B29398049
theorem B2716831 : Blo 1695548 2716831 := bstep (se 1 (by rfl) ⟨2037623, by rfl⟩ : syracuseStep 2716831 = 4075247) B4075247
theorem B16111775 : Blo 1695548 16111775 := bstep (se 1 (by rfl) ⟨12083831, by rfl⟩ : syracuseStep 16111775 = 24167663) B24167663
theorem B10741183 : Blo 1695548 10741183 := bstep (se 1 (by rfl) ⟨8055887, by rfl⟩ : syracuseStep 10741183 = 16111775) B16111775
theorem B14489765 : Blo 1695548 14489765 := bstep (se 4 (by rfl) ⟨1358415, by rfl⟩ : syracuseStep 14489765 = 2716831) B2716831
theorem B13065799 : Blo 1695548 13065799 := bstep (se 1 (by rfl) ⟨9799349, by rfl⟩ : syracuseStep 13065799 = 19598699) B19598699
theorem B9659843 : Blo 1695548 9659843 := bstep (se 1 (by rfl) ⟨7244882, by rfl⟩ : syracuseStep 9659843 = 14489765) B14489765
theorem B17421065 : Blo 1695548 17421065 := bstep (se 2 (by rfl) ⟨6532899, by rfl⟩ : syracuseStep 17421065 = 13065799) B13065799
theorem B57286309 : Blo 1695548 57286309 := bstep (se 4 (by rfl) ⟨5370591, by rfl⟩ : syracuseStep 57286309 = 10741183) B10741183
theorem B6439895 : Blo 1695548 6439895 := bstep (se 1 (by rfl) ⟨4829921, by rfl⟩ : syracuseStep 6439895 = 9659843) B9659843
theorem B11614043 : Blo 1695548 11614043 := bstep (se 1 (by rfl) ⟨8710532, by rfl⟩ : syracuseStep 11614043 = 17421065) B17421065
theorem B76381745 : Blo 1695548 76381745 := bstep (se 2 (by rfl) ⟨28643154, by rfl⟩ : syracuseStep 76381745 = 57286309) B57286309
theorem B4293263 : Blo 1695548 4293263 := bstep (se 1 (by rfl) ⟨3219947, by rfl⟩ : syracuseStep 4293263 = 6439895) B6439895
theorem B30970781 : Blo 1695548 30970781 := bstep (se 3 (by rfl) ⟨5807021, by rfl⟩ : syracuseStep 30970781 = 11614043) B11614043
theorem B203684653 : Blo 1695548 203684653 := bstep (se 3 (by rfl) ⟨38190872, by rfl⟩ : syracuseStep 203684653 = 76381745) B76381745
theorem B2862175 : Blo 1695548 2862175 := bstep (se 1 (by rfl) ⟨2146631, by rfl⟩ : syracuseStep 2862175 = 4293263) B4293263
theorem B20647187 : Blo 1695548 20647187 := bstep (se 1 (by rfl) ⟨15485390, by rfl⟩ : syracuseStep 20647187 = 30970781) B30970781
theorem B271579537 : Blo 1695548 271579537 := bstep (se 2 (by rfl) ⟨101842326, by rfl⟩ : syracuseStep 271579537 = 203684653) B203684653
theorem B13764791 : Blo 1695548 13764791 := bstep (se 1 (by rfl) ⟨10323593, by rfl⟩ : syracuseStep 13764791 = 20647187) B20647187
theorem B362106049 : Blo 1695548 362106049 := bstep (se 2 (by rfl) ⟨135789768, by rfl⟩ : syracuseStep 362106049 = 271579537) B271579537
theorem B3816233 : Blo 1695548 3816233 := bstep (se 2 (by rfl) ⟨1431087, by rfl⟩ : syracuseStep 3816233 = 2862175) B2862175
theorem B9176527 : Blo 1695548 9176527 := bstep (se 1 (by rfl) ⟨6882395, by rfl⟩ : syracuseStep 9176527 = 13764791) B13764791
theorem B482808065 : Blo 1695548 482808065 := bstep (se 2 (by rfl) ⟨181053024, by rfl⟩ : syracuseStep 482808065 = 362106049) B362106049
theorem B2544155 : Blo 1695548 2544155 := bstep (se 1 (by rfl) ⟨1908116, by rfl⟩ : syracuseStep 2544155 = 3816233) B3816233
theorem B1696103 : Blo 1695548 1696103 := bstep (se 1 (by rfl) ⟨1272077, by rfl⟩ : syracuseStep 1696103 = 2544155) B2544155
theorem B5149952693 : Blo 1695548 5149952693 := bstep (se 5 (by rfl) ⟨241404032, by rfl⟩ : syracuseStep 5149952693 = 482808065) B482808065
theorem B12235369 : Blo 1695548 12235369 := bstep (se 2 (by rfl) ⟨4588263, by rfl⟩ : syracuseStep 12235369 = 9176527) B9176527
theorem B3433301795 : Blo 1695548 3433301795 := bstep (se 1 (by rfl) ⟨2574976346, by rfl⟩ : syracuseStep 3433301795 = 5149952693) B5149952693
theorem B16313825 : Blo 1695548 16313825 := bstep (se 2 (by rfl) ⟨6117684, by rfl⟩ : syracuseStep 16313825 = 12235369) B12235369
theorem B10875883 : Blo 1695548 10875883 := bstep (se 1 (by rfl) ⟨8156912, by rfl⟩ : syracuseStep 10875883 = 16313825) B16313825
theorem B2288867863 : Blo 1695548 2288867863 := bstep (se 1 (by rfl) ⟨1716650897, by rfl⟩ : syracuseStep 2288867863 = 3433301795) B3433301795
theorem B3051823817 : Blo 1695548 3051823817 := bstep (se 2 (by rfl) ⟨1144433931, by rfl⟩ : syracuseStep 3051823817 = 2288867863) B2288867863
theorem B14501177 : Blo 1695548 14501177 := bstep (se 2 (by rfl) ⟨5437941, by rfl⟩ : syracuseStep 14501177 = 10875883) B10875883
theorem B9667451 : Blo 1695548 9667451 := bstep (se 1 (by rfl) ⟨7250588, by rfl⟩ : syracuseStep 9667451 = 14501177) B14501177
theorem B8138196845 : Blo 1695548 8138196845 := bstep (se 3 (by rfl) ⟨1525911908, by rfl⟩ : syracuseStep 8138196845 = 3051823817) B3051823817
theorem B5425464563 : Blo 1695548 5425464563 := bstep (se 1 (by rfl) ⟨4069098422, by rfl⟩ : syracuseStep 5425464563 = 8138196845) B8138196845
theorem B6444967 : Blo 1695548 6444967 := bstep (se 1 (by rfl) ⟨4833725, by rfl⟩ : syracuseStep 6444967 = 9667451) B9667451
theorem B3616976375 : Blo 1695548 3616976375 := bstep (se 1 (by rfl) ⟨2712732281, by rfl⟩ : syracuseStep 3616976375 = 5425464563) B5425464563
theorem B8593289 : Blo 1695548 8593289 := bstep (se 2 (by rfl) ⟨3222483, by rfl⟩ : syracuseStep 8593289 = 6444967) B6444967
theorem B2411317583 : Blo 1695548 2411317583 := bstep (se 1 (by rfl) ⟨1808488187, by rfl⟩ : syracuseStep 2411317583 = 3616976375) B3616976375
theorem B5728859 : Blo 1695548 5728859 := bstep (se 1 (by rfl) ⟨4296644, by rfl⟩ : syracuseStep 5728859 = 8593289) B8593289
theorem B3819239 : Blo 1695548 3819239 := bstep (se 1 (by rfl) ⟨2864429, by rfl⟩ : syracuseStep 3819239 = 5728859) B5728859
theorem B1607545055 : Blo 1695548 1607545055 := bstep (se 1 (by rfl) ⟨1205658791, by rfl⟩ : syracuseStep 1607545055 = 2411317583) B2411317583
theorem B1071696703 : Blo 1695548 1071696703 := bstep (se 1 (by rfl) ⟨803772527, by rfl⟩ : syracuseStep 1071696703 = 1607545055) B1607545055
theorem B2546159 : Blo 1695548 2546159 := bstep (se 1 (by rfl) ⟨1909619, by rfl⟩ : syracuseStep 2546159 = 3819239) B3819239
theorem B1697439 : Blo 1695548 1697439 := bstep (se 1 (by rfl) ⟨1273079, by rfl⟩ : syracuseStep 1697439 = 2546159) B2546159
theorem B1428928937 : Blo 1695548 1428928937 := bstep (se 2 (by rfl) ⟨535848351, by rfl⟩ : syracuseStep 1428928937 = 1071696703) B1071696703
theorem B952619291 : Blo 1695548 952619291 := bstep (se 1 (by rfl) ⟨714464468, by rfl⟩ : syracuseStep 952619291 = 1428928937) B1428928937
theorem B635079527 : Blo 1695548 635079527 := bstep (se 1 (by rfl) ⟨476309645, by rfl⟩ : syracuseStep 635079527 = 952619291) B952619291
theorem B423386351 : Blo 1695548 423386351 := bstep (se 1 (by rfl) ⟨317539763, by rfl⟩ : syracuseStep 423386351 = 635079527) B635079527
theorem B282257567 : Blo 1695548 282257567 := bstep (se 1 (by rfl) ⟨211693175, by rfl⟩ : syracuseStep 282257567 = 423386351) B423386351
theorem B188171711 : Blo 1695548 188171711 := bstep (se 1 (by rfl) ⟨141128783, by rfl⟩ : syracuseStep 188171711 = 282257567) B282257567
theorem B125447807 : Blo 1695548 125447807 := bstep (se 1 (by rfl) ⟨94085855, by rfl⟩ : syracuseStep 125447807 = 188171711) B188171711
theorem B83631871 : Blo 1695548 83631871 := bstep (se 1 (by rfl) ⟨62723903, by rfl⟩ : syracuseStep 83631871 = 125447807) B125447807
theorem B446036645 : Blo 1695548 446036645 := bstep (se 4 (by rfl) ⟨41815935, by rfl⟩ : syracuseStep 446036645 = 83631871) B83631871
theorem B297357763 : Blo 1695548 297357763 := bstep (se 1 (by rfl) ⟨223018322, by rfl⟩ : syracuseStep 297357763 = 446036645) B446036645
theorem B396477017 : Blo 1695548 396477017 := bstep (se 2 (by rfl) ⟨148678881, by rfl⟩ : syracuseStep 396477017 = 297357763) B297357763
theorem B264318011 : Blo 1695548 264318011 := bstep (se 1 (by rfl) ⟨198238508, by rfl⟩ : syracuseStep 264318011 = 396477017) B396477017
theorem B176212007 : Blo 1695548 176212007 := bstep (se 1 (by rfl) ⟨132159005, by rfl⟩ : syracuseStep 176212007 = 264318011) B264318011
theorem B117474671 : Blo 1695548 117474671 := bstep (se 1 (by rfl) ⟨88106003, by rfl⟩ : syracuseStep 117474671 = 176212007) B176212007
theorem B313265789 : Blo 1695548 313265789 := bstep (se 3 (by rfl) ⟨58737335, by rfl⟩ : syracuseStep 313265789 = 117474671) B117474671
theorem B208843859 : Blo 1695548 208843859 := bstep (se 1 (by rfl) ⟨156632894, by rfl⟩ : syracuseStep 208843859 = 313265789) B313265789
theorem B139229239 : Blo 1695548 139229239 := bstep (se 1 (by rfl) ⟨104421929, by rfl⟩ : syracuseStep 139229239 = 208843859) B208843859
theorem B185638985 : Blo 1695548 185638985 := bstep (se 2 (by rfl) ⟨69614619, by rfl⟩ : syracuseStep 185638985 = 139229239) B139229239
theorem B123759323 : Blo 1695548 123759323 := bstep (se 1 (by rfl) ⟨92819492, by rfl⟩ : syracuseStep 123759323 = 185638985) B185638985
theorem B82506215 : Blo 1695548 82506215 := bstep (se 1 (by rfl) ⟨61879661, by rfl⟩ : syracuseStep 82506215 = 123759323) B123759323
theorem B220016573 : Blo 1695548 220016573 := bstep (se 3 (by rfl) ⟨41253107, by rfl⟩ : syracuseStep 220016573 = 82506215) B82506215
theorem B146677715 : Blo 1695548 146677715 := bstep (se 1 (by rfl) ⟨110008286, by rfl⟩ : syracuseStep 146677715 = 220016573) B220016573
theorem B97785143 : Blo 1695548 97785143 := bstep (se 1 (by rfl) ⟨73338857, by rfl⟩ : syracuseStep 97785143 = 146677715) B146677715
theorem B65190095 : Blo 1695548 65190095 := bstep (se 1 (by rfl) ⟨48892571, by rfl⟩ : syracuseStep 65190095 = 97785143) B97785143
theorem B43460063 : Blo 1695548 43460063 := bstep (se 1 (by rfl) ⟨32595047, by rfl⟩ : syracuseStep 43460063 = 65190095) B65190095
theorem B28973375 : Blo 1695548 28973375 := bstep (se 1 (by rfl) ⟨21730031, by rfl⟩ : syracuseStep 28973375 = 43460063) B43460063
theorem B19315583 : Blo 1695548 19315583 := bstep (se 1 (by rfl) ⟨14486687, by rfl⟩ : syracuseStep 19315583 = 28973375) B28973375
theorem B12877055 : Blo 1695548 12877055 := bstep (se 1 (by rfl) ⟨9657791, by rfl⟩ : syracuseStep 12877055 = 19315583) B19315583
theorem B8584703 : Blo 1695548 8584703 := bstep (se 1 (by rfl) ⟨6438527, by rfl⟩ : syracuseStep 8584703 = 12877055) B12877055
theorem B5723135 : Blo 1695548 5723135 := bstep (se 1 (by rfl) ⟨4292351, by rfl⟩ : syracuseStep 5723135 = 8584703) B8584703
theorem B3815423 : Blo 1695548 3815423 := bstep (se 1 (by rfl) ⟨2861567, by rfl⟩ : syracuseStep 3815423 = 5723135) B5723135
theorem B2543615 : Blo 1695548 2543615 := bstep (se 1 (by rfl) ⟨1907711, by rfl⟩ : syracuseStep 2543615 = 3815423) B3815423
theorem B1695743 : Blo 1695548 1695743 := bstep (se 1 (by rfl) ⟨1271807, by rfl⟩ : syracuseStep 1695743 = 2543615) B2543615

theorem C0 (j : ℕ) (h1 : 423887 ≤ j) (h2 : j ≤ 424386) : Blo 1695548 (4 * j + 3) := by
  interval_cases j
  · exact B1695551
  · exact B1695555
  · exact B1695559
  · exact B1695563
  · exact B1695567
  · exact B1695571
  · exact B1695575
  · exact B1695579
  · exact B1695583
  · exact B1695587
  · exact B1695591
  · exact B1695595
  · exact B1695599
  · exact B1695603
  · exact B1695607
  · exact B1695611
  · exact B1695615
  · exact B1695619
  · exact B1695623
  · exact B1695627
  · exact B1695631
  · exact B1695635
  · exact B1695639
  · exact B1695643
  · exact B1695647
  · exact B1695651
  · exact B1695655
  · exact B1695659
  · exact B1695663
  · exact B1695667
  · exact B1695671
  · exact B1695675
  · exact B1695679
  · exact B1695683
  · exact B1695687
  · exact B1695691
  · exact B1695695
  · exact B1695699
  · exact B1695703
  · exact B1695707
  · exact B1695711
  · exact B1695715
  · exact B1695719
  · exact B1695723
  · exact B1695727
  · exact B1695731
  · exact B1695735
  · exact B1695739
  · exact B1695743
  · exact B1695747
  · exact B1695751
  · exact B1695755
  · exact B1695759
  · exact B1695763
  · exact B1695767
  · exact B1695771
  · exact B1695775
  · exact B1695779
  · exact B1695783
  · exact B1695787
  · exact B1695791
  · exact B1695795
  · exact B1695799
  · exact B1695803
  · exact B1695807
  · exact B1695811
  · exact B1695815
  · exact B1695819
  · exact B1695823
  · exact B1695827
  · exact B1695831
  · exact B1695835
  · exact B1695839
  · exact B1695843
  · exact B1695847
  · exact B1695851
  · exact B1695855
  · exact B1695859
  · exact B1695863
  · exact B1695867
  · exact B1695871
  · exact B1695875
  · exact B1695879
  · exact B1695883
  · exact B1695887
  · exact B1695891
  · exact B1695895
  · exact B1695899
  · exact B1695903
  · exact B1695907
  · exact B1695911
  · exact B1695915
  · exact B1695919
  · exact B1695923
  · exact B1695927
  · exact B1695931
  · exact B1695935
  · exact B1695939
  · exact B1695943
  · exact B1695947
  · exact B1695951
  · exact B1695955
  · exact B1695959
  · exact B1695963
  · exact B1695967
  · exact B1695971
  · exact B1695975
  · exact B1695979
  · exact B1695983
  · exact B1695987
  · exact B1695991
  · exact B1695995
  · exact B1695999
  · exact B1696003
  · exact B1696007
  · exact B1696011
  · exact B1696015
  · exact B1696019
  · exact B1696023
  · exact B1696027
  · exact B1696031
  · exact B1696035
  · exact B1696039
  · exact B1696043
  · exact B1696047
  · exact B1696051
  · exact B1696055
  · exact B1696059
  · exact B1696063
  · exact B1696067
  · exact B1696071
  · exact B1696075
  · exact B1696079
  · exact B1696083
  · exact B1696087
  · exact B1696091
  · exact B1696095
  · exact B1696099
  · exact B1696103
  · exact B1696107
  · exact B1696111
  · exact B1696115
  · exact B1696119
  · exact B1696123
  · exact B1696127
  · exact B1696131
  · exact B1696135
  · exact B1696139
  · exact B1696143
  · exact B1696147
  · exact B1696151
  · exact B1696155
  · exact B1696159
  · exact B1696163
  · exact B1696167
  · exact B1696171
  · exact B1696175
  · exact B1696179
  · exact B1696183
  · exact B1696187
  · exact B1696191
  · exact B1696195
  · exact B1696199
  · exact B1696203
  · exact B1696207
  · exact B1696211
  · exact B1696215
  · exact B1696219
  · exact B1696223
  · exact B1696227
  · exact B1696231
  · exact B1696235
  · exact B1696239
  · exact B1696243
  · exact B1696247
  · exact B1696251
  · exact B1696255
  · exact B1696259
  · exact B1696263
  · exact B1696267
  · exact B1696271
  · exact B1696275
  · exact B1696279
  · exact B1696283
  · exact B1696287
  · exact B1696291
  · exact B1696295
  · exact B1696299
  · exact B1696303
  · exact B1696307
  · exact B1696311
  · exact B1696315
  · exact B1696319
  · exact B1696323
  · exact B1696327
  · exact B1696331
  · exact B1696335
  · exact B1696339
  · exact B1696343
  · exact B1696347
  · exact B1696351
  · exact B1696355
  · exact B1696359
  · exact B1696363
  · exact B1696367
  · exact B1696371
  · exact B1696375
  · exact B1696379
  · exact B1696383
  · exact B1696387
  · exact B1696391
  · exact B1696395
  · exact B1696399
  · exact B1696403
  · exact B1696407
  · exact B1696411
  · exact B1696415
  · exact B1696419
  · exact B1696423
  · exact B1696427
  · exact B1696431
  · exact B1696435
  · exact B1696439
  · exact B1696443
  · exact B1696447
  · exact B1696451
  · exact B1696455
  · exact B1696459
  · exact B1696463
  · exact B1696467
  · exact B1696471
  · exact B1696475
  · exact B1696479
  · exact B1696483
  · exact B1696487
  · exact B1696491
  · exact B1696495
  · exact B1696499
  · exact B1696503
  · exact B1696507
  · exact B1696511
  · exact B1696515
  · exact B1696519
  · exact B1696523
  · exact B1696527
  · exact B1696531
  · exact B1696535
  · exact B1696539
  · exact B1696543
  · exact B1696547
  · exact B1696551
  · exact B1696555
  · exact B1696559
  · exact B1696563
  · exact B1696567
  · exact B1696571
  · exact B1696575
  · exact B1696579
  · exact B1696583
  · exact B1696587
  · exact B1696591
  · exact B1696595
  · exact B1696599
  · exact B1696603
  · exact B1696607
  · exact B1696611
  · exact B1696615
  · exact B1696619
  · exact B1696623
  · exact B1696627
  · exact B1696631
  · exact B1696635
  · exact B1696639
  · exact B1696643
  · exact B1696647
  · exact B1696651
  · exact B1696655
  · exact B1696659
  · exact B1696663
  · exact B1696667
  · exact B1696671
  · exact B1696675
  · exact B1696679
  · exact B1696683
  · exact B1696687
  · exact B1696691
  · exact B1696695
  · exact B1696699
  · exact B1696703
  · exact B1696707
  · exact B1696711
  · exact B1696715
  · exact B1696719
  · exact B1696723
  · exact B1696727
  · exact B1696731
  · exact B1696735
  · exact B1696739
  · exact B1696743
  · exact B1696747
  · exact B1696751
  · exact B1696755
  · exact B1696759
  · exact B1696763
  · exact B1696767
  · exact B1696771
  · exact B1696775
  · exact B1696779
  · exact B1696783
  · exact B1696787
  · exact B1696791
  · exact B1696795
  · exact B1696799
  · exact B1696803
  · exact B1696807
  · exact B1696811
  · exact B1696815
  · exact B1696819
  · exact B1696823
  · exact B1696827
  · exact B1696831
  · exact B1696835
  · exact B1696839
  · exact B1696843
  · exact B1696847
  · exact B1696851
  · exact B1696855
  · exact B1696859
  · exact B1696863
  · exact B1696867
  · exact B1696871
  · exact B1696875
  · exact B1696879
  · exact B1696883
  · exact B1696887
  · exact B1696891
  · exact B1696895
  · exact B1696899
  · exact B1696903
  · exact B1696907
  · exact B1696911
  · exact B1696915
  · exact B1696919
  · exact B1696923
  · exact B1696927
  · exact B1696931
  · exact B1696935
  · exact B1696939
  · exact B1696943
  · exact B1696947
  · exact B1696951
  · exact B1696955
  · exact B1696959
  · exact B1696963
  · exact B1696967
  · exact B1696971
  · exact B1696975
  · exact B1696979
  · exact B1696983
  · exact B1696987
  · exact B1696991
  · exact B1696995
  · exact B1696999
  · exact B1697003
  · exact B1697007
  · exact B1697011
  · exact B1697015
  · exact B1697019
  · exact B1697023
  · exact B1697027
  · exact B1697031
  · exact B1697035
  · exact B1697039
  · exact B1697043
  · exact B1697047
  · exact B1697051
  · exact B1697055
  · exact B1697059
  · exact B1697063
  · exact B1697067
  · exact B1697071
  · exact B1697075
  · exact B1697079
  · exact B1697083
  · exact B1697087
  · exact B1697091
  · exact B1697095
  · exact B1697099
  · exact B1697103
  · exact B1697107
  · exact B1697111
  · exact B1697115
  · exact B1697119
  · exact B1697123
  · exact B1697127
  · exact B1697131
  · exact B1697135
  · exact B1697139
  · exact B1697143
  · exact B1697147
  · exact B1697151
  · exact B1697155
  · exact B1697159
  · exact B1697163
  · exact B1697167
  · exact B1697171
  · exact B1697175
  · exact B1697179
  · exact B1697183
  · exact B1697187
  · exact B1697191
  · exact B1697195
  · exact B1697199
  · exact B1697203
  · exact B1697207
  · exact B1697211
  · exact B1697215
  · exact B1697219
  · exact B1697223
  · exact B1697227
  · exact B1697231
  · exact B1697235
  · exact B1697239
  · exact B1697243
  · exact B1697247
  · exact B1697251
  · exact B1697255
  · exact B1697259
  · exact B1697263
  · exact B1697267
  · exact B1697271
  · exact B1697275
  · exact B1697279
  · exact B1697283
  · exact B1697287
  · exact B1697291
  · exact B1697295
  · exact B1697299
  · exact B1697303
  · exact B1697307
  · exact B1697311
  · exact B1697315
  · exact B1697319
  · exact B1697323
  · exact B1697327
  · exact B1697331
  · exact B1697335
  · exact B1697339
  · exact B1697343
  · exact B1697347
  · exact B1697351
  · exact B1697355
  · exact B1697359
  · exact B1697363
  · exact B1697367
  · exact B1697371
  · exact B1697375
  · exact B1697379
  · exact B1697383
  · exact B1697387
  · exact B1697391
  · exact B1697395
  · exact B1697399
  · exact B1697403
  · exact B1697407
  · exact B1697411
  · exact B1697415
  · exact B1697419
  · exact B1697423
  · exact B1697427
  · exact B1697431
  · exact B1697435
  · exact B1697439
  · exact B1697443
  · exact B1697447
  · exact B1697451
  · exact B1697455
  · exact B1697459
  · exact B1697463
  · exact B1697467
  · exact B1697471
  · exact B1697475
  · exact B1697479
  · exact B1697483
  · exact B1697487
  · exact B1697491
  · exact B1697495
  · exact B1697499
  · exact B1697503
  · exact B1697507
  · exact B1697511
  · exact B1697515
  · exact B1697519
  · exact B1697523
  · exact B1697527
  · exact B1697531
  · exact B1697535
  · exact B1697539
  · exact B1697543
  · exact B1697547

theorem solution (m : ℕ) (hlo : 1695548 ≤ m) (hhi : m ≤ 1697548) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 423887 ≤ j := by omega
    have hj2 : j ≤ 424386 := by omega
    have hb : Blo 1695548 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
