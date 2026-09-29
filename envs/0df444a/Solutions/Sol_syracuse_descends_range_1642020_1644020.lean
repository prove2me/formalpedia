-- Prove2me | solution 1 for syracuse_descends_range_1642020_1644020
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:16:23.033103+00:00
-- url     : https://prove2.me/submissions/4acda9d1-0e50-48cc-8fb9-ebcf510e4671

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


theorem B2465813 : Blo 1642020 2465813 := bbase (se 6 (by rfl) ⟨57792, by rfl⟩ : syracuseStep 2465813 = 115585) (by norm_num)
theorem B2465837 : Blo 1642020 2465837 := bbase (se 3 (by rfl) ⟨462344, by rfl⟩ : syracuseStep 2465837 = 924689) (by norm_num)
theorem B3694661 : Blo 1642020 3694661 := bbase (se 4 (by rfl) ⟨346374, by rfl⟩ : syracuseStep 3694661 = 692749) (by norm_num)
theorem B2465861 : Blo 1642020 2465861 := bbase (se 4 (by rfl) ⟨231174, by rfl⟩ : syracuseStep 2465861 = 462349) (by norm_num)
theorem B5546069 : Blo 1642020 5546069 := bbase (se 8 (by rfl) ⟨32496, by rfl⟩ : syracuseStep 5546069 = 64993) (by norm_num)
theorem B2465885 : Blo 1642020 2465885 := bbase (se 3 (by rfl) ⟨462353, by rfl⟩ : syracuseStep 2465885 = 924707) (by norm_num)
theorem B7897189 : Blo 1642020 7897189 := bbase (se 4 (by rfl) ⟨740361, by rfl⟩ : syracuseStep 7897189 = 1480723) (by norm_num)
theorem B2465909 : Blo 1642020 2465909 := bbase (se 5 (by rfl) ⟨115589, by rfl⟩ : syracuseStep 2465909 = 231179) (by norm_num)
theorem B3694733 : Blo 1642020 3694733 := bbase (se 3 (by rfl) ⟨692762, by rfl⟩ : syracuseStep 3694733 = 1385525) (by norm_num)
theorem B1974413 : Blo 1642020 1974413 := bbase (se 3 (by rfl) ⟨370202, by rfl⟩ : syracuseStep 1974413 = 740405) (by norm_num)
theorem B2465933 : Blo 1642020 2465933 := bbase (se 3 (by rfl) ⟨462362, by rfl⟩ : syracuseStep 2465933 = 924725) (by norm_num)
theorem B2465957 : Blo 1642020 2465957 := bbase (se 4 (by rfl) ⟨231183, by rfl⟩ : syracuseStep 2465957 = 462367) (by norm_num)
theorem B2465981 : Blo 1642020 2465981 := bbase (se 3 (by rfl) ⟨462371, by rfl⟩ : syracuseStep 2465981 = 924743) (by norm_num)
theorem B3694805 : Blo 1642020 3694805 := bbase (se 7 (by rfl) ⟨43298, by rfl⟩ : syracuseStep 3694805 = 86597) (by norm_num)
theorem B2466005 : Blo 1642020 2466005 := bbase (se 7 (by rfl) ⟨28898, by rfl⟩ : syracuseStep 2466005 = 57797) (by norm_num)
theorem B2466029 : Blo 1642020 2466029 := bbase (se 3 (by rfl) ⟨462380, by rfl⟩ : syracuseStep 2466029 = 924761) (by norm_num)
theorem B3694877 : Blo 1642020 3694877 := bbase (se 3 (by rfl) ⟨692789, by rfl⟩ : syracuseStep 3694877 = 1385579) (by norm_num)
theorem B4677925 : Blo 1642020 4677925 := bbase (se 4 (by rfl) ⟨438555, by rfl⟩ : syracuseStep 4677925 = 877111) (by norm_num)
theorem B3694949 : Blo 1642020 3694949 := bbase (se 4 (by rfl) ⟨346401, by rfl⟩ : syracuseStep 3694949 = 692803) (by norm_num)
theorem B3695021 : Blo 1642020 3695021 := bbase (se 3 (by rfl) ⟨692816, by rfl⟩ : syracuseStep 3695021 = 1385633) (by norm_num)
theorem B1974721 : Blo 1642020 1974721 := bbase (se 2 (by rfl) ⟨740520, by rfl⟩ : syracuseStep 1974721 = 1481041) (by norm_num)
theorem B3695093 : Blo 1642020 3695093 := bbase (se 5 (by rfl) ⟨173207, by rfl⟩ : syracuseStep 3695093 = 346415) (by norm_num)
theorem B5546501 : Blo 1642020 5546501 := bbase (se 4 (by rfl) ⟨519984, by rfl⟩ : syracuseStep 5546501 = 1039969) (by norm_num)
theorem B1974817 : Blo 1642020 1974817 := bbase (se 2 (by rfl) ⟨740556, by rfl⟩ : syracuseStep 1974817 = 1481113) (by norm_num)
theorem B3695165 : Blo 1642020 3695165 := bbase (se 3 (by rfl) ⟨692843, by rfl⟩ : syracuseStep 3695165 = 1385687) (by norm_num)
theorem B1753697 : Blo 1642020 1753697 := bbase (se 2 (by rfl) ⟨657636, by rfl⟩ : syracuseStep 1753697 = 1315273) (by norm_num)
theorem B3695237 : Blo 1642020 3695237 := bbase (se 4 (by rfl) ⟨346428, by rfl⟩ : syracuseStep 3695237 = 692857) (by norm_num)
theorem B12477077 : Blo 1642020 12477077 := bbase (se 6 (by rfl) ⟨292431, by rfl⟩ : syracuseStep 12477077 = 584863) (by norm_num)
theorem B1753769 : Blo 1642020 1753769 := bbase (se 2 (by rfl) ⟨657663, by rfl⟩ : syracuseStep 1753769 = 1315327) (by norm_num)
theorem B3695309 : Blo 1642020 3695309 := bbase (se 3 (by rfl) ⟨692870, by rfl⟩ : syracuseStep 3695309 = 1385741) (by norm_num)
theorem B24011477 : Blo 1642020 24011477 := bbase (se 7 (by rfl) ⟨281384, by rfl⟩ : syracuseStep 24011477 = 562769) (by norm_num)
theorem B8315621 : Blo 1642020 8315621 := bbase (se 4 (by rfl) ⟨779589, by rfl⟩ : syracuseStep 8315621 = 1559179) (by norm_num)
theorem B3695381 : Blo 1642020 3695381 := bbase (se 6 (by rfl) ⟨86610, by rfl⟩ : syracuseStep 3695381 = 173221) (by norm_num)
theorem B7021349 : Blo 1642020 7021349 := bbase (se 4 (by rfl) ⟨658251, by rfl⟩ : syracuseStep 7021349 = 1316503) (by norm_num)
theorem B3695453 : Blo 1642020 3695453 := bbase (se 3 (by rfl) ⟨692897, by rfl⟩ : syracuseStep 3695453 = 1385795) (by norm_num)
theorem B1753957 : Blo 1642020 1753957 := bbase (se 4 (by rfl) ⟨164433, by rfl⟩ : syracuseStep 1753957 = 328867) (by norm_num)
theorem B2532197 : Blo 1642020 2532197 := bbase (se 4 (by rfl) ⟨237393, by rfl⟩ : syracuseStep 2532197 = 474787) (by norm_num)
theorem B3507077 : Blo 1642020 3507077 := bbase (se 4 (by rfl) ⟨328788, by rfl⟩ : syracuseStep 3507077 = 657577) (by norm_num)
theorem B3695525 : Blo 1642020 3695525 := bbase (se 4 (by rfl) ⟨346455, by rfl⟩ : syracuseStep 3695525 = 692911) (by norm_num)
theorem B5546933 : Blo 1642020 5546933 := bbase (se 5 (by rfl) ⟨260012, by rfl⟩ : syracuseStep 5546933 = 520025) (by norm_num)
theorem B3949517 : Blo 1642020 3949517 := bbase (se 3 (by rfl) ⟨740534, by rfl⟩ : syracuseStep 3949517 = 1481069) (by norm_num)
theorem B3695597 : Blo 1642020 3695597 := bbase (se 3 (by rfl) ⟨692924, by rfl⟩ : syracuseStep 3695597 = 1385849) (by norm_num)
theorem B1754141 : Blo 1642020 1754141 := bbase (se 3 (by rfl) ⟨328901, by rfl⟩ : syracuseStep 1754141 = 657803) (by norm_num)
theorem B12469301 : Blo 1642020 12469301 := bbase (se 5 (by rfl) ⟨584498, by rfl⟩ : syracuseStep 12469301 = 1168997) (by norm_num)
theorem B3695669 : Blo 1642020 3695669 := bbase (se 5 (by rfl) ⟨173234, by rfl⟩ : syracuseStep 3695669 = 346469) (by norm_num)
theorem B7021637 : Blo 1642020 7021637 := bbase (se 4 (by rfl) ⟨658278, by rfl⟩ : syracuseStep 7021637 = 1316557) (by norm_num)
theorem B3695741 : Blo 1642020 3695741 := bbase (se 3 (by rfl) ⟨692951, by rfl⟩ : syracuseStep 3695741 = 1385903) (by norm_num)
theorem B2630821 : Blo 1642020 2630821 := bbase (se 4 (by rfl) ⟨246639, by rfl⟩ : syracuseStep 2630821 = 493279) (by norm_num)
theorem B3695813 : Blo 1642020 3695813 := bbase (se 4 (by rfl) ⟨346482, by rfl⟩ : syracuseStep 3695813 = 692965) (by norm_num)
theorem B2221301 : Blo 1642020 2221301 := bbase (se 5 (by rfl) ⟨104123, by rfl⟩ : syracuseStep 2221301 = 208247) (by norm_num)
theorem B3695885 : Blo 1642020 3695885 := bbase (se 3 (by rfl) ⟨692978, by rfl⟩ : syracuseStep 3695885 = 1385957) (by norm_num)
theorem B2106653 : Blo 1642020 2106653 := bbase (se 3 (by rfl) ⟨394997, by rfl⟩ : syracuseStep 2106653 = 789995) (by norm_num)
theorem B3695957 : Blo 1642020 3695957 := bbase (se 12 (by rfl) ⟨1353, by rfl⟩ : syracuseStep 3695957 = 2707) (by norm_num)
theorem B5547365 : Blo 1642020 5547365 := bbase (se 4 (by rfl) ⟨520065, by rfl⟩ : syracuseStep 5547365 = 1040131) (by norm_num)
theorem B2106757 : Blo 1642020 2106757 := bbase (se 4 (by rfl) ⟨197508, by rfl⟩ : syracuseStep 2106757 = 395017) (by norm_num)
theorem B4441477 : Blo 1642020 4441477 := bbase (se 4 (by rfl) ⟨416388, by rfl⟩ : syracuseStep 4441477 = 832777) (by norm_num)
theorem B3696029 : Blo 1642020 3696029 := bbase (se 3 (by rfl) ⟨693005, by rfl⟩ : syracuseStep 3696029 = 1386011) (by norm_num)
theorem B3696101 : Blo 1642020 3696101 := bbase (se 4 (by rfl) ⟨346509, by rfl⟩ : syracuseStep 3696101 = 693019) (by norm_num)
theorem B3696173 : Blo 1642020 3696173 := bbase (se 3 (by rfl) ⟨693032, by rfl⟩ : syracuseStep 3696173 = 1386065) (by norm_num)
theorem B5064245 : Blo 1642020 5064245 := bbase (se 5 (by rfl) ⟨237386, by rfl⟩ : syracuseStep 5064245 = 474773) (by norm_num)
theorem B2631269 : Blo 1642020 2631269 := bbase (se 4 (by rfl) ⟨246681, by rfl⟩ : syracuseStep 2631269 = 493363) (by norm_num)
theorem B3696245 : Blo 1642020 3696245 := bbase (se 5 (by rfl) ⟨173261, by rfl⟩ : syracuseStep 3696245 = 346523) (by norm_num)
theorem B2000533 : Blo 1642020 2000533 := bbase (se 6 (by rfl) ⟨46887, by rfl⟩ : syracuseStep 2000533 = 93775) (by norm_num)
theorem B9995957 : Blo 1642020 9995957 := bbase (se 5 (by rfl) ⟨468560, by rfl⟩ : syracuseStep 9995957 = 937121) (by norm_num)
theorem B3696317 : Blo 1642020 3696317 := bbase (se 3 (by rfl) ⟨693059, by rfl⟩ : syracuseStep 3696317 = 1386119) (by norm_num)
theorem B3507941 : Blo 1642020 3507941 := bbase (se 4 (by rfl) ⟨328869, by rfl⟩ : syracuseStep 3507941 = 657739) (by norm_num)
theorem B3696389 : Blo 1642020 3696389 := bbase (se 4 (by rfl) ⟨346536, by rfl⟩ : syracuseStep 3696389 = 693073) (by norm_num)
theorem B1754893 : Blo 1642020 1754893 := bbase (se 3 (by rfl) ⟨329042, by rfl⟩ : syracuseStep 1754893 = 658085) (by norm_num)
theorem B5547797 : Blo 1642020 5547797 := bbase (se 6 (by rfl) ⟨130026, by rfl⟩ : syracuseStep 5547797 = 260053) (by norm_num)
theorem B2811677 : Blo 1642020 2811677 := bbase (se 3 (by rfl) ⟨527189, by rfl⟩ : syracuseStep 2811677 = 1054379) (by norm_num)
theorem B7022389 : Blo 1642020 7022389 := bbase (se 5 (by rfl) ⟨329174, by rfl⟩ : syracuseStep 7022389 = 658349) (by norm_num)
theorem B6235973 : Blo 1642020 6235973 := bbase (se 4 (by rfl) ⟨584622, by rfl⟩ : syracuseStep 6235973 = 1169245) (by norm_num)
theorem B3696461 : Blo 1642020 3696461 := bbase (se 3 (by rfl) ⟨693086, by rfl⟩ : syracuseStep 3696461 = 1386173) (by norm_num)
theorem B1754965 : Blo 1642020 1754965 := bbase (se 9 (by rfl) ⟨5141, by rfl⟩ : syracuseStep 1754965 = 10283) (by norm_num)
theorem B2959213 : Blo 1642020 2959213 := bbase (se 3 (by rfl) ⟨554852, by rfl⟩ : syracuseStep 2959213 = 1109705) (by norm_num)
theorem B3508085 : Blo 1642020 3508085 := bbase (se 5 (by rfl) ⟨164441, by rfl⟩ : syracuseStep 3508085 = 328883) (by norm_num)
theorem B1664905 : Blo 1642020 1664905 := bbase (se 2 (by rfl) ⟨624339, by rfl⟩ : syracuseStep 1664905 = 1248679) (by norm_num)
theorem B3696533 : Blo 1642020 3696533 := bbase (se 6 (by rfl) ⟨86637, by rfl⟩ : syracuseStep 3696533 = 173275) (by norm_num)
theorem B14034869 : Blo 1642020 14034869 := bbase (se 5 (by rfl) ⟨657884, by rfl⟩ : syracuseStep 14034869 = 1315769) (by norm_num)
theorem B3696605 : Blo 1642020 3696605 := bbase (se 3 (by rfl) ⟨693113, by rfl⟩ : syracuseStep 3696605 = 1386227) (by norm_num)
theorem B8316917 : Blo 1642020 8316917 := bbase (se 5 (by rfl) ⟨389855, by rfl⟩ : syracuseStep 8316917 = 779711) (by norm_num)
theorem B2770949 : Blo 1642020 2770949 := bbase (se 4 (by rfl) ⟨259776, by rfl⟩ : syracuseStep 2770949 = 519553) (by norm_num)
theorem B1755145 : Blo 1642020 1755145 := bbase (se 2 (by rfl) ⟨658179, by rfl⟩ : syracuseStep 1755145 = 1316359) (by norm_num)
theorem B3696677 : Blo 1642020 3696677 := bbase (se 4 (by rfl) ⟨346563, by rfl⟩ : syracuseStep 3696677 = 693127) (by norm_num)
theorem B2959421 : Blo 1642020 2959421 := bbase (se 3 (by rfl) ⟨554891, by rfl⟩ : syracuseStep 2959421 = 1109783) (by norm_num)
theorem B2959429 : Blo 1642020 2959429 := bbase (se 4 (by rfl) ⟨277446, by rfl⟩ : syracuseStep 2959429 = 554893) (by norm_num)
theorem B6236261 : Blo 1642020 6236261 := bbase (se 4 (by rfl) ⟨584649, by rfl⟩ : syracuseStep 6236261 = 1169299) (by norm_num)
theorem B3696749 : Blo 1642020 3696749 := bbase (se 3 (by rfl) ⟨693140, by rfl⟩ : syracuseStep 3696749 = 1386281) (by norm_num)
theorem B2771077 : Blo 1642020 2771077 := bbase (se 4 (by rfl) ⟨259788, by rfl⟩ : syracuseStep 2771077 = 519577) (by norm_num)
theorem B3696821 : Blo 1642020 3696821 := bbase (se 5 (by rfl) ⟨173288, by rfl⟩ : syracuseStep 3696821 = 346577) (by norm_num)
theorem B5548229 : Blo 1642020 5548229 := bbase (se 4 (by rfl) ⟨520146, by rfl⟩ : syracuseStep 5548229 = 1040293) (by norm_num)
theorem B2959573 : Blo 1642020 2959573 := bbase (se 7 (by rfl) ⟨34682, by rfl⟩ : syracuseStep 2959573 = 69365) (by norm_num)
theorem B2771165 : Blo 1642020 2771165 := bbase (se 3 (by rfl) ⟨519593, by rfl⟩ : syracuseStep 2771165 = 1039187) (by norm_num)
theorem B3696893 : Blo 1642020 3696893 := bbase (se 3 (by rfl) ⟨693167, by rfl⟩ : syracuseStep 3696893 = 1386335) (by norm_num)
theorem B3557629 : Blo 1642020 3557629 := bbase (se 3 (by rfl) ⟨667055, by rfl⟩ : syracuseStep 3557629 = 1334111) (by norm_num)
theorem B5335301 : Blo 1642020 5335301 := bbase (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) (by norm_num)
theorem B3696965 : Blo 1642020 3696965 := bbase (se 4 (by rfl) ⟨346590, by rfl⟩ : syracuseStep 3696965 = 693181) (by norm_num)
theorem B2771293 : Blo 1642020 2771293 := bbase (se 3 (by rfl) ⟨519617, by rfl⟩ : syracuseStep 2771293 = 1039235) (by norm_num)
theorem B3697037 : Blo 1642020 3697037 := bbase (se 3 (by rfl) ⟨693194, by rfl⟩ : syracuseStep 3697037 = 1386389) (by norm_num)
theorem B5261717 : Blo 1642020 5261717 := bbase (se 6 (by rfl) ⟨123321, by rfl⟩ : syracuseStep 5261717 = 246643) (by norm_num)
theorem B2771381 : Blo 1642020 2771381 := bbase (se 5 (by rfl) ⟨129908, by rfl⟩ : syracuseStep 2771381 = 259817) (by norm_num)
theorem B1755589 : Blo 1642020 1755589 := bbase (se 4 (by rfl) ⟨164586, by rfl⟩ : syracuseStep 1755589 = 329173) (by norm_num)
theorem B3697109 : Blo 1642020 3697109 := bbase (se 7 (by rfl) ⟨43325, by rfl⟩ : syracuseStep 3697109 = 86651) (by norm_num)
theorem B4270589 : Blo 1642020 4270589 := bbase (se 3 (by rfl) ⟨800735, by rfl⟩ : syracuseStep 4270589 = 1601471) (by norm_num)
theorem B3697181 : Blo 1642020 3697181 := bbase (se 3 (by rfl) ⟨693221, by rfl⟩ : syracuseStep 3697181 = 1386443) (by norm_num)
theorem B2771509 : Blo 1642020 2771509 := bbase (se 5 (by rfl) ⟨129914, by rfl⟩ : syracuseStep 2771509 = 259829) (by norm_num)
theorem B3508829 : Blo 1642020 3508829 := bbase (se 3 (by rfl) ⟨657905, by rfl⟩ : syracuseStep 3508829 = 1315811) (by norm_num)
theorem B3697253 : Blo 1642020 3697253 := bbase (se 4 (by rfl) ⟨346617, by rfl⟩ : syracuseStep 3697253 = 693235) (by norm_num)
theorem B2771597 : Blo 1642020 2771597 := bbase (se 3 (by rfl) ⟨519674, by rfl⟩ : syracuseStep 2771597 = 1039349) (by norm_num)
theorem B3697325 : Blo 1642020 3697325 := bbase (se 3 (by rfl) ⟨693248, by rfl⟩ : syracuseStep 3697325 = 1386497) (by norm_num)
theorem B9358037 : Blo 1642020 9358037 := bbase (se 7 (by rfl) ⟨109664, by rfl⟩ : syracuseStep 9358037 = 219329) (by norm_num)
theorem B3697397 : Blo 1642020 3697397 := bbase (se 5 (by rfl) ⟨173315, by rfl⟩ : syracuseStep 3697397 = 346631) (by norm_num)
theorem B2771725 : Blo 1642020 2771725 := bbase (se 3 (by rfl) ⟨519698, by rfl⟩ : syracuseStep 2771725 = 1039397) (by norm_num)
theorem B3697469 : Blo 1642020 3697469 := bbase (se 3 (by rfl) ⟨693275, by rfl⟩ : syracuseStep 3697469 = 1386551) (by norm_num)
theorem B18713429 : Blo 1642020 18713429 := bbase (se 9 (by rfl) ⟨54824, by rfl⟩ : syracuseStep 18713429 = 109649) (by norm_num)
theorem B2771813 : Blo 1642020 2771813 := bbase (se 4 (by rfl) ⟨259857, by rfl⟩ : syracuseStep 2771813 = 519715) (by norm_num)
theorem B3697541 : Blo 1642020 3697541 := bbase (se 4 (by rfl) ⟨346644, by rfl⟩ : syracuseStep 3697541 = 693289) (by norm_num)
theorem B7900037 : Blo 1642020 7900037 := bbase (se 4 (by rfl) ⟨740628, by rfl⟩ : syracuseStep 7900037 = 1481257) (by norm_num)
theorem B2960293 : Blo 1642020 2960293 := bbase (se 4 (by rfl) ⟨277527, by rfl⟩ : syracuseStep 2960293 = 555055) (by norm_num)
theorem B7015349 : Blo 1642020 7015349 := bbase (se 5 (by rfl) ⟨328844, by rfl⟩ : syracuseStep 7015349 = 657689) (by norm_num)
theorem B12643253 : Blo 1642020 12643253 := bbase (se 5 (by rfl) ⟨592652, by rfl⟩ : syracuseStep 12643253 = 1185305) (by norm_num)
theorem B3697613 : Blo 1642020 3697613 := bbase (se 3 (by rfl) ⟨693302, by rfl⟩ : syracuseStep 3697613 = 1386605) (by norm_num)
theorem B4156373 : Blo 1642020 4156373 := bbase (se 7 (by rfl) ⟨48707, by rfl⟩ : syracuseStep 4156373 = 97415) (by norm_num)
theorem B2771941 : Blo 1642020 2771941 := bbase (se 4 (by rfl) ⟨259869, by rfl⟩ : syracuseStep 2771941 = 519739) (by norm_num)
theorem B10521589 : Blo 1642020 10521589 := bbase (se 5 (by rfl) ⟨493199, by rfl⟩ : syracuseStep 10521589 = 986399) (by norm_num)
theorem B2960381 : Blo 1642020 2960381 := bbase (se 3 (by rfl) ⟨555071, by rfl⟩ : syracuseStep 2960381 = 1110143) (by norm_num)
theorem B1666049 : Blo 1642020 1666049 := bbase (se 2 (by rfl) ⟨624768, by rfl⟩ : syracuseStep 1666049 = 1249537) (by norm_num)
theorem B3697685 : Blo 1642020 3697685 := bbase (se 6 (by rfl) ⟨86664, by rfl⟩ : syracuseStep 3697685 = 173329) (by norm_num)
theorem B1666073 : Blo 1642020 1666073 := bbase (se 2 (by rfl) ⟨624777, by rfl⟩ : syracuseStep 1666073 = 1249555) (by norm_num)
theorem B2772029 : Blo 1642020 2772029 := bbase (se 3 (by rfl) ⟨519755, by rfl⟩ : syracuseStep 2772029 = 1039511) (by norm_num)
theorem B4680773 : Blo 1642020 4680773 := bbase (se 4 (by rfl) ⟨438822, by rfl⟩ : syracuseStep 4680773 = 877645) (by norm_num)
theorem B2632781 : Blo 1642020 2632781 := bbase (se 3 (by rfl) ⟨493646, by rfl⟩ : syracuseStep 2632781 = 987293) (by norm_num)
theorem B3697757 : Blo 1642020 3697757 := bbase (se 3 (by rfl) ⟨693329, by rfl⟩ : syracuseStep 3697757 = 1386659) (by norm_num)
theorem B3697829 : Blo 1642020 3697829 := bbase (se 4 (by rfl) ⟨346671, by rfl⟩ : syracuseStep 3697829 = 693343) (by norm_num)
theorem B2772157 : Blo 1642020 2772157 := bbase (se 3 (by rfl) ⟨519779, by rfl⟩ : syracuseStep 2772157 = 1039559) (by norm_num)
theorem B2632909 : Blo 1642020 2632909 := bbase (se 3 (by rfl) ⟨493670, by rfl⟩ : syracuseStep 2632909 = 987341) (by norm_num)
theorem B3697901 : Blo 1642020 3697901 := bbase (se 3 (by rfl) ⟨693356, by rfl⟩ : syracuseStep 3697901 = 1386713) (by norm_num)
theorem B2465789 : Blo 1642020 2465789 := bbase (se 3 (by rfl) ⟨462335, by rfl⟩ : syracuseStep 2465789 = 924671) (by norm_num)
theorem B2313461 : Blo 1642020 2313461 := bbase (se 5 (by rfl) ⟨108443, by rfl⟩ : syracuseStep 2313461 = 216887) (by norm_num)
theorem B6237445 : Blo 1642020 6237445 := bbase (se 4 (by rfl) ⟨584760, by rfl⟩ : syracuseStep 6237445 = 1169521) (by norm_num)
theorem B8318213 : Blo 1642020 8318213 := bbase (se 4 (by rfl) ⟨779832, by rfl⟩ : syracuseStep 8318213 = 1559665) (by norm_num)
theorem B2772245 : Blo 1642020 2772245 := bbase (se 6 (by rfl) ⟨64974, by rfl⟩ : syracuseStep 2772245 = 129949) (by norm_num)
theorem B1666333 : Blo 1642020 1666333 := bbase (se 3 (by rfl) ⟨312437, by rfl⟩ : syracuseStep 1666333 = 624875) (by norm_num)
theorem B4156717 : Blo 1642020 4156717 := bbase (se 3 (by rfl) ⟨779384, by rfl⟩ : syracuseStep 4156717 = 1558769) (by norm_num)
theorem B3697973 : Blo 1642020 3697973 := bbase (se 5 (by rfl) ⟨173342, by rfl⟩ : syracuseStep 3697973 = 346685) (by norm_num)
theorem B3509581 : Blo 1642020 3509581 := bbase (se 3 (by rfl) ⟨658046, by rfl⟩ : syracuseStep 3509581 = 1316093) (by norm_num)
theorem B3796325 : Blo 1642020 3796325 := bbase (se 4 (by rfl) ⟨355905, by rfl⟩ : syracuseStep 3796325 = 711811) (by norm_num)
theorem B3698045 : Blo 1642020 3698045 := bbase (se 3 (by rfl) ⟨693383, by rfl⟩ : syracuseStep 3698045 = 1386767) (by norm_num)
theorem B2772373 : Blo 1642020 2772373 := bbase (se 6 (by rfl) ⟨64977, by rfl⟩ : syracuseStep 2772373 = 129955) (by norm_num)
theorem B4156829 : Blo 1642020 4156829 := bbase (se 3 (by rfl) ⟨779405, by rfl⟩ : syracuseStep 4156829 = 1558811) (by norm_num)
theorem B2960813 : Blo 1642020 2960813 := bbase (se 3 (by rfl) ⟨555152, by rfl⟩ : syracuseStep 2960813 = 1110305) (by norm_num)
theorem B3698117 : Blo 1642020 3698117 := bbase (se 4 (by rfl) ⟨346698, by rfl⟩ : syracuseStep 3698117 = 693397) (by norm_num)
theorem B3509725 : Blo 1642020 3509725 := bbase (se 3 (by rfl) ⟨658073, by rfl⟩ : syracuseStep 3509725 = 1316147) (by norm_num)
theorem B5336549 : Blo 1642020 5336549 := bbase (se 4 (by rfl) ⟨500301, by rfl⟩ : syracuseStep 5336549 = 1000603) (by norm_num)
theorem B2772461 : Blo 1642020 2772461 := bbase (se 3 (by rfl) ⟨519836, by rfl⟩ : syracuseStep 2772461 = 1039673) (by norm_num)
theorem B3698189 : Blo 1642020 3698189 := bbase (se 3 (by rfl) ⟨693410, by rfl⟩ : syracuseStep 3698189 = 1386821) (by norm_num)
theorem B6237749 : Blo 1642020 6237749 := bbase (se 5 (by rfl) ⟨292394, by rfl⟩ : syracuseStep 6237749 = 584789) (by norm_num)
theorem B4574773 : Blo 1642020 4574773 := bbase (se 5 (by rfl) ⟨214442, by rfl⟩ : syracuseStep 4574773 = 428885) (by norm_num)
theorem B2960957 : Blo 1642020 2960957 := bbase (se 3 (by rfl) ⟨555179, by rfl⟩ : syracuseStep 2960957 = 1110359) (by norm_num)
theorem B3698261 : Blo 1642020 3698261 := bbase (se 8 (by rfl) ⟨21669, by rfl⟩ : syracuseStep 3698261 = 43339) (by norm_num)
theorem B4157021 : Blo 1642020 4157021 := bbase (se 3 (by rfl) ⟨779441, by rfl⟩ : syracuseStep 4157021 = 1558883) (by norm_num)
theorem B2772589 : Blo 1642020 2772589 := bbase (se 3 (by rfl) ⟨519860, by rfl⟩ : syracuseStep 2772589 = 1039721) (by norm_num)
theorem B3698333 : Blo 1642020 3698333 := bbase (se 3 (by rfl) ⟨693437, by rfl⟩ : syracuseStep 3698333 = 1386875) (by norm_num)
theorem B2772677 : Blo 1642020 2772677 := bbase (se 4 (by rfl) ⟨259938, by rfl⟩ : syracuseStep 2772677 = 519877) (by norm_num)
theorem B3698405 : Blo 1642020 3698405 := bbase (se 4 (by rfl) ⟨346725, by rfl⟩ : syracuseStep 3698405 = 693451) (by norm_num)
theorem B2961173 : Blo 1642020 2961173 := bbase (se 6 (by rfl) ⟨69402, by rfl⟩ : syracuseStep 2961173 = 138805) (by norm_num)
theorem B3698477 : Blo 1642020 3698477 := bbase (se 3 (by rfl) ⟨693464, by rfl⟩ : syracuseStep 3698477 = 1386929) (by norm_num)
theorem B2772805 : Blo 1642020 2772805 := bbase (se 4 (by rfl) ⟨259950, by rfl⟩ : syracuseStep 2772805 = 519901) (by norm_num)
theorem B3329869 : Blo 1642020 3329869 := bbase (se 3 (by rfl) ⟨624350, by rfl⟩ : syracuseStep 3329869 = 1248701) (by norm_num)
theorem B17764181 : Blo 1642020 17764181 := bbase (se 9 (by rfl) ⟨52043, by rfl⟩ : syracuseStep 17764181 = 104087) (by norm_num)
theorem B3510101 : Blo 1642020 3510101 := bbase (se 9 (by rfl) ⟨10283, by rfl⟩ : syracuseStep 3510101 = 20567) (by norm_num)
theorem B3698549 : Blo 1642020 3698549 := bbase (se 5 (by rfl) ⟨173369, by rfl⟩ : syracuseStep 3698549 = 346739) (by norm_num)
theorem B7016341 : Blo 1642020 7016341 := bbase (se 6 (by rfl) ⟨164445, by rfl⟩ : syracuseStep 7016341 = 328891) (by norm_num)
theorem B2772893 : Blo 1642020 2772893 := bbase (se 3 (by rfl) ⟨519917, by rfl⟩ : syracuseStep 2772893 = 1039835) (by norm_num)
theorem B4157365 : Blo 1642020 4157365 := bbase (se 5 (by rfl) ⟨194876, by rfl⟩ : syracuseStep 4157365 = 389753) (by norm_num)
theorem B3698621 : Blo 1642020 3698621 := bbase (se 3 (by rfl) ⟨693491, by rfl⟩ : syracuseStep 3698621 = 1386983) (by norm_num)
theorem B1847281 : Blo 1642020 1847281 := bbase (se 2 (by rfl) ⟨692730, by rfl⟩ : syracuseStep 1847281 = 1385461) (by norm_num)
theorem B3698693 : Blo 1642020 3698693 := bbase (se 4 (by rfl) ⟨346752, by rfl⟩ : syracuseStep 3698693 = 693505) (by norm_num)
theorem B1847317 : Blo 1642020 1847317 := bbase (se 6 (by rfl) ⟨43296, by rfl⟩ : syracuseStep 1847317 = 86593) (by norm_num)
theorem B2773021 : Blo 1642020 2773021 := bbase (se 3 (by rfl) ⟨519941, by rfl⟩ : syracuseStep 2773021 = 1039883) (by norm_num)
theorem B4157477 : Blo 1642020 4157477 := bbase (se 4 (by rfl) ⟨389763, by rfl⟩ : syracuseStep 4157477 = 779527) (by norm_num)
theorem B7491637 : Blo 1642020 7491637 := bbase (se 5 (by rfl) ⟨351170, by rfl⟩ : syracuseStep 7491637 = 702341) (by norm_num)
theorem B1847353 : Blo 1642020 1847353 := bbase (se 2 (by rfl) ⟨692757, by rfl⟩ : syracuseStep 1847353 = 1385515) (by norm_num)
theorem B3698765 : Blo 1642020 3698765 := bbase (se 3 (by rfl) ⟨693518, by rfl⟩ : syracuseStep 3698765 = 1387037) (by norm_num)
theorem B1847389 : Blo 1642020 1847389 := bbase (se 3 (by rfl) ⟨346385, by rfl⟩ : syracuseStep 1847389 = 692771) (by norm_num)
theorem B2773109 : Blo 1642020 2773109 := bbase (se 5 (by rfl) ⟨129989, by rfl⟩ : syracuseStep 2773109 = 259979) (by norm_num)
theorem B1847425 : Blo 1642020 1847425 := bbase (se 2 (by rfl) ⟨692784, by rfl⟩ : syracuseStep 1847425 = 1385569) (by norm_num)
theorem B3698837 : Blo 1642020 3698837 := bbase (se 6 (by rfl) ⟨86691, by rfl⟩ : syracuseStep 3698837 = 173383) (by norm_num)
theorem B1847461 : Blo 1642020 1847461 := bbase (se 4 (by rfl) ⟨173199, by rfl⟩ : syracuseStep 1847461 = 346399) (by norm_num)
theorem B3510469 : Blo 1642020 3510469 := bbase (se 4 (by rfl) ⟨329106, by rfl⟩ : syracuseStep 3510469 = 658213) (by norm_num)
theorem B1847497 : Blo 1642020 1847497 := bbase (se 2 (by rfl) ⟨692811, by rfl⟩ : syracuseStep 1847497 = 1385623) (by norm_num)
theorem B3698909 : Blo 1642020 3698909 := bbase (se 3 (by rfl) ⟨693545, by rfl⟩ : syracuseStep 3698909 = 1387091) (by norm_num)
theorem B4157669 : Blo 1642020 4157669 := bbase (se 4 (by rfl) ⟨389781, by rfl⟩ : syracuseStep 4157669 = 779563) (by norm_num)
theorem B1847533 : Blo 1642020 1847533 := bbase (se 3 (by rfl) ⟨346412, by rfl⟩ : syracuseStep 1847533 = 692825) (by norm_num)
theorem B2773237 : Blo 1642020 2773237 := bbase (se 5 (by rfl) ⟨129995, by rfl⟩ : syracuseStep 2773237 = 259991) (by norm_num)
theorem B1847569 : Blo 1642020 1847569 := bbase (se 2 (by rfl) ⟨692838, by rfl⟩ : syracuseStep 1847569 = 1385677) (by norm_num)
theorem B3117341 : Blo 1642020 3117341 := bbase (se 3 (by rfl) ⟨584501, by rfl⟩ : syracuseStep 3117341 = 1169003) (by norm_num)
theorem B5542181 : Blo 1642020 5542181 := bbase (se 4 (by rfl) ⟨519579, by rfl⟩ : syracuseStep 5542181 = 1039159) (by norm_num)
theorem B3698981 : Blo 1642020 3698981 := bbase (se 4 (by rfl) ⟨346779, by rfl⟩ : syracuseStep 3698981 = 693559) (by norm_num)
theorem B1847605 : Blo 1642020 1847605 := bbase (se 5 (by rfl) ⟨86606, by rfl⟩ : syracuseStep 1847605 = 173213) (by norm_num)
theorem B2773325 : Blo 1642020 2773325 := bbase (se 3 (by rfl) ⟨519998, by rfl⟩ : syracuseStep 2773325 = 1039997) (by norm_num)
theorem B1847641 : Blo 1642020 1847641 := bbase (se 2 (by rfl) ⟨692865, by rfl⟩ : syracuseStep 1847641 = 1385731) (by norm_num)
theorem B5263717 : Blo 1642020 5263717 := bbase (se 4 (by rfl) ⟨493473, by rfl⟩ : syracuseStep 5263717 = 986947) (by norm_num)
theorem B1847677 : Blo 1642020 1847677 := bbase (se 3 (by rfl) ⟨346439, by rfl⟩ : syracuseStep 1847677 = 692879) (by norm_num)
theorem B1847713 : Blo 1642020 1847713 := bbase (se 2 (by rfl) ⟨692892, by rfl⟩ : syracuseStep 1847713 = 1385785) (by norm_num)
theorem B1847749 : Blo 1642020 1847749 := bbase (se 4 (by rfl) ⟨173226, by rfl⟩ : syracuseStep 1847749 = 346453) (by norm_num)
theorem B2773453 : Blo 1642020 2773453 := bbase (se 3 (by rfl) ⟨520022, by rfl⟩ : syracuseStep 2773453 = 1040045) (by norm_num)
theorem B2339293 : Blo 1642020 2339293 := bbase (se 3 (by rfl) ⟨438617, by rfl⟩ : syracuseStep 2339293 = 877235) (by norm_num)
theorem B1847785 : Blo 1642020 1847785 := bbase (se 2 (by rfl) ⟨692919, by rfl⟩ : syracuseStep 1847785 = 1385839) (by norm_num)
theorem B1847821 : Blo 1642020 1847821 := bbase (se 3 (by rfl) ⟨346466, by rfl⟩ : syracuseStep 1847821 = 692933) (by norm_num)
theorem B8319509 : Blo 1642020 8319509 := bbase (se 6 (by rfl) ⟨194988, by rfl⟩ : syracuseStep 8319509 = 389977) (by norm_num)
theorem B3748373 : Blo 1642020 3748373 := bbase (se 6 (by rfl) ⟨87852, by rfl⟩ : syracuseStep 3748373 = 175705) (by norm_num)
theorem B2773541 : Blo 1642020 2773541 := bbase (se 4 (by rfl) ⟨260019, by rfl⟩ : syracuseStep 2773541 = 520039) (by norm_num)
theorem B2961965 : Blo 1642020 2961965 := bbase (se 3 (by rfl) ⟨555368, by rfl⟩ : syracuseStep 2961965 = 1110737) (by norm_num)
theorem B1847857 : Blo 1642020 1847857 := bbase (se 2 (by rfl) ⟨692946, by rfl⟩ : syracuseStep 1847857 = 1385893) (by norm_num)
theorem B3117629 : Blo 1642020 3117629 := bbase (se 3 (by rfl) ⟨584555, by rfl⟩ : syracuseStep 3117629 = 1169111) (by norm_num)
theorem B4158013 : Blo 1642020 4158013 := bbase (se 3 (by rfl) ⟨779627, by rfl⟩ : syracuseStep 4158013 = 1559255) (by norm_num)
theorem B1847893 : Blo 1642020 1847893 := bbase (se 8 (by rfl) ⟨10827, by rfl⟩ : syracuseStep 1847893 = 21655) (by norm_num)
theorem B1847929 : Blo 1642020 1847929 := bbase (se 2 (by rfl) ⟨692973, by rfl⟩ : syracuseStep 1847929 = 1385947) (by norm_num)
theorem B1847965 : Blo 1642020 1847965 := bbase (se 3 (by rfl) ⟨346493, by rfl⟩ : syracuseStep 1847965 = 692987) (by norm_num)
theorem B2773669 : Blo 1642020 2773669 := bbase (se 4 (by rfl) ⟨260031, by rfl⟩ : syracuseStep 2773669 = 520063) (by norm_num)
theorem B2372261 : Blo 1642020 2372261 := bbase (se 4 (by rfl) ⟨222399, by rfl⟩ : syracuseStep 2372261 = 444799) (by norm_num)
theorem B4158125 : Blo 1642020 4158125 := bbase (se 3 (by rfl) ⟨779648, by rfl⟩ : syracuseStep 4158125 = 1559297) (by norm_num)
theorem B1848001 : Blo 1642020 1848001 := bbase (se 2 (by rfl) ⟨693000, by rfl⟩ : syracuseStep 1848001 = 1386001) (by norm_num)
theorem B5542613 : Blo 1642020 5542613 := bbase (se 7 (by rfl) ⟨64952, by rfl⟩ : syracuseStep 5542613 = 129905) (by norm_num)
theorem B3117781 : Blo 1642020 3117781 := bbase (se 7 (by rfl) ⟨36536, by rfl⟩ : syracuseStep 3117781 = 73073) (by norm_num)
theorem B1848037 : Blo 1642020 1848037 := bbase (se 4 (by rfl) ⟨173253, by rfl⟩ : syracuseStep 1848037 = 346507) (by norm_num)
theorem B2773757 : Blo 1642020 2773757 := bbase (se 3 (by rfl) ⟨520079, by rfl⟩ : syracuseStep 2773757 = 1040159) (by norm_num)
theorem B2667269 : Blo 1642020 2667269 := bbase (se 4 (by rfl) ⟨250056, by rfl⟩ : syracuseStep 2667269 = 500113) (by norm_num)
theorem B1848073 : Blo 1642020 1848073 := bbase (se 2 (by rfl) ⟨693027, by rfl⟩ : syracuseStep 1848073 = 1386055) (by norm_num)
theorem B2962189 : Blo 1642020 2962189 := bbase (se 3 (by rfl) ⟨555410, by rfl⟩ : syracuseStep 2962189 = 1110821) (by norm_num)
theorem B11842325 : Blo 1642020 11842325 := bbase (se 6 (by rfl) ⟨277554, by rfl⟩ : syracuseStep 11842325 = 555109) (by norm_num)
theorem B1848109 : Blo 1642020 1848109 := bbase (se 3 (by rfl) ⟨346520, by rfl⟩ : syracuseStep 1848109 = 693041) (by norm_num)
theorem B4215605 : Blo 1642020 4215605 := bbase (se 5 (by rfl) ⟨197606, by rfl⟩ : syracuseStep 4215605 = 395213) (by norm_num)
theorem B1848145 : Blo 1642020 1848145 := bbase (se 2 (by rfl) ⟨693054, by rfl⟩ : syracuseStep 1848145 = 1386109) (by norm_num)
theorem B4158317 : Blo 1642020 4158317 := bbase (se 3 (by rfl) ⟨779684, by rfl⟩ : syracuseStep 4158317 = 1559369) (by norm_num)
theorem B1848181 : Blo 1642020 1848181 := bbase (se 5 (by rfl) ⟨86633, by rfl⟩ : syracuseStep 1848181 = 173267) (by norm_num)
theorem B2773885 : Blo 1642020 2773885 := bbase (se 3 (by rfl) ⟨520103, by rfl⟩ : syracuseStep 2773885 = 1040207) (by norm_num)
theorem B1848217 : Blo 1642020 1848217 := bbase (se 2 (by rfl) ⟨693081, by rfl⟩ : syracuseStep 1848217 = 1386163) (by norm_num)
theorem B1848253 : Blo 1642020 1848253 := bbase (se 3 (by rfl) ⟨346547, by rfl⟩ : syracuseStep 1848253 = 693095) (by norm_num)
theorem B2773973 : Blo 1642020 2773973 := bbase (se 7 (by rfl) ⟨32507, by rfl⟩ : syracuseStep 2773973 = 65015) (by norm_num)
theorem B3331037 : Blo 1642020 3331037 := bbase (se 3 (by rfl) ⟨624569, by rfl⟩ : syracuseStep 3331037 = 1249139) (by norm_num)
theorem B1848289 : Blo 1642020 1848289 := bbase (se 2 (by rfl) ⟨693108, by rfl⟩ : syracuseStep 1848289 = 1386217) (by norm_num)
theorem B2888677 : Blo 1642020 2888677 := bbase (se 4 (by rfl) ⟨270813, by rfl⟩ : syracuseStep 2888677 = 541627) (by norm_num)
theorem B3118085 : Blo 1642020 3118085 := bbase (se 4 (by rfl) ⟨292320, by rfl⟩ : syracuseStep 3118085 = 584641) (by norm_num)
theorem B1848325 : Blo 1642020 1848325 := bbase (se 4 (by rfl) ⟨173280, by rfl⟩ : syracuseStep 1848325 = 346561) (by norm_num)
theorem B7894037 : Blo 1642020 7894037 := bbase (se 6 (by rfl) ⟨185016, by rfl⟩ : syracuseStep 7894037 = 370033) (by norm_num)
theorem B1848361 : Blo 1642020 1848361 := bbase (se 2 (by rfl) ⟨693135, by rfl⟩ : syracuseStep 1848361 = 1386271) (by norm_num)
theorem B2339885 : Blo 1642020 2339885 := bbase (se 3 (by rfl) ⟨438728, by rfl⟩ : syracuseStep 2339885 = 877457) (by norm_num)
theorem B2249789 : Blo 1642020 2249789 := bbase (se 3 (by rfl) ⟨421835, by rfl⟩ : syracuseStep 2249789 = 843671) (by norm_num)
theorem B1848397 : Blo 1642020 1848397 := bbase (se 3 (by rfl) ⟨346574, by rfl⟩ : syracuseStep 1848397 = 693149) (by norm_num)
theorem B2774101 : Blo 1642020 2774101 := bbase (se 8 (by rfl) ⟨16254, by rfl⟩ : syracuseStep 2774101 = 32509) (by norm_num)
theorem B21353557 : Blo 1642020 21353557 := bbase (se 8 (by rfl) ⟨125118, by rfl⟩ : syracuseStep 21353557 = 250237) (by norm_num)
theorem B1848433 : Blo 1642020 1848433 := bbase (se 2 (by rfl) ⟨693162, by rfl⟩ : syracuseStep 1848433 = 1386325) (by norm_num)
theorem B2339965 : Blo 1642020 2339965 := bbase (se 3 (by rfl) ⟨438743, by rfl⟩ : syracuseStep 2339965 = 877487) (by norm_num)
theorem B5543045 : Blo 1642020 5543045 := bbase (se 4 (by rfl) ⟨519660, by rfl⟩ : syracuseStep 5543045 = 1039321) (by norm_num)
theorem B1848469 : Blo 1642020 1848469 := bbase (se 6 (by rfl) ⟨43323, by rfl⟩ : syracuseStep 1848469 = 86647) (by norm_num)
theorem B2774189 : Blo 1642020 2774189 := bbase (se 3 (by rfl) ⟨520160, by rfl⟩ : syracuseStep 2774189 = 1040321) (by norm_num)
theorem B5919925 : Blo 1642020 5919925 := bbase (se 5 (by rfl) ⟨277496, by rfl⟩ : syracuseStep 5919925 = 554993) (by norm_num)
theorem B1848505 : Blo 1642020 1848505 := bbase (se 2 (by rfl) ⟨693189, by rfl⟩ : syracuseStep 1848505 = 1386379) (by norm_num)
theorem B4158661 : Blo 1642020 4158661 := bbase (se 4 (by rfl) ⟨389874, by rfl⟩ : syracuseStep 4158661 = 779749) (by norm_num)
theorem B1848541 : Blo 1642020 1848541 := bbase (se 3 (by rfl) ⟨346601, by rfl⟩ : syracuseStep 1848541 = 693203) (by norm_num)
theorem B2340085 : Blo 1642020 2340085 := bbase (se 5 (by rfl) ⟨109691, by rfl⟩ : syracuseStep 2340085 = 219383) (by norm_num)
theorem B1848577 : Blo 1642020 1848577 := bbase (se 2 (by rfl) ⟨693216, by rfl⟩ : syracuseStep 1848577 = 1386433) (by norm_num)
theorem B1848613 : Blo 1642020 1848613 := bbase (se 4 (by rfl) ⟨173307, by rfl⟩ : syracuseStep 1848613 = 346615) (by norm_num)
theorem B4158773 : Blo 1642020 4158773 := bbase (se 5 (by rfl) ⟨194942, by rfl⟩ : syracuseStep 4158773 = 389885) (by norm_num)
theorem B1848649 : Blo 1642020 1848649 := bbase (se 2 (by rfl) ⟨693243, by rfl⟩ : syracuseStep 1848649 = 1386487) (by norm_num)
theorem B2463053 : Blo 1642020 2463053 := bbase (se 3 (by rfl) ⟨461822, by rfl⟩ : syracuseStep 2463053 = 923645) (by norm_num)
theorem B2340181 : Blo 1642020 2340181 := bbase (se 13 (by rfl) ⟨428, by rfl⟩ : syracuseStep 2340181 = 857) (by norm_num)
theorem B2463077 : Blo 1642020 2463077 := bbase (se 4 (by rfl) ⟨230913, by rfl⟩ : syracuseStep 2463077 = 461827) (by norm_num)
theorem B1848685 : Blo 1642020 1848685 := bbase (se 3 (by rfl) ⟨346628, by rfl⟩ : syracuseStep 1848685 = 693257) (by norm_num)
theorem B2463101 : Blo 1642020 2463101 := bbase (se 3 (by rfl) ⟨461831, by rfl⟩ : syracuseStep 2463101 = 923663) (by norm_num)
theorem B1848721 : Blo 1642020 1848721 := bbase (se 2 (by rfl) ⟨693270, by rfl⟩ : syracuseStep 1848721 = 1386541) (by norm_num)
theorem B2463125 : Blo 1642020 2463125 := bbase (se 6 (by rfl) ⟨57729, by rfl⟩ : syracuseStep 2463125 = 115459) (by norm_num)
theorem B2463149 : Blo 1642020 2463149 := bbase (se 3 (by rfl) ⟨461840, by rfl⟩ : syracuseStep 2463149 = 923681) (by norm_num)
theorem B1848757 : Blo 1642020 1848757 := bbase (se 5 (by rfl) ⟨86660, by rfl⟩ : syracuseStep 1848757 = 173321) (by norm_num)
theorem B2463173 : Blo 1642020 2463173 := bbase (se 4 (by rfl) ⟨230922, by rfl⟩ : syracuseStep 2463173 = 461845) (by norm_num)
theorem B1848793 : Blo 1642020 1848793 := bbase (se 2 (by rfl) ⟨693297, by rfl⟩ : syracuseStep 1848793 = 1386595) (by norm_num)
theorem B2463197 : Blo 1642020 2463197 := bbase (se 3 (by rfl) ⟨461849, by rfl⟩ : syracuseStep 2463197 = 923699) (by norm_num)
theorem B2463221 : Blo 1642020 2463221 := bbase (se 5 (by rfl) ⟨115463, by rfl⟩ : syracuseStep 2463221 = 230927) (by norm_num)
theorem B4158965 : Blo 1642020 4158965 := bbase (se 5 (by rfl) ⟨194951, by rfl⟩ : syracuseStep 4158965 = 389903) (by norm_num)
theorem B1848829 : Blo 1642020 1848829 := bbase (se 3 (by rfl) ⟨346655, by rfl⟩ : syracuseStep 1848829 = 693311) (by norm_num)
theorem B2463245 : Blo 1642020 2463245 := bbase (se 3 (by rfl) ⟨461858, by rfl⟩ : syracuseStep 2463245 = 923717) (by norm_num)
theorem B2078237 : Blo 1642020 2078237 := bbase (se 3 (by rfl) ⟨389669, by rfl⟩ : syracuseStep 2078237 = 779339) (by norm_num)
theorem B1848865 : Blo 1642020 1848865 := bbase (se 2 (by rfl) ⟨693324, by rfl⟩ : syracuseStep 1848865 = 1386649) (by norm_num)
theorem B2463269 : Blo 1642020 2463269 := bbase (se 4 (by rfl) ⟨230931, by rfl⟩ : syracuseStep 2463269 = 461863) (by norm_num)
theorem B5543477 : Blo 1642020 5543477 := bbase (se 5 (by rfl) ⟨259850, by rfl⟩ : syracuseStep 5543477 = 519701) (by norm_num)
theorem B2463293 : Blo 1642020 2463293 := bbase (se 3 (by rfl) ⟨461867, by rfl⟩ : syracuseStep 2463293 = 923735) (by norm_num)
theorem B1848901 : Blo 1642020 1848901 := bbase (se 4 (by rfl) ⟨173334, by rfl⟩ : syracuseStep 1848901 = 346669) (by norm_num)
theorem B2078293 : Blo 1642020 2078293 := bbase (se 8 (by rfl) ⟨12177, by rfl⟩ : syracuseStep 2078293 = 24355) (by norm_num)
theorem B2463317 : Blo 1642020 2463317 := bbase (se 8 (by rfl) ⟨14433, by rfl⟩ : syracuseStep 2463317 = 28867) (by norm_num)
theorem B8001125 : Blo 1642020 8001125 := bbase (se 4 (by rfl) ⟨750105, by rfl⟩ : syracuseStep 8001125 = 1500211) (by norm_num)
theorem B1848937 : Blo 1642020 1848937 := bbase (se 2 (by rfl) ⟨693351, by rfl⟩ : syracuseStep 1848937 = 1386703) (by norm_num)
theorem B2463341 : Blo 1642020 2463341 := bbase (se 3 (by rfl) ⟨461876, by rfl⟩ : syracuseStep 2463341 = 923753) (by norm_num)
theorem B6239861 : Blo 1642020 6239861 := bbase (se 5 (by rfl) ⟨292493, by rfl⟩ : syracuseStep 6239861 = 584987) (by norm_num)
theorem B2463365 : Blo 1642020 2463365 := bbase (se 4 (by rfl) ⟨230940, by rfl⟩ : syracuseStep 2463365 = 461881) (by norm_num)
theorem B1848973 : Blo 1642020 1848973 := bbase (se 3 (by rfl) ⟨346682, by rfl⟩ : syracuseStep 1848973 = 693365) (by norm_num)
theorem B2463389 : Blo 1642020 2463389 := bbase (se 3 (by rfl) ⟨461885, by rfl⟩ : syracuseStep 2463389 = 923771) (by norm_num)
theorem B3331757 : Blo 1642020 3331757 := bbase (se 3 (by rfl) ⟨624704, by rfl⟩ : syracuseStep 3331757 = 1249409) (by norm_num)
theorem B1849009 : Blo 1642020 1849009 := bbase (se 2 (by rfl) ⟨693378, by rfl⟩ : syracuseStep 1849009 = 1386757) (by norm_num)
theorem B2078389 : Blo 1642020 2078389 := bbase (se 5 (by rfl) ⟨97424, by rfl⟩ : syracuseStep 2078389 = 194849) (by norm_num)
theorem B2463413 : Blo 1642020 2463413 := bbase (se 5 (by rfl) ⟨115472, by rfl⟩ : syracuseStep 2463413 = 230945) (by norm_num)
theorem B2463437 : Blo 1642020 2463437 := bbase (se 3 (by rfl) ⟨461894, by rfl⟩ : syracuseStep 2463437 = 923789) (by norm_num)
theorem B1849045 : Blo 1642020 1849045 := bbase (se 7 (by rfl) ⟨21668, by rfl⟩ : syracuseStep 1849045 = 43337) (by norm_num)
theorem B2463461 : Blo 1642020 2463461 := bbase (se 4 (by rfl) ⟨230949, by rfl⟩ : syracuseStep 2463461 = 461899) (by norm_num)
theorem B3118837 : Blo 1642020 3118837 := bbase (se 5 (by rfl) ⟨146195, by rfl⟩ : syracuseStep 3118837 = 292391) (by norm_num)
theorem B1849081 : Blo 1642020 1849081 := bbase (se 2 (by rfl) ⟨693405, by rfl⟩ : syracuseStep 1849081 = 1386811) (by norm_num)
theorem B2463485 : Blo 1642020 2463485 := bbase (se 3 (by rfl) ⟨461903, by rfl⟩ : syracuseStep 2463485 = 923807) (by norm_num)
theorem B8427269 : Blo 1642020 8427269 := bbase (se 4 (by rfl) ⟨790056, by rfl⟩ : syracuseStep 8427269 = 1580113) (by norm_num)
theorem B2463509 : Blo 1642020 2463509 := bbase (se 6 (by rfl) ⟨57738, by rfl⟩ : syracuseStep 2463509 = 115477) (by norm_num)
theorem B10524437 : Blo 1642020 10524437 := bbase (se 6 (by rfl) ⟨246666, by rfl⟩ : syracuseStep 10524437 = 493333) (by norm_num)
theorem B1849117 : Blo 1642020 1849117 := bbase (se 3 (by rfl) ⟨346709, by rfl⟩ : syracuseStep 1849117 = 693419) (by norm_num)
theorem B8320805 : Blo 1642020 8320805 := bbase (se 4 (by rfl) ⟨780075, by rfl⟩ : syracuseStep 8320805 = 1560151) (by norm_num)
theorem B2463533 : Blo 1642020 2463533 := bbase (se 3 (by rfl) ⟨461912, by rfl⟩ : syracuseStep 2463533 = 923825) (by norm_num)
theorem B1849153 : Blo 1642020 1849153 := bbase (se 2 (by rfl) ⟨693432, by rfl⟩ : syracuseStep 1849153 = 1386865) (by norm_num)
theorem B2463557 : Blo 1642020 2463557 := bbase (se 4 (by rfl) ⟨230958, by rfl⟩ : syracuseStep 2463557 = 461917) (by norm_num)
theorem B2340677 : Blo 1642020 2340677 := bbase (se 4 (by rfl) ⟨219438, by rfl⟩ : syracuseStep 2340677 = 438877) (by norm_num)
theorem B4159309 : Blo 1642020 4159309 := bbase (se 3 (by rfl) ⟨779870, by rfl⟩ : syracuseStep 4159309 = 1559741) (by norm_num)
theorem B2463581 : Blo 1642020 2463581 := bbase (se 3 (by rfl) ⟨461921, by rfl⟩ : syracuseStep 2463581 = 923843) (by norm_num)
theorem B2078561 : Blo 1642020 2078561 := bbase (se 2 (by rfl) ⟨779460, by rfl⟩ : syracuseStep 2078561 = 1558921) (by norm_num)
theorem B1849189 : Blo 1642020 1849189 := bbase (se 4 (by rfl) ⟨173361, by rfl⟩ : syracuseStep 1849189 = 346723) (by norm_num)
theorem B2463605 : Blo 1642020 2463605 := bbase (se 5 (by rfl) ⟨115481, by rfl⟩ : syracuseStep 2463605 = 230963) (by norm_num)
theorem B3118981 : Blo 1642020 3118981 := bbase (se 4 (by rfl) ⟨292404, by rfl⟩ : syracuseStep 3118981 = 584809) (by norm_num)
theorem B1849225 : Blo 1642020 1849225 := bbase (se 2 (by rfl) ⟨693459, by rfl⟩ : syracuseStep 1849225 = 1386919) (by norm_num)
theorem B2463629 : Blo 1642020 2463629 := bbase (se 3 (by rfl) ⟨461930, by rfl⟩ : syracuseStep 2463629 = 923861) (by norm_num)
theorem B6240149 : Blo 1642020 6240149 := bbase (se 6 (by rfl) ⟨146253, by rfl⟩ : syracuseStep 6240149 = 292507) (by norm_num)
theorem B2078617 : Blo 1642020 2078617 := bbase (se 2 (by rfl) ⟨779481, by rfl⟩ : syracuseStep 2078617 = 1558963) (by norm_num)
theorem B2463653 : Blo 1642020 2463653 := bbase (se 4 (by rfl) ⟨230967, by rfl⟩ : syracuseStep 2463653 = 461935) (by norm_num)
theorem B1849261 : Blo 1642020 1849261 := bbase (se 3 (by rfl) ⟨346736, by rfl⟩ : syracuseStep 1849261 = 693473) (by norm_num)
theorem B2463677 : Blo 1642020 2463677 := bbase (se 3 (by rfl) ⟨461939, by rfl⟩ : syracuseStep 2463677 = 923879) (by norm_num)
theorem B4159421 : Blo 1642020 4159421 := bbase (se 3 (by rfl) ⟨779891, by rfl⟩ : syracuseStep 4159421 = 1559783) (by norm_num)
theorem B7493573 : Blo 1642020 7493573 := bbase (se 4 (by rfl) ⟨702522, by rfl⟩ : syracuseStep 7493573 = 1405045) (by norm_num)
theorem B1849297 : Blo 1642020 1849297 := bbase (se 2 (by rfl) ⟨693486, by rfl⟩ : syracuseStep 1849297 = 1386973) (by norm_num)
theorem B2463701 : Blo 1642020 2463701 := bbase (se 7 (by rfl) ⟨28871, by rfl⟩ : syracuseStep 2463701 = 57743) (by norm_num)
theorem B5543909 : Blo 1642020 5543909 := bbase (se 4 (by rfl) ⟨519741, by rfl⟩ : syracuseStep 5543909 = 1039483) (by norm_num)
theorem B2463725 : Blo 1642020 2463725 := bbase (se 3 (by rfl) ⟨461948, by rfl⟩ : syracuseStep 2463725 = 923897) (by norm_num)
theorem B1849333 : Blo 1642020 1849333 := bbase (se 5 (by rfl) ⟨86687, by rfl⟩ : syracuseStep 1849333 = 173375) (by norm_num)
theorem B2078713 : Blo 1642020 2078713 := bbase (se 2 (by rfl) ⟨779517, by rfl⟩ : syracuseStep 2078713 = 1559035) (by norm_num)
theorem B2463749 : Blo 1642020 2463749 := bbase (se 4 (by rfl) ⟨230976, by rfl⟩ : syracuseStep 2463749 = 461953) (by norm_num)
theorem B1849369 : Blo 1642020 1849369 := bbase (se 2 (by rfl) ⟨693513, by rfl⟩ : syracuseStep 1849369 = 1387027) (by norm_num)
theorem B2463773 : Blo 1642020 2463773 := bbase (se 3 (by rfl) ⟨461957, by rfl⟩ : syracuseStep 2463773 = 923915) (by norm_num)
theorem B3119141 : Blo 1642020 3119141 := bbase (se 4 (by rfl) ⟨292419, by rfl⟩ : syracuseStep 3119141 = 584839) (by norm_num)
theorem B2463797 : Blo 1642020 2463797 := bbase (se 5 (by rfl) ⟨115490, by rfl⟩ : syracuseStep 2463797 = 230981) (by norm_num)
theorem B1849405 : Blo 1642020 1849405 := bbase (se 3 (by rfl) ⟨346763, by rfl⟩ : syracuseStep 1849405 = 693527) (by norm_num)
theorem B2463821 : Blo 1642020 2463821 := bbase (se 3 (by rfl) ⟨461966, by rfl⟩ : syracuseStep 2463821 = 923933) (by norm_num)
theorem B1849441 : Blo 1642020 1849441 := bbase (se 2 (by rfl) ⟨693540, by rfl⟩ : syracuseStep 1849441 = 1387081) (by norm_num)
theorem B2463845 : Blo 1642020 2463845 := bbase (se 4 (by rfl) ⟨230985, by rfl⟩ : syracuseStep 2463845 = 461971) (by norm_num)
theorem B2463869 : Blo 1642020 2463869 := bbase (se 3 (by rfl) ⟨461975, by rfl⟩ : syracuseStep 2463869 = 923951) (by norm_num)
theorem B4159613 : Blo 1642020 4159613 := bbase (se 3 (by rfl) ⟨779927, by rfl⟩ : syracuseStep 4159613 = 1559855) (by norm_num)
theorem B1849477 : Blo 1642020 1849477 := bbase (se 4 (by rfl) ⟨173388, by rfl⟩ : syracuseStep 1849477 = 346777) (by norm_num)
theorem B2463893 : Blo 1642020 2463893 := bbase (se 6 (by rfl) ⟨57747, by rfl⟩ : syracuseStep 2463893 = 115495) (by norm_num)
theorem B2078885 : Blo 1642020 2078885 := bbase (se 4 (by rfl) ⟨194895, by rfl⟩ : syracuseStep 2078885 = 389791) (by norm_num)
theorem B1849513 : Blo 1642020 1849513 := bbase (se 2 (by rfl) ⟨693567, by rfl⟩ : syracuseStep 1849513 = 1387135) (by norm_num)
theorem B2463917 : Blo 1642020 2463917 := bbase (se 3 (by rfl) ⟨461984, by rfl⟩ : syracuseStep 2463917 = 923969) (by norm_num)
theorem B3119285 : Blo 1642020 3119285 := bbase (se 5 (by rfl) ⟨146216, by rfl⟩ : syracuseStep 3119285 = 292433) (by norm_num)
theorem B8313029 : Blo 1642020 8313029 := bbase (se 4 (by rfl) ⟨779346, by rfl⟩ : syracuseStep 8313029 = 1558693) (by norm_num)
theorem B2463941 : Blo 1642020 2463941 := bbase (se 4 (by rfl) ⟨230994, by rfl⟩ : syracuseStep 2463941 = 461989) (by norm_num)
theorem B2078941 : Blo 1642020 2078941 := bbase (se 3 (by rfl) ⟨389801, by rfl⟩ : syracuseStep 2078941 = 779603) (by norm_num)
theorem B2463965 : Blo 1642020 2463965 := bbase (se 3 (by rfl) ⟨461993, by rfl⟩ : syracuseStep 2463965 = 923987) (by norm_num)
theorem B2463989 : Blo 1642020 2463989 := bbase (se 5 (by rfl) ⟨115499, by rfl⟩ : syracuseStep 2463989 = 230999) (by norm_num)
theorem B2464013 : Blo 1642020 2464013 := bbase (se 3 (by rfl) ⟨462002, by rfl⟩ : syracuseStep 2464013 = 924005) (by norm_num)
theorem B6658325 : Blo 1642020 6658325 := bbase (se 6 (by rfl) ⟨156054, by rfl⟩ : syracuseStep 6658325 = 312109) (by norm_num)
theorem B23689493 : Blo 1642020 23689493 := bbase (se 6 (by rfl) ⟨555222, by rfl⟩ : syracuseStep 23689493 = 1110445) (by norm_num)
theorem B2464037 : Blo 1642020 2464037 := bbase (se 4 (by rfl) ⟨231003, by rfl⟩ : syracuseStep 2464037 = 462007) (by norm_num)
theorem B2079037 : Blo 1642020 2079037 := bbase (se 3 (by rfl) ⟨389819, by rfl⟩ : syracuseStep 2079037 = 779639) (by norm_num)
theorem B2464061 : Blo 1642020 2464061 := bbase (se 3 (by rfl) ⟨462011, by rfl⟩ : syracuseStep 2464061 = 924023) (by norm_num)
theorem B2464085 : Blo 1642020 2464085 := bbase (se 10 (by rfl) ⟨3609, by rfl⟩ : syracuseStep 2464085 = 7219) (by norm_num)
theorem B2464109 : Blo 1642020 2464109 := bbase (se 3 (by rfl) ⟨462020, by rfl⟩ : syracuseStep 2464109 = 924041) (by norm_num)
theorem B2464133 : Blo 1642020 2464133 := bbase (se 4 (by rfl) ⟨231012, by rfl⟩ : syracuseStep 2464133 = 462025) (by norm_num)
theorem B5544341 : Blo 1642020 5544341 := bbase (se 6 (by rfl) ⟨129945, by rfl⟩ : syracuseStep 5544341 = 259891) (by norm_num)
theorem B15792533 : Blo 1642020 15792533 := bbase (se 6 (by rfl) ⟨370137, by rfl⟩ : syracuseStep 15792533 = 740275) (by norm_num)
theorem B2464157 : Blo 1642020 2464157 := bbase (se 3 (by rfl) ⟨462029, by rfl⟩ : syracuseStep 2464157 = 924059) (by norm_num)
theorem B2464181 : Blo 1642020 2464181 := bbase (se 5 (by rfl) ⟨115508, by rfl⟩ : syracuseStep 2464181 = 231017) (by norm_num)
theorem B2464205 : Blo 1642020 2464205 := bbase (se 3 (by rfl) ⟨462038, by rfl⟩ : syracuseStep 2464205 = 924077) (by norm_num)
theorem B3119573 : Blo 1642020 3119573 := bbase (se 7 (by rfl) ⟨36557, by rfl⟩ : syracuseStep 3119573 = 73115) (by norm_num)
theorem B4159957 : Blo 1642020 4159957 := bbase (se 7 (by rfl) ⟨48749, by rfl⟩ : syracuseStep 4159957 = 97499) (by norm_num)
theorem B4676069 : Blo 1642020 4676069 := bbase (se 4 (by rfl) ⟨438381, by rfl⟩ : syracuseStep 4676069 = 876763) (by norm_num)
theorem B3946981 : Blo 1642020 3946981 := bbase (se 4 (by rfl) ⟨370029, by rfl⟩ : syracuseStep 3946981 = 740059) (by norm_num)
theorem B2464229 : Blo 1642020 2464229 := bbase (se 4 (by rfl) ⟨231021, by rfl⟩ : syracuseStep 2464229 = 462043) (by norm_num)
theorem B2079209 : Blo 1642020 2079209 := bbase (se 2 (by rfl) ⟨779703, by rfl⟩ : syracuseStep 2079209 = 1559407) (by norm_num)
theorem B2464253 : Blo 1642020 2464253 := bbase (se 3 (by rfl) ⟨462047, by rfl⟩ : syracuseStep 2464253 = 924095) (by norm_num)
theorem B1972741 : Blo 1642020 1972741 := bbase (se 4 (by rfl) ⟨184944, by rfl⟩ : syracuseStep 1972741 = 369889) (by norm_num)
theorem B2464277 : Blo 1642020 2464277 := bbase (se 6 (by rfl) ⟨57756, by rfl⟩ : syracuseStep 2464277 = 115513) (by norm_num)
theorem B2079265 : Blo 1642020 2079265 := bbase (se 2 (by rfl) ⟨779724, by rfl⟩ : syracuseStep 2079265 = 1559449) (by norm_num)
theorem B2464301 : Blo 1642020 2464301 := bbase (se 3 (by rfl) ⟨462056, by rfl⟩ : syracuseStep 2464301 = 924113) (by norm_num)
theorem B2464325 : Blo 1642020 2464325 := bbase (se 4 (by rfl) ⟨231030, by rfl⟩ : syracuseStep 2464325 = 462061) (by norm_num)
theorem B4160069 : Blo 1642020 4160069 := bbase (se 4 (by rfl) ⟨390006, by rfl⟩ : syracuseStep 4160069 = 780013) (by norm_num)
theorem B2464349 : Blo 1642020 2464349 := bbase (se 3 (by rfl) ⟨462065, by rfl⟩ : syracuseStep 2464349 = 924131) (by norm_num)
theorem B3119725 : Blo 1642020 3119725 := bbase (se 3 (by rfl) ⟨584948, by rfl⟩ : syracuseStep 3119725 = 1169897) (by norm_num)
theorem B3947125 : Blo 1642020 3947125 := bbase (se 5 (by rfl) ⟨185021, by rfl⟩ : syracuseStep 3947125 = 370043) (by norm_num)
theorem B2464373 : Blo 1642020 2464373 := bbase (se 5 (by rfl) ⟨115517, by rfl⟩ : syracuseStep 2464373 = 231035) (by norm_num)
theorem B2079361 : Blo 1642020 2079361 := bbase (se 2 (by rfl) ⟨779760, by rfl⟩ : syracuseStep 2079361 = 1559521) (by norm_num)
theorem B1874561 : Blo 1642020 1874561 := bbase (se 2 (by rfl) ⟨702960, by rfl⟩ : syracuseStep 1874561 = 1405921) (by norm_num)
theorem B2464397 : Blo 1642020 2464397 := bbase (se 3 (by rfl) ⟨462074, by rfl⟩ : syracuseStep 2464397 = 924149) (by norm_num)
theorem B1972885 : Blo 1642020 1972885 := bbase (se 6 (by rfl) ⟨46239, by rfl⟩ : syracuseStep 1972885 = 92479) (by norm_num)
theorem B2464421 : Blo 1642020 2464421 := bbase (se 4 (by rfl) ⟨231039, by rfl⟩ : syracuseStep 2464421 = 462079) (by norm_num)
theorem B1874597 : Blo 1642020 1874597 := bbase (se 4 (by rfl) ⟨175743, by rfl⟩ : syracuseStep 1874597 = 351487) (by norm_num)
theorem B2464445 : Blo 1642020 2464445 := bbase (se 3 (by rfl) ⟨462083, by rfl⟩ : syracuseStep 2464445 = 924167) (by norm_num)
theorem B5774021 : Blo 1642020 5774021 := bbase (se 4 (by rfl) ⟨541314, by rfl⟩ : syracuseStep 5774021 = 1082629) (by norm_num)
theorem B2464469 : Blo 1642020 2464469 := bbase (se 7 (by rfl) ⟨28880, by rfl⟩ : syracuseStep 2464469 = 57761) (by norm_num)
theorem B2464493 : Blo 1642020 2464493 := bbase (se 3 (by rfl) ⟨462092, by rfl⟩ : syracuseStep 2464493 = 924185) (by norm_num)
theorem B2464517 : Blo 1642020 2464517 := bbase (se 4 (by rfl) ⟨231048, by rfl⟩ : syracuseStep 2464517 = 462097) (by norm_num)
theorem B4160261 : Blo 1642020 4160261 := bbase (se 4 (by rfl) ⟨390024, by rfl⟩ : syracuseStep 4160261 = 780049) (by norm_num)
theorem B2464541 : Blo 1642020 2464541 := bbase (se 3 (by rfl) ⟨462101, by rfl⟩ : syracuseStep 2464541 = 924203) (by norm_num)
theorem B2079533 : Blo 1642020 2079533 := bbase (se 3 (by rfl) ⟨389912, by rfl⟩ : syracuseStep 2079533 = 779825) (by norm_num)
theorem B2464565 : Blo 1642020 2464565 := bbase (se 5 (by rfl) ⟨115526, by rfl⟩ : syracuseStep 2464565 = 231053) (by norm_num)
theorem B5544773 : Blo 1642020 5544773 := bbase (se 4 (by rfl) ⟨519822, by rfl⟩ : syracuseStep 5544773 = 1039645) (by norm_num)
theorem B2464589 : Blo 1642020 2464589 := bbase (se 3 (by rfl) ⟨462110, by rfl⟩ : syracuseStep 2464589 = 924221) (by norm_num)
theorem B2464613 : Blo 1642020 2464613 := bbase (se 4 (by rfl) ⟨231057, by rfl⟩ : syracuseStep 2464613 = 462115) (by norm_num)
theorem B2079589 : Blo 1642020 2079589 := bbase (se 4 (by rfl) ⟨194961, by rfl⟩ : syracuseStep 2079589 = 389923) (by norm_num)
theorem B2464637 : Blo 1642020 2464637 := bbase (se 3 (by rfl) ⟨462119, by rfl⟩ : syracuseStep 2464637 = 924239) (by norm_num)
theorem B2464661 : Blo 1642020 2464661 := bbase (se 6 (by rfl) ⟨57765, by rfl⟩ : syracuseStep 2464661 = 115531) (by norm_num)
theorem B3120029 : Blo 1642020 3120029 := bbase (se 3 (by rfl) ⟨585005, by rfl⟩ : syracuseStep 3120029 = 1170011) (by norm_num)
theorem B2464685 : Blo 1642020 2464685 := bbase (se 3 (by rfl) ⟨462128, by rfl⟩ : syracuseStep 2464685 = 924257) (by norm_num)
theorem B2464709 : Blo 1642020 2464709 := bbase (se 4 (by rfl) ⟨231066, by rfl⟩ : syracuseStep 2464709 = 462133) (by norm_num)
theorem B2079685 : Blo 1642020 2079685 := bbase (se 4 (by rfl) ⟨194970, by rfl⟩ : syracuseStep 2079685 = 389941) (by norm_num)
theorem B1899461 : Blo 1642020 1899461 := bbase (se 4 (by rfl) ⟨178074, by rfl⟩ : syracuseStep 1899461 = 356149) (by norm_num)
theorem B2464733 : Blo 1642020 2464733 := bbase (se 3 (by rfl) ⟨462137, by rfl⟩ : syracuseStep 2464733 = 924275) (by norm_num)
theorem B2464757 : Blo 1642020 2464757 := bbase (se 5 (by rfl) ⟨115535, by rfl⟩ : syracuseStep 2464757 = 231071) (by norm_num)
theorem B2464781 : Blo 1642020 2464781 := bbase (se 3 (by rfl) ⟨462146, by rfl⟩ : syracuseStep 2464781 = 924293) (by norm_num)
theorem B2464805 : Blo 1642020 2464805 := bbase (se 4 (by rfl) ⟨231075, by rfl⟩ : syracuseStep 2464805 = 462151) (by norm_num)
theorem B6241333 : Blo 1642020 6241333 := bbase (se 5 (by rfl) ⟨292562, by rfl⟩ : syracuseStep 6241333 = 585125) (by norm_num)
theorem B8322101 : Blo 1642020 8322101 := bbase (se 5 (by rfl) ⟨390098, by rfl⟩ : syracuseStep 8322101 = 780197) (by norm_num)
theorem B2464829 : Blo 1642020 2464829 := bbase (se 3 (by rfl) ⟨462155, by rfl⟩ : syracuseStep 2464829 = 924311) (by norm_num)
theorem B2464853 : Blo 1642020 2464853 := bbase (se 8 (by rfl) ⟨14442, by rfl⟩ : syracuseStep 2464853 = 28885) (by norm_num)
theorem B4160605 : Blo 1642020 4160605 := bbase (se 3 (by rfl) ⟨780113, by rfl⟩ : syracuseStep 4160605 = 1560227) (by norm_num)
theorem B2464877 : Blo 1642020 2464877 := bbase (se 3 (by rfl) ⟨462164, by rfl⟩ : syracuseStep 2464877 = 924329) (by norm_num)
theorem B2079857 : Blo 1642020 2079857 := bbase (se 2 (by rfl) ⟨779946, by rfl⟩ : syracuseStep 2079857 = 1559893) (by norm_num)
theorem B4676741 : Blo 1642020 4676741 := bbase (se 4 (by rfl) ⟨438444, by rfl⟩ : syracuseStep 4676741 = 876889) (by norm_num)
theorem B2464901 : Blo 1642020 2464901 := bbase (se 4 (by rfl) ⟨231084, by rfl⟩ : syracuseStep 2464901 = 462169) (by norm_num)
theorem B2464925 : Blo 1642020 2464925 := bbase (se 3 (by rfl) ⟨462173, by rfl⟩ : syracuseStep 2464925 = 924347) (by norm_num)
theorem B2079913 : Blo 1642020 2079913 := bbase (se 2 (by rfl) ⟨779967, by rfl⟩ : syracuseStep 2079913 = 1559935) (by norm_num)
theorem B2464949 : Blo 1642020 2464949 := bbase (se 5 (by rfl) ⟨115544, by rfl⟩ : syracuseStep 2464949 = 231089) (by norm_num)
theorem B2464973 : Blo 1642020 2464973 := bbase (se 3 (by rfl) ⟨462182, by rfl⟩ : syracuseStep 2464973 = 924365) (by norm_num)
theorem B4160717 : Blo 1642020 4160717 := bbase (se 3 (by rfl) ⟨780134, by rfl⟩ : syracuseStep 4160717 = 1560269) (by norm_num)
theorem B3947741 : Blo 1642020 3947741 := bbase (se 3 (by rfl) ⟨740201, by rfl⟩ : syracuseStep 3947741 = 1480403) (by norm_num)
theorem B3849445 : Blo 1642020 3849445 := bbase (se 4 (by rfl) ⟨360885, by rfl⟩ : syracuseStep 3849445 = 721771) (by norm_num)
theorem B2464997 : Blo 1642020 2464997 := bbase (se 4 (by rfl) ⟨231093, by rfl⟩ : syracuseStep 2464997 = 462187) (by norm_num)
theorem B5545205 : Blo 1642020 5545205 := bbase (se 5 (by rfl) ⟨259931, by rfl⟩ : syracuseStep 5545205 = 519863) (by norm_num)
theorem B2465021 : Blo 1642020 2465021 := bbase (se 3 (by rfl) ⟨462191, by rfl⟩ : syracuseStep 2465021 = 924383) (by norm_num)
theorem B2080009 : Blo 1642020 2080009 := bbase (se 2 (by rfl) ⟨780003, by rfl⟩ : syracuseStep 2080009 = 1560007) (by norm_num)
theorem B2465045 : Blo 1642020 2465045 := bbase (se 6 (by rfl) ⟨57774, by rfl⟩ : syracuseStep 2465045 = 115549) (by norm_num)
theorem B5922085 : Blo 1642020 5922085 := bbase (se 4 (by rfl) ⟨555195, by rfl⟩ : syracuseStep 5922085 = 1110391) (by norm_num)
theorem B2465069 : Blo 1642020 2465069 := bbase (se 3 (by rfl) ⟨462200, by rfl⟩ : syracuseStep 2465069 = 924401) (by norm_num)
theorem B5266741 : Blo 1642020 5266741 := bbase (se 5 (by rfl) ⟨246878, by rfl⟩ : syracuseStep 5266741 = 493757) (by norm_num)
theorem B2465093 : Blo 1642020 2465093 := bbase (se 4 (by rfl) ⟨231102, by rfl⟩ : syracuseStep 2465093 = 462205) (by norm_num)
theorem B2465117 : Blo 1642020 2465117 := bbase (se 3 (by rfl) ⟨462209, by rfl⟩ : syracuseStep 2465117 = 924419) (by norm_num)
theorem B6241637 : Blo 1642020 6241637 := bbase (se 4 (by rfl) ⟨585153, by rfl⟩ : syracuseStep 6241637 = 1170307) (by norm_num)
theorem B2465141 : Blo 1642020 2465141 := bbase (se 5 (by rfl) ⟨115553, by rfl⟩ : syracuseStep 2465141 = 231107) (by norm_num)
theorem B2465165 : Blo 1642020 2465165 := bbase (se 3 (by rfl) ⟨462218, by rfl⟩ : syracuseStep 2465165 = 924437) (by norm_num)
theorem B4160909 : Blo 1642020 4160909 := bbase (se 3 (by rfl) ⟨780170, by rfl⟩ : syracuseStep 4160909 = 1560341) (by norm_num)
theorem B2465189 : Blo 1642020 2465189 := bbase (se 4 (by rfl) ⟨231111, by rfl⟩ : syracuseStep 2465189 = 462223) (by norm_num)
theorem B2080181 : Blo 1642020 2080181 := bbase (se 5 (by rfl) ⟨97508, by rfl⟩ : syracuseStep 2080181 = 195017) (by norm_num)
theorem B2465213 : Blo 1642020 2465213 := bbase (se 3 (by rfl) ⟨462227, by rfl⟩ : syracuseStep 2465213 = 924455) (by norm_num)
theorem B8314325 : Blo 1642020 8314325 := bbase (se 7 (by rfl) ⟨97433, by rfl⟩ : syracuseStep 8314325 = 194867) (by norm_num)
theorem B2465237 : Blo 1642020 2465237 := bbase (se 7 (by rfl) ⟨28889, by rfl⟩ : syracuseStep 2465237 = 57779) (by norm_num)
theorem B3800549 : Blo 1642020 3800549 := bbase (se 4 (by rfl) ⟨356301, by rfl⟩ : syracuseStep 3800549 = 712603) (by norm_num)
theorem B2465261 : Blo 1642020 2465261 := bbase (se 3 (by rfl) ⟨462236, by rfl⟩ : syracuseStep 2465261 = 924473) (by norm_num)
theorem B2080237 : Blo 1642020 2080237 := bbase (se 3 (by rfl) ⟨390044, by rfl⟩ : syracuseStep 2080237 = 780089) (by norm_num)
theorem B2465285 : Blo 1642020 2465285 := bbase (se 4 (by rfl) ⟨231120, by rfl⟩ : syracuseStep 2465285 = 462241) (by norm_num)
theorem B25288213 : Blo 1642020 25288213 := bbase (se 6 (by rfl) ⟨592692, by rfl⟩ : syracuseStep 25288213 = 1185385) (by norm_num)
theorem B2465309 : Blo 1642020 2465309 := bbase (se 3 (by rfl) ⟨462245, by rfl⟩ : syracuseStep 2465309 = 924491) (by norm_num)
theorem B3948077 : Blo 1642020 3948077 := bbase (se 3 (by rfl) ⟨740264, by rfl⟩ : syracuseStep 3948077 = 1480529) (by norm_num)
theorem B4677173 : Blo 1642020 4677173 := bbase (se 5 (by rfl) ⟨219242, by rfl⟩ : syracuseStep 4677173 = 438485) (by norm_num)
theorem B8879669 : Blo 1642020 8879669 := bbase (se 5 (by rfl) ⟨416234, by rfl⟩ : syracuseStep 8879669 = 832469) (by norm_num)
theorem B2465333 : Blo 1642020 2465333 := bbase (se 5 (by rfl) ⟨115562, by rfl⟩ : syracuseStep 2465333 = 231125) (by norm_num)
theorem B2465357 : Blo 1642020 2465357 := bbase (se 3 (by rfl) ⟨462254, by rfl⟩ : syracuseStep 2465357 = 924509) (by norm_num)
theorem B2080333 : Blo 1642020 2080333 := bbase (se 3 (by rfl) ⟨390062, by rfl⟩ : syracuseStep 2080333 = 780125) (by norm_num)
theorem B2465381 : Blo 1642020 2465381 := bbase (se 4 (by rfl) ⟨231129, by rfl⟩ : syracuseStep 2465381 = 462259) (by norm_num)
theorem B7593589 : Blo 1642020 7593589 := bbase (se 5 (by rfl) ⟨355949, by rfl⟩ : syracuseStep 7593589 = 711899) (by norm_num)
theorem B2465405 : Blo 1642020 2465405 := bbase (se 3 (by rfl) ⟨462263, by rfl⟩ : syracuseStep 2465405 = 924527) (by norm_num)
theorem B2219653 : Blo 1642020 2219653 := bbase (se 4 (by rfl) ⟨208092, by rfl⟩ : syracuseStep 2219653 = 416185) (by norm_num)
theorem B3948173 : Blo 1642020 3948173 := bbase (se 3 (by rfl) ⟨740282, by rfl⟩ : syracuseStep 3948173 = 1480565) (by norm_num)
theorem B3120781 : Blo 1642020 3120781 := bbase (se 3 (by rfl) ⟨585146, by rfl⟩ : syracuseStep 3120781 = 1170293) (by norm_num)
theorem B2465429 : Blo 1642020 2465429 := bbase (se 6 (by rfl) ⟨57783, by rfl⟩ : syracuseStep 2465429 = 115567) (by norm_num)
theorem B5545637 : Blo 1642020 5545637 := bbase (se 4 (by rfl) ⟨519903, by rfl⟩ : syracuseStep 5545637 = 1039807) (by norm_num)
theorem B2465453 : Blo 1642020 2465453 := bbase (se 3 (by rfl) ⟨462272, by rfl⟩ : syracuseStep 2465453 = 924545) (by norm_num)
theorem B2465477 : Blo 1642020 2465477 := bbase (se 4 (by rfl) ⟨231138, by rfl⟩ : syracuseStep 2465477 = 462277) (by norm_num)
theorem B2465501 : Blo 1642020 2465501 := bbase (se 3 (by rfl) ⟨462281, by rfl⟩ : syracuseStep 2465501 = 924563) (by norm_num)
theorem B5922533 : Blo 1642020 5922533 := bbase (se 4 (by rfl) ⟨555237, by rfl⟩ : syracuseStep 5922533 = 1110475) (by norm_num)
theorem B4161253 : Blo 1642020 4161253 := bbase (se 4 (by rfl) ⟨390117, by rfl⟩ : syracuseStep 4161253 = 780235) (by norm_num)
theorem B2465525 : Blo 1642020 2465525 := bbase (se 5 (by rfl) ⟨115571, by rfl⟩ : syracuseStep 2465525 = 231143) (by norm_num)
theorem B2080505 : Blo 1642020 2080505 := bbase (se 2 (by rfl) ⟨780189, by rfl⟩ : syracuseStep 2080505 = 1560379) (by norm_num)
theorem B2465549 : Blo 1642020 2465549 := bbase (se 3 (by rfl) ⟨462290, by rfl⟩ : syracuseStep 2465549 = 924581) (by norm_num)
theorem B3120925 : Blo 1642020 3120925 := bbase (se 3 (by rfl) ⟨585173, by rfl⟩ : syracuseStep 3120925 = 1170347) (by norm_num)
theorem B2465573 : Blo 1642020 2465573 := bbase (se 4 (by rfl) ⟨231147, by rfl⟩ : syracuseStep 2465573 = 462295) (by norm_num)
theorem B2080561 : Blo 1642020 2080561 := bbase (se 2 (by rfl) ⟨780210, by rfl⟩ : syracuseStep 2080561 = 1560421) (by norm_num)
theorem B2465597 : Blo 1642020 2465597 := bbase (se 3 (by rfl) ⟨462299, by rfl⟩ : syracuseStep 2465597 = 924599) (by norm_num)
theorem B3948365 : Blo 1642020 3948365 := bbase (se 3 (by rfl) ⟨740318, by rfl⟩ : syracuseStep 3948365 = 1480637) (by norm_num)
theorem B2465621 : Blo 1642020 2465621 := bbase (se 9 (by rfl) ⟨7223, by rfl⟩ : syracuseStep 2465621 = 14447) (by norm_num)
theorem B4161365 : Blo 1642020 4161365 := bbase (se 9 (by rfl) ⟨12191, by rfl⟩ : syracuseStep 4161365 = 24383) (by norm_num)
theorem B2465645 : Blo 1642020 2465645 := bbase (se 3 (by rfl) ⟨462308, by rfl⟩ : syracuseStep 2465645 = 924617) (by norm_num)
theorem B2465669 : Blo 1642020 2465669 := bbase (se 4 (by rfl) ⟨231156, by rfl⟩ : syracuseStep 2465669 = 462313) (by norm_num)
theorem B2080657 : Blo 1642020 2080657 := bbase (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) (by norm_num)
theorem B2465693 : Blo 1642020 2465693 := bbase (se 3 (by rfl) ⟨462317, by rfl⟩ : syracuseStep 2465693 = 924635) (by norm_num)
theorem B2465717 : Blo 1642020 2465717 := bbase (se 5 (by rfl) ⟨115580, by rfl⟩ : syracuseStep 2465717 = 231161) (by norm_num)
theorem B2465741 : Blo 1642020 2465741 := bbase (se 3 (by rfl) ⟨462326, by rfl⟩ : syracuseStep 2465741 = 924653) (by norm_num)
theorem B2465765 : Blo 1642020 2465765 := bbase (se 4 (by rfl) ⟨231165, by rfl⟩ : syracuseStep 2465765 = 462331) (by norm_num)
theorem B14032885 : Blo 1642020 14032885 := bbase (se 5 (by rfl) ⟨657791, by rfl⟩ : syracuseStep 14032885 = 1315583) (by norm_num)
theorem B3694589 : Blo 1642020 3694589 := bbase (se 3 (by rfl) ⟨692735, by rfl⟩ : syracuseStep 3694589 = 1385471) (by norm_num)
theorem B2465795 : Blo 1642020 2465795 := bstep (se 1 (by rfl) ⟨1849346, by rfl⟩ : syracuseStep 2465795 = 3698693) B3698693
theorem B2465825 : Blo 1642020 2465825 := bstep (se 2 (by rfl) ⟨924684, by rfl⟩ : syracuseStep 2465825 = 1849369) B1849369
theorem B2465843 : Blo 1642020 2465843 := bstep (se 1 (by rfl) ⟨1849382, by rfl⟩ : syracuseStep 2465843 = 3698765) B3698765
theorem B4677709 : Blo 1642020 4677709 := bstep (se 3 (by rfl) ⟨877070, by rfl⟩ : syracuseStep 4677709 = 1754141) B1754141
theorem B2465873 : Blo 1642020 2465873 := bstep (se 2 (by rfl) ⟨924702, by rfl⟩ : syracuseStep 2465873 = 1849405) B1849405
theorem B2465891 : Blo 1642020 2465891 := bstep (se 1 (by rfl) ⟨1849418, by rfl⟩ : syracuseStep 2465891 = 3698837) B3698837
theorem B2465921 : Blo 1642020 2465921 := bstep (se 2 (by rfl) ⟨924720, by rfl⟩ : syracuseStep 2465921 = 1849441) B1849441
theorem B2465939 : Blo 1642020 2465939 := bstep (se 1 (by rfl) ⟨1849454, by rfl⟩ : syracuseStep 2465939 = 3698909) B3698909
theorem B3694769 : Blo 1642020 3694769 := bstep (se 2 (by rfl) ⟨1385538, by rfl⟩ : syracuseStep 3694769 = 2771077) B2771077
theorem B2465969 : Blo 1642020 2465969 := bstep (se 2 (by rfl) ⟨924738, by rfl⟩ : syracuseStep 2465969 = 1849477) B1849477
theorem B3694787 : Blo 1642020 3694787 := bstep (se 1 (by rfl) ⟨2771090, by rfl⟩ : syracuseStep 3694787 = 5542181) B5542181
theorem B2465987 : Blo 1642020 2465987 := bstep (se 1 (by rfl) ⟨1849490, by rfl⟩ : syracuseStep 2465987 = 3698981) B3698981
theorem B7020749 : Blo 1642020 7020749 := bstep (se 3 (by rfl) ⟨1316390, by rfl⟩ : syracuseStep 7020749 = 2632781) B2632781
theorem B2466017 : Blo 1642020 2466017 := bstep (se 2 (by rfl) ⟨924756, by rfl⟩ : syracuseStep 2466017 = 1849513) B1849513
theorem B5546285 : Blo 1642020 5546285 := bstep (se 3 (by rfl) ⟨1039928, by rfl⟩ : syracuseStep 5546285 = 2079857) B2079857
theorem B22470965 : Blo 1642020 22470965 := bstep (se 5 (by rfl) ⟨1053326, by rfl⟩ : syracuseStep 22470965 = 2106653) B2106653
theorem B29991221 : Blo 1642020 29991221 := bstep (se 5 (by rfl) ⟨1405838, by rfl⟩ : syracuseStep 29991221 = 2811677) B2811677
theorem B4743505 : Blo 1642020 4743505 := bstep (se 2 (by rfl) ⟨1778814, by rfl⟩ : syracuseStep 4743505 = 3557629) B3557629
theorem B5546339 : Blo 1642020 5546339 := bstep (se 1 (by rfl) ⟨4159754, by rfl⟩ : syracuseStep 5546339 = 8319509) B8319509
theorem B2498915 : Blo 1642020 2498915 := bstep (se 1 (by rfl) ⟨1874186, by rfl⟩ : syracuseStep 2498915 = 3748373) B3748373
theorem B3695057 : Blo 1642020 3695057 := bstep (se 2 (by rfl) ⟨1385646, by rfl⟩ : syracuseStep 3695057 = 2771293) B2771293
theorem B3695075 : Blo 1642020 3695075 := bstep (se 1 (by rfl) ⟨2771306, by rfl⟩ : syracuseStep 3695075 = 5542613) B5542613
theorem B16007651 : Blo 1642020 16007651 := bstep (se 1 (by rfl) ⟨12005738, by rfl⟩ : syracuseStep 16007651 = 24011477) B24011477
theorem B1688131 : Blo 1642020 1688131 := bstep (se 1 (by rfl) ⟨1266098, by rfl⟩ : syracuseStep 1688131 = 2532197) B2532197
theorem B5546609 : Blo 1642020 5546609 := bstep (se 2 (by rfl) ⟨2079978, by rfl⟩ : syracuseStep 5546609 = 4159957) B4159957
theorem B6169229 : Blo 1642020 6169229 := bstep (se 3 (by rfl) ⟨1156730, by rfl⟩ : syracuseStep 6169229 = 2313461) B2313461
theorem B5923469 : Blo 1642020 5923469 := bstep (se 3 (by rfl) ⟨1110650, by rfl⟩ : syracuseStep 5923469 = 2221301) B2221301
theorem B2220691 : Blo 1642020 2220691 := bstep (se 1 (by rfl) ⟨1665518, by rfl⟩ : syracuseStep 2220691 = 3331037) B3331037
theorem B2630321 : Blo 1642020 2630321 := bstep (se 2 (by rfl) ⟨986370, by rfl⟩ : syracuseStep 2630321 = 1972741) B1972741
theorem B11838149 : Blo 1642020 11838149 := bstep (se 4 (by rfl) ⟨1109826, by rfl⟩ : syracuseStep 11838149 = 2219653) B2219653
theorem B3695345 : Blo 1642020 3695345 := bstep (se 2 (by rfl) ⟨1385754, by rfl⟩ : syracuseStep 3695345 = 2771509) B2771509
theorem B3695363 : Blo 1642020 3695363 := bstep (se 1 (by rfl) ⟨2771522, by rfl⟩ : syracuseStep 3695363 = 5543045) B5543045
theorem B2630513 : Blo 1642020 2630513 := bstep (se 2 (by rfl) ⟨986442, by rfl⟩ : syracuseStep 2630513 = 1972885) B1972885
theorem B3695633 : Blo 1642020 3695633 := bstep (se 2 (by rfl) ⟨1385862, by rfl⟩ : syracuseStep 3695633 = 2771725) B2771725
theorem B3695651 : Blo 1642020 3695651 := bstep (se 1 (by rfl) ⟨2771738, by rfl⟩ : syracuseStep 3695651 = 5543477) B5543477
theorem B3376163 : Blo 1642020 3376163 := bstep (se 1 (by rfl) ⟨2532122, by rfl⟩ : syracuseStep 3376163 = 5064245) B5064245
theorem B5334083 : Blo 1642020 5334083 := bstep (se 1 (by rfl) ⟨4000562, by rfl⟩ : syracuseStep 5334083 = 8001125) B8001125
theorem B1754179 : Blo 1642020 1754179 := bstep (se 1 (by rfl) ⟨1315634, by rfl⟩ : syracuseStep 1754179 = 2631269) B2631269
theorem B2221171 : Blo 1642020 2221171 := bstep (se 1 (by rfl) ⟨1665878, by rfl⟩ : syracuseStep 2221171 = 3331757) B3331757
theorem B5547149 : Blo 1642020 5547149 := bstep (se 3 (by rfl) ⟨1040090, by rfl⟩ : syracuseStep 5547149 = 2080181) B2080181
theorem B5547203 : Blo 1642020 5547203 := bstep (se 1 (by rfl) ⟨4160402, by rfl⟩ : syracuseStep 5547203 = 8320805) B8320805
theorem B9356579 : Blo 1642020 9356579 := bstep (se 1 (by rfl) ⟨7017434, by rfl⟩ : syracuseStep 9356579 = 14034869) B14034869
theorem B3695921 : Blo 1642020 3695921 := bstep (se 2 (by rfl) ⟨1385970, by rfl⟩ : syracuseStep 3695921 = 2771941) B2771941
theorem B3851569 : Blo 1642020 3851569 := bstep (se 2 (by rfl) ⟨1444338, by rfl⟩ : syracuseStep 3851569 = 2888677) B2888677
theorem B3695939 : Blo 1642020 3695939 := bstep (se 1 (by rfl) ⟨2771954, by rfl⟩ : syracuseStep 3695939 = 5543909) B5543909
theorem B7898573 : Blo 1642020 7898573 := bstep (se 3 (by rfl) ⟨1480982, by rfl⟩ : syracuseStep 7898573 = 2961965) B2961965
theorem B5547473 : Blo 1642020 5547473 := bstep (se 2 (by rfl) ⟨2080302, by rfl⟩ : syracuseStep 5547473 = 4160605) B4160605
theorem B3556867 : Blo 1642020 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B3507761 : Blo 1642020 3507761 := bstep (se 2 (by rfl) ⟨1315410, by rfl⟩ : syracuseStep 3507761 = 2630821) B2630821
theorem B3696209 : Blo 1642020 3696209 := bstep (se 2 (by rfl) ⟨1386078, by rfl⟩ : syracuseStep 3696209 = 2772157) B2772157
theorem B3696227 : Blo 1642020 3696227 := bstep (se 1 (by rfl) ⟨2772170, by rfl⟩ : syracuseStep 3696227 = 5544341) B5544341
theorem B10528355 : Blo 1642020 10528355 := bstep (se 1 (by rfl) ⟨7896266, by rfl⟩ : syracuseStep 10528355 = 15792533) B15792533
theorem B4998829 : Blo 1642020 4998829 := bstep (se 3 (by rfl) ⟨937280, by rfl⟩ : syracuseStep 4998829 = 1874561) B1874561
theorem B8316593 : Blo 1642020 8316593 := bstep (se 2 (by rfl) ⟨3118722, by rfl⟩ : syracuseStep 8316593 = 6237445) B6237445
theorem B2221777 : Blo 1642020 2221777 := bstep (se 2 (by rfl) ⟨833166, by rfl⟩ : syracuseStep 2221777 = 1666333) B1666333
theorem B7022321 : Blo 1642020 7022321 := bstep (se 2 (by rfl) ⟨2633370, by rfl⟩ : syracuseStep 7022321 = 5266741) B5266741
theorem B6326029 : Blo 1642020 6326029 := bstep (se 3 (by rfl) ⟨1186130, by rfl⟩ : syracuseStep 6326029 = 2372261) B2372261
theorem B4998925 : Blo 1642020 4998925 := bstep (se 3 (by rfl) ⟨937298, by rfl⟩ : syracuseStep 4998925 = 1874597) B1874597
theorem B4679441 : Blo 1642020 4679441 := bstep (se 2 (by rfl) ⟨1754790, by rfl⟩ : syracuseStep 4679441 = 3509581) B3509581
theorem B3696497 : Blo 1642020 3696497 := bstep (se 2 (by rfl) ⟨1386186, by rfl⟩ : syracuseStep 3696497 = 2772373) B2772373
theorem B3696515 : Blo 1642020 3696515 := bstep (se 1 (by rfl) ⟨2772386, by rfl⟩ : syracuseStep 3696515 = 5544773) B5544773
theorem B4679633 : Blo 1642020 4679633 := bstep (se 2 (by rfl) ⟨1754862, by rfl⟩ : syracuseStep 4679633 = 3509725) B3509725
theorem B2770915 : Blo 1642020 2770915 := bstep (se 1 (by rfl) ⟨2078186, by rfl⟩ : syracuseStep 2770915 = 4156373) B4156373
theorem B5548013 : Blo 1642020 5548013 := bstep (se 3 (by rfl) ⟨1040252, by rfl⟩ : syracuseStep 5548013 = 2080505) B2080505
theorem B7112717 : Blo 1642020 7112717 := bstep (se 3 (by rfl) ⟨1333634, by rfl⟩ : syracuseStep 7112717 = 2667269) B2667269
theorem B5548067 : Blo 1642020 5548067 := bstep (se 1 (by rfl) ⟨4161050, by rfl⟩ : syracuseStep 5548067 = 8322101) B8322101
theorem B2771057 : Blo 1642020 2771057 := bstep (se 2 (by rfl) ⟨1039146, by rfl⟩ : syracuseStep 2771057 = 2078293) B2078293
theorem B11241613 : Blo 1642020 11241613 := bstep (se 3 (by rfl) ⟨2107802, by rfl⟩ : syracuseStep 11241613 = 4215605) B4215605
theorem B3696785 : Blo 1642020 3696785 := bstep (se 2 (by rfl) ⟨1386294, by rfl⟩ : syracuseStep 3696785 = 2772589) B2772589
theorem B2631827 : Blo 1642020 2631827 := bstep (se 1 (by rfl) ⟨1973870, by rfl⟩ : syracuseStep 2631827 = 3947741) B3947741
theorem B3696803 : Blo 1642020 3696803 := bstep (se 1 (by rfl) ⟨2772602, by rfl⟩ : syracuseStep 3696803 = 5545205) B5545205
theorem B2771185 : Blo 1642020 2771185 := bstep (se 2 (by rfl) ⟨1039194, by rfl⟩ : syracuseStep 2771185 = 2078389) B2078389
theorem B2771219 : Blo 1642020 2771219 := bstep (se 1 (by rfl) ⟨2078414, by rfl⟩ : syracuseStep 2771219 = 4156829) B4156829
theorem B5548337 : Blo 1642020 5548337 := bstep (se 2 (by rfl) ⟨2080626, by rfl⟩ : syracuseStep 5548337 = 4161253) B4161253
theorem B3557699 : Blo 1642020 3557699 := bstep (se 1 (by rfl) ⟨2668274, by rfl⟩ : syracuseStep 3557699 = 5336549) B5336549
theorem B2533699 : Blo 1642020 2533699 := bstep (se 1 (by rfl) ⟨1900274, by rfl⟩ : syracuseStep 2533699 = 3800549) B3800549
theorem B2632051 : Blo 1642020 2632051 := bstep (se 1 (by rfl) ⟨1974038, by rfl⟩ : syracuseStep 2632051 = 3948077) B3948077
theorem B2771347 : Blo 1642020 2771347 := bstep (se 1 (by rfl) ⟨2078510, by rfl⟩ : syracuseStep 2771347 = 4157021) B4157021
theorem B3697073 : Blo 1642020 3697073 := bstep (se 2 (by rfl) ⟨1386402, by rfl⟩ : syracuseStep 3697073 = 2772805) B2772805
theorem B2632115 : Blo 1642020 2632115 := bstep (se 1 (by rfl) ⟨1974086, by rfl⟩ : syracuseStep 2632115 = 3948173) B3948173
theorem B3697091 : Blo 1642020 3697091 := bstep (se 1 (by rfl) ⟨2772818, by rfl⟩ : syracuseStep 3697091 = 5545637) B5545637
theorem B19982861 : Blo 1642020 19982861 := bstep (se 3 (by rfl) ⟨3746786, by rfl⟩ : syracuseStep 19982861 = 7493573) B7493573
theorem B5065229 : Blo 1642020 5065229 := bstep (se 3 (by rfl) ⟨949730, by rfl⟩ : syracuseStep 5065229 = 1899461) B1899461
theorem B2771489 : Blo 1642020 2771489 := bstep (se 2 (by rfl) ⟨1039308, by rfl⟩ : syracuseStep 2771489 = 2078617) B2078617
theorem B2632243 : Blo 1642020 2632243 := bstep (se 1 (by rfl) ⟨1974182, by rfl⟩ : syracuseStep 2632243 = 3948365) B3948365
theorem B2771617 : Blo 1642020 2771617 := bstep (se 2 (by rfl) ⟨1039356, by rfl⟩ : syracuseStep 2771617 = 2078713) B2078713
theorem B4442797 : Blo 1642020 4442797 := bstep (se 3 (by rfl) ⟨833024, by rfl⟩ : syracuseStep 4442797 = 1666049) B1666049
theorem B2771651 : Blo 1642020 2771651 := bstep (se 1 (by rfl) ⟨2078738, by rfl⟩ : syracuseStep 2771651 = 4157477) B4157477
theorem B3697361 : Blo 1642020 3697361 := bstep (se 2 (by rfl) ⟨1386510, by rfl⟩ : syracuseStep 3697361 = 2773021) B2773021
theorem B3697379 : Blo 1642020 3697379 := bstep (se 1 (by rfl) ⟨2773034, by rfl⟩ : syracuseStep 3697379 = 5546069) B5546069
theorem B4442861 : Blo 1642020 4442861 := bstep (se 3 (by rfl) ⟨833036, by rfl⟩ : syracuseStep 4442861 = 1666073) B1666073
theorem B9988849 : Blo 1642020 9988849 := bstep (se 2 (by rfl) ⟨3745818, by rfl⟩ : syracuseStep 9988849 = 7491637) B7491637
theorem B10529585 : Blo 1642020 10529585 := bstep (se 2 (by rfl) ⟨3948594, by rfl⟩ : syracuseStep 10529585 = 7897189) B7897189
theorem B2771779 : Blo 1642020 2771779 := bstep (se 1 (by rfl) ⟨2078834, by rfl⟩ : syracuseStep 2771779 = 4157669) B4157669
theorem B5999437 : Blo 1642020 5999437 := bstep (se 3 (by rfl) ⟨1124894, by rfl⟩ : syracuseStep 5999437 = 2249789) B2249789
theorem B4680625 : Blo 1642020 4680625 := bstep (se 2 (by rfl) ⟨1755234, by rfl⟩ : syracuseStep 4680625 = 3510469) B3510469
theorem B2771921 : Blo 1642020 2771921 := bstep (se 2 (by rfl) ⟨1039470, by rfl⟩ : syracuseStep 2771921 = 2078941) B2078941
theorem B3697649 : Blo 1642020 3697649 := bstep (se 2 (by rfl) ⟨1386618, by rfl⟩ : syracuseStep 3697649 = 2773237) B2773237
theorem B3697667 : Blo 1642020 3697667 := bstep (se 1 (by rfl) ⟨2773250, by rfl⟩ : syracuseStep 3697667 = 5546501) B5546501
theorem B6237233 : Blo 1642020 6237233 := bstep (se 2 (by rfl) ⟨2338962, by rfl⟩ : syracuseStep 6237233 = 4677925) B4677925
theorem B2772049 : Blo 1642020 2772049 := bstep (se 2 (by rfl) ⟨1039518, by rfl⟩ : syracuseStep 2772049 = 2079037) B2079037
theorem B8318051 : Blo 1642020 8318051 := bstep (se 1 (by rfl) ⟨6238538, by rfl⟩ : syracuseStep 8318051 = 12477077) B12477077
theorem B2772083 : Blo 1642020 2772083 := bstep (se 1 (by rfl) ⟨2079062, by rfl⟩ : syracuseStep 2772083 = 4158125) B4158125
theorem B4680899 : Blo 1642020 4680899 := bstep (se 1 (by rfl) ⟨3510674, by rfl⟩ : syracuseStep 4680899 = 7021349) B7021349
theorem B2772211 : Blo 1642020 2772211 := bstep (se 1 (by rfl) ⟨2079158, by rfl⟩ : syracuseStep 2772211 = 4158317) B4158317
theorem B2632961 : Blo 1642020 2632961 := bstep (se 2 (by rfl) ⟨987360, by rfl⟩ : syracuseStep 2632961 = 1974721) B1974721
theorem B3697937 : Blo 1642020 3697937 := bstep (se 2 (by rfl) ⟨1386726, by rfl⟩ : syracuseStep 3697937 = 2773453) B2773453
theorem B3697955 : Blo 1642020 3697955 := bstep (se 1 (by rfl) ⟨2773466, by rfl⟩ : syracuseStep 3697955 = 5546933) B5546933
theorem B5262641 : Blo 1642020 5262641 := bstep (se 2 (by rfl) ⟨1973490, by rfl⟩ : syracuseStep 5262641 = 3946981) B3946981
theorem B31567157 : Blo 1642020 31567157 := bstep (se 5 (by rfl) ⟨1479710, by rfl⟩ : syracuseStep 31567157 = 2959421) B2959421
theorem B2772353 : Blo 1642020 2772353 := bstep (se 2 (by rfl) ⟨1039632, by rfl⟩ : syracuseStep 2772353 = 2079265) B2079265
theorem B2633089 : Blo 1642020 2633089 := bstep (se 2 (by rfl) ⟨987408, by rfl⟩ : syracuseStep 2633089 = 1974817) B1974817
theorem B4681091 : Blo 1642020 4681091 := bstep (se 1 (by rfl) ⟨3510818, by rfl⟩ : syracuseStep 4681091 = 7021637) B7021637
theorem B5262833 : Blo 1642020 5262833 := bstep (se 2 (by rfl) ⟨1973562, by rfl⟩ : syracuseStep 5262833 = 3947125) B3947125
theorem B2772481 : Blo 1642020 2772481 := bstep (se 2 (by rfl) ⟨1039680, by rfl⟩ : syracuseStep 2772481 = 2079361) B2079361
theorem B2772515 : Blo 1642020 2772515 := bstep (se 1 (by rfl) ⟨2079386, by rfl⟩ : syracuseStep 2772515 = 4158773) B4158773
theorem B3698225 : Blo 1642020 3698225 := bstep (se 2 (by rfl) ⟨1386834, by rfl⟩ : syracuseStep 3698225 = 2773669) B2773669
theorem B1642035 : Blo 1642020 1642035 := bstep (se 1 (by rfl) ⟨1231526, by rfl⟩ : syracuseStep 1642035 = 2463053) B2463053
theorem B1642051 : Blo 1642020 1642051 := bstep (se 1 (by rfl) ⟨1231538, by rfl⟩ : syracuseStep 1642051 = 2463077) B2463077
theorem B3698243 : Blo 1642020 3698243 := bstep (se 1 (by rfl) ⟨2773682, by rfl⟩ : syracuseStep 3698243 = 5547365) B5547365
theorem B1642067 : Blo 1642020 1642067 := bstep (se 1 (by rfl) ⟨1231550, by rfl⟩ : syracuseStep 1642067 = 2463101) B2463101
theorem B1642083 : Blo 1642020 1642083 := bstep (se 1 (by rfl) ⟨1231562, by rfl⟩ : syracuseStep 1642083 = 2463125) B2463125
theorem B4157041 : Blo 1642020 4157041 := bstep (se 2 (by rfl) ⟨1558890, by rfl⟩ : syracuseStep 4157041 = 3117781) B3117781
theorem B1642099 : Blo 1642020 1642099 := bstep (se 1 (by rfl) ⟨1231574, by rfl⟩ : syracuseStep 1642099 = 2463149) B2463149
theorem B1642115 : Blo 1642020 1642115 := bstep (se 1 (by rfl) ⟨1231586, by rfl⟩ : syracuseStep 1642115 = 2463173) B2463173
theorem B1642131 : Blo 1642020 1642131 := bstep (se 1 (by rfl) ⟨1231598, by rfl⟩ : syracuseStep 1642131 = 2463197) B2463197
theorem B1642147 : Blo 1642020 1642147 := bstep (se 1 (by rfl) ⟨1231610, by rfl⟩ : syracuseStep 1642147 = 2463221) B2463221
theorem B2772643 : Blo 1642020 2772643 := bstep (se 1 (by rfl) ⟨2079482, by rfl⟩ : syracuseStep 2772643 = 4158965) B4158965
theorem B1642163 : Blo 1642020 1642163 := bstep (se 1 (by rfl) ⟨1231622, by rfl⟩ : syracuseStep 1642163 = 2463245) B2463245
theorem B1642179 : Blo 1642020 1642179 := bstep (se 1 (by rfl) ⟨1231634, by rfl⟩ : syracuseStep 1642179 = 2463269) B2463269
theorem B1642195 : Blo 1642020 1642195 := bstep (se 1 (by rfl) ⟨1231646, by rfl⟩ : syracuseStep 1642195 = 2463293) B2463293
theorem B1642211 : Blo 1642020 1642211 := bstep (se 1 (by rfl) ⟨1231658, by rfl⟩ : syracuseStep 1642211 = 2463317) B2463317
theorem B1642227 : Blo 1642020 1642227 := bstep (se 1 (by rfl) ⟨1231670, by rfl⟩ : syracuseStep 1642227 = 2463341) B2463341
theorem B1642243 : Blo 1642020 1642243 := bstep (se 1 (by rfl) ⟨1231682, by rfl⟩ : syracuseStep 1642243 = 2463365) B2463365
theorem B1642259 : Blo 1642020 1642259 := bstep (se 1 (by rfl) ⟨1231694, by rfl⟩ : syracuseStep 1642259 = 2463389) B2463389
theorem B1642275 : Blo 1642020 1642275 := bstep (se 1 (by rfl) ⟨1231706, by rfl⟩ : syracuseStep 1642275 = 2463413) B2463413
theorem B6663971 : Blo 1642020 6663971 := bstep (se 1 (by rfl) ⟨4997978, by rfl⟩ : syracuseStep 6663971 = 9995957) B9995957
theorem B2772785 : Blo 1642020 2772785 := bstep (se 2 (by rfl) ⟨1039794, by rfl⟩ : syracuseStep 2772785 = 2079589) B2079589
theorem B1642291 : Blo 1642020 1642291 := bstep (se 1 (by rfl) ⟨1231718, by rfl⟩ : syracuseStep 1642291 = 2463437) B2463437
theorem B1642307 : Blo 1642020 1642307 := bstep (se 1 (by rfl) ⟨1231730, by rfl⟩ : syracuseStep 1642307 = 2463461) B2463461
theorem B2338627 : Blo 1642020 2338627 := bstep (se 1 (by rfl) ⟨1753970, by rfl⟩ : syracuseStep 2338627 = 3507941) B3507941
theorem B3698513 : Blo 1642020 3698513 := bstep (se 2 (by rfl) ⟨1386942, by rfl⟩ : syracuseStep 3698513 = 2773885) B2773885
theorem B1642323 : Blo 1642020 1642323 := bstep (se 1 (by rfl) ⟨1231742, by rfl⟩ : syracuseStep 1642323 = 2463485) B2463485
theorem B1642339 : Blo 1642020 1642339 := bstep (se 1 (by rfl) ⟨1231754, by rfl⟩ : syracuseStep 1642339 = 2463509) B2463509
theorem B7016291 : Blo 1642020 7016291 := bstep (se 1 (by rfl) ⟨5262218, by rfl⟩ : syracuseStep 7016291 = 10524437) B10524437
theorem B3698531 : Blo 1642020 3698531 := bstep (se 1 (by rfl) ⟨2773898, by rfl⟩ : syracuseStep 3698531 = 5547797) B5547797
theorem B1642355 : Blo 1642020 1642355 := bstep (se 1 (by rfl) ⟨1231766, by rfl⟩ : syracuseStep 1642355 = 2463533) B2463533
theorem B1642371 : Blo 1642020 1642371 := bstep (se 1 (by rfl) ⟨1231778, by rfl⟩ : syracuseStep 1642371 = 2463557) B2463557
theorem B4157315 : Blo 1642020 4157315 := bstep (se 1 (by rfl) ⟨3117986, by rfl⟩ : syracuseStep 4157315 = 6235973) B6235973
theorem B8318861 : Blo 1642020 8318861 := bstep (se 3 (by rfl) ⟨1559786, by rfl⟩ : syracuseStep 8318861 = 3119573) B3119573
theorem B1642387 : Blo 1642020 1642387 := bstep (se 1 (by rfl) ⟨1231790, by rfl⟩ : syracuseStep 1642387 = 2463581) B2463581
theorem B1642403 : Blo 1642020 1642403 := bstep (se 1 (by rfl) ⟨1231802, by rfl⟩ : syracuseStep 1642403 = 2463605) B2463605
theorem B2338723 : Blo 1642020 2338723 := bstep (se 1 (by rfl) ⟨1754042, by rfl⟩ : syracuseStep 2338723 = 3508085) B3508085
theorem B2772913 : Blo 1642020 2772913 := bstep (se 2 (by rfl) ⟨1039842, by rfl⟩ : syracuseStep 2772913 = 2079685) B2079685
theorem B1642419 : Blo 1642020 1642419 := bstep (se 1 (by rfl) ⟨1231814, by rfl⟩ : syracuseStep 1642419 = 2463629) B2463629
theorem B1642435 : Blo 1642020 1642435 := bstep (se 1 (by rfl) ⟨1231826, by rfl⟩ : syracuseStep 1642435 = 2463653) B2463653
theorem B1642451 : Blo 1642020 1642451 := bstep (se 1 (by rfl) ⟨1231838, by rfl⟩ : syracuseStep 1642451 = 2463677) B2463677
theorem B2772947 : Blo 1642020 2772947 := bstep (se 1 (by rfl) ⟨2079710, by rfl⟩ : syracuseStep 2772947 = 4159421) B4159421
theorem B1642467 : Blo 1642020 1642467 := bstep (se 1 (by rfl) ⟨1231850, by rfl⟩ : syracuseStep 1642467 = 2463701) B2463701
theorem B14028785 : Blo 1642020 14028785 := bstep (se 2 (by rfl) ⟨5260794, by rfl⟩ : syracuseStep 14028785 = 10521589) B10521589
theorem B1642483 : Blo 1642020 1642483 := bstep (se 1 (by rfl) ⟨1231862, by rfl⟩ : syracuseStep 1642483 = 2463725) B2463725
theorem B1847299 : Blo 1642020 1847299 := bstep (se 1 (by rfl) ⟨1385474, by rfl⟩ : syracuseStep 1847299 = 2770949) B2770949
theorem B1642499 : Blo 1642020 1642499 := bstep (se 1 (by rfl) ⟨1231874, by rfl⟩ : syracuseStep 1642499 = 2463749) B2463749
theorem B1642515 : Blo 1642020 1642515 := bstep (se 1 (by rfl) ⟨1231886, by rfl⟩ : syracuseStep 1642515 = 2463773) B2463773
theorem B1642531 : Blo 1642020 1642531 := bstep (se 1 (by rfl) ⟨1231898, by rfl⟩ : syracuseStep 1642531 = 2463797) B2463797
theorem B1642547 : Blo 1642020 1642547 := bstep (se 1 (by rfl) ⟨1231910, by rfl⟩ : syracuseStep 1642547 = 2463821) B2463821
theorem B4157507 : Blo 1642020 4157507 := bstep (se 1 (by rfl) ⟨3118130, by rfl⟩ : syracuseStep 4157507 = 6236261) B6236261
theorem B1642563 : Blo 1642020 1642563 := bstep (se 1 (by rfl) ⟨1231922, by rfl⟩ : syracuseStep 1642563 = 2463845) B2463845
theorem B15798341 : Blo 1642020 15798341 := bstep (se 4 (by rfl) ⟨1481094, by rfl⟩ : syracuseStep 15798341 = 2962189) B2962189
theorem B5541965 : Blo 1642020 5541965 := bstep (se 3 (by rfl) ⟨1039118, by rfl⟩ : syracuseStep 5541965 = 2078237) B2078237
theorem B1642579 : Blo 1642020 1642579 := bstep (se 1 (by rfl) ⟨1231934, by rfl⟩ : syracuseStep 1642579 = 2463869) B2463869
theorem B2773075 : Blo 1642020 2773075 := bstep (se 1 (by rfl) ⟨2079806, by rfl⟩ : syracuseStep 2773075 = 4159613) B4159613
theorem B1642595 : Blo 1642020 1642595 := bstep (se 1 (by rfl) ⟨1231946, by rfl⟩ : syracuseStep 1642595 = 2463893) B2463893
theorem B3698801 : Blo 1642020 3698801 := bstep (se 2 (by rfl) ⟨1387050, by rfl⟩ : syracuseStep 3698801 = 2774101) B2774101
theorem B1642611 : Blo 1642020 1642611 := bstep (se 1 (by rfl) ⟨1231958, by rfl⟩ : syracuseStep 1642611 = 2463917) B2463917
theorem B28471409 : Blo 1642020 28471409 := bstep (se 2 (by rfl) ⟨10676778, by rfl⟩ : syracuseStep 28471409 = 21353557) B21353557
theorem B5542019 : Blo 1642020 5542019 := bstep (se 1 (by rfl) ⟨4156514, by rfl⟩ : syracuseStep 5542019 = 8313029) B8313029
theorem B1642627 : Blo 1642020 1642627 := bstep (se 1 (by rfl) ⟨1231970, by rfl⟩ : syracuseStep 1642627 = 2463941) B2463941
theorem B3698819 : Blo 1642020 3698819 := bstep (se 1 (by rfl) ⟨2774114, by rfl⟩ : syracuseStep 3698819 = 5548229) B5548229
theorem B1847443 : Blo 1642020 1847443 := bstep (se 1 (by rfl) ⟨1385582, by rfl⟩ : syracuseStep 1847443 = 2771165) B2771165
theorem B1642643 : Blo 1642020 1642643 := bstep (se 1 (by rfl) ⟨1231982, by rfl⟩ : syracuseStep 1642643 = 2463965) B2463965
theorem B1642659 : Blo 1642020 1642659 := bstep (se 1 (by rfl) ⟨1231994, by rfl⟩ : syracuseStep 1642659 = 2463989) B2463989
theorem B1642675 : Blo 1642020 1642675 := bstep (se 1 (by rfl) ⟨1232006, by rfl⟩ : syracuseStep 1642675 = 2464013) B2464013
theorem B1642691 : Blo 1642020 1642691 := bstep (se 1 (by rfl) ⟨1232018, by rfl⟩ : syracuseStep 1642691 = 2464037) B2464037
theorem B1642707 : Blo 1642020 1642707 := bstep (se 1 (by rfl) ⟨1232030, by rfl⟩ : syracuseStep 1642707 = 2464061) B2464061
theorem B2773217 : Blo 1642020 2773217 := bstep (se 2 (by rfl) ⟨1039956, by rfl⟩ : syracuseStep 2773217 = 2079913) B2079913
theorem B1642723 : Blo 1642020 1642723 := bstep (se 1 (by rfl) ⟨1232042, by rfl⟩ : syracuseStep 1642723 = 2464085) B2464085
theorem B7893233 : Blo 1642020 7893233 := bstep (se 2 (by rfl) ⟨2959962, by rfl⟩ : syracuseStep 7893233 = 5919925) B5919925
theorem B1642739 : Blo 1642020 1642739 := bstep (se 1 (by rfl) ⟨1232054, by rfl⟩ : syracuseStep 1642739 = 2464109) B2464109
theorem B1642755 : Blo 1642020 1642755 := bstep (se 1 (by rfl) ⟨1232066, by rfl⟩ : syracuseStep 1642755 = 2464133) B2464133
theorem B3510545 : Blo 1642020 3510545 := bstep (se 2 (by rfl) ⟨1316454, by rfl⟩ : syracuseStep 3510545 = 2632909) B2632909
theorem B1642771 : Blo 1642020 1642771 := bstep (se 1 (by rfl) ⟨1232078, by rfl⟩ : syracuseStep 1642771 = 2464157) B2464157
theorem B1847587 : Blo 1642020 1847587 := bstep (se 1 (by rfl) ⟨1385690, by rfl⟩ : syracuseStep 1847587 = 2771381) B2771381
theorem B1642787 : Blo 1642020 1642787 := bstep (se 1 (by rfl) ⟨1232090, by rfl⟩ : syracuseStep 1642787 = 2464181) B2464181
theorem B5132593 : Blo 1642020 5132593 := bstep (se 2 (by rfl) ⟨1924722, by rfl⟩ : syracuseStep 5132593 = 3849445) B3849445
theorem B1642803 : Blo 1642020 1642803 := bstep (se 1 (by rfl) ⟨1232102, by rfl⟩ : syracuseStep 1642803 = 2464205) B2464205
theorem B3117379 : Blo 1642020 3117379 := bstep (se 1 (by rfl) ⟨2338034, by rfl⟩ : syracuseStep 3117379 = 4676069) B4676069
theorem B1642819 : Blo 1642020 1642819 := bstep (se 1 (by rfl) ⟨1232114, by rfl⟩ : syracuseStep 1642819 = 2464229) B2464229
theorem B2847059 : Blo 1642020 2847059 := bstep (se 1 (by rfl) ⟨2135294, by rfl⟩ : syracuseStep 2847059 = 4270589) B4270589
theorem B1642835 : Blo 1642020 1642835 := bstep (se 1 (by rfl) ⟨1232126, by rfl⟩ : syracuseStep 1642835 = 2464253) B2464253
theorem B2773345 : Blo 1642020 2773345 := bstep (se 2 (by rfl) ⟨1040004, by rfl⟩ : syracuseStep 2773345 = 2080009) B2080009
theorem B1642851 : Blo 1642020 1642851 := bstep (se 1 (by rfl) ⟨1232138, by rfl⟩ : syracuseStep 1642851 = 2464277) B2464277
theorem B1642867 : Blo 1642020 1642867 := bstep (se 1 (by rfl) ⟨1232150, by rfl⟩ : syracuseStep 1642867 = 2464301) B2464301
theorem B1642883 : Blo 1642020 1642883 := bstep (se 1 (by rfl) ⟨1232162, by rfl⟩ : syracuseStep 1642883 = 2464325) B2464325
theorem B2773379 : Blo 1642020 2773379 := bstep (se 1 (by rfl) ⟨2080034, by rfl⟩ : syracuseStep 2773379 = 4160069) B4160069
theorem B5542289 : Blo 1642020 5542289 := bstep (se 2 (by rfl) ⟨2078358, by rfl⟩ : syracuseStep 5542289 = 4156717) B4156717
theorem B1642899 : Blo 1642020 1642899 := bstep (se 1 (by rfl) ⟨1232174, by rfl⟩ : syracuseStep 1642899 = 2464349) B2464349
theorem B2339219 : Blo 1642020 2339219 := bstep (se 1 (by rfl) ⟨1754414, by rfl⟩ : syracuseStep 2339219 = 3508829) B3508829
theorem B1642915 : Blo 1642020 1642915 := bstep (se 1 (by rfl) ⟨1232186, by rfl⟩ : syracuseStep 1642915 = 2464373) B2464373
theorem B1847731 : Blo 1642020 1847731 := bstep (se 1 (by rfl) ⟨1385798, by rfl⟩ : syracuseStep 1847731 = 2771597) B2771597
theorem B1642931 : Blo 1642020 1642931 := bstep (se 1 (by rfl) ⟨1232198, by rfl⟩ : syracuseStep 1642931 = 2464397) B2464397
theorem B1642947 : Blo 1642020 1642947 := bstep (se 1 (by rfl) ⟨1232210, by rfl⟩ : syracuseStep 1642947 = 2464421) B2464421
theorem B9359813 : Blo 1642020 9359813 := bstep (se 4 (by rfl) ⟨877482, by rfl⟩ : syracuseStep 9359813 = 1754965) B1754965
theorem B12480965 : Blo 1642020 12480965 := bstep (se 4 (by rfl) ⟨1170090, by rfl⟩ : syracuseStep 12480965 = 2340181) B2340181
theorem B1642963 : Blo 1642020 1642963 := bstep (se 1 (by rfl) ⟨1232222, by rfl⟩ : syracuseStep 1642963 = 2464445) B2464445
theorem B1642979 : Blo 1642020 1642979 := bstep (se 1 (by rfl) ⟨1232234, by rfl⟩ : syracuseStep 1642979 = 2464469) B2464469
theorem B6238691 : Blo 1642020 6238691 := bstep (se 1 (by rfl) ⟨4679018, by rfl⟩ : syracuseStep 6238691 = 9358037) B9358037
theorem B1642995 : Blo 1642020 1642995 := bstep (se 1 (by rfl) ⟨1232246, by rfl⟩ : syracuseStep 1642995 = 2464493) B2464493
theorem B1643011 : Blo 1642020 1643011 := bstep (se 1 (by rfl) ⟨1232258, by rfl⟩ : syracuseStep 1643011 = 2464517) B2464517
theorem B2773507 : Blo 1642020 2773507 := bstep (se 1 (by rfl) ⟨2080130, by rfl⟩ : syracuseStep 2773507 = 4160261) B4160261
theorem B1643027 : Blo 1642020 1643027 := bstep (se 1 (by rfl) ⟨1232270, by rfl⟩ : syracuseStep 1643027 = 2464541) B2464541
theorem B1643043 : Blo 1642020 1643043 := bstep (se 1 (by rfl) ⟨1232282, by rfl⟩ : syracuseStep 1643043 = 2464565) B2464565
theorem B1643059 : Blo 1642020 1643059 := bstep (se 1 (by rfl) ⟨1232294, by rfl⟩ : syracuseStep 1643059 = 2464589) B2464589
theorem B1847875 : Blo 1642020 1847875 := bstep (se 1 (by rfl) ⟨1385906, by rfl⟩ : syracuseStep 1847875 = 2771813) B2771813
theorem B1643075 : Blo 1642020 1643075 := bstep (se 1 (by rfl) ⟨1232306, by rfl⟩ : syracuseStep 1643075 = 2464613) B2464613
theorem B1643091 : Blo 1642020 1643091 := bstep (se 1 (by rfl) ⟨1232318, by rfl⟩ : syracuseStep 1643091 = 2464637) B2464637
theorem B1643107 : Blo 1642020 1643107 := bstep (se 1 (by rfl) ⟨1232330, by rfl⟩ : syracuseStep 1643107 = 2464661) B2464661
theorem B1643123 : Blo 1642020 1643123 := bstep (se 1 (by rfl) ⟨1232342, by rfl⟩ : syracuseStep 1643123 = 2464685) B2464685
theorem B1643139 : Blo 1642020 1643139 := bstep (se 1 (by rfl) ⟨1232354, by rfl⟩ : syracuseStep 1643139 = 2464709) B2464709
theorem B2773649 : Blo 1642020 2773649 := bstep (se 2 (by rfl) ⟨1040118, by rfl⟩ : syracuseStep 2773649 = 2080237) B2080237
theorem B1643155 : Blo 1642020 1643155 := bstep (se 1 (by rfl) ⟨1232366, by rfl⟩ : syracuseStep 1643155 = 2464733) B2464733
theorem B1643171 : Blo 1642020 1643171 := bstep (se 1 (by rfl) ⟨1232378, by rfl⟩ : syracuseStep 1643171 = 2464757) B2464757
theorem B1643187 : Blo 1642020 1643187 := bstep (se 1 (by rfl) ⟨1232390, by rfl⟩ : syracuseStep 1643187 = 2464781) B2464781
theorem B1643203 : Blo 1642020 1643203 := bstep (se 1 (by rfl) ⟨1232402, by rfl⟩ : syracuseStep 1643203 = 2464805) B2464805
theorem B1848019 : Blo 1642020 1848019 := bstep (se 1 (by rfl) ⟨1386014, by rfl⟩ : syracuseStep 1848019 = 2772029) B2772029
theorem B1643219 : Blo 1642020 1643219 := bstep (se 1 (by rfl) ⟨1232414, by rfl⟩ : syracuseStep 1643219 = 2464829) B2464829
theorem B1643235 : Blo 1642020 1643235 := bstep (se 1 (by rfl) ⟨1232426, by rfl⟩ : syracuseStep 1643235 = 2464853) B2464853
theorem B6099697 : Blo 1642020 6099697 := bstep (se 2 (by rfl) ⟨2287386, by rfl⟩ : syracuseStep 6099697 = 4574773) B4574773
theorem B1643251 : Blo 1642020 1643251 := bstep (se 1 (by rfl) ⟨1232438, by rfl⟩ : syracuseStep 1643251 = 2464877) B2464877
theorem B3117827 : Blo 1642020 3117827 := bstep (se 1 (by rfl) ⟨2338370, by rfl⟩ : syracuseStep 3117827 = 4676741) B4676741
theorem B1643267 : Blo 1642020 1643267 := bstep (se 1 (by rfl) ⟨1232450, by rfl⟩ : syracuseStep 1643267 = 2464901) B2464901
theorem B2773777 : Blo 1642020 2773777 := bstep (se 2 (by rfl) ⟨1040166, by rfl⟩ : syracuseStep 2773777 = 2080333) B2080333
theorem B1643283 : Blo 1642020 1643283 := bstep (se 1 (by rfl) ⟨1232462, by rfl⟩ : syracuseStep 1643283 = 2464925) B2464925
theorem B1643299 : Blo 1642020 1643299 := bstep (se 1 (by rfl) ⟨1232474, by rfl⟩ : syracuseStep 1643299 = 2464949) B2464949
theorem B1643315 : Blo 1642020 1643315 := bstep (se 1 (by rfl) ⟨1232486, by rfl⟩ : syracuseStep 1643315 = 2464973) B2464973
theorem B2773811 : Blo 1642020 2773811 := bstep (se 1 (by rfl) ⟨2080358, by rfl⟩ : syracuseStep 2773811 = 4160717) B4160717
theorem B1643331 : Blo 1642020 1643331 := bstep (se 1 (by rfl) ⟨1232498, by rfl⟩ : syracuseStep 1643331 = 2464997) B2464997
theorem B1643347 : Blo 1642020 1643347 := bstep (se 1 (by rfl) ⟨1232510, by rfl⟩ : syracuseStep 1643347 = 2465021) B2465021
theorem B1848163 : Blo 1642020 1848163 := bstep (se 1 (by rfl) ⟨1386122, by rfl⟩ : syracuseStep 1848163 = 2772245) B2772245
theorem B1643363 : Blo 1642020 1643363 := bstep (se 1 (by rfl) ⟨1232522, by rfl⟩ : syracuseStep 1643363 = 2465045) B2465045
theorem B2667377 : Blo 1642020 2667377 := bstep (se 2 (by rfl) ⟨1000266, by rfl⟩ : syracuseStep 2667377 = 2000533) B2000533
theorem B1643379 : Blo 1642020 1643379 := bstep (se 1 (by rfl) ⟨1232534, by rfl⟩ : syracuseStep 1643379 = 2465069) B2465069
theorem B1643395 : Blo 1642020 1643395 := bstep (se 1 (by rfl) ⟨1232546, by rfl⟩ : syracuseStep 1643395 = 2465093) B2465093
theorem B9360269 : Blo 1642020 9360269 := bstep (se 3 (by rfl) ⟨1755050, by rfl⟩ : syracuseStep 9360269 = 3510101) B3510101
theorem B1643411 : Blo 1642020 1643411 := bstep (se 1 (by rfl) ⟨1232558, by rfl⟩ : syracuseStep 1643411 = 2465117) B2465117
theorem B1643427 : Blo 1642020 1643427 := bstep (se 1 (by rfl) ⟨1232570, by rfl⟩ : syracuseStep 1643427 = 2465141) B2465141
theorem B5542829 : Blo 1642020 5542829 := bstep (se 3 (by rfl) ⟨1039280, by rfl⟩ : syracuseStep 5542829 = 2078561) B2078561
theorem B1643443 : Blo 1642020 1643443 := bstep (se 1 (by rfl) ⟨1232582, by rfl⟩ : syracuseStep 1643443 = 2465165) B2465165
theorem B2773939 : Blo 1642020 2773939 := bstep (se 1 (by rfl) ⟨2080454, by rfl⟩ : syracuseStep 2773939 = 4160909) B4160909
theorem B1643459 : Blo 1642020 1643459 := bstep (se 1 (by rfl) ⟨1232594, by rfl⟩ : syracuseStep 1643459 = 2465189) B2465189
theorem B1643475 : Blo 1642020 1643475 := bstep (se 1 (by rfl) ⟨1232606, by rfl⟩ : syracuseStep 1643475 = 2465213) B2465213
theorem B5542883 : Blo 1642020 5542883 := bstep (se 1 (by rfl) ⟨4157162, by rfl⟩ : syracuseStep 5542883 = 8314325) B8314325
theorem B1643491 : Blo 1642020 1643491 := bstep (se 1 (by rfl) ⟨1232618, by rfl⟩ : syracuseStep 1643491 = 2465237) B2465237
theorem B4158449 : Blo 1642020 4158449 := bstep (se 2 (by rfl) ⟨1559418, by rfl⟩ : syracuseStep 4158449 = 3118837) B3118837
theorem B1848307 : Blo 1642020 1848307 := bstep (se 1 (by rfl) ⟨1386230, by rfl⟩ : syracuseStep 1848307 = 2772461) B2772461
theorem B1643507 : Blo 1642020 1643507 := bstep (se 1 (by rfl) ⟨1232630, by rfl⟩ : syracuseStep 1643507 = 2465261) B2465261
theorem B1643523 : Blo 1642020 1643523 := bstep (se 1 (by rfl) ⟨1232642, by rfl⟩ : syracuseStep 1643523 = 2465285) B2465285
theorem B9352205 : Blo 1642020 9352205 := bstep (se 3 (by rfl) ⟨1753538, by rfl⟩ : syracuseStep 9352205 = 3507077) B3507077
theorem B2339857 : Blo 1642020 2339857 := bstep (se 2 (by rfl) ⟨877446, by rfl⟩ : syracuseStep 2339857 = 1754893) B1754893
theorem B1643539 : Blo 1642020 1643539 := bstep (se 1 (by rfl) ⟨1232654, by rfl⟩ : syracuseStep 1643539 = 2465309) B2465309
theorem B3118115 : Blo 1642020 3118115 := bstep (se 1 (by rfl) ⟨2338586, by rfl⟩ : syracuseStep 3118115 = 4677173) B4677173
theorem B5919779 : Blo 1642020 5919779 := bstep (se 1 (by rfl) ⟨4439834, by rfl⟩ : syracuseStep 5919779 = 8879669) B8879669
theorem B4158499 : Blo 1642020 4158499 := bstep (se 1 (by rfl) ⟨3118874, by rfl⟩ : syracuseStep 4158499 = 6237749) B6237749
theorem B1643555 : Blo 1642020 1643555 := bstep (se 1 (by rfl) ⟨1232666, by rfl⟩ : syracuseStep 1643555 = 2465333) B2465333
theorem B1643571 : Blo 1642020 1643571 := bstep (se 1 (by rfl) ⟨1232678, by rfl⟩ : syracuseStep 1643571 = 2465357) B2465357
theorem B2774081 : Blo 1642020 2774081 := bstep (se 2 (by rfl) ⟨1040280, by rfl⟩ : syracuseStep 2774081 = 2080561) B2080561
theorem B1643587 : Blo 1642020 1643587 := bstep (se 1 (by rfl) ⟨1232690, by rfl⟩ : syracuseStep 1643587 = 2465381) B2465381
theorem B1643603 : Blo 1642020 1643603 := bstep (se 1 (by rfl) ⟨1232702, by rfl⟩ : syracuseStep 1643603 = 2465405) B2465405
theorem B1643619 : Blo 1642020 1643619 := bstep (se 1 (by rfl) ⟨1232714, by rfl⟩ : syracuseStep 1643619 = 2465429) B2465429
theorem B1643635 : Blo 1642020 1643635 := bstep (se 1 (by rfl) ⟨1232726, by rfl⟩ : syracuseStep 1643635 = 2465453) B2465453
theorem B1848451 : Blo 1642020 1848451 := bstep (se 1 (by rfl) ⟨1386338, by rfl⟩ : syracuseStep 1848451 = 2772677) B2772677
theorem B1643651 : Blo 1642020 1643651 := bstep (se 1 (by rfl) ⟨1232738, by rfl⟩ : syracuseStep 1643651 = 2465477) B2465477
theorem B18707597 : Blo 1642020 18707597 := bstep (se 3 (by rfl) ⟨3507674, by rfl⟩ : syracuseStep 18707597 = 7015349) B7015349
theorem B3945617 : Blo 1642020 3945617 := bstep (se 2 (by rfl) ⟨1479606, by rfl⟩ : syracuseStep 3945617 = 2959213) B2959213
theorem B1643667 : Blo 1642020 1643667 := bstep (se 1 (by rfl) ⟨1232750, by rfl⟩ : syracuseStep 1643667 = 2465501) B2465501
theorem B1643683 : Blo 1642020 1643683 := bstep (se 1 (by rfl) ⟨1232762, by rfl⟩ : syracuseStep 1643683 = 2465525) B2465525
theorem B4158641 : Blo 1642020 4158641 := bstep (se 2 (by rfl) ⟨1559490, by rfl⟩ : syracuseStep 4158641 = 3118981) B3118981
theorem B1643699 : Blo 1642020 1643699 := bstep (se 1 (by rfl) ⟨1232774, by rfl⟩ : syracuseStep 1643699 = 2465549) B2465549
theorem B2774209 : Blo 1642020 2774209 := bstep (se 2 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 2774209 = 2080657) B2080657
theorem B1643715 : Blo 1642020 1643715 := bstep (se 1 (by rfl) ⟨1232786, by rfl⟩ : syracuseStep 1643715 = 2465573) B2465573
theorem B10532045 : Blo 1642020 10532045 := bstep (se 3 (by rfl) ⟨1974758, by rfl⟩ : syracuseStep 10532045 = 3949517) B3949517
theorem B1643731 : Blo 1642020 1643731 := bstep (se 1 (by rfl) ⟨1232798, by rfl⟩ : syracuseStep 1643731 = 2465597) B2465597
theorem B11842787 : Blo 1642020 11842787 := bstep (se 1 (by rfl) ⟨8882090, by rfl⟩ : syracuseStep 11842787 = 17764181) B17764181
theorem B1643747 : Blo 1642020 1643747 := bstep (se 1 (by rfl) ⟨1232810, by rfl⟩ : syracuseStep 1643747 = 2465621) B2465621
theorem B2774243 : Blo 1642020 2774243 := bstep (se 1 (by rfl) ⟨2080682, by rfl⟩ : syracuseStep 2774243 = 4161365) B4161365
theorem B5543153 : Blo 1642020 5543153 := bstep (se 2 (by rfl) ⟨2078682, by rfl⟩ : syracuseStep 5543153 = 4157365) B4157365
theorem B1643763 : Blo 1642020 1643763 := bstep (se 1 (by rfl) ⟨1232822, by rfl⟩ : syracuseStep 1643763 = 2465645) B2465645
theorem B1643779 : Blo 1642020 1643779 := bstep (se 1 (by rfl) ⟨1232834, by rfl⟩ : syracuseStep 1643779 = 2465669) B2465669
theorem B1848595 : Blo 1642020 1848595 := bstep (se 1 (by rfl) ⟨1386446, by rfl⟩ : syracuseStep 1848595 = 2772893) B2772893
theorem B1643795 : Blo 1642020 1643795 := bstep (se 1 (by rfl) ⟨1232846, by rfl⟩ : syracuseStep 1643795 = 2465693) B2465693
theorem B1643811 : Blo 1642020 1643811 := bstep (se 1 (by rfl) ⟨1232858, by rfl⟩ : syracuseStep 1643811 = 2465717) B2465717
theorem B1643827 : Blo 1642020 1643827 := bstep (se 1 (by rfl) ⟨1232870, by rfl⟩ : syracuseStep 1643827 = 2465741) B2465741
theorem B2463041 : Blo 1642020 2463041 := bstep (se 2 (by rfl) ⟨923640, by rfl⟩ : syracuseStep 2463041 = 1847281) B1847281
theorem B1643843 : Blo 1642020 1643843 := bstep (se 1 (by rfl) ⟨1232882, by rfl⟩ : syracuseStep 1643843 = 2465765) B2465765
theorem B2463059 : Blo 1642020 2463059 := bstep (se 1 (by rfl) ⟨1847294, by rfl⟩ : syracuseStep 2463059 = 3694589) B3694589
theorem B1643859 : Blo 1642020 1643859 := bstep (se 1 (by rfl) ⟨1232894, by rfl⟩ : syracuseStep 1643859 = 2465789) B2465789
theorem B2340193 : Blo 1642020 2340193 := bstep (se 2 (by rfl) ⟨877572, by rfl⟩ : syracuseStep 2340193 = 1755145) B1755145
theorem B1643875 : Blo 1642020 1643875 := bstep (se 1 (by rfl) ⟨1232906, by rfl⟩ : syracuseStep 1643875 = 2465813) B2465813
theorem B2463089 : Blo 1642020 2463089 := bstep (se 2 (by rfl) ⟨923658, by rfl⟩ : syracuseStep 2463089 = 1847317) B1847317
theorem B1643891 : Blo 1642020 1643891 := bstep (se 1 (by rfl) ⟨1232918, by rfl⟩ : syracuseStep 1643891 = 2465837) B2465837
theorem B2463107 : Blo 1642020 2463107 := bstep (se 1 (by rfl) ⟨1847330, by rfl⟩ : syracuseStep 2463107 = 3694661) B3694661
theorem B1643907 : Blo 1642020 1643907 := bstep (se 1 (by rfl) ⟨1232930, by rfl⟩ : syracuseStep 1643907 = 2465861) B2465861
theorem B21050765 : Blo 1642020 21050765 := bstep (se 3 (by rfl) ⟨3947018, by rfl⟩ : syracuseStep 21050765 = 7894037) B7894037
theorem B1643923 : Blo 1642020 1643923 := bstep (se 1 (by rfl) ⟨1232942, by rfl⟩ : syracuseStep 1643923 = 2465885) B2465885
theorem B2463137 : Blo 1642020 2463137 := bstep (se 2 (by rfl) ⟨923676, by rfl⟩ : syracuseStep 2463137 = 1847353) B1847353
theorem B1848739 : Blo 1642020 1848739 := bstep (se 1 (by rfl) ⟨1386554, by rfl⟩ : syracuseStep 1848739 = 2773109) B2773109
theorem B1643939 : Blo 1642020 1643939 := bstep (se 1 (by rfl) ⟨1232954, by rfl⟩ : syracuseStep 1643939 = 2465909) B2465909
theorem B3945905 : Blo 1642020 3945905 := bstep (se 2 (by rfl) ⟨1479714, by rfl⟩ : syracuseStep 3945905 = 2959429) B2959429
theorem B2463155 : Blo 1642020 2463155 := bstep (se 1 (by rfl) ⟨1847366, by rfl⟩ : syracuseStep 2463155 = 3694733) B3694733
theorem B1643955 : Blo 1642020 1643955 := bstep (se 1 (by rfl) ⟨1232966, by rfl⟩ : syracuseStep 1643955 = 2465933) B2465933
theorem B1643971 : Blo 1642020 1643971 := bstep (se 1 (by rfl) ⟨1232978, by rfl⟩ : syracuseStep 1643971 = 2465957) B2465957
theorem B6239693 : Blo 1642020 6239693 := bstep (se 3 (by rfl) ⟨1169942, by rfl⟩ : syracuseStep 6239693 = 2339885) B2339885
theorem B2463185 : Blo 1642020 2463185 := bstep (se 2 (by rfl) ⟨923694, by rfl⟩ : syracuseStep 2463185 = 1847389) B1847389
theorem B1643987 : Blo 1642020 1643987 := bstep (se 1 (by rfl) ⟨1232990, by rfl⟩ : syracuseStep 1643987 = 2465981) B2465981
theorem B2463203 : Blo 1642020 2463203 := bstep (se 1 (by rfl) ⟨1847402, by rfl⟩ : syracuseStep 2463203 = 3694805) B3694805
theorem B1644003 : Blo 1642020 1644003 := bstep (se 1 (by rfl) ⟨1233002, by rfl⟩ : syracuseStep 1644003 = 2466005) B2466005
theorem B1644019 : Blo 1642020 1644019 := bstep (se 1 (by rfl) ⟨1233014, by rfl⟩ : syracuseStep 1644019 = 2466029) B2466029
theorem B2463233 : Blo 1642020 2463233 := bstep (se 2 (by rfl) ⟨923712, by rfl⟩ : syracuseStep 2463233 = 1847425) B1847425
theorem B2078227 : Blo 1642020 2078227 := bstep (se 1 (by rfl) ⟨1558670, by rfl⟩ : syracuseStep 2078227 = 3117341) B3117341
theorem B2463251 : Blo 1642020 2463251 := bstep (se 1 (by rfl) ⟨1847438, by rfl⟩ : syracuseStep 2463251 = 3694877) B3694877
theorem B2463281 : Blo 1642020 2463281 := bstep (se 2 (by rfl) ⟨923730, by rfl⟩ : syracuseStep 2463281 = 1847461) B1847461
theorem B1848883 : Blo 1642020 1848883 := bstep (se 1 (by rfl) ⟨1386662, by rfl⟩ : syracuseStep 1848883 = 2773325) B2773325
theorem B2463299 : Blo 1642020 2463299 := bstep (se 1 (by rfl) ⟨1847474, by rfl⟩ : syracuseStep 2463299 = 3694949) B3694949
theorem B2463329 : Blo 1642020 2463329 := bstep (se 2 (by rfl) ⟨923748, by rfl⟩ : syracuseStep 2463329 = 1847497) B1847497
theorem B3946097 : Blo 1642020 3946097 := bstep (se 2 (by rfl) ⟨1479786, by rfl⟩ : syracuseStep 3946097 = 2959573) B2959573
theorem B2463347 : Blo 1642020 2463347 := bstep (se 1 (by rfl) ⟨1847510, by rfl⟩ : syracuseStep 2463347 = 3695021) B3695021
theorem B2463377 : Blo 1642020 2463377 := bstep (se 2 (by rfl) ⟨923766, by rfl⟩ : syracuseStep 2463377 = 1847533) B1847533
theorem B2463395 : Blo 1642020 2463395 := bstep (se 1 (by rfl) ⟨1847546, by rfl⟩ : syracuseStep 2463395 = 3695093) B3695093
theorem B2463425 : Blo 1642020 2463425 := bstep (se 2 (by rfl) ⟨923784, by rfl⟩ : syracuseStep 2463425 = 1847569) B1847569
theorem B1849027 : Blo 1642020 1849027 := bstep (se 1 (by rfl) ⟨1386770, by rfl⟩ : syracuseStep 1849027 = 2773541) B2773541
theorem B5265101 : Blo 1642020 5265101 := bstep (se 3 (by rfl) ⟨987206, by rfl⟩ : syracuseStep 5265101 = 1974413) B1974413
theorem B2463443 : Blo 1642020 2463443 := bstep (se 1 (by rfl) ⟨1847582, by rfl⟩ : syracuseStep 2463443 = 3695165) B3695165
theorem B2463473 : Blo 1642020 2463473 := bstep (se 2 (by rfl) ⟨923802, by rfl⟩ : syracuseStep 2463473 = 1847605) B1847605
theorem B2463491 : Blo 1642020 2463491 := bstep (se 1 (by rfl) ⟨1847618, by rfl⟩ : syracuseStep 2463491 = 3695237) B3695237
theorem B5543693 : Blo 1642020 5543693 := bstep (se 3 (by rfl) ⟨1039442, by rfl⟩ : syracuseStep 5543693 = 2078885) B2078885
theorem B2463521 : Blo 1642020 2463521 := bstep (se 2 (by rfl) ⟨923820, by rfl⟩ : syracuseStep 2463521 = 1847641) B1847641
theorem B7018289 : Blo 1642020 7018289 := bstep (se 2 (by rfl) ⟨2631858, by rfl⟩ : syracuseStep 7018289 = 5263717) B5263717
theorem B2463539 : Blo 1642020 2463539 := bstep (se 1 (by rfl) ⟨1847654, by rfl⟩ : syracuseStep 2463539 = 3695309) B3695309
theorem B5543747 : Blo 1642020 5543747 := bstep (se 1 (by rfl) ⟨4157810, by rfl⟩ : syracuseStep 5543747 = 8315621) B8315621
theorem B2463569 : Blo 1642020 2463569 := bstep (se 2 (by rfl) ⟨923838, by rfl⟩ : syracuseStep 2463569 = 1847677) B1847677
theorem B1849171 : Blo 1642020 1849171 := bstep (se 1 (by rfl) ⟨1386878, by rfl⟩ : syracuseStep 1849171 = 2773757) B2773757
theorem B2463587 : Blo 1642020 2463587 := bstep (se 1 (by rfl) ⟨1847690, by rfl⟩ : syracuseStep 2463587 = 3695381) B3695381
theorem B7894883 : Blo 1642020 7894883 := bstep (se 1 (by rfl) ⟨5921162, by rfl⟩ : syracuseStep 7894883 = 11842325) B11842325
theorem B2463617 : Blo 1642020 2463617 := bstep (se 2 (by rfl) ⟨923856, by rfl⟩ : syracuseStep 2463617 = 1847713) B1847713
theorem B2463635 : Blo 1642020 2463635 := bstep (se 1 (by rfl) ⟨1847726, by rfl⟩ : syracuseStep 2463635 = 3695453) B3695453
theorem B2463665 : Blo 1642020 2463665 := bstep (se 2 (by rfl) ⟨923874, by rfl⟩ : syracuseStep 2463665 = 1847749) B1847749
theorem B2340785 : Blo 1642020 2340785 := bstep (se 2 (by rfl) ⟨877794, by rfl⟩ : syracuseStep 2340785 = 1755589) B1755589
theorem B2463683 : Blo 1642020 2463683 := bstep (se 1 (by rfl) ⟨1847762, by rfl⟩ : syracuseStep 2463683 = 3695525) B3695525
theorem B3119057 : Blo 1642020 3119057 := bstep (se 2 (by rfl) ⟨1169646, by rfl⟩ : syracuseStep 3119057 = 2339293) B2339293
theorem B2463713 : Blo 1642020 2463713 := bstep (se 2 (by rfl) ⟨923892, by rfl⟩ : syracuseStep 2463713 = 1847785) B1847785
theorem B1849315 : Blo 1642020 1849315 := bstep (se 1 (by rfl) ⟨1386986, by rfl⟩ : syracuseStep 1849315 = 2773973) B2773973
theorem B2463731 : Blo 1642020 2463731 := bstep (se 1 (by rfl) ⟨1847798, by rfl⟩ : syracuseStep 2463731 = 3695597) B3695597
theorem B2078723 : Blo 1642020 2078723 := bstep (se 1 (by rfl) ⟨1559042, by rfl⟩ : syracuseStep 2078723 = 3118085) B3118085
theorem B2463761 : Blo 1642020 2463761 := bstep (se 2 (by rfl) ⟨923910, by rfl⟩ : syracuseStep 2463761 = 1847821) B1847821
theorem B8312867 : Blo 1642020 8312867 := bstep (se 1 (by rfl) ⟨6234650, by rfl⟩ : syracuseStep 8312867 = 12469301) B12469301
theorem B2463779 : Blo 1642020 2463779 := bstep (se 1 (by rfl) ⟨1847834, by rfl⟩ : syracuseStep 2463779 = 3695669) B3695669
theorem B2463809 : Blo 1642020 2463809 := bstep (se 2 (by rfl) ⟨923928, by rfl⟩ : syracuseStep 2463809 = 1847857) B1847857
theorem B5544017 : Blo 1642020 5544017 := bstep (se 2 (by rfl) ⟨2079006, by rfl⟩ : syracuseStep 5544017 = 4158013) B4158013
theorem B2463827 : Blo 1642020 2463827 := bstep (se 1 (by rfl) ⟨1847870, by rfl⟩ : syracuseStep 2463827 = 3695741) B3695741
theorem B142071893 : Blo 1642020 142071893 := bstep (se 8 (by rfl) ⟨832452, by rfl⟩ : syracuseStep 142071893 = 1664905) B1664905
theorem B2463857 : Blo 1642020 2463857 := bstep (se 2 (by rfl) ⟨923946, by rfl⟩ : syracuseStep 2463857 = 1847893) B1847893
theorem B1849459 : Blo 1642020 1849459 := bstep (se 1 (by rfl) ⟨1387094, by rfl⟩ : syracuseStep 1849459 = 2774189) B2774189
theorem B2463875 : Blo 1642020 2463875 := bstep (se 1 (by rfl) ⟨1847906, by rfl⟩ : syracuseStep 2463875 = 3695813) B3695813
theorem B4159633 : Blo 1642020 4159633 := bstep (se 2 (by rfl) ⟨1559862, by rfl⟩ : syracuseStep 4159633 = 3119725) B3119725
theorem B2463905 : Blo 1642020 2463905 := bstep (se 2 (by rfl) ⟨923964, by rfl⟩ : syracuseStep 2463905 = 1847929) B1847929
theorem B2463923 : Blo 1642020 2463923 := bstep (se 1 (by rfl) ⟨1847942, by rfl⟩ : syracuseStep 2463923 = 3695885) B3695885
theorem B2463953 : Blo 1642020 2463953 := bstep (se 2 (by rfl) ⟨923982, by rfl⟩ : syracuseStep 2463953 = 1847965) B1847965
theorem B2463971 : Blo 1642020 2463971 := bstep (se 1 (by rfl) ⟨1847978, by rfl⟩ : syracuseStep 2463971 = 3695957) B3695957
theorem B2464001 : Blo 1642020 2464001 := bstep (se 2 (by rfl) ⟨924000, by rfl⟩ : syracuseStep 2464001 = 1848001) B1848001
theorem B2464019 : Blo 1642020 2464019 := bstep (se 1 (by rfl) ⟨1848014, by rfl⟩ : syracuseStep 2464019 = 3696029) B3696029
theorem B2464049 : Blo 1642020 2464049 := bstep (se 2 (by rfl) ⟨924018, by rfl⟩ : syracuseStep 2464049 = 1848037) B1848037
theorem B2464067 : Blo 1642020 2464067 := bstep (se 1 (by rfl) ⟨1848050, by rfl⟩ : syracuseStep 2464067 = 3696101) B3696101
theorem B2464097 : Blo 1642020 2464097 := bstep (se 2 (by rfl) ⟨924036, by rfl⟩ : syracuseStep 2464097 = 1848073) B1848073
theorem B2464115 : Blo 1642020 2464115 := bstep (se 1 (by rfl) ⟨1848086, by rfl⟩ : syracuseStep 2464115 = 3696173) B3696173
theorem B14031245 : Blo 1642020 14031245 := bstep (se 3 (by rfl) ⟨2630858, by rfl⟩ : syracuseStep 14031245 = 5261717) B5261717
theorem B2464145 : Blo 1642020 2464145 := bstep (se 2 (by rfl) ⟨924054, by rfl⟩ : syracuseStep 2464145 = 1848109) B1848109
theorem B2464163 : Blo 1642020 2464163 := bstep (se 1 (by rfl) ⟨1848122, by rfl⟩ : syracuseStep 2464163 = 3696245) B3696245
theorem B4159907 : Blo 1642020 4159907 := bstep (se 1 (by rfl) ⟨3119930, by rfl⟩ : syracuseStep 4159907 = 6239861) B6239861
theorem B2464193 : Blo 1642020 2464193 := bstep (se 2 (by rfl) ⟨924072, by rfl⟩ : syracuseStep 2464193 = 1848145) B1848145
theorem B2464211 : Blo 1642020 2464211 := bstep (se 1 (by rfl) ⟨1848158, by rfl⟩ : syracuseStep 2464211 = 3696317) B3696317
theorem B2464241 : Blo 1642020 2464241 := bstep (se 2 (by rfl) ⟨924090, by rfl⟩ : syracuseStep 2464241 = 1848181) B1848181
theorem B5618179 : Blo 1642020 5618179 := bstep (se 1 (by rfl) ⟨4213634, by rfl⟩ : syracuseStep 5618179 = 8427269) B8427269
theorem B2464259 : Blo 1642020 2464259 := bstep (se 1 (by rfl) ⟨1848194, by rfl⟩ : syracuseStep 2464259 = 3696389) B3696389
theorem B2464289 : Blo 1642020 2464289 := bstep (se 2 (by rfl) ⟨924108, by rfl⟩ : syracuseStep 2464289 = 1848217) B1848217
theorem B3947057 : Blo 1642020 3947057 := bstep (se 2 (by rfl) ⟨1480146, by rfl⟩ : syracuseStep 3947057 = 2960293) B2960293
theorem B2464307 : Blo 1642020 2464307 := bstep (se 1 (by rfl) ⟨1848230, by rfl⟩ : syracuseStep 2464307 = 3696461) B3696461
theorem B2464337 : Blo 1642020 2464337 := bstep (se 2 (by rfl) ⟨924126, by rfl⟩ : syracuseStep 2464337 = 1848253) B1848253
theorem B2464355 : Blo 1642020 2464355 := bstep (se 1 (by rfl) ⟨1848266, by rfl⟩ : syracuseStep 2464355 = 3696533) B3696533
theorem B4160099 : Blo 1642020 4160099 := bstep (se 1 (by rfl) ⟨3120074, by rfl⟩ : syracuseStep 4160099 = 6240149) B6240149
theorem B5544557 : Blo 1642020 5544557 := bstep (se 3 (by rfl) ⟨1039604, by rfl⟩ : syracuseStep 5544557 = 2079209) B2079209
theorem B2464385 : Blo 1642020 2464385 := bstep (se 2 (by rfl) ⟨924144, by rfl⟩ : syracuseStep 2464385 = 1848289) B1848289
theorem B2464403 : Blo 1642020 2464403 := bstep (se 1 (by rfl) ⟨1848302, by rfl⟩ : syracuseStep 2464403 = 3696605) B3696605
theorem B5544611 : Blo 1642020 5544611 := bstep (se 1 (by rfl) ⟨4158458, by rfl⟩ : syracuseStep 5544611 = 8316917) B8316917
theorem B2464433 : Blo 1642020 2464433 := bstep (se 2 (by rfl) ⟨924162, by rfl⟩ : syracuseStep 2464433 = 1848325) B1848325
theorem B2464451 : Blo 1642020 2464451 := bstep (se 1 (by rfl) ⟨1848338, by rfl⟩ : syracuseStep 2464451 = 3696677) B3696677
theorem B2079427 : Blo 1642020 2079427 := bstep (se 1 (by rfl) ⟨1559570, by rfl⟩ : syracuseStep 2079427 = 3119141) B3119141
theorem B2464481 : Blo 1642020 2464481 := bstep (se 2 (by rfl) ⟨924180, by rfl⟩ : syracuseStep 2464481 = 1848361) B1848361
theorem B8321777 : Blo 1642020 8321777 := bstep (se 2 (by rfl) ⟨3120666, by rfl⟩ : syracuseStep 8321777 = 6241333) B6241333
theorem B2464499 : Blo 1642020 2464499 := bstep (se 1 (by rfl) ⟨1848374, by rfl⟩ : syracuseStep 2464499 = 3696749) B3696749
theorem B2464529 : Blo 1642020 2464529 := bstep (se 2 (by rfl) ⟨924198, by rfl⟩ : syracuseStep 2464529 = 1848397) B1848397
theorem B2464547 : Blo 1642020 2464547 := bstep (se 1 (by rfl) ⟨1848410, by rfl⟩ : syracuseStep 2464547 = 3696821) B3696821
theorem B2079523 : Blo 1642020 2079523 := bstep (se 1 (by rfl) ⟨1559642, by rfl⟩ : syracuseStep 2079523 = 3119285) B3119285
theorem B2464577 : Blo 1642020 2464577 := bstep (se 2 (by rfl) ⟨924216, by rfl⟩ : syracuseStep 2464577 = 1848433) B1848433
theorem B8313677 : Blo 1642020 8313677 := bstep (se 3 (by rfl) ⟨1558814, by rfl⟩ : syracuseStep 8313677 = 3117629) B3117629
theorem B3119953 : Blo 1642020 3119953 := bstep (se 2 (by rfl) ⟨1169982, by rfl⟩ : syracuseStep 3119953 = 2339965) B2339965
theorem B2464595 : Blo 1642020 2464595 := bstep (se 1 (by rfl) ⟨1848446, by rfl⟩ : syracuseStep 2464595 = 3696893) B3696893
theorem B4438883 : Blo 1642020 4438883 := bstep (se 1 (by rfl) ⟨3329162, by rfl⟩ : syracuseStep 4438883 = 6658325) B6658325
theorem B15792995 : Blo 1642020 15792995 := bstep (se 1 (by rfl) ⟨11844746, by rfl⟩ : syracuseStep 15792995 = 23689493) B23689493
theorem B2464625 : Blo 1642020 2464625 := bstep (se 2 (by rfl) ⟨924234, by rfl⟩ : syracuseStep 2464625 = 1848469) B1848469
theorem B2464643 : Blo 1642020 2464643 := bstep (se 1 (by rfl) ⟨1848482, by rfl⟩ : syracuseStep 2464643 = 3696965) B3696965
theorem B2464673 : Blo 1642020 2464673 := bstep (se 2 (by rfl) ⟨924252, by rfl⟩ : syracuseStep 2464673 = 1848505) B1848505
theorem B4676525 : Blo 1642020 4676525 := bstep (se 3 (by rfl) ⟨876848, by rfl⟩ : syracuseStep 4676525 = 1753697) B1753697
theorem B5544881 : Blo 1642020 5544881 := bstep (se 2 (by rfl) ⟨2079330, by rfl⟩ : syracuseStep 5544881 = 4158661) B4158661
theorem B2464691 : Blo 1642020 2464691 := bstep (se 1 (by rfl) ⟨1848518, by rfl⟩ : syracuseStep 2464691 = 3697037) B3697037
theorem B2464721 : Blo 1642020 2464721 := bstep (se 2 (by rfl) ⟨924270, by rfl⟩ : syracuseStep 2464721 = 1848541) B1848541
theorem B2464739 : Blo 1642020 2464739 := bstep (se 1 (by rfl) ⟨1848554, by rfl⟩ : syracuseStep 2464739 = 3697109) B3697109
theorem B3120113 : Blo 1642020 3120113 := bstep (se 2 (by rfl) ⟨1170042, by rfl⟩ : syracuseStep 3120113 = 2340085) B2340085
theorem B2464769 : Blo 1642020 2464769 := bstep (se 2 (by rfl) ⟨924288, by rfl⟩ : syracuseStep 2464769 = 1848577) B1848577
theorem B2464787 : Blo 1642020 2464787 := bstep (se 1 (by rfl) ⟨1848590, by rfl⟩ : syracuseStep 2464787 = 3697181) B3697181
theorem B7896113 : Blo 1642020 7896113 := bstep (se 2 (by rfl) ⟨2961042, by rfl⟩ : syracuseStep 7896113 = 5922085) B5922085
theorem B2464817 : Blo 1642020 2464817 := bstep (se 2 (by rfl) ⟨924306, by rfl⟩ : syracuseStep 2464817 = 1848613) B1848613
theorem B2464835 : Blo 1642020 2464835 := bstep (se 1 (by rfl) ⟨1848626, by rfl⟩ : syracuseStep 2464835 = 3697253) B3697253
theorem B2464865 : Blo 1642020 2464865 := bstep (se 2 (by rfl) ⟨924324, by rfl⟩ : syracuseStep 2464865 = 1848649) B1848649
theorem B4676717 : Blo 1642020 4676717 := bstep (se 3 (by rfl) ⟨876884, by rfl⟩ : syracuseStep 4676717 = 1753769) B1753769
theorem B2464883 : Blo 1642020 2464883 := bstep (se 1 (by rfl) ⟨1848662, by rfl⟩ : syracuseStep 2464883 = 3697325) B3697325
theorem B3849347 : Blo 1642020 3849347 := bstep (se 1 (by rfl) ⟨2887010, by rfl⟩ : syracuseStep 3849347 = 5774021) B5774021
theorem B2464913 : Blo 1642020 2464913 := bstep (se 2 (by rfl) ⟨924342, by rfl⟩ : syracuseStep 2464913 = 1848685) B1848685
theorem B2464931 : Blo 1642020 2464931 := bstep (se 1 (by rfl) ⟨1848698, by rfl⟩ : syracuseStep 2464931 = 3697397) B3697397
theorem B2809009 : Blo 1642020 2809009 := bstep (se 2 (by rfl) ⟨1053378, by rfl⟩ : syracuseStep 2809009 = 2106757) B2106757
theorem B5921969 : Blo 1642020 5921969 := bstep (se 2 (by rfl) ⟨2220738, by rfl⟩ : syracuseStep 5921969 = 4441477) B4441477
theorem B2464961 : Blo 1642020 2464961 := bstep (se 2 (by rfl) ⟨924360, by rfl⟩ : syracuseStep 2464961 = 1848721) B1848721
theorem B9354437 : Blo 1642020 9354437 := bstep (se 4 (by rfl) ⟨876978, by rfl⟩ : syracuseStep 9354437 = 1753957) B1753957
theorem B2464979 : Blo 1642020 2464979 := bstep (se 1 (by rfl) ⟨1848734, by rfl⟩ : syracuseStep 2464979 = 3697469) B3697469
theorem B12475619 : Blo 1642020 12475619 := bstep (se 1 (by rfl) ⟨9356714, by rfl⟩ : syracuseStep 12475619 = 18713429) B18713429
theorem B2465009 : Blo 1642020 2465009 := bstep (se 2 (by rfl) ⟨924378, by rfl⟩ : syracuseStep 2465009 = 1848757) B1848757
theorem B2465027 : Blo 1642020 2465027 := bstep (se 1 (by rfl) ⟨1848770, by rfl⟩ : syracuseStep 2465027 = 3697541) B3697541
theorem B5266691 : Blo 1642020 5266691 := bstep (se 1 (by rfl) ⟨3950018, by rfl⟩ : syracuseStep 5266691 = 7900037) B7900037
theorem B2080019 : Blo 1642020 2080019 := bstep (se 1 (by rfl) ⟨1560014, by rfl⟩ : syracuseStep 2080019 = 3120029) B3120029
theorem B2465057 : Blo 1642020 2465057 := bstep (se 2 (by rfl) ⟨924396, by rfl⟩ : syracuseStep 2465057 = 1848793) B1848793
theorem B8428835 : Blo 1642020 8428835 := bstep (se 1 (by rfl) ⟨6321626, by rfl⟩ : syracuseStep 8428835 = 12643253) B12643253
theorem B2465075 : Blo 1642020 2465075 := bstep (se 1 (by rfl) ⟨1848806, by rfl⟩ : syracuseStep 2465075 = 3697613) B3697613
theorem B2465105 : Blo 1642020 2465105 := bstep (se 2 (by rfl) ⟨924414, by rfl⟩ : syracuseStep 2465105 = 1848829) B1848829
theorem B1973587 : Blo 1642020 1973587 := bstep (se 1 (by rfl) ⟨1480190, by rfl⟩ : syracuseStep 1973587 = 2960381) B2960381
theorem B2465123 : Blo 1642020 2465123 := bstep (se 1 (by rfl) ⟨1848842, by rfl⟩ : syracuseStep 2465123 = 3697685) B3697685
theorem B33717617 : Blo 1642020 33717617 := bstep (se 2 (by rfl) ⟨12644106, by rfl⟩ : syracuseStep 33717617 = 25288213) B25288213
theorem B2465153 : Blo 1642020 2465153 := bstep (se 2 (by rfl) ⟨924432, by rfl⟩ : syracuseStep 2465153 = 1848865) B1848865
theorem B3120515 : Blo 1642020 3120515 := bstep (se 1 (by rfl) ⟨2340386, by rfl⟩ : syracuseStep 3120515 = 4680773) B4680773
theorem B2465171 : Blo 1642020 2465171 := bstep (se 1 (by rfl) ⟨1848878, by rfl⟩ : syracuseStep 2465171 = 3697757) B3697757
theorem B2465201 : Blo 1642020 2465201 := bstep (se 2 (by rfl) ⟨924450, by rfl⟩ : syracuseStep 2465201 = 1848901) B1848901
theorem B2465219 : Blo 1642020 2465219 := bstep (se 1 (by rfl) ⟨1848914, by rfl⟩ : syracuseStep 2465219 = 3697829) B3697829
theorem B5545421 : Blo 1642020 5545421 := bstep (se 3 (by rfl) ⟨1039766, by rfl⟩ : syracuseStep 5545421 = 2079533) B2079533
theorem B2465249 : Blo 1642020 2465249 := bstep (se 2 (by rfl) ⟨924468, by rfl⟩ : syracuseStep 2465249 = 1848937) B1848937
theorem B10124785 : Blo 1642020 10124785 := bstep (se 2 (by rfl) ⟨3796794, by rfl⟩ : syracuseStep 10124785 = 7593589) B7593589
theorem B2465267 : Blo 1642020 2465267 := bstep (se 1 (by rfl) ⟨1848950, by rfl⟩ : syracuseStep 2465267 = 3697901) B3697901
theorem B5545475 : Blo 1642020 5545475 := bstep (se 1 (by rfl) ⟨4159106, by rfl⟩ : syracuseStep 5545475 = 8318213) B8318213
theorem B6241805 : Blo 1642020 6241805 := bstep (se 3 (by rfl) ⟨1170338, by rfl⟩ : syracuseStep 6241805 = 2340677) B2340677
theorem B2465297 : Blo 1642020 2465297 := bstep (se 2 (by rfl) ⟨924486, by rfl⟩ : syracuseStep 2465297 = 1848973) B1848973
theorem B4161041 : Blo 1642020 4161041 := bstep (se 2 (by rfl) ⟨1560390, by rfl⟩ : syracuseStep 4161041 = 3120781) B3120781
theorem B2465315 : Blo 1642020 2465315 := bstep (se 1 (by rfl) ⟨1848986, by rfl⟩ : syracuseStep 2465315 = 3697973) B3697973
theorem B2465345 : Blo 1642020 2465345 := bstep (se 2 (by rfl) ⟨924504, by rfl⟩ : syracuseStep 2465345 = 1849009) B1849009
theorem B2530883 : Blo 1642020 2530883 := bstep (se 1 (by rfl) ⟨1898162, by rfl⟩ : syracuseStep 2530883 = 3796325) B3796325
theorem B4161091 : Blo 1642020 4161091 := bstep (se 1 (by rfl) ⟨3120818, by rfl⟩ : syracuseStep 4161091 = 6241637) B6241637
theorem B2465363 : Blo 1642020 2465363 := bstep (se 1 (by rfl) ⟨1849022, by rfl⟩ : syracuseStep 2465363 = 3698045) B3698045
theorem B2465393 : Blo 1642020 2465393 := bstep (se 2 (by rfl) ⟨924522, by rfl⟩ : syracuseStep 2465393 = 1849045) B1849045
theorem B1973875 : Blo 1642020 1973875 := bstep (se 1 (by rfl) ⟨1480406, by rfl⟩ : syracuseStep 1973875 = 2960813) B2960813
theorem B2465411 : Blo 1642020 2465411 := bstep (se 1 (by rfl) ⟨1849058, by rfl⟩ : syracuseStep 2465411 = 3698117) B3698117
theorem B2465441 : Blo 1642020 2465441 := bstep (se 2 (by rfl) ⟨924540, by rfl⟩ : syracuseStep 2465441 = 1849081) B1849081
theorem B2465459 : Blo 1642020 2465459 := bstep (se 1 (by rfl) ⟨1849094, by rfl⟩ : syracuseStep 2465459 = 3698189) B3698189
theorem B2465489 : Blo 1642020 2465489 := bstep (se 2 (by rfl) ⟨924558, by rfl⟩ : syracuseStep 2465489 = 1849117) B1849117
theorem B1973971 : Blo 1642020 1973971 := bstep (se 1 (by rfl) ⟨1480478, by rfl⟩ : syracuseStep 1973971 = 2960957) B2960957
theorem B4161233 : Blo 1642020 4161233 := bstep (se 2 (by rfl) ⟨1560462, by rfl⟩ : syracuseStep 4161233 = 3120925) B3120925
theorem B2465507 : Blo 1642020 2465507 := bstep (se 1 (by rfl) ⟨1849130, by rfl⟩ : syracuseStep 2465507 = 3698261) B3698261
theorem B9363185 : Blo 1642020 9363185 := bstep (se 2 (by rfl) ⟨3511194, by rfl⟩ : syracuseStep 9363185 = 7022389) B7022389
theorem B2465537 : Blo 1642020 2465537 := bstep (se 2 (by rfl) ⟨924576, by rfl⟩ : syracuseStep 2465537 = 1849153) B1849153
theorem B4439825 : Blo 1642020 4439825 := bstep (se 2 (by rfl) ⟨1664934, by rfl⟩ : syracuseStep 4439825 = 3329869) B3329869
theorem B5545745 : Blo 1642020 5545745 := bstep (se 2 (by rfl) ⟨2079654, by rfl⟩ : syracuseStep 5545745 = 4159309) B4159309
theorem B2465555 : Blo 1642020 2465555 := bstep (se 1 (by rfl) ⟨1849166, by rfl⟩ : syracuseStep 2465555 = 3698333) B3698333
theorem B2465585 : Blo 1642020 2465585 := bstep (se 2 (by rfl) ⟨924594, by rfl⟩ : syracuseStep 2465585 = 1849189) B1849189
theorem B3948355 : Blo 1642020 3948355 := bstep (se 1 (by rfl) ⟨2961266, by rfl⟩ : syracuseStep 3948355 = 5922533) B5922533
theorem B2465603 : Blo 1642020 2465603 := bstep (se 1 (by rfl) ⟨1849202, by rfl⟩ : syracuseStep 2465603 = 3698405) B3698405
theorem B2465633 : Blo 1642020 2465633 := bstep (se 2 (by rfl) ⟨924612, by rfl⟩ : syracuseStep 2465633 = 1849225) B1849225
theorem B1974115 : Blo 1642020 1974115 := bstep (se 1 (by rfl) ⟨1480586, by rfl⟩ : syracuseStep 1974115 = 2961173) B2961173
theorem B9355121 : Blo 1642020 9355121 := bstep (se 2 (by rfl) ⟨3508170, by rfl⟩ : syracuseStep 9355121 = 7016341) B7016341
theorem B2465651 : Blo 1642020 2465651 := bstep (se 1 (by rfl) ⟨1849238, by rfl⟩ : syracuseStep 2465651 = 3698477) B3698477
theorem B2465681 : Blo 1642020 2465681 := bstep (se 2 (by rfl) ⟨924630, by rfl⟩ : syracuseStep 2465681 = 1849261) B1849261
theorem B2465699 : Blo 1642020 2465699 := bstep (se 1 (by rfl) ⟨1849274, by rfl⟩ : syracuseStep 2465699 = 3698549) B3698549
theorem B2465729 : Blo 1642020 2465729 := bstep (se 2 (by rfl) ⟨924648, by rfl⟩ : syracuseStep 2465729 = 1849297) B1849297
theorem B2465747 : Blo 1642020 2465747 := bstep (se 1 (by rfl) ⟨1849310, by rfl⟩ : syracuseStep 2465747 = 3698621) B3698621
theorem B18710513 : Blo 1642020 18710513 := bstep (se 2 (by rfl) ⟨7016442, by rfl⟩ : syracuseStep 18710513 = 14032885) B14032885
theorem B2465777 : Blo 1642020 2465777 := bstep (se 2 (by rfl) ⟨924666, by rfl⟩ : syracuseStep 2465777 = 1849333) B1849333
theorem B3694643 : Blo 1642020 3694643 := bstep (se 1 (by rfl) ⟨2770982, by rfl⟩ : syracuseStep 3694643 = 5541965) B5541965
theorem B2465867 : Blo 1642020 2465867 := bstep (se 1 (by rfl) ⟨1849400, by rfl⟩ : syracuseStep 2465867 = 3698801) B3698801
theorem B18980939 : Blo 1642020 18980939 := bstep (se 1 (by rfl) ⟨14235704, by rfl⟩ : syracuseStep 18980939 = 28471409) B28471409
theorem B3694679 : Blo 1642020 3694679 := bstep (se 1 (by rfl) ⟨2771009, by rfl⟩ : syracuseStep 3694679 = 5542019) B5542019
theorem B2465879 : Blo 1642020 2465879 := bstep (se 1 (by rfl) ⟨1849409, by rfl⟩ : syracuseStep 2465879 = 3698819) B3698819
theorem B8314973 : Blo 1642020 8314973 := bstep (se 3 (by rfl) ⟨1559057, by rfl⟩ : syracuseStep 8314973 = 3118115) B3118115
theorem B2465945 : Blo 1642020 2465945 := bstep (se 2 (by rfl) ⟨924729, by rfl⟩ : syracuseStep 2465945 = 1849459) B1849459
theorem B5546177 : Blo 1642020 5546177 := bstep (se 2 (by rfl) ⟨2079816, by rfl⟩ : syracuseStep 5546177 = 4159633) B4159633
theorem B3694859 : Blo 1642020 3694859 := bstep (se 1 (by rfl) ⟨2771144, by rfl⟩ : syracuseStep 3694859 = 5542289) B5542289
theorem B3694913 : Blo 1642020 3694913 := bstep (se 2 (by rfl) ⟨1385592, by rfl⟩ : syracuseStep 3694913 = 2771185) B2771185
theorem B9355621 : Blo 1642020 9355621 := bstep (se 4 (by rfl) ⟨877089, by rfl⟩ : syracuseStep 9355621 = 1754179) B1754179
theorem B4112819 : Blo 1642020 4112819 := bstep (se 1 (by rfl) ⟨3084614, by rfl⟩ : syracuseStep 4112819 = 6169229) B6169229
theorem B1753547 : Blo 1642020 1753547 := bstep (se 1 (by rfl) ⟨1315160, by rfl⟩ : syracuseStep 1753547 = 2630321) B2630321
theorem B3695129 : Blo 1642020 3695129 := bstep (se 2 (by rfl) ⟨1385673, by rfl⟩ : syracuseStep 3695129 = 2771347) B2771347
theorem B11846245 : Blo 1642020 11846245 := bstep (se 4 (by rfl) ⟨1110585, by rfl⟩ : syracuseStep 11846245 = 2221171) B2221171
theorem B3695219 : Blo 1642020 3695219 := bstep (se 1 (by rfl) ⟨2771414, by rfl⟩ : syracuseStep 3695219 = 5542829) B5542829
theorem B3695255 : Blo 1642020 3695255 := bstep (se 1 (by rfl) ⟨2771441, by rfl⟩ : syracuseStep 3695255 = 5542883) B5542883
theorem B6234803 : Blo 1642020 6234803 := bstep (se 1 (by rfl) ⟨4676102, by rfl⟩ : syracuseStep 6234803 = 9352205) B9352205
theorem B3556055 : Blo 1642020 3556055 := bstep (se 1 (by rfl) ⟨2667041, by rfl⟩ : syracuseStep 3556055 = 5334083) B5334083
theorem B5546717 : Blo 1642020 5546717 := bstep (se 3 (by rfl) ⟨1040009, by rfl⟩ : syracuseStep 5546717 = 2080019) B2080019
theorem B2630411 : Blo 1642020 2630411 := bstep (se 1 (by rfl) ⟨1972808, by rfl⟩ : syracuseStep 2630411 = 3945617) B3945617
theorem B3695435 : Blo 1642020 3695435 := bstep (se 1 (by rfl) ⟨2771576, by rfl⟩ : syracuseStep 3695435 = 5543153) B5543153
theorem B3695489 : Blo 1642020 3695489 := bstep (se 2 (by rfl) ⟨1385808, by rfl⟩ : syracuseStep 3695489 = 2771617) B2771617
theorem B5923729 : Blo 1642020 5923729 := bstep (se 2 (by rfl) ⟨2221398, by rfl⟩ : syracuseStep 5923729 = 4442797) B4442797
theorem B14033843 : Blo 1642020 14033843 := bstep (se 1 (by rfl) ⟨10525382, by rfl⟩ : syracuseStep 14033843 = 21050765) B21050765
theorem B2630603 : Blo 1642020 2630603 := bstep (se 1 (by rfl) ⟨1972952, by rfl⟩ : syracuseStep 2630603 = 3945905) B3945905
theorem B2630731 : Blo 1642020 2630731 := bstep (se 1 (by rfl) ⟨1973048, by rfl⟩ : syracuseStep 2630731 = 3946097) B3946097
theorem B3695705 : Blo 1642020 3695705 := bstep (se 2 (by rfl) ⟨1385889, by rfl⟩ : syracuseStep 3695705 = 2771779) B2771779
theorem B3695795 : Blo 1642020 3695795 := bstep (se 1 (by rfl) ⟨2771846, by rfl⟩ : syracuseStep 3695795 = 5543693) B5543693
theorem B4678859 : Blo 1642020 4678859 := bstep (se 1 (by rfl) ⟨3509144, by rfl⟩ : syracuseStep 4678859 = 7018289) B7018289
theorem B21062861 : Blo 1642020 21062861 := bstep (se 3 (by rfl) ⟨3949286, by rfl⟩ : syracuseStep 21062861 = 7898573) B7898573
theorem B3695831 : Blo 1642020 3695831 := bstep (se 1 (by rfl) ⟨2771873, by rfl⟩ : syracuseStep 3695831 = 5543747) B5543747
theorem B32531717 : Blo 1642020 32531717 := bstep (se 4 (by rfl) ⟨3049848, by rfl⟩ : syracuseStep 32531717 = 6099697) B6099697
theorem B14034221 : Blo 1642020 14034221 := bstep (se 3 (by rfl) ⟨2631416, by rfl⟩ : syracuseStep 14034221 = 5262833) B5262833
theorem B3696011 : Blo 1642020 3696011 := bstep (se 1 (by rfl) ⟨2772008, by rfl⟩ : syracuseStep 3696011 = 5544017) B5544017
theorem B1754551 : Blo 1642020 1754551 := bstep (se 1 (by rfl) ⟨1315913, by rfl⟩ : syracuseStep 1754551 = 2631827) B2631827
theorem B3696065 : Blo 1642020 3696065 := bstep (se 2 (by rfl) ⟨1386024, by rfl⟩ : syracuseStep 3696065 = 2772049) B2772049
theorem B3745345 : Blo 1642020 3745345 := bstep (se 2 (by rfl) ⟨1404504, by rfl⟩ : syracuseStep 3745345 = 2809009) B2809009
theorem B3696281 : Blo 1642020 3696281 := bstep (se 2 (by rfl) ⟨1386105, by rfl⟩ : syracuseStep 3696281 = 2772211) B2772211
theorem B13321907 : Blo 1642020 13321907 := bstep (se 1 (by rfl) ⟨9991430, by rfl⟩ : syracuseStep 13321907 = 19982861) B19982861
theorem B3376819 : Blo 1642020 3376819 := bstep (se 1 (by rfl) ⟨2532614, by rfl⟩ : syracuseStep 3376819 = 5065229) B5065229
theorem B2631371 : Blo 1642020 2631371 := bstep (se 1 (by rfl) ⟨1973528, by rfl⟩ : syracuseStep 2631371 = 3947057) B3947057
theorem B15795917 : Blo 1642020 15795917 := bstep (se 3 (by rfl) ⟨2961734, by rfl⟩ : syracuseStep 15795917 = 5923469) B5923469
theorem B3696371 : Blo 1642020 3696371 := bstep (se 1 (by rfl) ⟨2772278, by rfl⟩ : syracuseStep 3696371 = 5544557) B5544557
theorem B25298693 : Blo 1642020 25298693 := bstep (se 4 (by rfl) ⟨2371752, by rfl⟩ : syracuseStep 25298693 = 4743505) B4743505
theorem B3696407 : Blo 1642020 3696407 := bstep (se 1 (by rfl) ⟨2772305, by rfl⟩ : syracuseStep 3696407 = 5544611) B5544611
theorem B2631449 : Blo 1642020 2631449 := bstep (se 2 (by rfl) ⟨986793, by rfl⟩ : syracuseStep 2631449 = 1973587) B1973587
theorem B5547851 : Blo 1642020 5547851 := bstep (se 1 (by rfl) ⟨4160888, by rfl⟩ : syracuseStep 5547851 = 8321777) B8321777
theorem B10528613 : Blo 1642020 10528613 := bstep (se 4 (by rfl) ⟨987057, by rfl⟩ : syracuseStep 10528613 = 1974115) B1974115
theorem B2959255 : Blo 1642020 2959255 := bstep (se 1 (by rfl) ⟨2219441, by rfl⟩ : syracuseStep 2959255 = 4438883) B4438883
theorem B10528663 : Blo 1642020 10528663 := bstep (se 1 (by rfl) ⟨7896497, by rfl⟩ : syracuseStep 10528663 = 15792995) B15792995
theorem B3696587 : Blo 1642020 3696587 := bstep (se 1 (by rfl) ⟨2772440, by rfl⟩ : syracuseStep 3696587 = 5544881) B5544881
theorem B11847629 : Blo 1642020 11847629 := bstep (se 3 (by rfl) ⟨2221430, by rfl⟩ : syracuseStep 11847629 = 4442861) B4442861
theorem B3696641 : Blo 1642020 3696641 := bstep (se 2 (by rfl) ⟨1386240, by rfl⟩ : syracuseStep 3696641 = 2772481) B2772481
theorem B2770969 : Blo 1642020 2770969 := bstep (se 2 (by rfl) ⟨1039113, by rfl⟩ : syracuseStep 2770969 = 2078227) B2078227
theorem B2566231 : Blo 1642020 2566231 := bstep (se 1 (by rfl) ⟨1924673, by rfl⟩ : syracuseStep 2566231 = 3849347) B3849347
theorem B5548121 : Blo 1642020 5548121 := bstep (se 2 (by rfl) ⟨2080545, by rfl⟩ : syracuseStep 5548121 = 4161091) B4161091
theorem B6236291 : Blo 1642020 6236291 := bstep (se 1 (by rfl) ⟨4677218, by rfl⟩ : syracuseStep 6236291 = 9354437) B9354437
theorem B8317079 : Blo 1642020 8317079 := bstep (se 1 (by rfl) ⟨6237809, by rfl⟩ : syracuseStep 8317079 = 12475619) B12475619
theorem B2631833 : Blo 1642020 2631833 := bstep (se 2 (by rfl) ⟨986937, by rfl⟩ : syracuseStep 2631833 = 1973875) B1973875
theorem B1755307 : Blo 1642020 1755307 := bstep (se 1 (by rfl) ⟨1316480, by rfl⟩ : syracuseStep 1755307 = 2632961) B2632961
theorem B3508427 : Blo 1642020 3508427 := bstep (se 1 (by rfl) ⟨2631320, by rfl⟩ : syracuseStep 3508427 = 5262641) B5262641
theorem B3696857 : Blo 1642020 3696857 := bstep (se 2 (by rfl) ⟨1386321, by rfl⟩ : syracuseStep 3696857 = 2772643) B2772643
theorem B2631961 : Blo 1642020 2631961 := bstep (se 2 (by rfl) ⟨986985, by rfl⟩ : syracuseStep 2631961 = 1973971) B1973971
theorem B7014701 : Blo 1642020 7014701 := bstep (se 3 (by rfl) ⟨1315256, by rfl⟩ : syracuseStep 7014701 = 2630513) B2630513
theorem B7113005 : Blo 1642020 7113005 := bstep (se 3 (by rfl) ⟨1333688, by rfl⟩ : syracuseStep 7113005 = 2667377) B2667377
theorem B3696947 : Blo 1642020 3696947 := bstep (se 1 (by rfl) ⟨2772710, by rfl⟩ : syracuseStep 3696947 = 5545421) B5545421
theorem B3696983 : Blo 1642020 3696983 := bstep (se 1 (by rfl) ⟨2772737, by rfl⟩ : syracuseStep 3696983 = 5545475) B5545475
theorem B2959883 : Blo 1642020 2959883 := bstep (se 1 (by rfl) ⟨2219912, by rfl⟩ : syracuseStep 2959883 = 4439825) B4439825
theorem B3697163 : Blo 1642020 3697163 := bstep (se 1 (by rfl) ⟨2772872, by rfl⟩ : syracuseStep 3697163 = 5545745) B5545745
theorem B4442647 : Blo 1642020 4442647 := bstep (se 1 (by rfl) ⟨3331985, by rfl⟩ : syracuseStep 4442647 = 6663971) B6663971
theorem B12479021 : Blo 1642020 12479021 := bstep (se 3 (by rfl) ⟨2339816, by rfl⟩ : syracuseStep 12479021 = 4679633) B4679633
theorem B3697217 : Blo 1642020 3697217 := bstep (se 2 (by rfl) ⟨1386456, by rfl⟩ : syracuseStep 3697217 = 2772913) B2772913
theorem B6236747 : Blo 1642020 6236747 := bstep (se 1 (by rfl) ⟨4677560, by rfl⟩ : syracuseStep 6236747 = 9355121) B9355121
theorem B2771543 : Blo 1642020 2771543 := bstep (se 1 (by rfl) ⟨2078657, by rfl⟩ : syracuseStep 2771543 = 4157315) B4157315
theorem B2771671 : Blo 1642020 2771671 := bstep (se 1 (by rfl) ⟨2078753, by rfl⟩ : syracuseStep 2771671 = 4157507) B4157507
theorem B6236945 : Blo 1642020 6236945 := bstep (se 2 (by rfl) ⟨2338854, by rfl⟩ : syracuseStep 6236945 = 4677709) B4677709
theorem B3697433 : Blo 1642020 3697433 := bstep (se 2 (by rfl) ⟨1386537, by rfl⟩ : syracuseStep 3697433 = 2773075) B2773075
theorem B4680499 : Blo 1642020 4680499 := bstep (se 1 (by rfl) ⟨3510374, by rfl⟩ : syracuseStep 4680499 = 7020749) B7020749
theorem B5262155 : Blo 1642020 5262155 := bstep (se 1 (by rfl) ⟨3946616, by rfl⟩ : syracuseStep 5262155 = 7893233) B7893233
theorem B3697523 : Blo 1642020 3697523 := bstep (se 1 (by rfl) ⟨2773142, by rfl⟩ : syracuseStep 3697523 = 5546285) B5546285
theorem B3697559 : Blo 1642020 3697559 := bstep (se 1 (by rfl) ⟨2773169, by rfl⟩ : syracuseStep 3697559 = 5546339) B5546339
theorem B1665943 : Blo 1642020 1665943 := bstep (se 1 (by rfl) ⟨1249457, by rfl⟩ : syracuseStep 1665943 = 2498915) B2498915
theorem B12471245 : Blo 1642020 12471245 := bstep (se 3 (by rfl) ⟨2338358, by rfl⟩ : syracuseStep 12471245 = 4676717) B4676717
theorem B6843457 : Blo 1642020 6843457 := bstep (se 2 (by rfl) ⟨2566296, by rfl⟩ : syracuseStep 6843457 = 5132593) B5132593
theorem B3697739 : Blo 1642020 3697739 := bstep (se 1 (by rfl) ⟨2773304, by rfl⟩ : syracuseStep 3697739 = 5546609) B5546609
theorem B4156505 : Blo 1642020 4156505 := bstep (se 2 (by rfl) ⟨1558689, by rfl⟩ : syracuseStep 4156505 = 3117379) B3117379
theorem B3697793 : Blo 1642020 3697793 := bstep (se 2 (by rfl) ⟨1386672, by rfl⟩ : syracuseStep 3697793 = 2773345) B2773345
theorem B7892099 : Blo 1642020 7892099 := bstep (se 1 (by rfl) ⟨5919074, by rfl⟩ : syracuseStep 7892099 = 11838149) B11838149
theorem B3509401 : Blo 1642020 3509401 := bstep (se 2 (by rfl) ⟨1316025, by rfl⟩ : syracuseStep 3509401 = 2632051) B2632051
theorem B28085453 : Blo 1642020 28085453 := bstep (se 3 (by rfl) ⟨5266022, by rfl⟩ : syracuseStep 28085453 = 10532045) B10532045
theorem B2772299 : Blo 1642020 2772299 := bstep (se 1 (by rfl) ⟨2079224, by rfl⟩ : syracuseStep 2772299 = 4158449) B4158449
theorem B3698009 : Blo 1642020 3698009 := bstep (se 2 (by rfl) ⟨1386753, by rfl⟩ : syracuseStep 3698009 = 2773507) B2773507
theorem B3509657 : Blo 1642020 3509657 := bstep (se 2 (by rfl) ⟨1316121, by rfl⟩ : syracuseStep 3509657 = 2632243) B2632243
theorem B12471731 : Blo 1642020 12471731 := bstep (se 1 (by rfl) ⟨9353798, by rfl⟩ : syracuseStep 12471731 = 18707597) B18707597
theorem B3698099 : Blo 1642020 3698099 := bstep (se 1 (by rfl) ⟨2773574, by rfl⟩ : syracuseStep 3698099 = 5547149) B5547149
theorem B2772427 : Blo 1642020 2772427 := bstep (se 1 (by rfl) ⟨2079320, by rfl⟩ : syracuseStep 2772427 = 4158641) B4158641
theorem B3698135 : Blo 1642020 3698135 := bstep (se 1 (by rfl) ⟨2773601, by rfl⟩ : syracuseStep 3698135 = 5547203) B5547203
theorem B6237719 : Blo 1642020 6237719 := bstep (se 1 (by rfl) ⟨4678289, by rfl⟩ : syracuseStep 6237719 = 9356579) B9356579
theorem B2960921 : Blo 1642020 2960921 := bstep (se 2 (by rfl) ⟨1110345, by rfl⟩ : syracuseStep 2960921 = 2220691) B2220691
theorem B1642027 : Blo 1642020 1642027 := bstep (se 1 (by rfl) ⟨1231520, by rfl⟩ : syracuseStep 1642027 = 2463041) B2463041
theorem B1642039 : Blo 1642020 1642039 := bstep (se 1 (by rfl) ⟨1231529, by rfl⟩ : syracuseStep 1642039 = 2463059) B2463059
theorem B1642059 : Blo 1642020 1642059 := bstep (se 1 (by rfl) ⟨1231544, by rfl⟩ : syracuseStep 1642059 = 2463089) B2463089
theorem B1642071 : Blo 1642020 1642071 := bstep (se 1 (by rfl) ⟨1231553, by rfl⟩ : syracuseStep 1642071 = 2463107) B2463107
theorem B2772569 : Blo 1642020 2772569 := bstep (se 2 (by rfl) ⟨1039713, by rfl⟩ : syracuseStep 2772569 = 2079427) B2079427
theorem B1642091 : Blo 1642020 1642091 := bstep (se 1 (by rfl) ⟨1231568, by rfl⟩ : syracuseStep 1642091 = 2463137) B2463137
theorem B1642103 : Blo 1642020 1642103 := bstep (se 1 (by rfl) ⟨1231577, by rfl⟩ : syracuseStep 1642103 = 2463155) B2463155
theorem B1642123 : Blo 1642020 1642123 := bstep (se 1 (by rfl) ⟨1231592, by rfl⟩ : syracuseStep 1642123 = 2463185) B2463185
theorem B3698315 : Blo 1642020 3698315 := bstep (se 1 (by rfl) ⟨2773736, by rfl⟩ : syracuseStep 3698315 = 5547473) B5547473
theorem B1642135 : Blo 1642020 1642135 := bstep (se 1 (by rfl) ⟨1231601, by rfl⟩ : syracuseStep 1642135 = 2463203) B2463203
theorem B1642155 : Blo 1642020 1642155 := bstep (se 1 (by rfl) ⟨1231616, by rfl⟩ : syracuseStep 1642155 = 2463233) B2463233
theorem B1642167 : Blo 1642020 1642167 := bstep (se 1 (by rfl) ⟨1231625, by rfl⟩ : syracuseStep 1642167 = 2463251) B2463251
theorem B3698369 : Blo 1642020 3698369 := bstep (se 2 (by rfl) ⟨1386888, by rfl⟩ : syracuseStep 3698369 = 2773777) B2773777
theorem B1642187 : Blo 1642020 1642187 := bstep (se 1 (by rfl) ⟨1231640, by rfl⟩ : syracuseStep 1642187 = 2463281) B2463281
theorem B2338507 : Blo 1642020 2338507 := bstep (se 1 (by rfl) ⟨1753880, by rfl⟩ : syracuseStep 2338507 = 3507761) B3507761
theorem B1642199 : Blo 1642020 1642199 := bstep (se 1 (by rfl) ⟨1231649, by rfl⟩ : syracuseStep 1642199 = 2463299) B2463299
theorem B2772697 : Blo 1642020 2772697 := bstep (se 2 (by rfl) ⟨1039761, by rfl⟩ : syracuseStep 2772697 = 2079523) B2079523
theorem B6237917 : Blo 1642020 6237917 := bstep (se 3 (by rfl) ⟨1169609, by rfl⟩ : syracuseStep 6237917 = 2339219) B2339219
theorem B1642219 : Blo 1642020 1642219 := bstep (se 1 (by rfl) ⟨1231664, by rfl⟩ : syracuseStep 1642219 = 2463329) B2463329
theorem B1642231 : Blo 1642020 1642231 := bstep (se 1 (by rfl) ⟨1231673, by rfl⟩ : syracuseStep 1642231 = 2463347) B2463347
theorem B1642251 : Blo 1642020 1642251 := bstep (se 1 (by rfl) ⟨1231688, by rfl⟩ : syracuseStep 1642251 = 2463377) B2463377
theorem B7999249 : Blo 1642020 7999249 := bstep (se 2 (by rfl) ⟨2999718, by rfl⟩ : syracuseStep 7999249 = 5999437) B5999437
theorem B1642263 : Blo 1642020 1642263 := bstep (se 1 (by rfl) ⟨1231697, by rfl⟩ : syracuseStep 1642263 = 2463395) B2463395
theorem B1642283 : Blo 1642020 1642283 := bstep (se 1 (by rfl) ⟨1231712, by rfl⟩ : syracuseStep 1642283 = 2463425) B2463425
theorem B3510067 : Blo 1642020 3510067 := bstep (se 1 (by rfl) ⟨2632550, by rfl⟩ : syracuseStep 3510067 = 5265101) B5265101
theorem B1642295 : Blo 1642020 1642295 := bstep (se 1 (by rfl) ⟨1231721, by rfl⟩ : syracuseStep 1642295 = 2463443) B2463443
theorem B1642315 : Blo 1642020 1642315 := bstep (se 1 (by rfl) ⟨1231736, by rfl⟩ : syracuseStep 1642315 = 2463473) B2463473
theorem B4681547 : Blo 1642020 4681547 := bstep (se 1 (by rfl) ⟨3511160, by rfl⟩ : syracuseStep 4681547 = 7022321) B7022321
theorem B1642327 : Blo 1642020 1642327 := bstep (se 1 (by rfl) ⟨1231745, by rfl⟩ : syracuseStep 1642327 = 2463491) B2463491
theorem B1642347 : Blo 1642020 1642347 := bstep (se 1 (by rfl) ⟨1231760, by rfl⟩ : syracuseStep 1642347 = 2463521) B2463521
theorem B1642359 : Blo 1642020 1642359 := bstep (se 1 (by rfl) ⟨1231769, by rfl⟩ : syracuseStep 1642359 = 2463539) B2463539
theorem B1642379 : Blo 1642020 1642379 := bstep (se 1 (by rfl) ⟨1231784, by rfl⟩ : syracuseStep 1642379 = 2463569) B2463569
theorem B1642391 : Blo 1642020 1642391 := bstep (se 1 (by rfl) ⟨1231793, by rfl⟩ : syracuseStep 1642391 = 2463587) B2463587
theorem B5263255 : Blo 1642020 5263255 := bstep (se 1 (by rfl) ⟨3947441, by rfl⟩ : syracuseStep 5263255 = 7894883) B7894883
theorem B3698585 : Blo 1642020 3698585 := bstep (se 2 (by rfl) ⟨1386969, by rfl⟩ : syracuseStep 3698585 = 2773939) B2773939
theorem B1642411 : Blo 1642020 1642411 := bstep (se 1 (by rfl) ⟨1231808, by rfl⟩ : syracuseStep 1642411 = 2463617) B2463617
theorem B1642423 : Blo 1642020 1642423 := bstep (se 1 (by rfl) ⟨1231817, by rfl⟩ : syracuseStep 1642423 = 2463635) B2463635
theorem B1642443 : Blo 1642020 1642443 := bstep (se 1 (by rfl) ⟨1231832, by rfl⟩ : syracuseStep 1642443 = 2463665) B2463665
theorem B1642455 : Blo 1642020 1642455 := bstep (se 1 (by rfl) ⟨1231841, by rfl⟩ : syracuseStep 1642455 = 2463683) B2463683
theorem B1642475 : Blo 1642020 1642475 := bstep (se 1 (by rfl) ⟨1231856, by rfl⟩ : syracuseStep 1642475 = 2463713) B2463713
theorem B3698675 : Blo 1642020 3698675 := bstep (se 1 (by rfl) ⟨2774006, by rfl⟩ : syracuseStep 3698675 = 5548013) B5548013
theorem B1642487 : Blo 1642020 1642487 := bstep (se 1 (by rfl) ⟨1231865, by rfl⟩ : syracuseStep 1642487 = 2463731) B2463731
theorem B1642507 : Blo 1642020 1642507 := bstep (se 1 (by rfl) ⟨1231880, by rfl⟩ : syracuseStep 1642507 = 2463761) B2463761
theorem B5541911 : Blo 1642020 5541911 := bstep (se 1 (by rfl) ⟨4156433, by rfl⟩ : syracuseStep 5541911 = 8312867) B8312867
theorem B1642519 : Blo 1642020 1642519 := bstep (se 1 (by rfl) ⟨1231889, by rfl⟩ : syracuseStep 1642519 = 2463779) B2463779
theorem B3698711 : Blo 1642020 3698711 := bstep (se 1 (by rfl) ⟨2774033, by rfl⟩ : syracuseStep 3698711 = 5548067) B5548067
theorem B1642539 : Blo 1642020 1642539 := bstep (se 1 (by rfl) ⟨1231904, by rfl⟩ : syracuseStep 1642539 = 2463809) B2463809
theorem B1642551 : Blo 1642020 1642551 := bstep (se 1 (by rfl) ⟨1231913, by rfl⟩ : syracuseStep 1642551 = 2463827) B2463827
theorem B26660933 : Blo 1642020 26660933 := bstep (se 4 (by rfl) ⟨2499462, by rfl⟩ : syracuseStep 26660933 = 4998925) B4998925
theorem B1847371 : Blo 1642020 1847371 := bstep (se 1 (by rfl) ⟨1385528, by rfl⟩ : syracuseStep 1847371 = 2771057) B2771057
theorem B1642571 : Blo 1642020 1642571 := bstep (se 1 (by rfl) ⟨1231928, by rfl⟩ : syracuseStep 1642571 = 2463857) B2463857
theorem B1642583 : Blo 1642020 1642583 := bstep (se 1 (by rfl) ⟨1231937, by rfl⟩ : syracuseStep 1642583 = 2463875) B2463875
theorem B1642603 : Blo 1642020 1642603 := bstep (se 1 (by rfl) ⟨1231952, by rfl⟩ : syracuseStep 1642603 = 2463905) B2463905
theorem B1642615 : Blo 1642020 1642615 := bstep (se 1 (by rfl) ⟨1231961, by rfl⟩ : syracuseStep 1642615 = 2463923) B2463923
theorem B1642635 : Blo 1642020 1642635 := bstep (se 1 (by rfl) ⟨1231976, by rfl⟩ : syracuseStep 1642635 = 2463953) B2463953
theorem B1642647 : Blo 1642020 1642647 := bstep (se 1 (by rfl) ⟨1231985, by rfl⟩ : syracuseStep 1642647 = 2463971) B2463971
theorem B1642667 : Blo 1642020 1642667 := bstep (se 1 (by rfl) ⟨1232000, by rfl⟩ : syracuseStep 1642667 = 2464001) B2464001
theorem B1847479 : Blo 1642020 1847479 := bstep (se 1 (by rfl) ⟨1385609, by rfl⟩ : syracuseStep 1847479 = 2771219) B2771219
theorem B1642679 : Blo 1642020 1642679 := bstep (se 1 (by rfl) ⟨1232009, by rfl⟩ : syracuseStep 1642679 = 2464019) B2464019
theorem B1642699 : Blo 1642020 1642699 := bstep (se 1 (by rfl) ⟨1232024, by rfl⟩ : syracuseStep 1642699 = 2464049) B2464049
theorem B3698891 : Blo 1642020 3698891 := bstep (se 1 (by rfl) ⟨2774168, by rfl⟩ : syracuseStep 3698891 = 5548337) B5548337
theorem B1642711 : Blo 1642020 1642711 := bstep (se 1 (by rfl) ⟨1232033, by rfl⟩ : syracuseStep 1642711 = 2464067) B2464067
theorem B2371799 : Blo 1642020 2371799 := bstep (se 1 (by rfl) ⟨1778849, by rfl⟩ : syracuseStep 2371799 = 3557699) B3557699
theorem B1642731 : Blo 1642020 1642731 := bstep (se 1 (by rfl) ⟨1232048, by rfl⟩ : syracuseStep 1642731 = 2464097) B2464097
theorem B1642743 : Blo 1642020 1642743 := bstep (se 1 (by rfl) ⟨1232057, by rfl⟩ : syracuseStep 1642743 = 2464115) B2464115
theorem B3698945 : Blo 1642020 3698945 := bstep (se 2 (by rfl) ⟨1387104, by rfl⟩ : syracuseStep 3698945 = 2774209) B2774209
theorem B1642763 : Blo 1642020 1642763 := bstep (se 1 (by rfl) ⟨1232072, by rfl⟩ : syracuseStep 1642763 = 2464145) B2464145
theorem B1642775 : Blo 1642020 1642775 := bstep (se 1 (by rfl) ⟨1232081, by rfl⟩ : syracuseStep 1642775 = 2464163) B2464163
theorem B2773271 : Blo 1642020 2773271 := bstep (se 1 (by rfl) ⟨2079953, by rfl⟩ : syracuseStep 2773271 = 4159907) B4159907
theorem B1642795 : Blo 1642020 1642795 := bstep (se 1 (by rfl) ⟨1232096, by rfl⟩ : syracuseStep 1642795 = 2464193) B2464193
theorem B1642807 : Blo 1642020 1642807 := bstep (se 1 (by rfl) ⟨1232105, by rfl⟩ : syracuseStep 1642807 = 2464211) B2464211
theorem B1642827 : Blo 1642020 1642827 := bstep (se 1 (by rfl) ⟨1232120, by rfl⟩ : syracuseStep 1642827 = 2464241) B2464241
theorem B1642839 : Blo 1642020 1642839 := bstep (se 1 (by rfl) ⟨1232129, by rfl⟩ : syracuseStep 1642839 = 2464259) B2464259
theorem B21057893 : Blo 1642020 21057893 := bstep (se 4 (by rfl) ⟨1974177, by rfl⟩ : syracuseStep 21057893 = 3948355) B3948355
theorem B13513061 : Blo 1642020 13513061 := bstep (se 4 (by rfl) ⟨1266849, by rfl⟩ : syracuseStep 13513061 = 2533699) B2533699
theorem B1847659 : Blo 1642020 1847659 := bstep (se 1 (by rfl) ⟨1385744, by rfl⟩ : syracuseStep 1847659 = 2771489) B2771489
theorem B1642859 : Blo 1642020 1642859 := bstep (se 1 (by rfl) ⟨1232144, by rfl⟩ : syracuseStep 1642859 = 2464289) B2464289
theorem B1642871 : Blo 1642020 1642871 := bstep (se 1 (by rfl) ⟨1232153, by rfl⟩ : syracuseStep 1642871 = 2464307) B2464307
theorem B1642891 : Blo 1642020 1642891 := bstep (se 1 (by rfl) ⟨1232168, by rfl⟩ : syracuseStep 1642891 = 2464337) B2464337
theorem B1642903 : Blo 1642020 1642903 := bstep (se 1 (by rfl) ⟨1232177, by rfl⟩ : syracuseStep 1642903 = 2464355) B2464355
theorem B2773399 : Blo 1642020 2773399 := bstep (se 1 (by rfl) ⟨2080049, by rfl⟩ : syracuseStep 2773399 = 4160099) B4160099
theorem B1642923 : Blo 1642020 1642923 := bstep (se 1 (by rfl) ⟨1232192, by rfl⟩ : syracuseStep 1642923 = 2464385) B2464385
theorem B1642935 : Blo 1642020 1642935 := bstep (se 1 (by rfl) ⟨1232201, by rfl⟩ : syracuseStep 1642935 = 2464403) B2464403
theorem B1642955 : Blo 1642020 1642955 := bstep (se 1 (by rfl) ⟨1232216, by rfl⟩ : syracuseStep 1642955 = 2464433) B2464433
theorem B1847767 : Blo 1642020 1847767 := bstep (se 1 (by rfl) ⟨1385825, by rfl⟩ : syracuseStep 1847767 = 2771651) B2771651
theorem B1642967 : Blo 1642020 1642967 := bstep (se 1 (by rfl) ⟨1232225, by rfl⟩ : syracuseStep 1642967 = 2464451) B2464451
theorem B1642987 : Blo 1642020 1642987 := bstep (se 1 (by rfl) ⟨1232240, by rfl⟩ : syracuseStep 1642987 = 2464481) B2464481
theorem B1642999 : Blo 1642020 1642999 := bstep (se 1 (by rfl) ⟨1232249, by rfl⟩ : syracuseStep 1642999 = 2464499) B2464499
theorem B3510785 : Blo 1642020 3510785 := bstep (se 2 (by rfl) ⟨1316544, by rfl⟩ : syracuseStep 3510785 = 2633089) B2633089
theorem B1643019 : Blo 1642020 1643019 := bstep (se 1 (by rfl) ⟨1232264, by rfl⟩ : syracuseStep 1643019 = 2464529) B2464529
theorem B1643031 : Blo 1642020 1643031 := bstep (se 1 (by rfl) ⟨1232273, by rfl⟩ : syracuseStep 1643031 = 2464547) B2464547
theorem B1643051 : Blo 1642020 1643051 := bstep (se 1 (by rfl) ⟨1232288, by rfl⟩ : syracuseStep 1643051 = 2464577) B2464577
theorem B5542451 : Blo 1642020 5542451 := bstep (se 1 (by rfl) ⟨4156838, by rfl⟩ : syracuseStep 5542451 = 8313677) B8313677
theorem B1643063 : Blo 1642020 1643063 := bstep (se 1 (by rfl) ⟨1232297, by rfl⟩ : syracuseStep 1643063 = 2464595) B2464595
theorem B1643083 : Blo 1642020 1643083 := bstep (se 1 (by rfl) ⟨1232312, by rfl⟩ : syracuseStep 1643083 = 2464625) B2464625
theorem B1643095 : Blo 1642020 1643095 := bstep (se 1 (by rfl) ⟨1232321, by rfl⟩ : syracuseStep 1643095 = 2464643) B2464643
theorem B1643115 : Blo 1642020 1643115 := bstep (se 1 (by rfl) ⟨1232336, by rfl⟩ : syracuseStep 1643115 = 2464673) B2464673
theorem B3117683 : Blo 1642020 3117683 := bstep (se 1 (by rfl) ⟨2338262, by rfl⟩ : syracuseStep 3117683 = 4676525) B4676525
theorem B1643127 : Blo 1642020 1643127 := bstep (se 1 (by rfl) ⟨1232345, by rfl⟩ : syracuseStep 1643127 = 2464691) B2464691
theorem B1847947 : Blo 1642020 1847947 := bstep (se 1 (by rfl) ⟨1385960, by rfl⟩ : syracuseStep 1847947 = 2771921) B2771921
theorem B1643147 : Blo 1642020 1643147 := bstep (se 1 (by rfl) ⟨1232360, by rfl⟩ : syracuseStep 1643147 = 2464721) B2464721
theorem B1643159 : Blo 1642020 1643159 := bstep (se 1 (by rfl) ⟨1232369, by rfl⟩ : syracuseStep 1643159 = 2464739) B2464739
theorem B1643179 : Blo 1642020 1643179 := bstep (se 1 (by rfl) ⟨1232384, by rfl⟩ : syracuseStep 1643179 = 2464769) B2464769
theorem B1643191 : Blo 1642020 1643191 := bstep (se 1 (by rfl) ⟨1232393, by rfl⟩ : syracuseStep 1643191 = 2464787) B2464787
theorem B4158155 : Blo 1642020 4158155 := bstep (se 1 (by rfl) ⟨3118616, by rfl⟩ : syracuseStep 4158155 = 6237233) B6237233
theorem B5264075 : Blo 1642020 5264075 := bstep (se 1 (by rfl) ⟨3948056, by rfl⟩ : syracuseStep 5264075 = 7896113) B7896113
theorem B1643211 : Blo 1642020 1643211 := bstep (se 1 (by rfl) ⟨1232408, by rfl⟩ : syracuseStep 1643211 = 2464817) B2464817
theorem B1643223 : Blo 1642020 1643223 := bstep (se 1 (by rfl) ⟨1232417, by rfl⟩ : syracuseStep 1643223 = 2464835) B2464835
theorem B1643243 : Blo 1642020 1643243 := bstep (se 1 (by rfl) ⟨1232432, by rfl⟩ : syracuseStep 1643243 = 2464865) B2464865
theorem B1848055 : Blo 1642020 1848055 := bstep (se 1 (by rfl) ⟨1386041, by rfl⟩ : syracuseStep 1848055 = 2772083) B2772083
theorem B1643255 : Blo 1642020 1643255 := bstep (se 1 (by rfl) ⟨1232441, by rfl⟩ : syracuseStep 1643255 = 2464883) B2464883
theorem B1643275 : Blo 1642020 1643275 := bstep (se 1 (by rfl) ⟨1232456, by rfl⟩ : syracuseStep 1643275 = 2464913) B2464913
theorem B1643287 : Blo 1642020 1643287 := bstep (se 1 (by rfl) ⟨1232465, by rfl⟩ : syracuseStep 1643287 = 2464931) B2464931
theorem B1643307 : Blo 1642020 1643307 := bstep (se 1 (by rfl) ⟨1232480, by rfl⟩ : syracuseStep 1643307 = 2464961) B2464961
theorem B1643319 : Blo 1642020 1643319 := bstep (se 1 (by rfl) ⟨1232489, by rfl⟩ : syracuseStep 1643319 = 2464979) B2464979
theorem B5542721 : Blo 1642020 5542721 := bstep (se 2 (by rfl) ⟨2078520, by rfl⟩ : syracuseStep 5542721 = 4157041) B4157041
theorem B1643339 : Blo 1642020 1643339 := bstep (se 1 (by rfl) ⟨1232504, by rfl⟩ : syracuseStep 1643339 = 2465009) B2465009
theorem B1643351 : Blo 1642020 1643351 := bstep (se 1 (by rfl) ⟨1232513, by rfl⟩ : syracuseStep 1643351 = 2465027) B2465027
theorem B3511127 : Blo 1642020 3511127 := bstep (se 1 (by rfl) ⟨2633345, by rfl⟩ : syracuseStep 3511127 = 5266691) B5266691
theorem B12473189 : Blo 1642020 12473189 := bstep (se 4 (by rfl) ⟨1169361, by rfl⟩ : syracuseStep 12473189 = 2338723) B2338723
theorem B1643371 : Blo 1642020 1643371 := bstep (se 1 (by rfl) ⟨1232528, by rfl⟩ : syracuseStep 1643371 = 2465057) B2465057
theorem B1643383 : Blo 1642020 1643383 := bstep (se 1 (by rfl) ⟨1232537, by rfl⟩ : syracuseStep 1643383 = 2465075) B2465075
theorem B1643403 : Blo 1642020 1643403 := bstep (se 1 (by rfl) ⟨1232552, by rfl⟩ : syracuseStep 1643403 = 2465105) B2465105
theorem B6665105 : Blo 1642020 6665105 := bstep (se 2 (by rfl) ⟨2499414, by rfl⟩ : syracuseStep 6665105 = 4998829) B4998829
theorem B1643415 : Blo 1642020 1643415 := bstep (se 1 (by rfl) ⟨1232561, by rfl⟩ : syracuseStep 1643415 = 2465123) B2465123
theorem B1848235 : Blo 1642020 1848235 := bstep (se 1 (by rfl) ⟨1386176, by rfl⟩ : syracuseStep 1848235 = 2772353) B2772353
theorem B1643435 : Blo 1642020 1643435 := bstep (se 1 (by rfl) ⟨1232576, by rfl⟩ : syracuseStep 1643435 = 2465153) B2465153
theorem B1643447 : Blo 1642020 1643447 := bstep (se 1 (by rfl) ⟨1232585, by rfl⟩ : syracuseStep 1643447 = 2465171) B2465171
theorem B2962369 : Blo 1642020 2962369 := bstep (se 2 (by rfl) ⟨1110888, by rfl⟩ : syracuseStep 2962369 = 2221777) B2221777
theorem B1643467 : Blo 1642020 1643467 := bstep (se 1 (by rfl) ⟨1232600, by rfl⟩ : syracuseStep 1643467 = 2465201) B2465201
theorem B1643479 : Blo 1642020 1643479 := bstep (se 1 (by rfl) ⟨1232609, by rfl⟩ : syracuseStep 1643479 = 2465219) B2465219
theorem B1643499 : Blo 1642020 1643499 := bstep (se 1 (by rfl) ⟨1232624, by rfl⟩ : syracuseStep 1643499 = 2465249) B2465249
theorem B1643511 : Blo 1642020 1643511 := bstep (se 1 (by rfl) ⟨1232633, by rfl⟩ : syracuseStep 1643511 = 2465267) B2465267
theorem B1643531 : Blo 1642020 1643531 := bstep (se 1 (by rfl) ⟨1232648, by rfl⟩ : syracuseStep 1643531 = 2465297) B2465297
theorem B2774027 : Blo 1642020 2774027 := bstep (se 1 (by rfl) ⟨2080520, by rfl⟩ : syracuseStep 2774027 = 4161041) B4161041
theorem B8434705 : Blo 1642020 8434705 := bstep (se 2 (by rfl) ⟨3163014, by rfl⟩ : syracuseStep 8434705 = 6326029) B6326029
theorem B1848343 : Blo 1642020 1848343 := bstep (se 1 (by rfl) ⟨1386257, by rfl⟩ : syracuseStep 1848343 = 2772515) B2772515
theorem B1643543 : Blo 1642020 1643543 := bstep (se 1 (by rfl) ⟨1232657, by rfl⟩ : syracuseStep 1643543 = 2465315) B2465315
theorem B1643563 : Blo 1642020 1643563 := bstep (se 1 (by rfl) ⟨1232672, by rfl⟩ : syracuseStep 1643563 = 2465345) B2465345
theorem B1643575 : Blo 1642020 1643575 := bstep (se 1 (by rfl) ⟨1232681, by rfl⟩ : syracuseStep 1643575 = 2465363) B2465363
theorem B1643595 : Blo 1642020 1643595 := bstep (se 1 (by rfl) ⟨1232696, by rfl⟩ : syracuseStep 1643595 = 2465393) B2465393
theorem B1643607 : Blo 1642020 1643607 := bstep (se 1 (by rfl) ⟨1232705, by rfl⟩ : syracuseStep 1643607 = 2465411) B2465411
theorem B3118169 : Blo 1642020 3118169 := bstep (se 2 (by rfl) ⟨1169313, by rfl⟩ : syracuseStep 3118169 = 2338627) B2338627
theorem B1643627 : Blo 1642020 1643627 := bstep (se 1 (by rfl) ⟨1232720, by rfl⟩ : syracuseStep 1643627 = 2465441) B2465441
theorem B1643639 : Blo 1642020 1643639 := bstep (se 1 (by rfl) ⟨1232729, by rfl⟩ : syracuseStep 1643639 = 2465459) B2465459
theorem B1643659 : Blo 1642020 1643659 := bstep (se 1 (by rfl) ⟨1232744, by rfl⟩ : syracuseStep 1643659 = 2465489) B2465489
theorem B2774155 : Blo 1642020 2774155 := bstep (se 1 (by rfl) ⟨2080616, by rfl⟩ : syracuseStep 2774155 = 4161233) B4161233
theorem B1643671 : Blo 1642020 1643671 := bstep (se 1 (by rfl) ⟨1232753, by rfl⟩ : syracuseStep 1643671 = 2465507) B2465507
theorem B1643691 : Blo 1642020 1643691 := bstep (se 1 (by rfl) ⟨1232768, by rfl⟩ : syracuseStep 1643691 = 2465537) B2465537
theorem B1643703 : Blo 1642020 1643703 := bstep (se 1 (by rfl) ⟨1232777, by rfl⟩ : syracuseStep 1643703 = 2465555) B2465555
theorem B1848523 : Blo 1642020 1848523 := bstep (se 1 (by rfl) ⟨1386392, by rfl⟩ : syracuseStep 1848523 = 2772785) B2772785
theorem B1643723 : Blo 1642020 1643723 := bstep (se 1 (by rfl) ⟨1232792, by rfl⟩ : syracuseStep 1643723 = 2465585) B2465585
theorem B1643735 : Blo 1642020 1643735 := bstep (se 1 (by rfl) ⟨1232801, by rfl⟩ : syracuseStep 1643735 = 2465603) B2465603
theorem B1643755 : Blo 1642020 1643755 := bstep (se 1 (by rfl) ⟨1232816, by rfl⟩ : syracuseStep 1643755 = 2465633) B2465633
theorem B1643767 : Blo 1642020 1643767 := bstep (se 1 (by rfl) ⟨1232825, by rfl⟩ : syracuseStep 1643767 = 2465651) B2465651
theorem B1643787 : Blo 1642020 1643787 := bstep (se 1 (by rfl) ⟨1232840, by rfl⟩ : syracuseStep 1643787 = 2465681) B2465681
theorem B1643799 : Blo 1642020 1643799 := bstep (se 1 (by rfl) ⟨1232849, by rfl⟩ : syracuseStep 1643799 = 2465699) B2465699
theorem B1643819 : Blo 1642020 1643819 := bstep (se 1 (by rfl) ⟨1232864, by rfl⟩ : syracuseStep 1643819 = 2465729) B2465729
theorem B1848631 : Blo 1642020 1848631 := bstep (se 1 (by rfl) ⟨1386473, by rfl⟩ : syracuseStep 1848631 = 2772947) B2772947
theorem B1643831 : Blo 1642020 1643831 := bstep (se 1 (by rfl) ⟨1232873, by rfl⟩ : syracuseStep 1643831 = 2465747) B2465747
theorem B9352523 : Blo 1642020 9352523 := bstep (se 1 (by rfl) ⟨7014392, by rfl⟩ : syracuseStep 9352523 = 14028785) B14028785
theorem B12473675 : Blo 1642020 12473675 := bstep (se 1 (by rfl) ⟨9355256, by rfl⟩ : syracuseStep 12473675 = 18710513) B18710513
theorem B1643851 : Blo 1642020 1643851 := bstep (se 1 (by rfl) ⟨1232888, by rfl⟩ : syracuseStep 1643851 = 2465777) B2465777
theorem B1643863 : Blo 1642020 1643863 := bstep (se 1 (by rfl) ⟨1232897, by rfl⟩ : syracuseStep 1643863 = 2465795) B2465795
theorem B2463065 : Blo 1642020 2463065 := bstep (se 2 (by rfl) ⟨923649, by rfl⟩ : syracuseStep 2463065 = 1847299) B1847299
theorem B5543261 : Blo 1642020 5543261 := bstep (se 3 (by rfl) ⟨1039361, by rfl⟩ : syracuseStep 5543261 = 2078723) B2078723
theorem B29963621 : Blo 1642020 29963621 := bstep (se 4 (by rfl) ⟨2809089, by rfl⟩ : syracuseStep 29963621 = 5618179) B5618179
theorem B1643883 : Blo 1642020 1643883 := bstep (se 1 (by rfl) ⟨1232912, by rfl⟩ : syracuseStep 1643883 = 2465825) B2465825
theorem B1643895 : Blo 1642020 1643895 := bstep (se 1 (by rfl) ⟨1232921, by rfl⟩ : syracuseStep 1643895 = 2465843) B2465843
theorem B10532227 : Blo 1642020 10532227 := bstep (se 1 (by rfl) ⟨7899170, by rfl⟩ : syracuseStep 10532227 = 15798341) B15798341
theorem B1643915 : Blo 1642020 1643915 := bstep (se 1 (by rfl) ⟨1232936, by rfl⟩ : syracuseStep 1643915 = 2465873) B2465873
theorem B1643927 : Blo 1642020 1643927 := bstep (se 1 (by rfl) ⟨1232945, by rfl⟩ : syracuseStep 1643927 = 2465891) B2465891
theorem B1643947 : Blo 1642020 1643947 := bstep (se 1 (by rfl) ⟨1232960, by rfl⟩ : syracuseStep 1643947 = 2465921) B2465921
theorem B1643959 : Blo 1642020 1643959 := bstep (se 1 (by rfl) ⟨1232969, by rfl⟩ : syracuseStep 1643959 = 2465939) B2465939
theorem B2463179 : Blo 1642020 2463179 := bstep (se 1 (by rfl) ⟨1847384, by rfl⟩ : syracuseStep 2463179 = 3694769) B3694769
theorem B1643979 : Blo 1642020 1643979 := bstep (se 1 (by rfl) ⟨1232984, by rfl⟩ : syracuseStep 1643979 = 2465969) B2465969
theorem B2463191 : Blo 1642020 2463191 := bstep (se 1 (by rfl) ⟨1847393, by rfl⟩ : syracuseStep 2463191 = 3694787) B3694787
theorem B1643991 : Blo 1642020 1643991 := bstep (se 1 (by rfl) ⟨1232993, by rfl⟩ : syracuseStep 1643991 = 2465987) B2465987
theorem B1848811 : Blo 1642020 1848811 := bstep (se 1 (by rfl) ⟨1386608, by rfl⟩ : syracuseStep 1848811 = 2773217) B2773217
theorem B1644011 : Blo 1642020 1644011 := bstep (se 1 (by rfl) ⟨1233008, by rfl⟩ : syracuseStep 1644011 = 2466017) B2466017
theorem B14988817 : Blo 1642020 14988817 := bstep (se 2 (by rfl) ⟨5620806, by rfl⟩ : syracuseStep 14988817 = 11241613) B11241613
theorem B2463257 : Blo 1642020 2463257 := bstep (se 2 (by rfl) ⟨923721, by rfl⟩ : syracuseStep 2463257 = 1847443) B1847443
theorem B14980643 : Blo 1642020 14980643 := bstep (se 1 (by rfl) ⟨11235482, by rfl⟩ : syracuseStep 14980643 = 22470965) B22470965
theorem B19994147 : Blo 1642020 19994147 := bstep (se 1 (by rfl) ⟨14995610, by rfl⟩ : syracuseStep 19994147 = 29991221) B29991221
theorem B1898039 : Blo 1642020 1898039 := bstep (se 1 (by rfl) ⟨1423529, by rfl⟩ : syracuseStep 1898039 = 2847059) B2847059
theorem B1848919 : Blo 1642020 1848919 := bstep (se 1 (by rfl) ⟨1386689, by rfl⟩ : syracuseStep 1848919 = 2773379) B2773379
theorem B6239875 : Blo 1642020 6239875 := bstep (se 1 (by rfl) ⟨4679906, by rfl⟩ : syracuseStep 6239875 = 9359813) B9359813
theorem B8320643 : Blo 1642020 8320643 := bstep (se 1 (by rfl) ⟨6240482, by rfl⟩ : syracuseStep 8320643 = 12480965) B12480965
theorem B2463371 : Blo 1642020 2463371 := bstep (se 1 (by rfl) ⟨1847528, by rfl⟩ : syracuseStep 2463371 = 3695057) B3695057
theorem B2463383 : Blo 1642020 2463383 := bstep (se 1 (by rfl) ⟨1847537, by rfl⟩ : syracuseStep 2463383 = 3695075) B3695075
theorem B4159127 : Blo 1642020 4159127 := bstep (se 1 (by rfl) ⟨3119345, by rfl⟩ : syracuseStep 4159127 = 6238691) B6238691
theorem B10671767 : Blo 1642020 10671767 := bstep (se 1 (by rfl) ⟨8003825, by rfl⟩ : syracuseStep 10671767 = 16007651) B16007651
theorem B2463449 : Blo 1642020 2463449 := bstep (se 2 (by rfl) ⟨923793, by rfl⟩ : syracuseStep 2463449 = 1847587) B1847587
theorem B1849099 : Blo 1642020 1849099 := bstep (se 1 (by rfl) ⟨1386824, by rfl⟩ : syracuseStep 1849099 = 2773649) B2773649
theorem B15791917 : Blo 1642020 15791917 := bstep (se 3 (by rfl) ⟨2960984, by rfl⟩ : syracuseStep 15791917 = 5921969) B5921969
theorem B2463563 : Blo 1642020 2463563 := bstep (se 1 (by rfl) ⟨1847672, by rfl⟩ : syracuseStep 2463563 = 3695345) B3695345
theorem B2078551 : Blo 1642020 2078551 := bstep (se 1 (by rfl) ⟨1558913, by rfl⟩ : syracuseStep 2078551 = 3117827) B3117827
theorem B2463575 : Blo 1642020 2463575 := bstep (se 1 (by rfl) ⟨1847681, by rfl⟩ : syracuseStep 2463575 = 3695363) B3695363
theorem B1849207 : Blo 1642020 1849207 := bstep (se 1 (by rfl) ⟨1386905, by rfl⟩ : syracuseStep 1849207 = 2773811) B2773811
theorem B2463641 : Blo 1642020 2463641 := bstep (se 2 (by rfl) ⟨923865, by rfl⟩ : syracuseStep 2463641 = 1847731) B1847731
theorem B6240179 : Blo 1642020 6240179 := bstep (se 1 (by rfl) ⟨4680134, by rfl⟩ : syracuseStep 6240179 = 9360269) B9360269
theorem B2463755 : Blo 1642020 2463755 := bstep (se 1 (by rfl) ⟨1847816, by rfl⟩ : syracuseStep 2463755 = 3695633) B3695633
theorem B2463767 : Blo 1642020 2463767 := bstep (se 1 (by rfl) ⟨1847825, by rfl⟩ : syracuseStep 2463767 = 3695651) B3695651
theorem B3946519 : Blo 1642020 3946519 := bstep (se 1 (by rfl) ⟨2959889, by rfl⟩ : syracuseStep 3946519 = 5919779) B5919779
theorem B2250775 : Blo 1642020 2250775 := bstep (se 1 (by rfl) ⟨1688081, by rfl⟩ : syracuseStep 2250775 = 3376163) B3376163
theorem B1849387 : Blo 1642020 1849387 := bstep (se 1 (by rfl) ⟨1387040, by rfl⟩ : syracuseStep 1849387 = 2774081) B2774081
theorem B9361453 : Blo 1642020 9361453 := bstep (se 3 (by rfl) ⟨1755272, by rfl⟩ : syracuseStep 9361453 = 3510545) B3510545
theorem B2463833 : Blo 1642020 2463833 := bstep (se 2 (by rfl) ⟨923937, by rfl⟩ : syracuseStep 2463833 = 1847875) B1847875
theorem B2250841 : Blo 1642020 2250841 := bstep (se 2 (by rfl) ⟨844065, by rfl⟩ : syracuseStep 2250841 = 1688131) B1688131
theorem B7895191 : Blo 1642020 7895191 := bstep (se 1 (by rfl) ⟨5921393, by rfl⟩ : syracuseStep 7895191 = 11842787) B11842787
theorem B1849495 : Blo 1642020 1849495 := bstep (se 1 (by rfl) ⟨1387121, by rfl⟩ : syracuseStep 1849495 = 2774243) B2774243
theorem B2463947 : Blo 1642020 2463947 := bstep (se 1 (by rfl) ⟨1847960, by rfl⟩ : syracuseStep 2463947 = 3695921) B3695921
theorem B2463959 : Blo 1642020 2463959 := bstep (se 1 (by rfl) ⟨1847969, by rfl⟩ : syracuseStep 2463959 = 3695939) B3695939
theorem B2464025 : Blo 1642020 2464025 := bstep (se 2 (by rfl) ⟨924009, by rfl⟩ : syracuseStep 2464025 = 1848019) B1848019
theorem B4159795 : Blo 1642020 4159795 := bstep (se 1 (by rfl) ⟨3119846, by rfl⟩ : syracuseStep 4159795 = 6239693) B6239693
theorem B13318465 : Blo 1642020 13318465 := bstep (se 2 (by rfl) ⟨4994424, by rfl⟩ : syracuseStep 13318465 = 9988849) B9988849
theorem B12482909 : Blo 1642020 12482909 := bstep (se 3 (by rfl) ⟨2340545, by rfl⟩ : syracuseStep 12482909 = 4681091) B4681091
theorem B2464139 : Blo 1642020 2464139 := bstep (se 1 (by rfl) ⟨1848104, by rfl⟩ : syracuseStep 2464139 = 3696209) B3696209
theorem B2464151 : Blo 1642020 2464151 := bstep (se 1 (by rfl) ⟨1848113, by rfl⟩ : syracuseStep 2464151 = 3696227) B3696227
theorem B7018903 : Blo 1642020 7018903 := bstep (se 1 (by rfl) ⟨5264177, by rfl⟩ : syracuseStep 7018903 = 10528355) B10528355
theorem B4159937 : Blo 1642020 4159937 := bstep (se 2 (by rfl) ⟨1559976, by rfl⟩ : syracuseStep 4159937 = 3119953) B3119953
theorem B5544395 : Blo 1642020 5544395 := bstep (se 1 (by rfl) ⟨4158296, by rfl⟩ : syracuseStep 5544395 = 8316593) B8316593
theorem B2464217 : Blo 1642020 2464217 := bstep (se 2 (by rfl) ⟨924081, by rfl⟩ : syracuseStep 2464217 = 1848163) B1848163
theorem B7018973 : Blo 1642020 7018973 := bstep (se 3 (by rfl) ⟨1316057, by rfl⟩ : syracuseStep 7018973 = 2632115) B2632115
theorem B3119627 : Blo 1642020 3119627 := bstep (se 1 (by rfl) ⟨2339720, by rfl⟩ : syracuseStep 3119627 = 4679441) B4679441
theorem B6240833 : Blo 1642020 6240833 := bstep (se 2 (by rfl) ⟨2340312, by rfl⟩ : syracuseStep 6240833 = 4680625) B4680625
theorem B2464331 : Blo 1642020 2464331 := bstep (se 1 (by rfl) ⟨1848248, by rfl⟩ : syracuseStep 2464331 = 3696497) B3696497
theorem B2464343 : Blo 1642020 2464343 := bstep (se 1 (by rfl) ⟨1848257, by rfl⟩ : syracuseStep 2464343 = 3696515) B3696515
theorem B2079371 : Blo 1642020 2079371 := bstep (se 1 (by rfl) ⟨1559528, by rfl⟩ : syracuseStep 2079371 = 3119057) B3119057
theorem B2464409 : Blo 1642020 2464409 := bstep (se 2 (by rfl) ⟨924153, by rfl⟩ : syracuseStep 2464409 = 1848307) B1848307
theorem B4741811 : Blo 1642020 4741811 := bstep (se 1 (by rfl) ⟨3556358, by rfl⟩ : syracuseStep 4741811 = 7112717) B7112717
theorem B3119809 : Blo 1642020 3119809 := bstep (se 2 (by rfl) ⟨1169928, by rfl⟩ : syracuseStep 3119809 = 2339857) B2339857
theorem B5544665 : Blo 1642020 5544665 := bstep (se 2 (by rfl) ⟨2079249, by rfl⟩ : syracuseStep 5544665 = 4158499) B4158499
theorem B94714595 : Blo 1642020 94714595 := bstep (se 1 (by rfl) ⟨71035946, by rfl⟩ : syracuseStep 94714595 = 142071893) B142071893
theorem B2464523 : Blo 1642020 2464523 := bstep (se 1 (by rfl) ⟨1848392, by rfl⟩ : syracuseStep 2464523 = 3696785) B3696785
theorem B2464535 : Blo 1642020 2464535 := bstep (se 1 (by rfl) ⟨1848401, by rfl⟩ : syracuseStep 2464535 = 3696803) B3696803
theorem B2464601 : Blo 1642020 2464601 := bstep (se 2 (by rfl) ⟨924225, by rfl⟩ : syracuseStep 2464601 = 1848451) B1848451
theorem B6749021 : Blo 1642020 6749021 := bstep (se 3 (by rfl) ⟨1265441, by rfl⟩ : syracuseStep 6749021 = 2530883) B2530883
theorem B9354163 : Blo 1642020 9354163 := bstep (se 1 (by rfl) ⟨7015622, by rfl⟩ : syracuseStep 9354163 = 14031245) B14031245
theorem B2464715 : Blo 1642020 2464715 := bstep (se 1 (by rfl) ⟨1848536, by rfl⟩ : syracuseStep 2464715 = 3697073) B3697073
theorem B2464727 : Blo 1642020 2464727 := bstep (se 1 (by rfl) ⟨1848545, by rfl⟩ : syracuseStep 2464727 = 3697091) B3697091
theorem B2464793 : Blo 1642020 2464793 := bstep (se 2 (by rfl) ⟨924297, by rfl⟩ : syracuseStep 2464793 = 1848595) B1848595
theorem B5135425 : Blo 1642020 5135425 := bstep (se 2 (by rfl) ⟨1925784, by rfl⟩ : syracuseStep 5135425 = 3851569) B3851569
theorem B3120257 : Blo 1642020 3120257 := bstep (se 2 (by rfl) ⟨1170096, by rfl⟩ : syracuseStep 3120257 = 2340193) B2340193
theorem B2464907 : Blo 1642020 2464907 := bstep (se 1 (by rfl) ⟨1848680, by rfl⟩ : syracuseStep 2464907 = 3697361) B3697361
theorem B2464919 : Blo 1642020 2464919 := bstep (se 1 (by rfl) ⟨1848689, by rfl⟩ : syracuseStep 2464919 = 3697379) B3697379
theorem B7019723 : Blo 1642020 7019723 := bstep (se 1 (by rfl) ⟨5264792, by rfl⟩ : syracuseStep 7019723 = 10529585) B10529585
theorem B2464985 : Blo 1642020 2464985 := bstep (se 2 (by rfl) ⟨924369, by rfl⟩ : syracuseStep 2464985 = 1848739) B1848739
theorem B13499713 : Blo 1642020 13499713 := bstep (se 2 (by rfl) ⟨5062392, by rfl⟩ : syracuseStep 13499713 = 10124785) B10124785
theorem B2465099 : Blo 1642020 2465099 := bstep (se 1 (by rfl) ⟨1848824, by rfl⟩ : syracuseStep 2465099 = 3697649) B3697649
theorem B2080075 : Blo 1642020 2080075 := bstep (se 1 (by rfl) ⟨1560056, by rfl⟩ : syracuseStep 2080075 = 3120113) B3120113
theorem B2465111 : Blo 1642020 2465111 := bstep (se 1 (by rfl) ⟨1848833, by rfl⟩ : syracuseStep 2465111 = 3697667) B3697667
theorem B4742489 : Blo 1642020 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B5545367 : Blo 1642020 5545367 := bstep (se 1 (by rfl) ⟨4159025, by rfl⟩ : syracuseStep 5545367 = 8318051) B8318051
theorem B2465177 : Blo 1642020 2465177 := bstep (se 2 (by rfl) ⟨924441, by rfl⟩ : syracuseStep 2465177 = 1848883) B1848883
theorem B3120599 : Blo 1642020 3120599 := bstep (se 1 (by rfl) ⟨2340449, by rfl⟩ : syracuseStep 3120599 = 4680899) B4680899
theorem B2465291 : Blo 1642020 2465291 := bstep (se 1 (by rfl) ⟨1848968, by rfl⟩ : syracuseStep 2465291 = 3697937) B3697937
theorem B5619223 : Blo 1642020 5619223 := bstep (se 1 (by rfl) ⟨4214417, by rfl⟩ : syracuseStep 5619223 = 8428835) B8428835
theorem B2465303 : Blo 1642020 2465303 := bstep (se 1 (by rfl) ⟨1848977, by rfl⟩ : syracuseStep 2465303 = 3697955) B3697955
theorem B21044771 : Blo 1642020 21044771 := bstep (se 1 (by rfl) ⟨15783578, by rfl⟩ : syracuseStep 21044771 = 31567157) B31567157
theorem B22478411 : Blo 1642020 22478411 := bstep (se 1 (by rfl) ⟨16858808, by rfl⟩ : syracuseStep 22478411 = 33717617) B33717617
theorem B2080343 : Blo 1642020 2080343 := bstep (se 1 (by rfl) ⟨1560257, by rfl⟩ : syracuseStep 2080343 = 3120515) B3120515
theorem B2465369 : Blo 1642020 2465369 := bstep (se 2 (by rfl) ⟨924513, by rfl⟩ : syracuseStep 2465369 = 1849027) B1849027
theorem B4161203 : Blo 1642020 4161203 := bstep (se 1 (by rfl) ⟨3120902, by rfl⟩ : syracuseStep 4161203 = 6241805) B6241805
theorem B2465483 : Blo 1642020 2465483 := bstep (se 1 (by rfl) ⟨1849112, by rfl⟩ : syracuseStep 2465483 = 3698225) B3698225
theorem B2465495 : Blo 1642020 2465495 := bstep (se 1 (by rfl) ⟨1849121, by rfl⟩ : syracuseStep 2465495 = 3698243) B3698243
theorem B2465561 : Blo 1642020 2465561 := bstep (se 2 (by rfl) ⟨924585, by rfl⟩ : syracuseStep 2465561 = 1849171) B1849171
theorem B6242093 : Blo 1642020 6242093 := bstep (se 3 (by rfl) ⟨1170392, by rfl⟩ : syracuseStep 6242093 = 2340785) B2340785
theorem B6242123 : Blo 1642020 6242123 := bstep (se 1 (by rfl) ⟨4681592, by rfl⟩ : syracuseStep 6242123 = 9363185) B9363185
theorem B2465675 : Blo 1642020 2465675 := bstep (se 1 (by rfl) ⟨1849256, by rfl⟩ : syracuseStep 2465675 = 3698513) B3698513
theorem B4677527 : Blo 1642020 4677527 := bstep (se 1 (by rfl) ⟨3508145, by rfl⟩ : syracuseStep 4677527 = 7016291) B7016291
theorem B2465687 : Blo 1642020 2465687 := bstep (se 1 (by rfl) ⟨1849265, by rfl⟩ : syracuseStep 2465687 = 3698531) B3698531
theorem B5545907 : Blo 1642020 5545907 := bstep (se 1 (by rfl) ⟨4159430, by rfl⟩ : syracuseStep 5545907 = 8318861) B8318861
theorem B3694553 : Blo 1642020 3694553 := bstep (se 2 (by rfl) ⟨1385457, by rfl⟩ : syracuseStep 3694553 = 2770915) B2770915
theorem B2465753 : Blo 1642020 2465753 := bstep (se 2 (by rfl) ⟨924657, by rfl⟩ : syracuseStep 2465753 = 1849315) B1849315
theorem B3694607 : Blo 1642020 3694607 := bstep (se 1 (by rfl) ⟨2770955, by rfl⟩ : syracuseStep 3694607 = 5541911) B5541911
theorem B2465807 : Blo 1642020 2465807 := bstep (se 1 (by rfl) ⟨1849355, by rfl⟩ : syracuseStep 2465807 = 3698711) B3698711
theorem B3694625 : Blo 1642020 3694625 := bstep (se 2 (by rfl) ⟨1385484, by rfl⟩ : syracuseStep 3694625 = 2770969) B2770969
theorem B2465849 : Blo 1642020 2465849 := bstep (se 2 (by rfl) ⟨924693, by rfl⟩ : syracuseStep 2465849 = 1849387) B1849387
theorem B2465927 : Blo 1642020 2465927 := bstep (se 1 (by rfl) ⟨1849445, by rfl⟩ : syracuseStep 2465927 = 3698891) B3698891
theorem B2465963 : Blo 1642020 2465963 := bstep (se 1 (by rfl) ⟨1849472, by rfl⟩ : syracuseStep 2465963 = 3698945) B3698945
theorem B10526921 : Blo 1642020 10526921 := bstep (se 2 (by rfl) ⟨3947595, by rfl⟩ : syracuseStep 10526921 = 7895191) B7895191
theorem B2465993 : Blo 1642020 2465993 := bstep (se 2 (by rfl) ⟨924747, by rfl⟩ : syracuseStep 2465993 = 1849495) B1849495
theorem B3694967 : Blo 1642020 3694967 := bstep (se 1 (by rfl) ⟨2771225, by rfl⟩ : syracuseStep 3694967 = 5542451) B5542451
theorem B5546393 : Blo 1642020 5546393 := bstep (se 2 (by rfl) ⟨2079897, by rfl⟩ : syracuseStep 5546393 = 4159795) B4159795
theorem B1753607 : Blo 1642020 1753607 := bstep (se 1 (by rfl) ⟨1315205, by rfl⟩ : syracuseStep 1753607 = 2630411) B2630411
theorem B18719261 : Blo 1642020 18719261 := bstep (se 3 (by rfl) ⟨3509861, by rfl⟩ : syracuseStep 18719261 = 7019723) B7019723
theorem B3695147 : Blo 1642020 3695147 := bstep (se 1 (by rfl) ⟨2771360, by rfl⟩ : syracuseStep 3695147 = 5542721) B5542721
theorem B6324797 : Blo 1642020 6324797 := bstep (se 3 (by rfl) ⟨1185899, by rfl⟩ : syracuseStep 6324797 = 2371799) B2371799
theorem B8315459 : Blo 1642020 8315459 := bstep (se 1 (by rfl) ⟨6236594, by rfl⟩ : syracuseStep 8315459 = 12473189) B12473189
theorem B9355895 : Blo 1642020 9355895 := bstep (se 1 (by rfl) ⟨7016921, by rfl⟩ : syracuseStep 9355895 = 14033843) B14033843
theorem B1753735 : Blo 1642020 1753735 := bstep (se 1 (by rfl) ⟨1315301, by rfl⟩ : syracuseStep 1753735 = 2630603) B2630603
theorem B5923529 : Blo 1642020 5923529 := bstep (se 2 (by rfl) ⟨2221323, by rfl⟩ : syracuseStep 5923529 = 4442647) B4442647
theorem B15794993 : Blo 1642020 15794993 := bstep (se 2 (by rfl) ⟨5923122, by rfl⟩ : syracuseStep 15794993 = 11846245) B11846245
theorem B14041907 : Blo 1642020 14041907 := bstep (se 1 (by rfl) ⟨10531430, by rfl⟩ : syracuseStep 14041907 = 21062861) B21062861
theorem B9356147 : Blo 1642020 9356147 := bstep (se 1 (by rfl) ⟨7017110, by rfl⟩ : syracuseStep 9356147 = 14034221) B14034221
theorem B6235015 : Blo 1642020 6235015 := bstep (se 1 (by rfl) ⟨4676261, by rfl⟩ : syracuseStep 6235015 = 9352523) B9352523
theorem B8315783 : Blo 1642020 8315783 := bstep (se 1 (by rfl) ⟨6236837, by rfl⟩ : syracuseStep 8315783 = 12473675) B12473675
theorem B3695507 : Blo 1642020 3695507 := bstep (se 1 (by rfl) ⟨2771630, by rfl⟩ : syracuseStep 3695507 = 5543261) B5543261
theorem B3695561 : Blo 1642020 3695561 := bstep (se 2 (by rfl) ⟨1385835, by rfl⟩ : syracuseStep 3695561 = 2771671) B2771671
theorem B9987095 : Blo 1642020 9987095 := bstep (se 1 (by rfl) ⟨7490321, by rfl⟩ : syracuseStep 9987095 = 14980643) B14980643
theorem B13329431 : Blo 1642020 13329431 := bstep (se 1 (by rfl) ⟨9997073, by rfl⟩ : syracuseStep 13329431 = 19994147) B19994147
theorem B5547095 : Blo 1642020 5547095 := bstep (se 1 (by rfl) ⟨4160321, by rfl⟩ : syracuseStep 5547095 = 8320643) B8320643
theorem B8881271 : Blo 1642020 8881271 := bstep (se 1 (by rfl) ⟨6660953, by rfl⟩ : syracuseStep 8881271 = 13321907) B13321907
theorem B1754299 : Blo 1642020 1754299 := bstep (se 1 (by rfl) ⟨1315724, by rfl⟩ : syracuseStep 1754299 = 2631449) B2631449
theorem B7898305 : Blo 1642020 7898305 := bstep (se 2 (by rfl) ⟨2961864, by rfl⟩ : syracuseStep 7898305 = 5923729) B5923729
theorem B3949825 : Blo 1642020 3949825 := bstep (se 2 (by rfl) ⟨1481184, by rfl⟩ : syracuseStep 3949825 = 2962369) B2962369
theorem B7898419 : Blo 1642020 7898419 := bstep (se 1 (by rfl) ⟨5923814, by rfl⟩ : syracuseStep 7898419 = 11847629) B11847629
theorem B3507641 : Blo 1642020 3507641 := bstep (se 2 (by rfl) ⟨1315365, by rfl⟩ : syracuseStep 3507641 = 2630731) B2630731
theorem B1754555 : Blo 1642020 1754555 := bstep (se 1 (by rfl) ⟨1315916, by rfl⟩ : syracuseStep 1754555 = 2631833) B2631833
theorem B4679201 : Blo 1642020 4679201 := bstep (se 2 (by rfl) ⟨1754700, by rfl⟩ : syracuseStep 4679201 = 3509401) B3509401
theorem B5547581 : Blo 1642020 5547581 := bstep (se 3 (by rfl) ⟨1040171, by rfl⟩ : syracuseStep 5547581 = 2080343) B2080343
theorem B3696263 : Blo 1642020 3696263 := bstep (se 1 (by rfl) ⟨2772197, by rfl⟩ : syracuseStep 3696263 = 5544395) B5544395
theorem B4679315 : Blo 1642020 4679315 := bstep (se 1 (by rfl) ⟨3509486, by rfl⟩ : syracuseStep 4679315 = 7018973) B7018973
theorem B17999617 : Blo 1642020 17999617 := bstep (se 2 (by rfl) ⟨6749856, by rfl⟩ : syracuseStep 17999617 = 13499713) B13499713
theorem B3696443 : Blo 1642020 3696443 := bstep (se 1 (by rfl) ⟨2772332, by rfl⟩ : syracuseStep 3696443 = 5544665) B5544665
theorem B14042969 : Blo 1642020 14042969 := bstep (se 2 (by rfl) ⟨5266113, by rfl⟩ : syracuseStep 14042969 = 10532227) B10532227
theorem B3508103 : Blo 1642020 3508103 := bstep (se 1 (by rfl) ⟨2631077, by rfl⟩ : syracuseStep 3508103 = 5262155) B5262155
theorem B3696569 : Blo 1642020 3696569 := bstep (se 2 (by rfl) ⟨1386213, by rfl⟩ : syracuseStep 3696569 = 2772427) B2772427
theorem B2771003 : Blo 1642020 2771003 := bstep (se 1 (by rfl) ⟨2078252, by rfl⟩ : syracuseStep 2771003 = 4156505) B4156505
theorem B5261399 : Blo 1642020 5261399 := bstep (se 1 (by rfl) ⟨3946049, by rfl⟩ : syracuseStep 5261399 = 7892099) B7892099
theorem B28067957 : Blo 1642020 28067957 := bstep (se 5 (by rfl) ⟨1315685, by rfl⟩ : syracuseStep 28067957 = 2631371) B2631371
theorem B3696911 : Blo 1642020 3696911 := bstep (se 1 (by rfl) ⟨2772683, by rfl⟩ : syracuseStep 3696911 = 5545367) B5545367
theorem B3696929 : Blo 1642020 3696929 := bstep (se 2 (by rfl) ⟨1386348, by rfl⟩ : syracuseStep 3696929 = 2772697) B2772697
theorem B9357605 : Blo 1642020 9357605 := bstep (se 4 (by rfl) ⟨877275, by rfl⟩ : syracuseStep 9357605 = 1754551) B1754551
theorem B14985607 : Blo 1642020 14985607 := bstep (se 1 (by rfl) ⟨11239205, by rfl⟩ : syracuseStep 14985607 = 22478411) B22478411
theorem B21055889 : Blo 1642020 21055889 := bstep (se 2 (by rfl) ⟨7895958, by rfl⟩ : syracuseStep 21055889 = 15791917) B15791917
theorem B4680089 : Blo 1642020 4680089 := bstep (se 2 (by rfl) ⟨1755033, by rfl⟩ : syracuseStep 4680089 = 3510067) B3510067
theorem B2771401 : Blo 1642020 2771401 := bstep (se 2 (by rfl) ⟨1039275, by rfl⟩ : syracuseStep 2771401 = 2078551) B2078551
theorem B3697271 : Blo 1642020 3697271 := bstep (se 1 (by rfl) ⟨2772953, by rfl⟩ : syracuseStep 3697271 = 5545907) B5545907
theorem B5262025 : Blo 1642020 5262025 := bstep (se 2 (by rfl) ⟨1973259, by rfl⟩ : syracuseStep 5262025 = 3946519) B3946519
theorem B3001033 : Blo 1642020 3001033 := bstep (se 2 (by rfl) ⟨1125387, by rfl⟩ : syracuseStep 3001033 = 2250775) B2250775
theorem B3001121 : Blo 1642020 3001121 := bstep (se 2 (by rfl) ⟨1125420, by rfl⟩ : syracuseStep 3001121 = 2250841) B2250841
theorem B3697451 : Blo 1642020 3697451 := bstep (se 1 (by rfl) ⟨2773088, by rfl⟩ : syracuseStep 3697451 = 5546177) B5546177
theorem B3509281 : Blo 1642020 3509281 := bstep (se 2 (by rfl) ⟨1315980, by rfl⟩ : syracuseStep 3509281 = 2631961) B2631961
theorem B4156535 : Blo 1642020 4156535 := bstep (se 1 (by rfl) ⟨3117401, by rfl⟩ : syracuseStep 4156535 = 6234803) B6234803
theorem B2772103 : Blo 1642020 2772103 := bstep (se 1 (by rfl) ⟨2079077, by rfl⟩ : syracuseStep 2772103 = 4158155) B4158155
theorem B2370703 : Blo 1642020 2370703 := bstep (se 1 (by rfl) ⟨1778027, by rfl⟩ : syracuseStep 2370703 = 3556055) B3556055
theorem B3697811 : Blo 1642020 3697811 := bstep (se 1 (by rfl) ⟨2773358, by rfl⟩ : syracuseStep 3697811 = 5546717) B5546717
theorem B35540117 : Blo 1642020 35540117 := bstep (se 6 (by rfl) ⟨832971, by rfl⟩ : syracuseStep 35540117 = 1665943) B1665943
theorem B9358537 : Blo 1642020 9358537 := bstep (se 2 (by rfl) ⟨3509451, by rfl⟩ : syracuseStep 9358537 = 7018903) B7018903
theorem B3697865 : Blo 1642020 3697865 := bstep (se 2 (by rfl) ⟨1386699, by rfl⟩ : syracuseStep 3697865 = 2773399) B2773399
theorem B1642043 : Blo 1642020 1642043 := bstep (se 1 (by rfl) ⟨1231532, by rfl⟩ : syracuseStep 1642043 = 2463065) B2463065
theorem B19975747 : Blo 1642020 19975747 := bstep (se 1 (by rfl) ⟨14981810, by rfl⟩ : syracuseStep 19975747 = 29963621) B29963621
theorem B18009701 : Blo 1642020 18009701 := bstep (se 4 (by rfl) ⟨1688409, by rfl⟩ : syracuseStep 18009701 = 3376819) B3376819
theorem B1642119 : Blo 1642020 1642119 := bstep (se 1 (by rfl) ⟨1231589, by rfl⟩ : syracuseStep 1642119 = 2463179) B2463179
theorem B1642127 : Blo 1642020 1642127 := bstep (se 1 (by rfl) ⟨1231595, by rfl⟩ : syracuseStep 1642127 = 2463191) B2463191
theorem B1642171 : Blo 1642020 1642171 := bstep (se 1 (by rfl) ⟨1231628, by rfl⟩ : syracuseStep 1642171 = 2463257) B2463257
theorem B1642247 : Blo 1642020 1642247 := bstep (se 1 (by rfl) ⟨1231685, by rfl⟩ : syracuseStep 1642247 = 2463371) B2463371
theorem B1642255 : Blo 1642020 1642255 := bstep (se 1 (by rfl) ⟨1231691, by rfl⟩ : syracuseStep 1642255 = 2463383) B2463383
theorem B2772751 : Blo 1642020 2772751 := bstep (se 1 (by rfl) ⟨2079563, by rfl⟩ : syracuseStep 2772751 = 4159127) B4159127
theorem B7114511 : Blo 1642020 7114511 := bstep (se 1 (by rfl) ⟨5335883, by rfl⟩ : syracuseStep 7114511 = 10671767) B10671767
theorem B10530611 : Blo 1642020 10530611 := bstep (se 1 (by rfl) ⟨7897958, by rfl⟩ : syracuseStep 10530611 = 15795917) B15795917
theorem B1642299 : Blo 1642020 1642299 := bstep (se 1 (by rfl) ⟨1231724, by rfl⟩ : syracuseStep 1642299 = 2463449) B2463449
theorem B1642375 : Blo 1642020 1642375 := bstep (se 1 (by rfl) ⟨1231781, by rfl⟩ : syracuseStep 1642375 = 2463563) B2463563
theorem B3698567 : Blo 1642020 3698567 := bstep (se 1 (by rfl) ⟨2773925, by rfl⟩ : syracuseStep 3698567 = 5547851) B5547851
theorem B1642383 : Blo 1642020 1642383 := bstep (se 1 (by rfl) ⟨1231787, by rfl⟩ : syracuseStep 1642383 = 2463575) B2463575
theorem B12472217 : Blo 1642020 12472217 := bstep (se 2 (by rfl) ⟨4677081, by rfl⟩ : syracuseStep 12472217 = 9354163) B9354163
theorem B1642427 : Blo 1642020 1642427 := bstep (se 1 (by rfl) ⟨1231820, by rfl⟩ : syracuseStep 1642427 = 2463641) B2463641
theorem B1642503 : Blo 1642020 1642503 := bstep (se 1 (by rfl) ⟨1231877, by rfl⟩ : syracuseStep 1642503 = 2463755) B2463755
theorem B1642511 : Blo 1642020 1642511 := bstep (se 1 (by rfl) ⟨1231883, by rfl⟩ : syracuseStep 1642511 = 2463767) B2463767
theorem B109555733 : Blo 1642020 109555733 := bstep (se 6 (by rfl) ⟨2567712, by rfl⟩ : syracuseStep 109555733 = 5135425) B5135425
theorem B1642555 : Blo 1642020 1642555 := bstep (se 1 (by rfl) ⟨1231916, by rfl⟩ : syracuseStep 1642555 = 2463833) B2463833
theorem B3698747 : Blo 1642020 3698747 := bstep (se 1 (by rfl) ⟨2774060, by rfl⟩ : syracuseStep 3698747 = 5548121) B5548121
theorem B4157527 : Blo 1642020 4157527 := bstep (se 1 (by rfl) ⟨3118145, by rfl⟩ : syracuseStep 4157527 = 6236291) B6236291
theorem B1642631 : Blo 1642020 1642631 := bstep (se 1 (by rfl) ⟨1231973, by rfl⟩ : syracuseStep 1642631 = 2463947) B2463947
theorem B2338951 : Blo 1642020 2338951 := bstep (se 1 (by rfl) ⟨1754213, by rfl⟩ : syracuseStep 2338951 = 3508427) B3508427
theorem B1642639 : Blo 1642020 1642639 := bstep (se 1 (by rfl) ⟨1231979, by rfl⟩ : syracuseStep 1642639 = 2463959) B2463959
theorem B3698873 : Blo 1642020 3698873 := bstep (se 2 (by rfl) ⟨1387077, by rfl⟩ : syracuseStep 3698873 = 2774155) B2774155
theorem B1642683 : Blo 1642020 1642683 := bstep (se 1 (by rfl) ⟨1232012, by rfl⟩ : syracuseStep 1642683 = 2464025) B2464025
theorem B1642759 : Blo 1642020 1642759 := bstep (se 1 (by rfl) ⟨1232069, by rfl⟩ : syracuseStep 1642759 = 2464139) B2464139
theorem B1642767 : Blo 1642020 1642767 := bstep (se 1 (by rfl) ⟨1232075, by rfl⟩ : syracuseStep 1642767 = 2464151) B2464151
theorem B2773291 : Blo 1642020 2773291 := bstep (se 1 (by rfl) ⟨2079968, by rfl⟩ : syracuseStep 2773291 = 4159937) B4159937
theorem B1642811 : Blo 1642020 1642811 := bstep (se 1 (by rfl) ⟨1232108, by rfl⟩ : syracuseStep 1642811 = 2464217) B2464217
theorem B8319347 : Blo 1642020 8319347 := bstep (se 1 (by rfl) ⟨6239510, by rfl⟩ : syracuseStep 8319347 = 12479021) B12479021
theorem B4157831 : Blo 1642020 4157831 := bstep (se 1 (by rfl) ⟨3118373, by rfl⟩ : syracuseStep 4157831 = 6236747) B6236747
theorem B1642887 : Blo 1642020 1642887 := bstep (se 1 (by rfl) ⟨1232165, by rfl⟩ : syracuseStep 1642887 = 2464331) B2464331
theorem B1847695 : Blo 1642020 1847695 := bstep (se 1 (by rfl) ⟨1385771, by rfl⟩ : syracuseStep 1847695 = 2771543) B2771543
theorem B1642895 : Blo 1642020 1642895 := bstep (se 1 (by rfl) ⟨1232171, by rfl⟩ : syracuseStep 1642895 = 2464343) B2464343
theorem B2773433 : Blo 1642020 2773433 := bstep (se 2 (by rfl) ⟨1040037, by rfl⟩ : syracuseStep 2773433 = 2080075) B2080075
theorem B1642939 : Blo 1642020 1642939 := bstep (se 1 (by rfl) ⟨1232204, by rfl⟩ : syracuseStep 1642939 = 2464409) B2464409
theorem B1643015 : Blo 1642020 1643015 := bstep (se 1 (by rfl) ⟨1232261, by rfl⟩ : syracuseStep 1643015 = 2464523) B2464523
theorem B4157963 : Blo 1642020 4157963 := bstep (se 1 (by rfl) ⟨3118472, by rfl⟩ : syracuseStep 4157963 = 6236945) B6236945
theorem B1643023 : Blo 1642020 1643023 := bstep (se 1 (by rfl) ⟨1232267, by rfl⟩ : syracuseStep 1643023 = 2464535) B2464535
theorem B14037533 : Blo 1642020 14037533 := bstep (se 3 (by rfl) ⟨2632037, by rfl⟩ : syracuseStep 14037533 = 5264075) B5264075
theorem B1643067 : Blo 1642020 1643067 := bstep (se 1 (by rfl) ⟨1232300, by rfl⟩ : syracuseStep 1643067 = 2464601) B2464601
theorem B1643143 : Blo 1642020 1643143 := bstep (se 1 (by rfl) ⟨1232357, by rfl⟩ : syracuseStep 1643143 = 2464715) B2464715
theorem B1643151 : Blo 1642020 1643151 := bstep (se 1 (by rfl) ⟨1232363, by rfl⟩ : syracuseStep 1643151 = 2464727) B2464727
theorem B1643195 : Blo 1642020 1643195 := bstep (se 1 (by rfl) ⟨1232396, by rfl⟩ : syracuseStep 1643195 = 2464793) B2464793
theorem B19985089 : Blo 1642020 19985089 := bstep (se 2 (by rfl) ⟨7494408, by rfl⟩ : syracuseStep 19985089 = 14988817) B14988817
theorem B7492297 : Blo 1642020 7492297 := bstep (se 2 (by rfl) ⟨2809611, by rfl⟩ : syracuseStep 7492297 = 5619223) B5619223
theorem B4993793 : Blo 1642020 4993793 := bstep (se 2 (by rfl) ⟨1872672, by rfl⟩ : syracuseStep 4993793 = 3745345) B3745345
theorem B1643271 : Blo 1642020 1643271 := bstep (se 1 (by rfl) ⟨1232453, by rfl⟩ : syracuseStep 1643271 = 2464907) B2464907
theorem B1643279 : Blo 1642020 1643279 := bstep (se 1 (by rfl) ⟨1232459, by rfl⟩ : syracuseStep 1643279 = 2464919) B2464919
theorem B18723635 : Blo 1642020 18723635 := bstep (se 1 (by rfl) ⟨14042726, by rfl⟩ : syracuseStep 18723635 = 28085453) B28085453
theorem B1643323 : Blo 1642020 1643323 := bstep (se 1 (by rfl) ⟨1232492, by rfl⟩ : syracuseStep 1643323 = 2464985) B2464985
theorem B8319833 : Blo 1642020 8319833 := bstep (se 2 (by rfl) ⟨3119937, by rfl⟩ : syracuseStep 8319833 = 6239875) B6239875
theorem B1848199 : Blo 1642020 1848199 := bstep (se 1 (by rfl) ⟨1386149, by rfl⟩ : syracuseStep 1848199 = 2772299) B2772299
theorem B1643399 : Blo 1642020 1643399 := bstep (se 1 (by rfl) ⟨1232549, by rfl⟩ : syracuseStep 1643399 = 2465099) B2465099
theorem B1643407 : Blo 1642020 1643407 := bstep (se 1 (by rfl) ⟨1232555, by rfl⟩ : syracuseStep 1643407 = 2465111) B2465111
theorem B3118009 : Blo 1642020 3118009 := bstep (se 2 (by rfl) ⟨1169253, by rfl⟩ : syracuseStep 3118009 = 2338507) B2338507
theorem B2339771 : Blo 1642020 2339771 := bstep (se 1 (by rfl) ⟨1754828, by rfl⟩ : syracuseStep 2339771 = 3509657) B3509657
theorem B1643451 : Blo 1642020 1643451 := bstep (se 1 (by rfl) ⟨1232588, by rfl⟩ : syracuseStep 1643451 = 2465177) B2465177
theorem B1643527 : Blo 1642020 1643527 := bstep (se 1 (by rfl) ⟨1232645, by rfl⟩ : syracuseStep 1643527 = 2465291) B2465291
theorem B4158479 : Blo 1642020 4158479 := bstep (se 1 (by rfl) ⟨3118859, by rfl⟩ : syracuseStep 4158479 = 6237719) B6237719
theorem B1643535 : Blo 1642020 1643535 := bstep (se 1 (by rfl) ⟨1232651, by rfl⟩ : syracuseStep 1643535 = 2465303) B2465303
theorem B14029847 : Blo 1642020 14029847 := bstep (se 1 (by rfl) ⟨10522385, by rfl⟩ : syracuseStep 14029847 = 21044771) B21044771
theorem B17773613 : Blo 1642020 17773613 := bstep (se 3 (by rfl) ⟨3332552, by rfl⟩ : syracuseStep 17773613 = 6665105) B6665105
theorem B1848379 : Blo 1642020 1848379 := bstep (se 1 (by rfl) ⟨1386284, by rfl⟩ : syracuseStep 1848379 = 2772569) B2772569
theorem B1643579 : Blo 1642020 1643579 := bstep (se 1 (by rfl) ⟨1232684, by rfl⟩ : syracuseStep 1643579 = 2465369) B2465369
theorem B2774135 : Blo 1642020 2774135 := bstep (se 1 (by rfl) ⟨2080601, by rfl⟩ : syracuseStep 2774135 = 4161203) B4161203
theorem B1643655 : Blo 1642020 1643655 := bstep (se 1 (by rfl) ⟨1232741, by rfl⟩ : syracuseStep 1643655 = 2465483) B2465483
theorem B1643663 : Blo 1642020 1643663 := bstep (se 1 (by rfl) ⟨1232747, by rfl⟩ : syracuseStep 1643663 = 2465495) B2465495
theorem B4158611 : Blo 1642020 4158611 := bstep (se 1 (by rfl) ⟨3118958, by rfl⟩ : syracuseStep 4158611 = 6237917) B6237917
theorem B1643707 : Blo 1642020 1643707 := bstep (se 1 (by rfl) ⟨1232780, by rfl⟩ : syracuseStep 1643707 = 2465561) B2465561
theorem B3945673 : Blo 1642020 3945673 := bstep (se 2 (by rfl) ⟨1479627, by rfl⟩ : syracuseStep 3945673 = 2959255) B2959255
theorem B7017673 : Blo 1642020 7017673 := bstep (se 2 (by rfl) ⟨2631627, by rfl⟩ : syracuseStep 7017673 = 5263255) B5263255
theorem B14038217 : Blo 1642020 14038217 := bstep (se 2 (by rfl) ⟨5264331, by rfl⟩ : syracuseStep 14038217 = 10528663) B10528663
theorem B1643783 : Blo 1642020 1643783 := bstep (se 1 (by rfl) ⟨1232837, by rfl⟩ : syracuseStep 1643783 = 2465675) B2465675
theorem B3118351 : Blo 1642020 3118351 := bstep (se 1 (by rfl) ⟨2338763, by rfl⟩ : syracuseStep 3118351 = 4677527) B4677527
theorem B1643791 : Blo 1642020 1643791 := bstep (se 1 (by rfl) ⟨1232843, by rfl⟩ : syracuseStep 1643791 = 2465687) B2465687
theorem B2463035 : Blo 1642020 2463035 := bstep (se 1 (by rfl) ⟨1847276, by rfl⟩ : syracuseStep 2463035 = 3694553) B3694553
theorem B1643835 : Blo 1642020 1643835 := bstep (se 1 (by rfl) ⟨1232876, by rfl⟩ : syracuseStep 1643835 = 2465753) B2465753
theorem B2463095 : Blo 1642020 2463095 := bstep (se 1 (by rfl) ⟨1847321, by rfl⟩ : syracuseStep 2463095 = 3694643) B3694643
theorem B17773955 : Blo 1642020 17773955 := bstep (se 1 (by rfl) ⟨13330466, by rfl⟩ : syracuseStep 17773955 = 26660933) B26660933
theorem B1643911 : Blo 1642020 1643911 := bstep (se 1 (by rfl) ⟨1232933, by rfl⟩ : syracuseStep 1643911 = 2465867) B2465867
theorem B2463119 : Blo 1642020 2463119 := bstep (se 1 (by rfl) ⟨1847339, by rfl⟩ : syracuseStep 2463119 = 3694679) B3694679
theorem B1643919 : Blo 1642020 1643919 := bstep (se 1 (by rfl) ⟨1232939, by rfl⟩ : syracuseStep 1643919 = 2465879) B2465879
theorem B12481937 : Blo 1642020 12481937 := bstep (se 2 (by rfl) ⟨4680726, by rfl⟩ : syracuseStep 12481937 = 9361453) B9361453
theorem B5543315 : Blo 1642020 5543315 := bstep (se 1 (by rfl) ⟨4157486, by rfl⟩ : syracuseStep 5543315 = 8314973) B8314973
theorem B2463161 : Blo 1642020 2463161 := bstep (se 2 (by rfl) ⟨923685, by rfl⟩ : syracuseStep 2463161 = 1847371) B1847371
theorem B1643963 : Blo 1642020 1643963 := bstep (se 1 (by rfl) ⟨1232972, by rfl⟩ : syracuseStep 1643963 = 2465945) B2465945
theorem B2463239 : Blo 1642020 2463239 := bstep (se 1 (by rfl) ⟨1847429, by rfl⟩ : syracuseStep 2463239 = 3694859) B3694859
theorem B1848847 : Blo 1642020 1848847 := bstep (se 1 (by rfl) ⟨1386635, by rfl⟩ : syracuseStep 1848847 = 2773271) B2773271
theorem B50615837 : Blo 1642020 50615837 := bstep (se 3 (by rfl) ⟨9490469, by rfl⟩ : syracuseStep 50615837 = 18980939) B18980939
theorem B2463275 : Blo 1642020 2463275 := bstep (se 1 (by rfl) ⟨1847456, by rfl⟩ : syracuseStep 2463275 = 3694913) B3694913
theorem B2340409 : Blo 1642020 2340409 := bstep (se 2 (by rfl) ⟨877653, by rfl⟩ : syracuseStep 2340409 = 1755307) B1755307
theorem B14038595 : Blo 1642020 14038595 := bstep (se 1 (by rfl) ⟨10528946, by rfl⟩ : syracuseStep 14038595 = 21057893) B21057893
theorem B9008707 : Blo 1642020 9008707 := bstep (se 1 (by rfl) ⟨6756530, by rfl⟩ : syracuseStep 9008707 = 13513061) B13513061
theorem B2463305 : Blo 1642020 2463305 := bstep (se 2 (by rfl) ⟨923739, by rfl⟩ : syracuseStep 2463305 = 1847479) B1847479
theorem B2741879 : Blo 1642020 2741879 := bstep (se 1 (by rfl) ⟨2056409, by rfl⟩ : syracuseStep 2741879 = 4112819) B4112819
theorem B2340523 : Blo 1642020 2340523 := bstep (se 1 (by rfl) ⟨1755392, by rfl⟩ : syracuseStep 2340523 = 3510785) B3510785
theorem B2463419 : Blo 1642020 2463419 := bstep (se 1 (by rfl) ⟨1847564, by rfl⟩ : syracuseStep 2463419 = 3695129) B3695129
theorem B2078455 : Blo 1642020 2078455 := bstep (se 1 (by rfl) ⟨1558841, by rfl⟩ : syracuseStep 2078455 = 3117683) B3117683
theorem B2463479 : Blo 1642020 2463479 := bstep (se 1 (by rfl) ⟨1847609, by rfl⟩ : syracuseStep 2463479 = 3695219) B3695219
theorem B17757953 : Blo 1642020 17757953 := bstep (se 2 (by rfl) ⟨6659232, by rfl⟩ : syracuseStep 17757953 = 13318465) B13318465
theorem B2463503 : Blo 1642020 2463503 := bstep (se 1 (by rfl) ⟨1847627, by rfl⟩ : syracuseStep 2463503 = 3695255) B3695255
theorem B13686565 : Blo 1642020 13686565 := bstep (se 4 (by rfl) ⟨1283115, by rfl⟩ : syracuseStep 13686565 = 2566231) B2566231
theorem B12474161 : Blo 1642020 12474161 := bstep (se 2 (by rfl) ⟨4677810, by rfl⟩ : syracuseStep 12474161 = 9355621) B9355621
theorem B2463545 : Blo 1642020 2463545 := bstep (se 2 (by rfl) ⟨923829, by rfl⟩ : syracuseStep 2463545 = 1847659) B1847659
theorem B2463623 : Blo 1642020 2463623 := bstep (se 1 (by rfl) ⟨1847717, by rfl⟩ : syracuseStep 2463623 = 3695435) B3695435
theorem B2340751 : Blo 1642020 2340751 := bstep (se 1 (by rfl) ⟨1755563, by rfl⟩ : syracuseStep 2340751 = 3511127) B3511127
theorem B2463659 : Blo 1642020 2463659 := bstep (se 1 (by rfl) ⟨1847744, by rfl⟩ : syracuseStep 2463659 = 3695489) B3695489
theorem B2463689 : Blo 1642020 2463689 := bstep (se 2 (by rfl) ⟨923883, by rfl⟩ : syracuseStep 2463689 = 1847767) B1847767
theorem B1849351 : Blo 1642020 1849351 := bstep (se 1 (by rfl) ⟨1387013, by rfl⟩ : syracuseStep 1849351 = 2774027) B2774027
theorem B86751245 : Blo 1642020 86751245 := bstep (se 3 (by rfl) ⟨16265858, by rfl⟩ : syracuseStep 86751245 = 32531717) B32531717
theorem B2078779 : Blo 1642020 2078779 := bstep (se 1 (by rfl) ⟨1559084, by rfl⟩ : syracuseStep 2078779 = 3118169) B3118169
theorem B2463803 : Blo 1642020 2463803 := bstep (se 1 (by rfl) ⟨1847852, by rfl⟩ : syracuseStep 2463803 = 3695705) B3695705
theorem B2463863 : Blo 1642020 2463863 := bstep (se 1 (by rfl) ⟨1847897, by rfl⟩ : syracuseStep 2463863 = 3695795) B3695795
theorem B3119239 : Blo 1642020 3119239 := bstep (se 1 (by rfl) ⟨2339429, by rfl⟩ : syracuseStep 3119239 = 4678859) B4678859
theorem B2463887 : Blo 1642020 2463887 := bstep (se 1 (by rfl) ⟨1847915, by rfl⟩ : syracuseStep 2463887 = 3695831) B3695831
theorem B2463929 : Blo 1642020 2463929 := bstep (se 2 (by rfl) ⟨923973, by rfl⟩ : syracuseStep 2463929 = 1847947) B1847947
theorem B4159745 : Blo 1642020 4159745 := bstep (se 2 (by rfl) ⟨1559904, by rfl⟩ : syracuseStep 4159745 = 3119809) B3119809
theorem B2464007 : Blo 1642020 2464007 := bstep (se 1 (by rfl) ⟨1848005, by rfl⟩ : syracuseStep 2464007 = 3696011) B3696011
theorem B2464043 : Blo 1642020 2464043 := bstep (se 1 (by rfl) ⟨1848032, by rfl⟩ : syracuseStep 2464043 = 3696065) B3696065
theorem B2464073 : Blo 1642020 2464073 := bstep (se 2 (by rfl) ⟨924027, by rfl⟩ : syracuseStep 2464073 = 1848055) B1848055
theorem B6240665 : Blo 1642020 6240665 := bstep (se 2 (by rfl) ⟨2340249, by rfl⟩ : syracuseStep 6240665 = 4680499) B4680499
theorem B2464187 : Blo 1642020 2464187 := bstep (se 1 (by rfl) ⟨1848140, by rfl⟩ : syracuseStep 2464187 = 3696281) B3696281
theorem B2464247 : Blo 1642020 2464247 := bstep (se 1 (by rfl) ⟨1848185, by rfl⟩ : syracuseStep 2464247 = 3696371) B3696371
theorem B16865795 : Blo 1642020 16865795 := bstep (se 1 (by rfl) ⟨12649346, by rfl⟩ : syracuseStep 16865795 = 25298693) B25298693
theorem B2464271 : Blo 1642020 2464271 := bstep (se 1 (by rfl) ⟨1848203, by rfl⟩ : syracuseStep 2464271 = 3696407) B3696407
theorem B4676125 : Blo 1642020 4676125 := bstep (se 3 (by rfl) ⟨876773, by rfl⟩ : syracuseStep 4676125 = 1753547) B1753547
theorem B2464313 : Blo 1642020 2464313 := bstep (se 2 (by rfl) ⟨924117, by rfl⟩ : syracuseStep 2464313 = 1848235) B1848235
theorem B7019075 : Blo 1642020 7019075 := bstep (se 1 (by rfl) ⟨5264306, by rfl⟩ : syracuseStep 7019075 = 10528613) B10528613
theorem B4160119 : Blo 1642020 4160119 := bstep (se 1 (by rfl) ⟨3120089, by rfl⟩ : syracuseStep 4160119 = 6240179) B6240179
theorem B2464391 : Blo 1642020 2464391 := bstep (se 1 (by rfl) ⟨1848293, by rfl⟩ : syracuseStep 2464391 = 3696587) B3696587
theorem B2464427 : Blo 1642020 2464427 := bstep (se 1 (by rfl) ⟨1848320, by rfl⟩ : syracuseStep 2464427 = 3696641) B3696641
theorem B11246273 : Blo 1642020 11246273 := bstep (se 2 (by rfl) ⟨4217352, by rfl⟩ : syracuseStep 11246273 = 8434705) B8434705
theorem B2464457 : Blo 1642020 2464457 := bstep (se 2 (by rfl) ⟨924171, by rfl⟩ : syracuseStep 2464457 = 1848343) B1848343
theorem B7895789 : Blo 1642020 7895789 := bstep (se 3 (by rfl) ⟨1480460, by rfl⟩ : syracuseStep 7895789 = 2960921) B2960921
theorem B9124609 : Blo 1642020 9124609 := bstep (se 2 (by rfl) ⟨3421728, by rfl⟩ : syracuseStep 9124609 = 6843457) B6843457
theorem B5544719 : Blo 1642020 5544719 := bstep (se 1 (by rfl) ⟨4158539, by rfl⟩ : syracuseStep 5544719 = 8317079) B8317079
theorem B2464571 : Blo 1642020 2464571 := bstep (se 1 (by rfl) ⟨1848428, by rfl⟩ : syracuseStep 2464571 = 3696857) B3696857
theorem B5061437 : Blo 1642020 5061437 := bstep (se 3 (by rfl) ⟨949019, by rfl⟩ : syracuseStep 5061437 = 1898039) B1898039
theorem B4676467 : Blo 1642020 4676467 := bstep (se 1 (by rfl) ⟨3507350, by rfl⟩ : syracuseStep 4676467 = 7014701) B7014701
theorem B4742003 : Blo 1642020 4742003 := bstep (se 1 (by rfl) ⟨3556502, by rfl⟩ : syracuseStep 4742003 = 7113005) B7113005
theorem B2464631 : Blo 1642020 2464631 := bstep (se 1 (by rfl) ⟨1848473, by rfl⟩ : syracuseStep 2464631 = 3696947) B3696947
theorem B2464655 : Blo 1642020 2464655 := bstep (se 1 (by rfl) ⟨1848491, by rfl⟩ : syracuseStep 2464655 = 3696983) B3696983
theorem B8321939 : Blo 1642020 8321939 := bstep (se 1 (by rfl) ⟨6241454, by rfl⟩ : syracuseStep 8321939 = 12482909) B12482909
theorem B2464697 : Blo 1642020 2464697 := bstep (se 2 (by rfl) ⟨924261, by rfl⟩ : syracuseStep 2464697 = 1848523) B1848523
theorem B1973255 : Blo 1642020 1973255 := bstep (se 1 (by rfl) ⟨1479941, by rfl⟩ : syracuseStep 1973255 = 2959883) B2959883
theorem B2464775 : Blo 1642020 2464775 := bstep (se 1 (by rfl) ⟨1848581, by rfl⟩ : syracuseStep 2464775 = 3697163) B3697163
theorem B2079751 : Blo 1642020 2079751 := bstep (se 1 (by rfl) ⟨1559813, by rfl⟩ : syracuseStep 2079751 = 3119627) B3119627
theorem B5544989 : Blo 1642020 5544989 := bstep (se 3 (by rfl) ⟨1039685, by rfl⟩ : syracuseStep 5544989 = 2079371) B2079371
theorem B2464811 : Blo 1642020 2464811 := bstep (se 1 (by rfl) ⟨1848608, by rfl⟩ : syracuseStep 2464811 = 3697217) B3697217
theorem B4160555 : Blo 1642020 4160555 := bstep (se 1 (by rfl) ⟨3120416, by rfl⟩ : syracuseStep 4160555 = 6240833) B6240833
theorem B2464841 : Blo 1642020 2464841 := bstep (se 2 (by rfl) ⟨924315, by rfl⟩ : syracuseStep 2464841 = 1848631) B1848631
theorem B3161207 : Blo 1642020 3161207 := bstep (se 1 (by rfl) ⟨2370905, by rfl⟩ : syracuseStep 3161207 = 4741811) B4741811
theorem B63143063 : Blo 1642020 63143063 := bstep (se 1 (by rfl) ⟨47357297, by rfl⟩ : syracuseStep 63143063 = 94714595) B94714595
theorem B2464955 : Blo 1642020 2464955 := bstep (se 1 (by rfl) ⟨1848716, by rfl⟩ : syracuseStep 2464955 = 3697433) B3697433
theorem B2465015 : Blo 1642020 2465015 := bstep (se 1 (by rfl) ⟨1848761, by rfl⟩ : syracuseStep 2465015 = 3697523) B3697523
theorem B2465039 : Blo 1642020 2465039 := bstep (se 1 (by rfl) ⟨1848779, by rfl⟩ : syracuseStep 2465039 = 3697559) B3697559
theorem B8314163 : Blo 1642020 8314163 := bstep (se 1 (by rfl) ⟨6235622, by rfl⟩ : syracuseStep 8314163 = 12471245) B12471245
theorem B2465081 : Blo 1642020 2465081 := bstep (se 2 (by rfl) ⟨924405, by rfl⟩ : syracuseStep 2465081 = 1848811) B1848811
theorem B2465159 : Blo 1642020 2465159 := bstep (se 1 (by rfl) ⟨1848869, by rfl⟩ : syracuseStep 2465159 = 3697739) B3697739
theorem B2465195 : Blo 1642020 2465195 := bstep (se 1 (by rfl) ⟨1848896, by rfl⟩ : syracuseStep 2465195 = 3697793) B3697793
theorem B2080171 : Blo 1642020 2080171 := bstep (se 1 (by rfl) ⟨1560128, by rfl⟩ : syracuseStep 2080171 = 3120257) B3120257
theorem B2465225 : Blo 1642020 2465225 := bstep (se 2 (by rfl) ⟨924459, by rfl⟩ : syracuseStep 2465225 = 1848919) B1848919
theorem B3161659 : Blo 1642020 3161659 := bstep (se 1 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 3161659 = 4742489) B4742489
theorem B2465339 : Blo 1642020 2465339 := bstep (se 1 (by rfl) ⟨1849004, by rfl⟩ : syracuseStep 2465339 = 3698009) B3698009
theorem B17997389 : Blo 1642020 17997389 := bstep (se 3 (by rfl) ⟨3374510, by rfl⟩ : syracuseStep 17997389 = 6749021) B6749021
theorem B8314487 : Blo 1642020 8314487 := bstep (se 1 (by rfl) ⟨6235865, by rfl⟩ : syracuseStep 8314487 = 12471731) B12471731
theorem B2465399 : Blo 1642020 2465399 := bstep (se 1 (by rfl) ⟨1849049, by rfl⟩ : syracuseStep 2465399 = 3698099) B3698099
theorem B2465423 : Blo 1642020 2465423 := bstep (se 1 (by rfl) ⟨1849067, by rfl⟩ : syracuseStep 2465423 = 3698135) B3698135
theorem B2080399 : Blo 1642020 2080399 := bstep (se 1 (by rfl) ⟨1560299, by rfl⟩ : syracuseStep 2080399 = 3120599) B3120599
theorem B2465465 : Blo 1642020 2465465 := bstep (se 2 (by rfl) ⟨924549, by rfl⟩ : syracuseStep 2465465 = 1849099) B1849099
theorem B10665665 : Blo 1642020 10665665 := bstep (se 2 (by rfl) ⟨3999624, by rfl⟩ : syracuseStep 10665665 = 7999249) B7999249
theorem B2465543 : Blo 1642020 2465543 := bstep (se 1 (by rfl) ⟨1849157, by rfl⟩ : syracuseStep 2465543 = 3698315) B3698315
theorem B2465579 : Blo 1642020 2465579 := bstep (se 1 (by rfl) ⟨1849184, by rfl⟩ : syracuseStep 2465579 = 3698369) B3698369
theorem B2465609 : Blo 1642020 2465609 := bstep (se 2 (by rfl) ⟨924603, by rfl⟩ : syracuseStep 2465609 = 1849207) B1849207
theorem B4161395 : Blo 1642020 4161395 := bstep (se 1 (by rfl) ⟨3121046, by rfl⟩ : syracuseStep 4161395 = 6242093) B6242093
theorem B3121031 : Blo 1642020 3121031 := bstep (se 1 (by rfl) ⟨2340773, by rfl⟩ : syracuseStep 3121031 = 4681547) B4681547
theorem B4161415 : Blo 1642020 4161415 := bstep (se 1 (by rfl) ⟨3121061, by rfl⟩ : syracuseStep 4161415 = 6242123) B6242123
theorem B2465723 : Blo 1642020 2465723 := bstep (se 1 (by rfl) ⟨1849292, by rfl⟩ : syracuseStep 2465723 = 3698585) B3698585
theorem B2465783 : Blo 1642020 2465783 := bstep (se 1 (by rfl) ⟨1849337, by rfl⟩ : syracuseStep 2465783 = 3698675) B3698675
theorem B2465801 : Blo 1642020 2465801 := bstep (se 2 (by rfl) ⟨924675, by rfl⟩ : syracuseStep 2465801 = 1849351) B1849351
theorem B2465831 : Blo 1642020 2465831 := bstep (se 1 (by rfl) ⟨1849373, by rfl⟩ : syracuseStep 2465831 = 3698747) B3698747
theorem B26632253 : Blo 1642020 26632253 := bstep (se 3 (by rfl) ⟨4993547, by rfl⟩ : syracuseStep 26632253 = 9987095) B9987095
theorem B2465915 : Blo 1642020 2465915 := bstep (se 1 (by rfl) ⟨1849436, by rfl⟩ : syracuseStep 2465915 = 3698873) B3698873
theorem B5546231 : Blo 1642020 5546231 := bstep (se 1 (by rfl) ⟨4159673, by rfl⟩ : syracuseStep 5546231 = 8319347) B8319347
theorem B3949019 : Blo 1642020 3949019 := bstep (se 1 (by rfl) ⟨2961764, by rfl⟩ : syracuseStep 3949019 = 5923529) B5923529
theorem B19980809 : Blo 1642020 19980809 := bstep (se 2 (by rfl) ⟨7492803, by rfl⟩ : syracuseStep 19980809 = 14985607) B14985607
theorem B5546555 : Blo 1642020 5546555 := bstep (se 1 (by rfl) ⟨4159916, by rfl⟩ : syracuseStep 5546555 = 8319833) B8319833
theorem B3695201 : Blo 1642020 3695201 := bstep (se 2 (by rfl) ⟨1385700, by rfl⟩ : syracuseStep 3695201 = 2771401) B2771401
theorem B6234833 : Blo 1642020 6234833 := bstep (se 2 (by rfl) ⟨2338062, by rfl⟩ : syracuseStep 6234833 = 4676125) B4676125
theorem B5546825 : Blo 1642020 5546825 := bstep (se 2 (by rfl) ⟨2080059, by rfl⟩ : syracuseStep 5546825 = 4160119) B4160119
theorem B3695543 : Blo 1642020 3695543 := bstep (se 1 (by rfl) ⟨2771657, by rfl⟩ : syracuseStep 3695543 = 5543315) B5543315
theorem B12166145 : Blo 1642020 12166145 := bstep (se 2 (by rfl) ⟨4562304, by rfl⟩ : syracuseStep 12166145 = 9124609) B9124609
theorem B33743891 : Blo 1642020 33743891 := bstep (se 1 (by rfl) ⟨25307918, by rfl⟩ : syracuseStep 33743891 = 50615837) B50615837
theorem B1827919 : Blo 1642020 1827919 := bstep (se 1 (by rfl) ⟨1370939, by rfl⟩ : syracuseStep 1827919 = 2741879) B2741879
theorem B6235289 : Blo 1642020 6235289 := bstep (se 2 (by rfl) ⟨2338233, by rfl⟩ : syracuseStep 6235289 = 4676467) B4676467
theorem B4678813 : Blo 1642020 4678813 := bstep (se 3 (by rfl) ⟨877277, by rfl⟩ : syracuseStep 4678813 = 1754555) B1754555
theorem B11838635 : Blo 1642020 11838635 := bstep (se 1 (by rfl) ⟨8878976, by rfl⟩ : syracuseStep 11838635 = 17757953) B17757953
theorem B8316107 : Blo 1642020 8316107 := bstep (se 1 (by rfl) ⟨6237080, by rfl⟩ : syracuseStep 8316107 = 12474161) B12474161
theorem B4679041 : Blo 1642020 4679041 := bstep (se 2 (by rfl) ⟨1754640, by rfl⟩ : syracuseStep 4679041 = 3509281) B3509281
theorem B3507599 : Blo 1642020 3507599 := bstep (se 1 (by rfl) ⟨2630699, by rfl⟩ : syracuseStep 3507599 = 5261399) B5261399
theorem B18711971 : Blo 1642020 18711971 := bstep (se 1 (by rfl) ⟨14033978, by rfl⟩ : syracuseStep 18711971 = 28067957) B28067957
theorem B3696137 : Blo 1642020 3696137 := bstep (se 2 (by rfl) ⟨1386051, by rfl⟩ : syracuseStep 3696137 = 2772103) B2772103
theorem B5260897 : Blo 1642020 5260897 := bstep (se 2 (by rfl) ⟨1972836, by rfl⟩ : syracuseStep 5260897 = 3945673) B3945673
theorem B9356897 : Blo 1642020 9356897 := bstep (se 2 (by rfl) ⟨3508836, by rfl⟩ : syracuseStep 9356897 = 7017673) B7017673
theorem B12478049 : Blo 1642020 12478049 := bstep (se 2 (by rfl) ⟨4679268, by rfl⟩ : syracuseStep 12478049 = 9358537) B9358537
theorem B4679383 : Blo 1642020 4679383 := bstep (se 1 (by rfl) ⟨3509537, by rfl⟩ : syracuseStep 4679383 = 7019075) B7019075
theorem B7497515 : Blo 1642020 7497515 := bstep (se 1 (by rfl) ⟨5623136, by rfl⟩ : syracuseStep 7497515 = 11246273) B11246273
theorem B3696479 : Blo 1642020 3696479 := bstep (se 1 (by rfl) ⟨2772359, by rfl⟩ : syracuseStep 3696479 = 5544719) B5544719
theorem B2000747 : Blo 1642020 2000747 := bstep (se 1 (by rfl) ⟨1500560, by rfl⟩ : syracuseStep 2000747 = 3001121) B3001121
theorem B5547959 : Blo 1642020 5547959 := bstep (se 1 (by rfl) ⟨4160969, by rfl⟩ : syracuseStep 5547959 = 8321939) B8321939
theorem B3696659 : Blo 1642020 3696659 := bstep (se 1 (by rfl) ⟨2772494, by rfl⟩ : syracuseStep 3696659 = 5544989) B5544989
theorem B2771023 : Blo 1642020 2771023 := bstep (se 1 (by rfl) ⟨2078267, by rfl⟩ : syracuseStep 2771023 = 4156535) B4156535
theorem B2107471 : Blo 1642020 2107471 := bstep (se 1 (by rfl) ⟨1580603, by rfl⟩ : syracuseStep 2107471 = 3161207) B3161207
theorem B26634329 : Blo 1642020 26634329 := bstep (se 2 (by rfl) ⟨9987873, by rfl⟩ : syracuseStep 26634329 = 19975747) B19975747
theorem B12011609 : Blo 1642020 12011609 := bstep (se 2 (by rfl) ⟨4504353, by rfl⟩ : syracuseStep 12011609 = 9008707) B9008707
theorem B23693411 : Blo 1642020 23693411 := bstep (se 1 (by rfl) ⟨17770058, by rfl⟩ : syracuseStep 23693411 = 35540117) B35540117
theorem B2771273 : Blo 1642020 2771273 := bstep (se 2 (by rfl) ⟨1039227, by rfl⟩ : syracuseStep 2771273 = 2078455) B2078455
theorem B3697001 : Blo 1642020 3697001 := bstep (se 2 (by rfl) ⟨1386375, by rfl⟩ : syracuseStep 3697001 = 2772751) B2772751
theorem B5548553 : Blo 1642020 5548553 := bstep (se 2 (by rfl) ⟨2080707, by rfl⟩ : syracuseStep 5548553 = 4161415) B4161415
theorem B5262013 : Blo 1642020 5262013 := bstep (se 3 (by rfl) ⟨986627, by rfl⟩ : syracuseStep 5262013 = 1973255) B1973255
theorem B2771705 : Blo 1642020 2771705 := bstep (se 2 (by rfl) ⟨1039389, by rfl⟩ : syracuseStep 2771705 = 2078779) B2078779
theorem B2771887 : Blo 1642020 2771887 := bstep (se 1 (by rfl) ⟨2078915, by rfl⟩ : syracuseStep 2771887 = 4157831) B4157831
theorem B3697595 : Blo 1642020 3697595 := bstep (se 1 (by rfl) ⟨2773196, by rfl⟩ : syracuseStep 3697595 = 5546393) B5546393
theorem B2771975 : Blo 1642020 2771975 := bstep (se 1 (by rfl) ⟨2078981, by rfl⟩ : syracuseStep 2771975 = 4157963) B4157963
theorem B9358355 : Blo 1642020 9358355 := bstep (se 1 (by rfl) ⟨7018766, by rfl⟩ : syracuseStep 9358355 = 14037533) B14037533
theorem B12479507 : Blo 1642020 12479507 := bstep (se 1 (by rfl) ⟨9359630, by rfl⟩ : syracuseStep 12479507 = 18719261) B18719261
theorem B3697721 : Blo 1642020 3697721 := bstep (se 2 (by rfl) ⟨1386645, by rfl⟩ : syracuseStep 3697721 = 2773291) B2773291
theorem B6237263 : Blo 1642020 6237263 := bstep (se 1 (by rfl) ⟨4677947, by rfl⟩ : syracuseStep 6237263 = 9355895) B9355895
theorem B3329195 : Blo 1642020 3329195 := bstep (se 1 (by rfl) ⟨2496896, by rfl⟩ : syracuseStep 3329195 = 4993793) B4993793
theorem B10529995 : Blo 1642020 10529995 := bstep (se 1 (by rfl) ⟨7897496, by rfl⟩ : syracuseStep 10529995 = 15794993) B15794993
theorem B6237431 : Blo 1642020 6237431 := bstep (se 1 (by rfl) ⟨4678073, by rfl⟩ : syracuseStep 6237431 = 9356147) B9356147
theorem B2772319 : Blo 1642020 2772319 := bstep (se 1 (by rfl) ⟨2079239, by rfl⟩ : syracuseStep 2772319 = 4158479) B4158479
theorem B11849075 : Blo 1642020 11849075 := bstep (se 1 (by rfl) ⟨8886806, by rfl⟩ : syracuseStep 11849075 = 17773613) B17773613
theorem B3698063 : Blo 1642020 3698063 := bstep (se 1 (by rfl) ⟨2773547, by rfl⟩ : syracuseStep 3698063 = 5547095) B5547095
theorem B2772407 : Blo 1642020 2772407 := bstep (se 1 (by rfl) ⟨2079305, by rfl⟩ : syracuseStep 2772407 = 4158611) B4158611
theorem B9358811 : Blo 1642020 9358811 := bstep (se 1 (by rfl) ⟨7019108, by rfl⟩ : syracuseStep 9358811 = 14038217) B14038217
theorem B2338313 : Blo 1642020 2338313 := bstep (se 2 (by rfl) ⟨876867, by rfl⟩ : syracuseStep 2338313 = 1753735) B1753735
theorem B1642023 : Blo 1642020 1642023 := bstep (se 1 (by rfl) ⟨1231517, by rfl⟩ : syracuseStep 1642023 = 2463035) B2463035
theorem B1642063 : Blo 1642020 1642063 := bstep (se 1 (by rfl) ⟨1231547, by rfl⟩ : syracuseStep 1642063 = 2463095) B2463095
theorem B11849303 : Blo 1642020 11849303 := bstep (se 1 (by rfl) ⟨8886977, by rfl⟩ : syracuseStep 11849303 = 17773955) B17773955
theorem B1642079 : Blo 1642020 1642079 := bstep (se 1 (by rfl) ⟨1231559, by rfl⟩ : syracuseStep 1642079 = 2463119) B2463119
theorem B7016033 : Blo 1642020 7016033 := bstep (se 2 (by rfl) ⟨2631012, by rfl⟩ : syracuseStep 7016033 = 5262025) B5262025
theorem B9989729 : Blo 1642020 9989729 := bstep (se 2 (by rfl) ⟨3746148, by rfl⟩ : syracuseStep 9989729 = 7492297) B7492297
theorem B1642107 : Blo 1642020 1642107 := bstep (se 1 (by rfl) ⟨1231580, by rfl⟩ : syracuseStep 1642107 = 2463161) B2463161
theorem B2338427 : Blo 1642020 2338427 := bstep (se 1 (by rfl) ⟨1753820, by rfl⟩ : syracuseStep 2338427 = 3507641) B3507641
theorem B1642159 : Blo 1642020 1642159 := bstep (se 1 (by rfl) ⟨1231619, by rfl⟩ : syracuseStep 1642159 = 2463239) B2463239
theorem B1642183 : Blo 1642020 1642183 := bstep (se 1 (by rfl) ⟨1231637, by rfl⟩ : syracuseStep 1642183 = 2463275) B2463275
theorem B3698387 : Blo 1642020 3698387 := bstep (se 1 (by rfl) ⟨2773790, by rfl⟩ : syracuseStep 3698387 = 5547581) B5547581
theorem B9359063 : Blo 1642020 9359063 := bstep (se 1 (by rfl) ⟨7019297, by rfl⟩ : syracuseStep 9359063 = 14038595) B14038595
theorem B1642203 : Blo 1642020 1642203 := bstep (se 1 (by rfl) ⟨1231652, by rfl⟩ : syracuseStep 1642203 = 2463305) B2463305
theorem B1642279 : Blo 1642020 1642279 := bstep (se 1 (by rfl) ⟨1231709, by rfl⟩ : syracuseStep 1642279 = 2463419) B2463419
theorem B1642319 : Blo 1642020 1642319 := bstep (se 1 (by rfl) ⟨1231739, by rfl⟩ : syracuseStep 1642319 = 2463479) B2463479
theorem B1642335 : Blo 1642020 1642335 := bstep (se 1 (by rfl) ⟨1231751, by rfl⟩ : syracuseStep 1642335 = 2463503) B2463503
theorem B1642363 : Blo 1642020 1642363 := bstep (se 1 (by rfl) ⟨1231772, by rfl⟩ : syracuseStep 1642363 = 2463545) B2463545
theorem B4157345 : Blo 1642020 4157345 := bstep (se 2 (by rfl) ⟨1559004, by rfl⟩ : syracuseStep 4157345 = 3118009) B3118009
theorem B1642415 : Blo 1642020 1642415 := bstep (se 1 (by rfl) ⟨1231811, by rfl⟩ : syracuseStep 1642415 = 2463623) B2463623
theorem B2338735 : Blo 1642020 2338735 := bstep (se 1 (by rfl) ⟨1754051, by rfl⟩ : syracuseStep 2338735 = 3508103) B3508103
theorem B1642439 : Blo 1642020 1642439 := bstep (se 1 (by rfl) ⟨1231829, by rfl⟩ : syracuseStep 1642439 = 2463659) B2463659
theorem B1642459 : Blo 1642020 1642459 := bstep (se 1 (by rfl) ⟨1231844, by rfl⟩ : syracuseStep 1642459 = 2463689) B2463689
theorem B2773001 : Blo 1642020 2773001 := bstep (se 2 (by rfl) ⟨1039875, by rfl⟩ : syracuseStep 2773001 = 2079751) B2079751
theorem B1847335 : Blo 1642020 1847335 := bstep (se 1 (by rfl) ⟨1385501, by rfl⟩ : syracuseStep 1847335 = 2771003) B2771003
theorem B1642535 : Blo 1642020 1642535 := bstep (se 1 (by rfl) ⟨1231901, by rfl⟩ : syracuseStep 1642535 = 2463803) B2463803
theorem B1642575 : Blo 1642020 1642575 := bstep (se 1 (by rfl) ⟨1231931, by rfl⟩ : syracuseStep 1642575 = 2463863) B2463863
theorem B1642591 : Blo 1642020 1642591 := bstep (se 1 (by rfl) ⟨1231943, by rfl⟩ : syracuseStep 1642591 = 2463887) B2463887
theorem B1642619 : Blo 1642020 1642619 := bstep (se 1 (by rfl) ⟨1231964, by rfl⟩ : syracuseStep 1642619 = 2463929) B2463929
theorem B2773163 : Blo 1642020 2773163 := bstep (se 1 (by rfl) ⟨2079872, by rfl⟩ : syracuseStep 2773163 = 4159745) B4159745
theorem B1642671 : Blo 1642020 1642671 := bstep (se 1 (by rfl) ⟨1232003, by rfl⟩ : syracuseStep 1642671 = 2464007) B2464007
theorem B6238403 : Blo 1642020 6238403 := bstep (se 1 (by rfl) ⟨4678802, by rfl⟩ : syracuseStep 6238403 = 9357605) B9357605
theorem B1642695 : Blo 1642020 1642695 := bstep (se 1 (by rfl) ⟨1232021, by rfl⟩ : syracuseStep 1642695 = 2464043) B2464043
theorem B1642715 : Blo 1642020 1642715 := bstep (se 1 (by rfl) ⟨1232036, by rfl⟩ : syracuseStep 1642715 = 2464073) B2464073
theorem B2339065 : Blo 1642020 2339065 := bstep (se 2 (by rfl) ⟨877149, by rfl⟩ : syracuseStep 2339065 = 1754299) B1754299
theorem B10531073 : Blo 1642020 10531073 := bstep (se 2 (by rfl) ⟨3949152, by rfl⟩ : syracuseStep 10531073 = 7898305) B7898305
theorem B14037259 : Blo 1642020 14037259 := bstep (se 1 (by rfl) ⟨10527944, by rfl⟩ : syracuseStep 14037259 = 21055889) B21055889
theorem B1642791 : Blo 1642020 1642791 := bstep (se 1 (by rfl) ⟨1232093, by rfl⟩ : syracuseStep 1642791 = 2464187) B2464187
theorem B1642831 : Blo 1642020 1642831 := bstep (se 1 (by rfl) ⟨1232123, by rfl⟩ : syracuseStep 1642831 = 2464247) B2464247
theorem B11243863 : Blo 1642020 11243863 := bstep (se 1 (by rfl) ⟨8432897, by rfl⟩ : syracuseStep 11243863 = 16865795) B16865795
theorem B1642847 : Blo 1642020 1642847 := bstep (se 1 (by rfl) ⟨1232135, by rfl⟩ : syracuseStep 1642847 = 2464271) B2464271
theorem B4157801 : Blo 1642020 4157801 := bstep (se 2 (by rfl) ⟨1559175, by rfl⟩ : syracuseStep 4157801 = 3118351) B3118351
theorem B1642875 : Blo 1642020 1642875 := bstep (se 1 (by rfl) ⟨1232156, by rfl⟩ : syracuseStep 1642875 = 2464313) B2464313
theorem B10531225 : Blo 1642020 10531225 := bstep (se 2 (by rfl) ⟨3949209, by rfl⟩ : syracuseStep 10531225 = 7898419) B7898419
theorem B1642927 : Blo 1642020 1642927 := bstep (se 1 (by rfl) ⟨1232195, by rfl⟩ : syracuseStep 1642927 = 2464391) B2464391
theorem B1642951 : Blo 1642020 1642951 := bstep (se 1 (by rfl) ⟨1232213, by rfl⟩ : syracuseStep 1642951 = 2464427) B2464427
theorem B1642971 : Blo 1642020 1642971 := bstep (se 1 (by rfl) ⟨1232228, by rfl⟩ : syracuseStep 1642971 = 2464457) B2464457
theorem B5263859 : Blo 1642020 5263859 := bstep (se 1 (by rfl) ⟨3947894, by rfl⟩ : syracuseStep 5263859 = 7895789) B7895789
theorem B1643047 : Blo 1642020 1643047 := bstep (se 1 (by rfl) ⟨1232285, by rfl⟩ : syracuseStep 1643047 = 2464571) B2464571
theorem B2773561 : Blo 1642020 2773561 := bstep (se 2 (by rfl) ⟨1040085, by rfl⟩ : syracuseStep 2773561 = 2080171) B2080171
theorem B1643087 : Blo 1642020 1643087 := bstep (se 1 (by rfl) ⟨1232315, by rfl⟩ : syracuseStep 1643087 = 2464631) B2464631
theorem B1643103 : Blo 1642020 1643103 := bstep (se 1 (by rfl) ⟨1232327, by rfl⟩ : syracuseStep 1643103 = 2464655) B2464655
theorem B1643131 : Blo 1642020 1643131 := bstep (se 1 (by rfl) ⟨1232348, by rfl⟩ : syracuseStep 1643131 = 2464697) B2464697
theorem B1643183 : Blo 1642020 1643183 := bstep (se 1 (by rfl) ⟨1232387, by rfl⟩ : syracuseStep 1643183 = 2464775) B2464775
theorem B1643207 : Blo 1642020 1643207 := bstep (se 1 (by rfl) ⟨1232405, by rfl⟩ : syracuseStep 1643207 = 2464811) B2464811
theorem B2773703 : Blo 1642020 2773703 := bstep (se 1 (by rfl) ⟨2080277, by rfl⟩ : syracuseStep 2773703 = 4160555) B4160555
theorem B1643227 : Blo 1642020 1643227 := bstep (se 1 (by rfl) ⟨1232420, by rfl⟩ : syracuseStep 1643227 = 2464841) B2464841
theorem B4215545 : Blo 1642020 4215545 := bstep (se 2 (by rfl) ⟨1580829, by rfl⟩ : syracuseStep 4215545 = 3161659) B3161659
theorem B42095375 : Blo 1642020 42095375 := bstep (se 1 (by rfl) ⟨31571531, by rfl⟩ : syracuseStep 42095375 = 63143063) B63143063
theorem B1643303 : Blo 1642020 1643303 := bstep (se 1 (by rfl) ⟨1232477, by rfl⟩ : syracuseStep 1643303 = 2464955) B2464955
theorem B1643343 : Blo 1642020 1643343 := bstep (se 1 (by rfl) ⟨1232507, by rfl⟩ : syracuseStep 1643343 = 2465015) B2465015
theorem B1643359 : Blo 1642020 1643359 := bstep (se 1 (by rfl) ⟨1232519, by rfl⟩ : syracuseStep 1643359 = 2465039) B2465039
theorem B2773865 : Blo 1642020 2773865 := bstep (se 2 (by rfl) ⟨1040199, by rfl⟩ : syracuseStep 2773865 = 2080399) B2080399
theorem B5542775 : Blo 1642020 5542775 := bstep (se 1 (by rfl) ⟨4157081, by rfl⟩ : syracuseStep 5542775 = 8314163) B8314163
theorem B1643387 : Blo 1642020 1643387 := bstep (se 1 (by rfl) ⟨1232540, by rfl⟩ : syracuseStep 1643387 = 2465081) B2465081
theorem B1643439 : Blo 1642020 1643439 := bstep (se 1 (by rfl) ⟨1232579, by rfl⟩ : syracuseStep 1643439 = 2465159) B2465159
theorem B1643463 : Blo 1642020 1643463 := bstep (se 1 (by rfl) ⟨1232597, by rfl⟩ : syracuseStep 1643463 = 2465195) B2465195
theorem B1643483 : Blo 1642020 1643483 := bstep (se 1 (by rfl) ⟨1232612, by rfl⟩ : syracuseStep 1643483 = 2465225) B2465225
theorem B12645341 : Blo 1642020 12645341 := bstep (se 3 (by rfl) ⟨2371001, by rfl⟩ : syracuseStep 12645341 = 4742003) B4742003
theorem B23999489 : Blo 1642020 23999489 := bstep (se 2 (by rfl) ⟨8999808, by rfl⟩ : syracuseStep 23999489 = 17999617) B17999617
theorem B1643559 : Blo 1642020 1643559 := bstep (se 1 (by rfl) ⟨1232669, by rfl⟩ : syracuseStep 1643559 = 2465339) B2465339
theorem B18248753 : Blo 1642020 18248753 := bstep (se 2 (by rfl) ⟨6843282, by rfl⟩ : syracuseStep 18248753 = 13686565) B13686565
theorem B11998259 : Blo 1642020 11998259 := bstep (se 1 (by rfl) ⟨8998694, by rfl⟩ : syracuseStep 11998259 = 17997389) B17997389
theorem B12006467 : Blo 1642020 12006467 := bstep (se 1 (by rfl) ⟨9004850, by rfl⟩ : syracuseStep 12006467 = 18009701) B18009701
theorem B5542991 : Blo 1642020 5542991 := bstep (se 1 (by rfl) ⟨4157243, by rfl⟩ : syracuseStep 5542991 = 8314487) B8314487
theorem B1643599 : Blo 1642020 1643599 := bstep (se 1 (by rfl) ⟨1232699, by rfl⟩ : syracuseStep 1643599 = 2465399) B2465399
theorem B1643615 : Blo 1642020 1643615 := bstep (se 1 (by rfl) ⟨1232711, by rfl⟩ : syracuseStep 1643615 = 2465423) B2465423
theorem B1643643 : Blo 1642020 1643643 := bstep (se 1 (by rfl) ⟨1232732, by rfl⟩ : syracuseStep 1643643 = 2465465) B2465465
theorem B6239389 : Blo 1642020 6239389 := bstep (se 3 (by rfl) ⟨1169885, by rfl⟩ : syracuseStep 6239389 = 2339771) B2339771
theorem B1643695 : Blo 1642020 1643695 := bstep (se 1 (by rfl) ⟨1232771, by rfl⟩ : syracuseStep 1643695 = 2465543) B2465543
theorem B1643719 : Blo 1642020 1643719 := bstep (se 1 (by rfl) ⟨1232789, by rfl⟩ : syracuseStep 1643719 = 2465579) B2465579
theorem B1643739 : Blo 1642020 1643739 := bstep (se 1 (by rfl) ⟨1232804, by rfl⟩ : syracuseStep 1643739 = 2465609) B2465609
theorem B2774263 : Blo 1642020 2774263 := bstep (se 1 (by rfl) ⟨2080697, by rfl⟩ : syracuseStep 2774263 = 4161395) B4161395
theorem B1643815 : Blo 1642020 1643815 := bstep (se 1 (by rfl) ⟨1232861, by rfl⟩ : syracuseStep 1643815 = 2465723) B2465723
theorem B1643855 : Blo 1642020 1643855 := bstep (se 1 (by rfl) ⟨1232891, by rfl⟩ : syracuseStep 1643855 = 2465783) B2465783
theorem B2463071 : Blo 1642020 2463071 := bstep (se 1 (by rfl) ⟨1847303, by rfl⟩ : syracuseStep 2463071 = 3694607) B3694607
theorem B1643871 : Blo 1642020 1643871 := bstep (se 1 (by rfl) ⟨1232903, by rfl⟩ : syracuseStep 1643871 = 2465807) B2465807
theorem B73037155 : Blo 1642020 73037155 := bstep (se 1 (by rfl) ⟨54777866, by rfl⟩ : syracuseStep 73037155 = 109555733) B109555733
theorem B2463083 : Blo 1642020 2463083 := bstep (se 1 (by rfl) ⟨1847312, by rfl⟩ : syracuseStep 2463083 = 3694625) B3694625
theorem B1643899 : Blo 1642020 1643899 := bstep (se 1 (by rfl) ⟨1232924, by rfl⟩ : syracuseStep 1643899 = 2465849) B2465849
theorem B1643951 : Blo 1642020 1643951 := bstep (se 1 (by rfl) ⟨1232963, by rfl⟩ : syracuseStep 1643951 = 2465927) B2465927
theorem B5543369 : Blo 1642020 5543369 := bstep (se 2 (by rfl) ⟨2078763, by rfl⟩ : syracuseStep 5543369 = 4157527) B4157527
theorem B1643975 : Blo 1642020 1643975 := bstep (se 1 (by rfl) ⟨1232981, by rfl⟩ : syracuseStep 1643975 = 2465963) B2465963
theorem B7017947 : Blo 1642020 7017947 := bstep (se 1 (by rfl) ⟨5263460, by rfl⟩ : syracuseStep 7017947 = 10526921) B10526921
theorem B1643995 : Blo 1642020 1643995 := bstep (se 1 (by rfl) ⟨1232996, by rfl⟩ : syracuseStep 1643995 = 2465993) B2465993
theorem B3118601 : Blo 1642020 3118601 := bstep (se 2 (by rfl) ⟨1169475, by rfl⟩ : syracuseStep 3118601 = 2338951) B2338951
theorem B4158985 : Blo 1642020 4158985 := bstep (se 2 (by rfl) ⟨1559619, by rfl⟩ : syracuseStep 4158985 = 3119239) B3119239
theorem B2463311 : Blo 1642020 2463311 := bstep (se 1 (by rfl) ⟨1847483, by rfl⟩ : syracuseStep 2463311 = 3694967) B3694967
theorem B1848955 : Blo 1642020 1848955 := bstep (se 1 (by rfl) ⟨1386716, by rfl⟩ : syracuseStep 1848955 = 2773433) B2773433
theorem B2463431 : Blo 1642020 2463431 := bstep (se 1 (by rfl) ⟨1847573, by rfl⟩ : syracuseStep 2463431 = 3695147) B3695147
theorem B4216531 : Blo 1642020 4216531 := bstep (se 1 (by rfl) ⟨3162398, by rfl⟩ : syracuseStep 4216531 = 6324797) B6324797
theorem B5543639 : Blo 1642020 5543639 := bstep (se 1 (by rfl) ⟨4157729, by rfl⟩ : syracuseStep 5543639 = 8315459) B8315459
theorem B2463593 : Blo 1642020 2463593 := bstep (se 2 (by rfl) ⟨923847, by rfl⟩ : syracuseStep 2463593 = 1847695) B1847695
theorem B9361271 : Blo 1642020 9361271 := bstep (se 1 (by rfl) ⟨7020953, by rfl⟩ : syracuseStep 9361271 = 14041907) B14041907
theorem B12482423 : Blo 1642020 12482423 := bstep (se 1 (by rfl) ⟨9361817, by rfl⟩ : syracuseStep 12482423 = 18723635) B18723635
theorem B5543855 : Blo 1642020 5543855 := bstep (se 1 (by rfl) ⟨4157891, by rfl⟩ : syracuseStep 5543855 = 8315783) B8315783
theorem B2463671 : Blo 1642020 2463671 := bstep (se 1 (by rfl) ⟨1847753, by rfl⟩ : syracuseStep 2463671 = 3695507) B3695507
theorem B2463707 : Blo 1642020 2463707 := bstep (se 1 (by rfl) ⟨1847780, by rfl⟩ : syracuseStep 2463707 = 3695561) B3695561
theorem B9353231 : Blo 1642020 9353231 := bstep (se 1 (by rfl) ⟨7014923, by rfl⟩ : syracuseStep 9353231 = 14029847) B14029847
theorem B8886287 : Blo 1642020 8886287 := bstep (se 1 (by rfl) ⟨6664715, by rfl⟩ : syracuseStep 8886287 = 13329431) B13329431
theorem B5920847 : Blo 1642020 5920847 := bstep (se 1 (by rfl) ⟨4440635, by rfl⟩ : syracuseStep 5920847 = 8881271) B8881271
theorem B1849423 : Blo 1642020 1849423 := bstep (se 1 (by rfl) ⟨1387067, by rfl⟩ : syracuseStep 1849423 = 2774135) B2774135
theorem B26646785 : Blo 1642020 26646785 := bstep (se 2 (by rfl) ⟨9992544, by rfl⟩ : syracuseStep 26646785 = 19985089) B19985089
theorem B8321291 : Blo 1642020 8321291 := bstep (se 1 (by rfl) ⟨6240968, by rfl⟩ : syracuseStep 8321291 = 12481937) B12481937
theorem B3119467 : Blo 1642020 3119467 := bstep (se 1 (by rfl) ⟨2339600, by rfl⟩ : syracuseStep 3119467 = 4679201) B4679201
theorem B16005509 : Blo 1642020 16005509 := bstep (se 4 (by rfl) ⟨1500516, by rfl⟩ : syracuseStep 16005509 = 3001033) B3001033
theorem B2464175 : Blo 1642020 2464175 := bstep (se 1 (by rfl) ⟨1848131, by rfl⟩ : syracuseStep 2464175 = 3696263) B3696263
theorem B3119543 : Blo 1642020 3119543 := bstep (se 1 (by rfl) ⟨2339657, by rfl⟩ : syracuseStep 3119543 = 4679315) B4679315
theorem B8313353 : Blo 1642020 8313353 := bstep (se 2 (by rfl) ⟨3117507, by rfl⟩ : syracuseStep 8313353 = 6235015) B6235015
theorem B2464265 : Blo 1642020 2464265 := bstep (se 2 (by rfl) ⟨924099, by rfl⟩ : syracuseStep 2464265 = 1848199) B1848199
theorem B2464295 : Blo 1642020 2464295 := bstep (se 1 (by rfl) ⟨1848221, by rfl⟩ : syracuseStep 2464295 = 3696443) B3696443
theorem B9361979 : Blo 1642020 9361979 := bstep (se 1 (by rfl) ⟨7021484, by rfl⟩ : syracuseStep 9361979 = 14042969) B14042969
theorem B2464379 : Blo 1642020 2464379 := bstep (se 1 (by rfl) ⟨1848284, by rfl⟩ : syracuseStep 2464379 = 3696569) B3696569
theorem B57834163 : Blo 1642020 57834163 := bstep (se 1 (by rfl) ⟨43375622, by rfl⟩ : syracuseStep 57834163 = 86751245) B86751245
theorem B4676285 : Blo 1642020 4676285 := bstep (se 3 (by rfl) ⟨876803, by rfl⟩ : syracuseStep 4676285 = 1753607) B1753607
theorem B2464505 : Blo 1642020 2464505 := bstep (se 2 (by rfl) ⟨924189, by rfl⟩ : syracuseStep 2464505 = 1848379) B1848379
theorem B2464607 : Blo 1642020 2464607 := bstep (se 1 (by rfl) ⟨1848455, by rfl⟩ : syracuseStep 2464607 = 3696911) B3696911
theorem B3160937 : Blo 1642020 3160937 := bstep (se 2 (by rfl) ⟨1185351, by rfl⟩ : syracuseStep 3160937 = 2370703) B2370703
theorem B2464619 : Blo 1642020 2464619 := bstep (se 1 (by rfl) ⟨1848464, by rfl⟩ : syracuseStep 2464619 = 3696929) B3696929
theorem B3120059 : Blo 1642020 3120059 := bstep (se 1 (by rfl) ⟨2340044, by rfl⟩ : syracuseStep 3120059 = 4680089) B4680089
theorem B4160443 : Blo 1642020 4160443 := bstep (se 1 (by rfl) ⟨3120332, by rfl⟩ : syracuseStep 4160443 = 6240665) B6240665
theorem B5266433 : Blo 1642020 5266433 := bstep (se 2 (by rfl) ⟨1974912, by rfl⟩ : syracuseStep 5266433 = 3949825) B3949825
theorem B2464847 : Blo 1642020 2464847 := bstep (se 1 (by rfl) ⟨1848635, by rfl⟩ : syracuseStep 2464847 = 3697271) B3697271
theorem B2464967 : Blo 1642020 2464967 := bstep (se 1 (by rfl) ⟨1848725, by rfl⟩ : syracuseStep 2464967 = 3697451) B3697451
theorem B3374291 : Blo 1642020 3374291 := bstep (se 1 (by rfl) ⟨2530718, by rfl⟩ : syracuseStep 3374291 = 5061437) B5061437
theorem B2465129 : Blo 1642020 2465129 := bstep (se 2 (by rfl) ⟨924423, by rfl⟩ : syracuseStep 2465129 = 1848847) B1848847
theorem B18972029 : Blo 1642020 18972029 := bstep (se 3 (by rfl) ⟨3557255, by rfl⟩ : syracuseStep 18972029 = 7114511) B7114511
theorem B3120545 : Blo 1642020 3120545 := bstep (se 2 (by rfl) ⟨1170204, by rfl⟩ : syracuseStep 3120545 = 2340409) B2340409
theorem B2465207 : Blo 1642020 2465207 := bstep (se 1 (by rfl) ⟨1848905, by rfl⟩ : syracuseStep 2465207 = 3697811) B3697811
theorem B2465243 : Blo 1642020 2465243 := bstep (se 1 (by rfl) ⟨1848932, by rfl⟩ : syracuseStep 2465243 = 3697865) B3697865
theorem B3120697 : Blo 1642020 3120697 := bstep (se 2 (by rfl) ⟨1170261, by rfl⟩ : syracuseStep 3120697 = 2340523) B2340523
theorem B8322749 : Blo 1642020 8322749 := bstep (se 3 (by rfl) ⟨1560515, by rfl⟩ : syracuseStep 8322749 = 3121031) B3121031
theorem B7110443 : Blo 1642020 7110443 := bstep (se 1 (by rfl) ⟨5332832, by rfl⟩ : syracuseStep 7110443 = 10665665) B10665665
theorem B3121001 : Blo 1642020 3121001 := bstep (se 2 (by rfl) ⟨1170375, by rfl⟩ : syracuseStep 3121001 = 2340751) B2340751
theorem B7020407 : Blo 1642020 7020407 := bstep (se 1 (by rfl) ⟨5265305, by rfl⟩ : syracuseStep 7020407 = 10530611) B10530611
theorem B2465711 : Blo 1642020 2465711 := bstep (se 1 (by rfl) ⟨1849283, by rfl⟩ : syracuseStep 2465711 = 3698567) B3698567
theorem B8314811 : Blo 1642020 8314811 := bstep (se 1 (by rfl) ⟨6236108, by rfl⟩ : syracuseStep 8314811 = 12472217) B12472217
theorem B3694697 : Blo 1642020 3694697 := bstep (se 2 (by rfl) ⟨1385511, by rfl⟩ : syracuseStep 3694697 = 2771023) B2771023
theorem B2809961 : Blo 1642020 2809961 := bstep (se 2 (by rfl) ⟨1053735, by rfl⟩ : syracuseStep 2809961 = 2107471) B2107471
theorem B2465897 : Blo 1642020 2465897 := bstep (se 2 (by rfl) ⟨924711, by rfl⟩ : syracuseStep 2465897 = 1849423) B1849423
theorem B7020715 : Blo 1642020 7020715 := bstep (se 1 (by rfl) ⟨5265536, by rfl⟩ : syracuseStep 7020715 = 10531073) B10531073
theorem B32030957 : Blo 1642020 32030957 := bstep (se 3 (by rfl) ⟨6005804, by rfl⟩ : syracuseStep 32030957 = 12011609) B12011609
theorem B13320539 : Blo 1642020 13320539 := bstep (se 1 (by rfl) ⟨9990404, by rfl⟩ : syracuseStep 13320539 = 19980809) B19980809
theorem B14991817 : Blo 1642020 14991817 := bstep (se 2 (by rfl) ⟨5621931, by rfl⟩ : syracuseStep 14991817 = 11243863) B11243863
theorem B14041633 : Blo 1642020 14041633 := bstep (se 2 (by rfl) ⟨5265612, by rfl⟩ : syracuseStep 14041633 = 10531225) B10531225
theorem B3695183 : Blo 1642020 3695183 := bstep (se 1 (by rfl) ⟨2771387, by rfl⟩ : syracuseStep 3695183 = 5542775) B5542775
theorem B8430227 : Blo 1642020 8430227 := bstep (se 1 (by rfl) ⟨6322670, by rfl⟩ : syracuseStep 8430227 = 12645341) B12645341
theorem B15999659 : Blo 1642020 15999659 := bstep (se 1 (by rfl) ⟨11999744, by rfl⟩ : syracuseStep 15999659 = 23999489) B23999489
theorem B8110763 : Blo 1642020 8110763 := bstep (se 1 (by rfl) ⟨6083072, by rfl⟩ : syracuseStep 8110763 = 12166145) B12166145
theorem B22495927 : Blo 1642020 22495927 := bstep (se 1 (by rfl) ⟨16871945, by rfl⟩ : syracuseStep 22495927 = 33743891) B33743891
theorem B12165835 : Blo 1642020 12165835 := bstep (se 1 (by rfl) ⟨9124376, by rfl⟩ : syracuseStep 12165835 = 18248753) B18248753
theorem B8004311 : Blo 1642020 8004311 := bstep (se 1 (by rfl) ⟨6003233, by rfl⟩ : syracuseStep 8004311 = 12006467) B12006467
theorem B3695327 : Blo 1642020 3695327 := bstep (se 1 (by rfl) ⟨2771495, by rfl⟩ : syracuseStep 3695327 = 5542991) B5542991
theorem B77112217 : Blo 1642020 77112217 := bstep (se 2 (by rfl) ⟨28917081, by rfl⟩ : syracuseStep 77112217 = 57834163) B57834163
theorem B3695579 : Blo 1642020 3695579 := bstep (se 1 (by rfl) ⟨2771684, by rfl⟩ : syracuseStep 3695579 = 5543369) B5543369
theorem B4678631 : Blo 1642020 4678631 := bstep (se 1 (by rfl) ⟨3508973, by rfl⟩ : syracuseStep 4678631 = 7017947) B7017947
theorem B3695759 : Blo 1642020 3695759 := bstep (se 1 (by rfl) ⟨2771819, by rfl⟩ : syracuseStep 3695759 = 5543639) B5543639
theorem B4998343 : Blo 1642020 4998343 := bstep (se 1 (by rfl) ⟨3748757, by rfl⟩ : syracuseStep 4998343 = 7497515) B7497515
theorem B3695849 : Blo 1642020 3695849 := bstep (se 2 (by rfl) ⟨1385943, by rfl⟩ : syracuseStep 3695849 = 2771887) B2771887
theorem B5547257 : Blo 1642020 5547257 := bstep (se 2 (by rfl) ⟨2080221, by rfl⟩ : syracuseStep 5547257 = 4160443) B4160443
theorem B3695903 : Blo 1642020 3695903 := bstep (se 1 (by rfl) ⟨2771927, by rfl⟩ : syracuseStep 3695903 = 5543855) B5543855
theorem B6235487 : Blo 1642020 6235487 := bstep (se 1 (by rfl) ⟨4676615, by rfl⟩ : syracuseStep 6235487 = 9353231) B9353231
theorem B5924191 : Blo 1642020 5924191 := bstep (se 1 (by rfl) ⟨4443143, by rfl⟩ : syracuseStep 5924191 = 8886287) B8886287
theorem B6235501 : Blo 1642020 6235501 := bstep (se 3 (by rfl) ⟨1169156, by rfl⟩ : syracuseStep 6235501 = 2338313) B2338313
theorem B8316269 : Blo 1642020 8316269 := bstep (se 3 (by rfl) ⟨1559300, by rfl⟩ : syracuseStep 8316269 = 3118601) B3118601
theorem B5547527 : Blo 1642020 5547527 := bstep (se 1 (by rfl) ⟨4160645, by rfl⟩ : syracuseStep 5547527 = 8321291) B8321291
theorem B6235805 : Blo 1642020 6235805 := bstep (se 3 (by rfl) ⟨1169213, by rfl⟩ : syracuseStep 6235805 = 2338427) B2338427
theorem B3696425 : Blo 1642020 3696425 := bstep (se 2 (by rfl) ⟨1386159, by rfl⟩ : syracuseStep 3696425 = 2772319) B2772319
theorem B2107291 : Blo 1642020 2107291 := bstep (se 1 (by rfl) ⟨1580468, by rfl⟩ : syracuseStep 2107291 = 3160937) B3160937
theorem B7014529 : Blo 1642020 7014529 := bstep (se 2 (by rfl) ⟨2630448, by rfl⟩ : syracuseStep 7014529 = 5260897) B5260897
theorem B7899383 : Blo 1642020 7899383 := bstep (se 1 (by rfl) ⟨5924537, by rfl⟩ : syracuseStep 7899383 = 11849075) B11849075
theorem B5622041 : Blo 1642020 5622041 := bstep (se 2 (by rfl) ⟨2108265, by rfl⟩ : syracuseStep 5622041 = 4216531) B4216531
theorem B5335325 : Blo 1642020 5335325 := bstep (se 3 (by rfl) ⟨1000373, by rfl⟩ : syracuseStep 5335325 = 2000747) B2000747
theorem B7899535 : Blo 1642020 7899535 := bstep (se 1 (by rfl) ⟨5924651, by rfl⟩ : syracuseStep 7899535 = 11849303) B11849303
theorem B5548499 : Blo 1642020 5548499 := bstep (se 1 (by rfl) ⟨4161374, by rfl⟩ : syracuseStep 5548499 = 8322749) B8322749
theorem B4680271 : Blo 1642020 4680271 := bstep (se 1 (by rfl) ⟨3510203, by rfl⟩ : syracuseStep 4680271 = 7020407) B7020407
theorem B2771563 : Blo 1642020 2771563 := bstep (se 1 (by rfl) ⟨2078672, by rfl⟩ : syracuseStep 2771563 = 4157345) B4157345
theorem B71019341 : Blo 1642020 71019341 := bstep (se 3 (by rfl) ⟨13316126, by rfl⟩ : syracuseStep 71019341 = 26632253) B26632253
theorem B3697487 : Blo 1642020 3697487 := bstep (se 1 (by rfl) ⟨2773115, by rfl⟩ : syracuseStep 3697487 = 5546231) B5546231
theorem B2771867 : Blo 1642020 2771867 := bstep (se 1 (by rfl) ⟨2078900, by rfl⟩ : syracuseStep 2771867 = 4157801) B4157801
theorem B2632679 : Blo 1642020 2632679 := bstep (se 1 (by rfl) ⟨1974509, by rfl⟩ : syracuseStep 2632679 = 3949019) B3949019
theorem B3509239 : Blo 1642020 3509239 := bstep (se 1 (by rfl) ⟨2631929, by rfl⟩ : syracuseStep 3509239 = 5263859) B5263859
theorem B3697703 : Blo 1642020 3697703 := bstep (se 1 (by rfl) ⟨2773277, by rfl⟩ : syracuseStep 3697703 = 5546555) B5546555
theorem B4156555 : Blo 1642020 4156555 := bstep (se 1 (by rfl) ⟨3117416, by rfl⟩ : syracuseStep 4156555 = 6234833) B6234833
theorem B3697883 : Blo 1642020 3697883 := bstep (se 1 (by rfl) ⟨2773412, by rfl⟩ : syracuseStep 3697883 = 5546825) B5546825
theorem B7998839 : Blo 1642020 7998839 := bstep (se 1 (by rfl) ⟨5999129, by rfl⟩ : syracuseStep 7998839 = 11998259) B11998259
theorem B3698081 : Blo 1642020 3698081 := bstep (se 2 (by rfl) ⟨1386780, by rfl⟩ : syracuseStep 3698081 = 2773561) B2773561
theorem B4156859 : Blo 1642020 4156859 := bstep (se 1 (by rfl) ⟨3117644, by rfl⟩ : syracuseStep 4156859 = 6235289) B6235289
theorem B7892423 : Blo 1642020 7892423 := bstep (se 1 (by rfl) ⟨5919317, by rfl⟩ : syracuseStep 7892423 = 11838635) B11838635
theorem B1642047 : Blo 1642020 1642047 := bstep (se 1 (by rfl) ⟨1231535, by rfl⟩ : syracuseStep 1642047 = 2463071) B2463071
theorem B1642055 : Blo 1642020 1642055 := bstep (se 1 (by rfl) ⟨1231541, by rfl⟩ : syracuseStep 1642055 = 2463083) B2463083
theorem B7016017 : Blo 1642020 7016017 := bstep (se 2 (by rfl) ⟨2631006, by rfl⟩ : syracuseStep 7016017 = 5262013) B5262013
theorem B2338399 : Blo 1642020 2338399 := bstep (se 1 (by rfl) ⟨1753799, by rfl⟩ : syracuseStep 2338399 = 3507599) B3507599
theorem B1642207 : Blo 1642020 1642207 := bstep (se 1 (by rfl) ⟨1231655, by rfl⟩ : syracuseStep 1642207 = 2463311) B2463311
theorem B6237931 : Blo 1642020 6237931 := bstep (se 1 (by rfl) ⟨4678448, by rfl⟩ : syracuseStep 6237931 = 9356897) B9356897
theorem B8318699 : Blo 1642020 8318699 := bstep (se 1 (by rfl) ⟨6239024, by rfl⟩ : syracuseStep 8318699 = 12478049) B12478049
theorem B1642287 : Blo 1642020 1642287 := bstep (se 1 (by rfl) ⟨1231715, by rfl⟩ : syracuseStep 1642287 = 2463431) B2463431
theorem B1642395 : Blo 1642020 1642395 := bstep (se 1 (by rfl) ⟨1231796, by rfl⟩ : syracuseStep 1642395 = 2463593) B2463593
theorem B1642447 : Blo 1642020 1642447 := bstep (se 1 (by rfl) ⟨1231835, by rfl⟩ : syracuseStep 1642447 = 2463671) B2463671
theorem B3698639 : Blo 1642020 3698639 := bstep (se 1 (by rfl) ⟨2773979, by rfl⟩ : syracuseStep 3698639 = 5547959) B5547959
theorem B1642471 : Blo 1642020 1642471 := bstep (se 1 (by rfl) ⟨1231853, by rfl⟩ : syracuseStep 1642471 = 2463707) B2463707
theorem B17756219 : Blo 1642020 17756219 := bstep (se 1 (by rfl) ⟨13317164, by rfl⟩ : syracuseStep 17756219 = 26634329) B26634329
theorem B2437225 : Blo 1642020 2437225 := bstep (se 2 (by rfl) ⟨913959, by rfl⟩ : syracuseStep 2437225 = 1827919) B1827919
theorem B17764523 : Blo 1642020 17764523 := bstep (se 1 (by rfl) ⟨13323392, by rfl⟩ : syracuseStep 17764523 = 26646785) B26646785
theorem B6238417 : Blo 1642020 6238417 := bstep (se 2 (by rfl) ⟨2339406, by rfl⟩ : syracuseStep 6238417 = 4678813) B4678813
theorem B8319185 : Blo 1642020 8319185 := bstep (se 2 (by rfl) ⟨3119694, by rfl⟩ : syracuseStep 8319185 = 6239389) B6239389
theorem B1847515 : Blo 1642020 1847515 := bstep (se 1 (by rfl) ⟨1385636, by rfl⟩ : syracuseStep 1847515 = 2771273) B2771273
theorem B10670339 : Blo 1642020 10670339 := bstep (se 1 (by rfl) ⟨8002754, by rfl⟩ : syracuseStep 10670339 = 16005509) B16005509
theorem B1642783 : Blo 1642020 1642783 := bstep (se 1 (by rfl) ⟨1232087, by rfl⟩ : syracuseStep 1642783 = 2464175) B2464175
theorem B3699017 : Blo 1642020 3699017 := bstep (se 2 (by rfl) ⟨1387131, by rfl⟩ : syracuseStep 3699017 = 2774263) B2774263
theorem B5542235 : Blo 1642020 5542235 := bstep (se 1 (by rfl) ⟨4156676, by rfl⟩ : syracuseStep 5542235 = 8313353) B8313353
theorem B1642843 : Blo 1642020 1642843 := bstep (se 1 (by rfl) ⟨1232132, by rfl⟩ : syracuseStep 1642843 = 2464265) B2464265
theorem B3699035 : Blo 1642020 3699035 := bstep (se 1 (by rfl) ⟨2774276, by rfl⟩ : syracuseStep 3699035 = 5548553) B5548553
theorem B1642863 : Blo 1642020 1642863 := bstep (se 1 (by rfl) ⟨1232147, by rfl⟩ : syracuseStep 1642863 = 2464295) B2464295
theorem B1642919 : Blo 1642020 1642919 := bstep (se 1 (by rfl) ⟨1232189, by rfl⟩ : syracuseStep 1642919 = 2464379) B2464379
theorem B3117523 : Blo 1642020 3117523 := bstep (se 1 (by rfl) ⟨2338142, by rfl⟩ : syracuseStep 3117523 = 4676285) B4676285
theorem B97382873 : Blo 1642020 97382873 := bstep (se 2 (by rfl) ⟨36518577, by rfl⟩ : syracuseStep 97382873 = 73037155) B73037155
theorem B1847803 : Blo 1642020 1847803 := bstep (se 1 (by rfl) ⟨1385852, by rfl⟩ : syracuseStep 1847803 = 2771705) B2771705
theorem B1643003 : Blo 1642020 1643003 := bstep (se 1 (by rfl) ⟨1232252, by rfl⟩ : syracuseStep 1643003 = 2464505) B2464505
theorem B6238721 : Blo 1642020 6238721 := bstep (se 2 (by rfl) ⟨2339520, by rfl⟩ : syracuseStep 6238721 = 4679041) B4679041
theorem B1643071 : Blo 1642020 1643071 := bstep (se 1 (by rfl) ⟨1232303, by rfl⟩ : syracuseStep 1643071 = 2464607) B2464607
theorem B1643079 : Blo 1642020 1643079 := bstep (se 1 (by rfl) ⟨1232309, by rfl⟩ : syracuseStep 1643079 = 2464619) B2464619
theorem B3510955 : Blo 1642020 3510955 := bstep (se 1 (by rfl) ⟨2633216, by rfl⟩ : syracuseStep 3510955 = 5266433) B5266433
theorem B1847983 : Blo 1642020 1847983 := bstep (se 1 (by rfl) ⟨1385987, by rfl⟩ : syracuseStep 1847983 = 2771975) B2771975
theorem B6238903 : Blo 1642020 6238903 := bstep (se 1 (by rfl) ⟨4679177, by rfl⟩ : syracuseStep 6238903 = 9358355) B9358355
theorem B8319671 : Blo 1642020 8319671 := bstep (se 1 (by rfl) ⟨6239753, by rfl⟩ : syracuseStep 8319671 = 12479507) B12479507
theorem B4158175 : Blo 1642020 4158175 := bstep (se 1 (by rfl) ⟨3118631, by rfl⟩ : syracuseStep 4158175 = 6237263) B6237263
theorem B1643231 : Blo 1642020 1643231 := bstep (se 1 (by rfl) ⟨1232423, by rfl⟩ : syracuseStep 1643231 = 2464847) B2464847
theorem B1643311 : Blo 1642020 1643311 := bstep (se 1 (by rfl) ⟨1232483, by rfl⟩ : syracuseStep 1643311 = 2464967) B2464967
theorem B2249527 : Blo 1642020 2249527 := bstep (se 1 (by rfl) ⟨1687145, by rfl⟩ : syracuseStep 2249527 = 3374291) B3374291
theorem B4158287 : Blo 1642020 4158287 := bstep (se 1 (by rfl) ⟨3118715, by rfl⟩ : syracuseStep 4158287 = 6237431) B6237431
theorem B1643419 : Blo 1642020 1643419 := bstep (se 1 (by rfl) ⟨1232564, by rfl⟩ : syracuseStep 1643419 = 2465129) B2465129
theorem B6239177 : Blo 1642020 6239177 := bstep (se 2 (by rfl) ⟨2339691, by rfl⟩ : syracuseStep 6239177 = 4679383) B4679383
theorem B1848271 : Blo 1642020 1848271 := bstep (se 1 (by rfl) ⟨1386203, by rfl⟩ : syracuseStep 1848271 = 2772407) B2772407
theorem B1643471 : Blo 1642020 1643471 := bstep (se 1 (by rfl) ⟨1232603, by rfl⟩ : syracuseStep 1643471 = 2465207) B2465207
theorem B6239207 : Blo 1642020 6239207 := bstep (se 1 (by rfl) ⟨4679405, by rfl⟩ : syracuseStep 6239207 = 9358811) B9358811
theorem B1643495 : Blo 1642020 1643495 := bstep (se 1 (by rfl) ⟨1232621, by rfl⟩ : syracuseStep 1643495 = 2465243) B2465243
theorem B6239375 : Blo 1642020 6239375 := bstep (se 1 (by rfl) ⟨4679531, by rfl⟩ : syracuseStep 6239375 = 9359063) B9359063
theorem B8320157 : Blo 1642020 8320157 := bstep (se 3 (by rfl) ⟨1560029, by rfl⟩ : syracuseStep 8320157 = 3120059) B3120059
theorem B4740295 : Blo 1642020 4740295 := bstep (se 1 (by rfl) ⟨3555221, by rfl⟩ : syracuseStep 4740295 = 7110443) B7110443
theorem B3118313 : Blo 1642020 3118313 := bstep (se 2 (by rfl) ⟨1169367, by rfl⟩ : syracuseStep 3118313 = 2338735) B2338735
theorem B1643807 : Blo 1642020 1643807 := bstep (se 1 (by rfl) ⟨1232855, by rfl⟩ : syracuseStep 1643807 = 2465711) B2465711
theorem B5543207 : Blo 1642020 5543207 := bstep (se 1 (by rfl) ⟨4157405, by rfl⟩ : syracuseStep 5543207 = 8314811) B8314811
theorem B1848667 : Blo 1642020 1848667 := bstep (se 1 (by rfl) ⟨1386500, by rfl⟩ : syracuseStep 1848667 = 2773001) B2773001
theorem B1643867 : Blo 1642020 1643867 := bstep (se 1 (by rfl) ⟨1232900, by rfl⟩ : syracuseStep 1643867 = 2465801) B2465801
theorem B1643887 : Blo 1642020 1643887 := bstep (se 1 (by rfl) ⟨1232915, by rfl⟩ : syracuseStep 1643887 = 2465831) B2465831
theorem B2463113 : Blo 1642020 2463113 := bstep (se 2 (by rfl) ⟨923667, by rfl⟩ : syracuseStep 2463113 = 1847335) B1847335
theorem B1643943 : Blo 1642020 1643943 := bstep (se 1 (by rfl) ⟨1232957, by rfl⟩ : syracuseStep 1643943 = 2465915) B2465915
theorem B1848775 : Blo 1642020 1848775 := bstep (se 1 (by rfl) ⟨1386581, by rfl⟩ : syracuseStep 1848775 = 2773163) B2773163
theorem B4158935 : Blo 1642020 4158935 := bstep (se 1 (by rfl) ⟨3119201, by rfl⟩ : syracuseStep 4158935 = 6238403) B6238403
theorem B63182429 : Blo 1642020 63182429 := bstep (se 3 (by rfl) ⟨11846705, by rfl⟩ : syracuseStep 63182429 = 23693411) B23693411
theorem B3118753 : Blo 1642020 3118753 := bstep (se 2 (by rfl) ⟨1169532, by rfl⟩ : syracuseStep 3118753 = 2339065) B2339065
theorem B18716345 : Blo 1642020 18716345 := bstep (se 2 (by rfl) ⟨7018629, by rfl⟩ : syracuseStep 18716345 = 14037259) B14037259
theorem B2463467 : Blo 1642020 2463467 := bstep (se 1 (by rfl) ⟨1847600, by rfl⟩ : syracuseStep 2463467 = 3695201) B3695201
theorem B8877853 : Blo 1642020 8877853 := bstep (se 3 (by rfl) ⟨1664597, by rfl⟩ : syracuseStep 8877853 = 3329195) B3329195
theorem B1849135 : Blo 1642020 1849135 := bstep (se 1 (by rfl) ⟨1386851, by rfl⟩ : syracuseStep 1849135 = 2773703) B2773703
theorem B4159289 : Blo 1642020 4159289 := bstep (se 2 (by rfl) ⟨1559733, by rfl⟩ : syracuseStep 4159289 = 3119467) B3119467
theorem B28063583 : Blo 1642020 28063583 := bstep (se 1 (by rfl) ⟨21047687, by rfl⟩ : syracuseStep 28063583 = 42095375) B42095375
theorem B1849243 : Blo 1642020 1849243 := bstep (se 1 (by rfl) ⟨1386932, by rfl⟩ : syracuseStep 1849243 = 2773865) B2773865
theorem B2463695 : Blo 1642020 2463695 := bstep (se 1 (by rfl) ⟨1847771, by rfl⟩ : syracuseStep 2463695 = 3695543) B3695543
theorem B5544071 : Blo 1642020 5544071 := bstep (se 1 (by rfl) ⟨4158053, by rfl⟩ : syracuseStep 5544071 = 8316107) B8316107
theorem B12474647 : Blo 1642020 12474647 := bstep (se 1 (by rfl) ⟨9355985, by rfl⟩ : syracuseStep 12474647 = 18711971) B18711971
theorem B50592077 : Blo 1642020 50592077 := bstep (se 3 (by rfl) ⟨9486014, by rfl⟩ : syracuseStep 50592077 = 18972029) B18972029
theorem B2464091 : Blo 1642020 2464091 := bstep (se 1 (by rfl) ⟨1848068, by rfl⟩ : syracuseStep 2464091 = 3696137) B3696137
theorem B8321453 : Blo 1642020 8321453 := bstep (se 3 (by rfl) ⟨1560272, by rfl⟩ : syracuseStep 8321453 = 3120545) B3120545
theorem B2464319 : Blo 1642020 2464319 := bstep (se 1 (by rfl) ⟨1848239, by rfl⟩ : syracuseStep 2464319 = 3696479) B3696479
theorem B6240847 : Blo 1642020 6240847 := bstep (se 1 (by rfl) ⟨4680635, by rfl⟩ : syracuseStep 6240847 = 9361271) B9361271
theorem B8321615 : Blo 1642020 8321615 := bstep (se 1 (by rfl) ⟨6241211, by rfl⟩ : syracuseStep 8321615 = 12482423) B12482423
theorem B2464439 : Blo 1642020 2464439 := bstep (se 1 (by rfl) ⟨1848329, by rfl⟩ : syracuseStep 2464439 = 3696659) B3696659
theorem B3947231 : Blo 1642020 3947231 := bstep (se 1 (by rfl) ⟨2960423, by rfl⟩ : syracuseStep 3947231 = 5920847) B5920847
theorem B2464667 : Blo 1642020 2464667 := bstep (se 1 (by rfl) ⟨1848500, by rfl⟩ : syracuseStep 2464667 = 3697001) B3697001
theorem B14039993 : Blo 1642020 14039993 := bstep (se 2 (by rfl) ⟨5264997, by rfl⟩ : syracuseStep 14039993 = 10529995) B10529995
theorem B2079695 : Blo 1642020 2079695 := bstep (se 1 (by rfl) ⟨1559771, by rfl⟩ : syracuseStep 2079695 = 3119543) B3119543
theorem B6241319 : Blo 1642020 6241319 := bstep (se 1 (by rfl) ⟨4680989, by rfl⟩ : syracuseStep 6241319 = 9361979) B9361979
theorem B2465063 : Blo 1642020 2465063 := bstep (se 1 (by rfl) ⟨1848797, by rfl⟩ : syracuseStep 2465063 = 3697595) B3697595
theorem B5545313 : Blo 1642020 5545313 := bstep (se 2 (by rfl) ⟨2079492, by rfl⟩ : syracuseStep 5545313 = 4158985) B4158985
theorem B2465147 : Blo 1642020 2465147 := bstep (se 1 (by rfl) ⟨1848860, by rfl⟩ : syracuseStep 2465147 = 3697721) B3697721
theorem B4160929 : Blo 1642020 4160929 := bstep (se 2 (by rfl) ⟨1560348, by rfl⟩ : syracuseStep 4160929 = 3120697) B3120697
theorem B2465273 : Blo 1642020 2465273 := bstep (se 2 (by rfl) ⟨924477, by rfl⟩ : syracuseStep 2465273 = 1848955) B1848955
theorem B2465375 : Blo 1642020 2465375 := bstep (se 1 (by rfl) ⟨1849031, by rfl⟩ : syracuseStep 2465375 = 3698063) B3698063
theorem B4677355 : Blo 1642020 4677355 := bstep (se 1 (by rfl) ⟨3508016, by rfl⟩ : syracuseStep 4677355 = 7016033) B7016033
theorem B6659819 : Blo 1642020 6659819 := bstep (se 1 (by rfl) ⟨4994864, by rfl⟩ : syracuseStep 6659819 = 9989729) B9989729
theorem B2465591 : Blo 1642020 2465591 := bstep (se 1 (by rfl) ⟨1849193, by rfl⟩ : syracuseStep 2465591 = 3698387) B3698387
theorem B2080667 : Blo 1642020 2080667 := bstep (se 1 (by rfl) ⟨1560500, by rfl⟩ : syracuseStep 2080667 = 3121001) B3121001
theorem B44965813 : Blo 1642020 44965813 := bstep (se 5 (by rfl) ⟨2107772, by rfl⟩ : syracuseStep 44965813 = 4215545) B4215545
theorem B5546123 : Blo 1642020 5546123 := bstep (se 1 (by rfl) ⟨4159592, by rfl⟩ : syracuseStep 5546123 = 8319185) B8319185
theorem B47349917 : Blo 1642020 47349917 := bstep (se 3 (by rfl) ⟨8878109, by rfl⟩ : syracuseStep 47349917 = 17756219) B17756219
theorem B2466011 : Blo 1642020 2466011 := bstep (se 1 (by rfl) ⟨1849508, by rfl⟩ : syracuseStep 2466011 = 3699017) B3699017
theorem B3694823 : Blo 1642020 3694823 := bstep (se 1 (by rfl) ⟨2771117, by rfl⟩ : syracuseStep 3694823 = 5542235) B5542235
theorem B8880359 : Blo 1642020 8880359 := bstep (se 1 (by rfl) ⟨6660269, by rfl⟩ : syracuseStep 8880359 = 13320539) B13320539
theorem B2466023 : Blo 1642020 2466023 := bstep (se 1 (by rfl) ⟨1849517, by rfl⟩ : syracuseStep 2466023 = 3699035) B3699035
theorem B64921915 : Blo 1642020 64921915 := bstep (se 1 (by rfl) ⟨48691436, by rfl⟩ : syracuseStep 64921915 = 97382873) B97382873
theorem B5620151 : Blo 1642020 5620151 := bstep (se 1 (by rfl) ⟨4215113, by rfl⟩ : syracuseStep 5620151 = 8430227) B8430227
theorem B10666439 : Blo 1642020 10666439 := bstep (se 1 (by rfl) ⟨7999829, by rfl⟩ : syracuseStep 10666439 = 15999659) B15999659
theorem B5407175 : Blo 1642020 5407175 := bstep (se 1 (by rfl) ⟨4055381, by rfl⟩ : syracuseStep 5407175 = 8110763) B8110763
theorem B5546447 : Blo 1642020 5546447 := bstep (se 1 (by rfl) ⟨4159835, by rfl⟩ : syracuseStep 5546447 = 8319671) B8319671
theorem B19989089 : Blo 1642020 19989089 := bstep (se 2 (by rfl) ⟨7495908, by rfl⟩ : syracuseStep 19989089 = 14991817) B14991817
theorem B5546771 : Blo 1642020 5546771 := bstep (se 1 (by rfl) ⟨4160078, by rfl⟩ : syracuseStep 5546771 = 8320157) B8320157
theorem B3695417 : Blo 1642020 3695417 := bstep (se 2 (by rfl) ⟨1385781, by rfl⟩ : syracuseStep 3695417 = 2771563) B2771563
theorem B3695471 : Blo 1642020 3695471 := bstep (se 1 (by rfl) ⟨2771603, by rfl⟩ : syracuseStep 3695471 = 5543207) B5543207
theorem B16221113 : Blo 1642020 16221113 := bstep (se 2 (by rfl) ⟨6082917, by rfl⟩ : syracuseStep 16221113 = 12165835) B12165835
theorem B2999369 : Blo 1642020 2999369 := bstep (se 2 (by rfl) ⟨1124763, by rfl⟩ : syracuseStep 2999369 = 2249527) B2249527
theorem B12477563 : Blo 1642020 12477563 := bstep (se 1 (by rfl) ⟨9358172, by rfl⟩ : syracuseStep 12477563 = 18716345) B18716345
theorem B4678985 : Blo 1642020 4678985 := bstep (se 2 (by rfl) ⟨1754619, by rfl⟩ : syracuseStep 4678985 = 3509239) B3509239
theorem B3696047 : Blo 1642020 3696047 := bstep (se 1 (by rfl) ⟨2772035, by rfl⟩ : syracuseStep 3696047 = 5544071) B5544071
theorem B8316431 : Blo 1642020 8316431 := bstep (se 1 (by rfl) ⟨6237323, by rfl⟩ : syracuseStep 8316431 = 12474647) B12474647
theorem B3556883 : Blo 1642020 3556883 := bstep (se 1 (by rfl) ⟨2667662, by rfl⟩ : syracuseStep 3556883 = 5335325) B5335325
theorem B33728051 : Blo 1642020 33728051 := bstep (se 1 (by rfl) ⟨25296038, by rfl⟩ : syracuseStep 33728051 = 50592077) B50592077
theorem B5547635 : Blo 1642020 5547635 := bstep (se 1 (by rfl) ⟨4160726, by rfl⟩ : syracuseStep 5547635 = 8321453) B8321453
theorem B5547743 : Blo 1642020 5547743 := bstep (se 1 (by rfl) ⟨4160807, by rfl⟩ : syracuseStep 5547743 = 8321615) B8321615
theorem B7898921 : Blo 1642020 7898921 := bstep (se 2 (by rfl) ⟨2962095, by rfl⟩ : syracuseStep 7898921 = 5924191) B5924191
theorem B5547905 : Blo 1642020 5547905 := bstep (se 2 (by rfl) ⟨2080464, by rfl⟩ : syracuseStep 5547905 = 4160929) B4160929
theorem B1755119 : Blo 1642020 1755119 := bstep (se 1 (by rfl) ⟨1316339, by rfl⟩ : syracuseStep 1755119 = 2632679) B2632679
theorem B3696875 : Blo 1642020 3696875 := bstep (se 1 (by rfl) ⟨2772656, by rfl⟩ : syracuseStep 3696875 = 5545313) B5545313
theorem B2771239 : Blo 1642020 2771239 := bstep (se 1 (by rfl) ⟨2078429, by rfl⟩ : syracuseStep 2771239 = 4156859) B4156859
theorem B5261615 : Blo 1642020 5261615 := bstep (se 1 (by rfl) ⟨3946211, by rfl⟩ : syracuseStep 5261615 = 7892423) B7892423
theorem B6236473 : Blo 1642020 6236473 := bstep (se 2 (by rfl) ⟨2338677, by rfl⟩ : syracuseStep 6236473 = 4677355) B4677355
theorem B8317241 : Blo 1642020 8317241 := bstep (se 2 (by rfl) ⟨3118965, by rfl⟩ : syracuseStep 8317241 = 6237931) B6237931
theorem B5548445 : Blo 1642020 5548445 := bstep (se 3 (by rfl) ⟨1040333, by rfl⟩ : syracuseStep 5548445 = 2080667) B2080667
theorem B8317889 : Blo 1642020 8317889 := bstep (se 2 (by rfl) ⟨3119208, by rfl⟩ : syracuseStep 8317889 = 6238417) B6238417
theorem B5336207 : Blo 1642020 5336207 := bstep (se 1 (by rfl) ⟨4002155, by rfl⟩ : syracuseStep 5336207 = 8004311) B8004311
theorem B2772191 : Blo 1642020 2772191 := bstep (se 1 (by rfl) ⟨2079143, by rfl⟩ : syracuseStep 2772191 = 4158287) B4158287
theorem B4156697 : Blo 1642020 4156697 := bstep (se 2 (by rfl) ⟨1558761, by rfl⟩ : syracuseStep 4156697 = 3117523) B3117523
theorem B28454237 : Blo 1642020 28454237 := bstep (se 3 (by rfl) ⟨5335169, by rfl⟩ : syracuseStep 28454237 = 10670339) B10670339
theorem B18722177 : Blo 1642020 18722177 := bstep (se 2 (by rfl) ⟨7020816, by rfl⟩ : syracuseStep 18722177 = 14041633) B14041633
theorem B3698171 : Blo 1642020 3698171 := bstep (se 1 (by rfl) ⟨2773628, by rfl⟩ : syracuseStep 3698171 = 5547257) B5547257
theorem B4156991 : Blo 1642020 4156991 := bstep (se 1 (by rfl) ⟨3117743, by rfl⟩ : syracuseStep 4156991 = 6235487) B6235487
theorem B8318537 : Blo 1642020 8318537 := bstep (se 2 (by rfl) ⟨3119451, by rfl⟩ : syracuseStep 8318537 = 6238903) B6238903
theorem B29994569 : Blo 1642020 29994569 := bstep (se 2 (by rfl) ⟨11247963, by rfl⟩ : syracuseStep 29994569 = 22495927) B22495927
theorem B1642075 : Blo 1642020 1642075 := bstep (se 1 (by rfl) ⟨1231556, by rfl⟩ : syracuseStep 1642075 = 2463113) B2463113
theorem B2772623 : Blo 1642020 2772623 := bstep (se 1 (by rfl) ⟨2079467, by rfl⟩ : syracuseStep 2772623 = 4158935) B4158935
theorem B3698351 : Blo 1642020 3698351 := bstep (se 1 (by rfl) ⟨2773763, by rfl⟩ : syracuseStep 3698351 = 5547527) B5547527
theorem B4157203 : Blo 1642020 4157203 := bstep (se 1 (by rfl) ⟨3117902, by rfl⟩ : syracuseStep 4157203 = 6235805) B6235805
theorem B1642311 : Blo 1642020 1642311 := bstep (se 1 (by rfl) ⟨1231733, by rfl⟩ : syracuseStep 1642311 = 2463467) B2463467
theorem B2772859 : Blo 1642020 2772859 := bstep (se 1 (by rfl) ⟨2079644, by rfl⟩ : syracuseStep 2772859 = 4159289) B4159289
theorem B1642463 : Blo 1642020 1642463 := bstep (se 1 (by rfl) ⟨1231847, by rfl⟩ : syracuseStep 1642463 = 2463695) B2463695
theorem B5542073 : Blo 1642020 5542073 := bstep (se 2 (by rfl) ⟨2078277, by rfl⟩ : syracuseStep 5542073 = 4156555) B4156555
theorem B3748027 : Blo 1642020 3748027 := bstep (se 1 (by rfl) ⟨2811020, by rfl⟩ : syracuseStep 3748027 = 5622041) B5622041
theorem B1642727 : Blo 1642020 1642727 := bstep (se 1 (by rfl) ⟨1232045, by rfl⟩ : syracuseStep 1642727 = 2464091) B2464091
theorem B6320393 : Blo 1642020 6320393 := bstep (se 2 (by rfl) ⟨2370147, by rfl⟩ : syracuseStep 6320393 = 4740295) B4740295
theorem B6664457 : Blo 1642020 6664457 := bstep (se 2 (by rfl) ⟨2499171, by rfl⟩ : syracuseStep 6664457 = 4998343) B4998343
theorem B3698999 : Blo 1642020 3698999 := bstep (se 1 (by rfl) ⟨2774249, by rfl⟩ : syracuseStep 3698999 = 5548499) B5548499
theorem B1642879 : Blo 1642020 1642879 := bstep (se 1 (by rfl) ⟨1232159, by rfl⟩ : syracuseStep 1642879 = 2464319) B2464319
theorem B1642959 : Blo 1642020 1642959 := bstep (se 1 (by rfl) ⟨1232219, by rfl⟩ : syracuseStep 1642959 = 2464439) B2464439
theorem B47346227 : Blo 1642020 47346227 := bstep (se 1 (by rfl) ⟨35509670, by rfl⟩ : syracuseStep 47346227 = 71019341) B71019341
theorem B1847911 : Blo 1642020 1847911 := bstep (se 1 (by rfl) ⟨1385933, by rfl⟩ : syracuseStep 1847911 = 2771867) B2771867
theorem B1643111 : Blo 1642020 1643111 := bstep (se 1 (by rfl) ⟨1232333, by rfl⟩ : syracuseStep 1643111 = 2464667) B2464667
theorem B9359995 : Blo 1642020 9359995 := bstep (se 1 (by rfl) ⟨7019996, by rfl⟩ : syracuseStep 9359995 = 14039993) B14039993
theorem B3117865 : Blo 1642020 3117865 := bstep (se 2 (by rfl) ⟨1169199, by rfl⟩ : syracuseStep 3117865 = 2338399) B2338399
theorem B1643375 : Blo 1642020 1643375 := bstep (se 1 (by rfl) ⟨1232531, by rfl⟩ : syracuseStep 1643375 = 2465063) B2465063
theorem B4158337 : Blo 1642020 4158337 := bstep (se 2 (by rfl) ⟨1559376, by rfl⟩ : syracuseStep 4158337 = 3118753) B3118753
theorem B1643431 : Blo 1642020 1643431 := bstep (se 1 (by rfl) ⟨1232573, by rfl⟩ : syracuseStep 1643431 = 2465147) B2465147
theorem B1643515 : Blo 1642020 1643515 := bstep (se 1 (by rfl) ⟨1232636, by rfl⟩ : syracuseStep 1643515 = 2465273) B2465273
theorem B1643583 : Blo 1642020 1643583 := bstep (se 1 (by rfl) ⟨1232687, by rfl⟩ : syracuseStep 1643583 = 2465375) B2465375
theorem B1643727 : Blo 1642020 1643727 := bstep (se 1 (by rfl) ⟨1232795, by rfl⟩ : syracuseStep 1643727 = 2465591) B2465591
theorem B59954417 : Blo 1642020 59954417 := bstep (se 2 (by rfl) ⟨22482906, by rfl⟩ : syracuseStep 59954417 = 44965813) B44965813
theorem B2463131 : Blo 1642020 2463131 := bstep (se 1 (by rfl) ⟨1847348, by rfl⟩ : syracuseStep 2463131 = 3694697) B3694697
theorem B1873307 : Blo 1642020 1873307 := bstep (se 1 (by rfl) ⟨1404980, by rfl⟩ : syracuseStep 1873307 = 2809961) B2809961
theorem B1643931 : Blo 1642020 1643931 := bstep (se 1 (by rfl) ⟨1232948, by rfl⟩ : syracuseStep 1643931 = 2465897) B2465897
theorem B11843015 : Blo 1642020 11843015 := bstep (se 1 (by rfl) ⟨8882261, by rfl⟩ : syracuseStep 11843015 = 17764523) B17764523
theorem B21353971 : Blo 1642020 21353971 := bstep (se 1 (by rfl) ⟨16015478, by rfl⟩ : syracuseStep 21353971 = 32030957) B32030957
theorem B9352705 : Blo 1642020 9352705 := bstep (se 2 (by rfl) ⟨3507264, by rfl⟩ : syracuseStep 9352705 = 7014529) B7014529
theorem B9360953 : Blo 1642020 9360953 := bstep (se 2 (by rfl) ⟨3510357, by rfl⟩ : syracuseStep 9360953 = 7020715) B7020715
theorem B2463353 : Blo 1642020 2463353 := bstep (se 2 (by rfl) ⟨923757, by rfl⟩ : syracuseStep 2463353 = 1847515) B1847515
theorem B4159147 : Blo 1642020 4159147 := bstep (se 1 (by rfl) ⟨3119360, by rfl⟩ : syracuseStep 4159147 = 6238721) B6238721
theorem B2463455 : Blo 1642020 2463455 := bstep (se 1 (by rfl) ⟨1847591, by rfl⟩ : syracuseStep 2463455 = 3695183) B3695183
theorem B2463551 : Blo 1642020 2463551 := bstep (se 1 (by rfl) ⟨1847663, by rfl⟩ : syracuseStep 2463551 = 3695327) B3695327
theorem B10532713 : Blo 1642020 10532713 := bstep (se 2 (by rfl) ⟨3949767, by rfl⟩ : syracuseStep 10532713 = 7899535) B7899535
theorem B4159451 : Blo 1642020 4159451 := bstep (se 1 (by rfl) ⟨3119588, by rfl⟩ : syracuseStep 4159451 = 6239177) B6239177
theorem B2463719 : Blo 1642020 2463719 := bstep (se 1 (by rfl) ⟨1847789, by rfl⟩ : syracuseStep 2463719 = 3695579) B3695579
theorem B3119087 : Blo 1642020 3119087 := bstep (se 1 (by rfl) ⟨2339315, by rfl⟩ : syracuseStep 3119087 = 4678631) B4678631
theorem B4159471 : Blo 1642020 4159471 := bstep (se 1 (by rfl) ⟨3119603, by rfl⟩ : syracuseStep 4159471 = 6239207) B6239207
theorem B2463737 : Blo 1642020 2463737 := bstep (se 2 (by rfl) ⟨923901, by rfl⟩ : syracuseStep 2463737 = 1847803) B1847803
theorem B2463839 : Blo 1642020 2463839 := bstep (se 1 (by rfl) ⟨1847879, by rfl⟩ : syracuseStep 2463839 = 3695759) B3695759
theorem B4159583 : Blo 1642020 4159583 := bstep (se 1 (by rfl) ⟨3119687, by rfl⟩ : syracuseStep 4159583 = 6239375) B6239375
theorem B6240361 : Blo 1642020 6240361 := bstep (se 2 (by rfl) ⟨2340135, by rfl⟩ : syracuseStep 6240361 = 4680271) B4680271
theorem B8321129 : Blo 1642020 8321129 := bstep (se 2 (by rfl) ⟨3120423, by rfl⟩ : syracuseStep 8321129 = 6240847) B6240847
theorem B2078875 : Blo 1642020 2078875 := bstep (se 1 (by rfl) ⟨1559156, by rfl⟩ : syracuseStep 2078875 = 3118313) B3118313
theorem B2463899 : Blo 1642020 2463899 := bstep (se 1 (by rfl) ⟨1847924, by rfl⟩ : syracuseStep 2463899 = 3695849) B3695849
theorem B2463935 : Blo 1642020 2463935 := bstep (se 1 (by rfl) ⟨1847951, by rfl⟩ : syracuseStep 2463935 = 3695903) B3695903
theorem B18725093 : Blo 1642020 18725093 := bstep (se 4 (by rfl) ⟨1755477, by rfl⟩ : syracuseStep 18725093 = 3510955) B3510955
theorem B2463977 : Blo 1642020 2463977 := bstep (se 2 (by rfl) ⟨923991, by rfl⟩ : syracuseStep 2463977 = 1847983) B1847983
theorem B5544179 : Blo 1642020 5544179 := bstep (se 1 (by rfl) ⟨4158134, by rfl⟩ : syracuseStep 5544179 = 8316269) B8316269
theorem B5544233 : Blo 1642020 5544233 := bstep (se 2 (by rfl) ⟨2079087, by rfl⟩ : syracuseStep 5544233 = 4158175) B4158175
theorem B42121619 : Blo 1642020 42121619 := bstep (se 1 (by rfl) ⟨31591214, by rfl⟩ : syracuseStep 42121619 = 63182429) B63182429
theorem B2464283 : Blo 1642020 2464283 := bstep (se 1 (by rfl) ⟨1848212, by rfl⟩ : syracuseStep 2464283 = 3696425) B3696425
theorem B102816289 : Blo 1642020 102816289 := bstep (se 2 (by rfl) ⟨38556108, by rfl⟩ : syracuseStep 102816289 = 77112217) B77112217
theorem B18709055 : Blo 1642020 18709055 := bstep (se 1 (by rfl) ⟨14031791, by rfl⟩ : syracuseStep 18709055 = 28063583) B28063583
theorem B2464361 : Blo 1642020 2464361 := bstep (se 2 (by rfl) ⟨924135, by rfl⟩ : syracuseStep 2464361 = 1848271) B1848271
theorem B5266255 : Blo 1642020 5266255 := bstep (se 1 (by rfl) ⟨3949691, by rfl⟩ : syracuseStep 5266255 = 7899383) B7899383
theorem B2464889 : Blo 1642020 2464889 := bstep (se 2 (by rfl) ⟨924333, by rfl⟩ : syracuseStep 2464889 = 1848667) B1848667
theorem B8314001 : Blo 1642020 8314001 := bstep (se 2 (by rfl) ⟨3117750, by rfl⟩ : syracuseStep 8314001 = 6235501) B6235501
theorem B2464991 : Blo 1642020 2464991 := bstep (se 1 (by rfl) ⟨1848743, by rfl⟩ : syracuseStep 2464991 = 3697487) B3697487
theorem B10525949 : Blo 1642020 10525949 := bstep (se 3 (by rfl) ⟨1973615, by rfl⟩ : syracuseStep 10525949 = 3947231) B3947231
theorem B2465033 : Blo 1642020 2465033 := bstep (se 2 (by rfl) ⟨924387, by rfl⟩ : syracuseStep 2465033 = 1848775) B1848775
theorem B2465135 : Blo 1642020 2465135 := bstep (se 1 (by rfl) ⟨1848851, by rfl⟩ : syracuseStep 2465135 = 3697703) B3697703
theorem B4160879 : Blo 1642020 4160879 := bstep (se 1 (by rfl) ⟨3120659, by rfl⟩ : syracuseStep 4160879 = 6241319) B6241319
theorem B9354689 : Blo 1642020 9354689 := bstep (se 2 (by rfl) ⟨3508008, by rfl⟩ : syracuseStep 9354689 = 7016017) B7016017
theorem B2465255 : Blo 1642020 2465255 := bstep (se 1 (by rfl) ⟨1848941, by rfl⟩ : syracuseStep 2465255 = 3697883) B3697883
theorem B51994133 : Blo 1642020 51994133 := bstep (se 6 (by rfl) ⟨1218612, by rfl⟩ : syracuseStep 51994133 = 2437225) B2437225
theorem B5332559 : Blo 1642020 5332559 := bstep (se 1 (by rfl) ⟨3999419, by rfl⟩ : syracuseStep 5332559 = 7998839) B7998839
theorem B2465387 : Blo 1642020 2465387 := bstep (se 1 (by rfl) ⟨1849040, by rfl⟩ : syracuseStep 2465387 = 3698081) B3698081
theorem B11837137 : Blo 1642020 11837137 := bstep (se 2 (by rfl) ⟨4438926, by rfl⟩ : syracuseStep 11837137 = 8877853) B8877853
theorem B2465513 : Blo 1642020 2465513 := bstep (se 2 (by rfl) ⟨924567, by rfl⟩ : syracuseStep 2465513 = 1849135) B1849135
theorem B4439879 : Blo 1642020 4439879 := bstep (se 1 (by rfl) ⟨3329909, by rfl⟩ : syracuseStep 4439879 = 6659819) B6659819
theorem B5545799 : Blo 1642020 5545799 := bstep (se 1 (by rfl) ⟨4159349, by rfl⟩ : syracuseStep 5545799 = 8318699) B8318699
theorem B2809721 : Blo 1642020 2809721 := bstep (se 2 (by rfl) ⟨1053645, by rfl⟩ : syracuseStep 2809721 = 2107291) B2107291
theorem B2465657 : Blo 1642020 2465657 := bstep (se 2 (by rfl) ⟨924621, by rfl⟩ : syracuseStep 2465657 = 1849243) B1849243
theorem B5545853 : Blo 1642020 5545853 := bstep (se 3 (by rfl) ⟨1039847, by rfl⟩ : syracuseStep 5545853 = 2079695) B2079695
theorem B2465759 : Blo 1642020 2465759 := bstep (se 1 (by rfl) ⟨1849319, by rfl⟩ : syracuseStep 2465759 = 3698639) B3698639
theorem B3694715 : Blo 1642020 3694715 := bstep (se 1 (by rfl) ⟨2771036, by rfl⟩ : syracuseStep 3694715 = 5542073) B5542073
theorem B2465999 : Blo 1642020 2465999 := bstep (se 1 (by rfl) ⟨1849499, by rfl⟩ : syracuseStep 2465999 = 3698999) B3698999
theorem B4997369 : Blo 1642020 4997369 := bstep (se 2 (by rfl) ⟨1874013, by rfl⟩ : syracuseStep 4997369 = 3748027) B3748027
theorem B7110959 : Blo 1642020 7110959 := bstep (se 1 (by rfl) ⟨5333219, by rfl⟩ : syracuseStep 7110959 = 10666439) B10666439
theorem B31564151 : Blo 1642020 31564151 := bstep (se 1 (by rfl) ⟨23673113, by rfl⟩ : syracuseStep 31564151 = 47346227) B47346227
theorem B3694985 : Blo 1642020 3694985 := bstep (se 2 (by rfl) ⟨1385619, by rfl⟩ : syracuseStep 3694985 = 2771239) B2771239
theorem B8315297 : Blo 1642020 8315297 := bstep (se 2 (by rfl) ⟨3118236, by rfl⟩ : syracuseStep 8315297 = 6236473) B6236473
theorem B10814075 : Blo 1642020 10814075 := bstep (se 1 (by rfl) ⟨8110556, by rfl⟩ : syracuseStep 10814075 = 16221113) B16221113
theorem B1999579 : Blo 1642020 1999579 := bstep (se 1 (by rfl) ⟨1499684, by rfl⟩ : syracuseStep 1999579 = 2999369) B2999369
theorem B39969611 : Blo 1642020 39969611 := bstep (se 1 (by rfl) ⟨29977208, by rfl⟩ : syracuseStep 39969611 = 59954417) B59954417
theorem B7021673 : Blo 1642020 7021673 := bstep (se 2 (by rfl) ⟨2633127, by rfl⟩ : syracuseStep 7021673 = 5266255) B5266255
theorem B14419133 : Blo 1642020 14419133 := bstep (se 3 (by rfl) ⟨2703587, by rfl⟩ : syracuseStep 14419133 = 5407175) B5407175
theorem B31581373 : Blo 1642020 31581373 := bstep (se 3 (by rfl) ⟨5921507, by rfl⟩ : syracuseStep 31581373 = 11843015) B11843015
theorem B5547419 : Blo 1642020 5547419 := bstep (se 1 (by rfl) ⟨4160564, by rfl⟩ : syracuseStep 5547419 = 8321129) B8321129
theorem B3696119 : Blo 1642020 3696119 := bstep (se 1 (by rfl) ⟨2772089, by rfl⟩ : syracuseStep 3696119 = 5544179) B5544179
theorem B3696155 : Blo 1642020 3696155 := bstep (se 1 (by rfl) ⟨2772116, by rfl⟩ : syracuseStep 3696155 = 5544233) B5544233
theorem B3507743 : Blo 1642020 3507743 := bstep (se 1 (by rfl) ⟨2630807, by rfl⟩ : syracuseStep 3507743 = 5261615) B5261615
theorem B12470273 : Blo 1642020 12470273 := bstep (se 2 (by rfl) ⟨4676352, by rfl⟩ : syracuseStep 12470273 = 9352705) B9352705
theorem B3557471 : Blo 1642020 3557471 := bstep (se 1 (by rfl) ⟨2668103, by rfl⟩ : syracuseStep 3557471 = 5336207) B5336207
theorem B2771131 : Blo 1642020 2771131 := bstep (se 1 (by rfl) ⟨2078348, by rfl⟩ : syracuseStep 2771131 = 4156697) B4156697
theorem B6236459 : Blo 1642020 6236459 := bstep (se 1 (by rfl) ⟨4677344, by rfl⟩ : syracuseStep 6236459 = 9354689) B9354689
theorem B34662755 : Blo 1642020 34662755 := bstep (se 1 (by rfl) ⟨25997066, by rfl⟩ : syracuseStep 34662755 = 51994133) B51994133
theorem B2771327 : Blo 1642020 2771327 := bstep (se 1 (by rfl) ⟨2078495, by rfl⟩ : syracuseStep 2771327 = 4156991) B4156991
theorem B14043617 : Blo 1642020 14043617 := bstep (se 2 (by rfl) ⟨5266356, by rfl⟩ : syracuseStep 14043617 = 10532713) B10532713
theorem B3697145 : Blo 1642020 3697145 := bstep (se 2 (by rfl) ⟨1386429, by rfl⟩ : syracuseStep 3697145 = 2772859) B2772859
theorem B2959919 : Blo 1642020 2959919 := bstep (se 1 (by rfl) ⟨2219939, by rfl⟩ : syracuseStep 2959919 = 4439879) B4439879
theorem B3697199 : Blo 1642020 3697199 := bstep (se 1 (by rfl) ⟨2772899, by rfl⟩ : syracuseStep 3697199 = 5545799) B5545799
theorem B3697235 : Blo 1642020 3697235 := bstep (se 1 (by rfl) ⟨2772926, by rfl⟩ : syracuseStep 3697235 = 5545853) B5545853
theorem B8317565 : Blo 1642020 8317565 := bstep (se 3 (by rfl) ⟨1559543, by rfl⟩ : syracuseStep 8317565 = 3119087) B3119087
theorem B4680317 : Blo 1642020 4680317 := bstep (se 3 (by rfl) ⟨877559, by rfl⟩ : syracuseStep 4680317 = 1755119) B1755119
theorem B3697415 : Blo 1642020 3697415 := bstep (se 1 (by rfl) ⟨2773061, by rfl⟩ : syracuseStep 3697415 = 5546123) B5546123
theorem B31566611 : Blo 1642020 31566611 := bstep (se 1 (by rfl) ⟨23674958, by rfl⟩ : syracuseStep 31566611 = 47349917) B47349917
theorem B4213595 : Blo 1642020 4213595 := bstep (se 1 (by rfl) ⟨3160196, by rfl⟩ : syracuseStep 4213595 = 6320393) B6320393
theorem B4442971 : Blo 1642020 4442971 := bstep (se 1 (by rfl) ⟨3332228, by rfl⟩ : syracuseStep 4442971 = 6664457) B6664457
theorem B2771833 : Blo 1642020 2771833 := bstep (se 2 (by rfl) ⟨1039437, by rfl⟩ : syracuseStep 2771833 = 2078875) B2078875
theorem B3746767 : Blo 1642020 3746767 := bstep (se 1 (by rfl) ⟨2810075, by rfl⟩ : syracuseStep 3746767 = 5620151) B5620151
theorem B3697631 : Blo 1642020 3697631 := bstep (se 1 (by rfl) ⟨2773223, by rfl⟩ : syracuseStep 3697631 = 5546447) B5546447
theorem B3697847 : Blo 1642020 3697847 := bstep (se 1 (by rfl) ⟨2773385, by rfl⟩ : syracuseStep 3697847 = 5546771) B5546771
theorem B137088385 : Blo 1642020 137088385 := bstep (se 2 (by rfl) ⟨51408144, by rfl⟩ : syracuseStep 137088385 = 102816289) B102816289
theorem B8318375 : Blo 1642020 8318375 := bstep (se 1 (by rfl) ⟨6238781, by rfl⟩ : syracuseStep 8318375 = 12477563) B12477563
theorem B12479993 : Blo 1642020 12479993 := bstep (se 2 (by rfl) ⟨4679997, by rfl⟩ : syracuseStep 12479993 = 9359995) B9359995
theorem B1642087 : Blo 1642020 1642087 := bstep (se 1 (by rfl) ⟨1231565, by rfl⟩ : syracuseStep 1642087 = 2463131) B2463131
theorem B4157153 : Blo 1642020 4157153 := bstep (se 2 (by rfl) ⟨1558932, by rfl⟩ : syracuseStep 4157153 = 3117865) B3117865
theorem B3698423 : Blo 1642020 3698423 := bstep (se 1 (by rfl) ⟨2773817, by rfl⟩ : syracuseStep 3698423 = 5547635) B5547635
theorem B1642235 : Blo 1642020 1642235 := bstep (se 1 (by rfl) ⟨1231676, by rfl⟩ : syracuseStep 1642235 = 2463353) B2463353
theorem B1642303 : Blo 1642020 1642303 := bstep (se 1 (by rfl) ⟨1231727, by rfl⟩ : syracuseStep 1642303 = 2463455) B2463455
theorem B3698495 : Blo 1642020 3698495 := bstep (se 1 (by rfl) ⟨2773871, by rfl⟩ : syracuseStep 3698495 = 5547743) B5547743
theorem B1642367 : Blo 1642020 1642367 := bstep (se 1 (by rfl) ⟨1231775, by rfl⟩ : syracuseStep 1642367 = 2463551) B2463551
theorem B3698603 : Blo 1642020 3698603 := bstep (se 1 (by rfl) ⟨2773952, by rfl⟩ : syracuseStep 3698603 = 5547905) B5547905
theorem B2772967 : Blo 1642020 2772967 := bstep (se 1 (by rfl) ⟨2079725, by rfl⟩ : syracuseStep 2772967 = 4159451) B4159451
theorem B1642479 : Blo 1642020 1642479 := bstep (se 1 (by rfl) ⟨1231859, by rfl⟩ : syracuseStep 1642479 = 2463719) B2463719
theorem B1642491 : Blo 1642020 1642491 := bstep (se 1 (by rfl) ⟨1231868, by rfl⟩ : syracuseStep 1642491 = 2463737) B2463737
theorem B1642559 : Blo 1642020 1642559 := bstep (se 1 (by rfl) ⟨1231919, by rfl⟩ : syracuseStep 1642559 = 2463839) B2463839
theorem B2773055 : Blo 1642020 2773055 := bstep (se 1 (by rfl) ⟨2079791, by rfl⟩ : syracuseStep 2773055 = 4159583) B4159583
theorem B1642599 : Blo 1642020 1642599 := bstep (se 1 (by rfl) ⟨1231949, by rfl⟩ : syracuseStep 1642599 = 2463899) B2463899
theorem B1642623 : Blo 1642020 1642623 := bstep (se 1 (by rfl) ⟨1231967, by rfl⟩ : syracuseStep 1642623 = 2463935) B2463935
theorem B1642651 : Blo 1642020 1642651 := bstep (se 1 (by rfl) ⟨1231988, by rfl⟩ : syracuseStep 1642651 = 2463977) B2463977
theorem B3698963 : Blo 1642020 3698963 := bstep (se 1 (by rfl) ⟨2774222, by rfl⟩ : syracuseStep 3698963 = 5548445) B5548445
theorem B1642855 : Blo 1642020 1642855 := bstep (se 1 (by rfl) ⟨1232141, by rfl⟩ : syracuseStep 1642855 = 2464283) B2464283
theorem B12472703 : Blo 1642020 12472703 := bstep (se 1 (by rfl) ⟨9354527, by rfl⟩ : syracuseStep 12472703 = 18709055) B18709055
theorem B1642907 : Blo 1642020 1642907 := bstep (se 1 (by rfl) ⟨1232180, by rfl⟩ : syracuseStep 1642907 = 2464361) B2464361
theorem B28471961 : Blo 1642020 28471961 := bstep (se 2 (by rfl) ⟨10676985, by rfl⟩ : syracuseStep 28471961 = 21353971) B21353971
theorem B1643259 : Blo 1642020 1643259 := bstep (se 1 (by rfl) ⟨1232444, by rfl⟩ : syracuseStep 1643259 = 2464889) B2464889
theorem B5542667 : Blo 1642020 5542667 := bstep (se 1 (by rfl) ⟨4157000, by rfl⟩ : syracuseStep 5542667 = 8314001) B8314001
theorem B1848127 : Blo 1642020 1848127 := bstep (se 1 (by rfl) ⟨1386095, by rfl⟩ : syracuseStep 1848127 = 2772191) B2772191
theorem B1643327 : Blo 1642020 1643327 := bstep (se 1 (by rfl) ⟨1232495, by rfl⟩ : syracuseStep 1643327 = 2464991) B2464991
theorem B7017299 : Blo 1642020 7017299 := bstep (se 1 (by rfl) ⟨5262974, by rfl⟩ : syracuseStep 7017299 = 10525949) B10525949
theorem B1643355 : Blo 1642020 1643355 := bstep (se 1 (by rfl) ⟨1232516, by rfl⟩ : syracuseStep 1643355 = 2465033) B2465033
theorem B18969491 : Blo 1642020 18969491 := bstep (se 1 (by rfl) ⟨14227118, by rfl⟩ : syracuseStep 18969491 = 28454237) B28454237
theorem B1643423 : Blo 1642020 1643423 := bstep (se 1 (by rfl) ⟨1232567, by rfl⟩ : syracuseStep 1643423 = 2465135) B2465135
theorem B2773919 : Blo 1642020 2773919 := bstep (se 1 (by rfl) ⟨2080439, by rfl⟩ : syracuseStep 2773919 = 4160879) B4160879
theorem B12481451 : Blo 1642020 12481451 := bstep (se 1 (by rfl) ⟨9361088, by rfl⟩ : syracuseStep 12481451 = 18722177) B18722177
theorem B15782849 : Blo 1642020 15782849 := bstep (se 2 (by rfl) ⟨5918568, by rfl⟩ : syracuseStep 15782849 = 11837137) B11837137
theorem B1643503 : Blo 1642020 1643503 := bstep (se 1 (by rfl) ⟨1232627, by rfl⟩ : syracuseStep 1643503 = 2465255) B2465255
theorem B5542937 : Blo 1642020 5542937 := bstep (se 2 (by rfl) ⟨2078601, by rfl⟩ : syracuseStep 5542937 = 4157203) B4157203
theorem B1643591 : Blo 1642020 1643591 := bstep (se 1 (by rfl) ⟨1232693, by rfl⟩ : syracuseStep 1643591 = 2465387) B2465387
theorem B1848415 : Blo 1642020 1848415 := bstep (se 1 (by rfl) ⟨1386311, by rfl⟩ : syracuseStep 1848415 = 2772623) B2772623
theorem B1643675 : Blo 1642020 1643675 := bstep (se 1 (by rfl) ⟨1232756, by rfl⟩ : syracuseStep 1643675 = 2465513) B2465513
theorem B1873147 : Blo 1642020 1873147 := bstep (se 1 (by rfl) ⟨1404860, by rfl⟩ : syracuseStep 1873147 = 2809721) B2809721
theorem B1643771 : Blo 1642020 1643771 := bstep (se 1 (by rfl) ⟨1232828, by rfl⟩ : syracuseStep 1643771 = 2465657) B2465657
theorem B1643839 : Blo 1642020 1643839 := bstep (se 1 (by rfl) ⟨1232879, by rfl⟩ : syracuseStep 1643839 = 2465759) B2465759
theorem B8320481 : Blo 1642020 8320481 := bstep (se 2 (by rfl) ⟨3120180, by rfl⟩ : syracuseStep 8320481 = 6240361) B6240361
theorem B1644007 : Blo 1642020 1644007 := bstep (se 1 (by rfl) ⟨1233005, by rfl⟩ : syracuseStep 1644007 = 2466011) B2466011
theorem B2463215 : Blo 1642020 2463215 := bstep (se 1 (by rfl) ⟨1847411, by rfl⟩ : syracuseStep 2463215 = 3694823) B3694823
theorem B1644015 : Blo 1642020 1644015 := bstep (se 1 (by rfl) ⟨1233011, by rfl⟩ : syracuseStep 1644015 = 2466023) B2466023
theorem B13326059 : Blo 1642020 13326059 := bstep (se 1 (by rfl) ⟨9994544, by rfl⟩ : syracuseStep 13326059 = 19989089) B19989089
theorem B86562553 : Blo 1642020 86562553 := bstep (se 2 (by rfl) ⟨32460957, by rfl⟩ : syracuseStep 86562553 = 64921915) B64921915
theorem B2463611 : Blo 1642020 2463611 := bstep (se 1 (by rfl) ⟨1847708, by rfl⟩ : syracuseStep 2463611 = 3695417) B3695417
theorem B2463647 : Blo 1642020 2463647 := bstep (se 1 (by rfl) ⟨1847735, by rfl⟩ : syracuseStep 2463647 = 3695471) B3695471
theorem B23680957 : Blo 1642020 23680957 := bstep (se 3 (by rfl) ⟨4440179, by rfl⟩ : syracuseStep 23680957 = 8880359) B8880359
theorem B2463881 : Blo 1642020 2463881 := bstep (se 2 (by rfl) ⟨923955, by rfl⟩ : syracuseStep 2463881 = 1847911) B1847911
theorem B3119323 : Blo 1642020 3119323 := bstep (se 1 (by rfl) ⟨2339492, by rfl⟩ : syracuseStep 3119323 = 4678985) B4678985
theorem B2464031 : Blo 1642020 2464031 := bstep (se 1 (by rfl) ⟨1848023, by rfl⟩ : syracuseStep 2464031 = 3696047) B3696047
theorem B5544287 : Blo 1642020 5544287 := bstep (se 1 (by rfl) ⟨4158215, by rfl⟩ : syracuseStep 5544287 = 8316431) B8316431
theorem B22485367 : Blo 1642020 22485367 := bstep (se 1 (by rfl) ⟨16864025, by rfl⟩ : syracuseStep 22485367 = 33728051) B33728051
theorem B6240635 : Blo 1642020 6240635 := bstep (se 1 (by rfl) ⟨4680476, by rfl⟩ : syracuseStep 6240635 = 9360953) B9360953
theorem B4995485 : Blo 1642020 4995485 := bstep (se 3 (by rfl) ⟨936653, by rfl⟩ : syracuseStep 4995485 = 1873307) B1873307
theorem B5544449 : Blo 1642020 5544449 := bstep (se 2 (by rfl) ⟨2079168, by rfl⟩ : syracuseStep 5544449 = 4158337) B4158337
theorem B5265947 : Blo 1642020 5265947 := bstep (se 1 (by rfl) ⟨3949460, by rfl⟩ : syracuseStep 5265947 = 7898921) B7898921
theorem B9485021 : Blo 1642020 9485021 := bstep (se 3 (by rfl) ⟨1778441, by rfl⟩ : syracuseStep 9485021 = 3556883) B3556883
theorem B12483395 : Blo 1642020 12483395 := bstep (se 1 (by rfl) ⟨9362546, by rfl⟩ : syracuseStep 12483395 = 18725093) B18725093
theorem B2464583 : Blo 1642020 2464583 := bstep (se 1 (by rfl) ⟨1848437, by rfl⟩ : syracuseStep 2464583 = 3696875) B3696875
theorem B5544827 : Blo 1642020 5544827 := bstep (se 1 (by rfl) ⟨4158620, by rfl⟩ : syracuseStep 5544827 = 8317241) B8317241
theorem B14220157 : Blo 1642020 14220157 := bstep (se 3 (by rfl) ⟨2666279, by rfl⟩ : syracuseStep 14220157 = 5332559) B5332559
theorem B28081079 : Blo 1642020 28081079 := bstep (se 1 (by rfl) ⟨21060809, by rfl⟩ : syracuseStep 28081079 = 42121619) B42121619
theorem B5545259 : Blo 1642020 5545259 := bstep (se 1 (by rfl) ⟨4158944, by rfl⟩ : syracuseStep 5545259 = 8317889) B8317889
theorem B5545529 : Blo 1642020 5545529 := bstep (se 2 (by rfl) ⟨2079573, by rfl⟩ : syracuseStep 5545529 = 4159147) B4159147
theorem B2465447 : Blo 1642020 2465447 := bstep (se 1 (by rfl) ⟨1849085, by rfl⟩ : syracuseStep 2465447 = 3698171) B3698171
theorem B5545691 : Blo 1642020 5545691 := bstep (se 1 (by rfl) ⟨4159268, by rfl⟩ : syracuseStep 5545691 = 8318537) B8318537
theorem B19996379 : Blo 1642020 19996379 := bstep (se 1 (by rfl) ⟨14997284, by rfl⟩ : syracuseStep 19996379 = 29994569) B29994569
theorem B2465567 : Blo 1642020 2465567 := bstep (se 1 (by rfl) ⟨1849175, by rfl⟩ : syracuseStep 2465567 = 3698351) B3698351
theorem B5545961 : Blo 1642020 5545961 := bstep (se 2 (by rfl) ⟨2079735, by rfl⟩ : syracuseStep 5545961 = 4159471) B4159471
theorem B2924552213 : Blo 1642020 2924552213 := bstep (se 6 (by rfl) ⟨68544192, by rfl⟩ : syracuseStep 2924552213 = 137088385) B137088385
theorem B2465975 : Blo 1642020 2465975 := bstep (se 1 (by rfl) ⟨1849481, by rfl⟩ : syracuseStep 2465975 = 3698963) B3698963
theorem B3694841 : Blo 1642020 3694841 := bstep (se 2 (by rfl) ⟨1385565, by rfl⟩ : syracuseStep 3694841 = 2771131) B2771131
theorem B8315135 : Blo 1642020 8315135 := bstep (se 1 (by rfl) ⟨6236351, by rfl⟩ : syracuseStep 8315135 = 12472703) B12472703
theorem B7209383 : Blo 1642020 7209383 := bstep (se 1 (by rfl) ⟨5407037, by rfl⟩ : syracuseStep 7209383 = 10814075) B10814075
theorem B18981307 : Blo 1642020 18981307 := bstep (se 1 (by rfl) ⟨14235980, by rfl⟩ : syracuseStep 18981307 = 28471961) B28471961
theorem B75850229 : Blo 1642020 75850229 := bstep (se 5 (by rfl) ⟨3555479, by rfl⟩ : syracuseStep 75850229 = 7110959) B7110959
theorem B3695111 : Blo 1642020 3695111 := bstep (se 1 (by rfl) ⟨2771333, by rfl⟩ : syracuseStep 3695111 = 5542667) B5542667
theorem B4678199 : Blo 1642020 4678199 := bstep (se 1 (by rfl) ⟨3508649, by rfl⟩ : syracuseStep 4678199 = 7017299) B7017299
theorem B3695291 : Blo 1642020 3695291 := bstep (se 1 (by rfl) ⟨2771468, by rfl⟩ : syracuseStep 3695291 = 5542937) B5542937
theorem B5546987 : Blo 1642020 5546987 := bstep (se 1 (by rfl) ⟨4160240, by rfl⟩ : syracuseStep 5546987 = 8320481) B8320481
theorem B37946357 : Blo 1642020 37946357 := bstep (se 5 (by rfl) ⟨1778735, by rfl⟩ : syracuseStep 37946357 = 3557471) B3557471
theorem B5923961 : Blo 1642020 5923961 := bstep (se 2 (by rfl) ⟨2221485, by rfl⟩ : syracuseStep 5923961 = 4442971) B4442971
theorem B3695777 : Blo 1642020 3695777 := bstep (se 2 (by rfl) ⟨1385916, by rfl⟩ : syracuseStep 3695777 = 2771833) B2771833
theorem B3696191 : Blo 1642020 3696191 := bstep (se 1 (by rfl) ⟨2772143, by rfl⟩ : syracuseStep 3696191 = 5544287) B5544287
theorem B42108497 : Blo 1642020 42108497 := bstep (se 2 (by rfl) ⟨15790686, by rfl⟩ : syracuseStep 42108497 = 31581373) B31581373
theorem B3696299 : Blo 1642020 3696299 := bstep (se 1 (by rfl) ⟨2772224, by rfl⟩ : syracuseStep 3696299 = 5544449) B5544449
theorem B3696551 : Blo 1642020 3696551 := bstep (se 1 (by rfl) ⟨2772413, by rfl⟩ : syracuseStep 3696551 = 5544827) B5544827
theorem B18720719 : Blo 1642020 18720719 := bstep (se 1 (by rfl) ⟨14040539, by rfl⟩ : syracuseStep 18720719 = 28081079) B28081079
theorem B3696839 : Blo 1642020 3696839 := bstep (se 1 (by rfl) ⟨2772629, by rfl⟩ : syracuseStep 3696839 = 5545259) B5545259
theorem B3697019 : Blo 1642020 3697019 := bstep (se 1 (by rfl) ⟨2772764, by rfl⟩ : syracuseStep 3697019 = 5545529) B5545529
theorem B3697127 : Blo 1642020 3697127 := bstep (se 1 (by rfl) ⟨2772845, by rfl⟩ : syracuseStep 3697127 = 5545691) B5545691
theorem B13330919 : Blo 1642020 13330919 := bstep (se 1 (by rfl) ⟨9998189, by rfl⟩ : syracuseStep 13330919 = 19996379) B19996379
theorem B2771435 : Blo 1642020 2771435 := bstep (se 1 (by rfl) ⟨2078576, by rfl⟩ : syracuseStep 2771435 = 4157153) B4157153
theorem B31574609 : Blo 1642020 31574609 := bstep (se 2 (by rfl) ⟨11840478, by rfl⟩ : syracuseStep 31574609 = 23680957) B23680957
theorem B3697289 : Blo 1642020 3697289 := bstep (se 2 (by rfl) ⟨1386483, by rfl⟩ : syracuseStep 3697289 = 2772967) B2772967
theorem B3697307 : Blo 1642020 3697307 := bstep (se 1 (by rfl) ⟨2772980, by rfl⟩ : syracuseStep 3697307 = 5545961) B5545961
theorem B10521899 : Blo 1642020 10521899 := bstep (se 1 (by rfl) ⟨7891424, by rfl⟩ : syracuseStep 10521899 = 15782849) B15782849
theorem B4681115 : Blo 1642020 4681115 := bstep (se 1 (by rfl) ⟨3510836, by rfl⟩ : syracuseStep 4681115 = 7021673) B7021673
theorem B9612755 : Blo 1642020 9612755 := bstep (se 1 (by rfl) ⟨7209566, by rfl⟩ : syracuseStep 9612755 = 14419133) B14419133
theorem B3698279 : Blo 1642020 3698279 := bstep (se 1 (by rfl) ⟨2773709, by rfl⟩ : syracuseStep 3698279 = 5547419) B5547419
theorem B2666105 : Blo 1642020 2666105 := bstep (se 2 (by rfl) ⟨999789, by rfl⟩ : syracuseStep 2666105 = 1999579) B1999579
theorem B1642143 : Blo 1642020 1642143 := bstep (se 1 (by rfl) ⟨1231607, by rfl⟩ : syracuseStep 1642143 = 2463215) B2463215
theorem B8884039 : Blo 1642020 8884039 := bstep (se 1 (by rfl) ⟨6663029, by rfl⟩ : syracuseStep 8884039 = 13326059) B13326059
theorem B18960209 : Blo 1642020 18960209 := bstep (se 2 (by rfl) ⟨7110078, by rfl⟩ : syracuseStep 18960209 = 14220157) B14220157
theorem B1642407 : Blo 1642020 1642407 := bstep (se 1 (by rfl) ⟨1231805, by rfl⟩ : syracuseStep 1642407 = 2463611) B2463611
theorem B1642431 : Blo 1642020 1642431 := bstep (se 1 (by rfl) ⟨1231823, by rfl⟩ : syracuseStep 1642431 = 2463647) B2463647
theorem B1642587 : Blo 1642020 1642587 := bstep (se 1 (by rfl) ⟨1231940, by rfl⟩ : syracuseStep 1642587 = 2463881) B2463881
theorem B1642687 : Blo 1642020 1642687 := bstep (se 1 (by rfl) ⟨1232015, by rfl⟩ : syracuseStep 1642687 = 2464031) B2464031
theorem B4157639 : Blo 1642020 4157639 := bstep (se 1 (by rfl) ⟨3118229, by rfl⟩ : syracuseStep 4157639 = 6236459) B6236459
theorem B1847551 : Blo 1642020 1847551 := bstep (se 1 (by rfl) ⟨1385663, by rfl⟩ : syracuseStep 1847551 = 2771327) B2771327
theorem B3330323 : Blo 1642020 3330323 := bstep (se 1 (by rfl) ⟨2497742, by rfl⟩ : syracuseStep 3330323 = 4995485) B4995485
theorem B3510631 : Blo 1642020 3510631 := bstep (se 1 (by rfl) ⟨2632973, by rfl⟩ : syracuseStep 3510631 = 5265947) B5265947
theorem B1643055 : Blo 1642020 1643055 := bstep (se 1 (by rfl) ⟨1232291, by rfl⟩ : syracuseStep 1643055 = 2464583) B2464583
theorem B8319995 : Blo 1642020 8319995 := bstep (se 1 (by rfl) ⟨6239996, by rfl⟩ : syracuseStep 8319995 = 12479993) B12479993
theorem B1643631 : Blo 1642020 1643631 := bstep (se 1 (by rfl) ⟨1232723, by rfl⟩ : syracuseStep 1643631 = 2465447) B2465447
theorem B1643711 : Blo 1642020 1643711 := bstep (se 1 (by rfl) ⟨1232783, by rfl⟩ : syracuseStep 1643711 = 2465567) B2465567
theorem B1848703 : Blo 1642020 1848703 := bstep (se 1 (by rfl) ⟨1386527, by rfl⟩ : syracuseStep 1848703 = 2773055) B2773055
theorem B2463143 : Blo 1642020 2463143 := bstep (se 1 (by rfl) ⟨1847357, by rfl⟩ : syracuseStep 2463143 = 3694715) B3694715
theorem B1643999 : Blo 1642020 1643999 := bstep (se 1 (by rfl) ⟨1232999, by rfl⟩ : syracuseStep 1643999 = 2465999) B2465999
theorem B3331579 : Blo 1642020 3331579 := bstep (se 1 (by rfl) ⟨2498684, by rfl⟩ : syracuseStep 3331579 = 4997369) B4997369
theorem B21042767 : Blo 1642020 21042767 := bstep (se 1 (by rfl) ⟨15782075, by rfl⟩ : syracuseStep 21042767 = 31564151) B31564151
theorem B2463323 : Blo 1642020 2463323 := bstep (se 1 (by rfl) ⟨1847492, by rfl⟩ : syracuseStep 2463323 = 3694985) B3694985
theorem B5543531 : Blo 1642020 5543531 := bstep (se 1 (by rfl) ⟨4157648, by rfl⟩ : syracuseStep 5543531 = 8315297) B8315297
theorem B4159097 : Blo 1642020 4159097 := bstep (se 2 (by rfl) ⟨1559661, by rfl⟩ : syracuseStep 4159097 = 3119323) B3119323
theorem B26646407 : Blo 1642020 26646407 := bstep (se 1 (by rfl) ⟨19984805, by rfl⟩ : syracuseStep 26646407 = 39969611) B39969611
theorem B1849279 : Blo 1642020 1849279 := bstep (se 1 (by rfl) ⟨1386959, by rfl⟩ : syracuseStep 1849279 = 2773919) B2773919
theorem B8320967 : Blo 1642020 8320967 := bstep (se 1 (by rfl) ⟨6240725, by rfl⟩ : syracuseStep 8320967 = 12481451) B12481451
theorem B2464079 : Blo 1642020 2464079 := bstep (se 1 (by rfl) ⟨1848059, by rfl⟩ : syracuseStep 2464079 = 3696119) B3696119
theorem B2464103 : Blo 1642020 2464103 := bstep (se 1 (by rfl) ⟨1848077, by rfl⟩ : syracuseStep 2464103 = 3696155) B3696155
theorem B2464169 : Blo 1642020 2464169 := bstep (se 2 (by rfl) ⟨924063, by rfl⟩ : syracuseStep 2464169 = 1848127) B1848127
theorem B4995689 : Blo 1642020 4995689 := bstep (se 2 (by rfl) ⟨1873383, by rfl⟩ : syracuseStep 4995689 = 3746767) B3746767
theorem B8313515 : Blo 1642020 8313515 := bstep (se 1 (by rfl) ⟨6235136, by rfl⟩ : syracuseStep 8313515 = 12470273) B12470273
theorem B9353981 : Blo 1642020 9353981 := bstep (se 3 (by rfl) ⟨1753871, by rfl⟩ : syracuseStep 9353981 = 3507743) B3507743
theorem B2464553 : Blo 1642020 2464553 := bstep (se 2 (by rfl) ⟨924207, by rfl⟩ : syracuseStep 2464553 = 1848415) B1848415
theorem B23108503 : Blo 1642020 23108503 := bstep (se 1 (by rfl) ⟨17331377, by rfl⟩ : syracuseStep 23108503 = 34662755) B34662755
theorem B4160423 : Blo 1642020 4160423 := bstep (se 1 (by rfl) ⟨3120317, by rfl⟩ : syracuseStep 4160423 = 6240635) B6240635
theorem B9362411 : Blo 1642020 9362411 := bstep (se 1 (by rfl) ⟨7021808, by rfl⟩ : syracuseStep 9362411 = 14043617) B14043617
theorem B2497529 : Blo 1642020 2497529 := bstep (se 2 (by rfl) ⟨936573, by rfl⟩ : syracuseStep 2497529 = 1873147) B1873147
theorem B2464763 : Blo 1642020 2464763 := bstep (se 1 (by rfl) ⟨1848572, by rfl⟩ : syracuseStep 2464763 = 3697145) B3697145
theorem B1973279 : Blo 1642020 1973279 := bstep (se 1 (by rfl) ⟨1479959, by rfl⟩ : syracuseStep 1973279 = 2959919) B2959919
theorem B2464799 : Blo 1642020 2464799 := bstep (se 1 (by rfl) ⟨1848599, by rfl⟩ : syracuseStep 2464799 = 3697199) B3697199
theorem B2464823 : Blo 1642020 2464823 := bstep (se 1 (by rfl) ⟨1848617, by rfl⟩ : syracuseStep 2464823 = 3697235) B3697235
theorem B5545043 : Blo 1642020 5545043 := bstep (se 1 (by rfl) ⟨4158782, by rfl⟩ : syracuseStep 5545043 = 8317565) B8317565
theorem B3120211 : Blo 1642020 3120211 := bstep (se 1 (by rfl) ⟨2340158, by rfl⟩ : syracuseStep 3120211 = 4680317) B4680317
theorem B6323347 : Blo 1642020 6323347 := bstep (se 1 (by rfl) ⟨4742510, by rfl⟩ : syracuseStep 6323347 = 9485021) B9485021
theorem B2464943 : Blo 1642020 2464943 := bstep (se 1 (by rfl) ⟨1848707, by rfl⟩ : syracuseStep 2464943 = 3697415) B3697415
theorem B21044407 : Blo 1642020 21044407 := bstep (se 1 (by rfl) ⟨15783305, by rfl⟩ : syracuseStep 21044407 = 31566611) B31566611
theorem B8322263 : Blo 1642020 8322263 := bstep (se 1 (by rfl) ⟨6241697, by rfl⟩ : syracuseStep 8322263 = 12483395) B12483395
theorem B2809063 : Blo 1642020 2809063 := bstep (se 1 (by rfl) ⟨2106797, by rfl⟩ : syracuseStep 2809063 = 4213595) B4213595
theorem B119921957 : Blo 1642020 119921957 := bstep (se 4 (by rfl) ⟨11242683, by rfl⟩ : syracuseStep 119921957 = 22485367) B22485367
theorem B2465087 : Blo 1642020 2465087 := bstep (se 1 (by rfl) ⟨1848815, by rfl⟩ : syracuseStep 2465087 = 3697631) B3697631
theorem B2465231 : Blo 1642020 2465231 := bstep (se 1 (by rfl) ⟨1848923, by rfl⟩ : syracuseStep 2465231 = 3697847) B3697847
theorem B5545583 : Blo 1642020 5545583 := bstep (se 1 (by rfl) ⟨4159187, by rfl⟩ : syracuseStep 5545583 = 8318375) B8318375
theorem B115416737 : Blo 1642020 115416737 := bstep (se 2 (by rfl) ⟨43281276, by rfl⟩ : syracuseStep 115416737 = 86562553) B86562553
theorem B50585309 : Blo 1642020 50585309 := bstep (se 3 (by rfl) ⟨9484745, by rfl⟩ : syracuseStep 50585309 = 18969491) B18969491
theorem B2465615 : Blo 1642020 2465615 := bstep (se 1 (by rfl) ⟨1849211, by rfl⟩ : syracuseStep 2465615 = 3698423) B3698423
theorem B2465663 : Blo 1642020 2465663 := bstep (se 1 (by rfl) ⟨1849247, by rfl⟩ : syracuseStep 2465663 = 3698495) B3698495
theorem B2465735 : Blo 1642020 2465735 := bstep (se 1 (by rfl) ⟨1849301, by rfl⟩ : syracuseStep 2465735 = 3698603) B3698603
theorem B2220215 : Blo 1642020 2220215 := bstep (se 1 (by rfl) ⟨1665161, by rfl⟩ : syracuseStep 2220215 = 3330323) B3330323
theorem B25297571 : Blo 1642020 25297571 := bstep (se 1 (by rfl) ⟨18973178, by rfl⟩ : syracuseStep 25297571 = 37946357) B37946357
theorem B5546663 : Blo 1642020 5546663 := bstep (se 1 (by rfl) ⟨4159997, by rfl⟩ : syracuseStep 5546663 = 8319995) B8319995
theorem B3949307 : Blo 1642020 3949307 := bstep (se 1 (by rfl) ⟨2961980, by rfl⟩ : syracuseStep 3949307 = 5923961) B5923961
theorem B3695687 : Blo 1642020 3695687 := bstep (se 1 (by rfl) ⟨2771765, by rfl⟩ : syracuseStep 3695687 = 5543531) B5543531
theorem B30811337 : Blo 1642020 30811337 := bstep (se 2 (by rfl) ⟨11554251, by rfl⟩ : syracuseStep 30811337 = 23108503) B23108503
theorem B5547311 : Blo 1642020 5547311 := bstep (se 1 (by rfl) ⟨4160483, by rfl⟩ : syracuseStep 5547311 = 8320967) B8320967
theorem B8431129 : Blo 1642020 8431129 := bstep (se 2 (by rfl) ⟨3161673, by rfl⟩ : syracuseStep 8431129 = 6323347) B6323347
theorem B28059209 : Blo 1642020 28059209 := bstep (se 2 (by rfl) ⟨10522203, by rfl⟩ : syracuseStep 28059209 = 21044407) B21044407
theorem B13321837 : Blo 1642020 13321837 := bstep (se 3 (by rfl) ⟨2497844, by rfl⟩ : syracuseStep 13321837 = 4995689) B4995689
theorem B6235987 : Blo 1642020 6235987 := bstep (se 1 (by rfl) ⟨4676990, by rfl⟩ : syracuseStep 6235987 = 9353981) B9353981
theorem B4442105 : Blo 1642020 4442105 := bstep (se 2 (by rfl) ⟨1665789, by rfl⟩ : syracuseStep 4442105 = 3331579) B3331579
theorem B1665019 : Blo 1642020 1665019 := bstep (se 1 (by rfl) ⟨1248764, by rfl⟩ : syracuseStep 1665019 = 2497529) B2497529
theorem B3696695 : Blo 1642020 3696695 := bstep (se 1 (by rfl) ⟨2772521, by rfl⟩ : syracuseStep 3696695 = 5545043) B5545043
theorem B5548175 : Blo 1642020 5548175 := bstep (se 1 (by rfl) ⟨4161131, by rfl⟩ : syracuseStep 5548175 = 8322263) B8322263
theorem B79947971 : Blo 1642020 79947971 := bstep (se 1 (by rfl) ⟨59960978, by rfl⟩ : syracuseStep 79947971 = 119921957) B119921957
theorem B7014599 : Blo 1642020 7014599 := bstep (se 1 (by rfl) ⟨5260949, by rfl⟩ : syracuseStep 7014599 = 10521899) B10521899
theorem B6408503 : Blo 1642020 6408503 := bstep (se 1 (by rfl) ⟨4806377, by rfl⟩ : syracuseStep 6408503 = 9612755) B9612755
theorem B3697055 : Blo 1642020 3697055 := bstep (se 1 (by rfl) ⟨2772791, by rfl⟩ : syracuseStep 3697055 = 5545583) B5545583
theorem B5262077 : Blo 1642020 5262077 := bstep (se 3 (by rfl) ⟨986639, by rfl⟩ : syracuseStep 5262077 = 1973279) B1973279
theorem B2771759 : Blo 1642020 2771759 := bstep (se 1 (by rfl) ⟨2078819, by rfl⟩ : syracuseStep 2771759 = 4157639) B4157639
theorem B4680841 : Blo 1642020 4680841 := bstep (se 2 (by rfl) ⟨1755315, by rfl⟩ : syracuseStep 4680841 = 3510631) B3510631
theorem B25308409 : Blo 1642020 25308409 := bstep (se 2 (by rfl) ⟨9490653, by rfl⟩ : syracuseStep 25308409 = 18981307) B18981307
theorem B3697991 : Blo 1642020 3697991 := bstep (se 1 (by rfl) ⟨2773493, by rfl⟩ : syracuseStep 3697991 = 5546987) B5546987
theorem B1642095 : Blo 1642020 1642095 := bstep (se 1 (by rfl) ⟨1231571, by rfl⟩ : syracuseStep 1642095 = 2463143) B2463143
theorem B14028511 : Blo 1642020 14028511 := bstep (se 1 (by rfl) ⟨10521383, by rfl⟩ : syracuseStep 14028511 = 21042767) B21042767
theorem B1642215 : Blo 1642020 1642215 := bstep (se 1 (by rfl) ⟨1231661, by rfl⟩ : syracuseStep 1642215 = 2463323) B2463323
theorem B2772731 : Blo 1642020 2772731 := bstep (se 1 (by rfl) ⟨2079548, by rfl⟩ : syracuseStep 2772731 = 4159097) B4159097
theorem B17764271 : Blo 1642020 17764271 := bstep (se 1 (by rfl) ⟨13323203, by rfl⟩ : syracuseStep 17764271 = 26646407) B26646407
theorem B35549117 : Blo 1642020 35549117 := bstep (se 3 (by rfl) ⟨6665459, by rfl⟩ : syracuseStep 35549117 = 13330919) B13330919
theorem B12480479 : Blo 1642020 12480479 := bstep (se 1 (by rfl) ⟨9360359, by rfl⟩ : syracuseStep 12480479 = 18720719) B18720719
theorem B1642719 : Blo 1642020 1642719 := bstep (se 1 (by rfl) ⟨1232039, by rfl⟩ : syracuseStep 1642719 = 2464079) B2464079
theorem B1642735 : Blo 1642020 1642735 := bstep (se 1 (by rfl) ⟨1232051, by rfl⟩ : syracuseStep 1642735 = 2464103) B2464103
theorem B1642779 : Blo 1642020 1642779 := bstep (se 1 (by rfl) ⟨1232084, by rfl⟩ : syracuseStep 1642779 = 2464169) B2464169
theorem B1847623 : Blo 1642020 1847623 := bstep (se 1 (by rfl) ⟨1385717, by rfl⟩ : syracuseStep 1847623 = 2771435) B2771435
theorem B21049739 : Blo 1642020 21049739 := bstep (se 1 (by rfl) ⟨15787304, by rfl⟩ : syracuseStep 21049739 = 31574609) B31574609
theorem B5542343 : Blo 1642020 5542343 := bstep (se 1 (by rfl) ⟨4156757, by rfl⟩ : syracuseStep 5542343 = 8313515) B8313515
theorem B1643035 : Blo 1642020 1643035 := bstep (se 1 (by rfl) ⟨1232276, by rfl⟩ : syracuseStep 1643035 = 2464553) B2464553
theorem B2773615 : Blo 1642020 2773615 := bstep (se 1 (by rfl) ⟨2080211, by rfl⟩ : syracuseStep 2773615 = 4160423) B4160423
theorem B1643175 : Blo 1642020 1643175 := bstep (se 1 (by rfl) ⟨1232381, by rfl⟩ : syracuseStep 1643175 = 2464763) B2464763
theorem B1643199 : Blo 1642020 1643199 := bstep (se 1 (by rfl) ⟨1232399, by rfl⟩ : syracuseStep 1643199 = 2464799) B2464799
theorem B1643215 : Blo 1642020 1643215 := bstep (se 1 (by rfl) ⟨1232411, by rfl⟩ : syracuseStep 1643215 = 2464823) B2464823
theorem B1643295 : Blo 1642020 1643295 := bstep (se 1 (by rfl) ⟨1232471, by rfl⟩ : syracuseStep 1643295 = 2464943) B2464943
theorem B1643391 : Blo 1642020 1643391 := bstep (se 1 (by rfl) ⟨1232543, by rfl⟩ : syracuseStep 1643391 = 2465087) B2465087
theorem B1643487 : Blo 1642020 1643487 := bstep (se 1 (by rfl) ⟨1232615, by rfl⟩ : syracuseStep 1643487 = 2465231) B2465231
theorem B76944491 : Blo 1642020 76944491 := bstep (se 1 (by rfl) ⟨57708368, by rfl⟩ : syracuseStep 76944491 = 115416737) B115416737
theorem B33723539 : Blo 1642020 33723539 := bstep (se 1 (by rfl) ⟨25292654, by rfl⟩ : syracuseStep 33723539 = 50585309) B50585309
theorem B1643743 : Blo 1642020 1643743 := bstep (se 1 (by rfl) ⟨1232807, by rfl⟩ : syracuseStep 1643743 = 2465615) B2465615
theorem B1643775 : Blo 1642020 1643775 := bstep (se 1 (by rfl) ⟨1232831, by rfl⟩ : syracuseStep 1643775 = 2465663) B2465663
theorem B1643823 : Blo 1642020 1643823 := bstep (se 1 (by rfl) ⟨1232867, by rfl⟩ : syracuseStep 1643823 = 2465735) B2465735
theorem B1949701475 : Blo 1642020 1949701475 := bstep (se 1 (by rfl) ⟨1462276106, by rfl⟩ : syracuseStep 1949701475 = 2924552213) B2924552213
theorem B1643983 : Blo 1642020 1643983 := bstep (se 1 (by rfl) ⟨1232987, by rfl⟩ : syracuseStep 1643983 = 2465975) B2465975
theorem B2463227 : Blo 1642020 2463227 := bstep (se 1 (by rfl) ⟨1847420, by rfl⟩ : syracuseStep 2463227 = 3694841) B3694841
theorem B5543423 : Blo 1642020 5543423 := bstep (se 1 (by rfl) ⟨4157567, by rfl⟩ : syracuseStep 5543423 = 8315135) B8315135
theorem B2463401 : Blo 1642020 2463401 := bstep (se 2 (by rfl) ⟨923775, by rfl⟩ : syracuseStep 2463401 = 1847551) B1847551
theorem B2463407 : Blo 1642020 2463407 := bstep (se 1 (by rfl) ⟨1847555, by rfl⟩ : syracuseStep 2463407 = 3695111) B3695111
theorem B3118799 : Blo 1642020 3118799 := bstep (se 1 (by rfl) ⟨2339099, by rfl⟩ : syracuseStep 3118799 = 4678199) B4678199
theorem B2463527 : Blo 1642020 2463527 := bstep (se 1 (by rfl) ⟨1847645, by rfl⟩ : syracuseStep 2463527 = 3695291) B3695291
theorem B2463851 : Blo 1642020 2463851 := bstep (se 1 (by rfl) ⟨1847888, by rfl⟩ : syracuseStep 2463851 = 3695777) B3695777
theorem B2464127 : Blo 1642020 2464127 := bstep (se 1 (by rfl) ⟨1848095, by rfl⟩ : syracuseStep 2464127 = 3696191) B3696191
theorem B28072331 : Blo 1642020 28072331 := bstep (se 1 (by rfl) ⟨21054248, by rfl⟩ : syracuseStep 28072331 = 42108497) B42108497
theorem B19225021 : Blo 1642020 19225021 := bstep (se 3 (by rfl) ⟨3604691, by rfl⟩ : syracuseStep 19225021 = 7209383) B7209383
theorem B2464199 : Blo 1642020 2464199 := bstep (se 1 (by rfl) ⟨1848149, by rfl⟩ : syracuseStep 2464199 = 3696299) B3696299
theorem B14981669 : Blo 1642020 14981669 := bstep (se 4 (by rfl) ⟨1404531, by rfl⟩ : syracuseStep 14981669 = 2809063) B2809063
theorem B2464367 : Blo 1642020 2464367 := bstep (se 1 (by rfl) ⟨1848275, by rfl⟩ : syracuseStep 2464367 = 3696551) B3696551
theorem B202267277 : Blo 1642020 202267277 := bstep (se 3 (by rfl) ⟨37925114, by rfl⟩ : syracuseStep 202267277 = 75850229) B75850229
theorem B4160281 : Blo 1642020 4160281 := bstep (se 2 (by rfl) ⟨1560105, by rfl⟩ : syracuseStep 4160281 = 3120211) B3120211
theorem B2464559 : Blo 1642020 2464559 := bstep (se 1 (by rfl) ⟨1848419, by rfl⟩ : syracuseStep 2464559 = 3696839) B3696839
theorem B2464679 : Blo 1642020 2464679 := bstep (se 1 (by rfl) ⟨1848509, by rfl⟩ : syracuseStep 2464679 = 3697019) B3697019
theorem B2464751 : Blo 1642020 2464751 := bstep (se 1 (by rfl) ⟨1848563, by rfl⟩ : syracuseStep 2464751 = 3697127) B3697127
theorem B2464859 : Blo 1642020 2464859 := bstep (se 1 (by rfl) ⟨1848644, by rfl⟩ : syracuseStep 2464859 = 3697289) B3697289
theorem B2464871 : Blo 1642020 2464871 := bstep (se 1 (by rfl) ⟨1848653, by rfl⟩ : syracuseStep 2464871 = 3697307) B3697307
theorem B2464937 : Blo 1642020 2464937 := bstep (se 2 (by rfl) ⟨924351, by rfl⟩ : syracuseStep 2464937 = 1848703) B1848703
theorem B6241607 : Blo 1642020 6241607 := bstep (se 1 (by rfl) ⟨4681205, by rfl⟩ : syracuseStep 6241607 = 9362411) B9362411
theorem B3120743 : Blo 1642020 3120743 := bstep (se 1 (by rfl) ⟨2340557, by rfl⟩ : syracuseStep 3120743 = 4681115) B4681115
theorem B2465519 : Blo 1642020 2465519 := bstep (se 1 (by rfl) ⟨1849139, by rfl⟩ : syracuseStep 2465519 = 3698279) B3698279
theorem B1777403 : Blo 1642020 1777403 := bstep (se 1 (by rfl) ⟨1333052, by rfl⟩ : syracuseStep 1777403 = 2666105) B2666105
theorem B11845385 : Blo 1642020 11845385 := bstep (se 2 (by rfl) ⟨4442019, by rfl⟩ : syracuseStep 11845385 = 8884039) B8884039
theorem B12640139 : Blo 1642020 12640139 := bstep (se 1 (by rfl) ⟨9480104, by rfl⟩ : syracuseStep 12640139 = 18960209) B18960209
theorem B2465705 : Blo 1642020 2465705 := bstep (se 2 (by rfl) ⟨924639, by rfl⟩ : syracuseStep 2465705 = 1849279) B1849279
theorem B14033159 : Blo 1642020 14033159 := bstep (se 1 (by rfl) ⟨10524869, by rfl⟩ : syracuseStep 14033159 = 21049739) B21049739
theorem B3694895 : Blo 1642020 3694895 := bstep (se 1 (by rfl) ⟨2771171, by rfl⟩ : syracuseStep 3694895 = 5542343) B5542343
theorem B25633361 : Blo 1642020 25633361 := bstep (se 2 (by rfl) ⟨9612510, by rfl⟩ : syracuseStep 25633361 = 19225021) B19225021
theorem B3695615 : Blo 1642020 3695615 := bstep (se 1 (by rfl) ⟨2771711, by rfl⟩ : syracuseStep 3695615 = 5543423) B5543423
theorem B5547041 : Blo 1642020 5547041 := bstep (se 2 (by rfl) ⟨2080140, by rfl⟩ : syracuseStep 5547041 = 4160281) B4160281
theorem B53298647 : Blo 1642020 53298647 := bstep (se 1 (by rfl) ⟨39973985, by rfl⟩ : syracuseStep 53298647 = 79947971) B79947971
theorem B33744545 : Blo 1642020 33744545 := bstep (se 2 (by rfl) ⟨12654204, by rfl⟩ : syracuseStep 33744545 = 25308409) B25308409
theorem B9987779 : Blo 1642020 9987779 := bstep (se 1 (by rfl) ⟨7490834, by rfl⟩ : syracuseStep 9987779 = 14981669) B14981669
theorem B3508051 : Blo 1642020 3508051 := bstep (se 1 (by rfl) ⟨2631038, by rfl⟩ : syracuseStep 3508051 = 5262077) B5262077
theorem B11241505 : Blo 1642020 11241505 := bstep (se 2 (by rfl) ⟨4215564, by rfl⟩ : syracuseStep 11241505 = 8431129) B8431129
theorem B17762449 : Blo 1642020 17762449 := bstep (se 2 (by rfl) ⟨6660918, by rfl⟩ : syracuseStep 17762449 = 13321837) B13321837
theorem B18704681 : Blo 1642020 18704681 := bstep (se 2 (by rfl) ⟨7014255, by rfl⟩ : syracuseStep 18704681 = 14028511) B14028511
theorem B3697775 : Blo 1642020 3697775 := bstep (se 1 (by rfl) ⟨2773331, by rfl⟩ : syracuseStep 3697775 = 5546663) B5546663
theorem B2632871 : Blo 1642020 2632871 := bstep (se 1 (by rfl) ⟨1974653, by rfl⟩ : syracuseStep 2632871 = 3949307) B3949307
theorem B22482359 : Blo 1642020 22482359 := bstep (se 1 (by rfl) ⟨16861769, by rfl⟩ : syracuseStep 22482359 = 33723539) B33723539
theorem B20540891 : Blo 1642020 20540891 := bstep (se 1 (by rfl) ⟨15405668, by rfl⟩ : syracuseStep 20540891 = 30811337) B30811337
theorem B3698153 : Blo 1642020 3698153 := bstep (se 2 (by rfl) ⟨1386807, by rfl⟩ : syracuseStep 3698153 = 2773615) B2773615
theorem B3698207 : Blo 1642020 3698207 := bstep (se 1 (by rfl) ⟨2773655, by rfl⟩ : syracuseStep 3698207 = 5547311) B5547311
theorem B5199203933 : Blo 1642020 5199203933 := bstep (se 3 (by rfl) ⟨974850737, by rfl⟩ : syracuseStep 5199203933 = 1949701475) B1949701475
theorem B1642151 : Blo 1642020 1642151 := bstep (se 1 (by rfl) ⟨1231613, by rfl⟩ : syracuseStep 1642151 = 2463227) B2463227
theorem B18706139 : Blo 1642020 18706139 := bstep (se 1 (by rfl) ⟨14029604, by rfl⟩ : syracuseStep 18706139 = 28059209) B28059209
theorem B1642267 : Blo 1642020 1642267 := bstep (se 1 (by rfl) ⟨1231700, by rfl⟩ : syracuseStep 1642267 = 2463401) B2463401
theorem B1642271 : Blo 1642020 1642271 := bstep (se 1 (by rfl) ⟨1231703, by rfl⟩ : syracuseStep 1642271 = 2463407) B2463407
theorem B1642351 : Blo 1642020 1642351 := bstep (se 1 (by rfl) ⟨1231763, by rfl⟩ : syracuseStep 1642351 = 2463527) B2463527
theorem B2961403 : Blo 1642020 2961403 := bstep (se 1 (by rfl) ⟨2221052, by rfl⟩ : syracuseStep 2961403 = 4442105) B4442105
theorem B1642567 : Blo 1642020 1642567 := bstep (se 1 (by rfl) ⟨1231925, by rfl⟩ : syracuseStep 1642567 = 2463851) B2463851
theorem B3698783 : Blo 1642020 3698783 := bstep (se 1 (by rfl) ⟨2774087, by rfl⟩ : syracuseStep 3698783 = 5548175) B5548175
theorem B4272335 : Blo 1642020 4272335 := bstep (se 1 (by rfl) ⟨3204251, by rfl⟩ : syracuseStep 4272335 = 6408503) B6408503
theorem B1642751 : Blo 1642020 1642751 := bstep (se 1 (by rfl) ⟨1232063, by rfl⟩ : syracuseStep 1642751 = 2464127) B2464127
theorem B18714887 : Blo 1642020 18714887 := bstep (se 1 (by rfl) ⟨14036165, by rfl⟩ : syracuseStep 18714887 = 28072331) B28072331
theorem B1642799 : Blo 1642020 1642799 := bstep (se 1 (by rfl) ⟨1232099, by rfl⟩ : syracuseStep 1642799 = 2464199) B2464199
theorem B1642911 : Blo 1642020 1642911 := bstep (se 1 (by rfl) ⟨1232183, by rfl⟩ : syracuseStep 1642911 = 2464367) B2464367
theorem B134844851 : Blo 1642020 134844851 := bstep (se 1 (by rfl) ⟨101133638, by rfl⟩ : syracuseStep 134844851 = 202267277) B202267277
theorem B1847839 : Blo 1642020 1847839 := bstep (se 1 (by rfl) ⟨1385879, by rfl⟩ : syracuseStep 1847839 = 2771759) B2771759
theorem B1643039 : Blo 1642020 1643039 := bstep (se 1 (by rfl) ⟨1232279, by rfl⟩ : syracuseStep 1643039 = 2464559) B2464559
theorem B1643119 : Blo 1642020 1643119 := bstep (se 1 (by rfl) ⟨1232339, by rfl⟩ : syracuseStep 1643119 = 2464679) B2464679
theorem B4739741 : Blo 1642020 4739741 := bstep (se 3 (by rfl) ⟨888701, by rfl⟩ : syracuseStep 4739741 = 1777403) B1777403
theorem B1643167 : Blo 1642020 1643167 := bstep (se 1 (by rfl) ⟨1232375, by rfl⟩ : syracuseStep 1643167 = 2464751) B2464751
theorem B1643239 : Blo 1642020 1643239 := bstep (se 1 (by rfl) ⟨1232429, by rfl⟩ : syracuseStep 1643239 = 2464859) B2464859
theorem B1643247 : Blo 1642020 1643247 := bstep (se 1 (by rfl) ⟨1232435, by rfl⟩ : syracuseStep 1643247 = 2464871) B2464871
theorem B1643291 : Blo 1642020 1643291 := bstep (se 1 (by rfl) ⟨1232468, by rfl⟩ : syracuseStep 1643291 = 2464937) B2464937
theorem B1643679 : Blo 1642020 1643679 := bstep (se 1 (by rfl) ⟨1232759, by rfl⟩ : syracuseStep 1643679 = 2465519) B2465519
theorem B1848487 : Blo 1642020 1848487 := bstep (se 1 (by rfl) ⟨1386365, by rfl⟩ : syracuseStep 1848487 = 2772731) B2772731
theorem B8426759 : Blo 1642020 8426759 := bstep (se 1 (by rfl) ⟨6320069, by rfl⟩ : syracuseStep 8426759 = 12640139) B12640139
theorem B1643803 : Blo 1642020 1643803 := bstep (se 1 (by rfl) ⟨1232852, by rfl⟩ : syracuseStep 1643803 = 2465705) B2465705
theorem B11842847 : Blo 1642020 11842847 := bstep (se 1 (by rfl) ⟨8882135, by rfl⟩ : syracuseStep 11842847 = 17764271) B17764271
theorem B8320319 : Blo 1642020 8320319 := bstep (se 1 (by rfl) ⟨6240239, by rfl⟩ : syracuseStep 8320319 = 12480479) B12480479
theorem B2463497 : Blo 1642020 2463497 := bstep (se 2 (by rfl) ⟨923811, by rfl⟩ : syracuseStep 2463497 = 1847623) B1847623
theorem B16865047 : Blo 1642020 16865047 := bstep (se 1 (by rfl) ⟨12648785, by rfl⟩ : syracuseStep 16865047 = 25297571) B25297571
theorem B2463791 : Blo 1642020 2463791 := bstep (se 1 (by rfl) ⟨1847843, by rfl⟩ : syracuseStep 2463791 = 3695687) B3695687
theorem B51296327 : Blo 1642020 51296327 := bstep (se 1 (by rfl) ⟨38472245, by rfl⟩ : syracuseStep 51296327 = 76944491) B76944491
theorem B2079199 : Blo 1642020 2079199 := bstep (se 1 (by rfl) ⟨1559399, by rfl⟩ : syracuseStep 2079199 = 3118799) B3118799
theorem B2464463 : Blo 1642020 2464463 := bstep (se 1 (by rfl) ⟨1848347, by rfl⟩ : syracuseStep 2464463 = 3696695) B3696695
theorem B4676399 : Blo 1642020 4676399 := bstep (se 1 (by rfl) ⟨3507299, by rfl⟩ : syracuseStep 4676399 = 7014599) B7014599
theorem B6241121 : Blo 1642020 6241121 := bstep (se 2 (by rfl) ⟨2340420, by rfl⟩ : syracuseStep 6241121 = 4680841) B4680841
theorem B2464703 : Blo 1642020 2464703 := bstep (se 1 (by rfl) ⟨1848527, by rfl⟩ : syracuseStep 2464703 = 3697055) B3697055
theorem B23682293 : Blo 1642020 23682293 := bstep (se 5 (by rfl) ⟨1110107, by rfl⟩ : syracuseStep 23682293 = 2220215) B2220215
theorem B2465327 : Blo 1642020 2465327 := bstep (se 1 (by rfl) ⟨1848995, by rfl⟩ : syracuseStep 2465327 = 3697991) B3697991
theorem B4161071 : Blo 1642020 4161071 := bstep (se 1 (by rfl) ⟨3120803, by rfl⟩ : syracuseStep 4161071 = 6241607) B6241607
theorem B2080495 : Blo 1642020 2080495 := bstep (se 1 (by rfl) ⟨1560371, by rfl⟩ : syracuseStep 2080495 = 3120743) B3120743
theorem B8314649 : Blo 1642020 8314649 := bstep (se 2 (by rfl) ⟨3117993, by rfl⟩ : syracuseStep 8314649 = 6235987) B6235987
theorem B7896923 : Blo 1642020 7896923 := bstep (se 1 (by rfl) ⟨5922692, by rfl⟩ : syracuseStep 7896923 = 11845385) B11845385
theorem B23699411 : Blo 1642020 23699411 := bstep (se 1 (by rfl) ⟨17774558, by rfl⟩ : syracuseStep 23699411 = 35549117) B35549117
theorem B8880101 : Blo 1642020 8880101 := bstep (se 4 (by rfl) ⟨832509, by rfl⟩ : syracuseStep 8880101 = 1665019) B1665019
theorem B2465855 : Blo 1642020 2465855 := bstep (se 1 (by rfl) ⟨1849391, by rfl⟩ : syracuseStep 2465855 = 3698783) B3698783
theorem B9355439 : Blo 1642020 9355439 := bstep (se 1 (by rfl) ⟨7016579, by rfl⟩ : syracuseStep 9355439 = 14033159) B14033159
theorem B12476591 : Blo 1642020 12476591 := bstep (se 1 (by rfl) ⟨9357443, by rfl⟩ : syracuseStep 12476591 = 18714887) B18714887
theorem B23683265 : Blo 1642020 23683265 := bstep (se 2 (by rfl) ⟨8881224, by rfl⟩ : syracuseStep 23683265 = 17762449) B17762449
theorem B17088907 : Blo 1642020 17088907 := bstep (se 1 (by rfl) ⟨12816680, by rfl⟩ : syracuseStep 17088907 = 25633361) B25633361
theorem B7020989 : Blo 1642020 7020989 := bstep (se 3 (by rfl) ⟨1316435, by rfl⟩ : syracuseStep 7020989 = 2632871) B2632871
theorem B22471357 : Blo 1642020 22471357 := bstep (se 3 (by rfl) ⟨4213379, by rfl⟩ : syracuseStep 22471357 = 8426759) B8426759
theorem B5546879 : Blo 1642020 5546879 := bstep (se 1 (by rfl) ⟨4160159, by rfl⟩ : syracuseStep 5546879 = 8320319) B8320319
theorem B22496363 : Blo 1642020 22496363 := bstep (se 1 (by rfl) ⟨16872272, by rfl⟩ : syracuseStep 22496363 = 33744545) B33744545
theorem B12469787 : Blo 1642020 12469787 := bstep (se 1 (by rfl) ⟨9352340, by rfl⟩ : syracuseStep 12469787 = 18704681) B18704681
theorem B15788195 : Blo 1642020 15788195 := bstep (se 1 (by rfl) ⟨11841146, by rfl⟩ : syracuseStep 15788195 = 23682293) B23682293
theorem B3466135955 : Blo 1642020 3466135955 := bstep (se 1 (by rfl) ⟨2599601966, by rfl⟩ : syracuseStep 3466135955 = 5199203933) B5199203933
theorem B12470759 : Blo 1642020 12470759 := bstep (se 1 (by rfl) ⟨9353069, by rfl⟩ : syracuseStep 12470759 = 18706139) B18706139
theorem B2772265 : Blo 1642020 2772265 := bstep (se 2 (by rfl) ⟨1039599, by rfl⟩ : syracuseStep 2772265 = 2079199) B2079199
theorem B3698027 : Blo 1642020 3698027 := bstep (se 1 (by rfl) ⟨2773520, by rfl⟩ : syracuseStep 3698027 = 5547041) B5547041
theorem B35532431 : Blo 1642020 35532431 := bstep (se 1 (by rfl) ⟨26649323, by rfl⟩ : syracuseStep 35532431 = 53298647) B53298647
theorem B1642331 : Blo 1642020 1642331 := bstep (se 1 (by rfl) ⟨1231748, by rfl⟩ : syracuseStep 1642331 = 2463497) B2463497
theorem B54775709 : Blo 1642020 54775709 := bstep (se 3 (by rfl) ⟨10270445, by rfl⟩ : syracuseStep 54775709 = 20540891) B20540891
theorem B1642527 : Blo 1642020 1642527 := bstep (se 1 (by rfl) ⟨1231895, by rfl⟩ : syracuseStep 1642527 = 2463791) B2463791
theorem B34197551 : Blo 1642020 34197551 := bstep (se 1 (by rfl) ⟨25648163, by rfl⟩ : syracuseStep 34197551 = 51296327) B51296327
theorem B1642975 : Blo 1642020 1642975 := bstep (se 1 (by rfl) ⟨1232231, by rfl⟩ : syracuseStep 1642975 = 2464463) B2464463
theorem B3117599 : Blo 1642020 3117599 := bstep (se 1 (by rfl) ⟨2338199, by rfl⟩ : syracuseStep 3117599 = 4676399) B4676399
theorem B1643135 : Blo 1642020 1643135 := bstep (se 1 (by rfl) ⟨1232351, by rfl⟩ : syracuseStep 1643135 = 2464703) B2464703
theorem B14988239 : Blo 1642020 14988239 := bstep (se 1 (by rfl) ⟨11241179, by rfl⟩ : syracuseStep 14988239 = 22482359) B22482359
theorem B2773993 : Blo 1642020 2773993 := bstep (se 2 (by rfl) ⟨1040247, by rfl⟩ : syracuseStep 2773993 = 2080495) B2080495
theorem B1643551 : Blo 1642020 1643551 := bstep (se 1 (by rfl) ⟨1232663, by rfl⟩ : syracuseStep 1643551 = 2465327) B2465327
theorem B2774047 : Blo 1642020 2774047 := bstep (se 1 (by rfl) ⟨2080535, by rfl⟩ : syracuseStep 2774047 = 4161071) B4161071
theorem B5543099 : Blo 1642020 5543099 := bstep (se 1 (by rfl) ⟨4157324, by rfl⟩ : syracuseStep 5543099 = 8314649) B8314649
theorem B5264615 : Blo 1642020 5264615 := bstep (se 1 (by rfl) ⟨3948461, by rfl⟩ : syracuseStep 5264615 = 7896923) B7896923
theorem B15799607 : Blo 1642020 15799607 := bstep (se 1 (by rfl) ⟨11849705, by rfl⟩ : syracuseStep 15799607 = 23699411) B23699411
theorem B5920067 : Blo 1642020 5920067 := bstep (se 1 (by rfl) ⟨4440050, by rfl⟩ : syracuseStep 5920067 = 8880101) B8880101
theorem B14988673 : Blo 1642020 14988673 := bstep (se 2 (by rfl) ⟨5620752, by rfl⟩ : syracuseStep 14988673 = 11241505) B11241505
theorem B2848223 : Blo 1642020 2848223 := bstep (se 1 (by rfl) ⟨2136167, by rfl⟩ : syracuseStep 2848223 = 4272335) B4272335
theorem B2463263 : Blo 1642020 2463263 := bstep (se 1 (by rfl) ⟨1847447, by rfl⟩ : syracuseStep 2463263 = 3694895) B3694895
theorem B89896567 : Blo 1642020 89896567 := bstep (se 1 (by rfl) ⟨67422425, by rfl⟩ : syracuseStep 89896567 = 134844851) B134844851
theorem B3159827 : Blo 1642020 3159827 := bstep (se 1 (by rfl) ⟨2369870, by rfl⟩ : syracuseStep 3159827 = 4739741) B4739741
theorem B2463743 : Blo 1642020 2463743 := bstep (se 1 (by rfl) ⟨1847807, by rfl⟩ : syracuseStep 2463743 = 3695615) B3695615
theorem B2463785 : Blo 1642020 2463785 := bstep (se 2 (by rfl) ⟨923919, by rfl⟩ : syracuseStep 2463785 = 1847839) B1847839
theorem B7895231 : Blo 1642020 7895231 := bstep (se 1 (by rfl) ⟨5921423, by rfl⟩ : syracuseStep 7895231 = 11842847) B11842847
theorem B6658519 : Blo 1642020 6658519 := bstep (se 1 (by rfl) ⟨4993889, by rfl⟩ : syracuseStep 6658519 = 9987779) B9987779
theorem B2464649 : Blo 1642020 2464649 := bstep (se 2 (by rfl) ⟨924243, by rfl⟩ : syracuseStep 2464649 = 1848487) B1848487
theorem B4160747 : Blo 1642020 4160747 := bstep (se 1 (by rfl) ⟨3120560, by rfl⟩ : syracuseStep 4160747 = 6241121) B6241121
theorem B2465183 : Blo 1642020 2465183 := bstep (se 1 (by rfl) ⟨1848887, by rfl⟩ : syracuseStep 2465183 = 3697775) B3697775
theorem B2465435 : Blo 1642020 2465435 := bstep (se 1 (by rfl) ⟨1849076, by rfl⟩ : syracuseStep 2465435 = 3698153) B3698153
theorem B2465471 : Blo 1642020 2465471 := bstep (se 1 (by rfl) ⟨1849103, by rfl⟩ : syracuseStep 2465471 = 3698207) B3698207
theorem B22486729 : Blo 1642020 22486729 := bstep (se 2 (by rfl) ⟨8432523, by rfl⟩ : syracuseStep 22486729 = 16865047) B16865047
theorem B4677401 : Blo 1642020 4677401 := bstep (se 2 (by rfl) ⟨1754025, by rfl⟩ : syracuseStep 4677401 = 3508051) B3508051
theorem B15794149 : Blo 1642020 15794149 := bstep (se 4 (by rfl) ⟨1480701, by rfl⟩ : syracuseStep 15794149 = 2961403) B2961403
theorem B22798367 : Blo 1642020 22798367 := bstep (se 1 (by rfl) ⟨17098775, by rfl⟩ : syracuseStep 22798367 = 34197551) B34197551
theorem B3695399 : Blo 1642020 3695399 := bstep (se 1 (by rfl) ⟨2771549, by rfl⟩ : syracuseStep 3695399 = 5543099) B5543099
theorem B15786845 : Blo 1642020 15786845 := bstep (se 3 (by rfl) ⟨2960033, by rfl⟩ : syracuseStep 15786845 = 5920067) B5920067
theorem B2106551 : Blo 1642020 2106551 := bstep (se 1 (by rfl) ⟨1579913, by rfl⟩ : syracuseStep 2106551 = 3159827) B3159827
theorem B3696353 : Blo 1642020 3696353 := bstep (se 2 (by rfl) ⟨1386132, by rfl⟩ : syracuseStep 3696353 = 2772265) B2772265
theorem B6236959 : Blo 1642020 6236959 := bstep (se 1 (by rfl) ⟨4677719, by rfl⟩ : syracuseStep 6236959 = 9355439) B9355439
theorem B8317727 : Blo 1642020 8317727 := bstep (se 1 (by rfl) ⟨6238295, by rfl⟩ : syracuseStep 8317727 = 12476591) B12476591
theorem B15788843 : Blo 1642020 15788843 := bstep (se 1 (by rfl) ⟨11841632, by rfl⟩ : syracuseStep 15788843 = 23683265) B23683265
theorem B4680659 : Blo 1642020 4680659 := bstep (se 1 (by rfl) ⟨3510494, by rfl⟩ : syracuseStep 4680659 = 7020989) B7020989
theorem B22785209 : Blo 1642020 22785209 := bstep (se 2 (by rfl) ⟨8544453, by rfl⟩ : syracuseStep 22785209 = 17088907) B17088907
theorem B3697919 : Blo 1642020 3697919 := bstep (se 1 (by rfl) ⟨2773439, by rfl⟩ : syracuseStep 3697919 = 5546879) B5546879
theorem B3509743 : Blo 1642020 3509743 := bstep (se 1 (by rfl) ⟨2632307, by rfl⟩ : syracuseStep 3509743 = 5264615) B5264615
theorem B29961809 : Blo 1642020 29961809 := bstep (se 2 (by rfl) ⟨11235678, by rfl⟩ : syracuseStep 29961809 = 22471357) B22471357
theorem B1642175 : Blo 1642020 1642175 := bstep (se 1 (by rfl) ⟨1231631, by rfl⟩ : syracuseStep 1642175 = 2463263) B2463263
theorem B3698657 : Blo 1642020 3698657 := bstep (se 2 (by rfl) ⟨1386996, by rfl⟩ : syracuseStep 3698657 = 2773993) B2773993
theorem B1642495 : Blo 1642020 1642495 := bstep (se 1 (by rfl) ⟨1231871, by rfl⟩ : syracuseStep 1642495 = 2463743) B2463743
theorem B1642523 : Blo 1642020 1642523 := bstep (se 1 (by rfl) ⟨1231892, by rfl⟩ : syracuseStep 1642523 = 2463785) B2463785
theorem B3698729 : Blo 1642020 3698729 := bstep (se 2 (by rfl) ⟨1387023, by rfl⟩ : syracuseStep 3698729 = 2774047) B2774047
theorem B5263487 : Blo 1642020 5263487 := bstep (se 1 (by rfl) ⟨3947615, by rfl⟩ : syracuseStep 5263487 = 7895231) B7895231
theorem B19984897 : Blo 1642020 19984897 := bstep (se 2 (by rfl) ⟨7494336, by rfl⟩ : syracuseStep 19984897 = 14988673) B14988673
theorem B1643099 : Blo 1642020 1643099 := bstep (se 1 (by rfl) ⟨1232324, by rfl⟩ : syracuseStep 1643099 = 2464649) B2464649
theorem B2773831 : Blo 1642020 2773831 := bstep (se 1 (by rfl) ⟨2080373, by rfl⟩ : syracuseStep 2773831 = 4160747) B4160747
theorem B119862089 : Blo 1642020 119862089 := bstep (se 2 (by rfl) ⟨44948283, by rfl⟩ : syracuseStep 119862089 = 89896567) B89896567
theorem B1643455 : Blo 1642020 1643455 := bstep (se 1 (by rfl) ⟨1232591, by rfl⟩ : syracuseStep 1643455 = 2465183) B2465183
theorem B23688287 : Blo 1642020 23688287 := bstep (se 1 (by rfl) ⟨17766215, by rfl⟩ : syracuseStep 23688287 = 35532431) B35532431
theorem B1643623 : Blo 1642020 1643623 := bstep (se 1 (by rfl) ⟨1232717, by rfl⟩ : syracuseStep 1643623 = 2465435) B2465435
theorem B1643647 : Blo 1642020 1643647 := bstep (se 1 (by rfl) ⟨1232735, by rfl⟩ : syracuseStep 1643647 = 2465471) B2465471
theorem B3118267 : Blo 1642020 3118267 := bstep (se 1 (by rfl) ⟨2338700, by rfl⟩ : syracuseStep 3118267 = 4677401) B4677401
theorem B36517139 : Blo 1642020 36517139 := bstep (se 1 (by rfl) ⟨27387854, by rfl⟩ : syracuseStep 36517139 = 54775709) B54775709
theorem B21058865 : Blo 1642020 21058865 := bstep (se 2 (by rfl) ⟨7897074, by rfl⟩ : syracuseStep 21058865 = 15794149) B15794149
theorem B1643903 : Blo 1642020 1643903 := bstep (se 1 (by rfl) ⟨1232927, by rfl⟩ : syracuseStep 1643903 = 2465855) B2465855
theorem B2078399 : Blo 1642020 2078399 := bstep (se 1 (by rfl) ⟨1558799, by rfl⟩ : syracuseStep 2078399 = 3117599) B3117599
theorem B8878025 : Blo 1642020 8878025 := bstep (se 2 (by rfl) ⟨3329259, by rfl⟩ : syracuseStep 8878025 = 6658519) B6658519
theorem B9992159 : Blo 1642020 9992159 := bstep (se 1 (by rfl) ⟨7494119, by rfl⟩ : syracuseStep 9992159 = 14988239) B14988239
theorem B14997575 : Blo 1642020 14997575 := bstep (se 1 (by rfl) ⟨11248181, by rfl⟩ : syracuseStep 14997575 = 22496363) B22496363
theorem B10533071 : Blo 1642020 10533071 := bstep (se 1 (by rfl) ⟨7899803, by rfl⟩ : syracuseStep 10533071 = 15799607) B15799607
theorem B1898815 : Blo 1642020 1898815 := bstep (se 1 (by rfl) ⟨1424111, by rfl⟩ : syracuseStep 1898815 = 2848223) B2848223
theorem B8313191 : Blo 1642020 8313191 := bstep (se 1 (by rfl) ⟨6234893, by rfl⟩ : syracuseStep 8313191 = 12469787) B12469787
theorem B10525463 : Blo 1642020 10525463 := bstep (se 1 (by rfl) ⟨7894097, by rfl⟩ : syracuseStep 10525463 = 15788195) B15788195
theorem B2310757303 : Blo 1642020 2310757303 := bstep (se 1 (by rfl) ⟨1733067977, by rfl⟩ : syracuseStep 2310757303 = 3466135955) B3466135955
theorem B8313839 : Blo 1642020 8313839 := bstep (se 1 (by rfl) ⟨6235379, by rfl⟩ : syracuseStep 8313839 = 12470759) B12470759
theorem B2465351 : Blo 1642020 2465351 := bstep (se 1 (by rfl) ⟨1849013, by rfl⟩ : syracuseStep 2465351 = 3698027) B3698027
theorem B29982305 : Blo 1642020 29982305 := bstep (se 2 (by rfl) ⟨11243364, by rfl⟩ : syracuseStep 29982305 = 22486729) B22486729
theorem B2465819 : Blo 1642020 2465819 := bstep (se 1 (by rfl) ⟨1849364, by rfl⟩ : syracuseStep 2465819 = 3698729) B3698729
theorem B39993533 : Blo 1642020 39993533 := bstep (se 3 (by rfl) ⟨7498787, by rfl⟩ : syracuseStep 39993533 = 14997575) B14997575
theorem B2531753 : Blo 1642020 2531753 := bstep (se 2 (by rfl) ⟨949407, by rfl⟩ : syracuseStep 2531753 = 1898815) B1898815
theorem B8315945 : Blo 1642020 8315945 := bstep (se 2 (by rfl) ⟨3118479, by rfl⟩ : syracuseStep 8315945 = 6236959) B6236959
theorem B6661439 : Blo 1642020 6661439 := bstep (se 1 (by rfl) ⟨4996079, by rfl⟩ : syracuseStep 6661439 = 9992159) B9992159
theorem B7022047 : Blo 1642020 7022047 := bstep (se 1 (by rfl) ⟨5266535, by rfl⟩ : syracuseStep 7022047 = 10533071) B10533071
theorem B4679657 : Blo 1642020 4679657 := bstep (se 2 (by rfl) ⟨1754871, by rfl⟩ : syracuseStep 4679657 = 3509743) B3509743
theorem B15190139 : Blo 1642020 15190139 := bstep (se 1 (by rfl) ⟨11392604, by rfl⟩ : syracuseStep 15190139 = 22785209) B22785209
theorem B19974539 : Blo 1642020 19974539 := bstep (se 1 (by rfl) ⟨14980904, by rfl⟩ : syracuseStep 19974539 = 29961809) B29961809
theorem B15198911 : Blo 1642020 15198911 := bstep (se 1 (by rfl) ⟨11399183, by rfl⟩ : syracuseStep 15198911 = 22798367) B22798367
theorem B3508991 : Blo 1642020 3508991 := bstep (se 1 (by rfl) ⟨2631743, by rfl⟩ : syracuseStep 3508991 = 5263487) B5263487
theorem B79908059 : Blo 1642020 79908059 := bstep (se 1 (by rfl) ⟨59931044, by rfl⟩ : syracuseStep 79908059 = 119862089) B119862089
theorem B3698441 : Blo 1642020 3698441 := bstep (se 2 (by rfl) ⟨1386915, by rfl⟩ : syracuseStep 3698441 = 2773831) B2773831
theorem B5918683 : Blo 1642020 5918683 := bstep (se 1 (by rfl) ⟨4439012, by rfl⟩ : syracuseStep 5918683 = 8878025) B8878025
theorem B5542127 : Blo 1642020 5542127 := bstep (se 1 (by rfl) ⟨4156595, by rfl⟩ : syracuseStep 5542127 = 8313191) B8313191
theorem B4157689 : Blo 1642020 4157689 := bstep (se 2 (by rfl) ⟨1559133, by rfl⟩ : syracuseStep 4157689 = 3118267) B3118267
theorem B5542397 : Blo 1642020 5542397 := bstep (se 3 (by rfl) ⟨1039199, by rfl⟩ : syracuseStep 5542397 = 2078399) B2078399
theorem B7016975 : Blo 1642020 7016975 := bstep (se 1 (by rfl) ⟨5262731, by rfl⟩ : syracuseStep 7016975 = 10525463) B10525463
theorem B5542559 : Blo 1642020 5542559 := bstep (se 1 (by rfl) ⟨4156919, by rfl⟩ : syracuseStep 5542559 = 8313839) B8313839
theorem B1643567 : Blo 1642020 1643567 := bstep (se 1 (by rfl) ⟨1232675, by rfl⟩ : syracuseStep 1643567 = 2465351) B2465351
theorem B5617469 : Blo 1642020 5617469 := bstep (se 3 (by rfl) ⟨1053275, by rfl⟩ : syracuseStep 5617469 = 2106551) B2106551
theorem B2463599 : Blo 1642020 2463599 := bstep (se 1 (by rfl) ⟨1847699, by rfl⟩ : syracuseStep 2463599 = 3695399) B3695399
theorem B10524563 : Blo 1642020 10524563 := bstep (se 1 (by rfl) ⟨7893422, by rfl⟩ : syracuseStep 10524563 = 15786845) B15786845
theorem B26646529 : Blo 1642020 26646529 := bstep (se 2 (by rfl) ⟨9992448, by rfl⟩ : syracuseStep 26646529 = 19984897) B19984897
theorem B15792191 : Blo 1642020 15792191 := bstep (se 1 (by rfl) ⟨11844143, by rfl⟩ : syracuseStep 15792191 = 23688287) B23688287
theorem B24344759 : Blo 1642020 24344759 := bstep (se 1 (by rfl) ⟨18258569, by rfl⟩ : syracuseStep 24344759 = 36517139) B36517139
theorem B14039243 : Blo 1642020 14039243 := bstep (se 1 (by rfl) ⟨10529432, by rfl⟩ : syracuseStep 14039243 = 21058865) B21058865
theorem B2464235 : Blo 1642020 2464235 := bstep (se 1 (by rfl) ⟨1848176, by rfl⟩ : syracuseStep 2464235 = 3696353) B3696353
theorem B3081009737 : Blo 1642020 3081009737 := bstep (se 2 (by rfl) ⟨1155378651, by rfl⟩ : syracuseStep 3081009737 = 2310757303) B2310757303
theorem B5545151 : Blo 1642020 5545151 := bstep (se 1 (by rfl) ⟨4158863, by rfl⟩ : syracuseStep 5545151 = 8317727) B8317727
theorem B10525895 : Blo 1642020 10525895 := bstep (se 1 (by rfl) ⟨7894421, by rfl⟩ : syracuseStep 10525895 = 15788843) B15788843
theorem B3120439 : Blo 1642020 3120439 := bstep (se 1 (by rfl) ⟨2340329, by rfl⟩ : syracuseStep 3120439 = 4680659) B4680659
theorem B2465279 : Blo 1642020 2465279 := bstep (se 1 (by rfl) ⟨1848959, by rfl⟩ : syracuseStep 2465279 = 3697919) B3697919
theorem B19988203 : Blo 1642020 19988203 := bstep (se 1 (by rfl) ⟨14991152, by rfl⟩ : syracuseStep 19988203 = 29982305) B29982305
theorem B2465771 : Blo 1642020 2465771 := bstep (se 1 (by rfl) ⟨1849328, by rfl⟩ : syracuseStep 2465771 = 3698657) B3698657
theorem B35528705 : Blo 1642020 35528705 := bstep (se 2 (by rfl) ⟨13323264, by rfl⟩ : syracuseStep 35528705 = 26646529) B26646529
theorem B3694751 : Blo 1642020 3694751 := bstep (se 1 (by rfl) ⟨2771063, by rfl⟩ : syracuseStep 3694751 = 5542127) B5542127
theorem B1687835 : Blo 1642020 1687835 := bstep (se 1 (by rfl) ⟨1265876, by rfl⟩ : syracuseStep 1687835 = 2531753) B2531753
theorem B3694931 : Blo 1642020 3694931 := bstep (se 1 (by rfl) ⟨2771198, by rfl⟩ : syracuseStep 3694931 = 5542397) B5542397
theorem B4677983 : Blo 1642020 4677983 := bstep (se 1 (by rfl) ⟨3508487, by rfl⟩ : syracuseStep 4677983 = 7016975) B7016975
theorem B3695039 : Blo 1642020 3695039 := bstep (se 1 (by rfl) ⟨2771279, by rfl⟩ : syracuseStep 3695039 = 5542559) B5542559
theorem B4440959 : Blo 1642020 4440959 := bstep (se 1 (by rfl) ⟨3330719, by rfl⟩ : syracuseStep 4440959 = 6661439) B6661439
theorem B10528127 : Blo 1642020 10528127 := bstep (se 1 (by rfl) ⟨7896095, by rfl⟩ : syracuseStep 10528127 = 15792191) B15792191
theorem B3696767 : Blo 1642020 3696767 := bstep (se 1 (by rfl) ⟨2772575, by rfl⟩ : syracuseStep 3696767 = 5545151) B5545151
theorem B26650937 : Blo 1642020 26650937 := bstep (se 2 (by rfl) ⟨9994101, by rfl⟩ : syracuseStep 26650937 = 19988203) B19988203
theorem B7891577 : Blo 1642020 7891577 := bstep (se 2 (by rfl) ⟨2959341, by rfl⟩ : syracuseStep 7891577 = 5918683) B5918683
theorem B1642399 : Blo 1642020 1642399 := bstep (se 1 (by rfl) ⟨1231799, by rfl⟩ : syracuseStep 1642399 = 2463599) B2463599
theorem B7016375 : Blo 1642020 7016375 := bstep (se 1 (by rfl) ⟨5262281, by rfl⟩ : syracuseStep 7016375 = 10524563) B10524563
theorem B9359495 : Blo 1642020 9359495 := bstep (se 1 (by rfl) ⟨7019621, by rfl⟩ : syracuseStep 9359495 = 14039243) B14039243
theorem B13316359 : Blo 1642020 13316359 := bstep (se 1 (by rfl) ⟨9987269, by rfl⟩ : syracuseStep 13316359 = 19974539) B19974539
theorem B1642823 : Blo 1642020 1642823 := bstep (se 1 (by rfl) ⟨1232117, by rfl⟩ : syracuseStep 1642823 = 2464235) B2464235
theorem B2339327 : Blo 1642020 2339327 := bstep (se 1 (by rfl) ⟨1754495, by rfl⟩ : syracuseStep 2339327 = 3508991) B3508991
theorem B7017263 : Blo 1642020 7017263 := bstep (se 1 (by rfl) ⟨5262947, by rfl⟩ : syracuseStep 7017263 = 10525895) B10525895
theorem B14979917 : Blo 1642020 14979917 := bstep (se 3 (by rfl) ⟨2808734, by rfl⟩ : syracuseStep 14979917 = 5617469) B5617469
theorem B1643519 : Blo 1642020 1643519 := bstep (se 1 (by rfl) ⟨1232639, by rfl⟩ : syracuseStep 1643519 = 2465279) B2465279
theorem B1643847 : Blo 1642020 1643847 := bstep (se 1 (by rfl) ⟨1232885, by rfl⟩ : syracuseStep 1643847 = 2465771) B2465771
theorem B1643879 : Blo 1642020 1643879 := bstep (se 1 (by rfl) ⟨1232909, by rfl⟩ : syracuseStep 1643879 = 2465819) B2465819
theorem B26662355 : Blo 1642020 26662355 := bstep (se 1 (by rfl) ⟨19996766, by rfl⟩ : syracuseStep 26662355 = 39993533) B39993533
theorem B40507037 : Blo 1642020 40507037 := bstep (se 3 (by rfl) ⟨7595069, by rfl⟩ : syracuseStep 40507037 = 15190139) B15190139
theorem B5543585 : Blo 1642020 5543585 := bstep (se 2 (by rfl) ⟨2078844, by rfl⟩ : syracuseStep 5543585 = 4157689) B4157689
theorem B64919357 : Blo 1642020 64919357 := bstep (se 3 (by rfl) ⟨12172379, by rfl⟩ : syracuseStep 64919357 = 24344759) B24344759
theorem B5543963 : Blo 1642020 5543963 := bstep (se 1 (by rfl) ⟨4157972, by rfl⟩ : syracuseStep 5543963 = 8315945) B8315945
theorem B3119771 : Blo 1642020 3119771 := bstep (se 1 (by rfl) ⟨2339828, by rfl⟩ : syracuseStep 3119771 = 4679657) B4679657
theorem B8216025965 : Blo 1642020 8216025965 := bstep (se 3 (by rfl) ⟨1540504868, by rfl⟩ : syracuseStep 8216025965 = 3081009737) B3081009737
theorem B4160585 : Blo 1642020 4160585 := bstep (se 2 (by rfl) ⟨1560219, by rfl⟩ : syracuseStep 4160585 = 3120439) B3120439
theorem B10132607 : Blo 1642020 10132607 := bstep (se 1 (by rfl) ⟨7599455, by rfl⟩ : syracuseStep 10132607 = 15198911) B15198911
theorem B9362729 : Blo 1642020 9362729 := bstep (se 2 (by rfl) ⟨3511023, by rfl⟩ : syracuseStep 9362729 = 7022047) B7022047
theorem B53272039 : Blo 1642020 53272039 := bstep (se 1 (by rfl) ⟨39954029, by rfl⟩ : syracuseStep 53272039 = 79908059) B79908059
theorem B2465627 : Blo 1642020 2465627 := bstep (se 1 (by rfl) ⟨1849220, by rfl⟩ : syracuseStep 2465627 = 3698441) B3698441
theorem B4678175 : Blo 1642020 4678175 := bstep (se 1 (by rfl) ⟨3508631, by rfl⟩ : syracuseStep 4678175 = 7017263) B7017263
theorem B3695723 : Blo 1642020 3695723 := bstep (se 1 (by rfl) ⟨2771792, by rfl⟩ : syracuseStep 3695723 = 5543585) B5543585
theorem B43279571 : Blo 1642020 43279571 := bstep (se 1 (by rfl) ⟨32459678, by rfl⟩ : syracuseStep 43279571 = 64919357) B64919357
theorem B3695975 : Blo 1642020 3695975 := bstep (se 1 (by rfl) ⟨2771981, by rfl⟩ : syracuseStep 3695975 = 5543963) B5543963
theorem B5261051 : Blo 1642020 5261051 := bstep (se 1 (by rfl) ⟨3945788, by rfl⟩ : syracuseStep 5261051 = 7891577) B7891577
theorem B39946445 : Blo 1642020 39946445 := bstep (se 3 (by rfl) ⟨7489958, by rfl⟩ : syracuseStep 39946445 = 14979917) B14979917
theorem B23685803 : Blo 1642020 23685803 := bstep (se 1 (by rfl) ⟨17764352, by rfl⟩ : syracuseStep 23685803 = 35528705) B35528705
theorem B17755145 : Blo 1642020 17755145 := bstep (se 2 (by rfl) ⟨6658179, by rfl⟩ : syracuseStep 17755145 = 13316359) B13316359
theorem B2960639 : Blo 1642020 2960639 := bstep (se 1 (by rfl) ⟨2220479, by rfl⟩ : syracuseStep 2960639 = 4440959) B4440959
theorem B4500893 : Blo 1642020 4500893 := bstep (se 3 (by rfl) ⟨843917, by rfl⟩ : syracuseStep 4500893 = 1687835) B1687835
theorem B27004691 : Blo 1642020 27004691 := bstep (se 1 (by rfl) ⟨20253518, by rfl⟩ : syracuseStep 27004691 = 40507037) B40507037
theorem B6238205 : Blo 1642020 6238205 := bstep (se 3 (by rfl) ⟨1169663, by rfl⟩ : syracuseStep 6238205 = 2339327) B2339327
theorem B71029385 : Blo 1642020 71029385 := bstep (se 2 (by rfl) ⟨26636019, by rfl⟩ : syracuseStep 71029385 = 53272039) B53272039
theorem B2773723 : Blo 1642020 2773723 := bstep (se 1 (by rfl) ⟨2080292, by rfl⟩ : syracuseStep 2773723 = 4160585) B4160585
theorem B6755071 : Blo 1642020 6755071 := bstep (se 1 (by rfl) ⟨5066303, by rfl⟩ : syracuseStep 6755071 = 10132607) B10132607
theorem B1643751 : Blo 1642020 1643751 := bstep (se 1 (by rfl) ⟨1232813, by rfl⟩ : syracuseStep 1643751 = 2465627) B2465627
theorem B6239663 : Blo 1642020 6239663 := bstep (se 1 (by rfl) ⟨4679747, by rfl⟩ : syracuseStep 6239663 = 9359495) B9359495
theorem B2463167 : Blo 1642020 2463167 := bstep (se 1 (by rfl) ⟨1847375, by rfl⟩ : syracuseStep 2463167 = 3694751) B3694751
theorem B2463287 : Blo 1642020 2463287 := bstep (se 1 (by rfl) ⟨1847465, by rfl⟩ : syracuseStep 2463287 = 3694931) B3694931
theorem B3118655 : Blo 1642020 3118655 := bstep (se 1 (by rfl) ⟨2338991, by rfl⟩ : syracuseStep 3118655 = 4677983) B4677983
theorem B2463359 : Blo 1642020 2463359 := bstep (se 1 (by rfl) ⟨1847519, by rfl⟩ : syracuseStep 2463359 = 3695039) B3695039
theorem B7018751 : Blo 1642020 7018751 := bstep (se 1 (by rfl) ⟨5264063, by rfl⟩ : syracuseStep 7018751 = 10528127) B10528127
theorem B17774903 : Blo 1642020 17774903 := bstep (se 1 (by rfl) ⟨13331177, by rfl⟩ : syracuseStep 17774903 = 26662355) B26662355
theorem B2464511 : Blo 1642020 2464511 := bstep (se 1 (by rfl) ⟨1848383, by rfl⟩ : syracuseStep 2464511 = 3696767) B3696767
theorem B17767291 : Blo 1642020 17767291 := bstep (se 1 (by rfl) ⟨13325468, by rfl⟩ : syracuseStep 17767291 = 26650937) B26650937
theorem B2079847 : Blo 1642020 2079847 := bstep (se 1 (by rfl) ⟨1559885, by rfl⟩ : syracuseStep 2079847 = 3119771) B3119771
theorem B5477350643 : Blo 1642020 5477350643 := bstep (se 1 (by rfl) ⟨4108012982, by rfl⟩ : syracuseStep 5477350643 = 8216025965) B8216025965
theorem B6241819 : Blo 1642020 6241819 := bstep (se 1 (by rfl) ⟨4681364, by rfl⟩ : syracuseStep 6241819 = 9362729) B9362729
theorem B4677583 : Blo 1642020 4677583 := bstep (se 1 (by rfl) ⟨3508187, by rfl⟩ : syracuseStep 4677583 = 7016375) B7016375
theorem B28853047 : Blo 1642020 28853047 := bstep (se 1 (by rfl) ⟨21639785, by rfl⟩ : syracuseStep 28853047 = 43279571) B43279571
theorem B47399741 : Blo 1642020 47399741 := bstep (se 3 (by rfl) ⟨8887451, by rfl⟩ : syracuseStep 47399741 = 17774903) B17774903
theorem B4679167 : Blo 1642020 4679167 := bstep (se 1 (by rfl) ⟨3509375, by rfl⟩ : syracuseStep 4679167 = 7018751) B7018751
theorem B3000595 : Blo 1642020 3000595 := bstep (se 1 (by rfl) ⟨2250446, by rfl⟩ : syracuseStep 3000595 = 4500893) B4500893
theorem B6236777 : Blo 1642020 6236777 := bstep (se 2 (by rfl) ⟨2338791, by rfl⟩ : syracuseStep 6236777 = 4677583) B4677583
theorem B47352923 : Blo 1642020 47352923 := bstep (se 1 (by rfl) ⟨35514692, by rfl⟩ : syracuseStep 47352923 = 71029385) B71029385
theorem B3698297 : Blo 1642020 3698297 := bstep (se 2 (by rfl) ⟨1386861, by rfl⟩ : syracuseStep 3698297 = 2773723) B2773723
theorem B1642111 : Blo 1642020 1642111 := bstep (se 1 (by rfl) ⟨1231583, by rfl⟩ : syracuseStep 1642111 = 2463167) B2463167
theorem B9006761 : Blo 1642020 9006761 := bstep (se 2 (by rfl) ⟨3377535, by rfl⟩ : syracuseStep 9006761 = 6755071) B6755071
theorem B1642191 : Blo 1642020 1642191 := bstep (se 1 (by rfl) ⟨1231643, by rfl⟩ : syracuseStep 1642191 = 2463287) B2463287
theorem B1642239 : Blo 1642020 1642239 := bstep (se 1 (by rfl) ⟨1231679, by rfl⟩ : syracuseStep 1642239 = 2463359) B2463359
theorem B2773129 : Blo 1642020 2773129 := bstep (se 2 (by rfl) ⟨1039923, by rfl⟩ : syracuseStep 2773129 = 2079847) B2079847
theorem B15790535 : Blo 1642020 15790535 := bstep (se 1 (by rfl) ⟨11842901, by rfl⟩ : syracuseStep 15790535 = 23685803) B23685803
theorem B1643007 : Blo 1642020 1643007 := bstep (se 1 (by rfl) ⟨1232255, by rfl⟩ : syracuseStep 1643007 = 2464511) B2464511
theorem B14029469 : Blo 1642020 14029469 := bstep (se 3 (by rfl) ⟨2630525, by rfl⟩ : syracuseStep 14029469 = 5261051) B5261051
theorem B18003127 : Blo 1642020 18003127 := bstep (se 1 (by rfl) ⟨13502345, by rfl⟩ : syracuseStep 18003127 = 27004691) B27004691
theorem B4158803 : Blo 1642020 4158803 := bstep (se 1 (by rfl) ⟨3119102, by rfl⟩ : syracuseStep 4158803 = 6238205) B6238205
theorem B2463815 : Blo 1642020 2463815 := bstep (se 1 (by rfl) ⟨1847861, by rfl⟩ : syracuseStep 2463815 = 3695723) B3695723
theorem B2463983 : Blo 1642020 2463983 := bstep (se 1 (by rfl) ⟨1847987, by rfl⟩ : syracuseStep 2463983 = 3695975) B3695975
theorem B4159775 : Blo 1642020 4159775 := bstep (se 1 (by rfl) ⟨3119831, by rfl⟩ : syracuseStep 4159775 = 6239663) B6239663
theorem B2079103 : Blo 1642020 2079103 := bstep (se 1 (by rfl) ⟨1559327, by rfl⟩ : syracuseStep 2079103 = 3118655) B3118655
theorem B23689721 : Blo 1642020 23689721 := bstep (se 2 (by rfl) ⟨8883645, by rfl⟩ : syracuseStep 23689721 = 17767291) B17767291
theorem B12475133 : Blo 1642020 12475133 := bstep (se 3 (by rfl) ⟨2339087, by rfl⟩ : syracuseStep 12475133 = 4678175) B4678175
theorem B26630963 : Blo 1642020 26630963 := bstep (se 1 (by rfl) ⟨19973222, by rfl⟩ : syracuseStep 26630963 = 39946445) B39946445
theorem B11836763 : Blo 1642020 11836763 := bstep (se 1 (by rfl) ⟨8877572, by rfl⟩ : syracuseStep 11836763 = 17755145) B17755145
theorem B8322425 : Blo 1642020 8322425 := bstep (se 2 (by rfl) ⟨3120909, by rfl⟩ : syracuseStep 8322425 = 6241819) B6241819
theorem B3651567095 : Blo 1642020 3651567095 := bstep (se 1 (by rfl) ⟨2738675321, by rfl⟩ : syracuseStep 3651567095 = 5477350643) B5477350643
theorem B1973759 : Blo 1642020 1973759 := bstep (se 1 (by rfl) ⟨1480319, by rfl⟩ : syracuseStep 1973759 = 2960639) B2960639
theorem B10527023 : Blo 1642020 10527023 := bstep (se 1 (by rfl) ⟨7895267, by rfl⟩ : syracuseStep 10527023 = 15790535) B15790535
theorem B64012693 : Blo 1642020 64012693 := bstep (se 6 (by rfl) ⟨1500297, by rfl⟩ : syracuseStep 64012693 = 3000595) B3000595
theorem B38470729 : Blo 1642020 38470729 := bstep (se 2 (by rfl) ⟨14426523, by rfl⟩ : syracuseStep 38470729 = 28853047) B28853047
theorem B24004169 : Blo 1642020 24004169 := bstep (se 2 (by rfl) ⟨9001563, by rfl⟩ : syracuseStep 24004169 = 18003127) B18003127
theorem B8316755 : Blo 1642020 8316755 := bstep (se 1 (by rfl) ⟨6237566, by rfl⟩ : syracuseStep 8316755 = 12475133) B12475133
theorem B17753975 : Blo 1642020 17753975 := bstep (se 1 (by rfl) ⟨13315481, by rfl⟩ : syracuseStep 17753975 = 26630963) B26630963
theorem B7891175 : Blo 1642020 7891175 := bstep (se 1 (by rfl) ⟨5918381, by rfl⟩ : syracuseStep 7891175 = 11836763) B11836763
theorem B5548283 : Blo 1642020 5548283 := bstep (se 1 (by rfl) ⟨4161212, by rfl⟩ : syracuseStep 5548283 = 8322425) B8322425
theorem B2434378063 : Blo 1642020 2434378063 := bstep (se 1 (by rfl) ⟨1825783547, by rfl⟩ : syracuseStep 2434378063 = 3651567095) B3651567095
theorem B3697505 : Blo 1642020 3697505 := bstep (se 2 (by rfl) ⟨1386564, by rfl⟩ : syracuseStep 3697505 = 2773129) B2773129
theorem B2772137 : Blo 1642020 2772137 := bstep (se 2 (by rfl) ⟨1039551, by rfl⟩ : syracuseStep 2772137 = 2079103) B2079103
theorem B31599827 : Blo 1642020 31599827 := bstep (se 1 (by rfl) ⟨23699870, by rfl⟩ : syracuseStep 31599827 = 47399741) B47399741
theorem B2772535 : Blo 1642020 2772535 := bstep (se 1 (by rfl) ⟨2079401, by rfl⟩ : syracuseStep 2772535 = 4158803) B4158803
theorem B1642543 : Blo 1642020 1642543 := bstep (se 1 (by rfl) ⟨1231907, by rfl⟩ : syracuseStep 1642543 = 2463815) B2463815
theorem B1642655 : Blo 1642020 1642655 := bstep (se 1 (by rfl) ⟨1231991, by rfl⟩ : syracuseStep 1642655 = 2463983) B2463983
theorem B2773183 : Blo 1642020 2773183 := bstep (se 1 (by rfl) ⟨2079887, by rfl⟩ : syracuseStep 2773183 = 4159775) B4159775
theorem B4157851 : Blo 1642020 4157851 := bstep (se 1 (by rfl) ⟨3118388, by rfl⟩ : syracuseStep 4157851 = 6236777) B6236777
theorem B6238889 : Blo 1642020 6238889 := bstep (se 2 (by rfl) ⟨2339583, by rfl⟩ : syracuseStep 6238889 = 4679167) B4679167
theorem B31568615 : Blo 1642020 31568615 := bstep (se 1 (by rfl) ⟨23676461, by rfl⟩ : syracuseStep 31568615 = 47352923) B47352923
theorem B9352979 : Blo 1642020 9352979 := bstep (se 1 (by rfl) ⟨7014734, by rfl⟩ : syracuseStep 9352979 = 14029469) B14029469
theorem B15793147 : Blo 1642020 15793147 := bstep (se 1 (by rfl) ⟨11844860, by rfl⟩ : syracuseStep 15793147 = 23689721) B23689721
theorem B2465531 : Blo 1642020 2465531 := bstep (se 1 (by rfl) ⟨1849148, by rfl⟩ : syracuseStep 2465531 = 3698297) B3698297
theorem B6004507 : Blo 1642020 6004507 := bstep (se 1 (by rfl) ⟨4503380, by rfl⟩ : syracuseStep 6004507 = 9006761) B9006761
theorem B21053429 : Blo 1642020 21053429 := bstep (se 5 (by rfl) ⟨986879, by rfl⟩ : syracuseStep 21053429 = 1973759) B1973759
theorem B21045743 : Blo 1642020 21045743 := bstep (se 1 (by rfl) ⟨15784307, by rfl⟩ : syracuseStep 21045743 = 31568615) B31568615
theorem B6235319 : Blo 1642020 6235319 := bstep (se 1 (by rfl) ⟨4676489, by rfl⟩ : syracuseStep 6235319 = 9352979) B9352979
theorem B5260783 : Blo 1642020 5260783 := bstep (se 1 (by rfl) ⟨3945587, by rfl⟩ : syracuseStep 5260783 = 7891175) B7891175
theorem B3696713 : Blo 1642020 3696713 := bstep (se 2 (by rfl) ⟨1386267, by rfl⟩ : syracuseStep 3696713 = 2772535) B2772535
theorem B8006009 : Blo 1642020 8006009 := bstep (se 2 (by rfl) ⟨3002253, by rfl⟩ : syracuseStep 8006009 = 6004507) B6004507
theorem B14035619 : Blo 1642020 14035619 := bstep (se 1 (by rfl) ⟨10526714, by rfl⟩ : syracuseStep 14035619 = 21053429) B21053429
theorem B3697577 : Blo 1642020 3697577 := bstep (se 2 (by rfl) ⟨1386591, by rfl⟩ : syracuseStep 3697577 = 2773183) B2773183
theorem B3245837417 : Blo 1642020 3245837417 := bstep (se 2 (by rfl) ⟨1217189031, by rfl⟩ : syracuseStep 3245837417 = 2434378063) B2434378063
theorem B16002779 : Blo 1642020 16002779 := bstep (se 1 (by rfl) ⟨12002084, by rfl⟩ : syracuseStep 16002779 = 24004169) B24004169
theorem B21057529 : Blo 1642020 21057529 := bstep (se 2 (by rfl) ⟨7896573, by rfl⟩ : syracuseStep 21057529 = 15793147) B15793147
theorem B51294305 : Blo 1642020 51294305 := bstep (se 2 (by rfl) ⟨19235364, by rfl⟩ : syracuseStep 51294305 = 38470729) B38470729
theorem B3698855 : Blo 1642020 3698855 := bstep (se 1 (by rfl) ⟨2774141, by rfl⟩ : syracuseStep 3698855 = 5548283) B5548283
theorem B1848091 : Blo 1642020 1848091 := bstep (se 1 (by rfl) ⟨1386068, by rfl⟩ : syracuseStep 1848091 = 2772137) B2772137
theorem B21066551 : Blo 1642020 21066551 := bstep (se 1 (by rfl) ⟨15799913, by rfl⟩ : syracuseStep 21066551 = 31599827) B31599827
theorem B1643687 : Blo 1642020 1643687 := bstep (se 1 (by rfl) ⟨1232765, by rfl⟩ : syracuseStep 1643687 = 2465531) B2465531
theorem B7018015 : Blo 1642020 7018015 := bstep (se 1 (by rfl) ⟨5263511, by rfl⟩ : syracuseStep 7018015 = 10527023) B10527023
theorem B4159259 : Blo 1642020 4159259 := bstep (se 1 (by rfl) ⟨3119444, by rfl⟩ : syracuseStep 4159259 = 6238889) B6238889
theorem B85350257 : Blo 1642020 85350257 := bstep (se 2 (by rfl) ⟨32006346, by rfl⟩ : syracuseStep 85350257 = 64012693) B64012693
theorem B5543801 : Blo 1642020 5543801 := bstep (se 2 (by rfl) ⟨2078925, by rfl⟩ : syracuseStep 5543801 = 4157851) B4157851
theorem B5544503 : Blo 1642020 5544503 := bstep (se 1 (by rfl) ⟨4158377, by rfl⟩ : syracuseStep 5544503 = 8316755) B8316755
theorem B11835983 : Blo 1642020 11835983 := bstep (se 1 (by rfl) ⟨8876987, by rfl⟩ : syracuseStep 11835983 = 17753975) B17753975
theorem B2465003 : Blo 1642020 2465003 := bstep (se 1 (by rfl) ⟨1848752, by rfl⟩ : syracuseStep 2465003 = 3697505) B3697505
theorem B2465903 : Blo 1642020 2465903 := bstep (se 1 (by rfl) ⟨1849427, by rfl⟩ : syracuseStep 2465903 = 3698855) B3698855
theorem B3695867 : Blo 1642020 3695867 := bstep (se 1 (by rfl) ⟨2771900, by rfl⟩ : syracuseStep 3695867 = 5543801) B5543801
theorem B3696335 : Blo 1642020 3696335 := bstep (se 1 (by rfl) ⟨2772251, by rfl⟩ : syracuseStep 3696335 = 5544503) B5544503
theorem B7890655 : Blo 1642020 7890655 := bstep (se 1 (by rfl) ⟨5917991, by rfl⟩ : syracuseStep 7890655 = 11835983) B11835983
theorem B9357079 : Blo 1642020 9357079 := bstep (se 1 (by rfl) ⟨7017809, by rfl⟩ : syracuseStep 9357079 = 14035619) B14035619
theorem B42674077 : Blo 1642020 42674077 := bstep (se 3 (by rfl) ⟨8001389, by rfl⟩ : syracuseStep 42674077 = 16002779) B16002779
theorem B7014377 : Blo 1642020 7014377 := bstep (se 2 (by rfl) ⟨2630391, by rfl⟩ : syracuseStep 7014377 = 5260783) B5260783
theorem B9357353 : Blo 1642020 9357353 := bstep (se 2 (by rfl) ⟨3509007, by rfl⟩ : syracuseStep 9357353 = 7018015) B7018015
theorem B28076705 : Blo 1642020 28076705 := bstep (se 2 (by rfl) ⟨10528764, by rfl⟩ : syracuseStep 28076705 = 21057529) B21057529
theorem B34196203 : Blo 1642020 34196203 := bstep (se 1 (by rfl) ⟨25647152, by rfl⟩ : syracuseStep 34196203 = 51294305) B51294305
theorem B14044367 : Blo 1642020 14044367 := bstep (se 1 (by rfl) ⟨10533275, by rfl⟩ : syracuseStep 14044367 = 21066551) B21066551
theorem B4156879 : Blo 1642020 4156879 := bstep (se 1 (by rfl) ⟨3117659, by rfl⟩ : syracuseStep 4156879 = 6235319) B6235319
theorem B2772839 : Blo 1642020 2772839 := bstep (se 1 (by rfl) ⟨2079629, by rfl⟩ : syracuseStep 2772839 = 4159259) B4159259
theorem B85397429 : Blo 1642020 85397429 := bstep (se 5 (by rfl) ⟨4003004, by rfl⟩ : syracuseStep 85397429 = 8006009) B8006009
theorem B1643335 : Blo 1642020 1643335 := bstep (se 1 (by rfl) ⟨1232501, by rfl⟩ : syracuseStep 1643335 = 2465003) B2465003
theorem B14030495 : Blo 1642020 14030495 := bstep (se 1 (by rfl) ⟨10522871, by rfl⟩ : syracuseStep 14030495 = 21045743) B21045743
theorem B2464121 : Blo 1642020 2464121 := bstep (se 2 (by rfl) ⟨924045, by rfl⟩ : syracuseStep 2464121 = 1848091) B1848091
theorem B56900171 : Blo 1642020 56900171 := bstep (se 1 (by rfl) ⟨42675128, by rfl⟩ : syracuseStep 56900171 = 85350257) B85350257
theorem B2464475 : Blo 1642020 2464475 := bstep (se 1 (by rfl) ⟨1848356, by rfl⟩ : syracuseStep 2464475 = 3696713) B3696713
theorem B2465051 : Blo 1642020 2465051 := bstep (se 1 (by rfl) ⟨1848788, by rfl⟩ : syracuseStep 2465051 = 3697577) B3697577
theorem B2163891611 : Blo 1642020 2163891611 := bstep (se 1 (by rfl) ⟨1622918708, by rfl⟩ : syracuseStep 2163891611 = 3245837417) B3245837417
theorem B10520873 : Blo 1642020 10520873 := bstep (se 2 (by rfl) ⟨3945327, by rfl⟩ : syracuseStep 10520873 = 7890655) B7890655
theorem B6238235 : Blo 1642020 6238235 := bstep (se 1 (by rfl) ⟨4678676, by rfl⟩ : syracuseStep 6238235 = 9357353) B9357353
theorem B1642747 : Blo 1642020 1642747 := bstep (se 1 (by rfl) ⟨1232060, by rfl⟩ : syracuseStep 1642747 = 2464121) B2464121
theorem B37933447 : Blo 1642020 37933447 := bstep (se 1 (by rfl) ⟨28450085, by rfl⟩ : syracuseStep 37933447 = 56900171) B56900171
theorem B1642983 : Blo 1642020 1642983 := bstep (se 1 (by rfl) ⟨1232237, by rfl⟩ : syracuseStep 1642983 = 2464475) B2464475
theorem B5542505 : Blo 1642020 5542505 := bstep (se 2 (by rfl) ⟨2078439, by rfl⟩ : syracuseStep 5542505 = 4156879) B4156879
theorem B1643367 : Blo 1642020 1643367 := bstep (se 1 (by rfl) ⟨1232525, by rfl⟩ : syracuseStep 1643367 = 2465051) B2465051
theorem B56898769 : Blo 1642020 56898769 := bstep (se 2 (by rfl) ⟨21337038, by rfl⟩ : syracuseStep 56898769 = 42674077) B42674077
theorem B1848559 : Blo 1642020 1848559 := bstep (se 1 (by rfl) ⟨1386419, by rfl⟩ : syracuseStep 1848559 = 2772839) B2772839
theorem B56931619 : Blo 1642020 56931619 := bstep (se 1 (by rfl) ⟨42698714, by rfl⟩ : syracuseStep 56931619 = 85397429) B85397429
theorem B1643935 : Blo 1642020 1643935 := bstep (se 1 (by rfl) ⟨1232951, by rfl⟩ : syracuseStep 1643935 = 2465903) B2465903
theorem B2463911 : Blo 1642020 2463911 := bstep (se 1 (by rfl) ⟨1847933, by rfl⟩ : syracuseStep 2463911 = 3695867) B3695867
theorem B45594937 : Blo 1642020 45594937 := bstep (se 2 (by rfl) ⟨17098101, by rfl⟩ : syracuseStep 45594937 = 34196203) B34196203
theorem B9353663 : Blo 1642020 9353663 := bstep (se 1 (by rfl) ⟨7015247, by rfl⟩ : syracuseStep 9353663 = 14030495) B14030495
theorem B2464223 : Blo 1642020 2464223 := bstep (se 1 (by rfl) ⟨1848167, by rfl⟩ : syracuseStep 2464223 = 3696335) B3696335
theorem B4676251 : Blo 1642020 4676251 := bstep (se 1 (by rfl) ⟨3507188, by rfl⟩ : syracuseStep 4676251 = 7014377) B7014377
theorem B18717803 : Blo 1642020 18717803 := bstep (se 1 (by rfl) ⟨14038352, by rfl⟩ : syracuseStep 18717803 = 28076705) B28076705
theorem B9362911 : Blo 1642020 9362911 := bstep (se 1 (by rfl) ⟨7022183, by rfl⟩ : syracuseStep 9362911 = 14044367) B14044367
theorem B1442594407 : Blo 1642020 1442594407 := bstep (se 1 (by rfl) ⟨1081945805, by rfl⟩ : syracuseStep 1442594407 = 2163891611) B2163891611
theorem B12476105 : Blo 1642020 12476105 := bstep (se 2 (by rfl) ⟨4678539, by rfl⟩ : syracuseStep 12476105 = 9357079) B9357079
theorem B3695003 : Blo 1642020 3695003 := bstep (se 1 (by rfl) ⟨2771252, by rfl⟩ : syracuseStep 3695003 = 5542505) B5542505
theorem B60793249 : Blo 1642020 60793249 := bstep (se 2 (by rfl) ⟨22797468, by rfl⟩ : syracuseStep 60793249 = 45594937) B45594937
theorem B50577929 : Blo 1642020 50577929 := bstep (se 2 (by rfl) ⟨18966723, by rfl⟩ : syracuseStep 50577929 = 37933447) B37933447
theorem B6235001 : Blo 1642020 6235001 := bstep (se 2 (by rfl) ⟨2338125, by rfl⟩ : syracuseStep 6235001 = 4676251) B4676251
theorem B7013915 : Blo 1642020 7013915 := bstep (se 1 (by rfl) ⟨5260436, by rfl⟩ : syracuseStep 7013915 = 10520873) B10520873
theorem B6235775 : Blo 1642020 6235775 := bstep (se 1 (by rfl) ⟨4676831, by rfl⟩ : syracuseStep 6235775 = 9353663) B9353663
theorem B75908825 : Blo 1642020 75908825 := bstep (se 2 (by rfl) ⟨28465809, by rfl⟩ : syracuseStep 75908825 = 56931619) B56931619
theorem B12478535 : Blo 1642020 12478535 := bstep (se 1 (by rfl) ⟨9358901, by rfl⟩ : syracuseStep 12478535 = 18717803) B18717803
theorem B1923459209 : Blo 1642020 1923459209 := bstep (se 2 (by rfl) ⟨721297203, by rfl⟩ : syracuseStep 1923459209 = 1442594407) B1442594407
theorem B8317403 : Blo 1642020 8317403 := bstep (se 1 (by rfl) ⟨6238052, by rfl⟩ : syracuseStep 8317403 = 12476105) B12476105
theorem B1642607 : Blo 1642020 1642607 := bstep (se 1 (by rfl) ⟨1231955, by rfl⟩ : syracuseStep 1642607 = 2463911) B2463911
theorem B1642815 : Blo 1642020 1642815 := bstep (se 1 (by rfl) ⟨1232111, by rfl⟩ : syracuseStep 1642815 = 2464223) B2464223
theorem B4158823 : Blo 1642020 4158823 := bstep (se 1 (by rfl) ⟨3119117, by rfl⟩ : syracuseStep 4158823 = 6238235) B6238235
theorem B75865025 : Blo 1642020 75865025 := bstep (se 2 (by rfl) ⟨28449384, by rfl⟩ : syracuseStep 75865025 = 56898769) B56898769
theorem B2464745 : Blo 1642020 2464745 := bstep (se 2 (by rfl) ⟨924279, by rfl⟩ : syracuseStep 2464745 = 1848559) B1848559
theorem B12483881 : Blo 1642020 12483881 := bstep (se 2 (by rfl) ⟨4681455, by rfl⟩ : syracuseStep 12483881 = 9362911) B9362911
theorem B33718619 : Blo 1642020 33718619 := bstep (se 1 (by rfl) ⟨25288964, by rfl⟩ : syracuseStep 33718619 = 50577929) B50577929
theorem B4156667 : Blo 1642020 4156667 := bstep (se 1 (by rfl) ⟨3117500, by rfl⟩ : syracuseStep 4156667 = 6235001) B6235001
theorem B4157183 : Blo 1642020 4157183 := bstep (se 1 (by rfl) ⟨3117887, by rfl⟩ : syracuseStep 4157183 = 6235775) B6235775
theorem B50605883 : Blo 1642020 50605883 := bstep (se 1 (by rfl) ⟨37954412, by rfl⟩ : syracuseStep 50605883 = 75908825) B75908825
theorem B8319023 : Blo 1642020 8319023 := bstep (se 1 (by rfl) ⟨6239267, by rfl⟩ : syracuseStep 8319023 = 12478535) B12478535
theorem B1282306139 : Blo 1642020 1282306139 := bstep (se 1 (by rfl) ⟨961729604, by rfl⟩ : syracuseStep 1282306139 = 1923459209) B1923459209
theorem B1643163 : Blo 1642020 1643163 := bstep (se 1 (by rfl) ⟨1232372, by rfl⟩ : syracuseStep 1643163 = 2464745) B2464745
theorem B2463335 : Blo 1642020 2463335 := bstep (se 1 (by rfl) ⟨1847501, by rfl⟩ : syracuseStep 2463335 = 3695003) B3695003
theorem B81057665 : Blo 1642020 81057665 := bstep (se 2 (by rfl) ⟨30396624, by rfl⟩ : syracuseStep 81057665 = 60793249) B60793249
theorem B4675943 : Blo 1642020 4675943 := bstep (se 1 (by rfl) ⟨3506957, by rfl⟩ : syracuseStep 4675943 = 7013915) B7013915
theorem B5544935 : Blo 1642020 5544935 := bstep (se 1 (by rfl) ⟨4158701, by rfl⟩ : syracuseStep 5544935 = 8317403) B8317403
theorem B5545097 : Blo 1642020 5545097 := bstep (se 2 (by rfl) ⟨2079411, by rfl⟩ : syracuseStep 5545097 = 4158823) B4158823
theorem B50576683 : Blo 1642020 50576683 := bstep (se 1 (by rfl) ⟨37932512, by rfl⟩ : syracuseStep 50576683 = 75865025) B75865025
theorem B8322587 : Blo 1642020 8322587 := bstep (se 1 (by rfl) ⟨6241940, by rfl⟩ : syracuseStep 8322587 = 12483881) B12483881
theorem B5546015 : Blo 1642020 5546015 := bstep (se 1 (by rfl) ⟨4159511, by rfl⟩ : syracuseStep 5546015 = 8319023) B8319023
theorem B22479079 : Blo 1642020 22479079 := bstep (se 1 (by rfl) ⟨16859309, by rfl⟩ : syracuseStep 22479079 = 33718619) B33718619
theorem B3696623 : Blo 1642020 3696623 := bstep (se 1 (by rfl) ⟨2772467, by rfl⟩ : syracuseStep 3696623 = 5544935) B5544935
theorem B3696731 : Blo 1642020 3696731 := bstep (se 1 (by rfl) ⟨2772548, by rfl⟩ : syracuseStep 3696731 = 5545097) B5545097
theorem B2771111 : Blo 1642020 2771111 := bstep (se 1 (by rfl) ⟨2078333, by rfl⟩ : syracuseStep 2771111 = 4156667) B4156667
theorem B5548391 : Blo 1642020 5548391 := bstep (se 1 (by rfl) ⟨4161293, by rfl⟩ : syracuseStep 5548391 = 8322587) B8322587
theorem B2771455 : Blo 1642020 2771455 := bstep (se 1 (by rfl) ⟨2078591, by rfl⟩ : syracuseStep 2771455 = 4157183) B4157183
theorem B33737255 : Blo 1642020 33737255 := bstep (se 1 (by rfl) ⟨25302941, by rfl⟩ : syracuseStep 33737255 = 50605883) B50605883
theorem B854870759 : Blo 1642020 854870759 := bstep (se 1 (by rfl) ⟨641153069, by rfl⟩ : syracuseStep 854870759 = 1282306139) B1282306139
theorem B1642223 : Blo 1642020 1642223 := bstep (se 1 (by rfl) ⟨1231667, by rfl⟩ : syracuseStep 1642223 = 2463335) B2463335
theorem B54038443 : Blo 1642020 54038443 := bstep (se 1 (by rfl) ⟨40528832, by rfl⟩ : syracuseStep 54038443 = 81057665) B81057665
theorem B3117295 : Blo 1642020 3117295 := bstep (se 1 (by rfl) ⟨2337971, by rfl⟩ : syracuseStep 3117295 = 4675943) B4675943
theorem B67435577 : Blo 1642020 67435577 := bstep (se 2 (by rfl) ⟨25288341, by rfl⟩ : syracuseStep 67435577 = 50576683) B50576683
theorem B3695273 : Blo 1642020 3695273 := bstep (se 2 (by rfl) ⟨1385727, by rfl⟩ : syracuseStep 3695273 = 2771455) B2771455
theorem B72051257 : Blo 1642020 72051257 := bstep (se 2 (by rfl) ⟨27019221, by rfl⟩ : syracuseStep 72051257 = 54038443) B54038443
theorem B3697343 : Blo 1642020 3697343 := bstep (se 1 (by rfl) ⟨2773007, by rfl⟩ : syracuseStep 3697343 = 5546015) B5546015
theorem B4156393 : Blo 1642020 4156393 := bstep (se 2 (by rfl) ⟨1558647, by rfl⟩ : syracuseStep 4156393 = 3117295) B3117295
theorem B1847407 : Blo 1642020 1847407 := bstep (se 1 (by rfl) ⟨1385555, by rfl⟩ : syracuseStep 1847407 = 2771111) B2771111
theorem B3698927 : Blo 1642020 3698927 := bstep (se 1 (by rfl) ⟨2774195, by rfl⟩ : syracuseStep 3698927 = 5548391) B5548391
theorem B22491503 : Blo 1642020 22491503 := bstep (se 1 (by rfl) ⟨16868627, by rfl⟩ : syracuseStep 22491503 = 33737255) B33737255
theorem B569913839 : Blo 1642020 569913839 := bstep (se 1 (by rfl) ⟨427435379, by rfl⟩ : syracuseStep 569913839 = 854870759) B854870759
theorem B29972105 : Blo 1642020 29972105 := bstep (se 2 (by rfl) ⟨11239539, by rfl⟩ : syracuseStep 29972105 = 22479079) B22479079
theorem B2464415 : Blo 1642020 2464415 := bstep (se 1 (by rfl) ⟨1848311, by rfl⟩ : syracuseStep 2464415 = 3696623) B3696623
theorem B2464487 : Blo 1642020 2464487 := bstep (se 1 (by rfl) ⟨1848365, by rfl⟩ : syracuseStep 2464487 = 3696731) B3696731
theorem B44957051 : Blo 1642020 44957051 := bstep (se 1 (by rfl) ⟨33717788, by rfl⟩ : syracuseStep 44957051 = 67435577) B67435577
theorem B2465951 : Blo 1642020 2465951 := bstep (se 1 (by rfl) ⟨1849463, by rfl⟩ : syracuseStep 2465951 = 3698927) B3698927
theorem B19981403 : Blo 1642020 19981403 := bstep (se 1 (by rfl) ⟨14986052, by rfl⟩ : syracuseStep 19981403 = 29972105) B29972105
theorem B14994335 : Blo 1642020 14994335 := bstep (se 1 (by rfl) ⟨11245751, by rfl⟩ : syracuseStep 14994335 = 22491503) B22491503
theorem B5541857 : Blo 1642020 5541857 := bstep (se 2 (by rfl) ⟨2078196, by rfl⟩ : syracuseStep 5541857 = 4156393) B4156393
theorem B48034171 : Blo 1642020 48034171 := bstep (se 1 (by rfl) ⟨36025628, by rfl⟩ : syracuseStep 48034171 = 72051257) B72051257
theorem B1642943 : Blo 1642020 1642943 := bstep (se 1 (by rfl) ⟨1232207, by rfl⟩ : syracuseStep 1642943 = 2464415) B2464415
theorem B1642991 : Blo 1642020 1642991 := bstep (se 1 (by rfl) ⟨1232243, by rfl⟩ : syracuseStep 1642991 = 2464487) B2464487
theorem B29971367 : Blo 1642020 29971367 := bstep (se 1 (by rfl) ⟨22478525, by rfl⟩ : syracuseStep 29971367 = 44957051) B44957051
theorem B2463209 : Blo 1642020 2463209 := bstep (se 2 (by rfl) ⟨923703, by rfl⟩ : syracuseStep 2463209 = 1847407) B1847407
theorem B379942559 : Blo 1642020 379942559 := bstep (se 1 (by rfl) ⟨284956919, by rfl⟩ : syracuseStep 379942559 = 569913839) B569913839
theorem B2463515 : Blo 1642020 2463515 := bstep (se 1 (by rfl) ⟨1847636, by rfl⟩ : syracuseStep 2463515 = 3695273) B3695273
theorem B2464895 : Blo 1642020 2464895 := bstep (se 1 (by rfl) ⟨1848671, by rfl⟩ : syracuseStep 2464895 = 3697343) B3697343
theorem B64045561 : Blo 1642020 64045561 := bstep (se 2 (by rfl) ⟨24017085, by rfl⟩ : syracuseStep 64045561 = 48034171) B48034171
theorem B19980911 : Blo 1642020 19980911 := bstep (se 1 (by rfl) ⟨14985683, by rfl⟩ : syracuseStep 19980911 = 29971367) B29971367
theorem B13320935 : Blo 1642020 13320935 := bstep (se 1 (by rfl) ⟨9990701, by rfl⟩ : syracuseStep 13320935 = 19981403) B19981403
theorem B9996223 : Blo 1642020 9996223 := bstep (se 1 (by rfl) ⟨7497167, by rfl⟩ : syracuseStep 9996223 = 14994335) B14994335
theorem B1642139 : Blo 1642020 1642139 := bstep (se 1 (by rfl) ⟨1231604, by rfl⟩ : syracuseStep 1642139 = 2463209) B2463209
theorem B1642343 : Blo 1642020 1642343 := bstep (se 1 (by rfl) ⟨1231757, by rfl⟩ : syracuseStep 1642343 = 2463515) B2463515
theorem B1643263 : Blo 1642020 1643263 := bstep (se 1 (by rfl) ⟨1232447, by rfl⟩ : syracuseStep 1643263 = 2464895) B2464895
theorem B1643967 : Blo 1642020 1643967 := bstep (se 1 (by rfl) ⟨1232975, by rfl⟩ : syracuseStep 1643967 = 2465951) B2465951
theorem B253295039 : Blo 1642020 253295039 := bstep (se 1 (by rfl) ⟨189971279, by rfl⟩ : syracuseStep 253295039 = 379942559) B379942559
theorem B3694571 : Blo 1642020 3694571 := bstep (se 1 (by rfl) ⟨2770928, by rfl⟩ : syracuseStep 3694571 = 5541857) B5541857
theorem B13320607 : Blo 1642020 13320607 := bstep (se 1 (by rfl) ⟨9990455, by rfl⟩ : syracuseStep 13320607 = 19980911) B19980911
theorem B8880623 : Blo 1642020 8880623 := bstep (se 1 (by rfl) ⟨6660467, by rfl⟩ : syracuseStep 8880623 = 13320935) B13320935
theorem B85394081 : Blo 1642020 85394081 := bstep (se 2 (by rfl) ⟨32022780, by rfl⟩ : syracuseStep 85394081 = 64045561) B64045561
theorem B168863359 : Blo 1642020 168863359 := bstep (se 1 (by rfl) ⟨126647519, by rfl⟩ : syracuseStep 168863359 = 253295039) B253295039
theorem B2463047 : Blo 1642020 2463047 := bstep (se 1 (by rfl) ⟨1847285, by rfl⟩ : syracuseStep 2463047 = 3694571) B3694571
theorem B13328297 : Blo 1642020 13328297 := bstep (se 2 (by rfl) ⟨4998111, by rfl⟩ : syracuseStep 13328297 = 9996223) B9996223
theorem B17760809 : Blo 1642020 17760809 := bstep (se 2 (by rfl) ⟨6660303, by rfl⟩ : syracuseStep 17760809 = 13320607) B13320607
theorem B225151145 : Blo 1642020 225151145 := bstep (se 2 (by rfl) ⟨84431679, by rfl⟩ : syracuseStep 225151145 = 168863359) B168863359
theorem B56929387 : Blo 1642020 56929387 := bstep (se 1 (by rfl) ⟨42697040, by rfl⟩ : syracuseStep 56929387 = 85394081) B85394081
theorem B1642031 : Blo 1642020 1642031 := bstep (se 1 (by rfl) ⟨1231523, by rfl⟩ : syracuseStep 1642031 = 2463047) B2463047
theorem B8885531 : Blo 1642020 8885531 := bstep (se 1 (by rfl) ⟨6664148, by rfl⟩ : syracuseStep 8885531 = 13328297) B13328297
theorem B5920415 : Blo 1642020 5920415 := bstep (se 1 (by rfl) ⟨4440311, by rfl⟩ : syracuseStep 5920415 = 8880623) B8880623
theorem B5923687 : Blo 1642020 5923687 := bstep (se 1 (by rfl) ⟨4442765, by rfl⟩ : syracuseStep 5923687 = 8885531) B8885531
theorem B11840539 : Blo 1642020 11840539 := bstep (se 1 (by rfl) ⟨8880404, by rfl⟩ : syracuseStep 11840539 = 17760809) B17760809
theorem B2401612213 : Blo 1642020 2401612213 := bstep (se 5 (by rfl) ⟨112575572, by rfl⟩ : syracuseStep 2401612213 = 225151145) B225151145
theorem B3946943 : Blo 1642020 3946943 := bstep (se 1 (by rfl) ⟨2960207, by rfl⟩ : syracuseStep 3946943 = 5920415) B5920415
theorem B75905849 : Blo 1642020 75905849 := bstep (se 2 (by rfl) ⟨28464693, by rfl⟩ : syracuseStep 75905849 = 56929387) B56929387
theorem B7898249 : Blo 1642020 7898249 := bstep (se 2 (by rfl) ⟨2961843, by rfl⟩ : syracuseStep 7898249 = 5923687) B5923687
theorem B15787385 : Blo 1642020 15787385 := bstep (se 2 (by rfl) ⟨5920269, by rfl⟩ : syracuseStep 15787385 = 11840539) B11840539
theorem B2631295 : Blo 1642020 2631295 := bstep (se 1 (by rfl) ⟨1973471, by rfl⟩ : syracuseStep 2631295 = 3946943) B3946943
theorem B3202149617 : Blo 1642020 3202149617 := bstep (se 2 (by rfl) ⟨1200806106, by rfl⟩ : syracuseStep 3202149617 = 2401612213) B2401612213
theorem B202415597 : Blo 1642020 202415597 := bstep (se 3 (by rfl) ⟨37952924, by rfl⟩ : syracuseStep 202415597 = 75905849) B75905849
theorem B3508393 : Blo 1642020 3508393 := bstep (se 2 (by rfl) ⟨1315647, by rfl⟩ : syracuseStep 3508393 = 2631295) B2631295
theorem B2134766411 : Blo 1642020 2134766411 := bstep (se 1 (by rfl) ⟨1601074808, by rfl⟩ : syracuseStep 2134766411 = 3202149617) B3202149617
theorem B134943731 : Blo 1642020 134943731 := bstep (se 1 (by rfl) ⟨101207798, by rfl⟩ : syracuseStep 134943731 = 202415597) B202415597
theorem B5265499 : Blo 1642020 5265499 := bstep (se 1 (by rfl) ⟨3949124, by rfl⟩ : syracuseStep 5265499 = 7898249) B7898249
theorem B10524923 : Blo 1642020 10524923 := bstep (se 1 (by rfl) ⟨7893692, by rfl⟩ : syracuseStep 10524923 = 15787385) B15787385
theorem B7020665 : Blo 1642020 7020665 := bstep (se 2 (by rfl) ⟨2632749, by rfl⟩ : syracuseStep 7020665 = 5265499) B5265499
theorem B4677857 : Blo 1642020 4677857 := bstep (se 2 (by rfl) ⟨1754196, by rfl⟩ : syracuseStep 4677857 = 3508393) B3508393
theorem B7016615 : Blo 1642020 7016615 := bstep (se 1 (by rfl) ⟨5262461, by rfl⟩ : syracuseStep 7016615 = 10524923) B10524923
theorem B1423177607 : Blo 1642020 1423177607 := bstep (se 1 (by rfl) ⟨1067383205, by rfl⟩ : syracuseStep 1423177607 = 2134766411) B2134766411
theorem B89962487 : Blo 1642020 89962487 := bstep (se 1 (by rfl) ⟨67471865, by rfl⟩ : syracuseStep 89962487 = 134943731) B134943731
theorem B4677743 : Blo 1642020 4677743 := bstep (se 1 (by rfl) ⟨3508307, by rfl⟩ : syracuseStep 4677743 = 7016615) B7016615
theorem B59974991 : Blo 1642020 59974991 := bstep (se 1 (by rfl) ⟨44981243, by rfl⟩ : syracuseStep 59974991 = 89962487) B89962487
theorem B4680443 : Blo 1642020 4680443 := bstep (se 1 (by rfl) ⟨3510332, by rfl⟩ : syracuseStep 4680443 = 7020665) B7020665
theorem B948785071 : Blo 1642020 948785071 := bstep (se 1 (by rfl) ⟨711588803, by rfl⟩ : syracuseStep 948785071 = 1423177607) B1423177607
theorem B3118571 : Blo 1642020 3118571 := bstep (se 1 (by rfl) ⟨2338928, by rfl⟩ : syracuseStep 3118571 = 4677857) B4677857
theorem B1265046761 : Blo 1642020 1265046761 := bstep (se 2 (by rfl) ⟨474392535, by rfl⟩ : syracuseStep 1265046761 = 948785071) B948785071
theorem B3118495 : Blo 1642020 3118495 := bstep (se 1 (by rfl) ⟨2338871, by rfl⟩ : syracuseStep 3118495 = 4677743) B4677743
theorem B39983327 : Blo 1642020 39983327 := bstep (se 1 (by rfl) ⟨29987495, by rfl⟩ : syracuseStep 39983327 = 59974991) B59974991
theorem B2079047 : Blo 1642020 2079047 := bstep (se 1 (by rfl) ⟨1559285, by rfl⟩ : syracuseStep 2079047 = 3118571) B3118571
theorem B3120295 : Blo 1642020 3120295 := bstep (se 1 (by rfl) ⟨2340221, by rfl⟩ : syracuseStep 3120295 = 4680443) B4680443
theorem B4157993 : Blo 1642020 4157993 := bstep (se 2 (by rfl) ⟨1559247, by rfl⟩ : syracuseStep 4157993 = 3118495) B3118495
theorem B843364507 : Blo 1642020 843364507 := bstep (se 1 (by rfl) ⟨632523380, by rfl⟩ : syracuseStep 843364507 = 1265046761) B1265046761
theorem B5544125 : Blo 1642020 5544125 := bstep (se 3 (by rfl) ⟨1039523, by rfl⟩ : syracuseStep 5544125 = 2079047) B2079047
theorem B26655551 : Blo 1642020 26655551 := bstep (se 1 (by rfl) ⟨19991663, by rfl⟩ : syracuseStep 26655551 = 39983327) B39983327
theorem B4160393 : Blo 1642020 4160393 := bstep (se 2 (by rfl) ⟨1560147, by rfl⟩ : syracuseStep 4160393 = 3120295) B3120295
theorem B3696083 : Blo 1642020 3696083 := bstep (se 1 (by rfl) ⟨2772062, by rfl⟩ : syracuseStep 3696083 = 5544125) B5544125
theorem B17770367 : Blo 1642020 17770367 := bstep (se 1 (by rfl) ⟨13327775, by rfl⟩ : syracuseStep 17770367 = 26655551) B26655551
theorem B1124486009 : Blo 1642020 1124486009 := bstep (se 2 (by rfl) ⟨421682253, by rfl⟩ : syracuseStep 1124486009 = 843364507) B843364507
theorem B2771995 : Blo 1642020 2771995 := bstep (se 1 (by rfl) ⟨2078996, by rfl⟩ : syracuseStep 2771995 = 4157993) B4157993
theorem B2773595 : Blo 1642020 2773595 := bstep (se 1 (by rfl) ⟨2080196, by rfl⟩ : syracuseStep 2773595 = 4160393) B4160393
theorem B11846911 : Blo 1642020 11846911 := bstep (se 1 (by rfl) ⟨8885183, by rfl⟩ : syracuseStep 11846911 = 17770367) B17770367
theorem B3695993 : Blo 1642020 3695993 := bstep (se 2 (by rfl) ⟨1385997, by rfl⟩ : syracuseStep 3695993 = 2771995) B2771995
theorem B1849063 : Blo 1642020 1849063 := bstep (se 1 (by rfl) ⟨1386797, by rfl⟩ : syracuseStep 1849063 = 2773595) B2773595
theorem B2464055 : Blo 1642020 2464055 := bstep (se 1 (by rfl) ⟨1848041, by rfl⟩ : syracuseStep 2464055 = 3696083) B3696083
theorem B749657339 : Blo 1642020 749657339 := bstep (se 1 (by rfl) ⟨562243004, by rfl⟩ : syracuseStep 749657339 = 1124486009) B1124486009
theorem B15795881 : Blo 1642020 15795881 := bstep (se 2 (by rfl) ⟨5923455, by rfl⟩ : syracuseStep 15795881 = 11846911) B11846911
theorem B499771559 : Blo 1642020 499771559 := bstep (se 1 (by rfl) ⟨374828669, by rfl⟩ : syracuseStep 499771559 = 749657339) B749657339
theorem B1642703 : Blo 1642020 1642703 := bstep (se 1 (by rfl) ⟨1232027, by rfl⟩ : syracuseStep 1642703 = 2464055) B2464055
theorem B2463995 : Blo 1642020 2463995 := bstep (se 1 (by rfl) ⟨1847996, by rfl⟩ : syracuseStep 2463995 = 3695993) B3695993
theorem B2465417 : Blo 1642020 2465417 := bstep (se 2 (by rfl) ⟨924531, by rfl⟩ : syracuseStep 2465417 = 1849063) B1849063
theorem B10530587 : Blo 1642020 10530587 := bstep (se 1 (by rfl) ⟨7897940, by rfl⟩ : syracuseStep 10530587 = 15795881) B15795881
theorem B333181039 : Blo 1642020 333181039 := bstep (se 1 (by rfl) ⟨249885779, by rfl⟩ : syracuseStep 333181039 = 499771559) B499771559
theorem B1642663 : Blo 1642020 1642663 := bstep (se 1 (by rfl) ⟨1231997, by rfl⟩ : syracuseStep 1642663 = 2463995) B2463995
theorem B1643611 : Blo 1642020 1643611 := bstep (se 1 (by rfl) ⟨1232708, by rfl⟩ : syracuseStep 1643611 = 2465417) B2465417
theorem B444241385 : Blo 1642020 444241385 := bstep (se 2 (by rfl) ⟨166590519, by rfl⟩ : syracuseStep 444241385 = 333181039) B333181039
theorem B7020391 : Blo 1642020 7020391 := bstep (se 1 (by rfl) ⟨5265293, by rfl⟩ : syracuseStep 7020391 = 10530587) B10530587
theorem B296160923 : Blo 1642020 296160923 := bstep (se 1 (by rfl) ⟨222120692, by rfl⟩ : syracuseStep 296160923 = 444241385) B444241385
theorem B9360521 : Blo 1642020 9360521 := bstep (se 2 (by rfl) ⟨3510195, by rfl⟩ : syracuseStep 9360521 = 7020391) B7020391
theorem B197440615 : Blo 1642020 197440615 := bstep (se 1 (by rfl) ⟨148080461, by rfl⟩ : syracuseStep 197440615 = 296160923) B296160923
theorem B6240347 : Blo 1642020 6240347 := bstep (se 1 (by rfl) ⟨4680260, by rfl⟩ : syracuseStep 6240347 = 9360521) B9360521
theorem B263254153 : Blo 1642020 263254153 := bstep (se 2 (by rfl) ⟨98720307, by rfl⟩ : syracuseStep 263254153 = 197440615) B197440615
theorem B4160231 : Blo 1642020 4160231 := bstep (se 1 (by rfl) ⟨3120173, by rfl⟩ : syracuseStep 4160231 = 6240347) B6240347
theorem B351005537 : Blo 1642020 351005537 := bstep (se 2 (by rfl) ⟨131627076, by rfl⟩ : syracuseStep 351005537 = 263254153) B263254153
theorem B2773487 : Blo 1642020 2773487 := bstep (se 1 (by rfl) ⟨2080115, by rfl⟩ : syracuseStep 2773487 = 4160231) B4160231
theorem B1848991 : Blo 1642020 1848991 := bstep (se 1 (by rfl) ⟨1386743, by rfl⟩ : syracuseStep 1848991 = 2773487) B2773487
theorem B234003691 : Blo 1642020 234003691 := bstep (se 1 (by rfl) ⟨175502768, by rfl⟩ : syracuseStep 234003691 = 351005537) B351005537
theorem B312004921 : Blo 1642020 312004921 := bstep (se 2 (by rfl) ⟨117001845, by rfl⟩ : syracuseStep 312004921 = 234003691) B234003691
theorem B2465321 : Blo 1642020 2465321 := bstep (se 2 (by rfl) ⟨924495, by rfl⟩ : syracuseStep 2465321 = 1848991) B1848991
theorem B416006561 : Blo 1642020 416006561 := bstep (se 2 (by rfl) ⟨156002460, by rfl⟩ : syracuseStep 416006561 = 312004921) B312004921
theorem B1643547 : Blo 1642020 1643547 := bstep (se 1 (by rfl) ⟨1232660, by rfl⟩ : syracuseStep 1643547 = 2465321) B2465321
theorem B1109350829 : Blo 1642020 1109350829 := bstep (se 3 (by rfl) ⟨208003280, by rfl⟩ : syracuseStep 1109350829 = 416006561) B416006561
theorem B739567219 : Blo 1642020 739567219 := bstep (se 1 (by rfl) ⟨554675414, by rfl⟩ : syracuseStep 739567219 = 1109350829) B1109350829
theorem B986089625 : Blo 1642020 986089625 := bstep (se 2 (by rfl) ⟨369783609, by rfl⟩ : syracuseStep 986089625 = 739567219) B739567219
theorem B657393083 : Blo 1642020 657393083 := bstep (se 1 (by rfl) ⟨493044812, by rfl⟩ : syracuseStep 657393083 = 986089625) B986089625
theorem B438262055 : Blo 1642020 438262055 := bstep (se 1 (by rfl) ⟨328696541, by rfl⟩ : syracuseStep 438262055 = 657393083) B657393083
theorem B292174703 : Blo 1642020 292174703 := bstep (se 1 (by rfl) ⟨219131027, by rfl⟩ : syracuseStep 292174703 = 438262055) B438262055
theorem B194783135 : Blo 1642020 194783135 := bstep (se 1 (by rfl) ⟨146087351, by rfl⟩ : syracuseStep 194783135 = 292174703) B292174703
theorem B519421693 : Blo 1642020 519421693 := bstep (se 3 (by rfl) ⟨97391567, by rfl⟩ : syracuseStep 519421693 = 194783135) B194783135
theorem B692562257 : Blo 1642020 692562257 := bstep (se 2 (by rfl) ⟨259710846, by rfl⟩ : syracuseStep 692562257 = 519421693) B519421693
theorem B461708171 : Blo 1642020 461708171 := bstep (se 1 (by rfl) ⟨346281128, by rfl⟩ : syracuseStep 461708171 = 692562257) B692562257
theorem B307805447 : Blo 1642020 307805447 := bstep (se 1 (by rfl) ⟨230854085, by rfl⟩ : syracuseStep 307805447 = 461708171) B461708171
theorem B205203631 : Blo 1642020 205203631 := bstep (se 1 (by rfl) ⟨153902723, by rfl⟩ : syracuseStep 205203631 = 307805447) B307805447
theorem B273604841 : Blo 1642020 273604841 := bstep (se 2 (by rfl) ⟨102601815, by rfl⟩ : syracuseStep 273604841 = 205203631) B205203631
theorem B182403227 : Blo 1642020 182403227 := bstep (se 1 (by rfl) ⟨136802420, by rfl⟩ : syracuseStep 182403227 = 273604841) B273604841
theorem B121602151 : Blo 1642020 121602151 := bstep (se 1 (by rfl) ⟨91201613, by rfl⟩ : syracuseStep 121602151 = 182403227) B182403227
theorem B648544805 : Blo 1642020 648544805 := bstep (se 4 (by rfl) ⟨60801075, by rfl⟩ : syracuseStep 648544805 = 121602151) B121602151
theorem B432363203 : Blo 1642020 432363203 := bstep (se 1 (by rfl) ⟨324272402, by rfl⟩ : syracuseStep 432363203 = 648544805) B648544805
theorem B288242135 : Blo 1642020 288242135 := bstep (se 1 (by rfl) ⟨216181601, by rfl⟩ : syracuseStep 288242135 = 432363203) B432363203
theorem B192161423 : Blo 1642020 192161423 := bstep (se 1 (by rfl) ⟨144121067, by rfl⟩ : syracuseStep 192161423 = 288242135) B288242135
theorem B128107615 : Blo 1642020 128107615 := bstep (se 1 (by rfl) ⟨96080711, by rfl⟩ : syracuseStep 128107615 = 192161423) B192161423
theorem B170810153 : Blo 1642020 170810153 := bstep (se 2 (by rfl) ⟨64053807, by rfl⟩ : syracuseStep 170810153 = 128107615) B128107615
theorem B113873435 : Blo 1642020 113873435 := bstep (se 1 (by rfl) ⟨85405076, by rfl⟩ : syracuseStep 113873435 = 170810153) B170810153
theorem B75915623 : Blo 1642020 75915623 := bstep (se 1 (by rfl) ⟨56936717, by rfl⟩ : syracuseStep 75915623 = 113873435) B113873435
theorem B50610415 : Blo 1642020 50610415 := bstep (se 1 (by rfl) ⟨37957811, by rfl⟩ : syracuseStep 50610415 = 75915623) B75915623
theorem B67480553 : Blo 1642020 67480553 := bstep (se 2 (by rfl) ⟨25305207, by rfl⟩ : syracuseStep 67480553 = 50610415) B50610415
theorem B44987035 : Blo 1642020 44987035 := bstep (se 1 (by rfl) ⟨33740276, by rfl⟩ : syracuseStep 44987035 = 67480553) B67480553
theorem B59982713 : Blo 1642020 59982713 := bstep (se 2 (by rfl) ⟨22493517, by rfl⟩ : syracuseStep 59982713 = 44987035) B44987035
theorem B39988475 : Blo 1642020 39988475 := bstep (se 1 (by rfl) ⟨29991356, by rfl⟩ : syracuseStep 39988475 = 59982713) B59982713
theorem B26658983 : Blo 1642020 26658983 := bstep (se 1 (by rfl) ⟨19994237, by rfl⟩ : syracuseStep 26658983 = 39988475) B39988475
theorem B71090621 : Blo 1642020 71090621 := bstep (se 3 (by rfl) ⟨13329491, by rfl⟩ : syracuseStep 71090621 = 26658983) B26658983
theorem B47393747 : Blo 1642020 47393747 := bstep (se 1 (by rfl) ⟨35545310, by rfl⟩ : syracuseStep 47393747 = 71090621) B71090621
theorem B31595831 : Blo 1642020 31595831 := bstep (se 1 (by rfl) ⟨23696873, by rfl⟩ : syracuseStep 31595831 = 47393747) B47393747
theorem B21063887 : Blo 1642020 21063887 := bstep (se 1 (by rfl) ⟨15797915, by rfl⟩ : syracuseStep 21063887 = 31595831) B31595831
theorem B14042591 : Blo 1642020 14042591 := bstep (se 1 (by rfl) ⟨10531943, by rfl⟩ : syracuseStep 14042591 = 21063887) B21063887
theorem B9361727 : Blo 1642020 9361727 := bstep (se 1 (by rfl) ⟨7021295, by rfl⟩ : syracuseStep 9361727 = 14042591) B14042591
theorem B6241151 : Blo 1642020 6241151 := bstep (se 1 (by rfl) ⟨4680863, by rfl⟩ : syracuseStep 6241151 = 9361727) B9361727
theorem B4160767 : Blo 1642020 4160767 := bstep (se 1 (by rfl) ⟨3120575, by rfl⟩ : syracuseStep 4160767 = 6241151) B6241151
theorem B5547689 : Blo 1642020 5547689 := bstep (se 2 (by rfl) ⟨2080383, by rfl⟩ : syracuseStep 5547689 = 4160767) B4160767
theorem B3698459 : Blo 1642020 3698459 := bstep (se 1 (by rfl) ⟨2773844, by rfl⟩ : syracuseStep 3698459 = 5547689) B5547689
theorem B2465639 : Blo 1642020 2465639 := bstep (se 1 (by rfl) ⟨1849229, by rfl⟩ : syracuseStep 2465639 = 3698459) B3698459
theorem B1643759 : Blo 1642020 1643759 := bstep (se 1 (by rfl) ⟨1232819, by rfl⟩ : syracuseStep 1643759 = 2465639) B2465639

theorem C0 (j : ℕ) (h1 : 410505 ≤ j) (h2 : j ≤ 411004) : Blo 1642020 (4 * j + 3) := by
  interval_cases j
  · exact B1642023
  · exact B1642027
  · exact B1642031
  · exact B1642035
  · exact B1642039
  · exact B1642043
  · exact B1642047
  · exact B1642051
  · exact B1642055
  · exact B1642059
  · exact B1642063
  · exact B1642067
  · exact B1642071
  · exact B1642075
  · exact B1642079
  · exact B1642083
  · exact B1642087
  · exact B1642091
  · exact B1642095
  · exact B1642099
  · exact B1642103
  · exact B1642107
  · exact B1642111
  · exact B1642115
  · exact B1642119
  · exact B1642123
  · exact B1642127
  · exact B1642131
  · exact B1642135
  · exact B1642139
  · exact B1642143
  · exact B1642147
  · exact B1642151
  · exact B1642155
  · exact B1642159
  · exact B1642163
  · exact B1642167
  · exact B1642171
  · exact B1642175
  · exact B1642179
  · exact B1642183
  · exact B1642187
  · exact B1642191
  · exact B1642195
  · exact B1642199
  · exact B1642203
  · exact B1642207
  · exact B1642211
  · exact B1642215
  · exact B1642219
  · exact B1642223
  · exact B1642227
  · exact B1642231
  · exact B1642235
  · exact B1642239
  · exact B1642243
  · exact B1642247
  · exact B1642251
  · exact B1642255
  · exact B1642259
  · exact B1642263
  · exact B1642267
  · exact B1642271
  · exact B1642275
  · exact B1642279
  · exact B1642283
  · exact B1642287
  · exact B1642291
  · exact B1642295
  · exact B1642299
  · exact B1642303
  · exact B1642307
  · exact B1642311
  · exact B1642315
  · exact B1642319
  · exact B1642323
  · exact B1642327
  · exact B1642331
  · exact B1642335
  · exact B1642339
  · exact B1642343
  · exact B1642347
  · exact B1642351
  · exact B1642355
  · exact B1642359
  · exact B1642363
  · exact B1642367
  · exact B1642371
  · exact B1642375
  · exact B1642379
  · exact B1642383
  · exact B1642387
  · exact B1642391
  · exact B1642395
  · exact B1642399
  · exact B1642403
  · exact B1642407
  · exact B1642411
  · exact B1642415
  · exact B1642419
  · exact B1642423
  · exact B1642427
  · exact B1642431
  · exact B1642435
  · exact B1642439
  · exact B1642443
  · exact B1642447
  · exact B1642451
  · exact B1642455
  · exact B1642459
  · exact B1642463
  · exact B1642467
  · exact B1642471
  · exact B1642475
  · exact B1642479
  · exact B1642483
  · exact B1642487
  · exact B1642491
  · exact B1642495
  · exact B1642499
  · exact B1642503
  · exact B1642507
  · exact B1642511
  · exact B1642515
  · exact B1642519
  · exact B1642523
  · exact B1642527
  · exact B1642531
  · exact B1642535
  · exact B1642539
  · exact B1642543
  · exact B1642547
  · exact B1642551
  · exact B1642555
  · exact B1642559
  · exact B1642563
  · exact B1642567
  · exact B1642571
  · exact B1642575
  · exact B1642579
  · exact B1642583
  · exact B1642587
  · exact B1642591
  · exact B1642595
  · exact B1642599
  · exact B1642603
  · exact B1642607
  · exact B1642611
  · exact B1642615
  · exact B1642619
  · exact B1642623
  · exact B1642627
  · exact B1642631
  · exact B1642635
  · exact B1642639
  · exact B1642643
  · exact B1642647
  · exact B1642651
  · exact B1642655
  · exact B1642659
  · exact B1642663
  · exact B1642667
  · exact B1642671
  · exact B1642675
  · exact B1642679
  · exact B1642683
  · exact B1642687
  · exact B1642691
  · exact B1642695
  · exact B1642699
  · exact B1642703
  · exact B1642707
  · exact B1642711
  · exact B1642715
  · exact B1642719
  · exact B1642723
  · exact B1642727
  · exact B1642731
  · exact B1642735
  · exact B1642739
  · exact B1642743
  · exact B1642747
  · exact B1642751
  · exact B1642755
  · exact B1642759
  · exact B1642763
  · exact B1642767
  · exact B1642771
  · exact B1642775
  · exact B1642779
  · exact B1642783
  · exact B1642787
  · exact B1642791
  · exact B1642795
  · exact B1642799
  · exact B1642803
  · exact B1642807
  · exact B1642811
  · exact B1642815
  · exact B1642819
  · exact B1642823
  · exact B1642827
  · exact B1642831
  · exact B1642835
  · exact B1642839
  · exact B1642843
  · exact B1642847
  · exact B1642851
  · exact B1642855
  · exact B1642859
  · exact B1642863
  · exact B1642867
  · exact B1642871
  · exact B1642875
  · exact B1642879
  · exact B1642883
  · exact B1642887
  · exact B1642891
  · exact B1642895
  · exact B1642899
  · exact B1642903
  · exact B1642907
  · exact B1642911
  · exact B1642915
  · exact B1642919
  · exact B1642923
  · exact B1642927
  · exact B1642931
  · exact B1642935
  · exact B1642939
  · exact B1642943
  · exact B1642947
  · exact B1642951
  · exact B1642955
  · exact B1642959
  · exact B1642963
  · exact B1642967
  · exact B1642971
  · exact B1642975
  · exact B1642979
  · exact B1642983
  · exact B1642987
  · exact B1642991
  · exact B1642995
  · exact B1642999
  · exact B1643003
  · exact B1643007
  · exact B1643011
  · exact B1643015
  · exact B1643019
  · exact B1643023
  · exact B1643027
  · exact B1643031
  · exact B1643035
  · exact B1643039
  · exact B1643043
  · exact B1643047
  · exact B1643051
  · exact B1643055
  · exact B1643059
  · exact B1643063
  · exact B1643067
  · exact B1643071
  · exact B1643075
  · exact B1643079
  · exact B1643083
  · exact B1643087
  · exact B1643091
  · exact B1643095
  · exact B1643099
  · exact B1643103
  · exact B1643107
  · exact B1643111
  · exact B1643115
  · exact B1643119
  · exact B1643123
  · exact B1643127
  · exact B1643131
  · exact B1643135
  · exact B1643139
  · exact B1643143
  · exact B1643147
  · exact B1643151
  · exact B1643155
  · exact B1643159
  · exact B1643163
  · exact B1643167
  · exact B1643171
  · exact B1643175
  · exact B1643179
  · exact B1643183
  · exact B1643187
  · exact B1643191
  · exact B1643195
  · exact B1643199
  · exact B1643203
  · exact B1643207
  · exact B1643211
  · exact B1643215
  · exact B1643219
  · exact B1643223
  · exact B1643227
  · exact B1643231
  · exact B1643235
  · exact B1643239
  · exact B1643243
  · exact B1643247
  · exact B1643251
  · exact B1643255
  · exact B1643259
  · exact B1643263
  · exact B1643267
  · exact B1643271
  · exact B1643275
  · exact B1643279
  · exact B1643283
  · exact B1643287
  · exact B1643291
  · exact B1643295
  · exact B1643299
  · exact B1643303
  · exact B1643307
  · exact B1643311
  · exact B1643315
  · exact B1643319
  · exact B1643323
  · exact B1643327
  · exact B1643331
  · exact B1643335
  · exact B1643339
  · exact B1643343
  · exact B1643347
  · exact B1643351
  · exact B1643355
  · exact B1643359
  · exact B1643363
  · exact B1643367
  · exact B1643371
  · exact B1643375
  · exact B1643379
  · exact B1643383
  · exact B1643387
  · exact B1643391
  · exact B1643395
  · exact B1643399
  · exact B1643403
  · exact B1643407
  · exact B1643411
  · exact B1643415
  · exact B1643419
  · exact B1643423
  · exact B1643427
  · exact B1643431
  · exact B1643435
  · exact B1643439
  · exact B1643443
  · exact B1643447
  · exact B1643451
  · exact B1643455
  · exact B1643459
  · exact B1643463
  · exact B1643467
  · exact B1643471
  · exact B1643475
  · exact B1643479
  · exact B1643483
  · exact B1643487
  · exact B1643491
  · exact B1643495
  · exact B1643499
  · exact B1643503
  · exact B1643507
  · exact B1643511
  · exact B1643515
  · exact B1643519
  · exact B1643523
  · exact B1643527
  · exact B1643531
  · exact B1643535
  · exact B1643539
  · exact B1643543
  · exact B1643547
  · exact B1643551
  · exact B1643555
  · exact B1643559
  · exact B1643563
  · exact B1643567
  · exact B1643571
  · exact B1643575
  · exact B1643579
  · exact B1643583
  · exact B1643587
  · exact B1643591
  · exact B1643595
  · exact B1643599
  · exact B1643603
  · exact B1643607
  · exact B1643611
  · exact B1643615
  · exact B1643619
  · exact B1643623
  · exact B1643627
  · exact B1643631
  · exact B1643635
  · exact B1643639
  · exact B1643643
  · exact B1643647
  · exact B1643651
  · exact B1643655
  · exact B1643659
  · exact B1643663
  · exact B1643667
  · exact B1643671
  · exact B1643675
  · exact B1643679
  · exact B1643683
  · exact B1643687
  · exact B1643691
  · exact B1643695
  · exact B1643699
  · exact B1643703
  · exact B1643707
  · exact B1643711
  · exact B1643715
  · exact B1643719
  · exact B1643723
  · exact B1643727
  · exact B1643731
  · exact B1643735
  · exact B1643739
  · exact B1643743
  · exact B1643747
  · exact B1643751
  · exact B1643755
  · exact B1643759
  · exact B1643763
  · exact B1643767
  · exact B1643771
  · exact B1643775
  · exact B1643779
  · exact B1643783
  · exact B1643787
  · exact B1643791
  · exact B1643795
  · exact B1643799
  · exact B1643803
  · exact B1643807
  · exact B1643811
  · exact B1643815
  · exact B1643819
  · exact B1643823
  · exact B1643827
  · exact B1643831
  · exact B1643835
  · exact B1643839
  · exact B1643843
  · exact B1643847
  · exact B1643851
  · exact B1643855
  · exact B1643859
  · exact B1643863
  · exact B1643867
  · exact B1643871
  · exact B1643875
  · exact B1643879
  · exact B1643883
  · exact B1643887
  · exact B1643891
  · exact B1643895
  · exact B1643899
  · exact B1643903
  · exact B1643907
  · exact B1643911
  · exact B1643915
  · exact B1643919
  · exact B1643923
  · exact B1643927
  · exact B1643931
  · exact B1643935
  · exact B1643939
  · exact B1643943
  · exact B1643947
  · exact B1643951
  · exact B1643955
  · exact B1643959
  · exact B1643963
  · exact B1643967
  · exact B1643971
  · exact B1643975
  · exact B1643979
  · exact B1643983
  · exact B1643987
  · exact B1643991
  · exact B1643995
  · exact B1643999
  · exact B1644003
  · exact B1644007
  · exact B1644011
  · exact B1644015
  · exact B1644019

theorem solution (m : ℕ) (hlo : 1642020 ≤ m) (hhi : m ≤ 1644020) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 410505 ≤ j := by omega
    have hj2 : j ≤ 411004 := by omega
    have hb : Blo 1642020 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
