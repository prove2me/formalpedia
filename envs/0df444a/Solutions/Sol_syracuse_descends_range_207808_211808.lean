-- Prove2me | solution 1 for syracuse_descends_range_207808_211808
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:54.445901+00:00
-- url     : https://prove2.me/submissions/b0f6a1a5-9bd3-443d-b0eb-2a6cfdb81bbb

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


theorem B950453 : Blo 207808 950453 := bbase (se 5 (by rfl) ⟨44552, by rfl⟩ : syracuseStep 950453 = 89105) (by norm_num)
theorem B360821 : Blo 207808 360821 := bbase (se 5 (by rfl) ⟨16913, by rfl⟩ : syracuseStep 360821 = 33827) (by norm_num)
theorem B1901045 : Blo 207808 1901045 := bbase (se 5 (by rfl) ⟨89111, by rfl⟩ : syracuseStep 1901045 = 178223) (by norm_num)
theorem B361045 : Blo 207808 361045 := bbase (se 8 (by rfl) ⟨2115, by rfl⟩ : syracuseStep 361045 = 4231) (by norm_num)
theorem B1606229 : Blo 207808 1606229 := bbase (se 8 (by rfl) ⟨9411, by rfl⟩ : syracuseStep 1606229 = 18823) (by norm_num)
theorem B262769 : Blo 207808 262769 := bbase (se 2 (by rfl) ⟨98538, by rfl⟩ : syracuseStep 262769 = 197077) (by norm_num)
theorem B263017 : Blo 207808 263017 := bbase (se 2 (by rfl) ⟨98631, by rfl⟩ : syracuseStep 263017 = 197263) (by norm_num)
theorem B263189 : Blo 207808 263189 := bbase (se 6 (by rfl) ⟨6168, by rfl⟩ : syracuseStep 263189 = 12337) (by norm_num)
theorem B263245 : Blo 207808 263245 := bbase (se 3 (by rfl) ⟨49358, by rfl⟩ : syracuseStep 263245 = 98717) (by norm_num)
theorem B361589 : Blo 207808 361589 := bbase (se 5 (by rfl) ⟨16949, by rfl⟩ : syracuseStep 361589 = 33899) (by norm_num)
theorem B296077 : Blo 207808 296077 := bbase (se 3 (by rfl) ⟨55514, by rfl⟩ : syracuseStep 296077 = 111029) (by norm_num)
theorem B263341 : Blo 207808 263341 := bbase (se 3 (by rfl) ⟨49376, by rfl⟩ : syracuseStep 263341 = 98753) (by norm_num)
theorem B722197 : Blo 207808 722197 := bbase (se 6 (by rfl) ⟨16926, by rfl⟩ : syracuseStep 722197 = 33853) (by norm_num)
theorem B230689 : Blo 207808 230689 := bbase (se 2 (by rfl) ⟨86508, by rfl⟩ : syracuseStep 230689 = 173017) (by norm_num)
theorem B394541 : Blo 207808 394541 := bbase (se 3 (by rfl) ⟨73976, by rfl⟩ : syracuseStep 394541 = 147953) (by norm_num)
theorem B263513 : Blo 207808 263513 := bbase (se 2 (by rfl) ⟨98817, by rfl⟩ : syracuseStep 263513 = 197635) (by norm_num)
theorem B296293 : Blo 207808 296293 := bbase (se 4 (by rfl) ⟨27777, by rfl⟩ : syracuseStep 296293 = 55555) (by norm_num)
theorem B263569 : Blo 207808 263569 := bbase (se 2 (by rfl) ⟨98838, by rfl⟩ : syracuseStep 263569 = 197677) (by norm_num)
theorem B263665 : Blo 207808 263665 := bbase (se 2 (by rfl) ⟨98874, by rfl⟩ : syracuseStep 263665 = 197749) (by norm_num)
theorem B1017365 : Blo 207808 1017365 := bbase (se 6 (by rfl) ⟨23844, by rfl⟩ : syracuseStep 1017365 = 47689) (by norm_num)
theorem B263837 : Blo 207808 263837 := bbase (se 3 (by rfl) ⟨49469, by rfl⟩ : syracuseStep 263837 = 98939) (by norm_num)
theorem B263893 : Blo 207808 263893 := bbase (se 7 (by rfl) ⟨3092, by rfl⟩ : syracuseStep 263893 = 6185) (by norm_num)
theorem B296669 : Blo 207808 296669 := bbase (se 3 (by rfl) ⟨55625, by rfl⟩ : syracuseStep 296669 = 111251) (by norm_num)
theorem B526085 : Blo 207808 526085 := bbase (se 4 (by rfl) ⟨49320, by rfl⟩ : syracuseStep 526085 = 98641) (by norm_num)
theorem B263989 : Blo 207808 263989 := bbase (se 5 (by rfl) ⟨12374, by rfl⟩ : syracuseStep 263989 = 24749) (by norm_num)
theorem B526277 : Blo 207808 526277 := bbase (se 4 (by rfl) ⟨49338, by rfl⟩ : syracuseStep 526277 = 98677) (by norm_num)
theorem B264161 : Blo 207808 264161 := bbase (se 2 (by rfl) ⟨99060, by rfl⟩ : syracuseStep 264161 = 198121) (by norm_num)
theorem B3377173 : Blo 207808 3377173 := bbase (se 6 (by rfl) ⟨79152, by rfl⟩ : syracuseStep 3377173 = 158305) (by norm_num)
theorem B264217 : Blo 207808 264217 := bbase (se 2 (by rfl) ⟨99081, by rfl⟩ : syracuseStep 264217 = 198163) (by norm_num)
theorem B395293 : Blo 207808 395293 := bbase (se 3 (by rfl) ⟨74117, by rfl⟩ : syracuseStep 395293 = 148235) (by norm_num)
theorem B264313 : Blo 207808 264313 := bbase (se 2 (by rfl) ⟨99117, by rfl⟩ : syracuseStep 264313 = 198235) (by norm_num)
theorem B395437 : Blo 207808 395437 := bbase (se 3 (by rfl) ⟨74144, by rfl⟩ : syracuseStep 395437 = 148289) (by norm_num)
theorem B592085 : Blo 207808 592085 := bbase (se 7 (by rfl) ⟨6938, by rfl⟩ : syracuseStep 592085 = 13877) (by norm_num)
theorem B526621 : Blo 207808 526621 := bbase (se 3 (by rfl) ⟨98741, by rfl⟩ : syracuseStep 526621 = 197483) (by norm_num)
theorem B264485 : Blo 207808 264485 := bbase (se 4 (by rfl) ⟨24795, by rfl⟩ : syracuseStep 264485 = 49591) (by norm_num)
theorem B395597 : Blo 207808 395597 := bbase (se 3 (by rfl) ⟨74174, by rfl⟩ : syracuseStep 395597 = 148349) (by norm_num)
theorem B264541 : Blo 207808 264541 := bbase (se 3 (by rfl) ⟨49601, by rfl⟩ : syracuseStep 264541 = 99203) (by norm_num)
theorem B526733 : Blo 207808 526733 := bbase (se 3 (by rfl) ⟨98762, by rfl⟩ : syracuseStep 526733 = 197525) (by norm_num)
theorem B264637 : Blo 207808 264637 := bbase (se 3 (by rfl) ⟨49619, by rfl⟩ : syracuseStep 264637 = 99239) (by norm_num)
theorem B428485 : Blo 207808 428485 := bbase (se 4 (by rfl) ⟨40170, by rfl⟩ : syracuseStep 428485 = 80341) (by norm_num)
theorem B395741 : Blo 207808 395741 := bbase (se 3 (by rfl) ⟨74201, by rfl⟩ : syracuseStep 395741 = 148403) (by norm_num)
theorem B1083941 : Blo 207808 1083941 := bbase (se 4 (by rfl) ⟨101619, by rfl⟩ : syracuseStep 1083941 = 203239) (by norm_num)
theorem B526925 : Blo 207808 526925 := bbase (se 3 (by rfl) ⟨98798, by rfl⟩ : syracuseStep 526925 = 197597) (by norm_num)
theorem B264809 : Blo 207808 264809 := bbase (se 2 (by rfl) ⟨99303, by rfl⟩ : syracuseStep 264809 = 198607) (by norm_num)
theorem B264865 : Blo 207808 264865 := bbase (se 2 (by rfl) ⟨99324, by rfl⟩ : syracuseStep 264865 = 198649) (by norm_num)
theorem B789173 : Blo 207808 789173 := bbase (se 5 (by rfl) ⟨36992, by rfl⟩ : syracuseStep 789173 = 73985) (by norm_num)
theorem B396029 : Blo 207808 396029 := bbase (se 3 (by rfl) ⟨74255, by rfl⟩ : syracuseStep 396029 = 148511) (by norm_num)
theorem B264961 : Blo 207808 264961 := bbase (se 2 (by rfl) ⟨99360, by rfl⟩ : syracuseStep 264961 = 198721) (by norm_num)
theorem B396181 : Blo 207808 396181 := bbase (se 6 (by rfl) ⟨9285, by rfl⟩ : syracuseStep 396181 = 18571) (by norm_num)
theorem B527269 : Blo 207808 527269 := bbase (se 4 (by rfl) ⟨49431, by rfl⟩ : syracuseStep 527269 = 98863) (by norm_num)
theorem B265133 : Blo 207808 265133 := bbase (se 3 (by rfl) ⟨49712, by rfl⟩ : syracuseStep 265133 = 99425) (by norm_num)
theorem B265189 : Blo 207808 265189 := bbase (se 4 (by rfl) ⟨24861, by rfl⟩ : syracuseStep 265189 = 49723) (by norm_num)
theorem B527381 : Blo 207808 527381 := bbase (se 6 (by rfl) ⟨12360, by rfl⟩ : syracuseStep 527381 = 24721) (by norm_num)
theorem B265285 : Blo 207808 265285 := bbase (se 4 (by rfl) ⟨24870, by rfl⟩ : syracuseStep 265285 = 49741) (by norm_num)
theorem B1346645 : Blo 207808 1346645 := bbase (se 8 (by rfl) ⟨7890, by rfl⟩ : syracuseStep 1346645 = 15781) (by norm_num)
theorem B298093 : Blo 207808 298093 := bbase (se 3 (by rfl) ⟨55892, by rfl⟩ : syracuseStep 298093 = 111785) (by norm_num)
theorem B396485 : Blo 207808 396485 := bbase (se 4 (by rfl) ⟨37170, by rfl⟩ : syracuseStep 396485 = 74341) (by norm_num)
theorem B527573 : Blo 207808 527573 := bbase (se 7 (by rfl) ⟨6182, by rfl⟩ : syracuseStep 527573 = 12365) (by norm_num)
theorem B265457 : Blo 207808 265457 := bbase (se 2 (by rfl) ⟨99546, by rfl⟩ : syracuseStep 265457 = 199093) (by norm_num)
theorem B265513 : Blo 207808 265513 := bbase (se 2 (by rfl) ⟨99567, by rfl⟩ : syracuseStep 265513 = 199135) (by norm_num)
theorem B265609 : Blo 207808 265609 := bbase (se 2 (by rfl) ⟨99603, by rfl⟩ : syracuseStep 265609 = 199207) (by norm_num)
theorem B527917 : Blo 207808 527917 := bbase (se 3 (by rfl) ⟨98984, by rfl⟩ : syracuseStep 527917 = 197969) (by norm_num)
theorem B265781 : Blo 207808 265781 := bbase (se 5 (by rfl) ⟨12458, by rfl⟩ : syracuseStep 265781 = 24917) (by norm_num)
theorem B265837 : Blo 207808 265837 := bbase (se 3 (by rfl) ⟨49844, by rfl⟩ : syracuseStep 265837 = 99689) (by norm_num)
theorem B528029 : Blo 207808 528029 := bbase (se 3 (by rfl) ⟨99005, by rfl⟩ : syracuseStep 528029 = 198011) (by norm_num)
theorem B298685 : Blo 207808 298685 := bbase (se 3 (by rfl) ⟨56003, by rfl⟩ : syracuseStep 298685 = 112007) (by norm_num)
theorem B265933 : Blo 207808 265933 := bbase (se 3 (by rfl) ⟨49862, by rfl⟩ : syracuseStep 265933 = 99725) (by norm_num)
theorem B593669 : Blo 207808 593669 := bbase (se 4 (by rfl) ⟨55656, by rfl⟩ : syracuseStep 593669 = 111313) (by norm_num)
theorem B298765 : Blo 207808 298765 := bbase (se 3 (by rfl) ⟨56018, by rfl⟩ : syracuseStep 298765 = 112037) (by norm_num)
theorem B790357 : Blo 207808 790357 := bbase (se 9 (by rfl) ⟨2315, by rfl⟩ : syracuseStep 790357 = 4631) (by norm_num)
theorem B528221 : Blo 207808 528221 := bbase (se 3 (by rfl) ⟨99041, by rfl⟩ : syracuseStep 528221 = 198083) (by norm_num)
theorem B266105 : Blo 207808 266105 := bbase (se 2 (by rfl) ⟨99789, by rfl⟩ : syracuseStep 266105 = 199579) (by norm_num)
theorem B298885 : Blo 207808 298885 := bbase (se 4 (by rfl) ⟨28020, by rfl⟩ : syracuseStep 298885 = 56041) (by norm_num)
theorem B266161 : Blo 207808 266161 := bbase (se 2 (by rfl) ⟨99810, by rfl⟩ : syracuseStep 266161 = 199621) (by norm_num)
theorem B397237 : Blo 207808 397237 := bbase (se 5 (by rfl) ⟨18620, by rfl⟩ : syracuseStep 397237 = 37241) (by norm_num)
theorem B298981 : Blo 207808 298981 := bbase (se 4 (by rfl) ⟨28029, by rfl⟩ : syracuseStep 298981 = 56059) (by norm_num)
theorem B266257 : Blo 207808 266257 := bbase (se 2 (by rfl) ⟨99846, by rfl⟩ : syracuseStep 266257 = 199693) (by norm_num)
theorem B397381 : Blo 207808 397381 := bbase (se 4 (by rfl) ⟨37254, by rfl⟩ : syracuseStep 397381 = 74509) (by norm_num)
theorem B790661 : Blo 207808 790661 := bbase (se 4 (by rfl) ⟨74124, by rfl⟩ : syracuseStep 790661 = 148249) (by norm_num)
theorem B1052837 : Blo 207808 1052837 := bbase (se 4 (by rfl) ⟨98703, by rfl⟩ : syracuseStep 1052837 = 197407) (by norm_num)
theorem B528565 : Blo 207808 528565 := bbase (se 5 (by rfl) ⟨24776, by rfl⟩ : syracuseStep 528565 = 49553) (by norm_num)
theorem B266429 : Blo 207808 266429 := bbase (se 3 (by rfl) ⟨49955, by rfl⟩ : syracuseStep 266429 = 99911) (by norm_num)
theorem B397541 : Blo 207808 397541 := bbase (se 4 (by rfl) ⟨37269, by rfl⟩ : syracuseStep 397541 = 74539) (by norm_num)
theorem B266485 : Blo 207808 266485 := bbase (se 5 (by rfl) ⟨12491, by rfl⟩ : syracuseStep 266485 = 24983) (by norm_num)
theorem B528677 : Blo 207808 528677 := bbase (se 4 (by rfl) ⟨49563, by rfl⟩ : syracuseStep 528677 = 99127) (by norm_num)
theorem B233797 : Blo 207808 233797 := bbase (se 4 (by rfl) ⟨21918, by rfl⟩ : syracuseStep 233797 = 43837) (by norm_num)
theorem B266581 : Blo 207808 266581 := bbase (se 10 (by rfl) ⟨390, by rfl⟩ : syracuseStep 266581 = 781) (by norm_num)
theorem B233833 : Blo 207808 233833 := bbase (se 2 (by rfl) ⟨87687, by rfl⟩ : syracuseStep 233833 = 175375) (by norm_num)
theorem B397685 : Blo 207808 397685 := bbase (se 5 (by rfl) ⟨18641, by rfl⟩ : syracuseStep 397685 = 37283) (by norm_num)
theorem B954757 : Blo 207808 954757 := bbase (se 4 (by rfl) ⟨89508, by rfl⟩ : syracuseStep 954757 = 179017) (by norm_num)
theorem B233869 : Blo 207808 233869 := bbase (se 3 (by rfl) ⟨43850, by rfl⟩ : syracuseStep 233869 = 87701) (by norm_num)
theorem B594341 : Blo 207808 594341 := bbase (se 4 (by rfl) ⟨55719, by rfl⟩ : syracuseStep 594341 = 111439) (by norm_num)
theorem B233905 : Blo 207808 233905 := bbase (se 2 (by rfl) ⟨87714, by rfl⟩ : syracuseStep 233905 = 175429) (by norm_num)
theorem B233941 : Blo 207808 233941 := bbase (se 7 (by rfl) ⟨2741, by rfl⟩ : syracuseStep 233941 = 5483) (by norm_num)
theorem B299477 : Blo 207808 299477 := bbase (se 7 (by rfl) ⟨3509, by rfl⟩ : syracuseStep 299477 = 7019) (by norm_num)
theorem B528869 : Blo 207808 528869 := bbase (se 4 (by rfl) ⟨49581, by rfl⟩ : syracuseStep 528869 = 99163) (by norm_num)
theorem B233977 : Blo 207808 233977 := bbase (se 2 (by rfl) ⟨87741, by rfl⟩ : syracuseStep 233977 = 175483) (by norm_num)
theorem B430589 : Blo 207808 430589 := bbase (se 3 (by rfl) ⟨80735, by rfl⟩ : syracuseStep 430589 = 161471) (by norm_num)
theorem B266753 : Blo 207808 266753 := bbase (se 2 (by rfl) ⟨100032, by rfl⟩ : syracuseStep 266753 = 200065) (by norm_num)
theorem B234013 : Blo 207808 234013 := bbase (se 3 (by rfl) ⟨43877, by rfl⟩ : syracuseStep 234013 = 87755) (by norm_num)
theorem B266797 : Blo 207808 266797 := bbase (se 3 (by rfl) ⟨50024, by rfl⟩ : syracuseStep 266797 = 100049) (by norm_num)
theorem B266809 : Blo 207808 266809 := bbase (se 2 (by rfl) ⟨100053, by rfl⟩ : syracuseStep 266809 = 200107) (by norm_num)
theorem B234049 : Blo 207808 234049 := bbase (se 2 (by rfl) ⟨87768, by rfl⟩ : syracuseStep 234049 = 175537) (by norm_num)
theorem B234085 : Blo 207808 234085 := bbase (se 4 (by rfl) ⟨21945, by rfl⟩ : syracuseStep 234085 = 43891) (by norm_num)
theorem B234121 : Blo 207808 234121 := bbase (se 2 (by rfl) ⟨87795, by rfl⟩ : syracuseStep 234121 = 175591) (by norm_num)
theorem B1217173 : Blo 207808 1217173 := bbase (se 6 (by rfl) ⟨28527, by rfl⟩ : syracuseStep 1217173 = 57055) (by norm_num)
theorem B397973 : Blo 207808 397973 := bbase (se 6 (by rfl) ⟨9327, by rfl⟩ : syracuseStep 397973 = 18655) (by norm_num)
theorem B266905 : Blo 207808 266905 := bbase (se 2 (by rfl) ⟨100089, by rfl⟩ : syracuseStep 266905 = 200179) (by norm_num)
theorem B234157 : Blo 207808 234157 := bbase (se 3 (by rfl) ⟨43904, by rfl⟩ : syracuseStep 234157 = 87809) (by norm_num)
theorem B234193 : Blo 207808 234193 := bbase (se 2 (by rfl) ⟨87822, by rfl⟩ : syracuseStep 234193 = 175645) (by norm_num)
theorem B234229 : Blo 207808 234229 := bbase (se 5 (by rfl) ⟨10979, by rfl⟩ : syracuseStep 234229 = 21959) (by norm_num)
theorem B234265 : Blo 207808 234265 := bbase (se 2 (by rfl) ⟨87849, by rfl⟩ : syracuseStep 234265 = 175699) (by norm_num)
theorem B398125 : Blo 207808 398125 := bbase (se 3 (by rfl) ⟨74648, by rfl⟩ : syracuseStep 398125 = 149297) (by norm_num)
theorem B234301 : Blo 207808 234301 := bbase (se 3 (by rfl) ⟨43931, by rfl⟩ : syracuseStep 234301 = 87863) (by norm_num)
theorem B529213 : Blo 207808 529213 := bbase (se 3 (by rfl) ⟨99227, by rfl⟩ : syracuseStep 529213 = 198455) (by norm_num)
theorem B267077 : Blo 207808 267077 := bbase (se 4 (by rfl) ⟨25038, by rfl⟩ : syracuseStep 267077 = 50077) (by norm_num)
theorem B594773 : Blo 207808 594773 := bbase (se 9 (by rfl) ⟨1742, by rfl⟩ : syracuseStep 594773 = 3485) (by norm_num)
theorem B234337 : Blo 207808 234337 := bbase (se 2 (by rfl) ⟨87876, by rfl⟩ : syracuseStep 234337 = 175753) (by norm_num)
theorem B267133 : Blo 207808 267133 := bbase (se 3 (by rfl) ⟨50087, by rfl⟩ : syracuseStep 267133 = 100175) (by norm_num)
theorem B234373 : Blo 207808 234373 := bbase (se 4 (by rfl) ⟨21972, by rfl⟩ : syracuseStep 234373 = 43945) (by norm_num)
theorem B234409 : Blo 207808 234409 := bbase (se 2 (by rfl) ⟨87903, by rfl⟩ : syracuseStep 234409 = 175807) (by norm_num)
theorem B529325 : Blo 207808 529325 := bbase (se 3 (by rfl) ⟨99248, by rfl⟩ : syracuseStep 529325 = 198497) (by norm_num)
theorem B234445 : Blo 207808 234445 := bbase (se 3 (by rfl) ⟨43958, by rfl⟩ : syracuseStep 234445 = 87917) (by norm_num)
theorem B267229 : Blo 207808 267229 := bbase (se 3 (by rfl) ⟨50105, by rfl⟩ : syracuseStep 267229 = 100211) (by norm_num)
theorem B234481 : Blo 207808 234481 := bbase (se 2 (by rfl) ⟨87930, by rfl⟩ : syracuseStep 234481 = 175861) (by norm_num)
theorem B300029 : Blo 207808 300029 := bbase (se 3 (by rfl) ⟨56255, by rfl⟩ : syracuseStep 300029 = 112511) (by norm_num)
theorem B234517 : Blo 207808 234517 := bbase (se 6 (by rfl) ⟨5496, by rfl⟩ : syracuseStep 234517 = 10993) (by norm_num)
theorem B234553 : Blo 207808 234553 := bbase (se 2 (by rfl) ⟨87957, by rfl⟩ : syracuseStep 234553 = 175915) (by norm_num)
theorem B234589 : Blo 207808 234589 := bbase (se 3 (by rfl) ⟨43985, by rfl⟩ : syracuseStep 234589 = 87971) (by norm_num)
theorem B398429 : Blo 207808 398429 := bbase (se 3 (by rfl) ⟨74705, by rfl⟩ : syracuseStep 398429 = 149411) (by norm_num)
theorem B529517 : Blo 207808 529517 := bbase (se 3 (by rfl) ⟨99284, by rfl⟩ : syracuseStep 529517 = 198569) (by norm_num)
theorem B889973 : Blo 207808 889973 := bbase (se 5 (by rfl) ⟨41717, by rfl⟩ : syracuseStep 889973 = 83435) (by norm_num)
theorem B234625 : Blo 207808 234625 := bbase (se 2 (by rfl) ⟨87984, by rfl⟩ : syracuseStep 234625 = 175969) (by norm_num)
theorem B267401 : Blo 207808 267401 := bbase (se 2 (by rfl) ⟨100275, by rfl⟩ : syracuseStep 267401 = 200551) (by norm_num)
theorem B234661 : Blo 207808 234661 := bbase (se 4 (by rfl) ⟨21999, by rfl⟩ : syracuseStep 234661 = 43999) (by norm_num)
theorem B267457 : Blo 207808 267457 := bbase (se 2 (by rfl) ⟨100296, by rfl⟩ : syracuseStep 267457 = 200593) (by norm_num)
theorem B234697 : Blo 207808 234697 := bbase (se 2 (by rfl) ⟨88011, by rfl⟩ : syracuseStep 234697 = 176023) (by norm_num)
theorem B234733 : Blo 207808 234733 := bbase (se 3 (by rfl) ⟨44012, by rfl⟩ : syracuseStep 234733 = 88025) (by norm_num)
theorem B234769 : Blo 207808 234769 := bbase (se 2 (by rfl) ⟨88038, by rfl⟩ : syracuseStep 234769 = 176077) (by norm_num)
theorem B267553 : Blo 207808 267553 := bbase (se 2 (by rfl) ⟨100332, by rfl⟩ : syracuseStep 267553 = 200665) (by norm_num)
theorem B234805 : Blo 207808 234805 := bbase (se 5 (by rfl) ⟨11006, by rfl⟩ : syracuseStep 234805 = 22013) (by norm_num)
theorem B300349 : Blo 207808 300349 := bbase (se 3 (by rfl) ⟨56315, by rfl⟩ : syracuseStep 300349 = 112631) (by norm_num)
theorem B234841 : Blo 207808 234841 := bbase (se 2 (by rfl) ⟨88065, by rfl⟩ : syracuseStep 234841 = 176131) (by norm_num)
theorem B234877 : Blo 207808 234877 := bbase (se 3 (by rfl) ⟨44039, by rfl⟩ : syracuseStep 234877 = 88079) (by norm_num)
theorem B234913 : Blo 207808 234913 := bbase (se 2 (by rfl) ⟨88092, by rfl⟩ : syracuseStep 234913 = 176185) (by norm_num)
theorem B1054133 : Blo 207808 1054133 := bbase (se 5 (by rfl) ⟨49412, by rfl⟩ : syracuseStep 1054133 = 98825) (by norm_num)
theorem B234949 : Blo 207808 234949 := bbase (se 4 (by rfl) ⟨22026, by rfl⟩ : syracuseStep 234949 = 44053) (by norm_num)
theorem B529861 : Blo 207808 529861 := bbase (se 4 (by rfl) ⟨49674, by rfl⟩ : syracuseStep 529861 = 99349) (by norm_num)
theorem B267725 : Blo 207808 267725 := bbase (se 3 (by rfl) ⟨50198, by rfl⟩ : syracuseStep 267725 = 100397) (by norm_num)
theorem B1807829 : Blo 207808 1807829 := bbase (se 7 (by rfl) ⟨21185, by rfl⟩ : syracuseStep 1807829 = 42371) (by norm_num)
theorem B234985 : Blo 207808 234985 := bbase (se 2 (by rfl) ⟨88119, by rfl⟩ : syracuseStep 234985 = 176239) (by norm_num)
theorem B267781 : Blo 207808 267781 := bbase (se 4 (by rfl) ⟨25104, by rfl⟩ : syracuseStep 267781 = 50209) (by norm_num)
theorem B235021 : Blo 207808 235021 := bbase (se 3 (by rfl) ⟨44066, by rfl⟩ : syracuseStep 235021 = 88133) (by norm_num)
theorem B955925 : Blo 207808 955925 := bbase (se 6 (by rfl) ⟨22404, by rfl⟩ : syracuseStep 955925 = 44809) (by norm_num)
theorem B235057 : Blo 207808 235057 := bbase (se 2 (by rfl) ⟨88146, by rfl⟩ : syracuseStep 235057 = 176293) (by norm_num)
theorem B529973 : Blo 207808 529973 := bbase (se 5 (by rfl) ⟨24842, by rfl⟩ : syracuseStep 529973 = 49685) (by norm_num)
theorem B595525 : Blo 207808 595525 := bbase (se 4 (by rfl) ⟨55830, by rfl⟩ : syracuseStep 595525 = 111661) (by norm_num)
theorem B235093 : Blo 207808 235093 := bbase (se 8 (by rfl) ⟨1377, by rfl⟩ : syracuseStep 235093 = 2755) (by norm_num)
theorem B267877 : Blo 207808 267877 := bbase (se 4 (by rfl) ⟨25113, by rfl⟩ : syracuseStep 267877 = 50227) (by norm_num)
theorem B235129 : Blo 207808 235129 := bbase (se 2 (by rfl) ⟨88173, by rfl⟩ : syracuseStep 235129 = 176347) (by norm_num)
theorem B235165 : Blo 207808 235165 := bbase (se 3 (by rfl) ⟨44093, by rfl⟩ : syracuseStep 235165 = 88187) (by norm_num)
theorem B235201 : Blo 207808 235201 := bbase (se 2 (by rfl) ⟨88200, by rfl⟩ : syracuseStep 235201 = 176401) (by norm_num)
theorem B235237 : Blo 207808 235237 := bbase (se 4 (by rfl) ⟨22053, by rfl⟩ : syracuseStep 235237 = 44107) (by norm_num)
theorem B300781 : Blo 207808 300781 := bbase (se 3 (by rfl) ⟨56396, by rfl⟩ : syracuseStep 300781 = 112793) (by norm_num)
theorem B530165 : Blo 207808 530165 := bbase (se 5 (by rfl) ⟨24851, by rfl⟩ : syracuseStep 530165 = 49703) (by norm_num)
theorem B235273 : Blo 207808 235273 := bbase (se 2 (by rfl) ⟨88227, by rfl⟩ : syracuseStep 235273 = 176455) (by norm_num)
theorem B268049 : Blo 207808 268049 := bbase (se 2 (by rfl) ⟨100518, by rfl⟩ : syracuseStep 268049 = 201037) (by norm_num)
theorem B235309 : Blo 207808 235309 := bbase (se 3 (by rfl) ⟨44120, by rfl⟩ : syracuseStep 235309 = 88241) (by norm_num)
theorem B399181 : Blo 207808 399181 := bbase (se 3 (by rfl) ⟨74846, by rfl⟩ : syracuseStep 399181 = 149693) (by norm_num)
theorem B235345 : Blo 207808 235345 := bbase (se 2 (by rfl) ⟨88254, by rfl⟩ : syracuseStep 235345 = 176509) (by norm_num)
theorem B235381 : Blo 207808 235381 := bbase (se 5 (by rfl) ⟨11033, by rfl⟩ : syracuseStep 235381 = 22067) (by norm_num)
theorem B235417 : Blo 207808 235417 := bbase (se 2 (by rfl) ⟨88281, by rfl⟩ : syracuseStep 235417 = 176563) (by norm_num)
theorem B235453 : Blo 207808 235453 := bbase (se 3 (by rfl) ⟨44147, by rfl⟩ : syracuseStep 235453 = 88295) (by norm_num)
theorem B399325 : Blo 207808 399325 := bbase (se 3 (by rfl) ⟨74873, by rfl⟩ : syracuseStep 399325 = 149747) (by norm_num)
theorem B235489 : Blo 207808 235489 := bbase (se 2 (by rfl) ⟨88308, by rfl⟩ : syracuseStep 235489 = 176617) (by norm_num)
theorem B1349621 : Blo 207808 1349621 := bbase (se 5 (by rfl) ⟨63263, by rfl⟩ : syracuseStep 1349621 = 126527) (by norm_num)
theorem B235525 : Blo 207808 235525 := bbase (se 4 (by rfl) ⟨22080, by rfl⟩ : syracuseStep 235525 = 44161) (by norm_num)
theorem B235561 : Blo 207808 235561 := bbase (se 2 (by rfl) ⟨88335, by rfl⟩ : syracuseStep 235561 = 176671) (by norm_num)
theorem B235597 : Blo 207808 235597 := bbase (se 3 (by rfl) ⟨44174, by rfl⟩ : syracuseStep 235597 = 88349) (by norm_num)
theorem B530509 : Blo 207808 530509 := bbase (se 3 (by rfl) ⟨99470, by rfl⟩ : syracuseStep 530509 = 198941) (by norm_num)
theorem B235633 : Blo 207808 235633 := bbase (se 2 (by rfl) ⟨88362, by rfl⟩ : syracuseStep 235633 = 176725) (by norm_num)
theorem B399485 : Blo 207808 399485 := bbase (se 3 (by rfl) ⟨74903, by rfl⟩ : syracuseStep 399485 = 149807) (by norm_num)
theorem B235669 : Blo 207808 235669 := bbase (se 6 (by rfl) ⟨5523, by rfl⟩ : syracuseStep 235669 = 11047) (by norm_num)
theorem B235705 : Blo 207808 235705 := bbase (se 2 (by rfl) ⟨88389, by rfl⟩ : syracuseStep 235705 = 176779) (by norm_num)
theorem B530621 : Blo 207808 530621 := bbase (se 3 (by rfl) ⟨99491, by rfl⟩ : syracuseStep 530621 = 198983) (by norm_num)
theorem B792773 : Blo 207808 792773 := bbase (se 4 (by rfl) ⟨74322, by rfl⟩ : syracuseStep 792773 = 148645) (by norm_num)
theorem B235741 : Blo 207808 235741 := bbase (se 3 (by rfl) ⟨44201, by rfl⟩ : syracuseStep 235741 = 88403) (by norm_num)
theorem B334061 : Blo 207808 334061 := bbase (se 3 (by rfl) ⟨62636, by rfl⟩ : syracuseStep 334061 = 125273) (by norm_num)
theorem B235777 : Blo 207808 235777 := bbase (se 2 (by rfl) ⟨88416, by rfl⟩ : syracuseStep 235777 = 176833) (by norm_num)
theorem B399629 : Blo 207808 399629 := bbase (se 3 (by rfl) ⟨74930, by rfl⟩ : syracuseStep 399629 = 149861) (by norm_num)
theorem B235813 : Blo 207808 235813 := bbase (se 4 (by rfl) ⟨22107, by rfl⟩ : syracuseStep 235813 = 44215) (by norm_num)
theorem B235849 : Blo 207808 235849 := bbase (se 2 (by rfl) ⟨88443, by rfl⟩ : syracuseStep 235849 = 176887) (by norm_num)
theorem B235885 : Blo 207808 235885 := bbase (se 3 (by rfl) ⟨44228, by rfl⟩ : syracuseStep 235885 = 88457) (by norm_num)
theorem B530813 : Blo 207808 530813 := bbase (se 3 (by rfl) ⟨99527, by rfl⟩ : syracuseStep 530813 = 199055) (by norm_num)
theorem B235921 : Blo 207808 235921 := bbase (se 2 (by rfl) ⟨88470, by rfl⟩ : syracuseStep 235921 = 176941) (by norm_num)
theorem B334253 : Blo 207808 334253 := bbase (se 3 (by rfl) ⟨62672, by rfl⟩ : syracuseStep 334253 = 125345) (by norm_num)
theorem B235957 : Blo 207808 235957 := bbase (se 5 (by rfl) ⟨11060, by rfl⟩ : syracuseStep 235957 = 22121) (by norm_num)
theorem B235993 : Blo 207808 235993 := bbase (se 2 (by rfl) ⟨88497, by rfl⟩ : syracuseStep 235993 = 176995) (by norm_num)
theorem B793061 : Blo 207808 793061 := bbase (se 4 (by rfl) ⟨74349, by rfl⟩ : syracuseStep 793061 = 148699) (by norm_num)
theorem B236029 : Blo 207808 236029 := bbase (se 3 (by rfl) ⟨44255, by rfl⟩ : syracuseStep 236029 = 88511) (by norm_num)
theorem B301573 : Blo 207808 301573 := bbase (se 4 (by rfl) ⟨28272, by rfl⟩ : syracuseStep 301573 = 56545) (by norm_num)
theorem B236065 : Blo 207808 236065 := bbase (se 2 (by rfl) ⟨88524, by rfl⟩ : syracuseStep 236065 = 177049) (by norm_num)
theorem B334381 : Blo 207808 334381 := bbase (se 3 (by rfl) ⟨62696, by rfl⟩ : syracuseStep 334381 = 125393) (by norm_num)
theorem B399917 : Blo 207808 399917 := bbase (se 3 (by rfl) ⟨74984, by rfl⟩ : syracuseStep 399917 = 149969) (by norm_num)
theorem B760373 : Blo 207808 760373 := bbase (se 5 (by rfl) ⟨35642, by rfl⟩ : syracuseStep 760373 = 71285) (by norm_num)
theorem B236101 : Blo 207808 236101 := bbase (se 4 (by rfl) ⟨22134, by rfl⟩ : syracuseStep 236101 = 44269) (by norm_num)
theorem B236137 : Blo 207808 236137 := bbase (se 2 (by rfl) ⟨88551, by rfl⟩ : syracuseStep 236137 = 177103) (by norm_num)
theorem B236173 : Blo 207808 236173 := bbase (se 3 (by rfl) ⟨44282, by rfl⟩ : syracuseStep 236173 = 88565) (by norm_num)
theorem B3054229 : Blo 207808 3054229 := bbase (se 6 (by rfl) ⟨71583, by rfl⟩ : syracuseStep 3054229 = 143167) (by norm_num)
theorem B236209 : Blo 207808 236209 := bbase (se 2 (by rfl) ⟨88578, by rfl⟩ : syracuseStep 236209 = 177157) (by norm_num)
theorem B1055429 : Blo 207808 1055429 := bbase (se 4 (by rfl) ⟨98946, by rfl⟩ : syracuseStep 1055429 = 197893) (by norm_num)
theorem B400069 : Blo 207808 400069 := bbase (se 4 (by rfl) ⟨37506, by rfl⟩ : syracuseStep 400069 = 75013) (by norm_num)
theorem B531157 : Blo 207808 531157 := bbase (se 7 (by rfl) ⟨6224, by rfl⟩ : syracuseStep 531157 = 12449) (by norm_num)
theorem B236245 : Blo 207808 236245 := bbase (se 7 (by rfl) ⟨2768, by rfl⟩ : syracuseStep 236245 = 5537) (by norm_num)
theorem B236281 : Blo 207808 236281 := bbase (se 2 (by rfl) ⟨88605, by rfl⟩ : syracuseStep 236281 = 177211) (by norm_num)
theorem B236317 : Blo 207808 236317 := bbase (se 3 (by rfl) ⟨44309, by rfl⟩ : syracuseStep 236317 = 88619) (by norm_num)
theorem B236353 : Blo 207808 236353 := bbase (se 2 (by rfl) ⟨88632, by rfl⟩ : syracuseStep 236353 = 177265) (by norm_num)
theorem B531269 : Blo 207808 531269 := bbase (se 4 (by rfl) ⟨49806, by rfl⟩ : syracuseStep 531269 = 99613) (by norm_num)
theorem B760661 : Blo 207808 760661 := bbase (se 9 (by rfl) ⟨2228, by rfl⟩ : syracuseStep 760661 = 4457) (by norm_num)
theorem B891749 : Blo 207808 891749 := bbase (se 4 (by rfl) ⟨83601, by rfl⟩ : syracuseStep 891749 = 167203) (by norm_num)
theorem B236389 : Blo 207808 236389 := bbase (se 4 (by rfl) ⟨22161, by rfl⟩ : syracuseStep 236389 = 44323) (by norm_num)
theorem B236425 : Blo 207808 236425 := bbase (se 2 (by rfl) ⟨88659, by rfl⟩ : syracuseStep 236425 = 177319) (by norm_num)
theorem B236461 : Blo 207808 236461 := bbase (se 3 (by rfl) ⟨44336, by rfl⟩ : syracuseStep 236461 = 88673) (by norm_num)
theorem B236497 : Blo 207808 236497 := bbase (se 2 (by rfl) ⟨88686, by rfl⟩ : syracuseStep 236497 = 177373) (by norm_num)
theorem B236533 : Blo 207808 236533 := bbase (se 5 (by rfl) ⟨11087, by rfl⟩ : syracuseStep 236533 = 22175) (by norm_num)
theorem B400373 : Blo 207808 400373 := bbase (se 5 (by rfl) ⟨18767, by rfl⟩ : syracuseStep 400373 = 37535) (by norm_num)
theorem B531461 : Blo 207808 531461 := bbase (se 4 (by rfl) ⟨49824, by rfl⟩ : syracuseStep 531461 = 99649) (by norm_num)
theorem B236569 : Blo 207808 236569 := bbase (se 2 (by rfl) ⟨88713, by rfl⟩ : syracuseStep 236569 = 177427) (by norm_num)
theorem B236605 : Blo 207808 236605 := bbase (se 3 (by rfl) ⟨44363, by rfl⟩ : syracuseStep 236605 = 88727) (by norm_num)
theorem B236641 : Blo 207808 236641 := bbase (se 2 (by rfl) ⟨88740, by rfl⟩ : syracuseStep 236641 = 177481) (by norm_num)
theorem B1055861 : Blo 207808 1055861 := bbase (se 5 (by rfl) ⟨49493, by rfl⟩ : syracuseStep 1055861 = 98987) (by norm_num)
theorem B236677 : Blo 207808 236677 := bbase (se 4 (by rfl) ⟨22188, by rfl⟩ : syracuseStep 236677 = 44377) (by norm_num)
theorem B236713 : Blo 207808 236713 := bbase (se 2 (by rfl) ⟨88767, by rfl⟩ : syracuseStep 236713 = 177535) (by norm_num)
theorem B335021 : Blo 207808 335021 := bbase (se 3 (by rfl) ⟨62816, by rfl⟩ : syracuseStep 335021 = 125633) (by norm_num)
theorem B400565 : Blo 207808 400565 := bbase (se 5 (by rfl) ⟨18776, by rfl⟩ : syracuseStep 400565 = 37553) (by norm_num)
theorem B564421 : Blo 207808 564421 := bbase (se 4 (by rfl) ⟨52914, by rfl⟩ : syracuseStep 564421 = 105829) (by norm_num)
theorem B236749 : Blo 207808 236749 := bbase (se 3 (by rfl) ⟨44390, by rfl⟩ : syracuseStep 236749 = 88781) (by norm_num)
theorem B236785 : Blo 207808 236785 := bbase (se 2 (by rfl) ⟨88794, by rfl⟩ : syracuseStep 236785 = 177589) (by norm_num)
theorem B236821 : Blo 207808 236821 := bbase (se 6 (by rfl) ⟨5550, by rfl⟩ : syracuseStep 236821 = 11101) (by norm_num)
theorem B236857 : Blo 207808 236857 := bbase (se 2 (by rfl) ⟨88821, by rfl⟩ : syracuseStep 236857 = 177643) (by norm_num)
theorem B531805 : Blo 207808 531805 := bbase (se 3 (by rfl) ⟨99713, by rfl⟩ : syracuseStep 531805 = 199427) (by norm_num)
theorem B236893 : Blo 207808 236893 := bbase (se 3 (by rfl) ⟨44417, by rfl⟩ : syracuseStep 236893 = 88835) (by norm_num)
theorem B236929 : Blo 207808 236929 := bbase (se 2 (by rfl) ⟨88848, by rfl⟩ : syracuseStep 236929 = 177697) (by norm_num)
theorem B236965 : Blo 207808 236965 := bbase (se 4 (by rfl) ⟨22215, by rfl⟩ : syracuseStep 236965 = 44431) (by norm_num)
theorem B237001 : Blo 207808 237001 := bbase (se 2 (by rfl) ⟨88875, by rfl⟩ : syracuseStep 237001 = 177751) (by norm_num)
theorem B531917 : Blo 207808 531917 := bbase (se 3 (by rfl) ⟨99734, by rfl⟩ : syracuseStep 531917 = 199469) (by norm_num)
theorem B237037 : Blo 207808 237037 := bbase (se 3 (by rfl) ⟨44444, by rfl⟩ : syracuseStep 237037 = 88889) (by norm_num)
theorem B237073 : Blo 207808 237073 := bbase (se 2 (by rfl) ⟨88902, by rfl⟩ : syracuseStep 237073 = 177805) (by norm_num)
theorem B237109 : Blo 207808 237109 := bbase (se 5 (by rfl) ⟨11114, by rfl⟩ : syracuseStep 237109 = 22229) (by norm_num)
theorem B237145 : Blo 207808 237145 := bbase (se 2 (by rfl) ⟨88929, by rfl⟩ : syracuseStep 237145 = 177859) (by norm_num)
theorem B335477 : Blo 207808 335477 := bbase (se 5 (by rfl) ⟨15725, by rfl⟩ : syracuseStep 335477 = 31451) (by norm_num)
theorem B237181 : Blo 207808 237181 := bbase (se 3 (by rfl) ⟨44471, by rfl⟩ : syracuseStep 237181 = 88943) (by norm_num)
theorem B794245 : Blo 207808 794245 := bbase (se 4 (by rfl) ⟨74460, by rfl⟩ : syracuseStep 794245 = 148921) (by norm_num)
theorem B532109 : Blo 207808 532109 := bbase (se 3 (by rfl) ⟨99770, by rfl⟩ : syracuseStep 532109 = 199541) (by norm_num)
theorem B237217 : Blo 207808 237217 := bbase (se 2 (by rfl) ⟨88956, by rfl⟩ : syracuseStep 237217 = 177913) (by norm_num)
theorem B237253 : Blo 207808 237253 := bbase (se 4 (by rfl) ⟨22242, by rfl⟩ : syracuseStep 237253 = 44485) (by norm_num)
theorem B401125 : Blo 207808 401125 := bbase (se 4 (by rfl) ⟨37605, by rfl⟩ : syracuseStep 401125 = 75211) (by norm_num)
theorem B237289 : Blo 207808 237289 := bbase (se 2 (by rfl) ⟨88983, by rfl⟩ : syracuseStep 237289 = 177967) (by norm_num)
theorem B237325 : Blo 207808 237325 := bbase (se 3 (by rfl) ⟨44498, by rfl⟩ : syracuseStep 237325 = 88997) (by norm_num)
theorem B1154837 : Blo 207808 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B237361 : Blo 207808 237361 := bbase (se 2 (by rfl) ⟨89010, by rfl⟩ : syracuseStep 237361 = 178021) (by norm_num)
theorem B892741 : Blo 207808 892741 := bbase (se 4 (by rfl) ⟨83694, by rfl⟩ : syracuseStep 892741 = 167389) (by norm_num)
theorem B335701 : Blo 207808 335701 := bbase (se 9 (by rfl) ⟨983, by rfl⟩ : syracuseStep 335701 = 1967) (by norm_num)
theorem B237397 : Blo 207808 237397 := bbase (se 9 (by rfl) ⟨695, by rfl⟩ : syracuseStep 237397 = 1391) (by norm_num)
theorem B401269 : Blo 207808 401269 := bbase (se 5 (by rfl) ⟨18809, by rfl⟩ : syracuseStep 401269 = 37619) (by norm_num)
theorem B237433 : Blo 207808 237433 := bbase (se 2 (by rfl) ⟨89037, by rfl⟩ : syracuseStep 237433 = 178075) (by norm_num)
theorem B335765 : Blo 207808 335765 := bbase (se 6 (by rfl) ⟨7869, by rfl⟩ : syracuseStep 335765 = 15739) (by norm_num)
theorem B237469 : Blo 207808 237469 := bbase (se 3 (by rfl) ⟨44525, by rfl⟩ : syracuseStep 237469 = 89051) (by norm_num)
theorem B794549 : Blo 207808 794549 := bbase (se 5 (by rfl) ⟨37244, by rfl⟩ : syracuseStep 794549 = 74489) (by norm_num)
theorem B237505 : Blo 207808 237505 := bbase (se 2 (by rfl) ⟨89064, by rfl⟩ : syracuseStep 237505 = 178129) (by norm_num)
theorem B1056725 : Blo 207808 1056725 := bbase (se 7 (by rfl) ⟨12383, by rfl⟩ : syracuseStep 1056725 = 24767) (by norm_num)
theorem B532453 : Blo 207808 532453 := bbase (se 4 (by rfl) ⟨49917, by rfl⟩ : syracuseStep 532453 = 99835) (by norm_num)
theorem B237541 : Blo 207808 237541 := bbase (se 4 (by rfl) ⟨22269, by rfl⟩ : syracuseStep 237541 = 44539) (by norm_num)
theorem B237577 : Blo 207808 237577 := bbase (se 2 (by rfl) ⟨89091, by rfl⟩ : syracuseStep 237577 = 178183) (by norm_num)
theorem B335893 : Blo 207808 335893 := bbase (se 6 (by rfl) ⟨7872, by rfl⟩ : syracuseStep 335893 = 15745) (by norm_num)
theorem B401429 : Blo 207808 401429 := bbase (se 6 (by rfl) ⟨9408, by rfl⟩ : syracuseStep 401429 = 18817) (by norm_num)
theorem B237613 : Blo 207808 237613 := bbase (se 3 (by rfl) ⟨44552, by rfl⟩ : syracuseStep 237613 = 89105) (by norm_num)
theorem B237649 : Blo 207808 237649 := bbase (se 2 (by rfl) ⟨89118, by rfl⟩ : syracuseStep 237649 = 178237) (by norm_num)
theorem B532565 : Blo 207808 532565 := bbase (se 8 (by rfl) ⟨3120, by rfl⟩ : syracuseStep 532565 = 6241) (by norm_num)
theorem B270425 : Blo 207808 270425 := bbase (se 2 (by rfl) ⟨101409, by rfl⟩ : syracuseStep 270425 = 202819) (by norm_num)
theorem B237685 : Blo 207808 237685 := bbase (se 5 (by rfl) ⟨11141, by rfl⟩ : syracuseStep 237685 = 22283) (by norm_num)
theorem B499861 : Blo 207808 499861 := bbase (se 6 (by rfl) ⟨11715, by rfl⟩ : syracuseStep 499861 = 23431) (by norm_num)
theorem B237721 : Blo 207808 237721 := bbase (se 2 (by rfl) ⟨89145, by rfl⟩ : syracuseStep 237721 = 178291) (by norm_num)
theorem B401573 : Blo 207808 401573 := bbase (se 4 (by rfl) ⟨37647, by rfl⟩ : syracuseStep 401573 = 75295) (by norm_num)
theorem B237757 : Blo 207808 237757 := bbase (se 3 (by rfl) ⟨44579, by rfl⟩ : syracuseStep 237757 = 89159) (by norm_num)
theorem B237793 : Blo 207808 237793 := bbase (se 2 (by rfl) ⟨89172, by rfl⟩ : syracuseStep 237793 = 178345) (by norm_num)
theorem B237829 : Blo 207808 237829 := bbase (se 4 (by rfl) ⟨22296, by rfl⟩ : syracuseStep 237829 = 44593) (by norm_num)
theorem B532757 : Blo 207808 532757 := bbase (se 6 (by rfl) ⟨12486, by rfl⟩ : syracuseStep 532757 = 24973) (by norm_num)
theorem B237865 : Blo 207808 237865 := bbase (se 2 (by rfl) ⟨89199, by rfl⟩ : syracuseStep 237865 = 178399) (by norm_num)
theorem B237901 : Blo 207808 237901 := bbase (se 3 (by rfl) ⟨44606, by rfl⟩ : syracuseStep 237901 = 89213) (by norm_num)
theorem B598373 : Blo 207808 598373 := bbase (se 4 (by rfl) ⟨56097, by rfl⟩ : syracuseStep 598373 = 112195) (by norm_num)
theorem B237937 : Blo 207808 237937 := bbase (se 2 (by rfl) ⟨89226, by rfl⟩ : syracuseStep 237937 = 178453) (by norm_num)
theorem B237973 : Blo 207808 237973 := bbase (se 6 (by rfl) ⟨5577, by rfl⟩ : syracuseStep 237973 = 11155) (by norm_num)
theorem B238009 : Blo 207808 238009 := bbase (se 2 (by rfl) ⟨89253, by rfl⟩ : syracuseStep 238009 = 178507) (by norm_num)
theorem B401861 : Blo 207808 401861 := bbase (se 4 (by rfl) ⟨37674, by rfl⟩ : syracuseStep 401861 = 75349) (by norm_num)
theorem B238045 : Blo 207808 238045 := bbase (se 3 (by rfl) ⟨44633, by rfl⟩ : syracuseStep 238045 = 89267) (by norm_num)
theorem B238081 : Blo 207808 238081 := bbase (se 2 (by rfl) ⟨89280, by rfl⟩ : syracuseStep 238081 = 178561) (by norm_num)
theorem B238117 : Blo 207808 238117 := bbase (se 4 (by rfl) ⟨22323, by rfl⟩ : syracuseStep 238117 = 44647) (by norm_num)
theorem B238153 : Blo 207808 238153 := bbase (se 2 (by rfl) ⟨89307, by rfl⟩ : syracuseStep 238153 = 178615) (by norm_num)
theorem B402013 : Blo 207808 402013 := bbase (se 3 (by rfl) ⟨75377, by rfl⟩ : syracuseStep 402013 = 150755) (by norm_num)
theorem B533101 : Blo 207808 533101 := bbase (se 3 (by rfl) ⟨99956, by rfl⟩ : syracuseStep 533101 = 199913) (by norm_num)
theorem B238189 : Blo 207808 238189 := bbase (se 3 (by rfl) ⟨44660, by rfl⟩ : syracuseStep 238189 = 89321) (by norm_num)
theorem B238225 : Blo 207808 238225 := bbase (se 2 (by rfl) ⟨89334, by rfl⟩ : syracuseStep 238225 = 178669) (by norm_num)
theorem B467621 : Blo 207808 467621 := bbase (se 4 (by rfl) ⟨43839, by rfl⟩ : syracuseStep 467621 = 87679) (by norm_num)
theorem B238261 : Blo 207808 238261 := bbase (se 5 (by rfl) ⟨11168, by rfl⟩ : syracuseStep 238261 = 22337) (by norm_num)
theorem B533213 : Blo 207808 533213 := bbase (se 3 (by rfl) ⟨99977, by rfl⟩ : syracuseStep 533213 = 199955) (by norm_num)
theorem B467693 : Blo 207808 467693 := bbase (se 3 (by rfl) ⟨87692, by rfl⟩ : syracuseStep 467693 = 175385) (by norm_num)
theorem B467765 : Blo 207808 467765 := bbase (se 5 (by rfl) ⟨21926, by rfl⟩ : syracuseStep 467765 = 43853) (by norm_num)
theorem B762709 : Blo 207808 762709 := bbase (se 9 (by rfl) ⟨2234, by rfl⟩ : syracuseStep 762709 = 4469) (by norm_num)
theorem B500573 : Blo 207808 500573 := bbase (se 3 (by rfl) ⟨93857, by rfl⟩ : syracuseStep 500573 = 187715) (by norm_num)
theorem B467837 : Blo 207808 467837 := bbase (se 3 (by rfl) ⟨87719, by rfl⟩ : syracuseStep 467837 = 175439) (by norm_num)
theorem B533405 : Blo 207808 533405 := bbase (se 3 (by rfl) ⟨100013, by rfl⟩ : syracuseStep 533405 = 200027) (by norm_num)
theorem B467909 : Blo 207808 467909 := bbase (se 4 (by rfl) ⟨43866, by rfl⟩ : syracuseStep 467909 = 87733) (by norm_num)
theorem B762853 : Blo 207808 762853 := bbase (se 4 (by rfl) ⟨71517, by rfl⟩ : syracuseStep 762853 = 143035) (by norm_num)
theorem B467981 : Blo 207808 467981 := bbase (se 3 (by rfl) ⟨87746, by rfl⟩ : syracuseStep 467981 = 175493) (by norm_num)
theorem B271441 : Blo 207808 271441 := bbase (se 2 (by rfl) ⟨101790, by rfl⟩ : syracuseStep 271441 = 203581) (by norm_num)
theorem B468053 : Blo 207808 468053 := bbase (se 8 (by rfl) ⟨2742, by rfl⟩ : syracuseStep 468053 = 5485) (by norm_num)
theorem B763013 : Blo 207808 763013 := bbase (se 4 (by rfl) ⟨71532, by rfl⟩ : syracuseStep 763013 = 143065) (by norm_num)
theorem B468125 : Blo 207808 468125 := bbase (se 3 (by rfl) ⟨87773, by rfl⟩ : syracuseStep 468125 = 175547) (by norm_num)
theorem B500957 : Blo 207808 500957 := bbase (se 3 (by rfl) ⟨93929, by rfl⟩ : syracuseStep 500957 = 187859) (by norm_num)
theorem B337117 : Blo 207808 337117 := bbase (se 3 (by rfl) ⟨63209, by rfl⟩ : syracuseStep 337117 = 126419) (by norm_num)
theorem B468197 : Blo 207808 468197 := bbase (se 4 (by rfl) ⟨43893, by rfl⟩ : syracuseStep 468197 = 87787) (by norm_num)
theorem B1058021 : Blo 207808 1058021 := bbase (se 4 (by rfl) ⟨99189, by rfl⟩ : syracuseStep 1058021 = 198379) (by norm_num)
theorem B533749 : Blo 207808 533749 := bbase (se 5 (by rfl) ⟨25019, by rfl⟩ : syracuseStep 533749 = 50039) (by norm_num)
theorem B763141 : Blo 207808 763141 := bbase (se 4 (by rfl) ⟨71544, by rfl⟩ : syracuseStep 763141 = 143089) (by norm_num)
theorem B468269 : Blo 207808 468269 := bbase (se 3 (by rfl) ⟨87800, by rfl⟩ : syracuseStep 468269 = 175601) (by norm_num)
theorem B533861 : Blo 207808 533861 := bbase (se 4 (by rfl) ⟨50049, by rfl⟩ : syracuseStep 533861 = 100099) (by norm_num)
theorem B468341 : Blo 207808 468341 := bbase (se 5 (by rfl) ⟨21953, by rfl⟩ : syracuseStep 468341 = 43907) (by norm_num)
theorem B468413 : Blo 207808 468413 := bbase (se 3 (by rfl) ⟨87827, by rfl⟩ : syracuseStep 468413 = 175655) (by norm_num)
theorem B501245 : Blo 207808 501245 := bbase (se 3 (by rfl) ⟨93983, by rfl⟩ : syracuseStep 501245 = 187967) (by norm_num)
theorem B468485 : Blo 207808 468485 := bbase (se 4 (by rfl) ⟨43920, by rfl⟩ : syracuseStep 468485 = 87841) (by norm_num)
theorem B599557 : Blo 207808 599557 := bbase (se 4 (by rfl) ⟨56208, by rfl⟩ : syracuseStep 599557 = 112417) (by norm_num)
theorem B534053 : Blo 207808 534053 := bbase (se 4 (by rfl) ⟨50067, by rfl⟩ : syracuseStep 534053 = 100135) (by norm_num)
theorem B468557 : Blo 207808 468557 := bbase (se 3 (by rfl) ⟨87854, by rfl⟩ : syracuseStep 468557 = 175709) (by norm_num)
theorem B468629 : Blo 207808 468629 := bbase (se 6 (by rfl) ⟨10983, by rfl⟩ : syracuseStep 468629 = 21967) (by norm_num)
theorem B599717 : Blo 207808 599717 := bbase (se 4 (by rfl) ⟨56223, by rfl⟩ : syracuseStep 599717 = 112447) (by norm_num)
theorem B468701 : Blo 207808 468701 := bbase (se 3 (by rfl) ⟨87881, by rfl⟩ : syracuseStep 468701 = 175763) (by norm_num)
theorem B4073237 : Blo 207808 4073237 := bbase (se 6 (by rfl) ⟨95466, by rfl⟩ : syracuseStep 4073237 = 190933) (by norm_num)
theorem B468773 : Blo 207808 468773 := bbase (se 4 (by rfl) ⟨43947, by rfl⟩ : syracuseStep 468773 = 87895) (by norm_num)
theorem B1582901 : Blo 207808 1582901 := bbase (se 5 (by rfl) ⟨74198, by rfl⟩ : syracuseStep 1582901 = 148397) (by norm_num)
theorem B468845 : Blo 207808 468845 := bbase (se 3 (by rfl) ⟨87908, by rfl⟩ : syracuseStep 468845 = 175817) (by norm_num)
theorem B337789 : Blo 207808 337789 := bbase (se 3 (by rfl) ⟨63335, by rfl⟩ : syracuseStep 337789 = 126671) (by norm_num)
theorem B534397 : Blo 207808 534397 := bbase (se 3 (by rfl) ⟨100199, by rfl⟩ : syracuseStep 534397 = 200399) (by norm_num)
theorem B599957 : Blo 207808 599957 := bbase (se 6 (by rfl) ⟨14061, by rfl⟩ : syracuseStep 599957 = 28123) (by norm_num)
theorem B468917 : Blo 207808 468917 := bbase (se 5 (by rfl) ⟨21980, by rfl⟩ : syracuseStep 468917 = 43961) (by norm_num)
theorem B305093 : Blo 207808 305093 := bbase (se 4 (by rfl) ⟨28602, by rfl⟩ : syracuseStep 305093 = 57205) (by norm_num)
theorem B534509 : Blo 207808 534509 := bbase (se 3 (by rfl) ⟨100220, by rfl⟩ : syracuseStep 534509 = 200441) (by norm_num)
theorem B796661 : Blo 207808 796661 := bbase (se 5 (by rfl) ⟨37343, by rfl⟩ : syracuseStep 796661 = 74687) (by norm_num)
theorem B468989 : Blo 207808 468989 := bbase (se 3 (by rfl) ⟨87935, by rfl⟩ : syracuseStep 468989 = 175871) (by norm_num)
theorem B469061 : Blo 207808 469061 := bbase (se 4 (by rfl) ⟨43974, by rfl⟩ : syracuseStep 469061 = 87949) (by norm_num)
theorem B600149 : Blo 207808 600149 := bbase (se 8 (by rfl) ⟨3516, by rfl⟩ : syracuseStep 600149 = 7033) (by norm_num)
theorem B469133 : Blo 207808 469133 := bbase (se 3 (by rfl) ⟨87962, by rfl⟩ : syracuseStep 469133 = 175925) (by norm_num)
theorem B534701 : Blo 207808 534701 := bbase (se 3 (by rfl) ⟨100256, by rfl⟩ : syracuseStep 534701 = 200513) (by norm_num)
theorem B469205 : Blo 207808 469205 := bbase (se 7 (by rfl) ⟨5498, by rfl⟩ : syracuseStep 469205 = 10997) (by norm_num)
theorem B567557 : Blo 207808 567557 := bbase (se 4 (by rfl) ⟨53208, by rfl⟩ : syracuseStep 567557 = 106417) (by norm_num)
theorem B796949 : Blo 207808 796949 := bbase (se 6 (by rfl) ⟨18678, by rfl⟩ : syracuseStep 796949 = 37357) (by norm_num)
theorem B239893 : Blo 207808 239893 := bbase (se 6 (by rfl) ⟨5622, by rfl⟩ : syracuseStep 239893 = 11245) (by norm_num)
theorem B469277 : Blo 207808 469277 := bbase (se 3 (by rfl) ⟨87989, by rfl⟩ : syracuseStep 469277 = 175979) (by norm_num)
theorem B469349 : Blo 207808 469349 := bbase (se 4 (by rfl) ⟨44001, by rfl⟩ : syracuseStep 469349 = 88003) (by norm_num)
theorem B469421 : Blo 207808 469421 := bbase (se 3 (by rfl) ⟨88016, by rfl⟩ : syracuseStep 469421 = 176033) (by norm_num)
theorem B469493 : Blo 207808 469493 := bbase (se 5 (by rfl) ⟨22007, by rfl⟩ : syracuseStep 469493 = 44015) (by norm_num)
theorem B1059317 : Blo 207808 1059317 := bbase (se 5 (by rfl) ⟨49655, by rfl⟩ : syracuseStep 1059317 = 99311) (by norm_num)
theorem B535045 : Blo 207808 535045 := bbase (se 4 (by rfl) ⟨50160, by rfl⟩ : syracuseStep 535045 = 100321) (by norm_num)
theorem B404021 : Blo 207808 404021 := bbase (se 5 (by rfl) ⟨18938, by rfl⟩ : syracuseStep 404021 = 37877) (by norm_num)
theorem B469565 : Blo 207808 469565 := bbase (se 3 (by rfl) ⟨88043, by rfl⟩ : syracuseStep 469565 = 176087) (by norm_num)
theorem B535157 : Blo 207808 535157 := bbase (se 5 (by rfl) ⟨25085, by rfl⟩ : syracuseStep 535157 = 50171) (by norm_num)
theorem B469637 : Blo 207808 469637 := bbase (se 4 (by rfl) ⟨44028, by rfl⟩ : syracuseStep 469637 = 88057) (by norm_num)
theorem B469709 : Blo 207808 469709 := bbase (se 3 (by rfl) ⟨88070, by rfl⟩ : syracuseStep 469709 = 176141) (by norm_num)
theorem B469781 : Blo 207808 469781 := bbase (se 6 (by rfl) ⟨11010, by rfl⟩ : syracuseStep 469781 = 22021) (by norm_num)
theorem B535349 : Blo 207808 535349 := bbase (se 5 (by rfl) ⟨25094, by rfl⟩ : syracuseStep 535349 = 50189) (by norm_num)
theorem B469853 : Blo 207808 469853 := bbase (se 3 (by rfl) ⟨88097, by rfl⟩ : syracuseStep 469853 = 176195) (by norm_num)
theorem B338789 : Blo 207808 338789 := bbase (se 4 (by rfl) ⟨31761, by rfl⟩ : syracuseStep 338789 = 63523) (by norm_num)
theorem B469925 : Blo 207808 469925 := bbase (se 4 (by rfl) ⟨44055, by rfl⟩ : syracuseStep 469925 = 88111) (by norm_num)
theorem B928741 : Blo 207808 928741 := bbase (se 4 (by rfl) ⟨87069, by rfl⟩ : syracuseStep 928741 = 174139) (by norm_num)
theorem B469997 : Blo 207808 469997 := bbase (se 3 (by rfl) ⟨88124, by rfl⟩ : syracuseStep 469997 = 176249) (by norm_num)
theorem B470069 : Blo 207808 470069 := bbase (se 5 (by rfl) ⟨22034, by rfl⟩ : syracuseStep 470069 = 44069) (by norm_num)
theorem B601141 : Blo 207808 601141 := bbase (se 5 (by rfl) ⟨28178, by rfl⟩ : syracuseStep 601141 = 56357) (by norm_num)
theorem B470141 : Blo 207808 470141 := bbase (se 3 (by rfl) ⟨88151, by rfl⟩ : syracuseStep 470141 = 176303) (by norm_num)
theorem B535693 : Blo 207808 535693 := bbase (se 3 (by rfl) ⟨100442, by rfl⟩ : syracuseStep 535693 = 200885) (by norm_num)
theorem B470213 : Blo 207808 470213 := bbase (se 4 (by rfl) ⟨44082, by rfl⟩ : syracuseStep 470213 = 88165) (by norm_num)
theorem B568549 : Blo 207808 568549 := bbase (se 4 (by rfl) ⟨53301, by rfl⟩ : syracuseStep 568549 = 106603) (by norm_num)
theorem B535805 : Blo 207808 535805 := bbase (se 3 (by rfl) ⟨100463, by rfl⟩ : syracuseStep 535805 = 200927) (by norm_num)
theorem B470285 : Blo 207808 470285 := bbase (se 3 (by rfl) ⟨88178, by rfl⟩ : syracuseStep 470285 = 176357) (by norm_num)
theorem B666917 : Blo 207808 666917 := bbase (se 4 (by rfl) ⟨62523, by rfl⟩ : syracuseStep 666917 = 125047) (by norm_num)
theorem B470357 : Blo 207808 470357 := bbase (se 11 (by rfl) ⟨344, by rfl⟩ : syracuseStep 470357 = 689) (by norm_num)
theorem B3026261 : Blo 207808 3026261 := bbase (se 11 (by rfl) ⟨2216, by rfl⟩ : syracuseStep 3026261 = 4433) (by norm_num)
theorem B470429 : Blo 207808 470429 := bbase (se 3 (by rfl) ⟨88205, by rfl⟩ : syracuseStep 470429 = 176411) (by norm_num)
theorem B798133 : Blo 207808 798133 := bbase (se 5 (by rfl) ⟨37412, by rfl⟩ : syracuseStep 798133 = 74825) (by norm_num)
theorem B535997 : Blo 207808 535997 := bbase (se 3 (by rfl) ⟨100499, by rfl⟩ : syracuseStep 535997 = 200999) (by norm_num)
theorem B470501 : Blo 207808 470501 := bbase (se 4 (by rfl) ⟨44109, by rfl⟩ : syracuseStep 470501 = 88219) (by norm_num)
theorem B470573 : Blo 207808 470573 := bbase (se 3 (by rfl) ⟨88232, by rfl⟩ : syracuseStep 470573 = 176465) (by norm_num)
theorem B405037 : Blo 207808 405037 := bbase (se 3 (by rfl) ⟨75944, by rfl⟩ : syracuseStep 405037 = 151889) (by norm_num)
theorem B831061 : Blo 207808 831061 := bbase (se 8 (by rfl) ⟨4869, by rfl⟩ : syracuseStep 831061 = 9739) (by norm_num)
theorem B470645 : Blo 207808 470645 := bbase (se 5 (by rfl) ⟨22061, by rfl⟩ : syracuseStep 470645 = 44123) (by norm_num)
theorem B470717 : Blo 207808 470717 := bbase (se 3 (by rfl) ⟨88259, by rfl⟩ : syracuseStep 470717 = 176519) (by norm_num)
theorem B798437 : Blo 207808 798437 := bbase (se 4 (by rfl) ⟨74853, by rfl⟩ : syracuseStep 798437 = 149707) (by norm_num)
theorem B470789 : Blo 207808 470789 := bbase (se 4 (by rfl) ⟨44136, by rfl⟩ : syracuseStep 470789 = 88273) (by norm_num)
theorem B1060613 : Blo 207808 1060613 := bbase (se 4 (by rfl) ⟨99432, by rfl⟩ : syracuseStep 1060613 = 198865) (by norm_num)
theorem B470861 : Blo 207808 470861 := bbase (se 3 (by rfl) ⟨88286, by rfl⟩ : syracuseStep 470861 = 176573) (by norm_num)
theorem B1027957 : Blo 207808 1027957 := bbase (se 5 (by rfl) ⟨48185, by rfl⟩ : syracuseStep 1027957 = 96371) (by norm_num)
theorem B470933 : Blo 207808 470933 := bbase (se 6 (by rfl) ⟨11037, by rfl⟩ : syracuseStep 470933 = 22075) (by norm_num)
theorem B471005 : Blo 207808 471005 := bbase (se 3 (by rfl) ⟨88313, by rfl⟩ : syracuseStep 471005 = 176627) (by norm_num)
theorem B667685 : Blo 207808 667685 := bbase (se 4 (by rfl) ⟨62595, by rfl⟩ : syracuseStep 667685 = 125191) (by norm_num)
theorem B471077 : Blo 207808 471077 := bbase (se 4 (by rfl) ⟨44163, by rfl⟩ : syracuseStep 471077 = 88327) (by norm_num)
theorem B634949 : Blo 207808 634949 := bbase (se 4 (by rfl) ⟨59526, by rfl⟩ : syracuseStep 634949 = 119053) (by norm_num)
theorem B471149 : Blo 207808 471149 := bbase (se 3 (by rfl) ⟨88340, by rfl⟩ : syracuseStep 471149 = 176681) (by norm_num)
theorem B602245 : Blo 207808 602245 := bbase (se 4 (by rfl) ⟨56460, by rfl⟩ : syracuseStep 602245 = 112921) (by norm_num)
theorem B471221 : Blo 207808 471221 := bbase (se 5 (by rfl) ⟨22088, by rfl⟩ : syracuseStep 471221 = 44177) (by norm_num)
theorem B471293 : Blo 207808 471293 := bbase (se 3 (by rfl) ⟨88367, by rfl⟩ : syracuseStep 471293 = 176735) (by norm_num)
theorem B471365 : Blo 207808 471365 := bbase (se 4 (by rfl) ⟨44190, by rfl⟩ : syracuseStep 471365 = 88381) (by norm_num)
theorem B471437 : Blo 207808 471437 := bbase (se 3 (by rfl) ⟨88394, by rfl⟩ : syracuseStep 471437 = 176789) (by norm_num)
theorem B471509 : Blo 207808 471509 := bbase (se 7 (by rfl) ⟨5525, by rfl⟩ : syracuseStep 471509 = 11051) (by norm_num)
theorem B504301 : Blo 207808 504301 := bbase (se 3 (by rfl) ⟨94556, by rfl⟩ : syracuseStep 504301 = 189113) (by norm_num)
theorem B471581 : Blo 207808 471581 := bbase (se 3 (by rfl) ⟨88421, by rfl⟩ : syracuseStep 471581 = 176843) (by norm_num)
theorem B668197 : Blo 207808 668197 := bbase (se 4 (by rfl) ⟨62643, by rfl⟩ : syracuseStep 668197 = 125287) (by norm_num)
theorem B471653 : Blo 207808 471653 := bbase (se 4 (by rfl) ⟨44217, by rfl⟩ : syracuseStep 471653 = 88435) (by norm_num)
theorem B471725 : Blo 207808 471725 := bbase (se 3 (by rfl) ⟨88448, by rfl⟩ : syracuseStep 471725 = 176897) (by norm_num)
theorem B897749 : Blo 207808 897749 := bbase (se 7 (by rfl) ⟨10520, by rfl⟩ : syracuseStep 897749 = 21041) (by norm_num)
theorem B471797 : Blo 207808 471797 := bbase (se 5 (by rfl) ⟨22115, by rfl⟩ : syracuseStep 471797 = 44231) (by norm_num)
theorem B471869 : Blo 207808 471869 := bbase (se 3 (by rfl) ⟨88475, by rfl⟩ : syracuseStep 471869 = 176951) (by norm_num)
theorem B471941 : Blo 207808 471941 := bbase (se 4 (by rfl) ⟨44244, by rfl⟩ : syracuseStep 471941 = 88489) (by norm_num)
theorem B472013 : Blo 207808 472013 := bbase (se 3 (by rfl) ⟨88502, by rfl⟩ : syracuseStep 472013 = 177005) (by norm_num)
theorem B898037 : Blo 207808 898037 := bbase (se 5 (by rfl) ⟨42095, by rfl⟩ : syracuseStep 898037 = 84191) (by norm_num)
theorem B1061909 : Blo 207808 1061909 := bbase (se 6 (by rfl) ⟨24888, by rfl⟩ : syracuseStep 1061909 = 49777) (by norm_num)
theorem B472085 : Blo 207808 472085 := bbase (se 6 (by rfl) ⟨11064, by rfl⟩ : syracuseStep 472085 = 22129) (by norm_num)
theorem B504917 : Blo 207808 504917 := bbase (se 8 (by rfl) ⟨2958, by rfl⟩ : syracuseStep 504917 = 5917) (by norm_num)
theorem B472157 : Blo 207808 472157 := bbase (se 3 (by rfl) ⟨88529, by rfl⟩ : syracuseStep 472157 = 177059) (by norm_num)
theorem B472229 : Blo 207808 472229 := bbase (se 4 (by rfl) ⟨44271, by rfl⟩ : syracuseStep 472229 = 88543) (by norm_num)
theorem B701621 : Blo 207808 701621 := bbase (se 5 (by rfl) ⟨32888, by rfl⟩ : syracuseStep 701621 = 65777) (by norm_num)
theorem B472301 : Blo 207808 472301 := bbase (se 3 (by rfl) ⟨88556, by rfl⟩ : syracuseStep 472301 = 177113) (by norm_num)
theorem B963845 : Blo 207808 963845 := bbase (se 4 (by rfl) ⟨90360, by rfl⟩ : syracuseStep 963845 = 180721) (by norm_num)
theorem B1193237 : Blo 207808 1193237 := bbase (se 6 (by rfl) ⟨27966, by rfl⟩ : syracuseStep 1193237 = 55933) (by norm_num)
theorem B505109 : Blo 207808 505109 := bbase (se 6 (by rfl) ⟨11838, by rfl⟩ : syracuseStep 505109 = 23677) (by norm_num)
theorem B472373 : Blo 207808 472373 := bbase (se 5 (by rfl) ⟨22142, by rfl⟩ : syracuseStep 472373 = 44285) (by norm_num)
theorem B472445 : Blo 207808 472445 := bbase (se 3 (by rfl) ⟨88583, by rfl⟩ : syracuseStep 472445 = 177167) (by norm_num)
theorem B472517 : Blo 207808 472517 := bbase (se 4 (by rfl) ⟨44298, by rfl⟩ : syracuseStep 472517 = 88597) (by norm_num)
theorem B472589 : Blo 207808 472589 := bbase (se 3 (by rfl) ⟨88610, by rfl⟩ : syracuseStep 472589 = 177221) (by norm_num)
theorem B472661 : Blo 207808 472661 := bbase (se 8 (by rfl) ⟨2769, by rfl⟩ : syracuseStep 472661 = 5539) (by norm_num)
theorem B702053 : Blo 207808 702053 := bbase (se 4 (by rfl) ⟨65817, by rfl⟩ : syracuseStep 702053 = 131635) (by norm_num)
theorem B996965 : Blo 207808 996965 := bbase (se 4 (by rfl) ⟨93465, by rfl⟩ : syracuseStep 996965 = 186931) (by norm_num)
theorem B472733 : Blo 207808 472733 := bbase (se 3 (by rfl) ⟨88637, by rfl⟩ : syracuseStep 472733 = 177275) (by norm_num)
theorem B472805 : Blo 207808 472805 := bbase (se 4 (by rfl) ⟨44325, by rfl⟩ : syracuseStep 472805 = 88651) (by norm_num)
theorem B898789 : Blo 207808 898789 := bbase (se 4 (by rfl) ⟨84261, by rfl⟩ : syracuseStep 898789 = 168523) (by norm_num)
theorem B800549 : Blo 207808 800549 := bbase (se 4 (by rfl) ⟨75051, by rfl⟩ : syracuseStep 800549 = 150103) (by norm_num)
theorem B472877 : Blo 207808 472877 := bbase (se 3 (by rfl) ⟨88664, by rfl⟩ : syracuseStep 472877 = 177329) (by norm_num)
theorem B505685 : Blo 207808 505685 := bbase (se 9 (by rfl) ⟨1481, by rfl⟩ : syracuseStep 505685 = 2963) (by norm_num)
theorem B472949 : Blo 207808 472949 := bbase (se 5 (by rfl) ⟨22169, by rfl⟩ : syracuseStep 472949 = 44339) (by norm_num)
theorem B473021 : Blo 207808 473021 := bbase (se 3 (by rfl) ⟨88691, by rfl⟩ : syracuseStep 473021 = 177383) (by norm_num)
theorem B473093 : Blo 207808 473093 := bbase (se 4 (by rfl) ⟨44352, by rfl⟩ : syracuseStep 473093 = 88705) (by norm_num)
theorem B702485 : Blo 207808 702485 := bbase (se 6 (by rfl) ⟨16464, by rfl⟩ : syracuseStep 702485 = 32929) (by norm_num)
theorem B800837 : Blo 207808 800837 := bbase (se 4 (by rfl) ⟨75078, by rfl⟩ : syracuseStep 800837 = 150157) (by norm_num)
theorem B473165 : Blo 207808 473165 := bbase (se 3 (by rfl) ⟨88718, by rfl⟩ : syracuseStep 473165 = 177437) (by norm_num)
theorem B4110421 : Blo 207808 4110421 := bbase (se 8 (by rfl) ⟨24084, by rfl⟩ : syracuseStep 4110421 = 48169) (by norm_num)
theorem B211033 : Blo 207808 211033 := bbase (se 2 (by rfl) ⟨79137, by rfl⟩ : syracuseStep 211033 = 158275) (by norm_num)
theorem B473237 : Blo 207808 473237 := bbase (se 6 (by rfl) ⟨11091, by rfl⟩ : syracuseStep 473237 = 22183) (by norm_num)
theorem B2865365 : Blo 207808 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B506069 : Blo 207808 506069 := bbase (se 7 (by rfl) ⟨5930, by rfl⟩ : syracuseStep 506069 = 11861) (by norm_num)
theorem B473309 : Blo 207808 473309 := bbase (se 3 (by rfl) ⟨88745, by rfl⟩ : syracuseStep 473309 = 177491) (by norm_num)
theorem B669941 : Blo 207808 669941 := bbase (se 5 (by rfl) ⟨31403, by rfl⟩ : syracuseStep 669941 = 62807) (by norm_num)
theorem B1063205 : Blo 207808 1063205 := bbase (se 4 (by rfl) ⟨99675, by rfl⟩ : syracuseStep 1063205 = 199351) (by norm_num)
theorem B473381 : Blo 207808 473381 := bbase (se 4 (by rfl) ⟨44379, by rfl⟩ : syracuseStep 473381 = 88759) (by norm_num)
theorem B473453 : Blo 207808 473453 := bbase (se 3 (by rfl) ⟨88772, by rfl⟩ : syracuseStep 473453 = 177545) (by norm_num)
theorem B539045 : Blo 207808 539045 := bbase (se 4 (by rfl) ⟨50535, by rfl⟩ : syracuseStep 539045 = 101071) (by norm_num)
theorem B670133 : Blo 207808 670133 := bbase (se 5 (by rfl) ⟨31412, by rfl⟩ : syracuseStep 670133 = 62825) (by norm_num)
theorem B473525 : Blo 207808 473525 := bbase (se 5 (by rfl) ⟨22196, by rfl⟩ : syracuseStep 473525 = 44393) (by norm_num)
theorem B702917 : Blo 207808 702917 := bbase (se 4 (by rfl) ⟨65898, by rfl⟩ : syracuseStep 702917 = 131797) (by norm_num)
theorem B899525 : Blo 207808 899525 := bbase (se 4 (by rfl) ⟨84330, by rfl⟩ : syracuseStep 899525 = 168661) (by norm_num)
theorem B506341 : Blo 207808 506341 := bbase (se 4 (by rfl) ⟨47469, by rfl⟩ : syracuseStep 506341 = 94939) (by norm_num)
theorem B473597 : Blo 207808 473597 := bbase (se 3 (by rfl) ⟨88799, by rfl⟩ : syracuseStep 473597 = 177599) (by norm_num)
theorem B473669 : Blo 207808 473669 := bbase (se 4 (by rfl) ⟨44406, by rfl⟩ : syracuseStep 473669 = 88813) (by norm_num)
theorem B473741 : Blo 207808 473741 := bbase (se 3 (by rfl) ⟨88826, by rfl⟩ : syracuseStep 473741 = 177653) (by norm_num)
theorem B506525 : Blo 207808 506525 := bbase (se 3 (by rfl) ⟨94973, by rfl⟩ : syracuseStep 506525 = 189947) (by norm_num)
theorem B473813 : Blo 207808 473813 := bbase (se 7 (by rfl) ⟨5552, by rfl⟩ : syracuseStep 473813 = 11105) (by norm_num)
theorem B473885 : Blo 207808 473885 := bbase (se 3 (by rfl) ⟨88853, by rfl⟩ : syracuseStep 473885 = 177707) (by norm_num)
theorem B473957 : Blo 207808 473957 := bbase (se 4 (by rfl) ⟨44433, by rfl⟩ : syracuseStep 473957 = 88867) (by norm_num)
theorem B703349 : Blo 207808 703349 := bbase (se 5 (by rfl) ⟨32969, by rfl⟩ : syracuseStep 703349 = 65939) (by norm_num)
theorem B474029 : Blo 207808 474029 := bbase (se 3 (by rfl) ⟨88880, by rfl⟩ : syracuseStep 474029 = 177761) (by norm_num)
theorem B375797 : Blo 207808 375797 := bbase (se 5 (by rfl) ⟨17615, by rfl⟩ : syracuseStep 375797 = 35231) (by norm_num)
theorem B474101 : Blo 207808 474101 := bbase (se 5 (by rfl) ⟨22223, by rfl⟩ : syracuseStep 474101 = 44447) (by norm_num)
theorem B343037 : Blo 207808 343037 := bbase (se 3 (by rfl) ⟨64319, by rfl⟩ : syracuseStep 343037 = 128639) (by norm_num)
theorem B474173 : Blo 207808 474173 := bbase (se 3 (by rfl) ⟨88907, by rfl⟩ : syracuseStep 474173 = 177815) (by norm_num)
theorem B474245 : Blo 207808 474245 := bbase (se 4 (by rfl) ⟨44460, by rfl⟩ : syracuseStep 474245 = 88921) (by norm_num)
theorem B474317 : Blo 207808 474317 := bbase (se 3 (by rfl) ⟨88934, by rfl⟩ : syracuseStep 474317 = 177869) (by norm_num)
theorem B802021 : Blo 207808 802021 := bbase (se 4 (by rfl) ⟨75189, by rfl⟩ : syracuseStep 802021 = 150379) (by norm_num)
theorem B474389 : Blo 207808 474389 := bbase (se 6 (by rfl) ⟨11118, by rfl⟩ : syracuseStep 474389 = 22237) (by norm_num)
theorem B703781 : Blo 207808 703781 := bbase (se 4 (by rfl) ⟨65979, by rfl⟩ : syracuseStep 703781 = 131959) (by norm_num)
theorem B474461 : Blo 207808 474461 := bbase (se 3 (by rfl) ⟨88961, by rfl⟩ : syracuseStep 474461 = 177923) (by norm_num)
theorem B474533 : Blo 207808 474533 := bbase (se 4 (by rfl) ⟨44487, by rfl⟩ : syracuseStep 474533 = 88975) (by norm_num)
theorem B998837 : Blo 207808 998837 := bbase (se 5 (by rfl) ⟨46820, by rfl⟩ : syracuseStep 998837 = 93641) (by norm_num)
theorem B474605 : Blo 207808 474605 := bbase (se 3 (by rfl) ⟨88988, by rfl⟩ : syracuseStep 474605 = 177977) (by norm_num)
theorem B212501 : Blo 207808 212501 := bbase (se 6 (by rfl) ⟨4980, by rfl⟩ : syracuseStep 212501 = 9961) (by norm_num)
theorem B802325 : Blo 207808 802325 := bbase (se 6 (by rfl) ⟨18804, by rfl⟩ : syracuseStep 802325 = 37609) (by norm_num)
theorem B1064501 : Blo 207808 1064501 := bbase (se 5 (by rfl) ⟨49898, by rfl⟩ : syracuseStep 1064501 = 99797) (by norm_num)
theorem B474677 : Blo 207808 474677 := bbase (se 5 (by rfl) ⟨22250, by rfl⟩ : syracuseStep 474677 = 44501) (by norm_num)
theorem B474749 : Blo 207808 474749 := bbase (se 3 (by rfl) ⟨89015, by rfl⟩ : syracuseStep 474749 = 178031) (by norm_num)
theorem B474821 : Blo 207808 474821 := bbase (se 4 (by rfl) ⟨44514, by rfl⟩ : syracuseStep 474821 = 89029) (by norm_num)
theorem B376525 : Blo 207808 376525 := bbase (se 3 (by rfl) ⟨70598, by rfl⟩ : syracuseStep 376525 = 141197) (by norm_num)
theorem B704213 : Blo 207808 704213 := bbase (se 7 (by rfl) ⟨8252, by rfl⟩ : syracuseStep 704213 = 16505) (by norm_num)
theorem B474893 : Blo 207808 474893 := bbase (se 3 (by rfl) ⟨89042, by rfl⟩ : syracuseStep 474893 = 178085) (by norm_num)
theorem B1785685 : Blo 207808 1785685 := bbase (se 9 (by rfl) ⟨5231, by rfl⟩ : syracuseStep 1785685 = 10463) (by norm_num)
theorem B474965 : Blo 207808 474965 := bbase (se 9 (by rfl) ⟨1391, by rfl⟩ : syracuseStep 474965 = 2783) (by norm_num)
theorem B475037 : Blo 207808 475037 := bbase (se 3 (by rfl) ⟨89069, by rfl⟩ : syracuseStep 475037 = 178139) (by norm_num)
theorem B376741 : Blo 207808 376741 := bbase (se 4 (by rfl) ⟨35319, by rfl⟩ : syracuseStep 376741 = 70639) (by norm_num)
theorem B507829 : Blo 207808 507829 := bbase (se 5 (by rfl) ⟨23804, by rfl⟩ : syracuseStep 507829 = 47609) (by norm_num)
theorem B475109 : Blo 207808 475109 := bbase (se 4 (by rfl) ⟨44541, by rfl⟩ : syracuseStep 475109 = 89083) (by norm_num)
theorem B475181 : Blo 207808 475181 := bbase (se 3 (by rfl) ⟨89096, by rfl⟩ : syracuseStep 475181 = 178193) (by norm_num)
theorem B475253 : Blo 207808 475253 := bbase (se 5 (by rfl) ⟨22277, by rfl⟩ : syracuseStep 475253 = 44555) (by norm_num)
theorem B704645 : Blo 207808 704645 := bbase (se 4 (by rfl) ⟨66060, by rfl⟩ : syracuseStep 704645 = 132121) (by norm_num)
theorem B475325 : Blo 207808 475325 := bbase (se 3 (by rfl) ⟨89123, by rfl⟩ : syracuseStep 475325 = 178247) (by norm_num)
theorem B475397 : Blo 207808 475397 := bbase (se 4 (by rfl) ⟨44568, by rfl⟩ : syracuseStep 475397 = 89137) (by norm_num)
theorem B475469 : Blo 207808 475469 := bbase (se 3 (by rfl) ⟨89150, by rfl⟩ : syracuseStep 475469 = 178301) (by norm_num)
theorem B475541 : Blo 207808 475541 := bbase (se 6 (by rfl) ⟨11145, by rfl⟩ : syracuseStep 475541 = 22291) (by norm_num)
theorem B377245 : Blo 207808 377245 := bbase (se 3 (by rfl) ⟨70733, by rfl⟩ : syracuseStep 377245 = 141467) (by norm_num)
theorem B311717 : Blo 207808 311717 := bbase (se 4 (by rfl) ⟨29223, by rfl⟩ : syracuseStep 311717 = 58447) (by norm_num)
theorem B311741 : Blo 207808 311741 := bbase (se 3 (by rfl) ⟨58451, by rfl⟩ : syracuseStep 311741 = 116903) (by norm_num)
theorem B311765 : Blo 207808 311765 := bbase (se 7 (by rfl) ⟨3653, by rfl⟩ : syracuseStep 311765 = 7307) (by norm_num)
theorem B4047317 : Blo 207808 4047317 := bbase (se 7 (by rfl) ⟨47429, by rfl⟩ : syracuseStep 4047317 = 94859) (by norm_num)
theorem B475613 : Blo 207808 475613 := bbase (se 3 (by rfl) ⟨89177, by rfl⟩ : syracuseStep 475613 = 178355) (by norm_num)
theorem B311789 : Blo 207808 311789 := bbase (se 3 (by rfl) ⟨58460, by rfl⟩ : syracuseStep 311789 = 116921) (by norm_num)
theorem B311813 : Blo 207808 311813 := bbase (se 4 (by rfl) ⟨29232, by rfl⟩ : syracuseStep 311813 = 58465) (by norm_num)
theorem B311837 : Blo 207808 311837 := bbase (se 3 (by rfl) ⟨58469, by rfl⟩ : syracuseStep 311837 = 116939) (by norm_num)
theorem B475685 : Blo 207808 475685 := bbase (se 4 (by rfl) ⟨44595, by rfl⟩ : syracuseStep 475685 = 89191) (by norm_num)
theorem B311861 : Blo 207808 311861 := bbase (se 5 (by rfl) ⟨14618, by rfl⟩ : syracuseStep 311861 = 29237) (by norm_num)
theorem B705077 : Blo 207808 705077 := bbase (se 5 (by rfl) ⟨33050, by rfl⟩ : syracuseStep 705077 = 66101) (by norm_num)
theorem B770629 : Blo 207808 770629 := bbase (se 4 (by rfl) ⟨72246, by rfl⟩ : syracuseStep 770629 = 144493) (by norm_num)
theorem B311885 : Blo 207808 311885 := bbase (se 3 (by rfl) ⟨58478, by rfl⟩ : syracuseStep 311885 = 116957) (by norm_num)
theorem B311909 : Blo 207808 311909 := bbase (se 4 (by rfl) ⟨29241, by rfl⟩ : syracuseStep 311909 = 58483) (by norm_num)
theorem B475757 : Blo 207808 475757 := bbase (se 3 (by rfl) ⟨89204, by rfl⟩ : syracuseStep 475757 = 178409) (by norm_num)
theorem B311933 : Blo 207808 311933 := bbase (se 3 (by rfl) ⟨58487, by rfl⟩ : syracuseStep 311933 = 116975) (by norm_num)
theorem B311957 : Blo 207808 311957 := bbase (se 6 (by rfl) ⟨7311, by rfl⟩ : syracuseStep 311957 = 14623) (by norm_num)
theorem B311981 : Blo 207808 311981 := bbase (se 3 (by rfl) ⟨58496, by rfl⟩ : syracuseStep 311981 = 116993) (by norm_num)
theorem B475829 : Blo 207808 475829 := bbase (se 5 (by rfl) ⟨22304, by rfl⟩ : syracuseStep 475829 = 44609) (by norm_num)
theorem B312005 : Blo 207808 312005 := bbase (se 4 (by rfl) ⟨29250, by rfl⟩ : syracuseStep 312005 = 58501) (by norm_num)
theorem B312029 : Blo 207808 312029 := bbase (se 3 (by rfl) ⟨58505, by rfl⟩ : syracuseStep 312029 = 117011) (by norm_num)
theorem B312053 : Blo 207808 312053 := bbase (se 5 (by rfl) ⟨14627, by rfl⟩ : syracuseStep 312053 = 29255) (by norm_num)
theorem B475901 : Blo 207808 475901 := bbase (se 3 (by rfl) ⟨89231, by rfl⟩ : syracuseStep 475901 = 178463) (by norm_num)
theorem B312077 : Blo 207808 312077 := bbase (se 3 (by rfl) ⟨58514, by rfl⟩ : syracuseStep 312077 = 117029) (by norm_num)
theorem B312101 : Blo 207808 312101 := bbase (se 4 (by rfl) ⟨29259, by rfl⟩ : syracuseStep 312101 = 58519) (by norm_num)
theorem B312125 : Blo 207808 312125 := bbase (se 3 (by rfl) ⟨58523, by rfl⟩ : syracuseStep 312125 = 117047) (by norm_num)
theorem B1065797 : Blo 207808 1065797 := bbase (se 4 (by rfl) ⟨99918, by rfl⟩ : syracuseStep 1065797 = 199837) (by norm_num)
theorem B475973 : Blo 207808 475973 := bbase (se 4 (by rfl) ⟨44622, by rfl⟩ : syracuseStep 475973 = 89245) (by norm_num)
theorem B312149 : Blo 207808 312149 := bbase (se 9 (by rfl) ⟨914, by rfl⟩ : syracuseStep 312149 = 1829) (by norm_num)
theorem B312173 : Blo 207808 312173 := bbase (se 3 (by rfl) ⟨58532, by rfl⟩ : syracuseStep 312173 = 117065) (by norm_num)
theorem B312197 : Blo 207808 312197 := bbase (se 4 (by rfl) ⟨29268, by rfl⟩ : syracuseStep 312197 = 58537) (by norm_num)
theorem B476045 : Blo 207808 476045 := bbase (se 3 (by rfl) ⟨89258, by rfl⟩ : syracuseStep 476045 = 178517) (by norm_num)
theorem B312221 : Blo 207808 312221 := bbase (se 3 (by rfl) ⟨58541, by rfl⟩ : syracuseStep 312221 = 117083) (by norm_num)
theorem B508837 : Blo 207808 508837 := bbase (se 4 (by rfl) ⟨47703, by rfl⟩ : syracuseStep 508837 = 95407) (by norm_num)
theorem B312245 : Blo 207808 312245 := bbase (se 5 (by rfl) ⟨14636, by rfl⟩ : syracuseStep 312245 = 29273) (by norm_num)
theorem B312269 : Blo 207808 312269 := bbase (se 3 (by rfl) ⟨58550, by rfl⟩ : syracuseStep 312269 = 117101) (by norm_num)
theorem B476117 : Blo 207808 476117 := bbase (se 7 (by rfl) ⟨5579, by rfl⟩ : syracuseStep 476117 = 11159) (by norm_num)
theorem B312293 : Blo 207808 312293 := bbase (se 4 (by rfl) ⟨29277, by rfl⟩ : syracuseStep 312293 = 58555) (by norm_num)
theorem B705509 : Blo 207808 705509 := bbase (se 4 (by rfl) ⟨66141, by rfl⟩ : syracuseStep 705509 = 132283) (by norm_num)
theorem B312317 : Blo 207808 312317 := bbase (se 3 (by rfl) ⟨58559, by rfl⟩ : syracuseStep 312317 = 117119) (by norm_num)
theorem B312341 : Blo 207808 312341 := bbase (se 6 (by rfl) ⟨7320, by rfl⟩ : syracuseStep 312341 = 14641) (by norm_num)
theorem B476189 : Blo 207808 476189 := bbase (se 3 (by rfl) ⟨89285, by rfl⟩ : syracuseStep 476189 = 178571) (by norm_num)
theorem B312365 : Blo 207808 312365 := bbase (se 3 (by rfl) ⟨58568, by rfl⟩ : syracuseStep 312365 = 117137) (by norm_num)
theorem B312389 : Blo 207808 312389 := bbase (se 4 (by rfl) ⟨29286, by rfl⟩ : syracuseStep 312389 = 58573) (by norm_num)
theorem B312413 : Blo 207808 312413 := bbase (se 3 (by rfl) ⟨58577, by rfl⟩ : syracuseStep 312413 = 117155) (by norm_num)
theorem B476261 : Blo 207808 476261 := bbase (se 4 (by rfl) ⟨44649, by rfl⟩ : syracuseStep 476261 = 89299) (by norm_num)
theorem B312437 : Blo 207808 312437 := bbase (se 5 (by rfl) ⟨14645, by rfl⟩ : syracuseStep 312437 = 29291) (by norm_num)
theorem B312461 : Blo 207808 312461 := bbase (se 3 (by rfl) ⟨58586, by rfl⟩ : syracuseStep 312461 = 117173) (by norm_num)
theorem B312485 : Blo 207808 312485 := bbase (se 4 (by rfl) ⟨29295, by rfl⟩ : syracuseStep 312485 = 58591) (by norm_num)
theorem B476333 : Blo 207808 476333 := bbase (se 3 (by rfl) ⟨89312, by rfl⟩ : syracuseStep 476333 = 178625) (by norm_num)
theorem B312509 : Blo 207808 312509 := bbase (se 3 (by rfl) ⟨58595, by rfl⟩ : syracuseStep 312509 = 117191) (by norm_num)
theorem B312533 : Blo 207808 312533 := bbase (se 7 (by rfl) ⟨3662, by rfl⟩ : syracuseStep 312533 = 7325) (by norm_num)
theorem B312557 : Blo 207808 312557 := bbase (se 3 (by rfl) ⟨58604, by rfl⟩ : syracuseStep 312557 = 117209) (by norm_num)
theorem B476405 : Blo 207808 476405 := bbase (se 5 (by rfl) ⟨22331, by rfl⟩ : syracuseStep 476405 = 44663) (by norm_num)
theorem B312581 : Blo 207808 312581 := bbase (se 4 (by rfl) ⟨29304, by rfl⟩ : syracuseStep 312581 = 58609) (by norm_num)
theorem B1525013 : Blo 207808 1525013 := bbase (se 6 (by rfl) ⟨35742, by rfl⟩ : syracuseStep 1525013 = 71485) (by norm_num)
theorem B312605 : Blo 207808 312605 := bbase (se 3 (by rfl) ⟨58613, by rfl⟩ : syracuseStep 312605 = 117227) (by norm_num)
theorem B214309 : Blo 207808 214309 := bbase (se 4 (by rfl) ⟨20091, by rfl⟩ : syracuseStep 214309 = 40183) (by norm_num)
theorem B312629 : Blo 207808 312629 := bbase (se 5 (by rfl) ⟨14654, by rfl⟩ : syracuseStep 312629 = 29309) (by norm_num)
theorem B476477 : Blo 207808 476477 := bbase (se 3 (by rfl) ⟨89339, by rfl⟩ : syracuseStep 476477 = 178679) (by norm_num)
theorem B312653 : Blo 207808 312653 := bbase (se 3 (by rfl) ⟨58622, by rfl⟩ : syracuseStep 312653 = 117245) (by norm_num)
theorem B312677 : Blo 207808 312677 := bbase (se 4 (by rfl) ⟨29313, by rfl⟩ : syracuseStep 312677 = 58627) (by norm_num)
theorem B214373 : Blo 207808 214373 := bbase (se 4 (by rfl) ⟨20097, by rfl⟩ : syracuseStep 214373 = 40195) (by norm_num)
theorem B312701 : Blo 207808 312701 := bbase (se 3 (by rfl) ⟨58631, by rfl⟩ : syracuseStep 312701 = 117263) (by norm_num)
theorem B476549 : Blo 207808 476549 := bbase (se 4 (by rfl) ⟨44676, by rfl⟩ : syracuseStep 476549 = 89353) (by norm_num)
theorem B312725 : Blo 207808 312725 := bbase (se 6 (by rfl) ⟨7329, by rfl⟩ : syracuseStep 312725 = 14659) (by norm_num)
theorem B705941 : Blo 207808 705941 := bbase (se 6 (by rfl) ⟨16545, by rfl⟩ : syracuseStep 705941 = 33091) (by norm_num)
theorem B1590677 : Blo 207808 1590677 := bbase (se 6 (by rfl) ⟨37281, by rfl⟩ : syracuseStep 1590677 = 74563) (by norm_num)
theorem B312749 : Blo 207808 312749 := bbase (se 3 (by rfl) ⟨58640, by rfl⟩ : syracuseStep 312749 = 117281) (by norm_num)
theorem B312773 : Blo 207808 312773 := bbase (se 4 (by rfl) ⟨29322, by rfl⟩ : syracuseStep 312773 = 58645) (by norm_num)
theorem B312797 : Blo 207808 312797 := bbase (se 3 (by rfl) ⟨58649, by rfl⟩ : syracuseStep 312797 = 117299) (by norm_num)
theorem B312821 : Blo 207808 312821 := bbase (se 5 (by rfl) ⟨14663, by rfl⟩ : syracuseStep 312821 = 29327) (by norm_num)
theorem B443893 : Blo 207808 443893 := bbase (se 5 (by rfl) ⟨20807, by rfl⟩ : syracuseStep 443893 = 41615) (by norm_num)
theorem B312845 : Blo 207808 312845 := bbase (se 3 (by rfl) ⟨58658, by rfl⟩ : syracuseStep 312845 = 117317) (by norm_num)
theorem B312869 : Blo 207808 312869 := bbase (se 4 (by rfl) ⟨29331, by rfl⟩ : syracuseStep 312869 = 58663) (by norm_num)
theorem B312893 : Blo 207808 312893 := bbase (se 3 (by rfl) ⟨58667, by rfl⟩ : syracuseStep 312893 = 117335) (by norm_num)
theorem B312917 : Blo 207808 312917 := bbase (se 8 (by rfl) ⟨1833, by rfl⟩ : syracuseStep 312917 = 3667) (by norm_num)
theorem B312941 : Blo 207808 312941 := bbase (se 3 (by rfl) ⟨58676, by rfl⟩ : syracuseStep 312941 = 117353) (by norm_num)
theorem B312965 : Blo 207808 312965 := bbase (se 4 (by rfl) ⟨29340, by rfl⟩ : syracuseStep 312965 = 58681) (by norm_num)
theorem B312989 : Blo 207808 312989 := bbase (se 3 (by rfl) ⟨58685, by rfl⟩ : syracuseStep 312989 = 117371) (by norm_num)
theorem B902821 : Blo 207808 902821 := bbase (se 4 (by rfl) ⟨84639, by rfl⟩ : syracuseStep 902821 = 169279) (by norm_num)
theorem B313013 : Blo 207808 313013 := bbase (se 5 (by rfl) ⟨14672, by rfl⟩ : syracuseStep 313013 = 29345) (by norm_num)
theorem B476869 : Blo 207808 476869 := bbase (se 4 (by rfl) ⟨44706, by rfl⟩ : syracuseStep 476869 = 89413) (by norm_num)
theorem B313037 : Blo 207808 313037 := bbase (se 3 (by rfl) ⟨58694, by rfl⟩ : syracuseStep 313037 = 117389) (by norm_num)
theorem B313061 : Blo 207808 313061 := bbase (se 4 (by rfl) ⟨29349, by rfl⟩ : syracuseStep 313061 = 58699) (by norm_num)
theorem B313085 : Blo 207808 313085 := bbase (se 3 (by rfl) ⟨58703, by rfl⟩ : syracuseStep 313085 = 117407) (by norm_num)
theorem B313109 : Blo 207808 313109 := bbase (se 6 (by rfl) ⟨7338, by rfl⟩ : syracuseStep 313109 = 14677) (by norm_num)
theorem B1787669 : Blo 207808 1787669 := bbase (se 6 (by rfl) ⟨41898, by rfl⟩ : syracuseStep 1787669 = 83797) (by norm_num)
theorem B313133 : Blo 207808 313133 := bbase (se 3 (by rfl) ⟨58712, by rfl⟩ : syracuseStep 313133 = 117425) (by norm_num)
theorem B313157 : Blo 207808 313157 := bbase (se 4 (by rfl) ⟨29358, by rfl⟩ : syracuseStep 313157 = 58717) (by norm_num)
theorem B706373 : Blo 207808 706373 := bbase (se 4 (by rfl) ⟨66222, by rfl⟩ : syracuseStep 706373 = 132445) (by norm_num)
theorem B313181 : Blo 207808 313181 := bbase (se 3 (by rfl) ⟨58721, by rfl⟩ : syracuseStep 313181 = 117443) (by norm_num)
theorem B313205 : Blo 207808 313205 := bbase (se 5 (by rfl) ⟨14681, by rfl⟩ : syracuseStep 313205 = 29363) (by norm_num)
theorem B313229 : Blo 207808 313229 := bbase (se 3 (by rfl) ⟨58730, by rfl⟩ : syracuseStep 313229 = 117461) (by norm_num)
theorem B313253 : Blo 207808 313253 := bbase (se 4 (by rfl) ⟨29367, by rfl⟩ : syracuseStep 313253 = 58735) (by norm_num)
theorem B313277 : Blo 207808 313277 := bbase (se 3 (by rfl) ⟨58739, by rfl⟩ : syracuseStep 313277 = 117479) (by norm_num)
theorem B673733 : Blo 207808 673733 := bbase (se 4 (by rfl) ⟨63162, by rfl⟩ : syracuseStep 673733 = 126325) (by norm_num)
theorem B313301 : Blo 207808 313301 := bbase (se 7 (by rfl) ⟨3671, by rfl⟩ : syracuseStep 313301 = 7343) (by norm_num)
theorem B313325 : Blo 207808 313325 := bbase (se 3 (by rfl) ⟨58748, by rfl⟩ : syracuseStep 313325 = 117497) (by norm_num)
theorem B575477 : Blo 207808 575477 := bbase (se 5 (by rfl) ⟨26975, by rfl⟩ : syracuseStep 575477 = 53951) (by norm_num)
theorem B313349 : Blo 207808 313349 := bbase (se 4 (by rfl) ⟨29376, by rfl⟩ : syracuseStep 313349 = 58753) (by norm_num)
theorem B313373 : Blo 207808 313373 := bbase (se 3 (by rfl) ⟨58757, by rfl⟩ : syracuseStep 313373 = 117515) (by norm_num)
theorem B313397 : Blo 207808 313397 := bbase (se 5 (by rfl) ⟨14690, by rfl⟩ : syracuseStep 313397 = 29381) (by norm_num)
theorem B313421 : Blo 207808 313421 := bbase (se 3 (by rfl) ⟨58766, by rfl⟩ : syracuseStep 313421 = 117533) (by norm_num)
theorem B12863573 : Blo 207808 12863573 := bbase (se 8 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 12863573 = 150745) (by norm_num)
theorem B1067093 : Blo 207808 1067093 := bbase (se 8 (by rfl) ⟨6252, by rfl⟩ : syracuseStep 1067093 = 12505) (by norm_num)
theorem B313445 : Blo 207808 313445 := bbase (se 4 (by rfl) ⟨29385, by rfl⟩ : syracuseStep 313445 = 58771) (by norm_num)
theorem B313469 : Blo 207808 313469 := bbase (se 3 (by rfl) ⟨58775, by rfl⟩ : syracuseStep 313469 = 117551) (by norm_num)
theorem B1001605 : Blo 207808 1001605 := bbase (se 4 (by rfl) ⟨93900, by rfl⟩ : syracuseStep 1001605 = 187801) (by norm_num)
theorem B313493 : Blo 207808 313493 := bbase (se 6 (by rfl) ⟨7347, by rfl⟩ : syracuseStep 313493 = 14695) (by norm_num)
theorem B313517 : Blo 207808 313517 := bbase (se 3 (by rfl) ⟨58784, by rfl⟩ : syracuseStep 313517 = 117569) (by norm_num)
theorem B313541 : Blo 207808 313541 := bbase (se 4 (by rfl) ⟨29394, by rfl⟩ : syracuseStep 313541 = 58789) (by norm_num)
theorem B313565 : Blo 207808 313565 := bbase (se 3 (by rfl) ⟨58793, by rfl⟩ : syracuseStep 313565 = 117587) (by norm_num)
theorem B313589 : Blo 207808 313589 := bbase (se 5 (by rfl) ⟨14699, by rfl⟩ : syracuseStep 313589 = 29399) (by norm_num)
theorem B706805 : Blo 207808 706805 := bbase (se 5 (by rfl) ⟨33131, by rfl⟩ : syracuseStep 706805 = 66263) (by norm_num)
theorem B313613 : Blo 207808 313613 := bbase (se 3 (by rfl) ⟨58802, by rfl⟩ : syracuseStep 313613 = 117605) (by norm_num)
theorem B313637 : Blo 207808 313637 := bbase (se 4 (by rfl) ⟨29403, by rfl⟩ : syracuseStep 313637 = 58807) (by norm_num)
theorem B313661 : Blo 207808 313661 := bbase (se 3 (by rfl) ⟨58811, by rfl⟩ : syracuseStep 313661 = 117623) (by norm_num)
theorem B313685 : Blo 207808 313685 := bbase (se 10 (by rfl) ⟨459, by rfl⟩ : syracuseStep 313685 = 919) (by norm_num)
theorem B444781 : Blo 207808 444781 := bbase (se 3 (by rfl) ⟨83396, by rfl⟩ : syracuseStep 444781 = 166793) (by norm_num)
theorem B313709 : Blo 207808 313709 := bbase (se 3 (by rfl) ⟨58820, by rfl⟩ : syracuseStep 313709 = 117641) (by norm_num)
theorem B313733 : Blo 207808 313733 := bbase (se 4 (by rfl) ⟨29412, by rfl⟩ : syracuseStep 313733 = 58825) (by norm_num)
theorem B313757 : Blo 207808 313757 := bbase (se 3 (by rfl) ⟨58829, by rfl⟩ : syracuseStep 313757 = 117659) (by norm_num)
theorem B313781 : Blo 207808 313781 := bbase (se 5 (by rfl) ⟨14708, by rfl⟩ : syracuseStep 313781 = 29417) (by norm_num)
theorem B313805 : Blo 207808 313805 := bbase (se 3 (by rfl) ⟨58838, by rfl⟩ : syracuseStep 313805 = 117677) (by norm_num)
theorem B313829 : Blo 207808 313829 := bbase (se 4 (by rfl) ⟨29421, by rfl⟩ : syracuseStep 313829 = 58843) (by norm_num)
theorem B2017781 : Blo 207808 2017781 := bbase (se 5 (by rfl) ⟨94583, by rfl⟩ : syracuseStep 2017781 = 189167) (by norm_num)
theorem B313853 : Blo 207808 313853 := bbase (se 3 (by rfl) ⟨58847, by rfl⟩ : syracuseStep 313853 = 117695) (by norm_num)
theorem B313877 : Blo 207808 313877 := bbase (se 6 (by rfl) ⟨7356, by rfl⟩ : syracuseStep 313877 = 14713) (by norm_num)
theorem B313901 : Blo 207808 313901 := bbase (se 3 (by rfl) ⟨58856, by rfl⟩ : syracuseStep 313901 = 117713) (by norm_num)
theorem B313925 : Blo 207808 313925 := bbase (se 4 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 313925 = 58861) (by norm_num)
theorem B313949 : Blo 207808 313949 := bbase (se 3 (by rfl) ⟨58865, by rfl⟩ : syracuseStep 313949 = 117731) (by norm_num)
theorem B313973 : Blo 207808 313973 := bbase (se 5 (by rfl) ⟨14717, by rfl⟩ : syracuseStep 313973 = 29435) (by norm_num)
theorem B313997 : Blo 207808 313997 := bbase (se 3 (by rfl) ⟨58874, by rfl⟩ : syracuseStep 313997 = 117749) (by norm_num)
theorem B314021 : Blo 207808 314021 := bbase (se 4 (by rfl) ⟨29439, by rfl⟩ : syracuseStep 314021 = 58879) (by norm_num)
theorem B707237 : Blo 207808 707237 := bbase (se 4 (by rfl) ⟨66303, by rfl⟩ : syracuseStep 707237 = 132607) (by norm_num)
theorem B510637 : Blo 207808 510637 := bbase (se 3 (by rfl) ⟨95744, by rfl⟩ : syracuseStep 510637 = 191489) (by norm_num)
theorem B1067701 : Blo 207808 1067701 := bbase (se 5 (by rfl) ⟨50048, by rfl⟩ : syracuseStep 1067701 = 100097) (by norm_num)
theorem B314045 : Blo 207808 314045 := bbase (se 3 (by rfl) ⟨58883, by rfl⟩ : syracuseStep 314045 = 117767) (by norm_num)
theorem B314069 : Blo 207808 314069 := bbase (se 7 (by rfl) ⟨3680, by rfl⟩ : syracuseStep 314069 = 7361) (by norm_num)
theorem B314093 : Blo 207808 314093 := bbase (se 3 (by rfl) ⟨58892, by rfl⟩ : syracuseStep 314093 = 117785) (by norm_num)
theorem B314117 : Blo 207808 314117 := bbase (se 4 (by rfl) ⟨29448, by rfl⟩ : syracuseStep 314117 = 58897) (by norm_num)
theorem B314141 : Blo 207808 314141 := bbase (se 3 (by rfl) ⟨58901, by rfl⟩ : syracuseStep 314141 = 117803) (by norm_num)
theorem B281389 : Blo 207808 281389 := bbase (se 3 (by rfl) ⟨52760, by rfl⟩ : syracuseStep 281389 = 105521) (by norm_num)
theorem B314165 : Blo 207808 314165 := bbase (se 5 (by rfl) ⟨14726, by rfl⟩ : syracuseStep 314165 = 29453) (by norm_num)
theorem B314189 : Blo 207808 314189 := bbase (se 3 (by rfl) ⟨58910, by rfl⟩ : syracuseStep 314189 = 117821) (by norm_num)
theorem B445277 : Blo 207808 445277 := bbase (se 3 (by rfl) ⟨83489, by rfl⟩ : syracuseStep 445277 = 166979) (by norm_num)
theorem B314213 : Blo 207808 314213 := bbase (se 4 (by rfl) ⟨29457, by rfl⟩ : syracuseStep 314213 = 58915) (by norm_num)
theorem B314237 : Blo 207808 314237 := bbase (se 3 (by rfl) ⟨58919, by rfl⟩ : syracuseStep 314237 = 117839) (by norm_num)
theorem B314261 : Blo 207808 314261 := bbase (se 6 (by rfl) ⟨7365, by rfl⟩ : syracuseStep 314261 = 14731) (by norm_num)
theorem B314285 : Blo 207808 314285 := bbase (se 3 (by rfl) ⟨58928, by rfl⟩ : syracuseStep 314285 = 117857) (by norm_num)
theorem B314309 : Blo 207808 314309 := bbase (se 4 (by rfl) ⟨29466, by rfl⟩ : syracuseStep 314309 = 58933) (by norm_num)
theorem B8604629 : Blo 207808 8604629 := bbase (se 7 (by rfl) ⟨100835, by rfl⟩ : syracuseStep 8604629 = 201671) (by norm_num)
theorem B314333 : Blo 207808 314333 := bbase (se 3 (by rfl) ⟨58937, by rfl⟩ : syracuseStep 314333 = 117875) (by norm_num)
theorem B314357 : Blo 207808 314357 := bbase (se 5 (by rfl) ⟨14735, by rfl⟩ : syracuseStep 314357 = 29471) (by norm_num)
theorem B314381 : Blo 207808 314381 := bbase (se 3 (by rfl) ⟨58946, by rfl⟩ : syracuseStep 314381 = 117893) (by norm_num)
theorem B314405 : Blo 207808 314405 := bbase (se 4 (by rfl) ⟨29475, by rfl⟩ : syracuseStep 314405 = 58951) (by norm_num)
theorem B314429 : Blo 207808 314429 := bbase (se 3 (by rfl) ⟨58955, by rfl⟩ : syracuseStep 314429 = 117911) (by norm_num)
theorem B314453 : Blo 207808 314453 := bbase (se 8 (by rfl) ⟨1842, by rfl⟩ : syracuseStep 314453 = 3685) (by norm_num)
theorem B707669 : Blo 207808 707669 := bbase (se 8 (by rfl) ⟨4146, by rfl⟩ : syracuseStep 707669 = 8293) (by norm_num)
theorem B314477 : Blo 207808 314477 := bbase (se 3 (by rfl) ⟨58964, by rfl⟩ : syracuseStep 314477 = 117929) (by norm_num)
theorem B314501 : Blo 207808 314501 := bbase (se 4 (by rfl) ⟨29484, by rfl⟩ : syracuseStep 314501 = 58969) (by norm_num)
theorem B642197 : Blo 207808 642197 := bbase (se 6 (by rfl) ⟨15051, by rfl⟩ : syracuseStep 642197 = 30103) (by norm_num)
theorem B314525 : Blo 207808 314525 := bbase (se 3 (by rfl) ⟨58973, by rfl⟩ : syracuseStep 314525 = 117947) (by norm_num)
theorem B314549 : Blo 207808 314549 := bbase (se 5 (by rfl) ⟨14744, by rfl⟩ : syracuseStep 314549 = 29489) (by norm_num)
theorem B314573 : Blo 207808 314573 := bbase (se 3 (by rfl) ⟨58982, by rfl⟩ : syracuseStep 314573 = 117965) (by norm_num)
theorem B314597 : Blo 207808 314597 := bbase (se 4 (by rfl) ⟨29493, by rfl⟩ : syracuseStep 314597 = 58987) (by norm_num)
theorem B314621 : Blo 207808 314621 := bbase (se 3 (by rfl) ⟨58991, by rfl⟩ : syracuseStep 314621 = 117983) (by norm_num)
theorem B314645 : Blo 207808 314645 := bbase (se 6 (by rfl) ⟨7374, by rfl⟩ : syracuseStep 314645 = 14749) (by norm_num)
theorem B314669 : Blo 207808 314669 := bbase (se 3 (by rfl) ⟨59000, by rfl⟩ : syracuseStep 314669 = 118001) (by norm_num)
theorem B2149685 : Blo 207808 2149685 := bbase (se 5 (by rfl) ⟨100766, by rfl⟩ : syracuseStep 2149685 = 201533) (by norm_num)
theorem B314693 : Blo 207808 314693 := bbase (se 4 (by rfl) ⟨29502, by rfl⟩ : syracuseStep 314693 = 59005) (by norm_num)
theorem B314717 : Blo 207808 314717 := bbase (se 3 (by rfl) ⟨59009, by rfl⟩ : syracuseStep 314717 = 118019) (by norm_num)
theorem B1068389 : Blo 207808 1068389 := bbase (se 4 (by rfl) ⟨100161, by rfl⟩ : syracuseStep 1068389 = 200323) (by norm_num)
theorem B314741 : Blo 207808 314741 := bbase (se 5 (by rfl) ⟨14753, by rfl⟩ : syracuseStep 314741 = 29507) (by norm_num)
theorem B314765 : Blo 207808 314765 := bbase (se 3 (by rfl) ⟨59018, by rfl⟩ : syracuseStep 314765 = 118037) (by norm_num)
theorem B314789 : Blo 207808 314789 := bbase (se 4 (by rfl) ⟨29511, by rfl⟩ : syracuseStep 314789 = 59023) (by norm_num)
theorem B314813 : Blo 207808 314813 := bbase (se 3 (by rfl) ⟨59027, by rfl⟩ : syracuseStep 314813 = 118055) (by norm_num)
theorem B314837 : Blo 207808 314837 := bbase (se 7 (by rfl) ⟨3689, by rfl⟩ : syracuseStep 314837 = 7379) (by norm_num)
theorem B314861 : Blo 207808 314861 := bbase (se 3 (by rfl) ⟨59036, by rfl⟩ : syracuseStep 314861 = 118073) (by norm_num)
theorem B708101 : Blo 207808 708101 := bbase (se 4 (by rfl) ⟨66384, by rfl⟩ : syracuseStep 708101 = 132769) (by norm_num)
theorem B314885 : Blo 207808 314885 := bbase (se 4 (by rfl) ⟨29520, by rfl⟩ : syracuseStep 314885 = 59041) (by norm_num)
theorem B314909 : Blo 207808 314909 := bbase (se 3 (by rfl) ⟨59045, by rfl⟩ : syracuseStep 314909 = 118091) (by norm_num)
theorem B314933 : Blo 207808 314933 := bbase (se 5 (by rfl) ⟨14762, by rfl⟩ : syracuseStep 314933 = 29525) (by norm_num)
theorem B314957 : Blo 207808 314957 := bbase (se 3 (by rfl) ⟨59054, by rfl⟩ : syracuseStep 314957 = 118109) (by norm_num)
theorem B314981 : Blo 207808 314981 := bbase (se 4 (by rfl) ⟨29529, by rfl⟩ : syracuseStep 314981 = 59059) (by norm_num)
theorem B380533 : Blo 207808 380533 := bbase (se 5 (by rfl) ⟨17837, by rfl⟩ : syracuseStep 380533 = 35675) (by norm_num)
theorem B315005 : Blo 207808 315005 := bbase (se 3 (by rfl) ⟨59063, by rfl⟩ : syracuseStep 315005 = 118127) (by norm_num)
theorem B315029 : Blo 207808 315029 := bbase (se 6 (by rfl) ⟨7383, by rfl⟩ : syracuseStep 315029 = 14767) (by norm_num)
theorem B315053 : Blo 207808 315053 := bbase (se 3 (by rfl) ⟨59072, by rfl⟩ : syracuseStep 315053 = 118145) (by norm_num)
theorem B446141 : Blo 207808 446141 := bbase (se 3 (by rfl) ⟨83651, by rfl⟩ : syracuseStep 446141 = 167303) (by norm_num)
theorem B315077 : Blo 207808 315077 := bbase (se 4 (by rfl) ⟨29538, by rfl⟩ : syracuseStep 315077 = 59077) (by norm_num)
theorem B315101 : Blo 207808 315101 := bbase (se 3 (by rfl) ⟨59081, by rfl⟩ : syracuseStep 315101 = 118163) (by norm_num)
theorem B315125 : Blo 207808 315125 := bbase (se 5 (by rfl) ⟨14771, by rfl⟩ : syracuseStep 315125 = 29543) (by norm_num)
theorem B315149 : Blo 207808 315149 := bbase (se 3 (by rfl) ⟨59090, by rfl⟩ : syracuseStep 315149 = 118181) (by norm_num)
theorem B315173 : Blo 207808 315173 := bbase (se 4 (by rfl) ⟨29547, by rfl⟩ : syracuseStep 315173 = 59095) (by norm_num)
theorem B315197 : Blo 207808 315197 := bbase (se 3 (by rfl) ⟨59099, by rfl⟩ : syracuseStep 315197 = 118199) (by norm_num)
theorem B446285 : Blo 207808 446285 := bbase (se 3 (by rfl) ⟨83678, by rfl⟩ : syracuseStep 446285 = 167357) (by norm_num)
theorem B315221 : Blo 207808 315221 := bbase (se 9 (by rfl) ⟨923, by rfl⟩ : syracuseStep 315221 = 1847) (by norm_num)
theorem B315245 : Blo 207808 315245 := bbase (se 3 (by rfl) ⟨59108, by rfl⟩ : syracuseStep 315245 = 118217) (by norm_num)
theorem B315269 : Blo 207808 315269 := bbase (se 4 (by rfl) ⟨29556, by rfl⟩ : syracuseStep 315269 = 59113) (by norm_num)
theorem B380821 : Blo 207808 380821 := bbase (se 6 (by rfl) ⟨8925, by rfl⟩ : syracuseStep 380821 = 17851) (by norm_num)
theorem B315293 : Blo 207808 315293 := bbase (se 3 (by rfl) ⟨59117, by rfl⟩ : syracuseStep 315293 = 118235) (by norm_num)
theorem B708533 : Blo 207808 708533 := bbase (se 5 (by rfl) ⟨33212, by rfl⟩ : syracuseStep 708533 = 66425) (by norm_num)
theorem B315317 : Blo 207808 315317 := bbase (se 5 (by rfl) ⟨14780, by rfl⟩ : syracuseStep 315317 = 29561) (by norm_num)
theorem B315341 : Blo 207808 315341 := bbase (se 3 (by rfl) ⟨59126, by rfl⟩ : syracuseStep 315341 = 118253) (by norm_num)
theorem B806869 : Blo 207808 806869 := bbase (se 7 (by rfl) ⟨9455, by rfl⟩ : syracuseStep 806869 = 18911) (by norm_num)
theorem B315365 : Blo 207808 315365 := bbase (se 4 (by rfl) ⟨29565, by rfl⟩ : syracuseStep 315365 = 59131) (by norm_num)
theorem B315389 : Blo 207808 315389 := bbase (se 3 (by rfl) ⟨59135, by rfl⟩ : syracuseStep 315389 = 118271) (by norm_num)
theorem B315413 : Blo 207808 315413 := bbase (se 6 (by rfl) ⟨7392, by rfl⟩ : syracuseStep 315413 = 14785) (by norm_num)
theorem B315437 : Blo 207808 315437 := bbase (se 3 (by rfl) ⟨59144, by rfl⟩ : syracuseStep 315437 = 118289) (by norm_num)
theorem B315461 : Blo 207808 315461 := bbase (se 4 (by rfl) ⟨29574, by rfl⟩ : syracuseStep 315461 = 59149) (by norm_num)
theorem B315485 : Blo 207808 315485 := bbase (se 3 (by rfl) ⟨59153, by rfl⟩ : syracuseStep 315485 = 118307) (by norm_num)
theorem B315509 : Blo 207808 315509 := bbase (se 5 (by rfl) ⟨14789, by rfl⟩ : syracuseStep 315509 = 29579) (by norm_num)
theorem B315533 : Blo 207808 315533 := bbase (se 3 (by rfl) ⟨59162, by rfl⟩ : syracuseStep 315533 = 118325) (by norm_num)
theorem B675989 : Blo 207808 675989 := bbase (se 6 (by rfl) ⟨15843, by rfl⟩ : syracuseStep 675989 = 31687) (by norm_num)
theorem B315557 : Blo 207808 315557 := bbase (se 4 (by rfl) ⟨29583, by rfl⟩ : syracuseStep 315557 = 59167) (by norm_num)
theorem B315581 : Blo 207808 315581 := bbase (se 3 (by rfl) ⟨59171, by rfl⟩ : syracuseStep 315581 = 118343) (by norm_num)
theorem B315605 : Blo 207808 315605 := bbase (se 7 (by rfl) ⟨3698, by rfl⟩ : syracuseStep 315605 = 7397) (by norm_num)
theorem B315629 : Blo 207808 315629 := bbase (se 3 (by rfl) ⟨59180, by rfl⟩ : syracuseStep 315629 = 118361) (by norm_num)
theorem B315653 : Blo 207808 315653 := bbase (se 4 (by rfl) ⟨29592, by rfl⟩ : syracuseStep 315653 = 59185) (by norm_num)
theorem B676117 : Blo 207808 676117 := bbase (se 6 (by rfl) ⟨15846, by rfl⟩ : syracuseStep 676117 = 31693) (by norm_num)
theorem B315677 : Blo 207808 315677 := bbase (se 3 (by rfl) ⟨59189, by rfl⟩ : syracuseStep 315677 = 118379) (by norm_num)
theorem B315701 : Blo 207808 315701 := bbase (se 5 (by rfl) ⟨14798, by rfl⟩ : syracuseStep 315701 = 29597) (by norm_num)
theorem B315725 : Blo 207808 315725 := bbase (se 3 (by rfl) ⟨59198, by rfl⟩ : syracuseStep 315725 = 118397) (by norm_num)
theorem B381277 : Blo 207808 381277 := bbase (se 3 (by rfl) ⟨71489, by rfl⟩ : syracuseStep 381277 = 142979) (by norm_num)
theorem B708965 : Blo 207808 708965 := bbase (se 4 (by rfl) ⟨66465, by rfl⟩ : syracuseStep 708965 = 132931) (by norm_num)
theorem B315749 : Blo 207808 315749 := bbase (se 4 (by rfl) ⟨29601, by rfl⟩ : syracuseStep 315749 = 59203) (by norm_num)
theorem B315773 : Blo 207808 315773 := bbase (se 3 (by rfl) ⟨59207, by rfl⟩ : syracuseStep 315773 = 118415) (by norm_num)
theorem B315797 : Blo 207808 315797 := bbase (se 6 (by rfl) ⟨7401, by rfl⟩ : syracuseStep 315797 = 14803) (by norm_num)
theorem B217505 : Blo 207808 217505 := bbase (se 2 (by rfl) ⟨81564, by rfl⟩ : syracuseStep 217505 = 163129) (by norm_num)
theorem B315821 : Blo 207808 315821 := bbase (se 3 (by rfl) ⟨59216, by rfl⟩ : syracuseStep 315821 = 118433) (by norm_num)
theorem B315845 : Blo 207808 315845 := bbase (se 4 (by rfl) ⟨29610, by rfl⟩ : syracuseStep 315845 = 59221) (by norm_num)
theorem B381397 : Blo 207808 381397 := bbase (se 7 (by rfl) ⟨4469, by rfl⟩ : syracuseStep 381397 = 8939) (by norm_num)
theorem B315869 : Blo 207808 315869 := bbase (se 3 (by rfl) ⟨59225, by rfl⟩ : syracuseStep 315869 = 118451) (by norm_num)
theorem B315893 : Blo 207808 315893 := bbase (se 5 (by rfl) ⟨14807, by rfl⟩ : syracuseStep 315893 = 29615) (by norm_num)
theorem B315917 : Blo 207808 315917 := bbase (se 3 (by rfl) ⟨59234, by rfl⟩ : syracuseStep 315917 = 118469) (by norm_num)
theorem B315941 : Blo 207808 315941 := bbase (se 4 (by rfl) ⟨29619, by rfl⟩ : syracuseStep 315941 = 59239) (by norm_num)
theorem B447029 : Blo 207808 447029 := bbase (se 5 (by rfl) ⟨20954, by rfl⟩ : syracuseStep 447029 = 41909) (by norm_num)
theorem B315965 : Blo 207808 315965 := bbase (se 3 (by rfl) ⟨59243, by rfl⟩ : syracuseStep 315965 = 118487) (by norm_num)
theorem B315989 : Blo 207808 315989 := bbase (se 8 (by rfl) ⟨1851, by rfl⟩ : syracuseStep 315989 = 3703) (by norm_num)
theorem B316013 : Blo 207808 316013 := bbase (se 3 (by rfl) ⟨59252, by rfl⟩ : syracuseStep 316013 = 118505) (by norm_num)
theorem B479861 : Blo 207808 479861 := bbase (se 5 (by rfl) ⟨22493, by rfl⟩ : syracuseStep 479861 = 44987) (by norm_num)
theorem B1069685 : Blo 207808 1069685 := bbase (se 5 (by rfl) ⟨50141, by rfl⟩ : syracuseStep 1069685 = 100283) (by norm_num)
theorem B316037 : Blo 207808 316037 := bbase (se 4 (by rfl) ⟨29628, by rfl⟩ : syracuseStep 316037 = 59257) (by norm_num)
theorem B316061 : Blo 207808 316061 := bbase (se 3 (by rfl) ⟨59261, by rfl⟩ : syracuseStep 316061 = 118523) (by norm_num)
theorem B316085 : Blo 207808 316085 := bbase (se 5 (by rfl) ⟨14816, by rfl⟩ : syracuseStep 316085 = 29633) (by norm_num)
theorem B479933 : Blo 207808 479933 := bbase (se 3 (by rfl) ⟨89987, by rfl⟩ : syracuseStep 479933 = 179975) (by norm_num)
theorem B316109 : Blo 207808 316109 := bbase (se 3 (by rfl) ⟨59270, by rfl⟩ : syracuseStep 316109 = 118541) (by norm_num)
theorem B217829 : Blo 207808 217829 := bbase (se 4 (by rfl) ⟨20421, by rfl⟩ : syracuseStep 217829 = 40843) (by norm_num)
theorem B316133 : Blo 207808 316133 := bbase (se 4 (by rfl) ⟨29637, by rfl⟩ : syracuseStep 316133 = 59275) (by norm_num)
theorem B316157 : Blo 207808 316157 := bbase (se 3 (by rfl) ⟨59279, by rfl⟩ : syracuseStep 316157 = 118559) (by norm_num)
theorem B283405 : Blo 207808 283405 := bbase (se 3 (by rfl) ⟨53138, by rfl⟩ : syracuseStep 283405 = 106277) (by norm_num)
theorem B709397 : Blo 207808 709397 := bbase (se 6 (by rfl) ⟨16626, by rfl⟩ : syracuseStep 709397 = 33253) (by norm_num)
theorem B316181 : Blo 207808 316181 := bbase (se 6 (by rfl) ⟨7410, by rfl⟩ : syracuseStep 316181 = 14821) (by norm_num)
theorem B316205 : Blo 207808 316205 := bbase (se 3 (by rfl) ⟨59288, by rfl⟩ : syracuseStep 316205 = 118577) (by norm_num)
theorem B316229 : Blo 207808 316229 := bbase (se 4 (by rfl) ⟨29646, by rfl⟩ : syracuseStep 316229 = 59293) (by norm_num)
theorem B316253 : Blo 207808 316253 := bbase (se 3 (by rfl) ⟨59297, by rfl⟩ : syracuseStep 316253 = 118595) (by norm_num)
theorem B316277 : Blo 207808 316277 := bbase (se 5 (by rfl) ⟨14825, by rfl⟩ : syracuseStep 316277 = 29651) (by norm_num)
theorem B316301 : Blo 207808 316301 := bbase (se 3 (by rfl) ⟨59306, by rfl⟩ : syracuseStep 316301 = 118613) (by norm_num)
theorem B971669 : Blo 207808 971669 := bbase (se 6 (by rfl) ⟨22773, by rfl⟩ : syracuseStep 971669 = 45547) (by norm_num)
theorem B316325 : Blo 207808 316325 := bbase (se 4 (by rfl) ⟨29655, by rfl⟩ : syracuseStep 316325 = 59311) (by norm_num)
theorem B1135541 : Blo 207808 1135541 := bbase (se 5 (by rfl) ⟨53228, by rfl⟩ : syracuseStep 1135541 = 106457) (by norm_num)
theorem B316349 : Blo 207808 316349 := bbase (se 3 (by rfl) ⟨59315, by rfl⟩ : syracuseStep 316349 = 118631) (by norm_num)
theorem B316373 : Blo 207808 316373 := bbase (se 7 (by rfl) ⟨3707, by rfl⟩ : syracuseStep 316373 = 7415) (by norm_num)
theorem B316381 : Blo 207808 316381 := bbase (se 3 (by rfl) ⟨59321, by rfl⟩ : syracuseStep 316381 = 118643) (by norm_num)
theorem B316397 : Blo 207808 316397 := bbase (se 3 (by rfl) ⟨59324, by rfl⟩ : syracuseStep 316397 = 118649) (by norm_num)
theorem B316421 : Blo 207808 316421 := bbase (se 4 (by rfl) ⟨29664, by rfl⟩ : syracuseStep 316421 = 59329) (by norm_num)
theorem B316445 : Blo 207808 316445 := bbase (se 3 (by rfl) ⟨59333, by rfl⟩ : syracuseStep 316445 = 118667) (by norm_num)
theorem B316469 : Blo 207808 316469 := bbase (se 5 (by rfl) ⟨14834, by rfl⟩ : syracuseStep 316469 = 29669) (by norm_num)
theorem B316493 : Blo 207808 316493 := bbase (se 3 (by rfl) ⟨59342, by rfl⟩ : syracuseStep 316493 = 118685) (by norm_num)
theorem B316517 : Blo 207808 316517 := bbase (se 4 (by rfl) ⟨29673, by rfl⟩ : syracuseStep 316517 = 59347) (by norm_num)
theorem B250997 : Blo 207808 250997 := bbase (se 5 (by rfl) ⟨11765, by rfl⟩ : syracuseStep 250997 = 23531) (by norm_num)
theorem B316541 : Blo 207808 316541 := bbase (se 3 (by rfl) ⟨59351, by rfl⟩ : syracuseStep 316541 = 118703) (by norm_num)
theorem B1201301 : Blo 207808 1201301 := bbase (se 6 (by rfl) ⟨28155, by rfl⟩ : syracuseStep 1201301 = 56311) (by norm_num)
theorem B316565 : Blo 207808 316565 := bbase (se 6 (by rfl) ⟨7419, by rfl⟩ : syracuseStep 316565 = 14839) (by norm_num)
theorem B316589 : Blo 207808 316589 := bbase (se 3 (by rfl) ⟨59360, by rfl⟩ : syracuseStep 316589 = 118721) (by norm_num)
theorem B382133 : Blo 207808 382133 := bbase (se 5 (by rfl) ⟨17912, by rfl⟩ : syracuseStep 382133 = 35825) (by norm_num)
theorem B709829 : Blo 207808 709829 := bbase (se 4 (by rfl) ⟨66546, by rfl⟩ : syracuseStep 709829 = 133093) (by norm_num)
theorem B316613 : Blo 207808 316613 := bbase (se 4 (by rfl) ⟨29682, by rfl⟩ : syracuseStep 316613 = 59365) (by norm_num)
theorem B316637 : Blo 207808 316637 := bbase (se 3 (by rfl) ⟨59369, by rfl⟩ : syracuseStep 316637 = 118739) (by norm_num)
theorem B316661 : Blo 207808 316661 := bbase (se 5 (by rfl) ⟨14843, by rfl⟩ : syracuseStep 316661 = 29687) (by norm_num)
theorem B316685 : Blo 207808 316685 := bbase (se 3 (by rfl) ⟨59378, by rfl⟩ : syracuseStep 316685 = 118757) (by norm_num)
theorem B447781 : Blo 207808 447781 := bbase (se 4 (by rfl) ⟨41979, by rfl⟩ : syracuseStep 447781 = 83959) (by norm_num)
theorem B316709 : Blo 207808 316709 := bbase (se 4 (by rfl) ⟨29691, by rfl⟩ : syracuseStep 316709 = 59383) (by norm_num)
theorem B316733 : Blo 207808 316733 := bbase (se 3 (by rfl) ⟨59387, by rfl⟩ : syracuseStep 316733 = 118775) (by norm_num)
theorem B480581 : Blo 207808 480581 := bbase (se 4 (by rfl) ⟨45054, by rfl⟩ : syracuseStep 480581 = 90109) (by norm_num)
theorem B251209 : Blo 207808 251209 := bbase (se 2 (by rfl) ⟨94203, by rfl⟩ : syracuseStep 251209 = 188407) (by norm_num)
theorem B316757 : Blo 207808 316757 := bbase (se 15 (by rfl) ⟨14, by rfl⟩ : syracuseStep 316757 = 29) (by norm_num)
theorem B316781 : Blo 207808 316781 := bbase (se 3 (by rfl) ⟨59396, by rfl⟩ : syracuseStep 316781 = 118793) (by norm_num)
theorem B316805 : Blo 207808 316805 := bbase (se 4 (by rfl) ⟨29700, by rfl⟩ : syracuseStep 316805 = 59401) (by norm_num)
theorem B316829 : Blo 207808 316829 := bbase (se 3 (by rfl) ⟨59405, by rfl⟩ : syracuseStep 316829 = 118811) (by norm_num)
theorem B447925 : Blo 207808 447925 := bbase (se 5 (by rfl) ⟨20996, by rfl⟩ : syracuseStep 447925 = 41993) (by norm_num)
theorem B316853 : Blo 207808 316853 := bbase (se 5 (by rfl) ⟨14852, by rfl⟩ : syracuseStep 316853 = 29705) (by norm_num)
theorem B316877 : Blo 207808 316877 := bbase (se 3 (by rfl) ⟨59414, by rfl⟩ : syracuseStep 316877 = 118829) (by norm_num)
theorem B316885 : Blo 207808 316885 := bbase (se 7 (by rfl) ⟨3713, by rfl⟩ : syracuseStep 316885 = 7427) (by norm_num)
theorem B251353 : Blo 207808 251353 := bbase (se 2 (by rfl) ⟨94257, by rfl⟩ : syracuseStep 251353 = 188515) (by norm_num)
theorem B316901 : Blo 207808 316901 := bbase (se 4 (by rfl) ⟨29709, by rfl⟩ : syracuseStep 316901 = 59419) (by norm_num)
theorem B316925 : Blo 207808 316925 := bbase (se 3 (by rfl) ⟨59423, by rfl⟩ : syracuseStep 316925 = 118847) (by norm_num)
theorem B480773 : Blo 207808 480773 := bbase (se 4 (by rfl) ⟨45072, by rfl⟩ : syracuseStep 480773 = 90145) (by norm_num)
theorem B316949 : Blo 207808 316949 := bbase (se 6 (by rfl) ⟨7428, by rfl⟩ : syracuseStep 316949 = 14857) (by norm_num)
theorem B316973 : Blo 207808 316973 := bbase (se 3 (by rfl) ⟨59432, by rfl⟩ : syracuseStep 316973 = 118865) (by norm_num)
theorem B316997 : Blo 207808 316997 := bbase (se 4 (by rfl) ⟨29718, by rfl⟩ : syracuseStep 316997 = 59437) (by norm_num)
theorem B317021 : Blo 207808 317021 := bbase (se 3 (by rfl) ⟨59441, by rfl⟩ : syracuseStep 317021 = 118883) (by norm_num)
theorem B710261 : Blo 207808 710261 := bbase (se 5 (by rfl) ⟨33293, by rfl⟩ : syracuseStep 710261 = 66587) (by norm_num)
theorem B317045 : Blo 207808 317045 := bbase (se 5 (by rfl) ⟨14861, by rfl⟩ : syracuseStep 317045 = 29723) (by norm_num)
theorem B480901 : Blo 207808 480901 := bbase (se 4 (by rfl) ⟨45084, by rfl⟩ : syracuseStep 480901 = 90169) (by norm_num)
theorem B317069 : Blo 207808 317069 := bbase (se 3 (by rfl) ⟨59450, by rfl⟩ : syracuseStep 317069 = 118901) (by norm_num)
theorem B317093 : Blo 207808 317093 := bbase (se 4 (by rfl) ⟨29727, by rfl⟩ : syracuseStep 317093 = 59455) (by norm_num)
theorem B317117 : Blo 207808 317117 := bbase (se 3 (by rfl) ⟨59459, by rfl⟩ : syracuseStep 317117 = 118919) (by norm_num)
theorem B317141 : Blo 207808 317141 := bbase (se 7 (by rfl) ⟨3716, by rfl⟩ : syracuseStep 317141 = 7433) (by norm_num)
theorem B317165 : Blo 207808 317165 := bbase (se 3 (by rfl) ⟨59468, by rfl⟩ : syracuseStep 317165 = 118937) (by norm_num)
theorem B317189 : Blo 207808 317189 := bbase (se 4 (by rfl) ⟨29736, by rfl⟩ : syracuseStep 317189 = 59473) (by norm_num)
theorem B317213 : Blo 207808 317213 := bbase (se 3 (by rfl) ⟨59477, by rfl⟩ : syracuseStep 317213 = 118955) (by norm_num)
theorem B448301 : Blo 207808 448301 := bbase (se 3 (by rfl) ⟨84056, by rfl⟩ : syracuseStep 448301 = 168113) (by norm_num)
theorem B317237 : Blo 207808 317237 := bbase (se 5 (by rfl) ⟨14870, by rfl⟩ : syracuseStep 317237 = 29741) (by norm_num)
theorem B317261 : Blo 207808 317261 := bbase (se 3 (by rfl) ⟨59486, by rfl⟩ : syracuseStep 317261 = 118973) (by norm_num)
theorem B317285 : Blo 207808 317285 := bbase (se 4 (by rfl) ⟨29745, by rfl⟩ : syracuseStep 317285 = 59491) (by norm_num)
theorem B317309 : Blo 207808 317309 := bbase (se 3 (by rfl) ⟨59495, by rfl⟩ : syracuseStep 317309 = 118991) (by norm_num)
theorem B1070981 : Blo 207808 1070981 := bbase (se 4 (by rfl) ⟨100404, by rfl⟩ : syracuseStep 1070981 = 200809) (by norm_num)
theorem B317333 : Blo 207808 317333 := bbase (se 6 (by rfl) ⟨7437, by rfl⟩ : syracuseStep 317333 = 14875) (by norm_num)
theorem B317357 : Blo 207808 317357 := bbase (se 3 (by rfl) ⟨59504, by rfl⟩ : syracuseStep 317357 = 119009) (by norm_num)
theorem B317381 : Blo 207808 317381 := bbase (se 4 (by rfl) ⟨29754, by rfl⟩ : syracuseStep 317381 = 59509) (by norm_num)
theorem B317405 : Blo 207808 317405 := bbase (se 3 (by rfl) ⟨59513, by rfl⟩ : syracuseStep 317405 = 119027) (by norm_num)
theorem B317429 : Blo 207808 317429 := bbase (se 5 (by rfl) ⟨14879, by rfl⟩ : syracuseStep 317429 = 29759) (by norm_num)
theorem B317453 : Blo 207808 317453 := bbase (se 3 (by rfl) ⟨59522, by rfl⟩ : syracuseStep 317453 = 119045) (by norm_num)
theorem B710693 : Blo 207808 710693 := bbase (se 4 (by rfl) ⟨66627, by rfl⟩ : syracuseStep 710693 = 133255) (by norm_num)
theorem B317477 : Blo 207808 317477 := bbase (se 4 (by rfl) ⟨29763, by rfl⟩ : syracuseStep 317477 = 59527) (by norm_num)
theorem B317501 : Blo 207808 317501 := bbase (se 3 (by rfl) ⟨59531, by rfl⟩ : syracuseStep 317501 = 119063) (by norm_num)
theorem B317525 : Blo 207808 317525 := bbase (se 8 (by rfl) ⟨1860, by rfl⟩ : syracuseStep 317525 = 3721) (by norm_num)
theorem B317549 : Blo 207808 317549 := bbase (se 3 (by rfl) ⟨59540, by rfl⟩ : syracuseStep 317549 = 119081) (by norm_num)
theorem B317573 : Blo 207808 317573 := bbase (se 4 (by rfl) ⟨29772, by rfl⟩ : syracuseStep 317573 = 59545) (by norm_num)
theorem B3037333 : Blo 207808 3037333 := bbase (se 6 (by rfl) ⟨71187, by rfl⟩ : syracuseStep 3037333 = 142375) (by norm_num)
theorem B448669 : Blo 207808 448669 := bbase (se 3 (by rfl) ⟨84125, by rfl⟩ : syracuseStep 448669 = 168251) (by norm_num)
theorem B317597 : Blo 207808 317597 := bbase (se 3 (by rfl) ⟨59549, by rfl⟩ : syracuseStep 317597 = 119099) (by norm_num)
theorem B317621 : Blo 207808 317621 := bbase (se 5 (by rfl) ⟨14888, by rfl⟩ : syracuseStep 317621 = 29777) (by norm_num)
theorem B317645 : Blo 207808 317645 := bbase (se 3 (by rfl) ⟨59558, by rfl⟩ : syracuseStep 317645 = 119117) (by norm_num)
theorem B317669 : Blo 207808 317669 := bbase (se 4 (by rfl) ⟨29781, by rfl⟩ : syracuseStep 317669 = 59563) (by norm_num)
theorem B317693 : Blo 207808 317693 := bbase (se 3 (by rfl) ⟨59567, by rfl⟩ : syracuseStep 317693 = 119135) (by norm_num)
theorem B1202485 : Blo 207808 1202485 := bbase (se 5 (by rfl) ⟨56366, by rfl⟩ : syracuseStep 1202485 = 112733) (by norm_num)
theorem B711125 : Blo 207808 711125 := bbase (se 7 (by rfl) ⟨8333, by rfl⟩ : syracuseStep 711125 = 16667) (by norm_num)
theorem B350797 : Blo 207808 350797 := bbase (se 3 (by rfl) ⟨65774, by rfl⟩ : syracuseStep 350797 = 131549) (by norm_num)
theorem B1006181 : Blo 207808 1006181 := bbase (se 4 (by rfl) ⟨94329, by rfl⟩ : syracuseStep 1006181 = 188659) (by norm_num)
theorem B350885 : Blo 207808 350885 := bbase (se 4 (by rfl) ⟨32895, by rfl⟩ : syracuseStep 350885 = 65791) (by norm_num)
theorem B940709 : Blo 207808 940709 := bbase (se 4 (by rfl) ⟨88191, by rfl⟩ : syracuseStep 940709 = 176383) (by norm_num)
theorem B351013 : Blo 207808 351013 := bbase (se 4 (by rfl) ⟨32907, by rfl⟩ : syracuseStep 351013 = 65815) (by norm_num)
theorem B351101 : Blo 207808 351101 := bbase (se 3 (by rfl) ⟨65831, by rfl⟩ : syracuseStep 351101 = 131663) (by norm_num)
theorem B711557 : Blo 207808 711557 := bbase (se 4 (by rfl) ⟨66708, by rfl⟩ : syracuseStep 711557 = 133417) (by norm_num)
theorem B351229 : Blo 207808 351229 := bbase (se 3 (by rfl) ⟨65855, by rfl⟩ : syracuseStep 351229 = 131711) (by norm_num)
theorem B252929 : Blo 207808 252929 := bbase (se 2 (by rfl) ⟨94848, by rfl⟩ : syracuseStep 252929 = 189697) (by norm_num)
theorem B351317 : Blo 207808 351317 := bbase (se 8 (by rfl) ⟨2058, by rfl⟩ : syracuseStep 351317 = 4117) (by norm_num)
theorem B1072277 : Blo 207808 1072277 := bbase (se 6 (by rfl) ⟨25131, by rfl⟩ : syracuseStep 1072277 = 50263) (by norm_num)
theorem B875717 : Blo 207808 875717 := bbase (se 4 (by rfl) ⟨82098, by rfl⟩ : syracuseStep 875717 = 164197) (by norm_num)
theorem B351445 : Blo 207808 351445 := bbase (se 7 (by rfl) ⟨4118, by rfl⟩ : syracuseStep 351445 = 8237) (by norm_num)
theorem B1334549 : Blo 207808 1334549 := bbase (se 6 (by rfl) ⟨31278, by rfl⟩ : syracuseStep 1334549 = 62557) (by norm_num)
theorem B351533 : Blo 207808 351533 := bbase (se 3 (by rfl) ⟨65912, by rfl⟩ : syracuseStep 351533 = 131825) (by norm_num)
theorem B711989 : Blo 207808 711989 := bbase (se 5 (by rfl) ⟨33374, by rfl⟩ : syracuseStep 711989 = 66749) (by norm_num)
theorem B253265 : Blo 207808 253265 := bbase (se 2 (by rfl) ⟨94974, by rfl⟩ : syracuseStep 253265 = 189949) (by norm_num)
theorem B15621461 : Blo 207808 15621461 := bbase (se 11 (by rfl) ⟨11441, by rfl⟩ : syracuseStep 15621461 = 22883) (by norm_num)
theorem B351661 : Blo 207808 351661 := bbase (se 3 (by rfl) ⟨65936, by rfl⟩ : syracuseStep 351661 = 131873) (by norm_num)
theorem B253381 : Blo 207808 253381 := bbase (se 4 (by rfl) ⟨23754, by rfl⟩ : syracuseStep 253381 = 47509) (by norm_num)
theorem B351749 : Blo 207808 351749 := bbase (se 4 (by rfl) ⟨32976, by rfl⟩ : syracuseStep 351749 = 65953) (by norm_num)
theorem B253453 : Blo 207808 253453 := bbase (se 3 (by rfl) ⟨47522, by rfl⟩ : syracuseStep 253453 = 95045) (by norm_num)
theorem B253477 : Blo 207808 253477 := bbase (se 4 (by rfl) ⟨23763, by rfl⟩ : syracuseStep 253477 = 47527) (by norm_num)
theorem B450173 : Blo 207808 450173 := bbase (se 3 (by rfl) ⟨84407, by rfl⟩ : syracuseStep 450173 = 168815) (by norm_num)
theorem B351877 : Blo 207808 351877 := bbase (se 4 (by rfl) ⟨32988, by rfl⟩ : syracuseStep 351877 = 65977) (by norm_num)
theorem B253621 : Blo 207808 253621 := bbase (se 5 (by rfl) ⟨11888, by rfl⟩ : syracuseStep 253621 = 23777) (by norm_num)
theorem B351965 : Blo 207808 351965 := bbase (se 3 (by rfl) ⟨65993, by rfl⟩ : syracuseStep 351965 = 131987) (by norm_num)
theorem B712421 : Blo 207808 712421 := bbase (se 4 (by rfl) ⟨66789, by rfl⟩ : syracuseStep 712421 = 133579) (by norm_num)
theorem B450317 : Blo 207808 450317 := bbase (se 3 (by rfl) ⟨84434, by rfl⟩ : syracuseStep 450317 = 168869) (by norm_num)
theorem B352093 : Blo 207808 352093 := bbase (se 3 (by rfl) ⟨66017, by rfl⟩ : syracuseStep 352093 = 132035) (by norm_num)
theorem B352181 : Blo 207808 352181 := bbase (se 5 (by rfl) ⟨16508, by rfl⟩ : syracuseStep 352181 = 33017) (by norm_num)
theorem B2383829 : Blo 207808 2383829 := bbase (se 7 (by rfl) ⟨27935, by rfl⟩ : syracuseStep 2383829 = 55871) (by norm_num)
theorem B319469 : Blo 207808 319469 := bbase (se 3 (by rfl) ⟨59900, by rfl⟩ : syracuseStep 319469 = 119801) (by norm_num)
theorem B352309 : Blo 207808 352309 := bbase (se 5 (by rfl) ⟨16514, by rfl⟩ : syracuseStep 352309 = 33029) (by norm_num)
theorem B450677 : Blo 207808 450677 := bbase (se 5 (by rfl) ⟨21125, by rfl⟩ : syracuseStep 450677 = 42251) (by norm_num)
theorem B352397 : Blo 207808 352397 := bbase (se 3 (by rfl) ⟨66074, by rfl⟩ : syracuseStep 352397 = 132149) (by norm_num)
theorem B712853 : Blo 207808 712853 := bbase (se 6 (by rfl) ⟨16707, by rfl⟩ : syracuseStep 712853 = 33415) (by norm_num)
theorem B1204469 : Blo 207808 1204469 := bbase (se 5 (by rfl) ⟨56459, by rfl⟩ : syracuseStep 1204469 = 112919) (by norm_num)
theorem B352525 : Blo 207808 352525 := bbase (se 3 (by rfl) ⟨66098, by rfl⟩ : syracuseStep 352525 = 132197) (by norm_num)
theorem B352613 : Blo 207808 352613 := bbase (se 4 (by rfl) ⟨33057, by rfl⟩ : syracuseStep 352613 = 66115) (by norm_num)
theorem B352741 : Blo 207808 352741 := bbase (se 4 (by rfl) ⟨33069, by rfl⟩ : syracuseStep 352741 = 66139) (by norm_num)
theorem B254497 : Blo 207808 254497 := bbase (se 2 (by rfl) ⟨95436, by rfl⟩ : syracuseStep 254497 = 190873) (by norm_num)
theorem B352829 : Blo 207808 352829 := bbase (se 3 (by rfl) ⟨66155, by rfl⟩ : syracuseStep 352829 = 132311) (by norm_num)
theorem B713285 : Blo 207808 713285 := bbase (se 4 (by rfl) ⟨66870, by rfl⟩ : syracuseStep 713285 = 133741) (by norm_num)
theorem B352957 : Blo 207808 352957 := bbase (se 3 (by rfl) ⟨66179, by rfl⟩ : syracuseStep 352957 = 132359) (by norm_num)
theorem B353045 : Blo 207808 353045 := bbase (se 6 (by rfl) ⟨8274, by rfl⟩ : syracuseStep 353045 = 16549) (by norm_num)
theorem B221977 : Blo 207808 221977 := bbase (se 2 (by rfl) ⟨83241, by rfl⟩ : syracuseStep 221977 = 166483) (by norm_num)
theorem B1696565 : Blo 207808 1696565 := bbase (se 5 (by rfl) ⟨79526, by rfl⟩ : syracuseStep 1696565 = 159053) (by norm_num)
theorem B222049 : Blo 207808 222049 := bbase (se 2 (by rfl) ⟨83268, by rfl⟩ : syracuseStep 222049 = 166537) (by norm_num)
theorem B353173 : Blo 207808 353173 := bbase (se 6 (by rfl) ⟨8277, by rfl⟩ : syracuseStep 353173 = 16555) (by norm_num)
theorem B353261 : Blo 207808 353261 := bbase (se 3 (by rfl) ⟨66236, by rfl⟩ : syracuseStep 353261 = 132473) (by norm_num)
theorem B451565 : Blo 207808 451565 := bbase (se 3 (by rfl) ⟨84668, by rfl⟩ : syracuseStep 451565 = 169337) (by norm_num)
theorem B1598453 : Blo 207808 1598453 := bbase (se 5 (by rfl) ⟨74927, by rfl⟩ : syracuseStep 1598453 = 149855) (by norm_num)
theorem B713717 : Blo 207808 713717 := bbase (se 5 (by rfl) ⟨33455, by rfl⟩ : syracuseStep 713717 = 66911) (by norm_num)
theorem B353389 : Blo 207808 353389 := bbase (se 3 (by rfl) ⟨66260, by rfl⟩ : syracuseStep 353389 = 132521) (by norm_num)
theorem B255145 : Blo 207808 255145 := bbase (se 2 (by rfl) ⟨95679, by rfl⟩ : syracuseStep 255145 = 191359) (by norm_num)
theorem B353477 : Blo 207808 353477 := bbase (se 4 (by rfl) ⟨33138, by rfl⟩ : syracuseStep 353477 = 66277) (by norm_num)
theorem B222421 : Blo 207808 222421 := bbase (se 7 (by rfl) ⟨2606, by rfl⟩ : syracuseStep 222421 = 5213) (by norm_num)
theorem B255197 : Blo 207808 255197 := bbase (se 3 (by rfl) ⟨47849, by rfl⟩ : syracuseStep 255197 = 95699) (by norm_num)
theorem B451813 : Blo 207808 451813 := bbase (se 4 (by rfl) ⟨42357, by rfl⟩ : syracuseStep 451813 = 84715) (by norm_num)
theorem B353605 : Blo 207808 353605 := bbase (se 4 (by rfl) ⟨33150, by rfl⟩ : syracuseStep 353605 = 66301) (by norm_num)
theorem B353693 : Blo 207808 353693 := bbase (se 3 (by rfl) ⟨66317, by rfl⟩ : syracuseStep 353693 = 132635) (by norm_num)
theorem B714149 : Blo 207808 714149 := bbase (se 4 (by rfl) ⟨66951, by rfl⟩ : syracuseStep 714149 = 133903) (by norm_num)
theorem B353821 : Blo 207808 353821 := bbase (se 3 (by rfl) ⟨66341, by rfl⟩ : syracuseStep 353821 = 132683) (by norm_num)
theorem B222797 : Blo 207808 222797 := bbase (se 3 (by rfl) ⟨41774, by rfl⟩ : syracuseStep 222797 = 83549) (by norm_num)
theorem B3434069 : Blo 207808 3434069 := bbase (se 8 (by rfl) ⟨20121, by rfl⟩ : syracuseStep 3434069 = 40243) (by norm_num)
theorem B353909 : Blo 207808 353909 := bbase (se 5 (by rfl) ⟨16589, by rfl⟩ : syracuseStep 353909 = 33179) (by norm_num)
theorem B222869 : Blo 207808 222869 := bbase (se 6 (by rfl) ⟨5223, by rfl⟩ : syracuseStep 222869 = 10447) (by norm_num)
theorem B321221 : Blo 207808 321221 := bbase (se 4 (by rfl) ⟨30114, by rfl⟩ : syracuseStep 321221 = 60229) (by norm_num)
theorem B452317 : Blo 207808 452317 := bbase (se 3 (by rfl) ⟨84809, by rfl⟩ : syracuseStep 452317 = 169619) (by norm_num)
theorem B354037 : Blo 207808 354037 := bbase (se 5 (by rfl) ⟨16595, by rfl⟩ : syracuseStep 354037 = 33191) (by norm_num)
theorem B354125 : Blo 207808 354125 := bbase (se 3 (by rfl) ⟨66398, by rfl⟩ : syracuseStep 354125 = 132797) (by norm_num)
theorem B223057 : Blo 207808 223057 := bbase (se 2 (by rfl) ⟨83646, by rfl⟩ : syracuseStep 223057 = 167293) (by norm_num)
theorem B714581 : Blo 207808 714581 := bbase (se 9 (by rfl) ⟨2093, by rfl⟩ : syracuseStep 714581 = 4187) (by norm_num)
theorem B354253 : Blo 207808 354253 := bbase (se 3 (by rfl) ⟨66422, by rfl⟩ : syracuseStep 354253 = 132845) (by norm_num)
theorem B223241 : Blo 207808 223241 := bbase (se 2 (by rfl) ⟨83715, by rfl⟩ : syracuseStep 223241 = 167431) (by norm_num)
theorem B354341 : Blo 207808 354341 := bbase (se 4 (by rfl) ⟨33219, by rfl⟩ : syracuseStep 354341 = 66439) (by norm_num)
theorem B354469 : Blo 207808 354469 := bbase (se 4 (by rfl) ⟨33231, by rfl⟩ : syracuseStep 354469 = 66463) (by norm_num)
theorem B354557 : Blo 207808 354557 := bbase (se 3 (by rfl) ⟨66479, by rfl⟩ : syracuseStep 354557 = 132959) (by norm_num)
theorem B321877 : Blo 207808 321877 := bbase (se 10 (by rfl) ⟨471, by rfl⟩ : syracuseStep 321877 = 943) (by norm_num)
theorem B354685 : Blo 207808 354685 := bbase (se 3 (by rfl) ⟨66503, by rfl⟩ : syracuseStep 354685 = 133007) (by norm_num)
theorem B354773 : Blo 207808 354773 := bbase (se 7 (by rfl) ⟨4157, by rfl⟩ : syracuseStep 354773 = 8315) (by norm_num)
theorem B256537 : Blo 207808 256537 := bbase (se 2 (by rfl) ⟨96201, by rfl⟩ : syracuseStep 256537 = 192403) (by norm_num)
theorem B354901 : Blo 207808 354901 := bbase (se 8 (by rfl) ⟨2079, by rfl⟩ : syracuseStep 354901 = 4159) (by norm_num)
theorem B354989 : Blo 207808 354989 := bbase (se 3 (by rfl) ⟨66560, by rfl⟩ : syracuseStep 354989 = 133121) (by norm_num)
theorem B223993 : Blo 207808 223993 := bbase (se 2 (by rfl) ⟨83997, by rfl⟩ : syracuseStep 223993 = 167995) (by norm_num)
theorem B355117 : Blo 207808 355117 := bbase (se 3 (by rfl) ⟨66584, by rfl⟩ : syracuseStep 355117 = 133169) (by norm_num)
theorem B1010485 : Blo 207808 1010485 := bbase (se 5 (by rfl) ⟨47366, by rfl⟩ : syracuseStep 1010485 = 94733) (by norm_num)
theorem B224065 : Blo 207808 224065 := bbase (se 2 (by rfl) ⟨84024, by rfl⟩ : syracuseStep 224065 = 168049) (by norm_num)
theorem B4025173 : Blo 207808 4025173 := bbase (se 9 (by rfl) ⟨11792, by rfl⟩ : syracuseStep 4025173 = 23585) (by norm_num)
theorem B355205 : Blo 207808 355205 := bbase (se 4 (by rfl) ⟨33300, by rfl⟩ : syracuseStep 355205 = 66601) (by norm_num)
theorem B224245 : Blo 207808 224245 := bbase (se 5 (by rfl) ⟨10511, by rfl⟩ : syracuseStep 224245 = 21023) (by norm_num)
theorem B355333 : Blo 207808 355333 := bbase (se 4 (by rfl) ⟨33312, by rfl⟩ : syracuseStep 355333 = 66625) (by norm_num)
theorem B355421 : Blo 207808 355421 := bbase (se 3 (by rfl) ⟨66641, by rfl⟩ : syracuseStep 355421 = 133283) (by norm_num)
theorem B257185 : Blo 207808 257185 := bbase (se 2 (by rfl) ⟨96444, by rfl⟩ : syracuseStep 257185 = 192889) (by norm_num)
theorem B257189 : Blo 207808 257189 := bbase (se 4 (by rfl) ⟨24111, by rfl⟩ : syracuseStep 257189 = 48223) (by norm_num)
theorem B355549 : Blo 207808 355549 := bbase (se 3 (by rfl) ⟨66665, by rfl⟩ : syracuseStep 355549 = 133331) (by norm_num)
theorem B355637 : Blo 207808 355637 := bbase (se 5 (by rfl) ⟨16670, by rfl⟩ : syracuseStep 355637 = 33341) (by norm_num)
theorem B224689 : Blo 207808 224689 := bbase (se 2 (by rfl) ⟨84258, by rfl⟩ : syracuseStep 224689 = 168517) (by norm_num)
theorem B355765 : Blo 207808 355765 := bbase (se 5 (by rfl) ⟨16676, by rfl⟩ : syracuseStep 355765 = 33353) (by norm_num)
theorem B355853 : Blo 207808 355853 := bbase (se 3 (by rfl) ⟨66722, by rfl⟩ : syracuseStep 355853 = 133445) (by norm_num)
theorem B224813 : Blo 207808 224813 := bbase (se 3 (by rfl) ⟨42152, by rfl⟩ : syracuseStep 224813 = 84305) (by norm_num)
theorem B355981 : Blo 207808 355981 := bbase (se 3 (by rfl) ⟨66746, by rfl⟩ : syracuseStep 355981 = 133493) (by norm_num)
theorem B356069 : Blo 207808 356069 := bbase (se 4 (by rfl) ⟨33381, by rfl⟩ : syracuseStep 356069 = 66763) (by norm_num)
theorem B421645 : Blo 207808 421645 := bbase (se 3 (by rfl) ⟨79058, by rfl⟩ : syracuseStep 421645 = 158117) (by norm_num)
theorem B225065 : Blo 207808 225065 := bbase (se 2 (by rfl) ⟨84399, by rfl⟩ : syracuseStep 225065 = 168799) (by norm_num)
theorem B683861 : Blo 207808 683861 := bbase (se 9 (by rfl) ⟨2003, by rfl⟩ : syracuseStep 683861 = 4007) (by norm_num)
theorem B356197 : Blo 207808 356197 := bbase (se 4 (by rfl) ⟨33393, by rfl⟩ : syracuseStep 356197 = 66787) (by norm_num)
theorem B421741 : Blo 207808 421741 := bbase (se 3 (by rfl) ⟨79076, by rfl⟩ : syracuseStep 421741 = 158153) (by norm_num)
theorem B1896373 : Blo 207808 1896373 := bbase (se 5 (by rfl) ⟨88892, by rfl⟩ : syracuseStep 1896373 = 177785) (by norm_num)
theorem B356285 : Blo 207808 356285 := bbase (se 3 (by rfl) ⟨66803, by rfl⟩ : syracuseStep 356285 = 133607) (by norm_num)
theorem B1929205 : Blo 207808 1929205 := bbase (se 5 (by rfl) ⟨90431, by rfl⟩ : syracuseStep 1929205 = 180863) (by norm_num)
theorem B356413 : Blo 207808 356413 := bbase (se 3 (by rfl) ⟨66827, by rfl⟩ : syracuseStep 356413 = 133655) (by norm_num)
theorem B323693 : Blo 207808 323693 := bbase (se 3 (by rfl) ⟨60692, by rfl⟩ : syracuseStep 323693 = 121385) (by norm_num)
theorem B356501 : Blo 207808 356501 := bbase (se 6 (by rfl) ⟨8355, by rfl⟩ : syracuseStep 356501 = 16711) (by norm_num)
theorem B749749 : Blo 207808 749749 := bbase (se 5 (by rfl) ⟨35144, by rfl⟩ : syracuseStep 749749 = 70289) (by norm_num)
theorem B225509 : Blo 207808 225509 := bbase (se 4 (by rfl) ⟨21141, by rfl⟩ : syracuseStep 225509 = 42283) (by norm_num)
theorem B356629 : Blo 207808 356629 := bbase (se 6 (by rfl) ⟨8358, by rfl⟩ : syracuseStep 356629 = 16717) (by norm_num)
theorem B356717 : Blo 207808 356717 := bbase (se 3 (by rfl) ⟨66884, by rfl⟩ : syracuseStep 356717 = 133769) (by norm_num)
theorem B225757 : Blo 207808 225757 := bbase (se 3 (by rfl) ⟨42329, by rfl⟩ : syracuseStep 225757 = 84659) (by norm_num)
theorem B356845 : Blo 207808 356845 := bbase (se 3 (by rfl) ⟨66908, by rfl⟩ : syracuseStep 356845 = 133817) (by norm_num)
theorem B356933 : Blo 207808 356933 := bbase (se 4 (by rfl) ⟨33462, by rfl⟩ : syracuseStep 356933 = 66925) (by norm_num)
theorem B357061 : Blo 207808 357061 := bbase (se 4 (by rfl) ⟨33474, by rfl⟩ : syracuseStep 357061 = 66949) (by norm_num)
theorem B357149 : Blo 207808 357149 := bbase (se 3 (by rfl) ⟨66965, by rfl⟩ : syracuseStep 357149 = 133931) (by norm_num)
theorem B357277 : Blo 207808 357277 := bbase (se 3 (by rfl) ⟨66989, by rfl⟩ : syracuseStep 357277 = 133979) (by norm_num)
theorem B357365 : Blo 207808 357365 := bbase (se 5 (by rfl) ⟨16751, by rfl⟩ : syracuseStep 357365 = 33503) (by norm_num)
theorem B848933 : Blo 207808 848933 := bbase (se 4 (by rfl) ⟨79587, by rfl⟩ : syracuseStep 848933 = 159175) (by norm_num)
theorem B357733 : Blo 207808 357733 := bbase (se 4 (by rfl) ⟨33537, by rfl⟩ : syracuseStep 357733 = 67075) (by norm_num)
theorem B652789 : Blo 207808 652789 := bbase (se 5 (by rfl) ⟨30599, by rfl⟩ : syracuseStep 652789 = 61199) (by norm_num)
theorem B1799765 : Blo 207808 1799765 := bbase (se 8 (by rfl) ⟨10545, by rfl⟩ : syracuseStep 1799765 = 21091) (by norm_num)
theorem B358357 : Blo 207808 358357 := bbase (se 7 (by rfl) ⟨4199, by rfl⟩ : syracuseStep 358357 = 8399) (by norm_num)
theorem B751781 : Blo 207808 751781 := bbase (se 4 (by rfl) ⟨70479, by rfl⟩ : syracuseStep 751781 = 140959) (by norm_num)
theorem B391493 : Blo 207808 391493 := bbase (se 4 (by rfl) ⟨36702, by rfl⟩ : syracuseStep 391493 = 73405) (by norm_num)
theorem B2259413 : Blo 207808 2259413 := bbase (se 7 (by rfl) ⟨26477, by rfl⟩ : syracuseStep 2259413 = 52955) (by norm_num)
theorem B424597 : Blo 207808 424597 := bbase (se 6 (by rfl) ⟨9951, by rfl⟩ : syracuseStep 424597 = 19903) (by norm_num)
theorem B1014677 : Blo 207808 1014677 := bbase (se 6 (by rfl) ⟨23781, by rfl⟩ : syracuseStep 1014677 = 47563) (by norm_num)
theorem B687109 : Blo 207808 687109 := bbase (se 4 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 687109 = 128833) (by norm_num)
theorem B752645 : Blo 207808 752645 := bbase (se 4 (by rfl) ⟨70560, by rfl⟩ : syracuseStep 752645 = 141121) (by norm_num)
theorem B425197 : Blo 207808 425197 := bbase (se 3 (by rfl) ⟨79724, by rfl⟩ : syracuseStep 425197 = 159449) (by norm_num)
theorem B458005 : Blo 207808 458005 := bbase (se 6 (by rfl) ⟨10734, by rfl⟩ : syracuseStep 458005 = 21469) (by norm_num)
theorem B425261 : Blo 207808 425261 := bbase (se 3 (by rfl) ⟨79736, by rfl⟩ : syracuseStep 425261 = 159473) (by norm_num)
theorem B425309 : Blo 207808 425309 := bbase (se 3 (by rfl) ⟨79745, by rfl⟩ : syracuseStep 425309 = 159491) (by norm_num)
theorem B359869 : Blo 207808 359869 := bbase (se 3 (by rfl) ⟨67475, by rfl⟩ : syracuseStep 359869 = 134951) (by norm_num)
theorem B425893 : Blo 207808 425893 := bbase (se 4 (by rfl) ⟨39927, by rfl⟩ : syracuseStep 425893 = 79855) (by norm_num)
theorem B721133 : Blo 207808 721133 := bstep (se 3 (by rfl) ⟨135212, by rfl⟩ : syracuseStep 721133 = 270425) B270425
theorem B1016675 : Blo 207808 1016675 := bstep (se 1 (by rfl) ⟨762506, by rfl⟩ : syracuseStep 1016675 = 1525013) B1525013
theorem B263027 : Blo 207808 263027 := bstep (se 1 (by rfl) ⟨197270, by rfl⟩ : syracuseStep 263027 = 394541) B394541
theorem B295969 : Blo 207808 295969 := bstep (se 2 (by rfl) ⟨110988, by rfl⟩ : syracuseStep 295969 = 221977) B221977
theorem B1016945 : Blo 207808 1016945 := bstep (se 2 (by rfl) ⟨381354, by rfl⟩ : syracuseStep 1016945 = 762709) B762709
theorem B296065 : Blo 207808 296065 := bstep (se 2 (by rfl) ⟨111024, by rfl⟩ : syracuseStep 296065 = 222049) B222049
theorem B1017137 : Blo 207808 1017137 := bstep (se 2 (by rfl) ⟨381426, by rfl⟩ : syracuseStep 1017137 = 762853) B762853
theorem B361921 : Blo 207808 361921 := bstep (se 2 (by rfl) ⟨135720, by rfl⟩ : syracuseStep 361921 = 271441) B271441
theorem B394723 : Blo 207808 394723 := bstep (se 1 (by rfl) ⟨296042, by rfl⟩ : syracuseStep 394723 = 592085) B592085
theorem B951821 : Blo 207808 951821 := bstep (se 3 (by rfl) ⟨178466, by rfl⟩ : syracuseStep 951821 = 356933) B356933
theorem B394769 : Blo 207808 394769 := bstep (se 2 (by rfl) ⟨148038, by rfl⟩ : syracuseStep 394769 = 296077) B296077
theorem B263731 : Blo 207808 263731 := bstep (se 1 (by rfl) ⟨197798, by rfl⟩ : syracuseStep 263731 = 395597) B395597
theorem B296561 : Blo 207808 296561 := bstep (se 2 (by rfl) ⟨111210, by rfl⟩ : syracuseStep 296561 = 222421) B222421
theorem B263827 : Blo 207808 263827 := bstep (se 1 (by rfl) ⟨197870, by rfl⟩ : syracuseStep 263827 = 395741) B395741
theorem B1345187 : Blo 207808 1345187 := bstep (se 1 (by rfl) ⟨1008890, by rfl⟩ : syracuseStep 1345187 = 2017781) B2017781
theorem B1017521 : Blo 207808 1017521 := bstep (se 2 (by rfl) ⟨381570, by rfl⟩ : syracuseStep 1017521 = 763141) B763141
theorem B722627 : Blo 207808 722627 := bstep (se 1 (by rfl) ⟨541970, by rfl⟩ : syracuseStep 722627 = 1083941) B1083941
theorem B526115 : Blo 207808 526115 := bstep (se 1 (by rfl) ⟨394586, by rfl⟩ : syracuseStep 526115 = 789173) B789173
theorem B395057 : Blo 207808 395057 := bstep (se 2 (by rfl) ⟨148146, by rfl⟩ : syracuseStep 395057 = 296293) B296293
theorem B3573557 : Blo 207808 3573557 := bstep (se 5 (by rfl) ⟨167510, by rfl⟩ : syracuseStep 3573557 = 335021) B335021
theorem B5736419 : Blo 207808 5736419 := bstep (se 1 (by rfl) ⟨4302314, by rfl⟩ : syracuseStep 5736419 = 8604629) B8604629
theorem B591857 : Blo 207808 591857 := bstep (se 2 (by rfl) ⟨221946, by rfl⟩ : syracuseStep 591857 = 443893) B443893
theorem B428131 : Blo 207808 428131 := bstep (se 1 (by rfl) ⟨321098, by rfl⟩ : syracuseStep 428131 = 642197) B642197
theorem B264323 : Blo 207808 264323 := bstep (se 1 (by rfl) ⟨198242, by rfl⟩ : syracuseStep 264323 = 396485) B396485
theorem B4524173 : Blo 207808 4524173 := bstep (se 3 (by rfl) ⟨848282, by rfl⟩ : syracuseStep 4524173 = 1696565) B1696565
theorem B2591117 : Blo 207808 2591117 := bstep (se 3 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 2591117 = 971669) B971669
theorem B297427 : Blo 207808 297427 := bstep (se 1 (by rfl) ⟨223070, by rfl⟩ : syracuseStep 297427 = 446141) B446141
theorem B395779 : Blo 207808 395779 := bstep (se 1 (by rfl) ⟨296834, by rfl⟩ : syracuseStep 395779 = 593669) B593669
theorem B297523 : Blo 207808 297523 := bstep (se 1 (by rfl) ⟨223142, by rfl⟩ : syracuseStep 297523 = 446285) B446285
theorem B527057 : Blo 207808 527057 := bstep (se 2 (by rfl) ⟨197646, by rfl⟩ : syracuseStep 527057 = 395293) B395293
theorem B527107 : Blo 207808 527107 := bstep (se 1 (by rfl) ⟨395330, by rfl⟩ : syracuseStep 527107 = 790661) B790661
theorem B265027 : Blo 207808 265027 := bstep (se 1 (by rfl) ⟨198770, by rfl⟩ : syracuseStep 265027 = 397541) B397541
theorem B527249 : Blo 207808 527249 := bstep (se 2 (by rfl) ⟨197718, by rfl⟩ : syracuseStep 527249 = 395437) B395437
theorem B265123 : Blo 207808 265123 := bstep (se 1 (by rfl) ⟨198842, by rfl⟩ : syracuseStep 265123 = 397685) B397685
theorem B396227 : Blo 207808 396227 := bstep (se 1 (by rfl) ⟨297170, by rfl⟩ : syracuseStep 396227 = 594341) B594341
theorem B298019 : Blo 207808 298019 := bstep (se 1 (by rfl) ⟨223514, by rfl⟩ : syracuseStep 298019 = 447029) B447029
theorem B396515 : Blo 207808 396515 := bstep (se 1 (by rfl) ⟨297386, by rfl⟩ : syracuseStep 396515 = 594773) B594773
theorem B757027 : Blo 207808 757027 := bstep (se 1 (by rfl) ⟨567770, by rfl⟩ : syracuseStep 757027 = 1135541) B1135541
theorem B265619 : Blo 207808 265619 := bstep (se 1 (by rfl) ⟨199214, by rfl⟩ : syracuseStep 265619 = 398429) B398429
theorem B593315 : Blo 207808 593315 := bstep (se 1 (by rfl) ⟨444986, by rfl⟩ : syracuseStep 593315 = 889973) B889973
theorem B16289221 : Blo 207808 16289221 := bstep (se 4 (by rfl) ⟨1527114, by rfl⟩ : syracuseStep 16289221 = 3054229) B3054229
theorem B298657 : Blo 207808 298657 := bstep (se 2 (by rfl) ⟨111996, by rfl⟩ : syracuseStep 298657 = 223993) B223993
theorem B1347313 : Blo 207808 1347313 := bstep (se 2 (by rfl) ⟨505242, by rfl⟩ : syracuseStep 1347313 = 1010485) B1010485
theorem B528241 : Blo 207808 528241 := bstep (se 2 (by rfl) ⟨198090, by rfl⟩ : syracuseStep 528241 = 396181) B396181
theorem B298993 : Blo 207808 298993 := bstep (se 2 (by rfl) ⟨112122, by rfl⟩ : syracuseStep 298993 = 224245) B224245
theorem B1282061 : Blo 207808 1282061 := bstep (se 3 (by rfl) ⟨240386, by rfl⟩ : syracuseStep 1282061 = 480773) B480773
theorem B266323 : Blo 207808 266323 := bstep (se 1 (by rfl) ⟨199742, by rfl⟩ : syracuseStep 266323 = 399485) B399485
theorem B528515 : Blo 207808 528515 := bstep (se 1 (by rfl) ⟨396386, by rfl⟩ : syracuseStep 528515 = 792773) B792773
theorem B397457 : Blo 207808 397457 := bstep (se 2 (by rfl) ⟨149046, by rfl⟩ : syracuseStep 397457 = 298093) B298093
theorem B266419 : Blo 207808 266419 := bstep (se 1 (by rfl) ⟨199814, by rfl⟩ : syracuseStep 266419 = 399629) B399629
theorem B594125 : Blo 207808 594125 := bstep (se 3 (by rfl) ⟨111398, by rfl⟩ : syracuseStep 594125 = 222797) B222797
theorem B528707 : Blo 207808 528707 := bstep (se 1 (by rfl) ⟨396530, by rfl⟩ : syracuseStep 528707 = 793061) B793061
theorem B594317 : Blo 207808 594317 := bstep (se 3 (by rfl) ⟨111434, by rfl⟩ : syracuseStep 594317 = 222869) B222869
theorem B233923 : Blo 207808 233923 := bstep (se 1 (by rfl) ⟨175442, by rfl⟩ : syracuseStep 233923 = 350885) B350885
theorem B627139 : Blo 207808 627139 := bstep (se 1 (by rfl) ⟨470354, by rfl⟩ : syracuseStep 627139 = 940709) B940709
theorem B299585 : Blo 207808 299585 := bstep (se 2 (by rfl) ⟨112344, by rfl⟩ : syracuseStep 299585 = 224689) B224689
theorem B791117 : Blo 207808 791117 := bstep (se 3 (by rfl) ⟨148334, by rfl⟩ : syracuseStep 791117 = 296669) B296669
theorem B234067 : Blo 207808 234067 := bstep (se 1 (by rfl) ⟨175550, by rfl⟩ : syracuseStep 234067 = 351101) B351101
theorem B266915 : Blo 207808 266915 := bstep (se 1 (by rfl) ⟨200186, by rfl⟩ : syracuseStep 266915 = 400373) B400373
theorem B234211 : Blo 207808 234211 := bstep (se 1 (by rfl) ⟨175658, by rfl⟩ : syracuseStep 234211 = 351317) B351317
theorem B889699 : Blo 207808 889699 := bstep (se 1 (by rfl) ⟨667274, by rfl⟩ : syracuseStep 889699 = 1334549) B1334549
theorem B234355 : Blo 207808 234355 := bstep (se 1 (by rfl) ⟨175766, by rfl⟩ : syracuseStep 234355 = 351533) B351533
theorem B234499 : Blo 207808 234499 := bstep (se 1 (by rfl) ⟨175874, by rfl⟩ : syracuseStep 234499 = 351749) B351749
theorem B562193 : Blo 207808 562193 := bstep (se 2 (by rfl) ⟨210822, by rfl⟩ : syracuseStep 562193 = 421645) B421645
theorem B398353 : Blo 207808 398353 := bstep (se 2 (by rfl) ⟨149382, by rfl⟩ : syracuseStep 398353 = 298765) B298765
theorem B300115 : Blo 207808 300115 := bstep (se 1 (by rfl) ⟨225086, by rfl⟩ : syracuseStep 300115 = 450173) B450173
theorem B1053809 : Blo 207808 1053809 := bstep (se 2 (by rfl) ⟨395178, by rfl⟩ : syracuseStep 1053809 = 790357) B790357
theorem B562321 : Blo 207808 562321 := bstep (se 2 (by rfl) ⟨210870, by rfl⟩ : syracuseStep 562321 = 421741) B421741
theorem B234643 : Blo 207808 234643 := bstep (se 1 (by rfl) ⟨175982, by rfl⟩ : syracuseStep 234643 = 351965) B351965
theorem B398513 : Blo 207808 398513 := bstep (se 2 (by rfl) ⟨149442, by rfl⟩ : syracuseStep 398513 = 298885) B298885
theorem B2528497 : Blo 207808 2528497 := bstep (se 2 (by rfl) ⟨948186, by rfl⟩ : syracuseStep 2528497 = 1896373) B1896373
theorem B529649 : Blo 207808 529649 := bstep (se 2 (by rfl) ⟨198618, by rfl⟩ : syracuseStep 529649 = 397237) B397237
theorem B234787 : Blo 207808 234787 := bstep (se 1 (by rfl) ⟨176090, by rfl⟩ : syracuseStep 234787 = 352181) B352181
theorem B529699 : Blo 207808 529699 := bstep (se 1 (by rfl) ⟨397274, by rfl⟩ : syracuseStep 529699 = 794549) B794549
theorem B267619 : Blo 207808 267619 := bstep (se 1 (by rfl) ⟨200714, by rfl⟩ : syracuseStep 267619 = 401429) B401429
theorem B595309 : Blo 207808 595309 := bstep (se 3 (by rfl) ⟨111620, by rfl⟩ : syracuseStep 595309 = 223241) B223241
theorem B300451 : Blo 207808 300451 := bstep (se 1 (by rfl) ⟨225338, by rfl⟩ : syracuseStep 300451 = 450677) B450677
theorem B529841 : Blo 207808 529841 := bstep (se 2 (by rfl) ⟨198690, by rfl⟩ : syracuseStep 529841 = 397381) B397381
theorem B234931 : Blo 207808 234931 := bstep (se 1 (by rfl) ⟨176198, by rfl⟩ : syracuseStep 234931 = 352397) B352397
theorem B267715 : Blo 207808 267715 := bstep (se 1 (by rfl) ⟨200786, by rfl⟩ : syracuseStep 267715 = 401573) B401573
theorem B235075 : Blo 207808 235075 := bstep (se 1 (by rfl) ⟨176306, by rfl⟩ : syracuseStep 235075 = 352613) B352613
theorem B398915 : Blo 207808 398915 := bstep (se 1 (by rfl) ⟨299186, by rfl⟩ : syracuseStep 398915 = 598373) B598373
theorem B235219 : Blo 207808 235219 := bstep (se 1 (by rfl) ⟨176414, by rfl⟩ : syracuseStep 235219 = 352829) B352829
theorem B2004749 : Blo 207808 2004749 := bstep (se 3 (by rfl) ⟨375890, by rfl⟩ : syracuseStep 2004749 = 751781) B751781
theorem B5117717 : Blo 207808 5117717 := bstep (se 6 (by rfl) ⟨119946, by rfl⟩ : syracuseStep 5117717 = 239893) B239893
theorem B235363 : Blo 207808 235363 := bstep (se 1 (by rfl) ⟨176522, by rfl⟩ : syracuseStep 235363 = 353045) B353045
theorem B333715 : Blo 207808 333715 := bstep (se 1 (by rfl) ⟨250286, by rfl⟩ : syracuseStep 333715 = 500573) B500573
theorem B301009 : Blo 207808 301009 := bstep (se 2 (by rfl) ⟨112878, by rfl⟩ : syracuseStep 301009 = 225757) B225757
theorem B235507 : Blo 207808 235507 := bstep (se 1 (by rfl) ⟨176630, by rfl⟩ : syracuseStep 235507 = 353261) B353261
theorem B301043 : Blo 207808 301043 := bstep (se 1 (by rfl) ⟨225782, by rfl⟩ : syracuseStep 301043 = 451565) B451565
theorem B890929 : Blo 207808 890929 := bstep (se 2 (by rfl) ⟨334098, by rfl⟩ : syracuseStep 890929 = 668197) B668197
theorem B235651 : Blo 207808 235651 := bstep (se 1 (by rfl) ⟨176738, by rfl⟩ : syracuseStep 235651 = 353477) B353477
theorem B333971 : Blo 207808 333971 := bstep (se 1 (by rfl) ⟨250478, by rfl⟩ : syracuseStep 333971 = 500957) B500957
theorem B235795 : Blo 207808 235795 := bstep (se 1 (by rfl) ⟨176846, by rfl⟩ : syracuseStep 235795 = 353693) B353693
theorem B334163 : Blo 207808 334163 := bstep (se 1 (by rfl) ⟨250622, by rfl⟩ : syracuseStep 334163 = 501245) B501245
theorem B530833 : Blo 207808 530833 := bstep (se 2 (by rfl) ⟨199062, by rfl⟩ : syracuseStep 530833 = 398125) B398125
theorem B235939 : Blo 207808 235939 := bstep (se 1 (by rfl) ⟨176954, by rfl⟩ : syracuseStep 235939 = 353909) B353909
theorem B399811 : Blo 207808 399811 := bstep (se 1 (by rfl) ⟨299858, by rfl⟩ : syracuseStep 399811 = 599717) B599717
theorem B1055267 : Blo 207808 1055267 := bstep (se 1 (by rfl) ⟨791450, by rfl⟩ : syracuseStep 1055267 = 1582901) B1582901
theorem B236083 : Blo 207808 236083 := bstep (se 1 (by rfl) ⟨177062, by rfl⟩ : syracuseStep 236083 = 354125) B354125
theorem B399971 : Blo 207808 399971 := bstep (se 1 (by rfl) ⟨299978, by rfl⟩ : syracuseStep 399971 = 599957) B599957
theorem B531107 : Blo 207808 531107 := bstep (se 1 (by rfl) ⟨398330, by rfl⟩ : syracuseStep 531107 = 796661) B796661
theorem B236227 : Blo 207808 236227 := bstep (se 1 (by rfl) ⟨177170, by rfl⟩ : syracuseStep 236227 = 354341) B354341
theorem B236371 : Blo 207808 236371 := bstep (se 1 (by rfl) ⟨177278, by rfl⟩ : syracuseStep 236371 = 354557) B354557
theorem B531299 : Blo 207808 531299 := bstep (se 1 (by rfl) ⟨398474, by rfl⟩ : syracuseStep 531299 = 796949) B796949
theorem B236515 : Blo 207808 236515 := bstep (se 1 (by rfl) ⟨177386, by rfl⟩ : syracuseStep 236515 = 354773) B354773
theorem B269347 : Blo 207808 269347 := bstep (se 1 (by rfl) ⟨202010, by rfl⟩ : syracuseStep 269347 = 404021) B404021
theorem B597041 : Blo 207808 597041 := bstep (se 2 (by rfl) ⟨223890, by rfl⟩ : syracuseStep 597041 = 447781) B447781
theorem B400465 : Blo 207808 400465 := bstep (se 2 (by rfl) ⟨150174, by rfl⟩ : syracuseStep 400465 = 300349) B300349
theorem B334945 : Blo 207808 334945 := bstep (se 2 (by rfl) ⟨125604, by rfl⟩ : syracuseStep 334945 = 251209) B251209
theorem B236659 : Blo 207808 236659 := bstep (se 1 (by rfl) ⟨177494, by rfl⟩ : syracuseStep 236659 = 354989) B354989
theorem B597233 : Blo 207808 597233 := bstep (se 2 (by rfl) ⟨223962, by rfl⟩ : syracuseStep 597233 = 447925) B447925
theorem B236803 : Blo 207808 236803 := bstep (se 1 (by rfl) ⟨177602, by rfl⟩ : syracuseStep 236803 = 355205) B355205
theorem B1056077 : Blo 207808 1056077 := bstep (se 3 (by rfl) ⟨198014, by rfl⟩ : syracuseStep 1056077 = 396029) B396029
theorem B236947 : Blo 207808 236947 := bstep (se 1 (by rfl) ⟨177710, by rfl⟩ : syracuseStep 236947 = 355421) B355421
theorem B794033 : Blo 207808 794033 := bstep (se 2 (by rfl) ⟨297762, by rfl⟩ : syracuseStep 794033 = 595525) B595525
theorem B237091 : Blo 207808 237091 := bstep (se 1 (by rfl) ⟨177818, by rfl⟩ : syracuseStep 237091 = 355637) B355637
theorem B1187405 : Blo 207808 1187405 := bstep (se 3 (by rfl) ⟨222638, by rfl⟩ : syracuseStep 1187405 = 445277) B445277
theorem B401041 : Blo 207808 401041 := bstep (se 2 (by rfl) ⟨150390, by rfl⟩ : syracuseStep 401041 = 300781) B300781
theorem B237235 : Blo 207808 237235 := bstep (se 1 (by rfl) ⟨177926, by rfl⟩ : syracuseStep 237235 = 355853) B355853
theorem B532241 : Blo 207808 532241 := bstep (se 2 (by rfl) ⟨199590, by rfl⟩ : syracuseStep 532241 = 399181) B399181
theorem B532291 : Blo 207808 532291 := bstep (se 1 (by rfl) ⟨399218, by rfl⟩ : syracuseStep 532291 = 798437) B798437
theorem B237379 : Blo 207808 237379 := bstep (se 1 (by rfl) ⟨178034, by rfl⟩ : syracuseStep 237379 = 356069) B356069
theorem B532433 : Blo 207808 532433 := bstep (se 2 (by rfl) ⟨199662, by rfl⟩ : syracuseStep 532433 = 399325) B399325
theorem B237523 : Blo 207808 237523 := bstep (se 1 (by rfl) ⟨178142, by rfl⟩ : syracuseStep 237523 = 356285) B356285
theorem B237667 : Blo 207808 237667 := bstep (se 1 (by rfl) ⟨178250, by rfl⟩ : syracuseStep 237667 = 356501) B356501
theorem B5480561 : Blo 207808 5480561 := bstep (se 2 (by rfl) ⟨2055210, by rfl⟩ : syracuseStep 5480561 = 4110421) B4110421
theorem B598225 : Blo 207808 598225 := bstep (se 2 (by rfl) ⟨224334, by rfl⟩ : syracuseStep 598225 = 448669) B448669
theorem B237811 : Blo 207808 237811 := bstep (se 1 (by rfl) ⟨178358, by rfl⟩ : syracuseStep 237811 = 356717) B356717
theorem B237955 : Blo 207808 237955 := bstep (se 1 (by rfl) ⟨178466, by rfl⟩ : syracuseStep 237955 = 356933) B356933
theorem B598499 : Blo 207808 598499 := bstep (se 1 (by rfl) ⟨448874, by rfl⟩ : syracuseStep 598499 = 897749) B897749
theorem B238099 : Blo 207808 238099 := bstep (se 1 (by rfl) ⟨178574, by rfl⟩ : syracuseStep 238099 = 357149) B357149
theorem B598691 : Blo 207808 598691 := bstep (se 1 (by rfl) ⟨449018, by rfl⟩ : syracuseStep 598691 = 898037) B898037
theorem B238243 : Blo 207808 238243 := bstep (se 1 (by rfl) ⟨178682, by rfl⟩ : syracuseStep 238243 = 357365) B357365
theorem B402097 : Blo 207808 402097 := bstep (se 2 (by rfl) ⟨150786, by rfl⟩ : syracuseStep 402097 = 301573) B301573
theorem B565955 : Blo 207808 565955 := bstep (se 1 (by rfl) ⟨424466, by rfl⟩ : syracuseStep 565955 = 848933) B848933
theorem B336611 : Blo 207808 336611 := bstep (se 1 (by rfl) ⟨252458, by rfl⟩ : syracuseStep 336611 = 504917) B504917
theorem B467729 : Blo 207808 467729 := bstep (se 2 (by rfl) ⟨175398, by rfl⟩ : syracuseStep 467729 = 350797) B350797
theorem B467747 : Blo 207808 467747 := bstep (se 1 (by rfl) ⟨350810, by rfl⟩ : syracuseStep 467747 = 701621) B701621
theorem B795491 : Blo 207808 795491 := bstep (se 1 (by rfl) ⟨596618, by rfl⟩ : syracuseStep 795491 = 1193237) B1193237
theorem B336739 : Blo 207808 336739 := bstep (se 1 (by rfl) ⟨252554, by rfl⟩ : syracuseStep 336739 = 505109) B505109
theorem B566129 : Blo 207808 566129 := bstep (se 2 (by rfl) ⟨212298, by rfl⟩ : syracuseStep 566129 = 424597) B424597
theorem B8070029 : Blo 207808 8070029 := bstep (se 3 (by rfl) ⟨1513130, by rfl⟩ : syracuseStep 8070029 = 3026261) B3026261
theorem B533425 : Blo 207808 533425 := bstep (se 2 (by rfl) ⟨200034, by rfl⟩ : syracuseStep 533425 = 400069) B400069
theorem B1352645 : Blo 207808 1352645 := bstep (se 4 (by rfl) ⟨126810, by rfl⟩ : syracuseStep 1352645 = 253621) B253621
theorem B468017 : Blo 207808 468017 := bstep (se 2 (by rfl) ⟨175506, by rfl⟩ : syracuseStep 468017 = 351013) B351013
theorem B468035 : Blo 207808 468035 := bstep (se 1 (by rfl) ⟨351026, by rfl⟩ : syracuseStep 468035 = 702053) B702053
theorem B664643 : Blo 207808 664643 := bstep (se 1 (by rfl) ⟨498482, by rfl⟩ : syracuseStep 664643 = 996965) B996965
theorem B533699 : Blo 207808 533699 := bstep (se 1 (by rfl) ⟨400274, by rfl⟩ : syracuseStep 533699 = 800549) B800549
theorem B337123 : Blo 207808 337123 := bstep (se 1 (by rfl) ⟨252842, by rfl⟩ : syracuseStep 337123 = 505685) B505685
theorem B468305 : Blo 207808 468305 := bstep (se 2 (by rfl) ⟨175614, by rfl⟩ : syracuseStep 468305 = 351229) B351229
theorem B468323 : Blo 207808 468323 := bstep (se 1 (by rfl) ⟨351242, by rfl⟩ : syracuseStep 468323 = 702485) B702485
theorem B533891 : Blo 207808 533891 := bstep (se 1 (by rfl) ⟨400418, by rfl⟩ : syracuseStep 533891 = 800837) B800837
theorem B566669 : Blo 207808 566669 := bstep (se 3 (by rfl) ⟨106250, by rfl⟩ : syracuseStep 566669 = 212501) B212501
theorem B599501 : Blo 207808 599501 := bstep (se 3 (by rfl) ⟨112406, by rfl⟩ : syracuseStep 599501 = 224813) B224813
theorem B1910243 : Blo 207808 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B337379 : Blo 207808 337379 := bstep (se 1 (by rfl) ⟨253034, by rfl⟩ : syracuseStep 337379 = 506069) B506069
theorem B468593 : Blo 207808 468593 := bstep (se 2 (by rfl) ⟨175722, by rfl⟩ : syracuseStep 468593 = 351445) B351445
theorem B468611 : Blo 207808 468611 := bstep (se 1 (by rfl) ⟨351458, by rfl⟩ : syracuseStep 468611 = 702917) B702917
theorem B599683 : Blo 207808 599683 := bstep (se 1 (by rfl) ⟨449762, by rfl⟩ : syracuseStep 599683 = 899525) B899525
theorem B566929 : Blo 207808 566929 := bstep (se 2 (by rfl) ⟨212598, by rfl⟩ : syracuseStep 566929 = 425197) B425197
theorem B1189637 : Blo 207808 1189637 := bstep (se 4 (by rfl) ⟨111528, by rfl⟩ : syracuseStep 1189637 = 223057) B223057
theorem B796493 : Blo 207808 796493 := bstep (se 3 (by rfl) ⟨149342, by rfl⟩ : syracuseStep 796493 = 298685) B298685
theorem B468881 : Blo 207808 468881 := bstep (se 2 (by rfl) ⟨175830, by rfl⟩ : syracuseStep 468881 = 351661) B351661
theorem B468899 : Blo 207808 468899 := bstep (se 1 (by rfl) ⟨351674, by rfl⟩ : syracuseStep 468899 = 703349) B703349
theorem B337841 : Blo 207808 337841 := bstep (se 2 (by rfl) ⟨126690, by rfl⟩ : syracuseStep 337841 = 253381) B253381
theorem B501763 : Blo 207808 501763 := bstep (se 1 (by rfl) ⟨376322, by rfl⟩ : syracuseStep 501763 = 752645) B752645
theorem B337937 : Blo 207808 337937 := bstep (se 2 (by rfl) ⟨126726, by rfl⟩ : syracuseStep 337937 = 253453) B253453
theorem B337969 : Blo 207808 337969 := bstep (se 2 (by rfl) ⟨126738, by rfl⟩ : syracuseStep 337969 = 253477) B253477
theorem B600173 : Blo 207808 600173 := bstep (se 3 (by rfl) ⟨112532, by rfl⟩ : syracuseStep 600173 = 225065) B225065
theorem B469169 : Blo 207808 469169 := bstep (se 2 (by rfl) ⟨175938, by rfl⟩ : syracuseStep 469169 = 351877) B351877
theorem B1058993 : Blo 207808 1058993 := bstep (se 2 (by rfl) ⟨397122, by rfl⟩ : syracuseStep 1058993 = 794245) B794245
theorem B469187 : Blo 207808 469187 := bstep (se 1 (by rfl) ⟨351890, by rfl⟩ : syracuseStep 469187 = 703781) B703781
theorem B2009285 : Blo 207808 2009285 := bstep (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) B376741
theorem B502033 : Blo 207808 502033 := bstep (se 2 (by rfl) ⟨188262, by rfl⟩ : syracuseStep 502033 = 376525) B376525
theorem B665891 : Blo 207808 665891 := bstep (se 1 (by rfl) ⟨499418, by rfl⟩ : syracuseStep 665891 = 998837) B998837
theorem B534833 : Blo 207808 534833 := bstep (se 2 (by rfl) ⟨200562, by rfl⟩ : syracuseStep 534833 = 401125) B401125
theorem B534883 : Blo 207808 534883 := bstep (se 1 (by rfl) ⟨401162, by rfl⟩ : syracuseStep 534883 = 802325) B802325
theorem B895373 : Blo 207808 895373 := bstep (se 3 (by rfl) ⟨167882, by rfl⟩ : syracuseStep 895373 = 335765) B335765
theorem B1190321 : Blo 207808 1190321 := bstep (se 2 (by rfl) ⟨446370, by rfl⟩ : syracuseStep 1190321 = 892741) B892741
theorem B469457 : Blo 207808 469457 := bstep (se 2 (by rfl) ⟨176046, by rfl⟩ : syracuseStep 469457 = 352093) B352093
theorem B469475 : Blo 207808 469475 := bstep (se 1 (by rfl) ⟨352106, by rfl⟩ : syracuseStep 469475 = 704213) B704213
theorem B535025 : Blo 207808 535025 := bstep (se 2 (by rfl) ⟨200634, by rfl⟩ : syracuseStep 535025 = 401269) B401269
theorem B567857 : Blo 207808 567857 := bstep (se 2 (by rfl) ⟨212946, by rfl⟩ : syracuseStep 567857 = 425893) B425893
theorem B469745 : Blo 207808 469745 := bstep (se 2 (by rfl) ⟨176154, by rfl⟩ : syracuseStep 469745 = 352309) B352309
theorem B469763 : Blo 207808 469763 := bstep (se 1 (by rfl) ⟨352322, by rfl⟩ : syracuseStep 469763 = 704645) B704645
theorem B633635 : Blo 207808 633635 := bstep (se 1 (by rfl) ⟨475226, by rfl⟩ : syracuseStep 633635 = 950453) B950453
theorem B666481 : Blo 207808 666481 := bstep (se 2 (by rfl) ⟨249930, by rfl⟩ : syracuseStep 666481 = 499861) B499861
theorem B207811 : Blo 207808 207811 := bstep (se 1 (by rfl) ⟨155858, by rfl⟩ : syracuseStep 207811 = 311717) B311717
theorem B207827 : Blo 207808 207827 := bstep (se 1 (by rfl) ⟨155870, by rfl⟩ : syracuseStep 207827 = 311741) B311741
theorem B207843 : Blo 207808 207843 := bstep (se 1 (by rfl) ⟨155882, by rfl⟩ : syracuseStep 207843 = 311765) B311765
theorem B2698211 : Blo 207808 2698211 := bstep (se 1 (by rfl) ⟨2023658, by rfl⟩ : syracuseStep 2698211 = 4047317) B4047317
theorem B207859 : Blo 207808 207859 := bstep (se 1 (by rfl) ⟨155894, by rfl⟩ : syracuseStep 207859 = 311789) B311789
theorem B207875 : Blo 207808 207875 := bstep (se 1 (by rfl) ⟨155906, by rfl⟩ : syracuseStep 207875 = 311813) B311813
theorem B470033 : Blo 207808 470033 := bstep (se 2 (by rfl) ⟨176262, by rfl⟩ : syracuseStep 470033 = 352525) B352525
theorem B207891 : Blo 207808 207891 := bstep (se 1 (by rfl) ⟨155918, by rfl⟩ : syracuseStep 207891 = 311837) B311837
theorem B207907 : Blo 207808 207907 := bstep (se 1 (by rfl) ⟨155930, by rfl⟩ : syracuseStep 207907 = 311861) B311861
theorem B470051 : Blo 207808 470051 := bstep (se 1 (by rfl) ⟨352538, by rfl⟩ : syracuseStep 470051 = 705077) B705077
theorem B207923 : Blo 207808 207923 := bstep (se 1 (by rfl) ⟨155942, by rfl⟩ : syracuseStep 207923 = 311885) B311885
theorem B207939 : Blo 207808 207939 := bstep (se 1 (by rfl) ⟨155954, by rfl⟩ : syracuseStep 207939 = 311909) B311909
theorem B207955 : Blo 207808 207955 := bstep (se 1 (by rfl) ⟨155966, by rfl⟩ : syracuseStep 207955 = 311933) B311933
theorem B207971 : Blo 207808 207971 := bstep (se 1 (by rfl) ⟨155978, by rfl⟩ : syracuseStep 207971 = 311957) B311957
theorem B207987 : Blo 207808 207987 := bstep (se 1 (by rfl) ⟨155990, by rfl⟩ : syracuseStep 207987 = 311981) B311981
theorem B208003 : Blo 207808 208003 := bstep (se 1 (by rfl) ⟨156002, by rfl⟩ : syracuseStep 208003 = 312005) B312005
theorem B208019 : Blo 207808 208019 := bstep (se 1 (by rfl) ⟨156014, by rfl⟩ : syracuseStep 208019 = 312029) B312029
theorem B208035 : Blo 207808 208035 := bstep (se 1 (by rfl) ⟨156026, by rfl⟩ : syracuseStep 208035 = 312053) B312053
theorem B208051 : Blo 207808 208051 := bstep (se 1 (by rfl) ⟨156038, by rfl⟩ : syracuseStep 208051 = 312077) B312077
theorem B208067 : Blo 207808 208067 := bstep (se 1 (by rfl) ⟨156050, by rfl⟩ : syracuseStep 208067 = 312101) B312101
theorem B502993 : Blo 207808 502993 := bstep (se 2 (by rfl) ⟨188622, by rfl⟩ : syracuseStep 502993 = 377245) B377245
theorem B208083 : Blo 207808 208083 := bstep (se 1 (by rfl) ⟨156062, by rfl⟩ : syracuseStep 208083 = 312125) B312125
theorem B208099 : Blo 207808 208099 := bstep (se 1 (by rfl) ⟨156074, by rfl⟩ : syracuseStep 208099 = 312149) B312149
theorem B208115 : Blo 207808 208115 := bstep (se 1 (by rfl) ⟨156086, by rfl⟩ : syracuseStep 208115 = 312173) B312173
theorem B208131 : Blo 207808 208131 := bstep (se 1 (by rfl) ⟨156098, by rfl⟩ : syracuseStep 208131 = 312197) B312197
theorem B601357 : Blo 207808 601357 := bstep (se 3 (by rfl) ⟨112754, by rfl⟩ : syracuseStep 601357 = 225509) B225509
theorem B208147 : Blo 207808 208147 := bstep (se 1 (by rfl) ⟨156110, by rfl⟩ : syracuseStep 208147 = 312221) B312221
theorem B208163 : Blo 207808 208163 := bstep (se 1 (by rfl) ⟨156122, by rfl⟩ : syracuseStep 208163 = 312245) B312245
theorem B470321 : Blo 207808 470321 := bstep (se 2 (by rfl) ⟨176370, by rfl⟩ : syracuseStep 470321 = 352741) B352741
theorem B208179 : Blo 207808 208179 := bstep (se 1 (by rfl) ⟨156134, by rfl⟩ : syracuseStep 208179 = 312269) B312269
theorem B208195 : Blo 207808 208195 := bstep (se 1 (by rfl) ⟨156146, by rfl⟩ : syracuseStep 208195 = 312293) B312293
theorem B470339 : Blo 207808 470339 := bstep (se 1 (by rfl) ⟨352754, by rfl⟩ : syracuseStep 470339 = 705509) B705509
theorem B208211 : Blo 207808 208211 := bstep (se 1 (by rfl) ⟨156158, by rfl⟩ : syracuseStep 208211 = 312317) B312317
theorem B208227 : Blo 207808 208227 := bstep (se 1 (by rfl) ⟨156170, by rfl⟩ : syracuseStep 208227 = 312341) B312341
theorem B208243 : Blo 207808 208243 := bstep (se 1 (by rfl) ⟨156182, by rfl⟩ : syracuseStep 208243 = 312365) B312365
theorem B339329 : Blo 207808 339329 := bstep (se 2 (by rfl) ⟨127248, by rfl⟩ : syracuseStep 339329 = 254497) B254497
theorem B208259 : Blo 207808 208259 := bstep (se 1 (by rfl) ⟨156194, by rfl⟩ : syracuseStep 208259 = 312389) B312389
theorem B208275 : Blo 207808 208275 := bstep (se 1 (by rfl) ⟨156206, by rfl⟩ : syracuseStep 208275 = 312413) B312413
theorem B208291 : Blo 207808 208291 := bstep (se 1 (by rfl) ⟨156218, by rfl⟩ : syracuseStep 208291 = 312437) B312437
theorem B1027505 : Blo 207808 1027505 := bstep (se 2 (by rfl) ⟨385314, by rfl⟩ : syracuseStep 1027505 = 770629) B770629
theorem B208307 : Blo 207808 208307 := bstep (se 1 (by rfl) ⟨156230, by rfl⟩ : syracuseStep 208307 = 312461) B312461
theorem B208323 : Blo 207808 208323 := bstep (se 1 (by rfl) ⟨156242, by rfl⟩ : syracuseStep 208323 = 312485) B312485
theorem B536017 : Blo 207808 536017 := bstep (se 2 (by rfl) ⟨201006, by rfl⟩ : syracuseStep 536017 = 402013) B402013
theorem B208339 : Blo 207808 208339 := bstep (se 1 (by rfl) ⟨156254, by rfl⟩ : syracuseStep 208339 = 312509) B312509
theorem B208355 : Blo 207808 208355 := bstep (se 1 (by rfl) ⟨156266, by rfl⟩ : syracuseStep 208355 = 312533) B312533
theorem B208371 : Blo 207808 208371 := bstep (se 1 (by rfl) ⟨156278, by rfl⟩ : syracuseStep 208371 = 312557) B312557
theorem B208387 : Blo 207808 208387 := bstep (se 1 (by rfl) ⟨156290, by rfl⟩ : syracuseStep 208387 = 312581) B312581
theorem B208403 : Blo 207808 208403 := bstep (se 1 (by rfl) ⟨156302, by rfl⟩ : syracuseStep 208403 = 312605) B312605
theorem B208419 : Blo 207808 208419 := bstep (se 1 (by rfl) ⟨156314, by rfl⟩ : syracuseStep 208419 = 312629) B312629
theorem B208435 : Blo 207808 208435 := bstep (se 1 (by rfl) ⟨156326, by rfl⟩ : syracuseStep 208435 = 312653) B312653
theorem B208451 : Blo 207808 208451 := bstep (se 1 (by rfl) ⟨156338, by rfl⟩ : syracuseStep 208451 = 312677) B312677
theorem B470609 : Blo 207808 470609 := bstep (se 2 (by rfl) ⟨176478, by rfl⟩ : syracuseStep 470609 = 352957) B352957
theorem B208467 : Blo 207808 208467 := bstep (se 1 (by rfl) ⟨156350, by rfl⟩ : syracuseStep 208467 = 312701) B312701
theorem B208483 : Blo 207808 208483 := bstep (se 1 (by rfl) ⟨156362, by rfl⟩ : syracuseStep 208483 = 312725) B312725
theorem B470627 : Blo 207808 470627 := bstep (se 1 (by rfl) ⟨352970, by rfl⟩ : syracuseStep 470627 = 705941) B705941
theorem B1060451 : Blo 207808 1060451 := bstep (se 1 (by rfl) ⟨795338, by rfl⟩ : syracuseStep 1060451 = 1590677) B1590677
theorem B208499 : Blo 207808 208499 := bstep (se 1 (by rfl) ⟨156374, by rfl⟩ : syracuseStep 208499 = 312749) B312749
theorem B208515 : Blo 207808 208515 := bstep (se 1 (by rfl) ⟨156386, by rfl⟩ : syracuseStep 208515 = 312773) B312773
theorem B962189 : Blo 207808 962189 := bstep (se 3 (by rfl) ⟨180410, by rfl⟩ : syracuseStep 962189 = 360821) B360821
theorem B208531 : Blo 207808 208531 := bstep (se 1 (by rfl) ⟨156398, by rfl⟩ : syracuseStep 208531 = 312797) B312797
theorem B208547 : Blo 207808 208547 := bstep (se 1 (by rfl) ⟨156410, by rfl⟩ : syracuseStep 208547 = 312821) B312821
theorem B208563 : Blo 207808 208563 := bstep (se 1 (by rfl) ⟨156422, by rfl⟩ : syracuseStep 208563 = 312845) B312845
theorem B208579 : Blo 207808 208579 := bstep (se 1 (by rfl) ⟨156434, by rfl⟩ : syracuseStep 208579 = 312869) B312869
theorem B208595 : Blo 207808 208595 := bstep (se 1 (by rfl) ⟨156446, by rfl⟩ : syracuseStep 208595 = 312893) B312893
theorem B208611 : Blo 207808 208611 := bstep (se 1 (by rfl) ⟨156458, by rfl⟩ : syracuseStep 208611 = 312917) B312917
theorem B208627 : Blo 207808 208627 := bstep (se 1 (by rfl) ⟨156470, by rfl⟩ : syracuseStep 208627 = 312941) B312941
theorem B208643 : Blo 207808 208643 := bstep (se 1 (by rfl) ⟨156482, by rfl⟩ : syracuseStep 208643 = 312965) B312965
theorem B208659 : Blo 207808 208659 := bstep (se 1 (by rfl) ⟨156494, by rfl⟩ : syracuseStep 208659 = 312989) B312989
theorem B208675 : Blo 207808 208675 := bstep (se 1 (by rfl) ⟨156506, by rfl⟩ : syracuseStep 208675 = 313013) B313013
theorem B208691 : Blo 207808 208691 := bstep (se 1 (by rfl) ⟨156518, by rfl⟩ : syracuseStep 208691 = 313037) B313037
theorem B208707 : Blo 207808 208707 := bstep (se 1 (by rfl) ⟨156530, by rfl⟩ : syracuseStep 208707 = 313061) B313061
theorem B208723 : Blo 207808 208723 := bstep (se 1 (by rfl) ⟨156542, by rfl⟩ : syracuseStep 208723 = 313085) B313085
theorem B208739 : Blo 207808 208739 := bstep (se 1 (by rfl) ⟨156554, by rfl⟩ : syracuseStep 208739 = 313109) B313109
theorem B1191779 : Blo 207808 1191779 := bstep (se 1 (by rfl) ⟨893834, by rfl⟩ : syracuseStep 1191779 = 1787669) B1787669
theorem B470897 : Blo 207808 470897 := bstep (se 2 (by rfl) ⟨176586, by rfl⟩ : syracuseStep 470897 = 353173) B353173
theorem B208755 : Blo 207808 208755 := bstep (se 1 (by rfl) ⟨156566, by rfl⟩ : syracuseStep 208755 = 313133) B313133
theorem B208771 : Blo 207808 208771 := bstep (se 1 (by rfl) ⟨156578, by rfl⟩ : syracuseStep 208771 = 313157) B313157
theorem B470915 : Blo 207808 470915 := bstep (se 1 (by rfl) ⟨353186, by rfl⟩ : syracuseStep 470915 = 706373) B706373
theorem B798605 : Blo 207808 798605 := bstep (se 3 (by rfl) ⟨149738, by rfl⟩ : syracuseStep 798605 = 299477) B299477
theorem B208787 : Blo 207808 208787 := bstep (se 1 (by rfl) ⟨156590, by rfl⟩ : syracuseStep 208787 = 313181) B313181
theorem B208803 : Blo 207808 208803 := bstep (se 1 (by rfl) ⟨156602, by rfl⟩ : syracuseStep 208803 = 313205) B313205
theorem B208819 : Blo 207808 208819 := bstep (se 1 (by rfl) ⟨156614, by rfl⟩ : syracuseStep 208819 = 313229) B313229
theorem B208835 : Blo 207808 208835 := bstep (se 1 (by rfl) ⟨156626, by rfl⟩ : syracuseStep 208835 = 313253) B313253
theorem B208851 : Blo 207808 208851 := bstep (se 1 (by rfl) ⟨156638, by rfl⟩ : syracuseStep 208851 = 313277) B313277
theorem B208867 : Blo 207808 208867 := bstep (se 1 (by rfl) ⟨156650, by rfl⟩ : syracuseStep 208867 = 313301) B313301
theorem B208883 : Blo 207808 208883 := bstep (se 1 (by rfl) ⟨156662, by rfl⟩ : syracuseStep 208883 = 313325) B313325
theorem B208899 : Blo 207808 208899 := bstep (se 1 (by rfl) ⟨156674, by rfl⟩ : syracuseStep 208899 = 313349) B313349
theorem B208915 : Blo 207808 208915 := bstep (se 1 (by rfl) ⟨156686, by rfl⟩ : syracuseStep 208915 = 313373) B313373
theorem B208931 : Blo 207808 208931 := bstep (se 1 (by rfl) ⟨156698, by rfl⟩ : syracuseStep 208931 = 313397) B313397
theorem B208947 : Blo 207808 208947 := bstep (se 1 (by rfl) ⟨156710, by rfl⟩ : syracuseStep 208947 = 313421) B313421
theorem B208963 : Blo 207808 208963 := bstep (se 1 (by rfl) ⟨156722, by rfl⟩ : syracuseStep 208963 = 313445) B313445
theorem B208979 : Blo 207808 208979 := bstep (se 1 (by rfl) ⟨156734, by rfl⟩ : syracuseStep 208979 = 313469) B313469
theorem B208995 : Blo 207808 208995 := bstep (se 1 (by rfl) ⟨156746, by rfl⟩ : syracuseStep 208995 = 313493) B313493
theorem B209011 : Blo 207808 209011 := bstep (se 1 (by rfl) ⟨156758, by rfl⟩ : syracuseStep 209011 = 313517) B313517
theorem B209027 : Blo 207808 209027 := bstep (se 1 (by rfl) ⟨156770, by rfl⟩ : syracuseStep 209027 = 313541) B313541
theorem B471185 : Blo 207808 471185 := bstep (se 2 (by rfl) ⟨176694, by rfl⟩ : syracuseStep 471185 = 353389) B353389
theorem B209043 : Blo 207808 209043 := bstep (se 1 (by rfl) ⟨156782, by rfl⟩ : syracuseStep 209043 = 313565) B313565
theorem B209059 : Blo 207808 209059 := bstep (se 1 (by rfl) ⟨156794, by rfl⟩ : syracuseStep 209059 = 313589) B313589
theorem B471203 : Blo 207808 471203 := bstep (se 1 (by rfl) ⟨353402, by rfl⟩ : syracuseStep 471203 = 706805) B706805
theorem B209075 : Blo 207808 209075 := bstep (se 1 (by rfl) ⟨156806, by rfl⟩ : syracuseStep 209075 = 313613) B313613
theorem B209091 : Blo 207808 209091 := bstep (se 1 (by rfl) ⟨156818, by rfl⟩ : syracuseStep 209091 = 313637) B313637
theorem B209107 : Blo 207808 209107 := bstep (se 1 (by rfl) ⟨156830, by rfl⟩ : syracuseStep 209107 = 313661) B313661
theorem B340193 : Blo 207808 340193 := bstep (se 2 (by rfl) ⟨127572, by rfl⟩ : syracuseStep 340193 = 255145) B255145
theorem B209123 : Blo 207808 209123 := bstep (se 1 (by rfl) ⟨156842, by rfl⟩ : syracuseStep 209123 = 313685) B313685
theorem B209139 : Blo 207808 209139 := bstep (se 1 (by rfl) ⟨156854, by rfl⟩ : syracuseStep 209139 = 313709) B313709
theorem B209155 : Blo 207808 209155 := bstep (se 1 (by rfl) ⟨156866, by rfl⟩ : syracuseStep 209155 = 313733) B313733
theorem B209171 : Blo 207808 209171 := bstep (se 1 (by rfl) ⟨156878, by rfl⟩ : syracuseStep 209171 = 313757) B313757
theorem B209187 : Blo 207808 209187 := bstep (se 1 (by rfl) ⟨156890, by rfl⟩ : syracuseStep 209187 = 313781) B313781
theorem B602417 : Blo 207808 602417 := bstep (se 2 (by rfl) ⟨225906, by rfl⟩ : syracuseStep 602417 = 451813) B451813
theorem B209203 : Blo 207808 209203 := bstep (se 1 (by rfl) ⟨156902, by rfl⟩ : syracuseStep 209203 = 313805) B313805
theorem B209219 : Blo 207808 209219 := bstep (se 1 (by rfl) ⟨156914, by rfl⟩ : syracuseStep 209219 = 313829) B313829
theorem B209235 : Blo 207808 209235 := bstep (se 1 (by rfl) ⟨156926, by rfl⟩ : syracuseStep 209235 = 313853) B313853
theorem B209251 : Blo 207808 209251 := bstep (se 1 (by rfl) ⟨156938, by rfl⟩ : syracuseStep 209251 = 313877) B313877
theorem B209267 : Blo 207808 209267 := bstep (se 1 (by rfl) ⟨156950, by rfl⟩ : syracuseStep 209267 = 313901) B313901
theorem B307585 : Blo 207808 307585 := bstep (se 2 (by rfl) ⟨115344, by rfl⟩ : syracuseStep 307585 = 230689) B230689
theorem B209283 : Blo 207808 209283 := bstep (se 1 (by rfl) ⟨156962, by rfl⟩ : syracuseStep 209283 = 313925) B313925
theorem B1061261 : Blo 207808 1061261 := bstep (se 3 (by rfl) ⟨198986, by rfl⟩ : syracuseStep 1061261 = 397973) B397973
theorem B209299 : Blo 207808 209299 := bstep (se 1 (by rfl) ⟨156974, by rfl⟩ : syracuseStep 209299 = 313949) B313949
theorem B209315 : Blo 207808 209315 := bstep (se 1 (by rfl) ⟨156986, by rfl⟩ : syracuseStep 209315 = 313973) B313973
theorem B471473 : Blo 207808 471473 := bstep (se 2 (by rfl) ⟨176802, by rfl⟩ : syracuseStep 471473 = 353605) B353605
theorem B209331 : Blo 207808 209331 := bstep (se 1 (by rfl) ⟨156998, by rfl⟩ : syracuseStep 209331 = 313997) B313997
theorem B209347 : Blo 207808 209347 := bstep (se 1 (by rfl) ⟨157010, by rfl⟩ : syracuseStep 209347 = 314021) B314021
theorem B471491 : Blo 207808 471491 := bstep (se 1 (by rfl) ⟨353618, by rfl⟩ : syracuseStep 471491 = 707237) B707237
theorem B1716677 : Blo 207808 1716677 := bstep (se 4 (by rfl) ⟨160938, by rfl⟩ : syracuseStep 1716677 = 321877) B321877
theorem B209363 : Blo 207808 209363 := bstep (se 1 (by rfl) ⟨157022, by rfl⟩ : syracuseStep 209363 = 314045) B314045
theorem B209379 : Blo 207808 209379 := bstep (se 1 (by rfl) ⟨157034, by rfl⟩ : syracuseStep 209379 = 314069) B314069
theorem B209395 : Blo 207808 209395 := bstep (se 1 (by rfl) ⟨157046, by rfl⟩ : syracuseStep 209395 = 314093) B314093
theorem B209411 : Blo 207808 209411 := bstep (se 1 (by rfl) ⟨157058, by rfl⟩ : syracuseStep 209411 = 314117) B314117
theorem B209427 : Blo 207808 209427 := bstep (se 1 (by rfl) ⟨157070, by rfl⟩ : syracuseStep 209427 = 314141) B314141
theorem B209443 : Blo 207808 209443 := bstep (se 1 (by rfl) ⟨157082, by rfl⟩ : syracuseStep 209443 = 314165) B314165
theorem B209459 : Blo 207808 209459 := bstep (se 1 (by rfl) ⟨157094, by rfl⟩ : syracuseStep 209459 = 314189) B314189
theorem B209475 : Blo 207808 209475 := bstep (se 1 (by rfl) ⟨157106, by rfl⟩ : syracuseStep 209475 = 314213) B314213
theorem B2372165 : Blo 207808 2372165 := bstep (se 4 (by rfl) ⟨222390, by rfl⟩ : syracuseStep 2372165 = 444781) B444781
theorem B209491 : Blo 207808 209491 := bstep (se 1 (by rfl) ⟨157118, by rfl⟩ : syracuseStep 209491 = 314237) B314237
theorem B209507 : Blo 207808 209507 := bstep (se 1 (by rfl) ⟨157130, by rfl⟩ : syracuseStep 209507 = 314261) B314261
theorem B209523 : Blo 207808 209523 := bstep (se 1 (by rfl) ⟨157142, by rfl⟩ : syracuseStep 209523 = 314285) B314285
theorem B209539 : Blo 207808 209539 := bstep (se 1 (by rfl) ⟨157154, by rfl⟩ : syracuseStep 209539 = 314309) B314309
theorem B209555 : Blo 207808 209555 := bstep (se 1 (by rfl) ⟨157166, by rfl⟩ : syracuseStep 209555 = 314333) B314333
theorem B209571 : Blo 207808 209571 := bstep (se 1 (by rfl) ⟨157178, by rfl⟩ : syracuseStep 209571 = 314357) B314357
theorem B799409 : Blo 207808 799409 := bstep (se 2 (by rfl) ⟨299778, by rfl⟩ : syracuseStep 799409 = 599557) B599557
theorem B209587 : Blo 207808 209587 := bstep (se 1 (by rfl) ⟨157190, by rfl⟩ : syracuseStep 209587 = 314381) B314381
theorem B209603 : Blo 207808 209603 := bstep (se 1 (by rfl) ⟨157202, by rfl⟩ : syracuseStep 209603 = 314405) B314405
theorem B471761 : Blo 207808 471761 := bstep (se 2 (by rfl) ⟨176910, by rfl⟩ : syracuseStep 471761 = 353821) B353821
theorem B209619 : Blo 207808 209619 := bstep (se 1 (by rfl) ⟨157214, by rfl⟩ : syracuseStep 209619 = 314429) B314429
theorem B209635 : Blo 207808 209635 := bstep (se 1 (by rfl) ⟨157226, by rfl⟩ : syracuseStep 209635 = 314453) B314453
theorem B471779 : Blo 207808 471779 := bstep (se 1 (by rfl) ⟨353834, by rfl⟩ : syracuseStep 471779 = 707669) B707669
theorem B209651 : Blo 207808 209651 := bstep (se 1 (by rfl) ⟨157238, by rfl⟩ : syracuseStep 209651 = 314477) B314477
theorem B209667 : Blo 207808 209667 := bstep (se 1 (by rfl) ⟨157250, by rfl⟩ : syracuseStep 209667 = 314501) B314501
theorem B209683 : Blo 207808 209683 := bstep (se 1 (by rfl) ⟨157262, by rfl⟩ : syracuseStep 209683 = 314525) B314525
theorem B209699 : Blo 207808 209699 := bstep (se 1 (by rfl) ⟨157274, by rfl⟩ : syracuseStep 209699 = 314549) B314549
theorem B209715 : Blo 207808 209715 := bstep (se 1 (by rfl) ⟨157286, by rfl⟩ : syracuseStep 209715 = 314573) B314573
theorem B209731 : Blo 207808 209731 := bstep (se 1 (by rfl) ⟨157298, by rfl⟩ : syracuseStep 209731 = 314597) B314597
theorem B209747 : Blo 207808 209747 := bstep (se 1 (by rfl) ⟨157310, by rfl⟩ : syracuseStep 209747 = 314621) B314621
theorem B209763 : Blo 207808 209763 := bstep (se 1 (by rfl) ⟨157322, by rfl⟩ : syracuseStep 209763 = 314645) B314645
theorem B209779 : Blo 207808 209779 := bstep (se 1 (by rfl) ⟨157334, by rfl⟩ : syracuseStep 209779 = 314669) B314669
theorem B209795 : Blo 207808 209795 := bstep (se 1 (by rfl) ⟨157346, by rfl⟩ : syracuseStep 209795 = 314693) B314693
theorem B209811 : Blo 207808 209811 := bstep (se 1 (by rfl) ⟨157358, by rfl⟩ : syracuseStep 209811 = 314717) B314717
theorem B209827 : Blo 207808 209827 := bstep (se 1 (by rfl) ⟨157370, by rfl⟩ : syracuseStep 209827 = 314741) B314741
theorem B635825 : Blo 207808 635825 := bstep (se 2 (by rfl) ⟨238434, by rfl⟩ : syracuseStep 635825 = 476869) B476869
theorem B209843 : Blo 207808 209843 := bstep (se 1 (by rfl) ⟨157382, by rfl⟩ : syracuseStep 209843 = 314765) B314765
theorem B209859 : Blo 207808 209859 := bstep (se 1 (by rfl) ⟨157394, by rfl⟩ : syracuseStep 209859 = 314789) B314789
theorem B603089 : Blo 207808 603089 := bstep (se 2 (by rfl) ⟨226158, by rfl⟩ : syracuseStep 603089 = 452317) B452317
theorem B209875 : Blo 207808 209875 := bstep (se 1 (by rfl) ⟨157406, by rfl⟩ : syracuseStep 209875 = 314813) B314813
theorem B209891 : Blo 207808 209891 := bstep (se 1 (by rfl) ⟨157418, by rfl⟩ : syracuseStep 209891 = 314837) B314837
theorem B472049 : Blo 207808 472049 := bstep (se 2 (by rfl) ⟨177018, by rfl⟩ : syracuseStep 472049 = 354037) B354037
theorem B209907 : Blo 207808 209907 := bstep (se 1 (by rfl) ⟨157430, by rfl⟩ : syracuseStep 209907 = 314861) B314861
theorem B472067 : Blo 207808 472067 := bstep (se 1 (by rfl) ⟨354050, by rfl⟩ : syracuseStep 472067 = 708101) B708101
theorem B209923 : Blo 207808 209923 := bstep (se 1 (by rfl) ⟨157442, by rfl⟩ : syracuseStep 209923 = 314885) B314885
theorem B209939 : Blo 207808 209939 := bstep (se 1 (by rfl) ⟨157454, by rfl⟩ : syracuseStep 209939 = 314909) B314909
theorem B209955 : Blo 207808 209955 := bstep (se 1 (by rfl) ⟨157466, by rfl⟩ : syracuseStep 209955 = 314933) B314933
theorem B209971 : Blo 207808 209971 := bstep (se 1 (by rfl) ⟨157478, by rfl⟩ : syracuseStep 209971 = 314957) B314957
theorem B209987 : Blo 207808 209987 := bstep (se 1 (by rfl) ⟨157490, by rfl⟩ : syracuseStep 209987 = 314981) B314981
theorem B210003 : Blo 207808 210003 := bstep (se 1 (by rfl) ⟨157502, by rfl⟩ : syracuseStep 210003 = 315005) B315005
theorem B210019 : Blo 207808 210019 := bstep (se 1 (by rfl) ⟨157514, by rfl⟩ : syracuseStep 210019 = 315029) B315029
theorem B210035 : Blo 207808 210035 := bstep (se 1 (by rfl) ⟨157526, by rfl⟩ : syracuseStep 210035 = 315053) B315053
theorem B210051 : Blo 207808 210051 := bstep (se 1 (by rfl) ⟨157538, by rfl⟩ : syracuseStep 210051 = 315077) B315077
theorem B210067 : Blo 207808 210067 := bstep (se 1 (by rfl) ⟨157550, by rfl⟩ : syracuseStep 210067 = 315101) B315101
theorem B210083 : Blo 207808 210083 := bstep (se 1 (by rfl) ⟨157562, by rfl⟩ : syracuseStep 210083 = 315125) B315125
theorem B210099 : Blo 207808 210099 := bstep (se 1 (by rfl) ⟨157574, by rfl⟩ : syracuseStep 210099 = 315149) B315149
theorem B210115 : Blo 207808 210115 := bstep (se 1 (by rfl) ⟨157586, by rfl⟩ : syracuseStep 210115 = 315173) B315173
theorem B2700485 : Blo 207808 2700485 := bstep (se 4 (by rfl) ⟨253170, by rfl⟩ : syracuseStep 2700485 = 506341) B506341
theorem B210131 : Blo 207808 210131 := bstep (se 1 (by rfl) ⟨157598, by rfl⟩ : syracuseStep 210131 = 315197) B315197
theorem B210147 : Blo 207808 210147 := bstep (se 1 (by rfl) ⟨157610, by rfl⟩ : syracuseStep 210147 = 315221) B315221
theorem B210163 : Blo 207808 210163 := bstep (se 1 (by rfl) ⟨157622, by rfl⟩ : syracuseStep 210163 = 315245) B315245
theorem B210179 : Blo 207808 210179 := bstep (se 1 (by rfl) ⟨157634, by rfl⟩ : syracuseStep 210179 = 315269) B315269
theorem B472337 : Blo 207808 472337 := bstep (se 2 (by rfl) ⟨177126, by rfl⟩ : syracuseStep 472337 = 354253) B354253
theorem B210195 : Blo 207808 210195 := bstep (se 1 (by rfl) ⟨157646, by rfl⟩ : syracuseStep 210195 = 315293) B315293
theorem B472355 : Blo 207808 472355 := bstep (se 1 (by rfl) ⟨354266, by rfl⟩ : syracuseStep 472355 = 708533) B708533
theorem B210211 : Blo 207808 210211 := bstep (se 1 (by rfl) ⟨157658, by rfl⟩ : syracuseStep 210211 = 315317) B315317
theorem B210227 : Blo 207808 210227 := bstep (se 1 (by rfl) ⟨157670, by rfl⟩ : syracuseStep 210227 = 315341) B315341
theorem B210243 : Blo 207808 210243 := bstep (se 1 (by rfl) ⟨157682, by rfl⟩ : syracuseStep 210243 = 315365) B315365
theorem B800077 : Blo 207808 800077 := bstep (se 3 (by rfl) ⟨150014, by rfl⟩ : syracuseStep 800077 = 300029) B300029
theorem B210259 : Blo 207808 210259 := bstep (se 1 (by rfl) ⟨157694, by rfl⟩ : syracuseStep 210259 = 315389) B315389
theorem B210275 : Blo 207808 210275 := bstep (se 1 (by rfl) ⟨157706, by rfl⟩ : syracuseStep 210275 = 315413) B315413
theorem B4502897 : Blo 207808 4502897 := bstep (se 2 (by rfl) ⟨1688586, by rfl⟩ : syracuseStep 4502897 = 3377173) B3377173
theorem B210291 : Blo 207808 210291 := bstep (se 1 (by rfl) ⟨157718, by rfl⟩ : syracuseStep 210291 = 315437) B315437
theorem B210307 : Blo 207808 210307 := bstep (se 1 (by rfl) ⟨157730, by rfl⟩ : syracuseStep 210307 = 315461) B315461
theorem B701837 : Blo 207808 701837 := bstep (se 3 (by rfl) ⟨131594, by rfl⟩ : syracuseStep 701837 = 263189) B263189
theorem B210323 : Blo 207808 210323 := bstep (se 1 (by rfl) ⟨157742, by rfl⟩ : syracuseStep 210323 = 315485) B315485
theorem B210339 : Blo 207808 210339 := bstep (se 1 (by rfl) ⟨157754, by rfl⟩ : syracuseStep 210339 = 315509) B315509
theorem B210355 : Blo 207808 210355 := bstep (se 1 (by rfl) ⟨157766, by rfl⟩ : syracuseStep 210355 = 315533) B315533
theorem B701891 : Blo 207808 701891 := bstep (se 1 (by rfl) ⟨526418, by rfl⟩ : syracuseStep 701891 = 1052837) B1052837
theorem B210371 : Blo 207808 210371 := bstep (se 1 (by rfl) ⟨157778, by rfl⟩ : syracuseStep 210371 = 315557) B315557
theorem B210387 : Blo 207808 210387 := bstep (se 1 (by rfl) ⟨157790, by rfl⟩ : syracuseStep 210387 = 315581) B315581
theorem B210403 : Blo 207808 210403 := bstep (se 1 (by rfl) ⟨157802, by rfl⟩ : syracuseStep 210403 = 315605) B315605
theorem B210419 : Blo 207808 210419 := bstep (se 1 (by rfl) ⟨157814, by rfl⟩ : syracuseStep 210419 = 315629) B315629
theorem B210435 : Blo 207808 210435 := bstep (se 1 (by rfl) ⟨157826, by rfl⟩ : syracuseStep 210435 = 315653) B315653
theorem B210451 : Blo 207808 210451 := bstep (se 1 (by rfl) ⟨157838, by rfl⟩ : syracuseStep 210451 = 315677) B315677
theorem B210467 : Blo 207808 210467 := bstep (se 1 (by rfl) ⟨157850, by rfl⟩ : syracuseStep 210467 = 315701) B315701
theorem B472625 : Blo 207808 472625 := bstep (se 2 (by rfl) ⟨177234, by rfl⟩ : syracuseStep 472625 = 354469) B354469
theorem B210483 : Blo 207808 210483 := bstep (se 1 (by rfl) ⟨157862, by rfl⟩ : syracuseStep 210483 = 315725) B315725
theorem B472643 : Blo 207808 472643 := bstep (se 1 (by rfl) ⟨354482, by rfl⟩ : syracuseStep 472643 = 708965) B708965
theorem B210499 : Blo 207808 210499 := bstep (se 1 (by rfl) ⟨157874, by rfl⟩ : syracuseStep 210499 = 315749) B315749
theorem B1422917 : Blo 207808 1422917 := bstep (se 4 (by rfl) ⟨133398, by rfl⟩ : syracuseStep 1422917 = 266797) B266797
theorem B210515 : Blo 207808 210515 := bstep (se 1 (by rfl) ⟨157886, by rfl⟩ : syracuseStep 210515 = 315773) B315773
theorem B210531 : Blo 207808 210531 := bstep (se 1 (by rfl) ⟨157898, by rfl⟩ : syracuseStep 210531 = 315797) B315797
theorem B210547 : Blo 207808 210547 := bstep (se 1 (by rfl) ⟨157910, by rfl⟩ : syracuseStep 210547 = 315821) B315821
theorem B210563 : Blo 207808 210563 := bstep (se 1 (by rfl) ⟨157922, by rfl⟩ : syracuseStep 210563 = 315845) B315845
theorem B964237 : Blo 207808 964237 := bstep (se 3 (by rfl) ⟨180794, by rfl⟩ : syracuseStep 964237 = 361589) B361589
theorem B669325 : Blo 207808 669325 := bstep (se 3 (by rfl) ⟨125498, by rfl⟩ : syracuseStep 669325 = 250997) B250997
theorem B210579 : Blo 207808 210579 := bstep (se 1 (by rfl) ⟨157934, by rfl⟩ : syracuseStep 210579 = 315869) B315869
theorem B210595 : Blo 207808 210595 := bstep (se 1 (by rfl) ⟨157946, by rfl⟩ : syracuseStep 210595 = 315893) B315893
theorem B210611 : Blo 207808 210611 := bstep (se 1 (by rfl) ⟨157958, by rfl⟩ : syracuseStep 210611 = 315917) B315917
theorem B210627 : Blo 207808 210627 := bstep (se 1 (by rfl) ⟨157970, by rfl⟩ : syracuseStep 210627 = 315941) B315941
theorem B702161 : Blo 207808 702161 := bstep (se 2 (by rfl) ⟨263310, by rfl⟩ : syracuseStep 702161 = 526621) B526621
theorem B210643 : Blo 207808 210643 := bstep (se 1 (by rfl) ⟨157982, by rfl⟩ : syracuseStep 210643 = 315965) B315965
theorem B210659 : Blo 207808 210659 := bstep (se 1 (by rfl) ⟨157994, by rfl⟩ : syracuseStep 210659 = 315989) B315989
theorem B210675 : Blo 207808 210675 := bstep (se 1 (by rfl) ⟨158006, by rfl⟩ : syracuseStep 210675 = 316013) B316013
theorem B210691 : Blo 207808 210691 := bstep (se 1 (by rfl) ⟨158018, by rfl⟩ : syracuseStep 210691 = 316037) B316037
theorem B210707 : Blo 207808 210707 := bstep (se 1 (by rfl) ⟨158030, by rfl⟩ : syracuseStep 210707 = 316061) B316061
theorem B210723 : Blo 207808 210723 := bstep (se 1 (by rfl) ⟨158042, by rfl⟩ : syracuseStep 210723 = 316085) B316085
theorem B210739 : Blo 207808 210739 := bstep (se 1 (by rfl) ⟨158054, by rfl⟩ : syracuseStep 210739 = 316109) B316109
theorem B210755 : Blo 207808 210755 := bstep (se 1 (by rfl) ⟨158066, by rfl⟩ : syracuseStep 210755 = 316133) B316133
theorem B472913 : Blo 207808 472913 := bstep (se 2 (by rfl) ⟨177342, by rfl⟩ : syracuseStep 472913 = 354685) B354685
theorem B210771 : Blo 207808 210771 := bstep (se 1 (by rfl) ⟨158078, by rfl⟩ : syracuseStep 210771 = 316157) B316157
theorem B472931 : Blo 207808 472931 := bstep (se 1 (by rfl) ⟨354698, by rfl⟩ : syracuseStep 472931 = 709397) B709397
theorem B210787 : Blo 207808 210787 := bstep (se 1 (by rfl) ⟨158090, by rfl⟩ : syracuseStep 210787 = 316181) B316181
theorem B210803 : Blo 207808 210803 := bstep (se 1 (by rfl) ⟨158102, by rfl⟩ : syracuseStep 210803 = 316205) B316205
theorem B210819 : Blo 207808 210819 := bstep (se 1 (by rfl) ⟨158114, by rfl⟩ : syracuseStep 210819 = 316229) B316229
theorem B210835 : Blo 207808 210835 := bstep (se 1 (by rfl) ⟨158126, by rfl⟩ : syracuseStep 210835 = 316253) B316253
theorem B210851 : Blo 207808 210851 := bstep (se 1 (by rfl) ⟨158138, by rfl⟩ : syracuseStep 210851 = 316277) B316277
theorem B571313 : Blo 207808 571313 := bstep (se 2 (by rfl) ⟨214242, by rfl⟩ : syracuseStep 571313 = 428485) B428485
theorem B210867 : Blo 207808 210867 := bstep (se 1 (by rfl) ⟨158150, by rfl⟩ : syracuseStep 210867 = 316301) B316301
theorem B210883 : Blo 207808 210883 := bstep (se 1 (by rfl) ⟨158162, by rfl⟩ : syracuseStep 210883 = 316325) B316325
theorem B210899 : Blo 207808 210899 := bstep (se 1 (by rfl) ⟨158174, by rfl⟩ : syracuseStep 210899 = 316349) B316349
theorem B210915 : Blo 207808 210915 := bstep (se 1 (by rfl) ⟨158186, by rfl⟩ : syracuseStep 210915 = 316373) B316373
theorem B210931 : Blo 207808 210931 := bstep (se 1 (by rfl) ⟨158198, by rfl⟩ : syracuseStep 210931 = 316397) B316397
theorem B210947 : Blo 207808 210947 := bstep (se 1 (by rfl) ⟨158210, by rfl⟩ : syracuseStep 210947 = 316421) B316421
theorem B210963 : Blo 207808 210963 := bstep (se 1 (by rfl) ⟨158222, by rfl⟩ : syracuseStep 210963 = 316445) B316445
theorem B210979 : Blo 207808 210979 := bstep (se 1 (by rfl) ⟨158234, by rfl⟩ : syracuseStep 210979 = 316469) B316469
theorem B210995 : Blo 207808 210995 := bstep (se 1 (by rfl) ⟨158246, by rfl⟩ : syracuseStep 210995 = 316493) B316493
theorem B211011 : Blo 207808 211011 := bstep (se 1 (by rfl) ⟨158258, by rfl⟩ : syracuseStep 211011 = 316517) B316517
theorem B211027 : Blo 207808 211027 := bstep (se 1 (by rfl) ⟨158270, by rfl⟩ : syracuseStep 211027 = 316541) B316541
theorem B800867 : Blo 207808 800867 := bstep (se 1 (by rfl) ⟨600650, by rfl⟩ : syracuseStep 800867 = 1201301) B1201301
theorem B211043 : Blo 207808 211043 := bstep (se 1 (by rfl) ⟨158282, by rfl⟩ : syracuseStep 211043 = 316565) B316565
theorem B473201 : Blo 207808 473201 := bstep (se 2 (by rfl) ⟨177450, by rfl⟩ : syracuseStep 473201 = 354901) B354901
theorem B211059 : Blo 207808 211059 := bstep (se 1 (by rfl) ⟨158294, by rfl⟩ : syracuseStep 211059 = 316589) B316589
theorem B473219 : Blo 207808 473219 := bstep (se 1 (by rfl) ⟨354914, by rfl⟩ : syracuseStep 473219 = 709829) B709829
theorem B211075 : Blo 207808 211075 := bstep (se 1 (by rfl) ⟨158306, by rfl⟩ : syracuseStep 211075 = 316613) B316613
theorem B211091 : Blo 207808 211091 := bstep (se 1 (by rfl) ⟨158318, by rfl⟩ : syracuseStep 211091 = 316637) B316637
theorem B211107 : Blo 207808 211107 := bstep (se 1 (by rfl) ⟨158330, by rfl⟩ : syracuseStep 211107 = 316661) B316661
theorem B211123 : Blo 207808 211123 := bstep (se 1 (by rfl) ⟨158342, by rfl⟩ : syracuseStep 211123 = 316685) B316685
theorem B211139 : Blo 207808 211139 := bstep (se 1 (by rfl) ⟨158354, by rfl⟩ : syracuseStep 211139 = 316709) B316709
theorem B211155 : Blo 207808 211155 := bstep (se 1 (by rfl) ⟨158366, by rfl⟩ : syracuseStep 211155 = 316733) B316733
theorem B211171 : Blo 207808 211171 := bstep (se 1 (by rfl) ⟨158378, by rfl⟩ : syracuseStep 211171 = 316757) B316757
theorem B702701 : Blo 207808 702701 := bstep (se 3 (by rfl) ⟨131756, by rfl⟩ : syracuseStep 702701 = 263513) B263513
theorem B1423601 : Blo 207808 1423601 := bstep (se 2 (by rfl) ⟨533850, by rfl⟩ : syracuseStep 1423601 = 1067701) B1067701
theorem B211187 : Blo 207808 211187 := bstep (se 1 (by rfl) ⟨158390, by rfl⟩ : syracuseStep 211187 = 316781) B316781
theorem B211203 : Blo 207808 211203 := bstep (se 1 (by rfl) ⟨158402, by rfl⟩ : syracuseStep 211203 = 316805) B316805
theorem B571661 : Blo 207808 571661 := bstep (se 3 (by rfl) ⟨107186, by rfl⟩ : syracuseStep 571661 = 214373) B214373
theorem B211219 : Blo 207808 211219 := bstep (se 1 (by rfl) ⟨158414, by rfl⟩ : syracuseStep 211219 = 316829) B316829
theorem B702755 : Blo 207808 702755 := bstep (se 1 (by rfl) ⟨527066, by rfl⟩ : syracuseStep 702755 = 1054133) B1054133
theorem B211235 : Blo 207808 211235 := bstep (se 1 (by rfl) ⟨158426, by rfl⟩ : syracuseStep 211235 = 316853) B316853
theorem B211251 : Blo 207808 211251 := bstep (se 1 (by rfl) ⟨158438, by rfl⟩ : syracuseStep 211251 = 316877) B316877
theorem B211267 : Blo 207808 211267 := bstep (se 1 (by rfl) ⟨158450, by rfl⟩ : syracuseStep 211267 = 316901) B316901
theorem B211283 : Blo 207808 211283 := bstep (se 1 (by rfl) ⟨158462, by rfl⟩ : syracuseStep 211283 = 316925) B316925
theorem B637283 : Blo 207808 637283 := bstep (se 1 (by rfl) ⟨477962, by rfl⟩ : syracuseStep 637283 = 955925) B955925
theorem B211299 : Blo 207808 211299 := bstep (se 1 (by rfl) ⟨158474, by rfl⟩ : syracuseStep 211299 = 316949) B316949
theorem B211315 : Blo 207808 211315 := bstep (se 1 (by rfl) ⟨158486, by rfl⟩ : syracuseStep 211315 = 316973) B316973
theorem B211331 : Blo 207808 211331 := bstep (se 1 (by rfl) ⟨158498, by rfl⟩ : syracuseStep 211331 = 316997) B316997
theorem B375185 : Blo 207808 375185 := bstep (se 2 (by rfl) ⟨140694, by rfl⟩ : syracuseStep 375185 = 281389) B281389
theorem B473489 : Blo 207808 473489 := bstep (se 2 (by rfl) ⟨177558, by rfl⟩ : syracuseStep 473489 = 355117) B355117
theorem B211347 : Blo 207808 211347 := bstep (se 1 (by rfl) ⟨158510, by rfl⟩ : syracuseStep 211347 = 317021) B317021
theorem B473507 : Blo 207808 473507 := bstep (se 1 (by rfl) ⟨355130, by rfl⟩ : syracuseStep 473507 = 710261) B710261
theorem B211363 : Blo 207808 211363 := bstep (se 1 (by rfl) ⟨158522, by rfl⟩ : syracuseStep 211363 = 317045) B317045
theorem B211379 : Blo 207808 211379 := bstep (se 1 (by rfl) ⟨158534, by rfl⟩ : syracuseStep 211379 = 317069) B317069
theorem B211395 : Blo 207808 211395 := bstep (se 1 (by rfl) ⟨158546, by rfl⟩ : syracuseStep 211395 = 317093) B317093
theorem B211411 : Blo 207808 211411 := bstep (se 1 (by rfl) ⟨158558, by rfl⟩ : syracuseStep 211411 = 317117) B317117
theorem B211427 : Blo 207808 211427 := bstep (se 1 (by rfl) ⟨158570, by rfl⟩ : syracuseStep 211427 = 317141) B317141
theorem B211443 : Blo 207808 211443 := bstep (se 1 (by rfl) ⟨158582, by rfl⟩ : syracuseStep 211443 = 317165) B317165
theorem B211459 : Blo 207808 211459 := bstep (se 1 (by rfl) ⟨158594, by rfl⟩ : syracuseStep 211459 = 317189) B317189
theorem B211475 : Blo 207808 211475 := bstep (se 1 (by rfl) ⟨158606, by rfl⟩ : syracuseStep 211475 = 317213) B317213
theorem B211491 : Blo 207808 211491 := bstep (se 1 (by rfl) ⟨158618, by rfl⟩ : syracuseStep 211491 = 317237) B317237
theorem B703025 : Blo 207808 703025 := bstep (se 2 (by rfl) ⟨263634, by rfl⟩ : syracuseStep 703025 = 527269) B527269
theorem B211507 : Blo 207808 211507 := bstep (se 1 (by rfl) ⟨158630, by rfl⟩ : syracuseStep 211507 = 317261) B317261
theorem B211523 : Blo 207808 211523 := bstep (se 1 (by rfl) ⟨158642, by rfl⟩ : syracuseStep 211523 = 317285) B317285
theorem B211539 : Blo 207808 211539 := bstep (se 1 (by rfl) ⟨158654, by rfl⟩ : syracuseStep 211539 = 317309) B317309
theorem B211555 : Blo 207808 211555 := bstep (se 1 (by rfl) ⟨158666, by rfl⟩ : syracuseStep 211555 = 317333) B317333
theorem B211571 : Blo 207808 211571 := bstep (se 1 (by rfl) ⟨158678, by rfl⟩ : syracuseStep 211571 = 317357) B317357
theorem B211587 : Blo 207808 211587 := bstep (se 1 (by rfl) ⟨158690, by rfl⟩ : syracuseStep 211587 = 317381) B317381
theorem B211603 : Blo 207808 211603 := bstep (se 1 (by rfl) ⟨158702, by rfl⟩ : syracuseStep 211603 = 317405) B317405
theorem B899747 : Blo 207808 899747 := bstep (se 1 (by rfl) ⟨674810, by rfl⟩ : syracuseStep 899747 = 1349621) B1349621
theorem B211619 : Blo 207808 211619 := bstep (se 1 (by rfl) ⟨158714, by rfl⟩ : syracuseStep 211619 = 317429) B317429
theorem B473777 : Blo 207808 473777 := bstep (se 2 (by rfl) ⟨177666, by rfl⟩ : syracuseStep 473777 = 355333) B355333
theorem B211635 : Blo 207808 211635 := bstep (se 1 (by rfl) ⟨158726, by rfl⟩ : syracuseStep 211635 = 317453) B317453
theorem B473795 : Blo 207808 473795 := bstep (se 1 (by rfl) ⟨355346, by rfl⟩ : syracuseStep 473795 = 710693) B710693
theorem B211651 : Blo 207808 211651 := bstep (se 1 (by rfl) ⟨158738, by rfl⟩ : syracuseStep 211651 = 317477) B317477
theorem B211667 : Blo 207808 211667 := bstep (se 1 (by rfl) ⟨158750, by rfl⟩ : syracuseStep 211667 = 317501) B317501
theorem B211683 : Blo 207808 211683 := bstep (se 1 (by rfl) ⟨158762, by rfl⟩ : syracuseStep 211683 = 317525) B317525
theorem B801521 : Blo 207808 801521 := bstep (se 2 (by rfl) ⟨300570, by rfl⟩ : syracuseStep 801521 = 601141) B601141
theorem B211699 : Blo 207808 211699 := bstep (se 1 (by rfl) ⟨158774, by rfl⟩ : syracuseStep 211699 = 317549) B317549
theorem B211715 : Blo 207808 211715 := bstep (se 1 (by rfl) ⟨158786, by rfl⟩ : syracuseStep 211715 = 317573) B317573
theorem B211731 : Blo 207808 211731 := bstep (se 1 (by rfl) ⟨158798, by rfl⟩ : syracuseStep 211731 = 317597) B317597
theorem B211747 : Blo 207808 211747 := bstep (se 1 (by rfl) ⟨158810, by rfl⟩ : syracuseStep 211747 = 317621) B317621
theorem B211763 : Blo 207808 211763 := bstep (se 1 (by rfl) ⟨158822, by rfl⟩ : syracuseStep 211763 = 317645) B317645
theorem B211779 : Blo 207808 211779 := bstep (se 1 (by rfl) ⟨158834, by rfl⟩ : syracuseStep 211779 = 317669) B317669
theorem B211795 : Blo 207808 211795 := bstep (se 1 (by rfl) ⟨158846, by rfl⟩ : syracuseStep 211795 = 317693) B317693
theorem B474065 : Blo 207808 474065 := bstep (se 2 (by rfl) ⟨177774, by rfl⟩ : syracuseStep 474065 = 355549) B355549
theorem B474083 : Blo 207808 474083 := bstep (se 1 (by rfl) ⟨355562, by rfl⟩ : syracuseStep 474083 = 711125) B711125
theorem B1195013 : Blo 207808 1195013 := bstep (se 4 (by rfl) ⟨112032, by rfl⟩ : syracuseStep 1195013 = 224065) B224065
theorem B506915 : Blo 207808 506915 := bstep (se 1 (by rfl) ⟨380186, by rfl⟩ : syracuseStep 506915 = 760373) B760373
theorem B670787 : Blo 207808 670787 := bstep (se 1 (by rfl) ⟨503090, by rfl⟩ : syracuseStep 670787 = 1006181) B1006181
theorem B703565 : Blo 207808 703565 := bstep (se 3 (by rfl) ⟨131918, by rfl⟩ : syracuseStep 703565 = 263837) B263837
theorem B703619 : Blo 207808 703619 := bstep (se 1 (by rfl) ⟨527714, by rfl⟩ : syracuseStep 703619 = 1055429) B1055429
theorem B507107 : Blo 207808 507107 := bstep (se 1 (by rfl) ⟨380330, by rfl⟩ : syracuseStep 507107 = 760661) B760661
theorem B1064177 : Blo 207808 1064177 := bstep (se 2 (by rfl) ⟨399066, by rfl⟩ : syracuseStep 1064177 = 798133) B798133
theorem B474353 : Blo 207808 474353 := bstep (se 2 (by rfl) ⟨177882, by rfl⟩ : syracuseStep 474353 = 355765) B355765
theorem B474371 : Blo 207808 474371 := bstep (se 1 (by rfl) ⟨355778, by rfl⟩ : syracuseStep 474371 = 711557) B711557
theorem B703889 : Blo 207808 703889 := bstep (se 2 (by rfl) ⟨263958, by rfl⟩ : syracuseStep 703889 = 527917) B527917
theorem B540049 : Blo 207808 540049 := bstep (se 2 (by rfl) ⟨202518, by rfl⟩ : syracuseStep 540049 = 405037) B405037
theorem B703907 : Blo 207808 703907 := bstep (se 1 (by rfl) ⟨527930, by rfl⟩ : syracuseStep 703907 = 1055861) B1055861
theorem B1195469 : Blo 207808 1195469 := bstep (se 3 (by rfl) ⟨224150, by rfl⟩ : syracuseStep 1195469 = 448301) B448301
theorem B507377 : Blo 207808 507377 := bstep (se 2 (by rfl) ⟨190266, by rfl⟩ : syracuseStep 507377 = 380533) B380533
theorem B474641 : Blo 207808 474641 := bstep (se 2 (by rfl) ⟨177990, by rfl⟩ : syracuseStep 474641 = 355981) B355981
theorem B474659 : Blo 207808 474659 := bstep (se 1 (by rfl) ⟨355994, by rfl⟩ : syracuseStep 474659 = 711989) B711989
theorem B474929 : Blo 207808 474929 := bstep (se 2 (by rfl) ⟨178098, by rfl⟩ : syracuseStep 474929 = 356197) B356197
theorem B474947 : Blo 207808 474947 := bstep (se 1 (by rfl) ⟨356210, by rfl⟩ : syracuseStep 474947 = 712421) B712421
theorem B507761 : Blo 207808 507761 := bstep (se 2 (by rfl) ⟨190410, by rfl⟩ : syracuseStep 507761 = 380821) B380821
theorem B704429 : Blo 207808 704429 := bstep (se 3 (by rfl) ⟨132080, by rfl⟩ : syracuseStep 704429 = 264161) B264161
theorem B704483 : Blo 207808 704483 := bstep (se 1 (by rfl) ⟨528362, by rfl⟩ : syracuseStep 704483 = 1056725) B1056725
theorem B1589219 : Blo 207808 1589219 := bstep (se 1 (by rfl) ⟨1191914, by rfl⟩ : syracuseStep 1589219 = 2383829) B2383829
theorem B2572273 : Blo 207808 2572273 := bstep (se 2 (by rfl) ⟨964602, by rfl⟩ : syracuseStep 2572273 = 1929205) B1929205
theorem B475217 : Blo 207808 475217 := bstep (se 2 (by rfl) ⟨178206, by rfl⟩ : syracuseStep 475217 = 356413) B356413
theorem B475235 : Blo 207808 475235 := bstep (se 1 (by rfl) ⟨356426, by rfl⟩ : syracuseStep 475235 = 712853) B712853
theorem B802979 : Blo 207808 802979 := bstep (se 1 (by rfl) ⟨602234, by rfl⟩ : syracuseStep 802979 = 1204469) B1204469
theorem B802993 : Blo 207808 802993 := bstep (se 2 (by rfl) ⟨301122, by rfl⟩ : syracuseStep 802993 = 602245) B602245
theorem B999665 : Blo 207808 999665 := bstep (se 2 (by rfl) ⟨374874, by rfl⟩ : syracuseStep 999665 = 749749) B749749
theorem B704753 : Blo 207808 704753 := bstep (se 2 (by rfl) ⟨264282, by rfl⟩ : syracuseStep 704753 = 528565) B528565
theorem B901489 : Blo 207808 901489 := bstep (se 2 (by rfl) ⟨338058, by rfl⟩ : syracuseStep 901489 = 676117) B676117
theorem B475505 : Blo 207808 475505 := bstep (se 2 (by rfl) ⟨178314, by rfl⟩ : syracuseStep 475505 = 356629) B356629
theorem B475523 : Blo 207808 475523 := bstep (se 1 (by rfl) ⟨356642, by rfl⟩ : syracuseStep 475523 = 713285) B713285
theorem B311729 : Blo 207808 311729 := bstep (se 2 (by rfl) ⟨116898, by rfl⟩ : syracuseStep 311729 = 233797) B233797
theorem B311747 : Blo 207808 311747 := bstep (se 1 (by rfl) ⟨233810, by rfl⟩ : syracuseStep 311747 = 467621) B467621
theorem B508369 : Blo 207808 508369 := bstep (se 2 (by rfl) ⟨190638, by rfl⟩ : syracuseStep 508369 = 381277) B381277
theorem B311777 : Blo 207808 311777 := bstep (se 2 (by rfl) ⟨116916, by rfl⟩ : syracuseStep 311777 = 233833) B233833
theorem B311795 : Blo 207808 311795 := bstep (se 1 (by rfl) ⟨233846, by rfl⟩ : syracuseStep 311795 = 467693) B467693
theorem B311825 : Blo 207808 311825 := bstep (se 2 (by rfl) ⟨116934, by rfl⟩ : syracuseStep 311825 = 233869) B233869
theorem B311843 : Blo 207808 311843 := bstep (se 1 (by rfl) ⟨233882, by rfl⟩ : syracuseStep 311843 = 467765) B467765
theorem B311873 : Blo 207808 311873 := bstep (se 2 (by rfl) ⟨116952, by rfl⟩ : syracuseStep 311873 = 233905) B233905
theorem B311891 : Blo 207808 311891 := bstep (se 1 (by rfl) ⟨233918, by rfl⟩ : syracuseStep 311891 = 467837) B467837
theorem B311921 : Blo 207808 311921 := bstep (se 2 (by rfl) ⟨116970, by rfl⟩ : syracuseStep 311921 = 233941) B233941
theorem B508529 : Blo 207808 508529 := bstep (se 2 (by rfl) ⟨190698, by rfl⟩ : syracuseStep 508529 = 381397) B381397
theorem B311939 : Blo 207808 311939 := bstep (se 1 (by rfl) ⟨233954, by rfl⟩ : syracuseStep 311939 = 467909) B467909
theorem B672401 : Blo 207808 672401 := bstep (se 2 (by rfl) ⟨252150, by rfl⟩ : syracuseStep 672401 = 504301) B504301
theorem B475793 : Blo 207808 475793 := bstep (se 2 (by rfl) ⟨178422, by rfl⟩ : syracuseStep 475793 = 356845) B356845
theorem B311969 : Blo 207808 311969 := bstep (se 2 (by rfl) ⟨116988, by rfl⟩ : syracuseStep 311969 = 233977) B233977
theorem B1065635 : Blo 207808 1065635 := bstep (se 1 (by rfl) ⟨799226, by rfl⟩ : syracuseStep 1065635 = 1598453) B1598453
theorem B475811 : Blo 207808 475811 := bstep (se 1 (by rfl) ⟨356858, by rfl⟩ : syracuseStep 475811 = 713717) B713717
theorem B311987 : Blo 207808 311987 := bstep (se 1 (by rfl) ⟨233990, by rfl⟩ : syracuseStep 311987 = 467981) B467981
theorem B312017 : Blo 207808 312017 := bstep (se 2 (by rfl) ⟨117006, by rfl⟩ : syracuseStep 312017 = 234013) B234013
theorem B312035 : Blo 207808 312035 := bstep (se 1 (by rfl) ⟨234026, by rfl⟩ : syracuseStep 312035 = 468053) B468053
theorem B312065 : Blo 207808 312065 := bstep (se 2 (by rfl) ⟨117024, by rfl⟩ : syracuseStep 312065 = 234049) B234049
theorem B508675 : Blo 207808 508675 := bstep (se 1 (by rfl) ⟨381506, by rfl⟩ : syracuseStep 508675 = 763013) B763013
theorem B705293 : Blo 207808 705293 := bstep (se 3 (by rfl) ⟨132242, by rfl⟩ : syracuseStep 705293 = 264485) B264485
theorem B312083 : Blo 207808 312083 := bstep (se 1 (by rfl) ⟨234062, by rfl⟩ : syracuseStep 312083 = 468125) B468125
theorem B312113 : Blo 207808 312113 := bstep (se 2 (by rfl) ⟨117042, by rfl⟩ : syracuseStep 312113 = 234085) B234085
theorem B312131 : Blo 207808 312131 := bstep (se 1 (by rfl) ⟨234098, by rfl⟩ : syracuseStep 312131 = 468197) B468197
theorem B705347 : Blo 207808 705347 := bstep (se 1 (by rfl) ⟨529010, by rfl⟩ : syracuseStep 705347 = 1058021) B1058021
theorem B312161 : Blo 207808 312161 := bstep (se 2 (by rfl) ⟨117060, by rfl⟩ : syracuseStep 312161 = 234121) B234121
theorem B1622897 : Blo 207808 1622897 := bstep (se 2 (by rfl) ⟨608586, by rfl⟩ : syracuseStep 1622897 = 1217173) B1217173
theorem B312179 : Blo 207808 312179 := bstep (se 1 (by rfl) ⟨234134, by rfl⟩ : syracuseStep 312179 = 468269) B468269
theorem B312209 : Blo 207808 312209 := bstep (se 2 (by rfl) ⟨117078, by rfl⟩ : syracuseStep 312209 = 234157) B234157
theorem B312227 : Blo 207808 312227 := bstep (se 1 (by rfl) ⟨234170, by rfl⟩ : syracuseStep 312227 = 468341) B468341
theorem B476081 : Blo 207808 476081 := bstep (se 2 (by rfl) ⟨178530, by rfl⟩ : syracuseStep 476081 = 357061) B357061
theorem B312257 : Blo 207808 312257 := bstep (se 2 (by rfl) ⟨117096, by rfl⟩ : syracuseStep 312257 = 234193) B234193
theorem B476099 : Blo 207808 476099 := bstep (se 1 (by rfl) ⟨357074, by rfl⟩ : syracuseStep 476099 = 714149) B714149
theorem B312275 : Blo 207808 312275 := bstep (se 1 (by rfl) ⟨234206, by rfl⟩ : syracuseStep 312275 = 468413) B468413
theorem B312305 : Blo 207808 312305 := bstep (se 2 (by rfl) ⟨117114, by rfl⟩ : syracuseStep 312305 = 234229) B234229
theorem B312323 : Blo 207808 312323 := bstep (se 1 (by rfl) ⟨234242, by rfl⟩ : syracuseStep 312323 = 468485) B468485
theorem B377873 : Blo 207808 377873 := bstep (se 2 (by rfl) ⟨141702, by rfl⟩ : syracuseStep 377873 = 283405) B283405
theorem B312353 : Blo 207808 312353 := bstep (se 2 (by rfl) ⟨117132, by rfl⟩ : syracuseStep 312353 = 234265) B234265
theorem B312371 : Blo 207808 312371 := bstep (se 1 (by rfl) ⟨234278, by rfl⟩ : syracuseStep 312371 = 468557) B468557
theorem B312401 : Blo 207808 312401 := bstep (se 2 (by rfl) ⟨117150, by rfl⟩ : syracuseStep 312401 = 234301) B234301
theorem B705617 : Blo 207808 705617 := bstep (se 2 (by rfl) ⟨264606, by rfl⟩ : syracuseStep 705617 = 529213) B529213
theorem B312419 : Blo 207808 312419 := bstep (se 1 (by rfl) ⟨234314, by rfl⟩ : syracuseStep 312419 = 468629) B468629
theorem B312449 : Blo 207808 312449 := bstep (se 2 (by rfl) ⟨117168, by rfl⟩ : syracuseStep 312449 = 234337) B234337
theorem B214147 : Blo 207808 214147 := bstep (se 1 (by rfl) ⟨160610, by rfl⟩ : syracuseStep 214147 = 321221) B321221
theorem B1787021 : Blo 207808 1787021 := bstep (se 3 (by rfl) ⟨335066, by rfl⟩ : syracuseStep 1787021 = 670133) B670133
theorem B312467 : Blo 207808 312467 := bstep (se 1 (by rfl) ⟨234350, by rfl⟩ : syracuseStep 312467 = 468701) B468701
theorem B312497 : Blo 207808 312497 := bstep (se 2 (by rfl) ⟨117186, by rfl⟩ : syracuseStep 312497 = 234373) B234373
theorem B2802869 : Blo 207808 2802869 := bstep (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) B262769
theorem B312515 : Blo 207808 312515 := bstep (se 1 (by rfl) ⟨234386, by rfl⟩ : syracuseStep 312515 = 468773) B468773
theorem B3032261 : Blo 207808 3032261 := bstep (se 4 (by rfl) ⟨284274, by rfl⟩ : syracuseStep 3032261 = 568549) B568549
theorem B476369 : Blo 207808 476369 := bstep (se 2 (by rfl) ⟨178638, by rfl⟩ : syracuseStep 476369 = 357277) B357277
theorem B312545 : Blo 207808 312545 := bstep (se 2 (by rfl) ⟨117204, by rfl⟩ : syracuseStep 312545 = 234409) B234409
theorem B476387 : Blo 207808 476387 := bstep (se 1 (by rfl) ⟨357290, by rfl⟩ : syracuseStep 476387 = 714581) B714581
theorem B312563 : Blo 207808 312563 := bstep (se 1 (by rfl) ⟨234422, by rfl⟩ : syracuseStep 312563 = 468845) B468845
theorem B312593 : Blo 207808 312593 := bstep (se 2 (by rfl) ⟨117222, by rfl⟩ : syracuseStep 312593 = 234445) B234445
theorem B312611 : Blo 207808 312611 := bstep (se 1 (by rfl) ⟨234458, by rfl⟩ : syracuseStep 312611 = 468917) B468917
theorem B312641 : Blo 207808 312641 := bstep (se 2 (by rfl) ⟨117240, by rfl⟩ : syracuseStep 312641 = 234481) B234481
theorem B312659 : Blo 207808 312659 := bstep (se 1 (by rfl) ⟨234494, by rfl⟩ : syracuseStep 312659 = 468989) B468989
theorem B312689 : Blo 207808 312689 := bstep (se 2 (by rfl) ⟨117258, by rfl⟩ : syracuseStep 312689 = 234517) B234517
theorem B312707 : Blo 207808 312707 := bstep (se 1 (by rfl) ⟨234530, by rfl⟩ : syracuseStep 312707 = 469061) B469061
theorem B312737 : Blo 207808 312737 := bstep (se 2 (by rfl) ⟨117276, by rfl⟩ : syracuseStep 312737 = 234553) B234553
theorem B312755 : Blo 207808 312755 := bstep (se 1 (by rfl) ⟨234566, by rfl⟩ : syracuseStep 312755 = 469133) B469133
theorem B3851717 : Blo 207808 3851717 := bstep (se 4 (by rfl) ⟨361098, by rfl⟩ : syracuseStep 3851717 = 722197) B722197
theorem B1066445 : Blo 207808 1066445 := bstep (se 3 (by rfl) ⟨199958, by rfl⟩ : syracuseStep 1066445 = 399917) B399917
theorem B312785 : Blo 207808 312785 := bstep (se 2 (by rfl) ⟨117294, by rfl⟩ : syracuseStep 312785 = 234589) B234589
theorem B312803 : Blo 207808 312803 := bstep (se 1 (by rfl) ⟨234602, by rfl⟩ : syracuseStep 312803 = 469205) B469205
theorem B312833 : Blo 207808 312833 := bstep (se 2 (by rfl) ⟨117312, by rfl⟩ : syracuseStep 312833 = 234625) B234625
theorem B378371 : Blo 207808 378371 := bstep (se 1 (by rfl) ⟨283778, by rfl⟩ : syracuseStep 378371 = 567557) B567557
theorem B312851 : Blo 207808 312851 := bstep (se 1 (by rfl) ⟨234638, by rfl⟩ : syracuseStep 312851 = 469277) B469277
theorem B312881 : Blo 207808 312881 := bstep (se 2 (by rfl) ⟨117330, by rfl⟩ : syracuseStep 312881 = 234661) B234661
theorem B312899 : Blo 207808 312899 := bstep (se 1 (by rfl) ⟨234674, by rfl⟩ : syracuseStep 312899 = 469349) B469349
theorem B312929 : Blo 207808 312929 := bstep (se 2 (by rfl) ⟨117348, by rfl⟩ : syracuseStep 312929 = 234697) B234697
theorem B706157 : Blo 207808 706157 := bstep (se 3 (by rfl) ⟨132404, by rfl⟩ : syracuseStep 706157 = 264809) B264809
theorem B312947 : Blo 207808 312947 := bstep (se 1 (by rfl) ⟨234710, by rfl⟩ : syracuseStep 312947 = 469421) B469421
theorem B312977 : Blo 207808 312977 := bstep (se 2 (by rfl) ⟨117366, by rfl⟩ : syracuseStep 312977 = 234733) B234733
theorem B312995 : Blo 207808 312995 := bstep (se 1 (by rfl) ⟨234746, by rfl⟩ : syracuseStep 312995 = 469493) B469493
theorem B706211 : Blo 207808 706211 := bstep (se 1 (by rfl) ⟨529658, by rfl⟩ : syracuseStep 706211 = 1059317) B1059317
theorem B313025 : Blo 207808 313025 := bstep (se 2 (by rfl) ⟨117384, by rfl⟩ : syracuseStep 313025 = 234769) B234769
theorem B313043 : Blo 207808 313043 := bstep (se 1 (by rfl) ⟨234782, by rfl⟩ : syracuseStep 313043 = 469565) B469565
theorem B313073 : Blo 207808 313073 := bstep (se 2 (by rfl) ⟨117402, by rfl⟩ : syracuseStep 313073 = 234805) B234805
theorem B313091 : Blo 207808 313091 := bstep (se 1 (by rfl) ⟨234818, by rfl⟩ : syracuseStep 313091 = 469637) B469637
theorem B313121 : Blo 207808 313121 := bstep (se 2 (by rfl) ⟨117420, by rfl⟩ : syracuseStep 313121 = 234841) B234841
theorem B476977 : Blo 207808 476977 := bstep (se 2 (by rfl) ⟨178866, by rfl⟩ : syracuseStep 476977 = 357733) B357733
theorem B313139 : Blo 207808 313139 := bstep (se 1 (by rfl) ⟨234854, by rfl⟩ : syracuseStep 313139 = 469709) B469709
theorem B313169 : Blo 207808 313169 := bstep (se 2 (by rfl) ⟨117438, by rfl⟩ : syracuseStep 313169 = 234877) B234877
theorem B313187 : Blo 207808 313187 := bstep (se 1 (by rfl) ⟨234890, by rfl⟩ : syracuseStep 313187 = 469781) B469781
theorem B313217 : Blo 207808 313217 := bstep (se 2 (by rfl) ⟨117456, by rfl⟩ : syracuseStep 313217 = 234913) B234913
theorem B313235 : Blo 207808 313235 := bstep (se 1 (by rfl) ⟨234926, by rfl⟩ : syracuseStep 313235 = 469853) B469853
theorem B313265 : Blo 207808 313265 := bstep (se 2 (by rfl) ⟨117474, by rfl⟩ : syracuseStep 313265 = 234949) B234949
theorem B706481 : Blo 207808 706481 := bstep (se 2 (by rfl) ⟨264930, by rfl⟩ : syracuseStep 706481 = 529861) B529861
theorem B313283 : Blo 207808 313283 := bstep (se 1 (by rfl) ⟨234962, by rfl⟩ : syracuseStep 313283 = 469925) B469925
theorem B313313 : Blo 207808 313313 := bstep (se 2 (by rfl) ⟨117492, by rfl⟩ : syracuseStep 313313 = 234985) B234985
theorem B870385 : Blo 207808 870385 := bstep (se 2 (by rfl) ⟨326394, by rfl⟩ : syracuseStep 870385 = 652789) B652789
theorem B313331 : Blo 207808 313331 := bstep (se 1 (by rfl) ⟨234998, by rfl⟩ : syracuseStep 313331 = 469997) B469997
theorem B313361 : Blo 207808 313361 := bstep (se 2 (by rfl) ⟨117510, by rfl⟩ : syracuseStep 313361 = 235021) B235021
theorem B313379 : Blo 207808 313379 := bstep (se 1 (by rfl) ⟨235034, by rfl⟩ : syracuseStep 313379 = 470069) B470069
theorem B313409 : Blo 207808 313409 := bstep (se 2 (by rfl) ⟨117528, by rfl⟩ : syracuseStep 313409 = 235057) B235057
theorem B313427 : Blo 207808 313427 := bstep (se 1 (by rfl) ⟨235070, by rfl⟩ : syracuseStep 313427 = 470141) B470141
theorem B313457 : Blo 207808 313457 := bstep (se 2 (by rfl) ⟨117546, by rfl⟩ : syracuseStep 313457 = 235093) B235093
theorem B313475 : Blo 207808 313475 := bstep (se 1 (by rfl) ⟨235106, by rfl⟩ : syracuseStep 313475 = 470213) B470213
theorem B313505 : Blo 207808 313505 := bstep (se 2 (by rfl) ⟨117564, by rfl⟩ : syracuseStep 313505 = 235129) B235129
theorem B641201 : Blo 207808 641201 := bstep (se 2 (by rfl) ⟨240450, by rfl⟩ : syracuseStep 641201 = 480901) B480901
theorem B313523 : Blo 207808 313523 := bstep (se 1 (by rfl) ⟨235142, by rfl⟩ : syracuseStep 313523 = 470285) B470285
theorem B444611 : Blo 207808 444611 := bstep (se 1 (by rfl) ⟨333458, by rfl⟩ : syracuseStep 444611 = 666917) B666917
theorem B313553 : Blo 207808 313553 := bstep (se 2 (by rfl) ⟨117582, by rfl⟩ : syracuseStep 313553 = 235165) B235165
theorem B313571 : Blo 207808 313571 := bstep (se 1 (by rfl) ⟨235178, by rfl⟩ : syracuseStep 313571 = 470357) B470357
theorem B313601 : Blo 207808 313601 := bstep (se 2 (by rfl) ⟨117600, by rfl⟩ : syracuseStep 313601 = 235201) B235201
theorem B2377997 : Blo 207808 2377997 := bstep (se 3 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 2377997 = 891749) B891749
theorem B903437 : Blo 207808 903437 := bstep (se 3 (by rfl) ⟨169394, by rfl⟩ : syracuseStep 903437 = 338789) B338789
theorem B313619 : Blo 207808 313619 := bstep (se 1 (by rfl) ⟨235214, by rfl⟩ : syracuseStep 313619 = 470429) B470429
theorem B313649 : Blo 207808 313649 := bstep (se 2 (by rfl) ⟨117618, by rfl⟩ : syracuseStep 313649 = 235237) B235237
theorem B1198385 : Blo 207808 1198385 := bstep (se 2 (by rfl) ⟨449394, by rfl⟩ : syracuseStep 1198385 = 898789) B898789
theorem B313667 : Blo 207808 313667 := bstep (se 1 (by rfl) ⟨235250, by rfl⟩ : syracuseStep 313667 = 470501) B470501
theorem B313697 : Blo 207808 313697 := bstep (se 2 (by rfl) ⟨117636, by rfl⟩ : syracuseStep 313697 = 235273) B235273
theorem B313715 : Blo 207808 313715 := bstep (se 1 (by rfl) ⟨235286, by rfl⟩ : syracuseStep 313715 = 470573) B470573
theorem B313745 : Blo 207808 313745 := bstep (se 2 (by rfl) ⟨117654, by rfl⟩ : syracuseStep 313745 = 235309) B235309
theorem B313763 : Blo 207808 313763 := bstep (se 1 (by rfl) ⟨235322, by rfl⟩ : syracuseStep 313763 = 470645) B470645
theorem B313793 : Blo 207808 313793 := bstep (se 2 (by rfl) ⟨117672, by rfl⟩ : syracuseStep 313793 = 235345) B235345
theorem B707021 : Blo 207808 707021 := bstep (se 3 (by rfl) ⟨132566, by rfl⟩ : syracuseStep 707021 = 265133) B265133
theorem B313811 : Blo 207808 313811 := bstep (se 1 (by rfl) ⟨235358, by rfl⟩ : syracuseStep 313811 = 470717) B470717
theorem B313841 : Blo 207808 313841 := bstep (se 2 (by rfl) ⟨117690, by rfl⟩ : syracuseStep 313841 = 235381) B235381
theorem B313859 : Blo 207808 313859 := bstep (se 1 (by rfl) ⟨235394, by rfl⟩ : syracuseStep 313859 = 470789) B470789
theorem B707075 : Blo 207808 707075 := bstep (se 1 (by rfl) ⟨530306, by rfl⟩ : syracuseStep 707075 = 1060613) B1060613
theorem B313889 : Blo 207808 313889 := bstep (se 2 (by rfl) ⟨117708, by rfl⟩ : syracuseStep 313889 = 235417) B235417
theorem B313907 : Blo 207808 313907 := bstep (se 1 (by rfl) ⟨235430, by rfl⟩ : syracuseStep 313907 = 470861) B470861
theorem B313937 : Blo 207808 313937 := bstep (se 2 (by rfl) ⟨117726, by rfl⟩ : syracuseStep 313937 = 235453) B235453
theorem B313955 : Blo 207808 313955 := bstep (se 1 (by rfl) ⟨235466, by rfl⟩ : syracuseStep 313955 = 470933) B470933
theorem B477809 : Blo 207808 477809 := bstep (se 2 (by rfl) ⟨179178, by rfl⟩ : syracuseStep 477809 = 358357) B358357
theorem B313985 : Blo 207808 313985 := bstep (se 2 (by rfl) ⟨117744, by rfl⟩ : syracuseStep 313985 = 235489) B235489
theorem B1002125 : Blo 207808 1002125 := bstep (se 3 (by rfl) ⟨187898, by rfl⟩ : syracuseStep 1002125 = 375797) B375797
theorem B314003 : Blo 207808 314003 := bstep (se 1 (by rfl) ⟨235502, by rfl⟩ : syracuseStep 314003 = 471005) B471005
theorem B674477 : Blo 207808 674477 := bstep (se 3 (by rfl) ⟨126464, by rfl⟩ : syracuseStep 674477 = 252929) B252929
theorem B314033 : Blo 207808 314033 := bstep (se 2 (by rfl) ⟨117762, by rfl⟩ : syracuseStep 314033 = 235525) B235525
theorem B445123 : Blo 207808 445123 := bstep (se 1 (by rfl) ⟨333842, by rfl⟩ : syracuseStep 445123 = 667685) B667685
theorem B314051 : Blo 207808 314051 := bstep (se 1 (by rfl) ⟨235538, by rfl⟩ : syracuseStep 314051 = 471077) B471077
theorem B314081 : Blo 207808 314081 := bstep (se 2 (by rfl) ⟨117780, by rfl⟩ : syracuseStep 314081 = 235561) B235561
theorem B314099 : Blo 207808 314099 := bstep (se 1 (by rfl) ⟨235574, by rfl⟩ : syracuseStep 314099 = 471149) B471149
theorem B215795 : Blo 207808 215795 := bstep (se 1 (by rfl) ⟨161846, by rfl⟩ : syracuseStep 215795 = 323693) B323693
theorem B314129 : Blo 207808 314129 := bstep (se 2 (by rfl) ⟨117798, by rfl⟩ : syracuseStep 314129 = 235597) B235597
theorem B707345 : Blo 207808 707345 := bstep (se 2 (by rfl) ⟨265254, by rfl⟩ : syracuseStep 707345 = 530509) B530509
theorem B281377 : Blo 207808 281377 := bstep (se 2 (by rfl) ⟨105516, by rfl⟩ : syracuseStep 281377 = 211033) B211033
theorem B314147 : Blo 207808 314147 := bstep (se 1 (by rfl) ⟨235610, by rfl⟩ : syracuseStep 314147 = 471221) B471221
theorem B314177 : Blo 207808 314177 := bstep (se 2 (by rfl) ⟨117816, by rfl⟩ : syracuseStep 314177 = 235633) B235633
theorem B314195 : Blo 207808 314195 := bstep (se 1 (by rfl) ⟨235646, by rfl⟩ : syracuseStep 314195 = 471293) B471293
theorem B314225 : Blo 207808 314225 := bstep (se 2 (by rfl) ⟨117834, by rfl⟩ : syracuseStep 314225 = 235669) B235669
theorem B4049777 : Blo 207808 4049777 := bstep (se 2 (by rfl) ⟨1518666, by rfl⟩ : syracuseStep 4049777 = 3037333) B3037333
theorem B314243 : Blo 207808 314243 := bstep (se 1 (by rfl) ⟨235682, by rfl⟩ : syracuseStep 314243 = 471365) B471365
theorem B3591053 : Blo 207808 3591053 := bstep (se 3 (by rfl) ⟨673322, by rfl⟩ : syracuseStep 3591053 = 1346645) B1346645
theorem B314273 : Blo 207808 314273 := bstep (se 2 (by rfl) ⟨117852, by rfl⟩ : syracuseStep 314273 = 235705) B235705
theorem B314291 : Blo 207808 314291 := bstep (se 1 (by rfl) ⟨235718, by rfl⟩ : syracuseStep 314291 = 471437) B471437
theorem B314321 : Blo 207808 314321 := bstep (se 2 (by rfl) ⟨117870, by rfl⟩ : syracuseStep 314321 = 235741) B235741
theorem B314339 : Blo 207808 314339 := bstep (se 1 (by rfl) ⟨235754, by rfl⟩ : syracuseStep 314339 = 471509) B471509
theorem B314369 : Blo 207808 314369 := bstep (se 2 (by rfl) ⟨117888, by rfl⟩ : syracuseStep 314369 = 235777) B235777
theorem B314387 : Blo 207808 314387 := bstep (se 1 (by rfl) ⟨235790, by rfl⟩ : syracuseStep 314387 = 471581) B471581
theorem B314417 : Blo 207808 314417 := bstep (se 2 (by rfl) ⟨117906, by rfl⟩ : syracuseStep 314417 = 235813) B235813
theorem B314435 : Blo 207808 314435 := bstep (se 1 (by rfl) ⟨235826, by rfl⟩ : syracuseStep 314435 = 471653) B471653
theorem B314465 : Blo 207808 314465 := bstep (se 2 (by rfl) ⟨117924, by rfl⟩ : syracuseStep 314465 = 235849) B235849
theorem B314483 : Blo 207808 314483 := bstep (se 1 (by rfl) ⟨235862, by rfl⟩ : syracuseStep 314483 = 471725) B471725
theorem B1068173 : Blo 207808 1068173 := bstep (se 3 (by rfl) ⟨200282, by rfl⟩ : syracuseStep 1068173 = 400565) B400565
theorem B314513 : Blo 207808 314513 := bstep (se 2 (by rfl) ⟨117942, by rfl⟩ : syracuseStep 314513 = 235885) B235885
theorem B314531 : Blo 207808 314531 := bstep (se 1 (by rfl) ⟨235898, by rfl⟩ : syracuseStep 314531 = 471797) B471797
theorem B314561 : Blo 207808 314561 := bstep (se 2 (by rfl) ⟨117960, by rfl⟩ : syracuseStep 314561 = 235921) B235921
theorem B314579 : Blo 207808 314579 := bstep (se 1 (by rfl) ⟨235934, by rfl⟩ : syracuseStep 314579 = 471869) B471869
theorem B314609 : Blo 207808 314609 := bstep (se 2 (by rfl) ⟨117978, by rfl⟩ : syracuseStep 314609 = 235957) B235957
theorem B314627 : Blo 207808 314627 := bstep (se 1 (by rfl) ⟨235970, by rfl⟩ : syracuseStep 314627 = 471941) B471941
theorem B314657 : Blo 207808 314657 := bstep (se 2 (by rfl) ⟨117996, by rfl⟩ : syracuseStep 314657 = 235993) B235993
theorem B707885 : Blo 207808 707885 := bstep (se 3 (by rfl) ⟨132728, by rfl⟩ : syracuseStep 707885 = 265457) B265457
theorem B314675 : Blo 207808 314675 := bstep (se 1 (by rfl) ⟨236006, by rfl⟩ : syracuseStep 314675 = 472013) B472013
theorem B314705 : Blo 207808 314705 := bstep (se 2 (by rfl) ⟨118014, by rfl⟩ : syracuseStep 314705 = 236029) B236029
theorem B707939 : Blo 207808 707939 := bstep (se 1 (by rfl) ⟨530954, by rfl⟩ : syracuseStep 707939 = 1061909) B1061909
theorem B314723 : Blo 207808 314723 := bstep (se 1 (by rfl) ⟨236042, by rfl⟩ : syracuseStep 314723 = 472085) B472085
theorem B314753 : Blo 207808 314753 := bstep (se 2 (by rfl) ⟨118032, by rfl⟩ : syracuseStep 314753 = 236065) B236065
theorem B445841 : Blo 207808 445841 := bstep (se 2 (by rfl) ⟨167190, by rfl⟩ : syracuseStep 445841 = 334381) B334381
theorem B314771 : Blo 207808 314771 := bstep (se 1 (by rfl) ⟨236078, by rfl⟩ : syracuseStep 314771 = 472157) B472157
theorem B314801 : Blo 207808 314801 := bstep (se 2 (by rfl) ⟨118050, by rfl⟩ : syracuseStep 314801 = 236101) B236101
theorem B314819 : Blo 207808 314819 := bstep (se 1 (by rfl) ⟨236114, by rfl⟩ : syracuseStep 314819 = 472229) B472229
theorem B314849 : Blo 207808 314849 := bstep (se 2 (by rfl) ⟨118068, by rfl⟩ : syracuseStep 314849 = 236137) B236137
theorem B314867 : Blo 207808 314867 := bstep (se 1 (by rfl) ⟨236150, by rfl⟩ : syracuseStep 314867 = 472301) B472301
theorem B642563 : Blo 207808 642563 := bstep (se 1 (by rfl) ⟨481922, by rfl⟩ : syracuseStep 642563 = 963845) B963845
theorem B314897 : Blo 207808 314897 := bstep (se 2 (by rfl) ⟨118086, by rfl⟩ : syracuseStep 314897 = 236173) B236173
theorem B314915 : Blo 207808 314915 := bstep (se 1 (by rfl) ⟨236186, by rfl⟩ : syracuseStep 314915 = 472373) B472373
theorem B675373 : Blo 207808 675373 := bstep (se 3 (by rfl) ⟨126632, by rfl⟩ : syracuseStep 675373 = 253265) B253265
theorem B314945 : Blo 207808 314945 := bstep (se 2 (by rfl) ⟨118104, by rfl⟩ : syracuseStep 314945 = 236209) B236209
theorem B1134157 : Blo 207808 1134157 := bstep (se 3 (by rfl) ⟨212654, by rfl⟩ : syracuseStep 1134157 = 425309) B425309
theorem B314963 : Blo 207808 314963 := bstep (se 1 (by rfl) ⟨236222, by rfl⟩ : syracuseStep 314963 = 472445) B472445
theorem B708209 : Blo 207808 708209 := bstep (se 2 (by rfl) ⟨265578, by rfl⟩ : syracuseStep 708209 = 531157) B531157
theorem B314993 : Blo 207808 314993 := bstep (se 2 (by rfl) ⟨118122, by rfl⟩ : syracuseStep 314993 = 236245) B236245
theorem B315011 : Blo 207808 315011 := bstep (se 1 (by rfl) ⟨236258, by rfl⟩ : syracuseStep 315011 = 472517) B472517
theorem B315041 : Blo 207808 315041 := bstep (se 2 (by rfl) ⟨118140, by rfl⟩ : syracuseStep 315041 = 236281) B236281
theorem B315059 : Blo 207808 315059 := bstep (se 1 (by rfl) ⟨236294, by rfl⟩ : syracuseStep 315059 = 472589) B472589
theorem B315089 : Blo 207808 315089 := bstep (se 2 (by rfl) ⟨118158, by rfl⟩ : syracuseStep 315089 = 236317) B236317
theorem B315107 : Blo 207808 315107 := bstep (se 1 (by rfl) ⟨236330, by rfl⟩ : syracuseStep 315107 = 472661) B472661
theorem B1199843 : Blo 207808 1199843 := bstep (se 1 (by rfl) ⟨899882, by rfl⟩ : syracuseStep 1199843 = 1799765) B1799765
theorem B315137 : Blo 207808 315137 := bstep (se 2 (by rfl) ⟨118176, by rfl⟩ : syracuseStep 315137 = 236353) B236353
theorem B315155 : Blo 207808 315155 := bstep (se 1 (by rfl) ⟨236366, by rfl⟩ : syracuseStep 315155 = 472733) B472733
theorem B315185 : Blo 207808 315185 := bstep (se 2 (by rfl) ⟨118194, by rfl⟩ : syracuseStep 315185 = 236389) B236389
theorem B315203 : Blo 207808 315203 := bstep (se 1 (by rfl) ⟨236402, by rfl⟩ : syracuseStep 315203 = 472805) B472805
theorem B315233 : Blo 207808 315233 := bstep (se 2 (by rfl) ⟨118212, by rfl⟩ : syracuseStep 315233 = 236425) B236425
theorem B315251 : Blo 207808 315251 := bstep (se 1 (by rfl) ⟨236438, by rfl⟩ : syracuseStep 315251 = 472877) B472877
theorem B315281 : Blo 207808 315281 := bstep (se 2 (by rfl) ⟨118230, by rfl⟩ : syracuseStep 315281 = 236461) B236461
theorem B315299 : Blo 207808 315299 := bstep (se 1 (by rfl) ⟨236474, by rfl⟩ : syracuseStep 315299 = 472949) B472949
theorem B315329 : Blo 207808 315329 := bstep (se 2 (by rfl) ⟨118248, by rfl⟩ : syracuseStep 315329 = 236497) B236497
theorem B315347 : Blo 207808 315347 := bstep (se 1 (by rfl) ⟨236510, by rfl⟩ : syracuseStep 315347 = 473021) B473021
theorem B315377 : Blo 207808 315377 := bstep (se 2 (by rfl) ⟨118266, by rfl⟩ : syracuseStep 315377 = 236533) B236533
theorem B315395 : Blo 207808 315395 := bstep (se 1 (by rfl) ⟨236546, by rfl⟩ : syracuseStep 315395 = 473093) B473093
theorem B315425 : Blo 207808 315425 := bstep (se 2 (by rfl) ⟨118284, by rfl⟩ : syracuseStep 315425 = 236569) B236569
theorem B315443 : Blo 207808 315443 := bstep (se 1 (by rfl) ⟨236582, by rfl⟩ : syracuseStep 315443 = 473165) B473165
theorem B315473 : Blo 207808 315473 := bstep (se 2 (by rfl) ⟨118302, by rfl⟩ : syracuseStep 315473 = 236605) B236605
theorem B315491 : Blo 207808 315491 := bstep (se 1 (by rfl) ⟨236618, by rfl⟩ : syracuseStep 315491 = 473237) B473237
theorem B315521 : Blo 207808 315521 := bstep (se 2 (by rfl) ⟨118320, by rfl⟩ : syracuseStep 315521 = 236641) B236641
theorem B708749 : Blo 207808 708749 := bstep (se 3 (by rfl) ⟨132890, by rfl⟩ : syracuseStep 708749 = 265781) B265781
theorem B315539 : Blo 207808 315539 := bstep (se 1 (by rfl) ⟨236654, by rfl⟩ : syracuseStep 315539 = 473309) B473309
theorem B446627 : Blo 207808 446627 := bstep (se 1 (by rfl) ⟨334970, by rfl⟩ : syracuseStep 446627 = 669941) B669941
theorem B315569 : Blo 207808 315569 := bstep (se 2 (by rfl) ⟨118338, by rfl⟩ : syracuseStep 315569 = 236677) B236677
theorem B708803 : Blo 207808 708803 := bstep (se 1 (by rfl) ⟨531602, by rfl⟩ : syracuseStep 708803 = 1063205) B1063205
theorem B315587 : Blo 207808 315587 := bstep (se 1 (by rfl) ⟨236690, by rfl⟩ : syracuseStep 315587 = 473381) B473381
theorem B315617 : Blo 207808 315617 := bstep (se 2 (by rfl) ⟨118356, by rfl⟩ : syracuseStep 315617 = 236713) B236713
theorem B315635 : Blo 207808 315635 := bstep (se 1 (by rfl) ⟨236726, by rfl⟩ : syracuseStep 315635 = 473453) B473453
theorem B315665 : Blo 207808 315665 := bstep (se 2 (by rfl) ⟨118374, by rfl⟩ : syracuseStep 315665 = 236749) B236749
theorem B315683 : Blo 207808 315683 := bstep (se 1 (by rfl) ⟨236762, by rfl⟩ : syracuseStep 315683 = 473525) B473525
theorem B1069361 : Blo 207808 1069361 := bstep (se 2 (by rfl) ⟨401010, by rfl⟩ : syracuseStep 1069361 = 802021) B802021
theorem B315713 : Blo 207808 315713 := bstep (se 2 (by rfl) ⟨118392, by rfl⟩ : syracuseStep 315713 = 236785) B236785
theorem B315731 : Blo 207808 315731 := bstep (se 1 (by rfl) ⟨236798, by rfl⟩ : syracuseStep 315731 = 473597) B473597
theorem B315761 : Blo 207808 315761 := bstep (se 2 (by rfl) ⟨118410, by rfl⟩ : syracuseStep 315761 = 236821) B236821
theorem B610673 : Blo 207808 610673 := bstep (se 2 (by rfl) ⟨229002, by rfl⟩ : syracuseStep 610673 = 458005) B458005
theorem B315779 : Blo 207808 315779 := bstep (se 1 (by rfl) ⟨236834, by rfl⟩ : syracuseStep 315779 = 473669) B473669
theorem B315809 : Blo 207808 315809 := bstep (se 2 (by rfl) ⟨118428, by rfl⟩ : syracuseStep 315809 = 236857) B236857
theorem B315827 : Blo 207808 315827 := bstep (se 1 (by rfl) ⟨236870, by rfl⟩ : syracuseStep 315827 = 473741) B473741
theorem B709073 : Blo 207808 709073 := bstep (se 2 (by rfl) ⟨265902, by rfl⟩ : syracuseStep 709073 = 531805) B531805
theorem B315857 : Blo 207808 315857 := bstep (se 2 (by rfl) ⟨118446, by rfl⟩ : syracuseStep 315857 = 236893) B236893
theorem B315875 : Blo 207808 315875 := bstep (se 1 (by rfl) ⟨236906, by rfl⟩ : syracuseStep 315875 = 473813) B473813
theorem B315905 : Blo 207808 315905 := bstep (se 2 (by rfl) ⟨118464, by rfl⟩ : syracuseStep 315905 = 236929) B236929
theorem B315923 : Blo 207808 315923 := bstep (se 1 (by rfl) ⟨236942, by rfl⟩ : syracuseStep 315923 = 473885) B473885
theorem B315953 : Blo 207808 315953 := bstep (se 2 (by rfl) ⟨118482, by rfl⟩ : syracuseStep 315953 = 236965) B236965
theorem B315971 : Blo 207808 315971 := bstep (se 1 (by rfl) ⟨236978, by rfl⟩ : syracuseStep 315971 = 473957) B473957
theorem B479825 : Blo 207808 479825 := bstep (se 2 (by rfl) ⟨179934, by rfl⟩ : syracuseStep 479825 = 359869) B359869
theorem B316001 : Blo 207808 316001 := bstep (se 2 (by rfl) ⟨118500, by rfl⟩ : syracuseStep 316001 = 237001) B237001
theorem B676451 : Blo 207808 676451 := bstep (se 1 (by rfl) ⟨507338, by rfl⟩ : syracuseStep 676451 = 1014677) B1014677
theorem B316019 : Blo 207808 316019 := bstep (se 1 (by rfl) ⟨237014, by rfl⟩ : syracuseStep 316019 = 474029) B474029
theorem B316049 : Blo 207808 316049 := bstep (se 2 (by rfl) ⟨118518, by rfl⟩ : syracuseStep 316049 = 237037) B237037
theorem B316067 : Blo 207808 316067 := bstep (se 1 (by rfl) ⟨237050, by rfl⟩ : syracuseStep 316067 = 474101) B474101
theorem B316097 : Blo 207808 316097 := bstep (se 2 (by rfl) ⟨118536, by rfl⟩ : syracuseStep 316097 = 237073) B237073
theorem B1200845 : Blo 207808 1200845 := bstep (se 3 (by rfl) ⟨225158, by rfl⟩ : syracuseStep 1200845 = 450317) B450317
theorem B316115 : Blo 207808 316115 := bstep (se 1 (by rfl) ⟨237086, by rfl⟩ : syracuseStep 316115 = 474173) B474173
theorem B316145 : Blo 207808 316145 := bstep (se 2 (by rfl) ⟨118554, by rfl⟩ : syracuseStep 316145 = 237109) B237109
theorem B316163 : Blo 207808 316163 := bstep (se 1 (by rfl) ⟨237122, by rfl⟩ : syracuseStep 316163 = 474245) B474245
theorem B316193 : Blo 207808 316193 := bstep (se 2 (by rfl) ⟨118572, by rfl⟩ : syracuseStep 316193 = 237145) B237145
theorem B316211 : Blo 207808 316211 := bstep (se 1 (by rfl) ⟨237158, by rfl⟩ : syracuseStep 316211 = 474317) B474317
theorem B316241 : Blo 207808 316241 := bstep (se 2 (by rfl) ⟨118590, by rfl⟩ : syracuseStep 316241 = 237181) B237181
theorem B316259 : Blo 207808 316259 := bstep (se 1 (by rfl) ⟨237194, by rfl⟩ : syracuseStep 316259 = 474389) B474389
theorem B283507 : Blo 207808 283507 := bstep (se 1 (by rfl) ⟨212630, by rfl⟩ : syracuseStep 283507 = 425261) B425261
theorem B316289 : Blo 207808 316289 := bstep (se 2 (by rfl) ⟨118608, by rfl⟩ : syracuseStep 316289 = 237217) B237217
theorem B1823629 : Blo 207808 1823629 := bstep (se 3 (by rfl) ⟨341930, by rfl⟩ : syracuseStep 1823629 = 683861) B683861
theorem B316307 : Blo 207808 316307 := bstep (se 1 (by rfl) ⟨237230, by rfl⟩ : syracuseStep 316307 = 474461) B474461
theorem B316337 : Blo 207808 316337 := bstep (se 2 (by rfl) ⟨118626, by rfl⟩ : syracuseStep 316337 = 237253) B237253
theorem B316355 : Blo 207808 316355 := bstep (se 1 (by rfl) ⟨237266, by rfl⟩ : syracuseStep 316355 = 474533) B474533
theorem B316385 : Blo 207808 316385 := bstep (se 2 (by rfl) ⟨118644, by rfl⟩ : syracuseStep 316385 = 237289) B237289
theorem B709613 : Blo 207808 709613 := bstep (se 3 (by rfl) ⟨133052, by rfl⟩ : syracuseStep 709613 = 266105) B266105
theorem B316403 : Blo 207808 316403 := bstep (se 1 (by rfl) ⟨237302, by rfl⟩ : syracuseStep 316403 = 474605) B474605
theorem B316433 : Blo 207808 316433 := bstep (se 2 (by rfl) ⟨118662, by rfl⟩ : syracuseStep 316433 = 237325) B237325
theorem B709667 : Blo 207808 709667 := bstep (se 1 (by rfl) ⟨532250, by rfl⟩ : syracuseStep 709667 = 1064501) B1064501
theorem B316451 : Blo 207808 316451 := bstep (se 1 (by rfl) ⟨237338, by rfl⟩ : syracuseStep 316451 = 474677) B474677
theorem B316481 : Blo 207808 316481 := bstep (se 2 (by rfl) ⟨118680, by rfl⟩ : syracuseStep 316481 = 237361) B237361
theorem B316499 : Blo 207808 316499 := bstep (se 1 (by rfl) ⟨237374, by rfl⟩ : syracuseStep 316499 = 474749) B474749
theorem B316529 : Blo 207808 316529 := bstep (se 2 (by rfl) ⟨118698, by rfl⟩ : syracuseStep 316529 = 237397) B237397
theorem B2380913 : Blo 207808 2380913 := bstep (se 2 (by rfl) ⟨892842, by rfl⟩ : syracuseStep 2380913 = 1785685) B1785685
theorem B447601 : Blo 207808 447601 := bstep (se 2 (by rfl) ⟨167850, by rfl⟩ : syracuseStep 447601 = 335701) B335701
theorem B316547 : Blo 207808 316547 := bstep (se 1 (by rfl) ⟨237410, by rfl⟩ : syracuseStep 316547 = 474821) B474821
theorem B316577 : Blo 207808 316577 := bstep (se 2 (by rfl) ⟨118716, by rfl⟩ : syracuseStep 316577 = 237433) B237433
theorem B316595 : Blo 207808 316595 := bstep (se 1 (by rfl) ⟨237446, by rfl⟩ : syracuseStep 316595 = 474893) B474893
theorem B1594565 : Blo 207808 1594565 := bstep (se 4 (by rfl) ⟨149490, by rfl⟩ : syracuseStep 1594565 = 298981) B298981
theorem B316625 : Blo 207808 316625 := bstep (se 2 (by rfl) ⟨118734, by rfl⟩ : syracuseStep 316625 = 237469) B237469
theorem B316643 : Blo 207808 316643 := bstep (se 1 (by rfl) ⟨237482, by rfl⟩ : syracuseStep 316643 = 474965) B474965
theorem B677105 : Blo 207808 677105 := bstep (se 2 (by rfl) ⟨253914, by rfl⟩ : syracuseStep 677105 = 507829) B507829
theorem B316673 : Blo 207808 316673 := bstep (se 2 (by rfl) ⟨118752, by rfl⟩ : syracuseStep 316673 = 237505) B237505
theorem B316691 : Blo 207808 316691 := bstep (se 1 (by rfl) ⟨237518, by rfl⟩ : syracuseStep 316691 = 475037) B475037
theorem B709937 : Blo 207808 709937 := bstep (se 2 (by rfl) ⟨266226, by rfl⟩ : syracuseStep 709937 = 532453) B532453
theorem B316721 : Blo 207808 316721 := bstep (se 2 (by rfl) ⟨118770, by rfl⟩ : syracuseStep 316721 = 237541) B237541
theorem B316739 : Blo 207808 316739 := bstep (se 1 (by rfl) ⟨237554, by rfl⟩ : syracuseStep 316739 = 475109) B475109
theorem B316769 : Blo 207808 316769 := bstep (se 2 (by rfl) ⟨118788, by rfl⟩ : syracuseStep 316769 = 237577) B237577
theorem B447857 : Blo 207808 447857 := bstep (se 2 (by rfl) ⟨167946, by rfl⟩ : syracuseStep 447857 = 335893) B335893
theorem B316787 : Blo 207808 316787 := bstep (se 1 (by rfl) ⟨237590, by rfl⟩ : syracuseStep 316787 = 475181) B475181
theorem B316817 : Blo 207808 316817 := bstep (se 2 (by rfl) ⟨118806, by rfl⟩ : syracuseStep 316817 = 237613) B237613
theorem B316835 : Blo 207808 316835 := bstep (se 1 (by rfl) ⟨237626, by rfl⟩ : syracuseStep 316835 = 475253) B475253
theorem B316865 : Blo 207808 316865 := bstep (se 2 (by rfl) ⟨118824, by rfl⟩ : syracuseStep 316865 = 237649) B237649
theorem B316883 : Blo 207808 316883 := bstep (se 1 (by rfl) ⟨237662, by rfl⟩ : syracuseStep 316883 = 475325) B475325
theorem B316913 : Blo 207808 316913 := bstep (se 2 (by rfl) ⟨118842, by rfl⟩ : syracuseStep 316913 = 237685) B237685
theorem B316931 : Blo 207808 316931 := bstep (se 1 (by rfl) ⟨237698, by rfl⟩ : syracuseStep 316931 = 475397) B475397
theorem B316961 : Blo 207808 316961 := bstep (se 2 (by rfl) ⟨118860, by rfl⟩ : syracuseStep 316961 = 237721) B237721
theorem B316979 : Blo 207808 316979 := bstep (se 1 (by rfl) ⟨237734, by rfl⟩ : syracuseStep 316979 = 475469) B475469
theorem B317009 : Blo 207808 317009 := bstep (se 2 (by rfl) ⟨118878, by rfl⟩ : syracuseStep 317009 = 237757) B237757
theorem B317027 : Blo 207808 317027 := bstep (se 1 (by rfl) ⟨237770, by rfl⟩ : syracuseStep 317027 = 475541) B475541
theorem B317057 : Blo 207808 317057 := bstep (se 2 (by rfl) ⟨118896, by rfl⟩ : syracuseStep 317057 = 237793) B237793
theorem B317075 : Blo 207808 317075 := bstep (se 1 (by rfl) ⟨237806, by rfl⟩ : syracuseStep 317075 = 475613) B475613
theorem B1267363 : Blo 207808 1267363 := bstep (se 1 (by rfl) ⟨950522, by rfl⟩ : syracuseStep 1267363 = 1901045) B1901045
theorem B317105 : Blo 207808 317105 := bstep (se 2 (by rfl) ⟨118914, by rfl⟩ : syracuseStep 317105 = 237829) B237829
theorem B317123 : Blo 207808 317123 := bstep (se 1 (by rfl) ⟨237842, by rfl⟩ : syracuseStep 317123 = 475685) B475685
theorem B317153 : Blo 207808 317153 := bstep (se 2 (by rfl) ⟨118932, by rfl⟩ : syracuseStep 317153 = 237865) B237865
theorem B1070819 : Blo 207808 1070819 := bstep (se 1 (by rfl) ⟨803114, by rfl⟩ : syracuseStep 1070819 = 1606229) B1606229
theorem B317171 : Blo 207808 317171 := bstep (se 1 (by rfl) ⟨237878, by rfl⟩ : syracuseStep 317171 = 475757) B475757
theorem B317201 : Blo 207808 317201 := bstep (se 2 (by rfl) ⟨118950, by rfl⟩ : syracuseStep 317201 = 237901) B237901
theorem B317219 : Blo 207808 317219 := bstep (se 1 (by rfl) ⟨237914, by rfl⟩ : syracuseStep 317219 = 475829) B475829
theorem B317249 : Blo 207808 317249 := bstep (se 2 (by rfl) ⟨118968, by rfl⟩ : syracuseStep 317249 = 237937) B237937
theorem B710477 : Blo 207808 710477 := bstep (se 3 (by rfl) ⟨133214, by rfl⟩ : syracuseStep 710477 = 266429) B266429
theorem B317267 : Blo 207808 317267 := bstep (se 1 (by rfl) ⟨237950, by rfl⟩ : syracuseStep 317267 = 475901) B475901
theorem B317297 : Blo 207808 317297 := bstep (se 2 (by rfl) ⟨118986, by rfl⟩ : syracuseStep 317297 = 237973) B237973
theorem B710531 : Blo 207808 710531 := bstep (se 1 (by rfl) ⟨532898, by rfl⟩ : syracuseStep 710531 = 1065797) B1065797
theorem B317315 : Blo 207808 317315 := bstep (se 1 (by rfl) ⟨237986, by rfl⟩ : syracuseStep 317315 = 475973) B475973
theorem B317345 : Blo 207808 317345 := bstep (se 2 (by rfl) ⟨119004, by rfl⟩ : syracuseStep 317345 = 238009) B238009
theorem B317363 : Blo 207808 317363 := bstep (se 1 (by rfl) ⟨238022, by rfl⟩ : syracuseStep 317363 = 476045) B476045
theorem B317393 : Blo 207808 317393 := bstep (se 2 (by rfl) ⟨119022, by rfl⟩ : syracuseStep 317393 = 238045) B238045
theorem B317411 : Blo 207808 317411 := bstep (se 1 (by rfl) ⟨238058, by rfl⟩ : syracuseStep 317411 = 476117) B476117
theorem B317441 : Blo 207808 317441 := bstep (se 2 (by rfl) ⟨119040, by rfl⟩ : syracuseStep 317441 = 238081) B238081
theorem B317459 : Blo 207808 317459 := bstep (se 1 (by rfl) ⟨238094, by rfl⟩ : syracuseStep 317459 = 476189) B476189
theorem B317489 : Blo 207808 317489 := bstep (se 2 (by rfl) ⟨119058, by rfl⟩ : syracuseStep 317489 = 238117) B238117
theorem B317507 : Blo 207808 317507 := bstep (se 1 (by rfl) ⟨238130, by rfl⟩ : syracuseStep 317507 = 476261) B476261
theorem B317537 : Blo 207808 317537 := bstep (se 2 (by rfl) ⟨119076, by rfl⟩ : syracuseStep 317537 = 238153) B238153
theorem B481393 : Blo 207808 481393 := bstep (se 2 (by rfl) ⟨180522, by rfl⟩ : syracuseStep 481393 = 361045) B361045
theorem B317555 : Blo 207808 317555 := bstep (se 1 (by rfl) ⟨238166, by rfl⟩ : syracuseStep 317555 = 476333) B476333
theorem B710801 : Blo 207808 710801 := bstep (se 2 (by rfl) ⟨266550, by rfl⟩ : syracuseStep 710801 = 533101) B533101
theorem B317585 : Blo 207808 317585 := bstep (se 2 (by rfl) ⟨119094, by rfl⟩ : syracuseStep 317585 = 238189) B238189
theorem B317603 : Blo 207808 317603 := bstep (se 1 (by rfl) ⟨238202, by rfl⟩ : syracuseStep 317603 = 476405) B476405
theorem B317633 : Blo 207808 317633 := bstep (se 2 (by rfl) ⟨119112, by rfl⟩ : syracuseStep 317633 = 238225) B238225
theorem B317651 : Blo 207808 317651 := bstep (se 1 (by rfl) ⟨238238, by rfl⟩ : syracuseStep 317651 = 476477) B476477
theorem B317681 : Blo 207808 317681 := bstep (se 2 (by rfl) ⟨119130, by rfl⟩ : syracuseStep 317681 = 238261) B238261
theorem B317699 : Blo 207808 317699 := bstep (se 1 (by rfl) ⟨238274, by rfl⟩ : syracuseStep 317699 = 476549) B476549
theorem B580013 : Blo 207808 580013 := bstep (se 3 (by rfl) ⟨108752, by rfl⟩ : syracuseStep 580013 = 217505) B217505
theorem B350689 : Blo 207808 350689 := bstep (se 2 (by rfl) ⟨131508, by rfl⟩ : syracuseStep 350689 = 263017) B263017
theorem B350723 : Blo 207808 350723 := bstep (se 1 (by rfl) ⟨263042, by rfl⟩ : syracuseStep 350723 = 526085) B526085
theorem B1071629 : Blo 207808 1071629 := bstep (se 3 (by rfl) ⟨200930, by rfl⟩ : syracuseStep 1071629 = 401861) B401861
theorem B678449 : Blo 207808 678449 := bstep (se 2 (by rfl) ⟨254418, by rfl⟩ : syracuseStep 678449 = 508837) B508837
theorem B350851 : Blo 207808 350851 := bstep (se 1 (by rfl) ⟨263138, by rfl⟩ : syracuseStep 350851 = 526277) B526277
theorem B449155 : Blo 207808 449155 := bstep (se 1 (by rfl) ⟨336866, by rfl⟩ : syracuseStep 449155 = 673733) B673733
theorem B383651 : Blo 207808 383651 := bstep (se 1 (by rfl) ⟨287738, by rfl⟩ : syracuseStep 383651 = 575477) B575477
theorem B711341 : Blo 207808 711341 := bstep (se 3 (by rfl) ⟨133376, by rfl⟩ : syracuseStep 711341 = 266753) B266753
theorem B8575715 : Blo 207808 8575715 := bstep (se 1 (by rfl) ⟨6431786, by rfl⟩ : syracuseStep 8575715 = 12863573) B12863573
theorem B711395 : Blo 207808 711395 := bstep (se 1 (by rfl) ⟨533546, by rfl⟩ : syracuseStep 711395 = 1067093) B1067093
theorem B350993 : Blo 207808 350993 := bstep (se 2 (by rfl) ⟨131622, by rfl⟩ : syracuseStep 350993 = 263245) B263245
theorem B351121 : Blo 207808 351121 := bstep (se 2 (by rfl) ⟨131670, by rfl⟩ : syracuseStep 351121 = 263341) B263341
theorem B351155 : Blo 207808 351155 := bstep (se 1 (by rfl) ⟨263366, by rfl⟩ : syracuseStep 351155 = 526733) B526733
theorem B449489 : Blo 207808 449489 := bstep (se 2 (by rfl) ⟨168558, by rfl⟩ : syracuseStep 449489 = 337117) B337117
theorem B711665 : Blo 207808 711665 := bstep (se 2 (by rfl) ⟨266874, by rfl⟩ : syracuseStep 711665 = 533749) B533749
theorem B351283 : Blo 207808 351283 := bstep (se 1 (by rfl) ⟨263462, by rfl⟩ : syracuseStep 351283 = 526925) B526925
theorem B351425 : Blo 207808 351425 := bstep (se 2 (by rfl) ⟨131784, by rfl⟩ : syracuseStep 351425 = 263569) B263569
theorem B580877 : Blo 207808 580877 := bstep (se 3 (by rfl) ⟨108914, by rfl⟩ : syracuseStep 580877 = 217829) B217829
theorem B351553 : Blo 207808 351553 := bstep (se 2 (by rfl) ⟨131832, by rfl⟩ : syracuseStep 351553 = 263665) B263665
theorem B351587 : Blo 207808 351587 := bstep (se 1 (by rfl) ⟨263690, by rfl⟩ : syracuseStep 351587 = 527381) B527381
theorem B351715 : Blo 207808 351715 := bstep (se 1 (by rfl) ⟨263786, by rfl⟩ : syracuseStep 351715 = 527573) B527573
theorem B712205 : Blo 207808 712205 := bstep (se 3 (by rfl) ⟨133538, by rfl⟩ : syracuseStep 712205 = 267077) B267077
theorem B1433123 : Blo 207808 1433123 := bstep (se 1 (by rfl) ⟨1074842, by rfl⟩ : syracuseStep 1433123 = 2149685) B2149685
theorem B1203761 : Blo 207808 1203761 := bstep (se 2 (by rfl) ⟨451410, by rfl⟩ : syracuseStep 1203761 = 902821) B902821
theorem B712259 : Blo 207808 712259 := bstep (se 1 (by rfl) ⟨534194, by rfl⟩ : syracuseStep 712259 = 1068389) B1068389
theorem B351857 : Blo 207808 351857 := bstep (se 2 (by rfl) ⟨131946, by rfl⟩ : syracuseStep 351857 = 263893) B263893
theorem B351985 : Blo 207808 351985 := bstep (se 2 (by rfl) ⟨131994, by rfl⟩ : syracuseStep 351985 = 263989) B263989
theorem B352019 : Blo 207808 352019 := bstep (se 1 (by rfl) ⟨264014, by rfl⟩ : syracuseStep 352019 = 528029) B528029
theorem B712529 : Blo 207808 712529 := bstep (se 2 (by rfl) ⟨267198, by rfl⟩ : syracuseStep 712529 = 534397) B534397
theorem B352147 : Blo 207808 352147 := bstep (se 1 (by rfl) ⟨264110, by rfl⟩ : syracuseStep 352147 = 528221) B528221
theorem B352289 : Blo 207808 352289 := bstep (se 2 (by rfl) ⟨132108, by rfl⟩ : syracuseStep 352289 = 264217) B264217
theorem B450659 : Blo 207808 450659 := bstep (se 1 (by rfl) ⟨337994, by rfl⟩ : syracuseStep 450659 = 675989) B675989
theorem B1368197 : Blo 207808 1368197 := bstep (se 4 (by rfl) ⟨128268, by rfl⟩ : syracuseStep 1368197 = 256537) B256537
theorem B352417 : Blo 207808 352417 := bstep (se 2 (by rfl) ⟨132156, by rfl⟩ : syracuseStep 352417 = 264313) B264313
theorem B1335473 : Blo 207808 1335473 := bstep (se 2 (by rfl) ⟨500802, by rfl⟩ : syracuseStep 1335473 = 1001605) B1001605
theorem B352451 : Blo 207808 352451 := bstep (se 1 (by rfl) ⟨264338, by rfl⟩ : syracuseStep 352451 = 528677) B528677
theorem B352579 : Blo 207808 352579 := bstep (se 1 (by rfl) ⟨264434, by rfl⟩ : syracuseStep 352579 = 528869) B528869
theorem B287059 : Blo 207808 287059 := bstep (se 1 (by rfl) ⟨215294, by rfl⟩ : syracuseStep 287059 = 430589) B430589
theorem B713069 : Blo 207808 713069 := bstep (se 3 (by rfl) ⟨133700, by rfl⟩ : syracuseStep 713069 = 267401) B267401
theorem B319907 : Blo 207808 319907 := bstep (se 1 (by rfl) ⟨239930, by rfl⟩ : syracuseStep 319907 = 479861) B479861
theorem B713123 : Blo 207808 713123 := bstep (se 1 (by rfl) ⟨534842, by rfl⟩ : syracuseStep 713123 = 1069685) B1069685
theorem B352721 : Blo 207808 352721 := bstep (se 2 (by rfl) ⟨132270, by rfl⟩ : syracuseStep 352721 = 264541) B264541
theorem B319955 : Blo 207808 319955 := bstep (se 1 (by rfl) ⟨239966, by rfl⟩ : syracuseStep 319955 = 479933) B479933
theorem B680525 : Blo 207808 680525 := bstep (se 3 (by rfl) ⟨127598, by rfl⟩ : syracuseStep 680525 = 255197) B255197
theorem B352849 : Blo 207808 352849 := bstep (se 2 (by rfl) ⟨132318, by rfl⟩ : syracuseStep 352849 = 264637) B264637
theorem B352883 : Blo 207808 352883 := bstep (se 1 (by rfl) ⟨264662, by rfl⟩ : syracuseStep 352883 = 529325) B529325
theorem B713393 : Blo 207808 713393 := bstep (se 2 (by rfl) ⟨267522, by rfl⟩ : syracuseStep 713393 = 535045) B535045
theorem B353011 : Blo 207808 353011 := bstep (se 1 (by rfl) ⟨264758, by rfl⟩ : syracuseStep 353011 = 529517) B529517
theorem B254755 : Blo 207808 254755 := bstep (se 1 (by rfl) ⟨191066, by rfl⟩ : syracuseStep 254755 = 382133) B382133
theorem B353153 : Blo 207808 353153 := bstep (se 2 (by rfl) ⟨132432, by rfl⟩ : syracuseStep 353153 = 264865) B264865
theorem B320387 : Blo 207808 320387 := bstep (se 1 (by rfl) ⟨240290, by rfl⟩ : syracuseStep 320387 = 480581) B480581
theorem B680849 : Blo 207808 680849 := bstep (se 2 (by rfl) ⟨255318, by rfl⟩ : syracuseStep 680849 = 510637) B510637
theorem B1205219 : Blo 207808 1205219 := bstep (se 1 (by rfl) ⟨903914, by rfl⟩ : syracuseStep 1205219 = 1807829) B1807829
theorem B353281 : Blo 207808 353281 := bstep (se 2 (by rfl) ⟨132480, by rfl⟩ : syracuseStep 353281 = 264961) B264961
theorem B353315 : Blo 207808 353315 := bstep (se 1 (by rfl) ⟨264986, by rfl⟩ : syracuseStep 353315 = 529973) B529973
theorem B5366897 : Blo 207808 5366897 := bstep (se 2 (by rfl) ⟨2012586, by rfl⟩ : syracuseStep 5366897 = 4025173) B4025173
theorem B353443 : Blo 207808 353443 := bstep (se 1 (by rfl) ⟨265082, by rfl⟩ : syracuseStep 353443 = 530165) B530165
theorem B713933 : Blo 207808 713933 := bstep (se 3 (by rfl) ⟨133862, by rfl⟩ : syracuseStep 713933 = 267725) B267725
theorem B713987 : Blo 207808 713987 := bstep (se 1 (by rfl) ⟨535490, by rfl⟩ : syracuseStep 713987 = 1070981) B1070981
theorem B353585 : Blo 207808 353585 := bstep (se 2 (by rfl) ⟨132594, by rfl⟩ : syracuseStep 353585 = 265189) B265189
theorem B1238321 : Blo 207808 1238321 := bstep (se 2 (by rfl) ⟨464370, by rfl⟩ : syracuseStep 1238321 = 928741) B928741
theorem B2712973 : Blo 207808 2712973 := bstep (se 3 (by rfl) ⟨508682, by rfl⟩ : syracuseStep 2712973 = 1017365) B1017365
theorem B353713 : Blo 207808 353713 := bstep (se 2 (by rfl) ⟨132642, by rfl⟩ : syracuseStep 353713 = 265285) B265285
theorem B353747 : Blo 207808 353747 := bstep (se 1 (by rfl) ⟨265310, by rfl⟩ : syracuseStep 353747 = 530621) B530621
theorem B222707 : Blo 207808 222707 := bstep (se 1 (by rfl) ⟨167030, by rfl⟩ : syracuseStep 222707 = 334061) B334061
theorem B714257 : Blo 207808 714257 := bstep (se 2 (by rfl) ⟨267846, by rfl⟩ : syracuseStep 714257 = 535693) B535693
theorem B353875 : Blo 207808 353875 := bstep (se 1 (by rfl) ⟨265406, by rfl⟩ : syracuseStep 353875 = 530813) B530813
theorem B222835 : Blo 207808 222835 := bstep (se 1 (by rfl) ⟨167126, by rfl⟩ : syracuseStep 222835 = 334253) B334253
theorem B354017 : Blo 207808 354017 := bstep (se 2 (by rfl) ⟨132756, by rfl⟩ : syracuseStep 354017 = 265513) B265513
theorem B354145 : Blo 207808 354145 := bstep (se 2 (by rfl) ⟨132804, by rfl⟩ : syracuseStep 354145 = 265609) B265609
theorem B354179 : Blo 207808 354179 := bstep (se 1 (by rfl) ⟨265634, by rfl⟩ : syracuseStep 354179 = 531269) B531269
theorem B354307 : Blo 207808 354307 := bstep (se 1 (by rfl) ⟨265730, by rfl⟩ : syracuseStep 354307 = 531461) B531461
theorem B714797 : Blo 207808 714797 := bstep (se 3 (by rfl) ⟨134024, by rfl⟩ : syracuseStep 714797 = 268049) B268049
theorem B714851 : Blo 207808 714851 := bstep (se 1 (by rfl) ⟨536138, by rfl⟩ : syracuseStep 714851 = 1072277) B1072277
theorem B1108081 : Blo 207808 1108081 := bstep (se 2 (by rfl) ⟨415530, by rfl⟩ : syracuseStep 1108081 = 831061) B831061
theorem B583811 : Blo 207808 583811 := bstep (se 1 (by rfl) ⟨437858, by rfl⟩ : syracuseStep 583811 = 875717) B875717
theorem B354449 : Blo 207808 354449 := bstep (se 2 (by rfl) ⟨132918, by rfl⟩ : syracuseStep 354449 = 265837) B265837
theorem B10414307 : Blo 207808 10414307 := bstep (se 1 (by rfl) ⟨7810730, by rfl⟩ : syracuseStep 10414307 = 15621461) B15621461
theorem B354577 : Blo 207808 354577 := bstep (se 2 (by rfl) ⟨132966, by rfl⟩ : syracuseStep 354577 = 265933) B265933
theorem B354611 : Blo 207808 354611 := bstep (se 1 (by rfl) ⟨265958, by rfl⟩ : syracuseStep 354611 = 531917) B531917
theorem B223651 : Blo 207808 223651 := bstep (se 1 (by rfl) ⟨167738, by rfl⟩ : syracuseStep 223651 = 335477) B335477
theorem B354739 : Blo 207808 354739 := bstep (se 1 (by rfl) ⟨266054, by rfl⟩ : syracuseStep 354739 = 532109) B532109
theorem B1370609 : Blo 207808 1370609 := bstep (se 2 (by rfl) ⟨513978, by rfl⟩ : syracuseStep 1370609 = 1027957) B1027957
theorem B813581 : Blo 207808 813581 := bstep (se 3 (by rfl) ⟨152546, by rfl⟩ : syracuseStep 813581 = 305093) B305093
theorem B354881 : Blo 207808 354881 := bstep (se 2 (by rfl) ⟨133080, by rfl⟩ : syracuseStep 354881 = 266161) B266161
theorem B1075825 : Blo 207808 1075825 := bstep (se 2 (by rfl) ⟨403434, by rfl⟩ : syracuseStep 1075825 = 806869) B806869
theorem B355009 : Blo 207808 355009 := bstep (se 2 (by rfl) ⟨133128, by rfl⟩ : syracuseStep 355009 = 266257) B266257
theorem B355043 : Blo 207808 355043 := bstep (se 1 (by rfl) ⟨266282, by rfl⟩ : syracuseStep 355043 = 532565) B532565
theorem B355171 : Blo 207808 355171 := bstep (se 1 (by rfl) ⟨266378, by rfl⟩ : syracuseStep 355171 = 532757) B532757
theorem B1600397 : Blo 207808 1600397 := bstep (se 3 (by rfl) ⟨300074, by rfl⟩ : syracuseStep 1600397 = 600149) B600149
theorem B355313 : Blo 207808 355313 := bstep (se 2 (by rfl) ⟨133242, by rfl⟩ : syracuseStep 355313 = 266485) B266485
theorem B355441 : Blo 207808 355441 := bstep (se 2 (by rfl) ⟨133290, by rfl⟩ : syracuseStep 355441 = 266581) B266581
theorem B355475 : Blo 207808 355475 := bstep (se 1 (by rfl) ⟨266606, by rfl⟩ : syracuseStep 355475 = 533213) B533213
theorem B1273009 : Blo 207808 1273009 := bstep (se 2 (by rfl) ⟨477378, by rfl⟩ : syracuseStep 1273009 = 954757) B954757
theorem B355603 : Blo 207808 355603 := bstep (se 1 (by rfl) ⟨266702, by rfl⟩ : syracuseStep 355603 = 533405) B533405
theorem B355745 : Blo 207808 355745 := bstep (se 2 (by rfl) ⟨133404, by rfl⟩ : syracuseStep 355745 = 266809) B266809
theorem B1371653 : Blo 207808 1371653 := bstep (se 4 (by rfl) ⟨128592, by rfl⟩ : syracuseStep 1371653 = 257185) B257185
theorem B355873 : Blo 207808 355873 := bstep (se 2 (by rfl) ⟨133452, by rfl⟩ : syracuseStep 355873 = 266905) B266905
theorem B355907 : Blo 207808 355907 := bstep (se 1 (by rfl) ⟨266930, by rfl⟩ : syracuseStep 355907 = 533861) B533861
theorem B356035 : Blo 207808 356035 := bstep (se 1 (by rfl) ⟨267026, by rfl⟩ : syracuseStep 356035 = 534053) B534053
theorem B2289379 : Blo 207808 2289379 := bstep (se 1 (by rfl) ⟨1717034, by rfl⟩ : syracuseStep 2289379 = 3434069) B3434069
theorem B356177 : Blo 207808 356177 := bstep (se 2 (by rfl) ⟨133566, by rfl⟩ : syracuseStep 356177 = 267133) B267133
theorem B2715491 : Blo 207808 2715491 := bstep (se 1 (by rfl) ⟨2036618, by rfl⟩ : syracuseStep 2715491 = 4073237) B4073237
theorem B421841 : Blo 207808 421841 := bstep (se 2 (by rfl) ⟨158190, by rfl⟩ : syracuseStep 421841 = 316381) B316381
theorem B356305 : Blo 207808 356305 := bstep (se 2 (by rfl) ⟨133614, by rfl⟩ : syracuseStep 356305 = 267229) B267229
theorem B356339 : Blo 207808 356339 := bstep (se 1 (by rfl) ⟨267254, by rfl⟩ : syracuseStep 356339 = 534509) B534509
theorem B356467 : Blo 207808 356467 := bstep (se 1 (by rfl) ⟨267350, by rfl⟩ : syracuseStep 356467 = 534701) B534701
theorem B1142981 : Blo 207808 1142981 := bstep (se 4 (by rfl) ⟨107154, by rfl⟩ : syracuseStep 1142981 = 214309) B214309
theorem B356609 : Blo 207808 356609 := bstep (se 2 (by rfl) ⟨133728, by rfl⟩ : syracuseStep 356609 = 267457) B267457
theorem B5402933 : Blo 207808 5402933 := bstep (se 5 (by rfl) ⟨253262, by rfl⟩ : syracuseStep 5402933 = 506525) B506525
theorem B356737 : Blo 207808 356737 := bstep (se 2 (by rfl) ⟨133776, by rfl⟩ : syracuseStep 356737 = 267553) B267553
theorem B356771 : Blo 207808 356771 := bstep (se 1 (by rfl) ⟨267578, by rfl⟩ : syracuseStep 356771 = 535157) B535157
theorem B356899 : Blo 207808 356899 := bstep (se 1 (by rfl) ⟨267674, by rfl⟩ : syracuseStep 356899 = 535349) B535349
theorem B422513 : Blo 207808 422513 := bstep (se 2 (by rfl) ⟨158442, by rfl⟩ : syracuseStep 422513 = 316885) B316885
theorem B357041 : Blo 207808 357041 := bstep (se 2 (by rfl) ⟨133890, by rfl⟩ : syracuseStep 357041 = 267781) B267781
theorem B357169 : Blo 207808 357169 := bstep (se 2 (by rfl) ⟨133938, by rfl⟩ : syracuseStep 357169 = 267877) B267877
theorem B357203 : Blo 207808 357203 := bstep (se 1 (by rfl) ⟨267902, by rfl⟩ : syracuseStep 357203 = 535805) B535805
theorem B357331 : Blo 207808 357331 := bstep (se 1 (by rfl) ⟨267998, by rfl⟩ : syracuseStep 357331 = 535997) B535997
theorem B1340549 : Blo 207808 1340549 := bstep (se 4 (by rfl) ⟨125676, by rfl⟩ : syracuseStep 1340549 = 251353) B251353
theorem B423299 : Blo 207808 423299 := bstep (se 1 (by rfl) ⟨317474, by rfl⟩ : syracuseStep 423299 = 634949) B634949
theorem B1603313 : Blo 207808 1603313 := bstep (se 2 (by rfl) ⟨601242, by rfl⟩ : syracuseStep 1603313 = 1202485) B1202485
theorem B685837 : Blo 207808 685837 := bstep (se 3 (by rfl) ⟨128594, by rfl⟩ : syracuseStep 685837 = 257189) B257189
theorem B916145 : Blo 207808 916145 := bstep (se 2 (by rfl) ⟨343554, by rfl⟩ : syracuseStep 916145 = 687109) B687109
theorem B260995 : Blo 207808 260995 := bstep (se 1 (by rfl) ⟨195746, by rfl⟩ : syracuseStep 260995 = 391493) B391493
theorem B752561 : Blo 207808 752561 := bstep (se 2 (by rfl) ⟨282210, by rfl⟩ : syracuseStep 752561 = 564421) B564421
theorem B359363 : Blo 207808 359363 := bstep (se 1 (by rfl) ⟨269522, by rfl⟩ : syracuseStep 359363 = 539045) B539045
theorem B1506275 : Blo 207808 1506275 := bstep (se 1 (by rfl) ⟨1129706, by rfl⟩ : syracuseStep 1506275 = 2259413) B2259413
theorem B1801541 : Blo 207808 1801541 := bstep (se 4 (by rfl) ⟨168894, by rfl⟩ : syracuseStep 1801541 = 337789) B337789
theorem B228691 : Blo 207808 228691 := bstep (se 1 (by rfl) ⟨171518, by rfl⟩ : syracuseStep 228691 = 343037) B343037
theorem B3079565 : Blo 207808 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B851917 : Blo 207808 851917 := bstep (se 3 (by rfl) ⟨159734, by rfl⟩ : syracuseStep 851917 = 319469) B319469
theorem B1081931 : Blo 207808 1081931 := bstep (se 1 (by rfl) ⟨811448, by rfl⟩ : syracuseStep 1081931 = 1622897) B1622897
theorem B1868579 : Blo 207808 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B263179 : Blo 207808 263179 := bstep (se 1 (by rfl) ⟨197384, by rfl⟩ : syracuseStep 263179 = 394769) B394769
theorem B853085 : Blo 207808 853085 := bstep (se 3 (by rfl) ⟨159953, by rfl⟩ : syracuseStep 853085 = 319907) B319907
theorem B853213 : Blo 207808 853213 := bstep (se 3 (by rfl) ⟨159977, by rfl⟩ : syracuseStep 853213 = 319955) B319955
theorem B394571 : Blo 207808 394571 := bstep (se 1 (by rfl) ⟨295928, by rfl⟩ : syracuseStep 394571 = 591857) B591857
theorem B394625 : Blo 207808 394625 := bstep (se 2 (by rfl) ⟨147984, by rfl⟩ : syracuseStep 394625 = 295969) B295969
theorem B3016115 : Blo 207808 3016115 := bstep (se 1 (by rfl) ⟨2262086, by rfl⟩ : syracuseStep 3016115 = 4524173) B4524173
theorem B296407 : Blo 207808 296407 := bstep (se 1 (by rfl) ⟨222305, by rfl⟩ : syracuseStep 296407 = 444611) B444611
theorem B2394035 : Blo 207808 2394035 := bstep (se 1 (by rfl) ⟨1795526, by rfl⟩ : syracuseStep 2394035 = 3591053) B3591053
theorem B264151 : Blo 207808 264151 := bstep (se 1 (by rfl) ⟨198113, by rfl⟩ : syracuseStep 264151 = 396227) B396227
theorem B526297 : Blo 207808 526297 := bstep (se 2 (by rfl) ⟨197361, by rfl⟩ : syracuseStep 526297 = 394723) B394723
theorem B297113 : Blo 207808 297113 := bstep (se 2 (by rfl) ⟨111417, by rfl⟩ : syracuseStep 297113 = 222835) B222835
theorem B755905 : Blo 207808 755905 := bstep (se 2 (by rfl) ⟨283464, by rfl⟩ : syracuseStep 755905 = 566929) B566929
theorem B297227 : Blo 207808 297227 := bstep (se 1 (by rfl) ⟨222920, by rfl⟩ : syracuseStep 297227 = 445841) B445841
theorem B395543 : Blo 207808 395543 := bstep (se 1 (by rfl) ⟨296657, by rfl⟩ : syracuseStep 395543 = 593315) B593315
theorem B428375 : Blo 207808 428375 := bstep (se 1 (by rfl) ⟨321281, by rfl⟩ : syracuseStep 428375 = 642563) B642563
theorem B854707 : Blo 207808 854707 := bstep (se 1 (by rfl) ⟨641030, by rfl⟩ : syracuseStep 854707 = 1282061) B1282061
theorem B264971 : Blo 207808 264971 := bstep (se 1 (by rfl) ⟨198728, by rfl⟩ : syracuseStep 264971 = 397457) B397457
theorem B297751 : Blo 207808 297751 := bstep (se 1 (by rfl) ⟨223313, by rfl⟩ : syracuseStep 297751 = 446627) B446627
theorem B396083 : Blo 207808 396083 := bstep (se 1 (by rfl) ⟨297062, by rfl⟩ : syracuseStep 396083 = 594125) B594125
theorem B1477441 : Blo 207808 1477441 := bstep (se 2 (by rfl) ⟨554040, by rfl⟩ : syracuseStep 1477441 = 1108081) B1108081
theorem B1772381 : Blo 207808 1772381 := bstep (se 3 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 1772381 = 664643) B664643
theorem B527411 : Blo 207808 527411 := bstep (se 1 (by rfl) ⟨395558, by rfl⟩ : syracuseStep 527411 = 791117) B791117
theorem B396569 : Blo 207808 396569 := bstep (se 2 (by rfl) ⟨148713, by rfl⟩ : syracuseStep 396569 = 297427) B297427
theorem B527705 : Blo 207808 527705 := bstep (se 2 (by rfl) ⟨197889, by rfl⟩ : syracuseStep 527705 = 395779) B395779
theorem B2395493 : Blo 207808 2395493 := bstep (se 4 (by rfl) ⟨224577, by rfl⟩ : syracuseStep 2395493 = 449155) B449155
theorem B265675 : Blo 207808 265675 := bstep (se 1 (by rfl) ⟨199256, by rfl⟩ : syracuseStep 265675 = 398513) B398513
theorem B298571 : Blo 207808 298571 := bstep (se 1 (by rfl) ⟨223928, by rfl⟩ : syracuseStep 298571 = 447857) B447857
theorem B593497 : Blo 207808 593497 := bstep (se 2 (by rfl) ⟨222561, by rfl⟩ : syracuseStep 593497 = 445123) B445123
theorem B265943 : Blo 207808 265943 := bstep (se 1 (by rfl) ⟨199457, by rfl⟩ : syracuseStep 265943 = 398915) B398915
theorem B888641 : Blo 207808 888641 := bstep (se 2 (by rfl) ⟨333240, by rfl⟩ : syracuseStep 888641 = 666481) B666481
theorem B3411811 : Blo 207808 3411811 := bstep (se 1 (by rfl) ⟨2558858, by rfl⟩ : syracuseStep 3411811 = 5117717) B5117717
theorem B593885 : Blo 207808 593885 := bstep (se 3 (by rfl) ⟨111353, by rfl⟩ : syracuseStep 593885 = 222707) B222707
theorem B790829 : Blo 207808 790829 := bstep (se 3 (by rfl) ⟨148280, by rfl⟩ : syracuseStep 790829 = 296561) B296561
theorem B233815 : Blo 207808 233815 := bstep (se 1 (by rfl) ⟨175361, by rfl⟩ : syracuseStep 233815 = 350723) B350723
theorem B266647 : Blo 207808 266647 := bstep (se 1 (by rfl) ⟨199985, by rfl⟩ : syracuseStep 266647 = 399971) B399971
theorem B233995 : Blo 207808 233995 := bstep (se 1 (by rfl) ⟨175496, by rfl⟩ : syracuseStep 233995 = 350993) B350993
theorem B1512037 : Blo 207808 1512037 := bstep (se 4 (by rfl) ⟨141753, by rfl⟩ : syracuseStep 1512037 = 283507) B283507
theorem B234103 : Blo 207808 234103 := bstep (se 1 (by rfl) ⟨175577, by rfl⟩ : syracuseStep 234103 = 351155) B351155
theorem B398027 : Blo 207808 398027 := bstep (se 1 (by rfl) ⟨298520, by rfl⟩ : syracuseStep 398027 = 597041) B597041
theorem B1512209 : Blo 207808 1512209 := bstep (se 2 (by rfl) ⟨567078, by rfl⟩ : syracuseStep 1512209 = 1134157) B1134157
theorem B234283 : Blo 207808 234283 := bstep (se 1 (by rfl) ⟨175712, by rfl⟩ : syracuseStep 234283 = 351425) B351425
theorem B1053485 : Blo 207808 1053485 := bstep (se 3 (by rfl) ⟨197528, by rfl⟩ : syracuseStep 1053485 = 395057) B395057
theorem B398209 : Blo 207808 398209 := bstep (se 2 (by rfl) ⟨149328, by rfl⟩ : syracuseStep 398209 = 298657) B298657
theorem B234391 : Blo 207808 234391 := bstep (se 1 (by rfl) ⟨175793, by rfl⟩ : syracuseStep 234391 = 351587) B351587
theorem B529355 : Blo 207808 529355 := bstep (se 1 (by rfl) ⟨397016, by rfl⟩ : syracuseStep 529355 = 794033) B794033
theorem B3052505 : Blo 207808 3052505 := bstep (se 2 (by rfl) ⟨1144689, by rfl⟩ : syracuseStep 3052505 = 2289379) B2289379
theorem B955415 : Blo 207808 955415 := bstep (se 1 (by rfl) ⟨716561, by rfl⟩ : syracuseStep 955415 = 1433123) B1433123
theorem B791603 : Blo 207808 791603 := bstep (se 1 (by rfl) ⟨593702, by rfl⟩ : syracuseStep 791603 = 1187405) B1187405
theorem B234571 : Blo 207808 234571 := bstep (se 1 (by rfl) ⟨175928, by rfl⟩ : syracuseStep 234571 = 351857) B351857
theorem B234679 : Blo 207808 234679 := bstep (se 1 (by rfl) ⟨176009, by rfl⟩ : syracuseStep 234679 = 352019) B352019
theorem B398657 : Blo 207808 398657 := bstep (se 2 (by rfl) ⟨149496, by rfl⟩ : syracuseStep 398657 = 298993) B298993
theorem B234859 : Blo 207808 234859 := bstep (se 1 (by rfl) ⟨176144, by rfl⟩ : syracuseStep 234859 = 352289) B352289
theorem B300439 : Blo 207808 300439 := bstep (se 1 (by rfl) ⟨225329, by rfl⟩ : syracuseStep 300439 = 450659) B450659
theorem B890315 : Blo 207808 890315 := bstep (se 1 (by rfl) ⟨667736, by rfl⟩ : syracuseStep 890315 = 1335473) B1335473
theorem B234967 : Blo 207808 234967 := bstep (se 1 (by rfl) ⟨176225, by rfl⟩ : syracuseStep 234967 = 352451) B352451
theorem B235147 : Blo 207808 235147 := bstep (se 1 (by rfl) ⟨176360, by rfl⟩ : syracuseStep 235147 = 352721) B352721
theorem B398999 : Blo 207808 398999 := bstep (se 1 (by rfl) ⟨299249, by rfl⟩ : syracuseStep 398999 = 598499) B598499
theorem B235255 : Blo 207808 235255 := bstep (se 1 (by rfl) ⟨176441, by rfl⟩ : syracuseStep 235255 = 352883) B352883
theorem B1709869 : Blo 207808 1709869 := bstep (se 3 (by rfl) ⟨320600, by rfl⟩ : syracuseStep 1709869 = 641201) B641201
theorem B530327 : Blo 207808 530327 := bstep (se 1 (by rfl) ⟨397745, by rfl⟩ : syracuseStep 530327 = 795491) B795491
theorem B235435 : Blo 207808 235435 := bstep (se 1 (by rfl) ⟨176576, by rfl⟩ : syracuseStep 235435 = 353153) B353153
theorem B5380019 : Blo 207808 5380019 := bstep (se 1 (by rfl) ⟨4035014, by rfl⟩ : syracuseStep 5380019 = 8070029) B8070029
theorem B1579013 : Blo 207808 1579013 := bstep (se 4 (by rfl) ⟨148032, by rfl⟩ : syracuseStep 1579013 = 296065) B296065
theorem B235543 : Blo 207808 235543 := bstep (se 1 (by rfl) ⟨176657, by rfl⟩ : syracuseStep 235543 = 353315) B353315
theorem B3577931 : Blo 207808 3577931 := bstep (se 1 (by rfl) ⟨2683448, by rfl⟩ : syracuseStep 3577931 = 5366897) B5366897
theorem B235723 : Blo 207808 235723 := bstep (se 1 (by rfl) ⟨176792, by rfl⟩ : syracuseStep 235723 = 353585) B353585
theorem B825547 : Blo 207808 825547 := bstep (se 1 (by rfl) ⟨619160, by rfl⟩ : syracuseStep 825547 = 1238321) B1238321
theorem B891101 : Blo 207808 891101 := bstep (se 3 (by rfl) ⟨167081, by rfl⟩ : syracuseStep 891101 = 334163) B334163
theorem B399667 : Blo 207808 399667 := bstep (se 1 (by rfl) ⟨299750, by rfl⟩ : syracuseStep 399667 = 599501) B599501
theorem B235831 : Blo 207808 235831 := bstep (se 1 (by rfl) ⟨176873, by rfl⟩ : syracuseStep 235831 = 353747) B353747
theorem B1186265 : Blo 207808 1186265 := bstep (se 2 (by rfl) ⟨444849, by rfl⟩ : syracuseStep 1186265 = 889699) B889699
theorem B236011 : Blo 207808 236011 := bstep (se 1 (by rfl) ⟨177008, by rfl⟩ : syracuseStep 236011 = 354017) B354017
theorem B793091 : Blo 207808 793091 := bstep (se 1 (by rfl) ⟨594818, by rfl⟩ : syracuseStep 793091 = 1189637) B1189637
theorem B2431505 : Blo 207808 2431505 := bstep (se 2 (by rfl) ⟨911814, by rfl⟩ : syracuseStep 2431505 = 1823629) B1823629
theorem B530995 : Blo 207808 530995 := bstep (se 1 (by rfl) ⟨398246, by rfl⟩ : syracuseStep 530995 = 796493) B796493
theorem B236119 : Blo 207808 236119 := bstep (se 1 (by rfl) ⟨177089, by rfl⟩ : syracuseStep 236119 = 354179) B354179
theorem B531137 : Blo 207808 531137 := bstep (se 2 (by rfl) ⟨199176, by rfl⟩ : syracuseStep 531137 = 398353) B398353
theorem B400115 : Blo 207808 400115 := bstep (se 1 (by rfl) ⟨300086, by rfl⟩ : syracuseStep 400115 = 600173) B600173
theorem B236299 : Blo 207808 236299 := bstep (se 1 (by rfl) ⟨177224, by rfl⟩ : syracuseStep 236299 = 354449) B354449
theorem B400153 : Blo 207808 400153 := bstep (se 2 (by rfl) ⟨150057, by rfl⟩ : syracuseStep 400153 = 300115) B300115
theorem B1514285 : Blo 207808 1514285 := bstep (se 3 (by rfl) ⟨283928, by rfl⟩ : syracuseStep 1514285 = 567857) B567857
theorem B596801 : Blo 207808 596801 := bstep (se 2 (by rfl) ⟨223800, by rfl⟩ : syracuseStep 596801 = 447601) B447601
theorem B236407 : Blo 207808 236407 := bstep (se 1 (by rfl) ⟨177305, by rfl⟩ : syracuseStep 236407 = 354611) B354611
theorem B596915 : Blo 207808 596915 := bstep (se 1 (by rfl) ⟨447686, by rfl⟩ : syracuseStep 596915 = 895373) B895373
theorem B793547 : Blo 207808 793547 := bstep (se 1 (by rfl) ⟨595160, by rfl⟩ : syracuseStep 793547 = 1190321) B1190321
theorem B236587 : Blo 207808 236587 := bstep (se 1 (by rfl) ⟨177440, by rfl⟩ : syracuseStep 236587 = 354881) B354881
theorem B793745 : Blo 207808 793745 := bstep (se 2 (by rfl) ⟨297654, by rfl⟩ : syracuseStep 793745 = 595309) B595309
theorem B236695 : Blo 207808 236695 := bstep (se 1 (by rfl) ⟨177521, by rfl⟩ : syracuseStep 236695 = 355043) B355043
theorem B400601 : Blo 207808 400601 := bstep (se 2 (by rfl) ⟨150225, by rfl⟩ : syracuseStep 400601 = 300451) B300451
theorem B236875 : Blo 207808 236875 := bstep (se 1 (by rfl) ⟨177656, by rfl⟩ : syracuseStep 236875 = 355313) B355313
theorem B236983 : Blo 207808 236983 := bstep (se 1 (by rfl) ⟨177737, by rfl⟩ : syracuseStep 236983 = 355475) B355475
theorem B1285649 : Blo 207808 1285649 := bstep (se 2 (by rfl) ⟨482118, by rfl⟩ : syracuseStep 1285649 = 964237) B964237
theorem B892433 : Blo 207808 892433 := bstep (se 2 (by rfl) ⟨334662, by rfl⟩ : syracuseStep 892433 = 669325) B669325
theorem B237163 : Blo 207808 237163 := bstep (se 1 (by rfl) ⟨177872, by rfl⟩ : syracuseStep 237163 = 355745) B355745
theorem B237271 : Blo 207808 237271 := bstep (se 1 (by rfl) ⟨177953, by rfl⟩ : syracuseStep 237271 = 355907) B355907
theorem B958301 : Blo 207808 958301 := bstep (se 3 (by rfl) ⟨179681, by rfl⟩ : syracuseStep 958301 = 359363) B359363
theorem B237451 : Blo 207808 237451 := bstep (se 1 (by rfl) ⟨178088, by rfl⟩ : syracuseStep 237451 = 356177) B356177
theorem B794519 : Blo 207808 794519 := bstep (se 1 (by rfl) ⟨595889, by rfl⟩ : syracuseStep 794519 = 1191779) B1191779
theorem B532403 : Blo 207808 532403 := bstep (se 1 (by rfl) ⟨399302, by rfl⟩ : syracuseStep 532403 = 798605) B798605
theorem B401345 : Blo 207808 401345 := bstep (se 2 (by rfl) ⟨150504, by rfl⟩ : syracuseStep 401345 = 301009) B301009
theorem B237559 : Blo 207808 237559 := bstep (se 1 (by rfl) ⟨178169, by rfl⟩ : syracuseStep 237559 = 356339) B356339
theorem B1187905 : Blo 207808 1187905 := bstep (se 2 (by rfl) ⟨445464, by rfl⟩ : syracuseStep 1187905 = 890929) B890929
theorem B794717 : Blo 207808 794717 := bstep (se 3 (by rfl) ⟨149009, by rfl⟩ : syracuseStep 794717 = 298019) B298019
theorem B761987 : Blo 207808 761987 := bstep (se 1 (by rfl) ⟨571490, by rfl⟩ : syracuseStep 761987 = 1142981) B1142981
theorem B237739 : Blo 207808 237739 := bstep (se 1 (by rfl) ⟨178304, by rfl⟩ : syracuseStep 237739 = 356609) B356609
theorem B401611 : Blo 207808 401611 := bstep (se 1 (by rfl) ⟨301208, by rfl⟩ : syracuseStep 401611 = 602417) B602417
theorem B237847 : Blo 207808 237847 := bstep (se 1 (by rfl) ⟨178385, by rfl⟩ : syracuseStep 237847 = 356771) B356771
theorem B1581443 : Blo 207808 1581443 := bstep (se 1 (by rfl) ⟨1186082, by rfl⟩ : syracuseStep 1581443 = 2372165) B2372165
theorem B532939 : Blo 207808 532939 := bstep (se 1 (by rfl) ⟨399704, by rfl⟩ : syracuseStep 532939 = 799409) B799409
theorem B238027 : Blo 207808 238027 := bstep (se 1 (by rfl) ⟨178520, by rfl⟩ : syracuseStep 238027 = 357041) B357041
theorem B238135 : Blo 207808 238135 := bstep (se 1 (by rfl) ⟨178601, by rfl⟩ : syracuseStep 238135 = 357203) B357203
theorem B533081 : Blo 207808 533081 := bstep (se 2 (by rfl) ⟨199905, by rfl⟩ : syracuseStep 533081 = 399811) B399811
theorem B1057373 : Blo 207808 1057373 := bstep (se 3 (by rfl) ⟨198257, by rfl⟩ : syracuseStep 1057373 = 396515) B396515
theorem B1352285 : Blo 207808 1352285 := bstep (se 3 (by rfl) ⟨253553, by rfl⟩ : syracuseStep 1352285 = 507107) B507107
theorem B467585 : Blo 207808 467585 := bstep (se 2 (by rfl) ⟨175344, by rfl⟩ : syracuseStep 467585 = 350689) B350689
theorem B402059 : Blo 207808 402059 := bstep (se 1 (by rfl) ⟨301544, by rfl⟩ : syracuseStep 402059 = 603089) B603089
theorem B893699 : Blo 207808 893699 := bstep (se 1 (by rfl) ⟨670274, by rfl⟩ : syracuseStep 893699 = 1340549) B1340549
theorem B467801 : Blo 207808 467801 := bstep (se 2 (by rfl) ⟨175425, by rfl⟩ : syracuseStep 467801 = 350851) B350851
theorem B467891 : Blo 207808 467891 := bstep (se 1 (by rfl) ⟨350918, by rfl⟩ : syracuseStep 467891 = 701837) B701837
theorem B467927 : Blo 207808 467927 := bstep (se 1 (by rfl) ⟨350945, by rfl⟩ : syracuseStep 467927 = 701891) B701891
theorem B468107 : Blo 207808 468107 := bstep (se 1 (by rfl) ⟨351080, by rfl⟩ : syracuseStep 468107 = 702161) B702161
theorem B468161 : Blo 207808 468161 := bstep (se 2 (by rfl) ⟨175560, by rfl⟩ : syracuseStep 468161 = 351121) B351121
theorem B3417461 : Blo 207808 3417461 := bstep (se 5 (by rfl) ⟨160193, by rfl⟩ : syracuseStep 3417461 = 320387) B320387
theorem B533911 : Blo 207808 533911 := bstep (se 1 (by rfl) ⟨400433, by rfl⟩ : syracuseStep 533911 = 800867) B800867
theorem B468377 : Blo 207808 468377 := bstep (se 2 (by rfl) ⟨175641, by rfl⟩ : syracuseStep 468377 = 351283) B351283
theorem B533953 : Blo 207808 533953 := bstep (se 2 (by rfl) ⟨200232, by rfl⟩ : syracuseStep 533953 = 400465) B400465
theorem B468467 : Blo 207808 468467 := bstep (se 1 (by rfl) ⟨351350, by rfl⟩ : syracuseStep 468467 = 702701) B702701
theorem B468503 : Blo 207808 468503 := bstep (se 1 (by rfl) ⟨351377, by rfl⟩ : syracuseStep 468503 = 702755) B702755
theorem B468683 : Blo 207808 468683 := bstep (se 1 (by rfl) ⟨351512, by rfl⟩ : syracuseStep 468683 = 703025) B703025
theorem B468737 : Blo 207808 468737 := bstep (se 2 (by rfl) ⟨175776, by rfl⟩ : syracuseStep 468737 = 351553) B351553
theorem B599831 : Blo 207808 599831 := bstep (se 1 (by rfl) ⟨449873, by rfl⟩ : syracuseStep 599831 = 899747) B899747
theorem B304921 : Blo 207808 304921 := bstep (se 2 (by rfl) ⟨114345, by rfl⟩ : syracuseStep 304921 = 228691) B228691
theorem B534347 : Blo 207808 534347 := bstep (se 1 (by rfl) ⟨400760, by rfl⟩ : syracuseStep 534347 = 801521) B801521
theorem B501707 : Blo 207808 501707 := bstep (se 1 (by rfl) ⟨376280, by rfl⟩ : syracuseStep 501707 = 752561) B752561
theorem B468953 : Blo 207808 468953 := bstep (se 2 (by rfl) ⟨175857, by rfl⟩ : syracuseStep 468953 = 351715) B351715
theorem B796675 : Blo 207808 796675 := bstep (se 1 (by rfl) ⟨597506, by rfl⟩ : syracuseStep 796675 = 1195013) B1195013
theorem B337943 : Blo 207808 337943 := bstep (se 1 (by rfl) ⟨253457, by rfl⟩ : syracuseStep 337943 = 506915) B506915
theorem B469043 : Blo 207808 469043 := bstep (se 1 (by rfl) ⟨351782, by rfl⟩ : syracuseStep 469043 = 703565) B703565
theorem B469079 : Blo 207808 469079 := bstep (se 1 (by rfl) ⟨351809, by rfl⟩ : syracuseStep 469079 = 703619) B703619
theorem B534721 : Blo 207808 534721 := bstep (se 2 (by rfl) ⟨200520, by rfl⟩ : syracuseStep 534721 = 401041) B401041
theorem B469259 : Blo 207808 469259 := bstep (se 1 (by rfl) ⟨351944, by rfl⟩ : syracuseStep 469259 = 703889) B703889
theorem B469271 : Blo 207808 469271 := bstep (se 1 (by rfl) ⟨351953, by rfl⟩ : syracuseStep 469271 = 703907) B703907
theorem B796979 : Blo 207808 796979 := bstep (se 1 (by rfl) ⟨597734, by rfl⟩ : syracuseStep 796979 = 1195469) B1195469
theorem B469313 : Blo 207808 469313 := bstep (se 2 (by rfl) ⟨175992, by rfl⟩ : syracuseStep 469313 = 351985) B351985
theorem B338251 : Blo 207808 338251 := bstep (se 1 (by rfl) ⟨253688, by rfl⟩ : syracuseStep 338251 = 507377) B507377
theorem B469529 : Blo 207808 469529 := bstep (se 2 (by rfl) ⟨176073, by rfl⟩ : syracuseStep 469529 = 352147) B352147
theorem B338507 : Blo 207808 338507 := bstep (se 1 (by rfl) ⟨253880, by rfl⟩ : syracuseStep 338507 = 507761) B507761
theorem B469619 : Blo 207808 469619 := bstep (se 1 (by rfl) ⟨352214, by rfl⟩ : syracuseStep 469619 = 704429) B704429
theorem B469655 : Blo 207808 469655 := bstep (se 1 (by rfl) ⟨352241, by rfl⟩ : syracuseStep 469655 = 704483) B704483
theorem B1059479 : Blo 207808 1059479 := bstep (se 1 (by rfl) ⟨794609, by rfl⟩ : syracuseStep 1059479 = 1589219) B1589219
theorem B535319 : Blo 207808 535319 := bstep (se 1 (by rfl) ⟨401489, by rfl⟩ : syracuseStep 535319 = 802979) B802979
theorem B666443 : Blo 207808 666443 := bstep (se 1 (by rfl) ⟨499832, by rfl⟩ : syracuseStep 666443 = 999665) B999665
theorem B469835 : Blo 207808 469835 := bstep (se 1 (by rfl) ⟨352376, by rfl⟩ : syracuseStep 469835 = 704753) B704753
theorem B469889 : Blo 207808 469889 := bstep (se 2 (by rfl) ⟨176208, by rfl⟩ : syracuseStep 469889 = 352417) B352417
theorem B797633 : Blo 207808 797633 := bstep (se 2 (by rfl) ⟨299112, by rfl⟩ : syracuseStep 797633 = 598225) B598225
theorem B207819 : Blo 207808 207819 := bstep (se 1 (by rfl) ⟨155864, by rfl⟩ : syracuseStep 207819 = 311729) B311729
theorem B207831 : Blo 207808 207831 := bstep (se 1 (by rfl) ⟨155873, by rfl⟩ : syracuseStep 207831 = 311747) B311747
theorem B207851 : Blo 207808 207851 := bstep (se 1 (by rfl) ⟨155888, by rfl⟩ : syracuseStep 207851 = 311777) B311777
theorem B207863 : Blo 207808 207863 := bstep (se 1 (by rfl) ⟨155897, by rfl⟩ : syracuseStep 207863 = 311795) B311795
theorem B207883 : Blo 207808 207883 := bstep (se 1 (by rfl) ⟨155912, by rfl⟩ : syracuseStep 207883 = 311825) B311825
theorem B207895 : Blo 207808 207895 := bstep (se 1 (by rfl) ⟨155921, by rfl⟩ : syracuseStep 207895 = 311843) B311843
theorem B207915 : Blo 207808 207915 := bstep (se 1 (by rfl) ⟨155936, by rfl⟩ : syracuseStep 207915 = 311873) B311873
theorem B207927 : Blo 207808 207927 := bstep (se 1 (by rfl) ⟨155945, by rfl⟩ : syracuseStep 207927 = 311891) B311891
theorem B207947 : Blo 207808 207947 := bstep (se 1 (by rfl) ⟨155960, by rfl⟩ : syracuseStep 207947 = 311921) B311921
theorem B207959 : Blo 207808 207959 := bstep (se 1 (by rfl) ⟨155969, by rfl⟩ : syracuseStep 207959 = 311939) B311939
theorem B470105 : Blo 207808 470105 := bstep (se 2 (by rfl) ⟨176289, by rfl⟩ : syracuseStep 470105 = 352579) B352579
theorem B207979 : Blo 207808 207979 := bstep (se 1 (by rfl) ⟨155984, by rfl⟩ : syracuseStep 207979 = 311969) B311969
theorem B207991 : Blo 207808 207991 := bstep (se 1 (by rfl) ⟨155993, by rfl⟩ : syracuseStep 207991 = 311987) B311987
theorem B208011 : Blo 207808 208011 := bstep (se 1 (by rfl) ⟨156008, by rfl⟩ : syracuseStep 208011 = 312017) B312017
theorem B208023 : Blo 207808 208023 := bstep (se 1 (by rfl) ⟨156017, by rfl⟩ : syracuseStep 208023 = 312035) B312035
theorem B208043 : Blo 207808 208043 := bstep (se 1 (by rfl) ⟨156032, by rfl⟩ : syracuseStep 208043 = 312065) B312065
theorem B470195 : Blo 207808 470195 := bstep (se 1 (by rfl) ⟨352646, by rfl⟩ : syracuseStep 470195 = 705293) B705293
theorem B208055 : Blo 207808 208055 := bstep (se 1 (by rfl) ⟨156041, by rfl⟩ : syracuseStep 208055 = 312083) B312083
theorem B208075 : Blo 207808 208075 := bstep (se 1 (by rfl) ⟨156056, by rfl⟩ : syracuseStep 208075 = 312113) B312113
theorem B208087 : Blo 207808 208087 := bstep (se 1 (by rfl) ⟨156065, by rfl⟩ : syracuseStep 208087 = 312131) B312131
theorem B470231 : Blo 207808 470231 := bstep (se 1 (by rfl) ⟨352673, by rfl⟩ : syracuseStep 470231 = 705347) B705347
theorem B208107 : Blo 207808 208107 := bstep (se 1 (by rfl) ⟨156080, by rfl⟩ : syracuseStep 208107 = 312161) B312161
theorem B208119 : Blo 207808 208119 := bstep (se 1 (by rfl) ⟨156089, by rfl⟩ : syracuseStep 208119 = 312179) B312179
theorem B208139 : Blo 207808 208139 := bstep (se 1 (by rfl) ⟨156104, by rfl⟩ : syracuseStep 208139 = 312209) B312209
theorem B208151 : Blo 207808 208151 := bstep (se 1 (by rfl) ⟨156113, by rfl⟩ : syracuseStep 208151 = 312227) B312227
theorem B208171 : Blo 207808 208171 := bstep (se 1 (by rfl) ⟨156128, by rfl⟩ : syracuseStep 208171 = 312257) B312257
theorem B208183 : Blo 207808 208183 := bstep (se 1 (by rfl) ⟨156137, by rfl⟩ : syracuseStep 208183 = 312275) B312275
theorem B208203 : Blo 207808 208203 := bstep (se 1 (by rfl) ⟨156152, by rfl⟩ : syracuseStep 208203 = 312305) B312305
theorem B208215 : Blo 207808 208215 := bstep (se 1 (by rfl) ⟨156161, by rfl⟩ : syracuseStep 208215 = 312323) B312323
theorem B208235 : Blo 207808 208235 := bstep (se 1 (by rfl) ⟨156176, by rfl⟩ : syracuseStep 208235 = 312353) B312353
theorem B208247 : Blo 207808 208247 := bstep (se 1 (by rfl) ⟨156185, by rfl⟩ : syracuseStep 208247 = 312371) B312371
theorem B208267 : Blo 207808 208267 := bstep (se 1 (by rfl) ⟨156200, by rfl⟩ : syracuseStep 208267 = 312401) B312401
theorem B470411 : Blo 207808 470411 := bstep (se 1 (by rfl) ⟨352808, by rfl⟩ : syracuseStep 470411 = 705617) B705617
theorem B208279 : Blo 207808 208279 := bstep (se 1 (by rfl) ⟨156209, by rfl⟩ : syracuseStep 208279 = 312419) B312419
theorem B208299 : Blo 207808 208299 := bstep (se 1 (by rfl) ⟨156224, by rfl⟩ : syracuseStep 208299 = 312449) B312449
theorem B1191347 : Blo 207808 1191347 := bstep (se 1 (by rfl) ⟨893510, by rfl⟩ : syracuseStep 1191347 = 1787021) B1787021
theorem B208311 : Blo 207808 208311 := bstep (se 1 (by rfl) ⟨156233, by rfl⟩ : syracuseStep 208311 = 312467) B312467
theorem B470465 : Blo 207808 470465 := bstep (se 2 (by rfl) ⟨176424, by rfl⟩ : syracuseStep 470465 = 352849) B352849
theorem B208331 : Blo 207808 208331 := bstep (se 1 (by rfl) ⟨156248, by rfl⟩ : syracuseStep 208331 = 312497) B312497
theorem B208343 : Blo 207808 208343 := bstep (se 1 (by rfl) ⟨156257, by rfl⟩ : syracuseStep 208343 = 312515) B312515
theorem B208363 : Blo 207808 208363 := bstep (se 1 (by rfl) ⟨156272, by rfl⟩ : syracuseStep 208363 = 312545) B312545
theorem B208375 : Blo 207808 208375 := bstep (se 1 (by rfl) ⟨156281, by rfl⟩ : syracuseStep 208375 = 312563) B312563
theorem B208395 : Blo 207808 208395 := bstep (se 1 (by rfl) ⟨156296, by rfl⟩ : syracuseStep 208395 = 312593) B312593
theorem B208407 : Blo 207808 208407 := bstep (se 1 (by rfl) ⟨156305, by rfl⟩ : syracuseStep 208407 = 312611) B312611
theorem B208427 : Blo 207808 208427 := bstep (se 1 (by rfl) ⟨156320, by rfl⟩ : syracuseStep 208427 = 312641) B312641
theorem B208439 : Blo 207808 208439 := bstep (se 1 (by rfl) ⟨156329, by rfl⟩ : syracuseStep 208439 = 312659) B312659
theorem B536129 : Blo 207808 536129 := bstep (se 2 (by rfl) ⟨201048, by rfl⟩ : syracuseStep 536129 = 402097) B402097
theorem B208459 : Blo 207808 208459 := bstep (se 1 (by rfl) ⟨156344, by rfl⟩ : syracuseStep 208459 = 312689) B312689
theorem B208471 : Blo 207808 208471 := bstep (se 1 (by rfl) ⟨156353, by rfl⟩ : syracuseStep 208471 = 312707) B312707
theorem B208491 : Blo 207808 208491 := bstep (se 1 (by rfl) ⟨156368, by rfl⟩ : syracuseStep 208491 = 312737) B312737
theorem B208503 : Blo 207808 208503 := bstep (se 1 (by rfl) ⟨156377, by rfl⟩ : syracuseStep 208503 = 312755) B312755
theorem B208523 : Blo 207808 208523 := bstep (se 1 (by rfl) ⟨156392, by rfl⟩ : syracuseStep 208523 = 312785) B312785
theorem B208535 : Blo 207808 208535 := bstep (se 1 (by rfl) ⟨156401, by rfl⟩ : syracuseStep 208535 = 312803) B312803
theorem B470681 : Blo 207808 470681 := bstep (se 2 (by rfl) ⟨176505, by rfl⟩ : syracuseStep 470681 = 353011) B353011
theorem B208555 : Blo 207808 208555 := bstep (se 1 (by rfl) ⟨156416, by rfl⟩ : syracuseStep 208555 = 312833) B312833
theorem B634547 : Blo 207808 634547 := bstep (se 1 (by rfl) ⟨475910, by rfl⟩ : syracuseStep 634547 = 951821) B951821
theorem B208567 : Blo 207808 208567 := bstep (se 1 (by rfl) ⟨156425, by rfl⟩ : syracuseStep 208567 = 312851) B312851
theorem B208587 : Blo 207808 208587 := bstep (se 1 (by rfl) ⟨156440, by rfl⟩ : syracuseStep 208587 = 312881) B312881
theorem B1584845 : Blo 207808 1584845 := bstep (se 3 (by rfl) ⟨297158, by rfl⟩ : syracuseStep 1584845 = 594317) B594317
theorem B208599 : Blo 207808 208599 := bstep (se 1 (by rfl) ⟨156449, by rfl⟩ : syracuseStep 208599 = 312899) B312899
theorem B208619 : Blo 207808 208619 := bstep (se 1 (by rfl) ⟨156464, by rfl⟩ : syracuseStep 208619 = 312929) B312929
theorem B470771 : Blo 207808 470771 := bstep (se 1 (by rfl) ⟨353078, by rfl⟩ : syracuseStep 470771 = 706157) B706157
theorem B208631 : Blo 207808 208631 := bstep (se 1 (by rfl) ⟨156473, by rfl⟩ : syracuseStep 208631 = 312947) B312947
theorem B208651 : Blo 207808 208651 := bstep (se 1 (by rfl) ⟨156488, by rfl⟩ : syracuseStep 208651 = 312977) B312977
theorem B208663 : Blo 207808 208663 := bstep (se 1 (by rfl) ⟨156497, by rfl⟩ : syracuseStep 208663 = 312995) B312995
theorem B470807 : Blo 207808 470807 := bstep (se 1 (by rfl) ⟨353105, by rfl⟩ : syracuseStep 470807 = 706211) B706211
theorem B896791 : Blo 207808 896791 := bstep (se 1 (by rfl) ⟨672593, by rfl⟩ : syracuseStep 896791 = 1345187) B1345187
theorem B208683 : Blo 207808 208683 := bstep (se 1 (by rfl) ⟨156512, by rfl⟩ : syracuseStep 208683 = 313025) B313025
theorem B208695 : Blo 207808 208695 := bstep (se 1 (by rfl) ⟨156521, by rfl⟩ : syracuseStep 208695 = 313043) B313043
theorem B208715 : Blo 207808 208715 := bstep (se 1 (by rfl) ⟨156536, by rfl⟩ : syracuseStep 208715 = 313073) B313073
theorem B208727 : Blo 207808 208727 := bstep (se 1 (by rfl) ⟨156545, by rfl⟩ : syracuseStep 208727 = 313091) B313091
theorem B208747 : Blo 207808 208747 := bstep (se 1 (by rfl) ⟨156560, by rfl⟩ : syracuseStep 208747 = 313121) B313121
theorem B208759 : Blo 207808 208759 := bstep (se 1 (by rfl) ⟨156569, by rfl⟩ : syracuseStep 208759 = 313139) B313139
theorem B208779 : Blo 207808 208779 := bstep (se 1 (by rfl) ⟨156584, by rfl⟩ : syracuseStep 208779 = 313169) B313169
theorem B208791 : Blo 207808 208791 := bstep (se 1 (by rfl) ⟨156593, by rfl⟩ : syracuseStep 208791 = 313187) B313187
theorem B208811 : Blo 207808 208811 := bstep (se 1 (by rfl) ⟨156608, by rfl⟩ : syracuseStep 208811 = 313217) B313217
theorem B208823 : Blo 207808 208823 := bstep (se 1 (by rfl) ⟨156617, by rfl⟩ : syracuseStep 208823 = 313235) B313235
theorem B208843 : Blo 207808 208843 := bstep (se 1 (by rfl) ⟨156632, by rfl⟩ : syracuseStep 208843 = 313265) B313265
theorem B470987 : Blo 207808 470987 := bstep (se 1 (by rfl) ⟨353240, by rfl⟩ : syracuseStep 470987 = 706481) B706481
theorem B208855 : Blo 207808 208855 := bstep (se 1 (by rfl) ⟨156641, by rfl⟩ : syracuseStep 208855 = 313283) B313283
theorem B208875 : Blo 207808 208875 := bstep (se 1 (by rfl) ⟨156656, by rfl⟩ : syracuseStep 208875 = 313313) B313313
theorem B208887 : Blo 207808 208887 := bstep (se 1 (by rfl) ⟨156665, by rfl⟩ : syracuseStep 208887 = 313331) B313331
theorem B471041 : Blo 207808 471041 := bstep (se 2 (by rfl) ⟨176640, by rfl⟩ : syracuseStep 471041 = 353281) B353281
theorem B208907 : Blo 207808 208907 := bstep (se 1 (by rfl) ⟨156680, by rfl⟩ : syracuseStep 208907 = 313361) B313361
theorem B208919 : Blo 207808 208919 := bstep (se 1 (by rfl) ⟨156689, by rfl⟩ : syracuseStep 208919 = 313379) B313379
theorem B208939 : Blo 207808 208939 := bstep (se 1 (by rfl) ⟨156704, by rfl⟩ : syracuseStep 208939 = 313409) B313409
theorem B208951 : Blo 207808 208951 := bstep (se 1 (by rfl) ⟨156713, by rfl⟩ : syracuseStep 208951 = 313427) B313427
theorem B208971 : Blo 207808 208971 := bstep (se 1 (by rfl) ⟨156728, by rfl⟩ : syracuseStep 208971 = 313457) B313457
theorem B208983 : Blo 207808 208983 := bstep (se 1 (by rfl) ⟨156737, by rfl⟩ : syracuseStep 208983 = 313475) B313475
theorem B209003 : Blo 207808 209003 := bstep (se 1 (by rfl) ⟨156752, by rfl⟩ : syracuseStep 209003 = 313505) B313505
theorem B209015 : Blo 207808 209015 := bstep (se 1 (by rfl) ⟨156761, by rfl⟩ : syracuseStep 209015 = 313523) B313523
theorem B209035 : Blo 207808 209035 := bstep (se 1 (by rfl) ⟨156776, by rfl⟩ : syracuseStep 209035 = 313553) B313553
theorem B209047 : Blo 207808 209047 := bstep (se 1 (by rfl) ⟨156785, by rfl⟩ : syracuseStep 209047 = 313571) B313571
theorem B209067 : Blo 207808 209067 := bstep (se 1 (by rfl) ⟨156800, by rfl⟩ : syracuseStep 209067 = 313601) B313601
theorem B798893 : Blo 207808 798893 := bstep (se 3 (by rfl) ⟨149792, by rfl⟩ : syracuseStep 798893 = 299585) B299585
theorem B1585331 : Blo 207808 1585331 := bstep (se 1 (by rfl) ⟨1188998, by rfl⟩ : syracuseStep 1585331 = 2377997) B2377997
theorem B602291 : Blo 207808 602291 := bstep (se 1 (by rfl) ⟨451718, by rfl⟩ : syracuseStep 602291 = 903437) B903437
theorem B209079 : Blo 207808 209079 := bstep (se 1 (by rfl) ⟨156809, by rfl⟩ : syracuseStep 209079 = 313619) B313619
theorem B209099 : Blo 207808 209099 := bstep (se 1 (by rfl) ⟨156824, by rfl⟩ : syracuseStep 209099 = 313649) B313649
theorem B798923 : Blo 207808 798923 := bstep (se 1 (by rfl) ⟨599192, by rfl⟩ : syracuseStep 798923 = 1198385) B1198385
theorem B209111 : Blo 207808 209111 := bstep (se 1 (by rfl) ⟨156833, by rfl⟩ : syracuseStep 209111 = 313667) B313667
theorem B471257 : Blo 207808 471257 := bstep (se 2 (by rfl) ⟨176721, by rfl⟩ : syracuseStep 471257 = 353443) B353443
theorem B209131 : Blo 207808 209131 := bstep (se 1 (by rfl) ⟨156848, by rfl⟩ : syracuseStep 209131 = 313697) B313697
theorem B209143 : Blo 207808 209143 := bstep (se 1 (by rfl) ⟨156857, by rfl⟩ : syracuseStep 209143 = 313715) B313715
theorem B209163 : Blo 207808 209163 := bstep (se 1 (by rfl) ⟨156872, by rfl⟩ : syracuseStep 209163 = 313745) B313745
theorem B209175 : Blo 207808 209175 := bstep (se 1 (by rfl) ⟨156881, by rfl⟩ : syracuseStep 209175 = 313763) B313763
theorem B209195 : Blo 207808 209195 := bstep (se 1 (by rfl) ⟨156896, by rfl⟩ : syracuseStep 209195 = 313793) B313793
theorem B1356077 : Blo 207808 1356077 := bstep (se 3 (by rfl) ⟨254264, by rfl⟩ : syracuseStep 1356077 = 508529) B508529
theorem B471347 : Blo 207808 471347 := bstep (se 1 (by rfl) ⟨353510, by rfl⟩ : syracuseStep 471347 = 707021) B707021
theorem B209207 : Blo 207808 209207 := bstep (se 1 (by rfl) ⟨156905, by rfl⟩ : syracuseStep 209207 = 313811) B313811
theorem B209227 : Blo 207808 209227 := bstep (se 1 (by rfl) ⟨156920, by rfl⟩ : syracuseStep 209227 = 313841) B313841
theorem B209239 : Blo 207808 209239 := bstep (se 1 (by rfl) ⟨156929, by rfl⟩ : syracuseStep 209239 = 313859) B313859
theorem B471383 : Blo 207808 471383 := bstep (se 1 (by rfl) ⟨353537, by rfl⟩ : syracuseStep 471383 = 707075) B707075
theorem B209259 : Blo 207808 209259 := bstep (se 1 (by rfl) ⟨156944, by rfl⟩ : syracuseStep 209259 = 313889) B313889
theorem B209271 : Blo 207808 209271 := bstep (se 1 (by rfl) ⟨156953, by rfl⟩ : syracuseStep 209271 = 313907) B313907
theorem B209291 : Blo 207808 209291 := bstep (se 1 (by rfl) ⟨156968, by rfl⟩ : syracuseStep 209291 = 313937) B313937
theorem B209303 : Blo 207808 209303 := bstep (se 1 (by rfl) ⟨156977, by rfl⟩ : syracuseStep 209303 = 313955) B313955
theorem B209323 : Blo 207808 209323 := bstep (se 1 (by rfl) ⟨156992, by rfl⟩ : syracuseStep 209323 = 313985) B313985
theorem B668083 : Blo 207808 668083 := bstep (se 1 (by rfl) ⟨501062, by rfl⟩ : syracuseStep 668083 = 1002125) B1002125
theorem B209335 : Blo 207808 209335 := bstep (se 1 (by rfl) ⟨157001, by rfl⟩ : syracuseStep 209335 = 314003) B314003
theorem B209355 : Blo 207808 209355 := bstep (se 1 (by rfl) ⟨157016, by rfl⟩ : syracuseStep 209355 = 314033) B314033
theorem B209367 : Blo 207808 209367 := bstep (se 1 (by rfl) ⟨157025, by rfl⟩ : syracuseStep 209367 = 314051) B314051
theorem B209387 : Blo 207808 209387 := bstep (se 1 (by rfl) ⟨157040, by rfl⟩ : syracuseStep 209387 = 314081) B314081
theorem B209399 : Blo 207808 209399 := bstep (se 1 (by rfl) ⟨157049, by rfl⟩ : syracuseStep 209399 = 314099) B314099
theorem B209419 : Blo 207808 209419 := bstep (se 1 (by rfl) ⟨157064, by rfl⟩ : syracuseStep 209419 = 314129) B314129
theorem B471563 : Blo 207808 471563 := bstep (se 1 (by rfl) ⟨353672, by rfl⟩ : syracuseStep 471563 = 707345) B707345
theorem B3617297 : Blo 207808 3617297 := bstep (se 2 (by rfl) ⟨1356486, by rfl⟩ : syracuseStep 3617297 = 2712973) B2712973
theorem B209431 : Blo 207808 209431 := bstep (se 1 (by rfl) ⟨157073, by rfl⟩ : syracuseStep 209431 = 314147) B314147
theorem B209451 : Blo 207808 209451 := bstep (se 1 (by rfl) ⟨157088, by rfl⟩ : syracuseStep 209451 = 314177) B314177
theorem B209463 : Blo 207808 209463 := bstep (se 1 (by rfl) ⟨157097, by rfl⟩ : syracuseStep 209463 = 314195) B314195
theorem B471617 : Blo 207808 471617 := bstep (se 2 (by rfl) ⟨176856, by rfl⟩ : syracuseStep 471617 = 353713) B353713
theorem B209483 : Blo 207808 209483 := bstep (se 1 (by rfl) ⟨157112, by rfl⟩ : syracuseStep 209483 = 314225) B314225
theorem B2699851 : Blo 207808 2699851 := bstep (se 1 (by rfl) ⟨2024888, by rfl⟩ : syracuseStep 2699851 = 4049777) B4049777
theorem B209495 : Blo 207808 209495 := bstep (se 1 (by rfl) ⟨157121, by rfl⟩ : syracuseStep 209495 = 314243) B314243
theorem B209515 : Blo 207808 209515 := bstep (se 1 (by rfl) ⟨157136, by rfl⟩ : syracuseStep 209515 = 314273) B314273
theorem B209527 : Blo 207808 209527 := bstep (se 1 (by rfl) ⟨157145, by rfl⟩ : syracuseStep 209527 = 314291) B314291
theorem B209547 : Blo 207808 209547 := bstep (se 1 (by rfl) ⟨157160, by rfl⟩ : syracuseStep 209547 = 314321) B314321
theorem B209559 : Blo 207808 209559 := bstep (se 1 (by rfl) ⟨157169, by rfl⟩ : syracuseStep 209559 = 314339) B314339
theorem B209579 : Blo 207808 209579 := bstep (se 1 (by rfl) ⟨157184, by rfl⟩ : syracuseStep 209579 = 314369) B314369
theorem B209591 : Blo 207808 209591 := bstep (se 1 (by rfl) ⟨157193, by rfl⟩ : syracuseStep 209591 = 314387) B314387
theorem B209611 : Blo 207808 209611 := bstep (se 1 (by rfl) ⟨157208, by rfl⟩ : syracuseStep 209611 = 314417) B314417
theorem B209623 : Blo 207808 209623 := bstep (se 1 (by rfl) ⟨157217, by rfl⟩ : syracuseStep 209623 = 314435) B314435
theorem B209643 : Blo 207808 209643 := bstep (se 1 (by rfl) ⟨157232, by rfl⟩ : syracuseStep 209643 = 314465) B314465
theorem B209655 : Blo 207808 209655 := bstep (se 1 (by rfl) ⟨157241, by rfl⟩ : syracuseStep 209655 = 314483) B314483
theorem B209675 : Blo 207808 209675 := bstep (se 1 (by rfl) ⟨157256, by rfl⟩ : syracuseStep 209675 = 314513) B314513
theorem B209687 : Blo 207808 209687 := bstep (se 1 (by rfl) ⟨157265, by rfl⟩ : syracuseStep 209687 = 314531) B314531
theorem B471833 : Blo 207808 471833 := bstep (se 2 (by rfl) ⟨176937, by rfl⟩ : syracuseStep 471833 = 353875) B353875
theorem B209707 : Blo 207808 209707 := bstep (se 1 (by rfl) ⟨157280, by rfl⟩ : syracuseStep 209707 = 314561) B314561
theorem B209719 : Blo 207808 209719 := bstep (se 1 (by rfl) ⟨157289, by rfl⟩ : syracuseStep 209719 = 314579) B314579
theorem B209739 : Blo 207808 209739 := bstep (se 1 (by rfl) ⟨157304, by rfl⟩ : syracuseStep 209739 = 314609) B314609
theorem B209751 : Blo 207808 209751 := bstep (se 1 (by rfl) ⟨157313, by rfl⟩ : syracuseStep 209751 = 314627) B314627
theorem B799577 : Blo 207808 799577 := bstep (se 2 (by rfl) ⟨299841, by rfl⟩ : syracuseStep 799577 = 599683) B599683
theorem B1192805 : Blo 207808 1192805 := bstep (se 4 (by rfl) ⟨111825, by rfl⟩ : syracuseStep 1192805 = 223651) B223651
theorem B209771 : Blo 207808 209771 := bstep (se 1 (by rfl) ⟨157328, by rfl⟩ : syracuseStep 209771 = 314657) B314657
theorem B471923 : Blo 207808 471923 := bstep (se 1 (by rfl) ⟨353942, by rfl⟩ : syracuseStep 471923 = 707885) B707885
theorem B209783 : Blo 207808 209783 := bstep (se 1 (by rfl) ⟨157337, by rfl⟩ : syracuseStep 209783 = 314675) B314675
theorem B209803 : Blo 207808 209803 := bstep (se 1 (by rfl) ⟨157352, by rfl⟩ : syracuseStep 209803 = 314705) B314705
theorem B471959 : Blo 207808 471959 := bstep (se 1 (by rfl) ⟨353969, by rfl⟩ : syracuseStep 471959 = 707939) B707939
theorem B209815 : Blo 207808 209815 := bstep (se 1 (by rfl) ⟨157361, by rfl⟩ : syracuseStep 209815 = 314723) B314723
theorem B209835 : Blo 207808 209835 := bstep (se 1 (by rfl) ⟨157376, by rfl⟩ : syracuseStep 209835 = 314753) B314753
theorem B209847 : Blo 207808 209847 := bstep (se 1 (by rfl) ⟨157385, by rfl⟩ : syracuseStep 209847 = 314771) B314771
theorem B209867 : Blo 207808 209867 := bstep (se 1 (by rfl) ⟨157400, by rfl⟩ : syracuseStep 209867 = 314801) B314801
theorem B209879 : Blo 207808 209879 := bstep (se 1 (by rfl) ⟨157409, by rfl⟩ : syracuseStep 209879 = 314819) B314819
theorem B701405 : Blo 207808 701405 := bstep (se 3 (by rfl) ⟨131513, by rfl⟩ : syracuseStep 701405 = 263027) B263027
theorem B209899 : Blo 207808 209899 := bstep (se 1 (by rfl) ⟨157424, by rfl⟩ : syracuseStep 209899 = 314849) B314849
theorem B209911 : Blo 207808 209911 := bstep (se 1 (by rfl) ⟨157433, by rfl⟩ : syracuseStep 209911 = 314867) B314867
theorem B209931 : Blo 207808 209931 := bstep (se 1 (by rfl) ⟨157448, by rfl⟩ : syracuseStep 209931 = 314897) B314897
theorem B209943 : Blo 207808 209943 := bstep (se 1 (by rfl) ⟨157457, by rfl⟩ : syracuseStep 209943 = 314915) B314915
theorem B209963 : Blo 207808 209963 := bstep (se 1 (by rfl) ⟨157472, by rfl⟩ : syracuseStep 209963 = 314945) B314945
theorem B209975 : Blo 207808 209975 := bstep (se 1 (by rfl) ⟨157481, by rfl⟩ : syracuseStep 209975 = 314963) B314963
theorem B635969 : Blo 207808 635969 := bstep (se 2 (by rfl) ⟨238488, by rfl⟩ : syracuseStep 635969 = 476977) B476977
theorem B472139 : Blo 207808 472139 := bstep (se 1 (by rfl) ⟨354104, by rfl⟩ : syracuseStep 472139 = 708209) B708209
theorem B209995 : Blo 207808 209995 := bstep (se 1 (by rfl) ⟨157496, by rfl⟩ : syracuseStep 209995 = 314993) B314993
theorem B210007 : Blo 207808 210007 := bstep (se 1 (by rfl) ⟨157505, by rfl⟩ : syracuseStep 210007 = 315011) B315011
theorem B210027 : Blo 207808 210027 := bstep (se 1 (by rfl) ⟨157520, by rfl⟩ : syracuseStep 210027 = 315041) B315041
theorem B210039 : Blo 207808 210039 := bstep (se 1 (by rfl) ⟨157529, by rfl⟩ : syracuseStep 210039 = 315059) B315059
theorem B472193 : Blo 207808 472193 := bstep (se 2 (by rfl) ⟨177072, by rfl⟩ : syracuseStep 472193 = 354145) B354145
theorem B210059 : Blo 207808 210059 := bstep (se 1 (by rfl) ⟨157544, by rfl⟩ : syracuseStep 210059 = 315089) B315089
theorem B210071 : Blo 207808 210071 := bstep (se 1 (by rfl) ⟨157553, by rfl⟩ : syracuseStep 210071 = 315107) B315107
theorem B799895 : Blo 207808 799895 := bstep (se 1 (by rfl) ⟨599921, by rfl⟩ : syracuseStep 799895 = 1199843) B1199843
theorem B210091 : Blo 207808 210091 := bstep (se 1 (by rfl) ⟨157568, by rfl⟩ : syracuseStep 210091 = 315137) B315137
theorem B210103 : Blo 207808 210103 := bstep (se 1 (by rfl) ⟨157577, by rfl⟩ : syracuseStep 210103 = 315155) B315155
theorem B210123 : Blo 207808 210123 := bstep (se 1 (by rfl) ⟨157592, by rfl⟩ : syracuseStep 210123 = 315185) B315185
theorem B210135 : Blo 207808 210135 := bstep (se 1 (by rfl) ⟨157601, by rfl⟩ : syracuseStep 210135 = 315203) B315203
theorem B210155 : Blo 207808 210155 := bstep (se 1 (by rfl) ⟨157616, by rfl⟩ : syracuseStep 210155 = 315233) B315233
theorem B210167 : Blo 207808 210167 := bstep (se 1 (by rfl) ⟨157625, by rfl⟩ : syracuseStep 210167 = 315251) B315251
theorem B210187 : Blo 207808 210187 := bstep (se 1 (by rfl) ⟨157640, by rfl⟩ : syracuseStep 210187 = 315281) B315281
theorem B210199 : Blo 207808 210199 := bstep (se 1 (by rfl) ⟨157649, by rfl⟩ : syracuseStep 210199 = 315299) B315299
theorem B210219 : Blo 207808 210219 := bstep (se 1 (by rfl) ⟨157664, by rfl⟩ : syracuseStep 210219 = 315329) B315329
theorem B210231 : Blo 207808 210231 := bstep (se 1 (by rfl) ⟨157673, by rfl⟩ : syracuseStep 210231 = 315347) B315347
theorem B1160513 : Blo 207808 1160513 := bstep (se 2 (by rfl) ⟨435192, by rfl⟩ : syracuseStep 1160513 = 870385) B870385
theorem B210251 : Blo 207808 210251 := bstep (se 1 (by rfl) ⟨157688, by rfl⟩ : syracuseStep 210251 = 315377) B315377
theorem B210263 : Blo 207808 210263 := bstep (se 1 (by rfl) ⟨157697, by rfl⟩ : syracuseStep 210263 = 315395) B315395
theorem B669017 : Blo 207808 669017 := bstep (se 2 (by rfl) ⟨250881, by rfl⟩ : syracuseStep 669017 = 501763) B501763
theorem B472409 : Blo 207808 472409 := bstep (se 2 (by rfl) ⟨177153, by rfl⟩ : syracuseStep 472409 = 354307) B354307
theorem B210283 : Blo 207808 210283 := bstep (se 1 (by rfl) ⟨157712, by rfl⟩ : syracuseStep 210283 = 315425) B315425
theorem B210295 : Blo 207808 210295 := bstep (se 1 (by rfl) ⟨157721, by rfl⟩ : syracuseStep 210295 = 315443) B315443
theorem B210315 : Blo 207808 210315 := bstep (se 1 (by rfl) ⟨157736, by rfl⟩ : syracuseStep 210315 = 315473) B315473
theorem B210327 : Blo 207808 210327 := bstep (se 1 (by rfl) ⟨157745, by rfl⟩ : syracuseStep 210327 = 315491) B315491
theorem B210347 : Blo 207808 210347 := bstep (se 1 (by rfl) ⟨157760, by rfl⟩ : syracuseStep 210347 = 315521) B315521
theorem B472499 : Blo 207808 472499 := bstep (se 1 (by rfl) ⟨354374, by rfl⟩ : syracuseStep 472499 = 708749) B708749
theorem B210359 : Blo 207808 210359 := bstep (se 1 (by rfl) ⟨157769, by rfl⟩ : syracuseStep 210359 = 315539) B315539
theorem B210379 : Blo 207808 210379 := bstep (se 1 (by rfl) ⟨157784, by rfl⟩ : syracuseStep 210379 = 315569) B315569
theorem B472535 : Blo 207808 472535 := bstep (se 1 (by rfl) ⟨354401, by rfl⟩ : syracuseStep 472535 = 708803) B708803
theorem B210391 : Blo 207808 210391 := bstep (se 1 (by rfl) ⟨157793, by rfl⟩ : syracuseStep 210391 = 315587) B315587
theorem B210411 : Blo 207808 210411 := bstep (se 1 (by rfl) ⟨157808, by rfl⟩ : syracuseStep 210411 = 315617) B315617
theorem B210423 : Blo 207808 210423 := bstep (se 1 (by rfl) ⟨157817, by rfl⟩ : syracuseStep 210423 = 315635) B315635
theorem B210443 : Blo 207808 210443 := bstep (se 1 (by rfl) ⟨157832, by rfl⟩ : syracuseStep 210443 = 315665) B315665
theorem B210455 : Blo 207808 210455 := bstep (se 1 (by rfl) ⟨157841, by rfl⟩ : syracuseStep 210455 = 315683) B315683
theorem B210475 : Blo 207808 210475 := bstep (se 1 (by rfl) ⟨157856, by rfl⟩ : syracuseStep 210475 = 315713) B315713
theorem B210487 : Blo 207808 210487 := bstep (se 1 (by rfl) ⟨157865, by rfl⟩ : syracuseStep 210487 = 315731) B315731
theorem B210507 : Blo 207808 210507 := bstep (se 1 (by rfl) ⟨157880, by rfl⟩ : syracuseStep 210507 = 315761) B315761
theorem B210519 : Blo 207808 210519 := bstep (se 1 (by rfl) ⟨157889, by rfl⟩ : syracuseStep 210519 = 315779) B315779
theorem B1586789 : Blo 207808 1586789 := bstep (se 4 (by rfl) ⟨148761, by rfl⟩ : syracuseStep 1586789 = 297523) B297523
theorem B210539 : Blo 207808 210539 := bstep (se 1 (by rfl) ⟨157904, by rfl⟩ : syracuseStep 210539 = 315809) B315809
theorem B210551 : Blo 207808 210551 := bstep (se 1 (by rfl) ⟨157913, by rfl⟩ : syracuseStep 210551 = 315827) B315827
theorem B472715 : Blo 207808 472715 := bstep (se 1 (by rfl) ⟨354536, by rfl⟩ : syracuseStep 472715 = 709073) B709073
theorem B210571 : Blo 207808 210571 := bstep (se 1 (by rfl) ⟨157928, by rfl⟩ : syracuseStep 210571 = 315857) B315857
theorem B210583 : Blo 207808 210583 := bstep (se 1 (by rfl) ⟨157937, by rfl⟩ : syracuseStep 210583 = 315875) B315875
theorem B210603 : Blo 207808 210603 := bstep (se 1 (by rfl) ⟨157952, by rfl⟩ : syracuseStep 210603 = 315905) B315905
theorem B210615 : Blo 207808 210615 := bstep (se 1 (by rfl) ⟨157961, by rfl⟩ : syracuseStep 210615 = 315923) B315923
theorem B669377 : Blo 207808 669377 := bstep (se 2 (by rfl) ⟨251016, by rfl⟩ : syracuseStep 669377 = 502033) B502033
theorem B472769 : Blo 207808 472769 := bstep (se 2 (by rfl) ⟨177288, by rfl⟩ : syracuseStep 472769 = 354577) B354577
theorem B210635 : Blo 207808 210635 := bstep (se 1 (by rfl) ⟨157976, by rfl⟩ : syracuseStep 210635 = 315953) B315953
theorem B210647 : Blo 207808 210647 := bstep (se 1 (by rfl) ⟨157985, by rfl⟩ : syracuseStep 210647 = 315971) B315971
theorem B210667 : Blo 207808 210667 := bstep (se 1 (by rfl) ⟨158000, by rfl⟩ : syracuseStep 210667 = 316001) B316001
theorem B210679 : Blo 207808 210679 := bstep (se 1 (by rfl) ⟨158009, by rfl⟩ : syracuseStep 210679 = 316019) B316019
theorem B210699 : Blo 207808 210699 := bstep (se 1 (by rfl) ⟨158024, by rfl⟩ : syracuseStep 210699 = 316049) B316049
theorem B210711 : Blo 207808 210711 := bstep (se 1 (by rfl) ⟨158033, by rfl⟩ : syracuseStep 210711 = 316067) B316067
theorem B210731 : Blo 207808 210731 := bstep (se 1 (by rfl) ⟨158048, by rfl⟩ : syracuseStep 210731 = 316097) B316097
theorem B800563 : Blo 207808 800563 := bstep (se 1 (by rfl) ⟨600422, by rfl⟩ : syracuseStep 800563 = 1200845) B1200845
theorem B210743 : Blo 207808 210743 := bstep (se 1 (by rfl) ⟨158057, by rfl⟩ : syracuseStep 210743 = 316115) B316115
theorem B210763 : Blo 207808 210763 := bstep (se 1 (by rfl) ⟨158072, by rfl⟩ : syracuseStep 210763 = 316145) B316145
theorem B210775 : Blo 207808 210775 := bstep (se 1 (by rfl) ⟨158081, by rfl⟩ : syracuseStep 210775 = 316163) B316163
theorem B210795 : Blo 207808 210795 := bstep (se 1 (by rfl) ⟨158096, by rfl⟩ : syracuseStep 210795 = 316193) B316193
theorem B210807 : Blo 207808 210807 := bstep (se 1 (by rfl) ⟨158105, by rfl⟩ : syracuseStep 210807 = 316211) B316211
theorem B210827 : Blo 207808 210827 := bstep (se 1 (by rfl) ⟨158120, by rfl⟩ : syracuseStep 210827 = 316241) B316241
theorem B210839 : Blo 207808 210839 := bstep (se 1 (by rfl) ⟨158129, by rfl⟩ : syracuseStep 210839 = 316259) B316259
theorem B472985 : Blo 207808 472985 := bstep (se 2 (by rfl) ⟨177369, by rfl⟩ : syracuseStep 472985 = 354739) B354739
theorem B210859 : Blo 207808 210859 := bstep (se 1 (by rfl) ⟨158144, by rfl⟩ : syracuseStep 210859 = 316289) B316289
theorem B210871 : Blo 207808 210871 := bstep (se 1 (by rfl) ⟨158153, by rfl⟩ : syracuseStep 210871 = 316307) B316307
theorem B210891 : Blo 207808 210891 := bstep (se 1 (by rfl) ⟨158168, by rfl⟩ : syracuseStep 210891 = 316337) B316337
theorem B210903 : Blo 207808 210903 := bstep (se 1 (by rfl) ⟨158177, by rfl⟩ : syracuseStep 210903 = 316355) B316355
theorem B210923 : Blo 207808 210923 := bstep (se 1 (by rfl) ⟨158192, by rfl⟩ : syracuseStep 210923 = 316385) B316385
theorem B473075 : Blo 207808 473075 := bstep (se 1 (by rfl) ⟨354806, by rfl⟩ : syracuseStep 473075 = 709613) B709613
theorem B210935 : Blo 207808 210935 := bstep (se 1 (by rfl) ⟨158201, by rfl⟩ : syracuseStep 210935 = 316403) B316403
theorem B374795 : Blo 207808 374795 := bstep (se 1 (by rfl) ⟨281096, by rfl⟩ : syracuseStep 374795 = 562193) B562193
theorem B210955 : Blo 207808 210955 := bstep (se 1 (by rfl) ⟨158216, by rfl⟩ : syracuseStep 210955 = 316433) B316433
theorem B473111 : Blo 207808 473111 := bstep (se 1 (by rfl) ⟨354833, by rfl⟩ : syracuseStep 473111 = 709667) B709667
theorem B210967 : Blo 207808 210967 := bstep (se 1 (by rfl) ⟨158225, by rfl⟩ : syracuseStep 210967 = 316451) B316451
theorem B210987 : Blo 207808 210987 := bstep (se 1 (by rfl) ⟨158240, by rfl⟩ : syracuseStep 210987 = 316481) B316481
theorem B210999 : Blo 207808 210999 := bstep (se 1 (by rfl) ⟨158249, by rfl⟩ : syracuseStep 210999 = 316499) B316499
theorem B702539 : Blo 207808 702539 := bstep (se 1 (by rfl) ⟨526904, by rfl⟩ : syracuseStep 702539 = 1053809) B1053809
theorem B1587275 : Blo 207808 1587275 := bstep (se 1 (by rfl) ⟨1190456, by rfl⟩ : syracuseStep 1587275 = 2380913) B2380913
theorem B211019 : Blo 207808 211019 := bstep (se 1 (by rfl) ⟨158264, by rfl⟩ : syracuseStep 211019 = 316529) B316529
theorem B211031 : Blo 207808 211031 := bstep (se 1 (by rfl) ⟨158273, by rfl⟩ : syracuseStep 211031 = 316547) B316547
theorem B211051 : Blo 207808 211051 := bstep (se 1 (by rfl) ⟨158288, by rfl⟩ : syracuseStep 211051 = 316577) B316577
theorem B211063 : Blo 207808 211063 := bstep (se 1 (by rfl) ⟨158297, by rfl⟩ : syracuseStep 211063 = 316595) B316595
theorem B1063043 : Blo 207808 1063043 := bstep (se 1 (by rfl) ⟨797282, by rfl⟩ : syracuseStep 1063043 = 1594565) B1594565
theorem B211083 : Blo 207808 211083 := bstep (se 1 (by rfl) ⟨158312, by rfl⟩ : syracuseStep 211083 = 316625) B316625
theorem B211095 : Blo 207808 211095 := bstep (se 1 (by rfl) ⟨158321, by rfl⟩ : syracuseStep 211095 = 316643) B316643
theorem B211115 : Blo 207808 211115 := bstep (se 1 (by rfl) ⟨158336, by rfl⟩ : syracuseStep 211115 = 316673) B316673
theorem B211127 : Blo 207808 211127 := bstep (se 1 (by rfl) ⟨158345, by rfl⟩ : syracuseStep 211127 = 316691) B316691
theorem B473291 : Blo 207808 473291 := bstep (se 1 (by rfl) ⟨354968, by rfl⟩ : syracuseStep 473291 = 709937) B709937
theorem B211147 : Blo 207808 211147 := bstep (se 1 (by rfl) ⟨158360, by rfl⟩ : syracuseStep 211147 = 316721) B316721
theorem B211159 : Blo 207808 211159 := bstep (se 1 (by rfl) ⟨158369, by rfl⟩ : syracuseStep 211159 = 316739) B316739
theorem B211179 : Blo 207808 211179 := bstep (se 1 (by rfl) ⟨158384, by rfl⟩ : syracuseStep 211179 = 316769) B316769
theorem B211191 : Blo 207808 211191 := bstep (se 1 (by rfl) ⟨158393, by rfl⟩ : syracuseStep 211191 = 316787) B316787
theorem B473345 : Blo 207808 473345 := bstep (se 2 (by rfl) ⟨177504, by rfl⟩ : syracuseStep 473345 = 355009) B355009
theorem B211211 : Blo 207808 211211 := bstep (se 1 (by rfl) ⟨158408, by rfl⟩ : syracuseStep 211211 = 316817) B316817
theorem B211223 : Blo 207808 211223 := bstep (se 1 (by rfl) ⟨158417, by rfl⟩ : syracuseStep 211223 = 316835) B316835
theorem B211243 : Blo 207808 211243 := bstep (se 1 (by rfl) ⟨158432, by rfl⟩ : syracuseStep 211243 = 316865) B316865
theorem B211255 : Blo 207808 211255 := bstep (se 1 (by rfl) ⟨158441, by rfl⟩ : syracuseStep 211255 = 316883) B316883
theorem B211275 : Blo 207808 211275 := bstep (se 1 (by rfl) ⟨158456, by rfl⟩ : syracuseStep 211275 = 316913) B316913
theorem B211287 : Blo 207808 211287 := bstep (se 1 (by rfl) ⟨158465, by rfl⟩ : syracuseStep 211287 = 316931) B316931
theorem B702809 : Blo 207808 702809 := bstep (se 2 (by rfl) ⟨263553, by rfl⟩ : syracuseStep 702809 = 527107) B527107
theorem B211307 : Blo 207808 211307 := bstep (se 1 (by rfl) ⟨158480, by rfl⟩ : syracuseStep 211307 = 316961) B316961
theorem B211319 : Blo 207808 211319 := bstep (se 1 (by rfl) ⟨158489, by rfl⟩ : syracuseStep 211319 = 316979) B316979
theorem B211339 : Blo 207808 211339 := bstep (se 1 (by rfl) ⟨158504, by rfl⟩ : syracuseStep 211339 = 317009) B317009
theorem B211351 : Blo 207808 211351 := bstep (se 1 (by rfl) ⟨158513, by rfl⟩ : syracuseStep 211351 = 317027) B317027
theorem B211371 : Blo 207808 211371 := bstep (se 1 (by rfl) ⟨158528, by rfl⟩ : syracuseStep 211371 = 317057) B317057
theorem B211383 : Blo 207808 211383 := bstep (se 1 (by rfl) ⟨158537, by rfl⟩ : syracuseStep 211383 = 317075) B317075
theorem B211403 : Blo 207808 211403 := bstep (se 1 (by rfl) ⟨158552, by rfl⟩ : syracuseStep 211403 = 317105) B317105
theorem B211415 : Blo 207808 211415 := bstep (se 1 (by rfl) ⟨158561, by rfl⟩ : syracuseStep 211415 = 317123) B317123
theorem B473561 : Blo 207808 473561 := bstep (se 2 (by rfl) ⟨177585, by rfl⟩ : syracuseStep 473561 = 355171) B355171
theorem B211435 : Blo 207808 211435 := bstep (se 1 (by rfl) ⟨158576, by rfl⟩ : syracuseStep 211435 = 317153) B317153
theorem B211447 : Blo 207808 211447 := bstep (se 1 (by rfl) ⟨158585, by rfl⟩ : syracuseStep 211447 = 317171) B317171
theorem B211467 : Blo 207808 211467 := bstep (se 1 (by rfl) ⟨158600, by rfl⟩ : syracuseStep 211467 = 317201) B317201
theorem B10271245 : Blo 207808 10271245 := bstep (se 3 (by rfl) ⟨1925858, by rfl⟩ : syracuseStep 10271245 = 3851717) B3851717
theorem B211479 : Blo 207808 211479 := bstep (se 1 (by rfl) ⟨158609, by rfl⟩ : syracuseStep 211479 = 317219) B317219
theorem B211499 : Blo 207808 211499 := bstep (se 1 (by rfl) ⟨158624, by rfl⟩ : syracuseStep 211499 = 317249) B317249
theorem B473651 : Blo 207808 473651 := bstep (se 1 (by rfl) ⟨355238, by rfl⟩ : syracuseStep 473651 = 710477) B710477
theorem B211511 : Blo 207808 211511 := bstep (se 1 (by rfl) ⟨158633, by rfl⟩ : syracuseStep 211511 = 317267) B317267
theorem B211531 : Blo 207808 211531 := bstep (se 1 (by rfl) ⟨158648, by rfl⟩ : syracuseStep 211531 = 317297) B317297
theorem B473687 : Blo 207808 473687 := bstep (se 1 (by rfl) ⟨355265, by rfl⟩ : syracuseStep 473687 = 710531) B710531
theorem B211543 : Blo 207808 211543 := bstep (se 1 (by rfl) ⟨158657, by rfl⟩ : syracuseStep 211543 = 317315) B317315
theorem B899677 : Blo 207808 899677 := bstep (se 3 (by rfl) ⟨168689, by rfl⟩ : syracuseStep 899677 = 337379) B337379
theorem B211563 : Blo 207808 211563 := bstep (se 1 (by rfl) ⟨158672, by rfl⟩ : syracuseStep 211563 = 317345) B317345
theorem B211575 : Blo 207808 211575 := bstep (se 1 (by rfl) ⟨158681, by rfl⟩ : syracuseStep 211575 = 317363) B317363
theorem B211595 : Blo 207808 211595 := bstep (se 1 (by rfl) ⟨158696, by rfl⟩ : syracuseStep 211595 = 317393) B317393
theorem B211607 : Blo 207808 211607 := bstep (se 1 (by rfl) ⟨158705, by rfl⟩ : syracuseStep 211607 = 317411) B317411
theorem B211627 : Blo 207808 211627 := bstep (se 1 (by rfl) ⟨158720, by rfl⟩ : syracuseStep 211627 = 317441) B317441
theorem B211639 : Blo 207808 211639 := bstep (se 1 (by rfl) ⟨158729, by rfl⟩ : syracuseStep 211639 = 317459) B317459
theorem B211659 : Blo 207808 211659 := bstep (se 1 (by rfl) ⟨158744, by rfl⟩ : syracuseStep 211659 = 317489) B317489
theorem B211671 : Blo 207808 211671 := bstep (se 1 (by rfl) ⟨158753, by rfl⟩ : syracuseStep 211671 = 317507) B317507
theorem B211691 : Blo 207808 211691 := bstep (se 1 (by rfl) ⟨158768, by rfl⟩ : syracuseStep 211691 = 317537) B317537
theorem B211703 : Blo 207808 211703 := bstep (se 1 (by rfl) ⟨158777, by rfl⟩ : syracuseStep 211703 = 317555) B317555
theorem B473867 : Blo 207808 473867 := bstep (se 1 (by rfl) ⟨355400, by rfl⟩ : syracuseStep 473867 = 710801) B710801
theorem B211723 : Blo 207808 211723 := bstep (se 1 (by rfl) ⟨158792, by rfl⟩ : syracuseStep 211723 = 317585) B317585
theorem B211735 : Blo 207808 211735 := bstep (se 1 (by rfl) ⟨158801, by rfl⟩ : syracuseStep 211735 = 317603) B317603
theorem B211755 : Blo 207808 211755 := bstep (se 1 (by rfl) ⟨158816, by rfl⟩ : syracuseStep 211755 = 317633) B317633
theorem B211767 : Blo 207808 211767 := bstep (se 1 (by rfl) ⟨158825, by rfl⟩ : syracuseStep 211767 = 317651) B317651
theorem B473921 : Blo 207808 473921 := bstep (se 2 (by rfl) ⟨177720, by rfl⟩ : syracuseStep 473921 = 355441) B355441
theorem B211787 : Blo 207808 211787 := bstep (se 1 (by rfl) ⟨158840, by rfl⟩ : syracuseStep 211787 = 317681) B317681
theorem B211799 : Blo 207808 211799 := bstep (se 1 (by rfl) ⟨158849, by rfl⟩ : syracuseStep 211799 = 317699) B317699
theorem B1358693 : Blo 207808 1358693 := bstep (se 4 (by rfl) ⟨127377, by rfl⟩ : syracuseStep 1358693 = 254755) B254755
theorem B801809 : Blo 207808 801809 := bstep (se 2 (by rfl) ⟨300678, by rfl⟩ : syracuseStep 801809 = 601357) B601357
theorem B703511 : Blo 207808 703511 := bstep (se 1 (by rfl) ⟨527633, by rfl⟩ : syracuseStep 703511 = 1055267) B1055267
theorem B474137 : Blo 207808 474137 := bstep (se 2 (by rfl) ⟨177801, by rfl⟩ : syracuseStep 474137 = 355603) B355603
theorem B474227 : Blo 207808 474227 := bstep (se 1 (by rfl) ⟨355670, by rfl⟩ : syracuseStep 474227 = 711341) B711341
theorem B5717143 : Blo 207808 5717143 := bstep (se 1 (by rfl) ⟨4287857, by rfl⟩ : syracuseStep 5717143 = 8575715) B8575715
theorem B474263 : Blo 207808 474263 := bstep (se 1 (by rfl) ⟨355697, by rfl⟩ : syracuseStep 474263 = 711395) B711395
theorem B474443 : Blo 207808 474443 := bstep (se 1 (by rfl) ⟨355832, by rfl⟩ : syracuseStep 474443 = 711665) B711665
theorem B474497 : Blo 207808 474497 := bstep (se 2 (by rfl) ⟨177936, by rfl⟩ : syracuseStep 474497 = 355873) B355873
theorem B900497 : Blo 207808 900497 := bstep (se 2 (by rfl) ⟨337686, by rfl⟩ : syracuseStep 900497 = 675373) B675373
theorem B704051 : Blo 207808 704051 := bstep (se 1 (by rfl) ⟨528038, by rfl⟩ : syracuseStep 704051 = 1056077) B1056077
theorem B474713 : Blo 207808 474713 := bstep (se 2 (by rfl) ⟨178017, by rfl⟩ : syracuseStep 474713 = 356035) B356035
theorem B474803 : Blo 207808 474803 := bstep (se 1 (by rfl) ⟨356102, by rfl⟩ : syracuseStep 474803 = 712205) B712205
theorem B802507 : Blo 207808 802507 := bstep (se 1 (by rfl) ⟨601880, by rfl⟩ : syracuseStep 802507 = 1203761) B1203761
theorem B474839 : Blo 207808 474839 := bstep (se 1 (by rfl) ⟨356129, by rfl⟩ : syracuseStep 474839 = 712259) B712259
theorem B704321 : Blo 207808 704321 := bstep (se 2 (by rfl) ⟨264120, by rfl⟩ : syracuseStep 704321 = 528241) B528241
theorem B475019 : Blo 207808 475019 := bstep (se 1 (by rfl) ⟨356264, by rfl⟩ : syracuseStep 475019 = 712529) B712529
theorem B475073 : Blo 207808 475073 := bstep (se 2 (by rfl) ⟨178152, by rfl⟩ : syracuseStep 475073 = 356305) B356305
theorem B802781 : Blo 207808 802781 := bstep (se 3 (by rfl) ⟨150521, by rfl⟩ : syracuseStep 802781 = 301043) B301043
theorem B901165 : Blo 207808 901165 := bstep (se 3 (by rfl) ⟨168968, by rfl⟩ : syracuseStep 901165 = 337937) B337937
theorem B3653707 : Blo 207808 3653707 := bstep (se 1 (by rfl) ⟨2740280, by rfl⟩ : syracuseStep 3653707 = 5480561) B5480561
theorem B475289 : Blo 207808 475289 := bstep (se 2 (by rfl) ⟨178233, by rfl⟩ : syracuseStep 475289 = 356467) B356467
theorem B5062837 : Blo 207808 5062837 := bstep (se 5 (by rfl) ⟨237320, by rfl⟩ : syracuseStep 5062837 = 474641) B474641
theorem B475379 : Blo 207808 475379 := bstep (se 1 (by rfl) ⟨356534, by rfl⟩ : syracuseStep 475379 = 713069) B713069
theorem B475415 : Blo 207808 475415 := bstep (se 1 (by rfl) ⟨356561, by rfl⟩ : syracuseStep 475415 = 713123) B713123
theorem B704861 : Blo 207808 704861 := bstep (se 3 (by rfl) ⟨132161, by rfl⟩ : syracuseStep 704861 = 264323) B264323
theorem B475595 : Blo 207808 475595 := bstep (se 1 (by rfl) ⟨356696, by rfl⟩ : syracuseStep 475595 = 713393) B713393
theorem B377303 : Blo 207808 377303 := bstep (se 1 (by rfl) ⟨282977, by rfl⟩ : syracuseStep 377303 = 565955) B565955
theorem B410113 : Blo 207808 410113 := bstep (se 2 (by rfl) ⟨153792, by rfl⟩ : syracuseStep 410113 = 307585) B307585
theorem B475649 : Blo 207808 475649 := bstep (se 2 (by rfl) ⟨178368, by rfl⟩ : syracuseStep 475649 = 356737) B356737
theorem B311819 : Blo 207808 311819 := bstep (se 1 (by rfl) ⟨233864, by rfl⟩ : syracuseStep 311819 = 467729) B467729
theorem B311831 : Blo 207808 311831 := bstep (se 1 (by rfl) ⟨233873, by rfl⟩ : syracuseStep 311831 = 467747) B467747
theorem B377419 : Blo 207808 377419 := bstep (se 1 (by rfl) ⟨283064, by rfl⟩ : syracuseStep 377419 = 566129) B566129
theorem B311897 : Blo 207808 311897 := bstep (se 2 (by rfl) ⟨116961, by rfl⟩ : syracuseStep 311897 = 233923) B233923
theorem B836185 : Blo 207808 836185 := bstep (se 2 (by rfl) ⟨313569, by rfl⟩ : syracuseStep 836185 = 627139) B627139
theorem B901763 : Blo 207808 901763 := bstep (se 1 (by rfl) ⟨676322, by rfl⟩ : syracuseStep 901763 = 1352645) B1352645
theorem B803479 : Blo 207808 803479 := bstep (se 1 (by rfl) ⟨602609, by rfl⟩ : syracuseStep 803479 = 1205219) B1205219
theorem B312011 : Blo 207808 312011 := bstep (se 1 (by rfl) ⟨234008, by rfl⟩ : syracuseStep 312011 = 468017) B468017
theorem B312023 : Blo 207808 312023 := bstep (se 1 (by rfl) ⟨234017, by rfl⟩ : syracuseStep 312023 = 468035) B468035
theorem B475865 : Blo 207808 475865 := bstep (se 2 (by rfl) ⟨178449, by rfl⟩ : syracuseStep 475865 = 356899) B356899
theorem B2999045 : Blo 207808 2999045 := bstep (se 4 (by rfl) ⟨281160, by rfl⟩ : syracuseStep 2999045 = 562321) B562321
theorem B312089 : Blo 207808 312089 := bstep (se 2 (by rfl) ⟨117033, by rfl⟩ : syracuseStep 312089 = 234067) B234067
theorem B475955 : Blo 207808 475955 := bstep (se 1 (by rfl) ⟨356966, by rfl⟩ : syracuseStep 475955 = 713933) B713933
theorem B475991 : Blo 207808 475991 := bstep (se 1 (by rfl) ⟨356993, by rfl⟩ : syracuseStep 475991 = 713987) B713987
theorem B312203 : Blo 207808 312203 := bstep (se 1 (by rfl) ⟨234152, by rfl⟩ : syracuseStep 312203 = 468305) B468305
theorem B312215 : Blo 207808 312215 := bstep (se 1 (by rfl) ⟨234161, by rfl⟩ : syracuseStep 312215 = 468323) B468323
theorem B377779 : Blo 207808 377779 := bstep (se 1 (by rfl) ⟨283334, by rfl⟩ : syracuseStep 377779 = 566669) B566669
theorem B312281 : Blo 207808 312281 := bstep (se 2 (by rfl) ⟨117105, by rfl⟩ : syracuseStep 312281 = 234211) B234211
theorem B476171 : Blo 207808 476171 := bstep (se 1 (by rfl) ⟨357128, by rfl⟩ : syracuseStep 476171 = 714257) B714257
theorem B476225 : Blo 207808 476225 := bstep (se 2 (by rfl) ⟨178584, by rfl⟩ : syracuseStep 476225 = 357169) B357169
theorem B312395 : Blo 207808 312395 := bstep (se 1 (by rfl) ⟨234296, by rfl⟩ : syracuseStep 312395 = 468593) B468593
theorem B312407 : Blo 207808 312407 := bstep (se 1 (by rfl) ⟨234305, by rfl⟩ : syracuseStep 312407 = 468611) B468611
theorem B312473 : Blo 207808 312473 := bstep (se 2 (by rfl) ⟨117177, by rfl⟩ : syracuseStep 312473 = 234355) B234355
theorem B312587 : Blo 207808 312587 := bstep (se 1 (by rfl) ⟨234440, by rfl⟩ : syracuseStep 312587 = 468881) B468881
theorem B312599 : Blo 207808 312599 := bstep (se 1 (by rfl) ⟨234449, by rfl⟩ : syracuseStep 312599 = 468899) B468899
theorem B476441 : Blo 207808 476441 := bstep (se 2 (by rfl) ⟨178665, by rfl⟩ : syracuseStep 476441 = 357331) B357331
theorem B312665 : Blo 207808 312665 := bstep (se 2 (by rfl) ⟨117249, by rfl⟩ : syracuseStep 312665 = 234499) B234499
theorem B476531 : Blo 207808 476531 := bstep (se 1 (by rfl) ⟨357398, by rfl⟩ : syracuseStep 476531 = 714797) B714797
theorem B476567 : Blo 207808 476567 := bstep (se 1 (by rfl) ⟨357425, by rfl⟩ : syracuseStep 476567 = 714851) B714851
theorem B312779 : Blo 207808 312779 := bstep (se 1 (by rfl) ⟨234584, by rfl⟩ : syracuseStep 312779 = 469169) B469169
theorem B705995 : Blo 207808 705995 := bstep (se 1 (by rfl) ⟨529496, by rfl⟩ : syracuseStep 705995 = 1058993) B1058993
theorem B312791 : Blo 207808 312791 := bstep (se 1 (by rfl) ⟨234593, by rfl⟩ : syracuseStep 312791 = 469187) B469187
theorem B443927 : Blo 207808 443927 := bstep (se 1 (by rfl) ⟨332945, by rfl⟩ : syracuseStep 443927 = 665891) B665891
theorem B312857 : Blo 207808 312857 := bstep (se 2 (by rfl) ⟨117321, by rfl⟩ : syracuseStep 312857 = 234643) B234643
theorem B312971 : Blo 207808 312971 := bstep (se 1 (by rfl) ⟨234728, by rfl⟩ : syracuseStep 312971 = 469457) B469457
theorem B312983 : Blo 207808 312983 := bstep (se 1 (by rfl) ⟨234737, by rfl⟩ : syracuseStep 312983 = 469475) B469475
theorem B542387 : Blo 207808 542387 := bstep (se 1 (by rfl) ⟨406790, by rfl⟩ : syracuseStep 542387 = 813581) B813581
theorem B313049 : Blo 207808 313049 := bstep (se 2 (by rfl) ⟨117393, by rfl⟩ : syracuseStep 313049 = 234787) B234787
theorem B706265 : Blo 207808 706265 := bstep (se 2 (by rfl) ⟨264849, by rfl⟩ : syracuseStep 706265 = 529699) B529699
theorem B1066769 : Blo 207808 1066769 := bstep (se 2 (by rfl) ⟨400038, by rfl⟩ : syracuseStep 1066769 = 800077) B800077
theorem B313163 : Blo 207808 313163 := bstep (se 1 (by rfl) ⟨234872, by rfl⟩ : syracuseStep 313163 = 469745) B469745
theorem B313175 : Blo 207808 313175 := bstep (se 1 (by rfl) ⟨234881, by rfl⟩ : syracuseStep 313175 = 469763) B469763
theorem B313241 : Blo 207808 313241 := bstep (se 2 (by rfl) ⟨117465, by rfl⟩ : syracuseStep 313241 = 234931) B234931
theorem B1066931 : Blo 207808 1066931 := bstep (se 1 (by rfl) ⟨800198, by rfl⟩ : syracuseStep 1066931 = 1600397) B1600397
theorem B575453 : Blo 207808 575453 := bstep (se 3 (by rfl) ⟨107897, by rfl⟩ : syracuseStep 575453 = 215795) B215795
theorem B313355 : Blo 207808 313355 := bstep (se 1 (by rfl) ⟨235016, by rfl⟩ : syracuseStep 313355 = 470033) B470033
theorem B313367 : Blo 207808 313367 := bstep (se 1 (by rfl) ⟨235025, by rfl⟩ : syracuseStep 313367 = 470051) B470051
theorem B313433 : Blo 207808 313433 := bstep (se 2 (by rfl) ⟨117537, by rfl⟩ : syracuseStep 313433 = 235075) B235075
theorem B313547 : Blo 207808 313547 := bstep (se 1 (by rfl) ⟨235160, by rfl⟩ : syracuseStep 313547 = 470321) B470321
theorem B313559 : Blo 207808 313559 := bstep (se 1 (by rfl) ⟨235169, by rfl⟩ : syracuseStep 313559 = 470339) B470339
theorem B1689817 : Blo 207808 1689817 := bstep (se 2 (by rfl) ⟨633681, by rfl⟩ : syracuseStep 1689817 = 1267363) B1267363
theorem B313625 : Blo 207808 313625 := bstep (se 2 (by rfl) ⟨117609, by rfl⟩ : syracuseStep 313625 = 235219) B235219
theorem B313739 : Blo 207808 313739 := bstep (se 1 (by rfl) ⟨235304, by rfl⟩ : syracuseStep 313739 = 470609) B470609
theorem B313751 : Blo 207808 313751 := bstep (se 1 (by rfl) ⟨235313, by rfl⟩ : syracuseStep 313751 = 470627) B470627
theorem B706967 : Blo 207808 706967 := bstep (se 1 (by rfl) ⟨530225, by rfl⟩ : syracuseStep 706967 = 1060451) B1060451
theorem B641459 : Blo 207808 641459 := bstep (se 1 (by rfl) ⟨481094, by rfl⟩ : syracuseStep 641459 = 962189) B962189
theorem B313817 : Blo 207808 313817 := bstep (se 2 (by rfl) ⟨117681, by rfl⟩ : syracuseStep 313817 = 235363) B235363
theorem B444953 : Blo 207808 444953 := bstep (se 2 (by rfl) ⟨166857, by rfl⟩ : syracuseStep 444953 = 333715) B333715
theorem B1198637 : Blo 207808 1198637 := bstep (se 3 (by rfl) ⟨224744, by rfl⟩ : syracuseStep 1198637 = 449489) B449489
theorem B313931 : Blo 207808 313931 := bstep (se 1 (by rfl) ⟨235448, by rfl⟩ : syracuseStep 313931 = 470897) B470897
theorem B313943 : Blo 207808 313943 := bstep (se 1 (by rfl) ⟨235457, by rfl⟩ : syracuseStep 313943 = 470915) B470915
theorem B281227 : Blo 207808 281227 := bstep (se 1 (by rfl) ⟨210920, by rfl⟩ : syracuseStep 281227 = 421841) B421841
theorem B314009 : Blo 207808 314009 := bstep (se 2 (by rfl) ⟨117753, by rfl⟩ : syracuseStep 314009 = 235507) B235507
theorem B314123 : Blo 207808 314123 := bstep (se 1 (by rfl) ⟨235592, by rfl⟩ : syracuseStep 314123 = 471185) B471185
theorem B314135 : Blo 207808 314135 := bstep (se 1 (by rfl) ⟨235601, by rfl⟩ : syracuseStep 314135 = 471203) B471203
theorem B641857 : Blo 207808 641857 := bstep (se 2 (by rfl) ⟨240696, by rfl⟩ : syracuseStep 641857 = 481393) B481393
theorem B314201 : Blo 207808 314201 := bstep (se 2 (by rfl) ⟨117825, by rfl⟩ : syracuseStep 314201 = 235651) B235651
theorem B707507 : Blo 207808 707507 := bstep (se 1 (by rfl) ⟨530630, by rfl⟩ : syracuseStep 707507 = 1061261) B1061261
theorem B314315 : Blo 207808 314315 := bstep (se 1 (by rfl) ⟨235736, by rfl⟩ : syracuseStep 314315 = 471473) B471473
theorem B314327 : Blo 207808 314327 := bstep (se 1 (by rfl) ⟨235745, by rfl⟩ : syracuseStep 314327 = 471491) B471491
theorem B314393 : Blo 207808 314393 := bstep (se 2 (by rfl) ⟨117897, by rfl⟩ : syracuseStep 314393 = 235795) B235795
theorem B281675 : Blo 207808 281675 := bstep (se 1 (by rfl) ⟨211256, by rfl⟩ : syracuseStep 281675 = 422513) B422513
theorem B314507 : Blo 207808 314507 := bstep (se 1 (by rfl) ⟨235880, by rfl⟩ : syracuseStep 314507 = 471761) B471761
theorem B314519 : Blo 207808 314519 := bstep (se 1 (by rfl) ⟨235889, by rfl⟩ : syracuseStep 314519 = 471779) B471779
theorem B707777 : Blo 207808 707777 := bstep (se 2 (by rfl) ⟨265416, by rfl⟩ : syracuseStep 707777 = 530833) B530833
theorem B314585 : Blo 207808 314585 := bstep (se 2 (by rfl) ⟨117969, by rfl⟩ : syracuseStep 314585 = 235939) B235939
theorem B1592621 : Blo 207808 1592621 := bstep (se 3 (by rfl) ⟨298616, by rfl⟩ : syracuseStep 1592621 = 597233) B597233
theorem B314699 : Blo 207808 314699 := bstep (se 1 (by rfl) ⟨236024, by rfl⟩ : syracuseStep 314699 = 472049) B472049
theorem B314711 : Blo 207808 314711 := bstep (se 1 (by rfl) ⟨236033, by rfl⟩ : syracuseStep 314711 = 472067) B472067
theorem B314777 : Blo 207808 314777 := bstep (se 2 (by rfl) ⟨118041, by rfl⟩ : syracuseStep 314777 = 236083) B236083
theorem B314891 : Blo 207808 314891 := bstep (se 1 (by rfl) ⟨236168, by rfl⟩ : syracuseStep 314891 = 472337) B472337
theorem B314903 : Blo 207808 314903 := bstep (se 1 (by rfl) ⟨236177, by rfl⟩ : syracuseStep 314903 = 472355) B472355
theorem B3001931 : Blo 207808 3001931 := bstep (se 1 (by rfl) ⟨2251448, by rfl⟩ : syracuseStep 3001931 = 4502897) B4502897
theorem B282199 : Blo 207808 282199 := bstep (se 1 (by rfl) ⟨211649, by rfl⟩ : syracuseStep 282199 = 423299) B423299
theorem B314969 : Blo 207808 314969 := bstep (se 2 (by rfl) ⟨118113, by rfl⟩ : syracuseStep 314969 = 236227) B236227
theorem B904877 : Blo 207808 904877 := bstep (se 3 (by rfl) ⟨169664, by rfl⟩ : syracuseStep 904877 = 339329) B339329
theorem B315083 : Blo 207808 315083 := bstep (se 1 (by rfl) ⟨236312, by rfl⟩ : syracuseStep 315083 = 472625) B472625
theorem B315095 : Blo 207808 315095 := bstep (se 1 (by rfl) ⟨236321, by rfl⟩ : syracuseStep 315095 = 472643) B472643
theorem B708317 : Blo 207808 708317 := bstep (se 3 (by rfl) ⟨132809, by rfl⟩ : syracuseStep 708317 = 265619) B265619
theorem B315161 : Blo 207808 315161 := bstep (se 2 (by rfl) ⟨118185, by rfl⟩ : syracuseStep 315161 = 236371) B236371
theorem B1068875 : Blo 207808 1068875 := bstep (se 1 (by rfl) ⟨801656, by rfl⟩ : syracuseStep 1068875 = 1603313) B1603313
theorem B347993 : Blo 207808 347993 := bstep (se 2 (by rfl) ⟨130497, by rfl⟩ : syracuseStep 347993 = 260995) B260995
theorem B315275 : Blo 207808 315275 := bstep (se 1 (by rfl) ⟨236456, by rfl⟩ : syracuseStep 315275 = 472913) B472913
theorem B315287 : Blo 207808 315287 := bstep (se 1 (by rfl) ⟨236465, by rfl⟩ : syracuseStep 315287 = 472931) B472931
theorem B380875 : Blo 207808 380875 := bstep (se 1 (by rfl) ⟨285656, by rfl⟩ : syracuseStep 380875 = 571313) B571313
theorem B315353 : Blo 207808 315353 := bstep (se 2 (by rfl) ⟨118257, by rfl⟩ : syracuseStep 315353 = 236515) B236515
theorem B315467 : Blo 207808 315467 := bstep (se 1 (by rfl) ⟨236600, by rfl⟩ : syracuseStep 315467 = 473201) B473201
theorem B315479 : Blo 207808 315479 := bstep (se 1 (by rfl) ⟨236609, by rfl⟩ : syracuseStep 315479 = 473219) B473219
theorem B446593 : Blo 207808 446593 := bstep (se 2 (by rfl) ⟨167472, by rfl⟩ : syracuseStep 446593 = 334945) B334945
theorem B315545 : Blo 207808 315545 := bstep (se 2 (by rfl) ⟨118329, by rfl⟩ : syracuseStep 315545 = 236659) B236659
theorem B381107 : Blo 207808 381107 := bstep (se 1 (by rfl) ⟨285830, by rfl⟩ : syracuseStep 381107 = 571661) B571661
theorem B250123 : Blo 207808 250123 := bstep (se 1 (by rfl) ⟨187592, by rfl⟩ : syracuseStep 250123 = 375185) B375185
theorem B315659 : Blo 207808 315659 := bstep (se 1 (by rfl) ⟨236744, by rfl⟩ : syracuseStep 315659 = 473489) B473489
theorem B315671 : Blo 207808 315671 := bstep (se 1 (by rfl) ⟨236753, by rfl⟩ : syracuseStep 315671 = 473507) B473507
theorem B315737 : Blo 207808 315737 := bstep (se 2 (by rfl) ⟨118401, by rfl⟩ : syracuseStep 315737 = 236803) B236803
theorem B610763 : Blo 207808 610763 := bstep (se 1 (by rfl) ⟨458072, by rfl⟩ : syracuseStep 610763 = 916145) B916145
theorem B315851 : Blo 207808 315851 := bstep (se 1 (by rfl) ⟨236888, by rfl⟩ : syracuseStep 315851 = 473777) B473777
theorem B315863 : Blo 207808 315863 := bstep (se 1 (by rfl) ⟨236897, by rfl⟩ : syracuseStep 315863 = 473795) B473795
theorem B315929 : Blo 207808 315929 := bstep (se 2 (by rfl) ⟨118473, by rfl⟩ : syracuseStep 315929 = 236947) B236947
theorem B316043 : Blo 207808 316043 := bstep (se 1 (by rfl) ⟨237032, by rfl⟩ : syracuseStep 316043 = 474065) B474065
theorem B316055 : Blo 207808 316055 := bstep (se 1 (by rfl) ⟨237041, by rfl⟩ : syracuseStep 316055 = 474083) B474083
theorem B1004183 : Blo 207808 1004183 := bstep (se 1 (by rfl) ⟨753137, by rfl⟩ : syracuseStep 1004183 = 1506275) B1506275
theorem B447191 : Blo 207808 447191 := bstep (se 1 (by rfl) ⟨335393, by rfl⟩ : syracuseStep 447191 = 670787) B670787
theorem B316121 : Blo 207808 316121 := bstep (se 2 (by rfl) ⟨118545, by rfl⟩ : syracuseStep 316121 = 237091) B237091
theorem B709451 : Blo 207808 709451 := bstep (se 1 (by rfl) ⟨532088, by rfl⟩ : syracuseStep 709451 = 1064177) B1064177
theorem B316235 : Blo 207808 316235 := bstep (se 1 (by rfl) ⟨237176, by rfl⟩ : syracuseStep 316235 = 474353) B474353
theorem B316247 : Blo 207808 316247 := bstep (se 1 (by rfl) ⟨237185, by rfl⟩ : syracuseStep 316247 = 474371) B474371
theorem B1201027 : Blo 207808 1201027 := bstep (se 1 (by rfl) ⟨900770, by rfl⟩ : syracuseStep 1201027 = 1801541) B1801541
theorem B316313 : Blo 207808 316313 := bstep (se 2 (by rfl) ⟨118617, by rfl⟩ : syracuseStep 316313 = 237235) B237235
theorem B2053043 : Blo 207808 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B316427 : Blo 207808 316427 := bstep (se 1 (by rfl) ⟨237320, by rfl⟩ : syracuseStep 316427 = 474641) B474641
theorem B316439 : Blo 207808 316439 := bstep (se 1 (by rfl) ⟨237329, by rfl⟩ : syracuseStep 316439 = 474659) B474659
theorem B709721 : Blo 207808 709721 := bstep (se 2 (by rfl) ⟨266145, by rfl⟩ : syracuseStep 709721 = 532291) B532291
theorem B316505 : Blo 207808 316505 := bstep (se 2 (by rfl) ⟨118689, by rfl⟩ : syracuseStep 316505 = 237379) B237379
theorem B316619 : Blo 207808 316619 := bstep (se 1 (by rfl) ⟨237464, by rfl⟩ : syracuseStep 316619 = 474929) B474929
theorem B316631 : Blo 207808 316631 := bstep (se 1 (by rfl) ⟨237473, by rfl⟩ : syracuseStep 316631 = 474947) B474947
theorem B1135889 : Blo 207808 1135889 := bstep (se 2 (by rfl) ⟨425958, by rfl⟩ : syracuseStep 1135889 = 851917) B851917
theorem B316697 : Blo 207808 316697 := bstep (se 2 (by rfl) ⟨118761, by rfl⟩ : syracuseStep 316697 = 237523) B237523
theorem B3429697 : Blo 207808 3429697 := bstep (se 2 (by rfl) ⟨1286136, by rfl⟩ : syracuseStep 3429697 = 2572273) B2572273
theorem B316811 : Blo 207808 316811 := bstep (se 1 (by rfl) ⟨237608, by rfl⟩ : syracuseStep 316811 = 475217) B475217
theorem B316823 : Blo 207808 316823 := bstep (se 1 (by rfl) ⟨237617, by rfl⟩ : syracuseStep 316823 = 475235) B475235
theorem B316889 : Blo 207808 316889 := bstep (se 2 (by rfl) ⟨118833, by rfl⟩ : syracuseStep 316889 = 237667) B237667
theorem B480755 : Blo 207808 480755 := bstep (se 1 (by rfl) ⟨360566, by rfl⟩ : syracuseStep 480755 = 721133) B721133
theorem B1070657 : Blo 207808 1070657 := bstep (se 2 (by rfl) ⟨401496, by rfl⟩ : syracuseStep 1070657 = 802993) B802993
theorem B317003 : Blo 207808 317003 := bstep (se 1 (by rfl) ⟨237752, by rfl⟩ : syracuseStep 317003 = 475505) B475505
theorem B317015 : Blo 207808 317015 := bstep (se 1 (by rfl) ⟨237761, by rfl⟩ : syracuseStep 317015 = 475523) B475523
theorem B317081 : Blo 207808 317081 := bstep (se 2 (by rfl) ⟨118905, by rfl⟩ : syracuseStep 317081 = 237811) B237811
theorem B448267 : Blo 207808 448267 := bstep (se 1 (by rfl) ⟨336200, by rfl⟩ : syracuseStep 448267 = 672401) B672401
theorem B317195 : Blo 207808 317195 := bstep (se 1 (by rfl) ⟨237896, by rfl⟩ : syracuseStep 317195 = 475793) B475793
theorem B710423 : Blo 207808 710423 := bstep (se 1 (by rfl) ⟨532817, by rfl⟩ : syracuseStep 710423 = 1065635) B1065635
theorem B317207 : Blo 207808 317207 := bstep (se 1 (by rfl) ⟨237905, by rfl⟩ : syracuseStep 317207 = 475811) B475811
theorem B382745 : Blo 207808 382745 := bstep (se 2 (by rfl) ⟨143529, by rfl⟩ : syracuseStep 382745 = 287059) B287059
theorem B1201985 : Blo 207808 1201985 := bstep (se 2 (by rfl) ⟨450744, by rfl⟩ : syracuseStep 1201985 = 901489) B901489
theorem B317273 : Blo 207808 317273 := bstep (se 2 (by rfl) ⟨118977, by rfl⟩ : syracuseStep 317273 = 237955) B237955
theorem B2283365 : Blo 207808 2283365 := bstep (se 4 (by rfl) ⟨214065, by rfl⟩ : syracuseStep 2283365 = 428131) B428131
theorem B677783 : Blo 207808 677783 := bstep (se 1 (by rfl) ⟨508337, by rfl⟩ : syracuseStep 677783 = 1016675) B1016675
theorem B677825 : Blo 207808 677825 := bstep (se 2 (by rfl) ⟨254184, by rfl⟩ : syracuseStep 677825 = 508369) B508369
theorem B317387 : Blo 207808 317387 := bstep (se 1 (by rfl) ⟨238040, by rfl⟩ : syracuseStep 317387 = 476081) B476081
theorem B317399 : Blo 207808 317399 := bstep (se 1 (by rfl) ⟨238049, by rfl⟩ : syracuseStep 317399 = 476099) B476099
theorem B251915 : Blo 207808 251915 := bstep (se 1 (by rfl) ⟨188936, by rfl⟩ : syracuseStep 251915 = 377873) B377873
theorem B317465 : Blo 207808 317465 := bstep (se 2 (by rfl) ⟨119049, by rfl⟩ : syracuseStep 317465 = 238099) B238099
theorem B677963 : Blo 207808 677963 := bstep (se 1 (by rfl) ⟨508472, by rfl⟩ : syracuseStep 677963 = 1016945) B1016945
theorem B2021507 : Blo 207808 2021507 := bstep (se 1 (by rfl) ⟨1516130, by rfl⟩ : syracuseStep 2021507 = 3032261) B3032261
theorem B317579 : Blo 207808 317579 := bstep (se 1 (by rfl) ⟨238184, by rfl⟩ : syracuseStep 317579 = 476369) B476369
theorem B317591 : Blo 207808 317591 := bstep (se 1 (by rfl) ⟨238193, by rfl⟩ : syracuseStep 317591 = 476387) B476387
theorem B678091 : Blo 207808 678091 := bstep (se 1 (by rfl) ⟨508568, by rfl⟩ : syracuseStep 678091 = 1017137) B1017137
theorem B317657 : Blo 207808 317657 := bstep (se 2 (by rfl) ⟨119121, by rfl⟩ : syracuseStep 317657 = 238243) B238243
theorem B1628461 : Blo 207808 1628461 := bstep (se 3 (by rfl) ⟨305336, by rfl⟩ : syracuseStep 1628461 = 610673) B610673
theorem B710963 : Blo 207808 710963 := bstep (se 1 (by rfl) ⟨533222, by rfl⟩ : syracuseStep 710963 = 1066445) B1066445
theorem B252247 : Blo 207808 252247 := bstep (se 1 (by rfl) ⟨189185, by rfl⟩ : syracuseStep 252247 = 378371) B378371
theorem B678233 : Blo 207808 678233 := bstep (se 2 (by rfl) ⟨254337, by rfl⟩ : syracuseStep 678233 = 508675) B508675
theorem B678347 : Blo 207808 678347 := bstep (se 1 (by rfl) ⟨508760, by rfl⟩ : syracuseStep 678347 = 1017521) B1017521
theorem B481751 : Blo 207808 481751 := bstep (se 1 (by rfl) ⟨361313, by rfl⟩ : syracuseStep 481751 = 722627) B722627
theorem B448985 : Blo 207808 448985 := bstep (se 2 (by rfl) ⟨168369, by rfl⟩ : syracuseStep 448985 = 336739) B336739
theorem B350743 : Blo 207808 350743 := bstep (se 1 (by rfl) ⟨263057, by rfl⟩ : syracuseStep 350743 = 526115) B526115
theorem B2382371 : Blo 207808 2382371 := bstep (se 1 (by rfl) ⟨1786778, by rfl⟩ : syracuseStep 2382371 = 3573557) B3573557
theorem B711233 : Blo 207808 711233 := bstep (se 2 (by rfl) ⟨266712, by rfl⟩ : syracuseStep 711233 = 533425) B533425
theorem B3824279 : Blo 207808 3824279 := bstep (se 1 (by rfl) ⟨2868209, by rfl⟩ : syracuseStep 3824279 = 5736419) B5736419
theorem B285529 : Blo 207808 285529 := bstep (se 2 (by rfl) ⟨107073, by rfl⟩ : syracuseStep 285529 = 214147) B214147
theorem B1727411 : Blo 207808 1727411 := bstep (se 1 (by rfl) ⟨1295558, by rfl⟩ : syracuseStep 1727411 = 2591117) B2591117
theorem B449497 : Blo 207808 449497 := bstep (se 2 (by rfl) ⟨168561, by rfl⟩ : syracuseStep 449497 = 337123) B337123
theorem B318539 : Blo 207808 318539 := bstep (se 1 (by rfl) ⟨238904, by rfl⟩ : syracuseStep 318539 = 477809) B477809
theorem B1596509 : Blo 207808 1596509 := bstep (se 3 (by rfl) ⟨299345, by rfl⟩ : syracuseStep 1596509 = 598691) B598691
theorem B711773 : Blo 207808 711773 := bstep (se 3 (by rfl) ⟨133457, by rfl⟩ : syracuseStep 711773 = 266915) B266915
theorem B449651 : Blo 207808 449651 := bstep (se 1 (by rfl) ⟨337238, by rfl⟩ : syracuseStep 449651 = 674477) B674477
theorem B351371 : Blo 207808 351371 := bstep (se 1 (by rfl) ⟨263528, by rfl⟩ : syracuseStep 351371 = 527057) B527057
theorem B482561 : Blo 207808 482561 := bstep (se 2 (by rfl) ⟨180960, by rfl⟩ : syracuseStep 482561 = 361921) B361921
theorem B351499 : Blo 207808 351499 := bstep (se 1 (by rfl) ⟨263624, by rfl⟩ : syracuseStep 351499 = 527249) B527249
theorem B351641 : Blo 207808 351641 := bstep (se 2 (by rfl) ⟨131865, by rfl⟩ : syracuseStep 351641 = 263731) B263731
theorem B712115 : Blo 207808 712115 := bstep (se 1 (by rfl) ⟨534086, by rfl⟩ : syracuseStep 712115 = 1068173) B1068173
theorem B351769 : Blo 207808 351769 := bstep (se 2 (by rfl) ⟨131913, by rfl⟩ : syracuseStep 351769 = 263827) B263827
theorem B450625 : Blo 207808 450625 := bstep (se 2 (by rfl) ⟨168984, by rfl⟩ : syracuseStep 450625 = 337969) B337969
theorem B352343 : Blo 207808 352343 := bstep (se 1 (by rfl) ⟨264257, by rfl⟩ : syracuseStep 352343 = 528515) B528515
theorem B712907 : Blo 207808 712907 := bstep (se 1 (by rfl) ⟨534680, by rfl⟩ : syracuseStep 712907 = 1069361) B1069361
theorem B352471 : Blo 207808 352471 := bstep (se 1 (by rfl) ⟨264353, by rfl⟩ : syracuseStep 352471 = 528707) B528707
theorem B319883 : Blo 207808 319883 := bstep (se 1 (by rfl) ⟨239912, by rfl⟩ : syracuseStep 319883 = 479825) B479825
theorem B450967 : Blo 207808 450967 := bstep (se 1 (by rfl) ⟨338225, by rfl⟩ : syracuseStep 450967 = 676451) B676451
theorem B713177 : Blo 207808 713177 := bstep (se 2 (by rfl) ⟨267441, by rfl⟩ : syracuseStep 713177 = 534883) B534883
theorem B1434433 : Blo 207808 1434433 := bstep (se 2 (by rfl) ⟨537912, by rfl⟩ : syracuseStep 1434433 = 1075825) B1075825
theorem B353099 : Blo 207808 353099 := bstep (se 1 (by rfl) ⟨264824, by rfl⟩ : syracuseStep 353099 = 529649) B529649
theorem B451403 : Blo 207808 451403 := bstep (se 1 (by rfl) ⟨338552, by rfl⟩ : syracuseStep 451403 = 677105) B677105
theorem B353227 : Blo 207808 353227 := bstep (se 1 (by rfl) ⟨264920, by rfl⟩ : syracuseStep 353227 = 529841) B529841
theorem B353369 : Blo 207808 353369 := bstep (se 2 (by rfl) ⟨132513, by rfl⟩ : syracuseStep 353369 = 265027) B265027
theorem B713879 : Blo 207808 713879 := bstep (se 1 (by rfl) ⟨535409, by rfl⟩ : syracuseStep 713879 = 1070819) B1070819
theorem B1336499 : Blo 207808 1336499 := bstep (se 1 (by rfl) ⟨1002374, by rfl⟩ : syracuseStep 1336499 = 2004749) B2004749
theorem B353497 : Blo 207808 353497 := bstep (se 2 (by rfl) ⟨132561, by rfl⟩ : syracuseStep 353497 = 265123) B265123
theorem B222647 : Blo 207808 222647 := bstep (se 1 (by rfl) ⟨166985, by rfl⟩ : syracuseStep 222647 = 333971) B333971
theorem B1500677 : Blo 207808 1500677 := bstep (se 4 (by rfl) ⟨140688, by rfl⟩ : syracuseStep 1500677 = 281377) B281377
theorem B1697345 : Blo 207808 1697345 := bstep (se 2 (by rfl) ⟨636504, by rfl⟩ : syracuseStep 1697345 = 1273009) B1273009
theorem B386675 : Blo 207808 386675 := bstep (se 1 (by rfl) ⟨290006, by rfl⟩ : syracuseStep 386675 = 580013) B580013
theorem B714419 : Blo 207808 714419 := bstep (se 1 (by rfl) ⟨535814, by rfl⟩ : syracuseStep 714419 = 1071629) B1071629
theorem B452299 : Blo 207808 452299 := bstep (se 1 (by rfl) ⟨339224, by rfl⟩ : syracuseStep 452299 = 678449) B678449
theorem B1009369 : Blo 207808 1009369 := bstep (se 2 (by rfl) ⟨378513, by rfl⟩ : syracuseStep 1009369 = 757027) B757027
theorem B354071 : Blo 207808 354071 := bstep (se 1 (by rfl) ⟨265553, by rfl⟩ : syracuseStep 354071 = 531107) B531107
theorem B255767 : Blo 207808 255767 := bstep (se 1 (by rfl) ⟨191825, by rfl⟩ : syracuseStep 255767 = 383651) B383651
theorem B354199 : Blo 207808 354199 := bstep (se 1 (by rfl) ⟨265649, by rfl⟩ : syracuseStep 354199 = 531299) B531299
theorem B21718961 : Blo 207808 21718961 := bstep (se 2 (by rfl) ⟨8144610, by rfl⟩ : syracuseStep 21718961 = 16289221) B16289221
theorem B714689 : Blo 207808 714689 := bstep (se 2 (by rfl) ⟨268008, by rfl⟩ : syracuseStep 714689 = 536017) B536017
theorem B387251 : Blo 207808 387251 := bstep (se 1 (by rfl) ⟨290438, by rfl⟩ : syracuseStep 387251 = 580877) B580877
theorem B1796417 : Blo 207808 1796417 := bstep (se 2 (by rfl) ⟨673656, by rfl⟩ : syracuseStep 1796417 = 1347313) B1347313
theorem B354827 : Blo 207808 354827 := bstep (se 1 (by rfl) ⟨266120, by rfl⟩ : syracuseStep 354827 = 532241) B532241
theorem B354955 : Blo 207808 354955 := bstep (se 1 (by rfl) ⟨266216, by rfl⟩ : syracuseStep 354955 = 532433) B532433
theorem B912131 : Blo 207808 912131 := bstep (se 1 (by rfl) ⟨684098, by rfl⟩ : syracuseStep 912131 = 1368197) B1368197
theorem B355097 : Blo 207808 355097 := bstep (se 2 (by rfl) ⟨133161, by rfl⟩ : syracuseStep 355097 = 266323) B266323
theorem B355225 : Blo 207808 355225 := bstep (se 2 (by rfl) ⟨133209, by rfl⟩ : syracuseStep 355225 = 266419) B266419
theorem B453683 : Blo 207808 453683 := bstep (se 1 (by rfl) ⟨340262, by rfl⟩ : syracuseStep 453683 = 680525) B680525
theorem B224407 : Blo 207808 224407 := bstep (se 1 (by rfl) ⟨168305, by rfl⟩ : syracuseStep 224407 = 336611) B336611
theorem B453899 : Blo 207808 453899 := bstep (se 1 (by rfl) ⟨340424, by rfl⟩ : syracuseStep 453899 = 680849) B680849
theorem B355799 : Blo 207808 355799 := bstep (se 1 (by rfl) ⟨266849, by rfl⟩ : syracuseStep 355799 = 533699) B533699
theorem B355927 : Blo 207808 355927 := bstep (se 1 (by rfl) ⟨266945, by rfl⟩ : syracuseStep 355927 = 533891) B533891
theorem B1273495 : Blo 207808 1273495 := bstep (se 1 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 1273495 = 1910243) B1910243
theorem B2682629 : Blo 207808 2682629 := bstep (se 4 (by rfl) ⟨251496, by rfl⟩ : syracuseStep 2682629 = 502993) B502993
theorem B225227 : Blo 207808 225227 := bstep (se 1 (by rfl) ⟨168920, by rfl⟩ : syracuseStep 225227 = 337841) B337841
theorem B389207 : Blo 207808 389207 := bstep (se 1 (by rfl) ⟨291905, by rfl⟩ : syracuseStep 389207 = 583811) B583811
theorem B1339523 : Blo 207808 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B6942871 : Blo 207808 6942871 := bstep (se 1 (by rfl) ⟨5207153, by rfl⟩ : syracuseStep 6942871 = 10414307) B10414307
theorem B356555 : Blo 207808 356555 := bstep (se 1 (by rfl) ⟨267416, by rfl⟩ : syracuseStep 356555 = 534833) B534833
theorem B3371329 : Blo 207808 3371329 := bstep (se 2 (by rfl) ⟨1264248, by rfl⟩ : syracuseStep 3371329 = 2528497) B2528497
theorem B913739 : Blo 207808 913739 := bstep (se 1 (by rfl) ⟨685304, by rfl⟩ : syracuseStep 913739 = 1370609) B1370609
theorem B356683 : Blo 207808 356683 := bstep (se 1 (by rfl) ⟨267512, by rfl⟩ : syracuseStep 356683 = 535025) B535025
theorem B356825 : Blo 207808 356825 := bstep (se 2 (by rfl) ⟨133809, by rfl⟩ : syracuseStep 356825 = 267619) B267619
theorem B422423 : Blo 207808 422423 := bstep (se 1 (by rfl) ⟨316817, by rfl⟩ : syracuseStep 422423 = 633635) B633635
theorem B356953 : Blo 207808 356953 := bstep (se 2 (by rfl) ⟨133857, by rfl⟩ : syracuseStep 356953 = 267715) B267715
theorem B1798807 : Blo 207808 1798807 := bstep (se 1 (by rfl) ⟨1349105, by rfl⟩ : syracuseStep 1798807 = 2698211) B2698211
theorem B685003 : Blo 207808 685003 := bstep (se 1 (by rfl) ⟨513752, by rfl⟩ : syracuseStep 685003 = 1027505) B1027505
theorem B914435 : Blo 207808 914435 := bstep (se 1 (by rfl) ⟨685826, by rfl⟩ : syracuseStep 914435 = 1371653) B1371653
theorem B914449 : Blo 207808 914449 := bstep (se 2 (by rfl) ⟨342918, by rfl⟩ : syracuseStep 914449 = 685837) B685837
theorem B226795 : Blo 207808 226795 := bstep (se 1 (by rfl) ⟨170096, by rfl⟩ : syracuseStep 226795 = 340193) B340193
theorem B3601955 : Blo 207808 3601955 := bstep (se 1 (by rfl) ⟨2701466, by rfl⟩ : syracuseStep 3601955 = 5402933) B5402933
theorem B1144451 : Blo 207808 1144451 := bstep (se 1 (by rfl) ⟨858338, by rfl⟩ : syracuseStep 1144451 = 1716677) B1716677
theorem B423883 : Blo 207808 423883 := bstep (se 1 (by rfl) ⟨317912, by rfl⟩ : syracuseStep 423883 = 635825) B635825
theorem B1800323 : Blo 207808 1800323 := bstep (se 1 (by rfl) ⟨1350242, by rfl⟩ : syracuseStep 1800323 = 2700485) B2700485
theorem B948611 : Blo 207808 948611 := bstep (se 1 (by rfl) ⟨711458, by rfl⟩ : syracuseStep 948611 = 1422917) B1422917
theorem B359129 : Blo 207808 359129 := bstep (se 2 (by rfl) ⟨134673, by rfl⟩ : syracuseStep 359129 = 269347) B269347
theorem B949067 : Blo 207808 949067 := bstep (se 1 (by rfl) ⟨711800, by rfl⟩ : syracuseStep 949067 = 1423601) B1423601
theorem B424855 : Blo 207808 424855 := bstep (se 1 (by rfl) ⟨318641, by rfl⟩ : syracuseStep 424855 = 637283) B637283
theorem B720065 : Blo 207808 720065 := bstep (se 2 (by rfl) ⟨270024, by rfl⟩ : syracuseStep 720065 = 540049) B540049
theorem B7241309 : Blo 207808 7241309 := bstep (se 3 (by rfl) ⟨1357745, by rfl⟩ : syracuseStep 7241309 = 2715491) B2715491
theorem B2687093 : Blo 207808 2687093 := bstep (se 5 (by rfl) ⟨125957, by rfl⟩ : syracuseStep 2687093 = 251915) B251915
theorem B6750449 : Blo 207808 6750449 := bstep (se 2 (by rfl) ⟨2531418, by rfl⟩ : syracuseStep 6750449 = 5062837) B5062837
theorem B2031965 : Blo 207808 2031965 := bstep (se 3 (by rfl) ⟨380993, by rfl⟩ : syracuseStep 2031965 = 761987) B761987
theorem B1999363 : Blo 207808 1999363 := bstep (se 1 (by rfl) ⟨1499522, by rfl⟩ : syracuseStep 1999363 = 2999045) B2999045
theorem B1245719 : Blo 207808 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B1114913 : Blo 207808 1114913 := bstep (se 2 (by rfl) ⟨418092, by rfl⟩ : syracuseStep 1114913 = 836185) B836185
theorem B263083 : Blo 207808 263083 := bstep (se 1 (by rfl) ⟨197312, by rfl⟩ : syracuseStep 263083 = 394625) B394625
theorem B853021 : Blo 207808 853021 := bstep (se 3 (by rfl) ⟨159941, by rfl⟩ : syracuseStep 853021 = 319883) B319883
theorem B2885149 : Blo 207808 2885149 := bstep (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) B1081931
theorem B427639 : Blo 207808 427639 := bstep (se 1 (by rfl) ⟨320729, by rfl⟩ : syracuseStep 427639 = 641459) B641459
theorem B296635 : Blo 207808 296635 := bstep (se 1 (by rfl) ⟨222476, by rfl⟩ : syracuseStep 296635 = 444953) B444953
theorem B264055 : Blo 207808 264055 := bstep (se 1 (by rfl) ⟨198041, by rfl⟩ : syracuseStep 264055 = 396083) B396083
theorem B395209 : Blo 207808 395209 := bstep (se 2 (by rfl) ⟨148203, by rfl⟩ : syracuseStep 395209 = 296407) B296407
theorem B264379 : Blo 207808 264379 := bstep (se 1 (by rfl) ⟨198284, by rfl⟩ : syracuseStep 264379 = 396569) B396569
theorem B1345825 : Blo 207808 1345825 := bstep (se 2 (by rfl) ⟨504684, by rfl⟩ : syracuseStep 1345825 = 1009369) B1009369
theorem B2001287 : Blo 207808 2001287 := bstep (se 1 (by rfl) ⟨1500965, by rfl⟩ : syracuseStep 2001287 = 3001931) B3001931
theorem B592427 : Blo 207808 592427 := bstep (se 1 (by rfl) ⟨444320, by rfl⟩ : syracuseStep 592427 = 888641) B888641
theorem B231995 : Blo 207808 231995 := bstep (se 1 (by rfl) ⟨173996, by rfl⟩ : syracuseStep 231995 = 347993) B347993
theorem B395923 : Blo 207808 395923 := bstep (se 1 (by rfl) ⟨296942, by rfl⟩ : syracuseStep 395923 = 593885) B593885
theorem B527219 : Blo 207808 527219 := bstep (se 1 (by rfl) ⟨395414, by rfl⟩ : syracuseStep 527219 = 790829) B790829
theorem B265351 : Blo 207808 265351 := bstep (se 1 (by rfl) ⟨199013, by rfl⟩ : syracuseStep 265351 = 398027) B398027
theorem B298127 : Blo 207808 298127 := bstep (se 1 (by rfl) ⟨223595, by rfl⟩ : syracuseStep 298127 = 447191) B447191
theorem B2035003 : Blo 207808 2035003 := bstep (se 1 (by rfl) ⟨1526252, by rfl⟩ : syracuseStep 2035003 = 3052505) B3052505
theorem B527735 : Blo 207808 527735 := bstep (se 1 (by rfl) ⟨395801, by rfl⟩ : syracuseStep 527735 = 791603) B791603
theorem B757259 : Blo 207808 757259 := bstep (se 1 (by rfl) ⟨567944, by rfl⟩ : syracuseStep 757259 = 1135889) B1135889
theorem B1052189 : Blo 207808 1052189 := bstep (se 3 (by rfl) ⟨197285, by rfl⟩ : syracuseStep 1052189 = 394571) B394571
theorem B265771 : Blo 207808 265771 := bstep (se 1 (by rfl) ⟨199328, by rfl⟩ : syracuseStep 265771 = 398657) B398657
theorem B593543 : Blo 207808 593543 := bstep (se 1 (by rfl) ⟨445157, by rfl⟩ : syracuseStep 593543 = 890315) B890315
theorem B397001 : Blo 207808 397001 := bstep (se 2 (by rfl) ⟨148875, by rfl⟩ : syracuseStep 397001 = 297751) B297751
theorem B855809 : Blo 207808 855809 := bstep (se 2 (by rfl) ⟨320928, by rfl⟩ : syracuseStep 855809 = 641857) B641857
theorem B1969921 : Blo 207808 1969921 := bstep (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) B1477441
theorem B265999 : Blo 207808 265999 := bstep (se 1 (by rfl) ⟨199499, by rfl⟩ : syracuseStep 265999 = 398999) B398999
theorem B593725 : Blo 207808 593725 := bstep (se 3 (by rfl) ⟨111323, by rfl⟩ : syracuseStep 593725 = 222647) B222647
theorem B1052675 : Blo 207808 1052675 := bstep (se 1 (by rfl) ⟨789506, by rfl⟩ : syracuseStep 1052675 = 1579013) B1579013
theorem B1183805 : Blo 207808 1183805 := bstep (se 3 (by rfl) ⟨221963, by rfl⟩ : syracuseStep 1183805 = 443927) B443927
theorem B1347671 : Blo 207808 1347671 := bstep (se 1 (by rfl) ⟨1010753, by rfl⟩ : syracuseStep 1347671 = 2021507) B2021507
theorem B9605213 : Blo 207808 9605213 := bstep (se 3 (by rfl) ⟨1800977, by rfl⟩ : syracuseStep 9605213 = 3601955) B3601955
theorem B594067 : Blo 207808 594067 := bstep (se 1 (by rfl) ⟨445550, by rfl⟩ : syracuseStep 594067 = 891101) B891101
theorem B299209 : Blo 207808 299209 := bstep (se 2 (by rfl) ⟨112203, by rfl⟩ : syracuseStep 299209 = 224407) B224407
theorem B790843 : Blo 207808 790843 := bstep (se 1 (by rfl) ⟨593132, by rfl⟩ : syracuseStep 790843 = 1186265) B1186265
theorem B299323 : Blo 207808 299323 := bstep (se 1 (by rfl) ⟨224492, by rfl⟩ : syracuseStep 299323 = 448985) B448985
theorem B528727 : Blo 207808 528727 := bstep (se 1 (by rfl) ⟨396545, by rfl⟩ : syracuseStep 528727 = 793091) B793091
theorem B1446365 : Blo 207808 1446365 := bstep (se 3 (by rfl) ⟨271193, by rfl⟩ : syracuseStep 1446365 = 542387) B542387
theorem B266743 : Blo 207808 266743 := bstep (se 1 (by rfl) ⟨200057, by rfl⟩ : syracuseStep 266743 = 400115) B400115
theorem B397867 : Blo 207808 397867 := bstep (se 1 (by rfl) ⟨298400, by rfl⟩ : syracuseStep 397867 = 596801) B596801
theorem B397943 : Blo 207808 397943 := bstep (se 1 (by rfl) ⟨298457, by rfl⟩ : syracuseStep 397943 = 596915) B596915
theorem B529031 : Blo 207808 529031 := bstep (se 1 (by rfl) ⟨396773, by rfl⟩ : syracuseStep 529031 = 793547) B793547
theorem B234247 : Blo 207808 234247 := bstep (se 1 (by rfl) ⟨175685, by rfl⟩ : syracuseStep 234247 = 351371) B351371
theorem B529163 : Blo 207808 529163 := bstep (se 1 (by rfl) ⟨396872, by rfl⟩ : syracuseStep 529163 = 793745) B793745
theorem B791329 : Blo 207808 791329 := bstep (se 2 (by rfl) ⟨296748, by rfl⟩ : syracuseStep 791329 = 593497) B593497
theorem B2265893 : Blo 207808 2265893 := bstep (se 4 (by rfl) ⟨212427, by rfl⟩ : syracuseStep 2265893 = 424855) B424855
theorem B267067 : Blo 207808 267067 := bstep (se 1 (by rfl) ⟨200300, by rfl⟩ : syracuseStep 267067 = 400601) B400601
theorem B234427 : Blo 207808 234427 := bstep (se 1 (by rfl) ⟨175820, by rfl⟩ : syracuseStep 234427 = 351641) B351641
theorem B857099 : Blo 207808 857099 := bstep (se 1 (by rfl) ⟨642824, by rfl⟩ : syracuseStep 857099 = 1285649) B1285649
theorem B594955 : Blo 207808 594955 := bstep (se 1 (by rfl) ⟨446216, by rfl⟩ : syracuseStep 594955 = 892433) B892433
theorem B529679 : Blo 207808 529679 := bstep (se 1 (by rfl) ⟨397259, by rfl⟩ : syracuseStep 529679 = 794519) B794519
theorem B267563 : Blo 207808 267563 := bstep (se 1 (by rfl) ⟨200672, by rfl⟩ : syracuseStep 267563 = 401345) B401345
theorem B234895 : Blo 207808 234895 := bstep (se 1 (by rfl) ⟨176171, by rfl⟩ : syracuseStep 234895 = 352343) B352343
theorem B529811 : Blo 207808 529811 := bstep (se 1 (by rfl) ⟨397358, by rfl⟩ : syracuseStep 529811 = 794717) B794717
theorem B595457 : Blo 207808 595457 := bstep (se 2 (by rfl) ⟨223296, by rfl⟩ : syracuseStep 595457 = 446593) B446593
theorem B1054295 : Blo 207808 1054295 := bstep (se 1 (by rfl) ⟨790721, by rfl⟩ : syracuseStep 1054295 = 1581443) B1581443
theorem B333497 : Blo 207808 333497 := bstep (se 2 (by rfl) ⟨125061, by rfl⟩ : syracuseStep 333497 = 250123) B250123
theorem B792301 : Blo 207808 792301 := bstep (se 3 (by rfl) ⟨148556, by rfl⟩ : syracuseStep 792301 = 297113) B297113
theorem B4495105 : Blo 207808 4495105 := bstep (se 2 (by rfl) ⟨1685664, by rfl⟩ : syracuseStep 4495105 = 3371329) B3371329
theorem B268039 : Blo 207808 268039 := bstep (se 1 (by rfl) ⟨201029, by rfl⟩ : syracuseStep 268039 = 402059) B402059
theorem B595799 : Blo 207808 595799 := bstep (se 1 (by rfl) ⟨446849, by rfl⟩ : syracuseStep 595799 = 893699) B893699
theorem B235399 : Blo 207808 235399 := bstep (se 1 (by rfl) ⟨176549, by rfl⟩ : syracuseStep 235399 = 353099) B353099
theorem B300935 : Blo 207808 300935 := bstep (se 1 (by rfl) ⟨225701, by rfl⟩ : syracuseStep 300935 = 451403) B451403
theorem B890777 : Blo 207808 890777 := bstep (se 2 (by rfl) ⟨334041, by rfl⟩ : syracuseStep 890777 = 668083) B668083
theorem B792605 : Blo 207808 792605 := bstep (se 3 (by rfl) ⟨148613, by rfl⟩ : syracuseStep 792605 = 297227) B297227
theorem B235579 : Blo 207808 235579 := bstep (se 1 (by rfl) ⟨176684, by rfl⟩ : syracuseStep 235579 = 353369) B353369
theorem B1251389 : Blo 207808 1251389 := bstep (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) B469271
theorem B1054781 : Blo 207808 1054781 := bstep (se 3 (by rfl) ⟨197771, by rfl⟩ : syracuseStep 1054781 = 395543) B395543
theorem B890999 : Blo 207808 890999 := bstep (se 1 (by rfl) ⟨668249, by rfl⟩ : syracuseStep 890999 = 1336499) B1336499
theorem B2398409 : Blo 207808 2398409 := bstep (se 2 (by rfl) ⟨899403, by rfl⟩ : syracuseStep 2398409 = 1798807) B1798807
theorem B2529629 : Blo 207808 2529629 := bstep (se 3 (by rfl) ⟨474305, by rfl⟩ : syracuseStep 2529629 = 948611) B948611
theorem B530945 : Blo 207808 530945 := bstep (se 2 (by rfl) ⟨199104, by rfl⟩ : syracuseStep 530945 = 398209) B398209
theorem B236047 : Blo 207808 236047 := bstep (se 1 (by rfl) ⟨177035, by rfl⟩ : syracuseStep 236047 = 354071) B354071
theorem B399887 : Blo 207808 399887 := bstep (se 1 (by rfl) ⟨299915, by rfl⟩ : syracuseStep 399887 = 599831) B599831
theorem B334471 : Blo 207808 334471 := bstep (se 1 (by rfl) ⟨250853, by rfl⟩ : syracuseStep 334471 = 501707) B501707
theorem B1219265 : Blo 207808 1219265 := bstep (se 2 (by rfl) ⟨457224, by rfl⟩ : syracuseStep 1219265 = 914449) B914449
theorem B531319 : Blo 207808 531319 := bstep (se 1 (by rfl) ⟨398489, by rfl⟩ : syracuseStep 531319 = 796979) B796979
theorem B236551 : Blo 207808 236551 := bstep (se 1 (by rfl) ⟨177413, by rfl⟩ : syracuseStep 236551 = 354827) B354827
theorem B236731 : Blo 207808 236731 := bstep (se 1 (by rfl) ⟨177548, by rfl⟩ : syracuseStep 236731 = 355097) B355097
theorem B531755 : Blo 207808 531755 := bstep (se 1 (by rfl) ⟨398816, by rfl⟩ : syracuseStep 531755 = 797633) B797633
theorem B302393 : Blo 207808 302393 := bstep (se 2 (by rfl) ⟨113397, by rfl⟩ : syracuseStep 302393 = 226795) B226795
theorem B302599 : Blo 207808 302599 := bstep (se 1 (by rfl) ⟨226949, by rfl⟩ : syracuseStep 302599 = 453899) B453899
theorem B4726349 : Blo 207808 4726349 := bstep (se 3 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 4726349 = 1772381) B1772381
theorem B794231 : Blo 207808 794231 := bstep (se 1 (by rfl) ⟨595673, by rfl⟩ : syracuseStep 794231 = 1191347) B1191347
theorem B237199 : Blo 207808 237199 := bstep (se 1 (by rfl) ⟨177899, by rfl⟩ : syracuseStep 237199 = 355799) B355799
theorem B597689 : Blo 207808 597689 := bstep (se 2 (by rfl) ⟨224133, by rfl⟩ : syracuseStep 597689 = 448267) B448267
theorem B1056563 : Blo 207808 1056563 := bstep (se 1 (by rfl) ⟨792422, by rfl⟩ : syracuseStep 1056563 = 1584845) B1584845
theorem B565177 : Blo 207808 565177 := bstep (se 2 (by rfl) ⟨211941, by rfl⟩ : syracuseStep 565177 = 423883) B423883
theorem B893015 : Blo 207808 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B532595 : Blo 207808 532595 := bstep (se 1 (by rfl) ⟨399446, by rfl⟩ : syracuseStep 532595 = 798893) B798893
theorem B1056887 : Blo 207808 1056887 := bstep (se 1 (by rfl) ⟨792665, by rfl⟩ : syracuseStep 1056887 = 1585331) B1585331
theorem B401527 : Blo 207808 401527 := bstep (se 1 (by rfl) ⟨301145, by rfl⟩ : syracuseStep 401527 = 602291) B602291
theorem B532615 : Blo 207808 532615 := bstep (se 1 (by rfl) ⟨399461, by rfl⟩ : syracuseStep 532615 = 798923) B798923
theorem B237703 : Blo 207808 237703 := bstep (se 1 (by rfl) ⟨178277, by rfl⟩ : syracuseStep 237703 = 356555) B356555
theorem B2728181 : Blo 207808 2728181 := bstep (se 5 (by rfl) ⟨127883, by rfl⟩ : syracuseStep 2728181 = 255767) B255767
theorem B237883 : Blo 207808 237883 := bstep (se 1 (by rfl) ⟨178412, by rfl⟩ : syracuseStep 237883 = 356825) B356825
theorem B2171281 : Blo 207808 2171281 := bstep (se 2 (by rfl) ⟨814230, by rfl⟩ : syracuseStep 2171281 = 1628461) B1628461
theorem B532889 : Blo 207808 532889 := bstep (se 2 (by rfl) ⟨199833, by rfl⟩ : syracuseStep 532889 = 399667) B399667
theorem B336329 : Blo 207808 336329 := bstep (se 2 (by rfl) ⟨126123, by rfl⟩ : syracuseStep 336329 = 252247) B252247
theorem B533051 : Blo 207808 533051 := bstep (se 1 (by rfl) ⟨399788, by rfl⟩ : syracuseStep 533051 = 799577) B799577
theorem B795203 : Blo 207808 795203 := bstep (se 1 (by rfl) ⟨596402, by rfl⟩ : syracuseStep 795203 = 1192805) B1192805
theorem B467603 : Blo 207808 467603 := bstep (se 1 (by rfl) ⟨350702, by rfl⟩ : syracuseStep 467603 = 701405) B701405
theorem B467657 : Blo 207808 467657 := bstep (se 2 (by rfl) ⟨175371, by rfl⟩ : syracuseStep 467657 = 350743) B350743
theorem B533263 : Blo 207808 533263 := bstep (se 1 (by rfl) ⟨399947, by rfl⟩ : syracuseStep 533263 = 799895) B799895
theorem B533537 : Blo 207808 533537 := bstep (se 2 (by rfl) ⟨200076, by rfl⟩ : syracuseStep 533537 = 400153) B400153
theorem B2401325 : Blo 207808 2401325 := bstep (se 3 (by rfl) ⟨450248, by rfl⟩ : syracuseStep 2401325 = 900497) B900497
theorem B1057859 : Blo 207808 1057859 := bstep (se 1 (by rfl) ⟨793394, by rfl⟩ : syracuseStep 1057859 = 1586789) B1586789
theorem B762967 : Blo 207808 762967 := bstep (se 1 (by rfl) ⟨572225, by rfl⟩ : syracuseStep 762967 = 1144451) B1144451
theorem B599329 : Blo 207808 599329 := bstep (se 2 (by rfl) ⟨224748, by rfl⟩ : syracuseStep 599329 = 449497) B449497
theorem B468359 : Blo 207808 468359 := bstep (se 1 (by rfl) ⟨351269, by rfl⟩ : syracuseStep 468359 = 702539) B702539
theorem B1058183 : Blo 207808 1058183 := bstep (se 1 (by rfl) ⟨793637, by rfl⟩ : syracuseStep 1058183 = 1587275) B1587275
theorem B796189 : Blo 207808 796189 := bstep (se 3 (by rfl) ⟨149285, by rfl⟩ : syracuseStep 796189 = 298571) B298571
theorem B468539 : Blo 207808 468539 := bstep (se 1 (by rfl) ⟨351404, by rfl⟩ : syracuseStep 468539 = 702809) B702809
theorem B468665 : Blo 207808 468665 := bstep (se 2 (by rfl) ⟨175749, by rfl⟩ : syracuseStep 468665 = 351499) B351499
theorem B239419 : Blo 207808 239419 := bstep (se 1 (by rfl) ⟨179564, by rfl⟩ : syracuseStep 239419 = 359129) B359129
theorem B18425717 : Blo 207808 18425717 := bstep (se 5 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 18425717 = 1727411) B1727411
theorem B632711 : Blo 207808 632711 := bstep (se 1 (by rfl) ⟨474533, by rfl⟩ : syracuseStep 632711 = 949067) B949067
theorem B534539 : Blo 207808 534539 := bstep (se 1 (by rfl) ⟨400904, by rfl⟩ : syracuseStep 534539 = 801809) B801809
theorem B469007 : Blo 207808 469007 := bstep (se 1 (by rfl) ⟨351755, by rfl⟩ : syracuseStep 469007 = 703511) B703511
theorem B469025 : Blo 207808 469025 := bstep (se 2 (by rfl) ⟨175884, by rfl⟩ : syracuseStep 469025 = 351769) B351769
theorem B469367 : Blo 207808 469367 := bstep (se 1 (by rfl) ⟨352025, by rfl⟩ : syracuseStep 469367 = 704051) B704051
theorem B4827539 : Blo 207808 4827539 := bstep (se 1 (by rfl) ⟨3620654, by rfl⟩ : syracuseStep 4827539 = 7241309) B7241309
theorem B600605 : Blo 207808 600605 := bstep (se 3 (by rfl) ⟨112613, by rfl⟩ : syracuseStep 600605 = 225227) B225227
theorem B469547 : Blo 207808 469547 := bstep (se 1 (by rfl) ⟨352160, by rfl⟩ : syracuseStep 469547 = 704321) B704321
theorem B535187 : Blo 207808 535187 := bstep (se 1 (by rfl) ⟨401390, by rfl⟩ : syracuseStep 535187 = 802781) B802781
theorem B1583873 : Blo 207808 1583873 := bstep (se 2 (by rfl) ⟨593952, by rfl⟩ : syracuseStep 1583873 = 1187905) B1187905
theorem B600833 : Blo 207808 600833 := bstep (se 2 (by rfl) ⟨225312, by rfl⟩ : syracuseStep 600833 = 450625) B450625
theorem B469907 : Blo 207808 469907 := bstep (se 1 (by rfl) ⟨352430, by rfl⟩ : syracuseStep 469907 = 704861) B704861
theorem B535481 : Blo 207808 535481 := bstep (se 2 (by rfl) ⟨200805, by rfl⟩ : syracuseStep 535481 = 401611) B401611
theorem B469961 : Blo 207808 469961 := bstep (se 2 (by rfl) ⟨176235, by rfl⟩ : syracuseStep 469961 = 352471) B352471
theorem B207879 : Blo 207808 207879 := bstep (se 1 (by rfl) ⟨155909, by rfl⟩ : syracuseStep 207879 = 311819) B311819
theorem B207887 : Blo 207808 207887 := bstep (se 1 (by rfl) ⟨155915, by rfl⟩ : syracuseStep 207887 = 311831) B311831
theorem B207931 : Blo 207808 207931 := bstep (se 1 (by rfl) ⟨155948, by rfl⟩ : syracuseStep 207931 = 311897) B311897
theorem B601175 : Blo 207808 601175 := bstep (se 1 (by rfl) ⟨450881, by rfl⟩ : syracuseStep 601175 = 901763) B901763
theorem B208007 : Blo 207808 208007 := bstep (se 1 (by rfl) ⟨156005, by rfl⟩ : syracuseStep 208007 = 312011) B312011
theorem B208015 : Blo 207808 208015 := bstep (se 1 (by rfl) ⟨156011, by rfl⟩ : syracuseStep 208015 = 312023) B312023
theorem B208059 : Blo 207808 208059 := bstep (se 1 (by rfl) ⟨156044, by rfl⟩ : syracuseStep 208059 = 312089) B312089
theorem B601289 : Blo 207808 601289 := bstep (se 2 (by rfl) ⟨225483, by rfl⟩ : syracuseStep 601289 = 450967) B450967
theorem B208135 : Blo 207808 208135 := bstep (se 1 (by rfl) ⟨156101, by rfl⟩ : syracuseStep 208135 = 312203) B312203
theorem B208143 : Blo 207808 208143 := bstep (se 1 (by rfl) ⟨156107, by rfl⟩ : syracuseStep 208143 = 312215) B312215
theorem B208187 : Blo 207808 208187 := bstep (se 1 (by rfl) ⟨156140, by rfl⟩ : syracuseStep 208187 = 312281) B312281
theorem B208263 : Blo 207808 208263 := bstep (se 1 (by rfl) ⟨156197, by rfl⟩ : syracuseStep 208263 = 312395) B312395
theorem B208271 : Blo 207808 208271 := bstep (se 1 (by rfl) ⟨156203, by rfl⟩ : syracuseStep 208271 = 312407) B312407
theorem B568723 : Blo 207808 568723 := bstep (se 1 (by rfl) ⟨426542, by rfl⟩ : syracuseStep 568723 = 853085) B853085
theorem B503225 : Blo 207808 503225 := bstep (se 2 (by rfl) ⟨188709, by rfl⟩ : syracuseStep 503225 = 377419) B377419
theorem B208315 : Blo 207808 208315 := bstep (se 1 (by rfl) ⟨156236, by rfl⟩ : syracuseStep 208315 = 312473) B312473
theorem B208391 : Blo 207808 208391 := bstep (se 1 (by rfl) ⟨156293, by rfl⟩ : syracuseStep 208391 = 312587) B312587
theorem B208399 : Blo 207808 208399 := bstep (se 1 (by rfl) ⟨156299, by rfl⟩ : syracuseStep 208399 = 312599) B312599
theorem B2436637 : Blo 207808 2436637 := bstep (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) B913739
theorem B208443 : Blo 207808 208443 := bstep (se 1 (by rfl) ⟨156332, by rfl⟩ : syracuseStep 208443 = 312665) B312665
theorem B2010743 : Blo 207808 2010743 := bstep (se 1 (by rfl) ⟨1508057, by rfl⟩ : syracuseStep 2010743 = 3016115) B3016115
theorem B208519 : Blo 207808 208519 := bstep (se 1 (by rfl) ⟨156389, by rfl⟩ : syracuseStep 208519 = 312779) B312779
theorem B470663 : Blo 207808 470663 := bstep (se 1 (by rfl) ⟨352997, by rfl⟩ : syracuseStep 470663 = 705995) B705995
theorem B208527 : Blo 207808 208527 := bstep (se 1 (by rfl) ⟨156395, by rfl⟩ : syracuseStep 208527 = 312791) B312791
theorem B208571 : Blo 207808 208571 := bstep (se 1 (by rfl) ⟨156428, by rfl⟩ : syracuseStep 208571 = 312857) B312857
theorem B1912577 : Blo 207808 1912577 := bstep (se 2 (by rfl) ⟨717216, by rfl⟩ : syracuseStep 1912577 = 1434433) B1434433
theorem B208647 : Blo 207808 208647 := bstep (se 1 (by rfl) ⟨156485, by rfl⟩ : syracuseStep 208647 = 312971) B312971
theorem B208655 : Blo 207808 208655 := bstep (se 1 (by rfl) ⟨156491, by rfl⟩ : syracuseStep 208655 = 312983) B312983
theorem B208699 : Blo 207808 208699 := bstep (se 1 (by rfl) ⟨156524, by rfl⟩ : syracuseStep 208699 = 313049) B313049
theorem B470843 : Blo 207808 470843 := bstep (se 1 (by rfl) ⟨353132, by rfl⟩ : syracuseStep 470843 = 706265) B706265
theorem B208775 : Blo 207808 208775 := bstep (se 1 (by rfl) ⟨156581, by rfl⟩ : syracuseStep 208775 = 313163) B313163
theorem B208783 : Blo 207808 208783 := bstep (se 1 (by rfl) ⟨156587, by rfl⟩ : syracuseStep 208783 = 313175) B313175
theorem B503705 : Blo 207808 503705 := bstep (se 2 (by rfl) ⟨188889, by rfl⟩ : syracuseStep 503705 = 377779) B377779
theorem B470969 : Blo 207808 470969 := bstep (se 2 (by rfl) ⟨176613, by rfl⟩ : syracuseStep 470969 = 353227) B353227
theorem B208827 : Blo 207808 208827 := bstep (se 1 (by rfl) ⟨156620, by rfl⟩ : syracuseStep 208827 = 313241) B313241
theorem B208903 : Blo 207808 208903 := bstep (se 1 (by rfl) ⟨156677, by rfl⟩ : syracuseStep 208903 = 313355) B313355
theorem B208911 : Blo 207808 208911 := bstep (se 1 (by rfl) ⟨156683, by rfl⟩ : syracuseStep 208911 = 313367) B313367
theorem B208955 : Blo 207808 208955 := bstep (se 1 (by rfl) ⟨156716, by rfl⟩ : syracuseStep 208955 = 313433) B313433
theorem B209031 : Blo 207808 209031 := bstep (se 1 (by rfl) ⟨156773, by rfl⟩ : syracuseStep 209031 = 313547) B313547
theorem B209039 : Blo 207808 209039 := bstep (se 1 (by rfl) ⟨156779, by rfl⟩ : syracuseStep 209039 = 313559) B313559
theorem B209083 : Blo 207808 209083 := bstep (se 1 (by rfl) ⟨156812, by rfl⟩ : syracuseStep 209083 = 313625) B313625
theorem B209159 : Blo 207808 209159 := bstep (se 1 (by rfl) ⟨156869, by rfl⟩ : syracuseStep 209159 = 313739) B313739
theorem B209167 : Blo 207808 209167 := bstep (se 1 (by rfl) ⟨156875, by rfl⟩ : syracuseStep 209167 = 313751) B313751
theorem B471311 : Blo 207808 471311 := bstep (se 1 (by rfl) ⟨353483, by rfl⟩ : syracuseStep 471311 = 706967) B706967
theorem B471329 : Blo 207808 471329 := bstep (se 2 (by rfl) ⟨176748, by rfl⟩ : syracuseStep 471329 = 353497) B353497
theorem B209211 : Blo 207808 209211 := bstep (se 1 (by rfl) ⟨156908, by rfl⟩ : syracuseStep 209211 = 313817) B313817
theorem B799091 : Blo 207808 799091 := bstep (se 1 (by rfl) ⟨599318, by rfl⟩ : syracuseStep 799091 = 1198637) B1198637
theorem B209287 : Blo 207808 209287 := bstep (se 1 (by rfl) ⟨156965, by rfl⟩ : syracuseStep 209287 = 313931) B313931
theorem B209295 : Blo 207808 209295 := bstep (se 1 (by rfl) ⟨156971, by rfl⟩ : syracuseStep 209295 = 313943) B313943
theorem B209339 : Blo 207808 209339 := bstep (se 1 (by rfl) ⟨157004, by rfl⟩ : syracuseStep 209339 = 314009) B314009
theorem B209415 : Blo 207808 209415 := bstep (se 1 (by rfl) ⟨157061, by rfl⟩ : syracuseStep 209415 = 314123) B314123
theorem B209423 : Blo 207808 209423 := bstep (se 1 (by rfl) ⟨157067, by rfl⟩ : syracuseStep 209423 = 314135) B314135
theorem B209467 : Blo 207808 209467 := bstep (se 1 (by rfl) ⟨157100, by rfl⟩ : syracuseStep 209467 = 314201) B314201
theorem B471671 : Blo 207808 471671 := bstep (se 1 (by rfl) ⟨353753, by rfl⟩ : syracuseStep 471671 = 707507) B707507
theorem B209543 : Blo 207808 209543 := bstep (se 1 (by rfl) ⟨157157, by rfl⟩ : syracuseStep 209543 = 314315) B314315
theorem B209551 : Blo 207808 209551 := bstep (se 1 (by rfl) ⟨157163, by rfl⟩ : syracuseStep 209551 = 314327) B314327
theorem B209595 : Blo 207808 209595 := bstep (se 1 (by rfl) ⟨157196, by rfl⟩ : syracuseStep 209595 = 314393) B314393
theorem B209671 : Blo 207808 209671 := bstep (se 1 (by rfl) ⟨157253, by rfl⟩ : syracuseStep 209671 = 314507) B314507
theorem B209679 : Blo 207808 209679 := bstep (se 1 (by rfl) ⟨157259, by rfl⟩ : syracuseStep 209679 = 314519) B314519
theorem B471851 : Blo 207808 471851 := bstep (se 1 (by rfl) ⟨353888, by rfl⟩ : syracuseStep 471851 = 707777) B707777
theorem B209723 : Blo 207808 209723 := bstep (se 1 (by rfl) ⟨157292, by rfl⟩ : syracuseStep 209723 = 314585) B314585
theorem B1061747 : Blo 207808 1061747 := bstep (se 1 (by rfl) ⟨796310, by rfl⟩ : syracuseStep 1061747 = 1592621) B1592621
theorem B209799 : Blo 207808 209799 := bstep (se 1 (by rfl) ⟨157349, by rfl⟩ : syracuseStep 209799 = 314699) B314699
theorem B209807 : Blo 207808 209807 := bstep (se 1 (by rfl) ⟨157355, by rfl⟩ : syracuseStep 209807 = 314711) B314711
theorem B603065 : Blo 207808 603065 := bstep (se 2 (by rfl) ⟨226149, by rfl⟩ : syracuseStep 603065 = 452299) B452299
theorem B209851 : Blo 207808 209851 := bstep (se 1 (by rfl) ⟨157388, by rfl⟩ : syracuseStep 209851 = 314777) B314777
theorem B209927 : Blo 207808 209927 := bstep (se 1 (by rfl) ⟨157445, by rfl⟩ : syracuseStep 209927 = 314891) B314891
theorem B209935 : Blo 207808 209935 := bstep (se 1 (by rfl) ⟨157451, by rfl⟩ : syracuseStep 209935 = 314903) B314903
theorem B406561 : Blo 207808 406561 := bstep (se 2 (by rfl) ⟨152460, by rfl⟩ : syracuseStep 406561 = 304921) B304921
theorem B209979 : Blo 207808 209979 := bstep (se 1 (by rfl) ⟨157484, by rfl⟩ : syracuseStep 209979 = 314969) B314969
theorem B603251 : Blo 207808 603251 := bstep (se 1 (by rfl) ⟨452438, by rfl⟩ : syracuseStep 603251 = 904877) B904877
theorem B210055 : Blo 207808 210055 := bstep (se 1 (by rfl) ⟨157541, by rfl⟩ : syracuseStep 210055 = 315083) B315083
theorem B210063 : Blo 207808 210063 := bstep (se 1 (by rfl) ⟨157547, by rfl⟩ : syracuseStep 210063 = 315095) B315095
theorem B472211 : Blo 207808 472211 := bstep (se 1 (by rfl) ⟨354158, by rfl⟩ : syracuseStep 472211 = 708317) B708317
theorem B210107 : Blo 207808 210107 := bstep (se 1 (by rfl) ⟨157580, by rfl⟩ : syracuseStep 210107 = 315161) B315161
theorem B472265 : Blo 207808 472265 := bstep (se 2 (by rfl) ⟨177099, by rfl⟩ : syracuseStep 472265 = 354199) B354199
theorem B210183 : Blo 207808 210183 := bstep (se 1 (by rfl) ⟨157637, by rfl⟩ : syracuseStep 210183 = 315275) B315275
theorem B210191 : Blo 207808 210191 := bstep (se 1 (by rfl) ⟨157643, by rfl⟩ : syracuseStep 210191 = 315287) B315287
theorem B701729 : Blo 207808 701729 := bstep (se 2 (by rfl) ⟨263148, by rfl⟩ : syracuseStep 701729 = 526297) B526297
theorem B210235 : Blo 207808 210235 := bstep (se 1 (by rfl) ⟨157676, by rfl⟩ : syracuseStep 210235 = 315353) B315353
theorem B1062233 : Blo 207808 1062233 := bstep (se 2 (by rfl) ⟨398337, by rfl⟩ : syracuseStep 1062233 = 796675) B796675
theorem B210311 : Blo 207808 210311 := bstep (se 1 (by rfl) ⟨157733, by rfl⟩ : syracuseStep 210311 = 315467) B315467
theorem B210319 : Blo 207808 210319 := bstep (se 1 (by rfl) ⟨157739, by rfl⟩ : syracuseStep 210319 = 315479) B315479
theorem B210363 : Blo 207808 210363 := bstep (se 1 (by rfl) ⟨157772, by rfl⟩ : syracuseStep 210363 = 315545) B315545
theorem B210439 : Blo 207808 210439 := bstep (se 1 (by rfl) ⟨157829, by rfl⟩ : syracuseStep 210439 = 315659) B315659
theorem B210447 : Blo 207808 210447 := bstep (se 1 (by rfl) ⟨157835, by rfl⟩ : syracuseStep 210447 = 315671) B315671
theorem B210491 : Blo 207808 210491 := bstep (se 1 (by rfl) ⟨157868, by rfl⟩ : syracuseStep 210491 = 315737) B315737
theorem B210567 : Blo 207808 210567 := bstep (se 1 (by rfl) ⟨157925, by rfl⟩ : syracuseStep 210567 = 315851) B315851
theorem B210575 : Blo 207808 210575 := bstep (se 1 (by rfl) ⟨157931, by rfl⟩ : syracuseStep 210575 = 315863) B315863
theorem B210619 : Blo 207808 210619 := bstep (se 1 (by rfl) ⟨157964, by rfl⟩ : syracuseStep 210619 = 315929) B315929
theorem B210695 : Blo 207808 210695 := bstep (se 1 (by rfl) ⟨158021, by rfl⟩ : syracuseStep 210695 = 316043) B316043
theorem B669455 : Blo 207808 669455 := bstep (se 1 (by rfl) ⟨502091, by rfl⟩ : syracuseStep 669455 = 1004183) B1004183
theorem B210703 : Blo 207808 210703 := bstep (se 1 (by rfl) ⟨158027, by rfl⟩ : syracuseStep 210703 = 316055) B316055
theorem B210747 : Blo 207808 210747 := bstep (se 1 (by rfl) ⟨158060, by rfl⟩ : syracuseStep 210747 = 316121) B316121
theorem B702323 : Blo 207808 702323 := bstep (se 1 (by rfl) ⟨526742, by rfl⟩ : syracuseStep 702323 = 1053485) B1053485
theorem B472967 : Blo 207808 472967 := bstep (se 1 (by rfl) ⟨354725, by rfl⟩ : syracuseStep 472967 = 709451) B709451
theorem B210823 : Blo 207808 210823 := bstep (se 1 (by rfl) ⟨158117, by rfl⟩ : syracuseStep 210823 = 316235) B316235
theorem B210831 : Blo 207808 210831 := bstep (se 1 (by rfl) ⟨158123, by rfl⟩ : syracuseStep 210831 = 316247) B316247
theorem B210875 : Blo 207808 210875 := bstep (se 1 (by rfl) ⟨158156, by rfl⟩ : syracuseStep 210875 = 316313) B316313
theorem B210951 : Blo 207808 210951 := bstep (se 1 (by rfl) ⟨158213, by rfl⟩ : syracuseStep 210951 = 316427) B316427
theorem B210959 : Blo 207808 210959 := bstep (se 1 (by rfl) ⟨158219, by rfl⟩ : syracuseStep 210959 = 316439) B316439
theorem B473147 : Blo 207808 473147 := bstep (se 1 (by rfl) ⟨354860, by rfl⟩ : syracuseStep 473147 = 709721) B709721
theorem B211003 : Blo 207808 211003 := bstep (se 1 (by rfl) ⟨158252, by rfl⟩ : syracuseStep 211003 = 316505) B316505
theorem B211079 : Blo 207808 211079 := bstep (se 1 (by rfl) ⟨158309, by rfl⟩ : syracuseStep 211079 = 316619) B316619
theorem B211087 : Blo 207808 211087 := bstep (se 1 (by rfl) ⟨158315, by rfl⟩ : syracuseStep 211087 = 316631) B316631
theorem B374969 : Blo 207808 374969 := bstep (se 2 (by rfl) ⟨140613, by rfl⟩ : syracuseStep 374969 = 281227) B281227
theorem B473273 : Blo 207808 473273 := bstep (se 2 (by rfl) ⟨177477, by rfl⟩ : syracuseStep 473273 = 354955) B354955
theorem B211131 : Blo 207808 211131 := bstep (se 1 (by rfl) ⟨158348, by rfl⟩ : syracuseStep 211131 = 316697) B316697
theorem B1784045 : Blo 207808 1784045 := bstep (se 3 (by rfl) ⟨334508, by rfl⟩ : syracuseStep 1784045 = 669017) B669017
theorem B211207 : Blo 207808 211207 := bstep (se 1 (by rfl) ⟨158405, by rfl⟩ : syracuseStep 211207 = 316811) B316811
theorem B211215 : Blo 207808 211215 := bstep (se 1 (by rfl) ⟨158411, by rfl⟩ : syracuseStep 211215 = 316823) B316823
theorem B211259 : Blo 207808 211259 := bstep (se 1 (by rfl) ⟨158444, by rfl⟩ : syracuseStep 211259 = 316889) B316889
theorem B211335 : Blo 207808 211335 := bstep (se 1 (by rfl) ⟨158501, by rfl⟩ : syracuseStep 211335 = 317003) B317003
theorem B211343 : Blo 207808 211343 := bstep (se 1 (by rfl) ⟨158507, by rfl⟩ : syracuseStep 211343 = 317015) B317015
theorem B211387 : Blo 207808 211387 := bstep (se 1 (by rfl) ⟨158540, by rfl⟩ : syracuseStep 211387 = 317081) B317081
theorem B211463 : Blo 207808 211463 := bstep (se 1 (by rfl) ⟨158597, by rfl⟩ : syracuseStep 211463 = 317195) B317195
theorem B473615 : Blo 207808 473615 := bstep (se 1 (by rfl) ⟨355211, by rfl⟩ : syracuseStep 473615 = 710423) B710423
theorem B211471 : Blo 207808 211471 := bstep (se 1 (by rfl) ⟨158603, by rfl⟩ : syracuseStep 211471 = 317207) B317207
theorem B473633 : Blo 207808 473633 := bstep (se 2 (by rfl) ⟨177612, by rfl⟩ : syracuseStep 473633 = 355225) B355225
theorem B801323 : Blo 207808 801323 := bstep (se 1 (by rfl) ⟨600992, by rfl⟩ : syracuseStep 801323 = 1201985) B1201985
theorem B211515 : Blo 207808 211515 := bstep (se 1 (by rfl) ⟨158636, by rfl⟩ : syracuseStep 211515 = 317273) B317273
theorem B1522243 : Blo 207808 1522243 := bstep (se 1 (by rfl) ⟨1141682, by rfl⟩ : syracuseStep 1522243 = 2283365) B2283365
theorem B3586679 : Blo 207808 3586679 := bstep (se 1 (by rfl) ⟨2690009, by rfl⟩ : syracuseStep 3586679 = 5380019) B5380019
theorem B211591 : Blo 207808 211591 := bstep (se 1 (by rfl) ⟨158693, by rfl⟩ : syracuseStep 211591 = 317387) B317387
theorem B211599 : Blo 207808 211599 := bstep (se 1 (by rfl) ⟨158699, by rfl⟩ : syracuseStep 211599 = 317399) B317399
theorem B211643 : Blo 207808 211643 := bstep (se 1 (by rfl) ⟨158732, by rfl⟩ : syracuseStep 211643 = 317465) B317465
theorem B211719 : Blo 207808 211719 := bstep (se 1 (by rfl) ⟨158789, by rfl⟩ : syracuseStep 211719 = 317579) B317579
theorem B211727 : Blo 207808 211727 := bstep (se 1 (by rfl) ⟨158795, by rfl⟩ : syracuseStep 211727 = 317591) B317591
theorem B211771 : Blo 207808 211771 := bstep (se 1 (by rfl) ⟨158828, by rfl⟩ : syracuseStep 211771 = 317657) B317657
theorem B473975 : Blo 207808 473975 := bstep (se 1 (by rfl) ⟨355481, by rfl⟩ : syracuseStep 473975 = 710963) B710963
theorem B1621003 : Blo 207808 1621003 := bstep (se 1 (by rfl) ⟨1215752, by rfl⟩ : syracuseStep 1621003 = 2431505) B2431505
theorem B1588247 : Blo 207808 1588247 := bstep (se 1 (by rfl) ⟨1191185, by rfl⟩ : syracuseStep 1588247 = 2382371) B2382371
theorem B474155 : Blo 207808 474155 := bstep (se 1 (by rfl) ⟨355616, by rfl⟩ : syracuseStep 474155 = 711233) B711233
theorem B1064339 : Blo 207808 1064339 := bstep (se 1 (by rfl) ⟨798254, by rfl⟩ : syracuseStep 1064339 = 1596509) B1596509
theorem B474515 : Blo 207808 474515 := bstep (se 1 (by rfl) ⟨355886, by rfl⟩ : syracuseStep 474515 = 711773) B711773
theorem B376265 : Blo 207808 376265 := bstep (se 2 (by rfl) ⟨141099, by rfl⟩ : syracuseStep 376265 = 282199) B282199
theorem B474569 : Blo 207808 474569 := bstep (se 2 (by rfl) ⟨177963, by rfl⟩ : syracuseStep 474569 = 355927) B355927
theorem B474743 : Blo 207808 474743 := bstep (se 1 (by rfl) ⟨356057, by rfl⟩ : syracuseStep 474743 = 712115) B712115
theorem B1195721 : Blo 207808 1195721 := bstep (se 2 (by rfl) ⟨448395, by rfl⟩ : syracuseStep 1195721 = 896791) B896791
theorem B638867 : Blo 207808 638867 := bstep (se 1 (by rfl) ⟨479150, by rfl⟩ : syracuseStep 638867 = 958301) B958301
theorem B507833 : Blo 207808 507833 := bstep (se 2 (by rfl) ⟨190437, by rfl⟩ : syracuseStep 507833 = 380875) B380875
theorem B901181 : Blo 207808 901181 := bstep (se 3 (by rfl) ⟨168971, by rfl⟩ : syracuseStep 901181 = 337943) B337943
theorem B475271 : Blo 207808 475271 := bstep (se 1 (by rfl) ⟨356453, by rfl⟩ : syracuseStep 475271 = 712907) B712907
theorem B9257161 : Blo 207808 9257161 := bstep (se 2 (by rfl) ⟨3471435, by rfl⟩ : syracuseStep 9257161 = 6942871) B6942871
theorem B475451 : Blo 207808 475451 := bstep (se 1 (by rfl) ⟨356588, by rfl⟩ : syracuseStep 475451 = 713177) B713177
theorem B704915 : Blo 207808 704915 := bstep (se 1 (by rfl) ⟨528686, by rfl⟩ : syracuseStep 704915 = 1057373) B1057373
theorem B901523 : Blo 207808 901523 := bstep (se 1 (by rfl) ⟨676142, by rfl⟩ : syracuseStep 901523 = 1352285) B1352285
theorem B311723 : Blo 207808 311723 := bstep (se 1 (by rfl) ⟨233792, by rfl⟩ : syracuseStep 311723 = 467585) B467585
theorem B475577 : Blo 207808 475577 := bstep (se 2 (by rfl) ⟨178341, by rfl⟩ : syracuseStep 475577 = 356683) B356683
theorem B311753 : Blo 207808 311753 := bstep (se 2 (by rfl) ⟨116907, by rfl⟩ : syracuseStep 311753 = 233815) B233815
theorem B311867 : Blo 207808 311867 := bstep (se 1 (by rfl) ⟨233900, by rfl⟩ : syracuseStep 311867 = 467801) B467801
theorem B311927 : Blo 207808 311927 := bstep (se 1 (by rfl) ⟨233945, by rfl⟩ : syracuseStep 311927 = 467891) B467891
theorem B311951 : Blo 207808 311951 := bstep (se 1 (by rfl) ⟨233963, by rfl⟩ : syracuseStep 311951 = 467927) B467927
theorem B311993 : Blo 207808 311993 := bstep (se 2 (by rfl) ⟨116997, by rfl⟩ : syracuseStep 311993 = 233995) B233995
theorem B312071 : Blo 207808 312071 := bstep (se 1 (by rfl) ⟨234053, by rfl⟩ : syracuseStep 312071 = 468107) B468107
theorem B475919 : Blo 207808 475919 := bstep (se 1 (by rfl) ⟨356939, by rfl⟩ : syracuseStep 475919 = 713879) B713879
theorem B475937 : Blo 207808 475937 := bstep (se 2 (by rfl) ⟨178476, by rfl⟩ : syracuseStep 475937 = 356953) B356953
theorem B312107 : Blo 207808 312107 := bstep (se 1 (by rfl) ⟨234080, by rfl⟩ : syracuseStep 312107 = 468161) B468161
theorem B2016049 : Blo 207808 2016049 := bstep (se 2 (by rfl) ⟨756018, by rfl⟩ : syracuseStep 2016049 = 1512037) B1512037
theorem B312137 : Blo 207808 312137 := bstep (se 2 (by rfl) ⟨117051, by rfl⟩ : syracuseStep 312137 = 234103) B234103
theorem B2278307 : Blo 207808 2278307 := bstep (se 1 (by rfl) ⟨1708730, by rfl⟩ : syracuseStep 2278307 = 3417461) B3417461
theorem B312251 : Blo 207808 312251 := bstep (se 1 (by rfl) ⟨234188, by rfl⟩ : syracuseStep 312251 = 468377) B468377
theorem B312311 : Blo 207808 312311 := bstep (se 1 (by rfl) ⟨234233, by rfl⟩ : syracuseStep 312311 = 468467) B468467
theorem B1000451 : Blo 207808 1000451 := bstep (se 1 (by rfl) ⟨750338, by rfl⟩ : syracuseStep 1000451 = 1500677) B1500677
theorem B312335 : Blo 207808 312335 := bstep (se 1 (by rfl) ⟨234251, by rfl⟩ : syracuseStep 312335 = 468503) B468503
theorem B1131563 : Blo 207808 1131563 := bstep (se 1 (by rfl) ⟨848672, by rfl⟩ : syracuseStep 1131563 = 1697345) B1697345
theorem B312377 : Blo 207808 312377 := bstep (se 2 (by rfl) ⟨117141, by rfl⟩ : syracuseStep 312377 = 234283) B234283
theorem B476279 : Blo 207808 476279 := bstep (se 1 (by rfl) ⟨357209, by rfl⟩ : syracuseStep 476279 = 714419) B714419
theorem B312455 : Blo 207808 312455 := bstep (se 1 (by rfl) ⟨234341, by rfl⟩ : syracuseStep 312455 = 468683) B468683
theorem B312491 : Blo 207808 312491 := bstep (se 1 (by rfl) ⟨234368, by rfl⟩ : syracuseStep 312491 = 468737) B468737
theorem B312521 : Blo 207808 312521 := bstep (se 2 (by rfl) ⟨117195, by rfl⟩ : syracuseStep 312521 = 234391) B234391
theorem B476459 : Blo 207808 476459 := bstep (se 1 (by rfl) ⟨357344, by rfl⟩ : syracuseStep 476459 = 714689) B714689
theorem B312635 : Blo 207808 312635 := bstep (se 1 (by rfl) ⟨234476, by rfl⟩ : syracuseStep 312635 = 468953) B468953
theorem B312695 : Blo 207808 312695 := bstep (se 1 (by rfl) ⟨234521, by rfl⟩ : syracuseStep 312695 = 469043) B469043
theorem B312719 : Blo 207808 312719 := bstep (se 1 (by rfl) ⟨234539, by rfl⟩ : syracuseStep 312719 = 469079) B469079
theorem B312761 : Blo 207808 312761 := bstep (se 2 (by rfl) ⟨117285, by rfl⟩ : syracuseStep 312761 = 234571) B234571
theorem B312839 : Blo 207808 312839 := bstep (se 1 (by rfl) ⟨234629, by rfl⟩ : syracuseStep 312839 = 469259) B469259
theorem B312875 : Blo 207808 312875 := bstep (se 1 (by rfl) ⟨234656, by rfl⟩ : syracuseStep 312875 = 469313) B469313
theorem B1197611 : Blo 207808 1197611 := bstep (se 1 (by rfl) ⟨898208, by rfl⟩ : syracuseStep 1197611 = 1796417) B1796417
theorem B312905 : Blo 207808 312905 := bstep (se 2 (by rfl) ⟨117339, by rfl⟩ : syracuseStep 312905 = 234679) B234679
theorem B313019 : Blo 207808 313019 := bstep (se 1 (by rfl) ⟨234764, by rfl⟩ : syracuseStep 313019 = 469529) B469529
theorem B313079 : Blo 207808 313079 := bstep (se 1 (by rfl) ⟨234809, by rfl⟩ : syracuseStep 313079 = 469619) B469619
theorem B4572929 : Blo 207808 4572929 := bstep (se 2 (by rfl) ⟨1714848, by rfl⟩ : syracuseStep 4572929 = 3429697) B3429697
theorem B313103 : Blo 207808 313103 := bstep (se 1 (by rfl) ⟨234827, by rfl⟩ : syracuseStep 313103 = 469655) B469655
theorem B706319 : Blo 207808 706319 := bstep (se 1 (by rfl) ⟨529739, by rfl⟩ : syracuseStep 706319 = 1059479) B1059479
theorem B313145 : Blo 207808 313145 := bstep (se 2 (by rfl) ⟨117429, by rfl⟩ : syracuseStep 313145 = 234859) B234859
theorem B608087 : Blo 207808 608087 := bstep (se 1 (by rfl) ⟨456065, by rfl⟩ : syracuseStep 608087 = 912131) B912131
theorem B444295 : Blo 207808 444295 := bstep (se 1 (by rfl) ⟨333221, by rfl⟩ : syracuseStep 444295 = 666443) B666443
theorem B313223 : Blo 207808 313223 := bstep (se 1 (by rfl) ⟨234917, by rfl⟩ : syracuseStep 313223 = 469835) B469835
theorem B313259 : Blo 207808 313259 := bstep (se 1 (by rfl) ⟨234944, by rfl⟩ : syracuseStep 313259 = 469889) B469889
theorem B313289 : Blo 207808 313289 := bstep (se 2 (by rfl) ⟨117483, by rfl⟩ : syracuseStep 313289 = 234967) B234967
theorem B706589 : Blo 207808 706589 := bstep (se 3 (by rfl) ⟨132485, by rfl⟩ : syracuseStep 706589 = 264971) B264971
theorem B313403 : Blo 207808 313403 := bstep (se 1 (by rfl) ⟨235052, by rfl⟩ : syracuseStep 313403 = 470105) B470105
theorem B313463 : Blo 207808 313463 := bstep (se 1 (by rfl) ⟨235097, by rfl⟩ : syracuseStep 313463 = 470195) B470195
theorem B313487 : Blo 207808 313487 := bstep (se 1 (by rfl) ⟨235115, by rfl⟩ : syracuseStep 313487 = 470231) B470231
theorem B313529 : Blo 207808 313529 := bstep (se 2 (by rfl) ⟨117573, by rfl⟩ : syracuseStep 313529 = 235147) B235147
theorem B313607 : Blo 207808 313607 := bstep (se 1 (by rfl) ⟨235205, by rfl⟩ : syracuseStep 313607 = 470411) B470411
theorem B313643 : Blo 207808 313643 := bstep (se 1 (by rfl) ⟨235232, by rfl⟩ : syracuseStep 313643 = 470465) B470465
theorem B313673 : Blo 207808 313673 := bstep (se 2 (by rfl) ⟨117627, by rfl⟩ : syracuseStep 313673 = 235255) B235255
theorem B2279825 : Blo 207808 2279825 := bstep (se 2 (by rfl) ⟨854934, by rfl⟩ : syracuseStep 2279825 = 1709869) B1709869
theorem B1067417 : Blo 207808 1067417 := bstep (se 2 (by rfl) ⟨400281, by rfl⟩ : syracuseStep 1067417 = 800563) B800563
theorem B313787 : Blo 207808 313787 := bstep (se 1 (by rfl) ⟨235340, by rfl⟩ : syracuseStep 313787 = 470681) B470681
theorem B313847 : Blo 207808 313847 := bstep (se 1 (by rfl) ⟨235385, by rfl⟩ : syracuseStep 313847 = 470771) B470771
theorem B1788419 : Blo 207808 1788419 := bstep (se 1 (by rfl) ⟨1341314, by rfl⟩ : syracuseStep 1788419 = 2682629) B2682629
theorem B313871 : Blo 207808 313871 := bstep (se 1 (by rfl) ⟨235403, by rfl⟩ : syracuseStep 313871 = 470807) B470807
theorem B313913 : Blo 207808 313913 := bstep (se 2 (by rfl) ⟨117717, by rfl⟩ : syracuseStep 313913 = 235435) B235435
theorem B313991 : Blo 207808 313991 := bstep (se 1 (by rfl) ⟨235493, by rfl⟩ : syracuseStep 313991 = 470987) B470987
theorem B314027 : Blo 207808 314027 := bstep (se 1 (by rfl) ⟨235520, by rfl⟩ : syracuseStep 314027 = 471041) B471041
theorem B314057 : Blo 207808 314057 := bstep (se 2 (by rfl) ⟨117771, by rfl⟩ : syracuseStep 314057 = 235543) B235543
theorem B314171 : Blo 207808 314171 := bstep (se 1 (by rfl) ⟨235628, by rfl⟩ : syracuseStep 314171 = 471257) B471257
theorem B904051 : Blo 207808 904051 := bstep (se 1 (by rfl) ⟨678038, by rfl⟩ : syracuseStep 904051 = 1356077) B1356077
theorem B314231 : Blo 207808 314231 := bstep (se 1 (by rfl) ⟨235673, by rfl⟩ : syracuseStep 314231 = 471347) B471347
theorem B314255 : Blo 207808 314255 := bstep (se 1 (by rfl) ⟨235691, by rfl⟩ : syracuseStep 314255 = 471383) B471383
theorem B314297 : Blo 207808 314297 := bstep (se 2 (by rfl) ⟨117861, by rfl⟩ : syracuseStep 314297 = 235723) B235723
theorem B1100729 : Blo 207808 1100729 := bstep (se 2 (by rfl) ⟨412773, by rfl⟩ : syracuseStep 1100729 = 825547) B825547
theorem B904121 : Blo 207808 904121 := bstep (se 2 (by rfl) ⟨339045, by rfl⟩ : syracuseStep 904121 = 678091) B678091
theorem B1199069 : Blo 207808 1199069 := bstep (se 3 (by rfl) ⟨224825, by rfl⟩ : syracuseStep 1199069 = 449651) B449651
theorem B314375 : Blo 207808 314375 := bstep (se 1 (by rfl) ⟨235781, by rfl⟩ : syracuseStep 314375 = 471563) B471563
theorem B2411531 : Blo 207808 2411531 := bstep (se 1 (by rfl) ⟨1808648, by rfl⟩ : syracuseStep 2411531 = 3617297) B3617297
theorem B281615 : Blo 207808 281615 := bstep (se 1 (by rfl) ⟨211211, by rfl⟩ : syracuseStep 281615 = 422423) B422423
theorem B314411 : Blo 207808 314411 := bstep (se 1 (by rfl) ⟨235808, by rfl⟩ : syracuseStep 314411 = 471617) B471617
theorem B314441 : Blo 207808 314441 := bstep (se 2 (by rfl) ⟨117915, by rfl⟩ : syracuseStep 314441 = 235831) B235831
theorem B314555 : Blo 207808 314555 := bstep (se 1 (by rfl) ⟨235916, by rfl⟩ : syracuseStep 314555 = 471833) B471833
theorem B314615 : Blo 207808 314615 := bstep (se 1 (by rfl) ⟨235961, by rfl⟩ : syracuseStep 314615 = 471923) B471923
theorem B314639 : Blo 207808 314639 := bstep (se 1 (by rfl) ⟨235979, by rfl⟩ : syracuseStep 314639 = 471959) B471959
theorem B314681 : Blo 207808 314681 := bstep (se 2 (by rfl) ⟨118005, by rfl⟩ : syracuseStep 314681 = 236011) B236011
theorem B609623 : Blo 207808 609623 := bstep (se 1 (by rfl) ⟨457217, by rfl⟩ : syracuseStep 609623 = 914435) B914435
theorem B314759 : Blo 207808 314759 := bstep (se 1 (by rfl) ⟨236069, by rfl⟩ : syracuseStep 314759 = 472139) B472139
theorem B707993 : Blo 207808 707993 := bstep (se 2 (by rfl) ⟨265497, by rfl⟩ : syracuseStep 707993 = 530995) B530995
theorem B314795 : Blo 207808 314795 := bstep (se 1 (by rfl) ⟨236096, by rfl⟩ : syracuseStep 314795 = 472193) B472193
theorem B314825 : Blo 207808 314825 := bstep (se 2 (by rfl) ⟨118059, by rfl⟩ : syracuseStep 314825 = 236119) B236119
theorem B1199569 : Blo 207808 1199569 := bstep (se 2 (by rfl) ⟨449838, by rfl⟩ : syracuseStep 1199569 = 899677) B899677
theorem B773675 : Blo 207808 773675 := bstep (se 1 (by rfl) ⟨580256, by rfl⟩ : syracuseStep 773675 = 1160513) B1160513
theorem B314939 : Blo 207808 314939 := bstep (se 1 (by rfl) ⟨236204, by rfl⟩ : syracuseStep 314939 = 472409) B472409
theorem B314999 : Blo 207808 314999 := bstep (se 1 (by rfl) ⟨236249, by rfl⟩ : syracuseStep 314999 = 472499) B472499
theorem B315023 : Blo 207808 315023 := bstep (se 1 (by rfl) ⟨236267, by rfl⟩ : syracuseStep 315023 = 472535) B472535
theorem B315065 : Blo 207808 315065 := bstep (se 2 (by rfl) ⟨118149, by rfl⟩ : syracuseStep 315065 = 236299) B236299
theorem B315143 : Blo 207808 315143 := bstep (se 1 (by rfl) ⟨236357, by rfl⟩ : syracuseStep 315143 = 472715) B472715
theorem B380705 : Blo 207808 380705 := bstep (se 2 (by rfl) ⟨142764, by rfl⟩ : syracuseStep 380705 = 285529) B285529
theorem B446251 : Blo 207808 446251 := bstep (se 1 (by rfl) ⟨334688, by rfl⟩ : syracuseStep 446251 = 669377) B669377
theorem B315179 : Blo 207808 315179 := bstep (se 1 (by rfl) ⟨236384, by rfl⟩ : syracuseStep 315179 = 472769) B472769
theorem B315209 : Blo 207808 315209 := bstep (se 2 (by rfl) ⟨118203, by rfl⟩ : syracuseStep 315209 = 236407) B236407
theorem B315323 : Blo 207808 315323 := bstep (se 1 (by rfl) ⟨236492, by rfl⟩ : syracuseStep 315323 = 472985) B472985
theorem B315383 : Blo 207808 315383 := bstep (se 1 (by rfl) ⟨236537, by rfl⟩ : syracuseStep 315383 = 473075) B473075
theorem B249863 : Blo 207808 249863 := bstep (se 1 (by rfl) ⟨187397, by rfl⟩ : syracuseStep 249863 = 374795) B374795
theorem B315407 : Blo 207808 315407 := bstep (se 1 (by rfl) ⟨236555, by rfl⟩ : syracuseStep 315407 = 473111) B473111
theorem B315449 : Blo 207808 315449 := bstep (se 2 (by rfl) ⟨118293, by rfl⟩ : syracuseStep 315449 = 236587) B236587
theorem B1200215 : Blo 207808 1200215 := bstep (se 1 (by rfl) ⟨900161, by rfl⟩ : syracuseStep 1200215 = 1800323) B1800323
theorem B708695 : Blo 207808 708695 := bstep (se 1 (by rfl) ⟨531521, by rfl⟩ : syracuseStep 708695 = 1063043) B1063043
theorem B315527 : Blo 207808 315527 := bstep (se 1 (by rfl) ⟨236645, by rfl⟩ : syracuseStep 315527 = 473291) B473291
theorem B315563 : Blo 207808 315563 := bstep (se 1 (by rfl) ⟨236672, by rfl⟩ : syracuseStep 315563 = 473345) B473345
theorem B7622857 : Blo 207808 7622857 := bstep (se 2 (by rfl) ⟨2858571, by rfl⟩ : syracuseStep 7622857 = 5717143) B5717143
theorem B315593 : Blo 207808 315593 := bstep (se 2 (by rfl) ⟨118347, by rfl⟩ : syracuseStep 315593 = 236695) B236695
theorem B315707 : Blo 207808 315707 := bstep (se 1 (by rfl) ⟨236780, by rfl⟩ : syracuseStep 315707 = 473561) B473561
theorem B315767 : Blo 207808 315767 := bstep (se 1 (by rfl) ⟨236825, by rfl⟩ : syracuseStep 315767 = 473651) B473651
theorem B315791 : Blo 207808 315791 := bstep (se 1 (by rfl) ⟨236843, by rfl⟩ : syracuseStep 315791 = 473687) B473687
theorem B315833 : Blo 207808 315833 := bstep (se 2 (by rfl) ⟨118437, by rfl⟩ : syracuseStep 315833 = 236875) B236875
theorem B315911 : Blo 207808 315911 := bstep (se 1 (by rfl) ⟨236933, by rfl⟩ : syracuseStep 315911 = 473867) B473867
theorem B315947 : Blo 207808 315947 := bstep (se 1 (by rfl) ⟨236960, by rfl⟩ : syracuseStep 315947 = 473921) B473921
theorem B709181 : Blo 207808 709181 := bstep (se 3 (by rfl) ⟨132971, by rfl⟩ : syracuseStep 709181 = 265943) B265943
theorem B905795 : Blo 207808 905795 := bstep (se 1 (by rfl) ⟨679346, by rfl⟩ : syracuseStep 905795 = 1358693) B1358693
theorem B315977 : Blo 207808 315977 := bstep (se 2 (by rfl) ⟨118491, by rfl⟩ : syracuseStep 315977 = 236983) B236983
theorem B316091 : Blo 207808 316091 := bstep (se 1 (by rfl) ⟨237068, by rfl⟩ : syracuseStep 316091 = 474137) B474137
theorem B316151 : Blo 207808 316151 := bstep (se 1 (by rfl) ⟨237113, by rfl⟩ : syracuseStep 316151 = 474227) B474227
theorem B316175 : Blo 207808 316175 := bstep (se 1 (by rfl) ⟨237131, by rfl⟩ : syracuseStep 316175 = 474263) B474263
theorem B480043 : Blo 207808 480043 := bstep (se 1 (by rfl) ⟨360032, by rfl⟩ : syracuseStep 480043 = 720065) B720065
theorem B316217 : Blo 207808 316217 := bstep (se 2 (by rfl) ⟨118581, by rfl⟩ : syracuseStep 316217 = 237163) B237163
theorem B316295 : Blo 207808 316295 := bstep (se 1 (by rfl) ⟨237221, by rfl⟩ : syracuseStep 316295 = 474443) B474443
theorem B316331 : Blo 207808 316331 := bstep (se 1 (by rfl) ⟨237248, by rfl⟩ : syracuseStep 316331 = 474497) B474497
theorem B1070009 : Blo 207808 1070009 := bstep (se 2 (by rfl) ⟨401253, by rfl⟩ : syracuseStep 1070009 = 802507) B802507
theorem B316361 : Blo 207808 316361 := bstep (se 2 (by rfl) ⟨118635, by rfl⟩ : syracuseStep 316361 = 237271) B237271
theorem B316475 : Blo 207808 316475 := bstep (se 1 (by rfl) ⟨237356, by rfl⟩ : syracuseStep 316475 = 474713) B474713
theorem B316535 : Blo 207808 316535 := bstep (se 1 (by rfl) ⟨237401, by rfl⟩ : syracuseStep 316535 = 474803) B474803
theorem B316559 : Blo 207808 316559 := bstep (se 1 (by rfl) ⟨237419, by rfl⟩ : syracuseStep 316559 = 474839) B474839
theorem B316601 : Blo 207808 316601 := bstep (se 2 (by rfl) ⟨118725, by rfl⟩ : syracuseStep 316601 = 237451) B237451
theorem B316679 : Blo 207808 316679 := bstep (se 1 (by rfl) ⟨237509, by rfl⟩ : syracuseStep 316679 = 475019) B475019
theorem B316715 : Blo 207808 316715 := bstep (se 1 (by rfl) ⟨237536, by rfl⟩ : syracuseStep 316715 = 475073) B475073
theorem B316745 : Blo 207808 316745 := bstep (se 2 (by rfl) ⟨118779, by rfl⟩ : syracuseStep 316745 = 237559) B237559
theorem B1201553 : Blo 207808 1201553 := bstep (se 2 (by rfl) ⟨450582, by rfl⟩ : syracuseStep 1201553 = 901165) B901165
theorem B4871609 : Blo 207808 4871609 := bstep (se 2 (by rfl) ⟨1826853, by rfl⟩ : syracuseStep 4871609 = 3653707) B3653707
theorem B316859 : Blo 207808 316859 := bstep (se 1 (by rfl) ⟨237644, by rfl⟩ : syracuseStep 316859 = 475289) B475289
theorem B316919 : Blo 207808 316919 := bstep (se 1 (by rfl) ⟨237689, by rfl⟩ : syracuseStep 316919 = 475379) B475379
theorem B316943 : Blo 207808 316943 := bstep (se 1 (by rfl) ⟨237707, by rfl⟩ : syracuseStep 316943 = 475415) B475415
theorem B316985 : Blo 207808 316985 := bstep (se 2 (by rfl) ⟨118869, by rfl⟩ : syracuseStep 316985 = 237739) B237739
theorem B317063 : Blo 207808 317063 := bstep (se 1 (by rfl) ⟨237797, by rfl⟩ : syracuseStep 317063 = 475595) B475595
theorem B317099 : Blo 207808 317099 := bstep (se 1 (by rfl) ⟨237824, by rfl⟩ : syracuseStep 317099 = 475649) B475649
theorem B317129 : Blo 207808 317129 := bstep (se 2 (by rfl) ⟨118923, by rfl⟩ : syracuseStep 317129 = 237847) B237847
theorem B317243 : Blo 207808 317243 := bstep (se 1 (by rfl) ⟨237932, by rfl⟩ : syracuseStep 317243 = 475865) B475865
theorem B317303 : Blo 207808 317303 := bstep (se 1 (by rfl) ⟨237977, by rfl⟩ : syracuseStep 317303 = 475955) B475955
theorem B317327 : Blo 207808 317327 := bstep (se 1 (by rfl) ⟨237995, by rfl⟩ : syracuseStep 317327 = 475991) B475991
theorem B710585 : Blo 207808 710585 := bstep (se 2 (by rfl) ⟨266469, by rfl⟩ : syracuseStep 710585 = 532939) B532939
theorem B317369 : Blo 207808 317369 := bstep (se 2 (by rfl) ⟨119013, by rfl⟩ : syracuseStep 317369 = 238027) B238027
theorem B546817 : Blo 207808 546817 := bstep (se 2 (by rfl) ⟨205056, by rfl⟩ : syracuseStep 546817 = 410113) B410113
theorem B317447 : Blo 207808 317447 := bstep (se 1 (by rfl) ⟨238085, by rfl⟩ : syracuseStep 317447 = 476171) B476171
theorem B317483 : Blo 207808 317483 := bstep (se 1 (by rfl) ⟨238112, by rfl⟩ : syracuseStep 317483 = 476225) B476225
theorem B317513 : Blo 207808 317513 := bstep (se 2 (by rfl) ⟨119067, by rfl⟩ : syracuseStep 317513 = 238135) B238135
theorem B317627 : Blo 207808 317627 := bstep (se 1 (by rfl) ⟨238220, by rfl⟩ : syracuseStep 317627 = 476441) B476441
theorem B1071305 : Blo 207808 1071305 := bstep (se 2 (by rfl) ⟨401739, by rfl⟩ : syracuseStep 1071305 = 803479) B803479
theorem B317687 : Blo 207808 317687 := bstep (se 1 (by rfl) ⟨238265, by rfl⟩ : syracuseStep 317687 = 476531) B476531
theorem B317711 : Blo 207808 317711 := bstep (se 1 (by rfl) ⟨238283, by rfl⟩ : syracuseStep 317711 = 476567) B476567
theorem B711179 : Blo 207808 711179 := bstep (se 1 (by rfl) ⟨533384, by rfl⟩ : syracuseStep 711179 = 1066769) B1066769
theorem B1006141 : Blo 207808 1006141 := bstep (se 3 (by rfl) ⟨188651, by rfl⟩ : syracuseStep 1006141 = 377303) B377303
theorem B1596023 : Blo 207808 1596023 := bstep (se 1 (by rfl) ⟨1197017, by rfl⟩ : syracuseStep 1596023 = 2394035) B2394035
theorem B711287 : Blo 207808 711287 := bstep (se 1 (by rfl) ⟨533465, by rfl⟩ : syracuseStep 711287 = 1066931) B1066931
theorem B383635 : Blo 207808 383635 := bstep (se 1 (by rfl) ⟨287726, by rfl⟩ : syracuseStep 383635 = 575453) B575453
theorem B350905 : Blo 207808 350905 := bstep (se 2 (by rfl) ⟨131589, by rfl⟩ : syracuseStep 350905 = 263179) B263179
theorem B1137617 : Blo 207808 1137617 := bstep (se 2 (by rfl) ⟨426606, by rfl⟩ : syracuseStep 1137617 = 853213) B853213
theorem B711881 : Blo 207808 711881 := bstep (se 2 (by rfl) ⟨266955, by rfl⟩ : syracuseStep 711881 = 533911) B533911
theorem B711937 : Blo 207808 711937 := bstep (se 2 (by rfl) ⟨266976, by rfl⟩ : syracuseStep 711937 = 533953) B533953
theorem B351607 : Blo 207808 351607 := bstep (se 1 (by rfl) ⟨263705, by rfl⟩ : syracuseStep 351607 = 527411) B527411
theorem B351803 : Blo 207808 351803 := bstep (se 1 (by rfl) ⟨263852, by rfl⟩ : syracuseStep 351803 = 527705) B527705
theorem B1596995 : Blo 207808 1596995 := bstep (se 1 (by rfl) ⟨1197746, by rfl⟩ : syracuseStep 1596995 = 2395493) B2395493
theorem B712583 : Blo 207808 712583 := bstep (se 1 (by rfl) ⟨534437, by rfl⟩ : syracuseStep 712583 = 1068875) B1068875
theorem B352201 : Blo 207808 352201 := bstep (se 2 (by rfl) ⟨132075, by rfl⟩ : syracuseStep 352201 = 264151) B264151
theorem B2547773 : Blo 207808 2547773 := bstep (se 3 (by rfl) ⟨477707, by rfl⟩ : syracuseStep 2547773 = 955415) B955415
theorem B254071 : Blo 207808 254071 := bstep (se 1 (by rfl) ⟨190553, by rfl⟩ : syracuseStep 254071 = 381107) B381107
theorem B1695917 : Blo 207808 1695917 := bstep (se 3 (by rfl) ⟨317984, by rfl⟩ : syracuseStep 1695917 = 635969) B635969
theorem B1007873 : Blo 207808 1007873 := bstep (se 2 (by rfl) ⟨377952, by rfl⟩ : syracuseStep 1007873 = 755905) B755905
theorem B712961 : Blo 207808 712961 := bstep (se 2 (by rfl) ⟨267360, by rfl⟩ : syracuseStep 712961 = 534721) B534721
theorem B2253089 : Blo 207808 2253089 := bstep (se 2 (by rfl) ⟨844908, by rfl⟩ : syracuseStep 2253089 = 1689817) B1689817
theorem B451001 : Blo 207808 451001 := bstep (se 2 (by rfl) ⟨169125, by rfl⟩ : syracuseStep 451001 = 338251) B338251
theorem B1008139 : Blo 207808 1008139 := bstep (se 1 (by rfl) ⟨756104, by rfl⟩ : syracuseStep 1008139 = 1512209) B1512209
theorem B1368695 : Blo 207808 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B352903 : Blo 207808 352903 := bstep (se 1 (by rfl) ⟨264677, by rfl⟩ : syracuseStep 352903 = 529355) B529355
theorem B1139609 : Blo 207808 1139609 := bstep (se 2 (by rfl) ⟨427353, by rfl⟩ : syracuseStep 1139609 = 854707) B854707
theorem B320503 : Blo 207808 320503 := bstep (se 1 (by rfl) ⟨240377, by rfl⟩ : syracuseStep 320503 = 480755) B480755
theorem B713771 : Blo 207808 713771 := bstep (se 1 (by rfl) ⟨535328, by rfl⟩ : syracuseStep 713771 = 1070657) B1070657
theorem B255163 : Blo 207808 255163 := bstep (se 1 (by rfl) ⟨191372, by rfl⟩ : syracuseStep 255163 = 382745) B382745
theorem B353551 : Blo 207808 353551 := bstep (se 1 (by rfl) ⟨265163, by rfl⟩ : syracuseStep 353551 = 530327) B530327
theorem B451855 : Blo 207808 451855 := bstep (se 1 (by rfl) ⟨338891, by rfl⟩ : syracuseStep 451855 = 677783) B677783
theorem B451883 : Blo 207808 451883 := bstep (se 1 (by rfl) ⟨338912, by rfl⟩ : syracuseStep 451883 = 677825) B677825
theorem B2385287 : Blo 207808 2385287 := bstep (se 1 (by rfl) ⟨1788965, by rfl⟩ : syracuseStep 2385287 = 3577931) B3577931
theorem B451975 : Blo 207808 451975 := bstep (se 1 (by rfl) ⟨338981, by rfl⟩ : syracuseStep 451975 = 677963) B677963
theorem B452155 : Blo 207808 452155 := bstep (se 1 (by rfl) ⟨339116, by rfl⟩ : syracuseStep 452155 = 678233) B678233
theorem B452231 : Blo 207808 452231 := bstep (se 1 (by rfl) ⟨339173, by rfl⟩ : syracuseStep 452231 = 678347) B678347
theorem B321167 : Blo 207808 321167 := bstep (se 1 (by rfl) ⟨240875, by rfl⟩ : syracuseStep 321167 = 481751) B481751
theorem B2549519 : Blo 207808 2549519 := bstep (se 1 (by rfl) ⟨1912139, by rfl⟩ : syracuseStep 2549519 = 3824279) B3824279
theorem B354091 : Blo 207808 354091 := bstep (se 1 (by rfl) ⟨265568, by rfl⟩ : syracuseStep 354091 = 531137) B531137
theorem B1009523 : Blo 207808 1009523 := bstep (se 1 (by rfl) ⟨757142, by rfl⟩ : syracuseStep 1009523 = 1514285) B1514285
theorem B354233 : Blo 207808 354233 := bstep (se 2 (by rfl) ⟨132837, by rfl⟩ : syracuseStep 354233 = 265675) B265675
theorem B6514805 : Blo 207808 6514805 := bstep (se 5 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 6514805 = 610763) B610763
theorem B321707 : Blo 207808 321707 := bstep (se 1 (by rfl) ⟨241280, by rfl⟩ : syracuseStep 321707 = 482561) B482561
theorem B1697993 : Blo 207808 1697993 := bstep (se 2 (by rfl) ⟨636747, by rfl⟩ : syracuseStep 1697993 = 1273495) B1273495
theorem B4549081 : Blo 207808 4549081 := bstep (se 2 (by rfl) ⟨1705905, by rfl⟩ : syracuseStep 4549081 = 3411811) B3411811
theorem B354935 : Blo 207808 354935 := bstep (se 1 (by rfl) ⟨266201, by rfl⟩ : syracuseStep 354935 = 532403) B532403
theorem B355387 : Blo 207808 355387 := bstep (se 1 (by rfl) ⟨266540, by rfl⟩ : syracuseStep 355387 = 533081) B533081
theorem B355529 : Blo 207808 355529 := bstep (se 2 (by rfl) ⟨133323, by rfl⟩ : syracuseStep 355529 = 266647) B266647
theorem B3599801 : Blo 207808 3599801 := bstep (se 2 (by rfl) ⟨1349925, by rfl⟩ : syracuseStep 3599801 = 2699851) B2699851
theorem B1142333 : Blo 207808 1142333 := bstep (se 3 (by rfl) ⟨214187, by rfl⟩ : syracuseStep 1142333 = 428375) B428375
theorem B58453589 : Blo 207808 58453589 := bstep (se 8 (by rfl) ⟨342501, by rfl⟩ : syracuseStep 58453589 = 685003) B685003
theorem B257783 : Blo 207808 257783 := bstep (se 1 (by rfl) ⟨193337, by rfl⟩ : syracuseStep 257783 = 386675) B386675
theorem B1601369 : Blo 207808 1601369 := bstep (se 2 (by rfl) ⟨600513, by rfl⟩ : syracuseStep 1601369 = 1201027) B1201027
theorem B356231 : Blo 207808 356231 := bstep (se 1 (by rfl) ⟨267173, by rfl⟩ : syracuseStep 356231 = 534347) B534347
theorem B14479307 : Blo 207808 14479307 := bstep (se 1 (by rfl) ⟨10859480, by rfl⟩ : syracuseStep 14479307 = 21718961) B21718961
theorem B258167 : Blo 207808 258167 := bstep (se 1 (by rfl) ⟨193625, by rfl⟩ : syracuseStep 258167 = 387251) B387251
theorem B225671 : Blo 207808 225671 := bstep (se 1 (by rfl) ⟨169253, by rfl⟩ : syracuseStep 225671 = 338507) B338507
theorem B356879 : Blo 207808 356879 := bstep (se 1 (by rfl) ⟨267659, by rfl⟩ : syracuseStep 356879 = 535319) B535319
theorem B1602341 : Blo 207808 1602341 := bstep (se 4 (by rfl) ⟨150219, by rfl⟩ : syracuseStep 1602341 = 300439) B300439
theorem B357419 : Blo 207808 357419 := bstep (se 1 (by rfl) ⟨268064, by rfl⟩ : syracuseStep 357419 = 536129) B536129
theorem B423031 : Blo 207808 423031 := bstep (se 1 (by rfl) ⟨317273, by rfl⟩ : syracuseStep 423031 = 634547) B634547
theorem B259471 : Blo 207808 259471 := bstep (se 1 (by rfl) ⟨194603, by rfl⟩ : syracuseStep 259471 = 389207) B389207
theorem B1209821 : Blo 207808 1209821 := bstep (se 3 (by rfl) ⟨226841, by rfl⟩ : syracuseStep 1209821 = 453683) B453683
theorem B751133 : Blo 207808 751133 := bstep (se 3 (by rfl) ⟨140837, by rfl⟩ : syracuseStep 751133 = 281675) B281675
theorem B849437 : Blo 207808 849437 := bstep (se 3 (by rfl) ⟨159269, by rfl⟩ : syracuseStep 849437 = 318539) B318539
theorem B13694993 : Blo 207808 13694993 := bstep (se 2 (by rfl) ⟨5135622, by rfl⟩ : syracuseStep 13694993 = 10271245) B10271245
theorem B688445 : Blo 207808 688445 := bstep (se 3 (by rfl) ⟨129083, by rfl⟩ : syracuseStep 688445 = 258167) B258167
theorem B1344185 : Blo 207808 1344185 := bstep (se 2 (by rfl) ⟨504069, by rfl⟩ : syracuseStep 1344185 = 1008139) B1008139
theorem B754375 : Blo 207808 754375 := bstep (se 1 (by rfl) ⟨565781, by rfl⟩ : syracuseStep 754375 = 1131563) B1131563
theorem B2688065 : Blo 207808 2688065 := bstep (se 2 (by rfl) ⟨1008024, by rfl⟩ : syracuseStep 2688065 = 2016049) B2016049
theorem B3048619 : Blo 207808 3048619 := bstep (se 1 (by rfl) ⟨2286464, by rfl⟩ : syracuseStep 3048619 = 4572929) B4572929
theorem B427337 : Blo 207808 427337 := bstep (se 2 (by rfl) ⟨160251, by rfl⟩ : syracuseStep 427337 = 320503) B320503
theorem B1017289 : Blo 207808 1017289 := bstep (se 2 (by rfl) ⟨381483, by rfl⟩ : syracuseStep 1017289 = 762967) B762967
theorem B394951 : Blo 207808 394951 := bstep (se 1 (by rfl) ⟨296213, by rfl⟩ : syracuseStep 394951 = 592427) B592427
theorem B1607687 : Blo 207808 1607687 := bstep (se 1 (by rfl) ⟨1205765, by rfl⟩ : syracuseStep 1607687 = 2411531) B2411531
theorem B395513 : Blo 207808 395513 := bstep (se 2 (by rfl) ⟨148317, by rfl⟩ : syracuseStep 395513 = 296635) B296635
theorem B395695 : Blo 207808 395695 := bstep (se 1 (by rfl) ⟨296771, by rfl⟩ : syracuseStep 395695 = 593543) B593543
theorem B1608173 : Blo 207808 1608173 := bstep (se 3 (by rfl) ⟨301532, by rfl⟩ : syracuseStep 1608173 = 603065) B603065
theorem B592393 : Blo 207808 592393 := bstep (se 2 (by rfl) ⟨222147, by rfl⟩ : syracuseStep 592393 = 444295) B444295
theorem B526945 : Blo 207808 526945 := bstep (se 2 (by rfl) ⟨197604, by rfl⟩ : syracuseStep 526945 = 395209) B395209
theorem B789203 : Blo 207808 789203 := bstep (se 1 (by rfl) ⟨591902, by rfl⟩ : syracuseStep 789203 = 1183805) B1183805
theorem B265295 : Blo 207808 265295 := bstep (se 1 (by rfl) ⟨198971, by rfl⟩ : syracuseStep 265295 = 397943) B397943
theorem B1510595 : Blo 207808 1510595 := bstep (se 1 (by rfl) ⟨1132946, by rfl⟩ : syracuseStep 1510595 = 2265893) B2265893
theorem B6065441 : Blo 207808 6065441 := bstep (se 2 (by rfl) ⟨2274540, by rfl⟩ : syracuseStep 6065441 = 4549081) B4549081
theorem B527897 : Blo 207808 527897 := bstep (se 2 (by rfl) ⟨197961, by rfl⟩ : syracuseStep 527897 = 395923) B395923
theorem B3247739 : Blo 207808 3247739 := bstep (se 1 (by rfl) ⟨2435804, by rfl⟩ : syracuseStep 3247739 = 4871609) B4871609
theorem B396971 : Blo 207808 396971 := bstep (se 1 (by rfl) ⟨297728, by rfl⟩ : syracuseStep 396971 = 595457) B595457
theorem B397199 : Blo 207808 397199 := bstep (se 1 (by rfl) ⟨297899, by rfl⟩ : syracuseStep 397199 = 595799) B595799
theorem B593851 : Blo 207808 593851 := bstep (se 1 (by rfl) ⟨445388, by rfl⟩ : syracuseStep 593851 = 890777) B890777
theorem B528403 : Blo 207808 528403 := bstep (se 1 (by rfl) ⟨396302, by rfl⟩ : syracuseStep 528403 = 792605) B792605
theorem B593999 : Blo 207808 593999 := bstep (se 1 (by rfl) ⟨445499, by rfl⟩ : syracuseStep 593999 = 890999) B890999
theorem B266591 : Blo 207808 266591 := bstep (se 1 (by rfl) ⟨199943, by rfl⟩ : syracuseStep 266591 = 399887) B399887
theorem B889325 : Blo 207808 889325 := bstep (se 3 (by rfl) ⟨166748, by rfl⟩ : syracuseStep 889325 = 333497) B333497
theorem B758297 : Blo 207808 758297 := bstep (se 2 (by rfl) ⟨284361, by rfl⟩ : syracuseStep 758297 = 568723) B568723
theorem B758411 : Blo 207808 758411 := bstep (se 1 (by rfl) ⟨568808, by rfl⟩ : syracuseStep 758411 = 1137617) B1137617
theorem B3248849 : Blo 207808 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B2692061 : Blo 207808 2692061 := bstep (se 3 (by rfl) ⟨504761, by rfl⟩ : syracuseStep 2692061 = 1009523) B1009523
theorem B2626561 : Blo 207808 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B234535 : Blo 207808 234535 := bstep (se 1 (by rfl) ⟨175901, by rfl⟩ : syracuseStep 234535 = 351803) B351803
theorem B3150899 : Blo 207808 3150899 := bstep (se 1 (by rfl) ⟨2363174, by rfl⟩ : syracuseStep 3150899 = 4726349) B4726349
theorem B595001 : Blo 207808 595001 := bstep (se 2 (by rfl) ⟨223125, by rfl⟩ : syracuseStep 595001 = 446251) B446251
theorem B529487 : Blo 207808 529487 := bstep (se 1 (by rfl) ⟨397115, by rfl⟩ : syracuseStep 529487 = 794231) B794231
theorem B791633 : Blo 207808 791633 := bstep (se 2 (by rfl) ⟨296862, by rfl⟩ : syracuseStep 791633 = 593725) B593725
theorem B398459 : Blo 207808 398459 := bstep (se 1 (by rfl) ⟨298844, by rfl⟩ : syracuseStep 398459 = 597689) B597689
theorem B595343 : Blo 207808 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B792089 : Blo 207808 792089 := bstep (se 2 (by rfl) ⟨297033, by rfl⟩ : syracuseStep 792089 = 594067) B594067
theorem B10163809 : Blo 207808 10163809 := bstep (se 2 (by rfl) ⟨3811428, by rfl⟩ : syracuseStep 10163809 = 7622857) B7622857
theorem B398945 : Blo 207808 398945 := bstep (se 2 (by rfl) ⟨149604, by rfl⟩ : syracuseStep 398945 = 299209) B299209
theorem B300667 : Blo 207808 300667 := bstep (se 1 (by rfl) ⟨225500, by rfl⟩ : syracuseStep 300667 = 451001) B451001
theorem B530135 : Blo 207808 530135 := bstep (se 1 (by rfl) ⟨397601, by rfl⟩ : syracuseStep 530135 = 795203) B795203
theorem B1054457 : Blo 207808 1054457 := bstep (se 2 (by rfl) ⟨395421, by rfl⟩ : syracuseStep 1054457 = 790843) B790843
theorem B399097 : Blo 207808 399097 := bstep (se 2 (by rfl) ⟨149661, by rfl⟩ : syracuseStep 399097 = 299323) B299323
theorem B759739 : Blo 207808 759739 := bstep (se 1 (by rfl) ⟨569804, by rfl⟩ : syracuseStep 759739 = 1139609) B1139609
theorem B530489 : Blo 207808 530489 := bstep (se 2 (by rfl) ⟨198933, by rfl⟩ : syracuseStep 530489 = 397867) B397867
theorem B301255 : Blo 207808 301255 := bstep (se 1 (by rfl) ⟨225941, by rfl⟩ : syracuseStep 301255 = 451883) B451883
theorem B1055105 : Blo 207808 1055105 := bstep (se 2 (by rfl) ⟨395664, by rfl⟩ : syracuseStep 1055105 = 791329) B791329
theorem B301487 : Blo 207808 301487 := bstep (se 1 (by rfl) ⟨226115, by rfl⟩ : syracuseStep 301487 = 452231) B452231
theorem B236155 : Blo 207808 236155 := bstep (se 1 (by rfl) ⟨177116, by rfl⟩ : syracuseStep 236155 = 354233) B354233
theorem B793273 : Blo 207808 793273 := bstep (se 2 (by rfl) ⟨297477, by rfl⟩ : syracuseStep 793273 = 594955) B594955
theorem B564041 : Blo 207808 564041 := bstep (se 2 (by rfl) ⟨211515, by rfl⟩ : syracuseStep 564041 = 423031) B423031
theorem B3218359 : Blo 207808 3218359 := bstep (se 1 (by rfl) ⟨2413769, by rfl⟩ : syracuseStep 3218359 = 4827539) B4827539
theorem B400403 : Blo 207808 400403 := bstep (se 1 (by rfl) ⟨300302, by rfl⟩ : syracuseStep 400403 = 600605) B600605
theorem B236623 : Blo 207808 236623 := bstep (se 1 (by rfl) ⟨177467, by rfl⟩ : syracuseStep 236623 = 354935) B354935
theorem B1055915 : Blo 207808 1055915 := bstep (se 1 (by rfl) ⟨791936, by rfl⟩ : syracuseStep 1055915 = 1583873) B1583873
theorem B400555 : Blo 207808 400555 := bstep (se 1 (by rfl) ⟨300416, by rfl⟩ : syracuseStep 400555 = 600833) B600833
theorem B400783 : Blo 207808 400783 := bstep (se 1 (by rfl) ⟨300587, by rfl⟩ : syracuseStep 400783 = 601175) B601175
theorem B237019 : Blo 207808 237019 := bstep (se 1 (by rfl) ⟨177764, by rfl⟩ : syracuseStep 237019 = 355529) B355529
theorem B400859 : Blo 207808 400859 := bstep (se 1 (by rfl) ⟨300644, by rfl⟩ : syracuseStep 400859 = 601289) B601289
theorem B335483 : Blo 207808 335483 := bstep (se 1 (by rfl) ⟨251612, by rfl⟩ : syracuseStep 335483 = 503225) B503225
theorem B2399867 : Blo 207808 2399867 := bstep (se 1 (by rfl) ⟨1799900, by rfl⟩ : syracuseStep 2399867 = 3599801) B3599801
theorem B1056401 : Blo 207808 1056401 := bstep (se 2 (by rfl) ⟨396150, by rfl⟩ : syracuseStep 1056401 = 792301) B792301
theorem B761555 : Blo 207808 761555 := bstep (se 1 (by rfl) ⟨571166, by rfl⟩ : syracuseStep 761555 = 1142333) B1142333
theorem B38969059 : Blo 207808 38969059 := bstep (se 1 (by rfl) ⟨29226794, by rfl⟩ : syracuseStep 38969059 = 58453589) B58453589
theorem B237487 : Blo 207808 237487 := bstep (se 1 (by rfl) ⟨178115, by rfl⟩ : syracuseStep 237487 = 356231) B356231
theorem B729089 : Blo 207808 729089 := bstep (se 2 (by rfl) ⟨273408, by rfl⟩ : syracuseStep 729089 = 546817) B546817
theorem B532727 : Blo 207808 532727 := bstep (se 1 (by rfl) ⟨399545, by rfl⟩ : syracuseStep 532727 = 799091) B799091
theorem B237919 : Blo 207808 237919 := bstep (se 1 (by rfl) ⟨178439, by rfl⟩ : syracuseStep 237919 = 356879) B356879
theorem B795005 : Blo 207808 795005 := bstep (se 3 (by rfl) ⟨149063, by rfl⟩ : syracuseStep 795005 = 298127) B298127
theorem B238279 : Blo 207808 238279 := bstep (se 1 (by rfl) ⟨178709, by rfl⟩ : syracuseStep 238279 = 357419) B357419
theorem B402167 : Blo 207808 402167 := bstep (se 1 (by rfl) ⟨301625, by rfl⟩ : syracuseStep 402167 = 603251) B603251
theorem B467819 : Blo 207808 467819 := bstep (se 1 (by rfl) ⟨350864, by rfl⟩ : syracuseStep 467819 = 701729) B701729
theorem B467873 : Blo 207808 467873 := bstep (se 2 (by rfl) ⟨175452, by rfl⟩ : syracuseStep 467873 = 350905) B350905
theorem B500755 : Blo 207808 500755 := bstep (se 1 (by rfl) ⟨375566, by rfl⟩ : syracuseStep 500755 = 751133) B751133
theorem B566291 : Blo 207808 566291 := bstep (se 1 (by rfl) ⟨424718, by rfl⟩ : syracuseStep 566291 = 849437) B849437
theorem B468215 : Blo 207808 468215 := bstep (se 1 (by rfl) ⟨351161, by rfl⟩ : syracuseStep 468215 = 702323) B702323
theorem B1189363 : Blo 207808 1189363 := bstep (se 1 (by rfl) ⟨892022, by rfl⟩ : syracuseStep 1189363 = 1784045) B1784045
theorem B534215 : Blo 207808 534215 := bstep (se 1 (by rfl) ⟨400661, by rfl⟩ : syracuseStep 534215 = 801323) B801323
theorem B468809 : Blo 207808 468809 := bstep (se 2 (by rfl) ⟨175803, by rfl⟩ : syracuseStep 468809 = 351607) B351607
theorem B1058669 : Blo 207808 1058669 := bstep (se 3 (by rfl) ⟨198500, by rfl⟩ : syracuseStep 1058669 = 397001) B397001
theorem B403465 : Blo 207808 403465 := bstep (se 2 (by rfl) ⟨151299, by rfl⟩ : syracuseStep 403465 = 302599) B302599
theorem B1058831 : Blo 207808 1058831 := bstep (se 1 (by rfl) ⟨794123, by rfl⟩ : syracuseStep 1058831 = 1588247) B1588247
theorem B797147 : Blo 207808 797147 := bstep (se 1 (by rfl) ⟨597860, by rfl⟩ : syracuseStep 797147 = 1195721) B1195721
theorem B469601 : Blo 207808 469601 := bstep (se 2 (by rfl) ⟨176100, by rfl⟩ : syracuseStep 469601 = 352201) B352201
theorem B338555 : Blo 207808 338555 := bstep (se 1 (by rfl) ⟨253916, by rfl⟩ : syracuseStep 338555 = 507833) B507833
theorem B666301 : Blo 207808 666301 := bstep (se 3 (by rfl) ⟨124931, by rfl⟩ : syracuseStep 666301 = 249863) B249863
theorem B600787 : Blo 207808 600787 := bstep (se 1 (by rfl) ⟨450590, by rfl⟩ : syracuseStep 600787 = 901181) B901181
theorem B338761 : Blo 207808 338761 := bstep (se 2 (by rfl) ⟨127035, by rfl⟩ : syracuseStep 338761 = 254071) B254071
theorem B535369 : Blo 207808 535369 := bstep (se 2 (by rfl) ⟨200763, by rfl⟩ : syracuseStep 535369 = 401527) B401527
theorem B4500299 : Blo 207808 4500299 := bstep (se 1 (by rfl) ⟨3375224, by rfl⟩ : syracuseStep 4500299 = 6750449) B6750449
theorem B1354643 : Blo 207808 1354643 := bstep (se 1 (by rfl) ⟨1015982, by rfl⟩ : syracuseStep 1354643 = 2031965) B2031965
theorem B469943 : Blo 207808 469943 := bstep (se 1 (by rfl) ⟨352457, by rfl⟩ : syracuseStep 469943 = 704915) B704915
theorem B601015 : Blo 207808 601015 := bstep (se 1 (by rfl) ⟨450761, by rfl⟩ : syracuseStep 601015 = 901523) B901523
theorem B207815 : Blo 207808 207815 := bstep (se 1 (by rfl) ⟨155861, by rfl⟩ : syracuseStep 207815 = 311723) B311723
theorem B207835 : Blo 207808 207835 := bstep (se 1 (by rfl) ⟨155876, by rfl⟩ : syracuseStep 207835 = 311753) B311753
theorem B207911 : Blo 207808 207911 := bstep (se 1 (by rfl) ⟨155933, by rfl⟩ : syracuseStep 207911 = 311867) B311867
theorem B207951 : Blo 207808 207951 := bstep (se 1 (by rfl) ⟨155963, by rfl⟩ : syracuseStep 207951 = 311927) B311927
theorem B207967 : Blo 207808 207967 := bstep (se 1 (by rfl) ⟨155975, by rfl⟩ : syracuseStep 207967 = 311951) B311951
theorem B207995 : Blo 207808 207995 := bstep (se 1 (by rfl) ⟨155996, by rfl⟩ : syracuseStep 207995 = 311993) B311993
theorem B208047 : Blo 207808 208047 := bstep (se 1 (by rfl) ⟨156035, by rfl⟩ : syracuseStep 208047 = 312071) B312071
theorem B2895041 : Blo 207808 2895041 := bstep (se 2 (by rfl) ⟨1085640, by rfl⟩ : syracuseStep 2895041 = 2171281) B2171281
theorem B208071 : Blo 207808 208071 := bstep (se 1 (by rfl) ⟨156053, by rfl⟩ : syracuseStep 208071 = 312107) B312107
theorem B208091 : Blo 207808 208091 := bstep (se 1 (by rfl) ⟨156068, by rfl⟩ : syracuseStep 208091 = 312137) B312137
theorem B208167 : Blo 207808 208167 := bstep (se 1 (by rfl) ⟨156125, by rfl⟩ : syracuseStep 208167 = 312251) B312251
theorem B208207 : Blo 207808 208207 := bstep (se 1 (by rfl) ⟨156155, by rfl⟩ : syracuseStep 208207 = 312311) B312311
theorem B666967 : Blo 207808 666967 := bstep (se 1 (by rfl) ⟨500225, by rfl⟩ : syracuseStep 666967 = 1000451) B1000451
theorem B2665817 : Blo 207808 2665817 := bstep (se 2 (by rfl) ⟨999681, by rfl⟩ : syracuseStep 2665817 = 1999363) B1999363
theorem B208223 : Blo 207808 208223 := bstep (se 1 (by rfl) ⟨156167, by rfl⟩ : syracuseStep 208223 = 312335) B312335
theorem B208251 : Blo 207808 208251 := bstep (se 1 (by rfl) ⟨156188, by rfl⟩ : syracuseStep 208251 = 312377) B312377
theorem B208303 : Blo 207808 208303 := bstep (se 1 (by rfl) ⟨156227, by rfl⟩ : syracuseStep 208303 = 312455) B312455
theorem B208327 : Blo 207808 208327 := bstep (se 1 (by rfl) ⟨156245, by rfl⟩ : syracuseStep 208327 = 312491) B312491
theorem B208347 : Blo 207808 208347 := bstep (se 1 (by rfl) ⟨156260, by rfl⟩ : syracuseStep 208347 = 312521) B312521
theorem B470537 : Blo 207808 470537 := bstep (se 2 (by rfl) ⟨176451, by rfl⟩ : syracuseStep 470537 = 352903) B352903
theorem B208423 : Blo 207808 208423 := bstep (se 1 (by rfl) ⟨156317, by rfl⟩ : syracuseStep 208423 = 312635) B312635
theorem B208463 : Blo 207808 208463 := bstep (se 1 (by rfl) ⟨156347, by rfl⟩ : syracuseStep 208463 = 312695) B312695
theorem B208479 : Blo 207808 208479 := bstep (se 1 (by rfl) ⟨156359, by rfl⟩ : syracuseStep 208479 = 312719) B312719
theorem B208507 : Blo 207808 208507 := bstep (se 1 (by rfl) ⟨156380, by rfl⟩ : syracuseStep 208507 = 312761) B312761
theorem B208559 : Blo 207808 208559 := bstep (se 1 (by rfl) ⟨156419, by rfl⟩ : syracuseStep 208559 = 312839) B312839
theorem B208583 : Blo 207808 208583 := bstep (se 1 (by rfl) ⟨156437, by rfl⟩ : syracuseStep 208583 = 312875) B312875
theorem B798407 : Blo 207808 798407 := bstep (se 1 (by rfl) ⟨598805, by rfl⟩ : syracuseStep 798407 = 1197611) B1197611
theorem B208603 : Blo 207808 208603 := bstep (se 1 (by rfl) ⟨156452, by rfl⟩ : syracuseStep 208603 = 312905) B312905
theorem B208679 : Blo 207808 208679 := bstep (se 1 (by rfl) ⟨156509, by rfl⟩ : syracuseStep 208679 = 313019) B313019
theorem B208719 : Blo 207808 208719 := bstep (se 1 (by rfl) ⟨156539, by rfl⟩ : syracuseStep 208719 = 313079) B313079
theorem B208735 : Blo 207808 208735 := bstep (se 1 (by rfl) ⟨156551, by rfl⟩ : syracuseStep 208735 = 313103) B313103
theorem B470879 : Blo 207808 470879 := bstep (se 1 (by rfl) ⟨353159, by rfl⟩ : syracuseStep 470879 = 706319) B706319
theorem B208763 : Blo 207808 208763 := bstep (se 1 (by rfl) ⟨156572, by rfl⟩ : syracuseStep 208763 = 313145) B313145
theorem B405391 : Blo 207808 405391 := bstep (se 1 (by rfl) ⟨304043, by rfl⟩ : syracuseStep 405391 = 608087) B608087
theorem B208815 : Blo 207808 208815 := bstep (se 1 (by rfl) ⟨156611, by rfl⟩ : syracuseStep 208815 = 313223) B313223
theorem B208839 : Blo 207808 208839 := bstep (se 1 (by rfl) ⟨156629, by rfl⟩ : syracuseStep 208839 = 313259) B313259
theorem B208859 : Blo 207808 208859 := bstep (se 1 (by rfl) ⟨156644, by rfl⟩ : syracuseStep 208859 = 313289) B313289
theorem B471059 : Blo 207808 471059 := bstep (se 1 (by rfl) ⟨353294, by rfl⟩ : syracuseStep 471059 = 706589) B706589
theorem B208935 : Blo 207808 208935 := bstep (se 1 (by rfl) ⟨156701, by rfl⟩ : syracuseStep 208935 = 313403) B313403
theorem B3321917 : Blo 207808 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B208975 : Blo 207808 208975 := bstep (se 1 (by rfl) ⟨156731, by rfl⟩ : syracuseStep 208975 = 313463) B313463
theorem B208991 : Blo 207808 208991 := bstep (se 1 (by rfl) ⟨156743, by rfl⟩ : syracuseStep 208991 = 313487) B313487
theorem B209019 : Blo 207808 209019 := bstep (se 1 (by rfl) ⟨156764, by rfl⟩ : syracuseStep 209019 = 313529) B313529
theorem B209071 : Blo 207808 209071 := bstep (se 1 (by rfl) ⟨156803, by rfl⟩ : syracuseStep 209071 = 313607) B313607
theorem B209095 : Blo 207808 209095 := bstep (se 1 (by rfl) ⟨156821, by rfl⟩ : syracuseStep 209095 = 313643) B313643
theorem B209115 : Blo 207808 209115 := bstep (se 1 (by rfl) ⟨156836, by rfl⟩ : syracuseStep 209115 = 313673) B313673
theorem B340217 : Blo 207808 340217 := bstep (se 2 (by rfl) ⟨127581, by rfl⟩ : syracuseStep 340217 = 255163) B255163
theorem B1519883 : Blo 207808 1519883 := bstep (se 1 (by rfl) ⟨1139912, by rfl⟩ : syracuseStep 1519883 = 2279825) B2279825
theorem B209191 : Blo 207808 209191 := bstep (se 1 (by rfl) ⟨156893, by rfl⟩ : syracuseStep 209191 = 313787) B313787
theorem B3649853 : Blo 207808 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B209231 : Blo 207808 209231 := bstep (se 1 (by rfl) ⟨156923, by rfl⟩ : syracuseStep 209231 = 313847) B313847
theorem B1192279 : Blo 207808 1192279 := bstep (se 1 (by rfl) ⟨894209, by rfl⟩ : syracuseStep 1192279 = 1788419) B1788419
theorem B209247 : Blo 207808 209247 := bstep (se 1 (by rfl) ⟨156935, by rfl⟩ : syracuseStep 209247 = 313871) B313871
theorem B471401 : Blo 207808 471401 := bstep (se 2 (by rfl) ⟨176775, by rfl⟩ : syracuseStep 471401 = 353551) B353551
theorem B602473 : Blo 207808 602473 := bstep (se 2 (by rfl) ⟨225927, by rfl⟩ : syracuseStep 602473 = 451855) B451855
theorem B209275 : Blo 207808 209275 := bstep (se 1 (by rfl) ⟨156956, by rfl⟩ : syracuseStep 209275 = 313913) B313913
theorem B799105 : Blo 207808 799105 := bstep (se 2 (by rfl) ⟨299664, by rfl⟩ : syracuseStep 799105 = 599329) B599329
theorem B209327 : Blo 207808 209327 := bstep (se 1 (by rfl) ⟨156995, by rfl⟩ : syracuseStep 209327 = 313991) B313991
theorem B209351 : Blo 207808 209351 := bstep (se 1 (by rfl) ⟨157013, by rfl⟩ : syracuseStep 209351 = 314027) B314027
theorem B209371 : Blo 207808 209371 := bstep (se 1 (by rfl) ⟨157028, by rfl⟩ : syracuseStep 209371 = 314057) B314057
theorem B602633 : Blo 207808 602633 := bstep (se 2 (by rfl) ⟨225987, by rfl⟩ : syracuseStep 602633 = 451975) B451975
theorem B209447 : Blo 207808 209447 := bstep (se 1 (by rfl) ⟨157085, by rfl⟩ : syracuseStep 209447 = 314171) B314171
theorem B209487 : Blo 207808 209487 := bstep (se 1 (by rfl) ⟨157115, by rfl⟩ : syracuseStep 209487 = 314231) B314231
theorem B209503 : Blo 207808 209503 := bstep (se 1 (by rfl) ⟨157127, by rfl⟩ : syracuseStep 209503 = 314255) B314255
theorem B209531 : Blo 207808 209531 := bstep (se 1 (by rfl) ⟨157148, by rfl⟩ : syracuseStep 209531 = 314297) B314297
theorem B733819 : Blo 207808 733819 := bstep (se 1 (by rfl) ⟨550364, by rfl⟩ : syracuseStep 733819 = 1100729) B1100729
theorem B602747 : Blo 207808 602747 := bstep (se 1 (by rfl) ⟨452060, by rfl⟩ : syracuseStep 602747 = 904121) B904121
theorem B799379 : Blo 207808 799379 := bstep (se 1 (by rfl) ⟨599534, by rfl⟩ : syracuseStep 799379 = 1199069) B1199069
theorem B209583 : Blo 207808 209583 := bstep (se 1 (by rfl) ⟨157187, by rfl⟩ : syracuseStep 209583 = 314375) B314375
theorem B209607 : Blo 207808 209607 := bstep (se 1 (by rfl) ⟨157205, by rfl⟩ : syracuseStep 209607 = 314411) B314411
theorem B3846865 : Blo 207808 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B1061585 : Blo 207808 1061585 := bstep (se 2 (by rfl) ⟨398094, by rfl⟩ : syracuseStep 1061585 = 796189) B796189
theorem B209627 : Blo 207808 209627 := bstep (se 1 (by rfl) ⟨157220, by rfl⟩ : syracuseStep 209627 = 314441) B314441
theorem B602873 : Blo 207808 602873 := bstep (se 2 (by rfl) ⟨226077, by rfl⟩ : syracuseStep 602873 = 452155) B452155
theorem B209703 : Blo 207808 209703 := bstep (se 1 (by rfl) ⟨157277, by rfl⟩ : syracuseStep 209703 = 314555) B314555
theorem B570185 : Blo 207808 570185 := bstep (se 2 (by rfl) ⟨213819, by rfl⟩ : syracuseStep 570185 = 427639) B427639
theorem B209743 : Blo 207808 209743 := bstep (se 1 (by rfl) ⟨157307, by rfl⟩ : syracuseStep 209743 = 314615) B314615
theorem B209759 : Blo 207808 209759 := bstep (se 1 (by rfl) ⟨157319, by rfl⟩ : syracuseStep 209759 = 314639) B314639
theorem B209787 : Blo 207808 209787 := bstep (se 1 (by rfl) ⟨157340, by rfl⟩ : syracuseStep 209787 = 314681) B314681
theorem B406415 : Blo 207808 406415 := bstep (se 1 (by rfl) ⟨304811, by rfl⟩ : syracuseStep 406415 = 609623) B609623
theorem B209839 : Blo 207808 209839 := bstep (se 1 (by rfl) ⟨157379, by rfl⟩ : syracuseStep 209839 = 314759) B314759
theorem B471995 : Blo 207808 471995 := bstep (se 1 (by rfl) ⟨353996, by rfl⟩ : syracuseStep 471995 = 707993) B707993
theorem B209863 : Blo 207808 209863 := bstep (se 1 (by rfl) ⟨157397, by rfl⟩ : syracuseStep 209863 = 314795) B314795
theorem B209883 : Blo 207808 209883 := bstep (se 1 (by rfl) ⟨157412, by rfl⟩ : syracuseStep 209883 = 314825) B314825
theorem B504839 : Blo 207808 504839 := bstep (se 1 (by rfl) ⟨378629, by rfl⟩ : syracuseStep 504839 = 757259) B757259
theorem B701459 : Blo 207808 701459 := bstep (se 1 (by rfl) ⟨526094, by rfl⟩ : syracuseStep 701459 = 1052189) B1052189
theorem B209959 : Blo 207808 209959 := bstep (se 1 (by rfl) ⟨157469, by rfl⟩ : syracuseStep 209959 = 314939) B314939
theorem B472121 : Blo 207808 472121 := bstep (se 2 (by rfl) ⟨177045, by rfl⟩ : syracuseStep 472121 = 354091) B354091
theorem B209999 : Blo 207808 209999 := bstep (se 1 (by rfl) ⟨157499, by rfl⟩ : syracuseStep 209999 = 314999) B314999
theorem B6075485 : Blo 207808 6075485 := bstep (se 3 (by rfl) ⟨1139153, by rfl⟩ : syracuseStep 6075485 = 2278307) B2278307
theorem B210015 : Blo 207808 210015 := bstep (se 1 (by rfl) ⟨157511, by rfl⟩ : syracuseStep 210015 = 315023) B315023
theorem B210043 : Blo 207808 210043 := bstep (se 1 (by rfl) ⟨157532, by rfl⟩ : syracuseStep 210043 = 315065) B315065
theorem B570539 : Blo 207808 570539 := bstep (se 1 (by rfl) ⟨427904, by rfl⟩ : syracuseStep 570539 = 855809) B855809
theorem B210095 : Blo 207808 210095 := bstep (se 1 (by rfl) ⟨157571, by rfl⟩ : syracuseStep 210095 = 315143) B315143
theorem B210119 : Blo 207808 210119 := bstep (se 1 (by rfl) ⟨157589, by rfl⟩ : syracuseStep 210119 = 315179) B315179
theorem B210139 : Blo 207808 210139 := bstep (se 1 (by rfl) ⟨157604, by rfl⟩ : syracuseStep 210139 = 315209) B315209
theorem B210215 : Blo 207808 210215 := bstep (se 1 (by rfl) ⟨157661, by rfl⟩ : syracuseStep 210215 = 315323) B315323
theorem B210255 : Blo 207808 210255 := bstep (se 1 (by rfl) ⟨157691, by rfl⟩ : syracuseStep 210255 = 315383) B315383
theorem B701783 : Blo 207808 701783 := bstep (se 1 (by rfl) ⟨526337, by rfl⟩ : syracuseStep 701783 = 1052675) B1052675
theorem B210271 : Blo 207808 210271 := bstep (se 1 (by rfl) ⟨157703, by rfl⟩ : syracuseStep 210271 = 315407) B315407
theorem B210299 : Blo 207808 210299 := bstep (se 1 (by rfl) ⟨157724, by rfl⟩ : syracuseStep 210299 = 315449) B315449
theorem B472463 : Blo 207808 472463 := bstep (se 1 (by rfl) ⟨354347, by rfl⟩ : syracuseStep 472463 = 708695) B708695
theorem B898447 : Blo 207808 898447 := bstep (se 1 (by rfl) ⟨673835, by rfl⟩ : syracuseStep 898447 = 1347671) B1347671
theorem B6403475 : Blo 207808 6403475 := bstep (se 1 (by rfl) ⟨4802606, by rfl⟩ : syracuseStep 6403475 = 9605213) B9605213
theorem B210351 : Blo 207808 210351 := bstep (se 1 (by rfl) ⟨157763, by rfl⟩ : syracuseStep 210351 = 315527) B315527
theorem B210375 : Blo 207808 210375 := bstep (se 1 (by rfl) ⟨157781, by rfl⟩ : syracuseStep 210375 = 315563) B315563
theorem B210395 : Blo 207808 210395 := bstep (se 1 (by rfl) ⟨157796, by rfl⟩ : syracuseStep 210395 = 315593) B315593
theorem B210471 : Blo 207808 210471 := bstep (se 1 (by rfl) ⟨157853, by rfl⟩ : syracuseStep 210471 = 315707) B315707
theorem B210511 : Blo 207808 210511 := bstep (se 1 (by rfl) ⟨157883, by rfl⟩ : syracuseStep 210511 = 315767) B315767
theorem B210527 : Blo 207808 210527 := bstep (se 1 (by rfl) ⟨157895, by rfl⟩ : syracuseStep 210527 = 315791) B315791
theorem B210555 : Blo 207808 210555 := bstep (se 1 (by rfl) ⟨157916, by rfl⟩ : syracuseStep 210555 = 315833) B315833
theorem B964243 : Blo 207808 964243 := bstep (se 1 (by rfl) ⟨723182, by rfl⟩ : syracuseStep 964243 = 1446365) B1446365
theorem B210607 : Blo 207808 210607 := bstep (se 1 (by rfl) ⟨157955, by rfl⟩ : syracuseStep 210607 = 315911) B315911
theorem B210631 : Blo 207808 210631 := bstep (se 1 (by rfl) ⟨157973, by rfl⟩ : syracuseStep 210631 = 315947) B315947
theorem B472787 : Blo 207808 472787 := bstep (se 1 (by rfl) ⟨354590, by rfl⟩ : syracuseStep 472787 = 709181) B709181
theorem B603863 : Blo 207808 603863 := bstep (se 1 (by rfl) ⟨452897, by rfl⟩ : syracuseStep 603863 = 905795) B905795
theorem B210651 : Blo 207808 210651 := bstep (se 1 (by rfl) ⟨157988, by rfl⟩ : syracuseStep 210651 = 315977) B315977
theorem B210727 : Blo 207808 210727 := bstep (se 1 (by rfl) ⟨158045, by rfl⟩ : syracuseStep 210727 = 316091) B316091
theorem B210767 : Blo 207808 210767 := bstep (se 1 (by rfl) ⟨158075, by rfl⟩ : syracuseStep 210767 = 316151) B316151
theorem B210783 : Blo 207808 210783 := bstep (se 1 (by rfl) ⟨158087, by rfl⟩ : syracuseStep 210783 = 316175) B316175
theorem B210811 : Blo 207808 210811 := bstep (se 1 (by rfl) ⟨158108, by rfl⟩ : syracuseStep 210811 = 316217) B316217
theorem B210863 : Blo 207808 210863 := bstep (se 1 (by rfl) ⟨158147, by rfl⟩ : syracuseStep 210863 = 316295) B316295
theorem B210887 : Blo 207808 210887 := bstep (se 1 (by rfl) ⟨158165, by rfl⟩ : syracuseStep 210887 = 316331) B316331
theorem B210907 : Blo 207808 210907 := bstep (se 1 (by rfl) ⟨158180, by rfl⟩ : syracuseStep 210907 = 316361) B316361
theorem B210983 : Blo 207808 210983 := bstep (se 1 (by rfl) ⟨158237, by rfl⟩ : syracuseStep 210983 = 316475) B316475
theorem B211023 : Blo 207808 211023 := bstep (se 1 (by rfl) ⟨158267, by rfl⟩ : syracuseStep 211023 = 316535) B316535
theorem B211039 : Blo 207808 211039 := bstep (se 1 (by rfl) ⟨158279, by rfl⟩ : syracuseStep 211039 = 316559) B316559
theorem B2046053 : Blo 207808 2046053 := bstep (se 4 (by rfl) ⟨191817, by rfl⟩ : syracuseStep 2046053 = 383635) B383635
theorem B211067 : Blo 207808 211067 := bstep (se 1 (by rfl) ⟨158300, by rfl⟩ : syracuseStep 211067 = 316601) B316601
theorem B211119 : Blo 207808 211119 := bstep (se 1 (by rfl) ⟨158339, by rfl⟩ : syracuseStep 211119 = 316679) B316679
theorem B211143 : Blo 207808 211143 := bstep (se 1 (by rfl) ⟨158357, by rfl⟩ : syracuseStep 211143 = 316715) B316715
theorem B211163 : Blo 207808 211163 := bstep (se 1 (by rfl) ⟨158372, by rfl⟩ : syracuseStep 211163 = 316745) B316745
theorem B801035 : Blo 207808 801035 := bstep (se 1 (by rfl) ⟨600776, by rfl⟩ : syracuseStep 801035 = 1201553) B1201553
theorem B211239 : Blo 207808 211239 := bstep (se 1 (by rfl) ⟨158429, by rfl⟩ : syracuseStep 211239 = 316859) B316859
theorem B211279 : Blo 207808 211279 := bstep (se 1 (by rfl) ⟨158459, by rfl⟩ : syracuseStep 211279 = 316919) B316919
theorem B211295 : Blo 207808 211295 := bstep (se 1 (by rfl) ⟨158471, by rfl⟩ : syracuseStep 211295 = 316943) B316943
theorem B211323 : Blo 207808 211323 := bstep (se 1 (by rfl) ⟨158492, by rfl⟩ : syracuseStep 211323 = 316985) B316985
theorem B702863 : Blo 207808 702863 := bstep (se 1 (by rfl) ⟨527147, by rfl⟩ : syracuseStep 702863 = 1054295) B1054295
theorem B211375 : Blo 207808 211375 := bstep (se 1 (by rfl) ⟨158531, by rfl⟩ : syracuseStep 211375 = 317063) B317063
theorem B211399 : Blo 207808 211399 := bstep (se 1 (by rfl) ⟨158549, by rfl⟩ : syracuseStep 211399 = 317099) B317099
theorem B211419 : Blo 207808 211419 := bstep (se 1 (by rfl) ⟨158564, by rfl⟩ : syracuseStep 211419 = 317129) B317129
theorem B211495 : Blo 207808 211495 := bstep (se 1 (by rfl) ⟨158621, by rfl⟩ : syracuseStep 211495 = 317243) B317243
theorem B3226189 : Blo 207808 3226189 := bstep (se 3 (by rfl) ⟨604910, by rfl⟩ : syracuseStep 3226189 = 1209821) B1209821
theorem B211535 : Blo 207808 211535 := bstep (se 1 (by rfl) ⟨158651, by rfl⟩ : syracuseStep 211535 = 317303) B317303
theorem B211551 : Blo 207808 211551 := bstep (se 1 (by rfl) ⟨158663, by rfl⟩ : syracuseStep 211551 = 317327) B317327
theorem B473723 : Blo 207808 473723 := bstep (se 1 (by rfl) ⟨355292, by rfl⟩ : syracuseStep 473723 = 710585) B710585
theorem B211579 : Blo 207808 211579 := bstep (se 1 (by rfl) ⟨158684, by rfl⟩ : syracuseStep 211579 = 317369) B317369
theorem B211631 : Blo 207808 211631 := bstep (se 1 (by rfl) ⟨158723, by rfl⟩ : syracuseStep 211631 = 317447) B317447
theorem B211655 : Blo 207808 211655 := bstep (se 1 (by rfl) ⟨158741, by rfl⟩ : syracuseStep 211655 = 317483) B317483
theorem B703187 : Blo 207808 703187 := bstep (se 1 (by rfl) ⟨527390, by rfl⟩ : syracuseStep 703187 = 1054781) B1054781
theorem B211675 : Blo 207808 211675 := bstep (se 1 (by rfl) ⟨158756, by rfl⟩ : syracuseStep 211675 = 317513) B317513
theorem B2407157 : Blo 207808 2407157 := bstep (se 5 (by rfl) ⟨112835, by rfl⟩ : syracuseStep 2407157 = 225671) B225671
theorem B473849 : Blo 207808 473849 := bstep (se 2 (by rfl) ⟨177693, by rfl⟩ : syracuseStep 473849 = 355387) B355387
theorem B211751 : Blo 207808 211751 := bstep (se 1 (by rfl) ⟨158813, by rfl⟩ : syracuseStep 211751 = 317627) B317627
theorem B211791 : Blo 207808 211791 := bstep (se 1 (by rfl) ⟨158843, by rfl⟩ : syracuseStep 211791 = 317687) B317687
theorem B211807 : Blo 207808 211807 := bstep (se 1 (by rfl) ⟨158855, by rfl⟩ : syracuseStep 211807 = 317711) B317711
theorem B1686419 : Blo 207808 1686419 := bstep (se 1 (by rfl) ⟨1264814, by rfl⟩ : syracuseStep 1686419 = 2529629) B2529629
theorem B474119 : Blo 207808 474119 := bstep (se 1 (by rfl) ⟨355589, by rfl⟩ : syracuseStep 474119 = 711179) B711179
theorem B1064015 : Blo 207808 1064015 := bstep (se 1 (by rfl) ⟨798011, by rfl⟩ : syracuseStep 1064015 = 1596023) B1596023
theorem B474191 : Blo 207808 474191 := bstep (se 1 (by rfl) ⟨355643, by rfl⟩ : syracuseStep 474191 = 711287) B711287
theorem B474587 : Blo 207808 474587 := bstep (se 1 (by rfl) ⟨355940, by rfl⟩ : syracuseStep 474587 = 711881) B711881
theorem B802493 : Blo 207808 802493 := bstep (se 3 (by rfl) ⟨150467, by rfl⟩ : syracuseStep 802493 = 300935) B300935
theorem B1064663 : Blo 207808 1064663 := bstep (se 1 (by rfl) ⟨798497, by rfl⟩ : syracuseStep 1064663 = 1596995) B1596995
theorem B704375 : Blo 207808 704375 := bstep (se 1 (by rfl) ⟨528281, by rfl⟩ : syracuseStep 704375 = 1056563) B1056563
theorem B475055 : Blo 207808 475055 := bstep (se 1 (by rfl) ⟨356291, by rfl⟩ : syracuseStep 475055 = 712583) B712583
theorem B704591 : Blo 207808 704591 := bstep (se 1 (by rfl) ⟨528443, by rfl⟩ : syracuseStep 704591 = 1056887) B1056887
theorem B1130611 : Blo 207808 1130611 := bstep (se 1 (by rfl) ⟨847958, by rfl⟩ : syracuseStep 1130611 = 1695917) B1695917
theorem B1818787 : Blo 207808 1818787 := bstep (se 1 (by rfl) ⟨1364090, by rfl⟩ : syracuseStep 1818787 = 2728181) B2728181
theorem B671915 : Blo 207808 671915 := bstep (se 1 (by rfl) ⟨503936, by rfl⟩ : syracuseStep 671915 = 1007873) B1007873
theorem B475307 : Blo 207808 475307 := bstep (se 1 (by rfl) ⟨356480, by rfl⟩ : syracuseStep 475307 = 712961) B712961
theorem B311735 : Blo 207808 311735 := bstep (se 1 (by rfl) ⟨233801, by rfl⟩ : syracuseStep 311735 = 467603) B467603
theorem B704969 : Blo 207808 704969 := bstep (se 2 (by rfl) ⟨264363, by rfl⟩ : syracuseStep 704969 = 528727) B528727
theorem B311771 : Blo 207808 311771 := bstep (se 1 (by rfl) ⟨233828, by rfl⟩ : syracuseStep 311771 = 467657) B467657
theorem B475847 : Blo 207808 475847 := bstep (se 1 (by rfl) ⟨356885, by rfl⟩ : syracuseStep 475847 = 713771) B713771
theorem B705239 : Blo 207808 705239 := bstep (se 1 (by rfl) ⟨528929, by rfl⟩ : syracuseStep 705239 = 1057859) B1057859
theorem B312239 : Blo 207808 312239 := bstep (se 1 (by rfl) ⟨234179, by rfl⟩ : syracuseStep 312239 = 468359) B468359
theorem B705455 : Blo 207808 705455 := bstep (se 1 (by rfl) ⟨529091, by rfl⟩ : syracuseStep 705455 = 1058183) B1058183
theorem B1590191 : Blo 207808 1590191 := bstep (se 1 (by rfl) ⟨1192643, by rfl⟩ : syracuseStep 1590191 = 2385287) B2385287
theorem B312329 : Blo 207808 312329 := bstep (se 2 (by rfl) ⟨117123, by rfl⟩ : syracuseStep 312329 = 234247) B234247
theorem B312359 : Blo 207808 312359 := bstep (se 1 (by rfl) ⟨234269, by rfl⟩ : syracuseStep 312359 = 468539) B468539
theorem B640057 : Blo 207808 640057 := bstep (se 2 (by rfl) ⟨240021, by rfl⟩ : syracuseStep 640057 = 480043) B480043
theorem B214111 : Blo 207808 214111 := bstep (se 1 (by rfl) ⟨160583, by rfl⟩ : syracuseStep 214111 = 321167) B321167
theorem B312443 : Blo 207808 312443 := bstep (se 1 (by rfl) ⟨234332, by rfl⟩ : syracuseStep 312443 = 468665) B468665
theorem B312569 : Blo 207808 312569 := bstep (se 2 (by rfl) ⟨117213, by rfl⟩ : syracuseStep 312569 = 234427) B234427
theorem B312671 : Blo 207808 312671 := bstep (se 1 (by rfl) ⟨234503, by rfl⟩ : syracuseStep 312671 = 469007) B469007
theorem B312683 : Blo 207808 312683 := bstep (se 1 (by rfl) ⟨234512, by rfl⟩ : syracuseStep 312683 = 469025) B469025
theorem B542081 : Blo 207808 542081 := bstep (se 2 (by rfl) ⟨203280, by rfl⟩ : syracuseStep 542081 = 406561) B406561
theorem B4343203 : Blo 207808 4343203 := bstep (se 1 (by rfl) ⟨3257402, by rfl⟩ : syracuseStep 4343203 = 6514805) B6514805
theorem B214471 : Blo 207808 214471 := bstep (se 1 (by rfl) ⟨160853, by rfl⟩ : syracuseStep 214471 = 321707) B321707
theorem B1131995 : Blo 207808 1131995 := bstep (se 1 (by rfl) ⟨848996, by rfl⟩ : syracuseStep 1131995 = 1697993) B1697993
theorem B312911 : Blo 207808 312911 := bstep (se 1 (by rfl) ⟨234683, by rfl⟩ : syracuseStep 312911 = 469367) B469367
theorem B313031 : Blo 207808 313031 := bstep (se 1 (by rfl) ⟨234773, by rfl⟩ : syracuseStep 313031 = 469547) B469547
theorem B313193 : Blo 207808 313193 := bstep (se 2 (by rfl) ⟨117447, by rfl⟩ : syracuseStep 313193 = 234895) B234895
theorem B345961 : Blo 207808 345961 := bstep (se 2 (by rfl) ⟨129735, by rfl⟩ : syracuseStep 345961 = 259471) B259471
theorem B313271 : Blo 207808 313271 := bstep (se 1 (by rfl) ⟨234953, by rfl⟩ : syracuseStep 313271 = 469907) B469907
theorem B313307 : Blo 207808 313307 := bstep (se 1 (by rfl) ⟨234980, by rfl⟩ : syracuseStep 313307 = 469961) B469961
theorem B313775 : Blo 207808 313775 := bstep (se 1 (by rfl) ⟨235331, by rfl⟩ : syracuseStep 313775 = 470663) B470663
theorem B313865 : Blo 207808 313865 := bstep (se 2 (by rfl) ⟨117699, by rfl⟩ : syracuseStep 313865 = 235399) B235399
theorem B313895 : Blo 207808 313895 := bstep (se 1 (by rfl) ⟨235421, by rfl⟩ : syracuseStep 313895 = 470843) B470843
theorem B1067579 : Blo 207808 1067579 := bstep (se 1 (by rfl) ⟨800684, by rfl⟩ : syracuseStep 1067579 = 1601369) B1601369
theorem B313979 : Blo 207808 313979 := bstep (se 1 (by rfl) ⟨235484, by rfl⟩ : syracuseStep 313979 = 470969) B470969
theorem B9652871 : Blo 207808 9652871 := bstep (se 1 (by rfl) ⟨7239653, by rfl⟩ : syracuseStep 9652871 = 14479307) B14479307
theorem B314105 : Blo 207808 314105 := bstep (se 2 (by rfl) ⟨117789, by rfl⟩ : syracuseStep 314105 = 235579) B235579
theorem B314207 : Blo 207808 314207 := bstep (se 1 (by rfl) ⟨235655, by rfl⟩ : syracuseStep 314207 = 471311) B471311
theorem B314219 : Blo 207808 314219 := bstep (se 1 (by rfl) ⟨235664, by rfl⟩ : syracuseStep 314219 = 471329) B471329
theorem B314447 : Blo 207808 314447 := bstep (se 1 (by rfl) ⟨235835, by rfl⟩ : syracuseStep 314447 = 471671) B471671
theorem B1068227 : Blo 207808 1068227 := bstep (se 1 (by rfl) ⟨801170, by rfl⟩ : syracuseStep 1068227 = 1602341) B1602341
theorem B314567 : Blo 207808 314567 := bstep (se 1 (by rfl) ⟨235925, by rfl⟩ : syracuseStep 314567 = 471851) B471851
theorem B707831 : Blo 207808 707831 := bstep (se 1 (by rfl) ⟨530873, by rfl⟩ : syracuseStep 707831 = 1061747) B1061747
theorem B314729 : Blo 207808 314729 := bstep (se 2 (by rfl) ⟨118023, by rfl⟩ : syracuseStep 314729 = 236047) B236047
theorem B314807 : Blo 207808 314807 := bstep (se 1 (by rfl) ⟨236105, by rfl⟩ : syracuseStep 314807 = 472211) B472211
theorem B314843 : Blo 207808 314843 := bstep (se 1 (by rfl) ⟨236132, by rfl⟩ : syracuseStep 314843 = 472265) B472265
theorem B806381 : Blo 207808 806381 := bstep (se 3 (by rfl) ⟨151196, by rfl⟩ : syracuseStep 806381 = 302393) B302393
theorem B445961 : Blo 207808 445961 := bstep (se 2 (by rfl) ⟨167235, by rfl⟩ : syracuseStep 445961 = 334471) B334471
theorem B708155 : Blo 207808 708155 := bstep (se 1 (by rfl) ⟨531116, by rfl⟩ : syracuseStep 708155 = 1062233) B1062233
theorem B708425 : Blo 207808 708425 := bstep (se 2 (by rfl) ⟨265659, by rfl⟩ : syracuseStep 708425 = 531319) B531319
theorem B446303 : Blo 207808 446303 := bstep (se 1 (by rfl) ⟨334727, by rfl⟩ : syracuseStep 446303 = 669455) B669455
theorem B1003373 : Blo 207808 1003373 := bstep (se 3 (by rfl) ⟨188132, by rfl⟩ : syracuseStep 1003373 = 376265) B376265
theorem B315311 : Blo 207808 315311 := bstep (se 1 (by rfl) ⟨236483, by rfl⟩ : syracuseStep 315311 = 472967) B472967
theorem B315401 : Blo 207808 315401 := bstep (se 2 (by rfl) ⟨118275, by rfl⟩ : syracuseStep 315401 = 236551) B236551
theorem B9129995 : Blo 207808 9129995 := bstep (se 1 (by rfl) ⟨6847496, by rfl⟩ : syracuseStep 9129995 = 13694993) B13694993
theorem B315431 : Blo 207808 315431 := bstep (se 1 (by rfl) ⟨236573, by rfl⟩ : syracuseStep 315431 = 473147) B473147
theorem B249979 : Blo 207808 249979 := bstep (se 1 (by rfl) ⟨187484, by rfl⟩ : syracuseStep 249979 = 374969) B374969
theorem B315515 : Blo 207808 315515 := bstep (se 1 (by rfl) ⟨236636, by rfl⟩ : syracuseStep 315515 = 473273) B473273
theorem B315641 : Blo 207808 315641 := bstep (se 2 (by rfl) ⟨118365, by rfl⟩ : syracuseStep 315641 = 236731) B236731
theorem B315743 : Blo 207808 315743 := bstep (se 1 (by rfl) ⟨236807, by rfl⟩ : syracuseStep 315743 = 473615) B473615
theorem B315755 : Blo 207808 315755 := bstep (se 1 (by rfl) ⟨236816, by rfl⟩ : syracuseStep 315755 = 473633) B473633
theorem B315983 : Blo 207808 315983 := bstep (se 1 (by rfl) ⟨236987, by rfl⟩ : syracuseStep 315983 = 473975) B473975
theorem B5100205 : Blo 207808 5100205 := bstep (se 3 (by rfl) ⟨956288, by rfl⟩ : syracuseStep 5100205 = 1912577) B1912577
theorem B316103 : Blo 207808 316103 := bstep (se 1 (by rfl) ⟨237077, by rfl⟩ : syracuseStep 316103 = 474155) B474155
theorem B316265 : Blo 207808 316265 := bstep (se 2 (by rfl) ⟨118599, by rfl⟩ : syracuseStep 316265 = 237199) B237199
theorem B709559 : Blo 207808 709559 := bstep (se 1 (by rfl) ⟨532169, by rfl⟩ : syracuseStep 709559 = 1064339) B1064339
theorem B316343 : Blo 207808 316343 := bstep (se 1 (by rfl) ⟨237257, by rfl⟩ : syracuseStep 316343 = 474515) B474515
theorem B316379 : Blo 207808 316379 := bstep (se 1 (by rfl) ⟨237284, by rfl⟩ : syracuseStep 316379 = 474569) B474569
theorem B316495 : Blo 207808 316495 := bstep (se 1 (by rfl) ⟨237371, by rfl⟩ : syracuseStep 316495 = 474743) B474743
theorem B1791395 : Blo 207808 1791395 := bstep (se 1 (by rfl) ⟨1343546, by rfl⟩ : syracuseStep 1791395 = 2687093) B2687093
theorem B316847 : Blo 207808 316847 := bstep (se 1 (by rfl) ⟨237635, by rfl⟩ : syracuseStep 316847 = 475271) B475271
theorem B710153 : Blo 207808 710153 := bstep (se 2 (by rfl) ⟨266307, by rfl⟩ : syracuseStep 710153 = 532615) B532615
theorem B316937 : Blo 207808 316937 := bstep (se 2 (by rfl) ⟨118851, by rfl⟩ : syracuseStep 316937 = 237703) B237703
theorem B316967 : Blo 207808 316967 := bstep (se 1 (by rfl) ⟨237725, by rfl⟩ : syracuseStep 316967 = 475451) B475451
theorem B3200573 : Blo 207808 3200573 := bstep (se 3 (by rfl) ⟨600107, by rfl⟩ : syracuseStep 3200573 = 1200215) B1200215
theorem B12342881 : Blo 207808 12342881 := bstep (se 2 (by rfl) ⟨4628580, by rfl⟩ : syracuseStep 12342881 = 9257161) B9257161
theorem B317051 : Blo 207808 317051 := bstep (se 1 (by rfl) ⟨237788, by rfl⟩ : syracuseStep 317051 = 475577) B475577
theorem B317177 : Blo 207808 317177 := bstep (se 2 (by rfl) ⟨118941, by rfl⟩ : syracuseStep 317177 = 237883) B237883
theorem B317279 : Blo 207808 317279 := bstep (se 1 (by rfl) ⟨237959, by rfl⟩ : syracuseStep 317279 = 475919) B475919
theorem B743275 : Blo 207808 743275 := bstep (se 1 (by rfl) ⟨557456, by rfl⟩ : syracuseStep 743275 = 1114913) B1114913
theorem B317291 : Blo 207808 317291 := bstep (se 1 (by rfl) ⟨237968, by rfl⟩ : syracuseStep 317291 = 475937) B475937
theorem B317519 : Blo 207808 317519 := bstep (se 1 (by rfl) ⟨238139, by rfl⟩ : syracuseStep 317519 = 476279) B476279
theorem B317639 : Blo 207808 317639 := bstep (se 1 (by rfl) ⟨238229, by rfl⟩ : syracuseStep 317639 = 476459) B476459
theorem B711017 : Blo 207808 711017 := bstep (se 2 (by rfl) ⟨266631, by rfl⟩ : syracuseStep 711017 = 533263) B533263
theorem B350777 : Blo 207808 350777 := bstep (se 2 (by rfl) ⟨131541, by rfl⟩ : syracuseStep 350777 = 263083) B263083
theorem B1137361 : Blo 207808 1137361 := bstep (se 2 (by rfl) ⟨426510, by rfl⟩ : syracuseStep 1137361 = 853021) B853021
theorem B1334191 : Blo 207808 1334191 := bstep (se 1 (by rfl) ⟨1000643, by rfl⟩ : syracuseStep 1334191 = 2001287) B2001287
theorem B711611 : Blo 207808 711611 := bstep (se 1 (by rfl) ⟨533708, by rfl⟩ : syracuseStep 711611 = 1067417) B1067417
theorem B351479 : Blo 207808 351479 := bstep (se 1 (by rfl) ⟨263609, by rfl⟩ : syracuseStep 351479 = 527219) B527219
theorem B351823 : Blo 207808 351823 := bstep (se 1 (by rfl) ⟨263867, by rfl⟩ : syracuseStep 351823 = 527735) B527735
theorem B515783 : Blo 207808 515783 := bstep (se 1 (by rfl) ⟨386837, by rfl⟩ : syracuseStep 515783 = 773675) B773675
theorem B352073 : Blo 207808 352073 := bstep (se 2 (by rfl) ⟨132027, by rfl⟩ : syracuseStep 352073 = 264055) B264055
theorem B2285597 : Blo 207808 2285597 := bstep (se 3 (by rfl) ⟨428549, by rfl⟩ : syracuseStep 2285597 = 857099) B857099
theorem B352505 : Blo 207808 352505 := bstep (se 2 (by rfl) ⟨132189, by rfl⟩ : syracuseStep 352505 = 264379) B264379
theorem B1794433 : Blo 207808 1794433 := bstep (se 2 (by rfl) ⟨672912, by rfl⟩ : syracuseStep 1794433 = 1345825) B1345825
theorem B352687 : Blo 207808 352687 := bstep (se 1 (by rfl) ⟨264515, by rfl⟩ : syracuseStep 352687 = 529031) B529031
theorem B352775 : Blo 207808 352775 := bstep (se 1 (by rfl) ⟨264581, by rfl⟩ : syracuseStep 352775 = 529163) B529163
theorem B713339 : Blo 207808 713339 := bstep (se 1 (by rfl) ⟨535004, by rfl⟩ : syracuseStep 713339 = 1070009) B1070009
theorem B713501 : Blo 207808 713501 := bstep (se 3 (by rfl) ⟨133781, by rfl⟩ : syracuseStep 713501 = 267563) B267563
theorem B353119 : Blo 207808 353119 := bstep (se 1 (by rfl) ⟨264839, by rfl⟩ : syracuseStep 353119 = 529679) B529679
theorem B353207 : Blo 207808 353207 := bstep (se 1 (by rfl) ⟨264905, by rfl⟩ : syracuseStep 353207 = 529811) B529811
theorem B1205401 : Blo 207808 1205401 := bstep (se 2 (by rfl) ⟨452025, by rfl⟩ : syracuseStep 1205401 = 904051) B904051
theorem B1598939 : Blo 207808 1598939 := bstep (se 1 (by rfl) ⟨1199204, by rfl⟩ : syracuseStep 1598939 = 2398409) B2398409
theorem B714203 : Blo 207808 714203 := bstep (se 1 (by rfl) ⟨535652, by rfl⟩ : syracuseStep 714203 = 1071305) B1071305
theorem B353801 : Blo 207808 353801 := bstep (se 2 (by rfl) ⟨132675, by rfl⟩ : syracuseStep 353801 = 265351) B265351
theorem B353963 : Blo 207808 353963 := bstep (se 1 (by rfl) ⟨265472, by rfl⟩ : syracuseStep 353963 = 530945) B530945
theorem B2713337 : Blo 207808 2713337 := bstep (se 2 (by rfl) ⟨1017501, by rfl⟩ : syracuseStep 2713337 = 2035003) B2035003
theorem B812843 : Blo 207808 812843 := bstep (se 1 (by rfl) ⟨609632, by rfl⟩ : syracuseStep 812843 = 1219265) B1219265
theorem B1599425 : Blo 207808 1599425 := bstep (se 2 (by rfl) ⟨599784, by rfl⟩ : syracuseStep 1599425 = 1199569) B1199569
theorem B354361 : Blo 207808 354361 := bstep (se 2 (by rfl) ⟨132885, by rfl⟩ : syracuseStep 354361 = 265771) B265771
theorem B354503 : Blo 207808 354503 := bstep (se 1 (by rfl) ⟨265877, by rfl⟩ : syracuseStep 354503 = 531755) B531755
theorem B354665 : Blo 207808 354665 := bstep (se 2 (by rfl) ⟨132999, by rfl⟩ : syracuseStep 354665 = 265999) B265999
theorem B1698515 : Blo 207808 1698515 := bstep (se 1 (by rfl) ⟨1273886, by rfl⟩ : syracuseStep 1698515 = 2547773) B2547773
theorem B355063 : Blo 207808 355063 := bstep (se 1 (by rfl) ⟨266297, by rfl⟩ : syracuseStep 355063 = 532595) B532595
theorem B3337037 : Blo 207808 3337037 := bstep (se 3 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 3337037 = 1251389) B1251389
theorem B1502059 : Blo 207808 1502059 := bstep (se 1 (by rfl) ⟨1126544, by rfl⟩ : syracuseStep 1502059 = 2253089) B2253089
theorem B355259 : Blo 207808 355259 := bstep (se 1 (by rfl) ⟨266444, by rfl⟩ : syracuseStep 355259 = 532889) B532889
theorem B224219 : Blo 207808 224219 := bstep (se 1 (by rfl) ⟨168164, by rfl⟩ : syracuseStep 224219 = 336329) B336329
theorem B355367 : Blo 207808 355367 := bstep (se 1 (by rfl) ⟨266525, by rfl⟩ : syracuseStep 355367 = 533051) B533051
theorem B355657 : Blo 207808 355657 := bstep (se 2 (by rfl) ⟨133371, by rfl⟩ : syracuseStep 355657 = 266743) B266743
theorem B355691 : Blo 207808 355691 := bstep (se 1 (by rfl) ⟨266768, by rfl⟩ : syracuseStep 355691 = 533537) B533537
theorem B1600883 : Blo 207808 1600883 := bstep (se 1 (by rfl) ⟨1200662, by rfl⟩ : syracuseStep 1600883 = 2401325) B2401325
theorem B356089 : Blo 207808 356089 := bstep (se 2 (by rfl) ⟨133533, by rfl⟩ : syracuseStep 356089 = 267067) B267067
theorem B1699679 : Blo 207808 1699679 := bstep (se 1 (by rfl) ⟨1274759, by rfl⟩ : syracuseStep 1699679 = 2549519) B2549519
theorem B12283811 : Blo 207808 12283811 := bstep (se 1 (by rfl) ⟨9212858, by rfl⟩ : syracuseStep 12283811 = 18425717) B18425717
theorem B421807 : Blo 207808 421807 := bstep (se 1 (by rfl) ⟨316355, by rfl⟩ : syracuseStep 421807 = 632711) B632711
theorem B356359 : Blo 207808 356359 := bstep (se 1 (by rfl) ⟨267269, by rfl⟩ : syracuseStep 356359 = 534539) B534539
theorem B618653 : Blo 207808 618653 := bstep (se 3 (by rfl) ⟨115997, by rfl⟩ : syracuseStep 618653 = 231995) B231995
theorem B356791 : Blo 207808 356791 := bstep (se 1 (by rfl) ⟨267593, by rfl⟩ : syracuseStep 356791 = 535187) B535187
theorem B356987 : Blo 207808 356987 := bstep (se 1 (by rfl) ⟨267740, by rfl⟩ : syracuseStep 356987 = 535481) B535481
theorem B5993473 : Blo 207808 5993473 := bstep (se 2 (by rfl) ⟨2247552, by rfl⟩ : syracuseStep 5993473 = 4495105) B4495105
theorem B357385 : Blo 207808 357385 := bstep (se 2 (by rfl) ⟨134019, by rfl⟩ : syracuseStep 357385 = 268039) B268039
theorem B1340495 : Blo 207808 1340495 := bstep (se 1 (by rfl) ⟨1005371, by rfl⟩ : syracuseStep 1340495 = 2010743) B2010743
theorem B750973 : Blo 207808 750973 := bstep (se 3 (by rfl) ⟨140807, by rfl⟩ : syracuseStep 750973 = 281615) B281615
theorem B1341521 : Blo 207808 1341521 := bstep (se 2 (by rfl) ⟨503070, by rfl⟩ : syracuseStep 1341521 = 1006141) B1006141
theorem B2029657 : Blo 207808 2029657 := bstep (se 2 (by rfl) ⟨761121, by rfl⟩ : syracuseStep 2029657 = 1522243) B1522243
theorem B2161337 : Blo 207808 2161337 := bstep (se 2 (by rfl) ⟨810501, by rfl⟩ : syracuseStep 2161337 = 1621003) B1621003
theorem B1276901 : Blo 207808 1276901 := bstep (se 4 (by rfl) ⟨119709, by rfl⟩ : syracuseStep 1276901 = 239419) B239419
theorem B949249 : Blo 207808 949249 := bstep (se 2 (by rfl) ⟨355968, by rfl⟩ : syracuseStep 949249 = 711937) B711937
theorem B2391119 : Blo 207808 2391119 := bstep (se 1 (by rfl) ⟨1793339, by rfl⟩ : syracuseStep 2391119 = 3586679) B3586679
theorem B687421 : Blo 207808 687421 := bstep (se 3 (by rfl) ⟨128891, by rfl⟩ : syracuseStep 687421 = 257783) B257783
theorem B1015213 : Blo 207808 1015213 := bstep (se 3 (by rfl) ⟨190352, by rfl⟩ : syracuseStep 1015213 = 380705) B380705
theorem B1343213 : Blo 207808 1343213 := bstep (se 3 (by rfl) ⟨251852, by rfl⟩ : syracuseStep 1343213 = 503705) B503705
theorem B753569 : Blo 207808 753569 := bstep (se 2 (by rfl) ⟨282588, by rfl⟩ : syracuseStep 753569 = 565177) B565177
theorem B425911 : Blo 207808 425911 := bstep (se 1 (by rfl) ⟨319433, by rfl⟩ : syracuseStep 425911 = 638867) B638867
theorem B1507481 : Blo 207808 1507481 := bstep (se 2 (by rfl) ⟨565305, by rfl⟩ : syracuseStep 1507481 = 1130611) B1130611
theorem B458963 : Blo 207808 458963 := bstep (se 1 (by rfl) ⟨344222, by rfl⟩ : syracuseStep 458963 = 688445) B688445
theorem B2425049 : Blo 207808 2425049 := bstep (se 2 (by rfl) ⟨909393, by rfl⟩ : syracuseStep 2425049 = 1818787) B1818787
theorem B2392577 : Blo 207808 2392577 := bstep (se 2 (by rfl) ⟨897216, by rfl⟩ : syracuseStep 2392577 = 1794433) B1794433
theorem B361387 : Blo 207808 361387 := bstep (se 1 (by rfl) ⟨271040, by rfl⟩ : syracuseStep 361387 = 542081) B542081
theorem B853409 : Blo 207808 853409 := bstep (se 2 (by rfl) ⟨320028, by rfl⟩ : syracuseStep 853409 = 640057) B640057
theorem B263675 : Blo 207808 263675 := bstep (se 1 (by rfl) ⟨197756, by rfl⟩ : syracuseStep 263675 = 395513) B395513
theorem B1607201 : Blo 207808 1607201 := bstep (se 2 (by rfl) ⟨602700, by rfl⟩ : syracuseStep 1607201 = 1205401) B1205401
theorem B4064825 : Blo 207808 4064825 := bstep (se 2 (by rfl) ⟨1524309, by rfl⟩ : syracuseStep 4064825 = 3048619) B3048619
theorem B526135 : Blo 207808 526135 := bstep (se 1 (by rfl) ⟨394601, by rfl⟩ : syracuseStep 526135 = 789203) B789203
theorem B526601 : Blo 207808 526601 := bstep (se 2 (by rfl) ⟨197475, by rfl⟩ : syracuseStep 526601 = 394951) B394951
theorem B297307 : Blo 207808 297307 := bstep (se 1 (by rfl) ⟨222980, by rfl⟩ : syracuseStep 297307 = 445961) B445961
theorem B1083773 : Blo 207808 1083773 := bstep (se 3 (by rfl) ⟨203207, by rfl⟩ : syracuseStep 1083773 = 406415) B406415
theorem B2165159 : Blo 207808 2165159 := bstep (se 1 (by rfl) ⟨1623869, by rfl⟩ : syracuseStep 2165159 = 3247739) B3247739
theorem B264647 : Blo 207808 264647 := bstep (se 1 (by rfl) ⟨198485, by rfl⟩ : syracuseStep 264647 = 396971) B396971
theorem B297535 : Blo 207808 297535 := bstep (se 1 (by rfl) ⟨223151, by rfl⟩ : syracuseStep 297535 = 446303) B446303
theorem B264799 : Blo 207808 264799 := bstep (se 1 (by rfl) ⟨198599, by rfl⟩ : syracuseStep 264799 = 397199) B397199
theorem B1510109 : Blo 207808 1510109 := bstep (se 3 (by rfl) ⟨283145, by rfl⟩ : syracuseStep 1510109 = 566291) B566291
theorem B395999 : Blo 207808 395999 := bstep (se 1 (by rfl) ⟨296999, by rfl⟩ : syracuseStep 395999 = 593999) B593999
theorem B592883 : Blo 207808 592883 := bstep (se 1 (by rfl) ⟨444662, by rfl⟩ : syracuseStep 592883 = 889325) B889325
theorem B527593 : Blo 207808 527593 := bstep (se 2 (by rfl) ⟨197847, by rfl⟩ : syracuseStep 527593 = 395695) B395695
theorem B789857 : Blo 207808 789857 := bstep (se 2 (by rfl) ⟨296196, by rfl⟩ : syracuseStep 789857 = 592393) B592393
theorem B2100599 : Blo 207808 2100599 := bstep (se 1 (by rfl) ⟨1575449, by rfl⟩ : syracuseStep 2100599 = 3150899) B3150899
theorem B396667 : Blo 207808 396667 := bstep (se 1 (by rfl) ⟨297500, by rfl⟩ : syracuseStep 396667 = 595001) B595001
theorem B527755 : Blo 207808 527755 := bstep (se 1 (by rfl) ⟨395816, by rfl⟩ : syracuseStep 527755 = 791633) B791633
theorem B888401 : Blo 207808 888401 := bstep (se 2 (by rfl) ⟨333150, by rfl⟩ : syracuseStep 888401 = 666301) B666301
theorem B396895 : Blo 207808 396895 := bstep (se 1 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 396895 = 595343) B595343
theorem B528059 : Blo 207808 528059 := bstep (se 1 (by rfl) ⟨396044, by rfl⟩ : syracuseStep 528059 = 792089) B792089
theorem B2133715 : Blo 207808 2133715 := bstep (se 1 (by rfl) ⟨1600286, by rfl⟩ : syracuseStep 2133715 = 3200573) B3200573
theorem B8228587 : Blo 207808 8228587 := bstep (se 1 (by rfl) ⟨6171440, by rfl⟩ : syracuseStep 8228587 = 12342881) B12342881
theorem B2002745 : Blo 207808 2002745 := bstep (se 2 (by rfl) ⟨751029, by rfl⟩ : syracuseStep 2002745 = 1502059) B1502059
theorem B3018653 : Blo 207808 3018653 := bstep (se 3 (by rfl) ⟨565997, by rfl⟩ : syracuseStep 3018653 = 1131995) B1131995
theorem B6426773 : Blo 207808 6426773 := bstep (se 6 (by rfl) ⟨150627, by rfl⟩ : syracuseStep 6426773 = 301255) B301255
theorem B233851 : Blo 207808 233851 := bstep (se 1 (by rfl) ⟨175388, by rfl⟩ : syracuseStep 233851 = 350777) B350777
theorem B889289 : Blo 207808 889289 := bstep (se 2 (by rfl) ⟨333483, by rfl⟩ : syracuseStep 889289 = 666967) B666967
theorem B234319 : Blo 207808 234319 := bstep (se 1 (by rfl) ⟨175739, by rfl⟩ : syracuseStep 234319 = 351479) B351479
theorem B267239 : Blo 207808 267239 := bstep (se 1 (by rfl) ⟨200429, by rfl⟩ : syracuseStep 267239 = 400859) B400859
theorem B234715 : Blo 207808 234715 := bstep (se 1 (by rfl) ⟨176036, by rfl⟩ : syracuseStep 234715 = 352073) B352073
theorem B562409 : Blo 207808 562409 := bstep (se 2 (by rfl) ⟨210903, by rfl⟩ : syracuseStep 562409 = 421807) B421807
theorem B791801 : Blo 207808 791801 := bstep (se 2 (by rfl) ⟨296925, by rfl⟩ : syracuseStep 791801 = 593851) B593851
theorem B333305 : Blo 207808 333305 := bstep (se 2 (by rfl) ⟨124989, by rfl⟩ : syracuseStep 333305 = 249979) B249979
theorem B235003 : Blo 207808 235003 := bstep (se 1 (by rfl) ⟨176252, by rfl⟩ : syracuseStep 235003 = 352505) B352505
theorem B530003 : Blo 207808 530003 := bstep (se 1 (by rfl) ⟨397502, by rfl⟩ : syracuseStep 530003 = 795005) B795005
theorem B235183 : Blo 207808 235183 := bstep (se 1 (by rfl) ⟨176387, by rfl⟩ : syracuseStep 235183 = 352775) B352775
theorem B268111 : Blo 207808 268111 := bstep (se 1 (by rfl) ⟨201083, by rfl⟩ : syracuseStep 268111 = 402167) B402167
theorem B235471 : Blo 207808 235471 := bstep (se 1 (by rfl) ⟨176603, by rfl⟩ : syracuseStep 235471 = 353207) B353207
theorem B235867 : Blo 207808 235867 := bstep (se 1 (by rfl) ⟨176900, by rfl⟩ : syracuseStep 235867 = 353801) B353801
theorem B235975 : Blo 207808 235975 := bstep (se 1 (by rfl) ⟨176981, by rfl⟩ : syracuseStep 235975 = 353963) B353963
theorem B1808891 : Blo 207808 1808891 := bstep (se 1 (by rfl) ⟨1356668, by rfl⟩ : syracuseStep 1808891 = 2713337) B2713337
theorem B236335 : Blo 207808 236335 := bstep (se 1 (by rfl) ⟨177251, by rfl⟩ : syracuseStep 236335 = 354503) B354503
theorem B236443 : Blo 207808 236443 := bstep (se 1 (by rfl) ⟨177332, by rfl⟩ : syracuseStep 236443 = 354665) B354665
theorem B531431 : Blo 207808 531431 := bstep (se 1 (by rfl) ⟨398573, by rfl⟩ : syracuseStep 531431 = 797147) B797147
theorem B236839 : Blo 207808 236839 := bstep (se 1 (by rfl) ⟨177629, by rfl⟩ : syracuseStep 236839 = 355259) B355259
theorem B236911 : Blo 207808 236911 := bstep (se 1 (by rfl) ⟨177683, by rfl⟩ : syracuseStep 236911 = 355367) B355367
theorem B400889 : Blo 207808 400889 := bstep (se 2 (by rfl) ⟨150333, by rfl⟩ : syracuseStep 400889 = 300667) B300667
theorem B1777211 : Blo 207808 1777211 := bstep (se 1 (by rfl) ⟨1332908, by rfl⟩ : syracuseStep 1777211 = 2665817) B2665817
theorem B237127 : Blo 207808 237127 := bstep (se 1 (by rfl) ⟨177845, by rfl⟩ : syracuseStep 237127 = 355691) B355691
theorem B532129 : Blo 207808 532129 := bstep (se 2 (by rfl) ⟨199548, by rfl⟩ : syracuseStep 532129 = 399097) B399097
theorem B532271 : Blo 207808 532271 := bstep (se 1 (by rfl) ⟨399203, by rfl⟩ : syracuseStep 532271 = 798407) B798407
theorem B991033 : Blo 207808 991033 := bstep (se 2 (by rfl) ⟨371637, by rfl⟩ : syracuseStep 991033 = 743275) B743275
theorem B597917 : Blo 207808 597917 := bstep (se 3 (by rfl) ⟨112109, by rfl⟩ : syracuseStep 597917 = 224219) B224219
theorem B2433235 : Blo 207808 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B401755 : Blo 207808 401755 := bstep (se 1 (by rfl) ⟨301316, by rfl⟩ : syracuseStep 401755 = 602633) B602633
theorem B237991 : Blo 207808 237991 := bstep (se 1 (by rfl) ⟨178493, by rfl⟩ : syracuseStep 237991 = 356987) B356987
theorem B401831 : Blo 207808 401831 := bstep (se 1 (by rfl) ⟨301373, by rfl⟩ : syracuseStep 401831 = 602747) B602747
theorem B532919 : Blo 207808 532919 := bstep (se 1 (by rfl) ⟨399689, by rfl⟩ : syracuseStep 532919 = 799379) B799379
theorem B401915 : Blo 207808 401915 := bstep (se 1 (by rfl) ⟨301436, by rfl⟩ : syracuseStep 401915 = 602873) B602873
theorem B336559 : Blo 207808 336559 := bstep (se 1 (by rfl) ⟨252419, by rfl⟩ : syracuseStep 336559 = 504839) B504839
theorem B467639 : Blo 207808 467639 := bstep (se 1 (by rfl) ⟨350729, by rfl⟩ : syracuseStep 467639 = 701459) B701459
theorem B893663 : Blo 207808 893663 := bstep (se 1 (by rfl) ⟨670247, by rfl⟩ : syracuseStep 893663 = 1340495) B1340495
theorem B4301585 : Blo 207808 4301585 := bstep (se 2 (by rfl) ⟨1613094, by rfl⟩ : syracuseStep 4301585 = 3226189) B3226189
theorem B467855 : Blo 207808 467855 := bstep (se 1 (by rfl) ⟨350891, by rfl⟩ : syracuseStep 467855 = 701783) B701783
theorem B1057697 : Blo 207808 1057697 := bstep (se 2 (by rfl) ⟨396636, by rfl⟩ : syracuseStep 1057697 = 793273) B793273
theorem B4268983 : Blo 207808 4268983 := bstep (se 1 (by rfl) ⟨3201737, by rfl⟩ : syracuseStep 4268983 = 6403475) B6403475
theorem B1516481 : Blo 207808 1516481 := bstep (se 2 (by rfl) ⟨568680, by rfl⟩ : syracuseStep 1516481 = 1137361) B1137361
theorem B402575 : Blo 207808 402575 := bstep (se 1 (by rfl) ⟨301931, by rfl⟩ : syracuseStep 402575 = 603863) B603863
theorem B1778921 : Blo 207808 1778921 := bstep (se 2 (by rfl) ⟨667095, by rfl⟩ : syracuseStep 1778921 = 1334191) B1334191
theorem B894347 : Blo 207808 894347 := bstep (se 1 (by rfl) ⟨670760, by rfl⟩ : syracuseStep 894347 = 1341521) B1341521
theorem B534023 : Blo 207808 534023 := bstep (se 1 (by rfl) ⟨400517, by rfl⟩ : syracuseStep 534023 = 801035) B801035
theorem B534073 : Blo 207808 534073 := bstep (se 2 (by rfl) ⟨200277, by rfl⟩ : syracuseStep 534073 = 400555) B400555
theorem B468575 : Blo 207808 468575 := bstep (se 1 (by rfl) ⟨351431, by rfl⟩ : syracuseStep 468575 = 702863) B702863
theorem B468791 : Blo 207808 468791 := bstep (se 1 (by rfl) ⟨351593, by rfl⟩ : syracuseStep 468791 = 703187) B703187
theorem B534377 : Blo 207808 534377 := bstep (se 2 (by rfl) ⟨200391, by rfl⟩ : syracuseStep 534377 = 400783) B400783
theorem B1845125 : Blo 207808 1845125 := bstep (se 4 (by rfl) ⟨172980, by rfl⟩ : syracuseStep 1845125 = 345961) B345961
theorem B1353617 : Blo 207808 1353617 := bstep (se 2 (by rfl) ⟨507606, by rfl⟩ : syracuseStep 1353617 = 1015213) B1015213
theorem B1124279 : Blo 207808 1124279 := bstep (se 1 (by rfl) ⟨843209, by rfl⟩ : syracuseStep 1124279 = 1686419) B1686419
theorem B469097 : Blo 207808 469097 := bstep (se 2 (by rfl) ⟨175911, by rfl⟩ : syracuseStep 469097 = 351823) B351823
theorem B534995 : Blo 207808 534995 := bstep (se 1 (by rfl) ⟨401246, by rfl⟩ : syracuseStep 534995 = 802493) B802493
theorem B895475 : Blo 207808 895475 := bstep (se 1 (by rfl) ⟨671606, by rfl⟩ : syracuseStep 895475 = 1343213) B1343213
theorem B567881 : Blo 207808 567881 := bstep (se 2 (by rfl) ⟨212955, by rfl⟩ : syracuseStep 567881 = 425911) B425911
theorem B469583 : Blo 207808 469583 := bstep (se 1 (by rfl) ⟨352187, by rfl⟩ : syracuseStep 469583 = 704375) B704375
theorem B502379 : Blo 207808 502379 := bstep (se 1 (by rfl) ⟨376784, by rfl⟩ : syracuseStep 502379 = 753569) B753569
theorem B469727 : Blo 207808 469727 := bstep (se 1 (by rfl) ⟨352295, by rfl⟩ : syracuseStep 469727 = 704591) B704591
theorem B207823 : Blo 207808 207823 := bstep (se 1 (by rfl) ⟨155867, by rfl⟩ : syracuseStep 207823 = 311735) B311735
theorem B469979 : Blo 207808 469979 := bstep (se 1 (by rfl) ⟨352484, by rfl⟩ : syracuseStep 469979 = 704969) B704969
theorem B207847 : Blo 207808 207847 := bstep (se 1 (by rfl) ⟨155885, by rfl⟩ : syracuseStep 207847 = 311771) B311771
theorem B896123 : Blo 207808 896123 := bstep (se 1 (by rfl) ⟨672092, by rfl⟩ : syracuseStep 896123 = 1344185) B1344185
theorem B470159 : Blo 207808 470159 := bstep (se 1 (by rfl) ⟨352619, by rfl⟩ : syracuseStep 470159 = 705239) B705239
theorem B470249 : Blo 207808 470249 := bstep (se 2 (by rfl) ⟨176343, by rfl⟩ : syracuseStep 470249 = 352687) B352687
theorem B208159 : Blo 207808 208159 := bstep (se 1 (by rfl) ⟨156119, by rfl⟩ : syracuseStep 208159 = 312239) B312239
theorem B470303 : Blo 207808 470303 := bstep (se 1 (by rfl) ⟨352727, by rfl⟩ : syracuseStep 470303 = 705455) B705455
theorem B1060127 : Blo 207808 1060127 := bstep (se 1 (by rfl) ⟨795095, by rfl⟩ : syracuseStep 1060127 = 1590191) B1590191
theorem B208219 : Blo 207808 208219 := bstep (se 1 (by rfl) ⟨156164, by rfl⟩ : syracuseStep 208219 = 312329) B312329
theorem B208239 : Blo 207808 208239 := bstep (se 1 (by rfl) ⟨156179, by rfl⟩ : syracuseStep 208239 = 312359) B312359
theorem B208295 : Blo 207808 208295 := bstep (se 1 (by rfl) ⟨156221, by rfl⟩ : syracuseStep 208295 = 312443) B312443
theorem B208379 : Blo 207808 208379 := bstep (se 1 (by rfl) ⟨156284, by rfl⟩ : syracuseStep 208379 = 312569) B312569
theorem B208447 : Blo 207808 208447 := bstep (se 1 (by rfl) ⟨156335, by rfl⟩ : syracuseStep 208447 = 312671) B312671
theorem B208455 : Blo 207808 208455 := bstep (se 1 (by rfl) ⟨156341, by rfl⟩ : syracuseStep 208455 = 312683) B312683
theorem B208607 : Blo 207808 208607 := bstep (se 1 (by rfl) ⟨156455, by rfl⟩ : syracuseStep 208607 = 312911) B312911
theorem B470825 : Blo 207808 470825 := bstep (se 2 (by rfl) ⟨176559, by rfl⟩ : syracuseStep 470825 = 353119) B353119
theorem B208687 : Blo 207808 208687 := bstep (se 1 (by rfl) ⟨156515, by rfl⟩ : syracuseStep 208687 = 313031) B313031
theorem B208795 : Blo 207808 208795 := bstep (se 1 (by rfl) ⟨156596, by rfl⟩ : syracuseStep 208795 = 313193) B313193
theorem B208847 : Blo 207808 208847 := bstep (se 1 (by rfl) ⟨156635, by rfl⟩ : syracuseStep 208847 = 313271) B313271
theorem B208871 : Blo 207808 208871 := bstep (se 1 (by rfl) ⟨156653, by rfl⟩ : syracuseStep 208871 = 313307) B313307
theorem B667673 : Blo 207808 667673 := bstep (se 2 (by rfl) ⟨250377, by rfl⟩ : syracuseStep 667673 = 500755) B500755
theorem B209183 : Blo 207808 209183 := bstep (se 1 (by rfl) ⟨156887, by rfl⟩ : syracuseStep 209183 = 313775) B313775
theorem B209243 : Blo 207808 209243 := bstep (se 1 (by rfl) ⟨156932, by rfl⟩ : syracuseStep 209243 = 313865) B313865
theorem B209263 : Blo 207808 209263 := bstep (se 1 (by rfl) ⟨156947, by rfl⟩ : syracuseStep 209263 = 313895) B313895
theorem B209319 : Blo 207808 209319 := bstep (se 1 (by rfl) ⟨156989, by rfl⟩ : syracuseStep 209319 = 313979) B313979
theorem B209403 : Blo 207808 209403 := bstep (se 1 (by rfl) ⟨157052, by rfl⟩ : syracuseStep 209403 = 314105) B314105
theorem B8663597 : Blo 207808 8663597 := bstep (se 3 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 8663597 = 3248849) B3248849
theorem B209471 : Blo 207808 209471 := bstep (se 1 (by rfl) ⟨157103, by rfl⟩ : syracuseStep 209471 = 314207) B314207
theorem B209479 : Blo 207808 209479 := bstep (se 1 (by rfl) ⟨157109, by rfl⟩ : syracuseStep 209479 = 314219) B314219
theorem B1356385 : Blo 207808 1356385 := bstep (se 2 (by rfl) ⟨508644, by rfl⟩ : syracuseStep 1356385 = 1017289) B1017289
theorem B1585817 : Blo 207808 1585817 := bstep (se 2 (by rfl) ⟨594681, by rfl⟩ : syracuseStep 1585817 = 1189363) B1189363
theorem B209631 : Blo 207808 209631 := bstep (se 1 (by rfl) ⟨157223, by rfl⟩ : syracuseStep 209631 = 314447) B314447
theorem B209711 : Blo 207808 209711 := bstep (se 1 (by rfl) ⟨157283, by rfl⟩ : syracuseStep 209711 = 314567) B314567
theorem B471887 : Blo 207808 471887 := bstep (se 1 (by rfl) ⟨353915, by rfl⟩ : syracuseStep 471887 = 707831) B707831
theorem B4043627 : Blo 207808 4043627 := bstep (se 1 (by rfl) ⟨3032720, by rfl⟩ : syracuseStep 4043627 = 6065441) B6065441
theorem B209819 : Blo 207808 209819 := bstep (se 1 (by rfl) ⟨157364, by rfl⟩ : syracuseStep 209819 = 314729) B314729
theorem B209871 : Blo 207808 209871 := bstep (se 1 (by rfl) ⟨157403, by rfl⟩ : syracuseStep 209871 = 314807) B314807
theorem B209895 : Blo 207808 209895 := bstep (se 1 (by rfl) ⟨157421, by rfl⟩ : syracuseStep 209895 = 314843) B314843
theorem B537587 : Blo 207808 537587 := bstep (se 1 (by rfl) ⟨403190, by rfl⟩ : syracuseStep 537587 = 806381) B806381
theorem B472103 : Blo 207808 472103 := bstep (se 1 (by rfl) ⟨354077, by rfl⟩ : syracuseStep 472103 = 708155) B708155
theorem B472283 : Blo 207808 472283 := bstep (se 1 (by rfl) ⟨354212, by rfl⟩ : syracuseStep 472283 = 708425) B708425
theorem B668915 : Blo 207808 668915 := bstep (se 1 (by rfl) ⟨501686, by rfl⟩ : syracuseStep 668915 = 1003373) B1003373
theorem B210207 : Blo 207808 210207 := bstep (se 1 (by rfl) ⟨157655, by rfl⟩ : syracuseStep 210207 = 315311) B315311
theorem B210267 : Blo 207808 210267 := bstep (se 1 (by rfl) ⟨157700, by rfl⟩ : syracuseStep 210267 = 315401) B315401
theorem B537953 : Blo 207808 537953 := bstep (se 2 (by rfl) ⟨201732, by rfl⟩ : syracuseStep 537953 = 403465) B403465
theorem B210287 : Blo 207808 210287 := bstep (se 1 (by rfl) ⟨157715, by rfl⟩ : syracuseStep 210287 = 315431) B315431
theorem B472481 : Blo 207808 472481 := bstep (se 2 (by rfl) ⟨177180, by rfl⟩ : syracuseStep 472481 = 354361) B354361
theorem B210343 : Blo 207808 210343 := bstep (se 1 (by rfl) ⟨157757, by rfl⟩ : syracuseStep 210343 = 315515) B315515
theorem B210427 : Blo 207808 210427 := bstep (se 1 (by rfl) ⟨157820, by rfl⟩ : syracuseStep 210427 = 315641) B315641
theorem B210495 : Blo 207808 210495 := bstep (se 1 (by rfl) ⟨157871, by rfl⟩ : syracuseStep 210495 = 315743) B315743
theorem B210503 : Blo 207808 210503 := bstep (se 1 (by rfl) ⟨157877, by rfl⟩ : syracuseStep 210503 = 315755) B315755
theorem B1062557 : Blo 207808 1062557 := bstep (se 3 (by rfl) ⟨199229, by rfl⟩ : syracuseStep 1062557 = 398459) B398459
theorem B505531 : Blo 207808 505531 := bstep (se 1 (by rfl) ⟨379148, by rfl⟩ : syracuseStep 505531 = 758297) B758297
theorem B210655 : Blo 207808 210655 := bstep (se 1 (by rfl) ⟨157991, by rfl⟩ : syracuseStep 210655 = 315983) B315983
theorem B505607 : Blo 207808 505607 := bstep (se 1 (by rfl) ⟨379205, by rfl⟩ : syracuseStep 505607 = 758411) B758411
theorem B210735 : Blo 207808 210735 := bstep (se 1 (by rfl) ⟨158051, by rfl⟩ : syracuseStep 210735 = 316103) B316103
theorem B210843 : Blo 207808 210843 := bstep (se 1 (by rfl) ⟨158132, by rfl⟩ : syracuseStep 210843 = 316265) B316265
theorem B473039 : Blo 207808 473039 := bstep (se 1 (by rfl) ⟨354779, by rfl⟩ : syracuseStep 473039 = 709559) B709559
theorem B210895 : Blo 207808 210895 := bstep (se 1 (by rfl) ⟨158171, by rfl⟩ : syracuseStep 210895 = 316343) B316343
theorem B210919 : Blo 207808 210919 := bstep (se 1 (by rfl) ⟨158189, by rfl⟩ : syracuseStep 210919 = 316379) B316379
theorem B702593 : Blo 207808 702593 := bstep (se 2 (by rfl) ⟨263472, by rfl⟩ : syracuseStep 702593 = 526945) B526945
theorem B1194263 : Blo 207808 1194263 := bstep (se 1 (by rfl) ⟨895697, by rfl⟩ : syracuseStep 1194263 = 1791395) B1791395
theorem B801049 : Blo 207808 801049 := bstep (se 2 (by rfl) ⟨300393, by rfl⟩ : syracuseStep 801049 = 600787) B600787
theorem B211231 : Blo 207808 211231 := bstep (se 1 (by rfl) ⟨158423, by rfl⟩ : syracuseStep 211231 = 316847) B316847
theorem B473417 : Blo 207808 473417 := bstep (se 2 (by rfl) ⟨177531, by rfl⟩ : syracuseStep 473417 = 355063) B355063
theorem B473435 : Blo 207808 473435 := bstep (se 1 (by rfl) ⟨355076, by rfl⟩ : syracuseStep 473435 = 710153) B710153
theorem B211291 : Blo 207808 211291 := bstep (se 1 (by rfl) ⟨158468, by rfl⟩ : syracuseStep 211291 = 316937) B316937
theorem B211311 : Blo 207808 211311 := bstep (se 1 (by rfl) ⟨158483, by rfl⟩ : syracuseStep 211311 = 316967) B316967
theorem B211367 : Blo 207808 211367 := bstep (se 1 (by rfl) ⟨158525, by rfl⟩ : syracuseStep 211367 = 317051) B317051
theorem B702971 : Blo 207808 702971 := bstep (se 1 (by rfl) ⟨527228, by rfl⟩ : syracuseStep 702971 = 1054457) B1054457
theorem B211451 : Blo 207808 211451 := bstep (se 1 (by rfl) ⟨158588, by rfl⟩ : syracuseStep 211451 = 317177) B317177
theorem B211519 : Blo 207808 211519 := bstep (se 1 (by rfl) ⟨158639, by rfl⟩ : syracuseStep 211519 = 317279) B317279
theorem B211527 : Blo 207808 211527 := bstep (se 1 (by rfl) ⟨158645, by rfl⟩ : syracuseStep 211527 = 317291) B317291
theorem B801353 : Blo 207808 801353 := bstep (se 2 (by rfl) ⟨300507, by rfl⟩ : syracuseStep 801353 = 601015) B601015
theorem B211679 : Blo 207808 211679 := bstep (se 1 (by rfl) ⟨158759, by rfl⟩ : syracuseStep 211679 = 317519) B317519
theorem B211759 : Blo 207808 211759 := bstep (se 1 (by rfl) ⟨158819, by rfl⟩ : syracuseStep 211759 = 317639) B317639
theorem B474011 : Blo 207808 474011 := bstep (se 1 (by rfl) ⟨355508, by rfl⟩ : syracuseStep 474011 = 711017) B711017
theorem B703403 : Blo 207808 703403 := bstep (se 1 (by rfl) ⟨527552, by rfl⟩ : syracuseStep 703403 = 1055105) B1055105
theorem B1063853 : Blo 207808 1063853 := bstep (se 3 (by rfl) ⟨199472, by rfl⟩ : syracuseStep 1063853 = 398945) B398945
theorem B474209 : Blo 207808 474209 := bstep (se 2 (by rfl) ⟨177828, by rfl⟩ : syracuseStep 474209 = 355657) B355657
theorem B474407 : Blo 207808 474407 := bstep (se 1 (by rfl) ⟨355805, by rfl⟩ : syracuseStep 474407 = 711611) B711611
theorem B703943 : Blo 207808 703943 := bstep (se 1 (by rfl) ⟨527957, by rfl⟩ : syracuseStep 703943 = 1055915) B1055915
theorem B474785 : Blo 207808 474785 := bstep (se 2 (by rfl) ⟨178044, by rfl⟩ : syracuseStep 474785 = 356089) B356089
theorem B704267 : Blo 207808 704267 := bstep (se 1 (by rfl) ⟨528200, by rfl⟩ : syracuseStep 704267 = 1056401) B1056401
theorem B343855 : Blo 207808 343855 := bstep (se 1 (by rfl) ⟨257891, by rfl⟩ : syracuseStep 343855 = 515783) B515783
theorem B507703 : Blo 207808 507703 := bstep (se 1 (by rfl) ⟨380777, by rfl⟩ : syracuseStep 507703 = 761555) B761555
theorem B540521 : Blo 207808 540521 := bstep (se 2 (by rfl) ⟨202695, by rfl⟩ : syracuseStep 540521 = 405391) B405391
theorem B475145 : Blo 207808 475145 := bstep (se 2 (by rfl) ⟨178179, by rfl⟩ : syracuseStep 475145 = 356359) B356359
theorem B1523731 : Blo 207808 1523731 := bstep (se 1 (by rfl) ⟨1142798, by rfl⟩ : syracuseStep 1523731 = 2285597) B2285597
theorem B704537 : Blo 207808 704537 := bstep (se 2 (by rfl) ⟨264201, by rfl⟩ : syracuseStep 704537 = 528403) B528403
theorem B475559 : Blo 207808 475559 := bstep (se 1 (by rfl) ⟨356669, by rfl⟩ : syracuseStep 475559 = 713339) B713339
theorem B1589705 : Blo 207808 1589705 := bstep (se 2 (by rfl) ⟨596139, by rfl⟩ : syracuseStep 1589705 = 1192279) B1192279
theorem B803297 : Blo 207808 803297 := bstep (se 2 (by rfl) ⟨301236, by rfl⟩ : syracuseStep 803297 = 602473) B602473
theorem B1065473 : Blo 207808 1065473 := bstep (se 2 (by rfl) ⟨399552, by rfl⟩ : syracuseStep 1065473 = 799105) B799105
theorem B475667 : Blo 207808 475667 := bstep (se 1 (by rfl) ⟨356750, by rfl⟩ : syracuseStep 475667 = 713501) B713501
theorem B311879 : Blo 207808 311879 := bstep (se 1 (by rfl) ⟨233909, by rfl⟩ : syracuseStep 311879 = 467819) B467819
theorem B475721 : Blo 207808 475721 := bstep (se 2 (by rfl) ⟨178395, by rfl⟩ : syracuseStep 475721 = 356791) B356791
theorem B311915 : Blo 207808 311915 := bstep (se 1 (by rfl) ⟨233936, by rfl⟩ : syracuseStep 311915 = 467873) B467873
theorem B312143 : Blo 207808 312143 := bstep (se 1 (by rfl) ⟨234107, by rfl⟩ : syracuseStep 312143 = 468215) B468215
theorem B6800273 : Blo 207808 6800273 := bstep (se 2 (by rfl) ⟨2550102, by rfl⟩ : syracuseStep 6800273 = 5100205) B5100205
theorem B5129153 : Blo 207808 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B1065959 : Blo 207808 1065959 := bstep (se 1 (by rfl) ⟨799469, by rfl⟩ : syracuseStep 1065959 = 1598939) B1598939
theorem B476135 : Blo 207808 476135 := bstep (se 1 (by rfl) ⟨357101, by rfl⟩ : syracuseStep 476135 = 714203) B714203
theorem B803965 : Blo 207808 803965 := bstep (se 3 (by rfl) ⟨150743, by rfl⟩ : syracuseStep 803965 = 301487) B301487
theorem B541895 : Blo 207808 541895 := bstep (se 1 (by rfl) ⟨406421, by rfl⟩ : syracuseStep 541895 = 812843) B812843
theorem B312539 : Blo 207808 312539 := bstep (se 1 (by rfl) ⟨234404, by rfl⟩ : syracuseStep 312539 = 468809) B468809
theorem B705779 : Blo 207808 705779 := bstep (se 1 (by rfl) ⟨529334, by rfl⟩ : syracuseStep 705779 = 1058669) B1058669
theorem B1066283 : Blo 207808 1066283 := bstep (se 1 (by rfl) ⟨799712, by rfl⟩ : syracuseStep 1066283 = 1599425) B1599425
theorem B705887 : Blo 207808 705887 := bstep (se 1 (by rfl) ⟨529415, by rfl⟩ : syracuseStep 705887 = 1058831) B1058831
theorem B476513 : Blo 207808 476513 := bstep (se 2 (by rfl) ⟨178692, by rfl⟩ : syracuseStep 476513 = 357385) B357385
theorem B312713 : Blo 207808 312713 := bstep (se 2 (by rfl) ⟨117267, by rfl⟩ : syracuseStep 312713 = 234535) B234535
theorem B25740989 : Blo 207808 25740989 := bstep (se 3 (by rfl) ⟨4826435, by rfl⟩ : syracuseStep 25740989 = 9652871) B9652871
theorem B313067 : Blo 207808 313067 := bstep (se 1 (by rfl) ⟨234800, by rfl⟩ : syracuseStep 313067 = 469601) B469601
theorem B1132343 : Blo 207808 1132343 := bstep (se 1 (by rfl) ⟨849257, by rfl⟩ : syracuseStep 1132343 = 1698515) B1698515
theorem B1001297 : Blo 207808 1001297 := bstep (se 2 (by rfl) ⟨375486, by rfl⟩ : syracuseStep 1001297 = 750973) B750973
theorem B1197929 : Blo 207808 1197929 := bstep (se 2 (by rfl) ⟨449223, by rfl⟩ : syracuseStep 1197929 = 898447) B898447
theorem B3000199 : Blo 207808 3000199 := bstep (se 1 (by rfl) ⟨2250149, by rfl⟩ : syracuseStep 3000199 = 4500299) B4500299
theorem B903095 : Blo 207808 903095 := bstep (se 1 (by rfl) ⟨677321, by rfl⟩ : syracuseStep 903095 = 1354643) B1354643
theorem B313295 : Blo 207808 313295 := bstep (se 1 (by rfl) ⟨234971, by rfl⟩ : syracuseStep 313295 = 469943) B469943
theorem B13551745 : Blo 207808 13551745 := bstep (se 2 (by rfl) ⟨5081904, by rfl⟩ : syracuseStep 13551745 = 10163809) B10163809
theorem B1067255 : Blo 207808 1067255 := bstep (se 1 (by rfl) ⟨800441, by rfl⟩ : syracuseStep 1067255 = 1600883) B1600883
theorem B313691 : Blo 207808 313691 := bstep (se 1 (by rfl) ⟨235268, by rfl⟩ : syracuseStep 313691 = 470537) B470537
theorem B313919 : Blo 207808 313919 := bstep (se 1 (by rfl) ⟨235439, by rfl⟩ : syracuseStep 313919 = 470879) B470879
theorem B1133119 : Blo 207808 1133119 := bstep (se 1 (by rfl) ⟨849839, by rfl⟩ : syracuseStep 1133119 = 1699679) B1699679
theorem B314039 : Blo 207808 314039 := bstep (se 1 (by rfl) ⟨235529, by rfl⟩ : syracuseStep 314039 = 471059) B471059
theorem B2214611 : Blo 207808 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B1067741 : Blo 207808 1067741 := bstep (se 3 (by rfl) ⟨200201, by rfl⟩ : syracuseStep 1067741 = 400403) B400403
theorem B412435 : Blo 207808 412435 := bstep (se 1 (by rfl) ⟨309326, by rfl⟩ : syracuseStep 412435 = 618653) B618653
theorem B2706209 : Blo 207808 2706209 := bstep (se 2 (by rfl) ⟨1014828, by rfl⟩ : syracuseStep 2706209 = 2029657) B2029657
theorem B707453 : Blo 207808 707453 := bstep (se 3 (by rfl) ⟨132647, by rfl⟩ : syracuseStep 707453 = 265295) B265295
theorem B314267 : Blo 207808 314267 := bstep (se 1 (by rfl) ⟨235700, by rfl⟩ : syracuseStep 314267 = 471401) B471401
theorem B707723 : Blo 207808 707723 := bstep (se 1 (by rfl) ⟨530792, by rfl⟩ : syracuseStep 707723 = 1061585) B1061585
theorem B380123 : Blo 207808 380123 := bstep (se 1 (by rfl) ⟨285092, by rfl⟩ : syracuseStep 380123 = 570185) B570185
theorem B314663 : Blo 207808 314663 := bstep (se 1 (by rfl) ⟨235997, by rfl⟩ : syracuseStep 314663 = 471995) B471995
theorem B314747 : Blo 207808 314747 := bstep (se 1 (by rfl) ⟨236060, by rfl⟩ : syracuseStep 314747 = 472121) B472121
theorem B4050323 : Blo 207808 4050323 := bstep (se 1 (by rfl) ⟨3037742, by rfl⟩ : syracuseStep 4050323 = 6075485) B6075485
theorem B380359 : Blo 207808 380359 := bstep (se 1 (by rfl) ⟨285269, by rfl⟩ : syracuseStep 380359 = 570539) B570539
theorem B314873 : Blo 207808 314873 := bstep (se 2 (by rfl) ⟨118077, by rfl⟩ : syracuseStep 314873 = 236155) B236155
theorem B314975 : Blo 207808 314975 := bstep (se 1 (by rfl) ⟨236231, by rfl⟩ : syracuseStep 314975 = 472463) B472463
theorem B315191 : Blo 207808 315191 := bstep (se 1 (by rfl) ⟨236393, by rfl⟩ : syracuseStep 315191 = 472787) B472787
theorem B1265665 : Blo 207808 1265665 := bstep (se 2 (by rfl) ⟨474624, by rfl⟩ : syracuseStep 1265665 = 949249) B949249
theorem B1364035 : Blo 207808 1364035 := bstep (se 1 (by rfl) ⟨1023026, by rfl⟩ : syracuseStep 1364035 = 2046053) B2046053
theorem B315497 : Blo 207808 315497 := bstep (se 2 (by rfl) ⟨118311, by rfl⟩ : syracuseStep 315497 = 236623) B236623
theorem B315815 : Blo 207808 315815 := bstep (se 1 (by rfl) ⟨236861, by rfl⟩ : syracuseStep 315815 = 473723) B473723
theorem B315899 : Blo 207808 315899 := bstep (se 1 (by rfl) ⟨236924, by rfl⟩ : syracuseStep 315899 = 473849) B473849
theorem B316025 : Blo 207808 316025 := bstep (se 2 (by rfl) ⟨118509, by rfl⟩ : syracuseStep 316025 = 237019) B237019
theorem B316079 : Blo 207808 316079 := bstep (se 1 (by rfl) ⟨237059, by rfl⟩ : syracuseStep 316079 = 474119) B474119
theorem B1594079 : Blo 207808 1594079 := bstep (se 1 (by rfl) ⟨1195559, by rfl⟩ : syracuseStep 1594079 = 2391119) B2391119
theorem B709343 : Blo 207808 709343 := bstep (se 1 (by rfl) ⟨532007, by rfl⟩ : syracuseStep 709343 = 1064015) B1064015
theorem B316127 : Blo 207808 316127 := bstep (se 1 (by rfl) ⟨237095, by rfl⟩ : syracuseStep 316127 = 474191) B474191
theorem B51958745 : Blo 207808 51958745 := bstep (se 2 (by rfl) ⟨19484529, by rfl⟩ : syracuseStep 51958745 = 38969059) B38969059
theorem B316391 : Blo 207808 316391 := bstep (se 1 (by rfl) ⟨237293, by rfl⟩ : syracuseStep 316391 = 474587) B474587
theorem B709775 : Blo 207808 709775 := bstep (se 1 (by rfl) ⟨532331, by rfl⟩ : syracuseStep 709775 = 1064663) B1064663
theorem B316649 : Blo 207808 316649 := bstep (se 2 (by rfl) ⟨118743, by rfl⟩ : syracuseStep 316649 = 237487) B237487
theorem B316703 : Blo 207808 316703 := bstep (se 1 (by rfl) ⟨237527, by rfl⟩ : syracuseStep 316703 = 475055) B475055
theorem B447943 : Blo 207808 447943 := bstep (se 1 (by rfl) ⟨335957, by rfl⟩ : syracuseStep 447943 = 671915) B671915
theorem B316871 : Blo 207808 316871 := bstep (se 1 (by rfl) ⟨237653, by rfl⟩ : syracuseStep 316871 = 475307) B475307
theorem B317225 : Blo 207808 317225 := bstep (se 2 (by rfl) ⟨118959, by rfl⟩ : syracuseStep 317225 = 237919) B237919
theorem B317231 : Blo 207808 317231 := bstep (se 1 (by rfl) ⟨237923, by rfl⟩ : syracuseStep 317231 = 475847) B475847
theorem B1792043 : Blo 207808 1792043 := bstep (se 1 (by rfl) ⟨1344032, by rfl⟩ : syracuseStep 1792043 = 2688065) B2688065
theorem B284891 : Blo 207808 284891 := bstep (se 1 (by rfl) ⟨213668, by rfl⟩ : syracuseStep 284891 = 427337) B427337
theorem B710909 : Blo 207808 710909 := bstep (se 3 (by rfl) ⟨133295, by rfl⟩ : syracuseStep 710909 = 266591) B266591
theorem B1005833 : Blo 207808 1005833 := bstep (se 2 (by rfl) ⟨377187, by rfl⟩ : syracuseStep 1005833 = 754375) B754375
theorem B317705 : Blo 207808 317705 := bstep (se 2 (by rfl) ⟨119139, by rfl⟩ : syracuseStep 317705 = 238279) B238279
theorem B1071791 : Blo 207808 1071791 := bstep (se 1 (by rfl) ⟨803843, by rfl⟩ : syracuseStep 1071791 = 1607687) B1607687
theorem B285481 : Blo 207808 285481 := bstep (se 2 (by rfl) ⟨107055, by rfl⟩ : syracuseStep 285481 = 214111) B214111
theorem B1072115 : Blo 207808 1072115 := bstep (se 1 (by rfl) ⟨804086, by rfl⟩ : syracuseStep 1072115 = 1608173) B1608173
theorem B711719 : Blo 207808 711719 := bstep (se 1 (by rfl) ⟨533789, by rfl⟩ : syracuseStep 711719 = 1067579) B1067579
theorem B5790937 : Blo 207808 5790937 := bstep (se 2 (by rfl) ⟨2171601, by rfl⟩ : syracuseStep 5790937 = 4343203) B4343203
theorem B1007063 : Blo 207808 1007063 := bstep (se 1 (by rfl) ⟨755297, by rfl⟩ : syracuseStep 1007063 = 1510595) B1510595
theorem B712151 : Blo 207808 712151 := bstep (se 1 (by rfl) ⟨534113, by rfl⟩ : syracuseStep 712151 = 1068227) B1068227
theorem B351931 : Blo 207808 351931 := bstep (se 1 (by rfl) ⟨263948, by rfl⟩ : syracuseStep 351931 = 527897) B527897
theorem B6086663 : Blo 207808 6086663 := bstep (se 1 (by rfl) ⟨4564997, by rfl⟩ : syracuseStep 6086663 = 9129995) B9129995
theorem B1794707 : Blo 207808 1794707 := bstep (se 1 (by rfl) ⟨1346030, by rfl⟩ : syracuseStep 1794707 = 2692061) B2692061
theorem B352991 : Blo 207808 352991 := bstep (se 1 (by rfl) ⟨264743, by rfl⟩ : syracuseStep 352991 = 529487) B529487
theorem B451681 : Blo 207808 451681 := bstep (se 2 (by rfl) ⟨169380, by rfl⟩ : syracuseStep 451681 = 338761) B338761
theorem B713825 : Blo 207808 713825 := bstep (se 2 (by rfl) ⟨267684, by rfl⟩ : syracuseStep 713825 = 535369) B535369
theorem B353423 : Blo 207808 353423 := bstep (se 1 (by rfl) ⟨265067, by rfl⟩ : syracuseStep 353423 = 530135) B530135
theorem B353659 : Blo 207808 353659 := bstep (se 1 (by rfl) ⟨265244, by rfl⟩ : syracuseStep 353659 = 530489) B530489
theorem B223655 : Blo 207808 223655 := bstep (se 1 (by rfl) ⟨167741, by rfl⟩ : syracuseStep 223655 = 335483) B335483
theorem B1599911 : Blo 207808 1599911 := bstep (se 1 (by rfl) ⟨1199933, by rfl⟩ : syracuseStep 1599911 = 2399867) B2399867
theorem B486059 : Blo 207808 486059 := bstep (se 1 (by rfl) ⟨364544, by rfl⟩ : syracuseStep 486059 = 729089) B729089
theorem B355151 : Blo 207808 355151 := bstep (se 1 (by rfl) ⟨266363, by rfl⟩ : syracuseStep 355151 = 532727) B532727
theorem B978425 : Blo 207808 978425 := bstep (se 2 (by rfl) ⟨366909, by rfl⟩ : syracuseStep 978425 = 733819) B733819
theorem B356143 : Blo 207808 356143 := bstep (se 1 (by rfl) ⟨267107, by rfl⟩ : syracuseStep 356143 = 534215) B534215
theorem B7991297 : Blo 207808 7991297 := bstep (se 2 (by rfl) ⟨2996736, by rfl⟩ : syracuseStep 7991297 = 5993473) B5993473
theorem B3502081 : Blo 207808 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B421993 : Blo 207808 421993 := bstep (se 2 (by rfl) ⟨158247, by rfl⟩ : syracuseStep 421993 = 316495) B316495
theorem B225703 : Blo 207808 225703 := bstep (se 1 (by rfl) ⟨169277, by rfl⟩ : syracuseStep 225703 = 338555) B338555
theorem B5763565 : Blo 207808 5763565 := bstep (se 3 (by rfl) ⟨1080668, by rfl⟩ : syracuseStep 5763565 = 2161337) B2161337
theorem B2224691 : Blo 207808 2224691 := bstep (se 1 (by rfl) ⟨1668518, by rfl⟩ : syracuseStep 2224691 = 3337037) B3337037
theorem B1930027 : Blo 207808 1930027 := bstep (se 1 (by rfl) ⟨1447520, by rfl⟩ : syracuseStep 1930027 = 2895041) B2895041
theorem B1504109 : Blo 207808 1504109 := bstep (se 3 (by rfl) ⟨282020, by rfl⟩ : syracuseStep 1504109 = 564041) B564041
theorem B1143845 : Blo 207808 1143845 := bstep (se 4 (by rfl) ⟨107235, by rfl⟩ : syracuseStep 1143845 = 214471) B214471
theorem B1012985 : Blo 207808 1012985 := bstep (se 2 (by rfl) ⟨379869, by rfl⟩ : syracuseStep 1012985 = 759739) B759739
theorem B8189207 : Blo 207808 8189207 := bstep (se 1 (by rfl) ⟨6141905, by rfl⟩ : syracuseStep 8189207 = 12283811) B12283811
theorem B226811 : Blo 207808 226811 := bstep (se 1 (by rfl) ⟨170108, by rfl⟩ : syracuseStep 226811 = 340217) B340217
theorem B1013255 : Blo 207808 1013255 := bstep (se 1 (by rfl) ⟨759941, by rfl⟩ : syracuseStep 1013255 = 1519883) B1519883
theorem B5142629 : Blo 207808 5142629 := bstep (se 4 (by rfl) ⟨482121, by rfl⟩ : syracuseStep 5142629 = 964243) B964243
theorem B4291145 : Blo 207808 4291145 := bstep (se 2 (by rfl) ⟨1609179, by rfl⟩ : syracuseStep 4291145 = 3218359) B3218359
theorem B916561 : Blo 207808 916561 := bstep (se 2 (by rfl) ⟨343710, by rfl⟩ : syracuseStep 916561 = 687421) B687421
theorem B1604771 : Blo 207808 1604771 := bstep (se 1 (by rfl) ⟨1203578, by rfl⟩ : syracuseStep 1604771 = 2407157) B2407157
theorem B851267 : Blo 207808 851267 := bstep (se 1 (by rfl) ⟨638450, by rfl⟩ : syracuseStep 851267 = 1276901) B1276901
theorem B18677765 : Blo 207808 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B2031641 : Blo 207808 2031641 := bstep (se 2 (by rfl) ⟨761865, by rfl⟩ : syracuseStep 2031641 = 1523731) B1523731
theorem B3244313 : Blo 207808 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B754895 : Blo 207808 754895 := bstep (se 1 (by rfl) ⟨566171, by rfl⟩ : syracuseStep 754895 = 1132343) B1132343
theorem B722515 : Blo 207808 722515 := bstep (se 1 (by rfl) ⟨541886, by rfl⟩ : syracuseStep 722515 = 1083773) B1083773
theorem B1443439 : Blo 207808 1443439 := bstep (se 1 (by rfl) ⟨1082579, by rfl⟩ : syracuseStep 1443439 = 2165159) B2165159
theorem B1476407 : Blo 207808 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B263999 : Blo 207808 263999 := bstep (se 1 (by rfl) ⟨197999, by rfl⟩ : syracuseStep 263999 = 395999) B395999
theorem B1804139 : Blo 207808 1804139 := bstep (se 1 (by rfl) ⟨1353104, by rfl⟩ : syracuseStep 1804139 = 2706209) B2706209
theorem B395255 : Blo 207808 395255 := bstep (se 1 (by rfl) ⟨296441, by rfl⟩ : syracuseStep 395255 = 592883) B592883
theorem B9635861 : Blo 207808 9635861 := bstep (se 6 (by rfl) ⟨225840, by rfl⟩ : syracuseStep 9635861 = 451681) B451681
theorem B526571 : Blo 207808 526571 := bstep (se 1 (by rfl) ⟨394928, by rfl⟩ : syracuseStep 526571 = 789857) B789857
theorem B592267 : Blo 207808 592267 := bstep (se 1 (by rfl) ⟨444200, by rfl⟩ : syracuseStep 592267 = 888401) B888401
theorem B4000265 : Blo 207808 4000265 := bstep (se 2 (by rfl) ⟨1500099, by rfl⟩ : syracuseStep 4000265 = 3000199) B3000199
theorem B592859 : Blo 207808 592859 := bstep (se 1 (by rfl) ⟨444644, by rfl⟩ : syracuseStep 592859 = 889289) B889289
theorem B396409 : Blo 207808 396409 := bstep (se 2 (by rfl) ⟨148653, by rfl⟩ : syracuseStep 396409 = 297307) B297307
theorem B1445053 : Blo 207808 1445053 := bstep (se 3 (by rfl) ⟨270947, by rfl⟩ : syracuseStep 1445053 = 541895) B541895
theorem B34639163 : Blo 207808 34639163 := bstep (se 1 (by rfl) ⟨25979372, by rfl⟩ : syracuseStep 34639163 = 51958745) B51958745
theorem B396713 : Blo 207808 396713 := bstep (se 2 (by rfl) ⟨148767, by rfl⟩ : syracuseStep 396713 = 297535) B297535
theorem B1510825 : Blo 207808 1510825 := bstep (se 2 (by rfl) ⟨566559, by rfl⟩ : syracuseStep 1510825 = 1133119) B1133119
theorem B527867 : Blo 207808 527867 := bstep (se 1 (by rfl) ⟨395900, by rfl⟩ : syracuseStep 527867 = 791801) B791801
theorem B5738165 : Blo 207808 5738165 := bstep (se 5 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 5738165 = 537953) B537953
theorem B2199653 : Blo 207808 2199653 := bstep (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) B412435
theorem B528889 : Blo 207808 528889 := bstep (se 2 (by rfl) ⟨198333, by rfl⟩ : syracuseStep 528889 = 396667) B396667
theorem B529193 : Blo 207808 529193 := bstep (se 2 (by rfl) ⟨198447, by rfl⟩ : syracuseStep 529193 = 396895) B396895
theorem B1184807 : Blo 207808 1184807 := bstep (se 1 (by rfl) ⟨888605, by rfl⟩ : syracuseStep 1184807 = 1777211) B1777211
theorem B398611 : Blo 207808 398611 := bstep (se 1 (by rfl) ⟨298958, by rfl⟩ : syracuseStep 398611 = 597917) B597917
theorem B267887 : Blo 207808 267887 := bstep (se 1 (by rfl) ⟨200915, by rfl⟩ : syracuseStep 267887 = 401831) B401831
theorem B267943 : Blo 207808 267943 := bstep (se 1 (by rfl) ⟨200957, by rfl⟩ : syracuseStep 267943 = 401915) B401915
theorem B4888325 : Blo 207808 4888325 := bstep (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) B916561
theorem B235327 : Blo 207808 235327 := bstep (se 1 (by rfl) ⟨176495, by rfl⟩ : syracuseStep 235327 = 352991) B352991
theorem B595775 : Blo 207808 595775 := bstep (se 1 (by rfl) ⟨446831, by rfl⟩ : syracuseStep 595775 = 893663) B893663
theorem B300937 : Blo 207808 300937 := bstep (se 2 (by rfl) ⟨112851, by rfl⟩ : syracuseStep 300937 = 225703) B225703
theorem B759709 : Blo 207808 759709 := bstep (se 3 (by rfl) ⟨142445, by rfl⟩ : syracuseStep 759709 = 284891) B284891
theorem B235615 : Blo 207808 235615 := bstep (se 1 (by rfl) ⟨176711, by rfl⟩ : syracuseStep 235615 = 353423) B353423
theorem B1808513 : Blo 207808 1808513 := bstep (se 2 (by rfl) ⟨678192, by rfl⟩ : syracuseStep 1808513 = 1356385) B1356385
theorem B1185947 : Blo 207808 1185947 := bstep (se 1 (by rfl) ⟨889460, by rfl⟩ : syracuseStep 1185947 = 1778921) B1778921
theorem B596231 : Blo 207808 596231 := bstep (se 1 (by rfl) ⟨447173, by rfl⟩ : syracuseStep 596231 = 894347) B894347
theorem B596413 : Blo 207808 596413 := bstep (se 3 (by rfl) ⟨111827, by rfl⟩ : syracuseStep 596413 = 223655) B223655
theorem B21142037 : Blo 207808 21142037 := bstep (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) B991033
theorem B596983 : Blo 207808 596983 := bstep (se 1 (by rfl) ⟨447737, by rfl⟩ : syracuseStep 596983 = 895475) B895475
theorem B334919 : Blo 207808 334919 := bstep (se 1 (by rfl) ⟨251189, by rfl⟩ : syracuseStep 334919 = 502379) B502379
theorem B236767 : Blo 207808 236767 := bstep (se 1 (by rfl) ⟨177575, by rfl⟩ : syracuseStep 236767 = 355151) B355151
theorem B597257 : Blo 207808 597257 := bstep (se 2 (by rfl) ⟨223971, by rfl⟩ : syracuseStep 597257 = 447943) B447943
theorem B5775731 : Blo 207808 5775731 := bstep (se 1 (by rfl) ⟨4331798, by rfl⟩ : syracuseStep 5775731 = 8663597) B8663597
theorem B1483127 : Blo 207808 1483127 := bstep (se 1 (by rfl) ⟨1112345, by rfl⟩ : syracuseStep 1483127 = 2224691) B2224691
theorem B1057211 : Blo 207808 1057211 := bstep (se 1 (by rfl) ⟨792908, by rfl⟩ : syracuseStep 1057211 = 1585817) B1585817
theorem B2695751 : Blo 207808 2695751 := bstep (se 1 (by rfl) ⟨2021813, by rfl⟩ : syracuseStep 2695751 = 4043627) B4043627
theorem B762563 : Blo 207808 762563 := bstep (se 1 (by rfl) ⟨571922, by rfl⟩ : syracuseStep 762563 = 1143845) B1143845
theorem B2270045 : Blo 207808 2270045 := bstep (se 3 (by rfl) ⟨425633, by rfl⟩ : syracuseStep 2270045 = 851267) B851267
theorem B468395 : Blo 207808 468395 := bstep (se 1 (by rfl) ⟨351296, by rfl⟩ : syracuseStep 468395 = 702593) B702593
theorem B796175 : Blo 207808 796175 := bstep (se 1 (by rfl) ⟨597131, by rfl⟩ : syracuseStep 796175 = 1194263) B1194263
theorem B468647 : Blo 207808 468647 := bstep (se 1 (by rfl) ⟨351485, by rfl⟩ : syracuseStep 468647 = 702971) B702971
theorem B534235 : Blo 207808 534235 := bstep (se 1 (by rfl) ⟨400676, by rfl⟩ : syracuseStep 534235 = 801353) B801353
theorem B2860763 : Blo 207808 2860763 := bstep (se 1 (by rfl) ⟨2145572, by rfl⟩ : syracuseStep 2860763 = 4291145) B4291145
theorem B468935 : Blo 207808 468935 := bstep (se 1 (by rfl) ⟨351701, by rfl⟩ : syracuseStep 468935 = 703403) B703403
theorem B469241 : Blo 207808 469241 := bstep (se 2 (by rfl) ⟨175965, by rfl⟩ : syracuseStep 469241 = 351931) B351931
theorem B469295 : Blo 207808 469295 := bstep (se 1 (by rfl) ⟨351971, by rfl⟩ : syracuseStep 469295 = 703943) B703943
theorem B469511 : Blo 207808 469511 := bstep (se 1 (by rfl) ⟨352133, by rfl⟩ : syracuseStep 469511 = 704267) B704267
theorem B469691 : Blo 207808 469691 := bstep (se 1 (by rfl) ⟨352268, by rfl⟩ : syracuseStep 469691 = 704537) B704537
theorem B305975 : Blo 207808 305975 := bstep (se 1 (by rfl) ⟨229481, by rfl⟩ : syracuseStep 305975 = 458963) B458963
theorem B1616699 : Blo 207808 1616699 := bstep (se 1 (by rfl) ⟨1212524, by rfl⟩ : syracuseStep 1616699 = 2425049) B2425049
theorem B1059803 : Blo 207808 1059803 := bstep (se 1 (by rfl) ⟨794852, by rfl⟩ : syracuseStep 1059803 = 1589705) B1589705
theorem B535531 : Blo 207808 535531 := bstep (se 1 (by rfl) ⟨401648, by rfl⟩ : syracuseStep 535531 = 803297) B803297
theorem B207919 : Blo 207808 207919 := bstep (se 1 (by rfl) ⟨155939, by rfl⟩ : syracuseStep 207919 = 311879) B311879
theorem B207943 : Blo 207808 207943 := bstep (se 1 (by rfl) ⟨155957, by rfl⟩ : syracuseStep 207943 = 311915) B311915
theorem B535673 : Blo 207808 535673 := bstep (se 2 (by rfl) ⟨200877, by rfl⟩ : syracuseStep 535673 = 401755) B401755
theorem B208095 : Blo 207808 208095 := bstep (se 1 (by rfl) ⟨156071, by rfl⟩ : syracuseStep 208095 = 312143) B312143
theorem B4533515 : Blo 207808 4533515 := bstep (se 1 (by rfl) ⟨3400136, by rfl⟩ : syracuseStep 4533515 = 6800273) B6800273
theorem B3419435 : Blo 207808 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B208359 : Blo 207808 208359 := bstep (se 1 (by rfl) ⟨156269, by rfl⟩ : syracuseStep 208359 = 312539) B312539
theorem B470519 : Blo 207808 470519 := bstep (se 1 (by rfl) ⟨352889, by rfl⟩ : syracuseStep 470519 = 705779) B705779
theorem B470591 : Blo 207808 470591 := bstep (se 1 (by rfl) ⟨352943, by rfl⟩ : syracuseStep 470591 = 705887) B705887
theorem B208475 : Blo 207808 208475 := bstep (se 1 (by rfl) ⟨156356, by rfl⟩ : syracuseStep 208475 = 312713) B312713
theorem B568939 : Blo 207808 568939 := bstep (se 1 (by rfl) ⟨426704, by rfl⟩ : syracuseStep 568939 = 853409) B853409
theorem B208711 : Blo 207808 208711 := bstep (se 1 (by rfl) ⟨156533, by rfl⟩ : syracuseStep 208711 = 313067) B313067
theorem B667531 : Blo 207808 667531 := bstep (se 1 (by rfl) ⟨500648, by rfl⟩ : syracuseStep 667531 = 1001297) B1001297
theorem B798619 : Blo 207808 798619 := bstep (se 1 (by rfl) ⟨598964, by rfl⟩ : syracuseStep 798619 = 1197929) B1197929
theorem B602063 : Blo 207808 602063 := bstep (se 1 (by rfl) ⟨451547, by rfl⟩ : syracuseStep 602063 = 903095) B903095
theorem B208863 : Blo 207808 208863 := bstep (se 1 (by rfl) ⟨156647, by rfl⟩ : syracuseStep 208863 = 313295) B313295
theorem B209127 : Blo 207808 209127 := bstep (se 1 (by rfl) ⟨156845, by rfl⟩ : syracuseStep 209127 = 313691) B313691
theorem B209279 : Blo 207808 209279 := bstep (se 1 (by rfl) ⟨156959, by rfl⟩ : syracuseStep 209279 = 313919) B313919
theorem B209359 : Blo 207808 209359 := bstep (se 1 (by rfl) ⟨157019, by rfl⟩ : syracuseStep 209359 = 314039) B314039
theorem B471545 : Blo 207808 471545 := bstep (se 2 (by rfl) ⟨176829, by rfl⟩ : syracuseStep 471545 = 353659) B353659
theorem B471635 : Blo 207808 471635 := bstep (se 1 (by rfl) ⟨353726, by rfl⟩ : syracuseStep 471635 = 707453) B707453
theorem B209511 : Blo 207808 209511 := bstep (se 1 (by rfl) ⟨157133, by rfl⟩ : syracuseStep 209511 = 314267) B314267
theorem B471815 : Blo 207808 471815 := bstep (se 1 (by rfl) ⟨353861, by rfl⟩ : syracuseStep 471815 = 707723) B707723
theorem B209775 : Blo 207808 209775 := bstep (se 1 (by rfl) ⟨157331, by rfl⟩ : syracuseStep 209775 = 314663) B314663
theorem B209831 : Blo 207808 209831 := bstep (se 1 (by rfl) ⟨157373, by rfl⟩ : syracuseStep 209831 = 314747) B314747
theorem B2700215 : Blo 207808 2700215 := bstep (se 1 (by rfl) ⟨2025161, by rfl⟩ : syracuseStep 2700215 = 4050323) B4050323
theorem B4010957 : Blo 207808 4010957 := bstep (se 3 (by rfl) ⟨752054, by rfl⟩ : syracuseStep 4010957 = 1504109) B1504109
theorem B209915 : Blo 207808 209915 := bstep (se 1 (by rfl) ⟨157436, by rfl⟩ : syracuseStep 209915 = 314873) B314873
theorem B209983 : Blo 207808 209983 := bstep (se 1 (by rfl) ⟨157487, by rfl⟩ : syracuseStep 209983 = 314975) B314975
theorem B701513 : Blo 207808 701513 := bstep (se 2 (by rfl) ⟨263067, by rfl⟩ : syracuseStep 701513 = 526135) B526135
theorem B210127 : Blo 207808 210127 := bstep (se 1 (by rfl) ⟨157595, by rfl⟩ : syracuseStep 210127 = 315191) B315191
theorem B2012435 : Blo 207808 2012435 := bstep (se 1 (by rfl) ⟨1509326, by rfl⟩ : syracuseStep 2012435 = 3018653) B3018653
theorem B210331 : Blo 207808 210331 := bstep (se 1 (by rfl) ⟨157748, by rfl⟩ : syracuseStep 210331 = 315497) B315497
theorem B18068993 : Blo 207808 18068993 := bstep (se 2 (by rfl) ⟨6775872, by rfl⟩ : syracuseStep 18068993 = 13551745) B13551745
theorem B210543 : Blo 207808 210543 := bstep (se 1 (by rfl) ⟨157907, by rfl⟩ : syracuseStep 210543 = 315815) B315815
theorem B210599 : Blo 207808 210599 := bstep (se 1 (by rfl) ⟨157949, by rfl⟩ : syracuseStep 210599 = 315899) B315899
theorem B210683 : Blo 207808 210683 := bstep (se 1 (by rfl) ⟨158012, by rfl⟩ : syracuseStep 210683 = 316025) B316025
theorem B210719 : Blo 207808 210719 := bstep (se 1 (by rfl) ⟨158039, by rfl⟩ : syracuseStep 210719 = 316079) B316079
theorem B1062719 : Blo 207808 1062719 := bstep (se 1 (by rfl) ⟨797039, by rfl⟩ : syracuseStep 1062719 = 1594079) B1594079
theorem B472895 : Blo 207808 472895 := bstep (se 1 (by rfl) ⟨354671, by rfl⟩ : syracuseStep 472895 = 709343) B709343
theorem B210751 : Blo 207808 210751 := bstep (se 1 (by rfl) ⟨158063, by rfl⟩ : syracuseStep 210751 = 316127) B316127
theorem B210927 : Blo 207808 210927 := bstep (se 1 (by rfl) ⟨158195, by rfl⟩ : syracuseStep 210927 = 316391) B316391
theorem B473183 : Blo 207808 473183 := bstep (se 1 (by rfl) ⟨354887, by rfl⟩ : syracuseStep 473183 = 709775) B709775
theorem B374939 : Blo 207808 374939 := bstep (se 1 (by rfl) ⟨281204, by rfl⟩ : syracuseStep 374939 = 562409) B562409
theorem B211099 : Blo 207808 211099 := bstep (se 1 (by rfl) ⟨158324, by rfl⟩ : syracuseStep 211099 = 316649) B316649
theorem B211135 : Blo 207808 211135 := bstep (se 1 (by rfl) ⟨158351, by rfl⟩ : syracuseStep 211135 = 316703) B316703
theorem B211247 : Blo 207808 211247 := bstep (se 1 (by rfl) ⟨158435, by rfl⟩ : syracuseStep 211247 = 316871) B316871
theorem B211483 : Blo 207808 211483 := bstep (se 1 (by rfl) ⟨158612, by rfl⟩ : syracuseStep 211483 = 317225) B317225
theorem B211487 : Blo 207808 211487 := bstep (se 1 (by rfl) ⟨158615, by rfl⟩ : syracuseStep 211487 = 317231) B317231
theorem B703133 : Blo 207808 703133 := bstep (se 3 (by rfl) ⟨131837, by rfl⟩ : syracuseStep 703133 = 263675) B263675
theorem B604829 : Blo 207808 604829 := bstep (se 3 (by rfl) ⟨113405, by rfl⟩ : syracuseStep 604829 = 226811) B226811
theorem B1194695 : Blo 207808 1194695 := bstep (se 1 (by rfl) ⟨896021, by rfl⟩ : syracuseStep 1194695 = 1792043) B1792043
theorem B473939 : Blo 207808 473939 := bstep (se 1 (by rfl) ⟨355454, by rfl⟩ : syracuseStep 473939 = 710909) B710909
theorem B670555 : Blo 207808 670555 := bstep (se 1 (by rfl) ⟨502916, by rfl⟩ : syracuseStep 670555 = 1005833) B1005833
theorem B211803 : Blo 207808 211803 := bstep (se 1 (by rfl) ⟨158852, by rfl⟩ : syracuseStep 211803 = 317705) B317705
theorem B703457 : Blo 207808 703457 := bstep (se 2 (by rfl) ⟨263796, by rfl⟩ : syracuseStep 703457 = 527593) B527593
theorem B703673 : Blo 207808 703673 := bstep (se 2 (by rfl) ⟨263877, by rfl⟩ : syracuseStep 703673 = 527755) B527755
theorem B507145 : Blo 207808 507145 := bstep (se 2 (by rfl) ⟨190179, by rfl⟩ : syracuseStep 507145 = 380359) B380359
theorem B474479 : Blo 207808 474479 := bstep (se 1 (by rfl) ⟨355859, by rfl⟩ : syracuseStep 474479 = 711719) B711719
theorem B671375 : Blo 207808 671375 := bstep (se 1 (by rfl) ⟨503531, by rfl⟩ : syracuseStep 671375 = 1007063) B1007063
theorem B474767 : Blo 207808 474767 := bstep (se 1 (by rfl) ⟨356075, by rfl⟩ : syracuseStep 474767 = 712151) B712151
theorem B474857 : Blo 207808 474857 := bstep (se 2 (by rfl) ⟨178071, by rfl⟩ : syracuseStep 474857 = 356143) B356143
theorem B1687553 : Blo 207808 1687553 := bstep (se 2 (by rfl) ⟨632832, by rfl⟩ : syracuseStep 1687553 = 1265665) B1265665
theorem B1818713 : Blo 207808 1818713 := bstep (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) B1364035
theorem B1196471 : Blo 207808 1196471 := bstep (se 1 (by rfl) ⟨897353, by rfl⟩ : syracuseStep 1196471 = 1794707) B1794707
theorem B311759 : Blo 207808 311759 := bstep (se 1 (by rfl) ⟨233819, by rfl⟩ : syracuseStep 311759 = 467639) B467639
theorem B311801 : Blo 207808 311801 := bstep (se 2 (by rfl) ⟨116925, by rfl⟩ : syracuseStep 311801 = 233851) B233851
theorem B2867723 : Blo 207808 2867723 := bstep (se 1 (by rfl) ⟨2150792, by rfl⟩ : syracuseStep 2867723 = 4301585) B4301585
theorem B311903 : Blo 207808 311903 := bstep (se 1 (by rfl) ⟨233927, by rfl⟩ : syracuseStep 311903 = 467855) B467855
theorem B705131 : Blo 207808 705131 := bstep (se 1 (by rfl) ⟨528848, by rfl⟩ : syracuseStep 705131 = 1057697) B1057697
theorem B7684753 : Blo 207808 7684753 := bstep (se 2 (by rfl) ⟨2881782, by rfl⟩ : syracuseStep 7684753 = 5763565) B5763565
theorem B475883 : Blo 207808 475883 := bstep (se 1 (by rfl) ⟨356912, by rfl⟩ : syracuseStep 475883 = 713825) B713825
theorem B2573369 : Blo 207808 2573369 := bstep (se 2 (by rfl) ⟨965013, by rfl⟩ : syracuseStep 2573369 = 1930027) B1930027
theorem B312383 : Blo 207808 312383 := bstep (se 1 (by rfl) ⟨234287, by rfl⟩ : syracuseStep 312383 = 468575) B468575
theorem B312425 : Blo 207808 312425 := bstep (se 2 (by rfl) ⟨117159, by rfl⟩ : syracuseStep 312425 = 234319) B234319
theorem B705725 : Blo 207808 705725 := bstep (se 3 (by rfl) ⟨132323, by rfl⟩ : syracuseStep 705725 = 264647) B264647
theorem B312527 : Blo 207808 312527 := bstep (se 1 (by rfl) ⟨234395, by rfl⟩ : syracuseStep 312527 = 468791) B468791
theorem B1230083 : Blo 207808 1230083 := bstep (se 1 (by rfl) ⟨922562, by rfl⟩ : syracuseStep 1230083 = 1845125) B1845125
theorem B902411 : Blo 207808 902411 := bstep (se 1 (by rfl) ⟨676808, by rfl⟩ : syracuseStep 902411 = 1353617) B1353617
theorem B312731 : Blo 207808 312731 := bstep (se 1 (by rfl) ⟨234548, by rfl⟩ : syracuseStep 312731 = 469097) B469097
theorem B1066607 : Blo 207808 1066607 := bstep (se 1 (by rfl) ⟨799955, by rfl⟩ : syracuseStep 1066607 = 1599911) B1599911
theorem B312953 : Blo 207808 312953 := bstep (se 2 (by rfl) ⟨117357, by rfl⟩ : syracuseStep 312953 = 234715) B234715
theorem B378587 : Blo 207808 378587 := bstep (se 1 (by rfl) ⟨283940, by rfl⟩ : syracuseStep 378587 = 567881) B567881
theorem B313055 : Blo 207808 313055 := bstep (se 1 (by rfl) ⟨234791, by rfl⟩ : syracuseStep 313055 = 469583) B469583
theorem B1296157 : Blo 207808 1296157 := bstep (se 3 (by rfl) ⟨243029, by rfl⟩ : syracuseStep 1296157 = 486059) B486059
theorem B313151 : Blo 207808 313151 := bstep (se 1 (by rfl) ⟨234863, by rfl⟩ : syracuseStep 313151 = 469727) B469727
theorem B313319 : Blo 207808 313319 := bstep (se 1 (by rfl) ⟨234989, by rfl⟩ : syracuseStep 313319 = 469979) B469979
theorem B313337 : Blo 207808 313337 := bstep (se 2 (by rfl) ⟨117501, by rfl⟩ : syracuseStep 313337 = 235003) B235003
theorem B313439 : Blo 207808 313439 := bstep (se 1 (by rfl) ⟨235079, by rfl⟩ : syracuseStep 313439 = 470159) B470159
theorem B313499 : Blo 207808 313499 := bstep (se 1 (by rfl) ⟨235124, by rfl⟩ : syracuseStep 313499 = 470249) B470249
theorem B313535 : Blo 207808 313535 := bstep (se 1 (by rfl) ⟨235151, by rfl⟩ : syracuseStep 313535 = 470303) B470303
theorem B706751 : Blo 207808 706751 := bstep (se 1 (by rfl) ⟨530063, by rfl⟩ : syracuseStep 706751 = 1060127) B1060127
theorem B313577 : Blo 207808 313577 := bstep (se 2 (by rfl) ⟨117591, by rfl⟩ : syracuseStep 313577 = 235183) B235183
theorem B674041 : Blo 207808 674041 := bstep (se 2 (by rfl) ⟨252765, by rfl⟩ : syracuseStep 674041 = 505531) B505531
theorem B313883 : Blo 207808 313883 := bstep (se 1 (by rfl) ⟨235412, by rfl⟩ : syracuseStep 313883 = 470825) B470825
theorem B313961 : Blo 207808 313961 := bstep (se 2 (by rfl) ⟨117735, by rfl⟩ : syracuseStep 313961 = 235471) B235471
theorem B5327531 : Blo 207808 5327531 := bstep (se 1 (by rfl) ⟨3995648, by rfl⟩ : syracuseStep 5327531 = 7991297) B7991297
theorem B445115 : Blo 207808 445115 := bstep (se 1 (by rfl) ⟨333836, by rfl⟩ : syracuseStep 445115 = 667673) B667673
theorem B5393141 : Blo 207808 5393141 := bstep (se 5 (by rfl) ⟨252803, by rfl⟩ : syracuseStep 5393141 = 505607) B505607
theorem B1068065 : Blo 207808 1068065 := bstep (se 2 (by rfl) ⟨400524, by rfl⟩ : syracuseStep 1068065 = 801049) B801049
theorem B314489 : Blo 207808 314489 := bstep (se 2 (by rfl) ⟨117933, by rfl⟩ : syracuseStep 314489 = 235867) B235867
theorem B314591 : Blo 207808 314591 := bstep (se 1 (by rfl) ⟨235943, by rfl⟩ : syracuseStep 314591 = 471887) B471887
theorem B314633 : Blo 207808 314633 := bstep (se 2 (by rfl) ⟨117987, by rfl⟩ : syracuseStep 314633 = 235975) B235975
theorem B314735 : Blo 207808 314735 := bstep (se 1 (by rfl) ⟨236051, by rfl⟩ : syracuseStep 314735 = 472103) B472103
theorem B314855 : Blo 207808 314855 := bstep (se 1 (by rfl) ⟨236141, by rfl⟩ : syracuseStep 314855 = 472283) B472283
theorem B445943 : Blo 207808 445943 := bstep (se 1 (by rfl) ⟨334457, by rfl⟩ : syracuseStep 445943 = 668915) B668915
theorem B675323 : Blo 207808 675323 := bstep (se 1 (by rfl) ⟨506492, by rfl⟩ : syracuseStep 675323 = 1012985) B1012985
theorem B5459471 : Blo 207808 5459471 := bstep (se 1 (by rfl) ⟨4094603, by rfl⟩ : syracuseStep 5459471 = 8189207) B8189207
theorem B314987 : Blo 207808 314987 := bstep (se 1 (by rfl) ⟨236240, by rfl⟩ : syracuseStep 314987 = 472481) B472481
theorem B675503 : Blo 207808 675503 := bstep (se 1 (by rfl) ⟨506627, by rfl⟩ : syracuseStep 675503 = 1013255) B1013255
theorem B380641 : Blo 207808 380641 := bstep (se 2 (by rfl) ⟨142740, by rfl⟩ : syracuseStep 380641 = 285481) B285481
theorem B315113 : Blo 207808 315113 := bstep (se 2 (by rfl) ⟨118167, by rfl⟩ : syracuseStep 315113 = 236335) B236335
theorem B708371 : Blo 207808 708371 := bstep (se 1 (by rfl) ⟨531278, by rfl⟩ : syracuseStep 708371 = 1062557) B1062557
theorem B315257 : Blo 207808 315257 := bstep (se 2 (by rfl) ⟨118221, by rfl⟩ : syracuseStep 315257 = 236443) B236443
theorem B315359 : Blo 207808 315359 := bstep (se 1 (by rfl) ⟨236519, by rfl⟩ : syracuseStep 315359 = 473039) B473039
theorem B1069037 : Blo 207808 1069037 := bstep (se 3 (by rfl) ⟨200444, by rfl⟩ : syracuseStep 1069037 = 400889) B400889
theorem B3428419 : Blo 207808 3428419 := bstep (se 1 (by rfl) ⟨2571314, by rfl⟩ : syracuseStep 3428419 = 5142629) B5142629
theorem B315611 : Blo 207808 315611 := bstep (se 1 (by rfl) ⟨236708, by rfl⟩ : syracuseStep 315611 = 473417) B473417
theorem B315623 : Blo 207808 315623 := bstep (se 1 (by rfl) ⟨236717, by rfl⟩ : syracuseStep 315623 = 473435) B473435
theorem B7721249 : Blo 207808 7721249 := bstep (se 2 (by rfl) ⟨2895468, by rfl⟩ : syracuseStep 7721249 = 5790937) B5790937
theorem B315785 : Blo 207808 315785 := bstep (se 2 (by rfl) ⟨118419, by rfl⟩ : syracuseStep 315785 = 236839) B236839
theorem B315881 : Blo 207808 315881 := bstep (se 2 (by rfl) ⟨118455, by rfl⟩ : syracuseStep 315881 = 236911) B236911
theorem B316007 : Blo 207808 316007 := bstep (se 1 (by rfl) ⟨237005, by rfl⟩ : syracuseStep 316007 = 474011) B474011
theorem B709235 : Blo 207808 709235 := bstep (se 1 (by rfl) ⟨531926, by rfl⟩ : syracuseStep 709235 = 1063853) B1063853
theorem B316139 : Blo 207808 316139 := bstep (se 1 (by rfl) ⟨237104, by rfl⟩ : syracuseStep 316139 = 474209) B474209
theorem B316169 : Blo 207808 316169 := bstep (se 2 (by rfl) ⟨118563, by rfl⟩ : syracuseStep 316169 = 237127) B237127
theorem B1069847 : Blo 207808 1069847 := bstep (se 1 (by rfl) ⟨802385, by rfl⟩ : syracuseStep 1069847 = 1604771) B1604771
theorem B316271 : Blo 207808 316271 := bstep (se 1 (by rfl) ⟨237203, by rfl⟩ : syracuseStep 316271 = 474407) B474407
theorem B709505 : Blo 207808 709505 := bstep (se 2 (by rfl) ⟨266064, by rfl⟩ : syracuseStep 709505 = 532129) B532129
theorem B676937 : Blo 207808 676937 := bstep (se 2 (by rfl) ⟨253851, by rfl⟩ : syracuseStep 676937 = 507703) B507703
theorem B316523 : Blo 207808 316523 := bstep (se 1 (by rfl) ⟨237392, by rfl⟩ : syracuseStep 316523 = 474785) B474785
theorem B316763 : Blo 207808 316763 := bstep (se 1 (by rfl) ⟨237572, by rfl⟩ : syracuseStep 316763 = 475145) B475145
theorem B1004987 : Blo 207808 1004987 := bstep (se 1 (by rfl) ⟨753740, by rfl⟩ : syracuseStep 1004987 = 1507481) B1507481
theorem B317039 : Blo 207808 317039 := bstep (se 1 (by rfl) ⟨237779, by rfl⟩ : syracuseStep 317039 = 475559) B475559
theorem B1595051 : Blo 207808 1595051 := bstep (se 1 (by rfl) ⟨1196288, by rfl⟩ : syracuseStep 1595051 = 2392577) B2392577
theorem B710315 : Blo 207808 710315 := bstep (se 1 (by rfl) ⟨532736, by rfl⟩ : syracuseStep 710315 = 1065473) B1065473
theorem B317111 : Blo 207808 317111 := bstep (se 1 (by rfl) ⟨237833, by rfl⟩ : syracuseStep 317111 = 475667) B475667
theorem B317147 : Blo 207808 317147 := bstep (se 1 (by rfl) ⟨237860, by rfl⟩ : syracuseStep 317147 = 475721) B475721
theorem B2250629 : Blo 207808 2250629 := bstep (se 4 (by rfl) ⟨210996, by rfl⟩ : syracuseStep 2250629 = 421993) B421993
theorem B317321 : Blo 207808 317321 := bstep (se 2 (by rfl) ⟨118995, by rfl⟩ : syracuseStep 317321 = 237991) B237991
theorem B710639 : Blo 207808 710639 := bstep (se 1 (by rfl) ⟨532979, by rfl⟩ : syracuseStep 710639 = 1065959) B1065959
theorem B317423 : Blo 207808 317423 := bstep (se 1 (by rfl) ⟨238067, by rfl⟩ : syracuseStep 317423 = 476135) B476135
theorem B710855 : Blo 207808 710855 := bstep (se 1 (by rfl) ⟨533141, by rfl⟩ : syracuseStep 710855 = 1066283) B1066283
theorem B448745 : Blo 207808 448745 := bstep (se 2 (by rfl) ⟨168279, by rfl⟩ : syracuseStep 448745 = 336559) B336559
theorem B317675 : Blo 207808 317675 := bstep (se 1 (by rfl) ⟨238256, by rfl⟩ : syracuseStep 317675 = 476513) B476513
theorem B1071467 : Blo 207808 1071467 := bstep (se 1 (by rfl) ⟨803600, by rfl⟩ : syracuseStep 1071467 = 1607201) B1607201
theorem B2709883 : Blo 207808 2709883 := bstep (se 1 (by rfl) ⟨2032412, by rfl⟩ : syracuseStep 2709883 = 4064825) B4064825
theorem B17160659 : Blo 207808 17160659 := bstep (se 1 (by rfl) ⟨12870494, by rfl⟩ : syracuseStep 17160659 = 25740989) B25740989
theorem B5691977 : Blo 207808 5691977 := bstep (se 2 (by rfl) ⟨2134491, by rfl⟩ : syracuseStep 5691977 = 4268983) B4268983
theorem B711503 : Blo 207808 711503 := bstep (se 1 (by rfl) ⟨533627, by rfl⟩ : syracuseStep 711503 = 1067255) B1067255
theorem B1071953 : Blo 207808 1071953 := bstep (se 2 (by rfl) ⟨401982, by rfl⟩ : syracuseStep 1071953 = 803965) B803965
theorem B351067 : Blo 207808 351067 := bstep (se 1 (by rfl) ⟨263300, by rfl⟩ : syracuseStep 351067 = 526601) B526601
theorem B1006739 : Blo 207808 1006739 := bstep (se 1 (by rfl) ⟨755054, by rfl⟩ : syracuseStep 1006739 = 1510109) B1510109
theorem B711827 : Blo 207808 711827 := bstep (se 1 (by rfl) ⟨533870, by rfl⟩ : syracuseStep 711827 = 1067741) B1067741
theorem B712097 : Blo 207808 712097 := bstep (se 2 (by rfl) ⟨267036, by rfl⟩ : syracuseStep 712097 = 534073) B534073
theorem B253415 : Blo 207808 253415 := bstep (se 1 (by rfl) ⟨190061, by rfl⟩ : syracuseStep 253415 = 380123) B380123
theorem B1400399 : Blo 207808 1400399 := bstep (se 1 (by rfl) ⟨1050299, by rfl⟩ : syracuseStep 1400399 = 2100599) B2100599
theorem B352039 : Blo 207808 352039 := bstep (se 1 (by rfl) ⟨264029, by rfl⟩ : syracuseStep 352039 = 528059) B528059
theorem B712637 : Blo 207808 712637 := bstep (se 3 (by rfl) ⟨133619, by rfl⟩ : syracuseStep 712637 = 267239) B267239
theorem B4284515 : Blo 207808 4284515 := bstep (se 1 (by rfl) ⟨3213386, by rfl⟩ : syracuseStep 4284515 = 6426773) B6426773
theorem B1073533 : Blo 207808 1073533 := bstep (se 3 (by rfl) ⟨201287, by rfl⟩ : syracuseStep 1073533 = 402575) B402575
theorem B353065 : Blo 207808 353065 := bstep (se 2 (by rfl) ⟨132399, by rfl⟩ : syracuseStep 353065 = 264799) B264799
theorem B222203 : Blo 207808 222203 := bstep (se 1 (by rfl) ⟨166652, by rfl⟩ : syracuseStep 222203 = 333305) B333305
theorem B353335 : Blo 207808 353335 := bstep (se 1 (by rfl) ⟨265001, by rfl⟩ : syracuseStep 353335 = 530003) B530003
theorem B1205927 : Blo 207808 1205927 := bstep (se 1 (by rfl) ⟨904445, by rfl⟩ : syracuseStep 1205927 = 1808891) B1808891
theorem B714527 : Blo 207808 714527 := bstep (se 1 (by rfl) ⟨535895, by rfl⟩ : syracuseStep 714527 = 1071791) B1071791
theorem B354287 : Blo 207808 354287 := bstep (se 1 (by rfl) ⟨265715, by rfl⟩ : syracuseStep 354287 = 531431) B531431
theorem B714743 : Blo 207808 714743 := bstep (se 1 (by rfl) ⟨536057, by rfl⟩ : syracuseStep 714743 = 1072115) B1072115
theorem B1927397 : Blo 207808 1927397 := bstep (se 4 (by rfl) ⟨180693, by rfl⟩ : syracuseStep 1927397 = 361387) B361387
theorem B2844953 : Blo 207808 2844953 := bstep (se 2 (by rfl) ⟨1066857, by rfl⟩ : syracuseStep 2844953 = 2133715) B2133715
theorem B10971449 : Blo 207808 10971449 := bstep (se 2 (by rfl) ⟨4114293, by rfl⟩ : syracuseStep 10971449 = 8228587) B8228587
theorem B354847 : Blo 207808 354847 := bstep (se 1 (by rfl) ⟨266135, by rfl⟩ : syracuseStep 354847 = 532271) B532271
theorem B4057775 : Blo 207808 4057775 := bstep (se 1 (by rfl) ⟨3043331, by rfl⟩ : syracuseStep 4057775 = 6086663) B6086663
theorem B355279 : Blo 207808 355279 := bstep (se 1 (by rfl) ⟨266459, by rfl⟩ : syracuseStep 355279 = 532919) B532919
theorem B1010987 : Blo 207808 1010987 := bstep (se 1 (by rfl) ⟨758240, by rfl⟩ : syracuseStep 1010987 = 1516481) B1516481
theorem B356015 : Blo 207808 356015 := bstep (se 1 (by rfl) ⟨267011, by rfl⟩ : syracuseStep 356015 = 534023) B534023
theorem B356251 : Blo 207808 356251 := bstep (se 1 (by rfl) ⟨267188, by rfl⟩ : syracuseStep 356251 = 534377) B534377
theorem B749519 : Blo 207808 749519 := bstep (se 1 (by rfl) ⟨562139, by rfl⟩ : syracuseStep 749519 = 1124279) B1124279
theorem B356663 : Blo 207808 356663 := bstep (se 1 (by rfl) ⟨267497, by rfl⟩ : syracuseStep 356663 = 534995) B534995
theorem B652283 : Blo 207808 652283 := bstep (se 1 (by rfl) ⟨489212, by rfl⟩ : syracuseStep 652283 = 978425) B978425
theorem B357481 : Blo 207808 357481 := bstep (se 2 (by rfl) ⟨134055, by rfl⟩ : syracuseStep 357481 = 268111) B268111
theorem B2389661 : Blo 207808 2389661 := bstep (se 3 (by rfl) ⟨448061, by rfl⟩ : syracuseStep 2389661 = 896123) B896123
theorem B358391 : Blo 207808 358391 := bstep (se 1 (by rfl) ⟨268793, by rfl⟩ : syracuseStep 358391 = 537587) B537587
theorem B5340653 : Blo 207808 5340653 := bstep (se 3 (by rfl) ⟨1001372, by rfl⟩ : syracuseStep 5340653 = 2002745) B2002745
theorem B458473 : Blo 207808 458473 := bstep (se 2 (by rfl) ⟨171927, by rfl⟩ : syracuseStep 458473 = 343855) B343855
theorem B360347 : Blo 207808 360347 := bstep (se 1 (by rfl) ⟨270260, by rfl⟩ : syracuseStep 360347 = 540521) B540521
theorem B12451843 : Blo 207808 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B2162875 : Blo 207808 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B4849901 : Blo 207808 4849901 := bstep (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) B1818713
theorem B820055 : Blo 207808 820055 := bstep (se 1 (by rfl) ⟨615041, by rfl⟩ : syracuseStep 820055 = 1230083) B1230083
theorem B263503 : Blo 207808 263503 := bstep (se 1 (by rfl) ⟨197627, by rfl⟩ : syracuseStep 263503 = 395255) B395255
theorem B6423907 : Blo 207808 6423907 := bstep (se 1 (by rfl) ⟨4817930, by rfl⟩ : syracuseStep 6423907 = 9635861) B9635861
theorem B264475 : Blo 207808 264475 := bstep (se 1 (by rfl) ⟨198356, by rfl⟩ : syracuseStep 264475 = 396713) B396713
theorem B3639647 : Blo 207808 3639647 := bstep (se 1 (by rfl) ⟨2729735, by rfl⟩ : syracuseStep 3639647 = 5459471) B5459471
theorem B592541 : Blo 207808 592541 := bstep (se 3 (by rfl) ⟨111101, by rfl⟩ : syracuseStep 592541 = 222203) B222203
theorem B1805165 : Blo 207808 1805165 := bstep (se 3 (by rfl) ⟨338468, by rfl⟩ : syracuseStep 1805165 = 676937) B676937
theorem B789689 : Blo 207808 789689 := bstep (se 2 (by rfl) ⟨296133, by rfl⟩ : syracuseStep 789689 = 592267) B592267
theorem B789871 : Blo 207808 789871 := bstep (se 1 (by rfl) ⟨592403, by rfl⟩ : syracuseStep 789871 = 1184807) B1184807
theorem B790631 : Blo 207808 790631 := bstep (se 1 (by rfl) ⟨592973, by rfl⟩ : syracuseStep 790631 = 1185947) B1185947
theorem B528545 : Blo 207808 528545 := bstep (se 2 (by rfl) ⟨198204, by rfl⟩ : syracuseStep 528545 = 396409) B396409
theorem B397487 : Blo 207808 397487 := bstep (se 1 (by rfl) ⟨298115, by rfl⟩ : syracuseStep 397487 = 596231) B596231
theorem B11440439 : Blo 207808 11440439 := bstep (se 1 (by rfl) ⟨8580329, by rfl⟩ : syracuseStep 11440439 = 17160659) B17160659
theorem B14094691 : Blo 207808 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B758585 : Blo 207808 758585 := bstep (se 2 (by rfl) ⟨284469, by rfl⟩ : syracuseStep 758585 = 568939) B568939
theorem B3937085 : Blo 207808 3937085 := bstep (se 3 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 3937085 = 1476407) B1476407
theorem B398171 : Blo 207808 398171 := bstep (se 1 (by rfl) ⟨298628, by rfl⟩ : syracuseStep 398171 = 597257) B597257
theorem B890041 : Blo 207808 890041 := bstep (se 2 (by rfl) ⟨333765, by rfl⟩ : syracuseStep 890041 = 667531) B667531
theorem B955709 : Blo 207808 955709 := bstep (se 3 (by rfl) ⟨179195, by rfl⟩ : syracuseStep 955709 = 358391) B358391
theorem B2856343 : Blo 207808 2856343 := bstep (se 1 (by rfl) ⟨2142257, by rfl⟩ : syracuseStep 2856343 = 4284515) B4284515
theorem B988751 : Blo 207808 988751 := bstep (se 1 (by rfl) ⟨741563, by rfl⟩ : syracuseStep 988751 = 1483127) B1483127
theorem B1513363 : Blo 207808 1513363 := bstep (se 1 (by rfl) ⟨1135022, by rfl⟩ : syracuseStep 1513363 = 2270045) B2270045
theorem B530783 : Blo 207808 530783 := bstep (se 1 (by rfl) ⟨398087, by rfl⟩ : syracuseStep 530783 = 796175) B796175
theorem B236191 : Blo 207808 236191 := bstep (se 1 (by rfl) ⟨177143, by rfl⟩ : syracuseStep 236191 = 354287) B354287
theorem B1284931 : Blo 207808 1284931 := bstep (se 1 (by rfl) ⟨963698, by rfl⟩ : syracuseStep 1284931 = 1927397) B1927397
theorem B7314299 : Blo 207808 7314299 := bstep (se 1 (by rfl) ⟨5485724, by rfl⟩ : syracuseStep 7314299 = 10971449) B10971449
theorem B531481 : Blo 207808 531481 := bstep (se 2 (by rfl) ⟨199305, by rfl⟩ : syracuseStep 531481 = 398611) B398611
theorem B1186973 : Blo 207808 1186973 := bstep (se 3 (by rfl) ⟨222557, by rfl⟩ : syracuseStep 1186973 = 445115) B445115
theorem B3022343 : Blo 207808 3022343 := bstep (se 1 (by rfl) ⟨2266757, by rfl⟩ : syracuseStep 3022343 = 4533515) B4533515
theorem B237343 : Blo 207808 237343 := bstep (se 1 (by rfl) ⟨178007, by rfl⟩ : syracuseStep 237343 = 356015) B356015
theorem B401249 : Blo 207808 401249 := bstep (se 2 (by rfl) ⟨150468, by rfl⟩ : syracuseStep 401249 = 300937) B300937
theorem B1580957 : Blo 207808 1580957 := bstep (se 3 (by rfl) ⟨296429, by rfl⟩ : syracuseStep 1580957 = 592859) B592859
theorem B499679 : Blo 207808 499679 := bstep (se 1 (by rfl) ⟨374759, by rfl⟩ : syracuseStep 499679 = 749519) B749519
theorem B401375 : Blo 207808 401375 := bstep (se 1 (by rfl) ⟨301031, by rfl⟩ : syracuseStep 401375 = 602063) B602063
theorem B237775 : Blo 207808 237775 := bstep (se 1 (by rfl) ⟨178331, by rfl⟩ : syracuseStep 237775 = 356663) B356663
theorem B3613177 : Blo 207808 3613177 := bstep (se 2 (by rfl) ⟨1354941, by rfl⟩ : syracuseStep 3613177 = 2709883) B2709883
theorem B795217 : Blo 207808 795217 := bstep (se 2 (by rfl) ⟨298206, by rfl⟩ : syracuseStep 795217 = 596413) B596413
theorem B434855 : Blo 207808 434855 := bstep (se 1 (by rfl) ⟨326141, by rfl⟩ : syracuseStep 434855 = 652283) B652283
theorem B467675 : Blo 207808 467675 := bstep (se 1 (by rfl) ⟨350756, by rfl⟩ : syracuseStep 467675 = 701513) B701513
theorem B9118493 : Blo 207808 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B468089 : Blo 207808 468089 := bstep (se 2 (by rfl) ⟨175533, by rfl⟩ : syracuseStep 468089 = 351067) B351067
theorem B894073 : Blo 207808 894073 := bstep (se 2 (by rfl) ⟨335277, by rfl⟩ : syracuseStep 894073 = 670555) B670555
theorem B1189181 : Blo 207808 1189181 := bstep (se 3 (by rfl) ⟨222971, by rfl⟩ : syracuseStep 1189181 = 445943) B445943
theorem B795977 : Blo 207808 795977 := bstep (se 2 (by rfl) ⟨298491, by rfl⟩ : syracuseStep 795977 = 596983) B596983
theorem B468755 : Blo 207808 468755 := bstep (se 1 (by rfl) ⟨351566, by rfl⟩ : syracuseStep 468755 = 703133) B703133
theorem B403219 : Blo 207808 403219 := bstep (se 1 (by rfl) ⟨302414, by rfl⟩ : syracuseStep 403219 = 604829) B604829
theorem B796463 : Blo 207808 796463 := bstep (se 1 (by rfl) ⟨597347, by rfl⟩ : syracuseStep 796463 = 1194695) B1194695
theorem B468971 : Blo 207808 468971 := bstep (se 1 (by rfl) ⟨351728, by rfl⟩ : syracuseStep 468971 = 703457) B703457
theorem B469115 : Blo 207808 469115 := bstep (se 1 (by rfl) ⟨351836, by rfl⟩ : syracuseStep 469115 = 703673) B703673
theorem B469385 : Blo 207808 469385 := bstep (se 2 (by rfl) ⟨176019, by rfl⟩ : syracuseStep 469385 = 352039) B352039
theorem B960925 : Blo 207808 960925 := bstep (se 3 (by rfl) ⟨180173, by rfl⟩ : syracuseStep 960925 = 360347) B360347
theorem B1125035 : Blo 207808 1125035 := bstep (se 1 (by rfl) ⟨843776, by rfl⟩ : syracuseStep 1125035 = 1687553) B1687553
theorem B1354427 : Blo 207808 1354427 := bstep (se 1 (by rfl) ⟨1015820, by rfl⟩ : syracuseStep 1354427 = 2031641) B2031641
theorem B797647 : Blo 207808 797647 := bstep (se 1 (by rfl) ⟨598235, by rfl⟩ : syracuseStep 797647 = 1196471) B1196471
theorem B207839 : Blo 207808 207839 := bstep (se 1 (by rfl) ⟨155879, by rfl⟩ : syracuseStep 207839 = 311759) B311759
theorem B207867 : Blo 207808 207867 := bstep (se 1 (by rfl) ⟨155900, by rfl⟩ : syracuseStep 207867 = 311801) B311801
theorem B1911815 : Blo 207808 1911815 := bstep (se 1 (by rfl) ⟨1433861, by rfl⟩ : syracuseStep 1911815 = 2867723) B2867723
theorem B207935 : Blo 207808 207935 := bstep (se 1 (by rfl) ⟨155951, by rfl⟩ : syracuseStep 207935 = 311903) B311903
theorem B470087 : Blo 207808 470087 := bstep (se 1 (by rfl) ⟨352565, by rfl⟩ : syracuseStep 470087 = 705131) B705131
theorem B1715579 : Blo 207808 1715579 := bstep (se 1 (by rfl) ⟨1286684, by rfl⟩ : syracuseStep 1715579 = 2573369) B2573369
theorem B208255 : Blo 207808 208255 := bstep (se 1 (by rfl) ⟨156191, by rfl⟩ : syracuseStep 208255 = 312383) B312383
theorem B208283 : Blo 207808 208283 := bstep (se 1 (by rfl) ⟨156212, by rfl⟩ : syracuseStep 208283 = 312425) B312425
theorem B20589997 : Blo 207808 20589997 := bstep (se 3 (by rfl) ⟨3860624, by rfl⟩ : syracuseStep 20589997 = 7721249) B7721249
theorem B470483 : Blo 207808 470483 := bstep (se 1 (by rfl) ⟨352862, by rfl⟩ : syracuseStep 470483 = 705725) B705725
theorem B208351 : Blo 207808 208351 := bstep (se 1 (by rfl) ⟨156263, by rfl⟩ : syracuseStep 208351 = 312527) B312527
theorem B503263 : Blo 207808 503263 := bstep (se 1 (by rfl) ⟨377447, by rfl⟩ : syracuseStep 503263 = 754895) B754895
theorem B601607 : Blo 207808 601607 := bstep (se 1 (by rfl) ⟨451205, by rfl⟩ : syracuseStep 601607 = 902411) B902411
theorem B208487 : Blo 207808 208487 := bstep (se 1 (by rfl) ⟨156365, by rfl⟩ : syracuseStep 208487 = 312731) B312731
theorem B470753 : Blo 207808 470753 := bstep (se 2 (by rfl) ⟨176532, by rfl⟩ : syracuseStep 470753 = 353065) B353065
theorem B208635 : Blo 207808 208635 := bstep (se 1 (by rfl) ⟨156476, by rfl⟩ : syracuseStep 208635 = 312953) B312953
theorem B208703 : Blo 207808 208703 := bstep (se 1 (by rfl) ⟨156527, by rfl⟩ : syracuseStep 208703 = 313055) B313055
theorem B208767 : Blo 207808 208767 := bstep (se 1 (by rfl) ⟨156575, by rfl⟩ : syracuseStep 208767 = 313151) B313151
theorem B208879 : Blo 207808 208879 := bstep (se 1 (by rfl) ⟨156659, by rfl⟩ : syracuseStep 208879 = 313319) B313319
theorem B208891 : Blo 207808 208891 := bstep (se 1 (by rfl) ⟨156668, by rfl⟩ : syracuseStep 208891 = 313337) B313337
theorem B208959 : Blo 207808 208959 := bstep (se 1 (by rfl) ⟨156719, by rfl⟩ : syracuseStep 208959 = 313439) B313439
theorem B471113 : Blo 207808 471113 := bstep (se 2 (by rfl) ⟨176667, by rfl⟩ : syracuseStep 471113 = 353335) B353335
theorem B208999 : Blo 207808 208999 := bstep (se 1 (by rfl) ⟨156749, by rfl⟩ : syracuseStep 208999 = 313499) B313499
theorem B209023 : Blo 207808 209023 := bstep (se 1 (by rfl) ⟨156767, by rfl⟩ : syracuseStep 209023 = 313535) B313535
theorem B471167 : Blo 207808 471167 := bstep (se 1 (by rfl) ⟨353375, by rfl⟩ : syracuseStep 471167 = 706751) B706751
theorem B209051 : Blo 207808 209051 := bstep (se 1 (by rfl) ⟨156788, by rfl⟩ : syracuseStep 209051 = 313577) B313577
theorem B2666843 : Blo 207808 2666843 := bstep (se 1 (by rfl) ⟨2000132, by rfl⟩ : syracuseStep 2666843 = 4000265) B4000265
theorem B209255 : Blo 207808 209255 := bstep (se 1 (by rfl) ⟨156941, by rfl⟩ : syracuseStep 209255 = 313883) B313883
theorem B209307 : Blo 207808 209307 := bstep (se 1 (by rfl) ⟨156980, by rfl⟩ : syracuseStep 209307 = 313961) B313961
theorem B3551687 : Blo 207808 3551687 := bstep (se 1 (by rfl) ⟨2663765, by rfl⟩ : syracuseStep 3551687 = 5327531) B5327531
theorem B209659 : Blo 207808 209659 := bstep (se 1 (by rfl) ⟨157244, by rfl⟩ : syracuseStep 209659 = 314489) B314489
theorem B963353 : Blo 207808 963353 := bstep (se 2 (by rfl) ⟨361257, by rfl⟩ : syracuseStep 963353 = 722515) B722515
theorem B209727 : Blo 207808 209727 := bstep (se 1 (by rfl) ⟨157295, by rfl⟩ : syracuseStep 209727 = 314591) B314591
theorem B209755 : Blo 207808 209755 := bstep (se 1 (by rfl) ⟨157316, by rfl⟩ : syracuseStep 209755 = 314633) B314633
theorem B209823 : Blo 207808 209823 := bstep (se 1 (by rfl) ⟨157367, by rfl⟩ : syracuseStep 209823 = 314735) B314735
theorem B209903 : Blo 207808 209903 := bstep (se 1 (by rfl) ⟨157427, by rfl⟩ : syracuseStep 209903 = 314855) B314855
theorem B209991 : Blo 207808 209991 := bstep (se 1 (by rfl) ⟨157493, by rfl⟩ : syracuseStep 209991 = 314987) B314987
theorem B210075 : Blo 207808 210075 := bstep (se 1 (by rfl) ⟨157556, by rfl⟩ : syracuseStep 210075 = 315113) B315113
theorem B472247 : Blo 207808 472247 := bstep (se 1 (by rfl) ⟨354185, by rfl⟩ : syracuseStep 472247 = 708371) B708371
theorem B210171 : Blo 207808 210171 := bstep (se 1 (by rfl) ⟨157628, by rfl⟩ : syracuseStep 210171 = 315257) B315257
theorem B210239 : Blo 207808 210239 := bstep (se 1 (by rfl) ⟨157679, by rfl⟩ : syracuseStep 210239 = 315359) B315359
theorem B210407 : Blo 207808 210407 := bstep (se 1 (by rfl) ⟨157805, by rfl⟩ : syracuseStep 210407 = 315611) B315611
theorem B210415 : Blo 207808 210415 := bstep (se 1 (by rfl) ⟨157811, by rfl⟩ : syracuseStep 210415 = 315623) B315623
theorem B210523 : Blo 207808 210523 := bstep (se 1 (by rfl) ⟨157892, by rfl⟩ : syracuseStep 210523 = 315785) B315785
theorem B210587 : Blo 207808 210587 := bstep (se 1 (by rfl) ⟨157940, by rfl⟩ : syracuseStep 210587 = 315881) B315881
theorem B898721 : Blo 207808 898721 := bstep (se 2 (by rfl) ⟨337020, by rfl⟩ : syracuseStep 898721 = 674041) B674041
theorem B210671 : Blo 207808 210671 := bstep (se 1 (by rfl) ⟨158003, by rfl⟩ : syracuseStep 210671 = 316007) B316007
theorem B472823 : Blo 207808 472823 := bstep (se 1 (by rfl) ⟨354617, by rfl⟩ : syracuseStep 472823 = 709235) B709235
theorem B210759 : Blo 207808 210759 := bstep (se 1 (by rfl) ⟨158069, by rfl⟩ : syracuseStep 210759 = 316139) B316139
theorem B210779 : Blo 207808 210779 := bstep (se 1 (by rfl) ⟨158084, by rfl⟩ : syracuseStep 210779 = 316169) B316169
theorem B210847 : Blo 207808 210847 := bstep (se 1 (by rfl) ⟨158135, by rfl⟩ : syracuseStep 210847 = 316271) B316271
theorem B473003 : Blo 207808 473003 := bstep (se 1 (by rfl) ⟨354752, by rfl⟩ : syracuseStep 473003 = 709505) B709505
theorem B473129 : Blo 207808 473129 := bstep (se 2 (by rfl) ⟨177423, by rfl⟩ : syracuseStep 473129 = 354847) B354847
theorem B211015 : Blo 207808 211015 := bstep (se 1 (by rfl) ⟨158261, by rfl⟩ : syracuseStep 211015 = 316523) B316523
theorem B211175 : Blo 207808 211175 := bstep (se 1 (by rfl) ⟨158381, by rfl⟩ : syracuseStep 211175 = 316763) B316763
theorem B211359 : Blo 207808 211359 := bstep (se 1 (by rfl) ⟨158519, by rfl⟩ : syracuseStep 211359 = 317039) B317039
theorem B1063367 : Blo 207808 1063367 := bstep (se 1 (by rfl) ⟨797525, by rfl⟩ : syracuseStep 1063367 = 1595051) B1595051
theorem B473543 : Blo 207808 473543 := bstep (se 1 (by rfl) ⟨355157, by rfl⟩ : syracuseStep 473543 = 710315) B710315
theorem B211407 : Blo 207808 211407 := bstep (se 1 (by rfl) ⟨158555, by rfl⟩ : syracuseStep 211407 = 317111) B317111
theorem B211431 : Blo 207808 211431 := bstep (se 1 (by rfl) ⟨158573, by rfl⟩ : syracuseStep 211431 = 317147) B317147
theorem B3258883 : Blo 207808 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B211547 : Blo 207808 211547 := bstep (se 1 (by rfl) ⟨158660, by rfl⟩ : syracuseStep 211547 = 317321) B317321
theorem B473705 : Blo 207808 473705 := bstep (se 2 (by rfl) ⟨177639, by rfl⟩ : syracuseStep 473705 = 355279) B355279
theorem B473759 : Blo 207808 473759 := bstep (se 1 (by rfl) ⟨355319, by rfl⟩ : syracuseStep 473759 = 710639) B710639
theorem B211615 : Blo 207808 211615 := bstep (se 1 (by rfl) ⟨158711, by rfl⟩ : syracuseStep 211615 = 317423) B317423
theorem B473903 : Blo 207808 473903 := bstep (se 1 (by rfl) ⟨355427, by rfl⟩ : syracuseStep 473903 = 710855) B710855
theorem B211783 : Blo 207808 211783 := bstep (se 1 (by rfl) ⟨158837, by rfl⟩ : syracuseStep 211783 = 317675) B317675
theorem B474335 : Blo 207808 474335 := bstep (se 1 (by rfl) ⟨355751, by rfl⟩ : syracuseStep 474335 = 711503) B711503
theorem B2014433 : Blo 207808 2014433 := bstep (se 2 (by rfl) ⟨755412, by rfl⟩ : syracuseStep 2014433 = 1510825) B1510825
theorem B671159 : Blo 207808 671159 := bstep (se 1 (by rfl) ⟨503369, by rfl⟩ : syracuseStep 671159 = 1006739) B1006739
theorem B474551 : Blo 207808 474551 := bstep (se 1 (by rfl) ⟨355913, by rfl⟩ : syracuseStep 474551 = 711827) B711827
theorem B703997 : Blo 207808 703997 := bstep (se 3 (by rfl) ⟨131999, by rfl⟩ : syracuseStep 703997 = 263999) B263999
theorem B1588733 : Blo 207808 1588733 := bstep (se 3 (by rfl) ⟨297887, by rfl⟩ : syracuseStep 1588733 = 595775) B595775
theorem B474731 : Blo 207808 474731 := bstep (se 1 (by rfl) ⟨356048, by rfl⟩ : syracuseStep 474731 = 712097) B712097
theorem B507521 : Blo 207808 507521 := bstep (se 2 (by rfl) ⟨190320, by rfl⟩ : syracuseStep 507521 = 380641) B380641
theorem B933599 : Blo 207808 933599 := bstep (se 1 (by rfl) ⟨700199, by rfl⟩ : syracuseStep 933599 = 1400399) B1400399
theorem B1064825 : Blo 207808 1064825 := bstep (se 2 (by rfl) ⟨399309, by rfl⟩ : syracuseStep 1064825 = 798619) B798619
theorem B475001 : Blo 207808 475001 := bstep (se 2 (by rfl) ⟨178125, by rfl⟩ : syracuseStep 475001 = 356251) B356251
theorem B475091 : Blo 207808 475091 := bstep (se 1 (by rfl) ⟨356318, by rfl⟩ : syracuseStep 475091 = 712637) B712637
theorem B4571225 : Blo 207808 4571225 := bstep (se 2 (by rfl) ⟨1714209, by rfl⟩ : syracuseStep 4571225 = 3428419) B3428419
theorem B3850487 : Blo 207808 3850487 := bstep (se 1 (by rfl) ⟨2887865, by rfl⟩ : syracuseStep 3850487 = 5775731) B5775731
theorem B704807 : Blo 207808 704807 := bstep (se 1 (by rfl) ⟨528605, by rfl⟩ : syracuseStep 704807 = 1057211) B1057211
theorem B508375 : Blo 207808 508375 := bstep (se 1 (by rfl) ⟨381281, by rfl⟩ : syracuseStep 508375 = 762563) B762563
theorem B1196653 : Blo 207808 1196653 := bstep (se 3 (by rfl) ⟨224372, by rfl⟩ : syracuseStep 1196653 = 448745) B448745
theorem B705185 : Blo 207808 705185 := bstep (se 2 (by rfl) ⟨264444, by rfl⟩ : syracuseStep 705185 = 528889) B528889
theorem B312263 : Blo 207808 312263 := bstep (se 1 (by rfl) ⟨234197, by rfl⟩ : syracuseStep 312263 = 468395) B468395
theorem B312431 : Blo 207808 312431 := bstep (se 1 (by rfl) ⟨234323, by rfl⟩ : syracuseStep 312431 = 468647) B468647
theorem B803951 : Blo 207808 803951 := bstep (se 1 (by rfl) ⟨602963, by rfl⟩ : syracuseStep 803951 = 1205927) B1205927
theorem B476351 : Blo 207808 476351 := bstep (se 1 (by rfl) ⟨357263, by rfl⟩ : syracuseStep 476351 = 714527) B714527
theorem B312623 : Blo 207808 312623 := bstep (se 1 (by rfl) ⟨234467, by rfl⟩ : syracuseStep 312623 = 468935) B468935
theorem B476495 : Blo 207808 476495 := bstep (se 1 (by rfl) ⟨357371, by rfl⟩ : syracuseStep 476495 = 714743) B714743
theorem B476641 : Blo 207808 476641 := bstep (se 2 (by rfl) ⟨178740, by rfl⟩ : syracuseStep 476641 = 357481) B357481
theorem B312827 : Blo 207808 312827 := bstep (se 1 (by rfl) ⟨234620, by rfl⟩ : syracuseStep 312827 = 469241) B469241
theorem B312863 : Blo 207808 312863 := bstep (se 1 (by rfl) ⟨234647, by rfl⟩ : syracuseStep 312863 = 469295) B469295
theorem B313007 : Blo 207808 313007 := bstep (se 1 (by rfl) ⟨234755, by rfl⟩ : syracuseStep 313007 = 469511) B469511
theorem B2705183 : Blo 207808 2705183 := bstep (se 1 (by rfl) ⟨2028887, by rfl⟩ : syracuseStep 2705183 = 4057775) B4057775
theorem B313127 : Blo 207808 313127 := bstep (se 1 (by rfl) ⟨234845, by rfl⟩ : syracuseStep 313127 = 469691) B469691
theorem B706535 : Blo 207808 706535 := bstep (se 1 (by rfl) ⟨529901, by rfl⟩ : syracuseStep 706535 = 1059803) B1059803
theorem B673991 : Blo 207808 673991 := bstep (se 1 (by rfl) ⟨505493, by rfl⟩ : syracuseStep 673991 = 1010987) B1010987
theorem B313679 : Blo 207808 313679 := bstep (se 1 (by rfl) ⟨235259, by rfl⟩ : syracuseStep 313679 = 470519) B470519
theorem B313727 : Blo 207808 313727 := bstep (se 1 (by rfl) ⟨235295, by rfl⟩ : syracuseStep 313727 = 470591) B470591
theorem B313769 : Blo 207808 313769 := bstep (se 2 (by rfl) ⟨117663, by rfl⟩ : syracuseStep 313769 = 235327) B235327
theorem B314153 : Blo 207808 314153 := bstep (se 2 (by rfl) ⟨117807, by rfl⟩ : syracuseStep 314153 = 235615) B235615
theorem B314363 : Blo 207808 314363 := bstep (se 1 (by rfl) ⟨235772, by rfl⟩ : syracuseStep 314363 = 471545) B471545
theorem B314423 : Blo 207808 314423 := bstep (se 1 (by rfl) ⟨235817, by rfl⟩ : syracuseStep 314423 = 471635) B471635
theorem B314543 : Blo 207808 314543 := bstep (se 1 (by rfl) ⟨235907, by rfl⟩ : syracuseStep 314543 = 471815) B471815
theorem B2673971 : Blo 207808 2673971 := bstep (se 1 (by rfl) ⟨2005478, by rfl⟩ : syracuseStep 2673971 = 4010957) B4010957
theorem B12045995 : Blo 207808 12045995 := bstep (se 1 (by rfl) ⟨9034496, by rfl⟩ : syracuseStep 12045995 = 18068993) B18068993
theorem B1593107 : Blo 207808 1593107 := bstep (se 1 (by rfl) ⟨1194830, by rfl⟩ : syracuseStep 1593107 = 2389661) B2389661
theorem B708479 : Blo 207808 708479 := bstep (se 1 (by rfl) ⟨531359, by rfl⟩ : syracuseStep 708479 = 1062719) B1062719
theorem B315263 : Blo 207808 315263 := bstep (se 1 (by rfl) ⟨236447, by rfl⟩ : syracuseStep 315263 = 472895) B472895
theorem B675773 : Blo 207808 675773 := bstep (se 3 (by rfl) ⟨126707, by rfl⟩ : syracuseStep 675773 = 253415) B253415
theorem B315455 : Blo 207808 315455 := bstep (se 1 (by rfl) ⟨236591, by rfl⟩ : syracuseStep 315455 = 473183) B473183
theorem B249959 : Blo 207808 249959 := bstep (se 1 (by rfl) ⟨187469, by rfl⟩ : syracuseStep 249959 = 374939) B374939
theorem B315689 : Blo 207808 315689 := bstep (se 2 (by rfl) ⟨118383, by rfl⟩ : syracuseStep 315689 = 236767) B236767
theorem B676193 : Blo 207808 676193 := bstep (se 2 (by rfl) ⟨253572, by rfl⟩ : syracuseStep 676193 = 507145) B507145
theorem B1790333 : Blo 207808 1790333 := bstep (se 3 (by rfl) ⟨335687, by rfl⟩ : syracuseStep 1790333 = 671375) B671375
theorem B315959 : Blo 207808 315959 := bstep (se 1 (by rfl) ⟨236969, by rfl⟩ : syracuseStep 315959 = 473939) B473939
theorem B4051781 : Blo 207808 4051781 := bstep (se 4 (by rfl) ⟨379854, by rfl⟩ : syracuseStep 4051781 = 759709) B759709
theorem B316319 : Blo 207808 316319 := bstep (se 1 (by rfl) ⟨237239, by rfl⟩ : syracuseStep 316319 = 474479) B474479
theorem B611297 : Blo 207808 611297 := bstep (se 2 (by rfl) ⟨229236, by rfl⟩ : syracuseStep 611297 = 458473) B458473
theorem B3560435 : Blo 207808 3560435 := bstep (se 1 (by rfl) ⟨2670326, by rfl⟩ : syracuseStep 3560435 = 5340653) B5340653
theorem B316511 : Blo 207808 316511 := bstep (se 1 (by rfl) ⟨237383, by rfl⟩ : syracuseStep 316511 = 474767) B474767
theorem B316571 : Blo 207808 316571 := bstep (se 1 (by rfl) ⟨237428, by rfl⟩ : syracuseStep 316571 = 474857) B474857
theorem B317255 : Blo 207808 317255 := bstep (se 1 (by rfl) ⟨237941, by rfl⟩ : syracuseStep 317255 = 475883) B475883
theorem B1431377 : Blo 207808 1431377 := bstep (se 2 (by rfl) ⟨536766, by rfl⟩ : syracuseStep 1431377 = 1073533) B1073533
theorem B10246337 : Blo 207808 10246337 := bstep (se 2 (by rfl) ⟨3842376, by rfl⟩ : syracuseStep 10246337 = 7684753) B7684753
theorem B711071 : Blo 207808 711071 := bstep (se 1 (by rfl) ⟨533303, by rfl⟩ : syracuseStep 711071 = 1066607) B1066607
theorem B252391 : Blo 207808 252391 := bstep (se 1 (by rfl) ⟨189293, by rfl⟩ : syracuseStep 252391 = 378587) B378587
theorem B1202759 : Blo 207808 1202759 := bstep (se 1 (by rfl) ⟨902069, by rfl⟩ : syracuseStep 1202759 = 1804139) B1804139
theorem B351047 : Blo 207808 351047 := bstep (se 1 (by rfl) ⟨263285, by rfl⟩ : syracuseStep 351047 = 526571) B526571
theorem B3595427 : Blo 207808 3595427 := bstep (se 1 (by rfl) ⟨2696570, by rfl⟩ : syracuseStep 3595427 = 5393141) B5393141
theorem B712043 : Blo 207808 712043 := bstep (se 1 (by rfl) ⟨534032, by rfl⟩ : syracuseStep 712043 = 1068065) B1068065
theorem B23092775 : Blo 207808 23092775 := bstep (se 1 (by rfl) ⟨17319581, by rfl⟩ : syracuseStep 23092775 = 34639163) B34639163
theorem B712313 : Blo 207808 712313 := bstep (se 2 (by rfl) ⟨267117, by rfl⟩ : syracuseStep 712313 = 534235) B534235
theorem B351911 : Blo 207808 351911 := bstep (se 1 (by rfl) ⟨263933, by rfl⟩ : syracuseStep 351911 = 527867) B527867
theorem B450215 : Blo 207808 450215 := bstep (se 1 (by rfl) ⟨337661, by rfl⟩ : syracuseStep 450215 = 675323) B675323
theorem B1728209 : Blo 207808 1728209 := bstep (se 2 (by rfl) ⟨648078, by rfl⟩ : syracuseStep 1728209 = 1296157) B1296157
theorem B450335 : Blo 207808 450335 := bstep (se 1 (by rfl) ⟨337751, by rfl⟩ : syracuseStep 450335 = 675503) B675503
theorem B3825443 : Blo 207808 3825443 := bstep (se 1 (by rfl) ⟨2869082, by rfl⟩ : syracuseStep 3825443 = 5738165) B5738165
theorem B712691 : Blo 207808 712691 := bstep (se 1 (by rfl) ⟨534518, by rfl⟩ : syracuseStep 712691 = 1069037) B1069037
theorem B1466435 : Blo 207808 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B713231 : Blo 207808 713231 := bstep (se 1 (by rfl) ⟨534923, by rfl⟩ : syracuseStep 713231 = 1069847) B1069847
theorem B352795 : Blo 207808 352795 := bstep (se 1 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 352795 = 529193) B529193
theorem B2679965 : Blo 207808 2679965 := bstep (se 3 (by rfl) ⟨502493, by rfl⟩ : syracuseStep 2679965 = 1004987) B1004987
theorem B1500419 : Blo 207808 1500419 := bstep (se 1 (by rfl) ⟨1125314, by rfl⟩ : syracuseStep 1500419 = 2250629) B2250629
theorem B714041 : Blo 207808 714041 := bstep (se 2 (by rfl) ⟨267765, by rfl⟩ : syracuseStep 714041 = 535531) B535531
theorem B1205675 : Blo 207808 1205675 := bstep (se 1 (by rfl) ⟨904256, by rfl⟩ : syracuseStep 1205675 = 1808513) B1808513
theorem B714311 : Blo 207808 714311 := bstep (se 1 (by rfl) ⟨535733, by rfl⟩ : syracuseStep 714311 = 1071467) B1071467
theorem B1926737 : Blo 207808 1926737 := bstep (se 2 (by rfl) ⟨722526, by rfl⟩ : syracuseStep 1926737 = 1445053) B1445053
theorem B714365 : Blo 207808 714365 := bstep (se 3 (by rfl) ⟨133943, by rfl⟩ : syracuseStep 714365 = 267887) B267887
theorem B3794651 : Blo 207808 3794651 := bstep (se 1 (by rfl) ⟨2845988, by rfl⟩ : syracuseStep 3794651 = 5691977) B5691977
theorem B714635 : Blo 207808 714635 := bstep (se 1 (by rfl) ⟨535976, by rfl⟩ : syracuseStep 714635 = 1071953) B1071953
theorem B7628701 : Blo 207808 7628701 := bstep (se 3 (by rfl) ⟨1430381, by rfl⟩ : syracuseStep 7628701 = 2860763) B2860763
theorem B223279 : Blo 207808 223279 := bstep (se 1 (by rfl) ⟨167459, by rfl⟩ : syracuseStep 223279 = 334919) B334919
theorem B1797167 : Blo 207808 1797167 := bstep (se 1 (by rfl) ⟨1347875, by rfl⟩ : syracuseStep 1797167 = 2695751) B2695751
theorem B1896635 : Blo 207808 1896635 := bstep (se 1 (by rfl) ⟨1422476, by rfl⟩ : syracuseStep 1896635 = 2844953) B2844953
theorem B1077799 : Blo 207808 1077799 := bstep (se 1 (by rfl) ⟨808349, by rfl⟩ : syracuseStep 1077799 = 1616699) B1616699
theorem B357115 : Blo 207808 357115 := bstep (se 1 (by rfl) ⟨267836, by rfl⟩ : syracuseStep 357115 = 535673) B535673
theorem B815933 : Blo 207808 815933 := bstep (se 3 (by rfl) ⟨152987, by rfl⟩ : syracuseStep 815933 = 305975) B305975
theorem B357257 : Blo 207808 357257 := bstep (se 2 (by rfl) ⟨133971, by rfl⟩ : syracuseStep 357257 = 267943) B267943
theorem B7698341 : Blo 207808 7698341 := bstep (se 4 (by rfl) ⟨721719, by rfl⟩ : syracuseStep 7698341 = 1443439) B1443439
theorem B1800143 : Blo 207808 1800143 := bstep (se 1 (by rfl) ⟨1350107, by rfl⟩ : syracuseStep 1800143 = 2700215) B2700215
theorem B1341623 : Blo 207808 1341623 := bstep (se 1 (by rfl) ⟨1006217, by rfl⟩ : syracuseStep 1341623 = 2012435) B2012435
theorem B3047483 : Blo 207808 3047483 := bstep (se 1 (by rfl) ⟨2285612, by rfl⟩ : syracuseStep 3047483 = 4571225) B4571225
theorem B2883833 : Blo 207808 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B4817569 : Blo 207808 4817569 := bstep (se 2 (by rfl) ⟨1806588, by rfl⟩ : syracuseStep 4817569 = 3613177) B3613177
theorem B1803181 : Blo 207808 1803181 := bstep (se 3 (by rfl) ⟨338096, by rfl⟩ : syracuseStep 1803181 = 676193) B676193
theorem B1803455 : Blo 207808 1803455 := bstep (se 1 (by rfl) ⟨1352591, by rfl⟩ : syracuseStep 1803455 = 2705183) B2705183
theorem B2426431 : Blo 207808 2426431 := bstep (se 1 (by rfl) ⟨1819823, by rfl⟩ : syracuseStep 2426431 = 3639647) B3639647
theorem B395027 : Blo 207808 395027 := bstep (se 1 (by rfl) ⟨296270, by rfl⟩ : syracuseStep 395027 = 592541) B592541
theorem B75171685 : Blo 207808 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B526459 : Blo 207808 526459 := bstep (se 1 (by rfl) ⟨394844, by rfl⟩ : syracuseStep 526459 = 789689) B789689
theorem B8030663 : Blo 207808 8030663 := bstep (se 1 (by rfl) ⟨6022997, by rfl⟩ : syracuseStep 8030663 = 12045995) B12045995
theorem B527087 : Blo 207808 527087 := bstep (se 1 (by rfl) ⟨395315, by rfl⟩ : syracuseStep 527087 = 790631) B790631
theorem B1281233 : Blo 207808 1281233 := bstep (se 2 (by rfl) ⟨480462, by rfl⟩ : syracuseStep 1281233 = 960925) B960925
theorem B2624723 : Blo 207808 2624723 := bstep (se 1 (by rfl) ⟨1968542, by rfl⟩ : syracuseStep 2624723 = 3937085) B3937085
theorem B265447 : Blo 207808 265447 := bstep (se 1 (by rfl) ⟨199085, by rfl⟩ : syracuseStep 265447 = 398171) B398171
theorem B659167 : Blo 207808 659167 := bstep (se 1 (by rfl) ⟨494375, by rfl⟩ : syracuseStep 659167 = 988751) B988751
theorem B954251 : Blo 207808 954251 := bstep (se 1 (by rfl) ⟨715688, by rfl⟩ : syracuseStep 954251 = 1431377) B1431377
theorem B1053161 : Blo 207808 1053161 := bstep (se 2 (by rfl) ⟨394935, by rfl⟩ : syracuseStep 1053161 = 789871) B789871
theorem B234031 : Blo 207808 234031 := bstep (se 1 (by rfl) ⟨175523, by rfl⟩ : syracuseStep 234031 = 351047) B351047
theorem B791315 : Blo 207808 791315 := bstep (se 1 (by rfl) ⟨593486, by rfl⟩ : syracuseStep 791315 = 1186973) B1186973
theorem B2396951 : Blo 207808 2396951 := bstep (se 1 (by rfl) ⟨1797713, by rfl⟩ : syracuseStep 2396951 = 3595427) B3595427
theorem B300143 : Blo 207808 300143 := bstep (se 1 (by rfl) ⟨225107, by rfl⟩ : syracuseStep 300143 = 450215) B450215
theorem B234607 : Blo 207808 234607 := bstep (se 1 (by rfl) ⟨175955, by rfl⟩ : syracuseStep 234607 = 351911) B351911
theorem B1152139 : Blo 207808 1152139 := bstep (se 1 (by rfl) ⟨864104, by rfl⟩ : syracuseStep 1152139 = 1728209) B1728209
theorem B300223 : Blo 207808 300223 := bstep (se 1 (by rfl) ⟨225167, by rfl⟩ : syracuseStep 300223 = 450335) B450335
theorem B267499 : Blo 207808 267499 := bstep (se 1 (by rfl) ⟨200624, by rfl⟩ : syracuseStep 267499 = 401249) B401249
theorem B1053971 : Blo 207808 1053971 := bstep (se 1 (by rfl) ⟨790478, by rfl⟩ : syracuseStep 1053971 = 1580957) B1580957
theorem B333119 : Blo 207808 333119 := bstep (se 1 (by rfl) ⟨249839, by rfl⟩ : syracuseStep 333119 = 499679) B499679
theorem B792787 : Blo 207808 792787 := bstep (se 1 (by rfl) ⟨594590, by rfl⟩ : syracuseStep 792787 = 1189181) B1189181
theorem B530651 : Blo 207808 530651 := bstep (se 1 (by rfl) ⟨397988, by rfl⟩ : syracuseStep 530651 = 795977) B795977
theorem B1284491 : Blo 207808 1284491 := bstep (se 1 (by rfl) ⟨963368, by rfl⟩ : syracuseStep 1284491 = 1926737) B1926737
theorem B2529767 : Blo 207808 2529767 := bstep (se 1 (by rfl) ⟨1897325, by rfl⟩ : syracuseStep 2529767 = 3794651) B3794651
theorem B530975 : Blo 207808 530975 := bstep (se 1 (by rfl) ⟨398231, by rfl⟩ : syracuseStep 530975 = 796463) B796463
theorem B1186721 : Blo 207808 1186721 := bstep (se 2 (by rfl) ⟨445020, by rfl⟩ : syracuseStep 1186721 = 890041) B890041
theorem B3808457 : Blo 207808 3808457 := bstep (se 2 (by rfl) ⟨1428171, by rfl⟩ : syracuseStep 3808457 = 2856343) B2856343
theorem B1777895 : Blo 207808 1777895 := bstep (se 1 (by rfl) ⟨1333421, by rfl⟩ : syracuseStep 1777895 = 2666843) B2666843
theorem B2367791 : Blo 207808 2367791 := bstep (se 1 (by rfl) ⟨1775843, by rfl⟩ : syracuseStep 2367791 = 3551687) B3551687
theorem B238171 : Blo 207808 238171 := bstep (se 1 (by rfl) ⟨178628, by rfl⟩ : syracuseStep 238171 = 357257) B357257
theorem B336521 : Blo 207808 336521 := bstep (se 2 (by rfl) ⟨126195, by rfl⟩ : syracuseStep 336521 = 252391) B252391
theorem B1713241 : Blo 207808 1713241 := bstep (se 2 (by rfl) ⟨642465, by rfl⟩ : syracuseStep 1713241 = 1284931) B1284931
theorem B599147 : Blo 207808 599147 := bstep (se 1 (by rfl) ⟨449360, by rfl⟩ : syracuseStep 599147 = 898721) B898721
theorem B894415 : Blo 207808 894415 := bstep (se 1 (by rfl) ⟨670811, by rfl⟩ : syracuseStep 894415 = 1341623) B1341623
theorem B469331 : Blo 207808 469331 := bstep (se 1 (by rfl) ⟨351998, by rfl⟩ : syracuseStep 469331 = 703997) B703997
theorem B1059155 : Blo 207808 1059155 := bstep (se 1 (by rfl) ⟨794366, by rfl⟩ : syracuseStep 1059155 = 1588733) B1588733
theorem B338347 : Blo 207808 338347 := bstep (se 1 (by rfl) ⟨253760, by rfl⟩ : syracuseStep 338347 = 507521) B507521
theorem B2566991 : Blo 207808 2566991 := bstep (se 1 (by rfl) ⟨1925243, by rfl⟩ : syracuseStep 2566991 = 3850487) B3850487
theorem B3910493 : Blo 207808 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B469871 : Blo 207808 469871 := bstep (se 1 (by rfl) ⟨352403, by rfl⟩ : syracuseStep 469871 = 704807) B704807
theorem B1190821 : Blo 207808 1190821 := bstep (se 4 (by rfl) ⟨111639, by rfl⟩ : syracuseStep 1190821 = 223279) B223279
theorem B666557 : Blo 207808 666557 := bstep (se 3 (by rfl) ⟨124979, by rfl⟩ : syracuseStep 666557 = 249959) B249959
theorem B470123 : Blo 207808 470123 := bstep (se 1 (by rfl) ⟨352592, by rfl⟩ : syracuseStep 470123 = 705185) B705185
theorem B1059965 : Blo 207808 1059965 := bstep (se 3 (by rfl) ⟨198743, by rfl⟩ : syracuseStep 1059965 = 397487) B397487
theorem B208175 : Blo 207808 208175 := bstep (se 1 (by rfl) ⟨156131, by rfl⟩ : syracuseStep 208175 = 312263) B312263
theorem B470393 : Blo 207808 470393 := bstep (se 2 (by rfl) ⟨176397, by rfl⟩ : syracuseStep 470393 = 352795) B352795
theorem B208287 : Blo 207808 208287 := bstep (se 1 (by rfl) ⟨156215, by rfl⟩ : syracuseStep 208287 = 312431) B312431
theorem B535967 : Blo 207808 535967 := bstep (se 1 (by rfl) ⟨401975, by rfl⟩ : syracuseStep 535967 = 803951) B803951
theorem B1060289 : Blo 207808 1060289 := bstep (se 2 (by rfl) ⟨397608, by rfl⟩ : syracuseStep 1060289 = 795217) B795217
theorem B208415 : Blo 207808 208415 := bstep (se 1 (by rfl) ⟨156311, by rfl⟩ : syracuseStep 208415 = 312623) B312623
theorem B208551 : Blo 207808 208551 := bstep (se 1 (by rfl) ⟨156413, by rfl⟩ : syracuseStep 208551 = 312827) B312827
theorem B208575 : Blo 207808 208575 := bstep (se 1 (by rfl) ⟨156431, by rfl⟩ : syracuseStep 208575 = 312863) B312863
theorem B208671 : Blo 207808 208671 := bstep (se 1 (by rfl) ⟨156503, by rfl⟩ : syracuseStep 208671 = 313007) B313007
theorem B208751 : Blo 207808 208751 := bstep (se 1 (by rfl) ⟨156563, by rfl⟩ : syracuseStep 208751 = 313127) B313127
theorem B471023 : Blo 207808 471023 := bstep (se 1 (by rfl) ⟨353267, by rfl⟩ : syracuseStep 471023 = 706535) B706535
theorem B1192097 : Blo 207808 1192097 := bstep (se 2 (by rfl) ⟨447036, by rfl⟩ : syracuseStep 1192097 = 894073) B894073
theorem B209119 : Blo 207808 209119 := bstep (se 1 (by rfl) ⟨156839, by rfl⟩ : syracuseStep 209119 = 313679) B313679
theorem B209151 : Blo 207808 209151 := bstep (se 1 (by rfl) ⟨156863, by rfl⟩ : syracuseStep 209151 = 313727) B313727
theorem B209179 : Blo 207808 209179 := bstep (se 1 (by rfl) ⟨156884, by rfl⟩ : syracuseStep 209179 = 313769) B313769
theorem B8565209 : Blo 207808 8565209 := bstep (se 2 (by rfl) ⟨3211953, by rfl⟩ : syracuseStep 8565209 = 6423907) B6423907
theorem B209435 : Blo 207808 209435 := bstep (se 1 (by rfl) ⟨157076, by rfl⟩ : syracuseStep 209435 = 314153) B314153
theorem B635521 : Blo 207808 635521 := bstep (se 2 (by rfl) ⟨238320, by rfl⟩ : syracuseStep 635521 = 476641) B476641
theorem B209575 : Blo 207808 209575 := bstep (se 1 (by rfl) ⟨157181, by rfl⟩ : syracuseStep 209575 = 314363) B314363
theorem B209615 : Blo 207808 209615 := bstep (se 1 (by rfl) ⟨157211, by rfl⟩ : syracuseStep 209615 = 314423) B314423
theorem B2568941 : Blo 207808 2568941 := bstep (se 3 (by rfl) ⟨481676, by rfl⟩ : syracuseStep 2568941 = 963353) B963353
theorem B209695 : Blo 207808 209695 := bstep (se 1 (by rfl) ⟨157271, by rfl⟩ : syracuseStep 209695 = 314543) B314543
theorem B1782647 : Blo 207808 1782647 := bstep (se 1 (by rfl) ⟨1336985, by rfl⟩ : syracuseStep 1782647 = 2673971) B2673971
theorem B537625 : Blo 207808 537625 := bstep (se 2 (by rfl) ⟨201609, by rfl⟩ : syracuseStep 537625 = 403219) B403219
theorem B1062071 : Blo 207808 1062071 := bstep (se 1 (by rfl) ⟨796553, by rfl⟩ : syracuseStep 1062071 = 1593107) B1593107
theorem B10171601 : Blo 207808 10171601 := bstep (se 2 (by rfl) ⟨3814350, by rfl⟩ : syracuseStep 10171601 = 7628701) B7628701
theorem B472319 : Blo 207808 472319 := bstep (se 1 (by rfl) ⟨354239, by rfl⟩ : syracuseStep 472319 = 708479) B708479
theorem B210175 : Blo 207808 210175 := bstep (se 1 (by rfl) ⟨157631, by rfl⟩ : syracuseStep 210175 = 315263) B315263
theorem B210303 : Blo 207808 210303 := bstep (se 1 (by rfl) ⟨157727, by rfl⟩ : syracuseStep 210303 = 315455) B315455
theorem B210459 : Blo 207808 210459 := bstep (se 1 (by rfl) ⟨157844, by rfl⟩ : syracuseStep 210459 = 315689) B315689
theorem B1193555 : Blo 207808 1193555 := bstep (se 1 (by rfl) ⟨895166, by rfl⟩ : syracuseStep 1193555 = 1790333) B1790333
theorem B210639 : Blo 207808 210639 := bstep (se 1 (by rfl) ⟨157979, by rfl⟩ : syracuseStep 210639 = 315959) B315959
theorem B2701187 : Blo 207808 2701187 := bstep (se 1 (by rfl) ⟨2025890, by rfl⟩ : syracuseStep 2701187 = 4051781) B4051781
theorem B210879 : Blo 207808 210879 := bstep (se 1 (by rfl) ⟨158159, by rfl⟩ : syracuseStep 210879 = 316319) B316319
theorem B407531 : Blo 207808 407531 := bstep (se 1 (by rfl) ⟨305648, by rfl⟩ : syracuseStep 407531 = 611297) B611297
theorem B2373623 : Blo 207808 2373623 := bstep (se 1 (by rfl) ⟨1780217, by rfl⟩ : syracuseStep 2373623 = 3560435) B3560435
theorem B211007 : Blo 207808 211007 := bstep (se 1 (by rfl) ⟨158255, by rfl⟩ : syracuseStep 211007 = 316511) B316511
theorem B211047 : Blo 207808 211047 := bstep (se 1 (by rfl) ⟨158285, by rfl⟩ : syracuseStep 211047 = 316571) B316571
theorem B637139 : Blo 207808 637139 := bstep (se 1 (by rfl) ⟨477854, by rfl⟩ : syracuseStep 637139 = 955709) B955709
theorem B211503 : Blo 207808 211503 := bstep (se 1 (by rfl) ⟨158627, by rfl⟩ : syracuseStep 211503 = 317255) B317255
theorem B1063529 : Blo 207808 1063529 := bstep (se 2 (by rfl) ⟨398823, by rfl⟩ : syracuseStep 1063529 = 797647) B797647
theorem B6830891 : Blo 207808 6830891 := bstep (se 1 (by rfl) ⟨5123168, by rfl⟩ : syracuseStep 6830891 = 10246337) B10246337
theorem B474047 : Blo 207808 474047 := bstep (se 1 (by rfl) ⟨355535, by rfl⟩ : syracuseStep 474047 = 711071) B711071
theorem B801839 : Blo 207808 801839 := bstep (se 1 (by rfl) ⟨601379, by rfl⟩ : syracuseStep 801839 = 1202759) B1202759
theorem B671017 : Blo 207808 671017 := bstep (se 2 (by rfl) ⟨251631, by rfl⟩ : syracuseStep 671017 = 503263) B503263
theorem B474695 : Blo 207808 474695 := bstep (se 1 (by rfl) ⟨356021, by rfl⟩ : syracuseStep 474695 = 712043) B712043
theorem B2014895 : Blo 207808 2014895 := bstep (se 1 (by rfl) ⟨1511171, by rfl⟩ : syracuseStep 2014895 = 3022343) B3022343
theorem B474875 : Blo 207808 474875 := bstep (se 1 (by rfl) ⟨356156, by rfl⟩ : syracuseStep 474875 = 712313) B712313
theorem B20528909 : Blo 207808 20528909 := bstep (se 3 (by rfl) ⟨3849170, by rfl⟩ : syracuseStep 20528909 = 7698341) B7698341
theorem B475127 : Blo 207808 475127 := bstep (se 1 (by rfl) ⟨356345, by rfl⟩ : syracuseStep 475127 = 712691) B712691
theorem B475487 : Blo 207808 475487 := bstep (se 1 (by rfl) ⟨356615, by rfl⟩ : syracuseStep 475487 = 713231) B713231
theorem B311783 : Blo 207808 311783 := bstep (se 1 (by rfl) ⟨233837, by rfl⟩ : syracuseStep 311783 = 467675) B467675
theorem B6078995 : Blo 207808 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B312059 : Blo 207808 312059 := bstep (se 1 (by rfl) ⟨234044, by rfl⟩ : syracuseStep 312059 = 468089) B468089
theorem B1786643 : Blo 207808 1786643 := bstep (se 1 (by rfl) ⟨1339982, by rfl⟩ : syracuseStep 1786643 = 2679965) B2679965
theorem B1000279 : Blo 207808 1000279 := bstep (se 1 (by rfl) ⟨750209, by rfl⟩ : syracuseStep 1000279 = 1500419) B1500419
theorem B476027 : Blo 207808 476027 := bstep (se 1 (by rfl) ⟨357020, by rfl⟩ : syracuseStep 476027 = 714041) B714041
theorem B803783 : Blo 207808 803783 := bstep (se 1 (by rfl) ⟨602837, by rfl⟩ : syracuseStep 803783 = 1205675) B1205675
theorem B476153 : Blo 207808 476153 := bstep (se 2 (by rfl) ⟨178557, by rfl⟩ : syracuseStep 476153 = 357115) B357115
theorem B476207 : Blo 207808 476207 := bstep (se 1 (by rfl) ⟨357155, by rfl⟩ : syracuseStep 476207 = 714311) B714311
theorem B476243 : Blo 207808 476243 := bstep (se 1 (by rfl) ⟨357182, by rfl⟩ : syracuseStep 476243 = 714365) B714365
theorem B312503 : Blo 207808 312503 := bstep (se 1 (by rfl) ⟨234377, by rfl⟩ : syracuseStep 312503 = 468755) B468755
theorem B476423 : Blo 207808 476423 := bstep (se 1 (by rfl) ⟨357317, by rfl⟩ : syracuseStep 476423 = 714635) B714635
theorem B312647 : Blo 207808 312647 := bstep (se 1 (by rfl) ⟨234485, by rfl⟩ : syracuseStep 312647 = 468971) B468971
theorem B312743 : Blo 207808 312743 := bstep (se 1 (by rfl) ⟨234557, by rfl⟩ : syracuseStep 312743 = 469115) B469115
theorem B312923 : Blo 207808 312923 := bstep (se 1 (by rfl) ⟨234692, by rfl⟩ : syracuseStep 312923 = 469385) B469385
theorem B902951 : Blo 207808 902951 := bstep (se 1 (by rfl) ⟨677213, by rfl⟩ : syracuseStep 902951 = 1354427) B1354427
theorem B1198111 : Blo 207808 1198111 := bstep (se 1 (by rfl) ⟨898583, by rfl⟩ : syracuseStep 1198111 = 1797167) B1797167
theorem B313391 : Blo 207808 313391 := bstep (se 1 (by rfl) ⟨235043, by rfl⟩ : syracuseStep 313391 = 470087) B470087
theorem B313655 : Blo 207808 313655 := bstep (se 1 (by rfl) ⟨235241, by rfl⟩ : syracuseStep 313655 = 470483) B470483
theorem B313835 : Blo 207808 313835 := bstep (se 1 (by rfl) ⟨235376, by rfl⟩ : syracuseStep 313835 = 470753) B470753
theorem B2017817 : Blo 207808 2017817 := bstep (se 2 (by rfl) ⟨756681, by rfl⟩ : syracuseStep 2017817 = 1513363) B1513363
theorem B314075 : Blo 207808 314075 := bstep (se 1 (by rfl) ⟨235556, by rfl⟩ : syracuseStep 314075 = 471113) B471113
theorem B314111 : Blo 207808 314111 := bstep (se 1 (by rfl) ⟨235583, by rfl⟩ : syracuseStep 314111 = 471167) B471167
theorem B1264423 : Blo 207808 1264423 := bstep (se 1 (by rfl) ⟨948317, by rfl⟩ : syracuseStep 1264423 = 1896635) B1896635
theorem B543955 : Blo 207808 543955 := bstep (se 1 (by rfl) ⟨407966, by rfl⟩ : syracuseStep 543955 = 815933) B815933
theorem B4345177 : Blo 207808 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B314831 : Blo 207808 314831 := bstep (se 1 (by rfl) ⟨236123, by rfl⟩ : syracuseStep 314831 = 472247) B472247
theorem B314921 : Blo 207808 314921 := bstep (se 2 (by rfl) ⟨118095, by rfl⟩ : syracuseStep 314921 = 236191) B236191
theorem B315215 : Blo 207808 315215 := bstep (se 1 (by rfl) ⟨236411, by rfl⟩ : syracuseStep 315215 = 472823) B472823
theorem B315335 : Blo 207808 315335 := bstep (se 1 (by rfl) ⟨236501, by rfl⟩ : syracuseStep 315335 = 473003) B473003
theorem B1200095 : Blo 207808 1200095 := bstep (se 1 (by rfl) ⟨900071, by rfl⟩ : syracuseStep 1200095 = 1800143) B1800143
theorem B315419 : Blo 207808 315419 := bstep (se 1 (by rfl) ⟨236564, by rfl⟩ : syracuseStep 315419 = 473129) B473129
theorem B708641 : Blo 207808 708641 := bstep (se 2 (by rfl) ⟨265740, by rfl⟩ : syracuseStep 708641 = 531481) B531481
theorem B708911 : Blo 207808 708911 := bstep (se 1 (by rfl) ⟨531683, by rfl⟩ : syracuseStep 708911 = 1063367) B1063367
theorem B315695 : Blo 207808 315695 := bstep (se 1 (by rfl) ⟨236771, by rfl⟩ : syracuseStep 315695 = 473543) B473543
theorem B315803 : Blo 207808 315803 := bstep (se 1 (by rfl) ⟨236852, by rfl⟩ : syracuseStep 315803 = 473705) B473705
theorem B315839 : Blo 207808 315839 := bstep (se 1 (by rfl) ⟨236879, by rfl⟩ : syracuseStep 315839 = 473759) B473759
theorem B315935 : Blo 207808 315935 := bstep (se 1 (by rfl) ⟨236951, by rfl⟩ : syracuseStep 315935 = 473903) B473903
theorem B316223 : Blo 207808 316223 := bstep (se 1 (by rfl) ⟨237167, by rfl⟩ : syracuseStep 316223 = 474335) B474335
theorem B447439 : Blo 207808 447439 := bstep (se 1 (by rfl) ⟨335579, by rfl⟩ : syracuseStep 447439 = 671159) B671159
theorem B316367 : Blo 207808 316367 := bstep (se 1 (by rfl) ⟨237275, by rfl⟩ : syracuseStep 316367 = 474551) B474551
theorem B316457 : Blo 207808 316457 := bstep (se 2 (by rfl) ⟨118671, by rfl⟩ : syracuseStep 316457 = 237343) B237343
theorem B316487 : Blo 207808 316487 := bstep (se 1 (by rfl) ⟨237365, by rfl⟩ : syracuseStep 316487 = 474731) B474731
theorem B709883 : Blo 207808 709883 := bstep (se 1 (by rfl) ⟨532412, by rfl⟩ : syracuseStep 709883 = 1064825) B1064825
theorem B316667 : Blo 207808 316667 := bstep (se 1 (by rfl) ⟨237500, by rfl⟩ : syracuseStep 316667 = 475001) B475001
theorem B1070333 : Blo 207808 1070333 := bstep (se 3 (by rfl) ⟨200687, by rfl⟩ : syracuseStep 1070333 = 401375) B401375
theorem B316727 : Blo 207808 316727 := bstep (se 1 (by rfl) ⟨237545, by rfl⟩ : syracuseStep 316727 = 475091) B475091
theorem B16602457 : Blo 207808 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B3233267 : Blo 207808 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B317033 : Blo 207808 317033 := bstep (se 2 (by rfl) ⟨118887, by rfl⟩ : syracuseStep 317033 = 237775) B237775
theorem B317567 : Blo 207808 317567 := bstep (se 1 (by rfl) ⟨238175, by rfl⟩ : syracuseStep 317567 = 476351) B476351
theorem B1595537 : Blo 207808 1595537 := bstep (se 2 (by rfl) ⟨598326, by rfl⟩ : syracuseStep 1595537 = 1196653) B1196653
theorem B317663 : Blo 207808 317663 := bstep (se 1 (by rfl) ⟨238247, by rfl⟩ : syracuseStep 317663 = 476495) B476495
theorem B449327 : Blo 207808 449327 := bstep (se 1 (by rfl) ⟨336995, by rfl⟩ : syracuseStep 449327 = 673991) B673991
theorem B351337 : Blo 207808 351337 := bstep (se 2 (by rfl) ⟨131751, by rfl⟩ : syracuseStep 351337 = 263503) B263503
theorem B1203443 : Blo 207808 1203443 := bstep (se 1 (by rfl) ⟨902582, by rfl⟩ : syracuseStep 1203443 = 1805165) B1805165
theorem B2022893 : Blo 207808 2022893 := bstep (se 3 (by rfl) ⟨379292, by rfl⟩ : syracuseStep 2022893 = 758585) B758585
theorem B2186813 : Blo 207808 2186813 := bstep (se 3 (by rfl) ⟨410027, by rfl⟩ : syracuseStep 2186813 = 820055) B820055
theorem B2711333 : Blo 207808 2711333 := bstep (se 4 (by rfl) ⟨254187, by rfl⟩ : syracuseStep 2711333 = 508375) B508375
theorem B450515 : Blo 207808 450515 := bstep (se 1 (by rfl) ⟨337886, by rfl⟩ : syracuseStep 450515 = 675773) B675773
theorem B352363 : Blo 207808 352363 := bstep (se 1 (by rfl) ⟨264272, by rfl⟩ : syracuseStep 352363 = 528545) B528545
theorem B7626959 : Blo 207808 7626959 := bstep (se 1 (by rfl) ⟨5720219, by rfl⟩ : syracuseStep 7626959 = 11440439) B11440439
theorem B352633 : Blo 207808 352633 := bstep (se 2 (by rfl) ⟨132237, by rfl⟩ : syracuseStep 352633 = 264475) B264475
theorem B353855 : Blo 207808 353855 := bstep (se 1 (by rfl) ⟨265391, by rfl⟩ : syracuseStep 353855 = 530783) B530783
theorem B27453329 : Blo 207808 27453329 := bstep (se 2 (by rfl) ⟨10294998, by rfl⟩ : syracuseStep 27453329 = 20589997) B20589997
theorem B4876199 : Blo 207808 4876199 := bstep (se 1 (by rfl) ⟨3657149, by rfl⟩ : syracuseStep 4876199 = 7314299) B7314299
theorem B15395183 : Blo 207808 15395183 := bstep (se 1 (by rfl) ⟨11546387, by rfl⟩ : syracuseStep 15395183 = 23092775) B23092775
theorem B2550295 : Blo 207808 2550295 := bstep (se 1 (by rfl) ⟨1912721, by rfl⟩ : syracuseStep 2550295 = 3825443) B3825443
theorem B289903 : Blo 207808 289903 := bstep (se 1 (by rfl) ⟨217427, by rfl⟩ : syracuseStep 289903 = 434855) B434855
theorem B1437065 : Blo 207808 1437065 := bstep (se 2 (by rfl) ⟨538899, by rfl⟩ : syracuseStep 1437065 = 1077799) B1077799
theorem B750023 : Blo 207808 750023 := bstep (se 1 (by rfl) ⟨562517, by rfl⟩ : syracuseStep 750023 = 1125035) B1125035
theorem B1274543 : Blo 207808 1274543 := bstep (se 1 (by rfl) ⟨955907, by rfl⟩ : syracuseStep 1274543 = 1911815) B1911815
theorem B1143719 : Blo 207808 1143719 := bstep (se 1 (by rfl) ⟨857789, by rfl⟩ : syracuseStep 1143719 = 1715579) B1715579
theorem B1604285 : Blo 207808 1604285 := bstep (se 3 (by rfl) ⟨300803, by rfl⟩ : syracuseStep 1604285 = 601607) B601607
theorem B1342955 : Blo 207808 1342955 := bstep (se 1 (by rfl) ⟨1007216, by rfl⟩ : syracuseStep 1342955 = 2014433) B2014433
theorem B622399 : Blo 207808 622399 := bstep (se 1 (by rfl) ⟨466799, by rfl⟩ : syracuseStep 622399 = 933599) B933599
theorem B2031655 : Blo 207808 2031655 := bstep (se 1 (by rfl) ⟨1523741, by rfl⟩ : syracuseStep 2031655 = 3047483) B3047483
theorem B6423425 : Blo 207808 6423425 := bstep (se 2 (by rfl) ⟨2408784, by rfl⟩ : syracuseStep 6423425 = 4817569) B4817569
theorem B263351 : Blo 207808 263351 := bstep (se 1 (by rfl) ⟨197513, by rfl⟩ : syracuseStep 263351 = 395027) B395027
theorem B1345211 : Blo 207808 1345211 := bstep (se 1 (by rfl) ⟨1008908, by rfl⟩ : syracuseStep 1345211 = 2017817) B2017817
theorem B854155 : Blo 207808 854155 := bstep (se 1 (by rfl) ⟨640616, by rfl⟩ : syracuseStep 854155 = 1281233) B1281233
theorem B1804517 : Blo 207808 1804517 := bstep (se 4 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 1804517 = 338347) B338347
theorem B527543 : Blo 207808 527543 := bstep (se 1 (by rfl) ⟨395657, by rfl⟩ : syracuseStep 527543 = 791315) B791315
theorem B888317 : Blo 207808 888317 := bstep (se 3 (by rfl) ⟨166559, by rfl⟩ : syracuseStep 888317 = 333119) B333119
theorem B856327 : Blo 207808 856327 := bstep (se 1 (by rfl) ⟨642245, by rfl⟩ : syracuseStep 856327 = 1284491) B1284491
theorem B725273 : Blo 207808 725273 := bstep (se 2 (by rfl) ⟨271977, by rfl⟩ : syracuseStep 725273 = 543955) B543955
theorem B299551 : Blo 207808 299551 := bstep (se 1 (by rfl) ⟨224663, by rfl⟩ : syracuseStep 299551 = 449327) B449327
theorem B791147 : Blo 207808 791147 := bstep (se 1 (by rfl) ⟨593360, by rfl⟩ : syracuseStep 791147 = 1186721) B1186721
theorem B1348595 : Blo 207808 1348595 := bstep (se 1 (by rfl) ⟨1011446, by rfl⟩ : syracuseStep 1348595 = 2022893) B2022893
theorem B1807555 : Blo 207808 1807555 := bstep (se 1 (by rfl) ⟨1355666, by rfl⟩ : syracuseStep 1807555 = 2711333) B2711333
theorem B300343 : Blo 207808 300343 := bstep (se 1 (by rfl) ⟨225257, by rfl⟩ : syracuseStep 300343 = 450515) B450515
theorem B5084639 : Blo 207808 5084639 := bstep (se 1 (by rfl) ⟨3813479, by rfl⟩ : syracuseStep 5084639 = 7626959) B7626959
theorem B1185263 : Blo 207808 1185263 := bstep (se 1 (by rfl) ⟨888947, by rfl⟩ : syracuseStep 1185263 = 1777895) B1777895
theorem B1578527 : Blo 207808 1578527 := bstep (se 1 (by rfl) ⟨1183895, by rfl⟩ : syracuseStep 1578527 = 2367791) B2367791
theorem B399431 : Blo 207808 399431 := bstep (se 1 (by rfl) ⟨299573, by rfl⟩ : syracuseStep 399431 = 599147) B599147
theorem B235903 : Blo 207808 235903 := bstep (se 1 (by rfl) ⟨176927, by rfl⟩ : syracuseStep 235903 = 353855) B353855
theorem B596585 : Blo 207808 596585 := bstep (se 2 (by rfl) ⟨223719, by rfl⟩ : syracuseStep 596585 = 447439) B447439
theorem B3250799 : Blo 207808 3250799 := bstep (se 1 (by rfl) ⟨2438099, by rfl⟩ : syracuseStep 3250799 = 4876199) B4876199
theorem B10263455 : Blo 207808 10263455 := bstep (se 1 (by rfl) ⟨7697591, by rfl⟩ : syracuseStep 10263455 = 15395183) B15395183
theorem B400297 : Blo 207808 400297 := bstep (se 2 (by rfl) ⟨150111, by rfl⟩ : syracuseStep 400297 = 300223) B300223
theorem B958043 : Blo 207808 958043 := bstep (se 1 (by rfl) ⟨718532, by rfl⟩ : syracuseStep 958043 = 1437065) B1437065
theorem B794731 : Blo 207808 794731 := bstep (se 1 (by rfl) ⟨596048, by rfl⟩ : syracuseStep 794731 = 1192097) B1192097
theorem B1057049 : Blo 207808 1057049 := bstep (se 2 (by rfl) ⟨396393, by rfl⟩ : syracuseStep 1057049 = 792787) B792787
theorem B500015 : Blo 207808 500015 := bstep (se 1 (by rfl) ⟨375011, by rfl⟩ : syracuseStep 500015 = 750023) B750023
theorem B5710139 : Blo 207808 5710139 := bstep (se 1 (by rfl) ⟨4282604, by rfl⟩ : syracuseStep 5710139 = 8565209) B8565209
theorem B1712627 : Blo 207808 1712627 := bstep (se 1 (by rfl) ⟨1284470, by rfl⟩ : syracuseStep 1712627 = 2568941) B2568941
theorem B1188431 : Blo 207808 1188431 := bstep (se 1 (by rfl) ⟨891323, by rfl⟩ : syracuseStep 1188431 = 1782647) B1782647
theorem B762479 : Blo 207808 762479 := bstep (se 1 (by rfl) ⟨571859, by rfl⟩ : syracuseStep 762479 = 1143719) B1143719
theorem B795703 : Blo 207808 795703 := bstep (se 1 (by rfl) ⟨596777, by rfl⟩ : syracuseStep 795703 = 1193555) B1193555
theorem B3515557 : Blo 207808 3515557 := bstep (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) B659167
theorem B271687 : Blo 207808 271687 := bstep (se 1 (by rfl) ⟨203765, by rfl⟩ : syracuseStep 271687 = 407531) B407531
theorem B1582415 : Blo 207808 1582415 := bstep (se 1 (by rfl) ⟨1186811, by rfl⟩ : syracuseStep 1582415 = 2373623) B2373623
theorem B468449 : Blo 207808 468449 := bstep (se 2 (by rfl) ⟨175668, by rfl⟩ : syracuseStep 468449 = 351337) B351337
theorem B894689 : Blo 207808 894689 := bstep (se 2 (by rfl) ⟨335508, by rfl⟩ : syracuseStep 894689 = 671017) B671017
theorem B534559 : Blo 207808 534559 := bstep (se 1 (by rfl) ⟨400919, by rfl⟩ : syracuseStep 534559 = 801839) B801839
theorem B895303 : Blo 207808 895303 := bstep (se 1 (by rfl) ⟨671477, by rfl⟩ : syracuseStep 895303 = 1342955) B1342955
theorem B829865 : Blo 207808 829865 := bstep (se 2 (by rfl) ⟨311199, by rfl⟩ : syracuseStep 829865 = 622399) B622399
theorem B469817 : Blo 207808 469817 := bstep (se 2 (by rfl) ⟨176181, by rfl⟩ : syracuseStep 469817 = 352363) B352363
theorem B207855 : Blo 207808 207855 := bstep (se 1 (by rfl) ⟨155891, by rfl⟩ : syracuseStep 207855 = 311783) B311783
theorem B470177 : Blo 207808 470177 := bstep (se 2 (by rfl) ⟨176316, by rfl⟩ : syracuseStep 470177 = 352633) B352633
theorem B208039 : Blo 207808 208039 := bstep (se 1 (by rfl) ⟨156029, by rfl⟩ : syracuseStep 208039 = 312059) B312059
theorem B1191095 : Blo 207808 1191095 := bstep (se 1 (by rfl) ⟨893321, by rfl⟩ : syracuseStep 1191095 = 1786643) B1786643
theorem B535855 : Blo 207808 535855 := bstep (se 1 (by rfl) ⟨401891, by rfl⟩ : syracuseStep 535855 = 803783) B803783
theorem B208335 : Blo 207808 208335 := bstep (se 1 (by rfl) ⟨156251, by rfl⟩ : syracuseStep 208335 = 312503) B312503
theorem B208431 : Blo 207808 208431 := bstep (se 1 (by rfl) ⟨156323, by rfl⟩ : syracuseStep 208431 = 312647) B312647
theorem B208495 : Blo 207808 208495 := bstep (se 1 (by rfl) ⟨156371, by rfl⟩ : syracuseStep 208495 = 312743) B312743
theorem B208615 : Blo 207808 208615 := bstep (se 1 (by rfl) ⟨156461, by rfl⟩ : syracuseStep 208615 = 312923) B312923
theorem B601967 : Blo 207808 601967 := bstep (se 1 (by rfl) ⟨451475, by rfl⟩ : syracuseStep 601967 = 902951) B902951
theorem B2404241 : Blo 207808 2404241 := bstep (se 2 (by rfl) ⟨901590, by rfl⟩ : syracuseStep 2404241 = 1803181) B1803181
theorem B208927 : Blo 207808 208927 := bstep (se 1 (by rfl) ⟨156695, by rfl⟩ : syracuseStep 208927 = 313391) B313391
theorem B209103 : Blo 207808 209103 := bstep (se 1 (by rfl) ⟨156827, by rfl⟩ : syracuseStep 209103 = 313655) B313655
theorem B5353775 : Blo 207808 5353775 := bstep (se 1 (by rfl) ⟨4015331, by rfl⟩ : syracuseStep 5353775 = 8030663) B8030663
theorem B209223 : Blo 207808 209223 := bstep (se 1 (by rfl) ⟨156917, by rfl⟩ : syracuseStep 209223 = 313835) B313835
theorem B897389 : Blo 207808 897389 := bstep (se 3 (by rfl) ⟨168260, by rfl⟩ : syracuseStep 897389 = 336521) B336521
theorem B209383 : Blo 207808 209383 := bstep (se 1 (by rfl) ⟨157037, by rfl⟩ : syracuseStep 209383 = 314075) B314075
theorem B209407 : Blo 207808 209407 := bstep (se 1 (by rfl) ⟨157055, by rfl⟩ : syracuseStep 209407 = 314111) B314111
theorem B1192553 : Blo 207808 1192553 := bstep (se 2 (by rfl) ⟨447207, by rfl⟩ : syracuseStep 1192553 = 894415) B894415
theorem B1749815 : Blo 207808 1749815 := bstep (se 1 (by rfl) ⟨1312361, by rfl⟩ : syracuseStep 1749815 = 2624723) B2624723
theorem B209887 : Blo 207808 209887 := bstep (se 1 (by rfl) ⟨157415, by rfl⟩ : syracuseStep 209887 = 314831) B314831
theorem B209947 : Blo 207808 209947 := bstep (se 1 (by rfl) ⟨157460, by rfl⟩ : syracuseStep 209947 = 314921) B314921
theorem B210143 : Blo 207808 210143 := bstep (se 1 (by rfl) ⟨157607, by rfl⟩ : syracuseStep 210143 = 315215) B315215
theorem B636167 : Blo 207808 636167 := bstep (se 1 (by rfl) ⟨477125, by rfl⟩ : syracuseStep 636167 = 954251) B954251
theorem B210223 : Blo 207808 210223 := bstep (se 1 (by rfl) ⟨157667, by rfl⟩ : syracuseStep 210223 = 315335) B315335
theorem B800063 : Blo 207808 800063 := bstep (se 1 (by rfl) ⟨600047, by rfl⟩ : syracuseStep 800063 = 1200095) B1200095
theorem B210279 : Blo 207808 210279 := bstep (se 1 (by rfl) ⟨157709, by rfl⟩ : syracuseStep 210279 = 315419) B315419
theorem B472427 : Blo 207808 472427 := bstep (se 1 (by rfl) ⟨354320, by rfl⟩ : syracuseStep 472427 = 708641) B708641
theorem B701945 : Blo 207808 701945 := bstep (se 2 (by rfl) ⟨263229, by rfl⟩ : syracuseStep 701945 = 526459) B526459
theorem B472607 : Blo 207808 472607 := bstep (se 1 (by rfl) ⟨354455, by rfl⟩ : syracuseStep 472607 = 708911) B708911
theorem B210463 : Blo 207808 210463 := bstep (se 1 (by rfl) ⟨157847, by rfl⟩ : syracuseStep 210463 = 315695) B315695
theorem B210535 : Blo 207808 210535 := bstep (se 1 (by rfl) ⟨157901, by rfl⟩ : syracuseStep 210535 = 315803) B315803
theorem B800381 : Blo 207808 800381 := bstep (se 3 (by rfl) ⟨150071, by rfl⟩ : syracuseStep 800381 = 300143) B300143
theorem B210559 : Blo 207808 210559 := bstep (se 1 (by rfl) ⟨157919, by rfl⟩ : syracuseStep 210559 = 315839) B315839
theorem B702107 : Blo 207808 702107 := bstep (se 1 (by rfl) ⟨526580, by rfl⟩ : syracuseStep 702107 = 1053161) B1053161
theorem B210623 : Blo 207808 210623 := bstep (se 1 (by rfl) ⟨157967, by rfl⟩ : syracuseStep 210623 = 315935) B315935
theorem B210815 : Blo 207808 210815 := bstep (se 1 (by rfl) ⟨158111, by rfl⟩ : syracuseStep 210815 = 316223) B316223
theorem B210911 : Blo 207808 210911 := bstep (se 1 (by rfl) ⟨158183, by rfl⟩ : syracuseStep 210911 = 316367) B316367
theorem B210971 : Blo 207808 210971 := bstep (se 1 (by rfl) ⟨158228, by rfl⟩ : syracuseStep 210971 = 316457) B316457
theorem B210991 : Blo 207808 210991 := bstep (se 1 (by rfl) ⟨158243, by rfl⟩ : syracuseStep 210991 = 316487) B316487
theorem B473255 : Blo 207808 473255 := bstep (se 1 (by rfl) ⟨354941, by rfl⟩ : syracuseStep 473255 = 709883) B709883
theorem B211111 : Blo 207808 211111 := bstep (se 1 (by rfl) ⟨158333, by rfl⟩ : syracuseStep 211111 = 316667) B316667
theorem B702647 : Blo 207808 702647 := bstep (se 1 (by rfl) ⟨526985, by rfl⟩ : syracuseStep 702647 = 1053971) B1053971
theorem B211151 : Blo 207808 211151 := bstep (se 1 (by rfl) ⟨158363, by rfl⟩ : syracuseStep 211151 = 316727) B316727
theorem B1685897 : Blo 207808 1685897 := bstep (se 2 (by rfl) ⟨632211, by rfl⟩ : syracuseStep 1685897 = 1264423) B1264423
theorem B211355 : Blo 207808 211355 := bstep (se 1 (by rfl) ⟨158516, by rfl⟩ : syracuseStep 211355 = 317033) B317033
theorem B1587761 : Blo 207808 1587761 := bstep (se 2 (by rfl) ⟨595410, by rfl⟩ : syracuseStep 1587761 = 1190821) B1190821
theorem B211711 : Blo 207808 211711 := bstep (se 1 (by rfl) ⟨158783, by rfl⟩ : syracuseStep 211711 = 317567) B317567
theorem B1063691 : Blo 207808 1063691 := bstep (se 1 (by rfl) ⟨797768, by rfl⟩ : syracuseStep 1063691 = 1595537) B1595537
theorem B211775 : Blo 207808 211775 := bstep (se 1 (by rfl) ⟨158831, by rfl⟩ : syracuseStep 211775 = 317663) B317663
theorem B1686511 : Blo 207808 1686511 := bstep (se 1 (by rfl) ⟨1264883, by rfl⟩ : syracuseStep 1686511 = 2529767) B2529767
theorem B2538971 : Blo 207808 2538971 := bstep (se 1 (by rfl) ⟨1904228, by rfl⟩ : syracuseStep 2538971 = 3808457) B3808457
theorem B802295 : Blo 207808 802295 := bstep (se 1 (by rfl) ⟨601721, by rfl⟩ : syracuseStep 802295 = 1203443) B1203443
theorem B1457875 : Blo 207808 1457875 := bstep (se 1 (by rfl) ⟨1093406, by rfl⟩ : syracuseStep 1457875 = 2186813) B2186813
theorem B312041 : Blo 207808 312041 := bstep (se 2 (by rfl) ⟨117015, by rfl⟩ : syracuseStep 312041 = 234031) B234031
theorem B18302219 : Blo 207808 18302219 := bstep (se 1 (by rfl) ⟨13726664, by rfl⟩ : syracuseStep 18302219 = 27453329) B27453329
theorem B312809 : Blo 207808 312809 := bstep (se 2 (by rfl) ⟨117303, by rfl⟩ : syracuseStep 312809 = 234607) B234607
theorem B312887 : Blo 207808 312887 := bstep (se 1 (by rfl) ⟨234665, by rfl⟩ : syracuseStep 312887 = 469331) B469331
theorem B706103 : Blo 207808 706103 := bstep (se 1 (by rfl) ⟨529577, by rfl⟩ : syracuseStep 706103 = 1059155) B1059155
theorem B22136609 : Blo 207808 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B2606995 : Blo 207808 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B313247 : Blo 207808 313247 := bstep (se 1 (by rfl) ⟨234935, by rfl⟩ : syracuseStep 313247 = 469871) B469871
theorem B444371 : Blo 207808 444371 := bstep (se 1 (by rfl) ⟨333278, by rfl⟩ : syracuseStep 444371 = 666557) B666557
theorem B313415 : Blo 207808 313415 := bstep (se 1 (by rfl) ⟨235061, by rfl⟩ : syracuseStep 313415 = 470123) B470123
theorem B706643 : Blo 207808 706643 := bstep (se 1 (by rfl) ⟨529982, by rfl⟩ : syracuseStep 706643 = 1059965) B1059965
theorem B313595 : Blo 207808 313595 := bstep (se 1 (by rfl) ⟨235196, by rfl⟩ : syracuseStep 313595 = 470393) B470393
theorem B706859 : Blo 207808 706859 := bstep (se 1 (by rfl) ⟨530144, by rfl⟩ : syracuseStep 706859 = 1060289) B1060289
theorem B314015 : Blo 207808 314015 := bstep (se 1 (by rfl) ⟨235511, by rfl⟩ : syracuseStep 314015 = 471023) B471023
theorem B708047 : Blo 207808 708047 := bstep (se 1 (by rfl) ⟨531035, by rfl⟩ : syracuseStep 708047 = 1062071) B1062071
theorem B314879 : Blo 207808 314879 := bstep (se 1 (by rfl) ⟨236159, by rfl⟩ : syracuseStep 314879 = 472319) B472319
theorem B709019 : Blo 207808 709019 := bstep (se 1 (by rfl) ⟨531764, by rfl⟩ : syracuseStep 709019 = 1063529) B1063529
theorem B1069523 : Blo 207808 1069523 := bstep (se 1 (by rfl) ⟨802142, by rfl⟩ : syracuseStep 1069523 = 1604285) B1604285
theorem B316031 : Blo 207808 316031 := bstep (se 1 (by rfl) ⟨237023, by rfl⟩ : syracuseStep 316031 = 474047) B474047
theorem B316463 : Blo 207808 316463 := bstep (se 1 (by rfl) ⟨237347, by rfl⟩ : syracuseStep 316463 = 474695) B474695
theorem B316583 : Blo 207808 316583 := bstep (se 1 (by rfl) ⟨237437, by rfl⟩ : syracuseStep 316583 = 474875) B474875
theorem B13685939 : Blo 207808 13685939 := bstep (se 1 (by rfl) ⟨10264454, by rfl⟩ : syracuseStep 13685939 = 20528909) B20528909
theorem B316751 : Blo 207808 316751 := bstep (se 1 (by rfl) ⟨237563, by rfl⟩ : syracuseStep 316751 = 475127) B475127
theorem B1922555 : Blo 207808 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B316991 : Blo 207808 316991 := bstep (se 1 (by rfl) ⟨237743, by rfl⟩ : syracuseStep 316991 = 475487) B475487
theorem B4052663 : Blo 207808 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B317351 : Blo 207808 317351 := bstep (se 1 (by rfl) ⟨238013, by rfl⟩ : syracuseStep 317351 = 476027) B476027
theorem B317435 : Blo 207808 317435 := bstep (se 1 (by rfl) ⟨238076, by rfl⟩ : syracuseStep 317435 = 476153) B476153
theorem B317471 : Blo 207808 317471 := bstep (se 1 (by rfl) ⟨238103, by rfl⟩ : syracuseStep 317471 = 476207) B476207
theorem B317495 : Blo 207808 317495 := bstep (se 1 (by rfl) ⟨238121, by rfl⟩ : syracuseStep 317495 = 476243) B476243
theorem B317561 : Blo 207808 317561 := bstep (se 2 (by rfl) ⟨119085, by rfl⟩ : syracuseStep 317561 = 238171) B238171
theorem B1202303 : Blo 207808 1202303 := bstep (se 1 (by rfl) ⟨901727, by rfl⟩ : syracuseStep 1202303 = 1803455) B1803455
theorem B317615 : Blo 207808 317615 := bstep (se 1 (by rfl) ⟨238211, by rfl⟩ : syracuseStep 317615 = 476423) B476423
theorem B1333705 : Blo 207808 1333705 := bstep (se 2 (by rfl) ⟨500139, by rfl⟩ : syracuseStep 1333705 = 1000279) B1000279
theorem B2284321 : Blo 207808 2284321 := bstep (se 2 (by rfl) ⟨856620, by rfl⟩ : syracuseStep 2284321 = 1713241) B1713241
theorem B351391 : Blo 207808 351391 := bstep (se 1 (by rfl) ⟨263543, by rfl⟩ : syracuseStep 351391 = 527087) B527087
theorem B3235241 : Blo 207808 3235241 := bstep (se 2 (by rfl) ⟨1213215, by rfl⟩ : syracuseStep 3235241 = 2426431) B2426431
theorem B100228913 : Blo 207808 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B1597481 : Blo 207808 1597481 := bstep (se 2 (by rfl) ⟨599055, by rfl⟩ : syracuseStep 1597481 = 1198111) B1198111
theorem B1597967 : Blo 207808 1597967 := bstep (se 1 (by rfl) ⟨1198475, by rfl⟩ : syracuseStep 1597967 = 2396951) B2396951
theorem B3400393 : Blo 207808 3400393 := bstep (se 2 (by rfl) ⟨1275147, by rfl⟩ : syracuseStep 3400393 = 2550295) B2550295
theorem B713555 : Blo 207808 713555 := bstep (se 1 (by rfl) ⟨535166, by rfl⟩ : syracuseStep 713555 = 1070333) B1070333
theorem B2155511 : Blo 207808 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B353767 : Blo 207808 353767 := bstep (se 1 (by rfl) ⟨265325, by rfl⟩ : syracuseStep 353767 = 530651) B530651
theorem B386537 : Blo 207808 386537 := bstep (se 2 (by rfl) ⟨144951, by rfl⟩ : syracuseStep 386537 = 289903) B289903
theorem B353929 : Blo 207808 353929 := bstep (se 2 (by rfl) ⟨132723, by rfl⟩ : syracuseStep 353929 = 265447) B265447
theorem B353983 : Blo 207808 353983 := bstep (se 1 (by rfl) ⟨265487, by rfl⟩ : syracuseStep 353983 = 530975) B530975
theorem B5793569 : Blo 207808 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B847361 : Blo 207808 847361 := bstep (se 2 (by rfl) ⟨317760, by rfl⟩ : syracuseStep 847361 = 635521) B635521
theorem B716833 : Blo 207808 716833 := bstep (se 2 (by rfl) ⟨268812, by rfl⟩ : syracuseStep 716833 = 537625) B537625
theorem B1536185 : Blo 207808 1536185 := bstep (se 2 (by rfl) ⟨576069, by rfl⟩ : syracuseStep 1536185 = 1152139) B1152139
theorem B356665 : Blo 207808 356665 := bstep (se 2 (by rfl) ⟨133749, by rfl⟩ : syracuseStep 356665 = 267499) B267499
theorem B6845309 : Blo 207808 6845309 := bstep (se 3 (by rfl) ⟨1283495, by rfl⟩ : syracuseStep 6845309 = 2566991) B2566991
theorem B357311 : Blo 207808 357311 := bstep (se 1 (by rfl) ⟨267983, by rfl⟩ : syracuseStep 357311 = 535967) B535967
theorem B849695 : Blo 207808 849695 := bstep (se 1 (by rfl) ⟨637271, by rfl⟩ : syracuseStep 849695 = 1274543) B1274543
theorem B6781067 : Blo 207808 6781067 := bstep (se 1 (by rfl) ⟨5085800, by rfl⟩ : syracuseStep 6781067 = 10171601) B10171601
theorem B1800791 : Blo 207808 1800791 := bstep (se 1 (by rfl) ⟨1350593, by rfl⟩ : syracuseStep 1800791 = 2701187) B2701187
theorem B424759 : Blo 207808 424759 := bstep (se 1 (by rfl) ⟨318569, by rfl⟩ : syracuseStep 424759 = 637139) B637139
theorem B4553927 : Blo 207808 4553927 := bstep (se 1 (by rfl) ⟨3415445, by rfl⟩ : syracuseStep 4553927 = 6830891) B6830891
theorem B1343263 : Blo 207808 1343263 := bstep (se 1 (by rfl) ⟨1007447, by rfl⟩ : syracuseStep 1343263 = 2014895) B2014895
theorem B4096493 : Blo 207808 4096493 := bstep (se 3 (by rfl) ⟨768092, by rfl⟩ : syracuseStep 4096493 = 1536185) B1536185
theorem B4687409 : Blo 207808 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B362249 : Blo 207808 362249 := bstep (se 2 (by rfl) ⟨135843, by rfl⟩ : syracuseStep 362249 = 271687) B271687
theorem B592211 : Blo 207808 592211 := bstep (se 1 (by rfl) ⟨444158, by rfl⟩ : syracuseStep 592211 = 888317) B888317
theorem B3475993 : Blo 207808 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B527431 : Blo 207808 527431 := bstep (se 1 (by rfl) ⟨395573, by rfl⟩ : syracuseStep 527431 = 791147) B791147
theorem B790175 : Blo 207808 790175 := bstep (se 1 (by rfl) ⟨592631, by rfl⟩ : syracuseStep 790175 = 1185263) B1185263
theorem B1281703 : Blo 207808 1281703 := bstep (se 1 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 1281703 = 1922555) B1922555
theorem B1052351 : Blo 207808 1052351 := bstep (se 1 (by rfl) ⟨789263, by rfl⟩ : syracuseStep 1052351 = 1578527) B1578527
theorem B397723 : Blo 207808 397723 := bstep (se 1 (by rfl) ⟨298292, by rfl⟩ : syracuseStep 397723 = 596585) B596585
theorem B2167199 : Blo 207808 2167199 := bstep (se 1 (by rfl) ⟨1625399, by rfl⟩ : syracuseStep 2167199 = 3250799) B3250799
theorem B2265853 : Blo 207808 2265853 := bstep (se 3 (by rfl) ⟨424847, by rfl⟩ : syracuseStep 2265853 = 849695) B849695
theorem B66819275 : Blo 207808 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B1184989 : Blo 207808 1184989 := bstep (se 3 (by rfl) ⟨222185, by rfl⟩ : syracuseStep 1184989 = 444371) B444371
theorem B333343 : Blo 207808 333343 := bstep (se 1 (by rfl) ⟨250007, by rfl⟩ : syracuseStep 333343 = 500015) B500015
theorem B3806759 : Blo 207808 3806759 := bstep (se 1 (by rfl) ⟨2855069, by rfl⟩ : syracuseStep 3806759 = 5710139) B5710139
theorem B792287 : Blo 207808 792287 := bstep (se 1 (by rfl) ⟨594215, by rfl⟩ : syracuseStep 792287 = 1188431) B1188431
theorem B399401 : Blo 207808 399401 := bstep (se 2 (by rfl) ⟨149775, by rfl⟩ : syracuseStep 399401 = 299551) B299551
theorem B1054943 : Blo 207808 1054943 := bstep (se 1 (by rfl) ⟨791207, by rfl⟩ : syracuseStep 1054943 = 1582415) B1582415
theorem B596459 : Blo 207808 596459 := bstep (se 1 (by rfl) ⟨447344, by rfl⟩ : syracuseStep 596459 = 894689) B894689
theorem B400457 : Blo 207808 400457 := bstep (se 2 (by rfl) ⟨150171, by rfl⟩ : syracuseStep 400457 = 300343) B300343
theorem B794063 : Blo 207808 794063 := bstep (se 1 (by rfl) ⟨595547, by rfl⟩ : syracuseStep 794063 = 1191095) B1191095
theorem B564907 : Blo 207808 564907 := bstep (se 1 (by rfl) ⟨423680, by rfl⟩ : syracuseStep 564907 = 847361) B847361
theorem B401311 : Blo 207808 401311 := bstep (se 1 (by rfl) ⟨300983, by rfl⟩ : syracuseStep 401311 = 601967) B601967
theorem B598259 : Blo 207808 598259 := bstep (se 1 (by rfl) ⟨448694, by rfl⟩ : syracuseStep 598259 = 897389) B897389
theorem B795035 : Blo 207808 795035 := bstep (se 1 (by rfl) ⟨596276, by rfl⟩ : syracuseStep 795035 = 1192553) B1192553
theorem B4563539 : Blo 207808 4563539 := bstep (se 1 (by rfl) ⟨3422654, by rfl⟩ : syracuseStep 4563539 = 6845309) B6845309
theorem B1778273 : Blo 207808 1778273 := bstep (se 2 (by rfl) ⟨666852, by rfl⟩ : syracuseStep 1778273 = 1333705) B1333705
theorem B238207 : Blo 207808 238207 := bstep (se 1 (by rfl) ⟨178655, by rfl⟩ : syracuseStep 238207 = 357311) B357311
theorem B533375 : Blo 207808 533375 := bstep (se 1 (by rfl) ⟨400031, by rfl⟩ : syracuseStep 533375 = 800063) B800063
theorem B467963 : Blo 207808 467963 := bstep (se 1 (by rfl) ⟨350972, by rfl⟩ : syracuseStep 467963 = 701945) B701945
theorem B566345 : Blo 207808 566345 := bstep (se 2 (by rfl) ⟨212379, by rfl⟩ : syracuseStep 566345 = 424759) B424759
theorem B533587 : Blo 207808 533587 := bstep (se 1 (by rfl) ⟨400190, by rfl⟩ : syracuseStep 533587 = 800381) B800381
theorem B468071 : Blo 207808 468071 := bstep (se 1 (by rfl) ⟨351053, by rfl⟩ : syracuseStep 468071 = 702107) B702107
theorem B533729 : Blo 207808 533729 := bstep (se 2 (by rfl) ⟨200148, by rfl⟩ : syracuseStep 533729 = 400297) B400297
theorem B468431 : Blo 207808 468431 := bstep (se 1 (by rfl) ⟨351323, by rfl⟩ : syracuseStep 468431 = 702647) B702647
theorem B468521 : Blo 207808 468521 := bstep (se 2 (by rfl) ⟨175695, by rfl⟩ : syracuseStep 468521 = 351391) B351391
theorem B1123931 : Blo 207808 1123931 := bstep (se 1 (by rfl) ⟨842948, by rfl⟩ : syracuseStep 1123931 = 1685897) B1685897
theorem B1058507 : Blo 207808 1058507 := bstep (se 1 (by rfl) ⟨793880, by rfl⟩ : syracuseStep 1058507 = 1587761) B1587761
theorem B1943833 : Blo 207808 1943833 := bstep (se 2 (by rfl) ⟨728937, by rfl⟩ : syracuseStep 1943833 = 1457875) B1457875
theorem B534863 : Blo 207808 534863 := bstep (se 1 (by rfl) ⟨401147, by rfl⟩ : syracuseStep 534863 = 802295) B802295
theorem B1059641 : Blo 207808 1059641 := bstep (se 2 (by rfl) ⟨397365, by rfl⟩ : syracuseStep 1059641 = 794731) B794731
theorem B208027 : Blo 207808 208027 := bstep (se 1 (by rfl) ⟨156020, by rfl⟩ : syracuseStep 208027 = 312041) B312041
theorem B12201479 : Blo 207808 12201479 := bstep (se 1 (by rfl) ⟨9151109, by rfl⟩ : syracuseStep 12201479 = 18302219) B18302219
theorem B4533857 : Blo 207808 4533857 := bstep (se 2 (by rfl) ⟨1700196, by rfl⟩ : syracuseStep 4533857 = 3400393) B3400393
theorem B208539 : Blo 207808 208539 := bstep (se 1 (by rfl) ⟨156404, by rfl⟩ : syracuseStep 208539 = 312809) B312809
theorem B208591 : Blo 207808 208591 := bstep (se 1 (by rfl) ⟨156443, by rfl⟩ : syracuseStep 208591 = 312887) B312887
theorem B470735 : Blo 207808 470735 := bstep (se 1 (by rfl) ⟨353051, by rfl⟩ : syracuseStep 470735 = 706103) B706103
theorem B896807 : Blo 207808 896807 := bstep (se 1 (by rfl) ⟨672605, by rfl⟩ : syracuseStep 896807 = 1345211) B1345211
theorem B208831 : Blo 207808 208831 := bstep (se 1 (by rfl) ⟨156623, by rfl⟩ : syracuseStep 208831 = 313247) B313247
theorem B208943 : Blo 207808 208943 := bstep (se 1 (by rfl) ⟨156707, by rfl⟩ : syracuseStep 208943 = 313415) B313415
theorem B471095 : Blo 207808 471095 := bstep (se 1 (by rfl) ⟨353321, by rfl⟩ : syracuseStep 471095 = 706643) B706643
theorem B1060937 : Blo 207808 1060937 := bstep (se 2 (by rfl) ⟨397851, by rfl⟩ : syracuseStep 1060937 = 795703) B795703
theorem B209063 : Blo 207808 209063 := bstep (se 1 (by rfl) ⟨156797, by rfl⟩ : syracuseStep 209063 = 313595) B313595
theorem B471239 : Blo 207808 471239 := bstep (se 1 (by rfl) ⟨353429, by rfl⟩ : syracuseStep 471239 = 706859) B706859
theorem B209343 : Blo 207808 209343 := bstep (se 1 (by rfl) ⟨157007, by rfl⟩ : syracuseStep 209343 = 314015) B314015
theorem B471689 : Blo 207808 471689 := bstep (se 2 (by rfl) ⟨176883, by rfl⟩ : syracuseStep 471689 = 353767) B353767
theorem B471905 : Blo 207808 471905 := bstep (se 2 (by rfl) ⟨176964, by rfl⟩ : syracuseStep 471905 = 353929) B353929
theorem B471977 : Blo 207808 471977 := bstep (se 2 (by rfl) ⟨176991, by rfl⟩ : syracuseStep 471977 = 353983) B353983
theorem B472031 : Blo 207808 472031 := bstep (se 1 (by rfl) ⟨354023, by rfl⟩ : syracuseStep 472031 = 708047) B708047
theorem B209919 : Blo 207808 209919 := bstep (se 1 (by rfl) ⟨157439, by rfl⟩ : syracuseStep 209919 = 314879) B314879
theorem B5748029 : Blo 207808 5748029 := bstep (se 3 (by rfl) ⟨1077755, by rfl⟩ : syracuseStep 5748029 = 2155511) B2155511
theorem B472679 : Blo 207808 472679 := bstep (se 1 (by rfl) ⟨354509, by rfl⟩ : syracuseStep 472679 = 709019) B709019
theorem B210687 : Blo 207808 210687 := bstep (se 1 (by rfl) ⟨158015, by rfl⟩ : syracuseStep 210687 = 316031) B316031
theorem B1193737 : Blo 207808 1193737 := bstep (se 2 (by rfl) ⟨447651, by rfl⟩ : syracuseStep 1193737 = 895303) B895303
theorem B702269 : Blo 207808 702269 := bstep (se 3 (by rfl) ⟨131675, by rfl⟩ : syracuseStep 702269 = 263351) B263351
theorem B899063 : Blo 207808 899063 := bstep (se 1 (by rfl) ⟨674297, by rfl⟩ : syracuseStep 899063 = 1348595) B1348595
theorem B210975 : Blo 207808 210975 := bstep (se 1 (by rfl) ⟨158231, by rfl⟩ : syracuseStep 210975 = 316463) B316463
theorem B211055 : Blo 207808 211055 := bstep (se 1 (by rfl) ⟨158291, by rfl⟩ : syracuseStep 211055 = 316583) B316583
theorem B9123959 : Blo 207808 9123959 := bstep (se 1 (by rfl) ⟨6842969, by rfl⟩ : syracuseStep 9123959 = 13685939) B13685939
theorem B211167 : Blo 207808 211167 := bstep (se 1 (by rfl) ⟨158375, by rfl⟩ : syracuseStep 211167 = 316751) B316751
theorem B3389759 : Blo 207808 3389759 := bstep (se 1 (by rfl) ⟨2542319, by rfl⟩ : syracuseStep 3389759 = 5084639) B5084639
theorem B211327 : Blo 207808 211327 := bstep (se 1 (by rfl) ⟨158495, by rfl⟩ : syracuseStep 211327 = 316991) B316991
theorem B2701775 : Blo 207808 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B1030765 : Blo 207808 1030765 := bstep (se 3 (by rfl) ⟨193268, by rfl⟩ : syracuseStep 1030765 = 386537) B386537
theorem B211567 : Blo 207808 211567 := bstep (se 1 (by rfl) ⟨158675, by rfl⟩ : syracuseStep 211567 = 317351) B317351
theorem B211623 : Blo 207808 211623 := bstep (se 1 (by rfl) ⟨158717, by rfl⟩ : syracuseStep 211623 = 317435) B317435
theorem B211647 : Blo 207808 211647 := bstep (se 1 (by rfl) ⟨158735, by rfl⟩ : syracuseStep 211647 = 317471) B317471
theorem B211663 : Blo 207808 211663 := bstep (se 1 (by rfl) ⟨158747, by rfl⟩ : syracuseStep 211663 = 317495) B317495
theorem B211707 : Blo 207808 211707 := bstep (se 1 (by rfl) ⟨158780, by rfl⟩ : syracuseStep 211707 = 317561) B317561
theorem B801535 : Blo 207808 801535 := bstep (se 1 (by rfl) ⟨601151, by rfl⟩ : syracuseStep 801535 = 1202303) B1202303
theorem B211743 : Blo 207808 211743 := bstep (se 1 (by rfl) ⟨158807, by rfl⟩ : syracuseStep 211743 = 317615) B317615
theorem B59030957 : Blo 207808 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B638695 : Blo 207808 638695 := bstep (se 1 (by rfl) ⟨479021, by rfl⟩ : syracuseStep 638695 = 958043) B958043
theorem B1064987 : Blo 207808 1064987 := bstep (se 1 (by rfl) ⟨798740, by rfl⟩ : syracuseStep 1064987 = 1597481) B1597481
theorem B704699 : Blo 207808 704699 := bstep (se 1 (by rfl) ⟨528524, by rfl⟩ : syracuseStep 704699 = 1057049) B1057049
theorem B1065149 : Blo 207808 1065149 := bstep (se 3 (by rfl) ⟨199715, by rfl⟩ : syracuseStep 1065149 = 399431) B399431
theorem B1065311 : Blo 207808 1065311 := bstep (se 1 (by rfl) ⟨798983, by rfl⟩ : syracuseStep 1065311 = 1597967) B1597967
theorem B508319 : Blo 207808 508319 := bstep (se 1 (by rfl) ⟨381239, by rfl⟩ : syracuseStep 508319 = 762479) B762479
theorem B475553 : Blo 207808 475553 := bstep (se 2 (by rfl) ⟨178332, by rfl⟩ : syracuseStep 475553 = 356665) B356665
theorem B475703 : Blo 207808 475703 := bstep (se 1 (by rfl) ⟨356777, by rfl⟩ : syracuseStep 475703 = 713555) B713555
theorem B312299 : Blo 207808 312299 := bstep (se 1 (by rfl) ⟨234224, by rfl⟩ : syracuseStep 312299 = 468449) B468449
theorem B2410073 : Blo 207808 2410073 := bstep (se 2 (by rfl) ⟨903777, by rfl⟩ : syracuseStep 2410073 = 1807555) B1807555
theorem B313211 : Blo 207808 313211 := bstep (se 1 (by rfl) ⟨234908, by rfl⟩ : syracuseStep 313211 = 469817) B469817
theorem B313451 : Blo 207808 313451 := bstep (se 1 (by rfl) ⟨235088, by rfl⟩ : syracuseStep 313451 = 470177) B470177
theorem B314537 : Blo 207808 314537 := bstep (se 2 (by rfl) ⟨117951, by rfl⟩ : syracuseStep 314537 = 235903) B235903
theorem B1166543 : Blo 207808 1166543 := bstep (se 1 (by rfl) ⟨874907, by rfl⟩ : syracuseStep 1166543 = 1749815) B1749815
theorem B314951 : Blo 207808 314951 := bstep (se 1 (by rfl) ⟨236213, by rfl⟩ : syracuseStep 314951 = 472427) B472427
theorem B315071 : Blo 207808 315071 := bstep (se 1 (by rfl) ⟨236303, by rfl⟩ : syracuseStep 315071 = 472607) B472607
theorem B2248681 : Blo 207808 2248681 := bstep (se 2 (by rfl) ⟨843255, by rfl⟩ : syracuseStep 2248681 = 1686511) B1686511
theorem B315503 : Blo 207808 315503 := bstep (se 1 (by rfl) ⟨236627, by rfl⟩ : syracuseStep 315503 = 473255) B473255
theorem B1200527 : Blo 207808 1200527 := bstep (se 1 (by rfl) ⟨900395, by rfl⟩ : syracuseStep 1200527 = 1800791) B1800791
theorem B709127 : Blo 207808 709127 := bstep (se 1 (by rfl) ⟨531845, by rfl⟩ : syracuseStep 709127 = 1063691) B1063691
theorem B3035951 : Blo 207808 3035951 := bstep (se 1 (by rfl) ⟨2276963, by rfl⟩ : syracuseStep 3035951 = 4553927) B4553927
theorem B1692647 : Blo 207808 1692647 := bstep (se 1 (by rfl) ⟨1269485, by rfl⟩ : syracuseStep 1692647 = 2538971) B2538971
theorem B1791017 : Blo 207808 1791017 := bstep (se 2 (by rfl) ⟨671631, by rfl⟩ : syracuseStep 1791017 = 1343263) B1343263
theorem B2708873 : Blo 207808 2708873 := bstep (se 2 (by rfl) ⟨1015827, by rfl⟩ : syracuseStep 2708873 = 2031655) B2031655
theorem B3823109 : Blo 207808 3823109 := bstep (se 4 (by rfl) ⟨358416, by rfl⟩ : syracuseStep 3823109 = 716833) B716833
theorem B4282283 : Blo 207808 4282283 := bstep (se 1 (by rfl) ⟨3211712, by rfl⟩ : syracuseStep 4282283 = 6423425) B6423425
theorem B1203011 : Blo 207808 1203011 := bstep (se 1 (by rfl) ⟨902258, by rfl⟩ : syracuseStep 1203011 = 1804517) B1804517
theorem B351695 : Blo 207808 351695 := bstep (se 1 (by rfl) ⟨263771, by rfl⟩ : syracuseStep 351695 = 527543) B527543
theorem B712745 : Blo 207808 712745 := bstep (se 2 (by rfl) ⟨267279, by rfl⟩ : syracuseStep 712745 = 534559) B534559
theorem B1138873 : Blo 207808 1138873 := bstep (se 2 (by rfl) ⟨427077, by rfl⟩ : syracuseStep 1138873 = 854155) B854155
theorem B483515 : Blo 207808 483515 := bstep (se 1 (by rfl) ⟨362636, by rfl⟩ : syracuseStep 483515 = 725273) B725273
theorem B713015 : Blo 207808 713015 := bstep (se 1 (by rfl) ⟨534761, by rfl⟩ : syracuseStep 713015 = 1069523) B1069523
theorem B714473 : Blo 207808 714473 := bstep (se 2 (by rfl) ⟨267927, by rfl⟩ : syracuseStep 714473 = 535855) B535855
theorem B6842303 : Blo 207808 6842303 := bstep (se 1 (by rfl) ⟨5131727, by rfl⟩ : syracuseStep 6842303 = 10263455) B10263455
theorem B2156827 : Blo 207808 2156827 := bstep (se 1 (by rfl) ⟨1617620, by rfl⟩ : syracuseStep 2156827 = 3235241) B3235241
theorem B1141751 : Blo 207808 1141751 := bstep (se 1 (by rfl) ⟨856313, by rfl⟩ : syracuseStep 1141751 = 1712627) B1712627
theorem B1141769 : Blo 207808 1141769 := bstep (se 2 (by rfl) ⟨428163, by rfl⟩ : syracuseStep 1141769 = 856327) B856327
theorem B3862379 : Blo 207808 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B553243 : Blo 207808 553243 := bstep (se 1 (by rfl) ⟨414932, by rfl⟩ : syracuseStep 553243 = 829865) B829865
theorem B1602827 : Blo 207808 1602827 := bstep (se 1 (by rfl) ⟨1202120, by rfl⟩ : syracuseStep 1602827 = 2404241) B2404241
theorem B3569183 : Blo 207808 3569183 := bstep (se 1 (by rfl) ⟨2676887, by rfl⟩ : syracuseStep 3569183 = 5353775) B5353775
theorem B424111 : Blo 207808 424111 := bstep (se 1 (by rfl) ⟨318083, by rfl⟩ : syracuseStep 424111 = 636167) B636167
theorem B3045761 : Blo 207808 3045761 := bstep (se 2 (by rfl) ⟨1142160, by rfl⟩ : syracuseStep 3045761 = 2284321) B2284321
theorem B4520711 : Blo 207808 4520711 := bstep (se 1 (by rfl) ⟨3390533, by rfl⟩ : syracuseStep 4520711 = 6781067) B6781067
theorem B1606715 : Blo 207808 1606715 := bstep (se 1 (by rfl) ⟨1205036, by rfl⟩ : syracuseStep 1606715 = 2410073) B2410073
theorem B394807 : Blo 207808 394807 := bstep (se 1 (by rfl) ⟨296105, by rfl⟩ : syracuseStep 394807 = 592211) B592211
theorem B526783 : Blo 207808 526783 := bstep (se 1 (by rfl) ⟨395087, by rfl⟩ : syracuseStep 526783 = 790175) B790175
theorem B1444799 : Blo 207808 1444799 := bstep (se 1 (by rfl) ⟨1083599, by rfl⟩ : syracuseStep 1444799 = 2167199) B2167199
theorem B2591777 : Blo 207808 2591777 := bstep (se 2 (by rfl) ⟨971916, by rfl⟩ : syracuseStep 2591777 = 1943833) B1943833
theorem B1805915 : Blo 207808 1805915 := bstep (se 1 (by rfl) ⟨1354436, by rfl⟩ : syracuseStep 1805915 = 2708873) B2708873
theorem B528191 : Blo 207808 528191 := bstep (se 1 (by rfl) ⟨396143, by rfl⟩ : syracuseStep 528191 = 792287) B792287
theorem B2854855 : Blo 207808 2854855 := bstep (se 1 (by rfl) ⟨2141141, by rfl⟩ : syracuseStep 2854855 = 4282283) B4282283
theorem B266267 : Blo 207808 266267 := bstep (se 1 (by rfl) ⟨199700, by rfl⟩ : syracuseStep 266267 = 399401) B399401
theorem B397639 : Blo 207808 397639 := bstep (se 1 (by rfl) ⟨298229, by rfl⟩ : syracuseStep 397639 = 596459) B596459
theorem B266971 : Blo 207808 266971 := bstep (se 1 (by rfl) ⟨200228, by rfl⟩ : syracuseStep 266971 = 400457) B400457
theorem B1708937 : Blo 207808 1708937 := bstep (se 2 (by rfl) ⟨640851, by rfl⟩ : syracuseStep 1708937 = 1281703) B1281703
theorem B234463 : Blo 207808 234463 := bstep (se 1 (by rfl) ⟨175847, by rfl⟩ : syracuseStep 234463 = 351695) B351695
theorem B529375 : Blo 207808 529375 := bstep (se 1 (by rfl) ⟨397031, by rfl⟩ : syracuseStep 529375 = 794063) B794063
theorem B398839 : Blo 207808 398839 := bstep (se 1 (by rfl) ⟨299129, by rfl⟩ : syracuseStep 398839 = 598259) B598259
theorem B530023 : Blo 207808 530023 := bstep (se 1 (by rfl) ⟨397517, by rfl⟩ : syracuseStep 530023 = 795035) B795035
theorem B1185515 : Blo 207808 1185515 := bstep (se 1 (by rfl) ⟨889136, by rfl⟩ : syracuseStep 1185515 = 1778273) B1778273
theorem B530297 : Blo 207808 530297 := bstep (se 2 (by rfl) ⟨198861, by rfl⟩ : syracuseStep 530297 = 397723) B397723
theorem B3021137 : Blo 207808 3021137 := bstep (se 2 (by rfl) ⟨1132926, by rfl⟩ : syracuseStep 3021137 = 2265853) B2265853
theorem B4561535 : Blo 207808 4561535 := bstep (se 1 (by rfl) ⟨3421151, by rfl⟩ : syracuseStep 4561535 = 6842303) B6842303
theorem B1579985 : Blo 207808 1579985 := bstep (se 2 (by rfl) ⟨592494, by rfl⟩ : syracuseStep 1579985 = 1184989) B1184989
theorem B761167 : Blo 207808 761167 := bstep (se 1 (by rfl) ⟨570875, by rfl⟩ : syracuseStep 761167 = 1141751) B1141751
theorem B761179 : Blo 207808 761179 := bstep (se 1 (by rfl) ⟨570884, by rfl⟩ : syracuseStep 761179 = 1141769) B1141769
theorem B8134319 : Blo 207808 8134319 := bstep (se 1 (by rfl) ⟨6100739, by rfl⟩ : syracuseStep 8134319 = 12201479) B12201479
theorem B3022571 : Blo 207808 3022571 := bstep (se 1 (by rfl) ⟨2266928, by rfl⟩ : syracuseStep 3022571 = 4533857) B4533857
theorem B597871 : Blo 207808 597871 := bstep (se 1 (by rfl) ⟨448403, by rfl⟩ : syracuseStep 597871 = 896807) B896807
theorem B565481 : Blo 207808 565481 := bstep (se 2 (by rfl) ⟨212055, by rfl⟩ : syracuseStep 565481 = 424111) B424111
theorem B468179 : Blo 207808 468179 := bstep (se 1 (by rfl) ⟨351134, by rfl⟩ : syracuseStep 468179 = 702269) B702269
theorem B599375 : Blo 207808 599375 := bstep (se 1 (by rfl) ⟨449531, by rfl⟩ : syracuseStep 599375 = 899063) B899063
theorem B535081 : Blo 207808 535081 := bstep (se 2 (by rfl) ⟨200655, by rfl⟩ : syracuseStep 535081 = 401311) B401311
theorem B469799 : Blo 207808 469799 := bstep (se 1 (by rfl) ⟨352349, by rfl⟩ : syracuseStep 469799 = 704699) B704699
theorem B1518497 : Blo 207808 1518497 := bstep (se 2 (by rfl) ⟨569436, by rfl⟩ : syracuseStep 1518497 = 1138873) B1138873
theorem B338879 : Blo 207808 338879 := bstep (se 1 (by rfl) ⟨254159, by rfl⟩ : syracuseStep 338879 = 508319) B508319
theorem B2730995 : Blo 207808 2730995 := bstep (se 1 (by rfl) ⟨2048246, by rfl⟩ : syracuseStep 2730995 = 4096493) B4096493
theorem B208199 : Blo 207808 208199 := bstep (se 1 (by rfl) ⟨156149, by rfl⟩ : syracuseStep 208199 = 312299) B312299
theorem B3124939 : Blo 207808 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B241499 : Blo 207808 241499 := bstep (se 1 (by rfl) ⟨181124, by rfl⟩ : syracuseStep 241499 = 362249) B362249
theorem B208807 : Blo 207808 208807 := bstep (se 1 (by rfl) ⟨156605, by rfl⟩ : syracuseStep 208807 = 313211) B313211
theorem B208967 : Blo 207808 208967 := bstep (se 1 (by rfl) ⟨156725, by rfl⟩ : syracuseStep 208967 = 313451) B313451
theorem B209691 : Blo 207808 209691 := bstep (se 1 (by rfl) ⟨157268, by rfl⟩ : syracuseStep 209691 = 314537) B314537
theorem B209967 : Blo 207808 209967 := bstep (se 1 (by rfl) ⟨157475, by rfl⟩ : syracuseStep 209967 = 314951) B314951
theorem B701567 : Blo 207808 701567 := bstep (se 1 (by rfl) ⟨526175, by rfl⟩ : syracuseStep 701567 = 1052351) B1052351
theorem B210047 : Blo 207808 210047 := bstep (se 1 (by rfl) ⟨157535, by rfl⟩ : syracuseStep 210047 = 315071) B315071
theorem B210335 : Blo 207808 210335 := bstep (se 1 (by rfl) ⟨157751, by rfl⟩ : syracuseStep 210335 = 315503) B315503
theorem B800351 : Blo 207808 800351 := bstep (se 1 (by rfl) ⟨600263, by rfl⟩ : syracuseStep 800351 = 1200527) B1200527
theorem B472751 : Blo 207808 472751 := bstep (se 1 (by rfl) ⟨354563, by rfl⟩ : syracuseStep 472751 = 709127) B709127
theorem B1128431 : Blo 207808 1128431 := bstep (se 1 (by rfl) ⟨846323, by rfl⟩ : syracuseStep 1128431 = 1692647) B1692647
theorem B1194011 : Blo 207808 1194011 := bstep (se 1 (by rfl) ⟨895508, by rfl⟩ : syracuseStep 1194011 = 1791017) B1791017
theorem B4634657 : Blo 207808 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B44546183 : Blo 207808 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B2537839 : Blo 207808 2537839 := bstep (se 1 (by rfl) ⟨1903379, by rfl⟩ : syracuseStep 2537839 = 3806759) B3806759
theorem B703241 : Blo 207808 703241 := bstep (se 2 (by rfl) ⟨263715, by rfl⟩ : syracuseStep 703241 = 527431) B527431
theorem B703295 : Blo 207808 703295 := bstep (se 1 (by rfl) ⟨527471, by rfl⟩ : syracuseStep 703295 = 1054943) B1054943
theorem B802007 : Blo 207808 802007 := bstep (se 1 (by rfl) ⟨601505, by rfl⟩ : syracuseStep 802007 = 1203011) B1203011
theorem B2998241 : Blo 207808 2998241 := bstep (se 2 (by rfl) ⟨1124340, by rfl⟩ : syracuseStep 2998241 = 2248681) B2248681
theorem B475163 : Blo 207808 475163 := bstep (se 1 (by rfl) ⟨356372, by rfl⟩ : syracuseStep 475163 = 712745) B712745
theorem B475343 : Blo 207808 475343 := bstep (se 1 (by rfl) ⟨356507, by rfl⟩ : syracuseStep 475343 = 713015) B713015
theorem B24330557 : Blo 207808 24330557 := bstep (se 3 (by rfl) ⟨4561979, by rfl⟩ : syracuseStep 24330557 = 9123959) B9123959
theorem B737657 : Blo 207808 737657 := bstep (se 2 (by rfl) ⟨276621, by rfl⟩ : syracuseStep 737657 = 553243) B553243
theorem B311975 : Blo 207808 311975 := bstep (se 1 (by rfl) ⟨233981, by rfl⟩ : syracuseStep 311975 = 467963) B467963
theorem B377563 : Blo 207808 377563 := bstep (se 1 (by rfl) ⟨283172, by rfl⟩ : syracuseStep 377563 = 566345) B566345
theorem B312047 : Blo 207808 312047 := bstep (se 1 (by rfl) ⟨234035, by rfl⟩ : syracuseStep 312047 = 468071) B468071
theorem B312287 : Blo 207808 312287 := bstep (se 1 (by rfl) ⟨234215, by rfl⟩ : syracuseStep 312287 = 468431) B468431
theorem B312347 : Blo 207808 312347 := bstep (se 1 (by rfl) ⟨234260, by rfl⟩ : syracuseStep 312347 = 468521) B468521
theorem B705671 : Blo 207808 705671 := bstep (se 1 (by rfl) ⟨529253, by rfl⟩ : syracuseStep 705671 = 1058507) B1058507
theorem B476315 : Blo 207808 476315 := bstep (se 1 (by rfl) ⟨357236, by rfl⟩ : syracuseStep 476315 = 714473) B714473
theorem B706427 : Blo 207808 706427 := bstep (se 1 (by rfl) ⟨529820, by rfl⟩ : syracuseStep 706427 = 1059641) B1059641
theorem B444457 : Blo 207808 444457 := bstep (se 2 (by rfl) ⟨166671, by rfl⟩ : syracuseStep 444457 = 333343) B333343
theorem B1591649 : Blo 207808 1591649 := bstep (se 2 (by rfl) ⟨596868, by rfl⟩ : syracuseStep 1591649 = 1193737) B1193737
theorem B313823 : Blo 207808 313823 := bstep (se 1 (by rfl) ⟨235367, by rfl⟩ : syracuseStep 313823 = 470735) B470735
theorem B2574919 : Blo 207808 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B314063 : Blo 207808 314063 := bstep (se 1 (by rfl) ⟨235547, by rfl⟩ : syracuseStep 314063 = 471095) B471095
theorem B707291 : Blo 207808 707291 := bstep (se 1 (by rfl) ⟨530468, by rfl⟩ : syracuseStep 707291 = 1060937) B1060937
theorem B314159 : Blo 207808 314159 := bstep (se 1 (by rfl) ⟨235619, by rfl⟩ : syracuseStep 314159 = 471239) B471239
theorem B314459 : Blo 207808 314459 := bstep (se 1 (by rfl) ⟨235844, by rfl⟩ : syracuseStep 314459 = 471689) B471689
theorem B314603 : Blo 207808 314603 := bstep (se 1 (by rfl) ⟨235952, by rfl⟩ : syracuseStep 314603 = 471905) B471905
theorem B314651 : Blo 207808 314651 := bstep (se 1 (by rfl) ⟨235988, by rfl⟩ : syracuseStep 314651 = 471977) B471977
theorem B314687 : Blo 207808 314687 := bstep (se 1 (by rfl) ⟨236015, by rfl⟩ : syracuseStep 314687 = 472031) B472031
theorem B1068551 : Blo 207808 1068551 := bstep (se 1 (by rfl) ⟨801413, by rfl⟩ : syracuseStep 1068551 = 1602827) B1602827
theorem B1068713 : Blo 207808 1068713 := bstep (se 2 (by rfl) ⟨400767, by rfl⟩ : syracuseStep 1068713 = 801535) B801535
theorem B2379455 : Blo 207808 2379455 := bstep (se 1 (by rfl) ⟨1784591, by rfl⟩ : syracuseStep 2379455 = 3569183) B3569183
theorem B315119 : Blo 207808 315119 := bstep (se 1 (by rfl) ⟨236339, by rfl⟩ : syracuseStep 315119 = 472679) B472679
theorem B709991 : Blo 207808 709991 := bstep (se 1 (by rfl) ⟨532493, by rfl⟩ : syracuseStep 709991 = 1064987) B1064987
theorem B710099 : Blo 207808 710099 := bstep (se 1 (by rfl) ⟨532574, by rfl⟩ : syracuseStep 710099 = 1065149) B1065149
theorem B710207 : Blo 207808 710207 := bstep (se 1 (by rfl) ⟨532655, by rfl⟩ : syracuseStep 710207 = 1065311) B1065311
theorem B317135 : Blo 207808 317135 := bstep (se 1 (by rfl) ⟨237851, by rfl⟩ : syracuseStep 317135 = 475703) B475703
theorem B317609 : Blo 207808 317609 := bstep (se 2 (by rfl) ⟨119103, by rfl⟩ : syracuseStep 317609 = 238207) B238207
theorem B1268141 : Blo 207808 1268141 := bstep (se 3 (by rfl) ⟨237776, by rfl⟩ : syracuseStep 1268141 = 475553) B475553
theorem B711449 : Blo 207808 711449 := bstep (se 2 (by rfl) ⟨266793, by rfl⟩ : syracuseStep 711449 = 533587) B533587
theorem B777695 : Blo 207808 777695 := bstep (se 1 (by rfl) ⟨583271, by rfl⟩ : syracuseStep 777695 = 1166543) B1166543
theorem B2875769 : Blo 207808 2875769 := bstep (se 2 (by rfl) ⟨1078413, by rfl⟩ : syracuseStep 2875769 = 2156827) B2156827
theorem B2023967 : Blo 207808 2023967 := bstep (se 1 (by rfl) ⟨1517975, by rfl⟩ : syracuseStep 2023967 = 3035951) B3035951
theorem B2548739 : Blo 207808 2548739 := bstep (se 1 (by rfl) ⟨1911554, by rfl⟩ : syracuseStep 2548739 = 3823109) B3823109
theorem B322343 : Blo 207808 322343 := bstep (se 1 (by rfl) ⟨241757, by rfl⟩ : syracuseStep 322343 = 483515) B483515
theorem B3042359 : Blo 207808 3042359 := bstep (se 1 (by rfl) ⟨2281769, by rfl⟩ : syracuseStep 3042359 = 4563539) B4563539
theorem B355583 : Blo 207808 355583 := bstep (se 1 (by rfl) ⟨266687, by rfl⟩ : syracuseStep 355583 = 533375) B533375
theorem B355819 : Blo 207808 355819 := bstep (se 1 (by rfl) ⟨266864, by rfl⟩ : syracuseStep 355819 = 533729) B533729
theorem B749287 : Blo 207808 749287 := bstep (se 1 (by rfl) ⟨561965, by rfl⟩ : syracuseStep 749287 = 1123931) B1123931
theorem B356575 : Blo 207808 356575 := bstep (se 1 (by rfl) ⟨267431, by rfl⟩ : syracuseStep 356575 = 534863) B534863
theorem B1374353 : Blo 207808 1374353 := bstep (se 2 (by rfl) ⟨515382, by rfl⟩ : syracuseStep 1374353 = 1030765) B1030765
theorem B3832019 : Blo 207808 3832019 := bstep (se 1 (by rfl) ⟨2874014, by rfl⟩ : syracuseStep 3832019 = 5748029) B5748029
theorem B2259839 : Blo 207808 2259839 := bstep (se 1 (by rfl) ⟨1694879, by rfl⟩ : syracuseStep 2259839 = 3389759) B3389759
theorem B2030507 : Blo 207808 2030507 := bstep (se 1 (by rfl) ⟨1522880, by rfl⟩ : syracuseStep 2030507 = 3045761) B3045761
theorem B1801183 : Blo 207808 1801183 := bstep (se 1 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 1801183 = 2701775) B2701775
theorem B3013807 : Blo 207808 3013807 := bstep (se 1 (by rfl) ⟨2260355, by rfl⟩ : syracuseStep 3013807 = 4520711) B4520711
theorem B753209 : Blo 207808 753209 := bstep (se 2 (by rfl) ⟨282453, by rfl⟩ : syracuseStep 753209 = 564907) B564907
theorem B39353971 : Blo 207808 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B851593 : Blo 207808 851593 := bstep (se 2 (by rfl) ⟨319347, by rfl⟩ : syracuseStep 851593 = 638695) B638695
theorem B16220371 : Blo 207808 16220371 := bstep (se 1 (by rfl) ⟨12165278, by rfl⟩ : syracuseStep 16220371 = 24330557) B24330557
theorem B491771 : Blo 207808 491771 := bstep (se 1 (by rfl) ⟨368828, by rfl⟩ : syracuseStep 491771 = 737657) B737657
theorem B526409 : Blo 207808 526409 := bstep (se 2 (by rfl) ⟨197403, by rfl⟩ : syracuseStep 526409 = 394807) B394807
theorem B592609 : Blo 207808 592609 := bstep (se 2 (by rfl) ⟨222228, by rfl⟩ : syracuseStep 592609 = 444457) B444457
theorem B790343 : Blo 207808 790343 := bstep (se 1 (by rfl) ⟨592757, by rfl⟩ : syracuseStep 790343 = 1185515) B1185515
theorem B1053323 : Blo 207808 1053323 := bstep (se 1 (by rfl) ⟨789992, by rfl⟩ : syracuseStep 1053323 = 1579985) B1579985
theorem B4166585 : Blo 207808 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B3806473 : Blo 207808 3806473 := bstep (se 2 (by rfl) ⟨1427427, by rfl⟩ : syracuseStep 3806473 = 2854855) B2854855
theorem B1349311 : Blo 207808 1349311 := bstep (se 1 (by rfl) ⟨1011983, by rfl⟩ : syracuseStep 1349311 = 2023967) B2023967
theorem B530185 : Blo 207808 530185 := bstep (se 2 (by rfl) ⟨198819, by rfl⟩ : syracuseStep 530185 = 397639) B397639
theorem B399583 : Blo 207808 399583 := bstep (se 1 (by rfl) ⟨299687, by rfl⟩ : syracuseStep 399583 = 599375) B599375
theorem B12164093 : Blo 207808 12164093 := bstep (se 3 (by rfl) ⟨2280767, by rfl⟩ : syracuseStep 12164093 = 4561535) B4561535
theorem B531785 : Blo 207808 531785 := bstep (se 2 (by rfl) ⟨199419, by rfl⟩ : syracuseStep 531785 = 398839) B398839
theorem B237055 : Blo 207808 237055 := bstep (se 1 (by rfl) ⟨177791, by rfl⟩ : syracuseStep 237055 = 355583) B355583
theorem B3383785 : Blo 207808 3383785 := bstep (se 2 (by rfl) ⟨1268919, by rfl⟩ : syracuseStep 3383785 = 2537839) B2537839
theorem B467711 : Blo 207808 467711 := bstep (se 1 (by rfl) ⟨350783, by rfl⟩ : syracuseStep 467711 = 701567) B701567
theorem B533567 : Blo 207808 533567 := bstep (se 1 (by rfl) ⟨400175, by rfl⟩ : syracuseStep 533567 = 800351) B800351
theorem B2073853 : Blo 207808 2073853 := bstep (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) B777695
theorem B2401577 : Blo 207808 2401577 := bstep (se 2 (by rfl) ⟨900591, by rfl⟩ : syracuseStep 2401577 = 1801183) B1801183
theorem B796007 : Blo 207808 796007 := bstep (se 1 (by rfl) ⟨597005, by rfl⟩ : syracuseStep 796007 = 1194011) B1194011
theorem B3089771 : Blo 207808 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B29697455 : Blo 207808 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B468827 : Blo 207808 468827 := bstep (se 1 (by rfl) ⟨351620, by rfl⟩ : syracuseStep 468827 = 703241) B703241
theorem B468863 : Blo 207808 468863 := bstep (se 1 (by rfl) ⟨351647, by rfl⟩ : syracuseStep 468863 = 703295) B703295
theorem B1353671 : Blo 207808 1353671 := bstep (se 1 (by rfl) ⟨1015253, by rfl⟩ : syracuseStep 1353671 = 2030507) B2030507
theorem B534671 : Blo 207808 534671 := bstep (se 1 (by rfl) ⟨401003, by rfl⟩ : syracuseStep 534671 = 802007) B802007
theorem B52471961 : Blo 207808 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B502139 : Blo 207808 502139 := bstep (se 1 (by rfl) ⟨376604, by rfl⟩ : syracuseStep 502139 = 753209) B753209
theorem B797161 : Blo 207808 797161 := bstep (se 2 (by rfl) ⟨298935, by rfl⟩ : syracuseStep 797161 = 597871) B597871
theorem B207983 : Blo 207808 207983 := bstep (se 1 (by rfl) ⟨155987, by rfl⟩ : syracuseStep 207983 = 311975) B311975
theorem B208031 : Blo 207808 208031 := bstep (se 1 (by rfl) ⟨156023, by rfl⟩ : syracuseStep 208031 = 312047) B312047
theorem B208191 : Blo 207808 208191 := bstep (se 1 (by rfl) ⟨156143, by rfl⟩ : syracuseStep 208191 = 312287) B312287
theorem B208231 : Blo 207808 208231 := bstep (se 1 (by rfl) ⟨156173, by rfl⟩ : syracuseStep 208231 = 312347) B312347
theorem B470447 : Blo 207808 470447 := bstep (se 1 (by rfl) ⟨352835, by rfl⟩ : syracuseStep 470447 = 705671) B705671
theorem B503417 : Blo 207808 503417 := bstep (se 2 (by rfl) ⟨188781, by rfl⟩ : syracuseStep 503417 = 377563) B377563
theorem B470951 : Blo 207808 470951 := bstep (se 1 (by rfl) ⟨353213, by rfl⟩ : syracuseStep 470951 = 706427) B706427
theorem B1061099 : Blo 207808 1061099 := bstep (se 1 (by rfl) ⟨795824, by rfl⟩ : syracuseStep 1061099 = 1591649) B1591649
theorem B209215 : Blo 207808 209215 := bstep (se 1 (by rfl) ⟨156911, by rfl⟩ : syracuseStep 209215 = 313823) B313823
theorem B209375 : Blo 207808 209375 := bstep (se 1 (by rfl) ⟨157031, by rfl⟩ : syracuseStep 209375 = 314063) B314063
theorem B471527 : Blo 207808 471527 := bstep (se 1 (by rfl) ⟨353645, by rfl⟩ : syracuseStep 471527 = 707291) B707291
theorem B209439 : Blo 207808 209439 := bstep (se 1 (by rfl) ⟨157079, by rfl⟩ : syracuseStep 209439 = 314159) B314159
theorem B963199 : Blo 207808 963199 := bstep (se 1 (by rfl) ⟨722399, by rfl⟩ : syracuseStep 963199 = 1444799) B1444799
theorem B209639 : Blo 207808 209639 := bstep (se 1 (by rfl) ⟨157229, by rfl⟩ : syracuseStep 209639 = 314459) B314459
theorem B209735 : Blo 207808 209735 := bstep (se 1 (by rfl) ⟨157301, by rfl⟩ : syracuseStep 209735 = 314603) B314603
theorem B209767 : Blo 207808 209767 := bstep (se 1 (by rfl) ⟨157325, by rfl⟩ : syracuseStep 209767 = 314651) B314651
theorem B209791 : Blo 207808 209791 := bstep (se 1 (by rfl) ⟨157343, by rfl⟩ : syracuseStep 209791 = 314687) B314687
theorem B1586303 : Blo 207808 1586303 := bstep (se 1 (by rfl) ⟨1189727, by rfl⟩ : syracuseStep 1586303 = 2379455) B2379455
theorem B210079 : Blo 207808 210079 := bstep (se 1 (by rfl) ⟨157559, by rfl⟩ : syracuseStep 210079 = 315119) B315119
theorem B702377 : Blo 207808 702377 := bstep (se 2 (by rfl) ⟨263391, by rfl⟩ : syracuseStep 702377 = 526783) B526783
theorem B473327 : Blo 207808 473327 := bstep (se 1 (by rfl) ⟨354995, by rfl⟩ : syracuseStep 473327 = 709991) B709991
theorem B473399 : Blo 207808 473399 := bstep (se 1 (by rfl) ⟨355049, by rfl⟩ : syracuseStep 473399 = 710099) B710099
theorem B473471 : Blo 207808 473471 := bstep (se 1 (by rfl) ⟨355103, by rfl⟩ : syracuseStep 473471 = 710207) B710207
theorem B211423 : Blo 207808 211423 := bstep (se 1 (by rfl) ⟨158567, by rfl⟩ : syracuseStep 211423 = 317135) B317135
theorem B211739 : Blo 207808 211739 := bstep (se 1 (by rfl) ⟨158804, by rfl⟩ : syracuseStep 211739 = 317609) B317609
theorem B2014091 : Blo 207808 2014091 := bstep (se 1 (by rfl) ⟨1510568, by rfl⟩ : syracuseStep 2014091 = 3021137) B3021137
theorem B474299 : Blo 207808 474299 := bstep (se 1 (by rfl) ⟨355724, by rfl⟩ : syracuseStep 474299 = 711449) B711449
theorem B474425 : Blo 207808 474425 := bstep (se 2 (by rfl) ⟨177909, by rfl⟩ : syracuseStep 474425 = 355819) B355819
theorem B999049 : Blo 207808 999049 := bstep (se 2 (by rfl) ⟨374643, by rfl⟩ : syracuseStep 999049 = 749287) B749287
theorem B5422879 : Blo 207808 5422879 := bstep (se 1 (by rfl) ⟨4067159, by rfl⟩ : syracuseStep 5422879 = 8134319) B8134319
theorem B2015047 : Blo 207808 2015047 := bstep (se 1 (by rfl) ⟨1511285, by rfl⟩ : syracuseStep 2015047 = 3022571) B3022571
theorem B376987 : Blo 207808 376987 := bstep (se 1 (by rfl) ⟨282740, by rfl⟩ : syracuseStep 376987 = 565481) B565481
theorem B1917179 : Blo 207808 1917179 := bstep (se 1 (by rfl) ⟨1437884, by rfl⟩ : syracuseStep 1917179 = 2875769) B2875769
theorem B475433 : Blo 207808 475433 := bstep (se 2 (by rfl) ⟨178287, by rfl⟩ : syracuseStep 475433 = 356575) B356575
theorem B312119 : Blo 207808 312119 := bstep (se 1 (by rfl) ⟨234089, by rfl⟩ : syracuseStep 312119 = 468179) B468179
theorem B312617 : Blo 207808 312617 := bstep (se 2 (by rfl) ⟨117231, by rfl⟩ : syracuseStep 312617 = 234463) B234463
theorem B705833 : Blo 207808 705833 := bstep (se 2 (by rfl) ⟨264687, by rfl⟩ : syracuseStep 705833 = 529375) B529375
theorem B313199 : Blo 207808 313199 := bstep (se 1 (by rfl) ⟨234899, by rfl⟩ : syracuseStep 313199 = 469799) B469799
theorem B214895 : Blo 207808 214895 := bstep (se 1 (by rfl) ⟨161171, by rfl⟩ : syracuseStep 214895 = 322343) B322343
theorem B1820663 : Blo 207808 1820663 := bstep (se 1 (by rfl) ⟨1365497, by rfl⟩ : syracuseStep 1820663 = 2730995) B2730995
theorem B706697 : Blo 207808 706697 := bstep (se 2 (by rfl) ⟨265011, by rfl⟩ : syracuseStep 706697 = 530023) B530023
theorem B315167 : Blo 207808 315167 := bstep (se 1 (by rfl) ⟨236375, by rfl⟩ : syracuseStep 315167 = 472751) B472751
theorem B4018409 : Blo 207808 4018409 := bstep (se 2 (by rfl) ⟨1506903, by rfl⟩ : syracuseStep 4018409 = 3013807) B3013807
theorem B1135457 : Blo 207808 1135457 := bstep (se 2 (by rfl) ⟨425796, by rfl⟩ : syracuseStep 1135457 = 851593) B851593
theorem B643997 : Blo 207808 643997 := bstep (se 3 (by rfl) ⟨120749, by rfl⟩ : syracuseStep 643997 = 241499) B241499
theorem B316775 : Blo 207808 316775 := bstep (se 1 (by rfl) ⟨237581, by rfl⟩ : syracuseStep 316775 = 475163) B475163
theorem B710045 : Blo 207808 710045 := bstep (se 3 (by rfl) ⟨133133, by rfl⟩ : syracuseStep 710045 = 266267) B266267
theorem B316895 : Blo 207808 316895 := bstep (se 1 (by rfl) ⟨237671, by rfl⟩ : syracuseStep 316895 = 475343) B475343
theorem B1071143 : Blo 207808 1071143 := bstep (se 1 (by rfl) ⟨803357, by rfl⟩ : syracuseStep 1071143 = 1606715) B1606715
theorem B317543 : Blo 207808 317543 := bstep (se 1 (by rfl) ⟨238157, by rfl⟩ : syracuseStep 317543 = 476315) B476315
theorem B1727851 : Blo 207808 1727851 := bstep (se 1 (by rfl) ⟨1295888, by rfl⟩ : syracuseStep 1727851 = 2591777) B2591777
theorem B712367 : Blo 207808 712367 := bstep (se 1 (by rfl) ⟨534275, by rfl⟩ : syracuseStep 712367 = 1068551) B1068551
theorem B1203943 : Blo 207808 1203943 := bstep (se 1 (by rfl) ⟨902957, by rfl⟩ : syracuseStep 1203943 = 1805915) B1805915
theorem B712475 : Blo 207808 712475 := bstep (se 1 (by rfl) ⟨534356, by rfl⟩ : syracuseStep 712475 = 1068713) B1068713
theorem B352127 : Blo 207808 352127 := bstep (se 1 (by rfl) ⟨264095, by rfl⟩ : syracuseStep 352127 = 528191) B528191
theorem B1139291 : Blo 207808 1139291 := bstep (se 1 (by rfl) ⟨854468, by rfl⟩ : syracuseStep 1139291 = 1708937) B1708937
theorem B713441 : Blo 207808 713441 := bstep (se 2 (by rfl) ⟨267540, by rfl⟩ : syracuseStep 713441 = 535081) B535081
theorem B3433225 : Blo 207808 3433225 := bstep (se 2 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 3433225 = 2574919) B2574919
theorem B353531 : Blo 207808 353531 := bstep (se 1 (by rfl) ⟨265148, by rfl⟩ : syracuseStep 353531 = 530297) B530297
theorem B13526837 : Blo 207808 13526837 := bstep (se 5 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 13526837 = 1268141) B1268141
theorem B1699159 : Blo 207808 1699159 := bstep (se 1 (by rfl) ⟨1274369, by rfl⟩ : syracuseStep 1699159 = 2548739) B2548739
theorem B355961 : Blo 207808 355961 := bstep (se 2 (by rfl) ⟨133485, by rfl⟩ : syracuseStep 355961 = 266971) B266971
theorem B1012331 : Blo 207808 1012331 := bstep (se 1 (by rfl) ⟨759248, by rfl⟩ : syracuseStep 1012331 = 1518497) B1518497
theorem B225919 : Blo 207808 225919 := bstep (se 1 (by rfl) ⟨169439, by rfl⟩ : syracuseStep 225919 = 338879) B338879
theorem B2028239 : Blo 207808 2028239 := bstep (se 1 (by rfl) ⟨1521179, by rfl⟩ : syracuseStep 2028239 = 3042359) B3042359
theorem B752287 : Blo 207808 752287 := bstep (se 1 (by rfl) ⟨564215, by rfl⟩ : syracuseStep 752287 = 1128431) B1128431
theorem B916235 : Blo 207808 916235 := bstep (se 1 (by rfl) ⟨687176, by rfl⟩ : syracuseStep 916235 = 1374353) B1374353
theorem B2554679 : Blo 207808 2554679 := bstep (se 1 (by rfl) ⟨1916009, by rfl⟩ : syracuseStep 2554679 = 3832019) B3832019
theorem B1014889 : Blo 207808 1014889 := bstep (se 2 (by rfl) ⟨380583, by rfl⟩ : syracuseStep 1014889 = 761167) B761167
theorem B1014905 : Blo 207808 1014905 := bstep (se 2 (by rfl) ⟨380589, by rfl⟩ : syracuseStep 1014905 = 761179) B761179
theorem B1506559 : Blo 207808 1506559 := bstep (se 1 (by rfl) ⟨1129919, by rfl⟩ : syracuseStep 1506559 = 2259839) B2259839
theorem B1998827 : Blo 207808 1998827 := bstep (se 1 (by rfl) ⟨1499120, by rfl⟩ : syracuseStep 1998827 = 2998241) B2998241
theorem B1278119 : Blo 207808 1278119 := bstep (se 1 (by rfl) ⟨958589, by rfl⟩ : syracuseStep 1278119 = 1917179) B1917179
theorem B21627161 : Blo 207808 21627161 := bstep (se 2 (by rfl) ⟨8110185, by rfl⟩ : syracuseStep 21627161 = 16220371) B16220371
theorem B1311389 : Blo 207808 1311389 := bstep (se 3 (by rfl) ⟨245885, by rfl⟩ : syracuseStep 1311389 = 491771) B491771
theorem B1213775 : Blo 207808 1213775 := bstep (se 1 (by rfl) ⟨910331, by rfl⟩ : syracuseStep 1213775 = 1820663) B1820663
theorem B526895 : Blo 207808 526895 := bstep (se 1 (by rfl) ⟨395171, by rfl⟩ : syracuseStep 526895 = 790343) B790343
theorem B756971 : Blo 207808 756971 := bstep (se 1 (by rfl) ⟨567728, by rfl⟩ : syracuseStep 756971 = 1135457) B1135457
theorem B429331 : Blo 207808 429331 := bstep (se 1 (by rfl) ⟨321998, by rfl⟩ : syracuseStep 429331 = 643997) B643997
theorem B790145 : Blo 207808 790145 := bstep (se 2 (by rfl) ⟨296304, by rfl⟩ : syracuseStep 790145 = 592609) B592609
theorem B2265545 : Blo 207808 2265545 := bstep (se 2 (by rfl) ⟨849579, by rfl⟩ : syracuseStep 2265545 = 1699159) B1699159
theorem B234751 : Blo 207808 234751 := bstep (se 1 (by rfl) ⟨176063, by rfl⟩ : syracuseStep 234751 = 352127) B352127
theorem B759527 : Blo 207808 759527 := bstep (se 1 (by rfl) ⟨569645, by rfl⟩ : syracuseStep 759527 = 1139291) B1139291
theorem B235687 : Blo 207808 235687 := bstep (se 1 (by rfl) ⟨176765, by rfl⟩ : syracuseStep 235687 = 353531) B353531
theorem B1284265 : Blo 207808 1284265 := bstep (se 2 (by rfl) ⟨481599, by rfl⟩ : syracuseStep 1284265 = 963199) B963199
theorem B530671 : Blo 207808 530671 := bstep (se 1 (by rfl) ⟨398003, by rfl⟩ : syracuseStep 530671 = 796007) B796007
theorem B9017891 : Blo 207808 9017891 := bstep (se 1 (by rfl) ⟨6763418, by rfl⟩ : syracuseStep 9017891 = 13526837) B13526837
theorem B335611 : Blo 207808 335611 := bstep (se 1 (by rfl) ⟨251708, by rfl⟩ : syracuseStep 335611 = 503417) B503417
theorem B237307 : Blo 207808 237307 := bstep (se 1 (by rfl) ⟨177980, by rfl⟩ : syracuseStep 237307 = 355961) B355961
theorem B532777 : Blo 207808 532777 := bstep (se 2 (by rfl) ⟨199791, by rfl⟩ : syracuseStep 532777 = 399583) B399583
theorem B1352159 : Blo 207808 1352159 := bstep (se 1 (by rfl) ⟨1014119, by rfl⟩ : syracuseStep 1352159 = 2028239) B2028239
theorem B1057535 : Blo 207808 1057535 := bstep (se 1 (by rfl) ⟨793151, by rfl⟩ : syracuseStep 1057535 = 1586303) B1586303
theorem B468251 : Blo 207808 468251 := bstep (se 1 (by rfl) ⟨351188, by rfl⟩ : syracuseStep 468251 = 702377) B702377
theorem B1353185 : Blo 207808 1353185 := bstep (se 2 (by rfl) ⟨507444, by rfl⟩ : syracuseStep 1353185 = 1014889) B1014889
theorem B2008745 : Blo 207808 2008745 := bstep (se 2 (by rfl) ⟨753279, by rfl⟩ : syracuseStep 2008745 = 1506559) B1506559
theorem B2303801 : Blo 207808 2303801 := bstep (se 2 (by rfl) ⟨863925, by rfl⟩ : syracuseStep 2303801 = 1727851) B1727851
theorem B502649 : Blo 207808 502649 := bstep (se 2 (by rfl) ⟨188493, by rfl⟩ : syracuseStep 502649 = 376987) B376987
theorem B208079 : Blo 207808 208079 := bstep (se 1 (by rfl) ⟨156059, by rfl⟩ : syracuseStep 208079 = 312119) B312119
theorem B208411 : Blo 207808 208411 := bstep (se 1 (by rfl) ⟨156308, by rfl⟩ : syracuseStep 208411 = 312617) B312617
theorem B470555 : Blo 207808 470555 := bstep (se 1 (by rfl) ⟨352916, by rfl⟩ : syracuseStep 470555 = 705833) B705833
theorem B208799 : Blo 207808 208799 := bstep (se 1 (by rfl) ⟨156599, by rfl⟩ : syracuseStep 208799 = 313199) B313199
theorem B471131 : Blo 207808 471131 := bstep (se 1 (by rfl) ⟨353348, by rfl⟩ : syracuseStep 471131 = 706697) B706697
theorem B2765137 : Blo 207808 2765137 := bstep (se 2 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 2765137 = 2073853) B2073853
theorem B210111 : Blo 207808 210111 := bstep (se 1 (by rfl) ⟨157583, by rfl⟩ : syracuseStep 210111 = 315167) B315167
theorem B702215 : Blo 207808 702215 := bstep (se 1 (by rfl) ⟨526661, by rfl⟩ : syracuseStep 702215 = 1053323) B1053323
theorem B1062881 : Blo 207808 1062881 := bstep (se 2 (by rfl) ⟨398580, by rfl⟩ : syracuseStep 1062881 = 797161) B797161
theorem B211183 : Blo 207808 211183 := bstep (se 1 (by rfl) ⟨158387, by rfl⟩ : syracuseStep 211183 = 316775) B316775
theorem B473363 : Blo 207808 473363 := bstep (se 1 (by rfl) ⟨355022, by rfl⟩ : syracuseStep 473363 = 710045) B710045
theorem B211263 : Blo 207808 211263 := bstep (se 1 (by rfl) ⟨158447, by rfl⟩ : syracuseStep 211263 = 316895) B316895
theorem B211695 : Blo 207808 211695 := bstep (se 1 (by rfl) ⟨158771, by rfl⟩ : syracuseStep 211695 = 317543) B317543
theorem B8109395 : Blo 207808 8109395 := bstep (se 1 (by rfl) ⟨6082046, by rfl⟩ : syracuseStep 8109395 = 12164093) B12164093
theorem B573053 : Blo 207808 573053 := bstep (se 3 (by rfl) ⟨107447, by rfl⟩ : syracuseStep 573053 = 214895) B214895
theorem B474911 : Blo 207808 474911 := bstep (se 1 (by rfl) ⟨356183, by rfl⟩ : syracuseStep 474911 = 712367) B712367
theorem B474983 : Blo 207808 474983 := bstep (se 1 (by rfl) ⟨356237, by rfl⟩ : syracuseStep 474983 = 712475) B712475
theorem B475627 : Blo 207808 475627 := bstep (se 1 (by rfl) ⟨356720, by rfl⟩ : syracuseStep 475627 = 713441) B713441
theorem B311807 : Blo 207808 311807 := bstep (se 1 (by rfl) ⟨233855, by rfl⟩ : syracuseStep 311807 = 467711) B467711
theorem B312551 : Blo 207808 312551 := bstep (se 1 (by rfl) ⟨234413, by rfl⟩ : syracuseStep 312551 = 468827) B468827
theorem B312575 : Blo 207808 312575 := bstep (se 1 (by rfl) ⟨234431, by rfl⟩ : syracuseStep 312575 = 468863) B468863
theorem B902447 : Blo 207808 902447 := bstep (se 1 (by rfl) ⟨676835, by rfl⟩ : syracuseStep 902447 = 1353671) B1353671
theorem B34981307 : Blo 207808 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B313631 : Blo 207808 313631 := bstep (se 1 (by rfl) ⟨235223, by rfl⟩ : syracuseStep 313631 = 470447) B470447
theorem B706913 : Blo 207808 706913 := bstep (se 2 (by rfl) ⟨265092, by rfl⟩ : syracuseStep 706913 = 530185) B530185
theorem B313967 : Blo 207808 313967 := bstep (se 1 (by rfl) ⟨235475, by rfl⟩ : syracuseStep 313967 = 470951) B470951
theorem B707399 : Blo 207808 707399 := bstep (se 1 (by rfl) ⟨530549, by rfl⟩ : syracuseStep 707399 = 1061099) B1061099
theorem B314351 : Blo 207808 314351 := bstep (se 1 (by rfl) ⟨235763, by rfl⟩ : syracuseStep 314351 = 471527) B471527
theorem B674887 : Blo 207808 674887 := bstep (se 1 (by rfl) ⟨506165, by rfl⟩ : syracuseStep 674887 = 1012331) B1012331
theorem B1003049 : Blo 207808 1003049 := bstep (se 2 (by rfl) ⟨376143, by rfl⟩ : syracuseStep 1003049 = 752287) B752287
theorem B315551 : Blo 207808 315551 := bstep (se 1 (by rfl) ⟨236663, by rfl⟩ : syracuseStep 315551 = 473327) B473327
theorem B315599 : Blo 207808 315599 := bstep (se 1 (by rfl) ⟨236699, by rfl⟩ : syracuseStep 315599 = 473399) B473399
theorem B315647 : Blo 207808 315647 := bstep (se 1 (by rfl) ⟨236735, by rfl⟩ : syracuseStep 315647 = 473471) B473471
theorem B610823 : Blo 207808 610823 := bstep (se 1 (by rfl) ⟨458117, by rfl⟩ : syracuseStep 610823 = 916235) B916235
theorem B316073 : Blo 207808 316073 := bstep (se 2 (by rfl) ⟨118527, by rfl⟩ : syracuseStep 316073 = 237055) B237055
theorem B676603 : Blo 207808 676603 := bstep (se 1 (by rfl) ⟨507452, by rfl⟩ : syracuseStep 676603 = 1014905) B1014905
theorem B316199 : Blo 207808 316199 := bstep (se 1 (by rfl) ⟨237149, by rfl⟩ : syracuseStep 316199 = 474299) B474299
theorem B1332065 : Blo 207808 1332065 := bstep (se 2 (by rfl) ⟨499524, by rfl⟩ : syracuseStep 1332065 = 999049) B999049
theorem B316283 : Blo 207808 316283 := bstep (se 1 (by rfl) ⟨237212, by rfl⟩ : syracuseStep 316283 = 474425) B474425
theorem B7230505 : Blo 207808 7230505 := bstep (se 2 (by rfl) ⟨2711439, by rfl⟩ : syracuseStep 7230505 = 5422879) B5422879
theorem B1332551 : Blo 207808 1332551 := bstep (se 1 (by rfl) ⟨999413, by rfl⟩ : syracuseStep 1332551 = 1998827) B1998827
theorem B316955 : Blo 207808 316955 := bstep (se 1 (by rfl) ⟨237716, by rfl⟩ : syracuseStep 316955 = 475433) B475433
theorem B4511713 : Blo 207808 4511713 := bstep (se 2 (by rfl) ⟨1691892, by rfl⟩ : syracuseStep 4511713 = 3383785) B3383785
theorem B4577633 : Blo 207808 4577633 := bstep (se 2 (by rfl) ⟨1716612, by rfl⟩ : syracuseStep 4577633 = 3433225) B3433225
theorem B350939 : Blo 207808 350939 := bstep (se 1 (by rfl) ⟨263204, by rfl⟩ : syracuseStep 350939 = 526409) B526409
theorem B2678939 : Blo 207808 2678939 := bstep (se 1 (by rfl) ⟨2009204, by rfl⟩ : syracuseStep 2678939 = 4018409) B4018409
theorem B2777723 : Blo 207808 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B1204901 : Blo 207808 1204901 := bstep (se 4 (by rfl) ⟨112959, by rfl⟩ : syracuseStep 1204901 = 225919) B225919
theorem B79193213 : Blo 207808 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B714095 : Blo 207808 714095 := bstep (se 1 (by rfl) ⟨535571, by rfl⟩ : syracuseStep 714095 = 1071143) B1071143
theorem B354523 : Blo 207808 354523 := bstep (se 1 (by rfl) ⟨265892, by rfl⟩ : syracuseStep 354523 = 531785) B531785
theorem B355711 : Blo 207808 355711 := bstep (se 1 (by rfl) ⟨266783, by rfl⟩ : syracuseStep 355711 = 533567) B533567
theorem B1601051 : Blo 207808 1601051 := bstep (se 1 (by rfl) ⟨1200788, by rfl⟩ : syracuseStep 1601051 = 2401577) B2401577
theorem B2059847 : Blo 207808 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B1339037 : Blo 207808 1339037 := bstep (se 3 (by rfl) ⟨251069, by rfl⟩ : syracuseStep 1339037 = 502139) B502139
theorem B356447 : Blo 207808 356447 := bstep (se 1 (by rfl) ⟨267335, by rfl⟩ : syracuseStep 356447 = 534671) B534671
theorem B5075297 : Blo 207808 5075297 := bstep (se 2 (by rfl) ⟨1903236, by rfl⟩ : syracuseStep 5075297 = 3806473) B3806473
theorem B1799081 : Blo 207808 1799081 := bstep (se 2 (by rfl) ⟨674655, by rfl⟩ : syracuseStep 1799081 = 1349311) B1349311
theorem B1703119 : Blo 207808 1703119 := bstep (se 1 (by rfl) ⟨1277339, by rfl⟩ : syracuseStep 1703119 = 2554679) B2554679
theorem B1342727 : Blo 207808 1342727 := bstep (se 1 (by rfl) ⟨1007045, by rfl⟩ : syracuseStep 1342727 = 2014091) B2014091
theorem B1605257 : Blo 207808 1605257 := bstep (se 2 (by rfl) ⟨601971, by rfl⟩ : syracuseStep 1605257 = 1203943) B1203943
theorem B2686729 : Blo 207808 2686729 := bstep (se 2 (by rfl) ⟨1007523, by rfl⟩ : syracuseStep 2686729 = 2015047) B2015047
theorem B14418107 : Blo 207808 14418107 := bstep (se 1 (by rfl) ⟨10813580, by rfl⟩ : syracuseStep 14418107 = 21627161) B21627161
theorem B3408317 : Blo 207808 3408317 := bstep (se 3 (by rfl) ⟨639059, by rfl⟩ : syracuseStep 3408317 = 1278119) B1278119
theorem B526763 : Blo 207808 526763 := bstep (se 1 (by rfl) ⟨395072, by rfl⟩ : syracuseStep 526763 = 790145) B790145
theorem B1510363 : Blo 207808 1510363 := bstep (se 1 (by rfl) ⟨1132772, by rfl⟩ : syracuseStep 1510363 = 2265545) B2265545
theorem B888043 : Blo 207808 888043 := bstep (se 1 (by rfl) ⟨666032, by rfl⟩ : syracuseStep 888043 = 1332065) B1332065
theorem B888367 : Blo 207808 888367 := bstep (se 1 (by rfl) ⟨666275, by rfl⟩ : syracuseStep 888367 = 1332551) B1332551
theorem B3608549 : Blo 207808 3608549 := bstep (se 4 (by rfl) ⟨338301, by rfl⟩ : syracuseStep 3608549 = 676603) B676603
theorem B3051755 : Blo 207808 3051755 := bstep (se 1 (by rfl) ⟨2288816, by rfl⟩ : syracuseStep 3051755 = 4577633) B4577633
theorem B233959 : Blo 207808 233959 := bstep (se 1 (by rfl) ⟨175469, by rfl⟩ : syracuseStep 233959 = 350939) B350939
theorem B52795475 : Blo 207808 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B9640673 : Blo 207808 9640673 := bstep (se 2 (by rfl) ⟨3615252, by rfl⟩ : syracuseStep 9640673 = 7230505) B7230505
theorem B335099 : Blo 207808 335099 := bstep (se 1 (by rfl) ⟨251324, by rfl⟩ : syracuseStep 335099 = 502649) B502649
theorem B892691 : Blo 207808 892691 := bstep (se 1 (by rfl) ⟨669518, by rfl⟩ : syracuseStep 892691 = 1339037) B1339037
theorem B237631 : Blo 207808 237631 := bstep (se 1 (by rfl) ⟨178223, by rfl⟩ : syracuseStep 237631 = 356447) B356447
theorem B1712353 : Blo 207808 1712353 := bstep (se 2 (by rfl) ⟨642132, by rfl⟩ : syracuseStep 1712353 = 1284265) B1284265
theorem B3383531 : Blo 207808 3383531 := bstep (se 1 (by rfl) ⟨2537648, by rfl⟩ : syracuseStep 3383531 = 5075297) B5075297
theorem B468143 : Blo 207808 468143 := bstep (se 1 (by rfl) ⟨351107, by rfl⟩ : syracuseStep 468143 = 702215) B702215
theorem B4269469 : Blo 207808 4269469 := bstep (se 3 (by rfl) ⟨800525, by rfl⟩ : syracuseStep 4269469 = 1601051) B1601051
theorem B2270825 : Blo 207808 2270825 := bstep (se 2 (by rfl) ⟨851559, by rfl⟩ : syracuseStep 2270825 = 1703119) B1703119
theorem B895151 : Blo 207808 895151 := bstep (se 1 (by rfl) ⟨671363, by rfl⟩ : syracuseStep 895151 = 1342727) B1342727
theorem B3582305 : Blo 207808 3582305 := bstep (se 2 (by rfl) ⟨1343364, by rfl⟩ : syracuseStep 3582305 = 2686729) B2686729
theorem B207871 : Blo 207808 207871 := bstep (se 1 (by rfl) ⟨155903, by rfl⟩ : syracuseStep 207871 = 311807) B311807
theorem B634169 : Blo 207808 634169 := bstep (se 2 (by rfl) ⟨237813, by rfl⟩ : syracuseStep 634169 = 475627) B475627
theorem B208367 : Blo 207808 208367 := bstep (se 1 (by rfl) ⟨156275, by rfl⟩ : syracuseStep 208367 = 312551) B312551
theorem B208383 : Blo 207808 208383 := bstep (se 1 (by rfl) ⟨156287, by rfl⟩ : syracuseStep 208383 = 312575) B312575
theorem B601631 : Blo 207808 601631 := bstep (se 1 (by rfl) ⟨451223, by rfl⟩ : syracuseStep 601631 = 902447) B902447
theorem B209087 : Blo 207808 209087 := bstep (se 1 (by rfl) ⟨156815, by rfl⟩ : syracuseStep 209087 = 313631) B313631
theorem B471275 : Blo 207808 471275 := bstep (se 1 (by rfl) ⟨353456, by rfl⟩ : syracuseStep 471275 = 706913) B706913
theorem B209311 : Blo 207808 209311 := bstep (se 1 (by rfl) ⟨156983, by rfl⟩ : syracuseStep 209311 = 313967) B313967
theorem B471599 : Blo 207808 471599 := bstep (se 1 (by rfl) ⟨353699, by rfl⟩ : syracuseStep 471599 = 707399) B707399
theorem B209567 : Blo 207808 209567 := bstep (se 1 (by rfl) ⟨157175, by rfl⟩ : syracuseStep 209567 = 314351) B314351
theorem B504647 : Blo 207808 504647 := bstep (se 1 (by rfl) ⟨378485, by rfl⟩ : syracuseStep 504647 = 756971) B756971
theorem B668699 : Blo 207808 668699 := bstep (se 1 (by rfl) ⟨501524, by rfl⟩ : syracuseStep 668699 = 1003049) B1003049
theorem B210367 : Blo 207808 210367 := bstep (se 1 (by rfl) ⟨157775, by rfl⟩ : syracuseStep 210367 = 315551) B315551
theorem B210399 : Blo 207808 210399 := bstep (se 1 (by rfl) ⟨157799, by rfl⟩ : syracuseStep 210399 = 315599) B315599
theorem B210431 : Blo 207808 210431 := bstep (se 1 (by rfl) ⟨157823, by rfl⟩ : syracuseStep 210431 = 315647) B315647
theorem B472697 : Blo 207808 472697 := bstep (se 2 (by rfl) ⟨177261, by rfl⟩ : syracuseStep 472697 = 354523) B354523
theorem B407215 : Blo 207808 407215 := bstep (se 1 (by rfl) ⟨305411, by rfl⟩ : syracuseStep 407215 = 610823) B610823
theorem B210715 : Blo 207808 210715 := bstep (se 1 (by rfl) ⟨158036, by rfl⟩ : syracuseStep 210715 = 316073) B316073
theorem B210799 : Blo 207808 210799 := bstep (se 1 (by rfl) ⟨158099, by rfl⟩ : syracuseStep 210799 = 316199) B316199
theorem B210855 : Blo 207808 210855 := bstep (se 1 (by rfl) ⟨158141, by rfl⟩ : syracuseStep 210855 = 316283) B316283
theorem B211303 : Blo 207808 211303 := bstep (se 1 (by rfl) ⟨158477, by rfl⟩ : syracuseStep 211303 = 316955) B316955
theorem B506351 : Blo 207808 506351 := bstep (se 1 (by rfl) ⟨379763, by rfl⟩ : syracuseStep 506351 = 759527) B759527
theorem B899849 : Blo 207808 899849 := bstep (se 2 (by rfl) ⟨337443, by rfl⟩ : syracuseStep 899849 = 674887) B674887
theorem B6011927 : Blo 207808 6011927 := bstep (se 1 (by rfl) ⟨4508945, by rfl⟩ : syracuseStep 6011927 = 9017891) B9017891
theorem B572441 : Blo 207808 572441 := bstep (se 2 (by rfl) ⟨214665, by rfl⟩ : syracuseStep 572441 = 429331) B429331
theorem B474281 : Blo 207808 474281 := bstep (se 2 (by rfl) ⟨177855, by rfl⟩ : syracuseStep 474281 = 355711) B355711
theorem B1785959 : Blo 207808 1785959 := bstep (se 1 (by rfl) ⟨1339469, by rfl⟩ : syracuseStep 1785959 = 2678939) B2678939
theorem B901439 : Blo 207808 901439 := bstep (se 1 (by rfl) ⟨676079, by rfl⟩ : syracuseStep 901439 = 1352159) B1352159
theorem B1851815 : Blo 207808 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B3686849 : Blo 207808 3686849 := bstep (se 2 (by rfl) ⟨1382568, by rfl⟩ : syracuseStep 3686849 = 2765137) B2765137
theorem B803267 : Blo 207808 803267 := bstep (se 1 (by rfl) ⟨602450, by rfl⟩ : syracuseStep 803267 = 1204901) B1204901
theorem B705023 : Blo 207808 705023 := bstep (se 1 (by rfl) ⟨528767, by rfl⟩ : syracuseStep 705023 = 1057535) B1057535
theorem B312167 : Blo 207808 312167 := bstep (se 1 (by rfl) ⟨234125, by rfl⟩ : syracuseStep 312167 = 468251) B468251
theorem B476063 : Blo 207808 476063 := bstep (se 1 (by rfl) ⟨357047, by rfl⟩ : syracuseStep 476063 = 714095) B714095
theorem B902123 : Blo 207808 902123 := bstep (se 1 (by rfl) ⟨676592, by rfl⟩ : syracuseStep 902123 = 1353185) B1353185
theorem B313001 : Blo 207808 313001 := bstep (se 2 (by rfl) ⟨117375, by rfl⟩ : syracuseStep 313001 = 234751) B234751
theorem B313703 : Blo 207808 313703 := bstep (se 1 (by rfl) ⟨235277, by rfl⟩ : syracuseStep 313703 = 470555) B470555
theorem B6015617 : Blo 207808 6015617 := bstep (se 2 (by rfl) ⟨2255856, by rfl⟩ : syracuseStep 6015617 = 4511713) B4511713
theorem B314087 : Blo 207808 314087 := bstep (se 1 (by rfl) ⟨235565, by rfl⟩ : syracuseStep 314087 = 471131) B471131
theorem B314249 : Blo 207808 314249 := bstep (se 2 (by rfl) ⟨117843, by rfl⟩ : syracuseStep 314249 = 235687) B235687
theorem B707561 : Blo 207808 707561 := bstep (se 2 (by rfl) ⟨265335, by rfl⟩ : syracuseStep 707561 = 530671) B530671
theorem B1199387 : Blo 207808 1199387 := bstep (se 1 (by rfl) ⟨899540, by rfl⟩ : syracuseStep 1199387 = 1799081) B1799081
theorem B708587 : Blo 207808 708587 := bstep (se 1 (by rfl) ⟨531440, by rfl⟩ : syracuseStep 708587 = 1062881) B1062881
theorem B315575 : Blo 207808 315575 := bstep (se 1 (by rfl) ⟨236681, by rfl⟩ : syracuseStep 315575 = 473363) B473363
theorem B1528141 : Blo 207808 1528141 := bstep (se 3 (by rfl) ⟨286526, by rfl⟩ : syracuseStep 1528141 = 573053) B573053
theorem B447481 : Blo 207808 447481 := bstep (se 2 (by rfl) ⟨167805, by rfl⟩ : syracuseStep 447481 = 335611) B335611
theorem B316409 : Blo 207808 316409 := bstep (se 2 (by rfl) ⟨118653, by rfl⟩ : syracuseStep 316409 = 237307) B237307
theorem B1070171 : Blo 207808 1070171 := bstep (se 1 (by rfl) ⟨802628, by rfl⟩ : syracuseStep 1070171 = 1605257) B1605257
theorem B316607 : Blo 207808 316607 := bstep (se 1 (by rfl) ⟨237455, by rfl⟩ : syracuseStep 316607 = 474911) B474911
theorem B316655 : Blo 207808 316655 := bstep (se 1 (by rfl) ⟨237491, by rfl⟩ : syracuseStep 316655 = 474983) B474983
theorem B710369 : Blo 207808 710369 := bstep (se 2 (by rfl) ⟨266388, by rfl⟩ : syracuseStep 710369 = 532777) B532777
theorem B874259 : Blo 207808 874259 := bstep (se 1 (by rfl) ⟨655694, by rfl⟩ : syracuseStep 874259 = 1311389) B1311389
theorem B809183 : Blo 207808 809183 := bstep (se 1 (by rfl) ⟨606887, by rfl⟩ : syracuseStep 809183 = 1213775) B1213775
theorem B23320871 : Blo 207808 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B351263 : Blo 207808 351263 := bstep (se 1 (by rfl) ⟨263447, by rfl⟩ : syracuseStep 351263 = 526895) B526895
theorem B1339163 : Blo 207808 1339163 := bstep (se 1 (by rfl) ⟨1004372, by rfl⟩ : syracuseStep 1339163 = 2008745) B2008745
theorem B1535867 : Blo 207808 1535867 := bstep (se 1 (by rfl) ⟨1151900, by rfl⟩ : syracuseStep 1535867 = 2303801) B2303801
theorem B1373231 : Blo 207808 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B5406263 : Blo 207808 5406263 := bstep (se 1 (by rfl) ⟨4054697, by rfl⟩ : syracuseStep 5406263 = 8109395) B8109395
theorem B2457899 : Blo 207808 2457899 := bstep (se 1 (by rfl) ⟨1843424, by rfl⟩ : syracuseStep 2457899 = 3686849) B3686849
theorem B2034503 : Blo 207808 2034503 := bstep (se 1 (by rfl) ⟨1525877, by rfl⟩ : syracuseStep 2034503 = 3051755) B3051755
theorem B35196983 : Blo 207808 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B1184057 : Blo 207808 1184057 := bstep (se 2 (by rfl) ⟨444021, by rfl⟩ : syracuseStep 1184057 = 888043) B888043
theorem B6427115 : Blo 207808 6427115 := bstep (se 1 (by rfl) ⟨4820336, by rfl⟩ : syracuseStep 6427115 = 9640673) B9640673
theorem B234175 : Blo 207808 234175 := bstep (se 1 (by rfl) ⟨175631, by rfl⟩ : syracuseStep 234175 = 351263) B351263
theorem B1184489 : Blo 207808 1184489 := bstep (se 2 (by rfl) ⟨444183, by rfl⟩ : syracuseStep 1184489 = 888367) B888367
theorem B595127 : Blo 207808 595127 := bstep (se 1 (by rfl) ⟨446345, by rfl⟩ : syracuseStep 595127 = 892691) B892691
theorem B2037521 : Blo 207808 2037521 := bstep (se 2 (by rfl) ⟨764070, by rfl⟩ : syracuseStep 2037521 = 1528141) B1528141
theorem B1513883 : Blo 207808 1513883 := bstep (se 1 (by rfl) ⟨1135412, by rfl⟩ : syracuseStep 1513883 = 2270825) B2270825
theorem B596641 : Blo 207808 596641 := bstep (se 2 (by rfl) ⟨223740, by rfl⟩ : syracuseStep 596641 = 447481) B447481
theorem B596767 : Blo 207808 596767 := bstep (se 1 (by rfl) ⟨447575, by rfl⟩ : syracuseStep 596767 = 895151) B895151
theorem B401087 : Blo 207808 401087 := bstep (se 1 (by rfl) ⟨300815, by rfl⟩ : syracuseStep 401087 = 601631) B601631
theorem B892775 : Blo 207808 892775 := bstep (se 1 (by rfl) ⟨669581, by rfl⟩ : syracuseStep 892775 = 1339163) B1339163
theorem B1023911 : Blo 207808 1023911 := bstep (se 1 (by rfl) ⟨767933, by rfl⟩ : syracuseStep 1023911 = 1535867) B1535867
theorem B336431 : Blo 207808 336431 := bstep (se 1 (by rfl) ⟨252323, by rfl⟩ : syracuseStep 336431 = 504647) B504647
theorem B337567 : Blo 207808 337567 := bstep (se 1 (by rfl) ⟨253175, by rfl⟩ : syracuseStep 337567 = 506351) B506351
theorem B599899 : Blo 207808 599899 := bstep (se 1 (by rfl) ⟨449924, by rfl⟩ : syracuseStep 599899 = 899849) B899849
theorem B4007951 : Blo 207808 4007951 := bstep (se 1 (by rfl) ⟨3005963, by rfl⟩ : syracuseStep 4007951 = 6011927) B6011927
theorem B1190639 : Blo 207808 1190639 := bstep (se 1 (by rfl) ⟨892979, by rfl⟩ : syracuseStep 1190639 = 1785959) B1785959
theorem B9612071 : Blo 207808 9612071 := bstep (se 1 (by rfl) ⟨7209053, by rfl⟩ : syracuseStep 9612071 = 14418107) B14418107
theorem B600959 : Blo 207808 600959 := bstep (se 1 (by rfl) ⟨450719, by rfl⟩ : syracuseStep 600959 = 901439) B901439
theorem B2272211 : Blo 207808 2272211 := bstep (se 1 (by rfl) ⟨1704158, by rfl⟩ : syracuseStep 2272211 = 3408317) B3408317
theorem B535511 : Blo 207808 535511 := bstep (se 1 (by rfl) ⟨401633, by rfl⟩ : syracuseStep 535511 = 803267) B803267
theorem B470015 : Blo 207808 470015 := bstep (se 1 (by rfl) ⟨352511, by rfl⟩ : syracuseStep 470015 = 705023) B705023
theorem B208111 : Blo 207808 208111 := bstep (se 1 (by rfl) ⟨156083, by rfl⟩ : syracuseStep 208111 = 312167) B312167
theorem B601415 : Blo 207808 601415 := bstep (se 1 (by rfl) ⟨451061, by rfl⟩ : syracuseStep 601415 = 902123) B902123
theorem B208667 : Blo 207808 208667 := bstep (se 1 (by rfl) ⟨156500, by rfl⟩ : syracuseStep 208667 = 313001) B313001
theorem B209135 : Blo 207808 209135 := bstep (se 1 (by rfl) ⟨156851, by rfl⟩ : syracuseStep 209135 = 313703) B313703
theorem B4010411 : Blo 207808 4010411 := bstep (se 1 (by rfl) ⟨3007808, by rfl⟩ : syracuseStep 4010411 = 6015617) B6015617
theorem B209391 : Blo 207808 209391 := bstep (se 1 (by rfl) ⟨157043, by rfl⟩ : syracuseStep 209391 = 314087) B314087
theorem B209499 : Blo 207808 209499 := bstep (se 1 (by rfl) ⟨157124, by rfl⟩ : syracuseStep 209499 = 314249) B314249
theorem B471707 : Blo 207808 471707 := bstep (se 1 (by rfl) ⟨353780, by rfl⟩ : syracuseStep 471707 = 707561) B707561
theorem B799591 : Blo 207808 799591 := bstep (se 1 (by rfl) ⟨599693, by rfl⟩ : syracuseStep 799591 = 1199387) B1199387
theorem B2405699 : Blo 207808 2405699 := bstep (se 1 (by rfl) ⟨1804274, by rfl⟩ : syracuseStep 2405699 = 3608549) B3608549
theorem B472391 : Blo 207808 472391 := bstep (se 1 (by rfl) ⟨354293, by rfl⟩ : syracuseStep 472391 = 708587) B708587
theorem B210383 : Blo 207808 210383 := bstep (se 1 (by rfl) ⟨157787, by rfl⟩ : syracuseStep 210383 = 315575) B315575
theorem B210939 : Blo 207808 210939 := bstep (se 1 (by rfl) ⟨158204, by rfl⟩ : syracuseStep 210939 = 316409) B316409
theorem B211071 : Blo 207808 211071 := bstep (se 1 (by rfl) ⟨158303, by rfl⟩ : syracuseStep 211071 = 316607) B316607
theorem B211103 : Blo 207808 211103 := bstep (se 1 (by rfl) ⟨158327, by rfl⟩ : syracuseStep 211103 = 316655) B316655
theorem B473579 : Blo 207808 473579 := bstep (se 1 (by rfl) ⟨355184, by rfl⟩ : syracuseStep 473579 = 710369) B710369
theorem B2013817 : Blo 207808 2013817 := bstep (se 2 (by rfl) ⟨755181, by rfl⟩ : syracuseStep 2013817 = 1510363) B1510363
theorem B539455 : Blo 207808 539455 := bstep (se 1 (by rfl) ⟨404591, by rfl⟩ : syracuseStep 539455 = 809183) B809183
theorem B15547247 : Blo 207808 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B311945 : Blo 207808 311945 := bstep (se 2 (by rfl) ⟨116979, by rfl⟩ : syracuseStep 311945 = 233959) B233959
theorem B312095 : Blo 207808 312095 := bstep (se 1 (by rfl) ⟨234071, by rfl⟩ : syracuseStep 312095 = 468143) B468143
theorem B542953 : Blo 207808 542953 := bstep (se 2 (by rfl) ⟨203607, by rfl⟩ : syracuseStep 542953 = 407215) B407215
theorem B1526509 : Blo 207808 1526509 := bstep (se 3 (by rfl) ⟨286220, by rfl⟩ : syracuseStep 1526509 = 572441) B572441
theorem B314183 : Blo 207808 314183 := bstep (se 1 (by rfl) ⟨235637, by rfl⟩ : syracuseStep 314183 = 471275) B471275
theorem B314399 : Blo 207808 314399 := bstep (se 1 (by rfl) ⟨235799, by rfl⟩ : syracuseStep 314399 = 471599) B471599
theorem B445799 : Blo 207808 445799 := bstep (se 1 (by rfl) ⟨334349, by rfl⟩ : syracuseStep 445799 = 668699) B668699
theorem B1691117 : Blo 207808 1691117 := bstep (se 3 (by rfl) ⟨317084, by rfl⟩ : syracuseStep 1691117 = 634169) B634169
theorem B315131 : Blo 207808 315131 := bstep (se 1 (by rfl) ⟨236348, by rfl⟩ : syracuseStep 315131 = 472697) B472697
theorem B316187 : Blo 207808 316187 := bstep (se 1 (by rfl) ⟨237140, by rfl⟩ : syracuseStep 316187 = 474281) B474281
theorem B316841 : Blo 207808 316841 := bstep (se 2 (by rfl) ⟨118815, by rfl⟩ : syracuseStep 316841 = 237631) B237631
theorem B1234543 : Blo 207808 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B2283137 : Blo 207808 2283137 := bstep (se 2 (by rfl) ⟨856176, by rfl⟩ : syracuseStep 2283137 = 1712353) B1712353
theorem B317375 : Blo 207808 317375 := bstep (se 1 (by rfl) ⟨238031, by rfl⟩ : syracuseStep 317375 = 476063) B476063
theorem B351175 : Blo 207808 351175 := bstep (se 1 (by rfl) ⟨263381, by rfl⟩ : syracuseStep 351175 = 526763) B526763
theorem B5692625 : Blo 207808 5692625 := bstep (se 2 (by rfl) ⟨2134734, by rfl⟩ : syracuseStep 5692625 = 4269469) B4269469
theorem B3661949 : Blo 207808 3661949 := bstep (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) B1373231
theorem B713447 : Blo 207808 713447 := bstep (se 1 (by rfl) ⟨535085, by rfl⟩ : syracuseStep 713447 = 1070171) B1070171
theorem B582839 : Blo 207808 582839 := bstep (se 1 (by rfl) ⟨437129, by rfl⟩ : syracuseStep 582839 = 874259) B874259
theorem B223399 : Blo 207808 223399 := bstep (se 1 (by rfl) ⟨167549, by rfl⟩ : syracuseStep 223399 = 335099) B335099
theorem B2255687 : Blo 207808 2255687 := bstep (se 1 (by rfl) ⟨1691765, by rfl⟩ : syracuseStep 2255687 = 3383531) B3383531
theorem B2388203 : Blo 207808 2388203 := bstep (se 1 (by rfl) ⟨1791152, by rfl⟩ : syracuseStep 2388203 = 3582305) B3582305
theorem B3604175 : Blo 207808 3604175 := bstep (se 1 (by rfl) ⟨2703131, by rfl⟩ : syracuseStep 3604175 = 5406263) B5406263
theorem B1638599 : Blo 207808 1638599 := bstep (se 1 (by rfl) ⟨1228949, by rfl⟩ : syracuseStep 1638599 = 2457899) B2457899
theorem B9765197 : Blo 207808 9765197 := bstep (se 3 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 9765197 = 3661949) B3661949
theorem B297199 : Blo 207808 297199 := bstep (se 1 (by rfl) ⟨222899, by rfl⟩ : syracuseStep 297199 = 445799) B445799
theorem B23464655 : Blo 207808 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B789371 : Blo 207808 789371 := bstep (se 1 (by rfl) ⟨592028, by rfl⟩ : syracuseStep 789371 = 1184057) B1184057
theorem B297865 : Blo 207808 297865 := bstep (se 2 (by rfl) ⟨111699, by rfl⟩ : syracuseStep 297865 = 223399) B223399
theorem B789659 : Blo 207808 789659 := bstep (se 1 (by rfl) ⟨592244, by rfl⟩ : syracuseStep 789659 = 1184489) B1184489
theorem B396751 : Blo 207808 396751 := bstep (se 1 (by rfl) ⟨297563, by rfl⟩ : syracuseStep 396751 = 595127) B595127
theorem B267391 : Blo 207808 267391 := bstep (se 1 (by rfl) ⟨200543, by rfl⟩ : syracuseStep 267391 = 401087) B401087
theorem B595183 : Blo 207808 595183 := bstep (se 1 (by rfl) ⟨446387, by rfl⟩ : syracuseStep 595183 = 892775) B892775
theorem B793759 : Blo 207808 793759 := bstep (se 1 (by rfl) ⟨595319, by rfl⟩ : syracuseStep 793759 = 1190639) B1190639
theorem B400639 : Blo 207808 400639 := bstep (se 1 (by rfl) ⟨300479, by rfl⟩ : syracuseStep 400639 = 600959) B600959
theorem B1514807 : Blo 207808 1514807 := bstep (se 1 (by rfl) ⟨1136105, by rfl⟩ : syracuseStep 1514807 = 2272211) B2272211
theorem B1646057 : Blo 207808 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B400943 : Blo 207808 400943 := bstep (se 1 (by rfl) ⟨300707, by rfl⟩ : syracuseStep 400943 = 601415) B601415
theorem B795521 : Blo 207808 795521 := bstep (se 2 (by rfl) ⟨298320, by rfl⟩ : syracuseStep 795521 = 596641) B596641
theorem B795689 : Blo 207808 795689 := bstep (se 2 (by rfl) ⟨298383, by rfl⟩ : syracuseStep 795689 = 596767) B596767
theorem B468233 : Blo 207808 468233 := bstep (se 2 (by rfl) ⟨175587, by rfl⟩ : syracuseStep 468233 = 351175) B351175
theorem B10364831 : Blo 207808 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B2402783 : Blo 207808 2402783 := bstep (se 1 (by rfl) ⟨1802087, by rfl⟩ : syracuseStep 2402783 = 3604175) B3604175
theorem B207963 : Blo 207808 207963 := bstep (se 1 (by rfl) ⟨155972, by rfl⟩ : syracuseStep 207963 = 311945) B311945
theorem B208063 : Blo 207808 208063 := bstep (se 1 (by rfl) ⟨156047, by rfl⟩ : syracuseStep 208063 = 312095) B312095
theorem B2895749 : Blo 207808 2895749 := bstep (se 4 (by rfl) ⟨271476, by rfl⟩ : syracuseStep 2895749 = 542953) B542953
theorem B897149 : Blo 207808 897149 := bstep (se 3 (by rfl) ⟨168215, by rfl⟩ : syracuseStep 897149 = 336431) B336431
theorem B209455 : Blo 207808 209455 := bstep (se 1 (by rfl) ⟨157091, by rfl⟩ : syracuseStep 209455 = 314183) B314183
theorem B1356335 : Blo 207808 1356335 := bstep (se 1 (by rfl) ⟨1017251, by rfl⟩ : syracuseStep 1356335 = 2034503) B2034503
theorem B209599 : Blo 207808 209599 := bstep (se 1 (by rfl) ⟨157199, by rfl⟩ : syracuseStep 209599 = 314399) B314399
theorem B1127411 : Blo 207808 1127411 := bstep (se 1 (by rfl) ⟨845558, by rfl⟩ : syracuseStep 1127411 = 1691117) B1691117
theorem B799865 : Blo 207808 799865 := bstep (se 2 (by rfl) ⟨299949, by rfl⟩ : syracuseStep 799865 = 599899) B599899
theorem B210087 : Blo 207808 210087 := bstep (se 1 (by rfl) ⟨157565, by rfl⟩ : syracuseStep 210087 = 315131) B315131
theorem B210791 : Blo 207808 210791 := bstep (se 1 (by rfl) ⟨158093, by rfl⟩ : syracuseStep 210791 = 316187) B316187
theorem B211227 : Blo 207808 211227 := bstep (se 1 (by rfl) ⟨158420, by rfl⟩ : syracuseStep 211227 = 316841) B316841
theorem B1522091 : Blo 207808 1522091 := bstep (se 1 (by rfl) ⟨1141568, by rfl⟩ : syracuseStep 1522091 = 2283137) B2283137
theorem B8141381 : Blo 207808 8141381 := bstep (se 4 (by rfl) ⟨763254, by rfl⟩ : syracuseStep 8141381 = 1526509) B1526509
theorem B211583 : Blo 207808 211583 := bstep (se 1 (by rfl) ⟨158687, by rfl⟩ : syracuseStep 211583 = 317375) B317375
theorem B475631 : Blo 207808 475631 := bstep (se 1 (by rfl) ⟨356723, by rfl⟩ : syracuseStep 475631 = 713447) B713447
theorem B312233 : Blo 207808 312233 := bstep (se 2 (by rfl) ⟨117087, by rfl⟩ : syracuseStep 312233 = 234175) B234175
theorem B1066121 : Blo 207808 1066121 := bstep (se 2 (by rfl) ⟨399795, by rfl⟩ : syracuseStep 1066121 = 799591) B799591
theorem B2671967 : Blo 207808 2671967 := bstep (se 1 (by rfl) ⟨2003975, by rfl⟩ : syracuseStep 2671967 = 4007951) B4007951
theorem B6408047 : Blo 207808 6408047 := bstep (se 1 (by rfl) ⟨4806035, by rfl⟩ : syracuseStep 6408047 = 9612071) B9612071
theorem B313343 : Blo 207808 313343 := bstep (se 1 (by rfl) ⟨235007, by rfl⟩ : syracuseStep 313343 = 470015) B470015
theorem B1592135 : Blo 207808 1592135 := bstep (se 1 (by rfl) ⟨1194101, by rfl⟩ : syracuseStep 1592135 = 2388203) B2388203
theorem B2673607 : Blo 207808 2673607 := bstep (se 1 (by rfl) ⟨2005205, by rfl⟩ : syracuseStep 2673607 = 4010411) B4010411
theorem B314471 : Blo 207808 314471 := bstep (se 1 (by rfl) ⟨235853, by rfl⟩ : syracuseStep 314471 = 471707) B471707
theorem B314927 : Blo 207808 314927 := bstep (se 1 (by rfl) ⟨236195, by rfl⟩ : syracuseStep 314927 = 472391) B472391
theorem B315719 : Blo 207808 315719 := bstep (se 1 (by rfl) ⟨236789, by rfl⟩ : syracuseStep 315719 = 473579) B473579
theorem B450089 : Blo 207808 450089 := bstep (se 2 (by rfl) ⟨168783, by rfl⟩ : syracuseStep 450089 = 337567) B337567
theorem B4284743 : Blo 207808 4284743 := bstep (se 1 (by rfl) ⟨3213557, by rfl⟩ : syracuseStep 4284743 = 6427115) B6427115
theorem B1009255 : Blo 207808 1009255 := bstep (se 1 (by rfl) ⟨756941, by rfl⟩ : syracuseStep 1009255 = 1513883) B1513883
theorem B5433389 : Blo 207808 5433389 := bstep (se 3 (by rfl) ⟨1018760, by rfl⟩ : syracuseStep 5433389 = 2037521) B2037521
theorem B3795083 : Blo 207808 3795083 := bstep (se 1 (by rfl) ⟨2846312, by rfl⟩ : syracuseStep 3795083 = 5692625) B5692625
theorem B682607 : Blo 207808 682607 := bstep (se 1 (by rfl) ⟨511955, by rfl⟩ : syracuseStep 682607 = 1023911) B1023911
theorem B388559 : Blo 207808 388559 := bstep (se 1 (by rfl) ⟨291419, by rfl⟩ : syracuseStep 388559 = 582839) B582839
theorem B1503791 : Blo 207808 1503791 := bstep (se 1 (by rfl) ⟨1127843, by rfl⟩ : syracuseStep 1503791 = 2255687) B2255687
theorem B357007 : Blo 207808 357007 := bstep (se 1 (by rfl) ⟨267755, by rfl⟩ : syracuseStep 357007 = 535511) B535511
theorem B2685089 : Blo 207808 2685089 := bstep (se 2 (by rfl) ⟨1006908, by rfl⟩ : syracuseStep 2685089 = 2013817) B2013817
theorem B1603799 : Blo 207808 1603799 := bstep (se 1 (by rfl) ⟨1202849, by rfl⟩ : syracuseStep 1603799 = 2405699) B2405699
theorem B719273 : Blo 207808 719273 := bstep (se 2 (by rfl) ⟨269727, by rfl⟩ : syracuseStep 719273 = 539455) B539455
theorem B526247 : Blo 207808 526247 := bstep (se 1 (by rfl) ⟨394685, by rfl⟩ : syracuseStep 526247 = 789371) B789371
theorem B526439 : Blo 207808 526439 := bstep (se 1 (by rfl) ⟨394829, by rfl⟩ : syracuseStep 526439 = 789659) B789659
theorem B1345673 : Blo 207808 1345673 := bstep (se 2 (by rfl) ⟨504627, by rfl⟩ : syracuseStep 1345673 = 1009255) B1009255
theorem B396265 : Blo 207808 396265 := bstep (se 2 (by rfl) ⟨148599, by rfl⟩ : syracuseStep 396265 = 297199) B297199
theorem B397153 : Blo 207808 397153 := bstep (se 2 (by rfl) ⟨148932, by rfl⟩ : syracuseStep 397153 = 297865) B297865
theorem B529001 : Blo 207808 529001 := bstep (se 2 (by rfl) ⟨198375, by rfl⟩ : syracuseStep 529001 = 396751) B396751
theorem B300059 : Blo 207808 300059 := bstep (se 1 (by rfl) ⟨225044, by rfl⟩ : syracuseStep 300059 = 450089) B450089
theorem B267295 : Blo 207808 267295 := bstep (se 1 (by rfl) ⟨200471, by rfl⟩ : syracuseStep 267295 = 400943) B400943
theorem B530347 : Blo 207808 530347 := bstep (se 1 (by rfl) ⟨397760, by rfl⟩ : syracuseStep 530347 = 795521) B795521
theorem B530459 : Blo 207808 530459 := bstep (se 1 (by rfl) ⟨397844, by rfl⟩ : syracuseStep 530459 = 795689) B795689
theorem B2530055 : Blo 207808 2530055 := bstep (se 1 (by rfl) ⟨1897541, by rfl⟩ : syracuseStep 2530055 = 3795083) B3795083
theorem B793577 : Blo 207808 793577 := bstep (se 2 (by rfl) ⟨297591, by rfl⟩ : syracuseStep 793577 = 595183) B595183
theorem B598099 : Blo 207808 598099 := bstep (se 1 (by rfl) ⟨448574, by rfl⟩ : syracuseStep 598099 = 897149) B897149
theorem B533243 : Blo 207808 533243 := bstep (se 1 (by rfl) ⟨399932, by rfl⟩ : syracuseStep 533243 = 799865) B799865
theorem B1058345 : Blo 207808 1058345 := bstep (se 2 (by rfl) ⟨396879, by rfl⟩ : syracuseStep 1058345 = 793759) B793759
theorem B534185 : Blo 207808 534185 := bstep (se 2 (by rfl) ⟨200319, by rfl⟩ : syracuseStep 534185 = 400639) B400639
theorem B208155 : Blo 207808 208155 := bstep (se 1 (by rfl) ⟨156116, by rfl⟩ : syracuseStep 208155 = 312233) B312233
theorem B1781311 : Blo 207808 1781311 := bstep (se 1 (by rfl) ⟨1335983, by rfl⟩ : syracuseStep 1781311 = 2671967) B2671967
theorem B4272031 : Blo 207808 4272031 := bstep (se 1 (by rfl) ⟨3204023, by rfl⟩ : syracuseStep 4272031 = 6408047) B6408047
theorem B208895 : Blo 207808 208895 := bstep (se 1 (by rfl) ⟨156671, by rfl⟩ : syracuseStep 208895 = 313343) B313343
theorem B15643103 : Blo 207808 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B1061423 : Blo 207808 1061423 := bstep (se 1 (by rfl) ⟨796067, by rfl⟩ : syracuseStep 1061423 = 1592135) B1592135
theorem B209647 : Blo 207808 209647 := bstep (se 1 (by rfl) ⟨157235, by rfl⟩ : syracuseStep 209647 = 314471) B314471
theorem B17478389 : Blo 207808 17478389 := bstep (se 5 (by rfl) ⟨819299, by rfl⟩ : syracuseStep 17478389 = 1638599) B1638599
theorem B209951 : Blo 207808 209951 := bstep (se 1 (by rfl) ⟨157463, by rfl⟩ : syracuseStep 209951 = 314927) B314927
theorem B210479 : Blo 207808 210479 := bstep (se 1 (by rfl) ⟨157859, by rfl⟩ : syracuseStep 210479 = 315719) B315719
theorem B1097371 : Blo 207808 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B312155 : Blo 207808 312155 := bstep (se 1 (by rfl) ⟨234116, by rfl⟩ : syracuseStep 312155 = 468233) B468233
theorem B476009 : Blo 207808 476009 := bstep (se 2 (by rfl) ⟨178503, by rfl⟩ : syracuseStep 476009 = 357007) B357007
theorem B3622259 : Blo 207808 3622259 := bstep (se 1 (by rfl) ⟨2716694, by rfl⟩ : syracuseStep 3622259 = 5433389) B5433389
theorem B1002527 : Blo 207808 1002527 := bstep (se 1 (by rfl) ⟨751895, by rfl⟩ : syracuseStep 1002527 = 1503791) B1503791
theorem B904223 : Blo 207808 904223 := bstep (se 1 (by rfl) ⟨678167, by rfl⟩ : syracuseStep 904223 = 1356335) B1356335
theorem B1790059 : Blo 207808 1790059 := bstep (se 1 (by rfl) ⟨1342544, by rfl⟩ : syracuseStep 1790059 = 2685089) B2685089
theorem B1069199 : Blo 207808 1069199 := bstep (se 1 (by rfl) ⟨801899, by rfl⟩ : syracuseStep 1069199 = 1603799) B1603799
theorem B479515 : Blo 207808 479515 := bstep (se 1 (by rfl) ⟨359636, by rfl⟩ : syracuseStep 479515 = 719273) B719273
theorem B5427587 : Blo 207808 5427587 := bstep (se 1 (by rfl) ⟨4070690, by rfl⟩ : syracuseStep 5427587 = 8141381) B8141381
theorem B6510131 : Blo 207808 6510131 := bstep (se 1 (by rfl) ⟨4882598, by rfl⟩ : syracuseStep 6510131 = 9765197) B9765197
theorem B317087 : Blo 207808 317087 := bstep (se 1 (by rfl) ⟨237815, by rfl⟩ : syracuseStep 317087 = 475631) B475631
theorem B710747 : Blo 207808 710747 := bstep (se 1 (by rfl) ⟨533060, by rfl⟩ : syracuseStep 710747 = 1066121) B1066121
theorem B45703925 : Blo 207808 45703925 := bstep (se 5 (by rfl) ⟨2142371, by rfl⟩ : syracuseStep 45703925 = 4284743) B4284743
theorem B3564809 : Blo 207808 3564809 := bstep (se 2 (by rfl) ⟨1336803, by rfl⟩ : syracuseStep 3564809 = 2673607) B2673607
theorem B1009871 : Blo 207808 1009871 := bstep (se 1 (by rfl) ⟨757403, by rfl⟩ : syracuseStep 1009871 = 1514807) B1514807
theorem B6909887 : Blo 207808 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B356521 : Blo 207808 356521 := bstep (se 2 (by rfl) ⟨133695, by rfl⟩ : syracuseStep 356521 = 267391) B267391
theorem B1601855 : Blo 207808 1601855 := bstep (se 1 (by rfl) ⟨1201391, by rfl⟩ : syracuseStep 1601855 = 2402783) B2402783
theorem B455071 : Blo 207808 455071 := bstep (se 1 (by rfl) ⟨341303, by rfl⟩ : syracuseStep 455071 = 682607) B682607
theorem B259039 : Blo 207808 259039 := bstep (se 1 (by rfl) ⟨194279, by rfl⟩ : syracuseStep 259039 = 388559) B388559
theorem B1930499 : Blo 207808 1930499 := bstep (se 1 (by rfl) ⟨1447874, by rfl⟩ : syracuseStep 1930499 = 2895749) B2895749
theorem B751607 : Blo 207808 751607 := bstep (se 1 (by rfl) ⟨563705, by rfl⟩ : syracuseStep 751607 = 1127411) B1127411
theorem B1014727 : Blo 207808 1014727 := bstep (se 1 (by rfl) ⟨761045, by rfl⟩ : syracuseStep 1014727 = 1522091) B1522091
theorem B41714941 : Blo 207808 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B528353 : Blo 207808 528353 := bstep (se 2 (by rfl) ⟨198132, by rfl⟩ : syracuseStep 528353 = 396265) B396265
theorem B529051 : Blo 207808 529051 := bstep (se 1 (by rfl) ⟨396788, by rfl⟩ : syracuseStep 529051 = 793577) B793577
theorem B529537 : Blo 207808 529537 := bstep (se 2 (by rfl) ⟨198576, by rfl⟩ : syracuseStep 529537 = 397153) B397153
theorem B1286999 : Blo 207808 1286999 := bstep (se 1 (by rfl) ⟨965249, by rfl⟩ : syracuseStep 1286999 = 1930499) B1930499
theorem B1352969 : Blo 207808 1352969 := bstep (se 2 (by rfl) ⟨507363, by rfl⟩ : syracuseStep 1352969 = 1014727) B1014727
theorem B501071 : Blo 207808 501071 := bstep (se 1 (by rfl) ⟨375803, by rfl⟩ : syracuseStep 501071 = 751607) B751607
theorem B18426365 : Blo 207808 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B797465 : Blo 207808 797465 := bstep (se 2 (by rfl) ⟨299049, by rfl⟩ : syracuseStep 797465 = 598099) B598099
theorem B208103 : Blo 207808 208103 := bstep (se 1 (by rfl) ⟨156077, by rfl⟩ : syracuseStep 208103 = 312155) B312155
theorem B897115 : Blo 207808 897115 := bstep (se 1 (by rfl) ⟨672836, by rfl⟩ : syracuseStep 897115 = 1345673) B1345673
theorem B46609037 : Blo 207808 46609037 := bstep (se 3 (by rfl) ⟨8739194, by rfl⟩ : syracuseStep 46609037 = 17478389) B17478389
theorem B668351 : Blo 207808 668351 := bstep (se 1 (by rfl) ⟨501263, by rfl⟩ : syracuseStep 668351 = 1002527) B1002527
theorem B602815 : Blo 207808 602815 := bstep (se 1 (by rfl) ⟨452111, by rfl⟩ : syracuseStep 602815 = 904223) B904223
theorem B3618391 : Blo 207808 3618391 := bstep (se 1 (by rfl) ⟨2713793, by rfl⟩ : syracuseStep 3618391 = 5427587) B5427587
theorem B4340087 : Blo 207808 4340087 := bstep (se 1 (by rfl) ⟨3255065, by rfl⟩ : syracuseStep 4340087 = 6510131) B6510131
theorem B211391 : Blo 207808 211391 := bstep (se 1 (by rfl) ⟨158543, by rfl⟩ : syracuseStep 211391 = 317087) B317087
theorem B473831 : Blo 207808 473831 := bstep (se 1 (by rfl) ⟨355373, by rfl⟩ : syracuseStep 473831 = 710747) B710747
theorem B2375081 : Blo 207808 2375081 := bstep (se 2 (by rfl) ⟨890655, by rfl⟩ : syracuseStep 2375081 = 1781311) B1781311
theorem B475361 : Blo 207808 475361 := bstep (se 2 (by rfl) ⟨178260, by rfl⟩ : syracuseStep 475361 = 356521) B356521
theorem B639353 : Blo 207808 639353 := bstep (se 2 (by rfl) ⟨239757, by rfl⟩ : syracuseStep 639353 = 479515) B479515
theorem B606761 : Blo 207808 606761 := bstep (se 2 (by rfl) ⟨227535, by rfl⟩ : syracuseStep 606761 = 455071) B455071
theorem B2376539 : Blo 207808 2376539 := bstep (se 1 (by rfl) ⟨1782404, by rfl⟩ : syracuseStep 2376539 = 3564809) B3564809
theorem B705563 : Blo 207808 705563 := bstep (se 1 (by rfl) ⟨529172, by rfl⟩ : syracuseStep 705563 = 1058345) B1058345
theorem B345385 : Blo 207808 345385 := bstep (se 2 (by rfl) ⟨129519, by rfl⟩ : syracuseStep 345385 = 259039) B259039
theorem B673247 : Blo 207808 673247 := bstep (se 1 (by rfl) ⟨504935, by rfl⟩ : syracuseStep 673247 = 1009871) B1009871
theorem B707129 : Blo 207808 707129 := bstep (se 2 (by rfl) ⟨265173, by rfl⟩ : syracuseStep 707129 = 530347) B530347
theorem B1067903 : Blo 207808 1067903 := bstep (se 1 (by rfl) ⟨800927, by rfl⟩ : syracuseStep 1067903 = 1601855) B1601855
theorem B707615 : Blo 207808 707615 := bstep (se 1 (by rfl) ⟨530711, by rfl⟩ : syracuseStep 707615 = 1061423) B1061423
theorem B5852645 : Blo 207808 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B3200629 : Blo 207808 3200629 := bstep (se 5 (by rfl) ⟨150029, by rfl⟩ : syracuseStep 3200629 = 300059) B300059
theorem B317339 : Blo 207808 317339 := bstep (se 1 (by rfl) ⟨238004, by rfl⟩ : syracuseStep 317339 = 476009) B476009
theorem B350831 : Blo 207808 350831 := bstep (se 1 (by rfl) ⟨263123, by rfl⟩ : syracuseStep 350831 = 526247) B526247
theorem B350959 : Blo 207808 350959 := bstep (se 1 (by rfl) ⟨263219, by rfl⟩ : syracuseStep 350959 = 526439) B526439
theorem B712799 : Blo 207808 712799 := bstep (se 1 (by rfl) ⟨534599, by rfl⟩ : syracuseStep 712799 = 1069199) B1069199
theorem B352667 : Blo 207808 352667 := bstep (se 1 (by rfl) ⟨264500, by rfl⟩ : syracuseStep 352667 = 529001) B529001
theorem B9659357 : Blo 207808 9659357 := bstep (se 3 (by rfl) ⟨1811129, by rfl⟩ : syracuseStep 9659357 = 3622259) B3622259
theorem B353639 : Blo 207808 353639 := bstep (se 1 (by rfl) ⟨265229, by rfl⟩ : syracuseStep 353639 = 530459) B530459
theorem B5696041 : Blo 207808 5696041 := bstep (se 2 (by rfl) ⟨2136015, by rfl⟩ : syracuseStep 5696041 = 4272031) B4272031
theorem B2386745 : Blo 207808 2386745 := bstep (se 2 (by rfl) ⟨895029, by rfl⟩ : syracuseStep 2386745 = 1790059) B1790059
theorem B30469283 : Blo 207808 30469283 := bstep (se 1 (by rfl) ⟨22851962, by rfl⟩ : syracuseStep 30469283 = 45703925) B45703925
theorem B355495 : Blo 207808 355495 := bstep (se 1 (by rfl) ⟨266621, by rfl⟩ : syracuseStep 355495 = 533243) B533243
theorem B356123 : Blo 207808 356123 := bstep (se 1 (by rfl) ⟨267092, by rfl⟩ : syracuseStep 356123 = 534185) B534185
theorem B356393 : Blo 207808 356393 := bstep (se 2 (by rfl) ⟨133647, by rfl⟩ : syracuseStep 356393 = 267295) B267295
theorem B6746813 : Blo 207808 6746813 := bstep (se 3 (by rfl) ⟨1265027, by rfl⟩ : syracuseStep 6746813 = 2530055) B2530055
theorem B426235 : Blo 207808 426235 := bstep (se 1 (by rfl) ⟨319676, by rfl⟩ : syracuseStep 426235 = 639353) B639353
theorem B460513 : Blo 207808 460513 := bstep (se 2 (by rfl) ⟨172692, by rfl⟩ : syracuseStep 460513 = 345385) B345385
theorem B3901763 : Blo 207808 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B233887 : Blo 207808 233887 := bstep (se 1 (by rfl) ⟨175415, by rfl⟩ : syracuseStep 233887 = 350831) B350831
theorem B235111 : Blo 207808 235111 := bstep (se 1 (by rfl) ⟨176333, by rfl⟩ : syracuseStep 235111 = 352667) B352667
theorem B857999 : Blo 207808 857999 := bstep (se 1 (by rfl) ⟨643499, by rfl⟩ : syracuseStep 857999 = 1286999) B1286999
theorem B235759 : Blo 207808 235759 := bstep (se 1 (by rfl) ⟨176819, by rfl⟩ : syracuseStep 235759 = 353639) B353639
theorem B531643 : Blo 207808 531643 := bstep (se 1 (by rfl) ⟨398732, by rfl⟩ : syracuseStep 531643 = 797465) B797465
theorem B4824521 : Blo 207808 4824521 := bstep (se 2 (by rfl) ⟨1809195, by rfl⟩ : syracuseStep 4824521 = 3618391) B3618391
theorem B4267505 : Blo 207808 4267505 := bstep (se 2 (by rfl) ⟨1600314, by rfl⟩ : syracuseStep 4267505 = 3200629) B3200629
theorem B237415 : Blo 207808 237415 := bstep (se 1 (by rfl) ⟨178061, by rfl⟩ : syracuseStep 237415 = 356123) B356123
theorem B237595 : Blo 207808 237595 := bstep (se 1 (by rfl) ⟨178196, by rfl⟩ : syracuseStep 237595 = 356393) B356393
theorem B31072691 : Blo 207808 31072691 := bstep (se 1 (by rfl) ⟨23304518, by rfl⟩ : syracuseStep 31072691 = 46609037) B46609037
theorem B4497875 : Blo 207808 4497875 := bstep (se 1 (by rfl) ⟨3373406, by rfl⟩ : syracuseStep 4497875 = 6746813) B6746813
theorem B467945 : Blo 207808 467945 := bstep (se 2 (by rfl) ⟨175479, by rfl⟩ : syracuseStep 467945 = 350959) B350959
theorem B2893391 : Blo 207808 2893391 := bstep (se 1 (by rfl) ⟨2170043, by rfl⟩ : syracuseStep 2893391 = 4340087) B4340087
theorem B1583387 : Blo 207808 1583387 := bstep (se 1 (by rfl) ⟨1187540, by rfl⟩ : syracuseStep 1583387 = 2375081) B2375081
theorem B404507 : Blo 207808 404507 := bstep (se 1 (by rfl) ⟨303380, by rfl⟩ : syracuseStep 404507 = 606761) B606761
theorem B1584359 : Blo 207808 1584359 := bstep (se 1 (by rfl) ⟨1188269, by rfl⟩ : syracuseStep 1584359 = 2376539) B2376539
theorem B470375 : Blo 207808 470375 := bstep (se 1 (by rfl) ⟨352781, by rfl⟩ : syracuseStep 470375 = 705563) B705563
theorem B55619921 : Blo 207808 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B471419 : Blo 207808 471419 := bstep (se 1 (by rfl) ⟨353564, by rfl⟩ : syracuseStep 471419 = 707129) B707129
theorem B1782269 : Blo 207808 1782269 := bstep (se 3 (by rfl) ⟨334175, by rfl⟩ : syracuseStep 1782269 = 668351) B668351
theorem B471743 : Blo 207808 471743 := bstep (se 1 (by rfl) ⟨353807, by rfl⟩ : syracuseStep 471743 = 707615) B707615
theorem B211559 : Blo 207808 211559 := bstep (se 1 (by rfl) ⟨158669, by rfl⟩ : syracuseStep 211559 = 317339) B317339
theorem B473993 : Blo 207808 473993 := bstep (se 2 (by rfl) ⟨177747, by rfl⟩ : syracuseStep 473993 = 355495) B355495
theorem B475199 : Blo 207808 475199 := bstep (se 1 (by rfl) ⟨356399, by rfl⟩ : syracuseStep 475199 = 712799) B712799
theorem B1196153 : Blo 207808 1196153 := bstep (se 2 (by rfl) ⟨448557, by rfl⟩ : syracuseStep 1196153 = 897115) B897115
theorem B6439571 : Blo 207808 6439571 := bstep (se 1 (by rfl) ⟨4829678, by rfl⟩ : syracuseStep 6439571 = 9659357) B9659357
theorem B901979 : Blo 207808 901979 := bstep (se 1 (by rfl) ⟨676484, by rfl⟩ : syracuseStep 901979 = 1352969) B1352969
theorem B705401 : Blo 207808 705401 := bstep (se 2 (by rfl) ⟨264525, by rfl⟩ : syracuseStep 705401 = 529051) B529051
theorem B803753 : Blo 207808 803753 := bstep (se 2 (by rfl) ⟨301407, by rfl⟩ : syracuseStep 803753 = 602815) B602815
theorem B706049 : Blo 207808 706049 := bstep (se 2 (by rfl) ⟨264768, by rfl⟩ : syracuseStep 706049 = 529537) B529537
theorem B1591163 : Blo 207808 1591163 := bstep (se 1 (by rfl) ⟨1193372, by rfl⟩ : syracuseStep 1591163 = 2386745) B2386745
theorem B315887 : Blo 207808 315887 := bstep (se 1 (by rfl) ⟨236915, by rfl⟩ : syracuseStep 315887 = 473831) B473831
theorem B316907 : Blo 207808 316907 := bstep (se 1 (by rfl) ⟨237680, by rfl⟩ : syracuseStep 316907 = 475361) B475361
theorem B448831 : Blo 207808 448831 := bstep (se 1 (by rfl) ⟨336623, by rfl⟩ : syracuseStep 448831 = 673247) B673247
theorem B711935 : Blo 207808 711935 := bstep (se 1 (by rfl) ⟨533951, by rfl⟩ : syracuseStep 711935 = 1067903) B1067903
theorem B352235 : Blo 207808 352235 := bstep (se 1 (by rfl) ⟨264176, by rfl⟩ : syracuseStep 352235 = 528353) B528353
theorem B7594721 : Blo 207808 7594721 := bstep (se 2 (by rfl) ⟨2848020, by rfl⟩ : syracuseStep 7594721 = 5696041) B5696041
theorem B1336189 : Blo 207808 1336189 := bstep (se 3 (by rfl) ⟨250535, by rfl⟩ : syracuseStep 1336189 = 501071) B501071
theorem B12284243 : Blo 207808 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B20312855 : Blo 207808 20312855 := bstep (se 1 (by rfl) ⟨15234641, by rfl⟩ : syracuseStep 20312855 = 30469283) B30469283
theorem B4293047 : Blo 207808 4293047 := bstep (se 1 (by rfl) ⟨3219785, by rfl⟩ : syracuseStep 4293047 = 6439571) B6439571
theorem B3216347 : Blo 207808 3216347 := bstep (se 1 (by rfl) ⟨2412260, by rfl⟩ : syracuseStep 3216347 = 4824521) B4824521
theorem B234823 : Blo 207808 234823 := bstep (se 1 (by rfl) ⟨176117, by rfl⟩ : syracuseStep 234823 = 352235) B352235
theorem B1055591 : Blo 207808 1055591 := bstep (se 1 (by rfl) ⟨791693, by rfl⟩ : syracuseStep 1055591 = 1583387) B1583387
theorem B269671 : Blo 207808 269671 := bstep (se 1 (by rfl) ⟨202253, by rfl⟩ : syracuseStep 269671 = 404507) B404507
theorem B1056239 : Blo 207808 1056239 := bstep (se 1 (by rfl) ⟨792179, by rfl⟩ : syracuseStep 1056239 = 1584359) B1584359
theorem B39297109 : Blo 207808 39297109 := bstep (se 8 (by rfl) ⟨230256, by rfl⟩ : syracuseStep 39297109 = 460513) B460513
theorem B1188179 : Blo 207808 1188179 := bstep (se 1 (by rfl) ⟨891134, by rfl⟩ : syracuseStep 1188179 = 1782269) B1782269
theorem B598441 : Blo 207808 598441 := bstep (se 2 (by rfl) ⟨224415, by rfl⟩ : syracuseStep 598441 = 448831) B448831
theorem B13541903 : Blo 207808 13541903 := bstep (se 1 (by rfl) ⟨10156427, by rfl⟩ : syracuseStep 13541903 = 20312855) B20312855
theorem B797435 : Blo 207808 797435 := bstep (se 1 (by rfl) ⟨598076, by rfl⟩ : syracuseStep 797435 = 1196153) B1196153
theorem B568313 : Blo 207808 568313 := bstep (se 2 (by rfl) ⟨213117, by rfl⟩ : syracuseStep 568313 = 426235) B426235
theorem B601319 : Blo 207808 601319 := bstep (se 1 (by rfl) ⟨450989, by rfl⟩ : syracuseStep 601319 = 901979) B901979
theorem B470267 : Blo 207808 470267 := bstep (se 1 (by rfl) ⟨352700, by rfl⟩ : syracuseStep 470267 = 705401) B705401
theorem B535835 : Blo 207808 535835 := bstep (se 1 (by rfl) ⟨401876, by rfl⟩ : syracuseStep 535835 = 803753) B803753
theorem B470699 : Blo 207808 470699 := bstep (se 1 (by rfl) ⟨353024, by rfl⟩ : syracuseStep 470699 = 706049) B706049
theorem B1781585 : Blo 207808 1781585 := bstep (se 2 (by rfl) ⟨668094, by rfl⟩ : syracuseStep 1781585 = 1336189) B1336189
theorem B1060775 : Blo 207808 1060775 := bstep (se 1 (by rfl) ⟨795581, by rfl⟩ : syracuseStep 1060775 = 1591163) B1591163
theorem B2601175 : Blo 207808 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B210591 : Blo 207808 210591 := bstep (se 1 (by rfl) ⟨157943, by rfl⟩ : syracuseStep 210591 = 315887) B315887
theorem B211271 : Blo 207808 211271 := bstep (se 1 (by rfl) ⟨158453, by rfl⟩ : syracuseStep 211271 = 316907) B316907
theorem B474623 : Blo 207808 474623 := bstep (se 1 (by rfl) ⟨355967, by rfl⟩ : syracuseStep 474623 = 711935) B711935
theorem B2998583 : Blo 207808 2998583 := bstep (se 1 (by rfl) ⟨2248937, by rfl⟩ : syracuseStep 2998583 = 4497875) B4497875
theorem B5063147 : Blo 207808 5063147 := bstep (se 1 (by rfl) ⟨3797360, by rfl⟩ : syracuseStep 5063147 = 7594721) B7594721
theorem B311849 : Blo 207808 311849 := bstep (se 2 (by rfl) ⟨116943, by rfl⟩ : syracuseStep 311849 = 233887) B233887
theorem B311963 : Blo 207808 311963 := bstep (se 1 (by rfl) ⟨233972, by rfl⟩ : syracuseStep 311963 = 467945) B467945
theorem B313481 : Blo 207808 313481 := bstep (se 2 (by rfl) ⟨117555, by rfl⟩ : syracuseStep 313481 = 235111) B235111
theorem B313583 : Blo 207808 313583 := bstep (se 1 (by rfl) ⟨235187, by rfl⟩ : syracuseStep 313583 = 470375) B470375
theorem B37079947 : Blo 207808 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B314279 : Blo 207808 314279 := bstep (se 1 (by rfl) ⟨235709, by rfl⟩ : syracuseStep 314279 = 471419) B471419
theorem B314345 : Blo 207808 314345 := bstep (se 2 (by rfl) ⟨117879, by rfl⟩ : syracuseStep 314345 = 235759) B235759
theorem B314495 : Blo 207808 314495 := bstep (se 1 (by rfl) ⟨235871, by rfl⟩ : syracuseStep 314495 = 471743) B471743
theorem B708857 : Blo 207808 708857 := bstep (se 2 (by rfl) ⟨265821, by rfl⟩ : syracuseStep 708857 = 531643) B531643
theorem B315995 : Blo 207808 315995 := bstep (se 1 (by rfl) ⟨236996, by rfl⟩ : syracuseStep 315995 = 473993) B473993
theorem B316553 : Blo 207808 316553 := bstep (se 2 (by rfl) ⟨118707, by rfl⟩ : syracuseStep 316553 = 237415) B237415
theorem B316793 : Blo 207808 316793 := bstep (se 2 (by rfl) ⟨118797, by rfl⟩ : syracuseStep 316793 = 237595) B237595
theorem B316799 : Blo 207808 316799 := bstep (se 1 (by rfl) ⟨237599, by rfl⟩ : syracuseStep 316799 = 475199) B475199
theorem B82860509 : Blo 207808 82860509 := bstep (se 3 (by rfl) ⟨15536345, by rfl⟩ : syracuseStep 82860509 = 31072691) B31072691
theorem B2845003 : Blo 207808 2845003 := bstep (se 1 (by rfl) ⟨2133752, by rfl⟩ : syracuseStep 2845003 = 4267505) B4267505
theorem B2287997 : Blo 207808 2287997 := bstep (se 3 (by rfl) ⟨428999, by rfl⟩ : syracuseStep 2287997 = 857999) B857999
theorem B1928927 : Blo 207808 1928927 := bstep (se 1 (by rfl) ⟨1446695, by rfl⟩ : syracuseStep 1928927 = 2893391) B2893391
theorem B8189495 : Blo 207808 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B52396145 : Blo 207808 52396145 := bstep (se 2 (by rfl) ⟨19648554, by rfl⟩ : syracuseStep 52396145 = 39297109) B39297109
theorem B1999055 : Blo 207808 1999055 := bstep (se 1 (by rfl) ⟨1499291, by rfl⟩ : syracuseStep 1999055 = 2998583) B2998583
theorem B3375431 : Blo 207808 3375431 := bstep (se 1 (by rfl) ⟨2531573, by rfl⟩ : syracuseStep 3375431 = 5063147) B5063147
theorem B197759717 : Blo 207808 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B792119 : Blo 207808 792119 := bstep (se 1 (by rfl) ⟨594089, by rfl⟩ : syracuseStep 792119 = 1188179) B1188179
theorem B531623 : Blo 207808 531623 := bstep (se 1 (by rfl) ⟨398717, by rfl⟩ : syracuseStep 531623 = 797435) B797435
theorem B400879 : Blo 207808 400879 := bstep (se 1 (by rfl) ⟨300659, by rfl⟩ : syracuseStep 400879 = 601319) B601319
theorem B1285951 : Blo 207808 1285951 := bstep (se 1 (by rfl) ⟨964463, by rfl⟩ : syracuseStep 1285951 = 1928927) B1928927
theorem B1187723 : Blo 207808 1187723 := bstep (se 1 (by rfl) ⟨890792, by rfl⟩ : syracuseStep 1187723 = 1781585) B1781585
theorem B207899 : Blo 207808 207899 := bstep (se 1 (by rfl) ⟨155924, by rfl⟩ : syracuseStep 207899 = 311849) B311849
theorem B207975 : Blo 207808 207975 := bstep (se 1 (by rfl) ⟨155981, by rfl⟩ : syracuseStep 207975 = 311963) B311963
theorem B797921 : Blo 207808 797921 := bstep (se 2 (by rfl) ⟨299220, by rfl⟩ : syracuseStep 797921 = 598441) B598441
theorem B11448125 : Blo 207808 11448125 := bstep (se 3 (by rfl) ⟨2146523, by rfl⟩ : syracuseStep 11448125 = 4293047) B4293047
theorem B208987 : Blo 207808 208987 := bstep (se 1 (by rfl) ⟨156740, by rfl⟩ : syracuseStep 208987 = 313481) B313481
theorem B209055 : Blo 207808 209055 := bstep (se 1 (by rfl) ⟨156791, by rfl⟩ : syracuseStep 209055 = 313583) B313583
theorem B209519 : Blo 207808 209519 := bstep (se 1 (by rfl) ⟨157139, by rfl⟩ : syracuseStep 209519 = 314279) B314279
theorem B209563 : Blo 207808 209563 := bstep (se 1 (by rfl) ⟨157172, by rfl⟩ : syracuseStep 209563 = 314345) B314345
theorem B209663 : Blo 207808 209663 := bstep (se 1 (by rfl) ⟨157247, by rfl⟩ : syracuseStep 209663 = 314495) B314495
theorem B472571 : Blo 207808 472571 := bstep (se 1 (by rfl) ⟨354428, by rfl⟩ : syracuseStep 472571 = 708857) B708857
theorem B210663 : Blo 207808 210663 := bstep (se 1 (by rfl) ⟨157997, by rfl⟩ : syracuseStep 210663 = 315995) B315995
theorem B2144231 : Blo 207808 2144231 := bstep (se 1 (by rfl) ⟨1608173, by rfl⟩ : syracuseStep 2144231 = 3216347) B3216347
theorem B211035 : Blo 207808 211035 := bstep (se 1 (by rfl) ⟨158276, by rfl⟩ : syracuseStep 211035 = 316553) B316553
theorem B211195 : Blo 207808 211195 := bstep (se 1 (by rfl) ⟨158396, by rfl⟩ : syracuseStep 211195 = 316793) B316793
theorem B211199 : Blo 207808 211199 := bstep (se 1 (by rfl) ⟨158399, by rfl⟩ : syracuseStep 211199 = 316799) B316799
theorem B703727 : Blo 207808 703727 := bstep (se 1 (by rfl) ⟨527795, by rfl⟩ : syracuseStep 703727 = 1055591) B1055591
theorem B704159 : Blo 207808 704159 := bstep (se 1 (by rfl) ⟨528119, by rfl⟩ : syracuseStep 704159 = 1056239) B1056239
theorem B9027935 : Blo 207808 9027935 := bstep (se 1 (by rfl) ⟨6770951, by rfl⟩ : syracuseStep 9027935 = 13541903) B13541903
theorem B1525331 : Blo 207808 1525331 := bstep (se 1 (by rfl) ⟨1143998, by rfl⟩ : syracuseStep 1525331 = 2287997) B2287997
theorem B313097 : Blo 207808 313097 := bstep (se 2 (by rfl) ⟨117411, by rfl⟩ : syracuseStep 313097 = 234823) B234823
theorem B378875 : Blo 207808 378875 := bstep (se 1 (by rfl) ⟨284156, by rfl⟩ : syracuseStep 378875 = 568313) B568313
theorem B313511 : Blo 207808 313511 := bstep (se 1 (by rfl) ⟨235133, by rfl⟩ : syracuseStep 313511 = 470267) B470267
theorem B313799 : Blo 207808 313799 := bstep (se 1 (by rfl) ⟨235349, by rfl⟩ : syracuseStep 313799 = 470699) B470699
theorem B707183 : Blo 207808 707183 := bstep (se 1 (by rfl) ⟨530387, by rfl⟩ : syracuseStep 707183 = 1060775) B1060775
theorem B5459663 : Blo 207808 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B316415 : Blo 207808 316415 := bstep (se 1 (by rfl) ⟨237311, by rfl⟩ : syracuseStep 316415 = 474623) B474623
theorem B3793337 : Blo 207808 3793337 := bstep (se 2 (by rfl) ⟨1422501, by rfl⟩ : syracuseStep 3793337 = 2845003) B2845003
theorem B55240339 : Blo 207808 55240339 := bstep (se 1 (by rfl) ⟨41430254, by rfl⟩ : syracuseStep 55240339 = 82860509) B82860509
theorem B3468233 : Blo 207808 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B357223 : Blo 207808 357223 := bstep (se 1 (by rfl) ⟨267917, by rfl⟩ : syracuseStep 357223 = 535835) B535835
theorem B359561 : Blo 207808 359561 := bstep (se 2 (by rfl) ⟨134835, by rfl⟩ : syracuseStep 359561 = 269671) B269671
theorem B34930763 : Blo 207808 34930763 := bstep (se 1 (by rfl) ⟨26198072, by rfl⟩ : syracuseStep 34930763 = 52396145) B52396145
theorem B1016887 : Blo 207808 1016887 := bstep (se 1 (by rfl) ⟨762665, by rfl⟩ : syracuseStep 1016887 = 1525331) B1525331
theorem B528079 : Blo 207808 528079 := bstep (se 1 (by rfl) ⟨396059, by rfl⟩ : syracuseStep 528079 = 792119) B792119
theorem B791815 : Blo 207808 791815 := bstep (se 1 (by rfl) ⟨593861, by rfl⟩ : syracuseStep 791815 = 1187723) B1187723
theorem B2528891 : Blo 207808 2528891 := bstep (se 1 (by rfl) ⟨1896668, by rfl⟩ : syracuseStep 2528891 = 3793337) B3793337
theorem B531947 : Blo 207808 531947 := bstep (se 1 (by rfl) ⟨398960, by rfl⟩ : syracuseStep 531947 = 797921) B797921
theorem B2138021 : Blo 207808 2138021 := bstep (se 4 (by rfl) ⟨200439, by rfl⟩ : syracuseStep 2138021 = 400879) B400879
theorem B14559101 : Blo 207808 14559101 := bstep (se 3 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 14559101 = 5459663) B5459663
theorem B239707 : Blo 207808 239707 := bstep (se 1 (by rfl) ⟨179780, by rfl⟩ : syracuseStep 239707 = 359561) B359561
theorem B469151 : Blo 207808 469151 := bstep (se 1 (by rfl) ⟨351863, by rfl⟩ : syracuseStep 469151 = 703727) B703727
theorem B1714601 : Blo 207808 1714601 := bstep (se 2 (by rfl) ⟨642975, by rfl⟩ : syracuseStep 1714601 = 1285951) B1285951
theorem B469439 : Blo 207808 469439 := bstep (se 1 (by rfl) ⟨352079, by rfl⟩ : syracuseStep 469439 = 704159) B704159
theorem B208731 : Blo 207808 208731 := bstep (se 1 (by rfl) ⟨156548, by rfl⟩ : syracuseStep 208731 = 313097) B313097
theorem B209007 : Blo 207808 209007 := bstep (se 1 (by rfl) ⟨156755, by rfl⟩ : syracuseStep 209007 = 313511) B313511
theorem B209199 : Blo 207808 209199 := bstep (se 1 (by rfl) ⟨156899, by rfl⟩ : syracuseStep 209199 = 313799) B313799
theorem B471455 : Blo 207808 471455 := bstep (se 1 (by rfl) ⟨353591, by rfl⟩ : syracuseStep 471455 = 707183) B707183
theorem B131839811 : Blo 207808 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B210943 : Blo 207808 210943 := bstep (se 1 (by rfl) ⟨158207, by rfl⟩ : syracuseStep 210943 = 316415) B316415
theorem B476297 : Blo 207808 476297 := bstep (se 2 (by rfl) ⟨178611, by rfl⟩ : syracuseStep 476297 = 357223) B357223
theorem B2312155 : Blo 207808 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B315047 : Blo 207808 315047 := bstep (se 1 (by rfl) ⟨236285, by rfl⟩ : syracuseStep 315047 = 472571) B472571
theorem B1429487 : Blo 207808 1429487 := bstep (se 1 (by rfl) ⟨1072115, by rfl⟩ : syracuseStep 1429487 = 2144231) B2144231
theorem B1332703 : Blo 207808 1332703 := bstep (se 1 (by rfl) ⟨999527, by rfl⟩ : syracuseStep 1332703 = 1999055) B1999055
theorem B2250287 : Blo 207808 2250287 := bstep (se 1 (by rfl) ⟨1687715, by rfl⟩ : syracuseStep 2250287 = 3375431) B3375431
theorem B6018623 : Blo 207808 6018623 := bstep (se 1 (by rfl) ⟨4513967, by rfl⟩ : syracuseStep 6018623 = 9027935) B9027935
theorem B73653785 : Blo 207808 73653785 := bstep (se 2 (by rfl) ⟨27620169, by rfl⟩ : syracuseStep 73653785 = 55240339) B55240339
theorem B354415 : Blo 207808 354415 := bstep (se 1 (by rfl) ⟨265811, by rfl⟩ : syracuseStep 354415 = 531623) B531623
theorem B1010333 : Blo 207808 1010333 := bstep (se 3 (by rfl) ⟨189437, by rfl⟩ : syracuseStep 1010333 = 378875) B378875
theorem B7632083 : Blo 207808 7632083 := bstep (se 1 (by rfl) ⟨5724062, by rfl⟩ : syracuseStep 7632083 = 11448125) B11448125
theorem B3082873 : Blo 207808 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B952991 : Blo 207808 952991 := bstep (se 1 (by rfl) ⟨714743, by rfl⟩ : syracuseStep 952991 = 1429487) B1429487
theorem B9706067 : Blo 207808 9706067 := bstep (se 1 (by rfl) ⟨7279550, by rfl⟩ : syracuseStep 9706067 = 14559101) B14559101
theorem B1055753 : Blo 207808 1055753 := bstep (se 2 (by rfl) ⟨395907, by rfl⟩ : syracuseStep 1055753 = 791815) B791815
theorem B1776937 : Blo 207808 1776937 := bstep (se 2 (by rfl) ⟨666351, by rfl⟩ : syracuseStep 1776937 = 1332703) B1332703
theorem B5088055 : Blo 207808 5088055 := bstep (se 1 (by rfl) ⟨3816041, by rfl⟩ : syracuseStep 5088055 = 7632083) B7632083
theorem B87893207 : Blo 207808 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B1355849 : Blo 207808 1355849 := bstep (se 2 (by rfl) ⟨508443, by rfl⟩ : syracuseStep 1355849 = 1016887) B1016887
theorem B210031 : Blo 207808 210031 := bstep (se 1 (by rfl) ⟨157523, by rfl⟩ : syracuseStep 210031 = 315047) B315047
theorem B472553 : Blo 207808 472553 := bstep (se 2 (by rfl) ⟨177207, by rfl⟩ : syracuseStep 472553 = 354415) B354415
theorem B4012415 : Blo 207808 4012415 := bstep (se 1 (by rfl) ⟨3009311, by rfl⟩ : syracuseStep 4012415 = 6018623) B6018623
theorem B1685927 : Blo 207808 1685927 := bstep (se 1 (by rfl) ⟨1264445, by rfl⟩ : syracuseStep 1685927 = 2528891) B2528891
theorem B704105 : Blo 207808 704105 := bstep (se 2 (by rfl) ⟨264039, by rfl⟩ : syracuseStep 704105 = 528079) B528079
theorem B49102523 : Blo 207808 49102523 := bstep (se 1 (by rfl) ⟨36826892, by rfl⟩ : syracuseStep 49102523 = 73653785) B73653785
theorem B1425347 : Blo 207808 1425347 := bstep (se 1 (by rfl) ⟨1069010, by rfl⟩ : syracuseStep 1425347 = 2138021) B2138021
theorem B312767 : Blo 207808 312767 := bstep (se 1 (by rfl) ⟨234575, by rfl⟩ : syracuseStep 312767 = 469151) B469151
theorem B312959 : Blo 207808 312959 := bstep (se 1 (by rfl) ⟨234719, by rfl⟩ : syracuseStep 312959 = 469439) B469439
theorem B673555 : Blo 207808 673555 := bstep (se 1 (by rfl) ⟨505166, by rfl⟩ : syracuseStep 673555 = 1010333) B1010333
theorem B314303 : Blo 207808 314303 := bstep (se 1 (by rfl) ⟨235727, by rfl⟩ : syracuseStep 314303 = 471455) B471455
theorem B23287175 : Blo 207808 23287175 := bstep (se 1 (by rfl) ⟨17465381, by rfl⟩ : syracuseStep 23287175 = 34930763) B34930763
theorem B317531 : Blo 207808 317531 := bstep (se 1 (by rfl) ⟨238148, by rfl⟩ : syracuseStep 317531 = 476297) B476297
theorem B319609 : Blo 207808 319609 := bstep (se 2 (by rfl) ⟨119853, by rfl⟩ : syracuseStep 319609 = 239707) B239707
theorem B1500191 : Blo 207808 1500191 := bstep (se 1 (by rfl) ⟨1125143, by rfl⟩ : syracuseStep 1500191 = 2250287) B2250287
theorem B354631 : Blo 207808 354631 := bstep (se 1 (by rfl) ⟨265973, by rfl⟩ : syracuseStep 354631 = 531947) B531947
theorem B1143067 : Blo 207808 1143067 := bstep (se 1 (by rfl) ⟨857300, by rfl⟩ : syracuseStep 1143067 = 1714601) B1714601
theorem B426145 : Blo 207808 426145 := bstep (se 2 (by rfl) ⟨159804, by rfl⟩ : syracuseStep 426145 = 319609) B319609
theorem B6784073 : Blo 207808 6784073 := bstep (se 2 (by rfl) ⟨2544027, by rfl⟩ : syracuseStep 6784073 = 5088055) B5088055
theorem B58595471 : Blo 207808 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B1123951 : Blo 207808 1123951 := bstep (se 1 (by rfl) ⟨842963, by rfl⟩ : syracuseStep 1123951 = 1685927) B1685927
theorem B2369249 : Blo 207808 2369249 := bstep (se 2 (by rfl) ⟨888468, by rfl⟩ : syracuseStep 2369249 = 1776937) B1776937
theorem B469403 : Blo 207808 469403 := bstep (se 1 (by rfl) ⟨352052, by rfl⟩ : syracuseStep 469403 = 704105) B704105
theorem B208511 : Blo 207808 208511 := bstep (se 1 (by rfl) ⟨156383, by rfl⟩ : syracuseStep 208511 = 312767) B312767
theorem B208639 : Blo 207808 208639 := bstep (se 1 (by rfl) ⟨156479, by rfl⟩ : syracuseStep 208639 = 312959) B312959
theorem B635327 : Blo 207808 635327 := bstep (se 1 (by rfl) ⟨476495, by rfl⟩ : syracuseStep 635327 = 952991) B952991
theorem B209535 : Blo 207808 209535 := bstep (se 1 (by rfl) ⟨157151, by rfl⟩ : syracuseStep 209535 = 314303) B314303
theorem B898073 : Blo 207808 898073 := bstep (se 2 (by rfl) ⟨336777, by rfl⟩ : syracuseStep 898073 = 673555) B673555
theorem B472841 : Blo 207808 472841 := bstep (se 2 (by rfl) ⟨177315, by rfl⟩ : syracuseStep 472841 = 354631) B354631
theorem B4110497 : Blo 207808 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B211687 : Blo 207808 211687 := bstep (se 1 (by rfl) ⟨158765, by rfl⟩ : syracuseStep 211687 = 317531) B317531
theorem B6470711 : Blo 207808 6470711 := bstep (se 1 (by rfl) ⟨4853033, by rfl⟩ : syracuseStep 6470711 = 9706067) B9706067
theorem B703835 : Blo 207808 703835 := bstep (se 1 (by rfl) ⟨527876, by rfl⟩ : syracuseStep 703835 = 1055753) B1055753
theorem B1524089 : Blo 207808 1524089 := bstep (se 2 (by rfl) ⟨571533, by rfl⟩ : syracuseStep 1524089 = 1143067) B1143067
theorem B1000127 : Blo 207808 1000127 := bstep (se 1 (by rfl) ⟨750095, by rfl⟩ : syracuseStep 1000127 = 1500191) B1500191
theorem B903899 : Blo 207808 903899 := bstep (se 1 (by rfl) ⟨677924, by rfl⟩ : syracuseStep 903899 = 1355849) B1355849
theorem B315035 : Blo 207808 315035 := bstep (se 1 (by rfl) ⟨236276, by rfl⟩ : syracuseStep 315035 = 472553) B472553
theorem B2674943 : Blo 207808 2674943 := bstep (se 1 (by rfl) ⟨2006207, by rfl⟩ : syracuseStep 2674943 = 4012415) B4012415
theorem B15524783 : Blo 207808 15524783 := bstep (se 1 (by rfl) ⟨11643587, by rfl⟩ : syracuseStep 15524783 = 23287175) B23287175
theorem B32735015 : Blo 207808 32735015 := bstep (se 1 (by rfl) ⟨24551261, by rfl⟩ : syracuseStep 32735015 = 49102523) B49102523
theorem B950231 : Blo 207808 950231 := bstep (se 1 (by rfl) ⟨712673, by rfl⟩ : syracuseStep 950231 = 1425347) B1425347
theorem B1016059 : Blo 207808 1016059 := bstep (se 1 (by rfl) ⟨762044, by rfl⟩ : syracuseStep 1016059 = 1524089) B1524089
theorem B4522715 : Blo 207808 4522715 := bstep (se 1 (by rfl) ⟨3392036, by rfl⟩ : syracuseStep 4522715 = 6784073) B6784073
theorem B39063647 : Blo 207808 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B1579499 : Blo 207808 1579499 := bstep (se 1 (by rfl) ⟨1184624, by rfl⟩ : syracuseStep 1579499 = 2369249) B2369249
theorem B598715 : Blo 207808 598715 := bstep (se 1 (by rfl) ⟨449036, by rfl⟩ : syracuseStep 598715 = 898073) B898073
theorem B469223 : Blo 207808 469223 := bstep (se 1 (by rfl) ⟨351917, by rfl⟩ : syracuseStep 469223 = 703835) B703835
theorem B2533949 : Blo 207808 2533949 := bstep (se 3 (by rfl) ⟨475115, by rfl⟩ : syracuseStep 2533949 = 950231) B950231
theorem B568193 : Blo 207808 568193 := bstep (se 2 (by rfl) ⟨213072, by rfl⟩ : syracuseStep 568193 = 426145) B426145
theorem B666751 : Blo 207808 666751 := bstep (se 1 (by rfl) ⟨500063, by rfl⟩ : syracuseStep 666751 = 1000127) B1000127
theorem B602599 : Blo 207808 602599 := bstep (se 1 (by rfl) ⟨451949, by rfl⟩ : syracuseStep 602599 = 903899) B903899
theorem B210023 : Blo 207808 210023 := bstep (se 1 (by rfl) ⟨157517, by rfl⟩ : syracuseStep 210023 = 315035) B315035
theorem B1783295 : Blo 207808 1783295 := bstep (se 1 (by rfl) ⟨1337471, by rfl⟩ : syracuseStep 1783295 = 2674943) B2674943
theorem B312935 : Blo 207808 312935 := bstep (se 1 (by rfl) ⟨234701, by rfl⟩ : syracuseStep 312935 = 469403) B469403
theorem B315227 : Blo 207808 315227 := bstep (se 1 (by rfl) ⟨236420, by rfl⟩ : syracuseStep 315227 = 472841) B472841
theorem B2740331 : Blo 207808 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B4313807 : Blo 207808 4313807 := bstep (se 1 (by rfl) ⟨3235355, by rfl⟩ : syracuseStep 4313807 = 6470711) B6470711
theorem B1498601 : Blo 207808 1498601 := bstep (se 2 (by rfl) ⟨561975, by rfl⟩ : syracuseStep 1498601 = 1123951) B1123951
theorem B10349855 : Blo 207808 10349855 := bstep (se 1 (by rfl) ⟨7762391, by rfl⟩ : syracuseStep 10349855 = 15524783) B15524783
theorem B423551 : Blo 207808 423551 := bstep (se 1 (by rfl) ⟨317663, by rfl⟩ : syracuseStep 423551 = 635327) B635327
theorem B21823343 : Blo 207808 21823343 := bstep (se 1 (by rfl) ⟨16367507, by rfl⟩ : syracuseStep 21823343 = 32735015) B32735015
theorem B3015143 : Blo 207808 3015143 := bstep (se 1 (by rfl) ⟨2261357, by rfl⟩ : syracuseStep 3015143 = 4522715) B4522715
theorem B889001 : Blo 207808 889001 := bstep (se 2 (by rfl) ⟨333375, by rfl⟩ : syracuseStep 889001 = 666751) B666751
theorem B1052999 : Blo 207808 1052999 := bstep (se 1 (by rfl) ⟨789749, by rfl⟩ : syracuseStep 1052999 = 1579499) B1579499
theorem B399143 : Blo 207808 399143 := bstep (se 1 (by rfl) ⟨299357, by rfl⟩ : syracuseStep 399143 = 598715) B598715
theorem B1515181 : Blo 207808 1515181 := bstep (se 3 (by rfl) ⟨284096, by rfl⟩ : syracuseStep 1515181 = 568193) B568193
theorem B1188863 : Blo 207808 1188863 := bstep (se 1 (by rfl) ⟨891647, by rfl⟩ : syracuseStep 1188863 = 1783295) B1783295
theorem B1354745 : Blo 207808 1354745 := bstep (se 2 (by rfl) ⟨508029, by rfl⟩ : syracuseStep 1354745 = 1016059) B1016059
theorem B208623 : Blo 207808 208623 := bstep (se 1 (by rfl) ⟨156467, by rfl⟩ : syracuseStep 208623 = 312935) B312935
theorem B210151 : Blo 207808 210151 := bstep (se 1 (by rfl) ⟨157613, by rfl⟩ : syracuseStep 210151 = 315227) B315227
theorem B999067 : Blo 207808 999067 := bstep (se 1 (by rfl) ⟨749300, by rfl⟩ : syracuseStep 999067 = 1498601) B1498601
theorem B803465 : Blo 207808 803465 := bstep (se 2 (by rfl) ⟨301299, by rfl⟩ : syracuseStep 803465 = 602599) B602599
theorem B312815 : Blo 207808 312815 := bstep (se 1 (by rfl) ⟨234611, by rfl⟩ : syracuseStep 312815 = 469223) B469223
theorem B1689299 : Blo 207808 1689299 := bstep (se 1 (by rfl) ⟨1266974, by rfl⟩ : syracuseStep 1689299 = 2533949) B2533949
theorem B6899903 : Blo 207808 6899903 := bstep (se 1 (by rfl) ⟨5174927, by rfl⟩ : syracuseStep 6899903 = 10349855) B10349855
theorem B282367 : Blo 207808 282367 := bstep (se 1 (by rfl) ⟨211775, by rfl⟩ : syracuseStep 282367 = 423551) B423551
theorem B26042431 : Blo 207808 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B1826887 : Blo 207808 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B2875871 : Blo 207808 2875871 := bstep (se 1 (by rfl) ⟨2156903, by rfl⟩ : syracuseStep 2875871 = 4313807) B4313807
theorem B14548895 : Blo 207808 14548895 := bstep (se 1 (by rfl) ⟨10911671, by rfl⟩ : syracuseStep 14548895 = 21823343) B21823343
theorem B7668989 : Blo 207808 7668989 := bstep (se 3 (by rfl) ⟨1437935, by rfl⟩ : syracuseStep 7668989 = 2875871) B2875871
theorem B592667 : Blo 207808 592667 := bstep (se 1 (by rfl) ⟨444500, by rfl⟩ : syracuseStep 592667 = 889001) B889001
theorem B266095 : Blo 207808 266095 := bstep (se 1 (by rfl) ⟨199571, by rfl⟩ : syracuseStep 266095 = 399143) B399143
theorem B792575 : Blo 207808 792575 := bstep (se 1 (by rfl) ⟨594431, by rfl⟩ : syracuseStep 792575 = 1188863) B1188863
theorem B2435849 : Blo 207808 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B2010095 : Blo 207808 2010095 := bstep (se 1 (by rfl) ⟨1507571, by rfl⟩ : syracuseStep 2010095 = 3015143) B3015143
theorem B535643 : Blo 207808 535643 := bstep (se 1 (by rfl) ⟨401732, by rfl⟩ : syracuseStep 535643 = 803465) B803465
theorem B208543 : Blo 207808 208543 := bstep (se 1 (by rfl) ⟨156407, by rfl⟩ : syracuseStep 208543 = 312815) B312815
theorem B1126199 : Blo 207808 1126199 := bstep (se 1 (by rfl) ⟨844649, by rfl⟩ : syracuseStep 1126199 = 1689299) B1689299
theorem B4599935 : Blo 207808 4599935 := bstep (se 1 (by rfl) ⟨3449951, by rfl⟩ : syracuseStep 4599935 = 6899903) B6899903
theorem B701999 : Blo 207808 701999 := bstep (se 1 (by rfl) ⟨526499, by rfl⟩ : syracuseStep 701999 = 1052999) B1052999
theorem B376489 : Blo 207808 376489 := bstep (se 2 (by rfl) ⟨141183, by rfl⟩ : syracuseStep 376489 = 282367) B282367
theorem B903163 : Blo 207808 903163 := bstep (se 1 (by rfl) ⟨677372, by rfl⟩ : syracuseStep 903163 = 1354745) B1354745
theorem B1332089 : Blo 207808 1332089 := bstep (se 2 (by rfl) ⟨499533, by rfl⟩ : syracuseStep 1332089 = 999067) B999067
theorem B2020241 : Blo 207808 2020241 := bstep (se 2 (by rfl) ⟨757590, by rfl⟩ : syracuseStep 2020241 = 1515181) B1515181
theorem B34723241 : Blo 207808 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B9699263 : Blo 207808 9699263 := bstep (se 1 (by rfl) ⟨7274447, by rfl⟩ : syracuseStep 9699263 = 14548895) B14548895
theorem B5112659 : Blo 207808 5112659 := bstep (se 1 (by rfl) ⟨3834494, by rfl⟩ : syracuseStep 5112659 = 7668989) B7668989
theorem B395111 : Blo 207808 395111 := bstep (se 1 (by rfl) ⟨296333, by rfl⟩ : syracuseStep 395111 = 592667) B592667
theorem B888059 : Blo 207808 888059 := bstep (se 1 (by rfl) ⟨666044, by rfl⟩ : syracuseStep 888059 = 1332089) B1332089
theorem B1346827 : Blo 207808 1346827 := bstep (se 1 (by rfl) ⟨1010120, by rfl⟩ : syracuseStep 1346827 = 2020241) B2020241
theorem B528383 : Blo 207808 528383 := bstep (se 1 (by rfl) ⟨396287, by rfl⟩ : syracuseStep 528383 = 792575) B792575
theorem B467999 : Blo 207808 467999 := bstep (se 1 (by rfl) ⟨350999, by rfl⟩ : syracuseStep 467999 = 701999) B701999
theorem B501985 : Blo 207808 501985 := bstep (se 2 (by rfl) ⟨188244, by rfl⟩ : syracuseStep 501985 = 376489) B376489
theorem B6466175 : Blo 207808 6466175 := bstep (se 1 (by rfl) ⟨4849631, by rfl⟩ : syracuseStep 6466175 = 9699263) B9699263
theorem B23148827 : Blo 207808 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B1623899 : Blo 207808 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B3066623 : Blo 207808 3066623 := bstep (se 1 (by rfl) ⟨2299967, by rfl⟩ : syracuseStep 3066623 = 4599935) B4599935
theorem B1204217 : Blo 207808 1204217 := bstep (se 2 (by rfl) ⟨451581, by rfl⟩ : syracuseStep 1204217 = 903163) B903163
theorem B354793 : Blo 207808 354793 := bstep (se 2 (by rfl) ⟨133047, by rfl⟩ : syracuseStep 354793 = 266095) B266095
theorem B1340063 : Blo 207808 1340063 := bstep (se 1 (by rfl) ⟨1005047, by rfl⟩ : syracuseStep 1340063 = 2010095) B2010095
theorem B357095 : Blo 207808 357095 := bstep (se 1 (by rfl) ⟨267821, by rfl⟩ : syracuseStep 357095 = 535643) B535643
theorem B750799 : Blo 207808 750799 := bstep (se 1 (by rfl) ⟨563099, by rfl⟩ : syracuseStep 750799 = 1126199) B1126199
theorem B263407 : Blo 207808 263407 := bstep (se 1 (by rfl) ⟨197555, by rfl⟩ : syracuseStep 263407 = 395111) B395111
theorem B592039 : Blo 207808 592039 := bstep (se 1 (by rfl) ⟨444029, by rfl⟩ : syracuseStep 592039 = 888059) B888059
theorem B13633757 : Blo 207808 13633757 := bstep (se 3 (by rfl) ⟨2556329, by rfl⟩ : syracuseStep 13633757 = 5112659) B5112659
theorem B4330397 : Blo 207808 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B4004261 : Blo 207808 4004261 := bstep (se 4 (by rfl) ⟨375399, by rfl⟩ : syracuseStep 4004261 = 750799) B750799
theorem B893375 : Blo 207808 893375 := bstep (se 1 (by rfl) ⟨670031, by rfl⟩ : syracuseStep 893375 = 1340063) B1340063
theorem B238063 : Blo 207808 238063 := bstep (se 1 (by rfl) ⟨178547, by rfl⟩ : syracuseStep 238063 = 357095) B357095
theorem B2044415 : Blo 207808 2044415 := bstep (se 1 (by rfl) ⟨1533311, by rfl⟩ : syracuseStep 2044415 = 3066623) B3066623
theorem B669313 : Blo 207808 669313 := bstep (se 2 (by rfl) ⟨250992, by rfl⟩ : syracuseStep 669313 = 501985) B501985
theorem B473057 : Blo 207808 473057 := bstep (se 2 (by rfl) ⟨177396, by rfl⟩ : syracuseStep 473057 = 354793) B354793
theorem B802811 : Blo 207808 802811 := bstep (se 1 (by rfl) ⟨602108, by rfl⟩ : syracuseStep 802811 = 1204217) B1204217
theorem B311999 : Blo 207808 311999 := bstep (se 1 (by rfl) ⟨233999, by rfl⟩ : syracuseStep 311999 = 467999) B467999
theorem B4310783 : Blo 207808 4310783 := bstep (se 1 (by rfl) ⟨3233087, by rfl⟩ : syracuseStep 4310783 = 6466175) B6466175
theorem B352255 : Blo 207808 352255 := bstep (se 1 (by rfl) ⟨264191, by rfl⟩ : syracuseStep 352255 = 528383) B528383
theorem B1795769 : Blo 207808 1795769 := bstep (se 2 (by rfl) ⟨673413, by rfl⟩ : syracuseStep 1795769 = 1346827) B1346827
theorem B15432551 : Blo 207808 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B789385 : Blo 207808 789385 := bstep (se 2 (by rfl) ⟨296019, by rfl⟩ : syracuseStep 789385 = 592039) B592039
theorem B2886931 : Blo 207808 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B595583 : Blo 207808 595583 := bstep (se 1 (by rfl) ⟨446687, by rfl⟩ : syracuseStep 595583 = 893375) B893375
theorem B892417 : Blo 207808 892417 := bstep (se 2 (by rfl) ⟨334656, by rfl⟩ : syracuseStep 892417 = 669313) B669313
theorem B535207 : Blo 207808 535207 := bstep (se 1 (by rfl) ⟨401405, by rfl⟩ : syracuseStep 535207 = 802811) B802811
theorem B469673 : Blo 207808 469673 := bstep (se 2 (by rfl) ⟨176127, by rfl⟩ : syracuseStep 469673 = 352255) B352255
theorem B207999 : Blo 207808 207999 := bstep (se 1 (by rfl) ⟨155999, by rfl⟩ : syracuseStep 207999 = 311999) B311999
theorem B9089171 : Blo 207808 9089171 := bstep (se 1 (by rfl) ⟨6816878, by rfl⟩ : syracuseStep 9089171 = 13633757) B13633757
theorem B2669507 : Blo 207808 2669507 := bstep (se 1 (by rfl) ⟨2002130, by rfl⟩ : syracuseStep 2669507 = 4004261) B4004261
theorem B1197179 : Blo 207808 1197179 := bstep (se 1 (by rfl) ⟨897884, by rfl⟩ : syracuseStep 1197179 = 1795769) B1795769
theorem B1362943 : Blo 207808 1362943 := bstep (se 1 (by rfl) ⟨1022207, by rfl⟩ : syracuseStep 1362943 = 2044415) B2044415
theorem B315371 : Blo 207808 315371 := bstep (se 1 (by rfl) ⟨236528, by rfl⟩ : syracuseStep 315371 = 473057) B473057
theorem B317417 : Blo 207808 317417 := bstep (se 2 (by rfl) ⟨119031, by rfl⟩ : syracuseStep 317417 = 238063) B238063
theorem B2873855 : Blo 207808 2873855 := bstep (se 1 (by rfl) ⟨2155391, by rfl⟩ : syracuseStep 2873855 = 4310783) B4310783
theorem B351209 : Blo 207808 351209 := bstep (se 2 (by rfl) ⟨131703, by rfl⟩ : syracuseStep 351209 = 263407) B263407
theorem B10288367 : Blo 207808 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B397055 : Blo 207808 397055 := bstep (se 1 (by rfl) ⟨297791, by rfl⟩ : syracuseStep 397055 = 595583) B595583
theorem B1052513 : Blo 207808 1052513 := bstep (se 2 (by rfl) ⟨394692, by rfl⟩ : syracuseStep 1052513 = 789385) B789385
theorem B234139 : Blo 207808 234139 := bstep (se 1 (by rfl) ⟨175604, by rfl⟩ : syracuseStep 234139 = 351209) B351209
theorem B1779671 : Blo 207808 1779671 := bstep (se 1 (by rfl) ⟨1334753, by rfl⟩ : syracuseStep 1779671 = 2669507) B2669507
theorem B1189889 : Blo 207808 1189889 := bstep (se 2 (by rfl) ⟨446208, by rfl⟩ : syracuseStep 1189889 = 892417) B892417
theorem B6858911 : Blo 207808 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B798119 : Blo 207808 798119 := bstep (se 1 (by rfl) ⟨598589, by rfl⟩ : syracuseStep 798119 = 1197179) B1197179
theorem B210247 : Blo 207808 210247 := bstep (se 1 (by rfl) ⟨157685, by rfl⟩ : syracuseStep 210247 = 315371) B315371
theorem B211611 : Blo 207808 211611 := bstep (se 1 (by rfl) ⟨158708, by rfl⟩ : syracuseStep 211611 = 317417) B317417
theorem B1817257 : Blo 207808 1817257 := bstep (se 2 (by rfl) ⟨681471, by rfl⟩ : syracuseStep 1817257 = 1362943) B1362943
theorem B1915903 : Blo 207808 1915903 := bstep (se 1 (by rfl) ⟨1436927, by rfl⟩ : syracuseStep 1915903 = 2873855) B2873855
theorem B3849241 : Blo 207808 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B313115 : Blo 207808 313115 := bstep (se 1 (by rfl) ⟨234836, by rfl⟩ : syracuseStep 313115 = 469673) B469673
theorem B713609 : Blo 207808 713609 := bstep (se 2 (by rfl) ⟨267603, by rfl⟩ : syracuseStep 713609 = 535207) B535207
theorem B6059447 : Blo 207808 6059447 := bstep (se 1 (by rfl) ⟨4544585, by rfl⟩ : syracuseStep 6059447 = 9089171) B9089171
theorem B264703 : Blo 207808 264703 := bstep (se 1 (by rfl) ⟨198527, by rfl⟩ : syracuseStep 264703 = 397055) B397055
theorem B1186447 : Blo 207808 1186447 := bstep (se 1 (by rfl) ⟨889835, by rfl⟩ : syracuseStep 1186447 = 1779671) B1779671
theorem B793259 : Blo 207808 793259 := bstep (se 1 (by rfl) ⟨594944, by rfl⟩ : syracuseStep 793259 = 1189889) B1189889
theorem B532079 : Blo 207808 532079 := bstep (se 1 (by rfl) ⟨399059, by rfl⟩ : syracuseStep 532079 = 798119) B798119
theorem B4039631 : Blo 207808 4039631 := bstep (se 1 (by rfl) ⟨3029723, by rfl⟩ : syracuseStep 4039631 = 6059447) B6059447
theorem B208743 : Blo 207808 208743 := bstep (se 1 (by rfl) ⟨156557, by rfl⟩ : syracuseStep 208743 = 313115) B313115
theorem B701675 : Blo 207808 701675 := bstep (se 1 (by rfl) ⟨526256, by rfl⟩ : syracuseStep 701675 = 1052513) B1052513
theorem B475739 : Blo 207808 475739 := bstep (se 1 (by rfl) ⟨356804, by rfl⟩ : syracuseStep 475739 = 713609) B713609
theorem B312185 : Blo 207808 312185 := bstep (se 2 (by rfl) ⟨117069, by rfl⟩ : syracuseStep 312185 = 234139) B234139
theorem B4572607 : Blo 207808 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B5132321 : Blo 207808 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B2423009 : Blo 207808 2423009 := bstep (se 2 (by rfl) ⟨908628, by rfl⟩ : syracuseStep 2423009 = 1817257) B1817257
theorem B2554537 : Blo 207808 2554537 := bstep (se 2 (by rfl) ⟨957951, by rfl⟩ : syracuseStep 2554537 = 1915903) B1915903
theorem B6096809 : Blo 207808 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B528839 : Blo 207808 528839 := bstep (se 1 (by rfl) ⟨396629, by rfl⟩ : syracuseStep 528839 = 793259) B793259
theorem B2693087 : Blo 207808 2693087 := bstep (se 1 (by rfl) ⟨2019815, by rfl⟩ : syracuseStep 2693087 = 4039631) B4039631
theorem B467783 : Blo 207808 467783 := bstep (se 1 (by rfl) ⟨350837, by rfl⟩ : syracuseStep 467783 = 701675) B701675
theorem B1581929 : Blo 207808 1581929 := bstep (se 2 (by rfl) ⟨593223, by rfl⟩ : syracuseStep 1581929 = 1186447) B1186447
theorem B1615339 : Blo 207808 1615339 := bstep (se 1 (by rfl) ⟨1211504, by rfl⟩ : syracuseStep 1615339 = 2423009) B2423009
theorem B208123 : Blo 207808 208123 := bstep (se 1 (by rfl) ⟨156092, by rfl⟩ : syracuseStep 208123 = 312185) B312185
theorem B3421547 : Blo 207808 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B317159 : Blo 207808 317159 := bstep (se 1 (by rfl) ⟨237869, by rfl⟩ : syracuseStep 317159 = 475739) B475739
theorem B352937 : Blo 207808 352937 := bstep (se 2 (by rfl) ⟨132351, by rfl⟩ : syracuseStep 352937 = 264703) B264703
theorem B354719 : Blo 207808 354719 := bstep (se 1 (by rfl) ⟨266039, by rfl⟩ : syracuseStep 354719 = 532079) B532079
theorem B3406049 : Blo 207808 3406049 := bstep (se 2 (by rfl) ⟨1277268, by rfl⟩ : syracuseStep 3406049 = 2554537) B2554537
theorem B4064539 : Blo 207808 4064539 := bstep (se 1 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 4064539 = 6096809) B6096809
theorem B235291 : Blo 207808 235291 := bstep (se 1 (by rfl) ⟨176468, by rfl⟩ : syracuseStep 235291 = 352937) B352937
theorem B1054619 : Blo 207808 1054619 := bstep (se 1 (by rfl) ⟨790964, by rfl⟩ : syracuseStep 1054619 = 1581929) B1581929
theorem B236479 : Blo 207808 236479 := bstep (se 1 (by rfl) ⟨177359, by rfl⟩ : syracuseStep 236479 = 354719) B354719
theorem B2270699 : Blo 207808 2270699 := bstep (se 1 (by rfl) ⟨1703024, by rfl⟩ : syracuseStep 2270699 = 3406049) B3406049
theorem B211439 : Blo 207808 211439 := bstep (se 1 (by rfl) ⟨158579, by rfl⟩ : syracuseStep 211439 = 317159) B317159
theorem B311855 : Blo 207808 311855 := bstep (se 1 (by rfl) ⟨233891, by rfl⟩ : syracuseStep 311855 = 467783) B467783
theorem B2281031 : Blo 207808 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B2153785 : Blo 207808 2153785 := bstep (se 2 (by rfl) ⟨807669, by rfl⟩ : syracuseStep 2153785 = 1615339) B1615339
theorem B352559 : Blo 207808 352559 := bstep (se 1 (by rfl) ⟨264419, by rfl⟩ : syracuseStep 352559 = 528839) B528839
theorem B1795391 : Blo 207808 1795391 := bstep (se 1 (by rfl) ⟨1346543, by rfl⟩ : syracuseStep 1795391 = 2693087) B2693087
theorem B235039 : Blo 207808 235039 := bstep (se 1 (by rfl) ⟨176279, by rfl⟩ : syracuseStep 235039 = 352559) B352559
theorem B1513799 : Blo 207808 1513799 := bstep (se 1 (by rfl) ⟨1135349, by rfl⟩ : syracuseStep 1513799 = 2270699) B2270699
theorem B207903 : Blo 207808 207903 := bstep (se 1 (by rfl) ⟨155927, by rfl⟩ : syracuseStep 207903 = 311855) B311855
theorem B5419385 : Blo 207808 5419385 := bstep (se 2 (by rfl) ⟨2032269, by rfl⟩ : syracuseStep 5419385 = 4064539) B4064539
theorem B1520687 : Blo 207808 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B703079 : Blo 207808 703079 := bstep (se 1 (by rfl) ⟨527309, by rfl⟩ : syracuseStep 703079 = 1054619) B1054619
theorem B1196927 : Blo 207808 1196927 := bstep (se 1 (by rfl) ⟨897695, by rfl⟩ : syracuseStep 1196927 = 1795391) B1795391
theorem B313721 : Blo 207808 313721 := bstep (se 2 (by rfl) ⟨117645, by rfl⟩ : syracuseStep 313721 = 235291) B235291
theorem B315305 : Blo 207808 315305 := bstep (se 2 (by rfl) ⟨118239, by rfl⟩ : syracuseStep 315305 = 236479) B236479
theorem B2871713 : Blo 207808 2871713 := bstep (se 2 (by rfl) ⟨1076892, by rfl⟩ : syracuseStep 2871713 = 2153785) B2153785
theorem B3612923 : Blo 207808 3612923 := bstep (se 1 (by rfl) ⟨2709692, by rfl⟩ : syracuseStep 3612923 = 5419385) B5419385
theorem B468719 : Blo 207808 468719 := bstep (se 1 (by rfl) ⟨351539, by rfl⟩ : syracuseStep 468719 = 703079) B703079
theorem B797951 : Blo 207808 797951 := bstep (se 1 (by rfl) ⟨598463, by rfl⟩ : syracuseStep 797951 = 1196927) B1196927
theorem B209147 : Blo 207808 209147 := bstep (se 1 (by rfl) ⟨156860, by rfl⟩ : syracuseStep 209147 = 313721) B313721
theorem B210203 : Blo 207808 210203 := bstep (se 1 (by rfl) ⟨157652, by rfl⟩ : syracuseStep 210203 = 315305) B315305
theorem B1914475 : Blo 207808 1914475 := bstep (se 1 (by rfl) ⟨1435856, by rfl⟩ : syracuseStep 1914475 = 2871713) B2871713
theorem B313385 : Blo 207808 313385 := bstep (se 2 (by rfl) ⟨117519, by rfl⟩ : syracuseStep 313385 = 235039) B235039
theorem B1009199 : Blo 207808 1009199 := bstep (se 1 (by rfl) ⟨756899, by rfl⟩ : syracuseStep 1009199 = 1513799) B1513799
theorem B1013791 : Blo 207808 1013791 := bstep (se 1 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 1013791 = 1520687) B1520687
theorem B531967 : Blo 207808 531967 := bstep (se 1 (by rfl) ⟨398975, by rfl⟩ : syracuseStep 531967 = 797951) B797951
theorem B1351721 : Blo 207808 1351721 := bstep (se 2 (by rfl) ⟨506895, by rfl⟩ : syracuseStep 1351721 = 1013791) B1013791
theorem B208923 : Blo 207808 208923 := bstep (se 1 (by rfl) ⟨156692, by rfl⟩ : syracuseStep 208923 = 313385) B313385
theorem B2408615 : Blo 207808 2408615 := bstep (se 1 (by rfl) ⟨1806461, by rfl⟩ : syracuseStep 2408615 = 3612923) B3612923
theorem B672799 : Blo 207808 672799 := bstep (se 1 (by rfl) ⟨504599, by rfl⟩ : syracuseStep 672799 = 1009199) B1009199
theorem B312479 : Blo 207808 312479 := bstep (se 1 (by rfl) ⟨234359, by rfl⟩ : syracuseStep 312479 = 468719) B468719
theorem B2552633 : Blo 207808 2552633 := bstep (se 2 (by rfl) ⟨957237, by rfl⟩ : syracuseStep 2552633 = 1914475) B1914475
theorem B1605743 : Blo 207808 1605743 := bstep (se 1 (by rfl) ⟨1204307, by rfl⟩ : syracuseStep 1605743 = 2408615) B2408615
theorem B208319 : Blo 207808 208319 := bstep (se 1 (by rfl) ⟨156239, by rfl⟩ : syracuseStep 208319 = 312479) B312479
theorem B897065 : Blo 207808 897065 := bstep (se 2 (by rfl) ⟨336399, by rfl⟩ : syracuseStep 897065 = 672799) B672799
theorem B901147 : Blo 207808 901147 := bstep (se 1 (by rfl) ⟨675860, by rfl⟩ : syracuseStep 901147 = 1351721) B1351721
theorem B709289 : Blo 207808 709289 := bstep (se 2 (by rfl) ⟨265983, by rfl⟩ : syracuseStep 709289 = 531967) B531967
theorem B1701755 : Blo 207808 1701755 := bstep (se 1 (by rfl) ⟨1276316, by rfl⟩ : syracuseStep 1701755 = 2552633) B2552633
theorem B598043 : Blo 207808 598043 := bstep (se 1 (by rfl) ⟨448532, by rfl⟩ : syracuseStep 598043 = 897065) B897065
theorem B472859 : Blo 207808 472859 := bstep (se 1 (by rfl) ⟨354644, by rfl⟩ : syracuseStep 472859 = 709289) B709289
theorem B1134503 : Blo 207808 1134503 := bstep (se 1 (by rfl) ⟨850877, by rfl⟩ : syracuseStep 1134503 = 1701755) B1701755
theorem B1201529 : Blo 207808 1201529 := bstep (se 2 (by rfl) ⟨450573, by rfl⟩ : syracuseStep 1201529 = 901147) B901147
theorem B1070495 : Blo 207808 1070495 := bstep (se 1 (by rfl) ⟨802871, by rfl⟩ : syracuseStep 1070495 = 1605743) B1605743
theorem B756335 : Blo 207808 756335 := bstep (se 1 (by rfl) ⟨567251, by rfl⟩ : syracuseStep 756335 = 1134503) B1134503
theorem B398695 : Blo 207808 398695 := bstep (se 1 (by rfl) ⟨299021, by rfl⟩ : syracuseStep 398695 = 598043) B598043
theorem B801019 : Blo 207808 801019 := bstep (se 1 (by rfl) ⟨600764, by rfl⟩ : syracuseStep 801019 = 1201529) B1201529
theorem B315239 : Blo 207808 315239 := bstep (se 1 (by rfl) ⟨236429, by rfl⟩ : syracuseStep 315239 = 472859) B472859
theorem B713663 : Blo 207808 713663 := bstep (se 1 (by rfl) ⟨535247, by rfl⟩ : syracuseStep 713663 = 1070495) B1070495
theorem B531593 : Blo 207808 531593 := bstep (se 2 (by rfl) ⟨199347, by rfl⟩ : syracuseStep 531593 = 398695) B398695
theorem B4272101 : Blo 207808 4272101 := bstep (se 4 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 4272101 = 801019) B801019
theorem B210159 : Blo 207808 210159 := bstep (se 1 (by rfl) ⟨157619, by rfl⟩ : syracuseStep 210159 = 315239) B315239
theorem B475775 : Blo 207808 475775 := bstep (se 1 (by rfl) ⟨356831, by rfl⟩ : syracuseStep 475775 = 713663) B713663
theorem B2016893 : Blo 207808 2016893 := bstep (se 3 (by rfl) ⟨378167, by rfl⟩ : syracuseStep 2016893 = 756335) B756335
theorem B1344595 : Blo 207808 1344595 := bstep (se 1 (by rfl) ⟨1008446, by rfl⟩ : syracuseStep 1344595 = 2016893) B2016893
theorem B317183 : Blo 207808 317183 := bstep (se 1 (by rfl) ⟨237887, by rfl⟩ : syracuseStep 317183 = 475775) B475775
theorem B354395 : Blo 207808 354395 := bstep (se 1 (by rfl) ⟨265796, by rfl⟩ : syracuseStep 354395 = 531593) B531593
theorem B2848067 : Blo 207808 2848067 := bstep (se 1 (by rfl) ⟨2136050, by rfl⟩ : syracuseStep 2848067 = 4272101) B4272101
theorem B236263 : Blo 207808 236263 := bstep (se 1 (by rfl) ⟨177197, by rfl⟩ : syracuseStep 236263 = 354395) B354395
theorem B211455 : Blo 207808 211455 := bstep (se 1 (by rfl) ⟨158591, by rfl⟩ : syracuseStep 211455 = 317183) B317183
theorem B1792793 : Blo 207808 1792793 := bstep (se 2 (by rfl) ⟨672297, by rfl⟩ : syracuseStep 1792793 = 1344595) B1344595
theorem B1898711 : Blo 207808 1898711 := bstep (se 1 (by rfl) ⟨1424033, by rfl⟩ : syracuseStep 1898711 = 2848067) B2848067
theorem B1195195 : Blo 207808 1195195 := bstep (se 1 (by rfl) ⟨896396, by rfl⟩ : syracuseStep 1195195 = 1792793) B1792793
theorem B315017 : Blo 207808 315017 := bstep (se 2 (by rfl) ⟨118131, by rfl⟩ : syracuseStep 315017 = 236263) B236263
theorem B1265807 : Blo 207808 1265807 := bstep (se 1 (by rfl) ⟨949355, by rfl⟩ : syracuseStep 1265807 = 1898711) B1898711
theorem B210011 : Blo 207808 210011 := bstep (se 1 (by rfl) ⟨157508, by rfl⟩ : syracuseStep 210011 = 315017) B315017
theorem B1593593 : Blo 207808 1593593 := bstep (se 2 (by rfl) ⟨597597, by rfl⟩ : syracuseStep 1593593 = 1195195) B1195195
theorem B843871 : Blo 207808 843871 := bstep (se 1 (by rfl) ⟨632903, by rfl⟩ : syracuseStep 843871 = 1265807) B1265807
theorem B1125161 : Blo 207808 1125161 := bstep (se 2 (by rfl) ⟨421935, by rfl⟩ : syracuseStep 1125161 = 843871) B843871
theorem B1062395 : Blo 207808 1062395 := bstep (se 1 (by rfl) ⟨796796, by rfl⟩ : syracuseStep 1062395 = 1593593) B1593593
theorem B708263 : Blo 207808 708263 := bstep (se 1 (by rfl) ⟨531197, by rfl⟩ : syracuseStep 708263 = 1062395) B1062395
theorem B750107 : Blo 207808 750107 := bstep (se 1 (by rfl) ⟨562580, by rfl⟩ : syracuseStep 750107 = 1125161) B1125161
theorem B2000285 : Blo 207808 2000285 := bstep (se 3 (by rfl) ⟨375053, by rfl⟩ : syracuseStep 2000285 = 750107) B750107
theorem B472175 : Blo 207808 472175 := bstep (se 1 (by rfl) ⟨354131, by rfl⟩ : syracuseStep 472175 = 708263) B708263
theorem B314783 : Blo 207808 314783 := bstep (se 1 (by rfl) ⟨236087, by rfl⟩ : syracuseStep 314783 = 472175) B472175
theorem B1333523 : Blo 207808 1333523 := bstep (se 1 (by rfl) ⟨1000142, by rfl⟩ : syracuseStep 1333523 = 2000285) B2000285
theorem B209855 : Blo 207808 209855 := bstep (se 1 (by rfl) ⟨157391, by rfl⟩ : syracuseStep 209855 = 314783) B314783
theorem B3556061 : Blo 207808 3556061 := bstep (se 3 (by rfl) ⟨666761, by rfl⟩ : syracuseStep 3556061 = 1333523) B1333523
theorem B2370707 : Blo 207808 2370707 := bstep (se 1 (by rfl) ⟨1778030, by rfl⟩ : syracuseStep 2370707 = 3556061) B3556061
theorem B1580471 : Blo 207808 1580471 := bstep (se 1 (by rfl) ⟨1185353, by rfl⟩ : syracuseStep 1580471 = 2370707) B2370707
theorem B1053647 : Blo 207808 1053647 := bstep (se 1 (by rfl) ⟨790235, by rfl⟩ : syracuseStep 1053647 = 1580471) B1580471
theorem B702431 : Blo 207808 702431 := bstep (se 1 (by rfl) ⟨526823, by rfl⟩ : syracuseStep 702431 = 1053647) B1053647
theorem B468287 : Blo 207808 468287 := bstep (se 1 (by rfl) ⟨351215, by rfl⟩ : syracuseStep 468287 = 702431) B702431
theorem B312191 : Blo 207808 312191 := bstep (se 1 (by rfl) ⟨234143, by rfl⟩ : syracuseStep 312191 = 468287) B468287
theorem B208127 : Blo 207808 208127 := bstep (se 1 (by rfl) ⟨156095, by rfl⟩ : syracuseStep 208127 = 312191) B312191

theorem C0 (j : ℕ) (h1 : 51952 ≤ j) (h2 : j ≤ 52651) : Blo 207808 (4 * j + 3) := by
  interval_cases j
  · exact B207811
  · exact B207815
  · exact B207819
  · exact B207823
  · exact B207827
  · exact B207831
  · exact B207835
  · exact B207839
  · exact B207843
  · exact B207847
  · exact B207851
  · exact B207855
  · exact B207859
  · exact B207863
  · exact B207867
  · exact B207871
  · exact B207875
  · exact B207879
  · exact B207883
  · exact B207887
  · exact B207891
  · exact B207895
  · exact B207899
  · exact B207903
  · exact B207907
  · exact B207911
  · exact B207915
  · exact B207919
  · exact B207923
  · exact B207927
  · exact B207931
  · exact B207935
  · exact B207939
  · exact B207943
  · exact B207947
  · exact B207951
  · exact B207955
  · exact B207959
  · exact B207963
  · exact B207967
  · exact B207971
  · exact B207975
  · exact B207979
  · exact B207983
  · exact B207987
  · exact B207991
  · exact B207995
  · exact B207999
  · exact B208003
  · exact B208007
  · exact B208011
  · exact B208015
  · exact B208019
  · exact B208023
  · exact B208027
  · exact B208031
  · exact B208035
  · exact B208039
  · exact B208043
  · exact B208047
  · exact B208051
  · exact B208055
  · exact B208059
  · exact B208063
  · exact B208067
  · exact B208071
  · exact B208075
  · exact B208079
  · exact B208083
  · exact B208087
  · exact B208091
  · exact B208095
  · exact B208099
  · exact B208103
  · exact B208107
  · exact B208111
  · exact B208115
  · exact B208119
  · exact B208123
  · exact B208127
  · exact B208131
  · exact B208135
  · exact B208139
  · exact B208143
  · exact B208147
  · exact B208151
  · exact B208155
  · exact B208159
  · exact B208163
  · exact B208167
  · exact B208171
  · exact B208175
  · exact B208179
  · exact B208183
  · exact B208187
  · exact B208191
  · exact B208195
  · exact B208199
  · exact B208203
  · exact B208207
  · exact B208211
  · exact B208215
  · exact B208219
  · exact B208223
  · exact B208227
  · exact B208231
  · exact B208235
  · exact B208239
  · exact B208243
  · exact B208247
  · exact B208251
  · exact B208255
  · exact B208259
  · exact B208263
  · exact B208267
  · exact B208271
  · exact B208275
  · exact B208279
  · exact B208283
  · exact B208287
  · exact B208291
  · exact B208295
  · exact B208299
  · exact B208303
  · exact B208307
  · exact B208311
  · exact B208315
  · exact B208319
  · exact B208323
  · exact B208327
  · exact B208331
  · exact B208335
  · exact B208339
  · exact B208343
  · exact B208347
  · exact B208351
  · exact B208355
  · exact B208359
  · exact B208363
  · exact B208367
  · exact B208371
  · exact B208375
  · exact B208379
  · exact B208383
  · exact B208387
  · exact B208391
  · exact B208395
  · exact B208399
  · exact B208403
  · exact B208407
  · exact B208411
  · exact B208415
  · exact B208419
  · exact B208423
  · exact B208427
  · exact B208431
  · exact B208435
  · exact B208439
  · exact B208443
  · exact B208447
  · exact B208451
  · exact B208455
  · exact B208459
  · exact B208463
  · exact B208467
  · exact B208471
  · exact B208475
  · exact B208479
  · exact B208483
  · exact B208487
  · exact B208491
  · exact B208495
  · exact B208499
  · exact B208503
  · exact B208507
  · exact B208511
  · exact B208515
  · exact B208519
  · exact B208523
  · exact B208527
  · exact B208531
  · exact B208535
  · exact B208539
  · exact B208543
  · exact B208547
  · exact B208551
  · exact B208555
  · exact B208559
  · exact B208563
  · exact B208567
  · exact B208571
  · exact B208575
  · exact B208579
  · exact B208583
  · exact B208587
  · exact B208591
  · exact B208595
  · exact B208599
  · exact B208603
  · exact B208607
  · exact B208611
  · exact B208615
  · exact B208619
  · exact B208623
  · exact B208627
  · exact B208631
  · exact B208635
  · exact B208639
  · exact B208643
  · exact B208647
  · exact B208651
  · exact B208655
  · exact B208659
  · exact B208663
  · exact B208667
  · exact B208671
  · exact B208675
  · exact B208679
  · exact B208683
  · exact B208687
  · exact B208691
  · exact B208695
  · exact B208699
  · exact B208703
  · exact B208707
  · exact B208711
  · exact B208715
  · exact B208719
  · exact B208723
  · exact B208727
  · exact B208731
  · exact B208735
  · exact B208739
  · exact B208743
  · exact B208747
  · exact B208751
  · exact B208755
  · exact B208759
  · exact B208763
  · exact B208767
  · exact B208771
  · exact B208775
  · exact B208779
  · exact B208783
  · exact B208787
  · exact B208791
  · exact B208795
  · exact B208799
  · exact B208803
  · exact B208807
  · exact B208811
  · exact B208815
  · exact B208819
  · exact B208823
  · exact B208827
  · exact B208831
  · exact B208835
  · exact B208839
  · exact B208843
  · exact B208847
  · exact B208851
  · exact B208855
  · exact B208859
  · exact B208863
  · exact B208867
  · exact B208871
  · exact B208875
  · exact B208879
  · exact B208883
  · exact B208887
  · exact B208891
  · exact B208895
  · exact B208899
  · exact B208903
  · exact B208907
  · exact B208911
  · exact B208915
  · exact B208919
  · exact B208923
  · exact B208927
  · exact B208931
  · exact B208935
  · exact B208939
  · exact B208943
  · exact B208947
  · exact B208951
  · exact B208955
  · exact B208959
  · exact B208963
  · exact B208967
  · exact B208971
  · exact B208975
  · exact B208979
  · exact B208983
  · exact B208987
  · exact B208991
  · exact B208995
  · exact B208999
  · exact B209003
  · exact B209007
  · exact B209011
  · exact B209015
  · exact B209019
  · exact B209023
  · exact B209027
  · exact B209031
  · exact B209035
  · exact B209039
  · exact B209043
  · exact B209047
  · exact B209051
  · exact B209055
  · exact B209059
  · exact B209063
  · exact B209067
  · exact B209071
  · exact B209075
  · exact B209079
  · exact B209083
  · exact B209087
  · exact B209091
  · exact B209095
  · exact B209099
  · exact B209103
  · exact B209107
  · exact B209111
  · exact B209115
  · exact B209119
  · exact B209123
  · exact B209127
  · exact B209131
  · exact B209135
  · exact B209139
  · exact B209143
  · exact B209147
  · exact B209151
  · exact B209155
  · exact B209159
  · exact B209163
  · exact B209167
  · exact B209171
  · exact B209175
  · exact B209179
  · exact B209183
  · exact B209187
  · exact B209191
  · exact B209195
  · exact B209199
  · exact B209203
  · exact B209207
  · exact B209211
  · exact B209215
  · exact B209219
  · exact B209223
  · exact B209227
  · exact B209231
  · exact B209235
  · exact B209239
  · exact B209243
  · exact B209247
  · exact B209251
  · exact B209255
  · exact B209259
  · exact B209263
  · exact B209267
  · exact B209271
  · exact B209275
  · exact B209279
  · exact B209283
  · exact B209287
  · exact B209291
  · exact B209295
  · exact B209299
  · exact B209303
  · exact B209307
  · exact B209311
  · exact B209315
  · exact B209319
  · exact B209323
  · exact B209327
  · exact B209331
  · exact B209335
  · exact B209339
  · exact B209343
  · exact B209347
  · exact B209351
  · exact B209355
  · exact B209359
  · exact B209363
  · exact B209367
  · exact B209371
  · exact B209375
  · exact B209379
  · exact B209383
  · exact B209387
  · exact B209391
  · exact B209395
  · exact B209399
  · exact B209403
  · exact B209407
  · exact B209411
  · exact B209415
  · exact B209419
  · exact B209423
  · exact B209427
  · exact B209431
  · exact B209435
  · exact B209439
  · exact B209443
  · exact B209447
  · exact B209451
  · exact B209455
  · exact B209459
  · exact B209463
  · exact B209467
  · exact B209471
  · exact B209475
  · exact B209479
  · exact B209483
  · exact B209487
  · exact B209491
  · exact B209495
  · exact B209499
  · exact B209503
  · exact B209507
  · exact B209511
  · exact B209515
  · exact B209519
  · exact B209523
  · exact B209527
  · exact B209531
  · exact B209535
  · exact B209539
  · exact B209543
  · exact B209547
  · exact B209551
  · exact B209555
  · exact B209559
  · exact B209563
  · exact B209567
  · exact B209571
  · exact B209575
  · exact B209579
  · exact B209583
  · exact B209587
  · exact B209591
  · exact B209595
  · exact B209599
  · exact B209603
  · exact B209607
  · exact B209611
  · exact B209615
  · exact B209619
  · exact B209623
  · exact B209627
  · exact B209631
  · exact B209635
  · exact B209639
  · exact B209643
  · exact B209647
  · exact B209651
  · exact B209655
  · exact B209659
  · exact B209663
  · exact B209667
  · exact B209671
  · exact B209675
  · exact B209679
  · exact B209683
  · exact B209687
  · exact B209691
  · exact B209695
  · exact B209699
  · exact B209703
  · exact B209707
  · exact B209711
  · exact B209715
  · exact B209719
  · exact B209723
  · exact B209727
  · exact B209731
  · exact B209735
  · exact B209739
  · exact B209743
  · exact B209747
  · exact B209751
  · exact B209755
  · exact B209759
  · exact B209763
  · exact B209767
  · exact B209771
  · exact B209775
  · exact B209779
  · exact B209783
  · exact B209787
  · exact B209791
  · exact B209795
  · exact B209799
  · exact B209803
  · exact B209807
  · exact B209811
  · exact B209815
  · exact B209819
  · exact B209823
  · exact B209827
  · exact B209831
  · exact B209835
  · exact B209839
  · exact B209843
  · exact B209847
  · exact B209851
  · exact B209855
  · exact B209859
  · exact B209863
  · exact B209867
  · exact B209871
  · exact B209875
  · exact B209879
  · exact B209883
  · exact B209887
  · exact B209891
  · exact B209895
  · exact B209899
  · exact B209903
  · exact B209907
  · exact B209911
  · exact B209915
  · exact B209919
  · exact B209923
  · exact B209927
  · exact B209931
  · exact B209935
  · exact B209939
  · exact B209943
  · exact B209947
  · exact B209951
  · exact B209955
  · exact B209959
  · exact B209963
  · exact B209967
  · exact B209971
  · exact B209975
  · exact B209979
  · exact B209983
  · exact B209987
  · exact B209991
  · exact B209995
  · exact B209999
  · exact B210003
  · exact B210007
  · exact B210011
  · exact B210015
  · exact B210019
  · exact B210023
  · exact B210027
  · exact B210031
  · exact B210035
  · exact B210039
  · exact B210043
  · exact B210047
  · exact B210051
  · exact B210055
  · exact B210059
  · exact B210063
  · exact B210067
  · exact B210071
  · exact B210075
  · exact B210079
  · exact B210083
  · exact B210087
  · exact B210091
  · exact B210095
  · exact B210099
  · exact B210103
  · exact B210107
  · exact B210111
  · exact B210115
  · exact B210119
  · exact B210123
  · exact B210127
  · exact B210131
  · exact B210135
  · exact B210139
  · exact B210143
  · exact B210147
  · exact B210151
  · exact B210155
  · exact B210159
  · exact B210163
  · exact B210167
  · exact B210171
  · exact B210175
  · exact B210179
  · exact B210183
  · exact B210187
  · exact B210191
  · exact B210195
  · exact B210199
  · exact B210203
  · exact B210207
  · exact B210211
  · exact B210215
  · exact B210219
  · exact B210223
  · exact B210227
  · exact B210231
  · exact B210235
  · exact B210239
  · exact B210243
  · exact B210247
  · exact B210251
  · exact B210255
  · exact B210259
  · exact B210263
  · exact B210267
  · exact B210271
  · exact B210275
  · exact B210279
  · exact B210283
  · exact B210287
  · exact B210291
  · exact B210295
  · exact B210299
  · exact B210303
  · exact B210307
  · exact B210311
  · exact B210315
  · exact B210319
  · exact B210323
  · exact B210327
  · exact B210331
  · exact B210335
  · exact B210339
  · exact B210343
  · exact B210347
  · exact B210351
  · exact B210355
  · exact B210359
  · exact B210363
  · exact B210367
  · exact B210371
  · exact B210375
  · exact B210379
  · exact B210383
  · exact B210387
  · exact B210391
  · exact B210395
  · exact B210399
  · exact B210403
  · exact B210407
  · exact B210411
  · exact B210415
  · exact B210419
  · exact B210423
  · exact B210427
  · exact B210431
  · exact B210435
  · exact B210439
  · exact B210443
  · exact B210447
  · exact B210451
  · exact B210455
  · exact B210459
  · exact B210463
  · exact B210467
  · exact B210471
  · exact B210475
  · exact B210479
  · exact B210483
  · exact B210487
  · exact B210491
  · exact B210495
  · exact B210499
  · exact B210503
  · exact B210507
  · exact B210511
  · exact B210515
  · exact B210519
  · exact B210523
  · exact B210527
  · exact B210531
  · exact B210535
  · exact B210539
  · exact B210543
  · exact B210547
  · exact B210551
  · exact B210555
  · exact B210559
  · exact B210563
  · exact B210567
  · exact B210571
  · exact B210575
  · exact B210579
  · exact B210583
  · exact B210587
  · exact B210591
  · exact B210595
  · exact B210599
  · exact B210603
  · exact B210607

theorem C1 (j : ℕ) (h1 : 52652 ≤ j) (h2 : j ≤ 52951) : Blo 207808 (4 * j + 3) := by
  interval_cases j
  · exact B210611
  · exact B210615
  · exact B210619
  · exact B210623
  · exact B210627
  · exact B210631
  · exact B210635
  · exact B210639
  · exact B210643
  · exact B210647
  · exact B210651
  · exact B210655
  · exact B210659
  · exact B210663
  · exact B210667
  · exact B210671
  · exact B210675
  · exact B210679
  · exact B210683
  · exact B210687
  · exact B210691
  · exact B210695
  · exact B210699
  · exact B210703
  · exact B210707
  · exact B210711
  · exact B210715
  · exact B210719
  · exact B210723
  · exact B210727
  · exact B210731
  · exact B210735
  · exact B210739
  · exact B210743
  · exact B210747
  · exact B210751
  · exact B210755
  · exact B210759
  · exact B210763
  · exact B210767
  · exact B210771
  · exact B210775
  · exact B210779
  · exact B210783
  · exact B210787
  · exact B210791
  · exact B210795
  · exact B210799
  · exact B210803
  · exact B210807
  · exact B210811
  · exact B210815
  · exact B210819
  · exact B210823
  · exact B210827
  · exact B210831
  · exact B210835
  · exact B210839
  · exact B210843
  · exact B210847
  · exact B210851
  · exact B210855
  · exact B210859
  · exact B210863
  · exact B210867
  · exact B210871
  · exact B210875
  · exact B210879
  · exact B210883
  · exact B210887
  · exact B210891
  · exact B210895
  · exact B210899
  · exact B210903
  · exact B210907
  · exact B210911
  · exact B210915
  · exact B210919
  · exact B210923
  · exact B210927
  · exact B210931
  · exact B210935
  · exact B210939
  · exact B210943
  · exact B210947
  · exact B210951
  · exact B210955
  · exact B210959
  · exact B210963
  · exact B210967
  · exact B210971
  · exact B210975
  · exact B210979
  · exact B210983
  · exact B210987
  · exact B210991
  · exact B210995
  · exact B210999
  · exact B211003
  · exact B211007
  · exact B211011
  · exact B211015
  · exact B211019
  · exact B211023
  · exact B211027
  · exact B211031
  · exact B211035
  · exact B211039
  · exact B211043
  · exact B211047
  · exact B211051
  · exact B211055
  · exact B211059
  · exact B211063
  · exact B211067
  · exact B211071
  · exact B211075
  · exact B211079
  · exact B211083
  · exact B211087
  · exact B211091
  · exact B211095
  · exact B211099
  · exact B211103
  · exact B211107
  · exact B211111
  · exact B211115
  · exact B211119
  · exact B211123
  · exact B211127
  · exact B211131
  · exact B211135
  · exact B211139
  · exact B211143
  · exact B211147
  · exact B211151
  · exact B211155
  · exact B211159
  · exact B211163
  · exact B211167
  · exact B211171
  · exact B211175
  · exact B211179
  · exact B211183
  · exact B211187
  · exact B211191
  · exact B211195
  · exact B211199
  · exact B211203
  · exact B211207
  · exact B211211
  · exact B211215
  · exact B211219
  · exact B211223
  · exact B211227
  · exact B211231
  · exact B211235
  · exact B211239
  · exact B211243
  · exact B211247
  · exact B211251
  · exact B211255
  · exact B211259
  · exact B211263
  · exact B211267
  · exact B211271
  · exact B211275
  · exact B211279
  · exact B211283
  · exact B211287
  · exact B211291
  · exact B211295
  · exact B211299
  · exact B211303
  · exact B211307
  · exact B211311
  · exact B211315
  · exact B211319
  · exact B211323
  · exact B211327
  · exact B211331
  · exact B211335
  · exact B211339
  · exact B211343
  · exact B211347
  · exact B211351
  · exact B211355
  · exact B211359
  · exact B211363
  · exact B211367
  · exact B211371
  · exact B211375
  · exact B211379
  · exact B211383
  · exact B211387
  · exact B211391
  · exact B211395
  · exact B211399
  · exact B211403
  · exact B211407
  · exact B211411
  · exact B211415
  · exact B211419
  · exact B211423
  · exact B211427
  · exact B211431
  · exact B211435
  · exact B211439
  · exact B211443
  · exact B211447
  · exact B211451
  · exact B211455
  · exact B211459
  · exact B211463
  · exact B211467
  · exact B211471
  · exact B211475
  · exact B211479
  · exact B211483
  · exact B211487
  · exact B211491
  · exact B211495
  · exact B211499
  · exact B211503
  · exact B211507
  · exact B211511
  · exact B211515
  · exact B211519
  · exact B211523
  · exact B211527
  · exact B211531
  · exact B211535
  · exact B211539
  · exact B211543
  · exact B211547
  · exact B211551
  · exact B211555
  · exact B211559
  · exact B211563
  · exact B211567
  · exact B211571
  · exact B211575
  · exact B211579
  · exact B211583
  · exact B211587
  · exact B211591
  · exact B211595
  · exact B211599
  · exact B211603
  · exact B211607
  · exact B211611
  · exact B211615
  · exact B211619
  · exact B211623
  · exact B211627
  · exact B211631
  · exact B211635
  · exact B211639
  · exact B211643
  · exact B211647
  · exact B211651
  · exact B211655
  · exact B211659
  · exact B211663
  · exact B211667
  · exact B211671
  · exact B211675
  · exact B211679
  · exact B211683
  · exact B211687
  · exact B211691
  · exact B211695
  · exact B211699
  · exact B211703
  · exact B211707
  · exact B211711
  · exact B211715
  · exact B211719
  · exact B211723
  · exact B211727
  · exact B211731
  · exact B211735
  · exact B211739
  · exact B211743
  · exact B211747
  · exact B211751
  · exact B211755
  · exact B211759
  · exact B211763
  · exact B211767
  · exact B211771
  · exact B211775
  · exact B211779
  · exact B211783
  · exact B211787
  · exact B211791
  · exact B211795
  · exact B211799
  · exact B211803
  · exact B211807

theorem solution (m : ℕ) (hlo : 207808 ≤ m) (hhi : m ≤ 211808) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 51952 ≤ j := by omega
    have hj2 : j ≤ 52951 := by omega
    have hb : Blo 207808 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 52652 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
