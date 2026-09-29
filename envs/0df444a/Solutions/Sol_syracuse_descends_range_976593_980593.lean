-- Prove2me | solution 1 for syracuse_descends_range_976593_980593
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:06.76169+00:00
-- url     : https://prove2.me/submissions/4fba4f51-6c44-40d2-836d-6dbaf629f235

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


theorem B6685109 : Blo 976593 6685109 := bbase (se 5 (by rfl) ⟨313364, by rfl⟩ : syracuseStep 6685109 = 626729) (by norm_num)
theorem B8028629 : Blo 976593 8028629 := bbase (se 7 (by rfl) ⟨94085, by rfl⟩ : syracuseStep 8028629 = 188171) (by norm_num)
theorem B4948613 : Blo 976593 4948613 := bbase (se 4 (by rfl) ⟨463932, by rfl⟩ : syracuseStep 4948613 = 927865) (by norm_num)
theorem B10060469 : Blo 976593 10060469 := bbase (se 5 (by rfl) ⟨471584, by rfl⟩ : syracuseStep 10060469 = 943169) (by norm_num)
theorem B1114825 : Blo 976593 1114825 := bbase (se 2 (by rfl) ⟨418059, by rfl⟩ : syracuseStep 1114825 = 836119) (by norm_num)
theorem B7144213 : Blo 976593 7144213 := bbase (se 6 (by rfl) ⟨167442, by rfl⟩ : syracuseStep 7144213 = 334885) (by norm_num)
theorem B1409909 : Blo 976593 1409909 := bbase (se 5 (by rfl) ⟨66089, by rfl⟩ : syracuseStep 1409909 = 132179) (by norm_num)
theorem B1114997 : Blo 976593 1114997 := bbase (se 5 (by rfl) ⟨52265, by rfl⟩ : syracuseStep 1114997 = 104531) (by norm_num)
theorem B9405557 : Blo 976593 9405557 := bbase (se 5 (by rfl) ⟨440885, by rfl⟩ : syracuseStep 9405557 = 881771) (by norm_num)
theorem B2786501 : Blo 976593 2786501 := bbase (se 4 (by rfl) ⟨261234, by rfl⟩ : syracuseStep 2786501 = 522469) (by norm_num)
theorem B4458053 : Blo 976593 4458053 := bbase (se 4 (by rfl) ⟨417942, by rfl⟩ : syracuseStep 4458053 = 835885) (by norm_num)
theorem B1672805 : Blo 976593 1672805 := bbase (se 4 (by rfl) ⟨156825, by rfl⟩ : syracuseStep 1672805 = 313651) (by norm_num)
theorem B1836805 : Blo 976593 1836805 := bbase (se 4 (by rfl) ⟨172200, by rfl⟩ : syracuseStep 1836805 = 344401) (by norm_num)
theorem B1673029 : Blo 976593 1673029 := bbase (se 4 (by rfl) ⟨156846, by rfl⟩ : syracuseStep 1673029 = 313693) (by norm_num)
theorem B2197349 : Blo 976593 2197349 := bbase (se 4 (by rfl) ⟨206001, by rfl⟩ : syracuseStep 2197349 = 412003) (by norm_num)
theorem B2787173 : Blo 976593 2787173 := bbase (se 4 (by rfl) ⟨261297, by rfl⟩ : syracuseStep 2787173 = 522595) (by norm_num)
theorem B4949909 : Blo 976593 4949909 := bbase (se 6 (by rfl) ⟨116013, by rfl⟩ : syracuseStep 4949909 = 232027) (by norm_num)
theorem B2197421 : Blo 976593 2197421 := bbase (se 3 (by rfl) ⟨412016, by rfl⟩ : syracuseStep 2197421 = 824033) (by norm_num)
theorem B2197493 : Blo 976593 2197493 := bbase (se 5 (by rfl) ⟨103007, by rfl⟩ : syracuseStep 2197493 = 206015) (by norm_num)
theorem B2197565 : Blo 976593 2197565 := bbase (se 3 (by rfl) ⟨412043, by rfl⟩ : syracuseStep 2197565 = 824087) (by norm_num)
theorem B1116229 : Blo 976593 1116229 := bbase (se 4 (by rfl) ⟨104646, by rfl⟩ : syracuseStep 1116229 = 209293) (by norm_num)
theorem B2197637 : Blo 976593 2197637 := bbase (se 4 (by rfl) ⟨206028, by rfl⟩ : syracuseStep 2197637 = 412057) (by norm_num)
theorem B2197709 : Blo 976593 2197709 := bbase (se 3 (by rfl) ⟨412070, by rfl⟩ : syracuseStep 2197709 = 824141) (by norm_num)
theorem B2197781 : Blo 976593 2197781 := bbase (se 6 (by rfl) ⟨51510, by rfl⟩ : syracuseStep 2197781 = 103021) (by norm_num)
theorem B2787605 : Blo 976593 2787605 := bbase (se 6 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 2787605 = 130669) (by norm_num)
theorem B2197853 : Blo 976593 2197853 := bbase (se 3 (by rfl) ⟨412097, by rfl⟩ : syracuseStep 2197853 = 824195) (by norm_num)
theorem B2197925 : Blo 976593 2197925 := bbase (se 4 (by rfl) ⟨206055, by rfl⟩ : syracuseStep 2197925 = 412111) (by norm_num)
theorem B2197997 : Blo 976593 2197997 := bbase (se 3 (by rfl) ⟨412124, by rfl⟩ : syracuseStep 2197997 = 824249) (by norm_num)
theorem B3574277 : Blo 976593 3574277 := bbase (se 4 (by rfl) ⟨335088, by rfl⟩ : syracuseStep 3574277 = 670177) (by norm_num)
theorem B2198069 : Blo 976593 2198069 := bbase (se 5 (by rfl) ⟨103034, by rfl⟩ : syracuseStep 2198069 = 206069) (by norm_num)
theorem B2198141 : Blo 976593 2198141 := bbase (se 3 (by rfl) ⟨412151, by rfl⟩ : syracuseStep 2198141 = 824303) (by norm_num)
theorem B1608317 : Blo 976593 1608317 := bbase (se 3 (by rfl) ⟨301559, by rfl⟩ : syracuseStep 1608317 = 603119) (by norm_num)
theorem B2198213 : Blo 976593 2198213 := bbase (se 4 (by rfl) ⟨206082, by rfl⟩ : syracuseStep 2198213 = 412165) (by norm_num)
theorem B2198285 : Blo 976593 2198285 := bbase (se 3 (by rfl) ⟨412178, by rfl⟩ : syracuseStep 2198285 = 824357) (by norm_num)
theorem B2198357 : Blo 976593 2198357 := bbase (se 9 (by rfl) ⟨6440, by rfl⟩ : syracuseStep 2198357 = 12881) (by norm_num)
theorem B2198429 : Blo 976593 2198429 := bbase (se 3 (by rfl) ⟨412205, by rfl⟩ : syracuseStep 2198429 = 824411) (by norm_num)
theorem B2198501 : Blo 976593 2198501 := bbase (se 4 (by rfl) ⟨206109, by rfl⟩ : syracuseStep 2198501 = 412219) (by norm_num)
theorem B1674229 : Blo 976593 1674229 := bbase (se 5 (by rfl) ⟨78479, by rfl⟩ : syracuseStep 1674229 = 156959) (by norm_num)
theorem B2788357 : Blo 976593 2788357 := bbase (se 4 (by rfl) ⟨261408, by rfl⟩ : syracuseStep 2788357 = 522817) (by norm_num)
theorem B2198573 : Blo 976593 2198573 := bbase (se 3 (by rfl) ⟨412232, by rfl⟩ : syracuseStep 2198573 = 824465) (by norm_num)
theorem B3771461 : Blo 976593 3771461 := bbase (se 4 (by rfl) ⟨353574, by rfl⟩ : syracuseStep 3771461 = 707149) (by norm_num)
theorem B2198645 : Blo 976593 2198645 := bbase (se 5 (by rfl) ⟨103061, by rfl⟩ : syracuseStep 2198645 = 206123) (by norm_num)
theorem B4951205 : Blo 976593 4951205 := bbase (se 4 (by rfl) ⟨464175, by rfl⟩ : syracuseStep 4951205 = 928351) (by norm_num)
theorem B2198717 : Blo 976593 2198717 := bbase (se 3 (by rfl) ⟨412259, by rfl⟩ : syracuseStep 2198717 = 824519) (by norm_num)
theorem B3181781 : Blo 976593 3181781 := bbase (se 7 (by rfl) ⟨37286, by rfl⟩ : syracuseStep 3181781 = 74573) (by norm_num)
theorem B1117433 : Blo 976593 1117433 := bbase (se 2 (by rfl) ⟨419037, by rfl⟩ : syracuseStep 1117433 = 838075) (by norm_num)
theorem B2198789 : Blo 976593 2198789 := bbase (se 4 (by rfl) ⟨206136, by rfl⟩ : syracuseStep 2198789 = 412273) (by norm_num)
theorem B2198861 : Blo 976593 2198861 := bbase (se 3 (by rfl) ⟨412286, by rfl⟩ : syracuseStep 2198861 = 824573) (by norm_num)
theorem B2198933 : Blo 976593 2198933 := bbase (se 6 (by rfl) ⟨51537, by rfl⟩ : syracuseStep 2198933 = 103075) (by norm_num)
theorem B2199005 : Blo 976593 2199005 := bbase (se 3 (by rfl) ⟨412313, by rfl⟩ : syracuseStep 2199005 = 824627) (by norm_num)
theorem B2199077 : Blo 976593 2199077 := bbase (se 4 (by rfl) ⟨206163, by rfl⟩ : syracuseStep 2199077 = 412327) (by norm_num)
theorem B2199149 : Blo 976593 2199149 := bbase (se 3 (by rfl) ⟨412340, by rfl⟩ : syracuseStep 2199149 = 824681) (by norm_num)
theorem B2199221 : Blo 976593 2199221 := bbase (se 5 (by rfl) ⟨103088, by rfl⟩ : syracuseStep 2199221 = 206177) (by norm_num)
theorem B2199293 : Blo 976593 2199293 := bbase (se 3 (by rfl) ⟨412367, by rfl⟩ : syracuseStep 2199293 = 824735) (by norm_num)
theorem B2199365 : Blo 976593 2199365 := bbase (se 4 (by rfl) ⟨206190, by rfl⟩ : syracuseStep 2199365 = 412381) (by norm_num)
theorem B2199437 : Blo 976593 2199437 := bbase (se 3 (by rfl) ⟨412394, by rfl⟩ : syracuseStep 2199437 = 824789) (by norm_num)
theorem B3772325 : Blo 976593 3772325 := bbase (se 4 (by rfl) ⟨353655, by rfl⟩ : syracuseStep 3772325 = 707311) (by norm_num)
theorem B2199509 : Blo 976593 2199509 := bbase (se 7 (by rfl) ⟨25775, by rfl⟩ : syracuseStep 2199509 = 51551) (by norm_num)
theorem B2199581 : Blo 976593 2199581 := bbase (se 3 (by rfl) ⟨412421, by rfl⟩ : syracuseStep 2199581 = 824843) (by norm_num)
theorem B2199653 : Blo 976593 2199653 := bbase (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) (by norm_num)
theorem B2199725 : Blo 976593 2199725 := bbase (se 3 (by rfl) ⟨412448, by rfl⟩ : syracuseStep 2199725 = 824897) (by norm_num)
theorem B2199797 : Blo 976593 2199797 := bbase (se 5 (by rfl) ⟨103115, by rfl⟩ : syracuseStep 2199797 = 206231) (by norm_num)
theorem B3969317 : Blo 976593 3969317 := bbase (se 4 (by rfl) ⟨372123, by rfl⟩ : syracuseStep 3969317 = 744247) (by norm_num)
theorem B2199869 : Blo 976593 2199869 := bbase (se 3 (by rfl) ⟨412475, by rfl⟩ : syracuseStep 2199869 = 824951) (by norm_num)
theorem B2199941 : Blo 976593 2199941 := bbase (se 4 (by rfl) ⟨206244, by rfl⟩ : syracuseStep 2199941 = 412489) (by norm_num)
theorem B4952501 : Blo 976593 4952501 := bbase (se 5 (by rfl) ⟨232148, by rfl⟩ : syracuseStep 4952501 = 464297) (by norm_num)
theorem B2200013 : Blo 976593 2200013 := bbase (se 3 (by rfl) ⟨412502, by rfl⟩ : syracuseStep 2200013 = 825005) (by norm_num)
theorem B2200085 : Blo 976593 2200085 := bbase (se 6 (by rfl) ⟨51564, by rfl⟩ : syracuseStep 2200085 = 103129) (by norm_num)
theorem B12554837 : Blo 976593 12554837 := bbase (se 8 (by rfl) ⟨73563, by rfl⟩ : syracuseStep 12554837 = 147127) (by norm_num)
theorem B2200157 : Blo 976593 2200157 := bbase (se 3 (by rfl) ⟨412529, by rfl⟩ : syracuseStep 2200157 = 825059) (by norm_num)
theorem B3347045 : Blo 976593 3347045 := bbase (se 4 (by rfl) ⟨313785, by rfl⟩ : syracuseStep 3347045 = 627571) (by norm_num)
theorem B2200229 : Blo 976593 2200229 := bbase (se 4 (by rfl) ⟨206271, by rfl⟩ : syracuseStep 2200229 = 412543) (by norm_num)
theorem B5083829 : Blo 976593 5083829 := bbase (se 5 (by rfl) ⟨238304, by rfl⟩ : syracuseStep 5083829 = 476609) (by norm_num)
theorem B6263477 : Blo 976593 6263477 := bbase (se 5 (by rfl) ⟨293600, by rfl⟩ : syracuseStep 6263477 = 587201) (by norm_num)
theorem B2233061 : Blo 976593 2233061 := bbase (se 4 (by rfl) ⟨209349, by rfl⟩ : syracuseStep 2233061 = 418699) (by norm_num)
theorem B2200301 : Blo 976593 2200301 := bbase (se 3 (by rfl) ⟨412556, by rfl⟩ : syracuseStep 2200301 = 825113) (by norm_num)
theorem B2200373 : Blo 976593 2200373 := bbase (se 5 (by rfl) ⟨103142, by rfl⟩ : syracuseStep 2200373 = 206285) (by norm_num)
theorem B1413941 : Blo 976593 1413941 := bbase (se 5 (by rfl) ⟨66278, by rfl⟩ : syracuseStep 1413941 = 132557) (by norm_num)
theorem B2200445 : Blo 976593 2200445 := bbase (se 3 (by rfl) ⟨412583, by rfl⟩ : syracuseStep 2200445 = 825167) (by norm_num)
theorem B2233261 : Blo 976593 2233261 := bbase (se 3 (by rfl) ⟨418736, by rfl⟩ : syracuseStep 2233261 = 837473) (by norm_num)
theorem B2200517 : Blo 976593 2200517 := bbase (se 4 (by rfl) ⟨206298, by rfl⟩ : syracuseStep 2200517 = 412597) (by norm_num)
theorem B2200589 : Blo 976593 2200589 := bbase (se 3 (by rfl) ⟨412610, by rfl⟩ : syracuseStep 2200589 = 825221) (by norm_num)
theorem B2200661 : Blo 976593 2200661 := bbase (se 8 (by rfl) ⟨12894, by rfl⟩ : syracuseStep 2200661 = 25789) (by norm_num)
theorem B2200733 : Blo 976593 2200733 := bbase (se 3 (by rfl) ⟨412637, by rfl⟩ : syracuseStep 2200733 = 825275) (by norm_num)
theorem B2200805 : Blo 976593 2200805 := bbase (se 4 (by rfl) ⟨206325, by rfl⟩ : syracuseStep 2200805 = 412651) (by norm_num)
theorem B2200877 : Blo 976593 2200877 := bbase (se 3 (by rfl) ⟨412664, by rfl⟩ : syracuseStep 2200877 = 825329) (by norm_num)
theorem B2200949 : Blo 976593 2200949 := bbase (se 5 (by rfl) ⟨103169, by rfl⟩ : syracuseStep 2200949 = 206339) (by norm_num)
theorem B2201021 : Blo 976593 2201021 := bbase (se 3 (by rfl) ⟨412691, by rfl⟩ : syracuseStep 2201021 = 825383) (by norm_num)
theorem B2201093 : Blo 976593 2201093 := bbase (se 4 (by rfl) ⟨206352, by rfl⟩ : syracuseStep 2201093 = 412705) (by norm_num)
theorem B2201165 : Blo 976593 2201165 := bbase (se 3 (by rfl) ⟨412718, by rfl⟩ : syracuseStep 2201165 = 825437) (by norm_num)
theorem B2201237 : Blo 976593 2201237 := bbase (se 6 (by rfl) ⟨51591, by rfl⟩ : syracuseStep 2201237 = 103183) (by norm_num)
theorem B4953797 : Blo 976593 4953797 := bbase (se 4 (by rfl) ⟨464418, by rfl⟩ : syracuseStep 4953797 = 928837) (by norm_num)
theorem B2201309 : Blo 976593 2201309 := bbase (se 3 (by rfl) ⟨412745, by rfl⟩ : syracuseStep 2201309 = 825491) (by norm_num)
theorem B2234101 : Blo 976593 2234101 := bbase (se 5 (by rfl) ⟨104723, by rfl⟩ : syracuseStep 2234101 = 209447) (by norm_num)
theorem B2201381 : Blo 976593 2201381 := bbase (se 4 (by rfl) ⟨206379, by rfl⟩ : syracuseStep 2201381 = 412759) (by norm_num)
theorem B2791205 : Blo 976593 2791205 := bbase (se 4 (by rfl) ⟨261675, by rfl⟩ : syracuseStep 2791205 = 523351) (by norm_num)
theorem B3708773 : Blo 976593 3708773 := bbase (se 4 (by rfl) ⟨347697, by rfl⟩ : syracuseStep 3708773 = 695395) (by norm_num)
theorem B2201453 : Blo 976593 2201453 := bbase (se 3 (by rfl) ⟨412772, by rfl⟩ : syracuseStep 2201453 = 825545) (by norm_num)
theorem B2201525 : Blo 976593 2201525 := bbase (se 5 (by rfl) ⟨103196, by rfl⟩ : syracuseStep 2201525 = 206393) (by norm_num)
theorem B2201597 : Blo 976593 2201597 := bbase (se 3 (by rfl) ⟨412799, by rfl⟩ : syracuseStep 2201597 = 825599) (by norm_num)
theorem B1906709 : Blo 976593 1906709 := bbase (se 6 (by rfl) ⟨44688, by rfl⟩ : syracuseStep 1906709 = 89377) (by norm_num)
theorem B2201669 : Blo 976593 2201669 := bbase (se 4 (by rfl) ⟨206406, by rfl⟩ : syracuseStep 2201669 = 412813) (by norm_num)
theorem B3709061 : Blo 976593 3709061 := bbase (se 4 (by rfl) ⟨347724, by rfl⟩ : syracuseStep 3709061 = 695449) (by norm_num)
theorem B2201741 : Blo 976593 2201741 := bbase (se 3 (by rfl) ⟨412826, by rfl⟩ : syracuseStep 2201741 = 825653) (by norm_num)
theorem B2201813 : Blo 976593 2201813 := bbase (se 7 (by rfl) ⟨25802, by rfl⟩ : syracuseStep 2201813 = 51605) (by norm_num)
theorem B2201885 : Blo 976593 2201885 := bbase (se 3 (by rfl) ⟨412853, by rfl⟩ : syracuseStep 2201885 = 825707) (by norm_num)
theorem B2201957 : Blo 976593 2201957 := bbase (se 4 (by rfl) ⟨206433, by rfl⟩ : syracuseStep 2201957 = 412867) (by norm_num)
theorem B2202029 : Blo 976593 2202029 := bbase (se 3 (by rfl) ⟨412880, by rfl⟩ : syracuseStep 2202029 = 825761) (by norm_num)
theorem B3578309 : Blo 976593 3578309 := bbase (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) (by norm_num)
theorem B2202101 : Blo 976593 2202101 := bbase (se 5 (by rfl) ⟨103223, by rfl⟩ : syracuseStep 2202101 = 206447) (by norm_num)
theorem B2202173 : Blo 976593 2202173 := bbase (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) (by norm_num)
theorem B4463237 : Blo 976593 4463237 := bbase (se 4 (by rfl) ⟨418428, by rfl⟩ : syracuseStep 4463237 = 836857) (by norm_num)
theorem B2202245 : Blo 976593 2202245 := bbase (se 4 (by rfl) ⟨206460, by rfl⟩ : syracuseStep 2202245 = 412921) (by norm_num)
theorem B3676837 : Blo 976593 3676837 := bbase (se 4 (by rfl) ⟨344703, by rfl⟩ : syracuseStep 3676837 = 689407) (by norm_num)
theorem B2235077 : Blo 976593 2235077 := bbase (se 4 (by rfl) ⟨209538, by rfl⟩ : syracuseStep 2235077 = 419077) (by norm_num)
theorem B2202317 : Blo 976593 2202317 := bbase (se 3 (by rfl) ⟨412934, by rfl⟩ : syracuseStep 2202317 = 825869) (by norm_num)
theorem B989965 : Blo 976593 989965 := bbase (se 3 (by rfl) ⟨185618, by rfl⟩ : syracuseStep 989965 = 371237) (by norm_num)
theorem B2202389 : Blo 976593 2202389 := bbase (se 6 (by rfl) ⟨51618, by rfl⟩ : syracuseStep 2202389 = 103237) (by norm_num)
theorem B2202461 : Blo 976593 2202461 := bbase (se 3 (by rfl) ⟨412961, by rfl⟩ : syracuseStep 2202461 = 825923) (by norm_num)
theorem B2235269 : Blo 976593 2235269 := bbase (se 4 (by rfl) ⟨209556, by rfl⟩ : syracuseStep 2235269 = 419113) (by norm_num)
theorem B2202533 : Blo 976593 2202533 := bbase (se 4 (by rfl) ⟨206487, by rfl⟩ : syracuseStep 2202533 = 412975) (by norm_num)
theorem B2792389 : Blo 976593 2792389 := bbase (se 4 (by rfl) ⟨261786, by rfl⟩ : syracuseStep 2792389 = 523573) (by norm_num)
theorem B4955093 : Blo 976593 4955093 := bbase (se 7 (by rfl) ⟨58067, by rfl⟩ : syracuseStep 4955093 = 116135) (by norm_num)
theorem B2202605 : Blo 976593 2202605 := bbase (se 3 (by rfl) ⟨412988, by rfl⟩ : syracuseStep 2202605 = 825977) (by norm_num)
theorem B4299797 : Blo 976593 4299797 := bbase (se 6 (by rfl) ⟨100776, by rfl⟩ : syracuseStep 4299797 = 201553) (by norm_num)
theorem B2202677 : Blo 976593 2202677 := bbase (se 5 (by rfl) ⟨103250, by rfl⟩ : syracuseStep 2202677 = 206501) (by norm_num)
theorem B2202749 : Blo 976593 2202749 := bbase (se 3 (by rfl) ⟨413015, by rfl⟩ : syracuseStep 2202749 = 826031) (by norm_num)
theorem B2202821 : Blo 976593 2202821 := bbase (se 4 (by rfl) ⟨206514, by rfl⟩ : syracuseStep 2202821 = 413029) (by norm_num)
theorem B2202893 : Blo 976593 2202893 := bbase (se 3 (by rfl) ⟨413042, by rfl⟩ : syracuseStep 2202893 = 826085) (by norm_num)
theorem B3710245 : Blo 976593 3710245 := bbase (se 4 (by rfl) ⟨347835, by rfl⟩ : syracuseStep 3710245 = 695671) (by norm_num)
theorem B2202965 : Blo 976593 2202965 := bbase (se 11 (by rfl) ⟨1613, by rfl⟩ : syracuseStep 2202965 = 3227) (by norm_num)
theorem B4234613 : Blo 976593 4234613 := bbase (se 5 (by rfl) ⟨198497, by rfl⟩ : syracuseStep 4234613 = 396995) (by norm_num)
theorem B2203037 : Blo 976593 2203037 := bbase (se 3 (by rfl) ⟨413069, by rfl⟩ : syracuseStep 2203037 = 826139) (by norm_num)
theorem B2203109 : Blo 976593 2203109 := bbase (se 4 (by rfl) ⟨206541, by rfl⟩ : syracuseStep 2203109 = 413083) (by norm_num)
theorem B7446005 : Blo 976593 7446005 := bbase (se 5 (by rfl) ⟨349031, by rfl⟩ : syracuseStep 7446005 = 698063) (by norm_num)
theorem B2203181 : Blo 976593 2203181 := bbase (se 3 (by rfl) ⟨413096, by rfl⟩ : syracuseStep 2203181 = 826193) (by norm_num)
theorem B3710549 : Blo 976593 3710549 := bbase (se 8 (by rfl) ⟨21741, by rfl⟩ : syracuseStep 3710549 = 43483) (by norm_num)
theorem B2203253 : Blo 976593 2203253 := bbase (se 5 (by rfl) ⟨103277, by rfl⟩ : syracuseStep 2203253 = 206555) (by norm_num)
theorem B5086901 : Blo 976593 5086901 := bbase (se 5 (by rfl) ⟨238448, by rfl⟩ : syracuseStep 5086901 = 476897) (by norm_num)
theorem B2203325 : Blo 976593 2203325 := bbase (se 3 (by rfl) ⟨413123, by rfl⟩ : syracuseStep 2203325 = 826247) (by norm_num)
theorem B2203397 : Blo 976593 2203397 := bbase (se 4 (by rfl) ⟨206568, by rfl⟩ : syracuseStep 2203397 = 413137) (by norm_num)
theorem B4693781 : Blo 976593 4693781 := bbase (se 6 (by rfl) ⟨110010, by rfl⟩ : syracuseStep 4693781 = 220021) (by norm_num)
theorem B2203469 : Blo 976593 2203469 := bbase (se 3 (by rfl) ⟨413150, by rfl⟩ : syracuseStep 2203469 = 826301) (by norm_num)
theorem B2236253 : Blo 976593 2236253 := bbase (se 3 (by rfl) ⟨419297, by rfl⟩ : syracuseStep 2236253 = 838595) (by norm_num)
theorem B2203541 : Blo 976593 2203541 := bbase (se 6 (by rfl) ⟨51645, by rfl⟩ : syracuseStep 2203541 = 103291) (by norm_num)
theorem B2203613 : Blo 976593 2203613 := bbase (se 3 (by rfl) ⟨413177, by rfl⟩ : syracuseStep 2203613 = 826355) (by norm_num)
theorem B2203685 : Blo 976593 2203685 := bbase (se 4 (by rfl) ⟨206595, by rfl⟩ : syracuseStep 2203685 = 413191) (by norm_num)
theorem B2203757 : Blo 976593 2203757 := bbase (se 3 (by rfl) ⟨413204, by rfl⟩ : syracuseStep 2203757 = 826409) (by norm_num)
theorem B8364181 : Blo 976593 8364181 := bbase (se 6 (by rfl) ⟨196035, by rfl⟩ : syracuseStep 8364181 = 392071) (by norm_num)
theorem B5578901 : Blo 976593 5578901 := bbase (se 6 (by rfl) ⟨130755, by rfl⟩ : syracuseStep 5578901 = 261511) (by norm_num)
theorem B2203829 : Blo 976593 2203829 := bbase (se 5 (by rfl) ⟨103304, by rfl⟩ : syracuseStep 2203829 = 206609) (by norm_num)
theorem B4956389 : Blo 976593 4956389 := bbase (se 4 (by rfl) ⟨464661, by rfl⟩ : syracuseStep 4956389 = 929323) (by norm_num)
theorem B2203901 : Blo 976593 2203901 := bbase (se 3 (by rfl) ⟨413231, by rfl⟩ : syracuseStep 2203901 = 826463) (by norm_num)
theorem B2203973 : Blo 976593 2203973 := bbase (se 4 (by rfl) ⟨206622, by rfl⟩ : syracuseStep 2203973 = 413245) (by norm_num)
theorem B2204045 : Blo 976593 2204045 := bbase (se 3 (by rfl) ⟨413258, by rfl⟩ : syracuseStep 2204045 = 826517) (by norm_num)
theorem B3350933 : Blo 976593 3350933 := bbase (se 6 (by rfl) ⟨78537, by rfl⟩ : syracuseStep 3350933 = 157075) (by norm_num)
theorem B2204117 : Blo 976593 2204117 := bbase (se 7 (by rfl) ⟨25829, by rfl⟩ : syracuseStep 2204117 = 51659) (by norm_num)
theorem B1810973 : Blo 976593 1810973 := bbase (se 3 (by rfl) ⟨339557, by rfl⟩ : syracuseStep 1810973 = 679115) (by norm_num)
theorem B2204189 : Blo 976593 2204189 := bbase (se 3 (by rfl) ⟨413285, by rfl⟩ : syracuseStep 2204189 = 826571) (by norm_num)
theorem B2204261 : Blo 976593 2204261 := bbase (se 4 (by rfl) ⟨206649, by rfl⟩ : syracuseStep 2204261 = 413299) (by norm_num)
theorem B2204333 : Blo 976593 2204333 := bbase (se 3 (by rfl) ⟨413312, by rfl⟩ : syracuseStep 2204333 = 826625) (by norm_num)
theorem B2204405 : Blo 976593 2204405 := bbase (se 5 (by rfl) ⟨103331, by rfl⟩ : syracuseStep 2204405 = 206663) (by norm_num)
theorem B992017 : Blo 976593 992017 := bbase (se 2 (by rfl) ⟨372006, by rfl⟩ : syracuseStep 992017 = 744013) (by norm_num)
theorem B2204477 : Blo 976593 2204477 := bbase (se 3 (by rfl) ⟨413339, by rfl⟩ : syracuseStep 2204477 = 826679) (by norm_num)
theorem B2204549 : Blo 976593 2204549 := bbase (se 4 (by rfl) ⟨206676, by rfl⟩ : syracuseStep 2204549 = 413353) (by norm_num)
theorem B2204621 : Blo 976593 2204621 := bbase (se 3 (by rfl) ⟨413366, by rfl⟩ : syracuseStep 2204621 = 826733) (by norm_num)
theorem B1057789 : Blo 976593 1057789 := bbase (se 3 (by rfl) ⟨198335, by rfl⟩ : syracuseStep 1057789 = 396671) (by norm_num)
theorem B2204693 : Blo 976593 2204693 := bbase (se 6 (by rfl) ⟨51672, by rfl⟩ : syracuseStep 2204693 = 103345) (by norm_num)
theorem B1254485 : Blo 976593 1254485 := bbase (se 8 (by rfl) ⟨7350, by rfl⟩ : syracuseStep 1254485 = 14701) (by norm_num)
theorem B2204765 : Blo 976593 2204765 := bbase (se 3 (by rfl) ⟨413393, by rfl⟩ : syracuseStep 2204765 = 826787) (by norm_num)
theorem B4695205 : Blo 976593 4695205 := bbase (se 4 (by rfl) ⟨440175, by rfl⟩ : syracuseStep 4695205 = 880351) (by norm_num)
theorem B2204837 : Blo 976593 2204837 := bbase (se 4 (by rfl) ⟨206703, by rfl⟩ : syracuseStep 2204837 = 413407) (by norm_num)
theorem B2204909 : Blo 976593 2204909 := bbase (se 3 (by rfl) ⟨413420, by rfl⟩ : syracuseStep 2204909 = 826841) (by norm_num)
theorem B2204981 : Blo 976593 2204981 := bbase (se 5 (by rfl) ⟨103358, by rfl⟩ : syracuseStep 2204981 = 206717) (by norm_num)
theorem B1058125 : Blo 976593 1058125 := bbase (se 3 (by rfl) ⟨198398, by rfl⟩ : syracuseStep 1058125 = 396797) (by norm_num)
theorem B2205053 : Blo 976593 2205053 := bbase (se 3 (by rfl) ⟨413447, by rfl⟩ : syracuseStep 2205053 = 826895) (by norm_num)
theorem B2860469 : Blo 976593 2860469 := bbase (se 5 (by rfl) ⟨134084, by rfl⟩ : syracuseStep 2860469 = 268169) (by norm_num)
theorem B2205125 : Blo 976593 2205125 := bbase (se 4 (by rfl) ⟨206730, by rfl⟩ : syracuseStep 2205125 = 413461) (by norm_num)
theorem B1648093 : Blo 976593 1648093 := bbase (se 3 (by rfl) ⟨309017, by rfl⟩ : syracuseStep 1648093 = 618035) (by norm_num)
theorem B4957685 : Blo 976593 4957685 := bbase (se 5 (by rfl) ⟨232391, by rfl⟩ : syracuseStep 4957685 = 464783) (by norm_num)
theorem B2205197 : Blo 976593 2205197 := bbase (se 3 (by rfl) ⟨413474, by rfl⟩ : syracuseStep 2205197 = 826949) (by norm_num)
theorem B1058333 : Blo 976593 1058333 := bbase (se 3 (by rfl) ⟨198437, by rfl⟩ : syracuseStep 1058333 = 396875) (by norm_num)
theorem B1648181 : Blo 976593 1648181 := bbase (se 5 (by rfl) ⟨77258, by rfl⟩ : syracuseStep 1648181 = 154517) (by norm_num)
theorem B4236869 : Blo 976593 4236869 := bbase (se 4 (by rfl) ⟨397206, by rfl⟩ : syracuseStep 4236869 = 794413) (by norm_num)
theorem B2205269 : Blo 976593 2205269 := bbase (se 8 (by rfl) ⟨12921, by rfl⟩ : syracuseStep 2205269 = 25843) (by norm_num)
theorem B6039157 : Blo 976593 6039157 := bbase (se 5 (by rfl) ⟨283085, by rfl⟩ : syracuseStep 6039157 = 566171) (by norm_num)
theorem B1320581 : Blo 976593 1320581 := bbase (se 4 (by rfl) ⟨123804, by rfl⟩ : syracuseStep 1320581 = 247609) (by norm_num)
theorem B3712661 : Blo 976593 3712661 := bbase (se 6 (by rfl) ⟨87015, by rfl⟩ : syracuseStep 3712661 = 174031) (by norm_num)
theorem B2205341 : Blo 976593 2205341 := bbase (se 3 (by rfl) ⟨413501, by rfl⟩ : syracuseStep 2205341 = 827003) (by norm_num)
theorem B1648309 : Blo 976593 1648309 := bbase (se 5 (by rfl) ⟨77264, by rfl⟩ : syracuseStep 1648309 = 154529) (by norm_num)
theorem B2205413 : Blo 976593 2205413 := bbase (se 4 (by rfl) ⟨206757, by rfl⟩ : syracuseStep 2205413 = 413515) (by norm_num)
theorem B1648397 : Blo 976593 1648397 := bbase (se 3 (by rfl) ⟨309074, by rfl⟩ : syracuseStep 1648397 = 618149) (by norm_num)
theorem B2205485 : Blo 976593 2205485 := bbase (se 3 (by rfl) ⟨413528, by rfl⟩ : syracuseStep 2205485 = 827057) (by norm_num)
theorem B2205557 : Blo 976593 2205557 := bbase (se 5 (by rfl) ⟨103385, by rfl⟩ : syracuseStep 2205557 = 206771) (by norm_num)
theorem B1648525 : Blo 976593 1648525 := bbase (se 3 (by rfl) ⟨309098, by rfl⟩ : syracuseStep 1648525 = 618197) (by norm_num)
theorem B3712949 : Blo 976593 3712949 := bbase (se 5 (by rfl) ⟨174044, by rfl⟩ : syracuseStep 3712949 = 348089) (by norm_num)
theorem B2205629 : Blo 976593 2205629 := bbase (se 3 (by rfl) ⟨413555, by rfl⟩ : syracuseStep 2205629 = 827111) (by norm_num)
theorem B1648613 : Blo 976593 1648613 := bbase (se 4 (by rfl) ⟨154557, by rfl⟩ : syracuseStep 1648613 = 309115) (by norm_num)
theorem B2205701 : Blo 976593 2205701 := bbase (se 4 (by rfl) ⟨206784, by rfl⟩ : syracuseStep 2205701 = 413569) (by norm_num)
theorem B1255441 : Blo 976593 1255441 := bbase (se 2 (by rfl) ⟨470790, by rfl⟩ : syracuseStep 1255441 = 941581) (by norm_num)
theorem B2205773 : Blo 976593 2205773 := bbase (se 3 (by rfl) ⟨413582, by rfl⟩ : syracuseStep 2205773 = 827165) (by norm_num)
theorem B8366165 : Blo 976593 8366165 := bbase (se 8 (by rfl) ⟨49020, by rfl⟩ : syracuseStep 8366165 = 98041) (by norm_num)
theorem B1648741 : Blo 976593 1648741 := bbase (se 4 (by rfl) ⟨154569, by rfl⟩ : syracuseStep 1648741 = 309139) (by norm_num)
theorem B2205845 : Blo 976593 2205845 := bbase (se 6 (by rfl) ⟨51699, by rfl⟩ : syracuseStep 2205845 = 103399) (by norm_num)
theorem B1648829 : Blo 976593 1648829 := bbase (se 3 (by rfl) ⟨309155, by rfl⟩ : syracuseStep 1648829 = 618311) (by norm_num)
theorem B2205917 : Blo 976593 2205917 := bbase (se 3 (by rfl) ⟨413609, by rfl⟩ : syracuseStep 2205917 = 827219) (by norm_num)
theorem B2205989 : Blo 976593 2205989 := bbase (se 4 (by rfl) ⟨206811, by rfl⟩ : syracuseStep 2205989 = 413623) (by norm_num)
theorem B1648957 : Blo 976593 1648957 := bbase (se 3 (by rfl) ⟨309179, by rfl⟩ : syracuseStep 1648957 = 618359) (by norm_num)
theorem B2206061 : Blo 976593 2206061 := bbase (se 3 (by rfl) ⟨413636, by rfl⟩ : syracuseStep 2206061 = 827273) (by norm_num)
theorem B1649045 : Blo 976593 1649045 := bbase (se 6 (by rfl) ⟨38649, by rfl⟩ : syracuseStep 1649045 = 77299) (by norm_num)
theorem B1321381 : Blo 976593 1321381 := bbase (se 4 (by rfl) ⟨123879, by rfl⟩ : syracuseStep 1321381 = 247759) (by norm_num)
theorem B2206133 : Blo 976593 2206133 := bbase (se 5 (by rfl) ⟨103412, by rfl⟩ : syracuseStep 2206133 = 206825) (by norm_num)
theorem B2206205 : Blo 976593 2206205 := bbase (se 3 (by rfl) ⟨413663, by rfl⟩ : syracuseStep 2206205 = 827327) (by norm_num)
theorem B1649173 : Blo 976593 1649173 := bbase (se 6 (by rfl) ⟨38652, by rfl⟩ : syracuseStep 1649173 = 77305) (by norm_num)
theorem B9054773 : Blo 976593 9054773 := bbase (se 5 (by rfl) ⟨424442, by rfl⟩ : syracuseStep 9054773 = 848885) (by norm_num)
theorem B2206277 : Blo 976593 2206277 := bbase (se 4 (by rfl) ⟨206838, by rfl⟩ : syracuseStep 2206277 = 413677) (by norm_num)
theorem B1649261 : Blo 976593 1649261 := bbase (se 3 (by rfl) ⟨309236, by rfl⟩ : syracuseStep 1649261 = 618473) (by norm_num)
theorem B1059485 : Blo 976593 1059485 := bbase (se 3 (by rfl) ⟨198653, by rfl⟩ : syracuseStep 1059485 = 397307) (by norm_num)
theorem B1288921 : Blo 976593 1288921 := bbase (se 2 (by rfl) ⟨483345, by rfl⟩ : syracuseStep 1288921 = 966691) (by norm_num)
theorem B1649389 : Blo 976593 1649389 := bbase (se 3 (by rfl) ⟨309260, by rfl⟩ : syracuseStep 1649389 = 618521) (by norm_num)
theorem B4958981 : Blo 976593 4958981 := bbase (se 4 (by rfl) ⟨464904, by rfl⟩ : syracuseStep 4958981 = 929809) (by norm_num)
theorem B1649477 : Blo 976593 1649477 := bbase (se 4 (by rfl) ⟨154638, by rfl⟩ : syracuseStep 1649477 = 309277) (by norm_num)
theorem B4533157 : Blo 976593 4533157 := bbase (se 4 (by rfl) ⟨424983, by rfl⟩ : syracuseStep 4533157 = 849967) (by norm_num)
theorem B1649605 : Blo 976593 1649605 := bbase (se 4 (by rfl) ⟨154650, by rfl⟩ : syracuseStep 1649605 = 309301) (by norm_num)
theorem B1649693 : Blo 976593 1649693 := bbase (se 3 (by rfl) ⟨309317, by rfl⟩ : syracuseStep 1649693 = 618635) (by norm_num)
theorem B1322029 : Blo 976593 1322029 := bbase (se 3 (by rfl) ⟨247880, by rfl⟩ : syracuseStep 1322029 = 495761) (by norm_num)
theorem B3714133 : Blo 976593 3714133 := bbase (se 8 (by rfl) ⟨21762, by rfl⟩ : syracuseStep 3714133 = 43525) (by norm_num)
theorem B1256537 : Blo 976593 1256537 := bbase (se 2 (by rfl) ⟨471201, by rfl⟩ : syracuseStep 1256537 = 942403) (by norm_num)
theorem B4172917 : Blo 976593 4172917 := bbase (se 5 (by rfl) ⟨195605, by rfl⟩ : syracuseStep 4172917 = 391211) (by norm_num)
theorem B4172933 : Blo 976593 4172933 := bbase (se 4 (by rfl) ⟨391212, by rfl⟩ : syracuseStep 4172933 = 782425) (by norm_num)
theorem B1649821 : Blo 976593 1649821 := bbase (se 3 (by rfl) ⟨309341, by rfl⟩ : syracuseStep 1649821 = 618683) (by norm_num)
theorem B1649909 : Blo 976593 1649909 := bbase (se 5 (by rfl) ⟨77339, by rfl⟩ : syracuseStep 1649909 = 154679) (by norm_num)
theorem B10595605 : Blo 976593 10595605 := bbase (se 6 (by rfl) ⟨248334, by rfl⟩ : syracuseStep 10595605 = 496669) (by norm_num)
theorem B1650037 : Blo 976593 1650037 := bbase (se 5 (by rfl) ⟨77345, by rfl⟩ : syracuseStep 1650037 = 154691) (by norm_num)
theorem B3714437 : Blo 976593 3714437 := bbase (se 4 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 3714437 = 696457) (by norm_num)
theorem B1650125 : Blo 976593 1650125 := bbase (se 3 (by rfl) ⟨309398, by rfl⟩ : syracuseStep 1650125 = 618797) (by norm_num)
theorem B6696469 : Blo 976593 6696469 := bbase (se 6 (by rfl) ⟨156948, by rfl⟩ : syracuseStep 6696469 = 313897) (by norm_num)
theorem B1650253 : Blo 976593 1650253 := bbase (se 3 (by rfl) ⟨309422, by rfl⟩ : syracuseStep 1650253 = 618845) (by norm_num)
theorem B1650341 : Blo 976593 1650341 := bbase (se 4 (by rfl) ⟨154719, by rfl⟩ : syracuseStep 1650341 = 309439) (by norm_num)
theorem B1191677 : Blo 976593 1191677 := bbase (se 3 (by rfl) ⟨223439, by rfl⟩ : syracuseStep 1191677 = 446879) (by norm_num)
theorem B1650469 : Blo 976593 1650469 := bbase (se 4 (by rfl) ⟨154731, by rfl⟩ : syracuseStep 1650469 = 309463) (by norm_num)
theorem B1650557 : Blo 976593 1650557 := bbase (se 3 (by rfl) ⟨309479, by rfl⟩ : syracuseStep 1650557 = 618959) (by norm_num)
theorem B1650685 : Blo 976593 1650685 := bbase (se 3 (by rfl) ⟨309503, by rfl⟩ : syracuseStep 1650685 = 619007) (by norm_num)
theorem B10563605 : Blo 976593 10563605 := bbase (se 6 (by rfl) ⟨247584, by rfl⟩ : syracuseStep 10563605 = 495169) (by norm_num)
theorem B4960277 : Blo 976593 4960277 := bbase (se 6 (by rfl) ⟨116256, by rfl⟩ : syracuseStep 4960277 = 232513) (by norm_num)
theorem B1650773 : Blo 976593 1650773 := bbase (se 8 (by rfl) ⟨9672, by rfl⟩ : syracuseStep 1650773 = 19345) (by norm_num)
theorem B1650901 : Blo 976593 1650901 := bbase (se 7 (by rfl) ⟨19346, by rfl⟩ : syracuseStep 1650901 = 38693) (by norm_num)
theorem B1880341 : Blo 976593 1880341 := bbase (se 6 (by rfl) ⟨44070, by rfl⟩ : syracuseStep 1880341 = 88141) (by norm_num)
theorem B1650989 : Blo 976593 1650989 := bbase (se 3 (by rfl) ⟨309560, by rfl⟩ : syracuseStep 1650989 = 619121) (by norm_num)
theorem B1651117 : Blo 976593 1651117 := bbase (se 3 (by rfl) ⟨309584, by rfl⟩ : syracuseStep 1651117 = 619169) (by norm_num)
theorem B1651205 : Blo 976593 1651205 := bbase (se 4 (by rfl) ⟨154800, by rfl⟩ : syracuseStep 1651205 = 309601) (by norm_num)
theorem B13414997 : Blo 976593 13414997 := bbase (se 8 (by rfl) ⟨78603, by rfl⟩ : syracuseStep 13414997 = 157207) (by norm_num)
theorem B1651333 : Blo 976593 1651333 := bbase (se 4 (by rfl) ⟨154812, by rfl⟩ : syracuseStep 1651333 = 309625) (by norm_num)
theorem B1651421 : Blo 976593 1651421 := bbase (se 3 (by rfl) ⟨309641, by rfl⟩ : syracuseStep 1651421 = 619283) (by norm_num)
theorem B1651549 : Blo 976593 1651549 := bbase (se 3 (by rfl) ⟨309665, by rfl⟩ : syracuseStep 1651549 = 619331) (by norm_num)
theorem B1651637 : Blo 976593 1651637 := bbase (se 5 (by rfl) ⟨77420, by rfl⟩ : syracuseStep 1651637 = 154841) (by norm_num)
theorem B1192925 : Blo 976593 1192925 := bbase (se 3 (by rfl) ⟨223673, by rfl⟩ : syracuseStep 1192925 = 447347) (by norm_num)
theorem B1651765 : Blo 976593 1651765 := bbase (se 5 (by rfl) ⟨77426, by rfl⟩ : syracuseStep 1651765 = 154853) (by norm_num)
theorem B1487965 : Blo 976593 1487965 := bbase (se 3 (by rfl) ⟨278993, by rfl⟩ : syracuseStep 1487965 = 557987) (by norm_num)
theorem B1651853 : Blo 976593 1651853 := bbase (se 3 (by rfl) ⟨309722, by rfl⟩ : syracuseStep 1651853 = 619445) (by norm_num)
theorem B1193197 : Blo 976593 1193197 := bbase (se 3 (by rfl) ⟨223724, by rfl⟩ : syracuseStep 1193197 = 447449) (by norm_num)
theorem B1651981 : Blo 976593 1651981 := bbase (se 3 (by rfl) ⟨309746, by rfl⟩ : syracuseStep 1651981 = 619493) (by norm_num)
theorem B4961573 : Blo 976593 4961573 := bbase (se 4 (by rfl) ⟨465147, by rfl⟩ : syracuseStep 4961573 = 930295) (by norm_num)
theorem B4175189 : Blo 976593 4175189 := bbase (se 13 (by rfl) ⟨764, by rfl⟩ : syracuseStep 4175189 = 1529) (by norm_num)
theorem B1652069 : Blo 976593 1652069 := bbase (se 4 (by rfl) ⟨154881, by rfl⟩ : syracuseStep 1652069 = 309763) (by norm_num)
theorem B3716549 : Blo 976593 3716549 := bbase (se 4 (by rfl) ⟨348426, by rfl⟩ : syracuseStep 3716549 = 696853) (by norm_num)
theorem B1652197 : Blo 976593 1652197 := bbase (se 4 (by rfl) ⟨154893, by rfl⟩ : syracuseStep 1652197 = 309787) (by norm_num)
theorem B1652285 : Blo 976593 1652285 := bbase (se 3 (by rfl) ⟨309803, by rfl⟩ : syracuseStep 1652285 = 619607) (by norm_num)
theorem B1652413 : Blo 976593 1652413 := bbase (se 3 (by rfl) ⟨309827, by rfl⟩ : syracuseStep 1652413 = 619655) (by norm_num)
theorem B11155157 : Blo 976593 11155157 := bbase (se 7 (by rfl) ⟨130724, by rfl⟩ : syracuseStep 11155157 = 261449) (by norm_num)
theorem B1324765 : Blo 976593 1324765 := bbase (se 3 (by rfl) ⟨248393, by rfl⟩ : syracuseStep 1324765 = 496787) (by norm_num)
theorem B3716837 : Blo 976593 3716837 := bbase (se 4 (by rfl) ⟨348453, by rfl⟩ : syracuseStep 3716837 = 696907) (by norm_num)
theorem B1652501 : Blo 976593 1652501 := bbase (se 6 (by rfl) ⟨38730, by rfl⟩ : syracuseStep 1652501 = 77461) (by norm_num)
theorem B1652629 : Blo 976593 1652629 := bbase (se 6 (by rfl) ⟨38733, by rfl⟩ : syracuseStep 1652629 = 77467) (by norm_num)
theorem B4700069 : Blo 976593 4700069 := bbase (se 4 (by rfl) ⟨440631, by rfl⟩ : syracuseStep 4700069 = 881263) (by norm_num)
theorem B2013125 : Blo 976593 2013125 := bbase (se 4 (by rfl) ⟨188730, by rfl⟩ : syracuseStep 2013125 = 377461) (by norm_num)
theorem B1652717 : Blo 976593 1652717 := bbase (se 3 (by rfl) ⟨309884, by rfl⟩ : syracuseStep 1652717 = 619769) (by norm_num)
theorem B1390613 : Blo 976593 1390613 := bbase (se 6 (by rfl) ⟨32592, by rfl⟩ : syracuseStep 1390613 = 65185) (by norm_num)
theorem B2472029 : Blo 976593 2472029 := bbase (se 3 (by rfl) ⟨463505, by rfl⟩ : syracuseStep 2472029 = 927011) (by norm_num)
theorem B1652845 : Blo 976593 1652845 := bbase (se 3 (by rfl) ⟨309908, by rfl⟩ : syracuseStep 1652845 = 619817) (by norm_num)
theorem B1652933 : Blo 976593 1652933 := bbase (se 4 (by rfl) ⟨154962, by rfl⟩ : syracuseStep 1652933 = 309925) (by norm_num)
theorem B2472221 : Blo 976593 2472221 := bbase (se 3 (by rfl) ⟨463541, by rfl⟩ : syracuseStep 2472221 = 927083) (by norm_num)
theorem B1653061 : Blo 976593 1653061 := bbase (se 4 (by rfl) ⟨154974, by rfl⟩ : syracuseStep 1653061 = 309949) (by norm_num)
theorem B188627285 : Blo 976593 188627285 := bbase (se 10 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 188627285 = 552619) (by norm_num)
theorem B1653149 : Blo 976593 1653149 := bbase (se 3 (by rfl) ⟨309965, by rfl⟩ : syracuseStep 1653149 = 619931) (by norm_num)
theorem B3521029 : Blo 976593 3521029 := bbase (se 4 (by rfl) ⟨330096, by rfl⟩ : syracuseStep 3521029 = 660193) (by norm_num)
theorem B1653277 : Blo 976593 1653277 := bbase (se 3 (by rfl) ⟨309989, by rfl⟩ : syracuseStep 1653277 = 619979) (by norm_num)
theorem B4962869 : Blo 976593 4962869 := bbase (se 5 (by rfl) ⟨232634, by rfl⟩ : syracuseStep 4962869 = 465269) (by norm_num)
theorem B1784413 : Blo 976593 1784413 := bbase (se 3 (by rfl) ⟨334577, by rfl⟩ : syracuseStep 1784413 = 669155) (by norm_num)
theorem B2472565 : Blo 976593 2472565 := bbase (se 5 (by rfl) ⟨115901, by rfl⟩ : syracuseStep 2472565 = 231803) (by norm_num)
theorem B1653365 : Blo 976593 1653365 := bbase (se 5 (by rfl) ⟨77501, by rfl⟩ : syracuseStep 1653365 = 155003) (by norm_num)
theorem B3521173 : Blo 976593 3521173 := bbase (se 6 (by rfl) ⟨82527, by rfl⟩ : syracuseStep 3521173 = 165055) (by norm_num)
theorem B2472677 : Blo 976593 2472677 := bbase (se 4 (by rfl) ⟨231813, by rfl⟩ : syracuseStep 2472677 = 463627) (by norm_num)
theorem B1653493 : Blo 976593 1653493 := bbase (se 5 (by rfl) ⟨77507, by rfl⟩ : syracuseStep 1653493 = 155015) (by norm_num)
theorem B1391365 : Blo 976593 1391365 := bbase (se 4 (by rfl) ⟨130440, by rfl⟩ : syracuseStep 1391365 = 260881) (by norm_num)
theorem B2013997 : Blo 976593 2013997 := bbase (se 3 (by rfl) ⟨377624, by rfl⟩ : syracuseStep 2013997 = 755249) (by norm_num)
theorem B1653581 : Blo 976593 1653581 := bbase (se 3 (by rfl) ⟨310046, by rfl⟩ : syracuseStep 1653581 = 620093) (by norm_num)
theorem B3718021 : Blo 976593 3718021 := bbase (se 4 (by rfl) ⟨348564, by rfl⟩ : syracuseStep 3718021 = 697129) (by norm_num)
theorem B2472869 : Blo 976593 2472869 := bbase (se 4 (by rfl) ⟨231831, by rfl⟩ : syracuseStep 2472869 = 463663) (by norm_num)
theorem B1653709 : Blo 976593 1653709 := bbase (se 3 (by rfl) ⟨310070, by rfl⟩ : syracuseStep 1653709 = 620141) (by norm_num)
theorem B1653797 : Blo 976593 1653797 := bbase (se 4 (by rfl) ⟨155043, by rfl⟩ : syracuseStep 1653797 = 310087) (by norm_num)
theorem B1653925 : Blo 976593 1653925 := bbase (se 4 (by rfl) ⟨155055, by rfl⟩ : syracuseStep 1653925 = 310111) (by norm_num)
theorem B3718325 : Blo 976593 3718325 := bbase (se 5 (by rfl) ⟨174296, by rfl⟩ : syracuseStep 3718325 = 348593) (by norm_num)
theorem B2473213 : Blo 976593 2473213 := bbase (se 3 (by rfl) ⟨463727, by rfl⟩ : syracuseStep 2473213 = 927455) (by norm_num)
theorem B1654013 : Blo 976593 1654013 := bbase (se 3 (by rfl) ⟨310127, by rfl⟩ : syracuseStep 1654013 = 620255) (by norm_num)
theorem B2473325 : Blo 976593 2473325 := bbase (se 3 (by rfl) ⟨463748, by rfl⟩ : syracuseStep 2473325 = 927497) (by norm_num)
theorem B6274421 : Blo 976593 6274421 := bbase (se 5 (by rfl) ⟨294113, by rfl⟩ : syracuseStep 6274421 = 588227) (by norm_num)
theorem B1654141 : Blo 976593 1654141 := bbase (se 3 (by rfl) ⟨310151, by rfl⟩ : syracuseStep 1654141 = 620303) (by norm_num)
theorem B1981829 : Blo 976593 1981829 := bbase (se 4 (by rfl) ⟨185796, by rfl⟩ : syracuseStep 1981829 = 371593) (by norm_num)
theorem B1654229 : Blo 976593 1654229 := bbase (se 7 (by rfl) ⟨19385, by rfl⟩ : syracuseStep 1654229 = 38771) (by norm_num)
theorem B4701701 : Blo 976593 4701701 := bbase (se 4 (by rfl) ⟨440784, by rfl⟩ : syracuseStep 4701701 = 881569) (by norm_num)
theorem B1392157 : Blo 976593 1392157 := bbase (se 3 (by rfl) ⟨261029, by rfl⟩ : syracuseStep 1392157 = 522059) (by norm_num)
theorem B2473517 : Blo 976593 2473517 := bbase (se 3 (by rfl) ⟨463784, by rfl⟩ : syracuseStep 2473517 = 927569) (by norm_num)
theorem B1654357 : Blo 976593 1654357 := bbase (se 8 (by rfl) ⟨9693, by rfl⟩ : syracuseStep 1654357 = 19387) (by norm_num)
theorem B1654445 : Blo 976593 1654445 := bbase (se 3 (by rfl) ⟨310208, by rfl⟩ : syracuseStep 1654445 = 620417) (by norm_num)
theorem B1654573 : Blo 976593 1654573 := bbase (se 3 (by rfl) ⟨310232, by rfl⟩ : syracuseStep 1654573 = 620465) (by norm_num)
theorem B4964165 : Blo 976593 4964165 := bbase (se 4 (by rfl) ⟨465390, by rfl⟩ : syracuseStep 4964165 = 930781) (by norm_num)
theorem B1392493 : Blo 976593 1392493 := bbase (se 3 (by rfl) ⟨261092, by rfl⟩ : syracuseStep 1392493 = 522185) (by norm_num)
theorem B2473861 : Blo 976593 2473861 := bbase (se 4 (by rfl) ⟨231924, by rfl⟩ : syracuseStep 2473861 = 463849) (by norm_num)
theorem B1654661 : Blo 976593 1654661 := bbase (se 4 (by rfl) ⟨155124, by rfl⟩ : syracuseStep 1654661 = 310249) (by norm_num)
theorem B3129317 : Blo 976593 3129317 := bbase (se 4 (by rfl) ⟨293373, by rfl⟩ : syracuseStep 3129317 = 586747) (by norm_num)
theorem B2473973 : Blo 976593 2473973 := bbase (se 5 (by rfl) ⟨115967, by rfl⟩ : syracuseStep 2473973 = 231935) (by norm_num)
theorem B1392709 : Blo 976593 1392709 := bbase (se 4 (by rfl) ⟨130566, by rfl⟩ : syracuseStep 1392709 = 261133) (by norm_num)
theorem B2474165 : Blo 976593 2474165 := bbase (se 5 (by rfl) ⟨115976, by rfl⟩ : syracuseStep 2474165 = 231953) (by norm_num)
theorem B1393085 : Blo 976593 1393085 := bbase (se 3 (by rfl) ⟨261203, by rfl⟩ : syracuseStep 1393085 = 522407) (by norm_num)
theorem B2474509 : Blo 976593 2474509 := bbase (se 3 (by rfl) ⟨463970, by rfl⟩ : syracuseStep 2474509 = 927941) (by norm_num)
theorem B1983037 : Blo 976593 1983037 := bbase (se 3 (by rfl) ⟨371819, by rfl⟩ : syracuseStep 1983037 = 743639) (by norm_num)
theorem B5292661 : Blo 976593 5292661 := bbase (se 5 (by rfl) ⟨248093, by rfl⟩ : syracuseStep 5292661 = 496187) (by norm_num)
theorem B2474621 : Blo 976593 2474621 := bbase (se 3 (by rfl) ⟨463991, by rfl⟩ : syracuseStep 2474621 = 927983) (by norm_num)
theorem B1983101 : Blo 976593 1983101 := bbase (se 3 (by rfl) ⟨371831, by rfl⟩ : syracuseStep 1983101 = 743663) (by norm_num)
theorem B7422677 : Blo 976593 7422677 := bbase (se 7 (by rfl) ⟨86984, by rfl⟩ : syracuseStep 7422677 = 173969) (by norm_num)
theorem B2474813 : Blo 976593 2474813 := bbase (se 3 (by rfl) ⟨464027, by rfl⟩ : syracuseStep 2474813 = 928055) (by norm_num)
theorem B1098697 : Blo 976593 1098697 := bbase (se 2 (by rfl) ⟨412011, by rfl⟩ : syracuseStep 1098697 = 824023) (by norm_num)
theorem B1098733 : Blo 976593 1098733 := bbase (se 3 (by rfl) ⟨206012, by rfl⟩ : syracuseStep 1098733 = 412025) (by norm_num)
theorem B1098769 : Blo 976593 1098769 := bbase (se 2 (by rfl) ⟨412038, by rfl⟩ : syracuseStep 1098769 = 824077) (by norm_num)
theorem B1098805 : Blo 976593 1098805 := bbase (se 5 (by rfl) ⟨51506, by rfl⟩ : syracuseStep 1098805 = 103013) (by norm_num)
theorem B1098841 : Blo 976593 1098841 := bbase (se 2 (by rfl) ⟨412065, by rfl⟩ : syracuseStep 1098841 = 824131) (by norm_num)
theorem B1098877 : Blo 976593 1098877 := bbase (se 3 (by rfl) ⟨206039, by rfl⟩ : syracuseStep 1098877 = 412079) (by norm_num)
theorem B1983629 : Blo 976593 1983629 := bbase (se 3 (by rfl) ⟨371930, by rfl⟩ : syracuseStep 1983629 = 743861) (by norm_num)
theorem B2475157 : Blo 976593 2475157 := bbase (se 6 (by rfl) ⟨58011, by rfl⟩ : syracuseStep 2475157 = 116023) (by norm_num)
theorem B1098913 : Blo 976593 1098913 := bbase (se 2 (by rfl) ⟨412092, by rfl⟩ : syracuseStep 1098913 = 824185) (by norm_num)
theorem B1098949 : Blo 976593 1098949 := bbase (se 4 (by rfl) ⟨103026, by rfl⟩ : syracuseStep 1098949 = 206053) (by norm_num)
theorem B1098985 : Blo 976593 1098985 := bbase (se 2 (by rfl) ⟨412119, by rfl⟩ : syracuseStep 1098985 = 824239) (by norm_num)
theorem B3720437 : Blo 976593 3720437 := bbase (se 5 (by rfl) ⟨174395, by rfl⟩ : syracuseStep 3720437 = 348791) (by norm_num)
theorem B2475269 : Blo 976593 2475269 := bbase (se 4 (by rfl) ⟨232056, by rfl⟩ : syracuseStep 2475269 = 464113) (by norm_num)
theorem B1099021 : Blo 976593 1099021 := bbase (se 3 (by rfl) ⟨206066, by rfl⟩ : syracuseStep 1099021 = 412133) (by norm_num)
theorem B4179221 : Blo 976593 4179221 := bbase (se 6 (by rfl) ⟨97950, by rfl⟩ : syracuseStep 4179221 = 195901) (by norm_num)
theorem B1099057 : Blo 976593 1099057 := bbase (se 2 (by rfl) ⟨412146, by rfl⟩ : syracuseStep 1099057 = 824293) (by norm_num)
theorem B1099093 : Blo 976593 1099093 := bbase (se 12 (by rfl) ⟨402, by rfl⟩ : syracuseStep 1099093 = 805) (by norm_num)
theorem B1099129 : Blo 976593 1099129 := bbase (se 2 (by rfl) ⟨412173, by rfl⟩ : syracuseStep 1099129 = 824347) (by norm_num)
theorem B1099165 : Blo 976593 1099165 := bbase (se 3 (by rfl) ⟨206093, by rfl⟩ : syracuseStep 1099165 = 412187) (by norm_num)
theorem B1099201 : Blo 976593 1099201 := bbase (se 2 (by rfl) ⟨412200, by rfl⟩ : syracuseStep 1099201 = 824401) (by norm_num)
theorem B2475461 : Blo 976593 2475461 := bbase (se 4 (by rfl) ⟨232074, by rfl⟩ : syracuseStep 2475461 = 464149) (by norm_num)
theorem B1099237 : Blo 976593 1099237 := bbase (se 4 (by rfl) ⟨103053, by rfl⟩ : syracuseStep 1099237 = 206107) (by norm_num)
theorem B1099273 : Blo 976593 1099273 := bbase (se 2 (by rfl) ⟨412227, by rfl⟩ : syracuseStep 1099273 = 824455) (by norm_num)
theorem B3720725 : Blo 976593 3720725 := bbase (se 6 (by rfl) ⟨87204, by rfl⟩ : syracuseStep 3720725 = 174409) (by norm_num)
theorem B1099309 : Blo 976593 1099309 := bbase (se 3 (by rfl) ⟨206120, by rfl⟩ : syracuseStep 1099309 = 412241) (by norm_num)
theorem B1099345 : Blo 976593 1099345 := bbase (se 2 (by rfl) ⟨412254, by rfl⟩ : syracuseStep 1099345 = 824509) (by norm_num)
theorem B1099381 : Blo 976593 1099381 := bbase (se 5 (by rfl) ⟨51533, by rfl⟩ : syracuseStep 1099381 = 103067) (by norm_num)
theorem B1099417 : Blo 976593 1099417 := bbase (se 2 (by rfl) ⟨412281, by rfl⟩ : syracuseStep 1099417 = 824563) (by norm_num)
theorem B1885853 : Blo 976593 1885853 := bbase (se 3 (by rfl) ⟨353597, by rfl⟩ : syracuseStep 1885853 = 707195) (by norm_num)
theorem B1099453 : Blo 976593 1099453 := bbase (se 3 (by rfl) ⟨206147, by rfl⟩ : syracuseStep 1099453 = 412295) (by norm_num)
theorem B1099489 : Blo 976593 1099489 := bbase (se 2 (by rfl) ⟨412308, by rfl⟩ : syracuseStep 1099489 = 824617) (by norm_num)
theorem B1099525 : Blo 976593 1099525 := bbase (se 4 (by rfl) ⟨103080, by rfl⟩ : syracuseStep 1099525 = 206161) (by norm_num)
theorem B1132309 : Blo 976593 1132309 := bbase (se 6 (by rfl) ⟨26538, by rfl⟩ : syracuseStep 1132309 = 53077) (by norm_num)
theorem B2475805 : Blo 976593 2475805 := bbase (se 3 (by rfl) ⟨464213, by rfl⟩ : syracuseStep 2475805 = 928427) (by norm_num)
theorem B1099561 : Blo 976593 1099561 := bbase (se 2 (by rfl) ⟨412335, by rfl⟩ : syracuseStep 1099561 = 824671) (by norm_num)
theorem B1099597 : Blo 976593 1099597 := bbase (se 3 (by rfl) ⟨206174, by rfl⟩ : syracuseStep 1099597 = 412349) (by norm_num)
theorem B1394509 : Blo 976593 1394509 := bbase (se 3 (by rfl) ⟨261470, by rfl⟩ : syracuseStep 1394509 = 522941) (by norm_num)
theorem B1099633 : Blo 976593 1099633 := bbase (se 2 (by rfl) ⟨412362, by rfl⟩ : syracuseStep 1099633 = 824725) (by norm_num)
theorem B2475917 : Blo 976593 2475917 := bbase (se 3 (by rfl) ⟨464234, by rfl⟩ : syracuseStep 2475917 = 928469) (by norm_num)
theorem B1099669 : Blo 976593 1099669 := bbase (se 6 (by rfl) ⟨25773, by rfl⟩ : syracuseStep 1099669 = 51547) (by norm_num)
theorem B1099705 : Blo 976593 1099705 := bbase (se 2 (by rfl) ⟨412389, by rfl⟩ : syracuseStep 1099705 = 824779) (by norm_num)
theorem B1099741 : Blo 976593 1099741 := bbase (se 3 (by rfl) ⟨206201, by rfl⟩ : syracuseStep 1099741 = 412403) (by norm_num)
theorem B1099777 : Blo 976593 1099777 := bbase (se 2 (by rfl) ⟨412416, by rfl⟩ : syracuseStep 1099777 = 824833) (by norm_num)
theorem B1099813 : Blo 976593 1099813 := bbase (se 4 (by rfl) ⟨103107, by rfl⟩ : syracuseStep 1099813 = 206215) (by norm_num)
theorem B1099849 : Blo 976593 1099849 := bbase (se 2 (by rfl) ⟨412443, by rfl⟩ : syracuseStep 1099849 = 824887) (by norm_num)
theorem B2476109 : Blo 976593 2476109 := bbase (se 3 (by rfl) ⟨464270, by rfl⟩ : syracuseStep 2476109 = 928541) (by norm_num)
theorem B1099885 : Blo 976593 1099885 := bbase (se 3 (by rfl) ⟨206228, by rfl⟩ : syracuseStep 1099885 = 412457) (by norm_num)
theorem B1099921 : Blo 976593 1099921 := bbase (se 2 (by rfl) ⟨412470, by rfl⟩ : syracuseStep 1099921 = 824941) (by norm_num)
theorem B1099957 : Blo 976593 1099957 := bbase (se 5 (by rfl) ⟨51560, by rfl⟩ : syracuseStep 1099957 = 103121) (by norm_num)
theorem B8472757 : Blo 976593 8472757 := bbase (se 5 (by rfl) ⟨397160, by rfl⟩ : syracuseStep 8472757 = 794321) (by norm_num)
theorem B1099993 : Blo 976593 1099993 := bbase (se 2 (by rfl) ⟨412497, by rfl⟩ : syracuseStep 1099993 = 824995) (by norm_num)
theorem B1100029 : Blo 976593 1100029 := bbase (se 3 (by rfl) ⟨206255, by rfl⟩ : syracuseStep 1100029 = 412511) (by norm_num)
theorem B1100065 : Blo 976593 1100065 := bbase (se 2 (by rfl) ⟨412524, by rfl⟩ : syracuseStep 1100065 = 825049) (by norm_num)
theorem B2509093 : Blo 976593 2509093 := bbase (se 4 (by rfl) ⟨235227, by rfl⟩ : syracuseStep 2509093 = 470455) (by norm_num)
theorem B1100101 : Blo 976593 1100101 := bbase (se 4 (by rfl) ⟨103134, by rfl⟩ : syracuseStep 1100101 = 206269) (by norm_num)
theorem B1100137 : Blo 976593 1100137 := bbase (se 2 (by rfl) ⟨412551, by rfl⟩ : syracuseStep 1100137 = 825103) (by norm_num)
theorem B1100173 : Blo 976593 1100173 := bbase (se 3 (by rfl) ⟨206282, by rfl⟩ : syracuseStep 1100173 = 412565) (by norm_num)
theorem B1395101 : Blo 976593 1395101 := bbase (se 3 (by rfl) ⟨261581, by rfl⟩ : syracuseStep 1395101 = 523163) (by norm_num)
theorem B2476453 : Blo 976593 2476453 := bbase (se 4 (by rfl) ⟨232167, by rfl⟩ : syracuseStep 2476453 = 464335) (by norm_num)
theorem B1100209 : Blo 976593 1100209 := bbase (se 2 (by rfl) ⟨412578, by rfl⟩ : syracuseStep 1100209 = 825157) (by norm_num)
theorem B1886653 : Blo 976593 1886653 := bbase (se 3 (by rfl) ⟨353747, by rfl⟩ : syracuseStep 1886653 = 707495) (by norm_num)
theorem B1100245 : Blo 976593 1100245 := bbase (se 7 (by rfl) ⟨12893, by rfl⟩ : syracuseStep 1100245 = 25787) (by norm_num)
theorem B1395181 : Blo 976593 1395181 := bbase (se 3 (by rfl) ⟨261596, by rfl⟩ : syracuseStep 1395181 = 523193) (by norm_num)
theorem B1100281 : Blo 976593 1100281 := bbase (se 2 (by rfl) ⟨412605, by rfl⟩ : syracuseStep 1100281 = 825211) (by norm_num)
theorem B2476565 : Blo 976593 2476565 := bbase (se 6 (by rfl) ⟨58044, by rfl⟩ : syracuseStep 2476565 = 116089) (by norm_num)
theorem B1100317 : Blo 976593 1100317 := bbase (se 3 (by rfl) ⟨206309, by rfl⟩ : syracuseStep 1100317 = 412619) (by norm_num)
theorem B2509373 : Blo 976593 2509373 := bbase (se 3 (by rfl) ⟨470507, by rfl⟩ : syracuseStep 2509373 = 941015) (by norm_num)
theorem B1100353 : Blo 976593 1100353 := bbase (se 2 (by rfl) ⟨412632, by rfl⟩ : syracuseStep 1100353 = 825265) (by norm_num)
theorem B1854029 : Blo 976593 1854029 := bbase (se 3 (by rfl) ⟨347630, by rfl⟩ : syracuseStep 1854029 = 695261) (by norm_num)
theorem B1100389 : Blo 976593 1100389 := bbase (se 4 (by rfl) ⟨103161, by rfl⟩ : syracuseStep 1100389 = 206323) (by norm_num)
theorem B1395301 : Blo 976593 1395301 := bbase (se 4 (by rfl) ⟨130809, by rfl⟩ : syracuseStep 1395301 = 261619) (by norm_num)
theorem B1100425 : Blo 976593 1100425 := bbase (se 2 (by rfl) ⟨412659, by rfl⟩ : syracuseStep 1100425 = 825319) (by norm_num)
theorem B1100461 : Blo 976593 1100461 := bbase (se 3 (by rfl) ⟨206336, by rfl⟩ : syracuseStep 1100461 = 412673) (by norm_num)
theorem B3721909 : Blo 976593 3721909 := bbase (se 5 (by rfl) ⟨174464, by rfl⟩ : syracuseStep 3721909 = 348929) (by norm_num)
theorem B1395397 : Blo 976593 1395397 := bbase (se 4 (by rfl) ⟨130818, by rfl⟩ : syracuseStep 1395397 = 261637) (by norm_num)
theorem B1100497 : Blo 976593 1100497 := bbase (se 2 (by rfl) ⟨412686, by rfl⟩ : syracuseStep 1100497 = 825373) (by norm_num)
theorem B2476757 : Blo 976593 2476757 := bbase (se 7 (by rfl) ⟨29024, by rfl⟩ : syracuseStep 2476757 = 58049) (by norm_num)
theorem B1854181 : Blo 976593 1854181 := bbase (se 4 (by rfl) ⟨173829, by rfl⟩ : syracuseStep 1854181 = 347659) (by norm_num)
theorem B1100533 : Blo 976593 1100533 := bbase (se 5 (by rfl) ⟨51587, by rfl⟩ : syracuseStep 1100533 = 103175) (by norm_num)
theorem B1100569 : Blo 976593 1100569 := bbase (se 2 (by rfl) ⟨412713, by rfl⟩ : syracuseStep 1100569 = 825427) (by norm_num)
theorem B1100605 : Blo 976593 1100605 := bbase (se 3 (by rfl) ⟨206363, by rfl⟩ : syracuseStep 1100605 = 412727) (by norm_num)
theorem B7064405 : Blo 976593 7064405 := bbase (se 9 (by rfl) ⟨20696, by rfl⟩ : syracuseStep 7064405 = 41393) (by norm_num)
theorem B9423701 : Blo 976593 9423701 := bbase (se 9 (by rfl) ⟨27608, by rfl⟩ : syracuseStep 9423701 = 55217) (by norm_num)
theorem B1100641 : Blo 976593 1100641 := bbase (se 2 (by rfl) ⟨412740, by rfl⟩ : syracuseStep 1100641 = 825481) (by norm_num)
theorem B1100677 : Blo 976593 1100677 := bbase (se 4 (by rfl) ⟨103188, by rfl⟩ : syracuseStep 1100677 = 206377) (by norm_num)
theorem B1100713 : Blo 976593 1100713 := bbase (se 2 (by rfl) ⟨412767, by rfl⟩ : syracuseStep 1100713 = 825535) (by norm_num)
theorem B1100749 : Blo 976593 1100749 := bbase (se 3 (by rfl) ⟨206390, by rfl⟩ : syracuseStep 1100749 = 412781) (by norm_num)
theorem B3296213 : Blo 976593 3296213 := bbase (se 7 (by rfl) ⟨38627, by rfl⟩ : syracuseStep 3296213 = 77255) (by norm_num)
theorem B1985509 : Blo 976593 1985509 := bbase (se 4 (by rfl) ⟨186141, by rfl⟩ : syracuseStep 1985509 = 372283) (by norm_num)
theorem B3722213 : Blo 976593 3722213 := bbase (se 4 (by rfl) ⟨348957, by rfl⟩ : syracuseStep 3722213 = 697915) (by norm_num)
theorem B2116589 : Blo 976593 2116589 := bbase (se 3 (by rfl) ⟨396860, by rfl⟩ : syracuseStep 2116589 = 793721) (by norm_num)
theorem B1100785 : Blo 976593 1100785 := bbase (se 2 (by rfl) ⟨412794, by rfl⟩ : syracuseStep 1100785 = 825589) (by norm_num)
theorem B4180997 : Blo 976593 4180997 := bbase (se 4 (by rfl) ⟨391968, by rfl⟩ : syracuseStep 4180997 = 783937) (by norm_num)
theorem B1854485 : Blo 976593 1854485 := bbase (se 6 (by rfl) ⟨43464, by rfl⟩ : syracuseStep 1854485 = 86929) (by norm_num)
theorem B1100821 : Blo 976593 1100821 := bbase (se 6 (by rfl) ⟨25800, by rfl⟩ : syracuseStep 1100821 = 51601) (by norm_num)
theorem B2477101 : Blo 976593 2477101 := bbase (se 3 (by rfl) ⟨464456, by rfl⟩ : syracuseStep 2477101 = 928913) (by norm_num)
theorem B1100857 : Blo 976593 1100857 := bbase (se 2 (by rfl) ⟨412821, by rfl⟩ : syracuseStep 1100857 = 825643) (by norm_num)
theorem B1100893 : Blo 976593 1100893 := bbase (se 3 (by rfl) ⟨206417, by rfl⟩ : syracuseStep 1100893 = 412835) (by norm_num)
theorem B1100929 : Blo 976593 1100929 := bbase (se 2 (by rfl) ⟨412848, by rfl⟩ : syracuseStep 1100929 = 825697) (by norm_num)
theorem B2477213 : Blo 976593 2477213 := bbase (se 3 (by rfl) ⟨464477, by rfl⟩ : syracuseStep 2477213 = 928955) (by norm_num)
theorem B1100965 : Blo 976593 1100965 := bbase (se 4 (by rfl) ⟨103215, by rfl⟩ : syracuseStep 1100965 = 206431) (by norm_num)
theorem B1395893 : Blo 976593 1395893 := bbase (se 5 (by rfl) ⟨65432, by rfl⟩ : syracuseStep 1395893 = 130865) (by norm_num)
theorem B1101001 : Blo 976593 1101001 := bbase (se 2 (by rfl) ⟨412875, by rfl⟩ : syracuseStep 1101001 = 825751) (by norm_num)
theorem B1101037 : Blo 976593 1101037 := bbase (se 3 (by rfl) ⟨206444, by rfl⟩ : syracuseStep 1101037 = 412889) (by norm_num)
theorem B1101073 : Blo 976593 1101073 := bbase (se 2 (by rfl) ⟨412902, by rfl⟩ : syracuseStep 1101073 = 825805) (by norm_num)
theorem B1101109 : Blo 976593 1101109 := bbase (se 5 (by rfl) ⟨51614, by rfl⟩ : syracuseStep 1101109 = 103229) (by norm_num)
theorem B1101145 : Blo 976593 1101145 := bbase (se 2 (by rfl) ⟨412929, by rfl⟩ : syracuseStep 1101145 = 825859) (by norm_num)
theorem B2477405 : Blo 976593 2477405 := bbase (se 3 (by rfl) ⟨464513, by rfl⟩ : syracuseStep 2477405 = 929027) (by norm_num)
theorem B1101181 : Blo 976593 1101181 := bbase (se 3 (by rfl) ⟨206471, by rfl⟩ : syracuseStep 1101181 = 412943) (by norm_num)
theorem B3296645 : Blo 976593 3296645 := bbase (se 4 (by rfl) ⟨309060, by rfl⟩ : syracuseStep 3296645 = 618121) (by norm_num)
theorem B1101217 : Blo 976593 1101217 := bbase (se 2 (by rfl) ⟨412956, by rfl⟩ : syracuseStep 1101217 = 825913) (by norm_num)
theorem B1101253 : Blo 976593 1101253 := bbase (se 4 (by rfl) ⟨103242, by rfl⟩ : syracuseStep 1101253 = 206485) (by norm_num)
theorem B1101289 : Blo 976593 1101289 := bbase (se 2 (by rfl) ⟨412983, by rfl⟩ : syracuseStep 1101289 = 825967) (by norm_num)
theorem B1101325 : Blo 976593 1101325 := bbase (se 3 (by rfl) ⟨206498, by rfl⟩ : syracuseStep 1101325 = 412997) (by norm_num)
theorem B1101361 : Blo 976593 1101361 := bbase (se 2 (by rfl) ⟨413010, by rfl⟩ : syracuseStep 1101361 = 826021) (by norm_num)
theorem B1986125 : Blo 976593 1986125 := bbase (se 3 (by rfl) ⟨372398, by rfl⟩ : syracuseStep 1986125 = 744797) (by norm_num)
theorem B1101397 : Blo 976593 1101397 := bbase (se 8 (by rfl) ⟨6453, by rfl⟩ : syracuseStep 1101397 = 12907) (by norm_num)
theorem B1101433 : Blo 976593 1101433 := bbase (se 2 (by rfl) ⟨413037, by rfl⟩ : syracuseStep 1101433 = 826075) (by norm_num)
theorem B1101469 : Blo 976593 1101469 := bbase (se 3 (by rfl) ⟨206525, by rfl⟩ : syracuseStep 1101469 = 413051) (by norm_num)
theorem B2477749 : Blo 976593 2477749 := bbase (se 5 (by rfl) ⟨116144, by rfl⟩ : syracuseStep 2477749 = 232289) (by norm_num)
theorem B1101505 : Blo 976593 1101505 := bbase (se 2 (by rfl) ⟨413064, by rfl⟩ : syracuseStep 1101505 = 826129) (by norm_num)
theorem B1101541 : Blo 976593 1101541 := bbase (se 4 (by rfl) ⟨103269, by rfl⟩ : syracuseStep 1101541 = 206539) (by norm_num)
theorem B1855237 : Blo 976593 1855237 := bbase (se 4 (by rfl) ⟨173928, by rfl⟩ : syracuseStep 1855237 = 347857) (by norm_num)
theorem B1101577 : Blo 976593 1101577 := bbase (se 2 (by rfl) ⟨413091, by rfl⟩ : syracuseStep 1101577 = 826183) (by norm_num)
theorem B2477861 : Blo 976593 2477861 := bbase (se 4 (by rfl) ⟨232299, by rfl⟩ : syracuseStep 2477861 = 464599) (by norm_num)
theorem B1101613 : Blo 976593 1101613 := bbase (se 3 (by rfl) ⟨206552, by rfl⟩ : syracuseStep 1101613 = 413105) (by norm_num)
theorem B3297077 : Blo 976593 3297077 := bbase (se 5 (by rfl) ⟨154550, by rfl⟩ : syracuseStep 3297077 = 309101) (by norm_num)
theorem B3133237 : Blo 976593 3133237 := bbase (se 5 (by rfl) ⟨146870, by rfl⟩ : syracuseStep 3133237 = 293741) (by norm_num)
theorem B1101649 : Blo 976593 1101649 := bbase (se 2 (by rfl) ⟨413118, by rfl⟩ : syracuseStep 1101649 = 826237) (by norm_num)
theorem B2346853 : Blo 976593 2346853 := bbase (se 4 (by rfl) ⟨220017, by rfl⟩ : syracuseStep 2346853 = 440035) (by norm_num)
theorem B1101685 : Blo 976593 1101685 := bbase (se 5 (by rfl) ⟨51641, by rfl⟩ : syracuseStep 1101685 = 103283) (by norm_num)
theorem B1855381 : Blo 976593 1855381 := bbase (se 6 (by rfl) ⟨43485, by rfl⟩ : syracuseStep 1855381 = 86971) (by norm_num)
theorem B1101721 : Blo 976593 1101721 := bbase (se 2 (by rfl) ⟨413145, by rfl⟩ : syracuseStep 1101721 = 826291) (by norm_num)
theorem B4018085 : Blo 976593 4018085 := bbase (se 4 (by rfl) ⟨376695, by rfl⟩ : syracuseStep 4018085 = 753391) (by norm_num)
theorem B1101757 : Blo 976593 1101757 := bbase (se 3 (by rfl) ⟨206579, by rfl⟩ : syracuseStep 1101757 = 413159) (by norm_num)
theorem B1101793 : Blo 976593 1101793 := bbase (se 2 (by rfl) ⟨413172, by rfl⟩ : syracuseStep 1101793 = 826345) (by norm_num)
theorem B2478053 : Blo 976593 2478053 := bbase (se 4 (by rfl) ⟨232317, by rfl⟩ : syracuseStep 2478053 = 464635) (by norm_num)
theorem B4181989 : Blo 976593 4181989 := bbase (se 4 (by rfl) ⟨392061, by rfl⟩ : syracuseStep 4181989 = 784123) (by norm_num)
theorem B1101829 : Blo 976593 1101829 := bbase (se 4 (by rfl) ⟨103296, by rfl⟩ : syracuseStep 1101829 = 206593) (by norm_num)
theorem B1101865 : Blo 976593 1101865 := bbase (se 2 (by rfl) ⟨413199, by rfl⟩ : syracuseStep 1101865 = 826399) (by norm_num)
theorem B1855541 : Blo 976593 1855541 := bbase (se 5 (by rfl) ⟨86978, by rfl⟩ : syracuseStep 1855541 = 173957) (by norm_num)
theorem B3133493 : Blo 976593 3133493 := bbase (se 5 (by rfl) ⟨146882, by rfl⟩ : syracuseStep 3133493 = 293765) (by norm_num)
theorem B1101901 : Blo 976593 1101901 := bbase (se 3 (by rfl) ⟨206606, by rfl⟩ : syracuseStep 1101901 = 413213) (by norm_num)
theorem B1101937 : Blo 976593 1101937 := bbase (se 2 (by rfl) ⟨413226, by rfl⟩ : syracuseStep 1101937 = 826453) (by norm_num)
theorem B1101973 : Blo 976593 1101973 := bbase (se 6 (by rfl) ⟨25827, by rfl⟩ : syracuseStep 1101973 = 51655) (by norm_num)
theorem B1102009 : Blo 976593 1102009 := bbase (se 2 (by rfl) ⟨413253, by rfl⟩ : syracuseStep 1102009 = 826507) (by norm_num)
theorem B1855685 : Blo 976593 1855685 := bbase (se 4 (by rfl) ⟨173970, by rfl⟩ : syracuseStep 1855685 = 347941) (by norm_num)
theorem B1102045 : Blo 976593 1102045 := bbase (se 3 (by rfl) ⟨206633, by rfl⟩ : syracuseStep 1102045 = 413267) (by norm_num)
theorem B3297509 : Blo 976593 3297509 := bbase (se 4 (by rfl) ⟨309141, by rfl⟩ : syracuseStep 3297509 = 618283) (by norm_num)
theorem B2117861 : Blo 976593 2117861 := bbase (se 4 (by rfl) ⟨198549, by rfl⟩ : syracuseStep 2117861 = 397099) (by norm_num)
theorem B1102081 : Blo 976593 1102081 := bbase (se 2 (by rfl) ⟨413280, by rfl⟩ : syracuseStep 1102081 = 826561) (by norm_num)
theorem B1102117 : Blo 976593 1102117 := bbase (se 4 (by rfl) ⟨103323, by rfl⟩ : syracuseStep 1102117 = 206647) (by norm_num)
theorem B2478397 : Blo 976593 2478397 := bbase (se 3 (by rfl) ⟨464699, by rfl⟩ : syracuseStep 2478397 = 929399) (by norm_num)
theorem B1102153 : Blo 976593 1102153 := bbase (se 2 (by rfl) ⟨413307, by rfl⟩ : syracuseStep 1102153 = 826615) (by norm_num)
theorem B2347373 : Blo 976593 2347373 := bbase (se 3 (by rfl) ⟨440132, by rfl⟩ : syracuseStep 2347373 = 880265) (by norm_num)
theorem B1102189 : Blo 976593 1102189 := bbase (se 3 (by rfl) ⟨206660, by rfl⟩ : syracuseStep 1102189 = 413321) (by norm_num)
theorem B1102225 : Blo 976593 1102225 := bbase (se 2 (by rfl) ⟨413334, by rfl⟩ : syracuseStep 1102225 = 826669) (by norm_num)
theorem B2478509 : Blo 976593 2478509 := bbase (se 3 (by rfl) ⟨464720, by rfl⟩ : syracuseStep 2478509 = 929441) (by norm_num)
theorem B1102261 : Blo 976593 1102261 := bbase (se 5 (by rfl) ⟨51668, by rfl⟩ : syracuseStep 1102261 = 103337) (by norm_num)
theorem B1102297 : Blo 976593 1102297 := bbase (se 2 (by rfl) ⟨413361, by rfl⟩ : syracuseStep 1102297 = 826723) (by norm_num)
theorem B1855973 : Blo 976593 1855973 := bbase (se 4 (by rfl) ⟨173997, by rfl⟩ : syracuseStep 1855973 = 347995) (by norm_num)
theorem B1102333 : Blo 976593 1102333 := bbase (se 3 (by rfl) ⟨206687, by rfl⟩ : syracuseStep 1102333 = 413375) (by norm_num)
theorem B1102369 : Blo 976593 1102369 := bbase (se 2 (by rfl) ⟨413388, by rfl⟩ : syracuseStep 1102369 = 826777) (by norm_num)
theorem B2642501 : Blo 976593 2642501 := bbase (se 4 (by rfl) ⟨247734, by rfl⟩ : syracuseStep 2642501 = 495469) (by norm_num)
theorem B1102405 : Blo 976593 1102405 := bbase (se 4 (by rfl) ⟨103350, by rfl⟩ : syracuseStep 1102405 = 206701) (by norm_num)
theorem B1102441 : Blo 976593 1102441 := bbase (se 2 (by rfl) ⟨413415, by rfl⟩ : syracuseStep 1102441 = 826831) (by norm_num)
theorem B2478701 : Blo 976593 2478701 := bbase (se 3 (by rfl) ⟨464756, by rfl⟩ : syracuseStep 2478701 = 929513) (by norm_num)
theorem B1856125 : Blo 976593 1856125 := bbase (se 3 (by rfl) ⟨348023, by rfl⟩ : syracuseStep 1856125 = 696047) (by norm_num)
theorem B1102477 : Blo 976593 1102477 := bbase (se 3 (by rfl) ⟨206714, by rfl⟩ : syracuseStep 1102477 = 413429) (by norm_num)
theorem B3297941 : Blo 976593 3297941 := bbase (se 6 (by rfl) ⟨77295, by rfl⟩ : syracuseStep 3297941 = 154591) (by norm_num)
theorem B5952149 : Blo 976593 5952149 := bbase (se 6 (by rfl) ⟨139503, by rfl⟩ : syracuseStep 5952149 = 279007) (by norm_num)
theorem B1102513 : Blo 976593 1102513 := bbase (se 2 (by rfl) ⟨413442, by rfl⟩ : syracuseStep 1102513 = 826885) (by norm_num)
theorem B1102549 : Blo 976593 1102549 := bbase (se 7 (by rfl) ⟨12920, by rfl⟩ : syracuseStep 1102549 = 25841) (by norm_num)
theorem B2347757 : Blo 976593 2347757 := bbase (se 3 (by rfl) ⟨440204, by rfl⟩ : syracuseStep 2347757 = 880409) (by norm_num)
theorem B1102585 : Blo 976593 1102585 := bbase (se 2 (by rfl) ⟨413469, by rfl⟩ : syracuseStep 1102585 = 826939) (by norm_num)
theorem B2347805 : Blo 976593 2347805 := bbase (se 3 (by rfl) ⟨440213, by rfl⟩ : syracuseStep 2347805 = 880427) (by norm_num)
theorem B1102621 : Blo 976593 1102621 := bbase (se 3 (by rfl) ⟨206741, by rfl⟩ : syracuseStep 1102621 = 413483) (by norm_num)
theorem B2347813 : Blo 976593 2347813 := bbase (se 4 (by rfl) ⟨220107, by rfl⟩ : syracuseStep 2347813 = 440215) (by norm_num)
theorem B1102657 : Blo 976593 1102657 := bbase (se 2 (by rfl) ⟨413496, by rfl⟩ : syracuseStep 1102657 = 826993) (by norm_num)
theorem B1102693 : Blo 976593 1102693 := bbase (se 4 (by rfl) ⟨103377, by rfl⟩ : syracuseStep 1102693 = 206755) (by norm_num)
theorem B1102729 : Blo 976593 1102729 := bbase (se 2 (by rfl) ⟨413523, by rfl⟩ : syracuseStep 1102729 = 827047) (by norm_num)
theorem B1856429 : Blo 976593 1856429 := bbase (se 3 (by rfl) ⟨348080, by rfl⟩ : syracuseStep 1856429 = 696161) (by norm_num)
theorem B1102765 : Blo 976593 1102765 := bbase (se 3 (by rfl) ⟨206768, by rfl⟩ : syracuseStep 1102765 = 413537) (by norm_num)
theorem B2479045 : Blo 976593 2479045 := bbase (se 4 (by rfl) ⟨232410, by rfl⟩ : syracuseStep 2479045 = 464821) (by norm_num)
theorem B1102801 : Blo 976593 1102801 := bbase (se 2 (by rfl) ⟨413550, by rfl⟩ : syracuseStep 1102801 = 827101) (by norm_num)
theorem B1004525 : Blo 976593 1004525 := bbase (se 3 (by rfl) ⟨188348, by rfl⟩ : syracuseStep 1004525 = 376697) (by norm_num)
theorem B1102837 : Blo 976593 1102837 := bbase (se 5 (by rfl) ⟨51695, by rfl⟩ : syracuseStep 1102837 = 103391) (by norm_num)
theorem B1102873 : Blo 976593 1102873 := bbase (se 2 (by rfl) ⟨413577, by rfl⟩ : syracuseStep 1102873 = 827155) (by norm_num)
theorem B2479157 : Blo 976593 2479157 := bbase (se 5 (by rfl) ⟨116210, by rfl⟩ : syracuseStep 2479157 = 232421) (by norm_num)
theorem B1102909 : Blo 976593 1102909 := bbase (se 3 (by rfl) ⟨206795, by rfl⟩ : syracuseStep 1102909 = 413591) (by norm_num)
theorem B3298373 : Blo 976593 3298373 := bbase (se 4 (by rfl) ⟨309222, by rfl⟩ : syracuseStep 3298373 = 618445) (by norm_num)
theorem B1102945 : Blo 976593 1102945 := bbase (se 2 (by rfl) ⟨413604, by rfl⟩ : syracuseStep 1102945 = 827209) (by norm_num)
theorem B1102981 : Blo 976593 1102981 := bbase (se 4 (by rfl) ⟨103404, by rfl⟩ : syracuseStep 1102981 = 206809) (by norm_num)
theorem B1103017 : Blo 976593 1103017 := bbase (se 2 (by rfl) ⟨413631, by rfl⟩ : syracuseStep 1103017 = 827263) (by norm_num)
theorem B1103053 : Blo 976593 1103053 := bbase (se 3 (by rfl) ⟨206822, by rfl⟩ : syracuseStep 1103053 = 413645) (by norm_num)
theorem B1103089 : Blo 976593 1103089 := bbase (se 2 (by rfl) ⟨413658, by rfl⟩ : syracuseStep 1103089 = 827317) (by norm_num)
theorem B2479349 : Blo 976593 2479349 := bbase (se 5 (by rfl) ⟨116219, by rfl⟩ : syracuseStep 2479349 = 232439) (by norm_num)
theorem B1103125 : Blo 976593 1103125 := bbase (se 6 (by rfl) ⟨25854, by rfl⟩ : syracuseStep 1103125 = 51709) (by norm_num)
theorem B3626293 : Blo 976593 3626293 := bbase (se 5 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 3626293 = 339965) (by norm_num)
theorem B1103161 : Blo 976593 1103161 := bbase (se 2 (by rfl) ⟨413685, by rfl⟩ : syracuseStep 1103161 = 827371) (by norm_num)
theorem B8345045 : Blo 976593 8345045 := bbase (se 7 (by rfl) ⟨97793, by rfl⟩ : syracuseStep 8345045 = 195587) (by norm_num)
theorem B3298805 : Blo 976593 3298805 := bbase (se 5 (by rfl) ⟨154631, by rfl⟩ : syracuseStep 3298805 = 309263) (by norm_num)
theorem B2479693 : Blo 976593 2479693 := bbase (se 3 (by rfl) ⟨464942, by rfl⟩ : syracuseStep 2479693 = 929885) (by norm_num)
theorem B2086501 : Blo 976593 2086501 := bbase (se 4 (by rfl) ⟨195609, by rfl⟩ : syracuseStep 2086501 = 391219) (by norm_num)
theorem B1857181 : Blo 976593 1857181 := bbase (se 3 (by rfl) ⟨348221, by rfl⟩ : syracuseStep 1857181 = 696443) (by norm_num)
theorem B2479805 : Blo 976593 2479805 := bbase (se 3 (by rfl) ⟨464963, by rfl⟩ : syracuseStep 2479805 = 929927) (by norm_num)
theorem B2119405 : Blo 976593 2119405 := bbase (se 3 (by rfl) ⟨397388, by rfl⟩ : syracuseStep 2119405 = 794777) (by norm_num)
theorem B2348813 : Blo 976593 2348813 := bbase (se 3 (by rfl) ⟨440402, by rfl⟩ : syracuseStep 2348813 = 880805) (by norm_num)
theorem B1857325 : Blo 976593 1857325 := bbase (se 3 (by rfl) ⟨348248, by rfl⟩ : syracuseStep 1857325 = 696497) (by norm_num)
theorem B2479997 : Blo 976593 2479997 := bbase (se 3 (by rfl) ⟨464999, by rfl⟩ : syracuseStep 2479997 = 929999) (by norm_num)
theorem B2381717 : Blo 976593 2381717 := bbase (se 6 (by rfl) ⟨55821, by rfl⟩ : syracuseStep 2381717 = 111643) (by norm_num)
theorem B3299237 : Blo 976593 3299237 := bbase (se 4 (by rfl) ⟨309303, by rfl⟩ : syracuseStep 3299237 = 618607) (by norm_num)
theorem B4708277 : Blo 976593 4708277 := bbase (se 5 (by rfl) ⟨220700, by rfl⟩ : syracuseStep 4708277 = 441401) (by norm_num)
theorem B2512829 : Blo 976593 2512829 := bbase (se 3 (by rfl) ⟨471155, by rfl⟩ : syracuseStep 2512829 = 942311) (by norm_num)
theorem B2349005 : Blo 976593 2349005 := bbase (se 3 (by rfl) ⟨440438, by rfl⟩ : syracuseStep 2349005 = 880877) (by norm_num)
theorem B1857485 : Blo 976593 1857485 := bbase (se 3 (by rfl) ⟨348278, by rfl⟩ : syracuseStep 1857485 = 696557) (by norm_num)
theorem B22566869 : Blo 976593 22566869 := bbase (se 7 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 22566869 = 528911) (by norm_num)
theorem B2086877 : Blo 976593 2086877 := bbase (se 3 (by rfl) ⟨391289, by rfl⟩ : syracuseStep 2086877 = 782579) (by norm_num)
theorem B2119645 : Blo 976593 2119645 := bbase (se 3 (by rfl) ⟨397433, by rfl⟩ : syracuseStep 2119645 = 794867) (by norm_num)
theorem B2578405 : Blo 976593 2578405 := bbase (se 4 (by rfl) ⟨241725, by rfl⟩ : syracuseStep 2578405 = 483451) (by norm_num)
theorem B6707285 : Blo 976593 6707285 := bbase (se 8 (by rfl) ⟨39300, by rfl⟩ : syracuseStep 6707285 = 78601) (by norm_num)
theorem B1857629 : Blo 976593 1857629 := bbase (se 3 (by rfl) ⟨348305, by rfl⟩ : syracuseStep 1857629 = 696611) (by norm_num)
theorem B2480341 : Blo 976593 2480341 := bbase (se 7 (by rfl) ⟨29066, by rfl⟩ : syracuseStep 2480341 = 58133) (by norm_num)
theorem B2480453 : Blo 976593 2480453 := bbase (se 4 (by rfl) ⟨232542, by rfl⟩ : syracuseStep 2480453 = 465085) (by norm_num)
theorem B3299669 : Blo 976593 3299669 := bbase (se 10 (by rfl) ⟨4833, by rfl⟩ : syracuseStep 3299669 = 9667) (by norm_num)
theorem B2546029 : Blo 976593 2546029 := bbase (se 3 (by rfl) ⟨477380, by rfl⟩ : syracuseStep 2546029 = 954761) (by norm_num)
theorem B1857917 : Blo 976593 1857917 := bbase (se 3 (by rfl) ⟨348359, by rfl⟩ : syracuseStep 1857917 = 696719) (by norm_num)
theorem B2480645 : Blo 976593 2480645 := bbase (se 4 (by rfl) ⟨232560, by rfl⟩ : syracuseStep 2480645 = 465121) (by norm_num)
theorem B1858069 : Blo 976593 1858069 := bbase (se 6 (by rfl) ⟨43548, by rfl⟩ : syracuseStep 1858069 = 87097) (by norm_num)
theorem B1464893 : Blo 976593 1464893 := bbase (se 3 (by rfl) ⟨274667, by rfl⟩ : syracuseStep 1464893 = 549335) (by norm_num)
theorem B1464917 : Blo 976593 1464917 := bbase (se 8 (by rfl) ⟨8583, by rfl⟩ : syracuseStep 1464917 = 17167) (by norm_num)
theorem B1464941 : Blo 976593 1464941 := bbase (se 3 (by rfl) ⟨274676, by rfl⟩ : syracuseStep 1464941 = 549353) (by norm_num)
theorem B2382461 : Blo 976593 2382461 := bbase (se 3 (by rfl) ⟨446711, by rfl⟩ : syracuseStep 2382461 = 893423) (by norm_num)
theorem B1464965 : Blo 976593 1464965 := bbase (se 4 (by rfl) ⟨137340, by rfl⟩ : syracuseStep 1464965 = 274681) (by norm_num)
theorem B1464989 : Blo 976593 1464989 := bbase (se 3 (by rfl) ⟨274685, by rfl⟩ : syracuseStep 1464989 = 549371) (by norm_num)
theorem B1759909 : Blo 976593 1759909 := bbase (se 4 (by rfl) ⟨164991, by rfl⟩ : syracuseStep 1759909 = 329983) (by norm_num)
theorem B2120357 : Blo 976593 2120357 := bbase (se 4 (by rfl) ⟨198783, by rfl⟩ : syracuseStep 2120357 = 397567) (by norm_num)
theorem B1465013 : Blo 976593 1465013 := bbase (se 5 (by rfl) ⟨68672, by rfl⟩ : syracuseStep 1465013 = 137345) (by norm_num)
theorem B1465037 : Blo 976593 1465037 := bbase (se 3 (by rfl) ⟨274694, by rfl⟩ : syracuseStep 1465037 = 549389) (by norm_num)
theorem B1465061 : Blo 976593 1465061 := bbase (se 4 (by rfl) ⟨137349, by rfl⟩ : syracuseStep 1465061 = 274699) (by norm_num)
theorem B1465085 : Blo 976593 1465085 := bbase (se 3 (by rfl) ⟨274703, by rfl⟩ : syracuseStep 1465085 = 549407) (by norm_num)
theorem B3300101 : Blo 976593 3300101 := bbase (se 4 (by rfl) ⟨309384, by rfl⟩ : syracuseStep 3300101 = 618769) (by norm_num)
theorem B3136261 : Blo 976593 3136261 := bbase (se 4 (by rfl) ⟨294024, by rfl⟩ : syracuseStep 3136261 = 588049) (by norm_num)
theorem B1006349 : Blo 976593 1006349 := bbase (se 3 (by rfl) ⟨188690, by rfl⟩ : syracuseStep 1006349 = 377381) (by norm_num)
theorem B1465109 : Blo 976593 1465109 := bbase (se 6 (by rfl) ⟨34338, by rfl⟩ : syracuseStep 1465109 = 68677) (by norm_num)
theorem B1465133 : Blo 976593 1465133 := bbase (se 3 (by rfl) ⟨274712, by rfl⟩ : syracuseStep 1465133 = 549425) (by norm_num)
theorem B1760069 : Blo 976593 1760069 := bbase (se 4 (by rfl) ⟨165006, by rfl⟩ : syracuseStep 1760069 = 330013) (by norm_num)
theorem B1465157 : Blo 976593 1465157 := bbase (se 4 (by rfl) ⟨137358, by rfl⟩ : syracuseStep 1465157 = 274717) (by norm_num)
theorem B1858373 : Blo 976593 1858373 := bbase (se 4 (by rfl) ⟨174222, by rfl⟩ : syracuseStep 1858373 = 348445) (by norm_num)
theorem B1465181 : Blo 976593 1465181 := bbase (se 3 (by rfl) ⟨274721, by rfl⟩ : syracuseStep 1465181 = 549443) (by norm_num)
theorem B2480989 : Blo 976593 2480989 := bbase (se 3 (by rfl) ⟨465185, by rfl⟩ : syracuseStep 2480989 = 930371) (by norm_num)
theorem B1465205 : Blo 976593 1465205 := bbase (se 5 (by rfl) ⟨68681, by rfl⟩ : syracuseStep 1465205 = 137363) (by norm_num)
theorem B1465229 : Blo 976593 1465229 := bbase (se 3 (by rfl) ⟨274730, by rfl⟩ : syracuseStep 1465229 = 549461) (by norm_num)
theorem B1465253 : Blo 976593 1465253 := bbase (se 4 (by rfl) ⟨137367, by rfl⟩ : syracuseStep 1465253 = 274735) (by norm_num)
theorem B1465277 : Blo 976593 1465277 := bbase (se 3 (by rfl) ⟨274739, by rfl⟩ : syracuseStep 1465277 = 549479) (by norm_num)
theorem B2481101 : Blo 976593 2481101 := bbase (se 3 (by rfl) ⟨465206, by rfl⟩ : syracuseStep 2481101 = 930413) (by norm_num)
theorem B1465301 : Blo 976593 1465301 := bbase (se 7 (by rfl) ⟨17171, by rfl⟩ : syracuseStep 1465301 = 34343) (by norm_num)
theorem B1465325 : Blo 976593 1465325 := bbase (se 3 (by rfl) ⟨274748, by rfl⟩ : syracuseStep 1465325 = 549497) (by norm_num)
theorem B1465349 : Blo 976593 1465349 := bbase (se 4 (by rfl) ⟨137376, by rfl⟩ : syracuseStep 1465349 = 274753) (by norm_num)
theorem B1465373 : Blo 976593 1465373 := bbase (se 3 (by rfl) ⟨274757, by rfl⟩ : syracuseStep 1465373 = 549515) (by norm_num)
theorem B1465397 : Blo 976593 1465397 := bbase (se 5 (by rfl) ⟨68690, by rfl⟩ : syracuseStep 1465397 = 137381) (by norm_num)
theorem B1465421 : Blo 976593 1465421 := bbase (se 3 (by rfl) ⟨274766, by rfl⟩ : syracuseStep 1465421 = 549533) (by norm_num)
theorem B1465445 : Blo 976593 1465445 := bbase (se 4 (by rfl) ⟨137385, by rfl⟩ : syracuseStep 1465445 = 274771) (by norm_num)
theorem B1465469 : Blo 976593 1465469 := bbase (se 3 (by rfl) ⟨274775, by rfl⟩ : syracuseStep 1465469 = 549551) (by norm_num)
theorem B2481293 : Blo 976593 2481293 := bbase (se 3 (by rfl) ⟨465242, by rfl⟩ : syracuseStep 2481293 = 930485) (by norm_num)
theorem B1465493 : Blo 976593 1465493 := bbase (se 6 (by rfl) ⟨34347, by rfl⟩ : syracuseStep 1465493 = 68695) (by norm_num)
theorem B1465517 : Blo 976593 1465517 := bbase (se 3 (by rfl) ⟨274784, by rfl⟩ : syracuseStep 1465517 = 549569) (by norm_num)
theorem B3300533 : Blo 976593 3300533 := bbase (se 5 (by rfl) ⟨154712, by rfl⟩ : syracuseStep 3300533 = 309425) (by norm_num)
theorem B2645173 : Blo 976593 2645173 := bbase (se 5 (by rfl) ⟨123992, by rfl⟩ : syracuseStep 2645173 = 247985) (by norm_num)
theorem B3529909 : Blo 976593 3529909 := bbase (se 5 (by rfl) ⟨165464, by rfl⟩ : syracuseStep 3529909 = 330929) (by norm_num)
theorem B1236161 : Blo 976593 1236161 := bbase (se 2 (by rfl) ⟨463560, by rfl⟩ : syracuseStep 1236161 = 927121) (by norm_num)
theorem B1465541 : Blo 976593 1465541 := bbase (se 4 (by rfl) ⟨137394, by rfl⟩ : syracuseStep 1465541 = 274789) (by norm_num)
theorem B1465565 : Blo 976593 1465565 := bbase (se 3 (by rfl) ⟨274793, by rfl⟩ : syracuseStep 1465565 = 549587) (by norm_num)
theorem B1465589 : Blo 976593 1465589 := bbase (se 5 (by rfl) ⟨68699, by rfl⟩ : syracuseStep 1465589 = 137399) (by norm_num)
theorem B1236217 : Blo 976593 1236217 := bbase (se 2 (by rfl) ⟨463581, by rfl⟩ : syracuseStep 1236217 = 927163) (by norm_num)
theorem B1465613 : Blo 976593 1465613 := bbase (se 3 (by rfl) ⟨274802, by rfl⟩ : syracuseStep 1465613 = 549605) (by norm_num)
theorem B1465637 : Blo 976593 1465637 := bbase (se 4 (by rfl) ⟨137403, by rfl⟩ : syracuseStep 1465637 = 274807) (by norm_num)
theorem B1465661 : Blo 976593 1465661 := bbase (se 3 (by rfl) ⟨274811, by rfl⟩ : syracuseStep 1465661 = 549623) (by norm_num)
theorem B1465685 : Blo 976593 1465685 := bbase (se 11 (by rfl) ⟨1073, by rfl⟩ : syracuseStep 1465685 = 2147) (by norm_num)
theorem B13557077 : Blo 976593 13557077 := bbase (se 11 (by rfl) ⟨9929, by rfl⟩ : syracuseStep 13557077 = 19859) (by norm_num)
theorem B1236313 : Blo 976593 1236313 := bbase (se 2 (by rfl) ⟨463617, by rfl⟩ : syracuseStep 1236313 = 927235) (by norm_num)
theorem B1465709 : Blo 976593 1465709 := bbase (se 3 (by rfl) ⟨274820, by rfl⟩ : syracuseStep 1465709 = 549641) (by norm_num)
theorem B1465733 : Blo 976593 1465733 := bbase (se 4 (by rfl) ⟨137412, by rfl⟩ : syracuseStep 1465733 = 274825) (by norm_num)
theorem B1465757 : Blo 976593 1465757 := bbase (se 3 (by rfl) ⟨274829, by rfl⟩ : syracuseStep 1465757 = 549659) (by norm_num)
theorem B1465781 : Blo 976593 1465781 := bbase (se 5 (by rfl) ⟨68708, by rfl⟩ : syracuseStep 1465781 = 137417) (by norm_num)
theorem B1465805 : Blo 976593 1465805 := bbase (se 3 (by rfl) ⟨274838, by rfl⟩ : syracuseStep 1465805 = 549677) (by norm_num)
theorem B1465829 : Blo 976593 1465829 := bbase (se 4 (by rfl) ⟨137421, by rfl⟩ : syracuseStep 1465829 = 274843) (by norm_num)
theorem B2481637 : Blo 976593 2481637 := bbase (se 4 (by rfl) ⟨232653, by rfl⟩ : syracuseStep 2481637 = 465307) (by norm_num)
theorem B1465853 : Blo 976593 1465853 := bbase (se 3 (by rfl) ⟨274847, by rfl⟩ : syracuseStep 1465853 = 549695) (by norm_num)
theorem B1236485 : Blo 976593 1236485 := bbase (se 4 (by rfl) ⟨115920, by rfl⟩ : syracuseStep 1236485 = 231841) (by norm_num)
theorem B1465877 : Blo 976593 1465877 := bbase (se 6 (by rfl) ⟨34356, by rfl⟩ : syracuseStep 1465877 = 68713) (by norm_num)
theorem B1465901 : Blo 976593 1465901 := bbase (se 3 (by rfl) ⟨274856, by rfl⟩ : syracuseStep 1465901 = 549713) (by norm_num)
theorem B1859125 : Blo 976593 1859125 := bbase (se 5 (by rfl) ⟨87146, by rfl⟩ : syracuseStep 1859125 = 174293) (by norm_num)
theorem B1236541 : Blo 976593 1236541 := bbase (se 3 (by rfl) ⟨231851, by rfl⟩ : syracuseStep 1236541 = 463703) (by norm_num)
theorem B1465925 : Blo 976593 1465925 := bbase (se 4 (by rfl) ⟨137430, by rfl⟩ : syracuseStep 1465925 = 274861) (by norm_num)
theorem B2088517 : Blo 976593 2088517 := bbase (se 4 (by rfl) ⟨195798, by rfl⟩ : syracuseStep 2088517 = 391597) (by norm_num)
theorem B2481749 : Blo 976593 2481749 := bbase (se 8 (by rfl) ⟨14541, by rfl⟩ : syracuseStep 2481749 = 29083) (by norm_num)
theorem B1465949 : Blo 976593 1465949 := bbase (se 3 (by rfl) ⟨274865, by rfl⟩ : syracuseStep 1465949 = 549731) (by norm_num)
theorem B3300965 : Blo 976593 3300965 := bbase (se 4 (by rfl) ⟨309465, by rfl⟩ : syracuseStep 3300965 = 618931) (by norm_num)
theorem B1465973 : Blo 976593 1465973 := bbase (se 5 (by rfl) ⟨68717, by rfl⟩ : syracuseStep 1465973 = 137435) (by norm_num)
theorem B1465997 : Blo 976593 1465997 := bbase (se 3 (by rfl) ⟨274874, by rfl⟩ : syracuseStep 1465997 = 549749) (by norm_num)
theorem B3399317 : Blo 976593 3399317 := bbase (se 6 (by rfl) ⟨79671, by rfl⟩ : syracuseStep 3399317 = 159343) (by norm_num)
theorem B1236637 : Blo 976593 1236637 := bbase (se 3 (by rfl) ⟨231869, by rfl⟩ : syracuseStep 1236637 = 463739) (by norm_num)
theorem B1466021 : Blo 976593 1466021 := bbase (se 4 (by rfl) ⟨137439, by rfl⟩ : syracuseStep 1466021 = 274879) (by norm_num)
theorem B1466045 : Blo 976593 1466045 := bbase (se 3 (by rfl) ⟨274883, by rfl⟩ : syracuseStep 1466045 = 549767) (by norm_num)
theorem B1859269 : Blo 976593 1859269 := bbase (se 4 (by rfl) ⟨174306, by rfl⟩ : syracuseStep 1859269 = 348613) (by norm_num)
theorem B1466069 : Blo 976593 1466069 := bbase (se 7 (by rfl) ⟨17180, by rfl⟩ : syracuseStep 1466069 = 34361) (by norm_num)
theorem B1466093 : Blo 976593 1466093 := bbase (se 3 (by rfl) ⟨274892, by rfl⟩ : syracuseStep 1466093 = 549785) (by norm_num)
theorem B1466117 : Blo 976593 1466117 := bbase (se 4 (by rfl) ⟨137448, by rfl⟩ : syracuseStep 1466117 = 274897) (by norm_num)
theorem B2481941 : Blo 976593 2481941 := bbase (se 6 (by rfl) ⟨58170, by rfl⟩ : syracuseStep 2481941 = 116341) (by norm_num)
theorem B1466141 : Blo 976593 1466141 := bbase (se 3 (by rfl) ⟨274901, by rfl⟩ : syracuseStep 1466141 = 549803) (by norm_num)
theorem B1466165 : Blo 976593 1466165 := bbase (se 5 (by rfl) ⟨68726, by rfl⟩ : syracuseStep 1466165 = 137453) (by norm_num)
theorem B1236809 : Blo 976593 1236809 := bbase (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) (by norm_num)
theorem B1466189 : Blo 976593 1466189 := bbase (se 3 (by rfl) ⟨274910, by rfl⟩ : syracuseStep 1466189 = 549821) (by norm_num)
theorem B1466213 : Blo 976593 1466213 := bbase (se 4 (by rfl) ⟨137457, by rfl⟩ : syracuseStep 1466213 = 274915) (by norm_num)
theorem B1859429 : Blo 976593 1859429 := bbase (se 4 (by rfl) ⟨174321, by rfl⟩ : syracuseStep 1859429 = 348643) (by norm_num)
theorem B2350957 : Blo 976593 2350957 := bbase (se 3 (by rfl) ⟨440804, by rfl⟩ : syracuseStep 2350957 = 881609) (by norm_num)
theorem B1761149 : Blo 976593 1761149 := bbase (se 3 (by rfl) ⟨330215, by rfl⟩ : syracuseStep 1761149 = 660431) (by norm_num)
theorem B1466237 : Blo 976593 1466237 := bbase (se 3 (by rfl) ⟨274919, by rfl⟩ : syracuseStep 1466237 = 549839) (by norm_num)
theorem B1236865 : Blo 976593 1236865 := bbase (se 2 (by rfl) ⟨463824, by rfl⟩ : syracuseStep 1236865 = 927649) (by norm_num)
theorem B1466261 : Blo 976593 1466261 := bbase (se 6 (by rfl) ⟨34365, by rfl⟩ : syracuseStep 1466261 = 68731) (by norm_num)
theorem B1466285 : Blo 976593 1466285 := bbase (se 3 (by rfl) ⟨274928, by rfl⟩ : syracuseStep 1466285 = 549857) (by norm_num)
theorem B1466309 : Blo 976593 1466309 := bbase (se 4 (by rfl) ⟨137466, by rfl⟩ : syracuseStep 1466309 = 274933) (by norm_num)
theorem B1466333 : Blo 976593 1466333 := bbase (se 3 (by rfl) ⟨274937, by rfl⟩ : syracuseStep 1466333 = 549875) (by norm_num)
theorem B1236961 : Blo 976593 1236961 := bbase (se 2 (by rfl) ⟨463860, by rfl⟩ : syracuseStep 1236961 = 927721) (by norm_num)
theorem B1564645 : Blo 976593 1564645 := bbase (se 4 (by rfl) ⟨146685, by rfl⟩ : syracuseStep 1564645 = 293371) (by norm_num)
theorem B1466357 : Blo 976593 1466357 := bbase (se 5 (by rfl) ⟨68735, by rfl⟩ : syracuseStep 1466357 = 137471) (by norm_num)
theorem B1859573 : Blo 976593 1859573 := bbase (se 5 (by rfl) ⟨87167, by rfl⟩ : syracuseStep 1859573 = 174335) (by norm_num)
theorem B1761293 : Blo 976593 1761293 := bbase (se 3 (by rfl) ⟨330242, by rfl⟩ : syracuseStep 1761293 = 660485) (by norm_num)
theorem B1466381 : Blo 976593 1466381 := bbase (se 3 (by rfl) ⟨274946, by rfl⟩ : syracuseStep 1466381 = 549893) (by norm_num)
theorem B3301397 : Blo 976593 3301397 := bbase (se 6 (by rfl) ⟨77376, by rfl⟩ : syracuseStep 3301397 = 154753) (by norm_num)
theorem B1466405 : Blo 976593 1466405 := bbase (se 4 (by rfl) ⟨137475, by rfl⟩ : syracuseStep 1466405 = 274951) (by norm_num)
theorem B1466429 : Blo 976593 1466429 := bbase (se 3 (by rfl) ⟨274955, by rfl⟩ : syracuseStep 1466429 = 549911) (by norm_num)
theorem B1466453 : Blo 976593 1466453 := bbase (se 8 (by rfl) ⟨8592, by rfl⟩ : syracuseStep 1466453 = 17185) (by norm_num)
theorem B1466477 : Blo 976593 1466477 := bbase (se 3 (by rfl) ⟨274964, by rfl⟩ : syracuseStep 1466477 = 549929) (by norm_num)
theorem B1466501 : Blo 976593 1466501 := bbase (se 4 (by rfl) ⟨137484, by rfl⟩ : syracuseStep 1466501 = 274969) (by norm_num)
theorem B1237133 : Blo 976593 1237133 := bbase (se 3 (by rfl) ⟨231962, by rfl⟩ : syracuseStep 1237133 = 463925) (by norm_num)
theorem B1466525 : Blo 976593 1466525 := bbase (se 3 (by rfl) ⟨274973, by rfl⟩ : syracuseStep 1466525 = 549947) (by norm_num)
theorem B1466549 : Blo 976593 1466549 := bbase (se 5 (by rfl) ⟨68744, by rfl⟩ : syracuseStep 1466549 = 137489) (by norm_num)
theorem B1237189 : Blo 976593 1237189 := bbase (se 4 (by rfl) ⟨115986, by rfl⟩ : syracuseStep 1237189 = 231973) (by norm_num)
theorem B1466573 : Blo 976593 1466573 := bbase (se 3 (by rfl) ⟨274982, by rfl⟩ : syracuseStep 1466573 = 549965) (by norm_num)
theorem B1466597 : Blo 976593 1466597 := bbase (se 4 (by rfl) ⟨137493, by rfl⟩ : syracuseStep 1466597 = 274987) (by norm_num)
theorem B1466621 : Blo 976593 1466621 := bbase (se 3 (by rfl) ⟨274991, by rfl⟩ : syracuseStep 1466621 = 549983) (by norm_num)
theorem B1466645 : Blo 976593 1466645 := bbase (se 6 (by rfl) ⟨34374, by rfl⟩ : syracuseStep 1466645 = 68749) (by norm_num)
theorem B1859861 : Blo 976593 1859861 := bbase (se 6 (by rfl) ⟨43590, by rfl⟩ : syracuseStep 1859861 = 87181) (by norm_num)
theorem B1237285 : Blo 976593 1237285 := bbase (se 4 (by rfl) ⟨115995, by rfl⟩ : syracuseStep 1237285 = 231991) (by norm_num)
theorem B1466669 : Blo 976593 1466669 := bbase (se 3 (by rfl) ⟨275000, by rfl⟩ : syracuseStep 1466669 = 550001) (by norm_num)
theorem B7430453 : Blo 976593 7430453 := bbase (se 5 (by rfl) ⟨348302, by rfl⟩ : syracuseStep 7430453 = 696605) (by norm_num)
theorem B1466693 : Blo 976593 1466693 := bbase (se 4 (by rfl) ⟨137502, by rfl⟩ : syracuseStep 1466693 = 275005) (by norm_num)
theorem B1466717 : Blo 976593 1466717 := bbase (se 3 (by rfl) ⟨275009, by rfl⟩ : syracuseStep 1466717 = 550019) (by norm_num)
theorem B8348021 : Blo 976593 8348021 := bbase (se 5 (by rfl) ⟨391313, by rfl⟩ : syracuseStep 8348021 = 782627) (by norm_num)
theorem B1466741 : Blo 976593 1466741 := bbase (se 5 (by rfl) ⟨68753, by rfl⟩ : syracuseStep 1466741 = 137507) (by norm_num)
theorem B1466765 : Blo 976593 1466765 := bbase (se 3 (by rfl) ⟨275018, by rfl⟩ : syracuseStep 1466765 = 550037) (by norm_num)
theorem B1466789 : Blo 976593 1466789 := bbase (se 4 (by rfl) ⟨137511, by rfl⟩ : syracuseStep 1466789 = 275023) (by norm_num)
theorem B2646437 : Blo 976593 2646437 := bbase (se 4 (by rfl) ⟨248103, by rfl⟩ : syracuseStep 2646437 = 496207) (by norm_num)
theorem B1860013 : Blo 976593 1860013 := bbase (se 3 (by rfl) ⟨348752, by rfl⟩ : syracuseStep 1860013 = 697505) (by norm_num)
theorem B1466813 : Blo 976593 1466813 := bbase (se 3 (by rfl) ⟨275027, by rfl⟩ : syracuseStep 1466813 = 550055) (by norm_num)
theorem B2089405 : Blo 976593 2089405 := bbase (se 3 (by rfl) ⟨391763, by rfl⟩ : syracuseStep 2089405 = 783527) (by norm_num)
theorem B3301829 : Blo 976593 3301829 := bbase (se 4 (by rfl) ⟨309546, by rfl⟩ : syracuseStep 3301829 = 619093) (by norm_num)
theorem B1237457 : Blo 976593 1237457 := bbase (se 2 (by rfl) ⟨464046, by rfl⟩ : syracuseStep 1237457 = 928093) (by norm_num)
theorem B1466837 : Blo 976593 1466837 := bbase (se 7 (by rfl) ⟨17189, by rfl⟩ : syracuseStep 1466837 = 34379) (by norm_num)
theorem B1466861 : Blo 976593 1466861 := bbase (se 3 (by rfl) ⟨275036, by rfl⟩ : syracuseStep 1466861 = 550073) (by norm_num)
theorem B1466885 : Blo 976593 1466885 := bbase (se 4 (by rfl) ⟨137520, by rfl⟩ : syracuseStep 1466885 = 275041) (by norm_num)
theorem B1237513 : Blo 976593 1237513 := bbase (se 2 (by rfl) ⟨464067, by rfl⟩ : syracuseStep 1237513 = 928135) (by norm_num)
theorem B1466909 : Blo 976593 1466909 := bbase (se 3 (by rfl) ⟨275045, by rfl⟩ : syracuseStep 1466909 = 550091) (by norm_num)
theorem B1466933 : Blo 976593 1466933 := bbase (se 5 (by rfl) ⟨68762, by rfl⟩ : syracuseStep 1466933 = 137525) (by norm_num)
theorem B1466957 : Blo 976593 1466957 := bbase (se 3 (by rfl) ⟨275054, by rfl⟩ : syracuseStep 1466957 = 550109) (by norm_num)
theorem B1466981 : Blo 976593 1466981 := bbase (se 4 (by rfl) ⟨137529, by rfl⟩ : syracuseStep 1466981 = 275059) (by norm_num)
theorem B1237609 : Blo 976593 1237609 := bbase (se 2 (by rfl) ⟨464103, by rfl⟩ : syracuseStep 1237609 = 928207) (by norm_num)
theorem B1467005 : Blo 976593 1467005 := bbase (se 3 (by rfl) ⟨275063, by rfl⟩ : syracuseStep 1467005 = 550127) (by norm_num)
theorem B1467029 : Blo 976593 1467029 := bbase (se 6 (by rfl) ⟨34383, by rfl⟩ : syracuseStep 1467029 = 68767) (by norm_num)
theorem B1467053 : Blo 976593 1467053 := bbase (se 3 (by rfl) ⟨275072, by rfl⟩ : syracuseStep 1467053 = 550145) (by norm_num)
theorem B1467077 : Blo 976593 1467077 := bbase (se 4 (by rfl) ⟨137538, by rfl⟩ : syracuseStep 1467077 = 275077) (by norm_num)
theorem B1467101 : Blo 976593 1467101 := bbase (se 3 (by rfl) ⟨275081, by rfl⟩ : syracuseStep 1467101 = 550163) (by norm_num)
theorem B1860317 : Blo 976593 1860317 := bbase (se 3 (by rfl) ⟨348809, by rfl⟩ : syracuseStep 1860317 = 697619) (by norm_num)
theorem B1467125 : Blo 976593 1467125 := bbase (se 5 (by rfl) ⟨68771, by rfl⟩ : syracuseStep 1467125 = 137543) (by norm_num)
theorem B1467149 : Blo 976593 1467149 := bbase (se 3 (by rfl) ⟨275090, by rfl⟩ : syracuseStep 1467149 = 550181) (by norm_num)
theorem B1237781 : Blo 976593 1237781 := bbase (se 6 (by rfl) ⟨29010, by rfl⟩ : syracuseStep 1237781 = 58021) (by norm_num)
theorem B1467173 : Blo 976593 1467173 := bbase (se 4 (by rfl) ⟨137547, by rfl⟩ : syracuseStep 1467173 = 275095) (by norm_num)
theorem B2351909 : Blo 976593 2351909 := bbase (se 4 (by rfl) ⟨220491, by rfl⟩ : syracuseStep 2351909 = 440983) (by norm_num)
theorem B2974517 : Blo 976593 2974517 := bbase (se 5 (by rfl) ⟨139430, by rfl⟩ : syracuseStep 2974517 = 278861) (by norm_num)
theorem B1467197 : Blo 976593 1467197 := bbase (se 3 (by rfl) ⟨275099, by rfl⟩ : syracuseStep 1467197 = 550199) (by norm_num)
theorem B1237837 : Blo 976593 1237837 := bbase (se 3 (by rfl) ⟨232094, by rfl⟩ : syracuseStep 1237837 = 464189) (by norm_num)
theorem B1467221 : Blo 976593 1467221 := bbase (se 9 (by rfl) ⟨4298, by rfl⟩ : syracuseStep 1467221 = 8597) (by norm_num)
theorem B2351965 : Blo 976593 2351965 := bbase (se 3 (by rfl) ⟨440993, by rfl⟩ : syracuseStep 2351965 = 881987) (by norm_num)
theorem B1467245 : Blo 976593 1467245 := bbase (se 3 (by rfl) ⟨275108, by rfl⟩ : syracuseStep 1467245 = 550217) (by norm_num)
theorem B3302261 : Blo 976593 3302261 := bbase (se 5 (by rfl) ⟨154793, by rfl⟩ : syracuseStep 3302261 = 309587) (by norm_num)
theorem B4186997 : Blo 976593 4186997 := bbase (se 5 (by rfl) ⟨196265, by rfl⟩ : syracuseStep 4186997 = 392531) (by norm_num)
theorem B1467269 : Blo 976593 1467269 := bbase (se 4 (by rfl) ⟨137556, by rfl⟩ : syracuseStep 1467269 = 275113) (by norm_num)
theorem B1565581 : Blo 976593 1565581 := bbase (se 3 (by rfl) ⟨293546, by rfl⟩ : syracuseStep 1565581 = 587093) (by norm_num)
theorem B1467293 : Blo 976593 1467293 := bbase (se 3 (by rfl) ⟨275117, by rfl⟩ : syracuseStep 1467293 = 550235) (by norm_num)
theorem B1237933 : Blo 976593 1237933 := bbase (se 3 (by rfl) ⟨232112, by rfl⟩ : syracuseStep 1237933 = 464225) (by norm_num)
theorem B2089901 : Blo 976593 2089901 := bbase (se 3 (by rfl) ⟨391856, by rfl⟩ : syracuseStep 2089901 = 783713) (by norm_num)
theorem B1467317 : Blo 976593 1467317 := bbase (se 5 (by rfl) ⟨68780, by rfl⟩ : syracuseStep 1467317 = 137561) (by norm_num)
theorem B1467341 : Blo 976593 1467341 := bbase (se 3 (by rfl) ⟨275126, by rfl⟩ : syracuseStep 1467341 = 550253) (by norm_num)
theorem B1467365 : Blo 976593 1467365 := bbase (se 4 (by rfl) ⟨137565, by rfl⟩ : syracuseStep 1467365 = 275131) (by norm_num)
theorem B1467389 : Blo 976593 1467389 := bbase (se 3 (by rfl) ⟨275135, by rfl⟩ : syracuseStep 1467389 = 550271) (by norm_num)
theorem B1467413 : Blo 976593 1467413 := bbase (se 6 (by rfl) ⟨34392, by rfl⟩ : syracuseStep 1467413 = 68785) (by norm_num)
theorem B1467437 : Blo 976593 1467437 := bbase (se 3 (by rfl) ⟨275144, by rfl⟩ : syracuseStep 1467437 = 550289) (by norm_num)
theorem B1467461 : Blo 976593 1467461 := bbase (se 4 (by rfl) ⟨137574, by rfl⟩ : syracuseStep 1467461 = 275149) (by norm_num)
theorem B1238105 : Blo 976593 1238105 := bbase (se 2 (by rfl) ⟨464289, by rfl⟩ : syracuseStep 1238105 = 928579) (by norm_num)
theorem B1467485 : Blo 976593 1467485 := bbase (se 3 (by rfl) ⟨275153, by rfl⟩ : syracuseStep 1467485 = 550307) (by norm_num)
theorem B1467509 : Blo 976593 1467509 := bbase (se 5 (by rfl) ⟨68789, by rfl⟩ : syracuseStep 1467509 = 137579) (by norm_num)
theorem B1467533 : Blo 976593 1467533 := bbase (se 3 (by rfl) ⟨275162, by rfl⟩ : syracuseStep 1467533 = 550325) (by norm_num)
theorem B1238161 : Blo 976593 1238161 := bbase (se 2 (by rfl) ⟨464310, by rfl⟩ : syracuseStep 1238161 = 928621) (by norm_num)
theorem B4187285 : Blo 976593 4187285 := bbase (se 6 (by rfl) ⟨98139, by rfl⟩ : syracuseStep 4187285 = 196279) (by norm_num)
theorem B1467557 : Blo 976593 1467557 := bbase (se 4 (by rfl) ⟨137583, by rfl⟩ : syracuseStep 1467557 = 275167) (by norm_num)
theorem B1467581 : Blo 976593 1467581 := bbase (se 3 (by rfl) ⟨275171, by rfl⟩ : syracuseStep 1467581 = 550343) (by norm_num)
theorem B1467605 : Blo 976593 1467605 := bbase (se 7 (by rfl) ⟨17198, by rfl⟩ : syracuseStep 1467605 = 34397) (by norm_num)
theorem B2352341 : Blo 976593 2352341 := bbase (se 7 (by rfl) ⟨27566, by rfl⟩ : syracuseStep 2352341 = 55133) (by norm_num)
theorem B1271017 : Blo 976593 1271017 := bbase (se 2 (by rfl) ⟨476631, by rfl⟩ : syracuseStep 1271017 = 953263) (by norm_num)
theorem B1467629 : Blo 976593 1467629 := bbase (se 3 (by rfl) ⟨275180, by rfl⟩ : syracuseStep 1467629 = 550361) (by norm_num)
theorem B1238257 : Blo 976593 1238257 := bbase (se 2 (by rfl) ⟨464346, by rfl⟩ : syracuseStep 1238257 = 928693) (by norm_num)
theorem B5563637 : Blo 976593 5563637 := bbase (se 5 (by rfl) ⟨260795, by rfl⟩ : syracuseStep 5563637 = 521591) (by norm_num)
theorem B1467653 : Blo 976593 1467653 := bbase (se 4 (by rfl) ⟨137592, by rfl⟩ : syracuseStep 1467653 = 275185) (by norm_num)
theorem B1467677 : Blo 976593 1467677 := bbase (se 3 (by rfl) ⟨275189, by rfl⟩ : syracuseStep 1467677 = 550379) (by norm_num)
theorem B3302693 : Blo 976593 3302693 := bbase (se 4 (by rfl) ⟨309627, by rfl⟩ : syracuseStep 3302693 = 619255) (by norm_num)
theorem B1467701 : Blo 976593 1467701 := bbase (se 5 (by rfl) ⟨68798, by rfl⟩ : syracuseStep 1467701 = 137597) (by norm_num)
theorem B1467725 : Blo 976593 1467725 := bbase (se 3 (by rfl) ⟨275198, by rfl⟩ : syracuseStep 1467725 = 550397) (by norm_num)
theorem B1467749 : Blo 976593 1467749 := bbase (se 4 (by rfl) ⟨137601, by rfl⟩ : syracuseStep 1467749 = 275203) (by norm_num)
theorem B1467773 : Blo 976593 1467773 := bbase (se 3 (by rfl) ⟨275207, by rfl⟩ : syracuseStep 1467773 = 550415) (by norm_num)
theorem B1467797 : Blo 976593 1467797 := bbase (se 6 (by rfl) ⟨34401, by rfl⟩ : syracuseStep 1467797 = 68803) (by norm_num)
theorem B1238429 : Blo 976593 1238429 := bbase (se 3 (by rfl) ⟨232205, by rfl⟩ : syracuseStep 1238429 = 464411) (by norm_num)
theorem B1467821 : Blo 976593 1467821 := bbase (se 3 (by rfl) ⟨275216, by rfl⟩ : syracuseStep 1467821 = 550433) (by norm_num)
theorem B1467845 : Blo 976593 1467845 := bbase (se 4 (by rfl) ⟨137610, by rfl⟩ : syracuseStep 1467845 = 275221) (by norm_num)
theorem B2352581 : Blo 976593 2352581 := bbase (se 4 (by rfl) ⟨220554, by rfl⟩ : syracuseStep 2352581 = 441109) (by norm_num)
theorem B1861069 : Blo 976593 1861069 := bbase (se 3 (by rfl) ⟨348950, by rfl⟩ : syracuseStep 1861069 = 697901) (by norm_num)
theorem B1238485 : Blo 976593 1238485 := bbase (se 7 (by rfl) ⟨14513, by rfl⟩ : syracuseStep 1238485 = 29027) (by norm_num)
theorem B1467869 : Blo 976593 1467869 := bbase (se 3 (by rfl) ⟨275225, by rfl⟩ : syracuseStep 1467869 = 550451) (by norm_num)
theorem B1467893 : Blo 976593 1467893 := bbase (se 5 (by rfl) ⟨68807, by rfl⟩ : syracuseStep 1467893 = 137615) (by norm_num)
theorem B1467917 : Blo 976593 1467917 := bbase (se 3 (by rfl) ⟨275234, by rfl⟩ : syracuseStep 1467917 = 550469) (by norm_num)
theorem B1467941 : Blo 976593 1467941 := bbase (se 4 (by rfl) ⟨137619, by rfl⟩ : syracuseStep 1467941 = 275239) (by norm_num)
theorem B1238581 : Blo 976593 1238581 := bbase (se 5 (by rfl) ⟨58058, by rfl⟩ : syracuseStep 1238581 = 116117) (by norm_num)
theorem B1467965 : Blo 976593 1467965 := bbase (se 3 (by rfl) ⟨275243, by rfl⟩ : syracuseStep 1467965 = 550487) (by norm_num)
theorem B1467989 : Blo 976593 1467989 := bbase (se 8 (by rfl) ⟨8601, by rfl⟩ : syracuseStep 1467989 = 17203) (by norm_num)
theorem B1861213 : Blo 976593 1861213 := bbase (se 3 (by rfl) ⟨348977, by rfl⟩ : syracuseStep 1861213 = 697955) (by norm_num)
theorem B1468013 : Blo 976593 1468013 := bbase (se 3 (by rfl) ⟨275252, by rfl⟩ : syracuseStep 1468013 = 550505) (by norm_num)
theorem B1468037 : Blo 976593 1468037 := bbase (se 4 (by rfl) ⟨137628, by rfl⟩ : syracuseStep 1468037 = 275257) (by norm_num)
theorem B1468061 : Blo 976593 1468061 := bbase (se 3 (by rfl) ⟨275261, by rfl⟩ : syracuseStep 1468061 = 550523) (by norm_num)
theorem B1468085 : Blo 976593 1468085 := bbase (se 5 (by rfl) ⟨68816, by rfl⟩ : syracuseStep 1468085 = 137633) (by norm_num)
theorem B1468109 : Blo 976593 1468109 := bbase (se 3 (by rfl) ⟨275270, by rfl⟩ : syracuseStep 1468109 = 550541) (by norm_num)
theorem B3303125 : Blo 976593 3303125 := bbase (se 7 (by rfl) ⟨38708, by rfl⟩ : syracuseStep 3303125 = 77417) (by norm_num)
theorem B1238753 : Blo 976593 1238753 := bbase (se 2 (by rfl) ⟨464532, by rfl⟩ : syracuseStep 1238753 = 929065) (by norm_num)
theorem B1468133 : Blo 976593 1468133 := bbase (se 4 (by rfl) ⟨137637, by rfl⟩ : syracuseStep 1468133 = 275275) (by norm_num)
theorem B1468157 : Blo 976593 1468157 := bbase (se 3 (by rfl) ⟨275279, by rfl⟩ : syracuseStep 1468157 = 550559) (by norm_num)
theorem B1861373 : Blo 976593 1861373 := bbase (se 3 (by rfl) ⟨349007, by rfl⟩ : syracuseStep 1861373 = 698015) (by norm_num)
theorem B2090765 : Blo 976593 2090765 := bbase (se 3 (by rfl) ⟨392018, by rfl⟩ : syracuseStep 2090765 = 784037) (by norm_num)
theorem B1468181 : Blo 976593 1468181 := bbase (se 6 (by rfl) ⟨34410, by rfl⟩ : syracuseStep 1468181 = 68821) (by norm_num)
theorem B1238809 : Blo 976593 1238809 := bbase (se 2 (by rfl) ⟨464553, by rfl⟩ : syracuseStep 1238809 = 929107) (by norm_num)
theorem B1468205 : Blo 976593 1468205 := bbase (se 3 (by rfl) ⟨275288, by rfl⟩ : syracuseStep 1468205 = 550577) (by norm_num)
theorem B1468229 : Blo 976593 1468229 := bbase (se 4 (by rfl) ⟨137646, by rfl⟩ : syracuseStep 1468229 = 275293) (by norm_num)
theorem B1468253 : Blo 976593 1468253 := bbase (se 3 (by rfl) ⟨275297, by rfl⟩ : syracuseStep 1468253 = 550595) (by norm_num)
theorem B1468277 : Blo 976593 1468277 := bbase (se 5 (by rfl) ⟨68825, by rfl⟩ : syracuseStep 1468277 = 137651) (by norm_num)
theorem B1238905 : Blo 976593 1238905 := bbase (se 2 (by rfl) ⟨464589, by rfl⟩ : syracuseStep 1238905 = 929179) (by norm_num)
theorem B4188037 : Blo 976593 4188037 := bbase (se 4 (by rfl) ⟨392628, by rfl⟩ : syracuseStep 4188037 = 785257) (by norm_num)
theorem B1468301 : Blo 976593 1468301 := bbase (se 3 (by rfl) ⟨275306, by rfl⟩ : syracuseStep 1468301 = 550613) (by norm_num)
theorem B1861517 : Blo 976593 1861517 := bbase (se 3 (by rfl) ⟨349034, by rfl⟩ : syracuseStep 1861517 = 698069) (by norm_num)
theorem B2090909 : Blo 976593 2090909 := bbase (se 3 (by rfl) ⟨392045, by rfl⟩ : syracuseStep 2090909 = 784091) (by norm_num)
theorem B1468325 : Blo 976593 1468325 := bbase (se 4 (by rfl) ⟨137655, by rfl⟩ : syracuseStep 1468325 = 275311) (by norm_num)
theorem B1468349 : Blo 976593 1468349 := bbase (se 3 (by rfl) ⟨275315, by rfl⟩ : syracuseStep 1468349 = 550631) (by norm_num)
theorem B1468373 : Blo 976593 1468373 := bbase (se 7 (by rfl) ⟨17207, by rfl⟩ : syracuseStep 1468373 = 34415) (by norm_num)
theorem B1468397 : Blo 976593 1468397 := bbase (se 3 (by rfl) ⟨275324, by rfl⟩ : syracuseStep 1468397 = 550649) (by norm_num)
theorem B1468421 : Blo 976593 1468421 := bbase (se 4 (by rfl) ⟨137664, by rfl⟩ : syracuseStep 1468421 = 275329) (by norm_num)
theorem B1468445 : Blo 976593 1468445 := bbase (se 3 (by rfl) ⟨275333, by rfl⟩ : syracuseStep 1468445 = 550667) (by norm_num)
theorem B1239077 : Blo 976593 1239077 := bbase (se 4 (by rfl) ⟨116163, by rfl⟩ : syracuseStep 1239077 = 232327) (by norm_num)
theorem B1566773 : Blo 976593 1566773 := bbase (se 5 (by rfl) ⟨73442, by rfl⟩ : syracuseStep 1566773 = 146885) (by norm_num)
theorem B1468469 : Blo 976593 1468469 := bbase (se 5 (by rfl) ⟨68834, by rfl⟩ : syracuseStep 1468469 = 137669) (by norm_num)
theorem B1468493 : Blo 976593 1468493 := bbase (se 3 (by rfl) ⟨275342, by rfl⟩ : syracuseStep 1468493 = 550685) (by norm_num)
theorem B1239133 : Blo 976593 1239133 := bbase (se 3 (by rfl) ⟨232337, by rfl⟩ : syracuseStep 1239133 = 464675) (by norm_num)
theorem B1468517 : Blo 976593 1468517 := bbase (se 4 (by rfl) ⟨137673, by rfl⟩ : syracuseStep 1468517 = 275347) (by norm_num)
theorem B1468541 : Blo 976593 1468541 := bbase (se 3 (by rfl) ⟨275351, by rfl⟩ : syracuseStep 1468541 = 550703) (by norm_num)
theorem B3303557 : Blo 976593 3303557 := bbase (se 4 (by rfl) ⟨309708, by rfl⟩ : syracuseStep 3303557 = 619417) (by norm_num)
theorem B1468565 : Blo 976593 1468565 := bbase (se 6 (by rfl) ⟨34419, by rfl⟩ : syracuseStep 1468565 = 68839) (by norm_num)
theorem B1468589 : Blo 976593 1468589 := bbase (se 3 (by rfl) ⟨275360, by rfl⟩ : syracuseStep 1468589 = 550721) (by norm_num)
theorem B1239229 : Blo 976593 1239229 := bbase (se 3 (by rfl) ⟨232355, by rfl⟩ : syracuseStep 1239229 = 464711) (by norm_num)
theorem B1468613 : Blo 976593 1468613 := bbase (se 4 (by rfl) ⟨137682, by rfl⟩ : syracuseStep 1468613 = 275365) (by norm_num)
theorem B1468637 : Blo 976593 1468637 := bbase (se 3 (by rfl) ⟨275369, by rfl⟩ : syracuseStep 1468637 = 550739) (by norm_num)
theorem B1566965 : Blo 976593 1566965 := bbase (se 5 (by rfl) ⟨73451, by rfl⟩ : syracuseStep 1566965 = 146903) (by norm_num)
theorem B1468661 : Blo 976593 1468661 := bbase (se 5 (by rfl) ⟨68843, by rfl⟩ : syracuseStep 1468661 = 137687) (by norm_num)
theorem B1468685 : Blo 976593 1468685 := bbase (se 3 (by rfl) ⟨275378, by rfl⟩ : syracuseStep 1468685 = 550757) (by norm_num)
theorem B1468709 : Blo 976593 1468709 := bbase (se 4 (by rfl) ⟨137691, by rfl⟩ : syracuseStep 1468709 = 275383) (by norm_num)
theorem B1468733 : Blo 976593 1468733 := bbase (se 3 (by rfl) ⟨275387, by rfl⟩ : syracuseStep 1468733 = 550775) (by norm_num)
theorem B1468757 : Blo 976593 1468757 := bbase (se 10 (by rfl) ⟨2151, by rfl⟩ : syracuseStep 1468757 = 4303) (by norm_num)
theorem B1239401 : Blo 976593 1239401 := bbase (se 2 (by rfl) ⟨464775, by rfl⟩ : syracuseStep 1239401 = 929551) (by norm_num)
theorem B1468781 : Blo 976593 1468781 := bbase (se 3 (by rfl) ⟨275396, by rfl⟩ : syracuseStep 1468781 = 550793) (by norm_num)
theorem B1468805 : Blo 976593 1468805 := bbase (se 4 (by rfl) ⟨137700, by rfl⟩ : syracuseStep 1468805 = 275401) (by norm_num)
theorem B5564821 : Blo 976593 5564821 := bbase (se 6 (by rfl) ⟨130425, by rfl⟩ : syracuseStep 5564821 = 260851) (by norm_num)
theorem B1468829 : Blo 976593 1468829 := bbase (se 3 (by rfl) ⟨275405, by rfl⟩ : syracuseStep 1468829 = 550811) (by norm_num)
theorem B1239457 : Blo 976593 1239457 := bbase (se 2 (by rfl) ⟨464796, by rfl⟩ : syracuseStep 1239457 = 929593) (by norm_num)
theorem B1468853 : Blo 976593 1468853 := bbase (se 5 (by rfl) ⟨68852, by rfl⟩ : syracuseStep 1468853 = 137705) (by norm_num)
theorem B1468877 : Blo 976593 1468877 := bbase (se 3 (by rfl) ⟨275414, by rfl⟩ : syracuseStep 1468877 = 550829) (by norm_num)
theorem B1468901 : Blo 976593 1468901 := bbase (se 4 (by rfl) ⟨137709, by rfl⟩ : syracuseStep 1468901 = 275419) (by norm_num)
theorem B1468925 : Blo 976593 1468925 := bbase (se 3 (by rfl) ⟨275423, by rfl⟩ : syracuseStep 1468925 = 550847) (by norm_num)
theorem B1239553 : Blo 976593 1239553 := bbase (se 2 (by rfl) ⟨464832, by rfl⟩ : syracuseStep 1239553 = 929665) (by norm_num)
theorem B1468949 : Blo 976593 1468949 := bbase (se 6 (by rfl) ⟨34428, by rfl⟩ : syracuseStep 1468949 = 68857) (by norm_num)
theorem B1468973 : Blo 976593 1468973 := bbase (se 3 (by rfl) ⟨275432, by rfl⟩ : syracuseStep 1468973 = 550865) (by norm_num)
theorem B3303989 : Blo 976593 3303989 := bbase (se 5 (by rfl) ⟨154874, by rfl⟩ : syracuseStep 3303989 = 309749) (by norm_num)
theorem B1468997 : Blo 976593 1468997 := bbase (se 4 (by rfl) ⟨137718, by rfl⟩ : syracuseStep 1468997 = 275437) (by norm_num)
theorem B11922005 : Blo 976593 11922005 := bbase (se 8 (by rfl) ⟨69855, by rfl⟩ : syracuseStep 11922005 = 139711) (by norm_num)
theorem B1469021 : Blo 976593 1469021 := bbase (se 3 (by rfl) ⟨275441, by rfl⟩ : syracuseStep 1469021 = 550883) (by norm_num)
theorem B1469045 : Blo 976593 1469045 := bbase (se 5 (by rfl) ⟨68861, by rfl⟩ : syracuseStep 1469045 = 137723) (by norm_num)
theorem B2091653 : Blo 976593 2091653 := bbase (se 4 (by rfl) ⟨196092, by rfl⟩ : syracuseStep 2091653 = 392185) (by norm_num)
theorem B1469069 : Blo 976593 1469069 := bbase (se 3 (by rfl) ⟨275450, by rfl⟩ : syracuseStep 1469069 = 550901) (by norm_num)
theorem B1469093 : Blo 976593 1469093 := bbase (se 4 (by rfl) ⟨137727, by rfl⟩ : syracuseStep 1469093 = 275455) (by norm_num)
theorem B1239725 : Blo 976593 1239725 := bbase (se 3 (by rfl) ⟨232448, by rfl⟩ : syracuseStep 1239725 = 464897) (by norm_num)
theorem B1469117 : Blo 976593 1469117 := bbase (se 3 (by rfl) ⟨275459, by rfl⟩ : syracuseStep 1469117 = 550919) (by norm_num)
theorem B1469141 : Blo 976593 1469141 := bbase (se 7 (by rfl) ⟨17216, by rfl⟩ : syracuseStep 1469141 = 34433) (by norm_num)
theorem B1043165 : Blo 976593 1043165 := bbase (se 3 (by rfl) ⟨195593, by rfl⟩ : syracuseStep 1043165 = 391187) (by norm_num)
theorem B1239781 : Blo 976593 1239781 := bbase (se 4 (by rfl) ⟨116229, by rfl⟩ : syracuseStep 1239781 = 232459) (by norm_num)
theorem B1469165 : Blo 976593 1469165 := bbase (se 3 (by rfl) ⟨275468, by rfl⟩ : syracuseStep 1469165 = 550937) (by norm_num)
theorem B1469189 : Blo 976593 1469189 := bbase (se 4 (by rfl) ⟨137736, by rfl⟩ : syracuseStep 1469189 = 275473) (by norm_num)
theorem B1469213 : Blo 976593 1469213 := bbase (se 3 (by rfl) ⟨275477, by rfl⟩ : syracuseStep 1469213 = 550955) (by norm_num)
theorem B1469237 : Blo 976593 1469237 := bbase (se 5 (by rfl) ⟨68870, by rfl⟩ : syracuseStep 1469237 = 137741) (by norm_num)
theorem B1239877 : Blo 976593 1239877 := bbase (se 4 (by rfl) ⟨116238, by rfl⟩ : syracuseStep 1239877 = 232477) (by norm_num)
theorem B1174349 : Blo 976593 1174349 := bbase (se 3 (by rfl) ⟨220190, by rfl⟩ : syracuseStep 1174349 = 440381) (by norm_num)
theorem B1469261 : Blo 976593 1469261 := bbase (se 3 (by rfl) ⟨275486, by rfl⟩ : syracuseStep 1469261 = 550973) (by norm_num)
theorem B1469285 : Blo 976593 1469285 := bbase (se 4 (by rfl) ⟨137745, by rfl⟩ : syracuseStep 1469285 = 275491) (by norm_num)
theorem B1469309 : Blo 976593 1469309 := bbase (se 3 (by rfl) ⟨275495, by rfl⟩ : syracuseStep 1469309 = 550991) (by norm_num)
theorem B1469333 : Blo 976593 1469333 := bbase (se 6 (by rfl) ⟨34437, by rfl⟩ : syracuseStep 1469333 = 68875) (by norm_num)
theorem B1469357 : Blo 976593 1469357 := bbase (se 3 (by rfl) ⟨275504, by rfl⟩ : syracuseStep 1469357 = 551009) (by norm_num)
theorem B1469381 : Blo 976593 1469381 := bbase (se 4 (by rfl) ⟨137754, by rfl⟩ : syracuseStep 1469381 = 275509) (by norm_num)
theorem B3959765 : Blo 976593 3959765 := bbase (se 7 (by rfl) ⟨46403, by rfl⟩ : syracuseStep 3959765 = 92807) (by norm_num)
theorem B1469405 : Blo 976593 1469405 := bbase (se 3 (by rfl) ⟨275513, by rfl⟩ : syracuseStep 1469405 = 551027) (by norm_num)
theorem B3304421 : Blo 976593 3304421 := bbase (se 4 (by rfl) ⟨309789, by rfl⟩ : syracuseStep 3304421 = 619579) (by norm_num)
theorem B1240049 : Blo 976593 1240049 := bbase (se 2 (by rfl) ⟨465018, by rfl⟩ : syracuseStep 1240049 = 930037) (by norm_num)
theorem B1469429 : Blo 976593 1469429 := bbase (se 5 (by rfl) ⟨68879, by rfl⟩ : syracuseStep 1469429 = 137759) (by norm_num)
theorem B1469453 : Blo 976593 1469453 := bbase (se 3 (by rfl) ⟨275522, by rfl⟩ : syracuseStep 1469453 = 551045) (by norm_num)
theorem B1469477 : Blo 976593 1469477 := bbase (se 4 (by rfl) ⟨137763, by rfl⟩ : syracuseStep 1469477 = 275527) (by norm_num)
theorem B1240105 : Blo 976593 1240105 := bbase (se 2 (by rfl) ⟨465039, by rfl⟩ : syracuseStep 1240105 = 930079) (by norm_num)
theorem B1469501 : Blo 976593 1469501 := bbase (se 3 (by rfl) ⟨275531, by rfl⟩ : syracuseStep 1469501 = 551063) (by norm_num)
theorem B1174609 : Blo 976593 1174609 := bbase (se 2 (by rfl) ⟨440478, by rfl⟩ : syracuseStep 1174609 = 880957) (by norm_num)
theorem B1469525 : Blo 976593 1469525 := bbase (se 8 (by rfl) ⟨8610, by rfl⟩ : syracuseStep 1469525 = 17221) (by norm_num)
theorem B1469549 : Blo 976593 1469549 := bbase (se 3 (by rfl) ⟨275540, by rfl⟩ : syracuseStep 1469549 = 551081) (by norm_num)
theorem B1174657 : Blo 976593 1174657 := bbase (se 2 (by rfl) ⟨440496, by rfl⟩ : syracuseStep 1174657 = 880993) (by norm_num)
theorem B1469573 : Blo 976593 1469573 := bbase (se 4 (by rfl) ⟨137772, by rfl⟩ : syracuseStep 1469573 = 275545) (by norm_num)
theorem B1240201 : Blo 976593 1240201 := bbase (se 2 (by rfl) ⟨465075, by rfl⟩ : syracuseStep 1240201 = 930151) (by norm_num)
theorem B1043609 : Blo 976593 1043609 := bbase (se 2 (by rfl) ⟨391353, by rfl⟩ : syracuseStep 1043609 = 782707) (by norm_num)
theorem B1469597 : Blo 976593 1469597 := bbase (se 3 (by rfl) ⟨275549, by rfl⟩ : syracuseStep 1469597 = 551099) (by norm_num)
theorem B1469621 : Blo 976593 1469621 := bbase (se 5 (by rfl) ⟨68888, by rfl⟩ : syracuseStep 1469621 = 137777) (by norm_num)
theorem B1469645 : Blo 976593 1469645 := bbase (se 3 (by rfl) ⟨275558, by rfl⟩ : syracuseStep 1469645 = 551117) (by norm_num)
theorem B1469669 : Blo 976593 1469669 := bbase (se 4 (by rfl) ⟨137781, by rfl⟩ : syracuseStep 1469669 = 275563) (by norm_num)
theorem B1469693 : Blo 976593 1469693 := bbase (se 3 (by rfl) ⟨275567, by rfl⟩ : syracuseStep 1469693 = 551135) (by norm_num)
theorem B1469717 : Blo 976593 1469717 := bbase (se 6 (by rfl) ⟨34446, by rfl⟩ : syracuseStep 1469717 = 68893) (by norm_num)
theorem B1469741 : Blo 976593 1469741 := bbase (se 3 (by rfl) ⟨275576, by rfl⟩ : syracuseStep 1469741 = 551153) (by norm_num)
theorem B1240373 : Blo 976593 1240373 := bbase (se 5 (by rfl) ⟨58142, by rfl⟩ : syracuseStep 1240373 = 116285) (by norm_num)
theorem B1469765 : Blo 976593 1469765 := bbase (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) (by norm_num)
theorem B1469789 : Blo 976593 1469789 := bbase (se 3 (by rfl) ⟨275585, by rfl⟩ : syracuseStep 1469789 = 551171) (by norm_num)
theorem B1240429 : Blo 976593 1240429 := bbase (se 3 (by rfl) ⟨232580, by rfl⟩ : syracuseStep 1240429 = 465161) (by norm_num)
theorem B2092405 : Blo 976593 2092405 := bbase (se 5 (by rfl) ⟨98081, by rfl⟩ : syracuseStep 2092405 = 196163) (by norm_num)
theorem B1469813 : Blo 976593 1469813 := bbase (se 5 (by rfl) ⟨68897, by rfl⟩ : syracuseStep 1469813 = 137795) (by norm_num)
theorem B1469837 : Blo 976593 1469837 := bbase (se 3 (by rfl) ⟨275594, by rfl⟩ : syracuseStep 1469837 = 551189) (by norm_num)
theorem B1043857 : Blo 976593 1043857 := bbase (se 2 (by rfl) ⟨391446, by rfl⟩ : syracuseStep 1043857 = 782893) (by norm_num)
theorem B7925141 : Blo 976593 7925141 := bbase (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) (by norm_num)
theorem B3304853 : Blo 976593 3304853 := bbase (se 6 (by rfl) ⟨77457, by rfl⟩ : syracuseStep 3304853 = 154915) (by norm_num)
theorem B1469861 : Blo 976593 1469861 := bbase (se 4 (by rfl) ⟨137799, by rfl⟩ : syracuseStep 1469861 = 275599) (by norm_num)
theorem B1469885 : Blo 976593 1469885 := bbase (se 3 (by rfl) ⟨275603, by rfl⟩ : syracuseStep 1469885 = 551207) (by norm_num)
theorem B1240525 : Blo 976593 1240525 := bbase (se 3 (by rfl) ⟨232598, by rfl⟩ : syracuseStep 1240525 = 465197) (by norm_num)
theorem B1469909 : Blo 976593 1469909 := bbase (se 7 (by rfl) ⟨17225, by rfl⟩ : syracuseStep 1469909 = 34451) (by norm_num)
theorem B1469933 : Blo 976593 1469933 := bbase (se 3 (by rfl) ⟨275612, by rfl⟩ : syracuseStep 1469933 = 551225) (by norm_num)
theorem B2092549 : Blo 976593 2092549 := bbase (se 4 (by rfl) ⟨196176, by rfl⟩ : syracuseStep 2092549 = 392353) (by norm_num)
theorem B1469957 : Blo 976593 1469957 := bbase (se 4 (by rfl) ⟨137808, by rfl⟩ : syracuseStep 1469957 = 275617) (by norm_num)
theorem B1469981 : Blo 976593 1469981 := bbase (se 3 (by rfl) ⟨275621, by rfl⟩ : syracuseStep 1469981 = 551243) (by norm_num)
theorem B1470005 : Blo 976593 1470005 := bbase (se 5 (by rfl) ⟨68906, by rfl⟩ : syracuseStep 1470005 = 137813) (by norm_num)
theorem B1470029 : Blo 976593 1470029 := bbase (se 3 (by rfl) ⟨275630, by rfl⟩ : syracuseStep 1470029 = 551261) (by norm_num)
theorem B1470053 : Blo 976593 1470053 := bbase (se 4 (by rfl) ⟨137817, by rfl⟩ : syracuseStep 1470053 = 275635) (by norm_num)
theorem B1240697 : Blo 976593 1240697 := bbase (se 2 (by rfl) ⟨465261, by rfl⟩ : syracuseStep 1240697 = 930523) (by norm_num)
theorem B1470077 : Blo 976593 1470077 := bbase (se 3 (by rfl) ⟨275639, by rfl⟩ : syracuseStep 1470077 = 551279) (by norm_num)
theorem B1470101 : Blo 976593 1470101 := bbase (se 6 (by rfl) ⟨34455, by rfl⟩ : syracuseStep 1470101 = 68911) (by norm_num)
theorem B1568413 : Blo 976593 1568413 := bbase (se 3 (by rfl) ⟨294077, by rfl⟩ : syracuseStep 1568413 = 588155) (by norm_num)
theorem B1470125 : Blo 976593 1470125 := bbase (se 3 (by rfl) ⟨275648, by rfl⟩ : syracuseStep 1470125 = 551297) (by norm_num)
theorem B1240753 : Blo 976593 1240753 := bbase (se 2 (by rfl) ⟨465282, by rfl⟩ : syracuseStep 1240753 = 930565) (by norm_num)
theorem B1470149 : Blo 976593 1470149 := bbase (se 4 (by rfl) ⟨137826, by rfl⟩ : syracuseStep 1470149 = 275653) (by norm_num)
theorem B1470173 : Blo 976593 1470173 := bbase (se 3 (by rfl) ⟨275657, by rfl⟩ : syracuseStep 1470173 = 551315) (by norm_num)
theorem B1470197 : Blo 976593 1470197 := bbase (se 5 (by rfl) ⟨68915, by rfl⟩ : syracuseStep 1470197 = 137831) (by norm_num)
theorem B1470221 : Blo 976593 1470221 := bbase (se 3 (by rfl) ⟨275666, by rfl⟩ : syracuseStep 1470221 = 551333) (by norm_num)
theorem B1240849 : Blo 976593 1240849 := bbase (se 2 (by rfl) ⟨465318, by rfl⟩ : syracuseStep 1240849 = 930637) (by norm_num)
theorem B1175329 : Blo 976593 1175329 := bbase (se 2 (by rfl) ⟨440748, by rfl⟩ : syracuseStep 1175329 = 881497) (by norm_num)
theorem B1470245 : Blo 976593 1470245 := bbase (se 4 (by rfl) ⟨137835, by rfl⟩ : syracuseStep 1470245 = 275671) (by norm_num)
theorem B3141413 : Blo 976593 3141413 := bbase (se 4 (by rfl) ⟨294507, by rfl⟩ : syracuseStep 3141413 = 589015) (by norm_num)
theorem B1470269 : Blo 976593 1470269 := bbase (se 3 (by rfl) ⟨275675, by rfl⟩ : syracuseStep 1470269 = 551351) (by norm_num)
theorem B1044289 : Blo 976593 1044289 := bbase (se 2 (by rfl) ⟨391608, by rfl⟩ : syracuseStep 1044289 = 783217) (by norm_num)
theorem B3305285 : Blo 976593 3305285 := bbase (se 4 (by rfl) ⟨309870, by rfl⟩ : syracuseStep 3305285 = 619741) (by norm_num)
theorem B1470293 : Blo 976593 1470293 := bbase (se 9 (by rfl) ⟨4307, by rfl⟩ : syracuseStep 1470293 = 8615) (by norm_num)
theorem B2649941 : Blo 976593 2649941 := bbase (se 9 (by rfl) ⟨7763, by rfl⟩ : syracuseStep 2649941 = 15527) (by norm_num)
theorem B1470317 : Blo 976593 1470317 := bbase (se 3 (by rfl) ⟨275684, by rfl⟩ : syracuseStep 1470317 = 551369) (by norm_num)
theorem B6352757 : Blo 976593 6352757 := bbase (se 5 (by rfl) ⟨297785, by rfl⟩ : syracuseStep 6352757 = 595571) (by norm_num)
theorem B2092925 : Blo 976593 2092925 := bbase (se 3 (by rfl) ⟨392423, by rfl⟩ : syracuseStep 2092925 = 784847) (by norm_num)
theorem B2977669 : Blo 976593 2977669 := bbase (se 4 (by rfl) ⟨279156, by rfl⟩ : syracuseStep 2977669 = 558313) (by norm_num)
theorem B1470341 : Blo 976593 1470341 := bbase (se 4 (by rfl) ⟨137844, by rfl⟩ : syracuseStep 1470341 = 275689) (by norm_num)
theorem B1044361 : Blo 976593 1044361 := bbase (se 2 (by rfl) ⟨391635, by rfl⟩ : syracuseStep 1044361 = 783271) (by norm_num)
theorem B1470365 : Blo 976593 1470365 := bbase (se 3 (by rfl) ⟨275693, by rfl⟩ : syracuseStep 1470365 = 551387) (by norm_num)
theorem B1470389 : Blo 976593 1470389 := bbase (se 5 (by rfl) ⟨68924, by rfl⟩ : syracuseStep 1470389 = 137849) (by norm_num)
theorem B1241021 : Blo 976593 1241021 := bbase (se 3 (by rfl) ⟨232691, by rfl⟩ : syracuseStep 1241021 = 465383) (by norm_num)
theorem B2781125 : Blo 976593 2781125 := bbase (se 4 (by rfl) ⟨260730, by rfl⟩ : syracuseStep 2781125 = 521461) (by norm_num)
theorem B1470413 : Blo 976593 1470413 := bbase (se 3 (by rfl) ⟨275702, by rfl⟩ : syracuseStep 1470413 = 551405) (by norm_num)
theorem B1470437 : Blo 976593 1470437 := bbase (se 4 (by rfl) ⟨137853, by rfl⟩ : syracuseStep 1470437 = 275707) (by norm_num)
theorem B1470461 : Blo 976593 1470461 := bbase (se 3 (by rfl) ⟨275711, by rfl⟩ : syracuseStep 1470461 = 551423) (by norm_num)
theorem B1470485 : Blo 976593 1470485 := bbase (se 6 (by rfl) ⟨34464, by rfl⟩ : syracuseStep 1470485 = 68929) (by norm_num)
theorem B2977829 : Blo 976593 2977829 := bbase (se 4 (by rfl) ⟨279171, by rfl⟩ : syracuseStep 2977829 = 558343) (by norm_num)
theorem B1470509 : Blo 976593 1470509 := bbase (se 3 (by rfl) ⟨275720, by rfl⟩ : syracuseStep 1470509 = 551441) (by norm_num)
theorem B1470533 : Blo 976593 1470533 := bbase (se 4 (by rfl) ⟨137862, by rfl⟩ : syracuseStep 1470533 = 275725) (by norm_num)
theorem B1470557 : Blo 976593 1470557 := bbase (se 3 (by rfl) ⟨275729, by rfl⟩ : syracuseStep 1470557 = 551459) (by norm_num)
theorem B1470581 : Blo 976593 1470581 := bbase (se 5 (by rfl) ⟨68933, by rfl⟩ : syracuseStep 1470581 = 137867) (by norm_num)
theorem B2781317 : Blo 976593 2781317 := bbase (se 4 (by rfl) ⟨260748, by rfl⟩ : syracuseStep 2781317 = 521497) (by norm_num)
theorem B1470605 : Blo 976593 1470605 := bbase (se 3 (by rfl) ⟨275738, by rfl⟩ : syracuseStep 1470605 = 551477) (by norm_num)
theorem B1470629 : Blo 976593 1470629 := bbase (se 4 (by rfl) ⟨137871, by rfl⟩ : syracuseStep 1470629 = 275743) (by norm_num)
theorem B1470653 : Blo 976593 1470653 := bbase (se 3 (by rfl) ⟨275747, by rfl⟩ : syracuseStep 1470653 = 551495) (by norm_num)
theorem B1241285 : Blo 976593 1241285 := bbase (se 4 (by rfl) ⟨116370, by rfl⟩ : syracuseStep 1241285 = 232741) (by norm_num)
theorem B1470677 : Blo 976593 1470677 := bbase (se 7 (by rfl) ⟨17234, by rfl⟩ : syracuseStep 1470677 = 34469) (by norm_num)
theorem B2093293 : Blo 976593 2093293 := bbase (se 3 (by rfl) ⟨392492, by rfl⟩ : syracuseStep 2093293 = 784985) (by norm_num)
theorem B1470701 : Blo 976593 1470701 := bbase (se 3 (by rfl) ⟨275756, by rfl⟩ : syracuseStep 1470701 = 551513) (by norm_num)
theorem B3305717 : Blo 976593 3305717 := bbase (se 5 (by rfl) ⟨154955, by rfl⟩ : syracuseStep 3305717 = 309911) (by norm_num)
theorem B1044733 : Blo 976593 1044733 := bbase (se 3 (by rfl) ⟨195887, by rfl⟩ : syracuseStep 1044733 = 391775) (by norm_num)
theorem B1470725 : Blo 976593 1470725 := bbase (se 4 (by rfl) ⟨137880, by rfl⟩ : syracuseStep 1470725 = 275761) (by norm_num)
theorem B1470749 : Blo 976593 1470749 := bbase (se 3 (by rfl) ⟨275765, by rfl⟩ : syracuseStep 1470749 = 551531) (by norm_num)
theorem B1470773 : Blo 976593 1470773 := bbase (se 5 (by rfl) ⟨68942, by rfl⟩ : syracuseStep 1470773 = 137885) (by norm_num)
theorem B1470797 : Blo 976593 1470797 := bbase (se 3 (by rfl) ⟨275774, by rfl⟩ : syracuseStep 1470797 = 551549) (by norm_num)
theorem B5566805 : Blo 976593 5566805 := bbase (se 10 (by rfl) ⟨8154, by rfl⟩ : syracuseStep 5566805 = 16309) (by norm_num)
theorem B1470821 : Blo 976593 1470821 := bbase (se 4 (by rfl) ⟨137889, by rfl⟩ : syracuseStep 1470821 = 275779) (by norm_num)
theorem B1470845 : Blo 976593 1470845 := bbase (se 3 (by rfl) ⟨275783, by rfl⟩ : syracuseStep 1470845 = 551567) (by norm_num)
theorem B1470869 : Blo 976593 1470869 := bbase (se 6 (by rfl) ⟨34473, by rfl⟩ : syracuseStep 1470869 = 68947) (by norm_num)
theorem B2355733 : Blo 976593 2355733 := bbase (se 6 (by rfl) ⟨55212, by rfl⟩ : syracuseStep 2355733 = 110425) (by norm_num)
theorem B1045109 : Blo 976593 1045109 := bbase (se 5 (by rfl) ⟨48989, by rfl⟩ : syracuseStep 1045109 = 97979) (by norm_num)
theorem B3306149 : Blo 976593 3306149 := bbase (se 4 (by rfl) ⟨309951, by rfl⟩ : syracuseStep 3306149 = 619903) (by norm_num)
theorem B1045181 : Blo 976593 1045181 := bbase (se 3 (by rfl) ⟨195971, by rfl⟩ : syracuseStep 1045181 = 391943) (by norm_num)
theorem B3764933 : Blo 976593 3764933 := bbase (se 4 (by rfl) ⟨352962, by rfl⟩ : syracuseStep 3764933 = 705925) (by norm_num)
theorem B1176329 : Blo 976593 1176329 := bbase (se 2 (by rfl) ⟨441123, by rfl⟩ : syracuseStep 1176329 = 882247) (by norm_num)
theorem B1766165 : Blo 976593 1766165 := bbase (se 6 (by rfl) ⟨41394, by rfl⟩ : syracuseStep 1766165 = 82789) (by norm_num)
theorem B1176401 : Blo 976593 1176401 := bbase (se 2 (by rfl) ⟨441150, by rfl⟩ : syracuseStep 1176401 = 882301) (by norm_num)
theorem B4944725 : Blo 976593 4944725 := bbase (se 9 (by rfl) ⟨14486, by rfl⟩ : syracuseStep 4944725 = 28973) (by norm_num)
theorem B1045369 : Blo 976593 1045369 := bbase (se 2 (by rfl) ⟨392013, by rfl⟩ : syracuseStep 1045369 = 784027) (by norm_num)
theorem B1569797 : Blo 976593 1569797 := bbase (se 4 (by rfl) ⟨147168, by rfl⟩ : syracuseStep 1569797 = 294337) (by norm_num)
theorem B1045553 : Blo 976593 1045553 := bbase (se 2 (by rfl) ⟨392082, by rfl⟩ : syracuseStep 1045553 = 784165) (by norm_num)
theorem B3306581 : Blo 976593 3306581 := bbase (se 8 (by rfl) ⟨19374, by rfl⟩ : syracuseStep 3306581 = 38749) (by norm_num)
theorem B2782309 : Blo 976593 2782309 := bbase (se 4 (by rfl) ⟨260841, by rfl⟩ : syracuseStep 2782309 = 521683) (by norm_num)
theorem B8909941 : Blo 976593 8909941 := bbase (se 5 (by rfl) ⟨417653, by rfl⟩ : syracuseStep 8909941 = 835307) (by norm_num)
theorem B1176709 : Blo 976593 1176709 := bbase (se 4 (by rfl) ⟨110316, by rfl⟩ : syracuseStep 1176709 = 220633) (by norm_num)
theorem B1569989 : Blo 976593 1569989 := bbase (se 4 (by rfl) ⟨147186, by rfl⟩ : syracuseStep 1569989 = 294373) (by norm_num)
theorem B7042261 : Blo 976593 7042261 := bbase (se 7 (by rfl) ⟨82526, by rfl⟩ : syracuseStep 7042261 = 165053) (by norm_num)
theorem B1176877 : Blo 976593 1176877 := bbase (se 3 (by rfl) ⟨220664, by rfl⟩ : syracuseStep 1176877 = 441329) (by norm_num)
theorem B1176925 : Blo 976593 1176925 := bbase (se 3 (by rfl) ⟨220673, by rfl⟩ : syracuseStep 1176925 = 441347) (by norm_num)
theorem B1177021 : Blo 976593 1177021 := bbase (se 3 (by rfl) ⟨220691, by rfl⟩ : syracuseStep 1177021 = 441383) (by norm_num)
theorem B7042517 : Blo 976593 7042517 := bbase (se 7 (by rfl) ⟨82529, by rfl⟩ : syracuseStep 7042517 = 165059) (by norm_num)
theorem B1766909 : Blo 976593 1766909 := bbase (se 3 (by rfl) ⟨331295, by rfl⟩ : syracuseStep 1766909 = 662591) (by norm_num)
theorem B3307013 : Blo 976593 3307013 := bbase (se 4 (by rfl) ⟨310032, by rfl⟩ : syracuseStep 3307013 = 620065) (by norm_num)
theorem B5961397 : Blo 976593 5961397 := bbase (se 5 (by rfl) ⟨279440, by rfl⟩ : syracuseStep 5961397 = 558881) (by norm_num)
theorem B1046305 : Blo 976593 1046305 := bbase (se 2 (by rfl) ⟨392364, by rfl⟩ : syracuseStep 1046305 = 784729) (by norm_num)
theorem B1046377 : Blo 976593 1046377 := bbase (se 2 (by rfl) ⟨392391, by rfl⟩ : syracuseStep 1046377 = 784783) (by norm_num)
theorem B3307445 : Blo 976593 3307445 := bbase (se 5 (by rfl) ⟨155036, by rfl⟩ : syracuseStep 3307445 = 310073) (by norm_num)
theorem B1177597 : Blo 976593 1177597 := bbase (se 3 (by rfl) ⟨220799, by rfl⟩ : syracuseStep 1177597 = 441599) (by norm_num)
theorem B1046557 : Blo 976593 1046557 := bbase (se 3 (by rfl) ⟨196229, by rfl⟩ : syracuseStep 1046557 = 392459) (by norm_num)
theorem B4946021 : Blo 976593 4946021 := bbase (se 4 (by rfl) ⟨463689, by rfl⟩ : syracuseStep 4946021 = 927379) (by norm_num)
theorem B4028549 : Blo 976593 4028549 := bbase (se 4 (by rfl) ⟨377676, by rfl⟩ : syracuseStep 4028549 = 755353) (by norm_num)
theorem B2783413 : Blo 976593 2783413 := bbase (se 5 (by rfl) ⟨130472, by rfl⟩ : syracuseStep 2783413 = 260945) (by norm_num)
theorem B3307877 : Blo 976593 3307877 := bbase (se 4 (by rfl) ⟨310113, by rfl⟩ : syracuseStep 3307877 = 620227) (by norm_num)
theorem B1047001 : Blo 976593 1047001 := bbase (se 2 (by rfl) ⟨392625, by rfl⟩ : syracuseStep 1047001 = 785251) (by norm_num)
theorem B5569013 : Blo 976593 5569013 := bbase (se 5 (by rfl) ⟨261047, by rfl⟩ : syracuseStep 5569013 = 522095) (by norm_num)
theorem B1047125 : Blo 976593 1047125 := bbase (se 8 (by rfl) ⟨6135, by rfl⟩ : syracuseStep 1047125 = 12271) (by norm_num)
theorem B3308309 : Blo 976593 3308309 := bbase (se 6 (by rfl) ⟨77538, by rfl⟩ : syracuseStep 3308309 = 155077) (by norm_num)
theorem B3767093 : Blo 976593 3767093 := bbase (se 5 (by rfl) ⟨176582, by rfl⟩ : syracuseStep 3767093 = 353165) (by norm_num)
theorem B4455269 : Blo 976593 4455269 := bbase (se 4 (by rfl) ⟨417681, by rfl⟩ : syracuseStep 4455269 = 835363) (by norm_num)
theorem B3308741 : Blo 976593 3308741 := bbase (se 4 (by rfl) ⟨310194, by rfl⟩ : syracuseStep 3308741 = 620389) (by norm_num)
theorem B3177701 : Blo 976593 3177701 := bbase (se 4 (by rfl) ⟨297909, by rfl⟩ : syracuseStep 3177701 = 595819) (by norm_num)
theorem B4947317 : Blo 976593 4947317 := bbase (se 5 (by rfl) ⟨231905, by rfl⟩ : syracuseStep 4947317 = 463811) (by norm_num)
theorem B3309173 : Blo 976593 3309173 := bbase (se 5 (by rfl) ⟨155117, by rfl⟩ : syracuseStep 3309173 = 310235) (by norm_num)
theorem B2784917 : Blo 976593 2784917 := bbase (se 6 (by rfl) ⟨65271, by rfl⟩ : syracuseStep 2784917 = 130543) (by norm_num)
theorem B2981573 : Blo 976593 2981573 := bbase (se 4 (by rfl) ⟨279522, by rfl⟩ : syracuseStep 2981573 = 559045) (by norm_num)
theorem B7438229 : Blo 976593 7438229 := bbase (se 6 (by rfl) ⟨174333, by rfl⟩ : syracuseStep 7438229 = 348667) (by norm_num)
theorem B4456739 : Blo 976593 4456739 := bstep (se 1 (by rfl) ⟨3342554, by rfl⟩ : syracuseStep 4456739 = 6685109) B6685109
theorem B4948451 : Blo 976593 4948451 := bstep (se 1 (by rfl) ⟨3711338, by rfl⟩ : syracuseStep 4948451 = 7422677) B7422677
theorem B3310093 : Blo 976593 3310093 := bstep (se 3 (by rfl) ⟨620642, by rfl⟩ : syracuseStep 3310093 = 1241285) B1241285
theorem B2786147 : Blo 976593 2786147 := bstep (se 1 (by rfl) ⟨2089610, by rfl⟩ : syracuseStep 2786147 = 4179221) B4179221
theorem B1115203 : Blo 976593 1115203 := bstep (se 1 (by rfl) ⟨836402, by rfl⟩ : syracuseStep 1115203 = 1672805) B1672805
theorem B4949261 : Blo 976593 4949261 := bstep (se 3 (by rfl) ⟨927986, by rfl⟩ : syracuseStep 4949261 = 1855973) B1855973
theorem B1410385 : Blo 976593 1410385 := bstep (se 2 (by rfl) ⟨528894, by rfl⟩ : syracuseStep 1410385 = 1057789) B1057789
theorem B10028485 : Blo 976593 10028485 := bstep (se 4 (by rfl) ⟨940170, by rfl⟩ : syracuseStep 10028485 = 1880341) B1880341
theorem B7046669 : Blo 976593 7046669 := bstep (se 3 (by rfl) ⟨1321250, by rfl⟩ : syracuseStep 7046669 = 2642501) B2642501
theorem B6260273 : Blo 976593 6260273 := bstep (se 2 (by rfl) ⟨2347602, by rfl⟩ : syracuseStep 6260273 = 4695205) B4695205
theorem B2786957 : Blo 976593 2786957 := bstep (se 3 (by rfl) ⟨522554, by rfl⟩ : syracuseStep 2786957 = 1045109) B1045109
theorem B1672915 : Blo 976593 1672915 := bstep (se 1 (by rfl) ⟨1254686, by rfl⟩ : syracuseStep 1672915 = 2509373) B2509373
theorem B1410833 : Blo 976593 1410833 := bstep (se 2 (by rfl) ⟨529062, by rfl⟩ : syracuseStep 1410833 = 1058125) B1058125
theorem B2787149 : Blo 976593 2787149 := bstep (se 3 (by rfl) ⟨522590, by rfl⟩ : syracuseStep 2787149 = 1045181) B1045181
theorem B2197457 : Blo 976593 2197457 := bstep (se 2 (by rfl) ⟨824046, by rfl⟩ : syracuseStep 2197457 = 1648093) B1648093
theorem B2197475 : Blo 976593 2197475 := bstep (se 1 (by rfl) ⟨1648106, by rfl⟩ : syracuseStep 2197475 = 3296213) B3296213
theorem B6260813 : Blo 976593 6260813 := bstep (se 3 (by rfl) ⟨1173902, by rfl⟩ : syracuseStep 6260813 = 2347805) B2347805
theorem B3770509 : Blo 976593 3770509 := bstep (se 3 (by rfl) ⟨706970, by rfl⟩ : syracuseStep 3770509 = 1413941) B1413941
theorem B2197745 : Blo 976593 2197745 := bstep (se 2 (by rfl) ⟨824154, by rfl⟩ : syracuseStep 2197745 = 1648309) B1648309
theorem B2197763 : Blo 976593 2197763 := bstep (se 1 (by rfl) ⟨1648322, by rfl⟩ : syracuseStep 2197763 = 3296645) B3296645
theorem B11143493 : Blo 976593 11143493 := bstep (se 4 (by rfl) ⟨1044702, by rfl⟩ : syracuseStep 11143493 = 2089405) B2089405
theorem B2230705 : Blo 976593 2230705 := bstep (se 2 (by rfl) ⟨836514, by rfl⟩ : syracuseStep 2230705 = 1673029) B1673029
theorem B5573069 : Blo 976593 5573069 := bstep (se 3 (by rfl) ⟨1044950, by rfl⟩ : syracuseStep 5573069 = 2089901) B2089901
theorem B2198033 : Blo 976593 2198033 := bstep (se 2 (by rfl) ⟨824262, by rfl⟩ : syracuseStep 2198033 = 1648525) B1648525
theorem B2198051 : Blo 976593 2198051 := bstep (se 1 (by rfl) ⟨1648538, by rfl⟩ : syracuseStep 2198051 = 3297077) B3297077
theorem B3181133 : Blo 976593 3181133 := bstep (se 3 (by rfl) ⟨596462, by rfl⟩ : syracuseStep 3181133 = 1192925) B1192925
theorem B1673921 : Blo 976593 1673921 := bstep (se 2 (by rfl) ⟨627720, by rfl⟩ : syracuseStep 1673921 = 1255441) B1255441
theorem B2788141 : Blo 976593 2788141 := bstep (se 3 (by rfl) ⟨522776, by rfl⟩ : syracuseStep 2788141 = 1045553) B1045553
theorem B2198321 : Blo 976593 2198321 := bstep (se 2 (by rfl) ⟨824370, by rfl⟩ : syracuseStep 2198321 = 1648741) B1648741
theorem B2198339 : Blo 976593 2198339 := bstep (se 1 (by rfl) ⟨1648754, by rfl⟩ : syracuseStep 2198339 = 3297509) B3297509
theorem B1411907 : Blo 976593 1411907 := bstep (se 1 (by rfl) ⟨1058930, by rfl⟩ : syracuseStep 1411907 = 2117861) B2117861
theorem B3345293 : Blo 976593 3345293 := bstep (se 3 (by rfl) ⟨627242, by rfl⟩ : syracuseStep 3345293 = 1254485) B1254485
theorem B3345457 : Blo 976593 3345457 := bstep (se 2 (by rfl) ⟨1254546, by rfl⟩ : syracuseStep 3345457 = 2509093) B2509093
theorem B2231363 : Blo 976593 2231363 := bstep (se 1 (by rfl) ⟨1673522, by rfl⟩ : syracuseStep 2231363 = 3347045) B3347045
theorem B2198609 : Blo 976593 2198609 := bstep (se 2 (by rfl) ⟨824478, by rfl⟩ : syracuseStep 2198609 = 1648957) B1648957
theorem B2198627 : Blo 976593 2198627 := bstep (se 1 (by rfl) ⟨1648970, by rfl⟩ : syracuseStep 2198627 = 3297941) B3297941
theorem B3968099 : Blo 976593 3968099 := bstep (se 1 (by rfl) ⟨2976074, by rfl⟩ : syracuseStep 3968099 = 5952149) B5952149
theorem B2198897 : Blo 976593 2198897 := bstep (se 2 (by rfl) ⟨824586, by rfl⟩ : syracuseStep 2198897 = 1649173) B1649173
theorem B2198915 : Blo 976593 2198915 := bstep (se 1 (by rfl) ⟨1649186, by rfl⟩ : syracuseStep 2198915 = 3298373) B3298373
theorem B2199185 : Blo 976593 2199185 := bstep (se 2 (by rfl) ⟨824694, by rfl⟩ : syracuseStep 2199185 = 1649389) B1649389
theorem B2199203 : Blo 976593 2199203 := bstep (se 1 (by rfl) ⟨1649402, by rfl⟩ : syracuseStep 2199203 = 3298805) B3298805
theorem B7442117 : Blo 976593 7442117 := bstep (se 4 (by rfl) ⟨697698, by rfl⟩ : syracuseStep 7442117 = 1395397) B1395397
theorem B2199473 : Blo 976593 2199473 := bstep (se 2 (by rfl) ⟨824802, by rfl⟩ : syracuseStep 2199473 = 1649605) B1649605
theorem B2199491 : Blo 976593 2199491 := bstep (se 1 (by rfl) ⟨1649618, by rfl⟩ : syracuseStep 2199491 = 3299237) B3299237
theorem B15044579 : Blo 976593 15044579 := bstep (se 1 (by rfl) ⟨11283434, by rfl⟩ : syracuseStep 15044579 = 22566869) B22566869
theorem B2232305 : Blo 976593 2232305 := bstep (se 2 (by rfl) ⟨837114, by rfl⟩ : syracuseStep 2232305 = 1674229) B1674229
theorem B2822221 : Blo 976593 2822221 := bstep (se 3 (by rfl) ⟨529166, by rfl⟩ : syracuseStep 2822221 = 1058333) B1058333
theorem B4952177 : Blo 976593 4952177 := bstep (se 2 (by rfl) ⟨1857066, by rfl⟩ : syracuseStep 4952177 = 3714133) B3714133
theorem B2199761 : Blo 976593 2199761 := bstep (se 2 (by rfl) ⟨824910, by rfl⟩ : syracuseStep 2199761 = 1649821) B1649821
theorem B2199779 : Blo 976593 2199779 := bstep (se 1 (by rfl) ⟨1649834, by rfl⟩ : syracuseStep 2199779 = 3299669) B3299669
theorem B14127473 : Blo 976593 14127473 := bstep (se 2 (by rfl) ⟨5297802, by rfl⟩ : syracuseStep 14127473 = 10595605) B10595605
theorem B2200049 : Blo 976593 2200049 := bstep (se 2 (by rfl) ⟨825018, by rfl⟩ : syracuseStep 2200049 = 1650037) B1650037
theorem B2789873 : Blo 976593 2789873 := bstep (se 2 (by rfl) ⟨1046202, by rfl⟩ : syracuseStep 2789873 = 2092405) B2092405
theorem B2200067 : Blo 976593 2200067 := bstep (se 1 (by rfl) ⟨1650050, by rfl⟩ : syracuseStep 2200067 = 3300101) B3300101
theorem B30511669 : Blo 976593 30511669 := bstep (se 5 (by rfl) ⟨1430234, by rfl⟩ : syracuseStep 30511669 = 2860469) B2860469
theorem B5575301 : Blo 976593 5575301 := bstep (se 4 (by rfl) ⟨522684, by rfl⟩ : syracuseStep 5575301 = 1045369) B1045369
theorem B2790065 : Blo 976593 2790065 := bstep (se 2 (by rfl) ⟨1046274, by rfl⟩ : syracuseStep 2790065 = 2092549) B2092549
theorem B2200337 : Blo 976593 2200337 := bstep (se 2 (by rfl) ⟨825126, by rfl⟩ : syracuseStep 2200337 = 1650253) B1650253
theorem B2200355 : Blo 976593 2200355 := bstep (se 1 (by rfl) ⟨1650266, by rfl⟩ : syracuseStep 2200355 = 3300533) B3300533
theorem B2200625 : Blo 976593 2200625 := bstep (se 2 (by rfl) ⟨825234, by rfl⟩ : syracuseStep 2200625 = 1650469) B1650469
theorem B2200643 : Blo 976593 2200643 := bstep (se 1 (by rfl) ⟨1650482, by rfl⟩ : syracuseStep 2200643 = 3300965) B3300965
theorem B2266211 : Blo 976593 2266211 := bstep (se 1 (by rfl) ⟨1699658, by rfl⟩ : syracuseStep 2266211 = 3399317) B3399317
theorem B3970225 : Blo 976593 3970225 := bstep (se 2 (by rfl) ⟨1488834, by rfl⟩ : syracuseStep 3970225 = 2977669) B2977669
theorem B6264013 : Blo 976593 6264013 := bstep (se 3 (by rfl) ⟨1174502, by rfl⟩ : syracuseStep 6264013 = 2349005) B2349005
theorem B5575985 : Blo 976593 5575985 := bstep (se 2 (by rfl) ⟨2090994, by rfl⟩ : syracuseStep 5575985 = 4181989) B4181989
theorem B2200913 : Blo 976593 2200913 := bstep (se 2 (by rfl) ⟨825342, by rfl⟩ : syracuseStep 2200913 = 1650685) B1650685
theorem B2200931 : Blo 976593 2200931 := bstep (se 1 (by rfl) ⟨1650698, by rfl⟩ : syracuseStep 2200931 = 3301397) B3301397
theorem B3708301 : Blo 976593 3708301 := bstep (se 3 (by rfl) ⟨695306, by rfl⟩ : syracuseStep 3708301 = 1390613) B1390613
theorem B4953635 : Blo 976593 4953635 := bstep (se 1 (by rfl) ⟨3715226, by rfl⟩ : syracuseStep 4953635 = 7430453) B7430453
theorem B2233955 : Blo 976593 2233955 := bstep (se 1 (by rfl) ⟨1675466, by rfl⟩ : syracuseStep 2233955 = 3350933) B3350933
theorem B2201201 : Blo 976593 2201201 := bstep (se 2 (by rfl) ⟨825450, by rfl⟩ : syracuseStep 2201201 = 1650901) B1650901
theorem B2201219 : Blo 976593 2201219 := bstep (se 1 (by rfl) ⟨1650914, by rfl⟩ : syracuseStep 2201219 = 3301829) B3301829
theorem B2791057 : Blo 976593 2791057 := bstep (se 2 (by rfl) ⟨1046646, by rfl⟩ : syracuseStep 2791057 = 2093293) B2093293
theorem B2201489 : Blo 976593 2201489 := bstep (se 2 (by rfl) ⟨825558, by rfl⟩ : syracuseStep 2201489 = 1651117) B1651117
theorem B2201507 : Blo 976593 2201507 := bstep (se 1 (by rfl) ⟨1651130, by rfl⟩ : syracuseStep 2201507 = 3302261) B3302261
theorem B2791331 : Blo 976593 2791331 := bstep (se 1 (by rfl) ⟨2093498, by rfl⟩ : syracuseStep 2791331 = 4186997) B4186997
theorem B2791523 : Blo 976593 2791523 := bstep (se 1 (by rfl) ⟨2093642, by rfl⟩ : syracuseStep 2791523 = 4187285) B4187285
theorem B3709091 : Blo 976593 3709091 := bstep (se 1 (by rfl) ⟨2781818, by rfl⟩ : syracuseStep 3709091 = 5563637) B5563637
theorem B2201777 : Blo 976593 2201777 := bstep (se 2 (by rfl) ⟨825666, by rfl⟩ : syracuseStep 2201777 = 1651333) B1651333
theorem B2201795 : Blo 976593 2201795 := bstep (se 1 (by rfl) ⟨1651346, by rfl⟩ : syracuseStep 2201795 = 3302693) B3302693
theorem B4954445 : Blo 976593 4954445 := bstep (se 3 (by rfl) ⟨928958, by rfl⟩ : syracuseStep 4954445 = 1857917) B1857917
theorem B2824579 : Blo 976593 2824579 := bstep (se 1 (by rfl) ⟨2118434, by rfl⟩ : syracuseStep 2824579 = 4236869) B4236869
theorem B2202065 : Blo 976593 2202065 := bstep (se 2 (by rfl) ⟨825774, by rfl⟩ : syracuseStep 2202065 = 1651549) B1651549
theorem B2202083 : Blo 976593 2202083 := bstep (se 1 (by rfl) ⟨1651562, by rfl⟩ : syracuseStep 2202083 = 3303125) B3303125
theorem B5577443 : Blo 976593 5577443 := bstep (se 1 (by rfl) ⟨4183082, by rfl⟩ : syracuseStep 5577443 = 8366165) B8366165
theorem B2202353 : Blo 976593 2202353 := bstep (se 2 (by rfl) ⟨825882, by rfl⟩ : syracuseStep 2202353 = 1651765) B1651765
theorem B2202371 : Blo 976593 2202371 := bstep (se 1 (by rfl) ⟨1651778, by rfl⟩ : syracuseStep 2202371 = 3303557) B3303557
theorem B3709745 : Blo 976593 3709745 := bstep (se 2 (by rfl) ⟨1391154, by rfl⟩ : syracuseStep 3709745 = 2782309) B2782309
theorem B2792333 : Blo 976593 2792333 := bstep (se 3 (by rfl) ⟨523562, by rfl⟩ : syracuseStep 2792333 = 1047125) B1047125
theorem B2202641 : Blo 976593 2202641 := bstep (se 2 (by rfl) ⟨825990, by rfl⟩ : syracuseStep 2202641 = 1651981) B1651981
theorem B2202659 : Blo 976593 2202659 := bstep (se 1 (by rfl) ⟨1651994, by rfl⟩ : syracuseStep 2202659 = 3303989) B3303989
theorem B6036515 : Blo 976593 6036515 := bstep (se 1 (by rfl) ⟨4527386, by rfl⟩ : syracuseStep 6036515 = 9054773) B9054773
theorem B2825293 : Blo 976593 2825293 := bstep (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) B1059485
theorem B2202929 : Blo 976593 2202929 := bstep (se 2 (by rfl) ⟨826098, by rfl⟩ : syracuseStep 2202929 = 1652197) B1652197
theorem B2202947 : Blo 976593 2202947 := bstep (se 1 (by rfl) ⟨1652210, by rfl⟩ : syracuseStep 2202947 = 3304421) B3304421
theorem B2203217 : Blo 976593 2203217 := bstep (se 2 (by rfl) ⟨826206, by rfl⟩ : syracuseStep 2203217 = 1652413) B1652413
theorem B5283427 : Blo 976593 5283427 := bstep (se 1 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 5283427 = 7925141) B7925141
theorem B2203235 : Blo 976593 2203235 := bstep (se 1 (by rfl) ⟨1652426, by rfl⟩ : syracuseStep 2203235 = 3304853) B3304853
theorem B2825873 : Blo 976593 2825873 := bstep (se 2 (by rfl) ⟨1059702, by rfl⟩ : syracuseStep 2825873 = 2119405) B2119405
theorem B2203505 : Blo 976593 2203505 := bstep (se 2 (by rfl) ⟨826314, by rfl⟩ : syracuseStep 2203505 = 1652629) B1652629
theorem B2203523 : Blo 976593 2203523 := bstep (se 1 (by rfl) ⟨1652642, by rfl⟩ : syracuseStep 2203523 = 3305285) B3305285
theorem B4235171 : Blo 976593 4235171 := bstep (se 1 (by rfl) ⟨3176378, by rfl⟩ : syracuseStep 4235171 = 6352757) B6352757
theorem B5644237 : Blo 976593 5644237 := bstep (se 3 (by rfl) ⟨1058294, by rfl⟩ : syracuseStep 5644237 = 2116589) B2116589
theorem B2826193 : Blo 976593 2826193 := bstep (se 2 (by rfl) ⟨1059822, by rfl⟩ : syracuseStep 2826193 = 2119645) B2119645
theorem B11149325 : Blo 976593 11149325 := bstep (se 3 (by rfl) ⟨2090498, by rfl⟩ : syracuseStep 11149325 = 4180997) B4180997
theorem B2203793 : Blo 976593 2203793 := bstep (se 2 (by rfl) ⟨826422, by rfl⟩ : syracuseStep 2203793 = 1652845) B1652845
theorem B2203811 : Blo 976593 2203811 := bstep (se 1 (by rfl) ⟨1652858, by rfl⟩ : syracuseStep 2203811 = 3305717) B3305717
theorem B3711203 : Blo 976593 3711203 := bstep (se 1 (by rfl) ⟨2783402, by rfl⟩ : syracuseStep 3711203 = 5566805) B5566805
theorem B3350765 : Blo 976593 3350765 := bstep (se 3 (by rfl) ⟨628268, by rfl⟩ : syracuseStep 3350765 = 1256537) B1256537
theorem B3711217 : Blo 976593 3711217 := bstep (se 2 (by rfl) ⟨1391706, by rfl⟩ : syracuseStep 3711217 = 2783413) B2783413
theorem B2204081 : Blo 976593 2204081 := bstep (se 2 (by rfl) ⟨826530, by rfl⟩ : syracuseStep 2204081 = 1653061) B1653061
theorem B2204099 : Blo 976593 2204099 := bstep (se 1 (by rfl) ⟨1653074, by rfl⟩ : syracuseStep 2204099 = 3306149) B3306149
theorem B4694705 : Blo 976593 4694705 := bstep (se 2 (by rfl) ⟨1760514, by rfl⟩ : syracuseStep 4694705 = 3521029) B3521029
theorem B2204369 : Blo 976593 2204369 := bstep (se 2 (by rfl) ⟨826638, by rfl⟩ : syracuseStep 2204369 = 1653277) B1653277
theorem B2204387 : Blo 976593 2204387 := bstep (se 1 (by rfl) ⟨1653290, by rfl⟩ : syracuseStep 2204387 = 3306581) B3306581
theorem B4694897 : Blo 976593 4694897 := bstep (se 2 (by rfl) ⟨1760586, by rfl⟩ : syracuseStep 4694897 = 3521173) B3521173
theorem B4695011 : Blo 976593 4695011 := bstep (se 1 (by rfl) ⟨3521258, by rfl⟩ : syracuseStep 4695011 = 7042517) B7042517
theorem B2204657 : Blo 976593 2204657 := bstep (se 2 (by rfl) ⟨826746, by rfl⟩ : syracuseStep 2204657 = 1653493) B1653493
theorem B2204675 : Blo 976593 2204675 := bstep (se 1 (by rfl) ⟨1653506, by rfl⟩ : syracuseStep 2204675 = 3307013) B3307013
theorem B1319953 : Blo 976593 1319953 := bstep (se 2 (by rfl) ⟨494982, by rfl⟩ : syracuseStep 1319953 = 989965) B989965
theorem B4957361 : Blo 976593 4957361 := bstep (se 2 (by rfl) ⟨1859010, by rfl⟩ : syracuseStep 4957361 = 3718021) B3718021
theorem B2204945 : Blo 976593 2204945 := bstep (se 2 (by rfl) ⟨826854, by rfl⟩ : syracuseStep 2204945 = 1653709) B1653709
theorem B2204963 : Blo 976593 2204963 := bstep (se 1 (by rfl) ⟨1653722, by rfl⟩ : syracuseStep 2204963 = 3307445) B3307445
theorem B1648019 : Blo 976593 1648019 := bstep (se 1 (by rfl) ⟨1236014, by rfl⟩ : syracuseStep 1648019 = 2472029) B2472029
theorem B6038981 : Blo 976593 6038981 := bstep (se 4 (by rfl) ⟨566154, by rfl⟩ : syracuseStep 6038981 = 1132309) B1132309
theorem B6268421 : Blo 976593 6268421 := bstep (se 4 (by rfl) ⟨587664, by rfl⟩ : syracuseStep 6268421 = 1175329) B1175329
theorem B1648147 : Blo 976593 1648147 := bstep (se 1 (by rfl) ⟨1236110, by rfl⟩ : syracuseStep 1648147 = 2472221) B2472221
theorem B2205233 : Blo 976593 2205233 := bstep (se 2 (by rfl) ⟨826962, by rfl⟩ : syracuseStep 2205233 = 1653925) B1653925
theorem B2205251 : Blo 976593 2205251 := bstep (se 1 (by rfl) ⟨1653938, by rfl⟩ : syracuseStep 2205251 = 3307877) B3307877
theorem B1648289 : Blo 976593 1648289 := bstep (se 2 (by rfl) ⟨618108, by rfl⟩ : syracuseStep 1648289 = 1236217) B1236217
theorem B3712675 : Blo 976593 3712675 := bstep (se 1 (by rfl) ⟨2784506, by rfl⟩ : syracuseStep 3712675 = 5569013) B5569013
theorem B1648417 : Blo 976593 1648417 := bstep (se 2 (by rfl) ⟨618156, by rfl⟩ : syracuseStep 1648417 = 1236313) B1236313
theorem B1648451 : Blo 976593 1648451 := bstep (se 1 (by rfl) ⟨1236338, by rfl⟩ : syracuseStep 1648451 = 2472677) B2472677
theorem B2205521 : Blo 976593 2205521 := bstep (se 2 (by rfl) ⟨827070, by rfl⟩ : syracuseStep 2205521 = 1654141) B1654141
theorem B2205539 : Blo 976593 2205539 := bstep (se 1 (by rfl) ⟨1654154, by rfl⟩ : syracuseStep 2205539 = 3308309) B3308309
theorem B5580677 : Blo 976593 5580677 := bstep (se 4 (by rfl) ⟨523188, by rfl⟩ : syracuseStep 5580677 = 1046377) B1046377
theorem B1648579 : Blo 976593 1648579 := bstep (se 1 (by rfl) ⟨1236434, by rfl⟩ : syracuseStep 1648579 = 2472869) B2472869
theorem B21473333 : Blo 976593 21473333 := bstep (se 5 (by rfl) ⟨1006562, by rfl⟩ : syracuseStep 21473333 = 2013125) B2013125
theorem B1648721 : Blo 976593 1648721 := bstep (se 2 (by rfl) ⟨618270, by rfl⟩ : syracuseStep 1648721 = 1236541) B1236541
theorem B2205809 : Blo 976593 2205809 := bstep (se 2 (by rfl) ⟨827178, by rfl⟩ : syracuseStep 2205809 = 1654357) B1654357
theorem B2205827 : Blo 976593 2205827 := bstep (se 1 (by rfl) ⟨1654370, by rfl⟩ : syracuseStep 2205827 = 3308741) B3308741
theorem B1648849 : Blo 976593 1648849 := bstep (se 2 (by rfl) ⟨618318, by rfl⟩ : syracuseStep 1648849 = 1236637) B1236637
theorem B1648883 : Blo 976593 1648883 := bstep (se 1 (by rfl) ⟨1236662, by rfl⟩ : syracuseStep 1648883 = 2473325) B2473325
theorem B1321219 : Blo 976593 1321219 := bstep (se 1 (by rfl) ⟨990914, by rfl⟩ : syracuseStep 1321219 = 1981829) B1981829
theorem B5581133 : Blo 976593 5581133 := bstep (se 3 (by rfl) ⟨1046462, by rfl⟩ : syracuseStep 5581133 = 2092925) B2092925
theorem B1649011 : Blo 976593 1649011 := bstep (se 1 (by rfl) ⟨1236758, by rfl⟩ : syracuseStep 1649011 = 2473517) B2473517
theorem B2206097 : Blo 976593 2206097 := bstep (se 2 (by rfl) ⟨827286, by rfl⟩ : syracuseStep 2206097 = 1654573) B1654573
theorem B2206115 : Blo 976593 2206115 := bstep (se 1 (by rfl) ⟨1654586, by rfl⟩ : syracuseStep 2206115 = 3309173) B3309173
theorem B1649153 : Blo 976593 1649153 := bstep (se 2 (by rfl) ⟨618432, by rfl⟩ : syracuseStep 1649153 = 1236865) B1236865
theorem B4958819 : Blo 976593 4958819 := bstep (se 1 (by rfl) ⟨3719114, by rfl⟩ : syracuseStep 4958819 = 7438229) B7438229
theorem B1649281 : Blo 976593 1649281 := bstep (se 2 (by rfl) ⟨618480, by rfl⟩ : syracuseStep 1649281 = 1236961) B1236961
theorem B1649315 : Blo 976593 1649315 := bstep (se 1 (by rfl) ⟨1236986, by rfl⟩ : syracuseStep 1649315 = 2473973) B2473973
theorem B1649443 : Blo 976593 1649443 := bstep (se 1 (by rfl) ⟨1237082, by rfl⟩ : syracuseStep 1649443 = 2474165) B2474165
theorem B11152241 : Blo 976593 11152241 := bstep (se 2 (by rfl) ⟨4182090, by rfl⟩ : syracuseStep 11152241 = 8364181) B8364181
theorem B1649585 : Blo 976593 1649585 := bstep (se 2 (by rfl) ⟨618594, by rfl⟩ : syracuseStep 1649585 = 1237189) B1237189
theorem B5352419 : Blo 976593 5352419 := bstep (se 1 (by rfl) ⟨4014314, by rfl⟩ : syracuseStep 5352419 = 8028629) B8028629
theorem B7416845 : Blo 976593 7416845 := bstep (se 3 (by rfl) ⟨1390658, by rfl⟩ : syracuseStep 7416845 = 2781317) B2781317
theorem B1649713 : Blo 976593 1649713 := bstep (se 2 (by rfl) ⟨618642, by rfl⟩ : syracuseStep 1649713 = 1237285) B1237285
theorem B1649747 : Blo 976593 1649747 := bstep (se 1 (by rfl) ⟨1237310, by rfl⟩ : syracuseStep 1649747 = 2474621) B2474621
theorem B1649875 : Blo 976593 1649875 := bstep (se 1 (by rfl) ⟨1237406, by rfl⟩ : syracuseStep 1649875 = 2474813) B2474813
theorem B1650017 : Blo 976593 1650017 := bstep (se 2 (by rfl) ⟨618756, by rfl⟩ : syracuseStep 1650017 = 1237513) B1237513
theorem B4959629 : Blo 976593 4959629 := bstep (se 3 (by rfl) ⟨929930, by rfl⟩ : syracuseStep 4959629 = 1859861) B1859861
theorem B6270371 : Blo 976593 6270371 := bstep (se 1 (by rfl) ⟨4702778, by rfl⟩ : syracuseStep 6270371 = 9405557) B9405557
theorem B1322419 : Blo 976593 1322419 := bstep (se 1 (by rfl) ⟨991814, by rfl⟩ : syracuseStep 1322419 = 1983629) B1983629
theorem B1650145 : Blo 976593 1650145 := bstep (se 2 (by rfl) ⟨618804, by rfl⟩ : syracuseStep 1650145 = 1237609) B1237609
theorem B7056881 : Blo 976593 7056881 := bstep (se 2 (by rfl) ⟨2646330, by rfl⟩ : syracuseStep 7056881 = 5292661) B5292661
theorem B1650179 : Blo 976593 1650179 := bstep (se 1 (by rfl) ⟨1237634, by rfl⟩ : syracuseStep 1650179 = 2475269) B2475269
theorem B1486433 : Blo 976593 1486433 := bstep (se 2 (by rfl) ⟨557412, by rfl⟩ : syracuseStep 1486433 = 1114825) B1114825
theorem B1650307 : Blo 976593 1650307 := bstep (se 1 (by rfl) ⟨1237730, by rfl⟩ : syracuseStep 1650307 = 2475461) B2475461
theorem B7057165 : Blo 976593 7057165 := bstep (se 3 (by rfl) ⟨1323218, by rfl⟩ : syracuseStep 7057165 = 2646437) B2646437
theorem B1650449 : Blo 976593 1650449 := bstep (se 2 (by rfl) ⟨618918, by rfl⟩ : syracuseStep 1650449 = 1237837) B1237837
theorem B3714893 : Blo 976593 3714893 := bstep (se 3 (by rfl) ⟨696542, by rfl⟩ : syracuseStep 3714893 = 1393085) B1393085
theorem B1650577 : Blo 976593 1650577 := bstep (se 2 (by rfl) ⟨618966, by rfl⟩ : syracuseStep 1650577 = 1237933) B1237933
theorem B1650611 : Blo 976593 1650611 := bstep (se 1 (by rfl) ⟨1237958, by rfl⟩ : syracuseStep 1650611 = 2475917) B2475917
theorem B1650739 : Blo 976593 1650739 := bstep (se 1 (by rfl) ⟨1238054, by rfl⟩ : syracuseStep 1650739 = 2476109) B2476109
theorem B1650881 : Blo 976593 1650881 := bstep (se 2 (by rfl) ⟨619080, by rfl⟩ : syracuseStep 1650881 = 1238161) B1238161
theorem B1651009 : Blo 976593 1651009 := bstep (se 2 (by rfl) ⟨619128, by rfl⟩ : syracuseStep 1651009 = 1238257) B1238257
theorem B5288269 : Blo 976593 5288269 := bstep (se 3 (by rfl) ⟨991550, by rfl⟩ : syracuseStep 5288269 = 1983101) B1983101
theorem B1651043 : Blo 976593 1651043 := bstep (se 1 (by rfl) ⟨1238282, by rfl⟩ : syracuseStep 1651043 = 2476565) B2476565
theorem B1651171 : Blo 976593 1651171 := bstep (se 1 (by rfl) ⟨1238378, by rfl⟩ : syracuseStep 1651171 = 2476757) B2476757
theorem B1651313 : Blo 976593 1651313 := bstep (se 2 (by rfl) ⟨619242, by rfl⟩ : syracuseStep 1651313 = 1238485) B1238485
theorem B1651441 : Blo 976593 1651441 := bstep (se 2 (by rfl) ⟨619290, by rfl⟩ : syracuseStep 1651441 = 1238581) B1238581
theorem B1651475 : Blo 976593 1651475 := bstep (se 1 (by rfl) ⟨1238606, by rfl⟩ : syracuseStep 1651475 = 2477213) B2477213
theorem B1651603 : Blo 976593 1651603 := bstep (se 1 (by rfl) ⟨1238702, by rfl⟩ : syracuseStep 1651603 = 2477405) B2477405
theorem B1651745 : Blo 976593 1651745 := bstep (se 2 (by rfl) ⟨619404, by rfl⟩ : syracuseStep 1651745 = 1238809) B1238809
theorem B1651873 : Blo 976593 1651873 := bstep (se 2 (by rfl) ⟨619452, by rfl⟩ : syracuseStep 1651873 = 1238905) B1238905
theorem B5584049 : Blo 976593 5584049 := bstep (se 2 (by rfl) ⟨2094018, by rfl⟩ : syracuseStep 5584049 = 4188037) B4188037
theorem B1651907 : Blo 976593 1651907 := bstep (se 1 (by rfl) ⟨1238930, by rfl⟩ : syracuseStep 1651907 = 2477861) B2477861
theorem B1652035 : Blo 976593 1652035 := bstep (se 1 (by rfl) ⟨1239026, by rfl⟩ : syracuseStep 1652035 = 2478053) B2478053
theorem B1488305 : Blo 976593 1488305 := bstep (se 2 (by rfl) ⟨558114, by rfl⟩ : syracuseStep 1488305 = 1116229) B1116229
theorem B1652177 : Blo 976593 1652177 := bstep (se 2 (by rfl) ⟨619566, by rfl⟩ : syracuseStep 1652177 = 1239133) B1239133
theorem B1652305 : Blo 976593 1652305 := bstep (se 2 (by rfl) ⟨619614, by rfl⟩ : syracuseStep 1652305 = 1239229) B1239229
theorem B1652339 : Blo 976593 1652339 := bstep (se 1 (by rfl) ⟨1239254, by rfl⟩ : syracuseStep 1652339 = 2478509) B2478509
theorem B8369891 : Blo 976593 8369891 := bstep (se 1 (by rfl) ⟨6277418, by rfl⟩ : syracuseStep 8369891 = 12554837) B12554837
theorem B1652467 : Blo 976593 1652467 := bstep (se 1 (by rfl) ⟨1239350, by rfl⟩ : syracuseStep 1652467 = 2478701) B2478701
theorem B3389219 : Blo 976593 3389219 := bstep (se 1 (by rfl) ⟨2541914, by rfl⟩ : syracuseStep 3389219 = 5083829) B5083829
theorem B4175651 : Blo 976593 4175651 := bstep (se 1 (by rfl) ⟨3131738, by rfl⟩ : syracuseStep 4175651 = 6263477) B6263477
theorem B1488707 : Blo 976593 1488707 := bstep (se 1 (by rfl) ⟨1116530, by rfl⟩ : syracuseStep 1488707 = 2233061) B2233061
theorem B7419761 : Blo 976593 7419761 := bstep (se 2 (by rfl) ⟨2782410, by rfl⟩ : syracuseStep 7419761 = 5564821) B5564821
theorem B1652609 : Blo 976593 1652609 := bstep (se 2 (by rfl) ⟨619728, by rfl⟩ : syracuseStep 1652609 = 1239457) B1239457
theorem B6272909 : Blo 976593 6272909 := bstep (se 3 (by rfl) ⟨1176170, by rfl⟩ : syracuseStep 6272909 = 2352341) B2352341
theorem B1652737 : Blo 976593 1652737 := bstep (se 2 (by rfl) ⟨619776, by rfl⟩ : syracuseStep 1652737 = 1239553) B1239553
theorem B1652771 : Blo 976593 1652771 := bstep (se 1 (by rfl) ⟨1239578, by rfl⟩ : syracuseStep 1652771 = 2479157) B2479157
theorem B1652899 : Blo 976593 1652899 := bstep (se 1 (by rfl) ⟨1239674, by rfl⟩ : syracuseStep 1652899 = 2479349) B2479349
theorem B4962545 : Blo 976593 4962545 := bstep (se 2 (by rfl) ⟨1860954, by rfl⟩ : syracuseStep 4962545 = 3721909) B3721909
theorem B1718561 : Blo 976593 1718561 := bstep (se 2 (by rfl) ⟨644460, by rfl⟩ : syracuseStep 1718561 = 1288921) B1288921
theorem B2472241 : Blo 976593 2472241 := bstep (se 2 (by rfl) ⟨927090, by rfl⟩ : syracuseStep 2472241 = 1854181) B1854181
theorem B1653041 : Blo 976593 1653041 := bstep (se 2 (by rfl) ⟨619890, by rfl⟩ : syracuseStep 1653041 = 1239781) B1239781
theorem B1653169 : Blo 976593 1653169 := bstep (se 2 (by rfl) ⟨619938, by rfl⟩ : syracuseStep 1653169 = 1239877) B1239877
theorem B1653203 : Blo 976593 1653203 := bstep (se 1 (by rfl) ⟨1239902, by rfl⟩ : syracuseStep 1653203 = 2479805) B2479805
theorem B2472515 : Blo 976593 2472515 := bstep (se 1 (by rfl) ⟨1854386, by rfl⟩ : syracuseStep 2472515 = 3708773) B3708773
theorem B1653331 : Blo 976593 1653331 := bstep (se 1 (by rfl) ⟨1239998, by rfl⟩ : syracuseStep 1653331 = 2479997) B2479997
theorem B1587811 : Blo 976593 1587811 := bstep (se 1 (by rfl) ⟨1190858, by rfl⟩ : syracuseStep 1587811 = 2381717) B2381717
theorem B1391251 : Blo 976593 1391251 := bstep (se 1 (by rfl) ⟨1043438, by rfl⟩ : syracuseStep 1391251 = 2086877) B2086877
theorem B3717809 : Blo 976593 3717809 := bstep (se 2 (by rfl) ⟨1394178, by rfl⟩ : syracuseStep 3717809 = 2788357) B2788357
theorem B1653473 : Blo 976593 1653473 := bstep (se 2 (by rfl) ⟨620052, by rfl⟩ : syracuseStep 1653473 = 1240105) B1240105
theorem B4471523 : Blo 976593 4471523 := bstep (se 1 (by rfl) ⟨3353642, by rfl⟩ : syracuseStep 4471523 = 6707285) B6707285
theorem B2472707 : Blo 976593 2472707 := bstep (se 1 (by rfl) ⟨1854530, by rfl⟩ : syracuseStep 2472707 = 3709061) B3709061
theorem B5290757 : Blo 976593 5290757 := bstep (se 4 (by rfl) ⟨496008, by rfl⟩ : syracuseStep 5290757 = 992017) B992017
theorem B1653601 : Blo 976593 1653601 := bstep (se 2 (by rfl) ⟨620100, by rfl⟩ : syracuseStep 1653601 = 1240201) B1240201
theorem B1653635 : Blo 976593 1653635 := bstep (se 1 (by rfl) ⟨1240226, by rfl⟩ : syracuseStep 1653635 = 2480453) B2480453
theorem B1653763 : Blo 976593 1653763 := bstep (se 1 (by rfl) ⟨1240322, by rfl⟩ : syracuseStep 1653763 = 2480645) B2480645
theorem B3521549 : Blo 976593 3521549 := bstep (se 3 (by rfl) ⟨660290, by rfl⟩ : syracuseStep 3521549 = 1320581) B1320581
theorem B5028941 : Blo 976593 5028941 := bstep (se 3 (by rfl) ⟨942926, by rfl⟩ : syracuseStep 5028941 = 1885853) B1885853
theorem B1588307 : Blo 976593 1588307 := bstep (se 1 (by rfl) ⟨1191230, by rfl⟩ : syracuseStep 1588307 = 2382461) B2382461
theorem B1490051 : Blo 976593 1490051 := bstep (se 1 (by rfl) ⟨1117538, by rfl⟩ : syracuseStep 1490051 = 2235077) B2235077
theorem B1653905 : Blo 976593 1653905 := bstep (se 2 (by rfl) ⟨620214, by rfl⟩ : syracuseStep 1653905 = 1240429) B1240429
theorem B1490179 : Blo 976593 1490179 := bstep (se 1 (by rfl) ⟨1117634, by rfl⟩ : syracuseStep 1490179 = 2235269) B2235269
theorem B1654033 : Blo 976593 1654033 := bstep (se 2 (by rfl) ⟨620262, by rfl⟩ : syracuseStep 1654033 = 1240525) B1240525
theorem B1654067 : Blo 976593 1654067 := bstep (se 1 (by rfl) ⟨1240550, by rfl⟩ : syracuseStep 1654067 = 2481101) B2481101
theorem B2866531 : Blo 976593 2866531 := bstep (se 1 (by rfl) ⟨2149898, by rfl⟩ : syracuseStep 2866531 = 4299797) B4299797
theorem B8928625 : Blo 976593 8928625 := bstep (se 2 (by rfl) ⟨3348234, by rfl⟩ : syracuseStep 8928625 = 6696469) B6696469
theorem B1654195 : Blo 976593 1654195 := bstep (se 1 (by rfl) ⟨1240646, by rfl⟩ : syracuseStep 1654195 = 2481293) B2481293
theorem B1654337 : Blo 976593 1654337 := bstep (se 2 (by rfl) ⟨620376, by rfl⟩ : syracuseStep 1654337 = 1240753) B1240753
theorem B4964003 : Blo 976593 4964003 := bstep (se 1 (by rfl) ⟨3723002, by rfl⟩ : syracuseStep 4964003 = 7446005) B7446005
theorem B2473649 : Blo 976593 2473649 := bstep (se 2 (by rfl) ⟨927618, by rfl⟩ : syracuseStep 2473649 = 1855237) B1855237
theorem B1654465 : Blo 976593 1654465 := bstep (se 2 (by rfl) ⟨620424, by rfl⟩ : syracuseStep 1654465 = 1240849) B1240849
theorem B2473699 : Blo 976593 2473699 := bstep (se 1 (by rfl) ⟨1855274, by rfl⟩ : syracuseStep 2473699 = 3710549) B3710549
theorem B1654499 : Blo 976593 1654499 := bstep (se 1 (by rfl) ⟨1240874, by rfl⟩ : syracuseStep 1654499 = 2481749) B2481749
theorem B4177649 : Blo 976593 4177649 := bstep (se 2 (by rfl) ⟨1566618, by rfl⟩ : syracuseStep 4177649 = 3133237) B3133237
theorem B1392385 : Blo 976593 1392385 := bstep (se 2 (by rfl) ⟨522144, by rfl⟩ : syracuseStep 1392385 = 1044289) B1044289
theorem B3129137 : Blo 976593 3129137 := bstep (se 2 (by rfl) ⟨1173426, by rfl⟩ : syracuseStep 3129137 = 2346853) B2346853
theorem B6700877 : Blo 976593 6700877 := bstep (se 3 (by rfl) ⟨1256414, by rfl⟩ : syracuseStep 6700877 = 2512829) B2512829
theorem B1392481 : Blo 976593 1392481 := bstep (se 2 (by rfl) ⟨522180, by rfl⟩ : syracuseStep 1392481 = 1044361) B1044361
theorem B3129187 : Blo 976593 3129187 := bstep (se 1 (by rfl) ⟨2346890, by rfl⟩ : syracuseStep 3129187 = 4693781) B4693781
theorem B1654627 : Blo 976593 1654627 := bstep (se 1 (by rfl) ⟨1240970, by rfl⟩ : syracuseStep 1654627 = 2481941) B2481941
theorem B2473841 : Blo 976593 2473841 := bstep (se 2 (by rfl) ⟨927690, by rfl⟩ : syracuseStep 2473841 = 1855381) B1855381
theorem B3719267 : Blo 976593 3719267 := bstep (se 1 (by rfl) ⟨2789450, by rfl⟩ : syracuseStep 3719267 = 5578901) B5578901
theorem B1392977 : Blo 976593 1392977 := bstep (se 2 (by rfl) ⟨522366, by rfl⟩ : syracuseStep 1392977 = 1044733) B1044733
theorem B1983011 : Blo 976593 1983011 := bstep (se 1 (by rfl) ⟨1487258, by rfl⟩ : syracuseStep 1983011 = 2974517) B2974517
theorem B4178573 : Blo 976593 4178573 := bstep (se 3 (by rfl) ⟨783482, by rfl⟩ : syracuseStep 4178573 = 1566965) B1566965
theorem B21185333 : Blo 976593 21185333 := bstep (se 5 (by rfl) ⟨993062, by rfl⟩ : syracuseStep 21185333 = 1986125) B1986125
theorem B2474833 : Blo 976593 2474833 := bstep (se 2 (by rfl) ⟨928062, by rfl⟩ : syracuseStep 2474833 = 1856125) B1856125
theorem B1098787 : Blo 976593 1098787 := bstep (se 1 (by rfl) ⟨824090, by rfl⟩ : syracuseStep 1098787 = 1648181) B1648181
theorem B3130417 : Blo 976593 3130417 := bstep (se 2 (by rfl) ⟨1173906, by rfl⟩ : syracuseStep 3130417 = 2347813) B2347813
theorem B3720269 : Blo 976593 3720269 := bstep (se 3 (by rfl) ⟨697550, by rfl⟩ : syracuseStep 3720269 = 1395101) B1395101
theorem B2475107 : Blo 976593 2475107 := bstep (se 1 (by rfl) ⟨1856330, by rfl⟩ : syracuseStep 2475107 = 3712661) B3712661
theorem B1098931 : Blo 976593 1098931 := bstep (se 1 (by rfl) ⟨824198, by rfl⟩ : syracuseStep 1098931 = 1648397) B1648397
theorem B1393843 : Blo 976593 1393843 := bstep (se 1 (by rfl) ⟨1045382, by rfl⟩ : syracuseStep 1393843 = 2090765) B2090765
theorem B1393939 : Blo 976593 1393939 := bstep (se 1 (by rfl) ⟨1045454, by rfl⟩ : syracuseStep 1393939 = 2090909) B2090909
theorem B2475299 : Blo 976593 2475299 := bstep (se 1 (by rfl) ⟨1856474, by rfl⟩ : syracuseStep 2475299 = 3712949) B3712949
theorem B1099075 : Blo 976593 1099075 := bstep (se 1 (by rfl) ⟨824306, by rfl⟩ : syracuseStep 1099075 = 1648613) B1648613
theorem B1983953 : Blo 976593 1983953 := bstep (se 2 (by rfl) ⟨743982, by rfl⟩ : syracuseStep 1983953 = 1487965) B1487965
theorem B1099219 : Blo 976593 1099219 := bstep (se 1 (by rfl) ⟨824414, by rfl⟩ : syracuseStep 1099219 = 1648829) B1648829
theorem B11879921 : Blo 976593 11879921 := bstep (se 2 (by rfl) ⟨4454970, by rfl⟩ : syracuseStep 11879921 = 8909941) B8909941
theorem B1099363 : Blo 976593 1099363 := bstep (se 1 (by rfl) ⟨824522, by rfl⟩ : syracuseStep 1099363 = 1649045) B1649045
theorem B9389681 : Blo 976593 9389681 := bstep (se 2 (by rfl) ⟨3521130, by rfl⟩ : syracuseStep 9389681 = 7042261) B7042261
theorem B1590929 : Blo 976593 1590929 := bstep (se 2 (by rfl) ⟨596598, by rfl⟩ : syracuseStep 1590929 = 1193197) B1193197
theorem B7948003 : Blo 976593 7948003 := bstep (se 1 (by rfl) ⟨5961002, by rfl⟩ : syracuseStep 7948003 = 11922005) B11922005
theorem B4835057 : Blo 976593 4835057 := bstep (se 2 (by rfl) ⟨1813146, by rfl⟩ : syracuseStep 4835057 = 3626293) B3626293
theorem B1099507 : Blo 976593 1099507 := bstep (se 1 (by rfl) ⟨824630, by rfl⟩ : syracuseStep 1099507 = 1649261) B1649261
theorem B1394435 : Blo 976593 1394435 := bstep (se 1 (by rfl) ⟨1045826, by rfl⟩ : syracuseStep 1394435 = 2091653) B2091653
theorem B5654285 : Blo 976593 5654285 := bstep (se 3 (by rfl) ⟨1060178, by rfl⟩ : syracuseStep 5654285 = 2120357) B2120357
theorem B1099651 : Blo 976593 1099651 := bstep (se 1 (by rfl) ⟨824738, by rfl⟩ : syracuseStep 1099651 = 1649477) B1649477
theorem B2639843 : Blo 976593 2639843 := bstep (se 1 (by rfl) ⟨1979882, by rfl⟩ : syracuseStep 2639843 = 3959765) B3959765
theorem B1099795 : Blo 976593 1099795 := bstep (se 1 (by rfl) ⟨824846, by rfl⟩ : syracuseStep 1099795 = 1649693) B1649693
theorem B1099939 : Blo 976593 1099939 := bstep (se 1 (by rfl) ⟨824954, by rfl⟩ : syracuseStep 1099939 = 1649909) B1649909
theorem B3131597 : Blo 976593 3131597 := bstep (se 3 (by rfl) ⟨587174, by rfl⟩ : syracuseStep 3131597 = 1174349) B1174349
theorem B2476241 : Blo 976593 2476241 := bstep (se 2 (by rfl) ⟨928590, by rfl⟩ : syracuseStep 2476241 = 1857181) B1857181
theorem B7948529 : Blo 976593 7948529 := bstep (se 2 (by rfl) ⟨2980698, by rfl⟩ : syracuseStep 7948529 = 5961397) B5961397
theorem B2476291 : Blo 976593 2476291 := bstep (se 1 (by rfl) ⟨1857218, by rfl⟩ : syracuseStep 2476291 = 3714437) B3714437
theorem B1100083 : Blo 976593 1100083 := bstep (se 1 (by rfl) ⟨825062, by rfl⟩ : syracuseStep 1100083 = 1650125) B1650125
theorem B1395073 : Blo 976593 1395073 := bstep (se 2 (by rfl) ⟨523152, by rfl⟩ : syracuseStep 1395073 = 1046305) B1046305
theorem B2476433 : Blo 976593 2476433 := bstep (se 2 (by rfl) ⟨928662, by rfl⟩ : syracuseStep 2476433 = 1857325) B1857325
theorem B1100227 : Blo 976593 1100227 := bstep (se 1 (by rfl) ⟨825170, by rfl⟩ : syracuseStep 1100227 = 1650341) B1650341
theorem B1100371 : Blo 976593 1100371 := bstep (se 1 (by rfl) ⟨825278, by rfl⟩ : syracuseStep 1100371 = 1650557) B1650557
theorem B1854083 : Blo 976593 1854083 := bstep (se 1 (by rfl) ⟨1390562, by rfl⟩ : syracuseStep 1854083 = 2781125) B2781125
theorem B1985219 : Blo 976593 1985219 := bstep (se 1 (by rfl) ⟨1488914, by rfl⟩ : syracuseStep 1985219 = 2977829) B2977829
theorem B1395409 : Blo 976593 1395409 := bstep (se 2 (by rfl) ⟨523278, by rfl⟩ : syracuseStep 1395409 = 1046557) B1046557
theorem B1100515 : Blo 976593 1100515 := bstep (se 1 (by rfl) ⟨825386, by rfl⟩ : syracuseStep 1100515 = 1650773) B1650773
theorem B10734389 : Blo 976593 10734389 := bstep (se 5 (by rfl) ⟨503174, by rfl⟩ : syracuseStep 10734389 = 1006349) B1006349
theorem B1100659 : Blo 976593 1100659 := bstep (se 1 (by rfl) ⟨825494, by rfl⟩ : syracuseStep 1100659 = 1650989) B1650989
theorem B1100803 : Blo 976593 1100803 := bstep (se 1 (by rfl) ⟨825602, by rfl⟩ : syracuseStep 1100803 = 1651205) B1651205
theorem B2509955 : Blo 976593 2509955 := bstep (se 1 (by rfl) ⟨1882466, by rfl⟩ : syracuseStep 2509955 = 3764933) B3764933
theorem B3722381 : Blo 976593 3722381 := bstep (se 3 (by rfl) ⟨697946, by rfl⟩ : syracuseStep 3722381 = 1395893) B1395893
theorem B3394705 : Blo 976593 3394705 := bstep (se 2 (by rfl) ⟨1273014, by rfl⟩ : syracuseStep 3394705 = 2546029) B2546029
theorem B1100947 : Blo 976593 1100947 := bstep (se 1 (by rfl) ⟨825710, by rfl⟩ : syracuseStep 1100947 = 1651421) B1651421
theorem B3296429 : Blo 976593 3296429 := bstep (se 3 (by rfl) ⟨618080, by rfl⟩ : syracuseStep 3296429 = 1236161) B1236161
theorem B3296483 : Blo 976593 3296483 := bstep (se 1 (by rfl) ⟨2472362, by rfl⟩ : syracuseStep 3296483 = 4944725) B4944725
theorem B1396001 : Blo 976593 1396001 := bstep (se 2 (by rfl) ⟨523500, by rfl⟩ : syracuseStep 1396001 = 1047001) B1047001
theorem B1101091 : Blo 976593 1101091 := bstep (se 1 (by rfl) ⟨825818, by rfl⟩ : syracuseStep 1101091 = 1651637) B1651637
theorem B2477425 : Blo 976593 2477425 := bstep (se 2 (by rfl) ⟨929034, by rfl⟩ : syracuseStep 2477425 = 1858069) B1858069
theorem B1101235 : Blo 976593 1101235 := bstep (se 1 (by rfl) ⟨825926, by rfl⟩ : syracuseStep 1101235 = 1651853) B1651853
theorem B2379217 : Blo 976593 2379217 := bstep (se 2 (by rfl) ⟨892206, by rfl⟩ : syracuseStep 2379217 = 1784413) B1784413
theorem B3296753 : Blo 976593 3296753 := bstep (se 2 (by rfl) ⟨1236282, by rfl⟩ : syracuseStep 3296753 = 2472565) B2472565
theorem B2346545 : Blo 976593 2346545 := bstep (se 2 (by rfl) ⟨879954, by rfl⟩ : syracuseStep 2346545 = 1759909) B1759909
theorem B4902449 : Blo 976593 4902449 := bstep (se 2 (by rfl) ⟨1838418, by rfl⟩ : syracuseStep 4902449 = 3676837) B3676837
theorem B1101379 : Blo 976593 1101379 := bstep (se 1 (by rfl) ⟨826034, by rfl⟩ : syracuseStep 1101379 = 1652069) B1652069
theorem B2477699 : Blo 976593 2477699 := bstep (se 1 (by rfl) ⟨1858274, by rfl⟩ : syracuseStep 2477699 = 3716549) B3716549
theorem B11292301 : Blo 976593 11292301 := bstep (se 3 (by rfl) ⟨2117306, by rfl⟩ : syracuseStep 11292301 = 4234613) B4234613
theorem B1855153 : Blo 976593 1855153 := bstep (se 2 (by rfl) ⟨695682, by rfl⟩ : syracuseStep 1855153 = 1391365) B1391365
theorem B4181681 : Blo 976593 4181681 := bstep (se 2 (by rfl) ⟨1568130, by rfl⟩ : syracuseStep 4181681 = 3136261) B3136261
theorem B1101523 : Blo 976593 1101523 := bstep (se 1 (by rfl) ⟨826142, by rfl⟩ : syracuseStep 1101523 = 1652285) B1652285
theorem B2477891 : Blo 976593 2477891 := bstep (se 1 (by rfl) ⟨1858418, by rfl⟩ : syracuseStep 2477891 = 3716837) B3716837
theorem B7065413 : Blo 976593 7065413 := bstep (se 4 (by rfl) ⟨662382, by rfl⟩ : syracuseStep 7065413 = 1324765) B1324765
theorem B1101667 : Blo 976593 1101667 := bstep (se 1 (by rfl) ⟨826250, by rfl⟩ : syracuseStep 1101667 = 1652501) B1652501
theorem B3723185 : Blo 976593 3723185 := bstep (se 2 (by rfl) ⟨1396194, by rfl⟩ : syracuseStep 3723185 = 2792389) B2792389
theorem B3133379 : Blo 976593 3133379 := bstep (se 1 (by rfl) ⟨2350034, by rfl⟩ : syracuseStep 3133379 = 4700069) B4700069
theorem B1101811 : Blo 976593 1101811 := bstep (se 1 (by rfl) ⟨826358, by rfl⟩ : syracuseStep 1101811 = 1652717) B1652717
theorem B3297293 : Blo 976593 3297293 := bstep (se 3 (by rfl) ⟨618242, by rfl⟩ : syracuseStep 3297293 = 1236485) B1236485
theorem B3297347 : Blo 976593 3297347 := bstep (se 1 (by rfl) ⟨2473010, by rfl⟩ : syracuseStep 3297347 = 4946021) B4946021
theorem B1101955 : Blo 976593 1101955 := bstep (se 1 (by rfl) ⟨826466, by rfl⟩ : syracuseStep 1101955 = 1652933) B1652933
theorem B125751523 : Blo 976593 125751523 := bstep (se 1 (by rfl) ⟨94313642, by rfl⟩ : syracuseStep 125751523 = 188627285) B188627285
theorem B3526897 : Blo 976593 3526897 := bstep (se 2 (by rfl) ⟨1322586, by rfl⟩ : syracuseStep 3526897 = 2645173) B2645173
theorem B4706545 : Blo 976593 4706545 := bstep (se 2 (by rfl) ⟨1764954, by rfl⟩ : syracuseStep 4706545 = 3529909) B3529909
theorem B1102099 : Blo 976593 1102099 := bstep (se 1 (by rfl) ⟨826574, by rfl⟩ : syracuseStep 1102099 = 1653149) B1653149
theorem B3297617 : Blo 976593 3297617 := bstep (se 2 (by rfl) ⟨1236606, by rfl⟩ : syracuseStep 3297617 = 2473213) B2473213
theorem B1102243 : Blo 976593 1102243 := bstep (se 1 (by rfl) ⟨826682, by rfl⟩ : syracuseStep 1102243 = 1653365) B1653365
theorem B2511395 : Blo 976593 2511395 := bstep (se 1 (by rfl) ⟨1883546, by rfl⟩ : syracuseStep 2511395 = 3767093) B3767093
theorem B1102387 : Blo 976593 1102387 := bstep (se 1 (by rfl) ⟨826790, by rfl⟩ : syracuseStep 1102387 = 1653581) B1653581
theorem B2970179 : Blo 976593 2970179 := bstep (se 1 (by rfl) ⟨2227634, by rfl⟩ : syracuseStep 2970179 = 4455269) B4455269
theorem B1102531 : Blo 976593 1102531 := bstep (se 1 (by rfl) ⟨826898, by rfl⟩ : syracuseStep 1102531 = 1653797) B1653797
theorem B1856209 : Blo 976593 1856209 := bstep (se 2 (by rfl) ⟨696078, by rfl⟩ : syracuseStep 1856209 = 1392157) B1392157
theorem B2478833 : Blo 976593 2478833 := bstep (se 2 (by rfl) ⟨929562, by rfl⟩ : syracuseStep 2478833 = 1859125) B1859125
theorem B2478883 : Blo 976593 2478883 := bstep (se 1 (by rfl) ⟨1859162, by rfl⟩ : syracuseStep 2478883 = 3718325) B3718325
theorem B2118467 : Blo 976593 2118467 := bstep (se 1 (by rfl) ⟨1588850, by rfl⟩ : syracuseStep 2118467 = 3177701) B3177701
theorem B1102675 : Blo 976593 1102675 := bstep (se 1 (by rfl) ⟨827006, by rfl⟩ : syracuseStep 1102675 = 1654013) B1654013
theorem B3298157 : Blo 976593 3298157 := bstep (se 3 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 3298157 = 1236809) B1236809
theorem B3298211 : Blo 976593 3298211 := bstep (se 1 (by rfl) ⟨2473658, by rfl⟩ : syracuseStep 3298211 = 4947317) B4947317
theorem B4182947 : Blo 976593 4182947 := bstep (se 1 (by rfl) ⟨3137210, by rfl⟩ : syracuseStep 4182947 = 6274421) B6274421
theorem B2479025 : Blo 976593 2479025 := bstep (se 2 (by rfl) ⟨929634, by rfl⟩ : syracuseStep 2479025 = 1859269) B1859269
theorem B1102819 : Blo 976593 1102819 := bstep (se 1 (by rfl) ⟨827114, by rfl⟩ : syracuseStep 1102819 = 1654229) B1654229
theorem B3134467 : Blo 976593 3134467 := bstep (se 1 (by rfl) ⟨2350850, by rfl⟩ : syracuseStep 3134467 = 4701701) B4701701
theorem B1856611 : Blo 976593 1856611 := bstep (se 1 (by rfl) ⟨1392458, by rfl⟩ : syracuseStep 1856611 = 2784917) B2784917
theorem B1102963 : Blo 976593 1102963 := bstep (se 1 (by rfl) ⟨827222, by rfl⟩ : syracuseStep 1102963 = 1654445) B1654445
theorem B1987715 : Blo 976593 1987715 := bstep (se 1 (by rfl) ⟨1490786, by rfl⟩ : syracuseStep 1987715 = 2981573) B2981573
theorem B1856657 : Blo 976593 1856657 := bstep (se 2 (by rfl) ⟨696246, by rfl⟩ : syracuseStep 1856657 = 1392493) B1392493
theorem B3134609 : Blo 976593 3134609 := bstep (se 2 (by rfl) ⟨1175478, by rfl⟩ : syracuseStep 3134609 = 2350957) B2350957
theorem B3298481 : Blo 976593 3298481 := bstep (se 2 (by rfl) ⟨1236930, by rfl⟩ : syracuseStep 3298481 = 2473861) B2473861
theorem B1103107 : Blo 976593 1103107 := bstep (se 1 (by rfl) ⟨827330, by rfl⟩ : syracuseStep 1103107 = 1654661) B1654661
theorem B2086193 : Blo 976593 2086193 := bstep (se 2 (by rfl) ⟨782322, by rfl⟩ : syracuseStep 2086193 = 1564645) B1564645
theorem B2086211 : Blo 976593 2086211 := bstep (se 1 (by rfl) ⟨1564658, by rfl⟩ : syracuseStep 2086211 = 3129317) B3129317
theorem B6280517 : Blo 976593 6280517 := bstep (se 4 (by rfl) ⟨588798, by rfl⟩ : syracuseStep 6280517 = 1177597) B1177597
theorem B1856945 : Blo 976593 1856945 := bstep (se 2 (by rfl) ⟨696354, by rfl⟩ : syracuseStep 1856945 = 1392709) B1392709
theorem B20338229 : Blo 976593 20338229 := bstep (se 5 (by rfl) ⟨953354, by rfl⟩ : syracuseStep 20338229 = 1906709) B1906709
theorem B3299021 : Blo 976593 3299021 := bstep (se 3 (by rfl) ⟨618566, by rfl⟩ : syracuseStep 3299021 = 1237133) B1237133
theorem B3299075 : Blo 976593 3299075 := bstep (se 1 (by rfl) ⟨2474306, by rfl⟩ : syracuseStep 3299075 = 4948613) B4948613
theorem B6706979 : Blo 976593 6706979 := bstep (se 1 (by rfl) ⟨5030234, by rfl⟩ : syracuseStep 6706979 = 10060469) B10060469
theorem B2480017 : Blo 976593 2480017 := bstep (se 2 (by rfl) ⟨930006, by rfl⟩ : syracuseStep 2480017 = 1860013) B1860013
theorem B3299345 : Blo 976593 3299345 := bstep (se 2 (by rfl) ⟨1237254, by rfl⟩ : syracuseStep 3299345 = 2474509) B2474509
theorem B2644049 : Blo 976593 2644049 := bstep (se 2 (by rfl) ⟨991518, by rfl⟩ : syracuseStep 2644049 = 1983037) B1983037
theorem B1857667 : Blo 976593 1857667 := bstep (se 1 (by rfl) ⟨1393250, by rfl⟩ : syracuseStep 1857667 = 2786501) B2786501
theorem B2480291 : Blo 976593 2480291 := bstep (se 1 (by rfl) ⟨1860218, by rfl⟩ : syracuseStep 2480291 = 3720437) B3720437
theorem B2480483 : Blo 976593 2480483 := bstep (se 1 (by rfl) ⟨1860362, by rfl⟩ : syracuseStep 2480483 = 3720725) B3720725
theorem B9525617 : Blo 976593 9525617 := bstep (se 2 (by rfl) ⟨3572106, by rfl⟩ : syracuseStep 9525617 = 7144213) B7144213
theorem B2972035 : Blo 976593 2972035 := bstep (se 1 (by rfl) ⟨2229026, by rfl⟩ : syracuseStep 2972035 = 4458053) B4458053
theorem B3135953 : Blo 976593 3135953 := bstep (se 2 (by rfl) ⟨1175982, by rfl⟩ : syracuseStep 3135953 = 2351965) B2351965
theorem B2087441 : Blo 976593 2087441 := bstep (se 2 (by rfl) ⟨782790, by rfl⟩ : syracuseStep 2087441 = 1565581) B1565581
theorem B3299885 : Blo 976593 3299885 := bstep (se 3 (by rfl) ⟨618728, by rfl⟩ : syracuseStep 3299885 = 1237457) B1237457
theorem B1464899 : Blo 976593 1464899 := bstep (se 1 (by rfl) ⟨1098674, by rfl⟩ : syracuseStep 1464899 = 2197349) B2197349
theorem B1858115 : Blo 976593 1858115 := bstep (se 1 (by rfl) ⟨1393586, by rfl⟩ : syracuseStep 1858115 = 2787173) B2787173
theorem B1464929 : Blo 976593 1464929 := bstep (se 2 (by rfl) ⟨549348, by rfl⟩ : syracuseStep 1464929 = 1098697) B1098697
theorem B3299939 : Blo 976593 3299939 := bstep (se 1 (by rfl) ⟨2474954, by rfl⟩ : syracuseStep 3299939 = 4949909) B4949909
theorem B1464947 : Blo 976593 1464947 := bstep (se 1 (by rfl) ⟨1098710, by rfl⟩ : syracuseStep 1464947 = 2197421) B2197421
theorem B1464977 : Blo 976593 1464977 := bstep (se 2 (by rfl) ⟨549366, by rfl⟩ : syracuseStep 1464977 = 1098733) B1098733
theorem B1464995 : Blo 976593 1464995 := bstep (se 1 (by rfl) ⟨1098746, by rfl⟩ : syracuseStep 1464995 = 2197493) B2197493
theorem B1465025 : Blo 976593 1465025 := bstep (se 2 (by rfl) ⟨549384, by rfl⟩ : syracuseStep 1465025 = 1098769) B1098769
theorem B1465043 : Blo 976593 1465043 := bstep (se 1 (by rfl) ⟨1098782, by rfl⟩ : syracuseStep 1465043 = 2197565) B2197565
theorem B1465073 : Blo 976593 1465073 := bstep (se 2 (by rfl) ⟨549402, by rfl⟩ : syracuseStep 1465073 = 1098805) B1098805
theorem B1465091 : Blo 976593 1465091 := bstep (se 1 (by rfl) ⟨1098818, by rfl⟩ : syracuseStep 1465091 = 2197637) B2197637
theorem B1465121 : Blo 976593 1465121 := bstep (se 2 (by rfl) ⟨549420, by rfl⟩ : syracuseStep 1465121 = 1098841) B1098841
theorem B1465139 : Blo 976593 1465139 := bstep (se 1 (by rfl) ⟨1098854, by rfl⟩ : syracuseStep 1465139 = 2197709) B2197709
theorem B1465169 : Blo 976593 1465169 := bstep (se 2 (by rfl) ⟨549438, by rfl⟩ : syracuseStep 1465169 = 1098877) B1098877
theorem B1465187 : Blo 976593 1465187 := bstep (se 1 (by rfl) ⟨1098890, by rfl⟩ : syracuseStep 1465187 = 2197781) B2197781
theorem B1858403 : Blo 976593 1858403 := bstep (se 1 (by rfl) ⟨1393802, by rfl⟩ : syracuseStep 1858403 = 2787605) B2787605
theorem B3300209 : Blo 976593 3300209 := bstep (se 2 (by rfl) ⟨1237578, by rfl⟩ : syracuseStep 3300209 = 2475157) B2475157
theorem B1465217 : Blo 976593 1465217 := bstep (se 2 (by rfl) ⟨549456, by rfl⟩ : syracuseStep 1465217 = 1098913) B1098913
theorem B1465235 : Blo 976593 1465235 := bstep (se 1 (by rfl) ⟨1098926, by rfl⟩ : syracuseStep 1465235 = 2197853) B2197853
theorem B1465265 : Blo 976593 1465265 := bstep (se 2 (by rfl) ⟨549474, by rfl⟩ : syracuseStep 1465265 = 1098949) B1098949
theorem B11131829 : Blo 976593 11131829 := bstep (se 5 (by rfl) ⟨521804, by rfl⟩ : syracuseStep 11131829 = 1043609) B1043609
theorem B1465283 : Blo 976593 1465283 := bstep (se 1 (by rfl) ⟨1098962, by rfl⟩ : syracuseStep 1465283 = 2197925) B2197925
theorem B1465313 : Blo 976593 1465313 := bstep (se 2 (by rfl) ⟨549492, by rfl⟩ : syracuseStep 1465313 = 1098985) B1098985
theorem B1694689 : Blo 976593 1694689 := bstep (se 2 (by rfl) ⟨635508, by rfl⟩ : syracuseStep 1694689 = 1271017) B1271017
theorem B1465331 : Blo 976593 1465331 := bstep (se 1 (by rfl) ⟨1098998, by rfl⟩ : syracuseStep 1465331 = 2197997) B2197997
theorem B2382851 : Blo 976593 2382851 := bstep (se 1 (by rfl) ⟨1787138, by rfl⟩ : syracuseStep 2382851 = 3574277) B3574277
theorem B1465361 : Blo 976593 1465361 := bstep (se 2 (by rfl) ⟨549510, by rfl⟩ : syracuseStep 1465361 = 1099021) B1099021
theorem B1465379 : Blo 976593 1465379 := bstep (se 1 (by rfl) ⟨1099034, by rfl⟩ : syracuseStep 1465379 = 2198069) B2198069
theorem B1465409 : Blo 976593 1465409 := bstep (se 2 (by rfl) ⟨549528, by rfl⟩ : syracuseStep 1465409 = 1099057) B1099057
theorem B1465427 : Blo 976593 1465427 := bstep (se 1 (by rfl) ⟨1099070, by rfl⟩ : syracuseStep 1465427 = 2198141) B2198141
theorem B1072211 : Blo 976593 1072211 := bstep (se 1 (by rfl) ⟨804158, by rfl⟩ : syracuseStep 1072211 = 1608317) B1608317
theorem B1465457 : Blo 976593 1465457 := bstep (se 2 (by rfl) ⟨549546, by rfl⟩ : syracuseStep 1465457 = 1099093) B1099093
theorem B1465475 : Blo 976593 1465475 := bstep (se 1 (by rfl) ⟨1099106, by rfl⟩ : syracuseStep 1465475 = 2198213) B2198213
theorem B1465505 : Blo 976593 1465505 := bstep (se 2 (by rfl) ⟨549564, by rfl⟩ : syracuseStep 1465505 = 1099129) B1099129
theorem B1465523 : Blo 976593 1465523 := bstep (se 1 (by rfl) ⟨1099142, by rfl⟩ : syracuseStep 1465523 = 2198285) B2198285
theorem B1465553 : Blo 976593 1465553 := bstep (se 2 (by rfl) ⟨549582, by rfl⟩ : syracuseStep 1465553 = 1099165) B1099165
theorem B1465571 : Blo 976593 1465571 := bstep (se 1 (by rfl) ⟨1099178, by rfl⟩ : syracuseStep 1465571 = 2198357) B2198357
theorem B4709603 : Blo 976593 4709603 := bstep (se 1 (by rfl) ⟨3532202, by rfl⟩ : syracuseStep 4709603 = 7064405) B7064405
theorem B6282467 : Blo 976593 6282467 := bstep (se 1 (by rfl) ⟨4711850, by rfl⟩ : syracuseStep 6282467 = 9423701) B9423701
theorem B1465601 : Blo 976593 1465601 := bstep (se 2 (by rfl) ⟨549600, by rfl⟩ : syracuseStep 1465601 = 1099201) B1099201
theorem B2481425 : Blo 976593 2481425 := bstep (se 2 (by rfl) ⟨930534, by rfl⟩ : syracuseStep 2481425 = 1861069) B1861069
theorem B1465619 : Blo 976593 1465619 := bstep (se 1 (by rfl) ⟨1099214, by rfl⟩ : syracuseStep 1465619 = 2198429) B2198429
theorem B1465649 : Blo 976593 1465649 := bstep (se 2 (by rfl) ⟨549618, by rfl⟩ : syracuseStep 1465649 = 1099237) B1099237
theorem B1465667 : Blo 976593 1465667 := bstep (se 1 (by rfl) ⟨1099250, by rfl⟩ : syracuseStep 1465667 = 2198501) B2198501
theorem B2481475 : Blo 976593 2481475 := bstep (se 1 (by rfl) ⟨1861106, by rfl⟩ : syracuseStep 2481475 = 3722213) B3722213
theorem B1465697 : Blo 976593 1465697 := bstep (se 2 (by rfl) ⟨549636, by rfl⟩ : syracuseStep 1465697 = 1099273) B1099273
theorem B1236323 : Blo 976593 1236323 := bstep (se 1 (by rfl) ⟨927242, by rfl⟩ : syracuseStep 1236323 = 1854485) B1854485
theorem B3136877 : Blo 976593 3136877 := bstep (se 3 (by rfl) ⟨588164, by rfl⟩ : syracuseStep 3136877 = 1176329) B1176329
theorem B1465715 : Blo 976593 1465715 := bstep (se 1 (by rfl) ⟨1099286, by rfl⟩ : syracuseStep 1465715 = 2198573) B2198573
theorem B3300749 : Blo 976593 3300749 := bstep (se 3 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 3300749 = 1237781) B1237781
theorem B4709773 : Blo 976593 4709773 := bstep (se 3 (by rfl) ⟨883082, by rfl⟩ : syracuseStep 4709773 = 1766165) B1766165
theorem B1465745 : Blo 976593 1465745 := bstep (se 2 (by rfl) ⟨549654, by rfl⟩ : syracuseStep 1465745 = 1099309) B1099309
theorem B1465763 : Blo 976593 1465763 := bstep (se 1 (by rfl) ⟨1099322, by rfl⟩ : syracuseStep 1465763 = 2198645) B2198645
theorem B1465793 : Blo 976593 1465793 := bstep (se 2 (by rfl) ⟨549672, by rfl⟩ : syracuseStep 1465793 = 1099345) B1099345
theorem B3300803 : Blo 976593 3300803 := bstep (se 1 (by rfl) ⟨2475602, by rfl⟩ : syracuseStep 3300803 = 4951205) B4951205
theorem B2481617 : Blo 976593 2481617 := bstep (se 2 (by rfl) ⟨930606, by rfl⟩ : syracuseStep 2481617 = 1861213) B1861213
theorem B1465811 : Blo 976593 1465811 := bstep (se 1 (by rfl) ⟨1099358, by rfl⟩ : syracuseStep 1465811 = 2198717) B2198717
theorem B1465841 : Blo 976593 1465841 := bstep (se 2 (by rfl) ⟨549690, by rfl⟩ : syracuseStep 1465841 = 1099381) B1099381
theorem B8052209 : Blo 976593 8052209 := bstep (se 2 (by rfl) ⟨3019578, by rfl⟩ : syracuseStep 8052209 = 6039157) B6039157
theorem B1465859 : Blo 976593 1465859 := bstep (se 1 (by rfl) ⟨1099394, by rfl⟩ : syracuseStep 1465859 = 2198789) B2198789
theorem B1465889 : Blo 976593 1465889 := bstep (se 2 (by rfl) ⟨549708, by rfl⟩ : syracuseStep 1465889 = 1099417) B1099417
theorem B3137069 : Blo 976593 3137069 := bstep (se 3 (by rfl) ⟨588200, by rfl⟩ : syracuseStep 3137069 = 1176401) B1176401
theorem B1465907 : Blo 976593 1465907 := bstep (se 1 (by rfl) ⟨1099430, by rfl⟩ : syracuseStep 1465907 = 2198861) B2198861
theorem B1465937 : Blo 976593 1465937 := bstep (se 2 (by rfl) ⟨549726, by rfl⟩ : syracuseStep 1465937 = 1099453) B1099453
theorem B1465955 : Blo 976593 1465955 := bstep (se 1 (by rfl) ⟨1099466, by rfl⟩ : syracuseStep 1465955 = 2198933) B2198933
theorem B1465985 : Blo 976593 1465985 := bstep (se 2 (by rfl) ⟨549744, by rfl⟩ : syracuseStep 1465985 = 1099489) B1099489
theorem B1466003 : Blo 976593 1466003 := bstep (se 1 (by rfl) ⟨1099502, by rfl⟩ : syracuseStep 1466003 = 2199005) B2199005
theorem B1466033 : Blo 976593 1466033 := bstep (se 2 (by rfl) ⟨549762, by rfl⟩ : syracuseStep 1466033 = 1099525) B1099525
theorem B2449073 : Blo 976593 2449073 := bstep (se 2 (by rfl) ⟨918402, by rfl⟩ : syracuseStep 2449073 = 1836805) B1836805
theorem B1466051 : Blo 976593 1466051 := bstep (se 1 (by rfl) ⟨1099538, by rfl⟩ : syracuseStep 1466051 = 2199077) B2199077
theorem B3301073 : Blo 976593 3301073 := bstep (se 2 (by rfl) ⟨1237902, by rfl⟩ : syracuseStep 3301073 = 2475805) B2475805
theorem B1466081 : Blo 976593 1466081 := bstep (se 2 (by rfl) ⟨549780, by rfl⟩ : syracuseStep 1466081 = 1099561) B1099561
theorem B1466099 : Blo 976593 1466099 := bstep (se 1 (by rfl) ⟨1099574, by rfl⟩ : syracuseStep 1466099 = 2199149) B2199149
theorem B1466129 : Blo 976593 1466129 := bstep (se 2 (by rfl) ⟨549798, by rfl⟩ : syracuseStep 1466129 = 1099597) B1099597
theorem B1859345 : Blo 976593 1859345 := bstep (se 2 (by rfl) ⟨697254, by rfl⟩ : syracuseStep 1859345 = 1394509) B1394509
theorem B1466147 : Blo 976593 1466147 := bstep (se 1 (by rfl) ⟨1099610, by rfl⟩ : syracuseStep 1466147 = 2199221) B2199221
theorem B1466177 : Blo 976593 1466177 := bstep (se 2 (by rfl) ⟨549816, by rfl⟩ : syracuseStep 1466177 = 1099633) B1099633
theorem B1466195 : Blo 976593 1466195 := bstep (se 1 (by rfl) ⟨1099646, by rfl⟩ : syracuseStep 1466195 = 2199293) B2199293
theorem B1466225 : Blo 976593 1466225 := bstep (se 2 (by rfl) ⟨549834, by rfl⟩ : syracuseStep 1466225 = 1099669) B1099669
theorem B1466243 : Blo 976593 1466243 := bstep (se 1 (by rfl) ⟨1099682, by rfl⟩ : syracuseStep 1466243 = 2199365) B2199365
theorem B1466273 : Blo 976593 1466273 := bstep (se 2 (by rfl) ⟨549852, by rfl⟩ : syracuseStep 1466273 = 1099705) B1099705
theorem B1466291 : Blo 976593 1466291 := bstep (se 1 (by rfl) ⟨1099718, by rfl⟩ : syracuseStep 1466291 = 2199437) B2199437
theorem B2678723 : Blo 976593 2678723 := bstep (se 1 (by rfl) ⟨2009042, by rfl⟩ : syracuseStep 2678723 = 4018085) B4018085
theorem B2514883 : Blo 976593 2514883 := bstep (se 1 (by rfl) ⟨1886162, by rfl⟩ : syracuseStep 2514883 = 3772325) B3772325
theorem B1466321 : Blo 976593 1466321 := bstep (se 2 (by rfl) ⟨549870, by rfl⟩ : syracuseStep 1466321 = 1099741) B1099741
theorem B1466339 : Blo 976593 1466339 := bstep (se 1 (by rfl) ⟨1099754, by rfl⟩ : syracuseStep 1466339 = 2199509) B2199509
theorem B1466369 : Blo 976593 1466369 := bstep (se 2 (by rfl) ⟨549888, by rfl⟩ : syracuseStep 1466369 = 1099777) B1099777
theorem B1466387 : Blo 976593 1466387 := bstep (se 1 (by rfl) ⟨1099790, by rfl⟩ : syracuseStep 1466387 = 2199581) B2199581
theorem B1237027 : Blo 976593 1237027 := bstep (se 1 (by rfl) ⟨927770, by rfl⟩ : syracuseStep 1237027 = 1855541) B1855541
theorem B2088995 : Blo 976593 2088995 := bstep (se 1 (by rfl) ⟨1566746, by rfl⟩ : syracuseStep 2088995 = 3133493) B3133493
theorem B1466417 : Blo 976593 1466417 := bstep (se 2 (by rfl) ⟨549906, by rfl⟩ : syracuseStep 1466417 = 1099813) B1099813
theorem B1466435 : Blo 976593 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B1466465 : Blo 976593 1466465 := bstep (se 2 (by rfl) ⟨549924, by rfl⟩ : syracuseStep 1466465 = 1099849) B1099849
theorem B1466483 : Blo 976593 1466483 := bstep (se 1 (by rfl) ⟨1099862, by rfl⟩ : syracuseStep 1466483 = 2199725) B2199725
theorem B1237123 : Blo 976593 1237123 := bstep (se 1 (by rfl) ⟨927842, by rfl⟩ : syracuseStep 1237123 = 1855685) B1855685
theorem B1466513 : Blo 976593 1466513 := bstep (se 2 (by rfl) ⟨549942, by rfl⟩ : syracuseStep 1466513 = 1099885) B1099885
theorem B1466531 : Blo 976593 1466531 := bstep (se 1 (by rfl) ⟨1099898, by rfl⟩ : syracuseStep 1466531 = 2199797) B2199797
theorem B1466561 : Blo 976593 1466561 := bstep (se 2 (by rfl) ⟨549960, by rfl⟩ : syracuseStep 1466561 = 1099921) B1099921
theorem B2646211 : Blo 976593 2646211 := bstep (se 1 (by rfl) ⟨1984658, by rfl⟩ : syracuseStep 2646211 = 3969317) B3969317
theorem B1466579 : Blo 976593 1466579 := bstep (se 1 (by rfl) ⟨1099934, by rfl⟩ : syracuseStep 1466579 = 2199869) B2199869
theorem B3301613 : Blo 976593 3301613 := bstep (se 3 (by rfl) ⟨619052, by rfl⟩ : syracuseStep 3301613 = 1238105) B1238105
theorem B1466609 : Blo 976593 1466609 := bstep (se 2 (by rfl) ⟨549978, by rfl⟩ : syracuseStep 1466609 = 1099957) B1099957
theorem B11297009 : Blo 976593 11297009 := bstep (se 2 (by rfl) ⟨4236378, by rfl⟩ : syracuseStep 11297009 = 8472757) B8472757
theorem B1564915 : Blo 976593 1564915 := bstep (se 1 (by rfl) ⟨1173686, by rfl⟩ : syracuseStep 1564915 = 2347373) B2347373
theorem B1466627 : Blo 976593 1466627 := bstep (se 1 (by rfl) ⟨1099970, by rfl⟩ : syracuseStep 1466627 = 2199941) B2199941
theorem B1466657 : Blo 976593 1466657 := bstep (se 2 (by rfl) ⟨549996, by rfl⟩ : syracuseStep 1466657 = 1099993) B1099993
theorem B3301667 : Blo 976593 3301667 := bstep (se 1 (by rfl) ⟨2476250, by rfl⟩ : syracuseStep 3301667 = 4952501) B4952501
theorem B1466675 : Blo 976593 1466675 := bstep (se 1 (by rfl) ⟨1100006, by rfl⟩ : syracuseStep 1466675 = 2200013) B2200013
theorem B1466705 : Blo 976593 1466705 := bstep (se 2 (by rfl) ⟨550014, by rfl⟩ : syracuseStep 1466705 = 1100029) B1100029
theorem B1466723 : Blo 976593 1466723 := bstep (se 1 (by rfl) ⟨1100042, by rfl⟩ : syracuseStep 1466723 = 2200085) B2200085
theorem B1466753 : Blo 976593 1466753 := bstep (se 2 (by rfl) ⟨550032, by rfl⟩ : syracuseStep 1466753 = 1100065) B1100065
theorem B1466771 : Blo 976593 1466771 := bstep (se 1 (by rfl) ⟨1100078, by rfl⟩ : syracuseStep 1466771 = 2200157) B2200157
theorem B1466801 : Blo 976593 1466801 := bstep (se 2 (by rfl) ⟨550050, by rfl⟩ : syracuseStep 1466801 = 1100101) B1100101
theorem B1466819 : Blo 976593 1466819 := bstep (se 1 (by rfl) ⟨1100114, by rfl⟩ : syracuseStep 1466819 = 2200229) B2200229
theorem B1466849 : Blo 976593 1466849 := bstep (se 2 (by rfl) ⟨550068, by rfl⟩ : syracuseStep 1466849 = 1100137) B1100137
theorem B1565171 : Blo 976593 1565171 := bstep (se 1 (by rfl) ⟨1173878, by rfl⟩ : syracuseStep 1565171 = 2347757) B2347757
theorem B1466867 : Blo 976593 1466867 := bstep (se 1 (by rfl) ⟨1100150, by rfl⟩ : syracuseStep 1466867 = 2200301) B2200301
theorem B4186637 : Blo 976593 4186637 := bstep (se 3 (by rfl) ⟨784994, by rfl⟩ : syracuseStep 4186637 = 1569989) B1569989
theorem B1466897 : Blo 976593 1466897 := bstep (se 2 (by rfl) ⟨550086, by rfl⟩ : syracuseStep 1466897 = 1100173) B1100173
theorem B1466915 : Blo 976593 1466915 := bstep (se 1 (by rfl) ⟨1100186, by rfl⟩ : syracuseStep 1466915 = 2200373) B2200373
theorem B1761841 : Blo 976593 1761841 := bstep (se 2 (by rfl) ⟨660690, by rfl⟩ : syracuseStep 1761841 = 1321381) B1321381
theorem B3301937 : Blo 976593 3301937 := bstep (se 2 (by rfl) ⟨1238226, by rfl⟩ : syracuseStep 3301937 = 2476453) B2476453
theorem B1466945 : Blo 976593 1466945 := bstep (se 2 (by rfl) ⟨550104, by rfl⟩ : syracuseStep 1466945 = 1100209) B1100209
theorem B2515537 : Blo 976593 2515537 := bstep (se 2 (by rfl) ⟨943326, by rfl⟩ : syracuseStep 2515537 = 1886653) B1886653
theorem B1466963 : Blo 976593 1466963 := bstep (se 1 (by rfl) ⟨1100222, by rfl⟩ : syracuseStep 1466963 = 2200445) B2200445
theorem B1466993 : Blo 976593 1466993 := bstep (se 2 (by rfl) ⟨550122, by rfl⟩ : syracuseStep 1466993 = 1100245) B1100245
theorem B1237619 : Blo 976593 1237619 := bstep (se 1 (by rfl) ⟨928214, by rfl⟩ : syracuseStep 1237619 = 1856429) B1856429
theorem B1467011 : Blo 976593 1467011 := bstep (se 1 (by rfl) ⟨1100258, by rfl⟩ : syracuseStep 1467011 = 2200517) B2200517
theorem B1860241 : Blo 976593 1860241 := bstep (se 2 (by rfl) ⟨697590, by rfl⟩ : syracuseStep 1860241 = 1395181) B1395181
theorem B1467041 : Blo 976593 1467041 := bstep (se 2 (by rfl) ⟨550140, by rfl⟩ : syracuseStep 1467041 = 1100281) B1100281
theorem B1467059 : Blo 976593 1467059 := bstep (se 1 (by rfl) ⟨1100294, by rfl⟩ : syracuseStep 1467059 = 2200589) B2200589
theorem B1467089 : Blo 976593 1467089 := bstep (se 2 (by rfl) ⟨550158, by rfl⟩ : syracuseStep 1467089 = 1100317) B1100317
theorem B1467107 : Blo 976593 1467107 := bstep (se 1 (by rfl) ⟨1100330, by rfl⟩ : syracuseStep 1467107 = 2200661) B2200661
theorem B1467137 : Blo 976593 1467137 := bstep (se 2 (by rfl) ⟨550176, by rfl⟩ : syracuseStep 1467137 = 1100353) B1100353
theorem B1467155 : Blo 976593 1467155 := bstep (se 1 (by rfl) ⟨1100366, by rfl⟩ : syracuseStep 1467155 = 2200733) B2200733
theorem B1467185 : Blo 976593 1467185 := bstep (se 2 (by rfl) ⟨550194, by rfl⟩ : syracuseStep 1467185 = 1100389) B1100389
theorem B1860401 : Blo 976593 1860401 := bstep (se 2 (by rfl) ⟨697650, by rfl⟩ : syracuseStep 1860401 = 1395301) B1395301
theorem B1467203 : Blo 976593 1467203 := bstep (se 1 (by rfl) ⟨1100402, by rfl⟩ : syracuseStep 1467203 = 2200805) B2200805
theorem B1467233 : Blo 976593 1467233 := bstep (se 2 (by rfl) ⟨550212, by rfl⟩ : syracuseStep 1467233 = 1100425) B1100425
theorem B1467251 : Blo 976593 1467251 := bstep (se 1 (by rfl) ⟨1100438, by rfl⟩ : syracuseStep 1467251 = 2200877) B2200877
theorem B1467281 : Blo 976593 1467281 := bstep (se 2 (by rfl) ⟨550230, by rfl⟩ : syracuseStep 1467281 = 1100461) B1100461
theorem B1467299 : Blo 976593 1467299 := bstep (se 1 (by rfl) ⟨1100474, by rfl⟩ : syracuseStep 1467299 = 2200949) B2200949
theorem B1467329 : Blo 976593 1467329 := bstep (se 2 (by rfl) ⟨550248, by rfl⟩ : syracuseStep 1467329 = 1100497) B1100497
theorem B1467347 : Blo 976593 1467347 := bstep (se 1 (by rfl) ⟨1100510, by rfl⟩ : syracuseStep 1467347 = 2201021) B2201021
theorem B5563363 : Blo 976593 5563363 := bstep (se 1 (by rfl) ⟨4172522, by rfl⟩ : syracuseStep 5563363 = 8345045) B8345045
theorem B1467377 : Blo 976593 1467377 := bstep (se 2 (by rfl) ⟨550266, by rfl⟩ : syracuseStep 1467377 = 1100533) B1100533
theorem B1467395 : Blo 976593 1467395 := bstep (se 1 (by rfl) ⟨1100546, by rfl⟩ : syracuseStep 1467395 = 2201093) B2201093
theorem B1467425 : Blo 976593 1467425 := bstep (se 2 (by rfl) ⟨550284, by rfl⟩ : syracuseStep 1467425 = 1100569) B1100569
theorem B1467443 : Blo 976593 1467443 := bstep (se 1 (by rfl) ⟨1100582, by rfl⟩ : syracuseStep 1467443 = 2201165) B2201165
theorem B3302477 : Blo 976593 3302477 := bstep (se 3 (by rfl) ⟨619214, by rfl⟩ : syracuseStep 3302477 = 1238429) B1238429
theorem B1467473 : Blo 976593 1467473 := bstep (se 2 (by rfl) ⟨550302, by rfl⟩ : syracuseStep 1467473 = 1100605) B1100605
theorem B1467491 : Blo 976593 1467491 := bstep (se 1 (by rfl) ⟨1100618, by rfl⟩ : syracuseStep 1467491 = 2201237) B2201237
theorem B1467521 : Blo 976593 1467521 := bstep (se 2 (by rfl) ⟨550320, by rfl⟩ : syracuseStep 1467521 = 1100641) B1100641
theorem B3302531 : Blo 976593 3302531 := bstep (se 1 (by rfl) ⟨2476898, by rfl⟩ : syracuseStep 3302531 = 4953797) B4953797
theorem B1467539 : Blo 976593 1467539 := bstep (se 1 (by rfl) ⟨1100654, by rfl⟩ : syracuseStep 1467539 = 2201309) B2201309
theorem B1467569 : Blo 976593 1467569 := bstep (se 2 (by rfl) ⟨550338, by rfl⟩ : syracuseStep 1467569 = 1100677) B1100677
theorem B1565875 : Blo 976593 1565875 := bstep (se 1 (by rfl) ⟨1174406, by rfl⟩ : syracuseStep 1565875 = 2348813) B2348813
theorem B1467587 : Blo 976593 1467587 := bstep (se 1 (by rfl) ⟨1100690, by rfl⟩ : syracuseStep 1467587 = 2201381) B2201381
theorem B1860803 : Blo 976593 1860803 := bstep (se 1 (by rfl) ⟨1395602, by rfl⟩ : syracuseStep 1860803 = 2791205) B2791205
theorem B1467617 : Blo 976593 1467617 := bstep (se 2 (by rfl) ⟨550356, by rfl⟩ : syracuseStep 1467617 = 1100713) B1100713
theorem B1467635 : Blo 976593 1467635 := bstep (se 1 (by rfl) ⟨1100726, by rfl⟩ : syracuseStep 1467635 = 2201453) B2201453
theorem B1467665 : Blo 976593 1467665 := bstep (se 2 (by rfl) ⟨550374, by rfl⟩ : syracuseStep 1467665 = 1100749) B1100749
theorem B1467683 : Blo 976593 1467683 := bstep (se 1 (by rfl) ⟨1100762, by rfl⟩ : syracuseStep 1467683 = 2201525) B2201525
theorem B3138851 : Blo 976593 3138851 := bstep (se 1 (by rfl) ⟨2354138, by rfl⟩ : syracuseStep 3138851 = 4708277) B4708277
theorem B2647345 : Blo 976593 2647345 := bstep (se 2 (by rfl) ⟨992754, by rfl⟩ : syracuseStep 2647345 = 1985509) B1985509
theorem B1238323 : Blo 976593 1238323 := bstep (se 1 (by rfl) ⟨928742, by rfl⟩ : syracuseStep 1238323 = 1857485) B1857485
theorem B1467713 : Blo 976593 1467713 := bstep (se 2 (by rfl) ⟨550392, by rfl⟩ : syracuseStep 1467713 = 1100785) B1100785
theorem B1467731 : Blo 976593 1467731 := bstep (se 1 (by rfl) ⟨1100798, by rfl⟩ : syracuseStep 1467731 = 2201597) B2201597
theorem B1467761 : Blo 976593 1467761 := bstep (se 2 (by rfl) ⟨550410, by rfl⟩ : syracuseStep 1467761 = 1100821) B1100821
theorem B1467779 : Blo 976593 1467779 := bstep (se 1 (by rfl) ⟨1100834, by rfl⟩ : syracuseStep 1467779 = 2201669) B2201669
theorem B1762705 : Blo 976593 1762705 := bstep (se 2 (by rfl) ⟨661014, by rfl⟩ : syracuseStep 1762705 = 1322029) B1322029
theorem B3302801 : Blo 976593 3302801 := bstep (se 2 (by rfl) ⟨1238550, by rfl⟩ : syracuseStep 3302801 = 2477101) B2477101
theorem B1238419 : Blo 976593 1238419 := bstep (se 1 (by rfl) ⟨928814, by rfl⟩ : syracuseStep 1238419 = 1857629) B1857629
theorem B1467809 : Blo 976593 1467809 := bstep (se 2 (by rfl) ⟨550428, by rfl⟩ : syracuseStep 1467809 = 1100857) B1100857
theorem B1467827 : Blo 976593 1467827 := bstep (se 1 (by rfl) ⟨1100870, by rfl⟩ : syracuseStep 1467827 = 2201741) B2201741
theorem B1566145 : Blo 976593 1566145 := bstep (se 2 (by rfl) ⟨587304, by rfl⟩ : syracuseStep 1566145 = 1174609) B1174609
theorem B1467857 : Blo 976593 1467857 := bstep (se 2 (by rfl) ⟨550446, by rfl⟩ : syracuseStep 1467857 = 1100893) B1100893
theorem B1467875 : Blo 976593 1467875 := bstep (se 1 (by rfl) ⟨1100906, by rfl⟩ : syracuseStep 1467875 = 2201813) B2201813
theorem B5563889 : Blo 976593 5563889 := bstep (se 2 (by rfl) ⟨2086458, by rfl⟩ : syracuseStep 5563889 = 4172917) B4172917
theorem B1566209 : Blo 976593 1566209 := bstep (se 2 (by rfl) ⟨587328, by rfl⟩ : syracuseStep 1566209 = 1174657) B1174657
theorem B1467905 : Blo 976593 1467905 := bstep (se 2 (by rfl) ⟨550464, by rfl⟩ : syracuseStep 1467905 = 1100929) B1100929
theorem B1467923 : Blo 976593 1467923 := bstep (se 1 (by rfl) ⟨1100942, by rfl⟩ : syracuseStep 1467923 = 2201885) B2201885
theorem B1467953 : Blo 976593 1467953 := bstep (se 2 (by rfl) ⟨550482, by rfl⟩ : syracuseStep 1467953 = 1100965) B1100965
theorem B1467971 : Blo 976593 1467971 := bstep (se 1 (by rfl) ⟨1100978, by rfl⟩ : syracuseStep 1467971 = 2201957) B2201957
theorem B1468001 : Blo 976593 1468001 := bstep (se 2 (by rfl) ⟨550500, by rfl⟩ : syracuseStep 1468001 = 1101001) B1101001
theorem B1468019 : Blo 976593 1468019 := bstep (se 1 (by rfl) ⟨1101014, by rfl⟩ : syracuseStep 1468019 = 2202029) B2202029
theorem B2385539 : Blo 976593 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B1468049 : Blo 976593 1468049 := bstep (se 2 (by rfl) ⟨550518, by rfl⟩ : syracuseStep 1468049 = 1101037) B1101037
theorem B1468067 : Blo 976593 1468067 := bstep (se 1 (by rfl) ⟨1101050, by rfl⟩ : syracuseStep 1468067 = 2202101) B2202101
theorem B1468097 : Blo 976593 1468097 := bstep (se 2 (by rfl) ⟨550536, by rfl⟩ : syracuseStep 1468097 = 1101073) B1101073
theorem B976595 : Blo 976593 976595 := bstep (se 1 (by rfl) ⟨732446, by rfl⟩ : syracuseStep 976595 = 1464893) B1464893
theorem B1468115 : Blo 976593 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B976611 : Blo 976593 976611 := bstep (se 1 (by rfl) ⟨732458, by rfl⟩ : syracuseStep 976611 = 1464917) B1464917
theorem B1468145 : Blo 976593 1468145 := bstep (se 2 (by rfl) ⟨550554, by rfl⟩ : syracuseStep 1468145 = 1101109) B1101109
theorem B976627 : Blo 976593 976627 := bstep (se 1 (by rfl) ⟨732470, by rfl⟩ : syracuseStep 976627 = 1464941) B1464941
theorem B976643 : Blo 976593 976643 := bstep (se 1 (by rfl) ⟨732482, by rfl⟩ : syracuseStep 976643 = 1464965) B1464965
theorem B2975491 : Blo 976593 2975491 := bstep (se 1 (by rfl) ⟨2231618, by rfl⟩ : syracuseStep 2975491 = 4463237) B4463237
theorem B1468163 : Blo 976593 1468163 := bstep (se 1 (by rfl) ⟨1101122, by rfl⟩ : syracuseStep 1468163 = 2202245) B2202245
theorem B976659 : Blo 976593 976659 := bstep (se 1 (by rfl) ⟨732494, by rfl⟩ : syracuseStep 976659 = 1464989) B1464989
theorem B1468193 : Blo 976593 1468193 := bstep (se 2 (by rfl) ⟨550572, by rfl⟩ : syracuseStep 1468193 = 1101145) B1101145
theorem B976675 : Blo 976593 976675 := bstep (se 1 (by rfl) ⟨732506, by rfl⟩ : syracuseStep 976675 = 1465013) B1465013
theorem B976691 : Blo 976593 976691 := bstep (se 1 (by rfl) ⟨732518, by rfl⟩ : syracuseStep 976691 = 1465037) B1465037
theorem B1468211 : Blo 976593 1468211 := bstep (se 1 (by rfl) ⟨1101158, by rfl⟩ : syracuseStep 1468211 = 2202317) B2202317
theorem B976707 : Blo 976593 976707 := bstep (se 1 (by rfl) ⟨732530, by rfl⟩ : syracuseStep 976707 = 1465061) B1465061
theorem B1468241 : Blo 976593 1468241 := bstep (se 2 (by rfl) ⟨550590, by rfl⟩ : syracuseStep 1468241 = 1101181) B1101181
theorem B976723 : Blo 976593 976723 := bstep (se 1 (by rfl) ⟨732542, by rfl⟩ : syracuseStep 976723 = 1465085) B1465085
theorem B976739 : Blo 976593 976739 := bstep (se 1 (by rfl) ⟨732554, by rfl⟩ : syracuseStep 976739 = 1465109) B1465109
theorem B1468259 : Blo 976593 1468259 := bstep (se 1 (by rfl) ⟨1101194, by rfl⟩ : syracuseStep 1468259 = 2202389) B2202389
theorem B976755 : Blo 976593 976755 := bstep (se 1 (by rfl) ⟨732566, by rfl⟩ : syracuseStep 976755 = 1465133) B1465133
theorem B1468289 : Blo 976593 1468289 := bstep (se 2 (by rfl) ⟨550608, by rfl⟩ : syracuseStep 1468289 = 1101217) B1101217
theorem B1173379 : Blo 976593 1173379 := bstep (se 1 (by rfl) ⟨880034, by rfl⟩ : syracuseStep 1173379 = 1760069) B1760069
theorem B976771 : Blo 976593 976771 := bstep (se 1 (by rfl) ⟨732578, by rfl⟩ : syracuseStep 976771 = 1465157) B1465157
theorem B1238915 : Blo 976593 1238915 := bstep (se 1 (by rfl) ⟨929186, by rfl⟩ : syracuseStep 1238915 = 1858373) B1858373
theorem B976787 : Blo 976593 976787 := bstep (se 1 (by rfl) ⟨732590, by rfl⟩ : syracuseStep 976787 = 1465181) B1465181
theorem B1468307 : Blo 976593 1468307 := bstep (se 1 (by rfl) ⟨1101230, by rfl⟩ : syracuseStep 1468307 = 2202461) B2202461
theorem B976803 : Blo 976593 976803 := bstep (se 1 (by rfl) ⟨732602, by rfl⟩ : syracuseStep 976803 = 1465205) B1465205
theorem B3303341 : Blo 976593 3303341 := bstep (se 3 (by rfl) ⟨619376, by rfl⟩ : syracuseStep 3303341 = 1238753) B1238753
theorem B1468337 : Blo 976593 1468337 := bstep (se 2 (by rfl) ⟨550626, by rfl⟩ : syracuseStep 1468337 = 1101253) B1101253
theorem B976819 : Blo 976593 976819 := bstep (se 1 (by rfl) ⟨732614, by rfl⟩ : syracuseStep 976819 = 1465229) B1465229
theorem B976835 : Blo 976593 976835 := bstep (se 1 (by rfl) ⟨732626, by rfl⟩ : syracuseStep 976835 = 1465253) B1465253
theorem B1468355 : Blo 976593 1468355 := bstep (se 1 (by rfl) ⟨1101266, by rfl⟩ : syracuseStep 1468355 = 2202533) B2202533
theorem B976851 : Blo 976593 976851 := bstep (se 1 (by rfl) ⟨732638, by rfl⟩ : syracuseStep 976851 = 1465277) B1465277
theorem B1468385 : Blo 976593 1468385 := bstep (se 2 (by rfl) ⟨550644, by rfl⟩ : syracuseStep 1468385 = 1101289) B1101289
theorem B976867 : Blo 976593 976867 := bstep (se 1 (by rfl) ⟨732650, by rfl⟩ : syracuseStep 976867 = 1465301) B1465301
theorem B3303395 : Blo 976593 3303395 := bstep (se 1 (by rfl) ⟨2477546, by rfl⟩ : syracuseStep 3303395 = 4955093) B4955093
theorem B976883 : Blo 976593 976883 := bstep (se 1 (by rfl) ⟨732662, by rfl⟩ : syracuseStep 976883 = 1465325) B1465325
theorem B1468403 : Blo 976593 1468403 := bstep (se 1 (by rfl) ⟨1101302, by rfl⟩ : syracuseStep 1468403 = 2202605) B2202605
theorem B976899 : Blo 976593 976899 := bstep (se 1 (by rfl) ⟨732674, by rfl⟩ : syracuseStep 976899 = 1465349) B1465349
theorem B1468433 : Blo 976593 1468433 := bstep (se 2 (by rfl) ⟨550662, by rfl⟩ : syracuseStep 1468433 = 1101325) B1101325
theorem B976915 : Blo 976593 976915 := bstep (se 1 (by rfl) ⟨732686, by rfl⟩ : syracuseStep 976915 = 1465373) B1465373
theorem B976931 : Blo 976593 976931 := bstep (se 1 (by rfl) ⟨732698, by rfl⟩ : syracuseStep 976931 = 1465397) B1465397
theorem B1468451 : Blo 976593 1468451 := bstep (se 1 (by rfl) ⟨1101338, by rfl⟩ : syracuseStep 1468451 = 2202677) B2202677
theorem B976947 : Blo 976593 976947 := bstep (se 1 (by rfl) ⟨732710, by rfl⟩ : syracuseStep 976947 = 1465421) B1465421
theorem B1468481 : Blo 976593 1468481 := bstep (se 2 (by rfl) ⟨550680, by rfl⟩ : syracuseStep 1468481 = 1101361) B1101361
theorem B976963 : Blo 976593 976963 := bstep (se 1 (by rfl) ⟨732722, by rfl⟩ : syracuseStep 976963 = 1465445) B1465445
theorem B976979 : Blo 976593 976979 := bstep (se 1 (by rfl) ⟨732734, by rfl⟩ : syracuseStep 976979 = 1465469) B1465469
theorem B1468499 : Blo 976593 1468499 := bstep (se 1 (by rfl) ⟨1101374, by rfl⟩ : syracuseStep 1468499 = 2202749) B2202749
theorem B976995 : Blo 976593 976995 := bstep (se 1 (by rfl) ⟨732746, by rfl⟩ : syracuseStep 976995 = 1465493) B1465493
theorem B1468529 : Blo 976593 1468529 := bstep (se 2 (by rfl) ⟨550698, by rfl⟩ : syracuseStep 1468529 = 1101397) B1101397
theorem B977011 : Blo 976593 977011 := bstep (se 1 (by rfl) ⟨732758, by rfl⟩ : syracuseStep 977011 = 1465517) B1465517
theorem B977027 : Blo 976593 977027 := bstep (se 1 (by rfl) ⟨732770, by rfl⟩ : syracuseStep 977027 = 1465541) B1465541
theorem B1468547 : Blo 976593 1468547 := bstep (se 1 (by rfl) ⟨1101410, by rfl⟩ : syracuseStep 1468547 = 2202821) B2202821
theorem B977043 : Blo 976593 977043 := bstep (se 1 (by rfl) ⟨732782, by rfl⟩ : syracuseStep 977043 = 1465565) B1465565
theorem B1468577 : Blo 976593 1468577 := bstep (se 2 (by rfl) ⟨550716, by rfl⟩ : syracuseStep 1468577 = 1101433) B1101433
theorem B977059 : Blo 976593 977059 := bstep (se 1 (by rfl) ⟨732794, by rfl⟩ : syracuseStep 977059 = 1465589) B1465589
theorem B977075 : Blo 976593 977075 := bstep (se 1 (by rfl) ⟨732806, by rfl⟩ : syracuseStep 977075 = 1465613) B1465613
theorem B1468595 : Blo 976593 1468595 := bstep (se 1 (by rfl) ⟨1101446, by rfl⟩ : syracuseStep 1468595 = 2202893) B2202893
theorem B977091 : Blo 976593 977091 := bstep (se 1 (by rfl) ⟨732818, by rfl⟩ : syracuseStep 977091 = 1465637) B1465637
theorem B24176837 : Blo 976593 24176837 := bstep (se 4 (by rfl) ⟨2266578, by rfl⟩ : syracuseStep 24176837 = 4533157) B4533157
theorem B1468625 : Blo 976593 1468625 := bstep (se 2 (by rfl) ⟨550734, by rfl⟩ : syracuseStep 1468625 = 1101469) B1101469
theorem B2091217 : Blo 976593 2091217 := bstep (se 2 (by rfl) ⟨784206, by rfl⟩ : syracuseStep 2091217 = 1568413) B1568413
theorem B977107 : Blo 976593 977107 := bstep (se 1 (by rfl) ⟨732830, by rfl⟩ : syracuseStep 977107 = 1465661) B1465661
theorem B977123 : Blo 976593 977123 := bstep (se 1 (by rfl) ⟨732842, by rfl⟩ : syracuseStep 977123 = 1465685) B1465685
theorem B9038051 : Blo 976593 9038051 := bstep (se 1 (by rfl) ⟨6778538, by rfl⟩ : syracuseStep 9038051 = 13557077) B13557077
theorem B1468643 : Blo 976593 1468643 := bstep (se 1 (by rfl) ⟨1101482, by rfl⟩ : syracuseStep 1468643 = 2202965) B2202965
theorem B3303665 : Blo 976593 3303665 := bstep (se 2 (by rfl) ⟨1238874, by rfl⟩ : syracuseStep 3303665 = 2477749) B2477749
theorem B977139 : Blo 976593 977139 := bstep (se 1 (by rfl) ⟨732854, by rfl⟩ : syracuseStep 977139 = 1465709) B1465709
theorem B1468673 : Blo 976593 1468673 := bstep (se 2 (by rfl) ⟨550752, by rfl⟩ : syracuseStep 1468673 = 1101505) B1101505
theorem B977155 : Blo 976593 977155 := bstep (se 1 (by rfl) ⟨732866, by rfl⟩ : syracuseStep 977155 = 1465733) B1465733
theorem B977171 : Blo 976593 977171 := bstep (se 1 (by rfl) ⟨732878, by rfl⟩ : syracuseStep 977171 = 1465757) B1465757
theorem B1468691 : Blo 976593 1468691 := bstep (se 1 (by rfl) ⟨1101518, by rfl⟩ : syracuseStep 1468691 = 2203037) B2203037
theorem B977187 : Blo 976593 977187 := bstep (se 1 (by rfl) ⟨732890, by rfl⟩ : syracuseStep 977187 = 1465781) B1465781
theorem B1468721 : Blo 976593 1468721 := bstep (se 2 (by rfl) ⟨550770, by rfl⟩ : syracuseStep 1468721 = 1101541) B1101541
theorem B977203 : Blo 976593 977203 := bstep (se 1 (by rfl) ⟨732902, by rfl⟩ : syracuseStep 977203 = 1465805) B1465805
theorem B977219 : Blo 976593 977219 := bstep (se 1 (by rfl) ⟨732914, by rfl⟩ : syracuseStep 977219 = 1465829) B1465829
theorem B1468739 : Blo 976593 1468739 := bstep (se 1 (by rfl) ⟨1101554, by rfl⟩ : syracuseStep 1468739 = 2203109) B2203109
theorem B977235 : Blo 976593 977235 := bstep (se 1 (by rfl) ⟨732926, by rfl⟩ : syracuseStep 977235 = 1465853) B1465853
theorem B1468769 : Blo 976593 1468769 := bstep (se 2 (by rfl) ⟨550788, by rfl⟩ : syracuseStep 1468769 = 1101577) B1101577
theorem B977251 : Blo 976593 977251 := bstep (se 1 (by rfl) ⟨732938, by rfl⟩ : syracuseStep 977251 = 1465877) B1465877
theorem B977267 : Blo 976593 977267 := bstep (se 1 (by rfl) ⟨732950, by rfl⟩ : syracuseStep 977267 = 1465901) B1465901
theorem B1468787 : Blo 976593 1468787 := bstep (se 1 (by rfl) ⟨1101590, by rfl⟩ : syracuseStep 1468787 = 2203181) B2203181
theorem B977283 : Blo 976593 977283 := bstep (se 1 (by rfl) ⟨732962, by rfl⟩ : syracuseStep 977283 = 1465925) B1465925
theorem B1468817 : Blo 976593 1468817 := bstep (se 2 (by rfl) ⟨550806, by rfl⟩ : syracuseStep 1468817 = 1101613) B1101613
theorem B977299 : Blo 976593 977299 := bstep (se 1 (by rfl) ⟨732974, by rfl⟩ : syracuseStep 977299 = 1465949) B1465949
theorem B977315 : Blo 976593 977315 := bstep (se 1 (by rfl) ⟨732986, by rfl⟩ : syracuseStep 977315 = 1465973) B1465973
theorem B1468835 : Blo 976593 1468835 := bstep (se 1 (by rfl) ⟨1101626, by rfl⟩ : syracuseStep 1468835 = 2203253) B2203253
theorem B977331 : Blo 976593 977331 := bstep (se 1 (by rfl) ⟨732998, by rfl⟩ : syracuseStep 977331 = 1465997) B1465997
theorem B1468865 : Blo 976593 1468865 := bstep (se 2 (by rfl) ⟨550824, by rfl⟩ : syracuseStep 1468865 = 1101649) B1101649
theorem B977347 : Blo 976593 977347 := bstep (se 1 (by rfl) ⟨733010, by rfl⟩ : syracuseStep 977347 = 1466021) B1466021
theorem B977363 : Blo 976593 977363 := bstep (se 1 (by rfl) ⟨733022, by rfl⟩ : syracuseStep 977363 = 1466045) B1466045
theorem B1468883 : Blo 976593 1468883 := bstep (se 1 (by rfl) ⟨1101662, by rfl⟩ : syracuseStep 1468883 = 2203325) B2203325
theorem B977379 : Blo 976593 977379 := bstep (se 1 (by rfl) ⟨733034, by rfl⟩ : syracuseStep 977379 = 1466069) B1466069
theorem B1468913 : Blo 976593 1468913 := bstep (se 2 (by rfl) ⟨550842, by rfl⟩ : syracuseStep 1468913 = 1101685) B1101685
theorem B977395 : Blo 976593 977395 := bstep (se 1 (by rfl) ⟨733046, by rfl⟩ : syracuseStep 977395 = 1466093) B1466093
theorem B977411 : Blo 976593 977411 := bstep (se 1 (by rfl) ⟨733058, by rfl⟩ : syracuseStep 977411 = 1466117) B1466117
theorem B1468931 : Blo 976593 1468931 := bstep (se 1 (by rfl) ⟨1101698, by rfl⟩ : syracuseStep 1468931 = 2203397) B2203397
theorem B977427 : Blo 976593 977427 := bstep (se 1 (by rfl) ⟨733070, by rfl⟩ : syracuseStep 977427 = 1466141) B1466141
theorem B1468961 : Blo 976593 1468961 := bstep (se 2 (by rfl) ⟨550860, by rfl⟩ : syracuseStep 1468961 = 1101721) B1101721
theorem B977443 : Blo 976593 977443 := bstep (se 1 (by rfl) ⟨733082, by rfl⟩ : syracuseStep 977443 = 1466165) B1466165
theorem B1468979 : Blo 976593 1468979 := bstep (se 1 (by rfl) ⟨1101734, by rfl⟩ : syracuseStep 1468979 = 2203469) B2203469
theorem B977459 : Blo 976593 977459 := bstep (se 1 (by rfl) ⟨733094, by rfl⟩ : syracuseStep 977459 = 1466189) B1466189
theorem B977475 : Blo 976593 977475 := bstep (se 1 (by rfl) ⟨733106, by rfl⟩ : syracuseStep 977475 = 1466213) B1466213
theorem B1239619 : Blo 976593 1239619 := bstep (se 1 (by rfl) ⟨929714, by rfl⟩ : syracuseStep 1239619 = 1859429) B1859429
theorem B1469009 : Blo 976593 1469009 := bstep (se 2 (by rfl) ⟨550878, by rfl⟩ : syracuseStep 1469009 = 1101757) B1101757
theorem B1174099 : Blo 976593 1174099 := bstep (se 1 (by rfl) ⟨880574, by rfl⟩ : syracuseStep 1174099 = 1761149) B1761149
theorem B977491 : Blo 976593 977491 := bstep (se 1 (by rfl) ⟨733118, by rfl⟩ : syracuseStep 977491 = 1466237) B1466237
theorem B977507 : Blo 976593 977507 := bstep (se 1 (by rfl) ⟨733130, by rfl⟩ : syracuseStep 977507 = 1466261) B1466261
theorem B1469027 : Blo 976593 1469027 := bstep (se 1 (by rfl) ⟨1101770, by rfl⟩ : syracuseStep 1469027 = 2203541) B2203541
theorem B977523 : Blo 976593 977523 := bstep (se 1 (by rfl) ⟨733142, by rfl⟩ : syracuseStep 977523 = 1466285) B1466285
theorem B1469057 : Blo 976593 1469057 := bstep (se 2 (by rfl) ⟨550896, by rfl⟩ : syracuseStep 1469057 = 1101793) B1101793
theorem B977539 : Blo 976593 977539 := bstep (se 1 (by rfl) ⟨733154, by rfl⟩ : syracuseStep 977539 = 1466309) B1466309
theorem B977555 : Blo 976593 977555 := bstep (se 1 (by rfl) ⟨733166, by rfl⟩ : syracuseStep 977555 = 1466333) B1466333
theorem B1469075 : Blo 976593 1469075 := bstep (se 1 (by rfl) ⟨1101806, by rfl⟩ : syracuseStep 1469075 = 2203613) B2203613
theorem B977571 : Blo 976593 977571 := bstep (se 1 (by rfl) ⟨733178, by rfl⟩ : syracuseStep 977571 = 1466357) B1466357
theorem B1239715 : Blo 976593 1239715 := bstep (se 1 (by rfl) ⟨929786, by rfl⟩ : syracuseStep 1239715 = 1859573) B1859573
theorem B1469105 : Blo 976593 1469105 := bstep (se 2 (by rfl) ⟨550914, by rfl⟩ : syracuseStep 1469105 = 1101829) B1101829
theorem B1174195 : Blo 976593 1174195 := bstep (se 1 (by rfl) ⟨880646, by rfl⟩ : syracuseStep 1174195 = 1761293) B1761293
theorem B977587 : Blo 976593 977587 := bstep (se 1 (by rfl) ⟨733190, by rfl⟩ : syracuseStep 977587 = 1466381) B1466381
theorem B977603 : Blo 976593 977603 := bstep (se 1 (by rfl) ⟨733202, by rfl⟩ : syracuseStep 977603 = 1466405) B1466405
theorem B1469123 : Blo 976593 1469123 := bstep (se 1 (by rfl) ⟨1101842, by rfl⟩ : syracuseStep 1469123 = 2203685) B2203685
theorem B977619 : Blo 976593 977619 := bstep (se 1 (by rfl) ⟨733214, by rfl⟩ : syracuseStep 977619 = 1466429) B1466429
theorem B1469153 : Blo 976593 1469153 := bstep (se 2 (by rfl) ⟨550932, by rfl⟩ : syracuseStep 1469153 = 1101865) B1101865
theorem B977635 : Blo 976593 977635 := bstep (se 1 (by rfl) ⟨733226, by rfl⟩ : syracuseStep 977635 = 1466453) B1466453
theorem B977651 : Blo 976593 977651 := bstep (se 1 (by rfl) ⟨733238, by rfl⟩ : syracuseStep 977651 = 1466477) B1466477
theorem B1469171 : Blo 976593 1469171 := bstep (se 1 (by rfl) ⟨1101878, by rfl⟩ : syracuseStep 1469171 = 2203757) B2203757
theorem B977667 : Blo 976593 977667 := bstep (se 1 (by rfl) ⟨733250, by rfl⟩ : syracuseStep 977667 = 1466501) B1466501
theorem B3304205 : Blo 976593 3304205 := bstep (se 3 (by rfl) ⟨619538, by rfl⟩ : syracuseStep 3304205 = 1239077) B1239077
theorem B1469201 : Blo 976593 1469201 := bstep (se 2 (by rfl) ⟨550950, by rfl⟩ : syracuseStep 1469201 = 1101901) B1101901
theorem B977683 : Blo 976593 977683 := bstep (se 1 (by rfl) ⟨733262, by rfl⟩ : syracuseStep 977683 = 1466525) B1466525
theorem B977699 : Blo 976593 977699 := bstep (se 1 (by rfl) ⟨733274, by rfl⟩ : syracuseStep 977699 = 1466549) B1466549
theorem B1469219 : Blo 976593 1469219 := bstep (se 1 (by rfl) ⟨1101914, by rfl⟩ : syracuseStep 1469219 = 2203829) B2203829
theorem B977715 : Blo 976593 977715 := bstep (se 1 (by rfl) ⟨733286, by rfl⟩ : syracuseStep 977715 = 1466573) B1466573
theorem B1469249 : Blo 976593 1469249 := bstep (se 2 (by rfl) ⟨550968, by rfl⟩ : syracuseStep 1469249 = 1101937) B1101937
theorem B977731 : Blo 976593 977731 := bstep (se 1 (by rfl) ⟨733298, by rfl⟩ : syracuseStep 977731 = 1466597) B1466597
theorem B3304259 : Blo 976593 3304259 := bstep (se 1 (by rfl) ⟨2478194, by rfl⟩ : syracuseStep 3304259 = 4956389) B4956389
theorem B977747 : Blo 976593 977747 := bstep (se 1 (by rfl) ⟨733310, by rfl⟩ : syracuseStep 977747 = 1466621) B1466621
theorem B1469267 : Blo 976593 1469267 := bstep (se 1 (by rfl) ⟨1101950, by rfl⟩ : syracuseStep 1469267 = 2203901) B2203901
theorem B977763 : Blo 976593 977763 := bstep (se 1 (by rfl) ⟨733322, by rfl⟩ : syracuseStep 977763 = 1466645) B1466645
theorem B1469297 : Blo 976593 1469297 := bstep (se 2 (by rfl) ⟨550986, by rfl⟩ : syracuseStep 1469297 = 1101973) B1101973
theorem B977779 : Blo 976593 977779 := bstep (se 1 (by rfl) ⟨733334, by rfl⟩ : syracuseStep 977779 = 1466669) B1466669
theorem B977795 : Blo 976593 977795 := bstep (se 1 (by rfl) ⟨733346, by rfl⟩ : syracuseStep 977795 = 1466693) B1466693
theorem B1469315 : Blo 976593 1469315 := bstep (se 1 (by rfl) ⟨1101986, by rfl⟩ : syracuseStep 1469315 = 2203973) B2203973
theorem B977811 : Blo 976593 977811 := bstep (se 1 (by rfl) ⟨733358, by rfl⟩ : syracuseStep 977811 = 1466717) B1466717
theorem B1469345 : Blo 976593 1469345 := bstep (se 2 (by rfl) ⟨551004, by rfl⟩ : syracuseStep 1469345 = 1102009) B1102009
theorem B5565347 : Blo 976593 5565347 := bstep (se 1 (by rfl) ⟨4174010, by rfl⟩ : syracuseStep 5565347 = 8348021) B8348021
theorem B977827 : Blo 976593 977827 := bstep (se 1 (by rfl) ⟨733370, by rfl⟩ : syracuseStep 977827 = 1466741) B1466741
theorem B977843 : Blo 976593 977843 := bstep (se 1 (by rfl) ⟨733382, by rfl⟩ : syracuseStep 977843 = 1466765) B1466765
theorem B1469363 : Blo 976593 1469363 := bstep (se 1 (by rfl) ⟨1102022, by rfl⟩ : syracuseStep 1469363 = 2204045) B2204045
theorem B977859 : Blo 976593 977859 := bstep (se 1 (by rfl) ⟨733394, by rfl⟩ : syracuseStep 977859 = 1466789) B1466789
theorem B1469393 : Blo 976593 1469393 := bstep (se 2 (by rfl) ⟨551022, by rfl⟩ : syracuseStep 1469393 = 1102045) B1102045
theorem B977875 : Blo 976593 977875 := bstep (se 1 (by rfl) ⟨733406, by rfl⟩ : syracuseStep 977875 = 1466813) B1466813
theorem B977891 : Blo 976593 977891 := bstep (se 1 (by rfl) ⟨733418, by rfl⟩ : syracuseStep 977891 = 1466837) B1466837
theorem B1469411 : Blo 976593 1469411 := bstep (se 1 (by rfl) ⟨1102058, by rfl⟩ : syracuseStep 1469411 = 2204117) B2204117
theorem B977907 : Blo 976593 977907 := bstep (se 1 (by rfl) ⟨733430, by rfl⟩ : syracuseStep 977907 = 1466861) B1466861
theorem B1469441 : Blo 976593 1469441 := bstep (se 2 (by rfl) ⟨551040, by rfl⟩ : syracuseStep 1469441 = 1102081) B1102081
theorem B977923 : Blo 976593 977923 := bstep (se 1 (by rfl) ⟨733442, by rfl⟩ : syracuseStep 977923 = 1466885) B1466885
theorem B10742797 : Blo 976593 10742797 := bstep (se 3 (by rfl) ⟨2014274, by rfl⟩ : syracuseStep 10742797 = 4028549) B4028549
theorem B977939 : Blo 976593 977939 := bstep (se 1 (by rfl) ⟨733454, by rfl⟩ : syracuseStep 977939 = 1466909) B1466909
theorem B1207315 : Blo 976593 1207315 := bstep (se 1 (by rfl) ⟨905486, by rfl⟩ : syracuseStep 1207315 = 1810973) B1810973
theorem B1469459 : Blo 976593 1469459 := bstep (se 1 (by rfl) ⟨1102094, by rfl⟩ : syracuseStep 1469459 = 2204189) B2204189
theorem B977955 : Blo 976593 977955 := bstep (se 1 (by rfl) ⟨733466, by rfl⟩ : syracuseStep 977955 = 1466933) B1466933
theorem B1469489 : Blo 976593 1469489 := bstep (se 2 (by rfl) ⟨551058, by rfl⟩ : syracuseStep 1469489 = 1102117) B1102117
theorem B977971 : Blo 976593 977971 := bstep (se 1 (by rfl) ⟨733478, by rfl⟩ : syracuseStep 977971 = 1466957) B1466957
theorem B977987 : Blo 976593 977987 := bstep (se 1 (by rfl) ⟨733490, by rfl⟩ : syracuseStep 977987 = 1466981) B1466981
theorem B1469507 : Blo 976593 1469507 := bstep (se 1 (by rfl) ⟨1102130, by rfl⟩ : syracuseStep 1469507 = 2204261) B2204261
theorem B3304529 : Blo 976593 3304529 := bstep (se 2 (by rfl) ⟨1239198, by rfl⟩ : syracuseStep 3304529 = 2478397) B2478397
theorem B978003 : Blo 976593 978003 := bstep (se 1 (by rfl) ⟨733502, by rfl⟩ : syracuseStep 978003 = 1467005) B1467005
theorem B1469537 : Blo 976593 1469537 := bstep (se 2 (by rfl) ⟨551076, by rfl⟩ : syracuseStep 1469537 = 1102153) B1102153
theorem B978019 : Blo 976593 978019 := bstep (se 1 (by rfl) ⟨733514, by rfl⟩ : syracuseStep 978019 = 1467029) B1467029
theorem B978035 : Blo 976593 978035 := bstep (se 1 (by rfl) ⟨733526, by rfl⟩ : syracuseStep 978035 = 1467053) B1467053
theorem B1469555 : Blo 976593 1469555 := bstep (se 1 (by rfl) ⟨1102166, by rfl⟩ : syracuseStep 1469555 = 2204333) B2204333
theorem B978051 : Blo 976593 978051 := bstep (se 1 (by rfl) ⟨733538, by rfl⟩ : syracuseStep 978051 = 1467077) B1467077
theorem B1469585 : Blo 976593 1469585 := bstep (se 2 (by rfl) ⟨551094, by rfl⟩ : syracuseStep 1469585 = 1102189) B1102189
theorem B978067 : Blo 976593 978067 := bstep (se 1 (by rfl) ⟨733550, by rfl⟩ : syracuseStep 978067 = 1467101) B1467101
theorem B1240211 : Blo 976593 1240211 := bstep (se 1 (by rfl) ⟨930158, by rfl⟩ : syracuseStep 1240211 = 1860317) B1860317
theorem B978083 : Blo 976593 978083 := bstep (se 1 (by rfl) ⟨733562, by rfl⟩ : syracuseStep 978083 = 1467125) B1467125
theorem B1469603 : Blo 976593 1469603 := bstep (se 1 (by rfl) ⟨1102202, by rfl⟩ : syracuseStep 1469603 = 2204405) B2204405
theorem B978099 : Blo 976593 978099 := bstep (se 1 (by rfl) ⟨733574, by rfl⟩ : syracuseStep 978099 = 1467149) B1467149
theorem B1469633 : Blo 976593 1469633 := bstep (se 2 (by rfl) ⟨551112, by rfl⟩ : syracuseStep 1469633 = 1102225) B1102225
theorem B978115 : Blo 976593 978115 := bstep (se 1 (by rfl) ⟨733586, by rfl⟩ : syracuseStep 978115 = 1467173) B1467173
theorem B1567939 : Blo 976593 1567939 := bstep (se 1 (by rfl) ⟨1175954, by rfl⟩ : syracuseStep 1567939 = 2351909) B2351909
theorem B978131 : Blo 976593 978131 := bstep (se 1 (by rfl) ⟨733598, by rfl⟩ : syracuseStep 978131 = 1467197) B1467197
theorem B1469651 : Blo 976593 1469651 := bstep (se 1 (by rfl) ⟨1102238, by rfl⟩ : syracuseStep 1469651 = 2204477) B2204477
theorem B978147 : Blo 976593 978147 := bstep (se 1 (by rfl) ⟨733610, by rfl⟩ : syracuseStep 978147 = 1467221) B1467221
theorem B1469681 : Blo 976593 1469681 := bstep (se 2 (by rfl) ⟨551130, by rfl⟩ : syracuseStep 1469681 = 1102261) B1102261
theorem B978163 : Blo 976593 978163 := bstep (se 1 (by rfl) ⟨733622, by rfl⟩ : syracuseStep 978163 = 1467245) B1467245
theorem B978179 : Blo 976593 978179 := bstep (se 1 (by rfl) ⟨733634, by rfl⟩ : syracuseStep 978179 = 1467269) B1467269
theorem B1469699 : Blo 976593 1469699 := bstep (se 1 (by rfl) ⟨1102274, by rfl⟩ : syracuseStep 1469699 = 2204549) B2204549
theorem B978195 : Blo 976593 978195 := bstep (se 1 (by rfl) ⟨733646, by rfl⟩ : syracuseStep 978195 = 1467293) B1467293
theorem B1469729 : Blo 976593 1469729 := bstep (se 2 (by rfl) ⟨551148, by rfl⟩ : syracuseStep 1469729 = 1102297) B1102297
theorem B978211 : Blo 976593 978211 := bstep (se 1 (by rfl) ⟨733658, by rfl⟩ : syracuseStep 978211 = 1467317) B1467317
theorem B978227 : Blo 976593 978227 := bstep (se 1 (by rfl) ⟨733670, by rfl⟩ : syracuseStep 978227 = 1467341) B1467341
theorem B1469747 : Blo 976593 1469747 := bstep (se 1 (by rfl) ⟨1102310, by rfl⟩ : syracuseStep 1469747 = 2204621) B2204621
theorem B978243 : Blo 976593 978243 := bstep (se 1 (by rfl) ⟨733682, by rfl⟩ : syracuseStep 978243 = 1467365) B1467365
theorem B1469777 : Blo 976593 1469777 := bstep (se 2 (by rfl) ⟨551166, by rfl⟩ : syracuseStep 1469777 = 1102333) B1102333
theorem B978259 : Blo 976593 978259 := bstep (se 1 (by rfl) ⟨733694, by rfl⟩ : syracuseStep 978259 = 1467389) B1467389
theorem B978275 : Blo 976593 978275 := bstep (se 1 (by rfl) ⟨733706, by rfl⟩ : syracuseStep 978275 = 1467413) B1467413
theorem B1469795 : Blo 976593 1469795 := bstep (se 1 (by rfl) ⟨1102346, by rfl⟩ : syracuseStep 1469795 = 2204693) B2204693
theorem B3140977 : Blo 976593 3140977 := bstep (se 2 (by rfl) ⟨1177866, by rfl⟩ : syracuseStep 3140977 = 2355733) B2355733
theorem B978291 : Blo 976593 978291 := bstep (se 1 (by rfl) ⟨733718, by rfl⟩ : syracuseStep 978291 = 1467437) B1467437
theorem B1469825 : Blo 976593 1469825 := bstep (se 2 (by rfl) ⟨551184, by rfl⟩ : syracuseStep 1469825 = 1102369) B1102369
theorem B978307 : Blo 976593 978307 := bstep (se 1 (by rfl) ⟨733730, by rfl⟩ : syracuseStep 978307 = 1467461) B1467461
theorem B978323 : Blo 976593 978323 := bstep (se 1 (by rfl) ⟨733742, by rfl⟩ : syracuseStep 978323 = 1467485) B1467485
theorem B1469843 : Blo 976593 1469843 := bstep (se 1 (by rfl) ⟨1102382, by rfl⟩ : syracuseStep 1469843 = 2204765) B2204765
theorem B978339 : Blo 976593 978339 := bstep (se 1 (by rfl) ⟨733754, by rfl⟩ : syracuseStep 978339 = 1467509) B1467509
theorem B1469873 : Blo 976593 1469873 := bstep (se 2 (by rfl) ⟨551202, by rfl⟩ : syracuseStep 1469873 = 1102405) B1102405
theorem B978355 : Blo 976593 978355 := bstep (se 1 (by rfl) ⟨733766, by rfl⟩ : syracuseStep 978355 = 1467533) B1467533
theorem B978371 : Blo 976593 978371 := bstep (se 1 (by rfl) ⟨733778, by rfl⟩ : syracuseStep 978371 = 1467557) B1467557
theorem B1469891 : Blo 976593 1469891 := bstep (se 1 (by rfl) ⟨1102418, by rfl⟩ : syracuseStep 1469891 = 2204837) B2204837
theorem B978387 : Blo 976593 978387 := bstep (se 1 (by rfl) ⟨733790, by rfl⟩ : syracuseStep 978387 = 1467581) B1467581
theorem B1469921 : Blo 976593 1469921 := bstep (se 2 (by rfl) ⟨551220, by rfl⟩ : syracuseStep 1469921 = 1102441) B1102441
theorem B978403 : Blo 976593 978403 := bstep (se 1 (by rfl) ⟨733802, by rfl⟩ : syracuseStep 978403 = 1467605) B1467605
theorem B978419 : Blo 976593 978419 := bstep (se 1 (by rfl) ⟨733814, by rfl⟩ : syracuseStep 978419 = 1467629) B1467629
theorem B1469939 : Blo 976593 1469939 := bstep (se 1 (by rfl) ⟨1102454, by rfl⟩ : syracuseStep 1469939 = 2204909) B2204909
theorem B978435 : Blo 976593 978435 := bstep (se 1 (by rfl) ⟨733826, by rfl⟩ : syracuseStep 978435 = 1467653) B1467653
theorem B1469969 : Blo 976593 1469969 := bstep (se 2 (by rfl) ⟨551238, by rfl⟩ : syracuseStep 1469969 = 1102477) B1102477
theorem B978451 : Blo 976593 978451 := bstep (se 1 (by rfl) ⟨733838, by rfl⟩ : syracuseStep 978451 = 1467677) B1467677
theorem B978467 : Blo 976593 978467 := bstep (se 1 (by rfl) ⟨733850, by rfl⟩ : syracuseStep 978467 = 1467701) B1467701
theorem B1469987 : Blo 976593 1469987 := bstep (se 1 (by rfl) ⟨1102490, by rfl⟩ : syracuseStep 1469987 = 2204981) B2204981
theorem B978483 : Blo 976593 978483 := bstep (se 1 (by rfl) ⟨733862, by rfl⟩ : syracuseStep 978483 = 1467725) B1467725
theorem B1470017 : Blo 976593 1470017 := bstep (se 2 (by rfl) ⟨551256, by rfl⟩ : syracuseStep 1470017 = 1102513) B1102513
theorem B978499 : Blo 976593 978499 := bstep (se 1 (by rfl) ⟨733874, by rfl⟩ : syracuseStep 978499 = 1467749) B1467749
theorem B978515 : Blo 976593 978515 := bstep (se 1 (by rfl) ⟨733886, by rfl⟩ : syracuseStep 978515 = 1467773) B1467773
theorem B1470035 : Blo 976593 1470035 := bstep (se 1 (by rfl) ⟨1102526, by rfl⟩ : syracuseStep 1470035 = 2205053) B2205053
theorem B978531 : Blo 976593 978531 := bstep (se 1 (by rfl) ⟨733898, by rfl⟩ : syracuseStep 978531 = 1467797) B1467797
theorem B3305069 : Blo 976593 3305069 := bstep (se 3 (by rfl) ⟨619700, by rfl⟩ : syracuseStep 3305069 = 1239401) B1239401
theorem B1470065 : Blo 976593 1470065 := bstep (se 2 (by rfl) ⟨551274, by rfl⟩ : syracuseStep 1470065 = 1102549) B1102549
theorem B978547 : Blo 976593 978547 := bstep (se 1 (by rfl) ⟨733910, by rfl⟩ : syracuseStep 978547 = 1467821) B1467821
theorem B978563 : Blo 976593 978563 := bstep (se 1 (by rfl) ⟨733922, by rfl⟩ : syracuseStep 978563 = 1467845) B1467845
theorem B1568387 : Blo 976593 1568387 := bstep (se 1 (by rfl) ⟨1176290, by rfl⟩ : syracuseStep 1568387 = 2352581) B2352581
theorem B1470083 : Blo 976593 1470083 := bstep (se 1 (by rfl) ⟨1102562, by rfl⟩ : syracuseStep 1470083 = 2205125) B2205125
theorem B978579 : Blo 976593 978579 := bstep (se 1 (by rfl) ⟨733934, by rfl⟩ : syracuseStep 978579 = 1467869) B1467869
theorem B1470113 : Blo 976593 1470113 := bstep (se 2 (by rfl) ⟨551292, by rfl⟩ : syracuseStep 1470113 = 1102585) B1102585
theorem B978595 : Blo 976593 978595 := bstep (se 1 (by rfl) ⟨733946, by rfl⟩ : syracuseStep 978595 = 1467893) B1467893
theorem B3305123 : Blo 976593 3305123 := bstep (se 1 (by rfl) ⟨2478842, by rfl⟩ : syracuseStep 3305123 = 4957685) B4957685
theorem B978611 : Blo 976593 978611 := bstep (se 1 (by rfl) ⟨733958, by rfl⟩ : syracuseStep 978611 = 1467917) B1467917
theorem B1470131 : Blo 976593 1470131 := bstep (se 1 (by rfl) ⟨1102598, by rfl⟩ : syracuseStep 1470131 = 2205197) B2205197
theorem B978627 : Blo 976593 978627 := bstep (se 1 (by rfl) ⟨733970, by rfl⟩ : syracuseStep 978627 = 1467941) B1467941
theorem B1470161 : Blo 976593 1470161 := bstep (se 2 (by rfl) ⟨551310, by rfl⟩ : syracuseStep 1470161 = 1102621) B1102621
theorem B978643 : Blo 976593 978643 := bstep (se 1 (by rfl) ⟨733982, by rfl⟩ : syracuseStep 978643 = 1467965) B1467965
theorem B978659 : Blo 976593 978659 := bstep (se 1 (by rfl) ⟨733994, by rfl⟩ : syracuseStep 978659 = 1467989) B1467989
theorem B1470179 : Blo 976593 1470179 := bstep (se 1 (by rfl) ⟨1102634, by rfl⟩ : syracuseStep 1470179 = 2205269) B2205269
theorem B978675 : Blo 976593 978675 := bstep (se 1 (by rfl) ⟨734006, by rfl⟩ : syracuseStep 978675 = 1468013) B1468013
theorem B1470209 : Blo 976593 1470209 := bstep (se 2 (by rfl) ⟨551328, by rfl⟩ : syracuseStep 1470209 = 1102657) B1102657
theorem B978691 : Blo 976593 978691 := bstep (se 1 (by rfl) ⟨734018, by rfl⟩ : syracuseStep 978691 = 1468037) B1468037
theorem B978707 : Blo 976593 978707 := bstep (se 1 (by rfl) ⟨734030, by rfl⟩ : syracuseStep 978707 = 1468061) B1468061
theorem B1470227 : Blo 976593 1470227 := bstep (se 1 (by rfl) ⟨1102670, by rfl⟩ : syracuseStep 1470227 = 2205341) B2205341
theorem B978723 : Blo 976593 978723 := bstep (se 1 (by rfl) ⟨734042, by rfl⟩ : syracuseStep 978723 = 1468085) B1468085
theorem B1470257 : Blo 976593 1470257 := bstep (se 2 (by rfl) ⟨551346, by rfl⟩ : syracuseStep 1470257 = 1102693) B1102693
theorem B978739 : Blo 976593 978739 := bstep (se 1 (by rfl) ⟨734054, by rfl⟩ : syracuseStep 978739 = 1468109) B1468109
theorem B978755 : Blo 976593 978755 := bstep (se 1 (by rfl) ⟨734066, by rfl⟩ : syracuseStep 978755 = 1468133) B1468133
theorem B1470275 : Blo 976593 1470275 := bstep (se 1 (by rfl) ⟨1102706, by rfl⟩ : syracuseStep 1470275 = 2205413) B2205413
theorem B978771 : Blo 976593 978771 := bstep (se 1 (by rfl) ⟨734078, by rfl⟩ : syracuseStep 978771 = 1468157) B1468157
theorem B1240915 : Blo 976593 1240915 := bstep (se 1 (by rfl) ⟨930686, by rfl⟩ : syracuseStep 1240915 = 1861373) B1861373
theorem B1470305 : Blo 976593 1470305 := bstep (se 2 (by rfl) ⟨551364, by rfl⟩ : syracuseStep 1470305 = 1102729) B1102729
theorem B978787 : Blo 976593 978787 := bstep (se 1 (by rfl) ⟨734090, by rfl⟩ : syracuseStep 978787 = 1468181) B1468181
theorem B978803 : Blo 976593 978803 := bstep (se 1 (by rfl) ⟨734102, by rfl⟩ : syracuseStep 978803 = 1468205) B1468205
theorem B1470323 : Blo 976593 1470323 := bstep (se 1 (by rfl) ⟨1102742, by rfl⟩ : syracuseStep 1470323 = 2205485) B2205485
theorem B978819 : Blo 976593 978819 := bstep (se 1 (by rfl) ⟨734114, by rfl⟩ : syracuseStep 978819 = 1468229) B1468229
theorem B2977681 : Blo 976593 2977681 := bstep (se 2 (by rfl) ⟨1116630, by rfl⟩ : syracuseStep 2977681 = 2233261) B2233261
theorem B1470353 : Blo 976593 1470353 := bstep (se 2 (by rfl) ⟨551382, by rfl⟩ : syracuseStep 1470353 = 1102765) B1102765
theorem B978835 : Blo 976593 978835 := bstep (se 1 (by rfl) ⟨734126, by rfl⟩ : syracuseStep 978835 = 1468253) B1468253
theorem B978851 : Blo 976593 978851 := bstep (se 1 (by rfl) ⟨734138, by rfl⟩ : syracuseStep 978851 = 1468277) B1468277
theorem B1470371 : Blo 976593 1470371 := bstep (se 1 (by rfl) ⟨1102778, by rfl⟩ : syracuseStep 1470371 = 2205557) B2205557
theorem B3305393 : Blo 976593 3305393 := bstep (se 2 (by rfl) ⟨1239522, by rfl⟩ : syracuseStep 3305393 = 2479045) B2479045
theorem B978867 : Blo 976593 978867 := bstep (se 1 (by rfl) ⟨734150, by rfl⟩ : syracuseStep 978867 = 1468301) B1468301
theorem B1241011 : Blo 976593 1241011 := bstep (se 1 (by rfl) ⟨930758, by rfl⟩ : syracuseStep 1241011 = 1861517) B1861517
theorem B1470401 : Blo 976593 1470401 := bstep (se 2 (by rfl) ⟨551400, by rfl⟩ : syracuseStep 1470401 = 1102801) B1102801
theorem B978883 : Blo 976593 978883 := bstep (se 1 (by rfl) ⟨734162, by rfl⟩ : syracuseStep 978883 = 1468325) B1468325
theorem B978899 : Blo 976593 978899 := bstep (se 1 (by rfl) ⟨734174, by rfl⟩ : syracuseStep 978899 = 1468349) B1468349
theorem B1470419 : Blo 976593 1470419 := bstep (se 1 (by rfl) ⟨1102814, by rfl⟩ : syracuseStep 1470419 = 2205629) B2205629
theorem B978915 : Blo 976593 978915 := bstep (se 1 (by rfl) ⟨734186, by rfl⟩ : syracuseStep 978915 = 1468373) B1468373
theorem B1470449 : Blo 976593 1470449 := bstep (se 2 (by rfl) ⟨551418, by rfl⟩ : syracuseStep 1470449 = 1102837) B1102837
theorem B978931 : Blo 976593 978931 := bstep (se 1 (by rfl) ⟨734198, by rfl⟩ : syracuseStep 978931 = 1468397) B1468397
theorem B978947 : Blo 976593 978947 := bstep (se 1 (by rfl) ⟨734210, by rfl⟩ : syracuseStep 978947 = 1468421) B1468421
theorem B1470467 : Blo 976593 1470467 := bstep (se 1 (by rfl) ⟨1102850, by rfl⟩ : syracuseStep 1470467 = 2205701) B2205701
theorem B978963 : Blo 976593 978963 := bstep (se 1 (by rfl) ⟨734222, by rfl⟩ : syracuseStep 978963 = 1468445) B1468445
theorem B1470497 : Blo 976593 1470497 := bstep (se 2 (by rfl) ⟨551436, by rfl⟩ : syracuseStep 1470497 = 1102873) B1102873
theorem B1044515 : Blo 976593 1044515 := bstep (se 1 (by rfl) ⟨783386, by rfl⟩ : syracuseStep 1044515 = 1566773) B1566773
theorem B978979 : Blo 976593 978979 := bstep (se 1 (by rfl) ⟨734234, by rfl⟩ : syracuseStep 978979 = 1468469) B1468469
theorem B978995 : Blo 976593 978995 := bstep (se 1 (by rfl) ⟨734246, by rfl⟩ : syracuseStep 978995 = 1468493) B1468493
theorem B1470515 : Blo 976593 1470515 := bstep (se 1 (by rfl) ⟨1102886, by rfl⟩ : syracuseStep 1470515 = 2205773) B2205773
theorem B979011 : Blo 976593 979011 := bstep (se 1 (by rfl) ⟨734258, by rfl⟩ : syracuseStep 979011 = 1468517) B1468517
theorem B1470545 : Blo 976593 1470545 := bstep (se 2 (by rfl) ⟨551454, by rfl⟩ : syracuseStep 1470545 = 1102909) B1102909
theorem B979027 : Blo 976593 979027 := bstep (se 1 (by rfl) ⟨734270, by rfl⟩ : syracuseStep 979027 = 1468541) B1468541
theorem B979043 : Blo 976593 979043 := bstep (se 1 (by rfl) ⟨734282, by rfl⟩ : syracuseStep 979043 = 1468565) B1468565
theorem B1470563 : Blo 976593 1470563 := bstep (se 1 (by rfl) ⟨1102922, by rfl⟩ : syracuseStep 1470563 = 2205845) B2205845
theorem B979059 : Blo 976593 979059 := bstep (se 1 (by rfl) ⟨734294, by rfl⟩ : syracuseStep 979059 = 1468589) B1468589
theorem B1470593 : Blo 976593 1470593 := bstep (se 2 (by rfl) ⟨551472, by rfl⟩ : syracuseStep 1470593 = 1102945) B1102945
theorem B979075 : Blo 976593 979075 := bstep (se 1 (by rfl) ⟨734306, by rfl⟩ : syracuseStep 979075 = 1468613) B1468613
theorem B979091 : Blo 976593 979091 := bstep (se 1 (by rfl) ⟨734318, by rfl⟩ : syracuseStep 979091 = 1468637) B1468637
theorem B1470611 : Blo 976593 1470611 := bstep (se 1 (by rfl) ⟨1102958, by rfl⟩ : syracuseStep 1470611 = 2205917) B2205917
theorem B979107 : Blo 976593 979107 := bstep (se 1 (by rfl) ⟨734330, by rfl⟩ : syracuseStep 979107 = 1468661) B1468661
theorem B1568945 : Blo 976593 1568945 := bstep (se 2 (by rfl) ⟨588354, by rfl⟩ : syracuseStep 1568945 = 1176709) B1176709
theorem B1470641 : Blo 976593 1470641 := bstep (se 2 (by rfl) ⟨551490, by rfl⟩ : syracuseStep 1470641 = 1102981) B1102981
theorem B979123 : Blo 976593 979123 := bstep (se 1 (by rfl) ⟨734342, by rfl⟩ : syracuseStep 979123 = 1468685) B1468685
theorem B979139 : Blo 976593 979139 := bstep (se 1 (by rfl) ⟨734354, by rfl⟩ : syracuseStep 979139 = 1468709) B1468709
theorem B1470659 : Blo 976593 1470659 := bstep (se 1 (by rfl) ⟨1102994, by rfl⟩ : syracuseStep 1470659 = 2205989) B2205989
theorem B4944077 : Blo 976593 4944077 := bstep (se 3 (by rfl) ⟨927014, by rfl⟩ : syracuseStep 4944077 = 1854029) B1854029
theorem B979155 : Blo 976593 979155 := bstep (se 1 (by rfl) ⟨734366, by rfl⟩ : syracuseStep 979155 = 1468733) B1468733
theorem B1470689 : Blo 976593 1470689 := bstep (se 2 (by rfl) ⟨551508, by rfl⟩ : syracuseStep 1470689 = 1103017) B1103017
theorem B979171 : Blo 976593 979171 := bstep (se 1 (by rfl) ⟨734378, by rfl⟩ : syracuseStep 979171 = 1468757) B1468757
theorem B979187 : Blo 976593 979187 := bstep (se 1 (by rfl) ⟨734390, by rfl⟩ : syracuseStep 979187 = 1468781) B1468781
theorem B1470707 : Blo 976593 1470707 := bstep (se 1 (by rfl) ⟨1103030, by rfl⟩ : syracuseStep 1470707 = 2206061) B2206061
theorem B979203 : Blo 976593 979203 := bstep (se 1 (by rfl) ⟨734402, by rfl⟩ : syracuseStep 979203 = 1468805) B1468805
theorem B1470737 : Blo 976593 1470737 := bstep (se 2 (by rfl) ⟨551526, by rfl⟩ : syracuseStep 1470737 = 1103053) B1103053
theorem B979219 : Blo 976593 979219 := bstep (se 1 (by rfl) ⟨734414, by rfl⟩ : syracuseStep 979219 = 1468829) B1468829
theorem B979235 : Blo 976593 979235 := bstep (se 1 (by rfl) ⟨734426, by rfl⟩ : syracuseStep 979235 = 1468853) B1468853
theorem B1470755 : Blo 976593 1470755 := bstep (se 1 (by rfl) ⟨1103066, by rfl⟩ : syracuseStep 1470755 = 2206133) B2206133
theorem B979251 : Blo 976593 979251 := bstep (se 1 (by rfl) ⟨734438, by rfl⟩ : syracuseStep 979251 = 1468877) B1468877
theorem B1470785 : Blo 976593 1470785 := bstep (se 2 (by rfl) ⟨551544, by rfl⟩ : syracuseStep 1470785 = 1103089) B1103089
theorem B979267 : Blo 976593 979267 := bstep (se 1 (by rfl) ⟨734450, by rfl⟩ : syracuseStep 979267 = 1468901) B1468901
theorem B979283 : Blo 976593 979283 := bstep (se 1 (by rfl) ⟨734462, by rfl⟩ : syracuseStep 979283 = 1468925) B1468925
theorem B1470803 : Blo 976593 1470803 := bstep (se 1 (by rfl) ⟨1103102, by rfl⟩ : syracuseStep 1470803 = 2206205) B2206205
theorem B979299 : Blo 976593 979299 := bstep (se 1 (by rfl) ⟨734474, by rfl⟩ : syracuseStep 979299 = 1468949) B1468949
theorem B1470833 : Blo 976593 1470833 := bstep (se 2 (by rfl) ⟨551562, by rfl⟩ : syracuseStep 1470833 = 1103125) B1103125
theorem B979315 : Blo 976593 979315 := bstep (se 1 (by rfl) ⟨734486, by rfl⟩ : syracuseStep 979315 = 1468973) B1468973
theorem B979331 : Blo 976593 979331 := bstep (se 1 (by rfl) ⟨734498, by rfl⟩ : syracuseStep 979331 = 1468997) B1468997
theorem B1470851 : Blo 976593 1470851 := bstep (se 1 (by rfl) ⟨1103138, by rfl⟩ : syracuseStep 1470851 = 2206277) B2206277
theorem B1569169 : Blo 976593 1569169 := bstep (se 2 (by rfl) ⟨588438, by rfl⟩ : syracuseStep 1569169 = 1176877) B1176877
theorem B979347 : Blo 976593 979347 := bstep (se 1 (by rfl) ⟨734510, by rfl⟩ : syracuseStep 979347 = 1469021) B1469021
theorem B1470881 : Blo 976593 1470881 := bstep (se 2 (by rfl) ⟨551580, by rfl⟩ : syracuseStep 1470881 = 1103161) B1103161
theorem B979363 : Blo 976593 979363 := bstep (se 1 (by rfl) ⟨734522, by rfl⟩ : syracuseStep 979363 = 1469045) B1469045
theorem B979379 : Blo 976593 979379 := bstep (se 1 (by rfl) ⟨734534, by rfl⟩ : syracuseStep 979379 = 1469069) B1469069
theorem B979395 : Blo 976593 979395 := bstep (se 1 (by rfl) ⟨734546, by rfl⟩ : syracuseStep 979395 = 1469093) B1469093
theorem B3305933 : Blo 976593 3305933 := bstep (se 3 (by rfl) ⟨619862, by rfl⟩ : syracuseStep 3305933 = 1239725) B1239725
theorem B1569233 : Blo 976593 1569233 := bstep (se 2 (by rfl) ⟨588462, by rfl⟩ : syracuseStep 1569233 = 1176925) B1176925
theorem B979411 : Blo 976593 979411 := bstep (se 1 (by rfl) ⟨734558, by rfl⟩ : syracuseStep 979411 = 1469117) B1469117
theorem B979427 : Blo 976593 979427 := bstep (se 1 (by rfl) ⟨734570, by rfl⟩ : syracuseStep 979427 = 1469141) B1469141
theorem B979443 : Blo 976593 979443 := bstep (se 1 (by rfl) ⟨734582, by rfl⟩ : syracuseStep 979443 = 1469165) B1469165
theorem B3305987 : Blo 976593 3305987 := bstep (se 1 (by rfl) ⟨2479490, by rfl⟩ : syracuseStep 3305987 = 4958981) B4958981
theorem B979459 : Blo 976593 979459 := bstep (se 1 (by rfl) ⟨734594, by rfl⟩ : syracuseStep 979459 = 1469189) B1469189
theorem B979475 : Blo 976593 979475 := bstep (se 1 (by rfl) ⟨734606, by rfl⟩ : syracuseStep 979475 = 1469213) B1469213
theorem B979491 : Blo 976593 979491 := bstep (se 1 (by rfl) ⟨734618, by rfl⟩ : syracuseStep 979491 = 1469237) B1469237
theorem B979507 : Blo 976593 979507 := bstep (se 1 (by rfl) ⟨734630, by rfl⟩ : syracuseStep 979507 = 1469261) B1469261
theorem B979523 : Blo 976593 979523 := bstep (se 1 (by rfl) ⟨734642, by rfl⟩ : syracuseStep 979523 = 1469285) B1469285
theorem B2781773 : Blo 976593 2781773 := bstep (se 3 (by rfl) ⟨521582, by rfl⟩ : syracuseStep 2781773 = 1043165) B1043165
theorem B1569361 : Blo 976593 1569361 := bstep (se 2 (by rfl) ⟨588510, by rfl⟩ : syracuseStep 1569361 = 1177021) B1177021
theorem B979539 : Blo 976593 979539 := bstep (se 1 (by rfl) ⟨734654, by rfl⟩ : syracuseStep 979539 = 1469309) B1469309
theorem B979555 : Blo 976593 979555 := bstep (se 1 (by rfl) ⟨734666, by rfl⟩ : syracuseStep 979555 = 1469333) B1469333
theorem B979571 : Blo 976593 979571 := bstep (se 1 (by rfl) ⟨734678, by rfl⟩ : syracuseStep 979571 = 1469357) B1469357
theorem B979587 : Blo 976593 979587 := bstep (se 1 (by rfl) ⟨734690, by rfl⟩ : syracuseStep 979587 = 1469381) B1469381
theorem B979603 : Blo 976593 979603 := bstep (se 1 (by rfl) ⟨734702, by rfl⟩ : syracuseStep 979603 = 1469405) B1469405
theorem B979619 : Blo 976593 979619 := bstep (se 1 (by rfl) ⟨734714, by rfl⟩ : syracuseStep 979619 = 1469429) B1469429
theorem B979635 : Blo 976593 979635 := bstep (se 1 (by rfl) ⟨734726, by rfl⟩ : syracuseStep 979635 = 1469453) B1469453
theorem B979651 : Blo 976593 979651 := bstep (se 1 (by rfl) ⟨734738, by rfl⟩ : syracuseStep 979651 = 1469477) B1469477
theorem B979667 : Blo 976593 979667 := bstep (se 1 (by rfl) ⟨734750, by rfl⟩ : syracuseStep 979667 = 1469501) B1469501
theorem B979683 : Blo 976593 979683 := bstep (se 1 (by rfl) ⟨734762, by rfl⟩ : syracuseStep 979683 = 1469525) B1469525
theorem B979699 : Blo 976593 979699 := bstep (se 1 (by rfl) ⟨734774, by rfl⟩ : syracuseStep 979699 = 1469549) B1469549
theorem B2781955 : Blo 976593 2781955 := bstep (se 1 (by rfl) ⟨2086466, by rfl⟩ : syracuseStep 2781955 = 4172933) B4172933
theorem B979715 : Blo 976593 979715 := bstep (se 1 (by rfl) ⟨734786, by rfl⟩ : syracuseStep 979715 = 1469573) B1469573
theorem B5567237 : Blo 976593 5567237 := bstep (se 4 (by rfl) ⟨521928, by rfl⟩ : syracuseStep 5567237 = 1043857) B1043857
theorem B3306257 : Blo 976593 3306257 := bstep (se 2 (by rfl) ⟨1239846, by rfl⟩ : syracuseStep 3306257 = 2479693) B2479693
theorem B979731 : Blo 976593 979731 := bstep (se 1 (by rfl) ⟨734798, by rfl⟩ : syracuseStep 979731 = 1469597) B1469597
theorem B979747 : Blo 976593 979747 := bstep (se 1 (by rfl) ⟨734810, by rfl⟩ : syracuseStep 979747 = 1469621) B1469621
theorem B2782001 : Blo 976593 2782001 := bstep (se 2 (by rfl) ⟨1043250, by rfl⟩ : syracuseStep 2782001 = 2086501) B2086501
theorem B979763 : Blo 976593 979763 := bstep (se 1 (by rfl) ⟨734822, by rfl⟩ : syracuseStep 979763 = 1469645) B1469645
theorem B979779 : Blo 976593 979779 := bstep (se 1 (by rfl) ⟨734834, by rfl⟩ : syracuseStep 979779 = 1469669) B1469669
theorem B979795 : Blo 976593 979795 := bstep (se 1 (by rfl) ⟨734846, by rfl⟩ : syracuseStep 979795 = 1469693) B1469693
theorem B979811 : Blo 976593 979811 := bstep (se 1 (by rfl) ⟨734858, by rfl⟩ : syracuseStep 979811 = 1469717) B1469717
theorem B979827 : Blo 976593 979827 := bstep (se 1 (by rfl) ⟨734870, by rfl⟩ : syracuseStep 979827 = 1469741) B1469741
theorem B979843 : Blo 976593 979843 := bstep (se 1 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 979843 = 1469765) B1469765
theorem B979859 : Blo 976593 979859 := bstep (se 1 (by rfl) ⟨734894, by rfl⟩ : syracuseStep 979859 = 1469789) B1469789
theorem B979875 : Blo 976593 979875 := bstep (se 1 (by rfl) ⟨734906, by rfl⟩ : syracuseStep 979875 = 1469813) B1469813
theorem B979891 : Blo 976593 979891 := bstep (se 1 (by rfl) ⟨734918, by rfl⟩ : syracuseStep 979891 = 1469837) B1469837
theorem B979907 : Blo 976593 979907 := bstep (se 1 (by rfl) ⟨734930, by rfl⟩ : syracuseStep 979907 = 1469861) B1469861
theorem B979923 : Blo 976593 979923 := bstep (se 1 (by rfl) ⟨734942, by rfl⟩ : syracuseStep 979923 = 1469885) B1469885
theorem B979939 : Blo 976593 979939 := bstep (se 1 (by rfl) ⟨734954, by rfl⟩ : syracuseStep 979939 = 1469909) B1469909
theorem B2978801 : Blo 976593 2978801 := bstep (se 2 (by rfl) ⟨1117050, by rfl⟩ : syracuseStep 2978801 = 2234101) B2234101
theorem B979955 : Blo 976593 979955 := bstep (se 1 (by rfl) ⟨734966, by rfl⟩ : syracuseStep 979955 = 1469933) B1469933
theorem B979971 : Blo 976593 979971 := bstep (se 1 (by rfl) ⟨734978, by rfl⟩ : syracuseStep 979971 = 1469957) B1469957
theorem B979987 : Blo 976593 979987 := bstep (se 1 (by rfl) ⟨734990, by rfl⟩ : syracuseStep 979987 = 1469981) B1469981
theorem B980003 : Blo 976593 980003 := bstep (se 1 (by rfl) ⟨735002, by rfl⟩ : syracuseStep 980003 = 1470005) B1470005
theorem B980019 : Blo 976593 980019 := bstep (se 1 (by rfl) ⟨735014, by rfl⟩ : syracuseStep 980019 = 1470029) B1470029
theorem B980035 : Blo 976593 980035 := bstep (se 1 (by rfl) ⟨735026, by rfl⟩ : syracuseStep 980035 = 1470053) B1470053
theorem B980051 : Blo 976593 980051 := bstep (se 1 (by rfl) ⟨735038, by rfl⟩ : syracuseStep 980051 = 1470077) B1470077
theorem B980067 : Blo 976593 980067 := bstep (se 1 (by rfl) ⟨735050, by rfl⟩ : syracuseStep 980067 = 1470101) B1470101
theorem B980083 : Blo 976593 980083 := bstep (se 1 (by rfl) ⟨735062, by rfl⟩ : syracuseStep 980083 = 1470125) B1470125
theorem B980099 : Blo 976593 980099 := bstep (se 1 (by rfl) ⟨735074, by rfl⟩ : syracuseStep 980099 = 1470149) B1470149
theorem B980115 : Blo 976593 980115 := bstep (se 1 (by rfl) ⟨735086, by rfl⟩ : syracuseStep 980115 = 1470173) B1470173
theorem B980131 : Blo 976593 980131 := bstep (se 1 (by rfl) ⟨735098, by rfl⟩ : syracuseStep 980131 = 1470197) B1470197
theorem B980147 : Blo 976593 980147 := bstep (se 1 (by rfl) ⟨735110, by rfl⟩ : syracuseStep 980147 = 1470221) B1470221
theorem B980163 : Blo 976593 980163 := bstep (se 1 (by rfl) ⟨735122, by rfl⟩ : syracuseStep 980163 = 1470245) B1470245
theorem B2094275 : Blo 976593 2094275 := bstep (se 1 (by rfl) ⟨1570706, by rfl⟩ : syracuseStep 2094275 = 3141413) B3141413
theorem B980179 : Blo 976593 980179 := bstep (se 1 (by rfl) ⟨735134, by rfl⟩ : syracuseStep 980179 = 1470269) B1470269
theorem B980195 : Blo 976593 980195 := bstep (se 1 (by rfl) ⟨735146, by rfl⟩ : syracuseStep 980195 = 1470293) B1470293
theorem B1766627 : Blo 976593 1766627 := bstep (se 1 (by rfl) ⟨1324970, by rfl⟩ : syracuseStep 1766627 = 2649941) B2649941
theorem B980211 : Blo 976593 980211 := bstep (se 1 (by rfl) ⟨735158, by rfl⟩ : syracuseStep 980211 = 1470317) B1470317
theorem B980227 : Blo 976593 980227 := bstep (se 1 (by rfl) ⟨735170, by rfl⟩ : syracuseStep 980227 = 1470341) B1470341
theorem B980243 : Blo 976593 980243 := bstep (se 1 (by rfl) ⟨735182, by rfl⟩ : syracuseStep 980243 = 1470365) B1470365
theorem B980259 : Blo 976593 980259 := bstep (se 1 (by rfl) ⟨735194, by rfl⟩ : syracuseStep 980259 = 1470389) B1470389
theorem B3306797 : Blo 976593 3306797 := bstep (se 3 (by rfl) ⟨620024, by rfl⟩ : syracuseStep 3306797 = 1240049) B1240049
theorem B3437873 : Blo 976593 3437873 := bstep (se 2 (by rfl) ⟨1289202, by rfl⟩ : syracuseStep 3437873 = 2578405) B2578405
theorem B980275 : Blo 976593 980275 := bstep (se 1 (by rfl) ⟨735206, by rfl⟩ : syracuseStep 980275 = 1470413) B1470413
theorem B12711221 : Blo 976593 12711221 := bstep (se 5 (by rfl) ⟨595838, by rfl⟩ : syracuseStep 12711221 = 1191677) B1191677
theorem B980291 : Blo 976593 980291 := bstep (se 1 (by rfl) ⟨735218, by rfl⟩ : syracuseStep 980291 = 1470437) B1470437
theorem B980307 : Blo 976593 980307 := bstep (se 1 (by rfl) ⟨735230, by rfl⟩ : syracuseStep 980307 = 1470461) B1470461
theorem B7042403 : Blo 976593 7042403 := bstep (se 1 (by rfl) ⟨5281802, by rfl⟩ : syracuseStep 7042403 = 10563605) B10563605
theorem B3306851 : Blo 976593 3306851 := bstep (se 1 (by rfl) ⟨2480138, by rfl⟩ : syracuseStep 3306851 = 4960277) B4960277
theorem B980323 : Blo 976593 980323 := bstep (se 1 (by rfl) ⟨735242, by rfl⟩ : syracuseStep 980323 = 1470485) B1470485
theorem B980339 : Blo 976593 980339 := bstep (se 1 (by rfl) ⟨735254, by rfl⟩ : syracuseStep 980339 = 1470509) B1470509
theorem B980355 : Blo 976593 980355 := bstep (se 1 (by rfl) ⟨735266, by rfl⟩ : syracuseStep 980355 = 1470533) B1470533
theorem B980371 : Blo 976593 980371 := bstep (se 1 (by rfl) ⟨735278, by rfl⟩ : syracuseStep 980371 = 1470557) B1470557
theorem B980387 : Blo 976593 980387 := bstep (se 1 (by rfl) ⟨735290, by rfl⟩ : syracuseStep 980387 = 1470581) B1470581
theorem B980403 : Blo 976593 980403 := bstep (se 1 (by rfl) ⟨735302, by rfl⟩ : syracuseStep 980403 = 1470605) B1470605
theorem B980419 : Blo 976593 980419 := bstep (se 1 (by rfl) ⟨735314, by rfl⟩ : syracuseStep 980419 = 1470629) B1470629
theorem B980435 : Blo 976593 980435 := bstep (se 1 (by rfl) ⟨735326, by rfl⟩ : syracuseStep 980435 = 1470653) B1470653
theorem B980451 : Blo 976593 980451 := bstep (se 1 (by rfl) ⟨735338, by rfl⟩ : syracuseStep 980451 = 1470677) B1470677
theorem B980467 : Blo 976593 980467 := bstep (se 1 (by rfl) ⟨735350, by rfl⟩ : syracuseStep 980467 = 1470701) B1470701
theorem B980483 : Blo 976593 980483 := bstep (se 1 (by rfl) ⟨735362, by rfl⟩ : syracuseStep 980483 = 1470725) B1470725
theorem B10057229 : Blo 976593 10057229 := bstep (se 3 (by rfl) ⟨1885730, by rfl⟩ : syracuseStep 10057229 = 3771461) B3771461
theorem B980499 : Blo 976593 980499 := bstep (se 1 (by rfl) ⟨735374, by rfl⟩ : syracuseStep 980499 = 1470749) B1470749
theorem B980515 : Blo 976593 980515 := bstep (se 1 (by rfl) ⟨735386, by rfl⟩ : syracuseStep 980515 = 1470773) B1470773
theorem B980531 : Blo 976593 980531 := bstep (se 1 (by rfl) ⟨735398, by rfl⟩ : syracuseStep 980531 = 1470797) B1470797
theorem B980547 : Blo 976593 980547 := bstep (se 1 (by rfl) ⟨735410, by rfl⟩ : syracuseStep 980547 = 1470821) B1470821
theorem B980563 : Blo 976593 980563 := bstep (se 1 (by rfl) ⟨735422, by rfl⟩ : syracuseStep 980563 = 1470845) B1470845
theorem B980579 : Blo 976593 980579 := bstep (se 1 (by rfl) ⟨735434, by rfl⟩ : syracuseStep 980579 = 1470869) B1470869
theorem B3307121 : Blo 976593 3307121 := bstep (se 2 (by rfl) ⟨1240170, by rfl⟩ : syracuseStep 3307121 = 2480341) B2480341
theorem B8943331 : Blo 976593 8943331 := bstep (se 1 (by rfl) ⟨6707498, by rfl⟩ : syracuseStep 8943331 = 13414997) B13414997
theorem B8484749 : Blo 976593 8484749 := bstep (se 3 (by rfl) ⟨1590890, by rfl⟩ : syracuseStep 8484749 = 3181781) B3181781
theorem B2979821 : Blo 976593 2979821 := bstep (se 3 (by rfl) ⟨558716, by rfl⟩ : syracuseStep 2979821 = 1117433) B1117433
theorem B1046531 : Blo 976593 1046531 := bstep (se 1 (by rfl) ⟨784898, by rfl⟩ : syracuseStep 1046531 = 1569797) B1569797
theorem B3307661 : Blo 976593 3307661 := bstep (se 3 (by rfl) ⟨620186, by rfl⟩ : syracuseStep 3307661 = 1240373) B1240373
theorem B3307715 : Blo 976593 3307715 := bstep (se 1 (by rfl) ⟨2480786, by rfl⟩ : syracuseStep 3307715 = 4961573) B4961573
theorem B2783459 : Blo 976593 2783459 := bstep (se 1 (by rfl) ⟨2087594, by rfl⟩ : syracuseStep 2783459 = 4175189) B4175189
theorem B1177939 : Blo 976593 1177939 := bstep (se 1 (by rfl) ⟨883454, by rfl⟩ : syracuseStep 1177939 = 1766909) B1766909
theorem B2685329 : Blo 976593 2685329 := bstep (se 2 (by rfl) ⟨1006998, by rfl⟩ : syracuseStep 2685329 = 2013997) B2013997
theorem B3307985 : Blo 976593 3307985 := bstep (se 2 (by rfl) ⟨1240494, by rfl⟩ : syracuseStep 3307985 = 2480989) B2480989
theorem B7436771 : Blo 976593 7436771 := bstep (se 1 (by rfl) ⟨5577578, by rfl⟩ : syracuseStep 7436771 = 11155157) B11155157
theorem B15039029 : Blo 976593 15039029 := bstep (se 5 (by rfl) ⟨704954, by rfl⟩ : syracuseStep 15039029 = 1409909) B1409909
theorem B11893301 : Blo 976593 11893301 := bstep (se 5 (by rfl) ⟨557498, by rfl⟩ : syracuseStep 11893301 = 1114997) B1114997
theorem B3308525 : Blo 976593 3308525 := bstep (se 3 (by rfl) ⟨620348, by rfl⟩ : syracuseStep 3308525 = 1240697) B1240697
theorem B3308579 : Blo 976593 3308579 := bstep (se 1 (by rfl) ⟨2481434, by rfl⟩ : syracuseStep 3308579 = 4962869) B4962869
theorem B4946993 : Blo 976593 4946993 := bstep (se 2 (by rfl) ⟨1855122, by rfl⟩ : syracuseStep 4946993 = 3710245) B3710245
theorem B13565069 : Blo 976593 13565069 := bstep (se 3 (by rfl) ⟨2543450, by rfl⟩ : syracuseStep 13565069 = 5086901) B5086901
theorem B3308849 : Blo 976593 3308849 := bstep (se 2 (by rfl) ⟨1240818, by rfl⟩ : syracuseStep 3308849 = 2481637) B2481637
theorem B2784689 : Blo 976593 2784689 := bstep (se 2 (by rfl) ⟨1044258, by rfl⟩ : syracuseStep 2784689 = 2088517) B2088517
theorem B5963341 : Blo 976593 5963341 := bstep (se 3 (by rfl) ⟨1118126, by rfl⟩ : syracuseStep 5963341 = 2236253) B2236253
theorem B10714933 : Blo 976593 10714933 := bstep (se 5 (by rfl) ⟨502262, by rfl⟩ : syracuseStep 10714933 = 1004525) B1004525
theorem B3309389 : Blo 976593 3309389 := bstep (se 3 (by rfl) ⟨620510, by rfl⟩ : syracuseStep 3309389 = 1241021) B1241021
theorem B3309443 : Blo 976593 3309443 := bstep (se 1 (by rfl) ⟨2482082, by rfl⟩ : syracuseStep 3309443 = 4964165) B4964165
theorem B5570653 : Blo 976593 5570653 := bstep (se 3 (by rfl) ⟨1044497, by rfl⟩ : syracuseStep 5570653 = 2088995) B2088995
theorem B2785373 : Blo 976593 2785373 := bstep (se 3 (by rfl) ⟨522257, by rfl⟩ : syracuseStep 2785373 = 1044515) B1044515
theorem B4948289 : Blo 976593 4948289 := bstep (se 2 (by rfl) ⟨1855608, by rfl⟩ : syracuseStep 4948289 = 3711217) B3711217
theorem B2785715 : Blo 976593 2785715 := bstep (se 1 (by rfl) ⟨2089286, by rfl⟩ : syracuseStep 2785715 = 4178573) B4178573
theorem B14123555 : Blo 976593 14123555 := bstep (se 1 (by rfl) ⟨10592666, by rfl⟩ : syracuseStep 14123555 = 21185333) B21185333
theorem B6259787 : Blo 976593 6259787 := bstep (se 1 (by rfl) ⟨4694840, by rfl⟩ : syracuseStep 6259787 = 9389681) B9389681
theorem B3769523 : Blo 976593 3769523 := bstep (se 1 (by rfl) ⟨2827142, by rfl⟩ : syracuseStep 3769523 = 5654285) B5654285
theorem B1115947 : Blo 976593 1115947 := bstep (se 1 (by rfl) ⟨836960, by rfl⟩ : syracuseStep 1115947 = 1673921) B1673921
theorem B7440173 : Blo 976593 7440173 := bstep (se 3 (by rfl) ⟨1395032, by rfl⟩ : syracuseStep 7440173 = 2790065) B2790065
theorem B13371313 : Blo 976593 13371313 := bstep (se 2 (by rfl) ⟨5014242, by rfl⟩ : syracuseStep 13371313 = 10028485) B10028485
theorem B2230195 : Blo 976593 2230195 := bstep (se 1 (by rfl) ⟨1672646, by rfl⟩ : syracuseStep 2230195 = 3345293) B3345293
theorem B2197529 : Blo 976593 2197529 := bstep (se 2 (by rfl) ⟨824073, by rfl⟩ : syracuseStep 2197529 = 1648147) B1648147
theorem B1673303 : Blo 976593 1673303 := bstep (se 1 (by rfl) ⟨1254977, by rfl⟩ : syracuseStep 1673303 = 2509955) B2509955
theorem B2197619 : Blo 976593 2197619 := bstep (se 1 (by rfl) ⟨1648214, by rfl⟩ : syracuseStep 2197619 = 3296429) B3296429
theorem B2197655 : Blo 976593 2197655 := bstep (se 1 (by rfl) ⟨1648241, by rfl⟩ : syracuseStep 2197655 = 3296483) B3296483
theorem B4950233 : Blo 976593 4950233 := bstep (se 2 (by rfl) ⟨1856337, by rfl⟩ : syracuseStep 4950233 = 3712675) B3712675
theorem B11897093 : Blo 976593 11897093 := bstep (se 4 (by rfl) ⟨1115352, by rfl⟩ : syracuseStep 11897093 = 2230705) B2230705
theorem B2230553 : Blo 976593 2230553 := bstep (se 2 (by rfl) ⟨836457, by rfl⟩ : syracuseStep 2230553 = 1672915) B1672915
theorem B2197835 : Blo 976593 2197835 := bstep (se 1 (by rfl) ⟨1648376, by rfl⟩ : syracuseStep 2197835 = 3296753) B3296753
theorem B3967321 : Blo 976593 3967321 := bstep (se 2 (by rfl) ⟨1487745, by rfl⟩ : syracuseStep 3967321 = 2975491) B2975491
theorem B2197889 : Blo 976593 2197889 := bstep (se 2 (by rfl) ⟨824208, by rfl⟩ : syracuseStep 2197889 = 1648417) B1648417
theorem B2787787 : Blo 976593 2787787 := bstep (se 1 (by rfl) ⟨2090840, by rfl⟩ : syracuseStep 2787787 = 4181681) B4181681
theorem B2198105 : Blo 976593 2198105 := bstep (se 2 (by rfl) ⟨824289, by rfl⟩ : syracuseStep 2198105 = 1648579) B1648579
theorem B10029719 : Blo 976593 10029719 := bstep (se 1 (by rfl) ⟨7522289, by rfl⟩ : syracuseStep 10029719 = 15044579) B15044579
theorem B2198195 : Blo 976593 2198195 := bstep (se 1 (by rfl) ⟨1648646, by rfl⟩ : syracuseStep 2198195 = 3297293) B3297293
theorem B2198231 : Blo 976593 2198231 := bstep (se 1 (by rfl) ⟨1648673, by rfl⟩ : syracuseStep 2198231 = 3297347) B3297347
theorem B2198411 : Blo 976593 2198411 := bstep (se 1 (by rfl) ⟨1648808, by rfl⟩ : syracuseStep 2198411 = 3297617) B3297617
theorem B2198465 : Blo 976593 2198465 := bstep (se 2 (by rfl) ⟨824424, by rfl⟩ : syracuseStep 2198465 = 1648849) B1648849
theorem B2788289 : Blo 976593 2788289 := bstep (se 2 (by rfl) ⟨1045608, by rfl⟩ : syracuseStep 2788289 = 2091217) B2091217
theorem B1674263 : Blo 976593 1674263 := bstep (se 1 (by rfl) ⟨1255697, by rfl⟩ : syracuseStep 1674263 = 2511395) B2511395
theorem B2198681 : Blo 976593 2198681 := bstep (se 2 (by rfl) ⟨824505, by rfl⟩ : syracuseStep 2198681 = 1649011) B1649011
theorem B1412311 : Blo 976593 1412311 := bstep (se 1 (by rfl) ⟨1059233, by rfl⟩ : syracuseStep 1412311 = 2118467) B2118467
theorem B2198771 : Blo 976593 2198771 := bstep (se 1 (by rfl) ⟨1649078, by rfl⟩ : syracuseStep 2198771 = 3298157) B3298157
theorem B2198807 : Blo 976593 2198807 := bstep (se 1 (by rfl) ⟨1649105, by rfl⟩ : syracuseStep 2198807 = 3298211) B3298211
theorem B2788631 : Blo 976593 2788631 := bstep (se 1 (by rfl) ⟨2091473, by rfl⟩ : syracuseStep 2788631 = 4182947) B4182947
theorem B1510807 : Blo 976593 1510807 := bstep (se 1 (by rfl) ⟨1133105, by rfl⟩ : syracuseStep 1510807 = 2266211) B2266211
theorem B2198987 : Blo 976593 2198987 := bstep (se 1 (by rfl) ⟨1649240, by rfl⟩ : syracuseStep 2198987 = 3298481) B3298481
theorem B2199041 : Blo 976593 2199041 := bstep (se 2 (by rfl) ⟨824640, by rfl⟩ : syracuseStep 2199041 = 1649281) B1649281
theorem B16748045 : Blo 976593 16748045 := bstep (se 3 (by rfl) ⟨3140258, by rfl⟩ : syracuseStep 16748045 = 6280517) B6280517
theorem B6262373 : Blo 976593 6262373 := bstep (se 4 (by rfl) ⟨587097, by rfl⟩ : syracuseStep 6262373 = 1174195) B1174195
theorem B2199257 : Blo 976593 2199257 := bstep (se 2 (by rfl) ⟨824721, by rfl⟩ : syracuseStep 2199257 = 1649443) B1649443
theorem B4951853 : Blo 976593 4951853 := bstep (se 3 (by rfl) ⟨928472, by rfl⟩ : syracuseStep 4951853 = 1856945) B1856945
theorem B3968813 : Blo 976593 3968813 := bstep (se 3 (by rfl) ⟨744152, by rfl⟩ : syracuseStep 3968813 = 1488305) B1488305
theorem B2199347 : Blo 976593 2199347 := bstep (se 1 (by rfl) ⟨1649510, by rfl⟩ : syracuseStep 2199347 = 3299021) B3299021
theorem B2199383 : Blo 976593 2199383 := bstep (se 1 (by rfl) ⟨1649537, by rfl⟩ : syracuseStep 2199383 = 3299075) B3299075
theorem B2199563 : Blo 976593 2199563 := bstep (se 1 (by rfl) ⟨1649672, by rfl⟩ : syracuseStep 2199563 = 3299345) B3299345
theorem B14323729 : Blo 976593 14323729 := bstep (se 2 (by rfl) ⟨5371398, by rfl⟩ : syracuseStep 14323729 = 10742797) B10742797
theorem B2199617 : Blo 976593 2199617 := bstep (se 2 (by rfl) ⟨824856, by rfl⟩ : syracuseStep 2199617 = 1649713) B1649713
theorem B4460609 : Blo 976593 4460609 := bstep (se 2 (by rfl) ⟨1672728, by rfl⟩ : syracuseStep 4460609 = 3345457) B3345457
theorem B54235277 : Blo 976593 54235277 := bstep (se 3 (by rfl) ⟨10169114, by rfl⟩ : syracuseStep 54235277 = 20338229) B20338229
theorem B4526273 : Blo 976593 4526273 := bstep (se 2 (by rfl) ⟨1697352, by rfl⟩ : syracuseStep 4526273 = 3394705) B3394705
theorem B2199833 : Blo 976593 2199833 := bstep (se 2 (by rfl) ⟨824937, by rfl⟩ : syracuseStep 2199833 = 1649875) B1649875
theorem B2199923 : Blo 976593 2199923 := bstep (se 1 (by rfl) ⟨1649942, by rfl⟩ : syracuseStep 2199923 = 3299885) B3299885
theorem B2199959 : Blo 976593 2199959 := bstep (se 1 (by rfl) ⟨1649969, by rfl⟩ : syracuseStep 2199959 = 3299939) B3299939
theorem B2200139 : Blo 976593 2200139 := bstep (se 1 (by rfl) ⟨1650104, by rfl⟩ : syracuseStep 2200139 = 3300209) B3300209
theorem B2200193 : Blo 976593 2200193 := bstep (se 2 (by rfl) ⟨825072, by rfl⟩ : syracuseStep 2200193 = 1650145) B1650145
theorem B2200409 : Blo 976593 2200409 := bstep (se 2 (by rfl) ⟨825153, by rfl⟩ : syracuseStep 2200409 = 1650307) B1650307
theorem B2200499 : Blo 976593 2200499 := bstep (se 1 (by rfl) ⟨1650374, by rfl⟩ : syracuseStep 2200499 = 3300749) B3300749
theorem B2200535 : Blo 976593 2200535 := bstep (se 1 (by rfl) ⟨1650401, by rfl⟩ : syracuseStep 2200535 = 3300803) B3300803
theorem B9409553 : Blo 976593 9409553 := bstep (se 2 (by rfl) ⟨3528582, by rfl⟩ : syracuseStep 9409553 = 7057165) B7057165
theorem B2200715 : Blo 976593 2200715 := bstep (se 1 (by rfl) ⟨1650536, by rfl⟩ : syracuseStep 2200715 = 3301073) B3301073
theorem B2200769 : Blo 976593 2200769 := bstep (se 2 (by rfl) ⟨825288, by rfl⟩ : syracuseStep 2200769 = 1650577) B1650577
theorem B3970241 : Blo 976593 3970241 := bstep (se 2 (by rfl) ⟨1488840, by rfl⟩ : syracuseStep 3970241 = 2977681) B2977681
theorem B2790749 : Blo 976593 2790749 := bstep (se 3 (by rfl) ⟨523265, by rfl⟩ : syracuseStep 2790749 = 1046531) B1046531
theorem B2200985 : Blo 976593 2200985 := bstep (se 2 (by rfl) ⟨825369, by rfl⟩ : syracuseStep 2200985 = 1650739) B1650739
theorem B2201075 : Blo 976593 2201075 := bstep (se 1 (by rfl) ⟨1650806, by rfl⟩ : syracuseStep 2201075 = 3301613) B3301613
theorem B2201111 : Blo 976593 2201111 := bstep (se 1 (by rfl) ⟨1650833, by rfl⟩ : syracuseStep 2201111 = 3301667) B3301667
theorem B7050797 : Blo 976593 7050797 := bstep (se 3 (by rfl) ⟨1322024, by rfl⟩ : syracuseStep 7050797 = 2644049) B2644049
theorem B7444061 : Blo 976593 7444061 := bstep (se 3 (by rfl) ⟨1395761, by rfl⟩ : syracuseStep 7444061 = 2791523) B2791523
theorem B2791091 : Blo 976593 2791091 := bstep (se 1 (by rfl) ⟨2093318, by rfl⟩ : syracuseStep 2791091 = 4186637) B4186637
theorem B2201291 : Blo 976593 2201291 := bstep (se 1 (by rfl) ⟨1650968, by rfl⟩ : syracuseStep 2201291 = 3301937) B3301937
theorem B2201345 : Blo 976593 2201345 := bstep (se 2 (by rfl) ⟨825504, by rfl⟩ : syracuseStep 2201345 = 1651009) B1651009
theorem B7051025 : Blo 976593 7051025 := bstep (se 2 (by rfl) ⟨2644134, by rfl⟩ : syracuseStep 7051025 = 5288269) B5288269
theorem B2201561 : Blo 976593 2201561 := bstep (se 2 (by rfl) ⟨825585, by rfl⟩ : syracuseStep 2201561 = 1651171) B1651171
theorem B2201651 : Blo 976593 2201651 := bstep (se 1 (by rfl) ⟨1651238, by rfl⟩ : syracuseStep 2201651 = 3302477) B3302477
theorem B2201687 : Blo 976593 2201687 := bstep (se 1 (by rfl) ⟨1651265, by rfl⟩ : syracuseStep 2201687 = 3302531) B3302531
theorem B21174533 : Blo 976593 21174533 := bstep (se 4 (by rfl) ⟨1985112, by rfl⟩ : syracuseStep 21174533 = 3970225) B3970225
theorem B2201867 : Blo 976593 2201867 := bstep (se 1 (by rfl) ⟨1651400, by rfl⟩ : syracuseStep 2201867 = 3302801) B3302801
theorem B2201921 : Blo 976593 2201921 := bstep (se 2 (by rfl) ⟨825720, by rfl⟩ : syracuseStep 2201921 = 1651441) B1651441
theorem B3709259 : Blo 976593 3709259 := bstep (se 1 (by rfl) ⟨2781944, by rfl⟩ : syracuseStep 3709259 = 5563889) B5563889
theorem B3709273 : Blo 976593 3709273 := bstep (se 2 (by rfl) ⟨1390977, by rfl⟩ : syracuseStep 3709273 = 2781955) B2781955
theorem B2202137 : Blo 976593 2202137 := bstep (se 2 (by rfl) ⟨825801, by rfl⟩ : syracuseStep 2202137 = 1651603) B1651603
theorem B8362541 : Blo 976593 8362541 := bstep (se 3 (by rfl) ⟨1567976, by rfl⟩ : syracuseStep 8362541 = 3135953) B3135953
theorem B2202227 : Blo 976593 2202227 := bstep (se 1 (by rfl) ⟨1651670, by rfl⟩ : syracuseStep 2202227 = 3303341) B3303341
theorem B2202263 : Blo 976593 2202263 := bstep (se 1 (by rfl) ⟨1651697, by rfl⟩ : syracuseStep 2202263 = 3303395) B3303395
theorem B2202443 : Blo 976593 2202443 := bstep (se 1 (by rfl) ⟨1651832, by rfl⟩ : syracuseStep 2202443 = 3303665) B3303665
theorem B2202497 : Blo 976593 2202497 := bstep (se 2 (by rfl) ⟨825936, by rfl⟩ : syracuseStep 2202497 = 1651873) B1651873
theorem B2202713 : Blo 976593 2202713 := bstep (se 2 (by rfl) ⟨826017, by rfl⟩ : syracuseStep 2202713 = 1652035) B1652035
theorem B2202803 : Blo 976593 2202803 := bstep (se 1 (by rfl) ⟨1652102, by rfl⟩ : syracuseStep 2202803 = 3304205) B3304205
theorem B2202839 : Blo 976593 2202839 := bstep (se 1 (by rfl) ⟨1652129, by rfl⟩ : syracuseStep 2202839 = 3304259) B3304259
theorem B3710231 : Blo 976593 3710231 := bstep (se 1 (by rfl) ⟨2782673, by rfl⟩ : syracuseStep 3710231 = 5565347) B5565347
theorem B2203019 : Blo 976593 2203019 := bstep (se 1 (by rfl) ⟨1652264, by rfl⟩ : syracuseStep 2203019 = 3304529) B3304529
theorem B2203073 : Blo 976593 2203073 := bstep (se 2 (by rfl) ⟨826152, by rfl⟩ : syracuseStep 2203073 = 1652305) B1652305
theorem B4955741 : Blo 976593 4955741 := bstep (se 3 (by rfl) ⟨929201, by rfl⟩ : syracuseStep 4955741 = 1858403) B1858403
theorem B2203289 : Blo 976593 2203289 := bstep (se 2 (by rfl) ⟨826233, by rfl⟩ : syracuseStep 2203289 = 1652467) B1652467
theorem B990955 : Blo 976593 990955 := bstep (se 1 (by rfl) ⟨743216, by rfl⟩ : syracuseStep 990955 = 1486433) B1486433
theorem B2203379 : Blo 976593 2203379 := bstep (se 1 (by rfl) ⟨1652534, by rfl⟩ : syracuseStep 2203379 = 3305069) B3305069
theorem B2203415 : Blo 976593 2203415 := bstep (se 1 (by rfl) ⟨1652561, by rfl⟩ : syracuseStep 2203415 = 3305123) B3305123
theorem B2203595 : Blo 976593 2203595 := bstep (se 1 (by rfl) ⟨1652696, by rfl⟩ : syracuseStep 2203595 = 3305393) B3305393
theorem B2203649 : Blo 976593 2203649 := bstep (se 2 (by rfl) ⟨826368, by rfl⟩ : syracuseStep 2203649 = 1652737) B1652737
theorem B2203865 : Blo 976593 2203865 := bstep (se 2 (by rfl) ⟨826449, by rfl⟩ : syracuseStep 2203865 = 1652899) B1652899
theorem B2859229 : Blo 976593 2859229 := bstep (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) B1072211
theorem B4235485 : Blo 976593 4235485 := bstep (se 3 (by rfl) ⟨794153, by rfl⟩ : syracuseStep 4235485 = 1588307) B1588307
theorem B2203955 : Blo 976593 2203955 := bstep (se 1 (by rfl) ⟨1652966, by rfl⟩ : syracuseStep 2203955 = 3305933) B3305933
theorem B2203991 : Blo 976593 2203991 := bstep (se 1 (by rfl) ⟨1652993, by rfl⟩ : syracuseStep 2203991 = 3305987) B3305987
theorem B3711491 : Blo 976593 3711491 := bstep (se 1 (by rfl) ⟨2783618, by rfl⟩ : syracuseStep 3711491 = 5567237) B5567237
theorem B2204171 : Blo 976593 2204171 := bstep (se 1 (by rfl) ⟨1653128, by rfl⟩ : syracuseStep 2204171 = 3306257) B3306257
theorem B2204225 : Blo 976593 2204225 := bstep (se 2 (by rfl) ⟨826584, by rfl⟩ : syracuseStep 2204225 = 1653169) B1653169
theorem B2204441 : Blo 976593 2204441 := bstep (se 2 (by rfl) ⟨826665, by rfl⟩ : syracuseStep 2204441 = 1653331) B1653331
theorem B2204531 : Blo 976593 2204531 := bstep (se 1 (by rfl) ⟨1653398, by rfl⟩ : syracuseStep 2204531 = 3306797) B3306797
theorem B4694935 : Blo 976593 4694935 := bstep (se 1 (by rfl) ⟨3521201, by rfl⟩ : syracuseStep 4694935 = 7042403) B7042403
theorem B2204567 : Blo 976593 2204567 := bstep (se 1 (by rfl) ⟨1653425, by rfl⟩ : syracuseStep 2204567 = 3306851) B3306851
theorem B2204747 : Blo 976593 2204747 := bstep (se 1 (by rfl) ⟨1653560, by rfl⟩ : syracuseStep 2204747 = 3307121) B3307121
theorem B2204801 : Blo 976593 2204801 := bstep (se 2 (by rfl) ⟨826800, by rfl⟩ : syracuseStep 2204801 = 1653601) B1653601
theorem B5579927 : Blo 976593 5579927 := bstep (se 1 (by rfl) ⟨4184945, by rfl⟩ : syracuseStep 5579927 = 8369891) B8369891
theorem B992471 : Blo 976593 992471 := bstep (se 1 (by rfl) ⟨744353, by rfl⟩ : syracuseStep 992471 = 1488707) B1488707
theorem B2205017 : Blo 976593 2205017 := bstep (se 2 (by rfl) ⟨826881, by rfl⟩ : syracuseStep 2205017 = 1653763) B1653763
theorem B2205107 : Blo 976593 2205107 := bstep (se 1 (by rfl) ⟨1653830, by rfl⟩ : syracuseStep 2205107 = 3307661) B3307661
theorem B8365517 : Blo 976593 8365517 := bstep (se 3 (by rfl) ⟨1568534, by rfl⟩ : syracuseStep 8365517 = 3137069) B3137069
theorem B2205143 : Blo 976593 2205143 := bstep (se 1 (by rfl) ⟨1653857, by rfl⟩ : syracuseStep 2205143 = 3307715) B3307715
theorem B2205323 : Blo 976593 2205323 := bstep (se 1 (by rfl) ⟨1653992, by rfl⟩ : syracuseStep 2205323 = 3307985) B3307985
theorem B4957847 : Blo 976593 4957847 := bstep (se 1 (by rfl) ⟨3718385, by rfl⟩ : syracuseStep 4957847 = 7436771) B7436771
theorem B2205377 : Blo 976593 2205377 := bstep (se 2 (by rfl) ⟨827016, by rfl⟩ : syracuseStep 2205377 = 1654033) B1654033
theorem B1648343 : Blo 976593 1648343 := bstep (se 1 (by rfl) ⟨1236257, by rfl⟩ : syracuseStep 1648343 = 2472515) B2472515
theorem B6530861 : Blo 976593 6530861 := bstep (se 3 (by rfl) ⟨1224536, by rfl⟩ : syracuseStep 6530861 = 2449073) B2449073
theorem B11904833 : Blo 976593 11904833 := bstep (se 2 (by rfl) ⟨4464312, by rfl⟩ : syracuseStep 11904833 = 8928625) B8928625
theorem B1648471 : Blo 976593 1648471 := bstep (se 1 (by rfl) ⟨1236353, by rfl⟩ : syracuseStep 1648471 = 2472707) B2472707
theorem B2205593 : Blo 976593 2205593 := bstep (se 2 (by rfl) ⟨827097, by rfl⟩ : syracuseStep 2205593 = 1654195) B1654195
theorem B2205683 : Blo 976593 2205683 := bstep (se 1 (by rfl) ⟨1654262, by rfl⟩ : syracuseStep 2205683 = 3308525) B3308525
theorem B2205719 : Blo 976593 2205719 := bstep (se 1 (by rfl) ⟨1654289, by rfl⟩ : syracuseStep 2205719 = 3308579) B3308579
theorem B3352627 : Blo 976593 3352627 := bstep (se 1 (by rfl) ⟨2514470, by rfl⟩ : syracuseStep 3352627 = 5028941) B5028941
theorem B993367 : Blo 976593 993367 := bstep (se 1 (by rfl) ⟨745025, by rfl⟩ : syracuseStep 993367 = 1490051) B1490051
theorem B2205899 : Blo 976593 2205899 := bstep (se 1 (by rfl) ⟨1654424, by rfl⟩ : syracuseStep 2205899 = 3308849) B3308849
theorem B2205953 : Blo 976593 2205953 := bstep (se 2 (by rfl) ⟨827232, by rfl⟩ : syracuseStep 2205953 = 1654465) B1654465
theorem B1649099 : Blo 976593 1649099 := bstep (se 1 (by rfl) ⟨1236824, by rfl⟩ : syracuseStep 1649099 = 2473649) B2473649
theorem B4172249 : Blo 976593 4172249 := bstep (se 2 (by rfl) ⟨1564593, by rfl⟩ : syracuseStep 4172249 = 3129187) B3129187
theorem B2206169 : Blo 976593 2206169 := bstep (se 2 (by rfl) ⟨827313, by rfl⟩ : syracuseStep 2206169 = 1654627) B1654627
theorem B4467251 : Blo 976593 4467251 := bstep (se 1 (by rfl) ⟨3350438, by rfl⟩ : syracuseStep 4467251 = 6700877) B6700877
theorem B2206259 : Blo 976593 2206259 := bstep (se 1 (by rfl) ⟨1654694, by rfl⟩ : syracuseStep 2206259 = 3309389) B3309389
theorem B1649227 : Blo 976593 1649227 := bstep (se 1 (by rfl) ⟨1236920, by rfl⟩ : syracuseStep 1649227 = 2473841) B2473841
theorem B2206295 : Blo 976593 2206295 := bstep (se 1 (by rfl) ⟨1654721, by rfl⟩ : syracuseStep 2206295 = 3309443) B3309443
theorem B3353177 : Blo 976593 3353177 := bstep (se 2 (by rfl) ⟨1257441, by rfl⟩ : syracuseStep 3353177 = 2514883) B2514883
theorem B1649369 : Blo 976593 1649369 := bstep (se 2 (by rfl) ⟨618513, by rfl⟩ : syracuseStep 1649369 = 1237027) B1237027
theorem B1649497 : Blo 976593 1649497 := bstep (se 2 (by rfl) ⟨618561, by rfl⟩ : syracuseStep 1649497 = 1237123) B1237123
theorem B15051845 : Blo 976593 15051845 := bstep (se 4 (by rfl) ⟨1411110, by rfl⟩ : syracuseStep 15051845 = 2822221) B2822221
theorem B30125357 : Blo 976593 30125357 := bstep (se 3 (by rfl) ⟨5648504, by rfl⟩ : syracuseStep 30125357 = 11297009) B11297009
theorem B1650071 : Blo 976593 1650071 := bstep (se 1 (by rfl) ⟨1237553, by rfl⟩ : syracuseStep 1650071 = 2475107) B2475107
theorem B3354049 : Blo 976593 3354049 := bstep (se 2 (by rfl) ⟨1257768, by rfl⟩ : syracuseStep 3354049 = 2515537) B2515537
theorem B1650199 : Blo 976593 1650199 := bstep (se 1 (by rfl) ⟨1237649, by rfl⟩ : syracuseStep 1650199 = 2475299) B2475299
theorem B3714605 : Blo 976593 3714605 := bstep (se 3 (by rfl) ⟨696488, by rfl⟩ : syracuseStep 3714605 = 1392977) B1392977
theorem B1322635 : Blo 976593 1322635 := bstep (se 1 (by rfl) ⟨991976, by rfl⟩ : syracuseStep 1322635 = 1983953) B1983953
theorem B4697779 : Blo 976593 4697779 := bstep (se 1 (by rfl) ⟨3523334, by rfl⟩ : syracuseStep 4697779 = 7046669) B7046669
theorem B4173515 : Blo 976593 4173515 := bstep (se 1 (by rfl) ⟨3130136, by rfl⟩ : syracuseStep 4173515 = 6260273) B6260273
theorem B1060619 : Blo 976593 1060619 := bstep (se 1 (by rfl) ⟨795464, by rfl⟩ : syracuseStep 1060619 = 1590929) B1590929
theorem B7417817 : Blo 976593 7417817 := bstep (se 2 (by rfl) ⟨2781681, by rfl⟩ : syracuseStep 7417817 = 5563363) B5563363
theorem B4173875 : Blo 976593 4173875 := bstep (se 1 (by rfl) ⟨3130406, by rfl⟩ : syracuseStep 4173875 = 6260813) B6260813
theorem B1486937 : Blo 976593 1486937 := bstep (se 2 (by rfl) ⟨557601, by rfl⟩ : syracuseStep 1486937 = 1115203) B1115203
theorem B1650827 : Blo 976593 1650827 := bstep (se 1 (by rfl) ⟨1238120, by rfl⟩ : syracuseStep 1650827 = 2476241) B2476241
theorem B1650955 : Blo 976593 1650955 := bstep (se 1 (by rfl) ⟨1238216, by rfl⟩ : syracuseStep 1650955 = 2476433) B2476433
theorem B3715379 : Blo 976593 3715379 := bstep (se 1 (by rfl) ⟨2786534, by rfl⟩ : syracuseStep 3715379 = 5573069) B5573069
theorem B1651097 : Blo 976593 1651097 := bstep (se 2 (by rfl) ⟨619161, by rfl⟩ : syracuseStep 1651097 = 1238323) B1238323
theorem B1880513 : Blo 976593 1880513 := bstep (se 2 (by rfl) ⟨705192, by rfl⟩ : syracuseStep 1880513 = 1410385) B1410385
theorem B1323479 : Blo 976593 1323479 := bstep (se 1 (by rfl) ⟨992609, by rfl⟩ : syracuseStep 1323479 = 1985219) B1985219
theorem B1651225 : Blo 976593 1651225 := bstep (se 2 (by rfl) ⟨619209, by rfl⟩ : syracuseStep 1651225 = 1238419) B1238419
theorem B7156259 : Blo 976593 7156259 := bstep (se 1 (by rfl) ⟨5367194, by rfl⟩ : syracuseStep 7156259 = 10734389) B10734389
theorem B1487575 : Blo 976593 1487575 := bstep (se 1 (by rfl) ⟨1115681, by rfl⟩ : syracuseStep 1487575 = 2231363) B2231363
theorem B10597337 : Blo 976593 10597337 := bstep (se 2 (by rfl) ⟨3974001, by rfl⟩ : syracuseStep 10597337 = 7948003) B7948003
theorem B1651799 : Blo 976593 1651799 := bstep (se 1 (by rfl) ⟨1238849, by rfl⟩ : syracuseStep 1651799 = 2477699) B2477699
theorem B4961411 : Blo 976593 4961411 := bstep (se 1 (by rfl) ⟨3721058, by rfl⟩ : syracuseStep 4961411 = 7442117) B7442117
theorem B1651927 : Blo 976593 1651927 := bstep (se 1 (by rfl) ⟨1238945, by rfl⟩ : syracuseStep 1651927 = 2477891) B2477891
theorem B1488203 : Blo 976593 1488203 := bstep (se 1 (by rfl) ⟨1116152, by rfl⟩ : syracuseStep 1488203 = 2232305) B2232305
theorem B5027345 : Blo 976593 5027345 := bstep (se 2 (by rfl) ⟨1885254, by rfl⟩ : syracuseStep 5027345 = 3770509) B3770509
theorem B1980119 : Blo 976593 1980119 := bstep (se 1 (by rfl) ⟨1485089, by rfl⟩ : syracuseStep 1980119 = 2970179) B2970179
theorem B3716867 : Blo 976593 3716867 := bstep (se 1 (by rfl) ⟨2787650, by rfl⟩ : syracuseStep 3716867 = 5575301) B5575301
theorem B1652555 : Blo 976593 1652555 := bstep (se 1 (by rfl) ⟨1239416, by rfl⟩ : syracuseStep 1652555 = 2478833) B2478833
theorem B5584733 : Blo 976593 5584733 := bstep (se 3 (by rfl) ⟨1047137, by rfl⟩ : syracuseStep 5584733 = 2094275) B2094275
theorem B1652683 : Blo 976593 1652683 := bstep (se 1 (by rfl) ⟨1239512, by rfl⟩ : syracuseStep 1652683 = 2479025) B2479025
theorem B1325143 : Blo 976593 1325143 := bstep (se 1 (by rfl) ⟨993857, by rfl⟩ : syracuseStep 1325143 = 1987715) B1987715
theorem B1652825 : Blo 976593 1652825 := bstep (se 2 (by rfl) ⟨619809, by rfl⟩ : syracuseStep 1652825 = 1239619) B1239619
theorem B3717323 : Blo 976593 3717323 := bstep (se 1 (by rfl) ⟨2787992, by rfl⟩ : syracuseStep 3717323 = 5575985) B5575985
theorem B1390807 : Blo 976593 1390807 := bstep (se 1 (by rfl) ⟨1043105, by rfl⟩ : syracuseStep 1390807 = 2086211) B2086211
theorem B1652953 : Blo 976593 1652953 := bstep (se 2 (by rfl) ⟨619857, by rfl⟩ : syracuseStep 1652953 = 1239715) B1239715
theorem B3717521 : Blo 976593 3717521 := bstep (se 2 (by rfl) ⟨1394070, by rfl⟩ : syracuseStep 3717521 = 2788141) B2788141
theorem B1489303 : Blo 976593 1489303 := bstep (se 1 (by rfl) ⟨1116977, by rfl⟩ : syracuseStep 1489303 = 2233955) B2233955
theorem B4471319 : Blo 976593 4471319 := bstep (se 1 (by rfl) ⟨3353489, by rfl⟩ : syracuseStep 4471319 = 6706979) B6706979
theorem B2472727 : Blo 976593 2472727 := bstep (se 1 (by rfl) ⟨1854545, by rfl⟩ : syracuseStep 2472727 = 3709091) B3709091
theorem B1653527 : Blo 976593 1653527 := bstep (se 1 (by rfl) ⟨1240145, by rfl⟩ : syracuseStep 1653527 = 2480291) B2480291
theorem B1653655 : Blo 976593 1653655 := bstep (se 1 (by rfl) ⟨1240241, by rfl⟩ : syracuseStep 1653655 = 2480483) B2480483
theorem B1391627 : Blo 976593 1391627 := bstep (se 1 (by rfl) ⟨1043720, by rfl⟩ : syracuseStep 1391627 = 2087441) B2087441
theorem B3718295 : Blo 976593 3718295 := bstep (se 1 (by rfl) ⟨2788721, by rfl⟩ : syracuseStep 3718295 = 5577443) B5577443
theorem B2473163 : Blo 976593 2473163 := bstep (se 1 (by rfl) ⟨1854872, by rfl⟩ : syracuseStep 2473163 = 3709745) B3709745
theorem B7421219 : Blo 976593 7421219 := bstep (se 1 (by rfl) ⟨5565914, by rfl⟩ : syracuseStep 7421219 = 11131829) B11131829
theorem B1588567 : Blo 976593 1588567 := bstep (se 1 (by rfl) ⟨1191425, by rfl⟩ : syracuseStep 1588567 = 2382851) B2382851
theorem B3718493 : Blo 976593 3718493 := bstep (se 3 (by rfl) ⟨697217, by rfl⟩ : syracuseStep 3718493 = 1394435) B1394435
theorem B1654283 : Blo 976593 1654283 := bstep (se 1 (by rfl) ⟨1240712, by rfl⟩ : syracuseStep 1654283 = 2481425) B2481425
theorem B2473537 : Blo 976593 2473537 := bstep (se 2 (by rfl) ⟨927576, by rfl⟩ : syracuseStep 2473537 = 1855153) B1855153
theorem B1654411 : Blo 976593 1654411 := bstep (se 1 (by rfl) ⟨1240808, by rfl⟩ : syracuseStep 1654411 = 2481617) B2481617
theorem B1883915 : Blo 976593 1883915 := bstep (se 1 (by rfl) ⟨1412936, by rfl⟩ : syracuseStep 1883915 = 2825873) B2825873
theorem B1654553 : Blo 976593 1654553 := bstep (se 2 (by rfl) ⟨620457, by rfl⟩ : syracuseStep 1654553 = 1240915) B1240915
theorem B1654681 : Blo 976593 1654681 := bstep (se 2 (by rfl) ⟨620505, by rfl⟩ : syracuseStep 1654681 = 1241011) B1241011
theorem B1785815 : Blo 976593 1785815 := bstep (se 1 (by rfl) ⟨1339361, by rfl⟩ : syracuseStep 1785815 = 2678723) B2678723
theorem B6439013 : Blo 976593 6439013 := bstep (se 4 (by rfl) ⟨603657, by rfl⟩ : syracuseStep 6439013 = 1207315) B1207315
theorem B2474135 : Blo 976593 2474135 := bstep (se 1 (by rfl) ⟨1855601, by rfl⟩ : syracuseStep 2474135 = 3711203) B3711203
theorem B16695557 : Blo 976593 16695557 := bstep (se 4 (by rfl) ⟨1565208, by rfl⟩ : syracuseStep 16695557 = 3130417) B3130417
theorem B4702529 : Blo 976593 4702529 := bstep (se 2 (by rfl) ⟨1763448, by rfl⟩ : syracuseStep 4702529 = 3526897) B3526897
theorem B6275393 : Blo 976593 6275393 := bstep (se 2 (by rfl) ⟨2353272, by rfl⟩ : syracuseStep 6275393 = 4706545) B4706545
theorem B21152117 : Blo 976593 21152117 := bstep (se 5 (by rfl) ⟨991505, by rfl⟩ : syracuseStep 21152117 = 1983011) B1983011
theorem B3129803 : Blo 976593 3129803 := bstep (se 1 (by rfl) ⟨2347352, by rfl⟩ : syracuseStep 3129803 = 4694705) B4694705
theorem B64471565 : Blo 976593 64471565 := bstep (se 3 (by rfl) ⟨12088418, by rfl⟩ : syracuseStep 64471565 = 24176837) B24176837
theorem B3129931 : Blo 976593 3129931 := bstep (se 1 (by rfl) ⟨2347448, by rfl⟩ : syracuseStep 3129931 = 4694897) B4694897
theorem B3130007 : Blo 976593 3130007 := bstep (se 1 (by rfl) ⟨2347505, by rfl⟩ : syracuseStep 3130007 = 4695011) B4695011
theorem B40682225 : Blo 976593 40682225 := bstep (se 2 (by rfl) ⟨15255834, by rfl⟩ : syracuseStep 40682225 = 30511669) B30511669
theorem B1098679 : Blo 976593 1098679 := bstep (se 1 (by rfl) ⟨824009, by rfl⟩ : syracuseStep 1098679 = 1648019) B1648019
theorem B2474945 : Blo 976593 2474945 := bstep (se 2 (by rfl) ⟨928104, by rfl⟩ : syracuseStep 2474945 = 1856209) B1856209
theorem B4178947 : Blo 976593 4178947 := bstep (se 1 (by rfl) ⟨3134210, by rfl⟩ : syracuseStep 4178947 = 6268421) B6268421
theorem B1590359 : Blo 976593 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B1098859 : Blo 976593 1098859 := bstep (se 1 (by rfl) ⟨824144, by rfl⟩ : syracuseStep 1098859 = 1648289) B1648289
theorem B1098967 : Blo 976593 1098967 := bstep (se 1 (by rfl) ⟨824225, by rfl⟩ : syracuseStep 1098967 = 1648451) B1648451
theorem B3720451 : Blo 976593 3720451 := bstep (se 1 (by rfl) ⟨2790338, by rfl⟩ : syracuseStep 3720451 = 5580677) B5580677
theorem B4179289 : Blo 976593 4179289 := bstep (se 2 (by rfl) ⟨1567233, by rfl⟩ : syracuseStep 4179289 = 3134467) B3134467
theorem B1099147 : Blo 976593 1099147 := bstep (se 1 (by rfl) ⟨824360, by rfl⟩ : syracuseStep 1099147 = 1648721) B1648721
theorem B2475481 : Blo 976593 2475481 := bstep (se 2 (by rfl) ⟨928305, by rfl⟩ : syracuseStep 2475481 = 1856611) B1856611
theorem B1099255 : Blo 976593 1099255 := bstep (se 1 (by rfl) ⟨824441, by rfl⟩ : syracuseStep 1099255 = 1648883) B1648883
theorem B3720755 : Blo 976593 3720755 := bstep (se 1 (by rfl) ⟨2790566, by rfl⟩ : syracuseStep 3720755 = 5581133) B5581133
theorem B1099435 : Blo 976593 1099435 := bstep (se 1 (by rfl) ⟨824576, by rfl⟩ : syracuseStep 1099435 = 1649153) B1649153
theorem B1099543 : Blo 976593 1099543 := bstep (se 1 (by rfl) ⟨824657, by rfl⟩ : syracuseStep 1099543 = 1649315) B1649315
theorem B1099723 : Blo 976593 1099723 := bstep (se 1 (by rfl) ⟨824792, by rfl⟩ : syracuseStep 1099723 = 1649585) B1649585
theorem B1099831 : Blo 976593 1099831 := bstep (se 1 (by rfl) ⟨824873, by rfl⟩ : syracuseStep 1099831 = 1649747) B1649747
theorem B3721409 : Blo 976593 3721409 := bstep (se 2 (by rfl) ⟨1395528, by rfl⟩ : syracuseStep 3721409 = 2791057) B2791057
theorem B1100011 : Blo 976593 1100011 := bstep (se 1 (by rfl) ⟨825008, by rfl⟩ : syracuseStep 1100011 = 1650017) B1650017
theorem B4180247 : Blo 976593 4180247 := bstep (se 1 (by rfl) ⟨3135185, by rfl⟩ : syracuseStep 4180247 = 6270371) B6270371
theorem B4704587 : Blo 976593 4704587 := bstep (se 1 (by rfl) ⟨3528440, by rfl⟩ : syracuseStep 4704587 = 7056881) B7056881
theorem B1100119 : Blo 976593 1100119 := bstep (se 1 (by rfl) ⟨825089, by rfl⟩ : syracuseStep 1100119 = 1650179) B1650179
theorem B1100299 : Blo 976593 1100299 := bstep (se 1 (by rfl) ⟨825224, by rfl⟩ : syracuseStep 1100299 = 1650449) B1650449
theorem B2476595 : Blo 976593 2476595 := bstep (se 1 (by rfl) ⟨1857446, by rfl⟩ : syracuseStep 2476595 = 3714893) B3714893
theorem B1100407 : Blo 976593 1100407 := bstep (se 1 (by rfl) ⟨825305, by rfl⟩ : syracuseStep 1100407 = 1650611) B1650611
theorem B1100587 : Blo 976593 1100587 := bstep (se 1 (by rfl) ⟨825440, by rfl⟩ : syracuseStep 1100587 = 1650881) B1650881
theorem B3296051 : Blo 976593 3296051 := bstep (se 1 (by rfl) ⟨2472038, by rfl⟩ : syracuseStep 3296051 = 4944077) B4944077
theorem B2476889 : Blo 976593 2476889 := bstep (se 2 (by rfl) ⟨928833, by rfl⟩ : syracuseStep 2476889 = 1857667) B1857667
theorem B1100695 : Blo 976593 1100695 := bstep (se 1 (by rfl) ⟨825521, by rfl⟩ : syracuseStep 1100695 = 1651043) B1651043
theorem B1854515 : Blo 976593 1854515 := bstep (se 1 (by rfl) ⟨1390886, by rfl⟩ : syracuseStep 1854515 = 2781773) B2781773
theorem B3296321 : Blo 976593 3296321 := bstep (se 2 (by rfl) ⟨1236120, by rfl⟩ : syracuseStep 3296321 = 2472241) B2472241
theorem B1100875 : Blo 976593 1100875 := bstep (se 1 (by rfl) ⟨825656, by rfl⟩ : syracuseStep 1100875 = 1651313) B1651313
theorem B1100983 : Blo 976593 1100983 := bstep (se 1 (by rfl) ⟨825737, by rfl⟩ : syracuseStep 1100983 = 1651475) B1651475
theorem B1854667 : Blo 976593 1854667 := bstep (se 1 (by rfl) ⟨1391000, by rfl⟩ : syracuseStep 1854667 = 2782001) B2782001
theorem B1985867 : Blo 976593 1985867 := bstep (se 1 (by rfl) ⟨1489400, by rfl⟩ : syracuseStep 1985867 = 2978801) B2978801
theorem B1101163 : Blo 976593 1101163 := bstep (se 1 (by rfl) ⟨825872, by rfl⟩ : syracuseStep 1101163 = 1651745) B1651745
theorem B3722669 : Blo 976593 3722669 := bstep (se 3 (by rfl) ⟨698000, by rfl⟩ : syracuseStep 3722669 = 1396001) B1396001
theorem B3722699 : Blo 976593 3722699 := bstep (se 1 (by rfl) ⟨2792024, by rfl⟩ : syracuseStep 3722699 = 5584049) B5584049
theorem B1101271 : Blo 976593 1101271 := bstep (se 1 (by rfl) ⟨825953, by rfl⟩ : syracuseStep 1101271 = 1651907) B1651907
theorem B2117081 : Blo 976593 2117081 := bstep (se 2 (by rfl) ⟨793905, by rfl⟩ : syracuseStep 2117081 = 1587811) B1587811
theorem B1855001 : Blo 976593 1855001 := bstep (se 2 (by rfl) ⟨695625, by rfl⟩ : syracuseStep 1855001 = 1391251) B1391251
theorem B8474147 : Blo 976593 8474147 := bstep (se 1 (by rfl) ⟨6355610, by rfl⟩ : syracuseStep 8474147 = 12711221) B12711221
theorem B3296861 : Blo 976593 3296861 := bstep (se 3 (by rfl) ⟨618161, by rfl⟩ : syracuseStep 3296861 = 1236323) B1236323
theorem B1101451 : Blo 976593 1101451 := bstep (se 1 (by rfl) ⟨826088, by rfl⟩ : syracuseStep 1101451 = 1652177) B1652177
theorem B6704819 : Blo 976593 6704819 := bstep (se 1 (by rfl) ⟨5028614, by rfl⟩ : syracuseStep 6704819 = 10057229) B10057229
theorem B1101559 : Blo 976593 1101559 := bstep (se 1 (by rfl) ⟨826169, by rfl⟩ : syracuseStep 1101559 = 1652339) B1652339
theorem B1101739 : Blo 976593 1101739 := bstep (se 1 (by rfl) ⟨826304, by rfl⟩ : syracuseStep 1101739 = 1652609) B1652609
theorem B4181939 : Blo 976593 4181939 := bstep (se 1 (by rfl) ⟨3136454, by rfl⟩ : syracuseStep 4181939 = 6272909) B6272909
theorem B5656499 : Blo 976593 5656499 := bstep (se 1 (by rfl) ⟨4242374, by rfl⟩ : syracuseStep 5656499 = 8484749) B8484749
theorem B1986547 : Blo 976593 1986547 := bstep (se 1 (by rfl) ⟨1489910, by rfl⟩ : syracuseStep 1986547 = 2979821) B2979821
theorem B1101847 : Blo 976593 1101847 := bstep (se 1 (by rfl) ⟨826385, by rfl⟩ : syracuseStep 1101847 = 1652771) B1652771
theorem B1855639 : Blo 976593 1855639 := bstep (se 1 (by rfl) ⟨1391729, by rfl⟩ : syracuseStep 1855639 = 2783459) B2783459
theorem B1102027 : Blo 976593 1102027 := bstep (se 1 (by rfl) ⟨826520, by rfl⟩ : syracuseStep 1102027 = 1653041) B1653041
theorem B1790219 : Blo 976593 1790219 := bstep (se 1 (by rfl) ⟨1342664, by rfl⟩ : syracuseStep 1790219 = 2685329) B2685329
theorem B1102135 : Blo 976593 1102135 := bstep (se 1 (by rfl) ⟨826601, by rfl⟩ : syracuseStep 1102135 = 1653203) B1653203
theorem B1986905 : Blo 976593 1986905 := bstep (se 2 (by rfl) ⟨745089, by rfl⟩ : syracuseStep 1986905 = 1490179) B1490179
theorem B2478539 : Blo 976593 2478539 := bstep (se 1 (by rfl) ⟨1858904, by rfl⟩ : syracuseStep 2478539 = 3717809) B3717809
theorem B3822041 : Blo 976593 3822041 := bstep (se 2 (by rfl) ⟨1433265, by rfl⟩ : syracuseStep 3822041 = 2866531) B2866531
theorem B1102315 : Blo 976593 1102315 := bstep (se 1 (by rfl) ⟨826736, by rfl⟩ : syracuseStep 1102315 = 1653473) B1653473
theorem B3527171 : Blo 976593 3527171 := bstep (se 1 (by rfl) ⟨2645378, by rfl⟩ : syracuseStep 3527171 = 5290757) B5290757
theorem B7426565 : Blo 976593 7426565 := bstep (se 4 (by rfl) ⟨696240, by rfl⟩ : syracuseStep 7426565 = 1392481) B1392481
theorem B6279697 : Blo 976593 6279697 := bstep (se 2 (by rfl) ⟨2354886, by rfl⟩ : syracuseStep 6279697 = 4709773) B4709773
theorem B1102423 : Blo 976593 1102423 := bstep (se 1 (by rfl) ⟨826817, by rfl⟩ : syracuseStep 1102423 = 1653635) B1653635
theorem B2347699 : Blo 976593 2347699 := bstep (se 1 (by rfl) ⟨1760774, by rfl⟩ : syracuseStep 2347699 = 3521549) B3521549
theorem B3297995 : Blo 976593 3297995 := bstep (se 1 (by rfl) ⟨2473496, by rfl⟩ : syracuseStep 3297995 = 4946993) B4946993
theorem B1102603 : Blo 976593 1102603 := bstep (se 1 (by rfl) ⟨826952, by rfl⟩ : syracuseStep 1102603 = 1653905) B1653905
theorem B7951121 : Blo 976593 7951121 := bstep (se 2 (by rfl) ⟨2981670, by rfl⟩ : syracuseStep 7951121 = 5963341) B5963341
theorem B1102711 : Blo 976593 1102711 := bstep (se 1 (by rfl) ⟨827033, by rfl⟩ : syracuseStep 1102711 = 1654067) B1654067
theorem B1856459 : Blo 976593 1856459 := bstep (se 1 (by rfl) ⟨1392344, by rfl⟩ : syracuseStep 1856459 = 2784689) B2784689
theorem B3298265 : Blo 976593 3298265 := bstep (se 2 (by rfl) ⟨1236849, by rfl⟩ : syracuseStep 3298265 = 2473699) B2473699
theorem B1856513 : Blo 976593 1856513 := bstep (se 2 (by rfl) ⟨696192, by rfl⟩ : syracuseStep 1856513 = 1392385) B1392385
theorem B1102891 : Blo 976593 1102891 := bstep (se 1 (by rfl) ⟨827168, by rfl⟩ : syracuseStep 1102891 = 1654337) B1654337
theorem B11293789 : Blo 976593 11293789 := bstep (se 3 (by rfl) ⟨2117585, by rfl⟩ : syracuseStep 11293789 = 4235171) B4235171
theorem B1102999 : Blo 976593 1102999 := bstep (se 1 (by rfl) ⟨827249, by rfl⟩ : syracuseStep 1102999 = 1654499) B1654499
theorem B2086091 : Blo 976593 2086091 := bstep (se 1 (by rfl) ⟨1564568, by rfl⟩ : syracuseStep 2086091 = 3129137) B3129137
theorem B7525649 : Blo 976593 7525649 := bstep (se 2 (by rfl) ⟨2822118, by rfl⟩ : syracuseStep 7525649 = 5644237) B5644237
theorem B2479511 : Blo 976593 2479511 := bstep (se 1 (by rfl) ⟨1859633, by rfl⟩ : syracuseStep 2479511 = 3719267) B3719267
theorem B3528281 : Blo 976593 3528281 := bstep (se 2 (by rfl) ⟨1323105, by rfl⟩ : syracuseStep 3528281 = 2646211) B2646211
theorem B3298967 : Blo 976593 3298967 := bstep (se 1 (by rfl) ⟨2474225, by rfl⟩ : syracuseStep 3298967 = 4948451) B4948451
theorem B2086553 : Blo 976593 2086553 := bstep (se 2 (by rfl) ⟨782457, by rfl⟩ : syracuseStep 2086553 = 1564915) B1564915
theorem B1857431 : Blo 976593 1857431 := bstep (se 1 (by rfl) ⟨1393073, by rfl⟩ : syracuseStep 1857431 = 2786147) B2786147
theorem B8935373 : Blo 976593 8935373 := bstep (se 3 (by rfl) ⟨1675382, by rfl⟩ : syracuseStep 8935373 = 3350765) B3350765
theorem B4413457 : Blo 976593 4413457 := bstep (se 2 (by rfl) ⟨1655046, by rfl⟩ : syracuseStep 4413457 = 3310093) B3310093
theorem B2480179 : Blo 976593 2480179 := bstep (se 1 (by rfl) ⟨1860134, by rfl⟩ : syracuseStep 2480179 = 3720269) B3720269
theorem B2349121 : Blo 976593 2349121 := bstep (se 2 (by rfl) ⟨880920, by rfl⟩ : syracuseStep 2349121 = 1761841) B1761841
theorem B11884637 : Blo 976593 11884637 := bstep (se 3 (by rfl) ⟨2228369, by rfl⟩ : syracuseStep 11884637 = 4456739) B4456739
theorem B3299507 : Blo 976593 3299507 := bstep (se 1 (by rfl) ⟨2474630, by rfl⟩ : syracuseStep 3299507 = 4949261) B4949261
theorem B2480321 : Blo 976593 2480321 := bstep (se 2 (by rfl) ⟨930120, by rfl⟩ : syracuseStep 2480321 = 1860241) B1860241
theorem B37673261 : Blo 976593 37673261 := bstep (se 3 (by rfl) ⟨7063736, by rfl⟩ : syracuseStep 37673261 = 14127473) B14127473
theorem B7919947 : Blo 976593 7919947 := bstep (se 1 (by rfl) ⟨5939960, by rfl⟩ : syracuseStep 7919947 = 11879921) B11879921
theorem B1857971 : Blo 976593 1857971 := bstep (se 1 (by rfl) ⟨1393478, by rfl⟩ : syracuseStep 1857971 = 2786957) B2786957
theorem B3299777 : Blo 976593 3299777 := bstep (se 2 (by rfl) ⟨1237416, by rfl⟩ : syracuseStep 3299777 = 2474833) B2474833
theorem B4184621 : Blo 976593 4184621 := bstep (se 3 (by rfl) ⟨784616, by rfl⟩ : syracuseStep 4184621 = 1569233) B1569233
theorem B1464971 : Blo 976593 1464971 := bstep (se 1 (by rfl) ⟨1098728, by rfl⟩ : syracuseStep 1464971 = 2197457) B2197457
theorem B1759895 : Blo 976593 1759895 := bstep (se 1 (by rfl) ⟨1319921, by rfl⟩ : syracuseStep 1759895 = 2639843) B2639843
theorem B1464983 : Blo 976593 1464983 := bstep (se 1 (by rfl) ⟨1098737, by rfl⟩ : syracuseStep 1464983 = 2197475) B2197475
theorem B1759937 : Blo 976593 1759937 := bstep (se 2 (by rfl) ⟨659976, by rfl⟩ : syracuseStep 1759937 = 1319953) B1319953
theorem B1465049 : Blo 976593 1465049 := bstep (se 2 (by rfl) ⟨549393, by rfl⟩ : syracuseStep 1465049 = 1098787) B1098787
theorem B2087731 : Blo 976593 2087731 := bstep (se 1 (by rfl) ⟨1565798, by rfl⟩ : syracuseStep 2087731 = 3131597) B3131597
theorem B1465163 : Blo 976593 1465163 := bstep (se 1 (by rfl) ⟨1098872, by rfl⟩ : syracuseStep 1465163 = 2197745) B2197745
theorem B5299019 : Blo 976593 5299019 := bstep (se 1 (by rfl) ⟨3974264, by rfl⟩ : syracuseStep 5299019 = 7948529) B7948529
theorem B1465175 : Blo 976593 1465175 := bstep (se 1 (by rfl) ⟨1098881, by rfl⟩ : syracuseStep 1465175 = 2197763) B2197763
theorem B7428995 : Blo 976593 7428995 := bstep (se 1 (by rfl) ⟨5571746, by rfl⟩ : syracuseStep 7428995 = 11143493) B11143493
theorem B1465241 : Blo 976593 1465241 := bstep (se 2 (by rfl) ⟨549465, by rfl⟩ : syracuseStep 1465241 = 1098931) B1098931
theorem B1858457 : Blo 976593 1858457 := bstep (se 2 (by rfl) ⟨696921, by rfl⟩ : syracuseStep 1858457 = 1393843) B1393843
theorem B3300317 : Blo 976593 3300317 := bstep (se 3 (by rfl) ⟨618809, by rfl⟩ : syracuseStep 3300317 = 1237619) B1237619
theorem B1465355 : Blo 976593 1465355 := bstep (se 1 (by rfl) ⟨1099016, by rfl⟩ : syracuseStep 1465355 = 2198033) B2198033
theorem B1465367 : Blo 976593 1465367 := bstep (se 1 (by rfl) ⟨1099025, by rfl⟩ : syracuseStep 1465367 = 2198051) B2198051
theorem B2120755 : Blo 976593 2120755 := bstep (se 1 (by rfl) ⟨1590566, by rfl⟩ : syracuseStep 2120755 = 3181133) B3181133
theorem B3529793 : Blo 976593 3529793 := bstep (se 2 (by rfl) ⟨1323672, by rfl⟩ : syracuseStep 3529793 = 2647345) B2647345
theorem B1236055 : Blo 976593 1236055 := bstep (se 1 (by rfl) ⟨927041, by rfl⟩ : syracuseStep 1236055 = 1854083) B1854083
theorem B1465433 : Blo 976593 1465433 := bstep (se 2 (by rfl) ⟨549537, by rfl⟩ : syracuseStep 1465433 = 1099075) B1099075
theorem B1465547 : Blo 976593 1465547 := bstep (se 1 (by rfl) ⟨1099160, by rfl⟩ : syracuseStep 1465547 = 2198321) B2198321
theorem B1465559 : Blo 976593 1465559 := bstep (se 1 (by rfl) ⟨1099169, by rfl⟩ : syracuseStep 1465559 = 2198339) B2198339
theorem B2088193 : Blo 976593 2088193 := bstep (se 2 (by rfl) ⟨783072, by rfl⟩ : syracuseStep 2088193 = 1566145) B1566145
theorem B1465625 : Blo 976593 1465625 := bstep (se 2 (by rfl) ⟨549609, by rfl⟩ : syracuseStep 1465625 = 1099219) B1099219
theorem B15850853 : Blo 976593 15850853 := bstep (se 4 (by rfl) ⟨1486017, by rfl⟩ : syracuseStep 15850853 = 2972035) B2972035
theorem B1465739 : Blo 976593 1465739 := bstep (se 1 (by rfl) ⟨1099304, by rfl⟩ : syracuseStep 1465739 = 2198609) B2198609
theorem B1465751 : Blo 976593 1465751 := bstep (se 1 (by rfl) ⟨1099313, by rfl⟩ : syracuseStep 1465751 = 2198627) B2198627
theorem B2645399 : Blo 976593 2645399 := bstep (se 1 (by rfl) ⟨1984049, by rfl⟩ : syracuseStep 2645399 = 3968099) B3968099
theorem B2481587 : Blo 976593 2481587 := bstep (se 1 (by rfl) ⟨1861190, by rfl⟩ : syracuseStep 2481587 = 3722381) B3722381
theorem B1465817 : Blo 976593 1465817 := bstep (se 2 (by rfl) ⟨549681, by rfl⟩ : syracuseStep 1465817 = 1099363) B1099363
theorem B1465931 : Blo 976593 1465931 := bstep (se 1 (by rfl) ⟨1099448, by rfl⟩ : syracuseStep 1465931 = 2198897) B2198897
theorem B1465943 : Blo 976593 1465943 := bstep (se 1 (by rfl) ⟨1099457, by rfl⟩ : syracuseStep 1465943 = 2198915) B2198915
theorem B1466009 : Blo 976593 1466009 := bstep (se 2 (by rfl) ⟨549753, by rfl⟩ : syracuseStep 1466009 = 1099507) B1099507
theorem B1564363 : Blo 976593 1564363 := bstep (se 1 (by rfl) ⟨1173272, by rfl⟩ : syracuseStep 1564363 = 2346545) B2346545
theorem B1466123 : Blo 976593 1466123 := bstep (se 1 (by rfl) ⟨1099592, by rfl⟩ : syracuseStep 1466123 = 2199185) B2199185
theorem B1466135 : Blo 976593 1466135 := bstep (se 1 (by rfl) ⟨1099601, by rfl⟩ : syracuseStep 1466135 = 2199203) B2199203
theorem B1564505 : Blo 976593 1564505 := bstep (se 2 (by rfl) ⟨586689, by rfl⟩ : syracuseStep 1564505 = 1173379) B1173379
theorem B1466201 : Blo 976593 1466201 := bstep (se 2 (by rfl) ⟨549825, by rfl⟩ : syracuseStep 1466201 = 1099651) B1099651
theorem B4710275 : Blo 976593 4710275 := bstep (se 1 (by rfl) ⟨3532706, by rfl⟩ : syracuseStep 4710275 = 7065413) B7065413
theorem B1466315 : Blo 976593 1466315 := bstep (se 1 (by rfl) ⟨1099736, by rfl⟩ : syracuseStep 1466315 = 2199473) B2199473
theorem B2482123 : Blo 976593 2482123 := bstep (se 1 (by rfl) ⟨1861592, by rfl⟩ : syracuseStep 2482123 = 3723185) B3723185
theorem B1466327 : Blo 976593 1466327 := bstep (se 1 (by rfl) ⟨1099745, by rfl⟩ : syracuseStep 1466327 = 2199491) B2199491
theorem B2088919 : Blo 976593 2088919 := bstep (se 1 (by rfl) ⟨1566689, by rfl⟩ : syracuseStep 2088919 = 3133379) B3133379
theorem B1466393 : Blo 976593 1466393 := bstep (se 2 (by rfl) ⟨549897, by rfl⟩ : syracuseStep 1466393 = 1099795) B1099795
theorem B3301451 : Blo 976593 3301451 := bstep (se 1 (by rfl) ⟨2476088, by rfl⟩ : syracuseStep 3301451 = 4952177) B4952177
theorem B1466507 : Blo 976593 1466507 := bstep (se 1 (by rfl) ⟨1099880, by rfl⟩ : syracuseStep 1466507 = 2199761) B2199761
theorem B1466519 : Blo 976593 1466519 := bstep (se 1 (by rfl) ⟨1099889, by rfl⟩ : syracuseStep 1466519 = 2199779) B2199779
theorem B1466585 : Blo 976593 1466585 := bstep (se 2 (by rfl) ⟨549969, by rfl⟩ : syracuseStep 1466585 = 1099939) B1099939
theorem B1466699 : Blo 976593 1466699 := bstep (se 1 (by rfl) ⟨1100024, by rfl⟩ : syracuseStep 1466699 = 2200049) B2200049
theorem B1859915 : Blo 976593 1859915 := bstep (se 1 (by rfl) ⟨1394936, by rfl⟩ : syracuseStep 1859915 = 2789873) B2789873
theorem B1466711 : Blo 976593 1466711 := bstep (se 1 (by rfl) ⟨1100033, by rfl⟩ : syracuseStep 1466711 = 2200067) B2200067
theorem B1761625 : Blo 976593 1761625 := bstep (se 2 (by rfl) ⟨660609, by rfl⟩ : syracuseStep 1761625 = 1321219) B1321219
theorem B3301721 : Blo 976593 3301721 := bstep (se 2 (by rfl) ⟨1238145, by rfl⟩ : syracuseStep 3301721 = 2476291) B2476291
theorem B1466777 : Blo 976593 1466777 := bstep (se 2 (by rfl) ⟨550041, by rfl⟩ : syracuseStep 1466777 = 1100083) B1100083
theorem B1860097 : Blo 976593 1860097 := bstep (se 2 (by rfl) ⟨697536, by rfl⟩ : syracuseStep 1860097 = 1395073) B1395073
theorem B1466891 : Blo 976593 1466891 := bstep (se 1 (by rfl) ⟨1100168, by rfl⟩ : syracuseStep 1466891 = 2200337) B2200337
theorem B1466903 : Blo 976593 1466903 := bstep (se 1 (by rfl) ⟨1100177, by rfl⟩ : syracuseStep 1466903 = 2200355) B2200355
theorem B1466969 : Blo 976593 1466969 := bstep (se 2 (by rfl) ⟨550113, by rfl⟩ : syracuseStep 1466969 = 1100227) B1100227
theorem B1467083 : Blo 976593 1467083 := bstep (se 1 (by rfl) ⟨1100312, by rfl⟩ : syracuseStep 1467083 = 2200625) B2200625
theorem B1467095 : Blo 976593 1467095 := bstep (se 1 (by rfl) ⟨1100321, by rfl⟩ : syracuseStep 1467095 = 2200643) B2200643
theorem B1237771 : Blo 976593 1237771 := bstep (se 1 (by rfl) ⟨928328, by rfl⟩ : syracuseStep 1237771 = 1856657) B1856657
theorem B2089739 : Blo 976593 2089739 := bstep (se 1 (by rfl) ⟨1567304, by rfl⟩ : syracuseStep 2089739 = 3134609) B3134609
theorem B1565465 : Blo 976593 1565465 := bstep (se 2 (by rfl) ⟨587049, by rfl⟩ : syracuseStep 1565465 = 1174099) B1174099
theorem B1467161 : Blo 976593 1467161 := bstep (se 2 (by rfl) ⟨550185, by rfl⟩ : syracuseStep 1467161 = 1100371) B1100371
theorem B5563181 : Blo 976593 5563181 := bstep (se 3 (by rfl) ⟨1043096, by rfl⟩ : syracuseStep 5563181 = 2086193) B2086193
theorem B1467275 : Blo 976593 1467275 := bstep (se 1 (by rfl) ⟨1100456, by rfl⟩ : syracuseStep 1467275 = 2200913) B2200913
theorem B1467287 : Blo 976593 1467287 := bstep (se 1 (by rfl) ⟨1100465, by rfl⟩ : syracuseStep 1467287 = 2200931) B2200931
theorem B1860545 : Blo 976593 1860545 := bstep (se 2 (by rfl) ⟨697704, by rfl⟩ : syracuseStep 1860545 = 1395409) B1395409
theorem B1467353 : Blo 976593 1467353 := bstep (se 2 (by rfl) ⟨550257, by rfl⟩ : syracuseStep 1467353 = 1100515) B1100515
theorem B3302423 : Blo 976593 3302423 := bstep (se 1 (by rfl) ⟨2476817, by rfl⟩ : syracuseStep 3302423 = 4953635) B4953635
theorem B1467467 : Blo 976593 1467467 := bstep (se 1 (by rfl) ⟨1100600, by rfl⟩ : syracuseStep 1467467 = 2201201) B2201201
theorem B1467479 : Blo 976593 1467479 := bstep (se 1 (by rfl) ⟨1100609, by rfl⟩ : syracuseStep 1467479 = 2201219) B2201219
theorem B1467545 : Blo 976593 1467545 := bstep (se 2 (by rfl) ⟨550329, by rfl⟩ : syracuseStep 1467545 = 1100659) B1100659
theorem B1467659 : Blo 976593 1467659 := bstep (se 1 (by rfl) ⟨1100744, by rfl⟩ : syracuseStep 1467659 = 2201489) B2201489
theorem B1467671 : Blo 976593 1467671 := bstep (se 1 (by rfl) ⟨1100753, by rfl⟩ : syracuseStep 1467671 = 2201507) B2201507
theorem B1860887 : Blo 976593 1860887 := bstep (se 1 (by rfl) ⟨1395665, by rfl⟩ : syracuseStep 1860887 = 2791331) B2791331
theorem B1467737 : Blo 976593 1467737 := bstep (se 2 (by rfl) ⟨550401, by rfl⟩ : syracuseStep 1467737 = 1100803) B1100803
theorem B1467851 : Blo 976593 1467851 := bstep (se 1 (by rfl) ⟨1100888, by rfl⟩ : syracuseStep 1467851 = 2201777) B2201777
theorem B1467863 : Blo 976593 1467863 := bstep (se 1 (by rfl) ⟨1100897, by rfl⟩ : syracuseStep 1467863 = 2201795) B2201795
theorem B1467929 : Blo 976593 1467929 := bstep (se 2 (by rfl) ⟨550473, by rfl⟩ : syracuseStep 1467929 = 1100947) B1100947
theorem B3302963 : Blo 976593 3302963 := bstep (se 1 (by rfl) ⟨2477222, by rfl⟩ : syracuseStep 3302963 = 4954445) B4954445
theorem B6350411 : Blo 976593 6350411 := bstep (se 1 (by rfl) ⟨4762808, by rfl⟩ : syracuseStep 6350411 = 9525617) B9525617
theorem B2090585 : Blo 976593 2090585 := bstep (se 2 (by rfl) ⟨783969, by rfl⟩ : syracuseStep 2090585 = 1567939) B1567939
theorem B1468043 : Blo 976593 1468043 := bstep (se 1 (by rfl) ⟨1101032, by rfl⟩ : syracuseStep 1468043 = 2202065) B2202065
theorem B1468055 : Blo 976593 1468055 := bstep (se 1 (by rfl) ⟨1101041, by rfl⟩ : syracuseStep 1468055 = 2202083) B2202083
theorem B976599 : Blo 976593 976599 := bstep (se 1 (by rfl) ⟨732449, by rfl⟩ : syracuseStep 976599 = 1464899) B1464899
theorem B1238743 : Blo 976593 1238743 := bstep (se 1 (by rfl) ⟨929057, by rfl⟩ : syracuseStep 1238743 = 1858115) B1858115
theorem B1468121 : Blo 976593 1468121 := bstep (se 2 (by rfl) ⟨550545, by rfl⟩ : syracuseStep 1468121 = 1101091) B1101091
theorem B976619 : Blo 976593 976619 := bstep (se 1 (by rfl) ⟨732464, by rfl⟩ : syracuseStep 976619 = 1464929) B1464929
theorem B976631 : Blo 976593 976631 := bstep (se 1 (by rfl) ⟨732473, by rfl⟩ : syracuseStep 976631 = 1464947) B1464947
theorem B976651 : Blo 976593 976651 := bstep (se 1 (by rfl) ⟨732488, by rfl⟩ : syracuseStep 976651 = 1464977) B1464977
theorem B976663 : Blo 976593 976663 := bstep (se 1 (by rfl) ⟨732497, by rfl⟩ : syracuseStep 976663 = 1464995) B1464995
theorem B976683 : Blo 976593 976683 := bstep (se 1 (by rfl) ⟨732512, by rfl⟩ : syracuseStep 976683 = 1465025) B1465025
theorem B976695 : Blo 976593 976695 := bstep (se 1 (by rfl) ⟨732521, by rfl⟩ : syracuseStep 976695 = 1465043) B1465043
theorem B3303233 : Blo 976593 3303233 := bstep (se 2 (by rfl) ⟨1238712, by rfl⟩ : syracuseStep 3303233 = 2477425) B2477425
theorem B4187969 : Blo 976593 4187969 := bstep (se 2 (by rfl) ⟨1570488, by rfl⟩ : syracuseStep 4187969 = 3140977) B3140977
theorem B976715 : Blo 976593 976715 := bstep (se 1 (by rfl) ⟨732536, by rfl⟩ : syracuseStep 976715 = 1465073) B1465073
theorem B1468235 : Blo 976593 1468235 := bstep (se 1 (by rfl) ⟨1101176, by rfl⟩ : syracuseStep 1468235 = 2202353) B2202353
theorem B976727 : Blo 976593 976727 := bstep (se 1 (by rfl) ⟨732545, by rfl⟩ : syracuseStep 976727 = 1465091) B1465091
theorem B1468247 : Blo 976593 1468247 := bstep (se 1 (by rfl) ⟨1101185, by rfl⟩ : syracuseStep 1468247 = 2202371) B2202371
theorem B976747 : Blo 976593 976747 := bstep (se 1 (by rfl) ⟨732560, by rfl⟩ : syracuseStep 976747 = 1465121) B1465121
theorem B976759 : Blo 976593 976759 := bstep (se 1 (by rfl) ⟨732569, by rfl⟩ : syracuseStep 976759 = 1465139) B1465139
theorem B976779 : Blo 976593 976779 := bstep (se 1 (by rfl) ⟨732584, by rfl⟩ : syracuseStep 976779 = 1465169) B1465169
theorem B976791 : Blo 976593 976791 := bstep (se 1 (by rfl) ⟨732593, by rfl⟩ : syracuseStep 976791 = 1465187) B1465187
theorem B1763225 : Blo 976593 1763225 := bstep (se 2 (by rfl) ⟨661209, by rfl⟩ : syracuseStep 1763225 = 1322419) B1322419
theorem B1468313 : Blo 976593 1468313 := bstep (se 2 (by rfl) ⟨550617, by rfl⟩ : syracuseStep 1468313 = 1101235) B1101235
theorem B976811 : Blo 976593 976811 := bstep (se 1 (by rfl) ⟨732608, by rfl⟩ : syracuseStep 976811 = 1465217) B1465217
theorem B1861555 : Blo 976593 1861555 := bstep (se 1 (by rfl) ⟨1396166, by rfl⟩ : syracuseStep 1861555 = 2792333) B2792333
theorem B976823 : Blo 976593 976823 := bstep (se 1 (by rfl) ⟨732617, by rfl⟩ : syracuseStep 976823 = 1465235) B1465235
theorem B3172289 : Blo 976593 3172289 := bstep (se 2 (by rfl) ⟨1189608, by rfl⟩ : syracuseStep 3172289 = 2379217) B2379217
theorem B976843 : Blo 976593 976843 := bstep (se 1 (by rfl) ⟨732632, by rfl⟩ : syracuseStep 976843 = 1465265) B1465265
theorem B976855 : Blo 976593 976855 := bstep (se 1 (by rfl) ⟨732641, by rfl⟩ : syracuseStep 976855 = 1465283) B1465283
theorem B976875 : Blo 976593 976875 := bstep (se 1 (by rfl) ⟨732656, by rfl⟩ : syracuseStep 976875 = 1465313) B1465313
theorem B976887 : Blo 976593 976887 := bstep (se 1 (by rfl) ⟨732665, by rfl⟩ : syracuseStep 976887 = 1465331) B1465331
theorem B976907 : Blo 976593 976907 := bstep (se 1 (by rfl) ⟨732680, by rfl⟩ : syracuseStep 976907 = 1465361) B1465361
theorem B1468427 : Blo 976593 1468427 := bstep (se 1 (by rfl) ⟨1101320, by rfl⟩ : syracuseStep 1468427 = 2202641) B2202641
theorem B976919 : Blo 976593 976919 := bstep (se 1 (by rfl) ⟨732689, by rfl⟩ : syracuseStep 976919 = 1465379) B1465379
theorem B1468439 : Blo 976593 1468439 := bstep (se 1 (by rfl) ⟨1101329, by rfl⟩ : syracuseStep 1468439 = 2202659) B2202659
theorem B4024343 : Blo 976593 4024343 := bstep (se 1 (by rfl) ⟨3018257, by rfl⟩ : syracuseStep 4024343 = 6036515) B6036515
theorem B976939 : Blo 976593 976939 := bstep (se 1 (by rfl) ⟨732704, by rfl⟩ : syracuseStep 976939 = 1465409) B1465409
theorem B3762221 : Blo 976593 3762221 := bstep (se 3 (by rfl) ⟨705416, by rfl⟩ : syracuseStep 3762221 = 1410833) B1410833
theorem B976951 : Blo 976593 976951 := bstep (se 1 (by rfl) ⟨732713, by rfl⟩ : syracuseStep 976951 = 1465427) B1465427
theorem B976971 : Blo 976593 976971 := bstep (se 1 (by rfl) ⟨732728, by rfl⟩ : syracuseStep 976971 = 1465457) B1465457
theorem B976983 : Blo 976593 976983 := bstep (se 1 (by rfl) ⟨732737, by rfl⟩ : syracuseStep 976983 = 1465475) B1465475
theorem B1468505 : Blo 976593 1468505 := bstep (se 2 (by rfl) ⟨550689, by rfl⟩ : syracuseStep 1468505 = 1101379) B1101379
theorem B977003 : Blo 976593 977003 := bstep (se 1 (by rfl) ⟨732752, by rfl⟩ : syracuseStep 977003 = 1465505) B1465505
theorem B977015 : Blo 976593 977015 := bstep (se 1 (by rfl) ⟨732761, by rfl⟩ : syracuseStep 977015 = 1465523) B1465523
theorem B977035 : Blo 976593 977035 := bstep (se 1 (by rfl) ⟨732776, by rfl⟩ : syracuseStep 977035 = 1465553) B1465553
theorem B977047 : Blo 976593 977047 := bstep (se 1 (by rfl) ⟨732785, by rfl⟩ : syracuseStep 977047 = 1465571) B1465571
theorem B3139735 : Blo 976593 3139735 := bstep (se 1 (by rfl) ⟨2354801, by rfl⟩ : syracuseStep 3139735 = 4709603) B4709603
theorem B4188311 : Blo 976593 4188311 := bstep (se 1 (by rfl) ⟨3141233, by rfl⟩ : syracuseStep 4188311 = 6282467) B6282467
theorem B977067 : Blo 976593 977067 := bstep (se 1 (by rfl) ⟨732800, by rfl⟩ : syracuseStep 977067 = 1465601) B1465601
theorem B977079 : Blo 976593 977079 := bstep (se 1 (by rfl) ⟨732809, by rfl⟩ : syracuseStep 977079 = 1465619) B1465619
theorem B977099 : Blo 976593 977099 := bstep (se 1 (by rfl) ⟨732824, by rfl⟩ : syracuseStep 977099 = 1465649) B1465649
theorem B1468619 : Blo 976593 1468619 := bstep (se 1 (by rfl) ⟨1101464, by rfl⟩ : syracuseStep 1468619 = 2202929) B2202929
theorem B7432397 : Blo 976593 7432397 := bstep (se 3 (by rfl) ⟨1393574, by rfl⟩ : syracuseStep 7432397 = 2787149) B2787149
theorem B977111 : Blo 976593 977111 := bstep (se 1 (by rfl) ⟨732833, by rfl⟩ : syracuseStep 977111 = 1465667) B1465667
theorem B1468631 : Blo 976593 1468631 := bstep (se 1 (by rfl) ⟨1101473, by rfl⟩ : syracuseStep 1468631 = 2202947) B2202947
theorem B977131 : Blo 976593 977131 := bstep (se 1 (by rfl) ⟨732848, by rfl⟩ : syracuseStep 977131 = 1465697) B1465697
theorem B2091251 : Blo 976593 2091251 := bstep (se 1 (by rfl) ⟨1568438, by rfl⟩ : syracuseStep 2091251 = 3136877) B3136877
theorem B977143 : Blo 976593 977143 := bstep (se 1 (by rfl) ⟨732857, by rfl⟩ : syracuseStep 977143 = 1465715) B1465715
theorem B977163 : Blo 976593 977163 := bstep (se 1 (by rfl) ⟨732872, by rfl⟩ : syracuseStep 977163 = 1465745) B1465745
theorem B977175 : Blo 976593 977175 := bstep (se 1 (by rfl) ⟨732881, by rfl⟩ : syracuseStep 977175 = 1465763) B1465763
theorem B1468697 : Blo 976593 1468697 := bstep (se 2 (by rfl) ⟨550761, by rfl⟩ : syracuseStep 1468697 = 1101523) B1101523
theorem B977195 : Blo 976593 977195 := bstep (se 1 (by rfl) ⟨732896, by rfl⟩ : syracuseStep 977195 = 1465793) B1465793
theorem B977207 : Blo 976593 977207 := bstep (se 1 (by rfl) ⟨732905, by rfl⟩ : syracuseStep 977207 = 1465811) B1465811
theorem B977227 : Blo 976593 977227 := bstep (se 1 (by rfl) ⟨732920, by rfl⟩ : syracuseStep 977227 = 1465841) B1465841
theorem B5368139 : Blo 976593 5368139 := bstep (se 1 (by rfl) ⟨4026104, by rfl⟩ : syracuseStep 5368139 = 8052209) B8052209
theorem B977239 : Blo 976593 977239 := bstep (se 1 (by rfl) ⟨732929, by rfl⟩ : syracuseStep 977239 = 1465859) B1465859
theorem B3303773 : Blo 976593 3303773 := bstep (se 3 (by rfl) ⟨619457, by rfl⟩ : syracuseStep 3303773 = 1238915) B1238915
theorem B977259 : Blo 976593 977259 := bstep (se 1 (by rfl) ⟨732944, by rfl⟩ : syracuseStep 977259 = 1465889) B1465889
theorem B977271 : Blo 976593 977271 := bstep (se 1 (by rfl) ⟨732953, by rfl⟩ : syracuseStep 977271 = 1465907) B1465907
theorem B977291 : Blo 976593 977291 := bstep (se 1 (by rfl) ⟨732968, by rfl⟩ : syracuseStep 977291 = 1465937) B1465937
theorem B1468811 : Blo 976593 1468811 := bstep (se 1 (by rfl) ⟨1101608, by rfl⟩ : syracuseStep 1468811 = 2203217) B2203217
theorem B977303 : Blo 976593 977303 := bstep (se 1 (by rfl) ⟨732977, by rfl⟩ : syracuseStep 977303 = 1465955) B1465955
theorem B1468823 : Blo 976593 1468823 := bstep (se 1 (by rfl) ⟨1101617, by rfl⟩ : syracuseStep 1468823 = 2203235) B2203235
theorem B977323 : Blo 976593 977323 := bstep (se 1 (by rfl) ⟨732992, by rfl⟩ : syracuseStep 977323 = 1465985) B1465985
theorem B977335 : Blo 976593 977335 := bstep (se 1 (by rfl) ⟨733001, by rfl⟩ : syracuseStep 977335 = 1466003) B1466003
theorem B977355 : Blo 976593 977355 := bstep (se 1 (by rfl) ⟨733016, by rfl⟩ : syracuseStep 977355 = 1466033) B1466033
theorem B977367 : Blo 976593 977367 := bstep (se 1 (by rfl) ⟨733025, by rfl⟩ : syracuseStep 977367 = 1466051) B1466051
theorem B1468889 : Blo 976593 1468889 := bstep (se 2 (by rfl) ⟨550833, by rfl⟩ : syracuseStep 1468889 = 1101667) B1101667
theorem B977387 : Blo 976593 977387 := bstep (se 1 (by rfl) ⟨733040, by rfl⟩ : syracuseStep 977387 = 1466081) B1466081
theorem B977399 : Blo 976593 977399 := bstep (se 1 (by rfl) ⟨733049, by rfl⟩ : syracuseStep 977399 = 1466099) B1466099
theorem B9038341 : Blo 976593 9038341 := bstep (se 4 (by rfl) ⟨847344, by rfl⟩ : syracuseStep 9038341 = 1694689) B1694689
theorem B977419 : Blo 976593 977419 := bstep (se 1 (by rfl) ⟨733064, by rfl⟩ : syracuseStep 977419 = 1466129) B1466129
theorem B1239563 : Blo 976593 1239563 := bstep (se 1 (by rfl) ⟨929672, by rfl⟩ : syracuseStep 1239563 = 1859345) B1859345
theorem B977431 : Blo 976593 977431 := bstep (se 1 (by rfl) ⟨733073, by rfl⟩ : syracuseStep 977431 = 1466147) B1466147
theorem B977451 : Blo 976593 977451 := bstep (se 1 (by rfl) ⟨733088, by rfl⟩ : syracuseStep 977451 = 1466177) B1466177
theorem B977463 : Blo 976593 977463 := bstep (se 1 (by rfl) ⟨733097, by rfl⟩ : syracuseStep 977463 = 1466195) B1466195
theorem B977483 : Blo 976593 977483 := bstep (se 1 (by rfl) ⟨733112, by rfl⟩ : syracuseStep 977483 = 1466225) B1466225
theorem B1469003 : Blo 976593 1469003 := bstep (se 1 (by rfl) ⟨1101752, by rfl⟩ : syracuseStep 1469003 = 2203505) B2203505
theorem B977495 : Blo 976593 977495 := bstep (se 1 (by rfl) ⟨733121, by rfl⟩ : syracuseStep 977495 = 1466243) B1466243
theorem B1469015 : Blo 976593 1469015 := bstep (se 1 (by rfl) ⟨1101761, by rfl⟩ : syracuseStep 1469015 = 2203523) B2203523
theorem B977515 : Blo 976593 977515 := bstep (se 1 (by rfl) ⟨733136, by rfl⟩ : syracuseStep 977515 = 1466273) B1466273
theorem B977527 : Blo 976593 977527 := bstep (se 1 (by rfl) ⟨733145, by rfl⟩ : syracuseStep 977527 = 1466291) B1466291
theorem B977547 : Blo 976593 977547 := bstep (se 1 (by rfl) ⟨733160, by rfl⟩ : syracuseStep 977547 = 1466321) B1466321
theorem B977559 : Blo 976593 977559 := bstep (se 1 (by rfl) ⟨733169, by rfl⟩ : syracuseStep 977559 = 1466339) B1466339
theorem B1469081 : Blo 976593 1469081 := bstep (se 2 (by rfl) ⟨550905, by rfl⟩ : syracuseStep 1469081 = 1101811) B1101811
theorem B977579 : Blo 976593 977579 := bstep (se 1 (by rfl) ⟨733184, by rfl⟩ : syracuseStep 977579 = 1466369) B1466369
theorem B7432883 : Blo 976593 7432883 := bstep (se 1 (by rfl) ⟨5574662, by rfl⟩ : syracuseStep 7432883 = 11149325) B11149325
theorem B977591 : Blo 976593 977591 := bstep (se 1 (by rfl) ⟨733193, by rfl⟩ : syracuseStep 977591 = 1466387) B1466387
theorem B977611 : Blo 976593 977611 := bstep (se 1 (by rfl) ⟨733208, by rfl⟩ : syracuseStep 977611 = 1466417) B1466417
theorem B977623 : Blo 976593 977623 := bstep (se 1 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 977623 = 1466435) B1466435
theorem B977643 : Blo 976593 977643 := bstep (se 1 (by rfl) ⟨733232, by rfl⟩ : syracuseStep 977643 = 1466465) B1466465
theorem B977655 : Blo 976593 977655 := bstep (se 1 (by rfl) ⟨733241, by rfl⟩ : syracuseStep 977655 = 1466483) B1466483
theorem B977675 : Blo 976593 977675 := bstep (se 1 (by rfl) ⟨733256, by rfl⟩ : syracuseStep 977675 = 1466513) B1466513
theorem B1469195 : Blo 976593 1469195 := bstep (se 1 (by rfl) ⟨1101896, by rfl⟩ : syracuseStep 1469195 = 2203793) B2203793
theorem B977687 : Blo 976593 977687 := bstep (se 1 (by rfl) ⟨733265, by rfl⟩ : syracuseStep 977687 = 1466531) B1466531
theorem B1469207 : Blo 976593 1469207 := bstep (se 1 (by rfl) ⟨1101905, by rfl⟩ : syracuseStep 1469207 = 2203811) B2203811
theorem B977707 : Blo 976593 977707 := bstep (se 1 (by rfl) ⟨733280, by rfl⟩ : syracuseStep 977707 = 1466561) B1466561
theorem B977719 : Blo 976593 977719 := bstep (se 1 (by rfl) ⟨733289, by rfl⟩ : syracuseStep 977719 = 1466579) B1466579
theorem B977739 : Blo 976593 977739 := bstep (se 1 (by rfl) ⟨733304, by rfl⟩ : syracuseStep 977739 = 1466609) B1466609
theorem B977751 : Blo 976593 977751 := bstep (se 1 (by rfl) ⟨733313, by rfl⟩ : syracuseStep 977751 = 1466627) B1466627
theorem B1469273 : Blo 976593 1469273 := bstep (se 2 (by rfl) ⟨550977, by rfl⟩ : syracuseStep 1469273 = 1101955) B1101955
theorem B977771 : Blo 976593 977771 := bstep (se 1 (by rfl) ⟨733328, by rfl⟩ : syracuseStep 977771 = 1466657) B1466657
theorem B977783 : Blo 976593 977783 := bstep (se 1 (by rfl) ⟨733337, by rfl⟩ : syracuseStep 977783 = 1466675) B1466675
theorem B977803 : Blo 976593 977803 := bstep (se 1 (by rfl) ⟨733352, by rfl⟩ : syracuseStep 977803 = 1466705) B1466705
theorem B977815 : Blo 976593 977815 := bstep (se 1 (by rfl) ⟨733361, by rfl⟩ : syracuseStep 977815 = 1466723) B1466723
theorem B977835 : Blo 976593 977835 := bstep (se 1 (by rfl) ⟨733376, by rfl⟩ : syracuseStep 977835 = 1466753) B1466753
theorem B977847 : Blo 976593 977847 := bstep (se 1 (by rfl) ⟨733385, by rfl⟩ : syracuseStep 977847 = 1466771) B1466771
theorem B977867 : Blo 976593 977867 := bstep (se 1 (by rfl) ⟨733400, by rfl⟩ : syracuseStep 977867 = 1466801) B1466801
theorem B1469387 : Blo 976593 1469387 := bstep (se 1 (by rfl) ⟨1102040, by rfl⟩ : syracuseStep 1469387 = 2204081) B2204081
theorem B977879 : Blo 976593 977879 := bstep (se 1 (by rfl) ⟨733409, by rfl⟩ : syracuseStep 977879 = 1466819) B1466819
theorem B1469399 : Blo 976593 1469399 := bstep (se 1 (by rfl) ⟨1102049, by rfl⟩ : syracuseStep 1469399 = 2204099) B2204099
theorem B167668697 : Blo 976593 167668697 := bstep (se 2 (by rfl) ⟨62875761, by rfl⟩ : syracuseStep 167668697 = 125751523) B125751523
theorem B977899 : Blo 976593 977899 := bstep (se 1 (by rfl) ⟨733424, by rfl⟩ : syracuseStep 977899 = 1466849) B1466849
theorem B1043447 : Blo 976593 1043447 := bstep (se 1 (by rfl) ⟨782585, by rfl⟩ : syracuseStep 1043447 = 1565171) B1565171
theorem B977911 : Blo 976593 977911 := bstep (se 1 (by rfl) ⟨733433, by rfl⟩ : syracuseStep 977911 = 1466867) B1466867
theorem B977931 : Blo 976593 977931 := bstep (se 1 (by rfl) ⟨733448, by rfl⟩ : syracuseStep 977931 = 1466897) B1466897
theorem B977943 : Blo 976593 977943 := bstep (se 1 (by rfl) ⟨733457, by rfl⟩ : syracuseStep 977943 = 1466915) B1466915
theorem B1469465 : Blo 976593 1469465 := bstep (se 2 (by rfl) ⟨551049, by rfl⟩ : syracuseStep 1469465 = 1102099) B1102099
theorem B977963 : Blo 976593 977963 := bstep (se 1 (by rfl) ⟨733472, by rfl⟩ : syracuseStep 977963 = 1466945) B1466945
theorem B977975 : Blo 976593 977975 := bstep (se 1 (by rfl) ⟨733481, by rfl⟩ : syracuseStep 977975 = 1466963) B1466963
theorem B977995 : Blo 976593 977995 := bstep (se 1 (by rfl) ⟨733496, by rfl⟩ : syracuseStep 977995 = 1466993) B1466993
theorem B978007 : Blo 976593 978007 := bstep (se 1 (by rfl) ⟨733505, by rfl⟩ : syracuseStep 978007 = 1467011) B1467011
theorem B978027 : Blo 976593 978027 := bstep (se 1 (by rfl) ⟨733520, by rfl⟩ : syracuseStep 978027 = 1467041) B1467041
theorem B978039 : Blo 976593 978039 := bstep (se 1 (by rfl) ⟨733529, by rfl⟩ : syracuseStep 978039 = 1467059) B1467059
theorem B978059 : Blo 976593 978059 := bstep (se 1 (by rfl) ⟨733544, by rfl⟩ : syracuseStep 978059 = 1467089) B1467089
theorem B1469579 : Blo 976593 1469579 := bstep (se 1 (by rfl) ⟨1102184, by rfl⟩ : syracuseStep 1469579 = 2204369) B2204369
theorem B978071 : Blo 976593 978071 := bstep (se 1 (by rfl) ⟨733553, by rfl⟩ : syracuseStep 978071 = 1467107) B1467107
theorem B1469591 : Blo 976593 1469591 := bstep (se 1 (by rfl) ⟨1102193, by rfl⟩ : syracuseStep 1469591 = 2204387) B2204387
theorem B978091 : Blo 976593 978091 := bstep (se 1 (by rfl) ⟨733568, by rfl⟩ : syracuseStep 978091 = 1467137) B1467137
theorem B52292789 : Blo 976593 52292789 := bstep (se 5 (by rfl) ⟨2451224, by rfl⟩ : syracuseStep 52292789 = 4902449) B4902449
theorem B978103 : Blo 976593 978103 := bstep (se 1 (by rfl) ⟨733577, by rfl⟩ : syracuseStep 978103 = 1467155) B1467155
theorem B2092225 : Blo 976593 2092225 := bstep (se 2 (by rfl) ⟨784584, by rfl⟩ : syracuseStep 2092225 = 1569169) B1569169
theorem B978123 : Blo 976593 978123 := bstep (se 1 (by rfl) ⟨733592, by rfl⟩ : syracuseStep 978123 = 1467185) B1467185
theorem B1240267 : Blo 976593 1240267 := bstep (se 1 (by rfl) ⟨930200, by rfl⟩ : syracuseStep 1240267 = 1860401) B1860401
theorem B978135 : Blo 976593 978135 := bstep (se 1 (by rfl) ⟨733601, by rfl⟩ : syracuseStep 978135 = 1467203) B1467203
theorem B1469657 : Blo 976593 1469657 := bstep (se 2 (by rfl) ⟨551121, by rfl⟩ : syracuseStep 1469657 = 1102243) B1102243
theorem B978155 : Blo 976593 978155 := bstep (se 1 (by rfl) ⟨733616, by rfl⟩ : syracuseStep 978155 = 1467233) B1467233
theorem B978167 : Blo 976593 978167 := bstep (se 1 (by rfl) ⟨733625, by rfl⟩ : syracuseStep 978167 = 1467251) B1467251
theorem B978187 : Blo 976593 978187 := bstep (se 1 (by rfl) ⟨733640, by rfl⟩ : syracuseStep 978187 = 1467281) B1467281
theorem B978199 : Blo 976593 978199 := bstep (se 1 (by rfl) ⟨733649, by rfl⟩ : syracuseStep 978199 = 1467299) B1467299
theorem B978219 : Blo 976593 978219 := bstep (se 1 (by rfl) ⟨733664, by rfl⟩ : syracuseStep 978219 = 1467329) B1467329
theorem B978231 : Blo 976593 978231 := bstep (se 1 (by rfl) ⟨733673, by rfl⟩ : syracuseStep 978231 = 1467347) B1467347
theorem B978251 : Blo 976593 978251 := bstep (se 1 (by rfl) ⟨733688, by rfl⟩ : syracuseStep 978251 = 1467377) B1467377
theorem B1469771 : Blo 976593 1469771 := bstep (se 1 (by rfl) ⟨1102328, by rfl⟩ : syracuseStep 1469771 = 2204657) B2204657
theorem B978263 : Blo 976593 978263 := bstep (se 1 (by rfl) ⟨733697, by rfl⟩ : syracuseStep 978263 = 1467395) B1467395
theorem B1469783 : Blo 976593 1469783 := bstep (se 1 (by rfl) ⟨1102337, by rfl⟩ : syracuseStep 1469783 = 2204675) B2204675
theorem B978283 : Blo 976593 978283 := bstep (se 1 (by rfl) ⟨733712, by rfl⟩ : syracuseStep 978283 = 1467425) B1467425
theorem B978295 : Blo 976593 978295 := bstep (se 1 (by rfl) ⟨733721, by rfl⟩ : syracuseStep 978295 = 1467443) B1467443
theorem B978315 : Blo 976593 978315 := bstep (se 1 (by rfl) ⟨733736, by rfl⟩ : syracuseStep 978315 = 1467473) B1467473
theorem B978327 : Blo 976593 978327 := bstep (se 1 (by rfl) ⟨733745, by rfl⟩ : syracuseStep 978327 = 1467491) B1467491
theorem B1469849 : Blo 976593 1469849 := bstep (se 2 (by rfl) ⟨551193, by rfl⟩ : syracuseStep 1469849 = 1102387) B1102387
theorem B978347 : Blo 976593 978347 := bstep (se 1 (by rfl) ⟨733760, by rfl⟩ : syracuseStep 978347 = 1467521) B1467521
theorem B978359 : Blo 976593 978359 := bstep (se 1 (by rfl) ⟨733769, by rfl⟩ : syracuseStep 978359 = 1467539) B1467539
theorem B2092481 : Blo 976593 2092481 := bstep (se 2 (by rfl) ⟨784680, by rfl⟩ : syracuseStep 2092481 = 1569361) B1569361
theorem B978379 : Blo 976593 978379 := bstep (se 1 (by rfl) ⟨733784, by rfl⟩ : syracuseStep 978379 = 1467569) B1467569
theorem B3304907 : Blo 976593 3304907 := bstep (se 1 (by rfl) ⟨2478680, by rfl⟩ : syracuseStep 3304907 = 4957361) B4957361
theorem B978391 : Blo 976593 978391 := bstep (se 1 (by rfl) ⟨733793, by rfl⟩ : syracuseStep 978391 = 1467587) B1467587
theorem B1240535 : Blo 976593 1240535 := bstep (se 1 (by rfl) ⟨930401, by rfl⟩ : syracuseStep 1240535 = 1860803) B1860803
theorem B978411 : Blo 976593 978411 := bstep (se 1 (by rfl) ⟨733808, by rfl⟩ : syracuseStep 978411 = 1467617) B1467617
theorem B978423 : Blo 976593 978423 := bstep (se 1 (by rfl) ⟨733817, by rfl⟩ : syracuseStep 978423 = 1467635) B1467635
theorem B978443 : Blo 976593 978443 := bstep (se 1 (by rfl) ⟨733832, by rfl⟩ : syracuseStep 978443 = 1467665) B1467665
theorem B1469963 : Blo 976593 1469963 := bstep (se 1 (by rfl) ⟨1102472, by rfl⟩ : syracuseStep 1469963 = 2204945) B2204945
theorem B978455 : Blo 976593 978455 := bstep (se 1 (by rfl) ⟨733841, by rfl⟩ : syracuseStep 978455 = 1467683) B1467683
theorem B2092567 : Blo 976593 2092567 := bstep (se 1 (by rfl) ⟨1569425, by rfl⟩ : syracuseStep 2092567 = 3138851) B3138851
theorem B1469975 : Blo 976593 1469975 := bstep (se 1 (by rfl) ⟨1102481, by rfl⟩ : syracuseStep 1469975 = 2204963) B2204963
theorem B978475 : Blo 976593 978475 := bstep (se 1 (by rfl) ⟨733856, by rfl⟩ : syracuseStep 978475 = 1467713) B1467713
theorem B978487 : Blo 976593 978487 := bstep (se 1 (by rfl) ⟨733865, by rfl⟩ : syracuseStep 978487 = 1467731) B1467731
theorem B978507 : Blo 976593 978507 := bstep (se 1 (by rfl) ⟨733880, by rfl⟩ : syracuseStep 978507 = 1467761) B1467761
theorem B978519 : Blo 976593 978519 := bstep (se 1 (by rfl) ⟨733889, by rfl⟩ : syracuseStep 978519 = 1467779) B1467779
theorem B1470041 : Blo 976593 1470041 := bstep (se 2 (by rfl) ⟨551265, by rfl⟩ : syracuseStep 1470041 = 1102531) B1102531
theorem B8351333 : Blo 976593 8351333 := bstep (se 4 (by rfl) ⟨782937, by rfl⟩ : syracuseStep 8351333 = 1565875) B1565875
theorem B978539 : Blo 976593 978539 := bstep (se 1 (by rfl) ⟨733904, by rfl⟩ : syracuseStep 978539 = 1467809) B1467809
theorem B978551 : Blo 976593 978551 := bstep (se 1 (by rfl) ⟨733913, by rfl⟩ : syracuseStep 978551 = 1467827) B1467827
theorem B4025987 : Blo 976593 4025987 := bstep (se 1 (by rfl) ⟨3019490, by rfl⟩ : syracuseStep 4025987 = 6038981) B6038981
theorem B978571 : Blo 976593 978571 := bstep (se 1 (by rfl) ⟨733928, by rfl⟩ : syracuseStep 978571 = 1467857) B1467857
theorem B978583 : Blo 976593 978583 := bstep (se 1 (by rfl) ⟨733937, by rfl⟩ : syracuseStep 978583 = 1467875) B1467875
theorem B1044139 : Blo 976593 1044139 := bstep (se 1 (by rfl) ⟨783104, by rfl⟩ : syracuseStep 1044139 = 1566209) B1566209
theorem B978603 : Blo 976593 978603 := bstep (se 1 (by rfl) ⟨733952, by rfl⟩ : syracuseStep 978603 = 1467905) B1467905
theorem B978615 : Blo 976593 978615 := bstep (se 1 (by rfl) ⟨733961, by rfl⟩ : syracuseStep 978615 = 1467923) B1467923
theorem B978635 : Blo 976593 978635 := bstep (se 1 (by rfl) ⟨733976, by rfl⟩ : syracuseStep 978635 = 1467953) B1467953
theorem B1470155 : Blo 976593 1470155 := bstep (se 1 (by rfl) ⟨1102616, by rfl⟩ : syracuseStep 1470155 = 2205233) B2205233
theorem B978647 : Blo 976593 978647 := bstep (se 1 (by rfl) ⟨733985, by rfl⟩ : syracuseStep 978647 = 1467971) B1467971
theorem B1470167 : Blo 976593 1470167 := bstep (se 1 (by rfl) ⟨1102625, by rfl⟩ : syracuseStep 1470167 = 2205251) B2205251
theorem B3305177 : Blo 976593 3305177 := bstep (se 2 (by rfl) ⟨1239441, by rfl⟩ : syracuseStep 3305177 = 2478883) B2478883
theorem B978667 : Blo 976593 978667 := bstep (se 1 (by rfl) ⟨734000, by rfl⟩ : syracuseStep 978667 = 1468001) B1468001
theorem B978679 : Blo 976593 978679 := bstep (se 1 (by rfl) ⟨734009, by rfl⟩ : syracuseStep 978679 = 1468019) B1468019
theorem B978699 : Blo 976593 978699 := bstep (se 1 (by rfl) ⟨734024, by rfl⟩ : syracuseStep 978699 = 1468049) B1468049
theorem B978711 : Blo 976593 978711 := bstep (se 1 (by rfl) ⟨734033, by rfl⟩ : syracuseStep 978711 = 1468067) B1468067
theorem B1470233 : Blo 976593 1470233 := bstep (se 2 (by rfl) ⟨551337, by rfl⟩ : syracuseStep 1470233 = 1102675) B1102675
theorem B978731 : Blo 976593 978731 := bstep (se 1 (by rfl) ⟨734048, by rfl⟩ : syracuseStep 978731 = 1468097) B1468097
theorem B978743 : Blo 976593 978743 := bstep (se 1 (by rfl) ⟨734057, by rfl⟩ : syracuseStep 978743 = 1468115) B1468115
theorem B978763 : Blo 976593 978763 := bstep (se 1 (by rfl) ⟨734072, by rfl⟩ : syracuseStep 978763 = 1468145) B1468145
theorem B978775 : Blo 976593 978775 := bstep (se 1 (by rfl) ⟨734081, by rfl⟩ : syracuseStep 978775 = 1468163) B1468163
theorem B978795 : Blo 976593 978795 := bstep (se 1 (by rfl) ⟨734096, by rfl⟩ : syracuseStep 978795 = 1468193) B1468193
theorem B978807 : Blo 976593 978807 := bstep (se 1 (by rfl) ⟨734105, by rfl⟩ : syracuseStep 978807 = 1468211) B1468211
theorem B978827 : Blo 976593 978827 := bstep (se 1 (by rfl) ⟨734120, by rfl⟩ : syracuseStep 978827 = 1468241) B1468241
theorem B1470347 : Blo 976593 1470347 := bstep (se 1 (by rfl) ⟨1102760, by rfl⟩ : syracuseStep 1470347 = 2205521) B2205521
theorem B978839 : Blo 976593 978839 := bstep (se 1 (by rfl) ⟨734129, by rfl⟩ : syracuseStep 978839 = 1468259) B1468259
theorem B1470359 : Blo 976593 1470359 := bstep (se 1 (by rfl) ⟨1102769, by rfl⟩ : syracuseStep 1470359 = 2205539) B2205539
theorem B978859 : Blo 976593 978859 := bstep (se 1 (by rfl) ⟨734144, by rfl⟩ : syracuseStep 978859 = 1468289) B1468289
theorem B978871 : Blo 976593 978871 := bstep (se 1 (by rfl) ⟨734153, by rfl⟩ : syracuseStep 978871 = 1468307) B1468307
theorem B978891 : Blo 976593 978891 := bstep (se 1 (by rfl) ⟨734168, by rfl⟩ : syracuseStep 978891 = 1468337) B1468337
theorem B978903 : Blo 976593 978903 := bstep (se 1 (by rfl) ⟨734177, by rfl⟩ : syracuseStep 978903 = 1468355) B1468355
theorem B1470425 : Blo 976593 1470425 := bstep (se 2 (by rfl) ⟨551409, by rfl⟩ : syracuseStep 1470425 = 1102819) B1102819
theorem B978923 : Blo 976593 978923 := bstep (se 1 (by rfl) ⟨734192, by rfl⟩ : syracuseStep 978923 = 1468385) B1468385
theorem B978935 : Blo 976593 978935 := bstep (se 1 (by rfl) ⟨734201, by rfl⟩ : syracuseStep 978935 = 1468403) B1468403
theorem B978955 : Blo 976593 978955 := bstep (se 1 (by rfl) ⟨734216, by rfl⟩ : syracuseStep 978955 = 1468433) B1468433
theorem B978967 : Blo 976593 978967 := bstep (se 1 (by rfl) ⟨734225, by rfl⟩ : syracuseStep 978967 = 1468451) B1468451
theorem B14315555 : Blo 976593 14315555 := bstep (se 1 (by rfl) ⟨10736666, by rfl⟩ : syracuseStep 14315555 = 21473333) B21473333
theorem B978987 : Blo 976593 978987 := bstep (se 1 (by rfl) ⟨734240, by rfl⟩ : syracuseStep 978987 = 1468481) B1468481
theorem B978999 : Blo 976593 978999 := bstep (se 1 (by rfl) ⟨734249, by rfl⟩ : syracuseStep 978999 = 1468499) B1468499
theorem B979019 : Blo 976593 979019 := bstep (se 1 (by rfl) ⟨734264, by rfl⟩ : syracuseStep 979019 = 1468529) B1468529
theorem B1470539 : Blo 976593 1470539 := bstep (se 1 (by rfl) ⟨1102904, by rfl⟩ : syracuseStep 1470539 = 2205809) B2205809
theorem B979031 : Blo 976593 979031 := bstep (se 1 (by rfl) ⟨734273, by rfl⟩ : syracuseStep 979031 = 1468547) B1468547
theorem B1470551 : Blo 976593 1470551 := bstep (se 1 (by rfl) ⟨1102913, by rfl⟩ : syracuseStep 1470551 = 2205827) B2205827
theorem B7434341 : Blo 976593 7434341 := bstep (se 4 (by rfl) ⟨696969, by rfl⟩ : syracuseStep 7434341 = 1393939) B1393939
theorem B979051 : Blo 976593 979051 := bstep (se 1 (by rfl) ⟨734288, by rfl⟩ : syracuseStep 979051 = 1468577) B1468577
theorem B979063 : Blo 976593 979063 := bstep (se 1 (by rfl) ⟨734297, by rfl⟩ : syracuseStep 979063 = 1468595) B1468595
theorem B979083 : Blo 976593 979083 := bstep (se 1 (by rfl) ⟨734312, by rfl⟩ : syracuseStep 979083 = 1468625) B1468625
theorem B6025367 : Blo 976593 6025367 := bstep (se 1 (by rfl) ⟨4519025, by rfl⟩ : syracuseStep 6025367 = 9038051) B9038051
theorem B979095 : Blo 976593 979095 := bstep (se 1 (by rfl) ⟨734321, by rfl⟩ : syracuseStep 979095 = 1468643) B1468643
theorem B1470617 : Blo 976593 1470617 := bstep (se 2 (by rfl) ⟨551481, by rfl⟩ : syracuseStep 1470617 = 1102963) B1102963
theorem B979115 : Blo 976593 979115 := bstep (se 1 (by rfl) ⟨734336, by rfl⟩ : syracuseStep 979115 = 1468673) B1468673
theorem B979127 : Blo 976593 979127 := bstep (se 1 (by rfl) ⟨734345, by rfl⟩ : syracuseStep 979127 = 1468691) B1468691
theorem B979147 : Blo 976593 979147 := bstep (se 1 (by rfl) ⟨734360, by rfl⟩ : syracuseStep 979147 = 1468721) B1468721
theorem B979159 : Blo 976593 979159 := bstep (se 1 (by rfl) ⟨734369, by rfl⟩ : syracuseStep 979159 = 1468739) B1468739
theorem B979179 : Blo 976593 979179 := bstep (se 1 (by rfl) ⟨734384, by rfl⟩ : syracuseStep 979179 = 1468769) B1468769
theorem B979191 : Blo 976593 979191 := bstep (se 1 (by rfl) ⟨734393, by rfl⟩ : syracuseStep 979191 = 1468787) B1468787
theorem B979211 : Blo 976593 979211 := bstep (se 1 (by rfl) ⟨734408, by rfl⟩ : syracuseStep 979211 = 1468817) B1468817
theorem B1470731 : Blo 976593 1470731 := bstep (se 1 (by rfl) ⟨1103048, by rfl⟩ : syracuseStep 1470731 = 2206097) B2206097
theorem B8352017 : Blo 976593 8352017 := bstep (se 2 (by rfl) ⟨3132006, by rfl⟩ : syracuseStep 8352017 = 6264013) B6264013
theorem B979223 : Blo 976593 979223 := bstep (se 1 (by rfl) ⟨734417, by rfl⟩ : syracuseStep 979223 = 1468835) B1468835
theorem B1470743 : Blo 976593 1470743 := bstep (se 1 (by rfl) ⟨1103057, by rfl⟩ : syracuseStep 1470743 = 2206115) B2206115
theorem B979243 : Blo 976593 979243 := bstep (se 1 (by rfl) ⟨734432, by rfl⟩ : syracuseStep 979243 = 1468865) B1468865
theorem B979255 : Blo 976593 979255 := bstep (se 1 (by rfl) ⟨734441, by rfl⟩ : syracuseStep 979255 = 1468883) B1468883
theorem B979275 : Blo 976593 979275 := bstep (se 1 (by rfl) ⟨734456, by rfl⟩ : syracuseStep 979275 = 1468913) B1468913
theorem B979287 : Blo 976593 979287 := bstep (se 1 (by rfl) ⟨734465, by rfl⟩ : syracuseStep 979287 = 1468931) B1468931
theorem B1470809 : Blo 976593 1470809 := bstep (se 2 (by rfl) ⟨551553, by rfl⟩ : syracuseStep 1470809 = 1103107) B1103107
theorem B979307 : Blo 976593 979307 := bstep (se 1 (by rfl) ⟨734480, by rfl⟩ : syracuseStep 979307 = 1468961) B1468961
theorem B979319 : Blo 976593 979319 := bstep (se 1 (by rfl) ⟨734489, by rfl⟩ : syracuseStep 979319 = 1468979) B1468979
theorem B979339 : Blo 976593 979339 := bstep (se 1 (by rfl) ⟨734504, by rfl⟩ : syracuseStep 979339 = 1469009) B1469009
theorem B979351 : Blo 976593 979351 := bstep (se 1 (by rfl) ⟨734513, by rfl⟩ : syracuseStep 979351 = 1469027) B1469027
theorem B3305879 : Blo 976593 3305879 := bstep (se 1 (by rfl) ⟨2479409, by rfl⟩ : syracuseStep 3305879 = 4958819) B4958819
theorem B979371 : Blo 976593 979371 := bstep (se 1 (by rfl) ⟨734528, by rfl⟩ : syracuseStep 979371 = 1469057) B1469057
theorem B979383 : Blo 976593 979383 := bstep (se 1 (by rfl) ⟨734537, by rfl⟩ : syracuseStep 979383 = 1469075) B1469075
theorem B979403 : Blo 976593 979403 := bstep (se 1 (by rfl) ⟨734552, by rfl⟩ : syracuseStep 979403 = 1469105) B1469105
theorem B979415 : Blo 976593 979415 := bstep (se 1 (by rfl) ⟨734561, by rfl⟩ : syracuseStep 979415 = 1469123) B1469123
theorem B979435 : Blo 976593 979435 := bstep (se 1 (by rfl) ⟨734576, by rfl⟩ : syracuseStep 979435 = 1469153) B1469153
theorem B979447 : Blo 976593 979447 := bstep (se 1 (by rfl) ⟨734585, by rfl⟩ : syracuseStep 979447 = 1469171) B1469171
theorem B979467 : Blo 976593 979467 := bstep (se 1 (by rfl) ⟨734600, by rfl⟩ : syracuseStep 979467 = 1469201) B1469201
theorem B4944401 : Blo 976593 4944401 := bstep (se 2 (by rfl) ⟨1854150, by rfl⟩ : syracuseStep 4944401 = 3708301) B3708301
theorem B979479 : Blo 976593 979479 := bstep (se 1 (by rfl) ⟨734609, by rfl⟩ : syracuseStep 979479 = 1469219) B1469219
theorem B979499 : Blo 976593 979499 := bstep (se 1 (by rfl) ⟨734624, by rfl⟩ : syracuseStep 979499 = 1469249) B1469249
theorem B979511 : Blo 976593 979511 := bstep (se 1 (by rfl) ⟨734633, by rfl⟩ : syracuseStep 979511 = 1469267) B1469267
theorem B7434827 : Blo 976593 7434827 := bstep (se 1 (by rfl) ⟨5576120, by rfl⟩ : syracuseStep 7434827 = 11152241) B11152241
theorem B979531 : Blo 976593 979531 := bstep (se 1 (by rfl) ⟨734648, by rfl⟩ : syracuseStep 979531 = 1469297) B1469297
theorem B979543 : Blo 976593 979543 := bstep (se 1 (by rfl) ⟨734657, by rfl⟩ : syracuseStep 979543 = 1469315) B1469315
theorem B979563 : Blo 976593 979563 := bstep (se 1 (by rfl) ⟨734672, by rfl⟩ : syracuseStep 979563 = 1469345) B1469345
theorem B979575 : Blo 976593 979575 := bstep (se 1 (by rfl) ⟨734681, by rfl⟩ : syracuseStep 979575 = 1469363) B1469363
theorem B979595 : Blo 976593 979595 := bstep (se 1 (by rfl) ⟨734696, by rfl⟩ : syracuseStep 979595 = 1469393) B1469393
theorem B3568279 : Blo 976593 3568279 := bstep (se 1 (by rfl) ⟨2676209, by rfl⟩ : syracuseStep 3568279 = 5352419) B5352419
theorem B979607 : Blo 976593 979607 := bstep (se 1 (by rfl) ⟨734705, by rfl⟩ : syracuseStep 979607 = 1469411) B1469411
theorem B979627 : Blo 976593 979627 := bstep (se 1 (by rfl) ⟨734720, by rfl⟩ : syracuseStep 979627 = 1469441) B1469441
theorem B4944563 : Blo 976593 4944563 := bstep (se 1 (by rfl) ⟨3708422, by rfl⟩ : syracuseStep 4944563 = 7416845) B7416845
theorem B979639 : Blo 976593 979639 := bstep (se 1 (by rfl) ⟨734729, by rfl⟩ : syracuseStep 979639 = 1469459) B1469459
theorem B979659 : Blo 976593 979659 := bstep (se 1 (by rfl) ⟨734744, by rfl⟩ : syracuseStep 979659 = 1469489) B1469489
theorem B979671 : Blo 976593 979671 := bstep (se 1 (by rfl) ⟨734753, by rfl⟩ : syracuseStep 979671 = 1469507) B1469507
theorem B979691 : Blo 976593 979691 := bstep (se 1 (by rfl) ⟨734768, by rfl⟩ : syracuseStep 979691 = 1469537) B1469537
theorem B979703 : Blo 976593 979703 := bstep (se 1 (by rfl) ⟨734777, by rfl⟩ : syracuseStep 979703 = 1469555) B1469555
theorem B9401093 : Blo 976593 9401093 := bstep (se 4 (by rfl) ⟨881352, by rfl⟩ : syracuseStep 9401093 = 1762705) B1762705
theorem B979723 : Blo 976593 979723 := bstep (se 1 (by rfl) ⟨734792, by rfl⟩ : syracuseStep 979723 = 1469585) B1469585
theorem B979735 : Blo 976593 979735 := bstep (se 1 (by rfl) ⟨734801, by rfl⟩ : syracuseStep 979735 = 1469603) B1469603
theorem B979755 : Blo 976593 979755 := bstep (se 1 (by rfl) ⟨734816, by rfl⟩ : syracuseStep 979755 = 1469633) B1469633
theorem B979767 : Blo 976593 979767 := bstep (se 1 (by rfl) ⟨734825, by rfl⟩ : syracuseStep 979767 = 1469651) B1469651
theorem B979787 : Blo 976593 979787 := bstep (se 1 (by rfl) ⟨734840, by rfl⟩ : syracuseStep 979787 = 1469681) B1469681
theorem B979799 : Blo 976593 979799 := bstep (se 1 (by rfl) ⟨734849, by rfl⟩ : syracuseStep 979799 = 1469699) B1469699
theorem B3765085 : Blo 976593 3765085 := bstep (se 3 (by rfl) ⟨705953, by rfl⟩ : syracuseStep 3765085 = 1411907) B1411907
theorem B979819 : Blo 976593 979819 := bstep (se 1 (by rfl) ⟨734864, by rfl⟩ : syracuseStep 979819 = 1469729) B1469729
theorem B979831 : Blo 976593 979831 := bstep (se 1 (by rfl) ⟨734873, by rfl⟩ : syracuseStep 979831 = 1469747) B1469747
theorem B979851 : Blo 976593 979851 := bstep (se 1 (by rfl) ⟨734888, by rfl⟩ : syracuseStep 979851 = 1469777) B1469777
theorem B979863 : Blo 976593 979863 := bstep (se 1 (by rfl) ⟨734897, by rfl⟩ : syracuseStep 979863 = 1469795) B1469795
theorem B979883 : Blo 976593 979883 := bstep (se 1 (by rfl) ⟨734912, by rfl⟩ : syracuseStep 979883 = 1469825) B1469825
theorem B3306419 : Blo 976593 3306419 := bstep (se 1 (by rfl) ⟨2479814, by rfl⟩ : syracuseStep 3306419 = 4959629) B4959629
theorem B979895 : Blo 976593 979895 := bstep (se 1 (by rfl) ⟨734921, by rfl⟩ : syracuseStep 979895 = 1469843) B1469843
theorem B979915 : Blo 976593 979915 := bstep (se 1 (by rfl) ⟨734936, by rfl⟩ : syracuseStep 979915 = 1469873) B1469873
theorem B979927 : Blo 976593 979927 := bstep (se 1 (by rfl) ⟨734945, by rfl⟩ : syracuseStep 979927 = 1469891) B1469891
theorem B11924441 : Blo 976593 11924441 := bstep (se 2 (by rfl) ⟨4471665, by rfl⟩ : syracuseStep 11924441 = 8943331) B8943331
theorem B979947 : Blo 976593 979947 := bstep (se 1 (by rfl) ⟨734960, by rfl⟩ : syracuseStep 979947 = 1469921) B1469921
theorem B979959 : Blo 976593 979959 := bstep (se 1 (by rfl) ⟨734969, by rfl⟩ : syracuseStep 979959 = 1469939) B1469939
theorem B979979 : Blo 976593 979979 := bstep (se 1 (by rfl) ⟨734984, by rfl⟩ : syracuseStep 979979 = 1469969) B1469969
theorem B979991 : Blo 976593 979991 := bstep (se 1 (by rfl) ⟨734993, by rfl⟩ : syracuseStep 979991 = 1469987) B1469987
theorem B980011 : Blo 976593 980011 := bstep (se 1 (by rfl) ⟨735008, by rfl⟩ : syracuseStep 980011 = 1470017) B1470017
theorem B980023 : Blo 976593 980023 := bstep (se 1 (by rfl) ⟨735017, by rfl⟩ : syracuseStep 980023 = 1470035) B1470035
theorem B980043 : Blo 976593 980043 := bstep (se 1 (by rfl) ⟨735032, by rfl⟩ : syracuseStep 980043 = 1470065) B1470065
theorem B1045591 : Blo 976593 1045591 := bstep (se 1 (by rfl) ⟨784193, by rfl⟩ : syracuseStep 1045591 = 1568387) B1568387
theorem B980055 : Blo 976593 980055 := bstep (se 1 (by rfl) ⟨735041, by rfl⟩ : syracuseStep 980055 = 1470083) B1470083
theorem B980075 : Blo 976593 980075 := bstep (se 1 (by rfl) ⟨735056, by rfl⟩ : syracuseStep 980075 = 1470113) B1470113
theorem B980087 : Blo 976593 980087 := bstep (se 1 (by rfl) ⟨735065, by rfl⟩ : syracuseStep 980087 = 1470131) B1470131
theorem B980107 : Blo 976593 980107 := bstep (se 1 (by rfl) ⟨735080, by rfl⟩ : syracuseStep 980107 = 1470161) B1470161
theorem B980119 : Blo 976593 980119 := bstep (se 1 (by rfl) ⟨735089, by rfl⟩ : syracuseStep 980119 = 1470179) B1470179
theorem B980139 : Blo 976593 980139 := bstep (se 1 (by rfl) ⟨735104, by rfl⟩ : syracuseStep 980139 = 1470209) B1470209
theorem B51573941 : Blo 976593 51573941 := bstep (se 5 (by rfl) ⟨2417528, by rfl⟩ : syracuseStep 51573941 = 4835057) B4835057
theorem B980151 : Blo 976593 980151 := bstep (se 1 (by rfl) ⟨735113, by rfl⟩ : syracuseStep 980151 = 1470227) B1470227
theorem B3306689 : Blo 976593 3306689 := bstep (se 2 (by rfl) ⟨1240008, by rfl⟩ : syracuseStep 3306689 = 2480017) B2480017
theorem B980171 : Blo 976593 980171 := bstep (se 1 (by rfl) ⟨735128, by rfl⟩ : syracuseStep 980171 = 1470257) B1470257
theorem B980183 : Blo 976593 980183 := bstep (se 1 (by rfl) ⟨735137, by rfl⟩ : syracuseStep 980183 = 1470275) B1470275
theorem B980203 : Blo 976593 980203 := bstep (se 1 (by rfl) ⟨735152, by rfl⟩ : syracuseStep 980203 = 1470305) B1470305
theorem B980215 : Blo 976593 980215 := bstep (se 1 (by rfl) ⟨735161, by rfl⟩ : syracuseStep 980215 = 1470323) B1470323
theorem B980235 : Blo 976593 980235 := bstep (se 1 (by rfl) ⟨735176, by rfl⟩ : syracuseStep 980235 = 1470353) B1470353
theorem B980247 : Blo 976593 980247 := bstep (se 1 (by rfl) ⟨735185, by rfl⟩ : syracuseStep 980247 = 1470371) B1470371
theorem B980267 : Blo 976593 980267 := bstep (se 1 (by rfl) ⟨735200, by rfl⟩ : syracuseStep 980267 = 1470401) B1470401
theorem B980279 : Blo 976593 980279 := bstep (se 1 (by rfl) ⟨735209, by rfl⟩ : syracuseStep 980279 = 1470419) B1470419
theorem B980299 : Blo 976593 980299 := bstep (se 1 (by rfl) ⟨735224, by rfl⟩ : syracuseStep 980299 = 1470449) B1470449
theorem B980311 : Blo 976593 980311 := bstep (se 1 (by rfl) ⟨735233, by rfl⟩ : syracuseStep 980311 = 1470467) B1470467
theorem B980331 : Blo 976593 980331 := bstep (se 1 (by rfl) ⟨735248, by rfl⟩ : syracuseStep 980331 = 1470497) B1470497
theorem B980343 : Blo 976593 980343 := bstep (se 1 (by rfl) ⟨735257, by rfl⟩ : syracuseStep 980343 = 1470515) B1470515
theorem B980363 : Blo 976593 980363 := bstep (se 1 (by rfl) ⟨735272, by rfl⟩ : syracuseStep 980363 = 1470545) B1470545
theorem B980375 : Blo 976593 980375 := bstep (se 1 (by rfl) ⟨735281, by rfl⟩ : syracuseStep 980375 = 1470563) B1470563
theorem B980395 : Blo 976593 980395 := bstep (se 1 (by rfl) ⟨735296, by rfl⟩ : syracuseStep 980395 = 1470593) B1470593
theorem B980407 : Blo 976593 980407 := bstep (se 1 (by rfl) ⟨735305, by rfl⟩ : syracuseStep 980407 = 1470611) B1470611
theorem B1045963 : Blo 976593 1045963 := bstep (se 1 (by rfl) ⟨784472, by rfl⟩ : syracuseStep 1045963 = 1568945) B1568945
theorem B980427 : Blo 976593 980427 := bstep (se 1 (by rfl) ⟨735320, by rfl⟩ : syracuseStep 980427 = 1470641) B1470641
theorem B980439 : Blo 976593 980439 := bstep (se 1 (by rfl) ⟨735329, by rfl⟩ : syracuseStep 980439 = 1470659) B1470659
theorem B980459 : Blo 976593 980459 := bstep (se 1 (by rfl) ⟨735344, by rfl⟩ : syracuseStep 980459 = 1470689) B1470689
theorem B980471 : Blo 976593 980471 := bstep (se 1 (by rfl) ⟨735353, by rfl⟩ : syracuseStep 980471 = 1470707) B1470707
theorem B980491 : Blo 976593 980491 := bstep (se 1 (by rfl) ⟨735368, by rfl⟩ : syracuseStep 980491 = 1470737) B1470737
theorem B980503 : Blo 976593 980503 := bstep (se 1 (by rfl) ⟨735377, by rfl⟩ : syracuseStep 980503 = 1470755) B1470755
theorem B980523 : Blo 976593 980523 := bstep (se 1 (by rfl) ⟨735392, by rfl⟩ : syracuseStep 980523 = 1470785) B1470785
theorem B980535 : Blo 976593 980535 := bstep (se 1 (by rfl) ⟨735401, by rfl⟩ : syracuseStep 980535 = 1470803) B1470803
theorem B980555 : Blo 976593 980555 := bstep (se 1 (by rfl) ⟨735416, by rfl⟩ : syracuseStep 980555 = 1470833) B1470833
theorem B980567 : Blo 976593 980567 := bstep (se 1 (by rfl) ⟨735425, by rfl⟩ : syracuseStep 980567 = 1470851) B1470851
theorem B980587 : Blo 976593 980587 := bstep (se 1 (by rfl) ⟨735440, by rfl⟩ : syracuseStep 980587 = 1470881) B1470881
theorem B3307229 : Blo 976593 3307229 := bstep (se 3 (by rfl) ⟨620105, by rfl⟩ : syracuseStep 3307229 = 1240211) B1240211
theorem B1570585 : Blo 976593 1570585 := bstep (se 2 (by rfl) ⟨588969, by rfl⟩ : syracuseStep 1570585 = 1177939) B1177939
theorem B3766105 : Blo 976593 3766105 := bstep (se 2 (by rfl) ⟨1412289, by rfl⟩ : syracuseStep 3766105 = 2824579) B2824579
theorem B60225605 : Blo 976593 60225605 := bstep (se 4 (by rfl) ⟨5646150, by rfl⟩ : syracuseStep 60225605 = 11292301) B11292301
theorem B1177751 : Blo 976593 1177751 := bstep (se 1 (by rfl) ⟨883313, by rfl⟩ : syracuseStep 1177751 = 1766627) B1766627
theorem B2291915 : Blo 976593 2291915 := bstep (se 1 (by rfl) ⟨1718936, by rfl⟩ : syracuseStep 2291915 = 3437873) B3437873
theorem B2259479 : Blo 976593 2259479 := bstep (se 1 (by rfl) ⟨1694609, by rfl⟩ : syracuseStep 2259479 = 3389219) B3389219
theorem B2783767 : Blo 976593 2783767 := bstep (se 1 (by rfl) ⟨2087825, by rfl⟩ : syracuseStep 2783767 = 4175651) B4175651
theorem B4946507 : Blo 976593 4946507 := bstep (se 1 (by rfl) ⟨3709880, by rfl⟩ : syracuseStep 4946507 = 7419761) B7419761
theorem B3767057 : Blo 976593 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B3308363 : Blo 976593 3308363 := bstep (se 1 (by rfl) ⟨2481272, by rfl⟩ : syracuseStep 3308363 = 4962545) B4962545
theorem B1145707 : Blo 976593 1145707 := bstep (se 1 (by rfl) ⟨859280, by rfl⟩ : syracuseStep 1145707 = 1718561) B1718561
theorem B10026019 : Blo 976593 10026019 := bstep (se 1 (by rfl) ⟨7519514, by rfl⟩ : syracuseStep 10026019 = 15039029) B15039029
theorem B7928867 : Blo 976593 7928867 := bstep (se 1 (by rfl) ⟨5946650, by rfl⟩ : syracuseStep 7928867 = 11893301) B11893301
theorem B3308633 : Blo 976593 3308633 := bstep (se 2 (by rfl) ⟨1240737, by rfl⟩ : syracuseStep 3308633 = 2481475) B2481475
theorem B2981015 : Blo 976593 2981015 := bstep (se 1 (by rfl) ⟨2235761, by rfl⟩ : syracuseStep 2981015 = 4471523) B4471523
theorem B9043379 : Blo 976593 9043379 := bstep (se 1 (by rfl) ⟨6782534, by rfl⟩ : syracuseStep 9043379 = 13565069) B13565069
theorem B7044569 : Blo 976593 7044569 := bstep (se 2 (by rfl) ⟨2641713, by rfl⟩ : syracuseStep 7044569 = 5283427) B5283427
theorem B14286577 : Blo 976593 14286577 := bstep (se 2 (by rfl) ⟨5357466, by rfl⟩ : syracuseStep 14286577 = 10714933) B10714933
theorem B3309335 : Blo 976593 3309335 := bstep (se 1 (by rfl) ⟨2482001, by rfl⟩ : syracuseStep 3309335 = 4964003) B4964003
theorem B2785099 : Blo 976593 2785099 := bstep (se 1 (by rfl) ⟨2088824, by rfl⟩ : syracuseStep 2785099 = 4177649) B4177649
theorem B3768257 : Blo 976593 3768257 := bstep (se 2 (by rfl) ⟨1413096, by rfl⟩ : syracuseStep 3768257 = 2826193) B2826193
theorem B4292675 : Blo 976593 4292675 := bstep (se 1 (by rfl) ⟨3219506, by rfl⟩ : syracuseStep 4292675 = 6439013) B6439013
theorem B11894957 : Blo 976593 11894957 := bstep (se 3 (by rfl) ⟨2230304, by rfl⟩ : syracuseStep 11894957 = 4460609) B4460609
theorem B3965165 : Blo 976593 3965165 := bstep (se 3 (by rfl) ⟨743468, by rfl⟩ : syracuseStep 3965165 = 1486937) B1486937
theorem B6259913 : Blo 976593 6259913 := bstep (se 2 (by rfl) ⟨2347467, by rfl⟩ : syracuseStep 6259913 = 4694935) B4694935
theorem B5571929 : Blo 976593 5571929 := bstep (se 2 (by rfl) ⟨2089473, by rfl⟩ : syracuseStep 5571929 = 4178947) B4178947
theorem B7931395 : Blo 976593 7931395 := bstep (se 1 (by rfl) ⟨5948546, by rfl⟩ : syracuseStep 7931395 = 11897093) B11897093
theorem B2786831 : Blo 976593 2786831 := bstep (se 1 (by rfl) ⟨2090123, by rfl⟩ : syracuseStep 2786831 = 4180247) B4180247
theorem B42239717 : Blo 976593 42239717 := bstep (se 4 (by rfl) ⟨3959973, by rfl⟩ : syracuseStep 42239717 = 7919947) B7919947
theorem B6686479 : Blo 976593 6686479 := bstep (se 1 (by rfl) ⟨5014859, by rfl⟩ : syracuseStep 6686479 = 10029719) B10029719
theorem B5572385 : Blo 976593 5572385 := bstep (se 2 (by rfl) ⟨2089644, by rfl⟩ : syracuseStep 5572385 = 4179289) B4179289
theorem B2197367 : Blo 976593 2197367 := bstep (se 1 (by rfl) ⟨1648025, by rfl⟩ : syracuseStep 2197367 = 3296051) B3296051
theorem B1116175 : Blo 976593 1116175 := bstep (se 1 (by rfl) ⟨837131, by rfl⟩ : syracuseStep 1116175 = 1674263) B1674263
theorem B5572637 : Blo 976593 5572637 := bstep (se 3 (by rfl) ⟨1044869, by rfl⟩ : syracuseStep 5572637 = 2089739) B2089739
theorem B2197547 : Blo 976593 2197547 := bstep (se 1 (by rfl) ⟨1648160, by rfl⟩ : syracuseStep 2197547 = 3296321) B3296321
theorem B1411387 : Blo 976593 1411387 := bstep (se 1 (by rfl) ⟨1058540, by rfl⟩ : syracuseStep 1411387 = 2117081) B2117081
theorem B2197907 : Blo 976593 2197907 := bstep (se 1 (by rfl) ⟨1648430, by rfl⟩ : syracuseStep 2197907 = 3296861) B3296861
theorem B2197961 : Blo 976593 2197961 := bstep (se 2 (by rfl) ⟨824235, by rfl⟩ : syracuseStep 2197961 = 1648471) B1648471
theorem B4950557 : Blo 976593 4950557 := bstep (se 3 (by rfl) ⟨928229, by rfl⟩ : syracuseStep 4950557 = 1856459) B1856459
theorem B17828417 : Blo 976593 17828417 := bstep (se 2 (by rfl) ⟨6685656, by rfl⟩ : syracuseStep 17828417 = 13371313) B13371313
theorem B2787959 : Blo 976593 2787959 := bstep (se 1 (by rfl) ⟨2090969, by rfl⟩ : syracuseStep 2787959 = 4181939) B4181939
theorem B3770999 : Blo 976593 3770999 := bstep (se 1 (by rfl) ⟨2828249, by rfl⟩ : syracuseStep 3770999 = 5656499) B5656499
theorem B48204485 : Blo 976593 48204485 := bstep (se 4 (by rfl) ⟨4519170, by rfl⟩ : syracuseStep 48204485 = 9038341) B9038341
theorem B3017515 : Blo 976593 3017515 := bstep (se 1 (by rfl) ⟨2263136, by rfl⟩ : syracuseStep 3017515 = 4526273) B4526273
theorem B4951043 : Blo 976593 4951043 := bstep (se 1 (by rfl) ⟨3713282, by rfl⟩ : syracuseStep 4951043 = 7426565) B7426565
theorem B2198663 : Blo 976593 2198663 := bstep (se 1 (by rfl) ⟨1648997, by rfl⟩ : syracuseStep 2198663 = 3297995) B3297995
theorem B2198843 : Blo 976593 2198843 := bstep (se 1 (by rfl) ⟨1649132, by rfl⟩ : syracuseStep 2198843 = 3298265) B3298265
theorem B2198969 : Blo 976593 2198969 := bstep (se 2 (by rfl) ⟨824613, by rfl⟩ : syracuseStep 2198969 = 1649227) B1649227
theorem B5017099 : Blo 976593 5017099 := bstep (se 1 (by rfl) ⟨3762824, by rfl⟩ : syracuseStep 5017099 = 7525649) B7525649
theorem B2199311 : Blo 976593 2199311 := bstep (se 1 (by rfl) ⟨1649483, by rfl⟩ : syracuseStep 2199311 = 3298967) B3298967
theorem B2199329 : Blo 976593 2199329 := bstep (se 2 (by rfl) ⟨824748, by rfl⟩ : syracuseStep 2199329 = 1649497) B1649497
theorem B2199671 : Blo 976593 2199671 := bstep (se 1 (by rfl) ⟨1649753, by rfl⟩ : syracuseStep 2199671 = 3299507) B3299507
theorem B2789633 : Blo 976593 2789633 := bstep (se 2 (by rfl) ⟨1046112, by rfl⟩ : syracuseStep 2789633 = 2092225) B2092225
theorem B2199851 : Blo 976593 2199851 := bstep (se 1 (by rfl) ⟨1649888, by rfl⟩ : syracuseStep 2199851 = 3299777) B3299777
theorem B5575027 : Blo 976593 5575027 := bstep (se 1 (by rfl) ⟨4181270, by rfl⟩ : syracuseStep 5575027 = 8362541) B8362541
theorem B2789747 : Blo 976593 2789747 := bstep (se 1 (by rfl) ⟨2092310, by rfl⟩ : syracuseStep 2789747 = 4184621) B4184621
theorem B4952663 : Blo 976593 4952663 := bstep (se 1 (by rfl) ⟨3714497, by rfl⟩ : syracuseStep 4952663 = 7428995) B7428995
theorem B2200211 : Blo 976593 2200211 := bstep (se 1 (by rfl) ⟨1650158, by rfl⟩ : syracuseStep 2200211 = 3300317) B3300317
theorem B2200265 : Blo 976593 2200265 := bstep (se 2 (by rfl) ⟨825099, by rfl⟩ : syracuseStep 2200265 = 1650199) B1650199
theorem B2790089 : Blo 976593 2790089 := bstep (se 2 (by rfl) ⟨1046283, by rfl⟩ : syracuseStep 2790089 = 2092567) B2092567
theorem B6263705 : Blo 976593 6263705 := bstep (se 2 (by rfl) ⟨2348889, by rfl⟩ : syracuseStep 6263705 = 4697779) B4697779
theorem B4953149 : Blo 976593 4953149 := bstep (se 3 (by rfl) ⟨928715, by rfl⟩ : syracuseStep 4953149 = 1857431) B1857431
theorem B8459437 : Blo 976593 8459437 := bstep (se 3 (by rfl) ⟨1586144, by rfl⟩ : syracuseStep 8459437 = 3172289) B3172289
theorem B2200967 : Blo 976593 2200967 := bstep (se 1 (by rfl) ⟨1650725, by rfl⟩ : syracuseStep 2200967 = 3301451) B3301451
theorem B10032589 : Blo 976593 10032589 := bstep (se 3 (by rfl) ⟨1881110, by rfl⟩ : syracuseStep 10032589 = 3762221) B3762221
theorem B2201147 : Blo 976593 2201147 := bstep (se 1 (by rfl) ⟨1650860, by rfl⟩ : syracuseStep 2201147 = 3301721) B3301721
theorem B4462141 : Blo 976593 4462141 := bstep (se 3 (by rfl) ⟨836651, by rfl⟩ : syracuseStep 4462141 = 1673303) B1673303
theorem B2201273 : Blo 976593 2201273 := bstep (se 2 (by rfl) ⟨825477, by rfl⟩ : syracuseStep 2201273 = 1650955) B1650955
theorem B5576485 : Blo 976593 5576485 := bstep (se 4 (by rfl) ⟨522795, by rfl⟩ : syracuseStep 5576485 = 1045591) B1045591
theorem B3708787 : Blo 976593 3708787 := bstep (se 1 (by rfl) ⟨2781590, by rfl⟩ : syracuseStep 3708787 = 5563181) B5563181
theorem B2201615 : Blo 976593 2201615 := bstep (se 1 (by rfl) ⟨1651211, by rfl⟩ : syracuseStep 2201615 = 3302423) B3302423
theorem B2201633 : Blo 976593 2201633 := bstep (se 2 (by rfl) ⟨825612, by rfl⟩ : syracuseStep 2201633 = 1651225) B1651225
theorem B4757705 : Blo 976593 4757705 := bstep (se 2 (by rfl) ⟨1784139, by rfl⟩ : syracuseStep 4757705 = 3568279) B3568279
theorem B5577011 : Blo 976593 5577011 := bstep (se 1 (by rfl) ⟨4182758, by rfl⟩ : syracuseStep 5577011 = 8365517) B8365517
theorem B2201975 : Blo 976593 2201975 := bstep (se 1 (by rfl) ⟨1651481, by rfl⟩ : syracuseStep 2201975 = 3302963) B3302963
theorem B7936555 : Blo 976593 7936555 := bstep (se 1 (by rfl) ⟨5952416, by rfl⟩ : syracuseStep 7936555 = 11904833) B11904833
theorem B2202155 : Blo 976593 2202155 := bstep (se 1 (by rfl) ⟨1651616, by rfl⟩ : syracuseStep 2202155 = 3303233) B3303233
theorem B2791979 : Blo 976593 2791979 := bstep (se 1 (by rfl) ⟨2093984, by rfl⟩ : syracuseStep 2791979 = 4187969) B4187969
theorem B2792207 : Blo 976593 2792207 := bstep (se 1 (by rfl) ⟨2094155, by rfl⟩ : syracuseStep 2792207 = 4188311) B4188311
theorem B4954931 : Blo 976593 4954931 := bstep (se 1 (by rfl) ⟨3716198, by rfl⟩ : syracuseStep 4954931 = 7432397) B7432397
theorem B3578759 : Blo 976593 3578759 := bstep (se 1 (by rfl) ⟨2684069, by rfl⟩ : syracuseStep 3578759 = 5368139) B5368139
theorem B2202515 : Blo 976593 2202515 := bstep (se 1 (by rfl) ⟨1651886, by rfl⟩ : syracuseStep 2202515 = 3303773) B3303773
theorem B2202569 : Blo 976593 2202569 := bstep (se 2 (by rfl) ⟨825963, by rfl⟩ : syracuseStep 2202569 = 1651927) B1651927
theorem B2235451 : Blo 976593 2235451 := bstep (se 1 (by rfl) ⟨1676588, by rfl⟩ : syracuseStep 2235451 = 3353177) B3353177
theorem B4955255 : Blo 976593 4955255 := bstep (se 1 (by rfl) ⟨3716441, by rfl⟩ : syracuseStep 4955255 = 7432883) B7432883
theorem B80321813 : Blo 976593 80321813 := bstep (se 6 (by rfl) ⟨1882542, by rfl⟩ : syracuseStep 80321813 = 3765085) B3765085
theorem B111779131 : Blo 976593 111779131 := bstep (se 1 (by rfl) ⟨83834348, by rfl⟩ : syracuseStep 111779131 = 167668697) B167668697
theorem B2203271 : Blo 976593 2203271 := bstep (se 1 (by rfl) ⟨1652453, by rfl⟩ : syracuseStep 2203271 = 3304907) B3304907
theorem B5578469 : Blo 976593 5578469 := bstep (se 4 (by rfl) ⟨522981, by rfl⟩ : syracuseStep 5578469 = 1045963) B1045963
theorem B5021473 : Blo 976593 5021473 := bstep (se 2 (by rfl) ⟨1883052, by rfl⟩ : syracuseStep 5021473 = 3766105) B3766105
theorem B2203451 : Blo 976593 2203451 := bstep (se 1 (by rfl) ⟨1652588, by rfl⟩ : syracuseStep 2203451 = 3305177) B3305177
theorem B2203577 : Blo 976593 2203577 := bstep (se 2 (by rfl) ⟨826341, by rfl⟩ : syracuseStep 2203577 = 1652683) B1652683
theorem B9543703 : Blo 976593 9543703 := bstep (se 1 (by rfl) ⟨7157777, by rfl⟩ : syracuseStep 9543703 = 14315555) B14315555
theorem B3711005 : Blo 976593 3711005 := bstep (se 3 (by rfl) ⟨695813, by rfl⟩ : syracuseStep 3711005 = 1391627) B1391627
theorem B4956227 : Blo 976593 4956227 := bstep (se 1 (by rfl) ⟨3717170, by rfl⟩ : syracuseStep 4956227 = 7434341) B7434341
theorem B2203919 : Blo 976593 2203919 := bstep (se 1 (by rfl) ⟨1652939, by rfl⟩ : syracuseStep 2203919 = 3305879) B3305879
theorem B2203937 : Blo 976593 2203937 := bstep (se 2 (by rfl) ⟨826476, by rfl⟩ : syracuseStep 2203937 = 1652953) B1652953
theorem B1253675 : Blo 976593 1253675 := bstep (se 1 (by rfl) ⟨940256, by rfl⟩ : syracuseStep 1253675 = 1880513) B1880513
theorem B4956551 : Blo 976593 4956551 := bstep (se 1 (by rfl) ⟨3717413, by rfl⟩ : syracuseStep 4956551 = 7434827) B7434827
theorem B6267395 : Blo 976593 6267395 := bstep (se 1 (by rfl) ⟨4700546, by rfl⟩ : syracuseStep 6267395 = 9401093) B9401093
theorem B2204279 : Blo 976593 2204279 := bstep (se 1 (by rfl) ⟨1653209, by rfl⟩ : syracuseStep 2204279 = 3306419) B3306419
theorem B3711689 : Blo 976593 3711689 := bstep (se 2 (by rfl) ⟨1391883, by rfl⟩ : syracuseStep 3711689 = 2783767) B2783767
theorem B34382627 : Blo 976593 34382627 := bstep (se 1 (by rfl) ⟨25786970, by rfl⟩ : syracuseStep 34382627 = 51573941) B51573941
theorem B2204459 : Blo 976593 2204459 := bstep (se 1 (by rfl) ⟨1653344, by rfl⟩ : syracuseStep 2204459 = 3306689) B3306689
theorem B992135 : Blo 976593 992135 := bstep (se 1 (by rfl) ⟨744101, by rfl⟩ : syracuseStep 992135 = 1488203) B1488203
theorem B3351563 : Blo 976593 3351563 := bstep (se 1 (by rfl) ⟨2513672, by rfl⟩ : syracuseStep 3351563 = 5027345) B5027345
theorem B7054397 : Blo 976593 7054397 := bstep (se 3 (by rfl) ⟨1322699, by rfl⟩ : syracuseStep 7054397 = 2645399) B2645399
theorem B1320079 : Blo 976593 1320079 := bstep (se 1 (by rfl) ⟨990059, by rfl⟩ : syracuseStep 1320079 = 1980119) B1980119
theorem B2204819 : Blo 976593 2204819 := bstep (se 1 (by rfl) ⟨1653614, by rfl⟩ : syracuseStep 2204819 = 3307229) B3307229
theorem B2204873 : Blo 976593 2204873 := bstep (se 2 (by rfl) ⟨826827, by rfl⟩ : syracuseStep 2204873 = 1653655) B1653655
theorem B40150403 : Blo 976593 40150403 := bstep (se 1 (by rfl) ⟨30112802, by rfl⟩ : syracuseStep 40150403 = 60225605) B60225605
theorem B2827673 : Blo 976593 2827673 := bstep (se 2 (by rfl) ⟨1060377, by rfl⟩ : syracuseStep 2827673 = 2120755) B2120755
theorem B1648073 : Blo 976593 1648073 := bstep (se 2 (by rfl) ⟨618027, by rfl⟩ : syracuseStep 1648073 = 1236055) B1236055
theorem B2205575 : Blo 976593 2205575 := bstep (se 1 (by rfl) ⟨1654181, by rfl⟩ : syracuseStep 2205575 = 3308363) B3308363
theorem B5285911 : Blo 976593 5285911 := bstep (se 1 (by rfl) ⟨3964433, by rfl⟩ : syracuseStep 5285911 = 7928867) B7928867
theorem B2828317 : Blo 976593 2828317 := bstep (se 3 (by rfl) ⟨530309, by rfl⟩ : syracuseStep 2828317 = 1060619) B1060619
theorem B2205755 : Blo 976593 2205755 := bstep (se 1 (by rfl) ⟨1654316, by rfl⟩ : syracuseStep 2205755 = 3308633) B3308633
theorem B1648775 : Blo 976593 1648775 := bstep (se 1 (by rfl) ⟨1236581, by rfl⟩ : syracuseStep 1648775 = 2473163) B2473163
theorem B2205881 : Blo 976593 2205881 := bstep (se 2 (by rfl) ⟨827205, by rfl⟩ : syracuseStep 2205881 = 1654411) B1654411
theorem B1321273 : Blo 976593 1321273 := bstep (se 2 (by rfl) ⟨495477, by rfl⟩ : syracuseStep 1321273 = 990955) B990955
theorem B4696379 : Blo 976593 4696379 := bstep (se 1 (by rfl) ⟨3522284, by rfl⟩ : syracuseStep 4696379 = 7044569) B7044569
theorem B19048769 : Blo 976593 19048769 := bstep (se 2 (by rfl) ⟨7143288, by rfl⟩ : syracuseStep 19048769 = 14286577) B14286577
theorem B3713465 : Blo 976593 3713465 := bstep (se 2 (by rfl) ⟨1392549, by rfl⟩ : syracuseStep 3713465 = 2785099) B2785099
theorem B1255943 : Blo 976593 1255943 := bstep (se 1 (by rfl) ⟨941957, by rfl⟩ : syracuseStep 1255943 = 1883915) B1883915
theorem B2206223 : Blo 976593 2206223 := bstep (se 1 (by rfl) ⟨1654667, by rfl⟩ : syracuseStep 2206223 = 3309335) B3309335
theorem B2206241 : Blo 976593 2206241 := bstep (se 2 (by rfl) ⟨827340, by rfl⟩ : syracuseStep 2206241 = 1654681) B1654681
theorem B1190543 : Blo 976593 1190543 := bstep (se 1 (by rfl) ⟨892907, by rfl⟩ : syracuseStep 1190543 = 1785815) B1785815
theorem B23538437 : Blo 976593 23538437 := bstep (se 4 (by rfl) ⟨2206728, by rfl⟩ : syracuseStep 23538437 = 4413457) B4413457
theorem B1649423 : Blo 976593 1649423 := bstep (se 1 (by rfl) ⟨1237067, by rfl⟩ : syracuseStep 1649423 = 2474135) B2474135
theorem B14101411 : Blo 976593 14101411 := bstep (se 1 (by rfl) ⟨10576058, by rfl⟩ : syracuseStep 14101411 = 21152117) B21152117
theorem B5647313 : Blo 976593 5647313 := bstep (se 2 (by rfl) ⟨2117742, by rfl⟩ : syracuseStep 5647313 = 4235485) B4235485
theorem B9415703 : Blo 976593 9415703 := bstep (se 1 (by rfl) ⟨7061777, by rfl⟩ : syracuseStep 9415703 = 14123555) B14123555
theorem B16067645 : Blo 976593 16067645 := bstep (se 3 (by rfl) ⟨3012683, by rfl⟩ : syracuseStep 16067645 = 6025367) B6025367
theorem B1649963 : Blo 976593 1649963 := bstep (se 1 (by rfl) ⟨1237472, by rfl⟩ : syracuseStep 1649963 = 2474945) B2474945
theorem B4173191 : Blo 976593 4173191 := bstep (se 1 (by rfl) ⟨3129893, by rfl⟩ : syracuseStep 4173191 = 6259787) B6259787
theorem B4173241 : Blo 976593 4173241 := bstep (se 2 (by rfl) ⟨1564965, by rfl⟩ : syracuseStep 4173241 = 3129931) B3129931
theorem B1650361 : Blo 976593 1650361 := bstep (se 2 (by rfl) ⟨618885, by rfl⟩ : syracuseStep 1650361 = 1237771) B1237771
theorem B15249221 : Blo 976593 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B4960115 : Blo 976593 4960115 := bstep (se 1 (by rfl) ⟨3720086, by rfl⟩ : syracuseStep 4960115 = 7440173) B7440173
theorem B1487035 : Blo 976593 1487035 := bstep (se 1 (by rfl) ⟨1115276, by rfl⟩ : syracuseStep 1487035 = 2230553) B2230553
theorem B4960601 : Blo 976593 4960601 := bstep (se 2 (by rfl) ⟨1860225, by rfl⟩ : syracuseStep 4960601 = 3720451) B3720451
theorem B1651063 : Blo 976593 1651063 := bstep (se 1 (by rfl) ⟨1238297, by rfl⟩ : syracuseStep 1651063 = 2476595) B2476595
theorem B1651259 : Blo 976593 1651259 := bstep (se 1 (by rfl) ⟨1238444, by rfl⟩ : syracuseStep 1651259 = 2476889) B2476889
theorem B4174573 : Blo 976593 4174573 := bstep (se 3 (by rfl) ⟨782732, by rfl⟩ : syracuseStep 4174573 = 1565465) B1565465
theorem B1323911 : Blo 976593 1323911 := bstep (se 1 (by rfl) ⟨992933, by rfl⟩ : syracuseStep 1323911 = 1985867) B1985867
theorem B1651657 : Blo 976593 1651657 := bstep (se 2 (by rfl) ⟨619371, by rfl⟩ : syracuseStep 1651657 = 1238743) B1238743
theorem B5649431 : Blo 976593 5649431 := bstep (se 1 (by rfl) ⟨4237073, by rfl⟩ : syracuseStep 5649431 = 8474147) B8474147
theorem B4174915 : Blo 976593 4174915 := bstep (se 1 (by rfl) ⟨3131186, by rfl⟩ : syracuseStep 4174915 = 6262373) B6262373
theorem B4469879 : Blo 976593 4469879 := bstep (se 1 (by rfl) ⟨3352409, by rfl⟩ : syracuseStep 4469879 = 6704819) B6704819
theorem B4470169 : Blo 976593 4470169 := bstep (se 2 (by rfl) ⟨1676313, by rfl⟩ : syracuseStep 4470169 = 3352627) B3352627
theorem B36156851 : Blo 976593 36156851 := bstep (se 1 (by rfl) ⟨27117638, by rfl⟩ : syracuseStep 36156851 = 54235277) B54235277
theorem B1324603 : Blo 976593 1324603 := bstep (se 1 (by rfl) ⟨993452, by rfl⟩ : syracuseStep 1324603 = 1986905) B1986905
theorem B1652359 : Blo 976593 1652359 := bstep (se 1 (by rfl) ⟨1239269, by rfl⟩ : syracuseStep 1652359 = 2478539) B2478539
theorem B5289761 : Blo 976593 5289761 := bstep (se 2 (by rfl) ⟨1983660, by rfl⟩ : syracuseStep 5289761 = 3967321) B3967321
theorem B3717049 : Blo 976593 3717049 := bstep (se 2 (by rfl) ⟨1393893, by rfl⟩ : syracuseStep 3717049 = 2787787) B2787787
theorem B6273035 : Blo 976593 6273035 := bstep (se 1 (by rfl) ⟨4704776, by rfl⟩ : syracuseStep 6273035 = 9409553) B9409553
theorem B1390727 : Blo 976593 1390727 := bstep (se 1 (by rfl) ⟨1043045, by rfl⟩ : syracuseStep 1390727 = 2086091) B2086091
theorem B1653007 : Blo 976593 1653007 := bstep (se 1 (by rfl) ⟨1239755, by rfl⟩ : syracuseStep 1653007 = 2479511) B2479511
theorem B4700531 : Blo 976593 4700531 := bstep (se 1 (by rfl) ⟨3525398, by rfl⟩ : syracuseStep 4700531 = 7050797) B7050797
theorem B4962707 : Blo 976593 4962707 := bstep (se 1 (by rfl) ⟨3722030, by rfl⟩ : syracuseStep 4962707 = 7444061) B7444061
theorem B1391035 : Blo 976593 1391035 := bstep (se 1 (by rfl) ⟨1043276, by rfl⟩ : syracuseStep 1391035 = 2086553) B2086553
theorem B4700683 : Blo 976593 4700683 := bstep (se 1 (by rfl) ⟨3525512, by rfl⟩ : syracuseStep 4700683 = 7051025) B7051025
theorem B1653547 : Blo 976593 1653547 := bstep (se 1 (by rfl) ⟨1240160, by rfl⟩ : syracuseStep 1653547 = 2480321) B2480321
theorem B25115507 : Blo 976593 25115507 := bstep (se 1 (by rfl) ⟨18836630, by rfl⟩ : syracuseStep 25115507 = 37673261) B37673261
theorem B2472839 : Blo 976593 2472839 := bstep (se 1 (by rfl) ⟨1854629, by rfl⟩ : syracuseStep 2472839 = 3709259) B3709259
theorem B2472889 : Blo 976593 2472889 := bstep (se 2 (by rfl) ⟨927333, by rfl⟩ : syracuseStep 2472889 = 1854667) B1854667
theorem B1653689 : Blo 976593 1653689 := bstep (se 2 (by rfl) ⟨620133, by rfl⟩ : syracuseStep 1653689 = 1240267) B1240267
theorem B1883081 : Blo 976593 1883081 := bstep (se 2 (by rfl) ⟨706155, by rfl⟩ : syracuseStep 1883081 = 1412311) B1412311
theorem B2014409 : Blo 976593 2014409 := bstep (se 2 (by rfl) ⟨755403, by rfl⟩ : syracuseStep 2014409 = 1510807) B1510807
theorem B6110437 : Blo 976593 6110437 := bstep (se 4 (by rfl) ⟨572853, by rfl⟩ : syracuseStep 6110437 = 1145707) B1145707
theorem B4472065 : Blo 976593 4472065 := bstep (se 2 (by rfl) ⟨1677024, by rfl⟩ : syracuseStep 4472065 = 3354049) B3354049
theorem B2473487 : Blo 976593 2473487 := bstep (se 1 (by rfl) ⟨1855115, by rfl⟩ : syracuseStep 2473487 = 3710231) B3710231
theorem B1392185 : Blo 976593 1392185 := bstep (se 2 (by rfl) ⟨522069, by rfl⟩ : syracuseStep 1392185 = 1044139) B1044139
theorem B10567235 : Blo 976593 10567235 := bstep (se 1 (by rfl) ⟨7925426, by rfl⟩ : syracuseStep 10567235 = 15850853) B15850853
theorem B1654391 : Blo 976593 1654391 := bstep (se 1 (by rfl) ⟨1240793, by rfl⟩ : syracuseStep 1654391 = 2481587) B2481587
theorem B2474185 : Blo 976593 2474185 := bstep (se 2 (by rfl) ⟨927819, by rfl⟩ : syracuseStep 2474185 = 1855639) B1855639
theorem B2474327 : Blo 976593 2474327 := bstep (se 1 (by rfl) ⟨1855745, by rfl⟩ : syracuseStep 2474327 = 3711491) B3711491
theorem B6111773 : Blo 976593 6111773 := bstep (se 3 (by rfl) ⟨1145957, by rfl⟩ : syracuseStep 6111773 = 2291915) B2291915
theorem B8372929 : Blo 976593 8372929 := bstep (se 2 (by rfl) ⟨3139848, by rfl⟩ : syracuseStep 8372929 = 6279697) B6279697
theorem B3719951 : Blo 976593 3719951 := bstep (se 1 (by rfl) ⟨2789963, by rfl⟩ : syracuseStep 3719951 = 5579927) B5579927
theorem B3130265 : Blo 976593 3130265 := bstep (se 2 (by rfl) ⟨1173849, by rfl⟩ : syracuseStep 3130265 = 2347699) B2347699
theorem B1983433 : Blo 976593 1983433 := bstep (se 2 (by rfl) ⟨743787, by rfl⟩ : syracuseStep 1983433 = 1487575) B1487575
theorem B1393723 : Blo 976593 1393723 := bstep (se 1 (by rfl) ⟨1045292, by rfl⟩ : syracuseStep 1393723 = 2090585) B2090585
theorem B1098895 : Blo 976593 1098895 := bstep (se 1 (by rfl) ⟨824171, by rfl⟩ : syracuseStep 1098895 = 1648343) B1648343
theorem B11125997 : Blo 976593 11125997 := bstep (se 3 (by rfl) ⟨2086124, by rfl⟩ : syracuseStep 11125997 = 4172249) B4172249
theorem B15058385 : Blo 976593 15058385 := bstep (se 2 (by rfl) ⟨5646894, by rfl⟩ : syracuseStep 15058385 = 11293789) B11293789
theorem B1394167 : Blo 976593 1394167 := bstep (se 1 (by rfl) ⟨1045625, by rfl⟩ : syracuseStep 1394167 = 2091251) B2091251
theorem B1099399 : Blo 976593 1099399 := bstep (se 1 (by rfl) ⟨824549, by rfl⟩ : syracuseStep 1099399 = 1649099) B1649099
theorem B1099579 : Blo 976593 1099579 := bstep (se 1 (by rfl) ⟨824684, by rfl⟩ : syracuseStep 1099579 = 1649369) B1649369
theorem B1100047 : Blo 976593 1100047 := bstep (se 1 (by rfl) ⟨825035, by rfl⟩ : syracuseStep 1100047 = 1650071) B1650071
theorem B1394987 : Blo 976593 1394987 := bstep (se 1 (by rfl) ⟨1046240, by rfl⟩ : syracuseStep 1394987 = 2092481) B2092481
theorem B2476403 : Blo 976593 2476403 := bstep (se 1 (by rfl) ⟨1857302, by rfl⟩ : syracuseStep 2476403 = 3714605) B3714605
theorem B3132161 : Blo 976593 3132161 := bstep (se 2 (by rfl) ⟨1174560, by rfl⟩ : syracuseStep 3132161 = 2349121) B2349121
theorem B1100551 : Blo 976593 1100551 := bstep (se 1 (by rfl) ⟨825413, by rfl⟩ : syracuseStep 1100551 = 1650827) B1650827
theorem B2476919 : Blo 976593 2476919 := bstep (se 1 (by rfl) ⟨1857689, by rfl⟩ : syracuseStep 2476919 = 3715379) B3715379
theorem B1100731 : Blo 976593 1100731 := bstep (se 1 (by rfl) ⟨825548, by rfl⟩ : syracuseStep 1100731 = 1651097) B1651097
theorem B1854409 : Blo 976593 1854409 := bstep (se 2 (by rfl) ⟨695403, by rfl⟩ : syracuseStep 1854409 = 1390807) B1390807
theorem B3296267 : Blo 976593 3296267 := bstep (se 1 (by rfl) ⟨2472200, by rfl⟩ : syracuseStep 3296267 = 4944401) B4944401
theorem B4770839 : Blo 976593 4770839 := bstep (se 1 (by rfl) ⟨3578129, by rfl⟩ : syracuseStep 4770839 = 7156259) B7156259
theorem B3296375 : Blo 976593 3296375 := bstep (se 1 (by rfl) ⟨2472281, by rfl⟩ : syracuseStep 3296375 = 4944563) B4944563
theorem B1985737 : Blo 976593 1985737 := bstep (se 2 (by rfl) ⟨744651, by rfl⟩ : syracuseStep 1985737 = 1489303) B1489303
theorem B7064891 : Blo 976593 7064891 := bstep (se 1 (by rfl) ⟨5298668, by rfl⟩ : syracuseStep 7064891 = 10597337) B10597337
theorem B7949627 : Blo 976593 7949627 := bstep (se 1 (by rfl) ⟨5962220, by rfl⟩ : syracuseStep 7949627 = 11924441) B11924441
theorem B1101199 : Blo 976593 1101199 := bstep (se 1 (by rfl) ⟨825899, by rfl⟩ : syracuseStep 1101199 = 1651799) B1651799
theorem B3296969 : Blo 976593 3296969 := bstep (se 2 (by rfl) ⟨1236363, by rfl⟩ : syracuseStep 3296969 = 2472727) B2472727
theorem B8343269 : Blo 976593 8343269 := bstep (se 4 (by rfl) ⟨782181, by rfl⟩ : syracuseStep 8343269 = 1564363) B1564363
theorem B2477911 : Blo 976593 2477911 := bstep (se 1 (by rfl) ⟨1858433, by rfl⟩ : syracuseStep 2477911 = 3716867) B3716867
theorem B1101703 : Blo 976593 1101703 := bstep (se 1 (by rfl) ⟨826277, by rfl⟩ : syracuseStep 1101703 = 1652555) B1652555
theorem B3723155 : Blo 976593 3723155 := bstep (se 1 (by rfl) ⟨2792366, by rfl⟩ : syracuseStep 3723155 = 5584733) B5584733
theorem B1101883 : Blo 976593 1101883 := bstep (se 1 (by rfl) ⟨826412, by rfl⟩ : syracuseStep 1101883 = 1652825) B1652825
theorem B2478215 : Blo 976593 2478215 := bstep (se 1 (by rfl) ⟨1858661, by rfl⟩ : syracuseStep 2478215 = 3717323) B3717323
theorem B5951717 : Blo 976593 5951717 := bstep (se 4 (by rfl) ⟨557973, by rfl⟩ : syracuseStep 5951717 = 1115947) B1115947
theorem B2478347 : Blo 976593 2478347 := bstep (se 1 (by rfl) ⟨1858760, by rfl⟩ : syracuseStep 2478347 = 3717521) B3717521
theorem B3297671 : Blo 976593 3297671 := bstep (se 1 (by rfl) ⟨2473253, by rfl⟩ : syracuseStep 3297671 = 4946507) B4946507
theorem B2118089 : Blo 976593 2118089 := bstep (se 2 (by rfl) ⟨794283, by rfl⟩ : syracuseStep 2118089 = 1588567) B1588567
theorem B2511371 : Blo 976593 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B1102351 : Blo 976593 1102351 := bstep (se 1 (by rfl) ⟨826763, by rfl⟩ : syracuseStep 1102351 = 1653527) B1653527
theorem B3298049 : Blo 976593 3298049 := bstep (se 2 (by rfl) ⟨1236768, by rfl⟩ : syracuseStep 3298049 = 2473537) B2473537
theorem B2478863 : Blo 976593 2478863 := bstep (se 1 (by rfl) ⟨1859147, by rfl⟩ : syracuseStep 2478863 = 3718295) B3718295
theorem B1987343 : Blo 976593 1987343 := bstep (se 1 (by rfl) ⟨1490507, by rfl⟩ : syracuseStep 1987343 = 2981015) B2981015
theorem B2478995 : Blo 976593 2478995 := bstep (se 1 (by rfl) ⟨1859246, by rfl⟩ : syracuseStep 2478995 = 3718493) B3718493
theorem B1102855 : Blo 976593 1102855 := bstep (se 1 (by rfl) ⟨827141, by rfl⟩ : syracuseStep 1102855 = 1654283) B1654283
theorem B1103035 : Blo 976593 1103035 := bstep (se 1 (by rfl) ⟨827276, by rfl⟩ : syracuseStep 1103035 = 1654553) B1654553
theorem B2512171 : Blo 976593 2512171 := bstep (se 1 (by rfl) ⟨1884128, by rfl⟩ : syracuseStep 2512171 = 3768257) B3768257
theorem B1856915 : Blo 976593 1856915 := bstep (se 1 (by rfl) ⟨1392686, by rfl⟩ : syracuseStep 1856915 = 2785373) B2785373
theorem B7427537 : Blo 976593 7427537 := bstep (se 2 (by rfl) ⟨2785326, by rfl⟩ : syracuseStep 7427537 = 5570653) B5570653
theorem B11130371 : Blo 976593 11130371 := bstep (se 1 (by rfl) ⟨8347778, by rfl⟩ : syracuseStep 11130371 = 16695557) B16695557
theorem B3298859 : Blo 976593 3298859 := bstep (se 1 (by rfl) ⟨2474144, by rfl⟩ : syracuseStep 3298859 = 4948289) B4948289
theorem B3135019 : Blo 976593 3135019 := bstep (se 1 (by rfl) ⟨2351264, by rfl⟩ : syracuseStep 3135019 = 4702529) B4702529
theorem B4183595 : Blo 976593 4183595 := bstep (se 1 (by rfl) ⟨3137696, by rfl⟩ : syracuseStep 4183595 = 6275393) B6275393
theorem B1857143 : Blo 976593 1857143 := bstep (se 1 (by rfl) ⟨1392857, by rfl⟩ : syracuseStep 1857143 = 2785715) B2785715
theorem B2086535 : Blo 976593 2086535 := bstep (se 1 (by rfl) ⟨1564901, by rfl⟩ : syracuseStep 2086535 = 3129803) B3129803
theorem B42981043 : Blo 976593 42981043 := bstep (se 1 (by rfl) ⟨32235782, by rfl⟩ : syracuseStep 42981043 = 64471565) B64471565
theorem B2348833 : Blo 976593 2348833 := bstep (se 2 (by rfl) ⟨880812, by rfl⟩ : syracuseStep 2348833 = 1761625) B1761625
theorem B5297957 : Blo 976593 5297957 := bstep (se 4 (by rfl) ⟨496683, by rfl⟩ : syracuseStep 5297957 = 993367) B993367
theorem B27121483 : Blo 976593 27121483 := bstep (se 1 (by rfl) ⟨20341112, by rfl⟩ : syracuseStep 27121483 = 40682225) B40682225
theorem B2480129 : Blo 976593 2480129 := bstep (se 2 (by rfl) ⟨930048, by rfl⟩ : syracuseStep 2480129 = 1860097) B1860097
theorem B4773917 : Blo 976593 4773917 := bstep (se 3 (by rfl) ⟨895109, by rfl⟩ : syracuseStep 4773917 = 1790219) B1790219
theorem B2513015 : Blo 976593 2513015 := bstep (se 1 (by rfl) ⟨1884761, by rfl⟩ : syracuseStep 2513015 = 3769523) B3769523
theorem B16963829 : Blo 976593 16963829 := bstep (se 5 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 16963829 = 1590359) B1590359
theorem B2480503 : Blo 976593 2480503 := bstep (se 1 (by rfl) ⟨1860377, by rfl⟩ : syracuseStep 2480503 = 3720755) B3720755
theorem B3529277 : Blo 976593 3529277 := bstep (se 3 (by rfl) ⟨661739, by rfl⟩ : syracuseStep 3529277 = 1323479) B1323479
theorem B1464905 : Blo 976593 1464905 := bstep (se 2 (by rfl) ⟨549339, by rfl⟩ : syracuseStep 1464905 = 1098679) B1098679
theorem B1465019 : Blo 976593 1465019 := bstep (se 1 (by rfl) ⟨1098764, by rfl⟩ : syracuseStep 1465019 = 2197529) B2197529
theorem B1465079 : Blo 976593 1465079 := bstep (se 1 (by rfl) ⟨1098809, by rfl⟩ : syracuseStep 1465079 = 2197619) B2197619
theorem B1465103 : Blo 976593 1465103 := bstep (se 1 (by rfl) ⟨1098827, by rfl⟩ : syracuseStep 1465103 = 2197655) B2197655
theorem B2480939 : Blo 976593 2480939 := bstep (se 1 (by rfl) ⟨1860704, by rfl⟩ : syracuseStep 2480939 = 3721409) B3721409
theorem B1465145 : Blo 976593 1465145 := bstep (se 2 (by rfl) ⟨549429, by rfl⟩ : syracuseStep 1465145 = 1098859) B1098859
theorem B3300155 : Blo 976593 3300155 := bstep (se 1 (by rfl) ⟨2475116, by rfl⟩ : syracuseStep 3300155 = 4950233) B4950233
theorem B1465223 : Blo 976593 1465223 := bstep (se 1 (by rfl) ⟨1098917, by rfl⟩ : syracuseStep 1465223 = 2197835) B2197835
theorem B3136391 : Blo 976593 3136391 := bstep (se 1 (by rfl) ⟨2352293, by rfl⟩ : syracuseStep 3136391 = 4704587) B4704587
theorem B1465259 : Blo 976593 1465259 := bstep (se 1 (by rfl) ⟨1098944, by rfl⟩ : syracuseStep 1465259 = 2197889) B2197889
theorem B1465289 : Blo 976593 1465289 := bstep (se 2 (by rfl) ⟨549483, by rfl⟩ : syracuseStep 1465289 = 1098967) B1098967
theorem B1465403 : Blo 976593 1465403 := bstep (se 1 (by rfl) ⟨1099052, by rfl⟩ : syracuseStep 1465403 = 2198105) B2198105
theorem B8346685 : Blo 976593 8346685 := bstep (se 3 (by rfl) ⟨1565003, by rfl⟩ : syracuseStep 8346685 = 3130007) B3130007
theorem B1465463 : Blo 976593 1465463 := bstep (se 1 (by rfl) ⟨1099097, by rfl⟩ : syracuseStep 1465463 = 2198195) B2198195
theorem B1465487 : Blo 976593 1465487 := bstep (se 1 (by rfl) ⟨1099115, by rfl⟩ : syracuseStep 1465487 = 2198231) B2198231
theorem B1465529 : Blo 976593 1465529 := bstep (se 2 (by rfl) ⟨549573, by rfl⟩ : syracuseStep 1465529 = 1099147) B1099147
theorem B1465607 : Blo 976593 1465607 := bstep (se 1 (by rfl) ⟨1099205, by rfl⟩ : syracuseStep 1465607 = 2198411) B2198411
theorem B3300641 : Blo 976593 3300641 := bstep (se 2 (by rfl) ⟨1237740, by rfl⟩ : syracuseStep 3300641 = 2475481) B2475481
theorem B1465643 : Blo 976593 1465643 := bstep (se 1 (by rfl) ⟨1099232, by rfl⟩ : syracuseStep 1465643 = 2198465) B2198465
theorem B1858859 : Blo 976593 1858859 := bstep (se 1 (by rfl) ⟨1394144, by rfl⟩ : syracuseStep 1858859 = 2788289) B2788289
theorem B1465673 : Blo 976593 1465673 := bstep (se 2 (by rfl) ⟨549627, by rfl⟩ : syracuseStep 1465673 = 1099255) B1099255
theorem B1465787 : Blo 976593 1465787 := bstep (se 1 (by rfl) ⟨1099340, by rfl⟩ : syracuseStep 1465787 = 2198681) B2198681
theorem B1465847 : Blo 976593 1465847 := bstep (se 1 (by rfl) ⟨1099385, by rfl⟩ : syracuseStep 1465847 = 2198771) B2198771
theorem B1465871 : Blo 976593 1465871 := bstep (se 1 (by rfl) ⟨1099403, by rfl⟩ : syracuseStep 1465871 = 2198807) B2198807
theorem B1859087 : Blo 976593 1859087 := bstep (se 1 (by rfl) ⟨1394315, by rfl⟩ : syracuseStep 1859087 = 2788631) B2788631
theorem B1465913 : Blo 976593 1465913 := bstep (se 2 (by rfl) ⟨549717, by rfl⟩ : syracuseStep 1465913 = 1099435) B1099435
theorem B2481779 : Blo 976593 2481779 := bstep (se 1 (by rfl) ⟨1861334, by rfl⟩ : syracuseStep 2481779 = 3722669) B3722669
theorem B1465991 : Blo 976593 1465991 := bstep (se 1 (by rfl) ⟨1099493, by rfl⟩ : syracuseStep 1465991 = 2198987) B2198987
theorem B2481799 : Blo 976593 2481799 := bstep (se 1 (by rfl) ⟨1861349, by rfl⟩ : syracuseStep 2481799 = 3722699) B3722699
theorem B1466027 : Blo 976593 1466027 := bstep (se 1 (by rfl) ⟨1099520, by rfl⟩ : syracuseStep 1466027 = 2199041) B2199041
theorem B11165363 : Blo 976593 11165363 := bstep (se 1 (by rfl) ⟨8374022, by rfl⟩ : syracuseStep 11165363 = 16748045) B16748045
theorem B1466057 : Blo 976593 1466057 := bstep (se 2 (by rfl) ⟨549771, by rfl⟩ : syracuseStep 1466057 = 1099543) B1099543
theorem B1466171 : Blo 976593 1466171 := bstep (se 1 (by rfl) ⟨1099628, by rfl⟩ : syracuseStep 1466171 = 2199257) B2199257
theorem B3301235 : Blo 976593 3301235 := bstep (se 1 (by rfl) ⟨2475926, by rfl⟩ : syracuseStep 3301235 = 4951853) B4951853
theorem B2645875 : Blo 976593 2645875 := bstep (se 1 (by rfl) ⟨1984406, by rfl⟩ : syracuseStep 2645875 = 3968813) B3968813
theorem B1466231 : Blo 976593 1466231 := bstep (se 1 (by rfl) ⟨1099673, by rfl⟩ : syracuseStep 1466231 = 2199347) B2199347
theorem B1466255 : Blo 976593 1466255 := bstep (se 1 (by rfl) ⟨1099691, by rfl⟩ : syracuseStep 1466255 = 2199383) B2199383
theorem B2973593 : Blo 976593 2973593 := bstep (se 2 (by rfl) ⟨1115097, by rfl⟩ : syracuseStep 2973593 = 2230195) B2230195
theorem B2482073 : Blo 976593 2482073 := bstep (se 2 (by rfl) ⟨930777, by rfl⟩ : syracuseStep 2482073 = 1861555) B1861555
theorem B1466297 : Blo 976593 1466297 := bstep (se 2 (by rfl) ⟨549861, by rfl⟩ : syracuseStep 1466297 = 1099723) B1099723
theorem B1466375 : Blo 976593 1466375 := bstep (se 1 (by rfl) ⟨1099781, by rfl⟩ : syracuseStep 1466375 = 2199563) B2199563
theorem B1466411 : Blo 976593 1466411 := bstep (se 1 (by rfl) ⟨1099808, by rfl⟩ : syracuseStep 1466411 = 2199617) B2199617
theorem B1466441 : Blo 976593 1466441 := bstep (se 2 (by rfl) ⟨549915, by rfl⟩ : syracuseStep 1466441 = 1099831) B1099831
theorem B1466555 : Blo 976593 1466555 := bstep (se 1 (by rfl) ⟨1099916, by rfl⟩ : syracuseStep 1466555 = 2199833) B2199833
theorem B4186313 : Blo 976593 4186313 := bstep (se 2 (by rfl) ⟨1569867, by rfl⟩ : syracuseStep 4186313 = 3139735) B3139735
theorem B1466615 : Blo 976593 1466615 := bstep (se 1 (by rfl) ⟨1099961, by rfl⟩ : syracuseStep 1466615 = 2199923) B2199923
theorem B1466639 : Blo 976593 1466639 := bstep (se 1 (by rfl) ⟨1099979, by rfl⟩ : syracuseStep 1466639 = 2199959) B2199959
theorem B1466681 : Blo 976593 1466681 := bstep (se 2 (by rfl) ⟨550005, by rfl⟩ : syracuseStep 1466681 = 1100011) B1100011
theorem B2548027 : Blo 976593 2548027 := bstep (se 1 (by rfl) ⟨1911020, by rfl⟩ : syracuseStep 2548027 = 3822041) B3822041
theorem B2351447 : Blo 976593 2351447 := bstep (se 1 (by rfl) ⟨1763585, by rfl⟩ : syracuseStep 2351447 = 3527171) B3527171
theorem B1466759 : Blo 976593 1466759 := bstep (se 1 (by rfl) ⟨1100069, by rfl⟩ : syracuseStep 1466759 = 2200139) B2200139
theorem B1466795 : Blo 976593 1466795 := bstep (se 1 (by rfl) ⟨1100096, by rfl⟩ : syracuseStep 1466795 = 2200193) B2200193
theorem B1466825 : Blo 976593 1466825 := bstep (se 2 (by rfl) ⟨550059, by rfl⟩ : syracuseStep 1466825 = 1100119) B1100119
theorem B5300747 : Blo 976593 5300747 := bstep (se 1 (by rfl) ⟨3975560, by rfl⟩ : syracuseStep 5300747 = 7951121) B7951121
theorem B1466939 : Blo 976593 1466939 := bstep (se 1 (by rfl) ⟨1100204, by rfl⟩ : syracuseStep 1466939 = 2200409) B2200409
theorem B2646589 : Blo 976593 2646589 := bstep (se 3 (by rfl) ⟨496235, by rfl⟩ : syracuseStep 2646589 = 992471) B992471
theorem B1466999 : Blo 976593 1466999 := bstep (se 1 (by rfl) ⟨1100249, by rfl⟩ : syracuseStep 1466999 = 2200499) B2200499
theorem B1467023 : Blo 976593 1467023 := bstep (se 1 (by rfl) ⟨1100267, by rfl⟩ : syracuseStep 1467023 = 2200535) B2200535
theorem B1237675 : Blo 976593 1237675 := bstep (se 1 (by rfl) ⟨928256, by rfl⟩ : syracuseStep 1237675 = 1856513) B1856513
theorem B1467065 : Blo 976593 1467065 := bstep (se 2 (by rfl) ⟨550149, by rfl⟩ : syracuseStep 1467065 = 1100299) B1100299
theorem B1467143 : Blo 976593 1467143 := bstep (se 1 (by rfl) ⟨1100357, by rfl⟩ : syracuseStep 1467143 = 2200715) B2200715
theorem B1467179 : Blo 976593 1467179 := bstep (se 1 (by rfl) ⟨1100384, by rfl⟩ : syracuseStep 1467179 = 2200769) B2200769
theorem B2646827 : Blo 976593 2646827 := bstep (se 1 (by rfl) ⟨1985120, by rfl⟩ : syracuseStep 2646827 = 3970241) B3970241
theorem B1467209 : Blo 976593 1467209 := bstep (se 2 (by rfl) ⟨550203, by rfl⟩ : syracuseStep 1467209 = 1100407) B1100407
theorem B1860499 : Blo 976593 1860499 := bstep (se 1 (by rfl) ⟨1395374, by rfl⟩ : syracuseStep 1860499 = 2790749) B2790749
theorem B1467323 : Blo 976593 1467323 := bstep (se 1 (by rfl) ⟨1100492, by rfl⟩ : syracuseStep 1467323 = 2200985) B2200985
theorem B1467383 : Blo 976593 1467383 := bstep (se 1 (by rfl) ⟨1100537, by rfl⟩ : syracuseStep 1467383 = 2201075) B2201075
theorem B1467407 : Blo 976593 1467407 := bstep (se 1 (by rfl) ⟨1100555, by rfl⟩ : syracuseStep 1467407 = 2201111) B2201111
theorem B1467449 : Blo 976593 1467449 := bstep (se 2 (by rfl) ⟨550293, by rfl⟩ : syracuseStep 1467449 = 1100587) B1100587
theorem B2352187 : Blo 976593 2352187 := bstep (se 1 (by rfl) ⟨1764140, by rfl⟩ : syracuseStep 2352187 = 3528281) B3528281
theorem B1860727 : Blo 976593 1860727 := bstep (se 1 (by rfl) ⟨1395545, by rfl⟩ : syracuseStep 1860727 = 2791091) B2791091
theorem B1467527 : Blo 976593 1467527 := bstep (se 1 (by rfl) ⟨1100645, by rfl⟩ : syracuseStep 1467527 = 2201291) B2201291
theorem B1467563 : Blo 976593 1467563 := bstep (se 1 (by rfl) ⟨1100672, by rfl⟩ : syracuseStep 1467563 = 2201345) B2201345
theorem B1467593 : Blo 976593 1467593 := bstep (se 2 (by rfl) ⟨550347, by rfl⟩ : syracuseStep 1467593 = 1100695) B1100695
theorem B5956915 : Blo 976593 5956915 := bstep (se 1 (by rfl) ⟨4467686, by rfl⟩ : syracuseStep 5956915 = 8935373) B8935373
theorem B1467707 : Blo 976593 1467707 := bstep (se 1 (by rfl) ⟨1100780, by rfl⟩ : syracuseStep 1467707 = 2201561) B2201561
theorem B1467767 : Blo 976593 1467767 := bstep (se 1 (by rfl) ⟨1100825, by rfl⟩ : syracuseStep 1467767 = 2201651) B2201651
theorem B1467791 : Blo 976593 1467791 := bstep (se 1 (by rfl) ⟨1100843, by rfl⟩ : syracuseStep 1467791 = 2201687) B2201687
theorem B7923091 : Blo 976593 7923091 := bstep (se 1 (by rfl) ⟨5942318, by rfl⟩ : syracuseStep 7923091 = 11884637) B11884637
theorem B1467833 : Blo 976593 1467833 := bstep (se 2 (by rfl) ⟨550437, by rfl⟩ : syracuseStep 1467833 = 1100875) B1100875
theorem B14116355 : Blo 976593 14116355 := bstep (se 1 (by rfl) ⟨10587266, by rfl⟩ : syracuseStep 14116355 = 21174533) B21174533
theorem B1467911 : Blo 976593 1467911 := bstep (se 1 (by rfl) ⟨1100933, by rfl⟩ : syracuseStep 1467911 = 2201867) B2201867
theorem B16934429 : Blo 976593 16934429 := bstep (se 3 (by rfl) ⟨3175205, by rfl⟩ : syracuseStep 16934429 = 6350411) B6350411
theorem B1467947 : Blo 976593 1467947 := bstep (se 1 (by rfl) ⟨1100960, by rfl⟩ : syracuseStep 1467947 = 2201921) B2201921
theorem B1467977 : Blo 976593 1467977 := bstep (se 2 (by rfl) ⟨550491, by rfl⟩ : syracuseStep 1467977 = 1100983) B1100983
theorem B1238647 : Blo 976593 1238647 := bstep (se 1 (by rfl) ⟨928985, by rfl⟩ : syracuseStep 1238647 = 1857971) B1857971
theorem B1468091 : Blo 976593 1468091 := bstep (se 1 (by rfl) ⟨1101068, by rfl⟩ : syracuseStep 1468091 = 2202137) B2202137
theorem B1468151 : Blo 976593 1468151 := bstep (se 1 (by rfl) ⟨1101113, by rfl⟩ : syracuseStep 1468151 = 2202227) B2202227
theorem B976647 : Blo 976593 976647 := bstep (se 1 (by rfl) ⟨732485, by rfl⟩ : syracuseStep 976647 = 1464971) B1464971
theorem B1173263 : Blo 976593 1173263 := bstep (se 1 (by rfl) ⟨879947, by rfl⟩ : syracuseStep 1173263 = 1759895) B1759895
theorem B976655 : Blo 976593 976655 := bstep (se 1 (by rfl) ⟨732491, by rfl⟩ : syracuseStep 976655 = 1464983) B1464983
theorem B1468175 : Blo 976593 1468175 := bstep (se 1 (by rfl) ⟨1101131, by rfl⟩ : syracuseStep 1468175 = 2202263) B2202263
theorem B1468217 : Blo 976593 1468217 := bstep (se 2 (by rfl) ⟨550581, by rfl⟩ : syracuseStep 1468217 = 1101163) B1101163
theorem B976699 : Blo 976593 976699 := bstep (se 1 (by rfl) ⟨732524, by rfl⟩ : syracuseStep 976699 = 1465049) B1465049
theorem B976775 : Blo 976593 976775 := bstep (se 1 (by rfl) ⟨732581, by rfl⟩ : syracuseStep 976775 = 1465163) B1465163
theorem B1468295 : Blo 976593 1468295 := bstep (se 1 (by rfl) ⟨1101221, by rfl⟩ : syracuseStep 1468295 = 2202443) B2202443
theorem B3532679 : Blo 976593 3532679 := bstep (se 1 (by rfl) ⟨2649509, by rfl⟩ : syracuseStep 3532679 = 5299019) B5299019
theorem B976783 : Blo 976593 976783 := bstep (se 1 (by rfl) ⟨732587, by rfl⟩ : syracuseStep 976783 = 1465175) B1465175
theorem B1468331 : Blo 976593 1468331 := bstep (se 1 (by rfl) ⟨1101248, by rfl⟩ : syracuseStep 1468331 = 2202497) B2202497
theorem B976827 : Blo 976593 976827 := bstep (se 1 (by rfl) ⟨732620, by rfl⟩ : syracuseStep 976827 = 1465241) B1465241
theorem B1238971 : Blo 976593 1238971 := bstep (se 1 (by rfl) ⟨929228, by rfl⟩ : syracuseStep 1238971 = 1858457) B1858457
theorem B1468361 : Blo 976593 1468361 := bstep (se 2 (by rfl) ⟨550635, by rfl⟩ : syracuseStep 1468361 = 1101271) B1101271
theorem B976903 : Blo 976593 976903 := bstep (se 1 (by rfl) ⟨732677, by rfl⟩ : syracuseStep 976903 = 1465355) B1465355
theorem B976911 : Blo 976593 976911 := bstep (se 1 (by rfl) ⟨732683, by rfl⟩ : syracuseStep 976911 = 1465367) B1465367
theorem B2353195 : Blo 976593 2353195 := bstep (se 1 (by rfl) ⟨1764896, by rfl⟩ : syracuseStep 2353195 = 3529793) B3529793
theorem B976955 : Blo 976593 976955 := bstep (se 1 (by rfl) ⟨732716, by rfl⟩ : syracuseStep 976955 = 1465433) B1465433
theorem B1468475 : Blo 976593 1468475 := bstep (se 1 (by rfl) ⟨1101356, by rfl⟩ : syracuseStep 1468475 = 2202713) B2202713
theorem B1468535 : Blo 976593 1468535 := bstep (se 1 (by rfl) ⟨1101401, by rfl⟩ : syracuseStep 1468535 = 2202803) B2202803
theorem B977031 : Blo 976593 977031 := bstep (se 1 (by rfl) ⟨732773, by rfl⟩ : syracuseStep 977031 = 1465547) B1465547
theorem B977039 : Blo 976593 977039 := bstep (se 1 (by rfl) ⟨732779, by rfl⟩ : syracuseStep 977039 = 1465559) B1465559
theorem B1468559 : Blo 976593 1468559 := bstep (se 1 (by rfl) ⟨1101419, by rfl⟩ : syracuseStep 1468559 = 2202839) B2202839
theorem B1763513 : Blo 976593 1763513 := bstep (se 2 (by rfl) ⟨661317, by rfl⟩ : syracuseStep 1763513 = 1322635) B1322635
theorem B1468601 : Blo 976593 1468601 := bstep (se 2 (by rfl) ⟨550725, by rfl⟩ : syracuseStep 1468601 = 1101451) B1101451
theorem B977083 : Blo 976593 977083 := bstep (se 1 (by rfl) ⟨732812, by rfl⟩ : syracuseStep 977083 = 1465625) B1465625
theorem B977159 : Blo 976593 977159 := bstep (se 1 (by rfl) ⟨732869, by rfl⟩ : syracuseStep 977159 = 1465739) B1465739
theorem B1468679 : Blo 976593 1468679 := bstep (se 1 (by rfl) ⟨1101509, by rfl⟩ : syracuseStep 1468679 = 2203019) B2203019
theorem B977167 : Blo 976593 977167 := bstep (se 1 (by rfl) ⟨732875, by rfl⟩ : syracuseStep 977167 = 1465751) B1465751
theorem B1468715 : Blo 976593 1468715 := bstep (se 1 (by rfl) ⟨1101536, by rfl⟩ : syracuseStep 1468715 = 2203073) B2203073
theorem B977211 : Blo 976593 977211 := bstep (se 1 (by rfl) ⟨732908, by rfl⟩ : syracuseStep 977211 = 1465817) B1465817
theorem B1468745 : Blo 976593 1468745 := bstep (se 2 (by rfl) ⟨550779, by rfl⟩ : syracuseStep 1468745 = 1101559) B1101559
theorem B977287 : Blo 976593 977287 := bstep (se 1 (by rfl) ⟨732965, by rfl⟩ : syracuseStep 977287 = 1465931) B1465931
theorem B977295 : Blo 976593 977295 := bstep (se 1 (by rfl) ⟨732971, by rfl⟩ : syracuseStep 977295 = 1465943) B1465943
theorem B3303827 : Blo 976593 3303827 := bstep (se 1 (by rfl) ⟨2477870, by rfl⟩ : syracuseStep 3303827 = 4955741) B4955741
theorem B977339 : Blo 976593 977339 := bstep (se 1 (by rfl) ⟨733004, by rfl⟩ : syracuseStep 977339 = 1466009) B1466009
theorem B1468859 : Blo 976593 1468859 := bstep (se 1 (by rfl) ⟨1101644, by rfl⟩ : syracuseStep 1468859 = 2203289) B2203289
theorem B1468919 : Blo 976593 1468919 := bstep (se 1 (by rfl) ⟨1101689, by rfl⟩ : syracuseStep 1468919 = 2203379) B2203379
theorem B977415 : Blo 976593 977415 := bstep (se 1 (by rfl) ⟨733061, by rfl⟩ : syracuseStep 977415 = 1466123) B1466123
theorem B977423 : Blo 976593 977423 := bstep (se 1 (by rfl) ⟨733067, by rfl⟩ : syracuseStep 977423 = 1466135) B1466135
theorem B1468943 : Blo 976593 1468943 := bstep (se 1 (by rfl) ⟨1101707, by rfl⟩ : syracuseStep 1468943 = 2203415) B2203415
theorem B1468985 : Blo 976593 1468985 := bstep (se 2 (by rfl) ⟨550869, by rfl⟩ : syracuseStep 1468985 = 1101739) B1101739
theorem B1043003 : Blo 976593 1043003 := bstep (se 1 (by rfl) ⟨782252, by rfl⟩ : syracuseStep 1043003 = 1564505) B1564505
theorem B977467 : Blo 976593 977467 := bstep (se 1 (by rfl) ⟨733100, by rfl⟩ : syracuseStep 977467 = 1466201) B1466201
theorem B3140183 : Blo 976593 3140183 := bstep (se 1 (by rfl) ⟨2355137, by rfl⟩ : syracuseStep 3140183 = 4710275) B4710275
theorem B977543 : Blo 976593 977543 := bstep (se 1 (by rfl) ⟨733157, by rfl⟩ : syracuseStep 977543 = 1466315) B1466315
theorem B1469063 : Blo 976593 1469063 := bstep (se 1 (by rfl) ⟨1101797, by rfl⟩ : syracuseStep 1469063 = 2203595) B2203595
theorem B977551 : Blo 976593 977551 := bstep (se 1 (by rfl) ⟨733163, by rfl⟩ : syracuseStep 977551 = 1466327) B1466327
theorem B2648729 : Blo 976593 2648729 := bstep (se 2 (by rfl) ⟨993273, by rfl⟩ : syracuseStep 2648729 = 1986547) B1986547
theorem B1469099 : Blo 976593 1469099 := bstep (se 1 (by rfl) ⟨1101824, by rfl⟩ : syracuseStep 1469099 = 2203649) B2203649
theorem B977595 : Blo 976593 977595 := bstep (se 1 (by rfl) ⟨733196, by rfl⟩ : syracuseStep 977595 = 1466393) B1466393
theorem B19098305 : Blo 976593 19098305 := bstep (se 2 (by rfl) ⟨7161864, by rfl⟩ : syracuseStep 19098305 = 14323729) B14323729
theorem B1469129 : Blo 976593 1469129 := bstep (se 2 (by rfl) ⟨550923, by rfl⟩ : syracuseStep 1469129 = 1101847) B1101847
theorem B977671 : Blo 976593 977671 := bstep (se 1 (by rfl) ⟨733253, by rfl⟩ : syracuseStep 977671 = 1466507) B1466507
theorem B977679 : Blo 976593 977679 := bstep (se 1 (by rfl) ⟨733259, by rfl⟩ : syracuseStep 977679 = 1466519) B1466519
theorem B977723 : Blo 976593 977723 := bstep (se 1 (by rfl) ⟨733292, by rfl⟩ : syracuseStep 977723 = 1466585) B1466585
theorem B1469243 : Blo 976593 1469243 := bstep (se 1 (by rfl) ⟨1101932, by rfl⟩ : syracuseStep 1469243 = 2203865) B2203865
theorem B1469303 : Blo 976593 1469303 := bstep (se 1 (by rfl) ⟨1101977, by rfl⟩ : syracuseStep 1469303 = 2203955) B2203955
theorem B977799 : Blo 976593 977799 := bstep (se 1 (by rfl) ⟨733349, by rfl⟩ : syracuseStep 977799 = 1466699) B1466699
theorem B1239943 : Blo 976593 1239943 := bstep (se 1 (by rfl) ⟨929957, by rfl⟩ : syracuseStep 1239943 = 1859915) B1859915
theorem B977807 : Blo 976593 977807 := bstep (se 1 (by rfl) ⟨733355, by rfl⟩ : syracuseStep 977807 = 1466711) B1466711
theorem B1469327 : Blo 976593 1469327 := bstep (se 1 (by rfl) ⟨1101995, by rfl⟩ : syracuseStep 1469327 = 2203991) B2203991
theorem B1469369 : Blo 976593 1469369 := bstep (se 2 (by rfl) ⟨551013, by rfl⟩ : syracuseStep 1469369 = 1102027) B1102027
theorem B977851 : Blo 976593 977851 := bstep (se 1 (by rfl) ⟨733388, by rfl⟩ : syracuseStep 977851 = 1466777) B1466777
theorem B977927 : Blo 976593 977927 := bstep (se 1 (by rfl) ⟨733445, by rfl⟩ : syracuseStep 977927 = 1466891) B1466891
theorem B1469447 : Blo 976593 1469447 := bstep (se 1 (by rfl) ⟨1102085, by rfl⟩ : syracuseStep 1469447 = 2204171) B2204171
theorem B977935 : Blo 976593 977935 := bstep (se 1 (by rfl) ⟨733451, by rfl⟩ : syracuseStep 977935 = 1466903) B1466903
theorem B1469483 : Blo 976593 1469483 := bstep (se 1 (by rfl) ⟨1102112, by rfl⟩ : syracuseStep 1469483 = 2204225) B2204225
theorem B977979 : Blo 976593 977979 := bstep (se 1 (by rfl) ⟨733484, by rfl⟩ : syracuseStep 977979 = 1466969) B1466969
theorem B3140669 : Blo 976593 3140669 := bstep (se 3 (by rfl) ⟨588875, by rfl⟩ : syracuseStep 3140669 = 1177751) B1177751
theorem B1469513 : Blo 976593 1469513 := bstep (se 2 (by rfl) ⟨551067, by rfl⟩ : syracuseStep 1469513 = 1102135) B1102135
theorem B978055 : Blo 976593 978055 := bstep (se 1 (by rfl) ⟨733541, by rfl⟩ : syracuseStep 978055 = 1467083) B1467083
theorem B978063 : Blo 976593 978063 := bstep (se 1 (by rfl) ⟨733547, by rfl⟩ : syracuseStep 978063 = 1467095) B1467095
theorem B978107 : Blo 976593 978107 := bstep (se 1 (by rfl) ⟨733580, by rfl⟩ : syracuseStep 978107 = 1467161) B1467161
theorem B1469627 : Blo 976593 1469627 := bstep (se 1 (by rfl) ⟨1102220, by rfl⟩ : syracuseStep 1469627 = 2204441) B2204441
theorem B1469687 : Blo 976593 1469687 := bstep (se 1 (by rfl) ⟨1102265, by rfl⟩ : syracuseStep 1469687 = 2204531) B2204531
theorem B978183 : Blo 976593 978183 := bstep (se 1 (by rfl) ⟨733637, by rfl⟩ : syracuseStep 978183 = 1467275) B1467275
theorem B978191 : Blo 976593 978191 := bstep (se 1 (by rfl) ⟨733643, by rfl⟩ : syracuseStep 978191 = 1467287) B1467287
theorem B1469711 : Blo 976593 1469711 := bstep (se 1 (by rfl) ⟨1102283, by rfl⟩ : syracuseStep 1469711 = 2204567) B2204567
theorem B1240363 : Blo 976593 1240363 := bstep (se 1 (by rfl) ⟨930272, by rfl⟩ : syracuseStep 1240363 = 1860545) B1860545
theorem B1469753 : Blo 976593 1469753 := bstep (se 2 (by rfl) ⟨551157, by rfl⟩ : syracuseStep 1469753 = 1102315) B1102315
theorem B978235 : Blo 976593 978235 := bstep (se 1 (by rfl) ⟨733676, by rfl⟩ : syracuseStep 978235 = 1467353) B1467353
theorem B978311 : Blo 976593 978311 := bstep (se 1 (by rfl) ⟨733733, by rfl⟩ : syracuseStep 978311 = 1467467) B1467467
theorem B1469831 : Blo 976593 1469831 := bstep (se 1 (by rfl) ⟨1102373, by rfl⟩ : syracuseStep 1469831 = 2204747) B2204747
theorem B978319 : Blo 976593 978319 := bstep (se 1 (by rfl) ⟨733739, by rfl⟩ : syracuseStep 978319 = 1467479) B1467479
theorem B1469867 : Blo 976593 1469867 := bstep (se 1 (by rfl) ⟨1102400, by rfl⟩ : syracuseStep 1469867 = 2204801) B2204801
theorem B978363 : Blo 976593 978363 := bstep (se 1 (by rfl) ⟨733772, by rfl⟩ : syracuseStep 978363 = 1467545) B1467545
theorem B1469897 : Blo 976593 1469897 := bstep (se 2 (by rfl) ⟨551211, by rfl⟩ : syracuseStep 1469897 = 1102423) B1102423
theorem B978439 : Blo 976593 978439 := bstep (se 1 (by rfl) ⟨733829, by rfl⟩ : syracuseStep 978439 = 1467659) B1467659
theorem B978447 : Blo 976593 978447 := bstep (se 1 (by rfl) ⟨733835, by rfl⟩ : syracuseStep 978447 = 1467671) B1467671
theorem B1240591 : Blo 976593 1240591 := bstep (se 1 (by rfl) ⟨930443, by rfl⟩ : syracuseStep 1240591 = 1860887) B1860887
theorem B978491 : Blo 976593 978491 := bstep (se 1 (by rfl) ⟨733868, by rfl⟩ : syracuseStep 978491 = 1467737) B1467737
theorem B1470011 : Blo 976593 1470011 := bstep (se 1 (by rfl) ⟨1102508, by rfl⟩ : syracuseStep 1470011 = 2205017) B2205017
theorem B1470071 : Blo 976593 1470071 := bstep (se 1 (by rfl) ⟨1102553, by rfl⟩ : syracuseStep 1470071 = 2205107) B2205107
theorem B978567 : Blo 976593 978567 := bstep (se 1 (by rfl) ⟨733925, by rfl⟩ : syracuseStep 978567 = 1467851) B1467851
theorem B978575 : Blo 976593 978575 := bstep (se 1 (by rfl) ⟨733931, by rfl⟩ : syracuseStep 978575 = 1467863) B1467863
theorem B1470095 : Blo 976593 1470095 := bstep (se 1 (by rfl) ⟨1102571, by rfl⟩ : syracuseStep 1470095 = 2205143) B2205143
theorem B1470137 : Blo 976593 1470137 := bstep (se 2 (by rfl) ⟨551301, by rfl⟩ : syracuseStep 1470137 = 1102603) B1102603
theorem B978619 : Blo 976593 978619 := bstep (se 1 (by rfl) ⟨733964, by rfl⟩ : syracuseStep 978619 = 1467929) B1467929
theorem B978695 : Blo 976593 978695 := bstep (se 1 (by rfl) ⟨734021, by rfl⟩ : syracuseStep 978695 = 1468043) B1468043
theorem B1470215 : Blo 976593 1470215 := bstep (se 1 (by rfl) ⟨1102661, by rfl⟩ : syracuseStep 1470215 = 2205323) B2205323
theorem B978703 : Blo 976593 978703 := bstep (se 1 (by rfl) ⟨734027, by rfl⟩ : syracuseStep 978703 = 1468055) B1468055
theorem B3305231 : Blo 976593 3305231 := bstep (se 1 (by rfl) ⟨2478923, by rfl⟩ : syracuseStep 3305231 = 4957847) B4957847
theorem B1470251 : Blo 976593 1470251 := bstep (se 1 (by rfl) ⟨1102688, by rfl⟩ : syracuseStep 1470251 = 2205377) B2205377
theorem B978747 : Blo 976593 978747 := bstep (se 1 (by rfl) ⟨734060, by rfl⟩ : syracuseStep 978747 = 1468121) B1468121
theorem B1470281 : Blo 976593 1470281 := bstep (se 2 (by rfl) ⟨551355, by rfl⟩ : syracuseStep 1470281 = 1102711) B1102711
theorem B4353907 : Blo 976593 4353907 := bstep (se 1 (by rfl) ⟨3265430, by rfl⟩ : syracuseStep 4353907 = 6530861) B6530861
theorem B978823 : Blo 976593 978823 := bstep (se 1 (by rfl) ⟨734117, by rfl⟩ : syracuseStep 978823 = 1468235) B1468235
theorem B978831 : Blo 976593 978831 := bstep (se 1 (by rfl) ⟨734123, by rfl⟩ : syracuseStep 978831 = 1468247) B1468247
theorem B1175483 : Blo 976593 1175483 := bstep (se 1 (by rfl) ⟨881612, by rfl⟩ : syracuseStep 1175483 = 1763225) B1763225
theorem B978875 : Blo 976593 978875 := bstep (se 1 (by rfl) ⟨734156, by rfl⟩ : syracuseStep 978875 = 1468313) B1468313
theorem B1470395 : Blo 976593 1470395 := bstep (se 1 (by rfl) ⟨1102796, by rfl⟩ : syracuseStep 1470395 = 2205593) B2205593
theorem B1470455 : Blo 976593 1470455 := bstep (se 1 (by rfl) ⟨1102841, by rfl⟩ : syracuseStep 1470455 = 2205683) B2205683
theorem B978951 : Blo 976593 978951 := bstep (se 1 (by rfl) ⟨734213, by rfl⟩ : syracuseStep 978951 = 1468427) B1468427
theorem B978959 : Blo 976593 978959 := bstep (se 1 (by rfl) ⟨734219, by rfl⟩ : syracuseStep 978959 = 1468439) B1468439
theorem B2682895 : Blo 976593 2682895 := bstep (se 1 (by rfl) ⟨2012171, by rfl⟩ : syracuseStep 2682895 = 4024343) B4024343
theorem B1470479 : Blo 976593 1470479 := bstep (se 1 (by rfl) ⟨1102859, by rfl⟩ : syracuseStep 1470479 = 2205719) B2205719
theorem B3305501 : Blo 976593 3305501 := bstep (se 3 (by rfl) ⟨619781, by rfl⟩ : syracuseStep 3305501 = 1239563) B1239563
theorem B1470521 : Blo 976593 1470521 := bstep (se 2 (by rfl) ⟨551445, by rfl⟩ : syracuseStep 1470521 = 1102891) B1102891
theorem B979003 : Blo 976593 979003 := bstep (se 1 (by rfl) ⟨734252, by rfl⟩ : syracuseStep 979003 = 1468505) B1468505
theorem B11923517 : Blo 976593 11923517 := bstep (se 3 (by rfl) ⟨2235659, by rfl⟩ : syracuseStep 11923517 = 4471319) B4471319
theorem B979079 : Blo 976593 979079 := bstep (se 1 (by rfl) ⟨734309, by rfl⟩ : syracuseStep 979079 = 1468619) B1468619
theorem B1470599 : Blo 976593 1470599 := bstep (se 1 (by rfl) ⟨1102949, by rfl⟩ : syracuseStep 1470599 = 2205899) B2205899
theorem B979087 : Blo 976593 979087 := bstep (se 1 (by rfl) ⟨734315, by rfl⟩ : syracuseStep 979087 = 1468631) B1468631
theorem B1470635 : Blo 976593 1470635 := bstep (se 1 (by rfl) ⟨1102976, by rfl⟩ : syracuseStep 1470635 = 2205953) B2205953
theorem B979131 : Blo 976593 979131 := bstep (se 1 (by rfl) ⟨734348, by rfl⟩ : syracuseStep 979131 = 1468697) B1468697
theorem B1470665 : Blo 976593 1470665 := bstep (se 2 (by rfl) ⟨551499, by rfl⟩ : syracuseStep 1470665 = 1102999) B1102999
theorem B979207 : Blo 976593 979207 := bstep (se 1 (by rfl) ⟨734405, by rfl⟩ : syracuseStep 979207 = 1468811) B1468811
theorem B979215 : Blo 976593 979215 := bstep (se 1 (by rfl) ⟨734411, by rfl⟩ : syracuseStep 979215 = 1468823) B1468823
theorem B979259 : Blo 976593 979259 := bstep (se 1 (by rfl) ⟨734444, by rfl⟩ : syracuseStep 979259 = 1468889) B1468889
theorem B1470779 : Blo 976593 1470779 := bstep (se 1 (by rfl) ⟨1103084, by rfl⟩ : syracuseStep 1470779 = 2206169) B2206169
theorem B2978167 : Blo 976593 2978167 := bstep (se 1 (by rfl) ⟨2233625, by rfl⟩ : syracuseStep 2978167 = 4467251) B4467251
theorem B1470839 : Blo 976593 1470839 := bstep (se 1 (by rfl) ⟨1103129, by rfl⟩ : syracuseStep 1470839 = 2206259) B2206259
theorem B979335 : Blo 976593 979335 := bstep (se 1 (by rfl) ⟨734501, by rfl⟩ : syracuseStep 979335 = 1469003) B1469003
theorem B979343 : Blo 976593 979343 := bstep (se 1 (by rfl) ⟨734507, by rfl⟩ : syracuseStep 979343 = 1469015) B1469015
theorem B1470863 : Blo 976593 1470863 := bstep (se 1 (by rfl) ⟨1103147, by rfl⟩ : syracuseStep 1470863 = 2206295) B2206295
theorem B979387 : Blo 976593 979387 := bstep (se 1 (by rfl) ⟨734540, by rfl⟩ : syracuseStep 979387 = 1469081) B1469081
theorem B979463 : Blo 976593 979463 := bstep (se 1 (by rfl) ⟨734597, by rfl⟩ : syracuseStep 979463 = 1469195) B1469195
theorem B979471 : Blo 976593 979471 := bstep (se 1 (by rfl) ⟨734603, by rfl⟩ : syracuseStep 979471 = 1469207) B1469207
theorem B979515 : Blo 976593 979515 := bstep (se 1 (by rfl) ⟨734636, by rfl⟩ : syracuseStep 979515 = 1469273) B1469273
theorem B979591 : Blo 976593 979591 := bstep (se 1 (by rfl) ⟨734693, by rfl⟩ : syracuseStep 979591 = 1469387) B1469387
theorem B979599 : Blo 976593 979599 := bstep (se 1 (by rfl) ⟨734699, by rfl⟩ : syracuseStep 979599 = 1469399) B1469399
theorem B18772661 : Blo 976593 18772661 := bstep (se 5 (by rfl) ⟨879968, by rfl⟩ : syracuseStep 18772661 = 1759937) B1759937
theorem B979643 : Blo 976593 979643 := bstep (se 1 (by rfl) ⟨734732, by rfl⟩ : syracuseStep 979643 = 1469465) B1469465
theorem B979719 : Blo 976593 979719 := bstep (se 1 (by rfl) ⟨734789, by rfl⟩ : syracuseStep 979719 = 1469579) B1469579
theorem B979727 : Blo 976593 979727 := bstep (se 1 (by rfl) ⟨734795, by rfl⟩ : syracuseStep 979727 = 1469591) B1469591
theorem B34861859 : Blo 976593 34861859 := bstep (se 1 (by rfl) ⟨26146394, by rfl⟩ : syracuseStep 34861859 = 52292789) B52292789
theorem B979771 : Blo 976593 979771 := bstep (se 1 (by rfl) ⟨734828, by rfl⟩ : syracuseStep 979771 = 1469657) B1469657
theorem B20083571 : Blo 976593 20083571 := bstep (se 1 (by rfl) ⟨15062678, by rfl⟩ : syracuseStep 20083571 = 30125357) B30125357
theorem B979847 : Blo 976593 979847 := bstep (se 1 (by rfl) ⟨734885, by rfl⟩ : syracuseStep 979847 = 1469771) B1469771
theorem B979855 : Blo 976593 979855 := bstep (se 1 (by rfl) ⟨734891, by rfl⟩ : syracuseStep 979855 = 1469783) B1469783
theorem B979899 : Blo 976593 979899 := bstep (se 1 (by rfl) ⟨734924, by rfl⟩ : syracuseStep 979899 = 1469849) B1469849
theorem B979975 : Blo 976593 979975 := bstep (se 1 (by rfl) ⟨734981, by rfl⟩ : syracuseStep 979975 = 1469963) B1469963
theorem B979983 : Blo 976593 979983 := bstep (se 1 (by rfl) ⟨734987, by rfl⟩ : syracuseStep 979983 = 1469975) B1469975
theorem B2094113 : Blo 976593 2094113 := bstep (se 2 (by rfl) ⟨785292, by rfl⟩ : syracuseStep 2094113 = 1570585) B1570585
theorem B980027 : Blo 976593 980027 := bstep (se 1 (by rfl) ⟨735020, by rfl⟩ : syracuseStep 980027 = 1470041) B1470041
theorem B5567555 : Blo 976593 5567555 := bstep (se 1 (by rfl) ⟨4175666, by rfl⟩ : syracuseStep 5567555 = 8351333) B8351333
theorem B2683991 : Blo 976593 2683991 := bstep (se 1 (by rfl) ⟨2012993, by rfl⟩ : syracuseStep 2683991 = 4025987) B4025987
theorem B2782343 : Blo 976593 2782343 := bstep (se 1 (by rfl) ⟨2086757, by rfl⟩ : syracuseStep 2782343 = 4173515) B4173515
theorem B980103 : Blo 976593 980103 := bstep (se 1 (by rfl) ⟨735077, by rfl⟩ : syracuseStep 980103 = 1470155) B1470155
theorem B980111 : Blo 976593 980111 := bstep (se 1 (by rfl) ⟨735083, by rfl⟩ : syracuseStep 980111 = 1470167) B1470167
theorem B980155 : Blo 976593 980155 := bstep (se 1 (by rfl) ⟨735116, by rfl⟩ : syracuseStep 980155 = 1470233) B1470233
theorem B980231 : Blo 976593 980231 := bstep (se 1 (by rfl) ⟨735173, by rfl⟩ : syracuseStep 980231 = 1470347) B1470347
theorem B980239 : Blo 976593 980239 := bstep (se 1 (by rfl) ⟨735179, by rfl⟩ : syracuseStep 980239 = 1470359) B1470359
theorem B4945211 : Blo 976593 4945211 := bstep (se 1 (by rfl) ⟨3708908, by rfl⟩ : syracuseStep 4945211 = 7417817) B7417817
theorem B980283 : Blo 976593 980283 := bstep (se 1 (by rfl) ⟨735212, by rfl⟩ : syracuseStep 980283 = 1470425) B1470425
theorem B2782525 : Blo 976593 2782525 := bstep (se 3 (by rfl) ⟨521723, by rfl⟩ : syracuseStep 2782525 = 1043447) B1043447
theorem B2782583 : Blo 976593 2782583 := bstep (se 1 (by rfl) ⟨2086937, by rfl⟩ : syracuseStep 2782583 = 4173875) B4173875
theorem B980359 : Blo 976593 980359 := bstep (se 1 (by rfl) ⟨735269, by rfl⟩ : syracuseStep 980359 = 1470539) B1470539
theorem B980367 : Blo 976593 980367 := bstep (se 1 (by rfl) ⟨735275, by rfl⟩ : syracuseStep 980367 = 1470551) B1470551
theorem B3306905 : Blo 976593 3306905 := bstep (se 2 (by rfl) ⟨1240089, by rfl⟩ : syracuseStep 3306905 = 2480179) B2480179
theorem B980411 : Blo 976593 980411 := bstep (se 1 (by rfl) ⟨735308, by rfl⟩ : syracuseStep 980411 = 1470617) B1470617
theorem B1766857 : Blo 976593 1766857 := bstep (se 2 (by rfl) ⟨662571, by rfl⟩ : syracuseStep 1766857 = 1325143) B1325143
theorem B4945373 : Blo 976593 4945373 := bstep (se 3 (by rfl) ⟨927257, by rfl⟩ : syracuseStep 4945373 = 1854515) B1854515
theorem B980487 : Blo 976593 980487 := bstep (se 1 (by rfl) ⟨735365, by rfl⟩ : syracuseStep 980487 = 1470731) B1470731
theorem B5568011 : Blo 976593 5568011 := bstep (se 1 (by rfl) ⟨4176008, by rfl⟩ : syracuseStep 5568011 = 8352017) B8352017
theorem B40138253 : Blo 976593 40138253 := bstep (se 3 (by rfl) ⟨7525922, by rfl⟩ : syracuseStep 40138253 = 15051845) B15051845
theorem B980495 : Blo 976593 980495 := bstep (se 1 (by rfl) ⟨735371, by rfl⟩ : syracuseStep 980495 = 1470743) B1470743
theorem B980539 : Blo 976593 980539 := bstep (se 1 (by rfl) ⟨735404, by rfl⟩ : syracuseStep 980539 = 1470809) B1470809
theorem B4945697 : Blo 976593 4945697 := bstep (se 2 (by rfl) ⟨1854636, by rfl⟩ : syracuseStep 4945697 = 3709273) B3709273
theorem B3307607 : Blo 976593 3307607 := bstep (se 1 (by rfl) ⟨2480705, by rfl⟩ : syracuseStep 3307607 = 4961411) B4961411
theorem B2783641 : Blo 976593 2783641 := bstep (se 2 (by rfl) ⟨1043865, by rfl⟩ : syracuseStep 2783641 = 2087731) B2087731
theorem B3308093 : Blo 976593 3308093 := bstep (se 3 (by rfl) ⟨620267, by rfl⟩ : syracuseStep 3308093 = 1240535) B1240535
theorem B13368025 : Blo 976593 13368025 := bstep (se 2 (by rfl) ⟨5013009, by rfl⟩ : syracuseStep 13368025 = 10026019) B10026019
theorem B4946669 : Blo 976593 4946669 := bstep (se 3 (by rfl) ⟨927500, by rfl⟩ : syracuseStep 4946669 = 1855001) B1855001
theorem B2784257 : Blo 976593 2784257 := bstep (se 2 (by rfl) ⟨1044096, by rfl⟩ : syracuseStep 2784257 = 2088193) B2088193
theorem B1506319 : Blo 976593 1506319 := bstep (se 1 (by rfl) ⟨1129739, by rfl⟩ : syracuseStep 1506319 = 2259479) B2259479
theorem B4947479 : Blo 976593 4947479 := bstep (se 1 (by rfl) ⟨3710609, by rfl⟩ : syracuseStep 4947479 = 7421219) B7421219
theorem B6028919 : Blo 976593 6028919 := bstep (se 1 (by rfl) ⟨4521689, by rfl⟩ : syracuseStep 6028919 = 9043379) B9043379
theorem B3309497 : Blo 976593 3309497 := bstep (se 2 (by rfl) ⟨1241061, by rfl⟩ : syracuseStep 3309497 = 2482123) B2482123
theorem B2785225 : Blo 976593 2785225 := bstep (se 2 (by rfl) ⟨1044459, by rfl⟩ : syracuseStep 2785225 = 2088919) B2088919
theorem B7929971 : Blo 976593 7929971 := bstep (se 1 (by rfl) ⟨5947478, by rfl⟩ : syracuseStep 7929971 = 11894957) B11894957
theorem B12550373 : Blo 976593 12550373 := bstep (se 4 (by rfl) ⟨1176597, by rfl⟩ : syracuseStep 12550373 = 2353195) B2353195
theorem B3343133 : Blo 976593 3343133 := bstep (se 3 (by rfl) ⟨626837, by rfl⟩ : syracuseStep 3343133 = 1253675) B1253675
theorem B16713053 : Blo 976593 16713053 := bstep (se 3 (by rfl) ⟨3133697, by rfl⟩ : syracuseStep 16713053 = 6267395) B6267395
theorem B2197511 : Blo 976593 2197511 := bstep (se 1 (by rfl) ⟨1648133, by rfl⟩ : syracuseStep 2197511 = 3296267) B3296267
theorem B3180559 : Blo 976593 3180559 := bstep (se 1 (by rfl) ⟨2385419, by rfl⟩ : syracuseStep 3180559 = 4770839) B4770839
theorem B2197583 : Blo 976593 2197583 := bstep (se 1 (by rfl) ⟨1648187, by rfl⟩ : syracuseStep 2197583 = 3296375) B3296375
theorem B2197979 : Blo 976593 2197979 := bstep (se 1 (by rfl) ⟨1648484, by rfl⟩ : syracuseStep 2197979 = 3296969) B3296969
theorem B7047881 : Blo 976593 7047881 := bstep (se 2 (by rfl) ⟨2642955, by rfl⟩ : syracuseStep 7047881 = 5285911) B5285911
theorem B3771089 : Blo 976593 3771089 := bstep (se 2 (by rfl) ⟨1414158, by rfl⟩ : syracuseStep 3771089 = 2828317) B2828317
theorem B3967811 : Blo 976593 3967811 := bstep (se 1 (by rfl) ⟨2975858, by rfl⟩ : syracuseStep 3967811 = 5951717) B5951717
theorem B2198447 : Blo 976593 2198447 := bstep (se 1 (by rfl) ⟨1648835, by rfl⟩ : syracuseStep 2198447 = 3297671) B3297671
theorem B1674247 : Blo 976593 1674247 := bstep (se 1 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 1674247 = 2511371) B2511371
theorem B2198699 : Blo 976593 2198699 := bstep (se 1 (by rfl) ⟨1649024, by rfl⟩ : syracuseStep 2198699 = 3298049) B3298049
theorem B4951691 : Blo 976593 4951691 := bstep (se 1 (by rfl) ⟨3713768, by rfl⟩ : syracuseStep 4951691 = 7427537) B7427537
theorem B2199239 : Blo 976593 2199239 := bstep (se 1 (by rfl) ⟨1649429, by rfl⟩ : syracuseStep 2199239 = 3298859) B3298859
theorem B2789063 : Blo 976593 2789063 := bstep (se 1 (by rfl) ⟨2091797, by rfl⟩ : syracuseStep 2789063 = 4183595) B4183595
theorem B3182611 : Blo 976593 3182611 := bstep (se 1 (by rfl) ⟨2386958, by rfl⟩ : syracuseStep 3182611 = 4773917) B4773917
theorem B1675343 : Blo 976593 1675343 := bstep (se 1 (by rfl) ⟨1256507, by rfl⟩ : syracuseStep 1675343 = 2513015) B2513015
theorem B11309219 : Blo 976593 11309219 := bstep (se 1 (by rfl) ⟨8481914, by rfl⟩ : syracuseStep 11309219 = 16963829) B16963829
theorem B2200103 : Blo 976593 2200103 := bstep (se 1 (by rfl) ⟨1650077, by rfl⟩ : syracuseStep 2200103 = 3300155) B3300155
theorem B6689465 : Blo 976593 6689465 := bstep (se 2 (by rfl) ⟨2508549, by rfl⟩ : syracuseStep 6689465 = 5017099) B5017099
theorem B53547875 : Blo 976593 53547875 := bstep (se 1 (by rfl) ⟨40160906, by rfl⟩ : syracuseStep 53547875 = 80321813) B80321813
theorem B2200427 : Blo 976593 2200427 := bstep (se 1 (by rfl) ⟨1650320, by rfl⟩ : syracuseStep 2200427 = 3300641) B3300641
theorem B2200481 : Blo 976593 2200481 := bstep (se 2 (by rfl) ⟨825180, by rfl⟩ : syracuseStep 2200481 = 1650361) B1650361
theorem B7443575 : Blo 976593 7443575 := bstep (se 1 (by rfl) ⟨5582681, by rfl⟩ : syracuseStep 7443575 = 11165363) B11165363
theorem B5805209 : Blo 976593 5805209 := bstep (se 2 (by rfl) ⟨2176953, by rfl⟩ : syracuseStep 5805209 = 4353907) B4353907
theorem B2200823 : Blo 976593 2200823 := bstep (se 1 (by rfl) ⟨1650617, by rfl⟩ : syracuseStep 2200823 = 3301235) B3301235
theorem B3577193 : Blo 976593 3577193 := bstep (se 2 (by rfl) ⟨1341447, by rfl⟩ : syracuseStep 3577193 = 2682895) B2682895
theorem B8033701 : Blo 976593 8033701 := bstep (se 4 (by rfl) ⟨753159, by rfl⟩ : syracuseStep 8033701 = 1506319) B1506319
theorem B2790875 : Blo 976593 2790875 := bstep (se 1 (by rfl) ⟨2093156, by rfl⟩ : syracuseStep 2790875 = 4186313) B4186313
theorem B3708605 : Blo 976593 3708605 := bstep (se 3 (by rfl) ⟨695363, by rfl⟩ : syracuseStep 3708605 = 1390727) B1390727
theorem B2201417 : Blo 976593 2201417 := bstep (se 2 (by rfl) ⟨825531, by rfl⟩ : syracuseStep 2201417 = 1651063) B1651063
theorem B3970889 : Blo 976593 3970889 := bstep (se 2 (by rfl) ⟨1489083, by rfl⟩ : syracuseStep 3970889 = 2978167) B2978167
theorem B2234375 : Blo 976593 2234375 := bstep (se 1 (by rfl) ⟨1675781, by rfl⟩ : syracuseStep 2234375 = 3351563) B3351563
theorem B9410903 : Blo 976593 9410903 := bstep (se 1 (by rfl) ⟨7058177, by rfl⟩ : syracuseStep 9410903 = 14116355) B14116355
theorem B2202209 : Blo 976593 2202209 := bstep (se 2 (by rfl) ⟨825828, by rfl⟩ : syracuseStep 2202209 = 1651657) B1651657
theorem B3349181 : Blo 976593 3349181 := bstep (se 3 (by rfl) ⟨627971, by rfl⟩ : syracuseStep 3349181 = 1255943) B1255943
theorem B11279249 : Blo 976593 11279249 := bstep (se 2 (by rfl) ⟨4229718, by rfl⟩ : syracuseStep 11279249 = 8459437) B8459437
theorem B2202551 : Blo 976593 2202551 := bstep (se 1 (by rfl) ⟨1651913, by rfl⟩ : syracuseStep 2202551 = 3303827) B3303827
theorem B3349561 : Blo 976593 3349561 := bstep (se 2 (by rfl) ⟨1256085, by rfl⟩ : syracuseStep 3349561 = 2512171) B2512171
theorem B3710033 : Blo 976593 3710033 := bstep (se 2 (by rfl) ⟨1391262, by rfl⟩ : syracuseStep 3710033 = 2782525) B2782525
theorem B2203145 : Blo 976593 2203145 := bstep (se 2 (by rfl) ⟨826179, by rfl⟩ : syracuseStep 2203145 = 1652359) B1652359
theorem B2203487 : Blo 976593 2203487 := bstep (se 1 (by rfl) ⟨1652615, by rfl⟩ : syracuseStep 2203487 = 3305231) B3305231
theorem B5021549 : Blo 976593 5021549 := bstep (se 3 (by rfl) ⟨941540, by rfl⟩ : syracuseStep 5021549 = 1883081) B1883081
theorem B10166147 : Blo 976593 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B4956065 : Blo 976593 4956065 := bstep (se 2 (by rfl) ⟨1858524, by rfl⟩ : syracuseStep 4956065 = 3717049) B3717049
theorem B2203667 : Blo 976593 2203667 := bstep (se 1 (by rfl) ⟨1652750, by rfl⟩ : syracuseStep 2203667 = 3305501) B3305501
theorem B2204009 : Blo 976593 2204009 := bstep (se 2 (by rfl) ⟨826503, by rfl⟩ : syracuseStep 2204009 = 1653007) B1653007
theorem B23241239 : Blo 976593 23241239 := bstep (se 1 (by rfl) ⟨17430929, by rfl⟩ : syracuseStep 23241239 = 34861859) B34861859
theorem B3711521 : Blo 976593 3711521 := bstep (se 2 (by rfl) ⟨1391820, by rfl⟩ : syracuseStep 3711521 = 2783641) B2783641
theorem B6267577 : Blo 976593 6267577 := bstep (se 2 (by rfl) ⟨2350341, by rfl⟩ : syracuseStep 6267577 = 4700683) B4700683
theorem B3711703 : Blo 976593 3711703 := bstep (se 1 (by rfl) ⟨2783777, by rfl⟩ : syracuseStep 3711703 = 5567555) B5567555
theorem B2204603 : Blo 976593 2204603 := bstep (se 1 (by rfl) ⟨1653452, by rfl⟩ : syracuseStep 2204603 = 3306905) B3306905
theorem B3712007 : Blo 976593 3712007 := bstep (se 1 (by rfl) ⟨2784005, by rfl⟩ : syracuseStep 3712007 = 5568011) B5568011
theorem B2204729 : Blo 976593 2204729 := bstep (se 2 (by rfl) ⟨826773, by rfl⟩ : syracuseStep 2204729 = 1653547) B1653547
theorem B2205071 : Blo 976593 2205071 := bstep (se 1 (by rfl) ⟨1653803, by rfl⟩ : syracuseStep 2205071 = 3307607) B3307607
theorem B35661221 : Blo 976593 35661221 := bstep (se 4 (by rfl) ⟨3343239, by rfl⟩ : syracuseStep 35661221 = 6686479) B6686479
theorem B3712493 : Blo 976593 3712493 := bstep (se 3 (by rfl) ⟨696092, by rfl⟩ : syracuseStep 3712493 = 1392185) B1392185
theorem B2205395 : Blo 976593 2205395 := bstep (se 1 (by rfl) ⟨1654046, by rfl⟩ : syracuseStep 2205395 = 3308093) B3308093
theorem B149038841 : Blo 976593 149038841 := bstep (se 2 (by rfl) ⟨55889565, by rfl⟩ : syracuseStep 149038841 = 111779131) B111779131
theorem B1648559 : Blo 976593 1648559 := bstep (se 1 (by rfl) ⟨1236419, by rfl⟩ : syracuseStep 1648559 = 2472839) B2472839
theorem B1648991 : Blo 976593 1648991 := bstep (se 1 (by rfl) ⟨1236743, by rfl⟩ : syracuseStep 1648991 = 2473487) B2473487
theorem B6695297 : Blo 976593 6695297 := bstep (se 2 (by rfl) ⟨2510736, by rfl⟩ : syracuseStep 6695297 = 5021473) B5021473
theorem B3713633 : Blo 976593 3713633 := bstep (se 2 (by rfl) ⟨1392612, by rfl⟩ : syracuseStep 3713633 = 2785225) B2785225
theorem B2206331 : Blo 976593 2206331 := bstep (se 1 (by rfl) ⟨1654748, by rfl⟩ : syracuseStep 2206331 = 3309497) B3309497
theorem B12724937 : Blo 976593 12724937 := bstep (se 2 (by rfl) ⟨4771851, by rfl⟩ : syracuseStep 12724937 = 9543703) B9543703
theorem B2861783 : Blo 976593 2861783 := bstep (se 1 (by rfl) ⟨2146337, by rfl⟩ : syracuseStep 2861783 = 4292675) B4292675
theorem B1649551 : Blo 976593 1649551 := bstep (se 1 (by rfl) ⟨1237163, by rfl⟩ : syracuseStep 1649551 = 2474327) B2474327
theorem B4074515 : Blo 976593 4074515 := bstep (se 1 (by rfl) ⟨3055886, by rfl⟩ : syracuseStep 4074515 = 6111773) B6111773
theorem B4173275 : Blo 976593 4173275 := bstep (se 1 (by rfl) ⟨3129956, by rfl⟩ : syracuseStep 4173275 = 6259913) B6259913
theorem B7417331 : Blo 976593 7417331 := bstep (se 1 (by rfl) ⟨5562998, by rfl⟩ : syracuseStep 7417331 = 11125997) B11125997
theorem B1650233 : Blo 976593 1650233 := bstep (se 2 (by rfl) ⟨618837, by rfl⟩ : syracuseStep 1650233 = 1237675) B1237675
theorem B3714619 : Blo 976593 3714619 := bstep (se 1 (by rfl) ⟨2785964, by rfl⟩ : syracuseStep 3714619 = 5571929) B5571929
theorem B10038923 : Blo 976593 10038923 := bstep (se 1 (by rfl) ⟨7529192, by rfl⟩ : syracuseStep 10038923 = 15058385) B15058385
theorem B28159811 : Blo 976593 28159811 := bstep (se 1 (by rfl) ⟨21119858, by rfl⟩ : syracuseStep 28159811 = 42239717) B42239717
theorem B3714923 : Blo 976593 3714923 := bstep (se 1 (by rfl) ⟨2786192, by rfl⟩ : syracuseStep 3714923 = 5572385) B5572385
theorem B5648237 : Blo 976593 5648237 := bstep (se 3 (by rfl) ⟨1059044, by rfl⟩ : syracuseStep 5648237 = 2118089) B2118089
theorem B3715091 : Blo 976593 3715091 := bstep (se 1 (by rfl) ⟨2786318, by rfl⟩ : syracuseStep 3715091 = 5572637) B5572637
theorem B1650935 : Blo 976593 1650935 := bstep (se 1 (by rfl) ⟨1238201, by rfl⟩ : syracuseStep 1650935 = 2476403) B2476403
theorem B7942553 : Blo 976593 7942553 := bstep (se 2 (by rfl) ⟨2978457, by rfl⟩ : syracuseStep 7942553 = 5956915) B5956915
theorem B10564121 : Blo 976593 10564121 := bstep (se 2 (by rfl) ⟨3961545, by rfl⟩ : syracuseStep 10564121 = 7923091) B7923091
theorem B1651279 : Blo 976593 1651279 := bstep (se 1 (by rfl) ⟨1238459, by rfl⟩ : syracuseStep 1651279 = 2476919) B2476919
theorem B1651529 : Blo 976593 1651529 := bstep (se 2 (by rfl) ⟨619323, by rfl⟩ : syracuseStep 1651529 = 1238647) B1238647
theorem B1651961 : Blo 976593 1651961 := bstep (se 2 (by rfl) ⟨619485, by rfl⟩ : syracuseStep 1651961 = 1238971) B1238971
theorem B1488233 : Blo 976593 1488233 := bstep (se 2 (by rfl) ⟨558087, by rfl⟩ : syracuseStep 1488233 = 1116175) B1116175
theorem B5584301 : Blo 976593 5584301 := bstep (se 3 (by rfl) ⟨1047056, by rfl⟩ : syracuseStep 5584301 = 2094113) B2094113
theorem B1652143 : Blo 976593 1652143 := bstep (se 1 (by rfl) ⟨1239107, by rfl⟩ : syracuseStep 1652143 = 2478215) B2478215
theorem B1652231 : Blo 976593 1652231 := bstep (se 1 (by rfl) ⟨1239173, by rfl⟩ : syracuseStep 1652231 = 2478347) B2478347
theorem B1652575 : Blo 976593 1652575 := bstep (se 1 (by rfl) ⟨1239431, by rfl⟩ : syracuseStep 1652575 = 2478863) B2478863
theorem B1324895 : Blo 976593 1324895 := bstep (se 1 (by rfl) ⟨993671, by rfl⟩ : syracuseStep 1324895 = 1987343) B1987343
theorem B1652663 : Blo 976593 1652663 := bstep (se 1 (by rfl) ⟨1239497, by rfl⟩ : syracuseStep 1652663 = 2478995) B2478995
theorem B4175803 : Blo 976593 4175803 := bstep (se 1 (by rfl) ⟨3131852, by rfl⟩ : syracuseStep 4175803 = 6263705) B6263705
theorem B7420247 : Blo 976593 7420247 := bstep (se 1 (by rfl) ⟨5565185, by rfl⟩ : syracuseStep 7420247 = 11130371) B11130371
theorem B1391023 : Blo 976593 1391023 := bstep (se 1 (by rfl) ⟨1043267, by rfl⟩ : syracuseStep 1391023 = 2086535) B2086535
theorem B1653257 : Blo 976593 1653257 := bstep (se 2 (by rfl) ⟨619971, by rfl⟩ : syracuseStep 1653257 = 1239943) B1239943
theorem B2472545 : Blo 976593 2472545 := bstep (se 2 (by rfl) ⟨927204, by rfl⟩ : syracuseStep 2472545 = 1854409) B1854409
theorem B1653419 : Blo 976593 1653419 := bstep (se 1 (by rfl) ⟨1240064, by rfl⟩ : syracuseStep 1653419 = 2480129) B2480129
theorem B3718007 : Blo 976593 3718007 := bstep (se 1 (by rfl) ⟨2788505, by rfl⟩ : syracuseStep 3718007 = 5577011) B5577011
theorem B1653817 : Blo 976593 1653817 := bstep (se 2 (by rfl) ⟨620181, by rfl⟩ : syracuseStep 1653817 = 1240363) B1240363
theorem B1653959 : Blo 976593 1653959 := bstep (se 1 (by rfl) ⟨1240469, by rfl⟩ : syracuseStep 1653959 = 2480939) B2480939
theorem B1654121 : Blo 976593 1654121 := bstep (se 2 (by rfl) ⟨620295, by rfl⟩ : syracuseStep 1654121 = 1240591) B1240591
theorem B3128701 : Blo 976593 3128701 := bstep (se 3 (by rfl) ⟨586631, by rfl⟩ : syracuseStep 3128701 = 1173263) B1173263
theorem B1654519 : Blo 976593 1654519 := bstep (se 1 (by rfl) ⟨1240889, by rfl⟩ : syracuseStep 1654519 = 2481779) B2481779
theorem B3718979 : Blo 976593 3718979 := bstep (se 1 (by rfl) ⟨2789234, by rfl⟩ : syracuseStep 3718979 = 5578469) B5578469
theorem B1982395 : Blo 976593 1982395 := bstep (se 1 (by rfl) ⟨1486796, by rfl⟩ : syracuseStep 1982395 = 2973593) B2973593
theorem B1654715 : Blo 976593 1654715 := bstep (se 1 (by rfl) ⟨1241036, by rfl⟩ : syracuseStep 1654715 = 2482073) B2482073
theorem B2474003 : Blo 976593 2474003 := bstep (se 1 (by rfl) ⟨1855502, by rfl⟩ : syracuseStep 2474003 = 3711005) B3711005
theorem B1982713 : Blo 976593 1982713 := bstep (se 2 (by rfl) ⟨743517, by rfl⟩ : syracuseStep 1982713 = 1487035) B1487035
theorem B2474459 : Blo 976593 2474459 := bstep (se 1 (by rfl) ⟨1855844, by rfl⟩ : syracuseStep 2474459 = 3711689) B3711689
theorem B22921751 : Blo 976593 22921751 := bstep (se 1 (by rfl) ⟨17191313, by rfl⟩ : syracuseStep 22921751 = 34382627) B34382627
theorem B4702931 : Blo 976593 4702931 := bstep (se 1 (by rfl) ⟨3527198, by rfl⟩ : syracuseStep 4702931 = 7054397) B7054397
theorem B3719965 : Blo 976593 3719965 := bstep (se 3 (by rfl) ⟨697493, by rfl⟩ : syracuseStep 3719965 = 1394987) B1394987
theorem B1885115 : Blo 976593 1885115 := bstep (se 1 (by rfl) ⟨1413836, by rfl⟩ : syracuseStep 1885115 = 2827673) B2827673
theorem B1098715 : Blo 976593 1098715 := bstep (se 1 (by rfl) ⟨824036, by rfl⟩ : syracuseStep 1098715 = 1648073) B1648073
theorem B11289619 : Blo 976593 11289619 := bstep (se 1 (by rfl) ⟨8467214, by rfl⟩ : syracuseStep 11289619 = 16934429) B16934429
theorem B1099183 : Blo 976593 1099183 := bstep (se 1 (by rfl) ⟨824387, by rfl⟩ : syracuseStep 1099183 = 1648775) B1648775
theorem B12699125 : Blo 976593 12699125 := bstep (se 5 (by rfl) ⟨595271, by rfl⟩ : syracuseStep 12699125 = 1190543) B1190543
theorem B3130919 : Blo 976593 3130919 := bstep (se 1 (by rfl) ⟨2348189, by rfl⟩ : syracuseStep 3130919 = 4696379) B4696379
theorem B12699179 : Blo 976593 12699179 := bstep (se 1 (by rfl) ⟨9524384, by rfl⟩ : syracuseStep 12699179 = 19048769) B19048769
theorem B2475643 : Blo 976593 2475643 := bstep (se 1 (by rfl) ⟨1856732, by rfl⟩ : syracuseStep 2475643 = 3713465) B3713465
theorem B12732203 : Blo 976593 12732203 := bstep (se 1 (by rfl) ⟨9549152, by rfl⟩ : syracuseStep 12732203 = 19098305) B19098305
theorem B1099615 : Blo 976593 1099615 := bstep (se 1 (by rfl) ⟨824711, by rfl⟩ : syracuseStep 1099615 = 1649423) B1649423
theorem B6277135 : Blo 976593 6277135 := bstep (se 1 (by rfl) ⟨4707851, by rfl⟩ : syracuseStep 6277135 = 9415703) B9415703
theorem B4180025 : Blo 976593 4180025 := bstep (se 2 (by rfl) ⟨1567509, by rfl⟩ : syracuseStep 4180025 = 3135019) B3135019
theorem B5949521 : Blo 976593 5949521 := bstep (se 2 (by rfl) ⟨2231070, by rfl⟩ : syracuseStep 5949521 = 4462141) B4462141
theorem B1099975 : Blo 976593 1099975 := bstep (se 1 (by rfl) ⟨824981, by rfl⟩ : syracuseStep 1099975 = 1649963) B1649963
theorem B3131777 : Blo 976593 3131777 := bstep (se 2 (by rfl) ⟨1174416, by rfl⟩ : syracuseStep 3131777 = 2348833) B2348833
theorem B36161977 : Blo 976593 36161977 := bstep (se 2 (by rfl) ⟨13560741, by rfl⟩ : syracuseStep 36161977 = 27121483) B27121483
theorem B7949011 : Blo 976593 7949011 := bstep (se 1 (by rfl) ⟨5961758, by rfl⟩ : syracuseStep 7949011 = 11923517) B11923517
theorem B1100839 : Blo 976593 1100839 := bstep (se 1 (by rfl) ⟨825629, by rfl⟩ : syracuseStep 1100839 = 1651259) B1651259
theorem B13389047 : Blo 976593 13389047 := bstep (se 1 (by rfl) ⟨10041785, by rfl⟩ : syracuseStep 13389047 = 20083571) B20083571
theorem B1854713 : Blo 976593 1854713 := bstep (se 2 (by rfl) ⟨695517, by rfl⟩ : syracuseStep 1854713 = 1391035) B1391035
theorem B1789327 : Blo 976593 1789327 := bstep (se 1 (by rfl) ⟨1341995, by rfl⟩ : syracuseStep 1789327 = 2683991) B2683991
theorem B1854895 : Blo 976593 1854895 := bstep (se 1 (by rfl) ⟨1391171, by rfl⟩ : syracuseStep 1854895 = 2782343) B2782343
theorem B3296807 : Blo 976593 3296807 := bstep (se 1 (by rfl) ⟨2472605, by rfl⟩ : syracuseStep 3296807 = 4945211) B4945211
theorem B1855055 : Blo 976593 1855055 := bstep (se 1 (by rfl) ⟨1391291, by rfl⟩ : syracuseStep 1855055 = 2782583) B2782583
theorem B24104567 : Blo 976593 24104567 := bstep (se 1 (by rfl) ⟨18078425, by rfl⟩ : syracuseStep 24104567 = 36156851) B36156851
theorem B3296915 : Blo 976593 3296915 := bstep (se 1 (by rfl) ⟨2472686, by rfl⟩ : syracuseStep 3296915 = 4945373) B4945373
theorem B26758835 : Blo 976593 26758835 := bstep (se 1 (by rfl) ⟨20069126, by rfl⟩ : syracuseStep 26758835 = 40138253) B40138253
theorem B3297131 : Blo 976593 3297131 := bstep (se 1 (by rfl) ⟨2472848, by rfl⟩ : syracuseStep 3297131 = 4945697) B4945697
theorem B3526507 : Blo 976593 3526507 := bstep (se 1 (by rfl) ⟨2644880, by rfl⟩ : syracuseStep 3526507 = 5289761) B5289761
theorem B3297185 : Blo 976593 3297185 := bstep (se 2 (by rfl) ⟨1236444, by rfl⟩ : syracuseStep 3297185 = 2472889) B2472889
theorem B4182023 : Blo 976593 4182023 := bstep (se 1 (by rfl) ⟨3136517, by rfl⟩ : syracuseStep 4182023 = 6273035) B6273035
theorem B11128913 : Blo 976593 11128913 := bstep (se 2 (by rfl) ⟨4173342, by rfl⟩ : syracuseStep 11128913 = 8346685) B8346685
theorem B3133687 : Blo 976593 3133687 := bstep (se 1 (by rfl) ⟨2350265, by rfl⟩ : syracuseStep 3133687 = 4700531) B4700531
theorem B8147249 : Blo 976593 8147249 := bstep (se 2 (by rfl) ⟨3055218, by rfl⟩ : syracuseStep 8147249 = 6110437) B6110437
theorem B3297779 : Blo 976593 3297779 := bstep (se 1 (by rfl) ⟨2473334, by rfl⟩ : syracuseStep 3297779 = 4946669) B4946669
theorem B1102459 : Blo 976593 1102459 := bstep (se 1 (by rfl) ⟨826844, by rfl⟩ : syracuseStep 1102459 = 1653689) B1653689
theorem B1856171 : Blo 976593 1856171 := bstep (se 1 (by rfl) ⟨1392128, by rfl⟩ : syracuseStep 1856171 = 2784257) B2784257
theorem B3298319 : Blo 976593 3298319 := bstep (se 1 (by rfl) ⟨2473739, by rfl⟩ : syracuseStep 3298319 = 4947479) B4947479
theorem B4019279 : Blo 976593 4019279 := bstep (se 1 (by rfl) ⟨3014459, by rfl⟩ : syracuseStep 4019279 = 6028919) B6028919
theorem B1102927 : Blo 976593 1102927 := bstep (se 1 (by rfl) ⟨827195, by rfl⟩ : syracuseStep 1102927 = 1654391) B1654391
theorem B3527833 : Blo 976593 3527833 := bstep (se 2 (by rfl) ⟨1322937, by rfl⟩ : syracuseStep 3527833 = 2645875) B2645875
theorem B3134621 : Blo 976593 3134621 := bstep (se 3 (by rfl) ⟨587741, by rfl⟩ : syracuseStep 3134621 = 1175483) B1175483
theorem B2643443 : Blo 976593 2643443 := bstep (se 1 (by rfl) ⟨1982582, by rfl⟩ : syracuseStep 2643443 = 3965165) B3965165
theorem B3298913 : Blo 976593 3298913 := bstep (se 2 (by rfl) ⟨1237092, by rfl⟩ : syracuseStep 3298913 = 2474185) B2474185
theorem B2479967 : Blo 976593 2479967 := bstep (se 1 (by rfl) ⟨1859975, by rfl⟩ : syracuseStep 2479967 = 3719951) B3719951
theorem B2086843 : Blo 976593 2086843 := bstep (se 1 (by rfl) ⟨1565132, by rfl⟩ : syracuseStep 2086843 = 3130265) B3130265
theorem B3528785 : Blo 976593 3528785 := bstep (se 2 (by rfl) ⟨1323294, by rfl⟩ : syracuseStep 3528785 = 2646589) B2646589
theorem B11163905 : Blo 976593 11163905 := bstep (se 2 (by rfl) ⟨4186464, by rfl⟩ : syracuseStep 11163905 = 8372929) B8372929
theorem B1857887 : Blo 976593 1857887 := bstep (se 1 (by rfl) ⟨1393415, by rfl⟩ : syracuseStep 1857887 = 2786831) B2786831
theorem B2480665 : Blo 976593 2480665 := bstep (se 2 (by rfl) ⟨930249, by rfl⟩ : syracuseStep 2480665 = 1860499) B1860499
theorem B1464911 : Blo 976593 1464911 := bstep (se 1 (by rfl) ⟨1098683, by rfl⟩ : syracuseStep 1464911 = 2197367) B2197367
theorem B2644577 : Blo 976593 2644577 := bstep (se 2 (by rfl) ⟨991716, by rfl⟩ : syracuseStep 2644577 = 1983433) B1983433
theorem B1465031 : Blo 976593 1465031 := bstep (se 1 (by rfl) ⟨1098773, by rfl⟩ : syracuseStep 1465031 = 2197547) B2197547
theorem B1858297 : Blo 976593 1858297 := bstep (se 2 (by rfl) ⟨696861, by rfl⟩ : syracuseStep 1858297 = 1393723) B1393723
theorem B3136249 : Blo 976593 3136249 := bstep (se 2 (by rfl) ⟨1176093, by rfl⟩ : syracuseStep 3136249 = 2352187) B2352187
theorem B2480969 : Blo 976593 2480969 := bstep (se 2 (by rfl) ⟨930363, by rfl⟩ : syracuseStep 2480969 = 1860727) B1860727
theorem B1760105 : Blo 976593 1760105 := bstep (se 2 (by rfl) ⟨660039, by rfl⟩ : syracuseStep 1760105 = 1320079) B1320079
theorem B1465193 : Blo 976593 1465193 := bstep (se 2 (by rfl) ⟨549447, by rfl⟩ : syracuseStep 1465193 = 1098895) B1098895
theorem B1465271 : Blo 976593 1465271 := bstep (se 1 (by rfl) ⟨1098953, by rfl⟩ : syracuseStep 1465271 = 2197907) B2197907
theorem B1465307 : Blo 976593 1465307 := bstep (se 1 (by rfl) ⟨1098980, by rfl⟩ : syracuseStep 1465307 = 2197961) B2197961
theorem B7527397 : Blo 976593 7527397 := bstep (se 4 (by rfl) ⟨705693, by rfl⟩ : syracuseStep 7527397 = 1411387) B1411387
theorem B13589477 : Blo 976593 13589477 := bstep (se 4 (by rfl) ⟨1274013, by rfl⟩ : syracuseStep 13589477 = 2548027) B2548027
theorem B3300371 : Blo 976593 3300371 := bstep (se 1 (by rfl) ⟨2475278, by rfl⟩ : syracuseStep 3300371 = 4950557) B4950557
theorem B11885611 : Blo 976593 11885611 := bstep (se 1 (by rfl) ⟨8914208, by rfl⟩ : syracuseStep 11885611 = 17828417) B17828417
theorem B1858639 : Blo 976593 1858639 := bstep (se 1 (by rfl) ⟨1393979, by rfl⟩ : syracuseStep 1858639 = 2787959) B2787959
theorem B2513999 : Blo 976593 2513999 := bstep (se 1 (by rfl) ⟨1885499, by rfl⟩ : syracuseStep 2513999 = 3770999) B3770999
theorem B32136323 : Blo 976593 32136323 := bstep (se 1 (by rfl) ⟨24102242, by rfl⟩ : syracuseStep 32136323 = 48204485) B48204485
theorem B2088107 : Blo 976593 2088107 := bstep (se 1 (by rfl) ⟨1566080, by rfl⟩ : syracuseStep 2088107 = 3132161) B3132161
theorem B1858889 : Blo 976593 1858889 := bstep (se 2 (by rfl) ⟨697083, by rfl⟩ : syracuseStep 1858889 = 1394167) B1394167
theorem B3300695 : Blo 976593 3300695 := bstep (se 1 (by rfl) ⟨2475521, by rfl⟩ : syracuseStep 3300695 = 4951043) B4951043
theorem B10575193 : Blo 976593 10575193 := bstep (se 2 (by rfl) ⟨3965697, by rfl⟩ : syracuseStep 10575193 = 7931395) B7931395
theorem B1465775 : Blo 976593 1465775 := bstep (se 1 (by rfl) ⟨1099331, by rfl⟩ : syracuseStep 1465775 = 2198663) B2198663
theorem B1465865 : Blo 976593 1465865 := bstep (se 2 (by rfl) ⟨549699, by rfl⟩ : syracuseStep 1465865 = 1099399) B1099399
theorem B1465895 : Blo 976593 1465895 := bstep (se 1 (by rfl) ⟨1099421, by rfl⟩ : syracuseStep 1465895 = 2198843) B2198843
theorem B4709927 : Blo 976593 4709927 := bstep (se 1 (by rfl) ⟨3532445, by rfl⟩ : syracuseStep 4709927 = 7064891) B7064891
theorem B5299751 : Blo 976593 5299751 := bstep (se 1 (by rfl) ⟨3974813, by rfl⟩ : syracuseStep 5299751 = 7949627) B7949627
theorem B1465979 : Blo 976593 1465979 := bstep (se 1 (by rfl) ⟨1099484, by rfl⟩ : syracuseStep 1465979 = 2198969) B2198969
theorem B2645693 : Blo 976593 2645693 := bstep (se 3 (by rfl) ⟨496067, by rfl⟩ : syracuseStep 2645693 = 992135) B992135
theorem B3530429 : Blo 976593 3530429 := bstep (se 3 (by rfl) ⟨661955, by rfl⟩ : syracuseStep 3530429 = 1323911) B1323911
theorem B1466105 : Blo 976593 1466105 := bstep (se 2 (by rfl) ⟨549789, by rfl⟩ : syracuseStep 1466105 = 1099579) B1099579
theorem B5562179 : Blo 976593 5562179 := bstep (se 1 (by rfl) ⟨4171634, by rfl⟩ : syracuseStep 5562179 = 8343269) B8343269
theorem B1466207 : Blo 976593 1466207 := bstep (se 1 (by rfl) ⟨1099655, by rfl⟩ : syracuseStep 1466207 = 2199311) B2199311
theorem B1466219 : Blo 976593 1466219 := bstep (se 1 (by rfl) ⟨1099664, by rfl⟩ : syracuseStep 1466219 = 2199329) B2199329
theorem B2482103 : Blo 976593 2482103 := bstep (se 1 (by rfl) ⟨1861577, by rfl⟩ : syracuseStep 2482103 = 3723155) B3723155
theorem B15065149 : Blo 976593 15065149 := bstep (se 3 (by rfl) ⟨2824715, by rfl⟩ : syracuseStep 15065149 = 5649431) B5649431
theorem B1466447 : Blo 976593 1466447 := bstep (se 1 (by rfl) ⟨1099835, by rfl⟩ : syracuseStep 1466447 = 2199671) B2199671
theorem B1859755 : Blo 976593 1859755 := bstep (se 1 (by rfl) ⟨1394816, by rfl⟩ : syracuseStep 1859755 = 2789633) B2789633
theorem B1466567 : Blo 976593 1466567 := bstep (se 1 (by rfl) ⟨1099925, by rfl⟩ : syracuseStep 1466567 = 2199851) B2199851
theorem B1859831 : Blo 976593 1859831 := bstep (se 1 (by rfl) ⟨1394873, by rfl⟩ : syracuseStep 1859831 = 2789747) B2789747
theorem B1466729 : Blo 976593 1466729 := bstep (se 2 (by rfl) ⟨550023, by rfl⟩ : syracuseStep 1466729 = 1100047) B1100047
theorem B3301775 : Blo 976593 3301775 := bstep (se 1 (by rfl) ⟨2476331, by rfl⟩ : syracuseStep 3301775 = 4952663) B4952663
theorem B1761697 : Blo 976593 1761697 := bstep (se 2 (by rfl) ⟨660636, by rfl⟩ : syracuseStep 1761697 = 1321273) B1321273
theorem B1466807 : Blo 976593 1466807 := bstep (se 1 (by rfl) ⟨1100105, by rfl⟩ : syracuseStep 1466807 = 2200211) B2200211
theorem B1466843 : Blo 976593 1466843 := bstep (se 1 (by rfl) ⟨1100132, by rfl⟩ : syracuseStep 1466843 = 2200265) B2200265
theorem B1860059 : Blo 976593 1860059 := bstep (se 1 (by rfl) ⟨1395044, by rfl⟩ : syracuseStep 1860059 = 2790089) B2790089
theorem B3302099 : Blo 976593 3302099 := bstep (se 1 (by rfl) ⟨2476574, by rfl⟩ : syracuseStep 3302099 = 4953149) B4953149
theorem B1467311 : Blo 976593 1467311 := bstep (se 1 (by rfl) ⟨1100483, by rfl⟩ : syracuseStep 1467311 = 2200967) B2200967
theorem B1237943 : Blo 976593 1237943 := bstep (se 1 (by rfl) ⟨928457, by rfl⟩ : syracuseStep 1237943 = 1856915) B1856915
theorem B1467401 : Blo 976593 1467401 := bstep (se 2 (by rfl) ⟨550275, by rfl⟩ : syracuseStep 1467401 = 1100551) B1100551
theorem B1467431 : Blo 976593 1467431 := bstep (se 1 (by rfl) ⟨1100573, by rfl⟩ : syracuseStep 1467431 = 2201147) B2201147
theorem B4023353 : Blo 976593 4023353 := bstep (se 2 (by rfl) ⟨1508757, by rfl⟩ : syracuseStep 4023353 = 3017515) B3017515
theorem B1238095 : Blo 976593 1238095 := bstep (se 1 (by rfl) ⟨928571, by rfl⟩ : syracuseStep 1238095 = 1857143) B1857143
theorem B1467515 : Blo 976593 1467515 := bstep (se 1 (by rfl) ⟨1100636, by rfl⟩ : syracuseStep 1467515 = 2201273) B2201273
theorem B3531971 : Blo 976593 3531971 := bstep (se 1 (by rfl) ⟨2648978, by rfl⟩ : syracuseStep 3531971 = 5297957) B5297957
theorem B18801881 : Blo 976593 18801881 := bstep (se 2 (by rfl) ⟨7050705, by rfl⟩ : syracuseStep 18801881 = 14101411) B14101411
theorem B1467641 : Blo 976593 1467641 := bstep (se 2 (by rfl) ⟨550365, by rfl⟩ : syracuseStep 1467641 = 1100731) B1100731
theorem B1467743 : Blo 976593 1467743 := bstep (se 1 (by rfl) ⟨1100807, by rfl⟩ : syracuseStep 1467743 = 2201615) B2201615
theorem B1467755 : Blo 976593 1467755 := bstep (se 1 (by rfl) ⟨1100816, by rfl⟩ : syracuseStep 1467755 = 2201633) B2201633
theorem B3171803 : Blo 976593 3171803 := bstep (se 1 (by rfl) ⟨2378852, by rfl⟩ : syracuseStep 3171803 = 4757705) B4757705
theorem B1467983 : Blo 976593 1467983 := bstep (se 1 (by rfl) ⟨1100987, by rfl⟩ : syracuseStep 1467983 = 2201975) B2201975
theorem B2647649 : Blo 976593 2647649 := bstep (se 2 (by rfl) ⟨992868, by rfl⟩ : syracuseStep 2647649 = 1985737) B1985737
theorem B1468103 : Blo 976593 1468103 := bstep (se 1 (by rfl) ⟨1101077, by rfl⟩ : syracuseStep 1468103 = 2202155) B2202155
theorem B1861319 : Blo 976593 1861319 := bstep (se 1 (by rfl) ⟨1395989, by rfl⟩ : syracuseStep 1861319 = 2791979) B2791979
theorem B2352851 : Blo 976593 2352851 := bstep (se 1 (by rfl) ⟨1764638, by rfl⟩ : syracuseStep 2352851 = 3529277) B3529277
theorem B976603 : Blo 976593 976603 := bstep (se 1 (by rfl) ⟨732452, by rfl⟩ : syracuseStep 976603 = 1464905) B1464905
theorem B976679 : Blo 976593 976679 := bstep (se 1 (by rfl) ⟨732509, by rfl⟩ : syracuseStep 976679 = 1465019) B1465019
theorem B976719 : Blo 976593 976719 := bstep (se 1 (by rfl) ⟨732539, by rfl⟩ : syracuseStep 976719 = 1465079) B1465079
theorem B976735 : Blo 976593 976735 := bstep (se 1 (by rfl) ⟨732551, by rfl⟩ : syracuseStep 976735 = 1465103) B1465103
theorem B1861471 : Blo 976593 1861471 := bstep (se 1 (by rfl) ⟨1396103, by rfl⟩ : syracuseStep 1861471 = 2792207) B2792207
theorem B1468265 : Blo 976593 1468265 := bstep (se 2 (by rfl) ⟨550599, by rfl⟩ : syracuseStep 1468265 = 1101199) B1101199
theorem B3303287 : Blo 976593 3303287 := bstep (se 1 (by rfl) ⟨2477465, by rfl⟩ : syracuseStep 3303287 = 4954931) B4954931
theorem B976763 : Blo 976593 976763 := bstep (se 1 (by rfl) ⟨732572, by rfl⟩ : syracuseStep 976763 = 1465145) B1465145
theorem B5564321 : Blo 976593 5564321 := bstep (se 2 (by rfl) ⟨2086620, by rfl⟩ : syracuseStep 5564321 = 4173241) B4173241
theorem B2090927 : Blo 976593 2090927 := bstep (se 1 (by rfl) ⟨1568195, by rfl⟩ : syracuseStep 2090927 = 3136391) B3136391
theorem B976815 : Blo 976593 976815 := bstep (se 1 (by rfl) ⟨732611, by rfl⟩ : syracuseStep 976815 = 1465223) B1465223
theorem B2385839 : Blo 976593 2385839 := bstep (se 1 (by rfl) ⟨1789379, by rfl⟩ : syracuseStep 2385839 = 3578759) B3578759
theorem B1468343 : Blo 976593 1468343 := bstep (se 1 (by rfl) ⟨1101257, by rfl⟩ : syracuseStep 1468343 = 2202515) B2202515
theorem B976839 : Blo 976593 976839 := bstep (se 1 (by rfl) ⟨732629, by rfl⟩ : syracuseStep 976839 = 1465259) B1465259
theorem B976859 : Blo 976593 976859 := bstep (se 1 (by rfl) ⟨732644, by rfl⟩ : syracuseStep 976859 = 1465289) B1465289
theorem B1468379 : Blo 976593 1468379 := bstep (se 1 (by rfl) ⟨1101284, by rfl⟩ : syracuseStep 1468379 = 2202569) B2202569
theorem B976935 : Blo 976593 976935 := bstep (se 1 (by rfl) ⟨732701, by rfl⟩ : syracuseStep 976935 = 1465403) B1465403
theorem B976975 : Blo 976593 976975 := bstep (se 1 (by rfl) ⟨732731, by rfl⟩ : syracuseStep 976975 = 1465463) B1465463
theorem B3303503 : Blo 976593 3303503 := bstep (se 1 (by rfl) ⟨2477627, by rfl⟩ : syracuseStep 3303503 = 4955255) B4955255
theorem B976991 : Blo 976593 976991 := bstep (se 1 (by rfl) ⟨732743, by rfl⟩ : syracuseStep 976991 = 1465487) B1465487
theorem B977019 : Blo 976593 977019 := bstep (se 1 (by rfl) ⟨732764, by rfl⟩ : syracuseStep 977019 = 1465529) B1465529
theorem B977071 : Blo 976593 977071 := bstep (se 1 (by rfl) ⟨732803, by rfl⟩ : syracuseStep 977071 = 1465607) B1465607
theorem B977095 : Blo 976593 977095 := bstep (se 1 (by rfl) ⟨732821, by rfl⟩ : syracuseStep 977095 = 1465643) B1465643
theorem B1239239 : Blo 976593 1239239 := bstep (se 1 (by rfl) ⟨929429, by rfl⟩ : syracuseStep 1239239 = 1858859) B1858859
theorem B977115 : Blo 976593 977115 := bstep (se 1 (by rfl) ⟨732836, by rfl⟩ : syracuseStep 977115 = 1465673) B1465673
theorem B977191 : Blo 976593 977191 := bstep (se 1 (by rfl) ⟨732893, by rfl⟩ : syracuseStep 977191 = 1465787) B1465787
theorem B977231 : Blo 976593 977231 := bstep (se 1 (by rfl) ⟨732923, by rfl⟩ : syracuseStep 977231 = 1465847) B1465847
theorem B977247 : Blo 976593 977247 := bstep (se 1 (by rfl) ⟨732935, by rfl⟩ : syracuseStep 977247 = 1465871) B1465871
theorem B1239391 : Blo 976593 1239391 := bstep (se 1 (by rfl) ⟨929543, by rfl⟩ : syracuseStep 1239391 = 1859087) B1859087
theorem B977275 : Blo 976593 977275 := bstep (se 1 (by rfl) ⟨732956, by rfl⟩ : syracuseStep 977275 = 1465913) B1465913
theorem B977327 : Blo 976593 977327 := bstep (se 1 (by rfl) ⟨732995, by rfl⟩ : syracuseStep 977327 = 1465991) B1465991
theorem B1468847 : Blo 976593 1468847 := bstep (se 1 (by rfl) ⟨1101635, by rfl⟩ : syracuseStep 1468847 = 2203271) B2203271
theorem B977351 : Blo 976593 977351 := bstep (se 1 (by rfl) ⟨733013, by rfl⟩ : syracuseStep 977351 = 1466027) B1466027
theorem B3303881 : Blo 976593 3303881 := bstep (se 2 (by rfl) ⟨1238955, by rfl⟩ : syracuseStep 3303881 = 2477911) B2477911
theorem B977371 : Blo 976593 977371 := bstep (se 1 (by rfl) ⟨733028, by rfl⟩ : syracuseStep 977371 = 1466057) B1466057
theorem B1468937 : Blo 976593 1468937 := bstep (se 2 (by rfl) ⟨550851, by rfl⟩ : syracuseStep 1468937 = 1101703) B1101703
theorem B977447 : Blo 976593 977447 := bstep (se 1 (by rfl) ⟨733085, by rfl⟩ : syracuseStep 977447 = 1466171) B1466171
theorem B1468967 : Blo 976593 1468967 := bstep (se 1 (by rfl) ⟨1101725, by rfl⟩ : syracuseStep 1468967 = 2203451) B2203451
theorem B977487 : Blo 976593 977487 := bstep (se 1 (by rfl) ⟨733115, by rfl⟩ : syracuseStep 977487 = 1466231) B1466231
theorem B977503 : Blo 976593 977503 := bstep (se 1 (by rfl) ⟨733127, by rfl⟩ : syracuseStep 977503 = 1466255) B1466255
theorem B977531 : Blo 976593 977531 := bstep (se 1 (by rfl) ⟨733148, by rfl⟩ : syracuseStep 977531 = 1466297) B1466297
theorem B1469051 : Blo 976593 1469051 := bstep (se 1 (by rfl) ⟨1101788, by rfl⟩ : syracuseStep 1469051 = 2203577) B2203577
theorem B977583 : Blo 976593 977583 := bstep (se 1 (by rfl) ⟨733187, by rfl⟩ : syracuseStep 977583 = 1466375) B1466375
theorem B977607 : Blo 976593 977607 := bstep (se 1 (by rfl) ⟨733205, by rfl⟩ : syracuseStep 977607 = 1466411) B1466411
theorem B3304151 : Blo 976593 3304151 := bstep (se 1 (by rfl) ⟨2478113, by rfl⟩ : syracuseStep 3304151 = 4956227) B4956227
theorem B977627 : Blo 976593 977627 := bstep (se 1 (by rfl) ⟨733220, by rfl⟩ : syracuseStep 977627 = 1466441) B1466441
theorem B1469177 : Blo 976593 1469177 := bstep (se 2 (by rfl) ⟨550941, by rfl⟩ : syracuseStep 1469177 = 1101883) B1101883
theorem B977703 : Blo 976593 977703 := bstep (se 1 (by rfl) ⟨733277, by rfl⟩ : syracuseStep 977703 = 1466555) B1466555
theorem B977743 : Blo 976593 977743 := bstep (se 1 (by rfl) ⟨733307, by rfl⟩ : syracuseStep 977743 = 1466615) B1466615
theorem B977759 : Blo 976593 977759 := bstep (se 1 (by rfl) ⟨733319, by rfl⟩ : syracuseStep 977759 = 1466639) B1466639
theorem B1469279 : Blo 976593 1469279 := bstep (se 1 (by rfl) ⟨1101959, by rfl⟩ : syracuseStep 1469279 = 2203919) B2203919
theorem B1469291 : Blo 976593 1469291 := bstep (se 1 (by rfl) ⟨1101968, by rfl⟩ : syracuseStep 1469291 = 2203937) B2203937
theorem B977787 : Blo 976593 977787 := bstep (se 1 (by rfl) ⟨733340, by rfl⟩ : syracuseStep 977787 = 1466681) B1466681
theorem B1567631 : Blo 976593 1567631 := bstep (se 1 (by rfl) ⟨1175723, by rfl⟩ : syracuseStep 1567631 = 2351447) B2351447
theorem B977839 : Blo 976593 977839 := bstep (se 1 (by rfl) ⟨733379, by rfl⟩ : syracuseStep 977839 = 1466759) B1466759
theorem B3304367 : Blo 976593 3304367 := bstep (se 1 (by rfl) ⟨2478275, by rfl⟩ : syracuseStep 3304367 = 4956551) B4956551
theorem B977863 : Blo 976593 977863 := bstep (se 1 (by rfl) ⟨733397, by rfl⟩ : syracuseStep 977863 = 1466795) B1466795
theorem B977883 : Blo 976593 977883 := bstep (se 1 (by rfl) ⟨733412, by rfl⟩ : syracuseStep 977883 = 1466825) B1466825
theorem B3533831 : Blo 976593 3533831 := bstep (se 1 (by rfl) ⟨2650373, by rfl⟩ : syracuseStep 3533831 = 5300747) B5300747
theorem B977959 : Blo 976593 977959 := bstep (se 1 (by rfl) ⟨733469, by rfl⟩ : syracuseStep 977959 = 1466939) B1466939
theorem B977999 : Blo 976593 977999 := bstep (se 1 (by rfl) ⟨733499, by rfl⟩ : syracuseStep 977999 = 1466999) B1466999
theorem B1469519 : Blo 976593 1469519 := bstep (se 1 (by rfl) ⟨1102139, by rfl⟩ : syracuseStep 1469519 = 2204279) B2204279
theorem B978015 : Blo 976593 978015 := bstep (se 1 (by rfl) ⟨733511, by rfl⟩ : syracuseStep 978015 = 1467023) B1467023
theorem B978043 : Blo 976593 978043 := bstep (se 1 (by rfl) ⟨733532, by rfl⟩ : syracuseStep 978043 = 1467065) B1467065
theorem B7433369 : Blo 976593 7433369 := bstep (se 2 (by rfl) ⟨2787513, by rfl⟩ : syracuseStep 7433369 = 5575027) B5575027
theorem B978095 : Blo 976593 978095 := bstep (se 1 (by rfl) ⟨733571, by rfl⟩ : syracuseStep 978095 = 1467143) B1467143
theorem B978119 : Blo 976593 978119 := bstep (se 1 (by rfl) ⟨733589, by rfl⟩ : syracuseStep 978119 = 1467179) B1467179
theorem B1764551 : Blo 976593 1764551 := bstep (se 1 (by rfl) ⟨1323413, by rfl⟩ : syracuseStep 1764551 = 2646827) B2646827
theorem B1469639 : Blo 976593 1469639 := bstep (se 1 (by rfl) ⟨1102229, by rfl⟩ : syracuseStep 1469639 = 2204459) B2204459
theorem B978139 : Blo 976593 978139 := bstep (se 1 (by rfl) ⟨733604, by rfl⟩ : syracuseStep 978139 = 1467209) B1467209
theorem B978215 : Blo 976593 978215 := bstep (se 1 (by rfl) ⟨733661, by rfl⟩ : syracuseStep 978215 = 1467323) B1467323
theorem B978255 : Blo 976593 978255 := bstep (se 1 (by rfl) ⟨733691, by rfl⟩ : syracuseStep 978255 = 1467383) B1467383
theorem B978271 : Blo 976593 978271 := bstep (se 1 (by rfl) ⟨733703, by rfl⟩ : syracuseStep 978271 = 1467407) B1467407
theorem B1469801 : Blo 976593 1469801 := bstep (se 2 (by rfl) ⟨551175, by rfl⟩ : syracuseStep 1469801 = 1102351) B1102351
theorem B978299 : Blo 976593 978299 := bstep (se 1 (by rfl) ⟨733724, by rfl⟩ : syracuseStep 978299 = 1467449) B1467449
theorem B978351 : Blo 976593 978351 := bstep (se 1 (by rfl) ⟨733763, by rfl⟩ : syracuseStep 978351 = 1467527) B1467527
theorem B1469879 : Blo 976593 1469879 := bstep (se 1 (by rfl) ⟨1102409, by rfl⟩ : syracuseStep 1469879 = 2204819) B2204819
theorem B978375 : Blo 976593 978375 := bstep (se 1 (by rfl) ⟨733781, by rfl⟩ : syracuseStep 978375 = 1467563) B1467563
theorem B978395 : Blo 976593 978395 := bstep (se 1 (by rfl) ⟨733796, by rfl⟩ : syracuseStep 978395 = 1467593) B1467593
theorem B1469915 : Blo 976593 1469915 := bstep (se 1 (by rfl) ⟨1102436, by rfl⟩ : syracuseStep 1469915 = 2204873) B2204873
theorem B978471 : Blo 976593 978471 := bstep (se 1 (by rfl) ⟨733853, by rfl⟩ : syracuseStep 978471 = 1467707) B1467707
theorem B978511 : Blo 976593 978511 := bstep (se 1 (by rfl) ⟨733883, by rfl⟩ : syracuseStep 978511 = 1467767) B1467767
theorem B26766935 : Blo 976593 26766935 := bstep (se 1 (by rfl) ⟨20075201, by rfl⟩ : syracuseStep 26766935 = 40150403) B40150403
theorem B978527 : Blo 976593 978527 := bstep (se 1 (by rfl) ⟨733895, by rfl⟩ : syracuseStep 978527 = 1467791) B1467791
theorem B978555 : Blo 976593 978555 := bstep (se 1 (by rfl) ⟨733916, by rfl⟩ : syracuseStep 978555 = 1467833) B1467833
theorem B5566097 : Blo 976593 5566097 := bstep (se 2 (by rfl) ⟨2087286, by rfl⟩ : syracuseStep 5566097 = 4174573) B4174573
theorem B978607 : Blo 976593 978607 := bstep (se 1 (by rfl) ⟨733955, by rfl⟩ : syracuseStep 978607 = 1467911) B1467911
theorem B978631 : Blo 976593 978631 := bstep (se 1 (by rfl) ⟨733973, by rfl⟩ : syracuseStep 978631 = 1467947) B1467947
theorem B978651 : Blo 976593 978651 := bstep (se 1 (by rfl) ⟨733988, by rfl⟩ : syracuseStep 978651 = 1467977) B1467977
theorem B978727 : Blo 976593 978727 := bstep (se 1 (by rfl) ⟨734045, by rfl⟩ : syracuseStep 978727 = 1468091) B1468091
theorem B978767 : Blo 976593 978767 := bstep (se 1 (by rfl) ⟨734075, by rfl⟩ : syracuseStep 978767 = 1468151) B1468151
theorem B978783 : Blo 976593 978783 := bstep (se 1 (by rfl) ⟨734087, by rfl⟩ : syracuseStep 978783 = 1468175) B1468175
theorem B978811 : Blo 976593 978811 := bstep (se 1 (by rfl) ⟨734108, by rfl⟩ : syracuseStep 978811 = 1468217) B1468217
theorem B978863 : Blo 976593 978863 := bstep (se 1 (by rfl) ⟨734147, by rfl⟩ : syracuseStep 978863 = 1468295) B1468295
theorem B2355119 : Blo 976593 2355119 := bstep (se 1 (by rfl) ⟨1766339, by rfl⟩ : syracuseStep 2355119 = 3532679) B3532679
theorem B1470383 : Blo 976593 1470383 := bstep (se 1 (by rfl) ⟨1102787, by rfl⟩ : syracuseStep 1470383 = 2205575) B2205575
theorem B978887 : Blo 976593 978887 := bstep (se 1 (by rfl) ⟨734165, by rfl⟩ : syracuseStep 978887 = 1468331) B1468331
theorem B978907 : Blo 976593 978907 := bstep (se 1 (by rfl) ⟨734180, by rfl⟩ : syracuseStep 978907 = 1468361) B1468361
theorem B1470473 : Blo 976593 1470473 := bstep (se 2 (by rfl) ⟨551427, by rfl⟩ : syracuseStep 1470473 = 1102855) B1102855
theorem B978983 : Blo 976593 978983 := bstep (se 1 (by rfl) ⟨734237, by rfl⟩ : syracuseStep 978983 = 1468475) B1468475
theorem B1470503 : Blo 976593 1470503 := bstep (se 1 (by rfl) ⟨1102877, by rfl⟩ : syracuseStep 1470503 = 2205755) B2205755
theorem B979023 : Blo 976593 979023 := bstep (se 1 (by rfl) ⟨734267, by rfl⟩ : syracuseStep 979023 = 1468535) B1468535
theorem B5566553 : Blo 976593 5566553 := bstep (se 2 (by rfl) ⟨2087457, by rfl⟩ : syracuseStep 5566553 = 4174915) B4174915
theorem B979039 : Blo 976593 979039 := bstep (se 1 (by rfl) ⟨734279, by rfl⟩ : syracuseStep 979039 = 1468559) B1468559
theorem B1175675 : Blo 976593 1175675 := bstep (se 1 (by rfl) ⟨881756, by rfl⟩ : syracuseStep 1175675 = 1763513) B1763513
theorem B979067 : Blo 976593 979067 := bstep (se 1 (by rfl) ⟨734300, by rfl⟩ : syracuseStep 979067 = 1468601) B1468601
theorem B1470587 : Blo 976593 1470587 := bstep (se 1 (by rfl) ⟨1102940, by rfl⟩ : syracuseStep 1470587 = 2205881) B2205881
theorem B2781341 : Blo 976593 2781341 := bstep (se 3 (by rfl) ⟨521501, by rfl⟩ : syracuseStep 2781341 = 1043003) B1043003
theorem B979119 : Blo 976593 979119 := bstep (se 1 (by rfl) ⟨734339, by rfl⟩ : syracuseStep 979119 = 1468679) B1468679
theorem B979143 : Blo 976593 979143 := bstep (se 1 (by rfl) ⟨734357, by rfl⟩ : syracuseStep 979143 = 1468715) B1468715
theorem B979163 : Blo 976593 979163 := bstep (se 1 (by rfl) ⟨734372, by rfl⟩ : syracuseStep 979163 = 1468745) B1468745
theorem B1470713 : Blo 976593 1470713 := bstep (se 2 (by rfl) ⟨551517, by rfl⟩ : syracuseStep 1470713 = 1103035) B1103035
theorem B979239 : Blo 976593 979239 := bstep (se 1 (by rfl) ⟨734429, by rfl⟩ : syracuseStep 979239 = 1468859) B1468859
theorem B979279 : Blo 976593 979279 := bstep (se 1 (by rfl) ⟨734459, by rfl⟩ : syracuseStep 979279 = 1468919) B1468919
theorem B979295 : Blo 976593 979295 := bstep (se 1 (by rfl) ⟨734471, by rfl⟩ : syracuseStep 979295 = 1468943) B1468943
theorem B1470815 : Blo 976593 1470815 := bstep (se 1 (by rfl) ⟨1103111, by rfl⟩ : syracuseStep 1470815 = 2206223) B2206223
theorem B1470827 : Blo 976593 1470827 := bstep (se 1 (by rfl) ⟨1103120, by rfl⟩ : syracuseStep 1470827 = 2206241) B2206241
theorem B979323 : Blo 976593 979323 := bstep (se 1 (by rfl) ⟨734492, by rfl⟩ : syracuseStep 979323 = 1468985) B1468985
theorem B2093455 : Blo 976593 2093455 := bstep (se 1 (by rfl) ⟨1570091, by rfl⟩ : syracuseStep 2093455 = 3140183) B3140183
theorem B979375 : Blo 976593 979375 := bstep (se 1 (by rfl) ⟨734531, by rfl⟩ : syracuseStep 979375 = 1469063) B1469063
theorem B1765819 : Blo 976593 1765819 := bstep (se 1 (by rfl) ⟨1324364, by rfl⟩ : syracuseStep 1765819 = 2648729) B2648729
theorem B979399 : Blo 976593 979399 := bstep (se 1 (by rfl) ⟨734549, by rfl⟩ : syracuseStep 979399 = 1469099) B1469099
theorem B979419 : Blo 976593 979419 := bstep (se 1 (by rfl) ⟨734564, by rfl⟩ : syracuseStep 979419 = 1469129) B1469129
theorem B15692291 : Blo 976593 15692291 := bstep (se 1 (by rfl) ⟨11769218, by rfl⟩ : syracuseStep 15692291 = 23538437) B23538437
theorem B5960225 : Blo 976593 5960225 := bstep (se 2 (by rfl) ⟨2235084, by rfl⟩ : syracuseStep 5960225 = 4470169) B4470169
theorem B979495 : Blo 976593 979495 := bstep (se 1 (by rfl) ⟨734621, by rfl⟩ : syracuseStep 979495 = 1469243) B1469243
theorem B979535 : Blo 976593 979535 := bstep (se 1 (by rfl) ⟨734651, by rfl⟩ : syracuseStep 979535 = 1469303) B1469303
theorem B979551 : Blo 976593 979551 := bstep (se 1 (by rfl) ⟨734663, by rfl⟩ : syracuseStep 979551 = 1469327) B1469327
theorem B2355809 : Blo 976593 2355809 := bstep (se 2 (by rfl) ⟨883428, by rfl⟩ : syracuseStep 2355809 = 1766857) B1766857
theorem B979579 : Blo 976593 979579 := bstep (se 1 (by rfl) ⟨734684, by rfl⟩ : syracuseStep 979579 = 1469369) B1469369
theorem B3764875 : Blo 976593 3764875 := bstep (se 1 (by rfl) ⟨2823656, by rfl⟩ : syracuseStep 3764875 = 5647313) B5647313
theorem B979631 : Blo 976593 979631 := bstep (se 1 (by rfl) ⟨734723, by rfl⟩ : syracuseStep 979631 = 1469447) B1469447
theorem B979655 : Blo 976593 979655 := bstep (se 1 (by rfl) ⟨734741, by rfl⟩ : syracuseStep 979655 = 1469483) B1469483
theorem B10711763 : Blo 976593 10711763 := bstep (se 1 (by rfl) ⟨8033822, by rfl⟩ : syracuseStep 10711763 = 16067645) B16067645
theorem B2093779 : Blo 976593 2093779 := bstep (se 1 (by rfl) ⟨1570334, by rfl⟩ : syracuseStep 2093779 = 3140669) B3140669
theorem B979675 : Blo 976593 979675 := bstep (se 1 (by rfl) ⟨734756, by rfl⟩ : syracuseStep 979675 = 1469513) B1469513
theorem B1766137 : Blo 976593 1766137 := bstep (se 2 (by rfl) ⟨662301, by rfl⟩ : syracuseStep 1766137 = 1324603) B1324603
theorem B979751 : Blo 976593 979751 := bstep (se 1 (by rfl) ⟨734813, by rfl⟩ : syracuseStep 979751 = 1469627) B1469627
theorem B979791 : Blo 976593 979791 := bstep (se 1 (by rfl) ⟨734843, by rfl⟩ : syracuseStep 979791 = 1469687) B1469687
theorem B979807 : Blo 976593 979807 := bstep (se 1 (by rfl) ⟨734855, by rfl⟩ : syracuseStep 979807 = 1469711) B1469711
theorem B979835 : Blo 976593 979835 := bstep (se 1 (by rfl) ⟨734876, by rfl⟩ : syracuseStep 979835 = 1469753) B1469753
theorem B57308057 : Blo 976593 57308057 := bstep (se 2 (by rfl) ⟨21490521, by rfl⟩ : syracuseStep 57308057 = 42981043) B42981043
theorem B2782127 : Blo 976593 2782127 := bstep (se 1 (by rfl) ⟨2086595, by rfl⟩ : syracuseStep 2782127 = 4173191) B4173191
theorem B979887 : Blo 976593 979887 := bstep (se 1 (by rfl) ⟨734915, by rfl⟩ : syracuseStep 979887 = 1469831) B1469831
theorem B979911 : Blo 976593 979911 := bstep (se 1 (by rfl) ⟨734933, by rfl⟩ : syracuseStep 979911 = 1469867) B1469867
theorem B979931 : Blo 976593 979931 := bstep (se 1 (by rfl) ⟨734948, by rfl⟩ : syracuseStep 979931 = 1469897) B1469897
theorem B980007 : Blo 976593 980007 := bstep (se 1 (by rfl) ⟨735005, by rfl⟩ : syracuseStep 980007 = 1470011) B1470011
theorem B7435313 : Blo 976593 7435313 := bstep (se 2 (by rfl) ⟨2788242, by rfl⟩ : syracuseStep 7435313 = 5576485) B5576485
theorem B53507141 : Blo 976593 53507141 := bstep (se 4 (by rfl) ⟨5016294, by rfl⟩ : syracuseStep 53507141 = 10032589) B10032589
theorem B980047 : Blo 976593 980047 := bstep (se 1 (by rfl) ⟨735035, by rfl⟩ : syracuseStep 980047 = 1470071) B1470071
theorem B980063 : Blo 976593 980063 := bstep (se 1 (by rfl) ⟨735047, by rfl⟩ : syracuseStep 980063 = 1470095) B1470095
theorem B980091 : Blo 976593 980091 := bstep (se 1 (by rfl) ⟨735068, by rfl⟩ : syracuseStep 980091 = 1470137) B1470137
theorem B4945049 : Blo 976593 4945049 := bstep (se 2 (by rfl) ⟨1854393, by rfl⟩ : syracuseStep 4945049 = 3708787) B3708787
theorem B980143 : Blo 976593 980143 := bstep (se 1 (by rfl) ⟨735107, by rfl⟩ : syracuseStep 980143 = 1470215) B1470215
theorem B980167 : Blo 976593 980167 := bstep (se 1 (by rfl) ⟨735125, by rfl⟩ : syracuseStep 980167 = 1470251) B1470251
theorem B980187 : Blo 976593 980187 := bstep (se 1 (by rfl) ⟨735140, by rfl⟩ : syracuseStep 980187 = 1470281) B1470281
theorem B3306743 : Blo 976593 3306743 := bstep (se 1 (by rfl) ⟨2480057, by rfl⟩ : syracuseStep 3306743 = 4960115) B4960115
theorem B980263 : Blo 976593 980263 := bstep (se 1 (by rfl) ⟨735197, by rfl⟩ : syracuseStep 980263 = 1470395) B1470395
theorem B980303 : Blo 976593 980303 := bstep (se 1 (by rfl) ⟨735227, by rfl⟩ : syracuseStep 980303 = 1470455) B1470455
theorem B980319 : Blo 976593 980319 := bstep (se 1 (by rfl) ⟨735239, by rfl⟩ : syracuseStep 980319 = 1470479) B1470479
theorem B980347 : Blo 976593 980347 := bstep (se 1 (by rfl) ⟨735260, by rfl⟩ : syracuseStep 980347 = 1470521) B1470521
theorem B980399 : Blo 976593 980399 := bstep (se 1 (by rfl) ⟨735299, by rfl⟩ : syracuseStep 980399 = 1470599) B1470599
theorem B980423 : Blo 976593 980423 := bstep (se 1 (by rfl) ⟨735317, by rfl⟩ : syracuseStep 980423 = 1470635) B1470635
theorem B980443 : Blo 976593 980443 := bstep (se 1 (by rfl) ⟨735332, by rfl⟩ : syracuseStep 980443 = 1470665) B1470665
theorem B980519 : Blo 976593 980519 := bstep (se 1 (by rfl) ⟨735389, by rfl⟩ : syracuseStep 980519 = 1470779) B1470779
theorem B3307067 : Blo 976593 3307067 := bstep (se 1 (by rfl) ⟨2480300, by rfl⟩ : syracuseStep 3307067 = 4960601) B4960601
theorem B980559 : Blo 976593 980559 := bstep (se 1 (by rfl) ⟨735419, by rfl⟩ : syracuseStep 980559 = 1470839) B1470839
theorem B980575 : Blo 976593 980575 := bstep (se 1 (by rfl) ⟨735431, by rfl⟩ : syracuseStep 980575 = 1470863) B1470863
theorem B12515107 : Blo 976593 12515107 := bstep (se 1 (by rfl) ⟨9386330, by rfl⟩ : syracuseStep 12515107 = 18772661) B18772661
theorem B3307337 : Blo 976593 3307337 := bstep (se 2 (by rfl) ⟨1240251, by rfl⟩ : syracuseStep 3307337 = 2480503) B2480503
theorem B5371757 : Blo 976593 5371757 := bstep (se 3 (by rfl) ⟨1007204, by rfl⟩ : syracuseStep 5371757 = 2014409) B2014409
theorem B10582073 : Blo 976593 10582073 := bstep (se 2 (by rfl) ⟨3968277, by rfl⟩ : syracuseStep 10582073 = 7936555) B7936555
theorem B2979919 : Blo 976593 2979919 := bstep (se 1 (by rfl) ⟨2234939, by rfl⟩ : syracuseStep 2979919 = 4469879) B4469879
theorem B17824033 : Blo 976593 17824033 := bstep (se 2 (by rfl) ⟨6684012, by rfl⟩ : syracuseStep 17824033 = 13368025) B13368025
theorem B2980601 : Blo 976593 2980601 := bstep (se 2 (by rfl) ⟨1117725, by rfl⟩ : syracuseStep 2980601 = 2235451) B2235451
theorem B3308471 : Blo 976593 3308471 := bstep (se 1 (by rfl) ⟨2481353, by rfl⟩ : syracuseStep 3308471 = 4962707) B4962707
theorem B5962753 : Blo 976593 5962753 := bstep (se 2 (by rfl) ⟨2236032, by rfl⟩ : syracuseStep 5962753 = 4472065) B4472065
theorem B16743671 : Blo 976593 16743671 := bstep (se 1 (by rfl) ⟨12557753, by rfl⟩ : syracuseStep 16743671 = 25115507) B25115507
theorem B3309065 : Blo 976593 3309065 := bstep (se 2 (by rfl) ⟨1240899, by rfl⟩ : syracuseStep 3309065 = 2481799) B2481799
theorem B7044823 : Blo 976593 7044823 := bstep (se 1 (by rfl) ⟨5283617, by rfl⟩ : syracuseStep 7044823 = 10567235) B10567235
theorem B20086865 : Blo 976593 20086865 := bstep (se 2 (by rfl) ⟨7532574, by rfl⟩ : syracuseStep 20086865 = 15065149) B15065149
theorem B2228755 : Blo 976593 2228755 := bstep (se 1 (by rfl) ⟨1671566, by rfl⟩ : syracuseStep 2228755 = 3343133) B3343133
theorem B11142035 : Blo 976593 11142035 := bstep (se 1 (by rfl) ⟨8356526, by rfl⟩ : syracuseStep 11142035 = 16713053) B16713053
theorem B8356769 : Blo 976593 8356769 := bstep (se 2 (by rfl) ⟨3133788, by rfl⟩ : syracuseStep 8356769 = 6267577) B6267577
theorem B4948937 : Blo 976593 4948937 := bstep (se 2 (by rfl) ⟨1855851, by rfl⟩ : syracuseStep 4948937 = 3711703) B3711703
theorem B2786683 : Blo 976593 2786683 := bstep (se 1 (by rfl) ⟨2090012, by rfl⟩ : syracuseStep 2786683 = 4180025) B4180025
theorem B3966347 : Blo 976593 3966347 := bstep (se 1 (by rfl) ⟨2974760, by rfl⟩ : syracuseStep 3966347 = 5949521) B5949521
theorem B95061509 : Blo 976593 95061509 := bstep (se 4 (by rfl) ⟨8912016, by rfl⟩ : syracuseStep 95061509 = 17824033) B17824033
theorem B2197871 : Blo 976593 2197871 := bstep (se 1 (by rfl) ⟨1648403, by rfl⟩ : syracuseStep 2197871 = 3296807) B3296807
theorem B2197943 : Blo 976593 2197943 := bstep (se 1 (by rfl) ⟨1648457, by rfl⟩ : syracuseStep 2197943 = 3296915) B3296915
theorem B2198087 : Blo 976593 2198087 := bstep (se 1 (by rfl) ⟨1648565, by rfl⟩ : syracuseStep 2198087 = 3297131) B3297131
theorem B2198123 : Blo 976593 2198123 := bstep (se 1 (by rfl) ⟨1648592, by rfl⟩ : syracuseStep 2198123 = 3297185) B3297185
theorem B2788015 : Blo 976593 2788015 := bstep (se 1 (by rfl) ⟨2091011, by rfl⟩ : syracuseStep 2788015 = 4182023) B4182023
theorem B7539479 : Blo 976593 7539479 := bstep (se 1 (by rfl) ⟨5654609, by rfl⟩ : syracuseStep 7539479 = 11309219) B11309219
theorem B10718077 : Blo 976593 10718077 := bstep (se 3 (by rfl) ⟨2009639, by rfl⟩ : syracuseStep 10718077 = 4019279) B4019279
theorem B2198519 : Blo 976593 2198519 := bstep (se 1 (by rfl) ⟨1648889, by rfl⟩ : syracuseStep 2198519 = 3297779) B3297779
theorem B4459643 : Blo 976593 4459643 := bstep (se 1 (by rfl) ⟨3344732, by rfl⟩ : syracuseStep 4459643 = 6689465) B6689465
theorem B2198879 : Blo 976593 2198879 := bstep (se 1 (by rfl) ⟨1649159, by rfl⟩ : syracuseStep 2198879 = 3298319) B3298319
theorem B3968621 : Blo 976593 3968621 := bstep (se 3 (by rfl) ⟨744116, by rfl⟩ : syracuseStep 3968621 = 1488233) B1488233
theorem B2199275 : Blo 976593 2199275 := bstep (se 1 (by rfl) ⟨1649456, by rfl⟩ : syracuseStep 2199275 = 3298913) B3298913
theorem B2199401 : Blo 976593 2199401 := bstep (se 2 (by rfl) ⟨824775, by rfl⟩ : syracuseStep 2199401 = 1649551) B1649551
theorem B8458141 : Blo 976593 8458141 := bstep (se 3 (by rfl) ⟨1585901, by rfl⟩ : syracuseStep 8458141 = 3171803) B3171803
theorem B2232329 : Blo 976593 2232329 := bstep (se 2 (by rfl) ⟨837123, by rfl⟩ : syracuseStep 2232329 = 1674247) B1674247
theorem B7442603 : Blo 976593 7442603 := bstep (se 1 (by rfl) ⟨5581952, by rfl⟩ : syracuseStep 7442603 = 11163905) B11163905
theorem B2232787 : Blo 976593 2232787 := bstep (se 1 (by rfl) ⟨1674590, by rfl⟩ : syracuseStep 2232787 = 3349181) B3349181
theorem B2200247 : Blo 976593 2200247 := bstep (se 1 (by rfl) ⟨1650185, by rfl⟩ : syracuseStep 2200247 = 3300371) B3300371
theorem B1675999 : Blo 976593 1675999 := bstep (se 1 (by rfl) ⟨1256999, by rfl⟩ : syracuseStep 1675999 = 2513999) B2513999
theorem B4952825 : Blo 976593 4952825 := bstep (se 2 (by rfl) ⟨1857309, by rfl⟩ : syracuseStep 4952825 = 3714619) B3714619
theorem B33952541 : Blo 976593 33952541 := bstep (se 3 (by rfl) ⟨6366101, by rfl⟩ : syracuseStep 33952541 = 12732203) B12732203
theorem B2200463 : Blo 976593 2200463 := bstep (se 1 (by rfl) ⟨1650347, by rfl⟩ : syracuseStep 2200463 = 3300695) B3300695
theorem B3708119 : Blo 976593 3708119 := bstep (se 1 (by rfl) ⟨2781089, by rfl⟩ : syracuseStep 3708119 = 5562179) B5562179
theorem B3347699 : Blo 976593 3347699 := bstep (se 1 (by rfl) ⟨2510774, by rfl⟩ : syracuseStep 3347699 = 5021549) B5021549
theorem B9410093 : Blo 976593 9410093 := bstep (se 3 (by rfl) ⟨1764392, by rfl⟩ : syracuseStep 9410093 = 3528785) B3528785
theorem B2201183 : Blo 976593 2201183 := bstep (se 1 (by rfl) ⟨1650887, by rfl⟩ : syracuseStep 2201183 = 3301775) B3301775
theorem B2201399 : Blo 976593 2201399 := bstep (se 1 (by rfl) ⟨1651049, by rfl⟩ : syracuseStep 2201399 = 3302099) B3302099
theorem B2791273 : Blo 976593 2791273 := bstep (se 2 (by rfl) ⟨1046727, by rfl⟩ : syracuseStep 2791273 = 2093455) B2093455
theorem B2201705 : Blo 976593 2201705 := bstep (se 2 (by rfl) ⟨825639, by rfl⟩ : syracuseStep 2201705 = 1651279) B1651279
theorem B5019833 : Blo 976593 5019833 := bstep (se 2 (by rfl) ⟨1882437, by rfl⟩ : syracuseStep 5019833 = 3764875) B3764875
theorem B99359227 : Blo 976593 99359227 := bstep (se 1 (by rfl) ⟨74519420, by rfl⟩ : syracuseStep 99359227 = 149038841) B149038841
theorem B2202191 : Blo 976593 2202191 := bstep (se 1 (by rfl) ⟨1651643, by rfl⟩ : syracuseStep 2202191 = 3303287) B3303287
theorem B3709547 : Blo 976593 3709547 := bstep (se 1 (by rfl) ⟨2782160, by rfl⟩ : syracuseStep 3709547 = 5564321) B5564321
theorem B2202335 : Blo 976593 2202335 := bstep (se 1 (by rfl) ⟨1651751, by rfl⟩ : syracuseStep 2202335 = 3303503) B3303503
theorem B4463531 : Blo 976593 4463531 := bstep (se 1 (by rfl) ⟨3347648, by rfl⟩ : syracuseStep 4463531 = 6695297) B6695297
theorem B2202587 : Blo 976593 2202587 := bstep (se 1 (by rfl) ⟨1651940, by rfl⟩ : syracuseStep 2202587 = 3303881) B3303881
theorem B1907855 : Blo 976593 1907855 := bstep (se 1 (by rfl) ⟨1430891, by rfl⟩ : syracuseStep 1907855 = 2861783) B2861783
theorem B2202767 : Blo 976593 2202767 := bstep (se 1 (by rfl) ⟨1652075, by rfl⟩ : syracuseStep 2202767 = 3304151) B3304151
theorem B2202857 : Blo 976593 2202857 := bstep (se 2 (by rfl) ⟨826071, by rfl⟩ : syracuseStep 2202857 = 1652143) B1652143
theorem B2202911 : Blo 976593 2202911 := bstep (se 1 (by rfl) ⟨1652183, by rfl⟩ : syracuseStep 2202911 = 3304367) B3304367
theorem B4955579 : Blo 976593 4955579 := bstep (se 1 (by rfl) ⟨3716684, by rfl⟩ : syracuseStep 4955579 = 7433369) B7433369
theorem B16686809 : Blo 976593 16686809 := bstep (se 2 (by rfl) ⟨6257553, by rfl⟩ : syracuseStep 16686809 = 12515107) B12515107
theorem B6692615 : Blo 976593 6692615 := bstep (se 1 (by rfl) ⟨5019461, by rfl⟩ : syracuseStep 6692615 = 10038923) B10038923
theorem B3710731 : Blo 976593 3710731 := bstep (se 1 (by rfl) ⟨2783048, by rfl⟩ : syracuseStep 3710731 = 5566097) B5566097
theorem B2203433 : Blo 976593 2203433 := bstep (se 2 (by rfl) ⟨826287, by rfl⟩ : syracuseStep 2203433 = 1652575) B1652575
theorem B3711035 : Blo 976593 3711035 := bstep (se 1 (by rfl) ⟨2783276, by rfl⟩ : syracuseStep 3711035 = 5566553) B5566553
theorem B3973225 : Blo 976593 3973225 := bstep (se 2 (by rfl) ⟨1489959, by rfl⟩ : syracuseStep 3973225 = 2979919) B2979919
theorem B10461527 : Blo 976593 10461527 := bstep (se 1 (by rfl) ⟨7846145, by rfl⟩ : syracuseStep 10461527 = 15692291) B15692291
theorem B85696861 : Blo 976593 85696861 := bstep (se 3 (by rfl) ⟨16068161, by rfl⟩ : syracuseStep 85696861 = 32136323) B32136323
theorem B3973483 : Blo 976593 3973483 := bstep (se 1 (by rfl) ⟨2980112, by rfl⟩ : syracuseStep 3973483 = 5960225) B5960225
theorem B4956875 : Blo 976593 4956875 := bstep (se 1 (by rfl) ⟨3717656, by rfl⟩ : syracuseStep 4956875 = 7435313) B7435313
theorem B2204495 : Blo 976593 2204495 := bstep (se 1 (by rfl) ⟨1653371, by rfl⟩ : syracuseStep 2204495 = 3306743) B3306743
theorem B4957037 : Blo 976593 4957037 := bstep (se 3 (by rfl) ⟨929444, by rfl⟩ : syracuseStep 4957037 = 1858889) B1858889
theorem B2204711 : Blo 976593 2204711 := bstep (se 1 (by rfl) ⟨1653533, by rfl⟩ : syracuseStep 2204711 = 3307067) B3307067
theorem B2204891 : Blo 976593 2204891 := bstep (se 1 (by rfl) ⟨1653668, by rfl⟩ : syracuseStep 2204891 = 3307337) B3307337
theorem B3581171 : Blo 976593 3581171 := bstep (se 1 (by rfl) ⟨2685878, by rfl⟩ : syracuseStep 3581171 = 5371757) B5371757
theorem B10036529 : Blo 976593 10036529 := bstep (se 2 (by rfl) ⟨3763698, by rfl⟩ : syracuseStep 10036529 = 7527397) B7527397
theorem B7054715 : Blo 976593 7054715 := bstep (se 1 (by rfl) ⟨5291036, by rfl⟩ : syracuseStep 7054715 = 10582073) B10582073
theorem B4466081 : Blo 976593 4466081 := bstep (se 2 (by rfl) ⟨1674780, by rfl⟩ : syracuseStep 4466081 = 3349561) B3349561
theorem B2205089 : Blo 976593 2205089 := bstep (se 2 (by rfl) ⟨826908, by rfl⟩ : syracuseStep 2205089 = 1653817) B1653817
theorem B12559805 : Blo 976593 12559805 := bstep (se 3 (by rfl) ⟨2354963, by rfl⟩ : syracuseStep 12559805 = 4709927) B4709927
theorem B1648363 : Blo 976593 1648363 := bstep (se 1 (by rfl) ⟨1236272, by rfl⟩ : syracuseStep 1648363 = 2472545) B2472545
theorem B14100257 : Blo 976593 14100257 := bstep (se 2 (by rfl) ⟨5287596, by rfl⟩ : syracuseStep 14100257 = 10575193) B10575193
theorem B4171601 : Blo 976593 4171601 := bstep (se 2 (by rfl) ⟨1564350, by rfl⟩ : syracuseStep 4171601 = 3128701) B3128701
theorem B2205647 : Blo 976593 2205647 := bstep (se 1 (by rfl) ⟨1654235, by rfl⟩ : syracuseStep 2205647 = 3308471) B3308471
theorem B2206025 : Blo 976593 2206025 := bstep (se 2 (by rfl) ⟨827259, by rfl⟩ : syracuseStep 2206025 = 1654519) B1654519
theorem B2206043 : Blo 976593 2206043 := bstep (se 1 (by rfl) ⟨1654532, by rfl⟩ : syracuseStep 2206043 = 3309065) B3309065
theorem B1649335 : Blo 976593 1649335 := bstep (se 1 (by rfl) ⟨1237001, by rfl⟩ : syracuseStep 1649335 = 2474003) B2474003
theorem B5286647 : Blo 976593 5286647 := bstep (se 1 (by rfl) ⟨3964985, by rfl⟩ : syracuseStep 5286647 = 7929971) B7929971
theorem B8366915 : Blo 976593 8366915 := bstep (se 1 (by rfl) ⟨6275186, by rfl⟩ : syracuseStep 8366915 = 12550373) B12550373
theorem B4467581 : Blo 976593 4467581 := bstep (se 3 (by rfl) ⟨837671, by rfl⟩ : syracuseStep 4467581 = 1675343) B1675343
theorem B1649639 : Blo 976593 1649639 := bstep (se 1 (by rfl) ⟨1237229, by rfl⟩ : syracuseStep 1649639 = 2474459) B2474459
theorem B15281167 : Blo 976593 15281167 := bstep (se 1 (by rfl) ⟨11460875, by rfl⟩ : syracuseStep 15281167 = 22921751) B22921751
theorem B1256743 : Blo 976593 1256743 := bstep (se 1 (by rfl) ⟨942557, by rfl⟩ : syracuseStep 1256743 = 1885115) B1885115
theorem B8466083 : Blo 976593 8466083 := bstep (se 1 (by rfl) ⟨6349562, by rfl⟩ : syracuseStep 8466083 = 12699125) B12699125
theorem B8466119 : Blo 976593 8466119 := bstep (se 1 (by rfl) ⟨6349589, by rfl⟩ : syracuseStep 8466119 = 12699179) B12699179
theorem B4959953 : Blo 976593 4959953 := bstep (se 2 (by rfl) ⟨1859982, by rfl⟩ : syracuseStep 4959953 = 3719965) B3719965
theorem B15052825 : Blo 976593 15052825 := bstep (se 2 (by rfl) ⟨5644809, by rfl⟩ : syracuseStep 15052825 = 11289619) B11289619
theorem B1650793 : Blo 976593 1650793 := bstep (se 2 (by rfl) ⟨619047, by rfl⟩ : syracuseStep 1650793 = 1238095) B1238095
theorem B4698587 : Blo 976593 4698587 := bstep (se 1 (by rfl) ⟨3523940, by rfl⟩ : syracuseStep 4698587 = 7047881) B7047881
theorem B8926031 : Blo 976593 8926031 := bstep (se 1 (by rfl) ⟨6694523, by rfl⟩ : syracuseStep 8926031 = 13389047) B13389047
theorem B7418789 : Blo 976593 7418789 := bstep (se 4 (by rfl) ⟨695511, by rfl⟩ : syracuseStep 7418789 = 1391023) B1391023
theorem B9417701 : Blo 976593 9417701 := bstep (se 4 (by rfl) ⟨882909, by rfl⟩ : syracuseStep 9417701 = 1765819) B1765819
theorem B16069711 : Blo 976593 16069711 := bstep (se 1 (by rfl) ⟨12052283, by rfl⟩ : syracuseStep 16069711 = 24104567) B24104567
theorem B17839223 : Blo 976593 17839223 := bstep (se 1 (by rfl) ⟨13379417, by rfl⟩ : syracuseStep 17839223 = 26758835) B26758835
theorem B4240745 : Blo 976593 4240745 := bstep (se 2 (by rfl) ⟨1590279, by rfl⟩ : syracuseStep 4240745 = 3180559) B3180559
theorem B8369513 : Blo 976593 8369513 := bstep (se 2 (by rfl) ⟨3138567, by rfl⟩ : syracuseStep 8369513 = 6277135) B6277135
theorem B7419275 : Blo 976593 7419275 := bstep (se 1 (by rfl) ⟨5564456, by rfl⟩ : syracuseStep 7419275 = 11128913) B11128913
theorem B10728941 : Blo 976593 10728941 := bstep (se 3 (by rfl) ⟨2011676, by rfl⟩ : syracuseStep 10728941 = 4023353) B4023353
theorem B15480557 : Blo 976593 15480557 := bstep (se 3 (by rfl) ⟨2902604, by rfl⟩ : syracuseStep 15480557 = 5805209) B5805209
theorem B1652521 : Blo 976593 1652521 := bstep (se 2 (by rfl) ⟨619695, by rfl⟩ : syracuseStep 1652521 = 1239391) B1239391
theorem B9418589 : Blo 976593 9418589 := bstep (se 3 (by rfl) ⟨1765985, by rfl⟩ : syracuseStep 9418589 = 3531971) B3531971
theorem B35698583 : Blo 976593 35698583 := bstep (se 1 (by rfl) ⟨26773937, by rfl⟩ : syracuseStep 35698583 = 53547875) B53547875
theorem B48215969 : Blo 976593 48215969 := bstep (se 2 (by rfl) ⟨18080988, by rfl⟩ : syracuseStep 48215969 = 36161977) B36161977
theorem B4962383 : Blo 976593 4962383 := bstep (se 1 (by rfl) ⟨3721787, by rfl⟩ : syracuseStep 4962383 = 7443575) B7443575
theorem B10598681 : Blo 976593 10598681 := bstep (se 2 (by rfl) ⟨3974505, by rfl⟩ : syracuseStep 10598681 = 7949011) B7949011
theorem B2472403 : Blo 976593 2472403 := bstep (se 1 (by rfl) ⟨1854302, by rfl⟩ : syracuseStep 2472403 = 3708605) B3708605
theorem B1653311 : Blo 976593 1653311 := bstep (se 1 (by rfl) ⟨1239983, by rfl⟩ : syracuseStep 1653311 = 2479967) B2479967
theorem B1489583 : Blo 976593 1489583 := bstep (se 1 (by rfl) ⟨1117187, by rfl⟩ : syracuseStep 1489583 = 2234375) B2234375
theorem B6273935 : Blo 976593 6273935 := bstep (se 1 (by rfl) ⟨4705451, by rfl⟩ : syracuseStep 6273935 = 9410903) B9410903
theorem B4963517 : Blo 976593 4963517 := bstep (se 3 (by rfl) ⟨930659, by rfl⟩ : syracuseStep 4963517 = 1861319) B1861319
theorem B1653979 : Blo 976593 1653979 := bstep (se 1 (by rfl) ⟨1240484, by rfl⟩ : syracuseStep 1653979 = 2480969) B2480969
theorem B2473193 : Blo 976593 2473193 := bstep (se 2 (by rfl) ⟨927447, by rfl⟩ : syracuseStep 2473193 = 1854895) B1854895
theorem B7519499 : Blo 976593 7519499 := bstep (se 1 (by rfl) ⟨5639624, by rfl⟩ : syracuseStep 7519499 = 11279249) B11279249
theorem B9059651 : Blo 976593 9059651 := bstep (se 1 (by rfl) ⟨6794738, by rfl⟩ : syracuseStep 9059651 = 13589477) B13589477
theorem B2473355 : Blo 976593 2473355 := bstep (se 1 (by rfl) ⟨1855016, by rfl⟩ : syracuseStep 2473355 = 3710033) B3710033
theorem B1392071 : Blo 976593 1392071 := bstep (se 1 (by rfl) ⟨1044053, by rfl⟩ : syracuseStep 1392071 = 2088107) B2088107
theorem B4702009 : Blo 976593 4702009 := bstep (se 2 (by rfl) ⟨1763253, by rfl⟩ : syracuseStep 4702009 = 3526507) B3526507
theorem B1654735 : Blo 976593 1654735 := bstep (se 1 (by rfl) ⟨1241051, by rfl⟩ : syracuseStep 1654735 = 2482103) B2482103
theorem B31801349 : Blo 976593 31801349 := bstep (se 4 (by rfl) ⟨2981376, by rfl⟩ : syracuseStep 31801349 = 5962753) B5962753
theorem B4243481 : Blo 976593 4243481 := bstep (se 2 (by rfl) ⟨1591305, by rfl⟩ : syracuseStep 4243481 = 3182611) B3182611
theorem B4178249 : Blo 976593 4178249 := bstep (se 2 (by rfl) ⟨1566843, by rfl⟩ : syracuseStep 4178249 = 3133687) B3133687
theorem B2474347 : Blo 976593 2474347 := bstep (se 1 (by rfl) ⟨1855760, by rfl⟩ : syracuseStep 2474347 = 3711521) B3711521
theorem B2474671 : Blo 976593 2474671 := bstep (se 1 (by rfl) ⟨1856003, by rfl⟩ : syracuseStep 2474671 = 3712007) B3712007
theorem B12534587 : Blo 976593 12534587 := bstep (se 1 (by rfl) ⟨9400940, by rfl⟩ : syracuseStep 12534587 = 18801881) B18801881
theorem B23774147 : Blo 976593 23774147 := bstep (se 1 (by rfl) ⟨17830610, by rfl⟩ : syracuseStep 23774147 = 35661221) B35661221
theorem B2474995 : Blo 976593 2474995 := bstep (se 1 (by rfl) ⟨1856246, by rfl⟩ : syracuseStep 2474995 = 3712493) B3712493
theorem B1099039 : Blo 976593 1099039 := bstep (se 1 (by rfl) ⟨824279, by rfl⟩ : syracuseStep 1099039 = 1648559) B1648559
theorem B1393951 : Blo 976593 1393951 := bstep (se 1 (by rfl) ⟨1045463, by rfl⟩ : syracuseStep 1393951 = 2090927) B2090927
theorem B1590559 : Blo 976593 1590559 := bstep (se 1 (by rfl) ⟨1192919, by rfl⟩ : syracuseStep 1590559 = 2385839) B2385839
theorem B4703777 : Blo 976593 4703777 := bstep (se 2 (by rfl) ⟨1763916, by rfl⟩ : syracuseStep 4703777 = 3527833) B3527833
theorem B1099327 : Blo 976593 1099327 := bstep (se 1 (by rfl) ⟨824495, by rfl⟩ : syracuseStep 1099327 = 1648991) B1648991
theorem B2475755 : Blo 976593 2475755 := bstep (se 1 (by rfl) ⟨1856816, by rfl⟩ : syracuseStep 2475755 = 3713633) B3713633
theorem B1100155 : Blo 976593 1100155 := bstep (se 1 (by rfl) ⟨825116, by rfl⟩ : syracuseStep 1100155 = 1650233) B1650233
theorem B4180349 : Blo 976593 4180349 := bstep (se 3 (by rfl) ⟨783815, by rfl⟩ : syracuseStep 4180349 = 1567631) B1567631
theorem B17844623 : Blo 976593 17844623 := bstep (se 1 (by rfl) ⟨13383467, by rfl⟩ : syracuseStep 17844623 = 26766935) B26766935
theorem B2476615 : Blo 976593 2476615 := bstep (se 1 (by rfl) ⟨1857461, by rfl⟩ : syracuseStep 2476615 = 3714923) B3714923
theorem B2476727 : Blo 976593 2476727 := bstep (se 1 (by rfl) ⟨1857545, by rfl⟩ : syracuseStep 2476727 = 3715091) B3715091
theorem B1854227 : Blo 976593 1854227 := bstep (se 1 (by rfl) ⟨1390670, by rfl⟩ : syracuseStep 1854227 = 2781341) B2781341
theorem B1100623 : Blo 976593 1100623 := bstep (se 1 (by rfl) ⟨825467, by rfl⟩ : syracuseStep 1100623 = 1650935) B1650935
theorem B5295035 : Blo 976593 5295035 := bstep (se 1 (by rfl) ⟨3971276, by rfl⟩ : syracuseStep 5295035 = 7942553) B7942553
theorem B1101019 : Blo 976593 1101019 := bstep (se 1 (by rfl) ⟨825764, by rfl⟩ : syracuseStep 1101019 = 1651529) B1651529
theorem B1854751 : Blo 976593 1854751 := bstep (se 1 (by rfl) ⟨1391063, by rfl⟩ : syracuseStep 1854751 = 2782127) B2782127
theorem B35671427 : Blo 976593 35671427 := bstep (se 1 (by rfl) ⟨26753570, by rfl⟩ : syracuseStep 35671427 = 53507141) B53507141
theorem B3296699 : Blo 976593 3296699 := bstep (se 1 (by rfl) ⟨2472524, by rfl⟩ : syracuseStep 3296699 = 4945049) B4945049
theorem B1101307 : Blo 976593 1101307 := bstep (se 1 (by rfl) ⟨825980, by rfl⟩ : syracuseStep 1101307 = 1651961) B1651961
theorem B3722867 : Blo 976593 3722867 := bstep (se 1 (by rfl) ⟨2792150, by rfl⟩ : syracuseStep 3722867 = 5584301) B5584301
theorem B2477729 : Blo 976593 2477729 := bstep (se 2 (by rfl) ⟨929148, by rfl⟩ : syracuseStep 2477729 = 1858297) B1858297
theorem B4181665 : Blo 976593 4181665 := bstep (se 2 (by rfl) ⟨1568124, by rfl⟩ : syracuseStep 4181665 = 3136249) B3136249
theorem B1101487 : Blo 976593 1101487 := bstep (se 1 (by rfl) ⟨826115, by rfl⟩ : syracuseStep 1101487 = 1652231) B1652231
theorem B1101775 : Blo 976593 1101775 := bstep (se 1 (by rfl) ⟨826331, by rfl⟩ : syracuseStep 1101775 = 1652663) B1652663
theorem B15847481 : Blo 976593 15847481 := bstep (se 2 (by rfl) ⟨5942805, by rfl⟩ : syracuseStep 15847481 = 11885611) B11885611
theorem B2478185 : Blo 976593 2478185 := bstep (se 2 (by rfl) ⟨929319, by rfl⟩ : syracuseStep 2478185 = 1858639) B1858639
theorem B1102171 : Blo 976593 1102171 := bstep (se 1 (by rfl) ⟨826628, by rfl⟩ : syracuseStep 1102171 = 1653257) B1653257
theorem B1102279 : Blo 976593 1102279 := bstep (se 1 (by rfl) ⟨826709, by rfl⟩ : syracuseStep 1102279 = 1653419) B1653419
theorem B1987067 : Blo 976593 1987067 := bstep (se 1 (by rfl) ⟨1490300, by rfl⟩ : syracuseStep 1987067 = 2980601) B2980601
theorem B2478671 : Blo 976593 2478671 := bstep (se 1 (by rfl) ⟨1859003, by rfl⟩ : syracuseStep 2478671 = 3718007) B3718007
theorem B1102639 : Blo 976593 1102639 := bstep (se 1 (by rfl) ⟨826979, by rfl⟩ : syracuseStep 1102639 = 1653959) B1653959
theorem B11162447 : Blo 976593 11162447 := bstep (se 1 (by rfl) ⟨8371835, by rfl⟩ : syracuseStep 11162447 = 16743671) B16743671
theorem B1102747 : Blo 976593 1102747 := bstep (se 1 (by rfl) ⟨827060, by rfl⟩ : syracuseStep 1102747 = 1654121) B1654121
theorem B9393097 : Blo 976593 9393097 := bstep (se 2 (by rfl) ⟨3522411, by rfl⟩ : syracuseStep 9393097 = 7044823) B7044823
theorem B2479319 : Blo 976593 2479319 := bstep (se 1 (by rfl) ⟨1859489, by rfl⟩ : syracuseStep 2479319 = 3718979) B3718979
theorem B2643193 : Blo 976593 2643193 := bstep (se 2 (by rfl) ⟨991197, by rfl⟩ : syracuseStep 2643193 = 1982395) B1982395
theorem B1103143 : Blo 976593 1103143 := bstep (se 1 (by rfl) ⟨827357, by rfl⟩ : syracuseStep 1103143 = 1654715) B1654715
theorem B2479673 : Blo 976593 2479673 := bstep (se 2 (by rfl) ⟨929877, by rfl⟩ : syracuseStep 2479673 = 1859755) B1859755
theorem B3135133 : Blo 976593 3135133 := bstep (se 3 (by rfl) ⟨587837, by rfl⟩ : syracuseStep 3135133 = 1175675) B1175675
theorem B2643617 : Blo 976593 2643617 := bstep (se 2 (by rfl) ⟨991356, by rfl⟩ : syracuseStep 2643617 = 1982713) B1982713
theorem B3135287 : Blo 976593 3135287 := bstep (se 1 (by rfl) ⟨2351465, by rfl⟩ : syracuseStep 3135287 = 4702931) B4702931
theorem B2348929 : Blo 976593 2348929 := bstep (se 2 (by rfl) ⟨880848, by rfl⟩ : syracuseStep 2348929 = 1761697) B1761697
theorem B2087279 : Blo 976593 2087279 := bstep (se 1 (by rfl) ⟨1565459, by rfl⟩ : syracuseStep 2087279 = 3130919) B3130919
theorem B1464953 : Blo 976593 1464953 := bstep (se 2 (by rfl) ⟨549357, by rfl⟩ : syracuseStep 1464953 = 1098715) B1098715
theorem B1465007 : Blo 976593 1465007 := bstep (se 1 (by rfl) ⟨1098755, by rfl⟩ : syracuseStep 1465007 = 2197511) B2197511
theorem B1465055 : Blo 976593 1465055 := bstep (se 1 (by rfl) ⟨1098791, by rfl⟩ : syracuseStep 1465055 = 2197583) B2197583
theorem B28170989 : Blo 976593 28170989 := bstep (se 3 (by rfl) ⟨5282060, by rfl⟩ : syracuseStep 28170989 = 10564121) B10564121
theorem B2087851 : Blo 976593 2087851 := bstep (se 1 (by rfl) ⟨1565888, by rfl⟩ : syracuseStep 2087851 = 3131777) B3131777
theorem B1465319 : Blo 976593 1465319 := bstep (se 1 (by rfl) ⟨1098989, by rfl⟩ : syracuseStep 1465319 = 2197979) B2197979
theorem B2514059 : Blo 976593 2514059 := bstep (se 1 (by rfl) ⟨1885544, by rfl⟩ : syracuseStep 2514059 = 3771089) B3771089
theorem B2645207 : Blo 976593 2645207 := bstep (se 1 (by rfl) ⟨1983905, by rfl⟩ : syracuseStep 2645207 = 3967811) B3967811
theorem B1465577 : Blo 976593 1465577 := bstep (se 2 (by rfl) ⟨549591, by rfl⟩ : syracuseStep 1465577 = 1099183) B1099183
theorem B1465631 : Blo 976593 1465631 := bstep (se 1 (by rfl) ⟨1099223, by rfl⟩ : syracuseStep 1465631 = 2198447) B2198447
theorem B1465799 : Blo 976593 1465799 := bstep (se 1 (by rfl) ⟨1099349, by rfl⟩ : syracuseStep 1465799 = 2198699) B2198699
theorem B3300857 : Blo 976593 3300857 := bstep (se 2 (by rfl) ⟨1237821, by rfl⟩ : syracuseStep 3300857 = 2475643) B2475643
theorem B1236475 : Blo 976593 1236475 := bstep (se 1 (by rfl) ⟨927356, by rfl⟩ : syracuseStep 1236475 = 1854713) B1854713
theorem B1236703 : Blo 976593 1236703 := bstep (se 1 (by rfl) ⟨927527, by rfl⟩ : syracuseStep 1236703 = 1855055) B1855055
theorem B3301127 : Blo 976593 3301127 := bstep (se 1 (by rfl) ⟨2475845, by rfl⟩ : syracuseStep 3301127 = 4951691) B4951691
theorem B1466153 : Blo 976593 1466153 := bstep (se 2 (by rfl) ⟨549807, by rfl⟩ : syracuseStep 1466153 = 1099615) B1099615
theorem B2481961 : Blo 976593 2481961 := bstep (se 2 (by rfl) ⟨930735, by rfl⟩ : syracuseStep 2481961 = 1861471) B1861471
theorem B1466159 : Blo 976593 1466159 := bstep (se 1 (by rfl) ⟨1099619, by rfl⟩ : syracuseStep 1466159 = 2199239) B2199239
theorem B1859375 : Blo 976593 1859375 := bstep (se 1 (by rfl) ⟨1394531, by rfl⟩ : syracuseStep 1859375 = 2789063) B2789063
theorem B3301181 : Blo 976593 3301181 := bstep (se 3 (by rfl) ⟨618971, by rfl⟩ : syracuseStep 3301181 = 1237943) B1237943
theorem B5431499 : Blo 976593 5431499 := bstep (se 1 (by rfl) ⟨4073624, by rfl⟩ : syracuseStep 5431499 = 8147249) B8147249
theorem B1466633 : Blo 976593 1466633 := bstep (se 2 (by rfl) ⟨549987, by rfl⟩ : syracuseStep 1466633 = 1099975) B1099975
theorem B1466735 : Blo 976593 1466735 := bstep (se 1 (by rfl) ⟨1100051, by rfl⟩ : syracuseStep 1466735 = 2200103) B2200103
theorem B1237447 : Blo 976593 1237447 := bstep (se 1 (by rfl) ⟨928085, by rfl⟩ : syracuseStep 1237447 = 1856171) B1856171
theorem B1466951 : Blo 976593 1466951 := bstep (se 1 (by rfl) ⟨1100213, by rfl⟩ : syracuseStep 1466951 = 2200427) B2200427
theorem B1466987 : Blo 976593 1466987 := bstep (se 1 (by rfl) ⟨1100240, by rfl⟩ : syracuseStep 1466987 = 2200481) B2200481
theorem B2089747 : Blo 976593 2089747 := bstep (se 1 (by rfl) ⟨1567310, by rfl⟩ : syracuseStep 2089747 = 3134621) B3134621
theorem B1467215 : Blo 976593 1467215 := bstep (se 1 (by rfl) ⟨1100411, by rfl⟩ : syracuseStep 1467215 = 2200823) B2200823
theorem B2384795 : Blo 976593 2384795 := bstep (se 1 (by rfl) ⟨1788596, by rfl⟩ : syracuseStep 2384795 = 3577193) B3577193
theorem B1860583 : Blo 976593 1860583 := bstep (se 1 (by rfl) ⟨1395437, by rfl⟩ : syracuseStep 1860583 = 2790875) B2790875
theorem B1762295 : Blo 976593 1762295 := bstep (se 1 (by rfl) ⟨1321721, by rfl⟩ : syracuseStep 1762295 = 2643443) B2643443
theorem B11166821 : Blo 976593 11166821 := bstep (se 4 (by rfl) ⟨1046889, by rfl⟩ : syracuseStep 11166821 = 2093779) B2093779
theorem B1467611 : Blo 976593 1467611 := bstep (se 1 (by rfl) ⟨1100708, by rfl⟩ : syracuseStep 1467611 = 2201417) B2201417
theorem B2647259 : Blo 976593 2647259 := bstep (se 1 (by rfl) ⟨1985444, by rfl⟩ : syracuseStep 2647259 = 3970889) B3970889
theorem B1467785 : Blo 976593 1467785 := bstep (se 2 (by rfl) ⟨550419, by rfl⟩ : syracuseStep 1467785 = 1100839) B1100839
theorem B1238591 : Blo 976593 1238591 := bstep (se 1 (by rfl) ⟨928943, by rfl⟩ : syracuseStep 1238591 = 1857887) B1857887
theorem B976607 : Blo 976593 976607 := bstep (se 1 (by rfl) ⟨732455, by rfl⟩ : syracuseStep 976607 = 1464911) B1464911
theorem B1763051 : Blo 976593 1763051 := bstep (se 1 (by rfl) ⟨1322288, by rfl⟩ : syracuseStep 1763051 = 2644577) B2644577
theorem B1468139 : Blo 976593 1468139 := bstep (se 1 (by rfl) ⟨1101104, by rfl⟩ : syracuseStep 1468139 = 2202209) B2202209
theorem B976687 : Blo 976593 976687 := bstep (se 1 (by rfl) ⟨732515, by rfl⟩ : syracuseStep 976687 = 1465031) B1465031
theorem B2385769 : Blo 976593 2385769 := bstep (se 2 (by rfl) ⟨894663, by rfl⟩ : syracuseStep 2385769 = 1789327) B1789327
theorem B1173403 : Blo 976593 1173403 := bstep (se 1 (by rfl) ⟨880052, by rfl⟩ : syracuseStep 1173403 = 1760105) B1760105
theorem B976795 : Blo 976593 976795 := bstep (se 1 (by rfl) ⟨732596, by rfl⟩ : syracuseStep 976795 = 1465193) B1465193
theorem B976847 : Blo 976593 976847 := bstep (se 1 (by rfl) ⟨732635, by rfl⟩ : syracuseStep 976847 = 1465271) B1465271
theorem B1468367 : Blo 976593 1468367 := bstep (se 1 (by rfl) ⟨1101275, by rfl⟩ : syracuseStep 1468367 = 2202551) B2202551
theorem B976871 : Blo 976593 976871 := bstep (se 1 (by rfl) ⟨732653, by rfl⟩ : syracuseStep 976871 = 1465307) B1465307
theorem B3533053 : Blo 976593 3533053 := bstep (se 3 (by rfl) ⟨662447, by rfl⟩ : syracuseStep 3533053 = 1324895) B1324895
theorem B977183 : Blo 976593 977183 := bstep (se 1 (by rfl) ⟨732887, by rfl⟩ : syracuseStep 977183 = 1465775) B1465775
theorem B977243 : Blo 976593 977243 := bstep (se 1 (by rfl) ⟨732932, by rfl⟩ : syracuseStep 977243 = 1465865) B1465865
theorem B1468763 : Blo 976593 1468763 := bstep (se 1 (by rfl) ⟨1101572, by rfl⟩ : syracuseStep 1468763 = 2203145) B2203145
theorem B977263 : Blo 976593 977263 := bstep (se 1 (by rfl) ⟨732947, by rfl⟩ : syracuseStep 977263 = 1465895) B1465895
theorem B3533167 : Blo 976593 3533167 := bstep (se 1 (by rfl) ⟨2649875, by rfl⟩ : syracuseStep 3533167 = 5299751) B5299751
theorem B977319 : Blo 976593 977319 := bstep (se 1 (by rfl) ⟨732989, by rfl⟩ : syracuseStep 977319 = 1465979) B1465979
theorem B1763795 : Blo 976593 1763795 := bstep (se 1 (by rfl) ⟨1322846, by rfl⟩ : syracuseStep 1763795 = 2645693) B2645693
theorem B2353619 : Blo 976593 2353619 := bstep (se 1 (by rfl) ⟨1765214, by rfl⟩ : syracuseStep 2353619 = 3530429) B3530429
theorem B977403 : Blo 976593 977403 := bstep (se 1 (by rfl) ⟨733052, by rfl⟩ : syracuseStep 977403 = 1466105) B1466105
theorem B977471 : Blo 976593 977471 := bstep (se 1 (by rfl) ⟨733103, by rfl⟩ : syracuseStep 977471 = 1466207) B1466207
theorem B1468991 : Blo 976593 1468991 := bstep (se 1 (by rfl) ⟨1101743, by rfl⟩ : syracuseStep 1468991 = 2203487) B2203487
theorem B977479 : Blo 976593 977479 := bstep (se 1 (by rfl) ⟨733109, by rfl⟩ : syracuseStep 977479 = 1466219) B1466219
theorem B6777431 : Blo 976593 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B3304043 : Blo 976593 3304043 := bstep (se 1 (by rfl) ⟨2478032, by rfl⟩ : syracuseStep 3304043 = 4956065) B4956065
theorem B1469111 : Blo 976593 1469111 := bstep (se 1 (by rfl) ⟨1101833, by rfl⟩ : syracuseStep 1469111 = 2203667) B2203667
theorem B977631 : Blo 976593 977631 := bstep (se 1 (by rfl) ⟨733223, by rfl⟩ : syracuseStep 977631 = 1466447) B1466447
theorem B977711 : Blo 976593 977711 := bstep (se 1 (by rfl) ⟨733283, by rfl⟩ : syracuseStep 977711 = 1466567) B1466567
theorem B1239887 : Blo 976593 1239887 := bstep (se 1 (by rfl) ⟨929915, by rfl⟩ : syracuseStep 1239887 = 1859831) B1859831
theorem B977819 : Blo 976593 977819 := bstep (se 1 (by rfl) ⟨733364, by rfl⟩ : syracuseStep 977819 = 1466729) B1466729
theorem B1469339 : Blo 976593 1469339 := bstep (se 1 (by rfl) ⟨1102004, by rfl⟩ : syracuseStep 1469339 = 2204009) B2204009
theorem B977871 : Blo 976593 977871 := bstep (se 1 (by rfl) ⟨733403, by rfl⟩ : syracuseStep 977871 = 1466807) B1466807
theorem B977895 : Blo 976593 977895 := bstep (se 1 (by rfl) ⟨733421, by rfl⟩ : syracuseStep 977895 = 1466843) B1466843
theorem B1240039 : Blo 976593 1240039 := bstep (se 1 (by rfl) ⟨930029, by rfl⟩ : syracuseStep 1240039 = 1860059) B1860059
theorem B15494159 : Blo 976593 15494159 := bstep (se 1 (by rfl) ⟨11620619, by rfl⟩ : syracuseStep 15494159 = 23241239) B23241239
theorem B3304637 : Blo 976593 3304637 := bstep (se 3 (by rfl) ⟨619619, by rfl⟩ : syracuseStep 3304637 = 1239239) B1239239
theorem B978207 : Blo 976593 978207 := bstep (se 1 (by rfl) ⟨733655, by rfl⟩ : syracuseStep 978207 = 1467311) B1467311
theorem B1469735 : Blo 976593 1469735 := bstep (se 1 (by rfl) ⟨1102301, by rfl⟩ : syracuseStep 1469735 = 2204603) B2204603
theorem B978267 : Blo 976593 978267 := bstep (se 1 (by rfl) ⟨733700, by rfl⟩ : syracuseStep 978267 = 1467401) B1467401
theorem B978287 : Blo 976593 978287 := bstep (se 1 (by rfl) ⟨733715, by rfl⟩ : syracuseStep 978287 = 1467431) B1467431
theorem B1469819 : Blo 976593 1469819 := bstep (se 1 (by rfl) ⟨1102364, by rfl⟩ : syracuseStep 1469819 = 2204729) B2204729
theorem B978343 : Blo 976593 978343 := bstep (se 1 (by rfl) ⟨733757, by rfl⟩ : syracuseStep 978343 = 1467515) B1467515
theorem B1469945 : Blo 976593 1469945 := bstep (se 2 (by rfl) ⟨551229, by rfl⟩ : syracuseStep 1469945 = 1102459) B1102459
theorem B978427 : Blo 976593 978427 := bstep (se 1 (by rfl) ⟨733820, by rfl⟩ : syracuseStep 978427 = 1467641) B1467641
theorem B978495 : Blo 976593 978495 := bstep (se 1 (by rfl) ⟨733871, by rfl⟩ : syracuseStep 978495 = 1467743) B1467743
theorem B978503 : Blo 976593 978503 := bstep (se 1 (by rfl) ⟨733877, by rfl⟩ : syracuseStep 978503 = 1467755) B1467755
theorem B1470047 : Blo 976593 1470047 := bstep (se 1 (by rfl) ⟨1102535, by rfl⟩ : syracuseStep 1470047 = 2205071) B2205071
theorem B2354849 : Blo 976593 2354849 := bstep (se 2 (by rfl) ⟨883068, by rfl⟩ : syracuseStep 2354849 = 1766137) B1766137
theorem B25128629 : Blo 976593 25128629 := bstep (se 5 (by rfl) ⟨1177904, by rfl⟩ : syracuseStep 25128629 = 2355809) B2355809
theorem B978655 : Blo 976593 978655 := bstep (se 1 (by rfl) ⟨733991, by rfl⟩ : syracuseStep 978655 = 1467983) B1467983
theorem B1765099 : Blo 976593 1765099 := bstep (se 1 (by rfl) ⟨1323824, by rfl⟩ : syracuseStep 1765099 = 2647649) B2647649
theorem B978735 : Blo 976593 978735 := bstep (se 1 (by rfl) ⟨734051, by rfl⟩ : syracuseStep 978735 = 1468103) B1468103
theorem B1568567 : Blo 976593 1568567 := bstep (se 1 (by rfl) ⟨1176425, by rfl⟩ : syracuseStep 1568567 = 2352851) B2352851
theorem B1470263 : Blo 976593 1470263 := bstep (se 1 (by rfl) ⟨1102697, by rfl⟩ : syracuseStep 1470263 = 2205395) B2205395
theorem B978843 : Blo 976593 978843 := bstep (se 1 (by rfl) ⟨734132, by rfl⟩ : syracuseStep 978843 = 1468265) B1468265
theorem B978895 : Blo 976593 978895 := bstep (se 1 (by rfl) ⟨734171, by rfl⟩ : syracuseStep 978895 = 1468343) B1468343
theorem B978919 : Blo 976593 978919 := bstep (se 1 (by rfl) ⟨734189, by rfl⟩ : syracuseStep 978919 = 1468379) B1468379
theorem B1470569 : Blo 976593 1470569 := bstep (se 2 (by rfl) ⟨551463, by rfl⟩ : syracuseStep 1470569 = 1102927) B1102927
theorem B979231 : Blo 976593 979231 := bstep (se 1 (by rfl) ⟨734423, by rfl⟩ : syracuseStep 979231 = 1468847) B1468847
theorem B979291 : Blo 976593 979291 := bstep (se 1 (by rfl) ⟨734468, by rfl⟩ : syracuseStep 979291 = 1468937) B1468937
theorem B979311 : Blo 976593 979311 := bstep (se 1 (by rfl) ⟨734483, by rfl⟩ : syracuseStep 979311 = 1468967) B1468967
theorem B979367 : Blo 976593 979367 := bstep (se 1 (by rfl) ⟨734525, by rfl⟩ : syracuseStep 979367 = 1469051) B1469051
theorem B1470887 : Blo 976593 1470887 := bstep (se 1 (by rfl) ⟨1103165, by rfl⟩ : syracuseStep 1470887 = 2206331) B2206331
theorem B8483291 : Blo 976593 8483291 := bstep (se 1 (by rfl) ⟨6362468, by rfl⟩ : syracuseStep 8483291 = 12724937) B12724937
theorem B979451 : Blo 976593 979451 := bstep (se 1 (by rfl) ⟨734588, by rfl⟩ : syracuseStep 979451 = 1469177) B1469177
theorem B10711601 : Blo 976593 10711601 := bstep (se 2 (by rfl) ⟨4016850, by rfl⟩ : syracuseStep 10711601 = 8033701) B8033701
theorem B979519 : Blo 976593 979519 := bstep (se 1 (by rfl) ⟨734639, by rfl⟩ : syracuseStep 979519 = 1469279) B1469279
theorem B979527 : Blo 976593 979527 := bstep (se 1 (by rfl) ⟨734645, by rfl⟩ : syracuseStep 979527 = 1469291) B1469291
theorem B2355887 : Blo 976593 2355887 := bstep (se 1 (by rfl) ⟨1766915, by rfl⟩ : syracuseStep 2355887 = 3533831) B3533831
theorem B2716343 : Blo 976593 2716343 := bstep (se 1 (by rfl) ⟨2037257, by rfl⟩ : syracuseStep 2716343 = 4074515) B4074515
theorem B979679 : Blo 976593 979679 := bstep (se 1 (by rfl) ⟨734759, by rfl⟩ : syracuseStep 979679 = 1469519) B1469519
theorem B1176367 : Blo 976593 1176367 := bstep (se 1 (by rfl) ⟨882275, by rfl⟩ : syracuseStep 1176367 = 1764551) B1764551
theorem B979759 : Blo 976593 979759 := bstep (se 1 (by rfl) ⟨734819, by rfl⟩ : syracuseStep 979759 = 1469639) B1469639
theorem B979867 : Blo 976593 979867 := bstep (se 1 (by rfl) ⟨734900, by rfl⟩ : syracuseStep 979867 = 1469801) B1469801
theorem B979919 : Blo 976593 979919 := bstep (se 1 (by rfl) ⟨734939, by rfl⟩ : syracuseStep 979919 = 1469879) B1469879
theorem B2782183 : Blo 976593 2782183 := bstep (se 1 (by rfl) ⟨2086637, by rfl⟩ : syracuseStep 2782183 = 4173275) B4173275
theorem B979943 : Blo 976593 979943 := bstep (se 1 (by rfl) ⟨734957, by rfl⟩ : syracuseStep 979943 = 1469915) B1469915
theorem B4944887 : Blo 976593 4944887 := bstep (se 1 (by rfl) ⟨3708665, by rfl⟩ : syracuseStep 4944887 = 7417331) B7417331
theorem B18773207 : Blo 976593 18773207 := bstep (se 1 (by rfl) ⟨14079905, by rfl⟩ : syracuseStep 18773207 = 28159811) B28159811
theorem B3765491 : Blo 976593 3765491 := bstep (se 1 (by rfl) ⟨2824118, by rfl⟩ : syracuseStep 3765491 = 5648237) B5648237
theorem B2782457 : Blo 976593 2782457 := bstep (se 2 (by rfl) ⟨1043421, by rfl⟩ : syracuseStep 2782457 = 2086843) B2086843
theorem B5567737 : Blo 976593 5567737 := bstep (se 2 (by rfl) ⟨2087901, by rfl⟩ : syracuseStep 5567737 = 4175803) B4175803
theorem B1570079 : Blo 976593 1570079 := bstep (se 1 (by rfl) ⟨1177559, by rfl⟩ : syracuseStep 1570079 = 2355119) B2355119
theorem B980255 : Blo 976593 980255 := bstep (se 1 (by rfl) ⟨735191, by rfl⟩ : syracuseStep 980255 = 1470383) B1470383
theorem B980315 : Blo 976593 980315 := bstep (se 1 (by rfl) ⟨735236, by rfl⟩ : syracuseStep 980315 = 1470473) B1470473
theorem B980335 : Blo 976593 980335 := bstep (se 1 (by rfl) ⟨735251, by rfl⟩ : syracuseStep 980335 = 1470503) B1470503
theorem B980391 : Blo 976593 980391 := bstep (se 1 (by rfl) ⟨735293, by rfl⟩ : syracuseStep 980391 = 1470587) B1470587
theorem B980475 : Blo 976593 980475 := bstep (se 1 (by rfl) ⟨735356, by rfl⟩ : syracuseStep 980475 = 1470713) B1470713
theorem B980543 : Blo 976593 980543 := bstep (se 1 (by rfl) ⟨735407, by rfl⟩ : syracuseStep 980543 = 1470815) B1470815
theorem B980551 : Blo 976593 980551 := bstep (se 1 (by rfl) ⟨735413, by rfl⟩ : syracuseStep 980551 = 1470827) B1470827
theorem B7141175 : Blo 976593 7141175 := bstep (se 1 (by rfl) ⟨5355881, by rfl⟩ : syracuseStep 7141175 = 10711763) B10711763
theorem B38205371 : Blo 976593 38205371 := bstep (se 1 (by rfl) ⟨28654028, by rfl⟩ : syracuseStep 38205371 = 57308057) B57308057
theorem B3307553 : Blo 976593 3307553 := bstep (se 2 (by rfl) ⟨1240332, by rfl⟩ : syracuseStep 3307553 = 2480665) B2480665
theorem B4946831 : Blo 976593 4946831 := bstep (se 1 (by rfl) ⟨3710123, by rfl⟩ : syracuseStep 4946831 = 7420247) B7420247
theorem B21200899 : Blo 976593 21200899 := bstep (se 1 (by rfl) ⟨15900674, by rfl⟩ : syracuseStep 21200899 = 31801349) B31801349
theorem B2785499 : Blo 976593 2785499 := bstep (se 1 (by rfl) ⟨2089124, by rfl⟩ : syracuseStep 2785499 = 4178249) B4178249
theorem B114262481 : Blo 976593 114262481 := bstep (se 2 (by rfl) ⟨42848430, by rfl⟩ : syracuseStep 114262481 = 85696861) B85696861
theorem B8356391 : Blo 976593 8356391 := bstep (se 1 (by rfl) ⟨6267293, by rfl⟩ : syracuseStep 8356391 = 12534587) B12534587
theorem B5571179 : Blo 976593 5571179 := bstep (se 1 (by rfl) ⟨4178384, by rfl⟩ : syracuseStep 5571179 = 8356769) B8356769
theorem B63374339 : Blo 976593 63374339 := bstep (se 1 (by rfl) ⟨47530754, by rfl⟩ : syracuseStep 63374339 = 95061509) B95061509
theorem B2786329 : Blo 976593 2786329 := bstep (se 2 (by rfl) ⟨1044873, by rfl⟩ : syracuseStep 2786329 = 2089747) B2089747
theorem B2786899 : Blo 976593 2786899 := bstep (se 1 (by rfl) ⟨2090174, by rfl⟩ : syracuseStep 2786899 = 4180349) B4180349
theorem B11896415 : Blo 976593 11896415 := bstep (se 1 (by rfl) ⟨8922311, by rfl⟩ : syracuseStep 11896415 = 17844623) B17844623
theorem B90540109 : Blo 976593 90540109 := bstep (se 3 (by rfl) ⟨16976270, by rfl⟩ : syracuseStep 90540109 = 33952541) B33952541
theorem B2197799 : Blo 976593 2197799 := bstep (se 1 (by rfl) ⟨1648349, by rfl⟩ : syracuseStep 2197799 = 3296699) B3296699
theorem B2197817 : Blo 976593 2197817 := bstep (se 2 (by rfl) ⟨824181, by rfl⟩ : syracuseStep 2197817 = 1648363) B1648363
theorem B6359453 : Blo 976593 6359453 := bstep (se 3 (by rfl) ⟨1192397, by rfl⟩ : syracuseStep 6359453 = 2384795) B2384795
theorem B3181025 : Blo 976593 3181025 := bstep (se 2 (by rfl) ⟨1192884, by rfl⟩ : syracuseStep 3181025 = 2385769) B2385769
theorem B7441631 : Blo 976593 7441631 := bstep (se 1 (by rfl) ⟨5581223, by rfl⟩ : syracuseStep 7441631 = 11162447) B11162447
theorem B2199113 : Blo 976593 2199113 := bstep (se 2 (by rfl) ⟨824667, by rfl⟩ : syracuseStep 2199113 = 1649335) B1649335
theorem B18812573 : Blo 976593 18812573 := bstep (se 3 (by rfl) ⟨3527357, by rfl⟩ : syracuseStep 18812573 = 7054715) B7054715
theorem B14290769 : Blo 976593 14290769 := bstep (se 2 (by rfl) ⟨5359038, by rfl⟩ : syracuseStep 14290769 = 10718077) B10718077
theorem B3346555 : Blo 976593 3346555 := bstep (se 1 (by rfl) ⟨2509916, by rfl⟩ : syracuseStep 3346555 = 5019833) B5019833
theorem B1675657 : Blo 976593 1675657 := bstep (se 2 (by rfl) ⟨628371, by rfl⟩ : syracuseStep 1675657 = 1256743) B1256743
theorem B18780659 : Blo 976593 18780659 := bstep (se 1 (by rfl) ⟨14085494, by rfl⟩ : syracuseStep 18780659 = 28170989) B28170989
theorem B8360765 : Blo 976593 8360765 := bstep (se 3 (by rfl) ⟨1567643, by rfl⟩ : syracuseStep 8360765 = 3135287) B3135287
theorem B5575553 : Blo 976593 5575553 := bstep (se 2 (by rfl) ⟨2090832, by rfl⟩ : syracuseStep 5575553 = 4181665) B4181665
theorem B2200571 : Blo 976593 2200571 := bstep (se 1 (by rfl) ⟨1650428, by rfl⟩ : syracuseStep 2200571 = 3300857) B3300857
theorem B2200751 : Blo 976593 2200751 := bstep (se 1 (by rfl) ⟨1650563, by rfl⟩ : syracuseStep 2200751 = 3301127) B3301127
theorem B4461743 : Blo 976593 4461743 := bstep (se 1 (by rfl) ⟨3346307, by rfl⟩ : syracuseStep 4461743 = 6692615) B6692615
theorem B11277521 : Blo 976593 11277521 := bstep (se 2 (by rfl) ⟨4229070, by rfl⟩ : syracuseStep 11277521 = 8458141) B8458141
theorem B2200787 : Blo 976593 2200787 := bstep (se 1 (by rfl) ⟨1650590, by rfl⟩ : syracuseStep 2200787 = 3301181) B3301181
theorem B2201057 : Blo 976593 2201057 := bstep (se 2 (by rfl) ⟨825396, by rfl⟩ : syracuseStep 2201057 = 1650793) B1650793
theorem B7444547 : Blo 976593 7444547 := bstep (se 1 (by rfl) ⟨5583410, by rfl⟩ : syracuseStep 7444547 = 11166821) B11166821
theorem B6691019 : Blo 976593 6691019 := bstep (se 1 (by rfl) ⟨5018264, by rfl⟩ : syracuseStep 6691019 = 10036529) B10036529
theorem B2234665 : Blo 976593 2234665 := bstep (se 2 (by rfl) ⟨837999, by rfl⟩ : syracuseStep 2234665 = 1675999) B1675999
theorem B12524129 : Blo 976593 12524129 := bstep (se 2 (by rfl) ⟨4696548, by rfl⟩ : syracuseStep 12524129 = 9393097) B9393097
theorem B3709577 : Blo 976593 3709577 := bstep (se 2 (by rfl) ⟨1391091, by rfl⟩ : syracuseStep 3709577 = 2782183) B2782183
theorem B2202695 : Blo 976593 2202695 := bstep (se 1 (by rfl) ⟨1652021, by rfl⟩ : syracuseStep 2202695 = 3304043) B3304043
theorem B5577943 : Blo 976593 5577943 := bstep (se 1 (by rfl) ⟨4183457, by rfl⟩ : syracuseStep 5577943 = 8366915) B8366915
theorem B10329439 : Blo 976593 10329439 := bstep (se 1 (by rfl) ⟨7747079, by rfl⟩ : syracuseStep 10329439 = 15494159) B15494159
theorem B2203091 : Blo 976593 2203091 := bstep (se 1 (by rfl) ⟨1652318, by rfl⟩ : syracuseStep 2203091 = 3304637) B3304637
theorem B2203361 : Blo 976593 2203361 := bstep (se 2 (by rfl) ⟨826260, by rfl⟩ : syracuseStep 2203361 = 1652521) B1652521
theorem B5644055 : Blo 976593 5644055 := bstep (se 1 (by rfl) ⟨4233041, by rfl⟩ : syracuseStep 5644055 = 8466083) B8466083
theorem B16752419 : Blo 976593 16752419 := bstep (se 1 (by rfl) ⟨12564314, by rfl⟩ : syracuseStep 16752419 = 25128629) B25128629
theorem B5644079 : Blo 976593 5644079 := bstep (se 1 (by rfl) ⟨4233059, by rfl⟩ : syracuseStep 5644079 = 8466119) B8466119
theorem B1810895 : Blo 976593 1810895 := bstep (se 1 (by rfl) ⟨1358171, by rfl⟩ : syracuseStep 1810895 = 2716343) B2716343
theorem B2827163 : Blo 976593 2827163 := bstep (se 1 (by rfl) ⟨2120372, by rfl⟩ : syracuseStep 2827163 = 4240745) B4240745
theorem B5579675 : Blo 976593 5579675 := bstep (se 1 (by rfl) ⟨4184756, by rfl⟩ : syracuseStep 5579675 = 8369513) B8369513
theorem B3712189 : Blo 976593 3712189 := bstep (se 3 (by rfl) ⟨696035, by rfl⟩ : syracuseStep 3712189 = 1392071) B1392071
theorem B4760783 : Blo 976593 4760783 := bstep (se 1 (by rfl) ⟨3570587, by rfl⟩ : syracuseStep 4760783 = 7141175) B7141175
theorem B23799055 : Blo 976593 23799055 := bstep (se 1 (by rfl) ⟨17849291, by rfl⟩ : syracuseStep 23799055 = 35698583) B35698583
theorem B25470247 : Blo 976593 25470247 := bstep (se 1 (by rfl) ⟨19102685, by rfl⟩ : syracuseStep 25470247 = 38205371) B38205371
theorem B2205035 : Blo 976593 2205035 := bstep (se 1 (by rfl) ⟨1653776, by rfl⟩ : syracuseStep 2205035 = 3307553) B3307553
theorem B2205305 : Blo 976593 2205305 := bstep (se 2 (by rfl) ⟨826989, by rfl⟩ : syracuseStep 2205305 = 1653979) B1653979
theorem B993055 : Blo 976593 993055 := bstep (se 1 (by rfl) ⟨744791, by rfl⟩ : syracuseStep 993055 = 1489583) B1489583
theorem B1648633 : Blo 976593 1648633 := bstep (se 2 (by rfl) ⟨618237, by rfl⟩ : syracuseStep 1648633 = 1236475) B1236475
theorem B4958333 : Blo 976593 4958333 := bstep (se 3 (by rfl) ⟨929687, by rfl⟩ : syracuseStep 4958333 = 1859375) B1859375
theorem B1648795 : Blo 976593 1648795 := bstep (se 1 (by rfl) ⟨1236596, by rfl⟩ : syracuseStep 1648795 = 2473193) B2473193
theorem B6039767 : Blo 976593 6039767 := bstep (se 1 (by rfl) ⟨4529825, by rfl⟩ : syracuseStep 6039767 = 9059651) B9059651
theorem B1648903 : Blo 976593 1648903 := bstep (se 1 (by rfl) ⟨1236677, by rfl⟩ : syracuseStep 1648903 = 2473355) B2473355
theorem B1648937 : Blo 976593 1648937 := bstep (se 2 (by rfl) ⟨618351, by rfl⟩ : syracuseStep 1648937 = 1236703) B1236703
theorem B6269345 : Blo 976593 6269345 := bstep (se 2 (by rfl) ⟨2351004, by rfl⟩ : syracuseStep 6269345 = 4702009) B4702009
theorem B2206313 : Blo 976593 2206313 := bstep (se 2 (by rfl) ⟨827367, by rfl⟩ : syracuseStep 2206313 = 1654735) B1654735
theorem B2828987 : Blo 976593 2828987 := bstep (se 1 (by rfl) ⟨2121740, by rfl⟩ : syracuseStep 2828987 = 4243481) B4243481
theorem B1649929 : Blo 976593 1649929 := bstep (se 2 (by rfl) ⟨618723, by rfl⟩ : syracuseStep 1649929 = 1237447) B1237447
theorem B1650503 : Blo 976593 1650503 := bstep (se 1 (by rfl) ⟨1237877, by rfl⟩ : syracuseStep 1650503 = 2475755) B2475755
theorem B12529565 : Blo 976593 12529565 := bstep (se 3 (by rfl) ⟨2349293, by rfl⟩ : syracuseStep 12529565 = 4698587) B4698587
theorem B26816629 : Blo 976593 26816629 := bstep (se 5 (by rfl) ⟨1257029, by rfl⟩ : syracuseStep 26816629 = 2514059) B2514059
theorem B1651151 : Blo 976593 1651151 := bstep (se 1 (by rfl) ⟨1238363, by rfl⟩ : syracuseStep 1651151 = 2476727) B2476727
theorem B3715577 : Blo 976593 3715577 := bstep (se 2 (by rfl) ⟨1393341, by rfl⟩ : syracuseStep 3715577 = 2786683) B2786683
theorem B5026319 : Blo 976593 5026319 := bstep (se 1 (by rfl) ⟨3769739, by rfl⟩ : syracuseStep 5026319 = 7539479) B7539479
theorem B1651819 : Blo 976593 1651819 := bstep (se 1 (by rfl) ⟨1238864, by rfl⟩ : syracuseStep 1651819 = 2477729) B2477729
theorem B4699453 : Blo 976593 4699453 := bstep (se 3 (by rfl) ⟨881147, by rfl⟩ : syracuseStep 4699453 = 1762295) B1762295
theorem B10564987 : Blo 976593 10564987 := bstep (se 1 (by rfl) ⟨7923740, by rfl⟩ : syracuseStep 10564987 = 15847481) B15847481
theorem B1652123 : Blo 976593 1652123 := bstep (se 1 (by rfl) ⟨1239092, by rfl⟩ : syracuseStep 1652123 = 2478185) B2478185
theorem B4961735 : Blo 976593 4961735 := bstep (se 1 (by rfl) ⟨3721301, by rfl⟩ : syracuseStep 4961735 = 7442603) B7442603
theorem B1324711 : Blo 976593 1324711 := bstep (se 1 (by rfl) ⟨993533, by rfl⟩ : syracuseStep 1324711 = 1987067) B1987067
theorem B1652447 : Blo 976593 1652447 := bstep (se 1 (by rfl) ⟨1239335, by rfl⟩ : syracuseStep 1652447 = 2478671) B2478671
theorem B2472079 : Blo 976593 2472079 := bstep (se 1 (by rfl) ⟨1854059, by rfl⟩ : syracuseStep 2472079 = 3708119) B3708119
theorem B1652879 : Blo 976593 1652879 := bstep (se 1 (by rfl) ⟨1239659, by rfl⟩ : syracuseStep 1652879 = 2479319) B2479319
theorem B3717353 : Blo 976593 3717353 := bstep (se 2 (by rfl) ⟨1394007, by rfl⟩ : syracuseStep 3717353 = 2788015) B2788015
theorem B6273395 : Blo 976593 6273395 := bstep (se 1 (by rfl) ⟨4705046, by rfl⟩ : syracuseStep 6273395 = 9410093) B9410093
theorem B1653115 : Blo 976593 1653115 := bstep (se 1 (by rfl) ⟨1239836, by rfl⟩ : syracuseStep 1653115 = 2479673) B2479673
theorem B1653385 : Blo 976593 1653385 := bstep (se 2 (by rfl) ⟨620019, by rfl⟩ : syracuseStep 1653385 = 1240039) B1240039
theorem B1391519 : Blo 976593 1391519 := bstep (se 1 (by rfl) ⟨1043639, by rfl⟩ : syracuseStep 1391519 = 2087279) B2087279
theorem B2473001 : Blo 976593 2473001 := bstep (se 2 (by rfl) ⟨927375, by rfl⟩ : syracuseStep 2473001 = 1854751) B1854751
theorem B2473031 : Blo 976593 2473031 := bstep (se 1 (by rfl) ⟨1854773, by rfl⟩ : syracuseStep 2473031 = 3709547) B3709547
theorem B114442037 : Blo 976593 114442037 := bstep (se 5 (by rfl) ⟨5364470, by rfl⟩ : syracuseStep 114442037 = 10728941) B10728941
theorem B11124539 : Blo 976593 11124539 := bstep (se 1 (by rfl) ⟨8343404, by rfl⟩ : syracuseStep 11124539 = 16686809) B16686809
theorem B20070433 : Blo 976593 20070433 := bstep (se 2 (by rfl) ⟨7526412, by rfl⟩ : syracuseStep 20070433 = 15052825) B15052825
theorem B2474023 : Blo 976593 2474023 := bstep (se 1 (by rfl) ⟨1855517, by rfl⟩ : syracuseStep 2474023 = 3711035) B3711035
theorem B3620999 : Blo 976593 3620999 := bstep (se 1 (by rfl) ⟨2715749, by rfl⟩ : syracuseStep 3620999 = 5431499) B5431499
theorem B8373203 : Blo 976593 8373203 := bstep (se 1 (by rfl) ⟨6279902, by rfl⟩ : syracuseStep 8373203 = 12559805) B12559805
theorem B4703453 : Blo 976593 4703453 := bstep (se 3 (by rfl) ⟨881897, by rfl⟩ : syracuseStep 4703453 = 1763795) B1763795
theorem B7423649 : Blo 976593 7423649 := bstep (se 2 (by rfl) ⟨2783868, by rfl⟩ : syracuseStep 7423649 = 5567737) B5567737
theorem B3524257 : Blo 976593 3524257 := bstep (se 2 (by rfl) ⟨1321596, by rfl⟩ : syracuseStep 3524257 = 2643193) B2643193
theorem B3524431 : Blo 976593 3524431 := bstep (se 1 (by rfl) ⟨2643323, by rfl⟩ : syracuseStep 3524431 = 5286647) B5286647
theorem B1099759 : Blo 976593 1099759 := bstep (se 1 (by rfl) ⟨824819, by rfl⟩ : syracuseStep 1099759 = 1649639) B1649639
theorem B4180177 : Blo 976593 4180177 := bstep (se 2 (by rfl) ⟨1567566, by rfl⟩ : syracuseStep 4180177 = 3135133) B3135133
theorem B3721697 : Blo 976593 3721697 := bstep (se 2 (by rfl) ⟨1395636, by rfl⟩ : syracuseStep 3721697 = 2791273) B2791273
theorem B3131905 : Blo 976593 3131905 := bstep (se 2 (by rfl) ⟨1174464, by rfl⟩ : syracuseStep 3131905 = 2348929) B2348929
theorem B5655527 : Blo 976593 5655527 := bstep (se 1 (by rfl) ⟨4241645, by rfl⟩ : syracuseStep 5655527 = 8483291) B8483291
theorem B5950687 : Blo 976593 5950687 := bstep (se 1 (by rfl) ⟨4463015, by rfl⟩ : syracuseStep 5950687 = 8926031) B8926031
theorem B3296537 : Blo 976593 3296537 := bstep (se 2 (by rfl) ⟨1236201, by rfl⟩ : syracuseStep 3296537 = 2472403) B2472403
theorem B6278467 : Blo 976593 6278467 := bstep (se 1 (by rfl) ⟨4708850, by rfl⟩ : syracuseStep 6278467 = 9417701) B9417701
theorem B3296591 : Blo 976593 3296591 := bstep (se 1 (by rfl) ⟨2472443, by rfl⟩ : syracuseStep 3296591 = 4944887) B4944887
theorem B2510327 : Blo 976593 2510327 := bstep (se 1 (by rfl) ⟨1882745, by rfl⟩ : syracuseStep 2510327 = 3765491) B3765491
theorem B1854971 : Blo 976593 1854971 := bstep (se 1 (by rfl) ⟨1391228, by rfl⟩ : syracuseStep 1854971 = 2782457) B2782457
theorem B6279059 : Blo 976593 6279059 := bstep (se 1 (by rfl) ⟨4709294, by rfl⟩ : syracuseStep 6279059 = 9418589) B9418589
theorem B7065787 : Blo 976593 7065787 := bstep (se 1 (by rfl) ⟨5299340, by rfl⟩ : syracuseStep 7065787 = 10598681) B10598681
theorem B1102207 : Blo 976593 1102207 := bstep (se 1 (by rfl) ⟨826655, by rfl⟩ : syracuseStep 1102207 = 1653311) B1653311
theorem B3297887 : Blo 976593 3297887 := bstep (se 1 (by rfl) ⟨2473415, by rfl⟩ : syracuseStep 3297887 = 4946831) B4946831
theorem B4182623 : Blo 976593 4182623 := bstep (se 1 (by rfl) ⟨3136967, by rfl⟩ : syracuseStep 4182623 = 6273935) B6273935
theorem B13391243 : Blo 976593 13391243 := bstep (se 1 (by rfl) ⟨10043432, by rfl⟩ : syracuseStep 13391243 = 20086865) B20086865
theorem B23811509 : Blo 976593 23811509 := bstep (se 5 (by rfl) ⟨1116164, by rfl⟩ : syracuseStep 23811509 = 2232329) B2232329
theorem B5297633 : Blo 976593 5297633 := bstep (se 2 (by rfl) ⟨1986612, by rfl⟩ : syracuseStep 5297633 = 3973225) B3973225
theorem B325998229 : Blo 976593 325998229 := bstep (se 6 (by rfl) ⟨7640583, by rfl⟩ : syracuseStep 325998229 = 15281167) B15281167
theorem B3299129 : Blo 976593 3299129 := bstep (se 2 (by rfl) ⟨1237173, by rfl⟩ : syracuseStep 3299129 = 2474347) B2474347
theorem B5297977 : Blo 976593 5297977 := bstep (se 2 (by rfl) ⟨1986741, by rfl⟩ : syracuseStep 5297977 = 3973483) B3973483
theorem B7428023 : Blo 976593 7428023 := bstep (se 1 (by rfl) ⟨5571017, by rfl⟩ : syracuseStep 7428023 = 11142035) B11142035
theorem B15849431 : Blo 976593 15849431 := bstep (se 1 (by rfl) ⟨11887073, by rfl⟩ : syracuseStep 15849431 = 23774147) B23774147
theorem B3299291 : Blo 976593 3299291 := bstep (se 1 (by rfl) ⟨2474468, by rfl⟩ : syracuseStep 3299291 = 4948937) B4948937
theorem B2971673 : Blo 976593 2971673 := bstep (se 2 (by rfl) ⟨1114377, by rfl⟩ : syracuseStep 2971673 = 2228755) B2228755
theorem B3299561 : Blo 976593 3299561 := bstep (se 2 (by rfl) ⟨1237335, by rfl⟩ : syracuseStep 3299561 = 2474671) B2474671
theorem B3135851 : Blo 976593 3135851 := bstep (se 1 (by rfl) ⟨2351888, by rfl⟩ : syracuseStep 3135851 = 4703777) B4703777
theorem B2480777 : Blo 976593 2480777 := bstep (se 2 (by rfl) ⟨930291, by rfl⟩ : syracuseStep 2480777 = 1860583) B1860583
theorem B3299993 : Blo 976593 3299993 := bstep (se 2 (by rfl) ⟨1237497, by rfl⟩ : syracuseStep 3299993 = 2474995) B2474995
theorem B1465247 : Blo 976593 1465247 := bstep (se 1 (by rfl) ⟨1098935, by rfl⟩ : syracuseStep 1465247 = 2197871) B2197871
theorem B1465295 : Blo 976593 1465295 := bstep (se 1 (by rfl) ⟨1098971, by rfl⟩ : syracuseStep 1465295 = 2197943) B2197943
theorem B1465385 : Blo 976593 1465385 := bstep (se 2 (by rfl) ⟨549519, by rfl⟩ : syracuseStep 1465385 = 1099039) B1099039
theorem B1858601 : Blo 976593 1858601 := bstep (se 2 (by rfl) ⟨696975, by rfl⟩ : syracuseStep 1858601 = 1393951) B1393951
theorem B1465391 : Blo 976593 1465391 := bstep (se 1 (by rfl) ⟨1099043, by rfl⟩ : syracuseStep 1465391 = 2198087) B2198087
theorem B1465415 : Blo 976593 1465415 := bstep (se 1 (by rfl) ⟨1099061, by rfl⟩ : syracuseStep 1465415 = 2198123) B2198123
theorem B1236151 : Blo 976593 1236151 := bstep (se 1 (by rfl) ⟨927113, by rfl⟩ : syracuseStep 1236151 = 1854227) B1854227
theorem B3530023 : Blo 976593 3530023 := bstep (se 1 (by rfl) ⟨2647517, by rfl⟩ : syracuseStep 3530023 = 5295035) B5295035
theorem B1465679 : Blo 976593 1465679 := bstep (se 1 (by rfl) ⟨1099259, by rfl⟩ : syracuseStep 1465679 = 2198519) B2198519
theorem B2973095 : Blo 976593 2973095 := bstep (se 1 (by rfl) ⟨2229821, by rfl⟩ : syracuseStep 2973095 = 4459643) B4459643
theorem B1465769 : Blo 976593 1465769 := bstep (se 2 (by rfl) ⟨549663, by rfl⟩ : syracuseStep 1465769 = 1099327) B1099327
theorem B1465919 : Blo 976593 1465919 := bstep (se 1 (by rfl) ⟨1099439, by rfl⟩ : syracuseStep 1465919 = 2198879) B2198879
theorem B23780951 : Blo 976593 23780951 := bstep (se 1 (by rfl) ⟨17835713, by rfl⟩ : syracuseStep 23780951 = 35671427) B35671427
theorem B2645747 : Blo 976593 2645747 := bstep (se 1 (by rfl) ⟨1984310, by rfl⟩ : syracuseStep 2645747 = 3968621) B3968621
theorem B2481911 : Blo 976593 2481911 := bstep (se 1 (by rfl) ⟨1861433, by rfl⟩ : syracuseStep 2481911 = 3722867) B3722867
theorem B1466183 : Blo 976593 1466183 := bstep (se 1 (by rfl) ⟨1099637, by rfl⟩ : syracuseStep 1466183 = 2199275) B2199275
theorem B35708789 : Blo 976593 35708789 := bstep (se 5 (by rfl) ⟨1673849, by rfl⟩ : syracuseStep 35708789 = 3347699) B3347699
theorem B1564537 : Blo 976593 1564537 := bstep (se 2 (by rfl) ⟨586701, by rfl⟩ : syracuseStep 1564537 = 1173403) B1173403
theorem B1466267 : Blo 976593 1466267 := bstep (se 1 (by rfl) ⟨1099700, by rfl⟩ : syracuseStep 1466267 = 2199401) B2199401
theorem B529915877 : Blo 976593 529915877 := bstep (se 4 (by rfl) ⟨49679613, by rfl⟩ : syracuseStep 529915877 = 99359227) B99359227
theorem B4710737 : Blo 976593 4710737 := bstep (se 2 (by rfl) ⟨1766526, by rfl⟩ : syracuseStep 4710737 = 3533053) B3533053
theorem B1466831 : Blo 976593 1466831 := bstep (se 1 (by rfl) ⟨1100123, by rfl⟩ : syracuseStep 1466831 = 2200247) B2200247
theorem B4710889 : Blo 976593 4710889 := bstep (se 2 (by rfl) ⟨1766583, by rfl⟩ : syracuseStep 4710889 = 3533167) B3533167
theorem B1466873 : Blo 976593 1466873 := bstep (se 2 (by rfl) ⟨550077, by rfl⟩ : syracuseStep 1466873 = 1100155) B1100155
theorem B3301883 : Blo 976593 3301883 := bstep (se 1 (by rfl) ⟨2476412, by rfl⟩ : syracuseStep 3301883 = 4952825) B4952825
theorem B1466975 : Blo 976593 1466975 := bstep (se 1 (by rfl) ⟨1100231, by rfl⟩ : syracuseStep 1466975 = 2200463) B2200463
theorem B3302153 : Blo 976593 3302153 := bstep (se 2 (by rfl) ⟨1238307, by rfl⟩ : syracuseStep 3302153 = 2476615) B2476615
theorem B10576925 : Blo 976593 10576925 := bstep (se 3 (by rfl) ⟨1983173, by rfl⟩ : syracuseStep 10576925 = 3966347) B3966347
theorem B1467455 : Blo 976593 1467455 := bstep (se 1 (by rfl) ⟨1100591, by rfl⟩ : syracuseStep 1467455 = 2201183) B2201183
theorem B1467497 : Blo 976593 1467497 := bstep (se 2 (by rfl) ⟨550311, by rfl⟩ : syracuseStep 1467497 = 1100623) B1100623
theorem B1762411 : Blo 976593 1762411 := bstep (se 1 (by rfl) ⟨1321808, by rfl⟩ : syracuseStep 1762411 = 2643617) B2643617
theorem B1467599 : Blo 976593 1467599 := bstep (se 1 (by rfl) ⟨1100699, by rfl⟩ : syracuseStep 1467599 = 2201399) B2201399
theorem B1467803 : Blo 976593 1467803 := bstep (se 1 (by rfl) ⟨1100852, by rfl⟩ : syracuseStep 1467803 = 2201705) B2201705
theorem B3302909 : Blo 976593 3302909 := bstep (se 3 (by rfl) ⟨619295, by rfl⟩ : syracuseStep 3302909 = 1238591) B1238591
theorem B1468025 : Blo 976593 1468025 := bstep (se 2 (by rfl) ⟨550509, by rfl⟩ : syracuseStep 1468025 = 1101019) B1101019
theorem B1468127 : Blo 976593 1468127 := bstep (se 1 (by rfl) ⟨1101095, by rfl⟩ : syracuseStep 1468127 = 2202191) B2202191
theorem B976635 : Blo 976593 976635 := bstep (se 1 (by rfl) ⟨732476, by rfl⟩ : syracuseStep 976635 = 1464953) B1464953
theorem B976671 : Blo 976593 976671 := bstep (se 1 (by rfl) ⟨732503, by rfl⟩ : syracuseStep 976671 = 1465007) B1465007
theorem B976703 : Blo 976593 976703 := bstep (se 1 (by rfl) ⟨732527, by rfl⟩ : syracuseStep 976703 = 1465055) B1465055
theorem B1468223 : Blo 976593 1468223 := bstep (se 1 (by rfl) ⟨1101167, by rfl⟩ : syracuseStep 1468223 = 2202335) B2202335
theorem B2975687 : Blo 976593 2975687 := bstep (se 1 (by rfl) ⟨2231765, by rfl⟩ : syracuseStep 2975687 = 4463531) B4463531
theorem B1468391 : Blo 976593 1468391 := bstep (se 1 (by rfl) ⟨1101293, by rfl⟩ : syracuseStep 1468391 = 2202587) B2202587
theorem B976879 : Blo 976593 976879 := bstep (se 1 (by rfl) ⟨732659, by rfl⟩ : syracuseStep 976879 = 1465319) B1465319
theorem B1468409 : Blo 976593 1468409 := bstep (se 2 (by rfl) ⟨550653, by rfl⟩ : syracuseStep 1468409 = 1101307) B1101307
theorem B1271903 : Blo 976593 1271903 := bstep (se 1 (by rfl) ⟨953927, by rfl⟩ : syracuseStep 1271903 = 1907855) B1907855
theorem B1468511 : Blo 976593 1468511 := bstep (se 1 (by rfl) ⟨1101383, by rfl⟩ : syracuseStep 1468511 = 2202767) B2202767
theorem B1763471 : Blo 976593 1763471 := bstep (se 1 (by rfl) ⟨1322603, by rfl⟩ : syracuseStep 1763471 = 2645207) B2645207
theorem B977051 : Blo 976593 977051 := bstep (se 1 (by rfl) ⟨732788, by rfl⟩ : syracuseStep 977051 = 1465577) B1465577
theorem B1468571 : Blo 976593 1468571 := bstep (se 1 (by rfl) ⟨1101428, by rfl⟩ : syracuseStep 1468571 = 2202857) B2202857
theorem B977087 : Blo 976593 977087 := bstep (se 1 (by rfl) ⟨732815, by rfl⟩ : syracuseStep 977087 = 1465631) B1465631
theorem B1468607 : Blo 976593 1468607 := bstep (se 1 (by rfl) ⟨1101455, by rfl⟩ : syracuseStep 1468607 = 2202911) B2202911
theorem B1468649 : Blo 976593 1468649 := bstep (se 2 (by rfl) ⟨550743, by rfl⟩ : syracuseStep 1468649 = 1101487) B1101487
theorem B3303719 : Blo 976593 3303719 := bstep (se 1 (by rfl) ⟨2477789, by rfl⟩ : syracuseStep 3303719 = 4955579) B4955579
theorem B977199 : Blo 976593 977199 := bstep (se 1 (by rfl) ⟨732899, by rfl⟩ : syracuseStep 977199 = 1465799) B1465799
theorem B2353465 : Blo 976593 2353465 := bstep (se 2 (by rfl) ⟨882549, by rfl⟩ : syracuseStep 2353465 = 1765099) B1765099
theorem B977435 : Blo 976593 977435 := bstep (se 1 (by rfl) ⟨733076, by rfl⟩ : syracuseStep 977435 = 1466153) B1466153
theorem B1468955 : Blo 976593 1468955 := bstep (se 1 (by rfl) ⟨1101716, by rfl⟩ : syracuseStep 1468955 = 2203433) B2203433
theorem B977439 : Blo 976593 977439 := bstep (se 1 (by rfl) ⟨733079, by rfl⟩ : syracuseStep 977439 = 1466159) B1466159
theorem B1469033 : Blo 976593 1469033 := bstep (se 2 (by rfl) ⟨550887, by rfl⟩ : syracuseStep 1469033 = 1101775) B1101775
theorem B977755 : Blo 976593 977755 := bstep (se 1 (by rfl) ⟨733316, by rfl⟩ : syracuseStep 977755 = 1466633) B1466633
theorem B6974351 : Blo 976593 6974351 := bstep (se 1 (by rfl) ⟨5230763, by rfl⟩ : syracuseStep 6974351 = 10461527) B10461527
theorem B977823 : Blo 976593 977823 := bstep (se 1 (by rfl) ⟨733367, by rfl⟩ : syracuseStep 977823 = 1466735) B1466735
theorem B977967 : Blo 976593 977967 := bstep (se 1 (by rfl) ⟨733475, by rfl⟩ : syracuseStep 977967 = 1466951) B1466951
theorem B977991 : Blo 976593 977991 := bstep (se 1 (by rfl) ⟨733493, by rfl⟩ : syracuseStep 977991 = 1466987) B1466987
theorem B1469561 : Blo 976593 1469561 := bstep (se 2 (by rfl) ⟨551085, by rfl⟩ : syracuseStep 1469561 = 1102171) B1102171
theorem B3304583 : Blo 976593 3304583 := bstep (se 1 (by rfl) ⟨2478437, by rfl⟩ : syracuseStep 3304583 = 4956875) B4956875
theorem B978143 : Blo 976593 978143 := bstep (se 1 (by rfl) ⟨733607, by rfl⟩ : syracuseStep 978143 = 1467215) B1467215
theorem B1469663 : Blo 976593 1469663 := bstep (se 1 (by rfl) ⟨1102247, by rfl⟩ : syracuseStep 1469663 = 2204495) B2204495
theorem B3304691 : Blo 976593 3304691 := bstep (se 1 (by rfl) ⟨2478518, by rfl⟩ : syracuseStep 3304691 = 4957037) B4957037
theorem B1469705 : Blo 976593 1469705 := bstep (se 2 (by rfl) ⟨551139, by rfl⟩ : syracuseStep 1469705 = 1102279) B1102279
theorem B2977049 : Blo 976593 2977049 := bstep (se 2 (by rfl) ⟨1116393, by rfl⟩ : syracuseStep 2977049 = 2232787) B2232787
theorem B1469807 : Blo 976593 1469807 := bstep (se 1 (by rfl) ⟨1102355, by rfl⟩ : syracuseStep 1469807 = 2204711) B2204711
theorem B978407 : Blo 976593 978407 := bstep (se 1 (by rfl) ⟨733805, by rfl⟩ : syracuseStep 978407 = 1467611) B1467611
theorem B1764839 : Blo 976593 1764839 := bstep (se 1 (by rfl) ⟨1323629, by rfl⟩ : syracuseStep 1764839 = 2647259) B2647259
theorem B1469927 : Blo 976593 1469927 := bstep (se 1 (by rfl) ⟨1102445, by rfl⟩ : syracuseStep 1469927 = 2204891) B2204891
theorem B2387447 : Blo 976593 2387447 := bstep (se 1 (by rfl) ⟨1790585, by rfl⟩ : syracuseStep 2387447 = 3581171) B3581171
theorem B978523 : Blo 976593 978523 := bstep (se 1 (by rfl) ⟨733892, by rfl⟩ : syracuseStep 978523 = 1467785) B1467785
theorem B2977387 : Blo 976593 2977387 := bstep (se 1 (by rfl) ⟨2233040, by rfl⟩ : syracuseStep 2977387 = 4466081) B4466081
theorem B1470059 : Blo 976593 1470059 := bstep (se 1 (by rfl) ⟨1102544, by rfl⟩ : syracuseStep 1470059 = 2205089) B2205089
theorem B1568489 : Blo 976593 1568489 := bstep (se 2 (by rfl) ⟨588183, by rfl⟩ : syracuseStep 1568489 = 1176367) B1176367
theorem B1470185 : Blo 976593 1470185 := bstep (se 2 (by rfl) ⟨551319, by rfl⟩ : syracuseStep 1470185 = 1102639) B1102639
theorem B978759 : Blo 976593 978759 := bstep (se 1 (by rfl) ⟨734069, by rfl⟩ : syracuseStep 978759 = 1468139) B1468139
theorem B9400171 : Blo 976593 9400171 := bstep (se 1 (by rfl) ⟨7050128, by rfl⟩ : syracuseStep 9400171 = 14100257) B14100257
theorem B1470329 : Blo 976593 1470329 := bstep (se 2 (by rfl) ⟨551373, by rfl⟩ : syracuseStep 1470329 = 1102747) B1102747
theorem B2781067 : Blo 976593 2781067 := bstep (se 1 (by rfl) ⟨2085800, by rfl⟩ : syracuseStep 2781067 = 4171601) B4171601
theorem B978911 : Blo 976593 978911 := bstep (se 1 (by rfl) ⟨734183, by rfl⟩ : syracuseStep 978911 = 1468367) B1468367
theorem B1470431 : Blo 976593 1470431 := bstep (se 1 (by rfl) ⟨1102823, by rfl⟩ : syracuseStep 1470431 = 2205647) B2205647
theorem B21426281 : Blo 976593 21426281 := bstep (se 2 (by rfl) ⟨8034855, by rfl⟩ : syracuseStep 21426281 = 16069711) B16069711
theorem B8482981 : Blo 976593 8482981 := bstep (se 4 (by rfl) ⟨795279, by rfl⟩ : syracuseStep 8482981 = 1590559) B1590559
theorem B1470683 : Blo 976593 1470683 := bstep (se 1 (by rfl) ⟨1103012, by rfl⟩ : syracuseStep 1470683 = 2206025) B2206025
theorem B979175 : Blo 976593 979175 := bstep (se 1 (by rfl) ⟨734381, by rfl⟩ : syracuseStep 979175 = 1468763) B1468763
theorem B1470695 : Blo 976593 1470695 := bstep (se 1 (by rfl) ⟨1103021, by rfl⟩ : syracuseStep 1470695 = 2206043) B2206043
theorem B1569079 : Blo 976593 1569079 := bstep (se 1 (by rfl) ⟨1176809, by rfl⟩ : syracuseStep 1569079 = 2353619) B2353619
theorem B979327 : Blo 976593 979327 := bstep (se 1 (by rfl) ⟨734495, by rfl⟩ : syracuseStep 979327 = 1468991) B1468991
theorem B1470857 : Blo 976593 1470857 := bstep (se 2 (by rfl) ⟨551571, by rfl⟩ : syracuseStep 1470857 = 1103143) B1103143
theorem B4518287 : Blo 976593 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B979407 : Blo 976593 979407 := bstep (se 1 (by rfl) ⟨734555, by rfl⟩ : syracuseStep 979407 = 1469111) B1469111
theorem B2978387 : Blo 976593 2978387 := bstep (se 1 (by rfl) ⟨2233790, by rfl⟩ : syracuseStep 2978387 = 4467581) B4467581
theorem B979559 : Blo 976593 979559 := bstep (se 1 (by rfl) ⟨734669, by rfl⟩ : syracuseStep 979559 = 1469339) B1469339
theorem B979823 : Blo 976593 979823 := bstep (se 1 (by rfl) ⟨734867, by rfl⟩ : syracuseStep 979823 = 1469735) B1469735
theorem B3306365 : Blo 976593 3306365 := bstep (se 3 (by rfl) ⟨619943, by rfl⟩ : syracuseStep 3306365 = 1239887) B1239887
theorem B979879 : Blo 976593 979879 := bstep (se 1 (by rfl) ⟨734909, by rfl⟩ : syracuseStep 979879 = 1469819) B1469819
theorem B979963 : Blo 976593 979963 := bstep (se 1 (by rfl) ⟨734972, by rfl⟩ : syracuseStep 979963 = 1469945) B1469945
theorem B980031 : Blo 976593 980031 := bstep (se 1 (by rfl) ⟨735023, by rfl⟩ : syracuseStep 980031 = 1470047) B1470047
theorem B1569899 : Blo 976593 1569899 := bstep (se 1 (by rfl) ⟨1177424, by rfl⟩ : syracuseStep 1569899 = 2354849) B2354849
theorem B18805877 : Blo 976593 18805877 := bstep (se 5 (by rfl) ⟨881525, by rfl⟩ : syracuseStep 18805877 = 1763051) B1763051
theorem B3306635 : Blo 976593 3306635 := bstep (se 1 (by rfl) ⟨2479976, by rfl⟩ : syracuseStep 3306635 = 4959953) B4959953
theorem B1045711 : Blo 976593 1045711 := bstep (se 1 (by rfl) ⟨784283, by rfl⟩ : syracuseStep 1045711 = 1568567) B1568567
theorem B980175 : Blo 976593 980175 := bstep (se 1 (by rfl) ⟨735131, by rfl⟩ : syracuseStep 980175 = 1470263) B1470263
theorem B980379 : Blo 976593 980379 := bstep (se 1 (by rfl) ⟨735284, by rfl⟩ : syracuseStep 980379 = 1470569) B1470569
theorem B980591 : Blo 976593 980591 := bstep (se 1 (by rfl) ⟨735443, by rfl⟩ : syracuseStep 980591 = 1470887) B1470887
theorem B7141067 : Blo 976593 7141067 := bstep (se 1 (by rfl) ⟨5355800, by rfl⟩ : syracuseStep 7141067 = 10711601) B10711601
theorem B1570591 : Blo 976593 1570591 := bstep (se 1 (by rfl) ⟨1177943, by rfl⟩ : syracuseStep 1570591 = 2355887) B2355887
theorem B4945859 : Blo 976593 4945859 := bstep (se 1 (by rfl) ⟨3709394, by rfl⟩ : syracuseStep 4945859 = 7418789) B7418789
theorem B11892815 : Blo 976593 11892815 := bstep (se 1 (by rfl) ⟨8919611, by rfl⟩ : syracuseStep 11892815 = 17839223) B17839223
theorem B12515471 : Blo 976593 12515471 := bstep (se 1 (by rfl) ⟨9386603, by rfl⟩ : syracuseStep 12515471 = 18773207) B18773207
theorem B1046719 : Blo 976593 1046719 := bstep (se 1 (by rfl) ⟨785039, by rfl⟩ : syracuseStep 1046719 = 1570079) B1570079
theorem B4946183 : Blo 976593 4946183 := bstep (se 1 (by rfl) ⟨3709637, by rfl⟩ : syracuseStep 4946183 = 7419275) B7419275
theorem B10320371 : Blo 976593 10320371 := bstep (se 1 (by rfl) ⟨7740278, by rfl⟩ : syracuseStep 10320371 = 15480557) B15480557
theorem B2783801 : Blo 976593 2783801 := bstep (se 2 (by rfl) ⟨1043925, by rfl⟩ : syracuseStep 2783801 = 2087851) B2087851
theorem B32143979 : Blo 976593 32143979 := bstep (se 1 (by rfl) ⟨24107984, by rfl⟩ : syracuseStep 32143979 = 48215969) B48215969
theorem B3308255 : Blo 976593 3308255 := bstep (se 1 (by rfl) ⟨2481191, by rfl⟩ : syracuseStep 3308255 = 4962383) B4962383
theorem B3309011 : Blo 976593 3309011 := bstep (se 1 (by rfl) ⟨2481758, by rfl⟩ : syracuseStep 3309011 = 4963517) B4963517
theorem B5012999 : Blo 976593 5012999 := bstep (se 1 (by rfl) ⟨3759749, by rfl⟩ : syracuseStep 5012999 = 7519499) B7519499
theorem B4947641 : Blo 976593 4947641 := bstep (se 2 (by rfl) ⟨1855365, by rfl⟩ : syracuseStep 4947641 = 3710731) B3710731
theorem B3309281 : Blo 976593 3309281 := bstep (se 2 (by rfl) ⟨1240980, by rfl⟩ : syracuseStep 3309281 = 2481961) B2481961
theorem B5570927 : Blo 976593 5570927 := bstep (se 1 (by rfl) ⟨4178195, by rfl⟩ : syracuseStep 5570927 = 8356391) B8356391
theorem B7930943 : Blo 976593 7930943 := bstep (se 1 (by rfl) ⟨5948207, by rfl⟩ : syracuseStep 7930943 = 11896415) B11896415
theorem B4949099 : Blo 976593 4949099 := bstep (se 1 (by rfl) ⟨3711824, by rfl⟩ : syracuseStep 4949099 = 7423649) B7423649
theorem B4949585 : Blo 976593 4949585 := bstep (se 2 (by rfl) ⟨1856094, by rfl⟩ : syracuseStep 4949585 = 3712189) B3712189
theorem B3770351 : Blo 976593 3770351 := bstep (se 1 (by rfl) ⟨2827763, by rfl⟩ : syracuseStep 3770351 = 5655527) B5655527
theorem B2197691 : Blo 976593 2197691 := bstep (se 1 (by rfl) ⟨1648268, by rfl⟩ : syracuseStep 2197691 = 3296537) B3296537
theorem B2197727 : Blo 976593 2197727 := bstep (se 1 (by rfl) ⟨1648295, by rfl⟩ : syracuseStep 2197727 = 3296591) B3296591
theorem B1673551 : Blo 976593 1673551 := bstep (se 1 (by rfl) ⟨1255163, by rfl⟩ : syracuseStep 1673551 = 2510327) B2510327
theorem B7539101 : Blo 976593 7539101 := bstep (se 3 (by rfl) ⟨1413581, by rfl⟩ : syracuseStep 7539101 = 2827163) B2827163
theorem B2198177 : Blo 976593 2198177 := bstep (se 2 (by rfl) ⟨824316, by rfl⟩ : syracuseStep 2198177 = 1648633) B1648633
theorem B120720145 : Blo 976593 120720145 := bstep (se 2 (by rfl) ⟨45270054, by rfl⟩ : syracuseStep 120720145 = 90540109) B90540109
theorem B2198393 : Blo 976593 2198393 := bstep (se 2 (by rfl) ⟨824397, by rfl⟩ : syracuseStep 2198393 = 1648795) B1648795
theorem B5573569 : Blo 976593 5573569 := bstep (se 2 (by rfl) ⟨2090088, by rfl⟩ : syracuseStep 5573569 = 4180177) B4180177
theorem B12520439 : Blo 976593 12520439 := bstep (se 1 (by rfl) ⟨9390329, by rfl⟩ : syracuseStep 12520439 = 18780659) B18780659
theorem B2198537 : Blo 976593 2198537 := bstep (se 2 (by rfl) ⟨824451, by rfl⟩ : syracuseStep 2198537 = 1648903) B1648903
theorem B2198591 : Blo 976593 2198591 := bstep (se 1 (by rfl) ⟨1648943, by rfl⟩ : syracuseStep 2198591 = 3297887) B3297887
theorem B2788415 : Blo 976593 2788415 := bstep (se 1 (by rfl) ⟨2091311, by rfl⟩ : syracuseStep 2788415 = 4182623) B4182623
theorem B5573843 : Blo 976593 5573843 := bstep (se 1 (by rfl) ⟨4180382, by rfl⟩ : syracuseStep 5573843 = 8360765) B8360765
theorem B2199419 : Blo 976593 2199419 := bstep (se 1 (by rfl) ⟨1649564, by rfl⟩ : syracuseStep 2199419 = 3299129) B3299129
theorem B4952015 : Blo 976593 4952015 := bstep (se 1 (by rfl) ⟨3714011, by rfl⟩ : syracuseStep 4952015 = 7428023) B7428023
theorem B2199527 : Blo 976593 2199527 := bstep (se 1 (by rfl) ⟨1649645, by rfl⟩ : syracuseStep 2199527 = 3299291) B3299291
theorem B2199707 : Blo 976593 2199707 := bstep (se 1 (by rfl) ⟨1649780, by rfl⟩ : syracuseStep 2199707 = 3299561) B3299561
theorem B7934249 : Blo 976593 7934249 := bstep (se 2 (by rfl) ⟨2975343, by rfl⟩ : syracuseStep 7934249 = 5950687) B5950687
theorem B2199905 : Blo 976593 2199905 := bstep (se 2 (by rfl) ⟨824964, by rfl⟩ : syracuseStep 2199905 = 1649929) B1649929
theorem B2199995 : Blo 976593 2199995 := bstep (se 1 (by rfl) ⟨1649996, by rfl⟩ : syracuseStep 2199995 = 3299993) B3299993
theorem B3708089 : Blo 976593 3708089 := bstep (se 2 (by rfl) ⟨1390533, by rfl⟩ : syracuseStep 3708089 = 2781067) B2781067
theorem B353277251 : Blo 976593 353277251 := bstep (se 1 (by rfl) ⟨264957938, by rfl⟩ : syracuseStep 353277251 = 529915877) B529915877
theorem B35755505 : Blo 976593 35755505 := bstep (se 2 (by rfl) ⟨13408314, by rfl⟩ : syracuseStep 35755505 = 26816629) B26816629
theorem B4462073 : Blo 976593 4462073 := bstep (se 2 (by rfl) ⟨1673277, by rfl⟩ : syracuseStep 4462073 = 3346555) B3346555
theorem B11310641 : Blo 976593 11310641 := bstep (se 2 (by rfl) ⟨4241490, by rfl⟩ : syracuseStep 11310641 = 8482981) B8482981
theorem B2201255 : Blo 976593 2201255 := bstep (se 1 (by rfl) ⟨1650941, by rfl⟩ : syracuseStep 2201255 = 3301883) B3301883
theorem B2201435 : Blo 976593 2201435 := bstep (se 1 (by rfl) ⟨1651076, by rfl⟩ : syracuseStep 2201435 = 3302153) B3302153
theorem B2234209 : Blo 976593 2234209 := bstep (se 2 (by rfl) ⟨837828, by rfl⟩ : syracuseStep 2234209 = 1675657) B1675657
theorem B7051283 : Blo 976593 7051283 := bstep (se 1 (by rfl) ⟨5288462, by rfl⟩ : syracuseStep 7051283 = 10576925) B10576925
theorem B2201939 : Blo 976593 2201939 := bstep (se 1 (by rfl) ⟨1651454, by rfl⟩ : syracuseStep 2201939 = 3302909) B3302909
theorem B2202425 : Blo 976593 2202425 := bstep (se 2 (by rfl) ⟨825909, by rfl⟩ : syracuseStep 2202425 = 1651819) B1651819
theorem B2202479 : Blo 976593 2202479 := bstep (se 1 (by rfl) ⟨1651859, by rfl⟩ : syracuseStep 2202479 = 3303719) B3303719
theorem B6265937 : Blo 976593 6265937 := bstep (se 2 (by rfl) ⟨2349726, by rfl⟩ : syracuseStep 6265937 = 4699453) B4699453
theorem B2203055 : Blo 976593 2203055 := bstep (se 1 (by rfl) ⟨1652291, by rfl⟩ : syracuseStep 2203055 = 3304583) B3304583
theorem B2203127 : Blo 976593 2203127 := bstep (se 1 (by rfl) ⟨1652345, by rfl⟩ : syracuseStep 2203127 = 3304691) B3304691
theorem B3710717 : Blo 976593 3710717 := bstep (se 3 (by rfl) ⟨695759, by rfl⟩ : syracuseStep 3710717 = 1391519) B1391519
theorem B3350879 : Blo 976593 3350879 := bstep (se 1 (by rfl) ⟨2513159, by rfl⟩ : syracuseStep 3350879 = 5026319) B5026319
theorem B2204153 : Blo 976593 2204153 := bstep (se 2 (by rfl) ⟨826557, by rfl⟩ : syracuseStep 2204153 = 1653115) B1653115
theorem B2204243 : Blo 976593 2204243 := bstep (se 1 (by rfl) ⟨1653182, by rfl⟩ : syracuseStep 2204243 = 3306365) B3306365
theorem B2204423 : Blo 976593 2204423 := bstep (se 1 (by rfl) ⟨1653317, by rfl⟩ : syracuseStep 2204423 = 3306635) B3306635
theorem B2204513 : Blo 976593 2204513 := bstep (se 2 (by rfl) ⟨826692, by rfl⟩ : syracuseStep 2204513 = 1653385) B1653385
theorem B4760711 : Blo 976593 4760711 := bstep (se 1 (by rfl) ⟨3570533, by rfl⟩ : syracuseStep 4760711 = 7141067) B7141067
theorem B1648201 : Blo 976593 1648201 := bstep (se 2 (by rfl) ⟨618075, by rfl⟩ : syracuseStep 1648201 = 1236151) B1236151
theorem B13772585 : Blo 976593 13772585 := bstep (se 2 (by rfl) ⟨5164719, by rfl⟩ : syracuseStep 13772585 = 10329439) B10329439
theorem B2205503 : Blo 976593 2205503 := bstep (se 1 (by rfl) ⟨1654127, by rfl⟩ : syracuseStep 2205503 = 3308255) B3308255
theorem B1648667 : Blo 976593 1648667 := bstep (se 1 (by rfl) ⟨1236500, by rfl⟩ : syracuseStep 1648667 = 2473001) B2473001
theorem B1648687 : Blo 976593 1648687 := bstep (se 1 (by rfl) ⟨1236515, by rfl⟩ : syracuseStep 1648687 = 2473031) B2473031
theorem B2206007 : Blo 976593 2206007 := bstep (se 1 (by rfl) ⟨1654505, by rfl⟩ : syracuseStep 2206007 = 3309011) B3309011
theorem B2206187 : Blo 976593 2206187 := bstep (se 1 (by rfl) ⟨1654640, by rfl⟩ : syracuseStep 2206187 = 3309281) B3309281
theorem B76294691 : Blo 976593 76294691 := bstep (se 1 (by rfl) ⟨57221018, by rfl⟩ : syracuseStep 76294691 = 114442037) B114442037
theorem B7416359 : Blo 976593 7416359 := bstep (se 1 (by rfl) ⟨5562269, by rfl⟩ : syracuseStep 7416359 = 11124539) B11124539
theorem B3714119 : Blo 976593 3714119 := bstep (se 1 (by rfl) ⟨2785589, by rfl⟩ : syracuseStep 3714119 = 5571179) B5571179
theorem B5582135 : Blo 976593 5582135 := bstep (se 1 (by rfl) ⟨4186601, by rfl⟩ : syracuseStep 5582135 = 8373203) B8373203
theorem B42249559 : Blo 976593 42249559 := bstep (se 1 (by rfl) ⟨31687169, by rfl⟩ : syracuseStep 42249559 = 63374339) B63374339
theorem B4829053 : Blo 976593 4829053 := bstep (se 3 (by rfl) ⟨905447, by rfl⟩ : syracuseStep 4829053 = 1810895) B1810895
theorem B3715105 : Blo 976593 3715105 := bstep (se 2 (by rfl) ⟨1393164, by rfl⟩ : syracuseStep 3715105 = 2786329) B2786329
theorem B4239635 : Blo 976593 4239635 := bstep (se 1 (by rfl) ⟨3179726, by rfl⟩ : syracuseStep 4239635 = 6359453) B6359453
theorem B31732073 : Blo 976593 31732073 := bstep (se 2 (by rfl) ⟨11899527, by rfl⟩ : syracuseStep 31732073 = 23799055) B23799055
theorem B33960329 : Blo 976593 33960329 := bstep (se 2 (by rfl) ⟨12735123, by rfl⟩ : syracuseStep 33960329 = 25470247) B25470247
theorem B3715865 : Blo 976593 3715865 := bstep (se 2 (by rfl) ⟨1393449, by rfl⟩ : syracuseStep 3715865 = 2786899) B2786899
theorem B4961087 : Blo 976593 4961087 := bstep (se 1 (by rfl) ⟨3720815, by rfl⟩ : syracuseStep 4961087 = 7441631) B7441631
theorem B4699009 : Blo 976593 4699009 := bstep (se 2 (by rfl) ⟨1762128, by rfl⟩ : syracuseStep 4699009 = 3524257) B3524257
theorem B1324073 : Blo 976593 1324073 := bstep (se 2 (by rfl) ⟨496527, by rfl⟩ : syracuseStep 1324073 = 993055) B993055
theorem B4699241 : Blo 976593 4699241 := bstep (se 2 (by rfl) ⟨1762215, by rfl⟩ : syracuseStep 4699241 = 3524431) B3524431
theorem B3717035 : Blo 976593 3717035 := bstep (se 1 (by rfl) ⟨2787776, by rfl⟩ : syracuseStep 3717035 = 5575553) B5575553
theorem B4175873 : Blo 976593 4175873 := bstep (se 2 (by rfl) ⟨1565952, by rfl⟩ : syracuseStep 4175873 = 3131905) B3131905
theorem B7518347 : Blo 976593 7518347 := bstep (se 1 (by rfl) ⟨5638760, by rfl⟩ : syracuseStep 7518347 = 11277521) B11277521
theorem B8927495 : Blo 976593 8927495 := bstep (se 1 (by rfl) ⟨6695621, by rfl⟩ : syracuseStep 8927495 = 13391243) B13391243
theorem B10566287 : Blo 976593 10566287 := bstep (se 1 (by rfl) ⟨7924715, by rfl⟩ : syracuseStep 10566287 = 15849431) B15849431
theorem B1981115 : Blo 976593 1981115 := bstep (se 1 (by rfl) ⟨1485836, by rfl⟩ : syracuseStep 1981115 = 2971673) B2971673
theorem B4963031 : Blo 976593 4963031 := bstep (se 1 (by rfl) ⟨3722273, by rfl⟩ : syracuseStep 4963031 = 7444547) B7444547
theorem B8371289 : Blo 976593 8371289 := bstep (se 2 (by rfl) ⟨3139233, by rfl⟩ : syracuseStep 8371289 = 6278467) B6278467
theorem B2473051 : Blo 976593 2473051 := bstep (se 1 (by rfl) ⟨1854788, by rfl⟩ : syracuseStep 2473051 = 3709577) B3709577
theorem B1653851 : Blo 976593 1653851 := bstep (se 1 (by rfl) ⟨1240388, by rfl⟩ : syracuseStep 1653851 = 2480777) B2480777
theorem B1982063 : Blo 976593 1982063 := bstep (se 1 (by rfl) ⟨1486547, by rfl⟩ : syracuseStep 1982063 = 2973095) B2973095
theorem B12533561 : Blo 976593 12533561 := bstep (se 2 (by rfl) ⟨4700085, by rfl⟩ : syracuseStep 12533561 = 9400171) B9400171
theorem B1654607 : Blo 976593 1654607 := bstep (se 1 (by rfl) ⟨1240955, by rfl⟩ : syracuseStep 1654607 = 2481911) B2481911
theorem B9421049 : Blo 976593 9421049 := bstep (se 2 (by rfl) ⟨3532893, by rfl⟩ : syracuseStep 9421049 = 7065787) B7065787
theorem B3391741 : Blo 976593 3391741 := bstep (se 3 (by rfl) ⟨635951, by rfl⟩ : syracuseStep 3391741 = 1271903) B1271903
theorem B17842717 : Blo 976593 17842717 := bstep (se 3 (by rfl) ⟨3345509, by rfl⟩ : syracuseStep 17842717 = 6691019) B6691019
theorem B3719783 : Blo 976593 3719783 := bstep (se 1 (by rfl) ⟨2789837, by rfl⟩ : syracuseStep 3719783 = 5579675) B5579675
theorem B1983791 : Blo 976593 1983791 := bstep (se 1 (by rfl) ⟨1487843, by rfl⟩ : syracuseStep 1983791 = 2975687) B2975687
theorem B1099291 : Blo 976593 1099291 := bstep (se 1 (by rfl) ⟨824468, by rfl⟩ : syracuseStep 1099291 = 1648937) B1648937
theorem B18826789 : Blo 976593 18826789 := bstep (se 4 (by rfl) ⟨1765011, by rfl⟩ : syracuseStep 18826789 = 3530023) B3530023
theorem B1394281 : Blo 976593 1394281 := bstep (se 2 (by rfl) ⟨522855, by rfl⟩ : syracuseStep 1394281 = 1045711) B1045711
theorem B4179563 : Blo 976593 4179563 := bstep (se 1 (by rfl) ⟨3134672, by rfl⟩ : syracuseStep 4179563 = 6269345) B6269345
theorem B1984699 : Blo 976593 1984699 := bstep (se 1 (by rfl) ⟨1488524, by rfl⟩ : syracuseStep 1984699 = 2977049) B2977049
theorem B1591631 : Blo 976593 1591631 := bstep (se 1 (by rfl) ⟨1193723, by rfl⟩ : syracuseStep 1591631 = 2387447) B2387447
theorem B7063969 : Blo 976593 7063969 := bstep (se 2 (by rfl) ⟨2648988, by rfl⟩ : syracuseStep 7063969 = 5297977) B5297977
theorem B16730549 : Blo 976593 16730549 := bstep (se 5 (by rfl) ⟨784244, by rfl⟩ : syracuseStep 16730549 = 1568489) B1568489
theorem B1100335 : Blo 976593 1100335 := bstep (se 1 (by rfl) ⟨825251, by rfl⟩ : syracuseStep 1100335 = 1650503) B1650503
theorem B3296105 : Blo 976593 3296105 := bstep (se 2 (by rfl) ⟨1236039, by rfl⟩ : syracuseStep 3296105 = 2472079) B2472079
theorem B1395625 : Blo 976593 1395625 := bstep (se 2 (by rfl) ⟨523359, by rfl⟩ : syracuseStep 1395625 = 1046719) B1046719
theorem B1100767 : Blo 976593 1100767 := bstep (se 1 (by rfl) ⟨825575, by rfl⟩ : syracuseStep 1100767 = 1651151) B1651151
theorem B2477051 : Blo 976593 2477051 := bstep (se 1 (by rfl) ⟨1857788, by rfl⟩ : syracuseStep 2477051 = 3715577) B3715577
theorem B1985591 : Blo 976593 1985591 := bstep (se 1 (by rfl) ⟨1489193, by rfl⟩ : syracuseStep 1985591 = 2978387) B2978387
theorem B15879397 : Blo 976593 15879397 := bstep (se 4 (by rfl) ⟨1488693, by rfl⟩ : syracuseStep 15879397 = 2977387) B2977387
theorem B12537251 : Blo 976593 12537251 := bstep (se 1 (by rfl) ⟨9402938, by rfl⟩ : syracuseStep 12537251 = 18805877) B18805877
theorem B1101415 : Blo 976593 1101415 := bstep (se 1 (by rfl) ⟨826061, by rfl⟩ : syracuseStep 1101415 = 1652123) B1652123
theorem B1101631 : Blo 976593 1101631 := bstep (se 1 (by rfl) ⟨826223, by rfl⟩ : syracuseStep 1101631 = 1652447) B1652447
theorem B4706237 : Blo 976593 4706237 := bstep (se 3 (by rfl) ⟨882419, by rfl⟩ : syracuseStep 4706237 = 1764839) B1764839
theorem B3297239 : Blo 976593 3297239 := bstep (se 1 (by rfl) ⟨2472929, by rfl⟩ : syracuseStep 3297239 = 4945859) B4945859
theorem B8343647 : Blo 976593 8343647 := bstep (se 1 (by rfl) ⟨6257735, by rfl⟩ : syracuseStep 8343647 = 12515471) B12515471
theorem B1101919 : Blo 976593 1101919 := bstep (se 1 (by rfl) ⟨826439, by rfl⟩ : syracuseStep 1101919 = 1652879) B1652879
theorem B2478235 : Blo 976593 2478235 := bstep (se 1 (by rfl) ⟨1858676, by rfl⟩ : syracuseStep 2478235 = 3717353) B3717353
theorem B3297455 : Blo 976593 3297455 := bstep (se 1 (by rfl) ⟨2473091, by rfl⟩ : syracuseStep 3297455 = 4946183) B4946183
theorem B4182263 : Blo 976593 4182263 := bstep (se 1 (by rfl) ⟨3136697, by rfl⟩ : syracuseStep 4182263 = 6273395) B6273395
theorem B1855867 : Blo 976593 1855867 := bstep (se 1 (by rfl) ⟨1391900, by rfl⟩ : syracuseStep 1855867 = 2783801) B2783801
theorem B3298427 : Blo 976593 3298427 := bstep (se 1 (by rfl) ⟨2473820, by rfl⟩ : syracuseStep 3298427 = 4947641) B4947641
theorem B2086049 : Blo 976593 2086049 := bstep (se 2 (by rfl) ⟨782268, by rfl⟩ : syracuseStep 2086049 = 1564537) B1564537
theorem B28267865 : Blo 976593 28267865 := bstep (se 2 (by rfl) ⟨10600449, by rfl⟩ : syracuseStep 28267865 = 21200899) B21200899
theorem B26760577 : Blo 976593 26760577 := bstep (se 2 (by rfl) ⟨10035216, by rfl⟩ : syracuseStep 26760577 = 20070433) B20070433
theorem B3298697 : Blo 976593 3298697 := bstep (se 2 (by rfl) ⟨1237011, by rfl⟩ : syracuseStep 3298697 = 2474023) B2474023
theorem B2413999 : Blo 976593 2413999 := bstep (se 1 (by rfl) ⟨1810499, by rfl⟩ : syracuseStep 2413999 = 3620999) B3620999
theorem B1856999 : Blo 976593 1856999 := bstep (se 1 (by rfl) ⟨1392749, by rfl⟩ : syracuseStep 1856999 = 2785499) B2785499
theorem B76174987 : Blo 976593 76174987 := bstep (se 1 (by rfl) ⟨57131240, by rfl⟩ : syracuseStep 76174987 = 114262481) B114262481
theorem B6281185 : Blo 976593 6281185 := bstep (se 2 (by rfl) ⟨2355444, by rfl⟩ : syracuseStep 6281185 = 4710889) B4710889
theorem B3135635 : Blo 976593 3135635 := bstep (se 1 (by rfl) ⟨2351726, by rfl⟩ : syracuseStep 3135635 = 4703453) B4703453
theorem B2349881 : Blo 976593 2349881 := bstep (se 2 (by rfl) ⟨881205, by rfl⟩ : syracuseStep 2349881 = 1762411) B1762411
theorem B1465199 : Blo 976593 1465199 := bstep (se 1 (by rfl) ⟨1098899, by rfl⟩ : syracuseStep 1465199 = 2197799) B2197799
theorem B1465211 : Blo 976593 1465211 := bstep (se 1 (by rfl) ⟨1098908, by rfl⟩ : syracuseStep 1465211 = 2197817) B2197817
theorem B2481131 : Blo 976593 2481131 := bstep (se 1 (by rfl) ⟨1860848, by rfl⟩ : syracuseStep 2481131 = 3721697) B3721697
theorem B1236647 : Blo 976593 1236647 := bstep (se 1 (by rfl) ⟨927485, by rfl⟩ : syracuseStep 1236647 = 1854971) B1854971
theorem B1466075 : Blo 976593 1466075 := bstep (se 1 (by rfl) ⟨1099556, by rfl⟩ : syracuseStep 1466075 = 2199113) B2199113
theorem B12541715 : Blo 976593 12541715 := bstep (se 1 (by rfl) ⟨9406286, by rfl⟩ : syracuseStep 12541715 = 18812573) B18812573
theorem B4186039 : Blo 976593 4186039 := bstep (se 1 (by rfl) ⟨3139529, by rfl⟩ : syracuseStep 4186039 = 6279059) B6279059
theorem B1466345 : Blo 976593 1466345 := bstep (se 2 (by rfl) ⟨549879, by rfl⟩ : syracuseStep 1466345 = 1099759) B1099759
theorem B4186397 : Blo 976593 4186397 := bstep (se 3 (by rfl) ⟨784949, by rfl⟩ : syracuseStep 4186397 = 1569899) B1569899
theorem B3137953 : Blo 976593 3137953 := bstep (se 2 (by rfl) ⟨1176732, by rfl⟩ : syracuseStep 3137953 = 2353465) B2353465
theorem B1467047 : Blo 976593 1467047 := bstep (se 1 (by rfl) ⟨1100285, by rfl⟩ : syracuseStep 1467047 = 2200571) B2200571
theorem B1467167 : Blo 976593 1467167 := bstep (se 1 (by rfl) ⟨1100375, by rfl⟩ : syracuseStep 1467167 = 2200751) B2200751
theorem B2974495 : Blo 976593 2974495 := bstep (se 1 (by rfl) ⟨2230871, by rfl⟩ : syracuseStep 2974495 = 4461743) B4461743
theorem B1467191 : Blo 976593 1467191 := bstep (se 1 (by rfl) ⟨1100393, by rfl⟩ : syracuseStep 1467191 = 2200787) B2200787
theorem B1467371 : Blo 976593 1467371 := bstep (se 1 (by rfl) ⟨1100528, by rfl⟩ : syracuseStep 1467371 = 2201057) B2201057
theorem B3531755 : Blo 976593 3531755 := bstep (se 1 (by rfl) ⟨2648816, by rfl⟩ : syracuseStep 3531755 = 5297633) B5297633
theorem B63497357 : Blo 976593 63497357 := bstep (se 3 (by rfl) ⟨11905754, by rfl⟩ : syracuseStep 63497357 = 23811509) B23811509
theorem B2090567 : Blo 976593 2090567 := bstep (se 1 (by rfl) ⟨1567925, by rfl⟩ : syracuseStep 2090567 = 3135851) B3135851
theorem B8349419 : Blo 976593 8349419 := bstep (se 1 (by rfl) ⟨6262064, by rfl⟩ : syracuseStep 8349419 = 12524129) B12524129
theorem B976831 : Blo 976593 976831 := bstep (se 1 (by rfl) ⟨732623, by rfl⟩ : syracuseStep 976831 = 1465247) B1465247
theorem B976863 : Blo 976593 976863 := bstep (se 1 (by rfl) ⟨732647, by rfl⟩ : syracuseStep 976863 = 1465295) B1465295
theorem B976923 : Blo 976593 976923 := bstep (se 1 (by rfl) ⟨732692, by rfl⟩ : syracuseStep 976923 = 1465385) B1465385
theorem B1239067 : Blo 976593 1239067 := bstep (se 1 (by rfl) ⟨929300, by rfl⟩ : syracuseStep 1239067 = 1858601) B1858601
theorem B976927 : Blo 976593 976927 := bstep (se 1 (by rfl) ⟨732695, by rfl⟩ : syracuseStep 976927 = 1465391) B1465391
theorem B976943 : Blo 976593 976943 := bstep (se 1 (by rfl) ⟨732707, by rfl⟩ : syracuseStep 976943 = 1465415) B1465415
theorem B1468463 : Blo 976593 1468463 := bstep (se 1 (by rfl) ⟨1101347, by rfl⟩ : syracuseStep 1468463 = 2202695) B2202695
theorem B977119 : Blo 976593 977119 := bstep (se 1 (by rfl) ⟨732839, by rfl⟩ : syracuseStep 977119 = 1465679) B1465679
theorem B977179 : Blo 976593 977179 := bstep (se 1 (by rfl) ⟨732884, by rfl⟩ : syracuseStep 977179 = 1465769) B1465769
theorem B1468727 : Blo 976593 1468727 := bstep (se 1 (by rfl) ⟨1101545, by rfl⟩ : syracuseStep 1468727 = 2203091) B2203091
theorem B977279 : Blo 976593 977279 := bstep (se 1 (by rfl) ⟨732959, by rfl⟩ : syracuseStep 977279 = 1465919) B1465919
theorem B15853967 : Blo 976593 15853967 := bstep (se 1 (by rfl) ⟨11890475, by rfl⟩ : syracuseStep 15853967 = 23780951) B23780951
theorem B1468907 : Blo 976593 1468907 := bstep (se 1 (by rfl) ⟨1101680, by rfl⟩ : syracuseStep 1468907 = 2203361) B2203361
theorem B1763831 : Blo 976593 1763831 := bstep (se 1 (by rfl) ⟨1322873, by rfl⟩ : syracuseStep 1763831 = 2645747) B2645747
theorem B3762703 : Blo 976593 3762703 := bstep (se 1 (by rfl) ⟨2822027, by rfl⟩ : syracuseStep 3762703 = 5644055) B5644055
theorem B11168279 : Blo 976593 11168279 := bstep (se 1 (by rfl) ⟨8376209, by rfl⟩ : syracuseStep 11168279 = 16752419) B16752419
theorem B3762719 : Blo 976593 3762719 := bstep (se 1 (by rfl) ⟨2822039, by rfl⟩ : syracuseStep 3762719 = 5644079) B5644079
theorem B977455 : Blo 976593 977455 := bstep (se 1 (by rfl) ⟨733091, by rfl⟩ : syracuseStep 977455 = 1466183) B1466183
theorem B977511 : Blo 976593 977511 := bstep (se 1 (by rfl) ⟨733133, by rfl⟩ : syracuseStep 977511 = 1466267) B1466267
theorem B3140491 : Blo 976593 3140491 := bstep (se 1 (by rfl) ⟨2355368, by rfl⟩ : syracuseStep 3140491 = 4710737) B4710737
theorem B977887 : Blo 976593 977887 := bstep (se 1 (by rfl) ⟨733415, by rfl⟩ : syracuseStep 977887 = 1466831) B1466831
theorem B977915 : Blo 976593 977915 := bstep (se 1 (by rfl) ⟨733436, by rfl⟩ : syracuseStep 977915 = 1466873) B1466873
theorem B977983 : Blo 976593 977983 := bstep (se 1 (by rfl) ⟨733487, by rfl⟩ : syracuseStep 977983 = 1466975) B1466975
theorem B2092105 : Blo 976593 2092105 := bstep (se 2 (by rfl) ⟨784539, by rfl⟩ : syracuseStep 2092105 = 1569079) B1569079
theorem B1469609 : Blo 976593 1469609 := bstep (se 2 (by rfl) ⟨551103, by rfl⟩ : syracuseStep 1469609 = 1102207) B1102207
theorem B978303 : Blo 976593 978303 := bstep (se 1 (by rfl) ⟨733727, by rfl⟩ : syracuseStep 978303 = 1467455) B1467455
theorem B978331 : Blo 976593 978331 := bstep (se 1 (by rfl) ⟨733748, by rfl⟩ : syracuseStep 978331 = 1467497) B1467497
theorem B3173855 : Blo 976593 3173855 := bstep (se 1 (by rfl) ⟨2380391, by rfl⟩ : syracuseStep 3173855 = 4760783) B4760783
theorem B978399 : Blo 976593 978399 := bstep (se 1 (by rfl) ⟨733799, by rfl⟩ : syracuseStep 978399 = 1467599) B1467599
theorem B1470023 : Blo 976593 1470023 := bstep (se 1 (by rfl) ⟨1102517, by rfl⟩ : syracuseStep 1470023 = 2205035) B2205035
theorem B978535 : Blo 976593 978535 := bstep (se 1 (by rfl) ⟨733901, by rfl⟩ : syracuseStep 978535 = 1467803) B1467803
theorem B978683 : Blo 976593 978683 := bstep (se 1 (by rfl) ⟨734012, by rfl⟩ : syracuseStep 978683 = 1468025) B1468025
theorem B1470203 : Blo 976593 1470203 := bstep (se 1 (by rfl) ⟨1102652, by rfl⟩ : syracuseStep 1470203 = 2205305) B2205305
theorem B978751 : Blo 976593 978751 := bstep (se 1 (by rfl) ⟨734063, by rfl⟩ : syracuseStep 978751 = 1468127) B1468127
theorem B978815 : Blo 976593 978815 := bstep (se 1 (by rfl) ⟨734111, by rfl⟩ : syracuseStep 978815 = 1468223) B1468223
theorem B8482733 : Blo 976593 8482733 := bstep (se 3 (by rfl) ⟨1590512, by rfl⟩ : syracuseStep 8482733 = 3181025) B3181025
theorem B978927 : Blo 976593 978927 := bstep (se 1 (by rfl) ⟨734195, by rfl⟩ : syracuseStep 978927 = 1468391) B1468391
theorem B978939 : Blo 976593 978939 := bstep (se 1 (by rfl) ⟨734204, by rfl⟩ : syracuseStep 978939 = 1468409) B1468409
theorem B979007 : Blo 976593 979007 := bstep (se 1 (by rfl) ⟨734255, by rfl⟩ : syracuseStep 979007 = 1468511) B1468511
theorem B3305555 : Blo 976593 3305555 := bstep (se 1 (by rfl) ⟨2479166, by rfl⟩ : syracuseStep 3305555 = 4958333) B4958333
theorem B1175647 : Blo 976593 1175647 := bstep (se 1 (by rfl) ⟨881735, by rfl⟩ : syracuseStep 1175647 = 1763471) B1763471
theorem B979047 : Blo 976593 979047 := bstep (se 1 (by rfl) ⟨734285, by rfl⟩ : syracuseStep 979047 = 1468571) B1468571
theorem B979071 : Blo 976593 979071 := bstep (se 1 (by rfl) ⟨734303, by rfl⟩ : syracuseStep 979071 = 1468607) B1468607
theorem B4026511 : Blo 976593 4026511 := bstep (se 1 (by rfl) ⟨3019883, by rfl⟩ : syracuseStep 4026511 = 6039767) B6039767
theorem B979099 : Blo 976593 979099 := bstep (se 1 (by rfl) ⟨734324, by rfl⟩ : syracuseStep 979099 = 1468649) B1468649
theorem B979303 : Blo 976593 979303 := bstep (se 1 (by rfl) ⟨734477, by rfl⟩ : syracuseStep 979303 = 1468955) B1468955
theorem B979355 : Blo 976593 979355 := bstep (se 1 (by rfl) ⟨734516, by rfl⟩ : syracuseStep 979355 = 1469033) B1469033
theorem B1470875 : Blo 976593 1470875 := bstep (se 1 (by rfl) ⟨1103156, by rfl⟩ : syracuseStep 1470875 = 2206313) B2206313
theorem B14086649 : Blo 976593 14086649 := bstep (se 2 (by rfl) ⟨5282493, by rfl⟩ : syracuseStep 14086649 = 10564987) B10564987
theorem B4649567 : Blo 976593 4649567 := bstep (se 1 (by rfl) ⟨3487175, by rfl⟩ : syracuseStep 4649567 = 6974351) B6974351
theorem B30175861 : Blo 976593 30175861 := bstep (se 5 (by rfl) ⟨1414493, by rfl⟩ : syracuseStep 30175861 = 2828987) B2828987
theorem B979707 : Blo 976593 979707 := bstep (se 1 (by rfl) ⟨734780, by rfl⟩ : syracuseStep 979707 = 1469561) B1469561
theorem B979775 : Blo 976593 979775 := bstep (se 1 (by rfl) ⟨734831, by rfl⟩ : syracuseStep 979775 = 1469663) B1469663
theorem B979803 : Blo 976593 979803 := bstep (se 1 (by rfl) ⟨734852, by rfl⟩ : syracuseStep 979803 = 1469705) B1469705
theorem B434664305 : Blo 976593 434664305 := bstep (se 2 (by rfl) ⟨162999114, by rfl⟩ : syracuseStep 434664305 = 325998229) B325998229
theorem B1766281 : Blo 976593 1766281 := bstep (se 2 (by rfl) ⟨662355, by rfl⟩ : syracuseStep 1766281 = 1324711) B1324711
theorem B979871 : Blo 976593 979871 := bstep (se 1 (by rfl) ⟨734903, by rfl⟩ : syracuseStep 979871 = 1469807) B1469807
theorem B979951 : Blo 976593 979951 := bstep (se 1 (by rfl) ⟨734963, by rfl⟩ : syracuseStep 979951 = 1469927) B1469927
theorem B2094121 : Blo 976593 2094121 := bstep (se 2 (by rfl) ⟨785295, by rfl⟩ : syracuseStep 2094121 = 1570591) B1570591
theorem B980039 : Blo 976593 980039 := bstep (se 1 (by rfl) ⟨735029, by rfl⟩ : syracuseStep 980039 = 1470059) B1470059
theorem B980123 : Blo 976593 980123 := bstep (se 1 (by rfl) ⟨735092, by rfl⟩ : syracuseStep 980123 = 1470185) B1470185
theorem B980219 : Blo 976593 980219 := bstep (se 1 (by rfl) ⟨735164, by rfl⟩ : syracuseStep 980219 = 1470329) B1470329
theorem B8353043 : Blo 976593 8353043 := bstep (se 1 (by rfl) ⟨6264782, by rfl⟩ : syracuseStep 8353043 = 12529565) B12529565
theorem B980287 : Blo 976593 980287 := bstep (se 1 (by rfl) ⟨735215, by rfl⟩ : syracuseStep 980287 = 1470431) B1470431
theorem B14284187 : Blo 976593 14284187 := bstep (se 1 (by rfl) ⟨10713140, by rfl⟩ : syracuseStep 14284187 = 21426281) B21426281
theorem B980455 : Blo 976593 980455 := bstep (se 1 (by rfl) ⟨735341, by rfl⟩ : syracuseStep 980455 = 1470683) B1470683
theorem B980463 : Blo 976593 980463 := bstep (se 1 (by rfl) ⟨735347, by rfl⟩ : syracuseStep 980463 = 1470695) B1470695
theorem B980571 : Blo 976593 980571 := bstep (se 1 (by rfl) ⟨735428, by rfl⟩ : syracuseStep 980571 = 1470857) B1470857
theorem B3012191 : Blo 976593 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B2979553 : Blo 976593 2979553 := bstep (se 2 (by rfl) ⟨1117332, by rfl⟩ : syracuseStep 2979553 = 2234665) B2234665
theorem B3307823 : Blo 976593 3307823 := bstep (se 1 (by rfl) ⟨2480867, by rfl⟩ : syracuseStep 3307823 = 4961735) B4961735
theorem B7928543 : Blo 976593 7928543 := bstep (se 1 (by rfl) ⟨5946407, by rfl⟩ : syracuseStep 7928543 = 11892815) B11892815
theorem B7437257 : Blo 976593 7437257 := bstep (se 2 (by rfl) ⟨2788971, by rfl⟩ : syracuseStep 7437257 = 5577943) B5577943
theorem B6880247 : Blo 976593 6880247 := bstep (se 1 (by rfl) ⟨5160185, by rfl⟩ : syracuseStep 6880247 = 10320371) B10320371
theorem B21429319 : Blo 976593 21429319 := bstep (se 1 (by rfl) ⟨16071989, by rfl⟩ : syracuseStep 21429319 = 32143979) B32143979
theorem B38108717 : Blo 976593 38108717 := bstep (se 3 (by rfl) ⟨7145384, by rfl⟩ : syracuseStep 38108717 = 14290769) B14290769
theorem B95223437 : Blo 976593 95223437 := bstep (se 3 (by rfl) ⟨17854394, by rfl⟩ : syracuseStep 95223437 = 35708789) B35708789
theorem B3341999 : Blo 976593 3341999 := bstep (se 1 (by rfl) ⟨2506499, by rfl⟩ : syracuseStep 3341999 = 5012999) B5012999
theorem B4522321 : Blo 976593 4522321 := bstep (se 2 (by rfl) ⟨1695870, by rfl⟩ : syracuseStep 4522321 = 3391741) B3391741
theorem B23790289 : Blo 976593 23790289 := bstep (se 2 (by rfl) ⟨8921358, by rfl⟩ : syracuseStep 23790289 = 17842717) B17842717
theorem B11305693 : Blo 976593 11305693 := bstep (se 3 (by rfl) ⟨2119817, by rfl⟩ : syracuseStep 11305693 = 4239635) B4239635
theorem B3965993 : Blo 976593 3965993 := bstep (se 2 (by rfl) ⟨1487247, by rfl⟩ : syracuseStep 3965993 = 2974495) B2974495
theorem B2786375 : Blo 976593 2786375 := bstep (se 1 (by rfl) ⟨2089781, by rfl⟩ : syracuseStep 2786375 = 4179563) B4179563
theorem B2197403 : Blo 976593 2197403 := bstep (se 1 (by rfl) ⟨1648052, by rfl⟩ : syracuseStep 2197403 = 3296105) B3296105
theorem B25102385 : Blo 976593 25102385 := bstep (se 2 (by rfl) ⟨9413394, by rfl⟩ : syracuseStep 25102385 = 18826789) B18826789
theorem B2197601 : Blo 976593 2197601 := bstep (se 2 (by rfl) ⟨824100, by rfl⟩ : syracuseStep 2197601 = 1648201) B1648201
theorem B8358167 : Blo 976593 8358167 := bstep (se 1 (by rfl) ⟨6268625, by rfl⟩ : syracuseStep 8358167 = 12537251) B12537251
theorem B2198159 : Blo 976593 2198159 := bstep (se 1 (by rfl) ⟨1648619, by rfl⟩ : syracuseStep 2198159 = 3297239) B3297239
theorem B2198249 : Blo 976593 2198249 := bstep (se 2 (by rfl) ⟨824343, by rfl⟩ : syracuseStep 2198249 = 1648687) B1648687
theorem B2198303 : Blo 976593 2198303 := bstep (se 1 (by rfl) ⟨1648727, by rfl⟩ : syracuseStep 2198303 = 3297455) B3297455
theorem B2788175 : Blo 976593 2788175 := bstep (se 1 (by rfl) ⟨2091131, by rfl⟩ : syracuseStep 2788175 = 4182263) B4182263
theorem B2231401 : Blo 976593 2231401 := bstep (se 2 (by rfl) ⟨836775, by rfl⟩ : syracuseStep 2231401 = 1673551) B1673551
theorem B5016937 : Blo 976593 5016937 := bstep (se 2 (by rfl) ⟨1881351, by rfl⟩ : syracuseStep 5016937 = 3762703) B3762703
theorem B2198951 : Blo 976593 2198951 := bstep (se 1 (by rfl) ⟨1649213, by rfl⟩ : syracuseStep 2198951 = 3298427) B3298427
theorem B16977397 : Blo 976593 16977397 := bstep (se 5 (by rfl) ⟨795815, by rfl⟩ : syracuseStep 16977397 = 1591631) B1591631
theorem B18845243 : Blo 976593 18845243 := bstep (se 1 (by rfl) ⟨14133932, by rfl⟩ : syracuseStep 18845243 = 28267865) B28267865
theorem B2199131 : Blo 976593 2199131 := bstep (se 1 (by rfl) ⟨1649348, by rfl⟩ : syracuseStep 2199131 = 3298697) B3298697
theorem B160960193 : Blo 976593 160960193 := bstep (se 2 (by rfl) ⟨60360072, by rfl⟩ : syracuseStep 160960193 = 120720145) B120720145
theorem B7540427 : Blo 976593 7540427 := bstep (se 1 (by rfl) ⟨5655320, by rfl⟩ : syracuseStep 7540427 = 11310641) B11310641
theorem B2789473 : Blo 976593 2789473 := bstep (se 2 (by rfl) ⟨1046052, by rfl⟩ : syracuseStep 2789473 = 2092105) B2092105
theorem B5574845 : Blo 976593 5574845 := bstep (se 3 (by rfl) ⟨1045283, by rfl⟩ : syracuseStep 5574845 = 2090567) B2090567
theorem B21172529 : Blo 976593 21172529 := bstep (se 2 (by rfl) ⟨7939698, by rfl⟩ : syracuseStep 21172529 = 15879397) B15879397
theorem B56332745 : Blo 976593 56332745 := bstep (se 2 (by rfl) ⟨21124779, by rfl⟩ : syracuseStep 56332745 = 42249559) B42249559
theorem B33854453 : Blo 976593 33854453 := bstep (se 5 (by rfl) ⟨1586927, by rfl⟩ : syracuseStep 33854453 = 3173855) B3173855
theorem B8361143 : Blo 976593 8361143 := bstep (se 1 (by rfl) ⟨6270857, by rfl⟩ : syracuseStep 8361143 = 12541715) B12541715
theorem B4953473 : Blo 976593 4953473 := bstep (se 2 (by rfl) ⟨1857552, by rfl⟩ : syracuseStep 4953473 = 3715105) B3715105
theorem B2790931 : Blo 976593 2790931 := bstep (se 1 (by rfl) ⟨2093198, by rfl⟩ : syracuseStep 2790931 = 4186397) B4186397
theorem B2233919 : Blo 976593 2233919 := bstep (se 1 (by rfl) ⟨1675439, by rfl⟩ : syracuseStep 2233919 = 3350879) B3350879
theorem B6265345 : Blo 976593 6265345 := bstep (se 2 (by rfl) ⟨2349504, by rfl⟩ : syracuseStep 6265345 = 4699009) B4699009
theorem B9181723 : Blo 976593 9181723 := bstep (se 1 (by rfl) ⟨6886292, by rfl⟩ : syracuseStep 9181723 = 13772585) B13772585
theorem B2792161 : Blo 976593 2792161 := bstep (se 2 (by rfl) ⟨1047060, by rfl⟩ : syracuseStep 2792161 = 2094121) B2094121
theorem B7445519 : Blo 976593 7445519 := bstep (se 1 (by rfl) ⟨5584139, by rfl⟩ : syracuseStep 7445519 = 11168279) B11168279
theorem B3218665 : Blo 976593 3218665 := bstep (se 2 (by rfl) ⟨1206999, by rfl⟩ : syracuseStep 3218665 = 2413999) B2413999
theorem B3972737 : Blo 976593 3972737 := bstep (se 2 (by rfl) ⟨1489776, by rfl⟩ : syracuseStep 3972737 = 2979553) B2979553
theorem B2203703 : Blo 976593 2203703 := bstep (se 1 (by rfl) ⟨1652777, by rfl⟩ : syracuseStep 2203703 = 3305555) B3305555
theorem B289776203 : Blo 976593 289776203 := bstep (se 1 (by rfl) ⟨217332152, by rfl⟩ : syracuseStep 289776203 = 434664305) B434664305
theorem B2008127 : Blo 976593 2008127 := bstep (se 1 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 2008127 = 3012191) B3012191
theorem B2205215 : Blo 976593 2205215 := bstep (se 1 (by rfl) ⟨1653911, by rfl⟩ : syracuseStep 2205215 = 3307823) B3307823
theorem B5285501 : Blo 976593 5285501 := bstep (se 3 (by rfl) ⟨991031, by rfl⟩ : syracuseStep 5285501 = 1982063) B1982063
theorem B1320743 : Blo 976593 1320743 := bstep (se 1 (by rfl) ⟨990557, by rfl⟩ : syracuseStep 1320743 = 1981115) B1981115
theorem B5285695 : Blo 976593 5285695 := bstep (se 1 (by rfl) ⟨3964271, by rfl⟩ : syracuseStep 5285695 = 7928543) B7928543
theorem B4958171 : Blo 976593 4958171 := bstep (se 1 (by rfl) ⟨3718628, by rfl⟩ : syracuseStep 4958171 = 7437257) B7437257
theorem B5580859 : Blo 976593 5580859 := bstep (se 1 (by rfl) ⟨4185644, by rfl⟩ : syracuseStep 5580859 = 8371289) B8371289
theorem B25405811 : Blo 976593 25405811 := bstep (se 1 (by rfl) ⟨19054358, by rfl⟩ : syracuseStep 25405811 = 38108717) B38108717
theorem B63482291 : Blo 976593 63482291 := bstep (se 1 (by rfl) ⟨47611718, by rfl⟩ : syracuseStep 63482291 = 95223437) B95223437
theorem B5581385 : Blo 976593 5581385 := bstep (se 2 (by rfl) ⟨2093019, by rfl⟩ : syracuseStep 5581385 = 4186039) B4186039
theorem B3713951 : Blo 976593 3713951 := bstep (se 1 (by rfl) ⟨2785463, by rfl⟩ : syracuseStep 3713951 = 5570927) B5570927
theorem B5287295 : Blo 976593 5287295 := bstep (se 1 (by rfl) ⟨3965471, by rfl⟩ : syracuseStep 5287295 = 7930943) B7930943
theorem B12398845 : Blo 976593 12398845 := bstep (se 3 (by rfl) ⟨2324783, by rfl⟩ : syracuseStep 12398845 = 4649567) B4649567
theorem B5026067 : Blo 976593 5026067 := bstep (se 1 (by rfl) ⟨3769550, by rfl⟩ : syracuseStep 5026067 = 7539101) B7539101
theorem B11153699 : Blo 976593 11153699 := bstep (se 1 (by rfl) ⟨8365274, by rfl⟩ : syracuseStep 11153699 = 16730549) B16730549
theorem B1651367 : Blo 976593 1651367 := bstep (se 1 (by rfl) ⟨1238525, by rfl⟩ : syracuseStep 1651367 = 2477051) B2477051
theorem B3715895 : Blo 976593 3715895 := bstep (se 1 (by rfl) ⟨2786921, by rfl⟩ : syracuseStep 3715895 = 5573843) B5573843
theorem B1652089 : Blo 976593 1652089 := bstep (se 2 (by rfl) ⟨619533, by rfl⟩ : syracuseStep 1652089 = 1239067) B1239067
theorem B5289499 : Blo 976593 5289499 := bstep (se 1 (by rfl) ⟨3967124, by rfl⟩ : syracuseStep 5289499 = 7934249) B7934249
theorem B9418625 : Blo 976593 9418625 := bstep (se 2 (by rfl) ⟨3531984, by rfl⟩ : syracuseStep 9418625 = 7063969) B7063969
theorem B1390699 : Blo 976593 1390699 := bstep (se 1 (by rfl) ⟨1043024, by rfl⟩ : syracuseStep 1390699 = 2086049) B2086049
theorem B2472059 : Blo 976593 2472059 := bstep (se 1 (by rfl) ⟨1854044, by rfl⟩ : syracuseStep 2472059 = 3708089) B3708089
theorem B5290109 : Blo 976593 5290109 := bstep (se 3 (by rfl) ⟨991895, by rfl⟩ : syracuseStep 5290109 = 1983791) B1983791
theorem B235518167 : Blo 976593 235518167 := bstep (se 1 (by rfl) ⟨176638625, by rfl⟩ : syracuseStep 235518167 = 353277251) B353277251
theorem B23837003 : Blo 976593 23837003 := bstep (se 1 (by rfl) ⟨17877752, by rfl⟩ : syracuseStep 23837003 = 35755505) B35755505
theorem B4700855 : Blo 976593 4700855 := bstep (se 1 (by rfl) ⟨3525641, by rfl⟩ : syracuseStep 4700855 = 7051283) B7051283
theorem B1654087 : Blo 976593 1654087 := bstep (se 1 (by rfl) ⟨1240565, by rfl⟩ : syracuseStep 1654087 = 2481131) B2481131
theorem B4177291 : Blo 976593 4177291 := bstep (se 1 (by rfl) ⟨3132968, by rfl⟩ : syracuseStep 4177291 = 6265937) B6265937
theorem B6438737 : Blo 976593 6438737 := bstep (se 2 (by rfl) ⟨2414526, by rfl⟩ : syracuseStep 6438737 = 4829053) B4829053
theorem B2473811 : Blo 976593 2473811 := bstep (se 1 (by rfl) ⟨1855358, by rfl⟩ : syracuseStep 2473811 = 3710717) B3710717
theorem B813810037 : Blo 976593 813810037 := bstep (se 5 (by rfl) ⟨38147345, by rfl⟩ : syracuseStep 813810037 = 76294691) B76294691
theorem B2474489 : Blo 976593 2474489 := bstep (se 2 (by rfl) ⟨927933, by rfl⟩ : syracuseStep 2474489 = 1855867) B1855867
theorem B1099111 : Blo 976593 1099111 := bstep (se 1 (by rfl) ⟨824333, by rfl⟩ : syracuseStep 1099111 = 1648667) B1648667
theorem B10569311 : Blo 976593 10569311 := bstep (se 1 (by rfl) ⟨7926983, by rfl⟩ : syracuseStep 10569311 = 15853967) B15853967
theorem B2508479 : Blo 976593 2508479 := bstep (se 1 (by rfl) ⟨1881359, by rfl⟩ : syracuseStep 2508479 = 3762719) B3762719
theorem B2476079 : Blo 976593 2476079 := bstep (se 1 (by rfl) ⟨1857059, by rfl⟩ : syracuseStep 2476079 = 3714119) B3714119
theorem B101566649 : Blo 976593 101566649 := bstep (se 2 (by rfl) ⟨38087493, by rfl⟩ : syracuseStep 101566649 = 76174987) B76174987
theorem B3721423 : Blo 976593 3721423 := bstep (se 1 (by rfl) ⟨2791067, by rfl⟩ : syracuseStep 3721423 = 5582135) B5582135
theorem B5655155 : Blo 976593 5655155 := bstep (se 1 (by rfl) ⟨4241366, by rfl⟩ : syracuseStep 5655155 = 8482733) B8482733
theorem B8374913 : Blo 976593 8374913 := bstep (se 2 (by rfl) ⟨3140592, by rfl⟩ : syracuseStep 8374913 = 6281185) B6281185
theorem B5294909 : Blo 976593 5294909 := bstep (se 3 (by rfl) ⟨992795, by rfl⟩ : syracuseStep 5294909 = 1985591) B1985591
theorem B21154715 : Blo 976593 21154715 := bstep (se 1 (by rfl) ⟨15866036, by rfl⟩ : syracuseStep 21154715 = 31732073) B31732073
theorem B9391099 : Blo 976593 9391099 := bstep (se 1 (by rfl) ⟨7043324, by rfl⟩ : syracuseStep 9391099 = 14086649) B14086649
theorem B2477243 : Blo 976593 2477243 := bstep (se 1 (by rfl) ⟨1857932, by rfl⟩ : syracuseStep 2477243 = 3715865) B3715865
theorem B3132827 : Blo 976593 3132827 := bstep (se 1 (by rfl) ⟨2349620, by rfl⟩ : syracuseStep 3132827 = 4699241) B4699241
theorem B9522791 : Blo 976593 9522791 := bstep (se 1 (by rfl) ⟨7142093, by rfl⟩ : syracuseStep 9522791 = 14284187) B14284187
theorem B2478023 : Blo 976593 2478023 := bstep (se 1 (by rfl) ⟨1858517, by rfl⟩ : syracuseStep 2478023 = 3717035) B3717035
theorem B3297401 : Blo 976593 3297401 := bstep (se 2 (by rfl) ⟨1236525, by rfl⟩ : syracuseStep 3297401 = 2473051) B2473051
theorem B5951663 : Blo 976593 5951663 := bstep (se 1 (by rfl) ⟨4463747, by rfl⟩ : syracuseStep 5951663 = 8927495) B8927495
theorem B3297725 : Blo 976593 3297725 := bstep (se 3 (by rfl) ⟨618323, by rfl⟩ : syracuseStep 3297725 = 1236647) B1236647
theorem B1102567 : Blo 976593 1102567 := bstep (se 1 (by rfl) ⟨826925, by rfl⟩ : syracuseStep 1102567 = 1653851) B1653851
theorem B1103071 : Blo 976593 1103071 := bstep (se 1 (by rfl) ⟨827303, by rfl⟩ : syracuseStep 1103071 = 1654607) B1654607
theorem B6280699 : Blo 976593 6280699 := bstep (se 1 (by rfl) ⟨4710524, by rfl⟩ : syracuseStep 6280699 = 9421049) B9421049
theorem B2479855 : Blo 976593 2479855 := bstep (se 1 (by rfl) ⟨1859891, by rfl⟩ : syracuseStep 2479855 = 3719783) B3719783
theorem B4183937 : Blo 976593 4183937 := bstep (se 2 (by rfl) ⟨1568976, by rfl⟩ : syracuseStep 4183937 = 3137953) B3137953
theorem B3299399 : Blo 976593 3299399 := bstep (se 1 (by rfl) ⟨2474549, by rfl⟩ : syracuseStep 3299399 = 4949099) B4949099
theorem B3299723 : Blo 976593 3299723 := bstep (se 1 (by rfl) ⟨2474792, by rfl⟩ : syracuseStep 3299723 = 4949585) B4949585
theorem B2513567 : Blo 976593 2513567 := bstep (se 1 (by rfl) ⟨1885175, by rfl⟩ : syracuseStep 2513567 = 3770351) B3770351
theorem B1465127 : Blo 976593 1465127 := bstep (se 1 (by rfl) ⟨1098845, by rfl⟩ : syracuseStep 1465127 = 2197691) B2197691
theorem B1465151 : Blo 976593 1465151 := bstep (se 1 (by rfl) ⟨1098863, by rfl⟩ : syracuseStep 1465151 = 2197727) B2197727
theorem B1465451 : Blo 976593 1465451 := bstep (se 1 (by rfl) ⟨1099088, by rfl⟩ : syracuseStep 1465451 = 2198177) B2198177
theorem B1465595 : Blo 976593 1465595 := bstep (se 1 (by rfl) ⟨1099196, by rfl⟩ : syracuseStep 1465595 = 2198393) B2198393
theorem B8346959 : Blo 976593 8346959 := bstep (se 1 (by rfl) ⟨6260219, by rfl⟩ : syracuseStep 8346959 = 12520439) B12520439
theorem B1465691 : Blo 976593 1465691 := bstep (se 1 (by rfl) ⟨1099268, by rfl⟩ : syracuseStep 1465691 = 2198537) B2198537
theorem B1465721 : Blo 976593 1465721 := bstep (se 2 (by rfl) ⟨549645, by rfl⟩ : syracuseStep 1465721 = 1099291) B1099291
theorem B1465727 : Blo 976593 1465727 := bstep (se 1 (by rfl) ⟨1099295, by rfl⟩ : syracuseStep 1465727 = 2198591) B2198591
theorem B1858943 : Blo 976593 1858943 := bstep (se 1 (by rfl) ⟨1394207, by rfl⟩ : syracuseStep 1858943 = 2788415) B2788415
theorem B1859041 : Blo 976593 1859041 := bstep (se 2 (by rfl) ⟨697140, by rfl⟩ : syracuseStep 1859041 = 1394281) B1394281
theorem B1466279 : Blo 976593 1466279 := bstep (se 1 (by rfl) ⟨1099709, by rfl⟩ : syracuseStep 1466279 = 2199419) B2199419
theorem B3137491 : Blo 976593 3137491 := bstep (se 1 (by rfl) ⟨2353118, by rfl⟩ : syracuseStep 3137491 = 4706237) B4706237
theorem B3301343 : Blo 976593 3301343 := bstep (se 1 (by rfl) ⟨2476007, by rfl⟩ : syracuseStep 3301343 = 4952015) B4952015
theorem B1466351 : Blo 976593 1466351 := bstep (se 1 (by rfl) ⟨1099763, by rfl⟩ : syracuseStep 1466351 = 2199527) B2199527
theorem B5562431 : Blo 976593 5562431 := bstep (se 1 (by rfl) ⟨4171823, by rfl⟩ : syracuseStep 5562431 = 8343647) B8343647
theorem B1466471 : Blo 976593 1466471 := bstep (se 1 (by rfl) ⟨1099853, by rfl⟩ : syracuseStep 1466471 = 2199707) B2199707
theorem B3530861 : Blo 976593 3530861 := bstep (se 3 (by rfl) ⟨662036, by rfl⟩ : syracuseStep 3530861 = 1324073) B1324073
theorem B1466603 : Blo 976593 1466603 := bstep (se 1 (by rfl) ⟨1099952, by rfl⟩ : syracuseStep 1466603 = 2199905) B2199905
theorem B2646265 : Blo 976593 2646265 := bstep (se 2 (by rfl) ⟨992349, by rfl⟩ : syracuseStep 2646265 = 1984699) B1984699
theorem B1466663 : Blo 976593 1466663 := bstep (se 1 (by rfl) ⟨1099997, by rfl⟩ : syracuseStep 1466663 = 2199995) B2199995
theorem B1467113 : Blo 976593 1467113 := bstep (se 2 (by rfl) ⟨550167, by rfl⟩ : syracuseStep 1467113 = 1100335) B1100335
theorem B1237999 : Blo 976593 1237999 := bstep (se 1 (by rfl) ⟨928499, by rfl⟩ : syracuseStep 1237999 = 1856999) B1856999
theorem B2974715 : Blo 976593 2974715 := bstep (se 1 (by rfl) ⟨2231036, by rfl⟩ : syracuseStep 2974715 = 4462073) B4462073
theorem B1467503 : Blo 976593 1467503 := bstep (se 1 (by rfl) ⟨1100627, by rfl⟩ : syracuseStep 1467503 = 2201255) B2201255
theorem B4187321 : Blo 976593 4187321 := bstep (se 2 (by rfl) ⟨1570245, by rfl⟩ : syracuseStep 4187321 = 3140491) B3140491
theorem B1860833 : Blo 976593 1860833 := bstep (se 2 (by rfl) ⟨697812, by rfl⟩ : syracuseStep 1860833 = 1395625) B1395625
theorem B1467623 : Blo 976593 1467623 := bstep (se 1 (by rfl) ⟨1100717, by rfl⟩ : syracuseStep 1467623 = 2201435) B2201435
theorem B7431425 : Blo 976593 7431425 := bstep (se 2 (by rfl) ⟨2786784, by rfl⟩ : syracuseStep 7431425 = 5573569) B5573569
theorem B1467689 : Blo 976593 1467689 := bstep (se 2 (by rfl) ⟨550383, by rfl⟩ : syracuseStep 1467689 = 1100767) B1100767
theorem B2090423 : Blo 976593 2090423 := bstep (se 1 (by rfl) ⟨1567817, by rfl⟩ : syracuseStep 2090423 = 3135635) B3135635
theorem B1467959 : Blo 976593 1467959 := bstep (se 1 (by rfl) ⟨1100969, by rfl⟩ : syracuseStep 1467959 = 2201939) B2201939
theorem B1566587 : Blo 976593 1566587 := bstep (se 1 (by rfl) ⟨1174940, by rfl⟩ : syracuseStep 1566587 = 2349881) B2349881
theorem B1468283 : Blo 976593 1468283 := bstep (se 1 (by rfl) ⟨1101212, by rfl⟩ : syracuseStep 1468283 = 2202425) B2202425
theorem B976799 : Blo 976593 976799 := bstep (se 1 (by rfl) ⟨732599, by rfl⟩ : syracuseStep 976799 = 1465199) B1465199
theorem B1468319 : Blo 976593 1468319 := bstep (se 1 (by rfl) ⟨1101239, by rfl⟩ : syracuseStep 1468319 = 2202479) B2202479
theorem B976807 : Blo 976593 976807 := bstep (se 1 (by rfl) ⟨732605, by rfl⟩ : syracuseStep 976807 = 1465211) B1465211
theorem B1468553 : Blo 976593 1468553 := bstep (se 2 (by rfl) ⟨550707, by rfl⟩ : syracuseStep 1468553 = 1101415) B1101415
theorem B1468703 : Blo 976593 1468703 := bstep (se 1 (by rfl) ⟨1101527, by rfl⟩ : syracuseStep 1468703 = 2203055) B2203055
theorem B1468751 : Blo 976593 1468751 := bstep (se 1 (by rfl) ⟨1101563, by rfl⟩ : syracuseStep 1468751 = 2203127) B2203127
theorem B1468841 : Blo 976593 1468841 := bstep (se 2 (by rfl) ⟨550815, by rfl⟩ : syracuseStep 1468841 = 1101631) B1101631
theorem B977383 : Blo 976593 977383 := bstep (se 1 (by rfl) ⟨733037, by rfl⟩ : syracuseStep 977383 = 1466075) B1466075
theorem B977563 : Blo 976593 977563 := bstep (se 1 (by rfl) ⟨733172, by rfl⟩ : syracuseStep 977563 = 1466345) B1466345
theorem B1567529 : Blo 976593 1567529 := bstep (se 2 (by rfl) ⟨587823, by rfl⟩ : syracuseStep 1567529 = 1175647) B1175647
theorem B1469225 : Blo 976593 1469225 := bstep (se 2 (by rfl) ⟨550959, by rfl⟩ : syracuseStep 1469225 = 1101919) B1101919
theorem B5368681 : Blo 976593 5368681 := bstep (se 2 (by rfl) ⟨2013255, by rfl⟩ : syracuseStep 5368681 = 4026511) B4026511
theorem B3304313 : Blo 976593 3304313 := bstep (se 2 (by rfl) ⟨1239117, by rfl⟩ : syracuseStep 3304313 = 2478235) B2478235
theorem B1469435 : Blo 976593 1469435 := bstep (se 1 (by rfl) ⟨1102076, by rfl⟩ : syracuseStep 1469435 = 2204153) B2204153
theorem B1469495 : Blo 976593 1469495 := bstep (se 1 (by rfl) ⟨1102121, by rfl⟩ : syracuseStep 1469495 = 2204243) B2204243
theorem B978031 : Blo 976593 978031 := bstep (se 1 (by rfl) ⟨733523, by rfl⟩ : syracuseStep 978031 = 1467047) B1467047
theorem B1469615 : Blo 976593 1469615 := bstep (se 1 (by rfl) ⟨1102211, by rfl⟩ : syracuseStep 1469615 = 2204423) B2204423
theorem B978111 : Blo 976593 978111 := bstep (se 1 (by rfl) ⟨733583, by rfl⟩ : syracuseStep 978111 = 1467167) B1467167
theorem B978127 : Blo 976593 978127 := bstep (se 1 (by rfl) ⟨733595, by rfl⟩ : syracuseStep 978127 = 1467191) B1467191
theorem B1469675 : Blo 976593 1469675 := bstep (se 1 (by rfl) ⟨1102256, by rfl⟩ : syracuseStep 1469675 = 2204513) B2204513
theorem B978247 : Blo 976593 978247 := bstep (se 1 (by rfl) ⟨733685, by rfl⟩ : syracuseStep 978247 = 1467371) B1467371
theorem B2354503 : Blo 976593 2354503 := bstep (se 1 (by rfl) ⟨1765877, by rfl⟩ : syracuseStep 2354503 = 3531755) B3531755
theorem B3173807 : Blo 976593 3173807 := bstep (se 1 (by rfl) ⟨2380355, by rfl⟩ : syracuseStep 3173807 = 4760711) B4760711
theorem B42331571 : Blo 976593 42331571 := bstep (se 1 (by rfl) ⟨31748678, by rfl⟩ : syracuseStep 42331571 = 63497357) B63497357
theorem B40234481 : Blo 976593 40234481 := bstep (se 2 (by rfl) ⟨15087930, by rfl⟩ : syracuseStep 40234481 = 30175861) B30175861
theorem B5566279 : Blo 976593 5566279 := bstep (se 1 (by rfl) ⟨4174709, by rfl⟩ : syracuseStep 5566279 = 8349419) B8349419
theorem B2355041 : Blo 976593 2355041 := bstep (se 2 (by rfl) ⟨883140, by rfl⟩ : syracuseStep 2355041 = 1766281) B1766281
theorem B1470335 : Blo 976593 1470335 := bstep (se 1 (by rfl) ⟨1102751, by rfl⟩ : syracuseStep 1470335 = 2205503) B2205503
theorem B978975 : Blo 976593 978975 := bstep (se 1 (by rfl) ⟨734231, by rfl⟩ : syracuseStep 978975 = 1468463) B1468463
theorem B979151 : Blo 976593 979151 := bstep (se 1 (by rfl) ⟨734363, by rfl⟩ : syracuseStep 979151 = 1468727) B1468727
theorem B1470671 : Blo 976593 1470671 := bstep (se 1 (by rfl) ⟨1103003, by rfl⟩ : syracuseStep 1470671 = 2206007) B2206007
theorem B979271 : Blo 976593 979271 := bstep (se 1 (by rfl) ⟨734453, by rfl⟩ : syracuseStep 979271 = 1468907) B1468907
theorem B1470791 : Blo 976593 1470791 := bstep (se 1 (by rfl) ⟨1103093, by rfl⟩ : syracuseStep 1470791 = 2206187) B2206187
theorem B1175887 : Blo 976593 1175887 := bstep (se 1 (by rfl) ⟨881915, by rfl⟩ : syracuseStep 1175887 = 1763831) B1763831
theorem B4944239 : Blo 976593 4944239 := bstep (se 1 (by rfl) ⟨3708179, by rfl⟩ : syracuseStep 4944239 = 7416359) B7416359
theorem B35680769 : Blo 976593 35680769 := bstep (se 2 (by rfl) ⟨13380288, by rfl⟩ : syracuseStep 35680769 = 26760577) B26760577
theorem B979739 : Blo 976593 979739 := bstep (se 1 (by rfl) ⟨734804, by rfl⟩ : syracuseStep 979739 = 1469609) B1469609
theorem B980015 : Blo 976593 980015 := bstep (se 1 (by rfl) ⟨735011, by rfl⟩ : syracuseStep 980015 = 1470023) B1470023
theorem B2978945 : Blo 976593 2978945 := bstep (se 2 (by rfl) ⟨1117104, by rfl⟩ : syracuseStep 2978945 = 2234209) B2234209
theorem B980135 : Blo 976593 980135 := bstep (se 1 (by rfl) ⟨735101, by rfl⟩ : syracuseStep 980135 = 1470203) B1470203
theorem B22640219 : Blo 976593 22640219 := bstep (se 1 (by rfl) ⟨16980164, by rfl⟩ : syracuseStep 22640219 = 33960329) B33960329
theorem B980583 : Blo 976593 980583 := bstep (se 1 (by rfl) ⟨735437, by rfl⟩ : syracuseStep 980583 = 1470875) B1470875
theorem B3307391 : Blo 976593 3307391 := bstep (se 1 (by rfl) ⟨2480543, by rfl⟩ : syracuseStep 3307391 = 4961087) B4961087
theorem B5568695 : Blo 976593 5568695 := bstep (se 1 (by rfl) ⟨4176521, by rfl⟩ : syracuseStep 5568695 = 8353043) B8353043
theorem B2783915 : Blo 976593 2783915 := bstep (se 1 (by rfl) ⟨2087936, by rfl⟩ : syracuseStep 2783915 = 4175873) B4175873
theorem B5012231 : Blo 976593 5012231 := bstep (se 1 (by rfl) ⟨3759173, by rfl⟩ : syracuseStep 5012231 = 7518347) B7518347
theorem B28572425 : Blo 976593 28572425 := bstep (se 2 (by rfl) ⟨10714659, by rfl⟩ : syracuseStep 28572425 = 21429319) B21429319
theorem B7044191 : Blo 976593 7044191 := bstep (se 1 (by rfl) ⟨5283143, by rfl⟩ : syracuseStep 7044191 = 10566287) B10566287
theorem B3308687 : Blo 976593 3308687 := bstep (se 1 (by rfl) ⟨2481515, by rfl⟩ : syracuseStep 3308687 = 4963031) B4963031
theorem B4586831 : Blo 976593 4586831 := bstep (se 1 (by rfl) ⟨3440123, by rfl⟩ : syracuseStep 4586831 = 6880247) B6880247
theorem B2227999 : Blo 976593 2227999 := bstep (se 1 (by rfl) ⟨1670999, by rfl⟩ : syracuseStep 2227999 = 3341999) B3341999
theorem B8355707 : Blo 976593 8355707 := bstep (se 1 (by rfl) ⟨6266780, by rfl⟩ : syracuseStep 8355707 = 12533561) B12533561
theorem B6029761 : Blo 976593 6029761 := bstep (se 2 (by rfl) ⟨2261160, by rfl⟩ : syracuseStep 6029761 = 4522321) B4522321
theorem B1085080049 : Blo 976593 1085080049 := bstep (se 2 (by rfl) ⟨406905018, by rfl⟩ : syracuseStep 1085080049 = 813810037) B813810037
theorem B31720385 : Blo 976593 31720385 := bstep (se 2 (by rfl) ⟨11895144, by rfl⟩ : syracuseStep 31720385 = 23790289) B23790289
theorem B15074257 : Blo 976593 15074257 := bstep (se 2 (by rfl) ⟨5652846, by rfl⟩ : syracuseStep 15074257 = 11305693) B11305693
theorem B7046207 : Blo 976593 7046207 := bstep (se 1 (by rfl) ⟨5284655, by rfl⟩ : syracuseStep 7046207 = 10569311) B10569311
theorem B1672319 : Blo 976593 1672319 := bstep (se 1 (by rfl) ⟨1254239, by rfl⟩ : syracuseStep 1672319 = 2508479) B2508479
theorem B5572111 : Blo 976593 5572111 := bstep (se 1 (by rfl) ⟨4179083, by rfl⟩ : syracuseStep 5572111 = 8358167) B8358167
theorem B7047593 : Blo 976593 7047593 := bstep (se 2 (by rfl) ⟨2642847, by rfl⟩ : syracuseStep 7047593 = 5285695) B5285695
theorem B7441145 : Blo 976593 7441145 := bstep (se 2 (by rfl) ⟨2790429, by rfl⟩ : syracuseStep 7441145 = 5580859) B5580859
theorem B2198267 : Blo 976593 2198267 := bstep (se 1 (by rfl) ⟨1648700, by rfl⟩ : syracuseStep 2198267 = 3297401) B3297401
theorem B3967775 : Blo 976593 3967775 := bstep (se 1 (by rfl) ⟨2975831, by rfl⟩ : syracuseStep 3967775 = 5951663) B5951663
theorem B2198483 : Blo 976593 2198483 := bstep (se 1 (by rfl) ⟨1648862, by rfl⟩ : syracuseStep 2198483 = 3297725) B3297725
theorem B37555163 : Blo 976593 37555163 := bstep (se 1 (by rfl) ⟨28166372, by rfl⟩ : syracuseStep 37555163 = 56332745) B56332745
theorem B5574095 : Blo 976593 5574095 := bstep (se 1 (by rfl) ⟨4180571, by rfl⟩ : syracuseStep 5574095 = 8361143) B8361143
theorem B2789291 : Blo 976593 2789291 := bstep (se 1 (by rfl) ⟨2091968, by rfl⟩ : syracuseStep 2789291 = 4183937) B4183937
theorem B12521465 : Blo 976593 12521465 := bstep (se 2 (by rfl) ⟨4695549, by rfl⟩ : syracuseStep 12521465 = 9391099) B9391099
theorem B2199599 : Blo 976593 2199599 := bstep (se 1 (by rfl) ⟨1649699, by rfl⟩ : syracuseStep 2199599 = 3299399) B3299399
theorem B2199815 : Blo 976593 2199815 := bstep (se 1 (by rfl) ⟨1649861, by rfl⟩ : syracuseStep 2199815 = 3299723) B3299723
theorem B1675711 : Blo 976593 1675711 := bstep (se 1 (by rfl) ⟨1256783, by rfl⟩ : syracuseStep 1675711 = 2513567) B2513567
theorem B6689249 : Blo 976593 6689249 := bstep (se 2 (by rfl) ⟨2508468, by rfl⟩ : syracuseStep 6689249 = 5016937) B5016937
theorem B2200895 : Blo 976593 2200895 := bstep (se 1 (by rfl) ⟨1650671, by rfl⟩ : syracuseStep 2200895 = 3301343) B3301343
theorem B3708287 : Blo 976593 3708287 := bstep (se 1 (by rfl) ⟨2781215, by rfl⟩ : syracuseStep 3708287 = 5562431) B5562431
theorem B2791547 : Blo 976593 2791547 := bstep (se 1 (by rfl) ⟨2093660, by rfl⟩ : syracuseStep 2791547 = 4187321) B4187321
theorem B4954283 : Blo 976593 4954283 := bstep (se 1 (by rfl) ⟨3715712, by rfl⟩ : syracuseStep 4954283 = 7431425) B7431425
theorem B15080413 : Blo 976593 15080413 := bstep (se 3 (by rfl) ⟨2827577, by rfl⟩ : syracuseStep 15080413 = 5655155) B5655155
theorem B2202785 : Blo 976593 2202785 := bstep (se 2 (by rfl) ⟨826044, by rfl⟩ : syracuseStep 2202785 = 1652089) B1652089
theorem B2202875 : Blo 976593 2202875 := bstep (se 1 (by rfl) ⟨1652156, by rfl⟩ : syracuseStep 2202875 = 3304313) B3304313
theorem B7052665 : Blo 976593 7052665 := bstep (se 2 (by rfl) ⟨2644749, by rfl⟩ : syracuseStep 7052665 = 5289499) B5289499
theorem B28221047 : Blo 976593 28221047 := bstep (se 1 (by rfl) ⟨21165785, by rfl⟩ : syracuseStep 28221047 = 42331571) B42331571
theorem B3350711 : Blo 976593 3350711 := bstep (se 1 (by rfl) ⟨2513033, by rfl⟩ : syracuseStep 3350711 = 5026067) B5026067
theorem B14099453 : Blo 976593 14099453 := bstep (se 3 (by rfl) ⟨2643647, by rfl⟩ : syracuseStep 14099453 = 5287295) B5287295
theorem B8463485 : Blo 976593 8463485 := bstep (se 3 (by rfl) ⟨1586903, by rfl⟩ : syracuseStep 8463485 = 3173807) B3173807
theorem B2204927 : Blo 976593 2204927 := bstep (se 1 (by rfl) ⟨1653695, by rfl⟩ : syracuseStep 2204927 = 3307391) B3307391
theorem B1648039 : Blo 976593 1648039 := bstep (se 1 (by rfl) ⟨1236029, by rfl⟩ : syracuseStep 1648039 = 2472059) B2472059
theorem B3712463 : Blo 976593 3712463 := bstep (se 1 (by rfl) ⟨2784347, by rfl⟩ : syracuseStep 3712463 = 5568695) B5568695
theorem B10593965 : Blo 976593 10593965 := bstep (se 3 (by rfl) ⟨1986368, by rfl⟩ : syracuseStep 10593965 = 3972737) B3972737
theorem B2205449 : Blo 976593 2205449 := bstep (se 2 (by rfl) ⟨827043, by rfl⟩ : syracuseStep 2205449 = 1654087) B1654087
theorem B19048283 : Blo 976593 19048283 := bstep (se 1 (by rfl) ⟨14286212, by rfl⟩ : syracuseStep 19048283 = 28572425) B28572425
theorem B4696127 : Blo 976593 4696127 := bstep (se 1 (by rfl) ⟨3522095, by rfl⟩ : syracuseStep 4696127 = 7044191) B7044191
theorem B2205791 : Blo 976593 2205791 := bstep (se 1 (by rfl) ⟨1654343, by rfl⟩ : syracuseStep 2205791 = 3308687) B3308687
theorem B3057887 : Blo 976593 3057887 := bstep (se 1 (by rfl) ⟨2293415, by rfl⟩ : syracuseStep 3057887 = 4586831) B4586831
theorem B1649207 : Blo 976593 1649207 := bstep (se 1 (by rfl) ⟨1236905, by rfl⟩ : syracuseStep 1649207 = 2473811) B2473811
theorem B1649659 : Blo 976593 1649659 := bstep (se 1 (by rfl) ⟨1237244, by rfl⟩ : syracuseStep 1649659 = 2474489) B2474489
theorem B1650665 : Blo 976593 1650665 := bstep (se 2 (by rfl) ⟨618999, by rfl⟩ : syracuseStep 1650665 = 1237999) B1237999
theorem B1650719 : Blo 976593 1650719 := bstep (se 1 (by rfl) ⟨1238039, by rfl⟩ : syracuseStep 1650719 = 2476079) B2476079
theorem B67711099 : Blo 976593 67711099 := bstep (se 1 (by rfl) ⟨50783324, by rfl⟩ : syracuseStep 67711099 = 101566649) B101566649
theorem B5583275 : Blo 976593 5583275 := bstep (se 1 (by rfl) ⟨4187456, by rfl⟩ : syracuseStep 5583275 = 8374913) B8374913
theorem B14103143 : Blo 976593 14103143 := bstep (se 1 (by rfl) ⟨10577357, by rfl⟩ : syracuseStep 14103143 = 21154715) B21154715
theorem B1651495 : Blo 976593 1651495 := bstep (se 1 (by rfl) ⟨1238621, by rfl⟩ : syracuseStep 1651495 = 2477243) B2477243
theorem B12563495 : Blo 976593 12563495 := bstep (se 1 (by rfl) ⟨9422621, by rfl⟩ : syracuseStep 12563495 = 18845243) B18845243
theorem B5026951 : Blo 976593 5026951 := bstep (se 1 (by rfl) ⟨3770213, by rfl⟩ : syracuseStep 5026951 = 7540427) B7540427
theorem B1652015 : Blo 976593 1652015 := bstep (se 1 (by rfl) ⟨1239011, by rfl⟩ : syracuseStep 1652015 = 2478023) B2478023
theorem B3716563 : Blo 976593 3716563 := bstep (se 1 (by rfl) ⟨2787422, by rfl⟩ : syracuseStep 3716563 = 5574845) B5574845
theorem B5355005 : Blo 976593 5355005 := bstep (se 3 (by rfl) ⟨1004063, by rfl⟩ : syracuseStep 5355005 = 2008127) B2008127
theorem B4961897 : Blo 976593 4961897 := bstep (se 2 (by rfl) ⟨1860711, by rfl⟩ : syracuseStep 4961897 = 3721423) B3721423
theorem B4962221 : Blo 976593 4962221 := bstep (se 3 (by rfl) ⟨930416, by rfl⟩ : syracuseStep 4962221 = 1860833) B1860833
theorem B1489279 : Blo 976593 1489279 := bstep (se 1 (by rfl) ⟨1116959, by rfl⟩ : syracuseStep 1489279 = 2233919) B2233919
theorem B7158241 : Blo 976593 7158241 := bstep (se 2 (by rfl) ⟨2684340, by rfl⟩ : syracuseStep 7158241 = 5368681) B5368681
theorem B4963679 : Blo 976593 4963679 := bstep (se 1 (by rfl) ⟨3722759, by rfl⟩ : syracuseStep 4963679 = 7445519) B7445519
theorem B3521981 : Blo 976593 3521981 := bstep (se 3 (by rfl) ⟨660371, by rfl⟩ : syracuseStep 3521981 = 1320743) B1320743
theorem B4177565 : Blo 976593 4177565 := bstep (se 3 (by rfl) ⟨783293, by rfl⟩ : syracuseStep 4177565 = 1566587) B1566587
theorem B7421705 : Blo 976593 7421705 := bstep (se 2 (by rfl) ⟨2783139, by rfl⟩ : syracuseStep 7421705 = 5566279) B5566279
theorem B3719297 : Blo 976593 3719297 := bstep (se 2 (by rfl) ⟨1394736, by rfl⟩ : syracuseStep 3719297 = 2789473) B2789473
theorem B16531793 : Blo 976593 16531793 := bstep (se 2 (by rfl) ⟨6199422, by rfl⟩ : syracuseStep 16531793 = 12398845) B12398845
theorem B193184135 : Blo 976593 193184135 := bstep (se 1 (by rfl) ⟨144888101, by rfl⟩ : syracuseStep 193184135 = 289776203) B289776203
theorem B1983143 : Blo 976593 1983143 := bstep (se 1 (by rfl) ⟨1487357, by rfl⟩ : syracuseStep 1983143 = 2974715) B2974715
theorem B1393615 : Blo 976593 1393615 := bstep (se 1 (by rfl) ⟨1045211, by rfl⟩ : syracuseStep 1393615 = 2090423) B2090423
theorem B3523667 : Blo 976593 3523667 := bstep (se 1 (by rfl) ⟨2642750, by rfl⟩ : syracuseStep 3523667 = 5285501) B5285501
theorem B42321527 : Blo 976593 42321527 := bstep (se 1 (by rfl) ⟨31741145, by rfl⟩ : syracuseStep 42321527 = 63482291) B63482291
theorem B3720923 : Blo 976593 3720923 := bstep (se 1 (by rfl) ⟨2790692, by rfl⟩ : syracuseStep 3720923 = 5581385) B5581385
theorem B2475967 : Blo 976593 2475967 := bstep (se 1 (by rfl) ⟨1856975, by rfl⟩ : syracuseStep 2475967 = 3713951) B3713951
theorem B8374265 : Blo 976593 8374265 := bstep (se 2 (by rfl) ⟨3140349, by rfl⟩ : syracuseStep 8374265 = 6280699) B6280699
theorem B3721241 : Blo 976593 3721241 := bstep (se 2 (by rfl) ⟨1395465, by rfl⟩ : syracuseStep 3721241 = 2790931) B2790931
theorem B26822987 : Blo 976593 26822987 := bstep (se 1 (by rfl) ⟨20117240, by rfl⟩ : syracuseStep 26822987 = 40234481) B40234481
theorem B53463797 : Blo 976593 53463797 := bstep (se 5 (by rfl) ⟨2506115, by rfl⟩ : syracuseStep 53463797 = 5012231) B5012231
theorem B1854265 : Blo 976593 1854265 := bstep (se 2 (by rfl) ⟨695349, by rfl⟩ : syracuseStep 1854265 = 1390699) B1390699
theorem B3296159 : Blo 976593 3296159 := bstep (se 1 (by rfl) ⟨2472119, by rfl⟩ : syracuseStep 3296159 = 4944239) B4944239
theorem B1100911 : Blo 976593 1100911 := bstep (se 1 (by rfl) ⟨825683, by rfl⟩ : syracuseStep 1100911 = 1651367) B1651367
theorem B2477263 : Blo 976593 2477263 := bstep (se 1 (by rfl) ⟨1857947, by rfl⟩ : syracuseStep 2477263 = 3715895) B3715895
theorem B12242297 : Blo 976593 12242297 := bstep (se 2 (by rfl) ⟨4590861, by rfl⟩ : syracuseStep 12242297 = 9181723) B9181723
theorem B1985963 : Blo 976593 1985963 := bstep (se 1 (by rfl) ⟨1489472, by rfl⟩ : syracuseStep 1985963 = 2978945) B2978945
theorem B3722881 : Blo 976593 3722881 := bstep (se 2 (by rfl) ⟨1396080, by rfl⟩ : syracuseStep 3722881 = 2792161) B2792161
theorem B15093479 : Blo 976593 15093479 := bstep (se 1 (by rfl) ⟨11320109, by rfl⟩ : syracuseStep 15093479 = 22640219) B22640219
theorem B6279083 : Blo 976593 6279083 := bstep (se 1 (by rfl) ⟨4709312, by rfl⟩ : syracuseStep 6279083 = 9418625) B9418625
theorem B3526739 : Blo 976593 3526739 := bstep (se 1 (by rfl) ⟨2645054, by rfl⟩ : syracuseStep 3526739 = 5290109) B5290109
theorem B157012111 : Blo 976593 157012111 := bstep (se 1 (by rfl) ⟨117759083, by rfl⟩ : syracuseStep 157012111 = 235518167) B235518167
theorem B1855943 : Blo 976593 1855943 := bstep (se 1 (by rfl) ⟨1391957, by rfl⟩ : syracuseStep 1855943 = 2783915) B2783915
theorem B3133903 : Blo 976593 3133903 := bstep (se 1 (by rfl) ⟨2350427, by rfl⟩ : syracuseStep 3133903 = 4700855) B4700855
theorem B2478721 : Blo 976593 2478721 := bstep (se 2 (by rfl) ⟨929520, by rfl⟩ : syracuseStep 2478721 = 1859041) B1859041
theorem B2970665 : Blo 976593 2970665 := bstep (se 2 (by rfl) ⟨1113999, by rfl⟩ : syracuseStep 2970665 = 2227999) B2227999
theorem B4183321 : Blo 976593 4183321 := bstep (se 2 (by rfl) ⟨1568745, by rfl⟩ : syracuseStep 4183321 = 3137491) B3137491
theorem B3528353 : Blo 976593 3528353 := bstep (se 2 (by rfl) ⟨1323132, by rfl⟩ : syracuseStep 3528353 = 2646265) B2646265
theorem B2643995 : Blo 976593 2643995 := bstep (se 1 (by rfl) ⟨1982996, by rfl⟩ : syracuseStep 2643995 = 3965993) B3965993
theorem B1857583 : Blo 976593 1857583 := bstep (se 1 (by rfl) ⟨1393187, by rfl⟩ : syracuseStep 1857583 = 2786375) B2786375
theorem B1464935 : Blo 976593 1464935 := bstep (se 1 (by rfl) ⟨1098701, by rfl⟩ : syracuseStep 1464935 = 2197403) B2197403
theorem B16734923 : Blo 976593 16734923 := bstep (se 1 (by rfl) ⟨12551192, by rfl⟩ : syracuseStep 16734923 = 25102385) B25102385
theorem B1465067 : Blo 976593 1465067 := bstep (se 1 (by rfl) ⟨1098800, by rfl⟩ : syracuseStep 1465067 = 2197601) B2197601
theorem B1465439 : Blo 976593 1465439 := bstep (se 1 (by rfl) ⟨1099079, by rfl⟩ : syracuseStep 1465439 = 2198159) B2198159
theorem B1465481 : Blo 976593 1465481 := bstep (se 2 (by rfl) ⟨549555, by rfl⟩ : syracuseStep 1465481 = 1099111) B1099111
theorem B1465499 : Blo 976593 1465499 := bstep (se 1 (by rfl) ⟨1099124, by rfl⟩ : syracuseStep 1465499 = 2198249) B2198249
theorem B1465535 : Blo 976593 1465535 := bstep (se 1 (by rfl) ⟨1099151, by rfl⟩ : syracuseStep 1465535 = 2198303) B2198303
theorem B3529939 : Blo 976593 3529939 := bstep (se 1 (by rfl) ⟨2647454, by rfl⟩ : syracuseStep 3529939 = 5294909) B5294909
theorem B1858783 : Blo 976593 1858783 := bstep (se 1 (by rfl) ⟨1394087, by rfl⟩ : syracuseStep 1858783 = 2788175) B2788175
theorem B2088551 : Blo 976593 2088551 := bstep (se 1 (by rfl) ⟨1566413, by rfl⟩ : syracuseStep 2088551 = 3132827) B3132827
theorem B1465967 : Blo 976593 1465967 := bstep (se 1 (by rfl) ⟨1099475, by rfl⟩ : syracuseStep 1465967 = 2198951) B2198951
theorem B1466087 : Blo 976593 1466087 := bstep (se 1 (by rfl) ⟨1099565, by rfl⟩ : syracuseStep 1466087 = 2199131) B2199131
theorem B6348527 : Blo 976593 6348527 := bstep (se 1 (by rfl) ⟨4761395, by rfl⟩ : syracuseStep 6348527 = 9522791) B9522791
theorem B107306795 : Blo 976593 107306795 := bstep (se 1 (by rfl) ⟨80480096, by rfl⟩ : syracuseStep 107306795 = 160960193) B160960193
theorem B14115019 : Blo 976593 14115019 := bstep (se 1 (by rfl) ⟨10586264, by rfl⟩ : syracuseStep 14115019 = 21172529) B21172529
theorem B22569635 : Blo 976593 22569635 := bstep (se 1 (by rfl) ⟨16927226, by rfl⟩ : syracuseStep 22569635 = 33854453) B33854453
theorem B3302315 : Blo 976593 3302315 := bstep (se 1 (by rfl) ⟨2476736, by rfl⟩ : syracuseStep 3302315 = 4953473) B4953473
theorem B2975201 : Blo 976593 2975201 := bstep (se 2 (by rfl) ⟨1115700, by rfl⟩ : syracuseStep 2975201 = 2231401) B2231401
theorem B3139337 : Blo 976593 3139337 := bstep (se 2 (by rfl) ⟨1177251, by rfl⟩ : syracuseStep 3139337 = 2354503) B2354503
theorem B976751 : Blo 976593 976751 := bstep (se 1 (by rfl) ⟨732563, by rfl⟩ : syracuseStep 976751 = 1465127) B1465127
theorem B976767 : Blo 976593 976767 := bstep (se 1 (by rfl) ⟨732575, by rfl⟩ : syracuseStep 976767 = 1465151) B1465151
theorem B22636529 : Blo 976593 22636529 := bstep (se 2 (by rfl) ⟨8488698, by rfl⟩ : syracuseStep 22636529 = 16977397) B16977397
theorem B976967 : Blo 976593 976967 := bstep (se 1 (by rfl) ⟨732725, by rfl⟩ : syracuseStep 976967 = 1465451) B1465451
theorem B977063 : Blo 976593 977063 := bstep (se 1 (by rfl) ⟨732797, by rfl⟩ : syracuseStep 977063 = 1465595) B1465595
theorem B5564639 : Blo 976593 5564639 := bstep (se 1 (by rfl) ⟨4173479, by rfl⟩ : syracuseStep 5564639 = 8346959) B8346959
theorem B977127 : Blo 976593 977127 := bstep (se 1 (by rfl) ⟨732845, by rfl⟩ : syracuseStep 977127 = 1465691) B1465691
theorem B977147 : Blo 976593 977147 := bstep (se 1 (by rfl) ⟨732860, by rfl⟩ : syracuseStep 977147 = 1465721) B1465721
theorem B977151 : Blo 976593 977151 := bstep (se 1 (by rfl) ⟨732863, by rfl⟩ : syracuseStep 977151 = 1465727) B1465727
theorem B1239295 : Blo 976593 1239295 := bstep (se 1 (by rfl) ⟨929471, by rfl⟩ : syracuseStep 1239295 = 1858943) B1858943
theorem B977519 : Blo 976593 977519 := bstep (se 1 (by rfl) ⟨733139, by rfl⟩ : syracuseStep 977519 = 1466279) B1466279
theorem B977567 : Blo 976593 977567 := bstep (se 1 (by rfl) ⟨733175, by rfl⟩ : syracuseStep 977567 = 1466351) B1466351
theorem B1469135 : Blo 976593 1469135 := bstep (se 1 (by rfl) ⟨1101851, by rfl⟩ : syracuseStep 1469135 = 2203703) B2203703
theorem B977647 : Blo 976593 977647 := bstep (se 1 (by rfl) ⟨733235, by rfl⟩ : syracuseStep 977647 = 1466471) B1466471
theorem B2353907 : Blo 976593 2353907 := bstep (se 1 (by rfl) ⟨1765430, by rfl⟩ : syracuseStep 2353907 = 3530861) B3530861
theorem B977735 : Blo 976593 977735 := bstep (se 1 (by rfl) ⟨733301, by rfl⟩ : syracuseStep 977735 = 1466603) B1466603
theorem B977775 : Blo 976593 977775 := bstep (se 1 (by rfl) ⟨733331, by rfl⟩ : syracuseStep 977775 = 1466663) B1466663
theorem B1567849 : Blo 976593 1567849 := bstep (se 2 (by rfl) ⟨587943, by rfl⟩ : syracuseStep 1567849 = 1175887) B1175887
theorem B978075 : Blo 976593 978075 := bstep (se 1 (by rfl) ⟨733556, by rfl⟩ : syracuseStep 978075 = 1467113) B1467113
theorem B978335 : Blo 976593 978335 := bstep (se 1 (by rfl) ⟨733751, by rfl⟩ : syracuseStep 978335 = 1467503) B1467503
theorem B978415 : Blo 976593 978415 := bstep (se 1 (by rfl) ⟨733811, by rfl⟩ : syracuseStep 978415 = 1467623) B1467623
theorem B978459 : Blo 976593 978459 := bstep (se 1 (by rfl) ⟨733844, by rfl⟩ : syracuseStep 978459 = 1467689) B1467689
theorem B1470089 : Blo 976593 1470089 := bstep (se 2 (by rfl) ⟨551283, by rfl⟩ : syracuseStep 1470089 = 1102567) B1102567
theorem B1470143 : Blo 976593 1470143 := bstep (se 1 (by rfl) ⟨1102607, by rfl⟩ : syracuseStep 1470143 = 2205215) B2205215
theorem B978639 : Blo 976593 978639 := bstep (se 1 (by rfl) ⟨733979, by rfl⟩ : syracuseStep 978639 = 1467959) B1467959
theorem B978855 : Blo 976593 978855 := bstep (se 1 (by rfl) ⟨734141, by rfl⟩ : syracuseStep 978855 = 1468283) B1468283
theorem B978879 : Blo 976593 978879 := bstep (se 1 (by rfl) ⟨734159, by rfl⟩ : syracuseStep 978879 = 1468319) B1468319
theorem B3305447 : Blo 976593 3305447 := bstep (se 1 (by rfl) ⟨2479085, by rfl⟩ : syracuseStep 3305447 = 4958171) B4958171
theorem B979035 : Blo 976593 979035 := bstep (se 1 (by rfl) ⟨734276, by rfl⟩ : syracuseStep 979035 = 1468553) B1468553
theorem B979135 : Blo 976593 979135 := bstep (se 1 (by rfl) ⟨734351, by rfl⟩ : syracuseStep 979135 = 1468703) B1468703
theorem B979167 : Blo 976593 979167 := bstep (se 1 (by rfl) ⟨734375, by rfl⟩ : syracuseStep 979167 = 1468751) B1468751
theorem B16937207 : Blo 976593 16937207 := bstep (se 1 (by rfl) ⟨12702905, by rfl⟩ : syracuseStep 16937207 = 25405811) B25405811
theorem B979227 : Blo 976593 979227 := bstep (se 1 (by rfl) ⟨734420, by rfl⟩ : syracuseStep 979227 = 1468841) B1468841
theorem B1470761 : Blo 976593 1470761 := bstep (se 2 (by rfl) ⟨551535, by rfl⟩ : syracuseStep 1470761 = 1103071) B1103071
theorem B1045019 : Blo 976593 1045019 := bstep (se 1 (by rfl) ⟨783764, by rfl⟩ : syracuseStep 1045019 = 1567529) B1567529
theorem B979483 : Blo 976593 979483 := bstep (se 1 (by rfl) ⟨734612, by rfl⟩ : syracuseStep 979483 = 1469225) B1469225
theorem B979623 : Blo 976593 979623 := bstep (se 1 (by rfl) ⟨734717, by rfl⟩ : syracuseStep 979623 = 1469435) B1469435
theorem B979663 : Blo 976593 979663 := bstep (se 1 (by rfl) ⟨734747, by rfl⟩ : syracuseStep 979663 = 1469495) B1469495
theorem B979743 : Blo 976593 979743 := bstep (se 1 (by rfl) ⟨734807, by rfl⟩ : syracuseStep 979743 = 1469615) B1469615
theorem B979783 : Blo 976593 979783 := bstep (se 1 (by rfl) ⟨734837, by rfl⟩ : syracuseStep 979783 = 1469675) B1469675
theorem B3306473 : Blo 976593 3306473 := bstep (se 2 (by rfl) ⟨1239927, by rfl⟩ : syracuseStep 3306473 = 2479855) B2479855
theorem B1570027 : Blo 976593 1570027 := bstep (se 1 (by rfl) ⟨1177520, by rfl⟩ : syracuseStep 1570027 = 2355041) B2355041
theorem B980223 : Blo 976593 980223 := bstep (se 1 (by rfl) ⟨735167, by rfl⟩ : syracuseStep 980223 = 1470335) B1470335
theorem B980447 : Blo 976593 980447 := bstep (se 1 (by rfl) ⟨735335, by rfl⟩ : syracuseStep 980447 = 1470671) B1470671
theorem B7435799 : Blo 976593 7435799 := bstep (se 1 (by rfl) ⟨5576849, by rfl⟩ : syracuseStep 7435799 = 11153699) B11153699
theorem B980527 : Blo 976593 980527 := bstep (se 1 (by rfl) ⟨735395, by rfl⟩ : syracuseStep 980527 = 1470791) B1470791
theorem B23787179 : Blo 976593 23787179 := bstep (se 1 (by rfl) ⟨17840384, by rfl⟩ : syracuseStep 23787179 = 35680769) B35680769
theorem B8353793 : Blo 976593 8353793 := bstep (se 2 (by rfl) ⟨3132672, by rfl⟩ : syracuseStep 8353793 = 6265345) B6265345
theorem B15891335 : Blo 976593 15891335 := bstep (se 1 (by rfl) ⟨11918501, by rfl⟩ : syracuseStep 15891335 = 23837003) B23837003
theorem B4291553 : Blo 976593 4291553 := bstep (se 2 (by rfl) ⟨1609332, by rfl⟩ : syracuseStep 4291553 = 3218665) B3218665
theorem B5569721 : Blo 976593 5569721 := bstep (se 2 (by rfl) ⟨2088645, by rfl⟩ : syracuseStep 5569721 = 4177291) B4177291
theorem B17169965 : Blo 976593 17169965 := bstep (se 3 (by rfl) ⟨3219368, by rfl⟩ : syracuseStep 17169965 = 6438737) B6438737
theorem B5570471 : Blo 976593 5570471 := bstep (se 1 (by rfl) ⟨4177853, by rfl⟩ : syracuseStep 5570471 = 8355707) B8355707
theorem B723386699 : Blo 976593 723386699 := bstep (se 1 (by rfl) ⟨542540024, by rfl⟩ : syracuseStep 723386699 = 1085080049) B1085080049
theorem B1114879 : Blo 976593 1114879 := bstep (se 1 (by rfl) ⟨836159, by rfl⟩ : syracuseStep 1114879 = 1672319) B1672319
theorem B28214351 : Blo 976593 28214351 := bstep (se 1 (by rfl) ⟨21160763, by rfl⟩ : syracuseStep 28214351 = 42321527) B42321527
theorem B2786717 : Blo 976593 2786717 := bstep (se 3 (by rfl) ⟨522509, by rfl⟩ : syracuseStep 2786717 = 1045019) B1045019
theorem B2197385 : Blo 976593 2197385 := bstep (se 2 (by rfl) ⟨824019, by rfl⟩ : syracuseStep 2197385 = 1648039) B1648039
theorem B2197439 : Blo 976593 2197439 := bstep (se 1 (by rfl) ⟨1648079, by rfl⟩ : syracuseStep 2197439 = 3296159) B3296159
theorem B25036775 : Blo 976593 25036775 := bstep (se 1 (by rfl) ⟨18777581, by rfl⟩ : syracuseStep 25036775 = 37555163) B37555163
theorem B10062319 : Blo 976593 10062319 := bstep (se 1 (by rfl) ⟨7546739, by rfl⟩ : syracuseStep 10062319 = 15093479) B15093479
theorem B4459499 : Blo 976593 4459499 := bstep (se 1 (by rfl) ⟨3344624, by rfl⟩ : syracuseStep 4459499 = 6689249) B6689249
theorem B2199545 : Blo 976593 2199545 := bstep (se 2 (by rfl) ⟨824829, by rfl⟩ : syracuseStep 2199545 = 1649659) B1649659
theorem B18814031 : Blo 976593 18814031 := bstep (se 1 (by rfl) ⟨14110523, by rfl⟩ : syracuseStep 18814031 = 28221047) B28221047
theorem B4232351 : Blo 976593 4232351 := bstep (se 1 (by rfl) ⟨3174263, by rfl⟩ : syracuseStep 4232351 = 6348527) B6348527
theorem B71537863 : Blo 976593 71537863 := bstep (se 1 (by rfl) ⟨53653397, by rfl⟩ : syracuseStep 71537863 = 107306795) B107306795
theorem B2233807 : Blo 976593 2233807 := bstep (se 1 (by rfl) ⟨1675355, by rfl⟩ : syracuseStep 2233807 = 3350711) B3350711
theorem B90281465 : Blo 976593 90281465 := bstep (se 2 (by rfl) ⟨33855549, by rfl⟩ : syracuseStep 90281465 = 67711099) B67711099
theorem B2201543 : Blo 976593 2201543 := bstep (se 1 (by rfl) ⟨1651157, by rfl⟩ : syracuseStep 2201543 = 3302315) B3302315
theorem B2201993 : Blo 976593 2201993 := bstep (se 2 (by rfl) ⟨825747, by rfl⟩ : syracuseStep 2201993 = 1651495) B1651495
theorem B3709759 : Blo 976593 3709759 := bstep (se 1 (by rfl) ⟨2782319, by rfl⟩ : syracuseStep 3709759 = 5564639) B5564639
theorem B2038591 : Blo 976593 2038591 := bstep (se 1 (by rfl) ⟨1528943, by rfl⟩ : syracuseStep 2038591 = 3057887) B3057887
theorem B5577761 : Blo 976593 5577761 := bstep (se 2 (by rfl) ⟨2091660, by rfl⟩ : syracuseStep 5577761 = 4183321) B4183321
theorem B4955417 : Blo 976593 4955417 := bstep (se 2 (by rfl) ⟨1858281, by rfl⟩ : syracuseStep 4955417 = 3716563) B3716563
theorem B11444141 : Blo 976593 11444141 := bstep (se 3 (by rfl) ⟨2145776, by rfl⟩ : syracuseStep 11444141 = 4291553) B4291553
theorem B2203631 : Blo 976593 2203631 := bstep (se 1 (by rfl) ⟨1652723, by rfl⟩ : syracuseStep 2203631 = 3305447) B3305447
theorem B9544321 : Blo 976593 9544321 := bstep (se 2 (by rfl) ⟨3579120, by rfl⟩ : syracuseStep 9544321 = 7158241) B7158241
theorem B2204315 : Blo 976593 2204315 := bstep (se 1 (by rfl) ⟨1653236, by rfl⟩ : syracuseStep 2204315 = 3306473) B3306473
theorem B32646125 : Blo 976593 32646125 := bstep (se 3 (by rfl) ⟨6121148, by rfl⟩ : syracuseStep 32646125 = 12242297) B12242297
theorem B4957199 : Blo 976593 4957199 := bstep (se 1 (by rfl) ⟨3717899, by rfl⟩ : syracuseStep 4957199 = 7435799) B7435799
theorem B10594223 : Blo 976593 10594223 := bstep (se 1 (by rfl) ⟨7945667, by rfl⟩ : syracuseStep 10594223 = 15891335) B15891335
theorem B3713147 : Blo 976593 3713147 := bstep (se 1 (by rfl) ⟨2784860, by rfl⟩ : syracuseStep 3713147 = 5569721) B5569721
theorem B11446643 : Blo 976593 11446643 := bstep (se 1 (by rfl) ⟨8584982, by rfl⟩ : syracuseStep 11446643 = 17169965) B17169965
theorem B3713647 : Blo 976593 3713647 := bstep (se 1 (by rfl) ⟨2785235, by rfl⟩ : syracuseStep 3713647 = 5570471) B5570471
theorem B11021195 : Blo 976593 11021195 := bstep (se 1 (by rfl) ⟨8265896, by rfl⟩ : syracuseStep 11021195 = 16531793) B16531793
theorem B128789423 : Blo 976593 128789423 := bstep (se 1 (by rfl) ⟨96592067, by rfl⟩ : syracuseStep 128789423 = 193184135) B193184135
theorem B18820025 : Blo 976593 18820025 := bstep (se 2 (by rfl) ⟨7057509, by rfl⟩ : syracuseStep 18820025 = 14115019) B14115019
theorem B1322095 : Blo 976593 1322095 := bstep (se 1 (by rfl) ⟨991571, by rfl⟩ : syracuseStep 1322095 = 1983143) B1983143
theorem B8039681 : Blo 976593 8039681 := bstep (se 2 (by rfl) ⟨3014880, by rfl⟩ : syracuseStep 8039681 = 6029761) B6029761
theorem B21146923 : Blo 976593 21146923 := bstep (se 1 (by rfl) ⟨15860192, by rfl⟩ : syracuseStep 21146923 = 31720385) B31720385
theorem B4697471 : Blo 976593 4697471 := bstep (se 1 (by rfl) ⟨3523103, by rfl⟩ : syracuseStep 4697471 = 7046207) B7046207
theorem B837397925 : Blo 976593 837397925 := bstep (se 4 (by rfl) ⟨78506055, by rfl⟩ : syracuseStep 837397925 = 157012111) B157012111
theorem B20099009 : Blo 976593 20099009 := bstep (se 2 (by rfl) ⟨7537128, by rfl⟩ : syracuseStep 20099009 = 15074257) B15074257
theorem B5582843 : Blo 976593 5582843 := bstep (se 1 (by rfl) ⟨4187132, by rfl⟩ : syracuseStep 5582843 = 8374265) B8374265
theorem B4698395 : Blo 976593 4698395 := bstep (se 1 (by rfl) ⟨3523796, by rfl⟩ : syracuseStep 4698395 = 7047593) B7047593
theorem B4960763 : Blo 976593 4960763 := bstep (se 1 (by rfl) ⟨3720572, by rfl⟩ : syracuseStep 4960763 = 7441145) B7441145
theorem B3716063 : Blo 976593 3716063 := bstep (se 1 (by rfl) ⟨2787047, by rfl⟩ : syracuseStep 3716063 = 5574095) B5574095
theorem B1652393 : Blo 976593 1652393 := bstep (se 2 (by rfl) ⟨619647, by rfl⟩ : syracuseStep 1652393 = 1239295) B1239295
theorem B1980443 : Blo 976593 1980443 := bstep (se 1 (by rfl) ⟨1485332, by rfl⟩ : syracuseStep 1980443 = 2970665) B2970665
theorem B2472191 : Blo 976593 2472191 := bstep (se 1 (by rfl) ⟨1854143, by rfl⟩ : syracuseStep 2472191 = 3708287) B3708287
theorem B2472353 : Blo 976593 2472353 := bstep (se 2 (by rfl) ⟨927132, by rfl⟩ : syracuseStep 2472353 = 1854265) B1854265
theorem B11156615 : Blo 976593 11156615 := bstep (se 1 (by rfl) ⟨8367461, by rfl⟩ : syracuseStep 11156615 = 16734923) B16734923
theorem B4963841 : Blo 976593 4963841 := bstep (se 2 (by rfl) ⟨1861440, by rfl⟩ : syracuseStep 4963841 = 3722881) B3722881
theorem B4178537 : Blo 976593 4178537 := bstep (se 2 (by rfl) ⟨1566951, by rfl⟩ : syracuseStep 4178537 = 3133903) B3133903
theorem B2474975 : Blo 976593 2474975 := bstep (se 1 (by rfl) ⟨1856231, by rfl⟩ : syracuseStep 2474975 = 3712463) B3712463
theorem B1983467 : Blo 976593 1983467 := bstep (se 1 (by rfl) ⟨1487600, by rfl⟩ : syracuseStep 1983467 = 2975201) B2975201
theorem B7062643 : Blo 976593 7062643 := bstep (se 1 (by rfl) ⟨5296982, by rfl⟩ : syracuseStep 7062643 = 10593965) B10593965
theorem B12698855 : Blo 976593 12698855 := bstep (se 1 (by rfl) ⟨9524141, by rfl⟩ : syracuseStep 12698855 = 19048283) B19048283
theorem B15091019 : Blo 976593 15091019 := bstep (se 1 (by rfl) ⟨11318264, by rfl⟩ : syracuseStep 15091019 = 22636529) B22636529
theorem B3130751 : Blo 976593 3130751 := bstep (se 1 (by rfl) ⟨2348063, by rfl⟩ : syracuseStep 3130751 = 4696127) B4696127
theorem B6702601 : Blo 976593 6702601 := bstep (se 2 (by rfl) ⟨2513475, by rfl⟩ : syracuseStep 6702601 = 5026951) B5026951
theorem B1099471 : Blo 976593 1099471 := bstep (se 1 (by rfl) ⟨824603, by rfl⟩ : syracuseStep 1099471 = 1649207) B1649207
theorem B6277085 : Blo 976593 6277085 := bstep (se 3 (by rfl) ⟨1176953, by rfl⟩ : syracuseStep 6277085 = 2353907) B2353907
theorem B1100443 : Blo 976593 1100443 := bstep (se 1 (by rfl) ⟨825332, by rfl⟩ : syracuseStep 1100443 = 1650665) B1650665
theorem B1100479 : Blo 976593 1100479 := bstep (se 1 (by rfl) ⟨825359, by rfl⟩ : syracuseStep 1100479 = 1650719) B1650719
theorem B2476777 : Blo 976593 2476777 := bstep (se 2 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 2476777 = 1857583) B1857583
theorem B11291471 : Blo 976593 11291471 := bstep (se 1 (by rfl) ⟨8468603, by rfl⟩ : syracuseStep 11291471 = 16937207) B16937207
theorem B3722183 : Blo 976593 3722183 := bstep (se 1 (by rfl) ⟨2791637, by rfl⟩ : syracuseStep 3722183 = 5583275) B5583275
theorem B1985705 : Blo 976593 1985705 := bstep (se 2 (by rfl) ⟨744639, by rfl⟩ : syracuseStep 1985705 = 1489279) B1489279
theorem B8375663 : Blo 976593 8375663 := bstep (se 1 (by rfl) ⟨6281747, by rfl⟩ : syracuseStep 8375663 = 12563495) B12563495
theorem B1101343 : Blo 976593 1101343 := bstep (se 1 (by rfl) ⟨826007, by rfl⟩ : syracuseStep 1101343 = 1652015) B1652015
theorem B5295901 : Blo 976593 5295901 := bstep (se 3 (by rfl) ⟨992981, by rfl⟩ : syracuseStep 5295901 = 1985963) B1985963
theorem B9391949 : Blo 976593 9391949 := bstep (se 3 (by rfl) ⟨1760990, by rfl⟩ : syracuseStep 9391949 = 3521981) B3521981
theorem B20107217 : Blo 976593 20107217 := bstep (se 2 (by rfl) ⟨7540206, by rfl⟩ : syracuseStep 20107217 = 15080413) B15080413
theorem B4706585 : Blo 976593 4706585 := bstep (se 2 (by rfl) ⟨1764969, by rfl⟩ : syracuseStep 4706585 = 3529939) B3529939
theorem B2478377 : Blo 976593 2478377 := bstep (se 2 (by rfl) ⟨929391, by rfl⟩ : syracuseStep 2478377 = 1858783) B1858783
theorem B2479531 : Blo 976593 2479531 := bstep (se 1 (by rfl) ⟨1859648, by rfl⟩ : syracuseStep 2479531 = 3719297) B3719297
theorem B2480615 : Blo 976593 2480615 := bstep (se 1 (by rfl) ⟨1860461, by rfl⟩ : syracuseStep 2480615 = 3720923) B3720923
theorem B1858153 : Blo 976593 1858153 := bstep (se 2 (by rfl) ⟨696807, by rfl⟩ : syracuseStep 1858153 = 1393615) B1393615
theorem B2480827 : Blo 976593 2480827 := bstep (se 1 (by rfl) ⟨1860620, by rfl⟩ : syracuseStep 2480827 = 3721241) B3721241
theorem B17881991 : Blo 976593 17881991 := bstep (se 1 (by rfl) ⟨13411493, by rfl⟩ : syracuseStep 17881991 = 26822987) B26822987
theorem B60185693 : Blo 976593 60185693 := bstep (se 3 (by rfl) ⟨11284817, by rfl⟩ : syracuseStep 60185693 = 22569635) B22569635
theorem B35642531 : Blo 976593 35642531 := bstep (se 1 (by rfl) ⟨26731898, by rfl⟩ : syracuseStep 35642531 = 53463797) B53463797
theorem B1465511 : Blo 976593 1465511 := bstep (se 1 (by rfl) ⟨1099133, by rfl⟩ : syracuseStep 1465511 = 2198267) B2198267
theorem B2645183 : Blo 976593 2645183 := bstep (se 1 (by rfl) ⟨1983887, by rfl⟩ : syracuseStep 2645183 = 3967775) B3967775
theorem B1465655 : Blo 976593 1465655 := bstep (se 1 (by rfl) ⟨1099241, by rfl⟩ : syracuseStep 1465655 = 2198483) B2198483
theorem B7429481 : Blo 976593 7429481 := bstep (se 2 (by rfl) ⟨2786055, by rfl⟩ : syracuseStep 7429481 = 5572111) B5572111
theorem B8937125 : Blo 976593 8937125 := bstep (se 4 (by rfl) ⟨837855, by rfl⟩ : syracuseStep 8937125 = 1675711) B1675711
theorem B3301289 : Blo 976593 3301289 := bstep (se 2 (by rfl) ⟨1237983, by rfl⟩ : syracuseStep 3301289 = 2475967) B2475967
theorem B1859527 : Blo 976593 1859527 := bstep (se 1 (by rfl) ⟨1394645, by rfl⟩ : syracuseStep 1859527 = 2789291) B2789291
theorem B4186055 : Blo 976593 4186055 := bstep (se 1 (by rfl) ⟨3139541, by rfl⟩ : syracuseStep 4186055 = 6279083) B6279083
theorem B8347643 : Blo 976593 8347643 := bstep (se 1 (by rfl) ⟨6260732, by rfl⟩ : syracuseStep 8347643 = 12521465) B12521465
theorem B1466399 : Blo 976593 1466399 := bstep (se 1 (by rfl) ⟨1099799, by rfl⟩ : syracuseStep 1466399 = 2199599) B2199599
theorem B2351159 : Blo 976593 2351159 := bstep (se 1 (by rfl) ⟨1763369, by rfl⟩ : syracuseStep 2351159 = 3526739) B3526739
theorem B1466543 : Blo 976593 1466543 := bstep (se 1 (by rfl) ⟨1099907, by rfl⟩ : syracuseStep 1466543 = 2199815) B2199815
theorem B9396445 : Blo 976593 9396445 := bstep (se 3 (by rfl) ⟨1761833, by rfl⟩ : syracuseStep 9396445 = 3523667) B3523667
theorem B1237295 : Blo 976593 1237295 := bstep (se 1 (by rfl) ⟨927971, by rfl⟩ : syracuseStep 1237295 = 1855943) B1855943
theorem B22569293 : Blo 976593 22569293 := bstep (se 3 (by rfl) ⟨4231742, by rfl⟩ : syracuseStep 22569293 = 8463485) B8463485
theorem B1467263 : Blo 976593 1467263 := bstep (se 1 (by rfl) ⟨1100447, by rfl⟩ : syracuseStep 1467263 = 2200895) B2200895
theorem B2352235 : Blo 976593 2352235 := bstep (se 1 (by rfl) ⟨1764176, by rfl⟩ : syracuseStep 2352235 = 3528353) B3528353
theorem B14280013 : Blo 976593 14280013 := bstep (se 3 (by rfl) ⟨2677502, by rfl⟩ : syracuseStep 14280013 = 5355005) B5355005
theorem B1762663 : Blo 976593 1762663 := bstep (se 1 (by rfl) ⟨1321997, by rfl⟩ : syracuseStep 1762663 = 2643995) B2643995
theorem B1861031 : Blo 976593 1861031 := bstep (se 1 (by rfl) ⟨1395773, by rfl⟩ : syracuseStep 1861031 = 2791547) B2791547
theorem B3302855 : Blo 976593 3302855 := bstep (se 1 (by rfl) ⟨2477141, by rfl⟩ : syracuseStep 3302855 = 4954283) B4954283
theorem B2090465 : Blo 976593 2090465 := bstep (se 2 (by rfl) ⟨783924, by rfl⟩ : syracuseStep 2090465 = 1567849) B1567849
theorem B1467881 : Blo 976593 1467881 := bstep (se 2 (by rfl) ⟨550455, by rfl⟩ : syracuseStep 1467881 = 1100911) B1100911
theorem B3303017 : Blo 976593 3303017 := bstep (se 2 (by rfl) ⟨1238631, by rfl⟩ : syracuseStep 3303017 = 2477263) B2477263
theorem B976623 : Blo 976593 976623 := bstep (se 1 (by rfl) ⟨732467, by rfl⟩ : syracuseStep 976623 = 1464935) B1464935
theorem B976711 : Blo 976593 976711 := bstep (se 1 (by rfl) ⟨732533, by rfl⟩ : syracuseStep 976711 = 1465067) B1465067
theorem B976959 : Blo 976593 976959 := bstep (se 1 (by rfl) ⟨732719, by rfl⟩ : syracuseStep 976959 = 1465439) B1465439
theorem B976987 : Blo 976593 976987 := bstep (se 1 (by rfl) ⟨732740, by rfl⟩ : syracuseStep 976987 = 1465481) B1465481
theorem B976999 : Blo 976593 976999 := bstep (se 1 (by rfl) ⟨732749, by rfl⟩ : syracuseStep 976999 = 1465499) B1465499
theorem B1468523 : Blo 976593 1468523 := bstep (se 1 (by rfl) ⟨1101392, by rfl⟩ : syracuseStep 1468523 = 2202785) B2202785
theorem B977023 : Blo 976593 977023 := bstep (se 1 (by rfl) ⟨732767, by rfl⟩ : syracuseStep 977023 = 1465535) B1465535
theorem B1468583 : Blo 976593 1468583 := bstep (se 1 (by rfl) ⟨1101437, by rfl⟩ : syracuseStep 1468583 = 2202875) B2202875
theorem B977311 : Blo 976593 977311 := bstep (se 1 (by rfl) ⟨732983, by rfl⟩ : syracuseStep 977311 = 1465967) B1465967
theorem B977391 : Blo 976593 977391 := bstep (se 1 (by rfl) ⟨733043, by rfl⟩ : syracuseStep 977391 = 1466087) B1466087
theorem B9399635 : Blo 976593 9399635 := bstep (se 1 (by rfl) ⟨7049726, by rfl⟩ : syracuseStep 9399635 = 14099453) B14099453
theorem B1469951 : Blo 976593 1469951 := bstep (se 1 (by rfl) ⟨1102463, by rfl⟩ : syracuseStep 1469951 = 2204927) B2204927
theorem B3304961 : Blo 976593 3304961 := bstep (se 2 (by rfl) ⟨1239360, by rfl⟩ : syracuseStep 3304961 = 2478721) B2478721
theorem B2092891 : Blo 976593 2092891 := bstep (se 1 (by rfl) ⟨1569668, by rfl⟩ : syracuseStep 2092891 = 3139337) B3139337
theorem B1470299 : Blo 976593 1470299 := bstep (se 1 (by rfl) ⟨1102724, by rfl⟩ : syracuseStep 1470299 = 2205449) B2205449
theorem B1470527 : Blo 976593 1470527 := bstep (se 1 (by rfl) ⟨1102895, by rfl⟩ : syracuseStep 1470527 = 2205791) B2205791
theorem B2093369 : Blo 976593 2093369 := bstep (se 2 (by rfl) ⟨785013, by rfl⟩ : syracuseStep 2093369 = 1570027) B1570027
theorem B979423 : Blo 976593 979423 := bstep (se 1 (by rfl) ⟨734567, by rfl⟩ : syracuseStep 979423 = 1469135) B1469135
theorem B980059 : Blo 976593 980059 := bstep (se 1 (by rfl) ⟨735044, by rfl⟩ : syracuseStep 980059 = 1470089) B1470089
theorem B980095 : Blo 976593 980095 := bstep (se 1 (by rfl) ⟨735071, by rfl⟩ : syracuseStep 980095 = 1470143) B1470143
theorem B980507 : Blo 976593 980507 := bstep (se 1 (by rfl) ⟨735380, by rfl⟩ : syracuseStep 980507 = 1470761) B1470761
theorem B9402095 : Blo 976593 9402095 := bstep (se 1 (by rfl) ⟨7051571, by rfl⟩ : syracuseStep 9402095 = 14103143) B14103143
theorem B3307931 : Blo 976593 3307931 := bstep (se 1 (by rfl) ⟨2480948, by rfl⟩ : syracuseStep 3307931 = 4961897) B4961897
theorem B15858119 : Blo 976593 15858119 := bstep (se 1 (by rfl) ⟨11893589, by rfl⟩ : syracuseStep 15858119 = 23787179) B23787179
theorem B3308147 : Blo 976593 3308147 := bstep (se 1 (by rfl) ⟨2481110, by rfl⟩ : syracuseStep 3308147 = 4962221) B4962221
theorem B5569195 : Blo 976593 5569195 := bstep (se 1 (by rfl) ⟨4176896, by rfl⟩ : syracuseStep 5569195 = 8353793) B8353793
theorem B5569469 : Blo 976593 5569469 := bstep (se 3 (by rfl) ⟨1044275, by rfl⟩ : syracuseStep 5569469 = 2088551) B2088551
theorem B9403553 : Blo 976593 9403553 := bstep (se 2 (by rfl) ⟨3526332, by rfl⟩ : syracuseStep 9403553 = 7052665) B7052665
theorem B3309119 : Blo 976593 3309119 := bstep (se 1 (by rfl) ⟨2481839, by rfl⟩ : syracuseStep 3309119 = 4963679) B4963679
theorem B2785043 : Blo 976593 2785043 := bstep (se 1 (by rfl) ⟨2088782, by rfl⟩ : syracuseStep 2785043 = 4177565) B4177565
theorem B4947803 : Blo 976593 4947803 := bstep (se 1 (by rfl) ⟨3710852, by rfl⟩ : syracuseStep 4947803 = 7421705) B7421705
theorem B2785691 : Blo 976593 2785691 := bstep (se 1 (by rfl) ⟨2089268, by rfl⟩ : syracuseStep 2785691 = 4178537) B4178537
theorem B18809567 : Blo 976593 18809567 := bstep (se 1 (by rfl) ⟨14107175, by rfl⟩ : syracuseStep 18809567 = 28214351) B28214351
theorem B10060679 : Blo 976593 10060679 := bstep (se 1 (by rfl) ⟨7545509, by rfl⟩ : syracuseStep 10060679 = 15091019) B15091019
theorem B19040017 : Blo 976593 19040017 := bstep (se 2 (by rfl) ⟨7140006, by rfl⟩ : syracuseStep 19040017 = 14280013) B14280013
theorem B6261299 : Blo 976593 6261299 := bstep (se 1 (by rfl) ⟨4695974, by rfl⟩ : syracuseStep 6261299 = 9391949) B9391949
theorem B13404811 : Blo 976593 13404811 := bstep (se 1 (by rfl) ⟨10053608, by rfl⟩ : syracuseStep 13404811 = 20107217) B20107217
theorem B2821567 : Blo 976593 2821567 := bstep (se 1 (by rfl) ⟨2116175, by rfl⟩ : syracuseStep 2821567 = 4232351) B4232351
theorem B4951529 : Blo 976593 4951529 := bstep (se 2 (by rfl) ⟨1856823, by rfl⟩ : syracuseStep 4951529 = 3713647) B3713647
theorem B23761687 : Blo 976593 23761687 := bstep (se 1 (by rfl) ⟨17821265, by rfl⟩ : syracuseStep 23761687 = 35642531) B35642531
theorem B4952987 : Blo 976593 4952987 := bstep (se 1 (by rfl) ⟨3714740, by rfl⟩ : syracuseStep 4952987 = 7429481) B7429481
theorem B2790521 : Blo 976593 2790521 := bstep (se 2 (by rfl) ⟨1046445, by rfl⟩ : syracuseStep 2790521 = 2092891) B2092891
theorem B2200859 : Blo 976593 2200859 := bstep (se 1 (by rfl) ⟨1650644, by rfl⟩ : syracuseStep 2200859 = 3301289) B3301289
theorem B2790703 : Blo 976593 2790703 := bstep (se 1 (by rfl) ⟨2093027, by rfl⟩ : syracuseStep 2790703 = 4186055) B4186055
theorem B15046195 : Blo 976593 15046195 := bstep (se 1 (by rfl) ⟨11284646, by rfl⟩ : syracuseStep 15046195 = 22569293) B22569293
theorem B2201903 : Blo 976593 2201903 := bstep (se 1 (by rfl) ⟨1651427, by rfl⟩ : syracuseStep 2201903 = 3302855) B3302855
theorem B2202011 : Blo 976593 2202011 := bstep (se 1 (by rfl) ⟨1651508, by rfl⟩ : syracuseStep 2202011 = 3303017) B3303017
theorem B85859615 : Blo 976593 85859615 := bstep (se 1 (by rfl) ⟨64394711, by rfl⟩ : syracuseStep 85859615 = 128789423) B128789423
theorem B6266423 : Blo 976593 6266423 := bstep (se 1 (by rfl) ⟨4699817, by rfl⟩ : syracuseStep 6266423 = 9399635) B9399635
theorem B2203307 : Blo 976593 2203307 := bstep (se 1 (by rfl) ⟨1652480, by rfl⟩ : syracuseStep 2203307 = 3304961) B3304961
theorem B25076141 : Blo 976593 25076141 := bstep (se 3 (by rfl) ⟨4701776, by rfl⟩ : syracuseStep 25076141 = 9403553) B9403553
theorem B12526589 : Blo 976593 12526589 := bstep (se 3 (by rfl) ⟨2348735, by rfl⟩ : syracuseStep 12526589 = 4697471) B4697471
theorem B6268063 : Blo 976593 6268063 := bstep (se 1 (by rfl) ⟨4701047, by rfl⟩ : syracuseStep 6268063 = 9402095) B9402095
theorem B1320295 : Blo 976593 1320295 := bstep (se 1 (by rfl) ⟨990221, by rfl⟩ : syracuseStep 1320295 = 1980443) B1980443
theorem B1648127 : Blo 976593 1648127 := bstep (se 1 (by rfl) ⟨1236095, by rfl⟩ : syracuseStep 1648127 = 2472191) B2472191
theorem B2205287 : Blo 976593 2205287 := bstep (se 1 (by rfl) ⟨1653965, by rfl⟩ : syracuseStep 2205287 = 3307931) B3307931
theorem B1648235 : Blo 976593 1648235 := bstep (se 1 (by rfl) ⟨1236176, by rfl⟩ : syracuseStep 1648235 = 2472353) B2472353
theorem B2205431 : Blo 976593 2205431 := bstep (se 1 (by rfl) ⟨1654073, by rfl⟩ : syracuseStep 2205431 = 3308147) B3308147
theorem B3712979 : Blo 976593 3712979 := bstep (se 1 (by rfl) ⟨2784734, by rfl⟩ : syracuseStep 3712979 = 5569469) B5569469
theorem B2206079 : Blo 976593 2206079 := bstep (se 1 (by rfl) ⟨1654559, by rfl⟩ : syracuseStep 2206079 = 3309119) B3309119
theorem B482257799 : Blo 976593 482257799 := bstep (se 1 (by rfl) ⟨361693349, by rfl⟩ : syracuseStep 482257799 = 723386699) B723386699
theorem B12528593 : Blo 976593 12528593 := bstep (se 2 (by rfl) ⟨4698222, by rfl⟩ : syracuseStep 12528593 = 9396445) B9396445
theorem B1649983 : Blo 976593 1649983 := bstep (se 1 (by rfl) ⟨1237487, by rfl⟩ : syracuseStep 1649983 = 2474975) B2474975
theorem B5582317 : Blo 976593 5582317 := bstep (se 3 (by rfl) ⟨1046684, by rfl⟩ : syracuseStep 5582317 = 2093369) B2093369
theorem B8465903 : Blo 976593 8465903 := bstep (se 1 (by rfl) ⟨6349427, by rfl⟩ : syracuseStep 8465903 = 12698855) B12698855
theorem B12725761 : Blo 976593 12725761 := bstep (se 2 (by rfl) ⟨4772160, by rfl⟩ : syracuseStep 12725761 = 9544321) B9544321
theorem B1486505 : Blo 976593 1486505 := bstep (se 2 (by rfl) ⟨557439, by rfl⟩ : syracuseStep 1486505 = 1114879) B1114879
theorem B16691183 : Blo 976593 16691183 := bstep (se 1 (by rfl) ⟨12518387, by rfl⟩ : syracuseStep 16691183 = 25036775) B25036775
theorem B9416857 : Blo 976593 9416857 := bstep (se 2 (by rfl) ⟨3531321, by rfl⟩ : syracuseStep 9416857 = 7062643) B7062643
theorem B1323803 : Blo 976593 1323803 := bstep (se 1 (by rfl) ⟨992852, by rfl⟩ : syracuseStep 1323803 = 1985705) B1985705
theorem B5583775 : Blo 976593 5583775 := bstep (se 1 (by rfl) ⟨4187831, by rfl⟩ : syracuseStep 5583775 = 8375663) B8375663
theorem B5289245 : Blo 976593 5289245 := bstep (se 3 (by rfl) ⟨991733, by rfl⟩ : syracuseStep 5289245 = 1983467) B1983467
theorem B1652251 : Blo 976593 1652251 := bstep (se 1 (by rfl) ⟨1239188, by rfl⟩ : syracuseStep 1652251 = 2478377) B2478377
theorem B13416425 : Blo 976593 13416425 := bstep (se 2 (by rfl) ⟨5031159, by rfl⟩ : syracuseStep 13416425 = 10062319) B10062319
theorem B1653743 : Blo 976593 1653743 := bstep (se 1 (by rfl) ⟨1240307, by rfl⟩ : syracuseStep 1653743 = 2480615) B2480615
theorem B28195897 : Blo 976593 28195897 := bstep (se 2 (by rfl) ⟨10573461, by rfl⟩ : syracuseStep 28195897 = 21146923) B21146923
theorem B3718507 : Blo 976593 3718507 := bstep (se 1 (by rfl) ⟨2788880, by rfl⟩ : syracuseStep 3718507 = 5577761) B5577761
theorem B7061201 : Blo 976593 7061201 := bstep (se 2 (by rfl) ⟨2647950, by rfl⟩ : syracuseStep 7061201 = 5295901) B5295901
theorem B30524381 : Blo 976593 30524381 := bstep (se 3 (by rfl) ⟨5723321, by rfl⟩ : syracuseStep 30524381 = 11446643) B11446643
theorem B1393643 : Blo 976593 1393643 := bstep (se 1 (by rfl) ⟨1045232, by rfl⟩ : syracuseStep 1393643 = 2090465) B2090465
theorem B7062815 : Blo 976593 7062815 := bstep (se 1 (by rfl) ⟨5297111, by rfl⟩ : syracuseStep 7062815 = 10594223) B10594223
theorem B2475431 : Blo 976593 2475431 := bstep (se 1 (by rfl) ⟨1856573, by rfl⟩ : syracuseStep 2475431 = 3713147) B3713147
theorem B5359787 : Blo 976593 5359787 := bstep (se 1 (by rfl) ⟨4019840, by rfl⟩ : syracuseStep 5359787 = 8039681) B8039681
theorem B11913637 : Blo 976593 11913637 := bstep (se 4 (by rfl) ⟨1116903, by rfl⟩ : syracuseStep 11913637 = 2233807) B2233807
theorem B3721895 : Blo 976593 3721895 := bstep (se 1 (by rfl) ⟨2791421, by rfl⟩ : syracuseStep 3721895 = 5582843) B5582843
theorem B3132263 : Blo 976593 3132263 := bstep (se 1 (by rfl) ⟨2349197, by rfl⟩ : syracuseStep 3132263 = 4698395) B4698395
theorem B2477375 : Blo 976593 2477375 := bstep (se 1 (by rfl) ⟨1858031, by rfl⟩ : syracuseStep 2477375 = 3716063) B3716063
theorem B2477537 : Blo 976593 2477537 := bstep (se 2 (by rfl) ⟨929076, by rfl⟩ : syracuseStep 2477537 = 1858153) B1858153
theorem B7425593 : Blo 976593 7425593 := bstep (se 2 (by rfl) ⟨2784597, by rfl⟩ : syracuseStep 7425593 = 5569195) B5569195
theorem B1101595 : Blo 976593 1101595 := bstep (se 1 (by rfl) ⟨826196, by rfl⟩ : syracuseStep 1101595 = 1652393) B1652393
theorem B10572079 : Blo 976593 10572079 := bstep (se 1 (by rfl) ⟨7929059, by rfl⟩ : syracuseStep 10572079 = 15858119) B15858119
theorem B1856695 : Blo 976593 1856695 := bstep (se 1 (by rfl) ⟨1392521, by rfl⟩ : syracuseStep 1856695 = 2785043) B2785043
theorem B3298535 : Blo 976593 3298535 := bstep (se 1 (by rfl) ⟨2473901, by rfl⟩ : syracuseStep 3298535 = 4947803) B4947803
theorem B2479369 : Blo 976593 2479369 := bstep (se 2 (by rfl) ⟨929763, by rfl⟩ : syracuseStep 2479369 = 1859527) B1859527
theorem B3299453 : Blo 976593 3299453 := bstep (se 3 (by rfl) ⟨618647, by rfl⟩ : syracuseStep 3299453 = 1237295) B1237295
theorem B1857811 : Blo 976593 1857811 := bstep (se 1 (by rfl) ⟨1393358, by rfl⟩ : syracuseStep 1857811 = 2786717) B2786717
theorem B1464923 : Blo 976593 1464923 := bstep (se 1 (by rfl) ⟨1098692, by rfl⟩ : syracuseStep 1464923 = 2197385) B2197385
theorem B1464959 : Blo 976593 1464959 := bstep (se 1 (by rfl) ⟨1098719, by rfl⟩ : syracuseStep 1464959 = 2197439) B2197439
theorem B4184723 : Blo 976593 4184723 := bstep (se 1 (by rfl) ⟨3138542, by rfl⟩ : syracuseStep 4184723 = 6277085) B6277085
theorem B3136313 : Blo 976593 3136313 := bstep (se 2 (by rfl) ⟨1176117, by rfl⟩ : syracuseStep 3136313 = 2352235) B2352235
theorem B2350217 : Blo 976593 2350217 := bstep (se 2 (by rfl) ⟨881331, by rfl⟩ : syracuseStep 2350217 = 1762663) B1762663
theorem B7527647 : Blo 976593 7527647 := bstep (se 1 (by rfl) ⟨5645735, by rfl⟩ : syracuseStep 7527647 = 11291471) B11291471
theorem B2481455 : Blo 976593 2481455 := bstep (se 1 (by rfl) ⟨1861091, by rfl⟩ : syracuseStep 2481455 = 3722183) B3722183
theorem B2972999 : Blo 976593 2972999 := bstep (se 1 (by rfl) ⟨2229749, by rfl⟩ : syracuseStep 2972999 = 4459499) B4459499
theorem B8936801 : Blo 976593 8936801 := bstep (se 2 (by rfl) ⟨3351300, by rfl⟩ : syracuseStep 8936801 = 6702601) B6702601
theorem B1465961 : Blo 976593 1465961 := bstep (se 2 (by rfl) ⟨549735, by rfl⟩ : syracuseStep 1465961 = 1099471) B1099471
theorem B87056333 : Blo 976593 87056333 := bstep (se 3 (by rfl) ⟨16323062, by rfl⟩ : syracuseStep 87056333 = 32646125) B32646125
theorem B1466363 : Blo 976593 1466363 := bstep (se 1 (by rfl) ⟨1099772, by rfl⟩ : syracuseStep 1466363 = 2199545) B2199545
theorem B3137723 : Blo 976593 3137723 := bstep (se 1 (by rfl) ⟨2353292, by rfl⟩ : syracuseStep 3137723 = 4706585) B4706585
theorem B12542687 : Blo 976593 12542687 := bstep (se 1 (by rfl) ⟨9407015, by rfl⟩ : syracuseStep 12542687 = 18814031) B18814031
theorem B1467257 : Blo 976593 1467257 := bstep (se 2 (by rfl) ⟨550221, by rfl⟩ : syracuseStep 1467257 = 1100443) B1100443
theorem B1467305 : Blo 976593 1467305 := bstep (se 2 (by rfl) ⟨550239, by rfl⟩ : syracuseStep 1467305 = 1100479) B1100479
theorem B3302369 : Blo 976593 3302369 := bstep (se 2 (by rfl) ⟨1238388, by rfl⟩ : syracuseStep 3302369 = 2476777) B2476777
theorem B60187643 : Blo 976593 60187643 := bstep (se 1 (by rfl) ⟨45140732, by rfl⟩ : syracuseStep 60187643 = 90281465) B90281465
theorem B8348669 : Blo 976593 8348669 := bstep (se 3 (by rfl) ⟨1565375, by rfl⟩ : syracuseStep 8348669 = 3130751) B3130751
theorem B1467695 : Blo 976593 1467695 := bstep (se 1 (by rfl) ⟨1100771, by rfl⟩ : syracuseStep 1467695 = 2201543) B2201543
theorem B1762793 : Blo 976593 1762793 := bstep (se 2 (by rfl) ⟨661047, by rfl⟩ : syracuseStep 1762793 = 1322095) B1322095
theorem B1467995 : Blo 976593 1467995 := bstep (se 1 (by rfl) ⟨1100996, by rfl⟩ : syracuseStep 1467995 = 2201993) B2201993
theorem B10872485 : Blo 976593 10872485 := bstep (se 4 (by rfl) ⟨1019295, by rfl⟩ : syracuseStep 10872485 = 2038591) B2038591
theorem B11921327 : Blo 976593 11921327 := bstep (se 1 (by rfl) ⟨8940995, by rfl⟩ : syracuseStep 11921327 = 17881991) B17881991
theorem B1468457 : Blo 976593 1468457 := bstep (se 2 (by rfl) ⟨550671, by rfl⟩ : syracuseStep 1468457 = 1101343) B1101343
theorem B977007 : Blo 976593 977007 := bstep (se 1 (by rfl) ⟨732755, by rfl⟩ : syracuseStep 977007 = 1465511) B1465511
theorem B1763455 : Blo 976593 1763455 := bstep (se 1 (by rfl) ⟨1322591, by rfl⟩ : syracuseStep 1763455 = 2645183) B2645183
theorem B3303611 : Blo 976593 3303611 := bstep (se 1 (by rfl) ⟨2477708, by rfl⟩ : syracuseStep 3303611 = 4955417) B4955417
theorem B977103 : Blo 976593 977103 := bstep (se 1 (by rfl) ⟨732827, by rfl⟩ : syracuseStep 977103 = 1465655) B1465655
theorem B5958083 : Blo 976593 5958083 := bstep (se 1 (by rfl) ⟨4468562, by rfl⟩ : syracuseStep 5958083 = 8937125) B8937125
theorem B7629427 : Blo 976593 7629427 := bstep (se 1 (by rfl) ⟨5722070, by rfl⟩ : syracuseStep 7629427 = 11444141) B11444141
theorem B1469087 : Blo 976593 1469087 := bstep (se 1 (by rfl) ⟨1101815, by rfl⟩ : syracuseStep 1469087 = 2203631) B2203631
theorem B5565095 : Blo 976593 5565095 := bstep (se 1 (by rfl) ⟨4173821, by rfl⟩ : syracuseStep 5565095 = 8347643) B8347643
theorem B977599 : Blo 976593 977599 := bstep (se 1 (by rfl) ⟨733199, by rfl⟩ : syracuseStep 977599 = 1466399) B1466399
theorem B1567439 : Blo 976593 1567439 := bstep (se 1 (by rfl) ⟨1175579, by rfl⟩ : syracuseStep 1567439 = 2351159) B2351159
theorem B977695 : Blo 976593 977695 := bstep (se 1 (by rfl) ⟨733271, by rfl⟩ : syracuseStep 977695 = 1466543) B1466543
theorem B1469543 : Blo 976593 1469543 := bstep (se 1 (by rfl) ⟨1102157, by rfl⟩ : syracuseStep 1469543 = 2204315) B2204315
theorem B978175 : Blo 976593 978175 := bstep (se 1 (by rfl) ⟨733631, by rfl⟩ : syracuseStep 978175 = 1467263) B1467263
theorem B3304799 : Blo 976593 3304799 := bstep (se 1 (by rfl) ⟨2478599, by rfl⟩ : syracuseStep 3304799 = 4957199) B4957199
theorem B1240687 : Blo 976593 1240687 := bstep (se 1 (by rfl) ⟨930515, by rfl⟩ : syracuseStep 1240687 = 1861031) B1861031
theorem B978587 : Blo 976593 978587 := bstep (se 1 (by rfl) ⟨733940, by rfl⟩ : syracuseStep 978587 = 1467881) B1467881
theorem B979015 : Blo 976593 979015 := bstep (se 1 (by rfl) ⟨734261, by rfl⟩ : syracuseStep 979015 = 1468523) B1468523
theorem B979055 : Blo 976593 979055 := bstep (se 1 (by rfl) ⟨734291, by rfl⟩ : syracuseStep 979055 = 1468583) B1468583
theorem B95383817 : Blo 976593 95383817 := bstep (se 2 (by rfl) ⟨35768931, by rfl⟩ : syracuseStep 95383817 = 71537863) B71537863
theorem B3306041 : Blo 976593 3306041 := bstep (se 2 (by rfl) ⟨1239765, by rfl⟩ : syracuseStep 3306041 = 2479531) B2479531
theorem B12546683 : Blo 976593 12546683 := bstep (se 1 (by rfl) ⟨9410012, by rfl⟩ : syracuseStep 12546683 = 18820025) B18820025
theorem B558265283 : Blo 976593 558265283 := bstep (se 1 (by rfl) ⟨418698962, by rfl⟩ : syracuseStep 558265283 = 837397925) B837397925
theorem B979967 : Blo 976593 979967 := bstep (se 1 (by rfl) ⟨734975, by rfl⟩ : syracuseStep 979967 = 1469951) B1469951
theorem B29389853 : Blo 976593 29389853 := bstep (se 3 (by rfl) ⟨5510597, by rfl⟩ : syracuseStep 29389853 = 11021195) B11021195
theorem B980199 : Blo 976593 980199 := bstep (se 1 (by rfl) ⟨735149, by rfl⟩ : syracuseStep 980199 = 1470299) B1470299
theorem B13399339 : Blo 976593 13399339 := bstep (se 1 (by rfl) ⟨10049504, by rfl⟩ : syracuseStep 13399339 = 20099009) B20099009
theorem B980351 : Blo 976593 980351 := bstep (se 1 (by rfl) ⟨735263, by rfl⟩ : syracuseStep 980351 = 1470527) B1470527
theorem B160495181 : Blo 976593 160495181 := bstep (se 3 (by rfl) ⟨30092846, by rfl⟩ : syracuseStep 160495181 = 60185693) B60185693
theorem B3307175 : Blo 976593 3307175 := bstep (se 1 (by rfl) ⟨2480381, by rfl⟩ : syracuseStep 3307175 = 4960763) B4960763
theorem B3307769 : Blo 976593 3307769 := bstep (se 2 (by rfl) ⟨1240413, by rfl⟩ : syracuseStep 3307769 = 2480827) B2480827
theorem B4946345 : Blo 976593 4946345 := bstep (se 2 (by rfl) ⟨1854879, by rfl⟩ : syracuseStep 4946345 = 3709759) B3709759
theorem B7437743 : Blo 976593 7437743 := bstep (se 1 (by rfl) ⟨5578307, by rfl⟩ : syracuseStep 7437743 = 11156615) B11156615
theorem B3309227 : Blo 976593 3309227 := bstep (se 1 (by rfl) ⟨2481920, by rfl⟩ : syracuseStep 3309227 = 4963841) B4963841
theorem B20349587 : Blo 976593 20349587 := bstep (se 1 (by rfl) ⟨15262190, by rfl⟩ : syracuseStep 20349587 = 30524381) B30524381
theorem B3573191 : Blo 976593 3573191 := bstep (se 1 (by rfl) ⟨2679893, by rfl⟩ : syracuseStep 3573191 = 5359787) B5359787
theorem B8357417 : Blo 976593 8357417 := bstep (se 2 (by rfl) ⟨3134031, by rfl⟩ : syracuseStep 8357417 = 6268063) B6268063
theorem B4950395 : Blo 976593 4950395 := bstep (se 1 (by rfl) ⟨3712796, by rfl⟩ : syracuseStep 4950395 = 7425593) B7425593
theorem B2199023 : Blo 976593 2199023 := bstep (se 1 (by rfl) ⟨1649267, by rfl⟩ : syracuseStep 2199023 = 3298535) B3298535
theorem B2199635 : Blo 976593 2199635 := bstep (se 1 (by rfl) ⟨1649726, by rfl⟩ : syracuseStep 2199635 = 3299453) B3299453
theorem B2199977 : Blo 976593 2199977 := bstep (se 2 (by rfl) ⟨824991, by rfl⟩ : syracuseStep 2199977 = 1649983) B1649983
theorem B2789815 : Blo 976593 2789815 := bstep (se 1 (by rfl) ⟨2092361, by rfl⟩ : syracuseStep 2789815 = 4184723) B4184723
theorem B7443089 : Blo 976593 7443089 := bstep (se 2 (by rfl) ⟨2791158, by rfl⟩ : syracuseStep 7443089 = 5582317) B5582317
theorem B5018431 : Blo 976593 5018431 := bstep (se 1 (by rfl) ⟨3763823, by rfl⟩ : syracuseStep 5018431 = 7527647) B7527647
theorem B58037555 : Blo 976593 58037555 := bstep (se 1 (by rfl) ⟨43528166, by rfl⟩ : syracuseStep 58037555 = 87056333) B87056333
theorem B12555809 : Blo 976593 12555809 := bstep (se 2 (by rfl) ⟨4708428, by rfl⟩ : syracuseStep 12555809 = 9416857) B9416857
theorem B16717427 : Blo 976593 16717427 := bstep (se 1 (by rfl) ⟨12538070, by rfl⟩ : syracuseStep 16717427 = 25076141) B25076141
theorem B14096105 : Blo 976593 14096105 := bstep (se 2 (by rfl) ⟨5286039, by rfl⟩ : syracuseStep 14096105 = 10572079) B10572079
theorem B8361791 : Blo 976593 8361791 := bstep (se 1 (by rfl) ⟨6271343, by rfl⟩ : syracuseStep 8361791 = 12542687) B12542687
theorem B2201579 : Blo 976593 2201579 := bstep (se 1 (by rfl) ⟨1651184, by rfl⟩ : syracuseStep 2201579 = 3302369) B3302369
theorem B7248323 : Blo 976593 7248323 := bstep (se 1 (by rfl) ⟨5436242, by rfl⟩ : syracuseStep 7248323 = 10872485) B10872485
theorem B7445033 : Blo 976593 7445033 := bstep (se 2 (by rfl) ⟨2791887, by rfl⟩ : syracuseStep 7445033 = 5583775) B5583775
theorem B2202407 : Blo 976593 2202407 := bstep (se 1 (by rfl) ⟨1651805, by rfl⟩ : syracuseStep 2202407 = 3303611) B3303611
theorem B17865785 : Blo 976593 17865785 := bstep (se 2 (by rfl) ⟨6699669, by rfl⟩ : syracuseStep 17865785 = 13399339) B13399339
theorem B3710063 : Blo 976593 3710063 := bstep (se 1 (by rfl) ⟨2782547, by rfl⟩ : syracuseStep 3710063 = 5565095) B5565095
theorem B2203001 : Blo 976593 2203001 := bstep (se 2 (by rfl) ⟨826125, by rfl⟩ : syracuseStep 2203001 = 1652251) B1652251
theorem B20061593 : Blo 976593 20061593 := bstep (se 2 (by rfl) ⟨7523097, by rfl⟩ : syracuseStep 20061593 = 15046195) B15046195
theorem B2203199 : Blo 976593 2203199 := bstep (se 1 (by rfl) ⟨1652399, by rfl⟩ : syracuseStep 2203199 = 3304799) B3304799
theorem B5643935 : Blo 976593 5643935 := bstep (se 1 (by rfl) ⟨4232951, by rfl⟩ : syracuseStep 5643935 = 8465903) B8465903
theorem B991003 : Blo 976593 991003 := bstep (se 1 (by rfl) ⟨743252, by rfl⟩ : syracuseStep 991003 = 1486505) B1486505
theorem B2204027 : Blo 976593 2204027 := bstep (se 1 (by rfl) ⟨1653020, by rfl⟩ : syracuseStep 2204027 = 3306041) B3306041
theorem B8364455 : Blo 976593 8364455 := bstep (se 1 (by rfl) ⟨6273341, by rfl⟩ : syracuseStep 8364455 = 12546683) B12546683
theorem B106996787 : Blo 976593 106996787 := bstep (se 1 (by rfl) ⟨80247590, by rfl⟩ : syracuseStep 106996787 = 160495181) B160495181
theorem B2204783 : Blo 976593 2204783 := bstep (se 1 (by rfl) ⟨1653587, by rfl⟩ : syracuseStep 2204783 = 3307175) B3307175
theorem B37594529 : Blo 976593 37594529 := bstep (se 2 (by rfl) ⟨14097948, by rfl⟩ : syracuseStep 37594529 = 28195897) B28195897
theorem B2205179 : Blo 976593 2205179 := bstep (se 1 (by rfl) ⟨1653884, by rfl⟩ : syracuseStep 2205179 = 3307769) B3307769
theorem B4958009 : Blo 976593 4958009 := bstep (se 2 (by rfl) ⟨1859253, by rfl⟩ : syracuseStep 4958009 = 3718507) B3718507
theorem B4958495 : Blo 976593 4958495 := bstep (se 1 (by rfl) ⟨3718871, by rfl⟩ : syracuseStep 4958495 = 7437743) B7437743
theorem B2206151 : Blo 976593 2206151 := bstep (se 1 (by rfl) ⟨1654613, by rfl⟩ : syracuseStep 2206151 = 3309227) B3309227
theorem B1650287 : Blo 976593 1650287 := bstep (se 1 (by rfl) ⟨1237715, by rfl⟩ : syracuseStep 1650287 = 2475431) B2475431
theorem B4174199 : Blo 976593 4174199 := bstep (se 1 (by rfl) ⟨3130649, by rfl⟩ : syracuseStep 4174199 = 6261299) B6261299
theorem B1651583 : Blo 976593 1651583 := bstep (se 1 (by rfl) ⟨1238687, by rfl⟩ : syracuseStep 1651583 = 2477375) B2477375
theorem B1651691 : Blo 976593 1651691 := bstep (se 1 (by rfl) ⟨1238768, by rfl⟩ : syracuseStep 1651691 = 2477537) B2477537
theorem B3716381 : Blo 976593 3716381 := bstep (se 3 (by rfl) ⟨696821, by rfl⟩ : syracuseStep 3716381 = 1393643) B1393643
theorem B10172569 : Blo 976593 10172569 := bstep (se 2 (by rfl) ⟨3814713, by rfl⟩ : syracuseStep 10172569 = 7629427) B7629427
theorem B17873081 : Blo 976593 17873081 := bstep (se 2 (by rfl) ⟨6702405, by rfl⟩ : syracuseStep 17873081 = 13404811) B13404811
theorem B1654249 : Blo 976593 1654249 := bstep (se 2 (by rfl) ⟨620343, by rfl⟩ : syracuseStep 1654249 = 1240687) B1240687
theorem B1654303 : Blo 976593 1654303 := bstep (se 1 (by rfl) ⟨1240727, by rfl⟩ : syracuseStep 1654303 = 2481455) B2481455
theorem B1981999 : Blo 976593 1981999 := bstep (se 1 (by rfl) ⟨1486499, by rfl⟩ : syracuseStep 1981999 = 2972999) B2972999
theorem B4177615 : Blo 976593 4177615 := bstep (se 1 (by rfl) ⟨3133211, by rfl⟩ : syracuseStep 4177615 = 6266423) B6266423
theorem B40125095 : Blo 976593 40125095 := bstep (se 1 (by rfl) ⟨30093821, by rfl⟩ : syracuseStep 40125095 = 60187643) B60187643
theorem B1098751 : Blo 976593 1098751 := bstep (se 1 (by rfl) ⟨824063, by rfl⟩ : syracuseStep 1098751 = 1648127) B1648127
theorem B1098823 : Blo 976593 1098823 := bstep (se 1 (by rfl) ⟨824117, by rfl⟩ : syracuseStep 1098823 = 1648235) B1648235
theorem B7947551 : Blo 976593 7947551 := bstep (se 1 (by rfl) ⟨5960663, by rfl⟩ : syracuseStep 7947551 = 11921327) B11921327
theorem B2475319 : Blo 976593 2475319 := bstep (se 1 (by rfl) ⟨1856489, by rfl⟩ : syracuseStep 2475319 = 3712979) B3712979
theorem B2475593 : Blo 976593 2475593 := bstep (se 2 (by rfl) ⟨928347, by rfl⟩ : syracuseStep 2475593 = 1856695) B1856695
theorem B3720937 : Blo 976593 3720937 := bstep (se 2 (by rfl) ⟨1395351, by rfl⟩ : syracuseStep 3720937 = 2790703) B2790703
theorem B321505199 : Blo 976593 321505199 := bstep (se 1 (by rfl) ⟨241128899, by rfl⟩ : syracuseStep 321505199 = 482257799) B482257799
theorem B11127455 : Blo 976593 11127455 := bstep (se 1 (by rfl) ⟨8345591, by rfl⟩ : syracuseStep 11127455 = 16691183) B16691183
theorem B63589211 : Blo 976593 63589211 := bstep (se 1 (by rfl) ⟨47691908, by rfl⟩ : syracuseStep 63589211 = 95383817) B95383817
theorem B2477081 : Blo 976593 2477081 := bstep (se 2 (by rfl) ⟨928905, by rfl⟩ : syracuseStep 2477081 = 1857811) B1857811
theorem B3526163 : Blo 976593 3526163 := bstep (se 1 (by rfl) ⟨2644622, by rfl⟩ : syracuseStep 3526163 = 5289245) B5289245
theorem B3297563 : Blo 976593 3297563 := bstep (se 1 (by rfl) ⟨2473172, by rfl⟩ : syracuseStep 3297563 = 4946345) B4946345
theorem B1102495 : Blo 976593 1102495 := bstep (se 1 (by rfl) ⟨826871, by rfl⟩ : syracuseStep 1102495 = 1653743) B1653743
theorem B4707467 : Blo 976593 4707467 := bstep (se 1 (by rfl) ⟨3530600, by rfl⟩ : syracuseStep 4707467 = 7061201) B7061201
theorem B12539711 : Blo 976593 12539711 := bstep (se 1 (by rfl) ⟨9404783, by rfl⟩ : syracuseStep 12539711 = 18809567) B18809567
theorem B6707119 : Blo 976593 6707119 := bstep (se 1 (by rfl) ⟨5030339, by rfl⟩ : syracuseStep 6707119 = 10060679) B10060679
theorem B4708543 : Blo 976593 4708543 := bstep (se 1 (by rfl) ⟨3531407, by rfl⟩ : syracuseStep 4708543 = 7062815) B7062815
theorem B7428509 : Blo 976593 7428509 := bstep (se 3 (by rfl) ⟨1392845, by rfl⟩ : syracuseStep 7428509 = 2785691) B2785691
theorem B2481263 : Blo 976593 2481263 := bstep (se 1 (by rfl) ⟨1860947, by rfl⟩ : syracuseStep 2481263 = 3721895) B3721895
theorem B1760393 : Blo 976593 1760393 := bstep (se 2 (by rfl) ⟨660147, by rfl⟩ : syracuseStep 1760393 = 1320295) B1320295
theorem B2088175 : Blo 976593 2088175 := bstep (se 1 (by rfl) ⟨1566131, by rfl⟩ : syracuseStep 2088175 = 3132263) B3132263
theorem B3530141 : Blo 976593 3530141 := bstep (se 3 (by rfl) ⟨661901, by rfl⟩ : syracuseStep 3530141 = 1323803) B1323803
theorem B3301019 : Blo 976593 3301019 := bstep (se 1 (by rfl) ⟨2475764, by rfl⟩ : syracuseStep 3301019 = 4951529) B4951529
theorem B25386689 : Blo 976593 25386689 := bstep (se 2 (by rfl) ⟨9520008, by rfl⟩ : syracuseStep 25386689 = 19040017) B19040017
theorem B2351273 : Blo 976593 2351273 := bstep (se 2 (by rfl) ⟨881727, by rfl⟩ : syracuseStep 2351273 = 1763455) B1763455
theorem B15884849 : Blo 976593 15884849 := bstep (se 2 (by rfl) ⟨5956818, by rfl⟩ : syracuseStep 15884849 = 11913637) B11913637
theorem B3301991 : Blo 976593 3301991 := bstep (se 1 (by rfl) ⟨2476493, by rfl⟩ : syracuseStep 3301991 = 4952987) B4952987
theorem B1860347 : Blo 976593 1860347 := bstep (se 1 (by rfl) ⟨1395260, by rfl⟩ : syracuseStep 1860347 = 2790521) B2790521
theorem B1467239 : Blo 976593 1467239 := bstep (se 1 (by rfl) ⟨1100429, by rfl⟩ : syracuseStep 1467239 = 2200859) B2200859
theorem B1467935 : Blo 976593 1467935 := bstep (se 1 (by rfl) ⟨1100951, by rfl⟩ : syracuseStep 1467935 = 2201903) B2201903
theorem B1468007 : Blo 976593 1468007 := bstep (se 1 (by rfl) ⟨1101005, by rfl⟩ : syracuseStep 1468007 = 2202011) B2202011
theorem B976615 : Blo 976593 976615 := bstep (se 1 (by rfl) ⟨732461, by rfl⟩ : syracuseStep 976615 = 1464923) B1464923
theorem B976639 : Blo 976593 976639 := bstep (se 1 (by rfl) ⟨732479, by rfl⟩ : syracuseStep 976639 = 1464959) B1464959
theorem B2090875 : Blo 976593 2090875 := bstep (se 1 (by rfl) ⟨1568156, by rfl⟩ : syracuseStep 2090875 = 3136313) B3136313
theorem B3762089 : Blo 976593 3762089 := bstep (se 2 (by rfl) ⟨1410783, by rfl⟩ : syracuseStep 3762089 = 2821567) B2821567
theorem B16967681 : Blo 976593 16967681 := bstep (se 2 (by rfl) ⟨6362880, by rfl⟩ : syracuseStep 16967681 = 12725761) B12725761
theorem B1566811 : Blo 976593 1566811 := bstep (se 1 (by rfl) ⟨1175108, by rfl⟩ : syracuseStep 1566811 = 2350217) B2350217
theorem B57239743 : Blo 976593 57239743 := bstep (se 1 (by rfl) ⟨42929807, by rfl⟩ : syracuseStep 57239743 = 85859615) B85859615
theorem B5957867 : Blo 976593 5957867 := bstep (se 1 (by rfl) ⟨4468400, by rfl⟩ : syracuseStep 5957867 = 8936801) B8936801
theorem B1468793 : Blo 976593 1468793 := bstep (se 2 (by rfl) ⟨550797, by rfl⟩ : syracuseStep 1468793 = 1101595) B1101595
theorem B977307 : Blo 976593 977307 := bstep (se 1 (by rfl) ⟨732980, by rfl⟩ : syracuseStep 977307 = 1465961) B1465961
theorem B1468871 : Blo 976593 1468871 := bstep (se 1 (by rfl) ⟨1101653, by rfl⟩ : syracuseStep 1468871 = 2203307) B2203307
theorem B977575 : Blo 976593 977575 := bstep (se 1 (by rfl) ⟨733181, by rfl⟩ : syracuseStep 977575 = 1466363) B1466363
theorem B2091815 : Blo 976593 2091815 := bstep (se 1 (by rfl) ⟨1568861, by rfl⟩ : syracuseStep 2091815 = 3137723) B3137723
theorem B978171 : Blo 976593 978171 := bstep (se 1 (by rfl) ⟨733628, by rfl⟩ : syracuseStep 978171 = 1467257) B1467257
theorem B978203 : Blo 976593 978203 := bstep (se 1 (by rfl) ⟨733652, by rfl⟩ : syracuseStep 978203 = 1467305) B1467305
theorem B5565779 : Blo 976593 5565779 := bstep (se 1 (by rfl) ⟨4174334, by rfl⟩ : syracuseStep 5565779 = 8348669) B8348669
theorem B8351059 : Blo 976593 8351059 := bstep (se 1 (by rfl) ⟨6263294, by rfl⟩ : syracuseStep 8351059 = 12526589) B12526589
theorem B978463 : Blo 976593 978463 := bstep (se 1 (by rfl) ⟨733847, by rfl⟩ : syracuseStep 978463 = 1467695) B1467695
theorem B1175195 : Blo 976593 1175195 := bstep (se 1 (by rfl) ⟨881396, by rfl⟩ : syracuseStep 1175195 = 1762793) B1762793
theorem B31682249 : Blo 976593 31682249 := bstep (se 2 (by rfl) ⟨11880843, by rfl⟩ : syracuseStep 31682249 = 23761687) B23761687
theorem B978663 : Blo 976593 978663 := bstep (se 1 (by rfl) ⟨733997, by rfl⟩ : syracuseStep 978663 = 1467995) B1467995
theorem B1470191 : Blo 976593 1470191 := bstep (se 1 (by rfl) ⟨1102643, by rfl⟩ : syracuseStep 1470191 = 2205287) B2205287
theorem B1470287 : Blo 976593 1470287 := bstep (se 1 (by rfl) ⟨1102715, by rfl⟩ : syracuseStep 1470287 = 2205431) B2205431
theorem B15888221 : Blo 976593 15888221 := bstep (se 3 (by rfl) ⟨2979041, by rfl⟩ : syracuseStep 15888221 = 5958083) B5958083
theorem B978971 : Blo 976593 978971 := bstep (se 1 (by rfl) ⟨734228, by rfl⟩ : syracuseStep 978971 = 1468457) B1468457
theorem B1470719 : Blo 976593 1470719 := bstep (se 1 (by rfl) ⟨1103039, by rfl⟩ : syracuseStep 1470719 = 2206079) B2206079
theorem B3305825 : Blo 976593 3305825 := bstep (se 2 (by rfl) ⟨1239684, by rfl⟩ : syracuseStep 3305825 = 2479369) B2479369
theorem B979391 : Blo 976593 979391 := bstep (se 1 (by rfl) ⟨734543, by rfl⟩ : syracuseStep 979391 = 1469087) B1469087
theorem B1044959 : Blo 976593 1044959 := bstep (se 1 (by rfl) ⟨783719, by rfl⟩ : syracuseStep 1044959 = 1567439) B1567439
theorem B8352395 : Blo 976593 8352395 := bstep (se 1 (by rfl) ⟨6264296, by rfl⟩ : syracuseStep 8352395 = 12528593) B12528593
theorem B979695 : Blo 976593 979695 := bstep (se 1 (by rfl) ⟨734771, by rfl⟩ : syracuseStep 979695 = 1469543) B1469543
theorem B372176855 : Blo 976593 372176855 := bstep (se 1 (by rfl) ⟨279132641, by rfl⟩ : syracuseStep 372176855 = 558265283) B558265283
theorem B19593235 : Blo 976593 19593235 := bstep (se 1 (by rfl) ⟨14694926, by rfl⟩ : syracuseStep 19593235 = 29389853) B29389853
theorem B8944283 : Blo 976593 8944283 := bstep (se 1 (by rfl) ⟨6708212, by rfl⟩ : syracuseStep 8944283 = 13416425) B13416425
theorem B104497253 : Blo 976593 104497253 := bstep (se 4 (by rfl) ⟨9796617, by rfl⟩ : syracuseStep 104497253 = 19593235) B19593235
theorem B5571611 : Blo 976593 5571611 := bstep (se 1 (by rfl) ⟨4178708, by rfl⟩ : syracuseStep 5571611 = 8357417) B8357417
theorem B2786557 : Blo 976593 2786557 := bstep (se 3 (by rfl) ⟨522479, by rfl⟩ : syracuseStep 2786557 = 1044959) B1044959
theorem B214336799 : Blo 976593 214336799 := bstep (se 1 (by rfl) ⟨160752599, by rfl⟩ : syracuseStep 214336799 = 321505199) B321505199
theorem B54265565 : Blo 976593 54265565 := bstep (se 3 (by rfl) ⟨10174793, by rfl⟩ : syracuseStep 54265565 = 20349587) B20349587
theorem B2787833 : Blo 976593 2787833 := bstep (se 2 (by rfl) ⟨1045437, by rfl⟩ : syracuseStep 2787833 = 2090875) B2090875
theorem B2198375 : Blo 976593 2198375 := bstep (se 1 (by rfl) ⟨1648781, by rfl⟩ : syracuseStep 2198375 = 3297563) B3297563
theorem B76319657 : Blo 976593 76319657 := bstep (se 2 (by rfl) ⟨28619871, by rfl⟩ : syracuseStep 76319657 = 57239743) B57239743
theorem B11144951 : Blo 976593 11144951 := bstep (se 1 (by rfl) ⟨8358713, by rfl⟩ : syracuseStep 11144951 = 16717427) B16717427
theorem B8359807 : Blo 976593 8359807 := bstep (se 1 (by rfl) ⟨6269855, by rfl⟩ : syracuseStep 8359807 = 12539711) B12539711
theorem B5574527 : Blo 976593 5574527 := bstep (se 1 (by rfl) ⟨4180895, by rfl⟩ : syracuseStep 5574527 = 8361791) B8361791
theorem B4952339 : Blo 976593 4952339 := bstep (se 1 (by rfl) ⟨3714254, by rfl⟩ : syracuseStep 4952339 = 7428509) B7428509
theorem B13374395 : Blo 976593 13374395 := bstep (se 1 (by rfl) ⟨10030796, by rfl⟩ : syracuseStep 13374395 = 20061593) B20061593
theorem B2200679 : Blo 976593 2200679 := bstep (se 1 (by rfl) ⟨1650509, by rfl⟩ : syracuseStep 2200679 = 3301019) B3301019
theorem B5576303 : Blo 976593 5576303 := bstep (se 1 (by rfl) ⟨4182227, by rfl⟩ : syracuseStep 5576303 = 8364455) B8364455
theorem B10589899 : Blo 976593 10589899 := bstep (se 1 (by rfl) ⟨7942424, by rfl⟩ : syracuseStep 10589899 = 15884849) B15884849
theorem B2201327 : Blo 976593 2201327 := bstep (se 1 (by rfl) ⟨1650995, by rfl⟩ : syracuseStep 2201327 = 3301991) B3301991
theorem B6691241 : Blo 976593 6691241 := bstep (se 2 (by rfl) ⟨2509215, by rfl⟩ : syracuseStep 6691241 = 5018431) B5018431
theorem B11311787 : Blo 976593 11311787 := bstep (se 1 (by rfl) ⟨8483840, by rfl⟩ : syracuseStep 11311787 = 16967681) B16967681
theorem B3971911 : Blo 976593 3971911 := bstep (se 1 (by rfl) ⟨2978933, by rfl⟩ : syracuseStep 3971911 = 5957867) B5957867
theorem B3710519 : Blo 976593 3710519 := bstep (se 1 (by rfl) ⟨2782889, by rfl⟩ : syracuseStep 3710519 = 5565779) B5565779
theorem B10592147 : Blo 976593 10592147 := bstep (se 1 (by rfl) ⟨7944110, by rfl⟩ : syracuseStep 10592147 = 15888221) B15888221
theorem B2203883 : Blo 976593 2203883 := bstep (se 1 (by rfl) ⟨1652912, by rfl⟩ : syracuseStep 2203883 = 3305825) B3305825
theorem B4694381 : Blo 976593 4694381 := bstep (se 3 (by rfl) ⟨880196, by rfl⟩ : syracuseStep 4694381 = 1760393) B1760393
theorem B2205665 : Blo 976593 2205665 := bstep (se 2 (by rfl) ⟨827124, by rfl⟩ : syracuseStep 2205665 = 1654249) B1654249
theorem B2205737 : Blo 976593 2205737 := bstep (se 2 (by rfl) ⟨827151, by rfl⟩ : syracuseStep 2205737 = 1654303) B1654303
theorem B1321337 : Blo 976593 1321337 := bstep (se 2 (by rfl) ⟨495501, by rfl⟩ : syracuseStep 1321337 = 991003) B991003
theorem B6270061 : Blo 976593 6270061 := bstep (se 3 (by rfl) ⟨1175636, by rfl⟩ : syracuseStep 6270061 = 2351273) B2351273
theorem B26750063 : Blo 976593 26750063 := bstep (se 1 (by rfl) ⟨20062547, by rfl⟩ : syracuseStep 26750063 = 40125095) B40125095
theorem B1650395 : Blo 976593 1650395 := bstep (se 1 (by rfl) ⟨1237796, by rfl⟩ : syracuseStep 1650395 = 2475593) B2475593
theorem B7418303 : Blo 976593 7418303 := bstep (se 1 (by rfl) ⟨5563727, by rfl⟩ : syracuseStep 7418303 = 11127455) B11127455
theorem B4960925 : Blo 976593 4960925 := bstep (se 3 (by rfl) ⟨930173, by rfl⟩ : syracuseStep 4960925 = 1860347) B1860347
theorem B1651387 : Blo 976593 1651387 := bstep (se 1 (by rfl) ⟨1238540, by rfl⟩ : syracuseStep 1651387 = 2477081) B2477081
theorem B4961249 : Blo 976593 4961249 := bstep (se 2 (by rfl) ⟨1860468, by rfl⟩ : syracuseStep 4961249 = 3720937) B3720937
theorem B4962059 : Blo 976593 4962059 := bstep (se 1 (by rfl) ⟨3721544, by rfl⟩ : syracuseStep 4962059 = 7443089) B7443089
theorem B8370539 : Blo 976593 8370539 := bstep (se 1 (by rfl) ⟨6277904, by rfl⟩ : syracuseStep 8370539 = 12555809) B12555809
theorem B4963355 : Blo 976593 4963355 := bstep (se 1 (by rfl) ⟨3722516, by rfl⟩ : syracuseStep 4963355 = 7445033) B7445033
theorem B11910523 : Blo 976593 11910523 := bstep (se 1 (by rfl) ⟨8932892, by rfl⟩ : syracuseStep 11910523 = 17865785) B17865785
theorem B2473375 : Blo 976593 2473375 := bstep (se 1 (by rfl) ⟨1855031, by rfl⟩ : syracuseStep 2473375 = 3710063) B3710063
theorem B1654175 : Blo 976593 1654175 := bstep (se 1 (by rfl) ⟨1240631, by rfl⟩ : syracuseStep 1654175 = 2481263) B2481263
theorem B16924459 : Blo 976593 16924459 := bstep (se 1 (by rfl) ⟨12693344, by rfl⟩ : syracuseStep 16924459 = 25386689) B25386689
theorem B3719753 : Blo 976593 3719753 := bstep (se 2 (by rfl) ⟨1394907, by rfl⟩ : syracuseStep 3719753 = 2789815) B2789815
theorem B2508059 : Blo 976593 2508059 := bstep (se 1 (by rfl) ⟨1881044, by rfl⟩ : syracuseStep 2508059 = 3762089) B3762089
theorem B1394543 : Blo 976593 1394543 := bstep (se 1 (by rfl) ⟨1045907, by rfl⟩ : syracuseStep 1394543 = 2091815) B2091815
theorem B1100191 : Blo 976593 1100191 := bstep (se 1 (by rfl) ⟨825143, by rfl⟩ : syracuseStep 1100191 = 1650287) B1650287
theorem B21121499 : Blo 976593 21121499 := bstep (se 1 (by rfl) ⟨15841124, by rfl⟩ : syracuseStep 21121499 = 31682249) B31682249
theorem B10570661 : Blo 976593 10570661 := bstep (se 4 (by rfl) ⟨990999, by rfl⟩ : syracuseStep 10570661 = 1981999) B1981999
theorem B6278057 : Blo 976593 6278057 := bstep (se 2 (by rfl) ⟨2354271, by rfl⟩ : syracuseStep 6278057 = 4708543) B4708543
theorem B1101055 : Blo 976593 1101055 := bstep (se 1 (by rfl) ⟨825791, by rfl⟩ : syracuseStep 1101055 = 1651583) B1651583
theorem B1101127 : Blo 976593 1101127 := bstep (se 1 (by rfl) ⟨825845, by rfl⟩ : syracuseStep 1101127 = 1651691) B1651691
theorem B2477587 : Blo 976593 2477587 := bstep (se 1 (by rfl) ⟨1858190, by rfl⟩ : syracuseStep 2477587 = 3716381) B3716381
theorem B11915387 : Blo 976593 11915387 := bstep (se 1 (by rfl) ⟨8936540, by rfl⟩ : syracuseStep 11915387 = 17873081) B17873081
theorem B3133853 : Blo 976593 3133853 := bstep (se 3 (by rfl) ⟨587597, by rfl⟩ : syracuseStep 3133853 = 1175195) B1175195
theorem B5298367 : Blo 976593 5298367 := bstep (se 1 (by rfl) ⟨3973775, by rfl⟩ : syracuseStep 5298367 = 7947551) B7947551
theorem B1465001 : Blo 976593 1465001 := bstep (se 2 (by rfl) ⟨549375, by rfl⟩ : syracuseStep 1465001 = 1098751) B1098751
theorem B1465097 : Blo 976593 1465097 := bstep (se 2 (by rfl) ⟨549411, by rfl⟩ : syracuseStep 1465097 = 1098823) B1098823
theorem B3300263 : Blo 976593 3300263 := bstep (se 1 (by rfl) ⟨2475197, by rfl⟩ : syracuseStep 3300263 = 4950395) B4950395
theorem B3300425 : Blo 976593 3300425 := bstep (se 2 (by rfl) ⟨1237659, by rfl⟩ : syracuseStep 3300425 = 2475319) B2475319
theorem B42392807 : Blo 976593 42392807 := bstep (se 1 (by rfl) ⟨31794605, by rfl⟩ : syracuseStep 42392807 = 63589211) B63589211
theorem B1466015 : Blo 976593 1466015 := bstep (se 1 (by rfl) ⟨1099511, by rfl⟩ : syracuseStep 1466015 = 2199023) B2199023
theorem B2350775 : Blo 976593 2350775 := bstep (se 1 (by rfl) ⟨1763081, by rfl⟩ : syracuseStep 2350775 = 3526163) B3526163
theorem B1466423 : Blo 976593 1466423 := bstep (se 1 (by rfl) ⟨1099817, by rfl⟩ : syracuseStep 1466423 = 2199635) B2199635
theorem B2089081 : Blo 976593 2089081 := bstep (se 2 (by rfl) ⟨783405, by rfl⟩ : syracuseStep 2089081 = 1566811) B1566811
theorem B1466651 : Blo 976593 1466651 := bstep (se 1 (by rfl) ⟨1099988, by rfl⟩ : syracuseStep 1466651 = 2199977) B2199977
theorem B3138311 : Blo 976593 3138311 := bstep (se 1 (by rfl) ⟨2353733, by rfl⟩ : syracuseStep 3138311 = 4707467) B4707467
theorem B38691703 : Blo 976593 38691703 := bstep (se 1 (by rfl) ⟨29018777, by rfl⟩ : syracuseStep 38691703 = 58037555) B58037555
theorem B9397403 : Blo 976593 9397403 := bstep (se 1 (by rfl) ⟨7048052, by rfl⟩ : syracuseStep 9397403 = 14096105) B14096105
theorem B9528509 : Blo 976593 9528509 := bstep (se 3 (by rfl) ⟨1786595, by rfl⟩ : syracuseStep 9528509 = 3573191) B3573191
theorem B1467719 : Blo 976593 1467719 := bstep (se 1 (by rfl) ⟨1100789, by rfl⟩ : syracuseStep 1467719 = 2201579) B2201579
theorem B11134745 : Blo 976593 11134745 := bstep (se 2 (by rfl) ⟨4175529, by rfl⟩ : syracuseStep 11134745 = 8351059) B8351059
theorem B1468271 : Blo 976593 1468271 := bstep (se 1 (by rfl) ⟨1101203, by rfl⟩ : syracuseStep 1468271 = 2202407) B2202407
theorem B1468667 : Blo 976593 1468667 := bstep (se 1 (by rfl) ⟨1101500, by rfl⟩ : syracuseStep 1468667 = 2203001) B2203001
theorem B2353427 : Blo 976593 2353427 := bstep (se 1 (by rfl) ⟨1765070, by rfl⟩ : syracuseStep 2353427 = 3530141) B3530141
theorem B1468799 : Blo 976593 1468799 := bstep (se 1 (by rfl) ⟨1101599, by rfl⟩ : syracuseStep 1468799 = 2203199) B2203199
theorem B3762623 : Blo 976593 3762623 := bstep (se 1 (by rfl) ⟨2821967, by rfl⟩ : syracuseStep 3762623 = 5643935) B5643935
theorem B1469351 : Blo 976593 1469351 := bstep (se 1 (by rfl) ⟨1102013, by rfl⟩ : syracuseStep 1469351 = 2204027) B2204027
theorem B978159 : Blo 976593 978159 := bstep (se 1 (by rfl) ⟨733619, by rfl⟩ : syracuseStep 978159 = 1467239) B1467239
theorem B71331191 : Blo 976593 71331191 := bstep (se 1 (by rfl) ⟨53498393, by rfl⟩ : syracuseStep 71331191 = 106996787) B106996787
theorem B1469855 : Blo 976593 1469855 := bstep (se 1 (by rfl) ⟨1102391, by rfl⟩ : syracuseStep 1469855 = 2204783) B2204783
theorem B1469993 : Blo 976593 1469993 := bstep (se 2 (by rfl) ⟨551247, by rfl⟩ : syracuseStep 1469993 = 1102495) B1102495
theorem B25063019 : Blo 976593 25063019 := bstep (se 1 (by rfl) ⟨18797264, by rfl⟩ : syracuseStep 25063019 = 37594529) B37594529
theorem B1470119 : Blo 976593 1470119 := bstep (se 1 (by rfl) ⟨1102589, by rfl⟩ : syracuseStep 1470119 = 2205179) B2205179
theorem B978623 : Blo 976593 978623 := bstep (se 1 (by rfl) ⟨733967, by rfl⟩ : syracuseStep 978623 = 1467935) B1467935
theorem B978671 : Blo 976593 978671 := bstep (se 1 (by rfl) ⟨734003, by rfl⟩ : syracuseStep 978671 = 1468007) B1468007
theorem B19328861 : Blo 976593 19328861 := bstep (se 3 (by rfl) ⟨3624161, by rfl⟩ : syracuseStep 19328861 = 7248323) B7248323
theorem B3305339 : Blo 976593 3305339 := bstep (se 1 (by rfl) ⟨2479004, by rfl⟩ : syracuseStep 3305339 = 4958009) B4958009
theorem B3305663 : Blo 976593 3305663 := bstep (se 1 (by rfl) ⟨2479247, by rfl⟩ : syracuseStep 3305663 = 4958495) B4958495
theorem B979195 : Blo 976593 979195 := bstep (se 1 (by rfl) ⟨734396, by rfl⟩ : syracuseStep 979195 = 1468793) B1468793
theorem B979247 : Blo 976593 979247 := bstep (se 1 (by rfl) ⟨734435, by rfl⟩ : syracuseStep 979247 = 1468871) B1468871
theorem B1470767 : Blo 976593 1470767 := bstep (se 1 (by rfl) ⟨1103075, by rfl⟩ : syracuseStep 1470767 = 2206151) B2206151
theorem B23851421 : Blo 976593 23851421 := bstep (se 3 (by rfl) ⟨4472141, by rfl⟩ : syracuseStep 23851421 = 8944283) B8944283
theorem B980127 : Blo 976593 980127 := bstep (se 1 (by rfl) ⟨735095, by rfl⟩ : syracuseStep 980127 = 1470191) B1470191
theorem B980191 : Blo 976593 980191 := bstep (se 1 (by rfl) ⟨735143, by rfl⟩ : syracuseStep 980191 = 1470287) B1470287
theorem B8942825 : Blo 976593 8942825 := bstep (se 2 (by rfl) ⟨3353559, by rfl⟩ : syracuseStep 8942825 = 6707119) B6707119
theorem B980479 : Blo 976593 980479 := bstep (se 1 (by rfl) ⟨735359, by rfl⟩ : syracuseStep 980479 = 1470719) B1470719
theorem B13563425 : Blo 976593 13563425 := bstep (se 2 (by rfl) ⟨5086284, by rfl⟩ : syracuseStep 13563425 = 10172569) B10172569
theorem B2782799 : Blo 976593 2782799 := bstep (se 1 (by rfl) ⟨2087099, by rfl⟩ : syracuseStep 2782799 = 4174199) B4174199
theorem B5568263 : Blo 976593 5568263 := bstep (se 1 (by rfl) ⟨4176197, by rfl⟩ : syracuseStep 5568263 = 8352395) B8352395
theorem B248117903 : Blo 976593 248117903 := bstep (se 1 (by rfl) ⟨186088427, by rfl⟩ : syracuseStep 248117903 = 372176855) B372176855
theorem B2784233 : Blo 976593 2784233 := bstep (se 2 (by rfl) ⟨1044087, by rfl⟩ : syracuseStep 2784233 = 2088175) B2088175
theorem B5570153 : Blo 976593 5570153 := bstep (se 2 (by rfl) ⟨2088807, by rfl⟩ : syracuseStep 5570153 = 4177615) B4177615
theorem B69664835 : Blo 976593 69664835 := bstep (se 1 (by rfl) ⟨52248626, by rfl⟩ : syracuseStep 69664835 = 104497253) B104497253
theorem B2785441 : Blo 976593 2785441 := bstep (se 2 (by rfl) ⟨1044540, by rfl⟩ : syracuseStep 2785441 = 2089081) B2089081
theorem B1672039 : Blo 976593 1672039 := bstep (se 1 (by rfl) ⟨1254029, by rfl⟩ : syracuseStep 1672039 = 2508059) B2508059
theorem B36177043 : Blo 976593 36177043 := bstep (se 1 (by rfl) ⟨27132782, by rfl⟩ : syracuseStep 36177043 = 54265565) B54265565
theorem B7047107 : Blo 976593 7047107 := bstep (se 1 (by rfl) ⟨5285330, by rfl⟩ : syracuseStep 7047107 = 10570661) B10570661
theorem B8916263 : Blo 976593 8916263 := bstep (se 1 (by rfl) ⟨6687197, by rfl⟩ : syracuseStep 8916263 = 13374395) B13374395
theorem B8360081 : Blo 976593 8360081 := bstep (se 2 (by rfl) ⟨3135030, by rfl⟩ : syracuseStep 8360081 = 6270061) B6270061
theorem B4460827 : Blo 976593 4460827 := bstep (se 1 (by rfl) ⟨3345620, by rfl⟩ : syracuseStep 4460827 = 6691241) B6691241
theorem B7541191 : Blo 976593 7541191 := bstep (se 1 (by rfl) ⟨5655893, by rfl⟩ : syracuseStep 7541191 = 11311787) B11311787
theorem B2200175 : Blo 976593 2200175 := bstep (se 1 (by rfl) ⟨1650131, by rfl⟩ : syracuseStep 2200175 = 3300263) B3300263
theorem B2200283 : Blo 976593 2200283 := bstep (se 1 (by rfl) ⟨1650212, by rfl⟩ : syracuseStep 2200283 = 3300425) B3300425
theorem B11146409 : Blo 976593 11146409 := bstep (se 2 (by rfl) ⟨4179903, by rfl⟩ : syracuseStep 11146409 = 8359807) B8359807
theorem B6264935 : Blo 976593 6264935 := bstep (se 1 (by rfl) ⟨4698701, by rfl⟩ : syracuseStep 6264935 = 9397403) B9397403
theorem B2201849 : Blo 976593 2201849 := bstep (se 2 (by rfl) ⟨825693, by rfl⟩ : syracuseStep 2201849 = 1651387) B1651387
theorem B17833375 : Blo 976593 17833375 := bstep (se 1 (by rfl) ⟨13375031, by rfl⟩ : syracuseStep 17833375 = 26750063) B26750063
theorem B47554127 : Blo 976593 47554127 := bstep (se 1 (by rfl) ⟨35665595, by rfl⟩ : syracuseStep 47554127 = 71331191) B71331191
theorem B12885907 : Blo 976593 12885907 := bstep (se 1 (by rfl) ⟨9664430, by rfl⟩ : syracuseStep 12885907 = 19328861) B19328861
theorem B2203559 : Blo 976593 2203559 := bstep (se 1 (by rfl) ⟨1652669, by rfl⟩ : syracuseStep 2203559 = 3305339) B3305339
theorem B2203775 : Blo 976593 2203775 := bstep (se 1 (by rfl) ⟨1652831, by rfl⟩ : syracuseStep 2203775 = 3305663) B3305663
theorem B15900947 : Blo 976593 15900947 := bstep (se 1 (by rfl) ⟨11925710, by rfl⟩ : syracuseStep 15900947 = 23851421) B23851421
theorem B3712175 : Blo 976593 3712175 := bstep (se 1 (by rfl) ⟨2784131, by rfl⟩ : syracuseStep 3712175 = 5568263) B5568263
theorem B5580359 : Blo 976593 5580359 := bstep (se 1 (by rfl) ⟨4185269, by rfl⟩ : syracuseStep 5580359 = 8370539) B8370539
theorem B3713435 : Blo 976593 3713435 := bstep (se 1 (by rfl) ⟨2785076, by rfl⟩ : syracuseStep 3713435 = 5570153) B5570153
theorem B3714407 : Blo 976593 3714407 := bstep (se 1 (by rfl) ⟨2785805, by rfl⟩ : syracuseStep 3714407 = 5571611) B5571611
theorem B51588937 : Blo 976593 51588937 := bstep (se 2 (by rfl) ⟨19345851, by rfl⟩ : syracuseStep 51588937 = 38691703) B38691703
theorem B3715409 : Blo 976593 3715409 := bstep (se 2 (by rfl) ⟨1393278, by rfl⟩ : syracuseStep 3715409 = 2786557) B2786557
theorem B8368829 : Blo 976593 8368829 := bstep (se 3 (by rfl) ⟨1569155, by rfl⟩ : syracuseStep 8368829 = 3138311) B3138311
theorem B3716351 : Blo 976593 3716351 := bstep (se 1 (by rfl) ⟨2787263, by rfl⟩ : syracuseStep 3716351 = 5574527) B5574527
theorem B7943591 : Blo 976593 7943591 := bstep (se 1 (by rfl) ⟨5957693, by rfl⟩ : syracuseStep 7943591 = 11915387) B11915387
theorem B3717535 : Blo 976593 3717535 := bstep (se 1 (by rfl) ⟨2788151, by rfl⟩ : syracuseStep 3717535 = 5576303) B5576303
theorem B28261871 : Blo 976593 28261871 := bstep (se 1 (by rfl) ⟨21196403, by rfl⟩ : syracuseStep 28261871 = 42392807) B42392807
theorem B3718781 : Blo 976593 3718781 := bstep (se 3 (by rfl) ⟨697271, by rfl⟩ : syracuseStep 3718781 = 1394543) B1394543
theorem B2473679 : Blo 976593 2473679 := bstep (se 1 (by rfl) ⟨1855259, by rfl⟩ : syracuseStep 2473679 = 3710519) B3710519
theorem B7061431 : Blo 976593 7061431 := bstep (se 1 (by rfl) ⟨5296073, by rfl⟩ : syracuseStep 7061431 = 10592147) B10592147
theorem B3129587 : Blo 976593 3129587 := bstep (se 1 (by rfl) ⟨2347190, by rfl⟩ : syracuseStep 3129587 = 4694381) B4694381
theorem B3523565 : Blo 976593 3523565 := bstep (se 3 (by rfl) ⟨660668, by rfl⟩ : syracuseStep 3523565 = 1321337) B1321337
theorem B7423163 : Blo 976593 7423163 := bstep (se 1 (by rfl) ⟨5567372, by rfl⟩ : syracuseStep 7423163 = 11134745) B11134745
theorem B2508415 : Blo 976593 2508415 := bstep (se 1 (by rfl) ⟨1881311, by rfl⟩ : syracuseStep 2508415 = 3762623) B3762623
theorem B1100263 : Blo 976593 1100263 := bstep (se 1 (by rfl) ⟨825197, by rfl⟩ : syracuseStep 1100263 = 1650395) B1650395
theorem B7424621 : Blo 976593 7424621 := bstep (se 3 (by rfl) ⟨1392116, by rfl⟩ : syracuseStep 7424621 = 2784233) B2784233
theorem B7064489 : Blo 976593 7064489 := bstep (se 2 (by rfl) ⟨2649183, by rfl⟩ : syracuseStep 7064489 = 5298367) B5298367
theorem B1855199 : Blo 976593 1855199 := bstep (se 1 (by rfl) ⟨1391399, by rfl⟩ : syracuseStep 1855199 = 2782799) B2782799
theorem B5295881 : Blo 976593 5295881 := bstep (se 2 (by rfl) ⟨1985955, by rfl⟩ : syracuseStep 5295881 = 3971911) B3971911
theorem B15880697 : Blo 976593 15880697 := bstep (se 2 (by rfl) ⟨5955261, by rfl⟩ : syracuseStep 15880697 = 11910523) B11910523
theorem B3297833 : Blo 976593 3297833 := bstep (se 2 (by rfl) ⟨1236687, by rfl⟩ : syracuseStep 3297833 = 2473375) B2473375
theorem B1102783 : Blo 976593 1102783 := bstep (se 1 (by rfl) ⟨827087, by rfl⟩ : syracuseStep 1102783 = 1654175) B1654175
theorem B22565945 : Blo 976593 22565945 := bstep (se 2 (by rfl) ⟨8462229, by rfl⟩ : syracuseStep 22565945 = 16924459) B16924459
theorem B2479835 : Blo 976593 2479835 := bstep (se 1 (by rfl) ⟨1859876, by rfl⟩ : syracuseStep 2479835 = 3719753) B3719753
theorem B142891199 : Blo 976593 142891199 := bstep (se 1 (by rfl) ⟨107168399, by rfl⟩ : syracuseStep 142891199 = 214336799) B214336799
theorem B14080999 : Blo 976593 14080999 := bstep (se 1 (by rfl) ⟨10560749, by rfl⟩ : syracuseStep 14080999 = 21121499) B21121499
theorem B1858555 : Blo 976593 1858555 := bstep (se 1 (by rfl) ⟨1393916, by rfl⟩ : syracuseStep 1858555 = 2787833) B2787833
theorem B1465583 : Blo 976593 1465583 := bstep (se 1 (by rfl) ⟨1099187, by rfl⟩ : syracuseStep 1465583 = 2198375) B2198375
theorem B50879771 : Blo 976593 50879771 := bstep (se 1 (by rfl) ⟨38159828, by rfl⟩ : syracuseStep 50879771 = 76319657) B76319657
theorem B4185371 : Blo 976593 4185371 := bstep (se 1 (by rfl) ⟨3139028, by rfl⟩ : syracuseStep 4185371 = 6278057) B6278057
theorem B7429967 : Blo 976593 7429967 := bstep (se 1 (by rfl) ⟨5572475, by rfl⟩ : syracuseStep 7429967 = 11144951) B11144951
theorem B3301559 : Blo 976593 3301559 := bstep (se 1 (by rfl) ⟨2476169, by rfl⟩ : syracuseStep 3301559 = 4952339) B4952339
theorem B2089235 : Blo 976593 2089235 := bstep (se 1 (by rfl) ⟨1566926, by rfl⟩ : syracuseStep 2089235 = 3133853) B3133853
theorem B1466921 : Blo 976593 1466921 := bstep (se 2 (by rfl) ⟨550095, by rfl⟩ : syracuseStep 1466921 = 1100191) B1100191
theorem B1467119 : Blo 976593 1467119 := bstep (se 1 (by rfl) ⟨1100339, by rfl⟩ : syracuseStep 1467119 = 2200679) B2200679
theorem B1467551 : Blo 976593 1467551 := bstep (se 1 (by rfl) ⟨1100663, by rfl⟩ : syracuseStep 1467551 = 2201327) B2201327
theorem B1468073 : Blo 976593 1468073 := bstep (se 2 (by rfl) ⟨550527, by rfl⟩ : syracuseStep 1468073 = 1101055) B1101055
theorem B1468169 : Blo 976593 1468169 := bstep (se 2 (by rfl) ⟨550563, by rfl⟩ : syracuseStep 1468169 = 1101127) B1101127
theorem B976667 : Blo 976593 976667 := bstep (se 1 (by rfl) ⟨732500, by rfl⟩ : syracuseStep 976667 = 1465001) B1465001
theorem B976731 : Blo 976593 976731 := bstep (se 1 (by rfl) ⟨732548, by rfl⟩ : syracuseStep 976731 = 1465097) B1465097
theorem B3303449 : Blo 976593 3303449 := bstep (se 2 (by rfl) ⟨1238793, by rfl⟩ : syracuseStep 3303449 = 2477587) B2477587
theorem B977343 : Blo 976593 977343 := bstep (se 1 (by rfl) ⟨733007, by rfl⟩ : syracuseStep 977343 = 1466015) B1466015
theorem B1567183 : Blo 976593 1567183 := bstep (se 1 (by rfl) ⟨1175387, by rfl⟩ : syracuseStep 1567183 = 2350775) B2350775
theorem B977615 : Blo 976593 977615 := bstep (se 1 (by rfl) ⟨733211, by rfl⟩ : syracuseStep 977615 = 1466423) B1466423
theorem B1469255 : Blo 976593 1469255 := bstep (se 1 (by rfl) ⟨1101941, by rfl⟩ : syracuseStep 1469255 = 2203883) B2203883
theorem B977767 : Blo 976593 977767 := bstep (se 1 (by rfl) ⟨733325, by rfl⟩ : syracuseStep 977767 = 1466651) B1466651
theorem B6352339 : Blo 976593 6352339 := bstep (se 1 (by rfl) ⟨4764254, by rfl⟩ : syracuseStep 6352339 = 9528509) B9528509
theorem B978479 : Blo 976593 978479 := bstep (se 1 (by rfl) ⟨733859, by rfl⟩ : syracuseStep 978479 = 1467719) B1467719
theorem B978847 : Blo 976593 978847 := bstep (se 1 (by rfl) ⟨734135, by rfl⟩ : syracuseStep 978847 = 1468271) B1468271
theorem B1470443 : Blo 976593 1470443 := bstep (se 1 (by rfl) ⟨1102832, by rfl⟩ : syracuseStep 1470443 = 2205665) B2205665
theorem B1470491 : Blo 976593 1470491 := bstep (se 1 (by rfl) ⟨1102868, by rfl⟩ : syracuseStep 1470491 = 2205737) B2205737
theorem B979111 : Blo 976593 979111 := bstep (se 1 (by rfl) ⟨734333, by rfl⟩ : syracuseStep 979111 = 1468667) B1468667
theorem B1568951 : Blo 976593 1568951 := bstep (se 1 (by rfl) ⟨1176713, by rfl⟩ : syracuseStep 1568951 = 2353427) B2353427
theorem B979199 : Blo 976593 979199 := bstep (se 1 (by rfl) ⟨734399, by rfl⟩ : syracuseStep 979199 = 1468799) B1468799
theorem B979567 : Blo 976593 979567 := bstep (se 1 (by rfl) ⟨734675, by rfl⟩ : syracuseStep 979567 = 1469351) B1469351
theorem B14119865 : Blo 976593 14119865 := bstep (se 2 (by rfl) ⟨5294949, by rfl⟩ : syracuseStep 14119865 = 10589899) B10589899
theorem B979903 : Blo 976593 979903 := bstep (se 1 (by rfl) ⟨734927, by rfl⟩ : syracuseStep 979903 = 1469855) B1469855
theorem B979995 : Blo 976593 979995 := bstep (se 1 (by rfl) ⟨734996, by rfl⟩ : syracuseStep 979995 = 1469993) B1469993
theorem B16708679 : Blo 976593 16708679 := bstep (se 1 (by rfl) ⟨12531509, by rfl⟩ : syracuseStep 16708679 = 25063019) B25063019
theorem B980079 : Blo 976593 980079 := bstep (se 1 (by rfl) ⟨735059, by rfl⟩ : syracuseStep 980079 = 1470119) B1470119
theorem B980511 : Blo 976593 980511 := bstep (se 1 (by rfl) ⟨735383, by rfl⟩ : syracuseStep 980511 = 1470767) B1470767
theorem B4945535 : Blo 976593 4945535 := bstep (se 1 (by rfl) ⟨3709151, by rfl⟩ : syracuseStep 4945535 = 7418303) B7418303
theorem B3307283 : Blo 976593 3307283 := bstep (se 1 (by rfl) ⟨2480462, by rfl⟩ : syracuseStep 3307283 = 4960925) B4960925
theorem B3307499 : Blo 976593 3307499 := bstep (se 1 (by rfl) ⟨2480624, by rfl⟩ : syracuseStep 3307499 = 4961249) B4961249
theorem B5961883 : Blo 976593 5961883 := bstep (se 1 (by rfl) ⟨4471412, by rfl⟩ : syracuseStep 5961883 = 8942825) B8942825
theorem B9042283 : Blo 976593 9042283 := bstep (se 1 (by rfl) ⟨6781712, by rfl⟩ : syracuseStep 9042283 = 13563425) B13563425
theorem B3308039 : Blo 976593 3308039 := bstep (se 1 (by rfl) ⟨2481029, by rfl⟩ : syracuseStep 3308039 = 4962059) B4962059
theorem B165411935 : Blo 976593 165411935 := bstep (se 1 (by rfl) ⟨124058951, by rfl⟩ : syracuseStep 165411935 = 248117903) B248117903
theorem B3308903 : Blo 976593 3308903 := bstep (se 1 (by rfl) ⟨2481677, by rfl⟩ : syracuseStep 3308903 = 4963355) B4963355
theorem B4948775 : Blo 976593 4948775 := bstep (se 1 (by rfl) ⟨3711581, by rfl⟩ : syracuseStep 4948775 = 7423163) B7423163
theorem B2229385 : Blo 976593 2229385 := bstep (se 2 (by rfl) ⟨836019, by rfl⟩ : syracuseStep 2229385 = 1672039) B1672039
theorem B48236057 : Blo 976593 48236057 := bstep (se 2 (by rfl) ⟨18088521, by rfl⟩ : syracuseStep 48236057 = 36177043) B36177043
theorem B4949747 : Blo 976593 4949747 := bstep (se 1 (by rfl) ⟨3712310, by rfl⟩ : syracuseStep 4949747 = 7424621) B7424621
theorem B5573387 : Blo 976593 5573387 := bstep (se 1 (by rfl) ⟨4180040, by rfl⟩ : syracuseStep 5573387 = 8360081) B8360081
theorem B10587131 : Blo 976593 10587131 := bstep (se 1 (by rfl) ⟨7940348, by rfl⟩ : syracuseStep 10587131 = 15880697) B15880697
theorem B2198555 : Blo 976593 2198555 := bstep (se 1 (by rfl) ⟨1648916, by rfl⟩ : syracuseStep 2198555 = 3297833) B3297833
theorem B15043963 : Blo 976593 15043963 := bstep (se 1 (by rfl) ⟨11282972, by rfl⟩ : syracuseStep 15043963 = 22565945) B22565945
theorem B95260799 : Blo 976593 95260799 := bstep (se 1 (by rfl) ⟨71445599, by rfl⟩ : syracuseStep 95260799 = 142891199) B142891199
theorem B33919847 : Blo 976593 33919847 := bstep (se 1 (by rfl) ⟨25439885, by rfl⟩ : syracuseStep 33919847 = 50879771) B50879771
theorem B68785249 : Blo 976593 68785249 := bstep (se 2 (by rfl) ⟨25794468, by rfl⟩ : syracuseStep 68785249 = 51588937) B51588937
theorem B4953311 : Blo 976593 4953311 := bstep (se 1 (by rfl) ⟨3714983, by rfl⟩ : syracuseStep 4953311 = 7429967) B7429967
theorem B2201039 : Blo 976593 2201039 := bstep (se 1 (by rfl) ⟨1650779, by rfl⟩ : syracuseStep 2201039 = 3301559) B3301559
theorem B2202299 : Blo 976593 2202299 := bstep (se 1 (by rfl) ⟨1651724, by rfl⟩ : syracuseStep 2202299 = 3303449) B3303449
theorem B5579219 : Blo 976593 5579219 := bstep (se 1 (by rfl) ⟨4184414, by rfl⟩ : syracuseStep 5579219 = 8368829) B8368829
theorem B4956713 : Blo 976593 4956713 := bstep (se 2 (by rfl) ⟨1858767, by rfl⟩ : syracuseStep 4956713 = 3717535) B3717535
theorem B9413243 : Blo 976593 9413243 := bstep (se 1 (by rfl) ⟨7059932, by rfl⟩ : syracuseStep 9413243 = 14119865) B14119865
theorem B13378213 : Blo 976593 13378213 := bstep (se 4 (by rfl) ⟨1254207, by rfl⟩ : syracuseStep 13378213 = 2508415) B2508415
theorem B2204855 : Blo 976593 2204855 := bstep (se 1 (by rfl) ⟨1653641, by rfl⟩ : syracuseStep 2204855 = 3307283) B3307283
theorem B2204999 : Blo 976593 2204999 := bstep (se 1 (by rfl) ⟨1653749, by rfl⟩ : syracuseStep 2204999 = 3307499) B3307499
theorem B2205359 : Blo 976593 2205359 := bstep (se 1 (by rfl) ⟨1654019, by rfl⟩ : syracuseStep 2205359 = 3308039) B3308039
theorem B110274623 : Blo 976593 110274623 := bstep (se 1 (by rfl) ⟨82705967, by rfl⟩ : syracuseStep 110274623 = 165411935) B165411935
theorem B2205935 : Blo 976593 2205935 := bstep (se 1 (by rfl) ⟨1654451, by rfl⟩ : syracuseStep 2205935 = 3308903) B3308903
theorem B1649119 : Blo 976593 1649119 := bstep (se 1 (by rfl) ⟨1236839, by rfl⟩ : syracuseStep 1649119 = 2473679) B2473679
theorem B17181209 : Blo 976593 17181209 := bstep (se 2 (by rfl) ⟨6442953, by rfl⟩ : syracuseStep 17181209 = 12885907) B12885907
theorem B9415241 : Blo 976593 9415241 := bstep (se 2 (by rfl) ⟨3530715, by rfl⟩ : syracuseStep 9415241 = 7061431) B7061431
theorem B46443223 : Blo 976593 46443223 := bstep (se 1 (by rfl) ⟨34832417, by rfl⟩ : syracuseStep 46443223 = 69664835) B69664835
theorem B3713921 : Blo 976593 3713921 := bstep (se 2 (by rfl) ⟨1392720, by rfl⟩ : syracuseStep 3713921 = 2785441) B2785441
theorem B4698071 : Blo 976593 4698071 := bstep (se 1 (by rfl) ⟨3523553, by rfl⟩ : syracuseStep 4698071 = 7047107) B7047107
theorem B5944175 : Blo 976593 5944175 := bstep (se 1 (by rfl) ⟨4458131, by rfl⟩ : syracuseStep 5944175 = 8916263) B8916263
theorem B1653223 : Blo 976593 1653223 := bstep (se 1 (by rfl) ⟨1239917, by rfl⟩ : syracuseStep 1653223 = 2479835) B2479835
theorem B4176623 : Blo 976593 4176623 := bstep (se 1 (by rfl) ⟨3132467, by rfl⟩ : syracuseStep 4176623 = 6264935) B6264935
theorem B8469785 : Blo 976593 8469785 := bstep (se 2 (by rfl) ⟨3176169, by rfl⟩ : syracuseStep 8469785 = 6352339) B6352339
theorem B31702751 : Blo 976593 31702751 := bstep (se 1 (by rfl) ⟨23777063, by rfl⟩ : syracuseStep 31702751 = 47554127) B47554127
theorem B1392823 : Blo 976593 1392823 := bstep (se 1 (by rfl) ⟨1044617, by rfl⟩ : syracuseStep 1392823 = 2089235) B2089235
theorem B10600631 : Blo 976593 10600631 := bstep (se 1 (by rfl) ⟨7950473, by rfl⟩ : syracuseStep 10600631 = 15900947) B15900947
theorem B5947769 : Blo 976593 5947769 := bstep (se 2 (by rfl) ⟨2230413, by rfl⟩ : syracuseStep 5947769 = 4460827) B4460827
theorem B2474783 : Blo 976593 2474783 := bstep (se 1 (by rfl) ⟨1856087, by rfl⟩ : syracuseStep 2474783 = 3712175) B3712175
theorem B3720239 : Blo 976593 3720239 := bstep (se 1 (by rfl) ⟨2790179, by rfl⟩ : syracuseStep 3720239 = 5580359) B5580359
theorem B2475623 : Blo 976593 2475623 := bstep (se 1 (by rfl) ⟨1856717, by rfl⟩ : syracuseStep 2475623 = 3713435) B3713435
theorem B95111333 : Blo 976593 95111333 := bstep (se 4 (by rfl) ⟨8916687, by rfl⟩ : syracuseStep 95111333 = 17833375) B17833375
theorem B2476271 : Blo 976593 2476271 := bstep (se 1 (by rfl) ⟨1857203, by rfl⟩ : syracuseStep 2476271 = 3714407) B3714407
theorem B7949177 : Blo 976593 7949177 := bstep (se 2 (by rfl) ⟨2980941, by rfl⟩ : syracuseStep 7949177 = 5961883) B5961883
theorem B2476939 : Blo 976593 2476939 := bstep (se 1 (by rfl) ⟨1857704, by rfl⟩ : syracuseStep 2476939 = 3715409) B3715409
theorem B11160989 : Blo 976593 11160989 := bstep (se 3 (by rfl) ⟨2092685, by rfl⟩ : syracuseStep 11160989 = 4185371) B4185371
theorem B2477567 : Blo 976593 2477567 := bstep (se 1 (by rfl) ⟨1858175, by rfl⟩ : syracuseStep 2477567 = 3716351) B3716351
theorem B5295727 : Blo 976593 5295727 := bstep (se 1 (by rfl) ⟨3971795, by rfl⟩ : syracuseStep 5295727 = 7943591) B7943591
theorem B3297023 : Blo 976593 3297023 := bstep (se 1 (by rfl) ⟨2472767, by rfl⟩ : syracuseStep 3297023 = 4945535) B4945535
theorem B2478073 : Blo 976593 2478073 := bstep (se 2 (by rfl) ⟨929277, by rfl⟩ : syracuseStep 2478073 = 1858555) B1858555
theorem B2479187 : Blo 976593 2479187 := bstep (se 1 (by rfl) ⟨1859390, by rfl⟩ : syracuseStep 2479187 = 3718781) B3718781
theorem B2086391 : Blo 976593 2086391 := bstep (se 1 (by rfl) ⟨1564793, by rfl⟩ : syracuseStep 2086391 = 3129587) B3129587
theorem B2349043 : Blo 976593 2349043 := bstep (se 1 (by rfl) ⟨1761782, by rfl⟩ : syracuseStep 2349043 = 3523565) B3523565
theorem B4709659 : Blo 976593 4709659 := bstep (se 1 (by rfl) ⟨3532244, by rfl⟩ : syracuseStep 4709659 = 7064489) B7064489
theorem B1236799 : Blo 976593 1236799 := bstep (se 1 (by rfl) ⟨927599, by rfl⟩ : syracuseStep 1236799 = 1855199) B1855199
theorem B1466783 : Blo 976593 1466783 := bstep (se 1 (by rfl) ⟨1100087, by rfl⟩ : syracuseStep 1466783 = 2200175) B2200175
theorem B1466855 : Blo 976593 1466855 := bstep (se 1 (by rfl) ⟨1100141, by rfl⟩ : syracuseStep 1466855 = 2200283) B2200283
theorem B2089577 : Blo 976593 2089577 := bstep (se 2 (by rfl) ⟨783591, by rfl⟩ : syracuseStep 2089577 = 1567183) B1567183
theorem B1467017 : Blo 976593 1467017 := bstep (se 2 (by rfl) ⟨550131, by rfl⟩ : syracuseStep 1467017 = 1100263) B1100263
theorem B7430939 : Blo 976593 7430939 := bstep (se 1 (by rfl) ⟨5573204, by rfl⟩ : syracuseStep 7430939 = 11146409) B11146409
theorem B1467899 : Blo 976593 1467899 := bstep (se 1 (by rfl) ⟨1100924, by rfl⟩ : syracuseStep 1467899 = 2201849) B2201849
theorem B977055 : Blo 976593 977055 := bstep (se 1 (by rfl) ⟨732791, by rfl⟩ : syracuseStep 977055 = 1465583) B1465583
theorem B1469039 : Blo 976593 1469039 := bstep (se 1 (by rfl) ⟨1101779, by rfl⟩ : syracuseStep 1469039 = 2203559) B2203559
theorem B1469183 : Blo 976593 1469183 := bstep (se 1 (by rfl) ⟨1101887, by rfl⟩ : syracuseStep 1469183 = 2203775) B2203775
theorem B977947 : Blo 976593 977947 := bstep (se 1 (by rfl) ⟨733460, by rfl⟩ : syracuseStep 977947 = 1466921) B1466921
theorem B978079 : Blo 976593 978079 := bstep (se 1 (by rfl) ⟨733559, by rfl⟩ : syracuseStep 978079 = 1467119) B1467119
theorem B10054921 : Blo 976593 10054921 := bstep (se 2 (by rfl) ⟨3770595, by rfl⟩ : syracuseStep 10054921 = 7541191) B7541191
theorem B978367 : Blo 976593 978367 := bstep (se 1 (by rfl) ⟨733775, by rfl⟩ : syracuseStep 978367 = 1467551) B1467551
theorem B978715 : Blo 976593 978715 := bstep (se 1 (by rfl) ⟨734036, by rfl⟩ : syracuseStep 978715 = 1468073) B1468073
theorem B978779 : Blo 976593 978779 := bstep (se 1 (by rfl) ⟨734084, by rfl⟩ : syracuseStep 978779 = 1468169) B1468169
theorem B1470377 : Blo 976593 1470377 := bstep (se 2 (by rfl) ⟨551391, by rfl⟩ : syracuseStep 1470377 = 1102783) B1102783
theorem B979503 : Blo 976593 979503 := bstep (se 1 (by rfl) ⟨734627, by rfl⟩ : syracuseStep 979503 = 1469255) B1469255
theorem B980295 : Blo 976593 980295 := bstep (se 1 (by rfl) ⟨735221, by rfl⟩ : syracuseStep 980295 = 1470443) B1470443
theorem B980327 : Blo 976593 980327 := bstep (se 1 (by rfl) ⟨735245, by rfl⟩ : syracuseStep 980327 = 1470491) B1470491
theorem B1045967 : Blo 976593 1045967 := bstep (se 1 (by rfl) ⟨784475, by rfl⟩ : syracuseStep 1045967 = 1568951) B1568951
theorem B12056377 : Blo 976593 12056377 := bstep (se 2 (by rfl) ⟨4521141, by rfl⟩ : syracuseStep 12056377 = 9042283) B9042283
theorem B11139119 : Blo 976593 11139119 := bstep (se 1 (by rfl) ⟨8354339, by rfl⟩ : syracuseStep 11139119 = 16708679) B16708679
theorem B18774665 : Blo 976593 18774665 := bstep (se 2 (by rfl) ⟨7040499, by rfl⟩ : syracuseStep 18774665 = 14080999) B14080999
theorem B14122349 : Blo 976593 14122349 := bstep (se 3 (by rfl) ⟨2647940, by rfl⟩ : syracuseStep 14122349 = 5295881) B5295881
theorem B18841247 : Blo 976593 18841247 := bstep (se 1 (by rfl) ⟨14130935, by rfl⟩ : syracuseStep 18841247 = 28261871) B28261871
theorem B15860717 : Blo 976593 15860717 := bstep (se 3 (by rfl) ⟨2973884, by rfl⟩ : syracuseStep 15860717 = 5947769) B5947769
theorem B63407555 : Blo 976593 63407555 := bstep (se 1 (by rfl) ⟨47555666, by rfl⟩ : syracuseStep 63407555 = 95111333) B95111333
theorem B7440659 : Blo 976593 7440659 := bstep (se 1 (by rfl) ⟨5580494, by rfl⟩ : syracuseStep 7440659 = 11160989) B11160989
theorem B2198015 : Blo 976593 2198015 := bstep (se 1 (by rfl) ⟨1648511, by rfl⟩ : syracuseStep 2198015 = 3297023) B3297023
theorem B63507199 : Blo 976593 63507199 := bstep (se 1 (by rfl) ⟨47630399, by rfl⟩ : syracuseStep 63507199 = 95260799) B95260799
theorem B22613231 : Blo 976593 22613231 := bstep (se 1 (by rfl) ⟨16959923, by rfl⟩ : syracuseStep 22613231 = 33919847) B33919847
theorem B2198825 : Blo 976593 2198825 := bstep (se 2 (by rfl) ⟨824559, by rfl⟩ : syracuseStep 2198825 = 1649119) B1649119
theorem B2789245 : Blo 976593 2789245 := bstep (se 3 (by rfl) ⟨522983, by rfl⟩ : syracuseStep 2789245 = 1045967) B1045967
theorem B13406561 : Blo 976593 13406561 := bstep (se 2 (by rfl) ⟨5027460, by rfl⟩ : syracuseStep 13406561 = 10054921) B10054921
theorem B20058617 : Blo 976593 20058617 := bstep (se 2 (by rfl) ⟨7521981, by rfl⟩ : syracuseStep 20058617 = 15043963) B15043963
theorem B4953959 : Blo 976593 4953959 := bstep (se 1 (by rfl) ⟨3715469, by rfl⟩ : syracuseStep 4953959 = 7430939) B7430939
theorem B2204297 : Blo 976593 2204297 := bstep (se 2 (by rfl) ⟨826611, by rfl⟩ : syracuseStep 2204297 = 1653223) B1653223
theorem B5646523 : Blo 976593 5646523 := bstep (se 1 (by rfl) ⟨4234892, by rfl⟩ : syracuseStep 5646523 = 8469785) B8469785
theorem B9414899 : Blo 976593 9414899 := bstep (se 1 (by rfl) ⟨7061174, by rfl⟩ : syracuseStep 9414899 = 14122349) B14122349
theorem B1649065 : Blo 976593 1649065 := bstep (se 2 (by rfl) ⟨618399, by rfl⟩ : syracuseStep 1649065 = 1236799) B1236799
theorem B12560831 : Blo 976593 12560831 := bstep (se 1 (by rfl) ⟨9420623, by rfl⟩ : syracuseStep 12560831 = 18841247) B18841247
theorem B12528229 : Blo 976593 12528229 := bstep (se 4 (by rfl) ⟨1174521, by rfl⟩ : syracuseStep 12528229 = 2349043) B2349043
theorem B1649855 : Blo 976593 1649855 := bstep (se 1 (by rfl) ⟨1237391, by rfl⟩ : syracuseStep 1649855 = 2474783) B2474783
theorem B17837617 : Blo 976593 17837617 := bstep (se 2 (by rfl) ⟨6689106, by rfl⟩ : syracuseStep 17837617 = 13378213) B13378213
theorem B32157371 : Blo 976593 32157371 := bstep (se 1 (by rfl) ⟨24118028, by rfl⟩ : syracuseStep 32157371 = 48236057) B48236057
theorem B1650415 : Blo 976593 1650415 := bstep (se 1 (by rfl) ⟨1237811, by rfl⟩ : syracuseStep 1650415 = 2475623) B2475623
theorem B1650847 : Blo 976593 1650847 := bstep (se 1 (by rfl) ⟨1238135, by rfl⟩ : syracuseStep 1650847 = 2476271) B2476271
theorem B3715591 : Blo 976593 3715591 := bstep (se 1 (by rfl) ⟨2786693, by rfl⟩ : syracuseStep 3715591 = 5573387) B5573387
theorem B7058087 : Blo 976593 7058087 := bstep (se 1 (by rfl) ⟨5293565, by rfl⟩ : syracuseStep 7058087 = 10587131) B10587131
theorem B1651711 : Blo 976593 1651711 := bstep (se 1 (by rfl) ⟨1238783, by rfl⟩ : syracuseStep 1651711 = 2477567) B2477567
theorem B1652791 : Blo 976593 1652791 := bstep (se 1 (by rfl) ⟨1239593, by rfl⟩ : syracuseStep 1652791 = 2479187) B2479187
theorem B1390927 : Blo 976593 1390927 := bstep (se 1 (by rfl) ⟨1043195, by rfl⟩ : syracuseStep 1390927 = 2086391) B2086391
theorem B7060969 : Blo 976593 7060969 := bstep (se 2 (by rfl) ⟨2647863, by rfl⟩ : syracuseStep 7060969 = 5295727) B5295727
theorem B3719479 : Blo 976593 3719479 := bstep (se 1 (by rfl) ⟨2789609, by rfl⟩ : syracuseStep 3719479 = 5579219) B5579219
theorem B1393051 : Blo 976593 1393051 := bstep (se 1 (by rfl) ⟨1044788, by rfl⟩ : syracuseStep 1393051 = 2089577) B2089577
theorem B6275495 : Blo 976593 6275495 := bstep (se 1 (by rfl) ⟨4706621, by rfl⟩ : syracuseStep 6275495 = 9413243) B9413243
theorem B73516415 : Blo 976593 73516415 := bstep (se 1 (by rfl) ⟨55137311, by rfl⟩ : syracuseStep 73516415 = 110274623) B110274623
theorem B11454139 : Blo 976593 11454139 := bstep (se 1 (by rfl) ⟨8590604, by rfl⟩ : syracuseStep 11454139 = 17181209) B17181209
theorem B6276827 : Blo 976593 6276827 := bstep (se 1 (by rfl) ⟨4707620, by rfl⟩ : syracuseStep 6276827 = 9415241) B9415241
theorem B2475947 : Blo 976593 2475947 := bstep (se 1 (by rfl) ⟨1856960, by rfl⟩ : syracuseStep 2475947 = 3713921) B3713921
theorem B16075169 : Blo 976593 16075169 := bstep (se 2 (by rfl) ⟨6028188, by rfl⟩ : syracuseStep 16075169 = 12056377) B12056377
theorem B3132047 : Blo 976593 3132047 := bstep (se 1 (by rfl) ⟨2349035, by rfl⟩ : syracuseStep 3132047 = 4698071) B4698071
theorem B7426079 : Blo 976593 7426079 := bstep (se 1 (by rfl) ⟨5569559, by rfl⟩ : syracuseStep 7426079 = 11139119) B11139119
theorem B6279545 : Blo 976593 6279545 := bstep (se 2 (by rfl) ⟨2354829, by rfl⟩ : syracuseStep 6279545 = 4709659) B4709659
theorem B7067087 : Blo 976593 7067087 := bstep (se 1 (by rfl) ⟨5300315, by rfl⟩ : syracuseStep 7067087 = 10600631) B10600631
theorem B1857097 : Blo 976593 1857097 := bstep (se 2 (by rfl) ⟨696411, by rfl⟩ : syracuseStep 1857097 = 1392823) B1392823
theorem B3299183 : Blo 976593 3299183 := bstep (se 1 (by rfl) ⟨2474387, by rfl⟩ : syracuseStep 3299183 = 4948775) B4948775
theorem B2480159 : Blo 976593 2480159 := bstep (se 1 (by rfl) ⟨1860119, by rfl⟩ : syracuseStep 2480159 = 3720239) B3720239
theorem B3299831 : Blo 976593 3299831 := bstep (se 1 (by rfl) ⟨2474873, by rfl⟩ : syracuseStep 3299831 = 4949747) B4949747
theorem B2972513 : Blo 976593 2972513 := bstep (se 2 (by rfl) ⟨1114692, by rfl⟩ : syracuseStep 2972513 = 2229385) B2229385
theorem B5299451 : Blo 976593 5299451 := bstep (se 1 (by rfl) ⟨3974588, by rfl⟩ : syracuseStep 5299451 = 7949177) B7949177
theorem B1465703 : Blo 976593 1465703 := bstep (se 1 (by rfl) ⟨1099277, by rfl⟩ : syracuseStep 1465703 = 2198555) B2198555
theorem B3302207 : Blo 976593 3302207 := bstep (se 1 (by rfl) ⟨2476655, by rfl⟩ : syracuseStep 3302207 = 4953311) B4953311
theorem B61924297 : Blo 976593 61924297 := bstep (se 2 (by rfl) ⟨23221611, by rfl⟩ : syracuseStep 61924297 = 46443223) B46443223
theorem B1467359 : Blo 976593 1467359 := bstep (se 1 (by rfl) ⟨1100519, by rfl⟩ : syracuseStep 1467359 = 2201039) B2201039
theorem B3302585 : Blo 976593 3302585 := bstep (se 2 (by rfl) ⟨1238469, by rfl⟩ : syracuseStep 3302585 = 2476939) B2476939
theorem B1468199 : Blo 976593 1468199 := bstep (se 1 (by rfl) ⟨1101149, by rfl⟩ : syracuseStep 1468199 = 2202299) B2202299
theorem B3304097 : Blo 976593 3304097 := bstep (se 2 (by rfl) ⟨1239036, by rfl⟩ : syracuseStep 3304097 = 2478073) B2478073
theorem B977855 : Blo 976593 977855 := bstep (se 1 (by rfl) ⟨733391, by rfl⟩ : syracuseStep 977855 = 1466783) B1466783
theorem B977903 : Blo 976593 977903 := bstep (se 1 (by rfl) ⟨733427, by rfl⟩ : syracuseStep 977903 = 1466855) B1466855
theorem B3304475 : Blo 976593 3304475 := bstep (se 1 (by rfl) ⟨2478356, by rfl⟩ : syracuseStep 3304475 = 4956713) B4956713
theorem B978011 : Blo 976593 978011 := bstep (se 1 (by rfl) ⟨733508, by rfl⟩ : syracuseStep 978011 = 1467017) B1467017
theorem B1469903 : Blo 976593 1469903 := bstep (se 1 (by rfl) ⟨1102427, by rfl⟩ : syracuseStep 1469903 = 2204855) B2204855
theorem B1469999 : Blo 976593 1469999 := bstep (se 1 (by rfl) ⟨1102499, by rfl⟩ : syracuseStep 1469999 = 2204999) B2204999
theorem B978599 : Blo 976593 978599 := bstep (se 1 (by rfl) ⟨733949, by rfl⟩ : syracuseStep 978599 = 1467899) B1467899
theorem B1470239 : Blo 976593 1470239 := bstep (se 1 (by rfl) ⟨1102679, by rfl⟩ : syracuseStep 1470239 = 2205359) B2205359
theorem B91713665 : Blo 976593 91713665 := bstep (se 2 (by rfl) ⟨34392624, by rfl⟩ : syracuseStep 91713665 = 68785249) B68785249
theorem B1470623 : Blo 976593 1470623 := bstep (se 1 (by rfl) ⟨1102967, by rfl⟩ : syracuseStep 1470623 = 2205935) B2205935
theorem B979359 : Blo 976593 979359 := bstep (se 1 (by rfl) ⟨734519, by rfl⟩ : syracuseStep 979359 = 1469039) B1469039
theorem B979455 : Blo 976593 979455 := bstep (se 1 (by rfl) ⟨734591, by rfl⟩ : syracuseStep 979455 = 1469183) B1469183
theorem B11137661 : Blo 976593 11137661 := bstep (se 3 (by rfl) ⟨2088311, by rfl⟩ : syracuseStep 11137661 = 4176623) B4176623
theorem B980251 : Blo 976593 980251 := bstep (se 1 (by rfl) ⟨735188, by rfl⟩ : syracuseStep 980251 = 1470377) B1470377
theorem B3962783 : Blo 976593 3962783 := bstep (se 1 (by rfl) ⟨2972087, by rfl⟩ : syracuseStep 3962783 = 5944175) B5944175
theorem B12516443 : Blo 976593 12516443 := bstep (se 1 (by rfl) ⟨9387332, by rfl⟩ : syracuseStep 12516443 = 18774665) B18774665
theorem B21135167 : Blo 976593 21135167 := bstep (se 1 (by rfl) ⟨15851375, by rfl⟩ : syracuseStep 21135167 = 31702751) B31702751
theorem B42271703 : Blo 976593 42271703 := bstep (se 1 (by rfl) ⟨31703777, by rfl⟩ : syracuseStep 42271703 = 63407555) B63407555
theorem B10716779 : Blo 976593 10716779 := bstep (se 1 (by rfl) ⟨8037584, by rfl⟩ : syracuseStep 10716779 = 16075169) B16075169
theorem B15075487 : Blo 976593 15075487 := bstep (se 1 (by rfl) ⟨11306615, by rfl⟩ : syracuseStep 15075487 = 22613231) B22613231
theorem B15272185 : Blo 976593 15272185 := bstep (se 2 (by rfl) ⟨5727069, by rfl⟩ : syracuseStep 15272185 = 11454139) B11454139
theorem B4950719 : Blo 976593 4950719 := bstep (se 1 (by rfl) ⟨3713039, by rfl⟩ : syracuseStep 4950719 = 7426079) B7426079
theorem B13372411 : Blo 976593 13372411 := bstep (se 1 (by rfl) ⟨10029308, by rfl⟩ : syracuseStep 13372411 = 20058617) B20058617
theorem B2198753 : Blo 976593 2198753 := bstep (se 2 (by rfl) ⟨824532, by rfl⟩ : syracuseStep 2198753 = 1649065) B1649065
theorem B84676265 : Blo 976593 84676265 := bstep (se 2 (by rfl) ⟨31753599, by rfl⟩ : syracuseStep 84676265 = 63507199) B63507199
theorem B2199455 : Blo 976593 2199455 := bstep (se 1 (by rfl) ⟨1649591, by rfl⟩ : syracuseStep 2199455 = 3299183) B3299183
theorem B2199887 : Blo 976593 2199887 := bstep (se 1 (by rfl) ⟨1649915, by rfl⟩ : syracuseStep 2199887 = 3299831) B3299831
theorem B2200553 : Blo 976593 2200553 := bstep (se 2 (by rfl) ⟨825207, by rfl⟩ : syracuseStep 2200553 = 1650415) B1650415
theorem B2201129 : Blo 976593 2201129 := bstep (se 2 (by rfl) ⟨825423, by rfl⟩ : syracuseStep 2201129 = 1650847) B1650847
theorem B2201471 : Blo 976593 2201471 := bstep (se 1 (by rfl) ⟨1651103, by rfl⟩ : syracuseStep 2201471 = 3302207) B3302207
theorem B4954121 : Blo 976593 4954121 := bstep (se 2 (by rfl) ⟨1857795, by rfl⟩ : syracuseStep 4954121 = 3715591) B3715591
theorem B2201723 : Blo 976593 2201723 := bstep (se 1 (by rfl) ⟨1651292, by rfl⟩ : syracuseStep 2201723 = 3302585) B3302585
theorem B2202281 : Blo 976593 2202281 := bstep (se 2 (by rfl) ⟨825855, by rfl⟩ : syracuseStep 2202281 = 1651711) B1651711
theorem B2202731 : Blo 976593 2202731 := bstep (se 1 (by rfl) ⟨1652048, by rfl⟩ : syracuseStep 2202731 = 3304097) B3304097
theorem B2202983 : Blo 976593 2202983 := bstep (se 1 (by rfl) ⟨1652237, by rfl⟩ : syracuseStep 2202983 = 3304475) B3304475
theorem B2203721 : Blo 976593 2203721 := bstep (se 2 (by rfl) ⟨826395, by rfl⟩ : syracuseStep 2203721 = 1652791) B1652791
theorem B9414625 : Blo 976593 9414625 := bstep (se 2 (by rfl) ⟨3530484, by rfl⟩ : syracuseStep 9414625 = 7060969) B7060969
theorem B4959305 : Blo 976593 4959305 := bstep (se 2 (by rfl) ⟨1859739, by rfl⟩ : syracuseStep 4959305 = 3719479) B3719479
theorem B1650631 : Blo 976593 1650631 := bstep (se 1 (by rfl) ⟨1237973, by rfl⟩ : syracuseStep 1650631 = 2475947) B2475947
theorem B4960439 : Blo 976593 4960439 := bstep (se 1 (by rfl) ⟨3720329, by rfl⟩ : syracuseStep 4960439 = 7440659) B7440659
theorem B1653439 : Blo 976593 1653439 := bstep (se 1 (by rfl) ⟨1240079, by rfl⟩ : syracuseStep 1653439 = 2480159) B2480159
theorem B1981675 : Blo 976593 1981675 := bstep (se 1 (by rfl) ⟨1486256, by rfl⟩ : syracuseStep 1981675 = 2972513) B2972513
theorem B3718993 : Blo 976593 3718993 := bstep (se 2 (by rfl) ⟨1394622, by rfl⟩ : syracuseStep 3718993 = 2789245) B2789245
theorem B6276599 : Blo 976593 6276599 := bstep (se 1 (by rfl) ⟨4707449, by rfl⟩ : syracuseStep 6276599 = 9414899) B9414899
theorem B8373887 : Blo 976593 8373887 := bstep (se 1 (by rfl) ⟨6280415, by rfl⟩ : syracuseStep 8373887 = 12560831) B12560831
theorem B2476129 : Blo 976593 2476129 := bstep (se 2 (by rfl) ⟨928548, by rfl⟩ : syracuseStep 2476129 = 1857097) B1857097
theorem B1099903 : Blo 976593 1099903 := bstep (se 1 (by rfl) ⟨824927, by rfl⟩ : syracuseStep 1099903 = 1649855) B1649855
theorem B7425107 : Blo 976593 7425107 := bstep (se 1 (by rfl) ⟨5568830, by rfl⟩ : syracuseStep 7425107 = 11137661) B11137661
theorem B1854569 : Blo 976593 1854569 := bstep (se 2 (by rfl) ⟨695463, by rfl⟩ : syracuseStep 1854569 = 1390927) B1390927
theorem B4705391 : Blo 976593 4705391 := bstep (se 1 (by rfl) ⟨3529043, by rfl⟩ : syracuseStep 4705391 = 7058087) B7058087
theorem B2641855 : Blo 976593 2641855 := bstep (se 1 (by rfl) ⟨1981391, by rfl⟩ : syracuseStep 2641855 = 3962783) B3962783
theorem B8344295 : Blo 976593 8344295 := bstep (se 1 (by rfl) ⟨6258221, by rfl⟩ : syracuseStep 8344295 = 12516443) B12516443
theorem B4183663 : Blo 976593 4183663 := bstep (se 1 (by rfl) ⟨3137747, by rfl⟩ : syracuseStep 4183663 = 6275495) B6275495
theorem B244569773 : Blo 976593 244569773 := bstep (se 3 (by rfl) ⟨45856832, by rfl⟩ : syracuseStep 244569773 = 91713665) B91713665
theorem B1857401 : Blo 976593 1857401 := bstep (se 2 (by rfl) ⟨696525, by rfl⟩ : syracuseStep 1857401 = 1393051) B1393051
theorem B10573811 : Blo 976593 10573811 := bstep (se 1 (by rfl) ⟨7930358, by rfl⟩ : syracuseStep 10573811 = 15860717) B15860717
theorem B4184551 : Blo 976593 4184551 := bstep (se 1 (by rfl) ⟨3138413, by rfl⟩ : syracuseStep 4184551 = 6276827) B6276827
theorem B82565729 : Blo 976593 82565729 := bstep (se 2 (by rfl) ⟨30962148, by rfl⟩ : syracuseStep 82565729 = 61924297) B61924297
theorem B1465343 : Blo 976593 1465343 := bstep (se 1 (by rfl) ⟨1099007, by rfl⟩ : syracuseStep 1465343 = 2198015) B2198015
theorem B2088031 : Blo 976593 2088031 := bstep (se 1 (by rfl) ⟨1566023, by rfl⟩ : syracuseStep 2088031 = 3132047) B3132047
theorem B1465883 : Blo 976593 1465883 := bstep (se 1 (by rfl) ⟨1099412, by rfl⟩ : syracuseStep 1465883 = 2198825) B2198825
theorem B8937707 : Blo 976593 8937707 := bstep (se 1 (by rfl) ⟨6703280, by rfl⟩ : syracuseStep 8937707 = 13406561) B13406561
theorem B7528697 : Blo 976593 7528697 := bstep (se 2 (by rfl) ⟨2823261, by rfl⟩ : syracuseStep 7528697 = 5646523) B5646523
theorem B4186363 : Blo 976593 4186363 := bstep (se 1 (by rfl) ⟨3139772, by rfl⟩ : syracuseStep 4186363 = 6279545) B6279545
theorem B16704305 : Blo 976593 16704305 := bstep (se 2 (by rfl) ⟨6264114, by rfl⟩ : syracuseStep 16704305 = 12528229) B12528229
theorem B4711391 : Blo 976593 4711391 := bstep (se 1 (by rfl) ⟨3533543, by rfl⟩ : syracuseStep 4711391 = 7067087) B7067087
theorem B196043773 : Blo 976593 196043773 := bstep (se 3 (by rfl) ⟨36758207, by rfl⟩ : syracuseStep 196043773 = 73516415) B73516415
theorem B3302639 : Blo 976593 3302639 := bstep (se 1 (by rfl) ⟨2476979, by rfl⟩ : syracuseStep 3302639 = 4953959) B4953959
theorem B23783489 : Blo 976593 23783489 := bstep (se 2 (by rfl) ⟨8918808, by rfl⟩ : syracuseStep 23783489 = 17837617) B17837617
theorem B3532967 : Blo 976593 3532967 := bstep (se 1 (by rfl) ⟨2649725, by rfl⟩ : syracuseStep 3532967 = 5299451) B5299451
theorem B977135 : Blo 976593 977135 := bstep (se 1 (by rfl) ⟨732851, by rfl⟩ : syracuseStep 977135 = 1465703) B1465703
theorem B1469531 : Blo 976593 1469531 := bstep (se 1 (by rfl) ⟨1102148, by rfl⟩ : syracuseStep 1469531 = 2204297) B2204297
theorem B978239 : Blo 976593 978239 := bstep (se 1 (by rfl) ⟨733679, by rfl⟩ : syracuseStep 978239 = 1467359) B1467359
theorem B978799 : Blo 976593 978799 := bstep (se 1 (by rfl) ⟨734099, by rfl⟩ : syracuseStep 978799 = 1468199) B1468199
theorem B979935 : Blo 976593 979935 := bstep (se 1 (by rfl) ⟨734951, by rfl⟩ : syracuseStep 979935 = 1469903) B1469903
theorem B979999 : Blo 976593 979999 := bstep (se 1 (by rfl) ⟨734999, by rfl⟩ : syracuseStep 979999 = 1469999) B1469999
theorem B980159 : Blo 976593 980159 := bstep (se 1 (by rfl) ⟨735119, by rfl⟩ : syracuseStep 980159 = 1470239) B1470239
theorem B980415 : Blo 976593 980415 := bstep (se 1 (by rfl) ⟨735311, by rfl⟩ : syracuseStep 980415 = 1470623) B1470623
theorem B85752989 : Blo 976593 85752989 := bstep (se 3 (by rfl) ⟨16078685, by rfl⟩ : syracuseStep 85752989 = 32157371) B32157371
theorem B14090111 : Blo 976593 14090111 := bstep (se 1 (by rfl) ⟨10567583, by rfl⟩ : syracuseStep 14090111 = 21135167) B21135167
theorem B28181135 : Blo 976593 28181135 := bstep (se 1 (by rfl) ⟨21135851, by rfl⟩ : syracuseStep 28181135 = 42271703) B42271703
theorem B7144519 : Blo 976593 7144519 := bstep (se 1 (by rfl) ⟨5358389, by rfl⟩ : syracuseStep 7144519 = 10716779) B10716779
theorem B261391697 : Blo 976593 261391697 := bstep (se 2 (by rfl) ⟨98021886, by rfl⟩ : syracuseStep 261391697 = 196043773) B196043773
theorem B4950071 : Blo 976593 4950071 := bstep (se 1 (by rfl) ⟨3712553, by rfl⟩ : syracuseStep 4950071 = 7425107) B7425107
theorem B12552833 : Blo 976593 12552833 := bstep (se 2 (by rfl) ⟨4707312, by rfl⟩ : syracuseStep 12552833 = 9414625) B9414625
theorem B7049207 : Blo 976593 7049207 := bstep (se 1 (by rfl) ⟨5286905, by rfl⟩ : syracuseStep 7049207 = 10573811) B10573811
theorem B17829881 : Blo 976593 17829881 := bstep (se 2 (by rfl) ⟨6686205, by rfl⟩ : syracuseStep 17829881 = 13372411) B13372411
theorem B2200841 : Blo 976593 2200841 := bstep (se 2 (by rfl) ⟨825315, by rfl⟩ : syracuseStep 2200841 = 1650631) B1650631
theorem B5019131 : Blo 976593 5019131 := bstep (se 1 (by rfl) ⟨3764348, by rfl⟩ : syracuseStep 5019131 = 7528697) B7528697
theorem B2201759 : Blo 976593 2201759 := bstep (se 1 (by rfl) ⟨1651319, by rfl⟩ : syracuseStep 2201759 = 3302639) B3302639
theorem B5578217 : Blo 976593 5578217 := bstep (se 2 (by rfl) ⟨2091831, by rfl⟩ : syracuseStep 5578217 = 4183663) B4183663
theorem B5579401 : Blo 976593 5579401 := bstep (se 2 (by rfl) ⟨2092275, by rfl⟩ : syracuseStep 5579401 = 4184551) B4184551
theorem B2204585 : Blo 976593 2204585 := bstep (se 2 (by rfl) ⟨826719, by rfl⟩ : syracuseStep 2204585 = 1653439) B1653439
theorem B4958657 : Blo 976593 4958657 := bstep (se 2 (by rfl) ⟨1859496, by rfl⟩ : syracuseStep 4958657 = 3718993) B3718993
theorem B5581817 : Blo 976593 5581817 := bstep (se 2 (by rfl) ⟨2093181, by rfl⟩ : syracuseStep 5581817 = 4186363) B4186363
theorem B23833885 : Blo 976593 23833885 := bstep (se 3 (by rfl) ⟨4468853, by rfl⟩ : syracuseStep 23833885 = 8937707) B8937707
theorem B5582591 : Blo 976593 5582591 := bstep (se 1 (by rfl) ⟨4186943, by rfl⟩ : syracuseStep 5582591 = 8373887) B8373887
theorem B20100649 : Blo 976593 20100649 := bstep (se 2 (by rfl) ⟨7537743, by rfl⟩ : syracuseStep 20100649 = 15075487) B15075487
theorem B20362913 : Blo 976593 20362913 := bstep (se 2 (by rfl) ⟨7636092, by rfl⟩ : syracuseStep 20362913 = 15272185) B15272185
theorem B3522473 : Blo 976593 3522473 := bstep (se 2 (by rfl) ⟨1320927, by rfl⟩ : syracuseStep 3522473 = 2641855) B2641855
theorem B2642233 : Blo 976593 2642233 := bstep (se 2 (by rfl) ⟨990837, by rfl⟩ : syracuseStep 2642233 = 1981675) B1981675
theorem B57168659 : Blo 976593 57168659 := bstep (se 1 (by rfl) ⟨42876494, by rfl⟩ : syracuseStep 57168659 = 85752989) B85752989
theorem B9393407 : Blo 976593 9393407 := bstep (se 1 (by rfl) ⟨7045055, by rfl⟩ : syracuseStep 9393407 = 14090111) B14090111
theorem B4184399 : Blo 976593 4184399 := bstep (se 1 (by rfl) ⟨3138299, by rfl⟩ : syracuseStep 4184399 = 6276599) B6276599
theorem B3300479 : Blo 976593 3300479 := bstep (se 1 (by rfl) ⟨2475359, by rfl⟩ : syracuseStep 3300479 = 4950719) B4950719
theorem B1236379 : Blo 976593 1236379 := bstep (se 1 (by rfl) ⟨927284, by rfl⟩ : syracuseStep 1236379 = 1854569) B1854569
theorem B1465835 : Blo 976593 1465835 := bstep (se 1 (by rfl) ⟨1099376, by rfl⟩ : syracuseStep 1465835 = 2198753) B2198753
theorem B56450843 : Blo 976593 56450843 := bstep (se 1 (by rfl) ⟨42338132, by rfl⟩ : syracuseStep 56450843 = 84676265) B84676265
theorem B1466303 : Blo 976593 1466303 := bstep (se 1 (by rfl) ⟨1099727, by rfl⟩ : syracuseStep 1466303 = 2199455) B2199455
theorem B3301505 : Blo 976593 3301505 := bstep (se 2 (by rfl) ⟨1238064, by rfl⟩ : syracuseStep 3301505 = 2476129) B2476129
theorem B1466537 : Blo 976593 1466537 := bstep (se 2 (by rfl) ⟨549951, by rfl⟩ : syracuseStep 1466537 = 1099903) B1099903
theorem B1466591 : Blo 976593 1466591 := bstep (se 1 (by rfl) ⟨1099943, by rfl⟩ : syracuseStep 1466591 = 2199887) B2199887
theorem B5562863 : Blo 976593 5562863 := bstep (se 1 (by rfl) ⟨4172147, by rfl⟩ : syracuseStep 5562863 = 8344295) B8344295
theorem B1467035 : Blo 976593 1467035 := bstep (se 1 (by rfl) ⟨1100276, by rfl⟩ : syracuseStep 1467035 = 2200553) B2200553
theorem B1467419 : Blo 976593 1467419 := bstep (se 1 (by rfl) ⟨1100564, by rfl⟩ : syracuseStep 1467419 = 2201129) B2201129
theorem B163046515 : Blo 976593 163046515 := bstep (se 1 (by rfl) ⟨122284886, by rfl⟩ : syracuseStep 163046515 = 244569773) B244569773
theorem B1238267 : Blo 976593 1238267 := bstep (se 1 (by rfl) ⟨928700, by rfl⟩ : syracuseStep 1238267 = 1857401) B1857401
theorem B1467647 : Blo 976593 1467647 := bstep (se 1 (by rfl) ⟨1100735, by rfl⟩ : syracuseStep 1467647 = 2201471) B2201471
theorem B3302747 : Blo 976593 3302747 := bstep (se 1 (by rfl) ⟨2477060, by rfl⟩ : syracuseStep 3302747 = 4954121) B4954121
theorem B1467815 : Blo 976593 1467815 := bstep (se 1 (by rfl) ⟨1100861, by rfl⟩ : syracuseStep 1467815 = 2201723) B2201723
theorem B55043819 : Blo 976593 55043819 := bstep (se 1 (by rfl) ⟨41282864, by rfl⟩ : syracuseStep 55043819 = 82565729) B82565729
theorem B1468187 : Blo 976593 1468187 := bstep (se 1 (by rfl) ⟨1101140, by rfl⟩ : syracuseStep 1468187 = 2202281) B2202281
theorem B976895 : Blo 976593 976895 := bstep (se 1 (by rfl) ⟨732671, by rfl⟩ : syracuseStep 976895 = 1465343) B1465343
theorem B1468487 : Blo 976593 1468487 := bstep (se 1 (by rfl) ⟨1101365, by rfl⟩ : syracuseStep 1468487 = 2202731) B2202731
theorem B1468655 : Blo 976593 1468655 := bstep (se 1 (by rfl) ⟨1101491, by rfl⟩ : syracuseStep 1468655 = 2202983) B2202983
theorem B977255 : Blo 976593 977255 := bstep (se 1 (by rfl) ⟨732941, by rfl⟩ : syracuseStep 977255 = 1465883) B1465883
theorem B1469147 : Blo 976593 1469147 := bstep (se 1 (by rfl) ⟨1101860, by rfl⟩ : syracuseStep 1469147 = 2203721) B2203721
theorem B11136203 : Blo 976593 11136203 := bstep (se 1 (by rfl) ⟨8352152, by rfl⟩ : syracuseStep 11136203 = 16704305) B16704305
theorem B3140927 : Blo 976593 3140927 := bstep (se 1 (by rfl) ⟨2355695, by rfl⟩ : syracuseStep 3140927 = 4711391) B4711391
theorem B15855659 : Blo 976593 15855659 := bstep (se 1 (by rfl) ⟨11891744, by rfl⟩ : syracuseStep 15855659 = 23783489) B23783489
theorem B2355311 : Blo 976593 2355311 := bstep (se 1 (by rfl) ⟨1766483, by rfl⟩ : syracuseStep 2355311 = 3532967) B3532967
theorem B3306203 : Blo 976593 3306203 := bstep (se 1 (by rfl) ⟨2479652, by rfl⟩ : syracuseStep 3306203 = 4959305) B4959305
theorem B979687 : Blo 976593 979687 := bstep (se 1 (by rfl) ⟨734765, by rfl⟩ : syracuseStep 979687 = 1469531) B1469531
theorem B3306959 : Blo 976593 3306959 := bstep (se 1 (by rfl) ⟨2480219, by rfl⟩ : syracuseStep 3306959 = 4960439) B4960439
theorem B12547709 : Blo 976593 12547709 := bstep (se 3 (by rfl) ⟨2352695, by rfl⟩ : syracuseStep 12547709 = 4705391) B4705391
theorem B2784041 : Blo 976593 2784041 := bstep (se 2 (by rfl) ⟨1044015, by rfl⟩ : syracuseStep 2784041 = 2088031) B2088031
theorem B7439201 : Blo 976593 7439201 := bstep (se 2 (by rfl) ⟨2789700, by rfl⟩ : syracuseStep 7439201 = 5579401) B5579401
theorem B174261131 : Blo 976593 174261131 := bstep (se 1 (by rfl) ⟨130695848, by rfl⟩ : syracuseStep 174261131 = 261391697) B261391697
theorem B38112439 : Blo 976593 38112439 := bstep (se 1 (by rfl) ⟨28584329, by rfl⟩ : syracuseStep 38112439 = 57168659) B57168659
theorem B6262271 : Blo 976593 6262271 := bstep (se 1 (by rfl) ⟨4696703, by rfl⟩ : syracuseStep 6262271 = 9393407) B9393407
theorem B2789599 : Blo 976593 2789599 := bstep (se 1 (by rfl) ⟨2092199, by rfl⟩ : syracuseStep 2789599 = 4184399) B4184399
theorem B2200319 : Blo 976593 2200319 := bstep (se 1 (by rfl) ⟨1650239, by rfl⟩ : syracuseStep 2200319 = 3300479) B3300479
theorem B2201003 : Blo 976593 2201003 := bstep (se 1 (by rfl) ⟨1650752, by rfl⟩ : syracuseStep 2201003 = 3301505) B3301505
theorem B3708575 : Blo 976593 3708575 := bstep (se 1 (by rfl) ⟨2781431, by rfl⟩ : syracuseStep 3708575 = 5562863) B5562863
theorem B2201831 : Blo 976593 2201831 := bstep (se 1 (by rfl) ⟨1651373, by rfl⟩ : syracuseStep 2201831 = 3302747) B3302747
theorem B2204135 : Blo 976593 2204135 := bstep (se 1 (by rfl) ⟨1653101, by rfl⟩ : syracuseStep 2204135 = 3306203) B3306203
theorem B2204639 : Blo 976593 2204639 := bstep (se 1 (by rfl) ⟨1653479, by rfl⟩ : syracuseStep 2204639 = 3306959) B3306959
theorem B8365139 : Blo 976593 8365139 := bstep (se 1 (by rfl) ⟨6273854, by rfl⟩ : syracuseStep 8365139 = 12547709) B12547709
theorem B13575275 : Blo 976593 13575275 := bstep (se 1 (by rfl) ⟨10181456, by rfl⟩ : syracuseStep 13575275 = 20362913) B20362913
theorem B1648505 : Blo 976593 1648505 := bstep (se 2 (by rfl) ⟨618189, by rfl⟩ : syracuseStep 1648505 = 1236379) B1236379
theorem B18787423 : Blo 976593 18787423 := bstep (se 1 (by rfl) ⟨14090567, by rfl⟩ : syracuseStep 18787423 = 28181135) B28181135
theorem B217395353 : Blo 976593 217395353 := bstep (se 2 (by rfl) ⟨81523257, by rfl⟩ : syracuseStep 217395353 = 163046515) B163046515
theorem B8368555 : Blo 976593 8368555 := bstep (se 1 (by rfl) ⟨6276416, by rfl⟩ : syracuseStep 8368555 = 12552833) B12552833
theorem B4699471 : Blo 976593 4699471 := bstep (se 1 (by rfl) ⟨3524603, by rfl⟩ : syracuseStep 4699471 = 7049207) B7049207
theorem B13384349 : Blo 976593 13384349 := bstep (se 3 (by rfl) ⟨2509565, by rfl⟩ : syracuseStep 13384349 = 5019131) B5019131
theorem B3718811 : Blo 976593 3718811 := bstep (se 1 (by rfl) ⟨2789108, by rfl⟩ : syracuseStep 3718811 = 5578217) B5578217
theorem B37633895 : Blo 976593 37633895 := bstep (se 1 (by rfl) ⟨28225421, by rfl⟩ : syracuseStep 37633895 = 56450843) B56450843
theorem B3522977 : Blo 976593 3522977 := bstep (se 2 (by rfl) ⟨1321116, by rfl⟩ : syracuseStep 3522977 = 2642233) B2642233
theorem B3721211 : Blo 976593 3721211 := bstep (se 1 (by rfl) ⟨2790908, by rfl⟩ : syracuseStep 3721211 = 5581817) B5581817
theorem B7424135 : Blo 976593 7424135 := bstep (se 1 (by rfl) ⟨5568101, by rfl⟩ : syracuseStep 7424135 = 11136203) B11136203
theorem B3721727 : Blo 976593 3721727 := bstep (se 1 (by rfl) ⟨2791295, by rfl⟩ : syracuseStep 3721727 = 5582591) B5582591
theorem B10570439 : Blo 976593 10570439 := bstep (se 1 (by rfl) ⟨7927829, by rfl⟩ : syracuseStep 10570439 = 15855659) B15855659
theorem B1856027 : Blo 976593 1856027 := bstep (se 1 (by rfl) ⟨1392020, by rfl⟩ : syracuseStep 1856027 = 2784041) B2784041
theorem B2348315 : Blo 976593 2348315 := bstep (se 1 (by rfl) ⟨1761236, by rfl⟩ : syracuseStep 2348315 = 3522473) B3522473
theorem B3300047 : Blo 976593 3300047 := bstep (se 1 (by rfl) ⟨2475035, by rfl⟩ : syracuseStep 3300047 = 4950071) B4950071
theorem B9526025 : Blo 976593 9526025 := bstep (se 2 (by rfl) ⟨3572259, by rfl⟩ : syracuseStep 9526025 = 7144519) B7144519
theorem B11886587 : Blo 976593 11886587 := bstep (se 1 (by rfl) ⟨8914940, by rfl⟩ : syracuseStep 11886587 = 17829881) B17829881
theorem B3302045 : Blo 976593 3302045 := bstep (se 3 (by rfl) ⟨619133, by rfl⟩ : syracuseStep 3302045 = 1238267) B1238267
theorem B1467227 : Blo 976593 1467227 := bstep (se 1 (by rfl) ⟨1100420, by rfl⟩ : syracuseStep 1467227 = 2200841) B2200841
theorem B1467839 : Blo 976593 1467839 := bstep (se 1 (by rfl) ⟨1100879, by rfl⟩ : syracuseStep 1467839 = 2201759) B2201759
theorem B31778513 : Blo 976593 31778513 := bstep (se 2 (by rfl) ⟨11916942, by rfl⟩ : syracuseStep 31778513 = 23833885) B23833885
theorem B977223 : Blo 976593 977223 := bstep (se 1 (by rfl) ⟨732917, by rfl⟩ : syracuseStep 977223 = 1465835) B1465835
theorem B977535 : Blo 976593 977535 := bstep (se 1 (by rfl) ⟨733151, by rfl⟩ : syracuseStep 977535 = 1466303) B1466303
theorem B977691 : Blo 976593 977691 := bstep (se 1 (by rfl) ⟨733268, by rfl⟩ : syracuseStep 977691 = 1466537) B1466537
theorem B977727 : Blo 976593 977727 := bstep (se 1 (by rfl) ⟨733295, by rfl⟩ : syracuseStep 977727 = 1466591) B1466591
theorem B978023 : Blo 976593 978023 := bstep (se 1 (by rfl) ⟨733517, by rfl⟩ : syracuseStep 978023 = 1467035) B1467035
theorem B1469723 : Blo 976593 1469723 := bstep (se 1 (by rfl) ⟨1102292, by rfl⟩ : syracuseStep 1469723 = 2204585) B2204585
theorem B978279 : Blo 976593 978279 := bstep (se 1 (by rfl) ⟨733709, by rfl⟩ : syracuseStep 978279 = 1467419) B1467419
theorem B978431 : Blo 976593 978431 := bstep (se 1 (by rfl) ⟨733823, by rfl⟩ : syracuseStep 978431 = 1467647) B1467647
theorem B978543 : Blo 976593 978543 := bstep (se 1 (by rfl) ⟨733907, by rfl⟩ : syracuseStep 978543 = 1467815) B1467815
theorem B36695879 : Blo 976593 36695879 := bstep (se 1 (by rfl) ⟨27521909, by rfl⟩ : syracuseStep 36695879 = 55043819) B55043819
theorem B978791 : Blo 976593 978791 := bstep (se 1 (by rfl) ⟨734093, by rfl⟩ : syracuseStep 978791 = 1468187) B1468187
theorem B978991 : Blo 976593 978991 := bstep (se 1 (by rfl) ⟨734243, by rfl⟩ : syracuseStep 978991 = 1468487) B1468487
theorem B979103 : Blo 976593 979103 := bstep (se 1 (by rfl) ⟨734327, by rfl⟩ : syracuseStep 979103 = 1468655) B1468655
theorem B3305771 : Blo 976593 3305771 := bstep (se 1 (by rfl) ⟨2479328, by rfl⟩ : syracuseStep 3305771 = 4958657) B4958657
theorem B979431 : Blo 976593 979431 := bstep (se 1 (by rfl) ⟨734573, by rfl⟩ : syracuseStep 979431 = 1469147) B1469147
theorem B26800865 : Blo 976593 26800865 := bstep (se 2 (by rfl) ⟨10050324, by rfl⟩ : syracuseStep 26800865 = 20100649) B20100649
theorem B2093951 : Blo 976593 2093951 := bstep (se 1 (by rfl) ⟨1570463, by rfl⟩ : syracuseStep 2093951 = 3140927) B3140927
theorem B1570207 : Blo 976593 1570207 := bstep (se 1 (by rfl) ⟨1177655, by rfl⟩ : syracuseStep 1570207 = 2355311) B2355311
theorem B4949423 : Blo 976593 4949423 := bstep (se 1 (by rfl) ⟨3712067, by rfl⟩ : syracuseStep 4949423 = 7424135) B7424135
theorem B7046959 : Blo 976593 7046959 := bstep (se 1 (by rfl) ⟨5285219, by rfl⟩ : syracuseStep 7046959 = 10570439) B10570439
theorem B2200031 : Blo 976593 2200031 := bstep (se 1 (by rfl) ⟨1650023, by rfl⟩ : syracuseStep 2200031 = 3300047) B3300047
theorem B2201363 : Blo 976593 2201363 := bstep (se 1 (by rfl) ⟨1651022, by rfl⟩ : syracuseStep 2201363 = 3302045) B3302045
theorem B5576759 : Blo 976593 5576759 := bstep (se 1 (by rfl) ⟨4182569, by rfl⟩ : syracuseStep 5576759 = 8365139) B8365139
theorem B9050183 : Blo 976593 9050183 := bstep (se 1 (by rfl) ⟨6787637, by rfl⟩ : syracuseStep 9050183 = 13575275) B13575275
theorem B6265961 : Blo 976593 6265961 := bstep (se 2 (by rfl) ⟨2349735, by rfl⟩ : syracuseStep 6265961 = 4699471) B4699471
theorem B2203847 : Blo 976593 2203847 := bstep (se 1 (by rfl) ⟨1652885, by rfl⟩ : syracuseStep 2203847 = 3305771) B3305771
theorem B17867243 : Blo 976593 17867243 := bstep (se 1 (by rfl) ⟨13400432, by rfl⟩ : syracuseStep 17867243 = 26800865) B26800865
theorem B8922899 : Blo 976593 8922899 := bstep (se 1 (by rfl) ⟨6692174, by rfl⟩ : syracuseStep 8922899 = 13384349) B13384349
theorem B4959467 : Blo 976593 4959467 := bstep (se 1 (by rfl) ⟨3719600, by rfl⟩ : syracuseStep 4959467 = 7439201) B7439201
theorem B116174087 : Blo 976593 116174087 := bstep (se 1 (by rfl) ⟨87130565, by rfl⟩ : syracuseStep 116174087 = 174261131) B174261131
theorem B4174847 : Blo 976593 4174847 := bstep (se 1 (by rfl) ⟨3131135, by rfl⟩ : syracuseStep 4174847 = 6262271) B6262271
theorem B2472383 : Blo 976593 2472383 := bstep (se 1 (by rfl) ⟨1854287, by rfl⟩ : syracuseStep 2472383 = 3708575) B3708575
theorem B25049897 : Blo 976593 25049897 := bstep (se 2 (by rfl) ⟨9393711, by rfl⟩ : syracuseStep 25049897 = 18787423) B18787423
theorem B3719465 : Blo 976593 3719465 := bstep (se 2 (by rfl) ⟨1394799, by rfl⟩ : syracuseStep 3719465 = 2789599) B2789599
theorem B11158073 : Blo 976593 11158073 := bstep (se 2 (by rfl) ⟨4184277, by rfl⟩ : syracuseStep 11158073 = 8368555) B8368555
theorem B21185675 : Blo 976593 21185675 := bstep (se 1 (by rfl) ⟨15889256, by rfl⟩ : syracuseStep 21185675 = 31778513) B31778513
theorem B1099003 : Blo 976593 1099003 := bstep (se 1 (by rfl) ⟨824252, by rfl⟩ : syracuseStep 1099003 = 1648505) B1648505
theorem B24463919 : Blo 976593 24463919 := bstep (se 1 (by rfl) ⟨18347939, by rfl⟩ : syracuseStep 24463919 = 36695879) B36695879
theorem B1395967 : Blo 976593 1395967 := bstep (se 1 (by rfl) ⟨1046975, by rfl⟩ : syracuseStep 1395967 = 2093951) B2093951
theorem B2479207 : Blo 976593 2479207 := bstep (se 1 (by rfl) ⟨1859405, by rfl⟩ : syracuseStep 2479207 = 3718811) B3718811
theorem B25089263 : Blo 976593 25089263 := bstep (se 1 (by rfl) ⟨18816947, by rfl⟩ : syracuseStep 25089263 = 37633895) B37633895
theorem B2348651 : Blo 976593 2348651 := bstep (se 1 (by rfl) ⟨1761488, by rfl⟩ : syracuseStep 2348651 = 3522977) B3522977
theorem B2480807 : Blo 976593 2480807 := bstep (se 1 (by rfl) ⟨1860605, by rfl⟩ : syracuseStep 2480807 = 3721211) B3721211
theorem B2481151 : Blo 976593 2481151 := bstep (se 1 (by rfl) ⟨1860863, by rfl⟩ : syracuseStep 2481151 = 3721727) B3721727
theorem B1237351 : Blo 976593 1237351 := bstep (se 1 (by rfl) ⟨928013, by rfl⟩ : syracuseStep 1237351 = 1856027) B1856027
theorem B1466879 : Blo 976593 1466879 := bstep (se 1 (by rfl) ⟨1100159, by rfl⟩ : syracuseStep 1466879 = 2200319) B2200319
theorem B1565543 : Blo 976593 1565543 := bstep (se 1 (by rfl) ⟨1174157, by rfl⟩ : syracuseStep 1565543 = 2348315) B2348315
theorem B1467335 : Blo 976593 1467335 := bstep (se 1 (by rfl) ⟨1100501, by rfl⟩ : syracuseStep 1467335 = 2201003) B2201003
theorem B1467887 : Blo 976593 1467887 := bstep (se 1 (by rfl) ⟨1100915, by rfl⟩ : syracuseStep 1467887 = 2201831) B2201831
theorem B50816585 : Blo 976593 50816585 := bstep (se 2 (by rfl) ⟨19056219, by rfl⟩ : syracuseStep 50816585 = 38112439) B38112439
theorem B6350683 : Blo 976593 6350683 := bstep (se 1 (by rfl) ⟨4763012, by rfl⟩ : syracuseStep 6350683 = 9526025) B9526025
theorem B7924391 : Blo 976593 7924391 := bstep (se 1 (by rfl) ⟨5943293, by rfl⟩ : syracuseStep 7924391 = 11886587) B11886587
theorem B1469423 : Blo 976593 1469423 := bstep (se 1 (by rfl) ⟨1102067, by rfl⟩ : syracuseStep 1469423 = 2204135) B2204135
theorem B978151 : Blo 976593 978151 := bstep (se 1 (by rfl) ⟨733613, by rfl⟩ : syracuseStep 978151 = 1467227) B1467227
theorem B1469759 : Blo 976593 1469759 := bstep (se 1 (by rfl) ⟨1102319, by rfl⟩ : syracuseStep 1469759 = 2204639) B2204639
theorem B978559 : Blo 976593 978559 := bstep (se 1 (by rfl) ⟨733919, by rfl⟩ : syracuseStep 978559 = 1467839) B1467839
theorem B2093609 : Blo 976593 2093609 := bstep (se 2 (by rfl) ⟨785103, by rfl⟩ : syracuseStep 2093609 = 1570207) B1570207
theorem B979815 : Blo 976593 979815 := bstep (se 1 (by rfl) ⟨734861, by rfl⟩ : syracuseStep 979815 = 1469723) B1469723
theorem B144930235 : Blo 976593 144930235 := bstep (se 1 (by rfl) ⟨108697676, by rfl⟩ : syracuseStep 144930235 = 217395353) B217395353
theorem B7438715 : Blo 976593 7438715 := bstep (se 1 (by rfl) ⟨5579036, by rfl⟩ : syracuseStep 7438715 = 11158073) B11158073
theorem B14123783 : Blo 976593 14123783 := bstep (se 1 (by rfl) ⟨10592837, by rfl⟩ : syracuseStep 14123783 = 21185675) B21185675
theorem B47645981 : Blo 976593 47645981 := bstep (se 3 (by rfl) ⟨8933621, by rfl⟩ : syracuseStep 47645981 = 17867243) B17867243
theorem B6033455 : Blo 976593 6033455 := bstep (se 1 (by rfl) ⟨4525091, by rfl⟩ : syracuseStep 6033455 = 9050183) B9050183
theorem B5282927 : Blo 976593 5282927 := bstep (se 1 (by rfl) ⟨3962195, by rfl⟩ : syracuseStep 5282927 = 7924391) B7924391
theorem B193240313 : Blo 976593 193240313 := bstep (se 2 (by rfl) ⟨72465117, by rfl⟩ : syracuseStep 193240313 = 144930235) B144930235
theorem B1648255 : Blo 976593 1648255 := bstep (se 1 (by rfl) ⟨1236191, by rfl⟩ : syracuseStep 1648255 = 2472383) B2472383
theorem B1649801 : Blo 976593 1649801 := bstep (se 2 (by rfl) ⟨618675, by rfl⟩ : syracuseStep 1649801 = 1237351) B1237351
theorem B8467577 : Blo 976593 8467577 := bstep (se 2 (by rfl) ⟨3175341, by rfl⟩ : syracuseStep 8467577 = 6350683) B6350683
theorem B16726175 : Blo 976593 16726175 := bstep (se 1 (by rfl) ⟨12544631, by rfl⟩ : syracuseStep 16726175 = 25089263) B25089263
theorem B3717839 : Blo 976593 3717839 := bstep (se 1 (by rfl) ⟨2788379, by rfl⟩ : syracuseStep 3717839 = 5576759) B5576759
theorem B135510893 : Blo 976593 135510893 := bstep (se 3 (by rfl) ⟨25408292, by rfl⟩ : syracuseStep 135510893 = 50816585) B50816585
theorem B1653871 : Blo 976593 1653871 := bstep (se 1 (by rfl) ⟨1240403, by rfl⟩ : syracuseStep 1653871 = 2480807) B2480807
theorem B4177307 : Blo 976593 4177307 := bstep (se 1 (by rfl) ⟨3132980, by rfl⟩ : syracuseStep 4177307 = 6265961) B6265961
theorem B5948599 : Blo 976593 5948599 := bstep (se 1 (by rfl) ⟨4461449, by rfl⟩ : syracuseStep 5948599 = 8922899) B8922899
theorem B77449391 : Blo 976593 77449391 := bstep (se 1 (by rfl) ⟨58087043, by rfl⟩ : syracuseStep 77449391 = 116174087) B116174087
theorem B1395739 : Blo 976593 1395739 := bstep (se 1 (by rfl) ⟨1046804, by rfl⟩ : syracuseStep 1395739 = 2093609) B2093609
theorem B16699931 : Blo 976593 16699931 := bstep (se 1 (by rfl) ⟨12524948, by rfl⟩ : syracuseStep 16699931 = 25049897) B25049897
theorem B2479643 : Blo 976593 2479643 := bstep (se 1 (by rfl) ⟨1859732, by rfl⟩ : syracuseStep 2479643 = 3719465) B3719465
theorem B3299615 : Blo 976593 3299615 := bstep (se 1 (by rfl) ⟨2474711, by rfl⟩ : syracuseStep 3299615 = 4949423) B4949423
theorem B1465337 : Blo 976593 1465337 := bstep (se 2 (by rfl) ⟨549501, by rfl⟩ : syracuseStep 1465337 = 1099003) B1099003
theorem B16309279 : Blo 976593 16309279 := bstep (se 1 (by rfl) ⟨12231959, by rfl⟩ : syracuseStep 16309279 = 24463919) B24463919
theorem B9395945 : Blo 976593 9395945 := bstep (se 2 (by rfl) ⟨3523479, by rfl⟩ : syracuseStep 9395945 = 7046959) B7046959
theorem B1466687 : Blo 976593 1466687 := bstep (se 1 (by rfl) ⟨1100015, by rfl⟩ : syracuseStep 1466687 = 2200031) B2200031
theorem B1565767 : Blo 976593 1565767 := bstep (se 1 (by rfl) ⟨1174325, by rfl⟩ : syracuseStep 1565767 = 2348651) B2348651
theorem B1467575 : Blo 976593 1467575 := bstep (se 1 (by rfl) ⟨1100681, by rfl⟩ : syracuseStep 1467575 = 2201363) B2201363
theorem B1861289 : Blo 976593 1861289 := bstep (se 2 (by rfl) ⟨697983, by rfl⟩ : syracuseStep 1861289 = 1395967) B1395967
theorem B1469231 : Blo 976593 1469231 := bstep (se 1 (by rfl) ⟨1101923, by rfl⟩ : syracuseStep 1469231 = 2203847) B2203847
theorem B977919 : Blo 976593 977919 := bstep (se 1 (by rfl) ⟨733439, by rfl⟩ : syracuseStep 977919 = 1466879) B1466879
theorem B1043695 : Blo 976593 1043695 := bstep (se 1 (by rfl) ⟨782771, by rfl⟩ : syracuseStep 1043695 = 1565543) B1565543
theorem B978223 : Blo 976593 978223 := bstep (se 1 (by rfl) ⟨733667, by rfl⟩ : syracuseStep 978223 = 1467335) B1467335
theorem B978591 : Blo 976593 978591 := bstep (se 1 (by rfl) ⟨733943, by rfl⟩ : syracuseStep 978591 = 1467887) B1467887
theorem B3305609 : Blo 976593 3305609 := bstep (se 2 (by rfl) ⟨1239603, by rfl⟩ : syracuseStep 3305609 = 2479207) B2479207
theorem B979615 : Blo 976593 979615 := bstep (se 1 (by rfl) ⟨734711, by rfl⟩ : syracuseStep 979615 = 1469423) B1469423
theorem B3306311 : Blo 976593 3306311 := bstep (se 1 (by rfl) ⟨2479733, by rfl⟩ : syracuseStep 3306311 = 4959467) B4959467
theorem B979839 : Blo 976593 979839 := bstep (se 1 (by rfl) ⟨734879, by rfl⟩ : syracuseStep 979839 = 1469759) B1469759
theorem B2783231 : Blo 976593 2783231 := bstep (se 1 (by rfl) ⟨2087423, by rfl⟩ : syracuseStep 2783231 = 4174847) B4174847
theorem B3308201 : Blo 976593 3308201 := bstep (se 2 (by rfl) ⟨1240575, by rfl⟩ : syracuseStep 3308201 = 2481151) B2481151
theorem B7931465 : Blo 976593 7931465 := bstep (se 2 (by rfl) ⟨2974299, by rfl⟩ : syracuseStep 7931465 = 5948599) B5948599
theorem B2197673 : Blo 976593 2197673 := bstep (se 2 (by rfl) ⟨824127, by rfl⟩ : syracuseStep 2197673 = 1648255) B1648255
theorem B2199743 : Blo 976593 2199743 := bstep (se 1 (by rfl) ⟨1649807, by rfl⟩ : syracuseStep 2199743 = 3299615) B3299615
theorem B6263963 : Blo 976593 6263963 := bstep (se 1 (by rfl) ⟨4697972, by rfl⟩ : syracuseStep 6263963 = 9395945) B9395945
theorem B2203739 : Blo 976593 2203739 := bstep (se 1 (by rfl) ⟨1652804, by rfl⟩ : syracuseStep 2203739 = 3305609) B3305609
theorem B2204207 : Blo 976593 2204207 := bstep (se 1 (by rfl) ⟨1653155, by rfl⟩ : syracuseStep 2204207 = 3306311) B3306311
theorem B5645051 : Blo 976593 5645051 := bstep (se 1 (by rfl) ⟨4233788, by rfl⟩ : syracuseStep 5645051 = 8467577) B8467577
theorem B11150783 : Blo 976593 11150783 := bstep (se 1 (by rfl) ⟨8363087, by rfl⟩ : syracuseStep 11150783 = 16726175) B16726175
theorem B2205161 : Blo 976593 2205161 := bstep (se 2 (by rfl) ⟨826935, by rfl⟩ : syracuseStep 2205161 = 1653871) B1653871
theorem B2205467 : Blo 976593 2205467 := bstep (se 1 (by rfl) ⟨1654100, by rfl⟩ : syracuseStep 2205467 = 3308201) B3308201
theorem B4959143 : Blo 976593 4959143 := bstep (se 1 (by rfl) ⟨3719357, by rfl⟩ : syracuseStep 4959143 = 7438715) B7438715
theorem B9415855 : Blo 976593 9415855 := bstep (se 1 (by rfl) ⟨7061891, by rfl⟩ : syracuseStep 9415855 = 14123783) B14123783
theorem B31763987 : Blo 976593 31763987 := bstep (se 1 (by rfl) ⟨23822990, by rfl⟩ : syracuseStep 31763987 = 47645981) B47645981
theorem B1653095 : Blo 976593 1653095 := bstep (se 1 (by rfl) ⟨1239821, by rfl⟩ : syracuseStep 1653095 = 2479643) B2479643
theorem B1391593 : Blo 976593 1391593 := bstep (se 2 (by rfl) ⟨521847, by rfl⟩ : syracuseStep 1391593 = 1043695) B1043695
theorem B3521951 : Blo 976593 3521951 := bstep (se 1 (by rfl) ⟨2641463, by rfl⟩ : syracuseStep 3521951 = 5282927) B5282927
theorem B128826875 : Blo 976593 128826875 := bstep (se 1 (by rfl) ⟨96620156, by rfl⟩ : syracuseStep 128826875 = 193240313) B193240313
theorem B1099867 : Blo 976593 1099867 := bstep (se 1 (by rfl) ⟨824900, by rfl⟩ : syracuseStep 1099867 = 1649801) B1649801
theorem B1855487 : Blo 976593 1855487 := bstep (se 1 (by rfl) ⟨1391615, by rfl⟩ : syracuseStep 1855487 = 2783231) B2783231
theorem B21745705 : Blo 976593 21745705 := bstep (se 2 (by rfl) ⟨8154639, by rfl⟩ : syracuseStep 21745705 = 16309279) B16309279
theorem B2478559 : Blo 976593 2478559 := bstep (se 1 (by rfl) ⟨1858919, by rfl⟩ : syracuseStep 2478559 = 3717839) B3717839
theorem B2087689 : Blo 976593 2087689 := bstep (se 2 (by rfl) ⟨782883, by rfl⟩ : syracuseStep 2087689 = 1565767) B1565767
theorem B51632927 : Blo 976593 51632927 := bstep (se 1 (by rfl) ⟨38724695, by rfl⟩ : syracuseStep 51632927 = 77449391) B77449391
theorem B4022303 : Blo 976593 4022303 := bstep (se 1 (by rfl) ⟨3016727, by rfl⟩ : syracuseStep 4022303 = 6033455) B6033455
theorem B11133287 : Blo 976593 11133287 := bstep (se 1 (by rfl) ⟨8349965, by rfl⟩ : syracuseStep 11133287 = 16699931) B16699931
theorem B1860985 : Blo 976593 1860985 := bstep (se 2 (by rfl) ⟨697869, by rfl⟩ : syracuseStep 1860985 = 1395739) B1395739
theorem B976891 : Blo 976593 976891 := bstep (se 1 (by rfl) ⟨732668, by rfl⟩ : syracuseStep 976891 = 1465337) B1465337
theorem B977791 : Blo 976593 977791 := bstep (se 1 (by rfl) ⟨733343, by rfl⟩ : syracuseStep 977791 = 1466687) B1466687
theorem B978383 : Blo 976593 978383 := bstep (se 1 (by rfl) ⟨733787, by rfl⟩ : syracuseStep 978383 = 1467575) B1467575
theorem B1240859 : Blo 976593 1240859 := bstep (se 1 (by rfl) ⟨930644, by rfl⟩ : syracuseStep 1240859 = 1861289) B1861289
theorem B979487 : Blo 976593 979487 := bstep (se 1 (by rfl) ⟨734615, by rfl⟩ : syracuseStep 979487 = 1469231) B1469231
theorem B90340595 : Blo 976593 90340595 := bstep (se 1 (by rfl) ⟨67755446, by rfl⟩ : syracuseStep 90340595 = 135510893) B135510893
theorem B2784871 : Blo 976593 2784871 := bstep (se 1 (by rfl) ⟨2088653, by rfl⟩ : syracuseStep 2784871 = 4177307) B4177307
theorem B12554473 : Blo 976593 12554473 := bstep (se 2 (by rfl) ⟨4707927, by rfl⟩ : syracuseStep 12554473 = 9415855) B9415855
theorem B21175991 : Blo 976593 21175991 := bstep (se 1 (by rfl) ⟨15881993, by rfl⟩ : syracuseStep 21175991 = 31763987) B31763987
theorem B3713161 : Blo 976593 3713161 := bstep (se 2 (by rfl) ⟨1392435, by rfl⟩ : syracuseStep 3713161 = 2784871) B2784871
theorem B42904565 : Blo 976593 42904565 := bstep (se 5 (by rfl) ⟨2011151, by rfl⟩ : syracuseStep 42904565 = 4022303) B4022303
theorem B5287643 : Blo 976593 5287643 := bstep (se 1 (by rfl) ⟨3965732, by rfl⟩ : syracuseStep 5287643 = 7931465) B7931465
theorem B4175975 : Blo 976593 4175975 := bstep (se 1 (by rfl) ⟨3131981, by rfl⟩ : syracuseStep 4175975 = 6263963) B6263963
theorem B34421951 : Blo 976593 34421951 := bstep (se 1 (by rfl) ⟨25816463, by rfl⟩ : syracuseStep 34421951 = 51632927) B51632927
theorem B7422191 : Blo 976593 7422191 := bstep (se 1 (by rfl) ⟨5566643, by rfl⟩ : syracuseStep 7422191 = 11133287) B11133287
theorem B1855457 : Blo 976593 1855457 := bstep (se 2 (by rfl) ⟨695796, by rfl⟩ : syracuseStep 1855457 = 1391593) B1391593
theorem B1102063 : Blo 976593 1102063 := bstep (se 1 (by rfl) ⟨826547, by rfl⟩ : syracuseStep 1102063 = 1653095) B1653095
theorem B2347967 : Blo 976593 2347967 := bstep (se 1 (by rfl) ⟨1760975, by rfl⟩ : syracuseStep 2347967 = 3521951) B3521951
theorem B1465115 : Blo 976593 1465115 := bstep (se 1 (by rfl) ⟨1098836, by rfl⟩ : syracuseStep 1465115 = 2197673) B2197673
theorem B2481313 : Blo 976593 2481313 := bstep (se 2 (by rfl) ⟨930492, by rfl⟩ : syracuseStep 2481313 = 1860985) B1860985
theorem B1466489 : Blo 976593 1466489 := bstep (se 2 (by rfl) ⟨549933, by rfl⟩ : syracuseStep 1466489 = 1099867) B1099867
theorem B1466495 : Blo 976593 1466495 := bstep (se 1 (by rfl) ⟨1099871, by rfl⟩ : syracuseStep 1466495 = 2199743) B2199743
theorem B28994273 : Blo 976593 28994273 := bstep (se 2 (by rfl) ⟨10872852, by rfl⟩ : syracuseStep 28994273 = 21745705) B21745705
theorem B1469159 : Blo 976593 1469159 := bstep (se 1 (by rfl) ⟨1101869, by rfl⟩ : syracuseStep 1469159 = 2203739) B2203739
theorem B1469471 : Blo 976593 1469471 := bstep (se 1 (by rfl) ⟨1102103, by rfl⟩ : syracuseStep 1469471 = 2204207) B2204207
theorem B3763367 : Blo 976593 3763367 := bstep (se 1 (by rfl) ⟨2822525, by rfl⟩ : syracuseStep 3763367 = 5645051) B5645051
theorem B3304745 : Blo 976593 3304745 := bstep (se 2 (by rfl) ⟨1239279, by rfl⟩ : syracuseStep 3304745 = 2478559) B2478559
theorem B7433855 : Blo 976593 7433855 := bstep (se 1 (by rfl) ⟨5575391, by rfl⟩ : syracuseStep 7433855 = 11150783) B11150783
theorem B1470107 : Blo 976593 1470107 := bstep (se 1 (by rfl) ⟨1102580, by rfl⟩ : syracuseStep 1470107 = 2205161) B2205161
theorem B1470311 : Blo 976593 1470311 := bstep (se 1 (by rfl) ⟨1102733, by rfl⟩ : syracuseStep 1470311 = 2205467) B2205467
theorem B3306095 : Blo 976593 3306095 := bstep (se 1 (by rfl) ⟨2479571, by rfl⟩ : syracuseStep 3306095 = 4959143) B4959143
theorem B2783585 : Blo 976593 2783585 := bstep (se 2 (by rfl) ⟨1043844, by rfl⟩ : syracuseStep 2783585 = 2087689) B2087689
theorem B3308957 : Blo 976593 3308957 := bstep (se 3 (by rfl) ⟨620429, by rfl⟩ : syracuseStep 3308957 = 1240859) B1240859
theorem B60227063 : Blo 976593 60227063 := bstep (se 1 (by rfl) ⟨45170297, by rfl⟩ : syracuseStep 60227063 = 90340595) B90340595
theorem B85884583 : Blo 976593 85884583 := bstep (se 1 (by rfl) ⟨64413437, by rfl⟩ : syracuseStep 85884583 = 128826875) B128826875
theorem B4947965 : Blo 976593 4947965 := bstep (se 3 (by rfl) ⟨927743, by rfl⟩ : syracuseStep 4947965 = 1855487) B1855487
theorem B4948127 : Blo 976593 4948127 := bstep (se 1 (by rfl) ⟨3711095, by rfl⟩ : syracuseStep 4948127 = 7422191) B7422191
theorem B6261245 : Blo 976593 6261245 := bstep (se 3 (by rfl) ⟨1173983, by rfl⟩ : syracuseStep 6261245 = 2347967) B2347967
theorem B4950881 : Blo 976593 4950881 := bstep (se 2 (by rfl) ⟨1856580, by rfl⟩ : syracuseStep 4950881 = 3713161) B3713161
theorem B2203163 : Blo 976593 2203163 := bstep (se 1 (by rfl) ⟨1652372, by rfl⟩ : syracuseStep 2203163 = 3304745) B3304745
theorem B4955903 : Blo 976593 4955903 := bstep (se 1 (by rfl) ⟨3716927, by rfl⟩ : syracuseStep 4955903 = 7433855) B7433855
theorem B2204063 : Blo 976593 2204063 := bstep (se 1 (by rfl) ⟨1653047, by rfl⟩ : syracuseStep 2204063 = 3306095) B3306095
theorem B22947967 : Blo 976593 22947967 := bstep (se 1 (by rfl) ⟨17210975, by rfl⟩ : syracuseStep 22947967 = 34421951) B34421951
theorem B2205971 : Blo 976593 2205971 := bstep (se 1 (by rfl) ⟨1654478, by rfl⟩ : syracuseStep 2205971 = 3308957) B3308957
theorem B40151375 : Blo 976593 40151375 := bstep (se 1 (by rfl) ⟨30113531, by rfl⟩ : syracuseStep 40151375 = 60227063) B60227063
theorem B2508911 : Blo 976593 2508911 := bstep (se 1 (by rfl) ⟨1881683, by rfl⟩ : syracuseStep 2508911 = 3763367) B3763367
theorem B3525095 : Blo 976593 3525095 := bstep (se 1 (by rfl) ⟨2643821, by rfl⟩ : syracuseStep 3525095 = 5287643) B5287643
theorem B1855723 : Blo 976593 1855723 := bstep (se 1 (by rfl) ⟨1391792, by rfl⟩ : syracuseStep 1855723 = 2783585) B2783585
theorem B114512777 : Blo 976593 114512777 := bstep (se 2 (by rfl) ⟨42942291, by rfl⟩ : syracuseStep 114512777 = 85884583) B85884583
theorem B3298643 : Blo 976593 3298643 := bstep (se 1 (by rfl) ⟨2473982, by rfl⟩ : syracuseStep 3298643 = 4947965) B4947965
theorem B1236971 : Blo 976593 1236971 := bstep (se 1 (by rfl) ⟨927728, by rfl⟩ : syracuseStep 1236971 = 1855457) B1855457
theorem B976743 : Blo 976593 976743 := bstep (se 1 (by rfl) ⟨732557, by rfl⟩ : syracuseStep 976743 = 1465115) B1465115
theorem B14117327 : Blo 976593 14117327 := bstep (se 1 (by rfl) ⟨10587995, by rfl⟩ : syracuseStep 14117327 = 21175991) B21175991
theorem B977659 : Blo 976593 977659 := bstep (se 1 (by rfl) ⟨733244, by rfl⟩ : syracuseStep 977659 = 1466489) B1466489
theorem B977663 : Blo 976593 977663 := bstep (se 1 (by rfl) ⟨733247, by rfl⟩ : syracuseStep 977663 = 1466495) B1466495
theorem B16739297 : Blo 976593 16739297 := bstep (se 2 (by rfl) ⟨6277236, by rfl⟩ : syracuseStep 16739297 = 12554473) B12554473
theorem B1469417 : Blo 976593 1469417 := bstep (se 2 (by rfl) ⟨551031, by rfl⟩ : syracuseStep 1469417 = 1102063) B1102063
theorem B19329515 : Blo 976593 19329515 := bstep (se 1 (by rfl) ⟨14497136, by rfl⟩ : syracuseStep 19329515 = 28994273) B28994273
theorem B979439 : Blo 976593 979439 := bstep (se 1 (by rfl) ⟨734579, by rfl⟩ : syracuseStep 979439 = 1469159) B1469159
theorem B28603043 : Blo 976593 28603043 := bstep (se 1 (by rfl) ⟨21452282, by rfl⟩ : syracuseStep 28603043 = 42904565) B42904565
theorem B979647 : Blo 976593 979647 := bstep (se 1 (by rfl) ⟨734735, by rfl⟩ : syracuseStep 979647 = 1469471) B1469471
theorem B980071 : Blo 976593 980071 := bstep (se 1 (by rfl) ⟨735053, by rfl⟩ : syracuseStep 980071 = 1470107) B1470107
theorem B980207 : Blo 976593 980207 := bstep (se 1 (by rfl) ⟨735155, by rfl⟩ : syracuseStep 980207 = 1470311) B1470311
theorem B2783983 : Blo 976593 2783983 := bstep (se 1 (by rfl) ⟨2087987, by rfl⟩ : syracuseStep 2783983 = 4175975) B4175975
theorem B3308417 : Blo 976593 3308417 := bstep (se 2 (by rfl) ⟨1240656, by rfl⟩ : syracuseStep 3308417 = 2481313) B2481313
theorem B122389157 : Blo 976593 122389157 := bstep (se 4 (by rfl) ⟨11473983, by rfl⟩ : syracuseStep 122389157 = 22947967) B22947967
theorem B1672607 : Blo 976593 1672607 := bstep (se 1 (by rfl) ⟨1254455, by rfl⟩ : syracuseStep 1672607 = 2508911) B2508911
theorem B2199095 : Blo 976593 2199095 := bstep (se 1 (by rfl) ⟨1649321, by rfl⟩ : syracuseStep 2199095 = 3298643) B3298643
theorem B9411551 : Blo 976593 9411551 := bstep (se 1 (by rfl) ⟨7058663, by rfl⟩ : syracuseStep 9411551 = 14117327) B14117327
theorem B12886343 : Blo 976593 12886343 := bstep (se 1 (by rfl) ⟨9664757, by rfl⟩ : syracuseStep 12886343 = 19329515) B19329515
theorem B3711977 : Blo 976593 3711977 := bstep (se 2 (by rfl) ⟨1391991, by rfl⟩ : syracuseStep 3711977 = 2783983) B2783983
theorem B2205611 : Blo 976593 2205611 := bstep (se 1 (by rfl) ⟨1654208, by rfl⟩ : syracuseStep 2205611 = 3308417) B3308417
theorem B4174163 : Blo 976593 4174163 := bstep (se 1 (by rfl) ⟨3130622, by rfl⟩ : syracuseStep 4174163 = 6261245) B6261245
theorem B2474297 : Blo 976593 2474297 := bstep (se 2 (by rfl) ⟨927861, by rfl⟩ : syracuseStep 2474297 = 1855723) B1855723
theorem B11159531 : Blo 976593 11159531 := bstep (se 1 (by rfl) ⟨8369648, by rfl⟩ : syracuseStep 11159531 = 16739297) B16739297
theorem B3298589 : Blo 976593 3298589 := bstep (se 3 (by rfl) ⟨618485, by rfl⟩ : syracuseStep 3298589 = 1236971) B1236971
theorem B3298751 : Blo 976593 3298751 := bstep (se 1 (by rfl) ⟨2474063, by rfl⟩ : syracuseStep 3298751 = 4948127) B4948127
theorem B2350063 : Blo 976593 2350063 := bstep (se 1 (by rfl) ⟨1762547, by rfl⟩ : syracuseStep 2350063 = 3525095) B3525095
theorem B3300587 : Blo 976593 3300587 := bstep (se 1 (by rfl) ⟨2475440, by rfl⟩ : syracuseStep 3300587 = 4950881) B4950881
theorem B76341851 : Blo 976593 76341851 := bstep (se 1 (by rfl) ⟨57256388, by rfl⟩ : syracuseStep 76341851 = 114512777) B114512777
theorem B1468775 : Blo 976593 1468775 := bstep (se 1 (by rfl) ⟨1101581, by rfl⟩ : syracuseStep 1468775 = 2203163) B2203163
theorem B3303935 : Blo 976593 3303935 := bstep (se 1 (by rfl) ⟨2477951, by rfl⟩ : syracuseStep 3303935 = 4955903) B4955903
theorem B1469375 : Blo 976593 1469375 := bstep (se 1 (by rfl) ⟨1102031, by rfl⟩ : syracuseStep 1469375 = 2204063) B2204063
theorem B1470647 : Blo 976593 1470647 := bstep (se 1 (by rfl) ⟨1102985, by rfl⟩ : syracuseStep 1470647 = 2205971) B2205971
theorem B26767583 : Blo 976593 26767583 := bstep (se 1 (by rfl) ⟨20075687, by rfl⟩ : syracuseStep 26767583 = 40151375) B40151375
theorem B979611 : Blo 976593 979611 := bstep (se 1 (by rfl) ⟨734708, by rfl⟩ : syracuseStep 979611 = 1469417) B1469417
theorem B19068695 : Blo 976593 19068695 := bstep (se 1 (by rfl) ⟨14301521, by rfl⟩ : syracuseStep 19068695 = 28603043) B28603043
theorem B81592771 : Blo 976593 81592771 := bstep (se 1 (by rfl) ⟨61194578, by rfl⟩ : syracuseStep 81592771 = 122389157) B122389157
theorem B7439687 : Blo 976593 7439687 := bstep (se 1 (by rfl) ⟨5579765, by rfl⟩ : syracuseStep 7439687 = 11159531) B11159531
theorem B2199059 : Blo 976593 2199059 := bstep (se 1 (by rfl) ⟨1649294, by rfl⟩ : syracuseStep 2199059 = 3298589) B3298589
theorem B2199167 : Blo 976593 2199167 := bstep (se 1 (by rfl) ⟨1649375, by rfl⟩ : syracuseStep 2199167 = 3298751) B3298751
theorem B4460285 : Blo 976593 4460285 := bstep (se 3 (by rfl) ⟨836303, by rfl⟩ : syracuseStep 4460285 = 1672607) B1672607
theorem B2200391 : Blo 976593 2200391 := bstep (se 1 (by rfl) ⟨1650293, by rfl⟩ : syracuseStep 2200391 = 3300587) B3300587
theorem B8590895 : Blo 976593 8590895 := bstep (se 1 (by rfl) ⟨6443171, by rfl⟩ : syracuseStep 8590895 = 12886343) B12886343
theorem B50894567 : Blo 976593 50894567 := bstep (se 1 (by rfl) ⟨38170925, by rfl⟩ : syracuseStep 50894567 = 76341851) B76341851
theorem B2202623 : Blo 976593 2202623 := bstep (se 1 (by rfl) ⟨1651967, by rfl⟩ : syracuseStep 2202623 = 3303935) B3303935
theorem B1649531 : Blo 976593 1649531 := bstep (se 1 (by rfl) ⟨1237148, by rfl⟩ : syracuseStep 1649531 = 2474297) B2474297
theorem B6274367 : Blo 976593 6274367 := bstep (se 1 (by rfl) ⟨4705775, by rfl⟩ : syracuseStep 6274367 = 9411551) B9411551
theorem B2474651 : Blo 976593 2474651 := bstep (se 1 (by rfl) ⟨1855988, by rfl⟩ : syracuseStep 2474651 = 3711977) B3711977
theorem B17845055 : Blo 976593 17845055 := bstep (se 1 (by rfl) ⟨13383791, by rfl⟩ : syracuseStep 17845055 = 26767583) B26767583
theorem B3133417 : Blo 976593 3133417 := bstep (se 2 (by rfl) ⟨1175031, by rfl⟩ : syracuseStep 3133417 = 2350063) B2350063
theorem B1466063 : Blo 976593 1466063 := bstep (se 1 (by rfl) ⟨1099547, by rfl⟩ : syracuseStep 1466063 = 2199095) B2199095
theorem B1470407 : Blo 976593 1470407 := bstep (se 1 (by rfl) ⟨1102805, by rfl⟩ : syracuseStep 1470407 = 2205611) B2205611
theorem B979183 : Blo 976593 979183 := bstep (se 1 (by rfl) ⟨734387, by rfl⟩ : syracuseStep 979183 = 1468775) B1468775
theorem B979583 : Blo 976593 979583 := bstep (se 1 (by rfl) ⟨734687, by rfl⟩ : syracuseStep 979583 = 1469375) B1469375
theorem B980431 : Blo 976593 980431 := bstep (se 1 (by rfl) ⟨735323, by rfl⟩ : syracuseStep 980431 = 1470647) B1470647
theorem B2782775 : Blo 976593 2782775 := bstep (se 1 (by rfl) ⟨2087081, by rfl⟩ : syracuseStep 2782775 = 4174163) B4174163
theorem B12712463 : Blo 976593 12712463 := bstep (se 1 (by rfl) ⟨9534347, by rfl⟩ : syracuseStep 12712463 = 19068695) B19068695
theorem B108790361 : Blo 976593 108790361 := bstep (se 2 (by rfl) ⟨40796385, by rfl⟩ : syracuseStep 108790361 = 81592771) B81592771
theorem B11896703 : Blo 976593 11896703 := bstep (se 1 (by rfl) ⟨8922527, by rfl⟩ : syracuseStep 11896703 = 17845055) B17845055
theorem B1649767 : Blo 976593 1649767 := bstep (se 1 (by rfl) ⟨1237325, by rfl⟩ : syracuseStep 1649767 = 2474651) B2474651
theorem B4959791 : Blo 976593 4959791 := bstep (se 1 (by rfl) ⟨3719843, by rfl⟩ : syracuseStep 4959791 = 7439687) B7439687
theorem B33929711 : Blo 976593 33929711 := bstep (se 1 (by rfl) ⟨25447283, by rfl⟩ : syracuseStep 33929711 = 50894567) B50894567
theorem B7420733 : Blo 976593 7420733 := bstep (se 3 (by rfl) ⟨1391387, by rfl⟩ : syracuseStep 7420733 = 2782775) B2782775
theorem B4177889 : Blo 976593 4177889 := bstep (se 2 (by rfl) ⟨1566708, by rfl⟩ : syracuseStep 4177889 = 3133417) B3133417
theorem B1099687 : Blo 976593 1099687 := bstep (se 1 (by rfl) ⟨824765, by rfl⟩ : syracuseStep 1099687 = 1649531) B1649531
theorem B8474975 : Blo 976593 8474975 := bstep (se 1 (by rfl) ⟨6356231, by rfl⟩ : syracuseStep 8474975 = 12712463) B12712463
theorem B4182911 : Blo 976593 4182911 := bstep (se 1 (by rfl) ⟨3137183, by rfl⟩ : syracuseStep 4182911 = 6274367) B6274367
theorem B1466039 : Blo 976593 1466039 := bstep (se 1 (by rfl) ⟨1099529, by rfl⟩ : syracuseStep 1466039 = 2199059) B2199059
theorem B1466111 : Blo 976593 1466111 := bstep (se 1 (by rfl) ⟨1099583, by rfl⟩ : syracuseStep 1466111 = 2199167) B2199167
theorem B2973523 : Blo 976593 2973523 := bstep (se 1 (by rfl) ⟨2230142, by rfl⟩ : syracuseStep 2973523 = 4460285) B4460285
theorem B1466927 : Blo 976593 1466927 := bstep (se 1 (by rfl) ⟨1100195, by rfl⟩ : syracuseStep 1466927 = 2200391) B2200391
theorem B5727263 : Blo 976593 5727263 := bstep (se 1 (by rfl) ⟨4295447, by rfl⟩ : syracuseStep 5727263 = 8590895) B8590895
theorem B1468415 : Blo 976593 1468415 := bstep (se 1 (by rfl) ⟨1101311, by rfl⟩ : syracuseStep 1468415 = 2202623) B2202623
theorem B977375 : Blo 976593 977375 := bstep (se 1 (by rfl) ⟨733031, by rfl⟩ : syracuseStep 977375 = 1466063) B1466063
theorem B980271 : Blo 976593 980271 := bstep (se 1 (by rfl) ⟨735203, by rfl⟩ : syracuseStep 980271 = 1470407) B1470407
theorem B7931135 : Blo 976593 7931135 := bstep (se 1 (by rfl) ⟨5948351, by rfl⟩ : syracuseStep 7931135 = 11896703) B11896703
theorem B15272701 : Blo 976593 15272701 := bstep (se 3 (by rfl) ⟨2863631, by rfl⟩ : syracuseStep 15272701 = 5727263) B5727263
theorem B2788607 : Blo 976593 2788607 := bstep (se 1 (by rfl) ⟨2091455, by rfl⟩ : syracuseStep 2788607 = 4182911) B4182911
theorem B2199689 : Blo 976593 2199689 := bstep (se 2 (by rfl) ⟨824883, by rfl⟩ : syracuseStep 2199689 = 1649767) B1649767
theorem B22619807 : Blo 976593 22619807 := bstep (se 1 (by rfl) ⟨16964855, by rfl⟩ : syracuseStep 22619807 = 33929711) B33929711
theorem B72526907 : Blo 976593 72526907 := bstep (se 1 (by rfl) ⟨54395180, by rfl⟩ : syracuseStep 72526907 = 108790361) B108790361
theorem B5649983 : Blo 976593 5649983 := bstep (se 1 (by rfl) ⟨4237487, by rfl⟩ : syracuseStep 5649983 = 8474975) B8474975
theorem B1466249 : Blo 976593 1466249 := bstep (se 2 (by rfl) ⟨549843, by rfl⟩ : syracuseStep 1466249 = 1099687) B1099687
theorem B977359 : Blo 976593 977359 := bstep (se 1 (by rfl) ⟨733019, by rfl⟩ : syracuseStep 977359 = 1466039) B1466039
theorem B977407 : Blo 976593 977407 := bstep (se 1 (by rfl) ⟨733055, by rfl⟩ : syracuseStep 977407 = 1466111) B1466111
theorem B977951 : Blo 976593 977951 := bstep (se 1 (by rfl) ⟨733463, by rfl⟩ : syracuseStep 977951 = 1466927) B1466927
theorem B978943 : Blo 976593 978943 := bstep (se 1 (by rfl) ⟨734207, by rfl⟩ : syracuseStep 978943 = 1468415) B1468415
theorem B3306527 : Blo 976593 3306527 := bstep (se 1 (by rfl) ⟨2479895, by rfl⟩ : syracuseStep 3306527 = 4959791) B4959791
theorem B4947155 : Blo 976593 4947155 := bstep (se 1 (by rfl) ⟨3710366, by rfl⟩ : syracuseStep 4947155 = 7420733) B7420733
theorem B3964697 : Blo 976593 3964697 := bstep (se 2 (by rfl) ⟨1486761, by rfl⟩ : syracuseStep 3964697 = 2973523) B2973523
theorem B2785259 : Blo 976593 2785259 := bstep (se 1 (by rfl) ⟨2088944, by rfl⟩ : syracuseStep 2785259 = 4177889) B4177889
theorem B15079871 : Blo 976593 15079871 := bstep (se 1 (by rfl) ⟨11309903, by rfl⟩ : syracuseStep 15079871 = 22619807) B22619807
theorem B2204351 : Blo 976593 2204351 := bstep (se 1 (by rfl) ⟨1653263, by rfl⟩ : syracuseStep 2204351 = 3306527) B3306527
theorem B21149693 : Blo 976593 21149693 := bstep (se 3 (by rfl) ⟨3965567, by rfl⟩ : syracuseStep 21149693 = 7931135) B7931135
theorem B48351271 : Blo 976593 48351271 := bstep (se 1 (by rfl) ⟨36263453, by rfl⟩ : syracuseStep 48351271 = 72526907) B72526907
theorem B3298103 : Blo 976593 3298103 := bstep (se 1 (by rfl) ⟨2473577, by rfl⟩ : syracuseStep 3298103 = 4947155) B4947155
theorem B2643131 : Blo 976593 2643131 := bstep (se 1 (by rfl) ⟨1982348, by rfl⟩ : syracuseStep 2643131 = 3964697) B3964697
theorem B1856839 : Blo 976593 1856839 := bstep (se 1 (by rfl) ⟨1392629, by rfl⟩ : syracuseStep 1856839 = 2785259) B2785259
theorem B1466459 : Blo 976593 1466459 := bstep (se 1 (by rfl) ⟨1099844, by rfl⟩ : syracuseStep 1466459 = 2199689) B2199689
theorem B81454405 : Blo 976593 81454405 := bstep (se 4 (by rfl) ⟨7636350, by rfl⟩ : syracuseStep 81454405 = 15272701) B15272701
theorem B977499 : Blo 976593 977499 := bstep (se 1 (by rfl) ⟨733124, by rfl⟩ : syracuseStep 977499 = 1466249) B1466249
theorem B7436285 : Blo 976593 7436285 := bstep (se 3 (by rfl) ⟨1394303, by rfl⟩ : syracuseStep 7436285 = 2788607) B2788607
theorem B3766655 : Blo 976593 3766655 := bstep (se 1 (by rfl) ⟨2824991, by rfl⟩ : syracuseStep 3766655 = 5649983) B5649983
theorem B2198735 : Blo 976593 2198735 := bstep (se 1 (by rfl) ⟨1649051, by rfl⟩ : syracuseStep 2198735 = 3298103) B3298103
theorem B14099795 : Blo 976593 14099795 := bstep (se 1 (by rfl) ⟨10574846, by rfl⟩ : syracuseStep 14099795 = 21149693) B21149693
theorem B4957523 : Blo 976593 4957523 := bstep (se 1 (by rfl) ⟨3718142, by rfl⟩ : syracuseStep 4957523 = 7436285) B7436285
theorem B108605873 : Blo 976593 108605873 := bstep (se 2 (by rfl) ⟨40727202, by rfl⟩ : syracuseStep 108605873 = 81454405) B81454405
theorem B64468361 : Blo 976593 64468361 := bstep (se 2 (by rfl) ⟨24175635, by rfl⟩ : syracuseStep 64468361 = 48351271) B48351271
theorem B2475785 : Blo 976593 2475785 := bstep (se 2 (by rfl) ⟨928419, by rfl⟩ : syracuseStep 2475785 = 1856839) B1856839
theorem B2511103 : Blo 976593 2511103 := bstep (se 1 (by rfl) ⟨1883327, by rfl⟩ : syracuseStep 2511103 = 3766655) B3766655
theorem B1762087 : Blo 976593 1762087 := bstep (se 1 (by rfl) ⟨1321565, by rfl⟩ : syracuseStep 1762087 = 2643131) B2643131
theorem B10053247 : Blo 976593 10053247 := bstep (se 1 (by rfl) ⟨7539935, by rfl⟩ : syracuseStep 10053247 = 15079871) B15079871
theorem B977639 : Blo 976593 977639 := bstep (se 1 (by rfl) ⟨733229, by rfl⟩ : syracuseStep 977639 = 1466459) B1466459
theorem B1469567 : Blo 976593 1469567 := bstep (se 1 (by rfl) ⟨1102175, by rfl⟩ : syracuseStep 1469567 = 2204351) B2204351
theorem B13404329 : Blo 976593 13404329 := bstep (se 2 (by rfl) ⟨5026623, by rfl⟩ : syracuseStep 13404329 = 10053247) B10053247
theorem B3348137 : Blo 976593 3348137 := bstep (se 2 (by rfl) ⟨1255551, by rfl⟩ : syracuseStep 3348137 = 2511103) B2511103
theorem B1650523 : Blo 976593 1650523 := bstep (se 1 (by rfl) ⟨1237892, by rfl⟩ : syracuseStep 1650523 = 2475785) B2475785
theorem B72403915 : Blo 976593 72403915 := bstep (se 1 (by rfl) ⟨54302936, by rfl⟩ : syracuseStep 72403915 = 108605873) B108605873
theorem B42978907 : Blo 976593 42978907 := bstep (se 1 (by rfl) ⟨32234180, by rfl⟩ : syracuseStep 42978907 = 64468361) B64468361
theorem B2349449 : Blo 976593 2349449 := bstep (se 2 (by rfl) ⟨881043, by rfl⟩ : syracuseStep 2349449 = 1762087) B1762087
theorem B1465823 : Blo 976593 1465823 := bstep (se 1 (by rfl) ⟨1099367, by rfl⟩ : syracuseStep 1465823 = 2198735) B2198735
theorem B9399863 : Blo 976593 9399863 := bstep (se 1 (by rfl) ⟨7049897, by rfl⟩ : syracuseStep 9399863 = 14099795) B14099795
theorem B3305015 : Blo 976593 3305015 := bstep (se 1 (by rfl) ⟨2478761, by rfl⟩ : syracuseStep 3305015 = 4957523) B4957523
theorem B979711 : Blo 976593 979711 := bstep (se 1 (by rfl) ⟨734783, by rfl⟩ : syracuseStep 979711 = 1469567) B1469567
theorem B96538553 : Blo 976593 96538553 := bstep (se 2 (by rfl) ⟨36201957, by rfl⟩ : syracuseStep 96538553 = 72403915) B72403915
theorem B2200697 : Blo 976593 2200697 := bstep (se 2 (by rfl) ⟨825261, by rfl⟩ : syracuseStep 2200697 = 1650523) B1650523
theorem B6266575 : Blo 976593 6266575 := bstep (se 1 (by rfl) ⟨4699931, by rfl⟩ : syracuseStep 6266575 = 9399863) B9399863
theorem B2203343 : Blo 976593 2203343 := bstep (se 1 (by rfl) ⟨1652507, by rfl⟩ : syracuseStep 2203343 = 3305015) B3305015
theorem B229220837 : Blo 976593 229220837 := bstep (se 4 (by rfl) ⟨21489453, by rfl⟩ : syracuseStep 229220837 = 42978907) B42978907
theorem B8928365 : Blo 976593 8928365 := bstep (se 3 (by rfl) ⟨1674068, by rfl⟩ : syracuseStep 8928365 = 3348137) B3348137
theorem B8936219 : Blo 976593 8936219 := bstep (se 1 (by rfl) ⟨6702164, by rfl⟩ : syracuseStep 8936219 = 13404329) B13404329
theorem B1566299 : Blo 976593 1566299 := bstep (se 1 (by rfl) ⟨1174724, by rfl⟩ : syracuseStep 1566299 = 2349449) B2349449
theorem B977215 : Blo 976593 977215 := bstep (se 1 (by rfl) ⟨732911, by rfl⟩ : syracuseStep 977215 = 1465823) B1465823
theorem B64359035 : Blo 976593 64359035 := bstep (se 1 (by rfl) ⟨48269276, by rfl⟩ : syracuseStep 64359035 = 96538553) B96538553
theorem B152813891 : Blo 976593 152813891 := bstep (se 1 (by rfl) ⟨114610418, by rfl⟩ : syracuseStep 152813891 = 229220837) B229220837
theorem B23808973 : Blo 976593 23808973 := bstep (se 3 (by rfl) ⟨4464182, by rfl⟩ : syracuseStep 23808973 = 8928365) B8928365
theorem B1467131 : Blo 976593 1467131 := bstep (se 1 (by rfl) ⟨1100348, by rfl⟩ : syracuseStep 1467131 = 2200697) B2200697
theorem B5957479 : Blo 976593 5957479 := bstep (se 1 (by rfl) ⟨4468109, by rfl⟩ : syracuseStep 5957479 = 8936219) B8936219
theorem B1468895 : Blo 976593 1468895 := bstep (se 1 (by rfl) ⟨1101671, by rfl⟩ : syracuseStep 1468895 = 2203343) B2203343
theorem B1044199 : Blo 976593 1044199 := bstep (se 1 (by rfl) ⟨783149, by rfl⟩ : syracuseStep 1044199 = 1566299) B1566299
theorem B8355433 : Blo 976593 8355433 := bstep (se 2 (by rfl) ⟨3133287, by rfl⟩ : syracuseStep 8355433 = 6266575) B6266575
theorem B101875927 : Blo 976593 101875927 := bstep (se 1 (by rfl) ⟨76406945, by rfl⟩ : syracuseStep 101875927 = 152813891) B152813891
theorem B42906023 : Blo 976593 42906023 := bstep (se 1 (by rfl) ⟨32179517, by rfl⟩ : syracuseStep 42906023 = 64359035) B64359035
theorem B7943305 : Blo 976593 7943305 := bstep (se 2 (by rfl) ⟨2978739, by rfl⟩ : syracuseStep 7943305 = 5957479) B5957479
theorem B1392265 : Blo 976593 1392265 := bstep (se 2 (by rfl) ⟨522099, by rfl⟩ : syracuseStep 1392265 = 1044199) B1044199
theorem B31745297 : Blo 976593 31745297 := bstep (se 2 (by rfl) ⟨11904486, by rfl⟩ : syracuseStep 31745297 = 23808973) B23808973
theorem B978087 : Blo 976593 978087 := bstep (se 1 (by rfl) ⟨733565, by rfl⟩ : syracuseStep 978087 = 1467131) B1467131
theorem B979263 : Blo 976593 979263 := bstep (se 1 (by rfl) ⟨734447, by rfl⟩ : syracuseStep 979263 = 1468895) B1468895
theorem B11140577 : Blo 976593 11140577 := bstep (se 2 (by rfl) ⟨4177716, by rfl⟩ : syracuseStep 11140577 = 8355433) B8355433
theorem B10591073 : Blo 976593 10591073 := bstep (se 2 (by rfl) ⟨3971652, by rfl⟩ : syracuseStep 10591073 = 7943305) B7943305
theorem B135834569 : Blo 976593 135834569 := bstep (se 2 (by rfl) ⟨50937963, by rfl⟩ : syracuseStep 135834569 = 101875927) B101875927
theorem B1856353 : Blo 976593 1856353 := bstep (se 2 (by rfl) ⟨696132, by rfl⟩ : syracuseStep 1856353 = 1392265) B1392265
theorem B7427051 : Blo 976593 7427051 := bstep (se 1 (by rfl) ⟨5570288, by rfl⟩ : syracuseStep 7427051 = 11140577) B11140577
theorem B21163531 : Blo 976593 21163531 := bstep (se 1 (by rfl) ⟨15872648, by rfl⟩ : syracuseStep 21163531 = 31745297) B31745297
theorem B28604015 : Blo 976593 28604015 := bstep (se 1 (by rfl) ⟨21453011, by rfl⟩ : syracuseStep 28604015 = 42906023) B42906023
theorem B4951367 : Blo 976593 4951367 := bstep (se 1 (by rfl) ⟨3713525, by rfl⟩ : syracuseStep 4951367 = 7427051) B7427051
theorem B28218041 : Blo 976593 28218041 := bstep (se 2 (by rfl) ⟨10581765, by rfl⟩ : syracuseStep 28218041 = 21163531) B21163531
theorem B7060715 : Blo 976593 7060715 := bstep (se 1 (by rfl) ⟨5295536, by rfl⟩ : syracuseStep 7060715 = 10591073) B10591073
theorem B2475137 : Blo 976593 2475137 := bstep (se 2 (by rfl) ⟨928176, by rfl⟩ : syracuseStep 2475137 = 1856353) B1856353
theorem B90556379 : Blo 976593 90556379 := bstep (se 1 (by rfl) ⟨67917284, by rfl⟩ : syracuseStep 90556379 = 135834569) B135834569
theorem B19069343 : Blo 976593 19069343 := bstep (se 1 (by rfl) ⟨14302007, by rfl⟩ : syracuseStep 19069343 = 28604015) B28604015
theorem B18812027 : Blo 976593 18812027 := bstep (se 1 (by rfl) ⟨14109020, by rfl⟩ : syracuseStep 18812027 = 28218041) B28218041
theorem B1650091 : Blo 976593 1650091 := bstep (se 1 (by rfl) ⟨1237568, by rfl⟩ : syracuseStep 1650091 = 2475137) B2475137
theorem B60370919 : Blo 976593 60370919 := bstep (se 1 (by rfl) ⟨45278189, by rfl⟩ : syracuseStep 60370919 = 90556379) B90556379
theorem B4707143 : Blo 976593 4707143 := bstep (se 1 (by rfl) ⟨3530357, by rfl⟩ : syracuseStep 4707143 = 7060715) B7060715
theorem B3300911 : Blo 976593 3300911 := bstep (se 1 (by rfl) ⟨2475683, by rfl⟩ : syracuseStep 3300911 = 4951367) B4951367
theorem B12712895 : Blo 976593 12712895 := bstep (se 1 (by rfl) ⟨9534671, by rfl⟩ : syracuseStep 12712895 = 19069343) B19069343
theorem B2200121 : Blo 976593 2200121 := bstep (se 2 (by rfl) ⟨825045, by rfl⟩ : syracuseStep 2200121 = 1650091) B1650091
theorem B2200607 : Blo 976593 2200607 := bstep (se 1 (by rfl) ⟨1650455, by rfl⟩ : syracuseStep 2200607 = 3300911) B3300911
theorem B40247279 : Blo 976593 40247279 := bstep (se 1 (by rfl) ⟨30185459, by rfl⟩ : syracuseStep 40247279 = 60370919) B60370919
theorem B8475263 : Blo 976593 8475263 := bstep (se 1 (by rfl) ⟨6356447, by rfl⟩ : syracuseStep 8475263 = 12712895) B12712895
theorem B12541351 : Blo 976593 12541351 := bstep (se 1 (by rfl) ⟨9406013, by rfl⟩ : syracuseStep 12541351 = 18812027) B18812027
theorem B3138095 : Blo 976593 3138095 := bstep (se 1 (by rfl) ⟨2353571, by rfl⟩ : syracuseStep 3138095 = 4707143) B4707143
theorem B16721801 : Blo 976593 16721801 := bstep (se 2 (by rfl) ⟨6270675, by rfl⟩ : syracuseStep 16721801 = 12541351) B12541351
theorem B5650175 : Blo 976593 5650175 := bstep (se 1 (by rfl) ⟨4237631, by rfl⟩ : syracuseStep 5650175 = 8475263) B8475263
theorem B1466747 : Blo 976593 1466747 := bstep (se 1 (by rfl) ⟨1100060, by rfl⟩ : syracuseStep 1466747 = 2200121) B2200121
theorem B1467071 : Blo 976593 1467071 := bstep (se 1 (by rfl) ⟨1100303, by rfl⟩ : syracuseStep 1467071 = 2200607) B2200607
theorem B26831519 : Blo 976593 26831519 := bstep (se 1 (by rfl) ⟨20123639, by rfl⟩ : syracuseStep 26831519 = 40247279) B40247279
theorem B2092063 : Blo 976593 2092063 := bstep (se 1 (by rfl) ⟨1569047, by rfl⟩ : syracuseStep 2092063 = 3138095) B3138095
theorem B2789417 : Blo 976593 2789417 := bstep (se 2 (by rfl) ⟨1046031, by rfl⟩ : syracuseStep 2789417 = 2092063) B2092063
theorem B11147867 : Blo 976593 11147867 := bstep (se 1 (by rfl) ⟨8360900, by rfl⟩ : syracuseStep 11147867 = 16721801) B16721801
theorem B15067133 : Blo 976593 15067133 := bstep (se 3 (by rfl) ⟨2825087, by rfl⟩ : syracuseStep 15067133 = 5650175) B5650175
theorem B977831 : Blo 976593 977831 := bstep (se 1 (by rfl) ⟨733373, by rfl⟩ : syracuseStep 977831 = 1466747) B1466747
theorem B978047 : Blo 976593 978047 := bstep (se 1 (by rfl) ⟨733535, by rfl⟩ : syracuseStep 978047 = 1467071) B1467071
theorem B17887679 : Blo 976593 17887679 := bstep (se 1 (by rfl) ⟨13415759, by rfl⟩ : syracuseStep 17887679 = 26831519) B26831519
theorem B10044755 : Blo 976593 10044755 := bstep (se 1 (by rfl) ⟨7533566, by rfl⟩ : syracuseStep 10044755 = 15067133) B15067133
theorem B1859611 : Blo 976593 1859611 := bstep (se 1 (by rfl) ⟨1394708, by rfl⟩ : syracuseStep 1859611 = 2789417) B2789417
theorem B7431911 : Blo 976593 7431911 := bstep (se 1 (by rfl) ⟨5573933, by rfl⟩ : syracuseStep 7431911 = 11147867) B11147867
theorem B11925119 : Blo 976593 11925119 := bstep (se 1 (by rfl) ⟨8943839, by rfl⟩ : syracuseStep 11925119 = 17887679) B17887679
theorem B4954607 : Blo 976593 4954607 := bstep (se 1 (by rfl) ⟨3715955, by rfl⟩ : syracuseStep 4954607 = 7431911) B7431911
theorem B6696503 : Blo 976593 6696503 := bstep (se 1 (by rfl) ⟨5022377, by rfl⟩ : syracuseStep 6696503 = 10044755) B10044755
theorem B7950079 : Blo 976593 7950079 := bstep (se 1 (by rfl) ⟨5962559, by rfl⟩ : syracuseStep 7950079 = 11925119) B11925119
theorem B2479481 : Blo 976593 2479481 := bstep (se 2 (by rfl) ⟨929805, by rfl⟩ : syracuseStep 2479481 = 1859611) B1859611
theorem B4464335 : Blo 976593 4464335 := bstep (se 1 (by rfl) ⟨3348251, by rfl⟩ : syracuseStep 4464335 = 6696503) B6696503
theorem B1652987 : Blo 976593 1652987 := bstep (se 1 (by rfl) ⟨1239740, by rfl⟩ : syracuseStep 1652987 = 2479481) B2479481
theorem B10600105 : Blo 976593 10600105 := bstep (se 2 (by rfl) ⟨3975039, by rfl⟩ : syracuseStep 10600105 = 7950079) B7950079
theorem B3303071 : Blo 976593 3303071 := bstep (se 1 (by rfl) ⟨2477303, by rfl⟩ : syracuseStep 3303071 = 4954607) B4954607
theorem B2202047 : Blo 976593 2202047 := bstep (se 1 (by rfl) ⟨1651535, by rfl⟩ : syracuseStep 2202047 = 3303071) B3303071
theorem B14133473 : Blo 976593 14133473 := bstep (se 2 (by rfl) ⟨5300052, by rfl⟩ : syracuseStep 14133473 = 10600105) B10600105
theorem B1101991 : Blo 976593 1101991 := bstep (se 1 (by rfl) ⟨826493, by rfl⟩ : syracuseStep 1101991 = 1652987) B1652987
theorem B2976223 : Blo 976593 2976223 := bstep (se 1 (by rfl) ⟨2232167, by rfl⟩ : syracuseStep 2976223 = 4464335) B4464335
theorem B3968297 : Blo 976593 3968297 := bstep (se 2 (by rfl) ⟨1488111, by rfl⟩ : syracuseStep 3968297 = 2976223) B2976223
theorem B9422315 : Blo 976593 9422315 := bstep (se 1 (by rfl) ⟨7066736, by rfl⟩ : syracuseStep 9422315 = 14133473) B14133473
theorem B1468031 : Blo 976593 1468031 := bstep (se 1 (by rfl) ⟨1101023, by rfl⟩ : syracuseStep 1468031 = 2202047) B2202047
theorem B1469321 : Blo 976593 1469321 := bstep (se 2 (by rfl) ⟨550995, by rfl⟩ : syracuseStep 1469321 = 1101991) B1101991
theorem B6281543 : Blo 976593 6281543 := bstep (se 1 (by rfl) ⟨4711157, by rfl⟩ : syracuseStep 6281543 = 9422315) B9422315
theorem B2645531 : Blo 976593 2645531 := bstep (se 1 (by rfl) ⟨1984148, by rfl⟩ : syracuseStep 2645531 = 3968297) B3968297
theorem B978687 : Blo 976593 978687 := bstep (se 1 (by rfl) ⟨734015, by rfl⟩ : syracuseStep 978687 = 1468031) B1468031
theorem B979547 : Blo 976593 979547 := bstep (se 1 (by rfl) ⟨734660, by rfl⟩ : syracuseStep 979547 = 1469321) B1469321
theorem B4187695 : Blo 976593 4187695 := bstep (se 1 (by rfl) ⟨3140771, by rfl⟩ : syracuseStep 4187695 = 6281543) B6281543
theorem B1763687 : Blo 976593 1763687 := bstep (se 1 (by rfl) ⟨1322765, by rfl⟩ : syracuseStep 1763687 = 2645531) B2645531
theorem B5583593 : Blo 976593 5583593 := bstep (se 2 (by rfl) ⟨2093847, by rfl⟩ : syracuseStep 5583593 = 4187695) B4187695
theorem B1175791 : Blo 976593 1175791 := bstep (se 1 (by rfl) ⟨881843, by rfl⟩ : syracuseStep 1175791 = 1763687) B1763687
theorem B3722395 : Blo 976593 3722395 := bstep (se 1 (by rfl) ⟨2791796, by rfl⟩ : syracuseStep 3722395 = 5583593) B5583593
theorem B1567721 : Blo 976593 1567721 := bstep (se 2 (by rfl) ⟨587895, by rfl⟩ : syracuseStep 1567721 = 1175791) B1175791
theorem B4963193 : Blo 976593 4963193 := bstep (se 2 (by rfl) ⟨1861197, by rfl⟩ : syracuseStep 4963193 = 3722395) B3722395
theorem B1045147 : Blo 976593 1045147 := bstep (se 1 (by rfl) ⟨783860, by rfl⟩ : syracuseStep 1045147 = 1567721) B1567721
theorem B1393529 : Blo 976593 1393529 := bstep (se 2 (by rfl) ⟨522573, by rfl⟩ : syracuseStep 1393529 = 1045147) B1045147
theorem B3308795 : Blo 976593 3308795 := bstep (se 1 (by rfl) ⟨2481596, by rfl⟩ : syracuseStep 3308795 = 4963193) B4963193
theorem B2205863 : Blo 976593 2205863 := bstep (se 1 (by rfl) ⟨1654397, by rfl⟩ : syracuseStep 2205863 = 3308795) B3308795
theorem B3716077 : Blo 976593 3716077 := bstep (se 3 (by rfl) ⟨696764, by rfl⟩ : syracuseStep 3716077 = 1393529) B1393529
theorem B4954769 : Blo 976593 4954769 := bstep (se 2 (by rfl) ⟨1858038, by rfl⟩ : syracuseStep 4954769 = 3716077) B3716077
theorem B1470575 : Blo 976593 1470575 := bstep (se 1 (by rfl) ⟨1102931, by rfl⟩ : syracuseStep 1470575 = 2205863) B2205863
theorem B3303179 : Blo 976593 3303179 := bstep (se 1 (by rfl) ⟨2477384, by rfl⟩ : syracuseStep 3303179 = 4954769) B4954769
theorem B980383 : Blo 976593 980383 := bstep (se 1 (by rfl) ⟨735287, by rfl⟩ : syracuseStep 980383 = 1470575) B1470575
theorem B2202119 : Blo 976593 2202119 := bstep (se 1 (by rfl) ⟨1651589, by rfl⟩ : syracuseStep 2202119 = 3303179) B3303179
theorem B1468079 : Blo 976593 1468079 := bstep (se 1 (by rfl) ⟨1101059, by rfl⟩ : syracuseStep 1468079 = 2202119) B2202119
theorem B978719 : Blo 976593 978719 := bstep (se 1 (by rfl) ⟨734039, by rfl⟩ : syracuseStep 978719 = 1468079) B1468079

theorem C0 (j : ℕ) (h1 : 244148 ≤ j) (h2 : j ≤ 244847) : Blo 976593 (4 * j + 3) := by
  interval_cases j
  · exact B976595
  · exact B976599
  · exact B976603
  · exact B976607
  · exact B976611
  · exact B976615
  · exact B976619
  · exact B976623
  · exact B976627
  · exact B976631
  · exact B976635
  · exact B976639
  · exact B976643
  · exact B976647
  · exact B976651
  · exact B976655
  · exact B976659
  · exact B976663
  · exact B976667
  · exact B976671
  · exact B976675
  · exact B976679
  · exact B976683
  · exact B976687
  · exact B976691
  · exact B976695
  · exact B976699
  · exact B976703
  · exact B976707
  · exact B976711
  · exact B976715
  · exact B976719
  · exact B976723
  · exact B976727
  · exact B976731
  · exact B976735
  · exact B976739
  · exact B976743
  · exact B976747
  · exact B976751
  · exact B976755
  · exact B976759
  · exact B976763
  · exact B976767
  · exact B976771
  · exact B976775
  · exact B976779
  · exact B976783
  · exact B976787
  · exact B976791
  · exact B976795
  · exact B976799
  · exact B976803
  · exact B976807
  · exact B976811
  · exact B976815
  · exact B976819
  · exact B976823
  · exact B976827
  · exact B976831
  · exact B976835
  · exact B976839
  · exact B976843
  · exact B976847
  · exact B976851
  · exact B976855
  · exact B976859
  · exact B976863
  · exact B976867
  · exact B976871
  · exact B976875
  · exact B976879
  · exact B976883
  · exact B976887
  · exact B976891
  · exact B976895
  · exact B976899
  · exact B976903
  · exact B976907
  · exact B976911
  · exact B976915
  · exact B976919
  · exact B976923
  · exact B976927
  · exact B976931
  · exact B976935
  · exact B976939
  · exact B976943
  · exact B976947
  · exact B976951
  · exact B976955
  · exact B976959
  · exact B976963
  · exact B976967
  · exact B976971
  · exact B976975
  · exact B976979
  · exact B976983
  · exact B976987
  · exact B976991
  · exact B976995
  · exact B976999
  · exact B977003
  · exact B977007
  · exact B977011
  · exact B977015
  · exact B977019
  · exact B977023
  · exact B977027
  · exact B977031
  · exact B977035
  · exact B977039
  · exact B977043
  · exact B977047
  · exact B977051
  · exact B977055
  · exact B977059
  · exact B977063
  · exact B977067
  · exact B977071
  · exact B977075
  · exact B977079
  · exact B977083
  · exact B977087
  · exact B977091
  · exact B977095
  · exact B977099
  · exact B977103
  · exact B977107
  · exact B977111
  · exact B977115
  · exact B977119
  · exact B977123
  · exact B977127
  · exact B977131
  · exact B977135
  · exact B977139
  · exact B977143
  · exact B977147
  · exact B977151
  · exact B977155
  · exact B977159
  · exact B977163
  · exact B977167
  · exact B977171
  · exact B977175
  · exact B977179
  · exact B977183
  · exact B977187
  · exact B977191
  · exact B977195
  · exact B977199
  · exact B977203
  · exact B977207
  · exact B977211
  · exact B977215
  · exact B977219
  · exact B977223
  · exact B977227
  · exact B977231
  · exact B977235
  · exact B977239
  · exact B977243
  · exact B977247
  · exact B977251
  · exact B977255
  · exact B977259
  · exact B977263
  · exact B977267
  · exact B977271
  · exact B977275
  · exact B977279
  · exact B977283
  · exact B977287
  · exact B977291
  · exact B977295
  · exact B977299
  · exact B977303
  · exact B977307
  · exact B977311
  · exact B977315
  · exact B977319
  · exact B977323
  · exact B977327
  · exact B977331
  · exact B977335
  · exact B977339
  · exact B977343
  · exact B977347
  · exact B977351
  · exact B977355
  · exact B977359
  · exact B977363
  · exact B977367
  · exact B977371
  · exact B977375
  · exact B977379
  · exact B977383
  · exact B977387
  · exact B977391
  · exact B977395
  · exact B977399
  · exact B977403
  · exact B977407
  · exact B977411
  · exact B977415
  · exact B977419
  · exact B977423
  · exact B977427
  · exact B977431
  · exact B977435
  · exact B977439
  · exact B977443
  · exact B977447
  · exact B977451
  · exact B977455
  · exact B977459
  · exact B977463
  · exact B977467
  · exact B977471
  · exact B977475
  · exact B977479
  · exact B977483
  · exact B977487
  · exact B977491
  · exact B977495
  · exact B977499
  · exact B977503
  · exact B977507
  · exact B977511
  · exact B977515
  · exact B977519
  · exact B977523
  · exact B977527
  · exact B977531
  · exact B977535
  · exact B977539
  · exact B977543
  · exact B977547
  · exact B977551
  · exact B977555
  · exact B977559
  · exact B977563
  · exact B977567
  · exact B977571
  · exact B977575
  · exact B977579
  · exact B977583
  · exact B977587
  · exact B977591
  · exact B977595
  · exact B977599
  · exact B977603
  · exact B977607
  · exact B977611
  · exact B977615
  · exact B977619
  · exact B977623
  · exact B977627
  · exact B977631
  · exact B977635
  · exact B977639
  · exact B977643
  · exact B977647
  · exact B977651
  · exact B977655
  · exact B977659
  · exact B977663
  · exact B977667
  · exact B977671
  · exact B977675
  · exact B977679
  · exact B977683
  · exact B977687
  · exact B977691
  · exact B977695
  · exact B977699
  · exact B977703
  · exact B977707
  · exact B977711
  · exact B977715
  · exact B977719
  · exact B977723
  · exact B977727
  · exact B977731
  · exact B977735
  · exact B977739
  · exact B977743
  · exact B977747
  · exact B977751
  · exact B977755
  · exact B977759
  · exact B977763
  · exact B977767
  · exact B977771
  · exact B977775
  · exact B977779
  · exact B977783
  · exact B977787
  · exact B977791
  · exact B977795
  · exact B977799
  · exact B977803
  · exact B977807
  · exact B977811
  · exact B977815
  · exact B977819
  · exact B977823
  · exact B977827
  · exact B977831
  · exact B977835
  · exact B977839
  · exact B977843
  · exact B977847
  · exact B977851
  · exact B977855
  · exact B977859
  · exact B977863
  · exact B977867
  · exact B977871
  · exact B977875
  · exact B977879
  · exact B977883
  · exact B977887
  · exact B977891
  · exact B977895
  · exact B977899
  · exact B977903
  · exact B977907
  · exact B977911
  · exact B977915
  · exact B977919
  · exact B977923
  · exact B977927
  · exact B977931
  · exact B977935
  · exact B977939
  · exact B977943
  · exact B977947
  · exact B977951
  · exact B977955
  · exact B977959
  · exact B977963
  · exact B977967
  · exact B977971
  · exact B977975
  · exact B977979
  · exact B977983
  · exact B977987
  · exact B977991
  · exact B977995
  · exact B977999
  · exact B978003
  · exact B978007
  · exact B978011
  · exact B978015
  · exact B978019
  · exact B978023
  · exact B978027
  · exact B978031
  · exact B978035
  · exact B978039
  · exact B978043
  · exact B978047
  · exact B978051
  · exact B978055
  · exact B978059
  · exact B978063
  · exact B978067
  · exact B978071
  · exact B978075
  · exact B978079
  · exact B978083
  · exact B978087
  · exact B978091
  · exact B978095
  · exact B978099
  · exact B978103
  · exact B978107
  · exact B978111
  · exact B978115
  · exact B978119
  · exact B978123
  · exact B978127
  · exact B978131
  · exact B978135
  · exact B978139
  · exact B978143
  · exact B978147
  · exact B978151
  · exact B978155
  · exact B978159
  · exact B978163
  · exact B978167
  · exact B978171
  · exact B978175
  · exact B978179
  · exact B978183
  · exact B978187
  · exact B978191
  · exact B978195
  · exact B978199
  · exact B978203
  · exact B978207
  · exact B978211
  · exact B978215
  · exact B978219
  · exact B978223
  · exact B978227
  · exact B978231
  · exact B978235
  · exact B978239
  · exact B978243
  · exact B978247
  · exact B978251
  · exact B978255
  · exact B978259
  · exact B978263
  · exact B978267
  · exact B978271
  · exact B978275
  · exact B978279
  · exact B978283
  · exact B978287
  · exact B978291
  · exact B978295
  · exact B978299
  · exact B978303
  · exact B978307
  · exact B978311
  · exact B978315
  · exact B978319
  · exact B978323
  · exact B978327
  · exact B978331
  · exact B978335
  · exact B978339
  · exact B978343
  · exact B978347
  · exact B978351
  · exact B978355
  · exact B978359
  · exact B978363
  · exact B978367
  · exact B978371
  · exact B978375
  · exact B978379
  · exact B978383
  · exact B978387
  · exact B978391
  · exact B978395
  · exact B978399
  · exact B978403
  · exact B978407
  · exact B978411
  · exact B978415
  · exact B978419
  · exact B978423
  · exact B978427
  · exact B978431
  · exact B978435
  · exact B978439
  · exact B978443
  · exact B978447
  · exact B978451
  · exact B978455
  · exact B978459
  · exact B978463
  · exact B978467
  · exact B978471
  · exact B978475
  · exact B978479
  · exact B978483
  · exact B978487
  · exact B978491
  · exact B978495
  · exact B978499
  · exact B978503
  · exact B978507
  · exact B978511
  · exact B978515
  · exact B978519
  · exact B978523
  · exact B978527
  · exact B978531
  · exact B978535
  · exact B978539
  · exact B978543
  · exact B978547
  · exact B978551
  · exact B978555
  · exact B978559
  · exact B978563
  · exact B978567
  · exact B978571
  · exact B978575
  · exact B978579
  · exact B978583
  · exact B978587
  · exact B978591
  · exact B978595
  · exact B978599
  · exact B978603
  · exact B978607
  · exact B978611
  · exact B978615
  · exact B978619
  · exact B978623
  · exact B978627
  · exact B978631
  · exact B978635
  · exact B978639
  · exact B978643
  · exact B978647
  · exact B978651
  · exact B978655
  · exact B978659
  · exact B978663
  · exact B978667
  · exact B978671
  · exact B978675
  · exact B978679
  · exact B978683
  · exact B978687
  · exact B978691
  · exact B978695
  · exact B978699
  · exact B978703
  · exact B978707
  · exact B978711
  · exact B978715
  · exact B978719
  · exact B978723
  · exact B978727
  · exact B978731
  · exact B978735
  · exact B978739
  · exact B978743
  · exact B978747
  · exact B978751
  · exact B978755
  · exact B978759
  · exact B978763
  · exact B978767
  · exact B978771
  · exact B978775
  · exact B978779
  · exact B978783
  · exact B978787
  · exact B978791
  · exact B978795
  · exact B978799
  · exact B978803
  · exact B978807
  · exact B978811
  · exact B978815
  · exact B978819
  · exact B978823
  · exact B978827
  · exact B978831
  · exact B978835
  · exact B978839
  · exact B978843
  · exact B978847
  · exact B978851
  · exact B978855
  · exact B978859
  · exact B978863
  · exact B978867
  · exact B978871
  · exact B978875
  · exact B978879
  · exact B978883
  · exact B978887
  · exact B978891
  · exact B978895
  · exact B978899
  · exact B978903
  · exact B978907
  · exact B978911
  · exact B978915
  · exact B978919
  · exact B978923
  · exact B978927
  · exact B978931
  · exact B978935
  · exact B978939
  · exact B978943
  · exact B978947
  · exact B978951
  · exact B978955
  · exact B978959
  · exact B978963
  · exact B978967
  · exact B978971
  · exact B978975
  · exact B978979
  · exact B978983
  · exact B978987
  · exact B978991
  · exact B978995
  · exact B978999
  · exact B979003
  · exact B979007
  · exact B979011
  · exact B979015
  · exact B979019
  · exact B979023
  · exact B979027
  · exact B979031
  · exact B979035
  · exact B979039
  · exact B979043
  · exact B979047
  · exact B979051
  · exact B979055
  · exact B979059
  · exact B979063
  · exact B979067
  · exact B979071
  · exact B979075
  · exact B979079
  · exact B979083
  · exact B979087
  · exact B979091
  · exact B979095
  · exact B979099
  · exact B979103
  · exact B979107
  · exact B979111
  · exact B979115
  · exact B979119
  · exact B979123
  · exact B979127
  · exact B979131
  · exact B979135
  · exact B979139
  · exact B979143
  · exact B979147
  · exact B979151
  · exact B979155
  · exact B979159
  · exact B979163
  · exact B979167
  · exact B979171
  · exact B979175
  · exact B979179
  · exact B979183
  · exact B979187
  · exact B979191
  · exact B979195
  · exact B979199
  · exact B979203
  · exact B979207
  · exact B979211
  · exact B979215
  · exact B979219
  · exact B979223
  · exact B979227
  · exact B979231
  · exact B979235
  · exact B979239
  · exact B979243
  · exact B979247
  · exact B979251
  · exact B979255
  · exact B979259
  · exact B979263
  · exact B979267
  · exact B979271
  · exact B979275
  · exact B979279
  · exact B979283
  · exact B979287
  · exact B979291
  · exact B979295
  · exact B979299
  · exact B979303
  · exact B979307
  · exact B979311
  · exact B979315
  · exact B979319
  · exact B979323
  · exact B979327
  · exact B979331
  · exact B979335
  · exact B979339
  · exact B979343
  · exact B979347
  · exact B979351
  · exact B979355
  · exact B979359
  · exact B979363
  · exact B979367
  · exact B979371
  · exact B979375
  · exact B979379
  · exact B979383
  · exact B979387
  · exact B979391

theorem C1 (j : ℕ) (h1 : 244848 ≤ j) (h2 : j ≤ 245147) : Blo 976593 (4 * j + 3) := by
  interval_cases j
  · exact B979395
  · exact B979399
  · exact B979403
  · exact B979407
  · exact B979411
  · exact B979415
  · exact B979419
  · exact B979423
  · exact B979427
  · exact B979431
  · exact B979435
  · exact B979439
  · exact B979443
  · exact B979447
  · exact B979451
  · exact B979455
  · exact B979459
  · exact B979463
  · exact B979467
  · exact B979471
  · exact B979475
  · exact B979479
  · exact B979483
  · exact B979487
  · exact B979491
  · exact B979495
  · exact B979499
  · exact B979503
  · exact B979507
  · exact B979511
  · exact B979515
  · exact B979519
  · exact B979523
  · exact B979527
  · exact B979531
  · exact B979535
  · exact B979539
  · exact B979543
  · exact B979547
  · exact B979551
  · exact B979555
  · exact B979559
  · exact B979563
  · exact B979567
  · exact B979571
  · exact B979575
  · exact B979579
  · exact B979583
  · exact B979587
  · exact B979591
  · exact B979595
  · exact B979599
  · exact B979603
  · exact B979607
  · exact B979611
  · exact B979615
  · exact B979619
  · exact B979623
  · exact B979627
  · exact B979631
  · exact B979635
  · exact B979639
  · exact B979643
  · exact B979647
  · exact B979651
  · exact B979655
  · exact B979659
  · exact B979663
  · exact B979667
  · exact B979671
  · exact B979675
  · exact B979679
  · exact B979683
  · exact B979687
  · exact B979691
  · exact B979695
  · exact B979699
  · exact B979703
  · exact B979707
  · exact B979711
  · exact B979715
  · exact B979719
  · exact B979723
  · exact B979727
  · exact B979731
  · exact B979735
  · exact B979739
  · exact B979743
  · exact B979747
  · exact B979751
  · exact B979755
  · exact B979759
  · exact B979763
  · exact B979767
  · exact B979771
  · exact B979775
  · exact B979779
  · exact B979783
  · exact B979787
  · exact B979791
  · exact B979795
  · exact B979799
  · exact B979803
  · exact B979807
  · exact B979811
  · exact B979815
  · exact B979819
  · exact B979823
  · exact B979827
  · exact B979831
  · exact B979835
  · exact B979839
  · exact B979843
  · exact B979847
  · exact B979851
  · exact B979855
  · exact B979859
  · exact B979863
  · exact B979867
  · exact B979871
  · exact B979875
  · exact B979879
  · exact B979883
  · exact B979887
  · exact B979891
  · exact B979895
  · exact B979899
  · exact B979903
  · exact B979907
  · exact B979911
  · exact B979915
  · exact B979919
  · exact B979923
  · exact B979927
  · exact B979931
  · exact B979935
  · exact B979939
  · exact B979943
  · exact B979947
  · exact B979951
  · exact B979955
  · exact B979959
  · exact B979963
  · exact B979967
  · exact B979971
  · exact B979975
  · exact B979979
  · exact B979983
  · exact B979987
  · exact B979991
  · exact B979995
  · exact B979999
  · exact B980003
  · exact B980007
  · exact B980011
  · exact B980015
  · exact B980019
  · exact B980023
  · exact B980027
  · exact B980031
  · exact B980035
  · exact B980039
  · exact B980043
  · exact B980047
  · exact B980051
  · exact B980055
  · exact B980059
  · exact B980063
  · exact B980067
  · exact B980071
  · exact B980075
  · exact B980079
  · exact B980083
  · exact B980087
  · exact B980091
  · exact B980095
  · exact B980099
  · exact B980103
  · exact B980107
  · exact B980111
  · exact B980115
  · exact B980119
  · exact B980123
  · exact B980127
  · exact B980131
  · exact B980135
  · exact B980139
  · exact B980143
  · exact B980147
  · exact B980151
  · exact B980155
  · exact B980159
  · exact B980163
  · exact B980167
  · exact B980171
  · exact B980175
  · exact B980179
  · exact B980183
  · exact B980187
  · exact B980191
  · exact B980195
  · exact B980199
  · exact B980203
  · exact B980207
  · exact B980211
  · exact B980215
  · exact B980219
  · exact B980223
  · exact B980227
  · exact B980231
  · exact B980235
  · exact B980239
  · exact B980243
  · exact B980247
  · exact B980251
  · exact B980255
  · exact B980259
  · exact B980263
  · exact B980267
  · exact B980271
  · exact B980275
  · exact B980279
  · exact B980283
  · exact B980287
  · exact B980291
  · exact B980295
  · exact B980299
  · exact B980303
  · exact B980307
  · exact B980311
  · exact B980315
  · exact B980319
  · exact B980323
  · exact B980327
  · exact B980331
  · exact B980335
  · exact B980339
  · exact B980343
  · exact B980347
  · exact B980351
  · exact B980355
  · exact B980359
  · exact B980363
  · exact B980367
  · exact B980371
  · exact B980375
  · exact B980379
  · exact B980383
  · exact B980387
  · exact B980391
  · exact B980395
  · exact B980399
  · exact B980403
  · exact B980407
  · exact B980411
  · exact B980415
  · exact B980419
  · exact B980423
  · exact B980427
  · exact B980431
  · exact B980435
  · exact B980439
  · exact B980443
  · exact B980447
  · exact B980451
  · exact B980455
  · exact B980459
  · exact B980463
  · exact B980467
  · exact B980471
  · exact B980475
  · exact B980479
  · exact B980483
  · exact B980487
  · exact B980491
  · exact B980495
  · exact B980499
  · exact B980503
  · exact B980507
  · exact B980511
  · exact B980515
  · exact B980519
  · exact B980523
  · exact B980527
  · exact B980531
  · exact B980535
  · exact B980539
  · exact B980543
  · exact B980547
  · exact B980551
  · exact B980555
  · exact B980559
  · exact B980563
  · exact B980567
  · exact B980571
  · exact B980575
  · exact B980579
  · exact B980583
  · exact B980587
  · exact B980591

theorem solution (m : ℕ) (hlo : 976593 ≤ m) (hhi : m ≤ 980593) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 244148 ≤ j := by omega
    have hj2 : j ≤ 245147 := by omega
    have hb : Blo 976593 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 244848 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
