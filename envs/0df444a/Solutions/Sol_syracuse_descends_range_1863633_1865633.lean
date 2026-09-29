-- Prove2me | solution 1 for syracuse_descends_range_1863633_1865633
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:11:34.383442+00:00
-- url     : https://prove2.me/submissions/7d8d3785-0e66-42de-a90a-a8132413abab

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


theorem B2359297 : Blo 1863633 2359297 := bbase (se 2 (by rfl) ⟨884736, by rfl⟩ : syracuseStep 2359297 = 1769473) (by norm_num)
theorem B2097157 : Blo 1863633 2097157 := bbase (se 4 (by rfl) ⟨196608, by rfl⟩ : syracuseStep 2097157 = 393217) (by norm_num)
theorem B2654221 : Blo 1863633 2654221 := bbase (se 3 (by rfl) ⟨497666, by rfl⟩ : syracuseStep 2654221 = 995333) (by norm_num)
theorem B28712981 : Blo 1863633 28712981 := bbase (se 6 (by rfl) ⟨672960, by rfl⟩ : syracuseStep 28712981 = 1345921) (by norm_num)
theorem B2154533 : Blo 1863633 2154533 := bbase (se 4 (by rfl) ⟨201987, by rfl⟩ : syracuseStep 2154533 = 403975) (by norm_num)
theorem B4194341 : Blo 1863633 4194341 := bbase (se 4 (by rfl) ⟨393219, by rfl⟩ : syracuseStep 4194341 = 786439) (by norm_num)
theorem B2097193 : Blo 1863633 2097193 := bbase (se 2 (by rfl) ⟨786447, by rfl⟩ : syracuseStep 2097193 = 1572895) (by norm_num)
theorem B4718645 : Blo 1863633 4718645 := bbase (se 5 (by rfl) ⟨221186, by rfl⟩ : syracuseStep 4718645 = 442373) (by norm_num)
theorem B2097229 : Blo 1863633 2097229 := bbase (se 3 (by rfl) ⟨393230, by rfl⟩ : syracuseStep 2097229 = 786461) (by norm_num)
theorem B3539045 : Blo 1863633 3539045 := bbase (se 4 (by rfl) ⟨331785, by rfl⟩ : syracuseStep 3539045 = 663571) (by norm_num)
theorem B4194413 : Blo 1863633 4194413 := bbase (se 3 (by rfl) ⟨786452, by rfl⟩ : syracuseStep 4194413 = 1572905) (by norm_num)
theorem B3145837 : Blo 1863633 3145837 := bbase (se 3 (by rfl) ⟨589844, by rfl⟩ : syracuseStep 3145837 = 1179689) (by norm_num)
theorem B2097265 : Blo 1863633 2097265 := bbase (se 2 (by rfl) ⟨786474, by rfl⟩ : syracuseStep 2097265 = 1572949) (by norm_num)
theorem B2097301 : Blo 1863633 2097301 := bbase (se 6 (by rfl) ⟨49155, by rfl⟩ : syracuseStep 2097301 = 98311) (by norm_num)
theorem B2359469 : Blo 1863633 2359469 := bbase (se 3 (by rfl) ⟨442400, by rfl⟩ : syracuseStep 2359469 = 884801) (by norm_num)
theorem B4194485 : Blo 1863633 4194485 := bbase (se 5 (by rfl) ⟨196616, by rfl⟩ : syracuseStep 4194485 = 393233) (by norm_num)
theorem B2097337 : Blo 1863633 2097337 := bbase (se 2 (by rfl) ⟨786501, by rfl⟩ : syracuseStep 2097337 = 1573003) (by norm_num)
theorem B3145925 : Blo 1863633 3145925 := bbase (se 4 (by rfl) ⟨294930, by rfl⟩ : syracuseStep 3145925 = 589861) (by norm_num)
theorem B3358925 : Blo 1863633 3358925 := bbase (se 3 (by rfl) ⟨629798, by rfl⟩ : syracuseStep 3358925 = 1259597) (by norm_num)
theorem B40337621 : Blo 1863633 40337621 := bbase (se 7 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 40337621 = 945413) (by norm_num)
theorem B2097373 : Blo 1863633 2097373 := bbase (se 3 (by rfl) ⟨393257, by rfl⟩ : syracuseStep 2097373 = 786515) (by norm_num)
theorem B2359525 : Blo 1863633 2359525 := bbase (se 4 (by rfl) ⟨221205, by rfl⟩ : syracuseStep 2359525 = 442411) (by norm_num)
theorem B6291701 : Blo 1863633 6291701 := bbase (se 5 (by rfl) ⟨294923, by rfl⟩ : syracuseStep 6291701 = 589847) (by norm_num)
theorem B4718837 : Blo 1863633 4718837 := bbase (se 5 (by rfl) ⟨221195, by rfl⟩ : syracuseStep 4718837 = 442391) (by norm_num)
theorem B3539189 : Blo 1863633 3539189 := bbase (se 5 (by rfl) ⟨165899, by rfl⟩ : syracuseStep 3539189 = 331799) (by norm_num)
theorem B2834677 : Blo 1863633 2834677 := bbase (se 5 (by rfl) ⟨132875, by rfl⟩ : syracuseStep 2834677 = 265751) (by norm_num)
theorem B4194557 : Blo 1863633 4194557 := bbase (se 3 (by rfl) ⟨786479, by rfl⟩ : syracuseStep 4194557 = 1572959) (by norm_num)
theorem B2097409 : Blo 1863633 2097409 := bbase (se 2 (by rfl) ⟨786528, by rfl⟩ : syracuseStep 2097409 = 1573057) (by norm_num)
theorem B4849949 : Blo 1863633 4849949 := bbase (se 3 (by rfl) ⟨909365, by rfl⟩ : syracuseStep 4849949 = 1818731) (by norm_num)
theorem B2097445 : Blo 1863633 2097445 := bbase (se 4 (by rfl) ⟨196635, by rfl⟩ : syracuseStep 2097445 = 393271) (by norm_num)
theorem B4784429 : Blo 1863633 4784429 := bbase (se 3 (by rfl) ⟨897080, by rfl⟩ : syracuseStep 4784429 = 1794161) (by norm_num)
theorem B4194629 : Blo 1863633 4194629 := bbase (se 4 (by rfl) ⟨393246, by rfl⟩ : syracuseStep 4194629 = 786493) (by norm_num)
theorem B3146053 : Blo 1863633 3146053 := bbase (se 4 (by rfl) ⟨294942, by rfl⟩ : syracuseStep 3146053 = 589885) (by norm_num)
theorem B2359621 : Blo 1863633 2359621 := bbase (se 4 (by rfl) ⟨221214, by rfl⟩ : syracuseStep 2359621 = 442429) (by norm_num)
theorem B2097481 : Blo 1863633 2097481 := bbase (se 2 (by rfl) ⟨786555, by rfl⟩ : syracuseStep 2097481 = 1573111) (by norm_num)
theorem B2097517 : Blo 1863633 2097517 := bbase (se 3 (by rfl) ⟨393284, by rfl⟩ : syracuseStep 2097517 = 786569) (by norm_num)
theorem B4194701 : Blo 1863633 4194701 := bbase (se 3 (by rfl) ⟨786506, by rfl⟩ : syracuseStep 4194701 = 1573013) (by norm_num)
theorem B2097553 : Blo 1863633 2097553 := bbase (se 2 (by rfl) ⟨786582, by rfl⟩ : syracuseStep 2097553 = 1573165) (by norm_num)
theorem B3146141 : Blo 1863633 3146141 := bbase (se 3 (by rfl) ⟨589901, by rfl⟩ : syracuseStep 3146141 = 1179803) (by norm_num)
theorem B1991089 : Blo 1863633 1991089 := bbase (se 2 (by rfl) ⟨746658, by rfl⟩ : syracuseStep 1991089 = 1493317) (by norm_num)
theorem B2097589 : Blo 1863633 2097589 := bbase (se 5 (by rfl) ⟨98324, by rfl⟩ : syracuseStep 2097589 = 196649) (by norm_num)
theorem B4194773 : Blo 1863633 4194773 := bbase (se 7 (by rfl) ⟨49157, by rfl⟩ : syracuseStep 4194773 = 98315) (by norm_num)
theorem B2097625 : Blo 1863633 2097625 := bbase (se 2 (by rfl) ⟨786609, by rfl⟩ : syracuseStep 2097625 = 1573219) (by norm_num)
theorem B2359793 : Blo 1863633 2359793 := bbase (se 2 (by rfl) ⟨884922, by rfl⟩ : syracuseStep 2359793 = 1769845) (by norm_num)
theorem B5669365 : Blo 1863633 5669365 := bbase (se 5 (by rfl) ⟨265751, by rfl⟩ : syracuseStep 5669365 = 531503) (by norm_num)
theorem B14164469 : Blo 1863633 14164469 := bbase (se 5 (by rfl) ⟨663959, by rfl⟩ : syracuseStep 14164469 = 1327919) (by norm_num)
theorem B1991161 : Blo 1863633 1991161 := bbase (se 2 (by rfl) ⟨746685, by rfl⟩ : syracuseStep 1991161 = 1493371) (by norm_num)
theorem B2097661 : Blo 1863633 2097661 := bbase (se 3 (by rfl) ⟨393311, by rfl⟩ : syracuseStep 2097661 = 786623) (by norm_num)
theorem B3539477 : Blo 1863633 3539477 := bbase (se 6 (by rfl) ⟨82956, by rfl⟩ : syracuseStep 3539477 = 165913) (by norm_num)
theorem B4194845 : Blo 1863633 4194845 := bbase (se 3 (by rfl) ⟨786533, by rfl⟩ : syracuseStep 4194845 = 1573067) (by norm_num)
theorem B4252189 : Blo 1863633 4252189 := bbase (se 3 (by rfl) ⟨797285, by rfl⟩ : syracuseStep 4252189 = 1594571) (by norm_num)
theorem B3146269 : Blo 1863633 3146269 := bbase (se 3 (by rfl) ⟨589925, by rfl⟩ : syracuseStep 3146269 = 1179851) (by norm_num)
theorem B2097697 : Blo 1863633 2097697 := bbase (se 2 (by rfl) ⟨786636, by rfl⟩ : syracuseStep 2097697 = 1573273) (by norm_num)
theorem B4481573 : Blo 1863633 4481573 := bbase (se 4 (by rfl) ⟨420147, by rfl⟩ : syracuseStep 4481573 = 840295) (by norm_num)
theorem B2359849 : Blo 1863633 2359849 := bbase (se 2 (by rfl) ⟨884943, by rfl⟩ : syracuseStep 2359849 = 1769887) (by norm_num)
theorem B8741429 : Blo 1863633 8741429 := bbase (se 5 (by rfl) ⟨409754, by rfl⟩ : syracuseStep 8741429 = 819509) (by norm_num)
theorem B2097733 : Blo 1863633 2097733 := bbase (se 4 (by rfl) ⟨196662, by rfl⟩ : syracuseStep 2097733 = 393325) (by norm_num)
theorem B4719181 : Blo 1863633 4719181 := bbase (se 3 (by rfl) ⟨884846, by rfl⟩ : syracuseStep 4719181 = 1769693) (by norm_num)
theorem B2654813 : Blo 1863633 2654813 := bbase (se 3 (by rfl) ⟨497777, by rfl⟩ : syracuseStep 2654813 = 995555) (by norm_num)
theorem B4194917 : Blo 1863633 4194917 := bbase (se 4 (by rfl) ⟨393273, by rfl⟩ : syracuseStep 4194917 = 786547) (by norm_num)
theorem B2097769 : Blo 1863633 2097769 := bbase (se 2 (by rfl) ⟨786663, by rfl⟩ : syracuseStep 2097769 = 1573327) (by norm_num)
theorem B2425457 : Blo 1863633 2425457 := bbase (se 2 (by rfl) ⟨909546, by rfl⟩ : syracuseStep 2425457 = 1819093) (by norm_num)
theorem B3146357 : Blo 1863633 3146357 := bbase (se 5 (by rfl) ⟨147485, by rfl⟩ : syracuseStep 3146357 = 294971) (by norm_num)
theorem B2359945 : Blo 1863633 2359945 := bbase (se 2 (by rfl) ⟨884979, by rfl⟩ : syracuseStep 2359945 = 1769959) (by norm_num)
theorem B2097805 : Blo 1863633 2097805 := bbase (se 3 (by rfl) ⟨393338, by rfl⟩ : syracuseStep 2097805 = 786677) (by norm_num)
theorem B3981973 : Blo 1863633 3981973 := bbase (se 6 (by rfl) ⟨93327, by rfl⟩ : syracuseStep 3981973 = 186655) (by norm_num)
theorem B6292133 : Blo 1863633 6292133 := bbase (se 4 (by rfl) ⟨589887, by rfl⟩ : syracuseStep 6292133 = 1179775) (by norm_num)
theorem B4194989 : Blo 1863633 4194989 := bbase (se 3 (by rfl) ⟨786560, by rfl⟩ : syracuseStep 4194989 = 1573121) (by norm_num)
theorem B3539629 : Blo 1863633 3539629 := bbase (se 3 (by rfl) ⟨663680, by rfl⟩ : syracuseStep 3539629 = 1327361) (by norm_num)
theorem B2654893 : Blo 1863633 2654893 := bbase (se 3 (by rfl) ⟨497792, by rfl⟩ : syracuseStep 2654893 = 995585) (by norm_num)
theorem B1991341 : Blo 1863633 1991341 := bbase (se 3 (by rfl) ⟨373376, by rfl⟩ : syracuseStep 1991341 = 746753) (by norm_num)
theorem B2097841 : Blo 1863633 2097841 := bbase (se 2 (by rfl) ⟨786690, by rfl⟩ : syracuseStep 2097841 = 1573381) (by norm_num)
theorem B4719293 : Blo 1863633 4719293 := bbase (se 3 (by rfl) ⟨884867, by rfl⟩ : syracuseStep 4719293 = 1769735) (by norm_num)
theorem B10076885 : Blo 1863633 10076885 := bbase (se 7 (by rfl) ⟨118088, by rfl⟩ : syracuseStep 10076885 = 236177) (by norm_num)
theorem B30646997 : Blo 1863633 30646997 := bbase (se 7 (by rfl) ⟨359144, by rfl⟩ : syracuseStep 30646997 = 718289) (by norm_num)
theorem B2097877 : Blo 1863633 2097877 := bbase (se 7 (by rfl) ⟨24584, by rfl⟩ : syracuseStep 2097877 = 49169) (by norm_num)
theorem B10085077 : Blo 1863633 10085077 := bbase (se 7 (by rfl) ⟨118184, by rfl⟩ : syracuseStep 10085077 = 236369) (by norm_num)
theorem B4195061 : Blo 1863633 4195061 := bbase (se 5 (by rfl) ⟨196643, by rfl⟩ : syracuseStep 4195061 = 393287) (by norm_num)
theorem B3146485 : Blo 1863633 3146485 := bbase (se 5 (by rfl) ⟨147491, by rfl⟩ : syracuseStep 3146485 = 294983) (by norm_num)
theorem B2097913 : Blo 1863633 2097913 := bbase (se 2 (by rfl) ⟨786717, by rfl⟩ : syracuseStep 2097913 = 1573435) (by norm_num)
theorem B9437957 : Blo 1863633 9437957 := bbase (se 4 (by rfl) ⟨884808, by rfl⟩ : syracuseStep 9437957 = 1769617) (by norm_num)
theorem B2097949 : Blo 1863633 2097949 := bbase (se 3 (by rfl) ⟨393365, by rfl⟩ : syracuseStep 2097949 = 786731) (by norm_num)
theorem B3982117 : Blo 1863633 3982117 := bbase (se 4 (by rfl) ⟨373323, by rfl⟩ : syracuseStep 3982117 = 746647) (by norm_num)
theorem B2655013 : Blo 1863633 2655013 := bbase (se 4 (by rfl) ⟨248907, by rfl⟩ : syracuseStep 2655013 = 497815) (by norm_num)
theorem B2360117 : Blo 1863633 2360117 := bbase (se 5 (by rfl) ⟨110630, by rfl⟩ : syracuseStep 2360117 = 221261) (by norm_num)
theorem B4195133 : Blo 1863633 4195133 := bbase (se 3 (by rfl) ⟨786587, by rfl⟩ : syracuseStep 4195133 = 1573175) (by norm_num)
theorem B2097985 : Blo 1863633 2097985 := bbase (se 2 (by rfl) ⟨786744, by rfl⟩ : syracuseStep 2097985 = 1573489) (by norm_num)
theorem B3146573 : Blo 1863633 3146573 := bbase (se 3 (by rfl) ⟨589982, by rfl⟩ : syracuseStep 3146573 = 1179965) (by norm_num)
theorem B2098021 : Blo 1863633 2098021 := bbase (se 4 (by rfl) ⟨196689, by rfl⟩ : syracuseStep 2098021 = 393379) (by norm_num)
theorem B2360173 : Blo 1863633 2360173 := bbase (se 3 (by rfl) ⟨442532, by rfl⟩ : syracuseStep 2360173 = 885065) (by norm_num)
theorem B4719485 : Blo 1863633 4719485 := bbase (se 3 (by rfl) ⟨884903, by rfl⟩ : syracuseStep 4719485 = 1769807) (by norm_num)
theorem B4195205 : Blo 1863633 4195205 := bbase (se 4 (by rfl) ⟨393300, by rfl⟩ : syracuseStep 4195205 = 786601) (by norm_num)
theorem B2655109 : Blo 1863633 2655109 := bbase (se 4 (by rfl) ⟨248916, by rfl⟩ : syracuseStep 2655109 = 497833) (by norm_num)
theorem B2098057 : Blo 1863633 2098057 := bbase (se 2 (by rfl) ⟨786771, by rfl⟩ : syracuseStep 2098057 = 1573543) (by norm_num)
theorem B14156693 : Blo 1863633 14156693 := bbase (se 6 (by rfl) ⟨331797, by rfl⟩ : syracuseStep 14156693 = 663595) (by norm_num)
theorem B10617749 : Blo 1863633 10617749 := bbase (se 6 (by rfl) ⟨248853, by rfl⟩ : syracuseStep 10617749 = 497707) (by norm_num)
theorem B2098093 : Blo 1863633 2098093 := bbase (se 3 (by rfl) ⟨393392, by rfl⟩ : syracuseStep 2098093 = 786785) (by norm_num)
theorem B4195277 : Blo 1863633 4195277 := bbase (se 3 (by rfl) ⟨786614, by rfl⟩ : syracuseStep 4195277 = 1573229) (by norm_num)
theorem B3146701 : Blo 1863633 3146701 := bbase (se 3 (by rfl) ⟨590006, by rfl⟩ : syracuseStep 3146701 = 1180013) (by norm_num)
theorem B2360269 : Blo 1863633 2360269 := bbase (se 3 (by rfl) ⟨442550, by rfl⟩ : syracuseStep 2360269 = 885101) (by norm_num)
theorem B2098129 : Blo 1863633 2098129 := bbase (se 2 (by rfl) ⟨786798, by rfl⟩ : syracuseStep 2098129 = 1573597) (by norm_num)
theorem B3539933 : Blo 1863633 3539933 := bbase (se 3 (by rfl) ⟨663737, by rfl⟩ : syracuseStep 3539933 = 1327475) (by norm_num)
theorem B2098165 : Blo 1863633 2098165 := bbase (se 5 (by rfl) ⟨98351, by rfl⟩ : syracuseStep 2098165 = 196703) (by norm_num)
theorem B2270225 : Blo 1863633 2270225 := bbase (se 2 (by rfl) ⟨851334, by rfl⟩ : syracuseStep 2270225 = 1702669) (by norm_num)
theorem B4195349 : Blo 1863633 4195349 := bbase (se 6 (by rfl) ⟨98328, by rfl⟩ : syracuseStep 4195349 = 196657) (by norm_num)
theorem B2098201 : Blo 1863633 2098201 := bbase (se 2 (by rfl) ⟨786825, by rfl⟩ : syracuseStep 2098201 = 1573651) (by norm_num)
theorem B3146789 : Blo 1863633 3146789 := bbase (se 4 (by rfl) ⟨295011, by rfl⟩ : syracuseStep 3146789 = 590023) (by norm_num)
theorem B2098237 : Blo 1863633 2098237 := bbase (se 3 (by rfl) ⟨393419, by rfl⟩ : syracuseStep 2098237 = 786839) (by norm_num)
theorem B6292565 : Blo 1863633 6292565 := bbase (se 8 (by rfl) ⟨36870, by rfl⟩ : syracuseStep 6292565 = 73741) (by norm_num)
theorem B4195421 : Blo 1863633 4195421 := bbase (se 3 (by rfl) ⟨786641, by rfl⟩ : syracuseStep 4195421 = 1573283) (by norm_num)
theorem B2098273 : Blo 1863633 2098273 := bbase (se 2 (by rfl) ⟨786852, by rfl⟩ : syracuseStep 2098273 = 1573705) (by norm_num)
theorem B1991785 : Blo 1863633 1991785 := bbase (se 2 (by rfl) ⟨746919, by rfl⟩ : syracuseStep 1991785 = 1493839) (by norm_num)
theorem B2360441 : Blo 1863633 2360441 := bbase (se 2 (by rfl) ⟨885165, by rfl⟩ : syracuseStep 2360441 = 1770331) (by norm_num)
theorem B2098309 : Blo 1863633 2098309 := bbase (se 4 (by rfl) ⟨196716, by rfl⟩ : syracuseStep 2098309 = 393433) (by norm_num)
theorem B3982493 : Blo 1863633 3982493 := bbase (se 3 (by rfl) ⟨746717, by rfl⟩ : syracuseStep 3982493 = 1493435) (by norm_num)
theorem B4195493 : Blo 1863633 4195493 := bbase (se 4 (by rfl) ⟨393327, by rfl⟩ : syracuseStep 4195493 = 786655) (by norm_num)
theorem B3146917 : Blo 1863633 3146917 := bbase (se 4 (by rfl) ⟨295023, by rfl⟩ : syracuseStep 3146917 = 590047) (by norm_num)
theorem B2098345 : Blo 1863633 2098345 := bbase (se 2 (by rfl) ⟨786879, by rfl⟩ : syracuseStep 2098345 = 1573759) (by norm_num)
theorem B2360497 : Blo 1863633 2360497 := bbase (se 2 (by rfl) ⟨885186, by rfl⟩ : syracuseStep 2360497 = 1770373) (by norm_num)
theorem B4310221 : Blo 1863633 4310221 := bbase (se 3 (by rfl) ⟨808166, by rfl⟩ : syracuseStep 4310221 = 1616333) (by norm_num)
theorem B2098381 : Blo 1863633 2098381 := bbase (se 3 (by rfl) ⟨393446, by rfl⟩ : syracuseStep 2098381 = 786893) (by norm_num)
theorem B4719829 : Blo 1863633 4719829 := bbase (se 7 (by rfl) ⟨55310, by rfl⟩ : syracuseStep 4719829 = 110621) (by norm_num)
theorem B1991909 : Blo 1863633 1991909 := bbase (se 4 (by rfl) ⟨186741, by rfl⟩ : syracuseStep 1991909 = 373483) (by norm_num)
theorem B4195565 : Blo 1863633 4195565 := bbase (se 3 (by rfl) ⟨786668, by rfl⟩ : syracuseStep 4195565 = 1573337) (by norm_num)
theorem B2098417 : Blo 1863633 2098417 := bbase (se 2 (by rfl) ⟨786906, by rfl⟩ : syracuseStep 2098417 = 1573813) (by norm_num)
theorem B3147005 : Blo 1863633 3147005 := bbase (se 3 (by rfl) ⟨590063, by rfl⟩ : syracuseStep 3147005 = 1180127) (by norm_num)
theorem B2360593 : Blo 1863633 2360593 := bbase (se 2 (by rfl) ⟨885222, by rfl⟩ : syracuseStep 2360593 = 1770445) (by norm_num)
theorem B2098453 : Blo 1863633 2098453 := bbase (se 6 (by rfl) ⟨49182, by rfl⟩ : syracuseStep 2098453 = 98365) (by norm_num)
theorem B4195637 : Blo 1863633 4195637 := bbase (se 5 (by rfl) ⟨196670, by rfl⟩ : syracuseStep 4195637 = 393341) (by norm_num)
theorem B2098489 : Blo 1863633 2098489 := bbase (se 2 (by rfl) ⟨786933, by rfl⟩ : syracuseStep 2098489 = 1573867) (by norm_num)
theorem B4719941 : Blo 1863633 4719941 := bbase (se 4 (by rfl) ⟨442494, by rfl⟩ : syracuseStep 4719941 = 884989) (by norm_num)
theorem B2098525 : Blo 1863633 2098525 := bbase (se 3 (by rfl) ⟨393473, by rfl⟩ : syracuseStep 2098525 = 786947) (by norm_num)
theorem B2655605 : Blo 1863633 2655605 := bbase (se 5 (by rfl) ⟨124481, by rfl⟩ : syracuseStep 2655605 = 248963) (by norm_num)
theorem B4195709 : Blo 1863633 4195709 := bbase (se 3 (by rfl) ⟨786695, by rfl⟩ : syracuseStep 4195709 = 1573391) (by norm_num)
theorem B3147133 : Blo 1863633 3147133 := bbase (se 3 (by rfl) ⟨590087, by rfl⟩ : syracuseStep 3147133 = 1180175) (by norm_num)
theorem B2098561 : Blo 1863633 2098561 := bbase (se 2 (by rfl) ⟨786960, by rfl⟩ : syracuseStep 2098561 = 1573921) (by norm_num)
theorem B2098597 : Blo 1863633 2098597 := bbase (se 4 (by rfl) ⟨196743, by rfl⟩ : syracuseStep 2098597 = 393487) (by norm_num)
theorem B2360765 : Blo 1863633 2360765 := bbase (se 3 (by rfl) ⟨442643, by rfl⟩ : syracuseStep 2360765 = 885287) (by norm_num)
theorem B4195781 : Blo 1863633 4195781 := bbase (se 4 (by rfl) ⟨393354, by rfl⟩ : syracuseStep 4195781 = 786709) (by norm_num)
theorem B2098633 : Blo 1863633 2098633 := bbase (se 2 (by rfl) ⟨786987, by rfl⟩ : syracuseStep 2098633 = 1573975) (by norm_num)
theorem B3147221 : Blo 1863633 3147221 := bbase (se 7 (by rfl) ⟨36881, by rfl⟩ : syracuseStep 3147221 = 73763) (by norm_num)
theorem B1992161 : Blo 1863633 1992161 := bbase (se 2 (by rfl) ⟨747060, by rfl⟩ : syracuseStep 1992161 = 1494121) (by norm_num)
theorem B2098669 : Blo 1863633 2098669 := bbase (se 3 (by rfl) ⟨393500, by rfl⟩ : syracuseStep 2098669 = 787001) (by norm_num)
theorem B2360821 : Blo 1863633 2360821 := bbase (se 5 (by rfl) ⟨110663, by rfl⟩ : syracuseStep 2360821 = 221327) (by norm_num)
theorem B6292997 : Blo 1863633 6292997 := bbase (se 4 (by rfl) ⟨589968, by rfl⟩ : syracuseStep 6292997 = 1179937) (by norm_num)
theorem B4720133 : Blo 1863633 4720133 := bbase (se 4 (by rfl) ⟨442512, by rfl⟩ : syracuseStep 4720133 = 885025) (by norm_num)
theorem B4195853 : Blo 1863633 4195853 := bbase (se 3 (by rfl) ⟨786722, by rfl⟩ : syracuseStep 4195853 = 1573445) (by norm_num)
theorem B3982861 : Blo 1863633 3982861 := bbase (se 3 (by rfl) ⟨746786, by rfl⟩ : syracuseStep 3982861 = 1493573) (by norm_num)
theorem B2098705 : Blo 1863633 2098705 := bbase (se 2 (by rfl) ⟨787014, by rfl⟩ : syracuseStep 2098705 = 1574029) (by norm_num)
theorem B2098741 : Blo 1863633 2098741 := bbase (se 5 (by rfl) ⟨98378, by rfl⟩ : syracuseStep 2098741 = 196757) (by norm_num)
theorem B4195925 : Blo 1863633 4195925 := bbase (se 8 (by rfl) ⟨24585, by rfl⟩ : syracuseStep 4195925 = 49171) (by norm_num)
theorem B3147349 : Blo 1863633 3147349 := bbase (se 8 (by rfl) ⟨18441, by rfl⟩ : syracuseStep 3147349 = 36883) (by norm_num)
theorem B2360917 : Blo 1863633 2360917 := bbase (se 8 (by rfl) ⟨13833, by rfl⟩ : syracuseStep 2360917 = 27667) (by norm_num)
theorem B15754837 : Blo 1863633 15754837 := bbase (se 8 (by rfl) ⟨92313, by rfl⟩ : syracuseStep 15754837 = 184627) (by norm_num)
theorem B2098777 : Blo 1863633 2098777 := bbase (se 2 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 2098777 = 1574083) (by norm_num)
theorem B3884645 : Blo 1863633 3884645 := bbase (se 4 (by rfl) ⟨364185, by rfl⟩ : syracuseStep 3884645 = 728371) (by norm_num)
theorem B2098813 : Blo 1863633 2098813 := bbase (se 3 (by rfl) ⟨393527, by rfl⟩ : syracuseStep 2098813 = 787055) (by norm_num)
theorem B5670533 : Blo 1863633 5670533 := bbase (se 4 (by rfl) ⟨531612, by rfl⟩ : syracuseStep 5670533 = 1063225) (by norm_num)
theorem B4368013 : Blo 1863633 4368013 := bbase (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) (by norm_num)
theorem B4195997 : Blo 1863633 4195997 := bbase (se 3 (by rfl) ⟨786749, by rfl⟩ : syracuseStep 4195997 = 1573499) (by norm_num)
theorem B4253357 : Blo 1863633 4253357 := bbase (se 3 (by rfl) ⟨797504, by rfl⟩ : syracuseStep 4253357 = 1595009) (by norm_num)
theorem B3147437 : Blo 1863633 3147437 := bbase (se 3 (by rfl) ⟨590144, by rfl⟩ : syracuseStep 3147437 = 1180289) (by norm_num)
theorem B3540685 : Blo 1863633 3540685 := bbase (se 3 (by rfl) ⟨663878, by rfl⟩ : syracuseStep 3540685 = 1327757) (by norm_num)
theorem B4196069 : Blo 1863633 4196069 := bbase (se 4 (by rfl) ⟨393381, by rfl⟩ : syracuseStep 4196069 = 786763) (by norm_num)
theorem B7079669 : Blo 1863633 7079669 := bbase (se 5 (by rfl) ⟨331859, by rfl⟩ : syracuseStep 7079669 = 663719) (by norm_num)
theorem B2361089 : Blo 1863633 2361089 := bbase (se 2 (by rfl) ⟨885408, by rfl⟩ : syracuseStep 2361089 = 1770817) (by norm_num)
theorem B4196141 : Blo 1863633 4196141 := bbase (se 3 (by rfl) ⟨786776, by rfl⟩ : syracuseStep 4196141 = 1573553) (by norm_num)
theorem B3147565 : Blo 1863633 3147565 := bbase (se 3 (by rfl) ⟨590168, by rfl⟩ : syracuseStep 3147565 = 1180337) (by norm_num)
theorem B2361145 : Blo 1863633 2361145 := bbase (se 2 (by rfl) ⟨885429, by rfl⟩ : syracuseStep 2361145 = 1770859) (by norm_num)
theorem B4720477 : Blo 1863633 4720477 := bbase (se 3 (by rfl) ⟨885089, by rfl⟩ : syracuseStep 4720477 = 1770179) (by norm_num)
theorem B3540829 : Blo 1863633 3540829 := bbase (se 3 (by rfl) ⟨663905, by rfl⟩ : syracuseStep 3540829 = 1327811) (by norm_num)
theorem B4196213 : Blo 1863633 4196213 := bbase (se 5 (by rfl) ⟨196697, by rfl⟩ : syracuseStep 4196213 = 393395) (by norm_num)
theorem B3147653 : Blo 1863633 3147653 := bbase (se 4 (by rfl) ⟨295092, by rfl⟩ : syracuseStep 3147653 = 590185) (by norm_num)
theorem B2656157 : Blo 1863633 2656157 := bbase (se 3 (by rfl) ⟨498029, by rfl⟩ : syracuseStep 2656157 = 996059) (by norm_num)
theorem B6293429 : Blo 1863633 6293429 := bbase (se 5 (by rfl) ⟨295004, by rfl⟩ : syracuseStep 6293429 = 590009) (by norm_num)
theorem B2795453 : Blo 1863633 2795453 := bbase (se 3 (by rfl) ⟨524147, by rfl⟩ : syracuseStep 2795453 = 1048295) (by norm_num)
theorem B4196285 : Blo 1863633 4196285 := bbase (se 3 (by rfl) ⟨786803, by rfl⟩ : syracuseStep 4196285 = 1573607) (by norm_num)
theorem B4720589 : Blo 1863633 4720589 := bbase (se 3 (by rfl) ⟨885110, by rfl⟩ : syracuseStep 4720589 = 1770221) (by norm_num)
theorem B2795477 : Blo 1863633 2795477 := bbase (se 7 (by rfl) ⟨32759, by rfl⟩ : syracuseStep 2795477 = 65519) (by norm_num)
theorem B2795501 : Blo 1863633 2795501 := bbase (se 3 (by rfl) ⟨524156, by rfl⟩ : syracuseStep 2795501 = 1048313) (by norm_num)
theorem B3540989 : Blo 1863633 3540989 := bbase (se 3 (by rfl) ⟨663935, by rfl⟩ : syracuseStep 3540989 = 1327871) (by norm_num)
theorem B2795525 : Blo 1863633 2795525 := bbase (se 4 (by rfl) ⟨262080, by rfl⟩ : syracuseStep 2795525 = 524161) (by norm_num)
theorem B4196357 : Blo 1863633 4196357 := bbase (se 4 (by rfl) ⟨393408, by rfl⟩ : syracuseStep 4196357 = 786817) (by norm_num)
theorem B3147781 : Blo 1863633 3147781 := bbase (se 4 (by rfl) ⟨295104, by rfl⟩ : syracuseStep 3147781 = 590209) (by norm_num)
theorem B9439253 : Blo 1863633 9439253 := bbase (se 6 (by rfl) ⟨221232, by rfl⟩ : syracuseStep 9439253 = 442465) (by norm_num)
theorem B7079957 : Blo 1863633 7079957 := bbase (se 6 (by rfl) ⟨165936, by rfl⟩ : syracuseStep 7079957 = 331873) (by norm_num)
theorem B2795549 : Blo 1863633 2795549 := bbase (se 3 (by rfl) ⟨524165, by rfl⟩ : syracuseStep 2795549 = 1048331) (by norm_num)
theorem B2795573 : Blo 1863633 2795573 := bbase (se 5 (by rfl) ⟨131042, by rfl⟩ : syracuseStep 2795573 = 262085) (by norm_num)
theorem B2795597 : Blo 1863633 2795597 := bbase (se 3 (by rfl) ⟨524174, by rfl⟩ : syracuseStep 2795597 = 1048349) (by norm_num)
theorem B4196429 : Blo 1863633 4196429 := bbase (se 3 (by rfl) ⟨786830, by rfl⟩ : syracuseStep 4196429 = 1573661) (by norm_num)
theorem B108980309 : Blo 1863633 108980309 := bbase (se 8 (by rfl) ⟨638556, by rfl⟩ : syracuseStep 108980309 = 1277113) (by norm_num)
theorem B3147869 : Blo 1863633 3147869 := bbase (se 3 (by rfl) ⟨590225, by rfl⟩ : syracuseStep 3147869 = 1180451) (by norm_num)
theorem B2795621 : Blo 1863633 2795621 := bbase (se 4 (by rfl) ⟨262089, by rfl⟩ : syracuseStep 2795621 = 524179) (by norm_num)
theorem B2795645 : Blo 1863633 2795645 := bbase (se 3 (by rfl) ⟨524183, by rfl⟩ : syracuseStep 2795645 = 1048367) (by norm_num)
theorem B4720781 : Blo 1863633 4720781 := bbase (se 3 (by rfl) ⟨885146, by rfl⟩ : syracuseStep 4720781 = 1770293) (by norm_num)
theorem B3541133 : Blo 1863633 3541133 := bbase (se 3 (by rfl) ⟨663962, by rfl⟩ : syracuseStep 3541133 = 1327925) (by norm_num)
theorem B2795669 : Blo 1863633 2795669 := bbase (se 6 (by rfl) ⟨65523, by rfl⟩ : syracuseStep 2795669 = 131047) (by norm_num)
theorem B4196501 : Blo 1863633 4196501 := bbase (se 6 (by rfl) ⟨98355, by rfl⟩ : syracuseStep 4196501 = 196711) (by norm_num)
theorem B2017445 : Blo 1863633 2017445 := bbase (se 4 (by rfl) ⟨189135, by rfl⟩ : syracuseStep 2017445 = 378271) (by norm_num)
theorem B5310629 : Blo 1863633 5310629 := bbase (se 4 (by rfl) ⟨497871, by rfl⟩ : syracuseStep 5310629 = 995743) (by norm_num)
theorem B2795693 : Blo 1863633 2795693 := bbase (se 3 (by rfl) ⟨524192, by rfl⟩ : syracuseStep 2795693 = 1048385) (by norm_num)
theorem B2795717 : Blo 1863633 2795717 := bbase (se 4 (by rfl) ⟨262098, by rfl⟩ : syracuseStep 2795717 = 524197) (by norm_num)
theorem B2795741 : Blo 1863633 2795741 := bbase (se 3 (by rfl) ⟨524201, by rfl⟩ : syracuseStep 2795741 = 1048403) (by norm_num)
theorem B4196573 : Blo 1863633 4196573 := bbase (se 3 (by rfl) ⟨786857, by rfl⟩ : syracuseStep 4196573 = 1573715) (by norm_num)
theorem B3147997 : Blo 1863633 3147997 := bbase (se 3 (by rfl) ⟨590249, by rfl⟩ : syracuseStep 3147997 = 1180499) (by norm_num)
theorem B2795765 : Blo 1863633 2795765 := bbase (se 5 (by rfl) ⟨131051, by rfl⟩ : syracuseStep 2795765 = 262103) (by norm_num)
theorem B2795789 : Blo 1863633 2795789 := bbase (se 3 (by rfl) ⟨524210, by rfl⟩ : syracuseStep 2795789 = 1048421) (by norm_num)
theorem B2795813 : Blo 1863633 2795813 := bbase (se 4 (by rfl) ⟨262107, by rfl⟩ : syracuseStep 2795813 = 524215) (by norm_num)
theorem B4196645 : Blo 1863633 4196645 := bbase (se 4 (by rfl) ⟨393435, by rfl⟩ : syracuseStep 4196645 = 786871) (by norm_num)
theorem B3148085 : Blo 1863633 3148085 := bbase (se 5 (by rfl) ⟨147566, by rfl⟩ : syracuseStep 3148085 = 295133) (by norm_num)
theorem B2795837 : Blo 1863633 2795837 := bbase (se 3 (by rfl) ⟨524219, by rfl⟩ : syracuseStep 2795837 = 1048439) (by norm_num)
theorem B2795861 : Blo 1863633 2795861 := bbase (se 10 (by rfl) ⟨4095, by rfl⟩ : syracuseStep 2795861 = 8191) (by norm_num)
theorem B6293861 : Blo 1863633 6293861 := bbase (se 4 (by rfl) ⟨590049, by rfl⟩ : syracuseStep 6293861 = 1180099) (by norm_num)
theorem B2795885 : Blo 1863633 2795885 := bbase (se 3 (by rfl) ⟨524228, by rfl⟩ : syracuseStep 2795885 = 1048457) (by norm_num)
theorem B4196717 : Blo 1863633 4196717 := bbase (se 3 (by rfl) ⟨786884, by rfl⟩ : syracuseStep 4196717 = 1573769) (by norm_num)
theorem B2795909 : Blo 1863633 2795909 := bbase (se 4 (by rfl) ⟨262116, by rfl⟩ : syracuseStep 2795909 = 524233) (by norm_num)
theorem B10078613 : Blo 1863633 10078613 := bbase (se 6 (by rfl) ⟨236217, by rfl⟩ : syracuseStep 10078613 = 472435) (by norm_num)
theorem B2795933 : Blo 1863633 2795933 := bbase (se 3 (by rfl) ⟨524237, by rfl⟩ : syracuseStep 2795933 = 1048475) (by norm_num)
theorem B3541421 : Blo 1863633 3541421 := bbase (se 3 (by rfl) ⟨664016, by rfl⟩ : syracuseStep 3541421 = 1328033) (by norm_num)
theorem B2795957 : Blo 1863633 2795957 := bbase (se 5 (by rfl) ⟨131060, by rfl⟩ : syracuseStep 2795957 = 262121) (by norm_num)
theorem B4196789 : Blo 1863633 4196789 := bbase (se 5 (by rfl) ⟨196724, by rfl⟩ : syracuseStep 4196789 = 393449) (by norm_num)
theorem B3148213 : Blo 1863633 3148213 := bbase (se 5 (by rfl) ⟨147572, by rfl⟩ : syracuseStep 3148213 = 295145) (by norm_num)
theorem B2795981 : Blo 1863633 2795981 := bbase (se 3 (by rfl) ⟨524246, by rfl⟩ : syracuseStep 2795981 = 1048493) (by norm_num)
theorem B2796005 : Blo 1863633 2796005 := bbase (se 4 (by rfl) ⟨262125, by rfl⟩ : syracuseStep 2796005 = 524251) (by norm_num)
theorem B4721125 : Blo 1863633 4721125 := bbase (se 4 (by rfl) ⟨442605, by rfl⟩ : syracuseStep 4721125 = 885211) (by norm_num)
theorem B2796029 : Blo 1863633 2796029 := bbase (se 3 (by rfl) ⟨524255, by rfl⟩ : syracuseStep 2796029 = 1048511) (by norm_num)
theorem B4196861 : Blo 1863633 4196861 := bbase (se 3 (by rfl) ⟨786911, by rfl⟩ : syracuseStep 4196861 = 1573823) (by norm_num)
theorem B2796053 : Blo 1863633 2796053 := bbase (se 6 (by rfl) ⟨65532, by rfl⟩ : syracuseStep 2796053 = 131065) (by norm_num)
theorem B2796077 : Blo 1863633 2796077 := bbase (se 3 (by rfl) ⟨524264, by rfl⟩ : syracuseStep 2796077 = 1048529) (by norm_num)
theorem B2796101 : Blo 1863633 2796101 := bbase (se 4 (by rfl) ⟨262134, by rfl⟩ : syracuseStep 2796101 = 524269) (by norm_num)
theorem B4196933 : Blo 1863633 4196933 := bbase (se 4 (by rfl) ⟨393462, by rfl⟩ : syracuseStep 4196933 = 786925) (by norm_num)
theorem B3541573 : Blo 1863633 3541573 := bbase (se 4 (by rfl) ⟨332022, by rfl⟩ : syracuseStep 3541573 = 664045) (by norm_num)
theorem B4721237 : Blo 1863633 4721237 := bbase (se 8 (by rfl) ⟨27663, by rfl⟩ : syracuseStep 4721237 = 55327) (by norm_num)
theorem B2796125 : Blo 1863633 2796125 := bbase (se 3 (by rfl) ⟨524273, by rfl⟩ : syracuseStep 2796125 = 1048547) (by norm_num)
theorem B2796149 : Blo 1863633 2796149 := bbase (se 5 (by rfl) ⟨131069, by rfl⟩ : syracuseStep 2796149 = 262139) (by norm_num)
theorem B2796173 : Blo 1863633 2796173 := bbase (se 3 (by rfl) ⟨524282, by rfl⟩ : syracuseStep 2796173 = 1048565) (by norm_num)
theorem B4197005 : Blo 1863633 4197005 := bbase (se 3 (by rfl) ⟨786938, by rfl⟩ : syracuseStep 4197005 = 1573877) (by norm_num)
theorem B2796197 : Blo 1863633 2796197 := bbase (se 4 (by rfl) ⟨262143, by rfl⟩ : syracuseStep 2796197 = 524287) (by norm_num)
theorem B2796221 : Blo 1863633 2796221 := bbase (se 3 (by rfl) ⟨524291, by rfl⟩ : syracuseStep 2796221 = 1048583) (by norm_num)
theorem B2796245 : Blo 1863633 2796245 := bbase (se 7 (by rfl) ⟨32768, by rfl⟩ : syracuseStep 2796245 = 65537) (by norm_num)
theorem B4197077 : Blo 1863633 4197077 := bbase (se 7 (by rfl) ⟨49184, by rfl⟩ : syracuseStep 4197077 = 98369) (by norm_num)
theorem B2796269 : Blo 1863633 2796269 := bbase (se 3 (by rfl) ⟨524300, by rfl⟩ : syracuseStep 2796269 = 1048601) (by norm_num)
theorem B2796293 : Blo 1863633 2796293 := bbase (se 4 (by rfl) ⟨262152, by rfl⟩ : syracuseStep 2796293 = 524305) (by norm_num)
theorem B2239249 : Blo 1863633 2239249 := bbase (se 2 (by rfl) ⟨839718, by rfl⟩ : syracuseStep 2239249 = 1679437) (by norm_num)
theorem B6294293 : Blo 1863633 6294293 := bbase (se 6 (by rfl) ⟨147522, by rfl⟩ : syracuseStep 6294293 = 295045) (by norm_num)
theorem B4721429 : Blo 1863633 4721429 := bbase (se 6 (by rfl) ⟨110658, by rfl⟩ : syracuseStep 4721429 = 221317) (by norm_num)
theorem B2796317 : Blo 1863633 2796317 := bbase (se 3 (by rfl) ⟨524309, by rfl⟩ : syracuseStep 2796317 = 1048619) (by norm_num)
theorem B4197149 : Blo 1863633 4197149 := bbase (se 3 (by rfl) ⟨786965, by rfl⟩ : syracuseStep 4197149 = 1573931) (by norm_num)
theorem B2796341 : Blo 1863633 2796341 := bbase (se 5 (by rfl) ⟨131078, by rfl⟩ : syracuseStep 2796341 = 262157) (by norm_num)
theorem B8964917 : Blo 1863633 8964917 := bbase (se 5 (by rfl) ⟨420230, by rfl⟩ : syracuseStep 8964917 = 840461) (by norm_num)
theorem B2796365 : Blo 1863633 2796365 := bbase (se 3 (by rfl) ⟨524318, by rfl⟩ : syracuseStep 2796365 = 1048637) (by norm_num)
theorem B2796389 : Blo 1863633 2796389 := bbase (se 4 (by rfl) ⟨262161, by rfl⟩ : syracuseStep 2796389 = 524323) (by norm_num)
theorem B4197221 : Blo 1863633 4197221 := bbase (se 4 (by rfl) ⟨393489, by rfl⟩ : syracuseStep 4197221 = 786979) (by norm_num)
theorem B2796413 : Blo 1863633 2796413 := bbase (se 3 (by rfl) ⟨524327, by rfl⟩ : syracuseStep 2796413 = 1048655) (by norm_num)
theorem B2796437 : Blo 1863633 2796437 := bbase (se 6 (by rfl) ⟨65541, by rfl⟩ : syracuseStep 2796437 = 131083) (by norm_num)
theorem B2796461 : Blo 1863633 2796461 := bbase (se 3 (by rfl) ⟨524336, by rfl⟩ : syracuseStep 2796461 = 1048673) (by norm_num)
theorem B4197293 : Blo 1863633 4197293 := bbase (se 3 (by rfl) ⟨786992, by rfl⟩ : syracuseStep 4197293 = 1573985) (by norm_num)
theorem B2796485 : Blo 1863633 2796485 := bbase (se 4 (by rfl) ⟨262170, by rfl⟩ : syracuseStep 2796485 = 524341) (by norm_num)
theorem B2796509 : Blo 1863633 2796509 := bbase (se 3 (by rfl) ⟨524345, by rfl⟩ : syracuseStep 2796509 = 1048691) (by norm_num)
theorem B3984365 : Blo 1863633 3984365 := bbase (se 3 (by rfl) ⟨747068, by rfl⟩ : syracuseStep 3984365 = 1494137) (by norm_num)
theorem B13618165 : Blo 1863633 13618165 := bbase (se 5 (by rfl) ⟨638351, by rfl⟩ : syracuseStep 13618165 = 1276703) (by norm_num)
theorem B2796533 : Blo 1863633 2796533 := bbase (se 5 (by rfl) ⟨131087, by rfl⟩ : syracuseStep 2796533 = 262175) (by norm_num)
theorem B4197365 : Blo 1863633 4197365 := bbase (se 5 (by rfl) ⟨196751, by rfl⟩ : syracuseStep 4197365 = 393503) (by norm_num)
theorem B2796557 : Blo 1863633 2796557 := bbase (se 3 (by rfl) ⟨524354, by rfl⟩ : syracuseStep 2796557 = 1048709) (by norm_num)
theorem B15936533 : Blo 1863633 15936533 := bbase (se 6 (by rfl) ⟨373512, by rfl⟩ : syracuseStep 15936533 = 747025) (by norm_num)
theorem B2796581 : Blo 1863633 2796581 := bbase (se 4 (by rfl) ⟨262179, by rfl⟩ : syracuseStep 2796581 = 524359) (by norm_num)
theorem B3361829 : Blo 1863633 3361829 := bbase (se 4 (by rfl) ⟨315171, by rfl⟩ : syracuseStep 3361829 = 630343) (by norm_num)
theorem B2796605 : Blo 1863633 2796605 := bbase (se 3 (by rfl) ⟨524363, by rfl⟩ : syracuseStep 2796605 = 1048727) (by norm_num)
theorem B4197437 : Blo 1863633 4197437 := bbase (se 3 (by rfl) ⟨787019, by rfl⟩ : syracuseStep 4197437 = 1574039) (by norm_num)
theorem B2796629 : Blo 1863633 2796629 := bbase (se 8 (by rfl) ⟨16386, by rfl⟩ : syracuseStep 2796629 = 32773) (by norm_num)
theorem B2796653 : Blo 1863633 2796653 := bbase (se 3 (by rfl) ⟨524372, by rfl⟩ : syracuseStep 2796653 = 1048745) (by norm_num)
theorem B4721773 : Blo 1863633 4721773 := bbase (se 3 (by rfl) ⟨885332, by rfl⟩ : syracuseStep 4721773 = 1770665) (by norm_num)
theorem B3984509 : Blo 1863633 3984509 := bbase (se 3 (by rfl) ⟨747095, by rfl⟩ : syracuseStep 3984509 = 1494191) (by norm_num)
theorem B2796677 : Blo 1863633 2796677 := bbase (se 4 (by rfl) ⟨262188, by rfl⟩ : syracuseStep 2796677 = 524377) (by norm_num)
theorem B4197509 : Blo 1863633 4197509 := bbase (se 4 (by rfl) ⟨393516, by rfl⟩ : syracuseStep 4197509 = 787033) (by norm_num)
theorem B2796701 : Blo 1863633 2796701 := bbase (se 3 (by rfl) ⟨524381, by rfl⟩ : syracuseStep 2796701 = 1048763) (by norm_num)
theorem B2796725 : Blo 1863633 2796725 := bbase (se 5 (by rfl) ⟨131096, by rfl⟩ : syracuseStep 2796725 = 262193) (by norm_num)
theorem B7081141 : Blo 1863633 7081141 := bbase (se 5 (by rfl) ⟨331928, by rfl⟩ : syracuseStep 7081141 = 663857) (by norm_num)
theorem B6294725 : Blo 1863633 6294725 := bbase (se 4 (by rfl) ⟨590130, by rfl⟩ : syracuseStep 6294725 = 1180261) (by norm_num)
theorem B2796749 : Blo 1863633 2796749 := bbase (se 3 (by rfl) ⟨524390, by rfl⟩ : syracuseStep 2796749 = 1048781) (by norm_num)
theorem B4197581 : Blo 1863633 4197581 := bbase (se 3 (by rfl) ⟨787046, by rfl⟩ : syracuseStep 4197581 = 1574093) (by norm_num)
theorem B4721885 : Blo 1863633 4721885 := bbase (se 3 (by rfl) ⟨885353, by rfl⟩ : syracuseStep 4721885 = 1770707) (by norm_num)
theorem B2796773 : Blo 1863633 2796773 := bbase (se 4 (by rfl) ⟨262197, by rfl⟩ : syracuseStep 2796773 = 524395) (by norm_num)
theorem B2796797 : Blo 1863633 2796797 := bbase (se 3 (by rfl) ⟨524399, by rfl⟩ : syracuseStep 2796797 = 1048799) (by norm_num)
theorem B2796821 : Blo 1863633 2796821 := bbase (se 6 (by rfl) ⟨65550, by rfl⟩ : syracuseStep 2796821 = 131101) (by norm_num)
theorem B4197653 : Blo 1863633 4197653 := bbase (se 6 (by rfl) ⟨98382, by rfl⟩ : syracuseStep 4197653 = 196765) (by norm_num)
theorem B9440549 : Blo 1863633 9440549 := bbase (se 4 (by rfl) ⟨885051, by rfl⟩ : syracuseStep 9440549 = 1770103) (by norm_num)
theorem B2796845 : Blo 1863633 2796845 := bbase (se 3 (by rfl) ⟨524408, by rfl⟩ : syracuseStep 2796845 = 1048817) (by norm_num)
theorem B2018605 : Blo 1863633 2018605 := bbase (se 3 (by rfl) ⟨378488, by rfl⟩ : syracuseStep 2018605 = 756977) (by norm_num)
theorem B13438261 : Blo 1863633 13438261 := bbase (se 5 (by rfl) ⟨629918, by rfl⟩ : syracuseStep 13438261 = 1259837) (by norm_num)
theorem B2796869 : Blo 1863633 2796869 := bbase (se 4 (by rfl) ⟨262206, by rfl⟩ : syracuseStep 2796869 = 524413) (by norm_num)
theorem B5311813 : Blo 1863633 5311813 := bbase (se 4 (by rfl) ⟨497982, by rfl⟩ : syracuseStep 5311813 = 995965) (by norm_num)
theorem B2796893 : Blo 1863633 2796893 := bbase (se 3 (by rfl) ⟨524417, by rfl⟩ : syracuseStep 2796893 = 1048835) (by norm_num)
theorem B2796917 : Blo 1863633 2796917 := bbase (se 5 (by rfl) ⟨131105, by rfl⟩ : syracuseStep 2796917 = 262211) (by norm_num)
theorem B2796941 : Blo 1863633 2796941 := bbase (se 3 (by rfl) ⟨524426, by rfl⟩ : syracuseStep 2796941 = 1048853) (by norm_num)
theorem B4722077 : Blo 1863633 4722077 := bbase (se 3 (by rfl) ⟨885389, by rfl⟩ : syracuseStep 4722077 = 1770779) (by norm_num)
theorem B2796965 : Blo 1863633 2796965 := bbase (se 4 (by rfl) ⟨262215, by rfl⟩ : syracuseStep 2796965 = 524431) (by norm_num)
theorem B7966133 : Blo 1863633 7966133 := bbase (se 5 (by rfl) ⟨373412, by rfl⟩ : syracuseStep 7966133 = 746825) (by norm_num)
theorem B2796989 : Blo 1863633 2796989 := bbase (se 3 (by rfl) ⟨524435, by rfl⟩ : syracuseStep 2796989 = 1048871) (by norm_num)
theorem B2797013 : Blo 1863633 2797013 := bbase (se 7 (by rfl) ⟨32777, by rfl⟩ : syracuseStep 2797013 = 65555) (by norm_num)
theorem B7081445 : Blo 1863633 7081445 := bbase (se 4 (by rfl) ⟨663885, by rfl⟩ : syracuseStep 7081445 = 1327771) (by norm_num)
theorem B5311973 : Blo 1863633 5311973 := bbase (se 4 (by rfl) ⟨497997, by rfl⟩ : syracuseStep 5311973 = 995995) (by norm_num)
theorem B2797037 : Blo 1863633 2797037 := bbase (se 3 (by rfl) ⟨524444, by rfl⟩ : syracuseStep 2797037 = 1048889) (by norm_num)
theorem B2797061 : Blo 1863633 2797061 := bbase (se 4 (by rfl) ⟨262224, by rfl⟩ : syracuseStep 2797061 = 524449) (by norm_num)
theorem B5041685 : Blo 1863633 5041685 := bbase (se 6 (by rfl) ⟨118164, by rfl⟩ : syracuseStep 5041685 = 236329) (by norm_num)
theorem B2797085 : Blo 1863633 2797085 := bbase (se 3 (by rfl) ⟨524453, by rfl⟩ : syracuseStep 2797085 = 1048907) (by norm_num)
theorem B2797109 : Blo 1863633 2797109 := bbase (se 5 (by rfl) ⟨131114, by rfl⟩ : syracuseStep 2797109 = 262229) (by norm_num)
theorem B8506949 : Blo 1863633 8506949 := bbase (se 4 (by rfl) ⟨797526, by rfl⟩ : syracuseStep 8506949 = 1595053) (by norm_num)
theorem B2797133 : Blo 1863633 2797133 := bbase (se 3 (by rfl) ⟨524462, by rfl⟩ : syracuseStep 2797133 = 1048925) (by norm_num)
theorem B2797157 : Blo 1863633 2797157 := bbase (se 4 (by rfl) ⟨262233, by rfl⟩ : syracuseStep 2797157 = 524467) (by norm_num)
theorem B2985589 : Blo 1863633 2985589 := bbase (se 5 (by rfl) ⟨139949, by rfl⟩ : syracuseStep 2985589 = 279899) (by norm_num)
theorem B6295157 : Blo 1863633 6295157 := bbase (se 5 (by rfl) ⟨295085, by rfl⟩ : syracuseStep 6295157 = 590171) (by norm_num)
theorem B2797181 : Blo 1863633 2797181 := bbase (se 3 (by rfl) ⟨524471, by rfl⟩ : syracuseStep 2797181 = 1048943) (by norm_num)
theorem B2797205 : Blo 1863633 2797205 := bbase (se 6 (by rfl) ⟨65559, by rfl⟩ : syracuseStep 2797205 = 131119) (by norm_num)
theorem B2797229 : Blo 1863633 2797229 := bbase (se 3 (by rfl) ⟨524480, by rfl⟩ : syracuseStep 2797229 = 1048961) (by norm_num)
theorem B2797253 : Blo 1863633 2797253 := bbase (se 4 (by rfl) ⟨262242, by rfl⟩ : syracuseStep 2797253 = 524485) (by norm_num)
theorem B7966421 : Blo 1863633 7966421 := bbase (se 7 (by rfl) ⟨93356, by rfl⟩ : syracuseStep 7966421 = 186713) (by norm_num)
theorem B5975765 : Blo 1863633 5975765 := bbase (se 7 (by rfl) ⟨70028, by rfl⟩ : syracuseStep 5975765 = 140057) (by norm_num)
theorem B5312213 : Blo 1863633 5312213 := bbase (se 7 (by rfl) ⟨62252, by rfl⟩ : syracuseStep 5312213 = 124505) (by norm_num)
theorem B2797277 : Blo 1863633 2797277 := bbase (se 3 (by rfl) ⟨524489, by rfl⟩ : syracuseStep 2797277 = 1048979) (by norm_num)
theorem B2797301 : Blo 1863633 2797301 := bbase (se 5 (by rfl) ⟨131123, by rfl⟩ : syracuseStep 2797301 = 262247) (by norm_num)
theorem B2797325 : Blo 1863633 2797325 := bbase (se 3 (by rfl) ⟨524498, by rfl⟩ : syracuseStep 2797325 = 1048997) (by norm_num)
theorem B2797349 : Blo 1863633 2797349 := bbase (se 4 (by rfl) ⟨262251, by rfl⟩ : syracuseStep 2797349 = 524503) (by norm_num)
theorem B2797373 : Blo 1863633 2797373 := bbase (se 3 (by rfl) ⟨524507, by rfl⟩ : syracuseStep 2797373 = 1049015) (by norm_num)
theorem B8957765 : Blo 1863633 8957765 := bbase (se 4 (by rfl) ⟨839790, by rfl⟩ : syracuseStep 8957765 = 1679581) (by norm_num)
theorem B2797397 : Blo 1863633 2797397 := bbase (se 9 (by rfl) ⟨8195, by rfl⟩ : syracuseStep 2797397 = 16391) (by norm_num)
theorem B2797421 : Blo 1863633 2797421 := bbase (se 3 (by rfl) ⟨524516, by rfl⟩ : syracuseStep 2797421 = 1049033) (by norm_num)
theorem B2797445 : Blo 1863633 2797445 := bbase (se 4 (by rfl) ⟨262260, by rfl⟩ : syracuseStep 2797445 = 524521) (by norm_num)
theorem B5312405 : Blo 1863633 5312405 := bbase (se 6 (by rfl) ⟨124509, by rfl⟩ : syracuseStep 5312405 = 249019) (by norm_num)
theorem B2797469 : Blo 1863633 2797469 := bbase (se 3 (by rfl) ⟨524525, by rfl⟩ : syracuseStep 2797469 = 1049051) (by norm_num)
theorem B2797493 : Blo 1863633 2797493 := bbase (se 5 (by rfl) ⟨131132, by rfl⟩ : syracuseStep 2797493 = 262265) (by norm_num)
theorem B2797517 : Blo 1863633 2797517 := bbase (se 3 (by rfl) ⟨524534, by rfl⟩ : syracuseStep 2797517 = 1049069) (by norm_num)
theorem B2797541 : Blo 1863633 2797541 := bbase (se 4 (by rfl) ⟨262269, by rfl⟩ : syracuseStep 2797541 = 524539) (by norm_num)
theorem B2797565 : Blo 1863633 2797565 := bbase (se 3 (by rfl) ⟨524543, by rfl⟩ : syracuseStep 2797565 = 1049087) (by norm_num)
theorem B2797589 : Blo 1863633 2797589 := bbase (se 6 (by rfl) ⟨65568, by rfl⟩ : syracuseStep 2797589 = 131137) (by norm_num)
theorem B6295589 : Blo 1863633 6295589 := bbase (se 4 (by rfl) ⟨590211, by rfl⟩ : syracuseStep 6295589 = 1180423) (by norm_num)
theorem B2797613 : Blo 1863633 2797613 := bbase (se 3 (by rfl) ⟨524552, by rfl⟩ : syracuseStep 2797613 = 1049105) (by norm_num)
theorem B2797637 : Blo 1863633 2797637 := bbase (se 4 (by rfl) ⟨262278, by rfl⟩ : syracuseStep 2797637 = 524557) (by norm_num)
theorem B2797661 : Blo 1863633 2797661 := bbase (se 3 (by rfl) ⟨524561, by rfl⟩ : syracuseStep 2797661 = 1049123) (by norm_num)
theorem B2797685 : Blo 1863633 2797685 := bbase (se 5 (by rfl) ⟨131141, by rfl⟩ : syracuseStep 2797685 = 262283) (by norm_num)
theorem B2240633 : Blo 1863633 2240633 := bbase (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) (by norm_num)
theorem B2797709 : Blo 1863633 2797709 := bbase (se 3 (by rfl) ⟨524570, by rfl⟩ : syracuseStep 2797709 = 1049141) (by norm_num)
theorem B3190933 : Blo 1863633 3190933 := bbase (se 6 (by rfl) ⟨74787, by rfl⟩ : syracuseStep 3190933 = 149575) (by norm_num)
theorem B2797733 : Blo 1863633 2797733 := bbase (se 4 (by rfl) ⟨262287, by rfl⟩ : syracuseStep 2797733 = 524575) (by norm_num)
theorem B2797757 : Blo 1863633 2797757 := bbase (se 3 (by rfl) ⟨524579, by rfl⟩ : syracuseStep 2797757 = 1049159) (by norm_num)
theorem B2797781 : Blo 1863633 2797781 := bbase (se 7 (by rfl) ⟨32786, by rfl⟩ : syracuseStep 2797781 = 65573) (by norm_num)
theorem B2797805 : Blo 1863633 2797805 := bbase (se 3 (by rfl) ⟨524588, by rfl⟩ : syracuseStep 2797805 = 1049177) (by norm_num)
theorem B2797829 : Blo 1863633 2797829 := bbase (se 4 (by rfl) ⟨262296, by rfl⟩ : syracuseStep 2797829 = 524593) (by norm_num)
theorem B23892245 : Blo 1863633 23892245 := bbase (se 6 (by rfl) ⟨559974, by rfl⟩ : syracuseStep 23892245 = 1119949) (by norm_num)
theorem B6721813 : Blo 1863633 6721813 := bbase (se 6 (by rfl) ⟨157542, by rfl⟩ : syracuseStep 6721813 = 315085) (by norm_num)
theorem B2797853 : Blo 1863633 2797853 := bbase (se 3 (by rfl) ⟨524597, by rfl⟩ : syracuseStep 2797853 = 1049195) (by norm_num)
theorem B2240821 : Blo 1863633 2240821 := bbase (se 5 (by rfl) ⟨105038, by rfl⟩ : syracuseStep 2240821 = 210077) (by norm_num)
theorem B2797877 : Blo 1863633 2797877 := bbase (se 5 (by rfl) ⟨131150, by rfl⟩ : syracuseStep 2797877 = 262301) (by norm_num)
theorem B2797901 : Blo 1863633 2797901 := bbase (se 3 (by rfl) ⟨524606, by rfl⟩ : syracuseStep 2797901 = 1049213) (by norm_num)
theorem B2797925 : Blo 1863633 2797925 := bbase (se 4 (by rfl) ⟨262305, by rfl⟩ : syracuseStep 2797925 = 524611) (by norm_num)
theorem B2797949 : Blo 1863633 2797949 := bbase (se 3 (by rfl) ⟨524615, by rfl⟩ : syracuseStep 2797949 = 1049231) (by norm_num)
theorem B2797973 : Blo 1863633 2797973 := bbase (se 6 (by rfl) ⟨65577, by rfl⟩ : syracuseStep 2797973 = 131155) (by norm_num)
theorem B2797997 : Blo 1863633 2797997 := bbase (se 3 (by rfl) ⟨524624, by rfl⟩ : syracuseStep 2797997 = 1049249) (by norm_num)
theorem B7967173 : Blo 1863633 7967173 := bbase (se 4 (by rfl) ⟨746922, by rfl⟩ : syracuseStep 7967173 = 1493845) (by norm_num)
theorem B2798021 : Blo 1863633 2798021 := bbase (se 4 (by rfl) ⟨262314, by rfl⟩ : syracuseStep 2798021 = 524629) (by norm_num)
theorem B2519501 : Blo 1863633 2519501 := bbase (se 3 (by rfl) ⟨472406, by rfl⟩ : syracuseStep 2519501 = 944813) (by norm_num)
theorem B6296021 : Blo 1863633 6296021 := bbase (se 7 (by rfl) ⟨73781, by rfl⟩ : syracuseStep 6296021 = 147563) (by norm_num)
theorem B2798045 : Blo 1863633 2798045 := bbase (se 3 (by rfl) ⟨524633, by rfl⟩ : syracuseStep 2798045 = 1049267) (by norm_num)
theorem B2798069 : Blo 1863633 2798069 := bbase (se 5 (by rfl) ⟨131159, by rfl⟩ : syracuseStep 2798069 = 262319) (by norm_num)
theorem B2798093 : Blo 1863633 2798093 := bbase (se 3 (by rfl) ⟨524642, by rfl⟩ : syracuseStep 2798093 = 1049285) (by norm_num)
theorem B2241037 : Blo 1863633 2241037 := bbase (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) (by norm_num)
theorem B2798117 : Blo 1863633 2798117 := bbase (se 4 (by rfl) ⟨262323, by rfl⟩ : syracuseStep 2798117 = 524647) (by norm_num)
theorem B9441845 : Blo 1863633 9441845 := bbase (se 5 (by rfl) ⟨442586, by rfl⟩ : syracuseStep 9441845 = 885173) (by norm_num)
theorem B2798141 : Blo 1863633 2798141 := bbase (se 3 (by rfl) ⟨524651, by rfl⟩ : syracuseStep 2798141 = 1049303) (by norm_num)
theorem B2798165 : Blo 1863633 2798165 := bbase (se 8 (by rfl) ⟨16395, by rfl⟩ : syracuseStep 2798165 = 32791) (by norm_num)
theorem B5976661 : Blo 1863633 5976661 := bbase (se 8 (by rfl) ⟨35019, by rfl⟩ : syracuseStep 5976661 = 70039) (by norm_num)
theorem B2798189 : Blo 1863633 2798189 := bbase (se 3 (by rfl) ⟨524660, by rfl⟩ : syracuseStep 2798189 = 1049321) (by norm_num)
theorem B2798213 : Blo 1863633 2798213 := bbase (se 4 (by rfl) ⟨262332, by rfl⟩ : syracuseStep 2798213 = 524665) (by norm_num)
theorem B2798237 : Blo 1863633 2798237 := bbase (se 3 (by rfl) ⟨524669, by rfl⟩ : syracuseStep 2798237 = 1049339) (by norm_num)
theorem B2798261 : Blo 1863633 2798261 := bbase (se 5 (by rfl) ⟨131168, by rfl⟩ : syracuseStep 2798261 = 262337) (by norm_num)
theorem B2798285 : Blo 1863633 2798285 := bbase (se 3 (by rfl) ⟨524678, by rfl⟩ : syracuseStep 2798285 = 1049357) (by norm_num)
theorem B2798309 : Blo 1863633 2798309 := bbase (se 4 (by rfl) ⟨262341, by rfl⟩ : syracuseStep 2798309 = 524683) (by norm_num)
theorem B17920757 : Blo 1863633 17920757 := bbase (se 5 (by rfl) ⟨840035, by rfl⟩ : syracuseStep 17920757 = 1680071) (by norm_num)
theorem B2798333 : Blo 1863633 2798333 := bbase (se 3 (by rfl) ⟨524687, by rfl⟩ : syracuseStep 2798333 = 1049375) (by norm_num)
theorem B2798357 : Blo 1863633 2798357 := bbase (se 6 (by rfl) ⟨65586, by rfl⟩ : syracuseStep 2798357 = 131173) (by norm_num)
theorem B2798381 : Blo 1863633 2798381 := bbase (se 3 (by rfl) ⟨524696, by rfl⟩ : syracuseStep 2798381 = 1049393) (by norm_num)
theorem B2798405 : Blo 1863633 2798405 := bbase (se 4 (by rfl) ⟨262350, by rfl⟩ : syracuseStep 2798405 = 524701) (by norm_num)
theorem B2798429 : Blo 1863633 2798429 := bbase (se 3 (by rfl) ⟨524705, by rfl⟩ : syracuseStep 2798429 = 1049411) (by norm_num)
theorem B3232613 : Blo 1863633 3232613 := bbase (se 4 (by rfl) ⟨303057, by rfl⟩ : syracuseStep 3232613 = 606115) (by norm_num)
theorem B6296453 : Blo 1863633 6296453 := bbase (se 4 (by rfl) ⟨590292, by rfl⟩ : syracuseStep 6296453 = 1180585) (by norm_num)
theorem B1889201 : Blo 1863633 1889201 := bbase (se 2 (by rfl) ⟨708450, by rfl⟩ : syracuseStep 1889201 = 1416901) (by norm_num)
theorem B2986973 : Blo 1863633 2986973 := bbase (se 3 (by rfl) ⟨560057, by rfl⟩ : syracuseStep 2986973 = 1120115) (by norm_num)
theorem B1889269 : Blo 1863633 1889269 := bbase (se 5 (by rfl) ⟨88559, by rfl⟩ : syracuseStep 1889269 = 177119) (by norm_num)
theorem B2987165 : Blo 1863633 2987165 := bbase (se 3 (by rfl) ⟨560093, by rfl⟩ : syracuseStep 2987165 = 1120187) (by norm_num)
theorem B7967909 : Blo 1863633 7967909 := bbase (se 4 (by rfl) ⟨746991, by rfl⟩ : syracuseStep 7967909 = 1493983) (by norm_num)
theorem B6722821 : Blo 1863633 6722821 := bbase (se 4 (by rfl) ⟨630264, by rfl⟩ : syracuseStep 6722821 = 1260529) (by norm_num)
theorem B15922453 : Blo 1863633 15922453 := bbase (se 6 (by rfl) ⟨373182, by rfl⟩ : syracuseStep 15922453 = 746365) (by norm_num)
theorem B2127217 : Blo 1863633 2127217 := bbase (se 2 (by rfl) ⟨797706, by rfl⟩ : syracuseStep 2127217 = 1595413) (by norm_num)
theorem B2872693 : Blo 1863633 2872693 := bbase (se 5 (by rfl) ⟨134657, by rfl⟩ : syracuseStep 2872693 = 269315) (by norm_num)
theorem B2520605 : Blo 1863633 2520605 := bbase (se 3 (by rfl) ⟨472613, by rfl⟩ : syracuseStep 2520605 = 945227) (by norm_num)
theorem B7083557 : Blo 1863633 7083557 := bbase (se 4 (by rfl) ⟨664083, by rfl⟩ : syracuseStep 7083557 = 1328167) (by norm_num)
theorem B1890113 : Blo 1863633 1890113 := bbase (se 2 (by rfl) ⟨708792, by rfl⟩ : syracuseStep 1890113 = 1417585) (by norm_num)
theorem B9443141 : Blo 1863633 9443141 := bbase (se 4 (by rfl) ⟨885294, by rfl⟩ : syracuseStep 9443141 = 1770589) (by norm_num)
theorem B36321173 : Blo 1863633 36321173 := bbase (se 6 (by rfl) ⟨851277, by rfl⟩ : syracuseStep 36321173 = 1702555) (by norm_num)
theorem B1914881 : Blo 1863633 1914881 := bbase (se 2 (by rfl) ⟨718080, by rfl⟩ : syracuseStep 1914881 = 1436161) (by norm_num)
theorem B7559189 : Blo 1863633 7559189 := bbase (se 6 (by rfl) ⟨177168, by rfl⟩ : syracuseStep 7559189 = 354337) (by norm_num)
theorem B1890373 : Blo 1863633 1890373 := bbase (se 4 (by rfl) ⟨177222, by rfl⟩ : syracuseStep 1890373 = 354445) (by norm_num)
theorem B7076069 : Blo 1863633 7076069 := bbase (se 4 (by rfl) ⟨663381, by rfl⟩ : syracuseStep 7076069 = 1326763) (by norm_num)
theorem B9435365 : Blo 1863633 9435365 := bbase (se 4 (by rfl) ⟨884565, by rfl⟩ : syracuseStep 9435365 = 1769131) (by norm_num)
theorem B10082549 : Blo 1863633 10082549 := bbase (se 5 (by rfl) ⟨472619, by rfl⟩ : syracuseStep 10082549 = 945239) (by norm_num)
theorem B4479229 : Blo 1863633 4479229 := bbase (se 3 (by rfl) ⟨839855, by rfl⟩ : syracuseStep 4479229 = 1679711) (by norm_num)
theorem B4036925 : Blo 1863633 4036925 := bbase (se 3 (by rfl) ⟨756923, by rfl⟩ : syracuseStep 4036925 = 1513847) (by norm_num)
theorem B1890697 : Blo 1863633 1890697 := bbase (se 2 (by rfl) ⟨709011, by rfl⟩ : syracuseStep 1890697 = 1418023) (by norm_num)
theorem B1890713 : Blo 1863633 1890713 := bbase (se 2 (by rfl) ⟨709017, by rfl⟩ : syracuseStep 1890713 = 1418035) (by norm_num)
theorem B3586493 : Blo 1863633 3586493 := bbase (se 3 (by rfl) ⟨672467, by rfl⟩ : syracuseStep 3586493 = 1344935) (by norm_num)
theorem B7174613 : Blo 1863633 7174613 := bbase (se 7 (by rfl) ⟨84077, by rfl⟩ : syracuseStep 7174613 = 168155) (by norm_num)
theorem B7961125 : Blo 1863633 7961125 := bbase (se 4 (by rfl) ⟨746355, by rfl⟩ : syracuseStep 7961125 = 1492711) (by norm_num)
theorem B6289973 : Blo 1863633 6289973 := bbase (se 5 (by rfl) ⟨294842, by rfl⟩ : syracuseStep 6289973 = 589685) (by norm_num)
theorem B6380117 : Blo 1863633 6380117 := bbase (se 8 (by rfl) ⟨37383, by rfl⟩ : syracuseStep 6380117 = 74767) (by norm_num)
theorem B8501861 : Blo 1863633 8501861 := bbase (se 4 (by rfl) ⟨797049, by rfl⟩ : syracuseStep 8501861 = 1594099) (by norm_num)
theorem B5307029 : Blo 1863633 5307029 := bbase (se 6 (by rfl) ⟨124383, by rfl⟩ : syracuseStep 5307029 = 248767) (by norm_num)
theorem B5970613 : Blo 1863633 5970613 := bbase (se 5 (by rfl) ⟨279872, by rfl⟩ : syracuseStep 5970613 = 559745) (by norm_num)
theorem B13441781 : Blo 1863633 13441781 := bbase (se 5 (by rfl) ⟨630083, by rfl⟩ : syracuseStep 13441781 = 1260167) (by norm_num)
theorem B2423585 : Blo 1863633 2423585 := bbase (se 2 (by rfl) ⟨908844, by rfl⟩ : syracuseStep 2423585 = 1817689) (by norm_num)
theorem B4717349 : Blo 1863633 4717349 := bbase (se 4 (by rfl) ⟨442251, by rfl⟩ : syracuseStep 4717349 = 884503) (by norm_num)
theorem B1915777 : Blo 1863633 1915777 := bbase (se 2 (by rfl) ⟨718416, by rfl⟩ : syracuseStep 1915777 = 1436833) (by norm_num)
theorem B4193189 : Blo 1863633 4193189 := bbase (se 4 (by rfl) ⟨393111, by rfl⟩ : syracuseStep 4193189 = 786223) (by norm_num)
theorem B4717541 : Blo 1863633 4717541 := bbase (se 4 (by rfl) ⟨442269, by rfl⟩ : syracuseStep 4717541 = 884539) (by norm_num)
theorem B6290405 : Blo 1863633 6290405 := bbase (se 4 (by rfl) ⟨589725, by rfl⟩ : syracuseStep 6290405 = 1179451) (by norm_num)
theorem B4193261 : Blo 1863633 4193261 := bbase (se 3 (by rfl) ⟨786236, by rfl⟩ : syracuseStep 4193261 = 1572473) (by norm_num)
theorem B3980333 : Blo 1863633 3980333 := bbase (se 3 (by rfl) ⟨746312, by rfl⟩ : syracuseStep 3980333 = 1492625) (by norm_num)
theorem B4193333 : Blo 1863633 4193333 := bbase (se 5 (by rfl) ⟨196562, by rfl⟩ : syracuseStep 4193333 = 393125) (by norm_num)
theorem B9444437 : Blo 1863633 9444437 := bbase (se 8 (by rfl) ⟨55338, by rfl⟩ : syracuseStep 9444437 = 110677) (by norm_num)
theorem B4193405 : Blo 1863633 4193405 := bbase (se 3 (by rfl) ⟨786263, by rfl⟩ : syracuseStep 4193405 = 1572527) (by norm_num)
theorem B3980477 : Blo 1863633 3980477 := bbase (se 3 (by rfl) ⟨746339, by rfl⟩ : syracuseStep 3980477 = 1492679) (by norm_num)
theorem B4193477 : Blo 1863633 4193477 := bbase (se 4 (by rfl) ⟨393138, by rfl⟩ : syracuseStep 4193477 = 786277) (by norm_num)
theorem B11943125 : Blo 1863633 11943125 := bbase (se 7 (by rfl) ⟨139958, by rfl⟩ : syracuseStep 11943125 = 279917) (by norm_num)
theorem B15924437 : Blo 1863633 15924437 := bbase (se 7 (by rfl) ⟨186614, by rfl⟩ : syracuseStep 15924437 = 373229) (by norm_num)
theorem B21232853 : Blo 1863633 21232853 := bbase (se 7 (by rfl) ⟨248822, by rfl⟩ : syracuseStep 21232853 = 497645) (by norm_num)
theorem B25509077 : Blo 1863633 25509077 := bbase (se 7 (by rfl) ⟨298934, by rfl⟩ : syracuseStep 25509077 = 597869) (by norm_num)
theorem B14351573 : Blo 1863633 14351573 := bbase (se 7 (by rfl) ⟨168182, by rfl⟩ : syracuseStep 14351573 = 336365) (by norm_num)
theorem B3144973 : Blo 1863633 3144973 := bbase (se 3 (by rfl) ⟨589682, by rfl⟩ : syracuseStep 3144973 = 1179365) (by norm_num)
theorem B4193549 : Blo 1863633 4193549 := bbase (se 3 (by rfl) ⟨786290, by rfl⟩ : syracuseStep 4193549 = 1572581) (by norm_num)
theorem B8961301 : Blo 1863633 8961301 := bbase (se 6 (by rfl) ⟨210030, by rfl⟩ : syracuseStep 8961301 = 420061) (by norm_num)
theorem B4717885 : Blo 1863633 4717885 := bbase (se 3 (by rfl) ⟨884603, by rfl⟩ : syracuseStep 4717885 = 1769207) (by norm_num)
theorem B4193621 : Blo 1863633 4193621 := bbase (se 11 (by rfl) ⟨3071, by rfl⟩ : syracuseStep 4193621 = 6143) (by norm_num)
theorem B3145061 : Blo 1863633 3145061 := bbase (se 4 (by rfl) ⟨294849, by rfl⟩ : syracuseStep 3145061 = 589699) (by norm_num)
theorem B4251005 : Blo 1863633 4251005 := bbase (se 3 (by rfl) ⟨797063, by rfl⟩ : syracuseStep 4251005 = 1594127) (by norm_num)
theorem B5307781 : Blo 1863633 5307781 := bbase (se 4 (by rfl) ⟨497604, by rfl⟩ : syracuseStep 5307781 = 995209) (by norm_num)
theorem B7077253 : Blo 1863633 7077253 := bbase (se 4 (by rfl) ⟨663492, by rfl⟩ : syracuseStep 7077253 = 1326985) (by norm_num)
theorem B6290837 : Blo 1863633 6290837 := bbase (se 6 (by rfl) ⟨147441, by rfl⟩ : syracuseStep 6290837 = 294883) (by norm_num)
theorem B4193693 : Blo 1863633 4193693 := bbase (se 3 (by rfl) ⟨786317, by rfl⟩ : syracuseStep 4193693 = 1572635) (by norm_num)
theorem B4717997 : Blo 1863633 4717997 := bbase (se 3 (by rfl) ⟨884624, by rfl⟩ : syracuseStep 4717997 = 1769249) (by norm_num)
theorem B3145189 : Blo 1863633 3145189 := bbase (se 4 (by rfl) ⟨294861, by rfl⟩ : syracuseStep 3145189 = 589723) (by norm_num)
theorem B4193765 : Blo 1863633 4193765 := bbase (se 4 (by rfl) ⟨393165, by rfl⟩ : syracuseStep 4193765 = 786331) (by norm_num)
theorem B2096617 : Blo 1863633 2096617 := bbase (se 2 (by rfl) ⟨786231, by rfl⟩ : syracuseStep 2096617 = 1572463) (by norm_num)
theorem B9436661 : Blo 1863633 9436661 := bbase (se 5 (by rfl) ⟨442343, by rfl⟩ : syracuseStep 9436661 = 884687) (by norm_num)
theorem B1990153 : Blo 1863633 1990153 := bbase (se 2 (by rfl) ⟨746307, by rfl⟩ : syracuseStep 1990153 = 1492615) (by norm_num)
theorem B2096653 : Blo 1863633 2096653 := bbase (se 3 (by rfl) ⟨393122, by rfl⟩ : syracuseStep 2096653 = 786245) (by norm_num)
theorem B2358821 : Blo 1863633 2358821 := bbase (se 4 (by rfl) ⟨221139, by rfl⟩ : syracuseStep 2358821 = 442279) (by norm_num)
theorem B4193837 : Blo 1863633 4193837 := bbase (se 3 (by rfl) ⟨786344, by rfl⟩ : syracuseStep 4193837 = 1572689) (by norm_num)
theorem B2096689 : Blo 1863633 2096689 := bbase (se 2 (by rfl) ⟨786258, by rfl⟩ : syracuseStep 2096689 = 1572517) (by norm_num)
theorem B2391601 : Blo 1863633 2391601 := bbase (se 2 (by rfl) ⟨896850, by rfl⟩ : syracuseStep 2391601 = 1793701) (by norm_num)
theorem B3145277 : Blo 1863633 3145277 := bbase (se 3 (by rfl) ⟨589739, by rfl⟩ : syracuseStep 3145277 = 1179479) (by norm_num)
theorem B2096725 : Blo 1863633 2096725 := bbase (se 8 (by rfl) ⟨12285, by rfl⟩ : syracuseStep 2096725 = 24571) (by norm_num)
theorem B2358877 : Blo 1863633 2358877 := bbase (se 3 (by rfl) ⟨442289, by rfl⟩ : syracuseStep 2358877 = 884579) (by norm_num)
theorem B4480613 : Blo 1863633 4480613 := bbase (se 4 (by rfl) ⟨420057, by rfl⟩ : syracuseStep 4480613 = 840115) (by norm_num)
theorem B4718189 : Blo 1863633 4718189 := bbase (se 3 (by rfl) ⟨884660, by rfl⟩ : syracuseStep 4718189 = 1769321) (by norm_num)
theorem B4193909 : Blo 1863633 4193909 := bbase (se 5 (by rfl) ⟨196589, by rfl⟩ : syracuseStep 4193909 = 393179) (by norm_num)
theorem B2096761 : Blo 1863633 2096761 := bbase (se 2 (by rfl) ⟨786285, by rfl⟩ : syracuseStep 2096761 = 1572571) (by norm_num)
theorem B2096797 : Blo 1863633 2096797 := bbase (se 3 (by rfl) ⟨393149, by rfl⟩ : syracuseStep 2096797 = 786299) (by norm_num)
theorem B6995621 : Blo 1863633 6995621 := bbase (se 4 (by rfl) ⟨655839, by rfl⟩ : syracuseStep 6995621 = 1311679) (by norm_num)
theorem B7077557 : Blo 1863633 7077557 := bbase (se 5 (by rfl) ⟨331760, by rfl⟩ : syracuseStep 7077557 = 663521) (by norm_num)
theorem B6053557 : Blo 1863633 6053557 := bbase (se 5 (by rfl) ⟨283760, by rfl⟩ : syracuseStep 6053557 = 567521) (by norm_num)
theorem B2358973 : Blo 1863633 2358973 := bbase (se 3 (by rfl) ⟨442307, by rfl⟩ : syracuseStep 2358973 = 884615) (by norm_num)
theorem B3145405 : Blo 1863633 3145405 := bbase (se 3 (by rfl) ⟨589763, by rfl⟩ : syracuseStep 3145405 = 1179527) (by norm_num)
theorem B4193981 : Blo 1863633 4193981 := bbase (se 3 (by rfl) ⟨786371, by rfl⟩ : syracuseStep 4193981 = 1572743) (by norm_num)
theorem B1990337 : Blo 1863633 1990337 := bbase (se 2 (by rfl) ⟨746376, by rfl⟩ : syracuseStep 1990337 = 1492753) (by norm_num)
theorem B2096833 : Blo 1863633 2096833 := bbase (se 2 (by rfl) ⟨786312, by rfl⟩ : syracuseStep 2096833 = 1572625) (by norm_num)
theorem B2096869 : Blo 1863633 2096869 := bbase (se 4 (by rfl) ⟨196581, by rfl⟩ : syracuseStep 2096869 = 393163) (by norm_num)
theorem B2391805 : Blo 1863633 2391805 := bbase (se 3 (by rfl) ⟨448463, by rfl⟩ : syracuseStep 2391805 = 896927) (by norm_num)
theorem B4194053 : Blo 1863633 4194053 := bbase (se 4 (by rfl) ⟨393192, by rfl⟩ : syracuseStep 4194053 = 786385) (by norm_num)
theorem B2096905 : Blo 1863633 2096905 := bbase (se 2 (by rfl) ⟨786339, by rfl⟩ : syracuseStep 2096905 = 1572679) (by norm_num)
theorem B3145493 : Blo 1863633 3145493 := bbase (se 6 (by rfl) ⟨73722, by rfl⟩ : syracuseStep 3145493 = 147445) (by norm_num)
theorem B4480805 : Blo 1863633 4480805 := bbase (se 4 (by rfl) ⟨420075, by rfl⟩ : syracuseStep 4480805 = 840151) (by norm_num)
theorem B2096941 : Blo 1863633 2096941 := bbase (se 3 (by rfl) ⟨393176, by rfl⟩ : syracuseStep 2096941 = 786353) (by norm_num)
theorem B3538741 : Blo 1863633 3538741 := bbase (se 5 (by rfl) ⟨165878, by rfl⟩ : syracuseStep 3538741 = 331757) (by norm_num)
theorem B6291269 : Blo 1863633 6291269 := bbase (se 4 (by rfl) ⟨589806, by rfl⟩ : syracuseStep 6291269 = 1179613) (by norm_num)
theorem B5381957 : Blo 1863633 5381957 := bbase (se 4 (by rfl) ⟨504558, by rfl⟩ : syracuseStep 5381957 = 1009117) (by norm_num)
theorem B4194125 : Blo 1863633 4194125 := bbase (se 3 (by rfl) ⟨786398, by rfl⟩ : syracuseStep 4194125 = 1572797) (by norm_num)
theorem B2096977 : Blo 1863633 2096977 := bbase (se 2 (by rfl) ⟨786366, by rfl⟩ : syracuseStep 2096977 = 1572733) (by norm_num)
theorem B2359145 : Blo 1863633 2359145 := bbase (se 2 (by rfl) ⟨884679, by rfl⟩ : syracuseStep 2359145 = 1769359) (by norm_num)
theorem B2097013 : Blo 1863633 2097013 := bbase (se 5 (by rfl) ⟨98297, by rfl⟩ : syracuseStep 2097013 = 196595) (by norm_num)
theorem B3145621 : Blo 1863633 3145621 := bbase (se 6 (by rfl) ⟨73725, by rfl⟩ : syracuseStep 3145621 = 147451) (by norm_num)
theorem B4194197 : Blo 1863633 4194197 := bbase (se 6 (by rfl) ⟨98301, by rfl⟩ : syracuseStep 4194197 = 196603) (by norm_num)
theorem B19136405 : Blo 1863633 19136405 := bbase (se 6 (by rfl) ⟨448509, by rfl⟩ : syracuseStep 19136405 = 897019) (by norm_num)
theorem B2097049 : Blo 1863633 2097049 := bbase (se 2 (by rfl) ⟨786393, by rfl⟩ : syracuseStep 2097049 = 1572787) (by norm_num)
theorem B2359201 : Blo 1863633 2359201 := bbase (se 2 (by rfl) ⟨884700, by rfl⟩ : syracuseStep 2359201 = 1769401) (by norm_num)
theorem B3981221 : Blo 1863633 3981221 := bbase (se 4 (by rfl) ⟨373239, by rfl⟩ : syracuseStep 3981221 = 746479) (by norm_num)
theorem B2097085 : Blo 1863633 2097085 := bbase (se 3 (by rfl) ⟨393203, by rfl⟩ : syracuseStep 2097085 = 786407) (by norm_num)
theorem B3538885 : Blo 1863633 3538885 := bbase (se 4 (by rfl) ⟨331770, by rfl⟩ : syracuseStep 3538885 = 663541) (by norm_num)
theorem B4718533 : Blo 1863633 4718533 := bbase (se 4 (by rfl) ⟨442362, by rfl⟩ : syracuseStep 4718533 = 884725) (by norm_num)
theorem B4194269 : Blo 1863633 4194269 := bbase (se 3 (by rfl) ⟨786425, by rfl⟩ : syracuseStep 4194269 = 1572851) (by norm_num)
theorem B2097121 : Blo 1863633 2097121 := bbase (se 2 (by rfl) ⟨786420, by rfl⟩ : syracuseStep 2097121 = 1572841) (by norm_num)
theorem B3145709 : Blo 1863633 3145709 := bbase (se 3 (by rfl) ⟨589820, by rfl⟩ : syracuseStep 3145709 = 1179641) (by norm_num)
theorem B3145729 : Blo 1863633 3145729 := bstep (se 2 (by rfl) ⟨1179648, by rfl⟩ : syracuseStep 3145729 = 2359297) B2359297
theorem B3538961 : Blo 1863633 3538961 := bstep (se 2 (by rfl) ⟨1327110, by rfl⟩ : syracuseStep 3538961 = 2654221) B2654221
theorem B3145763 : Blo 1863633 3145763 := bstep (se 1 (by rfl) ⟨2359322, by rfl⟩ : syracuseStep 3145763 = 4718645) B4718645
theorem B6053933 : Blo 1863633 6053933 := bstep (se 3 (by rfl) ⟨1135112, by rfl⟩ : syracuseStep 6053933 = 2270225) B2270225
theorem B2359363 : Blo 1863633 2359363 := bstep (se 1 (by rfl) ⟨1769522, by rfl⟩ : syracuseStep 2359363 = 3539045) B3539045
theorem B11952197 : Blo 1863633 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B2097283 : Blo 1863633 2097283 := bstep (se 1 (by rfl) ⟨1572962, by rfl⟩ : syracuseStep 2097283 = 3145925) B3145925
theorem B4194449 : Blo 1863633 4194449 := bstep (se 2 (by rfl) ⟨1572918, by rfl⟩ : syracuseStep 4194449 = 3145837) B3145837
theorem B4194467 : Blo 1863633 4194467 := bstep (se 1 (by rfl) ⟨3145850, by rfl⟩ : syracuseStep 4194467 = 6291701) B6291701
theorem B3145891 : Blo 1863633 3145891 := bstep (se 1 (by rfl) ⟨2359418, by rfl⟩ : syracuseStep 3145891 = 4718837) B4718837
theorem B2359459 : Blo 1863633 2359459 := bstep (se 1 (by rfl) ⟨1769594, by rfl⟩ : syracuseStep 2359459 = 3539189) B3539189
theorem B2097427 : Blo 1863633 2097427 := bstep (se 1 (by rfl) ⟨1573070, by rfl⟩ : syracuseStep 2097427 = 3146141) B3146141
theorem B93184277 : Blo 1863633 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B3146033 : Blo 1863633 3146033 := bstep (se 2 (by rfl) ⟨1179762, by rfl⟩ : syracuseStep 3146033 = 2359525) B2359525
theorem B10625357 : Blo 1863633 10625357 := bstep (se 3 (by rfl) ⟨1992254, by rfl⟩ : syracuseStep 10625357 = 3984509) B3984509
theorem B5972305 : Blo 1863633 5972305 := bstep (se 2 (by rfl) ⟨2239614, by rfl⟩ : syracuseStep 5972305 = 4479229) B4479229
theorem B8962417 : Blo 1863633 8962417 := bstep (se 2 (by rfl) ⟨3360906, by rfl⟩ : syracuseStep 8962417 = 6721813) B6721813
theorem B2097571 : Blo 1863633 2097571 := bstep (se 1 (by rfl) ⟨1573178, by rfl⟩ : syracuseStep 2097571 = 3146357) B3146357
theorem B4194737 : Blo 1863633 4194737 := bstep (se 2 (by rfl) ⟨1573026, by rfl⟩ : syracuseStep 4194737 = 3146053) B3146053
theorem B3146161 : Blo 1863633 3146161 := bstep (se 2 (by rfl) ⟨1179810, by rfl⟩ : syracuseStep 3146161 = 2359621) B2359621
theorem B4194755 : Blo 1863633 4194755 := bstep (se 1 (by rfl) ⟨3146066, by rfl⟩ : syracuseStep 4194755 = 6292133) B6292133
theorem B6291917 : Blo 1863633 6291917 := bstep (se 3 (by rfl) ⟨1179734, by rfl⟩ : syracuseStep 6291917 = 2359469) B2359469
theorem B3146195 : Blo 1863633 3146195 := bstep (se 1 (by rfl) ⟨2359646, by rfl⟩ : syracuseStep 3146195 = 4719293) B4719293
theorem B6717923 : Blo 1863633 6717923 := bstep (se 1 (by rfl) ⟨5038442, by rfl⟩ : syracuseStep 6717923 = 10076885) B10076885
theorem B20431331 : Blo 1863633 20431331 := bstep (se 1 (by rfl) ⟨15323498, by rfl⟩ : syracuseStep 20431331 = 30646997) B30646997
theorem B6291971 : Blo 1863633 6291971 := bstep (se 1 (by rfl) ⟨4718978, by rfl⟩ : syracuseStep 6291971 = 9437957) B9437957
theorem B2097715 : Blo 1863633 2097715 := bstep (se 1 (by rfl) ⟨1573286, by rfl⟩ : syracuseStep 2097715 = 3146573) B3146573
theorem B2654785 : Blo 1863633 2654785 := bstep (se 2 (by rfl) ⟨995544, by rfl⟩ : syracuseStep 2654785 = 1991089) B1991089
theorem B2155075 : Blo 1863633 2155075 := bstep (se 1 (by rfl) ⟨1616306, by rfl⟩ : syracuseStep 2155075 = 3232613) B3232613
theorem B3146323 : Blo 1863633 3146323 := bstep (se 1 (by rfl) ⟨2359742, by rfl⟩ : syracuseStep 3146323 = 4719485) B4719485
theorem B9437795 : Blo 1863633 9437795 := bstep (se 1 (by rfl) ⟨7078346, by rfl⟩ : syracuseStep 9437795 = 14156693) B14156693
theorem B7078499 : Blo 1863633 7078499 := bstep (se 1 (by rfl) ⟨5308874, by rfl⟩ : syracuseStep 7078499 = 10617749) B10617749
theorem B2359955 : Blo 1863633 2359955 := bstep (se 1 (by rfl) ⟨1769966, by rfl⟩ : syracuseStep 2359955 = 3539933) B3539933
theorem B1991315 : Blo 1863633 1991315 := bstep (se 1 (by rfl) ⟨1493486, by rfl⟩ : syracuseStep 1991315 = 2986973) B2986973
theorem B2097859 : Blo 1863633 2097859 := bstep (se 1 (by rfl) ⟨1573394, by rfl⟩ : syracuseStep 2097859 = 3146789) B3146789
theorem B5669585 : Blo 1863633 5669585 := bstep (se 2 (by rfl) ⟨2126094, by rfl⟩ : syracuseStep 5669585 = 4252189) B4252189
theorem B4195025 : Blo 1863633 4195025 := bstep (se 2 (by rfl) ⟨1573134, by rfl⟩ : syracuseStep 4195025 = 3146269) B3146269
theorem B3146465 : Blo 1863633 3146465 := bstep (se 2 (by rfl) ⟨1179924, by rfl⟩ : syracuseStep 3146465 = 2359849) B2359849
theorem B4195043 : Blo 1863633 4195043 := bstep (se 1 (by rfl) ⟨3146282, by rfl⟩ : syracuseStep 4195043 = 6292565) B6292565
theorem B6292241 : Blo 1863633 6292241 := bstep (se 2 (by rfl) ⟨2359590, by rfl⟩ : syracuseStep 6292241 = 4719181) B4719181
theorem B10765133 : Blo 1863633 10765133 := bstep (se 3 (by rfl) ⟨2018462, by rfl⟩ : syracuseStep 10765133 = 4036925) B4036925
theorem B2098003 : Blo 1863633 2098003 := bstep (se 1 (by rfl) ⟨1573502, by rfl⟩ : syracuseStep 2098003 = 3147005) B3147005
theorem B3146593 : Blo 1863633 3146593 := bstep (se 2 (by rfl) ⟨1179972, by rfl⟩ : syracuseStep 3146593 = 2359945) B2359945
theorem B5309297 : Blo 1863633 5309297 := bstep (se 2 (by rfl) ⟨1990986, by rfl⟩ : syracuseStep 5309297 = 3981973) B3981973
theorem B3146627 : Blo 1863633 3146627 := bstep (se 1 (by rfl) ⟨2359970, by rfl⟩ : syracuseStep 3146627 = 4719941) B4719941
theorem B4719505 : Blo 1863633 4719505 := bstep (se 2 (by rfl) ⟨1769814, by rfl⟩ : syracuseStep 4719505 = 3539629) B3539629
theorem B3539857 : Blo 1863633 3539857 := bstep (se 2 (by rfl) ⟨1327446, by rfl⟩ : syracuseStep 3539857 = 2654893) B2654893
theorem B2655121 : Blo 1863633 2655121 := bstep (se 2 (by rfl) ⟨995670, by rfl⟩ : syracuseStep 2655121 = 1991341) B1991341
theorem B2098147 : Blo 1863633 2098147 := bstep (se 1 (by rfl) ⟨1573610, by rfl⟩ : syracuseStep 2098147 = 3147221) B3147221
theorem B4195313 : Blo 1863633 4195313 := bstep (se 2 (by rfl) ⟨1573242, by rfl⟩ : syracuseStep 4195313 = 3146485) B3146485
theorem B4195331 : Blo 1863633 4195331 := bstep (se 1 (by rfl) ⟨3146498, by rfl⟩ : syracuseStep 4195331 = 6292997) B6292997
theorem B3146755 : Blo 1863633 3146755 := bstep (se 1 (by rfl) ⟨2360066, by rfl⟩ : syracuseStep 3146755 = 4720133) B4720133
theorem B5309489 : Blo 1863633 5309489 := bstep (se 2 (by rfl) ⟨1991058, by rfl⟩ : syracuseStep 5309489 = 3982117) B3982117
theorem B3540017 : Blo 1863633 3540017 := bstep (se 2 (by rfl) ⟨1327506, by rfl⟩ : syracuseStep 3540017 = 2655013) B2655013
theorem B2589763 : Blo 1863633 2589763 := bstep (se 1 (by rfl) ⟨1942322, by rfl⟩ : syracuseStep 2589763 = 3884645) B3884645
theorem B2835571 : Blo 1863633 2835571 := bstep (se 1 (by rfl) ⟨2126678, by rfl⟩ : syracuseStep 2835571 = 4253357) B4253357
theorem B2098291 : Blo 1863633 2098291 := bstep (se 1 (by rfl) ⟨1573718, by rfl⟩ : syracuseStep 2098291 = 3147437) B3147437
theorem B3146897 : Blo 1863633 3146897 := bstep (se 2 (by rfl) ⟨1180086, by rfl⟩ : syracuseStep 3146897 = 2360173) B2360173
theorem B4719779 : Blo 1863633 4719779 := bstep (se 1 (by rfl) ⟨3539834, by rfl⟩ : syracuseStep 4719779 = 7079669) B7079669
theorem B6718669 : Blo 1863633 6718669 := bstep (se 3 (by rfl) ⟨1259750, by rfl⟩ : syracuseStep 6718669 = 2519501) B2519501
theorem B2098435 : Blo 1863633 2098435 := bstep (se 1 (by rfl) ⟨1573826, by rfl⟩ : syracuseStep 2098435 = 3147653) B3147653
theorem B4195601 : Blo 1863633 4195601 := bstep (se 2 (by rfl) ⟨1573350, by rfl⟩ : syracuseStep 4195601 = 3146701) B3146701
theorem B3147025 : Blo 1863633 3147025 := bstep (se 2 (by rfl) ⟨1180134, by rfl⟩ : syracuseStep 3147025 = 2360269) B2360269
theorem B4195619 : Blo 1863633 4195619 := bstep (se 1 (by rfl) ⟨3146714, by rfl⟩ : syracuseStep 4195619 = 6293429) B6293429
theorem B6292781 : Blo 1863633 6292781 := bstep (se 3 (by rfl) ⟨1179896, by rfl⟩ : syracuseStep 6292781 = 2359793) B2359793
theorem B3147059 : Blo 1863633 3147059 := bstep (se 1 (by rfl) ⟨2360294, by rfl⟩ : syracuseStep 3147059 = 4720589) B4720589
theorem B2360659 : Blo 1863633 2360659 := bstep (se 1 (by rfl) ⟨1770494, by rfl⟩ : syracuseStep 2360659 = 3540989) B3540989
theorem B5039459 : Blo 1863633 5039459 := bstep (se 1 (by rfl) ⟨3779594, by rfl⟩ : syracuseStep 5039459 = 7559189) B7559189
theorem B6292835 : Blo 1863633 6292835 := bstep (se 1 (by rfl) ⟨4719626, by rfl⟩ : syracuseStep 6292835 = 9439253) B9439253
theorem B4719971 : Blo 1863633 4719971 := bstep (se 1 (by rfl) ⟨3539978, by rfl⟩ : syracuseStep 4719971 = 7079957) B7079957
theorem B9438605 : Blo 1863633 9438605 := bstep (se 3 (by rfl) ⟨1769738, by rfl⟩ : syracuseStep 9438605 = 3539477) B3539477
theorem B2098579 : Blo 1863633 2098579 := bstep (se 1 (by rfl) ⟨1573934, by rfl⟩ : syracuseStep 2098579 = 3147869) B3147869
theorem B3147187 : Blo 1863633 3147187 := bstep (se 1 (by rfl) ⟨2360390, by rfl⟩ : syracuseStep 3147187 = 4720781) B4720781
theorem B2360755 : Blo 1863633 2360755 := bstep (se 1 (by rfl) ⟨1770566, by rfl⟩ : syracuseStep 2360755 = 3541133) B3541133
theorem B3540419 : Blo 1863633 3540419 := bstep (se 1 (by rfl) ⟨2655314, by rfl⟩ : syracuseStep 3540419 = 5310629) B5310629
theorem B2655713 : Blo 1863633 2655713 := bstep (se 2 (by rfl) ⟨995892, by rfl⟩ : syracuseStep 2655713 = 1991785) B1991785
theorem B22685197 : Blo 1863633 22685197 := bstep (se 3 (by rfl) ⟨4253474, by rfl⟩ : syracuseStep 22685197 = 8506949) B8506949
theorem B2098723 : Blo 1863633 2098723 := bstep (se 1 (by rfl) ⟨1574042, by rfl⟩ : syracuseStep 2098723 = 3148085) B3148085
theorem B4195889 : Blo 1863633 4195889 := bstep (se 2 (by rfl) ⟨1573458, by rfl⟩ : syracuseStep 4195889 = 3146917) B3146917
theorem B3147329 : Blo 1863633 3147329 := bstep (se 2 (by rfl) ⟨1180248, by rfl⟩ : syracuseStep 3147329 = 2360497) B2360497
theorem B4195907 : Blo 1863633 4195907 := bstep (se 1 (by rfl) ⟨3146930, by rfl⟩ : syracuseStep 4195907 = 6293861) B6293861
theorem B7079501 : Blo 1863633 7079501 := bstep (se 3 (by rfl) ⟨1327406, by rfl⟩ : syracuseStep 7079501 = 2654813) B2654813
theorem B6719075 : Blo 1863633 6719075 := bstep (se 1 (by rfl) ⟨5039306, by rfl⟩ : syracuseStep 6719075 = 10078613) B10078613
theorem B6293105 : Blo 1863633 6293105 := bstep (se 2 (by rfl) ⟨2359914, by rfl⟩ : syracuseStep 6293105 = 4719829) B4719829
theorem B3147457 : Blo 1863633 3147457 := bstep (se 2 (by rfl) ⟨1180296, by rfl⟩ : syracuseStep 3147457 = 2360593) B2360593
theorem B4253411 : Blo 1863633 4253411 := bstep (se 1 (by rfl) ⟨3190058, by rfl⟩ : syracuseStep 4253411 = 6380117) B6380117
theorem B3147491 : Blo 1863633 3147491 := bstep (se 1 (by rfl) ⟨2360618, by rfl⟩ : syracuseStep 3147491 = 4721237) B4721237
theorem B17917681 : Blo 1863633 17917681 := bstep (se 2 (by rfl) ⟨6719130, by rfl⟩ : syracuseStep 17917681 = 13438261) B13438261
theorem B2836289 : Blo 1863633 2836289 := bstep (se 2 (by rfl) ⟨1063608, by rfl⟩ : syracuseStep 2836289 = 2127217) B2127217
theorem B4196177 : Blo 1863633 4196177 := bstep (se 2 (by rfl) ⟨1573566, by rfl⟩ : syracuseStep 4196177 = 3147133) B3147133
theorem B4196195 : Blo 1863633 4196195 := bstep (se 1 (by rfl) ⟨3147146, by rfl⟩ : syracuseStep 4196195 = 6294293) B6294293
theorem B3147619 : Blo 1863633 3147619 := bstep (se 1 (by rfl) ⟨2360714, by rfl⟩ : syracuseStep 3147619 = 4721429) B4721429
theorem B2795459 : Blo 1863633 2795459 := bstep (se 1 (by rfl) ⟨2096594, by rfl⟩ : syracuseStep 2795459 = 4193189) B4193189
theorem B2795489 : Blo 1863633 2795489 := bstep (se 2 (by rfl) ⟨1048308, by rfl⟩ : syracuseStep 2795489 = 2096617) B2096617
theorem B3147761 : Blo 1863633 3147761 := bstep (se 2 (by rfl) ⟨1180410, by rfl⟩ : syracuseStep 3147761 = 2360821) B2360821
theorem B2795507 : Blo 1863633 2795507 := bstep (se 1 (by rfl) ⟨2096630, by rfl⟩ : syracuseStep 2795507 = 4193261) B4193261
theorem B2656243 : Blo 1863633 2656243 := bstep (se 1 (by rfl) ⟨1992182, by rfl⟩ : syracuseStep 2656243 = 3984365) B3984365
theorem B2795537 : Blo 1863633 2795537 := bstep (se 2 (by rfl) ⟨1048326, by rfl⟩ : syracuseStep 2795537 = 2096653) B2096653
theorem B5310481 : Blo 1863633 5310481 := bstep (se 2 (by rfl) ⟨1991430, by rfl⟩ : syracuseStep 5310481 = 3982861) B3982861
theorem B2795555 : Blo 1863633 2795555 := bstep (se 1 (by rfl) ⟨2096666, by rfl⟩ : syracuseStep 2795555 = 4193333) B4193333
theorem B2795585 : Blo 1863633 2795585 := bstep (se 2 (by rfl) ⟨1048344, by rfl⟩ : syracuseStep 2795585 = 2096689) B2096689
theorem B3188801 : Blo 1863633 3188801 := bstep (se 2 (by rfl) ⟨1195800, by rfl⟩ : syracuseStep 3188801 = 2391601) B2391601
theorem B2795603 : Blo 1863633 2795603 := bstep (se 1 (by rfl) ⟨2096702, by rfl⟩ : syracuseStep 2795603 = 4193405) B4193405
theorem B2795633 : Blo 1863633 2795633 := bstep (se 2 (by rfl) ⟨1048362, by rfl⟩ : syracuseStep 2795633 = 2096725) B2096725
theorem B4196465 : Blo 1863633 4196465 := bstep (se 2 (by rfl) ⟨1573674, by rfl⟩ : syracuseStep 4196465 = 3147349) B3147349
theorem B3147889 : Blo 1863633 3147889 := bstep (se 2 (by rfl) ⟨1180458, by rfl⟩ : syracuseStep 3147889 = 2360917) B2360917
theorem B21006449 : Blo 1863633 21006449 := bstep (se 2 (by rfl) ⟨7877418, by rfl⟩ : syracuseStep 21006449 = 15754837) B15754837
theorem B2795651 : Blo 1863633 2795651 := bstep (se 1 (by rfl) ⟨2096738, by rfl⟩ : syracuseStep 2795651 = 4193477) B4193477
theorem B4196483 : Blo 1863633 4196483 := bstep (se 1 (by rfl) ⟨3147362, by rfl⟩ : syracuseStep 4196483 = 6294725) B6294725
theorem B6293645 : Blo 1863633 6293645 := bstep (se 3 (by rfl) ⟨1180058, by rfl⟩ : syracuseStep 6293645 = 2360117) B2360117
theorem B3147923 : Blo 1863633 3147923 := bstep (se 1 (by rfl) ⟨2360942, by rfl⟩ : syracuseStep 3147923 = 4721885) B4721885
theorem B2795681 : Blo 1863633 2795681 := bstep (se 2 (by rfl) ⟨1048380, by rfl⟩ : syracuseStep 2795681 = 2096761) B2096761
theorem B5040301 : Blo 1863633 5040301 := bstep (se 3 (by rfl) ⟨945056, by rfl⟩ : syracuseStep 5040301 = 1890113) B1890113
theorem B2795699 : Blo 1863633 2795699 := bstep (se 1 (by rfl) ⟨2096774, by rfl⟩ : syracuseStep 2795699 = 4193549) B4193549
theorem B6293699 : Blo 1863633 6293699 := bstep (se 1 (by rfl) ⟨4720274, by rfl⟩ : syracuseStep 6293699 = 9440549) B9440549
theorem B2795729 : Blo 1863633 2795729 := bstep (se 2 (by rfl) ⟨1048398, by rfl⟩ : syracuseStep 2795729 = 2096797) B2096797
theorem B2795747 : Blo 1863633 2795747 := bstep (se 1 (by rfl) ⟨2096810, by rfl⟩ : syracuseStep 2795747 = 4193621) B4193621
theorem B8071409 : Blo 1863633 8071409 := bstep (se 2 (by rfl) ⟨3026778, by rfl⟩ : syracuseStep 8071409 = 6053557) B6053557
theorem B2795777 : Blo 1863633 2795777 := bstep (se 2 (by rfl) ⟨1048416, by rfl⟩ : syracuseStep 2795777 = 2096833) B2096833
theorem B4720913 : Blo 1863633 4720913 := bstep (se 2 (by rfl) ⟨1770342, by rfl⟩ : syracuseStep 4720913 = 3540685) B3540685
theorem B2795795 : Blo 1863633 2795795 := bstep (se 1 (by rfl) ⟨2096846, by rfl⟩ : syracuseStep 2795795 = 4193693) B4193693
theorem B3148051 : Blo 1863633 3148051 := bstep (se 1 (by rfl) ⟨2361038, by rfl⟩ : syracuseStep 3148051 = 4722077) B4722077
theorem B5310755 : Blo 1863633 5310755 := bstep (se 1 (by rfl) ⟨3983066, by rfl⟩ : syracuseStep 5310755 = 7966133) B7966133
theorem B2795825 : Blo 1863633 2795825 := bstep (se 2 (by rfl) ⟨1048434, by rfl⟩ : syracuseStep 2795825 = 2096869) B2096869
theorem B2795843 : Blo 1863633 2795843 := bstep (se 1 (by rfl) ⟨2096882, by rfl⟩ : syracuseStep 2795843 = 4193765) B4193765
theorem B4720963 : Blo 1863633 4720963 := bstep (se 1 (by rfl) ⟨3540722, by rfl⟩ : syracuseStep 4720963 = 7081445) B7081445
theorem B3541315 : Blo 1863633 3541315 := bstep (se 1 (by rfl) ⟨2655986, by rfl⟩ : syracuseStep 3541315 = 5311973) B5311973
theorem B3189073 : Blo 1863633 3189073 := bstep (se 2 (by rfl) ⟨1195902, by rfl⟩ : syracuseStep 3189073 = 2391805) B2391805
theorem B2795873 : Blo 1863633 2795873 := bstep (se 2 (by rfl) ⟨1048452, by rfl⟩ : syracuseStep 2795873 = 2096905) B2096905
theorem B3361123 : Blo 1863633 3361123 := bstep (se 1 (by rfl) ⟨2520842, by rfl⟩ : syracuseStep 3361123 = 5041685) B5041685
theorem B2795891 : Blo 1863633 2795891 := bstep (se 1 (by rfl) ⟨2096918, by rfl⟩ : syracuseStep 2795891 = 4193837) B4193837
theorem B14166413 : Blo 1863633 14166413 := bstep (se 3 (by rfl) ⟨2656202, by rfl⟩ : syracuseStep 14166413 = 5312405) B5312405
theorem B2795921 : Blo 1863633 2795921 := bstep (se 2 (by rfl) ⟨1048470, by rfl⟩ : syracuseStep 2795921 = 2096941) B2096941
theorem B4196753 : Blo 1863633 4196753 := bstep (se 2 (by rfl) ⟨1573782, by rfl⟩ : syracuseStep 4196753 = 3147565) B3147565
theorem B3148193 : Blo 1863633 3148193 := bstep (se 2 (by rfl) ⟨1180572, by rfl⟩ : syracuseStep 3148193 = 2361145) B2361145
theorem B2795939 : Blo 1863633 2795939 := bstep (se 1 (by rfl) ⟨2096954, by rfl⟩ : syracuseStep 2795939 = 4193909) B4193909
theorem B4196771 : Blo 1863633 4196771 := bstep (se 1 (by rfl) ⟨3147578, by rfl⟩ : syracuseStep 4196771 = 6295157) B6295157
theorem B2795969 : Blo 1863633 2795969 := bstep (se 2 (by rfl) ⟨1048488, by rfl⟩ : syracuseStep 2795969 = 2096977) B2096977
theorem B4663747 : Blo 1863633 4663747 := bstep (se 1 (by rfl) ⟨3497810, by rfl⟩ : syracuseStep 4663747 = 6995621) B6995621
theorem B6293969 : Blo 1863633 6293969 := bstep (se 2 (by rfl) ⟨2360238, by rfl⟩ : syracuseStep 6293969 = 4720477) B4720477
theorem B4721105 : Blo 1863633 4721105 := bstep (se 2 (by rfl) ⟨1770414, by rfl⟩ : syracuseStep 4721105 = 3540829) B3540829
theorem B2795987 : Blo 1863633 2795987 := bstep (se 1 (by rfl) ⟨2096990, by rfl⟩ : syracuseStep 2795987 = 4193981) B4193981
theorem B5310947 : Blo 1863633 5310947 := bstep (se 1 (by rfl) ⟨3983210, by rfl⟩ : syracuseStep 5310947 = 7966421) B7966421
theorem B3983843 : Blo 1863633 3983843 := bstep (se 1 (by rfl) ⟨2987882, by rfl⟩ : syracuseStep 3983843 = 5975765) B5975765
theorem B3541475 : Blo 1863633 3541475 := bstep (se 1 (by rfl) ⟨2656106, by rfl⟩ : syracuseStep 3541475 = 5312213) B5312213
theorem B2796017 : Blo 1863633 2796017 := bstep (se 2 (by rfl) ⟨1048506, by rfl⟩ : syracuseStep 2796017 = 2097013) B2097013
theorem B2796035 : Blo 1863633 2796035 := bstep (se 1 (by rfl) ⟨2097026, by rfl⟩ : syracuseStep 2796035 = 4194053) B4194053
theorem B2796065 : Blo 1863633 2796065 := bstep (se 2 (by rfl) ⟨1048524, by rfl⟩ : syracuseStep 2796065 = 2097049) B2097049
theorem B2796083 : Blo 1863633 2796083 := bstep (se 1 (by rfl) ⟨2097062, by rfl⟩ : syracuseStep 2796083 = 4194125) B4194125
theorem B2796113 : Blo 1863633 2796113 := bstep (se 2 (by rfl) ⟨1048542, by rfl⟩ : syracuseStep 2796113 = 2097085) B2097085
theorem B2796131 : Blo 1863633 2796131 := bstep (se 1 (by rfl) ⟨2097098, by rfl⟩ : syracuseStep 2796131 = 4194197) B4194197
theorem B12757603 : Blo 1863633 12757603 := bstep (se 1 (by rfl) ⟨9568202, by rfl⟩ : syracuseStep 12757603 = 19136405) B19136405
theorem B2796161 : Blo 1863633 2796161 := bstep (se 2 (by rfl) ⟨1048560, by rfl⟩ : syracuseStep 2796161 = 2097121) B2097121
theorem B10619525 : Blo 1863633 10619525 := bstep (se 4 (by rfl) ⟨995580, by rfl⟩ : syracuseStep 10619525 = 1991161) B1991161
theorem B2796179 : Blo 1863633 2796179 := bstep (se 1 (by rfl) ⟨2097134, by rfl⟩ : syracuseStep 2796179 = 4194269) B4194269
theorem B5106349 : Blo 1863633 5106349 := bstep (se 3 (by rfl) ⟨957440, by rfl⟩ : syracuseStep 5106349 = 1914881) B1914881
theorem B2796209 : Blo 1863633 2796209 := bstep (se 2 (by rfl) ⟨1048578, by rfl⟩ : syracuseStep 2796209 = 2097157) B2097157
theorem B4197041 : Blo 1863633 4197041 := bstep (se 2 (by rfl) ⟨1573890, by rfl⟩ : syracuseStep 4197041 = 3147781) B3147781
theorem B2796227 : Blo 1863633 2796227 := bstep (se 1 (by rfl) ⟨2097170, by rfl⟩ : syracuseStep 2796227 = 4194341) B4194341
theorem B4197059 : Blo 1863633 4197059 := bstep (se 1 (by rfl) ⟨3147794, by rfl⟩ : syracuseStep 4197059 = 6295589) B6295589
theorem B2796257 : Blo 1863633 2796257 := bstep (se 2 (by rfl) ⟨1048596, by rfl⟩ : syracuseStep 2796257 = 2097193) B2097193
theorem B2796275 : Blo 1863633 2796275 := bstep (se 1 (by rfl) ⟨2097206, by rfl⟩ : syracuseStep 2796275 = 4194413) B4194413
theorem B5745421 : Blo 1863633 5745421 := bstep (se 3 (by rfl) ⟨1077266, by rfl⟩ : syracuseStep 5745421 = 2154533) B2154533
theorem B2796305 : Blo 1863633 2796305 := bstep (se 2 (by rfl) ⟨1048614, by rfl⟩ : syracuseStep 2796305 = 2097229) B2097229
theorem B2796323 : Blo 1863633 2796323 := bstep (se 1 (by rfl) ⟨2097242, by rfl⟩ : syracuseStep 2796323 = 4194485) B4194485
theorem B2239283 : Blo 1863633 2239283 := bstep (se 1 (by rfl) ⟨1679462, by rfl⟩ : syracuseStep 2239283 = 3358925) B3358925
theorem B2796353 : Blo 1863633 2796353 := bstep (se 2 (by rfl) ⟨1048632, by rfl⟩ : syracuseStep 2796353 = 2097265) B2097265
theorem B2796371 : Blo 1863633 2796371 := bstep (se 1 (by rfl) ⟨2097278, by rfl⟩ : syracuseStep 2796371 = 4194557) B4194557
theorem B15928163 : Blo 1863633 15928163 := bstep (se 1 (by rfl) ⟨11946122, by rfl⟩ : syracuseStep 15928163 = 23892245) B23892245
theorem B2796401 : Blo 1863633 2796401 := bstep (se 2 (by rfl) ⟨1048650, by rfl⟩ : syracuseStep 2796401 = 2097301) B2097301
theorem B2796419 : Blo 1863633 2796419 := bstep (se 1 (by rfl) ⟨2097314, by rfl⟩ : syracuseStep 2796419 = 4194629) B4194629
theorem B2796449 : Blo 1863633 2796449 := bstep (se 2 (by rfl) ⟨1048668, by rfl⟩ : syracuseStep 2796449 = 2097337) B2097337
theorem B2796467 : Blo 1863633 2796467 := bstep (se 1 (by rfl) ⟨2097350, by rfl⟩ : syracuseStep 2796467 = 4194701) B4194701
theorem B2796497 : Blo 1863633 2796497 := bstep (se 2 (by rfl) ⟨1048686, by rfl⟩ : syracuseStep 2796497 = 2097373) B2097373
theorem B4197329 : Blo 1863633 4197329 := bstep (se 2 (by rfl) ⟨1573998, by rfl⟩ : syracuseStep 4197329 = 3147997) B3147997
theorem B2796515 : Blo 1863633 2796515 := bstep (se 1 (by rfl) ⟨2097386, by rfl⟩ : syracuseStep 2796515 = 4194773) B4194773
theorem B4197347 : Blo 1863633 4197347 := bstep (se 1 (by rfl) ⟨3148010, by rfl⟩ : syracuseStep 4197347 = 6296021) B6296021
theorem B6294509 : Blo 1863633 6294509 := bstep (se 3 (by rfl) ⟨1180220, by rfl⟩ : syracuseStep 6294509 = 2360441) B2360441
theorem B5975021 : Blo 1863633 5975021 := bstep (se 3 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 5975021 = 2240633) B2240633
theorem B3779569 : Blo 1863633 3779569 := bstep (se 2 (by rfl) ⟨1417338, by rfl⟩ : syracuseStep 3779569 = 2834677) B2834677
theorem B2796545 : Blo 1863633 2796545 := bstep (se 2 (by rfl) ⟨1048704, by rfl⟩ : syracuseStep 2796545 = 2097409) B2097409
theorem B2796563 : Blo 1863633 2796563 := bstep (se 1 (by rfl) ⟨2097422, by rfl⟩ : syracuseStep 2796563 = 4194845) B4194845
theorem B6294563 : Blo 1863633 6294563 := bstep (se 1 (by rfl) ⟨4720922, by rfl⟩ : syracuseStep 6294563 = 9441845) B9441845
theorem B5827619 : Blo 1863633 5827619 := bstep (se 1 (by rfl) ⟨4370714, by rfl⟩ : syracuseStep 5827619 = 8741429) B8741429
theorem B2796593 : Blo 1863633 2796593 := bstep (se 2 (by rfl) ⟨1048722, by rfl⟩ : syracuseStep 2796593 = 2097445) B2097445
theorem B47803445 : Blo 1863633 47803445 := bstep (se 5 (by rfl) ⟨2240786, by rfl⟩ : syracuseStep 47803445 = 4481573) B4481573
theorem B35859509 : Blo 1863633 35859509 := bstep (se 5 (by rfl) ⟨1680914, by rfl⟩ : syracuseStep 35859509 = 3361829) B3361829
theorem B2796611 : Blo 1863633 2796611 := bstep (se 1 (by rfl) ⟨2097458, by rfl⟩ : syracuseStep 2796611 = 4194917) B4194917
theorem B10619981 : Blo 1863633 10619981 := bstep (se 3 (by rfl) ⟨1991246, by rfl⟩ : syracuseStep 10619981 = 3982493) B3982493
theorem B7965773 : Blo 1863633 7965773 := bstep (se 3 (by rfl) ⟨1493582, by rfl⟩ : syracuseStep 7965773 = 2987165) B2987165
theorem B2796641 : Blo 1863633 2796641 := bstep (se 2 (by rfl) ⟨1048740, by rfl⟩ : syracuseStep 2796641 = 2097481) B2097481
theorem B2796659 : Blo 1863633 2796659 := bstep (se 1 (by rfl) ⟨2097494, by rfl⟩ : syracuseStep 2796659 = 4194989) B4194989
theorem B2796689 : Blo 1863633 2796689 := bstep (se 2 (by rfl) ⟨1048758, by rfl⟩ : syracuseStep 2796689 = 2097517) B2097517
theorem B2796707 : Blo 1863633 2796707 := bstep (se 1 (by rfl) ⟨2097530, by rfl⟩ : syracuseStep 2796707 = 4195061) B4195061
theorem B11947171 : Blo 1863633 11947171 := bstep (se 1 (by rfl) ⟨8960378, by rfl⟩ : syracuseStep 11947171 = 17920757) B17920757
theorem B2796737 : Blo 1863633 2796737 := bstep (se 2 (by rfl) ⟨1048776, by rfl⟩ : syracuseStep 2796737 = 2097553) B2097553
theorem B2796755 : Blo 1863633 2796755 := bstep (se 1 (by rfl) ⟨2097566, by rfl⟩ : syracuseStep 2796755 = 4195133) B4195133
theorem B2796785 : Blo 1863633 2796785 := bstep (se 2 (by rfl) ⟨1048794, by rfl⟩ : syracuseStep 2796785 = 2097589) B2097589
theorem B4197617 : Blo 1863633 4197617 := bstep (se 2 (by rfl) ⟨1574106, by rfl⟩ : syracuseStep 4197617 = 3148213) B3148213
theorem B2796803 : Blo 1863633 2796803 := bstep (se 1 (by rfl) ⟨2097602, by rfl⟩ : syracuseStep 2796803 = 4195205) B4195205
theorem B4197635 : Blo 1863633 4197635 := bstep (se 1 (by rfl) ⟨3148226, by rfl⟩ : syracuseStep 4197635 = 6296453) B6296453
theorem B5311757 : Blo 1863633 5311757 := bstep (se 3 (by rfl) ⟨995954, by rfl⟩ : syracuseStep 5311757 = 1991909) B1991909
theorem B2796833 : Blo 1863633 2796833 := bstep (se 2 (by rfl) ⟨1048812, by rfl⟩ : syracuseStep 2796833 = 2097625) B2097625
theorem B6294833 : Blo 1863633 6294833 := bstep (se 2 (by rfl) ⟨2360562, by rfl⟩ : syracuseStep 6294833 = 4721125) B4721125
theorem B2796851 : Blo 1863633 2796851 := bstep (se 1 (by rfl) ⟨2097638, by rfl⟩ : syracuseStep 2796851 = 4195277) B4195277
theorem B2796881 : Blo 1863633 2796881 := bstep (se 2 (by rfl) ⟨1048830, by rfl⟩ : syracuseStep 2796881 = 2097661) B2097661
theorem B2796899 : Blo 1863633 2796899 := bstep (se 1 (by rfl) ⟨2097674, by rfl⟩ : syracuseStep 2796899 = 4195349) B4195349
theorem B2796929 : Blo 1863633 2796929 := bstep (se 2 (by rfl) ⟨1048848, by rfl⟩ : syracuseStep 2796929 = 2097697) B2097697
theorem B2796947 : Blo 1863633 2796947 := bstep (se 1 (by rfl) ⟨2097710, by rfl⟩ : syracuseStep 2796947 = 4195421) B4195421
theorem B2796977 : Blo 1863633 2796977 := bstep (se 2 (by rfl) ⟨1048866, by rfl⟩ : syracuseStep 2796977 = 2097733) B2097733
theorem B4722097 : Blo 1863633 4722097 := bstep (se 2 (by rfl) ⟨1770786, by rfl⟩ : syracuseStep 4722097 = 3541573) B3541573
theorem B2796995 : Blo 1863633 2796995 := bstep (se 1 (by rfl) ⟨2097746, by rfl⟩ : syracuseStep 2796995 = 4195493) B4195493
theorem B5311939 : Blo 1863633 5311939 := bstep (se 1 (by rfl) ⟨3983954, by rfl⟩ : syracuseStep 5311939 = 7967909) B7967909
theorem B17018309 : Blo 1863633 17018309 := bstep (se 4 (by rfl) ⟨1595466, by rfl⟩ : syracuseStep 17018309 = 3190933) B3190933
theorem B12758477 : Blo 1863633 12758477 := bstep (se 3 (by rfl) ⟨2392214, by rfl⟩ : syracuseStep 12758477 = 4784429) B4784429
theorem B2797025 : Blo 1863633 2797025 := bstep (se 2 (by rfl) ⟨1048884, by rfl⟩ : syracuseStep 2797025 = 2097769) B2097769
theorem B2797043 : Blo 1863633 2797043 := bstep (se 1 (by rfl) ⟨2097782, by rfl⟩ : syracuseStep 2797043 = 4195565) B4195565
theorem B2797073 : Blo 1863633 2797073 := bstep (se 2 (by rfl) ⟨1048902, by rfl⟩ : syracuseStep 2797073 = 2097805) B2097805
theorem B2797091 : Blo 1863633 2797091 := bstep (se 1 (by rfl) ⟨2097818, by rfl⟩ : syracuseStep 2797091 = 4195637) B4195637
theorem B2797121 : Blo 1863633 2797121 := bstep (se 2 (by rfl) ⟨1048920, by rfl⟩ : syracuseStep 2797121 = 2097841) B2097841
theorem B2797139 : Blo 1863633 2797139 := bstep (se 1 (by rfl) ⟨2097854, by rfl⟩ : syracuseStep 2797139 = 4195709) B4195709
theorem B2797169 : Blo 1863633 2797169 := bstep (se 2 (by rfl) ⟨1048938, by rfl⟩ : syracuseStep 2797169 = 2097877) B2097877
theorem B2797187 : Blo 1863633 2797187 := bstep (se 1 (by rfl) ⟨2097890, by rfl⟩ : syracuseStep 2797187 = 4195781) B4195781
theorem B7081613 : Blo 1863633 7081613 := bstep (se 3 (by rfl) ⟨1327802, by rfl⟩ : syracuseStep 7081613 = 2655605) B2655605
theorem B2797217 : Blo 1863633 2797217 := bstep (se 2 (by rfl) ⟨1048956, by rfl⟩ : syracuseStep 2797217 = 2097913) B2097913
theorem B2797235 : Blo 1863633 2797235 := bstep (se 1 (by rfl) ⟨2097926, by rfl⟩ : syracuseStep 2797235 = 4195853) B4195853
theorem B2985665 : Blo 1863633 2985665 := bstep (se 2 (by rfl) ⟨1119624, by rfl⟩ : syracuseStep 2985665 = 2239249) B2239249
theorem B4722371 : Blo 1863633 4722371 := bstep (se 1 (by rfl) ⟨3541778, by rfl⟩ : syracuseStep 4722371 = 7083557) B7083557
theorem B2797265 : Blo 1863633 2797265 := bstep (se 2 (by rfl) ⟨1048974, by rfl⟩ : syracuseStep 2797265 = 2097949) B2097949
theorem B2797283 : Blo 1863633 2797283 := bstep (se 1 (by rfl) ⟨2097962, by rfl⟩ : syracuseStep 2797283 = 4195925) B4195925
theorem B5041901 : Blo 1863633 5041901 := bstep (se 3 (by rfl) ⟨945356, by rfl⟩ : syracuseStep 5041901 = 1890713) B1890713
theorem B2797313 : Blo 1863633 2797313 := bstep (se 2 (by rfl) ⟨1048992, by rfl⟩ : syracuseStep 2797313 = 2097985) B2097985
theorem B3780355 : Blo 1863633 3780355 := bstep (se 1 (by rfl) ⟨2835266, by rfl⟩ : syracuseStep 3780355 = 5670533) B5670533
theorem B2797331 : Blo 1863633 2797331 := bstep (se 1 (by rfl) ⟨2097998, by rfl⟩ : syracuseStep 2797331 = 4195997) B4195997
theorem B2797361 : Blo 1863633 2797361 := bstep (se 2 (by rfl) ⟨1049010, by rfl⟩ : syracuseStep 2797361 = 2098021) B2098021
theorem B2797379 : Blo 1863633 2797379 := bstep (se 1 (by rfl) ⟨2098034, by rfl⟩ : syracuseStep 2797379 = 4196069) B4196069
theorem B6295373 : Blo 1863633 6295373 := bstep (se 3 (by rfl) ⟨1180382, by rfl⟩ : syracuseStep 6295373 = 2360765) B2360765
theorem B2797409 : Blo 1863633 2797409 := bstep (se 2 (by rfl) ⟨1049028, by rfl⟩ : syracuseStep 2797409 = 2098057) B2098057
theorem B2797427 : Blo 1863633 2797427 := bstep (se 1 (by rfl) ⟨2098070, by rfl⟩ : syracuseStep 2797427 = 4196141) B4196141
theorem B6295427 : Blo 1863633 6295427 := bstep (se 1 (by rfl) ⟨4721570, by rfl⟩ : syracuseStep 6295427 = 9443141) B9443141
theorem B19132301 : Blo 1863633 19132301 := bstep (se 3 (by rfl) ⟨3587306, by rfl⟩ : syracuseStep 19132301 = 7174613) B7174613
theorem B2797457 : Blo 1863633 2797457 := bstep (se 2 (by rfl) ⟨1049046, by rfl⟩ : syracuseStep 2797457 = 2098093) B2098093
theorem B2797475 : Blo 1863633 2797475 := bstep (se 1 (by rfl) ⟨2098106, by rfl⟩ : syracuseStep 2797475 = 4196213) B4196213
theorem B5312429 : Blo 1863633 5312429 := bstep (se 3 (by rfl) ⟨996080, by rfl⟩ : syracuseStep 5312429 = 1992161) B1992161
theorem B2797505 : Blo 1863633 2797505 := bstep (se 2 (by rfl) ⟨1049064, by rfl⟩ : syracuseStep 2797505 = 2098129) B2098129
theorem B1863635 : Blo 1863633 1863635 := bstep (se 1 (by rfl) ⟨1397726, by rfl⟩ : syracuseStep 1863635 = 2795453) B2795453
theorem B2797523 : Blo 1863633 2797523 := bstep (se 1 (by rfl) ⟨2098142, by rfl⟩ : syracuseStep 2797523 = 4196285) B4196285
theorem B1863651 : Blo 1863633 1863651 := bstep (se 1 (by rfl) ⟨1397738, by rfl⟩ : syracuseStep 1863651 = 2795477) B2795477
theorem B18157553 : Blo 1863633 18157553 := bstep (se 2 (by rfl) ⟨6809082, by rfl⟩ : syracuseStep 18157553 = 13618165) B13618165
theorem B2797553 : Blo 1863633 2797553 := bstep (se 2 (by rfl) ⟨1049082, by rfl⟩ : syracuseStep 2797553 = 2098165) B2098165
theorem B1863667 : Blo 1863633 1863667 := bstep (se 1 (by rfl) ⟨1397750, by rfl⟩ : syracuseStep 1863667 = 2795501) B2795501
theorem B1863683 : Blo 1863633 1863683 := bstep (se 1 (by rfl) ⟨1397762, by rfl⟩ : syracuseStep 1863683 = 2795525) B2795525
theorem B2797571 : Blo 1863633 2797571 := bstep (se 1 (by rfl) ⟨2098178, by rfl⟩ : syracuseStep 2797571 = 4196357) B4196357
theorem B1863699 : Blo 1863633 1863699 := bstep (se 1 (by rfl) ⟨1397774, by rfl⟩ : syracuseStep 1863699 = 2795549) B2795549
theorem B2797601 : Blo 1863633 2797601 := bstep (se 2 (by rfl) ⟨1049100, by rfl⟩ : syracuseStep 2797601 = 2098201) B2098201
theorem B1863715 : Blo 1863633 1863715 := bstep (se 1 (by rfl) ⟨1397786, by rfl⟩ : syracuseStep 1863715 = 2795573) B2795573
theorem B1863731 : Blo 1863633 1863731 := bstep (se 1 (by rfl) ⟨1397798, by rfl⟩ : syracuseStep 1863731 = 2795597) B2795597
theorem B2797619 : Blo 1863633 2797619 := bstep (se 1 (by rfl) ⟨2098214, by rfl⟩ : syracuseStep 2797619 = 4196429) B4196429
theorem B1863747 : Blo 1863633 1863747 := bstep (se 1 (by rfl) ⟨1397810, by rfl⟩ : syracuseStep 1863747 = 2795621) B2795621
theorem B6721613 : Blo 1863633 6721613 := bstep (se 3 (by rfl) ⟨1260302, by rfl⟩ : syracuseStep 6721613 = 2520605) B2520605
theorem B2797649 : Blo 1863633 2797649 := bstep (se 2 (by rfl) ⟨1049118, by rfl⟩ : syracuseStep 2797649 = 2098237) B2098237
theorem B1863763 : Blo 1863633 1863763 := bstep (se 1 (by rfl) ⟨1397822, by rfl⟩ : syracuseStep 1863763 = 2795645) B2795645
theorem B1863779 : Blo 1863633 1863779 := bstep (se 1 (by rfl) ⟨1397834, by rfl⟩ : syracuseStep 1863779 = 2795669) B2795669
theorem B2797667 : Blo 1863633 2797667 := bstep (se 1 (by rfl) ⟨2098250, by rfl⟩ : syracuseStep 2797667 = 4196501) B4196501
theorem B1863795 : Blo 1863633 1863795 := bstep (se 1 (by rfl) ⟨1397846, by rfl⟩ : syracuseStep 1863795 = 2795693) B2795693
theorem B2797697 : Blo 1863633 2797697 := bstep (se 2 (by rfl) ⟨1049136, by rfl⟩ : syracuseStep 2797697 = 2098273) B2098273
theorem B1863811 : Blo 1863633 1863811 := bstep (se 1 (by rfl) ⟨1397858, by rfl⟩ : syracuseStep 1863811 = 2795717) B2795717
theorem B6295697 : Blo 1863633 6295697 := bstep (se 2 (by rfl) ⟨2360886, by rfl⟩ : syracuseStep 6295697 = 4721773) B4721773
theorem B1863827 : Blo 1863633 1863827 := bstep (se 1 (by rfl) ⟨1397870, by rfl⟩ : syracuseStep 1863827 = 2795741) B2795741
theorem B2797715 : Blo 1863633 2797715 := bstep (se 1 (by rfl) ⟨2098286, by rfl⟩ : syracuseStep 2797715 = 4196573) B4196573
theorem B1863843 : Blo 1863633 1863843 := bstep (se 1 (by rfl) ⟨1397882, by rfl⟩ : syracuseStep 1863843 = 2795765) B2795765
theorem B6721699 : Blo 1863633 6721699 := bstep (se 1 (by rfl) ⟨5041274, by rfl⟩ : syracuseStep 6721699 = 10082549) B10082549
theorem B2797745 : Blo 1863633 2797745 := bstep (se 2 (by rfl) ⟨1049154, by rfl⟩ : syracuseStep 2797745 = 2098309) B2098309
theorem B1863859 : Blo 1863633 1863859 := bstep (se 1 (by rfl) ⟨1397894, by rfl⟩ : syracuseStep 1863859 = 2795789) B2795789
theorem B1863875 : Blo 1863633 1863875 := bstep (se 1 (by rfl) ⟨1397906, by rfl⟩ : syracuseStep 1863875 = 2795813) B2795813
theorem B2797763 : Blo 1863633 2797763 := bstep (se 1 (by rfl) ⟨2098322, by rfl⟩ : syracuseStep 2797763 = 4196645) B4196645
theorem B1863891 : Blo 1863633 1863891 := bstep (se 1 (by rfl) ⟨1397918, by rfl⟩ : syracuseStep 1863891 = 2795837) B2795837
theorem B2797793 : Blo 1863633 2797793 := bstep (se 2 (by rfl) ⟨1049172, by rfl⟩ : syracuseStep 2797793 = 2098345) B2098345
theorem B1863907 : Blo 1863633 1863907 := bstep (se 1 (by rfl) ⟨1397930, by rfl⟩ : syracuseStep 1863907 = 2795861) B2795861
theorem B9441521 : Blo 1863633 9441521 := bstep (se 2 (by rfl) ⟨3540570, by rfl⟩ : syracuseStep 9441521 = 7081141) B7081141
theorem B1863923 : Blo 1863633 1863923 := bstep (se 1 (by rfl) ⟨1397942, by rfl⟩ : syracuseStep 1863923 = 2795885) B2795885
theorem B2797811 : Blo 1863633 2797811 := bstep (se 1 (by rfl) ⟨2098358, by rfl⟩ : syracuseStep 2797811 = 4196717) B4196717
theorem B1863939 : Blo 1863633 1863939 := bstep (se 1 (by rfl) ⟨1397954, by rfl⟩ : syracuseStep 1863939 = 2795909) B2795909
theorem B5746961 : Blo 1863633 5746961 := bstep (se 2 (by rfl) ⟨2155110, by rfl⟩ : syracuseStep 5746961 = 4310221) B4310221
theorem B1863955 : Blo 1863633 1863955 := bstep (se 1 (by rfl) ⟨1397966, by rfl⟩ : syracuseStep 1863955 = 2795933) B2795933
theorem B2797841 : Blo 1863633 2797841 := bstep (se 2 (by rfl) ⟨1049190, by rfl⟩ : syracuseStep 2797841 = 2098381) B2098381
theorem B1863971 : Blo 1863633 1863971 := bstep (se 1 (by rfl) ⟨1397978, by rfl⟩ : syracuseStep 1863971 = 2795957) B2795957
theorem B2797859 : Blo 1863633 2797859 := bstep (se 1 (by rfl) ⟨2098394, by rfl⟩ : syracuseStep 2797859 = 4196789) B4196789
theorem B6467885 : Blo 1863633 6467885 := bstep (se 3 (by rfl) ⟨1212728, by rfl⟩ : syracuseStep 6467885 = 2425457) B2425457
theorem B1863987 : Blo 1863633 1863987 := bstep (se 1 (by rfl) ⟨1397990, by rfl⟩ : syracuseStep 1863987 = 2795981) B2795981
theorem B2797889 : Blo 1863633 2797889 := bstep (se 2 (by rfl) ⟨1049208, by rfl⟩ : syracuseStep 2797889 = 2098417) B2098417
theorem B1864003 : Blo 1863633 1864003 := bstep (se 1 (by rfl) ⟨1398002, by rfl⟩ : syracuseStep 1864003 = 2796005) B2796005
theorem B1864019 : Blo 1863633 1864019 := bstep (se 1 (by rfl) ⟨1398014, by rfl⟩ : syracuseStep 1864019 = 2796029) B2796029
theorem B2797907 : Blo 1863633 2797907 := bstep (se 1 (by rfl) ⟨2098430, by rfl⟩ : syracuseStep 2797907 = 4196861) B4196861
theorem B1864035 : Blo 1863633 1864035 := bstep (se 1 (by rfl) ⟨1398026, by rfl⟩ : syracuseStep 1864035 = 2796053) B2796053
theorem B21229937 : Blo 1863633 21229937 := bstep (se 2 (by rfl) ⟨7961226, by rfl⟩ : syracuseStep 21229937 = 15922453) B15922453
theorem B11948401 : Blo 1863633 11948401 := bstep (se 2 (by rfl) ⟨4480650, by rfl⟩ : syracuseStep 11948401 = 8961301) B8961301
theorem B1864051 : Blo 1863633 1864051 := bstep (se 1 (by rfl) ⟨1398038, by rfl⟩ : syracuseStep 1864051 = 2796077) B2796077
theorem B2797937 : Blo 1863633 2797937 := bstep (se 2 (by rfl) ⟨1049226, by rfl⟩ : syracuseStep 2797937 = 2098453) B2098453
theorem B1864067 : Blo 1863633 1864067 := bstep (se 1 (by rfl) ⟨1398050, by rfl⟩ : syracuseStep 1864067 = 2796101) B2796101
theorem B2797955 : Blo 1863633 2797955 := bstep (se 1 (by rfl) ⟨2098466, by rfl⟩ : syracuseStep 2797955 = 4196933) B4196933
theorem B2691473 : Blo 1863633 2691473 := bstep (se 2 (by rfl) ⟨1009302, by rfl⟩ : syracuseStep 2691473 = 2018605) B2018605
theorem B1864083 : Blo 1863633 1864083 := bstep (se 1 (by rfl) ⟨1398062, by rfl⟩ : syracuseStep 1864083 = 2796125) B2796125
theorem B2797985 : Blo 1863633 2797985 := bstep (se 2 (by rfl) ⟨1049244, by rfl⟩ : syracuseStep 2797985 = 2098489) B2098489
theorem B1864099 : Blo 1863633 1864099 := bstep (se 1 (by rfl) ⟨1398074, by rfl⟩ : syracuseStep 1864099 = 2796149) B2796149
theorem B7082417 : Blo 1863633 7082417 := bstep (se 2 (by rfl) ⟨2655906, by rfl⟩ : syracuseStep 7082417 = 5311813) B5311813
theorem B1864115 : Blo 1863633 1864115 := bstep (se 1 (by rfl) ⟨1398086, by rfl⟩ : syracuseStep 1864115 = 2796173) B2796173
theorem B2798003 : Blo 1863633 2798003 := bstep (se 1 (by rfl) ⟨2098502, by rfl⟩ : syracuseStep 2798003 = 4197005) B4197005
theorem B1864131 : Blo 1863633 1864131 := bstep (se 1 (by rfl) ⟨1398098, by rfl⟩ : syracuseStep 1864131 = 2796197) B2796197
theorem B2798033 : Blo 1863633 2798033 := bstep (se 2 (by rfl) ⟨1049262, by rfl⟩ : syracuseStep 2798033 = 2098525) B2098525
theorem B1864147 : Blo 1863633 1864147 := bstep (se 1 (by rfl) ⟨1398110, by rfl⟩ : syracuseStep 1864147 = 2796221) B2796221
theorem B1864163 : Blo 1863633 1864163 := bstep (se 1 (by rfl) ⟨1398122, by rfl⟩ : syracuseStep 1864163 = 2796245) B2796245
theorem B2798051 : Blo 1863633 2798051 := bstep (se 1 (by rfl) ⟨2098538, by rfl⟩ : syracuseStep 2798051 = 4197077) B4197077
theorem B3830257 : Blo 1863633 3830257 := bstep (se 2 (by rfl) ⟨1436346, by rfl⟩ : syracuseStep 3830257 = 2872693) B2872693
theorem B1864179 : Blo 1863633 1864179 := bstep (se 1 (by rfl) ⟨1398134, by rfl⟩ : syracuseStep 1864179 = 2796269) B2796269
theorem B2798081 : Blo 1863633 2798081 := bstep (se 2 (by rfl) ⟨1049280, by rfl⟩ : syracuseStep 2798081 = 2098561) B2098561
theorem B1864195 : Blo 1863633 1864195 := bstep (se 1 (by rfl) ⟨1398146, by rfl⟩ : syracuseStep 1864195 = 2796293) B2796293
theorem B1864211 : Blo 1863633 1864211 := bstep (se 1 (by rfl) ⟨1398158, by rfl⟩ : syracuseStep 1864211 = 2796317) B2796317
theorem B2798099 : Blo 1863633 2798099 := bstep (se 1 (by rfl) ⟨2098574, by rfl⟩ : syracuseStep 2798099 = 4197149) B4197149
theorem B1864227 : Blo 1863633 1864227 := bstep (se 1 (by rfl) ⟨1398170, by rfl⟩ : syracuseStep 1864227 = 2796341) B2796341
theorem B5976611 : Blo 1863633 5976611 := bstep (se 1 (by rfl) ⟨4482458, by rfl⟩ : syracuseStep 5976611 = 8964917) B8964917
theorem B2798129 : Blo 1863633 2798129 := bstep (se 2 (by rfl) ⟨1049298, by rfl⟩ : syracuseStep 2798129 = 2098597) B2098597
theorem B1864243 : Blo 1863633 1864243 := bstep (se 1 (by rfl) ⟨1398182, by rfl⟩ : syracuseStep 1864243 = 2796365) B2796365
theorem B1864259 : Blo 1863633 1864259 := bstep (se 1 (by rfl) ⟨1398194, by rfl⟩ : syracuseStep 1864259 = 2796389) B2796389
theorem B2798147 : Blo 1863633 2798147 := bstep (se 1 (by rfl) ⟨2098610, by rfl⟩ : syracuseStep 2798147 = 4197221) B4197221
theorem B1864275 : Blo 1863633 1864275 := bstep (se 1 (by rfl) ⟨1398206, by rfl⟩ : syracuseStep 1864275 = 2796413) B2796413
theorem B2798177 : Blo 1863633 2798177 := bstep (se 2 (by rfl) ⟨1049316, by rfl⟩ : syracuseStep 2798177 = 2098633) B2098633
theorem B1864291 : Blo 1863633 1864291 := bstep (se 1 (by rfl) ⟨1398218, by rfl⟩ : syracuseStep 1864291 = 2796437) B2796437
theorem B1864307 : Blo 1863633 1864307 := bstep (se 1 (by rfl) ⟨1398230, by rfl⟩ : syracuseStep 1864307 = 2796461) B2796461
theorem B2798195 : Blo 1863633 2798195 := bstep (se 1 (by rfl) ⟨2098646, by rfl⟩ : syracuseStep 2798195 = 4197293) B4197293
theorem B1864323 : Blo 1863633 1864323 := bstep (se 1 (by rfl) ⟨1398242, by rfl⟩ : syracuseStep 1864323 = 2796485) B2796485
theorem B2798225 : Blo 1863633 2798225 := bstep (se 2 (by rfl) ⟨1049334, by rfl⟩ : syracuseStep 2798225 = 2098669) B2098669
theorem B1864339 : Blo 1863633 1864339 := bstep (se 1 (by rfl) ⟨1398254, by rfl⟩ : syracuseStep 1864339 = 2796509) B2796509
theorem B1864355 : Blo 1863633 1864355 := bstep (se 1 (by rfl) ⟨1398266, by rfl⟩ : syracuseStep 1864355 = 2796533) B2796533
theorem B2798243 : Blo 1863633 2798243 := bstep (se 1 (by rfl) ⟨2098682, by rfl⟩ : syracuseStep 2798243 = 4197365) B4197365
theorem B6296237 : Blo 1863633 6296237 := bstep (se 3 (by rfl) ⟨1180544, by rfl⟩ : syracuseStep 6296237 = 2361089) B2361089
theorem B1864371 : Blo 1863633 1864371 := bstep (se 1 (by rfl) ⟨1398278, by rfl⟩ : syracuseStep 1864371 = 2796557) B2796557
theorem B2798273 : Blo 1863633 2798273 := bstep (se 2 (by rfl) ⟨1049352, by rfl⟩ : syracuseStep 2798273 = 2098705) B2098705
theorem B1864387 : Blo 1863633 1864387 := bstep (se 1 (by rfl) ⟨1398290, by rfl⟩ : syracuseStep 1864387 = 2796581) B2796581
theorem B14160581 : Blo 1863633 14160581 := bstep (se 4 (by rfl) ⟨1327554, by rfl⟩ : syracuseStep 14160581 = 2655109) B2655109
theorem B1864403 : Blo 1863633 1864403 := bstep (se 1 (by rfl) ⟨1398302, by rfl⟩ : syracuseStep 1864403 = 2796605) B2796605
theorem B2798291 : Blo 1863633 2798291 := bstep (se 1 (by rfl) ⟨2098718, by rfl⟩ : syracuseStep 2798291 = 4197437) B4197437
theorem B1864419 : Blo 1863633 1864419 := bstep (se 1 (by rfl) ⟨1398314, by rfl⟩ : syracuseStep 1864419 = 2796629) B2796629
theorem B6296291 : Blo 1863633 6296291 := bstep (se 1 (by rfl) ⟨4722218, by rfl⟩ : syracuseStep 6296291 = 9444437) B9444437
theorem B2798321 : Blo 1863633 2798321 := bstep (se 2 (by rfl) ⟨1049370, by rfl⟩ : syracuseStep 2798321 = 2098741) B2098741
theorem B1864435 : Blo 1863633 1864435 := bstep (se 1 (by rfl) ⟨1398326, by rfl⟩ : syracuseStep 1864435 = 2796653) B2796653
theorem B1864451 : Blo 1863633 1864451 := bstep (se 1 (by rfl) ⟨1398338, by rfl⟩ : syracuseStep 1864451 = 2796677) B2796677
theorem B2798339 : Blo 1863633 2798339 := bstep (se 1 (by rfl) ⟨2098754, by rfl⟩ : syracuseStep 2798339 = 4197509) B4197509
theorem B1864467 : Blo 1863633 1864467 := bstep (se 1 (by rfl) ⟨1398350, by rfl⟩ : syracuseStep 1864467 = 2796701) B2796701
theorem B2798369 : Blo 1863633 2798369 := bstep (se 2 (by rfl) ⟨1049388, by rfl⟩ : syracuseStep 2798369 = 2098777) B2098777
theorem B1864483 : Blo 1863633 1864483 := bstep (se 1 (by rfl) ⟨1398362, by rfl⟩ : syracuseStep 1864483 = 2796725) B2796725
theorem B1864499 : Blo 1863633 1864499 := bstep (se 1 (by rfl) ⟨1398374, by rfl⟩ : syracuseStep 1864499 = 2796749) B2796749
theorem B2798387 : Blo 1863633 2798387 := bstep (se 1 (by rfl) ⟨2098790, by rfl⟩ : syracuseStep 2798387 = 4197581) B4197581
theorem B1864515 : Blo 1863633 1864515 := bstep (se 1 (by rfl) ⟨1398386, by rfl⟩ : syracuseStep 1864515 = 2796773) B2796773
theorem B2798417 : Blo 1863633 2798417 := bstep (se 2 (by rfl) ⟨1049406, by rfl⟩ : syracuseStep 2798417 = 2098813) B2098813
theorem B1864531 : Blo 1863633 1864531 := bstep (se 1 (by rfl) ⟨1398398, by rfl⟩ : syracuseStep 1864531 = 2796797) B2796797
theorem B1864547 : Blo 1863633 1864547 := bstep (se 1 (by rfl) ⟨1398410, by rfl⟩ : syracuseStep 1864547 = 2796821) B2796821
theorem B2798435 : Blo 1863633 2798435 := bstep (se 1 (by rfl) ⟨2098826, by rfl⟩ : syracuseStep 2798435 = 4197653) B4197653
theorem B1864563 : Blo 1863633 1864563 := bstep (se 1 (by rfl) ⟨1398422, by rfl⟩ : syracuseStep 1864563 = 2796845) B2796845
theorem B1864579 : Blo 1863633 1864579 := bstep (se 1 (by rfl) ⟨1398434, by rfl⟩ : syracuseStep 1864579 = 2796869) B2796869
theorem B1864595 : Blo 1863633 1864595 := bstep (se 1 (by rfl) ⟨1398446, by rfl⟩ : syracuseStep 1864595 = 2796893) B2796893
theorem B1864611 : Blo 1863633 1864611 := bstep (se 1 (by rfl) ⟨1398458, by rfl⟩ : syracuseStep 1864611 = 2796917) B2796917
theorem B1864627 : Blo 1863633 1864627 := bstep (se 1 (by rfl) ⟨1398470, by rfl⟩ : syracuseStep 1864627 = 2796941) B2796941
theorem B1864643 : Blo 1863633 1864643 := bstep (se 1 (by rfl) ⟨1398482, by rfl⟩ : syracuseStep 1864643 = 2796965) B2796965
theorem B1864659 : Blo 1863633 1864659 := bstep (se 1 (by rfl) ⟨1398494, by rfl⟩ : syracuseStep 1864659 = 2796989) B2796989
theorem B1864675 : Blo 1863633 1864675 := bstep (se 1 (by rfl) ⟨1398506, by rfl⟩ : syracuseStep 1864675 = 2797013) B2797013
theorem B1864691 : Blo 1863633 1864691 := bstep (se 1 (by rfl) ⟨1398518, by rfl⟩ : syracuseStep 1864691 = 2797037) B2797037
theorem B1864707 : Blo 1863633 1864707 := bstep (se 1 (by rfl) ⟨1398530, by rfl⟩ : syracuseStep 1864707 = 2797061) B2797061
theorem B1864723 : Blo 1863633 1864723 := bstep (se 1 (by rfl) ⟨1398542, by rfl⟩ : syracuseStep 1864723 = 2797085) B2797085
theorem B1864739 : Blo 1863633 1864739 := bstep (se 1 (by rfl) ⟨1398554, by rfl⟩ : syracuseStep 1864739 = 2797109) B2797109
theorem B1864755 : Blo 1863633 1864755 := bstep (se 1 (by rfl) ⟨1398566, by rfl⟩ : syracuseStep 1864755 = 2797133) B2797133
theorem B1864771 : Blo 1863633 1864771 := bstep (se 1 (by rfl) ⟨1398578, by rfl⟩ : syracuseStep 1864771 = 2797157) B2797157
theorem B2987075 : Blo 1863633 2987075 := bstep (se 1 (by rfl) ⟨2240306, by rfl⟩ : syracuseStep 2987075 = 4480613) B4480613
theorem B7083085 : Blo 1863633 7083085 := bstep (se 3 (by rfl) ⟨1328078, by rfl⟩ : syracuseStep 7083085 = 2656157) B2656157
theorem B1864787 : Blo 1863633 1864787 := bstep (se 1 (by rfl) ⟨1398590, by rfl⟩ : syracuseStep 1864787 = 2797181) B2797181
theorem B1864803 : Blo 1863633 1864803 := bstep (se 1 (by rfl) ⟨1398602, by rfl⟩ : syracuseStep 1864803 = 2797205) B2797205
theorem B1864819 : Blo 1863633 1864819 := bstep (se 1 (by rfl) ⟨1398614, by rfl⟩ : syracuseStep 1864819 = 2797229) B2797229
theorem B1864835 : Blo 1863633 1864835 := bstep (se 1 (by rfl) ⟨1398626, by rfl⟩ : syracuseStep 1864835 = 2797253) B2797253
theorem B1864851 : Blo 1863633 1864851 := bstep (se 1 (by rfl) ⟨1398638, by rfl⟩ : syracuseStep 1864851 = 2797277) B2797277
theorem B1864867 : Blo 1863633 1864867 := bstep (se 1 (by rfl) ⟨1398650, by rfl⟩ : syracuseStep 1864867 = 2797301) B2797301
theorem B1864883 : Blo 1863633 1864883 := bstep (se 1 (by rfl) ⟨1398662, by rfl⟩ : syracuseStep 1864883 = 2797325) B2797325
theorem B2987203 : Blo 1863633 2987203 := bstep (se 1 (by rfl) ⟨2240402, by rfl⟩ : syracuseStep 2987203 = 4480805) B4480805
theorem B1864899 : Blo 1863633 1864899 := bstep (se 1 (by rfl) ⟨1398674, by rfl⟩ : syracuseStep 1864899 = 2797349) B2797349
theorem B1864915 : Blo 1863633 1864915 := bstep (se 1 (by rfl) ⟨1398686, by rfl⟩ : syracuseStep 1864915 = 2797373) B2797373
theorem B1864931 : Blo 1863633 1864931 := bstep (se 1 (by rfl) ⟨1398698, by rfl⟩ : syracuseStep 1864931 = 2797397) B2797397
theorem B1864947 : Blo 1863633 1864947 := bstep (se 1 (by rfl) ⟨1398710, by rfl⟩ : syracuseStep 1864947 = 2797421) B2797421
theorem B1864963 : Blo 1863633 1864963 := bstep (se 1 (by rfl) ⟨1398722, by rfl⟩ : syracuseStep 1864963 = 2797445) B2797445
theorem B1864979 : Blo 1863633 1864979 := bstep (se 1 (by rfl) ⟨1398734, by rfl⟩ : syracuseStep 1864979 = 2797469) B2797469
theorem B1864995 : Blo 1863633 1864995 := bstep (se 1 (by rfl) ⟨1398746, by rfl⟩ : syracuseStep 1864995 = 2797493) B2797493
theorem B1865011 : Blo 1863633 1865011 := bstep (se 1 (by rfl) ⟨1398758, by rfl⟩ : syracuseStep 1865011 = 2797517) B2797517
theorem B1865027 : Blo 1863633 1865027 := bstep (se 1 (by rfl) ⟨1398770, by rfl⟩ : syracuseStep 1865027 = 2797541) B2797541
theorem B1865043 : Blo 1863633 1865043 := bstep (se 1 (by rfl) ⟨1398782, by rfl⟩ : syracuseStep 1865043 = 2797565) B2797565
theorem B1865059 : Blo 1863633 1865059 := bstep (se 1 (by rfl) ⟨1398794, by rfl⟩ : syracuseStep 1865059 = 2797589) B2797589
theorem B1865075 : Blo 1863633 1865075 := bstep (se 1 (by rfl) ⟨1398806, by rfl⟩ : syracuseStep 1865075 = 2797613) B2797613
theorem B1865091 : Blo 1863633 1865091 := bstep (se 1 (by rfl) ⟨1398818, by rfl⟩ : syracuseStep 1865091 = 2797637) B2797637
theorem B10614149 : Blo 1863633 10614149 := bstep (se 4 (by rfl) ⟨995076, by rfl⟩ : syracuseStep 10614149 = 1990153) B1990153
theorem B76567949 : Blo 1863633 76567949 := bstep (se 3 (by rfl) ⟨14356490, by rfl⟩ : syracuseStep 76567949 = 28712981) B28712981
theorem B1865107 : Blo 1863633 1865107 := bstep (se 1 (by rfl) ⟨1398830, by rfl⟩ : syracuseStep 1865107 = 2797661) B2797661
theorem B1865123 : Blo 1863633 1865123 := bstep (se 1 (by rfl) ⟨1398842, by rfl⟩ : syracuseStep 1865123 = 2797685) B2797685
theorem B2520497 : Blo 1863633 2520497 := bstep (se 2 (by rfl) ⟨945186, by rfl⟩ : syracuseStep 2520497 = 1890373) B1890373
theorem B1865139 : Blo 1863633 1865139 := bstep (se 1 (by rfl) ⟨1398854, by rfl⟩ : syracuseStep 1865139 = 2797709) B2797709
theorem B1865155 : Blo 1863633 1865155 := bstep (se 1 (by rfl) ⟨1398866, by rfl⟩ : syracuseStep 1865155 = 2797733) B2797733
theorem B1865171 : Blo 1863633 1865171 := bstep (se 1 (by rfl) ⟨1398878, by rfl⟩ : syracuseStep 1865171 = 2797757) B2797757
theorem B1865187 : Blo 1863633 1865187 := bstep (se 1 (by rfl) ⟨1398890, by rfl⟩ : syracuseStep 1865187 = 2797781) B2797781
theorem B26891747 : Blo 1863633 26891747 := bstep (se 1 (by rfl) ⟨20168810, by rfl⟩ : syracuseStep 26891747 = 40337621) B40337621
theorem B1865203 : Blo 1863633 1865203 := bstep (se 1 (by rfl) ⟨1398902, by rfl⟩ : syracuseStep 1865203 = 2797805) B2797805
theorem B1865219 : Blo 1863633 1865219 := bstep (se 1 (by rfl) ⟨1398914, by rfl⟩ : syracuseStep 1865219 = 2797829) B2797829
theorem B3233299 : Blo 1863633 3233299 := bstep (se 1 (by rfl) ⟨2424974, by rfl⟩ : syracuseStep 3233299 = 4849949) B4849949
theorem B1865235 : Blo 1863633 1865235 := bstep (se 1 (by rfl) ⟨1398926, by rfl⟩ : syracuseStep 1865235 = 2797853) B2797853
theorem B1865251 : Blo 1863633 1865251 := bstep (se 1 (by rfl) ⟨1398938, by rfl⟩ : syracuseStep 1865251 = 2797877) B2797877
theorem B1865267 : Blo 1863633 1865267 := bstep (se 1 (by rfl) ⟨1398950, by rfl⟩ : syracuseStep 1865267 = 2797901) B2797901
theorem B1865283 : Blo 1863633 1865283 := bstep (se 1 (by rfl) ⟨1398962, by rfl⟩ : syracuseStep 1865283 = 2797925) B2797925
theorem B1865299 : Blo 1863633 1865299 := bstep (se 1 (by rfl) ⟨1398974, by rfl⟩ : syracuseStep 1865299 = 2797949) B2797949
theorem B1865315 : Blo 1863633 1865315 := bstep (se 1 (by rfl) ⟨1398986, by rfl⟩ : syracuseStep 1865315 = 2797973) B2797973
theorem B1865331 : Blo 1863633 1865331 := bstep (se 1 (by rfl) ⟨1398998, by rfl⟩ : syracuseStep 1865331 = 2797997) B2797997
theorem B1865347 : Blo 1863633 1865347 := bstep (se 1 (by rfl) ⟨1399010, by rfl⟩ : syracuseStep 1865347 = 2798021) B2798021
theorem B1865363 : Blo 1863633 1865363 := bstep (se 1 (by rfl) ⟨1399022, by rfl⟩ : syracuseStep 1865363 = 2798045) B2798045
theorem B9442979 : Blo 1863633 9442979 := bstep (se 1 (by rfl) ⟨7082234, by rfl⟩ : syracuseStep 9442979 = 14164469) B14164469
theorem B1865379 : Blo 1863633 1865379 := bstep (se 1 (by rfl) ⟨1399034, by rfl⟩ : syracuseStep 1865379 = 2798069) B2798069
theorem B1865395 : Blo 1863633 1865395 := bstep (se 1 (by rfl) ⟨1399046, by rfl⟩ : syracuseStep 1865395 = 2798093) B2798093
theorem B1865411 : Blo 1863633 1865411 := bstep (se 1 (by rfl) ⟨1399058, by rfl⟩ : syracuseStep 1865411 = 2798117) B2798117
theorem B1865427 : Blo 1863633 1865427 := bstep (se 1 (by rfl) ⟨1399070, by rfl⟩ : syracuseStep 1865427 = 2798141) B2798141
theorem B1865443 : Blo 1863633 1865443 := bstep (se 1 (by rfl) ⟨1399082, by rfl⟩ : syracuseStep 1865443 = 2798165) B2798165
theorem B2987761 : Blo 1863633 2987761 := bstep (se 2 (by rfl) ⟨1120410, by rfl⟩ : syracuseStep 2987761 = 2240821) B2240821
theorem B1865459 : Blo 1863633 1865459 := bstep (se 1 (by rfl) ⟨1399094, by rfl⟩ : syracuseStep 1865459 = 2798189) B2798189
theorem B1865475 : Blo 1863633 1865475 := bstep (se 1 (by rfl) ⟨1399106, by rfl⟩ : syracuseStep 1865475 = 2798213) B2798213
theorem B5379853 : Blo 1863633 5379853 := bstep (se 3 (by rfl) ⟨1008722, by rfl⟩ : syracuseStep 5379853 = 2017445) B2017445
theorem B1865491 : Blo 1863633 1865491 := bstep (se 1 (by rfl) ⟨1399118, by rfl⟩ : syracuseStep 1865491 = 2798237) B2798237
theorem B1865507 : Blo 1863633 1865507 := bstep (se 1 (by rfl) ⟨1399130, by rfl⟩ : syracuseStep 1865507 = 2798261) B2798261
theorem B1865523 : Blo 1863633 1865523 := bstep (se 1 (by rfl) ⟨1399142, by rfl⟩ : syracuseStep 1865523 = 2798285) B2798285
theorem B1865539 : Blo 1863633 1865539 := bstep (se 1 (by rfl) ⟨1399154, by rfl⟩ : syracuseStep 1865539 = 2798309) B2798309
theorem B1865555 : Blo 1863633 1865555 := bstep (se 1 (by rfl) ⟨1399166, by rfl⟩ : syracuseStep 1865555 = 2798333) B2798333
theorem B2520929 : Blo 1863633 2520929 := bstep (se 2 (by rfl) ⟨945348, by rfl⟩ : syracuseStep 2520929 = 1890697) B1890697
theorem B1865571 : Blo 1863633 1865571 := bstep (se 1 (by rfl) ⟨1399178, by rfl⟩ : syracuseStep 1865571 = 2798357) B2798357
theorem B1865587 : Blo 1863633 1865587 := bstep (se 1 (by rfl) ⟨1399190, by rfl⟩ : syracuseStep 1865587 = 2798381) B2798381
theorem B1865603 : Blo 1863633 1865603 := bstep (se 1 (by rfl) ⟨1399202, by rfl⟩ : syracuseStep 1865603 = 2798405) B2798405
theorem B1865619 : Blo 1863633 1865619 := bstep (se 1 (by rfl) ⟨1399214, by rfl⟩ : syracuseStep 1865619 = 2798429) B2798429
theorem B10622897 : Blo 1863633 10622897 := bstep (se 2 (by rfl) ⟨3983586, by rfl⟩ : syracuseStep 10622897 = 7967173) B7967173
theorem B7559153 : Blo 1863633 7559153 := bstep (se 2 (by rfl) ⟨2834682, by rfl⟩ : syracuseStep 7559153 = 5669365) B5669365
theorem B10614833 : Blo 1863633 10614833 := bstep (se 2 (by rfl) ⟨3980562, by rfl⟩ : syracuseStep 10614833 = 7961125) B7961125
theorem B7968881 : Blo 1863633 7968881 := bstep (se 2 (by rfl) ⟨2988330, by rfl⟩ : syracuseStep 7968881 = 5976661) B5976661
theorem B7960817 : Blo 1863633 7960817 := bstep (se 2 (by rfl) ⟨2985306, by rfl⟩ : syracuseStep 7960817 = 5970613) B5970613
theorem B53787077 : Blo 1863633 53787077 := bstep (se 4 (by rfl) ⟨5042538, by rfl⟩ : syracuseStep 53787077 = 10085077) B10085077
theorem B9443789 : Blo 1863633 9443789 := bstep (se 3 (by rfl) ⟨1770710, by rfl⟩ : syracuseStep 9443789 = 3541421) B3541421
theorem B2554369 : Blo 1863633 2554369 := bstep (se 2 (by rfl) ⟨957888, by rfl⟩ : syracuseStep 2554369 = 1915777) B1915777
theorem B24214115 : Blo 1863633 24214115 := bstep (se 1 (by rfl) ⟨18160586, by rfl⟩ : syracuseStep 24214115 = 36321173) B36321173
theorem B35855045 : Blo 1863633 35855045 := bstep (se 4 (by rfl) ⟨3361410, by rfl⟩ : syracuseStep 35855045 = 6722821) B6722821
theorem B72653539 : Blo 1863633 72653539 := bstep (se 1 (by rfl) ⟨54490154, by rfl⟩ : syracuseStep 72653539 = 108980309) B108980309
theorem B6290189 : Blo 1863633 6290189 := bstep (se 3 (by rfl) ⟨1179410, by rfl⟩ : syracuseStep 6290189 = 2358821) B2358821
theorem B4717379 : Blo 1863633 4717379 := bstep (se 1 (by rfl) ⟨3538034, by rfl⟩ : syracuseStep 4717379 = 7076069) B7076069
theorem B6290243 : Blo 1863633 6290243 := bstep (se 1 (by rfl) ⟨4717682, by rfl⟩ : syracuseStep 6290243 = 9435365) B9435365
theorem B2390995 : Blo 1863633 2390995 := bstep (se 1 (by rfl) ⟨1793246, by rfl⟩ : syracuseStep 2390995 = 3586493) B3586493
theorem B4193297 : Blo 1863633 4193297 := bstep (se 2 (by rfl) ⟨1572486, by rfl⟩ : syracuseStep 4193297 = 3144973) B3144973
theorem B4193315 : Blo 1863633 4193315 := bstep (se 1 (by rfl) ⟨3144986, by rfl⟩ : syracuseStep 4193315 = 6289973) B6289973
theorem B5667907 : Blo 1863633 5667907 := bstep (se 1 (by rfl) ⟨4250930, by rfl⟩ : syracuseStep 5667907 = 8501861) B8501861
theorem B6290513 : Blo 1863633 6290513 := bstep (se 2 (by rfl) ⟨2358942, by rfl⟩ : syracuseStep 6290513 = 4717885) B4717885
theorem B3538019 : Blo 1863633 3538019 := bstep (se 1 (by rfl) ⟨2653514, by rfl⟩ : syracuseStep 3538019 = 5307029) B5307029
theorem B8961187 : Blo 1863633 8961187 := bstep (se 1 (by rfl) ⟨6720890, by rfl⟩ : syracuseStep 8961187 = 13441781) B13441781
theorem B5307565 : Blo 1863633 5307565 := bstep (se 3 (by rfl) ⟨995168, by rfl⟩ : syracuseStep 5307565 = 1990337) B1990337
theorem B7077041 : Blo 1863633 7077041 := bstep (se 2 (by rfl) ⟨2653890, by rfl⟩ : syracuseStep 7077041 = 5307781) B5307781
theorem B9436337 : Blo 1863633 9436337 := bstep (se 2 (by rfl) ⟨3538626, by rfl⟩ : syracuseStep 9436337 = 7077253) B7077253
theorem B3144899 : Blo 1863633 3144899 := bstep (se 1 (by rfl) ⟨2358674, by rfl⟩ : syracuseStep 3144899 = 4717349) B4717349
theorem B4193585 : Blo 1863633 4193585 := bstep (se 2 (by rfl) ⟨1572594, by rfl⟩ : syracuseStep 4193585 = 3145189) B3145189
theorem B3145027 : Blo 1863633 3145027 := bstep (se 1 (by rfl) ⟨2358770, by rfl⟩ : syracuseStep 3145027 = 4717541) B4717541
theorem B4193603 : Blo 1863633 4193603 := bstep (se 1 (by rfl) ⟨3145202, by rfl⟩ : syracuseStep 4193603 = 6290405) B6290405
theorem B10624355 : Blo 1863633 10624355 := bstep (se 1 (by rfl) ⟨7968266, by rfl⟩ : syracuseStep 10624355 = 15936533) B15936533
theorem B2653555 : Blo 1863633 2653555 := bstep (se 1 (by rfl) ⟨1990166, by rfl⟩ : syracuseStep 2653555 = 3980333) B3980333
theorem B6462893 : Blo 1863633 6462893 := bstep (se 3 (by rfl) ⟨1211792, by rfl⟩ : syracuseStep 6462893 = 2423585) B2423585
theorem B3145169 : Blo 1863633 3145169 := bstep (se 2 (by rfl) ⟨1179438, by rfl⟩ : syracuseStep 3145169 = 2358877) B2358877
theorem B2653651 : Blo 1863633 2653651 := bstep (se 1 (by rfl) ⟨1990238, by rfl⟩ : syracuseStep 2653651 = 3980477) B3980477
theorem B7962083 : Blo 1863633 7962083 := bstep (se 1 (by rfl) ⟨5971562, by rfl⟩ : syracuseStep 7962083 = 11943125) B11943125
theorem B10616291 : Blo 1863633 10616291 := bstep (se 1 (by rfl) ⟨7962218, by rfl⟩ : syracuseStep 10616291 = 15924437) B15924437
theorem B14155235 : Blo 1863633 14155235 := bstep (se 1 (by rfl) ⟨10616426, by rfl⟩ : syracuseStep 14155235 = 21232853) B21232853
theorem B17006051 : Blo 1863633 17006051 := bstep (se 1 (by rfl) ⟨12754538, by rfl⟩ : syracuseStep 17006051 = 25509077) B25509077
theorem B9567715 : Blo 1863633 9567715 := bstep (se 1 (by rfl) ⟨7175786, by rfl⟩ : syracuseStep 9567715 = 14351573) B14351573
theorem B3980785 : Blo 1863633 3980785 := bstep (se 2 (by rfl) ⟨1492794, by rfl⟩ : syracuseStep 3980785 = 2985589) B2985589
theorem B2096707 : Blo 1863633 2096707 := bstep (se 1 (by rfl) ⟨1572530, by rfl⟩ : syracuseStep 2096707 = 3145061) B3145061
theorem B3145297 : Blo 1863633 3145297 := bstep (se 2 (by rfl) ⟨1179486, by rfl⟩ : syracuseStep 3145297 = 2358973) B2358973
theorem B4193873 : Blo 1863633 4193873 := bstep (se 2 (by rfl) ⟨1572702, by rfl⟩ : syracuseStep 4193873 = 3145405) B3145405
theorem B2834003 : Blo 1863633 2834003 := bstep (se 1 (by rfl) ⟨2125502, by rfl⟩ : syracuseStep 2834003 = 4251005) B4251005
theorem B4193891 : Blo 1863633 4193891 := bstep (se 1 (by rfl) ⟨3145418, by rfl⟩ : syracuseStep 4193891 = 6290837) B6290837
theorem B6291053 : Blo 1863633 6291053 := bstep (se 3 (by rfl) ⟨1179572, by rfl⟩ : syracuseStep 6291053 = 2359145) B2359145
theorem B3145331 : Blo 1863633 3145331 := bstep (se 1 (by rfl) ⟨2358998, by rfl⟩ : syracuseStep 3145331 = 4717997) B4717997
theorem B6291107 : Blo 1863633 6291107 := bstep (se 1 (by rfl) ⟨4718330, by rfl⟩ : syracuseStep 6291107 = 9436661) B9436661
theorem B2096851 : Blo 1863633 2096851 := bstep (se 1 (by rfl) ⟨1572638, by rfl⟩ : syracuseStep 2096851 = 3145277) B3145277
theorem B4718321 : Blo 1863633 4718321 := bstep (se 2 (by rfl) ⟨1769370, by rfl⟩ : syracuseStep 4718321 = 3538741) B3538741
theorem B3145459 : Blo 1863633 3145459 := bstep (se 1 (by rfl) ⟨2359094, by rfl⟩ : syracuseStep 3145459 = 4718189) B4718189
theorem B40304405 : Blo 1863633 40304405 := bstep (se 6 (by rfl) ⟨944634, by rfl⟩ : syracuseStep 40304405 = 1889269) B1889269
theorem B4718371 : Blo 1863633 4718371 := bstep (se 1 (by rfl) ⟨3538778, by rfl⟩ : syracuseStep 4718371 = 7077557) B7077557
theorem B5037869 : Blo 1863633 5037869 := bstep (se 3 (by rfl) ⟨944600, by rfl⟩ : syracuseStep 5037869 = 1889201) B1889201
theorem B2096995 : Blo 1863633 2096995 := bstep (se 1 (by rfl) ⟨1572746, by rfl⟩ : syracuseStep 2096995 = 3145493) B3145493
theorem B4194161 : Blo 1863633 4194161 := bstep (se 2 (by rfl) ⟨1572810, by rfl⟩ : syracuseStep 4194161 = 3145621) B3145621
theorem B3145601 : Blo 1863633 3145601 := bstep (se 2 (by rfl) ⟨1179600, by rfl⟩ : syracuseStep 3145601 = 2359201) B2359201
theorem B4194179 : Blo 1863633 4194179 := bstep (se 1 (by rfl) ⟨3145634, by rfl⟩ : syracuseStep 4194179 = 6291269) B6291269
theorem B5971843 : Blo 1863633 5971843 := bstep (se 1 (by rfl) ⟨4478882, by rfl⟩ : syracuseStep 5971843 = 8957765) B8957765
theorem B3587971 : Blo 1863633 3587971 := bstep (se 1 (by rfl) ⟨2690978, by rfl⟩ : syracuseStep 3587971 = 5381957) B5381957
theorem B4718513 : Blo 1863633 4718513 := bstep (se 2 (by rfl) ⟨1769442, by rfl⟩ : syracuseStep 4718513 = 3538885) B3538885
theorem B6291377 : Blo 1863633 6291377 := bstep (se 2 (by rfl) ⟨2359266, by rfl⟩ : syracuseStep 6291377 = 4718533) B4718533
theorem B2654147 : Blo 1863633 2654147 := bstep (se 1 (by rfl) ⟨1990610, by rfl⟩ : syracuseStep 2654147 = 3981221) B3981221
theorem B2097139 : Blo 1863633 2097139 := bstep (se 1 (by rfl) ⟨1572854, by rfl⟩ : syracuseStep 2097139 = 3145709) B3145709
theorem B4194305 : Blo 1863633 4194305 := bstep (se 2 (by rfl) ⟨1572864, by rfl⟩ : syracuseStep 4194305 = 3145729) B3145729
theorem B13623301 : Blo 1863633 13623301 := bstep (se 4 (by rfl) ⟨1277184, by rfl⟩ : syracuseStep 13623301 = 2554369) B2554369
theorem B2359307 : Blo 1863633 2359307 := bstep (se 1 (by rfl) ⟨1769480, by rfl⟩ : syracuseStep 2359307 = 3538961) B3538961
theorem B2097175 : Blo 1863633 2097175 := bstep (se 1 (by rfl) ⟨1572881, by rfl⟩ : syracuseStep 2097175 = 3145763) B3145763
theorem B4481075 : Blo 1863633 4481075 := bstep (se 1 (by rfl) ⟨3360806, by rfl⟩ : syracuseStep 4481075 = 6721613) B6721613
theorem B3145817 : Blo 1863633 3145817 := bstep (se 2 (by rfl) ⟨1179681, by rfl⟩ : syracuseStep 3145817 = 2359363) B2359363
theorem B2097355 : Blo 1863633 2097355 := bstep (se 1 (by rfl) ⟨1573016, by rfl⟩ : syracuseStep 2097355 = 3146033) B3146033
theorem B4194521 : Blo 1863633 4194521 := bstep (se 2 (by rfl) ⟨1572945, by rfl⟩ : syracuseStep 4194521 = 3145891) B3145891
theorem B3145945 : Blo 1863633 3145945 := bstep (se 2 (by rfl) ⟨1179729, by rfl⟩ : syracuseStep 3145945 = 2359459) B2359459
theorem B8962265 : Blo 1863633 8962265 := bstep (se 2 (by rfl) ⟨3360849, by rfl⟩ : syracuseStep 8962265 = 6721699) B6721699
theorem B21250349 : Blo 1863633 21250349 := bstep (se 3 (by rfl) ⟨3984440, by rfl⟩ : syracuseStep 21250349 = 7968881) B7968881
theorem B4194611 : Blo 1863633 4194611 := bstep (se 1 (by rfl) ⟨3145958, by rfl⟩ : syracuseStep 4194611 = 6291917) B6291917
theorem B2097463 : Blo 1863633 2097463 := bstep (se 1 (by rfl) ⟨1573097, by rfl⟩ : syracuseStep 2097463 = 3146195) B3146195
theorem B4194647 : Blo 1863633 4194647 := bstep (se 1 (by rfl) ⟨3145985, by rfl⟩ : syracuseStep 4194647 = 6291971) B6291971
theorem B11493733 : Blo 1863633 11493733 := bstep (se 4 (by rfl) ⟨1077537, by rfl⟩ : syracuseStep 11493733 = 2155075) B2155075
theorem B6291863 : Blo 1863633 6291863 := bstep (se 1 (by rfl) ⟨4718897, by rfl⟩ : syracuseStep 6291863 = 9437795) B9437795
theorem B4718999 : Blo 1863633 4718999 := bstep (se 1 (by rfl) ⟨3539249, by rfl⟩ : syracuseStep 4718999 = 7078499) B7078499
theorem B7963073 : Blo 1863633 7963073 := bstep (se 2 (by rfl) ⟨2986152, by rfl⟩ : syracuseStep 7963073 = 5972305) B5972305
theorem B4252097 : Blo 1863633 4252097 := bstep (se 2 (by rfl) ⟨1594536, by rfl⟩ : syracuseStep 4252097 = 3189073) B3189073
theorem B4481497 : Blo 1863633 4481497 := bstep (se 2 (by rfl) ⟨1680561, by rfl⟩ : syracuseStep 4481497 = 3361123) B3361123
theorem B2097643 : Blo 1863633 2097643 := bstep (se 1 (by rfl) ⟨1573232, by rfl⟩ : syracuseStep 2097643 = 3146465) B3146465
theorem B4194827 : Blo 1863633 4194827 := bstep (se 1 (by rfl) ⟨3146120, by rfl⟩ : syracuseStep 4194827 = 6292241) B6292241
theorem B7176755 : Blo 1863633 7176755 := bstep (se 1 (by rfl) ⟨5382566, by rfl⟩ : syracuseStep 7176755 = 10765133) B10765133
theorem B4194881 : Blo 1863633 4194881 := bstep (se 2 (by rfl) ⟨1573080, by rfl⟩ : syracuseStep 4194881 = 3146161) B3146161
theorem B3539531 : Blo 1863633 3539531 := bstep (se 1 (by rfl) ⟨2654648, by rfl⟩ : syracuseStep 3539531 = 5309297) B5309297
theorem B2097751 : Blo 1863633 2097751 := bstep (se 1 (by rfl) ⟨1573313, by rfl⟩ : syracuseStep 2097751 = 3146627) B3146627
theorem B2360011 : Blo 1863633 2360011 := bstep (se 1 (by rfl) ⟨1770008, by rfl⟩ : syracuseStep 2360011 = 3540017) B3540017
theorem B3539713 : Blo 1863633 3539713 := bstep (se 2 (by rfl) ⟨1327392, by rfl⟩ : syracuseStep 3539713 = 2654785) B2654785
theorem B2097931 : Blo 1863633 2097931 := bstep (se 1 (by rfl) ⟨1573448, by rfl⟩ : syracuseStep 2097931 = 3146897) B3146897
theorem B3146519 : Blo 1863633 3146519 := bstep (se 1 (by rfl) ⟨2359889, by rfl⟩ : syracuseStep 3146519 = 4719779) B4719779
theorem B4195097 : Blo 1863633 4195097 := bstep (se 2 (by rfl) ⟨1573161, by rfl⟩ : syracuseStep 4195097 = 3146323) B3146323
theorem B4195187 : Blo 1863633 4195187 := bstep (se 1 (by rfl) ⟨3146390, by rfl⟩ : syracuseStep 4195187 = 6292781) B6292781
theorem B2098039 : Blo 1863633 2098039 := bstep (se 1 (by rfl) ⟨1573529, by rfl⟩ : syracuseStep 2098039 = 3147059) B3147059
theorem B6808465 : Blo 1863633 6808465 := bstep (se 2 (by rfl) ⟨2553174, by rfl⟩ : syracuseStep 6808465 = 5106349) B5106349
theorem B3359639 : Blo 1863633 3359639 := bstep (se 1 (by rfl) ⟨2519729, by rfl⟩ : syracuseStep 3359639 = 5039459) B5039459
theorem B4195223 : Blo 1863633 4195223 := bstep (se 1 (by rfl) ⟨3146417, by rfl⟩ : syracuseStep 4195223 = 6292835) B6292835
theorem B3146647 : Blo 1863633 3146647 := bstep (se 1 (by rfl) ⟨2359985, by rfl⟩ : syracuseStep 3146647 = 4719971) B4719971
theorem B6292403 : Blo 1863633 6292403 := bstep (se 1 (by rfl) ⟨4719302, by rfl⟩ : syracuseStep 6292403 = 9438605) B9438605
theorem B51045299 : Blo 1863633 51045299 := bstep (se 1 (by rfl) ⟨38283974, by rfl⟩ : syracuseStep 51045299 = 76567949) B76567949
theorem B2360279 : Blo 1863633 2360279 := bstep (se 1 (by rfl) ⟨1770209, by rfl⟩ : syracuseStep 2360279 = 3540419) B3540419
theorem B96871385 : Blo 1863633 96871385 := bstep (se 2 (by rfl) ⟨36326769, by rfl⟩ : syracuseStep 96871385 = 72653539) B72653539
theorem B2098219 : Blo 1863633 2098219 := bstep (se 1 (by rfl) ⟨1573664, by rfl⟩ : syracuseStep 2098219 = 3147329) B3147329
theorem B7177261 : Blo 1863633 7177261 := bstep (se 3 (by rfl) ⟨1345736, by rfl⟩ : syracuseStep 7177261 = 2691473) B2691473
theorem B4719667 : Blo 1863633 4719667 := bstep (se 1 (by rfl) ⟨3539750, by rfl⟩ : syracuseStep 4719667 = 7079501) B7079501
theorem B35832901 : Blo 1863633 35832901 := bstep (se 4 (by rfl) ⟨3359334, by rfl⟩ : syracuseStep 35832901 = 6718669) B6718669
theorem B4195403 : Blo 1863633 4195403 := bstep (se 1 (by rfl) ⟨3146552, by rfl⟩ : syracuseStep 4195403 = 6293105) B6293105
theorem B4195457 : Blo 1863633 4195457 := bstep (se 2 (by rfl) ⟨1573296, by rfl⟩ : syracuseStep 4195457 = 3146593) B3146593
theorem B2098327 : Blo 1863633 2098327 := bstep (se 1 (by rfl) ⟨1573745, by rfl⟩ : syracuseStep 2098327 = 3147491) B3147491
theorem B6292673 : Blo 1863633 6292673 := bstep (se 2 (by rfl) ⟨2359752, by rfl⟩ : syracuseStep 6292673 = 4719505) B4719505
theorem B4719809 : Blo 1863633 4719809 := bstep (se 2 (by rfl) ⟨1769928, by rfl⟩ : syracuseStep 4719809 = 3539857) B3539857
theorem B3540161 : Blo 1863633 3540161 := bstep (se 2 (by rfl) ⟨1327560, by rfl⟩ : syracuseStep 3540161 = 2655121) B2655121
theorem B34022605 : Blo 1863633 34022605 := bstep (se 3 (by rfl) ⟨6379238, by rfl⟩ : syracuseStep 34022605 = 12758477) B12758477
theorem B3187993 : Blo 1863633 3187993 := bstep (se 2 (by rfl) ⟨1195497, by rfl⟩ : syracuseStep 3187993 = 2390995) B2390995
theorem B5039425 : Blo 1863633 5039425 := bstep (se 2 (by rfl) ⟨1889784, by rfl⟩ : syracuseStep 5039425 = 3779569) B3779569
theorem B5039435 : Blo 1863633 5039435 := bstep (se 1 (by rfl) ⟨3779576, by rfl⟩ : syracuseStep 5039435 = 7559153) B7559153
theorem B2098507 : Blo 1863633 2098507 := bstep (se 1 (by rfl) ⟨1573880, by rfl⟩ : syracuseStep 2098507 = 3147761) B3147761
theorem B4195673 : Blo 1863633 4195673 := bstep (se 2 (by rfl) ⟨1573377, by rfl⟩ : syracuseStep 4195673 = 3146755) B3146755
theorem B55248277 : Blo 1863633 55248277 := bstep (se 6 (by rfl) ⟨1294881, by rfl⟩ : syracuseStep 55248277 = 2589763) B2589763
theorem B4195763 : Blo 1863633 4195763 := bstep (se 1 (by rfl) ⟨3146822, by rfl⟩ : syracuseStep 4195763 = 6293645) B6293645
theorem B2098615 : Blo 1863633 2098615 := bstep (se 1 (by rfl) ⟨1573961, by rfl⟩ : syracuseStep 2098615 = 3147923) B3147923
theorem B4195799 : Blo 1863633 4195799 := bstep (se 1 (by rfl) ⟨3146849, by rfl⟩ : syracuseStep 4195799 = 6293699) B6293699
theorem B3147275 : Blo 1863633 3147275 := bstep (se 1 (by rfl) ⟨2360456, by rfl⟩ : syracuseStep 3147275 = 4720913) B4720913
theorem B3540503 : Blo 1863633 3540503 := bstep (se 1 (by rfl) ⟨2655377, by rfl⟩ : syracuseStep 3540503 = 5310755) B5310755
theorem B3982937 : Blo 1863633 3982937 := bstep (se 2 (by rfl) ⟨1493601, by rfl⟩ : syracuseStep 3982937 = 2987203) B2987203
theorem B2098795 : Blo 1863633 2098795 := bstep (se 1 (by rfl) ⟨1574096, by rfl⟩ : syracuseStep 2098795 = 3148193) B3148193
theorem B35858051 : Blo 1863633 35858051 := bstep (se 1 (by rfl) ⟨26893538, by rfl⟩ : syracuseStep 35858051 = 53787077) B53787077
theorem B4195979 : Blo 1863633 4195979 := bstep (se 1 (by rfl) ⟨3146984, by rfl⟩ : syracuseStep 4195979 = 6293969) B6293969
theorem B3147403 : Blo 1863633 3147403 := bstep (se 1 (by rfl) ⟨2360552, by rfl⟩ : syracuseStep 3147403 = 4721105) B4721105
theorem B2360983 : Blo 1863633 2360983 := bstep (se 1 (by rfl) ⟨1770737, by rfl⟩ : syracuseStep 2360983 = 3541475) B3541475
theorem B4196033 : Blo 1863633 4196033 := bstep (se 2 (by rfl) ⟨1573512, by rfl⟩ : syracuseStep 4196033 = 3147025) B3147025
theorem B6293213 : Blo 1863633 6293213 := bstep (se 3 (by rfl) ⟨1179977, by rfl⟩ : syracuseStep 6293213 = 2359955) B2359955
theorem B5310173 : Blo 1863633 5310173 := bstep (se 3 (by rfl) ⟨995657, by rfl⟩ : syracuseStep 5310173 = 1991315) B1991315
theorem B7079683 : Blo 1863633 7079683 := bstep (se 1 (by rfl) ⟨5309762, by rfl⟩ : syracuseStep 7079683 = 10619525) B10619525
theorem B3147545 : Blo 1863633 3147545 := bstep (se 2 (by rfl) ⟨1180329, by rfl⟩ : syracuseStep 3147545 = 2360659) B2360659
theorem B10618775 : Blo 1863633 10618775 := bstep (se 1 (by rfl) ⟨7964081, by rfl⟩ : syracuseStep 10618775 = 15928163) B15928163
theorem B4196249 : Blo 1863633 4196249 := bstep (se 2 (by rfl) ⟨1573593, by rfl⟩ : syracuseStep 4196249 = 3147187) B3147187
theorem B3147673 : Blo 1863633 3147673 := bstep (se 2 (by rfl) ⟨1180377, by rfl⟩ : syracuseStep 3147673 = 2360755) B2360755
theorem B12756953 : Blo 1863633 12756953 := bstep (se 2 (by rfl) ⟨4783857, by rfl⟩ : syracuseStep 12756953 = 9567715) B9567715
theorem B4196339 : Blo 1863633 4196339 := bstep (se 1 (by rfl) ⟨3147254, by rfl⟩ : syracuseStep 4196339 = 6294509) B6294509
theorem B3983347 : Blo 1863633 3983347 := bstep (se 1 (by rfl) ⟨2987510, by rfl⟩ : syracuseStep 3983347 = 5975021) B5975021
theorem B2795531 : Blo 1863633 2795531 := bstep (se 1 (by rfl) ⟨2096648, by rfl⟩ : syracuseStep 2795531 = 4193297) B4193297
theorem B30246929 : Blo 1863633 30246929 := bstep (se 2 (by rfl) ⟨11342598, by rfl⟩ : syracuseStep 30246929 = 22685197) B22685197
theorem B2795543 : Blo 1863633 2795543 := bstep (se 1 (by rfl) ⟨2096657, by rfl⟩ : syracuseStep 2795543 = 4193315) B4193315
theorem B4196375 : Blo 1863633 4196375 := bstep (se 1 (by rfl) ⟨3147281, by rfl⟩ : syracuseStep 4196375 = 6294563) B6294563
theorem B4311065 : Blo 1863633 4311065 := bstep (se 2 (by rfl) ⟨1616649, by rfl⟩ : syracuseStep 4311065 = 3233299) B3233299
theorem B3885079 : Blo 1863633 3885079 := bstep (se 1 (by rfl) ⟨2913809, by rfl⟩ : syracuseStep 3885079 = 5827619) B5827619
theorem B31868963 : Blo 1863633 31868963 := bstep (se 1 (by rfl) ⟨23901722, by rfl⟩ : syracuseStep 31868963 = 47803445) B47803445
theorem B23906339 : Blo 1863633 23906339 := bstep (se 1 (by rfl) ⟨17929754, by rfl⟩ : syracuseStep 23906339 = 35859509) B35859509
theorem B7079987 : Blo 1863633 7079987 := bstep (se 1 (by rfl) ⟨5309990, by rfl⟩ : syracuseStep 7079987 = 10619981) B10619981
theorem B5310515 : Blo 1863633 5310515 := bstep (se 1 (by rfl) ⟨3982886, by rfl⟩ : syracuseStep 5310515 = 7965773) B7965773
theorem B2795609 : Blo 1863633 2795609 := bstep (se 2 (by rfl) ⟨1048353, by rfl⟩ : syracuseStep 2795609 = 2096707) B2096707
theorem B3541171 : Blo 1863633 3541171 := bstep (se 1 (by rfl) ⟨2655878, by rfl⟩ : syracuseStep 3541171 = 5311757) B5311757
theorem B2795723 : Blo 1863633 2795723 := bstep (se 1 (by rfl) ⟨2096792, by rfl⟩ : syracuseStep 2795723 = 4193585) B4193585
theorem B4196555 : Blo 1863633 4196555 := bstep (se 1 (by rfl) ⟨3147416, by rfl⟩ : syracuseStep 4196555 = 6294833) B6294833
theorem B2795735 : Blo 1863633 2795735 := bstep (se 1 (by rfl) ⟨2096801, by rfl⟩ : syracuseStep 2795735 = 4193603) B4193603
theorem B4196609 : Blo 1863633 4196609 := bstep (se 2 (by rfl) ⟨1573728, by rfl⟩ : syracuseStep 4196609 = 3147457) B3147457
theorem B2795801 : Blo 1863633 2795801 := bstep (se 2 (by rfl) ⟨1048425, by rfl⟩ : syracuseStep 2795801 = 2096851) B2096851
theorem B23890241 : Blo 1863633 23890241 := bstep (se 2 (by rfl) ⟨8958840, by rfl⟩ : syracuseStep 23890241 = 17917681) B17917681
theorem B3983681 : Blo 1863633 3983681 := bstep (se 2 (by rfl) ⟨1493880, by rfl⟩ : syracuseStep 3983681 = 2987761) B2987761
theorem B5040473 : Blo 1863633 5040473 := bstep (se 2 (by rfl) ⟨1890177, by rfl⟩ : syracuseStep 5040473 = 3780355) B3780355
theorem B24873317 : Blo 1863633 24873317 := bstep (se 4 (by rfl) ⟨2331873, by rfl⟩ : syracuseStep 24873317 = 4663747) B4663747
theorem B2795915 : Blo 1863633 2795915 := bstep (se 1 (by rfl) ⟨2096936, by rfl⟩ : syracuseStep 2795915 = 4193873) B4193873
theorem B2795927 : Blo 1863633 2795927 := bstep (se 1 (by rfl) ⟨2096945, by rfl⟩ : syracuseStep 2795927 = 4193891) B4193891
theorem B4721075 : Blo 1863633 4721075 := bstep (se 1 (by rfl) ⟨3540806, by rfl⟩ : syracuseStep 4721075 = 7081613) B7081613
theorem B3148247 : Blo 1863633 3148247 := bstep (se 1 (by rfl) ⟨2361185, by rfl⟩ : syracuseStep 3148247 = 4722371) B4722371
theorem B2795993 : Blo 1863633 2795993 := bstep (se 2 (by rfl) ⟨1048497, by rfl⟩ : syracuseStep 2795993 = 2096995) B2096995
theorem B4196825 : Blo 1863633 4196825 := bstep (se 2 (by rfl) ⟨1573809, by rfl⟩ : syracuseStep 4196825 = 3147619) B3147619
theorem B3361267 : Blo 1863633 3361267 := bstep (se 1 (by rfl) ⟨2520950, by rfl⟩ : syracuseStep 3361267 = 5041901) B5041901
theorem B4196915 : Blo 1863633 4196915 := bstep (se 1 (by rfl) ⟨3147686, by rfl⟩ : syracuseStep 4196915 = 6295373) B6295373
theorem B2796107 : Blo 1863633 2796107 := bstep (se 1 (by rfl) ⟨2097080, by rfl⟩ : syracuseStep 2796107 = 4194161) B4194161
theorem B2796119 : Blo 1863633 2796119 := bstep (se 1 (by rfl) ⟨2097089, by rfl⟩ : syracuseStep 2796119 = 4194179) B4194179
theorem B4196951 : Blo 1863633 4196951 := bstep (se 1 (by rfl) ⟨3147713, by rfl⟩ : syracuseStep 4196951 = 6295427) B6295427
theorem B3541619 : Blo 1863633 3541619 := bstep (se 1 (by rfl) ⟨2656214, by rfl⟩ : syracuseStep 3541619 = 5312429) B5312429
theorem B2796185 : Blo 1863633 2796185 := bstep (se 2 (by rfl) ⟨1048569, by rfl⟩ : syracuseStep 2796185 = 2097139) B2097139
theorem B3541657 : Blo 1863633 3541657 := bstep (se 2 (by rfl) ⟨1328121, by rfl⟩ : syracuseStep 3541657 = 2656243) B2656243
theorem B7080641 : Blo 1863633 7080641 := bstep (se 2 (by rfl) ⟨2655240, by rfl⟩ : syracuseStep 7080641 = 5310481) B5310481
theorem B2796299 : Blo 1863633 2796299 := bstep (se 1 (by rfl) ⟨2097224, by rfl⟩ : syracuseStep 2796299 = 4194449) B4194449
theorem B4197131 : Blo 1863633 4197131 := bstep (se 1 (by rfl) ⟨3147848, by rfl⟩ : syracuseStep 4197131 = 6295697) B6295697
theorem B2796311 : Blo 1863633 2796311 := bstep (se 1 (by rfl) ⟨2097233, by rfl⟩ : syracuseStep 2796311 = 4194467) B4194467
theorem B14158637 : Blo 1863633 14158637 := bstep (se 3 (by rfl) ⟨2654744, by rfl⟩ : syracuseStep 14158637 = 5309489) B5309489
theorem B4197185 : Blo 1863633 4197185 := bstep (se 2 (by rfl) ⟨1573944, by rfl⟩ : syracuseStep 4197185 = 3147889) B3147889
theorem B6294347 : Blo 1863633 6294347 := bstep (se 1 (by rfl) ⟨4720760, by rfl⟩ : syracuseStep 6294347 = 9441521) B9441521
theorem B2796377 : Blo 1863633 2796377 := bstep (se 2 (by rfl) ⟨1048641, by rfl⟩ : syracuseStep 2796377 = 2097283) B2097283
theorem B7965533 : Blo 1863633 7965533 := bstep (se 3 (by rfl) ⟨1493537, by rfl⟩ : syracuseStep 7965533 = 2987075) B2987075
theorem B4311923 : Blo 1863633 4311923 := bstep (se 1 (by rfl) ⟨3233942, by rfl⟩ : syracuseStep 4311923 = 6467885) B6467885
theorem B6720401 : Blo 1863633 6720401 := bstep (se 2 (by rfl) ⟨2520150, by rfl⟩ : syracuseStep 6720401 = 5040301) B5040301
theorem B2796491 : Blo 1863633 2796491 := bstep (se 1 (by rfl) ⟨2097368, by rfl⟩ : syracuseStep 2796491 = 4194737) B4194737
theorem B4721611 : Blo 1863633 4721611 := bstep (se 1 (by rfl) ⟨3541208, by rfl⟩ : syracuseStep 4721611 = 7082417) B7082417
theorem B2796503 : Blo 1863633 2796503 := bstep (se 1 (by rfl) ⟨2097377, by rfl⟩ : syracuseStep 2796503 = 4194755) B4194755
theorem B3984407 : Blo 1863633 3984407 := bstep (se 1 (by rfl) ⟨2988305, by rfl⟩ : syracuseStep 3984407 = 5976611) B5976611
theorem B2796569 : Blo 1863633 2796569 := bstep (se 2 (by rfl) ⟨1048713, by rfl⟩ : syracuseStep 2796569 = 2097427) B2097427
theorem B4197401 : Blo 1863633 4197401 := bstep (se 2 (by rfl) ⟨1574025, by rfl⟩ : syracuseStep 4197401 = 3148051) B3148051
theorem B6294617 : Blo 1863633 6294617 := bstep (se 2 (by rfl) ⟨2360481, by rfl⟩ : syracuseStep 6294617 = 4720963) B4720963
theorem B4721753 : Blo 1863633 4721753 := bstep (se 2 (by rfl) ⟨1770657, by rfl⟩ : syracuseStep 4721753 = 3541315) B3541315
theorem B4197491 : Blo 1863633 4197491 := bstep (se 1 (by rfl) ⟨3148118, by rfl⟩ : syracuseStep 4197491 = 6296237) B6296237
theorem B9440387 : Blo 1863633 9440387 := bstep (se 1 (by rfl) ⟨7080290, by rfl⟩ : syracuseStep 9440387 = 14160581) B14160581
theorem B3779723 : Blo 1863633 3779723 := bstep (se 1 (by rfl) ⟨2834792, by rfl⟩ : syracuseStep 3779723 = 5669585) B5669585
theorem B2796683 : Blo 1863633 2796683 := bstep (se 1 (by rfl) ⟨2097512, by rfl⟩ : syracuseStep 2796683 = 4195025) B4195025
theorem B2796695 : Blo 1863633 2796695 := bstep (se 1 (by rfl) ⟨2097521, by rfl⟩ : syracuseStep 2796695 = 4195043) B4195043
theorem B4197527 : Blo 1863633 4197527 := bstep (se 1 (by rfl) ⟨3148145, by rfl⟩ : syracuseStep 4197527 = 6296291) B6296291
theorem B2796761 : Blo 1863633 2796761 := bstep (se 2 (by rfl) ⟨1048785, by rfl⟩ : syracuseStep 2796761 = 2097571) B2097571
theorem B2796875 : Blo 1863633 2796875 := bstep (se 1 (by rfl) ⟨2097656, by rfl⟩ : syracuseStep 2796875 = 4195313) B4195313
theorem B2796887 : Blo 1863633 2796887 := bstep (se 1 (by rfl) ⟨2097665, by rfl⟩ : syracuseStep 2796887 = 4195331) B4195331
theorem B248491405 : Blo 1863633 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B2796953 : Blo 1863633 2796953 := bstep (se 2 (by rfl) ⟨1048857, by rfl⟩ : syracuseStep 2796953 = 2097715) B2097715
theorem B17010137 : Blo 1863633 17010137 := bstep (se 2 (by rfl) ⟨6378801, by rfl⟩ : syracuseStep 17010137 = 12757603) B12757603
theorem B2797067 : Blo 1863633 2797067 := bstep (se 1 (by rfl) ⟨2097800, by rfl⟩ : syracuseStep 2797067 = 4195601) B4195601
theorem B2797079 : Blo 1863633 2797079 := bstep (se 1 (by rfl) ⟨2097809, by rfl⟩ : syracuseStep 2797079 = 4195619) B4195619
theorem B2797145 : Blo 1863633 2797145 := bstep (se 2 (by rfl) ⟨1048929, by rfl⟩ : syracuseStep 2797145 = 2097859) B2097859
theorem B17927831 : Blo 1863633 17927831 := bstep (se 1 (by rfl) ⟨13445873, by rfl⟩ : syracuseStep 17927831 = 26891747) B26891747
theorem B2797259 : Blo 1863633 2797259 := bstep (se 1 (by rfl) ⟨2097944, by rfl⟩ : syracuseStep 2797259 = 4195889) B4195889
theorem B2797271 : Blo 1863633 2797271 := bstep (se 1 (by rfl) ⟨2097953, by rfl⟩ : syracuseStep 2797271 = 4195907) B4195907
theorem B6295319 : Blo 1863633 6295319 := bstep (se 1 (by rfl) ⟨4721489, by rfl⟩ : syracuseStep 6295319 = 9442979) B9442979
theorem B2797337 : Blo 1863633 2797337 := bstep (se 2 (by rfl) ⟨1049001, by rfl⟩ : syracuseStep 2797337 = 2098003) B2098003
theorem B6721325 : Blo 1863633 6721325 := bstep (se 3 (by rfl) ⟨1260248, by rfl⟩ : syracuseStep 6721325 = 2520497) B2520497
theorem B2797451 : Blo 1863633 2797451 := bstep (se 1 (by rfl) ⟨2098088, by rfl⟩ : syracuseStep 2797451 = 4196177) B4196177
theorem B2797463 : Blo 1863633 2797463 := bstep (se 1 (by rfl) ⟨2098097, by rfl⟩ : syracuseStep 2797463 = 4196195) B4196195
theorem B7081901 : Blo 1863633 7081901 := bstep (se 3 (by rfl) ⟨1327856, by rfl⟩ : syracuseStep 7081901 = 2655713) B2655713
theorem B7081931 : Blo 1863633 7081931 := bstep (se 1 (by rfl) ⟨5311448, by rfl⟩ : syracuseStep 7081931 = 10622897) B10622897
theorem B1863639 : Blo 1863633 1863639 := bstep (se 1 (by rfl) ⟨1397729, by rfl⟩ : syracuseStep 1863639 = 2795459) B2795459
theorem B2797529 : Blo 1863633 2797529 := bstep (se 2 (by rfl) ⟨1049073, by rfl⟩ : syracuseStep 2797529 = 2098147) B2098147
theorem B1863659 : Blo 1863633 1863659 := bstep (se 1 (by rfl) ⟨1397744, by rfl⟩ : syracuseStep 1863659 = 2795489) B2795489
theorem B1863671 : Blo 1863633 1863671 := bstep (se 1 (by rfl) ⟨1397753, by rfl⟩ : syracuseStep 1863671 = 2795507) B2795507
theorem B1863691 : Blo 1863633 1863691 := bstep (se 1 (by rfl) ⟨1397768, by rfl⟩ : syracuseStep 1863691 = 2795537) B2795537
theorem B1863703 : Blo 1863633 1863703 := bstep (se 1 (by rfl) ⟨1397777, by rfl⟩ : syracuseStep 1863703 = 2795555) B2795555
theorem B1863723 : Blo 1863633 1863723 := bstep (se 1 (by rfl) ⟨1397792, by rfl⟩ : syracuseStep 1863723 = 2795585) B2795585
theorem B2125867 : Blo 1863633 2125867 := bstep (se 1 (by rfl) ⟨1594400, by rfl⟩ : syracuseStep 2125867 = 3188801) B3188801
theorem B1863735 : Blo 1863633 1863735 := bstep (se 1 (by rfl) ⟨1397801, by rfl⟩ : syracuseStep 1863735 = 2795603) B2795603
theorem B30642245 : Blo 1863633 30642245 := bstep (se 4 (by rfl) ⟨2872710, by rfl⟩ : syracuseStep 30642245 = 5745421) B5745421
theorem B1863755 : Blo 1863633 1863755 := bstep (se 1 (by rfl) ⟨1397816, by rfl⟩ : syracuseStep 1863755 = 2795633) B2795633
theorem B2797643 : Blo 1863633 2797643 := bstep (se 1 (by rfl) ⟨2098232, by rfl⟩ : syracuseStep 2797643 = 4196465) B4196465
theorem B14004299 : Blo 1863633 14004299 := bstep (se 1 (by rfl) ⟨10503224, by rfl⟩ : syracuseStep 14004299 = 21006449) B21006449
theorem B1863767 : Blo 1863633 1863767 := bstep (se 1 (by rfl) ⟨1397825, by rfl⟩ : syracuseStep 1863767 = 2795651) B2795651
theorem B2797655 : Blo 1863633 2797655 := bstep (se 1 (by rfl) ⟨2098241, by rfl⟩ : syracuseStep 2797655 = 4196483) B4196483
theorem B7557209 : Blo 1863633 7557209 := bstep (se 2 (by rfl) ⟨2833953, by rfl⟩ : syracuseStep 7557209 = 5667907) B5667907
theorem B1863787 : Blo 1863633 1863787 := bstep (se 1 (by rfl) ⟨1397840, by rfl⟩ : syracuseStep 1863787 = 2795681) B2795681
theorem B1863799 : Blo 1863633 1863799 := bstep (se 1 (by rfl) ⟨1397849, by rfl⟩ : syracuseStep 1863799 = 2795699) B2795699
theorem B1863819 : Blo 1863633 1863819 := bstep (se 1 (by rfl) ⟨1397864, by rfl⟩ : syracuseStep 1863819 = 2795729) B2795729
theorem B1863831 : Blo 1863633 1863831 := bstep (se 1 (by rfl) ⟨1397873, by rfl⟩ : syracuseStep 1863831 = 2795747) B2795747
theorem B3780761 : Blo 1863633 3780761 := bstep (se 2 (by rfl) ⟨1417785, by rfl⟩ : syracuseStep 3780761 = 2835571) B2835571
theorem B2797721 : Blo 1863633 2797721 := bstep (se 2 (by rfl) ⟨1049145, by rfl⟩ : syracuseStep 2797721 = 2098291) B2098291
theorem B1863851 : Blo 1863633 1863851 := bstep (se 1 (by rfl) ⟨1397888, by rfl⟩ : syracuseStep 1863851 = 2795777) B2795777
theorem B1863863 : Blo 1863633 1863863 := bstep (se 1 (by rfl) ⟨1397897, by rfl⟩ : syracuseStep 1863863 = 2795795) B2795795
theorem B1863883 : Blo 1863633 1863883 := bstep (se 1 (by rfl) ⟨1397912, by rfl⟩ : syracuseStep 1863883 = 2795825) B2795825
theorem B1863895 : Blo 1863633 1863895 := bstep (se 1 (by rfl) ⟨1397921, by rfl⟩ : syracuseStep 1863895 = 2795843) B2795843
theorem B15929561 : Blo 1863633 15929561 := bstep (se 2 (by rfl) ⟨5973585, by rfl⟩ : syracuseStep 15929561 = 11947171) B11947171
theorem B11948249 : Blo 1863633 11948249 := bstep (se 2 (by rfl) ⟨4480593, by rfl⟩ : syracuseStep 11948249 = 8961187) B8961187
theorem B1863915 : Blo 1863633 1863915 := bstep (se 1 (by rfl) ⟨1397936, by rfl⟩ : syracuseStep 1863915 = 2795873) B2795873
theorem B1863927 : Blo 1863633 1863927 := bstep (se 1 (by rfl) ⟨1397945, by rfl⟩ : syracuseStep 1863927 = 2795891) B2795891
theorem B1863947 : Blo 1863633 1863947 := bstep (se 1 (by rfl) ⟨1397960, by rfl⟩ : syracuseStep 1863947 = 2795921) B2795921
theorem B2797835 : Blo 1863633 2797835 := bstep (se 1 (by rfl) ⟨2098376, by rfl⟩ : syracuseStep 2797835 = 4196753) B4196753
theorem B1863959 : Blo 1863633 1863959 := bstep (se 1 (by rfl) ⟨1397969, by rfl⟩ : syracuseStep 1863959 = 2795939) B2795939
theorem B2797847 : Blo 1863633 2797847 := bstep (se 1 (by rfl) ⟨2098385, by rfl⟩ : syracuseStep 2797847 = 4196771) B4196771
theorem B1863979 : Blo 1863633 1863979 := bstep (se 1 (by rfl) ⟨1397984, by rfl⟩ : syracuseStep 1863979 = 2795969) B2795969
theorem B6295859 : Blo 1863633 6295859 := bstep (se 1 (by rfl) ⟨4721894, by rfl⟩ : syracuseStep 6295859 = 9443789) B9443789
theorem B1863991 : Blo 1863633 1863991 := bstep (se 1 (by rfl) ⟨1397993, by rfl⟩ : syracuseStep 1863991 = 2795987) B2795987
theorem B1864011 : Blo 1863633 1864011 := bstep (se 1 (by rfl) ⟨1398008, by rfl⟩ : syracuseStep 1864011 = 2796017) B2796017
theorem B1864023 : Blo 1863633 1864023 := bstep (se 1 (by rfl) ⟨1398017, by rfl⟩ : syracuseStep 1864023 = 2796035) B2796035
theorem B2797913 : Blo 1863633 2797913 := bstep (se 2 (by rfl) ⟨1049217, by rfl⟩ : syracuseStep 2797913 = 2098435) B2098435
theorem B1864043 : Blo 1863633 1864043 := bstep (se 1 (by rfl) ⟨1398032, by rfl⟩ : syracuseStep 1864043 = 2796065) B2796065
theorem B1864055 : Blo 1863633 1864055 := bstep (se 1 (by rfl) ⟨1398041, by rfl⟩ : syracuseStep 1864055 = 2796083) B2796083
theorem B1864075 : Blo 1863633 1864075 := bstep (se 1 (by rfl) ⟨1398056, by rfl⟩ : syracuseStep 1864075 = 2796113) B2796113
theorem B1864087 : Blo 1863633 1864087 := bstep (se 1 (by rfl) ⟨1398065, by rfl⟩ : syracuseStep 1864087 = 2796131) B2796131
theorem B16142743 : Blo 1863633 16142743 := bstep (se 1 (by rfl) ⟨12107057, by rfl⟩ : syracuseStep 16142743 = 24214115) B24214115
theorem B1864107 : Blo 1863633 1864107 := bstep (se 1 (by rfl) ⟨1398080, by rfl⟩ : syracuseStep 1864107 = 2796161) B2796161
theorem B1864119 : Blo 1863633 1864119 := bstep (se 1 (by rfl) ⟨1398089, by rfl⟩ : syracuseStep 1864119 = 2796179) B2796179
theorem B1864139 : Blo 1863633 1864139 := bstep (se 1 (by rfl) ⟨1398104, by rfl⟩ : syracuseStep 1864139 = 2796209) B2796209
theorem B2798027 : Blo 1863633 2798027 := bstep (se 1 (by rfl) ⟨2098520, by rfl⟩ : syracuseStep 2798027 = 4197041) B4197041
theorem B1864151 : Blo 1863633 1864151 := bstep (se 1 (by rfl) ⟨1398113, by rfl⟩ : syracuseStep 1864151 = 2796227) B2796227
theorem B2798039 : Blo 1863633 2798039 := bstep (se 1 (by rfl) ⟨2098529, by rfl⟩ : syracuseStep 2798039 = 4197059) B4197059
theorem B1864171 : Blo 1863633 1864171 := bstep (se 1 (by rfl) ⟨1398128, by rfl⟩ : syracuseStep 1864171 = 2796257) B2796257
theorem B1864183 : Blo 1863633 1864183 := bstep (se 1 (by rfl) ⟨1398137, by rfl⟩ : syracuseStep 1864183 = 2796275) B2796275
theorem B1864203 : Blo 1863633 1864203 := bstep (se 1 (by rfl) ⟨1398152, by rfl⟩ : syracuseStep 1864203 = 2796305) B2796305
theorem B1864215 : Blo 1863633 1864215 := bstep (se 1 (by rfl) ⟨1398161, by rfl⟩ : syracuseStep 1864215 = 2796323) B2796323
theorem B2798105 : Blo 1863633 2798105 := bstep (se 2 (by rfl) ⟨1049289, by rfl⟩ : syracuseStep 2798105 = 2098579) B2098579
theorem B1864235 : Blo 1863633 1864235 := bstep (se 1 (by rfl) ⟨1398176, by rfl⟩ : syracuseStep 1864235 = 2796353) B2796353
theorem B1864247 : Blo 1863633 1864247 := bstep (se 1 (by rfl) ⟨1398185, by rfl⟩ : syracuseStep 1864247 = 2796371) B2796371
theorem B6296129 : Blo 1863633 6296129 := bstep (se 2 (by rfl) ⟨2361048, by rfl⟩ : syracuseStep 6296129 = 4722097) B4722097
theorem B1864267 : Blo 1863633 1864267 := bstep (se 1 (by rfl) ⟨1398200, by rfl⟩ : syracuseStep 1864267 = 2796401) B2796401
theorem B1864279 : Blo 1863633 1864279 := bstep (se 1 (by rfl) ⟨1398209, by rfl⟩ : syracuseStep 1864279 = 2796419) B2796419
theorem B7082585 : Blo 1863633 7082585 := bstep (se 2 (by rfl) ⟨2655969, by rfl⟩ : syracuseStep 7082585 = 5311939) B5311939
theorem B11342429 : Blo 1863633 11342429 := bstep (se 3 (by rfl) ⟨2126705, by rfl⟩ : syracuseStep 11342429 = 4253411) B4253411
theorem B1864299 : Blo 1863633 1864299 := bstep (se 1 (by rfl) ⟨1398224, by rfl⟩ : syracuseStep 1864299 = 2796449) B2796449
theorem B1864311 : Blo 1863633 1864311 := bstep (se 1 (by rfl) ⟨1398233, by rfl⟩ : syracuseStep 1864311 = 2796467) B2796467
theorem B1864331 : Blo 1863633 1864331 := bstep (se 1 (by rfl) ⟨1398248, by rfl⟩ : syracuseStep 1864331 = 2796497) B2796497
theorem B2798219 : Blo 1863633 2798219 := bstep (se 1 (by rfl) ⟨2098664, by rfl⟩ : syracuseStep 2798219 = 4197329) B4197329
theorem B1864343 : Blo 1863633 1864343 := bstep (se 1 (by rfl) ⟨1398257, by rfl⟩ : syracuseStep 1864343 = 2796515) B2796515
theorem B2798231 : Blo 1863633 2798231 := bstep (se 1 (by rfl) ⟨2098673, by rfl⟩ : syracuseStep 2798231 = 4197347) B4197347
theorem B1864363 : Blo 1863633 1864363 := bstep (se 1 (by rfl) ⟨1398272, by rfl⟩ : syracuseStep 1864363 = 2796545) B2796545
theorem B31847093 : Blo 1863633 31847093 := bstep (se 5 (by rfl) ⟨1492832, by rfl⟩ : syracuseStep 31847093 = 2985665) B2985665
theorem B1864375 : Blo 1863633 1864375 := bstep (se 1 (by rfl) ⟨1398281, by rfl⟩ : syracuseStep 1864375 = 2796563) B2796563
theorem B1864395 : Blo 1863633 1864395 := bstep (se 1 (by rfl) ⟨1398296, by rfl⟩ : syracuseStep 1864395 = 2796593) B2796593
theorem B1864407 : Blo 1863633 1864407 := bstep (se 1 (by rfl) ⟨1398305, by rfl⟩ : syracuseStep 1864407 = 2796611) B2796611
theorem B2798297 : Blo 1863633 2798297 := bstep (se 2 (by rfl) ⟨1049361, by rfl⟩ : syracuseStep 2798297 = 2098723) B2098723
theorem B1864427 : Blo 1863633 1864427 := bstep (se 1 (by rfl) ⟨1398320, by rfl⟩ : syracuseStep 1864427 = 2796641) B2796641
theorem B1864439 : Blo 1863633 1864439 := bstep (se 1 (by rfl) ⟨1398329, by rfl⟩ : syracuseStep 1864439 = 2796659) B2796659
theorem B1864459 : Blo 1863633 1864459 := bstep (se 1 (by rfl) ⟨1398344, by rfl⟩ : syracuseStep 1864459 = 2796689) B2796689
theorem B1864471 : Blo 1863633 1864471 := bstep (se 1 (by rfl) ⟨1398353, by rfl⟩ : syracuseStep 1864471 = 2796707) B2796707
theorem B1864491 : Blo 1863633 1864491 := bstep (se 1 (by rfl) ⟨1398368, by rfl⟩ : syracuseStep 1864491 = 2796737) B2796737
theorem B1864503 : Blo 1863633 1864503 := bstep (se 1 (by rfl) ⟨1398377, by rfl⟩ : syracuseStep 1864503 = 2796755) B2796755
theorem B1864523 : Blo 1863633 1864523 := bstep (se 1 (by rfl) ⟨1398392, by rfl⟩ : syracuseStep 1864523 = 2796785) B2796785
theorem B2798411 : Blo 1863633 2798411 := bstep (se 1 (by rfl) ⟨2098808, by rfl⟩ : syracuseStep 2798411 = 4197617) B4197617
theorem B1864535 : Blo 1863633 1864535 := bstep (se 1 (by rfl) ⟨1398401, by rfl⟩ : syracuseStep 1864535 = 2796803) B2796803
theorem B2798423 : Blo 1863633 2798423 := bstep (se 1 (by rfl) ⟨2098817, by rfl⟩ : syracuseStep 2798423 = 4197635) B4197635
theorem B1864555 : Blo 1863633 1864555 := bstep (se 1 (by rfl) ⟨1398416, by rfl⟩ : syracuseStep 1864555 = 2796833) B2796833
theorem B1864567 : Blo 1863633 1864567 := bstep (se 1 (by rfl) ⟨1398425, by rfl⟩ : syracuseStep 1864567 = 2796851) B2796851
theorem B1864587 : Blo 1863633 1864587 := bstep (se 1 (by rfl) ⟨1398440, by rfl⟩ : syracuseStep 1864587 = 2796881) B2796881
theorem B1864599 : Blo 1863633 1864599 := bstep (se 1 (by rfl) ⟨1398449, by rfl⟩ : syracuseStep 1864599 = 2796899) B2796899
theorem B7082903 : Blo 1863633 7082903 := bstep (se 1 (by rfl) ⟨5312177, by rfl⟩ : syracuseStep 7082903 = 10624355) B10624355
theorem B1864619 : Blo 1863633 1864619 := bstep (se 1 (by rfl) ⟨1398464, by rfl⟩ : syracuseStep 1864619 = 2796929) B2796929
theorem B6722477 : Blo 1863633 6722477 := bstep (se 3 (by rfl) ⟨1260464, by rfl⟩ : syracuseStep 6722477 = 2520929) B2520929
theorem B1864631 : Blo 1863633 1864631 := bstep (se 1 (by rfl) ⟨1398473, by rfl⟩ : syracuseStep 1864631 = 2796947) B2796947
theorem B1864651 : Blo 1863633 1864651 := bstep (se 1 (by rfl) ⟨1398488, by rfl⟩ : syracuseStep 1864651 = 2796977) B2796977
theorem B1864663 : Blo 1863633 1864663 := bstep (se 1 (by rfl) ⟨1398497, by rfl⟩ : syracuseStep 1864663 = 2796995) B2796995
theorem B1864683 : Blo 1863633 1864683 := bstep (se 1 (by rfl) ⟨1398512, by rfl⟩ : syracuseStep 1864683 = 2797025) B2797025
theorem B1864695 : Blo 1863633 1864695 := bstep (se 1 (by rfl) ⟨1398521, by rfl⟩ : syracuseStep 1864695 = 2797043) B2797043
theorem B1864715 : Blo 1863633 1864715 := bstep (se 1 (by rfl) ⟨1398536, by rfl⟩ : syracuseStep 1864715 = 2797073) B2797073
theorem B7173137 : Blo 1863633 7173137 := bstep (se 2 (by rfl) ⟨2689926, by rfl⟩ : syracuseStep 7173137 = 5379853) B5379853
theorem B1864727 : Blo 1863633 1864727 := bstep (se 1 (by rfl) ⟨1398545, by rfl⟩ : syracuseStep 1864727 = 2797091) B2797091
theorem B1864747 : Blo 1863633 1864747 := bstep (se 1 (by rfl) ⟨1398560, by rfl⟩ : syracuseStep 1864747 = 2797121) B2797121
theorem B1889335 : Blo 1863633 1889335 := bstep (se 1 (by rfl) ⟨1417001, by rfl⟩ : syracuseStep 1889335 = 2834003) B2834003
theorem B1864759 : Blo 1863633 1864759 := bstep (se 1 (by rfl) ⟨1398569, by rfl⟩ : syracuseStep 1864759 = 2797139) B2797139
theorem B1864779 : Blo 1863633 1864779 := bstep (se 1 (by rfl) ⟨1398584, by rfl⟩ : syracuseStep 1864779 = 2797169) B2797169
theorem B1864791 : Blo 1863633 1864791 := bstep (se 1 (by rfl) ⟨1398593, by rfl⟩ : syracuseStep 1864791 = 2797187) B2797187
theorem B14152805 : Blo 1863633 14152805 := bstep (se 4 (by rfl) ⟨1326825, by rfl⟩ : syracuseStep 14152805 = 2653651) B2653651
theorem B1864811 : Blo 1863633 1864811 := bstep (se 1 (by rfl) ⟨1398608, by rfl⟩ : syracuseStep 1864811 = 2797217) B2797217
theorem B1864823 : Blo 1863633 1864823 := bstep (se 1 (by rfl) ⟨1398617, by rfl⟩ : syracuseStep 1864823 = 2797235) B2797235
theorem B1864843 : Blo 1863633 1864843 := bstep (se 1 (by rfl) ⟨1398632, by rfl⟩ : syracuseStep 1864843 = 2797265) B2797265
theorem B1864855 : Blo 1863633 1864855 := bstep (se 1 (by rfl) ⟨1398641, by rfl⟩ : syracuseStep 1864855 = 2797283) B2797283
theorem B1864875 : Blo 1863633 1864875 := bstep (se 1 (by rfl) ⟨1398656, by rfl⟩ : syracuseStep 1864875 = 2797313) B2797313
theorem B1864887 : Blo 1863633 1864887 := bstep (se 1 (by rfl) ⟨1398665, by rfl⟩ : syracuseStep 1864887 = 2797331) B2797331
theorem B1864907 : Blo 1863633 1864907 := bstep (se 1 (by rfl) ⟨1398680, by rfl⟩ : syracuseStep 1864907 = 2797361) B2797361
theorem B1864919 : Blo 1863633 1864919 := bstep (se 1 (by rfl) ⟨1398689, by rfl⟩ : syracuseStep 1864919 = 2797379) B2797379
theorem B1864939 : Blo 1863633 1864939 := bstep (se 1 (by rfl) ⟨1398704, by rfl⟩ : syracuseStep 1864939 = 2797409) B2797409
theorem B1864951 : Blo 1863633 1864951 := bstep (se 1 (by rfl) ⟨1398713, by rfl⟩ : syracuseStep 1864951 = 2797427) B2797427
theorem B20428037 : Blo 1863633 20428037 := bstep (se 4 (by rfl) ⟨1915128, by rfl⟩ : syracuseStep 20428037 = 3830257) B3830257
theorem B1864971 : Blo 1863633 1864971 := bstep (se 1 (by rfl) ⟨1398728, by rfl⟩ : syracuseStep 1864971 = 2797457) B2797457
theorem B1864983 : Blo 1863633 1864983 := bstep (se 1 (by rfl) ⟨1398737, by rfl⟩ : syracuseStep 1864983 = 2797475) B2797475
theorem B1865003 : Blo 1863633 1865003 := bstep (se 1 (by rfl) ⟨1398752, by rfl⟩ : syracuseStep 1865003 = 2797505) B2797505
theorem B1865015 : Blo 1863633 1865015 := bstep (se 1 (by rfl) ⟨1398761, by rfl⟩ : syracuseStep 1865015 = 2797523) B2797523
theorem B12105035 : Blo 1863633 12105035 := bstep (se 1 (by rfl) ⟨9078776, by rfl⟩ : syracuseStep 12105035 = 18157553) B18157553
theorem B1865035 : Blo 1863633 1865035 := bstep (se 1 (by rfl) ⟨1398776, by rfl⟩ : syracuseStep 1865035 = 2797553) B2797553
theorem B1865047 : Blo 1863633 1865047 := bstep (se 1 (by rfl) ⟨1398785, by rfl⟩ : syracuseStep 1865047 = 2797571) B2797571
theorem B1865067 : Blo 1863633 1865067 := bstep (se 1 (by rfl) ⟨1398800, by rfl⟩ : syracuseStep 1865067 = 2797601) B2797601
theorem B4035955 : Blo 1863633 4035955 := bstep (se 1 (by rfl) ⟨3026966, by rfl⟩ : syracuseStep 4035955 = 6053933) B6053933
theorem B1865079 : Blo 1863633 1865079 := bstep (se 1 (by rfl) ⟨1398809, by rfl⟩ : syracuseStep 1865079 = 2797619) B2797619
theorem B7968131 : Blo 1863633 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B1865099 : Blo 1863633 1865099 := bstep (se 1 (by rfl) ⟨1398824, by rfl⟩ : syracuseStep 1865099 = 2797649) B2797649
theorem B1865111 : Blo 1863633 1865111 := bstep (se 1 (by rfl) ⟨1398833, by rfl⟩ : syracuseStep 1865111 = 2797667) B2797667
theorem B1865131 : Blo 1863633 1865131 := bstep (se 1 (by rfl) ⟨1398848, by rfl⟩ : syracuseStep 1865131 = 2797697) B2797697
theorem B1865143 : Blo 1863633 1865143 := bstep (se 1 (by rfl) ⟨1398857, by rfl⟩ : syracuseStep 1865143 = 2797715) B2797715
theorem B1865163 : Blo 1863633 1865163 := bstep (se 1 (by rfl) ⟨1398872, by rfl⟩ : syracuseStep 1865163 = 2797745) B2797745
theorem B1865175 : Blo 1863633 1865175 := bstep (se 1 (by rfl) ⟨1398881, by rfl⟩ : syracuseStep 1865175 = 2797763) B2797763
theorem B1865195 : Blo 1863633 1865195 := bstep (se 1 (by rfl) ⟨1398896, by rfl⟩ : syracuseStep 1865195 = 2797793) B2797793
theorem B1865207 : Blo 1863633 1865207 := bstep (se 1 (by rfl) ⟨1398905, by rfl⟩ : syracuseStep 1865207 = 2797811) B2797811
theorem B3831307 : Blo 1863633 3831307 := bstep (se 1 (by rfl) ⟨2873480, by rfl⟩ : syracuseStep 3831307 = 5746961) B5746961
theorem B1865227 : Blo 1863633 1865227 := bstep (se 1 (by rfl) ⟨1398920, by rfl⟩ : syracuseStep 1865227 = 2797841) B2797841
theorem B1865239 : Blo 1863633 1865239 := bstep (se 1 (by rfl) ⟨1398929, by rfl⟩ : syracuseStep 1865239 = 2797859) B2797859
theorem B1865259 : Blo 1863633 1865259 := bstep (se 1 (by rfl) ⟨1398944, by rfl⟩ : syracuseStep 1865259 = 2797889) B2797889
theorem B7083571 : Blo 1863633 7083571 := bstep (se 1 (by rfl) ⟨5312678, by rfl⟩ : syracuseStep 7083571 = 10625357) B10625357
theorem B1865271 : Blo 1863633 1865271 := bstep (se 1 (by rfl) ⟨1398953, by rfl⟩ : syracuseStep 1865271 = 2797907) B2797907
theorem B14153291 : Blo 1863633 14153291 := bstep (se 1 (by rfl) ⟨10614968, by rfl⟩ : syracuseStep 14153291 = 21229937) B21229937
theorem B1865291 : Blo 1863633 1865291 := bstep (se 1 (by rfl) ⟨1398968, by rfl⟩ : syracuseStep 1865291 = 2797937) B2797937
theorem B1865303 : Blo 1863633 1865303 := bstep (se 1 (by rfl) ⟨1398977, by rfl⟩ : syracuseStep 1865303 = 2797955) B2797955
theorem B9434717 : Blo 1863633 9434717 := bstep (se 3 (by rfl) ⟨1769009, by rfl⟩ : syracuseStep 9434717 = 3538019) B3538019
theorem B1865323 : Blo 1863633 1865323 := bstep (se 1 (by rfl) ⟨1398992, by rfl⟩ : syracuseStep 1865323 = 2797985) B2797985
theorem B1865335 : Blo 1863633 1865335 := bstep (se 1 (by rfl) ⟨1399001, by rfl⟩ : syracuseStep 1865335 = 2798003) B2798003
theorem B1865355 : Blo 1863633 1865355 := bstep (se 1 (by rfl) ⟨1399016, by rfl⟩ : syracuseStep 1865355 = 2798033) B2798033
theorem B4478615 : Blo 1863633 4478615 := bstep (se 1 (by rfl) ⟨3358961, by rfl⟩ : syracuseStep 4478615 = 6717923) B6717923
theorem B13620887 : Blo 1863633 13620887 := bstep (se 1 (by rfl) ⟨10215665, by rfl⟩ : syracuseStep 13620887 = 20431331) B20431331
theorem B1865367 : Blo 1863633 1865367 := bstep (se 1 (by rfl) ⟨1399025, by rfl⟩ : syracuseStep 1865367 = 2798051) B2798051
theorem B1865387 : Blo 1863633 1865387 := bstep (se 1 (by rfl) ⟨1399040, by rfl⟩ : syracuseStep 1865387 = 2798081) B2798081
theorem B1865399 : Blo 1863633 1865399 := bstep (se 1 (by rfl) ⟨1399049, by rfl⟩ : syracuseStep 1865399 = 2798099) B2798099
theorem B1865419 : Blo 1863633 1865419 := bstep (se 1 (by rfl) ⟨1399064, by rfl⟩ : syracuseStep 1865419 = 2798129) B2798129
theorem B1865431 : Blo 1863633 1865431 := bstep (se 1 (by rfl) ⟨1399073, by rfl⟩ : syracuseStep 1865431 = 2798147) B2798147
theorem B1865451 : Blo 1863633 1865451 := bstep (se 1 (by rfl) ⟨1399088, by rfl⟩ : syracuseStep 1865451 = 2798177) B2798177
theorem B1865463 : Blo 1863633 1865463 := bstep (se 1 (by rfl) ⟨1399097, by rfl⟩ : syracuseStep 1865463 = 2798195) B2798195
theorem B1865483 : Blo 1863633 1865483 := bstep (se 1 (by rfl) ⟨1399112, by rfl⟩ : syracuseStep 1865483 = 2798225) B2798225
theorem B1865495 : Blo 1863633 1865495 := bstep (se 1 (by rfl) ⟨1399121, by rfl⟩ : syracuseStep 1865495 = 2798243) B2798243
theorem B1865515 : Blo 1863633 1865515 := bstep (se 1 (by rfl) ⟨1399136, by rfl⟩ : syracuseStep 1865515 = 2798273) B2798273
theorem B1865527 : Blo 1863633 1865527 := bstep (se 1 (by rfl) ⟨1399145, by rfl⟩ : syracuseStep 1865527 = 2798291) B2798291
theorem B15931201 : Blo 1863633 15931201 := bstep (se 2 (by rfl) ⟨5974200, by rfl⟩ : syracuseStep 15931201 = 11948401) B11948401
theorem B11949889 : Blo 1863633 11949889 := bstep (se 2 (by rfl) ⟨4481208, by rfl⟩ : syracuseStep 11949889 = 8962417) B8962417
theorem B1865547 : Blo 1863633 1865547 := bstep (se 1 (by rfl) ⟨1399160, by rfl⟩ : syracuseStep 1865547 = 2798321) B2798321
theorem B1865559 : Blo 1863633 1865559 := bstep (se 1 (by rfl) ⟨1399169, by rfl⟩ : syracuseStep 1865559 = 2798339) B2798339
theorem B1865579 : Blo 1863633 1865579 := bstep (se 1 (by rfl) ⟨1399184, by rfl⟩ : syracuseStep 1865579 = 2798369) B2798369
theorem B1865591 : Blo 1863633 1865591 := bstep (se 1 (by rfl) ⟨1399193, by rfl⟩ : syracuseStep 1865591 = 2798387) B2798387
theorem B1865611 : Blo 1863633 1865611 := bstep (se 1 (by rfl) ⟨1399208, by rfl⟩ : syracuseStep 1865611 = 2798417) B2798417
theorem B1865623 : Blo 1863633 1865623 := bstep (se 1 (by rfl) ⟨1399217, by rfl⟩ : syracuseStep 1865623 = 2798435) B2798435
theorem B7076099 : Blo 1863633 7076099 := bstep (se 1 (by rfl) ⟨5307074, by rfl⟩ : syracuseStep 7076099 = 10614149) B10614149
theorem B4479383 : Blo 1863633 4479383 := bstep (se 1 (by rfl) ⟨3359537, by rfl⟩ : syracuseStep 4479383 = 6719075) B6719075
theorem B45382157 : Blo 1863633 45382157 := bstep (se 3 (by rfl) ⟨8509154, by rfl⟩ : syracuseStep 45382157 = 17018309) B17018309
theorem B1890859 : Blo 1863633 1890859 := bstep (se 1 (by rfl) ⟨1418144, by rfl⟩ : syracuseStep 1890859 = 2836289) B2836289
theorem B14162525 : Blo 1863633 14162525 := bstep (se 3 (by rfl) ⟨2655473, by rfl⟩ : syracuseStep 14162525 = 5310947) B5310947
theorem B10623581 : Blo 1863633 10623581 := bstep (se 3 (by rfl) ⟨1991921, by rfl⟩ : syracuseStep 10623581 = 3983843) B3983843
theorem B7076555 : Blo 1863633 7076555 := bstep (se 1 (by rfl) ⟨5307416, by rfl⟩ : syracuseStep 7076555 = 10614833) B10614833
theorem B9444113 : Blo 1863633 9444113 := bstep (se 2 (by rfl) ⟨3541542, by rfl⟩ : syracuseStep 9444113 = 7083085) B7083085
theorem B5307211 : Blo 1863633 5307211 := bstep (se 1 (by rfl) ⟨3980408, by rfl⟩ : syracuseStep 5307211 = 7960817) B7960817
theorem B5380939 : Blo 1863633 5380939 := bstep (se 1 (by rfl) ⟨4035704, by rfl⟩ : syracuseStep 5380939 = 8071409) B8071409
theorem B7076753 : Blo 1863633 7076753 := bstep (se 2 (by rfl) ⟨2653782, by rfl⟩ : syracuseStep 7076753 = 5307565) B5307565
theorem B9444275 : Blo 1863633 9444275 := bstep (se 1 (by rfl) ⟨7083206, by rfl⟩ : syracuseStep 9444275 = 14166413) B14166413
theorem B4193369 : Blo 1863633 4193369 := bstep (se 2 (by rfl) ⟨1572513, by rfl⟩ : syracuseStep 4193369 = 3145027) B3145027
theorem B23903363 : Blo 1863633 23903363 := bstep (se 1 (by rfl) ⟨17927522, by rfl⟩ : syracuseStep 23903363 = 35855045) B35855045
theorem B3538073 : Blo 1863633 3538073 := bstep (se 2 (by rfl) ⟨1326777, by rfl⟩ : syracuseStep 3538073 = 2653555) B2653555
theorem B4193459 : Blo 1863633 4193459 := bstep (se 1 (by rfl) ⟨3145094, by rfl⟩ : syracuseStep 4193459 = 6290189) B6290189
theorem B3144919 : Blo 1863633 3144919 := bstep (se 1 (by rfl) ⟨2358689, by rfl⟩ : syracuseStep 3144919 = 4717379) B4717379
theorem B4193495 : Blo 1863633 4193495 := bstep (se 1 (by rfl) ⟨3145121, by rfl⟩ : syracuseStep 4193495 = 6290243) B6290243
theorem B5307713 : Blo 1863633 5307713 := bstep (se 2 (by rfl) ⟨1990392, by rfl⟩ : syracuseStep 5307713 = 3980785) B3980785
theorem B4193675 : Blo 1863633 4193675 := bstep (se 1 (by rfl) ⟨3145256, by rfl⟩ : syracuseStep 4193675 = 6290513) B6290513
theorem B4193729 : Blo 1863633 4193729 := bstep (se 2 (by rfl) ⟨1572648, by rfl⟩ : syracuseStep 4193729 = 3145297) B3145297
theorem B4718027 : Blo 1863633 4718027 := bstep (se 1 (by rfl) ⟨3538520, by rfl⟩ : syracuseStep 4718027 = 7077041) B7077041
theorem B6290891 : Blo 1863633 6290891 := bstep (se 1 (by rfl) ⟨4718168, by rfl⟩ : syracuseStep 6290891 = 9436337) B9436337
theorem B2096599 : Blo 1863633 2096599 := bstep (se 1 (by rfl) ⟨1572449, by rfl⟩ : syracuseStep 2096599 = 3144899) B3144899
theorem B5971421 : Blo 1863633 5971421 := bstep (se 3 (by rfl) ⟨1119641, by rfl⟩ : syracuseStep 5971421 = 2239283) B2239283
theorem B4308595 : Blo 1863633 4308595 := bstep (se 1 (by rfl) ⟨3231446, by rfl⟩ : syracuseStep 4308595 = 6462893) B6462893
theorem B2096779 : Blo 1863633 2096779 := bstep (se 1 (by rfl) ⟨1572584, by rfl⟩ : syracuseStep 2096779 = 3145169) B3145169
theorem B5308055 : Blo 1863633 5308055 := bstep (se 1 (by rfl) ⟨3981041, by rfl⟩ : syracuseStep 5308055 = 7962083) B7962083
theorem B7077527 : Blo 1863633 7077527 := bstep (se 1 (by rfl) ⟨5308145, by rfl⟩ : syracuseStep 7077527 = 10616291) B10616291
theorem B4193945 : Blo 1863633 4193945 := bstep (se 2 (by rfl) ⟨1572729, by rfl⟩ : syracuseStep 4193945 = 3145459) B3145459
theorem B9436823 : Blo 1863633 9436823 := bstep (se 1 (by rfl) ⟨7077617, by rfl⟩ : syracuseStep 9436823 = 14155235) B14155235
theorem B11337367 : Blo 1863633 11337367 := bstep (se 1 (by rfl) ⟨8503025, by rfl⟩ : syracuseStep 11337367 = 17006051) B17006051
theorem B6291161 : Blo 1863633 6291161 := bstep (se 2 (by rfl) ⟨2359185, by rfl⟩ : syracuseStep 6291161 = 4718371) B4718371
theorem B4194035 : Blo 1863633 4194035 := bstep (se 1 (by rfl) ⟨3145526, by rfl⟩ : syracuseStep 4194035 = 6291053) B6291053
theorem B2096887 : Blo 1863633 2096887 := bstep (se 1 (by rfl) ⟨1572665, by rfl⟩ : syracuseStep 2096887 = 3145331) B3145331
theorem B4194071 : Blo 1863633 4194071 := bstep (se 1 (by rfl) ⟨3145553, by rfl⟩ : syracuseStep 4194071 = 6291107) B6291107
theorem B3145547 : Blo 1863633 3145547 := bstep (se 1 (by rfl) ⟨2359160, by rfl⟩ : syracuseStep 3145547 = 4718321) B4718321
theorem B7962457 : Blo 1863633 7962457 := bstep (se 2 (by rfl) ⟨2985921, by rfl⟩ : syracuseStep 7962457 = 5971843) B5971843
theorem B4783961 : Blo 1863633 4783961 := bstep (se 2 (by rfl) ⟨1793985, by rfl⟩ : syracuseStep 4783961 = 3587971) B3587971
theorem B7077725 : Blo 1863633 7077725 := bstep (se 3 (by rfl) ⟨1327073, by rfl⟩ : syracuseStep 7077725 = 2654147) B2654147
theorem B26869603 : Blo 1863633 26869603 := bstep (se 1 (by rfl) ⟨20152202, by rfl⟩ : syracuseStep 26869603 = 40304405) B40304405
theorem B3358579 : Blo 1863633 3358579 := bstep (se 1 (by rfl) ⟨2518934, by rfl⟩ : syracuseStep 3358579 = 5037869) B5037869
theorem B2097067 : Blo 1863633 2097067 := bstep (se 1 (by rfl) ⟨1572800, by rfl⟩ : syracuseStep 2097067 = 3145601) B3145601
theorem B12754867 : Blo 1863633 12754867 := bstep (se 1 (by rfl) ⟨9566150, by rfl⟩ : syracuseStep 12754867 = 19132301) B19132301
theorem B3145675 : Blo 1863633 3145675 := bstep (se 1 (by rfl) ⟨2359256, by rfl⟩ : syracuseStep 3145675 = 4718513) B4718513
theorem B4194251 : Blo 1863633 4194251 := bstep (se 1 (by rfl) ⟨3145688, by rfl⟩ : syracuseStep 4194251 = 6291377) B6291377
theorem B6291485 : Blo 1863633 6291485 := bstep (se 3 (by rfl) ⟨1179653, by rfl⟩ : syracuseStep 6291485 = 2359307) B2359307
theorem B2834489 : Blo 1863633 2834489 := bstep (se 2 (by rfl) ⟨1062933, by rfl⟩ : syracuseStep 2834489 = 2125867) B2125867
theorem B5038139 : Blo 1863633 5038139 := bstep (se 1 (by rfl) ⟨3778604, by rfl⟩ : syracuseStep 5038139 = 7557209) B7557209
theorem B2097211 : Blo 1863633 2097211 := bstep (se 1 (by rfl) ⟨1572908, by rfl⟩ : syracuseStep 2097211 = 3145817) B3145817
theorem B4194575 : Blo 1863633 4194575 := bstep (se 1 (by rfl) ⟨3145931, by rfl⟩ : syracuseStep 4194575 = 6291863) B6291863
theorem B3145999 : Blo 1863633 3145999 := bstep (se 1 (by rfl) ⟨2359499, by rfl⟩ : syracuseStep 3145999 = 4718999) B4718999
theorem B4194593 : Blo 1863633 4194593 := bstep (se 2 (by rfl) ⟨1572972, by rfl⟩ : syracuseStep 4194593 = 3145945) B3145945
theorem B5308715 : Blo 1863633 5308715 := bstep (se 1 (by rfl) ⟨3981536, by rfl⟩ : syracuseStep 5308715 = 7963073) B7963073
theorem B2834731 : Blo 1863633 2834731 := bstep (se 1 (by rfl) ⟨2126048, by rfl⟩ : syracuseStep 2834731 = 4252097) B4252097
theorem B4784503 : Blo 1863633 4784503 := bstep (se 1 (by rfl) ⟨3588377, by rfl⟩ : syracuseStep 4784503 = 7176755) B7176755
theorem B2359687 : Blo 1863633 2359687 := bstep (se 1 (by rfl) ⟨1769765, by rfl⟩ : syracuseStep 2359687 = 3539531) B3539531
theorem B7561619 : Blo 1863633 7561619 := bstep (se 1 (by rfl) ⟨5671214, by rfl⟩ : syracuseStep 7561619 = 11342429) B11342429
theorem B2097679 : Blo 1863633 2097679 := bstep (se 1 (by rfl) ⟨1573259, by rfl⟩ : syracuseStep 2097679 = 3146519) B3146519
theorem B4481651 : Blo 1863633 4481651 := bstep (se 1 (by rfl) ⟨3361238, by rfl⟩ : syracuseStep 4481651 = 6722477) B6722477
theorem B4194935 : Blo 1863633 4194935 := bstep (se 1 (by rfl) ⟨3146201, by rfl⟩ : syracuseStep 4194935 = 6292403) B6292403
theorem B34030199 : Blo 1863633 34030199 := bstep (se 1 (by rfl) ⟨25522649, by rfl⟩ : syracuseStep 34030199 = 51045299) B51045299
theorem B4195115 : Blo 1863633 4195115 := bstep (se 1 (by rfl) ⟨3146336, by rfl⟩ : syracuseStep 4195115 = 6292673) B6292673
theorem B3146539 : Blo 1863633 3146539 := bstep (se 1 (by rfl) ⟨2359904, by rfl⟩ : syracuseStep 3146539 = 4719809) B4719809
theorem B2360107 : Blo 1863633 2360107 := bstep (se 1 (by rfl) ⟨1770080, by rfl⟩ : syracuseStep 2360107 = 3540161) B3540161
theorem B8070023 : Blo 1863633 8070023 := bstep (se 1 (by rfl) ⟨6052517, by rfl⟩ : syracuseStep 8070023 = 12105035) B12105035
theorem B3146681 : Blo 1863633 3146681 := bstep (se 2 (by rfl) ⟨1180005, by rfl⟩ : syracuseStep 3146681 = 2360011) B2360011
theorem B4719617 : Blo 1863633 4719617 := bstep (se 2 (by rfl) ⟨1769856, by rfl⟩ : syracuseStep 4719617 = 3539713) B3539713
theorem B2098183 : Blo 1863633 2098183 := bstep (se 1 (by rfl) ⟨1573637, by rfl⟩ : syracuseStep 2098183 = 3147275) B3147275
theorem B2360335 : Blo 1863633 2360335 := bstep (se 1 (by rfl) ⟨1770251, by rfl⟩ : syracuseStep 2360335 = 3540503) B3540503
theorem B23905367 : Blo 1863633 23905367 := bstep (se 1 (by rfl) ⟨17929025, by rfl⟩ : syracuseStep 23905367 = 35858051) B35858051
theorem B4195475 : Blo 1863633 4195475 := bstep (se 1 (by rfl) ⟨3146606, by rfl⟩ : syracuseStep 4195475 = 6293213) B6293213
theorem B3540115 : Blo 1863633 3540115 := bstep (se 1 (by rfl) ⟨2655086, by rfl⟩ : syracuseStep 3540115 = 5310173) B5310173
theorem B2098363 : Blo 1863633 2098363 := bstep (se 1 (by rfl) ⟨1573772, by rfl⟩ : syracuseStep 2098363 = 3147545) B3147545
theorem B9077953 : Blo 1863633 9077953 := bstep (se 2 (by rfl) ⟨3404232, by rfl⟩ : syracuseStep 9077953 = 6808465) B6808465
theorem B4195529 : Blo 1863633 4195529 := bstep (se 2 (by rfl) ⟨1573323, by rfl⟩ : syracuseStep 4195529 = 3146647) B3146647
theorem B7079183 : Blo 1863633 7079183 := bstep (se 1 (by rfl) ⟨5309387, by rfl⟩ : syracuseStep 7079183 = 10618775) B10618775
theorem B8504635 : Blo 1863633 8504635 := bstep (se 1 (by rfl) ⟨6378476, by rfl⟩ : syracuseStep 8504635 = 12756953) B12756953
theorem B4719991 : Blo 1863633 4719991 := bstep (se 1 (by rfl) ⟨3539993, by rfl⟩ : syracuseStep 4719991 = 7079987) B7079987
theorem B3540343 : Blo 1863633 3540343 := bstep (se 1 (by rfl) ⟨2655257, by rfl⟩ : syracuseStep 3540343 = 5310515) B5310515
theorem B9569681 : Blo 1863633 9569681 := bstep (se 2 (by rfl) ⟨3588630, by rfl⟩ : syracuseStep 9569681 = 7177261) B7177261
theorem B6292889 : Blo 1863633 6292889 := bstep (se 2 (by rfl) ⟨2359833, by rfl⟩ : syracuseStep 6292889 = 4719667) B4719667
theorem B47777201 : Blo 1863633 47777201 := bstep (se 2 (by rfl) ⟨17916450, by rfl⟩ : syracuseStep 47777201 = 35832901) B35832901
theorem B15926827 : Blo 1863633 15926827 := bstep (se 1 (by rfl) ⟨11945120, by rfl⟩ : syracuseStep 15926827 = 23890241) B23890241
theorem B16582211 : Blo 1863633 16582211 := bstep (se 1 (by rfl) ⟨12436658, by rfl⟩ : syracuseStep 16582211 = 24873317) B24873317
theorem B3147383 : Blo 1863633 3147383 := bstep (se 1 (by rfl) ⟨2360537, by rfl⟩ : syracuseStep 3147383 = 4721075) B4721075
theorem B2098831 : Blo 1863633 2098831 := bstep (se 1 (by rfl) ⟨1574123, by rfl⟩ : syracuseStep 2098831 = 3148247) B3148247
theorem B30254771 : Blo 1863633 30254771 := bstep (se 1 (by rfl) ⟨22691078, by rfl⟩ : syracuseStep 30254771 = 45382157) B45382157
theorem B2361079 : Blo 1863633 2361079 := bstep (se 1 (by rfl) ⟨1770809, by rfl⟩ : syracuseStep 2361079 = 3541619) B3541619
theorem B4720427 : Blo 1863633 4720427 := bstep (se 1 (by rfl) ⟨3540320, by rfl⟩ : syracuseStep 4720427 = 7080641) B7080641
theorem B73664369 : Blo 1863633 73664369 := bstep (se 2 (by rfl) ⟨27624138, by rfl⟩ : syracuseStep 73664369 = 55248277) B55248277
theorem B9439091 : Blo 1863633 9439091 := bstep (se 1 (by rfl) ⟨7079318, by rfl⟩ : syracuseStep 9439091 = 14158637) B14158637
theorem B4196231 : Blo 1863633 4196231 := bstep (se 1 (by rfl) ⟨3147173, by rfl⟩ : syracuseStep 4196231 = 6294347) B6294347
theorem B5310355 : Blo 1863633 5310355 := bstep (se 1 (by rfl) ⟨3982766, by rfl⟩ : syracuseStep 5310355 = 7965533) B7965533
theorem B2795465 : Blo 1863633 2795465 := bstep (se 2 (by rfl) ⟨1048299, by rfl⟩ : syracuseStep 2795465 = 2096599) B2096599
theorem B2656271 : Blo 1863633 2656271 := bstep (se 1 (by rfl) ⟨1992203, by rfl⟩ : syracuseStep 2656271 = 3984407) B3984407
theorem B2795579 : Blo 1863633 2795579 := bstep (se 1 (by rfl) ⟨2096684, by rfl⟩ : syracuseStep 2795579 = 4193369) B4193369
theorem B4196411 : Blo 1863633 4196411 := bstep (se 1 (by rfl) ⟨3147308, by rfl⟩ : syracuseStep 4196411 = 6294617) B6294617
theorem B3147835 : Blo 1863633 3147835 := bstep (se 1 (by rfl) ⟨2360876, by rfl⟩ : syracuseStep 3147835 = 4721753) B4721753
theorem B6293591 : Blo 1863633 6293591 := bstep (se 1 (by rfl) ⟨4720193, by rfl⟩ : syracuseStep 6293591 = 9440387) B9440387
theorem B15935575 : Blo 1863633 15935575 := bstep (se 1 (by rfl) ⟨11951681, by rfl⟩ : syracuseStep 15935575 = 23903363) B23903363
theorem B2795639 : Blo 1863633 2795639 := bstep (se 1 (by rfl) ⟨2096729, by rfl⟩ : syracuseStep 2795639 = 4193459) B4193459
theorem B2795663 : Blo 1863633 2795663 := bstep (se 1 (by rfl) ⟨2096747, by rfl⟩ : syracuseStep 2795663 = 4193495) B4193495
theorem B2795705 : Blo 1863633 2795705 := bstep (se 2 (by rfl) ⟨1048389, by rfl⟩ : syracuseStep 2795705 = 2096779) B2096779
theorem B4196537 : Blo 1863633 4196537 := bstep (se 2 (by rfl) ⟨1573701, by rfl⟩ : syracuseStep 4196537 = 3147403) B3147403
theorem B15116489 : Blo 1863633 15116489 := bstep (se 2 (by rfl) ⟨5668683, by rfl⟩ : syracuseStep 15116489 = 11337367) B11337367
theorem B3147977 : Blo 1863633 3147977 := bstep (se 2 (by rfl) ⟨1180491, by rfl⟩ : syracuseStep 3147977 = 2360983) B2360983
theorem B2795783 : Blo 1863633 2795783 := bstep (se 1 (by rfl) ⟨2096837, by rfl⟩ : syracuseStep 2795783 = 4193675) B4193675
theorem B2795819 : Blo 1863633 2795819 := bstep (se 1 (by rfl) ⟨2096864, by rfl⟩ : syracuseStep 2795819 = 4193729) B4193729
theorem B11340091 : Blo 1863633 11340091 := bstep (se 1 (by rfl) ⟨8505068, by rfl⟩ : syracuseStep 11340091 = 17010137) B17010137
theorem B2795849 : Blo 1863633 2795849 := bstep (se 2 (by rfl) ⟨1048443, by rfl⟩ : syracuseStep 2795849 = 2096887) B2096887
theorem B9439577 : Blo 1863633 9439577 := bstep (se 2 (by rfl) ⟨3539841, by rfl⟩ : syracuseStep 9439577 = 7079683) B7079683
theorem B91916693 : Blo 1863633 91916693 := bstep (se 6 (by rfl) ⟨2154297, by rfl⟩ : syracuseStep 91916693 = 4308595) B4308595
theorem B2795963 : Blo 1863633 2795963 := bstep (se 1 (by rfl) ⟨2096972, by rfl⟩ : syracuseStep 2795963 = 4193945) B4193945
theorem B35826137 : Blo 1863633 35826137 := bstep (se 2 (by rfl) ⟨13434801, by rfl⟩ : syracuseStep 35826137 = 26869603) B26869603
theorem B2796023 : Blo 1863633 2796023 := bstep (se 1 (by rfl) ⟨2097017, by rfl⟩ : syracuseStep 2796023 = 4194035) B4194035
theorem B2796047 : Blo 1863633 2796047 := bstep (se 1 (by rfl) ⟨2097035, by rfl⟩ : syracuseStep 2796047 = 4194071) B4194071
theorem B4196879 : Blo 1863633 4196879 := bstep (se 1 (by rfl) ⟨3147659, by rfl⟩ : syracuseStep 4196879 = 6295319) B6295319
theorem B4196897 : Blo 1863633 4196897 := bstep (se 2 (by rfl) ⟨1573836, by rfl⟩ : syracuseStep 4196897 = 3147673) B3147673
theorem B2796089 : Blo 1863633 2796089 := bstep (se 2 (by rfl) ⟨1048533, by rfl⟩ : syracuseStep 2796089 = 2097067) B2097067
theorem B3189307 : Blo 1863633 3189307 := bstep (se 1 (by rfl) ⟨2391980, by rfl⟩ : syracuseStep 3189307 = 4783961) B4783961
theorem B6294077 : Blo 1863633 6294077 := bstep (se 3 (by rfl) ⟨1180139, by rfl⟩ : syracuseStep 6294077 = 2360279) B2360279
theorem B21244517 : Blo 1863633 21244517 := bstep (se 4 (by rfl) ⟨1991673, by rfl⟩ : syracuseStep 21244517 = 3983347) B3983347
theorem B17926757 : Blo 1863633 17926757 := bstep (se 4 (by rfl) ⟨1680633, by rfl⟩ : syracuseStep 17926757 = 3361267) B3361267
theorem B4721267 : Blo 1863633 4721267 := bstep (se 1 (by rfl) ⟨3540950, by rfl⟩ : syracuseStep 4721267 = 7081901) B7081901
theorem B2796167 : Blo 1863633 2796167 := bstep (se 1 (by rfl) ⟨2097125, by rfl⟩ : syracuseStep 2796167 = 4194251) B4194251
theorem B4721287 : Blo 1863633 4721287 := bstep (se 1 (by rfl) ⟨3540965, by rfl⟩ : syracuseStep 4721287 = 7081931) B7081931
theorem B2796203 : Blo 1863633 2796203 := bstep (se 1 (by rfl) ⟨2097152, by rfl⟩ : syracuseStep 2796203 = 4194305) B4194305
theorem B18164401 : Blo 1863633 18164401 := bstep (se 2 (by rfl) ⟨6811650, by rfl⟩ : syracuseStep 18164401 = 13623301) B13623301
theorem B2796233 : Blo 1863633 2796233 := bstep (se 2 (by rfl) ⟨1048587, by rfl⟩ : syracuseStep 2796233 = 2097175) B2097175
theorem B5180105 : Blo 1863633 5180105 := bstep (se 2 (by rfl) ⟨1942539, by rfl⟩ : syracuseStep 5180105 = 3885079) B3885079
theorem B20433637 : Blo 1863633 20433637 := bstep (se 4 (by rfl) ⟨1915653, by rfl⟩ : syracuseStep 20433637 = 3831307) B3831307
theorem B2796347 : Blo 1863633 2796347 := bstep (se 1 (by rfl) ⟨2097260, by rfl⟩ : syracuseStep 2796347 = 4194521) B4194521
theorem B10619707 : Blo 1863633 10619707 := bstep (se 1 (by rfl) ⟨7964780, by rfl⟩ : syracuseStep 10619707 = 15929561) B15929561
theorem B7965499 : Blo 1863633 7965499 := bstep (se 1 (by rfl) ⟨5974124, by rfl⟩ : syracuseStep 7965499 = 11948249) B11948249
theorem B5974843 : Blo 1863633 5974843 := bstep (se 1 (by rfl) ⟨4481132, by rfl⟩ : syracuseStep 5974843 = 8962265) B8962265
theorem B14166899 : Blo 1863633 14166899 := bstep (se 1 (by rfl) ⟨10625174, by rfl⟩ : syracuseStep 14166899 = 21250349) B21250349
theorem B2796407 : Blo 1863633 2796407 := bstep (se 1 (by rfl) ⟨2097305, by rfl⟩ : syracuseStep 2796407 = 4194611) B4194611
theorem B4197239 : Blo 1863633 4197239 := bstep (se 1 (by rfl) ⟨3147929, by rfl⟩ : syracuseStep 4197239 = 6295859) B6295859
theorem B2796431 : Blo 1863633 2796431 := bstep (se 1 (by rfl) ⟨2097323, by rfl⟩ : syracuseStep 2796431 = 4194647) B4194647
theorem B4721561 : Blo 1863633 4721561 := bstep (se 2 (by rfl) ⟨1770585, by rfl⟩ : syracuseStep 4721561 = 3541171) B3541171
theorem B2796473 : Blo 1863633 2796473 := bstep (se 2 (by rfl) ⟨1048677, by rfl⟩ : syracuseStep 2796473 = 2097355) B2097355
theorem B2796551 : Blo 1863633 2796551 := bstep (se 1 (by rfl) ⟨2097413, by rfl⟩ : syracuseStep 2796551 = 4194827) B4194827
theorem B10079261 : Blo 1863633 10079261 := bstep (se 3 (by rfl) ⟨1889861, by rfl⟩ : syracuseStep 10079261 = 3779723) B3779723
theorem B2796587 : Blo 1863633 2796587 := bstep (se 1 (by rfl) ⟨2097440, by rfl⟩ : syracuseStep 2796587 = 4194881) B4194881
theorem B4197419 : Blo 1863633 4197419 := bstep (se 1 (by rfl) ⟨3148064, by rfl⟩ : syracuseStep 4197419 = 6296129) B6296129
theorem B4721723 : Blo 1863633 4721723 := bstep (se 1 (by rfl) ⟨3541292, by rfl⟩ : syracuseStep 4721723 = 7082585) B7082585
theorem B2796617 : Blo 1863633 2796617 := bstep (se 2 (by rfl) ⟨1048731, by rfl⟩ : syracuseStep 2796617 = 2097463) B2097463
theorem B2796731 : Blo 1863633 2796731 := bstep (se 1 (by rfl) ⟨2097548, by rfl⟩ : syracuseStep 2796731 = 4195097) B4195097
theorem B21523657 : Blo 1863633 21523657 := bstep (se 2 (by rfl) ⟨8071371, by rfl⟩ : syracuseStep 21523657 = 16142743) B16142743
theorem B2796791 : Blo 1863633 2796791 := bstep (se 1 (by rfl) ⟨2097593, by rfl⟩ : syracuseStep 2796791 = 4195187) B4195187
theorem B2239759 : Blo 1863633 2239759 := bstep (se 1 (by rfl) ⟨1679819, by rfl⟩ : syracuseStep 2239759 = 3359639) B3359639
theorem B2796815 : Blo 1863633 2796815 := bstep (se 1 (by rfl) ⟨2097611, by rfl⟩ : syracuseStep 2796815 = 4195223) B4195223
theorem B4721935 : Blo 1863633 4721935 := bstep (se 1 (by rfl) ⟨3541451, by rfl⟩ : syracuseStep 4721935 = 7082903) B7082903
theorem B5975329 : Blo 1863633 5975329 := bstep (se 2 (by rfl) ⟨2240748, by rfl⟩ : syracuseStep 5975329 = 4481497) B4481497
theorem B2796857 : Blo 1863633 2796857 := bstep (se 2 (by rfl) ⟨1048821, by rfl⟩ : syracuseStep 2796857 = 2097643) B2097643
theorem B64580923 : Blo 1863633 64580923 := bstep (se 1 (by rfl) ⟨48435692, by rfl⟩ : syracuseStep 64580923 = 96871385) B96871385
theorem B2796935 : Blo 1863633 2796935 := bstep (se 1 (by rfl) ⟨2097701, by rfl⟩ : syracuseStep 2796935 = 4195403) B4195403
theorem B2796971 : Blo 1863633 2796971 := bstep (se 1 (by rfl) ⟨2097728, by rfl⟩ : syracuseStep 2796971 = 4195457) B4195457
theorem B2797001 : Blo 1863633 2797001 := bstep (se 2 (by rfl) ⟨1048875, by rfl⟩ : syracuseStep 2797001 = 2097751) B2097751
theorem B13618691 : Blo 1863633 13618691 := bstep (se 1 (by rfl) ⟨10214018, by rfl⟩ : syracuseStep 13618691 = 20428037) B20428037
theorem B13438493 : Blo 1863633 13438493 := bstep (se 3 (by rfl) ⟨2519717, by rfl⟩ : syracuseStep 13438493 = 5039435) B5039435
theorem B4722209 : Blo 1863633 4722209 := bstep (se 2 (by rfl) ⟨1770828, by rfl⟩ : syracuseStep 4722209 = 3541657) B3541657
theorem B2797115 : Blo 1863633 2797115 := bstep (se 1 (by rfl) ⟨2097836, by rfl⟩ : syracuseStep 2797115 = 4195673) B4195673
theorem B5312087 : Blo 1863633 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B2797175 : Blo 1863633 2797175 := bstep (se 1 (by rfl) ⟨2097881, by rfl⟩ : syracuseStep 2797175 = 4195763) B4195763
theorem B2797199 : Blo 1863633 2797199 := bstep (se 1 (by rfl) ⟨2097899, by rfl⟩ : syracuseStep 2797199 = 4195799) B4195799
theorem B2797241 : Blo 1863633 2797241 := bstep (se 2 (by rfl) ⟨1048965, by rfl⟩ : syracuseStep 2797241 = 2097931) B2097931
theorem B2797319 : Blo 1863633 2797319 := bstep (se 1 (by rfl) ⟨2097989, by rfl⟩ : syracuseStep 2797319 = 4195979) B4195979
theorem B2985743 : Blo 1863633 2985743 := bstep (se 1 (by rfl) ⟨2239307, by rfl⟩ : syracuseStep 2985743 = 4478615) B4478615
theorem B9080591 : Blo 1863633 9080591 := bstep (se 1 (by rfl) ⟨6810443, by rfl⟩ : syracuseStep 9080591 = 13620887) B13620887
theorem B2797355 : Blo 1863633 2797355 := bstep (se 1 (by rfl) ⟨2098016, by rfl⟩ : syracuseStep 2797355 = 4196033) B4196033
theorem B2797385 : Blo 1863633 2797385 := bstep (se 2 (by rfl) ⟨1049019, by rfl⟩ : syracuseStep 2797385 = 2098039) B2098039
theorem B45993845 : Blo 1863633 45993845 := bstep (se 5 (by rfl) ⟨2155961, by rfl⟩ : syracuseStep 45993845 = 4311923) B4311923
theorem B6295481 : Blo 1863633 6295481 := bstep (se 2 (by rfl) ⟨2360805, by rfl⟩ : syracuseStep 6295481 = 4721611) B4721611
theorem B2797499 : Blo 1863633 2797499 := bstep (se 1 (by rfl) ⟨2098124, by rfl⟩ : syracuseStep 2797499 = 4196249) B4196249
theorem B2797559 : Blo 1863633 2797559 := bstep (se 1 (by rfl) ⟨2098169, by rfl⟩ : syracuseStep 2797559 = 4196339) B4196339
theorem B1863687 : Blo 1863633 1863687 := bstep (se 1 (by rfl) ⟨1397765, by rfl⟩ : syracuseStep 1863687 = 2795531) B2795531
theorem B20164619 : Blo 1863633 20164619 := bstep (se 1 (by rfl) ⟨15123464, by rfl⟩ : syracuseStep 20164619 = 30246929) B30246929
theorem B1863695 : Blo 1863633 1863695 := bstep (se 1 (by rfl) ⟨1397771, by rfl⟩ : syracuseStep 1863695 = 2795543) B2795543
theorem B2797583 : Blo 1863633 2797583 := bstep (se 1 (by rfl) ⟨2098187, by rfl⟩ : syracuseStep 2797583 = 4196375) B4196375
theorem B21245975 : Blo 1863633 21245975 := bstep (se 1 (by rfl) ⟨15934481, by rfl⟩ : syracuseStep 21245975 = 31868963) B31868963
theorem B15937559 : Blo 1863633 15937559 := bstep (se 1 (by rfl) ⟨11953169, by rfl⟩ : syracuseStep 15937559 = 23906339) B23906339
theorem B2797625 : Blo 1863633 2797625 := bstep (se 2 (by rfl) ⟨1049109, by rfl⟩ : syracuseStep 2797625 = 2098219) B2098219
theorem B1863739 : Blo 1863633 1863739 := bstep (se 1 (by rfl) ⟨1397804, by rfl⟩ : syracuseStep 1863739 = 2795609) B2795609
theorem B2519113 : Blo 1863633 2519113 := bstep (se 2 (by rfl) ⟨944667, by rfl⟩ : syracuseStep 2519113 = 1889335) B1889335
theorem B1863815 : Blo 1863633 1863815 := bstep (se 1 (by rfl) ⟨1397861, by rfl⟩ : syracuseStep 1863815 = 2795723) B2795723
theorem B2797703 : Blo 1863633 2797703 := bstep (se 1 (by rfl) ⟨2098277, by rfl⟩ : syracuseStep 2797703 = 4196555) B4196555
theorem B1863823 : Blo 1863633 1863823 := bstep (se 1 (by rfl) ⟨1397867, by rfl⟩ : syracuseStep 1863823 = 2795735) B2795735
theorem B2797739 : Blo 1863633 2797739 := bstep (se 1 (by rfl) ⟨2098304, by rfl⟩ : syracuseStep 2797739 = 4196609) B4196609
theorem B1863867 : Blo 1863633 1863867 := bstep (se 1 (by rfl) ⟨1397900, by rfl⟩ : syracuseStep 1863867 = 2795801) B2795801
theorem B2797769 : Blo 1863633 2797769 := bstep (se 2 (by rfl) ⟨1049163, by rfl⟩ : syracuseStep 2797769 = 2098327) B2098327
theorem B10621165 : Blo 1863633 10621165 := bstep (se 3 (by rfl) ⟨1991468, by rfl⟩ : syracuseStep 10621165 = 3982937) B3982937
theorem B1863943 : Blo 1863633 1863943 := bstep (se 1 (by rfl) ⟨1397957, by rfl⟩ : syracuseStep 1863943 = 2795915) B2795915
theorem B1863951 : Blo 1863633 1863951 := bstep (se 1 (by rfl) ⟨1397963, by rfl⟩ : syracuseStep 1863951 = 2795927) B2795927
theorem B2986255 : Blo 1863633 2986255 := bstep (se 1 (by rfl) ⟨2239691, by rfl⟩ : syracuseStep 2986255 = 4479383) B4479383
theorem B45363473 : Blo 1863633 45363473 := bstep (se 2 (by rfl) ⟨17011302, by rfl⟩ : syracuseStep 45363473 = 34022605) B34022605
theorem B1863995 : Blo 1863633 1863995 := bstep (se 1 (by rfl) ⟨1397996, by rfl⟩ : syracuseStep 1863995 = 2795993) B2795993
theorem B2797883 : Blo 1863633 2797883 := bstep (se 1 (by rfl) ⟨2098412, by rfl⟩ : syracuseStep 2797883 = 4196825) B4196825
theorem B2797943 : Blo 1863633 2797943 := bstep (se 1 (by rfl) ⟨2098457, by rfl⟩ : syracuseStep 2797943 = 4196915) B4196915
theorem B1864071 : Blo 1863633 1864071 := bstep (se 1 (by rfl) ⟨1398053, by rfl⟩ : syracuseStep 1864071 = 2796107) B2796107
theorem B1864079 : Blo 1863633 1864079 := bstep (se 1 (by rfl) ⟨1398059, by rfl⟩ : syracuseStep 1864079 = 2796119) B2796119
theorem B2797967 : Blo 1863633 2797967 := bstep (se 1 (by rfl) ⟨2098475, by rfl⟩ : syracuseStep 2797967 = 4196951) B4196951
theorem B9441683 : Blo 1863633 9441683 := bstep (se 1 (by rfl) ⟨7081262, by rfl⟩ : syracuseStep 9441683 = 14162525) B14162525
theorem B7082387 : Blo 1863633 7082387 := bstep (se 1 (by rfl) ⟨5311790, by rfl⟩ : syracuseStep 7082387 = 10623581) B10623581
theorem B2798009 : Blo 1863633 2798009 := bstep (se 2 (by rfl) ⟨1049253, by rfl⟩ : syracuseStep 2798009 = 2098507) B2098507
theorem B1864123 : Blo 1863633 1864123 := bstep (se 1 (by rfl) ⟨1398092, by rfl⟩ : syracuseStep 1864123 = 2796185) B2796185
theorem B1864199 : Blo 1863633 1864199 := bstep (se 1 (by rfl) ⟨1398149, by rfl⟩ : syracuseStep 1864199 = 2796299) B2796299
theorem B2798087 : Blo 1863633 2798087 := bstep (se 1 (by rfl) ⟨2098565, by rfl⟩ : syracuseStep 2798087 = 4197131) B4197131
theorem B6296075 : Blo 1863633 6296075 := bstep (se 1 (by rfl) ⟨4722056, by rfl⟩ : syracuseStep 6296075 = 9444113) B9444113
theorem B1864207 : Blo 1863633 1864207 := bstep (se 1 (by rfl) ⟨1398155, by rfl⟩ : syracuseStep 1864207 = 2796311) B2796311
theorem B331321873 : Blo 1863633 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B2798123 : Blo 1863633 2798123 := bstep (se 1 (by rfl) ⟨2098592, by rfl⟩ : syracuseStep 2798123 = 4197185) B4197185
theorem B1864251 : Blo 1863633 1864251 := bstep (se 1 (by rfl) ⟨1398188, by rfl⟩ : syracuseStep 1864251 = 2796377) B2796377
theorem B2798153 : Blo 1863633 2798153 := bstep (se 2 (by rfl) ⟨1049307, by rfl⟩ : syracuseStep 2798153 = 2098615) B2098615
theorem B6296183 : Blo 1863633 6296183 := bstep (se 1 (by rfl) ⟨4722137, by rfl⟩ : syracuseStep 6296183 = 9444275) B9444275
theorem B1864327 : Blo 1863633 1864327 := bstep (se 1 (by rfl) ⟨1398245, by rfl⟩ : syracuseStep 1864327 = 2796491) B2796491
theorem B1864335 : Blo 1863633 1864335 := bstep (se 1 (by rfl) ⟨1398251, by rfl⟩ : syracuseStep 1864335 = 2796503) B2796503
theorem B1864379 : Blo 1863633 1864379 := bstep (se 1 (by rfl) ⟨1398284, by rfl⟩ : syracuseStep 1864379 = 2796569) B2796569
theorem B2798267 : Blo 1863633 2798267 := bstep (se 1 (by rfl) ⟨2098700, by rfl⟩ : syracuseStep 2798267 = 4197401) B4197401
theorem B2798327 : Blo 1863633 2798327 := bstep (se 1 (by rfl) ⟨2098745, by rfl⟩ : syracuseStep 2798327 = 4197491) B4197491
theorem B1864455 : Blo 1863633 1864455 := bstep (se 1 (by rfl) ⟨1398341, by rfl⟩ : syracuseStep 1864455 = 2796683) B2796683
theorem B1864463 : Blo 1863633 1864463 := bstep (se 1 (by rfl) ⟨1398347, by rfl⟩ : syracuseStep 1864463 = 2796695) B2796695
theorem B2798351 : Blo 1863633 2798351 := bstep (se 1 (by rfl) ⟨2098763, by rfl⟩ : syracuseStep 2798351 = 4197527) B4197527
theorem B2798393 : Blo 1863633 2798393 := bstep (se 2 (by rfl) ⟨1049397, by rfl⟩ : syracuseStep 2798393 = 2098795) B2098795
theorem B1864507 : Blo 1863633 1864507 := bstep (se 1 (by rfl) ⟨1398380, by rfl⟩ : syracuseStep 1864507 = 2796761) B2796761
theorem B1864583 : Blo 1863633 1864583 := bstep (se 1 (by rfl) ⟨1398437, by rfl⟩ : syracuseStep 1864583 = 2796875) B2796875
theorem B1864591 : Blo 1863633 1864591 := bstep (se 1 (by rfl) ⟨1398443, by rfl⟩ : syracuseStep 1864591 = 2796887) B2796887
theorem B1864635 : Blo 1863633 1864635 := bstep (se 1 (by rfl) ⟨1398476, by rfl⟩ : syracuseStep 1864635 = 2796953) B2796953
theorem B1864711 : Blo 1863633 1864711 := bstep (se 1 (by rfl) ⟨1398533, by rfl⟩ : syracuseStep 1864711 = 2797067) B2797067
theorem B1864719 : Blo 1863633 1864719 := bstep (se 1 (by rfl) ⟨1398539, by rfl⟩ : syracuseStep 1864719 = 2797079) B2797079
theorem B1864763 : Blo 1863633 1864763 := bstep (se 1 (by rfl) ⟨1398572, by rfl⟩ : syracuseStep 1864763 = 2797145) B2797145
theorem B1864839 : Blo 1863633 1864839 := bstep (se 1 (by rfl) ⟨1398629, by rfl⟩ : syracuseStep 1864839 = 2797259) B2797259
theorem B1864847 : Blo 1863633 1864847 := bstep (se 1 (by rfl) ⟨1398635, by rfl⟩ : syracuseStep 1864847 = 2797271) B2797271
theorem B4478105 : Blo 1863633 4478105 := bstep (se 2 (by rfl) ⟨1679289, by rfl⟩ : syracuseStep 4478105 = 3358579) B3358579
theorem B1864891 : Blo 1863633 1864891 := bstep (se 1 (by rfl) ⟨1398668, by rfl⟩ : syracuseStep 1864891 = 2797337) B2797337
theorem B1864967 : Blo 1863633 1864967 := bstep (se 1 (by rfl) ⟨1398725, by rfl⟩ : syracuseStep 1864967 = 2797451) B2797451
theorem B1864975 : Blo 1863633 1864975 := bstep (se 1 (by rfl) ⟨1398731, by rfl⟩ : syracuseStep 1864975 = 2797463) B2797463
theorem B1865019 : Blo 1863633 1865019 := bstep (se 1 (by rfl) ⟨1398764, by rfl⟩ : syracuseStep 1865019 = 2797529) B2797529
theorem B2987383 : Blo 1863633 2987383 := bstep (se 1 (by rfl) ⟨2240537, by rfl⟩ : syracuseStep 2987383 = 4481075) B4481075
theorem B20428163 : Blo 1863633 20428163 := bstep (se 1 (by rfl) ⟨15321122, by rfl⟩ : syracuseStep 20428163 = 30642245) B30642245
theorem B1865095 : Blo 1863633 1865095 := bstep (se 1 (by rfl) ⟨1398821, by rfl⟩ : syracuseStep 1865095 = 2797643) B2797643
theorem B1865103 : Blo 1863633 1865103 := bstep (se 1 (by rfl) ⟨1398827, by rfl⟩ : syracuseStep 1865103 = 2797655) B2797655
theorem B1865147 : Blo 1863633 1865147 := bstep (se 1 (by rfl) ⟨1398860, by rfl⟩ : syracuseStep 1865147 = 2797721) B2797721
theorem B1865223 : Blo 1863633 1865223 := bstep (se 1 (by rfl) ⟨1398917, by rfl⟩ : syracuseStep 1865223 = 2797835) B2797835
theorem B1865231 : Blo 1863633 1865231 := bstep (se 1 (by rfl) ⟨1398923, by rfl⟩ : syracuseStep 1865231 = 2797847) B2797847
theorem B37344797 : Blo 1863633 37344797 := bstep (se 3 (by rfl) ⟨7002149, by rfl⟩ : syracuseStep 37344797 = 14004299) B14004299
theorem B1865275 : Blo 1863633 1865275 := bstep (se 1 (by rfl) ⟨1398956, by rfl⟩ : syracuseStep 1865275 = 2797913) B2797913
theorem B1865351 : Blo 1863633 1865351 := bstep (se 1 (by rfl) ⟨1399013, by rfl⟩ : syracuseStep 1865351 = 2798027) B2798027
theorem B1865359 : Blo 1863633 1865359 := bstep (se 1 (by rfl) ⟨1399019, by rfl⟩ : syracuseStep 1865359 = 2798039) B2798039
theorem B1865403 : Blo 1863633 1865403 := bstep (se 1 (by rfl) ⟨1399052, by rfl⟩ : syracuseStep 1865403 = 2798105) B2798105
theorem B10082029 : Blo 1863633 10082029 := bstep (se 3 (by rfl) ⟨1890380, by rfl⟩ : syracuseStep 10082029 = 3780761) B3780761
theorem B1865479 : Blo 1863633 1865479 := bstep (se 1 (by rfl) ⟨1399109, by rfl⟩ : syracuseStep 1865479 = 2798219) B2798219
theorem B1865487 : Blo 1863633 1865487 := bstep (se 1 (by rfl) ⟨1399115, by rfl⟩ : syracuseStep 1865487 = 2798231) B2798231
theorem B21231395 : Blo 1863633 21231395 := bstep (se 1 (by rfl) ⟨15923546, by rfl⟩ : syracuseStep 21231395 = 31847093) B31847093
theorem B15324977 : Blo 1863633 15324977 := bstep (se 2 (by rfl) ⟨5746866, by rfl⟩ : syracuseStep 15324977 = 11493733) B11493733
theorem B1865531 : Blo 1863633 1865531 := bstep (se 1 (by rfl) ⟨1399148, by rfl⟩ : syracuseStep 1865531 = 2798297) B2798297
theorem B1865607 : Blo 1863633 1865607 := bstep (se 1 (by rfl) ⟨1399205, by rfl⟩ : syracuseStep 1865607 = 2798411) B2798411
theorem B1865615 : Blo 1863633 1865615 := bstep (se 1 (by rfl) ⟨1399211, by rfl⟩ : syracuseStep 1865615 = 2798423) B2798423
theorem B4782091 : Blo 1863633 4782091 := bstep (se 1 (by rfl) ⟨3586568, by rfl⟩ : syracuseStep 4782091 = 7173137) B7173137
theorem B2521145 : Blo 1863633 2521145 := bstep (se 2 (by rfl) ⟨945429, by rfl⟩ : syracuseStep 2521145 = 1890859) B1890859
theorem B9435203 : Blo 1863633 9435203 := bstep (se 1 (by rfl) ⟨7076402, by rfl⟩ : syracuseStep 9435203 = 14152805) B14152805
theorem B10623149 : Blo 1863633 10623149 := bstep (se 3 (by rfl) ⟨1991840, by rfl⟩ : syracuseStep 10623149 = 3983681) B3983681
theorem B13441261 : Blo 1863633 13441261 := bstep (se 3 (by rfl) ⟨2520236, by rfl⟩ : syracuseStep 13441261 = 5040473) B5040473
theorem B9435527 : Blo 1863633 9435527 := bstep (se 1 (by rfl) ⟨7076645, by rfl⟩ : syracuseStep 9435527 = 14153291) B14153291
theorem B6289811 : Blo 1863633 6289811 := bstep (se 1 (by rfl) ⟨4717358, by rfl⟩ : syracuseStep 6289811 = 9434717) B9434717
theorem B7076281 : Blo 1863633 7076281 := bstep (se 2 (by rfl) ⟨2653605, by rfl⟩ : syracuseStep 7076281 = 5307211) B5307211
theorem B7174585 : Blo 1863633 7174585 := bstep (se 2 (by rfl) ⟨2690469, by rfl⟩ : syracuseStep 7174585 = 5380939) B5380939
theorem B15923789 : Blo 1863633 15923789 := bstep (se 3 (by rfl) ⟨2985710, by rfl⟩ : syracuseStep 15923789 = 5971421) B5971421
theorem B2874043 : Blo 1863633 2874043 := bstep (se 1 (by rfl) ⟨2155532, by rfl⟩ : syracuseStep 2874043 = 4311065) B4311065
theorem B4717399 : Blo 1863633 4717399 := bstep (se 1 (by rfl) ⟨3538049, by rfl⟩ : syracuseStep 4717399 = 7076099) B7076099
theorem B4193225 : Blo 1863633 4193225 := bstep (se 2 (by rfl) ⟨1572459, by rfl⟩ : syracuseStep 4193225 = 3144919) B3144919
theorem B26876933 : Blo 1863633 26876933 := bstep (se 4 (by rfl) ⟨2519712, by rfl⟩ : syracuseStep 26876933 = 5039425) B5039425
theorem B4250657 : Blo 1863633 4250657 := bstep (se 2 (by rfl) ⟨1593996, by rfl⟩ : syracuseStep 4250657 = 3187993) B3187993
theorem B4717703 : Blo 1863633 4717703 := bstep (se 1 (by rfl) ⟨3538277, by rfl⟩ : syracuseStep 4717703 = 7076555) B7076555
theorem B5381273 : Blo 1863633 5381273 := bstep (se 2 (by rfl) ⟨2017977, by rfl⟩ : syracuseStep 5381273 = 4035955) B4035955
theorem B4717835 : Blo 1863633 4717835 := bstep (se 1 (by rfl) ⟨3538376, by rfl⟩ : syracuseStep 4717835 = 7076753) B7076753
theorem B4480267 : Blo 1863633 4480267 := bstep (se 1 (by rfl) ⟨3360200, by rfl⟩ : syracuseStep 4480267 = 6720401) B6720401
theorem B9444761 : Blo 1863633 9444761 := bstep (se 2 (by rfl) ⟨3541785, by rfl⟩ : syracuseStep 9444761 = 7083571) B7083571
theorem B2358715 : Blo 1863633 2358715 := bstep (se 1 (by rfl) ⟨1769036, by rfl⟩ : syracuseStep 2358715 = 3538073) B3538073
theorem B3538475 : Blo 1863633 3538475 := bstep (se 1 (by rfl) ⟨2653856, by rfl⟩ : syracuseStep 3538475 = 5307713) B5307713
theorem B3145351 : Blo 1863633 3145351 := bstep (se 1 (by rfl) ⟨2359013, by rfl⟩ : syracuseStep 3145351 = 4718027) B4718027
theorem B4193927 : Blo 1863633 4193927 := bstep (se 1 (by rfl) ⟨3145445, by rfl⟩ : syracuseStep 4193927 = 6290891) B6290891
theorem B21241601 : Blo 1863633 21241601 := bstep (se 2 (by rfl) ⟨7965600, by rfl⟩ : syracuseStep 21241601 = 15931201) B15931201
theorem B15933185 : Blo 1863633 15933185 := bstep (se 2 (by rfl) ⟨5974944, by rfl⟩ : syracuseStep 15933185 = 11949889) B11949889
theorem B3538703 : Blo 1863633 3538703 := bstep (se 1 (by rfl) ⟨2654027, by rfl⟩ : syracuseStep 3538703 = 5308055) B5308055
theorem B4718351 : Blo 1863633 4718351 := bstep (se 1 (by rfl) ⟨3538763, by rfl⟩ : syracuseStep 4718351 = 7077527) B7077527
theorem B6291215 : Blo 1863633 6291215 := bstep (se 1 (by rfl) ⟨4718411, by rfl⟩ : syracuseStep 6291215 = 9436823) B9436823
theorem B11951887 : Blo 1863633 11951887 := bstep (se 1 (by rfl) ⟨8963915, by rfl⟩ : syracuseStep 11951887 = 17927831) B17927831
theorem B10616609 : Blo 1863633 10616609 := bstep (se 2 (by rfl) ⟨3981228, by rfl⟩ : syracuseStep 10616609 = 7962457) B7962457
theorem B4194107 : Blo 1863633 4194107 := bstep (se 1 (by rfl) ⟨3145580, by rfl⟩ : syracuseStep 4194107 = 6291161) B6291161
theorem B4480883 : Blo 1863633 4480883 := bstep (se 1 (by rfl) ⟨3360662, by rfl⟩ : syracuseStep 4480883 = 6721325) B6721325
theorem B2097031 : Blo 1863633 2097031 := bstep (se 1 (by rfl) ⟨1572773, by rfl⟩ : syracuseStep 2097031 = 3145547) B3145547
theorem B4718483 : Blo 1863633 4718483 := bstep (se 1 (by rfl) ⟨3538862, by rfl⟩ : syracuseStep 4718483 = 7077725) B7077725
theorem B17006489 : Blo 1863633 17006489 := bstep (se 2 (by rfl) ⟨6377433, by rfl⟩ : syracuseStep 17006489 = 12754867) B12754867
theorem B4194233 : Blo 1863633 4194233 := bstep (se 2 (by rfl) ⟨1572837, by rfl⟩ : syracuseStep 4194233 = 3145675) B3145675
theorem B13443079 : Blo 1863633 13443079 := bstep (se 1 (by rfl) ⟨10082309, by rfl⟩ : syracuseStep 13443079 = 20164619) B20164619
theorem B14163983 : Blo 1863633 14163983 := bstep (se 1 (by rfl) ⟨10622987, by rfl⟩ : syracuseStep 14163983 = 21245975) B21245975
theorem B10625039 : Blo 1863633 10625039 := bstep (se 1 (by rfl) ⟨7968779, by rfl⟩ : syracuseStep 10625039 = 15937559) B15937559
theorem B4194323 : Blo 1863633 4194323 := bstep (se 1 (by rfl) ⟨3145742, by rfl⟩ : syracuseStep 4194323 = 6291485) B6291485
theorem B3358759 : Blo 1863633 3358759 := bstep (se 1 (by rfl) ⟨2519069, by rfl⟩ : syracuseStep 3358759 = 5038139) B5038139
theorem B3358817 : Blo 1863633 3358817 := bstep (se 2 (by rfl) ⟨1259556, by rfl⟩ : syracuseStep 3358817 = 2519113) B2519113
theorem B3539143 : Blo 1863633 3539143 := bstep (se 1 (by rfl) ⟨2654357, by rfl⟩ : syracuseStep 3539143 = 5308715) B5308715
theorem B4194665 : Blo 1863633 4194665 := bstep (se 2 (by rfl) ⟨1572999, by rfl⟩ : syracuseStep 4194665 = 3145999) B3145999
theorem B3981673 : Blo 1863633 3981673 := bstep (se 2 (by rfl) ⟨1493127, by rfl⟩ : syracuseStep 3981673 = 2986255) B2986255
theorem B3146249 : Blo 1863633 3146249 := bstep (se 2 (by rfl) ⟨1179843, by rfl⟩ : syracuseStep 3146249 = 2359687) B2359687
theorem B2097787 : Blo 1863633 2097787 := bstep (se 1 (by rfl) ⟨1573340, by rfl⟩ : syracuseStep 2097787 = 3146681) B3146681
theorem B3146411 : Blo 1863633 3146411 := bstep (se 1 (by rfl) ⟨2359808, by rfl⟩ : syracuseStep 3146411 = 4719617) B4719617
theorem B441762497 : Blo 1863633 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B4252409 : Blo 1863633 4252409 := bstep (se 2 (by rfl) ⟨1594653, by rfl⟩ : syracuseStep 4252409 = 3189307) B3189307
theorem B4719455 : Blo 1863633 4719455 := bstep (se 1 (by rfl) ⟨3539591, by rfl⟩ : syracuseStep 4719455 = 7079183) B7079183
theorem B4195259 : Blo 1863633 4195259 := bstep (se 1 (by rfl) ⟨3146444, by rfl⟩ : syracuseStep 4195259 = 6292889) B6292889
theorem B31851467 : Blo 1863633 31851467 := bstep (se 1 (by rfl) ⟨23888600, by rfl⟩ : syracuseStep 31851467 = 47777201) B47777201
theorem B24896531 : Blo 1863633 24896531 := bstep (se 1 (by rfl) ⟨18672398, by rfl⟩ : syracuseStep 24896531 = 37344797) B37344797
theorem B4195385 : Blo 1863633 4195385 := bstep (se 2 (by rfl) ⟨1573269, by rfl⟩ : syracuseStep 4195385 = 3146539) B3146539
theorem B3146809 : Blo 1863633 3146809 := bstep (se 2 (by rfl) ⟨1180053, by rfl⟩ : syracuseStep 3146809 = 2360107) B2360107
theorem B2098255 : Blo 1863633 2098255 := bstep (se 1 (by rfl) ⟨1573691, by rfl⟩ : syracuseStep 2098255 = 3147383) B3147383
theorem B20169847 : Blo 1863633 20169847 := bstep (se 1 (by rfl) ⟨15127385, by rfl⟩ : syracuseStep 20169847 = 30254771) B30254771
theorem B3146951 : Blo 1863633 3146951 := bstep (se 1 (by rfl) ⟨2360213, by rfl⟩ : syracuseStep 3146951 = 4720427) B4720427
theorem B10216651 : Blo 1863633 10216651 := bstep (se 1 (by rfl) ⟨7662488, by rfl⟩ : syracuseStep 10216651 = 15324977) B15324977
theorem B6292727 : Blo 1863633 6292727 := bstep (se 1 (by rfl) ⟨4719545, by rfl⟩ : syracuseStep 6292727 = 9439091) B9439091
theorem B3147113 : Blo 1863633 3147113 := bstep (se 2 (by rfl) ⟨1180167, by rfl⟩ : syracuseStep 3147113 = 2360335) B2360335
theorem B4195727 : Blo 1863633 4195727 := bstep (se 1 (by rfl) ⟨3146795, by rfl⟩ : syracuseStep 4195727 = 6293591) B6293591
theorem B10077659 : Blo 1863633 10077659 := bstep (se 1 (by rfl) ⟨7558244, by rfl⟩ : syracuseStep 10077659 = 15116489) B15116489
theorem B2098651 : Blo 1863633 2098651 := bstep (se 1 (by rfl) ⟨1573988, by rfl⟩ : syracuseStep 2098651 = 3147977) B3147977
theorem B4720153 : Blo 1863633 4720153 := bstep (se 2 (by rfl) ⟨1770057, by rfl⟩ : syracuseStep 4720153 = 3540115) B3540115
theorem B6293051 : Blo 1863633 6293051 := bstep (se 1 (by rfl) ⟨4719788, by rfl⟩ : syracuseStep 6293051 = 9439577) B9439577
theorem B28698209 : Blo 1863633 28698209 := bstep (se 2 (by rfl) ⟨10761828, by rfl⟩ : syracuseStep 28698209 = 21523657) B21523657
theorem B61277795 : Blo 1863633 61277795 := bstep (se 1 (by rfl) ⟨45958346, by rfl⟩ : syracuseStep 61277795 = 91916693) B91916693
theorem B5973689 : Blo 1863633 5973689 := bstep (se 2 (by rfl) ⟨2240133, by rfl⟩ : syracuseStep 5973689 = 4480267) B4480267
theorem B4196051 : Blo 1863633 4196051 := bstep (se 1 (by rfl) ⟨3147038, by rfl⟩ : syracuseStep 4196051 = 6294077) B6294077
theorem B3147511 : Blo 1863633 3147511 := bstep (se 1 (by rfl) ⟨2360633, by rfl⟩ : syracuseStep 3147511 = 4721267) B4721267
theorem B86107897 : Blo 1863633 86107897 := bstep (se 2 (by rfl) ⟨32290461, by rfl⟩ : syracuseStep 86107897 = 64580923) B64580923
theorem B11339513 : Blo 1863633 11339513 := bstep (se 2 (by rfl) ⟨4252317, by rfl⟩ : syracuseStep 11339513 = 8504635) B8504635
theorem B6293321 : Blo 1863633 6293321 := bstep (se 2 (by rfl) ⟨2359995, by rfl⟩ : syracuseStep 6293321 = 4719991) B4719991
theorem B4720457 : Blo 1863633 4720457 := bstep (se 2 (by rfl) ⟨1770171, by rfl⟩ : syracuseStep 4720457 = 3540343) B3540343
theorem B3983177 : Blo 1863633 3983177 := bstep (se 2 (by rfl) ⟨1493691, by rfl⟩ : syracuseStep 3983177 = 2987383) B2987383
theorem B3147707 : Blo 1863633 3147707 := bstep (se 1 (by rfl) ⟨2360780, by rfl⟩ : syracuseStep 3147707 = 4721561) B4721561
theorem B2795483 : Blo 1863633 2795483 := bstep (se 1 (by rfl) ⟨2096612, by rfl⟩ : syracuseStep 2795483 = 4193225) B4193225
theorem B17917955 : Blo 1863633 17917955 := bstep (se 1 (by rfl) ⟨13438466, by rfl⟩ : syracuseStep 17917955 = 26876933) B26876933
theorem B6719507 : Blo 1863633 6719507 := bstep (se 1 (by rfl) ⟨5039630, by rfl⟩ : syracuseStep 6719507 = 10079261) B10079261
theorem B3147815 : Blo 1863633 3147815 := bstep (se 1 (by rfl) ⟨2360861, by rfl⟩ : syracuseStep 3147815 = 4721723) B4721723
theorem B21235769 : Blo 1863633 21235769 := bstep (se 2 (by rfl) ⟨7963413, by rfl⟩ : syracuseStep 21235769 = 15926827) B15926827
theorem B3148105 : Blo 1863633 3148105 := bstep (se 2 (by rfl) ⟨1180539, by rfl⟩ : syracuseStep 3148105 = 2361079) B2361079
theorem B9079127 : Blo 1863633 9079127 := bstep (se 1 (by rfl) ⟨6809345, by rfl⟩ : syracuseStep 9079127 = 13618691) B13618691
theorem B15935849 : Blo 1863633 15935849 := bstep (se 2 (by rfl) ⟨5975943, by rfl⟩ : syracuseStep 15935849 = 11951887) B11951887
theorem B3148139 : Blo 1863633 3148139 := bstep (se 1 (by rfl) ⟨2361104, by rfl⟩ : syracuseStep 3148139 = 4722209) B4722209
theorem B3541391 : Blo 1863633 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B2795951 : Blo 1863633 2795951 := bstep (se 1 (by rfl) ⟨2096963, by rfl⟩ : syracuseStep 2795951 = 4193927) B4193927
theorem B2796041 : Blo 1863633 2796041 := bstep (se 2 (by rfl) ⟨1048515, by rfl⟩ : syracuseStep 2796041 = 2097031) B2097031
theorem B7080473 : Blo 1863633 7080473 := bstep (se 2 (by rfl) ⟨2655177, by rfl⟩ : syracuseStep 7080473 = 5310355) B5310355
theorem B2796071 : Blo 1863633 2796071 := bstep (se 1 (by rfl) ⟨2097053, by rfl⟩ : syracuseStep 2796071 = 4194107) B4194107
theorem B2796155 : Blo 1863633 2796155 := bstep (se 1 (by rfl) ⟨2097116, by rfl⟩ : syracuseStep 2796155 = 4194233) B4194233
theorem B4196987 : Blo 1863633 4196987 := bstep (se 1 (by rfl) ⟨3147740, by rfl⟩ : syracuseStep 4196987 = 6295481) B6295481
theorem B6376121 : Blo 1863633 6376121 := bstep (se 2 (by rfl) ⟨2391045, by rfl⟩ : syracuseStep 6376121 = 4782091) B4782091
theorem B2796281 : Blo 1863633 2796281 := bstep (se 2 (by rfl) ⟨1048605, by rfl⟩ : syracuseStep 2796281 = 2097211) B2097211
theorem B4197113 : Blo 1863633 4197113 := bstep (se 2 (by rfl) ⟨1573917, by rfl⟩ : syracuseStep 4197113 = 3147835) B3147835
theorem B2796383 : Blo 1863633 2796383 := bstep (se 1 (by rfl) ⟨2097287, by rfl⟩ : syracuseStep 2796383 = 4194575) B4194575
theorem B2796395 : Blo 1863633 2796395 := bstep (se 1 (by rfl) ⟨2097296, by rfl⟩ : syracuseStep 2796395 = 4194593) B4194593
theorem B5041079 : Blo 1863633 5041079 := bstep (se 1 (by rfl) ⟨3780809, by rfl⟩ : syracuseStep 5041079 = 7561619) B7561619
theorem B6294455 : Blo 1863633 6294455 := bstep (se 1 (by rfl) ⟨4720841, by rfl⟩ : syracuseStep 6294455 = 9441683) B9441683
theorem B4721591 : Blo 1863633 4721591 := bstep (se 1 (by rfl) ⟨3541193, by rfl⟩ : syracuseStep 4721591 = 7082387) B7082387
theorem B4197383 : Blo 1863633 4197383 := bstep (se 1 (by rfl) ⟨3148037, by rfl⟩ : syracuseStep 4197383 = 6296075) B6296075
theorem B3779641 : Blo 1863633 3779641 := bstep (se 2 (by rfl) ⟨1417365, by rfl⟩ : syracuseStep 3779641 = 2834731) B2834731
theorem B2796623 : Blo 1863633 2796623 := bstep (se 1 (by rfl) ⟨2097467, by rfl⟩ : syracuseStep 2796623 = 4194935) B4194935
theorem B22686799 : Blo 1863633 22686799 := bstep (se 1 (by rfl) ⟨17015099, by rfl⟩ : syracuseStep 22686799 = 34030199) B34030199
theorem B4197455 : Blo 1863633 4197455 := bstep (se 1 (by rfl) ⟨3148091, by rfl⟩ : syracuseStep 4197455 = 6296183) B6296183
theorem B2796743 : Blo 1863633 2796743 := bstep (se 1 (by rfl) ⟨2097557, by rfl⟩ : syracuseStep 2796743 = 4195115) B4195115
theorem B2796905 : Blo 1863633 2796905 := bstep (se 2 (by rfl) ⟨1048839, by rfl⟩ : syracuseStep 2796905 = 2097679) B2097679
theorem B15936911 : Blo 1863633 15936911 := bstep (se 1 (by rfl) ⟨11952683, by rfl⟩ : syracuseStep 15936911 = 23905367) B23905367
theorem B2796983 : Blo 1863633 2796983 := bstep (se 1 (by rfl) ⟨2097737, by rfl⟩ : syracuseStep 2796983 = 4195475) B4195475
theorem B2797019 : Blo 1863633 2797019 := bstep (se 1 (by rfl) ⟨2097764, by rfl⟩ : syracuseStep 2797019 = 4195529) B4195529
theorem B6295049 : Blo 1863633 6295049 := bstep (se 2 (by rfl) ⟨2360643, by rfl⟩ : syracuseStep 6295049 = 4721287) B4721287
theorem B13618775 : Blo 1863633 13618775 := bstep (se 1 (by rfl) ⟨10214081, by rfl⟩ : syracuseStep 13618775 = 20428163) B20428163
theorem B11054807 : Blo 1863633 11054807 := bstep (se 1 (by rfl) ⟨8291105, by rfl⟩ : syracuseStep 11054807 = 16582211) B16582211
theorem B14159609 : Blo 1863633 14159609 := bstep (se 2 (by rfl) ⟨5309853, by rfl⟩ : syracuseStep 14159609 = 10619707) B10619707
theorem B10620665 : Blo 1863633 10620665 := bstep (se 2 (by rfl) ⟨3982749, by rfl⟩ : syracuseStep 10620665 = 7965499) B7965499
theorem B7966457 : Blo 1863633 7966457 := bstep (se 2 (by rfl) ⟨2987421, by rfl⟩ : syracuseStep 7966457 = 5974843) B5974843
theorem B2797487 : Blo 1863633 2797487 := bstep (se 1 (by rfl) ⟨2098115, by rfl⟩ : syracuseStep 2797487 = 4196231) B4196231
theorem B1863643 : Blo 1863633 1863643 := bstep (se 1 (by rfl) ⟨1397732, by rfl⟩ : syracuseStep 1863643 = 2795465) B2795465
theorem B2797577 : Blo 1863633 2797577 := bstep (se 2 (by rfl) ⟨1049091, by rfl⟩ : syracuseStep 2797577 = 2098183) B2098183
theorem B1863719 : Blo 1863633 1863719 := bstep (se 1 (by rfl) ⟨1397789, by rfl⟩ : syracuseStep 1863719 = 2795579) B2795579
theorem B2797607 : Blo 1863633 2797607 := bstep (se 1 (by rfl) ⟨2098205, by rfl⟩ : syracuseStep 2797607 = 4196411) B4196411
theorem B1863759 : Blo 1863633 1863759 := bstep (se 1 (by rfl) ⟨1397819, by rfl⟩ : syracuseStep 1863759 = 2795639) B2795639
theorem B1863775 : Blo 1863633 1863775 := bstep (se 1 (by rfl) ⟨1397831, by rfl⟩ : syracuseStep 1863775 = 2795663) B2795663
theorem B7082099 : Blo 1863633 7082099 := bstep (se 1 (by rfl) ⟨5311574, by rfl⟩ : syracuseStep 7082099 = 10623149) B10623149
theorem B1863803 : Blo 1863633 1863803 := bstep (se 1 (by rfl) ⟨1397852, by rfl⟩ : syracuseStep 1863803 = 2795705) B2795705
theorem B2797691 : Blo 1863633 2797691 := bstep (se 1 (by rfl) ⟨2098268, by rfl⟩ : syracuseStep 2797691 = 4196537) B4196537
theorem B1863855 : Blo 1863633 1863855 := bstep (se 1 (by rfl) ⟨1397891, by rfl⟩ : syracuseStep 1863855 = 2795783) B2795783
theorem B1863879 : Blo 1863633 1863879 := bstep (se 1 (by rfl) ⟨1397909, by rfl⟩ : syracuseStep 1863879 = 2795819) B2795819
theorem B1863899 : Blo 1863633 1863899 := bstep (se 1 (by rfl) ⟨1397924, by rfl⟩ : syracuseStep 1863899 = 2795849) B2795849
theorem B2797817 : Blo 1863633 2797817 := bstep (se 2 (by rfl) ⟨1049181, by rfl⟩ : syracuseStep 2797817 = 2098363) B2098363
theorem B12103937 : Blo 1863633 12103937 := bstep (se 2 (by rfl) ⟨4538976, by rfl⟩ : syracuseStep 12103937 = 9077953) B9077953
theorem B1863975 : Blo 1863633 1863975 := bstep (se 1 (by rfl) ⟨1397981, by rfl⟩ : syracuseStep 1863975 = 2795963) B2795963
theorem B23884091 : Blo 1863633 23884091 := bstep (se 1 (by rfl) ⟨17913068, by rfl⟩ : syracuseStep 23884091 = 35826137) B35826137
theorem B1864015 : Blo 1863633 1864015 := bstep (se 1 (by rfl) ⟨1398011, by rfl⟩ : syracuseStep 1864015 = 2796023) B2796023
theorem B1864031 : Blo 1863633 1864031 := bstep (se 1 (by rfl) ⟨1398023, by rfl⟩ : syracuseStep 1864031 = 2796047) B2796047
theorem B2797919 : Blo 1863633 2797919 := bstep (se 1 (by rfl) ⟨2098439, by rfl⟩ : syracuseStep 2797919 = 4196879) B4196879
theorem B2986345 : Blo 1863633 2986345 := bstep (se 2 (by rfl) ⟨1119879, by rfl⟩ : syracuseStep 2986345 = 2239759) B2239759
theorem B6295913 : Blo 1863633 6295913 := bstep (se 2 (by rfl) ⟨2360967, by rfl⟩ : syracuseStep 6295913 = 4721935) B4721935
theorem B2797931 : Blo 1863633 2797931 := bstep (se 1 (by rfl) ⟨2098448, by rfl⟩ : syracuseStep 2797931 = 4196897) B4196897
theorem B1864059 : Blo 1863633 1864059 := bstep (se 1 (by rfl) ⟨1398044, by rfl⟩ : syracuseStep 1864059 = 2796089) B2796089
theorem B7967105 : Blo 1863633 7967105 := bstep (se 2 (by rfl) ⟨2987664, by rfl⟩ : syracuseStep 7967105 = 5975329) B5975329
theorem B1864111 : Blo 1863633 1864111 := bstep (se 1 (by rfl) ⟨1398083, by rfl⟩ : syracuseStep 1864111 = 2796167) B2796167
theorem B1864135 : Blo 1863633 1864135 := bstep (se 1 (by rfl) ⟨1398101, by rfl⟩ : syracuseStep 1864135 = 2796203) B2796203
theorem B1864155 : Blo 1863633 1864155 := bstep (se 1 (by rfl) ⟨1398116, by rfl⟩ : syracuseStep 1864155 = 2796233) B2796233
theorem B3453403 : Blo 1863633 3453403 := bstep (se 1 (by rfl) ⟨2590052, by rfl⟩ : syracuseStep 3453403 = 5180105) B5180105
theorem B1864231 : Blo 1863633 1864231 := bstep (se 1 (by rfl) ⟨1398173, by rfl⟩ : syracuseStep 1864231 = 2796347) B2796347
theorem B1864271 : Blo 1863633 1864271 := bstep (se 1 (by rfl) ⟨1398203, by rfl⟩ : syracuseStep 1864271 = 2796407) B2796407
theorem B2798159 : Blo 1863633 2798159 := bstep (se 1 (by rfl) ⟨2098619, by rfl⟩ : syracuseStep 2798159 = 4197239) B4197239
theorem B1864287 : Blo 1863633 1864287 := bstep (se 1 (by rfl) ⟨1398215, by rfl⟩ : syracuseStep 1864287 = 2796431) B2796431
theorem B1864315 : Blo 1863633 1864315 := bstep (se 1 (by rfl) ⟨1398236, by rfl⟩ : syracuseStep 1864315 = 2796473) B2796473
theorem B1864367 : Blo 1863633 1864367 := bstep (se 1 (by rfl) ⟨1398275, by rfl⟩ : syracuseStep 1864367 = 2796551) B2796551
theorem B1864391 : Blo 1863633 1864391 := bstep (se 1 (by rfl) ⟨1398293, by rfl⟩ : syracuseStep 1864391 = 2796587) B2796587
theorem B2798279 : Blo 1863633 2798279 := bstep (se 1 (by rfl) ⟨2098709, by rfl⟩ : syracuseStep 2798279 = 4197419) B4197419
theorem B1864411 : Blo 1863633 1864411 := bstep (se 1 (by rfl) ⟨1398308, by rfl⟩ : syracuseStep 1864411 = 2796617) B2796617
theorem B1864487 : Blo 1863633 1864487 := bstep (se 1 (by rfl) ⟨1398365, by rfl⟩ : syracuseStep 1864487 = 2796731) B2796731
theorem B1864527 : Blo 1863633 1864527 := bstep (se 1 (by rfl) ⟨1398395, by rfl⟩ : syracuseStep 1864527 = 2796791) B2796791
theorem B1864543 : Blo 1863633 1864543 := bstep (se 1 (by rfl) ⟨1398407, by rfl⟩ : syracuseStep 1864543 = 2796815) B2796815
theorem B2798441 : Blo 1863633 2798441 := bstep (se 2 (by rfl) ⟨1049415, by rfl⟩ : syracuseStep 2798441 = 2098831) B2098831
theorem B1864571 : Blo 1863633 1864571 := bstep (se 1 (by rfl) ⟨1398428, by rfl⟩ : syracuseStep 1864571 = 2796857) B2796857
theorem B1864623 : Blo 1863633 1864623 := bstep (se 1 (by rfl) ⟨1398467, by rfl⟩ : syracuseStep 1864623 = 2796935) B2796935
theorem B6296507 : Blo 1863633 6296507 := bstep (se 1 (by rfl) ⟨4722380, by rfl⟩ : syracuseStep 6296507 = 9444761) B9444761
theorem B1864647 : Blo 1863633 1864647 := bstep (se 1 (by rfl) ⟨1398485, by rfl⟩ : syracuseStep 1864647 = 2796971) B2796971
theorem B1864667 : Blo 1863633 1864667 := bstep (se 1 (by rfl) ⟨1398500, by rfl⟩ : syracuseStep 1864667 = 2797001) B2797001
theorem B8958995 : Blo 1863633 8958995 := bstep (se 1 (by rfl) ⟨6719246, by rfl⟩ : syracuseStep 8958995 = 13438493) B13438493
theorem B1864743 : Blo 1863633 1864743 := bstep (se 1 (by rfl) ⟨1398557, by rfl⟩ : syracuseStep 1864743 = 2797115) B2797115
theorem B1864783 : Blo 1863633 1864783 := bstep (se 1 (by rfl) ⟨1398587, by rfl⟩ : syracuseStep 1864783 = 2797175) B2797175
theorem B1864799 : Blo 1863633 1864799 := bstep (se 1 (by rfl) ⟨1398599, by rfl⟩ : syracuseStep 1864799 = 2797199) B2797199
theorem B1864827 : Blo 1863633 1864827 := bstep (se 1 (by rfl) ⟨1398620, by rfl⟩ : syracuseStep 1864827 = 2797241) B2797241
theorem B14161067 : Blo 1863633 14161067 := bstep (se 1 (by rfl) ⟨10620800, by rfl⟩ : syracuseStep 14161067 = 21241601) B21241601
theorem B10622123 : Blo 1863633 10622123 := bstep (se 1 (by rfl) ⟨7966592, by rfl⟩ : syracuseStep 10622123 = 15933185) B15933185
theorem B1864879 : Blo 1863633 1864879 := bstep (se 1 (by rfl) ⟨1398659, by rfl⟩ : syracuseStep 1864879 = 2797319) B2797319
theorem B1864903 : Blo 1863633 1864903 := bstep (se 1 (by rfl) ⟨1398677, by rfl⟩ : syracuseStep 1864903 = 2797355) B2797355
theorem B1864923 : Blo 1863633 1864923 := bstep (se 1 (by rfl) ⟨1398692, by rfl⟩ : syracuseStep 1864923 = 2797385) B2797385
theorem B2987255 : Blo 1863633 2987255 := bstep (se 1 (by rfl) ⟨2240441, by rfl⟩ : syracuseStep 2987255 = 4480883) B4480883
theorem B1864999 : Blo 1863633 1864999 := bstep (se 1 (by rfl) ⟨1398749, by rfl⟩ : syracuseStep 1864999 = 2797499) B2797499
theorem B1865039 : Blo 1863633 1865039 := bstep (se 1 (by rfl) ⟨1398779, by rfl⟩ : syracuseStep 1865039 = 2797559) B2797559
theorem B1865055 : Blo 1863633 1865055 := bstep (se 1 (by rfl) ⟨1398791, by rfl⟩ : syracuseStep 1865055 = 2797583) B2797583
theorem B1889659 : Blo 1863633 1889659 := bstep (se 1 (by rfl) ⟨1417244, by rfl⟩ : syracuseStep 1889659 = 2834489) B2834489
theorem B1865083 : Blo 1863633 1865083 := bstep (se 1 (by rfl) ⟨1398812, by rfl⟩ : syracuseStep 1865083 = 2797625) B2797625
theorem B7083389 : Blo 1863633 7083389 := bstep (se 3 (by rfl) ⟨1328135, by rfl⟩ : syracuseStep 7083389 = 2656271) B2656271
theorem B11335085 : Blo 1863633 11335085 := bstep (se 3 (by rfl) ⟨2125328, by rfl⟩ : syracuseStep 11335085 = 4250657) B4250657
theorem B1865135 : Blo 1863633 1865135 := bstep (se 1 (by rfl) ⟨1398851, by rfl⟩ : syracuseStep 1865135 = 2797703) B2797703
theorem B1865159 : Blo 1863633 1865159 := bstep (se 1 (by rfl) ⟨1398869, by rfl⟩ : syracuseStep 1865159 = 2797739) B2797739
theorem B21247433 : Blo 1863633 21247433 := bstep (se 2 (by rfl) ⟨7967787, by rfl⟩ : syracuseStep 21247433 = 15935575) B15935575
theorem B1865179 : Blo 1863633 1865179 := bstep (se 1 (by rfl) ⟨1398884, by rfl⟩ : syracuseStep 1865179 = 2797769) B2797769
theorem B6723053 : Blo 1863633 6723053 := bstep (se 3 (by rfl) ⟨1260572, by rfl⟩ : syracuseStep 6723053 = 2521145) B2521145
theorem B30242315 : Blo 1863633 30242315 := bstep (se 1 (by rfl) ⟨22681736, by rfl⟩ : syracuseStep 30242315 = 45363473) B45363473
theorem B1865255 : Blo 1863633 1865255 := bstep (se 1 (by rfl) ⟨1398941, by rfl⟩ : syracuseStep 1865255 = 2797883) B2797883
theorem B1865295 : Blo 1863633 1865295 := bstep (se 1 (by rfl) ⟨1398971, by rfl⟩ : syracuseStep 1865295 = 2797943) B2797943
theorem B1865311 : Blo 1863633 1865311 := bstep (se 1 (by rfl) ⟨1398983, by rfl⟩ : syracuseStep 1865311 = 2797967) B2797967
theorem B1865339 : Blo 1863633 1865339 := bstep (se 1 (by rfl) ⟨1399004, by rfl⟩ : syracuseStep 1865339 = 2798009) B2798009
theorem B17921681 : Blo 1863633 17921681 := bstep (se 2 (by rfl) ⟨6720630, by rfl⟩ : syracuseStep 17921681 = 13441261) B13441261
theorem B14161553 : Blo 1863633 14161553 := bstep (se 2 (by rfl) ⟨5310582, by rfl⟩ : syracuseStep 14161553 = 10621165) B10621165
theorem B1865391 : Blo 1863633 1865391 := bstep (se 1 (by rfl) ⟨1399043, by rfl⟩ : syracuseStep 1865391 = 2798087) B2798087
theorem B1865415 : Blo 1863633 1865415 := bstep (se 1 (by rfl) ⟨1399061, by rfl⟩ : syracuseStep 1865415 = 2798123) B2798123
theorem B1865435 : Blo 1863633 1865435 := bstep (se 1 (by rfl) ⟨1399076, by rfl⟩ : syracuseStep 1865435 = 2798153) B2798153
theorem B11941613 : Blo 1863633 11941613 := bstep (se 3 (by rfl) ⟨2239052, by rfl⟩ : syracuseStep 11941613 = 4478105) B4478105
theorem B14350061 : Blo 1863633 14350061 := bstep (se 3 (by rfl) ⟨2690636, by rfl⟩ : syracuseStep 14350061 = 5381273) B5381273
theorem B2987767 : Blo 1863633 2987767 := bstep (se 1 (by rfl) ⟨2240825, by rfl⟩ : syracuseStep 2987767 = 4481651) B4481651
theorem B15120121 : Blo 1863633 15120121 := bstep (se 2 (by rfl) ⟨5670045, by rfl⟩ : syracuseStep 15120121 = 11340091) B11340091
theorem B1865511 : Blo 1863633 1865511 := bstep (se 1 (by rfl) ⟨1399133, by rfl⟩ : syracuseStep 1865511 = 2798267) B2798267
theorem B6379337 : Blo 1863633 6379337 := bstep (se 2 (by rfl) ⟨2392251, by rfl⟩ : syracuseStep 6379337 = 4784503) B4784503
theorem B1865551 : Blo 1863633 1865551 := bstep (se 1 (by rfl) ⟨1399163, by rfl⟩ : syracuseStep 1865551 = 2798327) B2798327
theorem B1865567 : Blo 1863633 1865567 := bstep (se 1 (by rfl) ⟨1399175, by rfl⟩ : syracuseStep 1865567 = 2798351) B2798351
theorem B1865595 : Blo 1863633 1865595 := bstep (se 1 (by rfl) ⟨1399196, by rfl⟩ : syracuseStep 1865595 = 2798393) B2798393
theorem B9435041 : Blo 1863633 9435041 := bstep (se 2 (by rfl) ⟨3538140, by rfl⟩ : syracuseStep 9435041 = 7076281) B7076281
theorem B9566113 : Blo 1863633 9566113 := bstep (se 2 (by rfl) ⟨3587292, by rfl⟩ : syracuseStep 9566113 = 7174585) B7174585
theorem B5380015 : Blo 1863633 5380015 := bstep (se 1 (by rfl) ⟨4035011, by rfl⟩ : syracuseStep 5380015 = 8070023) B8070023
theorem B3832057 : Blo 1863633 3832057 := bstep (se 2 (by rfl) ⟨1437021, by rfl⟩ : syracuseStep 3832057 = 2874043) B2874043
theorem B96876805 : Blo 1863633 96876805 := bstep (se 4 (by rfl) ⟨9082200, by rfl⟩ : syracuseStep 96876805 = 18164401) B18164401
theorem B6379787 : Blo 1863633 6379787 := bstep (se 1 (by rfl) ⟨4784840, by rfl⟩ : syracuseStep 6379787 = 9569681) B9569681
theorem B27244849 : Blo 1863633 27244849 := bstep (se 2 (by rfl) ⟨10216818, by rfl⟩ : syracuseStep 27244849 = 20433637) B20433637
theorem B6289865 : Blo 1863633 6289865 := bstep (se 2 (by rfl) ⟨2358699, by rfl⟩ : syracuseStep 6289865 = 4717399) B4717399
theorem B14154263 : Blo 1863633 14154263 := bstep (se 1 (by rfl) ⟨10615697, by rfl⟩ : syracuseStep 14154263 = 21231395) B21231395
theorem B49109579 : Blo 1863633 49109579 := bstep (se 1 (by rfl) ⟨36832184, by rfl⟩ : syracuseStep 49109579 = 73664369) B73664369
theorem B6290135 : Blo 1863633 6290135 := bstep (se 1 (by rfl) ⟨4717601, by rfl⟩ : syracuseStep 6290135 = 9435203) B9435203
theorem B6290351 : Blo 1863633 6290351 := bstep (se 1 (by rfl) ⟨4717763, by rfl⟩ : syracuseStep 6290351 = 9435527) B9435527
theorem B4193207 : Blo 1863633 4193207 := bstep (se 1 (by rfl) ⟨3144905, by rfl⟩ : syracuseStep 4193207 = 6289811) B6289811
theorem B10615859 : Blo 1863633 10615859 := bstep (se 1 (by rfl) ⟨7961894, by rfl⟩ : syracuseStep 10615859 = 15923789) B15923789
theorem B14163011 : Blo 1863633 14163011 := bstep (se 1 (by rfl) ⟨10622258, by rfl⟩ : syracuseStep 14163011 = 21244517) B21244517
theorem B11951171 : Blo 1863633 11951171 := bstep (se 1 (by rfl) ⟨8963378, by rfl⟩ : syracuseStep 11951171 = 17926757) B17926757
theorem B9444599 : Blo 1863633 9444599 := bstep (se 1 (by rfl) ⟨7083449, by rfl⟩ : syracuseStep 9444599 = 14166899) B14166899
theorem B3144953 : Blo 1863633 3144953 := bstep (se 2 (by rfl) ⟨1179357, by rfl⟩ : syracuseStep 3144953 = 2358715) B2358715
theorem B24214909 : Blo 1863633 24214909 := bstep (se 3 (by rfl) ⟨4540295, by rfl⟩ : syracuseStep 24214909 = 9080591) B9080591
theorem B3145135 : Blo 1863633 3145135 := bstep (se 1 (by rfl) ⟨2358851, by rfl⟩ : syracuseStep 3145135 = 4717703) B4717703
theorem B3145223 : Blo 1863633 3145223 := bstep (se 1 (by rfl) ⟨2358917, by rfl⟩ : syracuseStep 3145223 = 4717835) B4717835
theorem B4193801 : Blo 1863633 4193801 := bstep (se 2 (by rfl) ⟨1572675, by rfl⟩ : syracuseStep 4193801 = 3145351) B3145351
theorem B122650253 : Blo 1863633 122650253 := bstep (se 3 (by rfl) ⟨22996922, by rfl⟩ : syracuseStep 122650253 = 45993845) B45993845
theorem B13442705 : Blo 1863633 13442705 := bstep (se 2 (by rfl) ⟨5041014, by rfl⟩ : syracuseStep 13442705 = 10082029) B10082029
theorem B2358983 : Blo 1863633 2358983 := bstep (se 1 (by rfl) ⟨1769237, by rfl⟩ : syracuseStep 2358983 = 3538475) B3538475
theorem B1990495 : Blo 1863633 1990495 := bstep (se 1 (by rfl) ⟨1492871, by rfl⟩ : syracuseStep 1990495 = 2985743) B2985743
theorem B2359135 : Blo 1863633 2359135 := bstep (se 1 (by rfl) ⟨1769351, by rfl⟩ : syracuseStep 2359135 = 3538703) B3538703
theorem B3145567 : Blo 1863633 3145567 := bstep (se 1 (by rfl) ⟨2359175, by rfl⟩ : syracuseStep 3145567 = 4718351) B4718351
theorem B4194143 : Blo 1863633 4194143 := bstep (se 1 (by rfl) ⟨3145607, by rfl⟩ : syracuseStep 4194143 = 6291215) B6291215
theorem B7077739 : Blo 1863633 7077739 := bstep (se 1 (by rfl) ⟨5308304, by rfl⟩ : syracuseStep 7077739 = 10616609) B10616609
theorem B3145655 : Blo 1863633 3145655 := bstep (se 1 (by rfl) ⟨2359241, by rfl⟩ : syracuseStep 3145655 = 4718483) B4718483
theorem B11337659 : Blo 1863633 11337659 := bstep (se 1 (by rfl) ⟨8503244, by rfl⟩ : syracuseStep 11337659 = 17006489) B17006489
theorem B17924105 : Blo 1863633 17924105 := bstep (se 2 (by rfl) ⟨6721539, by rfl⟩ : syracuseStep 17924105 = 13443079) B13443079
theorem B8069291 : Blo 1863633 8069291 := bstep (se 1 (by rfl) ⟨6051968, by rfl⟩ : syracuseStep 8069291 = 12103937) B12103937
theorem B4718857 : Blo 1863633 4718857 := bstep (se 2 (by rfl) ⟨1769571, by rfl⟩ : syracuseStep 4718857 = 3539143) B3539143
theorem B2097499 : Blo 1863633 2097499 := bstep (se 1 (by rfl) ⟨1573124, by rfl⟩ : syracuseStep 2097499 = 3146249) B3146249
theorem B2097607 : Blo 1863633 2097607 := bstep (se 1 (by rfl) ⟨1573205, by rfl⟩ : syracuseStep 2097607 = 3146411) B3146411
theorem B5308897 : Blo 1863633 5308897 := bstep (se 2 (by rfl) ⟨1990836, by rfl⟩ : syracuseStep 5308897 = 3981673) B3981673
theorem B3981793 : Blo 1863633 3981793 := bstep (se 2 (by rfl) ⟨1493172, by rfl⟩ : syracuseStep 3981793 = 2986345) B2986345
theorem B2834939 : Blo 1863633 2834939 := bstep (se 1 (by rfl) ⟨2126204, by rfl⟩ : syracuseStep 2834939 = 4252409) B4252409
theorem B3146303 : Blo 1863633 3146303 := bstep (se 1 (by rfl) ⟨2359727, by rfl⟩ : syracuseStep 3146303 = 4719455) B4719455
theorem B4604537 : Blo 1863633 4604537 := bstep (se 2 (by rfl) ⟨1726701, by rfl⟩ : syracuseStep 4604537 = 3453403) B3453403
theorem B21234311 : Blo 1863633 21234311 := bstep (se 1 (by rfl) ⟨15925733, by rfl⟩ : syracuseStep 21234311 = 31851467) B31851467
theorem B5972663 : Blo 1863633 5972663 := bstep (se 1 (by rfl) ⟨4479497, by rfl⟩ : syracuseStep 5972663 = 8958995) B8958995
theorem B2097967 : Blo 1863633 2097967 := bstep (se 1 (by rfl) ⟨1573475, by rfl⟩ : syracuseStep 2097967 = 3146951) B3146951
theorem B4195151 : Blo 1863633 4195151 := bstep (se 1 (by rfl) ⟨3146363, by rfl⟩ : syracuseStep 4195151 = 6292727) B6292727
theorem B1991503 : Blo 1863633 1991503 := bstep (se 1 (by rfl) ⟨1493627, by rfl⟩ : syracuseStep 1991503 = 2987255) B2987255
theorem B2098075 : Blo 1863633 2098075 := bstep (se 1 (by rfl) ⟨1573556, by rfl⟩ : syracuseStep 2098075 = 3147113) B3147113
theorem B14164955 : Blo 1863633 14164955 := bstep (se 1 (by rfl) ⟨10623716, by rfl⟩ : syracuseStep 14164955 = 21247433) B21247433
theorem B6718439 : Blo 1863633 6718439 := bstep (se 1 (by rfl) ⟨5038829, by rfl⟩ : syracuseStep 6718439 = 10077659) B10077659
theorem B4482035 : Blo 1863633 4482035 := bstep (se 1 (by rfl) ⟨3361526, by rfl⟩ : syracuseStep 4482035 = 6723053) B6723053
theorem B20161543 : Blo 1863633 20161543 := bstep (se 1 (by rfl) ⟨15121157, by rfl⟩ : syracuseStep 20161543 = 30242315) B30242315
theorem B4195367 : Blo 1863633 4195367 := bstep (se 1 (by rfl) ⟨3146525, by rfl⟩ : syracuseStep 4195367 = 6293051) B6293051
theorem B3982459 : Blo 1863633 3982459 := bstep (se 1 (by rfl) ⟨2986844, by rfl⟩ : syracuseStep 3982459 = 5973689) B5973689
theorem B4195547 : Blo 1863633 4195547 := bstep (se 1 (by rfl) ⟨3146660, by rfl⟩ : syracuseStep 4195547 = 6293321) B6293321
theorem B3146971 : Blo 1863633 3146971 := bstep (se 1 (by rfl) ⟨2360228, by rfl⟩ : syracuseStep 3146971 = 4720457) B4720457
theorem B2655451 : Blo 1863633 2655451 := bstep (se 1 (by rfl) ⟨1991588, by rfl⟩ : syracuseStep 2655451 = 3983177) B3983177
theorem B2098471 : Blo 1863633 2098471 := bstep (se 1 (by rfl) ⟨1573853, by rfl⟩ : syracuseStep 2098471 = 3147707) B3147707
theorem B11945303 : Blo 1863633 11945303 := bstep (se 1 (by rfl) ⟨8958977, by rfl⟩ : syracuseStep 11945303 = 17917955) B17917955
theorem B2098543 : Blo 1863633 2098543 := bstep (se 1 (by rfl) ⟨1573907, by rfl⟩ : syracuseStep 2098543 = 3147815) B3147815
theorem B14157179 : Blo 1863633 14157179 := bstep (se 1 (by rfl) ⟨10617884, by rfl⟩ : syracuseStep 14157179 = 21235769) B21235769
theorem B4195745 : Blo 1863633 4195745 := bstep (se 2 (by rfl) ⟨1573404, by rfl⟩ : syracuseStep 4195745 = 3146809) B3146809
theorem B4253191 : Blo 1863633 4253191 := bstep (se 1 (by rfl) ⟨3189893, by rfl⟩ : syracuseStep 4253191 = 6379787) B6379787
theorem B2098759 : Blo 1863633 2098759 := bstep (se 1 (by rfl) ⟨1574069, by rfl⟩ : syracuseStep 2098759 = 3148139) B3148139
theorem B2360927 : Blo 1863633 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B4720315 : Blo 1863633 4720315 := bstep (se 1 (by rfl) ⟨3540236, by rfl⟩ : syracuseStep 4720315 = 7080473) B7080473
theorem B32286545 : Blo 1863633 32286545 := bstep (se 2 (by rfl) ⟨12107454, by rfl⟩ : syracuseStep 32286545 = 24214909) B24214909
theorem B38266829 : Blo 1863633 38266829 := bstep (se 3 (by rfl) ⟨7175030, by rfl⟩ : syracuseStep 38266829 = 14350061) B14350061
theorem B2795471 : Blo 1863633 2795471 := bstep (se 1 (by rfl) ⟨2096603, by rfl⟩ : syracuseStep 2795471 = 4193207) B4193207
theorem B3360719 : Blo 1863633 3360719 := bstep (se 1 (by rfl) ⟨2520539, by rfl⟩ : syracuseStep 3360719 = 5041079) B5041079
theorem B4196303 : Blo 1863633 4196303 := bstep (se 1 (by rfl) ⟨3147227, by rfl⟩ : syracuseStep 4196303 = 6294455) B6294455
theorem B3147727 : Blo 1863633 3147727 := bstep (se 1 (by rfl) ⟨2360795, by rfl⟩ : syracuseStep 3147727 = 4721591) B4721591
theorem B10078181 : Blo 1863633 10078181 := bstep (se 4 (by rfl) ⟨944829, by rfl⟩ : syracuseStep 10078181 = 1889659) B1889659
theorem B6293537 : Blo 1863633 6293537 := bstep (se 2 (by rfl) ⟨2360076, by rfl⟩ : syracuseStep 6293537 = 4720153) B4720153
theorem B4196681 : Blo 1863633 4196681 := bstep (se 2 (by rfl) ⟨1573755, by rfl⟩ : syracuseStep 4196681 = 3147511) B3147511
theorem B3983689 : Blo 1863633 3983689 := bstep (se 2 (by rfl) ⟨1493883, by rfl⟩ : syracuseStep 3983689 = 2987767) B2987767
theorem B2795867 : Blo 1863633 2795867 := bstep (se 1 (by rfl) ⟨2096900, by rfl⟩ : syracuseStep 2795867 = 4193801) B4193801
theorem B4196699 : Blo 1863633 4196699 := bstep (se 1 (by rfl) ⟨3147524, by rfl⟩ : syracuseStep 4196699 = 6295049) B6295049
theorem B9079183 : Blo 1863633 9079183 := bstep (se 1 (by rfl) ⟨6809387, by rfl⟩ : syracuseStep 9079183 = 13618775) B13618775
theorem B81766835 : Blo 1863633 81766835 := bstep (se 1 (by rfl) ⟨61325126, by rfl⟩ : syracuseStep 81766835 = 122650253) B122650253
theorem B9439739 : Blo 1863633 9439739 := bstep (se 1 (by rfl) ⟨7079804, by rfl⟩ : syracuseStep 9439739 = 14159609) B14159609
theorem B7080443 : Blo 1863633 7080443 := bstep (se 1 (by rfl) ⟨5310332, by rfl⟩ : syracuseStep 7080443 = 10620665) B10620665
theorem B5310971 : Blo 1863633 5310971 := bstep (se 1 (by rfl) ⟨3983228, by rfl⟩ : syracuseStep 5310971 = 7966457) B7966457
theorem B2796095 : Blo 1863633 2796095 := bstep (se 1 (by rfl) ⟨2097071, by rfl⟩ : syracuseStep 2796095 = 4194143) B4194143
theorem B2796215 : Blo 1863633 2796215 := bstep (se 1 (by rfl) ⟨2097161, by rfl⟩ : syracuseStep 2796215 = 4194323) B4194323
theorem B66390749 : Blo 1863633 66390749 := bstep (se 3 (by rfl) ⟨12448265, by rfl⟩ : syracuseStep 66390749 = 24896531) B24896531
theorem B2239211 : Blo 1863633 2239211 := bstep (se 1 (by rfl) ⟨1679408, by rfl⟩ : syracuseStep 2239211 = 3358817) B3358817
theorem B4721399 : Blo 1863633 4721399 := bstep (se 1 (by rfl) ⟨3541049, by rfl⟩ : syracuseStep 4721399 = 7082099) B7082099
theorem B2796443 : Blo 1863633 2796443 := bstep (se 1 (by rfl) ⟨2097332, by rfl⟩ : syracuseStep 2796443 = 4194665) B4194665
theorem B4197275 : Blo 1863633 4197275 := bstep (se 1 (by rfl) ⟨3147956, by rfl⟩ : syracuseStep 4197275 = 6295913) B6295913
theorem B5311403 : Blo 1863633 5311403 := bstep (se 1 (by rfl) ⟨3983552, by rfl⟩ : syracuseStep 5311403 = 7967105) B7967105
theorem B36326465 : Blo 1863633 36326465 := bstep (se 2 (by rfl) ⟨13622424, by rfl⟩ : syracuseStep 36326465 = 27244849) B27244849
theorem B4197473 : Blo 1863633 4197473 := bstep (se 2 (by rfl) ⟨1574052, by rfl⟩ : syracuseStep 4197473 = 3148105) B3148105
theorem B2796839 : Blo 1863633 2796839 := bstep (se 1 (by rfl) ⟨2097629, by rfl⟩ : syracuseStep 2796839 = 4195259) B4195259
theorem B4197671 : Blo 1863633 4197671 := bstep (se 1 (by rfl) ⟨3148253, by rfl⟩ : syracuseStep 4197671 = 6296507) B6296507
theorem B2796923 : Blo 1863633 2796923 := bstep (se 1 (by rfl) ⟨2097692, by rfl⟩ : syracuseStep 2796923 = 4195385) B4195385
theorem B9440711 : Blo 1863633 9440711 := bstep (se 1 (by rfl) ⟨7080533, by rfl⟩ : syracuseStep 9440711 = 14161067) B14161067
theorem B7081415 : Blo 1863633 7081415 := bstep (se 1 (by rfl) ⟨5311061, by rfl⟩ : syracuseStep 7081415 = 10622123) B10622123
theorem B2797049 : Blo 1863633 2797049 := bstep (se 2 (by rfl) ⟨1048893, by rfl⟩ : syracuseStep 2797049 = 2097787) B2097787
theorem B4722259 : Blo 1863633 4722259 := bstep (se 1 (by rfl) ⟨3541694, by rfl⟩ : syracuseStep 4722259 = 7083389) B7083389
theorem B2797151 : Blo 1863633 2797151 := bstep (se 1 (by rfl) ⟨2097863, by rfl⟩ : syracuseStep 2797151 = 4195727) B4195727
theorem B7556723 : Blo 1863633 7556723 := bstep (se 1 (by rfl) ⟨5667542, by rfl⟩ : syracuseStep 7556723 = 11335085) B11335085
theorem B19132139 : Blo 1863633 19132139 := bstep (se 1 (by rfl) ⟨14349104, by rfl⟩ : syracuseStep 19132139 = 28698209) B28698209
theorem B11947787 : Blo 1863633 11947787 := bstep (se 1 (by rfl) ⟨8960840, by rfl⟩ : syracuseStep 11947787 = 17921681) B17921681
theorem B9441035 : Blo 1863633 9441035 := bstep (se 1 (by rfl) ⟨7080776, by rfl⟩ : syracuseStep 9441035 = 14161553) B14161553
theorem B2797367 : Blo 1863633 2797367 := bstep (se 1 (by rfl) ⟨2098025, by rfl⟩ : syracuseStep 2797367 = 4196051) B4196051
theorem B1863655 : Blo 1863633 1863655 := bstep (se 1 (by rfl) ⟨1397741, by rfl⟩ : syracuseStep 1863655 = 2795483) B2795483
theorem B2797673 : Blo 1863633 2797673 := bstep (se 2 (by rfl) ⟨1049127, by rfl⟩ : syracuseStep 2797673 = 2098255) B2098255
theorem B30249065 : Blo 1863633 30249065 := bstep (se 2 (by rfl) ⟨11343399, by rfl⟩ : syracuseStep 30249065 = 22686799) B22686799
theorem B1863967 : Blo 1863633 1863967 := bstep (se 1 (by rfl) ⟨1397975, by rfl⟩ : syracuseStep 1863967 = 2795951) B2795951
theorem B1864027 : Blo 1863633 1864027 := bstep (se 1 (by rfl) ⟨1398020, by rfl⟩ : syracuseStep 1864027 = 2796041) B2796041
theorem B1864047 : Blo 1863633 1864047 := bstep (se 1 (by rfl) ⟨1398035, by rfl⟩ : syracuseStep 1864047 = 2796071) B2796071
theorem B32739719 : Blo 1863633 32739719 := bstep (se 1 (by rfl) ⟨24554789, by rfl⟩ : syracuseStep 32739719 = 49109579) B49109579
theorem B1864103 : Blo 1863633 1864103 := bstep (se 1 (by rfl) ⟨1398077, by rfl⟩ : syracuseStep 1864103 = 2796155) B2796155
theorem B2797991 : Blo 1863633 2797991 := bstep (se 1 (by rfl) ⟨2098493, by rfl⟩ : syracuseStep 2797991 = 4196987) B4196987
theorem B1864187 : Blo 1863633 1864187 := bstep (se 1 (by rfl) ⟨1398140, by rfl⟩ : syracuseStep 1864187 = 2796281) B2796281
theorem B2798075 : Blo 1863633 2798075 := bstep (se 1 (by rfl) ⟨2098556, by rfl⟩ : syracuseStep 2798075 = 4197113) B4197113
theorem B1864255 : Blo 1863633 1864255 := bstep (se 1 (by rfl) ⟨1398191, by rfl⟩ : syracuseStep 1864255 = 2796383) B2796383
theorem B1864263 : Blo 1863633 1864263 := bstep (se 1 (by rfl) ⟨1398197, by rfl⟩ : syracuseStep 1864263 = 2796395) B2796395
theorem B2798201 : Blo 1863633 2798201 := bstep (se 2 (by rfl) ⟨1049325, by rfl⟩ : syracuseStep 2798201 = 2098651) B2098651
theorem B2798255 : Blo 1863633 2798255 := bstep (se 1 (by rfl) ⟨2098691, by rfl⟩ : syracuseStep 2798255 = 4197383) B4197383
theorem B9442007 : Blo 1863633 9442007 := bstep (se 1 (by rfl) ⟨7081505, by rfl⟩ : syracuseStep 9442007 = 14163011) B14163011
theorem B7967447 : Blo 1863633 7967447 := bstep (se 1 (by rfl) ⟨5975585, by rfl⟩ : syracuseStep 7967447 = 11951171) B11951171
theorem B1864415 : Blo 1863633 1864415 := bstep (se 1 (by rfl) ⟨1398311, by rfl⟩ : syracuseStep 1864415 = 2796623) B2796623
theorem B2798303 : Blo 1863633 2798303 := bstep (se 1 (by rfl) ⟨2098727, by rfl⟩ : syracuseStep 2798303 = 4197455) B4197455
theorem B1864495 : Blo 1863633 1864495 := bstep (se 1 (by rfl) ⟨1398371, by rfl⟩ : syracuseStep 1864495 = 2796743) B2796743
theorem B6296399 : Blo 1863633 6296399 := bstep (se 1 (by rfl) ⟨4722299, by rfl⟩ : syracuseStep 6296399 = 9444599) B9444599
theorem B17011565 : Blo 1863633 17011565 := bstep (se 3 (by rfl) ⟨3189668, by rfl⟩ : syracuseStep 17011565 = 6379337) B6379337
theorem B1864603 : Blo 1863633 1864603 := bstep (se 1 (by rfl) ⟨1398452, by rfl⟩ : syracuseStep 1864603 = 2796905) B2796905
theorem B1864655 : Blo 1863633 1864655 := bstep (se 1 (by rfl) ⟨1398491, by rfl⟩ : syracuseStep 1864655 = 2796983) B2796983
theorem B1864679 : Blo 1863633 1864679 := bstep (se 1 (by rfl) ⟨1398509, by rfl⟩ : syracuseStep 1864679 = 2797019) B2797019
theorem B7369871 : Blo 1863633 7369871 := bstep (se 1 (by rfl) ⟨5527403, by rfl⟩ : syracuseStep 7369871 = 11054807) B11054807
theorem B7173353 : Blo 1863633 7173353 := bstep (se 2 (by rfl) ⟨2690007, by rfl⟩ : syracuseStep 7173353 = 5380015) B5380015
theorem B1864991 : Blo 1863633 1864991 := bstep (se 1 (by rfl) ⟨1398743, by rfl⟩ : syracuseStep 1864991 = 2797487) B2797487
theorem B7558439 : Blo 1863633 7558439 := bstep (se 1 (by rfl) ⟨5668829, by rfl⟩ : syracuseStep 7558439 = 11337659) B11337659
theorem B1865051 : Blo 1863633 1865051 := bstep (se 1 (by rfl) ⟨1398788, by rfl⟩ : syracuseStep 1865051 = 2797577) B2797577
theorem B9442655 : Blo 1863633 9442655 := bstep (se 1 (by rfl) ⟨7081991, by rfl⟩ : syracuseStep 9442655 = 14163983) B14163983
theorem B7083359 : Blo 1863633 7083359 := bstep (se 1 (by rfl) ⟨5312519, by rfl⟩ : syracuseStep 7083359 = 10625039) B10625039
theorem B1865071 : Blo 1863633 1865071 := bstep (se 1 (by rfl) ⟨1398803, by rfl⟩ : syracuseStep 1865071 = 2797607) B2797607
theorem B4478345 : Blo 1863633 4478345 := bstep (se 2 (by rfl) ⟨1679379, by rfl⟩ : syracuseStep 4478345 = 3358759) B3358759
theorem B1865127 : Blo 1863633 1865127 := bstep (se 1 (by rfl) ⟨1398845, by rfl⟩ : syracuseStep 1865127 = 2797691) B2797691
theorem B1865211 : Blo 1863633 1865211 := bstep (se 1 (by rfl) ⟨1398908, by rfl⟩ : syracuseStep 1865211 = 2797817) B2797817
theorem B15922727 : Blo 1863633 15922727 := bstep (se 1 (by rfl) ⟨11942045, by rfl⟩ : syracuseStep 15922727 = 23884091) B23884091
theorem B1865279 : Blo 1863633 1865279 := bstep (se 1 (by rfl) ⟨1398959, by rfl⟩ : syracuseStep 1865279 = 2797919) B2797919
theorem B1865287 : Blo 1863633 1865287 := bstep (se 1 (by rfl) ⟨1398965, by rfl⟩ : syracuseStep 1865287 = 2797931) B2797931
theorem B20158085 : Blo 1863633 20158085 := bstep (se 4 (by rfl) ⟨1889820, by rfl⟩ : syracuseStep 20158085 = 3779641) B3779641
theorem B5109409 : Blo 1863633 5109409 := bstep (se 2 (by rfl) ⟨1916028, by rfl⟩ : syracuseStep 5109409 = 3832057) B3832057
theorem B129169073 : Blo 1863633 129169073 := bstep (se 2 (by rfl) ⟨48438402, by rfl⟩ : syracuseStep 129169073 = 96876805) B96876805
theorem B1865439 : Blo 1863633 1865439 := bstep (se 1 (by rfl) ⟨1399079, by rfl⟩ : syracuseStep 1865439 = 2798159) B2798159
theorem B294508331 : Blo 1863633 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B1865519 : Blo 1863633 1865519 := bstep (se 1 (by rfl) ⟨1399139, by rfl⟩ : syracuseStep 1865519 = 2798279) B2798279
theorem B1865627 : Blo 1863633 1865627 := bstep (se 1 (by rfl) ⟨1399220, by rfl⟩ : syracuseStep 1865627 = 2798441) B2798441
theorem B40851863 : Blo 1863633 40851863 := bstep (se 1 (by rfl) ⟨30638897, by rfl⟩ : syracuseStep 40851863 = 61277795) B61277795
theorem B7961075 : Blo 1863633 7961075 := bstep (se 1 (by rfl) ⟨5970806, by rfl⟩ : syracuseStep 7961075 = 11941613) B11941613
theorem B7559675 : Blo 1863633 7559675 := bstep (se 1 (by rfl) ⟨5669756, by rfl⟩ : syracuseStep 7559675 = 11339513) B11339513
theorem B6290027 : Blo 1863633 6290027 := bstep (se 1 (by rfl) ⟨4717520, by rfl⟩ : syracuseStep 6290027 = 9435041) B9435041
theorem B4479671 : Blo 1863633 4479671 := bstep (se 1 (by rfl) ⟨3359753, by rfl⟩ : syracuseStep 4479671 = 6719507) B6719507
theorem B26893129 : Blo 1863633 26893129 := bstep (se 2 (by rfl) ⟨10084923, by rfl⟩ : syracuseStep 26893129 = 20169847) B20169847
theorem B6052751 : Blo 1863633 6052751 := bstep (se 1 (by rfl) ⟨4539563, by rfl⟩ : syracuseStep 6052751 = 9079127) B9079127
theorem B10623899 : Blo 1863633 10623899 := bstep (se 1 (by rfl) ⟨7967924, by rfl⟩ : syracuseStep 10623899 = 15935849) B15935849
theorem B13622201 : Blo 1863633 13622201 := bstep (se 2 (by rfl) ⟨5108325, by rfl⟩ : syracuseStep 13622201 = 10216651) B10216651
theorem B4193243 : Blo 1863633 4193243 := bstep (se 1 (by rfl) ⟨3144932, by rfl⟩ : syracuseStep 4193243 = 6289865) B6289865
theorem B9436175 : Blo 1863633 9436175 := bstep (se 1 (by rfl) ⟨7077131, by rfl⟩ : syracuseStep 9436175 = 14154263) B14154263
theorem B4250747 : Blo 1863633 4250747 := bstep (se 1 (by rfl) ⟨3188060, by rfl⟩ : syracuseStep 4250747 = 6376121) B6376121
theorem B4193423 : Blo 1863633 4193423 := bstep (se 1 (by rfl) ⟨3145067, by rfl⟩ : syracuseStep 4193423 = 6290135) B6290135
theorem B6290621 : Blo 1863633 6290621 := bstep (se 3 (by rfl) ⟨1179491, by rfl⟩ : syracuseStep 6290621 = 2358983) B2358983
theorem B4193513 : Blo 1863633 4193513 := bstep (se 2 (by rfl) ⟨1572567, by rfl⟩ : syracuseStep 4193513 = 3145135) B3145135
theorem B4193567 : Blo 1863633 4193567 := bstep (se 1 (by rfl) ⟨3145175, by rfl⟩ : syracuseStep 4193567 = 6290351) B6290351
theorem B7077239 : Blo 1863633 7077239 := bstep (se 1 (by rfl) ⟨5307929, by rfl⟩ : syracuseStep 7077239 = 10615859) B10615859
theorem B2096635 : Blo 1863633 2096635 := bstep (se 1 (by rfl) ⟨1572476, by rfl⟩ : syracuseStep 2096635 = 3144953) B3144953
theorem B10624607 : Blo 1863633 10624607 := bstep (se 1 (by rfl) ⟨7968455, by rfl⟩ : syracuseStep 10624607 = 15936911) B15936911
theorem B114810529 : Blo 1863633 114810529 := bstep (se 2 (by rfl) ⟨43053948, by rfl⟩ : syracuseStep 114810529 = 86107897) B86107897
theorem B20160161 : Blo 1863633 20160161 := bstep (se 2 (by rfl) ⟨7560060, by rfl⟩ : syracuseStep 20160161 = 15120121) B15120121
theorem B2096815 : Blo 1863633 2096815 := bstep (se 1 (by rfl) ⟨1572611, by rfl⟩ : syracuseStep 2096815 = 3145223) B3145223
theorem B8961803 : Blo 1863633 8961803 := bstep (se 1 (by rfl) ⟨6721352, by rfl⟩ : syracuseStep 8961803 = 13442705) B13442705
theorem B2653993 : Blo 1863633 2653993 := bstep (se 2 (by rfl) ⟨995247, by rfl⟩ : syracuseStep 2653993 = 1990495) B1990495
theorem B3145513 : Blo 1863633 3145513 := bstep (se 2 (by rfl) ⟨1179567, by rfl⟩ : syracuseStep 3145513 = 2359135) B2359135
theorem B4194089 : Blo 1863633 4194089 := bstep (se 2 (by rfl) ⟨1572783, by rfl⟩ : syracuseStep 4194089 = 3145567) B3145567
theorem B9436985 : Blo 1863633 9436985 := bstep (se 2 (by rfl) ⟨3538869, by rfl⟩ : syracuseStep 9436985 = 7077739) B7077739
theorem B12754817 : Blo 1863633 12754817 := bstep (se 2 (by rfl) ⟨4783056, by rfl⟩ : syracuseStep 12754817 = 9566113) B9566113
theorem B2097103 : Blo 1863633 2097103 := bstep (se 1 (by rfl) ⟨1572827, by rfl⟩ : syracuseStep 2097103 = 3145655) B3145655
theorem B22683685 : Blo 1863633 22683685 := bstep (se 4 (by rfl) ⟨2126595, by rfl⟩ : syracuseStep 22683685 = 4253191) B4253191
theorem B6291809 : Blo 1863633 6291809 := bstep (se 2 (by rfl) ⟨2359428, by rfl⟩ : syracuseStep 6291809 = 4718857) B4718857
theorem B2097535 : Blo 1863633 2097535 := bstep (se 1 (by rfl) ⟨1573151, by rfl⟩ : syracuseStep 2097535 = 3146303) B3146303
theorem B14156207 : Blo 1863633 14156207 := bstep (se 1 (by rfl) ⟨10617155, by rfl⟩ : syracuseStep 14156207 = 21234311) B21234311
theorem B7078529 : Blo 1863633 7078529 := bstep (se 2 (by rfl) ⟨2654448, by rfl⟩ : syracuseStep 7078529 = 5308897) B5308897
theorem B5309057 : Blo 1863633 5309057 := bstep (se 2 (by rfl) ⟨1990896, by rfl⟩ : syracuseStep 5309057 = 3981793) B3981793
theorem B7963535 : Blo 1863633 7963535 := bstep (se 1 (by rfl) ⟨5972651, by rfl⟩ : syracuseStep 7963535 = 11945303) B11945303
theorem B9438119 : Blo 1863633 9438119 := bstep (se 1 (by rfl) ⟨7078589, by rfl⟩ : syracuseStep 9438119 = 14157179) B14157179
theorem B35857505 : Blo 1863633 35857505 := bstep (se 2 (by rfl) ⟨13446564, by rfl⟩ : syracuseStep 35857505 = 26893129) B26893129
theorem B2655337 : Blo 1863633 2655337 := bstep (se 2 (by rfl) ⟨995751, by rfl⟩ : syracuseStep 2655337 = 1991503) B1991503
theorem B196338887 : Blo 1863633 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B25511219 : Blo 1863633 25511219 := bstep (se 1 (by rfl) ⟨19133414, by rfl⟩ : syracuseStep 25511219 = 38266829) B38266829
theorem B6718787 : Blo 1863633 6718787 := bstep (se 1 (by rfl) ⟨5039090, by rfl⟩ : syracuseStep 6718787 = 10078181) B10078181
theorem B4195691 : Blo 1863633 4195691 := bstep (se 1 (by rfl) ⟨3146768, by rfl⟩ : syracuseStep 4195691 = 6293537) B6293537
theorem B78611957 : Blo 1863633 78611957 := bstep (se 5 (by rfl) ⟨3684935, by rfl⟩ : syracuseStep 78611957 = 7369871) B7369871
theorem B5309945 : Blo 1863633 5309945 := bstep (se 2 (by rfl) ⟨1991229, by rfl⟩ : syracuseStep 5309945 = 3982459) B3982459
theorem B54511223 : Blo 1863633 54511223 := bstep (se 1 (by rfl) ⟨40883417, by rfl⟩ : syracuseStep 54511223 = 81766835) B81766835
theorem B4195961 : Blo 1863633 4195961 := bstep (se 2 (by rfl) ⟨1573485, by rfl⟩ : syracuseStep 4195961 = 3146971) B3146971
theorem B3540601 : Blo 1863633 3540601 := bstep (se 2 (by rfl) ⟨1327725, by rfl⟩ : syracuseStep 3540601 = 2655451) B2655451
theorem B5039783 : Blo 1863633 5039783 := bstep (se 1 (by rfl) ⟨3779837, by rfl⟩ : syracuseStep 5039783 = 7559675) B7559675
theorem B6293159 : Blo 1863633 6293159 := bstep (se 1 (by rfl) ⟨4719869, by rfl⟩ : syracuseStep 6293159 = 9439739) B9439739
theorem B4720295 : Blo 1863633 4720295 := bstep (se 1 (by rfl) ⟨3540221, by rfl⟩ : syracuseStep 4720295 = 7080443) B7080443
theorem B3540647 : Blo 1863633 3540647 := bstep (se 1 (by rfl) ⟨2655485, by rfl⟩ : syracuseStep 3540647 = 5310971) B5310971
theorem B15927101 : Blo 1863633 15927101 := bstep (se 3 (by rfl) ⟨2986331, by rfl⟩ : syracuseStep 15927101 = 5972663) B5972663
theorem B11945789 : Blo 1863633 11945789 := bstep (se 3 (by rfl) ⟨2239835, by rfl⟩ : syracuseStep 11945789 = 4479671) B4479671
theorem B3147599 : Blo 1863633 3147599 := bstep (se 1 (by rfl) ⟨2360699, by rfl⟩ : syracuseStep 3147599 = 4721399) B4721399
theorem B3540935 : Blo 1863633 3540935 := bstep (se 1 (by rfl) ⟨2655701, by rfl⟩ : syracuseStep 3540935 = 5311403) B5311403
theorem B2795495 : Blo 1863633 2795495 := bstep (se 1 (by rfl) ⟨2096621, by rfl⟩ : syracuseStep 2795495 = 4193243) B4193243
theorem B2795513 : Blo 1863633 2795513 := bstep (se 2 (by rfl) ⟨1048317, by rfl⟩ : syracuseStep 2795513 = 2096635) B2096635
theorem B24217643 : Blo 1863633 24217643 := bstep (se 1 (by rfl) ⟨18163232, by rfl⟩ : syracuseStep 24217643 = 36326465) B36326465
theorem B2795615 : Blo 1863633 2795615 := bstep (se 1 (by rfl) ⟨2096711, by rfl⟩ : syracuseStep 2795615 = 4193423) B4193423
theorem B2795675 : Blo 1863633 2795675 := bstep (se 1 (by rfl) ⟨2096756, by rfl⟩ : syracuseStep 2795675 = 4193513) B4193513
theorem B2795711 : Blo 1863633 2795711 := bstep (se 1 (by rfl) ⟨2096783, by rfl⟩ : syracuseStep 2795711 = 4193567) B4193567
theorem B2795753 : Blo 1863633 2795753 := bstep (se 2 (by rfl) ⟨1048407, by rfl⟩ : syracuseStep 2795753 = 2096815) B2096815
theorem B6293753 : Blo 1863633 6293753 := bstep (se 2 (by rfl) ⟨2360157, by rfl⟩ : syracuseStep 6293753 = 4720315) B4720315
theorem B6293807 : Blo 1863633 6293807 := bstep (se 1 (by rfl) ⟨4720355, by rfl⟩ : syracuseStep 6293807 = 9440711) B9440711
theorem B4720943 : Blo 1863633 4720943 := bstep (se 1 (by rfl) ⟨3540707, by rfl⟩ : syracuseStep 4720943 = 7081415) B7081415
theorem B7965191 : Blo 1863633 7965191 := bstep (se 1 (by rfl) ⟨5973893, by rfl⟩ : syracuseStep 7965191 = 11947787) B11947787
theorem B6294023 : Blo 1863633 6294023 := bstep (se 1 (by rfl) ⟨4720517, by rfl⟩ : syracuseStep 6294023 = 9441035) B9441035
theorem B5974535 : Blo 1863633 5974535 := bstep (se 1 (by rfl) ⟨4480901, by rfl⟩ : syracuseStep 5974535 = 8961803) B8961803
theorem B2796059 : Blo 1863633 2796059 := bstep (se 1 (by rfl) ⟨2097044, by rfl⟩ : syracuseStep 2796059 = 4194089) B4194089
theorem B2796137 : Blo 1863633 2796137 := bstep (se 2 (by rfl) ⟨1048551, by rfl⟩ : syracuseStep 2796137 = 2097103) B2097103
theorem B4196969 : Blo 1863633 4196969 := bstep (se 2 (by rfl) ⟨1573863, by rfl⟩ : syracuseStep 4196969 = 3147727) B3147727
theorem B5311585 : Blo 1863633 5311585 := bstep (se 2 (by rfl) ⟨1991844, by rfl⟩ : syracuseStep 5311585 = 3983689) B3983689
theorem B2796665 : Blo 1863633 2796665 := bstep (se 2 (by rfl) ⟨1048749, by rfl⟩ : syracuseStep 2796665 = 2097499) B2097499
theorem B6294671 : Blo 1863633 6294671 := bstep (se 1 (by rfl) ⟨4721003, by rfl⟩ : syracuseStep 6294671 = 9442007) B9442007
theorem B5311631 : Blo 1863633 5311631 := bstep (se 1 (by rfl) ⟨3983723, by rfl⟩ : syracuseStep 5311631 = 7967447) B7967447
theorem B2796767 : Blo 1863633 2796767 := bstep (se 1 (by rfl) ⟨2097575, by rfl⟩ : syracuseStep 2796767 = 4195151) B4195151
theorem B4197599 : Blo 1863633 4197599 := bstep (se 1 (by rfl) ⟨3148199, by rfl⟩ : syracuseStep 4197599 = 6296399) B6296399
theorem B11341043 : Blo 1863633 11341043 := bstep (se 1 (by rfl) ⟨8505782, by rfl⟩ : syracuseStep 11341043 = 17011565) B17011565
theorem B2796809 : Blo 1863633 2796809 := bstep (se 2 (by rfl) ⟨1048803, by rfl⟩ : syracuseStep 2796809 = 2097607) B2097607
theorem B2796911 : Blo 1863633 2796911 := bstep (se 1 (by rfl) ⟨2097683, by rfl⟩ : syracuseStep 2796911 = 4195367) B4195367
theorem B20155837 : Blo 1863633 20155837 := bstep (se 3 (by rfl) ⟨3779219, by rfl⟩ : syracuseStep 20155837 = 7558439) B7558439
theorem B2797031 : Blo 1863633 2797031 := bstep (se 1 (by rfl) ⟨2097773, by rfl⟩ : syracuseStep 2797031 = 4195547) B4195547
theorem B27250181 : Blo 1863633 27250181 := bstep (se 4 (by rfl) ⟨2554704, by rfl⟩ : syracuseStep 27250181 = 5109409) B5109409
theorem B6295103 : Blo 1863633 6295103 := bstep (se 1 (by rfl) ⟨4721327, by rfl⟩ : syracuseStep 6295103 = 9442655) B9442655
theorem B4722239 : Blo 1863633 4722239 := bstep (se 1 (by rfl) ⟨3541679, by rfl⟩ : syracuseStep 4722239 = 7083359) B7083359
theorem B2985563 : Blo 1863633 2985563 := bstep (se 1 (by rfl) ⟨2239172, by rfl⟩ : syracuseStep 2985563 = 4478345) B4478345
theorem B2797163 : Blo 1863633 2797163 := bstep (se 1 (by rfl) ⟨2097872, by rfl⟩ : syracuseStep 2797163 = 4195745) B4195745
theorem B2797289 : Blo 1863633 2797289 := bstep (se 2 (by rfl) ⟨1048983, by rfl⟩ : syracuseStep 2797289 = 2097967) B2097967
theorem B13438723 : Blo 1863633 13438723 := bstep (se 1 (by rfl) ⟨10079042, by rfl⟩ : syracuseStep 13438723 = 20158085) B20158085
theorem B2797433 : Blo 1863633 2797433 := bstep (se 2 (by rfl) ⟨1049037, by rfl⟩ : syracuseStep 2797433 = 2098075) B2098075
theorem B21524363 : Blo 1863633 21524363 := bstep (se 1 (by rfl) ⟨16143272, by rfl⟩ : syracuseStep 21524363 = 32286545) B32286545
theorem B1863647 : Blo 1863633 1863647 := bstep (se 1 (by rfl) ⟨1397735, by rfl⟩ : syracuseStep 1863647 = 2795471) B2795471
theorem B2240479 : Blo 1863633 2240479 := bstep (se 1 (by rfl) ⟨1680359, by rfl⟩ : syracuseStep 2240479 = 3360719) B3360719
theorem B2797535 : Blo 1863633 2797535 := bstep (se 1 (by rfl) ⟨2098151, by rfl⟩ : syracuseStep 2797535 = 4196303) B4196303
theorem B26882057 : Blo 1863633 26882057 := bstep (se 2 (by rfl) ⟨10080771, by rfl⟩ : syracuseStep 26882057 = 20161543) B20161543
theorem B2797787 : Blo 1863633 2797787 := bstep (se 1 (by rfl) ⟨2098340, by rfl⟩ : syracuseStep 2797787 = 4196681) B4196681
theorem B1863911 : Blo 1863633 1863911 := bstep (se 1 (by rfl) ⟨1397933, by rfl⟩ : syracuseStep 1863911 = 2795867) B2795867
theorem B2797799 : Blo 1863633 2797799 := bstep (se 1 (by rfl) ⟨2098349, by rfl⟩ : syracuseStep 2797799 = 4196699) B4196699
theorem B6295805 : Blo 1863633 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B27234575 : Blo 1863633 27234575 := bstep (se 1 (by rfl) ⟨20425931, by rfl⟩ : syracuseStep 27234575 = 40851863) B40851863
theorem B1864063 : Blo 1863633 1864063 := bstep (se 1 (by rfl) ⟨1398047, by rfl⟩ : syracuseStep 1864063 = 2796095) B2796095
theorem B2797961 : Blo 1863633 2797961 := bstep (se 2 (by rfl) ⟨1049235, by rfl⟩ : syracuseStep 2797961 = 2098471) B2098471
theorem B1864143 : Blo 1863633 1864143 := bstep (se 1 (by rfl) ⟨1398107, by rfl⟩ : syracuseStep 1864143 = 2796215) B2796215
theorem B2798057 : Blo 1863633 2798057 := bstep (se 2 (by rfl) ⟨1049271, by rfl⟩ : syracuseStep 2798057 = 2098543) B2098543
theorem B4035167 : Blo 1863633 4035167 := bstep (se 1 (by rfl) ⟨3026375, by rfl⟩ : syracuseStep 4035167 = 6052751) B6052751
theorem B1864295 : Blo 1863633 1864295 := bstep (se 1 (by rfl) ⟨1398221, by rfl⟩ : syracuseStep 1864295 = 2796443) B2796443
theorem B7082599 : Blo 1863633 7082599 := bstep (se 1 (by rfl) ⟨5311949, by rfl⟩ : syracuseStep 7082599 = 10623899) B10623899
theorem B2798183 : Blo 1863633 2798183 := bstep (se 1 (by rfl) ⟨2098637, by rfl⟩ : syracuseStep 2798183 = 4197275) B4197275
theorem B9081467 : Blo 1863633 9081467 := bstep (se 1 (by rfl) ⟨6811100, by rfl⟩ : syracuseStep 9081467 = 13622201) B13622201
theorem B2798315 : Blo 1863633 2798315 := bstep (se 1 (by rfl) ⟨2098736, by rfl⟩ : syracuseStep 2798315 = 4197473) B4197473
theorem B2798345 : Blo 1863633 2798345 := bstep (se 2 (by rfl) ⟨1049379, by rfl⟩ : syracuseStep 2798345 = 2098759) B2098759
theorem B6296345 : Blo 1863633 6296345 := bstep (se 2 (by rfl) ⟨2361129, by rfl⟩ : syracuseStep 6296345 = 4722259) B4722259
theorem B1864559 : Blo 1863633 1864559 := bstep (se 1 (by rfl) ⟨1398419, by rfl⟩ : syracuseStep 1864559 = 2796839) B2796839
theorem B2798447 : Blo 1863633 2798447 := bstep (se 1 (by rfl) ⟨2098835, by rfl⟩ : syracuseStep 2798447 = 4197671) B4197671
theorem B153080705 : Blo 1863633 153080705 := bstep (se 2 (by rfl) ⟨57405264, by rfl⟩ : syracuseStep 153080705 = 114810529) B114810529
theorem B1864615 : Blo 1863633 1864615 := bstep (se 1 (by rfl) ⟨1398461, by rfl⟩ : syracuseStep 1864615 = 2796923) B2796923
theorem B1864699 : Blo 1863633 1864699 := bstep (se 1 (by rfl) ⟨1398524, by rfl⟩ : syracuseStep 1864699 = 2797049) B2797049
theorem B1864767 : Blo 1863633 1864767 := bstep (se 1 (by rfl) ⟨1398575, by rfl⟩ : syracuseStep 1864767 = 2797151) B2797151
theorem B7083071 : Blo 1863633 7083071 := bstep (se 1 (by rfl) ⟨5312303, by rfl⟩ : syracuseStep 7083071 = 10624607) B10624607
theorem B13440107 : Blo 1863633 13440107 := bstep (se 1 (by rfl) ⟨10080080, by rfl⟩ : syracuseStep 13440107 = 20160161) B20160161
theorem B1864911 : Blo 1863633 1864911 := bstep (se 1 (by rfl) ⟨1398683, by rfl⟩ : syracuseStep 1864911 = 2797367) B2797367
theorem B11949403 : Blo 1863633 11949403 := bstep (se 1 (by rfl) ⟨8962052, by rfl⟩ : syracuseStep 11949403 = 17924105) B17924105
theorem B1865115 : Blo 1863633 1865115 := bstep (se 1 (by rfl) ⟨1398836, by rfl⟩ : syracuseStep 1865115 = 2797673) B2797673
theorem B20166043 : Blo 1863633 20166043 := bstep (se 1 (by rfl) ⟨15124532, by rfl⟩ : syracuseStep 20166043 = 30249065) B30249065
theorem B5379527 : Blo 1863633 5379527 := bstep (se 1 (by rfl) ⟨4034645, by rfl⟩ : syracuseStep 5379527 = 8069291) B8069291
theorem B1865327 : Blo 1863633 1865327 := bstep (se 1 (by rfl) ⟨1398995, by rfl⟩ : syracuseStep 1865327 = 2797991) B2797991
theorem B1865383 : Blo 1863633 1865383 := bstep (se 1 (by rfl) ⟨1399037, by rfl⟩ : syracuseStep 1865383 = 2798075) B2798075
theorem B1865467 : Blo 1863633 1865467 := bstep (se 1 (by rfl) ⟨1399100, by rfl⟩ : syracuseStep 1865467 = 2798201) B2798201
theorem B1865503 : Blo 1863633 1865503 := bstep (se 1 (by rfl) ⟨1399127, by rfl⟩ : syracuseStep 1865503 = 2798255) B2798255
theorem B1865535 : Blo 1863633 1865535 := bstep (se 1 (by rfl) ⟨1399151, by rfl⟩ : syracuseStep 1865535 = 2798303) B2798303
theorem B12105577 : Blo 1863633 12105577 := bstep (se 2 (by rfl) ⟨4539591, by rfl⟩ : syracuseStep 12105577 = 9079183) B9079183
theorem B9443303 : Blo 1863633 9443303 := bstep (se 1 (by rfl) ⟨7082477, by rfl⟩ : syracuseStep 9443303 = 14164955) B14164955
theorem B4478959 : Blo 1863633 4478959 := bstep (se 1 (by rfl) ⟨3359219, by rfl⟩ : syracuseStep 4478959 = 6718439) B6718439
theorem B2988023 : Blo 1863633 2988023 := bstep (se 1 (by rfl) ⟨2241017, by rfl⟩ : syracuseStep 2988023 = 4482035) B4482035
theorem B4782235 : Blo 1863633 4782235 := bstep (se 1 (by rfl) ⟨3586676, by rfl⟩ : syracuseStep 4782235 = 7173353) B7173353
theorem B10615151 : Blo 1863633 10615151 := bstep (se 1 (by rfl) ⟨7961363, by rfl⟩ : syracuseStep 10615151 = 15922727) B15922727
theorem B86112715 : Blo 1863633 86112715 := bstep (se 1 (by rfl) ⟨64584536, by rfl⟩ : syracuseStep 86112715 = 129169073) B129169073
theorem B7559837 : Blo 1863633 7559837 := bstep (se 3 (by rfl) ⟨1417469, by rfl⟩ : syracuseStep 7559837 = 2834939) B2834939
theorem B349223669 : Blo 1863633 349223669 := bstep (se 5 (by rfl) ⟨16369859, by rfl⟩ : syracuseStep 349223669 = 32739719) B32739719
theorem B12278765 : Blo 1863633 12278765 := bstep (se 3 (by rfl) ⟨2302268, by rfl⟩ : syracuseStep 12278765 = 4604537) B4604537
theorem B5307383 : Blo 1863633 5307383 := bstep (se 1 (by rfl) ⟨3980537, by rfl⟩ : syracuseStep 5307383 = 7961075) B7961075
theorem B4193351 : Blo 1863633 4193351 := bstep (se 1 (by rfl) ⟨3145013, by rfl⟩ : syracuseStep 4193351 = 6290027) B6290027
theorem B44260499 : Blo 1863633 44260499 := bstep (se 1 (by rfl) ⟨33195374, by rfl⟩ : syracuseStep 44260499 = 66390749) B66390749
theorem B5971229 : Blo 1863633 5971229 := bstep (se 3 (by rfl) ⟨1119605, by rfl⟩ : syracuseStep 5971229 = 2239211) B2239211
theorem B6290783 : Blo 1863633 6290783 := bstep (se 1 (by rfl) ⟨4718087, by rfl⟩ : syracuseStep 6290783 = 9436175) B9436175
theorem B2833831 : Blo 1863633 2833831 := bstep (se 1 (by rfl) ⟨2125373, by rfl⟩ : syracuseStep 2833831 = 4250747) B4250747
theorem B4193747 : Blo 1863633 4193747 := bstep (se 1 (by rfl) ⟨3145310, by rfl⟩ : syracuseStep 4193747 = 6290621) B6290621
theorem B4718159 : Blo 1863633 4718159 := bstep (se 1 (by rfl) ⟨3538619, by rfl⟩ : syracuseStep 4718159 = 7077239) B7077239
theorem B3538657 : Blo 1863633 3538657 := bstep (se 2 (by rfl) ⟨1326996, by rfl⟩ : syracuseStep 3538657 = 2653993) B2653993
theorem B4194017 : Blo 1863633 4194017 := bstep (se 2 (by rfl) ⟨1572756, by rfl⟩ : syracuseStep 4194017 = 3145513) B3145513
theorem B5037815 : Blo 1863633 5037815 := bstep (se 1 (by rfl) ⟨3778361, by rfl⟩ : syracuseStep 5037815 = 7556723) B7556723
theorem B12754759 : Blo 1863633 12754759 := bstep (se 1 (by rfl) ⟨9566069, by rfl⟩ : syracuseStep 12754759 = 19132139) B19132139
theorem B6291323 : Blo 1863633 6291323 := bstep (se 1 (by rfl) ⟨4718492, by rfl⟩ : syracuseStep 6291323 = 9436985) B9436985
theorem B8503211 : Blo 1863633 8503211 := bstep (se 1 (by rfl) ⟨6377408, by rfl⟩ : syracuseStep 8503211 = 12754817) B12754817
theorem B30244913 : Blo 1863633 30244913 := bstep (se 2 (by rfl) ⟨11341842, by rfl⟩ : syracuseStep 30244913 = 22683685) B22683685
theorem B4194539 : Blo 1863633 4194539 := bstep (se 1 (by rfl) ⟨3145904, by rfl⟩ : syracuseStep 4194539 = 6291809) B6291809
theorem B9437471 : Blo 1863633 9437471 := bstep (se 1 (by rfl) ⟨7078103, by rfl⟩ : syracuseStep 9437471 = 14156207) B14156207
theorem B6054311 : Blo 1863633 6054311 := bstep (se 1 (by rfl) ⟨4540733, by rfl⟩ : syracuseStep 6054311 = 9081467) B9081467
theorem B4719019 : Blo 1863633 4719019 := bstep (se 1 (by rfl) ⟨3539264, by rfl⟩ : syracuseStep 4719019 = 7078529) B7078529
theorem B3539371 : Blo 1863633 3539371 := bstep (se 1 (by rfl) ⟨2654528, by rfl⟩ : syracuseStep 3539371 = 5309057) B5309057
theorem B5309023 : Blo 1863633 5309023 := bstep (se 1 (by rfl) ⟨3981767, by rfl⟩ : syracuseStep 5309023 = 7963535) B7963535
theorem B6292079 : Blo 1863633 6292079 := bstep (se 1 (by rfl) ⟨4719059, by rfl⟩ : syracuseStep 6292079 = 9438119) B9438119
theorem B23905003 : Blo 1863633 23905003 := bstep (se 1 (by rfl) ⟨17928752, by rfl⟩ : syracuseStep 23905003 = 35857505) B35857505
theorem B130892591 : Blo 1863633 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B17007479 : Blo 1863633 17007479 := bstep (se 1 (by rfl) ⟨12755609, by rfl⟩ : syracuseStep 17007479 = 25511219) B25511219
theorem B3539963 : Blo 1863633 3539963 := bstep (se 1 (by rfl) ⟨2654972, by rfl⟩ : syracuseStep 3539963 = 5309945) B5309945
theorem B3359855 : Blo 1863633 3359855 := bstep (se 1 (by rfl) ⟨2519891, by rfl⟩ : syracuseStep 3359855 = 5039783) B5039783
theorem B4195439 : Blo 1863633 4195439 := bstep (se 1 (by rfl) ⟨3146579, by rfl⟩ : syracuseStep 4195439 = 6293159) B6293159
theorem B3146863 : Blo 1863633 3146863 := bstep (se 1 (by rfl) ⟨2360147, by rfl⟩ : syracuseStep 3146863 = 4720295) B4720295
theorem B2360431 : Blo 1863633 2360431 := bstep (se 1 (by rfl) ⟨1770323, by rfl⟩ : syracuseStep 2360431 = 3540647) B3540647
theorem B10618067 : Blo 1863633 10618067 := bstep (se 1 (by rfl) ⟨7963550, by rfl⟩ : syracuseStep 10618067 = 15927101) B15927101
theorem B7963859 : Blo 1863633 7963859 := bstep (se 1 (by rfl) ⟨5972894, by rfl⟩ : syracuseStep 7963859 = 11945789) B11945789
theorem B2098399 : Blo 1863633 2098399 := bstep (se 1 (by rfl) ⟨1573799, by rfl⟩ : syracuseStep 2098399 = 3147599) B3147599
theorem B3540449 : Blo 1863633 3540449 := bstep (se 2 (by rfl) ⟨1327668, by rfl⟩ : syracuseStep 3540449 = 2655337) B2655337
theorem B4195835 : Blo 1863633 4195835 := bstep (se 1 (by rfl) ⟨3146876, by rfl⟩ : syracuseStep 4195835 = 6293753) B6293753
theorem B4195871 : Blo 1863633 4195871 := bstep (se 1 (by rfl) ⟨3146903, by rfl⟩ : syracuseStep 4195871 = 6293807) B6293807
theorem B3147295 : Blo 1863633 3147295 := bstep (se 1 (by rfl) ⟨2360471, by rfl⟩ : syracuseStep 3147295 = 4720943) B4720943
theorem B5310127 : Blo 1863633 5310127 := bstep (se 1 (by rfl) ⟨3982595, by rfl⟩ : syracuseStep 5310127 = 7965191) B7965191
theorem B4196015 : Blo 1863633 4196015 := bstep (se 1 (by rfl) ⟨3147011, by rfl⟩ : syracuseStep 4196015 = 6294023) B6294023
theorem B3983023 : Blo 1863633 3983023 := bstep (se 1 (by rfl) ⟨2987267, by rfl⟩ : syracuseStep 3983023 = 5974535) B5974535
theorem B5039891 : Blo 1863633 5039891 := bstep (se 1 (by rfl) ⟨3779918, by rfl⟩ : syracuseStep 5039891 = 7559837) B7559837
theorem B26888057 : Blo 1863633 26888057 := bstep (se 2 (by rfl) ⟨10083021, by rfl⟩ : syracuseStep 26888057 = 20166043) B20166043
theorem B64563077 : Blo 1863633 64563077 := bstep (se 4 (by rfl) ⟨6052788, by rfl⟩ : syracuseStep 64563077 = 12105577) B12105577
theorem B8185843 : Blo 1863633 8185843 := bstep (se 1 (by rfl) ⟨6139382, by rfl⟩ : syracuseStep 8185843 = 12278765) B12278765
theorem B2795567 : Blo 1863633 2795567 := bstep (se 1 (by rfl) ⟨2096675, by rfl⟩ : syracuseStep 2795567 = 4193351) B4193351
theorem B4196447 : Blo 1863633 4196447 := bstep (se 1 (by rfl) ⟨3147335, by rfl⟩ : syracuseStep 4196447 = 6294671) B6294671
theorem B3541087 : Blo 1863633 3541087 := bstep (se 1 (by rfl) ⟨2655815, by rfl⟩ : syracuseStep 3541087 = 5311631) B5311631
theorem B4720801 : Blo 1863633 4720801 := bstep (se 2 (by rfl) ⟨1770300, by rfl⟩ : syracuseStep 4720801 = 3540601) B3540601
theorem B2795831 : Blo 1863633 2795831 := bstep (se 1 (by rfl) ⟨2096873, by rfl⟩ : syracuseStep 2795831 = 4193747) B4193747
theorem B17918297 : Blo 1863633 17918297 := bstep (se 2 (by rfl) ⟨6719361, by rfl⟩ : syracuseStep 17918297 = 13438723) B13438723
theorem B4196735 : Blo 1863633 4196735 := bstep (se 1 (by rfl) ⟨3147551, by rfl⟩ : syracuseStep 4196735 = 6295103) B6295103
theorem B3148159 : Blo 1863633 3148159 := bstep (se 1 (by rfl) ⟨2361119, by rfl⟩ : syracuseStep 3148159 = 4722239) B4722239
theorem B2796011 : Blo 1863633 2796011 := bstep (se 1 (by rfl) ⟨2097008, by rfl⟩ : syracuseStep 2796011 = 4194017) B4194017
theorem B4197203 : Blo 1863633 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B18156383 : Blo 1863633 18156383 := bstep (se 1 (by rfl) ⟨13617287, by rfl⟩ : syracuseStep 18156383 = 27234575) B27234575
theorem B6376313 : Blo 1863633 6376313 := bstep (se 2 (by rfl) ⟨2391117, by rfl⟩ : syracuseStep 6376313 = 4782235) B4782235
theorem B2690111 : Blo 1863633 2690111 := bstep (se 1 (by rfl) ⟨2017583, by rfl⟩ : syracuseStep 2690111 = 4035167) B4035167
theorem B2796713 : Blo 1863633 2796713 := bstep (se 2 (by rfl) ⟨1048767, by rfl⟩ : syracuseStep 2796713 = 2097535) B2097535
theorem B4197563 : Blo 1863633 4197563 := bstep (se 1 (by rfl) ⟨3148172, by rfl⟩ : syracuseStep 4197563 = 6296345) B6296345
theorem B4722047 : Blo 1863633 4722047 := bstep (se 1 (by rfl) ⟨3541535, by rfl⟩ : syracuseStep 4722047 = 7083071) B7083071
theorem B2797127 : Blo 1863633 2797127 := bstep (se 1 (by rfl) ⟨2097845, by rfl⟩ : syracuseStep 2797127 = 4195691) B4195691
theorem B52407971 : Blo 1863633 52407971 := bstep (se 1 (by rfl) ⟨39305978, by rfl⟩ : syracuseStep 52407971 = 78611957) B78611957
theorem B2797307 : Blo 1863633 2797307 := bstep (se 1 (by rfl) ⟨2097980, by rfl⟩ : syracuseStep 2797307 = 4195961) B4195961
theorem B1863663 : Blo 1863633 1863663 := bstep (se 1 (by rfl) ⟨1397747, by rfl⟩ : syracuseStep 1863663 = 2795495) B2795495
theorem B6295535 : Blo 1863633 6295535 := bstep (se 1 (by rfl) ⟨4721651, by rfl⟩ : syracuseStep 6295535 = 9443303) B9443303
theorem B1863675 : Blo 1863633 1863675 := bstep (se 1 (by rfl) ⟨1397756, by rfl⟩ : syracuseStep 1863675 = 2795513) B2795513
theorem B1863743 : Blo 1863633 1863743 := bstep (se 1 (by rfl) ⟨1397807, by rfl⟩ : syracuseStep 1863743 = 2795615) B2795615
theorem B1863783 : Blo 1863633 1863783 := bstep (se 1 (by rfl) ⟨1397837, by rfl⟩ : syracuseStep 1863783 = 2795675) B2795675
theorem B1863807 : Blo 1863633 1863807 := bstep (se 1 (by rfl) ⟨1397855, by rfl⟩ : syracuseStep 1863807 = 2795711) B2795711
theorem B7082113 : Blo 1863633 7082113 := bstep (se 2 (by rfl) ⟨2655792, by rfl⟩ : syracuseStep 7082113 = 5311585) B5311585
theorem B1863835 : Blo 1863633 1863835 := bstep (se 1 (by rfl) ⟨1397876, by rfl⟩ : syracuseStep 1863835 = 2795753) B2795753
theorem B145363261 : Blo 1863633 145363261 := bstep (se 3 (by rfl) ⟨27255611, by rfl⟩ : syracuseStep 145363261 = 54511223) B54511223
theorem B1864039 : Blo 1863633 1864039 := bstep (se 1 (by rfl) ⟨1398029, by rfl⟩ : syracuseStep 1864039 = 2796059) B2796059
theorem B1864091 : Blo 1863633 1864091 := bstep (se 1 (by rfl) ⟨1398068, by rfl⟩ : syracuseStep 1864091 = 2796137) B2796137
theorem B2797979 : Blo 1863633 2797979 := bstep (se 1 (by rfl) ⟨2098484, by rfl⟩ : syracuseStep 2797979 = 4196969) B4196969
theorem B26874449 : Blo 1863633 26874449 := bstep (se 2 (by rfl) ⟨10077918, by rfl⟩ : syracuseStep 26874449 = 20155837) B20155837
theorem B1864443 : Blo 1863633 1864443 := bstep (se 1 (by rfl) ⟨1398332, by rfl⟩ : syracuseStep 1864443 = 2796665) B2796665
theorem B1864511 : Blo 1863633 1864511 := bstep (se 1 (by rfl) ⟨1398383, by rfl⟩ : syracuseStep 1864511 = 2796767) B2796767
theorem B2798399 : Blo 1863633 2798399 := bstep (se 1 (by rfl) ⟨2098799, by rfl⟩ : syracuseStep 2798399 = 4197599) B4197599
theorem B1864539 : Blo 1863633 1864539 := bstep (se 1 (by rfl) ⟨1398404, by rfl⟩ : syracuseStep 1864539 = 2796809) B2796809
theorem B1864607 : Blo 1863633 1864607 := bstep (se 1 (by rfl) ⟨1398455, by rfl⟩ : syracuseStep 1864607 = 2796911) B2796911
theorem B1864687 : Blo 1863633 1864687 := bstep (se 1 (by rfl) ⟨1398515, by rfl⟩ : syracuseStep 1864687 = 2797031) B2797031
theorem B18166787 : Blo 1863633 18166787 := bstep (se 1 (by rfl) ⟨13625090, by rfl⟩ : syracuseStep 18166787 = 27250181) B27250181
theorem B1864775 : Blo 1863633 1864775 := bstep (se 1 (by rfl) ⟨1398581, by rfl⟩ : syracuseStep 1864775 = 2797163) B2797163
theorem B1864859 : Blo 1863633 1864859 := bstep (se 1 (by rfl) ⟨1398644, by rfl⟩ : syracuseStep 1864859 = 2797289) B2797289
theorem B11949221 : Blo 1863633 11949221 := bstep (se 4 (by rfl) ⟨1120239, by rfl⟩ : syracuseStep 11949221 = 2240479) B2240479
theorem B9442493 : Blo 1863633 9442493 := bstep (se 3 (by rfl) ⟨1770467, by rfl⟩ : syracuseStep 9442493 = 3540935) B3540935
theorem B1864955 : Blo 1863633 1864955 := bstep (se 1 (by rfl) ⟨1398716, by rfl⟩ : syracuseStep 1864955 = 2797433) B2797433
theorem B14349575 : Blo 1863633 14349575 := bstep (se 1 (by rfl) ⟨10762181, by rfl⟩ : syracuseStep 14349575 = 21524363) B21524363
theorem B1865023 : Blo 1863633 1865023 := bstep (se 1 (by rfl) ⟨1398767, by rfl⟩ : syracuseStep 1865023 = 2797535) B2797535
theorem B7968061 : Blo 1863633 7968061 := bstep (se 3 (by rfl) ⟨1494011, by rfl⟩ : syracuseStep 7968061 = 2988023) B2988023
theorem B71685485 : Blo 1863633 71685485 := bstep (se 3 (by rfl) ⟨13441028, by rfl⟩ : syracuseStep 71685485 = 26882057) B26882057
theorem B1865191 : Blo 1863633 1865191 := bstep (se 1 (by rfl) ⟨1398893, by rfl⟩ : syracuseStep 1865191 = 2797787) B2797787
theorem B1865199 : Blo 1863633 1865199 := bstep (se 1 (by rfl) ⟨1398899, by rfl⟩ : syracuseStep 1865199 = 2797799) B2797799
theorem B1865307 : Blo 1863633 1865307 := bstep (se 1 (by rfl) ⟨1398980, by rfl⟩ : syracuseStep 1865307 = 2797961) B2797961
theorem B1865371 : Blo 1863633 1865371 := bstep (se 1 (by rfl) ⟨1399028, by rfl⟩ : syracuseStep 1865371 = 2798057) B2798057
theorem B1865455 : Blo 1863633 1865455 := bstep (se 1 (by rfl) ⟨1399091, by rfl⟩ : syracuseStep 1865455 = 2798183) B2798183
theorem B1865543 : Blo 1863633 1865543 := bstep (se 1 (by rfl) ⟨1399157, by rfl⟩ : syracuseStep 1865543 = 2798315) B2798315
theorem B1865563 : Blo 1863633 1865563 := bstep (se 1 (by rfl) ⟨1399172, by rfl⟩ : syracuseStep 1865563 = 2798345) B2798345
theorem B1865631 : Blo 1863633 1865631 := bstep (se 1 (by rfl) ⟨1399223, by rfl⟩ : syracuseStep 1865631 = 2798447) B2798447
theorem B102053803 : Blo 1863633 102053803 := bstep (se 1 (by rfl) ⟨76540352, by rfl⟩ : syracuseStep 102053803 = 153080705) B153080705
theorem B114816953 : Blo 1863633 114816953 := bstep (se 2 (by rfl) ⟨43056357, by rfl⟩ : syracuseStep 114816953 = 86112715) B86112715
theorem B8960071 : Blo 1863633 8960071 := bstep (se 1 (by rfl) ⟨6720053, by rfl⟩ : syracuseStep 8960071 = 13440107) B13440107
theorem B9443465 : Blo 1863633 9443465 := bstep (se 2 (by rfl) ⟨3541299, by rfl⟩ : syracuseStep 9443465 = 7082599) B7082599
theorem B4479191 : Blo 1863633 4479191 := bstep (se 1 (by rfl) ⟨3359393, by rfl⟩ : syracuseStep 4479191 = 6718787) B6718787
theorem B3586351 : Blo 1863633 3586351 := bstep (se 1 (by rfl) ⟨2689763, by rfl⟩ : syracuseStep 3586351 = 5379527) B5379527
theorem B16145095 : Blo 1863633 16145095 := bstep (se 1 (by rfl) ⟨12108821, by rfl⟩ : syracuseStep 16145095 = 24217643) B24217643
theorem B7076767 : Blo 1863633 7076767 := bstep (se 1 (by rfl) ⟨5307575, by rfl⟩ : syracuseStep 7076767 = 10615151) B10615151
theorem B15932537 : Blo 1863633 15932537 := bstep (se 2 (by rfl) ⟨5974701, by rfl⟩ : syracuseStep 15932537 = 11949403) B11949403
theorem B232815779 : Blo 1863633 232815779 := bstep (se 1 (by rfl) ⟨174611834, by rfl⟩ : syracuseStep 232815779 = 349223669) B349223669
theorem B13434173 : Blo 1863633 13434173 := bstep (se 3 (by rfl) ⟨2518907, by rfl⟩ : syracuseStep 13434173 = 5037815) B5037815
theorem B3538255 : Blo 1863633 3538255 := bstep (se 1 (by rfl) ⟨2653691, by rfl⟩ : syracuseStep 3538255 = 5307383) B5307383
theorem B29506999 : Blo 1863633 29506999 := bstep (se 1 (by rfl) ⟨22130249, by rfl⟩ : syracuseStep 29506999 = 44260499) B44260499
theorem B7560695 : Blo 1863633 7560695 := bstep (se 1 (by rfl) ⟨5670521, by rfl⟩ : syracuseStep 7560695 = 11341043) B11341043
theorem B3980819 : Blo 1863633 3980819 := bstep (se 1 (by rfl) ⟨2985614, by rfl⟩ : syracuseStep 3980819 = 5971229) B5971229
theorem B15113765 : Blo 1863633 15113765 := bstep (se 4 (by rfl) ⟨1416915, by rfl⟩ : syracuseStep 15113765 = 2833831) B2833831
theorem B4193855 : Blo 1863633 4193855 := bstep (se 1 (by rfl) ⟨3145391, by rfl⟩ : syracuseStep 4193855 = 6290783) B6290783
theorem B4718209 : Blo 1863633 4718209 := bstep (se 2 (by rfl) ⟨1769328, by rfl⟩ : syracuseStep 4718209 = 3538657) B3538657
theorem B3145439 : Blo 1863633 3145439 := bstep (se 1 (by rfl) ⟨2359079, by rfl⟩ : syracuseStep 3145439 = 4718159) B4718159
theorem B1990375 : Blo 1863633 1990375 := bstep (se 1 (by rfl) ⟨1492781, by rfl⟩ : syracuseStep 1990375 = 2985563) B2985563
theorem B17006345 : Blo 1863633 17006345 := bstep (se 2 (by rfl) ⟨6377379, by rfl⟩ : syracuseStep 17006345 = 12754759) B12754759
theorem B23887781 : Blo 1863633 23887781 := bstep (se 4 (by rfl) ⟨2239479, by rfl⟩ : syracuseStep 23887781 = 4478959) B4478959
theorem B4194215 : Blo 1863633 4194215 := bstep (se 1 (by rfl) ⟨3145661, by rfl⟩ : syracuseStep 4194215 = 6291323) B6291323
theorem B5668807 : Blo 1863633 5668807 := bstep (se 1 (by rfl) ⟨4251605, by rfl⟩ : syracuseStep 5668807 = 8503211) B8503211
theorem B6291647 : Blo 1863633 6291647 := bstep (se 1 (by rfl) ⟨4718735, by rfl⟩ : syracuseStep 6291647 = 9437471) B9437471
theorem B17916299 : Blo 1863633 17916299 := bstep (se 1 (by rfl) ⟨13437224, by rfl⟩ : syracuseStep 17916299 = 26874449) B26874449
theorem B4194719 : Blo 1863633 4194719 := bstep (se 1 (by rfl) ⟨3146039, by rfl⟩ : syracuseStep 4194719 = 6292079) B6292079
theorem B6292025 : Blo 1863633 6292025 := bstep (se 2 (by rfl) ⟨2359509, by rfl⟩ : syracuseStep 6292025 = 4719019) B4719019
theorem B4719161 : Blo 1863633 4719161 := bstep (se 2 (by rfl) ⟨1769685, by rfl⟩ : syracuseStep 4719161 = 3539371) B3539371
theorem B11338319 : Blo 1863633 11338319 := bstep (se 1 (by rfl) ⟨8503739, by rfl⟩ : syracuseStep 11338319 = 17007479) B17007479
theorem B7078697 : Blo 1863633 7078697 := bstep (se 2 (by rfl) ⟨2654511, by rfl⟩ : syracuseStep 7078697 = 5309023) B5309023
theorem B7078711 : Blo 1863633 7078711 := bstep (se 1 (by rfl) ⟨5309033, by rfl⟩ : syracuseStep 7078711 = 10618067) B10618067
theorem B5309239 : Blo 1863633 5309239 := bstep (se 1 (by rfl) ⟨3981929, by rfl⟩ : syracuseStep 5309239 = 7963859) B7963859
theorem B3359927 : Blo 1863633 3359927 := bstep (se 1 (by rfl) ⟨2519945, by rfl⟩ : syracuseStep 3359927 = 5039891) B5039891
theorem B17925371 : Blo 1863633 17925371 := bstep (se 1 (by rfl) ⟨13444028, by rfl⟩ : syracuseStep 17925371 = 26888057) B26888057
theorem B43042051 : Blo 1863633 43042051 := bstep (se 1 (by rfl) ⟨32281538, by rfl⟩ : syracuseStep 43042051 = 64563077) B64563077
theorem B4195817 : Blo 1863633 4195817 := bstep (se 2 (by rfl) ⟨1573431, by rfl⟩ : syracuseStep 4195817 = 3146863) B3146863
theorem B3147241 : Blo 1863633 3147241 := bstep (se 2 (by rfl) ⟨1180215, by rfl⟩ : syracuseStep 3147241 = 2360431) B2360431
theorem B11945531 : Blo 1863633 11945531 := bstep (se 1 (by rfl) ⟨8959148, by rfl⟩ : syracuseStep 11945531 = 17918297) B17918297
theorem B4196393 : Blo 1863633 4196393 := bstep (se 2 (by rfl) ⟨1573647, by rfl⟩ : syracuseStep 4196393 = 3147295) B3147295
theorem B349046909 : Blo 1863633 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B8956115 : Blo 1863633 8956115 := bstep (se 1 (by rfl) ⟨6717086, by rfl⟩ : syracuseStep 8956115 = 13434173) B13434173
theorem B7080169 : Blo 1863633 7080169 := bstep (se 2 (by rfl) ⟨2655063, by rfl⟩ : syracuseStep 7080169 = 5310127) B5310127
theorem B5310697 : Blo 1863633 5310697 := bstep (se 2 (by rfl) ⟨1991511, by rfl⟩ : syracuseStep 5310697 = 3983023) B3983023
theorem B3148031 : Blo 1863633 3148031 := bstep (se 1 (by rfl) ⟨2361023, by rfl⟩ : syracuseStep 3148031 = 4722047) B4722047
theorem B5040463 : Blo 1863633 5040463 := bstep (se 1 (by rfl) ⟨3780347, by rfl⟩ : syracuseStep 5040463 = 7560695) B7560695
theorem B2795903 : Blo 1863633 2795903 := bstep (se 1 (by rfl) ⟨2096927, by rfl⟩ : syracuseStep 2795903 = 4193855) B4193855
theorem B136071737 : Blo 1863633 136071737 := bstep (se 2 (by rfl) ⟨51026901, by rfl⟩ : syracuseStep 136071737 = 102053803) B102053803
theorem B43657829 : Blo 1863633 43657829 := bstep (se 4 (by rfl) ⟨4092921, by rfl⟩ : syracuseStep 43657829 = 8185843) B8185843
theorem B2796143 : Blo 1863633 2796143 := bstep (se 1 (by rfl) ⟨2097107, by rfl⟩ : syracuseStep 2796143 = 4194215) B4194215
theorem B9439901 : Blo 1863633 9439901 := bstep (se 3 (by rfl) ⟨1769981, by rfl⟩ : syracuseStep 9439901 = 3539963) B3539963
theorem B4197023 : Blo 1863633 4197023 := bstep (se 1 (by rfl) ⟨3147767, by rfl⟩ : syracuseStep 4197023 = 6295535) B6295535
theorem B20163275 : Blo 1863633 20163275 := bstep (se 1 (by rfl) ⟨15122456, by rfl⟩ : syracuseStep 20163275 = 30244913) B30244913
theorem B11946761 : Blo 1863633 11946761 := bstep (se 2 (by rfl) ⟨4480035, by rfl⟩ : syracuseStep 11946761 = 8960071) B8960071
theorem B4721449 : Blo 1863633 4721449 := bstep (se 2 (by rfl) ⟨1770543, by rfl⟩ : syracuseStep 4721449 = 3541087) B3541087
theorem B2796359 : Blo 1863633 2796359 := bstep (se 1 (by rfl) ⟨2097269, by rfl⟩ : syracuseStep 2796359 = 4194539) B4194539
theorem B6294401 : Blo 1863633 6294401 := bstep (se 2 (by rfl) ⟨2360400, by rfl⟩ : syracuseStep 6294401 = 4720801) B4720801
theorem B193817681 : Blo 1863633 193817681 := bstep (se 2 (by rfl) ⟨72681630, by rfl⟩ : syracuseStep 193817681 = 145363261) B145363261
theorem B4197545 : Blo 1863633 4197545 := bstep (se 2 (by rfl) ⟨1574079, by rfl⟩ : syracuseStep 4197545 = 3148159) B3148159
theorem B12111191 : Blo 1863633 12111191 := bstep (se 1 (by rfl) ⟨9083393, by rfl⟩ : syracuseStep 12111191 = 18166787) B18166787
theorem B2239903 : Blo 1863633 2239903 := bstep (se 1 (by rfl) ⟨1679927, by rfl⟩ : syracuseStep 2239903 = 3359855) B3359855
theorem B2796959 : Blo 1863633 2796959 := bstep (se 1 (by rfl) ⟨2097719, by rfl⟩ : syracuseStep 2796959 = 4195439) B4195439
theorem B6294995 : Blo 1863633 6294995 := bstep (se 1 (by rfl) ⟨4721246, by rfl⟩ : syracuseStep 6294995 = 9442493) B9442493
theorem B76508821 : Blo 1863633 76508821 := bstep (se 6 (by rfl) ⟨1793175, by rfl⟩ : syracuseStep 76508821 = 3586351) B3586351
theorem B2797223 : Blo 1863633 2797223 := bstep (se 1 (by rfl) ⟨2097917, by rfl⟩ : syracuseStep 2797223 = 4195835) B4195835
theorem B2797247 : Blo 1863633 2797247 := bstep (se 1 (by rfl) ⟨2097935, by rfl⟩ : syracuseStep 2797247 = 4195871) B4195871
theorem B2797343 : Blo 1863633 2797343 := bstep (se 1 (by rfl) ⟨2098007, by rfl⟩ : syracuseStep 2797343 = 4196015) B4196015
theorem B9441197 : Blo 1863633 9441197 := bstep (se 3 (by rfl) ⟨1770224, by rfl⟩ : syracuseStep 9441197 = 3540449) B3540449
theorem B1863711 : Blo 1863633 1863711 := bstep (se 1 (by rfl) ⟨1397783, by rfl⟩ : syracuseStep 1863711 = 2795567) B2795567
theorem B2797631 : Blo 1863633 2797631 := bstep (se 1 (by rfl) ⟨2098223, by rfl⟩ : syracuseStep 2797631 = 4196447) B4196447
theorem B6295643 : Blo 1863633 6295643 := bstep (se 1 (by rfl) ⟨4721732, by rfl⟩ : syracuseStep 6295643 = 9443465) B9443465
theorem B2986127 : Blo 1863633 2986127 := bstep (se 1 (by rfl) ⟨2239595, by rfl⟩ : syracuseStep 2986127 = 4479191) B4479191
theorem B1863887 : Blo 1863633 1863887 := bstep (se 1 (by rfl) ⟨1397915, by rfl⟩ : syracuseStep 1863887 = 2795831) B2795831
theorem B2797823 : Blo 1863633 2797823 := bstep (se 1 (by rfl) ⟨2098367, by rfl⟩ : syracuseStep 2797823 = 4196735) B4196735
theorem B2797865 : Blo 1863633 2797865 := bstep (se 2 (by rfl) ⟨1049199, by rfl⟩ : syracuseStep 2797865 = 2098399) B2098399
theorem B1864007 : Blo 1863633 1864007 := bstep (se 1 (by rfl) ⟨1398005, by rfl⟩ : syracuseStep 1864007 = 2796011) B2796011
theorem B2798135 : Blo 1863633 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B12104255 : Blo 1863633 12104255 := bstep (se 1 (by rfl) ⟨9078191, by rfl⟩ : syracuseStep 12104255 = 18156383) B18156383
theorem B39342665 : Blo 1863633 39342665 := bstep (se 2 (by rfl) ⟨14753499, by rfl⟩ : syracuseStep 39342665 = 29506999) B29506999
theorem B10621691 : Blo 1863633 10621691 := bstep (se 1 (by rfl) ⟨7966268, by rfl⟩ : syracuseStep 10621691 = 15932537) B15932537
theorem B155210519 : Blo 1863633 155210519 := bstep (se 1 (by rfl) ⟨116407889, by rfl⟩ : syracuseStep 155210519 = 232815779) B232815779
theorem B1864475 : Blo 1863633 1864475 := bstep (se 1 (by rfl) ⟨1398356, by rfl⟩ : syracuseStep 1864475 = 2796713) B2796713
theorem B2798375 : Blo 1863633 2798375 := bstep (se 1 (by rfl) ⟨2098781, by rfl⟩ : syracuseStep 2798375 = 4197563) B4197563
theorem B1864751 : Blo 1863633 1864751 := bstep (se 1 (by rfl) ⟨1398563, by rfl⟩ : syracuseStep 1864751 = 2797127) B2797127
theorem B1864871 : Blo 1863633 1864871 := bstep (se 1 (by rfl) ⟨1398653, by rfl⟩ : syracuseStep 1864871 = 2797307) B2797307
theorem B7558409 : Blo 1863633 7558409 := bstep (se 2 (by rfl) ⟨2834403, by rfl⟩ : syracuseStep 7558409 = 5668807) B5668807
theorem B7173629 : Blo 1863633 7173629 := bstep (se 3 (by rfl) ⟨1345055, by rfl⟩ : syracuseStep 7173629 = 2690111) B2690111
theorem B9442817 : Blo 1863633 9442817 := bstep (se 2 (by rfl) ⟨3541056, by rfl⟩ : syracuseStep 9442817 = 7082113) B7082113
theorem B1865319 : Blo 1863633 1865319 := bstep (se 1 (by rfl) ⟨1398989, by rfl⟩ : syracuseStep 1865319 = 2797979) B2797979
theorem B31864589 : Blo 1863633 31864589 := bstep (se 3 (by rfl) ⟨5974610, by rfl⟩ : syracuseStep 31864589 = 11949221) B11949221
theorem B1865599 : Blo 1863633 1865599 := bstep (se 1 (by rfl) ⟨1399199, by rfl⟩ : syracuseStep 1865599 = 2798399) B2798399
theorem B9566383 : Blo 1863633 9566383 := bstep (se 1 (by rfl) ⟨7174787, by rfl⟩ : syracuseStep 9566383 = 14349575) B14349575
theorem B47790323 : Blo 1863633 47790323 := bstep (se 1 (by rfl) ⟨35842742, by rfl⟩ : syracuseStep 47790323 = 71685485) B71685485
theorem B21526793 : Blo 1863633 21526793 := bstep (se 2 (by rfl) ⟨8072547, by rfl⟩ : syracuseStep 21526793 = 16145095) B16145095
theorem B31873337 : Blo 1863633 31873337 := bstep (se 2 (by rfl) ⟨11952501, by rfl⟩ : syracuseStep 31873337 = 23905003) B23905003
theorem B16144829 : Blo 1863633 16144829 := bstep (se 3 (by rfl) ⟨3027155, by rfl⟩ : syracuseStep 16144829 = 6054311) B6054311
theorem B10615333 : Blo 1863633 10615333 := bstep (se 4 (by rfl) ⟨995187, by rfl⟩ : syracuseStep 10615333 = 1990375) B1990375
theorem B9435689 : Blo 1863633 9435689 := bstep (se 2 (by rfl) ⟨3538383, by rfl⟩ : syracuseStep 9435689 = 7076767) B7076767
theorem B76544635 : Blo 1863633 76544635 := bstep (se 1 (by rfl) ⟨57408476, by rfl⟩ : syracuseStep 76544635 = 114816953) B114816953
theorem B10624081 : Blo 1863633 10624081 := bstep (se 2 (by rfl) ⟨3984030, by rfl⟩ : syracuseStep 10624081 = 7968061) B7968061
theorem B4717673 : Blo 1863633 4717673 := bstep (se 2 (by rfl) ⟨1769127, by rfl⟩ : syracuseStep 4717673 = 3538255) B3538255
theorem B4250875 : Blo 1863633 4250875 := bstep (se 1 (by rfl) ⟨3188156, by rfl⟩ : syracuseStep 4250875 = 6376313) B6376313
theorem B6290945 : Blo 1863633 6290945 := bstep (se 2 (by rfl) ⟨2359104, by rfl⟩ : syracuseStep 6290945 = 4718209) B4718209
theorem B2653879 : Blo 1863633 2653879 := bstep (se 1 (by rfl) ⟨1990409, by rfl⟩ : syracuseStep 2653879 = 3980819) B3980819
theorem B10075843 : Blo 1863633 10075843 := bstep (se 1 (by rfl) ⟨7556882, by rfl⟩ : syracuseStep 10075843 = 15113765) B15113765
theorem B34938647 : Blo 1863633 34938647 := bstep (se 1 (by rfl) ⟨26203985, by rfl⟩ : syracuseStep 34938647 = 52407971) B52407971
theorem B2096959 : Blo 1863633 2096959 := bstep (se 1 (by rfl) ⟨1572719, by rfl⟩ : syracuseStep 2096959 = 3145439) B3145439
theorem B11337563 : Blo 1863633 11337563 := bstep (se 1 (by rfl) ⟨8503172, by rfl⟩ : syracuseStep 11337563 = 17006345) B17006345
theorem B15925187 : Blo 1863633 15925187 := bstep (se 1 (by rfl) ⟨11943890, by rfl⟩ : syracuseStep 15925187 = 23887781) B23887781
theorem B1990751 : Blo 1863633 1990751 := bstep (se 1 (by rfl) ⟨1493063, by rfl⟩ : syracuseStep 1990751 = 2986127) B2986127
theorem B4194431 : Blo 1863633 4194431 := bstep (se 1 (by rfl) ⟨3145823, by rfl⟩ : syracuseStep 4194431 = 6291647) B6291647
theorem B12755177 : Blo 1863633 12755177 := bstep (se 2 (by rfl) ⟨4783191, by rfl⟩ : syracuseStep 12755177 = 9566383) B9566383
theorem B11944199 : Blo 1863633 11944199 := bstep (se 1 (by rfl) ⟨8958149, by rfl⟩ : syracuseStep 11944199 = 17916299) B17916299
theorem B4194683 : Blo 1863633 4194683 := bstep (se 1 (by rfl) ⟨3146012, by rfl⟩ : syracuseStep 4194683 = 6292025) B6292025
theorem B3146107 : Blo 1863633 3146107 := bstep (se 1 (by rfl) ⟨2359580, by rfl⟩ : syracuseStep 3146107 = 4719161) B4719161
theorem B8069503 : Blo 1863633 8069503 := bstep (se 1 (by rfl) ⟨6052127, by rfl⟩ : syracuseStep 8069503 = 12104255) B12104255
theorem B4719131 : Blo 1863633 4719131 := bstep (se 1 (by rfl) ⟨3539348, by rfl⟩ : syracuseStep 4719131 = 7078697) B7078697
theorem B5038939 : Blo 1863633 5038939 := bstep (se 1 (by rfl) ⟨3779204, by rfl⟩ : syracuseStep 5038939 = 7558409) B7558409
theorem B7963687 : Blo 1863633 7963687 := bstep (se 1 (by rfl) ⟨5972765, by rfl⟩ : syracuseStep 7963687 = 11945531) B11945531
theorem B9438281 : Blo 1863633 9438281 := bstep (se 2 (by rfl) ⟨3539355, by rfl⟩ : syracuseStep 9438281 = 7078711) B7078711
theorem B7078985 : Blo 1863633 7078985 := bstep (se 2 (by rfl) ⟨2654619, by rfl⟩ : syracuseStep 7078985 = 5309239) B5309239
theorem B21243059 : Blo 1863633 21243059 := bstep (se 1 (by rfl) ⟨15932294, by rfl⟩ : syracuseStep 21243059 = 31864589) B31864589
theorem B14165441 : Blo 1863633 14165441 := bstep (se 2 (by rfl) ⟨5312040, by rfl⟩ : syracuseStep 14165441 = 10624081) B10624081
theorem B31860215 : Blo 1863633 31860215 := bstep (se 1 (by rfl) ⟨23895161, by rfl⟩ : syracuseStep 31860215 = 47790323) B47790323
theorem B2098687 : Blo 1863633 2098687 := bstep (se 1 (by rfl) ⟨1574015, by rfl⟩ : syracuseStep 2098687 = 3148031) B3148031
theorem B6293267 : Blo 1863633 6293267 := bstep (se 1 (by rfl) ⟨4719950, by rfl⟩ : syracuseStep 6293267 = 9439901) B9439901
theorem B7964507 : Blo 1863633 7964507 := bstep (se 1 (by rfl) ⟨5973380, by rfl⟩ : syracuseStep 7964507 = 11946761) B11946761
theorem B4196267 : Blo 1863633 4196267 := bstep (se 1 (by rfl) ⟨3147200, by rfl⟩ : syracuseStep 4196267 = 6294401) B6294401
theorem B4196321 : Blo 1863633 4196321 := bstep (se 2 (by rfl) ⟨1573620, by rfl⟩ : syracuseStep 4196321 = 3147241) B3147241
theorem B413894717 : Blo 1863633 413894717 := bstep (se 3 (by rfl) ⟨77605259, by rfl⟩ : syracuseStep 413894717 = 155210519) B155210519
theorem B4196663 : Blo 1863633 4196663 := bstep (se 1 (by rfl) ⟨3147497, by rfl⟩ : syracuseStep 4196663 = 6294995) B6294995
theorem B2795945 : Blo 1863633 2795945 := bstep (se 2 (by rfl) ⟨1048479, by rfl⟩ : syracuseStep 2795945 = 2096959) B2096959
theorem B23292431 : Blo 1863633 23292431 := bstep (se 1 (by rfl) ⟨17469323, by rfl⟩ : syracuseStep 23292431 = 34938647) B34938647
theorem B6294131 : Blo 1863633 6294131 := bstep (se 1 (by rfl) ⟨4720598, by rfl⟩ : syracuseStep 6294131 = 9441197) B9441197
theorem B4197095 : Blo 1863633 4197095 := bstep (se 1 (by rfl) ⟨3147821, by rfl⟩ : syracuseStep 4197095 = 6295643) B6295643
theorem B2796479 : Blo 1863633 2796479 := bstep (se 1 (by rfl) ⟨2097359, by rfl⟩ : syracuseStep 2796479 = 4194719) B4194719
theorem B9440225 : Blo 1863633 9440225 := bstep (se 2 (by rfl) ⟨3540084, by rfl⟩ : syracuseStep 9440225 = 7080169) B7080169
theorem B7080929 : Blo 1863633 7080929 := bstep (se 2 (by rfl) ⟨2655348, by rfl⟩ : syracuseStep 7080929 = 5310697) B5310697
theorem B6720617 : Blo 1863633 6720617 := bstep (se 2 (by rfl) ⟨2520231, by rfl⟩ : syracuseStep 6720617 = 5040463) B5040463
theorem B7081127 : Blo 1863633 7081127 := bstep (se 1 (by rfl) ⟨5310845, by rfl⟩ : syracuseStep 7081127 = 10621691) B10621691
theorem B102059513 : Blo 1863633 102059513 := bstep (se 2 (by rfl) ⟨38272317, by rfl⟩ : syracuseStep 102059513 = 76544635) B76544635
theorem B2797211 : Blo 1863633 2797211 := bstep (se 1 (by rfl) ⟨2097908, by rfl⟩ : syracuseStep 2797211 = 4195817) B4195817
theorem B6295211 : Blo 1863633 6295211 := bstep (se 1 (by rfl) ⟨4721408, by rfl⟩ : syracuseStep 6295211 = 9442817) B9442817
theorem B6295265 : Blo 1863633 6295265 := bstep (se 2 (by rfl) ⟨2360724, by rfl⟩ : syracuseStep 6295265 = 4721449) B4721449
theorem B2797595 : Blo 1863633 2797595 := bstep (se 1 (by rfl) ⟨2098196, by rfl⟩ : syracuseStep 2797595 = 4196393) B4196393
theorem B232697939 : Blo 1863633 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B1863935 : Blo 1863633 1863935 := bstep (se 1 (by rfl) ⟨1397951, by rfl⟩ : syracuseStep 1863935 = 2795903) B2795903
theorem B57389401 : Blo 1863633 57389401 := bstep (se 2 (by rfl) ⟨21521025, by rfl⟩ : syracuseStep 57389401 = 43042051) B43042051
theorem B90714491 : Blo 1863633 90714491 := bstep (se 1 (by rfl) ⟨68035868, by rfl⟩ : syracuseStep 90714491 = 136071737) B136071737
theorem B1864095 : Blo 1863633 1864095 := bstep (se 1 (by rfl) ⟨1398071, by rfl⟩ : syracuseStep 1864095 = 2796143) B2796143
theorem B2798015 : Blo 1863633 2798015 := bstep (se 1 (by rfl) ⟨2098511, by rfl⟩ : syracuseStep 2798015 = 4197023) B4197023
theorem B2986537 : Blo 1863633 2986537 := bstep (se 2 (by rfl) ⟨1119951, by rfl⟩ : syracuseStep 2986537 = 2239903) B2239903
theorem B1864239 : Blo 1863633 1864239 := bstep (se 1 (by rfl) ⟨1398179, by rfl⟩ : syracuseStep 1864239 = 2796359) B2796359
theorem B2798363 : Blo 1863633 2798363 := bstep (se 1 (by rfl) ⟨2098772, by rfl⟩ : syracuseStep 2798363 = 4197545) B4197545
theorem B102011761 : Blo 1863633 102011761 := bstep (se 2 (by rfl) ⟨38254410, by rfl⟩ : syracuseStep 102011761 = 76508821) B76508821
theorem B8074127 : Blo 1863633 8074127 := bstep (se 1 (by rfl) ⟨6055595, by rfl⟩ : syracuseStep 8074127 = 12111191) B12111191
theorem B1864639 : Blo 1863633 1864639 := bstep (se 1 (by rfl) ⟨1398479, by rfl⟩ : syracuseStep 1864639 = 2796959) B2796959
theorem B1864815 : Blo 1863633 1864815 := bstep (se 1 (by rfl) ⟨1398611, by rfl⟩ : syracuseStep 1864815 = 2797223) B2797223
theorem B1864831 : Blo 1863633 1864831 := bstep (se 1 (by rfl) ⟨1398623, by rfl⟩ : syracuseStep 1864831 = 2797247) B2797247
theorem B1864895 : Blo 1863633 1864895 := bstep (se 1 (by rfl) ⟨1398671, by rfl⟩ : syracuseStep 1864895 = 2797343) B2797343
theorem B7558375 : Blo 1863633 7558375 := bstep (se 1 (by rfl) ⟨5668781, by rfl⟩ : syracuseStep 7558375 = 11337563) B11337563
theorem B1865087 : Blo 1863633 1865087 := bstep (se 1 (by rfl) ⟨1398815, by rfl⟩ : syracuseStep 1865087 = 2797631) B2797631
theorem B1865215 : Blo 1863633 1865215 := bstep (se 1 (by rfl) ⟨1398911, by rfl⟩ : syracuseStep 1865215 = 2797823) B2797823
theorem B1865243 : Blo 1863633 1865243 := bstep (se 1 (by rfl) ⟨1398932, by rfl⟩ : syracuseStep 1865243 = 2797865) B2797865
theorem B1865423 : Blo 1863633 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B8959805 : Blo 1863633 8959805 := bstep (se 3 (by rfl) ⟨1679963, by rfl⟩ : syracuseStep 8959805 = 3359927) B3359927
theorem B1865583 : Blo 1863633 1865583 := bstep (se 1 (by rfl) ⟨1399187, by rfl⟩ : syracuseStep 1865583 = 2798375) B2798375
theorem B14153777 : Blo 1863633 14153777 := bstep (se 2 (by rfl) ⟨5307666, by rfl⟩ : syracuseStep 14153777 = 10615333) B10615333
theorem B11950247 : Blo 1863633 11950247 := bstep (se 1 (by rfl) ⟨8962685, by rfl⟩ : syracuseStep 11950247 = 17925371) B17925371
theorem B4782419 : Blo 1863633 4782419 := bstep (se 1 (by rfl) ⟨3586814, by rfl⟩ : syracuseStep 4782419 = 7173629) B7173629
theorem B5970743 : Blo 1863633 5970743 := bstep (se 1 (by rfl) ⟨4478057, by rfl⟩ : syracuseStep 5970743 = 8956115) B8956115
theorem B14351195 : Blo 1863633 14351195 := bstep (se 1 (by rfl) ⟨10763396, by rfl⟩ : syracuseStep 14351195 = 21526793) B21526793
theorem B104913773 : Blo 1863633 104913773 := bstep (se 3 (by rfl) ⟨19671332, by rfl⟩ : syracuseStep 104913773 = 39342665) B39342665
theorem B21248891 : Blo 1863633 21248891 := bstep (se 1 (by rfl) ⟨15936668, by rfl⟩ : syracuseStep 21248891 = 31873337) B31873337
theorem B30235517 : Blo 1863633 30235517 := bstep (se 3 (by rfl) ⟨5669159, by rfl⟩ : syracuseStep 30235517 = 11338319) B11338319
theorem B10763219 : Blo 1863633 10763219 := bstep (se 1 (by rfl) ⟨8072414, by rfl⟩ : syracuseStep 10763219 = 16144829) B16144829
theorem B5667833 : Blo 1863633 5667833 := bstep (se 2 (by rfl) ⟨2125437, by rfl⟩ : syracuseStep 5667833 = 4250875) B4250875
theorem B6290459 : Blo 1863633 6290459 := bstep (se 1 (by rfl) ⟨4717844, by rfl⟩ : syracuseStep 6290459 = 9435689) B9435689
theorem B29105219 : Blo 1863633 29105219 := bstep (se 1 (by rfl) ⟨21828914, by rfl⟩ : syracuseStep 29105219 = 43657829) B43657829
theorem B13442183 : Blo 1863633 13442183 := bstep (se 1 (by rfl) ⟨10081637, by rfl⟩ : syracuseStep 13442183 = 20163275) B20163275
theorem B129211787 : Blo 1863633 129211787 := bstep (se 1 (by rfl) ⟨96908840, by rfl⟩ : syracuseStep 129211787 = 193817681) B193817681
theorem B3145115 : Blo 1863633 3145115 := bstep (se 1 (by rfl) ⟨2358836, by rfl⟩ : syracuseStep 3145115 = 4717673) B4717673
theorem B3538505 : Blo 1863633 3538505 := bstep (se 2 (by rfl) ⟨1326939, by rfl⟩ : syracuseStep 3538505 = 2653879) B2653879
theorem B13434457 : Blo 1863633 13434457 := bstep (se 2 (by rfl) ⟨5037921, by rfl⟩ : syracuseStep 13434457 = 10075843) B10075843
theorem B4193963 : Blo 1863633 4193963 := bstep (se 1 (by rfl) ⟨3145472, by rfl⟩ : syracuseStep 4193963 = 6290945) B6290945
theorem B10616791 : Blo 1863633 10616791 := bstep (se 1 (by rfl) ⟨7962593, by rfl⟩ : syracuseStep 10616791 = 15925187) B15925187
theorem B8503451 : Blo 1863633 8503451 := bstep (se 1 (by rfl) ⟨6377588, by rfl⟩ : syracuseStep 8503451 = 12755177) B12755177
theorem B7962799 : Blo 1863633 7962799 := bstep (se 1 (by rfl) ⟨5972099, by rfl⟩ : syracuseStep 7962799 = 11944199) B11944199
theorem B620527837 : Blo 1863633 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B5308669 : Blo 1863633 5308669 := bstep (se 3 (by rfl) ⟨995375, by rfl⟩ : syracuseStep 5308669 = 1990751) B1990751
theorem B3146087 : Blo 1863633 3146087 := bstep (se 1 (by rfl) ⟨2359565, by rfl⟩ : syracuseStep 3146087 = 4719131) B4719131
theorem B4194809 : Blo 1863633 4194809 := bstep (se 2 (by rfl) ⟨1573053, by rfl⟩ : syracuseStep 4194809 = 3146107) B3146107
theorem B6292187 : Blo 1863633 6292187 := bstep (se 1 (by rfl) ⟨4719140, by rfl⟩ : syracuseStep 6292187 = 9438281) B9438281
theorem B4719323 : Blo 1863633 4719323 := bstep (se 1 (by rfl) ⟨3539492, by rfl⟩ : syracuseStep 4719323 = 7078985) B7078985
theorem B3982049 : Blo 1863633 3982049 := bstep (se 2 (by rfl) ⟨1493268, by rfl⟩ : syracuseStep 3982049 = 2986537) B2986537
theorem B6718585 : Blo 1863633 6718585 := bstep (se 2 (by rfl) ⟨2519469, by rfl⟩ : syracuseStep 6718585 = 5038939) B5038939
theorem B4195511 : Blo 1863633 4195511 := bstep (se 1 (by rfl) ⟨3146633, by rfl⟩ : syracuseStep 4195511 = 6293267) B6293267
theorem B5973203 : Blo 1863633 5973203 := bstep (se 1 (by rfl) ⟨4479902, by rfl⟩ : syracuseStep 5973203 = 8959805) B8959805
theorem B10618249 : Blo 1863633 10618249 := bstep (se 2 (by rfl) ⟨3981843, by rfl⟩ : syracuseStep 10618249 = 7963687) B7963687
theorem B3188279 : Blo 1863633 3188279 := bstep (se 1 (by rfl) ⟨2391209, by rfl⟩ : syracuseStep 3188279 = 4782419) B4782419
theorem B10077833 : Blo 1863633 10077833 := bstep (se 2 (by rfl) ⟨3779187, by rfl⟩ : syracuseStep 10077833 = 7558375) B7558375
theorem B4196087 : Blo 1863633 4196087 := bstep (se 1 (by rfl) ⟨3147065, by rfl⟩ : syracuseStep 4196087 = 6294131) B6294131
theorem B14165927 : Blo 1863633 14165927 := bstep (se 1 (by rfl) ⟨10624445, by rfl⟩ : syracuseStep 14165927 = 21248891) B21248891
theorem B6293483 : Blo 1863633 6293483 := bstep (se 1 (by rfl) ⟨4720112, by rfl⟩ : syracuseStep 6293483 = 9440225) B9440225
theorem B4720619 : Blo 1863633 4720619 := bstep (se 1 (by rfl) ⟨3540464, by rfl⟩ : syracuseStep 4720619 = 7080929) B7080929
theorem B4720751 : Blo 1863633 4720751 := bstep (se 1 (by rfl) ⟨3540563, by rfl⟩ : syracuseStep 4720751 = 7081127) B7081127
theorem B86141191 : Blo 1863633 86141191 := bstep (se 1 (by rfl) ⟨64605893, by rfl⟩ : syracuseStep 86141191 = 129211787) B129211787
theorem B21531005 : Blo 1863633 21531005 := bstep (se 3 (by rfl) ⟨4037063, by rfl⟩ : syracuseStep 21531005 = 8074127) B8074127
theorem B2795975 : Blo 1863633 2795975 := bstep (se 1 (by rfl) ⟨2096981, by rfl⟩ : syracuseStep 2795975 = 4193963) B4193963
theorem B4196807 : Blo 1863633 4196807 := bstep (se 1 (by rfl) ⟨3147605, by rfl⟩ : syracuseStep 4196807 = 6295211) B6295211
theorem B4196843 : Blo 1863633 4196843 := bstep (se 1 (by rfl) ⟨3147632, by rfl⟩ : syracuseStep 4196843 = 6295265) B6295265
theorem B2796287 : Blo 1863633 2796287 := bstep (se 1 (by rfl) ⟨2097215, by rfl⟩ : syracuseStep 2796287 = 4194431) B4194431
theorem B2796455 : Blo 1863633 2796455 := bstep (se 1 (by rfl) ⟨2097341, by rfl⟩ : syracuseStep 2796455 = 4194683) B4194683
theorem B60476327 : Blo 1863633 60476327 := bstep (se 1 (by rfl) ⟨45357245, by rfl⟩ : syracuseStep 60476327 = 90714491) B90714491
theorem B10759337 : Blo 1863633 10759337 := bstep (se 2 (by rfl) ⟨4034751, by rfl⟩ : syracuseStep 10759337 = 8069503) B8069503
theorem B136015681 : Blo 1863633 136015681 := bstep (se 2 (by rfl) ⟨51005880, by rfl⟩ : syracuseStep 136015681 = 102011761) B102011761
theorem B2797511 : Blo 1863633 2797511 := bstep (se 1 (by rfl) ⟨2098133, by rfl⟩ : syracuseStep 2797511 = 4196267) B4196267
theorem B2797547 : Blo 1863633 2797547 := bstep (se 1 (by rfl) ⟨2098160, by rfl⟩ : syracuseStep 2797547 = 4196321) B4196321
theorem B7966831 : Blo 1863633 7966831 := bstep (se 1 (by rfl) ⟨5975123, by rfl⟩ : syracuseStep 7966831 = 11950247) B11950247
theorem B2797775 : Blo 1863633 2797775 := bstep (se 1 (by rfl) ⟨2098331, by rfl⟩ : syracuseStep 2797775 = 4196663) B4196663
theorem B1863963 : Blo 1863633 1863963 := bstep (se 1 (by rfl) ⟨1397972, by rfl⟩ : syracuseStep 1863963 = 2795945) B2795945
theorem B15528287 : Blo 1863633 15528287 := bstep (se 1 (by rfl) ⟨11646215, by rfl⟩ : syracuseStep 15528287 = 23292431) B23292431
theorem B2798063 : Blo 1863633 2798063 := bstep (se 1 (by rfl) ⟨2098547, by rfl⟩ : syracuseStep 2798063 = 4197095) B4197095
theorem B20157011 : Blo 1863633 20157011 := bstep (se 1 (by rfl) ⟨15117758, by rfl⟩ : syracuseStep 20157011 = 30235517) B30235517
theorem B1864319 : Blo 1863633 1864319 := bstep (se 1 (by rfl) ⟨1398239, by rfl⟩ : syracuseStep 1864319 = 2796479) B2796479
theorem B2798249 : Blo 1863633 2798249 := bstep (se 2 (by rfl) ⟨1049343, by rfl⟩ : syracuseStep 2798249 = 2098687) B2098687
theorem B19403479 : Blo 1863633 19403479 := bstep (se 1 (by rfl) ⟨14552609, by rfl⟩ : syracuseStep 19403479 = 29105219) B29105219
theorem B17912609 : Blo 1863633 17912609 := bstep (se 2 (by rfl) ⟨6717228, by rfl⟩ : syracuseStep 17912609 = 13434457) B13434457
theorem B38269853 : Blo 1863633 38269853 := bstep (se 3 (by rfl) ⟨7175597, by rfl⟩ : syracuseStep 38269853 = 14351195) B14351195
theorem B21238685 : Blo 1863633 21238685 := bstep (se 3 (by rfl) ⟨3982253, by rfl⟩ : syracuseStep 21238685 = 7964507) B7964507
theorem B68039675 : Blo 1863633 68039675 := bstep (se 1 (by rfl) ⟨51029756, by rfl⟩ : syracuseStep 68039675 = 102059513) B102059513
theorem B1864807 : Blo 1863633 1864807 := bstep (se 1 (by rfl) ⟨1398605, by rfl⟩ : syracuseStep 1864807 = 2797211) B2797211
theorem B1865063 : Blo 1863633 1865063 := bstep (se 1 (by rfl) ⟨1398797, by rfl⟩ : syracuseStep 1865063 = 2797595) B2797595
theorem B17921645 : Blo 1863633 17921645 := bstep (se 3 (by rfl) ⟨3360308, by rfl⟩ : syracuseStep 17921645 = 6720617) B6720617
theorem B1865343 : Blo 1863633 1865343 := bstep (se 1 (by rfl) ⟨1399007, by rfl⟩ : syracuseStep 1865343 = 2798015) B2798015
theorem B76519201 : Blo 1863633 76519201 := bstep (se 2 (by rfl) ⟨28694700, by rfl⟩ : syracuseStep 76519201 = 57389401) B57389401
theorem B1865575 : Blo 1863633 1865575 := bstep (se 1 (by rfl) ⟨1399181, by rfl⟩ : syracuseStep 1865575 = 2798363) B2798363
theorem B14162039 : Blo 1863633 14162039 := bstep (se 1 (by rfl) ⟨10621529, by rfl⟩ : syracuseStep 14162039 = 21243059) B21243059
theorem B9443627 : Blo 1863633 9443627 := bstep (se 1 (by rfl) ⟨7082720, by rfl⟩ : syracuseStep 9443627 = 14165441) B14165441
theorem B21240143 : Blo 1863633 21240143 := bstep (se 1 (by rfl) ⟨15930107, by rfl⟩ : syracuseStep 21240143 = 31860215) B31860215
theorem B9435851 : Blo 1863633 9435851 := bstep (se 1 (by rfl) ⟨7076888, by rfl⟩ : syracuseStep 9435851 = 14153777) B14153777
theorem B275929811 : Blo 1863633 275929811 := bstep (se 1 (by rfl) ⟨206947358, by rfl⟩ : syracuseStep 275929811 = 413894717) B413894717
theorem B9436013 : Blo 1863633 9436013 := bstep (se 3 (by rfl) ⟨1769252, by rfl⟩ : syracuseStep 9436013 = 3538505) B3538505
theorem B3980495 : Blo 1863633 3980495 := bstep (se 1 (by rfl) ⟨2985371, by rfl⟩ : syracuseStep 3980495 = 5970743) B5970743
theorem B4476320981 : Blo 1863633 4476320981 := bstep (se 7 (by rfl) ⟨52456886, by rfl⟩ : syracuseStep 4476320981 = 104913773) B104913773
theorem B7175479 : Blo 1863633 7175479 := bstep (se 1 (by rfl) ⟨5381609, by rfl⟩ : syracuseStep 7175479 = 10763219) B10763219
theorem B4193639 : Blo 1863633 4193639 := bstep (se 1 (by rfl) ⟨3145229, by rfl⟩ : syracuseStep 4193639 = 6290459) B6290459
theorem B8961455 : Blo 1863633 8961455 := bstep (se 1 (by rfl) ⟨6721091, by rfl⟩ : syracuseStep 8961455 = 13442183) B13442183
theorem B2096743 : Blo 1863633 2096743 := bstep (se 1 (by rfl) ⟨1572557, by rfl⟩ : syracuseStep 2096743 = 3145115) B3145115
theorem B14155721 : Blo 1863633 14155721 := bstep (se 2 (by rfl) ⟨5308395, by rfl⟩ : syracuseStep 14155721 = 10616791) B10616791
theorem B15114221 : Blo 1863633 15114221 := bstep (se 3 (by rfl) ⟨2833916, by rfl⟩ : syracuseStep 15114221 = 5667833) B5667833
theorem B5668967 : Blo 1863633 5668967 := bstep (se 1 (by rfl) ⟨4251725, by rfl⟩ : syracuseStep 5668967 = 8503451) B8503451
theorem B10617065 : Blo 1863633 10617065 := bstep (se 2 (by rfl) ⟨3981399, by rfl⟩ : syracuseStep 10617065 = 7962799) B7962799
theorem B2097391 : Blo 1863633 2097391 := bstep (se 1 (by rfl) ⟨1573043, by rfl⟩ : syracuseStep 2097391 = 3146087) B3146087
theorem B7078225 : Blo 1863633 7078225 := bstep (se 2 (by rfl) ⟨2654334, by rfl⟩ : syracuseStep 7078225 = 5308669) B5308669
theorem B4194791 : Blo 1863633 4194791 := bstep (se 1 (by rfl) ⟨3146093, by rfl⟩ : syracuseStep 4194791 = 6292187) B6292187
theorem B3146215 : Blo 1863633 3146215 := bstep (se 1 (by rfl) ⟨2359661, by rfl⟩ : syracuseStep 3146215 = 4719323) B4719323
theorem B2654699 : Blo 1863633 2654699 := bstep (se 1 (by rfl) ⟨1991024, by rfl⟩ : syracuseStep 2654699 = 3982049) B3982049
theorem B45359783 : Blo 1863633 45359783 := bstep (se 1 (by rfl) ⟨34019837, by rfl⟩ : syracuseStep 45359783 = 68039675) B68039675
theorem B3982135 : Blo 1863633 3982135 := bstep (se 1 (by rfl) ⟨2986601, by rfl⟩ : syracuseStep 3982135 = 5973203) B5973203
theorem B25871305 : Blo 1863633 25871305 := bstep (se 2 (by rfl) ⟨9701739, by rfl⟩ : syracuseStep 25871305 = 19403479) B19403479
theorem B6718555 : Blo 1863633 6718555 := bstep (se 1 (by rfl) ⟨5038916, by rfl⟩ : syracuseStep 6718555 = 10077833) B10077833
theorem B23897213 : Blo 1863633 23897213 := bstep (se 3 (by rfl) ⟨4480727, by rfl⟩ : syracuseStep 23897213 = 8961455) B8961455
theorem B4195655 : Blo 1863633 4195655 := bstep (se 1 (by rfl) ⟨3146741, by rfl⟩ : syracuseStep 4195655 = 6293483) B6293483
theorem B3147079 : Blo 1863633 3147079 := bstep (se 1 (by rfl) ⟨2360309, by rfl⟩ : syracuseStep 3147079 = 4720619) B4720619
theorem B3147167 : Blo 1863633 3147167 := bstep (se 1 (by rfl) ⟨2360375, by rfl⟩ : syracuseStep 3147167 = 4720751) B4720751
theorem B14354003 : Blo 1863633 14354003 := bstep (se 1 (by rfl) ⟨10765502, by rfl⟩ : syracuseStep 14354003 = 21531005) B21531005
theorem B183953207 : Blo 1863633 183953207 := bstep (se 1 (by rfl) ⟨137964905, by rfl⟩ : syracuseStep 183953207 = 275929811) B275929811
theorem B14157665 : Blo 1863633 14157665 := bstep (se 2 (by rfl) ⟨5309124, by rfl⟩ : syracuseStep 14157665 = 10618249) B10618249
theorem B2795657 : Blo 1863633 2795657 := bstep (se 2 (by rfl) ⟨1048371, by rfl⟩ : syracuseStep 2795657 = 2096743) B2096743
theorem B2795759 : Blo 1863633 2795759 := bstep (se 1 (by rfl) ⟨2096819, by rfl⟩ : syracuseStep 2795759 = 4193639) B4193639
theorem B102025601 : Blo 1863633 102025601 := bstep (se 2 (by rfl) ⟨38259600, by rfl⟩ : syracuseStep 102025601 = 76519201) B76519201
theorem B827370449 : Blo 1863633 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B2796539 : Blo 1863633 2796539 := bstep (se 1 (by rfl) ⟨2097404, by rfl⟩ : syracuseStep 2796539 = 4194809) B4194809
theorem B114854921 : Blo 1863633 114854921 := bstep (se 2 (by rfl) ⟨43070595, by rfl⟩ : syracuseStep 114854921 = 86141191) B86141191
theorem B13438007 : Blo 1863633 13438007 := bstep (se 1 (by rfl) ⟨10078505, by rfl⟩ : syracuseStep 13438007 = 20157011) B20157011
theorem B25513235 : Blo 1863633 25513235 := bstep (se 1 (by rfl) ⟨19134926, by rfl⟩ : syracuseStep 25513235 = 38269853) B38269853
theorem B14159123 : Blo 1863633 14159123 := bstep (se 1 (by rfl) ⟨10619342, by rfl⟩ : syracuseStep 14159123 = 21238685) B21238685
theorem B2797007 : Blo 1863633 2797007 := bstep (se 1 (by rfl) ⟨2097755, by rfl⟩ : syracuseStep 2797007 = 4195511) B4195511
theorem B11947763 : Blo 1863633 11947763 := bstep (se 1 (by rfl) ⟨8960822, by rfl⟩ : syracuseStep 11947763 = 17921645) B17921645
theorem B2797391 : Blo 1863633 2797391 := bstep (se 1 (by rfl) ⟨2098043, by rfl⟩ : syracuseStep 2797391 = 4196087) B4196087
theorem B9441359 : Blo 1863633 9441359 := bstep (se 1 (by rfl) ⟨7081019, by rfl⟩ : syracuseStep 9441359 = 14162039) B14162039
theorem B8958113 : Blo 1863633 8958113 := bstep (se 2 (by rfl) ⟨3359292, by rfl⟩ : syracuseStep 8958113 = 6718585) B6718585
theorem B6295751 : Blo 1863633 6295751 := bstep (se 1 (by rfl) ⟨4721813, by rfl⟩ : syracuseStep 6295751 = 9443627) B9443627
theorem B14160095 : Blo 1863633 14160095 := bstep (se 1 (by rfl) ⟨10620071, by rfl⟩ : syracuseStep 14160095 = 21240143) B21240143
theorem B1863983 : Blo 1863633 1863983 := bstep (se 1 (by rfl) ⟨1397987, by rfl⟩ : syracuseStep 1863983 = 2795975) B2795975
theorem B2797871 : Blo 1863633 2797871 := bstep (se 1 (by rfl) ⟨2098403, by rfl⟩ : syracuseStep 2797871 = 4196807) B4196807
theorem B2797895 : Blo 1863633 2797895 := bstep (se 1 (by rfl) ⟨2098421, by rfl⟩ : syracuseStep 2797895 = 4196843) B4196843
theorem B1864191 : Blo 1863633 1864191 := bstep (se 1 (by rfl) ⟨1398143, by rfl⟩ : syracuseStep 1864191 = 2796287) B2796287
theorem B1864303 : Blo 1863633 1864303 := bstep (se 1 (by rfl) ⟨1398227, by rfl⟩ : syracuseStep 1864303 = 2796455) B2796455
theorem B40317551 : Blo 1863633 40317551 := bstep (se 1 (by rfl) ⟨30238163, by rfl⟩ : syracuseStep 40317551 = 60476327) B60476327
theorem B7172891 : Blo 1863633 7172891 := bstep (se 1 (by rfl) ⟨5379668, by rfl⟩ : syracuseStep 7172891 = 10759337) B10759337
theorem B1865007 : Blo 1863633 1865007 := bstep (se 1 (by rfl) ⟨1398755, by rfl⟩ : syracuseStep 1865007 = 2797511) B2797511
theorem B1865031 : Blo 1863633 1865031 := bstep (se 1 (by rfl) ⟨1398773, by rfl⟩ : syracuseStep 1865031 = 2797547) B2797547
theorem B1865183 : Blo 1863633 1865183 := bstep (se 1 (by rfl) ⟨1398887, by rfl⟩ : syracuseStep 1865183 = 2797775) B2797775
theorem B10622441 : Blo 1863633 10622441 := bstep (se 2 (by rfl) ⟨3983415, by rfl⟩ : syracuseStep 10622441 = 7966831) B7966831
theorem B1865375 : Blo 1863633 1865375 := bstep (se 1 (by rfl) ⟨1399031, by rfl⟩ : syracuseStep 1865375 = 2798063) B2798063
theorem B1865499 : Blo 1863633 1865499 := bstep (se 1 (by rfl) ⟨1399124, by rfl⟩ : syracuseStep 1865499 = 2798249) B2798249
theorem B11941739 : Blo 1863633 11941739 := bstep (se 1 (by rfl) ⟨8956304, by rfl⟩ : syracuseStep 11941739 = 17912609) B17912609
theorem B41408765 : Blo 1863633 41408765 := bstep (se 3 (by rfl) ⟨7764143, by rfl⟩ : syracuseStep 41408765 = 15528287) B15528287
theorem B9443951 : Blo 1863633 9443951 := bstep (se 1 (by rfl) ⟨7082963, by rfl⟩ : syracuseStep 9443951 = 14165927) B14165927
theorem B8502077 : Blo 1863633 8502077 := bstep (se 3 (by rfl) ⟨1594139, by rfl⟩ : syracuseStep 8502077 = 3188279) B3188279
theorem B9567305 : Blo 1863633 9567305 := bstep (se 2 (by rfl) ⟨3587739, by rfl⟩ : syracuseStep 9567305 = 7175479) B7175479
theorem B6290567 : Blo 1863633 6290567 := bstep (se 1 (by rfl) ⟨4717925, by rfl⟩ : syracuseStep 6290567 = 9435851) B9435851
theorem B6290675 : Blo 1863633 6290675 := bstep (se 1 (by rfl) ⟨4718006, by rfl⟩ : syracuseStep 6290675 = 9436013) B9436013
theorem B2653663 : Blo 1863633 2653663 := bstep (se 1 (by rfl) ⟨1990247, by rfl⟩ : syracuseStep 2653663 = 3980495) B3980495
theorem B2984213987 : Blo 1863633 2984213987 := bstep (se 1 (by rfl) ⟨2238160490, by rfl⟩ : syracuseStep 2984213987 = 4476320981) B4476320981
theorem B181354241 : Blo 1863633 181354241 := bstep (se 2 (by rfl) ⟨68007840, by rfl⟩ : syracuseStep 181354241 = 136015681) B136015681
theorem B9437147 : Blo 1863633 9437147 := bstep (se 1 (by rfl) ⟨7077860, by rfl⟩ : syracuseStep 9437147 = 14155721) B14155721
theorem B10076147 : Blo 1863633 10076147 := bstep (se 1 (by rfl) ⟨7557110, by rfl⟩ : syracuseStep 10076147 = 15114221) B15114221
theorem B5972075 : Blo 1863633 5972075 := bstep (se 1 (by rfl) ⟨4479056, by rfl⟩ : syracuseStep 5972075 = 8958113) B8958113
theorem B7078043 : Blo 1863633 7078043 := bstep (se 1 (by rfl) ⟨5308532, by rfl⟩ : syracuseStep 7078043 = 10617065) B10617065
theorem B26878367 : Blo 1863633 26878367 := bstep (se 1 (by rfl) ⟨20158775, by rfl⟩ : syracuseStep 26878367 = 40317551) B40317551
theorem B9437633 : Blo 1863633 9437633 := bstep (se 2 (by rfl) ⟨3539112, by rfl⟩ : syracuseStep 9437633 = 7078225) B7078225
theorem B4194953 : Blo 1863633 4194953 := bstep (se 2 (by rfl) ⟨1573107, by rfl⟩ : syracuseStep 4194953 = 3146215) B3146215
theorem B2098111 : Blo 1863633 2098111 := bstep (se 1 (by rfl) ⟨1573583, by rfl⟩ : syracuseStep 2098111 = 3147167) B3147167
theorem B9569335 : Blo 1863633 9569335 := bstep (se 1 (by rfl) ⟨7177001, by rfl⟩ : syracuseStep 9569335 = 14354003) B14354003
theorem B5309513 : Blo 1863633 5309513 := bstep (se 2 (by rfl) ⟨1991067, by rfl⟩ : syracuseStep 5309513 = 3982135) B3982135
theorem B122635471 : Blo 1863633 122635471 := bstep (se 1 (by rfl) ⟨91976603, by rfl⟩ : syracuseStep 122635471 = 183953207) B183953207
theorem B9438443 : Blo 1863633 9438443 := bstep (se 1 (by rfl) ⟨7078832, by rfl⟩ : syracuseStep 9438443 = 14157665) B14157665
theorem B7079197 : Blo 1863633 7079197 := bstep (se 3 (by rfl) ⟨1327349, by rfl⟩ : syracuseStep 7079197 = 2654699) B2654699
theorem B4196105 : Blo 1863633 4196105 := bstep (se 2 (by rfl) ⟨1573539, by rfl⟩ : syracuseStep 4196105 = 3147079) B3147079
theorem B17008823 : Blo 1863633 17008823 := bstep (se 1 (by rfl) ⟨12756617, by rfl⟩ : syracuseStep 17008823 = 25513235) B25513235
theorem B9439415 : Blo 1863633 9439415 := bstep (se 1 (by rfl) ⟨7079561, by rfl⟩ : syracuseStep 9439415 = 14159123) B14159123
theorem B7965175 : Blo 1863633 7965175 := bstep (se 1 (by rfl) ⟨5973881, by rfl⟩ : syracuseStep 7965175 = 11947763) B11947763
theorem B6294239 : Blo 1863633 6294239 := bstep (se 1 (by rfl) ⟨4720679, by rfl⟩ : syracuseStep 6294239 = 9441359) B9441359
theorem B3779311 : Blo 1863633 3779311 := bstep (se 1 (by rfl) ⟨2834483, by rfl⟩ : syracuseStep 3779311 = 5668967) B5668967
theorem B4197167 : Blo 1863633 4197167 := bstep (se 1 (by rfl) ⟨3147875, by rfl⟩ : syracuseStep 4197167 = 6295751) B6295751
theorem B9440063 : Blo 1863633 9440063 := bstep (se 1 (by rfl) ⟨7080047, by rfl⟩ : syracuseStep 9440063 = 14160095) B14160095
theorem B2796521 : Blo 1863633 2796521 := bstep (se 2 (by rfl) ⟨1048695, by rfl⟩ : syracuseStep 2796521 = 2097391) B2097391
theorem B2796527 : Blo 1863633 2796527 := bstep (se 1 (by rfl) ⟨2097395, by rfl⟩ : syracuseStep 2796527 = 4194791) B4194791
theorem B30239855 : Blo 1863633 30239855 := bstep (se 1 (by rfl) ⟨22679891, by rfl⟩ : syracuseStep 30239855 = 45359783) B45359783
theorem B2797103 : Blo 1863633 2797103 := bstep (se 1 (by rfl) ⟨2097827, by rfl⟩ : syracuseStep 2797103 = 4195655) B4195655
theorem B7081627 : Blo 1863633 7081627 := bstep (se 1 (by rfl) ⟨5311220, by rfl⟩ : syracuseStep 7081627 = 10622441) B10622441
theorem B1863771 : Blo 1863633 1863771 := bstep (se 1 (by rfl) ⟨1397828, by rfl⟩ : syracuseStep 1863771 = 2795657) B2795657
theorem B8958073 : Blo 1863633 8958073 := bstep (se 2 (by rfl) ⟨3359277, by rfl⟩ : syracuseStep 8958073 = 6718555) B6718555
theorem B1863839 : Blo 1863633 1863839 := bstep (se 1 (by rfl) ⟨1397879, by rfl⟩ : syracuseStep 1863839 = 2795759) B2795759
theorem B6295967 : Blo 1863633 6295967 := bstep (se 1 (by rfl) ⟨4721975, by rfl⟩ : syracuseStep 6295967 = 9443951) B9443951
theorem B551580299 : Blo 1863633 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B1864359 : Blo 1863633 1864359 := bstep (se 1 (by rfl) ⟨1398269, by rfl⟩ : syracuseStep 1864359 = 2796539) B2796539
theorem B8958671 : Blo 1863633 8958671 := bstep (se 1 (by rfl) ⟨6719003, by rfl⟩ : syracuseStep 8958671 = 13438007) B13438007
theorem B6378203 : Blo 1863633 6378203 := bstep (se 1 (by rfl) ⟨4783652, by rfl⟩ : syracuseStep 6378203 = 9567305) B9567305
theorem B1864671 : Blo 1863633 1864671 := bstep (se 1 (by rfl) ⟨1398503, by rfl⟩ : syracuseStep 1864671 = 2797007) B2797007
theorem B120902827 : Blo 1863633 120902827 := bstep (se 1 (by rfl) ⟨90677120, by rfl⟩ : syracuseStep 120902827 = 181354241) B181354241
theorem B1864927 : Blo 1863633 1864927 := bstep (se 1 (by rfl) ⟨1398695, by rfl⟩ : syracuseStep 1864927 = 2797391) B2797391
theorem B1865247 : Blo 1863633 1865247 := bstep (se 1 (by rfl) ⟨1398935, by rfl⟩ : syracuseStep 1865247 = 2797871) B2797871
theorem B1865263 : Blo 1863633 1865263 := bstep (se 1 (by rfl) ⟨1398947, by rfl⟩ : syracuseStep 1865263 = 2797895) B2797895
theorem B4781927 : Blo 1863633 4781927 := bstep (se 1 (by rfl) ⟨3586445, by rfl⟩ : syracuseStep 4781927 = 7172891) B7172891
theorem B15931475 : Blo 1863633 15931475 := bstep (se 1 (by rfl) ⟨11948606, by rfl⟩ : syracuseStep 15931475 = 23897213) B23897213
theorem B7961159 : Blo 1863633 7961159 := bstep (se 1 (by rfl) ⟨5970869, by rfl⟩ : syracuseStep 7961159 = 11941739) B11941739
theorem B34495073 : Blo 1863633 34495073 := bstep (se 2 (by rfl) ⟨12935652, by rfl⟩ : syracuseStep 34495073 = 25871305) B25871305
theorem B27605843 : Blo 1863633 27605843 := bstep (se 1 (by rfl) ⟨20704382, by rfl⟩ : syracuseStep 27605843 = 41408765) B41408765
theorem B68017067 : Blo 1863633 68017067 := bstep (se 1 (by rfl) ⟨51012800, by rfl⟩ : syracuseStep 68017067 = 102025601) B102025601
theorem B5668051 : Blo 1863633 5668051 := bstep (se 1 (by rfl) ⟨4251038, by rfl⟩ : syracuseStep 5668051 = 8502077) B8502077
theorem B3538217 : Blo 1863633 3538217 := bstep (se 2 (by rfl) ⟨1326831, by rfl⟩ : syracuseStep 3538217 = 2653663) B2653663
theorem B76569947 : Blo 1863633 76569947 := bstep (se 1 (by rfl) ⟨57427460, by rfl⟩ : syracuseStep 76569947 = 114854921) B114854921
theorem B4193711 : Blo 1863633 4193711 := bstep (se 1 (by rfl) ⟨3145283, by rfl⟩ : syracuseStep 4193711 = 6290567) B6290567
theorem B4193783 : Blo 1863633 4193783 := bstep (se 1 (by rfl) ⟨3145337, by rfl⟩ : syracuseStep 4193783 = 6290675) B6290675
theorem B1989475991 : Blo 1863633 1989475991 := bstep (se 1 (by rfl) ⟨1492106993, by rfl⟩ : syracuseStep 1989475991 = 2984213987) B2984213987
theorem B6291431 : Blo 1863633 6291431 := bstep (se 1 (by rfl) ⟨4718573, by rfl⟩ : syracuseStep 6291431 = 9437147) B9437147
theorem B6717431 : Blo 1863633 6717431 := bstep (se 1 (by rfl) ⟨5038073, by rfl⟩ : syracuseStep 6717431 = 10076147) B10076147
theorem B3981383 : Blo 1863633 3981383 := bstep (se 1 (by rfl) ⟨2986037, by rfl⟩ : syracuseStep 3981383 = 5972075) B5972075
theorem B4718695 : Blo 1863633 4718695 := bstep (se 1 (by rfl) ⟨3539021, by rfl⟩ : syracuseStep 4718695 = 7078043) B7078043
theorem B11944097 : Blo 1863633 11944097 := bstep (se 2 (by rfl) ⟨4479036, by rfl⟩ : syracuseStep 11944097 = 8958073) B8958073
theorem B6291755 : Blo 1863633 6291755 := bstep (se 1 (by rfl) ⟨4718816, by rfl⟩ : syracuseStep 6291755 = 9437633) B9437633
theorem B5972447 : Blo 1863633 5972447 := bstep (se 1 (by rfl) ⟨4479335, by rfl⟩ : syracuseStep 5972447 = 8958671) B8958671
theorem B3539675 : Blo 1863633 3539675 := bstep (se 1 (by rfl) ⟨2654756, by rfl⟩ : syracuseStep 3539675 = 5309513) B5309513
theorem B6292295 : Blo 1863633 6292295 := bstep (se 1 (by rfl) ⟨4719221, by rfl⟩ : syracuseStep 6292295 = 9438443) B9438443
theorem B5039081 : Blo 1863633 5039081 := bstep (se 2 (by rfl) ⟨1889655, by rfl⟩ : syracuseStep 5039081 = 3779311) B3779311
theorem B6292943 : Blo 1863633 6292943 := bstep (se 1 (by rfl) ⟨4719707, by rfl⟩ : syracuseStep 6292943 = 9439415) B9439415
theorem B161203769 : Blo 1863633 161203769 := bstep (se 2 (by rfl) ⟨60451413, by rfl⟩ : syracuseStep 161203769 = 120902827) B120902827
theorem B163513961 : Blo 1863633 163513961 := bstep (se 2 (by rfl) ⟨61317735, by rfl⟩ : syracuseStep 163513961 = 122635471) B122635471
theorem B9438929 : Blo 1863633 9438929 := bstep (se 2 (by rfl) ⟨3539598, by rfl⟩ : syracuseStep 9438929 = 7079197) B7079197
theorem B22996715 : Blo 1863633 22996715 := bstep (se 1 (by rfl) ⟨17247536, by rfl⟩ : syracuseStep 22996715 = 34495073) B34495073
theorem B4196159 : Blo 1863633 4196159 := bstep (se 1 (by rfl) ⟨3147119, by rfl⟩ : syracuseStep 4196159 = 6294239) B6294239
theorem B6293375 : Blo 1863633 6293375 := bstep (se 1 (by rfl) ⟨4720031, by rfl⟩ : syracuseStep 6293375 = 9440063) B9440063
theorem B17008541 : Blo 1863633 17008541 := bstep (se 3 (by rfl) ⟨3189101, by rfl⟩ : syracuseStep 17008541 = 6378203) B6378203
theorem B45344711 : Blo 1863633 45344711 := bstep (se 1 (by rfl) ⟨34008533, by rfl⟩ : syracuseStep 45344711 = 68017067) B68017067
theorem B51046631 : Blo 1863633 51046631 := bstep (se 1 (by rfl) ⟨38284973, by rfl⟩ : syracuseStep 51046631 = 76569947) B76569947
theorem B2795807 : Blo 1863633 2795807 := bstep (se 1 (by rfl) ⟨2096855, by rfl⟩ : syracuseStep 2795807 = 4193711) B4193711
theorem B2795855 : Blo 1863633 2795855 := bstep (se 1 (by rfl) ⟨2096891, by rfl⟩ : syracuseStep 2795855 = 4193783) B4193783
theorem B17918911 : Blo 1863633 17918911 := bstep (se 1 (by rfl) ⟨13439183, by rfl⟩ : syracuseStep 17918911 = 26878367) B26878367
theorem B4197311 : Blo 1863633 4197311 := bstep (se 1 (by rfl) ⟨3147983, by rfl⟩ : syracuseStep 4197311 = 6295967) B6295967
theorem B2796635 : Blo 1863633 2796635 := bstep (se 1 (by rfl) ⟨2097476, by rfl⟩ : syracuseStep 2796635 = 4194953) B4194953
theorem B10620233 : Blo 1863633 10620233 := bstep (se 2 (by rfl) ⟨3982587, by rfl⟩ : syracuseStep 10620233 = 7965175) B7965175
theorem B2797403 : Blo 1863633 2797403 := bstep (se 1 (by rfl) ⟨2098052, by rfl⟩ : syracuseStep 2797403 = 4196105) B4196105
theorem B2797481 : Blo 1863633 2797481 := bstep (se 2 (by rfl) ⟨1049055, by rfl⟩ : syracuseStep 2797481 = 2098111) B2098111
theorem B10620983 : Blo 1863633 10620983 := bstep (se 1 (by rfl) ⟨7965737, by rfl⟩ : syracuseStep 10620983 = 15931475) B15931475
theorem B12759113 : Blo 1863633 12759113 := bstep (se 2 (by rfl) ⟨4784667, by rfl⟩ : syracuseStep 12759113 = 9569335) B9569335
theorem B7557401 : Blo 1863633 7557401 := bstep (se 2 (by rfl) ⟨2834025, by rfl⟩ : syracuseStep 7557401 = 5668051) B5668051
theorem B2798111 : Blo 1863633 2798111 := bstep (se 1 (by rfl) ⟨2098583, by rfl⟩ : syracuseStep 2798111 = 4197167) B4197167
theorem B18403895 : Blo 1863633 18403895 := bstep (se 1 (by rfl) ⟨13802921, by rfl⟩ : syracuseStep 18403895 = 27605843) B27605843
theorem B1864347 : Blo 1863633 1864347 := bstep (se 1 (by rfl) ⟨1398260, by rfl⟩ : syracuseStep 1864347 = 2796521) B2796521
theorem B1864351 : Blo 1863633 1864351 := bstep (se 1 (by rfl) ⟨1398263, by rfl⟩ : syracuseStep 1864351 = 2796527) B2796527
theorem B9442169 : Blo 1863633 9442169 := bstep (se 2 (by rfl) ⟨3540813, by rfl⟩ : syracuseStep 9442169 = 7081627) B7081627
theorem B12751805 : Blo 1863633 12751805 := bstep (se 3 (by rfl) ⟨2390963, by rfl⟩ : syracuseStep 12751805 = 4781927) B4781927
theorem B1864735 : Blo 1863633 1864735 := bstep (se 1 (by rfl) ⟨1398551, by rfl⟩ : syracuseStep 1864735 = 2797103) B2797103
theorem B17913149 : Blo 1863633 17913149 := bstep (se 3 (by rfl) ⟨3358715, by rfl⟩ : syracuseStep 17913149 = 6717431) B6717431
theorem B367720199 : Blo 1863633 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B45356861 : Blo 1863633 45356861 := bstep (se 3 (by rfl) ⟨8504411, by rfl⟩ : syracuseStep 45356861 = 17008823) B17008823
theorem B5307439 : Blo 1863633 5307439 := bstep (se 1 (by rfl) ⟨3980579, by rfl⟩ : syracuseStep 5307439 = 7961159) B7961159
theorem B20159903 : Blo 1863633 20159903 := bstep (se 1 (by rfl) ⟨15119927, by rfl⟩ : syracuseStep 20159903 = 30239855) B30239855
theorem B2358811 : Blo 1863633 2358811 := bstep (se 1 (by rfl) ⟨1769108, by rfl⟩ : syracuseStep 2358811 = 3538217) B3538217
theorem B1326317327 : Blo 1863633 1326317327 := bstep (se 1 (by rfl) ⟨994737995, by rfl⟩ : syracuseStep 1326317327 = 1989475991) B1989475991
theorem B4194287 : Blo 1863633 4194287 := bstep (se 1 (by rfl) ⟨3145715, by rfl⟩ : syracuseStep 4194287 = 6291431) B6291431
theorem B2654255 : Blo 1863633 2654255 := bstep (se 1 (by rfl) ⟨1990691, by rfl⟩ : syracuseStep 2654255 = 3981383) B3981383
theorem B7962731 : Blo 1863633 7962731 := bstep (se 1 (by rfl) ⟨5972048, by rfl⟩ : syracuseStep 7962731 = 11944097) B11944097
theorem B6291593 : Blo 1863633 6291593 := bstep (se 2 (by rfl) ⟨2359347, by rfl⟩ : syracuseStep 6291593 = 4718695) B4718695
theorem B4194503 : Blo 1863633 4194503 := bstep (se 1 (by rfl) ⟨3145877, by rfl⟩ : syracuseStep 4194503 = 6291755) B6291755
theorem B3981631 : Blo 1863633 3981631 := bstep (se 1 (by rfl) ⟨2986223, by rfl⟩ : syracuseStep 3981631 = 5972447) B5972447
theorem B2359783 : Blo 1863633 2359783 := bstep (se 1 (by rfl) ⟨1769837, by rfl⟩ : syracuseStep 2359783 = 3539675) B3539675
theorem B4194863 : Blo 1863633 4194863 := bstep (se 1 (by rfl) ⟨3146147, by rfl⟩ : syracuseStep 4194863 = 6292295) B6292295
theorem B3359387 : Blo 1863633 3359387 := bstep (se 1 (by rfl) ⟨2519540, by rfl⟩ : syracuseStep 3359387 = 5039081) B5039081
theorem B20153069 : Blo 1863633 20153069 := bstep (se 3 (by rfl) ⟨3778700, by rfl⟩ : syracuseStep 20153069 = 7557401) B7557401
theorem B4195295 : Blo 1863633 4195295 := bstep (se 1 (by rfl) ⟨3146471, by rfl⟩ : syracuseStep 4195295 = 6292943) B6292943
theorem B6292619 : Blo 1863633 6292619 := bstep (se 1 (by rfl) ⟨4719464, by rfl⟩ : syracuseStep 6292619 = 9438929) B9438929
theorem B245146799 : Blo 1863633 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B30237907 : Blo 1863633 30237907 := bstep (se 1 (by rfl) ⟨22678430, by rfl⟩ : syracuseStep 30237907 = 45356861) B45356861
theorem B4195583 : Blo 1863633 4195583 := bstep (se 1 (by rfl) ⟨3146687, by rfl⟩ : syracuseStep 4195583 = 6293375) B6293375
theorem B11339027 : Blo 1863633 11339027 := bstep (se 1 (by rfl) ⟨8504270, by rfl⟩ : syracuseStep 11339027 = 17008541) B17008541
theorem B30229807 : Blo 1863633 30229807 := bstep (se 1 (by rfl) ⟨22672355, by rfl⟩ : syracuseStep 30229807 = 45344711) B45344711
theorem B34031087 : Blo 1863633 34031087 := bstep (se 1 (by rfl) ⟨25523315, by rfl⟩ : syracuseStep 34031087 = 51046631) B51046631
theorem B7080155 : Blo 1863633 7080155 := bstep (se 1 (by rfl) ⟨5310116, by rfl⟩ : syracuseStep 7080155 = 10620233) B10620233
theorem B2796191 : Blo 1863633 2796191 := bstep (se 1 (by rfl) ⟨2097143, by rfl⟩ : syracuseStep 2796191 = 4194287) B4194287
theorem B7080655 : Blo 1863633 7080655 := bstep (se 1 (by rfl) ⟨5310491, by rfl⟩ : syracuseStep 7080655 = 10620983) B10620983
theorem B8506075 : Blo 1863633 8506075 := bstep (se 1 (by rfl) ⟨6379556, by rfl⟩ : syracuseStep 8506075 = 12759113) B12759113
theorem B6294779 : Blo 1863633 6294779 := bstep (se 1 (by rfl) ⟨4721084, by rfl⟩ : syracuseStep 6294779 = 9442169) B9442169
theorem B2797439 : Blo 1863633 2797439 := bstep (se 1 (by rfl) ⟨2098079, by rfl⟩ : syracuseStep 2797439 = 4196159) B4196159
theorem B23891881 : Blo 1863633 23891881 := bstep (se 2 (by rfl) ⟨8959455, by rfl⟩ : syracuseStep 23891881 = 17918911) B17918911
theorem B1863871 : Blo 1863633 1863871 := bstep (se 1 (by rfl) ⟨1397903, by rfl⟩ : syracuseStep 1863871 = 2795807) B2795807
theorem B1863903 : Blo 1863633 1863903 := bstep (se 1 (by rfl) ⟨1397927, by rfl⟩ : syracuseStep 1863903 = 2795855) B2795855
theorem B2798207 : Blo 1863633 2798207 := bstep (se 1 (by rfl) ⟨2098655, by rfl⟩ : syracuseStep 2798207 = 4197311) B4197311
theorem B1864423 : Blo 1863633 1864423 := bstep (se 1 (by rfl) ⟨1398317, by rfl⟩ : syracuseStep 1864423 = 2796635) B2796635
theorem B13439935 : Blo 1863633 13439935 := bstep (se 1 (by rfl) ⟨10079951, by rfl⟩ : syracuseStep 13439935 = 20159903) B20159903
theorem B245298293 : Blo 1863633 245298293 := bstep (se 5 (by rfl) ⟨11498357, by rfl⟩ : syracuseStep 245298293 = 22996715) B22996715
theorem B1864935 : Blo 1863633 1864935 := bstep (se 1 (by rfl) ⟨1398701, by rfl⟩ : syracuseStep 1864935 = 2797403) B2797403
theorem B1864987 : Blo 1863633 1864987 := bstep (se 1 (by rfl) ⟨1398740, by rfl⟩ : syracuseStep 1864987 = 2797481) B2797481
theorem B1865407 : Blo 1863633 1865407 := bstep (se 1 (by rfl) ⟨1399055, by rfl⟩ : syracuseStep 1865407 = 2798111) B2798111
theorem B12269263 : Blo 1863633 12269263 := bstep (se 1 (by rfl) ⟨9201947, by rfl⟩ : syracuseStep 12269263 = 18403895) B18403895
theorem B8501203 : Blo 1863633 8501203 := bstep (se 1 (by rfl) ⟨6375902, by rfl⟩ : syracuseStep 8501203 = 12751805) B12751805
theorem B11942099 : Blo 1863633 11942099 := bstep (se 1 (by rfl) ⟨8956574, by rfl⟩ : syracuseStep 11942099 = 17913149) B17913149
theorem B107469179 : Blo 1863633 107469179 := bstep (se 1 (by rfl) ⟨80601884, by rfl⟩ : syracuseStep 107469179 = 161203769) B161203769
theorem B109009307 : Blo 1863633 109009307 := bstep (se 1 (by rfl) ⟨81756980, by rfl⟩ : syracuseStep 109009307 = 163513961) B163513961
theorem B7076585 : Blo 1863633 7076585 := bstep (se 2 (by rfl) ⟨2653719, by rfl⟩ : syracuseStep 7076585 = 5307439) B5307439
theorem B3145081 : Blo 1863633 3145081 := bstep (se 2 (by rfl) ⟨1179405, by rfl⟩ : syracuseStep 3145081 = 2358811) B2358811
theorem B884211551 : Blo 1863633 884211551 := bstep (se 1 (by rfl) ⟨663158663, by rfl⟩ : syracuseStep 884211551 = 1326317327) B1326317327
theorem B5308487 : Blo 1863633 5308487 := bstep (se 1 (by rfl) ⟨3981365, by rfl⟩ : syracuseStep 5308487 = 7962731) B7962731
theorem B4194395 : Blo 1863633 4194395 := bstep (se 1 (by rfl) ⟨3145796, by rfl⟩ : syracuseStep 4194395 = 6291593) B6291593
theorem B7078013 : Blo 1863633 7078013 := bstep (se 3 (by rfl) ⟨1327127, by rfl⟩ : syracuseStep 7078013 = 2654255) B2654255
theorem B5308841 : Blo 1863633 5308841 := bstep (se 2 (by rfl) ⟨1990815, by rfl⟩ : syracuseStep 5308841 = 3981631) B3981631
theorem B13435379 : Blo 1863633 13435379 := bstep (se 1 (by rfl) ⟨10076534, by rfl⟩ : syracuseStep 13435379 = 20153069) B20153069
theorem B3146377 : Blo 1863633 3146377 := bstep (se 2 (by rfl) ⟨1179891, by rfl⟩ : syracuseStep 3146377 = 2359783) B2359783
theorem B4195079 : Blo 1863633 4195079 := bstep (se 1 (by rfl) ⟨3146309, by rfl⟩ : syracuseStep 4195079 = 6292619) B6292619
theorem B163431199 : Blo 1863633 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B4720103 : Blo 1863633 4720103 := bstep (se 1 (by rfl) ⟨3540077, by rfl⟩ : syracuseStep 4720103 = 7080155) B7080155
theorem B72672871 : Blo 1863633 72672871 := bstep (se 1 (by rfl) ⟨54504653, by rfl⟩ : syracuseStep 72672871 = 109009307) B109009307
theorem B40306409 : Blo 1863633 40306409 := bstep (se 2 (by rfl) ⟨15114903, by rfl⟩ : syracuseStep 40306409 = 30229807) B30229807
theorem B4196519 : Blo 1863633 4196519 := bstep (se 1 (by rfl) ⟨3147389, by rfl⟩ : syracuseStep 4196519 = 6294779) B6294779
theorem B589474367 : Blo 1863633 589474367 := bstep (se 1 (by rfl) ⟨442105775, by rfl⟩ : syracuseStep 589474367 = 884211551) B884211551
theorem B2796335 : Blo 1863633 2796335 := bstep (se 1 (by rfl) ⟨2097251, by rfl⟩ : syracuseStep 2796335 = 4194503) B4194503
theorem B2796575 : Blo 1863633 2796575 := bstep (se 1 (by rfl) ⟨2097431, by rfl⟩ : syracuseStep 2796575 = 4194863) B4194863
theorem B2239591 : Blo 1863633 2239591 := bstep (se 1 (by rfl) ⟨1679693, by rfl⟩ : syracuseStep 2239591 = 3359387) B3359387
theorem B2796863 : Blo 1863633 2796863 := bstep (se 1 (by rfl) ⟨2097647, by rfl⟩ : syracuseStep 2796863 = 4195295) B4195295
theorem B163532195 : Blo 1863633 163532195 := bstep (se 1 (by rfl) ⟨122649146, by rfl⟩ : syracuseStep 163532195 = 245298293) B245298293
theorem B2797055 : Blo 1863633 2797055 := bstep (se 1 (by rfl) ⟨2097791, by rfl⟩ : syracuseStep 2797055 = 4195583) B4195583
theorem B9440873 : Blo 1863633 9440873 := bstep (se 2 (by rfl) ⟨3540327, by rfl⟩ : syracuseStep 9440873 = 7080655) B7080655
theorem B11341433 : Blo 1863633 11341433 := bstep (se 2 (by rfl) ⟨4253037, by rfl⟩ : syracuseStep 11341433 = 8506075) B8506075
theorem B22687391 : Blo 1863633 22687391 := bstep (se 1 (by rfl) ⟨17015543, by rfl⟩ : syracuseStep 22687391 = 34031087) B34031087
theorem B17919913 : Blo 1863633 17919913 := bstep (se 2 (by rfl) ⟨6719967, by rfl⟩ : syracuseStep 17919913 = 13439935) B13439935
theorem B40317209 : Blo 1863633 40317209 := bstep (se 2 (by rfl) ⟨15118953, by rfl⟩ : syracuseStep 40317209 = 30237907) B30237907
theorem B1864127 : Blo 1863633 1864127 := bstep (se 1 (by rfl) ⟨1398095, by rfl⟩ : syracuseStep 1864127 = 2796191) B2796191
theorem B31855841 : Blo 1863633 31855841 := bstep (se 2 (by rfl) ⟨11945940, by rfl⟩ : syracuseStep 31855841 = 23891881) B23891881
theorem B1864959 : Blo 1863633 1864959 := bstep (se 1 (by rfl) ⟨1398719, by rfl⟩ : syracuseStep 1864959 = 2797439) B2797439
theorem B11334937 : Blo 1863633 11334937 := bstep (se 2 (by rfl) ⟨4250601, by rfl⟩ : syracuseStep 11334937 = 8501203) B8501203
theorem B1865471 : Blo 1863633 1865471 := bstep (se 1 (by rfl) ⟨1399103, by rfl⟩ : syracuseStep 1865471 = 2798207) B2798207
theorem B7559351 : Blo 1863633 7559351 := bstep (se 1 (by rfl) ⟨5669513, by rfl⟩ : syracuseStep 7559351 = 11339027) B11339027
theorem B7961399 : Blo 1863633 7961399 := bstep (se 1 (by rfl) ⟨5971049, by rfl⟩ : syracuseStep 7961399 = 11942099) B11942099
theorem B71646119 : Blo 1863633 71646119 := bstep (se 1 (by rfl) ⟨53734589, by rfl⟩ : syracuseStep 71646119 = 107469179) B107469179
theorem B4717723 : Blo 1863633 4717723 := bstep (se 1 (by rfl) ⟨3538292, by rfl⟩ : syracuseStep 4717723 = 7076585) B7076585
theorem B4193441 : Blo 1863633 4193441 := bstep (se 2 (by rfl) ⟨1572540, by rfl⟩ : syracuseStep 4193441 = 3145081) B3145081
theorem B16359017 : Blo 1863633 16359017 := bstep (se 2 (by rfl) ⟨6134631, by rfl⟩ : syracuseStep 16359017 = 12269263) B12269263
theorem B3538991 : Blo 1863633 3538991 := bstep (se 1 (by rfl) ⟨2654243, by rfl⟩ : syracuseStep 3538991 = 5308487) B5308487
theorem B4718675 : Blo 1863633 4718675 := bstep (se 1 (by rfl) ⟨3539006, by rfl⟩ : syracuseStep 4718675 = 7078013) B7078013
theorem B26878139 : Blo 1863633 26878139 := bstep (se 1 (by rfl) ⟨20158604, by rfl⟩ : syracuseStep 26878139 = 40317209) B40317209
theorem B3539227 : Blo 1863633 3539227 := bstep (se 1 (by rfl) ⟨2654420, by rfl⟩ : syracuseStep 3539227 = 5308841) B5308841
theorem B4195169 : Blo 1863633 4195169 := bstep (se 2 (by rfl) ⟨1573188, by rfl⟩ : syracuseStep 4195169 = 3146377) B3146377
theorem B3146735 : Blo 1863633 3146735 := bstep (se 1 (by rfl) ⟨2360051, by rfl⟩ : syracuseStep 3146735 = 4720103) B4720103
theorem B217908265 : Blo 1863633 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B26870939 : Blo 1863633 26870939 := bstep (se 1 (by rfl) ⟨20153204, by rfl⟩ : syracuseStep 26870939 = 40306409) B40306409
theorem B5039567 : Blo 1863633 5039567 := bstep (se 1 (by rfl) ⟨3779675, by rfl⟩ : syracuseStep 5039567 = 7559351) B7559351
theorem B43624045 : Blo 1863633 43624045 := bstep (se 3 (by rfl) ⟨8179508, by rfl⟩ : syracuseStep 43624045 = 16359017) B16359017
theorem B2795627 : Blo 1863633 2795627 := bstep (se 1 (by rfl) ⟨2096720, by rfl⟩ : syracuseStep 2795627 = 4193441) B4193441
theorem B96897161 : Blo 1863633 96897161 := bstep (se 2 (by rfl) ⟨36336435, by rfl⟩ : syracuseStep 96897161 = 72672871) B72672871
theorem B109021463 : Blo 1863633 109021463 := bstep (se 1 (by rfl) ⟨81766097, by rfl⟩ : syracuseStep 109021463 = 163532195) B163532195
theorem B6293915 : Blo 1863633 6293915 := bstep (se 1 (by rfl) ⟨4720436, by rfl⟩ : syracuseStep 6293915 = 9440873) B9440873
theorem B15124927 : Blo 1863633 15124927 := bstep (se 1 (by rfl) ⟨11343695, by rfl⟩ : syracuseStep 15124927 = 22687391) B22687391
theorem B2796263 : Blo 1863633 2796263 := bstep (se 1 (by rfl) ⟨2097197, by rfl⟩ : syracuseStep 2796263 = 4194395) B4194395
theorem B8956919 : Blo 1863633 8956919 := bstep (se 1 (by rfl) ⟨6717689, by rfl⟩ : syracuseStep 8956919 = 13435379) B13435379
theorem B2796719 : Blo 1863633 2796719 := bstep (se 1 (by rfl) ⟨2097539, by rfl⟩ : syracuseStep 2796719 = 4195079) B4195079
theorem B21237227 : Blo 1863633 21237227 := bstep (se 1 (by rfl) ⟨15927920, by rfl⟩ : syracuseStep 21237227 = 31855841) B31855841
theorem B2797679 : Blo 1863633 2797679 := bstep (se 1 (by rfl) ⟨2098259, by rfl⟩ : syracuseStep 2797679 = 4196519) B4196519
theorem B2986121 : Blo 1863633 2986121 := bstep (se 2 (by rfl) ⟨1119795, by rfl⟩ : syracuseStep 2986121 = 2239591) B2239591
theorem B392982911 : Blo 1863633 392982911 := bstep (se 1 (by rfl) ⟨294737183, by rfl⟩ : syracuseStep 392982911 = 589474367) B589474367
theorem B1864223 : Blo 1863633 1864223 := bstep (se 1 (by rfl) ⟨1398167, by rfl⟩ : syracuseStep 1864223 = 2796335) B2796335
theorem B47764079 : Blo 1863633 47764079 := bstep (se 1 (by rfl) ⟨35823059, by rfl⟩ : syracuseStep 47764079 = 71646119) B71646119
theorem B1864383 : Blo 1863633 1864383 := bstep (se 1 (by rfl) ⟨1398287, by rfl⟩ : syracuseStep 1864383 = 2796575) B2796575
theorem B1864575 : Blo 1863633 1864575 := bstep (se 1 (by rfl) ⟨1398431, by rfl⟩ : syracuseStep 1864575 = 2796863) B2796863
theorem B1864703 : Blo 1863633 1864703 := bstep (se 1 (by rfl) ⟨1398527, by rfl⟩ : syracuseStep 1864703 = 2797055) B2797055
theorem B23893217 : Blo 1863633 23893217 := bstep (se 2 (by rfl) ⟨8959956, by rfl⟩ : syracuseStep 23893217 = 17919913) B17919913
theorem B6290297 : Blo 1863633 6290297 := bstep (se 2 (by rfl) ⟨2358861, by rfl⟩ : syracuseStep 6290297 = 4717723) B4717723
theorem B15113249 : Blo 1863633 15113249 := bstep (se 2 (by rfl) ⟨5667468, by rfl⟩ : syracuseStep 15113249 = 11334937) B11334937
theorem B5307599 : Blo 1863633 5307599 := bstep (se 1 (by rfl) ⟨3980699, by rfl⟩ : syracuseStep 5307599 = 7961399) B7961399
theorem B7560955 : Blo 1863633 7560955 := bstep (se 1 (by rfl) ⟨5670716, by rfl⟩ : syracuseStep 7560955 = 11341433) B11341433
theorem B3145783 : Blo 1863633 3145783 := bstep (se 1 (by rfl) ⟨2359337, by rfl⟩ : syracuseStep 3145783 = 4718675) B4718675
theorem B1990747 : Blo 1863633 1990747 := bstep (se 1 (by rfl) ⟨1493060, by rfl⟩ : syracuseStep 1990747 = 2986121) B2986121
theorem B9437309 : Blo 1863633 9437309 := bstep (se 3 (by rfl) ⟨1769495, by rfl⟩ : syracuseStep 9437309 = 3538991) B3538991
theorem B261988607 : Blo 1863633 261988607 := bstep (se 1 (by rfl) ⟨196491455, by rfl⟩ : syracuseStep 261988607 = 392982911) B392982911
theorem B258392429 : Blo 1863633 258392429 := bstep (se 3 (by rfl) ⟨48448580, by rfl⟩ : syracuseStep 258392429 = 96897161) B96897161
theorem B4718969 : Blo 1863633 4718969 := bstep (se 2 (by rfl) ⟨1769613, by rfl⟩ : syracuseStep 4718969 = 3539227) B3539227
theorem B31842719 : Blo 1863633 31842719 := bstep (se 1 (by rfl) ⟨23882039, by rfl⟩ : syracuseStep 31842719 = 47764079) B47764079
theorem B2097823 : Blo 1863633 2097823 := bstep (se 1 (by rfl) ⟨1573367, by rfl⟩ : syracuseStep 2097823 = 3146735) B3146735
theorem B3359711 : Blo 1863633 3359711 := bstep (se 1 (by rfl) ⟨2519783, by rfl⟩ : syracuseStep 3359711 = 5039567) B5039567
theorem B72680975 : Blo 1863633 72680975 := bstep (se 1 (by rfl) ⟨54510731, by rfl⟩ : syracuseStep 72680975 = 109021463) B109021463
theorem B4195943 : Blo 1863633 4195943 := bstep (se 1 (by rfl) ⟨3146957, by rfl⟩ : syracuseStep 4195943 = 6293915) B6293915
theorem B58165393 : Blo 1863633 58165393 := bstep (se 2 (by rfl) ⟨21812022, by rfl⟩ : syracuseStep 58165393 = 43624045) B43624045
theorem B14158151 : Blo 1863633 14158151 := bstep (se 1 (by rfl) ⟨10618613, by rfl⟩ : syracuseStep 14158151 = 21237227) B21237227
theorem B17918759 : Blo 1863633 17918759 := bstep (se 1 (by rfl) ⟨13439069, by rfl⟩ : syracuseStep 17918759 = 26878139) B26878139
theorem B2796779 : Blo 1863633 2796779 := bstep (se 1 (by rfl) ⟨2097584, by rfl⟩ : syracuseStep 2796779 = 4195169) B4195169
theorem B15928811 : Blo 1863633 15928811 := bstep (se 1 (by rfl) ⟨11946608, by rfl⟩ : syracuseStep 15928811 = 23893217) B23893217
theorem B1863751 : Blo 1863633 1863751 := bstep (se 1 (by rfl) ⟨1397813, by rfl⟩ : syracuseStep 1863751 = 2795627) B2795627
theorem B1864175 : Blo 1863633 1864175 := bstep (se 1 (by rfl) ⟨1398131, by rfl⟩ : syracuseStep 1864175 = 2796263) B2796263
theorem B1864479 : Blo 1863633 1864479 := bstep (se 1 (by rfl) ⟨1398359, by rfl⟩ : syracuseStep 1864479 = 2796719) B2796719
theorem B10081273 : Blo 1863633 10081273 := bstep (se 2 (by rfl) ⟨3780477, by rfl⟩ : syracuseStep 10081273 = 7560955) B7560955
theorem B23885117 : Blo 1863633 23885117 := bstep (se 3 (by rfl) ⟨4478459, by rfl⟩ : syracuseStep 23885117 = 8956919) B8956919
theorem B1865119 : Blo 1863633 1865119 := bstep (se 1 (by rfl) ⟨1398839, by rfl⟩ : syracuseStep 1865119 = 2797679) B2797679
theorem B20166569 : Blo 1863633 20166569 := bstep (se 2 (by rfl) ⟨7562463, by rfl⟩ : syracuseStep 20166569 = 15124927) B15124927
theorem B17913959 : Blo 1863633 17913959 := bstep (se 1 (by rfl) ⟨13435469, by rfl⟩ : syracuseStep 17913959 = 26870939) B26870939
theorem B290544353 : Blo 1863633 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B4193531 : Blo 1863633 4193531 := bstep (se 1 (by rfl) ⟨3145148, by rfl⟩ : syracuseStep 4193531 = 6290297) B6290297
theorem B10075499 : Blo 1863633 10075499 := bstep (se 1 (by rfl) ⟨7556624, by rfl⟩ : syracuseStep 10075499 = 15113249) B15113249
theorem B3538399 : Blo 1863633 3538399 := bstep (se 1 (by rfl) ⟨2653799, by rfl⟩ : syracuseStep 3538399 = 5307599) B5307599
theorem B4194377 : Blo 1863633 4194377 := bstep (se 2 (by rfl) ⟨1572891, by rfl⟩ : syracuseStep 4194377 = 3145783) B3145783
theorem B6291539 : Blo 1863633 6291539 := bstep (se 1 (by rfl) ⟨4718654, by rfl⟩ : syracuseStep 6291539 = 9437309) B9437309
theorem B77553857 : Blo 1863633 77553857 := bstep (se 2 (by rfl) ⟨29082696, by rfl⟩ : syracuseStep 77553857 = 58165393) B58165393
theorem B172261619 : Blo 1863633 172261619 := bstep (se 1 (by rfl) ⟨129196214, by rfl⟩ : syracuseStep 172261619 = 258392429) B258392429
theorem B3145979 : Blo 1863633 3145979 := bstep (se 1 (by rfl) ⟨2359484, by rfl⟩ : syracuseStep 3145979 = 4718969) B4718969
theorem B10617317 : Blo 1863633 10617317 := bstep (se 4 (by rfl) ⟨995373, by rfl⟩ : syracuseStep 10617317 = 1990747) B1990747
theorem B13444379 : Blo 1863633 13444379 := bstep (se 1 (by rfl) ⟨10083284, by rfl⟩ : syracuseStep 13444379 = 20166569) B20166569
theorem B9438767 : Blo 1863633 9438767 := bstep (se 1 (by rfl) ⟨7079075, by rfl⟩ : syracuseStep 9438767 = 14158151) B14158151
theorem B11945839 : Blo 1863633 11945839 := bstep (se 1 (by rfl) ⟨8959379, by rfl⟩ : syracuseStep 11945839 = 17918759) B17918759
theorem B2795687 : Blo 1863633 2795687 := bstep (se 1 (by rfl) ⟨2096765, by rfl⟩ : syracuseStep 2795687 = 4193531) B4193531
theorem B10619207 : Blo 1863633 10619207 := bstep (se 1 (by rfl) ⟨7964405, by rfl⟩ : syracuseStep 10619207 = 15928811) B15928811
theorem B21228479 : Blo 1863633 21228479 := bstep (se 1 (by rfl) ⟨15921359, by rfl⟩ : syracuseStep 21228479 = 31842719) B31842719
theorem B2239807 : Blo 1863633 2239807 := bstep (se 1 (by rfl) ⟨1679855, by rfl⟩ : syracuseStep 2239807 = 3359711) B3359711
theorem B2797097 : Blo 1863633 2797097 := bstep (se 2 (by rfl) ⟨1048911, by rfl⟩ : syracuseStep 2797097 = 2097823) B2097823
theorem B2797295 : Blo 1863633 2797295 := bstep (se 1 (by rfl) ⟨2097971, by rfl⟩ : syracuseStep 2797295 = 4195943) B4195943
theorem B193696235 : Blo 1863633 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B1864519 : Blo 1863633 1864519 := bstep (se 1 (by rfl) ⟨1398389, by rfl⟩ : syracuseStep 1864519 = 2796779) B2796779
theorem B698636285 : Blo 1863633 698636285 := bstep (se 3 (by rfl) ⟨130994303, by rfl⟩ : syracuseStep 698636285 = 261988607) B261988607
theorem B15923411 : Blo 1863633 15923411 := bstep (se 1 (by rfl) ⟨11942558, by rfl⟩ : syracuseStep 15923411 = 23885117) B23885117
theorem B48453983 : Blo 1863633 48453983 := bstep (se 1 (by rfl) ⟨36340487, by rfl⟩ : syracuseStep 48453983 = 72680975) B72680975
theorem B13441697 : Blo 1863633 13441697 := bstep (se 2 (by rfl) ⟨5040636, by rfl⟩ : syracuseStep 13441697 = 10081273) B10081273
theorem B11942639 : Blo 1863633 11942639 := bstep (se 1 (by rfl) ⟨8956979, by rfl⟩ : syracuseStep 11942639 = 17913959) B17913959
theorem B4717865 : Blo 1863633 4717865 := bstep (se 2 (by rfl) ⟨1769199, by rfl⟩ : syracuseStep 4717865 = 3538399) B3538399
theorem B6716999 : Blo 1863633 6716999 := bstep (se 1 (by rfl) ⟨5037749, by rfl⟩ : syracuseStep 6716999 = 10075499) B10075499
theorem B4194359 : Blo 1863633 4194359 := bstep (se 1 (by rfl) ⟨3145769, by rfl⟩ : syracuseStep 4194359 = 6291539) B6291539
theorem B2097319 : Blo 1863633 2097319 := bstep (se 1 (by rfl) ⟨1572989, by rfl⟩ : syracuseStep 2097319 = 3145979) B3145979
theorem B7078211 : Blo 1863633 7078211 := bstep (se 1 (by rfl) ⟨5308658, by rfl⟩ : syracuseStep 7078211 = 10617317) B10617317
theorem B129130823 : Blo 1863633 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B8962919 : Blo 1863633 8962919 := bstep (se 1 (by rfl) ⟨6722189, by rfl⟩ : syracuseStep 8962919 = 13444379) B13444379
theorem B6292511 : Blo 1863633 6292511 := bstep (se 1 (by rfl) ⟨4719383, by rfl⟩ : syracuseStep 6292511 = 9438767) B9438767
theorem B465757523 : Blo 1863633 465757523 := bstep (se 1 (by rfl) ⟨349318142, by rfl⟩ : syracuseStep 465757523 = 698636285) B698636285
theorem B7079471 : Blo 1863633 7079471 := bstep (se 1 (by rfl) ⟨5309603, by rfl⟩ : syracuseStep 7079471 = 10619207) B10619207
theorem B32302655 : Blo 1863633 32302655 := bstep (se 1 (by rfl) ⟨24226991, by rfl⟩ : syracuseStep 32302655 = 48453983) B48453983
theorem B15927785 : Blo 1863633 15927785 := bstep (se 2 (by rfl) ⟨5972919, by rfl⟩ : syracuseStep 15927785 = 11945839) B11945839
theorem B2796251 : Blo 1863633 2796251 := bstep (se 1 (by rfl) ⟨2097188, by rfl⟩ : syracuseStep 2796251 = 4194377) B4194377
theorem B51702571 : Blo 1863633 51702571 := bstep (se 1 (by rfl) ⟨38776928, by rfl⟩ : syracuseStep 51702571 = 77553857) B77553857
theorem B1863791 : Blo 1863633 1863791 := bstep (se 1 (by rfl) ⟨1397843, by rfl⟩ : syracuseStep 1863791 = 2795687) B2795687
theorem B2986409 : Blo 1863633 2986409 := bstep (se 2 (by rfl) ⟨1119903, by rfl⟩ : syracuseStep 2986409 = 2239807) B2239807
theorem B14152319 : Blo 1863633 14152319 := bstep (se 1 (by rfl) ⟨10614239, by rfl⟩ : syracuseStep 14152319 = 21228479) B21228479
theorem B1864731 : Blo 1863633 1864731 := bstep (se 1 (by rfl) ⟨1398548, by rfl⟩ : syracuseStep 1864731 = 2797097) B2797097
theorem B4477999 : Blo 1863633 4477999 := bstep (se 1 (by rfl) ⟨3358499, by rfl⟩ : syracuseStep 4477999 = 6716999) B6716999
theorem B1864863 : Blo 1863633 1864863 := bstep (se 1 (by rfl) ⟨1398647, by rfl⟩ : syracuseStep 1864863 = 2797295) B2797295
theorem B114841079 : Blo 1863633 114841079 := bstep (se 1 (by rfl) ⟨86130809, by rfl⟩ : syracuseStep 114841079 = 172261619) B172261619
theorem B10615607 : Blo 1863633 10615607 := bstep (se 1 (by rfl) ⟨7961705, by rfl⟩ : syracuseStep 10615607 = 15923411) B15923411
theorem B8961131 : Blo 1863633 8961131 := bstep (se 1 (by rfl) ⟨6720848, by rfl⟩ : syracuseStep 8961131 = 13441697) B13441697
theorem B7961759 : Blo 1863633 7961759 := bstep (se 1 (by rfl) ⟨5971319, by rfl⟩ : syracuseStep 7961759 = 11942639) B11942639
theorem B3145243 : Blo 1863633 3145243 := bstep (se 1 (by rfl) ⟨2358932, by rfl⟩ : syracuseStep 3145243 = 4717865) B4717865
theorem B4718807 : Blo 1863633 4718807 := bstep (se 1 (by rfl) ⟨3539105, by rfl⟩ : syracuseStep 4718807 = 7078211) B7078211
theorem B4195007 : Blo 1863633 4195007 := bstep (se 1 (by rfl) ⟨3146255, by rfl⟩ : syracuseStep 4195007 = 6292511) B6292511
theorem B4719647 : Blo 1863633 4719647 := bstep (se 1 (by rfl) ⟨3539735, by rfl⟩ : syracuseStep 4719647 = 7079471) B7079471
theorem B68936761 : Blo 1863633 68936761 := bstep (se 2 (by rfl) ⟨25851285, by rfl⟩ : syracuseStep 68936761 = 51702571) B51702571
theorem B7963757 : Blo 1863633 7963757 := bstep (se 3 (by rfl) ⟨1493204, by rfl⟩ : syracuseStep 7963757 = 2986409) B2986409
theorem B10618523 : Blo 1863633 10618523 := bstep (se 1 (by rfl) ⟨7963892, by rfl⟩ : syracuseStep 10618523 = 15927785) B15927785
theorem B5974087 : Blo 1863633 5974087 := bstep (se 1 (by rfl) ⟨4480565, by rfl⟩ : syracuseStep 5974087 = 8961131) B8961131
theorem B2796239 : Blo 1863633 2796239 := bstep (se 1 (by rfl) ⟨2097179, by rfl⟩ : syracuseStep 2796239 = 4194359) B4194359
theorem B2796425 : Blo 1863633 2796425 := bstep (se 2 (by rfl) ⟨1048659, by rfl⟩ : syracuseStep 2796425 = 2097319) B2097319
theorem B5975279 : Blo 1863633 5975279 := bstep (se 1 (by rfl) ⟨4481459, by rfl⟩ : syracuseStep 5975279 = 8962919) B8962919
theorem B310505015 : Blo 1863633 310505015 := bstep (se 1 (by rfl) ⟨232878761, by rfl⟩ : syracuseStep 310505015 = 465757523) B465757523
theorem B1864167 : Blo 1863633 1864167 := bstep (se 1 (by rfl) ⟨1398125, by rfl⟩ : syracuseStep 1864167 = 2796251) B2796251
theorem B86087215 : Blo 1863633 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B9434879 : Blo 1863633 9434879 := bstep (se 1 (by rfl) ⟨7076159, by rfl⟩ : syracuseStep 9434879 = 14152319) B14152319
theorem B76560719 : Blo 1863633 76560719 := bstep (se 1 (by rfl) ⟨57420539, by rfl⟩ : syracuseStep 76560719 = 114841079) B114841079
theorem B21535103 : Blo 1863633 21535103 := bstep (se 1 (by rfl) ⟨16151327, by rfl⟩ : syracuseStep 21535103 = 32302655) B32302655
theorem B5970665 : Blo 1863633 5970665 := bstep (se 2 (by rfl) ⟨2238999, by rfl⟩ : syracuseStep 5970665 = 4477999) B4477999
theorem B7077071 : Blo 1863633 7077071 := bstep (se 1 (by rfl) ⟨5307803, by rfl⟩ : syracuseStep 7077071 = 10615607) B10615607
theorem B4193657 : Blo 1863633 4193657 := bstep (se 2 (by rfl) ⟨1572621, by rfl⟩ : syracuseStep 4193657 = 3145243) B3145243
theorem B5307839 : Blo 1863633 5307839 := bstep (se 1 (by rfl) ⟨3980879, by rfl⟩ : syracuseStep 5307839 = 7961759) B7961759
theorem B3145871 : Blo 1863633 3145871 := bstep (se 1 (by rfl) ⟨2359403, by rfl⟩ : syracuseStep 3145871 = 4718807) B4718807
theorem B3146431 : Blo 1863633 3146431 := bstep (se 1 (by rfl) ⟨2359823, by rfl⟩ : syracuseStep 3146431 = 4719647) B4719647
theorem B5309171 : Blo 1863633 5309171 := bstep (se 1 (by rfl) ⟨3981878, by rfl⟩ : syracuseStep 5309171 = 7963757) B7963757
theorem B204161917 : Blo 1863633 204161917 := bstep (se 3 (by rfl) ⟨38280359, by rfl⟩ : syracuseStep 204161917 = 76560719) B76560719
theorem B57426941 : Blo 1863633 57426941 := bstep (se 3 (by rfl) ⟨10767551, by rfl⟩ : syracuseStep 57426941 = 21535103) B21535103
theorem B7079015 : Blo 1863633 7079015 := bstep (se 1 (by rfl) ⟨5309261, by rfl⟩ : syracuseStep 7079015 = 10618523) B10618523
theorem B91915681 : Blo 1863633 91915681 := bstep (se 2 (by rfl) ⟨34468380, by rfl⟩ : syracuseStep 91915681 = 68936761) B68936761
theorem B3983519 : Blo 1863633 3983519 := bstep (se 1 (by rfl) ⟨2987639, by rfl⟩ : syracuseStep 3983519 = 5975279) B5975279
theorem B2795771 : Blo 1863633 2795771 := bstep (se 1 (by rfl) ⟨2096828, by rfl⟩ : syracuseStep 2795771 = 4193657) B4193657
theorem B7965449 : Blo 1863633 7965449 := bstep (se 2 (by rfl) ⟨2987043, by rfl⟩ : syracuseStep 7965449 = 5974087) B5974087
theorem B2796671 : Blo 1863633 2796671 := bstep (se 1 (by rfl) ⟨2097503, by rfl⟩ : syracuseStep 2796671 = 4195007) B4195007
theorem B1864159 : Blo 1863633 1864159 := bstep (se 1 (by rfl) ⟨1398119, by rfl⟩ : syracuseStep 1864159 = 2796239) B2796239
theorem B1864283 : Blo 1863633 1864283 := bstep (se 1 (by rfl) ⟨1398212, by rfl⟩ : syracuseStep 1864283 = 2796425) B2796425
theorem B114782953 : Blo 1863633 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B6289919 : Blo 1863633 6289919 := bstep (se 1 (by rfl) ⟨4717439, by rfl⟩ : syracuseStep 6289919 = 9434879) B9434879
theorem B828013373 : Blo 1863633 828013373 := bstep (se 3 (by rfl) ⟨155252507, by rfl⟩ : syracuseStep 828013373 = 310505015) B310505015
theorem B3980443 : Blo 1863633 3980443 := bstep (se 1 (by rfl) ⟨2985332, by rfl⟩ : syracuseStep 3980443 = 5970665) B5970665
theorem B4718047 : Blo 1863633 4718047 := bstep (se 1 (by rfl) ⟨3538535, by rfl⟩ : syracuseStep 4718047 = 7077071) B7077071
theorem B3538559 : Blo 1863633 3538559 := bstep (se 1 (by rfl) ⟨2653919, by rfl⟩ : syracuseStep 3538559 = 5307839) B5307839
theorem B2097247 : Blo 1863633 2097247 := bstep (se 1 (by rfl) ⟨1572935, by rfl⟩ : syracuseStep 2097247 = 3145871) B3145871
theorem B3539447 : Blo 1863633 3539447 := bstep (se 1 (by rfl) ⟨2654585, by rfl⟩ : syracuseStep 3539447 = 5309171) B5309171
theorem B4719343 : Blo 1863633 4719343 := bstep (se 1 (by rfl) ⟨3539507, by rfl⟩ : syracuseStep 4719343 = 7079015) B7079015
theorem B4195241 : Blo 1863633 4195241 := bstep (se 2 (by rfl) ⟨1573215, by rfl⟩ : syracuseStep 4195241 = 3146431) B3146431
theorem B153043937 : Blo 1863633 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B2655679 : Blo 1863633 2655679 := bstep (se 1 (by rfl) ⟨1991759, by rfl⟩ : syracuseStep 2655679 = 3983519) B3983519
theorem B5310299 : Blo 1863633 5310299 := bstep (se 1 (by rfl) ⟨3982724, by rfl⟩ : syracuseStep 5310299 = 7965449) B7965449
theorem B122554241 : Blo 1863633 122554241 := bstep (se 2 (by rfl) ⟨45957840, by rfl⟩ : syracuseStep 122554241 = 91915681) B91915681
theorem B272215889 : Blo 1863633 272215889 := bstep (se 2 (by rfl) ⟨102080958, by rfl⟩ : syracuseStep 272215889 = 204161917) B204161917
theorem B1863847 : Blo 1863633 1863847 := bstep (se 1 (by rfl) ⟨1397885, by rfl⟩ : syracuseStep 1863847 = 2795771) B2795771
theorem B1864447 : Blo 1863633 1864447 := bstep (se 1 (by rfl) ⟨1398335, by rfl⟩ : syracuseStep 1864447 = 2796671) B2796671
theorem B153138509 : Blo 1863633 153138509 := bstep (se 3 (by rfl) ⟨28713470, by rfl⟩ : syracuseStep 153138509 = 57426941) B57426941
theorem B5307257 : Blo 1863633 5307257 := bstep (se 2 (by rfl) ⟨1990221, by rfl⟩ : syracuseStep 5307257 = 3980443) B3980443
theorem B4193279 : Blo 1863633 4193279 := bstep (se 1 (by rfl) ⟨3144959, by rfl⟩ : syracuseStep 4193279 = 6289919) B6289919
theorem B552008915 : Blo 1863633 552008915 := bstep (se 1 (by rfl) ⟨414006686, by rfl⟩ : syracuseStep 552008915 = 828013373) B828013373
theorem B6290729 : Blo 1863633 6290729 := bstep (se 2 (by rfl) ⟨2359023, by rfl⟩ : syracuseStep 6290729 = 4718047) B4718047
theorem B2359039 : Blo 1863633 2359039 := bstep (se 1 (by rfl) ⟨1769279, by rfl⟩ : syracuseStep 2359039 = 3538559) B3538559
theorem B2359631 : Blo 1863633 2359631 := bstep (se 1 (by rfl) ⟨1769723, by rfl⟩ : syracuseStep 2359631 = 3539447) B3539447
theorem B6292457 : Blo 1863633 6292457 := bstep (se 2 (by rfl) ⟨2359671, by rfl⟩ : syracuseStep 6292457 = 4719343) B4719343
theorem B3540199 : Blo 1863633 3540199 := bstep (se 1 (by rfl) ⟨2655149, by rfl⟩ : syracuseStep 3540199 = 5310299) B5310299
theorem B3540905 : Blo 1863633 3540905 := bstep (se 2 (by rfl) ⟨1327839, by rfl⟩ : syracuseStep 3540905 = 2655679) B2655679
theorem B2795519 : Blo 1863633 2795519 := bstep (se 1 (by rfl) ⟨2096639, by rfl⟩ : syracuseStep 2795519 = 4193279) B4193279
theorem B2796329 : Blo 1863633 2796329 := bstep (se 2 (by rfl) ⟨1048623, by rfl⟩ : syracuseStep 2796329 = 2097247) B2097247
theorem B2796827 : Blo 1863633 2796827 := bstep (se 1 (by rfl) ⟨2097620, by rfl⟩ : syracuseStep 2796827 = 4195241) B4195241
theorem B102092339 : Blo 1863633 102092339 := bstep (se 1 (by rfl) ⟨76569254, by rfl⟩ : syracuseStep 102092339 = 153138509) B153138509
theorem B81702827 : Blo 1863633 81702827 := bstep (se 1 (by rfl) ⟨61277120, by rfl⟩ : syracuseStep 81702827 = 122554241) B122554241
theorem B368005943 : Blo 1863633 368005943 := bstep (se 1 (by rfl) ⟨276004457, by rfl⟩ : syracuseStep 368005943 = 552008915) B552008915
theorem B102029291 : Blo 1863633 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B3538171 : Blo 1863633 3538171 := bstep (se 1 (by rfl) ⟨2653628, by rfl⟩ : syracuseStep 3538171 = 5307257) B5307257
theorem B4193819 : Blo 1863633 4193819 := bstep (se 1 (by rfl) ⟨3145364, by rfl⟩ : syracuseStep 4193819 = 6290729) B6290729
theorem B3145385 : Blo 1863633 3145385 := bstep (se 2 (by rfl) ⟨1179519, by rfl⟩ : syracuseStep 3145385 = 2359039) B2359039
theorem B181477259 : Blo 1863633 181477259 := bstep (se 1 (by rfl) ⟨136107944, by rfl⟩ : syracuseStep 181477259 = 272215889) B272215889
theorem B4194971 : Blo 1863633 4194971 := bstep (se 1 (by rfl) ⟨3146228, by rfl⟩ : syracuseStep 4194971 = 6292457) B6292457
theorem B6292349 : Blo 1863633 6292349 := bstep (se 3 (by rfl) ⟨1179815, by rfl⟩ : syracuseStep 6292349 = 2359631) B2359631
theorem B2360603 : Blo 1863633 2360603 := bstep (se 1 (by rfl) ⟨1770452, by rfl⟩ : syracuseStep 2360603 = 3540905) B3540905
theorem B68019527 : Blo 1863633 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B4720265 : Blo 1863633 4720265 := bstep (se 2 (by rfl) ⟨1770099, by rfl⟩ : syracuseStep 4720265 = 3540199) B3540199
theorem B2795879 : Blo 1863633 2795879 := bstep (se 1 (by rfl) ⟨2096909, by rfl⟩ : syracuseStep 2795879 = 4193819) B4193819
theorem B68061559 : Blo 1863633 68061559 := bstep (se 1 (by rfl) ⟨51046169, by rfl⟩ : syracuseStep 68061559 = 102092339) B102092339
theorem B245337295 : Blo 1863633 245337295 := bstep (se 1 (by rfl) ⟨184002971, by rfl⟩ : syracuseStep 245337295 = 368005943) B368005943
theorem B1863679 : Blo 1863633 1863679 := bstep (se 1 (by rfl) ⟨1397759, by rfl⟩ : syracuseStep 1863679 = 2795519) B2795519
theorem B1864219 : Blo 1863633 1864219 := bstep (se 1 (by rfl) ⟨1398164, by rfl⟩ : syracuseStep 1864219 = 2796329) B2796329
theorem B1864551 : Blo 1863633 1864551 := bstep (se 1 (by rfl) ⟨1398413, by rfl⟩ : syracuseStep 1864551 = 2796827) B2796827
theorem B120984839 : Blo 1863633 120984839 := bstep (se 1 (by rfl) ⟨90738629, by rfl⟩ : syracuseStep 120984839 = 181477259) B181477259
theorem B4717561 : Blo 1863633 4717561 := bstep (se 2 (by rfl) ⟨1769085, by rfl⟩ : syracuseStep 4717561 = 3538171) B3538171
theorem B2096923 : Blo 1863633 2096923 := bstep (se 1 (by rfl) ⟨1572692, by rfl⟩ : syracuseStep 2096923 = 3145385) B3145385
theorem B54468551 : Blo 1863633 54468551 := bstep (se 1 (by rfl) ⟨40851413, by rfl⟩ : syracuseStep 54468551 = 81702827) B81702827
theorem B4194899 : Blo 1863633 4194899 := bstep (se 1 (by rfl) ⟨3146174, by rfl⟩ : syracuseStep 4194899 = 6292349) B6292349
theorem B3146843 : Blo 1863633 3146843 := bstep (se 1 (by rfl) ⟨2360132, by rfl⟩ : syracuseStep 3146843 = 4720265) B4720265
theorem B327116393 : Blo 1863633 327116393 := bstep (se 2 (by rfl) ⟨122668647, by rfl⟩ : syracuseStep 327116393 = 245337295) B245337295
theorem B2795897 : Blo 1863633 2795897 := bstep (se 2 (by rfl) ⟨1048461, by rfl⟩ : syracuseStep 2795897 = 2096923) B2096923
theorem B2796647 : Blo 1863633 2796647 := bstep (se 1 (by rfl) ⟨2097485, by rfl⟩ : syracuseStep 2796647 = 4194971) B4194971
theorem B6294941 : Blo 1863633 6294941 := bstep (se 3 (by rfl) ⟨1180301, by rfl⟩ : syracuseStep 6294941 = 2360603) B2360603
theorem B45346351 : Blo 1863633 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B1863919 : Blo 1863633 1863919 := bstep (se 1 (by rfl) ⟨1397939, by rfl⟩ : syracuseStep 1863919 = 2795879) B2795879
theorem B145249469 : Blo 1863633 145249469 := bstep (se 3 (by rfl) ⟨27234275, by rfl⟩ : syracuseStep 145249469 = 54468551) B54468551
theorem B90748745 : Blo 1863633 90748745 := bstep (se 2 (by rfl) ⟨34030779, by rfl⟩ : syracuseStep 90748745 = 68061559) B68061559
theorem B80656559 : Blo 1863633 80656559 := bstep (se 1 (by rfl) ⟨60492419, by rfl⟩ : syracuseStep 80656559 = 120984839) B120984839
theorem B6290081 : Blo 1863633 6290081 := bstep (se 2 (by rfl) ⟨2358780, by rfl⟩ : syracuseStep 6290081 = 4717561) B4717561
theorem B2097895 : Blo 1863633 2097895 := bstep (se 1 (by rfl) ⟨1573421, by rfl⟩ : syracuseStep 2097895 = 3146843) B3146843
theorem B60499163 : Blo 1863633 60499163 := bstep (se 1 (by rfl) ⟨45374372, by rfl⟩ : syracuseStep 60499163 = 90748745) B90748745
theorem B4196627 : Blo 1863633 4196627 := bstep (se 1 (by rfl) ⟨3147470, by rfl⟩ : syracuseStep 4196627 = 6294941) B6294941
theorem B2796599 : Blo 1863633 2796599 := bstep (se 1 (by rfl) ⟨2097449, by rfl⟩ : syracuseStep 2796599 = 4194899) B4194899
theorem B96832979 : Blo 1863633 96832979 := bstep (se 1 (by rfl) ⟨72624734, by rfl⟩ : syracuseStep 96832979 = 145249469) B145249469
theorem B1863931 : Blo 1863633 1863931 := bstep (se 1 (by rfl) ⟨1397948, by rfl⟩ : syracuseStep 1863931 = 2795897) B2795897
theorem B60461801 : Blo 1863633 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B1864431 : Blo 1863633 1864431 := bstep (se 1 (by rfl) ⟨1398323, by rfl⟩ : syracuseStep 1864431 = 2796647) B2796647
theorem B218077595 : Blo 1863633 218077595 := bstep (se 1 (by rfl) ⟨163558196, by rfl⟩ : syracuseStep 218077595 = 327116393) B327116393
theorem B53771039 : Blo 1863633 53771039 := bstep (se 1 (by rfl) ⟨40328279, by rfl⟩ : syracuseStep 53771039 = 80656559) B80656559
theorem B4193387 : Blo 1863633 4193387 := bstep (se 1 (by rfl) ⟨3145040, by rfl⟩ : syracuseStep 4193387 = 6290081) B6290081
theorem B145385063 : Blo 1863633 145385063 := bstep (se 1 (by rfl) ⟨109038797, by rfl⟩ : syracuseStep 145385063 = 218077595) B218077595
theorem B2795591 : Blo 1863633 2795591 := bstep (se 1 (by rfl) ⟨2096693, by rfl⟩ : syracuseStep 2795591 = 4193387) B4193387
theorem B64555319 : Blo 1863633 64555319 := bstep (se 1 (by rfl) ⟨48416489, by rfl⟩ : syracuseStep 64555319 = 96832979) B96832979
theorem B40307867 : Blo 1863633 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B40332775 : Blo 1863633 40332775 := bstep (se 1 (by rfl) ⟨30249581, by rfl⟩ : syracuseStep 40332775 = 60499163) B60499163
theorem B2797193 : Blo 1863633 2797193 := bstep (se 2 (by rfl) ⟨1048947, by rfl⟩ : syracuseStep 2797193 = 2097895) B2097895
theorem B2797751 : Blo 1863633 2797751 := bstep (se 1 (by rfl) ⟨2098313, by rfl⟩ : syracuseStep 2797751 = 4196627) B4196627
theorem B1864399 : Blo 1863633 1864399 := bstep (se 1 (by rfl) ⟨1398299, by rfl⟩ : syracuseStep 1864399 = 2796599) B2796599
theorem B35847359 : Blo 1863633 35847359 := bstep (se 1 (by rfl) ⟨26885519, by rfl⟩ : syracuseStep 35847359 = 53771039) B53771039
theorem B172147517 : Blo 1863633 172147517 := bstep (se 3 (by rfl) ⟨32277659, by rfl⟩ : syracuseStep 172147517 = 64555319) B64555319
theorem B26871911 : Blo 1863633 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B23898239 : Blo 1863633 23898239 := bstep (se 1 (by rfl) ⟨17923679, by rfl⟩ : syracuseStep 23898239 = 35847359) B35847359
theorem B96923375 : Blo 1863633 96923375 := bstep (se 1 (by rfl) ⟨72692531, by rfl⟩ : syracuseStep 96923375 = 145385063) B145385063
theorem B1863727 : Blo 1863633 1863727 := bstep (se 1 (by rfl) ⟨1397795, by rfl⟩ : syracuseStep 1863727 = 2795591) B2795591
theorem B53777033 : Blo 1863633 53777033 := bstep (se 2 (by rfl) ⟨20166387, by rfl⟩ : syracuseStep 53777033 = 40332775) B40332775
theorem B1864795 : Blo 1863633 1864795 := bstep (se 1 (by rfl) ⟨1398596, by rfl⟩ : syracuseStep 1864795 = 2797193) B2797193
theorem B1865167 : Blo 1863633 1865167 := bstep (se 1 (by rfl) ⟨1398875, by rfl⟩ : syracuseStep 1865167 = 2797751) B2797751
theorem B35851355 : Blo 1863633 35851355 := bstep (se 1 (by rfl) ⟨26888516, by rfl⟩ : syracuseStep 35851355 = 53777033) B53777033
theorem B114765011 : Blo 1863633 114765011 := bstep (se 1 (by rfl) ⟨86073758, by rfl⟩ : syracuseStep 114765011 = 172147517) B172147517
theorem B64615583 : Blo 1863633 64615583 := bstep (se 1 (by rfl) ⟨48461687, by rfl⟩ : syracuseStep 64615583 = 96923375) B96923375
theorem B17914607 : Blo 1863633 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B15932159 : Blo 1863633 15932159 := bstep (se 1 (by rfl) ⟨11949119, by rfl⟩ : syracuseStep 15932159 = 23898239) B23898239
theorem B43077055 : Blo 1863633 43077055 := bstep (se 1 (by rfl) ⟨32307791, by rfl⟩ : syracuseStep 43077055 = 64615583) B64615583
theorem B10621439 : Blo 1863633 10621439 := bstep (se 1 (by rfl) ⟨7966079, by rfl⟩ : syracuseStep 10621439 = 15932159) B15932159
theorem B23900903 : Blo 1863633 23900903 := bstep (se 1 (by rfl) ⟨17925677, by rfl⟩ : syracuseStep 23900903 = 35851355) B35851355
theorem B76510007 : Blo 1863633 76510007 := bstep (se 1 (by rfl) ⟨57382505, by rfl⟩ : syracuseStep 76510007 = 114765011) B114765011
theorem B11943071 : Blo 1863633 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B15933935 : Blo 1863633 15933935 := bstep (se 1 (by rfl) ⟨11950451, by rfl⟩ : syracuseStep 15933935 = 23900903) B23900903
theorem B57436073 : Blo 1863633 57436073 := bstep (se 2 (by rfl) ⟨21538527, by rfl⟩ : syracuseStep 57436073 = 43077055) B43077055
theorem B7080959 : Blo 1863633 7080959 := bstep (se 1 (by rfl) ⟨5310719, by rfl⟩ : syracuseStep 7080959 = 10621439) B10621439
theorem B51006671 : Blo 1863633 51006671 := bstep (se 1 (by rfl) ⟨38255003, by rfl⟩ : syracuseStep 51006671 = 76510007) B76510007
theorem B7962047 : Blo 1863633 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B38290715 : Blo 1863633 38290715 := bstep (se 1 (by rfl) ⟨28718036, by rfl⟩ : syracuseStep 38290715 = 57436073) B57436073
theorem B4720639 : Blo 1863633 4720639 := bstep (se 1 (by rfl) ⟨3540479, by rfl⟩ : syracuseStep 4720639 = 7080959) B7080959
theorem B10622623 : Blo 1863633 10622623 := bstep (se 1 (by rfl) ⟨7966967, by rfl⟩ : syracuseStep 10622623 = 15933935) B15933935
theorem B34004447 : Blo 1863633 34004447 := bstep (se 1 (by rfl) ⟨25503335, by rfl⟩ : syracuseStep 34004447 = 51006671) B51006671
theorem B5308031 : Blo 1863633 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B25527143 : Blo 1863633 25527143 := bstep (se 1 (by rfl) ⟨19145357, by rfl⟩ : syracuseStep 25527143 = 38290715) B38290715
theorem B22669631 : Blo 1863633 22669631 := bstep (se 1 (by rfl) ⟨17002223, by rfl⟩ : syracuseStep 22669631 = 34004447) B34004447
theorem B6294185 : Blo 1863633 6294185 := bstep (se 2 (by rfl) ⟨2360319, by rfl⟩ : syracuseStep 6294185 = 4720639) B4720639
theorem B14154749 : Blo 1863633 14154749 := bstep (se 3 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 14154749 = 5308031) B5308031
theorem B14163497 : Blo 1863633 14163497 := bstep (se 2 (by rfl) ⟨5311311, by rfl⟩ : syracuseStep 14163497 = 10622623) B10622623
theorem B4196123 : Blo 1863633 4196123 := bstep (se 1 (by rfl) ⟨3147092, by rfl⟩ : syracuseStep 4196123 = 6294185) B6294185
theorem B17018095 : Blo 1863633 17018095 := bstep (se 1 (by rfl) ⟨12763571, by rfl⟩ : syracuseStep 17018095 = 25527143) B25527143
theorem B9442331 : Blo 1863633 9442331 := bstep (se 1 (by rfl) ⟨7081748, by rfl⟩ : syracuseStep 9442331 = 14163497) B14163497
theorem B15113087 : Blo 1863633 15113087 := bstep (se 1 (by rfl) ⟨11334815, by rfl⟩ : syracuseStep 15113087 = 22669631) B22669631
theorem B9436499 : Blo 1863633 9436499 := bstep (se 1 (by rfl) ⟨7077374, by rfl⟩ : syracuseStep 9436499 = 14154749) B14154749
theorem B6294887 : Blo 1863633 6294887 := bstep (se 1 (by rfl) ⟨4721165, by rfl⟩ : syracuseStep 6294887 = 9442331) B9442331
theorem B2797415 : Blo 1863633 2797415 := bstep (se 1 (by rfl) ⟨2098061, by rfl⟩ : syracuseStep 2797415 = 4196123) B4196123
theorem B22690793 : Blo 1863633 22690793 := bstep (se 2 (by rfl) ⟨8509047, by rfl⟩ : syracuseStep 22690793 = 17018095) B17018095
theorem B10075391 : Blo 1863633 10075391 := bstep (se 1 (by rfl) ⟨7556543, by rfl⟩ : syracuseStep 10075391 = 15113087) B15113087
theorem B6290999 : Blo 1863633 6290999 := bstep (se 1 (by rfl) ⟨4718249, by rfl⟩ : syracuseStep 6290999 = 9436499) B9436499
theorem B4196591 : Blo 1863633 4196591 := bstep (se 1 (by rfl) ⟨3147443, by rfl⟩ : syracuseStep 4196591 = 6294887) B6294887
theorem B15127195 : Blo 1863633 15127195 := bstep (se 1 (by rfl) ⟨11345396, by rfl⟩ : syracuseStep 15127195 = 22690793) B22690793
theorem B1864943 : Blo 1863633 1864943 := bstep (se 1 (by rfl) ⟨1398707, by rfl⟩ : syracuseStep 1864943 = 2797415) B2797415
theorem B6716927 : Blo 1863633 6716927 := bstep (se 1 (by rfl) ⟨5037695, by rfl⟩ : syracuseStep 6716927 = 10075391) B10075391
theorem B4193999 : Blo 1863633 4193999 := bstep (se 1 (by rfl) ⟨3145499, by rfl⟩ : syracuseStep 4193999 = 6290999) B6290999
theorem B20169593 : Blo 1863633 20169593 := bstep (se 2 (by rfl) ⟨7563597, by rfl⟩ : syracuseStep 20169593 = 15127195) B15127195
theorem B2795999 : Blo 1863633 2795999 := bstep (se 1 (by rfl) ⟨2096999, by rfl⟩ : syracuseStep 2795999 = 4193999) B4193999
theorem B2797727 : Blo 1863633 2797727 := bstep (se 1 (by rfl) ⟨2098295, by rfl⟩ : syracuseStep 2797727 = 4196591) B4196591
theorem B4477951 : Blo 1863633 4477951 := bstep (se 1 (by rfl) ⟨3358463, by rfl⟩ : syracuseStep 4477951 = 6716927) B6716927
theorem B13446395 : Blo 1863633 13446395 := bstep (se 1 (by rfl) ⟨10084796, by rfl⟩ : syracuseStep 13446395 = 20169593) B20169593
theorem B1863999 : Blo 1863633 1863999 := bstep (se 1 (by rfl) ⟨1397999, by rfl⟩ : syracuseStep 1863999 = 2795999) B2795999
theorem B1865151 : Blo 1863633 1865151 := bstep (se 1 (by rfl) ⟨1398863, by rfl⟩ : syracuseStep 1865151 = 2797727) B2797727
theorem B5970601 : Blo 1863633 5970601 := bstep (se 2 (by rfl) ⟨2238975, by rfl⟩ : syracuseStep 5970601 = 4477951) B4477951
theorem B8964263 : Blo 1863633 8964263 := bstep (se 1 (by rfl) ⟨6723197, by rfl⟩ : syracuseStep 8964263 = 13446395) B13446395
theorem B7960801 : Blo 1863633 7960801 := bstep (se 2 (by rfl) ⟨2985300, by rfl⟩ : syracuseStep 7960801 = 5970601) B5970601
theorem B5976175 : Blo 1863633 5976175 := bstep (se 1 (by rfl) ⟨4482131, by rfl⟩ : syracuseStep 5976175 = 8964263) B8964263
theorem B10614401 : Blo 1863633 10614401 := bstep (se 2 (by rfl) ⟨3980400, by rfl⟩ : syracuseStep 10614401 = 7960801) B7960801
theorem B7968233 : Blo 1863633 7968233 := bstep (se 2 (by rfl) ⟨2988087, by rfl⟩ : syracuseStep 7968233 = 5976175) B5976175
theorem B7076267 : Blo 1863633 7076267 := bstep (se 1 (by rfl) ⟨5307200, by rfl⟩ : syracuseStep 7076267 = 10614401) B10614401
theorem B5312155 : Blo 1863633 5312155 := bstep (se 1 (by rfl) ⟨3984116, by rfl⟩ : syracuseStep 5312155 = 7968233) B7968233
theorem B4717511 : Blo 1863633 4717511 := bstep (se 1 (by rfl) ⟨3538133, by rfl⟩ : syracuseStep 4717511 = 7076267) B7076267
theorem B7082873 : Blo 1863633 7082873 := bstep (se 2 (by rfl) ⟨2656077, by rfl⟩ : syracuseStep 7082873 = 5312155) B5312155
theorem B3145007 : Blo 1863633 3145007 := bstep (se 1 (by rfl) ⟨2358755, by rfl⟩ : syracuseStep 3145007 = 4717511) B4717511
theorem B4721915 : Blo 1863633 4721915 := bstep (se 1 (by rfl) ⟨3541436, by rfl⟩ : syracuseStep 4721915 = 7082873) B7082873
theorem B2096671 : Blo 1863633 2096671 := bstep (se 1 (by rfl) ⟨1572503, by rfl⟩ : syracuseStep 2096671 = 3145007) B3145007
theorem B2795561 : Blo 1863633 2795561 := bstep (se 2 (by rfl) ⟨1048335, by rfl⟩ : syracuseStep 2795561 = 2096671) B2096671
theorem B3147943 : Blo 1863633 3147943 := bstep (se 1 (by rfl) ⟨2360957, by rfl⟩ : syracuseStep 3147943 = 4721915) B4721915
theorem B4197257 : Blo 1863633 4197257 := bstep (se 2 (by rfl) ⟨1573971, by rfl⟩ : syracuseStep 4197257 = 3147943) B3147943
theorem B1863707 : Blo 1863633 1863707 := bstep (se 1 (by rfl) ⟨1397780, by rfl⟩ : syracuseStep 1863707 = 2795561) B2795561
theorem B2798171 : Blo 1863633 2798171 := bstep (se 1 (by rfl) ⟨2098628, by rfl⟩ : syracuseStep 2798171 = 4197257) B4197257
theorem B1865447 : Blo 1863633 1865447 := bstep (se 1 (by rfl) ⟨1399085, by rfl⟩ : syracuseStep 1865447 = 2798171) B2798171

theorem C0 (j : ℕ) (h1 : 465908 ≤ j) (h2 : j ≤ 466407) : Blo 1863633 (4 * j + 3) := by
  interval_cases j
  · exact B1863635
  · exact B1863639
  · exact B1863643
  · exact B1863647
  · exact B1863651
  · exact B1863655
  · exact B1863659
  · exact B1863663
  · exact B1863667
  · exact B1863671
  · exact B1863675
  · exact B1863679
  · exact B1863683
  · exact B1863687
  · exact B1863691
  · exact B1863695
  · exact B1863699
  · exact B1863703
  · exact B1863707
  · exact B1863711
  · exact B1863715
  · exact B1863719
  · exact B1863723
  · exact B1863727
  · exact B1863731
  · exact B1863735
  · exact B1863739
  · exact B1863743
  · exact B1863747
  · exact B1863751
  · exact B1863755
  · exact B1863759
  · exact B1863763
  · exact B1863767
  · exact B1863771
  · exact B1863775
  · exact B1863779
  · exact B1863783
  · exact B1863787
  · exact B1863791
  · exact B1863795
  · exact B1863799
  · exact B1863803
  · exact B1863807
  · exact B1863811
  · exact B1863815
  · exact B1863819
  · exact B1863823
  · exact B1863827
  · exact B1863831
  · exact B1863835
  · exact B1863839
  · exact B1863843
  · exact B1863847
  · exact B1863851
  · exact B1863855
  · exact B1863859
  · exact B1863863
  · exact B1863867
  · exact B1863871
  · exact B1863875
  · exact B1863879
  · exact B1863883
  · exact B1863887
  · exact B1863891
  · exact B1863895
  · exact B1863899
  · exact B1863903
  · exact B1863907
  · exact B1863911
  · exact B1863915
  · exact B1863919
  · exact B1863923
  · exact B1863927
  · exact B1863931
  · exact B1863935
  · exact B1863939
  · exact B1863943
  · exact B1863947
  · exact B1863951
  · exact B1863955
  · exact B1863959
  · exact B1863963
  · exact B1863967
  · exact B1863971
  · exact B1863975
  · exact B1863979
  · exact B1863983
  · exact B1863987
  · exact B1863991
  · exact B1863995
  · exact B1863999
  · exact B1864003
  · exact B1864007
  · exact B1864011
  · exact B1864015
  · exact B1864019
  · exact B1864023
  · exact B1864027
  · exact B1864031
  · exact B1864035
  · exact B1864039
  · exact B1864043
  · exact B1864047
  · exact B1864051
  · exact B1864055
  · exact B1864059
  · exact B1864063
  · exact B1864067
  · exact B1864071
  · exact B1864075
  · exact B1864079
  · exact B1864083
  · exact B1864087
  · exact B1864091
  · exact B1864095
  · exact B1864099
  · exact B1864103
  · exact B1864107
  · exact B1864111
  · exact B1864115
  · exact B1864119
  · exact B1864123
  · exact B1864127
  · exact B1864131
  · exact B1864135
  · exact B1864139
  · exact B1864143
  · exact B1864147
  · exact B1864151
  · exact B1864155
  · exact B1864159
  · exact B1864163
  · exact B1864167
  · exact B1864171
  · exact B1864175
  · exact B1864179
  · exact B1864183
  · exact B1864187
  · exact B1864191
  · exact B1864195
  · exact B1864199
  · exact B1864203
  · exact B1864207
  · exact B1864211
  · exact B1864215
  · exact B1864219
  · exact B1864223
  · exact B1864227
  · exact B1864231
  · exact B1864235
  · exact B1864239
  · exact B1864243
  · exact B1864247
  · exact B1864251
  · exact B1864255
  · exact B1864259
  · exact B1864263
  · exact B1864267
  · exact B1864271
  · exact B1864275
  · exact B1864279
  · exact B1864283
  · exact B1864287
  · exact B1864291
  · exact B1864295
  · exact B1864299
  · exact B1864303
  · exact B1864307
  · exact B1864311
  · exact B1864315
  · exact B1864319
  · exact B1864323
  · exact B1864327
  · exact B1864331
  · exact B1864335
  · exact B1864339
  · exact B1864343
  · exact B1864347
  · exact B1864351
  · exact B1864355
  · exact B1864359
  · exact B1864363
  · exact B1864367
  · exact B1864371
  · exact B1864375
  · exact B1864379
  · exact B1864383
  · exact B1864387
  · exact B1864391
  · exact B1864395
  · exact B1864399
  · exact B1864403
  · exact B1864407
  · exact B1864411
  · exact B1864415
  · exact B1864419
  · exact B1864423
  · exact B1864427
  · exact B1864431
  · exact B1864435
  · exact B1864439
  · exact B1864443
  · exact B1864447
  · exact B1864451
  · exact B1864455
  · exact B1864459
  · exact B1864463
  · exact B1864467
  · exact B1864471
  · exact B1864475
  · exact B1864479
  · exact B1864483
  · exact B1864487
  · exact B1864491
  · exact B1864495
  · exact B1864499
  · exact B1864503
  · exact B1864507
  · exact B1864511
  · exact B1864515
  · exact B1864519
  · exact B1864523
  · exact B1864527
  · exact B1864531
  · exact B1864535
  · exact B1864539
  · exact B1864543
  · exact B1864547
  · exact B1864551
  · exact B1864555
  · exact B1864559
  · exact B1864563
  · exact B1864567
  · exact B1864571
  · exact B1864575
  · exact B1864579
  · exact B1864583
  · exact B1864587
  · exact B1864591
  · exact B1864595
  · exact B1864599
  · exact B1864603
  · exact B1864607
  · exact B1864611
  · exact B1864615
  · exact B1864619
  · exact B1864623
  · exact B1864627
  · exact B1864631
  · exact B1864635
  · exact B1864639
  · exact B1864643
  · exact B1864647
  · exact B1864651
  · exact B1864655
  · exact B1864659
  · exact B1864663
  · exact B1864667
  · exact B1864671
  · exact B1864675
  · exact B1864679
  · exact B1864683
  · exact B1864687
  · exact B1864691
  · exact B1864695
  · exact B1864699
  · exact B1864703
  · exact B1864707
  · exact B1864711
  · exact B1864715
  · exact B1864719
  · exact B1864723
  · exact B1864727
  · exact B1864731
  · exact B1864735
  · exact B1864739
  · exact B1864743
  · exact B1864747
  · exact B1864751
  · exact B1864755
  · exact B1864759
  · exact B1864763
  · exact B1864767
  · exact B1864771
  · exact B1864775
  · exact B1864779
  · exact B1864783
  · exact B1864787
  · exact B1864791
  · exact B1864795
  · exact B1864799
  · exact B1864803
  · exact B1864807
  · exact B1864811
  · exact B1864815
  · exact B1864819
  · exact B1864823
  · exact B1864827
  · exact B1864831
  · exact B1864835
  · exact B1864839
  · exact B1864843
  · exact B1864847
  · exact B1864851
  · exact B1864855
  · exact B1864859
  · exact B1864863
  · exact B1864867
  · exact B1864871
  · exact B1864875
  · exact B1864879
  · exact B1864883
  · exact B1864887
  · exact B1864891
  · exact B1864895
  · exact B1864899
  · exact B1864903
  · exact B1864907
  · exact B1864911
  · exact B1864915
  · exact B1864919
  · exact B1864923
  · exact B1864927
  · exact B1864931
  · exact B1864935
  · exact B1864939
  · exact B1864943
  · exact B1864947
  · exact B1864951
  · exact B1864955
  · exact B1864959
  · exact B1864963
  · exact B1864967
  · exact B1864971
  · exact B1864975
  · exact B1864979
  · exact B1864983
  · exact B1864987
  · exact B1864991
  · exact B1864995
  · exact B1864999
  · exact B1865003
  · exact B1865007
  · exact B1865011
  · exact B1865015
  · exact B1865019
  · exact B1865023
  · exact B1865027
  · exact B1865031
  · exact B1865035
  · exact B1865039
  · exact B1865043
  · exact B1865047
  · exact B1865051
  · exact B1865055
  · exact B1865059
  · exact B1865063
  · exact B1865067
  · exact B1865071
  · exact B1865075
  · exact B1865079
  · exact B1865083
  · exact B1865087
  · exact B1865091
  · exact B1865095
  · exact B1865099
  · exact B1865103
  · exact B1865107
  · exact B1865111
  · exact B1865115
  · exact B1865119
  · exact B1865123
  · exact B1865127
  · exact B1865131
  · exact B1865135
  · exact B1865139
  · exact B1865143
  · exact B1865147
  · exact B1865151
  · exact B1865155
  · exact B1865159
  · exact B1865163
  · exact B1865167
  · exact B1865171
  · exact B1865175
  · exact B1865179
  · exact B1865183
  · exact B1865187
  · exact B1865191
  · exact B1865195
  · exact B1865199
  · exact B1865203
  · exact B1865207
  · exact B1865211
  · exact B1865215
  · exact B1865219
  · exact B1865223
  · exact B1865227
  · exact B1865231
  · exact B1865235
  · exact B1865239
  · exact B1865243
  · exact B1865247
  · exact B1865251
  · exact B1865255
  · exact B1865259
  · exact B1865263
  · exact B1865267
  · exact B1865271
  · exact B1865275
  · exact B1865279
  · exact B1865283
  · exact B1865287
  · exact B1865291
  · exact B1865295
  · exact B1865299
  · exact B1865303
  · exact B1865307
  · exact B1865311
  · exact B1865315
  · exact B1865319
  · exact B1865323
  · exact B1865327
  · exact B1865331
  · exact B1865335
  · exact B1865339
  · exact B1865343
  · exact B1865347
  · exact B1865351
  · exact B1865355
  · exact B1865359
  · exact B1865363
  · exact B1865367
  · exact B1865371
  · exact B1865375
  · exact B1865379
  · exact B1865383
  · exact B1865387
  · exact B1865391
  · exact B1865395
  · exact B1865399
  · exact B1865403
  · exact B1865407
  · exact B1865411
  · exact B1865415
  · exact B1865419
  · exact B1865423
  · exact B1865427
  · exact B1865431
  · exact B1865435
  · exact B1865439
  · exact B1865443
  · exact B1865447
  · exact B1865451
  · exact B1865455
  · exact B1865459
  · exact B1865463
  · exact B1865467
  · exact B1865471
  · exact B1865475
  · exact B1865479
  · exact B1865483
  · exact B1865487
  · exact B1865491
  · exact B1865495
  · exact B1865499
  · exact B1865503
  · exact B1865507
  · exact B1865511
  · exact B1865515
  · exact B1865519
  · exact B1865523
  · exact B1865527
  · exact B1865531
  · exact B1865535
  · exact B1865539
  · exact B1865543
  · exact B1865547
  · exact B1865551
  · exact B1865555
  · exact B1865559
  · exact B1865563
  · exact B1865567
  · exact B1865571
  · exact B1865575
  · exact B1865579
  · exact B1865583
  · exact B1865587
  · exact B1865591
  · exact B1865595
  · exact B1865599
  · exact B1865603
  · exact B1865607
  · exact B1865611
  · exact B1865615
  · exact B1865619
  · exact B1865623
  · exact B1865627
  · exact B1865631

theorem solution (m : ℕ) (hlo : 1863633 ≤ m) (hhi : m ≤ 1865633) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 465908 ≤ j := by omega
    have hj2 : j ≤ 466407 := by omega
    have hb : Blo 1863633 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
