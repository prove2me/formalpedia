-- Prove2me | solution 1 for syracuse_descends_range_1744573_1746573
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:35:05.708839+00:00
-- url     : https://prove2.me/submissions/53571501-5631-44f1-b12a-81d91f6fd8f0

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


theorem B4194317 : Blo 1744573 4194317 := bbase (se 3 (by rfl) ⟨786434, by rfl⟩ : syracuseStep 4194317 = 1572869) (by norm_num)
theorem B13254677 : Blo 1744573 13254677 := bbase (se 6 (by rfl) ⟨310656, by rfl⟩ : syracuseStep 13254677 = 621313) (by norm_num)
theorem B8839205 : Blo 1744573 8839205 := bbase (se 4 (by rfl) ⟨828675, by rfl⟩ : syracuseStep 8839205 = 1657351) (by norm_num)
theorem B10616885 : Blo 1744573 10616885 := bbase (se 5 (by rfl) ⟨497666, by rfl⟩ : syracuseStep 10616885 = 995333) (by norm_num)
theorem B4481093 : Blo 1744573 4481093 := bbase (se 4 (by rfl) ⟨420102, by rfl⟩ : syracuseStep 4481093 = 840205) (by norm_num)
theorem B6291589 : Blo 1744573 6291589 := bbase (se 4 (by rfl) ⟨589836, by rfl⟩ : syracuseStep 6291589 = 1179673) (by norm_num)
theorem B4538549 : Blo 1744573 4538549 := bbase (se 5 (by rfl) ⟨212744, by rfl⟩ : syracuseStep 4538549 = 425489) (by norm_num)
theorem B2359525 : Blo 1744573 2359525 := bbase (se 4 (by rfl) ⟨221205, by rfl⟩ : syracuseStep 2359525 = 442411) (by norm_num)
theorem B1990885 : Blo 1744573 1990885 := bbase (se 4 (by rfl) ⟨186645, by rfl⟩ : syracuseStep 1990885 = 373291) (by norm_num)
theorem B1769725 : Blo 1744573 1769725 := bbase (se 3 (by rfl) ⟨331823, by rfl⟩ : syracuseStep 1769725 = 663647) (by norm_num)
theorem B6291749 : Blo 1744573 6291749 := bbase (se 4 (by rfl) ⟨589851, by rfl⟩ : syracuseStep 6291749 = 1179703) (by norm_num)
theorem B1769773 : Blo 1744573 1769773 := bbase (se 3 (by rfl) ⟨331832, by rfl⟩ : syracuseStep 1769773 = 663665) (by norm_num)
theorem B5890373 : Blo 1744573 5890373 := bbase (se 4 (by rfl) ⟨552222, by rfl⟩ : syracuseStep 5890373 = 1104445) (by norm_num)
theorem B2097581 : Blo 1744573 2097581 := bbase (se 3 (by rfl) ⟨393296, by rfl⟩ : syracuseStep 2097581 = 786593) (by norm_num)
theorem B8733109 : Blo 1744573 8733109 := bbase (se 5 (by rfl) ⟨409364, by rfl⟩ : syracuseStep 8733109 = 818729) (by norm_num)
theorem B4416029 : Blo 1744573 4416029 := bbase (se 3 (by rfl) ⟨828005, by rfl⟩ : syracuseStep 4416029 = 1656011) (by norm_num)
theorem B2097749 : Blo 1744573 2097749 := bbase (se 8 (by rfl) ⟨12291, by rfl⟩ : syracuseStep 2097749 = 24583) (by norm_num)
theorem B3727981 : Blo 1744573 3727981 := bbase (se 3 (by rfl) ⟨698996, by rfl⟩ : syracuseStep 3727981 = 1397993) (by norm_num)
theorem B4420757 : Blo 1744573 4420757 := bbase (se 6 (by rfl) ⟨103611, by rfl⟩ : syracuseStep 4420757 = 207223) (by norm_num)
theorem B3539629 : Blo 1744573 3539629 := bbase (se 3 (by rfl) ⟨663680, by rfl⟩ : syracuseStep 3539629 = 1327361) (by norm_num)
theorem B4416221 : Blo 1744573 4416221 := bbase (se 3 (by rfl) ⟨828041, by rfl⟩ : syracuseStep 4416221 = 1656083) (by norm_num)
theorem B3728101 : Blo 1744573 3728101 := bbase (se 4 (by rfl) ⟨349509, by rfl⟩ : syracuseStep 3728101 = 699019) (by norm_num)
theorem B3539693 : Blo 1744573 3539693 := bbase (se 3 (by rfl) ⟨663692, by rfl⟩ : syracuseStep 3539693 = 1327385) (by norm_num)
theorem B5890805 : Blo 1744573 5890805 := bbase (se 5 (by rfl) ⟨276131, by rfl⟩ : syracuseStep 5890805 = 552263) (by norm_num)
theorem B5309221 : Blo 1744573 5309221 := bbase (se 4 (by rfl) ⟨497739, by rfl⟩ : syracuseStep 5309221 = 995479) (by norm_num)
theorem B5178149 : Blo 1744573 5178149 := bbase (se 4 (by rfl) ⟨485451, by rfl⟩ : syracuseStep 5178149 = 970903) (by norm_num)
theorem B2360173 : Blo 1744573 2360173 := bbase (se 3 (by rfl) ⟨442532, by rfl⟩ : syracuseStep 2360173 = 885065) (by norm_num)
theorem B2098057 : Blo 1744573 2098057 := bbase (se 2 (by rfl) ⟨786771, by rfl⟩ : syracuseStep 2098057 = 1573543) (by norm_num)
theorem B3728357 : Blo 1744573 3728357 := bbase (se 4 (by rfl) ⟨349533, by rfl⟩ : syracuseStep 3728357 = 699067) (by norm_num)
theorem B4973557 : Blo 1744573 4973557 := bbase (se 5 (by rfl) ⟨233135, by rfl⟩ : syracuseStep 4973557 = 466271) (by norm_num)
theorem B3146797 : Blo 1744573 3146797 := bbase (se 3 (by rfl) ⟨590024, by rfl⟩ : syracuseStep 3146797 = 1180049) (by norm_num)
theorem B4416565 : Blo 1744573 4416565 := bbase (se 5 (by rfl) ⟨207026, by rfl⟩ : syracuseStep 4416565 = 414053) (by norm_num)
theorem B2835509 : Blo 1744573 2835509 := bbase (se 5 (by rfl) ⟨132914, by rfl⟩ : syracuseStep 2835509 = 265829) (by norm_num)
theorem B5104709 : Blo 1744573 5104709 := bbase (se 4 (by rfl) ⟨478566, by rfl⟩ : syracuseStep 5104709 = 957133) (by norm_num)
theorem B3982493 : Blo 1744573 3982493 := bbase (se 3 (by rfl) ⟨746717, by rfl⟩ : syracuseStep 3982493 = 1493435) (by norm_num)
theorem B2655389 : Blo 1744573 2655389 := bbase (se 3 (by rfl) ⟨497885, by rfl⟩ : syracuseStep 2655389 = 995771) (by norm_num)
theorem B4416677 : Blo 1744573 4416677 := bbase (se 4 (by rfl) ⟨414063, by rfl⟩ : syracuseStep 4416677 = 828127) (by norm_num)
theorem B5891237 : Blo 1744573 5891237 := bbase (se 4 (by rfl) ⟨552303, by rfl⟩ : syracuseStep 5891237 = 1104607) (by norm_num)
theorem B2794781 : Blo 1744573 2794781 := bbase (se 3 (by rfl) ⟨524021, by rfl⟩ : syracuseStep 2794781 = 1048043) (by norm_num)
theorem B6628661 : Blo 1744573 6628661 := bbase (se 5 (by rfl) ⟨310718, by rfl⟩ : syracuseStep 6628661 = 621437) (by norm_num)
theorem B8840501 : Blo 1744573 8840501 := bbase (se 5 (by rfl) ⟨414398, by rfl⟩ : syracuseStep 8840501 = 828797) (by norm_num)
theorem B3925349 : Blo 1744573 3925349 := bbase (se 4 (by rfl) ⟨368001, by rfl⟩ : syracuseStep 3925349 = 736003) (by norm_num)
theorem B4416869 : Blo 1744573 4416869 := bbase (se 4 (by rfl) ⟨414081, by rfl⟩ : syracuseStep 4416869 = 828163) (by norm_num)
theorem B4195709 : Blo 1744573 4195709 := bbase (se 3 (by rfl) ⟨786695, by rfl⟩ : syracuseStep 4195709 = 1573391) (by norm_num)
theorem B3925421 : Blo 1744573 3925421 := bbase (se 3 (by rfl) ⟨736016, by rfl⟩ : syracuseStep 3925421 = 1472033) (by norm_num)
theorem B4195805 : Blo 1744573 4195805 := bbase (se 3 (by rfl) ⟨786713, by rfl⟩ : syracuseStep 4195805 = 1573427) (by norm_num)
theorem B2794981 : Blo 1744573 2794981 := bbase (se 4 (by rfl) ⟨262029, by rfl⟩ : syracuseStep 2794981 = 524059) (by norm_num)
theorem B3925493 : Blo 1744573 3925493 := bbase (se 5 (by rfl) ⟨184007, by rfl⟩ : syracuseStep 3925493 = 368015) (by norm_num)
theorem B15918581 : Blo 1744573 15918581 := bbase (se 5 (by rfl) ⟨746183, by rfl⟩ : syracuseStep 15918581 = 1492367) (by norm_num)
theorem B3925565 : Blo 1744573 3925565 := bbase (se 3 (by rfl) ⟨736043, by rfl⟩ : syracuseStep 3925565 = 1472087) (by norm_num)
theorem B5891669 : Blo 1744573 5891669 := bbase (se 8 (by rfl) ⟨34521, by rfl⟩ : syracuseStep 5891669 = 69043) (by norm_num)
theorem B6628949 : Blo 1744573 6628949 := bbase (se 8 (by rfl) ⟨38841, by rfl⟩ : syracuseStep 6628949 = 77683) (by norm_num)
theorem B7456373 : Blo 1744573 7456373 := bbase (se 5 (by rfl) ⟨349517, by rfl⟩ : syracuseStep 7456373 = 699035) (by norm_num)
theorem B3925637 : Blo 1744573 3925637 := bbase (se 4 (by rfl) ⟨368028, by rfl⟩ : syracuseStep 3925637 = 736057) (by norm_num)
theorem B4417213 : Blo 1744573 4417213 := bbase (se 3 (by rfl) ⟨828227, by rfl⟩ : syracuseStep 4417213 = 1656455) (by norm_num)
theorem B3925709 : Blo 1744573 3925709 := bbase (se 3 (by rfl) ⟨736070, by rfl⟩ : syracuseStep 3925709 = 1472141) (by norm_num)
theorem B8832725 : Blo 1744573 8832725 := bbase (se 7 (by rfl) ⟨103508, by rfl⟩ : syracuseStep 8832725 = 207017) (by norm_num)
theorem B2795237 : Blo 1744573 2795237 := bbase (se 4 (by rfl) ⟨262053, by rfl⟩ : syracuseStep 2795237 = 524107) (by norm_num)
theorem B3925781 : Blo 1744573 3925781 := bbase (se 6 (by rfl) ⟨92010, by rfl⟩ : syracuseStep 3925781 = 184021) (by norm_num)
theorem B2017045 : Blo 1744573 2017045 := bbase (se 6 (by rfl) ⟨47274, by rfl⟩ : syracuseStep 2017045 = 94549) (by norm_num)
theorem B4417325 : Blo 1744573 4417325 := bbase (se 3 (by rfl) ⟨828248, by rfl⟩ : syracuseStep 4417325 = 1656497) (by norm_num)
theorem B3925853 : Blo 1744573 3925853 := bbase (se 3 (by rfl) ⟨736097, by rfl⟩ : syracuseStep 3925853 = 1472195) (by norm_num)
theorem B3729245 : Blo 1744573 3729245 := bbase (se 3 (by rfl) ⟨699233, by rfl⟩ : syracuseStep 3729245 = 1398467) (by norm_num)
theorem B3188621 : Blo 1744573 3188621 := bbase (se 3 (by rfl) ⟨597866, by rfl⟩ : syracuseStep 3188621 = 1195733) (by norm_num)
theorem B3925925 : Blo 1744573 3925925 := bbase (se 4 (by rfl) ⟨368055, by rfl⟩ : syracuseStep 3925925 = 736111) (by norm_num)
theorem B4417517 : Blo 1744573 4417517 := bbase (se 3 (by rfl) ⟨828284, by rfl⟩ : syracuseStep 4417517 = 1656569) (by norm_num)
theorem B3925997 : Blo 1744573 3925997 := bbase (se 3 (by rfl) ⟨736124, by rfl⟩ : syracuseStep 3925997 = 1472249) (by norm_num)
theorem B5892101 : Blo 1744573 5892101 := bbase (se 4 (by rfl) ⟨552384, by rfl⟩ : syracuseStep 5892101 = 1104769) (by norm_num)
theorem B3926069 : Blo 1744573 3926069 := bbase (se 5 (by rfl) ⟨184034, by rfl⟩ : syracuseStep 3926069 = 368069) (by norm_num)
theorem B3729485 : Blo 1744573 3729485 := bbase (se 3 (by rfl) ⟨699278, by rfl⟩ : syracuseStep 3729485 = 1398557) (by norm_num)
theorem B3926141 : Blo 1744573 3926141 := bbase (se 3 (by rfl) ⟨736151, by rfl⟩ : syracuseStep 3926141 = 1472303) (by norm_num)
theorem B3926213 : Blo 1744573 3926213 := bbase (se 4 (by rfl) ⟨368082, by rfl⟩ : syracuseStep 3926213 = 736165) (by norm_num)
theorem B3926285 : Blo 1744573 3926285 := bbase (se 3 (by rfl) ⟨736178, by rfl⟩ : syracuseStep 3926285 = 1472357) (by norm_num)
theorem B4417861 : Blo 1744573 4417861 := bbase (se 4 (by rfl) ⟨414174, by rfl⟩ : syracuseStep 4417861 = 828349) (by norm_num)
theorem B3926357 : Blo 1744573 3926357 := bbase (se 10 (by rfl) ⟨5751, by rfl⟩ : syracuseStep 3926357 = 11503) (by norm_num)
theorem B10619221 : Blo 1744573 10619221 := bbase (se 10 (by rfl) ⟨15555, by rfl⟩ : syracuseStep 10619221 = 31111) (by norm_num)
theorem B6293909 : Blo 1744573 6293909 := bbase (se 6 (by rfl) ⟨147513, by rfl⟩ : syracuseStep 6293909 = 295027) (by norm_num)
theorem B3312029 : Blo 1744573 3312029 := bbase (se 3 (by rfl) ⟨621005, by rfl⟩ : syracuseStep 3312029 = 1242011) (by norm_num)
theorem B3926429 : Blo 1744573 3926429 := bbase (se 3 (by rfl) ⟨736205, by rfl⟩ : syracuseStep 3926429 = 1472411) (by norm_num)
theorem B4417973 : Blo 1744573 4417973 := bbase (se 5 (by rfl) ⟨207092, by rfl⟩ : syracuseStep 4417973 = 414185) (by norm_num)
theorem B5892533 : Blo 1744573 5892533 := bbase (se 5 (by rfl) ⟨276212, by rfl⟩ : syracuseStep 5892533 = 552425) (by norm_num)
theorem B8391109 : Blo 1744573 8391109 := bbase (se 4 (by rfl) ⟨786666, by rfl⟩ : syracuseStep 8391109 = 1573333) (by norm_num)
theorem B2238925 : Blo 1744573 2238925 := bbase (se 3 (by rfl) ⟨419798, by rfl⟩ : syracuseStep 2238925 = 839597) (by norm_num)
theorem B3926501 : Blo 1744573 3926501 := bbase (se 4 (by rfl) ⟨368109, by rfl⟩ : syracuseStep 3926501 = 736219) (by norm_num)
theorem B5974517 : Blo 1744573 5974517 := bbase (se 5 (by rfl) ⟨280055, by rfl⟩ : syracuseStep 5974517 = 560111) (by norm_num)
theorem B3926573 : Blo 1744573 3926573 := bbase (se 3 (by rfl) ⟨736232, by rfl⟩ : syracuseStep 3926573 = 1472465) (by norm_num)
theorem B3312181 : Blo 1744573 3312181 := bbase (se 5 (by rfl) ⟨155258, by rfl⟩ : syracuseStep 3312181 = 310517) (by norm_num)
theorem B3729989 : Blo 1744573 3729989 := bbase (se 4 (by rfl) ⟨349686, by rfl⟩ : syracuseStep 3729989 = 699373) (by norm_num)
theorem B8841797 : Blo 1744573 8841797 := bbase (se 4 (by rfl) ⟨828918, by rfl⟩ : syracuseStep 8841797 = 1657837) (by norm_num)
theorem B3729997 : Blo 1744573 3729997 := bbase (se 3 (by rfl) ⟨699374, by rfl⟩ : syracuseStep 3729997 = 1398749) (by norm_num)
theorem B3926645 : Blo 1744573 3926645 := bbase (se 5 (by rfl) ⟨184061, by rfl⟩ : syracuseStep 3926645 = 368123) (by norm_num)
theorem B4418165 : Blo 1744573 4418165 := bbase (se 5 (by rfl) ⟨207101, by rfl⟩ : syracuseStep 4418165 = 414203) (by norm_num)
theorem B22375061 : Blo 1744573 22375061 := bbase (se 6 (by rfl) ⟨524415, by rfl⟩ : syracuseStep 22375061 = 1048831) (by norm_num)
theorem B3926717 : Blo 1744573 3926717 := bbase (se 3 (by rfl) ⟨736259, by rfl⟩ : syracuseStep 3926717 = 1472519) (by norm_num)
theorem B6630133 : Blo 1744573 6630133 := bbase (se 5 (by rfl) ⟨310787, by rfl⟩ : syracuseStep 6630133 = 621575) (by norm_num)
theorem B3926789 : Blo 1744573 3926789 := bbase (se 4 (by rfl) ⟨368136, by rfl⟩ : syracuseStep 3926789 = 736273) (by norm_num)
theorem B3926861 : Blo 1744573 3926861 := bbase (se 3 (by rfl) ⟨736286, by rfl⟩ : syracuseStep 3926861 = 1472573) (by norm_num)
theorem B2796365 : Blo 1744573 2796365 := bbase (se 3 (by rfl) ⟨524318, by rfl⟩ : syracuseStep 2796365 = 1048637) (by norm_num)
theorem B3312485 : Blo 1744573 3312485 := bbase (se 4 (by rfl) ⟨310545, by rfl⟩ : syracuseStep 3312485 = 621091) (by norm_num)
theorem B2485093 : Blo 1744573 2485093 := bbase (se 4 (by rfl) ⟨232977, by rfl⟩ : syracuseStep 2485093 = 465955) (by norm_num)
theorem B5892965 : Blo 1744573 5892965 := bbase (se 4 (by rfl) ⟨552465, by rfl⟩ : syracuseStep 5892965 = 1104931) (by norm_num)
theorem B3926933 : Blo 1744573 3926933 := bbase (se 6 (by rfl) ⟨92037, by rfl⟩ : syracuseStep 3926933 = 184075) (by norm_num)
theorem B4418509 : Blo 1744573 4418509 := bbase (se 3 (by rfl) ⟨828470, by rfl⟩ : syracuseStep 4418509 = 1656941) (by norm_num)
theorem B3927005 : Blo 1744573 3927005 := bbase (se 3 (by rfl) ⟨736313, by rfl⟩ : syracuseStep 3927005 = 1472627) (by norm_num)
theorem B8834021 : Blo 1744573 8834021 := bbase (se 4 (by rfl) ⟨828189, by rfl⟩ : syracuseStep 8834021 = 1656379) (by norm_num)
theorem B3927077 : Blo 1744573 3927077 := bbase (se 4 (by rfl) ⟨368163, by rfl⟩ : syracuseStep 3927077 = 736327) (by norm_num)
theorem B6630437 : Blo 1744573 6630437 := bbase (se 4 (by rfl) ⟨621603, by rfl⟩ : syracuseStep 6630437 = 1243207) (by norm_num)
theorem B4418621 : Blo 1744573 4418621 := bbase (se 3 (by rfl) ⟨828491, by rfl⟩ : syracuseStep 4418621 = 1656983) (by norm_num)
theorem B2944093 : Blo 1744573 2944093 := bbase (se 3 (by rfl) ⟨552017, by rfl⟩ : syracuseStep 2944093 = 1104035) (by norm_num)
theorem B3927149 : Blo 1744573 3927149 := bbase (se 3 (by rfl) ⟨736340, by rfl⟩ : syracuseStep 3927149 = 1472681) (by norm_num)
theorem B2239633 : Blo 1744573 2239633 := bbase (se 2 (by rfl) ⟨839862, by rfl⟩ : syracuseStep 2239633 = 1679725) (by norm_num)
theorem B2944181 : Blo 1744573 2944181 := bbase (se 5 (by rfl) ⟨138008, by rfl⟩ : syracuseStep 2944181 = 276017) (by norm_num)
theorem B3927221 : Blo 1744573 3927221 := bbase (se 5 (by rfl) ⟨184088, by rfl⟩ : syracuseStep 3927221 = 368177) (by norm_num)
theorem B2518237 : Blo 1744573 2518237 := bbase (se 3 (by rfl) ⟨472169, by rfl⟩ : syracuseStep 2518237 = 944339) (by norm_num)
theorem B3927293 : Blo 1744573 3927293 := bbase (se 3 (by rfl) ⟨736367, by rfl⟩ : syracuseStep 3927293 = 1472735) (by norm_num)
theorem B4418813 : Blo 1744573 4418813 := bbase (se 3 (by rfl) ⟨828527, by rfl⟩ : syracuseStep 4418813 = 1657055) (by norm_num)
theorem B5893397 : Blo 1744573 5893397 := bbase (se 6 (by rfl) ⟨138126, by rfl⟩ : syracuseStep 5893397 = 276253) (by norm_num)
theorem B2944309 : Blo 1744573 2944309 := bbase (se 5 (by rfl) ⟨138014, by rfl⟩ : syracuseStep 2944309 = 276029) (by norm_num)
theorem B3927365 : Blo 1744573 3927365 := bbase (se 4 (by rfl) ⟨368190, by rfl⟩ : syracuseStep 3927365 = 736381) (by norm_num)
theorem B2796877 : Blo 1744573 2796877 := bbase (se 3 (by rfl) ⟨524414, by rfl⟩ : syracuseStep 2796877 = 1048829) (by norm_num)
theorem B7458149 : Blo 1744573 7458149 := bbase (se 4 (by rfl) ⟨699201, by rfl⟩ : syracuseStep 7458149 = 1398403) (by norm_num)
theorem B4148597 : Blo 1744573 4148597 := bbase (se 5 (by rfl) ⟨194465, by rfl⟩ : syracuseStep 4148597 = 388931) (by norm_num)
theorem B2944397 : Blo 1744573 2944397 := bbase (se 3 (by rfl) ⟨552074, by rfl⟩ : syracuseStep 2944397 = 1104149) (by norm_num)
theorem B3927437 : Blo 1744573 3927437 := bbase (se 3 (by rfl) ⟨736394, by rfl⟩ : syracuseStep 3927437 = 1472789) (by norm_num)
theorem B1863085 : Blo 1744573 1863085 := bbase (se 3 (by rfl) ⟨349328, by rfl⟩ : syracuseStep 1863085 = 698657) (by norm_num)
theorem B2485685 : Blo 1744573 2485685 := bbase (se 5 (by rfl) ⟨116516, by rfl⟩ : syracuseStep 2485685 = 233033) (by norm_num)
theorem B3927509 : Blo 1744573 3927509 := bbase (se 7 (by rfl) ⟨46025, by rfl⟩ : syracuseStep 3927509 = 92051) (by norm_num)
theorem B2485765 : Blo 1744573 2485765 := bbase (se 4 (by rfl) ⟨233040, by rfl⟩ : syracuseStep 2485765 = 466081) (by norm_num)
theorem B2944525 : Blo 1744573 2944525 := bbase (se 3 (by rfl) ⟨552098, by rfl⟩ : syracuseStep 2944525 = 1104197) (by norm_num)
theorem B11185685 : Blo 1744573 11185685 := bbase (se 6 (by rfl) ⟨262164, by rfl⟩ : syracuseStep 11185685 = 524329) (by norm_num)
theorem B3927581 : Blo 1744573 3927581 := bbase (se 3 (by rfl) ⟨736421, by rfl⟩ : syracuseStep 3927581 = 1472843) (by norm_num)
theorem B2616869 : Blo 1744573 2616869 := bbase (se 4 (by rfl) ⟨245331, by rfl⟩ : syracuseStep 2616869 = 490663) (by norm_num)
theorem B2616893 : Blo 1744573 2616893 := bbase (se 3 (by rfl) ⟨490667, by rfl⟩ : syracuseStep 2616893 = 981335) (by norm_num)
theorem B2616917 : Blo 1744573 2616917 := bbase (se 8 (by rfl) ⟨15333, by rfl⟩ : syracuseStep 2616917 = 30667) (by norm_num)
theorem B3313237 : Blo 1744573 3313237 := bbase (se 8 (by rfl) ⟨19413, by rfl⟩ : syracuseStep 3313237 = 38827) (by norm_num)
theorem B4419157 : Blo 1744573 4419157 := bbase (se 8 (by rfl) ⟨25893, by rfl⟩ : syracuseStep 4419157 = 51787) (by norm_num)
theorem B7458389 : Blo 1744573 7458389 := bbase (se 8 (by rfl) ⟨43701, by rfl⟩ : syracuseStep 7458389 = 87403) (by norm_num)
theorem B2944613 : Blo 1744573 2944613 := bbase (se 4 (by rfl) ⟨276057, by rfl⟩ : syracuseStep 2944613 = 552115) (by norm_num)
theorem B3927653 : Blo 1744573 3927653 := bbase (se 4 (by rfl) ⟨368217, by rfl⟩ : syracuseStep 3927653 = 736435) (by norm_num)
theorem B2616941 : Blo 1744573 2616941 := bbase (se 3 (by rfl) ⟨490676, by rfl⟩ : syracuseStep 2616941 = 981353) (by norm_num)
theorem B2485885 : Blo 1744573 2485885 := bbase (se 3 (by rfl) ⟨466103, by rfl⟩ : syracuseStep 2485885 = 932207) (by norm_num)
theorem B2616965 : Blo 1744573 2616965 := bbase (se 4 (by rfl) ⟨245340, by rfl⟩ : syracuseStep 2616965 = 490681) (by norm_num)
theorem B2616989 : Blo 1744573 2616989 := bbase (se 3 (by rfl) ⟨490685, by rfl⟩ : syracuseStep 2616989 = 981371) (by norm_num)
theorem B3927725 : Blo 1744573 3927725 := bbase (se 3 (by rfl) ⟨736448, by rfl⟩ : syracuseStep 3927725 = 1472897) (by norm_num)
theorem B2617013 : Blo 1744573 2617013 := bbase (se 5 (by rfl) ⟨122672, by rfl⟩ : syracuseStep 2617013 = 245345) (by norm_num)
theorem B4419269 : Blo 1744573 4419269 := bbase (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) (by norm_num)
theorem B5893829 : Blo 1744573 5893829 := bbase (se 4 (by rfl) ⟨552546, by rfl⟩ : syracuseStep 5893829 = 1105093) (by norm_num)
theorem B2617037 : Blo 1744573 2617037 := bbase (se 3 (by rfl) ⟨490694, by rfl⟩ : syracuseStep 2617037 = 981389) (by norm_num)
theorem B2485981 : Blo 1744573 2485981 := bbase (se 3 (by rfl) ⟨466121, by rfl⟩ : syracuseStep 2485981 = 932243) (by norm_num)
theorem B2617061 : Blo 1744573 2617061 := bbase (se 4 (by rfl) ⟨245349, by rfl⟩ : syracuseStep 2617061 = 490699) (by norm_num)
theorem B2944741 : Blo 1744573 2944741 := bbase (se 4 (by rfl) ⟨276069, by rfl⟩ : syracuseStep 2944741 = 552139) (by norm_num)
theorem B3313381 : Blo 1744573 3313381 := bbase (se 4 (by rfl) ⟨310629, by rfl⟩ : syracuseStep 3313381 = 621259) (by norm_num)
theorem B3780325 : Blo 1744573 3780325 := bbase (se 4 (by rfl) ⟨354405, by rfl⟩ : syracuseStep 3780325 = 708811) (by norm_num)
theorem B3927797 : Blo 1744573 3927797 := bbase (se 5 (by rfl) ⟨184115, by rfl⟩ : syracuseStep 3927797 = 368231) (by norm_num)
theorem B2617085 : Blo 1744573 2617085 := bbase (se 3 (by rfl) ⟨490703, by rfl⟩ : syracuseStep 2617085 = 981407) (by norm_num)
theorem B2617109 : Blo 1744573 2617109 := bbase (se 6 (by rfl) ⟨61338, by rfl⟩ : syracuseStep 2617109 = 122677) (by norm_num)
theorem B2617133 : Blo 1744573 2617133 := bbase (se 3 (by rfl) ⟨490712, by rfl⟩ : syracuseStep 2617133 = 981425) (by norm_num)
theorem B2985781 : Blo 1744573 2985781 := bbase (se 5 (by rfl) ⟨139958, by rfl⟩ : syracuseStep 2985781 = 279917) (by norm_num)
theorem B2944829 : Blo 1744573 2944829 := bbase (se 3 (by rfl) ⟨552155, by rfl⟩ : syracuseStep 2944829 = 1104311) (by norm_num)
theorem B3927869 : Blo 1744573 3927869 := bbase (se 3 (by rfl) ⟨736475, by rfl⟩ : syracuseStep 3927869 = 1472951) (by norm_num)
theorem B2617157 : Blo 1744573 2617157 := bbase (se 4 (by rfl) ⟨245358, by rfl⟩ : syracuseStep 2617157 = 490717) (by norm_num)
theorem B2617181 : Blo 1744573 2617181 := bbase (se 3 (by rfl) ⟨490721, by rfl⟩ : syracuseStep 2617181 = 981443) (by norm_num)
theorem B1863529 : Blo 1744573 1863529 := bbase (se 2 (by rfl) ⟨698823, by rfl⟩ : syracuseStep 1863529 = 1397647) (by norm_num)
theorem B2797421 : Blo 1744573 2797421 := bbase (se 3 (by rfl) ⟨524516, by rfl⟩ : syracuseStep 2797421 = 1049033) (by norm_num)
theorem B2617205 : Blo 1744573 2617205 := bbase (se 5 (by rfl) ⟨122681, by rfl⟩ : syracuseStep 2617205 = 245363) (by norm_num)
theorem B2125697 : Blo 1744573 2125697 := bbase (se 2 (by rfl) ⟨797136, by rfl⟩ : syracuseStep 2125697 = 1594273) (by norm_num)
theorem B3313541 : Blo 1744573 3313541 := bbase (se 4 (by rfl) ⟨310644, by rfl⟩ : syracuseStep 3313541 = 621289) (by norm_num)
theorem B3927941 : Blo 1744573 3927941 := bbase (se 4 (by rfl) ⟨368244, by rfl⟩ : syracuseStep 3927941 = 736489) (by norm_num)
theorem B4419461 : Blo 1744573 4419461 := bbase (se 4 (by rfl) ⟨414324, by rfl⟩ : syracuseStep 4419461 = 828649) (by norm_num)
theorem B2617229 : Blo 1744573 2617229 := bbase (se 3 (by rfl) ⟨490730, by rfl⟩ : syracuseStep 2617229 = 981461) (by norm_num)
theorem B4968341 : Blo 1744573 4968341 := bbase (se 6 (by rfl) ⟨116445, by rfl⟩ : syracuseStep 4968341 = 232891) (by norm_num)
theorem B2617253 : Blo 1744573 2617253 := bbase (se 4 (by rfl) ⟨245367, by rfl⟩ : syracuseStep 2617253 = 490735) (by norm_num)
theorem B2617277 : Blo 1744573 2617277 := bbase (se 3 (by rfl) ⟨490739, by rfl⟩ : syracuseStep 2617277 = 981479) (by norm_num)
theorem B2944957 : Blo 1744573 2944957 := bbase (se 3 (by rfl) ⟨552179, by rfl⟩ : syracuseStep 2944957 = 1104359) (by norm_num)
theorem B3928013 : Blo 1744573 3928013 := bbase (se 3 (by rfl) ⟨736502, by rfl⟩ : syracuseStep 3928013 = 1473005) (by norm_num)
theorem B2617301 : Blo 1744573 2617301 := bbase (se 7 (by rfl) ⟨30671, by rfl⟩ : syracuseStep 2617301 = 61343) (by norm_num)
theorem B1863649 : Blo 1744573 1863649 := bbase (se 2 (by rfl) ⟨698868, by rfl⟩ : syracuseStep 1863649 = 1397737) (by norm_num)
theorem B4542437 : Blo 1744573 4542437 := bbase (se 4 (by rfl) ⟨425853, by rfl⟩ : syracuseStep 4542437 = 851707) (by norm_num)
theorem B2617325 : Blo 1744573 2617325 := bbase (se 3 (by rfl) ⟨490748, by rfl⟩ : syracuseStep 2617325 = 981497) (by norm_num)
theorem B2617349 : Blo 1744573 2617349 := bbase (se 4 (by rfl) ⟨245376, by rfl⟩ : syracuseStep 2617349 = 490753) (by norm_num)
theorem B2945045 : Blo 1744573 2945045 := bbase (se 6 (by rfl) ⟨69024, by rfl⟩ : syracuseStep 2945045 = 138049) (by norm_num)
theorem B3313685 : Blo 1744573 3313685 := bbase (se 6 (by rfl) ⟨77664, by rfl⟩ : syracuseStep 3313685 = 155329) (by norm_num)
theorem B3928085 : Blo 1744573 3928085 := bbase (se 6 (by rfl) ⟨92064, by rfl⟩ : syracuseStep 3928085 = 184129) (by norm_num)
theorem B2617373 : Blo 1744573 2617373 := bbase (se 3 (by rfl) ⟨490757, by rfl⟩ : syracuseStep 2617373 = 981515) (by norm_num)
theorem B2617397 : Blo 1744573 2617397 := bbase (se 5 (by rfl) ⟨122690, by rfl⟩ : syracuseStep 2617397 = 245381) (by norm_num)
theorem B2617421 : Blo 1744573 2617421 := bbase (se 3 (by rfl) ⟨490766, by rfl⟩ : syracuseStep 2617421 = 981533) (by norm_num)
theorem B3928157 : Blo 1744573 3928157 := bbase (se 3 (by rfl) ⟨736529, by rfl⟩ : syracuseStep 3928157 = 1473059) (by norm_num)
theorem B2617445 : Blo 1744573 2617445 := bbase (se 4 (by rfl) ⟨245385, by rfl⟩ : syracuseStep 2617445 = 490771) (by norm_num)
theorem B5894261 : Blo 1744573 5894261 := bbase (se 5 (by rfl) ⟨276293, by rfl⟩ : syracuseStep 5894261 = 552587) (by norm_num)
theorem B2617469 : Blo 1744573 2617469 := bbase (se 3 (by rfl) ⟨490775, by rfl⟩ : syracuseStep 2617469 = 981551) (by norm_num)
theorem B2617493 : Blo 1744573 2617493 := bbase (se 6 (by rfl) ⟨61347, by rfl⟩ : syracuseStep 2617493 = 122695) (by norm_num)
theorem B2945173 : Blo 1744573 2945173 := bbase (se 6 (by rfl) ⟨69027, by rfl⟩ : syracuseStep 2945173 = 138055) (by norm_num)
theorem B3928229 : Blo 1744573 3928229 := bbase (se 4 (by rfl) ⟨368271, by rfl⟩ : syracuseStep 3928229 = 736543) (by norm_num)
theorem B2617517 : Blo 1744573 2617517 := bbase (se 3 (by rfl) ⟨490784, by rfl⟩ : syracuseStep 2617517 = 981569) (by norm_num)
theorem B2617541 : Blo 1744573 2617541 := bbase (se 4 (by rfl) ⟨245394, by rfl⟩ : syracuseStep 2617541 = 490789) (by norm_num)
theorem B2486477 : Blo 1744573 2486477 := bbase (se 3 (by rfl) ⟨466214, by rfl⟩ : syracuseStep 2486477 = 932429) (by norm_num)
theorem B2617565 : Blo 1744573 2617565 := bbase (se 3 (by rfl) ⟨490793, by rfl⟩ : syracuseStep 2617565 = 981587) (by norm_num)
theorem B1863901 : Blo 1744573 1863901 := bbase (se 3 (by rfl) ⟨349481, by rfl⟩ : syracuseStep 1863901 = 698963) (by norm_num)
theorem B4419805 : Blo 1744573 4419805 := bbase (se 3 (by rfl) ⟨828713, by rfl⟩ : syracuseStep 4419805 = 1657427) (by norm_num)
theorem B1863905 : Blo 1744573 1863905 := bbase (se 2 (by rfl) ⟨698964, by rfl⟩ : syracuseStep 1863905 = 1397929) (by norm_num)
theorem B2945261 : Blo 1744573 2945261 := bbase (se 3 (by rfl) ⟨552236, by rfl⟩ : syracuseStep 2945261 = 1104473) (by norm_num)
theorem B3928301 : Blo 1744573 3928301 := bbase (se 3 (by rfl) ⟨736556, by rfl⟩ : syracuseStep 3928301 = 1473113) (by norm_num)
theorem B2207989 : Blo 1744573 2207989 := bbase (se 5 (by rfl) ⟨103499, by rfl⟩ : syracuseStep 2207989 = 206999) (by norm_num)
theorem B2617589 : Blo 1744573 2617589 := bbase (se 5 (by rfl) ⟨122699, by rfl⟩ : syracuseStep 2617589 = 245399) (by norm_num)
theorem B8835317 : Blo 1744573 8835317 := bbase (se 5 (by rfl) ⟨414155, by rfl⟩ : syracuseStep 8835317 = 828311) (by norm_num)
theorem B9941237 : Blo 1744573 9941237 := bbase (se 5 (by rfl) ⟨465995, by rfl⟩ : syracuseStep 9941237 = 931991) (by norm_num)
theorem B2617613 : Blo 1744573 2617613 := bbase (se 3 (by rfl) ⟨490802, by rfl⟩ : syracuseStep 2617613 = 981605) (by norm_num)
theorem B6721813 : Blo 1744573 6721813 := bbase (se 6 (by rfl) ⟨157542, by rfl⟩ : syracuseStep 6721813 = 315085) (by norm_num)
theorem B2617637 : Blo 1744573 2617637 := bbase (se 4 (by rfl) ⟨245403, by rfl⟩ : syracuseStep 2617637 = 490807) (by norm_num)
theorem B3313973 : Blo 1744573 3313973 := bbase (se 5 (by rfl) ⟨155342, by rfl⟩ : syracuseStep 3313973 = 310685) (by norm_num)
theorem B3928373 : Blo 1744573 3928373 := bbase (se 5 (by rfl) ⟨184142, by rfl⟩ : syracuseStep 3928373 = 368285) (by norm_num)
theorem B2617661 : Blo 1744573 2617661 := bbase (se 3 (by rfl) ⟨490811, by rfl⟩ : syracuseStep 2617661 = 981623) (by norm_num)
theorem B4968773 : Blo 1744573 4968773 := bbase (se 4 (by rfl) ⟨465822, by rfl⟩ : syracuseStep 4968773 = 931645) (by norm_num)
theorem B4419917 : Blo 1744573 4419917 := bbase (se 3 (by rfl) ⟨828734, by rfl⟩ : syracuseStep 4419917 = 1657469) (by norm_num)
theorem B2617685 : Blo 1744573 2617685 := bbase (se 10 (by rfl) ⟨3834, by rfl⟩ : syracuseStep 2617685 = 7669) (by norm_num)
theorem B2617709 : Blo 1744573 2617709 := bbase (se 3 (by rfl) ⟨490820, by rfl⟩ : syracuseStep 2617709 = 981641) (by norm_num)
theorem B2945389 : Blo 1744573 2945389 := bbase (se 3 (by rfl) ⟨552260, by rfl⟩ : syracuseStep 2945389 = 1104521) (by norm_num)
theorem B3928445 : Blo 1744573 3928445 := bbase (se 3 (by rfl) ⟨736583, by rfl⟩ : syracuseStep 3928445 = 1473167) (by norm_num)
theorem B2617733 : Blo 1744573 2617733 := bbase (se 4 (by rfl) ⟨245412, by rfl⟩ : syracuseStep 2617733 = 490825) (by norm_num)
theorem B2617757 : Blo 1744573 2617757 := bbase (se 3 (by rfl) ⟨490829, by rfl⟩ : syracuseStep 2617757 = 981659) (by norm_num)
theorem B2208161 : Blo 1744573 2208161 := bbase (se 2 (by rfl) ⟨828060, by rfl⟩ : syracuseStep 2208161 = 1656121) (by norm_num)
theorem B2617781 : Blo 1744573 2617781 := bbase (se 5 (by rfl) ⟨122708, by rfl⟩ : syracuseStep 2617781 = 245417) (by norm_num)
theorem B2945477 : Blo 1744573 2945477 := bbase (se 4 (by rfl) ⟨276138, by rfl⟩ : syracuseStep 2945477 = 552277) (by norm_num)
theorem B3928517 : Blo 1744573 3928517 := bbase (se 4 (by rfl) ⟨368298, by rfl⟩ : syracuseStep 3928517 = 736597) (by norm_num)
theorem B2617805 : Blo 1744573 2617805 := bbase (se 3 (by rfl) ⟨490838, by rfl⟩ : syracuseStep 2617805 = 981677) (by norm_num)
theorem B3314125 : Blo 1744573 3314125 := bbase (se 3 (by rfl) ⟨621398, by rfl⟩ : syracuseStep 3314125 = 1242797) (by norm_num)
theorem B2208217 : Blo 1744573 2208217 := bbase (se 2 (by rfl) ⟨828081, by rfl⟩ : syracuseStep 2208217 = 1656163) (by norm_num)
theorem B2617829 : Blo 1744573 2617829 := bbase (se 4 (by rfl) ⟨245421, by rfl⟩ : syracuseStep 2617829 = 490843) (by norm_num)
theorem B2617853 : Blo 1744573 2617853 := bbase (se 3 (by rfl) ⟨490847, by rfl⟩ : syracuseStep 2617853 = 981695) (by norm_num)
theorem B3928589 : Blo 1744573 3928589 := bbase (se 3 (by rfl) ⟨736610, by rfl⟩ : syracuseStep 3928589 = 1473221) (by norm_num)
theorem B4420109 : Blo 1744573 4420109 := bbase (se 3 (by rfl) ⟨828770, by rfl⟩ : syracuseStep 4420109 = 1657541) (by norm_num)
theorem B2617877 : Blo 1744573 2617877 := bbase (se 6 (by rfl) ⟨61356, by rfl⟩ : syracuseStep 2617877 = 122713) (by norm_num)
theorem B2617901 : Blo 1744573 2617901 := bbase (se 3 (by rfl) ⟨490856, by rfl⟩ : syracuseStep 2617901 = 981713) (by norm_num)
theorem B2208313 : Blo 1744573 2208313 := bbase (se 2 (by rfl) ⟨828117, by rfl⟩ : syracuseStep 2208313 = 1656235) (by norm_num)
theorem B2617925 : Blo 1744573 2617925 := bbase (se 4 (by rfl) ⟨245430, by rfl⟩ : syracuseStep 2617925 = 490861) (by norm_num)
theorem B2945605 : Blo 1744573 2945605 := bbase (se 4 (by rfl) ⟨276150, by rfl⟩ : syracuseStep 2945605 = 552301) (by norm_num)
theorem B9433685 : Blo 1744573 9433685 := bbase (se 8 (by rfl) ⟨55275, by rfl⟩ : syracuseStep 9433685 = 110551) (by norm_num)
theorem B3928661 : Blo 1744573 3928661 := bbase (se 8 (by rfl) ⟨23019, by rfl⟩ : syracuseStep 3928661 = 46039) (by norm_num)
theorem B2617949 : Blo 1744573 2617949 := bbase (se 3 (by rfl) ⟨490865, by rfl⟩ : syracuseStep 2617949 = 981731) (by norm_num)
theorem B2617973 : Blo 1744573 2617973 := bbase (se 5 (by rfl) ⟨122717, by rfl⟩ : syracuseStep 2617973 = 245435) (by norm_num)
theorem B2617997 : Blo 1744573 2617997 := bbase (se 3 (by rfl) ⟨490874, by rfl⟩ : syracuseStep 2617997 = 981749) (by norm_num)
theorem B2945693 : Blo 1744573 2945693 := bbase (se 3 (by rfl) ⟨552317, by rfl⟩ : syracuseStep 2945693 = 1104635) (by norm_num)
theorem B3928733 : Blo 1744573 3928733 := bbase (se 3 (by rfl) ⟨736637, by rfl⟩ : syracuseStep 3928733 = 1473275) (by norm_num)
theorem B1962661 : Blo 1744573 1962661 := bbase (se 4 (by rfl) ⟨183999, by rfl⟩ : syracuseStep 1962661 = 367999) (by norm_num)
theorem B2618021 : Blo 1744573 2618021 := bbase (se 4 (by rfl) ⟨245439, by rfl⟩ : syracuseStep 2618021 = 490879) (by norm_num)
theorem B2618045 : Blo 1744573 2618045 := bbase (se 3 (by rfl) ⟨490883, by rfl⟩ : syracuseStep 2618045 = 981767) (by norm_num)
theorem B1962697 : Blo 1744573 1962697 := bbase (se 2 (by rfl) ⟨736011, by rfl⟩ : syracuseStep 1962697 = 1472023) (by norm_num)
theorem B2618069 : Blo 1744573 2618069 := bbase (se 7 (by rfl) ⟨30680, by rfl⟩ : syracuseStep 2618069 = 61361) (by norm_num)
theorem B2208485 : Blo 1744573 2208485 := bbase (se 4 (by rfl) ⟨207045, by rfl⟩ : syracuseStep 2208485 = 414091) (by norm_num)
theorem B2872037 : Blo 1744573 2872037 := bbase (se 4 (by rfl) ⟨269253, by rfl⟩ : syracuseStep 2872037 = 538507) (by norm_num)
theorem B3928805 : Blo 1744573 3928805 := bbase (se 4 (by rfl) ⟨368325, by rfl⟩ : syracuseStep 3928805 = 736651) (by norm_num)
theorem B1962733 : Blo 1744573 1962733 := bbase (se 3 (by rfl) ⟨368012, by rfl⟩ : syracuseStep 1962733 = 736025) (by norm_num)
theorem B2618093 : Blo 1744573 2618093 := bbase (se 3 (by rfl) ⟨490892, by rfl⟩ : syracuseStep 2618093 = 981785) (by norm_num)
theorem B3314429 : Blo 1744573 3314429 := bbase (se 3 (by rfl) ⟨621455, by rfl⟩ : syracuseStep 3314429 = 1242911) (by norm_num)
theorem B2618117 : Blo 1744573 2618117 := bbase (se 4 (by rfl) ⟨245448, by rfl⟩ : syracuseStep 2618117 = 490897) (by norm_num)
theorem B1962769 : Blo 1744573 1962769 := bbase (se 2 (by rfl) ⟨736038, by rfl⟩ : syracuseStep 1962769 = 1472077) (by norm_num)
theorem B1864469 : Blo 1744573 1864469 := bbase (se 6 (by rfl) ⟨43698, by rfl⟩ : syracuseStep 1864469 = 87397) (by norm_num)
theorem B2208541 : Blo 1744573 2208541 := bbase (se 3 (by rfl) ⟨414101, by rfl⟩ : syracuseStep 2208541 = 828203) (by norm_num)
theorem B2618141 : Blo 1744573 2618141 := bbase (se 3 (by rfl) ⟨490901, by rfl⟩ : syracuseStep 2618141 = 981803) (by norm_num)
theorem B2945821 : Blo 1744573 2945821 := bbase (se 3 (by rfl) ⟨552341, by rfl⟩ : syracuseStep 2945821 = 1104683) (by norm_num)
theorem B3928877 : Blo 1744573 3928877 := bbase (se 3 (by rfl) ⟨736664, by rfl⟩ : syracuseStep 3928877 = 1473329) (by norm_num)
theorem B1962805 : Blo 1744573 1962805 := bbase (se 5 (by rfl) ⟨92006, by rfl⟩ : syracuseStep 1962805 = 184013) (by norm_num)
theorem B2618165 : Blo 1744573 2618165 := bbase (se 5 (by rfl) ⟨122726, by rfl⟩ : syracuseStep 2618165 = 245453) (by norm_num)
theorem B2618189 : Blo 1744573 2618189 := bbase (se 3 (by rfl) ⟨490910, by rfl⟩ : syracuseStep 2618189 = 981821) (by norm_num)
theorem B5665621 : Blo 1744573 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B1962841 : Blo 1744573 1962841 := bbase (se 2 (by rfl) ⟨736065, by rfl⟩ : syracuseStep 1962841 = 1472131) (by norm_num)
theorem B2618213 : Blo 1744573 2618213 := bbase (se 4 (by rfl) ⟨245457, by rfl⟩ : syracuseStep 2618213 = 490915) (by norm_num)
theorem B5591909 : Blo 1744573 5591909 := bbase (se 4 (by rfl) ⟨524241, by rfl⟩ : syracuseStep 5591909 = 1048483) (by norm_num)
theorem B4420453 : Blo 1744573 4420453 := bbase (se 4 (by rfl) ⟨414417, by rfl⟩ : syracuseStep 4420453 = 828835) (by norm_num)
theorem B2945909 : Blo 1744573 2945909 := bbase (se 5 (by rfl) ⟨138089, by rfl⟩ : syracuseStep 2945909 = 276179) (by norm_num)
theorem B3928949 : Blo 1744573 3928949 := bbase (se 5 (by rfl) ⟨184169, by rfl⟩ : syracuseStep 3928949 = 368339) (by norm_num)
theorem B1962877 : Blo 1744573 1962877 := bbase (se 3 (by rfl) ⟨368039, by rfl⟩ : syracuseStep 1962877 = 736079) (by norm_num)
theorem B2208637 : Blo 1744573 2208637 := bbase (se 3 (by rfl) ⟨414119, by rfl⟩ : syracuseStep 2208637 = 828239) (by norm_num)
theorem B2618237 : Blo 1744573 2618237 := bbase (se 3 (by rfl) ⟨490919, by rfl⟩ : syracuseStep 2618237 = 981839) (by norm_num)
theorem B2618261 : Blo 1744573 2618261 := bbase (se 6 (by rfl) ⟨61365, by rfl⟩ : syracuseStep 2618261 = 122731) (by norm_num)
theorem B1962913 : Blo 1744573 1962913 := bbase (se 2 (by rfl) ⟨736092, by rfl⟩ : syracuseStep 1962913 = 1472185) (by norm_num)
theorem B2618285 : Blo 1744573 2618285 := bbase (se 3 (by rfl) ⟨490928, by rfl⟩ : syracuseStep 2618285 = 981857) (by norm_num)
theorem B3929021 : Blo 1744573 3929021 := bbase (se 3 (by rfl) ⟨736691, by rfl⟩ : syracuseStep 3929021 = 1473383) (by norm_num)
theorem B1962949 : Blo 1744573 1962949 := bbase (se 4 (by rfl) ⟨184026, by rfl⟩ : syracuseStep 1962949 = 368053) (by norm_num)
theorem B2618309 : Blo 1744573 2618309 := bbase (se 4 (by rfl) ⟨245466, by rfl⟩ : syracuseStep 2618309 = 490933) (by norm_num)
theorem B1864657 : Blo 1744573 1864657 := bbase (se 2 (by rfl) ⟨699246, by rfl⟩ : syracuseStep 1864657 = 1398493) (by norm_num)
theorem B4420565 : Blo 1744573 4420565 := bbase (se 7 (by rfl) ⟨51803, by rfl⟩ : syracuseStep 4420565 = 103607) (by norm_num)
theorem B2618333 : Blo 1744573 2618333 := bbase (se 3 (by rfl) ⟨490937, by rfl⟩ : syracuseStep 2618333 = 981875) (by norm_num)
theorem B1962985 : Blo 1744573 1962985 := bbase (se 2 (by rfl) ⟨736119, by rfl⟩ : syracuseStep 1962985 = 1472239) (by norm_num)
theorem B2618357 : Blo 1744573 2618357 := bbase (se 5 (by rfl) ⟨122735, by rfl⟩ : syracuseStep 2618357 = 245471) (by norm_num)
theorem B2946037 : Blo 1744573 2946037 := bbase (se 5 (by rfl) ⟨138095, by rfl⟩ : syracuseStep 2946037 = 276191) (by norm_num)
theorem B3929093 : Blo 1744573 3929093 := bbase (se 4 (by rfl) ⟨368352, by rfl⟩ : syracuseStep 3929093 = 736705) (by norm_num)
theorem B1963021 : Blo 1744573 1963021 := bbase (se 3 (by rfl) ⟨368066, by rfl⟩ : syracuseStep 1963021 = 736133) (by norm_num)
theorem B2618381 : Blo 1744573 2618381 := bbase (se 3 (by rfl) ⟨490946, by rfl⟩ : syracuseStep 2618381 = 981893) (by norm_num)
theorem B2618405 : Blo 1744573 2618405 := bbase (se 4 (by rfl) ⟨245475, by rfl⟩ : syracuseStep 2618405 = 490951) (by norm_num)
theorem B2208809 : Blo 1744573 2208809 := bbase (se 2 (by rfl) ⟨828303, by rfl⟩ : syracuseStep 2208809 = 1656607) (by norm_num)
theorem B1963057 : Blo 1744573 1963057 := bbase (se 2 (by rfl) ⟨736146, by rfl⟩ : syracuseStep 1963057 = 1472293) (by norm_num)
theorem B4969525 : Blo 1744573 4969525 := bbase (se 5 (by rfl) ⟨232946, by rfl⟩ : syracuseStep 4969525 = 465893) (by norm_num)
theorem B2618429 : Blo 1744573 2618429 := bbase (se 3 (by rfl) ⟨490955, by rfl⟩ : syracuseStep 2618429 = 981911) (by norm_num)
theorem B2946125 : Blo 1744573 2946125 := bbase (se 3 (by rfl) ⟨552398, by rfl⟩ : syracuseStep 2946125 = 1104797) (by norm_num)
theorem B3929165 : Blo 1744573 3929165 := bbase (se 3 (by rfl) ⟨736718, by rfl⟩ : syracuseStep 3929165 = 1473437) (by norm_num)
theorem B1963093 : Blo 1744573 1963093 := bbase (se 8 (by rfl) ⟨11502, by rfl⟩ : syracuseStep 1963093 = 23005) (by norm_num)
theorem B2618453 : Blo 1744573 2618453 := bbase (se 8 (by rfl) ⟨15342, by rfl⟩ : syracuseStep 2618453 = 30685) (by norm_num)
theorem B2208865 : Blo 1744573 2208865 := bbase (se 2 (by rfl) ⟨828324, by rfl⟩ : syracuseStep 2208865 = 1656649) (by norm_num)
theorem B2618477 : Blo 1744573 2618477 := bbase (se 3 (by rfl) ⟨490964, by rfl⟩ : syracuseStep 2618477 = 981929) (by norm_num)
theorem B1963129 : Blo 1744573 1963129 := bbase (se 2 (by rfl) ⟨736173, by rfl⟩ : syracuseStep 1963129 = 1472347) (by norm_num)
theorem B2618501 : Blo 1744573 2618501 := bbase (se 4 (by rfl) ⟨245484, by rfl⟩ : syracuseStep 2618501 = 490969) (by norm_num)
theorem B5969045 : Blo 1744573 5969045 := bbase (se 6 (by rfl) ⟨139899, by rfl⟩ : syracuseStep 5969045 = 279799) (by norm_num)
theorem B3929237 : Blo 1744573 3929237 := bbase (se 6 (by rfl) ⟨92091, by rfl⟩ : syracuseStep 3929237 = 184183) (by norm_num)
theorem B1963165 : Blo 1744573 1963165 := bbase (se 3 (by rfl) ⟨368093, by rfl⟩ : syracuseStep 1963165 = 736187) (by norm_num)
theorem B2618525 : Blo 1744573 2618525 := bbase (se 3 (by rfl) ⟨490973, by rfl⟩ : syracuseStep 2618525 = 981947) (by norm_num)
theorem B2618549 : Blo 1744573 2618549 := bbase (se 5 (by rfl) ⟨122744, by rfl⟩ : syracuseStep 2618549 = 245489) (by norm_num)
theorem B1963201 : Blo 1744573 1963201 := bbase (se 2 (by rfl) ⟨736200, by rfl⟩ : syracuseStep 1963201 = 1472401) (by norm_num)
theorem B2208961 : Blo 1744573 2208961 := bbase (se 2 (by rfl) ⟨828360, by rfl⟩ : syracuseStep 2208961 = 1656721) (by norm_num)
theorem B2618573 : Blo 1744573 2618573 := bbase (se 3 (by rfl) ⟨490982, by rfl⟩ : syracuseStep 2618573 = 981965) (by norm_num)
theorem B2946253 : Blo 1744573 2946253 := bbase (se 3 (by rfl) ⟨552422, by rfl⟩ : syracuseStep 2946253 = 1104845) (by norm_num)
theorem B3929309 : Blo 1744573 3929309 := bbase (se 3 (by rfl) ⟨736745, by rfl⟩ : syracuseStep 3929309 = 1473491) (by norm_num)
theorem B1963237 : Blo 1744573 1963237 := bbase (se 4 (by rfl) ⟨184053, by rfl⟩ : syracuseStep 1963237 = 368107) (by norm_num)
theorem B2618597 : Blo 1744573 2618597 := bbase (se 4 (by rfl) ⟨245493, by rfl⟩ : syracuseStep 2618597 = 490987) (by norm_num)
theorem B2618621 : Blo 1744573 2618621 := bbase (se 3 (by rfl) ⟨490991, by rfl⟩ : syracuseStep 2618621 = 981983) (by norm_num)
theorem B1963273 : Blo 1744573 1963273 := bbase (se 2 (by rfl) ⟨736227, by rfl⟩ : syracuseStep 1963273 = 1472455) (by norm_num)
theorem B2618645 : Blo 1744573 2618645 := bbase (se 6 (by rfl) ⟨61374, by rfl⟩ : syracuseStep 2618645 = 122749) (by norm_num)
theorem B2946341 : Blo 1744573 2946341 := bbase (se 4 (by rfl) ⟨276219, by rfl⟩ : syracuseStep 2946341 = 552439) (by norm_num)
theorem B3929381 : Blo 1744573 3929381 := bbase (se 4 (by rfl) ⟨368379, by rfl⟩ : syracuseStep 3929381 = 736759) (by norm_num)
theorem B1963309 : Blo 1744573 1963309 := bbase (se 3 (by rfl) ⟨368120, by rfl⟩ : syracuseStep 1963309 = 736241) (by norm_num)
theorem B2618669 : Blo 1744573 2618669 := bbase (se 3 (by rfl) ⟨491000, by rfl⟩ : syracuseStep 2618669 = 982001) (by norm_num)
theorem B2618693 : Blo 1744573 2618693 := bbase (se 4 (by rfl) ⟨245502, by rfl⟩ : syracuseStep 2618693 = 491005) (by norm_num)
theorem B1963345 : Blo 1744573 1963345 := bbase (se 2 (by rfl) ⟨736254, by rfl⟩ : syracuseStep 1963345 = 1472509) (by norm_num)
theorem B2618717 : Blo 1744573 2618717 := bbase (se 3 (by rfl) ⟨491009, by rfl⟩ : syracuseStep 2618717 = 982019) (by norm_num)
theorem B2209133 : Blo 1744573 2209133 := bbase (se 3 (by rfl) ⟨414212, by rfl⟩ : syracuseStep 2209133 = 828425) (by norm_num)
theorem B3929453 : Blo 1744573 3929453 := bbase (se 3 (by rfl) ⟨736772, by rfl⟩ : syracuseStep 3929453 = 1473545) (by norm_num)
theorem B1963381 : Blo 1744573 1963381 := bbase (se 5 (by rfl) ⟨92033, by rfl⟩ : syracuseStep 1963381 = 184067) (by norm_num)
theorem B2618741 : Blo 1744573 2618741 := bbase (se 5 (by rfl) ⟨122753, by rfl⟩ : syracuseStep 2618741 = 245507) (by norm_num)
theorem B2618765 : Blo 1744573 2618765 := bbase (se 3 (by rfl) ⟨491018, by rfl⟩ : syracuseStep 2618765 = 982037) (by norm_num)
theorem B1963417 : Blo 1744573 1963417 := bbase (se 2 (by rfl) ⟨736281, by rfl⟩ : syracuseStep 1963417 = 1472563) (by norm_num)
theorem B2209189 : Blo 1744573 2209189 := bbase (se 4 (by rfl) ⟨207111, by rfl⟩ : syracuseStep 2209189 = 414223) (by norm_num)
theorem B2618789 : Blo 1744573 2618789 := bbase (se 4 (by rfl) ⟨245511, by rfl⟩ : syracuseStep 2618789 = 491023) (by norm_num)
theorem B2946469 : Blo 1744573 2946469 := bbase (se 4 (by rfl) ⟨276231, by rfl⟩ : syracuseStep 2946469 = 552463) (by norm_num)
theorem B3929525 : Blo 1744573 3929525 := bbase (se 5 (by rfl) ⟨184196, by rfl⟩ : syracuseStep 3929525 = 368393) (by norm_num)
theorem B1963453 : Blo 1744573 1963453 := bbase (se 3 (by rfl) ⟨368147, by rfl⟩ : syracuseStep 1963453 = 736295) (by norm_num)
theorem B2618813 : Blo 1744573 2618813 := bbase (se 3 (by rfl) ⟨491027, by rfl⟩ : syracuseStep 2618813 = 982055) (by norm_num)
theorem B7452101 : Blo 1744573 7452101 := bbase (se 4 (by rfl) ⟨698634, by rfl⟩ : syracuseStep 7452101 = 1397269) (by norm_num)
theorem B2618837 : Blo 1744573 2618837 := bbase (se 7 (by rfl) ⟨30689, by rfl⟩ : syracuseStep 2618837 = 61379) (by norm_num)
theorem B1963489 : Blo 1744573 1963489 := bbase (se 2 (by rfl) ⟨736308, by rfl⟩ : syracuseStep 1963489 = 1472617) (by norm_num)
theorem B2618861 : Blo 1744573 2618861 := bbase (se 3 (by rfl) ⟨491036, by rfl⟩ : syracuseStep 2618861 = 982073) (by norm_num)
theorem B3315181 : Blo 1744573 3315181 := bbase (se 3 (by rfl) ⟨621596, by rfl⟩ : syracuseStep 3315181 = 1243193) (by norm_num)
theorem B8386037 : Blo 1744573 8386037 := bbase (se 5 (by rfl) ⟨393095, by rfl⟩ : syracuseStep 8386037 = 786191) (by norm_num)
theorem B12269045 : Blo 1744573 12269045 := bbase (se 5 (by rfl) ⟨575111, by rfl⟩ : syracuseStep 12269045 = 1150223) (by norm_num)
theorem B2946557 : Blo 1744573 2946557 := bbase (se 3 (by rfl) ⟨552479, by rfl⟩ : syracuseStep 2946557 = 1104959) (by norm_num)
theorem B3929597 : Blo 1744573 3929597 := bbase (se 3 (by rfl) ⟨736799, by rfl⟩ : syracuseStep 3929597 = 1473599) (by norm_num)
theorem B6624773 : Blo 1744573 6624773 := bbase (se 4 (by rfl) ⟨621072, by rfl⟩ : syracuseStep 6624773 = 1242145) (by norm_num)
theorem B1963525 : Blo 1744573 1963525 := bbase (se 4 (by rfl) ⟨184080, by rfl⟩ : syracuseStep 1963525 = 368161) (by norm_num)
theorem B8836613 : Blo 1744573 8836613 := bbase (se 4 (by rfl) ⟨828432, by rfl⟩ : syracuseStep 8836613 = 1656865) (by norm_num)
theorem B2209285 : Blo 1744573 2209285 := bbase (se 4 (by rfl) ⟨207120, by rfl⟩ : syracuseStep 2209285 = 414241) (by norm_num)
theorem B2618885 : Blo 1744573 2618885 := bbase (se 4 (by rfl) ⟨245520, by rfl⟩ : syracuseStep 2618885 = 491041) (by norm_num)
theorem B17913365 : Blo 1744573 17913365 := bbase (se 6 (by rfl) ⟨419844, by rfl⟩ : syracuseStep 17913365 = 839689) (by norm_num)
theorem B2618909 : Blo 1744573 2618909 := bbase (se 3 (by rfl) ⟨491045, by rfl⟩ : syracuseStep 2618909 = 982091) (by norm_num)
theorem B1963561 : Blo 1744573 1963561 := bbase (se 2 (by rfl) ⟨736335, by rfl⟩ : syracuseStep 1963561 = 1472671) (by norm_num)
theorem B2618933 : Blo 1744573 2618933 := bbase (se 5 (by rfl) ⟨122762, by rfl⟩ : syracuseStep 2618933 = 245525) (by norm_num)
theorem B3929669 : Blo 1744573 3929669 := bbase (se 4 (by rfl) ⟨368406, by rfl⟩ : syracuseStep 3929669 = 736813) (by norm_num)
theorem B1963597 : Blo 1744573 1963597 := bbase (se 3 (by rfl) ⟨368174, by rfl⟩ : syracuseStep 1963597 = 736349) (by norm_num)
theorem B2618957 : Blo 1744573 2618957 := bbase (se 3 (by rfl) ⟨491054, by rfl⟩ : syracuseStep 2618957 = 982109) (by norm_num)
theorem B2618981 : Blo 1744573 2618981 := bbase (se 4 (by rfl) ⟨245529, by rfl⟩ : syracuseStep 2618981 = 491059) (by norm_num)
theorem B1963633 : Blo 1744573 1963633 := bbase (se 2 (by rfl) ⟨736362, by rfl⟩ : syracuseStep 1963633 = 1472725) (by norm_num)
theorem B2619005 : Blo 1744573 2619005 := bbase (se 3 (by rfl) ⟨491063, by rfl⟩ : syracuseStep 2619005 = 982127) (by norm_num)
theorem B2946685 : Blo 1744573 2946685 := bbase (se 3 (by rfl) ⟨552503, by rfl⟩ : syracuseStep 2946685 = 1105007) (by norm_num)
theorem B3315325 : Blo 1744573 3315325 := bbase (se 3 (by rfl) ⟨621623, by rfl⟩ : syracuseStep 3315325 = 1243247) (by norm_num)
theorem B3929741 : Blo 1744573 3929741 := bbase (se 3 (by rfl) ⟨736826, by rfl⟩ : syracuseStep 3929741 = 1473653) (by norm_num)
theorem B1963669 : Blo 1744573 1963669 := bbase (se 6 (by rfl) ⟨46023, by rfl⟩ : syracuseStep 1963669 = 92047) (by norm_num)
theorem B2619029 : Blo 1744573 2619029 := bbase (se 6 (by rfl) ⟨61383, by rfl⟩ : syracuseStep 2619029 = 122767) (by norm_num)
theorem B2619053 : Blo 1744573 2619053 := bbase (se 3 (by rfl) ⟨491072, by rfl⟩ : syracuseStep 2619053 = 982145) (by norm_num)
theorem B2209457 : Blo 1744573 2209457 := bbase (se 2 (by rfl) ⟨828546, by rfl⟩ : syracuseStep 2209457 = 1657093) (by norm_num)
theorem B1963705 : Blo 1744573 1963705 := bbase (se 2 (by rfl) ⟨736389, by rfl⟩ : syracuseStep 1963705 = 1472779) (by norm_num)
theorem B2619077 : Blo 1744573 2619077 := bbase (se 4 (by rfl) ⟨245538, by rfl⟩ : syracuseStep 2619077 = 491077) (by norm_num)
theorem B2946773 : Blo 1744573 2946773 := bbase (se 7 (by rfl) ⟨34532, by rfl⟩ : syracuseStep 2946773 = 69065) (by norm_num)
theorem B1963741 : Blo 1744573 1963741 := bbase (se 3 (by rfl) ⟨368201, by rfl⟩ : syracuseStep 1963741 = 736403) (by norm_num)
theorem B2619101 : Blo 1744573 2619101 := bbase (se 3 (by rfl) ⟨491081, by rfl⟩ : syracuseStep 2619101 = 982163) (by norm_num)
theorem B2209513 : Blo 1744573 2209513 := bbase (se 2 (by rfl) ⟨828567, by rfl⟩ : syracuseStep 2209513 = 1657135) (by norm_num)
theorem B2619125 : Blo 1744573 2619125 := bbase (se 5 (by rfl) ⟨122771, by rfl⟩ : syracuseStep 2619125 = 245543) (by norm_num)
theorem B1963777 : Blo 1744573 1963777 := bbase (se 2 (by rfl) ⟨736416, by rfl⟩ : syracuseStep 1963777 = 1472833) (by norm_num)
theorem B2619149 : Blo 1744573 2619149 := bbase (se 3 (by rfl) ⟨491090, by rfl⟩ : syracuseStep 2619149 = 982181) (by norm_num)
theorem B8386325 : Blo 1744573 8386325 := bbase (se 6 (by rfl) ⟨196554, by rfl⟩ : syracuseStep 8386325 = 393109) (by norm_num)
theorem B3315485 : Blo 1744573 3315485 := bbase (se 3 (by rfl) ⟨621653, by rfl⟩ : syracuseStep 3315485 = 1243307) (by norm_num)
theorem B6625061 : Blo 1744573 6625061 := bbase (se 4 (by rfl) ⟨621099, by rfl⟩ : syracuseStep 6625061 = 1242199) (by norm_num)
theorem B1963813 : Blo 1744573 1963813 := bbase (se 4 (by rfl) ⟨184107, by rfl⟩ : syracuseStep 1963813 = 368215) (by norm_num)
theorem B2619173 : Blo 1744573 2619173 := bbase (se 4 (by rfl) ⟨245547, by rfl⟩ : syracuseStep 2619173 = 491095) (by norm_num)
theorem B2619197 : Blo 1744573 2619197 := bbase (se 3 (by rfl) ⟨491099, by rfl⟩ : syracuseStep 2619197 = 982199) (by norm_num)
theorem B1963849 : Blo 1744573 1963849 := bbase (se 2 (by rfl) ⟨736443, by rfl⟩ : syracuseStep 1963849 = 1472887) (by norm_num)
theorem B2209609 : Blo 1744573 2209609 := bbase (se 2 (by rfl) ⟨828603, by rfl⟩ : syracuseStep 2209609 = 1657207) (by norm_num)
theorem B2619221 : Blo 1744573 2619221 := bbase (se 9 (by rfl) ⟨7673, by rfl⟩ : syracuseStep 2619221 = 15347) (by norm_num)
theorem B2946901 : Blo 1744573 2946901 := bbase (se 9 (by rfl) ⟨8633, by rfl⟩ : syracuseStep 2946901 = 17267) (by norm_num)
theorem B1963885 : Blo 1744573 1963885 := bbase (se 3 (by rfl) ⟨368228, by rfl⟩ : syracuseStep 1963885 = 736457) (by norm_num)
theorem B2619245 : Blo 1744573 2619245 := bbase (se 3 (by rfl) ⟨491108, by rfl⟩ : syracuseStep 2619245 = 982217) (by norm_num)
theorem B2619269 : Blo 1744573 2619269 := bbase (se 4 (by rfl) ⟨245556, by rfl⟩ : syracuseStep 2619269 = 491113) (by norm_num)
theorem B1963921 : Blo 1744573 1963921 := bbase (se 2 (by rfl) ⟨736470, by rfl⟩ : syracuseStep 1963921 = 1472941) (by norm_num)
theorem B3536789 : Blo 1744573 3536789 := bbase (se 6 (by rfl) ⟨82893, by rfl⟩ : syracuseStep 3536789 = 165787) (by norm_num)
theorem B19879829 : Blo 1744573 19879829 := bbase (se 6 (by rfl) ⟨465933, by rfl⟩ : syracuseStep 19879829 = 931867) (by norm_num)
theorem B2619293 : Blo 1744573 2619293 := bbase (se 3 (by rfl) ⟨491117, by rfl⟩ : syracuseStep 2619293 = 982235) (by norm_num)
theorem B2946989 : Blo 1744573 2946989 := bbase (se 3 (by rfl) ⟨552560, by rfl⟩ : syracuseStep 2946989 = 1105121) (by norm_num)
theorem B3315629 : Blo 1744573 3315629 := bbase (se 3 (by rfl) ⟨621680, by rfl⟩ : syracuseStep 3315629 = 1243361) (by norm_num)
theorem B1963957 : Blo 1744573 1963957 := bbase (se 5 (by rfl) ⟨92060, by rfl⟩ : syracuseStep 1963957 = 184121) (by norm_num)
theorem B2619317 : Blo 1744573 2619317 := bbase (se 5 (by rfl) ⟨122780, by rfl⟩ : syracuseStep 2619317 = 245561) (by norm_num)
theorem B2619341 : Blo 1744573 2619341 := bbase (se 3 (by rfl) ⟨491126, by rfl⟩ : syracuseStep 2619341 = 982253) (by norm_num)
theorem B1963993 : Blo 1744573 1963993 := bbase (se 2 (by rfl) ⟨736497, by rfl⟩ : syracuseStep 1963993 = 1472995) (by norm_num)
theorem B2619365 : Blo 1744573 2619365 := bbase (se 4 (by rfl) ⟨245565, by rfl⟩ : syracuseStep 2619365 = 491131) (by norm_num)
theorem B2209781 : Blo 1744573 2209781 := bbase (se 5 (by rfl) ⟨103583, by rfl⟩ : syracuseStep 2209781 = 207167) (by norm_num)
theorem B1964029 : Blo 1744573 1964029 := bbase (se 3 (by rfl) ⟨368255, by rfl⟩ : syracuseStep 1964029 = 736511) (by norm_num)
theorem B2619389 : Blo 1744573 2619389 := bbase (se 3 (by rfl) ⟨491135, by rfl⟩ : syracuseStep 2619389 = 982271) (by norm_num)
theorem B2619413 : Blo 1744573 2619413 := bbase (se 6 (by rfl) ⟨61392, by rfl⟩ : syracuseStep 2619413 = 122785) (by norm_num)
theorem B1964065 : Blo 1744573 1964065 := bbase (se 2 (by rfl) ⟨736524, by rfl⟩ : syracuseStep 1964065 = 1473049) (by norm_num)
theorem B2209837 : Blo 1744573 2209837 := bbase (se 3 (by rfl) ⟨414344, by rfl⟩ : syracuseStep 2209837 = 828689) (by norm_num)
theorem B2619437 : Blo 1744573 2619437 := bbase (se 3 (by rfl) ⟨491144, by rfl⟩ : syracuseStep 2619437 = 982289) (by norm_num)
theorem B2947117 : Blo 1744573 2947117 := bbase (se 3 (by rfl) ⟨552584, by rfl⟩ : syracuseStep 2947117 = 1105169) (by norm_num)
theorem B1964101 : Blo 1744573 1964101 := bbase (se 4 (by rfl) ⟨184134, by rfl⟩ : syracuseStep 1964101 = 368269) (by norm_num)
theorem B2619461 : Blo 1744573 2619461 := bbase (se 4 (by rfl) ⟨245574, by rfl⟩ : syracuseStep 2619461 = 491149) (by norm_num)
theorem B2619485 : Blo 1744573 2619485 := bbase (se 3 (by rfl) ⟨491153, by rfl⟩ : syracuseStep 2619485 = 982307) (by norm_num)
theorem B1964137 : Blo 1744573 1964137 := bbase (se 2 (by rfl) ⟨736551, by rfl⟩ : syracuseStep 1964137 = 1473103) (by norm_num)
theorem B2619509 : Blo 1744573 2619509 := bbase (se 5 (by rfl) ⟨122789, by rfl⟩ : syracuseStep 2619509 = 245579) (by norm_num)
theorem B2947205 : Blo 1744573 2947205 := bbase (se 4 (by rfl) ⟨276300, by rfl⟩ : syracuseStep 2947205 = 552601) (by norm_num)
theorem B1964173 : Blo 1744573 1964173 := bbase (se 3 (by rfl) ⟨368282, by rfl⟩ : syracuseStep 1964173 = 736565) (by norm_num)
theorem B2209933 : Blo 1744573 2209933 := bbase (se 3 (by rfl) ⟨414362, by rfl⟩ : syracuseStep 2209933 = 828725) (by norm_num)
theorem B2619533 : Blo 1744573 2619533 := bbase (se 3 (by rfl) ⟨491162, by rfl⟩ : syracuseStep 2619533 = 982325) (by norm_num)
theorem B2619557 : Blo 1744573 2619557 := bbase (se 4 (by rfl) ⟨245583, by rfl⟩ : syracuseStep 2619557 = 491167) (by norm_num)
theorem B1964209 : Blo 1744573 1964209 := bbase (se 2 (by rfl) ⟨736578, by rfl⟩ : syracuseStep 1964209 = 1473157) (by norm_num)
theorem B2619581 : Blo 1744573 2619581 := bbase (se 3 (by rfl) ⟨491171, by rfl⟩ : syracuseStep 2619581 = 982343) (by norm_num)
theorem B3143893 : Blo 1744573 3143893 := bbase (se 7 (by rfl) ⟨36842, by rfl⟩ : syracuseStep 3143893 = 73685) (by norm_num)
theorem B5888213 : Blo 1744573 5888213 := bbase (se 7 (by rfl) ⟨69002, by rfl⟩ : syracuseStep 5888213 = 138005) (by norm_num)
theorem B1964245 : Blo 1744573 1964245 := bbase (se 7 (by rfl) ⟨23018, by rfl⟩ : syracuseStep 1964245 = 46037) (by norm_num)
theorem B50346197 : Blo 1744573 50346197 := bbase (se 7 (by rfl) ⟨589994, by rfl⟩ : syracuseStep 50346197 = 1179989) (by norm_num)
theorem B2619605 : Blo 1744573 2619605 := bbase (se 7 (by rfl) ⟨30698, by rfl⟩ : syracuseStep 2619605 = 61397) (by norm_num)
theorem B2619629 : Blo 1744573 2619629 := bbase (se 3 (by rfl) ⟨491180, by rfl⟩ : syracuseStep 2619629 = 982361) (by norm_num)
theorem B1964281 : Blo 1744573 1964281 := bbase (se 2 (by rfl) ⟨736605, by rfl⟩ : syracuseStep 1964281 = 1473211) (by norm_num)
theorem B2619653 : Blo 1744573 2619653 := bbase (se 4 (by rfl) ⟨245592, by rfl⟩ : syracuseStep 2619653 = 491185) (by norm_num)
theorem B2947333 : Blo 1744573 2947333 := bbase (se 4 (by rfl) ⟨276312, by rfl⟩ : syracuseStep 2947333 = 552625) (by norm_num)
theorem B6715669 : Blo 1744573 6715669 := bbase (se 6 (by rfl) ⟨157398, by rfl⟩ : syracuseStep 6715669 = 314797) (by norm_num)
theorem B1964317 : Blo 1744573 1964317 := bbase (se 3 (by rfl) ⟨368309, by rfl⟩ : syracuseStep 1964317 = 736619) (by norm_num)
theorem B2619677 : Blo 1744573 2619677 := bbase (se 3 (by rfl) ⟨491189, by rfl⟩ : syracuseStep 2619677 = 982379) (by norm_num)
theorem B2619701 : Blo 1744573 2619701 := bbase (se 5 (by rfl) ⟨122798, by rfl⟩ : syracuseStep 2619701 = 245597) (by norm_num)
theorem B2210105 : Blo 1744573 2210105 := bbase (se 2 (by rfl) ⟨828789, by rfl⟩ : syracuseStep 2210105 = 1657579) (by norm_num)
theorem B1964353 : Blo 1744573 1964353 := bbase (se 2 (by rfl) ⟨736632, by rfl⟩ : syracuseStep 1964353 = 1473265) (by norm_num)
theorem B2619725 : Blo 1744573 2619725 := bbase (se 3 (by rfl) ⟨491198, by rfl⟩ : syracuseStep 2619725 = 982397) (by norm_num)
theorem B1964389 : Blo 1744573 1964389 := bbase (se 4 (by rfl) ⟨184161, by rfl⟩ : syracuseStep 1964389 = 368323) (by norm_num)
theorem B2619749 : Blo 1744573 2619749 := bbase (se 4 (by rfl) ⟨245601, by rfl⟩ : syracuseStep 2619749 = 491203) (by norm_num)
theorem B2210161 : Blo 1744573 2210161 := bbase (se 2 (by rfl) ⟨828810, by rfl⟩ : syracuseStep 2210161 = 1657621) (by norm_num)
theorem B2619773 : Blo 1744573 2619773 := bbase (se 3 (by rfl) ⟨491207, by rfl⟩ : syracuseStep 2619773 = 982415) (by norm_num)
theorem B1964425 : Blo 1744573 1964425 := bbase (se 2 (by rfl) ⟨736659, by rfl⟩ : syracuseStep 1964425 = 1473319) (by norm_num)
theorem B2619797 : Blo 1744573 2619797 := bbase (se 6 (by rfl) ⟨61401, by rfl⟩ : syracuseStep 2619797 = 122803) (by norm_num)
theorem B1964461 : Blo 1744573 1964461 := bbase (se 3 (by rfl) ⟨368336, by rfl⟩ : syracuseStep 1964461 = 736673) (by norm_num)
theorem B2619821 : Blo 1744573 2619821 := bbase (se 3 (by rfl) ⟨491216, by rfl⟩ : syracuseStep 2619821 = 982433) (by norm_num)
theorem B2619845 : Blo 1744573 2619845 := bbase (se 4 (by rfl) ⟨245610, by rfl⟩ : syracuseStep 2619845 = 491221) (by norm_num)
theorem B1964497 : Blo 1744573 1964497 := bbase (se 2 (by rfl) ⟨736686, by rfl⟩ : syracuseStep 1964497 = 1473373) (by norm_num)
theorem B2210257 : Blo 1744573 2210257 := bbase (se 2 (by rfl) ⟨828846, by rfl⟩ : syracuseStep 2210257 = 1657693) (by norm_num)
theorem B1964533 : Blo 1744573 1964533 := bbase (se 5 (by rfl) ⟨92087, by rfl⟩ : syracuseStep 1964533 = 184175) (by norm_num)
theorem B1964569 : Blo 1744573 1964569 := bbase (se 2 (by rfl) ⟨736713, by rfl⟩ : syracuseStep 1964569 = 1473427) (by norm_num)
theorem B1915429 : Blo 1744573 1915429 := bbase (se 4 (by rfl) ⟨179571, by rfl⟩ : syracuseStep 1915429 = 359143) (by norm_num)
theorem B1964605 : Blo 1744573 1964605 := bbase (se 3 (by rfl) ⟨368363, by rfl⟩ : syracuseStep 1964605 = 736727) (by norm_num)
theorem B1964641 : Blo 1744573 1964641 := bbase (se 2 (by rfl) ⟨736740, by rfl⟩ : syracuseStep 1964641 = 1473481) (by norm_num)
theorem B2210429 : Blo 1744573 2210429 := bbase (se 3 (by rfl) ⟨414455, by rfl⟩ : syracuseStep 2210429 = 828911) (by norm_num)
theorem B5888645 : Blo 1744573 5888645 := bbase (se 4 (by rfl) ⟨552060, by rfl⟩ : syracuseStep 5888645 = 1104121) (by norm_num)
theorem B1964677 : Blo 1744573 1964677 := bbase (se 4 (by rfl) ⟨184188, by rfl⟩ : syracuseStep 1964677 = 368377) (by norm_num)
theorem B6806165 : Blo 1744573 6806165 := bbase (se 6 (by rfl) ⟨159519, by rfl⟩ : syracuseStep 6806165 = 319039) (by norm_num)
theorem B10074773 : Blo 1744573 10074773 := bbase (se 6 (by rfl) ⟨236127, by rfl⟩ : syracuseStep 10074773 = 472255) (by norm_num)
theorem B30227093 : Blo 1744573 30227093 := bbase (se 6 (by rfl) ⟨708447, by rfl⟩ : syracuseStep 30227093 = 1416895) (by norm_num)
theorem B1964713 : Blo 1744573 1964713 := bbase (se 2 (by rfl) ⟨736767, by rfl⟩ : syracuseStep 1964713 = 1473535) (by norm_num)
theorem B2210485 : Blo 1744573 2210485 := bbase (se 5 (by rfl) ⟨103616, by rfl⟩ : syracuseStep 2210485 = 207233) (by norm_num)
theorem B1964749 : Blo 1744573 1964749 := bbase (se 3 (by rfl) ⟨368390, by rfl⟩ : syracuseStep 1964749 = 736781) (by norm_num)
theorem B29817557 : Blo 1744573 29817557 := bbase (se 7 (by rfl) ⟨349424, by rfl⟩ : syracuseStep 29817557 = 698849) (by norm_num)
theorem B1964785 : Blo 1744573 1964785 := bbase (se 2 (by rfl) ⟨736794, by rfl⟩ : syracuseStep 1964785 = 1473589) (by norm_num)
theorem B8837909 : Blo 1744573 8837909 := bbase (se 6 (by rfl) ⟨207138, by rfl⟩ : syracuseStep 8837909 = 414277) (by norm_num)
theorem B1964821 : Blo 1744573 1964821 := bbase (se 6 (by rfl) ⟨46050, by rfl⟩ : syracuseStep 1964821 = 92101) (by norm_num)
theorem B2095913 : Blo 1744573 2095913 := bbase (se 2 (by rfl) ⟨785967, by rfl⟩ : syracuseStep 2095913 = 1571935) (by norm_num)
theorem B1964857 : Blo 1744573 1964857 := bbase (se 2 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 1964857 = 1473643) (by norm_num)
theorem B22362965 : Blo 1744573 22362965 := bbase (se 9 (by rfl) ⟨65516, by rfl⟩ : syracuseStep 22362965 = 131033) (by norm_num)
theorem B1964893 : Blo 1744573 1964893 := bbase (se 3 (by rfl) ⟨368417, by rfl⟩ : syracuseStep 1964893 = 736835) (by norm_num)
theorem B6626245 : Blo 1744573 6626245 := bbase (se 4 (by rfl) ⟨621210, by rfl⟩ : syracuseStep 6626245 = 1242421) (by norm_num)
theorem B7076821 : Blo 1744573 7076821 := bbase (se 7 (by rfl) ⟨82931, by rfl⟩ : syracuseStep 7076821 = 165863) (by norm_num)
theorem B2653165 : Blo 1744573 2653165 := bbase (se 3 (by rfl) ⟨497468, by rfl⟩ : syracuseStep 2653165 = 994937) (by norm_num)
theorem B1989617 : Blo 1744573 1989617 := bbase (se 2 (by rfl) ⟨746106, by rfl⟩ : syracuseStep 1989617 = 1492213) (by norm_num)
theorem B18152437 : Blo 1744573 18152437 := bbase (se 5 (by rfl) ⟨850895, by rfl⟩ : syracuseStep 18152437 = 1701791) (by norm_num)
theorem B3726341 : Blo 1744573 3726341 := bbase (se 4 (by rfl) ⟨349344, by rfl⟩ : syracuseStep 3726341 = 698689) (by norm_num)
theorem B5889077 : Blo 1744573 5889077 := bbase (se 5 (by rfl) ⟨276050, by rfl⟩ : syracuseStep 5889077 = 552101) (by norm_num)
theorem B1768537 : Blo 1744573 1768537 := bbase (se 2 (by rfl) ⟨663201, by rfl⟩ : syracuseStep 1768537 = 1326403) (by norm_num)
theorem B2096221 : Blo 1744573 2096221 := bbase (se 3 (by rfl) ⟨393041, by rfl⟩ : syracuseStep 2096221 = 786083) (by norm_num)
theorem B3726461 : Blo 1744573 3726461 := bbase (se 3 (by rfl) ⟨698711, by rfl⟩ : syracuseStep 3726461 = 1397423) (by norm_num)
theorem B16776341 : Blo 1744573 16776341 := bbase (se 6 (by rfl) ⟨393195, by rfl⟩ : syracuseStep 16776341 = 786391) (by norm_num)
theorem B2096317 : Blo 1744573 2096317 := bbase (se 3 (by rfl) ⟨393059, by rfl⟩ : syracuseStep 2096317 = 786119) (by norm_num)
theorem B2096365 : Blo 1744573 2096365 := bbase (se 3 (by rfl) ⟨393068, by rfl⟩ : syracuseStep 2096365 = 786137) (by norm_num)
theorem B6626549 : Blo 1744573 6626549 := bbase (se 5 (by rfl) ⟨310619, by rfl⟩ : syracuseStep 6626549 = 621239) (by norm_num)
theorem B1989937 : Blo 1744573 1989937 := bbase (se 2 (by rfl) ⟨746226, by rfl⟩ : syracuseStep 1989937 = 1492453) (by norm_num)
theorem B4193653 : Blo 1744573 4193653 := bbase (se 5 (by rfl) ⟨196577, by rfl⟩ : syracuseStep 4193653 = 393155) (by norm_num)
theorem B3980677 : Blo 1744573 3980677 := bbase (se 4 (by rfl) ⟨373188, by rfl⟩ : syracuseStep 3980677 = 746377) (by norm_num)
theorem B5889509 : Blo 1744573 5889509 := bbase (se 4 (by rfl) ⟨552141, by rfl⟩ : syracuseStep 5889509 = 1104283) (by norm_num)
theorem B2358757 : Blo 1744573 2358757 := bbase (se 4 (by rfl) ⟨221133, by rfl⟩ : syracuseStep 2358757 = 442267) (by norm_num)
theorem B3538541 : Blo 1744573 3538541 := bbase (se 3 (by rfl) ⟨663476, by rfl⟩ : syracuseStep 3538541 = 1326953) (by norm_num)
theorem B5594741 : Blo 1744573 5594741 := bbase (se 5 (by rfl) ⟨262253, by rfl⟩ : syracuseStep 5594741 = 524507) (by norm_num)
theorem B13262453 : Blo 1744573 13262453 := bbase (se 5 (by rfl) ⟨621677, by rfl⟩ : syracuseStep 13262453 = 1243355) (by norm_num)
theorem B1990265 : Blo 1744573 1990265 := bbase (se 2 (by rfl) ⟨746349, by rfl⟩ : syracuseStep 1990265 = 1492699) (by norm_num)
theorem B1990301 : Blo 1744573 1990301 := bbase (se 3 (by rfl) ⟨373181, by rfl⟩ : syracuseStep 1990301 = 746363) (by norm_num)
theorem B3727093 : Blo 1744573 3727093 := bbase (se 5 (by rfl) ⟨174707, by rfl⟩ : syracuseStep 3727093 = 349415) (by norm_num)
theorem B2391805 : Blo 1744573 2391805 := bbase (se 3 (by rfl) ⟨448463, by rfl⟩ : syracuseStep 2391805 = 896927) (by norm_num)
theorem B4718357 : Blo 1744573 4718357 := bbase (se 6 (by rfl) ⟨110586, by rfl⟩ : syracuseStep 4718357 = 221173) (by norm_num)
theorem B4972373 : Blo 1744573 4972373 := bbase (se 9 (by rfl) ⟨14567, by rfl⟩ : syracuseStep 4972373 = 29135) (by norm_num)
theorem B5889941 : Blo 1744573 5889941 := bbase (se 6 (by rfl) ⟨138045, by rfl⟩ : syracuseStep 5889941 = 276091) (by norm_num)
theorem B3186677 : Blo 1744573 3186677 := bbase (se 5 (by rfl) ⟨149375, by rfl⟩ : syracuseStep 3186677 = 298751) (by norm_num)
theorem B2654197 : Blo 1744573 2654197 := bbase (se 5 (by rfl) ⟨124415, by rfl⟩ : syracuseStep 2654197 = 248831) (by norm_num)
theorem B1744899 : Blo 1744573 1744899 := bstep (se 1 (by rfl) ⟨1308674, by rfl⟩ : syracuseStep 1744899 = 2617349) B2617349
theorem B1744915 : Blo 1744573 1744915 := bstep (se 1 (by rfl) ⟨1308686, by rfl⟩ : syracuseStep 1744915 = 2617373) B2617373
theorem B1744931 : Blo 1744573 1744931 := bstep (se 1 (by rfl) ⟨1308698, by rfl⟩ : syracuseStep 1744931 = 2617397) B2617397
theorem B7077923 : Blo 1744573 7077923 := bstep (se 1 (by rfl) ⟨5308442, by rfl⟩ : syracuseStep 7077923 = 10616885) B10616885
theorem B1744947 : Blo 1744573 1744947 := bstep (se 1 (by rfl) ⟨1308710, by rfl⟩ : syracuseStep 1744947 = 2617421) B2617421
theorem B1744963 : Blo 1744573 1744963 := bstep (se 1 (by rfl) ⟨1308722, by rfl⟩ : syracuseStep 1744963 = 2617445) B2617445
theorem B1744979 : Blo 1744573 1744979 := bstep (se 1 (by rfl) ⟨1308734, by rfl⟩ : syracuseStep 1744979 = 2617469) B2617469
theorem B1744995 : Blo 1744573 1744995 := bstep (se 1 (by rfl) ⟨1308746, by rfl⟩ : syracuseStep 1744995 = 2617493) B2617493
theorem B5890157 : Blo 1744573 5890157 := bstep (se 3 (by rfl) ⟨1104404, by rfl⟩ : syracuseStep 5890157 = 2208809) B2208809
theorem B1745011 : Blo 1744573 1745011 := bstep (se 1 (by rfl) ⟨1308758, by rfl⟩ : syracuseStep 1745011 = 2617517) B2617517
theorem B1745027 : Blo 1744573 1745027 := bstep (se 1 (by rfl) ⟨1308770, by rfl⟩ : syracuseStep 1745027 = 2617541) B2617541
theorem B1745043 : Blo 1744573 1745043 := bstep (se 1 (by rfl) ⟨1308782, by rfl⟩ : syracuseStep 1745043 = 2617565) B2617565
theorem B1745059 : Blo 1744573 1745059 := bstep (se 1 (by rfl) ⟨1308794, by rfl⟩ : syracuseStep 1745059 = 2617589) B2617589
theorem B5890211 : Blo 1744573 5890211 := bstep (se 1 (by rfl) ⟨4417658, by rfl⟩ : syracuseStep 5890211 = 8835317) B8835317
theorem B6627491 : Blo 1744573 6627491 := bstep (se 1 (by rfl) ⟨4970618, by rfl⟩ : syracuseStep 6627491 = 9941237) B9941237
theorem B8388785 : Blo 1744573 8388785 := bstep (se 2 (by rfl) ⟨3145794, by rfl⟩ : syracuseStep 8388785 = 6291589) B6291589
theorem B1745075 : Blo 1744573 1745075 := bstep (se 1 (by rfl) ⟨1308806, by rfl⟩ : syracuseStep 1745075 = 2617613) B2617613
theorem B1745091 : Blo 1744573 1745091 := bstep (se 1 (by rfl) ⟨1308818, by rfl⟩ : syracuseStep 1745091 = 2617637) B2617637
theorem B4194499 : Blo 1744573 4194499 := bstep (se 1 (by rfl) ⟨3145874, by rfl⟩ : syracuseStep 4194499 = 6291749) B6291749
theorem B1745107 : Blo 1744573 1745107 := bstep (se 1 (by rfl) ⟨1308830, by rfl⟩ : syracuseStep 1745107 = 2617661) B2617661
theorem B1745123 : Blo 1744573 1745123 := bstep (se 1 (by rfl) ⟨1308842, by rfl⟩ : syracuseStep 1745123 = 2617685) B2617685
theorem B1745139 : Blo 1744573 1745139 := bstep (se 1 (by rfl) ⟨1308854, by rfl⟩ : syracuseStep 1745139 = 2617709) B2617709
theorem B1745155 : Blo 1744573 1745155 := bstep (se 1 (by rfl) ⟨1308866, by rfl⟩ : syracuseStep 1745155 = 2617733) B2617733
theorem B1745171 : Blo 1744573 1745171 := bstep (se 1 (by rfl) ⟨1308878, by rfl⟩ : syracuseStep 1745171 = 2617757) B2617757
theorem B1745187 : Blo 1744573 1745187 := bstep (se 1 (by rfl) ⟨1308890, by rfl⟩ : syracuseStep 1745187 = 2617781) B2617781
theorem B3146033 : Blo 1744573 3146033 := bstep (se 2 (by rfl) ⟨1179762, by rfl⟩ : syracuseStep 3146033 = 2359525) B2359525
theorem B2654513 : Blo 1744573 2654513 := bstep (se 2 (by rfl) ⟨995442, by rfl⟩ : syracuseStep 2654513 = 1990885) B1990885
theorem B1745203 : Blo 1744573 1745203 := bstep (se 1 (by rfl) ⟨1308902, by rfl⟩ : syracuseStep 1745203 = 2617805) B2617805
theorem B1745219 : Blo 1744573 1745219 := bstep (se 1 (by rfl) ⟨1308914, by rfl⟩ : syracuseStep 1745219 = 2617829) B2617829
theorem B2359633 : Blo 1744573 2359633 := bstep (se 2 (by rfl) ⟨884862, by rfl⟩ : syracuseStep 2359633 = 1769725) B1769725
theorem B1745235 : Blo 1744573 1745235 := bstep (se 1 (by rfl) ⟨1308926, by rfl⟩ : syracuseStep 1745235 = 2617853) B2617853
theorem B1745251 : Blo 1744573 1745251 := bstep (se 1 (by rfl) ⟨1308938, by rfl⟩ : syracuseStep 1745251 = 2617877) B2617877
theorem B8954225 : Blo 1744573 8954225 := bstep (se 2 (by rfl) ⟨3357834, by rfl⟩ : syracuseStep 8954225 = 6715669) B6715669
theorem B8962417 : Blo 1744573 8962417 := bstep (se 2 (by rfl) ⟨3360906, by rfl⟩ : syracuseStep 8962417 = 6721813) B6721813
theorem B1745267 : Blo 1744573 1745267 := bstep (se 1 (by rfl) ⟨1308950, by rfl⟩ : syracuseStep 1745267 = 2617901) B2617901
theorem B1745283 : Blo 1744573 1745283 := bstep (se 1 (by rfl) ⟨1308962, by rfl⟩ : syracuseStep 1745283 = 2617925) B2617925
theorem B2359697 : Blo 1744573 2359697 := bstep (se 2 (by rfl) ⟨884886, by rfl⟩ : syracuseStep 2359697 = 1769773) B1769773
theorem B1745299 : Blo 1744573 1745299 := bstep (se 1 (by rfl) ⟨1308974, by rfl⟩ : syracuseStep 1745299 = 2617949) B2617949
theorem B1745315 : Blo 1744573 1745315 := bstep (se 1 (by rfl) ⟨1308986, by rfl⟩ : syracuseStep 1745315 = 2617973) B2617973
theorem B5890481 : Blo 1744573 5890481 := bstep (se 2 (by rfl) ⟨2208930, by rfl⟩ : syracuseStep 5890481 = 4417861) B4417861
theorem B1745331 : Blo 1744573 1745331 := bstep (se 1 (by rfl) ⟨1308998, by rfl⟩ : syracuseStep 1745331 = 2617997) B2617997
theorem B1745347 : Blo 1744573 1745347 := bstep (se 1 (by rfl) ⟨1309010, by rfl⟩ : syracuseStep 1745347 = 2618021) B2618021
theorem B1745363 : Blo 1744573 1745363 := bstep (se 1 (by rfl) ⟨1309022, by rfl⟩ : syracuseStep 1745363 = 2618045) B2618045
theorem B1745379 : Blo 1744573 1745379 := bstep (se 1 (by rfl) ⟨1309034, by rfl⟩ : syracuseStep 1745379 = 2618069) B2618069
theorem B1745395 : Blo 1744573 1745395 := bstep (se 1 (by rfl) ⟨1309046, by rfl⟩ : syracuseStep 1745395 = 2618093) B2618093
theorem B2359795 : Blo 1744573 2359795 := bstep (se 1 (by rfl) ⟨1769846, by rfl⟩ : syracuseStep 2359795 = 3539693) B3539693
theorem B1745411 : Blo 1744573 1745411 := bstep (se 1 (by rfl) ⟨1309058, by rfl⟩ : syracuseStep 1745411 = 2618117) B2618117
theorem B1745427 : Blo 1744573 1745427 := bstep (se 1 (by rfl) ⟨1309070, by rfl⟩ : syracuseStep 1745427 = 2618141) B2618141
theorem B1745443 : Blo 1744573 1745443 := bstep (se 1 (by rfl) ⟨1309082, by rfl⟩ : syracuseStep 1745443 = 2618165) B2618165
theorem B1745459 : Blo 1744573 1745459 := bstep (se 1 (by rfl) ⟨1309094, by rfl⟩ : syracuseStep 1745459 = 2618189) B2618189
theorem B30245429 : Blo 1744573 30245429 := bstep (se 5 (by rfl) ⟨1417754, by rfl⟩ : syracuseStep 30245429 = 2835509) B2835509
theorem B1745475 : Blo 1744573 1745475 := bstep (se 1 (by rfl) ⟨1309106, by rfl⟩ : syracuseStep 1745475 = 2618213) B2618213
theorem B3727939 : Blo 1744573 3727939 := bstep (se 1 (by rfl) ⟨2795954, by rfl⟩ : syracuseStep 3727939 = 5591909) B5591909
theorem B1745491 : Blo 1744573 1745491 := bstep (se 1 (by rfl) ⟨1309118, by rfl⟩ : syracuseStep 1745491 = 2618237) B2618237
theorem B1745507 : Blo 1744573 1745507 := bstep (se 1 (by rfl) ⟨1309130, by rfl⟩ : syracuseStep 1745507 = 2618261) B2618261
theorem B1745523 : Blo 1744573 1745523 := bstep (se 1 (by rfl) ⟨1309142, by rfl⟩ : syracuseStep 1745523 = 2618285) B2618285
theorem B1745539 : Blo 1744573 1745539 := bstep (se 1 (by rfl) ⟨1309154, by rfl⟩ : syracuseStep 1745539 = 2618309) B2618309
theorem B1745555 : Blo 1744573 1745555 := bstep (se 1 (by rfl) ⟨1309166, by rfl⟩ : syracuseStep 1745555 = 2618333) B2618333
theorem B1745571 : Blo 1744573 1745571 := bstep (se 1 (by rfl) ⟨1309178, by rfl⟩ : syracuseStep 1745571 = 2618357) B2618357
theorem B1745587 : Blo 1744573 1745587 := bstep (se 1 (by rfl) ⟨1309190, by rfl⟩ : syracuseStep 1745587 = 2618381) B2618381
theorem B1745603 : Blo 1744573 1745603 := bstep (se 1 (by rfl) ⟨1309202, by rfl⟩ : syracuseStep 1745603 = 2618405) B2618405
theorem B1745619 : Blo 1744573 1745619 := bstep (se 1 (by rfl) ⟨1309214, by rfl⟩ : syracuseStep 1745619 = 2618429) B2618429
theorem B1745635 : Blo 1744573 1745635 := bstep (se 1 (by rfl) ⟨1309226, by rfl⟩ : syracuseStep 1745635 = 2618453) B2618453
theorem B4416241 : Blo 1744573 4416241 := bstep (se 2 (by rfl) ⟨1656090, by rfl⟩ : syracuseStep 4416241 = 3312181) B3312181
theorem B1745651 : Blo 1744573 1745651 := bstep (se 1 (by rfl) ⟨1309238, by rfl⟩ : syracuseStep 1745651 = 2618477) B2618477
theorem B1745667 : Blo 1744573 1745667 := bstep (se 1 (by rfl) ⟨1309250, by rfl⟩ : syracuseStep 1745667 = 2618501) B2618501
theorem B11944709 : Blo 1744573 11944709 := bstep (se 4 (by rfl) ⟨1119816, by rfl⟩ : syracuseStep 11944709 = 2239633) B2239633
theorem B4973329 : Blo 1744573 4973329 := bstep (se 2 (by rfl) ⟨1864998, by rfl⟩ : syracuseStep 4973329 = 3729997) B3729997
theorem B1745683 : Blo 1744573 1745683 := bstep (se 1 (by rfl) ⟨1309262, by rfl⟩ : syracuseStep 1745683 = 2618525) B2618525
theorem B40862485 : Blo 1744573 40862485 := bstep (se 6 (by rfl) ⟨957714, by rfl⟩ : syracuseStep 40862485 = 1915429) B1915429
theorem B1745699 : Blo 1744573 1745699 := bstep (se 1 (by rfl) ⟨1309274, by rfl⟩ : syracuseStep 1745699 = 2618549) B2618549
theorem B1745715 : Blo 1744573 1745715 := bstep (se 1 (by rfl) ⟨1309286, by rfl⟩ : syracuseStep 1745715 = 2618573) B2618573
theorem B1745731 : Blo 1744573 1745731 := bstep (se 1 (by rfl) ⟨1309298, by rfl⟩ : syracuseStep 1745731 = 2618597) B2618597
theorem B1745747 : Blo 1744573 1745747 := bstep (se 1 (by rfl) ⟨1309310, by rfl⟩ : syracuseStep 1745747 = 2618621) B2618621
theorem B1745763 : Blo 1744573 1745763 := bstep (se 1 (by rfl) ⟨1309322, by rfl⟩ : syracuseStep 1745763 = 2618645) B2618645
theorem B1745779 : Blo 1744573 1745779 := bstep (se 1 (by rfl) ⟨1309334, by rfl⟩ : syracuseStep 1745779 = 2618669) B2618669
theorem B1745795 : Blo 1744573 1745795 := bstep (se 1 (by rfl) ⟨1309346, by rfl⟩ : syracuseStep 1745795 = 2618693) B2618693
theorem B4719505 : Blo 1744573 4719505 := bstep (se 2 (by rfl) ⟨1769814, by rfl⟩ : syracuseStep 4719505 = 3539629) B3539629
theorem B1745811 : Blo 1744573 1745811 := bstep (se 1 (by rfl) ⟨1309358, by rfl⟩ : syracuseStep 1745811 = 2618717) B2618717
theorem B1745827 : Blo 1744573 1745827 := bstep (se 1 (by rfl) ⟨1309370, by rfl⟩ : syracuseStep 1745827 = 2618741) B2618741
theorem B1745843 : Blo 1744573 1745843 := bstep (se 1 (by rfl) ⟨1309382, by rfl⟩ : syracuseStep 1745843 = 2618765) B2618765
theorem B1745859 : Blo 1744573 1745859 := bstep (se 1 (by rfl) ⟨1309394, by rfl⟩ : syracuseStep 1745859 = 2618789) B2618789
theorem B5891021 : Blo 1744573 5891021 := bstep (se 3 (by rfl) ⟨1104566, by rfl⟩ : syracuseStep 5891021 = 2209133) B2209133
theorem B1745875 : Blo 1744573 1745875 := bstep (se 1 (by rfl) ⟨1309406, by rfl⟩ : syracuseStep 1745875 = 2618813) B2618813
theorem B1745891 : Blo 1744573 1745891 := bstep (se 1 (by rfl) ⟨1309418, by rfl⟩ : syracuseStep 1745891 = 2618837) B2618837
theorem B8840177 : Blo 1744573 8840177 := bstep (se 2 (by rfl) ⟨3315066, by rfl⟩ : syracuseStep 8840177 = 6630133) B6630133
theorem B1745907 : Blo 1744573 1745907 := bstep (se 1 (by rfl) ⟨1309430, by rfl⟩ : syracuseStep 1745907 = 2618861) B2618861
theorem B4416515 : Blo 1744573 4416515 := bstep (se 1 (by rfl) ⟨3312386, by rfl⟩ : syracuseStep 4416515 = 6624773) B6624773
theorem B5891075 : Blo 1744573 5891075 := bstep (se 1 (by rfl) ⟨4418306, by rfl⟩ : syracuseStep 5891075 = 8836613) B8836613
theorem B1745923 : Blo 1744573 1745923 := bstep (se 1 (by rfl) ⟨1309442, by rfl⟩ : syracuseStep 1745923 = 2618885) B2618885
theorem B1745939 : Blo 1744573 1745939 := bstep (se 1 (by rfl) ⟨1309454, by rfl⟩ : syracuseStep 1745939 = 2618909) B2618909
theorem B1745955 : Blo 1744573 1745955 := bstep (se 1 (by rfl) ⟨1309466, by rfl⟩ : syracuseStep 1745955 = 2618933) B2618933
theorem B7078961 : Blo 1744573 7078961 := bstep (se 2 (by rfl) ⟨2654610, by rfl⟩ : syracuseStep 7078961 = 5309221) B5309221
theorem B1745971 : Blo 1744573 1745971 := bstep (se 1 (by rfl) ⟨1309478, by rfl⟩ : syracuseStep 1745971 = 2618957) B2618957
theorem B1745987 : Blo 1744573 1745987 := bstep (se 1 (by rfl) ⟨1309490, by rfl⟩ : syracuseStep 1745987 = 2618981) B2618981
theorem B8832077 : Blo 1744573 8832077 := bstep (se 3 (by rfl) ⟨1656014, by rfl⟩ : syracuseStep 8832077 = 3312029) B3312029
theorem B1746003 : Blo 1744573 1746003 := bstep (se 1 (by rfl) ⟨1309502, by rfl⟩ : syracuseStep 1746003 = 2619005) B2619005
theorem B1746019 : Blo 1744573 1746019 := bstep (se 1 (by rfl) ⟨1309514, by rfl⟩ : syracuseStep 1746019 = 2619029) B2619029
theorem B7554161 : Blo 1744573 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B1746035 : Blo 1744573 1746035 := bstep (se 1 (by rfl) ⟨1309526, by rfl⟩ : syracuseStep 1746035 = 2619053) B2619053
theorem B1746051 : Blo 1744573 1746051 := bstep (se 1 (by rfl) ⟨1309538, by rfl⟩ : syracuseStep 1746051 = 2619077) B2619077
theorem B6628493 : Blo 1744573 6628493 := bstep (se 3 (by rfl) ⟨1242842, by rfl⟩ : syracuseStep 6628493 = 2485685) B2485685
theorem B3146897 : Blo 1744573 3146897 := bstep (se 2 (by rfl) ⟨1180086, by rfl⟩ : syracuseStep 3146897 = 2360173) B2360173
theorem B1746067 : Blo 1744573 1746067 := bstep (se 1 (by rfl) ⟨1309550, by rfl⟩ : syracuseStep 1746067 = 2619101) B2619101
theorem B1746083 : Blo 1744573 1746083 := bstep (se 1 (by rfl) ⟨1309562, by rfl⟩ : syracuseStep 1746083 = 2619125) B2619125
theorem B1746099 : Blo 1744573 1746099 := bstep (se 1 (by rfl) ⟨1309574, by rfl⟩ : syracuseStep 1746099 = 2619149) B2619149
theorem B4416707 : Blo 1744573 4416707 := bstep (se 1 (by rfl) ⟨3312530, by rfl⟩ : syracuseStep 4416707 = 6625061) B6625061
theorem B1746115 : Blo 1744573 1746115 := bstep (se 1 (by rfl) ⟨1309586, by rfl⟩ : syracuseStep 1746115 = 2619173) B2619173
theorem B1746131 : Blo 1744573 1746131 := bstep (se 1 (by rfl) ⟨1309598, by rfl⟩ : syracuseStep 1746131 = 2619197) B2619197
theorem B1746147 : Blo 1744573 1746147 := bstep (se 1 (by rfl) ⟨1309610, by rfl⟩ : syracuseStep 1746147 = 2619221) B2619221
theorem B1746163 : Blo 1744573 1746163 := bstep (se 1 (by rfl) ⟨1309622, by rfl⟩ : syracuseStep 1746163 = 2619245) B2619245
theorem B1746179 : Blo 1744573 1746179 := bstep (se 1 (by rfl) ⟨1309634, by rfl⟩ : syracuseStep 1746179 = 2619269) B2619269
theorem B5891345 : Blo 1744573 5891345 := bstep (se 2 (by rfl) ⟨2209254, by rfl⟩ : syracuseStep 5891345 = 4418509) B4418509
theorem B1746195 : Blo 1744573 1746195 := bstep (se 1 (by rfl) ⟨1309646, by rfl⟩ : syracuseStep 1746195 = 2619293) B2619293
theorem B1746211 : Blo 1744573 1746211 := bstep (se 1 (by rfl) ⟨1309658, by rfl⟩ : syracuseStep 1746211 = 2619317) B2619317
theorem B1746227 : Blo 1744573 1746227 := bstep (se 1 (by rfl) ⟨1309670, by rfl⟩ : syracuseStep 1746227 = 2619341) B2619341
theorem B1746243 : Blo 1744573 1746243 := bstep (se 1 (by rfl) ⟨1309682, by rfl⟩ : syracuseStep 1746243 = 2619365) B2619365
theorem B1746259 : Blo 1744573 1746259 := bstep (se 1 (by rfl) ⟨1309694, by rfl⟩ : syracuseStep 1746259 = 2619389) B2619389
theorem B1746275 : Blo 1744573 1746275 := bstep (se 1 (by rfl) ⟨1309706, by rfl⟩ : syracuseStep 1746275 = 2619413) B2619413
theorem B1746291 : Blo 1744573 1746291 := bstep (se 1 (by rfl) ⟨1309718, by rfl⟩ : syracuseStep 1746291 = 2619437) B2619437
theorem B1746307 : Blo 1744573 1746307 := bstep (se 1 (by rfl) ⟨1309730, by rfl⟩ : syracuseStep 1746307 = 2619461) B2619461
theorem B4195729 : Blo 1744573 4195729 := bstep (se 2 (by rfl) ⟨1573398, by rfl⟩ : syracuseStep 4195729 = 3146797) B3146797
theorem B1746323 : Blo 1744573 1746323 := bstep (se 1 (by rfl) ⟨1309742, by rfl⟩ : syracuseStep 1746323 = 2619485) B2619485
theorem B1746339 : Blo 1744573 1746339 := bstep (se 1 (by rfl) ⟨1309754, by rfl⟩ : syracuseStep 1746339 = 2619509) B2619509
theorem B1746355 : Blo 1744573 1746355 := bstep (se 1 (by rfl) ⟨1309766, by rfl⟩ : syracuseStep 1746355 = 2619533) B2619533
theorem B1746371 : Blo 1744573 1746371 := bstep (se 1 (by rfl) ⟨1309778, by rfl⟩ : syracuseStep 1746371 = 2619557) B2619557
theorem B3925457 : Blo 1744573 3925457 := bstep (se 2 (by rfl) ⟨1472046, by rfl⟩ : syracuseStep 3925457 = 2944093) B2944093
theorem B2794961 : Blo 1744573 2794961 := bstep (se 2 (by rfl) ⟨1048110, by rfl⟩ : syracuseStep 2794961 = 2096221) B2096221
theorem B1746387 : Blo 1744573 1746387 := bstep (se 1 (by rfl) ⟨1309790, by rfl⟩ : syracuseStep 1746387 = 2619581) B2619581
theorem B3925475 : Blo 1744573 3925475 := bstep (se 1 (by rfl) ⟨2944106, by rfl⟩ : syracuseStep 3925475 = 5888213) B5888213
theorem B33564131 : Blo 1744573 33564131 := bstep (se 1 (by rfl) ⟨25173098, by rfl⟩ : syracuseStep 33564131 = 50346197) B50346197
theorem B1746403 : Blo 1744573 1746403 := bstep (se 1 (by rfl) ⟨1309802, by rfl⟩ : syracuseStep 1746403 = 2619605) B2619605
theorem B1746419 : Blo 1744573 1746419 := bstep (se 1 (by rfl) ⟨1309814, by rfl⟩ : syracuseStep 1746419 = 2619629) B2619629
theorem B1746435 : Blo 1744573 1746435 := bstep (se 1 (by rfl) ⟨1309826, by rfl⟩ : syracuseStep 1746435 = 2619653) B2619653
theorem B9946637 : Blo 1744573 9946637 := bstep (se 3 (by rfl) ⟨1864994, by rfl⟩ : syracuseStep 9946637 = 3729989) B3729989
theorem B1746451 : Blo 1744573 1746451 := bstep (se 1 (by rfl) ⟨1309838, by rfl⟩ : syracuseStep 1746451 = 2619677) B2619677
theorem B1746467 : Blo 1744573 1746467 := bstep (se 1 (by rfl) ⟨1309850, by rfl⟩ : syracuseStep 1746467 = 2619701) B2619701
theorem B1746483 : Blo 1744573 1746483 := bstep (se 1 (by rfl) ⟨1309862, by rfl⟩ : syracuseStep 1746483 = 2619725) B2619725
theorem B37725749 : Blo 1744573 37725749 := bstep (se 5 (by rfl) ⟨1768394, by rfl⟩ : syracuseStep 37725749 = 3536789) B3536789
theorem B1746499 : Blo 1744573 1746499 := bstep (se 1 (by rfl) ⟨1309874, by rfl⟩ : syracuseStep 1746499 = 2619749) B2619749
theorem B2795089 : Blo 1744573 2795089 := bstep (se 2 (by rfl) ⟨1048158, by rfl⟩ : syracuseStep 2795089 = 2096317) B2096317
theorem B1746515 : Blo 1744573 1746515 := bstep (se 1 (by rfl) ⟨1309886, by rfl⟩ : syracuseStep 1746515 = 2619773) B2619773
theorem B1746531 : Blo 1744573 1746531 := bstep (se 1 (by rfl) ⟨1309898, by rfl⟩ : syracuseStep 1746531 = 2619797) B2619797
theorem B1746547 : Blo 1744573 1746547 := bstep (se 1 (by rfl) ⟨1309910, by rfl⟩ : syracuseStep 1746547 = 2619821) B2619821
theorem B1746563 : Blo 1744573 1746563 := bstep (se 1 (by rfl) ⟨1309922, by rfl⟩ : syracuseStep 1746563 = 2619845) B2619845
theorem B2795153 : Blo 1744573 2795153 := bstep (se 2 (by rfl) ⟨1048182, by rfl⟩ : syracuseStep 2795153 = 2096365) B2096365
theorem B3925745 : Blo 1744573 3925745 := bstep (se 2 (by rfl) ⟨1472154, by rfl⟩ : syracuseStep 3925745 = 2944309) B2944309
theorem B3925763 : Blo 1744573 3925763 := bstep (se 1 (by rfl) ⟨2944322, by rfl⟩ : syracuseStep 3925763 = 5888645) B5888645
theorem B3729169 : Blo 1744573 3729169 := bstep (se 2 (by rfl) ⟨1398438, by rfl⟩ : syracuseStep 3729169 = 2796877) B2796877
theorem B5891885 : Blo 1744573 5891885 := bstep (se 3 (by rfl) ⟨1104728, by rfl⟩ : syracuseStep 5891885 = 2209457) B2209457
theorem B5891939 : Blo 1744573 5891939 := bstep (se 1 (by rfl) ⟨4418954, by rfl⟩ : syracuseStep 5891939 = 8837909) B8837909
theorem B9938821 : Blo 1744573 9938821 := bstep (se 4 (by rfl) ⟨931764, by rfl⟩ : syracuseStep 9938821 = 1863529) B1863529
theorem B2484113 : Blo 1744573 2484113 := bstep (se 2 (by rfl) ⟨931542, by rfl⟩ : syracuseStep 2484113 = 1863085) B1863085
theorem B2484227 : Blo 1744573 2484227 := bstep (se 1 (by rfl) ⟨1863170, by rfl⟩ : syracuseStep 2484227 = 3726341) B3726341
theorem B3926033 : Blo 1744573 3926033 := bstep (se 2 (by rfl) ⟨1472262, by rfl⟩ : syracuseStep 3926033 = 2944525) B2944525
theorem B3926051 : Blo 1744573 3926051 := bstep (se 1 (by rfl) ⟨2944538, by rfl⟩ : syracuseStep 3926051 = 5889077) B5889077
theorem B2484307 : Blo 1744573 2484307 := bstep (se 1 (by rfl) ⟨1863230, by rfl⟩ : syracuseStep 2484307 = 3726461) B3726461
theorem B11184227 : Blo 1744573 11184227 := bstep (se 1 (by rfl) ⟨8388170, by rfl⟩ : syracuseStep 11184227 = 16776341) B16776341
theorem B5589101 : Blo 1744573 5589101 := bstep (se 3 (by rfl) ⟨1047956, by rfl⟩ : syracuseStep 5589101 = 2095913) B2095913
theorem B4417649 : Blo 1744573 4417649 := bstep (se 2 (by rfl) ⟨1656618, by rfl⟩ : syracuseStep 4417649 = 3313237) B3313237
theorem B5892209 : Blo 1744573 5892209 := bstep (se 2 (by rfl) ⟨2209578, by rfl⟩ : syracuseStep 5892209 = 4419157) B4419157
theorem B4417699 : Blo 1744573 4417699 := bstep (se 1 (by rfl) ⟨3313274, by rfl⟩ : syracuseStep 4417699 = 6626549) B6626549
theorem B3926321 : Blo 1744573 3926321 := bstep (se 2 (by rfl) ⟨1472370, by rfl⟩ : syracuseStep 3926321 = 2944741) B2944741
theorem B4417841 : Blo 1744573 4417841 := bstep (se 2 (by rfl) ⟨1656690, by rfl⟩ : syracuseStep 4417841 = 3313381) B3313381
theorem B5040433 : Blo 1744573 5040433 := bstep (se 2 (by rfl) ⟨1890162, by rfl⟩ : syracuseStep 5040433 = 3780325) B3780325
theorem B3926339 : Blo 1744573 3926339 := bstep (se 1 (by rfl) ⟨2944754, by rfl⟩ : syracuseStep 3926339 = 5889509) B5889509
theorem B3189073 : Blo 1744573 3189073 := bstep (se 2 (by rfl) ⟨1195902, by rfl⟩ : syracuseStep 3189073 = 2391805) B2391805
theorem B7457123 : Blo 1744573 7457123 := bstep (se 1 (by rfl) ⟨5592842, by rfl⟩ : syracuseStep 7457123 = 11185685) B11185685
theorem B2689393 : Blo 1744573 2689393 := bstep (se 2 (by rfl) ⟨1008522, by rfl⟩ : syracuseStep 2689393 = 2017045) B2017045
theorem B3729827 : Blo 1744573 3729827 := bstep (se 1 (by rfl) ⟨2797370, by rfl⟩ : syracuseStep 3729827 = 5594741) B5594741
theorem B8841635 : Blo 1744573 8841635 := bstep (se 1 (by rfl) ⟨6631226, by rfl⟩ : syracuseStep 8841635 = 13262453) B13262453
theorem B3926609 : Blo 1744573 3926609 := bstep (se 2 (by rfl) ⟨1472478, by rfl⟩ : syracuseStep 3926609 = 2944957) B2944957
theorem B3312227 : Blo 1744573 3312227 := bstep (se 1 (by rfl) ⟨2484170, by rfl⟩ : syracuseStep 3312227 = 4968341) B4968341
theorem B3926627 : Blo 1744573 3926627 := bstep (se 1 (by rfl) ⟨2944970, by rfl⟩ : syracuseStep 3926627 = 5889941) B5889941
theorem B2484865 : Blo 1744573 2484865 := bstep (se 2 (by rfl) ⟨931824, by rfl⟩ : syracuseStep 2484865 = 1863649) B1863649
theorem B5892749 : Blo 1744573 5892749 := bstep (se 3 (by rfl) ⟨1104890, by rfl⟩ : syracuseStep 5892749 = 2209781) B2209781
theorem B2124451 : Blo 1744573 2124451 := bstep (se 1 (by rfl) ⟨1593338, by rfl⟩ : syracuseStep 2124451 = 3186677) B3186677
theorem B2796211 : Blo 1744573 2796211 := bstep (se 1 (by rfl) ⟨2097158, by rfl⟩ : syracuseStep 2796211 = 4194317) B4194317
theorem B5892803 : Blo 1744573 5892803 := bstep (se 1 (by rfl) ⟨4419602, by rfl⟩ : syracuseStep 5892803 = 8839205) B8839205
theorem B3926897 : Blo 1744573 3926897 := bstep (se 2 (by rfl) ⟨1472586, by rfl⟩ : syracuseStep 3926897 = 2945173) B2945173
theorem B3312515 : Blo 1744573 3312515 := bstep (se 1 (by rfl) ⟨2484386, by rfl⟩ : syracuseStep 3312515 = 4968773) B4968773
theorem B3926915 : Blo 1744573 3926915 := bstep (se 1 (by rfl) ⟨2945186, by rfl⟩ : syracuseStep 3926915 = 5890373) B5890373
theorem B5893073 : Blo 1744573 5893073 := bstep (se 2 (by rfl) ⟨2209902, by rfl⟩ : syracuseStep 5893073 = 4419805) B4419805
theorem B2943985 : Blo 1744573 2943985 := bstep (se 2 (by rfl) ⟨1103994, by rfl⟩ : syracuseStep 2943985 = 2207989) B2207989
theorem B2944019 : Blo 1744573 2944019 := bstep (se 1 (by rfl) ⟨2208014, by rfl⟩ : syracuseStep 2944019 = 4416029) B4416029
theorem B10619981 : Blo 1744573 10619981 := bstep (se 3 (by rfl) ⟨1991246, by rfl⟩ : syracuseStep 10619981 = 3982493) B3982493
theorem B7081037 : Blo 1744573 7081037 := bstep (se 3 (by rfl) ⟨1327694, by rfl⟩ : syracuseStep 7081037 = 2655389) B2655389
theorem B14158961 : Blo 1744573 14158961 := bstep (se 2 (by rfl) ⟨5309610, by rfl⟩ : syracuseStep 14158961 = 10619221) B10619221
theorem B9432197 : Blo 1744573 9432197 := bstep (se 4 (by rfl) ⟨884268, by rfl⟩ : syracuseStep 9432197 = 1768537) B1768537
theorem B12102797 : Blo 1744573 12102797 := bstep (se 3 (by rfl) ⟨2269274, by rfl⟩ : syracuseStep 12102797 = 4538549) B4538549
theorem B3927185 : Blo 1744573 3927185 := bstep (se 2 (by rfl) ⟨1472694, by rfl⟩ : syracuseStep 3927185 = 2945389) B2945389
theorem B2944147 : Blo 1744573 2944147 := bstep (se 1 (by rfl) ⟨2208110, by rfl⟩ : syracuseStep 2944147 = 4416221) B4416221
theorem B3927203 : Blo 1744573 3927203 := bstep (se 1 (by rfl) ⟨2945402, by rfl⟩ : syracuseStep 3927203 = 5890805) B5890805
theorem B3452099 : Blo 1744573 3452099 := bstep (se 1 (by rfl) ⟨2589074, by rfl⟩ : syracuseStep 3452099 = 5178149) B5178149
theorem B6630605 : Blo 1744573 6630605 := bstep (se 3 (by rfl) ⟨1243238, by rfl⟩ : syracuseStep 6630605 = 2486477) B2486477
theorem B11644145 : Blo 1744573 11644145 := bstep (se 2 (by rfl) ⟨4366554, by rfl⟩ : syracuseStep 11644145 = 8733109) B8733109
theorem B2985233 : Blo 1744573 2985233 := bstep (se 2 (by rfl) ⟨1119462, by rfl⟩ : syracuseStep 2985233 = 2238925) B2238925
theorem B4418833 : Blo 1744573 4418833 := bstep (se 2 (by rfl) ⟨1657062, by rfl⟩ : syracuseStep 4418833 = 3314125) B3314125
theorem B2944289 : Blo 1744573 2944289 := bstep (se 2 (by rfl) ⟨1104108, by rfl⟩ : syracuseStep 2944289 = 2208217) B2208217
theorem B2485571 : Blo 1744573 2485571 := bstep (se 1 (by rfl) ⟨1864178, by rfl⟩ : syracuseStep 2485571 = 3728357) B3728357
theorem B3403139 : Blo 1744573 3403139 := bstep (se 1 (by rfl) ⟨2552354, by rfl⟩ : syracuseStep 3403139 = 5104709) B5104709
theorem B2944417 : Blo 1744573 2944417 := bstep (se 2 (by rfl) ⟨1104156, by rfl⟩ : syracuseStep 2944417 = 2208313) B2208313
theorem B3927473 : Blo 1744573 3927473 := bstep (se 2 (by rfl) ⟨1472802, by rfl⟩ : syracuseStep 3927473 = 2945605) B2945605
theorem B2944451 : Blo 1744573 2944451 := bstep (se 1 (by rfl) ⟨2208338, by rfl⟩ : syracuseStep 2944451 = 4416677) B4416677
theorem B3927491 : Blo 1744573 3927491 := bstep (se 1 (by rfl) ⟨2945618, by rfl⟩ : syracuseStep 3927491 = 5891237) B5891237
theorem B5893613 : Blo 1744573 5893613 := bstep (se 3 (by rfl) ⟨1105052, by rfl⟩ : syracuseStep 5893613 = 2210105) B2210105
theorem B4419107 : Blo 1744573 4419107 := bstep (se 1 (by rfl) ⟨3314330, by rfl⟩ : syracuseStep 4419107 = 6628661) B6628661
theorem B5893667 : Blo 1744573 5893667 := bstep (se 1 (by rfl) ⟨4420250, by rfl⟩ : syracuseStep 5893667 = 8840501) B8840501
theorem B2616881 : Blo 1744573 2616881 := bstep (se 2 (by rfl) ⟨981330, by rfl⟩ : syracuseStep 2616881 = 1962661) B1962661
theorem B2616899 : Blo 1744573 2616899 := bstep (se 1 (by rfl) ⟨1962674, by rfl⟩ : syracuseStep 2616899 = 3925349) B3925349
theorem B2944579 : Blo 1744573 2944579 := bstep (se 1 (by rfl) ⟨2208434, by rfl⟩ : syracuseStep 2944579 = 4416869) B4416869
theorem B2797139 : Blo 1744573 2797139 := bstep (se 1 (by rfl) ⟨2097854, by rfl⟩ : syracuseStep 2797139 = 4195709) B4195709
theorem B2616929 : Blo 1744573 2616929 := bstep (se 2 (by rfl) ⟨981348, by rfl⟩ : syracuseStep 2616929 = 1962697) B1962697
theorem B2616947 : Blo 1744573 2616947 := bstep (se 1 (by rfl) ⟨1962710, by rfl⟩ : syracuseStep 2616947 = 3925421) B3925421
theorem B4968067 : Blo 1744573 4968067 := bstep (se 1 (by rfl) ⟨3726050, by rfl⟩ : syracuseStep 4968067 = 7452101) B7452101
theorem B11062925 : Blo 1744573 11062925 := bstep (se 3 (by rfl) ⟨2074298, by rfl⟩ : syracuseStep 11062925 = 4148597) B4148597
theorem B2616977 : Blo 1744573 2616977 := bstep (se 2 (by rfl) ⟨981366, by rfl⟩ : syracuseStep 2616977 = 1962733) B1962733
theorem B2616995 : Blo 1744573 2616995 := bstep (se 1 (by rfl) ⟨1962746, by rfl⟩ : syracuseStep 2616995 = 3925493) B3925493
theorem B10612387 : Blo 1744573 10612387 := bstep (se 1 (by rfl) ⟨7959290, by rfl⟩ : syracuseStep 10612387 = 15918581) B15918581
theorem B5590691 : Blo 1744573 5590691 := bstep (se 1 (by rfl) ⟨4193018, by rfl⟩ : syracuseStep 5590691 = 8386037) B8386037
theorem B8179363 : Blo 1744573 8179363 := bstep (se 1 (by rfl) ⟨6134522, by rfl⟩ : syracuseStep 8179363 = 12269045) B12269045
theorem B2617025 : Blo 1744573 2617025 := bstep (se 2 (by rfl) ⟨981384, by rfl⟩ : syracuseStep 2617025 = 1962769) B1962769
theorem B2944721 : Blo 1744573 2944721 := bstep (se 2 (by rfl) ⟨1104270, by rfl⟩ : syracuseStep 2944721 = 2208541) B2208541
theorem B3927761 : Blo 1744573 3927761 := bstep (se 2 (by rfl) ⟨1472910, by rfl⟩ : syracuseStep 3927761 = 2945821) B2945821
theorem B2617043 : Blo 1744573 2617043 := bstep (se 1 (by rfl) ⟨1962782, by rfl⟩ : syracuseStep 2617043 = 3925565) B3925565
theorem B3927779 : Blo 1744573 3927779 := bstep (se 1 (by rfl) ⟨2945834, by rfl⟩ : syracuseStep 3927779 = 5891669) B5891669
theorem B4419299 : Blo 1744573 4419299 := bstep (se 1 (by rfl) ⟨3314474, by rfl⟩ : syracuseStep 4419299 = 6628949) B6628949
theorem B2617073 : Blo 1744573 2617073 := bstep (se 2 (by rfl) ⟨981402, by rfl⟩ : syracuseStep 2617073 = 1962805) B1962805
theorem B2617091 : Blo 1744573 2617091 := bstep (se 1 (by rfl) ⟨1962818, by rfl⟩ : syracuseStep 2617091 = 3925637) B3925637
theorem B2617121 : Blo 1744573 2617121 := bstep (se 2 (by rfl) ⟨981420, by rfl⟩ : syracuseStep 2617121 = 1962841) B1962841
theorem B3313457 : Blo 1744573 3313457 := bstep (se 2 (by rfl) ⟨1242546, by rfl⟩ : syracuseStep 3313457 = 2485093) B2485093
theorem B5893937 : Blo 1744573 5893937 := bstep (se 2 (by rfl) ⟨2210226, by rfl⟩ : syracuseStep 5893937 = 4420453) B4420453
theorem B2617139 : Blo 1744573 2617139 := bstep (se 1 (by rfl) ⟨1962854, by rfl⟩ : syracuseStep 2617139 = 3925709) B3925709
theorem B1863491 : Blo 1744573 1863491 := bstep (se 1 (by rfl) ⟨1397618, by rfl⟩ : syracuseStep 1863491 = 2795237) B2795237
theorem B9940805 : Blo 1744573 9940805 := bstep (se 4 (by rfl) ⟨931950, by rfl⟩ : syracuseStep 9940805 = 1863901) B1863901
theorem B13258565 : Blo 1744573 13258565 := bstep (se 4 (by rfl) ⟨1242990, by rfl⟩ : syracuseStep 13258565 = 2485981) B2485981
theorem B2617169 : Blo 1744573 2617169 := bstep (se 2 (by rfl) ⟨981438, by rfl⟩ : syracuseStep 2617169 = 1962877) B1962877
theorem B2944849 : Blo 1744573 2944849 := bstep (se 2 (by rfl) ⟨1104318, by rfl⟩ : syracuseStep 2944849 = 2208637) B2208637
theorem B2797409 : Blo 1744573 2797409 := bstep (se 2 (by rfl) ⟨1049028, by rfl⟩ : syracuseStep 2797409 = 2098057) B2098057
theorem B2617187 : Blo 1744573 2617187 := bstep (se 1 (by rfl) ⟨1962890, by rfl⟩ : syracuseStep 2617187 = 3925781) B3925781
theorem B5590883 : Blo 1744573 5590883 := bstep (se 1 (by rfl) ⟨4193162, by rfl⟩ : syracuseStep 5590883 = 8386325) B8386325
theorem B2944883 : Blo 1744573 2944883 := bstep (se 1 (by rfl) ⟨2208662, by rfl⟩ : syracuseStep 2944883 = 4417325) B4417325
theorem B2617217 : Blo 1744573 2617217 := bstep (se 2 (by rfl) ⟨981456, by rfl⟩ : syracuseStep 2617217 = 1962913) B1962913
theorem B2617235 : Blo 1744573 2617235 := bstep (se 1 (by rfl) ⟨1962926, by rfl⟩ : syracuseStep 2617235 = 3925853) B3925853
theorem B2617265 : Blo 1744573 2617265 := bstep (se 2 (by rfl) ⟨981474, by rfl⟩ : syracuseStep 2617265 = 1962949) B1962949
theorem B8834993 : Blo 1744573 8834993 := bstep (se 2 (by rfl) ⟨3313122, by rfl⟩ : syracuseStep 8834993 = 6626245) B6626245
theorem B2125747 : Blo 1744573 2125747 := bstep (se 1 (by rfl) ⟨1594310, by rfl⟩ : syracuseStep 2125747 = 3188621) B3188621
theorem B2486209 : Blo 1744573 2486209 := bstep (se 2 (by rfl) ⟨932328, by rfl⟩ : syracuseStep 2486209 = 1864657) B1864657
theorem B2617283 : Blo 1744573 2617283 := bstep (se 1 (by rfl) ⟨1962962, by rfl⟩ : syracuseStep 2617283 = 3925925) B3925925
theorem B2617313 : Blo 1744573 2617313 := bstep (se 2 (by rfl) ⟨981492, by rfl⟩ : syracuseStep 2617313 = 1962985) B1962985
theorem B24203249 : Blo 1744573 24203249 := bstep (se 2 (by rfl) ⟨9076218, by rfl⟩ : syracuseStep 24203249 = 18152437) B18152437
theorem B3928049 : Blo 1744573 3928049 := bstep (se 2 (by rfl) ⟨1473018, by rfl⟩ : syracuseStep 3928049 = 2946037) B2946037
theorem B2617331 : Blo 1744573 2617331 := bstep (se 1 (by rfl) ⟨1962998, by rfl⟩ : syracuseStep 2617331 = 3925997) B3925997
theorem B2945011 : Blo 1744573 2945011 := bstep (se 1 (by rfl) ⟨2208758, by rfl⟩ : syracuseStep 2945011 = 4417517) B4417517
theorem B6631409 : Blo 1744573 6631409 := bstep (se 2 (by rfl) ⟨2486778, by rfl⟩ : syracuseStep 6631409 = 4973557) B4973557
theorem B3928067 : Blo 1744573 3928067 := bstep (se 1 (by rfl) ⟨2946050, by rfl⟩ : syracuseStep 3928067 = 5892101) B5892101
theorem B2617361 : Blo 1744573 2617361 := bstep (se 2 (by rfl) ⟨981510, by rfl⟩ : syracuseStep 2617361 = 1963021) B1963021
theorem B2617379 : Blo 1744573 2617379 := bstep (se 1 (by rfl) ⟨1963034, by rfl⟩ : syracuseStep 2617379 = 3926069) B3926069
theorem B2486323 : Blo 1744573 2486323 := bstep (se 1 (by rfl) ⟨1864742, by rfl⟩ : syracuseStep 2486323 = 3729485) B3729485
theorem B2617409 : Blo 1744573 2617409 := bstep (se 2 (by rfl) ⟨981528, by rfl⟩ : syracuseStep 2617409 = 1963057) B1963057
theorem B2617427 : Blo 1744573 2617427 := bstep (se 1 (by rfl) ⟨1963070, by rfl⟩ : syracuseStep 2617427 = 3926141) B3926141
theorem B2617457 : Blo 1744573 2617457 := bstep (se 2 (by rfl) ⟨981546, by rfl⟩ : syracuseStep 2617457 = 1963093) B1963093
theorem B2945153 : Blo 1744573 2945153 := bstep (se 2 (by rfl) ⟨1104432, by rfl⟩ : syracuseStep 2945153 = 2208865) B2208865
theorem B2617475 : Blo 1744573 2617475 := bstep (se 1 (by rfl) ⟨1963106, by rfl⟩ : syracuseStep 2617475 = 3926213) B3926213
theorem B2617505 : Blo 1744573 2617505 := bstep (se 2 (by rfl) ⟨981564, by rfl⟩ : syracuseStep 2617505 = 1963129) B1963129
theorem B2617523 : Blo 1744573 2617523 := bstep (se 1 (by rfl) ⟨1963142, by rfl⟩ : syracuseStep 2617523 = 3926285) B3926285
theorem B2617553 : Blo 1744573 2617553 := bstep (se 2 (by rfl) ⟨981582, by rfl⟩ : syracuseStep 2617553 = 1963165) B1963165
theorem B2617571 : Blo 1744573 2617571 := bstep (se 1 (by rfl) ⟨1963178, by rfl⟩ : syracuseStep 2617571 = 3926357) B3926357
theorem B2617601 : Blo 1744573 2617601 := bstep (se 2 (by rfl) ⟨981600, by rfl⟩ : syracuseStep 2617601 = 1963201) B1963201
theorem B2945281 : Blo 1744573 2945281 := bstep (se 2 (by rfl) ⟨1104480, by rfl⟩ : syracuseStep 2945281 = 2208961) B2208961
theorem B3928337 : Blo 1744573 3928337 := bstep (se 2 (by rfl) ⟨1473126, by rfl⟩ : syracuseStep 3928337 = 2946253) B2946253
theorem B2617619 : Blo 1744573 2617619 := bstep (se 1 (by rfl) ⟨1963214, by rfl⟩ : syracuseStep 2617619 = 3926429) B3926429
theorem B2945315 : Blo 1744573 2945315 := bstep (se 1 (by rfl) ⟨2208986, by rfl⟩ : syracuseStep 2945315 = 4417973) B4417973
theorem B3928355 : Blo 1744573 3928355 := bstep (se 1 (by rfl) ⟨2946266, by rfl⟩ : syracuseStep 3928355 = 5892533) B5892533
theorem B2617649 : Blo 1744573 2617649 := bstep (se 2 (by rfl) ⟨981618, by rfl⟩ : syracuseStep 2617649 = 1963237) B1963237
theorem B21229877 : Blo 1744573 21229877 := bstep (se 5 (by rfl) ⟨995150, by rfl⟩ : syracuseStep 21229877 = 1990301) B1990301
theorem B2617667 : Blo 1744573 2617667 := bstep (se 1 (by rfl) ⟨1963250, by rfl⟩ : syracuseStep 2617667 = 3926501) B3926501
theorem B5894477 : Blo 1744573 5894477 := bstep (se 3 (by rfl) ⟨1105214, by rfl⟩ : syracuseStep 5894477 = 2210429) B2210429
theorem B2617697 : Blo 1744573 2617697 := bstep (se 2 (by rfl) ⟨981636, by rfl⟩ : syracuseStep 2617697 = 1963273) B1963273
theorem B2617715 : Blo 1744573 2617715 := bstep (se 1 (by rfl) ⟨1963286, by rfl⟩ : syracuseStep 2617715 = 3926573) B3926573
theorem B5894531 : Blo 1744573 5894531 := bstep (se 1 (by rfl) ⟨4420898, by rfl⟩ : syracuseStep 5894531 = 8841797) B8841797
theorem B18149773 : Blo 1744573 18149773 := bstep (se 3 (by rfl) ⟨3403082, by rfl⟩ : syracuseStep 18149773 = 6806165) B6806165
theorem B2617745 : Blo 1744573 2617745 := bstep (se 2 (by rfl) ⟨981654, by rfl⟩ : syracuseStep 2617745 = 1963309) B1963309
theorem B2617763 : Blo 1744573 2617763 := bstep (se 1 (by rfl) ⟨1963322, by rfl⟩ : syracuseStep 2617763 = 3926645) B3926645
theorem B2945443 : Blo 1744573 2945443 := bstep (se 1 (by rfl) ⟨2209082, by rfl⟩ : syracuseStep 2945443 = 4418165) B4418165
theorem B2617793 : Blo 1744573 2617793 := bstep (se 2 (by rfl) ⟨981672, by rfl⟩ : syracuseStep 2617793 = 1963345) B1963345
theorem B2617811 : Blo 1744573 2617811 := bstep (se 1 (by rfl) ⟨1963358, by rfl⟩ : syracuseStep 2617811 = 3926717) B3926717
theorem B19878371 : Blo 1744573 19878371 := bstep (se 1 (by rfl) ⟨14908778, by rfl⟩ : syracuseStep 19878371 = 29817557) B29817557
theorem B2617841 : Blo 1744573 2617841 := bstep (se 2 (by rfl) ⟨981690, by rfl⟩ : syracuseStep 2617841 = 1963381) B1963381
theorem B5591537 : Blo 1744573 5591537 := bstep (se 2 (by rfl) ⟨2096826, by rfl⟩ : syracuseStep 5591537 = 4193653) B4193653
theorem B2617859 : Blo 1744573 2617859 := bstep (se 1 (by rfl) ⟨1963394, by rfl⟩ : syracuseStep 2617859 = 3926789) B3926789
theorem B2617889 : Blo 1744573 2617889 := bstep (se 2 (by rfl) ⟨981708, by rfl⟩ : syracuseStep 2617889 = 1963417) B1963417
theorem B2945585 : Blo 1744573 2945585 := bstep (se 2 (by rfl) ⟨1104594, by rfl⟩ : syracuseStep 2945585 = 2209189) B2209189
theorem B3928625 : Blo 1744573 3928625 := bstep (se 2 (by rfl) ⟨1473234, by rfl⟩ : syracuseStep 3928625 = 2946469) B2946469
theorem B2617907 : Blo 1744573 2617907 := bstep (se 1 (by rfl) ⟨1963430, by rfl⟩ : syracuseStep 2617907 = 3926861) B3926861
theorem B1864243 : Blo 1744573 1864243 := bstep (se 1 (by rfl) ⟨1398182, by rfl⟩ : syracuseStep 1864243 = 2796365) B2796365
theorem B2208323 : Blo 1744573 2208323 := bstep (se 1 (by rfl) ⟨1656242, by rfl⟩ : syracuseStep 2208323 = 3312485) B3312485
theorem B3928643 : Blo 1744573 3928643 := bstep (se 1 (by rfl) ⟨2946482, by rfl⟩ : syracuseStep 3928643 = 5892965) B5892965
theorem B2617937 : Blo 1744573 2617937 := bstep (se 2 (by rfl) ⟨981726, by rfl⟩ : syracuseStep 2617937 = 1963453) B1963453
theorem B2617955 : Blo 1744573 2617955 := bstep (se 1 (by rfl) ⟨1963466, by rfl⟩ : syracuseStep 2617955 = 3926933) B3926933
theorem B2617985 : Blo 1744573 2617985 := bstep (se 2 (by rfl) ⟨981744, by rfl⟩ : syracuseStep 2617985 = 1963489) B1963489
theorem B4420241 : Blo 1744573 4420241 := bstep (se 2 (by rfl) ⟨1657590, by rfl⟩ : syracuseStep 4420241 = 3315181) B3315181
theorem B2618003 : Blo 1744573 2618003 := bstep (se 1 (by rfl) ⟨1963502, by rfl⟩ : syracuseStep 2618003 = 3927005) B3927005
theorem B2618033 : Blo 1744573 2618033 := bstep (se 2 (by rfl) ⟨981762, by rfl⟩ : syracuseStep 2618033 = 1963525) B1963525
theorem B2945713 : Blo 1744573 2945713 := bstep (se 2 (by rfl) ⟨1104642, by rfl⟩ : syracuseStep 2945713 = 2209285) B2209285
theorem B3314353 : Blo 1744573 3314353 := bstep (se 2 (by rfl) ⟨1242882, by rfl⟩ : syracuseStep 3314353 = 2485765) B2485765
theorem B2618051 : Blo 1744573 2618051 := bstep (se 1 (by rfl) ⟨1963538, by rfl⟩ : syracuseStep 2618051 = 3927077) B3927077
theorem B4420291 : Blo 1744573 4420291 := bstep (se 1 (by rfl) ⟨3315218, by rfl⟩ : syracuseStep 4420291 = 6630437) B6630437
theorem B2945747 : Blo 1744573 2945747 := bstep (se 1 (by rfl) ⟨2209310, by rfl⟩ : syracuseStep 2945747 = 4418621) B4418621
theorem B2618081 : Blo 1744573 2618081 := bstep (se 2 (by rfl) ⟨981780, by rfl⟩ : syracuseStep 2618081 = 1963561) B1963561
theorem B2618099 : Blo 1744573 2618099 := bstep (se 1 (by rfl) ⟨1963574, by rfl⟩ : syracuseStep 2618099 = 3927149) B3927149
theorem B2618129 : Blo 1744573 2618129 := bstep (se 2 (by rfl) ⟨981798, by rfl⟩ : syracuseStep 2618129 = 1963597) B1963597
theorem B1962787 : Blo 1744573 1962787 := bstep (se 1 (by rfl) ⟨1472090, by rfl⟩ : syracuseStep 1962787 = 2944181) B2944181
theorem B2618147 : Blo 1744573 2618147 := bstep (se 1 (by rfl) ⟨1963610, by rfl⟩ : syracuseStep 2618147 = 3927221) B3927221
theorem B2618177 : Blo 1744573 2618177 := bstep (se 2 (by rfl) ⟨981816, by rfl⟩ : syracuseStep 2618177 = 1963633) B1963633
theorem B3314513 : Blo 1744573 3314513 := bstep (se 2 (by rfl) ⟨1242942, by rfl⟩ : syracuseStep 3314513 = 2485885) B2485885
theorem B3928913 : Blo 1744573 3928913 := bstep (se 2 (by rfl) ⟨1473342, by rfl⟩ : syracuseStep 3928913 = 2946685) B2946685
theorem B2618195 : Blo 1744573 2618195 := bstep (se 1 (by rfl) ⟨1963646, by rfl⟩ : syracuseStep 2618195 = 3927293) B3927293
theorem B2945875 : Blo 1744573 2945875 := bstep (se 1 (by rfl) ⟨2209406, by rfl⟩ : syracuseStep 2945875 = 4418813) B4418813
theorem B4420433 : Blo 1744573 4420433 := bstep (se 2 (by rfl) ⟨1657662, by rfl⟩ : syracuseStep 4420433 = 3315325) B3315325
theorem B3928931 : Blo 1744573 3928931 := bstep (se 1 (by rfl) ⟨2946698, by rfl⟩ : syracuseStep 3928931 = 5893397) B5893397
theorem B2618225 : Blo 1744573 2618225 := bstep (se 2 (by rfl) ⟨981834, by rfl⟩ : syracuseStep 2618225 = 1963669) B1963669
theorem B2618243 : Blo 1744573 2618243 := bstep (se 1 (by rfl) ⟨1963682, by rfl⟩ : syracuseStep 2618243 = 3927365) B3927365
theorem B2618273 : Blo 1744573 2618273 := bstep (se 2 (by rfl) ⟨981852, by rfl⟩ : syracuseStep 2618273 = 1963705) B1963705
theorem B1962931 : Blo 1744573 1962931 := bstep (se 1 (by rfl) ⟨1472198, by rfl⟩ : syracuseStep 1962931 = 2944397) B2944397
theorem B2618291 : Blo 1744573 2618291 := bstep (se 1 (by rfl) ⟨1963718, by rfl⟩ : syracuseStep 2618291 = 3927437) B3927437
theorem B7459789 : Blo 1744573 7459789 := bstep (se 3 (by rfl) ⟨1398710, by rfl⟩ : syracuseStep 7459789 = 2797421) B2797421
theorem B2618321 : Blo 1744573 2618321 := bstep (se 2 (by rfl) ⟨981870, by rfl⟩ : syracuseStep 2618321 = 1963741) B1963741
theorem B2946017 : Blo 1744573 2946017 := bstep (se 2 (by rfl) ⟨1104756, by rfl⟩ : syracuseStep 2946017 = 2209513) B2209513
theorem B2618339 : Blo 1744573 2618339 := bstep (se 1 (by rfl) ⟨1963754, by rfl⟩ : syracuseStep 2618339 = 3927509) B3927509
theorem B4969457 : Blo 1744573 4969457 := bstep (se 2 (by rfl) ⟨1863546, by rfl⟩ : syracuseStep 4969457 = 3727093) B3727093
theorem B2618369 : Blo 1744573 2618369 := bstep (se 2 (by rfl) ⟨981888, by rfl⟩ : syracuseStep 2618369 = 1963777) B1963777
theorem B2618387 : Blo 1744573 2618387 := bstep (se 1 (by rfl) ⟨1963790, by rfl⟩ : syracuseStep 2618387 = 3927581) B3927581
theorem B2618417 : Blo 1744573 2618417 := bstep (se 2 (by rfl) ⟨981906, by rfl⟩ : syracuseStep 2618417 = 1963813) B1963813
theorem B1963075 : Blo 1744573 1963075 := bstep (se 1 (by rfl) ⟨1472306, by rfl⟩ : syracuseStep 1963075 = 2944613) B2944613
theorem B2618435 : Blo 1744573 2618435 := bstep (se 1 (by rfl) ⟨1963826, by rfl⟩ : syracuseStep 2618435 = 3927653) B3927653
theorem B2618465 : Blo 1744573 2618465 := bstep (se 2 (by rfl) ⟨981924, by rfl⟩ : syracuseStep 2618465 = 1963849) B1963849
theorem B2946145 : Blo 1744573 2946145 := bstep (se 2 (by rfl) ⟨1104804, by rfl⟩ : syracuseStep 2946145 = 2209609) B2209609
theorem B3929201 : Blo 1744573 3929201 := bstep (se 2 (by rfl) ⟨1473450, by rfl⟩ : syracuseStep 3929201 = 2946901) B2946901
theorem B2618483 : Blo 1744573 2618483 := bstep (se 1 (by rfl) ⟨1963862, by rfl⟩ : syracuseStep 2618483 = 3927725) B3927725
theorem B2946179 : Blo 1744573 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B3929219 : Blo 1744573 3929219 := bstep (se 1 (by rfl) ⟨2946914, by rfl⟩ : syracuseStep 3929219 = 5893829) B5893829
theorem B2618513 : Blo 1744573 2618513 := bstep (se 2 (by rfl) ⟨981942, by rfl⟩ : syracuseStep 2618513 = 1963885) B1963885
theorem B2618531 : Blo 1744573 2618531 := bstep (se 1 (by rfl) ⟨1963898, by rfl⟩ : syracuseStep 2618531 = 3927797) B3927797
theorem B2618561 : Blo 1744573 2618561 := bstep (se 2 (by rfl) ⟨981960, by rfl⟩ : syracuseStep 2618561 = 1963921) B1963921
theorem B1963219 : Blo 1744573 1963219 := bstep (se 1 (by rfl) ⟨1472414, by rfl⟩ : syracuseStep 1963219 = 2944829) B2944829
theorem B2618579 : Blo 1744573 2618579 := bstep (se 1 (by rfl) ⟨1963934, by rfl⟩ : syracuseStep 2618579 = 3927869) B3927869
theorem B3314915 : Blo 1744573 3314915 := bstep (se 1 (by rfl) ⟨2486186, by rfl⟩ : syracuseStep 3314915 = 4972373) B4972373
theorem B2618609 : Blo 1744573 2618609 := bstep (se 2 (by rfl) ⟨981978, by rfl⟩ : syracuseStep 2618609 = 1963957) B1963957
theorem B2209027 : Blo 1744573 2209027 := bstep (se 1 (by rfl) ⟨1656770, by rfl⟩ : syracuseStep 2209027 = 3313541) B3313541
theorem B2618627 : Blo 1744573 2618627 := bstep (se 1 (by rfl) ⟨1963970, by rfl⟩ : syracuseStep 2618627 = 3927941) B3927941
theorem B2946307 : Blo 1744573 2946307 := bstep (se 1 (by rfl) ⟨2209730, by rfl⟩ : syracuseStep 2946307 = 4419461) B4419461
theorem B2618657 : Blo 1744573 2618657 := bstep (se 2 (by rfl) ⟨981996, by rfl⟩ : syracuseStep 2618657 = 1963993) B1963993
theorem B5305645 : Blo 1744573 5305645 := bstep (se 3 (by rfl) ⟨994808, by rfl⟩ : syracuseStep 5305645 = 1989617) B1989617
theorem B2618675 : Blo 1744573 2618675 := bstep (se 1 (by rfl) ⟨1964006, by rfl⟩ : syracuseStep 2618675 = 3928013) B3928013
theorem B3028291 : Blo 1744573 3028291 := bstep (se 1 (by rfl) ⟨2271218, by rfl⟩ : syracuseStep 3028291 = 4542437) B4542437
theorem B2618705 : Blo 1744573 2618705 := bstep (se 2 (by rfl) ⟨982014, by rfl⟩ : syracuseStep 2618705 = 1964029) B1964029
theorem B1963363 : Blo 1744573 1963363 := bstep (se 1 (by rfl) ⟨1472522, by rfl⟩ : syracuseStep 1963363 = 2945045) B2945045
theorem B8836451 : Blo 1744573 8836451 := bstep (se 1 (by rfl) ⟨6627338, by rfl⟩ : syracuseStep 8836451 = 13254677) B13254677
theorem B2209123 : Blo 1744573 2209123 := bstep (se 1 (by rfl) ⟨1656842, by rfl⟩ : syracuseStep 2209123 = 3313685) B3313685
theorem B2618723 : Blo 1744573 2618723 := bstep (se 1 (by rfl) ⟨1964042, by rfl⟩ : syracuseStep 2618723 = 3928085) B3928085
theorem B2618753 : Blo 1744573 2618753 := bstep (se 2 (by rfl) ⟨982032, by rfl⟩ : syracuseStep 2618753 = 1964065) B1964065
theorem B2946449 : Blo 1744573 2946449 := bstep (se 2 (by rfl) ⟨1104918, by rfl⟩ : syracuseStep 2946449 = 2209837) B2209837
theorem B2618771 : Blo 1744573 2618771 := bstep (se 1 (by rfl) ⟨1964078, by rfl⟩ : syracuseStep 2618771 = 3928157) B3928157
theorem B3929489 : Blo 1744573 3929489 := bstep (se 2 (by rfl) ⟨1473558, by rfl⟩ : syracuseStep 3929489 = 2947117) B2947117
theorem B3929507 : Blo 1744573 3929507 := bstep (se 1 (by rfl) ⟨2947130, by rfl⟩ : syracuseStep 3929507 = 5894261) B5894261
theorem B2618801 : Blo 1744573 2618801 := bstep (se 2 (by rfl) ⟨982050, by rfl⟩ : syracuseStep 2618801 = 1964101) B1964101
theorem B2618819 : Blo 1744573 2618819 := bstep (se 1 (by rfl) ⟨1964114, by rfl⟩ : syracuseStep 2618819 = 3928229) B3928229
theorem B2618849 : Blo 1744573 2618849 := bstep (se 2 (by rfl) ⟨982068, by rfl⟩ : syracuseStep 2618849 = 1964137) B1964137
theorem B1963507 : Blo 1744573 1963507 := bstep (se 1 (by rfl) ⟨1472630, by rfl⟩ : syracuseStep 1963507 = 2945261) B2945261
theorem B2618867 : Blo 1744573 2618867 := bstep (se 1 (by rfl) ⟨1964150, by rfl⟩ : syracuseStep 2618867 = 3928301) B3928301
theorem B11949581 : Blo 1744573 11949581 := bstep (se 3 (by rfl) ⟨2240546, by rfl⟩ : syracuseStep 11949581 = 4481093) B4481093
theorem B2618897 : Blo 1744573 2618897 := bstep (se 2 (by rfl) ⟨982086, by rfl⟩ : syracuseStep 2618897 = 1964173) B1964173
theorem B2946577 : Blo 1744573 2946577 := bstep (se 2 (by rfl) ⟨1104966, by rfl⟩ : syracuseStep 2946577 = 2209933) B2209933
theorem B2618915 : Blo 1744573 2618915 := bstep (se 1 (by rfl) ⟨1964186, by rfl⟩ : syracuseStep 2618915 = 3928373) B3928373
theorem B2946611 : Blo 1744573 2946611 := bstep (se 1 (by rfl) ⟨2209958, by rfl⟩ : syracuseStep 2946611 = 4419917) B4419917
theorem B2618945 : Blo 1744573 2618945 := bstep (se 2 (by rfl) ⟨982104, by rfl⟩ : syracuseStep 2618945 = 1964209) B1964209
theorem B2618963 : Blo 1744573 2618963 := bstep (se 1 (by rfl) ⟨1964222, by rfl⟩ : syracuseStep 2618963 = 3928445) B3928445
theorem B4191857 : Blo 1744573 4191857 := bstep (se 2 (by rfl) ⟨1571946, by rfl⟩ : syracuseStep 4191857 = 3143893) B3143893
theorem B2618993 : Blo 1744573 2618993 := bstep (se 2 (by rfl) ⟨982122, by rfl⟩ : syracuseStep 2618993 = 1964245) B1964245
theorem B1963651 : Blo 1744573 1963651 := bstep (se 1 (by rfl) ⟨1472738, by rfl⟩ : syracuseStep 1963651 = 2945477) B2945477
theorem B2619011 : Blo 1744573 2619011 := bstep (se 1 (by rfl) ⟨1964258, by rfl⟩ : syracuseStep 2619011 = 3928517) B3928517
theorem B2619041 : Blo 1744573 2619041 := bstep (se 2 (by rfl) ⟨982140, by rfl⟩ : syracuseStep 2619041 = 1964281) B1964281
theorem B3929777 : Blo 1744573 3929777 := bstep (se 2 (by rfl) ⟨1473666, by rfl⟩ : syracuseStep 3929777 = 2947333) B2947333
theorem B2619059 : Blo 1744573 2619059 := bstep (se 1 (by rfl) ⟨1964294, by rfl⟩ : syracuseStep 2619059 = 3928589) B3928589
theorem B2946739 : Blo 1744573 2946739 := bstep (se 1 (by rfl) ⟨2210054, by rfl⟩ : syracuseStep 2946739 = 4420109) B4420109
theorem B2619089 : Blo 1744573 2619089 := bstep (se 2 (by rfl) ⟨982158, by rfl⟩ : syracuseStep 2619089 = 1964317) B1964317
theorem B2619107 : Blo 1744573 2619107 := bstep (se 1 (by rfl) ⟨1964330, by rfl⟩ : syracuseStep 2619107 = 3928661) B3928661
theorem B2619137 : Blo 1744573 2619137 := bstep (se 2 (by rfl) ⟨982176, by rfl⟩ : syracuseStep 2619137 = 1964353) B1964353
theorem B1963795 : Blo 1744573 1963795 := bstep (se 1 (by rfl) ⟨1472846, by rfl⟩ : syracuseStep 1963795 = 2945693) B2945693
theorem B2619155 : Blo 1744573 2619155 := bstep (se 1 (by rfl) ⟨1964366, by rfl⟩ : syracuseStep 2619155 = 3928733) B3928733
theorem B2619185 : Blo 1744573 2619185 := bstep (se 2 (by rfl) ⟨982194, by rfl⟩ : syracuseStep 2619185 = 1964389) B1964389
theorem B2946881 : Blo 1744573 2946881 := bstep (se 2 (by rfl) ⟨1105080, by rfl⟩ : syracuseStep 2946881 = 2210161) B2210161
theorem B1914691 : Blo 1744573 1914691 := bstep (se 1 (by rfl) ⟨1436018, by rfl⟩ : syracuseStep 1914691 = 2872037) B2872037
theorem B2619203 : Blo 1744573 2619203 := bstep (se 1 (by rfl) ⟨1964402, by rfl⟩ : syracuseStep 2619203 = 3928805) B3928805
theorem B2209619 : Blo 1744573 2209619 := bstep (se 1 (by rfl) ⟨1657214, by rfl⟩ : syracuseStep 2209619 = 3314429) B3314429
theorem B2619233 : Blo 1744573 2619233 := bstep (se 2 (by rfl) ⟨982212, by rfl⟩ : syracuseStep 2619233 = 1964425) B1964425
theorem B2619251 : Blo 1744573 2619251 := bstep (se 1 (by rfl) ⟨1964438, by rfl⟩ : syracuseStep 2619251 = 3928877) B3928877
theorem B2619281 : Blo 1744573 2619281 := bstep (se 2 (by rfl) ⟨982230, by rfl⟩ : syracuseStep 2619281 = 1964461) B1964461
theorem B1963939 : Blo 1744573 1963939 := bstep (se 1 (by rfl) ⟨1472954, by rfl⟩ : syracuseStep 1963939 = 2945909) B2945909
theorem B2619299 : Blo 1744573 2619299 := bstep (se 1 (by rfl) ⟨1964474, by rfl⟩ : syracuseStep 2619299 = 3928949) B3928949
theorem B4970413 : Blo 1744573 4970413 := bstep (se 3 (by rfl) ⟨931952, by rfl⟩ : syracuseStep 4970413 = 1863905) B1863905
theorem B11188145 : Blo 1744573 11188145 := bstep (se 2 (by rfl) ⟨4195554, by rfl⟩ : syracuseStep 11188145 = 8391109) B8391109
theorem B2619329 : Blo 1744573 2619329 := bstep (se 2 (by rfl) ⟨982248, by rfl⟩ : syracuseStep 2619329 = 1964497) B1964497
theorem B2947009 : Blo 1744573 2947009 := bstep (se 2 (by rfl) ⟨1105128, by rfl⟩ : syracuseStep 2947009 = 2210257) B2210257
theorem B2619347 : Blo 1744573 2619347 := bstep (se 1 (by rfl) ⟨1964510, by rfl⟩ : syracuseStep 2619347 = 3929021) B3929021
theorem B2947043 : Blo 1744573 2947043 := bstep (se 1 (by rfl) ⟨2210282, by rfl⟩ : syracuseStep 2947043 = 4420565) B4420565
theorem B2619377 : Blo 1744573 2619377 := bstep (se 2 (by rfl) ⟨982266, by rfl⟩ : syracuseStep 2619377 = 1964533) B1964533
theorem B2619395 : Blo 1744573 2619395 := bstep (se 1 (by rfl) ⟨1964546, by rfl⟩ : syracuseStep 2619395 = 3929093) B3929093
theorem B2619425 : Blo 1744573 2619425 := bstep (se 2 (by rfl) ⟨982284, by rfl⟩ : syracuseStep 2619425 = 1964569) B1964569
theorem B1964083 : Blo 1744573 1964083 := bstep (se 1 (by rfl) ⟨1473062, by rfl⟩ : syracuseStep 1964083 = 2946125) B2946125
theorem B2619443 : Blo 1744573 2619443 := bstep (se 1 (by rfl) ⟨1964582, by rfl⟩ : syracuseStep 2619443 = 3929165) B3929165
theorem B7452749 : Blo 1744573 7452749 := bstep (se 3 (by rfl) ⟨1397390, by rfl⟩ : syracuseStep 7452749 = 2794781) B2794781
theorem B2619473 : Blo 1744573 2619473 := bstep (se 2 (by rfl) ⟨982302, by rfl⟩ : syracuseStep 2619473 = 1964605) B1964605
theorem B3979363 : Blo 1744573 3979363 := bstep (se 1 (by rfl) ⟨2984522, by rfl⟩ : syracuseStep 3979363 = 5969045) B5969045
theorem B2619491 : Blo 1744573 2619491 := bstep (se 1 (by rfl) ⟨1964618, by rfl⟩ : syracuseStep 2619491 = 3929237) B3929237
theorem B2947171 : Blo 1744573 2947171 := bstep (se 1 (by rfl) ⟨2210378, by rfl⟩ : syracuseStep 2947171 = 4420757) B4420757
theorem B2619521 : Blo 1744573 2619521 := bstep (se 2 (by rfl) ⟨982320, by rfl⟩ : syracuseStep 2619521 = 1964641) B1964641
theorem B8837261 : Blo 1744573 8837261 := bstep (se 3 (by rfl) ⟨1656986, by rfl⟩ : syracuseStep 8837261 = 3313973) B3313973
theorem B4970641 : Blo 1744573 4970641 := bstep (se 2 (by rfl) ⟨1863990, by rfl⟩ : syracuseStep 4970641 = 3727981) B3727981
theorem B2619539 : Blo 1744573 2619539 := bstep (se 1 (by rfl) ⟨1964654, by rfl⟩ : syracuseStep 2619539 = 3929309) B3929309
theorem B2619569 : Blo 1744573 2619569 := bstep (se 2 (by rfl) ⟨982338, by rfl⟩ : syracuseStep 2619569 = 1964677) B1964677
theorem B1964227 : Blo 1744573 1964227 := bstep (se 1 (by rfl) ⟨1473170, by rfl⟩ : syracuseStep 1964227 = 2946341) B2946341
theorem B2619587 : Blo 1744573 2619587 := bstep (se 1 (by rfl) ⟨1964690, by rfl⟩ : syracuseStep 2619587 = 3929381) B3929381
theorem B2619617 : Blo 1744573 2619617 := bstep (se 2 (by rfl) ⟨982356, by rfl⟩ : syracuseStep 2619617 = 1964713) B1964713
theorem B2947313 : Blo 1744573 2947313 := bstep (se 2 (by rfl) ⟨1105242, by rfl⟩ : syracuseStep 2947313 = 2210485) B2210485
theorem B2619635 : Blo 1744573 2619635 := bstep (se 1 (by rfl) ⟨1964726, by rfl⟩ : syracuseStep 2619635 = 3929453) B3929453
theorem B2619665 : Blo 1744573 2619665 := bstep (se 2 (by rfl) ⟨982374, by rfl⟩ : syracuseStep 2619665 = 1964749) B1964749
theorem B2619683 : Blo 1744573 2619683 := bstep (se 1 (by rfl) ⟨1964762, by rfl⟩ : syracuseStep 2619683 = 3929525) B3929525
theorem B4970801 : Blo 1744573 4970801 := bstep (se 2 (by rfl) ⟨1864050, by rfl⟩ : syracuseStep 4970801 = 3728101) B3728101
theorem B2619713 : Blo 1744573 2619713 := bstep (se 2 (by rfl) ⟨982392, by rfl⟩ : syracuseStep 2619713 = 1964785) B1964785
theorem B1964371 : Blo 1744573 1964371 := bstep (se 1 (by rfl) ⟨1473278, by rfl⟩ : syracuseStep 1964371 = 2946557) B2946557
theorem B2619731 : Blo 1744573 2619731 := bstep (se 1 (by rfl) ⟨1964798, by rfl⟩ : syracuseStep 2619731 = 3929597) B3929597
theorem B11942243 : Blo 1744573 11942243 := bstep (se 1 (by rfl) ⟨8956682, by rfl⟩ : syracuseStep 11942243 = 17913365) B17913365
theorem B2619761 : Blo 1744573 2619761 := bstep (se 2 (by rfl) ⟨982410, by rfl⟩ : syracuseStep 2619761 = 1964821) B1964821
theorem B2619779 : Blo 1744573 2619779 := bstep (se 1 (by rfl) ⟨1964834, by rfl⟩ : syracuseStep 2619779 = 3929669) B3929669
theorem B16783757 : Blo 1744573 16783757 := bstep (se 3 (by rfl) ⟨3146954, by rfl⟩ : syracuseStep 16783757 = 6293909) B6293909
theorem B2619809 : Blo 1744573 2619809 := bstep (se 2 (by rfl) ⟨982428, by rfl⟩ : syracuseStep 2619809 = 1964857) B1964857
theorem B4970915 : Blo 1744573 4970915 := bstep (se 1 (by rfl) ⟨3728186, by rfl⟩ : syracuseStep 4970915 = 7456373) B7456373
theorem B5888429 : Blo 1744573 5888429 := bstep (se 3 (by rfl) ⟨1104080, by rfl⟩ : syracuseStep 5888429 = 2208161) B2208161
theorem B2619827 : Blo 1744573 2619827 := bstep (se 1 (by rfl) ⟨1964870, by rfl⟩ : syracuseStep 2619827 = 3929741) B3929741
theorem B5593549 : Blo 1744573 5593549 := bstep (se 3 (by rfl) ⟨1048790, by rfl⟩ : syracuseStep 5593549 = 2097581) B2097581
theorem B2619857 : Blo 1744573 2619857 := bstep (se 2 (by rfl) ⟨982446, by rfl⟩ : syracuseStep 2619857 = 1964893) B1964893
theorem B5888483 : Blo 1744573 5888483 := bstep (se 1 (by rfl) ⟨4416362, by rfl⟩ : syracuseStep 5888483 = 8832725) B8832725
theorem B1964515 : Blo 1744573 1964515 := bstep (se 1 (by rfl) ⟨1473386, by rfl⟩ : syracuseStep 1964515 = 2946773) B2946773
theorem B2210323 : Blo 1744573 2210323 := bstep (se 1 (by rfl) ⟨1657742, by rfl⟩ : syracuseStep 2210323 = 3315485) B3315485
theorem B11188813 : Blo 1744573 11188813 := bstep (se 3 (by rfl) ⟨2097902, by rfl⟩ : syracuseStep 11188813 = 4195805) B4195805
theorem B13253219 : Blo 1744573 13253219 := bstep (se 1 (by rfl) ⟨9939914, by rfl⟩ : syracuseStep 13253219 = 19879829) B19879829
theorem B9435761 : Blo 1744573 9435761 := bstep (se 2 (by rfl) ⟨3538410, by rfl⟩ : syracuseStep 9435761 = 7076821) B7076821
theorem B1964659 : Blo 1744573 1964659 := bstep (se 1 (by rfl) ⟨1473494, by rfl⟩ : syracuseStep 1964659 = 2946989) B2946989
theorem B2210419 : Blo 1744573 2210419 := bstep (se 1 (by rfl) ⟨1657814, by rfl⟩ : syracuseStep 2210419 = 3315629) B3315629
theorem B15932045 : Blo 1744573 15932045 := bstep (se 3 (by rfl) ⟨2987258, by rfl⟩ : syracuseStep 15932045 = 5974517) B5974517
theorem B3537553 : Blo 1744573 3537553 := bstep (se 2 (by rfl) ⟨1326582, by rfl⟩ : syracuseStep 3537553 = 2653165) B2653165
theorem B5888753 : Blo 1744573 5888753 := bstep (se 2 (by rfl) ⟨2208282, by rfl⟩ : syracuseStep 5888753 = 4416565) B4416565
theorem B6626033 : Blo 1744573 6626033 := bstep (se 2 (by rfl) ⟨2484762, by rfl⟩ : syracuseStep 6626033 = 4969525) B4969525
theorem B1964803 : Blo 1744573 1964803 := bstep (se 1 (by rfl) ⟨1473602, by rfl⟩ : syracuseStep 1964803 = 2947205) B2947205
theorem B25156493 : Blo 1744573 25156493 := bstep (se 3 (by rfl) ⟨4716842, by rfl⟩ : syracuseStep 25156493 = 9433685) B9433685
theorem B5593997 : Blo 1744573 5593997 := bstep (se 3 (by rfl) ⟨1048874, by rfl⟩ : syracuseStep 5593997 = 2097749) B2097749
theorem B3357649 : Blo 1744573 3357649 := bstep (se 2 (by rfl) ⟨1259118, by rfl⟩ : syracuseStep 3357649 = 2518237) B2518237
theorem B5307373 : Blo 1744573 5307373 := bstep (se 3 (by rfl) ⟨995132, by rfl⟩ : syracuseStep 5307373 = 1990265) B1990265
theorem B2653249 : Blo 1744573 2653249 := bstep (se 2 (by rfl) ⟨994968, by rfl⟩ : syracuseStep 2653249 = 1989937) B1989937
theorem B6716515 : Blo 1744573 6716515 := bstep (se 1 (by rfl) ⟨5037386, by rfl⟩ : syracuseStep 6716515 = 10074773) B10074773
theorem B20151395 : Blo 1744573 20151395 := bstep (se 1 (by rfl) ⟨15113546, by rfl⟩ : syracuseStep 20151395 = 30227093) B30227093
theorem B14916707 : Blo 1744573 14916707 := bstep (se 1 (by rfl) ⟨11187530, by rfl⟩ : syracuseStep 14916707 = 22375061) B22375061
theorem B5307569 : Blo 1744573 5307569 := bstep (se 2 (by rfl) ⟨1990338, by rfl⟩ : syracuseStep 5307569 = 3980677) B3980677
theorem B14908643 : Blo 1744573 14908643 := bstep (se 1 (by rfl) ⟨11181482, by rfl⟩ : syracuseStep 14908643 = 22362965) B22362965
theorem B5889293 : Blo 1744573 5889293 := bstep (se 3 (by rfl) ⟨1104242, by rfl⟩ : syracuseStep 5889293 = 2208485) B2208485
theorem B3726641 : Blo 1744573 3726641 := bstep (se 2 (by rfl) ⟨1397490, by rfl⟩ : syracuseStep 3726641 = 2794981) B2794981
theorem B3145009 : Blo 1744573 3145009 := bstep (se 2 (by rfl) ⟨1179378, by rfl⟩ : syracuseStep 3145009 = 2358757) B2358757
theorem B5889347 : Blo 1744573 5889347 := bstep (se 1 (by rfl) ⟨4417010, by rfl⟩ : syracuseStep 5889347 = 8834021) B8834021
theorem B4971917 : Blo 1744573 4971917 := bstep (se 3 (by rfl) ⟨932234, by rfl⟩ : syracuseStep 4971917 = 1864469) B1864469
theorem B4972099 : Blo 1744573 4972099 := bstep (se 1 (by rfl) ⟨3729074, by rfl⟩ : syracuseStep 4972099 = 7458149) B7458149
theorem B9944653 : Blo 1744573 9944653 := bstep (se 3 (by rfl) ⟨1864622, by rfl⟩ : syracuseStep 9944653 = 3729245) B3729245
theorem B5889617 : Blo 1744573 5889617 := bstep (se 2 (by rfl) ⟨2208606, by rfl⟩ : syracuseStep 5889617 = 4417213) B4417213
theorem B5668525 : Blo 1744573 5668525 := bstep (se 3 (by rfl) ⟨1062848, by rfl⟩ : syracuseStep 5668525 = 2125697) B2125697
theorem B1744579 : Blo 1744573 1744579 := bstep (se 1 (by rfl) ⟨1308434, by rfl⟩ : syracuseStep 1744579 = 2616869) B2616869
theorem B1744595 : Blo 1744573 1744595 := bstep (se 1 (by rfl) ⟨1308446, by rfl⟩ : syracuseStep 1744595 = 2616893) B2616893
theorem B1744611 : Blo 1744573 1744611 := bstep (se 1 (by rfl) ⟨1308458, by rfl⟩ : syracuseStep 1744611 = 2616917) B2616917
theorem B4972259 : Blo 1744573 4972259 := bstep (se 1 (by rfl) ⟨3729194, by rfl⟩ : syracuseStep 4972259 = 7458389) B7458389
theorem B3981041 : Blo 1744573 3981041 := bstep (se 2 (by rfl) ⟨1492890, by rfl⟩ : syracuseStep 3981041 = 2985781) B2985781
theorem B1744627 : Blo 1744573 1744627 := bstep (se 1 (by rfl) ⟨1308470, by rfl⟩ : syracuseStep 1744627 = 2616941) B2616941
theorem B2359027 : Blo 1744573 2359027 := bstep (se 1 (by rfl) ⟨1769270, by rfl⟩ : syracuseStep 2359027 = 3538541) B3538541
theorem B1744643 : Blo 1744573 1744643 := bstep (se 1 (by rfl) ⟨1308482, by rfl⟩ : syracuseStep 1744643 = 2616965) B2616965
theorem B1744659 : Blo 1744573 1744659 := bstep (se 1 (by rfl) ⟨1308494, by rfl⟩ : syracuseStep 1744659 = 2616989) B2616989
theorem B1744675 : Blo 1744573 1744675 := bstep (se 1 (by rfl) ⟨1308506, by rfl⟩ : syracuseStep 1744675 = 2617013) B2617013
theorem B1744691 : Blo 1744573 1744691 := bstep (se 1 (by rfl) ⟨1308518, by rfl⟩ : syracuseStep 1744691 = 2617037) B2617037
theorem B1744707 : Blo 1744573 1744707 := bstep (se 1 (by rfl) ⟨1308530, by rfl⟩ : syracuseStep 1744707 = 2617061) B2617061
theorem B1744723 : Blo 1744573 1744723 := bstep (se 1 (by rfl) ⟨1308542, by rfl⟩ : syracuseStep 1744723 = 2617085) B2617085
theorem B1744739 : Blo 1744573 1744739 := bstep (se 1 (by rfl) ⟨1308554, by rfl⟩ : syracuseStep 1744739 = 2617109) B2617109
theorem B3145571 : Blo 1744573 3145571 := bstep (se 1 (by rfl) ⟨2359178, by rfl⟩ : syracuseStep 3145571 = 4718357) B4718357
theorem B1744755 : Blo 1744573 1744755 := bstep (se 1 (by rfl) ⟨1308566, by rfl⟩ : syracuseStep 1744755 = 2617133) B2617133
theorem B1744771 : Blo 1744573 1744771 := bstep (se 1 (by rfl) ⟨1308578, by rfl⟩ : syracuseStep 1744771 = 2617157) B2617157
theorem B1744787 : Blo 1744573 1744787 := bstep (se 1 (by rfl) ⟨1308590, by rfl⟩ : syracuseStep 1744787 = 2617181) B2617181
theorem B1744803 : Blo 1744573 1744803 := bstep (se 1 (by rfl) ⟨1308602, by rfl⟩ : syracuseStep 1744803 = 2617205) B2617205
theorem B1744819 : Blo 1744573 1744819 := bstep (se 1 (by rfl) ⟨1308614, by rfl⟩ : syracuseStep 1744819 = 2617229) B2617229
theorem B1744835 : Blo 1744573 1744835 := bstep (se 1 (by rfl) ⟨1308626, by rfl⟩ : syracuseStep 1744835 = 2617253) B2617253
theorem B14155717 : Blo 1744573 14155717 := bstep (se 4 (by rfl) ⟨1327098, by rfl⟩ : syracuseStep 14155717 = 2654197) B2654197
theorem B1744851 : Blo 1744573 1744851 := bstep (se 1 (by rfl) ⟨1308638, by rfl⟩ : syracuseStep 1744851 = 2617277) B2617277
theorem B1744867 : Blo 1744573 1744867 := bstep (se 1 (by rfl) ⟨1308650, by rfl⟩ : syracuseStep 1744867 = 2617301) B2617301
theorem B1744883 : Blo 1744573 1744883 := bstep (se 1 (by rfl) ⟨1308662, by rfl⟩ : syracuseStep 1744883 = 2617325) B2617325
theorem B1744907 : Blo 1744573 1744907 := bstep (se 1 (by rfl) ⟨1308680, by rfl⟩ : syracuseStep 1744907 = 2617361) B2617361
theorem B1744919 : Blo 1744573 1744919 := bstep (se 1 (by rfl) ⟨1308689, by rfl⟩ : syracuseStep 1744919 = 2617379) B2617379
theorem B4718615 : Blo 1744573 4718615 := bstep (se 1 (by rfl) ⟨3538961, by rfl⟩ : syracuseStep 4718615 = 7077923) B7077923
theorem B1744939 : Blo 1744573 1744939 := bstep (se 1 (by rfl) ⟨1308704, by rfl⟩ : syracuseStep 1744939 = 2617409) B2617409
theorem B1744951 : Blo 1744573 1744951 := bstep (se 1 (by rfl) ⟨1308713, by rfl⟩ : syracuseStep 1744951 = 2617427) B2617427
theorem B1744971 : Blo 1744573 1744971 := bstep (se 1 (by rfl) ⟨1308728, by rfl⟩ : syracuseStep 1744971 = 2617457) B2617457
theorem B1744983 : Blo 1744573 1744983 := bstep (se 1 (by rfl) ⟨1308737, by rfl⟩ : syracuseStep 1744983 = 2617475) B2617475
theorem B1745003 : Blo 1744573 1745003 := bstep (se 1 (by rfl) ⟨1308752, by rfl⟩ : syracuseStep 1745003 = 2617505) B2617505
theorem B1745015 : Blo 1744573 1745015 := bstep (se 1 (by rfl) ⟨1308761, by rfl⟩ : syracuseStep 1745015 = 2617523) B2617523
theorem B1745035 : Blo 1744573 1745035 := bstep (se 1 (by rfl) ⟨1308776, by rfl⟩ : syracuseStep 1745035 = 2617553) B2617553
theorem B1745047 : Blo 1744573 1745047 := bstep (se 1 (by rfl) ⟨1308785, by rfl⟩ : syracuseStep 1745047 = 2617571) B2617571
theorem B1745067 : Blo 1744573 1745067 := bstep (se 1 (by rfl) ⟨1308800, by rfl⟩ : syracuseStep 1745067 = 2617601) B2617601
theorem B1745079 : Blo 1744573 1745079 := bstep (se 1 (by rfl) ⟨1308809, by rfl⟩ : syracuseStep 1745079 = 2617619) B2617619
theorem B6627521 : Blo 1744573 6627521 := bstep (se 2 (by rfl) ⟨2485320, by rfl⟩ : syracuseStep 6627521 = 4970641) B4970641
theorem B1745099 : Blo 1744573 1745099 := bstep (se 1 (by rfl) ⟨1308824, by rfl⟩ : syracuseStep 1745099 = 2617649) B2617649
theorem B2097355 : Blo 1744573 2097355 := bstep (se 1 (by rfl) ⟨1573016, by rfl⟩ : syracuseStep 2097355 = 3146033) B3146033
theorem B19873997 : Blo 1744573 19873997 := bstep (se 3 (by rfl) ⟨3726374, by rfl⟩ : syracuseStep 19873997 = 7452749) B7452749
theorem B1745111 : Blo 1744573 1745111 := bstep (se 1 (by rfl) ⟨1308833, by rfl⟩ : syracuseStep 1745111 = 2617667) B2617667
theorem B5890265 : Blo 1744573 5890265 := bstep (se 2 (by rfl) ⟨2208849, by rfl⟩ : syracuseStep 5890265 = 4417699) B4417699
theorem B1745131 : Blo 1744573 1745131 := bstep (se 1 (by rfl) ⟨1308848, by rfl⟩ : syracuseStep 1745131 = 2617697) B2617697
theorem B1745143 : Blo 1744573 1745143 := bstep (se 1 (by rfl) ⟨1308857, by rfl⟩ : syracuseStep 1745143 = 2617715) B2617715
theorem B1745163 : Blo 1744573 1745163 := bstep (se 1 (by rfl) ⟨1308872, by rfl⟩ : syracuseStep 1745163 = 2617745) B2617745
theorem B1745175 : Blo 1744573 1745175 := bstep (se 1 (by rfl) ⟨1308881, by rfl⟩ : syracuseStep 1745175 = 2617763) B2617763
theorem B1745195 : Blo 1744573 1745195 := bstep (se 1 (by rfl) ⟨1308896, by rfl⟩ : syracuseStep 1745195 = 2617793) B2617793
theorem B1745207 : Blo 1744573 1745207 := bstep (se 1 (by rfl) ⟨1308905, by rfl⟩ : syracuseStep 1745207 = 2617811) B2617811
theorem B1745227 : Blo 1744573 1745227 := bstep (se 1 (by rfl) ⟨1308920, by rfl⟩ : syracuseStep 1745227 = 2617841) B2617841
theorem B3727691 : Blo 1744573 3727691 := bstep (se 1 (by rfl) ⟨2795768, by rfl⟩ : syracuseStep 3727691 = 5591537) B5591537
theorem B1745239 : Blo 1744573 1745239 := bstep (se 1 (by rfl) ⟨1308929, by rfl⟩ : syracuseStep 1745239 = 2617859) B2617859
theorem B1745259 : Blo 1744573 1745259 := bstep (se 1 (by rfl) ⟨1308944, by rfl⟩ : syracuseStep 1745259 = 2617889) B2617889
theorem B1745271 : Blo 1744573 1745271 := bstep (se 1 (by rfl) ⟨1308953, by rfl⟩ : syracuseStep 1745271 = 2617907) B2617907
theorem B1745291 : Blo 1744573 1745291 := bstep (se 1 (by rfl) ⟨1308968, by rfl⟩ : syracuseStep 1745291 = 2617937) B2617937
theorem B1745303 : Blo 1744573 1745303 := bstep (se 1 (by rfl) ⟨1308977, by rfl⟩ : syracuseStep 1745303 = 2617955) B2617955
theorem B1745323 : Blo 1744573 1745323 := bstep (se 1 (by rfl) ⟨1308992, by rfl⟩ : syracuseStep 1745323 = 2617985) B2617985
theorem B1745335 : Blo 1744573 1745335 := bstep (se 1 (by rfl) ⟨1309001, by rfl⟩ : syracuseStep 1745335 = 2618003) B2618003
theorem B4252097 : Blo 1744573 4252097 := bstep (se 2 (by rfl) ⟨1594536, by rfl⟩ : syracuseStep 4252097 = 3189073) B3189073
theorem B3146177 : Blo 1744573 3146177 := bstep (se 2 (by rfl) ⟨1179816, by rfl⟩ : syracuseStep 3146177 = 2359633) B2359633
theorem B1745355 : Blo 1744573 1745355 := bstep (se 1 (by rfl) ⟨1309016, by rfl⟩ : syracuseStep 1745355 = 2618033) B2618033
theorem B1745367 : Blo 1744573 1745367 := bstep (se 1 (by rfl) ⟨1309025, by rfl⟩ : syracuseStep 1745367 = 2618051) B2618051
theorem B1745387 : Blo 1744573 1745387 := bstep (se 1 (by rfl) ⟨1309040, by rfl⟩ : syracuseStep 1745387 = 2618081) B2618081
theorem B1745399 : Blo 1744573 1745399 := bstep (se 1 (by rfl) ⟨1309049, by rfl⟩ : syracuseStep 1745399 = 2618099) B2618099
theorem B7963139 : Blo 1744573 7963139 := bstep (se 1 (by rfl) ⟨5972354, by rfl⟩ : syracuseStep 7963139 = 11944709) B11944709
theorem B1745419 : Blo 1744573 1745419 := bstep (se 1 (by rfl) ⟨1309064, by rfl⟩ : syracuseStep 1745419 = 2618129) B2618129
theorem B24199697 : Blo 1744573 24199697 := bstep (se 2 (by rfl) ⟨9074886, by rfl⟩ : syracuseStep 24199697 = 18149773) B18149773
theorem B1745431 : Blo 1744573 1745431 := bstep (se 1 (by rfl) ⟨1309073, by rfl⟩ : syracuseStep 1745431 = 2618147) B2618147
theorem B1745451 : Blo 1744573 1745451 := bstep (se 1 (by rfl) ⟨1309088, by rfl⟩ : syracuseStep 1745451 = 2618177) B2618177
theorem B1745463 : Blo 1744573 1745463 := bstep (se 1 (by rfl) ⟨1309097, by rfl⟩ : syracuseStep 1745463 = 2618195) B2618195
theorem B1745483 : Blo 1744573 1745483 := bstep (se 1 (by rfl) ⟨1309112, by rfl⟩ : syracuseStep 1745483 = 2618225) B2618225
theorem B1745495 : Blo 1744573 1745495 := bstep (se 1 (by rfl) ⟨1309121, by rfl⟩ : syracuseStep 1745495 = 2618243) B2618243
theorem B1745515 : Blo 1744573 1745515 := bstep (se 1 (by rfl) ⟨1309136, by rfl⟩ : syracuseStep 1745515 = 2618273) B2618273
theorem B1745527 : Blo 1744573 1745527 := bstep (se 1 (by rfl) ⟨1309145, by rfl⟩ : syracuseStep 1745527 = 2618291) B2618291
theorem B1745547 : Blo 1744573 1745547 := bstep (se 1 (by rfl) ⟨1309160, by rfl⟩ : syracuseStep 1745547 = 2618321) B2618321
theorem B1745559 : Blo 1744573 1745559 := bstep (se 1 (by rfl) ⟨1309169, by rfl⟩ : syracuseStep 1745559 = 2618339) B2618339
theorem B3146393 : Blo 1744573 3146393 := bstep (se 2 (by rfl) ⟨1179897, by rfl⟩ : syracuseStep 3146393 = 2359795) B2359795
theorem B1745579 : Blo 1744573 1745579 := bstep (se 1 (by rfl) ⟨1309184, by rfl⟩ : syracuseStep 1745579 = 2618369) B2618369
theorem B1745591 : Blo 1744573 1745591 := bstep (se 1 (by rfl) ⟨1309193, by rfl⟩ : syracuseStep 1745591 = 2618387) B2618387
theorem B1745611 : Blo 1744573 1745611 := bstep (se 1 (by rfl) ⟨1309208, by rfl⟩ : syracuseStep 1745611 = 2618417) B2618417
theorem B4719307 : Blo 1744573 4719307 := bstep (se 1 (by rfl) ⟨3539480, by rfl⟩ : syracuseStep 4719307 = 7078961) B7078961
theorem B1745623 : Blo 1744573 1745623 := bstep (se 1 (by rfl) ⟨1309217, by rfl⟩ : syracuseStep 1745623 = 2618435) B2618435
theorem B1745643 : Blo 1744573 1745643 := bstep (se 1 (by rfl) ⟨1309232, by rfl⟩ : syracuseStep 1745643 = 2618465) B2618465
theorem B1745655 : Blo 1744573 1745655 := bstep (se 1 (by rfl) ⟨1309241, by rfl⟩ : syracuseStep 1745655 = 2618483) B2618483
theorem B1745675 : Blo 1744573 1745675 := bstep (se 1 (by rfl) ⟨1309256, by rfl⟩ : syracuseStep 1745675 = 2618513) B2618513
theorem B14918417 : Blo 1744573 14918417 := bstep (se 2 (by rfl) ⟨5594406, by rfl⟩ : syracuseStep 14918417 = 11188813) B11188813
theorem B1745687 : Blo 1744573 1745687 := bstep (se 1 (by rfl) ⟨1309265, by rfl⟩ : syracuseStep 1745687 = 2618531) B2618531
theorem B1745707 : Blo 1744573 1745707 := bstep (se 1 (by rfl) ⟨1309280, by rfl⟩ : syracuseStep 1745707 = 2618561) B2618561
theorem B1745719 : Blo 1744573 1745719 := bstep (se 1 (by rfl) ⟨1309289, by rfl⟩ : syracuseStep 1745719 = 2618579) B2618579
theorem B1745739 : Blo 1744573 1745739 := bstep (se 1 (by rfl) ⟨1309304, by rfl⟩ : syracuseStep 1745739 = 2618609) B2618609
theorem B1745751 : Blo 1744573 1745751 := bstep (se 1 (by rfl) ⟨1309313, by rfl⟩ : syracuseStep 1745751 = 2618627) B2618627
theorem B6628189 : Blo 1744573 6628189 := bstep (se 3 (by rfl) ⟨1242785, by rfl⟩ : syracuseStep 6628189 = 2485571) B2485571
theorem B43623269 : Blo 1744573 43623269 := bstep (se 4 (by rfl) ⟨4089681, by rfl⟩ : syracuseStep 43623269 = 8179363) B8179363
theorem B1745771 : Blo 1744573 1745771 := bstep (se 1 (by rfl) ⟨1309328, by rfl⟩ : syracuseStep 1745771 = 2618657) B2618657
theorem B1745783 : Blo 1744573 1745783 := bstep (se 1 (by rfl) ⟨1309337, by rfl⟩ : syracuseStep 1745783 = 2618675) B2618675
theorem B1745803 : Blo 1744573 1745803 := bstep (se 1 (by rfl) ⟨1309352, by rfl⟩ : syracuseStep 1745803 = 2618705) B2618705
theorem B5890967 : Blo 1744573 5890967 := bstep (se 1 (by rfl) ⟨4418225, by rfl⟩ : syracuseStep 5890967 = 8836451) B8836451
theorem B1745815 : Blo 1744573 1745815 := bstep (se 1 (by rfl) ⟨1309361, by rfl⟩ : syracuseStep 1745815 = 2618723) B2618723
theorem B3728281 : Blo 1744573 3728281 := bstep (se 2 (by rfl) ⟨1398105, by rfl⟩ : syracuseStep 3728281 = 2796211) B2796211
theorem B1745835 : Blo 1744573 1745835 := bstep (se 1 (by rfl) ⟨1309376, by rfl⟩ : syracuseStep 1745835 = 2618753) B2618753
theorem B1745847 : Blo 1744573 1745847 := bstep (se 1 (by rfl) ⟨1309385, by rfl⟩ : syracuseStep 1745847 = 2618771) B2618771
theorem B1745867 : Blo 1744573 1745867 := bstep (se 1 (by rfl) ⟨1309400, by rfl⟩ : syracuseStep 1745867 = 2618801) B2618801
theorem B1745879 : Blo 1744573 1745879 := bstep (se 1 (by rfl) ⟨1309409, by rfl⟩ : syracuseStep 1745879 = 2618819) B2618819
theorem B1745899 : Blo 1744573 1745899 := bstep (se 1 (by rfl) ⟨1309424, by rfl⟩ : syracuseStep 1745899 = 2618849) B2618849
theorem B1745911 : Blo 1744573 1745911 := bstep (se 1 (by rfl) ⟨1309433, by rfl⟩ : syracuseStep 1745911 = 2618867) B2618867
theorem B1745931 : Blo 1744573 1745931 := bstep (se 1 (by rfl) ⟨1309448, by rfl⟩ : syracuseStep 1745931 = 2618897) B2618897
theorem B1745943 : Blo 1744573 1745943 := bstep (se 1 (by rfl) ⟨1309457, by rfl⟩ : syracuseStep 1745943 = 2618915) B2618915
theorem B25150499 : Blo 1744573 25150499 := bstep (se 1 (by rfl) ⟨18862874, by rfl⟩ : syracuseStep 25150499 = 37725749) B37725749
theorem B1745963 : Blo 1744573 1745963 := bstep (se 1 (by rfl) ⟨1309472, by rfl⟩ : syracuseStep 1745963 = 2618945) B2618945
theorem B1745975 : Blo 1744573 1745975 := bstep (se 1 (by rfl) ⟨1309481, by rfl⟩ : syracuseStep 1745975 = 2618963) B2618963
theorem B2794571 : Blo 1744573 2794571 := bstep (se 1 (by rfl) ⟨2095928, by rfl⟩ : syracuseStep 2794571 = 4191857) B4191857
theorem B1745995 : Blo 1744573 1745995 := bstep (se 1 (by rfl) ⟨1309496, by rfl⟩ : syracuseStep 1745995 = 2618993) B2618993
theorem B1746007 : Blo 1744573 1746007 := bstep (se 1 (by rfl) ⟨1309505, by rfl⟩ : syracuseStep 1746007 = 2619011) B2619011
theorem B1746027 : Blo 1744573 1746027 := bstep (se 1 (by rfl) ⟨1309520, by rfl⟩ : syracuseStep 1746027 = 2619041) B2619041
theorem B1746039 : Blo 1744573 1746039 := bstep (se 1 (by rfl) ⟨1309529, by rfl⟩ : syracuseStep 1746039 = 2619059) B2619059
theorem B1746059 : Blo 1744573 1746059 := bstep (se 1 (by rfl) ⟨1309544, by rfl⟩ : syracuseStep 1746059 = 2619089) B2619089
theorem B1746071 : Blo 1744573 1746071 := bstep (se 1 (by rfl) ⟨1309553, by rfl⟩ : syracuseStep 1746071 = 2619107) B2619107
theorem B1746091 : Blo 1744573 1746091 := bstep (se 1 (by rfl) ⟨1309568, by rfl⟩ : syracuseStep 1746091 = 2619137) B2619137
theorem B1746103 : Blo 1744573 1746103 := bstep (se 1 (by rfl) ⟨1309577, by rfl⟩ : syracuseStep 1746103 = 2619155) B2619155
theorem B6292673 : Blo 1744573 6292673 := bstep (se 2 (by rfl) ⟨2359752, by rfl⟩ : syracuseStep 6292673 = 4719505) B4719505
theorem B1746123 : Blo 1744573 1746123 := bstep (se 1 (by rfl) ⟨1309592, by rfl⟩ : syracuseStep 1746123 = 2619185) B2619185
theorem B1746135 : Blo 1744573 1746135 := bstep (se 1 (by rfl) ⟨1309601, by rfl⟩ : syracuseStep 1746135 = 2619203) B2619203
theorem B1746155 : Blo 1744573 1746155 := bstep (se 1 (by rfl) ⟨1309616, by rfl⟩ : syracuseStep 1746155 = 2619233) B2619233
theorem B1746167 : Blo 1744573 1746167 := bstep (se 1 (by rfl) ⟨1309625, by rfl⟩ : syracuseStep 1746167 = 2619251) B2619251
theorem B1746187 : Blo 1744573 1746187 := bstep (se 1 (by rfl) ⟨1309640, by rfl⟩ : syracuseStep 1746187 = 2619281) B2619281
theorem B9946385 : Blo 1744573 9946385 := bstep (se 2 (by rfl) ⟨3729894, by rfl⟩ : syracuseStep 9946385 = 7459789) B7459789
theorem B1746199 : Blo 1744573 1746199 := bstep (se 1 (by rfl) ⟨1309649, by rfl⟩ : syracuseStep 1746199 = 2619299) B2619299
theorem B1746219 : Blo 1744573 1746219 := bstep (se 1 (by rfl) ⟨1309664, by rfl⟩ : syracuseStep 1746219 = 2619329) B2619329
theorem B1746231 : Blo 1744573 1746231 := bstep (se 1 (by rfl) ⟨1309673, by rfl⟩ : syracuseStep 1746231 = 2619347) B2619347
theorem B3925313 : Blo 1744573 3925313 := bstep (se 2 (by rfl) ⟨1471992, by rfl⟩ : syracuseStep 3925313 = 2943985) B2943985
theorem B1746251 : Blo 1744573 1746251 := bstep (se 1 (by rfl) ⟨1309688, by rfl⟩ : syracuseStep 1746251 = 2619377) B2619377
theorem B1746263 : Blo 1744573 1746263 := bstep (se 1 (by rfl) ⟨1309697, by rfl⟩ : syracuseStep 1746263 = 2619395) B2619395
theorem B1746283 : Blo 1744573 1746283 := bstep (se 1 (by rfl) ⟨1309712, by rfl⟩ : syracuseStep 1746283 = 2619425) B2619425
theorem B1746295 : Blo 1744573 1746295 := bstep (se 1 (by rfl) ⟨1309721, by rfl⟩ : syracuseStep 1746295 = 2619443) B2619443
theorem B1746315 : Blo 1744573 1746315 := bstep (se 1 (by rfl) ⟨1309736, by rfl⟩ : syracuseStep 1746315 = 2619473) B2619473
theorem B64603541 : Blo 1744573 64603541 := bstep (se 6 (by rfl) ⟨1514145, by rfl⟩ : syracuseStep 64603541 = 3028291) B3028291
theorem B7456151 : Blo 1744573 7456151 := bstep (se 1 (by rfl) ⟨5592113, by rfl⟩ : syracuseStep 7456151 = 11184227) B11184227
theorem B1746327 : Blo 1744573 1746327 := bstep (se 1 (by rfl) ⟨1309745, by rfl⟩ : syracuseStep 1746327 = 2619491) B2619491
theorem B1746347 : Blo 1744573 1746347 := bstep (se 1 (by rfl) ⟨1309760, by rfl⟩ : syracuseStep 1746347 = 2619521) B2619521
theorem B5891507 : Blo 1744573 5891507 := bstep (se 1 (by rfl) ⟨4418630, by rfl⟩ : syracuseStep 5891507 = 8837261) B8837261
theorem B1746359 : Blo 1744573 1746359 := bstep (se 1 (by rfl) ⟨1309769, by rfl⟩ : syracuseStep 1746359 = 2619539) B2619539
theorem B217933253 : Blo 1744573 217933253 := bstep (se 4 (by rfl) ⟨20431242, by rfl⟩ : syracuseStep 217933253 = 40862485) B40862485
theorem B1746379 : Blo 1744573 1746379 := bstep (se 1 (by rfl) ⟨1309784, by rfl⟩ : syracuseStep 1746379 = 2619569) B2619569
theorem B1746391 : Blo 1744573 1746391 := bstep (se 1 (by rfl) ⟨1309793, by rfl⟩ : syracuseStep 1746391 = 2619587) B2619587
theorem B8955353 : Blo 1744573 8955353 := bstep (se 2 (by rfl) ⟨3358257, by rfl⟩ : syracuseStep 8955353 = 6716515) B6716515
theorem B1746411 : Blo 1744573 1746411 := bstep (se 1 (by rfl) ⟨1309808, by rfl⟩ : syracuseStep 1746411 = 2619617) B2619617
theorem B1746423 : Blo 1744573 1746423 := bstep (se 1 (by rfl) ⟨1309817, by rfl⟩ : syracuseStep 1746423 = 2619635) B2619635
theorem B1746443 : Blo 1744573 1746443 := bstep (se 1 (by rfl) ⟨1309832, by rfl⟩ : syracuseStep 1746443 = 2619665) B2619665
theorem B1746455 : Blo 1744573 1746455 := bstep (se 1 (by rfl) ⟨1309841, by rfl⟩ : syracuseStep 1746455 = 2619683) B2619683
theorem B3925529 : Blo 1744573 3925529 := bstep (se 2 (by rfl) ⟨1472073, by rfl⟩ : syracuseStep 3925529 = 2944147) B2944147
theorem B1746475 : Blo 1744573 1746475 := bstep (se 1 (by rfl) ⟨1309856, by rfl⟩ : syracuseStep 1746475 = 2619713) B2619713
theorem B1746487 : Blo 1744573 1746487 := bstep (se 1 (by rfl) ⟨1309865, by rfl⟩ : syracuseStep 1746487 = 2619731) B2619731
theorem B28296773 : Blo 1744573 28296773 := bstep (se 4 (by rfl) ⟨2652822, by rfl⟩ : syracuseStep 28296773 = 5305645) B5305645
theorem B1746507 : Blo 1744573 1746507 := bstep (se 1 (by rfl) ⟨1309880, by rfl⟩ : syracuseStep 1746507 = 2619761) B2619761
theorem B1746519 : Blo 1744573 1746519 := bstep (se 1 (by rfl) ⟨1309889, by rfl⟩ : syracuseStep 1746519 = 2619779) B2619779
theorem B1746539 : Blo 1744573 1746539 := bstep (se 1 (by rfl) ⟨1309904, by rfl⟩ : syracuseStep 1746539 = 2619809) B2619809
theorem B3925619 : Blo 1744573 3925619 := bstep (se 1 (by rfl) ⟨2944214, by rfl⟩ : syracuseStep 3925619 = 5888429) B5888429
theorem B1746551 : Blo 1744573 1746551 := bstep (se 1 (by rfl) ⟨1309913, by rfl⟩ : syracuseStep 1746551 = 2619827) B2619827
theorem B1746571 : Blo 1744573 1746571 := bstep (se 1 (by rfl) ⟨1309928, by rfl⟩ : syracuseStep 1746571 = 2619857) B2619857
theorem B3925655 : Blo 1744573 3925655 := bstep (se 1 (by rfl) ⟨2944241, by rfl⟩ : syracuseStep 3925655 = 5888483) B5888483
theorem B5891777 : Blo 1744573 5891777 := bstep (se 2 (by rfl) ⟨2209416, by rfl⟩ : syracuseStep 5891777 = 4418833) B4418833
theorem B3925835 : Blo 1744573 3925835 := bstep (se 1 (by rfl) ⟨2944376, by rfl⟩ : syracuseStep 3925835 = 5888753) B5888753
theorem B4417355 : Blo 1744573 4417355 := bstep (se 1 (by rfl) ⟨3313016, by rfl⟩ : syracuseStep 4417355 = 6626033) B6626033
theorem B3925889 : Blo 1744573 3925889 := bstep (se 2 (by rfl) ⟨1472208, by rfl⟩ : syracuseStep 3925889 = 2944417) B2944417
theorem B16770995 : Blo 1744573 16770995 := bstep (se 1 (by rfl) ⟨12578246, by rfl⟩ : syracuseStep 16770995 = 25156493) B25156493
theorem B3729331 : Blo 1744573 3729331 := bstep (se 1 (by rfl) ⟨2796998, by rfl⟩ : syracuseStep 3729331 = 5593997) B5593997
theorem B7079987 : Blo 1744573 7079987 := bstep (se 1 (by rfl) ⟨5309990, by rfl⟩ : syracuseStep 7079987 = 10619981) B10619981
theorem B4720691 : Blo 1744573 4720691 := bstep (se 1 (by rfl) ⟨3540518, by rfl⟩ : syracuseStep 4720691 = 7081037) B7081037
theorem B9439307 : Blo 1744573 9439307 := bstep (se 1 (by rfl) ⟨7079480, by rfl⟩ : syracuseStep 9439307 = 14158961) B14158961
theorem B3926105 : Blo 1744573 3926105 := bstep (se 2 (by rfl) ⟨1472289, by rfl⟩ : syracuseStep 3926105 = 2944579) B2944579
theorem B6629465 : Blo 1744573 6629465 := bstep (se 2 (by rfl) ⟨2486049, by rfl⟩ : syracuseStep 6629465 = 4972099) B4972099
theorem B9939095 : Blo 1744573 9939095 := bstep (se 1 (by rfl) ⟨7454321, by rfl⟩ : syracuseStep 9939095 = 14908643) B14908643
theorem B3926195 : Blo 1744573 3926195 := bstep (se 1 (by rfl) ⟨2944646, by rfl⟩ : syracuseStep 3926195 = 5889293) B5889293
theorem B2484427 : Blo 1744573 2484427 := bstep (se 1 (by rfl) ⟨1863320, by rfl⟩ : syracuseStep 2484427 = 3726641) B3726641
theorem B3926231 : Blo 1744573 3926231 := bstep (se 1 (by rfl) ⟨2944673, by rfl⟩ : syracuseStep 3926231 = 5889347) B5889347
theorem B14149849 : Blo 1744573 14149849 := bstep (se 2 (by rfl) ⟨5306193, by rfl⟩ : syracuseStep 14149849 = 10612387) B10612387
theorem B5892317 : Blo 1744573 5892317 := bstep (se 3 (by rfl) ⟨1104809, by rfl⟩ : syracuseStep 5892317 = 2209619) B2209619
theorem B8833373 : Blo 1744573 8833373 := bstep (se 3 (by rfl) ⟨1656257, by rfl⟩ : syracuseStep 8833373 = 3312515) B3312515
theorem B3926411 : Blo 1744573 3926411 := bstep (se 1 (by rfl) ⟨2944808, by rfl⟩ : syracuseStep 3926411 = 5889617) B5889617
theorem B7375283 : Blo 1744573 7375283 := bstep (se 1 (by rfl) ⟨5531462, by rfl⟩ : syracuseStep 7375283 = 11062925) B11062925
theorem B3926465 : Blo 1744573 3926465 := bstep (se 2 (by rfl) ⟨1472424, by rfl⟩ : syracuseStep 3926465 = 2944849) B2944849
theorem B3926681 : Blo 1744573 3926681 := bstep (se 2 (by rfl) ⟨1472505, by rfl⟩ : syracuseStep 3926681 = 2945011) B2945011
theorem B3926771 : Blo 1744573 3926771 := bstep (se 1 (by rfl) ⟨2945078, by rfl⟩ : syracuseStep 3926771 = 5890157) B5890157
theorem B3926807 : Blo 1744573 3926807 := bstep (se 1 (by rfl) ⟨2945105, by rfl⟩ : syracuseStep 3926807 = 5890211) B5890211
theorem B3312409 : Blo 1744573 3312409 := bstep (se 2 (by rfl) ⟨1242153, by rfl⟩ : syracuseStep 3312409 = 2484307) B2484307
theorem B4418327 : Blo 1744573 4418327 := bstep (se 1 (by rfl) ⟨3313745, by rfl⟩ : syracuseStep 4418327 = 6627491) B6627491
theorem B3926987 : Blo 1744573 3926987 := bstep (se 1 (by rfl) ⟨2945240, by rfl⟩ : syracuseStep 3926987 = 5890481) B5890481
theorem B14904269 : Blo 1744573 14904269 := bstep (se 3 (by rfl) ⟨2794550, by rfl⟩ : syracuseStep 14904269 = 5589101) B5589101
theorem B3927041 : Blo 1744573 3927041 := bstep (se 2 (by rfl) ⟨1472640, by rfl⟩ : syracuseStep 3927041 = 2945281) B2945281
theorem B20163619 : Blo 1744573 20163619 := bstep (se 1 (by rfl) ⟨15122714, by rfl⟩ : syracuseStep 20163619 = 30245429) B30245429
theorem B8391725 : Blo 1744573 8391725 := bstep (se 3 (by rfl) ⟨1573448, by rfl⟩ : syracuseStep 8391725 = 3146897) B3146897
theorem B6720577 : Blo 1744573 6720577 := bstep (se 2 (by rfl) ⟨2520216, by rfl⟩ : syracuseStep 6720577 = 5040433) B5040433
theorem B28314805 : Blo 1744573 28314805 := bstep (se 5 (by rfl) ⟨1327256, by rfl⟩ : syracuseStep 28314805 = 2654513) B2654513
theorem B3927257 : Blo 1744573 3927257 := bstep (se 2 (by rfl) ⟨1472721, by rfl⟩ : syracuseStep 3927257 = 2945443) B2945443
theorem B7458065 : Blo 1744573 7458065 := bstep (se 2 (by rfl) ⟨2796774, by rfl⟩ : syracuseStep 7458065 = 5593549) B5593549
theorem B3927347 : Blo 1744573 3927347 := bstep (se 1 (by rfl) ⟨2945510, by rfl⟩ : syracuseStep 3927347 = 5891021) B5891021
theorem B3312971 : Blo 1744573 3312971 := bstep (se 1 (by rfl) ⟨2484728, by rfl⟩ : syracuseStep 3312971 = 4969457) B4969457
theorem B5893451 : Blo 1744573 5893451 := bstep (se 1 (by rfl) ⟨4420088, by rfl⟩ : syracuseStep 5893451 = 8840177) B8840177
theorem B2944343 : Blo 1744573 2944343 := bstep (se 1 (by rfl) ⟨2208257, by rfl⟩ : syracuseStep 2944343 = 4416515) B4416515
theorem B3927383 : Blo 1744573 3927383 := bstep (se 1 (by rfl) ⟨2945537, by rfl⟩ : syracuseStep 3927383 = 5891075) B5891075
theorem B2485657 : Blo 1744573 2485657 := bstep (se 2 (by rfl) ⟨932121, by rfl⟩ : syracuseStep 2485657 = 1864243) B1864243
theorem B4418995 : Blo 1744573 4418995 := bstep (se 1 (by rfl) ⟨3314246, by rfl⟩ : syracuseStep 4418995 = 6628493) B6628493
theorem B2944471 : Blo 1744573 2944471 := bstep (se 1 (by rfl) ⟨2208353, by rfl⟩ : syracuseStep 2944471 = 4416707) B4416707
theorem B3313153 : Blo 1744573 3313153 := bstep (se 2 (by rfl) ⟨1242432, by rfl⟩ : syracuseStep 3313153 = 2484865) B2484865
theorem B3927563 : Blo 1744573 3927563 := bstep (se 1 (by rfl) ⟨2945672, by rfl⟩ : syracuseStep 3927563 = 5891345) B5891345
theorem B3927617 : Blo 1744573 3927617 := bstep (se 2 (by rfl) ⟨1472856, by rfl⟩ : syracuseStep 3927617 = 2945713) B2945713
theorem B4419137 : Blo 1744573 4419137 := bstep (se 2 (by rfl) ⟨1657176, by rfl⟩ : syracuseStep 4419137 = 3314353) B3314353
theorem B5893721 : Blo 1744573 5893721 := bstep (se 2 (by rfl) ⟨2210145, by rfl⟩ : syracuseStep 5893721 = 4420291) B4420291
theorem B19885661 : Blo 1744573 19885661 := bstep (se 3 (by rfl) ⟨3728561, by rfl⟩ : syracuseStep 19885661 = 7457123) B7457123
theorem B2616971 : Blo 1744573 2616971 := bstep (se 1 (by rfl) ⟨1962728, by rfl⟩ : syracuseStep 2616971 = 3925457) B3925457
theorem B1863307 : Blo 1744573 1863307 := bstep (se 1 (by rfl) ⟨1397480, by rfl⟩ : syracuseStep 1863307 = 2794961) B2794961
theorem B2616983 : Blo 1744573 2616983 := bstep (se 1 (by rfl) ⟨1962737, by rfl⟩ : syracuseStep 2616983 = 3925475) B3925475
theorem B22376087 : Blo 1744573 22376087 := bstep (se 1 (by rfl) ⟨16782065, by rfl⟩ : syracuseStep 22376087 = 33564131) B33564131
theorem B6631091 : Blo 1744573 6631091 := bstep (se 1 (by rfl) ⟨4973318, by rfl⟩ : syracuseStep 6631091 = 9946637) B9946637
theorem B7966387 : Blo 1744573 7966387 := bstep (se 1 (by rfl) ⟨5974790, by rfl⟩ : syracuseStep 7966387 = 11949581) B11949581
theorem B6631105 : Blo 1744573 6631105 := bstep (se 2 (by rfl) ⟨2486664, by rfl⟩ : syracuseStep 6631105 = 4973329) B4973329
theorem B2617049 : Blo 1744573 2617049 := bstep (se 2 (by rfl) ⟨981393, by rfl⟩ : syracuseStep 2617049 = 1962787) B1962787
theorem B3927833 : Blo 1744573 3927833 := bstep (se 2 (by rfl) ⟨1472937, by rfl⟩ : syracuseStep 3927833 = 2945875) B2945875
theorem B2617163 : Blo 1744573 2617163 := bstep (se 1 (by rfl) ⟨1962872, by rfl⟩ : syracuseStep 2617163 = 3925745) B3925745
theorem B2617175 : Blo 1744573 2617175 := bstep (se 1 (by rfl) ⟨1962881, by rfl⟩ : syracuseStep 2617175 = 3925763) B3925763
theorem B3927923 : Blo 1744573 3927923 := bstep (se 1 (by rfl) ⟨2945942, by rfl⟩ : syracuseStep 3927923 = 5891885) B5891885
theorem B3927959 : Blo 1744573 3927959 := bstep (se 1 (by rfl) ⟨2945969, by rfl⟩ : syracuseStep 3927959 = 5891939) B5891939
theorem B2617241 : Blo 1744573 2617241 := bstep (se 2 (by rfl) ⟨981465, by rfl⟩ : syracuseStep 2617241 = 1962931) B1962931
theorem B4476865 : Blo 1744573 4476865 := bstep (se 2 (by rfl) ⟨1678824, by rfl⟩ : syracuseStep 4476865 = 3357649) B3357649
theorem B2617355 : Blo 1744573 2617355 := bstep (se 1 (by rfl) ⟨1963016, by rfl⟩ : syracuseStep 2617355 = 3926033) B3926033
theorem B2617367 : Blo 1744573 2617367 := bstep (se 1 (by rfl) ⟨1963025, by rfl⟩ : syracuseStep 2617367 = 3926051) B3926051
theorem B2945099 : Blo 1744573 2945099 := bstep (se 1 (by rfl) ⟨2208824, by rfl⟩ : syracuseStep 2945099 = 4417649) B4417649
theorem B3928139 : Blo 1744573 3928139 := bstep (se 1 (by rfl) ⟨2946104, by rfl⟩ : syracuseStep 3928139 = 5892209) B5892209
theorem B2617433 : Blo 1744573 2617433 := bstep (se 2 (by rfl) ⟨981537, by rfl⟩ : syracuseStep 2617433 = 1963075) B1963075
theorem B3928193 : Blo 1744573 3928193 := bstep (se 2 (by rfl) ⟨1473072, by rfl⟩ : syracuseStep 3928193 = 2946145) B2946145
theorem B25170101 : Blo 1744573 25170101 := bstep (se 5 (by rfl) ⟨1179848, by rfl⟩ : syracuseStep 25170101 = 2359697) B2359697
theorem B2617547 : Blo 1744573 2617547 := bstep (se 1 (by rfl) ⟨1963160, by rfl⟩ : syracuseStep 2617547 = 3926321) B3926321
theorem B2945227 : Blo 1744573 2945227 := bstep (se 1 (by rfl) ⟨2208920, by rfl⟩ : syracuseStep 2945227 = 4417841) B4417841
theorem B3313867 : Blo 1744573 3313867 := bstep (se 1 (by rfl) ⟨2485400, by rfl⟩ : syracuseStep 3313867 = 4970801) B4970801
theorem B2617559 : Blo 1744573 2617559 := bstep (se 1 (by rfl) ⟨1963169, by rfl⟩ : syracuseStep 2617559 = 3926339) B3926339
theorem B7459037 : Blo 1744573 7459037 := bstep (se 3 (by rfl) ⟨1398569, by rfl⟩ : syracuseStep 7459037 = 2797139) B2797139
theorem B3313943 : Blo 1744573 3313943 := bstep (se 1 (by rfl) ⟨2485457, by rfl⟩ : syracuseStep 3313943 = 4970915) B4970915
theorem B2486551 : Blo 1744573 2486551 := bstep (se 1 (by rfl) ⟨1864913, by rfl⟩ : syracuseStep 2486551 = 3729827) B3729827
theorem B2617625 : Blo 1744573 2617625 := bstep (se 2 (by rfl) ⟨981609, by rfl⟩ : syracuseStep 2617625 = 1963219) B1963219
theorem B5894423 : Blo 1744573 5894423 := bstep (se 1 (by rfl) ⟨4420817, by rfl⟩ : syracuseStep 5894423 = 8841635) B8841635
theorem B2945369 : Blo 1744573 2945369 := bstep (se 2 (by rfl) ⟨1104513, by rfl⟩ : syracuseStep 2945369 = 2209027) B2209027
theorem B3928409 : Blo 1744573 3928409 := bstep (se 2 (by rfl) ⟨1473153, by rfl⟩ : syracuseStep 3928409 = 2946307) B2946307
theorem B2617739 : Blo 1744573 2617739 := bstep (se 1 (by rfl) ⟨1963304, by rfl⟩ : syracuseStep 2617739 = 3926609) B3926609
theorem B2208151 : Blo 1744573 2208151 := bstep (se 1 (by rfl) ⟨1656113, by rfl⟩ : syracuseStep 2208151 = 3312227) B3312227
theorem B2617751 : Blo 1744573 2617751 := bstep (se 1 (by rfl) ⟨1963313, by rfl⟩ : syracuseStep 2617751 = 3926627) B3926627
theorem B8835479 : Blo 1744573 8835479 := bstep (se 1 (by rfl) ⟨6626609, by rfl⟩ : syracuseStep 8835479 = 13253219) B13253219
theorem B3928499 : Blo 1744573 3928499 := bstep (se 1 (by rfl) ⟨2946374, by rfl⟩ : syracuseStep 3928499 = 5892749) B5892749
theorem B10621363 : Blo 1744573 10621363 := bstep (se 1 (by rfl) ⟨7966022, by rfl⟩ : syracuseStep 10621363 = 15932045) B15932045
theorem B3928535 : Blo 1744573 3928535 := bstep (se 1 (by rfl) ⟨2946401, by rfl⟩ : syracuseStep 3928535 = 5892803) B5892803
theorem B2617817 : Blo 1744573 2617817 := bstep (se 2 (by rfl) ⟨981681, by rfl⟩ : syracuseStep 2617817 = 1963363) B1963363
theorem B2945497 : Blo 1744573 2945497 := bstep (se 2 (by rfl) ⟨1104561, by rfl⟩ : syracuseStep 2945497 = 2209123) B2209123
theorem B2617931 : Blo 1744573 2617931 := bstep (se 1 (by rfl) ⟨1963448, by rfl⟩ : syracuseStep 2617931 = 3926897) B3926897
theorem B2617943 : Blo 1744573 2617943 := bstep (se 1 (by rfl) ⟨1963457, by rfl⟩ : syracuseStep 2617943 = 3926915) B3926915
theorem B3928715 : Blo 1744573 3928715 := bstep (se 1 (by rfl) ⟨2946536, by rfl⟩ : syracuseStep 3928715 = 5893073) B5893073
theorem B2618009 : Blo 1744573 2618009 := bstep (se 2 (by rfl) ⟨981753, by rfl⟩ : syracuseStep 2618009 = 1963507) B1963507
theorem B1962679 : Blo 1744573 1962679 := bstep (se 1 (by rfl) ⟨1472009, by rfl⟩ : syracuseStep 1962679 = 2944019) B2944019
theorem B3928769 : Blo 1744573 3928769 := bstep (se 2 (by rfl) ⟨1473288, by rfl⟩ : syracuseStep 3928769 = 2946577) B2946577
theorem B6288131 : Blo 1744573 6288131 := bstep (se 1 (by rfl) ⟨4716098, by rfl⟩ : syracuseStep 6288131 = 9432197) B9432197
theorem B2618123 : Blo 1744573 2618123 := bstep (se 1 (by rfl) ⟨1963592, by rfl⟩ : syracuseStep 2618123 = 3927185) B3927185
theorem B13259537 : Blo 1744573 13259537 := bstep (se 2 (by rfl) ⟨4972326, by rfl⟩ : syracuseStep 13259537 = 9944653) B9944653
theorem B2618135 : Blo 1744573 2618135 := bstep (se 1 (by rfl) ⟨1963601, by rfl⟩ : syracuseStep 2618135 = 3927203) B3927203
theorem B4420403 : Blo 1744573 4420403 := bstep (se 1 (by rfl) ⟨3315302, by rfl⟩ : syracuseStep 4420403 = 6630605) B6630605
theorem B7762763 : Blo 1744573 7762763 := bstep (se 1 (by rfl) ⟨5822072, by rfl⟩ : syracuseStep 7762763 = 11644145) B11644145
theorem B6624089 : Blo 1744573 6624089 := bstep (se 2 (by rfl) ⟨2484033, by rfl⟩ : syracuseStep 6624089 = 4968067) B4968067
theorem B2618201 : Blo 1744573 2618201 := bstep (se 2 (by rfl) ⟨981825, by rfl⟩ : syracuseStep 2618201 = 1963651) B1963651
theorem B4969309 : Blo 1744573 4969309 := bstep (se 3 (by rfl) ⟨931745, by rfl⟩ : syracuseStep 4969309 = 1863491) B1863491
theorem B1962859 : Blo 1744573 1962859 := bstep (se 1 (by rfl) ⟨1472144, by rfl⟩ : syracuseStep 1962859 = 2944289) B2944289
theorem B7558033 : Blo 1744573 7558033 := bstep (se 2 (by rfl) ⟨2834262, by rfl⟩ : syracuseStep 7558033 = 5668525) B5668525
theorem B3928985 : Blo 1744573 3928985 := bstep (se 2 (by rfl) ⟨1473369, by rfl⟩ : syracuseStep 3928985 = 2946739) B2946739
theorem B3314611 : Blo 1744573 3314611 := bstep (se 1 (by rfl) ⟨2485958, by rfl⟩ : syracuseStep 3314611 = 4971917) B4971917
theorem B2618315 : Blo 1744573 2618315 := bstep (se 1 (by rfl) ⟨1963736, by rfl⟩ : syracuseStep 2618315 = 3927473) B3927473
theorem B1962967 : Blo 1744573 1962967 := bstep (se 1 (by rfl) ⟨1472225, by rfl⟩ : syracuseStep 1962967 = 2944451) B2944451
theorem B2618327 : Blo 1744573 2618327 := bstep (se 1 (by rfl) ⟨1963745, by rfl⟩ : syracuseStep 2618327 = 3927491) B3927491
theorem B3929075 : Blo 1744573 3929075 := bstep (se 1 (by rfl) ⟨2946806, by rfl⟩ : syracuseStep 3929075 = 5893613) B5893613
theorem B57373717 : Blo 1744573 57373717 := bstep (se 6 (by rfl) ⟨1344696, by rfl⟩ : syracuseStep 57373717 = 2689393) B2689393
theorem B2946071 : Blo 1744573 2946071 := bstep (se 1 (by rfl) ⟨2209553, by rfl⟩ : syracuseStep 2946071 = 4419107) B4419107
theorem B3929111 : Blo 1744573 3929111 := bstep (se 1 (by rfl) ⟨2946833, by rfl⟩ : syracuseStep 3929111 = 5893667) B5893667
theorem B2618393 : Blo 1744573 2618393 := bstep (se 2 (by rfl) ⟨981897, by rfl⟩ : syracuseStep 2618393 = 1963795) B1963795
theorem B6624301 : Blo 1744573 6624301 := bstep (se 3 (by rfl) ⟨1242056, by rfl⟩ : syracuseStep 6624301 = 2484113) B2484113
theorem B2552921 : Blo 1744573 2552921 := bstep (se 2 (by rfl) ⟨957345, by rfl⟩ : syracuseStep 2552921 = 1914691) B1914691
theorem B1963147 : Blo 1744573 1963147 := bstep (se 1 (by rfl) ⟨1472360, by rfl⟩ : syracuseStep 1963147 = 2944721) B2944721
theorem B2618507 : Blo 1744573 2618507 := bstep (se 1 (by rfl) ⟨1963880, by rfl⟩ : syracuseStep 2618507 = 3927761) B3927761
theorem B2618519 : Blo 1744573 2618519 := bstep (se 1 (by rfl) ⟨1963889, by rfl⟩ : syracuseStep 2618519 = 3927779) B3927779
theorem B2946199 : Blo 1744573 2946199 := bstep (se 1 (by rfl) ⟨2209649, by rfl⟩ : syracuseStep 2946199 = 4419299) B4419299
theorem B3314839 : Blo 1744573 3314839 := bstep (se 1 (by rfl) ⟨2486129, by rfl⟩ : syracuseStep 3314839 = 4972259) B4972259
theorem B13251761 : Blo 1744573 13251761 := bstep (se 2 (by rfl) ⟨4969410, by rfl⟩ : syracuseStep 13251761 = 9938821) B9938821
theorem B2208971 : Blo 1744573 2208971 := bstep (se 1 (by rfl) ⟨1656728, by rfl⟩ : syracuseStep 2208971 = 3313457) B3313457
theorem B3929291 : Blo 1744573 3929291 := bstep (se 1 (by rfl) ⟨2946968, by rfl⟩ : syracuseStep 3929291 = 5893937) B5893937
theorem B2618585 : Blo 1744573 2618585 := bstep (se 2 (by rfl) ⟨981969, by rfl⟩ : syracuseStep 2618585 = 1963939) B1963939
theorem B1864939 : Blo 1744573 1864939 := bstep (se 1 (by rfl) ⟨1398704, by rfl⟩ : syracuseStep 1864939 = 2797409) B2797409
theorem B1963255 : Blo 1744573 1963255 := bstep (se 1 (by rfl) ⟨1472441, by rfl⟩ : syracuseStep 1963255 = 2944883) B2944883
theorem B3314945 : Blo 1744573 3314945 := bstep (se 2 (by rfl) ⟨1243104, by rfl⟩ : syracuseStep 3314945 = 2486209) B2486209
theorem B3929345 : Blo 1744573 3929345 := bstep (se 2 (by rfl) ⟨1473504, by rfl⟩ : syracuseStep 3929345 = 2947009) B2947009
theorem B16135499 : Blo 1744573 16135499 := bstep (se 1 (by rfl) ⟨12101624, by rfl⟩ : syracuseStep 16135499 = 24203249) B24203249
theorem B2618699 : Blo 1744573 2618699 := bstep (se 1 (by rfl) ⟨1964024, by rfl⟩ : syracuseStep 2618699 = 3928049) B3928049
theorem B4420939 : Blo 1744573 4420939 := bstep (se 1 (by rfl) ⟨3315704, by rfl⟩ : syracuseStep 4420939 = 6631409) B6631409
theorem B2618711 : Blo 1744573 2618711 := bstep (se 1 (by rfl) ⟨1964033, by rfl⟩ : syracuseStep 2618711 = 3928067) B3928067
theorem B6624605 : Blo 1744573 6624605 := bstep (se 3 (by rfl) ⟨1242113, by rfl⟩ : syracuseStep 6624605 = 2484227) B2484227
theorem B2618777 : Blo 1744573 2618777 := bstep (se 2 (by rfl) ⟨982041, by rfl⟩ : syracuseStep 2618777 = 1964083) B1964083
theorem B3315097 : Blo 1744573 3315097 := bstep (se 2 (by rfl) ⟨1243161, by rfl⟩ : syracuseStep 3315097 = 2486323) B2486323
theorem B1963435 : Blo 1744573 1963435 := bstep (se 1 (by rfl) ⟨1472576, by rfl⟩ : syracuseStep 1963435 = 2945153) B2945153
theorem B5305817 : Blo 1744573 5305817 := bstep (se 2 (by rfl) ⟨1989681, by rfl⟩ : syracuseStep 5305817 = 3979363) B3979363
theorem B3929561 : Blo 1744573 3929561 := bstep (se 2 (by rfl) ⟨1473585, by rfl⟩ : syracuseStep 3929561 = 2947171) B2947171
theorem B2618891 : Blo 1744573 2618891 := bstep (se 1 (by rfl) ⟨1964168, by rfl⟩ : syracuseStep 2618891 = 3928337) B3928337
theorem B1963543 : Blo 1744573 1963543 := bstep (se 1 (by rfl) ⟨1472657, by rfl⟩ : syracuseStep 1963543 = 2945315) B2945315
theorem B2618903 : Blo 1744573 2618903 := bstep (se 1 (by rfl) ⟨1964177, by rfl⟩ : syracuseStep 2618903 = 3928355) B3928355
theorem B14153251 : Blo 1744573 14153251 := bstep (se 1 (by rfl) ⟨10614938, by rfl⟩ : syracuseStep 14153251 = 21229877) B21229877
theorem B3929651 : Blo 1744573 3929651 := bstep (se 1 (by rfl) ⟨2947238, by rfl⟩ : syracuseStep 3929651 = 5894477) B5894477
theorem B5969483 : Blo 1744573 5969483 := bstep (se 1 (by rfl) ⟨4477112, by rfl⟩ : syracuseStep 5969483 = 8954225) B8954225
theorem B3929687 : Blo 1744573 3929687 := bstep (se 1 (by rfl) ⟨2947265, by rfl⟩ : syracuseStep 3929687 = 5894531) B5894531
theorem B5592665 : Blo 1744573 5592665 := bstep (se 2 (by rfl) ⟨2097249, by rfl⟩ : syracuseStep 5592665 = 4194499) B4194499
theorem B2618969 : Blo 1744573 2618969 := bstep (se 2 (by rfl) ⟨982113, by rfl⟩ : syracuseStep 2618969 = 1964227) B1964227
theorem B13252247 : Blo 1744573 13252247 := bstep (se 1 (by rfl) ⟨9939185, by rfl⟩ : syracuseStep 13252247 = 19878371) B19878371
theorem B1963723 : Blo 1744573 1963723 := bstep (se 1 (by rfl) ⟨1472792, by rfl⟩ : syracuseStep 1963723 = 2945585) B2945585
theorem B2619083 : Blo 1744573 2619083 := bstep (se 1 (by rfl) ⟨1964312, by rfl⟩ : syracuseStep 2619083 = 3928625) B3928625
theorem B2619095 : Blo 1744573 2619095 := bstep (se 1 (by rfl) ⟨1964321, by rfl⟩ : syracuseStep 2619095 = 3928643) B3928643
theorem B2946827 : Blo 1744573 2946827 := bstep (se 1 (by rfl) ⟨2210120, by rfl⟩ : syracuseStep 2946827 = 4420241) B4420241
theorem B2619161 : Blo 1744573 2619161 := bstep (se 2 (by rfl) ⟨982185, by rfl⟩ : syracuseStep 2619161 = 1964371) B1964371
theorem B22370093 : Blo 1744573 22370093 := bstep (se 3 (by rfl) ⟨4194392, by rfl⟩ : syracuseStep 22370093 = 8388785) B8388785
theorem B1963831 : Blo 1744573 1963831 := bstep (se 1 (by rfl) ⟨1472873, by rfl⟩ : syracuseStep 1963831 = 2945747) B2945747
theorem B11949889 : Blo 1744573 11949889 := bstep (se 2 (by rfl) ⟨4481208, by rfl⟩ : syracuseStep 11949889 = 8962417) B8962417
theorem B9205597 : Blo 1744573 9205597 := bstep (se 3 (by rfl) ⟨1726049, by rfl⟩ : syracuseStep 9205597 = 3452099) B3452099
theorem B2209675 : Blo 1744573 2209675 := bstep (se 1 (by rfl) ⟨1657256, by rfl⟩ : syracuseStep 2209675 = 3314513) B3314513
theorem B2619275 : Blo 1744573 2619275 := bstep (se 1 (by rfl) ⟨1964456, by rfl⟩ : syracuseStep 2619275 = 3928913) B3928913
theorem B2946955 : Blo 1744573 2946955 := bstep (se 1 (by rfl) ⟨2210216, by rfl⟩ : syracuseStep 2946955 = 4420433) B4420433
theorem B2619287 : Blo 1744573 2619287 := bstep (se 1 (by rfl) ⟨1964465, by rfl⟩ : syracuseStep 2619287 = 3928931) B3928931
theorem B2619353 : Blo 1744573 2619353 := bstep (se 2 (by rfl) ⟨982257, by rfl⟩ : syracuseStep 2619353 = 1964515) B1964515
theorem B1964011 : Blo 1744573 1964011 := bstep (se 1 (by rfl) ⟨1473008, by rfl⟩ : syracuseStep 1964011 = 2946017) B2946017
theorem B2947097 : Blo 1744573 2947097 := bstep (se 2 (by rfl) ⟨1105161, by rfl⟩ : syracuseStep 2947097 = 2210323) B2210323
theorem B7960621 : Blo 1744573 7960621 := bstep (se 3 (by rfl) ⟨1492616, by rfl⟩ : syracuseStep 7960621 = 2985233) B2985233
theorem B5888051 : Blo 1744573 5888051 := bstep (se 1 (by rfl) ⟨4416038, by rfl⟩ : syracuseStep 5888051 = 8832077) B8832077
theorem B5036107 : Blo 1744573 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B2619467 : Blo 1744573 2619467 := bstep (se 1 (by rfl) ⟨1964600, by rfl⟩ : syracuseStep 2619467 = 3929201) B3929201
theorem B1964119 : Blo 1744573 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B2619479 : Blo 1744573 2619479 := bstep (se 1 (by rfl) ⟨1964609, by rfl⟩ : syracuseStep 2619479 = 3929219) B3929219
theorem B4970585 : Blo 1744573 4970585 := bstep (se 2 (by rfl) ⟨1863969, by rfl⟩ : syracuseStep 4970585 = 3727939) B3727939
theorem B2209943 : Blo 1744573 2209943 := bstep (se 1 (by rfl) ⟨1657457, by rfl⟩ : syracuseStep 2209943 = 3314915) B3314915
theorem B2619545 : Blo 1744573 2619545 := bstep (se 2 (by rfl) ⟨982329, by rfl⟩ : syracuseStep 2619545 = 1964659) B1964659
theorem B2947225 : Blo 1744573 2947225 := bstep (se 2 (by rfl) ⟨1105209, by rfl⟩ : syracuseStep 2947225 = 2210419) B2210419
theorem B4716737 : Blo 1744573 4716737 := bstep (se 2 (by rfl) ⟨1768776, by rfl⟩ : syracuseStep 4716737 = 3537553) B3537553
theorem B2832601 : Blo 1744573 2832601 := bstep (se 2 (by rfl) ⟨1062225, by rfl⟩ : syracuseStep 2832601 = 2124451) B2124451
theorem B1964299 : Blo 1744573 1964299 := bstep (se 1 (by rfl) ⟨1473224, by rfl⟩ : syracuseStep 1964299 = 2946449) B2946449
theorem B2619659 : Blo 1744573 2619659 := bstep (se 1 (by rfl) ⟨1964744, by rfl⟩ : syracuseStep 2619659 = 3929489) B3929489
theorem B2619671 : Blo 1744573 2619671 := bstep (se 1 (by rfl) ⟨1964753, by rfl⟩ : syracuseStep 2619671 = 3929507) B3929507
theorem B5888321 : Blo 1744573 5888321 := bstep (se 2 (by rfl) ⟨2208120, by rfl⟩ : syracuseStep 5888321 = 4416241) B4416241
theorem B2619737 : Blo 1744573 2619737 := bstep (se 2 (by rfl) ⟨982401, by rfl⟩ : syracuseStep 2619737 = 1964803) B1964803
theorem B9075037 : Blo 1744573 9075037 := bstep (se 3 (by rfl) ⟨1701569, by rfl⟩ : syracuseStep 9075037 = 3403139) B3403139
theorem B1964407 : Blo 1744573 1964407 := bstep (se 1 (by rfl) ⟨1473305, by rfl⟩ : syracuseStep 1964407 = 2946611) B2946611
theorem B2619851 : Blo 1744573 2619851 := bstep (se 1 (by rfl) ⟨1964888, by rfl⟩ : syracuseStep 2619851 = 3929777) B3929777
theorem B1964587 : Blo 1744573 1964587 := bstep (se 1 (by rfl) ⟨1473440, by rfl⟩ : syracuseStep 1964587 = 2946881) B2946881
theorem B12581477 : Blo 1744573 12581477 := bstep (se 4 (by rfl) ⟨1179513, by rfl⟩ : syracuseStep 12581477 = 2359027) B2359027
theorem B7076497 : Blo 1744573 7076497 := bstep (se 2 (by rfl) ⟨2653686, by rfl⟩ : syracuseStep 7076497 = 5307373) B5307373
theorem B1964695 : Blo 1744573 1964695 := bstep (se 1 (by rfl) ⟨1473521, by rfl⟩ : syracuseStep 1964695 = 2947043) B2947043
theorem B3537665 : Blo 1744573 3537665 := bstep (se 2 (by rfl) ⟨1326624, by rfl⟩ : syracuseStep 3537665 = 2653249) B2653249
theorem B1964875 : Blo 1744573 1964875 := bstep (se 1 (by rfl) ⟨1473656, by rfl⟩ : syracuseStep 1964875 = 2947313) B2947313
theorem B5888861 : Blo 1744573 5888861 := bstep (se 3 (by rfl) ⟨1104161, by rfl⟩ : syracuseStep 5888861 = 2208323) B2208323
theorem B7961495 : Blo 1744573 7961495 := bstep (se 1 (by rfl) ⟨5971121, by rfl⟩ : syracuseStep 7961495 = 11942243) B11942243
theorem B11189171 : Blo 1744573 11189171 := bstep (se 1 (by rfl) ⟨8391878, by rfl⟩ : syracuseStep 11189171 = 16783757) B16783757
theorem B7453741 : Blo 1744573 7453741 := bstep (se 3 (by rfl) ⟨1397576, by rfl⟩ : syracuseStep 7453741 = 2795153) B2795153
theorem B4193345 : Blo 1744573 4193345 := bstep (se 2 (by rfl) ⟨1572504, by rfl⟩ : syracuseStep 4193345 = 3145009) B3145009
theorem B6290507 : Blo 1744573 6290507 := bstep (se 1 (by rfl) ⟨4717880, by rfl⟩ : syracuseStep 6290507 = 9435761) B9435761
theorem B5594305 : Blo 1744573 5594305 := bstep (se 2 (by rfl) ⟨2097864, by rfl⟩ : syracuseStep 5594305 = 4195729) B4195729
theorem B13434263 : Blo 1744573 13434263 := bstep (se 1 (by rfl) ⟨10075697, by rfl⟩ : syracuseStep 13434263 = 20151395) B20151395
theorem B9944471 : Blo 1744573 9944471 := bstep (se 1 (by rfl) ⟨7458353, by rfl⟩ : syracuseStep 9944471 = 14916707) B14916707
theorem B8068531 : Blo 1744573 8068531 := bstep (se 1 (by rfl) ⟨6051398, by rfl⟩ : syracuseStep 8068531 = 12102797) B12102797
theorem B3726785 : Blo 1744573 3726785 := bstep (se 2 (by rfl) ⟨1397544, by rfl⟩ : syracuseStep 3726785 = 2795089) B2795089
theorem B3538379 : Blo 1744573 3538379 := bstep (se 1 (by rfl) ⟨2653784, by rfl⟩ : syracuseStep 3538379 = 5307569) B5307569
theorem B14909021 : Blo 1744573 14909021 := bstep (se 3 (by rfl) ⟨2795441, by rfl⟩ : syracuseStep 14909021 = 5590883) B5590883
theorem B11337317 : Blo 1744573 11337317 := bstep (se 4 (by rfl) ⟨1062873, by rfl⟩ : syracuseStep 11337317 = 2125747) B2125747
theorem B4972225 : Blo 1744573 4972225 := bstep (se 2 (by rfl) ⟨1864584, by rfl⟩ : syracuseStep 4972225 = 3729169) B3729169
theorem B1744587 : Blo 1744573 1744587 := bstep (se 1 (by rfl) ⟨1308440, by rfl⟩ : syracuseStep 1744587 = 2616881) B2616881
theorem B1744599 : Blo 1744573 1744599 := bstep (se 1 (by rfl) ⟨1308449, by rfl⟩ : syracuseStep 1744599 = 2616899) B2616899
theorem B1744619 : Blo 1744573 1744619 := bstep (se 1 (by rfl) ⟨1308464, by rfl⟩ : syracuseStep 1744619 = 2616929) B2616929
theorem B1744631 : Blo 1744573 1744631 := bstep (se 1 (by rfl) ⟨1308473, by rfl⟩ : syracuseStep 1744631 = 2616947) B2616947
theorem B1744651 : Blo 1744573 1744651 := bstep (se 1 (by rfl) ⟨1308488, by rfl⟩ : syracuseStep 1744651 = 2616977) B2616977
theorem B1744663 : Blo 1744573 1744663 := bstep (se 1 (by rfl) ⟨1308497, by rfl⟩ : syracuseStep 1744663 = 2616995) B2616995
theorem B3727127 : Blo 1744573 3727127 := bstep (se 1 (by rfl) ⟨2795345, by rfl⟩ : syracuseStep 3727127 = 5590691) B5590691
theorem B1744683 : Blo 1744573 1744683 := bstep (se 1 (by rfl) ⟨1308512, by rfl⟩ : syracuseStep 1744683 = 2617025) B2617025
theorem B29835053 : Blo 1744573 29835053 := bstep (se 3 (by rfl) ⟨5594072, by rfl⟩ : syracuseStep 29835053 = 11188145) B11188145
theorem B1744695 : Blo 1744573 1744695 := bstep (se 1 (by rfl) ⟨1308521, by rfl⟩ : syracuseStep 1744695 = 2617043) B2617043
theorem B1744715 : Blo 1744573 1744715 := bstep (se 1 (by rfl) ⟨1308536, by rfl⟩ : syracuseStep 1744715 = 2617073) B2617073
theorem B2654027 : Blo 1744573 2654027 := bstep (se 1 (by rfl) ⟨1990520, by rfl⟩ : syracuseStep 2654027 = 3981041) B3981041
theorem B1744727 : Blo 1744573 1744727 := bstep (se 1 (by rfl) ⟨1308545, by rfl⟩ : syracuseStep 1744727 = 2617091) B2617091
theorem B1744747 : Blo 1744573 1744747 := bstep (se 1 (by rfl) ⟨1308560, by rfl⟩ : syracuseStep 1744747 = 2617121) B2617121
theorem B1744759 : Blo 1744573 1744759 := bstep (se 1 (by rfl) ⟨1308569, by rfl⟩ : syracuseStep 1744759 = 2617139) B2617139
theorem B6627203 : Blo 1744573 6627203 := bstep (se 1 (by rfl) ⟨4970402, by rfl⟩ : syracuseStep 6627203 = 9940805) B9940805
theorem B8839043 : Blo 1744573 8839043 := bstep (se 1 (by rfl) ⟨6629282, by rfl⟩ : syracuseStep 8839043 = 13258565) B13258565
theorem B1744779 : Blo 1744573 1744779 := bstep (se 1 (by rfl) ⟨1308584, by rfl⟩ : syracuseStep 1744779 = 2617169) B2617169
theorem B6627217 : Blo 1744573 6627217 := bstep (se 2 (by rfl) ⟨2485206, by rfl⟩ : syracuseStep 6627217 = 4970413) B4970413
theorem B1744791 : Blo 1744573 1744791 := bstep (se 1 (by rfl) ⟨1308593, by rfl⟩ : syracuseStep 1744791 = 2617187) B2617187
theorem B2097047 : Blo 1744573 2097047 := bstep (se 1 (by rfl) ⟨1572785, by rfl⟩ : syracuseStep 2097047 = 3145571) B3145571
theorem B1744811 : Blo 1744573 1744811 := bstep (se 1 (by rfl) ⟨1308608, by rfl⟩ : syracuseStep 1744811 = 2617217) B2617217
theorem B18874289 : Blo 1744573 18874289 := bstep (se 2 (by rfl) ⟨7077858, by rfl⟩ : syracuseStep 18874289 = 14155717) B14155717
theorem B1744823 : Blo 1744573 1744823 := bstep (se 1 (by rfl) ⟨1308617, by rfl⟩ : syracuseStep 1744823 = 2617235) B2617235
theorem B1744843 : Blo 1744573 1744843 := bstep (se 1 (by rfl) ⟨1308632, by rfl⟩ : syracuseStep 1744843 = 2617265) B2617265
theorem B5889995 : Blo 1744573 5889995 := bstep (se 1 (by rfl) ⟨4417496, by rfl⟩ : syracuseStep 5889995 = 8834993) B8834993
theorem B1744855 : Blo 1744573 1744855 := bstep (se 1 (by rfl) ⟨1308641, by rfl⟩ : syracuseStep 1744855 = 2617283) B2617283
theorem B1744875 : Blo 1744573 1744875 := bstep (se 1 (by rfl) ⟨1308656, by rfl⟩ : syracuseStep 1744875 = 2617313) B2617313
theorem B1744887 : Blo 1744573 1744887 := bstep (se 1 (by rfl) ⟨1308665, by rfl⟩ : syracuseStep 1744887 = 2617331) B2617331
theorem B1744903 : Blo 1744573 1744903 := bstep (se 1 (by rfl) ⟨1308677, by rfl⟩ : syracuseStep 1744903 = 2617355) B2617355
theorem B1744911 : Blo 1744573 1744911 := bstep (se 1 (by rfl) ⟨1308683, by rfl⟩ : syracuseStep 1744911 = 2617367) B2617367
theorem B1744955 : Blo 1744573 1744955 := bstep (se 1 (by rfl) ⟨1308716, by rfl⟩ : syracuseStep 1744955 = 2617433) B2617433
theorem B12582973 : Blo 1744573 12582973 := bstep (se 3 (by rfl) ⟨2359307, by rfl⟩ : syracuseStep 12582973 = 4718615) B4718615
theorem B1745031 : Blo 1744573 1745031 := bstep (se 1 (by rfl) ⟨1308773, by rfl⟩ : syracuseStep 1745031 = 2617547) B2617547
theorem B1745039 : Blo 1744573 1745039 := bstep (se 1 (by rfl) ⟨1308779, by rfl⟩ : syracuseStep 1745039 = 2617559) B2617559
theorem B4972691 : Blo 1744573 4972691 := bstep (se 1 (by rfl) ⟨3729518, by rfl⟩ : syracuseStep 4972691 = 7459037) B7459037
theorem B1745083 : Blo 1744573 1745083 := bstep (se 1 (by rfl) ⟨1308812, by rfl⟩ : syracuseStep 1745083 = 2617625) B2617625
theorem B1745159 : Blo 1744573 1745159 := bstep (se 1 (by rfl) ⟨1308869, by rfl⟩ : syracuseStep 1745159 = 2617739) B2617739
theorem B1745167 : Blo 1744573 1745167 := bstep (se 1 (by rfl) ⟨1308875, by rfl⟩ : syracuseStep 1745167 = 2617751) B2617751
theorem B5890319 : Blo 1744573 5890319 := bstep (se 1 (by rfl) ⟨4417739, by rfl⟩ : syracuseStep 5890319 = 8835479) B8835479
theorem B3776801 : Blo 1744573 3776801 := bstep (se 2 (by rfl) ⟨1416300, by rfl⟩ : syracuseStep 3776801 = 2832601) B2832601
theorem B18866465 : Blo 1744573 18866465 := bstep (se 2 (by rfl) ⟨7074924, by rfl⟩ : syracuseStep 18866465 = 14149849) B14149849
theorem B2834731 : Blo 1744573 2834731 := bstep (se 1 (by rfl) ⟨2126048, by rfl⟩ : syracuseStep 2834731 = 4252097) B4252097
theorem B2097451 : Blo 1744573 2097451 := bstep (se 1 (by rfl) ⟨1573088, by rfl⟩ : syracuseStep 2097451 = 3146177) B3146177
theorem B1745211 : Blo 1744573 1745211 := bstep (se 1 (by rfl) ⟨1308908, by rfl⟩ : syracuseStep 1745211 = 2617817) B2617817
theorem B5308759 : Blo 1744573 5308759 := bstep (se 1 (by rfl) ⟨3981569, by rfl⟩ : syracuseStep 5308759 = 7963139) B7963139
theorem B1745287 : Blo 1744573 1745287 := bstep (se 1 (by rfl) ⟨1308965, by rfl⟩ : syracuseStep 1745287 = 2617931) B2617931
theorem B1745295 : Blo 1744573 1745295 := bstep (se 1 (by rfl) ⟨1308971, by rfl⟩ : syracuseStep 1745295 = 2617943) B2617943
theorem B1745339 : Blo 1744573 1745339 := bstep (se 1 (by rfl) ⟨1309004, by rfl⟩ : syracuseStep 1745339 = 2618009) B2618009
theorem B2097595 : Blo 1744573 2097595 := bstep (se 1 (by rfl) ⟨1573196, by rfl⟩ : syracuseStep 2097595 = 3146393) B3146393
theorem B12100049 : Blo 1744573 12100049 := bstep (se 2 (by rfl) ⟨4537518, by rfl⟩ : syracuseStep 12100049 = 9075037) B9075037
theorem B1745415 : Blo 1744573 1745415 := bstep (se 1 (by rfl) ⟨1309061, by rfl⟩ : syracuseStep 1745415 = 2618123) B2618123
theorem B8839691 : Blo 1744573 8839691 := bstep (se 1 (by rfl) ⟨6629768, by rfl⟩ : syracuseStep 8839691 = 13259537) B13259537
theorem B9945611 : Blo 1744573 9945611 := bstep (se 1 (by rfl) ⟨7459208, by rfl⟩ : syracuseStep 9945611 = 14918417) B14918417
theorem B1745423 : Blo 1744573 1745423 := bstep (se 1 (by rfl) ⟨1309067, by rfl⟩ : syracuseStep 1745423 = 2618135) B2618135
theorem B5890589 : Blo 1744573 5890589 := bstep (se 3 (by rfl) ⟨1104485, by rfl⟩ : syracuseStep 5890589 = 2208971) B2208971
theorem B4416059 : Blo 1744573 4416059 := bstep (se 1 (by rfl) ⟨3312044, by rfl⟩ : syracuseStep 4416059 = 6624089) B6624089
theorem B1745467 : Blo 1744573 1745467 := bstep (se 1 (by rfl) ⟨1309100, by rfl⟩ : syracuseStep 1745467 = 2618201) B2618201
theorem B29082179 : Blo 1744573 29082179 := bstep (se 1 (by rfl) ⟨21811634, by rfl⟩ : syracuseStep 29082179 = 43623269) B43623269
theorem B1745543 : Blo 1744573 1745543 := bstep (se 1 (by rfl) ⟨1309157, by rfl⟩ : syracuseStep 1745543 = 2618315) B2618315
theorem B1745551 : Blo 1744573 1745551 := bstep (se 1 (by rfl) ⟨1309163, by rfl⟩ : syracuseStep 1745551 = 2618327) B2618327
theorem B8839853 : Blo 1744573 8839853 := bstep (se 3 (by rfl) ⟨1657472, by rfl⟩ : syracuseStep 8839853 = 3314945) B3314945
theorem B1745595 : Blo 1744573 1745595 := bstep (se 1 (by rfl) ⟨1309196, by rfl⟩ : syracuseStep 1745595 = 2618393) B2618393
theorem B9937637 : Blo 1744573 9937637 := bstep (se 4 (by rfl) ⟨931653, by rfl⟩ : syracuseStep 9937637 = 1863307) B1863307
theorem B1745671 : Blo 1744573 1745671 := bstep (se 1 (by rfl) ⟨1309253, by rfl⟩ : syracuseStep 1745671 = 2618507) B2618507
theorem B1745679 : Blo 1744573 1745679 := bstep (se 1 (by rfl) ⟨1309259, by rfl⟩ : syracuseStep 1745679 = 2618519) B2618519
theorem B4195115 : Blo 1744573 4195115 := bstep (se 1 (by rfl) ⟨3146336, by rfl⟩ : syracuseStep 4195115 = 6292673) B6292673
theorem B1745723 : Blo 1744573 1745723 := bstep (se 1 (by rfl) ⟨1309292, by rfl⟩ : syracuseStep 1745723 = 2618585) B2618585
theorem B10756999 : Blo 1744573 10756999 := bstep (se 1 (by rfl) ⟨8067749, by rfl⟩ : syracuseStep 10756999 = 16135499) B16135499
theorem B1745799 : Blo 1744573 1745799 := bstep (se 1 (by rfl) ⟨1309349, by rfl⟩ : syracuseStep 1745799 = 2618699) B2618699
theorem B1745807 : Blo 1744573 1745807 := bstep (se 1 (by rfl) ⟨1309355, by rfl⟩ : syracuseStep 1745807 = 2618711) B2618711
theorem B4416403 : Blo 1744573 4416403 := bstep (se 1 (by rfl) ⟨3312302, by rfl⟩ : syracuseStep 4416403 = 6624605) B6624605
theorem B27231157 : Blo 1744573 27231157 := bstep (se 5 (by rfl) ⟨1276460, by rfl⟩ : syracuseStep 27231157 = 2552921) B2552921
theorem B6292409 : Blo 1744573 6292409 := bstep (se 2 (by rfl) ⟨2359653, by rfl⟩ : syracuseStep 6292409 = 4719307) B4719307
theorem B1745851 : Blo 1744573 1745851 := bstep (se 1 (by rfl) ⟨1309388, by rfl⟩ : syracuseStep 1745851 = 2618777) B2618777
theorem B1745927 : Blo 1744573 1745927 := bstep (se 1 (by rfl) ⟨1309445, by rfl⟩ : syracuseStep 1745927 = 2618891) B2618891
theorem B1745935 : Blo 1744573 1745935 := bstep (se 1 (by rfl) ⟨1309451, by rfl⟩ : syracuseStep 1745935 = 2618903) B2618903
theorem B4416545 : Blo 1744573 4416545 := bstep (se 2 (by rfl) ⟨1656204, by rfl⟩ : syracuseStep 4416545 = 3312409) B3312409
theorem B3728443 : Blo 1744573 3728443 := bstep (se 1 (by rfl) ⟨2796332, by rfl⟩ : syracuseStep 3728443 = 5592665) B5592665
theorem B1745979 : Blo 1744573 1745979 := bstep (se 1 (by rfl) ⟨1309484, by rfl⟩ : syracuseStep 1745979 = 2618969) B2618969
theorem B1746055 : Blo 1744573 1746055 := bstep (se 1 (by rfl) ⟨1309541, by rfl⟩ : syracuseStep 1746055 = 2619083) B2619083
theorem B1746063 : Blo 1744573 1746063 := bstep (se 1 (by rfl) ⟨1309547, by rfl⟩ : syracuseStep 1746063 = 2619095) B2619095
theorem B1746107 : Blo 1744573 1746107 := bstep (se 1 (by rfl) ⟨1309580, by rfl⟩ : syracuseStep 1746107 = 2619161) B2619161
theorem B10077377 : Blo 1744573 10077377 := bstep (se 2 (by rfl) ⟨3779016, by rfl⟩ : syracuseStep 10077377 = 7558033) B7558033
theorem B1746183 : Blo 1744573 1746183 := bstep (se 1 (by rfl) ⟨1309637, by rfl⟩ : syracuseStep 1746183 = 2619275) B2619275
theorem B1746191 : Blo 1744573 1746191 := bstep (se 1 (by rfl) ⟨1309643, by rfl⟩ : syracuseStep 1746191 = 2619287) B2619287
theorem B1746235 : Blo 1744573 1746235 := bstep (se 1 (by rfl) ⟨1309676, by rfl⟩ : syracuseStep 1746235 = 2619353) B2619353
theorem B76498289 : Blo 1744573 76498289 := bstep (se 2 (by rfl) ⟨28686858, by rfl⟩ : syracuseStep 76498289 = 57373717) B57373717
theorem B3925367 : Blo 1744573 3925367 := bstep (se 1 (by rfl) ⟨2944025, by rfl⟩ : syracuseStep 3925367 = 5888051) B5888051
theorem B4719991 : Blo 1744573 4719991 := bstep (se 1 (by rfl) ⟨3539993, by rfl⟩ : syracuseStep 4719991 = 7079987) B7079987
theorem B6292871 : Blo 1744573 6292871 := bstep (se 1 (by rfl) ⟨4719653, by rfl⟩ : syracuseStep 6292871 = 9439307) B9439307
theorem B1746311 : Blo 1744573 1746311 := bstep (se 1 (by rfl) ⟨1309733, by rfl⟩ : syracuseStep 1746311 = 2619467) B2619467
theorem B1746319 : Blo 1744573 1746319 := bstep (se 1 (by rfl) ⟨1309739, by rfl⟩ : syracuseStep 1746319 = 2619479) B2619479
theorem B8832401 : Blo 1744573 8832401 := bstep (se 2 (by rfl) ⟨3312150, by rfl⟩ : syracuseStep 8832401 = 6624301) B6624301
theorem B9938321 : Blo 1744573 9938321 := bstep (se 2 (by rfl) ⟨3726870, by rfl⟩ : syracuseStep 9938321 = 7453741) B7453741
theorem B1746363 : Blo 1744573 1746363 := bstep (se 1 (by rfl) ⟨1309772, by rfl⟩ : syracuseStep 1746363 = 2619545) B2619545
theorem B1746439 : Blo 1744573 1746439 := bstep (se 1 (by rfl) ⟨1309829, by rfl⟩ : syracuseStep 1746439 = 2619659) B2619659
theorem B1746447 : Blo 1744573 1746447 := bstep (se 1 (by rfl) ⟨1309835, by rfl⟩ : syracuseStep 1746447 = 2619671) B2619671
theorem B3925547 : Blo 1744573 3925547 := bstep (se 1 (by rfl) ⟨2944160, by rfl⟩ : syracuseStep 3925547 = 5888321) B5888321
theorem B1746491 : Blo 1744573 1746491 := bstep (se 1 (by rfl) ⟨1309868, by rfl⟩ : syracuseStep 1746491 = 2619737) B2619737
theorem B4916855 : Blo 1744573 4916855 := bstep (se 1 (by rfl) ⟨3687641, by rfl⟩ : syracuseStep 4916855 = 7375283) B7375283
theorem B1746567 : Blo 1744573 1746567 := bstep (se 1 (by rfl) ⟨1309925, by rfl⟩ : syracuseStep 1746567 = 2619851) B2619851
theorem B3925907 : Blo 1744573 3925907 := bstep (se 1 (by rfl) ⟨2944430, by rfl⟩ : syracuseStep 3925907 = 5888861) B5888861
theorem B10758041 : Blo 1744573 10758041 := bstep (se 2 (by rfl) ⟨4034265, by rfl⟩ : syracuseStep 10758041 = 8068531) B8068531
theorem B5891993 : Blo 1744573 5891993 := bstep (se 2 (by rfl) ⟨2209497, by rfl⟩ : syracuseStep 5891993 = 4418995) B4418995
theorem B3925961 : Blo 1744573 3925961 := bstep (se 2 (by rfl) ⟨1472235, by rfl⟩ : syracuseStep 3925961 = 2944471) B2944471
theorem B4417537 : Blo 1744573 4417537 := bstep (se 2 (by rfl) ⟨1656576, by rfl⟩ : syracuseStep 4417537 = 3313153) B3313153
theorem B2795563 : Blo 1744573 2795563 := bstep (se 1 (by rfl) ⟨2096672, by rfl⟩ : syracuseStep 2795563 = 4193345) B4193345
theorem B6629633 : Blo 1744573 6629633 := bstep (se 2 (by rfl) ⟨2486112, by rfl⟩ : syracuseStep 6629633 = 4972225) B4972225
theorem B8841473 : Blo 1744573 8841473 := bstep (se 2 (by rfl) ⟨3315552, by rfl⟩ : syracuseStep 8841473 = 6631105) B6631105
theorem B8956175 : Blo 1744573 8956175 := bstep (se 1 (by rfl) ⟨6717131, by rfl⟩ : syracuseStep 8956175 = 13434263) B13434263
theorem B6629647 : Blo 1744573 6629647 := bstep (se 1 (by rfl) ⟨4972235, by rfl⟩ : syracuseStep 6629647 = 9944471) B9944471
theorem B2484523 : Blo 1744573 2484523 := bstep (se 1 (by rfl) ⟨1863392, by rfl⟩ : syracuseStep 2484523 = 3726785) B3726785
theorem B9939347 : Blo 1744573 9939347 := bstep (se 1 (by rfl) ⟨7454510, by rfl⟩ : syracuseStep 9939347 = 14909021) B14909021
theorem B13257107 : Blo 1744573 13257107 := bstep (se 1 (by rfl) ⟨9942830, by rfl⟩ : syracuseStep 13257107 = 19885661) B19885661
theorem B2484751 : Blo 1744573 2484751 := bstep (se 1 (by rfl) ⟨1863563, by rfl⟩ : syracuseStep 2484751 = 3727127) B3727127
theorem B4418135 : Blo 1744573 4418135 := bstep (se 1 (by rfl) ⟨3313601, by rfl⟩ : syracuseStep 4418135 = 6627203) B6627203
theorem B5892695 : Blo 1744573 5892695 := bstep (se 1 (by rfl) ⟨4419521, by rfl⟩ : syracuseStep 5892695 = 8839043) B8839043
theorem B3926663 : Blo 1744573 3926663 := bstep (se 1 (by rfl) ⟨2944997, by rfl⟩ : syracuseStep 3926663 = 5889995) B5889995
theorem B16780067 : Blo 1744573 16780067 := bstep (se 1 (by rfl) ⟨12585050, by rfl⟩ : syracuseStep 16780067 = 25170101) B25170101
theorem B4418347 : Blo 1744573 4418347 := bstep (se 1 (by rfl) ⟨3313760, by rfl⟩ : syracuseStep 4418347 = 6627521) B6627521
theorem B13249331 : Blo 1744573 13249331 := bstep (se 1 (by rfl) ⟨9936998, by rfl⟩ : syracuseStep 13249331 = 19873997) B19873997
theorem B3926843 : Blo 1744573 3926843 := bstep (se 1 (by rfl) ⟨2945132, by rfl⟩ : syracuseStep 3926843 = 5890265) B5890265
theorem B107539301 : Blo 1744573 107539301 := bstep (se 4 (by rfl) ⟨10081809, by rfl⟩ : syracuseStep 107539301 = 20163619) B20163619
theorem B2485127 : Blo 1744573 2485127 := bstep (se 1 (by rfl) ⟨1863845, by rfl⟩ : syracuseStep 2485127 = 3727691) B3727691
theorem B3312569 : Blo 1744573 3312569 := bstep (se 2 (by rfl) ⟨1242213, by rfl⟩ : syracuseStep 3312569 = 2484427) B2484427
theorem B3926969 : Blo 1744573 3926969 := bstep (se 2 (by rfl) ⟨1472613, by rfl⟩ : syracuseStep 3926969 = 2945227) B2945227
theorem B4418489 : Blo 1744573 4418489 := bstep (se 2 (by rfl) ⟨1656933, by rfl⟩ : syracuseStep 4418489 = 3313867) B3313867
theorem B2796473 : Blo 1744573 2796473 := bstep (se 2 (by rfl) ⟨1048677, by rfl⟩ : syracuseStep 2796473 = 2097355) B2097355
theorem B35843077 : Blo 1744573 35843077 := bstep (se 4 (by rfl) ⟨3360288, by rfl⟩ : syracuseStep 35843077 = 6720577) B6720577
theorem B16133131 : Blo 1744573 16133131 := bstep (se 1 (by rfl) ⟨12099848, by rfl⟩ : syracuseStep 16133131 = 24199697) B24199697
theorem B5893181 : Blo 1744573 5893181 := bstep (se 3 (by rfl) ⟨1104971, by rfl⟩ : syracuseStep 5893181 = 2209943) B2209943
theorem B2944201 : Blo 1744573 2944201 := bstep (se 2 (by rfl) ⟨1104075, by rfl⟩ : syracuseStep 2944201 = 2208151) B2208151
theorem B3927311 : Blo 1744573 3927311 := bstep (se 1 (by rfl) ⟨2945483, by rfl⟩ : syracuseStep 3927311 = 5890967) B5890967
theorem B3927329 : Blo 1744573 3927329 := bstep (se 2 (by rfl) ⟨1472748, by rfl⟩ : syracuseStep 3927329 = 2945497) B2945497
theorem B1863047 : Blo 1744573 1863047 := bstep (se 1 (by rfl) ⟨1397285, by rfl⟩ : syracuseStep 1863047 = 2794571) B2794571
theorem B8834507 : Blo 1744573 8834507 := bstep (se 1 (by rfl) ⟨6625880, by rfl⟩ : syracuseStep 8834507 = 13251761) B13251761
theorem B6630923 : Blo 1744573 6630923 := bstep (se 1 (by rfl) ⟨4973192, by rfl⟩ : syracuseStep 6630923 = 9946385) B9946385
theorem B2616875 : Blo 1744573 2616875 := bstep (se 1 (by rfl) ⟨1962656, by rfl⟩ : syracuseStep 2616875 = 3925313) B3925313
theorem B2616905 : Blo 1744573 2616905 := bstep (se 2 (by rfl) ⟨981339, by rfl⟩ : syracuseStep 2616905 = 1962679) B1962679
theorem B43069027 : Blo 1744573 43069027 := bstep (se 1 (by rfl) ⟨32301770, by rfl⟩ : syracuseStep 43069027 = 64603541) B64603541
theorem B3927671 : Blo 1744573 3927671 := bstep (se 1 (by rfl) ⟨2945753, by rfl⟩ : syracuseStep 3927671 = 5891507) B5891507
theorem B145288835 : Blo 1744573 145288835 := bstep (se 1 (by rfl) ⟨108966626, by rfl⟩ : syracuseStep 145288835 = 217933253) B217933253
theorem B2617019 : Blo 1744573 2617019 := bstep (se 1 (by rfl) ⟨1962764, by rfl⟩ : syracuseStep 2617019 = 3925529) B3925529
theorem B2617079 : Blo 1744573 2617079 := bstep (se 1 (by rfl) ⟨1962809, by rfl⟩ : syracuseStep 2617079 = 3925619) B3925619
theorem B2617103 : Blo 1744573 2617103 := bstep (se 1 (by rfl) ⟨1962827, by rfl⟩ : syracuseStep 2617103 = 3925655) B3925655
theorem B8834831 : Blo 1744573 8834831 := bstep (se 1 (by rfl) ⟨6626123, by rfl⟩ : syracuseStep 8834831 = 13252247) B13252247
theorem B3927851 : Blo 1744573 3927851 := bstep (se 1 (by rfl) ⟨2945888, by rfl⟩ : syracuseStep 3927851 = 5891777) B5891777
theorem B2617145 : Blo 1744573 2617145 := bstep (se 2 (by rfl) ⟨981429, by rfl⟩ : syracuseStep 2617145 = 1962859) B1962859
theorem B14913395 : Blo 1744573 14913395 := bstep (se 1 (by rfl) ⟨11185046, by rfl⟩ : syracuseStep 14913395 = 22370093) B22370093
theorem B2617223 : Blo 1744573 2617223 := bstep (se 1 (by rfl) ⟨1962917, by rfl⟩ : syracuseStep 2617223 = 3925835) B3925835
theorem B2944903 : Blo 1744573 2944903 := bstep (se 1 (by rfl) ⟨2208677, by rfl⟩ : syracuseStep 2944903 = 4417355) B4417355
theorem B4419481 : Blo 1744573 4419481 := bstep (se 2 (by rfl) ⟨1657305, by rfl⟩ : syracuseStep 4419481 = 3314611) B3314611
theorem B2617259 : Blo 1744573 2617259 := bstep (se 1 (by rfl) ⟨1962944, by rfl⟩ : syracuseStep 2617259 = 3925889) B3925889
theorem B2617289 : Blo 1744573 2617289 := bstep (se 2 (by rfl) ⟨981483, by rfl⟩ : syracuseStep 2617289 = 1962967) B1962967
theorem B2617403 : Blo 1744573 2617403 := bstep (se 1 (by rfl) ⟨1963052, by rfl⟩ : syracuseStep 2617403 = 3926105) B3926105
theorem B3313723 : Blo 1744573 3313723 := bstep (se 1 (by rfl) ⟨2485292, by rfl⟩ : syracuseStep 3313723 = 4970585) B4970585
theorem B4419643 : Blo 1744573 4419643 := bstep (se 1 (by rfl) ⟨3314732, by rfl⟩ : syracuseStep 4419643 = 6629465) B6629465
theorem B2617463 : Blo 1744573 2617463 := bstep (se 1 (by rfl) ⟨1963097, by rfl⟩ : syracuseStep 2617463 = 3926195) B3926195
theorem B2617487 : Blo 1744573 2617487 := bstep (se 1 (by rfl) ⟨1963115, by rfl⟩ : syracuseStep 2617487 = 3926231) B3926231
theorem B3928211 : Blo 1744573 3928211 := bstep (se 1 (by rfl) ⟨2946158, by rfl⟩ : syracuseStep 3928211 = 5892317) B5892317
theorem B2617529 : Blo 1744573 2617529 := bstep (se 2 (by rfl) ⟨981573, by rfl⟩ : syracuseStep 2617529 = 1963147) B1963147
theorem B3928265 : Blo 1744573 3928265 := bstep (se 2 (by rfl) ⟨1473099, by rfl⟩ : syracuseStep 3928265 = 2946199) B2946199
theorem B4419785 : Blo 1744573 4419785 := bstep (se 2 (by rfl) ⟨1657419, by rfl⟩ : syracuseStep 4419785 = 3314839) B3314839
theorem B37753073 : Blo 1744573 37753073 := bstep (se 2 (by rfl) ⟨14157402, by rfl⟩ : syracuseStep 37753073 = 28314805) B28314805
theorem B84922613 : Blo 1744573 84922613 := bstep (se 5 (by rfl) ⟨3980747, by rfl⟩ : syracuseStep 84922613 = 7961495) B7961495
theorem B7459073 : Blo 1744573 7459073 := bstep (se 2 (by rfl) ⟨2797152, by rfl⟩ : syracuseStep 7459073 = 5594305) B5594305
theorem B2617607 : Blo 1744573 2617607 := bstep (se 1 (by rfl) ⟨1963205, by rfl⟩ : syracuseStep 2617607 = 3926411) B3926411
theorem B2617643 : Blo 1744573 2617643 := bstep (se 1 (by rfl) ⟨1963232, by rfl⟩ : syracuseStep 2617643 = 3926465) B3926465
theorem B2486585 : Blo 1744573 2486585 := bstep (se 2 (by rfl) ⟨932469, by rfl⟩ : syracuseStep 2486585 = 1864939) B1864939
theorem B2617673 : Blo 1744573 2617673 := bstep (se 2 (by rfl) ⟨981627, by rfl⟩ : syracuseStep 2617673 = 1963255) B1963255
theorem B5894585 : Blo 1744573 5894585 := bstep (se 2 (by rfl) ⟨2210469, by rfl⟩ : syracuseStep 5894585 = 4420939) B4420939
theorem B2617787 : Blo 1744573 2617787 := bstep (se 1 (by rfl) ⟨1963340, by rfl⟩ : syracuseStep 2617787 = 3926681) B3926681
theorem B2617847 : Blo 1744573 2617847 := bstep (se 1 (by rfl) ⟨1963385, by rfl⟩ : syracuseStep 2617847 = 3926771) B3926771
theorem B2617871 : Blo 1744573 2617871 := bstep (se 1 (by rfl) ⟨1963403, by rfl⟩ : syracuseStep 2617871 = 3926807) B3926807
theorem B2945551 : Blo 1744573 2945551 := bstep (se 1 (by rfl) ⟨2209163, by rfl⟩ : syracuseStep 2945551 = 4418327) B4418327
theorem B3314209 : Blo 1744573 3314209 := bstep (se 2 (by rfl) ⟨1242828, by rfl⟩ : syracuseStep 3314209 = 2485657) B2485657
theorem B4420129 : Blo 1744573 4420129 := bstep (se 2 (by rfl) ⟨1657548, by rfl⟩ : syracuseStep 4420129 = 3315097) B3315097
theorem B2617913 : Blo 1744573 2617913 := bstep (se 2 (by rfl) ⟨981717, by rfl⟩ : syracuseStep 2617913 = 1963435) B1963435
theorem B7459447 : Blo 1744573 7459447 := bstep (se 1 (by rfl) ⟨5594585, by rfl⟩ : syracuseStep 7459447 = 11189171) B11189171
theorem B2617991 : Blo 1744573 2617991 := bstep (se 1 (by rfl) ⟨1963493, by rfl⟩ : syracuseStep 2617991 = 3926987) B3926987
theorem B2618027 : Blo 1744573 2618027 := bstep (se 1 (by rfl) ⟨1963520, by rfl⟩ : syracuseStep 2618027 = 3927041) B3927041
theorem B2618057 : Blo 1744573 2618057 := bstep (se 2 (by rfl) ⟨981771, by rfl⟩ : syracuseStep 2618057 = 1963543) B1963543
theorem B18871001 : Blo 1744573 18871001 := bstep (se 2 (by rfl) ⟨7076625, by rfl⟩ : syracuseStep 18871001 = 14153251) B14153251
theorem B2618171 : Blo 1744573 2618171 := bstep (se 1 (by rfl) ⟨1963628, by rfl⟩ : syracuseStep 2618171 = 3927257) B3927257
theorem B2618231 : Blo 1744573 2618231 := bstep (se 1 (by rfl) ⟨1963673, by rfl⟩ : syracuseStep 2618231 = 3927347) B3927347
theorem B2208647 : Blo 1744573 2208647 := bstep (se 1 (by rfl) ⟨1656485, by rfl⟩ : syracuseStep 2208647 = 3312971) B3312971
theorem B3928967 : Blo 1744573 3928967 := bstep (se 1 (by rfl) ⟨2946725, by rfl⟩ : syracuseStep 3928967 = 5893451) B5893451
theorem B1962895 : Blo 1744573 1962895 := bstep (se 1 (by rfl) ⟨1472171, by rfl⟩ : syracuseStep 1962895 = 2944343) B2944343
theorem B2618255 : Blo 1744573 2618255 := bstep (se 1 (by rfl) ⟨1963691, by rfl⟩ : syracuseStep 2618255 = 3927383) B3927383
theorem B10621849 : Blo 1744573 10621849 := bstep (se 2 (by rfl) ⟨3983193, by rfl⟩ : syracuseStep 10621849 = 7966387) B7966387
theorem B2618297 : Blo 1744573 2618297 := bstep (se 2 (by rfl) ⟨981861, by rfl⟩ : syracuseStep 2618297 = 1963723) B1963723
theorem B2618375 : Blo 1744573 2618375 := bstep (se 1 (by rfl) ⟨1963781, by rfl⟩ : syracuseStep 2618375 = 3927563) B3927563
theorem B2618411 : Blo 1744573 2618411 := bstep (se 1 (by rfl) ⟨1963808, by rfl⟩ : syracuseStep 2618411 = 3927617) B3927617
theorem B2946091 : Blo 1744573 2946091 := bstep (se 1 (by rfl) ⟨2209568, by rfl⟩ : syracuseStep 2946091 = 4419137) B4419137
theorem B3929147 : Blo 1744573 3929147 := bstep (se 1 (by rfl) ⟨2946860, by rfl⟩ : syracuseStep 3929147 = 5893721) B5893721
theorem B5592125 : Blo 1744573 5592125 := bstep (se 3 (by rfl) ⟨1048523, by rfl⟩ : syracuseStep 5592125 = 2097047) B2097047
theorem B7558211 : Blo 1744573 7558211 := bstep (se 1 (by rfl) ⟨5668658, by rfl⟩ : syracuseStep 7558211 = 11337317) B11337317
theorem B2618441 : Blo 1744573 2618441 := bstep (se 2 (by rfl) ⟨981915, by rfl⟩ : syracuseStep 2618441 = 1963831) B1963831
theorem B785544277 : Blo 1744573 785544277 := bstep (se 8 (by rfl) ⟨4602798, by rfl⟩ : syracuseStep 785544277 = 9205597) B9205597
theorem B4420727 : Blo 1744573 4420727 := bstep (se 1 (by rfl) ⟨3315545, by rfl⟩ : syracuseStep 4420727 = 6631091) B6631091
theorem B2946233 : Blo 1744573 2946233 := bstep (se 2 (by rfl) ⟨1104837, by rfl⟩ : syracuseStep 2946233 = 2209675) B2209675
theorem B3929273 : Blo 1744573 3929273 := bstep (se 2 (by rfl) ⟨1473477, by rfl⟩ : syracuseStep 3929273 = 2946955) B2946955
theorem B2618555 : Blo 1744573 2618555 := bstep (se 1 (by rfl) ⟨1963916, by rfl⟩ : syracuseStep 2618555 = 3927833) B3927833
theorem B8836289 : Blo 1744573 8836289 := bstep (se 2 (by rfl) ⟨3313608, by rfl⟩ : syracuseStep 8836289 = 6627217) B6627217
theorem B2618615 : Blo 1744573 2618615 := bstep (se 1 (by rfl) ⟨1963961, by rfl⟩ : syracuseStep 2618615 = 3927923) B3927923
theorem B5969153 : Blo 1744573 5969153 := bstep (se 2 (by rfl) ⟨2238432, by rfl⟩ : syracuseStep 5969153 = 4476865) B4476865
theorem B2618639 : Blo 1744573 2618639 := bstep (se 1 (by rfl) ⟨1963979, by rfl⟩ : syracuseStep 2618639 = 3927959) B3927959
theorem B2618681 : Blo 1744573 2618681 := bstep (se 2 (by rfl) ⟨982005, by rfl⟩ : syracuseStep 2618681 = 1964011) B1964011
theorem B1963399 : Blo 1744573 1963399 := bstep (se 1 (by rfl) ⟨1472549, by rfl⟩ : syracuseStep 1963399 = 2945099) B2945099
theorem B2618759 : Blo 1744573 2618759 := bstep (se 1 (by rfl) ⟨1964069, by rfl⟩ : syracuseStep 2618759 = 3928139) B3928139
theorem B10614161 : Blo 1744573 10614161 := bstep (se 2 (by rfl) ⟨3980310, by rfl⟩ : syracuseStep 10614161 = 7960621) B7960621
theorem B2618795 : Blo 1744573 2618795 := bstep (se 1 (by rfl) ⟨1964096, by rfl⟩ : syracuseStep 2618795 = 3928193) B3928193
theorem B6714809 : Blo 1744573 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B2618825 : Blo 1744573 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B12588509 : Blo 1744573 12588509 := bstep (se 3 (by rfl) ⟨2360345, by rfl⟩ : syracuseStep 12588509 = 4720691) B4720691
theorem B2209295 : Blo 1744573 2209295 := bstep (se 1 (by rfl) ⟨1656971, by rfl⟩ : syracuseStep 2209295 = 3313943) B3313943
theorem B3929615 : Blo 1744573 3929615 := bstep (se 1 (by rfl) ⟨2947211, by rfl⟩ : syracuseStep 3929615 = 5894423) B5894423
theorem B16774685 : Blo 1744573 16774685 := bstep (se 3 (by rfl) ⟨3145253, by rfl⟩ : syracuseStep 16774685 = 6290507) B6290507
theorem B3929633 : Blo 1744573 3929633 := bstep (se 2 (by rfl) ⟨1473612, by rfl⟩ : syracuseStep 3929633 = 2947225) B2947225
theorem B1963579 : Blo 1744573 1963579 := bstep (se 1 (by rfl) ⟨1472684, by rfl⟩ : syracuseStep 1963579 = 2945369) B2945369
theorem B2618939 : Blo 1744573 2618939 := bstep (se 1 (by rfl) ⟨1964204, by rfl⟩ : syracuseStep 2618939 = 3928409) B3928409
theorem B2618999 : Blo 1744573 2618999 := bstep (se 1 (by rfl) ⟨1964249, by rfl⟩ : syracuseStep 2618999 = 3928499) B3928499
theorem B2619023 : Blo 1744573 2619023 := bstep (se 1 (by rfl) ⟨1964267, by rfl⟩ : syracuseStep 2619023 = 3928535) B3928535
theorem B2619065 : Blo 1744573 2619065 := bstep (se 2 (by rfl) ⟨982149, by rfl⟩ : syracuseStep 2619065 = 1964299) B1964299
theorem B3315401 : Blo 1744573 3315401 := bstep (se 2 (by rfl) ⟨1243275, by rfl⟩ : syracuseStep 3315401 = 2486551) B2486551
theorem B2619143 : Blo 1744573 2619143 := bstep (se 1 (by rfl) ⟨1964357, by rfl⟩ : syracuseStep 2619143 = 3928715) B3928715
theorem B2619179 : Blo 1744573 2619179 := bstep (se 1 (by rfl) ⟨1964384, by rfl⟩ : syracuseStep 2619179 = 3928769) B3928769
theorem B2619209 : Blo 1744573 2619209 := bstep (se 2 (by rfl) ⟨982203, by rfl⟩ : syracuseStep 2619209 = 1964407) B1964407
theorem B4192087 : Blo 1744573 4192087 := bstep (se 1 (by rfl) ⟨3144065, by rfl⟩ : syracuseStep 4192087 = 6288131) B6288131
theorem B2946935 : Blo 1744573 2946935 := bstep (se 1 (by rfl) ⟨2210201, by rfl⟩ : syracuseStep 2946935 = 4420403) B4420403
theorem B5175175 : Blo 1744573 5175175 := bstep (se 1 (by rfl) ⟨3881381, by rfl⟩ : syracuseStep 5175175 = 7762763) B7762763
theorem B14161817 : Blo 1744573 14161817 := bstep (se 2 (by rfl) ⟨5310681, by rfl⟩ : syracuseStep 14161817 = 10621363) B10621363
theorem B2619323 : Blo 1744573 2619323 := bstep (se 1 (by rfl) ⟨1964492, by rfl⟩ : syracuseStep 2619323 = 3928985) B3928985
theorem B2619383 : Blo 1744573 2619383 := bstep (se 1 (by rfl) ⟨1964537, by rfl⟩ : syracuseStep 2619383 = 3929075) B3929075
theorem B1964047 : Blo 1744573 1964047 := bstep (se 1 (by rfl) ⟨1473035, by rfl⟩ : syracuseStep 1964047 = 2946071) B2946071
theorem B2619407 : Blo 1744573 2619407 := bstep (se 1 (by rfl) ⟨1964555, by rfl⟩ : syracuseStep 2619407 = 3929111) B3929111
theorem B16766999 : Blo 1744573 16766999 := bstep (se 1 (by rfl) ⟨12575249, by rfl⟩ : syracuseStep 16766999 = 25150499) B25150499
theorem B2619449 : Blo 1744573 2619449 := bstep (se 2 (by rfl) ⟨982293, by rfl⟩ : syracuseStep 2619449 = 1964587) B1964587
theorem B2619527 : Blo 1744573 2619527 := bstep (se 1 (by rfl) ⟨1964645, by rfl⟩ : syracuseStep 2619527 = 3929291) B3929291
theorem B2619563 : Blo 1744573 2619563 := bstep (se 1 (by rfl) ⟨1964672, by rfl⟩ : syracuseStep 2619563 = 3929345) B3929345
theorem B9435329 : Blo 1744573 9435329 := bstep (se 2 (by rfl) ⟨3538248, by rfl⟩ : syracuseStep 9435329 = 7076497) B7076497
theorem B2619593 : Blo 1744573 2619593 := bstep (se 2 (by rfl) ⟨982347, by rfl⟩ : syracuseStep 2619593 = 1964695) B1964695
theorem B4970767 : Blo 1744573 4970767 := bstep (se 1 (by rfl) ⟨3728075, by rfl⟩ : syracuseStep 4970767 = 7456151) B7456151
theorem B3537211 : Blo 1744573 3537211 := bstep (se 1 (by rfl) ⟨2652908, by rfl⟩ : syracuseStep 3537211 = 5305817) B5305817
theorem B5970235 : Blo 1744573 5970235 := bstep (se 1 (by rfl) ⟨4477676, by rfl⟩ : syracuseStep 5970235 = 8955353) B8955353
theorem B2619707 : Blo 1744573 2619707 := bstep (se 1 (by rfl) ⟨1964780, by rfl⟩ : syracuseStep 2619707 = 3929561) B3929561
theorem B2619767 : Blo 1744573 2619767 := bstep (se 1 (by rfl) ⟨1964825, by rfl⟩ : syracuseStep 2619767 = 3929651) B3929651
theorem B18864515 : Blo 1744573 18864515 := bstep (se 1 (by rfl) ⟨14148386, by rfl⟩ : syracuseStep 18864515 = 28296773) B28296773
theorem B3979655 : Blo 1744573 3979655 := bstep (se 1 (by rfl) ⟨2984741, by rfl⟩ : syracuseStep 3979655 = 5969483) B5969483
theorem B2619791 : Blo 1744573 2619791 := bstep (se 1 (by rfl) ⟨1964843, by rfl⟩ : syracuseStep 2619791 = 3929687) B3929687
theorem B2619833 : Blo 1744573 2619833 := bstep (se 2 (by rfl) ⟨982437, by rfl⟩ : syracuseStep 2619833 = 1964875) B1964875
theorem B6625745 : Blo 1744573 6625745 := bstep (se 2 (by rfl) ⟨2484654, by rfl⟩ : syracuseStep 6625745 = 4969309) B4969309
theorem B8837585 : Blo 1744573 8837585 := bstep (se 2 (by rfl) ⟨3314094, by rfl⟩ : syracuseStep 8837585 = 6628189) B6628189
theorem B1964551 : Blo 1744573 1964551 := bstep (se 1 (by rfl) ⟨1473413, by rfl⟩ : syracuseStep 1964551 = 2946827) B2946827
theorem B4971041 : Blo 1744573 4971041 := bstep (se 2 (by rfl) ⟨1864140, by rfl⟩ : syracuseStep 4971041 = 3728281) B3728281
theorem B11180663 : Blo 1744573 11180663 := bstep (se 1 (by rfl) ⟨8385497, by rfl⟩ : syracuseStep 11180663 = 16770995) B16770995
theorem B1964731 : Blo 1744573 1964731 := bstep (se 1 (by rfl) ⟨1473548, by rfl⟩ : syracuseStep 1964731 = 2947097) B2947097
theorem B6626063 : Blo 1744573 6626063 := bstep (se 1 (by rfl) ⟨4969547, by rfl⟩ : syracuseStep 6626063 = 9939095) B9939095
theorem B3144491 : Blo 1744573 3144491 := bstep (se 1 (by rfl) ⟨2358368, by rfl⟩ : syracuseStep 3144491 = 4716737) B4716737
theorem B5888915 : Blo 1744573 5888915 := bstep (se 1 (by rfl) ⟨4416686, by rfl⟩ : syracuseStep 5888915 = 8833373) B8833373
theorem B8387651 : Blo 1744573 8387651 := bstep (se 1 (by rfl) ⟨6290738, by rfl⟩ : syracuseStep 8387651 = 12581477) B12581477
theorem B2358443 : Blo 1744573 2358443 := bstep (se 1 (by rfl) ⟨1768832, by rfl⟩ : syracuseStep 2358443 = 3537665) B3537665
theorem B9936179 : Blo 1744573 9936179 := bstep (se 1 (by rfl) ⟨7452134, by rfl⟩ : syracuseStep 9936179 = 14904269) B14904269
theorem B5594483 : Blo 1744573 5594483 := bstep (se 1 (by rfl) ⟨4195862, by rfl⟩ : syracuseStep 5594483 = 8391725) B8391725
theorem B4972043 : Blo 1744573 4972043 := bstep (se 1 (by rfl) ⟨3729032, by rfl⟩ : syracuseStep 4972043 = 7458065) B7458065
theorem B2358919 : Blo 1744573 2358919 := bstep (se 1 (by rfl) ⟨1769189, by rfl⟩ : syracuseStep 2358919 = 3538379) B3538379
theorem B15933185 : Blo 1744573 15933185 := bstep (se 2 (by rfl) ⟨5974944, by rfl⟩ : syracuseStep 15933185 = 11949889) B11949889
theorem B1744647 : Blo 1744573 1744647 := bstep (se 1 (by rfl) ⟨1308485, by rfl⟩ : syracuseStep 1744647 = 2616971) B2616971
theorem B1744655 : Blo 1744573 1744655 := bstep (se 1 (by rfl) ⟨1308491, by rfl⟩ : syracuseStep 1744655 = 2616983) B2616983
theorem B14917391 : Blo 1744573 14917391 := bstep (se 1 (by rfl) ⟨11188043, by rfl⟩ : syracuseStep 14917391 = 22376087) B22376087
theorem B1744699 : Blo 1744573 1744699 := bstep (se 1 (by rfl) ⟨1308524, by rfl⟩ : syracuseStep 1744699 = 2617049) B2617049
theorem B19890035 : Blo 1744573 19890035 := bstep (se 1 (by rfl) ⟨14917526, by rfl⟩ : syracuseStep 19890035 = 29835053) B29835053
theorem B1744775 : Blo 1744573 1744775 := bstep (se 1 (by rfl) ⟨1308581, by rfl⟩ : syracuseStep 1744775 = 2617163) B2617163
theorem B1769351 : Blo 1744573 1769351 := bstep (se 1 (by rfl) ⟨1327013, by rfl⟩ : syracuseStep 1769351 = 2654027) B2654027
theorem B1744783 : Blo 1744573 1744783 := bstep (se 1 (by rfl) ⟨1308587, by rfl⟩ : syracuseStep 1744783 = 2617175) B2617175
theorem B4972441 : Blo 1744573 4972441 := bstep (se 2 (by rfl) ⟨1864665, by rfl⟩ : syracuseStep 4972441 = 3729331) B3729331
theorem B1744827 : Blo 1744573 1744827 := bstep (se 1 (by rfl) ⟨1308620, by rfl⟩ : syracuseStep 1744827 = 2617241) B2617241
theorem B12582859 : Blo 1744573 12582859 := bstep (se 1 (by rfl) ⟨9437144, by rfl⟩ : syracuseStep 12582859 = 18874289) B18874289
theorem B5890049 : Blo 1744573 5890049 := bstep (se 2 (by rfl) ⟨2208768, by rfl⟩ : syracuseStep 5890049 = 4417537) B4417537
theorem B1744935 : Blo 1744573 1744935 := bstep (se 1 (by rfl) ⟨1308701, by rfl⟩ : syracuseStep 1744935 = 2617403) B2617403
theorem B1744975 : Blo 1744573 1744975 := bstep (se 1 (by rfl) ⟨1308731, by rfl⟩ : syracuseStep 1744975 = 2617463) B2617463
theorem B16777297 : Blo 1744573 16777297 := bstep (se 2 (by rfl) ⟨6291486, by rfl⟩ : syracuseStep 16777297 = 12582973) B12582973
theorem B1744991 : Blo 1744573 1744991 := bstep (se 1 (by rfl) ⟨1308743, by rfl⟩ : syracuseStep 1744991 = 2617487) B2617487
theorem B1745019 : Blo 1744573 1745019 := bstep (se 1 (by rfl) ⟨1308764, by rfl⟩ : syracuseStep 1745019 = 2617529) B2617529
theorem B56615075 : Blo 1744573 56615075 := bstep (se 1 (by rfl) ⟨42461306, by rfl⟩ : syracuseStep 56615075 = 84922613) B84922613
theorem B4972715 : Blo 1744573 4972715 := bstep (se 1 (by rfl) ⟨3729536, by rfl⟩ : syracuseStep 4972715 = 7459073) B7459073
theorem B1745071 : Blo 1744573 1745071 := bstep (se 1 (by rfl) ⟨1308803, by rfl⟩ : syracuseStep 1745071 = 2617607) B2617607
theorem B1745095 : Blo 1744573 1745095 := bstep (se 1 (by rfl) ⟨1308821, by rfl⟩ : syracuseStep 1745095 = 2617643) B2617643
theorem B1745115 : Blo 1744573 1745115 := bstep (se 1 (by rfl) ⟨1308836, by rfl⟩ : syracuseStep 1745115 = 2617673) B2617673
theorem B14909669 : Blo 1744573 14909669 := bstep (se 4 (by rfl) ⟨1397781, by rfl⟩ : syracuseStep 14909669 = 2795563) B2795563
theorem B1745191 : Blo 1744573 1745191 := bstep (se 1 (by rfl) ⟨1308893, by rfl⟩ : syracuseStep 1745191 = 2617787) B2617787
theorem B1745231 : Blo 1744573 1745231 := bstep (se 1 (by rfl) ⟨1308923, by rfl⟩ : syracuseStep 1745231 = 2617847) B2617847
theorem B1745247 : Blo 1744573 1745247 := bstep (se 1 (by rfl) ⟨1308935, by rfl⟩ : syracuseStep 1745247 = 2617871) B2617871
theorem B6627689 : Blo 1744573 6627689 := bstep (se 2 (by rfl) ⟨2485383, by rfl⟩ : syracuseStep 6627689 = 4970767) B4970767
theorem B8839529 : Blo 1744573 8839529 := bstep (se 2 (by rfl) ⟨3314823, by rfl⟩ : syracuseStep 8839529 = 6629647) B6629647
theorem B1745275 : Blo 1744573 1745275 := bstep (se 1 (by rfl) ⟨1308956, by rfl⟩ : syracuseStep 1745275 = 2617913) B2617913
theorem B1745327 : Blo 1744573 1745327 := bstep (se 1 (by rfl) ⟨1308995, by rfl⟩ : syracuseStep 1745327 = 2617991) B2617991
theorem B1745351 : Blo 1744573 1745351 := bstep (se 1 (by rfl) ⟨1309013, by rfl⟩ : syracuseStep 1745351 = 2618027) B2618027
theorem B1745371 : Blo 1744573 1745371 := bstep (se 1 (by rfl) ⟨1309028, by rfl⟩ : syracuseStep 1745371 = 2618057) B2618057
theorem B1745447 : Blo 1744573 1745447 := bstep (se 1 (by rfl) ⟨1309085, by rfl⟩ : syracuseStep 1745447 = 2618171) B2618171
theorem B1745487 : Blo 1744573 1745487 := bstep (se 1 (by rfl) ⟨1309115, by rfl⟩ : syracuseStep 1745487 = 2618231) B2618231
theorem B1745503 : Blo 1744573 1745503 := bstep (se 1 (by rfl) ⟨1309127, by rfl⟩ : syracuseStep 1745503 = 2618255) B2618255
theorem B1745531 : Blo 1744573 1745531 := bstep (se 1 (by rfl) ⟨1309148, by rfl⟩ : syracuseStep 1745531 = 2618297) B2618297
theorem B1745583 : Blo 1744573 1745583 := bstep (se 1 (by rfl) ⟨1309187, by rfl⟩ : syracuseStep 1745583 = 2618375) B2618375
theorem B1745607 : Blo 1744573 1745607 := bstep (se 1 (by rfl) ⟨1309205, by rfl⟩ : syracuseStep 1745607 = 2618411) B2618411
theorem B5038807 : Blo 1744573 5038807 := bstep (se 1 (by rfl) ⟨3779105, by rfl⟩ : syracuseStep 5038807 = 7558211) B7558211
theorem B1745627 : Blo 1744573 1745627 := bstep (se 1 (by rfl) ⟨1309220, by rfl⟩ : syracuseStep 1745627 = 2618441) B2618441
theorem B1745703 : Blo 1744573 1745703 := bstep (se 1 (by rfl) ⟨1309277, by rfl⟩ : syracuseStep 1745703 = 2618555) B2618555
theorem B5890859 : Blo 1744573 5890859 := bstep (se 1 (by rfl) ⟨4418144, by rfl⟩ : syracuseStep 5890859 = 8836289) B8836289
theorem B9945929 : Blo 1744573 9945929 := bstep (se 2 (by rfl) ⟨3729723, by rfl⟩ : syracuseStep 9945929 = 7459447) B7459447
theorem B1745743 : Blo 1744573 1745743 := bstep (se 1 (by rfl) ⟨1309307, by rfl⟩ : syracuseStep 1745743 = 2618615) B2618615
theorem B1745759 : Blo 1744573 1745759 := bstep (se 1 (by rfl) ⟨1309319, by rfl⟩ : syracuseStep 1745759 = 2618639) B2618639
theorem B1745787 : Blo 1744573 1745787 := bstep (se 1 (by rfl) ⟨1309340, by rfl⟩ : syracuseStep 1745787 = 2618681) B2618681
theorem B1745839 : Blo 1744573 1745839 := bstep (se 1 (by rfl) ⟨1309379, by rfl⟩ : syracuseStep 1745839 = 2618759) B2618759
theorem B4195247 : Blo 1744573 4195247 := bstep (se 1 (by rfl) ⟨3146435, by rfl⟩ : syracuseStep 4195247 = 6292871) B6292871
theorem B1745863 : Blo 1744573 1745863 := bstep (se 1 (by rfl) ⟨1309397, by rfl⟩ : syracuseStep 1745863 = 2618795) B2618795
theorem B1745883 : Blo 1744573 1745883 := bstep (se 1 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 1745883 = 2618825) B2618825
theorem B11183123 : Blo 1744573 11183123 := bstep (se 1 (by rfl) ⟨8387342, by rfl⟩ : syracuseStep 11183123 = 16774685) B16774685
theorem B1745959 : Blo 1744573 1745959 := bstep (se 1 (by rfl) ⟨1309469, by rfl⟩ : syracuseStep 1745959 = 2618939) B2618939
theorem B5891129 : Blo 1744573 5891129 := bstep (se 2 (by rfl) ⟨2209173, by rfl⟩ : syracuseStep 5891129 = 4418347) B4418347
theorem B1745999 : Blo 1744573 1745999 := bstep (se 1 (by rfl) ⟨1309499, by rfl⟩ : syracuseStep 1745999 = 2618999) B2618999
theorem B3277903 : Blo 1744573 3277903 := bstep (se 1 (by rfl) ⟨2458427, by rfl⟩ : syracuseStep 3277903 = 4916855) B4916855
theorem B1746015 : Blo 1744573 1746015 := bstep (se 1 (by rfl) ⟨1309511, by rfl⟩ : syracuseStep 1746015 = 2619023) B2619023
theorem B1746043 : Blo 1744573 1746043 := bstep (se 1 (by rfl) ⟨1309532, by rfl⟩ : syracuseStep 1746043 = 2619065) B2619065
theorem B1746095 : Blo 1744573 1746095 := bstep (se 1 (by rfl) ⟨1309571, by rfl⟩ : syracuseStep 1746095 = 2619143) B2619143
theorem B1746119 : Blo 1744573 1746119 := bstep (se 1 (by rfl) ⟨1309589, by rfl⟩ : syracuseStep 1746119 = 2619179) B2619179
theorem B1746139 : Blo 1744573 1746139 := bstep (se 1 (by rfl) ⟨1309604, by rfl⟩ : syracuseStep 1746139 = 2619209) B2619209
theorem B36308209 : Blo 1744573 36308209 := bstep (se 2 (by rfl) ⟨13615578, by rfl⟩ : syracuseStep 36308209 = 27231157) B27231157
theorem B1746215 : Blo 1744573 1746215 := bstep (se 1 (by rfl) ⟨1309661, by rfl⟩ : syracuseStep 1746215 = 2619323) B2619323
theorem B1746255 : Blo 1744573 1746255 := bstep (se 1 (by rfl) ⟨1309691, by rfl⟩ : syracuseStep 1746255 = 2619383) B2619383
theorem B1746271 : Blo 1744573 1746271 := bstep (se 1 (by rfl) ⟨1309703, by rfl⟩ : syracuseStep 1746271 = 2619407) B2619407
theorem B1746299 : Blo 1744573 1746299 := bstep (se 1 (by rfl) ⟨1309724, by rfl⟩ : syracuseStep 1746299 = 2619449) B2619449
theorem B5891453 : Blo 1744573 5891453 := bstep (se 3 (by rfl) ⟨1104647, by rfl⟩ : syracuseStep 5891453 = 2209295) B2209295
theorem B1746351 : Blo 1744573 1746351 := bstep (se 1 (by rfl) ⟨1309763, by rfl⟩ : syracuseStep 1746351 = 2619527) B2619527
theorem B1746375 : Blo 1744573 1746375 := bstep (se 1 (by rfl) ⟨1309781, by rfl⟩ : syracuseStep 1746375 = 2619563) B2619563
theorem B1746395 : Blo 1744573 1746395 := bstep (se 1 (by rfl) ⟨1309796, by rfl⟩ : syracuseStep 1746395 = 2619593) B2619593
theorem B1746471 : Blo 1744573 1746471 := bstep (se 1 (by rfl) ⟨1309853, by rfl⟩ : syracuseStep 1746471 = 2619707) B2619707
theorem B1746511 : Blo 1744573 1746511 := bstep (se 1 (by rfl) ⟨1309883, by rfl⟩ : syracuseStep 1746511 = 2619767) B2619767
theorem B1746527 : Blo 1744573 1746527 := bstep (se 1 (by rfl) ⟨1309895, by rfl⟩ : syracuseStep 1746527 = 2619791) B2619791
theorem B3925601 : Blo 1744573 3925601 := bstep (se 2 (by rfl) ⟨1472100, by rfl⟩ : syracuseStep 3925601 = 2944201) B2944201
theorem B1746555 : Blo 1744573 1746555 := bstep (se 1 (by rfl) ⟨1309916, by rfl⟩ : syracuseStep 1746555 = 2619833) B2619833
theorem B4417163 : Blo 1744573 4417163 := bstep (se 1 (by rfl) ⟨3312872, by rfl⟩ : syracuseStep 4417163 = 6625745) B6625745
theorem B5891723 : Blo 1744573 5891723 := bstep (se 1 (by rfl) ⟨4418792, by rfl⟩ : syracuseStep 5891723 = 8837585) B8837585
theorem B28313381 : Blo 1744573 28313381 := bstep (se 4 (by rfl) ⟨2654379, by rfl⟩ : syracuseStep 28313381 = 5308759) B5308759
theorem B6293321 : Blo 1744573 6293321 := bstep (se 2 (by rfl) ⟨2359995, by rfl⟩ : syracuseStep 6293321 = 4719991) B4719991
theorem B4417375 : Blo 1744573 4417375 := bstep (se 1 (by rfl) ⟨3313031, by rfl⟩ : syracuseStep 4417375 = 6626063) B6626063
theorem B8832887 : Blo 1744573 8832887 := bstep (se 1 (by rfl) ⟨6624665, by rfl⟩ : syracuseStep 8832887 = 13249331) B13249331
theorem B67119029 : Blo 1744573 67119029 := bstep (se 5 (by rfl) ⟨3146204, by rfl⟩ : syracuseStep 67119029 = 6292409) B6292409
theorem B3925943 : Blo 1744573 3925943 := bstep (se 1 (by rfl) ⟨2944457, by rfl⟩ : syracuseStep 3925943 = 5888915) B5888915
theorem B3729655 : Blo 1744573 3729655 := bstep (se 1 (by rfl) ⟨2797241, by rfl⟩ : syracuseStep 3729655 = 5594483) B5594483
theorem B5589449 : Blo 1744573 5589449 := bstep (se 2 (by rfl) ⟨2096043, by rfl⟩ : syracuseStep 5589449 = 4192087) B4192087
theorem B6900233 : Blo 1744573 6900233 := bstep (se 2 (by rfl) ⟨2587587, by rfl⟩ : syracuseStep 6900233 = 5175175) B5175175
theorem B3926537 : Blo 1744573 3926537 := bstep (se 2 (by rfl) ⟨1472451, by rfl⟩ : syracuseStep 3926537 = 2944903) B2944903
theorem B5892641 : Blo 1744573 5892641 := bstep (se 2 (by rfl) ⟨2209740, by rfl⟩ : syracuseStep 5892641 = 4419481) B4419481
theorem B6629921 : Blo 1744573 6629921 := bstep (se 2 (by rfl) ⟨2486220, by rfl⟩ : syracuseStep 6629921 = 4972441) B4972441
theorem B4418297 : Blo 1744573 4418297 := bstep (se 2 (by rfl) ⟨1656861, by rfl⟩ : syracuseStep 4418297 = 3313723) B3313723
theorem B5892857 : Blo 1744573 5892857 := bstep (se 2 (by rfl) ⟨2209821, by rfl⟩ : syracuseStep 5892857 = 4419643) B4419643
theorem B25168715 : Blo 1744573 25168715 := bstep (se 1 (by rfl) ⟨18876536, by rfl⟩ : syracuseStep 25168715 = 37753073) B37753073
theorem B14912333 : Blo 1744573 14912333 := bstep (se 3 (by rfl) ⟨2796062, by rfl⟩ : syracuseStep 14912333 = 5592125) B5592125
theorem B3926879 : Blo 1744573 3926879 := bstep (se 1 (by rfl) ⟨2945159, by rfl⟩ : syracuseStep 3926879 = 5890319) B5890319
theorem B12577643 : Blo 1744573 12577643 := bstep (se 1 (by rfl) ⟨9433232, by rfl⟩ : syracuseStep 12577643 = 18866465) B18866465
theorem B5893127 : Blo 1744573 5893127 := bstep (se 1 (by rfl) ⟨4419845, by rfl⟩ : syracuseStep 5893127 = 8839691) B8839691
theorem B6630407 : Blo 1744573 6630407 := bstep (se 1 (by rfl) ⟨4972805, by rfl⟩ : syracuseStep 6630407 = 9945611) B9945611
theorem B3927059 : Blo 1744573 3927059 := bstep (se 1 (by rfl) ⟨2945294, by rfl⟩ : syracuseStep 3927059 = 5890589) B5890589
theorem B2944039 : Blo 1744573 2944039 := bstep (se 1 (by rfl) ⟨2208029, by rfl⟩ : syracuseStep 2944039 = 4416059) B4416059
theorem B3779641 : Blo 1744573 3779641 := bstep (se 2 (by rfl) ⟨1417365, by rfl⟩ : syracuseStep 3779641 = 2834731) B2834731
theorem B2796601 : Blo 1744573 2796601 := bstep (se 2 (by rfl) ⟨1048725, by rfl⟩ : syracuseStep 2796601 = 2097451) B2097451
theorem B5893235 : Blo 1744573 5893235 := bstep (se 1 (by rfl) ⟨4419926, by rfl⟩ : syracuseStep 5893235 = 8839853) B8839853
theorem B2796743 : Blo 1744573 2796743 := bstep (se 1 (by rfl) ⟨2097557, by rfl⟩ : syracuseStep 2796743 = 4195115) B4195115
theorem B3313001 : Blo 1744573 3313001 := bstep (se 2 (by rfl) ⟨1242375, by rfl⟩ : syracuseStep 3313001 = 2484751) B2484751
theorem B2944363 : Blo 1744573 2944363 := bstep (se 1 (by rfl) ⟨2208272, by rfl⟩ : syracuseStep 2944363 = 4416545) B4416545
theorem B3927401 : Blo 1744573 3927401 := bstep (se 2 (by rfl) ⟨1472775, by rfl⟩ : syracuseStep 3927401 = 2945551) B2945551
theorem B23883133 : Blo 1744573 23883133 := bstep (se 3 (by rfl) ⟨4478087, by rfl⟩ : syracuseStep 23883133 = 8956175) B8956175
theorem B4418945 : Blo 1744573 4418945 := bstep (se 2 (by rfl) ⟨1657104, by rfl⟩ : syracuseStep 4418945 = 3314209) B3314209
theorem B5893505 : Blo 1744573 5893505 := bstep (se 2 (by rfl) ⟨2210064, by rfl⟩ : syracuseStep 5893505 = 4420129) B4420129
theorem B10071469 : Blo 1744573 10071469 := bstep (se 3 (by rfl) ⟨1888400, by rfl⟩ : syracuseStep 10071469 = 3776801) B3776801
theorem B6630893 : Blo 1744573 6630893 := bstep (se 3 (by rfl) ⟨1243292, by rfl⟩ : syracuseStep 6630893 = 2486585) B2486585
theorem B50998859 : Blo 1744573 50998859 := bstep (se 1 (by rfl) ⟨38249144, by rfl⟩ : syracuseStep 50998859 = 76498289) B76498289
theorem B2616911 : Blo 1744573 2616911 := bstep (se 1 (by rfl) ⟨1962683, by rfl⟩ : syracuseStep 2616911 = 3925367) B3925367
theorem B4476539 : Blo 1744573 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B8392339 : Blo 1744573 8392339 := bstep (se 1 (by rfl) ⟨6294254, by rfl⟩ : syracuseStep 8392339 = 12588509) B12588509
theorem B4968125 : Blo 1744573 4968125 := bstep (se 3 (by rfl) ⟨931523, by rfl⟩ : syracuseStep 4968125 = 1863047) B1863047
theorem B2617031 : Blo 1744573 2617031 := bstep (se 1 (by rfl) ⟨1962773, by rfl⟩ : syracuseStep 2617031 = 3925547) B3925547
theorem B2617193 : Blo 1744573 2617193 := bstep (se 2 (by rfl) ⟨981447, by rfl⟩ : syracuseStep 2617193 = 1962895) B1962895
theorem B2617271 : Blo 1744573 2617271 := bstep (se 1 (by rfl) ⟨1962953, by rfl⟩ : syracuseStep 2617271 = 3925907) B3925907
theorem B7172027 : Blo 1744573 7172027 := bstep (se 1 (by rfl) ⟨5379020, by rfl⟩ : syracuseStep 7172027 = 10758041) B10758041
theorem B3927995 : Blo 1744573 3927995 := bstep (se 1 (by rfl) ⟨2945996, by rfl⟩ : syracuseStep 3927995 = 5891993) B5891993
theorem B9441211 : Blo 1744573 9441211 := bstep (se 1 (by rfl) ⟨7080908, by rfl⟩ : syracuseStep 9441211 = 14161817) B14161817
theorem B2617307 : Blo 1744573 2617307 := bstep (se 1 (by rfl) ⟨1962980, by rfl⟩ : syracuseStep 2617307 = 3925961) B3925961
theorem B11177999 : Blo 1744573 11177999 := bstep (se 1 (by rfl) ⟨8383499, by rfl⟩ : syracuseStep 11177999 = 16766999) B16766999
theorem B3928121 : Blo 1744573 3928121 := bstep (se 2 (by rfl) ⟨1473045, by rfl⟩ : syracuseStep 3928121 = 2946091) B2946091
theorem B1047392369 : Blo 1744573 1047392369 := bstep (se 2 (by rfl) ⟨392772138, by rfl⟩ : syracuseStep 1047392369 = 785544277) B785544277
theorem B4419755 : Blo 1744573 4419755 := bstep (se 1 (by rfl) ⟨3314816, by rfl⟩ : syracuseStep 4419755 = 6629633) B6629633
theorem B5894315 : Blo 1744573 5894315 := bstep (se 1 (by rfl) ⟨4420736, by rfl⟩ : syracuseStep 5894315 = 8841473) B8841473
theorem B13250789 : Blo 1744573 13250789 := bstep (se 4 (by rfl) ⟨1242261, by rfl⟩ : syracuseStep 13250789 = 2484523) B2484523
theorem B3314027 : Blo 1744573 3314027 := bstep (se 1 (by rfl) ⟨2485520, by rfl⟩ : syracuseStep 3314027 = 4971041) B4971041
theorem B2945423 : Blo 1744573 2945423 := bstep (se 1 (by rfl) ⟨2209067, by rfl⟩ : syracuseStep 2945423 = 4418135) B4418135
theorem B3928463 : Blo 1744573 3928463 := bstep (se 1 (by rfl) ⟨2946347, by rfl⟩ : syracuseStep 3928463 = 5892695) B5892695
theorem B2617775 : Blo 1744573 2617775 := bstep (se 1 (by rfl) ⟨1963331, by rfl⟩ : syracuseStep 2617775 = 3926663) B3926663
theorem B2617865 : Blo 1744573 2617865 := bstep (se 2 (by rfl) ⟨981699, by rfl⟩ : syracuseStep 2617865 = 1963399) B1963399
theorem B11186711 : Blo 1744573 11186711 := bstep (se 1 (by rfl) ⟨8390033, by rfl⟩ : syracuseStep 11186711 = 16780067) B16780067
theorem B2617895 : Blo 1744573 2617895 := bstep (se 1 (by rfl) ⟨1963421, by rfl⟩ : syracuseStep 2617895 = 3926843) B3926843
theorem B71692867 : Blo 1744573 71692867 := bstep (se 1 (by rfl) ⟨53769650, by rfl⟩ : syracuseStep 71692867 = 107539301) B107539301
theorem B2208379 : Blo 1744573 2208379 := bstep (se 1 (by rfl) ⟨1656284, by rfl⟩ : syracuseStep 2208379 = 3312569) B3312569
theorem B2617979 : Blo 1744573 2617979 := bstep (se 1 (by rfl) ⟨1963484, by rfl⟩ : syracuseStep 2617979 = 3926969) B3926969
theorem B2945659 : Blo 1744573 2945659 := bstep (se 1 (by rfl) ⟨2209244, by rfl⟩ : syracuseStep 2945659 = 4418489) B4418489
theorem B1864315 : Blo 1744573 1864315 := bstep (se 1 (by rfl) ⟨1398236, by rfl⟩ : syracuseStep 1864315 = 2796473) B2796473
theorem B107492021 : Blo 1744573 107492021 := bstep (se 5 (by rfl) ⟨5038688, by rfl⟩ : syracuseStep 107492021 = 10077377) B10077377
theorem B3928787 : Blo 1744573 3928787 := bstep (se 1 (by rfl) ⟨2946590, by rfl⟩ : syracuseStep 3928787 = 5893181) B5893181
theorem B5591767 : Blo 1744573 5591767 := bstep (se 1 (by rfl) ⟨4193825, by rfl⟩ : syracuseStep 5591767 = 8387651) B8387651
theorem B2618105 : Blo 1744573 2618105 := bstep (se 2 (by rfl) ⟨981789, by rfl⟩ : syracuseStep 2618105 = 1963579) B1963579
theorem B2618207 : Blo 1744573 2618207 := bstep (se 1 (by rfl) ⟨1963655, by rfl⟩ : syracuseStep 2618207 = 3927311) B3927311
theorem B2618219 : Blo 1744573 2618219 := bstep (se 1 (by rfl) ⟨1963664, by rfl⟩ : syracuseStep 2618219 = 3927329) B3927329
theorem B6624119 : Blo 1744573 6624119 := bstep (se 1 (by rfl) ⟨4968089, by rfl⟩ : syracuseStep 6624119 = 9936179) B9936179
theorem B11187173 : Blo 1744573 11187173 := bstep (se 4 (by rfl) ⟨1048797, by rfl⟩ : syracuseStep 11187173 = 2097595) B2097595
theorem B3314695 : Blo 1744573 3314695 := bstep (se 1 (by rfl) ⟨2486021, by rfl⟩ : syracuseStep 3314695 = 4972043) B4972043
theorem B4420615 : Blo 1744573 4420615 := bstep (se 1 (by rfl) ⟨3315461, by rfl⟩ : syracuseStep 4420615 = 6630923) B6630923
theorem B2618447 : Blo 1744573 2618447 := bstep (se 1 (by rfl) ⟨1963835, by rfl⟩ : syracuseStep 2618447 = 3927671) B3927671
theorem B96859223 : Blo 1744573 96859223 := bstep (se 1 (by rfl) ⟨72644417, by rfl⟩ : syracuseStep 96859223 = 145288835) B145288835
theorem B10622123 : Blo 1744573 10622123 := bstep (se 1 (by rfl) ⟨7966592, by rfl⟩ : syracuseStep 10622123 = 15933185) B15933185
theorem B2618567 : Blo 1744573 2618567 := bstep (se 1 (by rfl) ⟨1963925, by rfl⟩ : syracuseStep 2618567 = 3927851) B3927851
theorem B9942263 : Blo 1744573 9942263 := bstep (se 1 (by rfl) ⟨7456697, by rfl⟩ : syracuseStep 9942263 = 14913395) B14913395
theorem B13260023 : Blo 1744573 13260023 := bstep (se 1 (by rfl) ⟨9945017, by rfl⟩ : syracuseStep 13260023 = 19890035) B19890035
theorem B2618729 : Blo 1744573 2618729 := bstep (se 2 (by rfl) ⟨982023, by rfl⟩ : syracuseStep 2618729 = 1964047) B1964047
theorem B2618807 : Blo 1744573 2618807 := bstep (se 1 (by rfl) ⟨1964105, by rfl⟩ : syracuseStep 2618807 = 3928211) B3928211
theorem B2618843 : Blo 1744573 2618843 := bstep (se 1 (by rfl) ⟨1964132, by rfl⟩ : syracuseStep 2618843 = 3928265) B3928265
theorem B2946523 : Blo 1744573 2946523 := bstep (se 1 (by rfl) ⟨2209892, by rfl⟩ : syracuseStep 2946523 = 4419785) B4419785
theorem B3929723 : Blo 1744573 3929723 := bstep (se 1 (by rfl) ⟨2947292, by rfl⟩ : syracuseStep 3929723 = 5894585) B5894585
theorem B8066699 : Blo 1744573 8066699 := bstep (se 1 (by rfl) ⟨6050024, by rfl⟩ : syracuseStep 8066699 = 12100049) B12100049
theorem B19388119 : Blo 1744573 19388119 := bstep (se 1 (by rfl) ⟨14541089, by rfl⟩ : syracuseStep 19388119 = 29082179) B29082179
theorem B13260509 : Blo 1744573 13260509 := bstep (se 3 (by rfl) ⟨2486345, by rfl⟩ : syracuseStep 13260509 = 4972691) B4972691
theorem B4716281 : Blo 1744573 4716281 := bstep (se 2 (by rfl) ⟨1768605, by rfl⟩ : syracuseStep 4716281 = 3537211) B3537211
theorem B7960313 : Blo 1744573 7960313 := bstep (se 2 (by rfl) ⟨2985117, by rfl⟩ : syracuseStep 7960313 = 5970235) B5970235
theorem B6289181 : Blo 1744573 6289181 := bstep (se 3 (by rfl) ⟨1179221, by rfl⟩ : syracuseStep 6289181 = 2358443) B2358443
theorem B12580667 : Blo 1744573 12580667 := bstep (se 1 (by rfl) ⟨9435500, by rfl⟩ : syracuseStep 12580667 = 18871001) B18871001
theorem B6625091 : Blo 1744573 6625091 := bstep (se 1 (by rfl) ⟨4968818, by rfl⟩ : syracuseStep 6625091 = 9937637) B9937637
theorem B2619311 : Blo 1744573 2619311 := bstep (se 1 (by rfl) ⟨1964483, by rfl⟩ : syracuseStep 2619311 = 3928967) B3928967
theorem B2619401 : Blo 1744573 2619401 := bstep (se 2 (by rfl) ⟨982275, by rfl⟩ : syracuseStep 2619401 = 1964551) B1964551
theorem B2619431 : Blo 1744573 2619431 := bstep (se 1 (by rfl) ⟨1964573, by rfl⟩ : syracuseStep 2619431 = 3929147) B3929147
theorem B2947151 : Blo 1744573 2947151 := bstep (se 1 (by rfl) ⟨2210363, by rfl⟩ : syracuseStep 2947151 = 4420727) B4420727
theorem B1964155 : Blo 1744573 1964155 := bstep (se 1 (by rfl) ⟨1473116, by rfl⟩ : syracuseStep 1964155 = 2946233) B2946233
theorem B2619515 : Blo 1744573 2619515 := bstep (se 1 (by rfl) ⟨1964636, by rfl⟩ : syracuseStep 2619515 = 3929273) B3929273
theorem B3979435 : Blo 1744573 3979435 := bstep (se 1 (by rfl) ⟨2984576, by rfl⟩ : syracuseStep 3979435 = 5969153) B5969153
theorem B2619641 : Blo 1744573 2619641 := bstep (se 2 (by rfl) ⟨982365, by rfl⟩ : syracuseStep 2619641 = 1964731) B1964731
theorem B5888267 : Blo 1744573 5888267 := bstep (se 1 (by rfl) ⟨4416200, by rfl⟩ : syracuseStep 5888267 = 8832401) B8832401
theorem B6625547 : Blo 1744573 6625547 := bstep (se 1 (by rfl) ⟨4969160, by rfl⟩ : syracuseStep 6625547 = 9938321) B9938321
theorem B7076107 : Blo 1744573 7076107 := bstep (se 1 (by rfl) ⟨5307080, by rfl⟩ : syracuseStep 7076107 = 10614161) B10614161
theorem B50305373 : Blo 1744573 50305373 := bstep (se 3 (by rfl) ⟨9432257, by rfl⟩ : syracuseStep 50305373 = 18864515) B18864515
theorem B2619743 : Blo 1744573 2619743 := bstep (se 1 (by rfl) ⟨1964807, by rfl⟩ : syracuseStep 2619743 = 3929615) B3929615
theorem B2619755 : Blo 1744573 2619755 := bstep (se 1 (by rfl) ⟨1964816, by rfl⟩ : syracuseStep 2619755 = 3929633) B3929633
theorem B2210267 : Blo 1744573 2210267 := bstep (se 1 (by rfl) ⟨1657700, by rfl⟩ : syracuseStep 2210267 = 3315401) B3315401
theorem B14342665 : Blo 1744573 14342665 := bstep (se 2 (by rfl) ⟨5378499, by rfl⟩ : syracuseStep 14342665 = 10756999) B10756999
theorem B5888537 : Blo 1744573 5888537 := bstep (se 2 (by rfl) ⟨2208201, by rfl⟩ : syracuseStep 5888537 = 4416403) B4416403
theorem B14162465 : Blo 1744573 14162465 := bstep (se 2 (by rfl) ⟨5310924, by rfl⟩ : syracuseStep 14162465 = 10621849) B10621849
theorem B1964623 : Blo 1744573 1964623 := bstep (se 1 (by rfl) ⟨1473467, by rfl⟩ : syracuseStep 1964623 = 2946935) B2946935
theorem B47790769 : Blo 1744573 47790769 := bstep (se 2 (by rfl) ⟨17921538, by rfl⟩ : syracuseStep 47790769 = 35843077) B35843077
theorem B21510841 : Blo 1744573 21510841 := bstep (se 2 (by rfl) ⟨8066565, by rfl⟩ : syracuseStep 21510841 = 16133131) B16133131
theorem B4971257 : Blo 1744573 4971257 := bstep (se 2 (by rfl) ⟨1864221, by rfl⟩ : syracuseStep 4971257 = 3728443) B3728443
theorem B6290219 : Blo 1744573 6290219 := bstep (se 1 (by rfl) ⟨4717664, by rfl⟩ : syracuseStep 6290219 = 9435329) B9435329
theorem B2653103 : Blo 1744573 2653103 := bstep (se 1 (by rfl) ⟨1989827, by rfl⟩ : syracuseStep 2653103 = 3979655) B3979655
theorem B6626231 : Blo 1744573 6626231 := bstep (se 1 (by rfl) ⟨4969673, by rfl⟩ : syracuseStep 6626231 = 9939347) B9939347
theorem B8838071 : Blo 1744573 8838071 := bstep (se 1 (by rfl) ⟨6628553, by rfl⟩ : syracuseStep 8838071 = 13257107) B13257107
theorem B7453775 : Blo 1744573 7453775 := bstep (se 1 (by rfl) ⟨5590331, by rfl⟩ : syracuseStep 7453775 = 11180663) B11180663
theorem B2096327 : Blo 1744573 2096327 := bstep (se 1 (by rfl) ⟨1572245, by rfl⟩ : syracuseStep 2096327 = 3144491) B3144491
theorem B57425369 : Blo 1744573 57425369 := bstep (se 2 (by rfl) ⟨21534513, by rfl⟩ : syracuseStep 57425369 = 43069027) B43069027
theorem B3145225 : Blo 1744573 3145225 := bstep (se 2 (by rfl) ⟨1179459, by rfl⟩ : syracuseStep 3145225 = 2358919) B2358919
theorem B5889671 : Blo 1744573 5889671 := bstep (se 1 (by rfl) ⟨4417253, by rfl⟩ : syracuseStep 5889671 = 8834507) B8834507
theorem B5889725 : Blo 1744573 5889725 := bstep (se 3 (by rfl) ⟨1104323, by rfl⟩ : syracuseStep 5889725 = 2208647) B2208647
theorem B6627005 : Blo 1744573 6627005 := bstep (se 3 (by rfl) ⟨1242563, by rfl⟩ : syracuseStep 6627005 = 2485127) B2485127
theorem B4718269 : Blo 1744573 4718269 := bstep (se 3 (by rfl) ⟨884675, by rfl⟩ : syracuseStep 4718269 = 1769351) B1769351
theorem B1744583 : Blo 1744573 1744583 := bstep (se 1 (by rfl) ⟨1308437, by rfl⟩ : syracuseStep 1744583 = 2616875) B2616875
theorem B1744603 : Blo 1744573 1744603 := bstep (se 1 (by rfl) ⟨1308452, by rfl⟩ : syracuseStep 1744603 = 2616905) B2616905
theorem B1744679 : Blo 1744573 1744679 := bstep (se 1 (by rfl) ⟨1308509, by rfl⟩ : syracuseStep 1744679 = 2617019) B2617019
theorem B1744719 : Blo 1744573 1744719 := bstep (se 1 (by rfl) ⟨1308539, by rfl⟩ : syracuseStep 1744719 = 2617079) B2617079
theorem B1744735 : Blo 1744573 1744735 := bstep (se 1 (by rfl) ⟨1308551, by rfl⟩ : syracuseStep 1744735 = 2617103) B2617103
theorem B5889887 : Blo 1744573 5889887 := bstep (se 1 (by rfl) ⟨4417415, by rfl⟩ : syracuseStep 5889887 = 8834831) B8834831
theorem B9944927 : Blo 1744573 9944927 := bstep (se 1 (by rfl) ⟨7458695, by rfl⟩ : syracuseStep 9944927 = 14917391) B14917391
theorem B1744763 : Blo 1744573 1744763 := bstep (se 1 (by rfl) ⟨1308572, by rfl⟩ : syracuseStep 1744763 = 2617145) B2617145
theorem B1744815 : Blo 1744573 1744815 := bstep (se 1 (by rfl) ⟨1308611, by rfl⟩ : syracuseStep 1744815 = 2617223) B2617223
theorem B16777145 : Blo 1744573 16777145 := bstep (se 2 (by rfl) ⟨6291429, by rfl⟩ : syracuseStep 16777145 = 12582859) B12582859
theorem B1744839 : Blo 1744573 1744839 := bstep (se 1 (by rfl) ⟨1308629, by rfl⟩ : syracuseStep 1744839 = 2617259) B2617259
theorem B1744859 : Blo 1744573 1744859 := bstep (se 1 (by rfl) ⟨1308644, by rfl⟩ : syracuseStep 1744859 = 2617289) B2617289
theorem B698261579 : Blo 1744573 698261579 := bstep (se 1 (by rfl) ⟨523696184, by rfl⟩ : syracuseStep 698261579 = 1047392369) B1047392369
theorem B1745183 : Blo 1744573 1745183 := bstep (se 1 (by rfl) ⟨1308887, by rfl⟩ : syracuseStep 1745183 = 2617775) B2617775
theorem B1745243 : Blo 1744573 1745243 := bstep (se 1 (by rfl) ⟨1308932, by rfl⟩ : syracuseStep 1745243 = 2617865) B2617865
theorem B382361957 : Blo 1744573 382361957 := bstep (se 4 (by rfl) ⟨35846433, by rfl⟩ : syracuseStep 382361957 = 71692867) B71692867
theorem B1745263 : Blo 1744573 1745263 := bstep (se 1 (by rfl) ⟨1308947, by rfl⟩ : syracuseStep 1745263 = 2617895) B2617895
theorem B1745319 : Blo 1744573 1745319 := bstep (se 1 (by rfl) ⟨1308989, by rfl⟩ : syracuseStep 1745319 = 2617979) B2617979
theorem B1745403 : Blo 1744573 1745403 := bstep (se 1 (by rfl) ⟨1309052, by rfl⟩ : syracuseStep 1745403 = 2618105) B2618105
theorem B1745471 : Blo 1744573 1745471 := bstep (se 1 (by rfl) ⟨1309103, by rfl⟩ : syracuseStep 1745471 = 2618207) B2618207
theorem B1745479 : Blo 1744573 1745479 := bstep (se 1 (by rfl) ⟨1309109, by rfl⟩ : syracuseStep 1745479 = 2618219) B2618219
theorem B4416079 : Blo 1744573 4416079 := bstep (se 1 (by rfl) ⟨3312059, by rfl⟩ : syracuseStep 4416079 = 6624119) B6624119
theorem B7455415 : Blo 1744573 7455415 := bstep (se 1 (by rfl) ⟨5591561, by rfl⟩ : syracuseStep 7455415 = 11183123) B11183123
theorem B1745631 : Blo 1744573 1745631 := bstep (se 1 (by rfl) ⟨1309223, by rfl⟩ : syracuseStep 1745631 = 2618447) B2618447
theorem B1745711 : Blo 1744573 1745711 := bstep (se 1 (by rfl) ⟨1309283, by rfl⟩ : syracuseStep 1745711 = 2618567) B2618567
theorem B6628175 : Blo 1744573 6628175 := bstep (se 1 (by rfl) ⟨4971131, by rfl⟩ : syracuseStep 6628175 = 9942263) B9942263
theorem B8840015 : Blo 1744573 8840015 := bstep (se 1 (by rfl) ⟨6630011, by rfl⟩ : syracuseStep 8840015 = 13260023) B13260023
theorem B1745819 : Blo 1744573 1745819 := bstep (se 1 (by rfl) ⟨1309364, by rfl⟩ : syracuseStep 1745819 = 2618729) B2618729
theorem B28681121 : Blo 1744573 28681121 := bstep (se 2 (by rfl) ⟨10755420, by rfl⟩ : syracuseStep 28681121 = 21510841) B21510841
theorem B7455689 : Blo 1744573 7455689 := bstep (se 2 (by rfl) ⟨2795883, by rfl⟩ : syracuseStep 7455689 = 5591767) B5591767
theorem B6718409 : Blo 1744573 6718409 := bstep (se 2 (by rfl) ⟨2519403, by rfl⟩ : syracuseStep 6718409 = 5038807) B5038807
theorem B1745871 : Blo 1744573 1745871 := bstep (se 1 (by rfl) ⟨1309403, by rfl⟩ : syracuseStep 1745871 = 2618807) B2618807
theorem B1745895 : Blo 1744573 1745895 := bstep (se 1 (by rfl) ⟨1309421, by rfl⟩ : syracuseStep 1745895 = 2618843) B2618843
theorem B8840339 : Blo 1744573 8840339 := bstep (se 1 (by rfl) ⟨6630254, by rfl⟩ : syracuseStep 8840339 = 13260509) B13260509
theorem B18875587 : Blo 1744573 18875587 := bstep (se 1 (by rfl) ⟨14156690, by rfl⟩ : syracuseStep 18875587 = 28313381) B28313381
theorem B4416727 : Blo 1744573 4416727 := bstep (se 1 (by rfl) ⟨3312545, by rfl⟩ : syracuseStep 4416727 = 6625091) B6625091
theorem B4195547 : Blo 1744573 4195547 := bstep (se 1 (by rfl) ⟨3146660, by rfl⟩ : syracuseStep 4195547 = 6293321) B6293321
theorem B153134317 : Blo 1744573 153134317 := bstep (se 3 (by rfl) ⟨28712684, by rfl⟩ : syracuseStep 153134317 = 57425369) B57425369
theorem B1746207 : Blo 1744573 1746207 := bstep (se 1 (by rfl) ⟨1309655, by rfl⟩ : syracuseStep 1746207 = 2619311) B2619311
theorem B44746019 : Blo 1744573 44746019 := bstep (se 1 (by rfl) ⟨33559514, by rfl⟩ : syracuseStep 44746019 = 67119029) B67119029
theorem B19891493 : Blo 1744573 19891493 := bstep (se 4 (by rfl) ⟨1864827, by rfl⟩ : syracuseStep 19891493 = 3729655) B3729655
theorem B1746267 : Blo 1744573 1746267 := bstep (se 1 (by rfl) ⟨1309700, by rfl⟩ : syracuseStep 1746267 = 2619401) B2619401
theorem B18400621 : Blo 1744573 18400621 := bstep (se 3 (by rfl) ⟨3450116, by rfl⟩ : syracuseStep 18400621 = 6900233) B6900233
theorem B1746287 : Blo 1744573 1746287 := bstep (se 1 (by rfl) ⟨1309715, by rfl⟩ : syracuseStep 1746287 = 2619431) B2619431
theorem B3925385 : Blo 1744573 3925385 := bstep (se 2 (by rfl) ⟨1472019, by rfl⟩ : syracuseStep 3925385 = 2944039) B2944039
theorem B3728801 : Blo 1744573 3728801 := bstep (se 2 (by rfl) ⟨1398300, by rfl⟩ : syracuseStep 3728801 = 2796601) B2796601
theorem B1746343 : Blo 1744573 1746343 := bstep (se 1 (by rfl) ⟨1309757, by rfl⟩ : syracuseStep 1746343 = 2619515) B2619515
theorem B37766573 : Blo 1744573 37766573 := bstep (se 3 (by rfl) ⟨7081232, by rfl⟩ : syracuseStep 37766573 = 14162465) B14162465
theorem B1746427 : Blo 1744573 1746427 := bstep (se 1 (by rfl) ⟨1309820, by rfl⟩ : syracuseStep 1746427 = 2619641) B2619641
theorem B3925511 : Blo 1744573 3925511 := bstep (se 1 (by rfl) ⟨2944133, by rfl⟩ : syracuseStep 3925511 = 5888267) B5888267
theorem B4417031 : Blo 1744573 4417031 := bstep (se 1 (by rfl) ⟨3312773, by rfl⟩ : syracuseStep 4417031 = 6625547) B6625547
theorem B1746495 : Blo 1744573 1746495 := bstep (se 1 (by rfl) ⟨1309871, by rfl⟩ : syracuseStep 1746495 = 2619743) B2619743
theorem B1746503 : Blo 1744573 1746503 := bstep (se 1 (by rfl) ⟨1309877, by rfl⟩ : syracuseStep 1746503 = 2619755) B2619755
theorem B3925691 : Blo 1744573 3925691 := bstep (se 1 (by rfl) ⟨2944268, by rfl⟩ : syracuseStep 3925691 = 5888537) B5888537
theorem B3925817 : Blo 1744573 3925817 := bstep (se 2 (by rfl) ⟨1472181, by rfl⟩ : syracuseStep 3925817 = 2944363) B2944363
theorem B31844177 : Blo 1744573 31844177 := bstep (se 2 (by rfl) ⟨11941566, by rfl⟩ : syracuseStep 31844177 = 23883133) B23883133
theorem B16779143 : Blo 1744573 16779143 := bstep (se 1 (by rfl) ⟨12584357, by rfl⟩ : syracuseStep 16779143 = 25168715) B25168715
theorem B13428625 : Blo 1744573 13428625 := bstep (se 2 (by rfl) ⟨5035734, by rfl⟩ : syracuseStep 13428625 = 10071469) B10071469
theorem B4417487 : Blo 1744573 4417487 := bstep (se 1 (by rfl) ⟨3313115, by rfl⟩ : syracuseStep 4417487 = 6626231) B6626231
theorem B5892047 : Blo 1744573 5892047 := bstep (se 1 (by rfl) ⟨4419035, by rfl⟩ : syracuseStep 5892047 = 8838071) B8838071
theorem B21227501 : Blo 1744573 21227501 := bstep (se 3 (by rfl) ⟨3980156, by rfl⟩ : syracuseStep 21227501 = 7960313) B7960313
theorem B33999239 : Blo 1744573 33999239 := bstep (se 1 (by rfl) ⟨25499429, by rfl⟩ : syracuseStep 33999239 = 50998859) B50998859
theorem B2984359 : Blo 1744573 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B3926447 : Blo 1744573 3926447 := bstep (se 1 (by rfl) ⟨2944835, by rfl⟩ : syracuseStep 3926447 = 5889671) B5889671
theorem B3312083 : Blo 1744573 3312083 := bstep (se 1 (by rfl) ⟨2484062, by rfl⟩ : syracuseStep 3312083 = 4968125) B4968125
theorem B3926483 : Blo 1744573 3926483 := bstep (se 1 (by rfl) ⟨2944862, by rfl⟩ : syracuseStep 3926483 = 5889725) B5889725
theorem B4418003 : Blo 1744573 4418003 := bstep (se 1 (by rfl) ⟨3313502, by rfl⟩ : syracuseStep 4418003 = 6627005) B6627005
theorem B3926591 : Blo 1744573 3926591 := bstep (se 1 (by rfl) ⟨2944943, by rfl⟩ : syracuseStep 3926591 = 5889887) B5889887
theorem B6629951 : Blo 1744573 6629951 := bstep (se 1 (by rfl) ⟨4972463, by rfl⟩ : syracuseStep 6629951 = 9944927) B9944927
theorem B11184763 : Blo 1744573 11184763 := bstep (se 1 (by rfl) ⟨8388572, by rfl⟩ : syracuseStep 11184763 = 16777145) B16777145
theorem B3926699 : Blo 1744573 3926699 := bstep (se 1 (by rfl) ⟨2945024, by rfl⟩ : syracuseStep 3926699 = 5890049) B5890049
theorem B37743383 : Blo 1744573 37743383 := bstep (se 1 (by rfl) ⟨28307537, by rfl⟩ : syracuseStep 37743383 = 56615075) B56615075
theorem B8833859 : Blo 1744573 8833859 := bstep (se 1 (by rfl) ⟨6625394, by rfl⟩ : syracuseStep 8833859 = 13250789) B13250789
theorem B9939779 : Blo 1744573 9939779 := bstep (se 1 (by rfl) ⟨7454834, by rfl⟩ : syracuseStep 9939779 = 14909669) B14909669
theorem B4418459 : Blo 1744573 4418459 := bstep (se 1 (by rfl) ⟨3313844, by rfl⟩ : syracuseStep 4418459 = 6627689) B6627689
theorem B5893019 : Blo 1744573 5893019 := bstep (se 1 (by rfl) ⟨4419764, by rfl⟩ : syracuseStep 5893019 = 8839529) B8839529
theorem B7457807 : Blo 1744573 7457807 := bstep (se 1 (by rfl) ⟨5593355, by rfl⟩ : syracuseStep 7457807 = 11186711) B11186711
theorem B5590205 : Blo 1744573 5590205 := bstep (se 3 (by rfl) ⟨1048163, by rfl⟩ : syracuseStep 5590205 = 2096327) B2096327
theorem B3927239 : Blo 1744573 3927239 := bstep (se 1 (by rfl) ⟨2945429, by rfl⟩ : syracuseStep 3927239 = 5890859) B5890859
theorem B6630619 : Blo 1744573 6630619 := bstep (se 1 (by rfl) ⟨4972964, by rfl⟩ : syracuseStep 6630619 = 9945929) B9945929
theorem B7458115 : Blo 1744573 7458115 := bstep (se 1 (by rfl) ⟨5593586, by rfl⟩ : syracuseStep 7458115 = 11187173) B11187173
theorem B19123553 : Blo 1744573 19123553 := bstep (se 2 (by rfl) ⟨7171332, by rfl⟩ : syracuseStep 19123553 = 14342665) B14342665
theorem B3927419 : Blo 1744573 3927419 := bstep (se 1 (by rfl) ⟨2945564, by rfl⟩ : syracuseStep 3927419 = 5891129) B5891129
theorem B64572815 : Blo 1744573 64572815 := bstep (se 1 (by rfl) ⟨48429611, by rfl⟩ : syracuseStep 64572815 = 96859223) B96859223
theorem B7081415 : Blo 1744573 7081415 := bstep (se 1 (by rfl) ⟨5311061, by rfl⟩ : syracuseStep 7081415 = 10622123) B10622123
theorem B2944505 : Blo 1744573 2944505 := bstep (se 2 (by rfl) ⟨1104189, by rfl⟩ : syracuseStep 2944505 = 2208379) B2208379
theorem B3927545 : Blo 1744573 3927545 := bstep (se 2 (by rfl) ⟨1472829, by rfl⟩ : syracuseStep 3927545 = 2945659) B2945659
theorem B63721025 : Blo 1744573 63721025 := bstep (se 2 (by rfl) ⟨23895384, by rfl⟩ : syracuseStep 63721025 = 47790769) B47790769
theorem B3927635 : Blo 1744573 3927635 := bstep (se 1 (by rfl) ⟨2945726, by rfl⟩ : syracuseStep 3927635 = 5891453) B5891453
theorem B8834669 : Blo 1744573 8834669 := bstep (se 3 (by rfl) ⟨1656500, by rfl⟩ : syracuseStep 8834669 = 3313001) B3313001
theorem B2617067 : Blo 1744573 2617067 := bstep (se 1 (by rfl) ⟨1962800, by rfl⟩ : syracuseStep 2617067 = 3925601) B3925601
theorem B5377799 : Blo 1744573 5377799 := bstep (se 1 (by rfl) ⟨4033349, by rfl⟩ : syracuseStep 5377799 = 8066699) B8066699
theorem B2944775 : Blo 1744573 2944775 := bstep (se 1 (by rfl) ⟨2208581, by rfl⟩ : syracuseStep 2944775 = 4417163) B4417163
theorem B3927815 : Blo 1744573 3927815 := bstep (se 1 (by rfl) ⟨2945861, by rfl⟩ : syracuseStep 3927815 = 5891723) B5891723
theorem B5894045 : Blo 1744573 5894045 := bstep (se 3 (by rfl) ⟨1105133, by rfl⟩ : syracuseStep 5894045 = 2210267) B2210267
theorem B2617295 : Blo 1744573 2617295 := bstep (se 1 (by rfl) ⟨1962971, by rfl⟩ : syracuseStep 2617295 = 3925943) B3925943
theorem B4419593 : Blo 1744573 4419593 := bstep (se 2 (by rfl) ⟨1657347, by rfl⟩ : syracuseStep 4419593 = 3314695) B3314695
theorem B5894153 : Blo 1744573 5894153 := bstep (se 2 (by rfl) ⟨2210307, by rfl⟩ : syracuseStep 5894153 = 4420615) B4420615
theorem B4370537 : Blo 1744573 4370537 := bstep (se 2 (by rfl) ⟨1638951, by rfl⟩ : syracuseStep 4370537 = 3277903) B3277903
theorem B48410945 : Blo 1744573 48410945 := bstep (se 2 (by rfl) ⟨18154104, by rfl⟩ : syracuseStep 48410945 = 36308209) B36308209
theorem B2617691 : Blo 1744573 2617691 := bstep (se 1 (by rfl) ⟨1963268, by rfl⟩ : syracuseStep 2617691 = 3926537) B3926537
theorem B3928427 : Blo 1744573 3928427 := bstep (se 1 (by rfl) ⟨2946320, by rfl⟩ : syracuseStep 3928427 = 5892641) B5892641
theorem B4419947 : Blo 1744573 4419947 := bstep (se 1 (by rfl) ⟨3314960, by rfl⟩ : syracuseStep 4419947 = 6629921) B6629921
theorem B2945531 : Blo 1744573 2945531 := bstep (se 1 (by rfl) ⟨2209148, by rfl⟩ : syracuseStep 2945531 = 4418297) B4418297
theorem B3314171 : Blo 1744573 3314171 := bstep (se 1 (by rfl) ⟨2485628, by rfl⟩ : syracuseStep 3314171 = 4971257) B4971257
theorem B3928571 : Blo 1744573 3928571 := bstep (se 1 (by rfl) ⟨2946428, by rfl⟩ : syracuseStep 3928571 = 5892857) B5892857
theorem B9941555 : Blo 1744573 9941555 := bstep (se 1 (by rfl) ⟨7456166, by rfl⟩ : syracuseStep 9941555 = 14912333) B14912333
theorem B2617919 : Blo 1744573 2617919 := bstep (se 1 (by rfl) ⟨1963439, by rfl⟩ : syracuseStep 2617919 = 3926879) B3926879
theorem B8385095 : Blo 1744573 8385095 := bstep (se 1 (by rfl) ⟨6288821, by rfl⟩ : syracuseStep 8385095 = 12577643) B12577643
theorem B3928697 : Blo 1744573 3928697 := bstep (se 2 (by rfl) ⟨1473261, by rfl⟩ : syracuseStep 3928697 = 2946523) B2946523
theorem B3928751 : Blo 1744573 3928751 := bstep (se 1 (by rfl) ⟨2946563, by rfl⟩ : syracuseStep 3928751 = 5893127) B5893127
theorem B4420271 : Blo 1744573 4420271 := bstep (se 1 (by rfl) ⟨3315203, by rfl⟩ : syracuseStep 4420271 = 6630407) B6630407
theorem B2618039 : Blo 1744573 2618039 := bstep (se 1 (by rfl) ⟨1963529, by rfl⟩ : syracuseStep 2618039 = 3927059) B3927059
theorem B4969183 : Blo 1744573 4969183 := bstep (se 1 (by rfl) ⟨3726887, by rfl⟩ : syracuseStep 4969183 = 7453775) B7453775
theorem B3928823 : Blo 1744573 3928823 := bstep (se 1 (by rfl) ⟨2946617, by rfl⟩ : syracuseStep 3928823 = 5893235) B5893235
theorem B1864495 : Blo 1744573 1864495 := bstep (se 1 (by rfl) ⟨1398371, by rfl⟩ : syracuseStep 1864495 = 2796743) B2796743
theorem B2618267 : Blo 1744573 2618267 := bstep (se 1 (by rfl) ⟨1963700, by rfl⟩ : syracuseStep 2618267 = 3927401) B3927401
theorem B2945963 : Blo 1744573 2945963 := bstep (se 1 (by rfl) ⟨2209472, by rfl⟩ : syracuseStep 2945963 = 4418945) B4418945
theorem B3929003 : Blo 1744573 3929003 := bstep (se 1 (by rfl) ⟨2946752, by rfl⟩ : syracuseStep 3929003 = 5893505) B5893505
theorem B25850825 : Blo 1744573 25850825 := bstep (se 2 (by rfl) ⟨9694059, by rfl⟩ : syracuseStep 25850825 = 19388119) B19388119
theorem B4420595 : Blo 1744573 4420595 := bstep (se 1 (by rfl) ⟨3315446, by rfl⟩ : syracuseStep 4420595 = 6630893) B6630893
theorem B11187325 : Blo 1744573 11187325 := bstep (se 3 (by rfl) ⟨2097623, by rfl⟩ : syracuseStep 11187325 = 4195247) B4195247
theorem B12588281 : Blo 1744573 12588281 := bstep (se 2 (by rfl) ⟨4720605, by rfl⟩ : syracuseStep 12588281 = 9441211) B9441211
theorem B4781351 : Blo 1744573 4781351 := bstep (se 1 (by rfl) ⟨3586013, by rfl⟩ : syracuseStep 4781351 = 7172027) B7172027
theorem B2618663 : Blo 1744573 2618663 := bstep (se 1 (by rfl) ⟨1963997, by rfl⟩ : syracuseStep 2618663 = 3927995) B3927995
theorem B7451999 : Blo 1744573 7451999 := bstep (se 1 (by rfl) ⟨5588999, by rfl⟩ : syracuseStep 7451999 = 11177999) B11177999
theorem B2618747 : Blo 1744573 2618747 := bstep (se 1 (by rfl) ⟨1964060, by rfl⟩ : syracuseStep 2618747 = 3928121) B3928121
theorem B22369729 : Blo 1744573 22369729 := bstep (se 2 (by rfl) ⟨8388648, by rfl⟩ : syracuseStep 22369729 = 16777297) B16777297
theorem B2946503 : Blo 1744573 2946503 := bstep (se 1 (by rfl) ⟨2209877, by rfl⟩ : syracuseStep 2946503 = 4419755) B4419755
theorem B3315143 : Blo 1744573 3315143 := bstep (se 1 (by rfl) ⟨2486357, by rfl⟩ : syracuseStep 3315143 = 4972715) B4972715
theorem B3929543 : Blo 1744573 3929543 := bstep (se 1 (by rfl) ⟨2947157, by rfl⟩ : syracuseStep 3929543 = 5894315) B5894315
theorem B2618873 : Blo 1744573 2618873 := bstep (se 2 (by rfl) ⟨982077, by rfl⟩ : syracuseStep 2618873 = 1964155) B1964155
theorem B5305913 : Blo 1744573 5305913 := bstep (se 2 (by rfl) ⟨1989717, by rfl⟩ : syracuseStep 5305913 = 3979435) B3979435
theorem B2209351 : Blo 1744573 2209351 := bstep (se 1 (by rfl) ⟨1657013, by rfl⟩ : syracuseStep 2209351 = 3314027) B3314027
theorem B1963615 : Blo 1744573 1963615 := bstep (se 1 (by rfl) ⟨1472711, by rfl⟩ : syracuseStep 1963615 = 2945423) B2945423
theorem B2618975 : Blo 1744573 2618975 := bstep (se 1 (by rfl) ⟨1964231, by rfl⟩ : syracuseStep 2618975 = 3928463) B3928463
theorem B20158085 : Blo 1744573 20158085 := bstep (se 4 (by rfl) ⟨1889820, by rfl⟩ : syracuseStep 20158085 = 3779641) B3779641
theorem B9434809 : Blo 1744573 9434809 := bstep (se 2 (by rfl) ⟨3538053, by rfl⟩ : syracuseStep 9434809 = 7076107) B7076107
theorem B71661347 : Blo 1744573 71661347 := bstep (se 1 (by rfl) ⟨53746010, by rfl⟩ : syracuseStep 71661347 = 107492021) B107492021
theorem B2619191 : Blo 1744573 2619191 := bstep (se 1 (by rfl) ⟨1964393, by rfl⟩ : syracuseStep 2619191 = 3928787) B3928787
theorem B9943013 : Blo 1744573 9943013 := bstep (se 4 (by rfl) ⟨932157, by rfl⟩ : syracuseStep 9943013 = 1864315) B1864315
theorem B44759141 : Blo 1744573 44759141 := bstep (se 4 (by rfl) ⟨4196169, by rfl⟩ : syracuseStep 44759141 = 8392339) B8392339
theorem B2619497 : Blo 1744573 2619497 := bstep (se 2 (by rfl) ⟨982311, by rfl⟩ : syracuseStep 2619497 = 1964623) B1964623
theorem B25164101 : Blo 1744573 25164101 := bstep (se 4 (by rfl) ⟨2359134, by rfl⟩ : syracuseStep 25164101 = 4718269) B4718269
theorem B2619815 : Blo 1744573 2619815 := bstep (se 1 (by rfl) ⟨1964861, by rfl⟩ : syracuseStep 2619815 = 3929723) B3929723
theorem B3144187 : Blo 1744573 3144187 := bstep (se 1 (by rfl) ⟨2358140, by rfl⟩ : syracuseStep 3144187 = 4716281) B4716281
theorem B4192787 : Blo 1744573 4192787 := bstep (se 1 (by rfl) ⟨3144590, by rfl⟩ : syracuseStep 4192787 = 6289181) B6289181
theorem B8387111 : Blo 1744573 8387111 := bstep (se 1 (by rfl) ⟨6290333, by rfl⟩ : syracuseStep 8387111 = 12580667) B12580667
theorem B5888591 : Blo 1744573 5888591 := bstep (se 1 (by rfl) ⟨4416443, by rfl⟩ : syracuseStep 5888591 = 8832887) B8832887
theorem B1964767 : Blo 1744573 1964767 := bstep (se 1 (by rfl) ⟨1473575, by rfl⟩ : syracuseStep 1964767 = 2947151) B2947151
theorem B33536915 : Blo 1744573 33536915 := bstep (se 1 (by rfl) ⟨25152686, by rfl⟩ : syracuseStep 33536915 = 50305373) B50305373
theorem B3726299 : Blo 1744573 3726299 := bstep (se 1 (by rfl) ⟨2794724, by rfl⟩ : syracuseStep 3726299 = 5589449) B5589449
theorem B4193479 : Blo 1744573 4193479 := bstep (se 1 (by rfl) ⟨3145109, by rfl⟩ : syracuseStep 4193479 = 6290219) B6290219
theorem B1768735 : Blo 1744573 1768735 := bstep (se 1 (by rfl) ⟨1326551, by rfl⟩ : syracuseStep 1768735 = 2653103) B2653103
theorem B4193633 : Blo 1744573 4193633 := bstep (se 2 (by rfl) ⟨1572612, by rfl⟩ : syracuseStep 4193633 = 3145225) B3145225
theorem B1744607 : Blo 1744573 1744607 := bstep (se 1 (by rfl) ⟨1308455, by rfl⟩ : syracuseStep 1744607 = 2616911) B2616911
theorem B5889833 : Blo 1744573 5889833 := bstep (se 2 (by rfl) ⟨2208687, by rfl⟩ : syracuseStep 5889833 = 4417375) B4417375
theorem B1744687 : Blo 1744573 1744687 := bstep (se 1 (by rfl) ⟨1308515, by rfl⟩ : syracuseStep 1744687 = 2617031) B2617031
theorem B1744795 : Blo 1744573 1744795 := bstep (se 1 (by rfl) ⟨1308596, by rfl⟩ : syracuseStep 1744795 = 2617193) B2617193
theorem B1744847 : Blo 1744573 1744847 := bstep (se 1 (by rfl) ⟨1308635, by rfl⟩ : syracuseStep 1744847 = 2617271) B2617271
theorem B1744871 : Blo 1744573 1744871 := bstep (se 1 (by rfl) ⟨1308653, by rfl⟩ : syracuseStep 1744871 = 2617307) B2617307
theorem B1745127 : Blo 1744573 1745127 := bstep (se 1 (by rfl) ⟨1308845, by rfl⟩ : syracuseStep 1745127 = 2617691) B2617691
theorem B6627703 : Blo 1744573 6627703 := bstep (se 1 (by rfl) ⟨4970777, by rfl⟩ : syracuseStep 6627703 = 9941555) B9941555
theorem B1745279 : Blo 1744573 1745279 := bstep (se 1 (by rfl) ⟨1308959, by rfl⟩ : syracuseStep 1745279 = 2617919) B2617919
theorem B1745359 : Blo 1744573 1745359 := bstep (se 1 (by rfl) ⟨1309019, by rfl⟩ : syracuseStep 1745359 = 2618039) B2618039
theorem B1745511 : Blo 1744573 1745511 := bstep (se 1 (by rfl) ⟨1309133, by rfl⟩ : syracuseStep 1745511 = 2618267) B2618267
theorem B19120747 : Blo 1744573 19120747 := bstep (se 1 (by rfl) ⟨14340560, by rfl⟩ : syracuseStep 19120747 = 28681121) B28681121
theorem B3187567 : Blo 1744573 3187567 := bstep (se 1 (by rfl) ⟨2390675, by rfl⟩ : syracuseStep 3187567 = 4781351) B4781351
theorem B1745775 : Blo 1744573 1745775 := bstep (se 1 (by rfl) ⟨1309331, by rfl⟩ : syracuseStep 1745775 = 2618663) B2618663
theorem B1745831 : Blo 1744573 1745831 := bstep (se 1 (by rfl) ⟨1309373, by rfl⟩ : syracuseStep 1745831 = 2618747) B2618747
theorem B11183021 : Blo 1744573 11183021 := bstep (se 3 (by rfl) ⟨2096816, by rfl⟩ : syracuseStep 11183021 = 4193633) B4193633
theorem B1745915 : Blo 1744573 1745915 := bstep (se 1 (by rfl) ⟨1309436, by rfl⟩ : syracuseStep 1745915 = 2618873) B2618873
theorem B1745983 : Blo 1744573 1745983 := bstep (se 1 (by rfl) ⟨1309487, by rfl⟩ : syracuseStep 1745983 = 2618975) B2618975
theorem B1746127 : Blo 1744573 1746127 := bstep (se 1 (by rfl) ⟨1309595, by rfl⟩ : syracuseStep 1746127 = 2619191) B2619191
theorem B6628675 : Blo 1744573 6628675 := bstep (se 1 (by rfl) ⟨4971506, by rfl⟩ : syracuseStep 6628675 = 9943013) B9943013
theorem B1746331 : Blo 1744573 1746331 := bstep (se 1 (by rfl) ⟨1309748, by rfl⟩ : syracuseStep 1746331 = 2619497) B2619497
theorem B22365629 : Blo 1744573 22365629 := bstep (se 3 (by rfl) ⟨4193555, by rfl⟩ : syracuseStep 22365629 = 8387111) B8387111
theorem B25167449 : Blo 1744573 25167449 := bstep (se 2 (by rfl) ⟨9437793, by rfl⟩ : syracuseStep 25167449 = 18875587) B18875587
theorem B1746543 : Blo 1744573 1746543 := bstep (se 1 (by rfl) ⟨1309907, by rfl⟩ : syracuseStep 1746543 = 2619815) B2619815
theorem B8840825 : Blo 1744573 8840825 := bstep (se 2 (by rfl) ⟨3315309, by rfl⟩ : syracuseStep 8840825 = 6630619) B6630619
theorem B2795191 : Blo 1744573 2795191 := bstep (se 1 (by rfl) ⟨2096393, by rfl⟩ : syracuseStep 2795191 = 4192787) B4192787
theorem B3925727 : Blo 1744573 3925727 := bstep (se 1 (by rfl) ⟨2944295, by rfl⟩ : syracuseStep 3925727 = 5888591) B5888591
theorem B22357943 : Blo 1744573 22357943 := bstep (se 1 (by rfl) ⟨16768457, by rfl⟩ : syracuseStep 22357943 = 33536915) B33536915
theorem B2484199 : Blo 1744573 2484199 := bstep (se 1 (by rfl) ⟨1863149, by rfl⟩ : syracuseStep 2484199 = 3726299) B3726299
theorem B12749035 : Blo 1744573 12749035 := bstep (se 1 (by rfl) ⟨9561776, by rfl⟩ : syracuseStep 12749035 = 19123553) B19123553
theorem B4720943 : Blo 1744573 4720943 := bstep (se 1 (by rfl) ⟨3540707, by rfl⟩ : syracuseStep 4720943 = 7081415) B7081415
theorem B3926555 : Blo 1744573 3926555 := bstep (se 1 (by rfl) ⟨2944916, by rfl⟩ : syracuseStep 3926555 = 5889833) B5889833
theorem B5590063 : Blo 1744573 5590063 := bstep (se 1 (by rfl) ⟨4192547, by rfl⟩ : syracuseStep 5590063 = 8385095) B8385095
theorem B4418783 : Blo 1744573 4418783 := bstep (se 1 (by rfl) ⟨3314087, by rfl⟩ : syracuseStep 4418783 = 6628175) B6628175
theorem B5893343 : Blo 1744573 5893343 := bstep (se 1 (by rfl) ⟨4420007, by rfl⟩ : syracuseStep 5893343 = 8840015) B8840015
theorem B5893559 : Blo 1744573 5893559 := bstep (se 1 (by rfl) ⟨4420169, by rfl⟩ : syracuseStep 5893559 = 8840339) B8840339
theorem B2797031 : Blo 1744573 2797031 := bstep (se 1 (by rfl) ⟨2097773, by rfl⟩ : syracuseStep 2797031 = 4195547) B4195547
theorem B14913017 : Blo 1744573 14913017 := bstep (se 2 (by rfl) ⟨5592381, by rfl⟩ : syracuseStep 14913017 = 11184763) B11184763
theorem B8392187 : Blo 1744573 8392187 := bstep (se 1 (by rfl) ⟨6294140, by rfl⟩ : syracuseStep 8392187 = 12588281) B12588281
theorem B29830679 : Blo 1744573 29830679 := bstep (se 1 (by rfl) ⟨22373009, by rfl⟩ : syracuseStep 29830679 = 44746019) B44746019
theorem B4967999 : Blo 1744573 4967999 := bstep (se 1 (by rfl) ⟨3725999, by rfl⟩ : syracuseStep 4967999 = 7451999) B7451999
theorem B9940553 : Blo 1744573 9940553 := bstep (se 2 (by rfl) ⟨3727707, by rfl⟩ : syracuseStep 9940553 = 7455415) B7455415
theorem B2616923 : Blo 1744573 2616923 := bstep (se 1 (by rfl) ⟨1962692, by rfl⟩ : syracuseStep 2616923 = 3925385) B3925385
theorem B25177715 : Blo 1744573 25177715 := bstep (se 1 (by rfl) ⟨18883286, by rfl⟩ : syracuseStep 25177715 = 37766573) B37766573
theorem B2617007 : Blo 1744573 2617007 := bstep (se 1 (by rfl) ⟨1962755, by rfl⟩ : syracuseStep 2617007 = 3925511) B3925511
theorem B2944687 : Blo 1744573 2944687 := bstep (se 1 (by rfl) ⟨2208515, by rfl⟩ : syracuseStep 2944687 = 4417031) B4417031
theorem B2485993 : Blo 1744573 2485993 := bstep (se 2 (by rfl) ⟨932247, by rfl⟩ : syracuseStep 2485993 = 1864495) B1864495
theorem B13438723 : Blo 1744573 13438723 := bstep (se 1 (by rfl) ⟨10079042, by rfl⟩ : syracuseStep 13438723 = 20158085) B20158085
theorem B2617127 : Blo 1744573 2617127 := bstep (se 1 (by rfl) ⟨1962845, by rfl⟩ : syracuseStep 2617127 = 3925691) B3925691
theorem B2617211 : Blo 1744573 2617211 := bstep (se 1 (by rfl) ⟨1962908, by rfl⟩ : syracuseStep 2617211 = 3925817) B3925817
theorem B21229451 : Blo 1744573 21229451 := bstep (se 1 (by rfl) ⟨15922088, by rfl⟩ : syracuseStep 21229451 = 31844177) B31844177
theorem B11186095 : Blo 1744573 11186095 := bstep (se 1 (by rfl) ⟨8389571, by rfl⟩ : syracuseStep 11186095 = 16779143) B16779143
theorem B2944991 : Blo 1744573 2944991 := bstep (se 1 (by rfl) ⟨2208743, by rfl⟩ : syracuseStep 2944991 = 4417487) B4417487
theorem B3928031 : Blo 1744573 3928031 := bstep (se 1 (by rfl) ⟨2946023, by rfl⟩ : syracuseStep 3928031 = 5892047) B5892047
theorem B14151667 : Blo 1744573 14151667 := bstep (se 1 (by rfl) ⟨10613750, by rfl⟩ : syracuseStep 14151667 = 21227501) B21227501
theorem B29839427 : Blo 1744573 29839427 := bstep (se 1 (by rfl) ⟨22379570, by rfl⟩ : syracuseStep 29839427 = 44759141) B44759141
theorem B9433253 : Blo 1744573 9433253 := bstep (se 4 (by rfl) ⟨884367, by rfl⟩ : syracuseStep 9433253 = 1768735) B1768735
theorem B5591305 : Blo 1744573 5591305 := bstep (se 2 (by rfl) ⟨2096739, by rfl⟩ : syracuseStep 5591305 = 4193479) B4193479
theorem B2617631 : Blo 1744573 2617631 := bstep (se 1 (by rfl) ⟨1963223, by rfl⟩ : syracuseStep 2617631 = 3926447) B3926447
theorem B2208055 : Blo 1744573 2208055 := bstep (se 1 (by rfl) ⟨1656041, by rfl⟩ : syracuseStep 2208055 = 3312083) B3312083
theorem B2617655 : Blo 1744573 2617655 := bstep (se 1 (by rfl) ⟨1963241, by rfl⟩ : syracuseStep 2617655 = 3926483) B3926483
theorem B2945335 : Blo 1744573 2945335 := bstep (se 1 (by rfl) ⟨2209001, by rfl⟩ : syracuseStep 2945335 = 4418003) B4418003
theorem B2617727 : Blo 1744573 2617727 := bstep (se 1 (by rfl) ⟨1963295, by rfl⟩ : syracuseStep 2617727 = 3926591) B3926591
theorem B4419967 : Blo 1744573 4419967 := bstep (se 1 (by rfl) ⟨3314975, by rfl⟩ : syracuseStep 4419967 = 6629951) B6629951
theorem B2617799 : Blo 1744573 2617799 := bstep (se 1 (by rfl) ⟨1963349, by rfl⟩ : syracuseStep 2617799 = 3926699) B3926699
theorem B25162255 : Blo 1744573 25162255 := bstep (se 1 (by rfl) ⟨18871691, by rfl⟩ : syracuseStep 25162255 = 37743383) B37743383
theorem B2945639 : Blo 1744573 2945639 := bstep (se 1 (by rfl) ⟨2209229, by rfl⟩ : syracuseStep 2945639 = 4418459) B4418459
theorem B3928679 : Blo 1744573 3928679 := bstep (se 1 (by rfl) ⟨2946509, by rfl⟩ : syracuseStep 3928679 = 5893019) B5893019
theorem B14340797 : Blo 1744573 14340797 := bstep (se 3 (by rfl) ⟨2688899, by rfl⟩ : syracuseStep 14340797 = 5377799) B5377799
theorem B2945801 : Blo 1744573 2945801 := bstep (se 2 (by rfl) ⟨1104675, by rfl⟩ : syracuseStep 2945801 = 2209351) B2209351
theorem B2618153 : Blo 1744573 2618153 := bstep (se 2 (by rfl) ⟨981807, by rfl⟩ : syracuseStep 2618153 = 1963615) B1963615
theorem B2618159 : Blo 1744573 2618159 := bstep (se 1 (by rfl) ⟨1963619, by rfl⟩ : syracuseStep 2618159 = 3927239) B3927239
theorem B12579745 : Blo 1744573 12579745 := bstep (se 2 (by rfl) ⟨4717404, by rfl⟩ : syracuseStep 12579745 = 9434809) B9434809
theorem B2618279 : Blo 1744573 2618279 := bstep (se 1 (by rfl) ⟨1963709, by rfl⟩ : syracuseStep 2618279 = 3927419) B3927419
theorem B1963003 : Blo 1744573 1963003 := bstep (se 1 (by rfl) ⟨1472252, by rfl⟩ : syracuseStep 1963003 = 2944505) B2944505
theorem B2618363 : Blo 1744573 2618363 := bstep (se 1 (by rfl) ⟨1963772, by rfl⟩ : syracuseStep 2618363 = 3927545) B3927545
theorem B42480683 : Blo 1744573 42480683 := bstep (se 1 (by rfl) ⟨31860512, by rfl⟩ : syracuseStep 42480683 = 63721025) B63721025
theorem B2618423 : Blo 1744573 2618423 := bstep (se 1 (by rfl) ⟨1963817, by rfl⟩ : syracuseStep 2618423 = 3927635) B3927635
theorem B1963183 : Blo 1744573 1963183 := bstep (se 1 (by rfl) ⟨1472387, by rfl⟩ : syracuseStep 1963183 = 2944775) B2944775
theorem B2618543 : Blo 1744573 2618543 := bstep (se 1 (by rfl) ⟨1963907, by rfl⟩ : syracuseStep 2618543 = 3927815) B3927815
theorem B17904833 : Blo 1744573 17904833 := bstep (se 2 (by rfl) ⟨6714312, by rfl⟩ : syracuseStep 17904833 = 13428625) B13428625
theorem B3929363 : Blo 1744573 3929363 := bstep (se 1 (by rfl) ⟨2947022, by rfl⟩ : syracuseStep 3929363 = 5894045) B5894045
theorem B2946395 : Blo 1744573 2946395 := bstep (se 1 (by rfl) ⟨2209796, by rfl⟩ : syracuseStep 2946395 = 4419593) B4419593
theorem B3929435 : Blo 1744573 3929435 := bstep (se 1 (by rfl) ⟨2947076, by rfl⟩ : syracuseStep 3929435 = 5894153) B5894153
theorem B465507719 : Blo 1744573 465507719 := bstep (se 1 (by rfl) ⟨349130789, by rfl⟩ : syracuseStep 465507719 = 698261579) B698261579
theorem B32273963 : Blo 1744573 32273963 := bstep (se 1 (by rfl) ⟨24205472, by rfl⟩ : syracuseStep 32273963 = 48410945) B48410945
theorem B254907971 : Blo 1744573 254907971 := bstep (se 1 (by rfl) ⟨191180978, by rfl⟩ : syracuseStep 254907971 = 382361957) B382361957
theorem B2618951 : Blo 1744573 2618951 := bstep (se 1 (by rfl) ⟨1964213, by rfl⟩ : syracuseStep 2618951 = 3928427) B3928427
theorem B2946631 : Blo 1744573 2946631 := bstep (se 1 (by rfl) ⟨2209973, by rfl⟩ : syracuseStep 2946631 = 4419947) B4419947
theorem B11654765 : Blo 1744573 11654765 := bstep (se 3 (by rfl) ⟨2185268, by rfl⟩ : syracuseStep 11654765 = 4370537) B4370537
theorem B1963687 : Blo 1744573 1963687 := bstep (se 1 (by rfl) ⟨1472765, by rfl⟩ : syracuseStep 1963687 = 2945531) B2945531
theorem B2209447 : Blo 1744573 2209447 := bstep (se 1 (by rfl) ⟨1657085, by rfl⟩ : syracuseStep 2209447 = 3314171) B3314171
theorem B2619047 : Blo 1744573 2619047 := bstep (se 1 (by rfl) ⟨1964285, by rfl⟩ : syracuseStep 2619047 = 3928571) B3928571
theorem B2619131 : Blo 1744573 2619131 := bstep (se 1 (by rfl) ⟨1964348, by rfl⟩ : syracuseStep 2619131 = 3928697) B3928697
theorem B2619167 : Blo 1744573 2619167 := bstep (se 1 (by rfl) ⟨1964375, by rfl⟩ : syracuseStep 2619167 = 3928751) B3928751
theorem B2946847 : Blo 1744573 2946847 := bstep (se 1 (by rfl) ⟨2210135, by rfl⟩ : syracuseStep 2946847 = 4420271) B4420271
theorem B2619215 : Blo 1744573 2619215 := bstep (se 1 (by rfl) ⟨1964411, by rfl⟩ : syracuseStep 2619215 = 3928823) B3928823
theorem B3979145 : Blo 1744573 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B1963975 : Blo 1744573 1963975 := bstep (se 1 (by rfl) ⟨1472981, by rfl⟩ : syracuseStep 1963975 = 2945963) B2945963
theorem B2619335 : Blo 1744573 2619335 := bstep (se 1 (by rfl) ⟨1964501, by rfl⟩ : syracuseStep 2619335 = 3929003) B3929003
theorem B17233883 : Blo 1744573 17233883 := bstep (se 1 (by rfl) ⟨12925412, by rfl⟩ : syracuseStep 17233883 = 25850825) B25850825
theorem B4970459 : Blo 1744573 4970459 := bstep (se 1 (by rfl) ⟨3727844, by rfl⟩ : syracuseStep 4970459 = 7455689) B7455689
theorem B4478939 : Blo 1744573 4478939 := bstep (se 1 (by rfl) ⟨3359204, by rfl⟩ : syracuseStep 4478939 = 6718409) B6718409
theorem B2947063 : Blo 1744573 2947063 := bstep (se 1 (by rfl) ⟨2210297, by rfl⟩ : syracuseStep 2947063 = 4420595) B4420595
theorem B4192249 : Blo 1744573 4192249 := bstep (se 2 (by rfl) ⟨1572093, by rfl⟩ : syracuseStep 4192249 = 3144187) B3144187
theorem B5888105 : Blo 1744573 5888105 := bstep (se 2 (by rfl) ⟨2208039, by rfl⟩ : syracuseStep 5888105 = 4416079) B4416079
theorem B13260995 : Blo 1744573 13260995 := bstep (se 1 (by rfl) ⟨9945746, by rfl⟩ : syracuseStep 13260995 = 19891493) B19891493
theorem B6625577 : Blo 1744573 6625577 := bstep (se 2 (by rfl) ⟨2484591, by rfl⟩ : syracuseStep 6625577 = 4969183) B4969183
theorem B2619689 : Blo 1744573 2619689 := bstep (se 2 (by rfl) ⟨982383, by rfl⟩ : syracuseStep 2619689 = 1964767) B1964767
theorem B1964335 : Blo 1744573 1964335 := bstep (se 1 (by rfl) ⟨1473251, by rfl⟩ : syracuseStep 1964335 = 2946503) B2946503
theorem B2210095 : Blo 1744573 2210095 := bstep (se 1 (by rfl) ⟨1657571, by rfl⟩ : syracuseStep 2210095 = 3315143) B3315143
theorem B2619695 : Blo 1744573 2619695 := bstep (se 1 (by rfl) ⟨1964771, by rfl⟩ : syracuseStep 2619695 = 3929543) B3929543
theorem B3537275 : Blo 1744573 3537275 := bstep (se 1 (by rfl) ⟨2652956, by rfl⟩ : syracuseStep 3537275 = 5305913) B5305913
theorem B9943469 : Blo 1744573 9943469 := bstep (se 3 (by rfl) ⟨1864400, by rfl⟩ : syracuseStep 9943469 = 3728801) B3728801
theorem B47774231 : Blo 1744573 47774231 := bstep (se 1 (by rfl) ⟨35830673, by rfl⟩ : syracuseStep 47774231 = 71661347) B71661347
theorem B816716357 : Blo 1744573 816716357 := bstep (se 4 (by rfl) ⟨76567158, by rfl⟩ : syracuseStep 816716357 = 153134317) B153134317
theorem B14916433 : Blo 1744573 14916433 := bstep (se 2 (by rfl) ⟨5593662, by rfl⟩ : syracuseStep 14916433 = 11187325) B11187325
theorem B16776067 : Blo 1744573 16776067 := bstep (se 1 (by rfl) ⟨12582050, by rfl⟩ : syracuseStep 16776067 = 25164101) B25164101
theorem B22666159 : Blo 1744573 22666159 := bstep (se 1 (by rfl) ⟨16999619, by rfl⟩ : syracuseStep 22666159 = 33999239) B33999239
theorem B5888969 : Blo 1744573 5888969 := bstep (se 2 (by rfl) ⟨2208363, by rfl⟩ : syracuseStep 5888969 = 4416727) B4416727
theorem B9944153 : Blo 1744573 9944153 := bstep (se 2 (by rfl) ⟨3729057, by rfl⟩ : syracuseStep 9944153 = 7458115) B7458115
theorem B24534161 : Blo 1744573 24534161 := bstep (se 2 (by rfl) ⟨9200310, by rfl⟩ : syracuseStep 24534161 = 18400621) B18400621
theorem B5889239 : Blo 1744573 5889239 := bstep (se 1 (by rfl) ⟨4416929, by rfl⟩ : syracuseStep 5889239 = 8833859) B8833859
theorem B6626519 : Blo 1744573 6626519 := bstep (se 1 (by rfl) ⟨4969889, by rfl⟩ : syracuseStep 6626519 = 9939779) B9939779
theorem B29826305 : Blo 1744573 29826305 := bstep (se 2 (by rfl) ⟨11184864, by rfl⟩ : syracuseStep 29826305 = 22369729) B22369729
theorem B4971871 : Blo 1744573 4971871 := bstep (se 1 (by rfl) ⟨3728903, by rfl⟩ : syracuseStep 4971871 = 7457807) B7457807
theorem B3726803 : Blo 1744573 3726803 := bstep (se 1 (by rfl) ⟨2795102, by rfl⟩ : syracuseStep 3726803 = 5590205) B5590205
theorem B43048543 : Blo 1744573 43048543 := bstep (se 1 (by rfl) ⟨32286407, by rfl⟩ : syracuseStep 43048543 = 64572815) B64572815
theorem B5889779 : Blo 1744573 5889779 := bstep (se 1 (by rfl) ⟨4417334, by rfl⟩ : syracuseStep 5889779 = 8834669) B8834669
theorem B1744711 : Blo 1744573 1744711 := bstep (se 1 (by rfl) ⟨1308533, by rfl⟩ : syracuseStep 1744711 = 2617067) B2617067
theorem B1744863 : Blo 1744573 1744863 := bstep (se 1 (by rfl) ⟨1308647, by rfl⟩ : syracuseStep 1744863 = 2617295) B2617295
theorem B1745087 : Blo 1744573 1745087 := bstep (se 1 (by rfl) ⟨1308815, by rfl⟩ : syracuseStep 1745087 = 2617631) B2617631
theorem B1745103 : Blo 1744573 1745103 := bstep (se 1 (by rfl) ⟨1308827, by rfl⟩ : syracuseStep 1745103 = 2617655) B2617655
theorem B1745151 : Blo 1744573 1745151 := bstep (se 1 (by rfl) ⟨1308863, by rfl⟩ : syracuseStep 1745151 = 2617727) B2617727
theorem B1745199 : Blo 1744573 1745199 := bstep (se 1 (by rfl) ⟨1308899, by rfl⟩ : syracuseStep 1745199 = 2617799) B2617799
theorem B16998713 : Blo 1744573 16998713 := bstep (se 2 (by rfl) ⟨6374517, by rfl⟩ : syracuseStep 16998713 = 12749035) B12749035
theorem B7455073 : Blo 1744573 7455073 := bstep (se 2 (by rfl) ⟨2795652, by rfl⟩ : syracuseStep 7455073 = 5591305) B5591305
theorem B9560531 : Blo 1744573 9560531 := bstep (se 1 (by rfl) ⟨7170398, by rfl⟩ : syracuseStep 9560531 = 14340797) B14340797
theorem B1745435 : Blo 1744573 1745435 := bstep (se 1 (by rfl) ⟨1309076, by rfl⟩ : syracuseStep 1745435 = 2618153) B2618153
theorem B1745439 : Blo 1744573 1745439 := bstep (se 1 (by rfl) ⟨1309079, by rfl⟩ : syracuseStep 1745439 = 2618159) B2618159
theorem B1745519 : Blo 1744573 1745519 := bstep (se 1 (by rfl) ⟨1309139, by rfl⟩ : syracuseStep 1745519 = 2618279) B2618279
theorem B7455347 : Blo 1744573 7455347 := bstep (se 1 (by rfl) ⟨5591510, by rfl⟩ : syracuseStep 7455347 = 11183021) B11183021
theorem B1745575 : Blo 1744573 1745575 := bstep (se 1 (by rfl) ⟨1309181, by rfl⟩ : syracuseStep 1745575 = 2618363) B2618363
theorem B28320455 : Blo 1744573 28320455 := bstep (se 1 (by rfl) ⟨21240341, by rfl⟩ : syracuseStep 28320455 = 42480683) B42480683
theorem B1745615 : Blo 1744573 1745615 := bstep (se 1 (by rfl) ⟨1309211, by rfl⟩ : syracuseStep 1745615 = 2618423) B2618423
theorem B1745695 : Blo 1744573 1745695 := bstep (se 1 (by rfl) ⟨1309271, by rfl⟩ : syracuseStep 1745695 = 2618543) B2618543
theorem B11936555 : Blo 1744573 11936555 := bstep (se 1 (by rfl) ⟨8952416, by rfl⟩ : syracuseStep 11936555 = 17904833) B17904833
theorem B25494329 : Blo 1744573 25494329 := bstep (se 2 (by rfl) ⟨9560373, by rfl⟩ : syracuseStep 25494329 = 19120747) B19120747
theorem B310338479 : Blo 1744573 310338479 := bstep (se 1 (by rfl) ⟨232753859, by rfl⟩ : syracuseStep 310338479 = 465507719) B465507719
theorem B14910419 : Blo 1744573 14910419 := bstep (se 1 (by rfl) ⟨11182814, by rfl⟩ : syracuseStep 14910419 = 22365629) B22365629
theorem B1745967 : Blo 1744573 1745967 := bstep (se 1 (by rfl) ⟨1309475, by rfl⟩ : syracuseStep 1745967 = 2618951) B2618951
theorem B16778299 : Blo 1744573 16778299 := bstep (se 1 (by rfl) ⟨12583724, by rfl⟩ : syracuseStep 16778299 = 25167449) B25167449
theorem B1746031 : Blo 1744573 1746031 := bstep (se 1 (by rfl) ⟨1309523, by rfl⟩ : syracuseStep 1746031 = 2619047) B2619047
theorem B1746087 : Blo 1744573 1746087 := bstep (se 1 (by rfl) ⟨1309565, by rfl⟩ : syracuseStep 1746087 = 2619131) B2619131
theorem B1746111 : Blo 1744573 1746111 := bstep (se 1 (by rfl) ⟨1309583, by rfl⟩ : syracuseStep 1746111 = 2619167) B2619167
theorem B1746143 : Blo 1744573 1746143 := bstep (se 1 (by rfl) ⟨1309607, by rfl⟩ : syracuseStep 1746143 = 2619215) B2619215
theorem B30221545 : Blo 1744573 30221545 := bstep (se 2 (by rfl) ⟨11333079, by rfl⟩ : syracuseStep 30221545 = 22666159) B22666159
theorem B1746223 : Blo 1744573 1746223 := bstep (se 1 (by rfl) ⟨1309667, by rfl⟩ : syracuseStep 1746223 = 2619335) B2619335
theorem B3925403 : Blo 1744573 3925403 := bstep (se 1 (by rfl) ⟨2944052, by rfl⟩ : syracuseStep 3925403 = 5888105) B5888105
theorem B8840663 : Blo 1744573 8840663 := bstep (se 1 (by rfl) ⟨6630497, by rfl⟩ : syracuseStep 8840663 = 13260995) B13260995
theorem B4417051 : Blo 1744573 4417051 := bstep (se 1 (by rfl) ⟨3312788, by rfl⟩ : syracuseStep 4417051 = 6625577) B6625577
theorem B1746459 : Blo 1744573 1746459 := bstep (se 1 (by rfl) ⟨1309844, by rfl⟩ : syracuseStep 1746459 = 2619689) B2619689
theorem B1746463 : Blo 1744573 1746463 := bstep (se 1 (by rfl) ⟨1309847, by rfl⟩ : syracuseStep 1746463 = 2619695) B2619695
theorem B3147295 : Blo 1744573 3147295 := bstep (se 1 (by rfl) ⟨2360471, by rfl⟩ : syracuseStep 3147295 = 4720943) B4720943
theorem B6628979 : Blo 1744573 6628979 := bstep (se 1 (by rfl) ⟨4971734, by rfl⟩ : syracuseStep 6628979 = 9943469) B9943469
theorem B6629161 : Blo 1744573 6629161 := bstep (se 2 (by rfl) ⟨2485935, by rfl⟩ : syracuseStep 6629161 = 4971871) B4971871
theorem B3925979 : Blo 1744573 3925979 := bstep (se 1 (by rfl) ⟨2944484, by rfl⟩ : syracuseStep 3925979 = 5888969) B5888969
theorem B6629435 : Blo 1744573 6629435 := bstep (se 1 (by rfl) ⟨4972076, by rfl⟩ : syracuseStep 6629435 = 9944153) B9944153
theorem B3926159 : Blo 1744573 3926159 := bstep (se 1 (by rfl) ⟨2944619, by rfl⟩ : syracuseStep 3926159 = 5889239) B5889239
theorem B4417679 : Blo 1744573 4417679 := bstep (se 1 (by rfl) ⟨3313259, by rfl⟩ : syracuseStep 4417679 = 6626519) B6626519
theorem B19884203 : Blo 1744573 19884203 := bstep (se 1 (by rfl) ⟨14913152, by rfl⟩ : syracuseStep 19884203 = 29826305) B29826305
theorem B3926249 : Blo 1744573 3926249 := bstep (se 2 (by rfl) ⟨1472343, by rfl⟩ : syracuseStep 3926249 = 2944687) B2944687
theorem B2484535 : Blo 1744573 2484535 := bstep (se 1 (by rfl) ⟨1863401, by rfl⟩ : syracuseStep 2484535 = 3726803) B3726803
theorem B17918297 : Blo 1744573 17918297 := bstep (se 2 (by rfl) ⟨6719361, by rfl⟩ : syracuseStep 17918297 = 13438723) B13438723
theorem B3311999 : Blo 1744573 3311999 := bstep (se 1 (by rfl) ⟨2483999, by rfl⟩ : syracuseStep 3311999 = 4967999) B4967999
theorem B3926519 : Blo 1744573 3926519 := bstep (se 1 (by rfl) ⟨2944889, by rfl⟩ : syracuseStep 3926519 = 5889779) B5889779
theorem B3312265 : Blo 1744573 3312265 := bstep (se 2 (by rfl) ⟨1242099, by rfl⟩ : syracuseStep 3312265 = 2484199) B2484199
theorem B18868889 : Blo 1744573 18868889 := bstep (se 2 (by rfl) ⟨7075833, by rfl⟩ : syracuseStep 18868889 = 14151667) B14151667
theorem B5589665 : Blo 1744573 5589665 := bstep (se 2 (by rfl) ⟨2096124, by rfl⟩ : syracuseStep 5589665 = 4192249) B4192249
theorem B19892951 : Blo 1744573 19892951 := bstep (se 1 (by rfl) ⟨14919713, by rfl⟩ : syracuseStep 19892951 = 29839427) B29839427
theorem B2944073 : Blo 1744573 2944073 := bstep (se 2 (by rfl) ⟨1104027, by rfl⟩ : syracuseStep 2944073 = 2208055) B2208055
theorem B3927113 : Blo 1744573 3927113 := bstep (se 2 (by rfl) ⟨1472667, by rfl⟩ : syracuseStep 3927113 = 2945335) B2945335
theorem B5893289 : Blo 1744573 5893289 := bstep (se 2 (by rfl) ⟨2209983, by rfl⟩ : syracuseStep 5893289 = 4419967) B4419967
theorem B33549673 : Blo 1744573 33549673 := bstep (se 2 (by rfl) ⟨12581127, by rfl⟩ : syracuseStep 33549673 = 25162255) B25162255
theorem B9432733 : Blo 1744573 9432733 := bstep (se 3 (by rfl) ⟨1768637, by rfl⟩ : syracuseStep 9432733 = 3537275) B3537275
theorem B21515975 : Blo 1744573 21515975 := bstep (se 1 (by rfl) ⟨16136981, by rfl⟩ : syracuseStep 21515975 = 32273963) B32273963
theorem B169938647 : Blo 1744573 169938647 := bstep (se 1 (by rfl) ⟨127453985, by rfl⟩ : syracuseStep 169938647 = 254907971) B254907971
theorem B7769843 : Blo 1744573 7769843 := bstep (se 1 (by rfl) ⟨5827382, by rfl⟩ : syracuseStep 7769843 = 11654765) B11654765
theorem B5893883 : Blo 1744573 5893883 := bstep (se 1 (by rfl) ⟨4420412, by rfl⟩ : syracuseStep 5893883 = 8840825) B8840825
theorem B2617151 : Blo 1744573 2617151 := bstep (se 1 (by rfl) ⟨1962863, by rfl⟩ : syracuseStep 2617151 = 3925727) B3925727
theorem B22368089 : Blo 1744573 22368089 := bstep (se 2 (by rfl) ⟨8388033, by rfl⟩ : syracuseStep 22368089 = 16776067) B16776067
theorem B16772993 : Blo 1744573 16772993 := bstep (se 2 (by rfl) ⟨6289872, by rfl⟩ : syracuseStep 16772993 = 12579745) B12579745
theorem B7458749 : Blo 1744573 7458749 := bstep (se 3 (by rfl) ⟨1398515, by rfl⟩ : syracuseStep 7458749 = 2797031) B2797031
theorem B14905295 : Blo 1744573 14905295 := bstep (se 1 (by rfl) ⟨11178971, by rfl⟩ : syracuseStep 14905295 = 22357943) B22357943
theorem B11489255 : Blo 1744573 11489255 := bstep (se 1 (by rfl) ⟨8616941, by rfl⟩ : syracuseStep 11489255 = 17233883) B17233883
theorem B3313639 : Blo 1744573 3313639 := bstep (se 1 (by rfl) ⟨2485229, by rfl⟩ : syracuseStep 3313639 = 4970459) B4970459
theorem B2985959 : Blo 1744573 2985959 := bstep (se 1 (by rfl) ⟨2239469, by rfl⟩ : syracuseStep 2985959 = 4478939) B4478939
theorem B2617337 : Blo 1744573 2617337 := bstep (se 2 (by rfl) ⟨981501, by rfl⟩ : syracuseStep 2617337 = 1963003) B1963003
theorem B2617577 : Blo 1744573 2617577 := bstep (se 2 (by rfl) ⟨981591, by rfl⟩ : syracuseStep 2617577 = 1963183) B1963183
theorem B2617703 : Blo 1744573 2617703 := bstep (se 1 (by rfl) ⟨1963277, by rfl⟩ : syracuseStep 2617703 = 3926555) B3926555
theorem B544477571 : Blo 1744573 544477571 := bstep (se 1 (by rfl) ⟨408358178, by rfl⟩ : syracuseStep 544477571 = 816716357) B816716357
theorem B3928841 : Blo 1744573 3928841 := bstep (se 2 (by rfl) ⟨1473315, by rfl⟩ : syracuseStep 3928841 = 2946631) B2946631
theorem B16356107 : Blo 1744573 16356107 := bstep (se 1 (by rfl) ⟨12267080, by rfl⟩ : syracuseStep 16356107 = 24534161) B24534161
theorem B57398057 : Blo 1744573 57398057 := bstep (se 2 (by rfl) ⟨21524271, by rfl⟩ : syracuseStep 57398057 = 43048543) B43048543
theorem B2945855 : Blo 1744573 2945855 := bstep (se 1 (by rfl) ⟨2209391, by rfl⟩ : syracuseStep 2945855 = 4418783) B4418783
theorem B3928895 : Blo 1744573 3928895 := bstep (se 1 (by rfl) ⟨2946671, by rfl⟩ : syracuseStep 3928895 = 5893343) B5893343
theorem B2618249 : Blo 1744573 2618249 := bstep (se 2 (by rfl) ⟨981843, by rfl⟩ : syracuseStep 2618249 = 1963687) B1963687
theorem B2945929 : Blo 1744573 2945929 := bstep (se 2 (by rfl) ⟨1104723, by rfl⟩ : syracuseStep 2945929 = 2209447) B2209447
theorem B3929039 : Blo 1744573 3929039 := bstep (se 1 (by rfl) ⟨2946779, by rfl⟩ : syracuseStep 3929039 = 5893559) B5893559
theorem B3314657 : Blo 1744573 3314657 := bstep (se 2 (by rfl) ⟨1242996, by rfl⟩ : syracuseStep 3314657 = 2485993) B2485993
theorem B9942011 : Blo 1744573 9942011 := bstep (se 1 (by rfl) ⟨7456508, by rfl⟩ : syracuseStep 9942011 = 14913017) B14913017
theorem B19887119 : Blo 1744573 19887119 := bstep (se 1 (by rfl) ⟨14915339, by rfl⟩ : syracuseStep 19887119 = 29830679) B29830679
theorem B3929129 : Blo 1744573 3929129 := bstep (se 2 (by rfl) ⟨1473423, by rfl⟩ : syracuseStep 3929129 = 2946847) B2946847
theorem B14914793 : Blo 1744573 14914793 := bstep (se 2 (by rfl) ⟨5593047, by rfl⟩ : syracuseStep 14914793 = 11186095) B11186095
theorem B14152967 : Blo 1744573 14152967 := bstep (se 1 (by rfl) ⟨10614725, by rfl⟩ : syracuseStep 14152967 = 21229451) B21229451
theorem B2618633 : Blo 1744573 2618633 := bstep (se 2 (by rfl) ⟨981987, by rfl⟩ : syracuseStep 2618633 = 1963975) B1963975
theorem B1963327 : Blo 1744573 1963327 := bstep (se 1 (by rfl) ⟨1472495, by rfl⟩ : syracuseStep 1963327 = 2944991) B2944991
theorem B2618687 : Blo 1744573 2618687 := bstep (se 1 (by rfl) ⟨1964015, by rfl⟩ : syracuseStep 2618687 = 3928031) B3928031
theorem B3929417 : Blo 1744573 3929417 := bstep (se 2 (by rfl) ⟨1473531, by rfl⟩ : syracuseStep 3929417 = 2947063) B2947063
theorem B6288835 : Blo 1744573 6288835 := bstep (se 1 (by rfl) ⟨4716626, by rfl⟩ : syracuseStep 6288835 = 9433253) B9433253
theorem B2619113 : Blo 1744573 2619113 := bstep (se 2 (by rfl) ⟨982167, by rfl⟩ : syracuseStep 2619113 = 1964335) B1964335
theorem B2946793 : Blo 1744573 2946793 := bstep (se 2 (by rfl) ⟨1105047, by rfl⟩ : syracuseStep 2946793 = 2210095) B2210095
theorem B1963759 : Blo 1744573 1963759 := bstep (se 1 (by rfl) ⟨1472819, by rfl⟩ : syracuseStep 1963759 = 2945639) B2945639
theorem B2619119 : Blo 1744573 2619119 := bstep (se 1 (by rfl) ⟨1964339, by rfl⟩ : syracuseStep 2619119 = 3928679) B3928679
theorem B8836937 : Blo 1744573 8836937 := bstep (se 2 (by rfl) ⟨3313851, by rfl⟩ : syracuseStep 8836937 = 6627703) B6627703
theorem B1963867 : Blo 1744573 1963867 := bstep (se 1 (by rfl) ⟨1472900, by rfl⟩ : syracuseStep 1963867 = 2945801) B2945801
theorem B2619575 : Blo 1744573 2619575 := bstep (se 1 (by rfl) ⟨1964681, by rfl⟩ : syracuseStep 2619575 = 3929363) B3929363
theorem B1964263 : Blo 1744573 1964263 := bstep (se 1 (by rfl) ⟨1473197, by rfl⟩ : syracuseStep 1964263 = 2946395) B2946395
theorem B2619623 : Blo 1744573 2619623 := bstep (se 1 (by rfl) ⟨1964717, by rfl⟩ : syracuseStep 2619623 = 3929435) B3929435
theorem B14907685 : Blo 1744573 14907685 := bstep (se 4 (by rfl) ⟨1397595, by rfl⟩ : syracuseStep 14907685 = 2795191) B2795191
theorem B19888577 : Blo 1744573 19888577 := bstep (se 2 (by rfl) ⟨7458216, by rfl⟩ : syracuseStep 19888577 = 14916433) B14916433
theorem B4250089 : Blo 1744573 4250089 := bstep (se 2 (by rfl) ⟨1593783, by rfl⟩ : syracuseStep 4250089 = 3187567) B3187567
theorem B2652763 : Blo 1744573 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B7453417 : Blo 1744573 7453417 := bstep (se 2 (by rfl) ⟨2795031, by rfl⟩ : syracuseStep 7453417 = 5590063) B5590063
theorem B31849487 : Blo 1744573 31849487 := bstep (se 1 (by rfl) ⟨23887115, by rfl⟩ : syracuseStep 31849487 = 47774231) B47774231
theorem B8838233 : Blo 1744573 8838233 := bstep (se 2 (by rfl) ⟨3314337, by rfl⟩ : syracuseStep 8838233 = 6628675) B6628675
theorem B5594791 : Blo 1744573 5594791 := bstep (se 1 (by rfl) ⟨4196093, by rfl⟩ : syracuseStep 5594791 = 8392187) B8392187
theorem B6627035 : Blo 1744573 6627035 := bstep (se 1 (by rfl) ⟨4970276, by rfl⟩ : syracuseStep 6627035 = 9940553) B9940553
theorem B1744615 : Blo 1744573 1744615 := bstep (se 1 (by rfl) ⟨1308461, by rfl⟩ : syracuseStep 1744615 = 2616923) B2616923
theorem B16785143 : Blo 1744573 16785143 := bstep (se 1 (by rfl) ⟨12588857, by rfl⟩ : syracuseStep 16785143 = 25177715) B25177715
theorem B1744671 : Blo 1744573 1744671 := bstep (se 1 (by rfl) ⟨1308503, by rfl⟩ : syracuseStep 1744671 = 2617007) B2617007
theorem B1744751 : Blo 1744573 1744751 := bstep (se 1 (by rfl) ⟨1308563, by rfl⟩ : syracuseStep 1744751 = 2617127) B2617127
theorem B1744807 : Blo 1744573 1744807 := bstep (se 1 (by rfl) ⟨1308605, by rfl⟩ : syracuseStep 1744807 = 2617211) B2617211
theorem B1745051 : Blo 1744573 1745051 := bstep (se 1 (by rfl) ⟨1308788, by rfl⟩ : syracuseStep 1745051 = 2617577) B2617577
theorem B1745135 : Blo 1744573 1745135 := bstep (se 1 (by rfl) ⟨1308851, by rfl⟩ : syracuseStep 1745135 = 2617703) B2617703
theorem B10904071 : Blo 1744573 10904071 := bstep (se 1 (by rfl) ⟨8178053, by rfl⟩ : syracuseStep 10904071 = 16356107) B16356107
theorem B38265371 : Blo 1744573 38265371 := bstep (se 1 (by rfl) ⟨28699028, by rfl⟩ : syracuseStep 38265371 = 57398057) B57398057
theorem B1745499 : Blo 1744573 1745499 := bstep (se 1 (by rfl) ⟨1309124, by rfl⟩ : syracuseStep 1745499 = 2618249) B2618249
theorem B6628007 : Blo 1744573 6628007 := bstep (se 1 (by rfl) ⟨4971005, by rfl⟩ : syracuseStep 6628007 = 9942011) B9942011
theorem B1745755 : Blo 1744573 1745755 := bstep (se 1 (by rfl) ⟨1309316, by rfl⟩ : syracuseStep 1745755 = 2618633) B2618633
theorem B4416353 : Blo 1744573 4416353 := bstep (se 2 (by rfl) ⟨1656132, by rfl⟩ : syracuseStep 4416353 = 3312265) B3312265
theorem B1745791 : Blo 1744573 1745791 := bstep (se 1 (by rfl) ⟨1309343, by rfl⟩ : syracuseStep 1745791 = 2618687) B2618687
theorem B9937889 : Blo 1744573 9937889 := bstep (se 2 (by rfl) ⟨3726708, by rfl⟩ : syracuseStep 9937889 = 7453417) B7453417
theorem B1746075 : Blo 1744573 1746075 := bstep (se 1 (by rfl) ⟨1309556, by rfl⟩ : syracuseStep 1746075 = 2619113) B2619113
theorem B1746079 : Blo 1744573 1746079 := bstep (se 1 (by rfl) ⟨1309559, by rfl⟩ : syracuseStep 1746079 = 2619119) B2619119
theorem B5891291 : Blo 1744573 5891291 := bstep (se 1 (by rfl) ⟨4418468, by rfl⟩ : syracuseStep 5891291 = 8836937) B8836937
theorem B25494749 : Blo 1744573 25494749 := bstep (se 3 (by rfl) ⟨4780265, by rfl⟩ : syracuseStep 25494749 = 9560531) B9560531
theorem B13256135 : Blo 1744573 13256135 := bstep (se 1 (by rfl) ⟨9942101, by rfl⟩ : syracuseStep 13256135 = 19884203) B19884203
theorem B1746383 : Blo 1744573 1746383 := bstep (se 1 (by rfl) ⟨1309787, by rfl⟩ : syracuseStep 1746383 = 2619575) B2619575
theorem B1746415 : Blo 1744573 1746415 := bstep (se 1 (by rfl) ⟨1309811, by rfl⟩ : syracuseStep 1746415 = 2619623) B2619623
theorem B11945531 : Blo 1744573 11945531 := bstep (se 1 (by rfl) ⟨8959148, by rfl⟩ : syracuseStep 11945531 = 17918297) B17918297
theorem B4196393 : Blo 1744573 4196393 := bstep (se 2 (by rfl) ⟨1573647, by rfl⟩ : syracuseStep 4196393 = 3147295) B3147295
theorem B5892155 : Blo 1744573 5892155 := bstep (se 1 (by rfl) ⟨4419116, by rfl⟩ : syracuseStep 5892155 = 8838233) B8838233
theorem B12576977 : Blo 1744573 12576977 := bstep (se 2 (by rfl) ⟨4716366, by rfl⟩ : syracuseStep 12576977 = 9432733) B9432733
theorem B4418023 : Blo 1744573 4418023 := bstep (se 1 (by rfl) ⟨3313517, by rfl⟩ : syracuseStep 4418023 = 6627035) B6627035
theorem B5179895 : Blo 1744573 5179895 := bstep (se 1 (by rfl) ⟨3884921, by rfl⟩ : syracuseStep 5179895 = 7769843) B7769843
theorem B14912059 : Blo 1744573 14912059 := bstep (se 1 (by rfl) ⟨11184044, by rfl⟩ : syracuseStep 14912059 = 22368089) B22368089
theorem B4418185 : Blo 1744573 4418185 := bstep (se 2 (by rfl) ⟨1656819, by rfl⟩ : syracuseStep 4418185 = 3313639) B3313639
theorem B11332475 : Blo 1744573 11332475 := bstep (se 1 (by rfl) ⟨8499356, by rfl⟩ : syracuseStep 11332475 = 16998713) B16998713
theorem B19876913 : Blo 1744573 19876913 := bstep (se 2 (by rfl) ⟨7453842, by rfl⟩ : syracuseStep 19876913 = 14907685) B14907685
theorem B3312713 : Blo 1744573 3312713 := bstep (se 2 (by rfl) ⟨1242267, by rfl⟩ : syracuseStep 3312713 = 2484535) B2484535
theorem B9940097 : Blo 1744573 9940097 := bstep (se 2 (by rfl) ⟨3727536, by rfl⟩ : syracuseStep 9940097 = 7455073) B7455073
theorem B7957703 : Blo 1744573 7957703 := bstep (se 1 (by rfl) ⟨5968277, by rfl⟩ : syracuseStep 7957703 = 11936555) B11936555
theorem B206892319 : Blo 1744573 206892319 := bstep (se 1 (by rfl) ⟨155169239, by rfl⟩ : syracuseStep 206892319 = 310338479) B310338479
theorem B9940279 : Blo 1744573 9940279 := bstep (se 1 (by rfl) ⟨7455209, by rfl⟩ : syracuseStep 9940279 = 14910419) B14910419
theorem B13258079 : Blo 1744573 13258079 := bstep (se 1 (by rfl) ⟨9943559, by rfl⟩ : syracuseStep 13258079 = 19887119) B19887119
theorem B2616935 : Blo 1744573 2616935 := bstep (se 1 (by rfl) ⟨1962701, by rfl⟩ : syracuseStep 2616935 = 3925403) B3925403
theorem B5893775 : Blo 1744573 5893775 := bstep (se 1 (by rfl) ⟨4420331, by rfl⟩ : syracuseStep 5893775 = 8840663) B8840663
theorem B4419319 : Blo 1744573 4419319 := bstep (se 1 (by rfl) ⟨3314489, by rfl⟩ : syracuseStep 4419319 = 6628979) B6628979
theorem B3927905 : Blo 1744573 3927905 := bstep (se 2 (by rfl) ⟨1472964, by rfl⟩ : syracuseStep 3927905 = 2945929) B2945929
theorem B2617319 : Blo 1744573 2617319 := bstep (se 1 (by rfl) ⟨1962989, by rfl⟩ : syracuseStep 2617319 = 3925979) B3925979
theorem B4419623 : Blo 1744573 4419623 := bstep (se 1 (by rfl) ⟨3314717, by rfl⟩ : syracuseStep 4419623 = 6629435) B6629435
theorem B2617439 : Blo 1744573 2617439 := bstep (se 1 (by rfl) ⟨1963079, by rfl⟩ : syracuseStep 2617439 = 3926159) B3926159
theorem B2945119 : Blo 1744573 2945119 := bstep (se 1 (by rfl) ⟨2208839, by rfl⟩ : syracuseStep 2945119 = 4417679) B4417679
theorem B2617499 : Blo 1744573 2617499 := bstep (se 1 (by rfl) ⟨1963124, by rfl⟩ : syracuseStep 2617499 = 3926249) B3926249
theorem B2207999 : Blo 1744573 2207999 := bstep (se 1 (by rfl) ⟨1655999, by rfl⟩ : syracuseStep 2207999 = 3311999) B3311999
theorem B13259051 : Blo 1744573 13259051 := bstep (se 1 (by rfl) ⟨9944288, by rfl⟩ : syracuseStep 13259051 = 19888577) B19888577
theorem B2617679 : Blo 1744573 2617679 := bstep (se 1 (by rfl) ⟨1963259, by rfl⟩ : syracuseStep 2617679 = 3926519) B3926519
theorem B2617769 : Blo 1744573 2617769 := bstep (se 2 (by rfl) ⟨981663, by rfl⟩ : syracuseStep 2617769 = 1963327) B1963327
theorem B12579259 : Blo 1744573 12579259 := bstep (se 1 (by rfl) ⟨9434444, by rfl⟩ : syracuseStep 12579259 = 18868889) B18868889
theorem B44732897 : Blo 1744573 44732897 := bstep (se 2 (by rfl) ⟨16774836, by rfl⟩ : syracuseStep 44732897 = 33549673) B33549673
theorem B8385113 : Blo 1744573 8385113 := bstep (se 2 (by rfl) ⟨3144417, by rfl⟩ : syracuseStep 8385113 = 6288835) B6288835
theorem B1962715 : Blo 1744573 1962715 := bstep (se 1 (by rfl) ⟨1472036, by rfl⟩ : syracuseStep 1962715 = 2944073) B2944073
theorem B2618075 : Blo 1744573 2618075 := bstep (se 1 (by rfl) ⟨1963556, by rfl⟩ : syracuseStep 2618075 = 3927113) B3927113
theorem B3928859 : Blo 1744573 3928859 := bstep (se 1 (by rfl) ⟨2946644, by rfl⟩ : syracuseStep 3928859 = 5893289) B5893289
theorem B7459721 : Blo 1744573 7459721 := bstep (se 2 (by rfl) ⟨2797395, by rfl⟩ : syracuseStep 7459721 = 5594791) B5594791
theorem B3929057 : Blo 1744573 3929057 := bstep (se 2 (by rfl) ⟨1473396, by rfl⟩ : syracuseStep 3929057 = 2946793) B2946793
theorem B2618345 : Blo 1744573 2618345 := bstep (se 2 (by rfl) ⟨981879, by rfl⟩ : syracuseStep 2618345 = 1963759) B1963759
theorem B2618489 : Blo 1744573 2618489 := bstep (se 2 (by rfl) ⟨981933, by rfl⟩ : syracuseStep 2618489 = 1963867) B1963867
theorem B113292431 : Blo 1744573 113292431 := bstep (se 1 (by rfl) ⟨84969323, by rfl⟩ : syracuseStep 113292431 = 169938647) B169938647
theorem B3929255 : Blo 1744573 3929255 := bstep (se 1 (by rfl) ⟨2946941, by rfl⟩ : syracuseStep 3929255 = 5893883) B5893883
theorem B362985047 : Blo 1744573 362985047 := bstep (se 1 (by rfl) ⟨272238785, by rfl⟩ : syracuseStep 362985047 = 544477571) B544477571
theorem B2619017 : Blo 1744573 2619017 := bstep (se 2 (by rfl) ⟨982131, by rfl⟩ : syracuseStep 2619017 = 1964263) B1964263
theorem B4970231 : Blo 1744573 4970231 := bstep (se 1 (by rfl) ⟨3727673, by rfl⟩ : syracuseStep 4970231 = 7455347) B7455347
theorem B18880303 : Blo 1744573 18880303 := bstep (se 1 (by rfl) ⟨14160227, by rfl⟩ : syracuseStep 18880303 = 28320455) B28320455
theorem B2619227 : Blo 1744573 2619227 := bstep (se 1 (by rfl) ⟨1964420, by rfl⟩ : syracuseStep 2619227 = 3928841) B3928841
theorem B16996219 : Blo 1744573 16996219 := bstep (se 1 (by rfl) ⟨12747164, by rfl⟩ : syracuseStep 16996219 = 25494329) B25494329
theorem B1963903 : Blo 1744573 1963903 := bstep (se 1 (by rfl) ⟨1472927, by rfl⟩ : syracuseStep 1963903 = 2945855) B2945855
theorem B2619263 : Blo 1744573 2619263 := bstep (se 1 (by rfl) ⟨1964447, by rfl⟩ : syracuseStep 2619263 = 3928895) B3928895
theorem B2619359 : Blo 1744573 2619359 := bstep (se 1 (by rfl) ⟨1964519, by rfl⟩ : syracuseStep 2619359 = 3929039) B3929039
theorem B2209771 : Blo 1744573 2209771 := bstep (se 1 (by rfl) ⟨1657328, by rfl⟩ : syracuseStep 2209771 = 3314657) B3314657
theorem B2619419 : Blo 1744573 2619419 := bstep (se 1 (by rfl) ⟨1964564, by rfl⟩ : syracuseStep 2619419 = 3929129) B3929129
theorem B3537017 : Blo 1744573 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B9943195 : Blo 1744573 9943195 := bstep (se 1 (by rfl) ⟨7457396, by rfl⟩ : syracuseStep 9943195 = 14914793) B14914793
theorem B9435311 : Blo 1744573 9435311 := bstep (se 1 (by rfl) ⟨7076483, by rfl⟩ : syracuseStep 9435311 = 14152967) B14152967
theorem B2619611 : Blo 1744573 2619611 := bstep (se 1 (by rfl) ⟨1964708, by rfl⟩ : syracuseStep 2619611 = 3929417) B3929417
theorem B22371065 : Blo 1744573 22371065 := bstep (se 2 (by rfl) ⟨8389149, by rfl⟩ : syracuseStep 22371065 = 16778299) B16778299
theorem B40295393 : Blo 1744573 40295393 := bstep (se 2 (by rfl) ⟨15110772, by rfl⟩ : syracuseStep 40295393 = 30221545) B30221545
theorem B3726443 : Blo 1744573 3726443 := bstep (se 1 (by rfl) ⟨2794832, by rfl⟩ : syracuseStep 3726443 = 5589665) B5589665
theorem B13261967 : Blo 1744573 13261967 := bstep (se 1 (by rfl) ⟨9946475, by rfl⟩ : syracuseStep 13261967 = 19892951) B19892951
theorem B21232991 : Blo 1744573 21232991 := bstep (se 1 (by rfl) ⟨15924743, by rfl⟩ : syracuseStep 21232991 = 31849487) B31849487
theorem B5889401 : Blo 1744573 5889401 := bstep (se 2 (by rfl) ⟨2208525, by rfl⟩ : syracuseStep 5889401 = 4417051) B4417051
theorem B8838881 : Blo 1744573 8838881 := bstep (se 2 (by rfl) ⟨3314580, by rfl⟩ : syracuseStep 8838881 = 6629161) B6629161
theorem B14343983 : Blo 1744573 14343983 := bstep (se 1 (by rfl) ⟨10757987, by rfl⟩ : syracuseStep 14343983 = 21515975) B21515975
theorem B11190095 : Blo 1744573 11190095 := bstep (se 1 (by rfl) ⟨8392571, by rfl⟩ : syracuseStep 11190095 = 16785143) B16785143
theorem B1744767 : Blo 1744573 1744767 := bstep (se 1 (by rfl) ⟨1308575, by rfl⟩ : syracuseStep 1744767 = 2617151) B2617151
theorem B22667141 : Blo 1744573 22667141 := bstep (se 4 (by rfl) ⟨2125044, by rfl⟩ : syracuseStep 22667141 = 4250089) B4250089
theorem B11181995 : Blo 1744573 11181995 := bstep (se 1 (by rfl) ⟨8386496, by rfl⟩ : syracuseStep 11181995 = 16772993) B16772993
theorem B4972499 : Blo 1744573 4972499 := bstep (se 1 (by rfl) ⟨3729374, by rfl⟩ : syracuseStep 4972499 = 7458749) B7458749
theorem B9936863 : Blo 1744573 9936863 := bstep (se 1 (by rfl) ⟨7452647, by rfl⟩ : syracuseStep 9936863 = 14905295) B14905295
theorem B7659503 : Blo 1744573 7659503 := bstep (se 1 (by rfl) ⟨5744627, by rfl⟩ : syracuseStep 7659503 = 11489255) B11489255
theorem B1990639 : Blo 1744573 1990639 := bstep (se 1 (by rfl) ⟨1492979, by rfl⟩ : syracuseStep 1990639 = 2985959) B2985959
theorem B1744891 : Blo 1744573 1744891 := bstep (se 1 (by rfl) ⟨1308668, by rfl⟩ : syracuseStep 1744891 = 2617337) B2617337
theorem B1744959 : Blo 1744573 1744959 := bstep (se 1 (by rfl) ⟨1308719, by rfl⟩ : syracuseStep 1744959 = 2617439) B2617439
theorem B1744999 : Blo 1744573 1744999 := bstep (se 1 (by rfl) ⟨1308749, by rfl⟩ : syracuseStep 1744999 = 2617499) B2617499
theorem B8839367 : Blo 1744573 8839367 := bstep (se 1 (by rfl) ⟨6629525, by rfl⟩ : syracuseStep 8839367 = 13259051) B13259051
theorem B1745119 : Blo 1744573 1745119 := bstep (se 1 (by rfl) ⟨1308839, by rfl⟩ : syracuseStep 1745119 = 2617679) B2617679
theorem B1745179 : Blo 1744573 1745179 := bstep (se 1 (by rfl) ⟨1308884, by rfl⟩ : syracuseStep 1745179 = 2617769) B2617769
theorem B9937181 : Blo 1744573 9937181 := bstep (se 3 (by rfl) ⟨1863221, by rfl⟩ : syracuseStep 9937181 = 3726443) B3726443
theorem B25510247 : Blo 1744573 25510247 := bstep (se 1 (by rfl) ⟨19132685, by rfl⟩ : syracuseStep 25510247 = 38265371) B38265371
theorem B1745383 : Blo 1744573 1745383 := bstep (se 1 (by rfl) ⟨1309037, by rfl⟩ : syracuseStep 1745383 = 2618075) B2618075
theorem B4973147 : Blo 1744573 4973147 := bstep (se 1 (by rfl) ⟨3729860, by rfl⟩ : syracuseStep 4973147 = 7459721) B7459721
theorem B5890697 : Blo 1744573 5890697 := bstep (se 2 (by rfl) ⟨2209011, by rfl⟩ : syracuseStep 5890697 = 4418023) B4418023
theorem B1745563 : Blo 1744573 1745563 := bstep (se 1 (by rfl) ⟨1309172, by rfl⟩ : syracuseStep 1745563 = 2618345) B2618345
theorem B19882745 : Blo 1744573 19882745 := bstep (se 2 (by rfl) ⟨7456029, by rfl⟩ : syracuseStep 19882745 = 14912059) B14912059
theorem B1745659 : Blo 1744573 1745659 := bstep (se 1 (by rfl) ⟨1309244, by rfl⟩ : syracuseStep 1745659 = 2618489) B2618489
theorem B5890913 : Blo 1744573 5890913 := bstep (se 2 (by rfl) ⟨2209092, by rfl⟩ : syracuseStep 5890913 = 4418185) B4418185
theorem B7963687 : Blo 1744573 7963687 := bstep (se 1 (by rfl) ⟨5972765, by rfl⟩ : syracuseStep 7963687 = 11945531) B11945531
theorem B1746011 : Blo 1744573 1746011 := bstep (se 1 (by rfl) ⟨1309508, by rfl⟩ : syracuseStep 1746011 = 2619017) B2619017
theorem B1746151 : Blo 1744573 1746151 := bstep (se 1 (by rfl) ⟨1309613, by rfl⟩ : syracuseStep 1746151 = 2619227) B2619227
theorem B1746175 : Blo 1744573 1746175 := bstep (se 1 (by rfl) ⟨1309631, by rfl⟩ : syracuseStep 1746175 = 2619263) B2619263
theorem B1746239 : Blo 1744573 1746239 := bstep (se 1 (by rfl) ⟨1309679, by rfl⟩ : syracuseStep 1746239 = 2619359) B2619359
theorem B1746279 : Blo 1744573 1746279 := bstep (se 1 (by rfl) ⟨1309709, by rfl⟩ : syracuseStep 1746279 = 2619419) B2619419
theorem B1746407 : Blo 1744573 1746407 := bstep (se 1 (by rfl) ⟨1309805, by rfl⟩ : syracuseStep 1746407 = 2619611) B2619611
theorem B90646501 : Blo 1744573 90646501 := bstep (se 4 (by rfl) ⟨8498109, by rfl⟩ : syracuseStep 90646501 = 16996219) B16996219
theorem B26863595 : Blo 1744573 26863595 := bstep (se 1 (by rfl) ⟨20147696, by rfl⟩ : syracuseStep 26863595 = 40295393) B40295393
theorem B8841311 : Blo 1744573 8841311 := bstep (se 1 (by rfl) ⟨6630983, by rfl⟩ : syracuseStep 8841311 = 13261967) B13261967
theorem B3926267 : Blo 1744573 3926267 := bstep (se 1 (by rfl) ⟨2944700, by rfl⟩ : syracuseStep 3926267 = 5889401) B5889401
theorem B5892425 : Blo 1744573 5892425 := bstep (se 2 (by rfl) ⟨2209659, by rfl⟩ : syracuseStep 5892425 = 4419319) B4419319
theorem B483518933 : Blo 1744573 483518933 := bstep (se 7 (by rfl) ⟨5666237, by rfl⟩ : syracuseStep 483518933 = 11332475) B11332475
theorem B5892587 : Blo 1744573 5892587 := bstep (se 1 (by rfl) ⟨4419440, by rfl⟩ : syracuseStep 5892587 = 8838881) B8838881
theorem B9562655 : Blo 1744573 9562655 := bstep (se 1 (by rfl) ⟨7171991, by rfl⟩ : syracuseStep 9562655 = 14343983) B14343983
theorem B5106335 : Blo 1744573 5106335 := bstep (se 1 (by rfl) ⟨3829751, by rfl⟩ : syracuseStep 5106335 = 7659503) B7659503
theorem B3926825 : Blo 1744573 3926825 := bstep (se 2 (by rfl) ⟨1472559, by rfl⟩ : syracuseStep 3926825 = 2945119) B2945119
theorem B13257593 : Blo 1744573 13257593 := bstep (se 2 (by rfl) ⟨4971597, by rfl⟩ : syracuseStep 13257593 = 9943195) B9943195
theorem B29821931 : Blo 1744573 29821931 := bstep (se 1 (by rfl) ⟨22366448, by rfl⟩ : syracuseStep 29821931 = 44732897) B44732897
theorem B5590075 : Blo 1744573 5590075 := bstep (se 1 (by rfl) ⟨4192556, by rfl⟩ : syracuseStep 5590075 = 8385113) B8385113
theorem B4418671 : Blo 1744573 4418671 := bstep (se 1 (by rfl) ⟨3314003, by rfl⟩ : syracuseStep 4418671 = 6628007) B6628007
theorem B2944235 : Blo 1744573 2944235 := bstep (se 1 (by rfl) ⟨2208176, by rfl⟩ : syracuseStep 2944235 = 4416353) B4416353
theorem B16772345 : Blo 1744573 16772345 := bstep (se 2 (by rfl) ⟨6289629, by rfl⟩ : syracuseStep 16772345 = 12579259) B12579259
theorem B3927527 : Blo 1744573 3927527 := bstep (se 1 (by rfl) ⟨2945645, by rfl⟩ : syracuseStep 3927527 = 5891291) B5891291
theorem B2616953 : Blo 1744573 2616953 := bstep (se 2 (by rfl) ⟨981357, by rfl⟩ : syracuseStep 2616953 = 1962715) B1962715
theorem B3313487 : Blo 1744573 3313487 := bstep (se 1 (by rfl) ⟨2485115, by rfl⟩ : syracuseStep 3313487 = 4970231) B4970231
theorem B2797595 : Blo 1744573 2797595 := bstep (se 1 (by rfl) ⟨2098196, by rfl⟩ : syracuseStep 2797595 = 4196393) B4196393
theorem B3928103 : Blo 1744573 3928103 := bstep (se 1 (by rfl) ⟨2946077, by rfl⟩ : syracuseStep 3928103 = 5892155) B5892155
theorem B8384651 : Blo 1744573 8384651 := bstep (se 1 (by rfl) ⟨6288488, by rfl⟩ : syracuseStep 8384651 = 12576977) B12576977
theorem B3453263 : Blo 1744573 3453263 := bstep (se 1 (by rfl) ⟨2589947, by rfl⟩ : syracuseStep 3453263 = 5179895) B5179895
theorem B14914043 : Blo 1744573 14914043 := bstep (se 1 (by rfl) ⟨11185532, by rfl⟩ : syracuseStep 14914043 = 22371065) B22371065
theorem B13251275 : Blo 1744573 13251275 := bstep (se 1 (by rfl) ⟨9938456, by rfl⟩ : syracuseStep 13251275 = 19876913) B19876913
theorem B2208475 : Blo 1744573 2208475 := bstep (se 1 (by rfl) ⟨1656356, by rfl⟩ : syracuseStep 2208475 = 3312713) B3312713
theorem B5305135 : Blo 1744573 5305135 := bstep (se 1 (by rfl) ⟨3978851, by rfl⟩ : syracuseStep 5305135 = 7957703) B7957703
theorem B60445709 : Blo 1744573 60445709 := bstep (se 3 (by rfl) ⟨11333570, by rfl⟩ : syracuseStep 60445709 = 22667141) B22667141
theorem B3929183 : Blo 1744573 3929183 := bstep (se 1 (by rfl) ⟨2946887, by rfl⟩ : syracuseStep 3929183 = 5893775) B5893775
theorem B2618537 : Blo 1744573 2618537 := bstep (se 2 (by rfl) ⟨981951, by rfl⟩ : syracuseStep 2618537 = 1963903) B1963903
theorem B7460063 : Blo 1744573 7460063 := bstep (se 1 (by rfl) ⟨5595047, by rfl⟩ : syracuseStep 7460063 = 11190095) B11190095
theorem B2618603 : Blo 1744573 2618603 := bstep (se 1 (by rfl) ⟨1963952, by rfl⟩ : syracuseStep 2618603 = 3927905) B3927905
theorem B3314999 : Blo 1744573 3314999 := bstep (se 1 (by rfl) ⟨2486249, by rfl⟩ : syracuseStep 3314999 = 4972499) B4972499
theorem B2946361 : Blo 1744573 2946361 := bstep (se 2 (by rfl) ⟨1104885, by rfl⟩ : syracuseStep 2946361 = 2209771) B2209771
theorem B6624575 : Blo 1744573 6624575 := bstep (se 1 (by rfl) ⟨4968431, by rfl⟩ : syracuseStep 6624575 = 9936863) B9936863
theorem B2946415 : Blo 1744573 2946415 := bstep (se 1 (by rfl) ⟨2209811, by rfl⟩ : syracuseStep 2946415 = 4419623) B4419623
theorem B2619239 : Blo 1744573 2619239 := bstep (se 1 (by rfl) ⟨1964429, by rfl⟩ : syracuseStep 2619239 = 3928859) B3928859
theorem B6625259 : Blo 1744573 6625259 := bstep (se 1 (by rfl) ⟨4968944, by rfl⟩ : syracuseStep 6625259 = 9937889) B9937889
theorem B2619371 : Blo 1744573 2619371 := bstep (se 1 (by rfl) ⟨1964528, by rfl⟩ : syracuseStep 2619371 = 3929057) B3929057
theorem B5887997 : Blo 1744573 5887997 := bstep (se 3 (by rfl) ⟨1103999, by rfl⟩ : syracuseStep 5887997 = 2207999) B2207999
theorem B14538761 : Blo 1744573 14538761 := bstep (se 2 (by rfl) ⟨5452035, by rfl⟩ : syracuseStep 14538761 = 10904071) B10904071
theorem B75528287 : Blo 1744573 75528287 := bstep (se 1 (by rfl) ⟨56646215, by rfl⟩ : syracuseStep 75528287 = 113292431) B113292431
theorem B2619503 : Blo 1744573 2619503 := bstep (se 1 (by rfl) ⟨1964627, by rfl⟩ : syracuseStep 2619503 = 3929255) B3929255
theorem B16996499 : Blo 1744573 16996499 := bstep (se 1 (by rfl) ⟨12747374, by rfl⟩ : syracuseStep 16996499 = 25494749) B25494749
theorem B8837423 : Blo 1744573 8837423 := bstep (se 1 (by rfl) ⟨6628067, by rfl⟩ : syracuseStep 8837423 = 13256135) B13256135
theorem B241990031 : Blo 1744573 241990031 := bstep (se 1 (by rfl) ⟨181492523, by rfl⟩ : syracuseStep 241990031 = 362985047) B362985047
theorem B2358011 : Blo 1744573 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B6290207 : Blo 1744573 6290207 := bstep (se 1 (by rfl) ⟨4717655, by rfl⟩ : syracuseStep 6290207 = 9435311) B9435311
theorem B275856425 : Blo 1744573 275856425 := bstep (se 2 (by rfl) ⟨103446159, by rfl⟩ : syracuseStep 275856425 = 206892319) B206892319
theorem B13253705 : Blo 1744573 13253705 := bstep (se 2 (by rfl) ⟨4970139, by rfl⟩ : syracuseStep 13253705 = 9940279) B9940279
theorem B6626731 : Blo 1744573 6626731 := bstep (se 1 (by rfl) ⟨4970048, by rfl⟩ : syracuseStep 6626731 = 9940097) B9940097
theorem B14155327 : Blo 1744573 14155327 := bstep (se 1 (by rfl) ⟨10616495, by rfl⟩ : syracuseStep 14155327 = 21232991) B21232991
theorem B8838719 : Blo 1744573 8838719 := bstep (se 1 (by rfl) ⟨6629039, by rfl⟩ : syracuseStep 8838719 = 13258079) B13258079
theorem B25173737 : Blo 1744573 25173737 := bstep (se 2 (by rfl) ⟨9440151, by rfl⟩ : syracuseStep 25173737 = 18880303) B18880303
theorem B1744623 : Blo 1744573 1744623 := bstep (se 1 (by rfl) ⟨1308467, by rfl⟩ : syracuseStep 1744623 = 2616935) B2616935
theorem B10616741 : Blo 1744573 10616741 := bstep (se 4 (by rfl) ⟨995319, by rfl⟩ : syracuseStep 10616741 = 1990639) B1990639
theorem B7454663 : Blo 1744573 7454663 := bstep (se 1 (by rfl) ⟨5590997, by rfl⟩ : syracuseStep 7454663 = 11181995) B11181995
theorem B1744879 : Blo 1744573 1744879 := bstep (se 1 (by rfl) ⟨1308659, by rfl⟩ : syracuseStep 1744879 = 2617319) B2617319
theorem B2302175 : Blo 1744573 2302175 := bstep (se 1 (by rfl) ⟨1726631, by rfl⟩ : syracuseStep 2302175 = 3453263) B3453263
theorem B17006831 : Blo 1744573 17006831 := bstep (se 1 (by rfl) ⟨12755123, by rfl⟩ : syracuseStep 17006831 = 25510247) B25510247
theorem B13255163 : Blo 1744573 13255163 := bstep (se 1 (by rfl) ⟨9941372, by rfl⟩ : syracuseStep 13255163 = 19882745) B19882745
theorem B40297139 : Blo 1744573 40297139 := bstep (se 1 (by rfl) ⟨30222854, by rfl⟩ : syracuseStep 40297139 = 60445709) B60445709
theorem B1745691 : Blo 1744573 1745691 := bstep (se 1 (by rfl) ⟨1309268, by rfl⟩ : syracuseStep 1745691 = 2618537) B2618537
theorem B4973375 : Blo 1744573 4973375 := bstep (se 1 (by rfl) ⟨3730031, by rfl⟩ : syracuseStep 4973375 = 7460063) B7460063
theorem B1745735 : Blo 1744573 1745735 := bstep (se 1 (by rfl) ⟨1309301, by rfl⟩ : syracuseStep 1745735 = 2618603) B2618603
theorem B4416383 : Blo 1744573 4416383 := bstep (se 1 (by rfl) ⟨3312287, by rfl⟩ : syracuseStep 4416383 = 6624575) B6624575
theorem B1746159 : Blo 1744573 1746159 := bstep (se 1 (by rfl) ⟨1309619, by rfl⟩ : syracuseStep 1746159 = 2619239) B2619239
theorem B4416839 : Blo 1744573 4416839 := bstep (se 1 (by rfl) ⟨3312629, by rfl⟩ : syracuseStep 4416839 = 6625259) B6625259
theorem B17909063 : Blo 1744573 17909063 := bstep (se 1 (by rfl) ⟨13431797, by rfl⟩ : syracuseStep 17909063 = 26863595) B26863595
theorem B1746247 : Blo 1744573 1746247 := bstep (se 1 (by rfl) ⟨1309685, by rfl⟩ : syracuseStep 1746247 = 2619371) B2619371
theorem B3925331 : Blo 1744573 3925331 := bstep (se 1 (by rfl) ⟨2943998, by rfl⟩ : syracuseStep 3925331 = 5887997) B5887997
theorem B9692507 : Blo 1744573 9692507 := bstep (se 1 (by rfl) ⟨7269380, by rfl⟩ : syracuseStep 9692507 = 14538761) B14538761
theorem B1746335 : Blo 1744573 1746335 := bstep (se 1 (by rfl) ⟨1309751, by rfl⟩ : syracuseStep 1746335 = 2619503) B2619503
theorem B11330999 : Blo 1744573 11330999 := bstep (se 1 (by rfl) ⟨8498249, by rfl⟩ : syracuseStep 11330999 = 16996499) B16996499
theorem B5891561 : Blo 1744573 5891561 := bstep (se 2 (by rfl) ⟨2209335, by rfl⟩ : syracuseStep 5891561 = 4418671) B4418671
theorem B5891615 : Blo 1744573 5891615 := bstep (se 1 (by rfl) ⟨4418711, by rfl⟩ : syracuseStep 5891615 = 8837423) B8837423
theorem B161326687 : Blo 1744573 161326687 := bstep (se 1 (by rfl) ⟨120995015, by rfl⟩ : syracuseStep 161326687 = 241990031) B241990031
theorem B13616893 : Blo 1744573 13616893 := bstep (se 3 (by rfl) ⟨2553167, by rfl⟩ : syracuseStep 13616893 = 5106335) B5106335
theorem B183904283 : Blo 1744573 183904283 := bstep (se 1 (by rfl) ⟨137928212, by rfl⟩ : syracuseStep 183904283 = 275856425) B275856425
theorem B5892479 : Blo 1744573 5892479 := bstep (se 1 (by rfl) ⟨4419359, by rfl⟩ : syracuseStep 5892479 = 8838719) B8838719
theorem B5589767 : Blo 1744573 5589767 := bstep (se 1 (by rfl) ⟨4192325, by rfl⟩ : syracuseStep 5589767 = 8384651) B8384651
theorem B5892911 : Blo 1744573 5892911 := bstep (se 1 (by rfl) ⟨4419683, by rfl⟩ : syracuseStep 5892911 = 8839367) B8839367
theorem B3927131 : Blo 1744573 3927131 := bstep (se 1 (by rfl) ⟨2945348, by rfl⟩ : syracuseStep 3927131 = 5890697) B5890697
theorem B8834183 : Blo 1744573 8834183 := bstep (se 1 (by rfl) ⟨6625637, by rfl⟩ : syracuseStep 8834183 = 13251275) B13251275
theorem B3927275 : Blo 1744573 3927275 := bstep (se 1 (by rfl) ⟨2945456, by rfl⟩ : syracuseStep 3927275 = 5890913) B5890913
theorem B2944633 : Blo 1744573 2944633 := bstep (se 2 (by rfl) ⟨1104237, by rfl⟩ : syracuseStep 2944633 = 2208475) B2208475
theorem B7073513 : Blo 1744573 7073513 := bstep (se 2 (by rfl) ⟨2652567, by rfl⟩ : syracuseStep 7073513 = 5305135) B5305135
theorem B50352191 : Blo 1744573 50352191 := bstep (se 1 (by rfl) ⟨37764143, by rfl⟩ : syracuseStep 50352191 = 75528287) B75528287
theorem B5894207 : Blo 1744573 5894207 := bstep (se 1 (by rfl) ⟨4420655, by rfl⟩ : syracuseStep 5894207 = 8841311) B8841311
theorem B2617511 : Blo 1744573 2617511 := bstep (se 1 (by rfl) ⟨1963133, by rfl⟩ : syracuseStep 2617511 = 3926267) B3926267
theorem B3928283 : Blo 1744573 3928283 := bstep (se 1 (by rfl) ⟨2946212, by rfl⟩ : syracuseStep 3928283 = 5892425) B5892425
theorem B3928391 : Blo 1744573 3928391 := bstep (se 1 (by rfl) ⟨2946293, by rfl⟩ : syracuseStep 3928391 = 5892587) B5892587
theorem B3928481 : Blo 1744573 3928481 := bstep (se 2 (by rfl) ⟨1473180, by rfl⟩ : syracuseStep 3928481 = 2946361) B2946361
theorem B3928553 : Blo 1744573 3928553 := bstep (se 2 (by rfl) ⟨1473207, by rfl⟩ : syracuseStep 3928553 = 2946415) B2946415
theorem B2617883 : Blo 1744573 2617883 := bstep (se 1 (by rfl) ⟨1963412, by rfl⟩ : syracuseStep 2617883 = 3926825) B3926825
theorem B8835641 : Blo 1744573 8835641 := bstep (se 2 (by rfl) ⟨3313365, by rfl⟩ : syracuseStep 8835641 = 6626731) B6626731
theorem B6288029 : Blo 1744573 6288029 := bstep (se 3 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 6288029 = 2358011) B2358011
theorem B8835803 : Blo 1744573 8835803 := bstep (se 1 (by rfl) ⟨6626852, by rfl⟩ : syracuseStep 8835803 = 13253705) B13253705
theorem B1962823 : Blo 1744573 1962823 := bstep (se 1 (by rfl) ⟨1472117, by rfl⟩ : syracuseStep 1962823 = 2944235) B2944235
theorem B8835965 : Blo 1744573 8835965 := bstep (se 3 (by rfl) ⟨1656743, by rfl⟩ : syracuseStep 8835965 = 3313487) B3313487
theorem B2618351 : Blo 1744573 2618351 := bstep (se 1 (by rfl) ⟨1963763, by rfl⟩ : syracuseStep 2618351 = 3927527) B3927527
theorem B16782491 : Blo 1744573 16782491 := bstep (se 1 (by rfl) ⟨12586868, by rfl⟩ : syracuseStep 16782491 = 25173737) B25173737
theorem B4969775 : Blo 1744573 4969775 := bstep (se 1 (by rfl) ⟨3727331, by rfl⟩ : syracuseStep 4969775 = 7454663) B7454663
theorem B120862001 : Blo 1744573 120862001 := bstep (se 2 (by rfl) ⟨45323250, by rfl⟩ : syracuseStep 120862001 = 90646501) B90646501
theorem B1865063 : Blo 1744573 1865063 := bstep (se 1 (by rfl) ⟨1398797, by rfl⟩ : syracuseStep 1865063 = 2797595) B2797595
theorem B2618735 : Blo 1744573 2618735 := bstep (se 1 (by rfl) ⟨1964051, by rfl⟩ : syracuseStep 2618735 = 3928103) B3928103
theorem B6624787 : Blo 1744573 6624787 := bstep (se 1 (by rfl) ⟨4968590, by rfl⟩ : syracuseStep 6624787 = 9937181) B9937181
theorem B42472997 : Blo 1744573 42472997 := bstep (se 4 (by rfl) ⟨3981843, by rfl⟩ : syracuseStep 42472997 = 7963687) B7963687
theorem B9942695 : Blo 1744573 9942695 := bstep (se 1 (by rfl) ⟨7457021, by rfl⟩ : syracuseStep 9942695 = 14914043) B14914043
theorem B3315431 : Blo 1744573 3315431 := bstep (se 1 (by rfl) ⟨2486573, by rfl⟩ : syracuseStep 3315431 = 4973147) B4973147
theorem B2619455 : Blo 1744573 2619455 := bstep (se 1 (by rfl) ⟨1964591, by rfl⟩ : syracuseStep 2619455 = 3929183) B3929183
theorem B2209999 : Blo 1744573 2209999 := bstep (se 1 (by rfl) ⟨1657499, by rfl⟩ : syracuseStep 2209999 = 3314999) B3314999
theorem B7453433 : Blo 1744573 7453433 := bstep (se 2 (by rfl) ⟨2795037, by rfl⟩ : syracuseStep 7453433 = 5590075) B5590075
theorem B25500413 : Blo 1744573 25500413 := bstep (se 3 (by rfl) ⟨4781327, by rfl⟩ : syracuseStep 25500413 = 9562655) B9562655
theorem B322345955 : Blo 1744573 322345955 := bstep (se 1 (by rfl) ⟨241759466, by rfl⟩ : syracuseStep 322345955 = 483518933) B483518933
theorem B4193471 : Blo 1744573 4193471 := bstep (se 1 (by rfl) ⟨3145103, by rfl⟩ : syracuseStep 4193471 = 6290207) B6290207
theorem B8838395 : Blo 1744573 8838395 := bstep (se 1 (by rfl) ⟨6628796, by rfl⟩ : syracuseStep 8838395 = 13257593) B13257593
theorem B19881287 : Blo 1744573 19881287 := bstep (se 1 (by rfl) ⟨14910965, by rfl⟩ : syracuseStep 19881287 = 29821931) B29821931
theorem B18873769 : Blo 1744573 18873769 := bstep (se 2 (by rfl) ⟨7077663, by rfl⟩ : syracuseStep 18873769 = 14155327) B14155327
theorem B11181563 : Blo 1744573 11181563 := bstep (se 1 (by rfl) ⟨8386172, by rfl⟩ : syracuseStep 11181563 = 16772345) B16772345
theorem B1744635 : Blo 1744573 1744635 := bstep (se 1 (by rfl) ⟨1308476, by rfl⟩ : syracuseStep 1744635 = 2616953) B2616953
theorem B7077827 : Blo 1744573 7077827 := bstep (se 1 (by rfl) ⟨5308370, by rfl⟩ : syracuseStep 7077827 = 10616741) B10616741
theorem B1745007 : Blo 1744573 1745007 := bstep (se 1 (by rfl) ⟨1308755, by rfl⟩ : syracuseStep 1745007 = 2617511) B2617511
theorem B11337887 : Blo 1744573 11337887 := bstep (se 1 (by rfl) ⟨8503415, by rfl⟩ : syracuseStep 11337887 = 17006831) B17006831
theorem B1745255 : Blo 1744573 1745255 := bstep (se 1 (by rfl) ⟨1308941, by rfl⟩ : syracuseStep 1745255 = 2617883) B2617883
theorem B5890427 : Blo 1744573 5890427 := bstep (se 1 (by rfl) ⟨4417820, by rfl⟩ : syracuseStep 5890427 = 8835641) B8835641
theorem B5890535 : Blo 1744573 5890535 := bstep (se 1 (by rfl) ⟨4417901, by rfl⟩ : syracuseStep 5890535 = 8835803) B8835803
theorem B5890643 : Blo 1744573 5890643 := bstep (se 1 (by rfl) ⟨4417982, by rfl⟩ : syracuseStep 5890643 = 8835965) B8835965
theorem B1745567 : Blo 1744573 1745567 := bstep (se 1 (by rfl) ⟨1309175, by rfl⟩ : syracuseStep 1745567 = 2618351) B2618351
theorem B322298669 : Blo 1744573 322298669 := bstep (se 3 (by rfl) ⟨60431000, by rfl⟩ : syracuseStep 322298669 = 120862001) B120862001
theorem B25846685 : Blo 1744573 25846685 := bstep (se 3 (by rfl) ⟨4846253, by rfl⟩ : syracuseStep 25846685 = 9692507) B9692507
theorem B1745823 : Blo 1744573 1745823 := bstep (se 1 (by rfl) ⟨1309367, by rfl⟩ : syracuseStep 1745823 = 2618735) B2618735
theorem B4973501 : Blo 1744573 4973501 := bstep (se 3 (by rfl) ⟨932531, by rfl⟩ : syracuseStep 4973501 = 1865063) B1865063
theorem B7553999 : Blo 1744573 7553999 := bstep (se 1 (by rfl) ⟨5665499, by rfl⟩ : syracuseStep 7553999 = 11330999) B11330999
theorem B6628463 : Blo 1744573 6628463 := bstep (se 1 (by rfl) ⟨4971347, by rfl⟩ : syracuseStep 6628463 = 9942695) B9942695
theorem B72623429 : Blo 1744573 72623429 := bstep (se 4 (by rfl) ⟨6808446, by rfl⟩ : syracuseStep 72623429 = 13616893) B13616893
theorem B122602855 : Blo 1744573 122602855 := bstep (se 1 (by rfl) ⟨91952141, by rfl⟩ : syracuseStep 122602855 = 183904283) B183904283
theorem B1746303 : Blo 1744573 1746303 := bstep (se 1 (by rfl) ⟨1309727, by rfl⟩ : syracuseStep 1746303 = 2619455) B2619455
theorem B17000275 : Blo 1744573 17000275 := bstep (se 1 (by rfl) ⟨12750206, by rfl⟩ : syracuseStep 17000275 = 25500413) B25500413
theorem B8841149 : Blo 1744573 8841149 := bstep (se 3 (by rfl) ⟨1657715, by rfl⟩ : syracuseStep 8841149 = 3315431) B3315431
theorem B8833049 : Blo 1744573 8833049 := bstep (se 2 (by rfl) ⟨3312393, by rfl⟩ : syracuseStep 8833049 = 6624787) B6624787
theorem B2795647 : Blo 1744573 2795647 := bstep (se 1 (by rfl) ⟨2096735, by rfl⟩ : syracuseStep 2795647 = 4193471) B4193471
theorem B3926177 : Blo 1744573 3926177 := bstep (se 2 (by rfl) ⟨1472316, by rfl⟩ : syracuseStep 3926177 = 2944633) B2944633
theorem B5892263 : Blo 1744573 5892263 := bstep (se 1 (by rfl) ⟨4419197, by rfl⟩ : syracuseStep 5892263 = 8838395) B8838395
theorem B26864759 : Blo 1744573 26864759 := bstep (se 1 (by rfl) ⟨20148569, by rfl⟩ : syracuseStep 26864759 = 40297139) B40297139
theorem B2944255 : Blo 1744573 2944255 := bstep (se 1 (by rfl) ⟨2208191, by rfl⟩ : syracuseStep 2944255 = 4416383) B4416383
theorem B6139133 : Blo 1744573 6139133 := bstep (se 3 (by rfl) ⟨1151087, by rfl⟩ : syracuseStep 6139133 = 2302175) B2302175
theorem B2944559 : Blo 1744573 2944559 := bstep (se 1 (by rfl) ⟨2208419, by rfl⟩ : syracuseStep 2944559 = 4416839) B4416839
theorem B11939375 : Blo 1744573 11939375 := bstep (se 1 (by rfl) ⟨8954531, by rfl⟩ : syracuseStep 11939375 = 17909063) B17909063
theorem B2616887 : Blo 1744573 2616887 := bstep (se 1 (by rfl) ⟨1962665, by rfl⟩ : syracuseStep 2616887 = 3925331) B3925331
theorem B3927707 : Blo 1744573 3927707 := bstep (se 1 (by rfl) ⟨2945780, by rfl⟩ : syracuseStep 3927707 = 5891561) B5891561
theorem B3927743 : Blo 1744573 3927743 := bstep (se 1 (by rfl) ⟨2945807, by rfl⟩ : syracuseStep 3927743 = 5891615) B5891615
theorem B28315331 : Blo 1744573 28315331 := bstep (se 1 (by rfl) ⟨21236498, by rfl⟩ : syracuseStep 28315331 = 42472997) B42472997
theorem B2617097 : Blo 1744573 2617097 := bstep (se 2 (by rfl) ⟨981411, by rfl⟩ : syracuseStep 2617097 = 1962823) B1962823
theorem B3928319 : Blo 1744573 3928319 := bstep (se 1 (by rfl) ⟨2946239, by rfl⟩ : syracuseStep 3928319 = 5892479) B5892479
theorem B4968955 : Blo 1744573 4968955 := bstep (se 1 (by rfl) ⟨3726716, by rfl⟩ : syracuseStep 4968955 = 7453433) B7453433
theorem B3928607 : Blo 1744573 3928607 := bstep (se 1 (by rfl) ⟨2946455, by rfl⟩ : syracuseStep 3928607 = 5892911) B5892911
theorem B214897303 : Blo 1744573 214897303 := bstep (se 1 (by rfl) ⟨161172977, by rfl⟩ : syracuseStep 214897303 = 322345955) B322345955
theorem B14906045 : Blo 1744573 14906045 := bstep (se 3 (by rfl) ⟨2794883, by rfl⟩ : syracuseStep 14906045 = 5589767) B5589767
theorem B2618087 : Blo 1744573 2618087 := bstep (se 1 (by rfl) ⟨1963565, by rfl⟩ : syracuseStep 2618087 = 3927131) B3927131
theorem B215102249 : Blo 1744573 215102249 := bstep (se 2 (by rfl) ⟨80663343, by rfl⟩ : syracuseStep 215102249 = 161326687) B161326687
theorem B2618183 : Blo 1744573 2618183 := bstep (se 1 (by rfl) ⟨1963637, by rfl⟩ : syracuseStep 2618183 = 3927275) B3927275
theorem B4715675 : Blo 1744573 4715675 := bstep (se 1 (by rfl) ⟨3536756, by rfl⟩ : syracuseStep 4715675 = 7073513) B7073513
theorem B33568127 : Blo 1744573 33568127 := bstep (se 1 (by rfl) ⟨25176095, by rfl⟩ : syracuseStep 33568127 = 50352191) B50352191
theorem B3929471 : Blo 1744573 3929471 := bstep (se 1 (by rfl) ⟨2947103, by rfl⟩ : syracuseStep 3929471 = 5894207) B5894207
theorem B2618855 : Blo 1744573 2618855 := bstep (se 1 (by rfl) ⟨1964141, by rfl⟩ : syracuseStep 2618855 = 3928283) B3928283
theorem B2618927 : Blo 1744573 2618927 := bstep (se 1 (by rfl) ⟨1964195, by rfl⟩ : syracuseStep 2618927 = 3928391) B3928391
theorem B2946665 : Blo 1744573 2946665 := bstep (se 2 (by rfl) ⟨1104999, by rfl⟩ : syracuseStep 2946665 = 2209999) B2209999
theorem B2618987 : Blo 1744573 2618987 := bstep (se 1 (by rfl) ⟨1964240, by rfl⟩ : syracuseStep 2618987 = 3928481) B3928481
theorem B2619035 : Blo 1744573 2619035 := bstep (se 1 (by rfl) ⟨1964276, by rfl⟩ : syracuseStep 2619035 = 3928553) B3928553
theorem B8836775 : Blo 1744573 8836775 := bstep (se 1 (by rfl) ⟨6627581, by rfl⟩ : syracuseStep 8836775 = 13255163) B13255163
theorem B4192019 : Blo 1744573 4192019 := bstep (se 1 (by rfl) ⟨3144014, by rfl⟩ : syracuseStep 4192019 = 6288029) B6288029
theorem B3315583 : Blo 1744573 3315583 := bstep (se 1 (by rfl) ⟨2486687, by rfl⟩ : syracuseStep 3315583 = 4973375) B4973375
theorem B11188327 : Blo 1744573 11188327 := bstep (se 1 (by rfl) ⟨8391245, by rfl⟩ : syracuseStep 11188327 = 16782491) B16782491
theorem B13252733 : Blo 1744573 13252733 := bstep (se 3 (by rfl) ⟨2484887, by rfl⟩ : syracuseStep 13252733 = 4969775) B4969775
theorem B25165025 : Blo 1744573 25165025 := bstep (se 2 (by rfl) ⟨9436884, by rfl⟩ : syracuseStep 25165025 = 18873769) B18873769
theorem B5889455 : Blo 1744573 5889455 := bstep (se 1 (by rfl) ⟨4417091, by rfl⟩ : syracuseStep 5889455 = 8834183) B8834183
theorem B13254191 : Blo 1744573 13254191 := bstep (se 1 (by rfl) ⟨9940643, by rfl⟩ : syracuseStep 13254191 = 19881287) B19881287
theorem B7454375 : Blo 1744573 7454375 := bstep (se 1 (by rfl) ⟨5590781, by rfl⟩ : syracuseStep 7454375 = 11181563) B11181563
theorem B18874205 : Blo 1744573 18874205 := bstep (se 3 (by rfl) ⟨3538913, by rfl⟩ : syracuseStep 18874205 = 7077827) B7077827
theorem B14917769 : Blo 1744573 14917769 := bstep (se 2 (by rfl) ⟨5594163, by rfl⟩ : syracuseStep 14917769 = 11188327) B11188327
theorem B3727529 : Blo 1744573 3727529 := bstep (se 2 (by rfl) ⟨1397823, by rfl⟩ : syracuseStep 3727529 = 2795647) B2795647
theorem B9937363 : Blo 1744573 9937363 := bstep (se 1 (by rfl) ⟨7453022, by rfl⟩ : syracuseStep 9937363 = 14906045) B14906045
theorem B1745391 : Blo 1744573 1745391 := bstep (se 1 (by rfl) ⟨1309043, by rfl⟩ : syracuseStep 1745391 = 2618087) B2618087
theorem B143401499 : Blo 1744573 143401499 := bstep (se 1 (by rfl) ⟨107551124, by rfl⟩ : syracuseStep 143401499 = 215102249) B215102249
theorem B1745455 : Blo 1744573 1745455 := bstep (se 1 (by rfl) ⟨1309091, by rfl⟩ : syracuseStep 1745455 = 2618183) B2618183
theorem B48415619 : Blo 1744573 48415619 := bstep (se 1 (by rfl) ⟨36311714, by rfl⟩ : syracuseStep 48415619 = 72623429) B72623429
theorem B1745903 : Blo 1744573 1745903 := bstep (se 1 (by rfl) ⟨1309427, by rfl⟩ : syracuseStep 1745903 = 2618855) B2618855
theorem B1745951 : Blo 1744573 1745951 := bstep (se 1 (by rfl) ⟨1309463, by rfl⟩ : syracuseStep 1745951 = 2618927) B2618927
theorem B1745991 : Blo 1744573 1745991 := bstep (se 1 (by rfl) ⟨1309493, by rfl⟩ : syracuseStep 1745991 = 2618987) B2618987
theorem B1746023 : Blo 1744573 1746023 := bstep (se 1 (by rfl) ⟨1309517, by rfl⟩ : syracuseStep 1746023 = 2619035) B2619035
theorem B5891183 : Blo 1744573 5891183 := bstep (se 1 (by rfl) ⟨4418387, by rfl⟩ : syracuseStep 5891183 = 8836775) B8836775
theorem B2794679 : Blo 1744573 2794679 := bstep (se 1 (by rfl) ⟨2096009, by rfl⟩ : syracuseStep 2794679 = 4192019) B4192019
theorem B3925673 : Blo 1744573 3925673 := bstep (se 2 (by rfl) ⟨1472127, by rfl⟩ : syracuseStep 3925673 = 2944255) B2944255
theorem B17909839 : Blo 1744573 17909839 := bstep (se 1 (by rfl) ⟨13432379, by rfl⟩ : syracuseStep 17909839 = 26864759) B26864759
theorem B3926303 : Blo 1744573 3926303 := bstep (se 1 (by rfl) ⟨2944727, by rfl⟩ : syracuseStep 3926303 = 5889455) B5889455
theorem B18876887 : Blo 1744573 18876887 := bstep (se 1 (by rfl) ⟨14157665, by rfl⟩ : syracuseStep 18876887 = 28315331) B28315331
theorem B3926951 : Blo 1744573 3926951 := bstep (se 1 (by rfl) ⟨2945213, by rfl⟩ : syracuseStep 3926951 = 5890427) B5890427
theorem B3927023 : Blo 1744573 3927023 := bstep (se 1 (by rfl) ⟨2945267, by rfl⟩ : syracuseStep 3927023 = 5890535) B5890535
theorem B3927095 : Blo 1744573 3927095 := bstep (se 1 (by rfl) ⟨2945321, by rfl⟩ : syracuseStep 3927095 = 5890643) B5890643
theorem B17231123 : Blo 1744573 17231123 := bstep (se 1 (by rfl) ⟨12923342, by rfl⟩ : syracuseStep 17231123 = 25846685) B25846685
theorem B4418975 : Blo 1744573 4418975 := bstep (se 1 (by rfl) ⟨3314231, by rfl⟩ : syracuseStep 4418975 = 6628463) B6628463
theorem B5894099 : Blo 1744573 5894099 := bstep (se 1 (by rfl) ⟨4420574, by rfl⟩ : syracuseStep 5894099 = 8841149) B8841149
theorem B8835155 : Blo 1744573 8835155 := bstep (se 1 (by rfl) ⟨6626366, by rfl⟩ : syracuseStep 8835155 = 13252733) B13252733
theorem B2617451 : Blo 1744573 2617451 := bstep (se 1 (by rfl) ⟨1963088, by rfl⟩ : syracuseStep 2617451 = 3926177) B3926177
theorem B3928175 : Blo 1744573 3928175 := bstep (se 1 (by rfl) ⟨2946131, by rfl⟩ : syracuseStep 3928175 = 5892263) B5892263
theorem B4092755 : Blo 1744573 4092755 := bstep (se 1 (by rfl) ⟨3069566, by rfl⟩ : syracuseStep 4092755 = 6139133) B6139133
theorem B1963039 : Blo 1744573 1963039 := bstep (se 1 (by rfl) ⟨1472279, by rfl⟩ : syracuseStep 1963039 = 2944559) B2944559
theorem B7959583 : Blo 1744573 7959583 := bstep (se 1 (by rfl) ⟨5969687, by rfl⟩ : syracuseStep 7959583 = 11939375) B11939375
theorem B8836127 : Blo 1744573 8836127 := bstep (se 1 (by rfl) ⟨6627095, by rfl⟩ : syracuseStep 8836127 = 13254191) B13254191
theorem B2618471 : Blo 1744573 2618471 := bstep (se 1 (by rfl) ⟨1963853, by rfl⟩ : syracuseStep 2618471 = 3927707) B3927707
theorem B4969583 : Blo 1744573 4969583 := bstep (se 1 (by rfl) ⟨3727187, by rfl⟩ : syracuseStep 4969583 = 7454375) B7454375
theorem B2618495 : Blo 1744573 2618495 := bstep (se 1 (by rfl) ⟨1963871, by rfl⟩ : syracuseStep 2618495 = 3927743) B3927743
theorem B4420777 : Blo 1744573 4420777 := bstep (se 2 (by rfl) ⟨1657791, by rfl⟩ : syracuseStep 4420777 = 3315583) B3315583
theorem B7558591 : Blo 1744573 7558591 := bstep (se 1 (by rfl) ⟨5668943, by rfl⟩ : syracuseStep 7558591 = 11337887) B11337887
theorem B2618879 : Blo 1744573 2618879 := bstep (se 1 (by rfl) ⟨1964159, by rfl⟩ : syracuseStep 2618879 = 3928319) B3928319
theorem B2619071 : Blo 1744573 2619071 := bstep (se 1 (by rfl) ⟨1964303, by rfl⟩ : syracuseStep 2619071 = 3928607) B3928607
theorem B214865779 : Blo 1744573 214865779 := bstep (se 1 (by rfl) ⟨161149334, by rfl⟩ : syracuseStep 214865779 = 322298669) B322298669
theorem B3315667 : Blo 1744573 3315667 := bstep (se 1 (by rfl) ⟨2486750, by rfl⟩ : syracuseStep 3315667 = 4973501) B4973501
theorem B6625273 : Blo 1744573 6625273 := bstep (se 2 (by rfl) ⟨2484477, by rfl⟩ : syracuseStep 6625273 = 4968955) B4968955
theorem B3143783 : Blo 1744573 3143783 := bstep (se 1 (by rfl) ⟨2357837, by rfl⟩ : syracuseStep 3143783 = 4715675) B4715675
theorem B286529737 : Blo 1744573 286529737 := bstep (se 2 (by rfl) ⟨107448651, by rfl⟩ : syracuseStep 286529737 = 214897303) B214897303
theorem B22378751 : Blo 1744573 22378751 := bstep (se 1 (by rfl) ⟨16784063, by rfl⟩ : syracuseStep 22378751 = 33568127) B33568127
theorem B2619647 : Blo 1744573 2619647 := bstep (se 1 (by rfl) ⟨1964735, by rfl⟩ : syracuseStep 2619647 = 3929471) B3929471
theorem B1964443 : Blo 1744573 1964443 := bstep (se 1 (by rfl) ⟨1473332, by rfl⟩ : syracuseStep 1964443 = 2946665) B2946665
theorem B5888699 : Blo 1744573 5888699 := bstep (se 1 (by rfl) ⟨4416524, by rfl⟩ : syracuseStep 5888699 = 8833049) B8833049
theorem B163470473 : Blo 1744573 163470473 := bstep (se 2 (by rfl) ⟨61301427, by rfl⟩ : syracuseStep 163470473 = 122602855) B122602855
theorem B16776683 : Blo 1744573 16776683 := bstep (se 1 (by rfl) ⟨12582512, by rfl⟩ : syracuseStep 16776683 = 25165025) B25165025
theorem B1744591 : Blo 1744573 1744591 := bstep (se 1 (by rfl) ⟨1308443, by rfl⟩ : syracuseStep 1744591 = 2616887) B2616887
theorem B22667033 : Blo 1744573 22667033 := bstep (se 2 (by rfl) ⟨8500137, by rfl⟩ : syracuseStep 22667033 = 17000275) B17000275
theorem B1744731 : Blo 1744573 1744731 := bstep (se 1 (by rfl) ⟨1308548, by rfl⟩ : syracuseStep 1744731 = 2617097) B2617097
theorem B20143997 : Blo 1744573 20143997 := bstep (se 3 (by rfl) ⟨3776999, by rfl⟩ : syracuseStep 20143997 = 7553999) B7553999
theorem B12582803 : Blo 1744573 12582803 := bstep (se 1 (by rfl) ⟨9437102, by rfl⟩ : syracuseStep 12582803 = 18874205) B18874205
theorem B5890103 : Blo 1744573 5890103 := bstep (se 1 (by rfl) ⟨4417577, by rfl⟩ : syracuseStep 5890103 = 8835155) B8835155
theorem B1744967 : Blo 1744573 1744967 := bstep (se 1 (by rfl) ⟨1308725, by rfl⟩ : syracuseStep 1744967 = 2617451) B2617451
theorem B9945179 : Blo 1744573 9945179 := bstep (se 1 (by rfl) ⟨7458884, by rfl⟩ : syracuseStep 9945179 = 14917769) B14917769
theorem B23879785 : Blo 1744573 23879785 := bstep (se 2 (by rfl) ⟨8954919, by rfl⟩ : syracuseStep 23879785 = 17909839) B17909839
theorem B95600999 : Blo 1744573 95600999 := bstep (se 1 (by rfl) ⟨71700749, by rfl⟩ : syracuseStep 95600999 = 143401499) B143401499
theorem B32277079 : Blo 1744573 32277079 := bstep (se 1 (by rfl) ⟨24207809, by rfl⟩ : syracuseStep 32277079 = 48415619) B48415619
theorem B5890751 : Blo 1744573 5890751 := bstep (se 1 (by rfl) ⟨4418063, by rfl⟩ : syracuseStep 5890751 = 8836127) B8836127
theorem B1745647 : Blo 1744573 1745647 := bstep (se 1 (by rfl) ⟨1309235, by rfl⟩ : syracuseStep 1745647 = 2618471) B2618471
theorem B1745663 : Blo 1744573 1745663 := bstep (se 1 (by rfl) ⟨1309247, by rfl⟩ : syracuseStep 1745663 = 2618495) B2618495
theorem B1745919 : Blo 1744573 1745919 := bstep (se 1 (by rfl) ⟨1309439, by rfl⟩ : syracuseStep 1745919 = 2618879) B2618879
theorem B1746047 : Blo 1744573 1746047 := bstep (se 1 (by rfl) ⟨1309535, by rfl⟩ : syracuseStep 1746047 = 2619071) B2619071
theorem B14919167 : Blo 1744573 14919167 := bstep (se 1 (by rfl) ⟨11189375, by rfl⟩ : syracuseStep 14919167 = 22378751) B22378751
theorem B1746431 : Blo 1744573 1746431 := bstep (se 1 (by rfl) ⟨1309823, by rfl⟩ : syracuseStep 1746431 = 2619647) B2619647
theorem B12584591 : Blo 1744573 12584591 := bstep (se 1 (by rfl) ⟨9438443, by rfl⟩ : syracuseStep 12584591 = 18876887) B18876887
theorem B3925799 : Blo 1744573 3925799 := bstep (se 1 (by rfl) ⟨2944349, by rfl⟩ : syracuseStep 3925799 = 5888699) B5888699
theorem B10078121 : Blo 1744573 10078121 := bstep (se 2 (by rfl) ⟨3779295, by rfl⟩ : syracuseStep 10078121 = 7558591) B7558591
theorem B108980315 : Blo 1744573 108980315 := bstep (se 1 (by rfl) ⟨81735236, by rfl⟩ : syracuseStep 108980315 = 163470473) B163470473
theorem B11487415 : Blo 1744573 11487415 := bstep (se 1 (by rfl) ⟨8615561, by rfl⟩ : syracuseStep 11487415 = 17231123) B17231123
theorem B10914013 : Blo 1744573 10914013 := bstep (se 3 (by rfl) ⟨2046377, by rfl⟩ : syracuseStep 10914013 = 4092755) B4092755
theorem B11184455 : Blo 1744573 11184455 := bstep (se 1 (by rfl) ⟨8388341, by rfl⟩ : syracuseStep 11184455 = 16776683) B16776683
theorem B13429331 : Blo 1744573 13429331 := bstep (se 1 (by rfl) ⟨10071998, by rfl⟩ : syracuseStep 13429331 = 20143997) B20143997
theorem B8833697 : Blo 1744573 8833697 := bstep (se 2 (by rfl) ⟨3312636, by rfl⟩ : syracuseStep 8833697 = 6625273) B6625273
theorem B2485019 : Blo 1744573 2485019 := bstep (se 1 (by rfl) ⟨1863764, by rfl⟩ : syracuseStep 2485019 = 3727529) B3727529
theorem B8383421 : Blo 1744573 8383421 := bstep (se 3 (by rfl) ⟨1571891, by rfl⟩ : syracuseStep 8383421 = 3143783) B3143783
theorem B13249817 : Blo 1744573 13249817 := bstep (se 2 (by rfl) ⟨4968681, by rfl⟩ : syracuseStep 13249817 = 9937363) B9937363
theorem B3313055 : Blo 1744573 3313055 := bstep (se 1 (by rfl) ⟨2484791, by rfl⟩ : syracuseStep 3313055 = 4969583) B4969583
theorem B3927455 : Blo 1744573 3927455 := bstep (se 1 (by rfl) ⟨2945591, by rfl⟩ : syracuseStep 3927455 = 5891183) B5891183
theorem B1863119 : Blo 1744573 1863119 := bstep (se 1 (by rfl) ⟨1397339, by rfl⟩ : syracuseStep 1863119 = 2794679) B2794679
theorem B2617115 : Blo 1744573 2617115 := bstep (se 1 (by rfl) ⟨1962836, by rfl⟩ : syracuseStep 2617115 = 3925673) B3925673
theorem B2617385 : Blo 1744573 2617385 := bstep (se 2 (by rfl) ⟨981519, by rfl⟩ : syracuseStep 2617385 = 1963039) B1963039
theorem B10612777 : Blo 1744573 10612777 := bstep (se 2 (by rfl) ⟨3979791, by rfl⟩ : syracuseStep 10612777 = 7959583) B7959583
theorem B2617535 : Blo 1744573 2617535 := bstep (se 1 (by rfl) ⟨1963151, by rfl⟩ : syracuseStep 2617535 = 3926303) B3926303
theorem B5894369 : Blo 1744573 5894369 := bstep (se 2 (by rfl) ⟨2210388, by rfl⟩ : syracuseStep 5894369 = 4420777) B4420777
theorem B2617967 : Blo 1744573 2617967 := bstep (se 1 (by rfl) ⟨1963475, by rfl⟩ : syracuseStep 2617967 = 3926951) B3926951
theorem B2618015 : Blo 1744573 2618015 := bstep (se 1 (by rfl) ⟨1963511, by rfl⟩ : syracuseStep 2618015 = 3927023) B3927023
theorem B2618063 : Blo 1744573 2618063 := bstep (se 1 (by rfl) ⟨1963547, by rfl⟩ : syracuseStep 2618063 = 3927095) B3927095
theorem B2945983 : Blo 1744573 2945983 := bstep (se 1 (by rfl) ⟨2209487, by rfl⟩ : syracuseStep 2945983 = 4418975) B4418975
theorem B286487705 : Blo 1744573 286487705 := bstep (se 2 (by rfl) ⟨107432889, by rfl⟩ : syracuseStep 286487705 = 214865779) B214865779
theorem B15111355 : Blo 1744573 15111355 := bstep (se 1 (by rfl) ⟨11333516, by rfl⟩ : syracuseStep 15111355 = 22667033) B22667033
theorem B4420889 : Blo 1744573 4420889 := bstep (se 2 (by rfl) ⟨1657833, by rfl⟩ : syracuseStep 4420889 = 3315667) B3315667
theorem B3929399 : Blo 1744573 3929399 := bstep (se 1 (by rfl) ⟨2947049, by rfl⟩ : syracuseStep 3929399 = 5894099) B5894099
theorem B2618783 : Blo 1744573 2618783 := bstep (se 1 (by rfl) ⟨1964087, by rfl⟩ : syracuseStep 2618783 = 3928175) B3928175
theorem B382039649 : Blo 1744573 382039649 := bstep (se 2 (by rfl) ⟨143264868, by rfl⟩ : syracuseStep 382039649 = 286529737) B286529737
theorem B2619257 : Blo 1744573 2619257 := bstep (se 2 (by rfl) ⟨982221, by rfl⟩ : syracuseStep 2619257 = 1964443) B1964443
theorem B8388535 : Blo 1744573 8388535 := bstep (se 1 (by rfl) ⟨6291401, by rfl⟩ : syracuseStep 8388535 = 12582803) B12582803
theorem B1744923 : Blo 1744573 1744923 := bstep (se 1 (by rfl) ⟨1308692, by rfl⟩ : syracuseStep 1744923 = 2617385) B2617385
theorem B1745023 : Blo 1744573 1745023 := bstep (se 1 (by rfl) ⟨1308767, by rfl⟩ : syracuseStep 1745023 = 2617535) B2617535
theorem B63733999 : Blo 1744573 63733999 := bstep (se 1 (by rfl) ⟨47800499, by rfl⟩ : syracuseStep 63733999 = 95600999) B95600999
theorem B1745311 : Blo 1744573 1745311 := bstep (se 1 (by rfl) ⟨1308983, by rfl⟩ : syracuseStep 1745311 = 2617967) B2617967
theorem B1745343 : Blo 1744573 1745343 := bstep (se 1 (by rfl) ⟨1309007, by rfl⟩ : syracuseStep 1745343 = 2618015) B2618015
theorem B1745375 : Blo 1744573 1745375 := bstep (se 1 (by rfl) ⟨1309031, by rfl⟩ : syracuseStep 1745375 = 2618063) B2618063
theorem B1745855 : Blo 1744573 1745855 := bstep (se 1 (by rfl) ⟨1309391, by rfl⟩ : syracuseStep 1745855 = 2618783) B2618783
theorem B9946111 : Blo 1744573 9946111 := bstep (se 1 (by rfl) ⟨7459583, by rfl⟩ : syracuseStep 9946111 = 14919167) B14919167
theorem B8389727 : Blo 1744573 8389727 := bstep (se 1 (by rfl) ⟨6292295, by rfl⟩ : syracuseStep 8389727 = 12584591) B12584591
theorem B1746171 : Blo 1744573 1746171 := bstep (se 1 (by rfl) ⟨1309628, by rfl⟩ : syracuseStep 1746171 = 2619257) B2619257
theorem B6718747 : Blo 1744573 6718747 := bstep (se 1 (by rfl) ⟨5039060, by rfl⟩ : syracuseStep 6718747 = 10078121) B10078121
theorem B7456303 : Blo 1744573 7456303 := bstep (se 1 (by rfl) ⟨5592227, by rfl⟩ : syracuseStep 7456303 = 11184455) B11184455
theorem B5588947 : Blo 1744573 5588947 := bstep (se 1 (by rfl) ⟨4191710, by rfl⟩ : syracuseStep 5588947 = 8383421) B8383421
theorem B8833211 : Blo 1744573 8833211 := bstep (se 1 (by rfl) ⟨6624908, by rfl⟩ : syracuseStep 8833211 = 13249817) B13249817
theorem B11184713 : Blo 1744573 11184713 := bstep (se 2 (by rfl) ⟨4194267, by rfl⟩ : syracuseStep 11184713 = 8388535) B8388535
theorem B3926735 : Blo 1744573 3926735 := bstep (se 1 (by rfl) ⟨2945051, by rfl⟩ : syracuseStep 3926735 = 5890103) B5890103
theorem B14150369 : Blo 1744573 14150369 := bstep (se 2 (by rfl) ⟨5306388, by rfl⟩ : syracuseStep 14150369 = 10612777) B10612777
theorem B6630119 : Blo 1744573 6630119 := bstep (se 1 (by rfl) ⟨4972589, by rfl⟩ : syracuseStep 6630119 = 9945179) B9945179
theorem B14552017 : Blo 1744573 14552017 := bstep (se 2 (by rfl) ⟨5457006, by rfl⟩ : syracuseStep 14552017 = 10914013) B10914013
theorem B3927167 : Blo 1744573 3927167 := bstep (se 1 (by rfl) ⟨2945375, by rfl⟩ : syracuseStep 3927167 = 5890751) B5890751
theorem B190991803 : Blo 1744573 190991803 := bstep (se 1 (by rfl) ⟨143243852, by rfl⟩ : syracuseStep 190991803 = 286487705) B286487705
theorem B43036105 : Blo 1744573 43036105 := bstep (se 2 (by rfl) ⟨16138539, by rfl⟩ : syracuseStep 43036105 = 32277079) B32277079
theorem B254693099 : Blo 1744573 254693099 := bstep (se 1 (by rfl) ⟨191019824, by rfl⟩ : syracuseStep 254693099 = 382039649) B382039649
theorem B2617199 : Blo 1744573 2617199 := bstep (se 1 (by rfl) ⟨1962899, by rfl⟩ : syracuseStep 2617199 = 3925799) B3925799
theorem B4968317 : Blo 1744573 4968317 := bstep (se 3 (by rfl) ⟨931559, by rfl⟩ : syracuseStep 4968317 = 1863119) B1863119
theorem B3927977 : Blo 1744573 3927977 := bstep (se 2 (by rfl) ⟨1472991, by rfl⟩ : syracuseStep 3927977 = 2945983) B2945983
theorem B20148473 : Blo 1744573 20148473 := bstep (se 2 (by rfl) ⟨7555677, by rfl⟩ : syracuseStep 20148473 = 15111355) B15111355
theorem B2208703 : Blo 1744573 2208703 := bstep (se 1 (by rfl) ⟨1656527, by rfl⟩ : syracuseStep 2208703 = 3313055) B3313055
theorem B2618303 : Blo 1744573 2618303 := bstep (se 1 (by rfl) ⟨1963727, by rfl⟩ : syracuseStep 2618303 = 3927455) B3927455
theorem B31839713 : Blo 1744573 31839713 := bstep (se 2 (by rfl) ⟨11939892, by rfl⟩ : syracuseStep 31839713 = 23879785) B23879785
theorem B3929579 : Blo 1744573 3929579 := bstep (se 1 (by rfl) ⟨2947184, by rfl⟩ : syracuseStep 3929579 = 5894369) B5894369
theorem B15316553 : Blo 1744573 15316553 := bstep (se 2 (by rfl) ⟨5743707, by rfl⟩ : syracuseStep 15316553 = 11487415) B11487415
theorem B2947259 : Blo 1744573 2947259 := bstep (se 1 (by rfl) ⟨2210444, by rfl⟩ : syracuseStep 2947259 = 4420889) B4420889
theorem B2619599 : Blo 1744573 2619599 := bstep (se 1 (by rfl) ⟨1964699, by rfl⟩ : syracuseStep 2619599 = 3929399) B3929399
theorem B72653543 : Blo 1744573 72653543 := bstep (se 1 (by rfl) ⟨54490157, by rfl⟩ : syracuseStep 72653543 = 108980315) B108980315
theorem B8952887 : Blo 1744573 8952887 := bstep (se 1 (by rfl) ⟨6714665, by rfl⟩ : syracuseStep 8952887 = 13429331) B13429331
theorem B5889131 : Blo 1744573 5889131 := bstep (se 1 (by rfl) ⟨4416848, by rfl⟩ : syracuseStep 5889131 = 8833697) B8833697
theorem B6626717 : Blo 1744573 6626717 := bstep (se 3 (by rfl) ⟨1242509, by rfl⟩ : syracuseStep 6626717 = 2485019) B2485019
theorem B1744743 : Blo 1744573 1744743 := bstep (se 1 (by rfl) ⟨1308557, by rfl⟩ : syracuseStep 1744743 = 2617115) B2617115
theorem B1745535 : Blo 1744573 1745535 := bstep (se 1 (by rfl) ⟨1309151, by rfl⟩ : syracuseStep 1745535 = 2618303) B2618303
theorem B21226475 : Blo 1744573 21226475 := bstep (se 1 (by rfl) ⟨15919856, by rfl⟩ : syracuseStep 21226475 = 31839713) B31839713
theorem B1746399 : Blo 1744573 1746399 := bstep (se 1 (by rfl) ⟨1309799, by rfl⟩ : syracuseStep 1746399 = 2619599) B2619599
theorem B7456475 : Blo 1744573 7456475 := bstep (se 1 (by rfl) ⟨5592356, by rfl⟩ : syracuseStep 7456475 = 11184713) B11184713
theorem B3926087 : Blo 1744573 3926087 := bstep (se 1 (by rfl) ⟨2944565, by rfl⟩ : syracuseStep 3926087 = 5889131) B5889131
theorem B4417811 : Blo 1744573 4417811 := bstep (se 1 (by rfl) ⟨3313358, by rfl⟩ : syracuseStep 4417811 = 6626717) B6626717
theorem B13248845 : Blo 1744573 13248845 := bstep (se 3 (by rfl) ⟨2484158, by rfl⟩ : syracuseStep 13248845 = 4968317) B4968317
theorem B23874365 : Blo 1744573 23874365 := bstep (se 3 (by rfl) ⟨4476443, by rfl⟩ : syracuseStep 23874365 = 8952887) B8952887
theorem B84978665 : Blo 1744573 84978665 := bstep (se 2 (by rfl) ⟨31866999, by rfl⟩ : syracuseStep 84978665 = 63733999) B63733999
theorem B10211035 : Blo 1744573 10211035 := bstep (se 1 (by rfl) ⟨7658276, by rfl⟩ : syracuseStep 10211035 = 15316553) B15316553
theorem B2944937 : Blo 1744573 2944937 := bstep (se 2 (by rfl) ⟨1104351, by rfl⟩ : syracuseStep 2944937 = 2208703) B2208703
theorem B8958329 : Blo 1744573 8958329 := bstep (se 2 (by rfl) ⟨3359373, by rfl⟩ : syracuseStep 8958329 = 6718747) B6718747
theorem B2617823 : Blo 1744573 2617823 := bstep (se 1 (by rfl) ⟨1963367, by rfl⟩ : syracuseStep 2617823 = 3926735) B3926735
theorem B9433579 : Blo 1744573 9433579 := bstep (se 1 (by rfl) ⟨7075184, by rfl⟩ : syracuseStep 9433579 = 14150369) B14150369
theorem B48435695 : Blo 1744573 48435695 := bstep (se 1 (by rfl) ⟨36326771, by rfl⟩ : syracuseStep 48435695 = 72653543) B72653543
theorem B4420079 : Blo 1744573 4420079 := bstep (se 1 (by rfl) ⟨3315059, by rfl⟩ : syracuseStep 4420079 = 6630119) B6630119
theorem B57381473 : Blo 1744573 57381473 := bstep (se 2 (by rfl) ⟨21518052, by rfl⟩ : syracuseStep 57381473 = 43036105) B43036105
theorem B9941737 : Blo 1744573 9941737 := bstep (se 2 (by rfl) ⟨3728151, by rfl⟩ : syracuseStep 9941737 = 7456303) B7456303
theorem B2618111 : Blo 1744573 2618111 := bstep (se 1 (by rfl) ⟨1963583, by rfl⟩ : syracuseStep 2618111 = 3927167) B3927167
theorem B7451929 : Blo 1744573 7451929 := bstep (se 2 (by rfl) ⟨2794473, by rfl⟩ : syracuseStep 7451929 = 5588947) B5588947
theorem B2618651 : Blo 1744573 2618651 := bstep (se 1 (by rfl) ⟨1963988, by rfl⟩ : syracuseStep 2618651 = 3927977) B3927977
theorem B13432315 : Blo 1744573 13432315 := bstep (se 1 (by rfl) ⟨10074236, by rfl⟩ : syracuseStep 13432315 = 20148473) B20148473
theorem B5593151 : Blo 1744573 5593151 := bstep (se 1 (by rfl) ⟨4194863, by rfl⟩ : syracuseStep 5593151 = 8389727) B8389727
theorem B2619719 : Blo 1744573 2619719 := bstep (se 1 (by rfl) ⟨1964789, by rfl⟩ : syracuseStep 2619719 = 3929579) B3929579
theorem B13261481 : Blo 1744573 13261481 := bstep (se 2 (by rfl) ⟨4973055, by rfl⟩ : syracuseStep 13261481 = 9946111) B9946111
theorem B5888807 : Blo 1744573 5888807 := bstep (se 1 (by rfl) ⟨4416605, by rfl⟩ : syracuseStep 5888807 = 8833211) B8833211
theorem B1964839 : Blo 1744573 1964839 := bstep (se 1 (by rfl) ⟨1473629, by rfl⟩ : syracuseStep 1964839 = 2947259) B2947259
theorem B254655737 : Blo 1744573 254655737 := bstep (se 2 (by rfl) ⟨95495901, by rfl⟩ : syracuseStep 254655737 = 190991803) B190991803
theorem B77610757 : Blo 1744573 77610757 := bstep (se 4 (by rfl) ⟨7276008, by rfl⟩ : syracuseStep 77610757 = 14552017) B14552017
theorem B169795399 : Blo 1744573 169795399 := bstep (se 1 (by rfl) ⟨127346549, by rfl⟩ : syracuseStep 169795399 = 254693099) B254693099
theorem B1744799 : Blo 1744573 1744799 := bstep (se 1 (by rfl) ⟨1308599, by rfl⟩ : syracuseStep 1744799 = 2617199) B2617199
theorem B5972219 : Blo 1744573 5972219 := bstep (se 1 (by rfl) ⟨4479164, by rfl⟩ : syracuseStep 5972219 = 8958329) B8958329
theorem B1745215 : Blo 1744573 1745215 := bstep (se 1 (by rfl) ⟨1308911, by rfl⟩ : syracuseStep 1745215 = 2617823) B2617823
theorem B1745407 : Blo 1744573 1745407 := bstep (se 1 (by rfl) ⟨1309055, by rfl⟩ : syracuseStep 1745407 = 2618111) B2618111
theorem B1745767 : Blo 1744573 1745767 := bstep (se 1 (by rfl) ⟨1309325, by rfl⟩ : syracuseStep 1745767 = 2618651) B2618651
theorem B13255649 : Blo 1744573 13255649 := bstep (se 2 (by rfl) ⟨4970868, by rfl⟩ : syracuseStep 13255649 = 9941737) B9941737
theorem B3728767 : Blo 1744573 3728767 := bstep (se 1 (by rfl) ⟨2796575, by rfl⟩ : syracuseStep 3728767 = 5593151) B5593151
theorem B1746479 : Blo 1744573 1746479 := bstep (se 1 (by rfl) ⟨1309859, by rfl⟩ : syracuseStep 1746479 = 2619719) B2619719
theorem B8832563 : Blo 1744573 8832563 := bstep (se 1 (by rfl) ⟨6624422, by rfl⟩ : syracuseStep 8832563 = 13248845) B13248845
theorem B8840987 : Blo 1744573 8840987 := bstep (se 1 (by rfl) ⟨6630740, by rfl⟩ : syracuseStep 8840987 = 13261481) B13261481
theorem B3925871 : Blo 1744573 3925871 := bstep (se 1 (by rfl) ⟨2944403, by rfl⟩ : syracuseStep 3925871 = 5888807) B5888807
theorem B17909753 : Blo 1744573 17909753 := bstep (se 2 (by rfl) ⟨6716157, by rfl⟩ : syracuseStep 17909753 = 13432315) B13432315
theorem B12578105 : Blo 1744573 12578105 := bstep (se 2 (by rfl) ⟨4716789, by rfl⟩ : syracuseStep 12578105 = 9433579) B9433579
theorem B2617391 : Blo 1744573 2617391 := bstep (se 1 (by rfl) ⟨1963043, by rfl⟩ : syracuseStep 2617391 = 3926087) B3926087
theorem B2945207 : Blo 1744573 2945207 := bstep (se 1 (by rfl) ⟨2208905, by rfl⟩ : syracuseStep 2945207 = 4417811) B4417811
theorem B56652443 : Blo 1744573 56652443 := bstep (se 1 (by rfl) ⟨42489332, by rfl⟩ : syracuseStep 56652443 = 84978665) B84978665
theorem B63664973 : Blo 1744573 63664973 := bstep (se 3 (by rfl) ⟨11937182, by rfl⟩ : syracuseStep 63664973 = 23874365) B23874365
theorem B1963291 : Blo 1744573 1963291 := bstep (se 1 (by rfl) ⟨1472468, by rfl⟩ : syracuseStep 1963291 = 2944937) B2944937
theorem B56603933 : Blo 1744573 56603933 := bstep (se 3 (by rfl) ⟨10613237, by rfl⟩ : syracuseStep 56603933 = 21226475) B21226475
theorem B32290463 : Blo 1744573 32290463 := bstep (se 1 (by rfl) ⟨24217847, by rfl⟩ : syracuseStep 32290463 = 48435695) B48435695
theorem B2946719 : Blo 1744573 2946719 := bstep (se 1 (by rfl) ⟨2210039, by rfl⟩ : syracuseStep 2946719 = 4420079) B4420079
theorem B2619785 : Blo 1744573 2619785 := bstep (se 2 (by rfl) ⟨982419, by rfl⟩ : syracuseStep 2619785 = 1964839) B1964839
theorem B4970983 : Blo 1744573 4970983 := bstep (se 1 (by rfl) ⟨3728237, by rfl⟩ : syracuseStep 4970983 = 7456475) B7456475
theorem B153017261 : Blo 1744573 153017261 := bstep (se 3 (by rfl) ⟨28690736, by rfl⟩ : syracuseStep 153017261 = 57381473) B57381473
theorem B9935905 : Blo 1744573 9935905 := bstep (se 2 (by rfl) ⟨3725964, by rfl⟩ : syracuseStep 9935905 = 7451929) B7451929
theorem B169770491 : Blo 1744573 169770491 := bstep (se 1 (by rfl) ⟨127327868, by rfl⟩ : syracuseStep 169770491 = 254655737) B254655737
theorem B13614713 : Blo 1744573 13614713 := bstep (se 2 (by rfl) ⟨5105517, by rfl⟩ : syracuseStep 13614713 = 10211035) B10211035
theorem B103481009 : Blo 1744573 103481009 := bstep (se 2 (by rfl) ⟨38805378, by rfl⟩ : syracuseStep 103481009 = 77610757) B77610757
theorem B226393865 : Blo 1744573 226393865 := bstep (se 2 (by rfl) ⟨84897699, by rfl⟩ : syracuseStep 226393865 = 169795399) B169795399
theorem B1744927 : Blo 1744573 1744927 := bstep (se 1 (by rfl) ⟨1308695, by rfl⟩ : syracuseStep 1744927 = 2617391) B2617391
theorem B3981479 : Blo 1744573 3981479 := bstep (se 1 (by rfl) ⟨2986109, by rfl⟩ : syracuseStep 3981479 = 5972219) B5972219
theorem B42443315 : Blo 1744573 42443315 := bstep (se 1 (by rfl) ⟨31832486, by rfl⟩ : syracuseStep 42443315 = 63664973) B63664973
theorem B6627977 : Blo 1744573 6627977 := bstep (se 2 (by rfl) ⟨2485491, by rfl⟩ : syracuseStep 6627977 = 4970983) B4970983
theorem B13247873 : Blo 1744573 13247873 := bstep (se 2 (by rfl) ⟨4967952, by rfl⟩ : syracuseStep 13247873 = 9935905) B9935905
theorem B1746523 : Blo 1744573 1746523 := bstep (se 1 (by rfl) ⟨1309892, by rfl⟩ : syracuseStep 1746523 = 2619785) B2619785
theorem B68987339 : Blo 1744573 68987339 := bstep (se 1 (by rfl) ⟨51740504, by rfl⟩ : syracuseStep 68987339 = 103481009) B103481009
theorem B37768295 : Blo 1744573 37768295 := bstep (se 1 (by rfl) ⟨28326221, by rfl⟩ : syracuseStep 37768295 = 56652443) B56652443
theorem B37735955 : Blo 1744573 37735955 := bstep (se 1 (by rfl) ⟨28301966, by rfl⟩ : syracuseStep 37735955 = 56603933) B56603933
theorem B5893991 : Blo 1744573 5893991 := bstep (se 1 (by rfl) ⟨4420493, by rfl⟩ : syracuseStep 5893991 = 8840987) B8840987
theorem B2617247 : Blo 1744573 2617247 := bstep (se 1 (by rfl) ⟨1962935, by rfl⟩ : syracuseStep 2617247 = 3925871) B3925871
theorem B2617721 : Blo 1744573 2617721 := bstep (se 2 (by rfl) ⟨981645, by rfl⟩ : syracuseStep 2617721 = 1963291) B1963291
theorem B102011507 : Blo 1744573 102011507 := bstep (se 1 (by rfl) ⟨76508630, by rfl⟩ : syracuseStep 102011507 = 153017261) B153017261
theorem B8385403 : Blo 1744573 8385403 := bstep (se 1 (by rfl) ⟨6289052, by rfl⟩ : syracuseStep 8385403 = 12578105) B12578105
theorem B1963471 : Blo 1744573 1963471 := bstep (se 1 (by rfl) ⟨1472603, by rfl⟩ : syracuseStep 1963471 = 2945207) B2945207
theorem B8837099 : Blo 1744573 8837099 := bstep (se 1 (by rfl) ⟨6627824, by rfl⟩ : syracuseStep 8837099 = 13255649) B13255649
theorem B5888375 : Blo 1744573 5888375 := bstep (se 1 (by rfl) ⟨4416281, by rfl⟩ : syracuseStep 5888375 = 8832563) B8832563
theorem B21526975 : Blo 1744573 21526975 := bstep (se 1 (by rfl) ⟨16145231, by rfl⟩ : syracuseStep 21526975 = 32290463) B32290463
theorem B1964479 : Blo 1744573 1964479 := bstep (se 1 (by rfl) ⟨1473359, by rfl⟩ : syracuseStep 1964479 = 2946719) B2946719
theorem B4971689 : Blo 1744573 4971689 := bstep (se 2 (by rfl) ⟨1864383, by rfl⟩ : syracuseStep 4971689 = 3728767) B3728767
theorem B113180327 : Blo 1744573 113180327 := bstep (se 1 (by rfl) ⟨84885245, by rfl⟩ : syracuseStep 113180327 = 169770491) B169770491
theorem B9076475 : Blo 1744573 9076475 := bstep (se 1 (by rfl) ⟨6807356, by rfl⟩ : syracuseStep 9076475 = 13614713) B13614713
theorem B150929243 : Blo 1744573 150929243 := bstep (se 1 (by rfl) ⟨113196932, by rfl⟩ : syracuseStep 150929243 = 226393865) B226393865
theorem B47759341 : Blo 1744573 47759341 := bstep (se 3 (by rfl) ⟨8954876, by rfl⟩ : syracuseStep 47759341 = 17909753) B17909753
theorem B1745147 : Blo 1744573 1745147 := bstep (se 1 (by rfl) ⟨1308860, by rfl⟩ : syracuseStep 1745147 = 2617721) B2617721
theorem B28295543 : Blo 1744573 28295543 := bstep (se 1 (by rfl) ⟨21221657, by rfl⟩ : syracuseStep 28295543 = 42443315) B42443315
theorem B10617277 : Blo 1744573 10617277 := bstep (se 3 (by rfl) ⟨1990739, by rfl⟩ : syracuseStep 10617277 = 3981479) B3981479
theorem B8831915 : Blo 1744573 8831915 := bstep (se 1 (by rfl) ⟨6623936, by rfl⟩ : syracuseStep 8831915 = 13247873) B13247873
theorem B5891399 : Blo 1744573 5891399 := bstep (se 1 (by rfl) ⟨4418549, by rfl⟩ : syracuseStep 5891399 = 8837099) B8837099
theorem B3925583 : Blo 1744573 3925583 := bstep (se 1 (by rfl) ⟨2944187, by rfl⟩ : syracuseStep 3925583 = 5888375) B5888375
theorem B45991559 : Blo 1744573 45991559 := bstep (se 1 (by rfl) ⟨34493669, by rfl⟩ : syracuseStep 45991559 = 68987339) B68987339
theorem B63679121 : Blo 1744573 63679121 := bstep (se 2 (by rfl) ⟨23879670, by rfl⟩ : syracuseStep 63679121 = 47759341) B47759341
theorem B4418651 : Blo 1744573 4418651 := bstep (se 1 (by rfl) ⟨3313988, by rfl⟩ : syracuseStep 4418651 = 6627977) B6627977
theorem B2617961 : Blo 1744573 2617961 := bstep (se 2 (by rfl) ⟨981735, by rfl⟩ : syracuseStep 2617961 = 1963471) B1963471
theorem B25178863 : Blo 1744573 25178863 := bstep (se 1 (by rfl) ⟨18884147, by rfl⟩ : syracuseStep 25178863 = 37768295) B37768295
theorem B3314459 : Blo 1744573 3314459 := bstep (se 1 (by rfl) ⟨2485844, by rfl⟩ : syracuseStep 3314459 = 4971689) B4971689
theorem B75453551 : Blo 1744573 75453551 := bstep (se 1 (by rfl) ⟨56590163, by rfl⟩ : syracuseStep 75453551 = 113180327) B113180327
theorem B6050983 : Blo 1744573 6050983 := bstep (se 1 (by rfl) ⟨4538237, by rfl⟩ : syracuseStep 6050983 = 9076475) B9076475
theorem B100619495 : Blo 1744573 100619495 := bstep (se 1 (by rfl) ⟨75464621, by rfl⟩ : syracuseStep 100619495 = 150929243) B150929243
theorem B3929327 : Blo 1744573 3929327 := bstep (se 1 (by rfl) ⟨2946995, by rfl⟩ : syracuseStep 3929327 = 5893991) B5893991
theorem B68007671 : Blo 1744573 68007671 := bstep (se 1 (by rfl) ⟨51005753, by rfl⟩ : syracuseStep 68007671 = 102011507) B102011507
theorem B28702633 : Blo 1744573 28702633 := bstep (se 2 (by rfl) ⟨10763487, by rfl⟩ : syracuseStep 28702633 = 21526975) B21526975
theorem B2619305 : Blo 1744573 2619305 := bstep (se 2 (by rfl) ⟨982239, by rfl⟩ : syracuseStep 2619305 = 1964479) B1964479
theorem B11180537 : Blo 1744573 11180537 := bstep (se 2 (by rfl) ⟨4192701, by rfl⟩ : syracuseStep 11180537 = 8385403) B8385403
theorem B25157303 : Blo 1744573 25157303 := bstep (se 1 (by rfl) ⟨18867977, by rfl⟩ : syracuseStep 25157303 = 37735955) B37735955
theorem B1744831 : Blo 1744573 1744831 := bstep (se 1 (by rfl) ⟨1308623, by rfl⟩ : syracuseStep 1744831 = 2617247) B2617247
theorem B1745307 : Blo 1744573 1745307 := bstep (se 1 (by rfl) ⟨1308980, by rfl⟩ : syracuseStep 1745307 = 2617961) B2617961
theorem B14156369 : Blo 1744573 14156369 := bstep (se 2 (by rfl) ⟨5308638, by rfl⟩ : syracuseStep 14156369 = 10617277) B10617277
theorem B33571817 : Blo 1744573 33571817 := bstep (se 2 (by rfl) ⟨12589431, by rfl⟩ : syracuseStep 33571817 = 25178863) B25178863
theorem B1746203 : Blo 1744573 1746203 := bstep (se 1 (by rfl) ⟨1309652, by rfl⟩ : syracuseStep 1746203 = 2619305) B2619305
theorem B42452747 : Blo 1744573 42452747 := bstep (se 1 (by rfl) ⟨31839560, by rfl⟩ : syracuseStep 42452747 = 63679121) B63679121
theorem B16771535 : Blo 1744573 16771535 := bstep (se 1 (by rfl) ⟨12578651, by rfl⟩ : syracuseStep 16771535 = 25157303) B25157303
theorem B50302367 : Blo 1744573 50302367 := bstep (se 1 (by rfl) ⟨37726775, by rfl⟩ : syracuseStep 50302367 = 75453551) B75453551
theorem B67079663 : Blo 1744573 67079663 := bstep (se 1 (by rfl) ⟨50309747, by rfl⟩ : syracuseStep 67079663 = 100619495) B100619495
theorem B3927599 : Blo 1744573 3927599 := bstep (se 1 (by rfl) ⟨2945699, by rfl⟩ : syracuseStep 3927599 = 5891399) B5891399
theorem B2617055 : Blo 1744573 2617055 := bstep (se 1 (by rfl) ⟨1962791, by rfl⟩ : syracuseStep 2617055 = 3925583) B3925583
theorem B45338447 : Blo 1744573 45338447 := bstep (se 1 (by rfl) ⟨34003835, by rfl⟩ : syracuseStep 45338447 = 68007671) B68007671
theorem B2945767 : Blo 1744573 2945767 := bstep (se 1 (by rfl) ⟨2209325, by rfl⟩ : syracuseStep 2945767 = 4418651) B4418651
theorem B38270177 : Blo 1744573 38270177 := bstep (se 2 (by rfl) ⟨14351316, by rfl⟩ : syracuseStep 38270177 = 28702633) B28702633
theorem B18863695 : Blo 1744573 18863695 := bstep (se 1 (by rfl) ⟨14147771, by rfl⟩ : syracuseStep 18863695 = 28295543) B28295543
theorem B5887943 : Blo 1744573 5887943 := bstep (se 1 (by rfl) ⟨4415957, by rfl⟩ : syracuseStep 5887943 = 8831915) B8831915
theorem B2619551 : Blo 1744573 2619551 := bstep (se 1 (by rfl) ⟨1964663, by rfl⟩ : syracuseStep 2619551 = 3929327) B3929327
theorem B30661039 : Blo 1744573 30661039 := bstep (se 1 (by rfl) ⟨22995779, by rfl⟩ : syracuseStep 30661039 = 45991559) B45991559
theorem B8067977 : Blo 1744573 8067977 := bstep (se 2 (by rfl) ⟨3025491, by rfl⟩ : syracuseStep 8067977 = 6050983) B6050983
theorem B7453691 : Blo 1744573 7453691 := bstep (se 1 (by rfl) ⟨5590268, by rfl⟩ : syracuseStep 7453691 = 11180537) B11180537
theorem B8838557 : Blo 1744573 8838557 := bstep (se 3 (by rfl) ⟨1657229, by rfl⟩ : syracuseStep 8838557 = 3314459) B3314459
theorem B9437579 : Blo 1744573 9437579 := bstep (se 1 (by rfl) ⟨7078184, by rfl⟩ : syracuseStep 9437579 = 14156369) B14156369
theorem B22381211 : Blo 1744573 22381211 := bstep (se 1 (by rfl) ⟨16785908, by rfl⟩ : syracuseStep 22381211 = 33571817) B33571817
theorem B3925295 : Blo 1744573 3925295 := bstep (se 1 (by rfl) ⟨2943971, by rfl⟩ : syracuseStep 3925295 = 5887943) B5887943
theorem B1746367 : Blo 1744573 1746367 := bstep (se 1 (by rfl) ⟨1309775, by rfl⟩ : syracuseStep 1746367 = 2619551) B2619551
theorem B25151593 : Blo 1744573 25151593 := bstep (se 2 (by rfl) ⟨9431847, by rfl⟩ : syracuseStep 25151593 = 18863695) B18863695
theorem B5892371 : Blo 1744573 5892371 := bstep (se 1 (by rfl) ⟨4419278, by rfl⟩ : syracuseStep 5892371 = 8838557) B8838557
theorem B40881385 : Blo 1744573 40881385 := bstep (se 2 (by rfl) ⟨15330519, by rfl⟩ : syracuseStep 40881385 = 30661039) B30661039
theorem B25513451 : Blo 1744573 25513451 := bstep (se 1 (by rfl) ⟨19135088, by rfl⟩ : syracuseStep 25513451 = 38270177) B38270177
theorem B3927689 : Blo 1744573 3927689 := bstep (se 2 (by rfl) ⟨1472883, by rfl⟩ : syracuseStep 3927689 = 2945767) B2945767
theorem B5378651 : Blo 1744573 5378651 := bstep (se 1 (by rfl) ⟨4033988, by rfl⟩ : syracuseStep 5378651 = 8067977) B8067977
theorem B4969127 : Blo 1744573 4969127 := bstep (se 1 (by rfl) ⟨3726845, by rfl⟩ : syracuseStep 4969127 = 7453691) B7453691
theorem B33534911 : Blo 1744573 33534911 := bstep (se 1 (by rfl) ⟨25151183, by rfl⟩ : syracuseStep 33534911 = 50302367) B50302367
theorem B2618399 : Blo 1744573 2618399 := bstep (se 1 (by rfl) ⟨1963799, by rfl⟩ : syracuseStep 2618399 = 3927599) B3927599
theorem B30225631 : Blo 1744573 30225631 := bstep (se 1 (by rfl) ⟨22669223, by rfl⟩ : syracuseStep 30225631 = 45338447) B45338447
theorem B28301831 : Blo 1744573 28301831 := bstep (se 1 (by rfl) ⟨21226373, by rfl⟩ : syracuseStep 28301831 = 42452747) B42452747
theorem B11181023 : Blo 1744573 11181023 := bstep (se 1 (by rfl) ⟨8385767, by rfl⟩ : syracuseStep 11181023 = 16771535) B16771535
theorem B44719775 : Blo 1744573 44719775 := bstep (se 1 (by rfl) ⟨33539831, by rfl⟩ : syracuseStep 44719775 = 67079663) B67079663
theorem B1744703 : Blo 1744573 1744703 := bstep (se 1 (by rfl) ⟨1308527, by rfl⟩ : syracuseStep 1744703 = 2617055) B2617055
theorem B6291719 : Blo 1744573 6291719 := bstep (se 1 (by rfl) ⟨4718789, by rfl⟩ : syracuseStep 6291719 = 9437579) B9437579
theorem B22356607 : Blo 1744573 22356607 := bstep (se 1 (by rfl) ⟨16767455, by rfl⟩ : syracuseStep 22356607 = 33534911) B33534911
theorem B1745599 : Blo 1744573 1745599 := bstep (se 1 (by rfl) ⟨1309199, by rfl⟩ : syracuseStep 1745599 = 2618399) B2618399
theorem B18867887 : Blo 1744573 18867887 := bstep (se 1 (by rfl) ⟨14150915, by rfl⟩ : syracuseStep 18867887 = 28301831) B28301831
theorem B17008967 : Blo 1744573 17008967 := bstep (se 1 (by rfl) ⟨12756725, by rfl⟩ : syracuseStep 17008967 = 25513451) B25513451
theorem B29813183 : Blo 1744573 29813183 := bstep (se 1 (by rfl) ⟨22359887, by rfl⟩ : syracuseStep 29813183 = 44719775) B44719775
theorem B14920807 : Blo 1744573 14920807 := bstep (se 1 (by rfl) ⟨11190605, by rfl⟩ : syracuseStep 14920807 = 22381211) B22381211
theorem B3312751 : Blo 1744573 3312751 := bstep (se 1 (by rfl) ⟨2484563, by rfl⟩ : syracuseStep 3312751 = 4969127) B4969127
theorem B2616863 : Blo 1744573 2616863 := bstep (se 1 (by rfl) ⟨1962647, by rfl⟩ : syracuseStep 2616863 = 3925295) B3925295
theorem B3928247 : Blo 1744573 3928247 := bstep (se 1 (by rfl) ⟨2946185, by rfl⟩ : syracuseStep 3928247 = 5892371) B5892371
theorem B40300841 : Blo 1744573 40300841 := bstep (se 2 (by rfl) ⟨15112815, by rfl⟩ : syracuseStep 40300841 = 30225631) B30225631
theorem B2618459 : Blo 1744573 2618459 := bstep (se 1 (by rfl) ⟨1963844, by rfl⟩ : syracuseStep 2618459 = 3927689) B3927689
theorem B33535457 : Blo 1744573 33535457 := bstep (se 2 (by rfl) ⟨12575796, by rfl⟩ : syracuseStep 33535457 = 25151593) B25151593
theorem B3585767 : Blo 1744573 3585767 := bstep (se 1 (by rfl) ⟨2689325, by rfl⟩ : syracuseStep 3585767 = 5378651) B5378651
theorem B54508513 : Blo 1744573 54508513 := bstep (se 2 (by rfl) ⟨20440692, by rfl⟩ : syracuseStep 54508513 = 40881385) B40881385
theorem B7454015 : Blo 1744573 7454015 := bstep (se 1 (by rfl) ⟨5590511, by rfl⟩ : syracuseStep 7454015 = 11181023) B11181023
theorem B4194479 : Blo 1744573 4194479 := bstep (se 1 (by rfl) ⟨3145859, by rfl⟩ : syracuseStep 4194479 = 6291719) B6291719
theorem B1745639 : Blo 1744573 1745639 := bstep (se 1 (by rfl) ⟨1309229, by rfl⟩ : syracuseStep 1745639 = 2618459) B2618459
theorem B22356971 : Blo 1744573 22356971 := bstep (se 1 (by rfl) ⟨16767728, by rfl⟩ : syracuseStep 22356971 = 33535457) B33535457
theorem B4417001 : Blo 1744573 4417001 := bstep (se 2 (by rfl) ⟨1656375, by rfl⟩ : syracuseStep 4417001 = 3312751) B3312751
theorem B19875455 : Blo 1744573 19875455 := bstep (se 1 (by rfl) ⟨14906591, by rfl⟩ : syracuseStep 19875455 = 29813183) B29813183
theorem B9562045 : Blo 1744573 9562045 := bstep (se 3 (by rfl) ⟨1792883, by rfl⟩ : syracuseStep 9562045 = 3585767) B3585767
theorem B12578591 : Blo 1744573 12578591 := bstep (se 1 (by rfl) ⟨9433943, by rfl⟩ : syracuseStep 12578591 = 18867887) B18867887
theorem B19894409 : Blo 1744573 19894409 := bstep (se 2 (by rfl) ⟨7460403, by rfl⟩ : syracuseStep 19894409 = 14920807) B14920807
theorem B4969343 : Blo 1744573 4969343 := bstep (se 1 (by rfl) ⟨3727007, by rfl⟩ : syracuseStep 4969343 = 7454015) B7454015
theorem B2618831 : Blo 1744573 2618831 := bstep (se 1 (by rfl) ⟨1964123, by rfl⟩ : syracuseStep 2618831 = 3928247) B3928247
theorem B26867227 : Blo 1744573 26867227 := bstep (se 1 (by rfl) ⟨20150420, by rfl⟩ : syracuseStep 26867227 = 40300841) B40300841
theorem B29808809 : Blo 1744573 29808809 := bstep (se 2 (by rfl) ⟨11178303, by rfl⟩ : syracuseStep 29808809 = 22356607) B22356607
theorem B45357245 : Blo 1744573 45357245 := bstep (se 3 (by rfl) ⟨8504483, by rfl⟩ : syracuseStep 45357245 = 17008967) B17008967
theorem B72678017 : Blo 1744573 72678017 := bstep (se 2 (by rfl) ⟨27254256, by rfl⟩ : syracuseStep 72678017 = 54508513) B54508513
theorem B1744575 : Blo 1744573 1744575 := bstep (se 1 (by rfl) ⟨1308431, by rfl⟩ : syracuseStep 1744575 = 2616863) B2616863
theorem B13262939 : Blo 1744573 13262939 := bstep (se 1 (by rfl) ⟨9947204, by rfl⟩ : syracuseStep 13262939 = 19894409) B19894409
theorem B1745887 : Blo 1744573 1745887 := bstep (se 1 (by rfl) ⟨1309415, by rfl⟩ : syracuseStep 1745887 = 2618831) B2618831
theorem B30238163 : Blo 1744573 30238163 := bstep (se 1 (by rfl) ⟨22678622, by rfl⟩ : syracuseStep 30238163 = 45357245) B45357245
theorem B193808045 : Blo 1744573 193808045 := bstep (se 3 (by rfl) ⟨36339008, by rfl⟩ : syracuseStep 193808045 = 72678017) B72678017
theorem B12749393 : Blo 1744573 12749393 := bstep (se 2 (by rfl) ⟨4781022, by rfl⟩ : syracuseStep 12749393 = 9562045) B9562045
theorem B2796319 : Blo 1744573 2796319 := bstep (se 1 (by rfl) ⟨2097239, by rfl⟩ : syracuseStep 2796319 = 4194479) B4194479
theorem B3312895 : Blo 1744573 3312895 := bstep (se 1 (by rfl) ⟨2484671, by rfl⟩ : syracuseStep 3312895 = 4969343) B4969343
theorem B14904647 : Blo 1744573 14904647 := bstep (se 1 (by rfl) ⟨11178485, by rfl⟩ : syracuseStep 14904647 = 22356971) B22356971
theorem B2944667 : Blo 1744573 2944667 := bstep (se 1 (by rfl) ⟨2208500, by rfl⟩ : syracuseStep 2944667 = 4417001) B4417001
theorem B13250303 : Blo 1744573 13250303 := bstep (se 1 (by rfl) ⟨9937727, by rfl⟩ : syracuseStep 13250303 = 19875455) B19875455
theorem B33542909 : Blo 1744573 33542909 := bstep (se 3 (by rfl) ⟨6289295, by rfl⟩ : syracuseStep 33542909 = 12578591) B12578591
theorem B19872539 : Blo 1744573 19872539 := bstep (se 1 (by rfl) ⟨14904404, by rfl⟩ : syracuseStep 19872539 = 29808809) B29808809
theorem B35822969 : Blo 1744573 35822969 := bstep (se 2 (by rfl) ⟨13433613, by rfl⟩ : syracuseStep 35822969 = 26867227) B26867227
theorem B3728425 : Blo 1744573 3728425 := bstep (se 2 (by rfl) ⟨1398159, by rfl⟩ : syracuseStep 3728425 = 2796319) B2796319
theorem B129205363 : Blo 1744573 129205363 := bstep (se 1 (by rfl) ⟨96904022, by rfl⟩ : syracuseStep 129205363 = 193808045) B193808045
theorem B4417193 : Blo 1744573 4417193 := bstep (se 2 (by rfl) ⟨1656447, by rfl⟩ : syracuseStep 4417193 = 3312895) B3312895
theorem B13248359 : Blo 1744573 13248359 := bstep (se 1 (by rfl) ⟨9936269, by rfl⟩ : syracuseStep 13248359 = 19872539) B19872539
theorem B23881979 : Blo 1744573 23881979 := bstep (se 1 (by rfl) ⟨17911484, by rfl⟩ : syracuseStep 23881979 = 35822969) B35822969
theorem B8833535 : Blo 1744573 8833535 := bstep (se 1 (by rfl) ⟨6625151, by rfl⟩ : syracuseStep 8833535 = 13250303) B13250303
theorem B8841959 : Blo 1744573 8841959 := bstep (se 1 (by rfl) ⟨6631469, by rfl⟩ : syracuseStep 8841959 = 13262939) B13262939
theorem B8499595 : Blo 1744573 8499595 := bstep (se 1 (by rfl) ⟨6374696, by rfl⟩ : syracuseStep 8499595 = 12749393) B12749393
theorem B1963111 : Blo 1744573 1963111 := bstep (se 1 (by rfl) ⟨1472333, by rfl⟩ : syracuseStep 1963111 = 2944667) B2944667
theorem B22361939 : Blo 1744573 22361939 := bstep (se 1 (by rfl) ⟨16771454, by rfl⟩ : syracuseStep 22361939 = 33542909) B33542909
theorem B20158775 : Blo 1744573 20158775 := bstep (se 1 (by rfl) ⟨15119081, by rfl⟩ : syracuseStep 20158775 = 30238163) B30238163
theorem B9936431 : Blo 1744573 9936431 := bstep (se 1 (by rfl) ⟨7452323, by rfl⟩ : syracuseStep 9936431 = 14904647) B14904647
theorem B8832239 : Blo 1744573 8832239 := bstep (se 1 (by rfl) ⟨6624179, by rfl⟩ : syracuseStep 8832239 = 13248359) B13248359
theorem B11332793 : Blo 1744573 11332793 := bstep (se 2 (by rfl) ⟨4249797, by rfl⟩ : syracuseStep 11332793 = 8499595) B8499595
theorem B215026933 : Blo 1744573 215026933 := bstep (se 5 (by rfl) ⟨10079387, by rfl⟩ : syracuseStep 215026933 = 20158775) B20158775
theorem B2944795 : Blo 1744573 2944795 := bstep (se 1 (by rfl) ⟨2208596, by rfl⟩ : syracuseStep 2944795 = 4417193) B4417193
theorem B2617481 : Blo 1744573 2617481 := bstep (se 2 (by rfl) ⟨981555, by rfl⟩ : syracuseStep 2617481 = 1963111) B1963111
theorem B172273817 : Blo 1744573 172273817 := bstep (se 2 (by rfl) ⟨64602681, by rfl⟩ : syracuseStep 172273817 = 129205363) B129205363
theorem B15921319 : Blo 1744573 15921319 := bstep (se 1 (by rfl) ⟨11940989, by rfl⟩ : syracuseStep 15921319 = 23881979) B23881979
theorem B5894639 : Blo 1744573 5894639 := bstep (se 1 (by rfl) ⟨4420979, by rfl⟩ : syracuseStep 5894639 = 8841959) B8841959
theorem B6624287 : Blo 1744573 6624287 := bstep (se 1 (by rfl) ⟨4968215, by rfl⟩ : syracuseStep 6624287 = 9936431) B9936431
theorem B14907959 : Blo 1744573 14907959 := bstep (se 1 (by rfl) ⟨11180969, by rfl⟩ : syracuseStep 14907959 = 22361939) B22361939
theorem B4971233 : Blo 1744573 4971233 := bstep (se 2 (by rfl) ⟨1864212, by rfl⟩ : syracuseStep 4971233 = 3728425) B3728425
theorem B5889023 : Blo 1744573 5889023 := bstep (se 1 (by rfl) ⟨4416767, by rfl⟩ : syracuseStep 5889023 = 8833535) B8833535
theorem B1744987 : Blo 1744573 1744987 := bstep (se 1 (by rfl) ⟨1308740, by rfl⟩ : syracuseStep 1744987 = 2617481) B2617481
theorem B4416191 : Blo 1744573 4416191 := bstep (se 1 (by rfl) ⟨3312143, by rfl⟩ : syracuseStep 4416191 = 6624287) B6624287
theorem B9938639 : Blo 1744573 9938639 := bstep (se 1 (by rfl) ⟨7453979, by rfl⟩ : syracuseStep 9938639 = 14907959) B14907959
theorem B13256621 : Blo 1744573 13256621 := bstep (se 3 (by rfl) ⟨2485616, by rfl⟩ : syracuseStep 13256621 = 4971233) B4971233
theorem B3926015 : Blo 1744573 3926015 := bstep (se 1 (by rfl) ⟨2944511, by rfl⟩ : syracuseStep 3926015 = 5889023) B5889023
theorem B7555195 : Blo 1744573 7555195 := bstep (se 1 (by rfl) ⟨5666396, by rfl⟩ : syracuseStep 7555195 = 11332793) B11332793
theorem B3926393 : Blo 1744573 3926393 := bstep (se 2 (by rfl) ⟨1472397, by rfl⟩ : syracuseStep 3926393 = 2944795) B2944795
theorem B21228425 : Blo 1744573 21228425 := bstep (se 2 (by rfl) ⟨7960659, by rfl⟩ : syracuseStep 21228425 = 15921319) B15921319
theorem B3929759 : Blo 1744573 3929759 := bstep (se 1 (by rfl) ⟨2947319, by rfl⟩ : syracuseStep 3929759 = 5894639) B5894639
theorem B459396845 : Blo 1744573 459396845 := bstep (se 3 (by rfl) ⟨86136908, by rfl⟩ : syracuseStep 459396845 = 172273817) B172273817
theorem B5888159 : Blo 1744573 5888159 := bstep (se 1 (by rfl) ⟨4416119, by rfl⟩ : syracuseStep 5888159 = 8832239) B8832239
theorem B286702577 : Blo 1744573 286702577 := bstep (se 2 (by rfl) ⟨107513466, by rfl⟩ : syracuseStep 286702577 = 215026933) B215026933
theorem B3925439 : Blo 1744573 3925439 := bstep (se 1 (by rfl) ⟨2944079, by rfl⟩ : syracuseStep 3925439 = 5888159) B5888159
theorem B2944127 : Blo 1744573 2944127 := bstep (se 1 (by rfl) ⟨2208095, by rfl⟩ : syracuseStep 2944127 = 4416191) B4416191
theorem B2617343 : Blo 1744573 2617343 := bstep (se 1 (by rfl) ⟨1963007, by rfl⟩ : syracuseStep 2617343 = 3926015) B3926015
theorem B2617595 : Blo 1744573 2617595 := bstep (se 1 (by rfl) ⟨1963196, by rfl⟩ : syracuseStep 2617595 = 3926393) B3926393
theorem B14152283 : Blo 1744573 14152283 := bstep (se 1 (by rfl) ⟨10614212, by rfl⟩ : syracuseStep 14152283 = 21228425) B21228425
theorem B10073593 : Blo 1744573 10073593 := bstep (se 2 (by rfl) ⟨3777597, by rfl⟩ : syracuseStep 10073593 = 7555195) B7555195
theorem B2619839 : Blo 1744573 2619839 := bstep (se 1 (by rfl) ⟨1964879, by rfl⟩ : syracuseStep 2619839 = 3929759) B3929759
theorem B6625759 : Blo 1744573 6625759 := bstep (se 1 (by rfl) ⟨4969319, by rfl⟩ : syracuseStep 6625759 = 9938639) B9938639
theorem B306264563 : Blo 1744573 306264563 := bstep (se 1 (by rfl) ⟨229698422, by rfl⟩ : syracuseStep 306264563 = 459396845) B459396845
theorem B8837747 : Blo 1744573 8837747 := bstep (se 1 (by rfl) ⟨6628310, by rfl⟩ : syracuseStep 8837747 = 13256621) B13256621
theorem B191135051 : Blo 1744573 191135051 := bstep (se 1 (by rfl) ⟨143351288, by rfl⟩ : syracuseStep 191135051 = 286702577) B286702577
theorem B1745063 : Blo 1744573 1745063 := bstep (se 1 (by rfl) ⟨1308797, by rfl⟩ : syracuseStep 1745063 = 2617595) B2617595
theorem B1746559 : Blo 1744573 1746559 := bstep (se 1 (by rfl) ⟨1309919, by rfl⟩ : syracuseStep 1746559 = 2619839) B2619839
theorem B5891831 : Blo 1744573 5891831 := bstep (se 1 (by rfl) ⟨4418873, by rfl⟩ : syracuseStep 5891831 = 8837747) B8837747
theorem B8834345 : Blo 1744573 8834345 := bstep (se 2 (by rfl) ⟨3312879, by rfl⟩ : syracuseStep 8834345 = 6625759) B6625759
theorem B2616959 : Blo 1744573 2616959 := bstep (se 1 (by rfl) ⟨1962719, by rfl⟩ : syracuseStep 2616959 = 3925439) B3925439
theorem B13431457 : Blo 1744573 13431457 := bstep (se 2 (by rfl) ⟨5036796, by rfl⟩ : syracuseStep 13431457 = 10073593) B10073593
theorem B1962751 : Blo 1744573 1962751 := bstep (se 1 (by rfl) ⟨1472063, by rfl⟩ : syracuseStep 1962751 = 2944127) B2944127
theorem B127423367 : Blo 1744573 127423367 := bstep (se 1 (by rfl) ⟨95567525, by rfl⟩ : syracuseStep 127423367 = 191135051) B191135051
theorem B9434855 : Blo 1744573 9434855 := bstep (se 1 (by rfl) ⟨7076141, by rfl⟩ : syracuseStep 9434855 = 14152283) B14152283
theorem B204176375 : Blo 1744573 204176375 := bstep (se 1 (by rfl) ⟨153132281, by rfl⟩ : syracuseStep 204176375 = 306264563) B306264563
theorem B1744895 : Blo 1744573 1744895 := bstep (se 1 (by rfl) ⟨1308671, by rfl⟩ : syracuseStep 1744895 = 2617343) B2617343
theorem B17908609 : Blo 1744573 17908609 := bstep (se 2 (by rfl) ⟨6715728, by rfl⟩ : syracuseStep 17908609 = 13431457) B13431457
theorem B2617001 : Blo 1744573 2617001 := bstep (se 2 (by rfl) ⟨981375, by rfl⟩ : syracuseStep 2617001 = 1962751) B1962751
theorem B3927887 : Blo 1744573 3927887 := bstep (se 1 (by rfl) ⟨2945915, by rfl⟩ : syracuseStep 3927887 = 5891831) B5891831
theorem B84948911 : Blo 1744573 84948911 := bstep (se 1 (by rfl) ⟨63711683, by rfl⟩ : syracuseStep 84948911 = 127423367) B127423367
theorem B6289903 : Blo 1744573 6289903 := bstep (se 1 (by rfl) ⟨4717427, by rfl⟩ : syracuseStep 6289903 = 9434855) B9434855
theorem B136117583 : Blo 1744573 136117583 := bstep (se 1 (by rfl) ⟨102088187, by rfl⟩ : syracuseStep 136117583 = 204176375) B204176375
theorem B5889563 : Blo 1744573 5889563 := bstep (se 1 (by rfl) ⟨4417172, by rfl⟩ : syracuseStep 5889563 = 8834345) B8834345
theorem B1744639 : Blo 1744573 1744639 := bstep (se 1 (by rfl) ⟨1308479, by rfl⟩ : syracuseStep 1744639 = 2616959) B2616959
theorem B56632607 : Blo 1744573 56632607 := bstep (se 1 (by rfl) ⟨42474455, by rfl⟩ : syracuseStep 56632607 = 84948911) B84948911
theorem B90745055 : Blo 1744573 90745055 := bstep (se 1 (by rfl) ⟨68058791, by rfl⟩ : syracuseStep 90745055 = 136117583) B136117583
theorem B3926375 : Blo 1744573 3926375 := bstep (se 1 (by rfl) ⟨2944781, by rfl⟩ : syracuseStep 3926375 = 5889563) B5889563
theorem B2618591 : Blo 1744573 2618591 := bstep (se 1 (by rfl) ⟨1963943, by rfl⟩ : syracuseStep 2618591 = 3927887) B3927887
theorem B8386537 : Blo 1744573 8386537 := bstep (se 2 (by rfl) ⟨3144951, by rfl⟩ : syracuseStep 8386537 = 6289903) B6289903
theorem B23878145 : Blo 1744573 23878145 := bstep (se 2 (by rfl) ⟨8954304, by rfl⟩ : syracuseStep 23878145 = 17908609) B17908609
theorem B1744667 : Blo 1744573 1744667 := bstep (se 1 (by rfl) ⟨1308500, by rfl⟩ : syracuseStep 1744667 = 2617001) B2617001
theorem B1745727 : Blo 1744573 1745727 := bstep (se 1 (by rfl) ⟨1309295, by rfl⟩ : syracuseStep 1745727 = 2618591) B2618591
theorem B15918763 : Blo 1744573 15918763 := bstep (se 1 (by rfl) ⟨11939072, by rfl⟩ : syracuseStep 15918763 = 23878145) B23878145
theorem B2617583 : Blo 1744573 2617583 := bstep (se 1 (by rfl) ⟨1963187, by rfl⟩ : syracuseStep 2617583 = 3926375) B3926375
theorem B37755071 : Blo 1744573 37755071 := bstep (se 1 (by rfl) ⟨28316303, by rfl⟩ : syracuseStep 37755071 = 56632607) B56632607
theorem B60496703 : Blo 1744573 60496703 := bstep (se 1 (by rfl) ⟨45372527, by rfl⟩ : syracuseStep 60496703 = 90745055) B90745055
theorem B11182049 : Blo 1744573 11182049 := bstep (se 2 (by rfl) ⟨4193268, by rfl⟩ : syracuseStep 11182049 = 8386537) B8386537
theorem B1745055 : Blo 1744573 1745055 := bstep (se 1 (by rfl) ⟨1308791, by rfl⟩ : syracuseStep 1745055 = 2617583) B2617583
theorem B40331135 : Blo 1744573 40331135 := bstep (se 1 (by rfl) ⟨30248351, by rfl⟩ : syracuseStep 40331135 = 60496703) B60496703
theorem B25170047 : Blo 1744573 25170047 := bstep (se 1 (by rfl) ⟨18877535, by rfl⟩ : syracuseStep 25170047 = 37755071) B37755071
theorem B21225017 : Blo 1744573 21225017 := bstep (se 2 (by rfl) ⟨7959381, by rfl⟩ : syracuseStep 21225017 = 15918763) B15918763
theorem B7454699 : Blo 1744573 7454699 := bstep (se 1 (by rfl) ⟨5591024, by rfl⟩ : syracuseStep 7454699 = 11182049) B11182049
theorem B26887423 : Blo 1744573 26887423 := bstep (se 1 (by rfl) ⟨20165567, by rfl⟩ : syracuseStep 26887423 = 40331135) B40331135
theorem B14150011 : Blo 1744573 14150011 := bstep (se 1 (by rfl) ⟨10612508, by rfl⟩ : syracuseStep 14150011 = 21225017) B21225017
theorem B16780031 : Blo 1744573 16780031 := bstep (se 1 (by rfl) ⟨12585023, by rfl⟩ : syracuseStep 16780031 = 25170047) B25170047
theorem B4969799 : Blo 1744573 4969799 := bstep (se 1 (by rfl) ⟨3727349, by rfl⟩ : syracuseStep 4969799 = 7454699) B7454699
theorem B18866681 : Blo 1744573 18866681 := bstep (se 2 (by rfl) ⟨7075005, by rfl⟩ : syracuseStep 18866681 = 14150011) B14150011
theorem B35849897 : Blo 1744573 35849897 := bstep (se 2 (by rfl) ⟨13443711, by rfl⟩ : syracuseStep 35849897 = 26887423) B26887423
theorem B3313199 : Blo 1744573 3313199 := bstep (se 1 (by rfl) ⟨2484899, by rfl⟩ : syracuseStep 3313199 = 4969799) B4969799
theorem B11186687 : Blo 1744573 11186687 := bstep (se 1 (by rfl) ⟨8390015, by rfl⟩ : syracuseStep 11186687 = 16780031) B16780031
theorem B12577787 : Blo 1744573 12577787 := bstep (se 1 (by rfl) ⟨9433340, by rfl⟩ : syracuseStep 12577787 = 18866681) B18866681
theorem B7457791 : Blo 1744573 7457791 := bstep (se 1 (by rfl) ⟨5593343, by rfl⟩ : syracuseStep 7457791 = 11186687) B11186687
theorem B23899931 : Blo 1744573 23899931 := bstep (se 1 (by rfl) ⟨17924948, by rfl⟩ : syracuseStep 23899931 = 35849897) B35849897
theorem B2208799 : Blo 1744573 2208799 := bstep (se 1 (by rfl) ⟨1656599, by rfl⟩ : syracuseStep 2208799 = 3313199) B3313199
theorem B2945065 : Blo 1744573 2945065 := bstep (se 2 (by rfl) ⟨1104399, by rfl⟩ : syracuseStep 2945065 = 2208799) B2208799
theorem B8385191 : Blo 1744573 8385191 := bstep (se 1 (by rfl) ⟨6288893, by rfl⟩ : syracuseStep 8385191 = 12577787) B12577787
theorem B9943721 : Blo 1744573 9943721 := bstep (se 2 (by rfl) ⟨3728895, by rfl⟩ : syracuseStep 9943721 = 7457791) B7457791
theorem B15933287 : Blo 1744573 15933287 := bstep (se 1 (by rfl) ⟨11949965, by rfl⟩ : syracuseStep 15933287 = 23899931) B23899931
theorem B6629147 : Blo 1744573 6629147 := bstep (se 1 (by rfl) ⟨4971860, by rfl⟩ : syracuseStep 6629147 = 9943721) B9943721
theorem B3926753 : Blo 1744573 3926753 := bstep (se 2 (by rfl) ⟨1472532, by rfl⟩ : syracuseStep 3926753 = 2945065) B2945065
theorem B5590127 : Blo 1744573 5590127 := bstep (se 1 (by rfl) ⟨4192595, by rfl⟩ : syracuseStep 5590127 = 8385191) B8385191
theorem B10622191 : Blo 1744573 10622191 := bstep (se 1 (by rfl) ⟨7966643, by rfl⟩ : syracuseStep 10622191 = 15933287) B15933287
theorem B4419431 : Blo 1744573 4419431 := bstep (se 1 (by rfl) ⟨3314573, by rfl⟩ : syracuseStep 4419431 = 6629147) B6629147
theorem B2617835 : Blo 1744573 2617835 := bstep (se 1 (by rfl) ⟨1963376, by rfl⟩ : syracuseStep 2617835 = 3926753) B3926753
theorem B14162921 : Blo 1744573 14162921 := bstep (se 2 (by rfl) ⟨5311095, by rfl⟩ : syracuseStep 14162921 = 10622191) B10622191
theorem B3726751 : Blo 1744573 3726751 := bstep (se 1 (by rfl) ⟨2795063, by rfl⟩ : syracuseStep 3726751 = 5590127) B5590127
theorem B1745223 : Blo 1744573 1745223 := bstep (se 1 (by rfl) ⟨1308917, by rfl⟩ : syracuseStep 1745223 = 2617835) B2617835
theorem B4969001 : Blo 1744573 4969001 := bstep (se 2 (by rfl) ⟨1863375, by rfl⟩ : syracuseStep 4969001 = 3726751) B3726751
theorem B9441947 : Blo 1744573 9441947 := bstep (se 1 (by rfl) ⟨7081460, by rfl⟩ : syracuseStep 9441947 = 14162921) B14162921
theorem B2946287 : Blo 1744573 2946287 := bstep (se 1 (by rfl) ⟨2209715, by rfl⟩ : syracuseStep 2946287 = 4419431) B4419431
theorem B3312667 : Blo 1744573 3312667 := bstep (se 1 (by rfl) ⟨2484500, by rfl⟩ : syracuseStep 3312667 = 4969001) B4969001
theorem B6294631 : Blo 1744573 6294631 := bstep (se 1 (by rfl) ⟨4720973, by rfl⟩ : syracuseStep 6294631 = 9441947) B9441947
theorem B1964191 : Blo 1744573 1964191 := bstep (se 1 (by rfl) ⟨1473143, by rfl⟩ : syracuseStep 1964191 = 2946287) B2946287
theorem B4416889 : Blo 1744573 4416889 := bstep (se 2 (by rfl) ⟨1656333, by rfl⟩ : syracuseStep 4416889 = 3312667) B3312667
theorem B8392841 : Blo 1744573 8392841 := bstep (se 2 (by rfl) ⟨3147315, by rfl⟩ : syracuseStep 8392841 = 6294631) B6294631
theorem B2618921 : Blo 1744573 2618921 := bstep (se 2 (by rfl) ⟨982095, by rfl⟩ : syracuseStep 2618921 = 1964191) B1964191
theorem B5595227 : Blo 1744573 5595227 := bstep (se 1 (by rfl) ⟨4196420, by rfl⟩ : syracuseStep 5595227 = 8392841) B8392841
theorem B1745947 : Blo 1744573 1745947 := bstep (se 1 (by rfl) ⟨1309460, by rfl⟩ : syracuseStep 1745947 = 2618921) B2618921
theorem B5889185 : Blo 1744573 5889185 := bstep (se 2 (by rfl) ⟨2208444, by rfl⟩ : syracuseStep 5889185 = 4416889) B4416889
theorem B3926123 : Blo 1744573 3926123 := bstep (se 1 (by rfl) ⟨2944592, by rfl⟩ : syracuseStep 3926123 = 5889185) B5889185
theorem B3730151 : Blo 1744573 3730151 := bstep (se 1 (by rfl) ⟨2797613, by rfl⟩ : syracuseStep 3730151 = 5595227) B5595227
theorem B9947069 : Blo 1744573 9947069 := bstep (se 3 (by rfl) ⟨1865075, by rfl⟩ : syracuseStep 9947069 = 3730151) B3730151
theorem B2617415 : Blo 1744573 2617415 := bstep (se 1 (by rfl) ⟨1963061, by rfl⟩ : syracuseStep 2617415 = 3926123) B3926123
theorem B1744943 : Blo 1744573 1744943 := bstep (se 1 (by rfl) ⟨1308707, by rfl⟩ : syracuseStep 1744943 = 2617415) B2617415
theorem B6631379 : Blo 1744573 6631379 := bstep (se 1 (by rfl) ⟨4973534, by rfl⟩ : syracuseStep 6631379 = 9947069) B9947069
theorem B4420919 : Blo 1744573 4420919 := bstep (se 1 (by rfl) ⟨3315689, by rfl⟩ : syracuseStep 4420919 = 6631379) B6631379
theorem B2947279 : Blo 1744573 2947279 := bstep (se 1 (by rfl) ⟨2210459, by rfl⟩ : syracuseStep 2947279 = 4420919) B4420919
theorem B3929705 : Blo 1744573 3929705 := bstep (se 2 (by rfl) ⟨1473639, by rfl⟩ : syracuseStep 3929705 = 2947279) B2947279
theorem B2619803 : Blo 1744573 2619803 := bstep (se 1 (by rfl) ⟨1964852, by rfl⟩ : syracuseStep 2619803 = 3929705) B3929705
theorem B1746535 : Blo 1744573 1746535 := bstep (se 1 (by rfl) ⟨1309901, by rfl⟩ : syracuseStep 1746535 = 2619803) B2619803

theorem C0 (j : ℕ) (h1 : 436143 ≤ j) (h2 : j ≤ 436642) : Blo 1744573 (4 * j + 3) := by
  interval_cases j
  · exact B1744575
  · exact B1744579
  · exact B1744583
  · exact B1744587
  · exact B1744591
  · exact B1744595
  · exact B1744599
  · exact B1744603
  · exact B1744607
  · exact B1744611
  · exact B1744615
  · exact B1744619
  · exact B1744623
  · exact B1744627
  · exact B1744631
  · exact B1744635
  · exact B1744639
  · exact B1744643
  · exact B1744647
  · exact B1744651
  · exact B1744655
  · exact B1744659
  · exact B1744663
  · exact B1744667
  · exact B1744671
  · exact B1744675
  · exact B1744679
  · exact B1744683
  · exact B1744687
  · exact B1744691
  · exact B1744695
  · exact B1744699
  · exact B1744703
  · exact B1744707
  · exact B1744711
  · exact B1744715
  · exact B1744719
  · exact B1744723
  · exact B1744727
  · exact B1744731
  · exact B1744735
  · exact B1744739
  · exact B1744743
  · exact B1744747
  · exact B1744751
  · exact B1744755
  · exact B1744759
  · exact B1744763
  · exact B1744767
  · exact B1744771
  · exact B1744775
  · exact B1744779
  · exact B1744783
  · exact B1744787
  · exact B1744791
  · exact B1744795
  · exact B1744799
  · exact B1744803
  · exact B1744807
  · exact B1744811
  · exact B1744815
  · exact B1744819
  · exact B1744823
  · exact B1744827
  · exact B1744831
  · exact B1744835
  · exact B1744839
  · exact B1744843
  · exact B1744847
  · exact B1744851
  · exact B1744855
  · exact B1744859
  · exact B1744863
  · exact B1744867
  · exact B1744871
  · exact B1744875
  · exact B1744879
  · exact B1744883
  · exact B1744887
  · exact B1744891
  · exact B1744895
  · exact B1744899
  · exact B1744903
  · exact B1744907
  · exact B1744911
  · exact B1744915
  · exact B1744919
  · exact B1744923
  · exact B1744927
  · exact B1744931
  · exact B1744935
  · exact B1744939
  · exact B1744943
  · exact B1744947
  · exact B1744951
  · exact B1744955
  · exact B1744959
  · exact B1744963
  · exact B1744967
  · exact B1744971
  · exact B1744975
  · exact B1744979
  · exact B1744983
  · exact B1744987
  · exact B1744991
  · exact B1744995
  · exact B1744999
  · exact B1745003
  · exact B1745007
  · exact B1745011
  · exact B1745015
  · exact B1745019
  · exact B1745023
  · exact B1745027
  · exact B1745031
  · exact B1745035
  · exact B1745039
  · exact B1745043
  · exact B1745047
  · exact B1745051
  · exact B1745055
  · exact B1745059
  · exact B1745063
  · exact B1745067
  · exact B1745071
  · exact B1745075
  · exact B1745079
  · exact B1745083
  · exact B1745087
  · exact B1745091
  · exact B1745095
  · exact B1745099
  · exact B1745103
  · exact B1745107
  · exact B1745111
  · exact B1745115
  · exact B1745119
  · exact B1745123
  · exact B1745127
  · exact B1745131
  · exact B1745135
  · exact B1745139
  · exact B1745143
  · exact B1745147
  · exact B1745151
  · exact B1745155
  · exact B1745159
  · exact B1745163
  · exact B1745167
  · exact B1745171
  · exact B1745175
  · exact B1745179
  · exact B1745183
  · exact B1745187
  · exact B1745191
  · exact B1745195
  · exact B1745199
  · exact B1745203
  · exact B1745207
  · exact B1745211
  · exact B1745215
  · exact B1745219
  · exact B1745223
  · exact B1745227
  · exact B1745231
  · exact B1745235
  · exact B1745239
  · exact B1745243
  · exact B1745247
  · exact B1745251
  · exact B1745255
  · exact B1745259
  · exact B1745263
  · exact B1745267
  · exact B1745271
  · exact B1745275
  · exact B1745279
  · exact B1745283
  · exact B1745287
  · exact B1745291
  · exact B1745295
  · exact B1745299
  · exact B1745303
  · exact B1745307
  · exact B1745311
  · exact B1745315
  · exact B1745319
  · exact B1745323
  · exact B1745327
  · exact B1745331
  · exact B1745335
  · exact B1745339
  · exact B1745343
  · exact B1745347
  · exact B1745351
  · exact B1745355
  · exact B1745359
  · exact B1745363
  · exact B1745367
  · exact B1745371
  · exact B1745375
  · exact B1745379
  · exact B1745383
  · exact B1745387
  · exact B1745391
  · exact B1745395
  · exact B1745399
  · exact B1745403
  · exact B1745407
  · exact B1745411
  · exact B1745415
  · exact B1745419
  · exact B1745423
  · exact B1745427
  · exact B1745431
  · exact B1745435
  · exact B1745439
  · exact B1745443
  · exact B1745447
  · exact B1745451
  · exact B1745455
  · exact B1745459
  · exact B1745463
  · exact B1745467
  · exact B1745471
  · exact B1745475
  · exact B1745479
  · exact B1745483
  · exact B1745487
  · exact B1745491
  · exact B1745495
  · exact B1745499
  · exact B1745503
  · exact B1745507
  · exact B1745511
  · exact B1745515
  · exact B1745519
  · exact B1745523
  · exact B1745527
  · exact B1745531
  · exact B1745535
  · exact B1745539
  · exact B1745543
  · exact B1745547
  · exact B1745551
  · exact B1745555
  · exact B1745559
  · exact B1745563
  · exact B1745567
  · exact B1745571
  · exact B1745575
  · exact B1745579
  · exact B1745583
  · exact B1745587
  · exact B1745591
  · exact B1745595
  · exact B1745599
  · exact B1745603
  · exact B1745607
  · exact B1745611
  · exact B1745615
  · exact B1745619
  · exact B1745623
  · exact B1745627
  · exact B1745631
  · exact B1745635
  · exact B1745639
  · exact B1745643
  · exact B1745647
  · exact B1745651
  · exact B1745655
  · exact B1745659
  · exact B1745663
  · exact B1745667
  · exact B1745671
  · exact B1745675
  · exact B1745679
  · exact B1745683
  · exact B1745687
  · exact B1745691
  · exact B1745695
  · exact B1745699
  · exact B1745703
  · exact B1745707
  · exact B1745711
  · exact B1745715
  · exact B1745719
  · exact B1745723
  · exact B1745727
  · exact B1745731
  · exact B1745735
  · exact B1745739
  · exact B1745743
  · exact B1745747
  · exact B1745751
  · exact B1745755
  · exact B1745759
  · exact B1745763
  · exact B1745767
  · exact B1745771
  · exact B1745775
  · exact B1745779
  · exact B1745783
  · exact B1745787
  · exact B1745791
  · exact B1745795
  · exact B1745799
  · exact B1745803
  · exact B1745807
  · exact B1745811
  · exact B1745815
  · exact B1745819
  · exact B1745823
  · exact B1745827
  · exact B1745831
  · exact B1745835
  · exact B1745839
  · exact B1745843
  · exact B1745847
  · exact B1745851
  · exact B1745855
  · exact B1745859
  · exact B1745863
  · exact B1745867
  · exact B1745871
  · exact B1745875
  · exact B1745879
  · exact B1745883
  · exact B1745887
  · exact B1745891
  · exact B1745895
  · exact B1745899
  · exact B1745903
  · exact B1745907
  · exact B1745911
  · exact B1745915
  · exact B1745919
  · exact B1745923
  · exact B1745927
  · exact B1745931
  · exact B1745935
  · exact B1745939
  · exact B1745943
  · exact B1745947
  · exact B1745951
  · exact B1745955
  · exact B1745959
  · exact B1745963
  · exact B1745967
  · exact B1745971
  · exact B1745975
  · exact B1745979
  · exact B1745983
  · exact B1745987
  · exact B1745991
  · exact B1745995
  · exact B1745999
  · exact B1746003
  · exact B1746007
  · exact B1746011
  · exact B1746015
  · exact B1746019
  · exact B1746023
  · exact B1746027
  · exact B1746031
  · exact B1746035
  · exact B1746039
  · exact B1746043
  · exact B1746047
  · exact B1746051
  · exact B1746055
  · exact B1746059
  · exact B1746063
  · exact B1746067
  · exact B1746071
  · exact B1746075
  · exact B1746079
  · exact B1746083
  · exact B1746087
  · exact B1746091
  · exact B1746095
  · exact B1746099
  · exact B1746103
  · exact B1746107
  · exact B1746111
  · exact B1746115
  · exact B1746119
  · exact B1746123
  · exact B1746127
  · exact B1746131
  · exact B1746135
  · exact B1746139
  · exact B1746143
  · exact B1746147
  · exact B1746151
  · exact B1746155
  · exact B1746159
  · exact B1746163
  · exact B1746167
  · exact B1746171
  · exact B1746175
  · exact B1746179
  · exact B1746183
  · exact B1746187
  · exact B1746191
  · exact B1746195
  · exact B1746199
  · exact B1746203
  · exact B1746207
  · exact B1746211
  · exact B1746215
  · exact B1746219
  · exact B1746223
  · exact B1746227
  · exact B1746231
  · exact B1746235
  · exact B1746239
  · exact B1746243
  · exact B1746247
  · exact B1746251
  · exact B1746255
  · exact B1746259
  · exact B1746263
  · exact B1746267
  · exact B1746271
  · exact B1746275
  · exact B1746279
  · exact B1746283
  · exact B1746287
  · exact B1746291
  · exact B1746295
  · exact B1746299
  · exact B1746303
  · exact B1746307
  · exact B1746311
  · exact B1746315
  · exact B1746319
  · exact B1746323
  · exact B1746327
  · exact B1746331
  · exact B1746335
  · exact B1746339
  · exact B1746343
  · exact B1746347
  · exact B1746351
  · exact B1746355
  · exact B1746359
  · exact B1746363
  · exact B1746367
  · exact B1746371
  · exact B1746375
  · exact B1746379
  · exact B1746383
  · exact B1746387
  · exact B1746391
  · exact B1746395
  · exact B1746399
  · exact B1746403
  · exact B1746407
  · exact B1746411
  · exact B1746415
  · exact B1746419
  · exact B1746423
  · exact B1746427
  · exact B1746431
  · exact B1746435
  · exact B1746439
  · exact B1746443
  · exact B1746447
  · exact B1746451
  · exact B1746455
  · exact B1746459
  · exact B1746463
  · exact B1746467
  · exact B1746471
  · exact B1746475
  · exact B1746479
  · exact B1746483
  · exact B1746487
  · exact B1746491
  · exact B1746495
  · exact B1746499
  · exact B1746503
  · exact B1746507
  · exact B1746511
  · exact B1746515
  · exact B1746519
  · exact B1746523
  · exact B1746527
  · exact B1746531
  · exact B1746535
  · exact B1746539
  · exact B1746543
  · exact B1746547
  · exact B1746551
  · exact B1746555
  · exact B1746559
  · exact B1746563
  · exact B1746567
  · exact B1746571

theorem solution (m : ℕ) (hlo : 1744573 ≤ m) (hhi : m ≤ 1746573) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 436143 ≤ j := by omega
    have hj2 : j ≤ 436642 := by omega
    have hb : Blo 1744573 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
