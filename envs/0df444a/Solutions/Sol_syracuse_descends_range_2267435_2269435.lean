-- Prove2me | solution 1 for syracuse_descends_range_2267435_2269435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:24.172932+00:00
-- url     : https://prove2.me/submissions/8903a8b8-d4d0-46af-9329-c96fd10a77c7

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

theorem B2550865 : Blo 2267435 2550865 := bbase (se 2 (by rfl) ⟨956574, by rfl⟩ : syracuseStep 2550865 = 1913149) (by norm_num)
theorem B3401153 : Blo 2267435 3401153 := bstep (se 2 (by rfl) ⟨1275432, by rfl⟩ : syracuseStep 3401153 = 2550865) B2550865
theorem B2267435 : Blo 2267435 2267435 := bstep (se 1 (by rfl) ⟨1700576, by rfl⟩ : syracuseStep 2267435 = 3401153) B3401153
theorem B3228445 : Blo 2267435 3228445 := bbase (se 3 (by rfl) ⟨605333, by rfl⟩ : syracuseStep 3228445 = 1210667) (by norm_num)
theorem B4304593 : Blo 2267435 4304593 := bstep (se 2 (by rfl) ⟨1614222, by rfl⟩ : syracuseStep 4304593 = 3228445) B3228445
theorem B5739457 : Blo 2267435 5739457 := bstep (se 2 (by rfl) ⟨2152296, by rfl⟩ : syracuseStep 5739457 = 4304593) B4304593
theorem B7652609 : Blo 2267435 7652609 := bstep (se 2 (by rfl) ⟨2869728, by rfl⟩ : syracuseStep 7652609 = 5739457) B5739457
theorem B5101739 : Blo 2267435 5101739 := bstep (se 1 (by rfl) ⟨3826304, by rfl⟩ : syracuseStep 5101739 = 7652609) B7652609
theorem B3401159 : Blo 2267435 3401159 := bstep (se 1 (by rfl) ⟨2550869, by rfl⟩ : syracuseStep 3401159 = 5101739) B5101739
theorem B2267439 : Blo 2267435 2267439 := bstep (se 1 (by rfl) ⟨1700579, by rfl⟩ : syracuseStep 2267439 = 3401159) B3401159
theorem B3401165 : Blo 2267435 3401165 := bbase (se 3 (by rfl) ⟨637718, by rfl⟩ : syracuseStep 3401165 = 1275437) (by norm_num)
theorem B2267443 : Blo 2267435 2267443 := bstep (se 1 (by rfl) ⟨1700582, by rfl⟩ : syracuseStep 2267443 = 3401165) B3401165
theorem B5101757 : Blo 2267435 5101757 := bbase (se 3 (by rfl) ⟨956579, by rfl⟩ : syracuseStep 5101757 = 1913159) (by norm_num)
theorem B3401171 : Blo 2267435 3401171 := bstep (se 1 (by rfl) ⟨2550878, by rfl⟩ : syracuseStep 3401171 = 5101757) B5101757
theorem B2267447 : Blo 2267435 2267447 := bstep (se 1 (by rfl) ⟨1700585, by rfl⟩ : syracuseStep 2267447 = 3401171) B3401171
theorem B3826325 : Blo 2267435 3826325 := bbase (se 6 (by rfl) ⟨89679, by rfl⟩ : syracuseStep 3826325 = 179359) (by norm_num)
theorem B2550883 : Blo 2267435 2550883 := bstep (se 1 (by rfl) ⟨1913162, by rfl⟩ : syracuseStep 2550883 = 3826325) B3826325
theorem B3401177 : Blo 2267435 3401177 := bstep (se 2 (by rfl) ⟨1275441, by rfl⟩ : syracuseStep 3401177 = 2550883) B2550883
theorem B2267451 : Blo 2267435 2267451 := bstep (se 1 (by rfl) ⟨1700588, by rfl⟩ : syracuseStep 2267451 = 3401177) B3401177
theorem B4908773 : Blo 2267435 4908773 := bbase (se 4 (by rfl) ⟨460197, by rfl⟩ : syracuseStep 4908773 = 920395) (by norm_num)
theorem B13090061 : Blo 2267435 13090061 := bstep (se 3 (by rfl) ⟨2454386, by rfl⟩ : syracuseStep 13090061 = 4908773) B4908773
theorem B8726707 : Blo 2267435 8726707 := bstep (se 1 (by rfl) ⟨6545030, by rfl⟩ : syracuseStep 8726707 = 13090061) B13090061
theorem B46542437 : Blo 2267435 46542437 := bstep (se 4 (by rfl) ⟨4363353, by rfl⟩ : syracuseStep 46542437 = 8726707) B8726707
theorem B31028291 : Blo 2267435 31028291 := bstep (se 1 (by rfl) ⟨23271218, by rfl⟩ : syracuseStep 31028291 = 46542437) B46542437
theorem B20685527 : Blo 2267435 20685527 := bstep (se 1 (by rfl) ⟨15514145, by rfl⟩ : syracuseStep 20685527 = 31028291) B31028291
theorem B13790351 : Blo 2267435 13790351 := bstep (se 1 (by rfl) ⟨10342763, by rfl⟩ : syracuseStep 13790351 = 20685527) B20685527
theorem B36774269 : Blo 2267435 36774269 := bstep (se 3 (by rfl) ⟨6895175, by rfl⟩ : syracuseStep 36774269 = 13790351) B13790351
theorem B24516179 : Blo 2267435 24516179 := bstep (se 1 (by rfl) ⟨18387134, by rfl⟩ : syracuseStep 24516179 = 36774269) B36774269
theorem B16344119 : Blo 2267435 16344119 := bstep (se 1 (by rfl) ⟨12258089, by rfl⟩ : syracuseStep 16344119 = 24516179) B24516179
theorem B10896079 : Blo 2267435 10896079 := bstep (se 1 (by rfl) ⟨8172059, by rfl⟩ : syracuseStep 10896079 = 16344119) B16344119
theorem B14528105 : Blo 2267435 14528105 := bstep (se 2 (by rfl) ⟨5448039, by rfl⟩ : syracuseStep 14528105 = 10896079) B10896079
theorem B9685403 : Blo 2267435 9685403 := bstep (se 1 (by rfl) ⟨7264052, by rfl⟩ : syracuseStep 9685403 = 14528105) B14528105
theorem B6456935 : Blo 2267435 6456935 := bstep (se 1 (by rfl) ⟨4842701, by rfl⟩ : syracuseStep 6456935 = 9685403) B9685403
theorem B17218493 : Blo 2267435 17218493 := bstep (se 3 (by rfl) ⟨3228467, by rfl⟩ : syracuseStep 17218493 = 6456935) B6456935
theorem B11478995 : Blo 2267435 11478995 := bstep (se 1 (by rfl) ⟨8609246, by rfl⟩ : syracuseStep 11478995 = 17218493) B17218493
theorem B7652663 : Blo 2267435 7652663 := bstep (se 1 (by rfl) ⟨5739497, by rfl⟩ : syracuseStep 7652663 = 11478995) B11478995
theorem B5101775 : Blo 2267435 5101775 := bstep (se 1 (by rfl) ⟨3826331, by rfl⟩ : syracuseStep 5101775 = 7652663) B7652663
theorem B3401183 : Blo 2267435 3401183 := bstep (se 1 (by rfl) ⟨2550887, by rfl⟩ : syracuseStep 3401183 = 5101775) B5101775
theorem B2267455 : Blo 2267435 2267455 := bstep (se 1 (by rfl) ⟨1700591, by rfl⟩ : syracuseStep 2267455 = 3401183) B3401183
theorem B3401189 : Blo 2267435 3401189 := bbase (se 4 (by rfl) ⟨318861, by rfl⟩ : syracuseStep 3401189 = 637723) (by norm_num)
theorem B2267459 : Blo 2267435 2267459 := bstep (se 1 (by rfl) ⟨1700594, by rfl⟩ : syracuseStep 2267459 = 3401189) B3401189
theorem B2393765 : Blo 2267435 2393765 := bbase (se 4 (by rfl) ⟨224415, by rfl⟩ : syracuseStep 2393765 = 448831) (by norm_num)
theorem B102133973 : Blo 2267435 102133973 := bstep (se 7 (by rfl) ⟨1196882, by rfl⟩ : syracuseStep 102133973 = 2393765) B2393765
theorem B272357261 : Blo 2267435 272357261 := bstep (se 3 (by rfl) ⟨51066986, by rfl⟩ : syracuseStep 272357261 = 102133973) B102133973
theorem B181571507 : Blo 2267435 181571507 := bstep (se 1 (by rfl) ⟨136178630, by rfl⟩ : syracuseStep 181571507 = 272357261) B272357261
theorem B121047671 : Blo 2267435 121047671 := bstep (se 1 (by rfl) ⟨90785753, by rfl⟩ : syracuseStep 121047671 = 181571507) B181571507
theorem B80698447 : Blo 2267435 80698447 := bstep (se 1 (by rfl) ⟨60523835, by rfl⟩ : syracuseStep 80698447 = 121047671) B121047671
theorem B107597929 : Blo 2267435 107597929 := bstep (se 2 (by rfl) ⟨40349223, by rfl⟩ : syracuseStep 107597929 = 80698447) B80698447
theorem B143463905 : Blo 2267435 143463905 := bstep (se 2 (by rfl) ⟨53798964, by rfl⟩ : syracuseStep 143463905 = 107597929) B107597929
theorem B95642603 : Blo 2267435 95642603 := bstep (se 1 (by rfl) ⟨71731952, by rfl⟩ : syracuseStep 95642603 = 143463905) B143463905
theorem B63761735 : Blo 2267435 63761735 := bstep (se 1 (by rfl) ⟨47821301, by rfl⟩ : syracuseStep 63761735 = 95642603) B95642603
theorem B42507823 : Blo 2267435 42507823 := bstep (se 1 (by rfl) ⟨31880867, by rfl⟩ : syracuseStep 42507823 = 63761735) B63761735
theorem B56677097 : Blo 2267435 56677097 := bstep (se 2 (by rfl) ⟨21253911, by rfl⟩ : syracuseStep 56677097 = 42507823) B42507823
theorem B37784731 : Blo 2267435 37784731 := bstep (se 1 (by rfl) ⟨28338548, by rfl⟩ : syracuseStep 37784731 = 56677097) B56677097
theorem B50379641 : Blo 2267435 50379641 := bstep (se 2 (by rfl) ⟨18892365, by rfl⟩ : syracuseStep 50379641 = 37784731) B37784731
theorem B33586427 : Blo 2267435 33586427 := bstep (se 1 (by rfl) ⟨25189820, by rfl⟩ : syracuseStep 33586427 = 50379641) B50379641
theorem B22390951 : Blo 2267435 22390951 := bstep (se 1 (by rfl) ⟨16793213, by rfl⟩ : syracuseStep 22390951 = 33586427) B33586427
theorem B29854601 : Blo 2267435 29854601 := bstep (se 2 (by rfl) ⟨11195475, by rfl⟩ : syracuseStep 29854601 = 22390951) B22390951
theorem B19903067 : Blo 2267435 19903067 := bstep (se 1 (by rfl) ⟨14927300, by rfl⟩ : syracuseStep 19903067 = 29854601) B29854601
theorem B13268711 : Blo 2267435 13268711 := bstep (se 1 (by rfl) ⟨9951533, by rfl⟩ : syracuseStep 13268711 = 19903067) B19903067
theorem B8845807 : Blo 2267435 8845807 := bstep (se 1 (by rfl) ⟨6634355, by rfl⟩ : syracuseStep 8845807 = 13268711) B13268711
theorem B11794409 : Blo 2267435 11794409 := bstep (se 2 (by rfl) ⟨4422903, by rfl⟩ : syracuseStep 11794409 = 8845807) B8845807
theorem B7862939 : Blo 2267435 7862939 := bstep (se 1 (by rfl) ⟨5897204, by rfl⟩ : syracuseStep 7862939 = 11794409) B11794409
theorem B5241959 : Blo 2267435 5241959 := bstep (se 1 (by rfl) ⟨3931469, by rfl⟩ : syracuseStep 5241959 = 7862939) B7862939
theorem B3494639 : Blo 2267435 3494639 := bstep (se 1 (by rfl) ⟨2620979, by rfl⟩ : syracuseStep 3494639 = 5241959) B5241959
theorem B2329759 : Blo 2267435 2329759 := bstep (se 1 (by rfl) ⟨1747319, by rfl⟩ : syracuseStep 2329759 = 3494639) B3494639
theorem B3106345 : Blo 2267435 3106345 := bstep (se 2 (by rfl) ⟨1164879, by rfl⟩ : syracuseStep 3106345 = 2329759) B2329759
theorem B4141793 : Blo 2267435 4141793 := bstep (se 2 (by rfl) ⟨1553172, by rfl⟩ : syracuseStep 4141793 = 3106345) B3106345
theorem B2761195 : Blo 2267435 2761195 := bstep (se 1 (by rfl) ⟨2070896, by rfl⟩ : syracuseStep 2761195 = 4141793) B4141793
theorem B3681593 : Blo 2267435 3681593 := bstep (se 2 (by rfl) ⟨1380597, by rfl⟩ : syracuseStep 3681593 = 2761195) B2761195
theorem B39270325 : Blo 2267435 39270325 := bstep (se 5 (by rfl) ⟨1840796, by rfl⟩ : syracuseStep 39270325 = 3681593) B3681593
theorem B52360433 : Blo 2267435 52360433 := bstep (se 2 (by rfl) ⟨19635162, by rfl⟩ : syracuseStep 52360433 = 39270325) B39270325
theorem B34906955 : Blo 2267435 34906955 := bstep (se 1 (by rfl) ⟨26180216, by rfl⟩ : syracuseStep 34906955 = 52360433) B52360433
theorem B93085213 : Blo 2267435 93085213 := bstep (se 3 (by rfl) ⟨17453477, by rfl⟩ : syracuseStep 93085213 = 34906955) B34906955
theorem B124113617 : Blo 2267435 124113617 := bstep (se 2 (by rfl) ⟨46542606, by rfl⟩ : syracuseStep 124113617 = 93085213) B93085213
theorem B82742411 : Blo 2267435 82742411 := bstep (se 1 (by rfl) ⟨62056808, by rfl⟩ : syracuseStep 82742411 = 124113617) B124113617
theorem B55161607 : Blo 2267435 55161607 := bstep (se 1 (by rfl) ⟨41371205, by rfl⟩ : syracuseStep 55161607 = 82742411) B82742411
theorem B73548809 : Blo 2267435 73548809 := bstep (se 2 (by rfl) ⟨27580803, by rfl⟩ : syracuseStep 73548809 = 55161607) B55161607
theorem B49032539 : Blo 2267435 49032539 := bstep (se 1 (by rfl) ⟨36774404, by rfl⟩ : syracuseStep 49032539 = 73548809) B73548809
theorem B32688359 : Blo 2267435 32688359 := bstep (se 1 (by rfl) ⟨24516269, by rfl⟩ : syracuseStep 32688359 = 49032539) B49032539
theorem B21792239 : Blo 2267435 21792239 := bstep (se 1 (by rfl) ⟨16344179, by rfl⟩ : syracuseStep 21792239 = 32688359) B32688359
theorem B14528159 : Blo 2267435 14528159 := bstep (se 1 (by rfl) ⟨10896119, by rfl⟩ : syracuseStep 14528159 = 21792239) B21792239
theorem B9685439 : Blo 2267435 9685439 := bstep (se 1 (by rfl) ⟨7264079, by rfl⟩ : syracuseStep 9685439 = 14528159) B14528159
theorem B6456959 : Blo 2267435 6456959 := bstep (se 1 (by rfl) ⟨4842719, by rfl⟩ : syracuseStep 6456959 = 9685439) B9685439
theorem B4304639 : Blo 2267435 4304639 := bstep (se 1 (by rfl) ⟨3228479, by rfl⟩ : syracuseStep 4304639 = 6456959) B6456959
theorem B2869759 : Blo 2267435 2869759 := bstep (se 1 (by rfl) ⟨2152319, by rfl⟩ : syracuseStep 2869759 = 4304639) B4304639
theorem B3826345 : Blo 2267435 3826345 := bstep (se 2 (by rfl) ⟨1434879, by rfl⟩ : syracuseStep 3826345 = 2869759) B2869759
theorem B5101793 : Blo 2267435 5101793 := bstep (se 2 (by rfl) ⟨1913172, by rfl⟩ : syracuseStep 5101793 = 3826345) B3826345
theorem B3401195 : Blo 2267435 3401195 := bstep (se 1 (by rfl) ⟨2550896, by rfl⟩ : syracuseStep 3401195 = 5101793) B5101793
theorem B2267463 : Blo 2267435 2267463 := bstep (se 1 (by rfl) ⟨1700597, by rfl⟩ : syracuseStep 2267463 = 3401195) B3401195
theorem B2550901 : Blo 2267435 2550901 := bbase (se 5 (by rfl) ⟨119573, by rfl⟩ : syracuseStep 2550901 = 239147) (by norm_num)
theorem B3401201 : Blo 2267435 3401201 := bstep (se 2 (by rfl) ⟨1275450, by rfl⟩ : syracuseStep 3401201 = 2550901) B2550901
theorem B2267467 : Blo 2267435 2267467 := bstep (se 1 (by rfl) ⟨1700600, by rfl⟩ : syracuseStep 2267467 = 3401201) B3401201
theorem B2869769 : Blo 2267435 2869769 := bbase (se 2 (by rfl) ⟨1076163, by rfl⟩ : syracuseStep 2869769 = 2152327) (by norm_num)
theorem B7652717 : Blo 2267435 7652717 := bstep (se 3 (by rfl) ⟨1434884, by rfl⟩ : syracuseStep 7652717 = 2869769) B2869769
theorem B5101811 : Blo 2267435 5101811 := bstep (se 1 (by rfl) ⟨3826358, by rfl⟩ : syracuseStep 5101811 = 7652717) B7652717
theorem B3401207 : Blo 2267435 3401207 := bstep (se 1 (by rfl) ⟨2550905, by rfl⟩ : syracuseStep 3401207 = 5101811) B5101811
theorem B2267471 : Blo 2267435 2267471 := bstep (se 1 (by rfl) ⟨1700603, by rfl⟩ : syracuseStep 2267471 = 3401207) B3401207
theorem B3401213 : Blo 2267435 3401213 := bbase (se 3 (by rfl) ⟨637727, by rfl⟩ : syracuseStep 3401213 = 1275455) (by norm_num)
theorem B2267475 : Blo 2267435 2267475 := bstep (se 1 (by rfl) ⟨1700606, by rfl⟩ : syracuseStep 2267475 = 3401213) B3401213
theorem B5101829 : Blo 2267435 5101829 := bbase (se 4 (by rfl) ⟨478296, by rfl⟩ : syracuseStep 5101829 = 956593) (by norm_num)
theorem B3401219 : Blo 2267435 3401219 := bstep (se 1 (by rfl) ⟨2550914, by rfl⟩ : syracuseStep 3401219 = 5101829) B5101829
theorem B2267479 : Blo 2267435 2267479 := bstep (se 1 (by rfl) ⟨1700609, by rfl⟩ : syracuseStep 2267479 = 3401219) B3401219
theorem B4304677 : Blo 2267435 4304677 := bbase (se 4 (by rfl) ⟨403563, by rfl⟩ : syracuseStep 4304677 = 807127) (by norm_num)
theorem B5739569 : Blo 2267435 5739569 := bstep (se 2 (by rfl) ⟨2152338, by rfl⟩ : syracuseStep 5739569 = 4304677) B4304677
theorem B3826379 : Blo 2267435 3826379 := bstep (se 1 (by rfl) ⟨2869784, by rfl⟩ : syracuseStep 3826379 = 5739569) B5739569
theorem B2550919 : Blo 2267435 2550919 := bstep (se 1 (by rfl) ⟨1913189, by rfl⟩ : syracuseStep 2550919 = 3826379) B3826379
theorem B3401225 : Blo 2267435 3401225 := bstep (se 2 (by rfl) ⟨1275459, by rfl⟩ : syracuseStep 3401225 = 2550919) B2550919
theorem B2267483 : Blo 2267435 2267483 := bstep (se 1 (by rfl) ⟨1700612, by rfl⟩ : syracuseStep 2267483 = 3401225) B3401225
theorem B11479157 : Blo 2267435 11479157 := bbase (se 5 (by rfl) ⟨538085, by rfl⟩ : syracuseStep 11479157 = 1076171) (by norm_num)
theorem B7652771 : Blo 2267435 7652771 := bstep (se 1 (by rfl) ⟨5739578, by rfl⟩ : syracuseStep 7652771 = 11479157) B11479157
theorem B5101847 : Blo 2267435 5101847 := bstep (se 1 (by rfl) ⟨3826385, by rfl⟩ : syracuseStep 5101847 = 7652771) B7652771
theorem B3401231 : Blo 2267435 3401231 := bstep (se 1 (by rfl) ⟨2550923, by rfl⟩ : syracuseStep 3401231 = 5101847) B5101847
theorem B2267487 : Blo 2267435 2267487 := bstep (se 1 (by rfl) ⟨1700615, by rfl⟩ : syracuseStep 2267487 = 3401231) B3401231
theorem B3401237 : Blo 2267435 3401237 := bbase (se 6 (by rfl) ⟨79716, by rfl⟩ : syracuseStep 3401237 = 159433) (by norm_num)
theorem B2267491 : Blo 2267435 2267491 := bstep (se 1 (by rfl) ⟨1700618, by rfl⟩ : syracuseStep 2267491 = 3401237) B3401237
theorem B7264181 : Blo 2267435 7264181 := bbase (se 5 (by rfl) ⟨340508, by rfl⟩ : syracuseStep 7264181 = 681017) (by norm_num)
theorem B19371149 : Blo 2267435 19371149 := bstep (se 3 (by rfl) ⟨3632090, by rfl⟩ : syracuseStep 19371149 = 7264181) B7264181
theorem B12914099 : Blo 2267435 12914099 := bstep (se 1 (by rfl) ⟨9685574, by rfl⟩ : syracuseStep 12914099 = 19371149) B19371149
theorem B8609399 : Blo 2267435 8609399 := bstep (se 1 (by rfl) ⟨6457049, by rfl⟩ : syracuseStep 8609399 = 12914099) B12914099
theorem B5739599 : Blo 2267435 5739599 := bstep (se 1 (by rfl) ⟨4304699, by rfl⟩ : syracuseStep 5739599 = 8609399) B8609399
theorem B3826399 : Blo 2267435 3826399 := bstep (se 1 (by rfl) ⟨2869799, by rfl⟩ : syracuseStep 3826399 = 5739599) B5739599
theorem B5101865 : Blo 2267435 5101865 := bstep (se 2 (by rfl) ⟨1913199, by rfl⟩ : syracuseStep 5101865 = 3826399) B3826399
theorem B3401243 : Blo 2267435 3401243 := bstep (se 1 (by rfl) ⟨2550932, by rfl⟩ : syracuseStep 3401243 = 5101865) B5101865
theorem B2267495 : Blo 2267435 2267495 := bstep (se 1 (by rfl) ⟨1700621, by rfl⟩ : syracuseStep 2267495 = 3401243) B3401243
theorem B2550937 : Blo 2267435 2550937 := bbase (se 2 (by rfl) ⟨956601, by rfl⟩ : syracuseStep 2550937 = 1913203) (by norm_num)
theorem B3401249 : Blo 2267435 3401249 := bstep (se 2 (by rfl) ⟨1275468, by rfl⟩ : syracuseStep 3401249 = 2550937) B2550937
theorem B2267499 : Blo 2267435 2267499 := bstep (se 1 (by rfl) ⟨1700624, by rfl⟩ : syracuseStep 2267499 = 3401249) B3401249
theorem B8609429 : Blo 2267435 8609429 := bbase (se 6 (by rfl) ⟨201783, by rfl⟩ : syracuseStep 8609429 = 403567) (by norm_num)
theorem B5739619 : Blo 2267435 5739619 := bstep (se 1 (by rfl) ⟨4304714, by rfl⟩ : syracuseStep 5739619 = 8609429) B8609429
theorem B7652825 : Blo 2267435 7652825 := bstep (se 2 (by rfl) ⟨2869809, by rfl⟩ : syracuseStep 7652825 = 5739619) B5739619
theorem B5101883 : Blo 2267435 5101883 := bstep (se 1 (by rfl) ⟨3826412, by rfl⟩ : syracuseStep 5101883 = 7652825) B7652825
theorem B3401255 : Blo 2267435 3401255 := bstep (se 1 (by rfl) ⟨2550941, by rfl⟩ : syracuseStep 3401255 = 5101883) B5101883
theorem B2267503 : Blo 2267435 2267503 := bstep (se 1 (by rfl) ⟨1700627, by rfl⟩ : syracuseStep 2267503 = 3401255) B3401255
theorem B3401261 : Blo 2267435 3401261 := bbase (se 3 (by rfl) ⟨637736, by rfl⟩ : syracuseStep 3401261 = 1275473) (by norm_num)
theorem B2267507 : Blo 2267435 2267507 := bstep (se 1 (by rfl) ⟨1700630, by rfl⟩ : syracuseStep 2267507 = 3401261) B3401261
theorem B5101901 : Blo 2267435 5101901 := bbase (se 3 (by rfl) ⟨956606, by rfl⟩ : syracuseStep 5101901 = 1913213) (by norm_num)
theorem B3401267 : Blo 2267435 3401267 := bstep (se 1 (by rfl) ⟨2550950, by rfl⟩ : syracuseStep 3401267 = 5101901) B5101901
theorem B2267511 : Blo 2267435 2267511 := bstep (se 1 (by rfl) ⟨1700633, by rfl⟩ : syracuseStep 2267511 = 3401267) B3401267
theorem B2869825 : Blo 2267435 2869825 := bbase (se 2 (by rfl) ⟨1076184, by rfl⟩ : syracuseStep 2869825 = 2152369) (by norm_num)
theorem B3826433 : Blo 2267435 3826433 := bstep (se 2 (by rfl) ⟨1434912, by rfl⟩ : syracuseStep 3826433 = 2869825) B2869825
theorem B2550955 : Blo 2267435 2550955 := bstep (se 1 (by rfl) ⟨1913216, by rfl⟩ : syracuseStep 2550955 = 3826433) B3826433
theorem B3401273 : Blo 2267435 3401273 := bstep (se 2 (by rfl) ⟨1275477, by rfl⟩ : syracuseStep 3401273 = 2550955) B2550955
theorem B2267515 : Blo 2267435 2267515 := bstep (se 1 (by rfl) ⟨1700636, by rfl⟩ : syracuseStep 2267515 = 3401273) B3401273
theorem B2724097 : Blo 2267435 2724097 := bbase (se 2 (by rfl) ⟨1021536, by rfl⟩ : syracuseStep 2724097 = 2043073) (by norm_num)
theorem B3632129 : Blo 2267435 3632129 := bstep (se 2 (by rfl) ⟨1362048, by rfl⟩ : syracuseStep 3632129 = 2724097) B2724097
theorem B2421419 : Blo 2267435 2421419 := bstep (se 1 (by rfl) ⟨1816064, by rfl⟩ : syracuseStep 2421419 = 3632129) B3632129
theorem B25828469 : Blo 2267435 25828469 := bstep (se 5 (by rfl) ⟨1210709, by rfl⟩ : syracuseStep 25828469 = 2421419) B2421419
theorem B17218979 : Blo 2267435 17218979 := bstep (se 1 (by rfl) ⟨12914234, by rfl⟩ : syracuseStep 17218979 = 25828469) B25828469
theorem B11479319 : Blo 2267435 11479319 := bstep (se 1 (by rfl) ⟨8609489, by rfl⟩ : syracuseStep 11479319 = 17218979) B17218979
theorem B7652879 : Blo 2267435 7652879 := bstep (se 1 (by rfl) ⟨5739659, by rfl⟩ : syracuseStep 7652879 = 11479319) B11479319
theorem B5101919 : Blo 2267435 5101919 := bstep (se 1 (by rfl) ⟨3826439, by rfl⟩ : syracuseStep 5101919 = 7652879) B7652879
theorem B3401279 : Blo 2267435 3401279 := bstep (se 1 (by rfl) ⟨2550959, by rfl⟩ : syracuseStep 3401279 = 5101919) B5101919
theorem B2267519 : Blo 2267435 2267519 := bstep (se 1 (by rfl) ⟨1700639, by rfl⟩ : syracuseStep 2267519 = 3401279) B3401279
theorem B3401285 : Blo 2267435 3401285 := bbase (se 4 (by rfl) ⟨318870, by rfl⟩ : syracuseStep 3401285 = 637741) (by norm_num)
theorem B2267523 : Blo 2267435 2267523 := bstep (se 1 (by rfl) ⟨1700642, by rfl⟩ : syracuseStep 2267523 = 3401285) B3401285
theorem B3826453 : Blo 2267435 3826453 := bbase (se 6 (by rfl) ⟨89682, by rfl⟩ : syracuseStep 3826453 = 179365) (by norm_num)
theorem B5101937 : Blo 2267435 5101937 := bstep (se 2 (by rfl) ⟨1913226, by rfl⟩ : syracuseStep 5101937 = 3826453) B3826453
theorem B3401291 : Blo 2267435 3401291 := bstep (se 1 (by rfl) ⟨2550968, by rfl⟩ : syracuseStep 3401291 = 5101937) B5101937
theorem B2267527 : Blo 2267435 2267527 := bstep (se 1 (by rfl) ⟨1700645, by rfl⟩ : syracuseStep 2267527 = 3401291) B3401291
theorem B2550973 : Blo 2267435 2550973 := bbase (se 3 (by rfl) ⟨478307, by rfl⟩ : syracuseStep 2550973 = 956615) (by norm_num)
theorem B3401297 : Blo 2267435 3401297 := bstep (se 2 (by rfl) ⟨1275486, by rfl⟩ : syracuseStep 3401297 = 2550973) B2550973
theorem B2267531 : Blo 2267435 2267531 := bstep (se 1 (by rfl) ⟨1700648, by rfl⟩ : syracuseStep 2267531 = 3401297) B3401297
theorem B7652933 : Blo 2267435 7652933 := bbase (se 4 (by rfl) ⟨717462, by rfl⟩ : syracuseStep 7652933 = 1434925) (by norm_num)
theorem B5101955 : Blo 2267435 5101955 := bstep (se 1 (by rfl) ⟨3826466, by rfl⟩ : syracuseStep 5101955 = 7652933) B7652933
theorem B3401303 : Blo 2267435 3401303 := bstep (se 1 (by rfl) ⟨2550977, by rfl⟩ : syracuseStep 3401303 = 5101955) B5101955
theorem B2267535 : Blo 2267435 2267535 := bstep (se 1 (by rfl) ⟨1700651, by rfl⟩ : syracuseStep 2267535 = 3401303) B3401303
theorem B3401309 : Blo 2267435 3401309 := bbase (se 3 (by rfl) ⟨637745, by rfl⟩ : syracuseStep 3401309 = 1275491) (by norm_num)
theorem B2267539 : Blo 2267435 2267539 := bstep (se 1 (by rfl) ⟨1700654, by rfl⟩ : syracuseStep 2267539 = 3401309) B3401309
theorem B5101973 : Blo 2267435 5101973 := bbase (se 6 (by rfl) ⟨119577, by rfl⟩ : syracuseStep 5101973 = 239155) (by norm_num)
theorem B3401315 : Blo 2267435 3401315 := bstep (se 1 (by rfl) ⟨2550986, by rfl⟩ : syracuseStep 3401315 = 5101973) B5101973
theorem B2267543 : Blo 2267435 2267543 := bstep (se 1 (by rfl) ⟨1700657, by rfl⟩ : syracuseStep 2267543 = 3401315) B3401315
theorem B4086197 : Blo 2267435 4086197 := bbase (se 5 (by rfl) ⟨191540, by rfl⟩ : syracuseStep 4086197 = 383081) (by norm_num)
theorem B2724131 : Blo 2267435 2724131 := bstep (se 1 (by rfl) ⟨2043098, by rfl⟩ : syracuseStep 2724131 = 4086197) B4086197
theorem B7264349 : Blo 2267435 7264349 := bstep (se 3 (by rfl) ⟨1362065, by rfl⟩ : syracuseStep 7264349 = 2724131) B2724131
theorem B4842899 : Blo 2267435 4842899 := bstep (se 1 (by rfl) ⟨3632174, by rfl⟩ : syracuseStep 4842899 = 7264349) B7264349
theorem B3228599 : Blo 2267435 3228599 := bstep (se 1 (by rfl) ⟨2421449, by rfl⟩ : syracuseStep 3228599 = 4842899) B4842899
theorem B8609597 : Blo 2267435 8609597 := bstep (se 3 (by rfl) ⟨1614299, by rfl⟩ : syracuseStep 8609597 = 3228599) B3228599
theorem B5739731 : Blo 2267435 5739731 := bstep (se 1 (by rfl) ⟨4304798, by rfl⟩ : syracuseStep 5739731 = 8609597) B8609597
theorem B3826487 : Blo 2267435 3826487 := bstep (se 1 (by rfl) ⟨2869865, by rfl⟩ : syracuseStep 3826487 = 5739731) B5739731
theorem B2550991 : Blo 2267435 2550991 := bstep (se 1 (by rfl) ⟨1913243, by rfl⟩ : syracuseStep 2550991 = 3826487) B3826487
theorem B3401321 : Blo 2267435 3401321 := bstep (se 2 (by rfl) ⟨1275495, by rfl⟩ : syracuseStep 3401321 = 2550991) B2550991
theorem B2267547 : Blo 2267435 2267547 := bstep (se 1 (by rfl) ⟨1700660, by rfl⟩ : syracuseStep 2267547 = 3401321) B3401321
theorem B9685813 : Blo 2267435 9685813 := bbase (se 5 (by rfl) ⟨454022, by rfl⟩ : syracuseStep 9685813 = 908045) (by norm_num)
theorem B12914417 : Blo 2267435 12914417 := bstep (se 2 (by rfl) ⟨4842906, by rfl⟩ : syracuseStep 12914417 = 9685813) B9685813
theorem B8609611 : Blo 2267435 8609611 := bstep (se 1 (by rfl) ⟨6457208, by rfl⟩ : syracuseStep 8609611 = 12914417) B12914417
theorem B11479481 : Blo 2267435 11479481 := bstep (se 2 (by rfl) ⟨4304805, by rfl⟩ : syracuseStep 11479481 = 8609611) B8609611
theorem B7652987 : Blo 2267435 7652987 := bstep (se 1 (by rfl) ⟨5739740, by rfl⟩ : syracuseStep 7652987 = 11479481) B11479481
theorem B5101991 : Blo 2267435 5101991 := bstep (se 1 (by rfl) ⟨3826493, by rfl⟩ : syracuseStep 5101991 = 7652987) B7652987
theorem B3401327 : Blo 2267435 3401327 := bstep (se 1 (by rfl) ⟨2550995, by rfl⟩ : syracuseStep 3401327 = 5101991) B5101991
theorem B2267551 : Blo 2267435 2267551 := bstep (se 1 (by rfl) ⟨1700663, by rfl⟩ : syracuseStep 2267551 = 3401327) B3401327
theorem B3401333 : Blo 2267435 3401333 := bbase (se 5 (by rfl) ⟨159437, by rfl⟩ : syracuseStep 3401333 = 318875) (by norm_num)
theorem B2267555 : Blo 2267435 2267555 := bstep (se 1 (by rfl) ⟨1700666, by rfl⟩ : syracuseStep 2267555 = 3401333) B3401333
theorem B4304821 : Blo 2267435 4304821 := bbase (se 5 (by rfl) ⟨201788, by rfl⟩ : syracuseStep 4304821 = 403577) (by norm_num)
theorem B5739761 : Blo 2267435 5739761 := bstep (se 2 (by rfl) ⟨2152410, by rfl⟩ : syracuseStep 5739761 = 4304821) B4304821
theorem B3826507 : Blo 2267435 3826507 := bstep (se 1 (by rfl) ⟨2869880, by rfl⟩ : syracuseStep 3826507 = 5739761) B5739761
theorem B5102009 : Blo 2267435 5102009 := bstep (se 2 (by rfl) ⟨1913253, by rfl⟩ : syracuseStep 5102009 = 3826507) B3826507
theorem B3401339 : Blo 2267435 3401339 := bstep (se 1 (by rfl) ⟨2551004, by rfl⟩ : syracuseStep 3401339 = 5102009) B5102009
theorem B2267559 : Blo 2267435 2267559 := bstep (se 1 (by rfl) ⟨1700669, by rfl⟩ : syracuseStep 2267559 = 3401339) B3401339
theorem B2551009 : Blo 2267435 2551009 := bbase (se 2 (by rfl) ⟨956628, by rfl⟩ : syracuseStep 2551009 = 1913257) (by norm_num)
theorem B3401345 : Blo 2267435 3401345 := bstep (se 2 (by rfl) ⟨1275504, by rfl⟩ : syracuseStep 3401345 = 2551009) B2551009
theorem B2267563 : Blo 2267435 2267563 := bstep (se 1 (by rfl) ⟨1700672, by rfl⟩ : syracuseStep 2267563 = 3401345) B3401345
theorem B5739781 : Blo 2267435 5739781 := bbase (se 4 (by rfl) ⟨538104, by rfl⟩ : syracuseStep 5739781 = 1076209) (by norm_num)
theorem B7653041 : Blo 2267435 7653041 := bstep (se 2 (by rfl) ⟨2869890, by rfl⟩ : syracuseStep 7653041 = 5739781) B5739781
theorem B5102027 : Blo 2267435 5102027 := bstep (se 1 (by rfl) ⟨3826520, by rfl⟩ : syracuseStep 5102027 = 7653041) B7653041
theorem B3401351 : Blo 2267435 3401351 := bstep (se 1 (by rfl) ⟨2551013, by rfl⟩ : syracuseStep 3401351 = 5102027) B5102027
theorem B2267567 : Blo 2267435 2267567 := bstep (se 1 (by rfl) ⟨1700675, by rfl⟩ : syracuseStep 2267567 = 3401351) B3401351
theorem B3401357 : Blo 2267435 3401357 := bbase (se 3 (by rfl) ⟨637754, by rfl⟩ : syracuseStep 3401357 = 1275509) (by norm_num)
theorem B2267571 : Blo 2267435 2267571 := bstep (se 1 (by rfl) ⟨1700678, by rfl⟩ : syracuseStep 2267571 = 3401357) B3401357
theorem B5102045 : Blo 2267435 5102045 := bbase (se 3 (by rfl) ⟨956633, by rfl⟩ : syracuseStep 5102045 = 1913267) (by norm_num)
theorem B3401363 : Blo 2267435 3401363 := bstep (se 1 (by rfl) ⟨2551022, by rfl⟩ : syracuseStep 3401363 = 5102045) B5102045
theorem B2267575 : Blo 2267435 2267575 := bstep (se 1 (by rfl) ⟨1700681, by rfl⟩ : syracuseStep 2267575 = 3401363) B3401363
theorem B3826541 : Blo 2267435 3826541 := bbase (se 3 (by rfl) ⟨717476, by rfl⟩ : syracuseStep 3826541 = 1434953) (by norm_num)
theorem B2551027 : Blo 2267435 2551027 := bstep (se 1 (by rfl) ⟨1913270, by rfl⟩ : syracuseStep 2551027 = 3826541) B3826541
theorem B3401369 : Blo 2267435 3401369 := bstep (se 2 (by rfl) ⟨1275513, by rfl⟩ : syracuseStep 3401369 = 2551027) B2551027
theorem B2267579 : Blo 2267435 2267579 := bstep (se 1 (by rfl) ⟨1700684, by rfl⟩ : syracuseStep 2267579 = 3401369) B3401369
theorem B5818133 : Blo 2267435 5818133 := bbase (se 6 (by rfl) ⟨136362, by rfl⟩ : syracuseStep 5818133 = 272725) (by norm_num)
theorem B3878755 : Blo 2267435 3878755 := bstep (se 1 (by rfl) ⟨2909066, by rfl⟩ : syracuseStep 3878755 = 5818133) B5818133
theorem B20686693 : Blo 2267435 20686693 := bstep (se 4 (by rfl) ⟨1939377, by rfl⟩ : syracuseStep 20686693 = 3878755) B3878755
theorem B27582257 : Blo 2267435 27582257 := bstep (se 2 (by rfl) ⟨10343346, by rfl⟩ : syracuseStep 27582257 = 20686693) B20686693
theorem B18388171 : Blo 2267435 18388171 := bstep (se 1 (by rfl) ⟨13791128, by rfl⟩ : syracuseStep 18388171 = 27582257) B27582257
theorem B24517561 : Blo 2267435 24517561 := bstep (se 2 (by rfl) ⟨9194085, by rfl⟩ : syracuseStep 24517561 = 18388171) B18388171
theorem B32690081 : Blo 2267435 32690081 := bstep (se 2 (by rfl) ⟨12258780, by rfl⟩ : syracuseStep 32690081 = 24517561) B24517561
theorem B21793387 : Blo 2267435 21793387 := bstep (se 1 (by rfl) ⟨16345040, by rfl⟩ : syracuseStep 21793387 = 32690081) B32690081
theorem B29057849 : Blo 2267435 29057849 := bstep (se 2 (by rfl) ⟨10896693, by rfl⟩ : syracuseStep 29057849 = 21793387) B21793387
theorem B19371899 : Blo 2267435 19371899 := bstep (se 1 (by rfl) ⟨14528924, by rfl⟩ : syracuseStep 19371899 = 29057849) B29057849
theorem B12914599 : Blo 2267435 12914599 := bstep (se 1 (by rfl) ⟨9685949, by rfl⟩ : syracuseStep 12914599 = 19371899) B19371899
theorem B17219465 : Blo 2267435 17219465 := bstep (se 2 (by rfl) ⟨6457299, by rfl⟩ : syracuseStep 17219465 = 12914599) B12914599
theorem B11479643 : Blo 2267435 11479643 := bstep (se 1 (by rfl) ⟨8609732, by rfl⟩ : syracuseStep 11479643 = 17219465) B17219465
theorem B7653095 : Blo 2267435 7653095 := bstep (se 1 (by rfl) ⟨5739821, by rfl⟩ : syracuseStep 7653095 = 11479643) B11479643
theorem B5102063 : Blo 2267435 5102063 := bstep (se 1 (by rfl) ⟨3826547, by rfl⟩ : syracuseStep 5102063 = 7653095) B7653095
theorem B3401375 : Blo 2267435 3401375 := bstep (se 1 (by rfl) ⟨2551031, by rfl⟩ : syracuseStep 3401375 = 5102063) B5102063
theorem B2267583 : Blo 2267435 2267583 := bstep (se 1 (by rfl) ⟨1700687, by rfl⟩ : syracuseStep 2267583 = 3401375) B3401375
theorem B3401381 : Blo 2267435 3401381 := bbase (se 4 (by rfl) ⟨318879, by rfl⟩ : syracuseStep 3401381 = 637759) (by norm_num)
theorem B2267587 : Blo 2267435 2267587 := bstep (se 1 (by rfl) ⟨1700690, by rfl⟩ : syracuseStep 2267587 = 3401381) B3401381
theorem B2869921 : Blo 2267435 2869921 := bbase (se 2 (by rfl) ⟨1076220, by rfl⟩ : syracuseStep 2869921 = 2152441) (by norm_num)
theorem B3826561 : Blo 2267435 3826561 := bstep (se 2 (by rfl) ⟨1434960, by rfl⟩ : syracuseStep 3826561 = 2869921) B2869921
theorem B5102081 : Blo 2267435 5102081 := bstep (se 2 (by rfl) ⟨1913280, by rfl⟩ : syracuseStep 5102081 = 3826561) B3826561
theorem B3401387 : Blo 2267435 3401387 := bstep (se 1 (by rfl) ⟨2551040, by rfl⟩ : syracuseStep 3401387 = 5102081) B5102081
theorem B2267591 : Blo 2267435 2267591 := bstep (se 1 (by rfl) ⟨1700693, by rfl⟩ : syracuseStep 2267591 = 3401387) B3401387
theorem B2551045 : Blo 2267435 2551045 := bbase (se 4 (by rfl) ⟨239160, by rfl⟩ : syracuseStep 2551045 = 478321) (by norm_num)
theorem B3401393 : Blo 2267435 3401393 := bstep (se 2 (by rfl) ⟨1275522, by rfl⟩ : syracuseStep 3401393 = 2551045) B2551045
theorem B2267595 : Blo 2267435 2267595 := bstep (se 1 (by rfl) ⟨1700696, by rfl⟩ : syracuseStep 2267595 = 3401393) B3401393
theorem B2421505 : Blo 2267435 2421505 := bbase (se 2 (by rfl) ⟨908064, by rfl⟩ : syracuseStep 2421505 = 1816129) (by norm_num)
theorem B3228673 : Blo 2267435 3228673 := bstep (se 2 (by rfl) ⟨1210752, by rfl⟩ : syracuseStep 3228673 = 2421505) B2421505
theorem B4304897 : Blo 2267435 4304897 := bstep (se 2 (by rfl) ⟨1614336, by rfl⟩ : syracuseStep 4304897 = 3228673) B3228673
theorem B2869931 : Blo 2267435 2869931 := bstep (se 1 (by rfl) ⟨2152448, by rfl⟩ : syracuseStep 2869931 = 4304897) B4304897
theorem B7653149 : Blo 2267435 7653149 := bstep (se 3 (by rfl) ⟨1434965, by rfl⟩ : syracuseStep 7653149 = 2869931) B2869931
theorem B5102099 : Blo 2267435 5102099 := bstep (se 1 (by rfl) ⟨3826574, by rfl⟩ : syracuseStep 5102099 = 7653149) B7653149
theorem B3401399 : Blo 2267435 3401399 := bstep (se 1 (by rfl) ⟨2551049, by rfl⟩ : syracuseStep 3401399 = 5102099) B5102099
theorem B2267599 : Blo 2267435 2267599 := bstep (se 1 (by rfl) ⟨1700699, by rfl⟩ : syracuseStep 2267599 = 3401399) B3401399
theorem B3401405 : Blo 2267435 3401405 := bbase (se 3 (by rfl) ⟨637763, by rfl⟩ : syracuseStep 3401405 = 1275527) (by norm_num)
theorem B2267603 : Blo 2267435 2267603 := bstep (se 1 (by rfl) ⟨1700702, by rfl⟩ : syracuseStep 2267603 = 3401405) B3401405
theorem B5102117 : Blo 2267435 5102117 := bbase (se 4 (by rfl) ⟨478323, by rfl⟩ : syracuseStep 5102117 = 956647) (by norm_num)
theorem B3401411 : Blo 2267435 3401411 := bstep (se 1 (by rfl) ⟨2551058, by rfl⟩ : syracuseStep 3401411 = 5102117) B5102117
theorem B2267607 : Blo 2267435 2267607 := bstep (se 1 (by rfl) ⟨1700705, by rfl⟩ : syracuseStep 2267607 = 3401411) B3401411
theorem B5739893 : Blo 2267435 5739893 := bbase (se 5 (by rfl) ⟨269057, by rfl⟩ : syracuseStep 5739893 = 538115) (by norm_num)
theorem B3826595 : Blo 2267435 3826595 := bstep (se 1 (by rfl) ⟨2869946, by rfl⟩ : syracuseStep 3826595 = 5739893) B5739893
theorem B2551063 : Blo 2267435 2551063 := bstep (se 1 (by rfl) ⟨1913297, by rfl⟩ : syracuseStep 2551063 = 3826595) B3826595
theorem B3401417 : Blo 2267435 3401417 := bstep (se 2 (by rfl) ⟨1275531, by rfl⟩ : syracuseStep 3401417 = 2551063) B2551063
theorem B2267611 : Blo 2267435 2267611 := bstep (se 1 (by rfl) ⟨1700708, by rfl⟩ : syracuseStep 2267611 = 3401417) B3401417
theorem B7757621 : Blo 2267435 7757621 := bbase (se 5 (by rfl) ⟨363638, by rfl⟩ : syracuseStep 7757621 = 727277) (by norm_num)
theorem B5171747 : Blo 2267435 5171747 := bstep (se 1 (by rfl) ⟨3878810, by rfl⟩ : syracuseStep 5171747 = 7757621) B7757621
theorem B13791325 : Blo 2267435 13791325 := bstep (se 3 (by rfl) ⟨2585873, by rfl⟩ : syracuseStep 13791325 = 5171747) B5171747
theorem B18388433 : Blo 2267435 18388433 := bstep (se 2 (by rfl) ⟨6895662, by rfl⟩ : syracuseStep 18388433 = 13791325) B13791325
theorem B12258955 : Blo 2267435 12258955 := bstep (se 1 (by rfl) ⟨9194216, by rfl⟩ : syracuseStep 12258955 = 18388433) B18388433
theorem B16345273 : Blo 2267435 16345273 := bstep (se 2 (by rfl) ⟨6129477, by rfl⟩ : syracuseStep 16345273 = 12258955) B12258955
theorem B21793697 : Blo 2267435 21793697 := bstep (se 2 (by rfl) ⟨8172636, by rfl⟩ : syracuseStep 21793697 = 16345273) B16345273
theorem B14529131 : Blo 2267435 14529131 := bstep (se 1 (by rfl) ⟨10896848, by rfl⟩ : syracuseStep 14529131 = 21793697) B21793697
theorem B9686087 : Blo 2267435 9686087 := bstep (se 1 (by rfl) ⟨7264565, by rfl⟩ : syracuseStep 9686087 = 14529131) B14529131
theorem B6457391 : Blo 2267435 6457391 := bstep (se 1 (by rfl) ⟨4843043, by rfl⟩ : syracuseStep 6457391 = 9686087) B9686087
theorem B4304927 : Blo 2267435 4304927 := bstep (se 1 (by rfl) ⟨3228695, by rfl⟩ : syracuseStep 4304927 = 6457391) B6457391
theorem B11479805 : Blo 2267435 11479805 := bstep (se 3 (by rfl) ⟨2152463, by rfl⟩ : syracuseStep 11479805 = 4304927) B4304927
theorem B7653203 : Blo 2267435 7653203 := bstep (se 1 (by rfl) ⟨5739902, by rfl⟩ : syracuseStep 7653203 = 11479805) B11479805
theorem B5102135 : Blo 2267435 5102135 := bstep (se 1 (by rfl) ⟨3826601, by rfl⟩ : syracuseStep 5102135 = 7653203) B7653203
theorem B3401423 : Blo 2267435 3401423 := bstep (se 1 (by rfl) ⟨2551067, by rfl⟩ : syracuseStep 3401423 = 5102135) B5102135
theorem B2267615 : Blo 2267435 2267615 := bstep (se 1 (by rfl) ⟨1700711, by rfl⟩ : syracuseStep 2267615 = 3401423) B3401423
theorem B3401429 : Blo 2267435 3401429 := bbase (se 7 (by rfl) ⟨39860, by rfl⟩ : syracuseStep 3401429 = 79721) (by norm_num)
theorem B2267619 : Blo 2267435 2267619 := bstep (se 1 (by rfl) ⟨1700714, by rfl⟩ : syracuseStep 2267619 = 3401429) B3401429
theorem B4843061 : Blo 2267435 4843061 := bbase (se 5 (by rfl) ⟨227018, by rfl⟩ : syracuseStep 4843061 = 454037) (by norm_num)
theorem B3228707 : Blo 2267435 3228707 := bstep (se 1 (by rfl) ⟨2421530, by rfl⟩ : syracuseStep 3228707 = 4843061) B4843061
theorem B8609885 : Blo 2267435 8609885 := bstep (se 3 (by rfl) ⟨1614353, by rfl⟩ : syracuseStep 8609885 = 3228707) B3228707
theorem B5739923 : Blo 2267435 5739923 := bstep (se 1 (by rfl) ⟨4304942, by rfl⟩ : syracuseStep 5739923 = 8609885) B8609885
theorem B3826615 : Blo 2267435 3826615 := bstep (se 1 (by rfl) ⟨2869961, by rfl⟩ : syracuseStep 3826615 = 5739923) B5739923
theorem B5102153 : Blo 2267435 5102153 := bstep (se 2 (by rfl) ⟨1913307, by rfl⟩ : syracuseStep 5102153 = 3826615) B3826615
theorem B3401435 : Blo 2267435 3401435 := bstep (se 1 (by rfl) ⟨2551076, by rfl⟩ : syracuseStep 3401435 = 5102153) B5102153
theorem B2267623 : Blo 2267435 2267623 := bstep (se 1 (by rfl) ⟨1700717, by rfl⟩ : syracuseStep 2267623 = 3401435) B3401435
theorem B2551081 : Blo 2267435 2551081 := bbase (se 2 (by rfl) ⟨956655, by rfl⟩ : syracuseStep 2551081 = 1913311) (by norm_num)
theorem B3401441 : Blo 2267435 3401441 := bstep (se 2 (by rfl) ⟨1275540, by rfl⟩ : syracuseStep 3401441 = 2551081) B2551081
theorem B2267627 : Blo 2267435 2267627 := bstep (se 1 (by rfl) ⟨1700720, by rfl⟩ : syracuseStep 2267627 = 3401441) B3401441
theorem B4597141 : Blo 2267435 4597141 := bbase (se 6 (by rfl) ⟨107745, by rfl⟩ : syracuseStep 4597141 = 215491) (by norm_num)
theorem B6129521 : Blo 2267435 6129521 := bstep (se 2 (by rfl) ⟨2298570, by rfl⟩ : syracuseStep 6129521 = 4597141) B4597141
theorem B4086347 : Blo 2267435 4086347 := bstep (se 1 (by rfl) ⟨3064760, by rfl⟩ : syracuseStep 4086347 = 6129521) B6129521
theorem B10896925 : Blo 2267435 10896925 := bstep (se 3 (by rfl) ⟨2043173, by rfl⟩ : syracuseStep 10896925 = 4086347) B4086347
theorem B14529233 : Blo 2267435 14529233 := bstep (se 2 (by rfl) ⟨5448462, by rfl⟩ : syracuseStep 14529233 = 10896925) B10896925
theorem B9686155 : Blo 2267435 9686155 := bstep (se 1 (by rfl) ⟨7264616, by rfl⟩ : syracuseStep 9686155 = 14529233) B14529233
theorem B12914873 : Blo 2267435 12914873 := bstep (se 2 (by rfl) ⟨4843077, by rfl⟩ : syracuseStep 12914873 = 9686155) B9686155
theorem B8609915 : Blo 2267435 8609915 := bstep (se 1 (by rfl) ⟨6457436, by rfl⟩ : syracuseStep 8609915 = 12914873) B12914873
theorem B5739943 : Blo 2267435 5739943 := bstep (se 1 (by rfl) ⟨4304957, by rfl⟩ : syracuseStep 5739943 = 8609915) B8609915
theorem B7653257 : Blo 2267435 7653257 := bstep (se 2 (by rfl) ⟨2869971, by rfl⟩ : syracuseStep 7653257 = 5739943) B5739943
theorem B5102171 : Blo 2267435 5102171 := bstep (se 1 (by rfl) ⟨3826628, by rfl⟩ : syracuseStep 5102171 = 7653257) B7653257
theorem B3401447 : Blo 2267435 3401447 := bstep (se 1 (by rfl) ⟨2551085, by rfl⟩ : syracuseStep 3401447 = 5102171) B5102171
theorem B2267631 : Blo 2267435 2267631 := bstep (se 1 (by rfl) ⟨1700723, by rfl⟩ : syracuseStep 2267631 = 3401447) B3401447
theorem B3401453 : Blo 2267435 3401453 := bbase (se 3 (by rfl) ⟨637772, by rfl⟩ : syracuseStep 3401453 = 1275545) (by norm_num)
theorem B2267635 : Blo 2267435 2267635 := bstep (se 1 (by rfl) ⟨1700726, by rfl⟩ : syracuseStep 2267635 = 3401453) B3401453
theorem B5102189 : Blo 2267435 5102189 := bbase (se 3 (by rfl) ⟨956660, by rfl⟩ : syracuseStep 5102189 = 1913321) (by norm_num)
theorem B3401459 : Blo 2267435 3401459 := bstep (se 1 (by rfl) ⟨2551094, by rfl⟩ : syracuseStep 3401459 = 5102189) B5102189
theorem B2267639 : Blo 2267435 2267639 := bstep (se 1 (by rfl) ⟨1700729, by rfl⟩ : syracuseStep 2267639 = 3401459) B3401459
theorem B4304981 : Blo 2267435 4304981 := bbase (se 8 (by rfl) ⟨25224, by rfl⟩ : syracuseStep 4304981 = 50449) (by norm_num)
theorem B2869987 : Blo 2267435 2869987 := bstep (se 1 (by rfl) ⟨2152490, by rfl⟩ : syracuseStep 2869987 = 4304981) B4304981
theorem B3826649 : Blo 2267435 3826649 := bstep (se 2 (by rfl) ⟨1434993, by rfl⟩ : syracuseStep 3826649 = 2869987) B2869987
theorem B2551099 : Blo 2267435 2551099 := bstep (se 1 (by rfl) ⟨1913324, by rfl⟩ : syracuseStep 2551099 = 3826649) B3826649
theorem B3401465 : Blo 2267435 3401465 := bstep (se 2 (by rfl) ⟨1275549, by rfl⟩ : syracuseStep 3401465 = 2551099) B2551099
theorem B2267643 : Blo 2267435 2267643 := bstep (se 1 (by rfl) ⟨1700732, by rfl⟩ : syracuseStep 2267643 = 3401465) B3401465
theorem B4909189 : Blo 2267435 4909189 := bbase (se 4 (by rfl) ⟨460236, by rfl⟩ : syracuseStep 4909189 = 920473) (by norm_num)
theorem B6545585 : Blo 2267435 6545585 := bstep (se 2 (by rfl) ⟨2454594, by rfl⟩ : syracuseStep 6545585 = 4909189) B4909189
theorem B4363723 : Blo 2267435 4363723 := bstep (se 1 (by rfl) ⟨3272792, by rfl⟩ : syracuseStep 4363723 = 6545585) B6545585
theorem B23273189 : Blo 2267435 23273189 := bstep (se 4 (by rfl) ⟨2181861, by rfl⟩ : syracuseStep 23273189 = 4363723) B4363723
theorem B15515459 : Blo 2267435 15515459 := bstep (se 1 (by rfl) ⟨11636594, by rfl⟩ : syracuseStep 15515459 = 23273189) B23273189
theorem B10343639 : Blo 2267435 10343639 := bstep (se 1 (by rfl) ⟨7757729, by rfl⟩ : syracuseStep 10343639 = 15515459) B15515459
theorem B6895759 : Blo 2267435 6895759 := bstep (se 1 (by rfl) ⟨5171819, by rfl⟩ : syracuseStep 6895759 = 10343639) B10343639
theorem B9194345 : Blo 2267435 9194345 := bstep (se 2 (by rfl) ⟨3447879, by rfl⟩ : syracuseStep 9194345 = 6895759) B6895759
theorem B6129563 : Blo 2267435 6129563 := bstep (se 1 (by rfl) ⟨4597172, by rfl⟩ : syracuseStep 6129563 = 9194345) B9194345
theorem B65382005 : Blo 2267435 65382005 := bstep (se 5 (by rfl) ⟨3064781, by rfl⟩ : syracuseStep 65382005 = 6129563) B6129563
theorem B43588003 : Blo 2267435 43588003 := bstep (se 1 (by rfl) ⟨32691002, by rfl⟩ : syracuseStep 43588003 = 65382005) B65382005
theorem B58117337 : Blo 2267435 58117337 := bstep (se 2 (by rfl) ⟨21794001, by rfl⟩ : syracuseStep 58117337 = 43588003) B43588003
theorem B38744891 : Blo 2267435 38744891 := bstep (se 1 (by rfl) ⟨29058668, by rfl⟩ : syracuseStep 38744891 = 58117337) B58117337
theorem B25829927 : Blo 2267435 25829927 := bstep (se 1 (by rfl) ⟨19372445, by rfl⟩ : syracuseStep 25829927 = 38744891) B38744891
theorem B17219951 : Blo 2267435 17219951 := bstep (se 1 (by rfl) ⟨12914963, by rfl⟩ : syracuseStep 17219951 = 25829927) B25829927
theorem B11479967 : Blo 2267435 11479967 := bstep (se 1 (by rfl) ⟨8609975, by rfl⟩ : syracuseStep 11479967 = 17219951) B17219951
theorem B7653311 : Blo 2267435 7653311 := bstep (se 1 (by rfl) ⟨5739983, by rfl⟩ : syracuseStep 7653311 = 11479967) B11479967
theorem B5102207 : Blo 2267435 5102207 := bstep (se 1 (by rfl) ⟨3826655, by rfl⟩ : syracuseStep 5102207 = 7653311) B7653311
theorem B3401471 : Blo 2267435 3401471 := bstep (se 1 (by rfl) ⟨2551103, by rfl⟩ : syracuseStep 3401471 = 5102207) B5102207
theorem B2267647 : Blo 2267435 2267647 := bstep (se 1 (by rfl) ⟨1700735, by rfl⟩ : syracuseStep 2267647 = 3401471) B3401471
theorem B3401477 : Blo 2267435 3401477 := bbase (se 4 (by rfl) ⟨318888, by rfl⟩ : syracuseStep 3401477 = 637777) (by norm_num)
theorem B2267651 : Blo 2267435 2267651 := bstep (se 1 (by rfl) ⟨1700738, by rfl⟩ : syracuseStep 2267651 = 3401477) B3401477
theorem B3826669 : Blo 2267435 3826669 := bbase (se 3 (by rfl) ⟨717500, by rfl⟩ : syracuseStep 3826669 = 1435001) (by norm_num)
theorem B5102225 : Blo 2267435 5102225 := bstep (se 2 (by rfl) ⟨1913334, by rfl⟩ : syracuseStep 5102225 = 3826669) B3826669
theorem B3401483 : Blo 2267435 3401483 := bstep (se 1 (by rfl) ⟨2551112, by rfl⟩ : syracuseStep 3401483 = 5102225) B5102225
theorem B2267655 : Blo 2267435 2267655 := bstep (se 1 (by rfl) ⟨1700741, by rfl⟩ : syracuseStep 2267655 = 3401483) B3401483
theorem B2551117 : Blo 2267435 2551117 := bbase (se 3 (by rfl) ⟨478334, by rfl⟩ : syracuseStep 2551117 = 956669) (by norm_num)
theorem B3401489 : Blo 2267435 3401489 := bstep (se 2 (by rfl) ⟨1275558, by rfl⟩ : syracuseStep 3401489 = 2551117) B2551117
theorem B2267659 : Blo 2267435 2267659 := bstep (se 1 (by rfl) ⟨1700744, by rfl⟩ : syracuseStep 2267659 = 3401489) B3401489
theorem B7653365 : Blo 2267435 7653365 := bbase (se 5 (by rfl) ⟨358751, by rfl⟩ : syracuseStep 7653365 = 717503) (by norm_num)
theorem B5102243 : Blo 2267435 5102243 := bstep (se 1 (by rfl) ⟨3826682, by rfl⟩ : syracuseStep 5102243 = 7653365) B7653365
theorem B3401495 : Blo 2267435 3401495 := bstep (se 1 (by rfl) ⟨2551121, by rfl⟩ : syracuseStep 3401495 = 5102243) B5102243
theorem B2267663 : Blo 2267435 2267663 := bstep (se 1 (by rfl) ⟨1700747, by rfl⟩ : syracuseStep 2267663 = 3401495) B3401495
theorem B3401501 : Blo 2267435 3401501 := bbase (se 3 (by rfl) ⟨637781, by rfl⟩ : syracuseStep 3401501 = 1275563) (by norm_num)
theorem B2267667 : Blo 2267435 2267667 := bstep (se 1 (by rfl) ⟨1700750, by rfl⟩ : syracuseStep 2267667 = 3401501) B3401501
theorem B5102261 : Blo 2267435 5102261 := bbase (se 5 (by rfl) ⟨239168, by rfl⟩ : syracuseStep 5102261 = 478337) (by norm_num)
theorem B3401507 : Blo 2267435 3401507 := bstep (se 1 (by rfl) ⟨2551130, by rfl⟩ : syracuseStep 3401507 = 5102261) B5102261
theorem B2267671 : Blo 2267435 2267671 := bstep (se 1 (by rfl) ⟨1700753, by rfl⟩ : syracuseStep 2267671 = 3401507) B3401507
theorem B12915125 : Blo 2267435 12915125 := bbase (se 5 (by rfl) ⟨605396, by rfl⟩ : syracuseStep 12915125 = 1210793) (by norm_num)
theorem B8610083 : Blo 2267435 8610083 := bstep (se 1 (by rfl) ⟨6457562, by rfl⟩ : syracuseStep 8610083 = 12915125) B12915125
theorem B5740055 : Blo 2267435 5740055 := bstep (se 1 (by rfl) ⟨4305041, by rfl⟩ : syracuseStep 5740055 = 8610083) B8610083
theorem B3826703 : Blo 2267435 3826703 := bstep (se 1 (by rfl) ⟨2870027, by rfl⟩ : syracuseStep 3826703 = 5740055) B5740055
theorem B2551135 : Blo 2267435 2551135 := bstep (se 1 (by rfl) ⟨1913351, by rfl⟩ : syracuseStep 2551135 = 3826703) B3826703
theorem B3401513 : Blo 2267435 3401513 := bstep (se 2 (by rfl) ⟨1275567, by rfl⟩ : syracuseStep 3401513 = 2551135) B2551135
theorem B2267675 : Blo 2267435 2267675 := bstep (se 1 (by rfl) ⟨1700756, by rfl⟩ : syracuseStep 2267675 = 3401513) B3401513
theorem B6457573 : Blo 2267435 6457573 := bbase (se 4 (by rfl) ⟨605397, by rfl⟩ : syracuseStep 6457573 = 1210795) (by norm_num)
theorem B8610097 : Blo 2267435 8610097 := bstep (se 2 (by rfl) ⟨3228786, by rfl⟩ : syracuseStep 8610097 = 6457573) B6457573
theorem B11480129 : Blo 2267435 11480129 := bstep (se 2 (by rfl) ⟨4305048, by rfl⟩ : syracuseStep 11480129 = 8610097) B8610097
theorem B7653419 : Blo 2267435 7653419 := bstep (se 1 (by rfl) ⟨5740064, by rfl⟩ : syracuseStep 7653419 = 11480129) B11480129
theorem B5102279 : Blo 2267435 5102279 := bstep (se 1 (by rfl) ⟨3826709, by rfl⟩ : syracuseStep 5102279 = 7653419) B7653419
theorem B3401519 : Blo 2267435 3401519 := bstep (se 1 (by rfl) ⟨2551139, by rfl⟩ : syracuseStep 3401519 = 5102279) B5102279
theorem B2267679 : Blo 2267435 2267679 := bstep (se 1 (by rfl) ⟨1700759, by rfl⟩ : syracuseStep 2267679 = 3401519) B3401519
theorem B3401525 : Blo 2267435 3401525 := bbase (se 5 (by rfl) ⟨159446, by rfl⟩ : syracuseStep 3401525 = 318893) (by norm_num)
theorem B2267683 : Blo 2267435 2267683 := bstep (se 1 (by rfl) ⟨1700762, by rfl⟩ : syracuseStep 2267683 = 3401525) B3401525
theorem B5740085 : Blo 2267435 5740085 := bbase (se 5 (by rfl) ⟨269066, by rfl⟩ : syracuseStep 5740085 = 538133) (by norm_num)
theorem B3826723 : Blo 2267435 3826723 := bstep (se 1 (by rfl) ⟨2870042, by rfl⟩ : syracuseStep 3826723 = 5740085) B5740085
theorem B5102297 : Blo 2267435 5102297 := bstep (se 2 (by rfl) ⟨1913361, by rfl⟩ : syracuseStep 5102297 = 3826723) B3826723
theorem B3401531 : Blo 2267435 3401531 := bstep (se 1 (by rfl) ⟨2551148, by rfl⟩ : syracuseStep 3401531 = 5102297) B5102297
theorem B2267687 : Blo 2267435 2267687 := bstep (se 1 (by rfl) ⟨1700765, by rfl⟩ : syracuseStep 2267687 = 3401531) B3401531
theorem B2551153 : Blo 2267435 2551153 := bbase (se 2 (by rfl) ⟨956682, by rfl⟩ : syracuseStep 2551153 = 1913365) (by norm_num)
theorem B3401537 : Blo 2267435 3401537 := bstep (se 2 (by rfl) ⟨1275576, by rfl⟩ : syracuseStep 3401537 = 2551153) B2551153
theorem B2267691 : Blo 2267435 2267691 := bstep (se 1 (by rfl) ⟨1700768, by rfl⟩ : syracuseStep 2267691 = 3401537) B3401537
theorem B5522957 : Blo 2267435 5522957 := bbase (se 3 (by rfl) ⟨1035554, by rfl⟩ : syracuseStep 5522957 = 2071109) (by norm_num)
theorem B3681971 : Blo 2267435 3681971 := bstep (se 1 (by rfl) ⟨2761478, by rfl⟩ : syracuseStep 3681971 = 5522957) B5522957
theorem B2454647 : Blo 2267435 2454647 := bstep (se 1 (by rfl) ⟨1840985, by rfl⟩ : syracuseStep 2454647 = 3681971) B3681971
theorem B26182901 : Blo 2267435 26182901 := bstep (se 5 (by rfl) ⟨1227323, by rfl⟩ : syracuseStep 26182901 = 2454647) B2454647
theorem B17455267 : Blo 2267435 17455267 := bstep (se 1 (by rfl) ⟨13091450, by rfl⟩ : syracuseStep 17455267 = 26182901) B26182901
theorem B23273689 : Blo 2267435 23273689 := bstep (se 2 (by rfl) ⟨8727633, by rfl⟩ : syracuseStep 23273689 = 17455267) B17455267
theorem B31031585 : Blo 2267435 31031585 := bstep (se 2 (by rfl) ⟨11636844, by rfl⟩ : syracuseStep 31031585 = 23273689) B23273689
theorem B20687723 : Blo 2267435 20687723 := bstep (se 1 (by rfl) ⟨15515792, by rfl⟩ : syracuseStep 20687723 = 31031585) B31031585
theorem B13791815 : Blo 2267435 13791815 := bstep (se 1 (by rfl) ⟨10343861, by rfl⟩ : syracuseStep 13791815 = 20687723) B20687723
theorem B9194543 : Blo 2267435 9194543 := bstep (se 1 (by rfl) ⟨6895907, by rfl⟩ : syracuseStep 9194543 = 13791815) B13791815
theorem B6129695 : Blo 2267435 6129695 := bstep (se 1 (by rfl) ⟨4597271, by rfl⟩ : syracuseStep 6129695 = 9194543) B9194543
theorem B4086463 : Blo 2267435 4086463 := bstep (se 1 (by rfl) ⟨3064847, by rfl⟩ : syracuseStep 4086463 = 6129695) B6129695
theorem B5448617 : Blo 2267435 5448617 := bstep (se 2 (by rfl) ⟨2043231, by rfl⟩ : syracuseStep 5448617 = 4086463) B4086463
theorem B3632411 : Blo 2267435 3632411 := bstep (se 1 (by rfl) ⟨2724308, by rfl⟩ : syracuseStep 3632411 = 5448617) B5448617
theorem B9686429 : Blo 2267435 9686429 := bstep (se 3 (by rfl) ⟨1816205, by rfl⟩ : syracuseStep 9686429 = 3632411) B3632411
theorem B6457619 : Blo 2267435 6457619 := bstep (se 1 (by rfl) ⟨4843214, by rfl⟩ : syracuseStep 6457619 = 9686429) B9686429
theorem B4305079 : Blo 2267435 4305079 := bstep (se 1 (by rfl) ⟨3228809, by rfl⟩ : syracuseStep 4305079 = 6457619) B6457619
theorem B5740105 : Blo 2267435 5740105 := bstep (se 2 (by rfl) ⟨2152539, by rfl⟩ : syracuseStep 5740105 = 4305079) B4305079
theorem B7653473 : Blo 2267435 7653473 := bstep (se 2 (by rfl) ⟨2870052, by rfl⟩ : syracuseStep 7653473 = 5740105) B5740105
theorem B5102315 : Blo 2267435 5102315 := bstep (se 1 (by rfl) ⟨3826736, by rfl⟩ : syracuseStep 5102315 = 7653473) B7653473
theorem B3401543 : Blo 2267435 3401543 := bstep (se 1 (by rfl) ⟨2551157, by rfl⟩ : syracuseStep 3401543 = 5102315) B5102315
theorem B2267695 : Blo 2267435 2267695 := bstep (se 1 (by rfl) ⟨1700771, by rfl⟩ : syracuseStep 2267695 = 3401543) B3401543
theorem B3401549 : Blo 2267435 3401549 := bbase (se 3 (by rfl) ⟨637790, by rfl⟩ : syracuseStep 3401549 = 1275581) (by norm_num)
theorem B2267699 : Blo 2267435 2267699 := bstep (se 1 (by rfl) ⟨1700774, by rfl⟩ : syracuseStep 2267699 = 3401549) B3401549
theorem B5102333 : Blo 2267435 5102333 := bbase (se 3 (by rfl) ⟨956687, by rfl⟩ : syracuseStep 5102333 = 1913375) (by norm_num)
theorem B3401555 : Blo 2267435 3401555 := bstep (se 1 (by rfl) ⟨2551166, by rfl⟩ : syracuseStep 3401555 = 5102333) B5102333
theorem B2267703 : Blo 2267435 2267703 := bstep (se 1 (by rfl) ⟨1700777, by rfl⟩ : syracuseStep 2267703 = 3401555) B3401555
theorem B3826757 : Blo 2267435 3826757 := bbase (se 4 (by rfl) ⟨358758, by rfl⟩ : syracuseStep 3826757 = 717517) (by norm_num)
theorem B2551171 : Blo 2267435 2551171 := bstep (se 1 (by rfl) ⟨1913378, by rfl⟩ : syracuseStep 2551171 = 3826757) B3826757
theorem B3401561 : Blo 2267435 3401561 := bstep (se 2 (by rfl) ⟨1275585, by rfl⟩ : syracuseStep 3401561 = 2551171) B2551171
theorem B2267707 : Blo 2267435 2267707 := bstep (se 1 (by rfl) ⟨1700780, by rfl⟩ : syracuseStep 2267707 = 3401561) B3401561
theorem B17220437 : Blo 2267435 17220437 := bbase (se 9 (by rfl) ⟨50450, by rfl⟩ : syracuseStep 17220437 = 100901) (by norm_num)
theorem B11480291 : Blo 2267435 11480291 := bstep (se 1 (by rfl) ⟨8610218, by rfl⟩ : syracuseStep 11480291 = 17220437) B17220437
theorem B7653527 : Blo 2267435 7653527 := bstep (se 1 (by rfl) ⟨5740145, by rfl⟩ : syracuseStep 7653527 = 11480291) B11480291
theorem B5102351 : Blo 2267435 5102351 := bstep (se 1 (by rfl) ⟨3826763, by rfl⟩ : syracuseStep 5102351 = 7653527) B7653527
theorem B3401567 : Blo 2267435 3401567 := bstep (se 1 (by rfl) ⟨2551175, by rfl⟩ : syracuseStep 3401567 = 5102351) B5102351
theorem B2267711 : Blo 2267435 2267711 := bstep (se 1 (by rfl) ⟨1700783, by rfl⟩ : syracuseStep 2267711 = 3401567) B3401567
theorem B3401573 : Blo 2267435 3401573 := bbase (se 4 (by rfl) ⟨318897, by rfl⟩ : syracuseStep 3401573 = 637795) (by norm_num)
theorem B2267715 : Blo 2267435 2267715 := bstep (se 1 (by rfl) ⟨1700786, by rfl⟩ : syracuseStep 2267715 = 3401573) B3401573
theorem B4305125 : Blo 2267435 4305125 := bbase (se 4 (by rfl) ⟨403605, by rfl⟩ : syracuseStep 4305125 = 807211) (by norm_num)
theorem B2870083 : Blo 2267435 2870083 := bstep (se 1 (by rfl) ⟨2152562, by rfl⟩ : syracuseStep 2870083 = 4305125) B4305125
theorem B3826777 : Blo 2267435 3826777 := bstep (se 2 (by rfl) ⟨1435041, by rfl⟩ : syracuseStep 3826777 = 2870083) B2870083
theorem B5102369 : Blo 2267435 5102369 := bstep (se 2 (by rfl) ⟨1913388, by rfl⟩ : syracuseStep 5102369 = 3826777) B3826777
theorem B3401579 : Blo 2267435 3401579 := bstep (se 1 (by rfl) ⟨2551184, by rfl⟩ : syracuseStep 3401579 = 5102369) B5102369
theorem B2267719 : Blo 2267435 2267719 := bstep (se 1 (by rfl) ⟨1700789, by rfl⟩ : syracuseStep 2267719 = 3401579) B3401579
theorem B2551189 : Blo 2267435 2551189 := bbase (se 6 (by rfl) ⟨59793, by rfl⟩ : syracuseStep 2551189 = 119587) (by norm_num)
theorem B3401585 : Blo 2267435 3401585 := bstep (se 2 (by rfl) ⟨1275594, by rfl⟩ : syracuseStep 3401585 = 2551189) B2551189
theorem B2267723 : Blo 2267435 2267723 := bstep (se 1 (by rfl) ⟨1700792, by rfl⟩ : syracuseStep 2267723 = 3401585) B3401585
theorem B2870093 : Blo 2267435 2870093 := bbase (se 3 (by rfl) ⟨538142, by rfl⟩ : syracuseStep 2870093 = 1076285) (by norm_num)
theorem B7653581 : Blo 2267435 7653581 := bstep (se 3 (by rfl) ⟨1435046, by rfl⟩ : syracuseStep 7653581 = 2870093) B2870093
theorem B5102387 : Blo 2267435 5102387 := bstep (se 1 (by rfl) ⟨3826790, by rfl⟩ : syracuseStep 5102387 = 7653581) B7653581
theorem B3401591 : Blo 2267435 3401591 := bstep (se 1 (by rfl) ⟨2551193, by rfl⟩ : syracuseStep 3401591 = 5102387) B5102387
theorem B2267727 : Blo 2267435 2267727 := bstep (se 1 (by rfl) ⟨1700795, by rfl⟩ : syracuseStep 2267727 = 3401591) B3401591
theorem B3401597 : Blo 2267435 3401597 := bbase (se 3 (by rfl) ⟨637799, by rfl⟩ : syracuseStep 3401597 = 1275599) (by norm_num)
theorem B2267731 : Blo 2267435 2267731 := bstep (se 1 (by rfl) ⟨1700798, by rfl⟩ : syracuseStep 2267731 = 3401597) B3401597
theorem B5102405 : Blo 2267435 5102405 := bbase (se 4 (by rfl) ⟨478350, by rfl⟩ : syracuseStep 5102405 = 956701) (by norm_num)
theorem B3401603 : Blo 2267435 3401603 := bstep (se 1 (by rfl) ⟨2551202, by rfl⟩ : syracuseStep 3401603 = 5102405) B5102405
theorem B2267735 : Blo 2267435 2267735 := bstep (se 1 (by rfl) ⟨1700801, by rfl⟩ : syracuseStep 2267735 = 3401603) B3401603
theorem B4843309 : Blo 2267435 4843309 := bbase (se 3 (by rfl) ⟨908120, by rfl⟩ : syracuseStep 4843309 = 1816241) (by norm_num)
theorem B6457745 : Blo 2267435 6457745 := bstep (se 2 (by rfl) ⟨2421654, by rfl⟩ : syracuseStep 6457745 = 4843309) B4843309
theorem B4305163 : Blo 2267435 4305163 := bstep (se 1 (by rfl) ⟨3228872, by rfl⟩ : syracuseStep 4305163 = 6457745) B6457745
theorem B5740217 : Blo 2267435 5740217 := bstep (se 2 (by rfl) ⟨2152581, by rfl⟩ : syracuseStep 5740217 = 4305163) B4305163
theorem B3826811 : Blo 2267435 3826811 := bstep (se 1 (by rfl) ⟨2870108, by rfl⟩ : syracuseStep 3826811 = 5740217) B5740217
theorem B2551207 : Blo 2267435 2551207 := bstep (se 1 (by rfl) ⟨1913405, by rfl⟩ : syracuseStep 2551207 = 3826811) B3826811
theorem B3401609 : Blo 2267435 3401609 := bstep (se 2 (by rfl) ⟨1275603, by rfl⟩ : syracuseStep 3401609 = 2551207) B2551207
theorem B2267739 : Blo 2267435 2267739 := bstep (se 1 (by rfl) ⟨1700804, by rfl⟩ : syracuseStep 2267739 = 3401609) B3401609
theorem B11480453 : Blo 2267435 11480453 := bbase (se 4 (by rfl) ⟨1076292, by rfl⟩ : syracuseStep 11480453 = 2152585) (by norm_num)
theorem B7653635 : Blo 2267435 7653635 := bstep (se 1 (by rfl) ⟨5740226, by rfl⟩ : syracuseStep 7653635 = 11480453) B11480453
theorem B5102423 : Blo 2267435 5102423 := bstep (se 1 (by rfl) ⟨3826817, by rfl⟩ : syracuseStep 5102423 = 7653635) B7653635
theorem B3401615 : Blo 2267435 3401615 := bstep (se 1 (by rfl) ⟨2551211, by rfl⟩ : syracuseStep 3401615 = 5102423) B5102423
theorem B2267743 : Blo 2267435 2267743 := bstep (se 1 (by rfl) ⟨1700807, by rfl⟩ : syracuseStep 2267743 = 3401615) B3401615
theorem B3401621 : Blo 2267435 3401621 := bbase (se 6 (by rfl) ⟨79725, by rfl⟩ : syracuseStep 3401621 = 159451) (by norm_num)
theorem B2267747 : Blo 2267435 2267747 := bstep (se 1 (by rfl) ⟨1700810, by rfl⟩ : syracuseStep 2267747 = 3401621) B3401621
theorem B3632501 : Blo 2267435 3632501 := bbase (se 5 (by rfl) ⟨170273, by rfl⟩ : syracuseStep 3632501 = 340547) (by norm_num)
theorem B2421667 : Blo 2267435 2421667 := bstep (se 1 (by rfl) ⟨1816250, by rfl⟩ : syracuseStep 2421667 = 3632501) B3632501
theorem B12915557 : Blo 2267435 12915557 := bstep (se 4 (by rfl) ⟨1210833, by rfl⟩ : syracuseStep 12915557 = 2421667) B2421667
theorem B8610371 : Blo 2267435 8610371 := bstep (se 1 (by rfl) ⟨6457778, by rfl⟩ : syracuseStep 8610371 = 12915557) B12915557
theorem B5740247 : Blo 2267435 5740247 := bstep (se 1 (by rfl) ⟨4305185, by rfl⟩ : syracuseStep 5740247 = 8610371) B8610371
theorem B3826831 : Blo 2267435 3826831 := bstep (se 1 (by rfl) ⟨2870123, by rfl⟩ : syracuseStep 3826831 = 5740247) B5740247
theorem B5102441 : Blo 2267435 5102441 := bstep (se 2 (by rfl) ⟨1913415, by rfl⟩ : syracuseStep 5102441 = 3826831) B3826831
theorem B3401627 : Blo 2267435 3401627 := bstep (se 1 (by rfl) ⟨2551220, by rfl⟩ : syracuseStep 3401627 = 5102441) B5102441
theorem B2267751 : Blo 2267435 2267751 := bstep (se 1 (by rfl) ⟨1700813, by rfl⟩ : syracuseStep 2267751 = 3401627) B3401627
theorem B2551225 : Blo 2267435 2551225 := bbase (se 2 (by rfl) ⟨956709, by rfl⟩ : syracuseStep 2551225 = 1913419) (by norm_num)
theorem B3401633 : Blo 2267435 3401633 := bstep (se 2 (by rfl) ⟨1275612, by rfl⟩ : syracuseStep 3401633 = 2551225) B2551225
theorem B2267755 : Blo 2267435 2267755 := bstep (se 1 (by rfl) ⟨1700816, by rfl⟩ : syracuseStep 2267755 = 3401633) B3401633
theorem B10897541 : Blo 2267435 10897541 := bbase (se 4 (by rfl) ⟨1021644, by rfl⟩ : syracuseStep 10897541 = 2043289) (by norm_num)
theorem B7265027 : Blo 2267435 7265027 := bstep (se 1 (by rfl) ⟨5448770, by rfl⟩ : syracuseStep 7265027 = 10897541) B10897541
theorem B4843351 : Blo 2267435 4843351 := bstep (se 1 (by rfl) ⟨3632513, by rfl⟩ : syracuseStep 4843351 = 7265027) B7265027
theorem B6457801 : Blo 2267435 6457801 := bstep (se 2 (by rfl) ⟨2421675, by rfl⟩ : syracuseStep 6457801 = 4843351) B4843351
theorem B8610401 : Blo 2267435 8610401 := bstep (se 2 (by rfl) ⟨3228900, by rfl⟩ : syracuseStep 8610401 = 6457801) B6457801
theorem B5740267 : Blo 2267435 5740267 := bstep (se 1 (by rfl) ⟨4305200, by rfl⟩ : syracuseStep 5740267 = 8610401) B8610401
theorem B7653689 : Blo 2267435 7653689 := bstep (se 2 (by rfl) ⟨2870133, by rfl⟩ : syracuseStep 7653689 = 5740267) B5740267
theorem B5102459 : Blo 2267435 5102459 := bstep (se 1 (by rfl) ⟨3826844, by rfl⟩ : syracuseStep 5102459 = 7653689) B7653689
theorem B3401639 : Blo 2267435 3401639 := bstep (se 1 (by rfl) ⟨2551229, by rfl⟩ : syracuseStep 3401639 = 5102459) B5102459
theorem B2267759 : Blo 2267435 2267759 := bstep (se 1 (by rfl) ⟨1700819, by rfl⟩ : syracuseStep 2267759 = 3401639) B3401639
theorem B3401645 : Blo 2267435 3401645 := bbase (se 3 (by rfl) ⟨637808, by rfl⟩ : syracuseStep 3401645 = 1275617) (by norm_num)
theorem B2267763 : Blo 2267435 2267763 := bstep (se 1 (by rfl) ⟨1700822, by rfl⟩ : syracuseStep 2267763 = 3401645) B3401645
theorem B5102477 : Blo 2267435 5102477 := bbase (se 3 (by rfl) ⟨956714, by rfl⟩ : syracuseStep 5102477 = 1913429) (by norm_num)
theorem B3401651 : Blo 2267435 3401651 := bstep (se 1 (by rfl) ⟨2551238, by rfl⟩ : syracuseStep 3401651 = 5102477) B5102477
theorem B2267767 : Blo 2267435 2267767 := bstep (se 1 (by rfl) ⟨1700825, by rfl⟩ : syracuseStep 2267767 = 3401651) B3401651
theorem B2870149 : Blo 2267435 2870149 := bbase (se 4 (by rfl) ⟨269076, by rfl⟩ : syracuseStep 2870149 = 538153) (by norm_num)
theorem B3826865 : Blo 2267435 3826865 := bstep (se 2 (by rfl) ⟨1435074, by rfl⟩ : syracuseStep 3826865 = 2870149) B2870149
theorem B2551243 : Blo 2267435 2551243 := bstep (se 1 (by rfl) ⟨1913432, by rfl⟩ : syracuseStep 2551243 = 3826865) B3826865
theorem B3401657 : Blo 2267435 3401657 := bstep (se 2 (by rfl) ⟨1275621, by rfl⟩ : syracuseStep 3401657 = 2551243) B2551243
theorem B2267771 : Blo 2267435 2267771 := bstep (se 1 (by rfl) ⟨1700828, by rfl⟩ : syracuseStep 2267771 = 3401657) B3401657
theorem B29060309 : Blo 2267435 29060309 := bbase (se 7 (by rfl) ⟨340550, by rfl⟩ : syracuseStep 29060309 = 681101) (by norm_num)
theorem B19373539 : Blo 2267435 19373539 := bstep (se 1 (by rfl) ⟨14530154, by rfl⟩ : syracuseStep 19373539 = 29060309) B29060309
theorem B25831385 : Blo 2267435 25831385 := bstep (se 2 (by rfl) ⟨9686769, by rfl⟩ : syracuseStep 25831385 = 19373539) B19373539
theorem B17220923 : Blo 2267435 17220923 := bstep (se 1 (by rfl) ⟨12915692, by rfl⟩ : syracuseStep 17220923 = 25831385) B25831385
theorem B11480615 : Blo 2267435 11480615 := bstep (se 1 (by rfl) ⟨8610461, by rfl⟩ : syracuseStep 11480615 = 17220923) B17220923
theorem B7653743 : Blo 2267435 7653743 := bstep (se 1 (by rfl) ⟨5740307, by rfl⟩ : syracuseStep 7653743 = 11480615) B11480615
theorem B5102495 : Blo 2267435 5102495 := bstep (se 1 (by rfl) ⟨3826871, by rfl⟩ : syracuseStep 5102495 = 7653743) B7653743
theorem B3401663 : Blo 2267435 3401663 := bstep (se 1 (by rfl) ⟨2551247, by rfl⟩ : syracuseStep 3401663 = 5102495) B5102495
theorem B2267775 : Blo 2267435 2267775 := bstep (se 1 (by rfl) ⟨1700831, by rfl⟩ : syracuseStep 2267775 = 3401663) B3401663
theorem B3401669 : Blo 2267435 3401669 := bbase (se 4 (by rfl) ⟨318906, by rfl⟩ : syracuseStep 3401669 = 637813) (by norm_num)
theorem B2267779 : Blo 2267435 2267779 := bstep (se 1 (by rfl) ⟨1700834, by rfl⟩ : syracuseStep 2267779 = 3401669) B3401669
theorem B3826885 : Blo 2267435 3826885 := bbase (se 4 (by rfl) ⟨358770, by rfl⟩ : syracuseStep 3826885 = 717541) (by norm_num)
theorem B5102513 : Blo 2267435 5102513 := bstep (se 2 (by rfl) ⟨1913442, by rfl⟩ : syracuseStep 5102513 = 3826885) B3826885
theorem B3401675 : Blo 2267435 3401675 := bstep (se 1 (by rfl) ⟨2551256, by rfl⟩ : syracuseStep 3401675 = 5102513) B5102513
theorem B2267783 : Blo 2267435 2267783 := bstep (se 1 (by rfl) ⟨1700837, by rfl⟩ : syracuseStep 2267783 = 3401675) B3401675
theorem B2551261 : Blo 2267435 2551261 := bbase (se 3 (by rfl) ⟨478361, by rfl⟩ : syracuseStep 2551261 = 956723) (by norm_num)
theorem B3401681 : Blo 2267435 3401681 := bstep (se 2 (by rfl) ⟨1275630, by rfl⟩ : syracuseStep 3401681 = 2551261) B2551261
theorem B2267787 : Blo 2267435 2267787 := bstep (se 1 (by rfl) ⟨1700840, by rfl⟩ : syracuseStep 2267787 = 3401681) B3401681
theorem B7653797 : Blo 2267435 7653797 := bbase (se 4 (by rfl) ⟨717543, by rfl⟩ : syracuseStep 7653797 = 1435087) (by norm_num)
theorem B5102531 : Blo 2267435 5102531 := bstep (se 1 (by rfl) ⟨3826898, by rfl⟩ : syracuseStep 5102531 = 7653797) B7653797
theorem B3401687 : Blo 2267435 3401687 := bstep (se 1 (by rfl) ⟨2551265, by rfl⟩ : syracuseStep 3401687 = 5102531) B5102531
theorem B2267791 : Blo 2267435 2267791 := bstep (se 1 (by rfl) ⟨1700843, by rfl⟩ : syracuseStep 2267791 = 3401687) B3401687
theorem B3401693 : Blo 2267435 3401693 := bbase (se 3 (by rfl) ⟨637817, by rfl⟩ : syracuseStep 3401693 = 1275635) (by norm_num)
theorem B2267795 : Blo 2267435 2267795 := bstep (se 1 (by rfl) ⟨1700846, by rfl⟩ : syracuseStep 2267795 = 3401693) B3401693
theorem B5102549 : Blo 2267435 5102549 := bbase (se 7 (by rfl) ⟨59795, by rfl⟩ : syracuseStep 5102549 = 119591) (by norm_num)
theorem B3401699 : Blo 2267435 3401699 := bstep (se 1 (by rfl) ⟨2551274, by rfl⟩ : syracuseStep 3401699 = 5102549) B5102549
theorem B2267799 : Blo 2267435 2267799 := bstep (se 1 (by rfl) ⟨1700849, by rfl⟩ : syracuseStep 2267799 = 3401699) B3401699
theorem B2298745 : Blo 2267435 2298745 := bbase (se 2 (by rfl) ⟨862029, by rfl⟩ : syracuseStep 2298745 = 1724059) (by norm_num)
theorem B12259973 : Blo 2267435 12259973 := bstep (se 4 (by rfl) ⟨1149372, by rfl⟩ : syracuseStep 12259973 = 2298745) B2298745
theorem B8173315 : Blo 2267435 8173315 := bstep (se 1 (by rfl) ⟨6129986, by rfl⟩ : syracuseStep 8173315 = 12259973) B12259973
theorem B10897753 : Blo 2267435 10897753 := bstep (se 2 (by rfl) ⟨4086657, by rfl⟩ : syracuseStep 10897753 = 8173315) B8173315
theorem B14530337 : Blo 2267435 14530337 := bstep (se 2 (by rfl) ⟨5448876, by rfl⟩ : syracuseStep 14530337 = 10897753) B10897753
theorem B9686891 : Blo 2267435 9686891 := bstep (se 1 (by rfl) ⟨7265168, by rfl⟩ : syracuseStep 9686891 = 14530337) B14530337
theorem B6457927 : Blo 2267435 6457927 := bstep (se 1 (by rfl) ⟨4843445, by rfl⟩ : syracuseStep 6457927 = 9686891) B9686891
theorem B8610569 : Blo 2267435 8610569 := bstep (se 2 (by rfl) ⟨3228963, by rfl⟩ : syracuseStep 8610569 = 6457927) B6457927
theorem B5740379 : Blo 2267435 5740379 := bstep (se 1 (by rfl) ⟨4305284, by rfl⟩ : syracuseStep 5740379 = 8610569) B8610569
theorem B3826919 : Blo 2267435 3826919 := bstep (se 1 (by rfl) ⟨2870189, by rfl⟩ : syracuseStep 3826919 = 5740379) B5740379
theorem B2551279 : Blo 2267435 2551279 := bstep (se 1 (by rfl) ⟨1913459, by rfl⟩ : syracuseStep 2551279 = 3826919) B3826919
theorem B3401705 : Blo 2267435 3401705 := bstep (se 2 (by rfl) ⟨1275639, by rfl⟩ : syracuseStep 3401705 = 2551279) B2551279
theorem B2267803 : Blo 2267435 2267803 := bstep (se 1 (by rfl) ⟨1700852, by rfl⟩ : syracuseStep 2267803 = 3401705) B3401705
theorem B19373813 : Blo 2267435 19373813 := bbase (se 5 (by rfl) ⟨908147, by rfl⟩ : syracuseStep 19373813 = 1816295) (by norm_num)
theorem B12915875 : Blo 2267435 12915875 := bstep (se 1 (by rfl) ⟨9686906, by rfl⟩ : syracuseStep 12915875 = 19373813) B19373813
theorem B8610583 : Blo 2267435 8610583 := bstep (se 1 (by rfl) ⟨6457937, by rfl⟩ : syracuseStep 8610583 = 12915875) B12915875
theorem B11480777 : Blo 2267435 11480777 := bstep (se 2 (by rfl) ⟨4305291, by rfl⟩ : syracuseStep 11480777 = 8610583) B8610583
theorem B7653851 : Blo 2267435 7653851 := bstep (se 1 (by rfl) ⟨5740388, by rfl⟩ : syracuseStep 7653851 = 11480777) B11480777
theorem B5102567 : Blo 2267435 5102567 := bstep (se 1 (by rfl) ⟨3826925, by rfl⟩ : syracuseStep 5102567 = 7653851) B7653851
theorem B3401711 : Blo 2267435 3401711 := bstep (se 1 (by rfl) ⟨2551283, by rfl⟩ : syracuseStep 3401711 = 5102567) B5102567
theorem B2267807 : Blo 2267435 2267807 := bstep (se 1 (by rfl) ⟨1700855, by rfl⟩ : syracuseStep 2267807 = 3401711) B3401711
theorem B3401717 : Blo 2267435 3401717 := bbase (se 5 (by rfl) ⟨159455, by rfl⟩ : syracuseStep 3401717 = 318911) (by norm_num)
theorem B2267811 : Blo 2267435 2267811 := bstep (se 1 (by rfl) ⟨1700858, by rfl⟩ : syracuseStep 2267811 = 3401717) B3401717
theorem B9195029 : Blo 2267435 9195029 := bbase (se 6 (by rfl) ⟨215508, by rfl⟩ : syracuseStep 9195029 = 431017) (by norm_num)
theorem B6130019 : Blo 2267435 6130019 := bstep (se 1 (by rfl) ⟨4597514, by rfl⟩ : syracuseStep 6130019 = 9195029) B9195029
theorem B16346717 : Blo 2267435 16346717 := bstep (se 3 (by rfl) ⟨3065009, by rfl⟩ : syracuseStep 16346717 = 6130019) B6130019
theorem B10897811 : Blo 2267435 10897811 := bstep (se 1 (by rfl) ⟨8173358, by rfl⟩ : syracuseStep 10897811 = 16346717) B16346717
theorem B7265207 : Blo 2267435 7265207 := bstep (se 1 (by rfl) ⟨5448905, by rfl⟩ : syracuseStep 7265207 = 10897811) B10897811
theorem B4843471 : Blo 2267435 4843471 := bstep (se 1 (by rfl) ⟨3632603, by rfl⟩ : syracuseStep 4843471 = 7265207) B7265207
theorem B6457961 : Blo 2267435 6457961 := bstep (se 2 (by rfl) ⟨2421735, by rfl⟩ : syracuseStep 6457961 = 4843471) B4843471
theorem B4305307 : Blo 2267435 4305307 := bstep (se 1 (by rfl) ⟨3228980, by rfl⟩ : syracuseStep 4305307 = 6457961) B6457961
theorem B5740409 : Blo 2267435 5740409 := bstep (se 2 (by rfl) ⟨2152653, by rfl⟩ : syracuseStep 5740409 = 4305307) B4305307
theorem B3826939 : Blo 2267435 3826939 := bstep (se 1 (by rfl) ⟨2870204, by rfl⟩ : syracuseStep 3826939 = 5740409) B5740409
theorem B5102585 : Blo 2267435 5102585 := bstep (se 2 (by rfl) ⟨1913469, by rfl⟩ : syracuseStep 5102585 = 3826939) B3826939
theorem B3401723 : Blo 2267435 3401723 := bstep (se 1 (by rfl) ⟨2551292, by rfl⟩ : syracuseStep 3401723 = 5102585) B5102585
theorem B2267815 : Blo 2267435 2267815 := bstep (se 1 (by rfl) ⟨1700861, by rfl⟩ : syracuseStep 2267815 = 3401723) B3401723
theorem B2551297 : Blo 2267435 2551297 := bbase (se 2 (by rfl) ⟨956736, by rfl⟩ : syracuseStep 2551297 = 1913473) (by norm_num)
theorem B3401729 : Blo 2267435 3401729 := bstep (se 2 (by rfl) ⟨1275648, by rfl⟩ : syracuseStep 3401729 = 2551297) B2551297
theorem B2267819 : Blo 2267435 2267819 := bstep (se 1 (by rfl) ⟨1700864, by rfl⟩ : syracuseStep 2267819 = 3401729) B3401729
theorem B5740429 : Blo 2267435 5740429 := bbase (se 3 (by rfl) ⟨1076330, by rfl⟩ : syracuseStep 5740429 = 2152661) (by norm_num)
theorem B7653905 : Blo 2267435 7653905 := bstep (se 2 (by rfl) ⟨2870214, by rfl⟩ : syracuseStep 7653905 = 5740429) B5740429
theorem B5102603 : Blo 2267435 5102603 := bstep (se 1 (by rfl) ⟨3826952, by rfl⟩ : syracuseStep 5102603 = 7653905) B7653905
theorem B3401735 : Blo 2267435 3401735 := bstep (se 1 (by rfl) ⟨2551301, by rfl⟩ : syracuseStep 3401735 = 5102603) B5102603
theorem B2267823 : Blo 2267435 2267823 := bstep (se 1 (by rfl) ⟨1700867, by rfl⟩ : syracuseStep 2267823 = 3401735) B3401735
theorem B3401741 : Blo 2267435 3401741 := bbase (se 3 (by rfl) ⟨637826, by rfl⟩ : syracuseStep 3401741 = 1275653) (by norm_num)
theorem B2267827 : Blo 2267435 2267827 := bstep (se 1 (by rfl) ⟨1700870, by rfl⟩ : syracuseStep 2267827 = 3401741) B3401741
theorem B5102621 : Blo 2267435 5102621 := bbase (se 3 (by rfl) ⟨956741, by rfl⟩ : syracuseStep 5102621 = 1913483) (by norm_num)
theorem B3401747 : Blo 2267435 3401747 := bstep (se 1 (by rfl) ⟨2551310, by rfl⟩ : syracuseStep 3401747 = 5102621) B5102621
theorem B2267831 : Blo 2267435 2267831 := bstep (se 1 (by rfl) ⟨1700873, by rfl⟩ : syracuseStep 2267831 = 3401747) B3401747
theorem B3826973 : Blo 2267435 3826973 := bbase (se 3 (by rfl) ⟨717557, by rfl⟩ : syracuseStep 3826973 = 1435115) (by norm_num)
theorem B2551315 : Blo 2267435 2551315 := bstep (se 1 (by rfl) ⟨1913486, by rfl⟩ : syracuseStep 2551315 = 3826973) B3826973
theorem B3401753 : Blo 2267435 3401753 := bstep (se 2 (by rfl) ⟨1275657, by rfl⟩ : syracuseStep 3401753 = 2551315) B2551315
theorem B2267835 : Blo 2267435 2267835 := bstep (se 1 (by rfl) ⟨1700876, by rfl⟩ : syracuseStep 2267835 = 3401753) B3401753
theorem B2724481 : Blo 2267435 2724481 := bbase (se 2 (by rfl) ⟨1021680, by rfl⟩ : syracuseStep 2724481 = 2043361) (by norm_num)
theorem B14530565 : Blo 2267435 14530565 := bstep (se 4 (by rfl) ⟨1362240, by rfl⟩ : syracuseStep 14530565 = 2724481) B2724481
theorem B9687043 : Blo 2267435 9687043 := bstep (se 1 (by rfl) ⟨7265282, by rfl⟩ : syracuseStep 9687043 = 14530565) B14530565
theorem B12916057 : Blo 2267435 12916057 := bstep (se 2 (by rfl) ⟨4843521, by rfl⟩ : syracuseStep 12916057 = 9687043) B9687043
theorem B17221409 : Blo 2267435 17221409 := bstep (se 2 (by rfl) ⟨6458028, by rfl⟩ : syracuseStep 17221409 = 12916057) B12916057
theorem B11480939 : Blo 2267435 11480939 := bstep (se 1 (by rfl) ⟨8610704, by rfl⟩ : syracuseStep 11480939 = 17221409) B17221409
theorem B7653959 : Blo 2267435 7653959 := bstep (se 1 (by rfl) ⟨5740469, by rfl⟩ : syracuseStep 7653959 = 11480939) B11480939
theorem B5102639 : Blo 2267435 5102639 := bstep (se 1 (by rfl) ⟨3826979, by rfl⟩ : syracuseStep 5102639 = 7653959) B7653959
theorem B3401759 : Blo 2267435 3401759 := bstep (se 1 (by rfl) ⟨2551319, by rfl⟩ : syracuseStep 3401759 = 5102639) B5102639
theorem B2267839 : Blo 2267435 2267839 := bstep (se 1 (by rfl) ⟨1700879, by rfl⟩ : syracuseStep 2267839 = 3401759) B3401759
theorem B3401765 : Blo 2267435 3401765 := bbase (se 4 (by rfl) ⟨318915, by rfl⟩ : syracuseStep 3401765 = 637831) (by norm_num)
theorem B2267843 : Blo 2267435 2267843 := bstep (se 1 (by rfl) ⟨1700882, by rfl⟩ : syracuseStep 2267843 = 3401765) B3401765
theorem B2870245 : Blo 2267435 2870245 := bbase (se 4 (by rfl) ⟨269085, by rfl⟩ : syracuseStep 2870245 = 538171) (by norm_num)
theorem B3826993 : Blo 2267435 3826993 := bstep (se 2 (by rfl) ⟨1435122, by rfl⟩ : syracuseStep 3826993 = 2870245) B2870245
theorem B5102657 : Blo 2267435 5102657 := bstep (se 2 (by rfl) ⟨1913496, by rfl⟩ : syracuseStep 5102657 = 3826993) B3826993
theorem B3401771 : Blo 2267435 3401771 := bstep (se 1 (by rfl) ⟨2551328, by rfl⟩ : syracuseStep 3401771 = 5102657) B5102657
theorem B2267847 : Blo 2267435 2267847 := bstep (se 1 (by rfl) ⟨1700885, by rfl⟩ : syracuseStep 2267847 = 3401771) B3401771
theorem B2551333 : Blo 2267435 2551333 := bbase (se 4 (by rfl) ⟨239187, by rfl⟩ : syracuseStep 2551333 = 478375) (by norm_num)
theorem B3401777 : Blo 2267435 3401777 := bstep (se 2 (by rfl) ⟨1275666, by rfl⟩ : syracuseStep 3401777 = 2551333) B2551333
theorem B2267851 : Blo 2267435 2267851 := bstep (se 1 (by rfl) ⟨1700888, by rfl⟩ : syracuseStep 2267851 = 3401777) B3401777
theorem B2761673 : Blo 2267435 2761673 := bbase (se 2 (by rfl) ⟨1035627, by rfl⟩ : syracuseStep 2761673 = 2071255) (by norm_num)
theorem B7364461 : Blo 2267435 7364461 := bstep (se 3 (by rfl) ⟨1380836, by rfl⟩ : syracuseStep 7364461 = 2761673) B2761673
theorem B9819281 : Blo 2267435 9819281 := bstep (se 2 (by rfl) ⟨3682230, by rfl⟩ : syracuseStep 9819281 = 7364461) B7364461
theorem B6546187 : Blo 2267435 6546187 := bstep (se 1 (by rfl) ⟨4909640, by rfl⟩ : syracuseStep 6546187 = 9819281) B9819281
theorem B8728249 : Blo 2267435 8728249 := bstep (se 2 (by rfl) ⟨3273093, by rfl⟩ : syracuseStep 8728249 = 6546187) B6546187
theorem B11637665 : Blo 2267435 11637665 := bstep (se 2 (by rfl) ⟨4364124, by rfl⟩ : syracuseStep 11637665 = 8728249) B8728249
theorem B7758443 : Blo 2267435 7758443 := bstep (se 1 (by rfl) ⟨5818832, by rfl⟩ : syracuseStep 7758443 = 11637665) B11637665
theorem B20689181 : Blo 2267435 20689181 := bstep (se 3 (by rfl) ⟨3879221, by rfl⟩ : syracuseStep 20689181 = 7758443) B7758443
theorem B13792787 : Blo 2267435 13792787 := bstep (se 1 (by rfl) ⟨10344590, by rfl⟩ : syracuseStep 13792787 = 20689181) B20689181
theorem B9195191 : Blo 2267435 9195191 := bstep (se 1 (by rfl) ⟨6896393, by rfl⟩ : syracuseStep 9195191 = 13792787) B13792787
theorem B6130127 : Blo 2267435 6130127 := bstep (se 1 (by rfl) ⟨4597595, by rfl⟩ : syracuseStep 6130127 = 9195191) B9195191
theorem B16347005 : Blo 2267435 16347005 := bstep (se 3 (by rfl) ⟨3065063, by rfl⟩ : syracuseStep 16347005 = 6130127) B6130127
theorem B10898003 : Blo 2267435 10898003 := bstep (se 1 (by rfl) ⟨8173502, by rfl⟩ : syracuseStep 10898003 = 16347005) B16347005
theorem B7265335 : Blo 2267435 7265335 := bstep (se 1 (by rfl) ⟨5449001, by rfl⟩ : syracuseStep 7265335 = 10898003) B10898003
theorem B9687113 : Blo 2267435 9687113 := bstep (se 2 (by rfl) ⟨3632667, by rfl⟩ : syracuseStep 9687113 = 7265335) B7265335
theorem B6458075 : Blo 2267435 6458075 := bstep (se 1 (by rfl) ⟨4843556, by rfl⟩ : syracuseStep 6458075 = 9687113) B9687113
theorem B4305383 : Blo 2267435 4305383 := bstep (se 1 (by rfl) ⟨3229037, by rfl⟩ : syracuseStep 4305383 = 6458075) B6458075
theorem B2870255 : Blo 2267435 2870255 := bstep (se 1 (by rfl) ⟨2152691, by rfl⟩ : syracuseStep 2870255 = 4305383) B4305383
theorem B7654013 : Blo 2267435 7654013 := bstep (se 3 (by rfl) ⟨1435127, by rfl⟩ : syracuseStep 7654013 = 2870255) B2870255
theorem B5102675 : Blo 2267435 5102675 := bstep (se 1 (by rfl) ⟨3827006, by rfl⟩ : syracuseStep 5102675 = 7654013) B7654013
theorem B3401783 : Blo 2267435 3401783 := bstep (se 1 (by rfl) ⟨2551337, by rfl⟩ : syracuseStep 3401783 = 5102675) B5102675
theorem B2267855 : Blo 2267435 2267855 := bstep (se 1 (by rfl) ⟨1700891, by rfl⟩ : syracuseStep 2267855 = 3401783) B3401783
theorem B3401789 : Blo 2267435 3401789 := bbase (se 3 (by rfl) ⟨637835, by rfl⟩ : syracuseStep 3401789 = 1275671) (by norm_num)
theorem B2267859 : Blo 2267435 2267859 := bstep (se 1 (by rfl) ⟨1700894, by rfl⟩ : syracuseStep 2267859 = 3401789) B3401789
theorem B5102693 : Blo 2267435 5102693 := bbase (se 4 (by rfl) ⟨478377, by rfl⟩ : syracuseStep 5102693 = 956755) (by norm_num)
theorem B3401795 : Blo 2267435 3401795 := bstep (se 1 (by rfl) ⟨2551346, by rfl⟩ : syracuseStep 3401795 = 5102693) B5102693
theorem B2267863 : Blo 2267435 2267863 := bstep (se 1 (by rfl) ⟨1700897, by rfl⟩ : syracuseStep 2267863 = 3401795) B3401795
theorem B5740541 : Blo 2267435 5740541 := bbase (se 3 (by rfl) ⟨1076351, by rfl⟩ : syracuseStep 5740541 = 2152703) (by norm_num)
theorem B3827027 : Blo 2267435 3827027 := bstep (se 1 (by rfl) ⟨2870270, by rfl⟩ : syracuseStep 3827027 = 5740541) B5740541
theorem B2551351 : Blo 2267435 2551351 := bstep (se 1 (by rfl) ⟨1913513, by rfl⟩ : syracuseStep 2551351 = 3827027) B3827027
theorem B3401801 : Blo 2267435 3401801 := bstep (se 2 (by rfl) ⟨1275675, by rfl⟩ : syracuseStep 3401801 = 2551351) B2551351
theorem B2267867 : Blo 2267435 2267867 := bstep (se 1 (by rfl) ⟨1700900, by rfl⟩ : syracuseStep 2267867 = 3401801) B3401801
theorem B4305413 : Blo 2267435 4305413 := bbase (se 4 (by rfl) ⟨403632, by rfl⟩ : syracuseStep 4305413 = 807265) (by norm_num)
theorem B11481101 : Blo 2267435 11481101 := bstep (se 3 (by rfl) ⟨2152706, by rfl⟩ : syracuseStep 11481101 = 4305413) B4305413
theorem B7654067 : Blo 2267435 7654067 := bstep (se 1 (by rfl) ⟨5740550, by rfl⟩ : syracuseStep 7654067 = 11481101) B11481101
theorem B5102711 : Blo 2267435 5102711 := bstep (se 1 (by rfl) ⟨3827033, by rfl⟩ : syracuseStep 5102711 = 7654067) B7654067
theorem B3401807 : Blo 2267435 3401807 := bstep (se 1 (by rfl) ⟨2551355, by rfl⟩ : syracuseStep 3401807 = 5102711) B5102711
theorem B2267871 : Blo 2267435 2267871 := bstep (se 1 (by rfl) ⟨1700903, by rfl⟩ : syracuseStep 2267871 = 3401807) B3401807
theorem B3401813 : Blo 2267435 3401813 := bbase (se 8 (by rfl) ⟨19932, by rfl⟩ : syracuseStep 3401813 = 39865) (by norm_num)
theorem B2267875 : Blo 2267435 2267875 := bstep (se 1 (by rfl) ⟨1700906, by rfl⟩ : syracuseStep 2267875 = 3401813) B3401813
theorem B20689397 : Blo 2267435 20689397 := bbase (se 5 (by rfl) ⟨969815, by rfl⟩ : syracuseStep 20689397 = 1939631) (by norm_num)
theorem B13792931 : Blo 2267435 13792931 := bstep (se 1 (by rfl) ⟨10344698, by rfl⟩ : syracuseStep 13792931 = 20689397) B20689397
theorem B9195287 : Blo 2267435 9195287 := bstep (se 1 (by rfl) ⟨6896465, by rfl⟩ : syracuseStep 9195287 = 13792931) B13792931
theorem B24520765 : Blo 2267435 24520765 := bstep (se 3 (by rfl) ⟨4597643, by rfl⟩ : syracuseStep 24520765 = 9195287) B9195287
theorem B32694353 : Blo 2267435 32694353 := bstep (se 2 (by rfl) ⟨12260382, by rfl⟩ : syracuseStep 32694353 = 24520765) B24520765
theorem B21796235 : Blo 2267435 21796235 := bstep (se 1 (by rfl) ⟨16347176, by rfl⟩ : syracuseStep 21796235 = 32694353) B32694353
theorem B14530823 : Blo 2267435 14530823 := bstep (se 1 (by rfl) ⟨10898117, by rfl⟩ : syracuseStep 14530823 = 21796235) B21796235
theorem B9687215 : Blo 2267435 9687215 := bstep (se 1 (by rfl) ⟨7265411, by rfl⟩ : syracuseStep 9687215 = 14530823) B14530823
theorem B6458143 : Blo 2267435 6458143 := bstep (se 1 (by rfl) ⟨4843607, by rfl⟩ : syracuseStep 6458143 = 9687215) B9687215
theorem B8610857 : Blo 2267435 8610857 := bstep (se 2 (by rfl) ⟨3229071, by rfl⟩ : syracuseStep 8610857 = 6458143) B6458143
theorem B5740571 : Blo 2267435 5740571 := bstep (se 1 (by rfl) ⟨4305428, by rfl⟩ : syracuseStep 5740571 = 8610857) B8610857
theorem B3827047 : Blo 2267435 3827047 := bstep (se 1 (by rfl) ⟨2870285, by rfl⟩ : syracuseStep 3827047 = 5740571) B5740571
theorem B5102729 : Blo 2267435 5102729 := bstep (se 2 (by rfl) ⟨1913523, by rfl⟩ : syracuseStep 5102729 = 3827047) B3827047
theorem B3401819 : Blo 2267435 3401819 := bstep (se 1 (by rfl) ⟨2551364, by rfl⟩ : syracuseStep 3401819 = 5102729) B5102729
theorem B2267879 : Blo 2267435 2267879 := bstep (se 1 (by rfl) ⟨1700909, by rfl⟩ : syracuseStep 2267879 = 3401819) B3401819
theorem B2551369 : Blo 2267435 2551369 := bbase (se 2 (by rfl) ⟨956763, by rfl⟩ : syracuseStep 2551369 = 1913527) (by norm_num)
theorem B3401825 : Blo 2267435 3401825 := bstep (se 2 (by rfl) ⟨1275684, by rfl⟩ : syracuseStep 3401825 = 2551369) B2551369
theorem B2267883 : Blo 2267435 2267883 := bstep (se 1 (by rfl) ⟨1700912, by rfl⟩ : syracuseStep 2267883 = 3401825) B3401825
theorem B4909709 : Blo 2267435 4909709 := bbase (se 3 (by rfl) ⟨920570, by rfl⟩ : syracuseStep 4909709 = 1841141) (by norm_num)
theorem B3273139 : Blo 2267435 3273139 := bstep (se 1 (by rfl) ⟨2454854, by rfl⟩ : syracuseStep 3273139 = 4909709) B4909709
theorem B17456741 : Blo 2267435 17456741 := bstep (se 4 (by rfl) ⟨1636569, by rfl⟩ : syracuseStep 17456741 = 3273139) B3273139
theorem B11637827 : Blo 2267435 11637827 := bstep (se 1 (by rfl) ⟨8728370, by rfl⟩ : syracuseStep 11637827 = 17456741) B17456741
theorem B7758551 : Blo 2267435 7758551 := bstep (se 1 (by rfl) ⟨5818913, by rfl⟩ : syracuseStep 7758551 = 11637827) B11637827
theorem B20689469 : Blo 2267435 20689469 := bstep (se 3 (by rfl) ⟨3879275, by rfl⟩ : syracuseStep 20689469 = 7758551) B7758551
theorem B13792979 : Blo 2267435 13792979 := bstep (se 1 (by rfl) ⟨10344734, by rfl⟩ : syracuseStep 13792979 = 20689469) B20689469
theorem B9195319 : Blo 2267435 9195319 := bstep (se 1 (by rfl) ⟨6896489, by rfl⟩ : syracuseStep 9195319 = 13792979) B13792979
theorem B12260425 : Blo 2267435 12260425 := bstep (se 2 (by rfl) ⟨4597659, by rfl⟩ : syracuseStep 12260425 = 9195319) B9195319
theorem B16347233 : Blo 2267435 16347233 := bstep (se 2 (by rfl) ⟨6130212, by rfl⟩ : syracuseStep 16347233 = 12260425) B12260425
theorem B10898155 : Blo 2267435 10898155 := bstep (se 1 (by rfl) ⟨8173616, by rfl⟩ : syracuseStep 10898155 = 16347233) B16347233
theorem B14530873 : Blo 2267435 14530873 := bstep (se 2 (by rfl) ⟨5449077, by rfl⟩ : syracuseStep 14530873 = 10898155) B10898155
theorem B19374497 : Blo 2267435 19374497 := bstep (se 2 (by rfl) ⟨7265436, by rfl⟩ : syracuseStep 19374497 = 14530873) B14530873
theorem B12916331 : Blo 2267435 12916331 := bstep (se 1 (by rfl) ⟨9687248, by rfl⟩ : syracuseStep 12916331 = 19374497) B19374497
theorem B8610887 : Blo 2267435 8610887 := bstep (se 1 (by rfl) ⟨6458165, by rfl⟩ : syracuseStep 8610887 = 12916331) B12916331
theorem B5740591 : Blo 2267435 5740591 := bstep (se 1 (by rfl) ⟨4305443, by rfl⟩ : syracuseStep 5740591 = 8610887) B8610887
theorem B7654121 : Blo 2267435 7654121 := bstep (se 2 (by rfl) ⟨2870295, by rfl⟩ : syracuseStep 7654121 = 5740591) B5740591
theorem B5102747 : Blo 2267435 5102747 := bstep (se 1 (by rfl) ⟨3827060, by rfl⟩ : syracuseStep 5102747 = 7654121) B7654121
theorem B3401831 : Blo 2267435 3401831 := bstep (se 1 (by rfl) ⟨2551373, by rfl⟩ : syracuseStep 3401831 = 5102747) B5102747
theorem B2267887 : Blo 2267435 2267887 := bstep (se 1 (by rfl) ⟨1700915, by rfl⟩ : syracuseStep 2267887 = 3401831) B3401831
theorem B3401837 : Blo 2267435 3401837 := bbase (se 3 (by rfl) ⟨637844, by rfl⟩ : syracuseStep 3401837 = 1275689) (by norm_num)
theorem B2267891 : Blo 2267435 2267891 := bstep (se 1 (by rfl) ⟨1700918, by rfl⟩ : syracuseStep 2267891 = 3401837) B3401837
theorem B5102765 : Blo 2267435 5102765 := bbase (se 3 (by rfl) ⟨956768, by rfl⟩ : syracuseStep 5102765 = 1913537) (by norm_num)
theorem B3401843 : Blo 2267435 3401843 := bstep (se 1 (by rfl) ⟨2551382, by rfl⟩ : syracuseStep 3401843 = 5102765) B5102765
theorem B2267895 : Blo 2267435 2267895 := bstep (se 1 (by rfl) ⟨1700921, by rfl⟩ : syracuseStep 2267895 = 3401843) B3401843
theorem B7265477 : Blo 2267435 7265477 := bbase (se 4 (by rfl) ⟨681138, by rfl⟩ : syracuseStep 7265477 = 1362277) (by norm_num)
theorem B4843651 : Blo 2267435 4843651 := bstep (se 1 (by rfl) ⟨3632738, by rfl⟩ : syracuseStep 4843651 = 7265477) B7265477
theorem B6458201 : Blo 2267435 6458201 := bstep (se 2 (by rfl) ⟨2421825, by rfl⟩ : syracuseStep 6458201 = 4843651) B4843651
theorem B4305467 : Blo 2267435 4305467 := bstep (se 1 (by rfl) ⟨3229100, by rfl⟩ : syracuseStep 4305467 = 6458201) B6458201
theorem B2870311 : Blo 2267435 2870311 := bstep (se 1 (by rfl) ⟨2152733, by rfl⟩ : syracuseStep 2870311 = 4305467) B4305467
theorem B3827081 : Blo 2267435 3827081 := bstep (se 2 (by rfl) ⟨1435155, by rfl⟩ : syracuseStep 3827081 = 2870311) B2870311
theorem B2551387 : Blo 2267435 2551387 := bstep (se 1 (by rfl) ⟨1913540, by rfl⟩ : syracuseStep 2551387 = 3827081) B3827081
theorem B3401849 : Blo 2267435 3401849 := bstep (se 2 (by rfl) ⟨1275693, by rfl⟩ : syracuseStep 3401849 = 2551387) B2551387
theorem B2267899 : Blo 2267435 2267899 := bstep (se 1 (by rfl) ⟨1700924, by rfl⟩ : syracuseStep 2267899 = 3401849) B3401849
theorem B2909477 : Blo 2267435 2909477 := bbase (se 4 (by rfl) ⟨272763, by rfl⟩ : syracuseStep 2909477 = 545527) (by norm_num)
theorem B7758605 : Blo 2267435 7758605 := bstep (se 3 (by rfl) ⟨1454738, by rfl⟩ : syracuseStep 7758605 = 2909477) B2909477
theorem B20689613 : Blo 2267435 20689613 := bstep (se 3 (by rfl) ⟨3879302, by rfl⟩ : syracuseStep 20689613 = 7758605) B7758605
theorem B13793075 : Blo 2267435 13793075 := bstep (se 1 (by rfl) ⟨10344806, by rfl⟩ : syracuseStep 13793075 = 20689613) B20689613
theorem B9195383 : Blo 2267435 9195383 := bstep (se 1 (by rfl) ⟨6896537, by rfl⟩ : syracuseStep 9195383 = 13793075) B13793075
theorem B24521021 : Blo 2267435 24521021 := bstep (se 3 (by rfl) ⟨4597691, by rfl⟩ : syracuseStep 24521021 = 9195383) B9195383
theorem B16347347 : Blo 2267435 16347347 := bstep (se 1 (by rfl) ⟨12260510, by rfl⟩ : syracuseStep 16347347 = 24521021) B24521021
theorem B10898231 : Blo 2267435 10898231 := bstep (se 1 (by rfl) ⟨8173673, by rfl⟩ : syracuseStep 10898231 = 16347347) B16347347
theorem B29061949 : Blo 2267435 29061949 := bstep (se 3 (by rfl) ⟨5449115, by rfl⟩ : syracuseStep 29061949 = 10898231) B10898231
theorem B38749265 : Blo 2267435 38749265 := bstep (se 2 (by rfl) ⟨14530974, by rfl⟩ : syracuseStep 38749265 = 29061949) B29061949
theorem B25832843 : Blo 2267435 25832843 := bstep (se 1 (by rfl) ⟨19374632, by rfl⟩ : syracuseStep 25832843 = 38749265) B38749265
theorem B17221895 : Blo 2267435 17221895 := bstep (se 1 (by rfl) ⟨12916421, by rfl⟩ : syracuseStep 17221895 = 25832843) B25832843
theorem B11481263 : Blo 2267435 11481263 := bstep (se 1 (by rfl) ⟨8610947, by rfl⟩ : syracuseStep 11481263 = 17221895) B17221895
theorem B7654175 : Blo 2267435 7654175 := bstep (se 1 (by rfl) ⟨5740631, by rfl⟩ : syracuseStep 7654175 = 11481263) B11481263
theorem B5102783 : Blo 2267435 5102783 := bstep (se 1 (by rfl) ⟨3827087, by rfl⟩ : syracuseStep 5102783 = 7654175) B7654175
theorem B3401855 : Blo 2267435 3401855 := bstep (se 1 (by rfl) ⟨2551391, by rfl⟩ : syracuseStep 3401855 = 5102783) B5102783
theorem B2267903 : Blo 2267435 2267903 := bstep (se 1 (by rfl) ⟨1700927, by rfl⟩ : syracuseStep 2267903 = 3401855) B3401855
theorem B3401861 : Blo 2267435 3401861 := bbase (se 4 (by rfl) ⟨318924, by rfl⟩ : syracuseStep 3401861 = 637849) (by norm_num)
theorem B2267907 : Blo 2267435 2267907 := bstep (se 1 (by rfl) ⟨1700930, by rfl⟩ : syracuseStep 2267907 = 3401861) B3401861
theorem B3827101 : Blo 2267435 3827101 := bbase (se 3 (by rfl) ⟨717581, by rfl⟩ : syracuseStep 3827101 = 1435163) (by norm_num)
theorem B5102801 : Blo 2267435 5102801 := bstep (se 2 (by rfl) ⟨1913550, by rfl⟩ : syracuseStep 5102801 = 3827101) B3827101
theorem B3401867 : Blo 2267435 3401867 := bstep (se 1 (by rfl) ⟨2551400, by rfl⟩ : syracuseStep 3401867 = 5102801) B5102801
theorem B2267911 : Blo 2267435 2267911 := bstep (se 1 (by rfl) ⟨1700933, by rfl⟩ : syracuseStep 2267911 = 3401867) B3401867
theorem B2551405 : Blo 2267435 2551405 := bbase (se 3 (by rfl) ⟨478388, by rfl⟩ : syracuseStep 2551405 = 956777) (by norm_num)
theorem B3401873 : Blo 2267435 3401873 := bstep (se 2 (by rfl) ⟨1275702, by rfl⟩ : syracuseStep 3401873 = 2551405) B2551405
theorem B2267915 : Blo 2267435 2267915 := bstep (se 1 (by rfl) ⟨1700936, by rfl⟩ : syracuseStep 2267915 = 3401873) B3401873
theorem B7654229 : Blo 2267435 7654229 := bbase (se 9 (by rfl) ⟨22424, by rfl⟩ : syracuseStep 7654229 = 44849) (by norm_num)
theorem B5102819 : Blo 2267435 5102819 := bstep (se 1 (by rfl) ⟨3827114, by rfl⟩ : syracuseStep 5102819 = 7654229) B7654229
theorem B3401879 : Blo 2267435 3401879 := bstep (se 1 (by rfl) ⟨2551409, by rfl⟩ : syracuseStep 3401879 = 5102819) B5102819
theorem B2267919 : Blo 2267435 2267919 := bstep (se 1 (by rfl) ⟨1700939, by rfl⟩ : syracuseStep 2267919 = 3401879) B3401879
theorem B3401885 : Blo 2267435 3401885 := bbase (se 3 (by rfl) ⟨637853, by rfl⟩ : syracuseStep 3401885 = 1275707) (by norm_num)
theorem B2267923 : Blo 2267435 2267923 := bstep (se 1 (by rfl) ⟨1700942, by rfl⟩ : syracuseStep 2267923 = 3401885) B3401885
theorem B5102837 : Blo 2267435 5102837 := bbase (se 5 (by rfl) ⟨239195, by rfl⟩ : syracuseStep 5102837 = 478391) (by norm_num)
theorem B3401891 : Blo 2267435 3401891 := bstep (se 1 (by rfl) ⟨2551418, by rfl⟩ : syracuseStep 3401891 = 5102837) B5102837
theorem B2267927 : Blo 2267435 2267927 := bstep (se 1 (by rfl) ⟨1700945, by rfl⟩ : syracuseStep 2267927 = 3401891) B3401891
theorem B5044693 : Blo 2267435 5044693 := bbase (se 7 (by rfl) ⟨59117, by rfl⟩ : syracuseStep 5044693 = 118235) (by norm_num)
theorem B6726257 : Blo 2267435 6726257 := bstep (se 2 (by rfl) ⟨2522346, by rfl⟩ : syracuseStep 6726257 = 5044693) B5044693
theorem B4484171 : Blo 2267435 4484171 := bstep (se 1 (by rfl) ⟨3363128, by rfl⟩ : syracuseStep 4484171 = 6726257) B6726257
theorem B11957789 : Blo 2267435 11957789 := bstep (se 3 (by rfl) ⟨2242085, by rfl⟩ : syracuseStep 11957789 = 4484171) B4484171
theorem B7971859 : Blo 2267435 7971859 := bstep (se 1 (by rfl) ⟨5978894, by rfl⟩ : syracuseStep 7971859 = 11957789) B11957789
theorem B10629145 : Blo 2267435 10629145 := bstep (se 2 (by rfl) ⟨3985929, by rfl⟩ : syracuseStep 10629145 = 7971859) B7971859
theorem B14172193 : Blo 2267435 14172193 := bstep (se 2 (by rfl) ⟨5314572, by rfl⟩ : syracuseStep 14172193 = 10629145) B10629145
theorem B18896257 : Blo 2267435 18896257 := bstep (se 2 (by rfl) ⟨7086096, by rfl⟩ : syracuseStep 18896257 = 14172193) B14172193
theorem B100780037 : Blo 2267435 100780037 := bstep (se 4 (by rfl) ⟨9448128, by rfl⟩ : syracuseStep 100780037 = 18896257) B18896257
theorem B67186691 : Blo 2267435 67186691 := bstep (se 1 (by rfl) ⟨50390018, by rfl⟩ : syracuseStep 67186691 = 100780037) B100780037
theorem B44791127 : Blo 2267435 44791127 := bstep (se 1 (by rfl) ⟨33593345, by rfl⟩ : syracuseStep 44791127 = 67186691) B67186691
theorem B29860751 : Blo 2267435 29860751 := bstep (se 1 (by rfl) ⟨22395563, by rfl⟩ : syracuseStep 29860751 = 44791127) B44791127
theorem B19907167 : Blo 2267435 19907167 := bstep (se 1 (by rfl) ⟨14930375, by rfl⟩ : syracuseStep 19907167 = 29860751) B29860751
theorem B26542889 : Blo 2267435 26542889 := bstep (se 2 (by rfl) ⟨9953583, by rfl⟩ : syracuseStep 26542889 = 19907167) B19907167
theorem B17695259 : Blo 2267435 17695259 := bstep (se 1 (by rfl) ⟨13271444, by rfl⟩ : syracuseStep 17695259 = 26542889) B26542889
theorem B11796839 : Blo 2267435 11796839 := bstep (se 1 (by rfl) ⟨8847629, by rfl⟩ : syracuseStep 11796839 = 17695259) B17695259
theorem B7864559 : Blo 2267435 7864559 := bstep (se 1 (by rfl) ⟨5898419, by rfl⟩ : syracuseStep 7864559 = 11796839) B11796839
theorem B5243039 : Blo 2267435 5243039 := bstep (se 1 (by rfl) ⟨3932279, by rfl⟩ : syracuseStep 5243039 = 7864559) B7864559
theorem B3495359 : Blo 2267435 3495359 := bstep (se 1 (by rfl) ⟨2621519, by rfl⟩ : syracuseStep 3495359 = 5243039) B5243039
theorem B9320957 : Blo 2267435 9320957 := bstep (se 3 (by rfl) ⟨1747679, by rfl⟩ : syracuseStep 9320957 = 3495359) B3495359
theorem B6213971 : Blo 2267435 6213971 := bstep (se 1 (by rfl) ⟨4660478, by rfl⟩ : syracuseStep 6213971 = 9320957) B9320957
theorem B4142647 : Blo 2267435 4142647 := bstep (se 1 (by rfl) ⟨3106985, by rfl⟩ : syracuseStep 4142647 = 6213971) B6213971
theorem B5523529 : Blo 2267435 5523529 := bstep (se 2 (by rfl) ⟨2071323, by rfl⟩ : syracuseStep 5523529 = 4142647) B4142647
theorem B7364705 : Blo 2267435 7364705 := bstep (se 2 (by rfl) ⟨2761764, by rfl⟩ : syracuseStep 7364705 = 5523529) B5523529
theorem B78556853 : Blo 2267435 78556853 := bstep (se 5 (by rfl) ⟨3682352, by rfl⟩ : syracuseStep 78556853 = 7364705) B7364705
theorem B52371235 : Blo 2267435 52371235 := bstep (se 1 (by rfl) ⟨39278426, by rfl⟩ : syracuseStep 52371235 = 78556853) B78556853
theorem B69828313 : Blo 2267435 69828313 := bstep (se 2 (by rfl) ⟨26185617, by rfl⟩ : syracuseStep 69828313 = 52371235) B52371235
theorem B93104417 : Blo 2267435 93104417 := bstep (se 2 (by rfl) ⟨34914156, by rfl⟩ : syracuseStep 93104417 = 69828313) B69828313
theorem B248278445 : Blo 2267435 248278445 := bstep (se 3 (by rfl) ⟨46552208, by rfl⟩ : syracuseStep 248278445 = 93104417) B93104417
theorem B165518963 : Blo 2267435 165518963 := bstep (se 1 (by rfl) ⟨124139222, by rfl⟩ : syracuseStep 165518963 = 248278445) B248278445
theorem B110345975 : Blo 2267435 110345975 := bstep (se 1 (by rfl) ⟨82759481, by rfl⟩ : syracuseStep 110345975 = 165518963) B165518963
theorem B73563983 : Blo 2267435 73563983 := bstep (se 1 (by rfl) ⟨55172987, by rfl⟩ : syracuseStep 73563983 = 110345975) B110345975
theorem B49042655 : Blo 2267435 49042655 := bstep (se 1 (by rfl) ⟨36781991, by rfl⟩ : syracuseStep 49042655 = 73563983) B73563983
theorem B32695103 : Blo 2267435 32695103 := bstep (se 1 (by rfl) ⟨24521327, by rfl⟩ : syracuseStep 32695103 = 49042655) B49042655
theorem B21796735 : Blo 2267435 21796735 := bstep (se 1 (by rfl) ⟨16347551, by rfl⟩ : syracuseStep 21796735 = 32695103) B32695103
theorem B29062313 : Blo 2267435 29062313 := bstep (se 2 (by rfl) ⟨10898367, by rfl⟩ : syracuseStep 29062313 = 21796735) B21796735
theorem B19374875 : Blo 2267435 19374875 := bstep (se 1 (by rfl) ⟨14531156, by rfl⟩ : syracuseStep 19374875 = 29062313) B29062313
theorem B12916583 : Blo 2267435 12916583 := bstep (se 1 (by rfl) ⟨9687437, by rfl⟩ : syracuseStep 12916583 = 19374875) B19374875
theorem B8611055 : Blo 2267435 8611055 := bstep (se 1 (by rfl) ⟨6458291, by rfl⟩ : syracuseStep 8611055 = 12916583) B12916583
theorem B5740703 : Blo 2267435 5740703 := bstep (se 1 (by rfl) ⟨4305527, by rfl⟩ : syracuseStep 5740703 = 8611055) B8611055
theorem B3827135 : Blo 2267435 3827135 := bstep (se 1 (by rfl) ⟨2870351, by rfl⟩ : syracuseStep 3827135 = 5740703) B5740703
theorem B2551423 : Blo 2267435 2551423 := bstep (se 1 (by rfl) ⟨1913567, by rfl⟩ : syracuseStep 2551423 = 3827135) B3827135
theorem B3401897 : Blo 2267435 3401897 := bstep (se 2 (by rfl) ⟨1275711, by rfl⟩ : syracuseStep 3401897 = 2551423) B2551423
theorem B2267931 : Blo 2267435 2267931 := bstep (se 1 (by rfl) ⟨1700948, by rfl⟩ : syracuseStep 2267931 = 3401897) B3401897
theorem B19639253 : Blo 2267435 19639253 := bbase (se 7 (by rfl) ⟨230147, by rfl⟩ : syracuseStep 19639253 = 460295) (by norm_num)
theorem B13092835 : Blo 2267435 13092835 := bstep (se 1 (by rfl) ⟨9819626, by rfl⟩ : syracuseStep 13092835 = 19639253) B19639253
theorem B17457113 : Blo 2267435 17457113 := bstep (se 2 (by rfl) ⟨6546417, by rfl⟩ : syracuseStep 17457113 = 13092835) B13092835
theorem B11638075 : Blo 2267435 11638075 := bstep (se 1 (by rfl) ⟨8728556, by rfl⟩ : syracuseStep 11638075 = 17457113) B17457113
theorem B15517433 : Blo 2267435 15517433 := bstep (se 2 (by rfl) ⟨5819037, by rfl⟩ : syracuseStep 15517433 = 11638075) B11638075
theorem B10344955 : Blo 2267435 10344955 := bstep (se 1 (by rfl) ⟨7758716, by rfl⟩ : syracuseStep 10344955 = 15517433) B15517433
theorem B13793273 : Blo 2267435 13793273 := bstep (se 2 (by rfl) ⟨5172477, by rfl⟩ : syracuseStep 13793273 = 10344955) B10344955
theorem B9195515 : Blo 2267435 9195515 := bstep (se 1 (by rfl) ⟨6896636, by rfl⟩ : syracuseStep 9195515 = 13793273) B13793273
theorem B6130343 : Blo 2267435 6130343 := bstep (se 1 (by rfl) ⟨4597757, by rfl⟩ : syracuseStep 6130343 = 9195515) B9195515
theorem B16347581 : Blo 2267435 16347581 := bstep (se 3 (by rfl) ⟨3065171, by rfl⟩ : syracuseStep 16347581 = 6130343) B6130343
theorem B10898387 : Blo 2267435 10898387 := bstep (se 1 (by rfl) ⟨8173790, by rfl⟩ : syracuseStep 10898387 = 16347581) B16347581
theorem B7265591 : Blo 2267435 7265591 := bstep (se 1 (by rfl) ⟨5449193, by rfl⟩ : syracuseStep 7265591 = 10898387) B10898387
theorem B4843727 : Blo 2267435 4843727 := bstep (se 1 (by rfl) ⟨3632795, by rfl⟩ : syracuseStep 4843727 = 7265591) B7265591
theorem B3229151 : Blo 2267435 3229151 := bstep (se 1 (by rfl) ⟨2421863, by rfl⟩ : syracuseStep 3229151 = 4843727) B4843727
theorem B8611069 : Blo 2267435 8611069 := bstep (se 3 (by rfl) ⟨1614575, by rfl⟩ : syracuseStep 8611069 = 3229151) B3229151
theorem B11481425 : Blo 2267435 11481425 := bstep (se 2 (by rfl) ⟨4305534, by rfl⟩ : syracuseStep 11481425 = 8611069) B8611069
theorem B7654283 : Blo 2267435 7654283 := bstep (se 1 (by rfl) ⟨5740712, by rfl⟩ : syracuseStep 7654283 = 11481425) B11481425
theorem B5102855 : Blo 2267435 5102855 := bstep (se 1 (by rfl) ⟨3827141, by rfl⟩ : syracuseStep 5102855 = 7654283) B7654283
theorem B3401903 : Blo 2267435 3401903 := bstep (se 1 (by rfl) ⟨2551427, by rfl⟩ : syracuseStep 3401903 = 5102855) B5102855
theorem B2267935 : Blo 2267435 2267935 := bstep (se 1 (by rfl) ⟨1700951, by rfl⟩ : syracuseStep 2267935 = 3401903) B3401903
theorem B3401909 : Blo 2267435 3401909 := bbase (se 5 (by rfl) ⟨159464, by rfl⟩ : syracuseStep 3401909 = 318929) (by norm_num)
theorem B2267939 : Blo 2267435 2267939 := bstep (se 1 (by rfl) ⟨1700954, by rfl⟩ : syracuseStep 2267939 = 3401909) B3401909
theorem B5740733 : Blo 2267435 5740733 := bbase (se 3 (by rfl) ⟨1076387, by rfl⟩ : syracuseStep 5740733 = 2152775) (by norm_num)
theorem B3827155 : Blo 2267435 3827155 := bstep (se 1 (by rfl) ⟨2870366, by rfl⟩ : syracuseStep 3827155 = 5740733) B5740733
theorem B5102873 : Blo 2267435 5102873 := bstep (se 2 (by rfl) ⟨1913577, by rfl⟩ : syracuseStep 5102873 = 3827155) B3827155
theorem B3401915 : Blo 2267435 3401915 := bstep (se 1 (by rfl) ⟨2551436, by rfl⟩ : syracuseStep 3401915 = 5102873) B5102873
theorem B2267943 : Blo 2267435 2267943 := bstep (se 1 (by rfl) ⟨1700957, by rfl⟩ : syracuseStep 2267943 = 3401915) B3401915
theorem B2551441 : Blo 2267435 2551441 := bbase (se 2 (by rfl) ⟨956790, by rfl⟩ : syracuseStep 2551441 = 1913581) (by norm_num)
theorem B3401921 : Blo 2267435 3401921 := bstep (se 2 (by rfl) ⟨1275720, by rfl⟩ : syracuseStep 3401921 = 2551441) B2551441
theorem B2267947 : Blo 2267435 2267947 := bstep (se 1 (by rfl) ⟨1700960, by rfl⟩ : syracuseStep 2267947 = 3401921) B3401921
theorem B4305565 : Blo 2267435 4305565 := bbase (se 3 (by rfl) ⟨807293, by rfl⟩ : syracuseStep 4305565 = 1614587) (by norm_num)
theorem B5740753 : Blo 2267435 5740753 := bstep (se 2 (by rfl) ⟨2152782, by rfl⟩ : syracuseStep 5740753 = 4305565) B4305565
theorem B7654337 : Blo 2267435 7654337 := bstep (se 2 (by rfl) ⟨2870376, by rfl⟩ : syracuseStep 7654337 = 5740753) B5740753
theorem B5102891 : Blo 2267435 5102891 := bstep (se 1 (by rfl) ⟨3827168, by rfl⟩ : syracuseStep 5102891 = 7654337) B7654337
theorem B3401927 : Blo 2267435 3401927 := bstep (se 1 (by rfl) ⟨2551445, by rfl⟩ : syracuseStep 3401927 = 5102891) B5102891
theorem B2267951 : Blo 2267435 2267951 := bstep (se 1 (by rfl) ⟨1700963, by rfl⟩ : syracuseStep 2267951 = 3401927) B3401927
theorem B3401933 : Blo 2267435 3401933 := bbase (se 3 (by rfl) ⟨637862, by rfl⟩ : syracuseStep 3401933 = 1275725) (by norm_num)
theorem B2267955 : Blo 2267435 2267955 := bstep (se 1 (by rfl) ⟨1700966, by rfl⟩ : syracuseStep 2267955 = 3401933) B3401933
theorem B5102909 : Blo 2267435 5102909 := bbase (se 3 (by rfl) ⟨956795, by rfl⟩ : syracuseStep 5102909 = 1913591) (by norm_num)
theorem B3401939 : Blo 2267435 3401939 := bstep (se 1 (by rfl) ⟨2551454, by rfl⟩ : syracuseStep 3401939 = 5102909) B5102909
theorem B2267959 : Blo 2267435 2267959 := bstep (se 1 (by rfl) ⟨1700969, by rfl⟩ : syracuseStep 2267959 = 3401939) B3401939
theorem B3827189 : Blo 2267435 3827189 := bbase (se 5 (by rfl) ⟨179399, by rfl⟩ : syracuseStep 3827189 = 358799) (by norm_num)
theorem B2551459 : Blo 2267435 2551459 := bstep (se 1 (by rfl) ⟨1913594, by rfl⟩ : syracuseStep 2551459 = 3827189) B3827189
theorem B3401945 : Blo 2267435 3401945 := bstep (se 2 (by rfl) ⟨1275729, by rfl⟩ : syracuseStep 3401945 = 2551459) B2551459
theorem B2267963 : Blo 2267435 2267963 := bstep (se 1 (by rfl) ⟨1700972, by rfl⟩ : syracuseStep 2267963 = 3401945) B3401945
theorem B8285429 : Blo 2267435 8285429 := bbase (se 5 (by rfl) ⟨388379, by rfl⟩ : syracuseStep 8285429 = 776759) (by norm_num)
theorem B22094477 : Blo 2267435 22094477 := bstep (se 3 (by rfl) ⟨4142714, by rfl⟩ : syracuseStep 22094477 = 8285429) B8285429
theorem B14729651 : Blo 2267435 14729651 := bstep (se 1 (by rfl) ⟨11047238, by rfl⟩ : syracuseStep 14729651 = 22094477) B22094477
theorem B9819767 : Blo 2267435 9819767 := bstep (se 1 (by rfl) ⟨7364825, by rfl⟩ : syracuseStep 9819767 = 14729651) B14729651
theorem B6546511 : Blo 2267435 6546511 := bstep (se 1 (by rfl) ⟨4909883, by rfl⟩ : syracuseStep 6546511 = 9819767) B9819767
theorem B34914725 : Blo 2267435 34914725 := bstep (se 4 (by rfl) ⟨3273255, by rfl⟩ : syracuseStep 34914725 = 6546511) B6546511
theorem B23276483 : Blo 2267435 23276483 := bstep (se 1 (by rfl) ⟨17457362, by rfl⟩ : syracuseStep 23276483 = 34914725) B34914725
theorem B15517655 : Blo 2267435 15517655 := bstep (se 1 (by rfl) ⟨11638241, by rfl⟩ : syracuseStep 15517655 = 23276483) B23276483
theorem B10345103 : Blo 2267435 10345103 := bstep (se 1 (by rfl) ⟨7758827, by rfl⟩ : syracuseStep 10345103 = 15517655) B15517655
theorem B6896735 : Blo 2267435 6896735 := bstep (se 1 (by rfl) ⟨5172551, by rfl⟩ : syracuseStep 6896735 = 10345103) B10345103
theorem B4597823 : Blo 2267435 4597823 := bstep (se 1 (by rfl) ⟨3448367, by rfl⟩ : syracuseStep 4597823 = 6896735) B6896735
theorem B3065215 : Blo 2267435 3065215 := bstep (se 1 (by rfl) ⟨2298911, by rfl⟩ : syracuseStep 3065215 = 4597823) B4597823
theorem B4086953 : Blo 2267435 4086953 := bstep (se 2 (by rfl) ⟨1532607, by rfl⟩ : syracuseStep 4086953 = 3065215) B3065215
theorem B2724635 : Blo 2267435 2724635 := bstep (se 1 (by rfl) ⟨2043476, by rfl⟩ : syracuseStep 2724635 = 4086953) B4086953
theorem B7265693 : Blo 2267435 7265693 := bstep (se 3 (by rfl) ⟨1362317, by rfl⟩ : syracuseStep 7265693 = 2724635) B2724635
theorem B4843795 : Blo 2267435 4843795 := bstep (se 1 (by rfl) ⟨3632846, by rfl⟩ : syracuseStep 4843795 = 7265693) B7265693
theorem B6458393 : Blo 2267435 6458393 := bstep (se 2 (by rfl) ⟨2421897, by rfl⟩ : syracuseStep 6458393 = 4843795) B4843795
theorem B17222381 : Blo 2267435 17222381 := bstep (se 3 (by rfl) ⟨3229196, by rfl⟩ : syracuseStep 17222381 = 6458393) B6458393
theorem B11481587 : Blo 2267435 11481587 := bstep (se 1 (by rfl) ⟨8611190, by rfl⟩ : syracuseStep 11481587 = 17222381) B17222381
theorem B7654391 : Blo 2267435 7654391 := bstep (se 1 (by rfl) ⟨5740793, by rfl⟩ : syracuseStep 7654391 = 11481587) B11481587
theorem B5102927 : Blo 2267435 5102927 := bstep (se 1 (by rfl) ⟨3827195, by rfl⟩ : syracuseStep 5102927 = 7654391) B7654391
theorem B3401951 : Blo 2267435 3401951 := bstep (se 1 (by rfl) ⟨2551463, by rfl⟩ : syracuseStep 3401951 = 5102927) B5102927
theorem B2267967 : Blo 2267435 2267967 := bstep (se 1 (by rfl) ⟨1700975, by rfl⟩ : syracuseStep 2267967 = 3401951) B3401951
theorem B3401957 : Blo 2267435 3401957 := bbase (se 4 (by rfl) ⟨318933, by rfl⟩ : syracuseStep 3401957 = 637867) (by norm_num)
theorem B2267971 : Blo 2267435 2267971 := bstep (se 1 (by rfl) ⟨1700978, by rfl⟩ : syracuseStep 2267971 = 3401957) B3401957
theorem B4843813 : Blo 2267435 4843813 := bbase (se 4 (by rfl) ⟨454107, by rfl⟩ : syracuseStep 4843813 = 908215) (by norm_num)
theorem B6458417 : Blo 2267435 6458417 := bstep (se 2 (by rfl) ⟨2421906, by rfl⟩ : syracuseStep 6458417 = 4843813) B4843813
theorem B4305611 : Blo 2267435 4305611 := bstep (se 1 (by rfl) ⟨3229208, by rfl⟩ : syracuseStep 4305611 = 6458417) B6458417
theorem B2870407 : Blo 2267435 2870407 := bstep (se 1 (by rfl) ⟨2152805, by rfl⟩ : syracuseStep 2870407 = 4305611) B4305611
theorem B3827209 : Blo 2267435 3827209 := bstep (se 2 (by rfl) ⟨1435203, by rfl⟩ : syracuseStep 3827209 = 2870407) B2870407
theorem B5102945 : Blo 2267435 5102945 := bstep (se 2 (by rfl) ⟨1913604, by rfl⟩ : syracuseStep 5102945 = 3827209) B3827209
theorem B3401963 : Blo 2267435 3401963 := bstep (se 1 (by rfl) ⟨2551472, by rfl⟩ : syracuseStep 3401963 = 5102945) B5102945
theorem B2267975 : Blo 2267435 2267975 := bstep (se 1 (by rfl) ⟨1700981, by rfl⟩ : syracuseStep 2267975 = 3401963) B3401963
theorem B2551477 : Blo 2267435 2551477 := bbase (se 5 (by rfl) ⟨119600, by rfl⟩ : syracuseStep 2551477 = 239201) (by norm_num)
theorem B3401969 : Blo 2267435 3401969 := bstep (se 2 (by rfl) ⟨1275738, by rfl⟩ : syracuseStep 3401969 = 2551477) B2551477
theorem B2267979 : Blo 2267435 2267979 := bstep (se 1 (by rfl) ⟨1700984, by rfl⟩ : syracuseStep 2267979 = 3401969) B3401969
theorem B2870417 : Blo 2267435 2870417 := bbase (se 2 (by rfl) ⟨1076406, by rfl⟩ : syracuseStep 2870417 = 2152813) (by norm_num)
theorem B7654445 : Blo 2267435 7654445 := bstep (se 3 (by rfl) ⟨1435208, by rfl⟩ : syracuseStep 7654445 = 2870417) B2870417
theorem B5102963 : Blo 2267435 5102963 := bstep (se 1 (by rfl) ⟨3827222, by rfl⟩ : syracuseStep 5102963 = 7654445) B7654445
theorem B3401975 : Blo 2267435 3401975 := bstep (se 1 (by rfl) ⟨2551481, by rfl⟩ : syracuseStep 3401975 = 5102963) B5102963
theorem B2267983 : Blo 2267435 2267983 := bstep (se 1 (by rfl) ⟨1700987, by rfl⟩ : syracuseStep 2267983 = 3401975) B3401975
theorem B3401981 : Blo 2267435 3401981 := bbase (se 3 (by rfl) ⟨637871, by rfl⟩ : syracuseStep 3401981 = 1275743) (by norm_num)
theorem B2267987 : Blo 2267435 2267987 := bstep (se 1 (by rfl) ⟨1700990, by rfl⟩ : syracuseStep 2267987 = 3401981) B3401981
theorem B5102981 : Blo 2267435 5102981 := bbase (se 4 (by rfl) ⟨478404, by rfl⟩ : syracuseStep 5102981 = 956809) (by norm_num)
theorem B3401987 : Blo 2267435 3401987 := bstep (se 1 (by rfl) ⟨2551490, by rfl⟩ : syracuseStep 3401987 = 5102981) B5102981
theorem B2267991 : Blo 2267435 2267991 := bstep (se 1 (by rfl) ⟨1700993, by rfl⟩ : syracuseStep 2267991 = 3401987) B3401987
theorem B3229237 : Blo 2267435 3229237 := bbase (se 5 (by rfl) ⟨151370, by rfl⟩ : syracuseStep 3229237 = 302741) (by norm_num)
theorem B4305649 : Blo 2267435 4305649 := bstep (se 2 (by rfl) ⟨1614618, by rfl⟩ : syracuseStep 4305649 = 3229237) B3229237
theorem B5740865 : Blo 2267435 5740865 := bstep (se 2 (by rfl) ⟨2152824, by rfl⟩ : syracuseStep 5740865 = 4305649) B4305649
theorem B3827243 : Blo 2267435 3827243 := bstep (se 1 (by rfl) ⟨2870432, by rfl⟩ : syracuseStep 3827243 = 5740865) B5740865
theorem B2551495 : Blo 2267435 2551495 := bstep (se 1 (by rfl) ⟨1913621, by rfl⟩ : syracuseStep 2551495 = 3827243) B3827243
theorem B3401993 : Blo 2267435 3401993 := bstep (se 2 (by rfl) ⟨1275747, by rfl⟩ : syracuseStep 3401993 = 2551495) B2551495
theorem B2267995 : Blo 2267435 2267995 := bstep (se 1 (by rfl) ⟨1700996, by rfl⟩ : syracuseStep 2267995 = 3401993) B3401993
theorem B11481749 : Blo 2267435 11481749 := bbase (se 6 (by rfl) ⟨269103, by rfl⟩ : syracuseStep 11481749 = 538207) (by norm_num)
theorem B7654499 : Blo 2267435 7654499 := bstep (se 1 (by rfl) ⟨5740874, by rfl⟩ : syracuseStep 7654499 = 11481749) B11481749
theorem B5102999 : Blo 2267435 5102999 := bstep (se 1 (by rfl) ⟨3827249, by rfl⟩ : syracuseStep 5102999 = 7654499) B7654499
theorem B3401999 : Blo 2267435 3401999 := bstep (se 1 (by rfl) ⟨2551499, by rfl⟩ : syracuseStep 3401999 = 5102999) B5102999
theorem B2267999 : Blo 2267435 2267999 := bstep (se 1 (by rfl) ⟨1700999, by rfl⟩ : syracuseStep 2267999 = 3401999) B3401999
theorem B3402005 : Blo 2267435 3402005 := bbase (se 6 (by rfl) ⟨79734, by rfl⟩ : syracuseStep 3402005 = 159469) (by norm_num)
theorem B2268003 : Blo 2267435 2268003 := bstep (se 1 (by rfl) ⟨1701002, by rfl⟩ : syracuseStep 2268003 = 3402005) B3402005
theorem B3065269 : Blo 2267435 3065269 := bbase (se 5 (by rfl) ⟨143684, by rfl⟩ : syracuseStep 3065269 = 287369) (by norm_num)
theorem B4087025 : Blo 2267435 4087025 := bstep (se 2 (by rfl) ⟨1532634, by rfl⟩ : syracuseStep 4087025 = 3065269) B3065269
theorem B2724683 : Blo 2267435 2724683 := bstep (se 1 (by rfl) ⟨2043512, by rfl⟩ : syracuseStep 2724683 = 4087025) B4087025
theorem B29063285 : Blo 2267435 29063285 := bstep (se 5 (by rfl) ⟨1362341, by rfl⟩ : syracuseStep 29063285 = 2724683) B2724683
theorem B19375523 : Blo 2267435 19375523 := bstep (se 1 (by rfl) ⟨14531642, by rfl⟩ : syracuseStep 19375523 = 29063285) B29063285
theorem B12917015 : Blo 2267435 12917015 := bstep (se 1 (by rfl) ⟨9687761, by rfl⟩ : syracuseStep 12917015 = 19375523) B19375523
theorem B8611343 : Blo 2267435 8611343 := bstep (se 1 (by rfl) ⟨6458507, by rfl⟩ : syracuseStep 8611343 = 12917015) B12917015
theorem B5740895 : Blo 2267435 5740895 := bstep (se 1 (by rfl) ⟨4305671, by rfl⟩ : syracuseStep 5740895 = 8611343) B8611343
theorem B3827263 : Blo 2267435 3827263 := bstep (se 1 (by rfl) ⟨2870447, by rfl⟩ : syracuseStep 3827263 = 5740895) B5740895
theorem B5103017 : Blo 2267435 5103017 := bstep (se 2 (by rfl) ⟨1913631, by rfl⟩ : syracuseStep 5103017 = 3827263) B3827263
theorem B3402011 : Blo 2267435 3402011 := bstep (se 1 (by rfl) ⟨2551508, by rfl⟩ : syracuseStep 3402011 = 5103017) B5103017
theorem B2268007 : Blo 2267435 2268007 := bstep (se 1 (by rfl) ⟨1701005, by rfl⟩ : syracuseStep 2268007 = 3402011) B3402011
theorem B2551513 : Blo 2267435 2551513 := bbase (se 2 (by rfl) ⟨956817, by rfl⟩ : syracuseStep 2551513 = 1913635) (by norm_num)
theorem B3402017 : Blo 2267435 3402017 := bstep (se 2 (by rfl) ⟨1275756, by rfl⟩ : syracuseStep 3402017 = 2551513) B2551513
theorem B2268011 : Blo 2267435 2268011 := bstep (se 1 (by rfl) ⟨1701008, by rfl⟩ : syracuseStep 2268011 = 3402017) B3402017
theorem B2421949 : Blo 2267435 2421949 := bbase (se 3 (by rfl) ⟨454115, by rfl⟩ : syracuseStep 2421949 = 908231) (by norm_num)
theorem B3229265 : Blo 2267435 3229265 := bstep (se 2 (by rfl) ⟨1210974, by rfl⟩ : syracuseStep 3229265 = 2421949) B2421949
theorem B8611373 : Blo 2267435 8611373 := bstep (se 3 (by rfl) ⟨1614632, by rfl⟩ : syracuseStep 8611373 = 3229265) B3229265
theorem B5740915 : Blo 2267435 5740915 := bstep (se 1 (by rfl) ⟨4305686, by rfl⟩ : syracuseStep 5740915 = 8611373) B8611373
theorem B7654553 : Blo 2267435 7654553 := bstep (se 2 (by rfl) ⟨2870457, by rfl⟩ : syracuseStep 7654553 = 5740915) B5740915
theorem B5103035 : Blo 2267435 5103035 := bstep (se 1 (by rfl) ⟨3827276, by rfl⟩ : syracuseStep 5103035 = 7654553) B7654553
theorem B3402023 : Blo 2267435 3402023 := bstep (se 1 (by rfl) ⟨2551517, by rfl⟩ : syracuseStep 3402023 = 5103035) B5103035
theorem B2268015 : Blo 2267435 2268015 := bstep (se 1 (by rfl) ⟨1701011, by rfl⟩ : syracuseStep 2268015 = 3402023) B3402023
theorem B3402029 : Blo 2267435 3402029 := bbase (se 3 (by rfl) ⟨637880, by rfl⟩ : syracuseStep 3402029 = 1275761) (by norm_num)
theorem B2268019 : Blo 2267435 2268019 := bstep (se 1 (by rfl) ⟨1701014, by rfl⟩ : syracuseStep 2268019 = 3402029) B3402029
theorem B5103053 : Blo 2267435 5103053 := bbase (se 3 (by rfl) ⟨956822, by rfl⟩ : syracuseStep 5103053 = 1913645) (by norm_num)
theorem B3402035 : Blo 2267435 3402035 := bstep (se 1 (by rfl) ⟨2551526, by rfl⟩ : syracuseStep 3402035 = 5103053) B5103053
theorem B2268023 : Blo 2267435 2268023 := bstep (se 1 (by rfl) ⟨1701017, by rfl⟩ : syracuseStep 2268023 = 3402035) B3402035
theorem B2870473 : Blo 2267435 2870473 := bbase (se 2 (by rfl) ⟨1076427, by rfl⟩ : syracuseStep 2870473 = 2152855) (by norm_num)
theorem B3827297 : Blo 2267435 3827297 := bstep (se 2 (by rfl) ⟨1435236, by rfl⟩ : syracuseStep 3827297 = 2870473) B2870473
theorem B2551531 : Blo 2267435 2551531 := bstep (se 1 (by rfl) ⟨1913648, by rfl⟩ : syracuseStep 2551531 = 3827297) B3827297
theorem B3402041 : Blo 2267435 3402041 := bstep (se 2 (by rfl) ⟨1275765, by rfl⟩ : syracuseStep 3402041 = 2551531) B2551531
theorem B2268027 : Blo 2267435 2268027 := bstep (se 1 (by rfl) ⟨1701020, by rfl⟩ : syracuseStep 2268027 = 3402041) B3402041
theorem B26186773 : Blo 2267435 26186773 := bbase (se 6 (by rfl) ⟨613752, by rfl⟩ : syracuseStep 26186773 = 1227505) (by norm_num)
theorem B34915697 : Blo 2267435 34915697 := bstep (se 2 (by rfl) ⟨13093386, by rfl⟩ : syracuseStep 34915697 = 26186773) B26186773
theorem B23277131 : Blo 2267435 23277131 := bstep (se 1 (by rfl) ⟨17457848, by rfl⟩ : syracuseStep 23277131 = 34915697) B34915697
theorem B15518087 : Blo 2267435 15518087 := bstep (se 1 (by rfl) ⟨11638565, by rfl⟩ : syracuseStep 15518087 = 23277131) B23277131
theorem B10345391 : Blo 2267435 10345391 := bstep (se 1 (by rfl) ⟨7759043, by rfl⟩ : syracuseStep 10345391 = 15518087) B15518087
theorem B6896927 : Blo 2267435 6896927 := bstep (se 1 (by rfl) ⟨5172695, by rfl⟩ : syracuseStep 6896927 = 10345391) B10345391
theorem B18391805 : Blo 2267435 18391805 := bstep (se 3 (by rfl) ⟨3448463, by rfl⟩ : syracuseStep 18391805 = 6896927) B6896927
theorem B12261203 : Blo 2267435 12261203 := bstep (se 1 (by rfl) ⟨9195902, by rfl⟩ : syracuseStep 12261203 = 18391805) B18391805
theorem B8174135 : Blo 2267435 8174135 := bstep (se 1 (by rfl) ⟨6130601, by rfl⟩ : syracuseStep 8174135 = 12261203) B12261203
theorem B21797693 : Blo 2267435 21797693 := bstep (se 3 (by rfl) ⟨4087067, by rfl⟩ : syracuseStep 21797693 = 8174135) B8174135
theorem B14531795 : Blo 2267435 14531795 := bstep (se 1 (by rfl) ⟨10898846, by rfl⟩ : syracuseStep 14531795 = 21797693) B21797693
theorem B9687863 : Blo 2267435 9687863 := bstep (se 1 (by rfl) ⟨7265897, by rfl⟩ : syracuseStep 9687863 = 14531795) B14531795
theorem B25834301 : Blo 2267435 25834301 := bstep (se 3 (by rfl) ⟨4843931, by rfl⟩ : syracuseStep 25834301 = 9687863) B9687863
theorem B17222867 : Blo 2267435 17222867 := bstep (se 1 (by rfl) ⟨12917150, by rfl⟩ : syracuseStep 17222867 = 25834301) B25834301
theorem B11481911 : Blo 2267435 11481911 := bstep (se 1 (by rfl) ⟨8611433, by rfl⟩ : syracuseStep 11481911 = 17222867) B17222867
theorem B7654607 : Blo 2267435 7654607 := bstep (se 1 (by rfl) ⟨5740955, by rfl⟩ : syracuseStep 7654607 = 11481911) B11481911
theorem B5103071 : Blo 2267435 5103071 := bstep (se 1 (by rfl) ⟨3827303, by rfl⟩ : syracuseStep 5103071 = 7654607) B7654607
theorem B3402047 : Blo 2267435 3402047 := bstep (se 1 (by rfl) ⟨2551535, by rfl⟩ : syracuseStep 3402047 = 5103071) B5103071
theorem B2268031 : Blo 2267435 2268031 := bstep (se 1 (by rfl) ⟨1701023, by rfl⟩ : syracuseStep 2268031 = 3402047) B3402047
theorem B3402053 : Blo 2267435 3402053 := bbase (se 4 (by rfl) ⟨318942, by rfl⟩ : syracuseStep 3402053 = 637885) (by norm_num)
theorem B2268035 : Blo 2267435 2268035 := bstep (se 1 (by rfl) ⟨1701026, by rfl⟩ : syracuseStep 2268035 = 3402053) B3402053
theorem B3827317 : Blo 2267435 3827317 := bbase (se 5 (by rfl) ⟨179405, by rfl⟩ : syracuseStep 3827317 = 358811) (by norm_num)
theorem B5103089 : Blo 2267435 5103089 := bstep (se 2 (by rfl) ⟨1913658, by rfl⟩ : syracuseStep 5103089 = 3827317) B3827317
theorem B3402059 : Blo 2267435 3402059 := bstep (se 1 (by rfl) ⟨2551544, by rfl⟩ : syracuseStep 3402059 = 5103089) B5103089
theorem B2268039 : Blo 2267435 2268039 := bstep (se 1 (by rfl) ⟨1701029, by rfl⟩ : syracuseStep 2268039 = 3402059) B3402059
theorem B2551549 : Blo 2267435 2551549 := bbase (se 3 (by rfl) ⟨478415, by rfl⟩ : syracuseStep 2551549 = 956831) (by norm_num)
theorem B3402065 : Blo 2267435 3402065 := bstep (se 2 (by rfl) ⟨1275774, by rfl⟩ : syracuseStep 3402065 = 2551549) B2551549
theorem B2268043 : Blo 2267435 2268043 := bstep (se 1 (by rfl) ⟨1701032, by rfl⟩ : syracuseStep 2268043 = 3402065) B3402065
theorem B7654661 : Blo 2267435 7654661 := bbase (se 4 (by rfl) ⟨717624, by rfl⟩ : syracuseStep 7654661 = 1435249) (by norm_num)
theorem B5103107 : Blo 2267435 5103107 := bstep (se 1 (by rfl) ⟨3827330, by rfl⟩ : syracuseStep 5103107 = 7654661) B7654661
theorem B3402071 : Blo 2267435 3402071 := bstep (se 1 (by rfl) ⟨2551553, by rfl⟩ : syracuseStep 3402071 = 5103107) B5103107
theorem B2268047 : Blo 2267435 2268047 := bstep (se 1 (by rfl) ⟨1701035, by rfl⟩ : syracuseStep 2268047 = 3402071) B3402071
theorem B3402077 : Blo 2267435 3402077 := bbase (se 3 (by rfl) ⟨637889, by rfl⟩ : syracuseStep 3402077 = 1275779) (by norm_num)
theorem B2268051 : Blo 2267435 2268051 := bstep (se 1 (by rfl) ⟨1701038, by rfl⟩ : syracuseStep 2268051 = 3402077) B3402077
theorem B5103125 : Blo 2267435 5103125 := bbase (se 6 (by rfl) ⟨119604, by rfl⟩ : syracuseStep 5103125 = 239209) (by norm_num)
theorem B3402083 : Blo 2267435 3402083 := bstep (se 1 (by rfl) ⟨2551562, by rfl⟩ : syracuseStep 3402083 = 5103125) B5103125
theorem B2268055 : Blo 2267435 2268055 := bstep (se 1 (by rfl) ⟨1701041, by rfl⟩ : syracuseStep 2268055 = 3402083) B3402083
theorem B8611541 : Blo 2267435 8611541 := bbase (se 7 (by rfl) ⟨100916, by rfl⟩ : syracuseStep 8611541 = 201833) (by norm_num)
theorem B5741027 : Blo 2267435 5741027 := bstep (se 1 (by rfl) ⟨4305770, by rfl⟩ : syracuseStep 5741027 = 8611541) B8611541
theorem B3827351 : Blo 2267435 3827351 := bstep (se 1 (by rfl) ⟨2870513, by rfl⟩ : syracuseStep 3827351 = 5741027) B5741027
theorem B2551567 : Blo 2267435 2551567 := bstep (se 1 (by rfl) ⟨1913675, by rfl⟩ : syracuseStep 2551567 = 3827351) B3827351
theorem B3402089 : Blo 2267435 3402089 := bstep (se 2 (by rfl) ⟨1275783, by rfl⟩ : syracuseStep 3402089 = 2551567) B2551567
theorem B2268059 : Blo 2267435 2268059 := bstep (se 1 (by rfl) ⟨1701044, by rfl⟩ : syracuseStep 2268059 = 3402089) B3402089
theorem B12917333 : Blo 2267435 12917333 := bbase (se 8 (by rfl) ⟨75687, by rfl⟩ : syracuseStep 12917333 = 151375) (by norm_num)
theorem B8611555 : Blo 2267435 8611555 := bstep (se 1 (by rfl) ⟨6458666, by rfl⟩ : syracuseStep 8611555 = 12917333) B12917333
theorem B11482073 : Blo 2267435 11482073 := bstep (se 2 (by rfl) ⟨4305777, by rfl⟩ : syracuseStep 11482073 = 8611555) B8611555
theorem B7654715 : Blo 2267435 7654715 := bstep (se 1 (by rfl) ⟨5741036, by rfl⟩ : syracuseStep 7654715 = 11482073) B11482073
theorem B5103143 : Blo 2267435 5103143 := bstep (se 1 (by rfl) ⟨3827357, by rfl⟩ : syracuseStep 5103143 = 7654715) B7654715
theorem B3402095 : Blo 2267435 3402095 := bstep (se 1 (by rfl) ⟨2551571, by rfl⟩ : syracuseStep 3402095 = 5103143) B5103143
theorem B2268063 : Blo 2267435 2268063 := bstep (se 1 (by rfl) ⟨1701047, by rfl⟩ : syracuseStep 2268063 = 3402095) B3402095
theorem B3402101 : Blo 2267435 3402101 := bbase (se 5 (by rfl) ⟨159473, by rfl⟩ : syracuseStep 3402101 = 318947) (by norm_num)
theorem B2268067 : Blo 2267435 2268067 := bstep (se 1 (by rfl) ⟨1701050, by rfl⟩ : syracuseStep 2268067 = 3402101) B3402101
theorem B2422009 : Blo 2267435 2422009 := bbase (se 2 (by rfl) ⟨908253, by rfl⟩ : syracuseStep 2422009 = 1816507) (by norm_num)
theorem B3229345 : Blo 2267435 3229345 := bstep (se 2 (by rfl) ⟨1211004, by rfl⟩ : syracuseStep 3229345 = 2422009) B2422009
theorem B4305793 : Blo 2267435 4305793 := bstep (se 2 (by rfl) ⟨1614672, by rfl⟩ : syracuseStep 4305793 = 3229345) B3229345
theorem B5741057 : Blo 2267435 5741057 := bstep (se 2 (by rfl) ⟨2152896, by rfl⟩ : syracuseStep 5741057 = 4305793) B4305793
theorem B3827371 : Blo 2267435 3827371 := bstep (se 1 (by rfl) ⟨2870528, by rfl⟩ : syracuseStep 3827371 = 5741057) B5741057
theorem B5103161 : Blo 2267435 5103161 := bstep (se 2 (by rfl) ⟨1913685, by rfl⟩ : syracuseStep 5103161 = 3827371) B3827371
theorem B3402107 : Blo 2267435 3402107 := bstep (se 1 (by rfl) ⟨2551580, by rfl⟩ : syracuseStep 3402107 = 5103161) B5103161
theorem B2268071 : Blo 2267435 2268071 := bstep (se 1 (by rfl) ⟨1701053, by rfl⟩ : syracuseStep 2268071 = 3402107) B3402107
theorem B2551585 : Blo 2267435 2551585 := bbase (se 2 (by rfl) ⟨956844, by rfl⟩ : syracuseStep 2551585 = 1913689) (by norm_num)
theorem B3402113 : Blo 2267435 3402113 := bstep (se 2 (by rfl) ⟨1275792, by rfl⟩ : syracuseStep 3402113 = 2551585) B2551585
theorem B2268075 : Blo 2267435 2268075 := bstep (se 1 (by rfl) ⟨1701056, by rfl⟩ : syracuseStep 2268075 = 3402113) B3402113
theorem B5741077 : Blo 2267435 5741077 := bbase (se 6 (by rfl) ⟨134556, by rfl⟩ : syracuseStep 5741077 = 269113) (by norm_num)
theorem B7654769 : Blo 2267435 7654769 := bstep (se 2 (by rfl) ⟨2870538, by rfl⟩ : syracuseStep 7654769 = 5741077) B5741077
theorem B5103179 : Blo 2267435 5103179 := bstep (se 1 (by rfl) ⟨3827384, by rfl⟩ : syracuseStep 5103179 = 7654769) B7654769
theorem B3402119 : Blo 2267435 3402119 := bstep (se 1 (by rfl) ⟨2551589, by rfl⟩ : syracuseStep 3402119 = 5103179) B5103179
theorem B2268079 : Blo 2267435 2268079 := bstep (se 1 (by rfl) ⟨1701059, by rfl⟩ : syracuseStep 2268079 = 3402119) B3402119
theorem B3402125 : Blo 2267435 3402125 := bbase (se 3 (by rfl) ⟨637898, by rfl⟩ : syracuseStep 3402125 = 1275797) (by norm_num)
theorem B2268083 : Blo 2267435 2268083 := bstep (se 1 (by rfl) ⟨1701062, by rfl⟩ : syracuseStep 2268083 = 3402125) B3402125
theorem B5103197 : Blo 2267435 5103197 := bbase (se 3 (by rfl) ⟨956849, by rfl⟩ : syracuseStep 5103197 = 1913699) (by norm_num)
theorem B3402131 : Blo 2267435 3402131 := bstep (se 1 (by rfl) ⟨2551598, by rfl⟩ : syracuseStep 3402131 = 5103197) B5103197
theorem B2268087 : Blo 2267435 2268087 := bstep (se 1 (by rfl) ⟨1701065, by rfl⟩ : syracuseStep 2268087 = 3402131) B3402131
theorem B3827405 : Blo 2267435 3827405 := bbase (se 3 (by rfl) ⟨717638, by rfl⟩ : syracuseStep 3827405 = 1435277) (by norm_num)
theorem B2551603 : Blo 2267435 2551603 := bstep (se 1 (by rfl) ⟨1913702, by rfl⟩ : syracuseStep 2551603 = 3827405) B3827405
theorem B3402137 : Blo 2267435 3402137 := bstep (se 2 (by rfl) ⟨1275801, by rfl⟩ : syracuseStep 3402137 = 2551603) B2551603
theorem B2268091 : Blo 2267435 2268091 := bstep (se 1 (by rfl) ⟨1701068, by rfl⟩ : syracuseStep 2268091 = 3402137) B3402137
theorem B2586421 : Blo 2267435 2586421 := bbase (se 5 (by rfl) ⟨121238, by rfl⟩ : syracuseStep 2586421 = 242477) (by norm_num)
theorem B13794245 : Blo 2267435 13794245 := bstep (se 4 (by rfl) ⟨1293210, by rfl⟩ : syracuseStep 13794245 = 2586421) B2586421
theorem B9196163 : Blo 2267435 9196163 := bstep (se 1 (by rfl) ⟨6897122, by rfl⟩ : syracuseStep 9196163 = 13794245) B13794245
theorem B6130775 : Blo 2267435 6130775 := bstep (se 1 (by rfl) ⟨4598081, by rfl⟩ : syracuseStep 6130775 = 9196163) B9196163
theorem B4087183 : Blo 2267435 4087183 := bstep (se 1 (by rfl) ⟨3065387, by rfl⟩ : syracuseStep 4087183 = 6130775) B6130775
theorem B5449577 : Blo 2267435 5449577 := bstep (se 2 (by rfl) ⟨2043591, by rfl⟩ : syracuseStep 5449577 = 4087183) B4087183
theorem B14532205 : Blo 2267435 14532205 := bstep (se 3 (by rfl) ⟨2724788, by rfl⟩ : syracuseStep 14532205 = 5449577) B5449577
theorem B19376273 : Blo 2267435 19376273 := bstep (se 2 (by rfl) ⟨7266102, by rfl⟩ : syracuseStep 19376273 = 14532205) B14532205
theorem B12917515 : Blo 2267435 12917515 := bstep (se 1 (by rfl) ⟨9688136, by rfl⟩ : syracuseStep 12917515 = 19376273) B19376273
theorem B17223353 : Blo 2267435 17223353 := bstep (se 2 (by rfl) ⟨6458757, by rfl⟩ : syracuseStep 17223353 = 12917515) B12917515
theorem B11482235 : Blo 2267435 11482235 := bstep (se 1 (by rfl) ⟨8611676, by rfl⟩ : syracuseStep 11482235 = 17223353) B17223353
theorem B7654823 : Blo 2267435 7654823 := bstep (se 1 (by rfl) ⟨5741117, by rfl⟩ : syracuseStep 7654823 = 11482235) B11482235
theorem B5103215 : Blo 2267435 5103215 := bstep (se 1 (by rfl) ⟨3827411, by rfl⟩ : syracuseStep 5103215 = 7654823) B7654823
theorem B3402143 : Blo 2267435 3402143 := bstep (se 1 (by rfl) ⟨2551607, by rfl⟩ : syracuseStep 3402143 = 5103215) B5103215
theorem B2268095 : Blo 2267435 2268095 := bstep (se 1 (by rfl) ⟨1701071, by rfl⟩ : syracuseStep 2268095 = 3402143) B3402143
theorem B3402149 : Blo 2267435 3402149 := bbase (se 4 (by rfl) ⟨318951, by rfl⟩ : syracuseStep 3402149 = 637903) (by norm_num)
theorem B2268099 : Blo 2267435 2268099 := bstep (se 1 (by rfl) ⟨1701074, by rfl⟩ : syracuseStep 2268099 = 3402149) B3402149
theorem B2870569 : Blo 2267435 2870569 := bbase (se 2 (by rfl) ⟨1076463, by rfl⟩ : syracuseStep 2870569 = 2152927) (by norm_num)
theorem B3827425 : Blo 2267435 3827425 := bstep (se 2 (by rfl) ⟨1435284, by rfl⟩ : syracuseStep 3827425 = 2870569) B2870569
theorem B5103233 : Blo 2267435 5103233 := bstep (se 2 (by rfl) ⟨1913712, by rfl⟩ : syracuseStep 5103233 = 3827425) B3827425
theorem B3402155 : Blo 2267435 3402155 := bstep (se 1 (by rfl) ⟨2551616, by rfl⟩ : syracuseStep 3402155 = 5103233) B5103233
theorem B2268103 : Blo 2267435 2268103 := bstep (se 1 (by rfl) ⟨1701077, by rfl⟩ : syracuseStep 2268103 = 3402155) B3402155
theorem B2551621 : Blo 2267435 2551621 := bbase (se 4 (by rfl) ⟨239214, by rfl⟩ : syracuseStep 2551621 = 478429) (by norm_num)
theorem B3402161 : Blo 2267435 3402161 := bstep (se 2 (by rfl) ⟨1275810, by rfl⟩ : syracuseStep 3402161 = 2551621) B2551621
theorem B2268107 : Blo 2267435 2268107 := bstep (se 1 (by rfl) ⟨1701080, by rfl⟩ : syracuseStep 2268107 = 3402161) B3402161
theorem B4305869 : Blo 2267435 4305869 := bbase (se 3 (by rfl) ⟨807350, by rfl⟩ : syracuseStep 4305869 = 1614701) (by norm_num)
theorem B2870579 : Blo 2267435 2870579 := bstep (se 1 (by rfl) ⟨2152934, by rfl⟩ : syracuseStep 2870579 = 4305869) B4305869
theorem B7654877 : Blo 2267435 7654877 := bstep (se 3 (by rfl) ⟨1435289, by rfl⟩ : syracuseStep 7654877 = 2870579) B2870579
theorem B5103251 : Blo 2267435 5103251 := bstep (se 1 (by rfl) ⟨3827438, by rfl⟩ : syracuseStep 5103251 = 7654877) B7654877
theorem B3402167 : Blo 2267435 3402167 := bstep (se 1 (by rfl) ⟨2551625, by rfl⟩ : syracuseStep 3402167 = 5103251) B5103251
theorem B2268111 : Blo 2267435 2268111 := bstep (se 1 (by rfl) ⟨1701083, by rfl⟩ : syracuseStep 2268111 = 3402167) B3402167
theorem B3402173 : Blo 2267435 3402173 := bbase (se 3 (by rfl) ⟨637907, by rfl⟩ : syracuseStep 3402173 = 1275815) (by norm_num)
theorem B2268115 : Blo 2267435 2268115 := bstep (se 1 (by rfl) ⟨1701086, by rfl⟩ : syracuseStep 2268115 = 3402173) B3402173
theorem B5103269 : Blo 2267435 5103269 := bbase (se 4 (by rfl) ⟨478431, by rfl⟩ : syracuseStep 5103269 = 956863) (by norm_num)
theorem B3402179 : Blo 2267435 3402179 := bstep (se 1 (by rfl) ⟨2551634, by rfl⟩ : syracuseStep 3402179 = 5103269) B5103269
theorem B2268119 : Blo 2267435 2268119 := bstep (se 1 (by rfl) ⟨1701089, by rfl⟩ : syracuseStep 2268119 = 3402179) B3402179
theorem B5741189 : Blo 2267435 5741189 := bbase (se 4 (by rfl) ⟨538236, by rfl⟩ : syracuseStep 5741189 = 1076473) (by norm_num)
theorem B3827459 : Blo 2267435 3827459 := bstep (se 1 (by rfl) ⟨2870594, by rfl⟩ : syracuseStep 3827459 = 5741189) B5741189
theorem B2551639 : Blo 2267435 2551639 := bstep (se 1 (by rfl) ⟨1913729, by rfl⟩ : syracuseStep 2551639 = 3827459) B3827459
theorem B3402185 : Blo 2267435 3402185 := bstep (se 2 (by rfl) ⟨1275819, by rfl⟩ : syracuseStep 3402185 = 2551639) B2551639
theorem B2268123 : Blo 2267435 2268123 := bstep (se 1 (by rfl) ⟨1701092, by rfl⟩ : syracuseStep 2268123 = 3402185) B3402185
theorem B6897221 : Blo 2267435 6897221 := bbase (se 4 (by rfl) ⟨646614, by rfl⟩ : syracuseStep 6897221 = 1293229) (by norm_num)
theorem B4598147 : Blo 2267435 4598147 := bstep (se 1 (by rfl) ⟨3448610, by rfl⟩ : syracuseStep 4598147 = 6897221) B6897221
theorem B12261725 : Blo 2267435 12261725 := bstep (se 3 (by rfl) ⟨2299073, by rfl⟩ : syracuseStep 12261725 = 4598147) B4598147
theorem B8174483 : Blo 2267435 8174483 := bstep (se 1 (by rfl) ⟨6130862, by rfl⟩ : syracuseStep 8174483 = 12261725) B12261725
theorem B5449655 : Blo 2267435 5449655 := bstep (se 1 (by rfl) ⟨4087241, by rfl⟩ : syracuseStep 5449655 = 8174483) B8174483
theorem B3633103 : Blo 2267435 3633103 := bstep (se 1 (by rfl) ⟨2724827, by rfl⟩ : syracuseStep 3633103 = 5449655) B5449655
theorem B4844137 : Blo 2267435 4844137 := bstep (se 2 (by rfl) ⟨1816551, by rfl⟩ : syracuseStep 4844137 = 3633103) B3633103
theorem B6458849 : Blo 2267435 6458849 := bstep (se 2 (by rfl) ⟨2422068, by rfl⟩ : syracuseStep 6458849 = 4844137) B4844137
theorem B4305899 : Blo 2267435 4305899 := bstep (se 1 (by rfl) ⟨3229424, by rfl⟩ : syracuseStep 4305899 = 6458849) B6458849
theorem B11482397 : Blo 2267435 11482397 := bstep (se 3 (by rfl) ⟨2152949, by rfl⟩ : syracuseStep 11482397 = 4305899) B4305899
theorem B7654931 : Blo 2267435 7654931 := bstep (se 1 (by rfl) ⟨5741198, by rfl⟩ : syracuseStep 7654931 = 11482397) B11482397
theorem B5103287 : Blo 2267435 5103287 := bstep (se 1 (by rfl) ⟨3827465, by rfl⟩ : syracuseStep 5103287 = 7654931) B7654931
theorem B3402191 : Blo 2267435 3402191 := bstep (se 1 (by rfl) ⟨2551643, by rfl⟩ : syracuseStep 3402191 = 5103287) B5103287
theorem B2268127 : Blo 2267435 2268127 := bstep (se 1 (by rfl) ⟨1701095, by rfl⟩ : syracuseStep 2268127 = 3402191) B3402191
theorem B3402197 : Blo 2267435 3402197 := bbase (se 7 (by rfl) ⟨39869, by rfl⟩ : syracuseStep 3402197 = 79739) (by norm_num)
theorem B2268131 : Blo 2267435 2268131 := bstep (se 1 (by rfl) ⟨1701098, by rfl⟩ : syracuseStep 2268131 = 3402197) B3402197
theorem B8611829 : Blo 2267435 8611829 := bbase (se 5 (by rfl) ⟨403679, by rfl⟩ : syracuseStep 8611829 = 807359) (by norm_num)
theorem B5741219 : Blo 2267435 5741219 := bstep (se 1 (by rfl) ⟨4305914, by rfl⟩ : syracuseStep 5741219 = 8611829) B8611829
theorem B3827479 : Blo 2267435 3827479 := bstep (se 1 (by rfl) ⟨2870609, by rfl⟩ : syracuseStep 3827479 = 5741219) B5741219
theorem B5103305 : Blo 2267435 5103305 := bstep (se 2 (by rfl) ⟨1913739, by rfl⟩ : syracuseStep 5103305 = 3827479) B3827479
theorem B3402203 : Blo 2267435 3402203 := bstep (se 1 (by rfl) ⟨2551652, by rfl⟩ : syracuseStep 3402203 = 5103305) B5103305
theorem B2268135 : Blo 2267435 2268135 := bstep (se 1 (by rfl) ⟨1701101, by rfl⟩ : syracuseStep 2268135 = 3402203) B3402203
theorem B2551657 : Blo 2267435 2551657 := bbase (se 2 (by rfl) ⟨956871, by rfl⟩ : syracuseStep 2551657 = 1913743) (by norm_num)
theorem B3402209 : Blo 2267435 3402209 := bstep (se 2 (by rfl) ⟨1275828, by rfl⟩ : syracuseStep 3402209 = 2551657) B2551657
theorem B2268139 : Blo 2267435 2268139 := bstep (se 1 (by rfl) ⟨1701104, by rfl⟩ : syracuseStep 2268139 = 3402209) B3402209
theorem B5449693 : Blo 2267435 5449693 := bbase (se 3 (by rfl) ⟨1021817, by rfl⟩ : syracuseStep 5449693 = 2043635) (by norm_num)
theorem B7266257 : Blo 2267435 7266257 := bstep (se 2 (by rfl) ⟨2724846, by rfl⟩ : syracuseStep 7266257 = 5449693) B5449693
theorem B4844171 : Blo 2267435 4844171 := bstep (se 1 (by rfl) ⟨3633128, by rfl⟩ : syracuseStep 4844171 = 7266257) B7266257
theorem B12917789 : Blo 2267435 12917789 := bstep (se 3 (by rfl) ⟨2422085, by rfl⟩ : syracuseStep 12917789 = 4844171) B4844171
theorem B8611859 : Blo 2267435 8611859 := bstep (se 1 (by rfl) ⟨6458894, by rfl⟩ : syracuseStep 8611859 = 12917789) B12917789
theorem B5741239 : Blo 2267435 5741239 := bstep (se 1 (by rfl) ⟨4305929, by rfl⟩ : syracuseStep 5741239 = 8611859) B8611859
theorem B7654985 : Blo 2267435 7654985 := bstep (se 2 (by rfl) ⟨2870619, by rfl⟩ : syracuseStep 7654985 = 5741239) B5741239
theorem B5103323 : Blo 2267435 5103323 := bstep (se 1 (by rfl) ⟨3827492, by rfl⟩ : syracuseStep 5103323 = 7654985) B7654985
theorem B3402215 : Blo 2267435 3402215 := bstep (se 1 (by rfl) ⟨2551661, by rfl⟩ : syracuseStep 3402215 = 5103323) B5103323
theorem B2268143 : Blo 2267435 2268143 := bstep (se 1 (by rfl) ⟨1701107, by rfl⟩ : syracuseStep 2268143 = 3402215) B3402215
theorem B3402221 : Blo 2267435 3402221 := bbase (se 3 (by rfl) ⟨637916, by rfl⟩ : syracuseStep 3402221 = 1275833) (by norm_num)
theorem B2268147 : Blo 2267435 2268147 := bstep (se 1 (by rfl) ⟨1701110, by rfl⟩ : syracuseStep 2268147 = 3402221) B3402221
theorem B5103341 : Blo 2267435 5103341 := bbase (se 3 (by rfl) ⟨956876, by rfl⟩ : syracuseStep 5103341 = 1913753) (by norm_num)
theorem B3402227 : Blo 2267435 3402227 := bstep (se 1 (by rfl) ⟨2551670, by rfl⟩ : syracuseStep 3402227 = 5103341) B5103341
theorem B2268151 : Blo 2267435 2268151 := bstep (se 1 (by rfl) ⟨1701113, by rfl⟩ : syracuseStep 2268151 = 3402227) B3402227
theorem B3633149 : Blo 2267435 3633149 := bbase (se 3 (by rfl) ⟨681215, by rfl⟩ : syracuseStep 3633149 = 1362431) (by norm_num)
theorem B2422099 : Blo 2267435 2422099 := bstep (se 1 (by rfl) ⟨1816574, by rfl⟩ : syracuseStep 2422099 = 3633149) B3633149
theorem B3229465 : Blo 2267435 3229465 := bstep (se 2 (by rfl) ⟨1211049, by rfl⟩ : syracuseStep 3229465 = 2422099) B2422099
theorem B4305953 : Blo 2267435 4305953 := bstep (se 2 (by rfl) ⟨1614732, by rfl⟩ : syracuseStep 4305953 = 3229465) B3229465
theorem B2870635 : Blo 2267435 2870635 := bstep (se 1 (by rfl) ⟨2152976, by rfl⟩ : syracuseStep 2870635 = 4305953) B4305953
theorem B3827513 : Blo 2267435 3827513 := bstep (se 2 (by rfl) ⟨1435317, by rfl⟩ : syracuseStep 3827513 = 2870635) B2870635
theorem B2551675 : Blo 2267435 2551675 := bstep (se 1 (by rfl) ⟨1913756, by rfl⟩ : syracuseStep 2551675 = 3827513) B3827513
theorem B3402233 : Blo 2267435 3402233 := bstep (se 2 (by rfl) ⟨1275837, by rfl⟩ : syracuseStep 3402233 = 2551675) B2551675
theorem B2268155 : Blo 2267435 2268155 := bstep (se 1 (by rfl) ⟨1701116, by rfl⟩ : syracuseStep 2268155 = 3402233) B3402233
theorem B3495709 : Blo 2267435 3495709 := bbase (se 3 (by rfl) ⟨655445, by rfl⟩ : syracuseStep 3495709 = 1310891) (by norm_num)
theorem B4660945 : Blo 2267435 4660945 := bstep (se 2 (by rfl) ⟨1747854, by rfl⟩ : syracuseStep 4660945 = 3495709) B3495709
theorem B99433493 : Blo 2267435 99433493 := bstep (se 6 (by rfl) ⟨2330472, by rfl⟩ : syracuseStep 99433493 = 4660945) B4660945
theorem B66288995 : Blo 2267435 66288995 := bstep (se 1 (by rfl) ⟨49716746, by rfl⟩ : syracuseStep 66288995 = 99433493) B99433493
theorem B44192663 : Blo 2267435 44192663 := bstep (se 1 (by rfl) ⟨33144497, by rfl⟩ : syracuseStep 44192663 = 66288995) B66288995
theorem B29461775 : Blo 2267435 29461775 := bstep (se 1 (by rfl) ⟨22096331, by rfl⟩ : syracuseStep 29461775 = 44192663) B44192663
theorem B314258933 : Blo 2267435 314258933 := bstep (se 5 (by rfl) ⟨14730887, by rfl⟩ : syracuseStep 314258933 = 29461775) B29461775
theorem B209505955 : Blo 2267435 209505955 := bstep (se 1 (by rfl) ⟨157129466, by rfl⟩ : syracuseStep 209505955 = 314258933) B314258933
theorem B279341273 : Blo 2267435 279341273 := bstep (se 2 (by rfl) ⟨104752977, by rfl⟩ : syracuseStep 279341273 = 209505955) B209505955
theorem B186227515 : Blo 2267435 186227515 := bstep (se 1 (by rfl) ⟨139670636, by rfl⟩ : syracuseStep 186227515 = 279341273) B279341273
theorem B248303353 : Blo 2267435 248303353 := bstep (se 2 (by rfl) ⟨93113757, by rfl⟩ : syracuseStep 248303353 = 186227515) B186227515
theorem B331071137 : Blo 2267435 331071137 := bstep (se 2 (by rfl) ⟨124151676, by rfl⟩ : syracuseStep 331071137 = 248303353) B248303353
theorem B220714091 : Blo 2267435 220714091 := bstep (se 1 (by rfl) ⟨165535568, by rfl⟩ : syracuseStep 220714091 = 331071137) B331071137
theorem B147142727 : Blo 2267435 147142727 := bstep (se 1 (by rfl) ⟨110357045, by rfl⟩ : syracuseStep 147142727 = 220714091) B220714091
theorem B98095151 : Blo 2267435 98095151 := bstep (se 1 (by rfl) ⟨73571363, by rfl⟩ : syracuseStep 98095151 = 147142727) B147142727
theorem B65396767 : Blo 2267435 65396767 := bstep (se 1 (by rfl) ⟨49047575, by rfl⟩ : syracuseStep 65396767 = 98095151) B98095151
theorem B87195689 : Blo 2267435 87195689 := bstep (se 2 (by rfl) ⟨32698383, by rfl⟩ : syracuseStep 87195689 = 65396767) B65396767
theorem B58130459 : Blo 2267435 58130459 := bstep (se 1 (by rfl) ⟨43597844, by rfl⟩ : syracuseStep 58130459 = 87195689) B87195689
theorem B38753639 : Blo 2267435 38753639 := bstep (se 1 (by rfl) ⟨29065229, by rfl⟩ : syracuseStep 38753639 = 58130459) B58130459
theorem B25835759 : Blo 2267435 25835759 := bstep (se 1 (by rfl) ⟨19376819, by rfl⟩ : syracuseStep 25835759 = 38753639) B38753639
theorem B17223839 : Blo 2267435 17223839 := bstep (se 1 (by rfl) ⟨12917879, by rfl⟩ : syracuseStep 17223839 = 25835759) B25835759
theorem B11482559 : Blo 2267435 11482559 := bstep (se 1 (by rfl) ⟨8611919, by rfl⟩ : syracuseStep 11482559 = 17223839) B17223839
theorem B7655039 : Blo 2267435 7655039 := bstep (se 1 (by rfl) ⟨5741279, by rfl⟩ : syracuseStep 7655039 = 11482559) B11482559
theorem B5103359 : Blo 2267435 5103359 := bstep (se 1 (by rfl) ⟨3827519, by rfl⟩ : syracuseStep 5103359 = 7655039) B7655039
theorem B3402239 : Blo 2267435 3402239 := bstep (se 1 (by rfl) ⟨2551679, by rfl⟩ : syracuseStep 3402239 = 5103359) B5103359
theorem B2268159 : Blo 2267435 2268159 := bstep (se 1 (by rfl) ⟨1701119, by rfl⟩ : syracuseStep 2268159 = 3402239) B3402239
theorem B3402245 : Blo 2267435 3402245 := bbase (se 4 (by rfl) ⟨318960, by rfl⟩ : syracuseStep 3402245 = 637921) (by norm_num)
theorem B2268163 : Blo 2267435 2268163 := bstep (se 1 (by rfl) ⟨1701122, by rfl⟩ : syracuseStep 2268163 = 3402245) B3402245
theorem B3827533 : Blo 2267435 3827533 := bbase (se 3 (by rfl) ⟨717662, by rfl⟩ : syracuseStep 3827533 = 1435325) (by norm_num)
theorem B5103377 : Blo 2267435 5103377 := bstep (se 2 (by rfl) ⟨1913766, by rfl⟩ : syracuseStep 5103377 = 3827533) B3827533
theorem B3402251 : Blo 2267435 3402251 := bstep (se 1 (by rfl) ⟨2551688, by rfl⟩ : syracuseStep 3402251 = 5103377) B5103377
theorem B2268167 : Blo 2267435 2268167 := bstep (se 1 (by rfl) ⟨1701125, by rfl⟩ : syracuseStep 2268167 = 3402251) B3402251
theorem B2551693 : Blo 2267435 2551693 := bbase (se 3 (by rfl) ⟨478442, by rfl⟩ : syracuseStep 2551693 = 956885) (by norm_num)
theorem B3402257 : Blo 2267435 3402257 := bstep (se 2 (by rfl) ⟨1275846, by rfl⟩ : syracuseStep 3402257 = 2551693) B2551693
theorem B2268171 : Blo 2267435 2268171 := bstep (se 1 (by rfl) ⟨1701128, by rfl⟩ : syracuseStep 2268171 = 3402257) B3402257
theorem B7655093 : Blo 2267435 7655093 := bbase (se 5 (by rfl) ⟨358832, by rfl⟩ : syracuseStep 7655093 = 717665) (by norm_num)
theorem B5103395 : Blo 2267435 5103395 := bstep (se 1 (by rfl) ⟨3827546, by rfl⟩ : syracuseStep 5103395 = 7655093) B7655093
theorem B3402263 : Blo 2267435 3402263 := bstep (se 1 (by rfl) ⟨2551697, by rfl⟩ : syracuseStep 3402263 = 5103395) B5103395
theorem B2268175 : Blo 2267435 2268175 := bstep (se 1 (by rfl) ⟨1701131, by rfl⟩ : syracuseStep 2268175 = 3402263) B3402263
theorem B3402269 : Blo 2267435 3402269 := bbase (se 3 (by rfl) ⟨637925, by rfl⟩ : syracuseStep 3402269 = 1275851) (by norm_num)
theorem B2268179 : Blo 2267435 2268179 := bstep (se 1 (by rfl) ⟨1701134, by rfl⟩ : syracuseStep 2268179 = 3402269) B3402269
theorem B5103413 : Blo 2267435 5103413 := bbase (se 5 (by rfl) ⟨239222, by rfl⟩ : syracuseStep 5103413 = 478445) (by norm_num)
theorem B3402275 : Blo 2267435 3402275 := bstep (se 1 (by rfl) ⟨2551706, by rfl⟩ : syracuseStep 3402275 = 5103413) B5103413
theorem B2268183 : Blo 2267435 2268183 := bstep (se 1 (by rfl) ⟨1701137, by rfl⟩ : syracuseStep 2268183 = 3402275) B3402275
theorem B11048309 : Blo 2267435 11048309 := bbase (se 5 (by rfl) ⟨517889, by rfl⟩ : syracuseStep 11048309 = 1035779) (by norm_num)
theorem B7365539 : Blo 2267435 7365539 := bstep (se 1 (by rfl) ⟨5524154, by rfl⟩ : syracuseStep 7365539 = 11048309) B11048309
theorem B19641437 : Blo 2267435 19641437 := bstep (se 3 (by rfl) ⟨3682769, by rfl⟩ : syracuseStep 19641437 = 7365539) B7365539
theorem B13094291 : Blo 2267435 13094291 := bstep (se 1 (by rfl) ⟨9820718, by rfl⟩ : syracuseStep 13094291 = 19641437) B19641437
theorem B8729527 : Blo 2267435 8729527 := bstep (se 1 (by rfl) ⟨6547145, by rfl⟩ : syracuseStep 8729527 = 13094291) B13094291
theorem B11639369 : Blo 2267435 11639369 := bstep (se 2 (by rfl) ⟨4364763, by rfl⟩ : syracuseStep 11639369 = 8729527) B8729527
theorem B7759579 : Blo 2267435 7759579 := bstep (se 1 (by rfl) ⟨5819684, by rfl⟩ : syracuseStep 7759579 = 11639369) B11639369
theorem B10346105 : Blo 2267435 10346105 := bstep (se 2 (by rfl) ⟨3879789, by rfl⟩ : syracuseStep 10346105 = 7759579) B7759579
theorem B6897403 : Blo 2267435 6897403 := bstep (se 1 (by rfl) ⟨5173052, by rfl⟩ : syracuseStep 6897403 = 10346105) B10346105
theorem B9196537 : Blo 2267435 9196537 := bstep (se 2 (by rfl) ⟨3448701, by rfl⟩ : syracuseStep 9196537 = 6897403) B6897403
theorem B12262049 : Blo 2267435 12262049 := bstep (se 2 (by rfl) ⟨4598268, by rfl⟩ : syracuseStep 12262049 = 9196537) B9196537
theorem B8174699 : Blo 2267435 8174699 := bstep (se 1 (by rfl) ⟨6131024, by rfl⟩ : syracuseStep 8174699 = 12262049) B12262049
theorem B5449799 : Blo 2267435 5449799 := bstep (se 1 (by rfl) ⟨4087349, by rfl⟩ : syracuseStep 5449799 = 8174699) B8174699
theorem B14532797 : Blo 2267435 14532797 := bstep (se 3 (by rfl) ⟨2724899, by rfl⟩ : syracuseStep 14532797 = 5449799) B5449799
theorem B9688531 : Blo 2267435 9688531 := bstep (se 1 (by rfl) ⟨7266398, by rfl⟩ : syracuseStep 9688531 = 14532797) B14532797
theorem B12918041 : Blo 2267435 12918041 := bstep (se 2 (by rfl) ⟨4844265, by rfl⟩ : syracuseStep 12918041 = 9688531) B9688531
theorem B8612027 : Blo 2267435 8612027 := bstep (se 1 (by rfl) ⟨6459020, by rfl⟩ : syracuseStep 8612027 = 12918041) B12918041
theorem B5741351 : Blo 2267435 5741351 := bstep (se 1 (by rfl) ⟨4306013, by rfl⟩ : syracuseStep 5741351 = 8612027) B8612027
theorem B3827567 : Blo 2267435 3827567 := bstep (se 1 (by rfl) ⟨2870675, by rfl⟩ : syracuseStep 3827567 = 5741351) B5741351
theorem B2551711 : Blo 2267435 2551711 := bstep (se 1 (by rfl) ⟨1913783, by rfl⟩ : syracuseStep 2551711 = 3827567) B3827567
theorem B3402281 : Blo 2267435 3402281 := bstep (se 2 (by rfl) ⟨1275855, by rfl⟩ : syracuseStep 3402281 = 2551711) B2551711
theorem B2268187 : Blo 2267435 2268187 := bstep (se 1 (by rfl) ⟨1701140, by rfl⟩ : syracuseStep 2268187 = 3402281) B3402281
theorem B14532821 : Blo 2267435 14532821 := bbase (se 7 (by rfl) ⟨170306, by rfl⟩ : syracuseStep 14532821 = 340613) (by norm_num)
theorem B9688547 : Blo 2267435 9688547 := bstep (se 1 (by rfl) ⟨7266410, by rfl⟩ : syracuseStep 9688547 = 14532821) B14532821
theorem B6459031 : Blo 2267435 6459031 := bstep (se 1 (by rfl) ⟨4844273, by rfl⟩ : syracuseStep 6459031 = 9688547) B9688547
theorem B8612041 : Blo 2267435 8612041 := bstep (se 2 (by rfl) ⟨3229515, by rfl⟩ : syracuseStep 8612041 = 6459031) B6459031
theorem B11482721 : Blo 2267435 11482721 := bstep (se 2 (by rfl) ⟨4306020, by rfl⟩ : syracuseStep 11482721 = 8612041) B8612041
theorem B7655147 : Blo 2267435 7655147 := bstep (se 1 (by rfl) ⟨5741360, by rfl⟩ : syracuseStep 7655147 = 11482721) B11482721
theorem B5103431 : Blo 2267435 5103431 := bstep (se 1 (by rfl) ⟨3827573, by rfl⟩ : syracuseStep 5103431 = 7655147) B7655147
theorem B3402287 : Blo 2267435 3402287 := bstep (se 1 (by rfl) ⟨2551715, by rfl⟩ : syracuseStep 3402287 = 5103431) B5103431
theorem B2268191 : Blo 2267435 2268191 := bstep (se 1 (by rfl) ⟨1701143, by rfl⟩ : syracuseStep 2268191 = 3402287) B3402287
theorem B3402293 : Blo 2267435 3402293 := bbase (se 5 (by rfl) ⟨159482, by rfl⟩ : syracuseStep 3402293 = 318965) (by norm_num)
theorem B2268195 : Blo 2267435 2268195 := bstep (se 1 (by rfl) ⟨1701146, by rfl⟩ : syracuseStep 2268195 = 3402293) B3402293
theorem B5741381 : Blo 2267435 5741381 := bbase (se 4 (by rfl) ⟨538254, by rfl⟩ : syracuseStep 5741381 = 1076509) (by norm_num)
theorem B3827587 : Blo 2267435 3827587 := bstep (se 1 (by rfl) ⟨2870690, by rfl⟩ : syracuseStep 3827587 = 5741381) B5741381
theorem B5103449 : Blo 2267435 5103449 := bstep (se 2 (by rfl) ⟨1913793, by rfl⟩ : syracuseStep 5103449 = 3827587) B3827587
theorem B3402299 : Blo 2267435 3402299 := bstep (se 1 (by rfl) ⟨2551724, by rfl⟩ : syracuseStep 3402299 = 5103449) B5103449
theorem B2268199 : Blo 2267435 2268199 := bstep (se 1 (by rfl) ⟨1701149, by rfl⟩ : syracuseStep 2268199 = 3402299) B3402299
theorem B2551729 : Blo 2267435 2551729 := bbase (se 2 (by rfl) ⟨956898, by rfl⟩ : syracuseStep 2551729 = 1913797) (by norm_num)
theorem B3402305 : Blo 2267435 3402305 := bstep (se 2 (by rfl) ⟨1275864, by rfl⟩ : syracuseStep 3402305 = 2551729) B2551729
theorem B2268203 : Blo 2267435 2268203 := bstep (se 1 (by rfl) ⟨1701152, by rfl⟩ : syracuseStep 2268203 = 3402305) B3402305
theorem B6459077 : Blo 2267435 6459077 := bbase (se 4 (by rfl) ⟨605538, by rfl⟩ : syracuseStep 6459077 = 1211077) (by norm_num)
theorem B4306051 : Blo 2267435 4306051 := bstep (se 1 (by rfl) ⟨3229538, by rfl⟩ : syracuseStep 4306051 = 6459077) B6459077
theorem B5741401 : Blo 2267435 5741401 := bstep (se 2 (by rfl) ⟨2153025, by rfl⟩ : syracuseStep 5741401 = 4306051) B4306051
theorem B7655201 : Blo 2267435 7655201 := bstep (se 2 (by rfl) ⟨2870700, by rfl⟩ : syracuseStep 7655201 = 5741401) B5741401
theorem B5103467 : Blo 2267435 5103467 := bstep (se 1 (by rfl) ⟨3827600, by rfl⟩ : syracuseStep 5103467 = 7655201) B7655201
theorem B3402311 : Blo 2267435 3402311 := bstep (se 1 (by rfl) ⟨2551733, by rfl⟩ : syracuseStep 3402311 = 5103467) B5103467
theorem B2268207 : Blo 2267435 2268207 := bstep (se 1 (by rfl) ⟨1701155, by rfl⟩ : syracuseStep 2268207 = 3402311) B3402311
theorem B3402317 : Blo 2267435 3402317 := bbase (se 3 (by rfl) ⟨637934, by rfl⟩ : syracuseStep 3402317 = 1275869) (by norm_num)
theorem B2268211 : Blo 2267435 2268211 := bstep (se 1 (by rfl) ⟨1701158, by rfl⟩ : syracuseStep 2268211 = 3402317) B3402317
theorem B5103485 : Blo 2267435 5103485 := bbase (se 3 (by rfl) ⟨956903, by rfl⟩ : syracuseStep 5103485 = 1913807) (by norm_num)
theorem B3402323 : Blo 2267435 3402323 := bstep (se 1 (by rfl) ⟨2551742, by rfl⟩ : syracuseStep 3402323 = 5103485) B5103485
theorem B2268215 : Blo 2267435 2268215 := bstep (se 1 (by rfl) ⟨1701161, by rfl⟩ : syracuseStep 2268215 = 3402323) B3402323
theorem B3827621 : Blo 2267435 3827621 := bbase (se 4 (by rfl) ⟨358839, by rfl⟩ : syracuseStep 3827621 = 717679) (by norm_num)
theorem B2551747 : Blo 2267435 2551747 := bstep (se 1 (by rfl) ⟨1913810, by rfl⟩ : syracuseStep 2551747 = 3827621) B3827621
theorem B3402329 : Blo 2267435 3402329 := bstep (se 2 (by rfl) ⟨1275873, by rfl⟩ : syracuseStep 3402329 = 2551747) B2551747
theorem B2268219 : Blo 2267435 2268219 := bstep (se 1 (by rfl) ⟨1701164, by rfl⟩ : syracuseStep 2268219 = 3402329) B3402329
theorem B3448757 : Blo 2267435 3448757 := bbase (se 5 (by rfl) ⟨161660, by rfl⟩ : syracuseStep 3448757 = 323321) (by norm_num)
theorem B9196685 : Blo 2267435 9196685 := bstep (se 3 (by rfl) ⟨1724378, by rfl⟩ : syracuseStep 9196685 = 3448757) B3448757
theorem B6131123 : Blo 2267435 6131123 := bstep (se 1 (by rfl) ⟨4598342, by rfl⟩ : syracuseStep 6131123 = 9196685) B9196685
theorem B4087415 : Blo 2267435 4087415 := bstep (se 1 (by rfl) ⟨3065561, by rfl⟩ : syracuseStep 4087415 = 6131123) B6131123
theorem B2724943 : Blo 2267435 2724943 := bstep (se 1 (by rfl) ⟨2043707, by rfl⟩ : syracuseStep 2724943 = 4087415) B4087415
theorem B3633257 : Blo 2267435 3633257 := bstep (se 2 (by rfl) ⟨1362471, by rfl⟩ : syracuseStep 3633257 = 2724943) B2724943
theorem B2422171 : Blo 2267435 2422171 := bstep (se 1 (by rfl) ⟨1816628, by rfl⟩ : syracuseStep 2422171 = 3633257) B3633257
theorem B3229561 : Blo 2267435 3229561 := bstep (se 2 (by rfl) ⟨1211085, by rfl⟩ : syracuseStep 3229561 = 2422171) B2422171
theorem B17224325 : Blo 2267435 17224325 := bstep (se 4 (by rfl) ⟨1614780, by rfl⟩ : syracuseStep 17224325 = 3229561) B3229561
theorem B11482883 : Blo 2267435 11482883 := bstep (se 1 (by rfl) ⟨8612162, by rfl⟩ : syracuseStep 11482883 = 17224325) B17224325
theorem B7655255 : Blo 2267435 7655255 := bstep (se 1 (by rfl) ⟨5741441, by rfl⟩ : syracuseStep 7655255 = 11482883) B11482883
theorem B5103503 : Blo 2267435 5103503 := bstep (se 1 (by rfl) ⟨3827627, by rfl⟩ : syracuseStep 5103503 = 7655255) B7655255
theorem B3402335 : Blo 2267435 3402335 := bstep (se 1 (by rfl) ⟨2551751, by rfl⟩ : syracuseStep 3402335 = 5103503) B5103503
theorem B2268223 : Blo 2267435 2268223 := bstep (se 1 (by rfl) ⟨1701167, by rfl⟩ : syracuseStep 2268223 = 3402335) B3402335
theorem B3402341 : Blo 2267435 3402341 := bbase (se 4 (by rfl) ⟨318969, by rfl⟩ : syracuseStep 3402341 = 637939) (by norm_num)
theorem B2268227 : Blo 2267435 2268227 := bstep (se 1 (by rfl) ⟨1701170, by rfl⟩ : syracuseStep 2268227 = 3402341) B3402341
theorem B3229573 : Blo 2267435 3229573 := bbase (se 4 (by rfl) ⟨302772, by rfl⟩ : syracuseStep 3229573 = 605545) (by norm_num)
theorem B4306097 : Blo 2267435 4306097 := bstep (se 2 (by rfl) ⟨1614786, by rfl⟩ : syracuseStep 4306097 = 3229573) B3229573
theorem B2870731 : Blo 2267435 2870731 := bstep (se 1 (by rfl) ⟨2153048, by rfl⟩ : syracuseStep 2870731 = 4306097) B4306097
theorem B3827641 : Blo 2267435 3827641 := bstep (se 2 (by rfl) ⟨1435365, by rfl⟩ : syracuseStep 3827641 = 2870731) B2870731
theorem B5103521 : Blo 2267435 5103521 := bstep (se 2 (by rfl) ⟨1913820, by rfl⟩ : syracuseStep 5103521 = 3827641) B3827641
theorem B3402347 : Blo 2267435 3402347 := bstep (se 1 (by rfl) ⟨2551760, by rfl⟩ : syracuseStep 3402347 = 5103521) B5103521
theorem B2268231 : Blo 2267435 2268231 := bstep (se 1 (by rfl) ⟨1701173, by rfl⟩ : syracuseStep 2268231 = 3402347) B3402347
theorem B2551765 : Blo 2267435 2551765 := bbase (se 7 (by rfl) ⟨29903, by rfl⟩ : syracuseStep 2551765 = 59807) (by norm_num)
theorem B3402353 : Blo 2267435 3402353 := bstep (se 2 (by rfl) ⟨1275882, by rfl⟩ : syracuseStep 3402353 = 2551765) B2551765
theorem B2268235 : Blo 2267435 2268235 := bstep (se 1 (by rfl) ⟨1701176, by rfl⟩ : syracuseStep 2268235 = 3402353) B3402353
theorem B2870741 : Blo 2267435 2870741 := bbase (se 7 (by rfl) ⟨33641, by rfl⟩ : syracuseStep 2870741 = 67283) (by norm_num)
theorem B7655309 : Blo 2267435 7655309 := bstep (se 3 (by rfl) ⟨1435370, by rfl⟩ : syracuseStep 7655309 = 2870741) B2870741
theorem B5103539 : Blo 2267435 5103539 := bstep (se 1 (by rfl) ⟨3827654, by rfl⟩ : syracuseStep 5103539 = 7655309) B7655309
theorem B3402359 : Blo 2267435 3402359 := bstep (se 1 (by rfl) ⟨2551769, by rfl⟩ : syracuseStep 3402359 = 5103539) B5103539
theorem B2268239 : Blo 2267435 2268239 := bstep (se 1 (by rfl) ⟨1701179, by rfl⟩ : syracuseStep 2268239 = 3402359) B3402359
theorem B3402365 : Blo 2267435 3402365 := bbase (se 3 (by rfl) ⟨637943, by rfl⟩ : syracuseStep 3402365 = 1275887) (by norm_num)
theorem B2268243 : Blo 2267435 2268243 := bstep (se 1 (by rfl) ⟨1701182, by rfl⟩ : syracuseStep 2268243 = 3402365) B3402365
theorem B5103557 : Blo 2267435 5103557 := bbase (se 4 (by rfl) ⟨478458, by rfl⟩ : syracuseStep 5103557 = 956917) (by norm_num)
theorem B3402371 : Blo 2267435 3402371 := bstep (se 1 (by rfl) ⟨2551778, by rfl⟩ : syracuseStep 3402371 = 5103557) B5103557
theorem B2268247 : Blo 2267435 2268247 := bstep (se 1 (by rfl) ⟨1701185, by rfl⟩ : syracuseStep 2268247 = 3402371) B3402371
theorem B9688805 : Blo 2267435 9688805 := bbase (se 4 (by rfl) ⟨908325, by rfl⟩ : syracuseStep 9688805 = 1816651) (by norm_num)
theorem B6459203 : Blo 2267435 6459203 := bstep (se 1 (by rfl) ⟨4844402, by rfl⟩ : syracuseStep 6459203 = 9688805) B9688805
theorem B4306135 : Blo 2267435 4306135 := bstep (se 1 (by rfl) ⟨3229601, by rfl⟩ : syracuseStep 4306135 = 6459203) B6459203
theorem B5741513 : Blo 2267435 5741513 := bstep (se 2 (by rfl) ⟨2153067, by rfl⟩ : syracuseStep 5741513 = 4306135) B4306135
theorem B3827675 : Blo 2267435 3827675 := bstep (se 1 (by rfl) ⟨2870756, by rfl⟩ : syracuseStep 3827675 = 5741513) B5741513
theorem B2551783 : Blo 2267435 2551783 := bstep (se 1 (by rfl) ⟨1913837, by rfl⟩ : syracuseStep 2551783 = 3827675) B3827675
theorem B3402377 : Blo 2267435 3402377 := bstep (se 2 (by rfl) ⟨1275891, by rfl⟩ : syracuseStep 3402377 = 2551783) B2551783
theorem B2268251 : Blo 2267435 2268251 := bstep (se 1 (by rfl) ⟨1701188, by rfl⟩ : syracuseStep 2268251 = 3402377) B3402377
theorem B11483045 : Blo 2267435 11483045 := bbase (se 4 (by rfl) ⟨1076535, by rfl⟩ : syracuseStep 11483045 = 2153071) (by norm_num)
theorem B7655363 : Blo 2267435 7655363 := bstep (se 1 (by rfl) ⟨5741522, by rfl⟩ : syracuseStep 7655363 = 11483045) B11483045
theorem B5103575 : Blo 2267435 5103575 := bstep (se 1 (by rfl) ⟨3827681, by rfl⟩ : syracuseStep 5103575 = 7655363) B7655363
theorem B3402383 : Blo 2267435 3402383 := bstep (se 1 (by rfl) ⟨2551787, by rfl⟩ : syracuseStep 3402383 = 5103575) B5103575
theorem B2268255 : Blo 2267435 2268255 := bstep (se 1 (by rfl) ⟨1701191, by rfl⟩ : syracuseStep 2268255 = 3402383) B3402383
theorem B3402389 : Blo 2267435 3402389 := bbase (se 6 (by rfl) ⟨79743, by rfl⟩ : syracuseStep 3402389 = 159487) (by norm_num)
theorem B2268259 : Blo 2267435 2268259 := bstep (se 1 (by rfl) ⟨1701194, by rfl⟩ : syracuseStep 2268259 = 3402389) B3402389
theorem B21799925 : Blo 2267435 21799925 := bbase (se 5 (by rfl) ⟨1021871, by rfl⟩ : syracuseStep 21799925 = 2043743) (by norm_num)
theorem B14533283 : Blo 2267435 14533283 := bstep (se 1 (by rfl) ⟨10899962, by rfl⟩ : syracuseStep 14533283 = 21799925) B21799925
theorem B9688855 : Blo 2267435 9688855 := bstep (se 1 (by rfl) ⟨7266641, by rfl⟩ : syracuseStep 9688855 = 14533283) B14533283
theorem B12918473 : Blo 2267435 12918473 := bstep (se 2 (by rfl) ⟨4844427, by rfl⟩ : syracuseStep 12918473 = 9688855) B9688855
theorem B8612315 : Blo 2267435 8612315 := bstep (se 1 (by rfl) ⟨6459236, by rfl⟩ : syracuseStep 8612315 = 12918473) B12918473
theorem B5741543 : Blo 2267435 5741543 := bstep (se 1 (by rfl) ⟨4306157, by rfl⟩ : syracuseStep 5741543 = 8612315) B8612315
theorem B3827695 : Blo 2267435 3827695 := bstep (se 1 (by rfl) ⟨2870771, by rfl⟩ : syracuseStep 3827695 = 5741543) B5741543
theorem B5103593 : Blo 2267435 5103593 := bstep (se 2 (by rfl) ⟨1913847, by rfl⟩ : syracuseStep 5103593 = 3827695) B3827695
theorem B3402395 : Blo 2267435 3402395 := bstep (se 1 (by rfl) ⟨2551796, by rfl⟩ : syracuseStep 3402395 = 5103593) B5103593
theorem B2268263 : Blo 2267435 2268263 := bstep (se 1 (by rfl) ⟨1701197, by rfl⟩ : syracuseStep 2268263 = 3402395) B3402395
theorem B2551801 : Blo 2267435 2551801 := bbase (se 2 (by rfl) ⟨956925, by rfl⟩ : syracuseStep 2551801 = 1913851) (by norm_num)
theorem B3402401 : Blo 2267435 3402401 := bstep (se 2 (by rfl) ⟨1275900, by rfl⟩ : syracuseStep 3402401 = 2551801) B2551801
theorem B2268267 : Blo 2267435 2268267 := bstep (se 1 (by rfl) ⟨1701200, by rfl⟩ : syracuseStep 2268267 = 3402401) B3402401
theorem B3448829 : Blo 2267435 3448829 := bbase (se 3 (by rfl) ⟨646655, by rfl⟩ : syracuseStep 3448829 = 1293311) (by norm_num)
theorem B9196877 : Blo 2267435 9196877 := bstep (se 3 (by rfl) ⟨1724414, by rfl⟩ : syracuseStep 9196877 = 3448829) B3448829
theorem B6131251 : Blo 2267435 6131251 := bstep (se 1 (by rfl) ⟨4598438, by rfl⟩ : syracuseStep 6131251 = 9196877) B9196877
theorem B8175001 : Blo 2267435 8175001 := bstep (se 2 (by rfl) ⟨3065625, by rfl⟩ : syracuseStep 8175001 = 6131251) B6131251
theorem B10900001 : Blo 2267435 10900001 := bstep (se 2 (by rfl) ⟨4087500, by rfl⟩ : syracuseStep 10900001 = 8175001) B8175001
theorem B7266667 : Blo 2267435 7266667 := bstep (se 1 (by rfl) ⟨5450000, by rfl⟩ : syracuseStep 7266667 = 10900001) B10900001
theorem B9688889 : Blo 2267435 9688889 := bstep (se 2 (by rfl) ⟨3633333, by rfl⟩ : syracuseStep 9688889 = 7266667) B7266667
theorem B6459259 : Blo 2267435 6459259 := bstep (se 1 (by rfl) ⟨4844444, by rfl⟩ : syracuseStep 6459259 = 9688889) B9688889
theorem B8612345 : Blo 2267435 8612345 := bstep (se 2 (by rfl) ⟨3229629, by rfl⟩ : syracuseStep 8612345 = 6459259) B6459259
theorem B5741563 : Blo 2267435 5741563 := bstep (se 1 (by rfl) ⟨4306172, by rfl⟩ : syracuseStep 5741563 = 8612345) B8612345
theorem B7655417 : Blo 2267435 7655417 := bstep (se 2 (by rfl) ⟨2870781, by rfl⟩ : syracuseStep 7655417 = 5741563) B5741563
theorem B5103611 : Blo 2267435 5103611 := bstep (se 1 (by rfl) ⟨3827708, by rfl⟩ : syracuseStep 5103611 = 7655417) B7655417
theorem B3402407 : Blo 2267435 3402407 := bstep (se 1 (by rfl) ⟨2551805, by rfl⟩ : syracuseStep 3402407 = 5103611) B5103611
theorem B2268271 : Blo 2267435 2268271 := bstep (se 1 (by rfl) ⟨1701203, by rfl⟩ : syracuseStep 2268271 = 3402407) B3402407
theorem B3402413 : Blo 2267435 3402413 := bbase (se 3 (by rfl) ⟨637952, by rfl⟩ : syracuseStep 3402413 = 1275905) (by norm_num)
theorem B2268275 : Blo 2267435 2268275 := bstep (se 1 (by rfl) ⟨1701206, by rfl⟩ : syracuseStep 2268275 = 3402413) B3402413
theorem B5103629 : Blo 2267435 5103629 := bbase (se 3 (by rfl) ⟨956930, by rfl⟩ : syracuseStep 5103629 = 1913861) (by norm_num)
theorem B3402419 : Blo 2267435 3402419 := bstep (se 1 (by rfl) ⟨2551814, by rfl⟩ : syracuseStep 3402419 = 5103629) B5103629
theorem B2268279 : Blo 2267435 2268279 := bstep (se 1 (by rfl) ⟨1701209, by rfl⟩ : syracuseStep 2268279 = 3402419) B3402419
theorem B2870797 : Blo 2267435 2870797 := bbase (se 3 (by rfl) ⟨538274, by rfl⟩ : syracuseStep 2870797 = 1076549) (by norm_num)
theorem B3827729 : Blo 2267435 3827729 := bstep (se 2 (by rfl) ⟨1435398, by rfl⟩ : syracuseStep 3827729 = 2870797) B2870797
theorem B2551819 : Blo 2267435 2551819 := bstep (se 1 (by rfl) ⟨1913864, by rfl⟩ : syracuseStep 2551819 = 3827729) B3827729
theorem B3402425 : Blo 2267435 3402425 := bstep (se 2 (by rfl) ⟨1275909, by rfl⟩ : syracuseStep 3402425 = 2551819) B2551819
theorem B2268283 : Blo 2267435 2268283 := bstep (se 1 (by rfl) ⟨1701212, by rfl⟩ : syracuseStep 2268283 = 3402425) B3402425
theorem B3448853 : Blo 2267435 3448853 := bbase (se 6 (by rfl) ⟨80832, by rfl⟩ : syracuseStep 3448853 = 161665) (by norm_num)
theorem B2299235 : Blo 2267435 2299235 := bstep (se 1 (by rfl) ⟨1724426, by rfl⟩ : syracuseStep 2299235 = 3448853) B3448853
theorem B24525173 : Blo 2267435 24525173 := bstep (se 5 (by rfl) ⟨1149617, by rfl⟩ : syracuseStep 24525173 = 2299235) B2299235
theorem B16350115 : Blo 2267435 16350115 := bstep (se 1 (by rfl) ⟨12262586, by rfl⟩ : syracuseStep 16350115 = 24525173) B24525173
theorem B21800153 : Blo 2267435 21800153 := bstep (se 2 (by rfl) ⟨8175057, by rfl⟩ : syracuseStep 21800153 = 16350115) B16350115
theorem B14533435 : Blo 2267435 14533435 := bstep (se 1 (by rfl) ⟨10900076, by rfl⟩ : syracuseStep 14533435 = 21800153) B21800153
theorem B19377913 : Blo 2267435 19377913 := bstep (se 2 (by rfl) ⟨7266717, by rfl⟩ : syracuseStep 19377913 = 14533435) B14533435
theorem B25837217 : Blo 2267435 25837217 := bstep (se 2 (by rfl) ⟨9688956, by rfl⟩ : syracuseStep 25837217 = 19377913) B19377913
theorem B17224811 : Blo 2267435 17224811 := bstep (se 1 (by rfl) ⟨12918608, by rfl⟩ : syracuseStep 17224811 = 25837217) B25837217
theorem B11483207 : Blo 2267435 11483207 := bstep (se 1 (by rfl) ⟨8612405, by rfl⟩ : syracuseStep 11483207 = 17224811) B17224811
theorem B7655471 : Blo 2267435 7655471 := bstep (se 1 (by rfl) ⟨5741603, by rfl⟩ : syracuseStep 7655471 = 11483207) B11483207
theorem B5103647 : Blo 2267435 5103647 := bstep (se 1 (by rfl) ⟨3827735, by rfl⟩ : syracuseStep 5103647 = 7655471) B7655471
theorem B3402431 : Blo 2267435 3402431 := bstep (se 1 (by rfl) ⟨2551823, by rfl⟩ : syracuseStep 3402431 = 5103647) B5103647
theorem B2268287 : Blo 2267435 2268287 := bstep (se 1 (by rfl) ⟨1701215, by rfl⟩ : syracuseStep 2268287 = 3402431) B3402431
theorem B3402437 : Blo 2267435 3402437 := bbase (se 4 (by rfl) ⟨318978, by rfl⟩ : syracuseStep 3402437 = 637957) (by norm_num)
theorem B2268291 : Blo 2267435 2268291 := bstep (se 1 (by rfl) ⟨1701218, by rfl⟩ : syracuseStep 2268291 = 3402437) B3402437
theorem B3827749 : Blo 2267435 3827749 := bbase (se 4 (by rfl) ⟨358851, by rfl⟩ : syracuseStep 3827749 = 717703) (by norm_num)
theorem B5103665 : Blo 2267435 5103665 := bstep (se 2 (by rfl) ⟨1913874, by rfl⟩ : syracuseStep 5103665 = 3827749) B3827749
theorem B3402443 : Blo 2267435 3402443 := bstep (se 1 (by rfl) ⟨2551832, by rfl⟩ : syracuseStep 3402443 = 5103665) B5103665
theorem B2268295 : Blo 2267435 2268295 := bstep (se 1 (by rfl) ⟨1701221, by rfl⟩ : syracuseStep 2268295 = 3402443) B3402443
theorem B2551837 : Blo 2267435 2551837 := bbase (se 3 (by rfl) ⟨478469, by rfl⟩ : syracuseStep 2551837 = 956939) (by norm_num)
theorem B3402449 : Blo 2267435 3402449 := bstep (se 2 (by rfl) ⟨1275918, by rfl⟩ : syracuseStep 3402449 = 2551837) B2551837
theorem B2268299 : Blo 2267435 2268299 := bstep (se 1 (by rfl) ⟨1701224, by rfl⟩ : syracuseStep 2268299 = 3402449) B3402449
theorem B7655525 : Blo 2267435 7655525 := bbase (se 4 (by rfl) ⟨717705, by rfl⟩ : syracuseStep 7655525 = 1435411) (by norm_num)
theorem B5103683 : Blo 2267435 5103683 := bstep (se 1 (by rfl) ⟨3827762, by rfl⟩ : syracuseStep 5103683 = 7655525) B7655525
theorem B3402455 : Blo 2267435 3402455 := bstep (se 1 (by rfl) ⟨2551841, by rfl⟩ : syracuseStep 3402455 = 5103683) B5103683
theorem B2268303 : Blo 2267435 2268303 := bstep (se 1 (by rfl) ⟨1701227, by rfl⟩ : syracuseStep 2268303 = 3402455) B3402455
theorem B3402461 : Blo 2267435 3402461 := bbase (se 3 (by rfl) ⟨637961, by rfl⟩ : syracuseStep 3402461 = 1275923) (by norm_num)
theorem B2268307 : Blo 2267435 2268307 := bstep (se 1 (by rfl) ⟨1701230, by rfl⟩ : syracuseStep 2268307 = 3402461) B3402461
theorem B5103701 : Blo 2267435 5103701 := bbase (se 8 (by rfl) ⟨29904, by rfl⟩ : syracuseStep 5103701 = 59809) (by norm_num)
theorem B3402467 : Blo 2267435 3402467 := bstep (se 1 (by rfl) ⟨2551850, by rfl⟩ : syracuseStep 3402467 = 5103701) B5103701
theorem B2268311 : Blo 2267435 2268311 := bstep (se 1 (by rfl) ⟨1701233, by rfl⟩ : syracuseStep 2268311 = 3402467) B3402467
theorem B5524469 : Blo 2267435 5524469 := bbase (se 5 (by rfl) ⟨258959, by rfl⟩ : syracuseStep 5524469 = 517919) (by norm_num)
theorem B3682979 : Blo 2267435 3682979 := bstep (se 1 (by rfl) ⟨2762234, by rfl⟩ : syracuseStep 3682979 = 5524469) B5524469
theorem B2455319 : Blo 2267435 2455319 := bstep (se 1 (by rfl) ⟨1841489, by rfl⟩ : syracuseStep 2455319 = 3682979) B3682979
theorem B6547517 : Blo 2267435 6547517 := bstep (se 3 (by rfl) ⟨1227659, by rfl⟩ : syracuseStep 6547517 = 2455319) B2455319
theorem B4365011 : Blo 2267435 4365011 := bstep (se 1 (by rfl) ⟨3273758, by rfl⟩ : syracuseStep 4365011 = 6547517) B6547517
theorem B2910007 : Blo 2267435 2910007 := bstep (se 1 (by rfl) ⟨2182505, by rfl⟩ : syracuseStep 2910007 = 4365011) B4365011
theorem B3880009 : Blo 2267435 3880009 := bstep (se 2 (by rfl) ⟨1455003, by rfl⟩ : syracuseStep 3880009 = 2910007) B2910007
theorem B5173345 : Blo 2267435 5173345 := bstep (se 2 (by rfl) ⟨1940004, by rfl⟩ : syracuseStep 5173345 = 3880009) B3880009
theorem B6897793 : Blo 2267435 6897793 := bstep (se 2 (by rfl) ⟨2586672, by rfl⟩ : syracuseStep 6897793 = 5173345) B5173345
theorem B9197057 : Blo 2267435 9197057 := bstep (se 2 (by rfl) ⟨3448896, by rfl⟩ : syracuseStep 9197057 = 6897793) B6897793
theorem B6131371 : Blo 2267435 6131371 := bstep (se 1 (by rfl) ⟨4598528, by rfl⟩ : syracuseStep 6131371 = 9197057) B9197057
theorem B8175161 : Blo 2267435 8175161 := bstep (se 2 (by rfl) ⟨3065685, by rfl⟩ : syracuseStep 8175161 = 6131371) B6131371
theorem B5450107 : Blo 2267435 5450107 := bstep (se 1 (by rfl) ⟨4087580, by rfl⟩ : syracuseStep 5450107 = 8175161) B8175161
theorem B7266809 : Blo 2267435 7266809 := bstep (se 2 (by rfl) ⟨2725053, by rfl⟩ : syracuseStep 7266809 = 5450107) B5450107
theorem B4844539 : Blo 2267435 4844539 := bstep (se 1 (by rfl) ⟨3633404, by rfl⟩ : syracuseStep 4844539 = 7266809) B7266809
theorem B6459385 : Blo 2267435 6459385 := bstep (se 2 (by rfl) ⟨2422269, by rfl⟩ : syracuseStep 6459385 = 4844539) B4844539
theorem B8612513 : Blo 2267435 8612513 := bstep (se 2 (by rfl) ⟨3229692, by rfl⟩ : syracuseStep 8612513 = 6459385) B6459385
theorem B5741675 : Blo 2267435 5741675 := bstep (se 1 (by rfl) ⟨4306256, by rfl⟩ : syracuseStep 5741675 = 8612513) B8612513
theorem B3827783 : Blo 2267435 3827783 := bstep (se 1 (by rfl) ⟨2870837, by rfl⟩ : syracuseStep 3827783 = 5741675) B5741675
theorem B2551855 : Blo 2267435 2551855 := bstep (se 1 (by rfl) ⟨1913891, by rfl⟩ : syracuseStep 2551855 = 3827783) B3827783
theorem B3402473 : Blo 2267435 3402473 := bstep (se 2 (by rfl) ⟨1275927, by rfl⟩ : syracuseStep 3402473 = 2551855) B2551855
theorem B2268315 : Blo 2267435 2268315 := bstep (se 1 (by rfl) ⟨1701236, by rfl⟩ : syracuseStep 2268315 = 3402473) B3402473
theorem B8175173 : Blo 2267435 8175173 := bbase (se 4 (by rfl) ⟨766422, by rfl⟩ : syracuseStep 8175173 = 1532845) (by norm_num)
theorem B21800461 : Blo 2267435 21800461 := bstep (se 3 (by rfl) ⟨4087586, by rfl⟩ : syracuseStep 21800461 = 8175173) B8175173
theorem B29067281 : Blo 2267435 29067281 := bstep (se 2 (by rfl) ⟨10900230, by rfl⟩ : syracuseStep 29067281 = 21800461) B21800461
theorem B19378187 : Blo 2267435 19378187 := bstep (se 1 (by rfl) ⟨14533640, by rfl⟩ : syracuseStep 19378187 = 29067281) B29067281
theorem B12918791 : Blo 2267435 12918791 := bstep (se 1 (by rfl) ⟨9689093, by rfl⟩ : syracuseStep 12918791 = 19378187) B19378187
theorem B8612527 : Blo 2267435 8612527 := bstep (se 1 (by rfl) ⟨6459395, by rfl⟩ : syracuseStep 8612527 = 12918791) B12918791
theorem B11483369 : Blo 2267435 11483369 := bstep (se 2 (by rfl) ⟨4306263, by rfl⟩ : syracuseStep 11483369 = 8612527) B8612527
theorem B7655579 : Blo 2267435 7655579 := bstep (se 1 (by rfl) ⟨5741684, by rfl⟩ : syracuseStep 7655579 = 11483369) B11483369
theorem B5103719 : Blo 2267435 5103719 := bstep (se 1 (by rfl) ⟨3827789, by rfl⟩ : syracuseStep 5103719 = 7655579) B7655579
theorem B3402479 : Blo 2267435 3402479 := bstep (se 1 (by rfl) ⟨2551859, by rfl⟩ : syracuseStep 3402479 = 5103719) B5103719
theorem B2268319 : Blo 2267435 2268319 := bstep (se 1 (by rfl) ⟨1701239, by rfl⟩ : syracuseStep 2268319 = 3402479) B3402479
theorem B3402485 : Blo 2267435 3402485 := bbase (se 5 (by rfl) ⟨159491, by rfl⟩ : syracuseStep 3402485 = 318983) (by norm_num)
theorem B2268323 : Blo 2267435 2268323 := bstep (se 1 (by rfl) ⟨1701242, by rfl⟩ : syracuseStep 2268323 = 3402485) B3402485
theorem B3682997 : Blo 2267435 3682997 := bbase (se 5 (by rfl) ⟨172640, by rfl⟩ : syracuseStep 3682997 = 345281) (by norm_num)
theorem B2455331 : Blo 2267435 2455331 := bstep (se 1 (by rfl) ⟨1841498, by rfl⟩ : syracuseStep 2455331 = 3682997) B3682997
theorem B6547549 : Blo 2267435 6547549 := bstep (se 3 (by rfl) ⟨1227665, by rfl⟩ : syracuseStep 6547549 = 2455331) B2455331
theorem B8730065 : Blo 2267435 8730065 := bstep (se 2 (by rfl) ⟨3273774, by rfl⟩ : syracuseStep 8730065 = 6547549) B6547549
theorem B5820043 : Blo 2267435 5820043 := bstep (se 1 (by rfl) ⟨4365032, by rfl⟩ : syracuseStep 5820043 = 8730065) B8730065
theorem B7760057 : Blo 2267435 7760057 := bstep (se 2 (by rfl) ⟨2910021, by rfl⟩ : syracuseStep 7760057 = 5820043) B5820043
theorem B20693485 : Blo 2267435 20693485 := bstep (se 3 (by rfl) ⟨3880028, by rfl⟩ : syracuseStep 20693485 = 7760057) B7760057
theorem B27591313 : Blo 2267435 27591313 := bstep (se 2 (by rfl) ⟨10346742, by rfl⟩ : syracuseStep 27591313 = 20693485) B20693485
theorem B36788417 : Blo 2267435 36788417 := bstep (se 2 (by rfl) ⟨13795656, by rfl⟩ : syracuseStep 36788417 = 27591313) B27591313
theorem B24525611 : Blo 2267435 24525611 := bstep (se 1 (by rfl) ⟨18394208, by rfl⟩ : syracuseStep 24525611 = 36788417) B36788417
theorem B16350407 : Blo 2267435 16350407 := bstep (se 1 (by rfl) ⟨12262805, by rfl⟩ : syracuseStep 16350407 = 24525611) B24525611
theorem B10900271 : Blo 2267435 10900271 := bstep (se 1 (by rfl) ⟨8175203, by rfl⟩ : syracuseStep 10900271 = 16350407) B16350407
theorem B7266847 : Blo 2267435 7266847 := bstep (se 1 (by rfl) ⟨5450135, by rfl⟩ : syracuseStep 7266847 = 10900271) B10900271
theorem B9689129 : Blo 2267435 9689129 := bstep (se 2 (by rfl) ⟨3633423, by rfl⟩ : syracuseStep 9689129 = 7266847) B7266847
theorem B6459419 : Blo 2267435 6459419 := bstep (se 1 (by rfl) ⟨4844564, by rfl⟩ : syracuseStep 6459419 = 9689129) B9689129
theorem B4306279 : Blo 2267435 4306279 := bstep (se 1 (by rfl) ⟨3229709, by rfl⟩ : syracuseStep 4306279 = 6459419) B6459419
theorem B5741705 : Blo 2267435 5741705 := bstep (se 2 (by rfl) ⟨2153139, by rfl⟩ : syracuseStep 5741705 = 4306279) B4306279
theorem B3827803 : Blo 2267435 3827803 := bstep (se 1 (by rfl) ⟨2870852, by rfl⟩ : syracuseStep 3827803 = 5741705) B5741705
theorem B5103737 : Blo 2267435 5103737 := bstep (se 2 (by rfl) ⟨1913901, by rfl⟩ : syracuseStep 5103737 = 3827803) B3827803
theorem B3402491 : Blo 2267435 3402491 := bstep (se 1 (by rfl) ⟨2551868, by rfl⟩ : syracuseStep 3402491 = 5103737) B5103737
theorem B2268327 : Blo 2267435 2268327 := bstep (se 1 (by rfl) ⟨1701245, by rfl⟩ : syracuseStep 2268327 = 3402491) B3402491
theorem B2551873 : Blo 2267435 2551873 := bbase (se 2 (by rfl) ⟨956952, by rfl⟩ : syracuseStep 2551873 = 1913905) (by norm_num)
theorem B3402497 : Blo 2267435 3402497 := bstep (se 2 (by rfl) ⟨1275936, by rfl⟩ : syracuseStep 3402497 = 2551873) B2551873
theorem B2268331 : Blo 2267435 2268331 := bstep (se 1 (by rfl) ⟨1701248, by rfl⟩ : syracuseStep 2268331 = 3402497) B3402497
theorem B5741725 : Blo 2267435 5741725 := bbase (se 3 (by rfl) ⟨1076573, by rfl⟩ : syracuseStep 5741725 = 2153147) (by norm_num)
theorem B7655633 : Blo 2267435 7655633 := bstep (se 2 (by rfl) ⟨2870862, by rfl⟩ : syracuseStep 7655633 = 5741725) B5741725
theorem B5103755 : Blo 2267435 5103755 := bstep (se 1 (by rfl) ⟨3827816, by rfl⟩ : syracuseStep 5103755 = 7655633) B7655633
theorem B3402503 : Blo 2267435 3402503 := bstep (se 1 (by rfl) ⟨2551877, by rfl⟩ : syracuseStep 3402503 = 5103755) B5103755
theorem B2268335 : Blo 2267435 2268335 := bstep (se 1 (by rfl) ⟨1701251, by rfl⟩ : syracuseStep 2268335 = 3402503) B3402503
theorem B3402509 : Blo 2267435 3402509 := bbase (se 3 (by rfl) ⟨637970, by rfl⟩ : syracuseStep 3402509 = 1275941) (by norm_num)
theorem B2268339 : Blo 2267435 2268339 := bstep (se 1 (by rfl) ⟨1701254, by rfl⟩ : syracuseStep 2268339 = 3402509) B3402509
theorem B5103773 : Blo 2267435 5103773 := bbase (se 3 (by rfl) ⟨956957, by rfl⟩ : syracuseStep 5103773 = 1913915) (by norm_num)
theorem B3402515 : Blo 2267435 3402515 := bstep (se 1 (by rfl) ⟨2551886, by rfl⟩ : syracuseStep 3402515 = 5103773) B5103773
theorem B2268343 : Blo 2267435 2268343 := bstep (se 1 (by rfl) ⟨1701257, by rfl⟩ : syracuseStep 2268343 = 3402515) B3402515
theorem B3827837 : Blo 2267435 3827837 := bbase (se 3 (by rfl) ⟨717719, by rfl⟩ : syracuseStep 3827837 = 1435439) (by norm_num)
theorem B2551891 : Blo 2267435 2551891 := bstep (se 1 (by rfl) ⟨1913918, by rfl⟩ : syracuseStep 2551891 = 3827837) B3827837
theorem B3402521 : Blo 2267435 3402521 := bstep (se 2 (by rfl) ⟨1275945, by rfl⟩ : syracuseStep 3402521 = 2551891) B2551891
theorem B2268347 : Blo 2267435 2268347 := bstep (se 1 (by rfl) ⟨1701260, by rfl⟩ : syracuseStep 2268347 = 3402521) B3402521
theorem B2586713 : Blo 2267435 2586713 := bbase (se 2 (by rfl) ⟨970017, by rfl⟩ : syracuseStep 2586713 = 1940035) (by norm_num)
theorem B6897901 : Blo 2267435 6897901 := bstep (se 3 (by rfl) ⟨1293356, by rfl⟩ : syracuseStep 6897901 = 2586713) B2586713
theorem B9197201 : Blo 2267435 9197201 := bstep (se 2 (by rfl) ⟨3448950, by rfl⟩ : syracuseStep 9197201 = 6897901) B6897901
theorem B6131467 : Blo 2267435 6131467 := bstep (se 1 (by rfl) ⟨4598600, by rfl⟩ : syracuseStep 6131467 = 9197201) B9197201
theorem B8175289 : Blo 2267435 8175289 := bstep (se 2 (by rfl) ⟨3065733, by rfl⟩ : syracuseStep 8175289 = 6131467) B6131467
theorem B10900385 : Blo 2267435 10900385 := bstep (se 2 (by rfl) ⟨4087644, by rfl⟩ : syracuseStep 10900385 = 8175289) B8175289
theorem B7266923 : Blo 2267435 7266923 := bstep (se 1 (by rfl) ⟨5450192, by rfl⟩ : syracuseStep 7266923 = 10900385) B10900385
theorem B4844615 : Blo 2267435 4844615 := bstep (se 1 (by rfl) ⟨3633461, by rfl⟩ : syracuseStep 4844615 = 7266923) B7266923
theorem B12918973 : Blo 2267435 12918973 := bstep (se 3 (by rfl) ⟨2422307, by rfl⟩ : syracuseStep 12918973 = 4844615) B4844615
theorem B17225297 : Blo 2267435 17225297 := bstep (se 2 (by rfl) ⟨6459486, by rfl⟩ : syracuseStep 17225297 = 12918973) B12918973
theorem B11483531 : Blo 2267435 11483531 := bstep (se 1 (by rfl) ⟨8612648, by rfl⟩ : syracuseStep 11483531 = 17225297) B17225297
theorem B7655687 : Blo 2267435 7655687 := bstep (se 1 (by rfl) ⟨5741765, by rfl⟩ : syracuseStep 7655687 = 11483531) B11483531
theorem B5103791 : Blo 2267435 5103791 := bstep (se 1 (by rfl) ⟨3827843, by rfl⟩ : syracuseStep 5103791 = 7655687) B7655687
theorem B3402527 : Blo 2267435 3402527 := bstep (se 1 (by rfl) ⟨2551895, by rfl⟩ : syracuseStep 3402527 = 5103791) B5103791
theorem B2268351 : Blo 2267435 2268351 := bstep (se 1 (by rfl) ⟨1701263, by rfl⟩ : syracuseStep 2268351 = 3402527) B3402527
theorem B3402533 : Blo 2267435 3402533 := bbase (se 4 (by rfl) ⟨318987, by rfl⟩ : syracuseStep 3402533 = 637975) (by norm_num)
theorem B2268355 : Blo 2267435 2268355 := bstep (se 1 (by rfl) ⟨1701266, by rfl⟩ : syracuseStep 2268355 = 3402533) B3402533
theorem B2870893 : Blo 2267435 2870893 := bbase (se 3 (by rfl) ⟨538292, by rfl⟩ : syracuseStep 2870893 = 1076585) (by norm_num)
theorem B3827857 : Blo 2267435 3827857 := bstep (se 2 (by rfl) ⟨1435446, by rfl⟩ : syracuseStep 3827857 = 2870893) B2870893
theorem B5103809 : Blo 2267435 5103809 := bstep (se 2 (by rfl) ⟨1913928, by rfl⟩ : syracuseStep 5103809 = 3827857) B3827857
theorem B3402539 : Blo 2267435 3402539 := bstep (se 1 (by rfl) ⟨2551904, by rfl⟩ : syracuseStep 3402539 = 5103809) B5103809
theorem B2268359 : Blo 2267435 2268359 := bstep (se 1 (by rfl) ⟨1701269, by rfl⟩ : syracuseStep 2268359 = 3402539) B3402539
theorem B2551909 : Blo 2267435 2551909 := bbase (se 4 (by rfl) ⟨239241, by rfl⟩ : syracuseStep 2551909 = 478483) (by norm_num)
theorem B3402545 : Blo 2267435 3402545 := bstep (se 2 (by rfl) ⟨1275954, by rfl⟩ : syracuseStep 3402545 = 2551909) B2551909
theorem B2268363 : Blo 2267435 2268363 := bstep (se 1 (by rfl) ⟨1701272, by rfl⟩ : syracuseStep 2268363 = 3402545) B3402545
theorem B2422325 : Blo 2267435 2422325 := bbase (se 5 (by rfl) ⟨113546, by rfl⟩ : syracuseStep 2422325 = 227093) (by norm_num)
theorem B6459533 : Blo 2267435 6459533 := bstep (se 3 (by rfl) ⟨1211162, by rfl⟩ : syracuseStep 6459533 = 2422325) B2422325
theorem B4306355 : Blo 2267435 4306355 := bstep (se 1 (by rfl) ⟨3229766, by rfl⟩ : syracuseStep 4306355 = 6459533) B6459533
theorem B2870903 : Blo 2267435 2870903 := bstep (se 1 (by rfl) ⟨2153177, by rfl⟩ : syracuseStep 2870903 = 4306355) B4306355
theorem B7655741 : Blo 2267435 7655741 := bstep (se 3 (by rfl) ⟨1435451, by rfl⟩ : syracuseStep 7655741 = 2870903) B2870903
theorem B5103827 : Blo 2267435 5103827 := bstep (se 1 (by rfl) ⟨3827870, by rfl⟩ : syracuseStep 5103827 = 7655741) B7655741
theorem B3402551 : Blo 2267435 3402551 := bstep (se 1 (by rfl) ⟨2551913, by rfl⟩ : syracuseStep 3402551 = 5103827) B5103827
theorem B2268367 : Blo 2267435 2268367 := bstep (se 1 (by rfl) ⟨1701275, by rfl⟩ : syracuseStep 2268367 = 3402551) B3402551
theorem B3402557 : Blo 2267435 3402557 := bbase (se 3 (by rfl) ⟨637979, by rfl⟩ : syracuseStep 3402557 = 1275959) (by norm_num)
theorem B2268371 : Blo 2267435 2268371 := bstep (se 1 (by rfl) ⟨1701278, by rfl⟩ : syracuseStep 2268371 = 3402557) B3402557
theorem B5103845 : Blo 2267435 5103845 := bbase (se 4 (by rfl) ⟨478485, by rfl⟩ : syracuseStep 5103845 = 956971) (by norm_num)
theorem B3402563 : Blo 2267435 3402563 := bstep (se 1 (by rfl) ⟨2551922, by rfl⟩ : syracuseStep 3402563 = 5103845) B5103845
theorem B2268375 : Blo 2267435 2268375 := bstep (se 1 (by rfl) ⟨1701281, by rfl⟩ : syracuseStep 2268375 = 3402563) B3402563
theorem B5741837 : Blo 2267435 5741837 := bbase (se 3 (by rfl) ⟨1076594, by rfl⟩ : syracuseStep 5741837 = 2153189) (by norm_num)
theorem B3827891 : Blo 2267435 3827891 := bstep (se 1 (by rfl) ⟨2870918, by rfl⟩ : syracuseStep 3827891 = 5741837) B5741837
theorem B2551927 : Blo 2267435 2551927 := bstep (se 1 (by rfl) ⟨1913945, by rfl⟩ : syracuseStep 2551927 = 3827891) B3827891
theorem B3402569 : Blo 2267435 3402569 := bstep (se 2 (by rfl) ⟨1275963, by rfl⟩ : syracuseStep 3402569 = 2551927) B2551927
theorem B2268379 : Blo 2267435 2268379 := bstep (se 1 (by rfl) ⟨1701284, by rfl⟩ : syracuseStep 2268379 = 3402569) B3402569
theorem B3229789 : Blo 2267435 3229789 := bbase (se 3 (by rfl) ⟨605585, by rfl⟩ : syracuseStep 3229789 = 1211171) (by norm_num)
theorem B4306385 : Blo 2267435 4306385 := bstep (se 2 (by rfl) ⟨1614894, by rfl⟩ : syracuseStep 4306385 = 3229789) B3229789
theorem B11483693 : Blo 2267435 11483693 := bstep (se 3 (by rfl) ⟨2153192, by rfl⟩ : syracuseStep 11483693 = 4306385) B4306385
theorem B7655795 : Blo 2267435 7655795 := bstep (se 1 (by rfl) ⟨5741846, by rfl⟩ : syracuseStep 7655795 = 11483693) B11483693
theorem B5103863 : Blo 2267435 5103863 := bstep (se 1 (by rfl) ⟨3827897, by rfl⟩ : syracuseStep 5103863 = 7655795) B7655795
theorem B3402575 : Blo 2267435 3402575 := bstep (se 1 (by rfl) ⟨2551931, by rfl⟩ : syracuseStep 3402575 = 5103863) B5103863
theorem B2268383 : Blo 2267435 2268383 := bstep (se 1 (by rfl) ⟨1701287, by rfl⟩ : syracuseStep 2268383 = 3402575) B3402575
theorem B3402581 : Blo 2267435 3402581 := bbase (se 9 (by rfl) ⟨9968, by rfl⟩ : syracuseStep 3402581 = 19937) (by norm_num)
theorem B2268387 : Blo 2267435 2268387 := bstep (se 1 (by rfl) ⟨1701290, by rfl⟩ : syracuseStep 2268387 = 3402581) B3402581
theorem B4844701 : Blo 2267435 4844701 := bbase (se 3 (by rfl) ⟨908381, by rfl⟩ : syracuseStep 4844701 = 1816763) (by norm_num)
theorem B6459601 : Blo 2267435 6459601 := bstep (se 2 (by rfl) ⟨2422350, by rfl⟩ : syracuseStep 6459601 = 4844701) B4844701
theorem B8612801 : Blo 2267435 8612801 := bstep (se 2 (by rfl) ⟨3229800, by rfl⟩ : syracuseStep 8612801 = 6459601) B6459601
theorem B5741867 : Blo 2267435 5741867 := bstep (se 1 (by rfl) ⟨4306400, by rfl⟩ : syracuseStep 5741867 = 8612801) B8612801
theorem B3827911 : Blo 2267435 3827911 := bstep (se 1 (by rfl) ⟨2870933, by rfl⟩ : syracuseStep 3827911 = 5741867) B5741867
theorem B5103881 : Blo 2267435 5103881 := bstep (se 2 (by rfl) ⟨1913955, by rfl⟩ : syracuseStep 5103881 = 3827911) B3827911
theorem B3402587 : Blo 2267435 3402587 := bstep (se 1 (by rfl) ⟨2551940, by rfl⟩ : syracuseStep 3402587 = 5103881) B5103881
theorem B2268391 : Blo 2267435 2268391 := bstep (se 1 (by rfl) ⟨1701293, by rfl⟩ : syracuseStep 2268391 = 3402587) B3402587
theorem B2551945 : Blo 2267435 2551945 := bbase (se 2 (by rfl) ⟨956979, by rfl⟩ : syracuseStep 2551945 = 1913959) (by norm_num)
theorem B3402593 : Blo 2267435 3402593 := bstep (se 2 (by rfl) ⟨1275972, by rfl⟩ : syracuseStep 3402593 = 2551945) B2551945
theorem B2268395 : Blo 2267435 2268395 := bstep (se 1 (by rfl) ⟨1701296, by rfl⟩ : syracuseStep 2268395 = 3402593) B3402593
theorem B2622061 : Blo 2267435 2622061 := bbase (se 3 (by rfl) ⟨491636, by rfl⟩ : syracuseStep 2622061 = 983273) (by norm_num)
theorem B13984325 : Blo 2267435 13984325 := bstep (se 4 (by rfl) ⟨1311030, by rfl⟩ : syracuseStep 13984325 = 2622061) B2622061
theorem B9322883 : Blo 2267435 9322883 := bstep (se 1 (by rfl) ⟨6992162, by rfl⟩ : syracuseStep 9322883 = 13984325) B13984325
theorem B6215255 : Blo 2267435 6215255 := bstep (se 1 (by rfl) ⟨4661441, by rfl⟩ : syracuseStep 6215255 = 9322883) B9322883
theorem B4143503 : Blo 2267435 4143503 := bstep (se 1 (by rfl) ⟨3107627, by rfl⟩ : syracuseStep 4143503 = 6215255) B6215255
theorem B2762335 : Blo 2267435 2762335 := bstep (se 1 (by rfl) ⟨2071751, by rfl⟩ : syracuseStep 2762335 = 4143503) B4143503
theorem B3683113 : Blo 2267435 3683113 := bstep (se 2 (by rfl) ⟨1381167, by rfl⟩ : syracuseStep 3683113 = 2762335) B2762335
theorem B19643269 : Blo 2267435 19643269 := bstep (se 4 (by rfl) ⟨1841556, by rfl⟩ : syracuseStep 19643269 = 3683113) B3683113
theorem B26191025 : Blo 2267435 26191025 := bstep (se 2 (by rfl) ⟨9821634, by rfl⟩ : syracuseStep 26191025 = 19643269) B19643269
theorem B17460683 : Blo 2267435 17460683 := bstep (se 1 (by rfl) ⟨13095512, by rfl⟩ : syracuseStep 17460683 = 26191025) B26191025
theorem B11640455 : Blo 2267435 11640455 := bstep (se 1 (by rfl) ⟨8730341, by rfl⟩ : syracuseStep 11640455 = 17460683) B17460683
theorem B7760303 : Blo 2267435 7760303 := bstep (se 1 (by rfl) ⟨5820227, by rfl⟩ : syracuseStep 7760303 = 11640455) B11640455
theorem B5173535 : Blo 2267435 5173535 := bstep (se 1 (by rfl) ⟨3880151, by rfl⟩ : syracuseStep 5173535 = 7760303) B7760303
theorem B3449023 : Blo 2267435 3449023 := bstep (se 1 (by rfl) ⟨2586767, by rfl⟩ : syracuseStep 3449023 = 5173535) B5173535
theorem B18394789 : Blo 2267435 18394789 := bstep (se 4 (by rfl) ⟨1724511, by rfl⟩ : syracuseStep 18394789 = 3449023) B3449023
theorem B24526385 : Blo 2267435 24526385 := bstep (se 2 (by rfl) ⟨9197394, by rfl⟩ : syracuseStep 24526385 = 18394789) B18394789
theorem B16350923 : Blo 2267435 16350923 := bstep (se 1 (by rfl) ⟨12263192, by rfl⟩ : syracuseStep 16350923 = 24526385) B24526385
theorem B43602461 : Blo 2267435 43602461 := bstep (se 3 (by rfl) ⟨8175461, by rfl⟩ : syracuseStep 43602461 = 16350923) B16350923
theorem B29068307 : Blo 2267435 29068307 := bstep (se 1 (by rfl) ⟨21801230, by rfl⟩ : syracuseStep 29068307 = 43602461) B43602461
theorem B19378871 : Blo 2267435 19378871 := bstep (se 1 (by rfl) ⟨14534153, by rfl⟩ : syracuseStep 19378871 = 29068307) B29068307
theorem B12919247 : Blo 2267435 12919247 := bstep (se 1 (by rfl) ⟨9689435, by rfl⟩ : syracuseStep 12919247 = 19378871) B19378871
theorem B8612831 : Blo 2267435 8612831 := bstep (se 1 (by rfl) ⟨6459623, by rfl⟩ : syracuseStep 8612831 = 12919247) B12919247
theorem B5741887 : Blo 2267435 5741887 := bstep (se 1 (by rfl) ⟨4306415, by rfl⟩ : syracuseStep 5741887 = 8612831) B8612831
theorem B7655849 : Blo 2267435 7655849 := bstep (se 2 (by rfl) ⟨2870943, by rfl⟩ : syracuseStep 7655849 = 5741887) B5741887
theorem B5103899 : Blo 2267435 5103899 := bstep (se 1 (by rfl) ⟨3827924, by rfl⟩ : syracuseStep 5103899 = 7655849) B7655849
theorem B3402599 : Blo 2267435 3402599 := bstep (se 1 (by rfl) ⟨2551949, by rfl⟩ : syracuseStep 3402599 = 5103899) B5103899
theorem B2268399 : Blo 2267435 2268399 := bstep (se 1 (by rfl) ⟨1701299, by rfl⟩ : syracuseStep 2268399 = 3402599) B3402599
theorem B3402605 : Blo 2267435 3402605 := bbase (se 3 (by rfl) ⟨637988, by rfl⟩ : syracuseStep 3402605 = 1275977) (by norm_num)
theorem B2268403 : Blo 2267435 2268403 := bstep (se 1 (by rfl) ⟨1701302, by rfl⟩ : syracuseStep 2268403 = 3402605) B3402605
theorem B5103917 : Blo 2267435 5103917 := bbase (se 3 (by rfl) ⟨956984, by rfl⟩ : syracuseStep 5103917 = 1913969) (by norm_num)
theorem B3402611 : Blo 2267435 3402611 := bstep (se 1 (by rfl) ⟨2551958, by rfl⟩ : syracuseStep 3402611 = 5103917) B5103917
theorem B2268407 : Blo 2267435 2268407 := bstep (se 1 (by rfl) ⟨1701305, by rfl⟩ : syracuseStep 2268407 = 3402611) B3402611
theorem B2725169 : Blo 2267435 2725169 := bbase (se 2 (by rfl) ⟨1021938, by rfl⟩ : syracuseStep 2725169 = 2043877) (by norm_num)
theorem B7267117 : Blo 2267435 7267117 := bstep (se 3 (by rfl) ⟨1362584, by rfl⟩ : syracuseStep 7267117 = 2725169) B2725169
theorem B9689489 : Blo 2267435 9689489 := bstep (se 2 (by rfl) ⟨3633558, by rfl⟩ : syracuseStep 9689489 = 7267117) B7267117
theorem B6459659 : Blo 2267435 6459659 := bstep (se 1 (by rfl) ⟨4844744, by rfl⟩ : syracuseStep 6459659 = 9689489) B9689489
theorem B4306439 : Blo 2267435 4306439 := bstep (se 1 (by rfl) ⟨3229829, by rfl⟩ : syracuseStep 4306439 = 6459659) B6459659
theorem B2870959 : Blo 2267435 2870959 := bstep (se 1 (by rfl) ⟨2153219, by rfl⟩ : syracuseStep 2870959 = 4306439) B4306439
theorem B3827945 : Blo 2267435 3827945 := bstep (se 2 (by rfl) ⟨1435479, by rfl⟩ : syracuseStep 3827945 = 2870959) B2870959
theorem B2551963 : Blo 2267435 2551963 := bstep (se 1 (by rfl) ⟨1913972, by rfl⟩ : syracuseStep 2551963 = 3827945) B3827945
theorem B3402617 : Blo 2267435 3402617 := bstep (se 2 (by rfl) ⟨1275981, by rfl⟩ : syracuseStep 3402617 = 2551963) B2551963
theorem B2268411 : Blo 2267435 2268411 := bstep (se 1 (by rfl) ⟨1701308, by rfl⟩ : syracuseStep 2268411 = 3402617) B3402617
theorem B41388565 : Blo 2267435 41388565 := bbase (se 6 (by rfl) ⟨970044, by rfl⟩ : syracuseStep 41388565 = 1940089) (by norm_num)
theorem B55184753 : Blo 2267435 55184753 := bstep (se 2 (by rfl) ⟨20694282, by rfl⟩ : syracuseStep 55184753 = 41388565) B41388565
theorem B36789835 : Blo 2267435 36789835 := bstep (se 1 (by rfl) ⟨27592376, by rfl⟩ : syracuseStep 36789835 = 55184753) B55184753
theorem B49053113 : Blo 2267435 49053113 := bstep (se 2 (by rfl) ⟨18394917, by rfl⟩ : syracuseStep 49053113 = 36789835) B36789835
theorem B32702075 : Blo 2267435 32702075 := bstep (se 1 (by rfl) ⟨24526556, by rfl⟩ : syracuseStep 32702075 = 49053113) B49053113
theorem B21801383 : Blo 2267435 21801383 := bstep (se 1 (by rfl) ⟨16351037, by rfl⟩ : syracuseStep 21801383 = 32702075) B32702075
theorem B14534255 : Blo 2267435 14534255 := bstep (se 1 (by rfl) ⟨10900691, by rfl⟩ : syracuseStep 14534255 = 21801383) B21801383
theorem B38758013 : Blo 2267435 38758013 := bstep (se 3 (by rfl) ⟨7267127, by rfl⟩ : syracuseStep 38758013 = 14534255) B14534255
theorem B25838675 : Blo 2267435 25838675 := bstep (se 1 (by rfl) ⟨19379006, by rfl⟩ : syracuseStep 25838675 = 38758013) B38758013
theorem B17225783 : Blo 2267435 17225783 := bstep (se 1 (by rfl) ⟨12919337, by rfl⟩ : syracuseStep 17225783 = 25838675) B25838675
theorem B11483855 : Blo 2267435 11483855 := bstep (se 1 (by rfl) ⟨8612891, by rfl⟩ : syracuseStep 11483855 = 17225783) B17225783
theorem B7655903 : Blo 2267435 7655903 := bstep (se 1 (by rfl) ⟨5741927, by rfl⟩ : syracuseStep 7655903 = 11483855) B11483855
theorem B5103935 : Blo 2267435 5103935 := bstep (se 1 (by rfl) ⟨3827951, by rfl⟩ : syracuseStep 5103935 = 7655903) B7655903
theorem B3402623 : Blo 2267435 3402623 := bstep (se 1 (by rfl) ⟨2551967, by rfl⟩ : syracuseStep 3402623 = 5103935) B5103935
theorem B2268415 : Blo 2267435 2268415 := bstep (se 1 (by rfl) ⟨1701311, by rfl⟩ : syracuseStep 2268415 = 3402623) B3402623
theorem B3402629 : Blo 2267435 3402629 := bbase (se 4 (by rfl) ⟨318996, by rfl⟩ : syracuseStep 3402629 = 637993) (by norm_num)
theorem B2268419 : Blo 2267435 2268419 := bstep (se 1 (by rfl) ⟨1701314, by rfl⟩ : syracuseStep 2268419 = 3402629) B3402629
theorem B3827965 : Blo 2267435 3827965 := bbase (se 3 (by rfl) ⟨717743, by rfl⟩ : syracuseStep 3827965 = 1435487) (by norm_num)
theorem B5103953 : Blo 2267435 5103953 := bstep (se 2 (by rfl) ⟨1913982, by rfl⟩ : syracuseStep 5103953 = 3827965) B3827965
theorem B3402635 : Blo 2267435 3402635 := bstep (se 1 (by rfl) ⟨2551976, by rfl⟩ : syracuseStep 3402635 = 5103953) B5103953
theorem B2268423 : Blo 2267435 2268423 := bstep (se 1 (by rfl) ⟨1701317, by rfl⟩ : syracuseStep 2268423 = 3402635) B3402635
theorem B2551981 : Blo 2267435 2551981 := bbase (se 3 (by rfl) ⟨478496, by rfl⟩ : syracuseStep 2551981 = 956993) (by norm_num)
theorem B3402641 : Blo 2267435 3402641 := bstep (se 2 (by rfl) ⟨1275990, by rfl⟩ : syracuseStep 3402641 = 2551981) B2551981
theorem B2268427 : Blo 2267435 2268427 := bstep (se 1 (by rfl) ⟨1701320, by rfl⟩ : syracuseStep 2268427 = 3402641) B3402641
theorem B7655957 : Blo 2267435 7655957 := bbase (se 6 (by rfl) ⟨179436, by rfl⟩ : syracuseStep 7655957 = 358873) (by norm_num)
theorem B5103971 : Blo 2267435 5103971 := bstep (se 1 (by rfl) ⟨3827978, by rfl⟩ : syracuseStep 5103971 = 7655957) B7655957
theorem B3402647 : Blo 2267435 3402647 := bstep (se 1 (by rfl) ⟨2551985, by rfl⟩ : syracuseStep 3402647 = 5103971) B5103971
theorem B2268431 : Blo 2267435 2268431 := bstep (se 1 (by rfl) ⟨1701323, by rfl⟩ : syracuseStep 2268431 = 3402647) B3402647
theorem B3402653 : Blo 2267435 3402653 := bbase (se 3 (by rfl) ⟨637997, by rfl⟩ : syracuseStep 3402653 = 1275995) (by norm_num)
theorem B2268435 : Blo 2267435 2268435 := bstep (se 1 (by rfl) ⟨1701326, by rfl⟩ : syracuseStep 2268435 = 3402653) B3402653
theorem B5103989 : Blo 2267435 5103989 := bbase (se 5 (by rfl) ⟨239249, by rfl⟩ : syracuseStep 5103989 = 478499) (by norm_num)
theorem B3402659 : Blo 2267435 3402659 := bstep (se 1 (by rfl) ⟨2551994, by rfl⟩ : syracuseStep 3402659 = 5103989) B5103989
theorem B2268439 : Blo 2267435 2268439 := bstep (se 1 (by rfl) ⟨1701329, by rfl⟩ : syracuseStep 2268439 = 3402659) B3402659
theorem B6131717 : Blo 2267435 6131717 := bbase (se 4 (by rfl) ⟨574848, by rfl⟩ : syracuseStep 6131717 = 1149697) (by norm_num)
theorem B4087811 : Blo 2267435 4087811 := bstep (se 1 (by rfl) ⟨3065858, by rfl⟩ : syracuseStep 4087811 = 6131717) B6131717
theorem B2725207 : Blo 2267435 2725207 := bstep (se 1 (by rfl) ⟨2043905, by rfl⟩ : syracuseStep 2725207 = 4087811) B4087811
theorem B14534437 : Blo 2267435 14534437 := bstep (se 4 (by rfl) ⟨1362603, by rfl⟩ : syracuseStep 14534437 = 2725207) B2725207
theorem B19379249 : Blo 2267435 19379249 := bstep (se 2 (by rfl) ⟨7267218, by rfl⟩ : syracuseStep 19379249 = 14534437) B14534437
theorem B12919499 : Blo 2267435 12919499 := bstep (se 1 (by rfl) ⟨9689624, by rfl⟩ : syracuseStep 12919499 = 19379249) B19379249
theorem B8612999 : Blo 2267435 8612999 := bstep (se 1 (by rfl) ⟨6459749, by rfl⟩ : syracuseStep 8612999 = 12919499) B12919499
theorem B5741999 : Blo 2267435 5741999 := bstep (se 1 (by rfl) ⟨4306499, by rfl⟩ : syracuseStep 5741999 = 8612999) B8612999
theorem B3827999 : Blo 2267435 3827999 := bstep (se 1 (by rfl) ⟨2870999, by rfl⟩ : syracuseStep 3827999 = 5741999) B5741999
theorem B2551999 : Blo 2267435 2551999 := bstep (se 1 (by rfl) ⟨1913999, by rfl⟩ : syracuseStep 2551999 = 3827999) B3827999
theorem B3402665 : Blo 2267435 3402665 := bstep (se 2 (by rfl) ⟨1275999, by rfl⟩ : syracuseStep 3402665 = 2551999) B2551999
theorem B2268443 : Blo 2267435 2268443 := bstep (se 1 (by rfl) ⟨1701332, by rfl⟩ : syracuseStep 2268443 = 3402665) B3402665
theorem B8613013 : Blo 2267435 8613013 := bbase (se 6 (by rfl) ⟨201867, by rfl⟩ : syracuseStep 8613013 = 403735) (by norm_num)
theorem B11484017 : Blo 2267435 11484017 := bstep (se 2 (by rfl) ⟨4306506, by rfl⟩ : syracuseStep 11484017 = 8613013) B8613013
theorem B7656011 : Blo 2267435 7656011 := bstep (se 1 (by rfl) ⟨5742008, by rfl⟩ : syracuseStep 7656011 = 11484017) B11484017
theorem B5104007 : Blo 2267435 5104007 := bstep (se 1 (by rfl) ⟨3828005, by rfl⟩ : syracuseStep 5104007 = 7656011) B7656011
theorem B3402671 : Blo 2267435 3402671 := bstep (se 1 (by rfl) ⟨2552003, by rfl⟩ : syracuseStep 3402671 = 5104007) B5104007
theorem B2268447 : Blo 2267435 2268447 := bstep (se 1 (by rfl) ⟨1701335, by rfl⟩ : syracuseStep 2268447 = 3402671) B3402671
theorem B3402677 : Blo 2267435 3402677 := bbase (se 5 (by rfl) ⟨159500, by rfl⟩ : syracuseStep 3402677 = 319001) (by norm_num)
theorem B2268451 : Blo 2267435 2268451 := bstep (se 1 (by rfl) ⟨1701338, by rfl⟩ : syracuseStep 2268451 = 3402677) B3402677
theorem B5742029 : Blo 2267435 5742029 := bbase (se 3 (by rfl) ⟨1076630, by rfl⟩ : syracuseStep 5742029 = 2153261) (by norm_num)
theorem B3828019 : Blo 2267435 3828019 := bstep (se 1 (by rfl) ⟨2871014, by rfl⟩ : syracuseStep 3828019 = 5742029) B5742029
theorem B5104025 : Blo 2267435 5104025 := bstep (se 2 (by rfl) ⟨1914009, by rfl⟩ : syracuseStep 5104025 = 3828019) B3828019
theorem B3402683 : Blo 2267435 3402683 := bstep (se 1 (by rfl) ⟨2552012, by rfl⟩ : syracuseStep 3402683 = 5104025) B5104025
theorem B2268455 : Blo 2267435 2268455 := bstep (se 1 (by rfl) ⟨1701341, by rfl⟩ : syracuseStep 2268455 = 3402683) B3402683
theorem B2552017 : Blo 2267435 2552017 := bbase (se 2 (by rfl) ⟨957006, by rfl⟩ : syracuseStep 2552017 = 1914013) (by norm_num)
theorem B3402689 : Blo 2267435 3402689 := bstep (se 2 (by rfl) ⟨1276008, by rfl⟩ : syracuseStep 3402689 = 2552017) B2552017
theorem B2268459 : Blo 2267435 2268459 := bstep (se 1 (by rfl) ⟨1701344, by rfl⟩ : syracuseStep 2268459 = 3402689) B3402689
theorem B10347365 : Blo 2267435 10347365 := bbase (se 4 (by rfl) ⟨970065, by rfl⟩ : syracuseStep 10347365 = 1940131) (by norm_num)
theorem B6898243 : Blo 2267435 6898243 := bstep (se 1 (by rfl) ⟨5173682, by rfl⟩ : syracuseStep 6898243 = 10347365) B10347365
theorem B9197657 : Blo 2267435 9197657 := bstep (se 2 (by rfl) ⟨3449121, by rfl⟩ : syracuseStep 9197657 = 6898243) B6898243
theorem B6131771 : Blo 2267435 6131771 := bstep (se 1 (by rfl) ⟨4598828, by rfl⟩ : syracuseStep 6131771 = 9197657) B9197657
theorem B4087847 : Blo 2267435 4087847 := bstep (se 1 (by rfl) ⟨3065885, by rfl⟩ : syracuseStep 4087847 = 6131771) B6131771
theorem B10900925 : Blo 2267435 10900925 := bstep (se 3 (by rfl) ⟨2043923, by rfl⟩ : syracuseStep 10900925 = 4087847) B4087847
theorem B7267283 : Blo 2267435 7267283 := bstep (se 1 (by rfl) ⟨5450462, by rfl⟩ : syracuseStep 7267283 = 10900925) B10900925
theorem B4844855 : Blo 2267435 4844855 := bstep (se 1 (by rfl) ⟨3633641, by rfl⟩ : syracuseStep 4844855 = 7267283) B7267283
theorem B3229903 : Blo 2267435 3229903 := bstep (se 1 (by rfl) ⟨2422427, by rfl⟩ : syracuseStep 3229903 = 4844855) B4844855
theorem B4306537 : Blo 2267435 4306537 := bstep (se 2 (by rfl) ⟨1614951, by rfl⟩ : syracuseStep 4306537 = 3229903) B3229903
theorem B5742049 : Blo 2267435 5742049 := bstep (se 2 (by rfl) ⟨2153268, by rfl⟩ : syracuseStep 5742049 = 4306537) B4306537
theorem B7656065 : Blo 2267435 7656065 := bstep (se 2 (by rfl) ⟨2871024, by rfl⟩ : syracuseStep 7656065 = 5742049) B5742049
theorem B5104043 : Blo 2267435 5104043 := bstep (se 1 (by rfl) ⟨3828032, by rfl⟩ : syracuseStep 5104043 = 7656065) B7656065
theorem B3402695 : Blo 2267435 3402695 := bstep (se 1 (by rfl) ⟨2552021, by rfl⟩ : syracuseStep 3402695 = 5104043) B5104043
theorem B2268463 : Blo 2267435 2268463 := bstep (se 1 (by rfl) ⟨1701347, by rfl⟩ : syracuseStep 2268463 = 3402695) B3402695
theorem B3402701 : Blo 2267435 3402701 := bbase (se 3 (by rfl) ⟨638006, by rfl⟩ : syracuseStep 3402701 = 1276013) (by norm_num)
theorem B2268467 : Blo 2267435 2268467 := bstep (se 1 (by rfl) ⟨1701350, by rfl⟩ : syracuseStep 2268467 = 3402701) B3402701
theorem B5104061 : Blo 2267435 5104061 := bbase (se 3 (by rfl) ⟨957011, by rfl⟩ : syracuseStep 5104061 = 1914023) (by norm_num)
theorem B3402707 : Blo 2267435 3402707 := bstep (se 1 (by rfl) ⟨2552030, by rfl⟩ : syracuseStep 3402707 = 5104061) B5104061
theorem B2268471 : Blo 2267435 2268471 := bstep (se 1 (by rfl) ⟨1701353, by rfl⟩ : syracuseStep 2268471 = 3402707) B3402707
theorem B3828053 : Blo 2267435 3828053 := bbase (se 10 (by rfl) ⟨5607, by rfl⟩ : syracuseStep 3828053 = 11215) (by norm_num)
theorem B2552035 : Blo 2267435 2552035 := bstep (se 1 (by rfl) ⟨1914026, by rfl⟩ : syracuseStep 2552035 = 3828053) B3828053
theorem B3402713 : Blo 2267435 3402713 := bstep (se 2 (by rfl) ⟨1276017, by rfl⟩ : syracuseStep 3402713 = 2552035) B2552035
theorem B2268475 : Blo 2267435 2268475 := bstep (se 1 (by rfl) ⟨1701356, by rfl⟩ : syracuseStep 2268475 = 3402713) B3402713
theorem B7267333 : Blo 2267435 7267333 := bbase (se 4 (by rfl) ⟨681312, by rfl⟩ : syracuseStep 7267333 = 1362625) (by norm_num)
theorem B9689777 : Blo 2267435 9689777 := bstep (se 2 (by rfl) ⟨3633666, by rfl⟩ : syracuseStep 9689777 = 7267333) B7267333
theorem B6459851 : Blo 2267435 6459851 := bstep (se 1 (by rfl) ⟨4844888, by rfl⟩ : syracuseStep 6459851 = 9689777) B9689777
theorem B17226269 : Blo 2267435 17226269 := bstep (se 3 (by rfl) ⟨3229925, by rfl⟩ : syracuseStep 17226269 = 6459851) B6459851
theorem B11484179 : Blo 2267435 11484179 := bstep (se 1 (by rfl) ⟨8613134, by rfl⟩ : syracuseStep 11484179 = 17226269) B17226269
theorem B7656119 : Blo 2267435 7656119 := bstep (se 1 (by rfl) ⟨5742089, by rfl⟩ : syracuseStep 7656119 = 11484179) B11484179
theorem B5104079 : Blo 2267435 5104079 := bstep (se 1 (by rfl) ⟨3828059, by rfl⟩ : syracuseStep 5104079 = 7656119) B7656119
theorem B3402719 : Blo 2267435 3402719 := bstep (se 1 (by rfl) ⟨2552039, by rfl⟩ : syracuseStep 3402719 = 5104079) B5104079
theorem B2268479 : Blo 2267435 2268479 := bstep (se 1 (by rfl) ⟨1701359, by rfl⟩ : syracuseStep 2268479 = 3402719) B3402719
theorem B3402725 : Blo 2267435 3402725 := bbase (se 4 (by rfl) ⟨319005, by rfl⟩ : syracuseStep 3402725 = 638011) (by norm_num)
theorem B2268483 : Blo 2267435 2268483 := bstep (se 1 (by rfl) ⟨1701362, by rfl⟩ : syracuseStep 2268483 = 3402725) B3402725
theorem B9689813 : Blo 2267435 9689813 := bbase (se 7 (by rfl) ⟨113552, by rfl⟩ : syracuseStep 9689813 = 227105) (by norm_num)
theorem B6459875 : Blo 2267435 6459875 := bstep (se 1 (by rfl) ⟨4844906, by rfl⟩ : syracuseStep 6459875 = 9689813) B9689813
theorem B4306583 : Blo 2267435 4306583 := bstep (se 1 (by rfl) ⟨3229937, by rfl⟩ : syracuseStep 4306583 = 6459875) B6459875
theorem B2871055 : Blo 2267435 2871055 := bstep (se 1 (by rfl) ⟨2153291, by rfl⟩ : syracuseStep 2871055 = 4306583) B4306583
theorem B3828073 : Blo 2267435 3828073 := bstep (se 2 (by rfl) ⟨1435527, by rfl⟩ : syracuseStep 3828073 = 2871055) B2871055
theorem B5104097 : Blo 2267435 5104097 := bstep (se 2 (by rfl) ⟨1914036, by rfl⟩ : syracuseStep 5104097 = 3828073) B3828073
theorem B3402731 : Blo 2267435 3402731 := bstep (se 1 (by rfl) ⟨2552048, by rfl⟩ : syracuseStep 3402731 = 5104097) B5104097
theorem B2268487 : Blo 2267435 2268487 := bstep (se 1 (by rfl) ⟨1701365, by rfl⟩ : syracuseStep 2268487 = 3402731) B3402731
theorem B2552053 : Blo 2267435 2552053 := bbase (se 5 (by rfl) ⟨119627, by rfl⟩ : syracuseStep 2552053 = 239255) (by norm_num)
theorem B3402737 : Blo 2267435 3402737 := bstep (se 2 (by rfl) ⟨1276026, by rfl⟩ : syracuseStep 3402737 = 2552053) B2552053
theorem B2268491 : Blo 2267435 2268491 := bstep (se 1 (by rfl) ⟨1701368, by rfl⟩ : syracuseStep 2268491 = 3402737) B3402737
theorem B2871065 : Blo 2267435 2871065 := bbase (se 2 (by rfl) ⟨1076649, by rfl⟩ : syracuseStep 2871065 = 2153299) (by norm_num)
theorem B7656173 : Blo 2267435 7656173 := bstep (se 3 (by rfl) ⟨1435532, by rfl⟩ : syracuseStep 7656173 = 2871065) B2871065
theorem B5104115 : Blo 2267435 5104115 := bstep (se 1 (by rfl) ⟨3828086, by rfl⟩ : syracuseStep 5104115 = 7656173) B7656173
theorem B3402743 : Blo 2267435 3402743 := bstep (se 1 (by rfl) ⟨2552057, by rfl⟩ : syracuseStep 3402743 = 5104115) B5104115
theorem B2268495 : Blo 2267435 2268495 := bstep (se 1 (by rfl) ⟨1701371, by rfl⟩ : syracuseStep 2268495 = 3402743) B3402743
theorem B3402749 : Blo 2267435 3402749 := bbase (se 3 (by rfl) ⟨638015, by rfl⟩ : syracuseStep 3402749 = 1276031) (by norm_num)
theorem B2268499 : Blo 2267435 2268499 := bstep (se 1 (by rfl) ⟨1701374, by rfl⟩ : syracuseStep 2268499 = 3402749) B3402749
theorem B5104133 : Blo 2267435 5104133 := bbase (se 4 (by rfl) ⟨478512, by rfl⟩ : syracuseStep 5104133 = 957025) (by norm_num)
theorem B3402755 : Blo 2267435 3402755 := bstep (se 1 (by rfl) ⟨2552066, by rfl⟩ : syracuseStep 3402755 = 5104133) B5104133
theorem B2268503 : Blo 2267435 2268503 := bstep (se 1 (by rfl) ⟨1701377, by rfl⟩ : syracuseStep 2268503 = 3402755) B3402755
theorem B4306621 : Blo 2267435 4306621 := bbase (se 3 (by rfl) ⟨807491, by rfl⟩ : syracuseStep 4306621 = 1614983) (by norm_num)
theorem B5742161 : Blo 2267435 5742161 := bstep (se 2 (by rfl) ⟨2153310, by rfl⟩ : syracuseStep 5742161 = 4306621) B4306621
theorem B3828107 : Blo 2267435 3828107 := bstep (se 1 (by rfl) ⟨2871080, by rfl⟩ : syracuseStep 3828107 = 5742161) B5742161
theorem B2552071 : Blo 2267435 2552071 := bstep (se 1 (by rfl) ⟨1914053, by rfl⟩ : syracuseStep 2552071 = 3828107) B3828107
theorem B3402761 : Blo 2267435 3402761 := bstep (se 2 (by rfl) ⟨1276035, by rfl⟩ : syracuseStep 3402761 = 2552071) B2552071
theorem B2268507 : Blo 2267435 2268507 := bstep (se 1 (by rfl) ⟨1701380, by rfl⟩ : syracuseStep 2268507 = 3402761) B3402761
theorem B11484341 : Blo 2267435 11484341 := bbase (se 5 (by rfl) ⟨538328, by rfl⟩ : syracuseStep 11484341 = 1076657) (by norm_num)
theorem B7656227 : Blo 2267435 7656227 := bstep (se 1 (by rfl) ⟨5742170, by rfl⟩ : syracuseStep 7656227 = 11484341) B11484341
theorem B5104151 : Blo 2267435 5104151 := bstep (se 1 (by rfl) ⟨3828113, by rfl⟩ : syracuseStep 5104151 = 7656227) B7656227
theorem B3402767 : Blo 2267435 3402767 := bstep (se 1 (by rfl) ⟨2552075, by rfl⟩ : syracuseStep 3402767 = 5104151) B5104151
theorem B2268511 : Blo 2267435 2268511 := bstep (se 1 (by rfl) ⟨1701383, by rfl⟩ : syracuseStep 2268511 = 3402767) B3402767
theorem B3402773 : Blo 2267435 3402773 := bbase (se 6 (by rfl) ⟨79752, by rfl⟩ : syracuseStep 3402773 = 159505) (by norm_num)
theorem B2268515 : Blo 2267435 2268515 := bstep (se 1 (by rfl) ⟨1701386, by rfl⟩ : syracuseStep 2268515 = 3402773) B3402773
theorem B4598941 : Blo 2267435 4598941 := bbase (se 3 (by rfl) ⟨862301, by rfl⟩ : syracuseStep 4598941 = 1724603) (by norm_num)
theorem B6131921 : Blo 2267435 6131921 := bstep (se 2 (by rfl) ⟨2299470, by rfl⟩ : syracuseStep 6131921 = 4598941) B4598941
theorem B16351789 : Blo 2267435 16351789 := bstep (se 3 (by rfl) ⟨3065960, by rfl⟩ : syracuseStep 16351789 = 6131921) B6131921
theorem B21802385 : Blo 2267435 21802385 := bstep (se 2 (by rfl) ⟨8175894, by rfl⟩ : syracuseStep 21802385 = 16351789) B16351789
theorem B14534923 : Blo 2267435 14534923 := bstep (se 1 (by rfl) ⟨10901192, by rfl⟩ : syracuseStep 14534923 = 21802385) B21802385
theorem B19379897 : Blo 2267435 19379897 := bstep (se 2 (by rfl) ⟨7267461, by rfl⟩ : syracuseStep 19379897 = 14534923) B14534923
theorem B12919931 : Blo 2267435 12919931 := bstep (se 1 (by rfl) ⟨9689948, by rfl⟩ : syracuseStep 12919931 = 19379897) B19379897
theorem B8613287 : Blo 2267435 8613287 := bstep (se 1 (by rfl) ⟨6459965, by rfl⟩ : syracuseStep 8613287 = 12919931) B12919931
theorem B5742191 : Blo 2267435 5742191 := bstep (se 1 (by rfl) ⟨4306643, by rfl⟩ : syracuseStep 5742191 = 8613287) B8613287
theorem B3828127 : Blo 2267435 3828127 := bstep (se 1 (by rfl) ⟨2871095, by rfl⟩ : syracuseStep 3828127 = 5742191) B5742191
theorem B5104169 : Blo 2267435 5104169 := bstep (se 2 (by rfl) ⟨1914063, by rfl⟩ : syracuseStep 5104169 = 3828127) B3828127
theorem B3402779 : Blo 2267435 3402779 := bstep (se 1 (by rfl) ⟨2552084, by rfl⟩ : syracuseStep 3402779 = 5104169) B5104169
theorem B2268519 : Blo 2267435 2268519 := bstep (se 1 (by rfl) ⟨1701389, by rfl⟩ : syracuseStep 2268519 = 3402779) B3402779
theorem B2552089 : Blo 2267435 2552089 := bbase (se 2 (by rfl) ⟨957033, by rfl⟩ : syracuseStep 2552089 = 1914067) (by norm_num)
theorem B3402785 : Blo 2267435 3402785 := bstep (se 2 (by rfl) ⟨1276044, by rfl⟩ : syracuseStep 3402785 = 2552089) B2552089
theorem B2268523 : Blo 2267435 2268523 := bstep (se 1 (by rfl) ⟨1701392, by rfl⟩ : syracuseStep 2268523 = 3402785) B3402785
theorem B8613317 : Blo 2267435 8613317 := bbase (se 4 (by rfl) ⟨807498, by rfl⟩ : syracuseStep 8613317 = 1614997) (by norm_num)
theorem B5742211 : Blo 2267435 5742211 := bstep (se 1 (by rfl) ⟨4306658, by rfl⟩ : syracuseStep 5742211 = 8613317) B8613317
theorem B7656281 : Blo 2267435 7656281 := bstep (se 2 (by rfl) ⟨2871105, by rfl⟩ : syracuseStep 7656281 = 5742211) B5742211
theorem B5104187 : Blo 2267435 5104187 := bstep (se 1 (by rfl) ⟨3828140, by rfl⟩ : syracuseStep 5104187 = 7656281) B7656281
theorem B3402791 : Blo 2267435 3402791 := bstep (se 1 (by rfl) ⟨2552093, by rfl⟩ : syracuseStep 3402791 = 5104187) B5104187
theorem B2268527 : Blo 2267435 2268527 := bstep (se 1 (by rfl) ⟨1701395, by rfl⟩ : syracuseStep 2268527 = 3402791) B3402791
theorem B3402797 : Blo 2267435 3402797 := bbase (se 3 (by rfl) ⟨638024, by rfl⟩ : syracuseStep 3402797 = 1276049) (by norm_num)
theorem B2268531 : Blo 2267435 2268531 := bstep (se 1 (by rfl) ⟨1701398, by rfl⟩ : syracuseStep 2268531 = 3402797) B3402797
theorem B5104205 : Blo 2267435 5104205 := bbase (se 3 (by rfl) ⟨957038, by rfl⟩ : syracuseStep 5104205 = 1914077) (by norm_num)
theorem B3402803 : Blo 2267435 3402803 := bstep (se 1 (by rfl) ⟨2552102, by rfl⟩ : syracuseStep 3402803 = 5104205) B5104205
theorem B2268535 : Blo 2267435 2268535 := bstep (se 1 (by rfl) ⟨1701401, by rfl⟩ : syracuseStep 2268535 = 3402803) B3402803
theorem B2871121 : Blo 2267435 2871121 := bbase (se 2 (by rfl) ⟨1076670, by rfl⟩ : syracuseStep 2871121 = 2153341) (by norm_num)
theorem B3828161 : Blo 2267435 3828161 := bstep (se 2 (by rfl) ⟨1435560, by rfl⟩ : syracuseStep 3828161 = 2871121) B2871121
theorem B2552107 : Blo 2267435 2552107 := bstep (se 1 (by rfl) ⟨1914080, by rfl⟩ : syracuseStep 2552107 = 3828161) B3828161
theorem B3402809 : Blo 2267435 3402809 := bstep (se 2 (by rfl) ⟨1276053, by rfl⟩ : syracuseStep 3402809 = 2552107) B2552107
theorem B2268539 : Blo 2267435 2268539 := bstep (se 1 (by rfl) ⟨1701404, by rfl⟩ : syracuseStep 2268539 = 3402809) B3402809
theorem B29868821 : Blo 2267435 29868821 := bbase (se 6 (by rfl) ⟨700050, by rfl⟩ : syracuseStep 29868821 = 1400101) (by norm_num)
theorem B19912547 : Blo 2267435 19912547 := bstep (se 1 (by rfl) ⟨14934410, by rfl⟩ : syracuseStep 19912547 = 29868821) B29868821
theorem B13275031 : Blo 2267435 13275031 := bstep (se 1 (by rfl) ⟨9956273, by rfl⟩ : syracuseStep 13275031 = 19912547) B19912547
theorem B17700041 : Blo 2267435 17700041 := bstep (se 2 (by rfl) ⟨6637515, by rfl⟩ : syracuseStep 17700041 = 13275031) B13275031
theorem B11800027 : Blo 2267435 11800027 := bstep (se 1 (by rfl) ⟨8850020, by rfl⟩ : syracuseStep 11800027 = 17700041) B17700041
theorem B15733369 : Blo 2267435 15733369 := bstep (se 2 (by rfl) ⟨5900013, by rfl⟩ : syracuseStep 15733369 = 11800027) B11800027
theorem B20977825 : Blo 2267435 20977825 := bstep (se 2 (by rfl) ⟨7866684, by rfl⟩ : syracuseStep 20977825 = 15733369) B15733369
theorem B27970433 : Blo 2267435 27970433 := bstep (se 2 (by rfl) ⟨10488912, by rfl⟩ : syracuseStep 27970433 = 20977825) B20977825
theorem B18646955 : Blo 2267435 18646955 := bstep (se 1 (by rfl) ⟨13985216, by rfl⟩ : syracuseStep 18646955 = 27970433) B27970433
theorem B12431303 : Blo 2267435 12431303 := bstep (se 1 (by rfl) ⟨9323477, by rfl⟩ : syracuseStep 12431303 = 18646955) B18646955
theorem B8287535 : Blo 2267435 8287535 := bstep (se 1 (by rfl) ⟨6215651, by rfl⟩ : syracuseStep 8287535 = 12431303) B12431303
theorem B5525023 : Blo 2267435 5525023 := bstep (se 1 (by rfl) ⟨4143767, by rfl⟩ : syracuseStep 5525023 = 8287535) B8287535
theorem B7366697 : Blo 2267435 7366697 := bstep (se 2 (by rfl) ⟨2762511, by rfl⟩ : syracuseStep 7366697 = 5525023) B5525023
theorem B4911131 : Blo 2267435 4911131 := bstep (se 1 (by rfl) ⟨3683348, by rfl⟩ : syracuseStep 4911131 = 7366697) B7366697
theorem B13096349 : Blo 2267435 13096349 := bstep (se 3 (by rfl) ⟨2455565, by rfl⟩ : syracuseStep 13096349 = 4911131) B4911131
theorem B8730899 : Blo 2267435 8730899 := bstep (se 1 (by rfl) ⟨6548174, by rfl⟩ : syracuseStep 8730899 = 13096349) B13096349
theorem B5820599 : Blo 2267435 5820599 := bstep (se 1 (by rfl) ⟨4365449, by rfl⟩ : syracuseStep 5820599 = 8730899) B8730899
theorem B3880399 : Blo 2267435 3880399 := bstep (se 1 (by rfl) ⟨2910299, by rfl⟩ : syracuseStep 3880399 = 5820599) B5820599
theorem B5173865 : Blo 2267435 5173865 := bstep (se 2 (by rfl) ⟨1940199, by rfl⟩ : syracuseStep 5173865 = 3880399) B3880399
theorem B3449243 : Blo 2267435 3449243 := bstep (se 1 (by rfl) ⟨2586932, by rfl⟩ : syracuseStep 3449243 = 5173865) B5173865
theorem B9197981 : Blo 2267435 9197981 := bstep (se 3 (by rfl) ⟨1724621, by rfl⟩ : syracuseStep 9197981 = 3449243) B3449243
theorem B6131987 : Blo 2267435 6131987 := bstep (se 1 (by rfl) ⟨4598990, by rfl⟩ : syracuseStep 6131987 = 9197981) B9197981
theorem B4087991 : Blo 2267435 4087991 := bstep (se 1 (by rfl) ⟨3065993, by rfl⟩ : syracuseStep 4087991 = 6131987) B6131987
theorem B2725327 : Blo 2267435 2725327 := bstep (se 1 (by rfl) ⟨2043995, by rfl⟩ : syracuseStep 2725327 = 4087991) B4087991
theorem B3633769 : Blo 2267435 3633769 := bstep (se 2 (by rfl) ⟨1362663, by rfl⟩ : syracuseStep 3633769 = 2725327) B2725327
theorem B4845025 : Blo 2267435 4845025 := bstep (se 2 (by rfl) ⟨1816884, by rfl⟩ : syracuseStep 4845025 = 3633769) B3633769
theorem B25840133 : Blo 2267435 25840133 := bstep (se 4 (by rfl) ⟨2422512, by rfl⟩ : syracuseStep 25840133 = 4845025) B4845025
theorem B17226755 : Blo 2267435 17226755 := bstep (se 1 (by rfl) ⟨12920066, by rfl⟩ : syracuseStep 17226755 = 25840133) B25840133
theorem B11484503 : Blo 2267435 11484503 := bstep (se 1 (by rfl) ⟨8613377, by rfl⟩ : syracuseStep 11484503 = 17226755) B17226755
theorem B7656335 : Blo 2267435 7656335 := bstep (se 1 (by rfl) ⟨5742251, by rfl⟩ : syracuseStep 7656335 = 11484503) B11484503
theorem B5104223 : Blo 2267435 5104223 := bstep (se 1 (by rfl) ⟨3828167, by rfl⟩ : syracuseStep 5104223 = 7656335) B7656335
theorem B3402815 : Blo 2267435 3402815 := bstep (se 1 (by rfl) ⟨2552111, by rfl⟩ : syracuseStep 3402815 = 5104223) B5104223
theorem B2268543 : Blo 2267435 2268543 := bstep (se 1 (by rfl) ⟨1701407, by rfl⟩ : syracuseStep 2268543 = 3402815) B3402815
theorem B3402821 : Blo 2267435 3402821 := bbase (se 4 (by rfl) ⟨319014, by rfl⟩ : syracuseStep 3402821 = 638029) (by norm_num)
theorem B2268547 : Blo 2267435 2268547 := bstep (se 1 (by rfl) ⟨1701410, by rfl⟩ : syracuseStep 2268547 = 3402821) B3402821
theorem B3828181 : Blo 2267435 3828181 := bbase (se 7 (by rfl) ⟨44861, by rfl⟩ : syracuseStep 3828181 = 89723) (by norm_num)
theorem B5104241 : Blo 2267435 5104241 := bstep (se 2 (by rfl) ⟨1914090, by rfl⟩ : syracuseStep 5104241 = 3828181) B3828181
theorem B3402827 : Blo 2267435 3402827 := bstep (se 1 (by rfl) ⟨2552120, by rfl⟩ : syracuseStep 3402827 = 5104241) B5104241
theorem B2268551 : Blo 2267435 2268551 := bstep (se 1 (by rfl) ⟨1701413, by rfl⟩ : syracuseStep 2268551 = 3402827) B3402827
theorem B2552125 : Blo 2267435 2552125 := bbase (se 3 (by rfl) ⟨478523, by rfl⟩ : syracuseStep 2552125 = 957047) (by norm_num)
theorem B3402833 : Blo 2267435 3402833 := bstep (se 2 (by rfl) ⟨1276062, by rfl⟩ : syracuseStep 3402833 = 2552125) B2552125
theorem B2268555 : Blo 2267435 2268555 := bstep (se 1 (by rfl) ⟨1701416, by rfl⟩ : syracuseStep 2268555 = 3402833) B3402833
theorem B7656389 : Blo 2267435 7656389 := bbase (se 4 (by rfl) ⟨717786, by rfl⟩ : syracuseStep 7656389 = 1435573) (by norm_num)
theorem B5104259 : Blo 2267435 5104259 := bstep (se 1 (by rfl) ⟨3828194, by rfl⟩ : syracuseStep 5104259 = 7656389) B7656389
theorem B3402839 : Blo 2267435 3402839 := bstep (se 1 (by rfl) ⟨2552129, by rfl⟩ : syracuseStep 3402839 = 5104259) B5104259
theorem B2268559 : Blo 2267435 2268559 := bstep (se 1 (by rfl) ⟨1701419, by rfl⟩ : syracuseStep 2268559 = 3402839) B3402839
theorem B3402845 : Blo 2267435 3402845 := bbase (se 3 (by rfl) ⟨638033, by rfl⟩ : syracuseStep 3402845 = 1276067) (by norm_num)
theorem B2268563 : Blo 2267435 2268563 := bstep (se 1 (by rfl) ⟨1701422, by rfl⟩ : syracuseStep 2268563 = 3402845) B3402845
theorem B5104277 : Blo 2267435 5104277 := bbase (se 6 (by rfl) ⟨119631, by rfl⟩ : syracuseStep 5104277 = 239263) (by norm_num)
theorem B3402851 : Blo 2267435 3402851 := bstep (se 1 (by rfl) ⟨2552138, by rfl⟩ : syracuseStep 3402851 = 5104277) B5104277
theorem B2268567 : Blo 2267435 2268567 := bstep (se 1 (by rfl) ⟨1701425, by rfl⟩ : syracuseStep 2268567 = 3402851) B3402851
theorem B8176085 : Blo 2267435 8176085 := bbase (se 7 (by rfl) ⟨95813, by rfl⟩ : syracuseStep 8176085 = 191627) (by norm_num)
theorem B5450723 : Blo 2267435 5450723 := bstep (se 1 (by rfl) ⟨4088042, by rfl⟩ : syracuseStep 5450723 = 8176085) B8176085
theorem B3633815 : Blo 2267435 3633815 := bstep (se 1 (by rfl) ⟨2725361, by rfl⟩ : syracuseStep 3633815 = 5450723) B5450723
theorem B2422543 : Blo 2267435 2422543 := bstep (se 1 (by rfl) ⟨1816907, by rfl⟩ : syracuseStep 2422543 = 3633815) B3633815
theorem B3230057 : Blo 2267435 3230057 := bstep (se 2 (by rfl) ⟨1211271, by rfl⟩ : syracuseStep 3230057 = 2422543) B2422543
theorem B8613485 : Blo 2267435 8613485 := bstep (se 3 (by rfl) ⟨1615028, by rfl⟩ : syracuseStep 8613485 = 3230057) B3230057
theorem B5742323 : Blo 2267435 5742323 := bstep (se 1 (by rfl) ⟨4306742, by rfl⟩ : syracuseStep 5742323 = 8613485) B8613485
theorem B3828215 : Blo 2267435 3828215 := bstep (se 1 (by rfl) ⟨2871161, by rfl⟩ : syracuseStep 3828215 = 5742323) B5742323
theorem B2552143 : Blo 2267435 2552143 := bstep (se 1 (by rfl) ⟨1914107, by rfl⟩ : syracuseStep 2552143 = 3828215) B3828215
theorem B3402857 : Blo 2267435 3402857 := bstep (se 2 (by rfl) ⟨1276071, by rfl⟩ : syracuseStep 3402857 = 2552143) B2552143
theorem B2268571 : Blo 2267435 2268571 := bstep (se 1 (by rfl) ⟨1701428, by rfl⟩ : syracuseStep 2268571 = 3402857) B3402857
theorem B10901461 : Blo 2267435 10901461 := bbase (se 7 (by rfl) ⟨127751, by rfl⟩ : syracuseStep 10901461 = 255503) (by norm_num)
theorem B14535281 : Blo 2267435 14535281 := bstep (se 2 (by rfl) ⟨5450730, by rfl⟩ : syracuseStep 14535281 = 10901461) B10901461
theorem B9690187 : Blo 2267435 9690187 := bstep (se 1 (by rfl) ⟨7267640, by rfl⟩ : syracuseStep 9690187 = 14535281) B14535281
theorem B12920249 : Blo 2267435 12920249 := bstep (se 2 (by rfl) ⟨4845093, by rfl⟩ : syracuseStep 12920249 = 9690187) B9690187
theorem B8613499 : Blo 2267435 8613499 := bstep (se 1 (by rfl) ⟨6460124, by rfl⟩ : syracuseStep 8613499 = 12920249) B12920249
theorem B11484665 : Blo 2267435 11484665 := bstep (se 2 (by rfl) ⟨4306749, by rfl⟩ : syracuseStep 11484665 = 8613499) B8613499
theorem B7656443 : Blo 2267435 7656443 := bstep (se 1 (by rfl) ⟨5742332, by rfl⟩ : syracuseStep 7656443 = 11484665) B11484665
theorem B5104295 : Blo 2267435 5104295 := bstep (se 1 (by rfl) ⟨3828221, by rfl⟩ : syracuseStep 5104295 = 7656443) B7656443
theorem B3402863 : Blo 2267435 3402863 := bstep (se 1 (by rfl) ⟨2552147, by rfl⟩ : syracuseStep 3402863 = 5104295) B5104295
theorem B2268575 : Blo 2267435 2268575 := bstep (se 1 (by rfl) ⟨1701431, by rfl⟩ : syracuseStep 2268575 = 3402863) B3402863
theorem B3402869 : Blo 2267435 3402869 := bbase (se 5 (by rfl) ⟨159509, by rfl⟩ : syracuseStep 3402869 = 319019) (by norm_num)
theorem B2268579 : Blo 2267435 2268579 := bstep (se 1 (by rfl) ⟨1701434, by rfl⟩ : syracuseStep 2268579 = 3402869) B3402869
theorem B4306765 : Blo 2267435 4306765 := bbase (se 3 (by rfl) ⟨807518, by rfl⟩ : syracuseStep 4306765 = 1615037) (by norm_num)
theorem B5742353 : Blo 2267435 5742353 := bstep (se 2 (by rfl) ⟨2153382, by rfl⟩ : syracuseStep 5742353 = 4306765) B4306765
theorem B3828235 : Blo 2267435 3828235 := bstep (se 1 (by rfl) ⟨2871176, by rfl⟩ : syracuseStep 3828235 = 5742353) B5742353
theorem B5104313 : Blo 2267435 5104313 := bstep (se 2 (by rfl) ⟨1914117, by rfl⟩ : syracuseStep 5104313 = 3828235) B3828235
theorem B3402875 : Blo 2267435 3402875 := bstep (se 1 (by rfl) ⟨2552156, by rfl⟩ : syracuseStep 3402875 = 5104313) B5104313
theorem B2268583 : Blo 2267435 2268583 := bstep (se 1 (by rfl) ⟨1701437, by rfl⟩ : syracuseStep 2268583 = 3402875) B3402875
theorem B2552161 : Blo 2267435 2552161 := bbase (se 2 (by rfl) ⟨957060, by rfl⟩ : syracuseStep 2552161 = 1914121) (by norm_num)
theorem B3402881 : Blo 2267435 3402881 := bstep (se 2 (by rfl) ⟨1276080, by rfl⟩ : syracuseStep 3402881 = 2552161) B2552161
theorem B2268587 : Blo 2267435 2268587 := bstep (se 1 (by rfl) ⟨1701440, by rfl⟩ : syracuseStep 2268587 = 3402881) B3402881
theorem B5742373 : Blo 2267435 5742373 := bbase (se 4 (by rfl) ⟨538347, by rfl⟩ : syracuseStep 5742373 = 1076695) (by norm_num)
theorem B7656497 : Blo 2267435 7656497 := bstep (se 2 (by rfl) ⟨2871186, by rfl⟩ : syracuseStep 7656497 = 5742373) B5742373
theorem B5104331 : Blo 2267435 5104331 := bstep (se 1 (by rfl) ⟨3828248, by rfl⟩ : syracuseStep 5104331 = 7656497) B7656497
theorem B3402887 : Blo 2267435 3402887 := bstep (se 1 (by rfl) ⟨2552165, by rfl⟩ : syracuseStep 3402887 = 5104331) B5104331
theorem B2268591 : Blo 2267435 2268591 := bstep (se 1 (by rfl) ⟨1701443, by rfl⟩ : syracuseStep 2268591 = 3402887) B3402887
theorem B3402893 : Blo 2267435 3402893 := bbase (se 3 (by rfl) ⟨638042, by rfl⟩ : syracuseStep 3402893 = 1276085) (by norm_num)
theorem B2268595 : Blo 2267435 2268595 := bstep (se 1 (by rfl) ⟨1701446, by rfl⟩ : syracuseStep 2268595 = 3402893) B3402893
theorem B5104349 : Blo 2267435 5104349 := bbase (se 3 (by rfl) ⟨957065, by rfl⟩ : syracuseStep 5104349 = 1914131) (by norm_num)
theorem B3402899 : Blo 2267435 3402899 := bstep (se 1 (by rfl) ⟨2552174, by rfl⟩ : syracuseStep 3402899 = 5104349) B5104349
theorem B2268599 : Blo 2267435 2268599 := bstep (se 1 (by rfl) ⟨1701449, by rfl⟩ : syracuseStep 2268599 = 3402899) B3402899
theorem B3828269 : Blo 2267435 3828269 := bbase (se 3 (by rfl) ⟨717800, by rfl⟩ : syracuseStep 3828269 = 1435601) (by norm_num)
theorem B2552179 : Blo 2267435 2552179 := bstep (se 1 (by rfl) ⟨1914134, by rfl⟩ : syracuseStep 2552179 = 3828269) B3828269
theorem B3402905 : Blo 2267435 3402905 := bstep (se 2 (by rfl) ⟨1276089, by rfl⟩ : syracuseStep 3402905 = 2552179) B2552179
theorem B2268603 : Blo 2267435 2268603 := bstep (se 1 (by rfl) ⟨1701452, by rfl⟩ : syracuseStep 2268603 = 3402905) B3402905
theorem B6548357 : Blo 2267435 6548357 := bbase (se 4 (by rfl) ⟨613908, by rfl⟩ : syracuseStep 6548357 = 1227817) (by norm_num)
theorem B4365571 : Blo 2267435 4365571 := bstep (se 1 (by rfl) ⟨3274178, by rfl⟩ : syracuseStep 4365571 = 6548357) B6548357
theorem B5820761 : Blo 2267435 5820761 := bstep (se 2 (by rfl) ⟨2182785, by rfl⟩ : syracuseStep 5820761 = 4365571) B4365571
theorem B3880507 : Blo 2267435 3880507 := bstep (se 1 (by rfl) ⟨2910380, by rfl⟩ : syracuseStep 3880507 = 5820761) B5820761
theorem B5174009 : Blo 2267435 5174009 := bstep (se 2 (by rfl) ⟨1940253, by rfl⟩ : syracuseStep 5174009 = 3880507) B3880507
theorem B3449339 : Blo 2267435 3449339 := bstep (se 1 (by rfl) ⟨2587004, by rfl⟩ : syracuseStep 3449339 = 5174009) B5174009
theorem B36792949 : Blo 2267435 36792949 := bstep (se 5 (by rfl) ⟨1724669, by rfl⟩ : syracuseStep 36792949 = 3449339) B3449339
theorem B49057265 : Blo 2267435 49057265 := bstep (se 2 (by rfl) ⟨18396474, by rfl⟩ : syracuseStep 49057265 = 36792949) B36792949
theorem B32704843 : Blo 2267435 32704843 := bstep (se 1 (by rfl) ⟨24528632, by rfl⟩ : syracuseStep 32704843 = 49057265) B49057265
theorem B43606457 : Blo 2267435 43606457 := bstep (se 2 (by rfl) ⟨16352421, by rfl⟩ : syracuseStep 43606457 = 32704843) B32704843
theorem B29070971 : Blo 2267435 29070971 := bstep (se 1 (by rfl) ⟨21803228, by rfl⟩ : syracuseStep 29070971 = 43606457) B43606457
theorem B19380647 : Blo 2267435 19380647 := bstep (se 1 (by rfl) ⟨14535485, by rfl⟩ : syracuseStep 19380647 = 29070971) B29070971
theorem B12920431 : Blo 2267435 12920431 := bstep (se 1 (by rfl) ⟨9690323, by rfl⟩ : syracuseStep 12920431 = 19380647) B19380647
theorem B17227241 : Blo 2267435 17227241 := bstep (se 2 (by rfl) ⟨6460215, by rfl⟩ : syracuseStep 17227241 = 12920431) B12920431
theorem B11484827 : Blo 2267435 11484827 := bstep (se 1 (by rfl) ⟨8613620, by rfl⟩ : syracuseStep 11484827 = 17227241) B17227241
theorem B7656551 : Blo 2267435 7656551 := bstep (se 1 (by rfl) ⟨5742413, by rfl⟩ : syracuseStep 7656551 = 11484827) B11484827
theorem B5104367 : Blo 2267435 5104367 := bstep (se 1 (by rfl) ⟨3828275, by rfl⟩ : syracuseStep 5104367 = 7656551) B7656551
theorem B3402911 : Blo 2267435 3402911 := bstep (se 1 (by rfl) ⟨2552183, by rfl⟩ : syracuseStep 3402911 = 5104367) B5104367
theorem B2268607 : Blo 2267435 2268607 := bstep (se 1 (by rfl) ⟨1701455, by rfl⟩ : syracuseStep 2268607 = 3402911) B3402911
theorem B3402917 : Blo 2267435 3402917 := bbase (se 4 (by rfl) ⟨319023, by rfl⟩ : syracuseStep 3402917 = 638047) (by norm_num)
theorem B2268611 : Blo 2267435 2268611 := bstep (se 1 (by rfl) ⟨1701458, by rfl⟩ : syracuseStep 2268611 = 3402917) B3402917
theorem B2871217 : Blo 2267435 2871217 := bbase (se 2 (by rfl) ⟨1076706, by rfl⟩ : syracuseStep 2871217 = 2153413) (by norm_num)
theorem B3828289 : Blo 2267435 3828289 := bstep (se 2 (by rfl) ⟨1435608, by rfl⟩ : syracuseStep 3828289 = 2871217) B2871217
theorem B5104385 : Blo 2267435 5104385 := bstep (se 2 (by rfl) ⟨1914144, by rfl⟩ : syracuseStep 5104385 = 3828289) B3828289
theorem B3402923 : Blo 2267435 3402923 := bstep (se 1 (by rfl) ⟨2552192, by rfl⟩ : syracuseStep 3402923 = 5104385) B5104385
theorem B2268615 : Blo 2267435 2268615 := bstep (se 1 (by rfl) ⟨1701461, by rfl⟩ : syracuseStep 2268615 = 3402923) B3402923
theorem B2552197 : Blo 2267435 2552197 := bbase (se 4 (by rfl) ⟨239268, by rfl⟩ : syracuseStep 2552197 = 478537) (by norm_num)
theorem B3402929 : Blo 2267435 3402929 := bstep (se 2 (by rfl) ⟨1276098, by rfl⟩ : syracuseStep 3402929 = 2552197) B2552197
theorem B2268619 : Blo 2267435 2268619 := bstep (se 1 (by rfl) ⟨1701464, by rfl⟩ : syracuseStep 2268619 = 3402929) B3402929
theorem B4845197 : Blo 2267435 4845197 := bbase (se 3 (by rfl) ⟨908474, by rfl⟩ : syracuseStep 4845197 = 1816949) (by norm_num)
theorem B3230131 : Blo 2267435 3230131 := bstep (se 1 (by rfl) ⟨2422598, by rfl⟩ : syracuseStep 3230131 = 4845197) B4845197
theorem B4306841 : Blo 2267435 4306841 := bstep (se 2 (by rfl) ⟨1615065, by rfl⟩ : syracuseStep 4306841 = 3230131) B3230131
theorem B2871227 : Blo 2267435 2871227 := bstep (se 1 (by rfl) ⟨2153420, by rfl⟩ : syracuseStep 2871227 = 4306841) B4306841
theorem B7656605 : Blo 2267435 7656605 := bstep (se 3 (by rfl) ⟨1435613, by rfl⟩ : syracuseStep 7656605 = 2871227) B2871227
theorem B5104403 : Blo 2267435 5104403 := bstep (se 1 (by rfl) ⟨3828302, by rfl⟩ : syracuseStep 5104403 = 7656605) B7656605
theorem B3402935 : Blo 2267435 3402935 := bstep (se 1 (by rfl) ⟨2552201, by rfl⟩ : syracuseStep 3402935 = 5104403) B5104403
theorem B2268623 : Blo 2267435 2268623 := bstep (se 1 (by rfl) ⟨1701467, by rfl⟩ : syracuseStep 2268623 = 3402935) B3402935
theorem B3402941 : Blo 2267435 3402941 := bbase (se 3 (by rfl) ⟨638051, by rfl⟩ : syracuseStep 3402941 = 1276103) (by norm_num)
theorem B2268627 : Blo 2267435 2268627 := bstep (se 1 (by rfl) ⟨1701470, by rfl⟩ : syracuseStep 2268627 = 3402941) B3402941
theorem B5104421 : Blo 2267435 5104421 := bbase (se 4 (by rfl) ⟨478539, by rfl⟩ : syracuseStep 5104421 = 957079) (by norm_num)
theorem B3402947 : Blo 2267435 3402947 := bstep (se 1 (by rfl) ⟨2552210, by rfl⟩ : syracuseStep 3402947 = 5104421) B5104421
theorem B2268631 : Blo 2267435 2268631 := bstep (se 1 (by rfl) ⟨1701473, by rfl⟩ : syracuseStep 2268631 = 3402947) B3402947
theorem B5742485 : Blo 2267435 5742485 := bbase (se 6 (by rfl) ⟨134589, by rfl⟩ : syracuseStep 5742485 = 269179) (by norm_num)
theorem B3828323 : Blo 2267435 3828323 := bstep (se 1 (by rfl) ⟨2871242, by rfl⟩ : syracuseStep 3828323 = 5742485) B5742485
theorem B2552215 : Blo 2267435 2552215 := bstep (se 1 (by rfl) ⟨1914161, by rfl⟩ : syracuseStep 2552215 = 3828323) B3828323
theorem B3402953 : Blo 2267435 3402953 := bstep (se 2 (by rfl) ⟨1276107, by rfl⟩ : syracuseStep 3402953 = 2552215) B2552215
theorem B2268635 : Blo 2267435 2268635 := bstep (se 1 (by rfl) ⟨1701476, by rfl⟩ : syracuseStep 2268635 = 3402953) B3402953
theorem B5450885 : Blo 2267435 5450885 := bbase (se 4 (by rfl) ⟨511020, by rfl⟩ : syracuseStep 5450885 = 1022041) (by norm_num)
theorem B3633923 : Blo 2267435 3633923 := bstep (se 1 (by rfl) ⟨2725442, by rfl⟩ : syracuseStep 3633923 = 5450885) B5450885
theorem B9690461 : Blo 2267435 9690461 := bstep (se 3 (by rfl) ⟨1816961, by rfl⟩ : syracuseStep 9690461 = 3633923) B3633923
theorem B6460307 : Blo 2267435 6460307 := bstep (se 1 (by rfl) ⟨4845230, by rfl⟩ : syracuseStep 6460307 = 9690461) B9690461
theorem B4306871 : Blo 2267435 4306871 := bstep (se 1 (by rfl) ⟨3230153, by rfl⟩ : syracuseStep 4306871 = 6460307) B6460307
theorem B11484989 : Blo 2267435 11484989 := bstep (se 3 (by rfl) ⟨2153435, by rfl⟩ : syracuseStep 11484989 = 4306871) B4306871
theorem B7656659 : Blo 2267435 7656659 := bstep (se 1 (by rfl) ⟨5742494, by rfl⟩ : syracuseStep 7656659 = 11484989) B11484989
theorem B5104439 : Blo 2267435 5104439 := bstep (se 1 (by rfl) ⟨3828329, by rfl⟩ : syracuseStep 5104439 = 7656659) B7656659
theorem B3402959 : Blo 2267435 3402959 := bstep (se 1 (by rfl) ⟨2552219, by rfl⟩ : syracuseStep 3402959 = 5104439) B5104439
theorem B2268639 : Blo 2267435 2268639 := bstep (se 1 (by rfl) ⟨1701479, by rfl⟩ : syracuseStep 2268639 = 3402959) B3402959
theorem B3402965 : Blo 2267435 3402965 := bbase (se 7 (by rfl) ⟨39878, by rfl⟩ : syracuseStep 3402965 = 79757) (by norm_num)
theorem B2268643 : Blo 2267435 2268643 := bstep (se 1 (by rfl) ⟨1701482, by rfl⟩ : syracuseStep 2268643 = 3402965) B3402965
theorem B3230165 : Blo 2267435 3230165 := bbase (se 7 (by rfl) ⟨37853, by rfl⟩ : syracuseStep 3230165 = 75707) (by norm_num)
theorem B8613773 : Blo 2267435 8613773 := bstep (se 3 (by rfl) ⟨1615082, by rfl⟩ : syracuseStep 8613773 = 3230165) B3230165
theorem B5742515 : Blo 2267435 5742515 := bstep (se 1 (by rfl) ⟨4306886, by rfl⟩ : syracuseStep 5742515 = 8613773) B8613773
theorem B3828343 : Blo 2267435 3828343 := bstep (se 1 (by rfl) ⟨2871257, by rfl⟩ : syracuseStep 3828343 = 5742515) B5742515
theorem B5104457 : Blo 2267435 5104457 := bstep (se 2 (by rfl) ⟨1914171, by rfl⟩ : syracuseStep 5104457 = 3828343) B3828343
theorem B3402971 : Blo 2267435 3402971 := bstep (se 1 (by rfl) ⟨2552228, by rfl⟩ : syracuseStep 3402971 = 5104457) B5104457
theorem B2268647 : Blo 2267435 2268647 := bstep (se 1 (by rfl) ⟨1701485, by rfl⟩ : syracuseStep 2268647 = 3402971) B3402971
theorem B2552233 : Blo 2267435 2552233 := bbase (se 2 (by rfl) ⟨957087, by rfl⟩ : syracuseStep 2552233 = 1914175) (by norm_num)
theorem B3402977 : Blo 2267435 3402977 := bstep (se 2 (by rfl) ⟨1276116, by rfl⟩ : syracuseStep 3402977 = 2552233) B2552233
theorem B2268651 : Blo 2267435 2268651 := bstep (se 1 (by rfl) ⟨1701488, by rfl⟩ : syracuseStep 2268651 = 3402977) B3402977
theorem B3449413 : Blo 2267435 3449413 := bbase (se 4 (by rfl) ⟨323382, by rfl⟩ : syracuseStep 3449413 = 646765) (by norm_num)
theorem B4599217 : Blo 2267435 4599217 := bstep (se 2 (by rfl) ⟨1724706, by rfl⟩ : syracuseStep 4599217 = 3449413) B3449413
theorem B6132289 : Blo 2267435 6132289 := bstep (se 2 (by rfl) ⟨2299608, by rfl⟩ : syracuseStep 6132289 = 4599217) B4599217
theorem B8176385 : Blo 2267435 8176385 := bstep (se 2 (by rfl) ⟨3066144, by rfl⟩ : syracuseStep 8176385 = 6132289) B6132289
theorem B5450923 : Blo 2267435 5450923 := bstep (se 1 (by rfl) ⟨4088192, by rfl⟩ : syracuseStep 5450923 = 8176385) B8176385
theorem B7267897 : Blo 2267435 7267897 := bstep (se 2 (by rfl) ⟨2725461, by rfl⟩ : syracuseStep 7267897 = 5450923) B5450923
theorem B9690529 : Blo 2267435 9690529 := bstep (se 2 (by rfl) ⟨3633948, by rfl⟩ : syracuseStep 9690529 = 7267897) B7267897
theorem B12920705 : Blo 2267435 12920705 := bstep (se 2 (by rfl) ⟨4845264, by rfl⟩ : syracuseStep 12920705 = 9690529) B9690529
theorem B8613803 : Blo 2267435 8613803 := bstep (se 1 (by rfl) ⟨6460352, by rfl⟩ : syracuseStep 8613803 = 12920705) B12920705
theorem B5742535 : Blo 2267435 5742535 := bstep (se 1 (by rfl) ⟨4306901, by rfl⟩ : syracuseStep 5742535 = 8613803) B8613803
theorem B7656713 : Blo 2267435 7656713 := bstep (se 2 (by rfl) ⟨2871267, by rfl⟩ : syracuseStep 7656713 = 5742535) B5742535
theorem B5104475 : Blo 2267435 5104475 := bstep (se 1 (by rfl) ⟨3828356, by rfl⟩ : syracuseStep 5104475 = 7656713) B7656713
theorem B3402983 : Blo 2267435 3402983 := bstep (se 1 (by rfl) ⟨2552237, by rfl⟩ : syracuseStep 3402983 = 5104475) B5104475
theorem B2268655 : Blo 2267435 2268655 := bstep (se 1 (by rfl) ⟨1701491, by rfl⟩ : syracuseStep 2268655 = 3402983) B3402983
theorem B3402989 : Blo 2267435 3402989 := bbase (se 3 (by rfl) ⟨638060, by rfl⟩ : syracuseStep 3402989 = 1276121) (by norm_num)
theorem B2268659 : Blo 2267435 2268659 := bstep (se 1 (by rfl) ⟨1701494, by rfl⟩ : syracuseStep 2268659 = 3402989) B3402989
theorem B5104493 : Blo 2267435 5104493 := bbase (se 3 (by rfl) ⟨957092, by rfl⟩ : syracuseStep 5104493 = 1914185) (by norm_num)
theorem B3402995 : Blo 2267435 3402995 := bstep (se 1 (by rfl) ⟨2552246, by rfl⟩ : syracuseStep 3402995 = 5104493) B5104493
theorem B2268663 : Blo 2267435 2268663 := bstep (se 1 (by rfl) ⟨1701497, by rfl⟩ : syracuseStep 2268663 = 3402995) B3402995
theorem B4306925 : Blo 2267435 4306925 := bbase (se 3 (by rfl) ⟨807548, by rfl⟩ : syracuseStep 4306925 = 1615097) (by norm_num)
theorem B2871283 : Blo 2267435 2871283 := bstep (se 1 (by rfl) ⟨2153462, by rfl⟩ : syracuseStep 2871283 = 4306925) B4306925
theorem B3828377 : Blo 2267435 3828377 := bstep (se 2 (by rfl) ⟨1435641, by rfl⟩ : syracuseStep 3828377 = 2871283) B2871283
theorem B2552251 : Blo 2267435 2552251 := bstep (se 1 (by rfl) ⟨1914188, by rfl⟩ : syracuseStep 2552251 = 3828377) B3828377
theorem B3403001 : Blo 2267435 3403001 := bstep (se 2 (by rfl) ⟨1276125, by rfl⟩ : syracuseStep 3403001 = 2552251) B2552251
theorem B2268667 : Blo 2267435 2268667 := bstep (se 1 (by rfl) ⟨1701500, by rfl⟩ : syracuseStep 2268667 = 3403001) B3403001
theorem B5820925 : Blo 2267435 5820925 := bbase (se 3 (by rfl) ⟨1091423, by rfl⟩ : syracuseStep 5820925 = 2182847) (by norm_num)
theorem B7761233 : Blo 2267435 7761233 := bstep (se 2 (by rfl) ⟨2910462, by rfl⟩ : syracuseStep 7761233 = 5820925) B5820925
theorem B5174155 : Blo 2267435 5174155 := bstep (se 1 (by rfl) ⟨3880616, by rfl⟩ : syracuseStep 5174155 = 7761233) B7761233
theorem B6898873 : Blo 2267435 6898873 := bstep (se 2 (by rfl) ⟨2587077, by rfl⟩ : syracuseStep 6898873 = 5174155) B5174155
theorem B9198497 : Blo 2267435 9198497 := bstep (se 2 (by rfl) ⟨3449436, by rfl⟩ : syracuseStep 9198497 = 6898873) B6898873
theorem B6132331 : Blo 2267435 6132331 := bstep (se 1 (by rfl) ⟨4599248, by rfl⟩ : syracuseStep 6132331 = 9198497) B9198497
theorem B32705765 : Blo 2267435 32705765 := bstep (se 4 (by rfl) ⟨3066165, by rfl⟩ : syracuseStep 32705765 = 6132331) B6132331
theorem B21803843 : Blo 2267435 21803843 := bstep (se 1 (by rfl) ⟨16352882, by rfl⟩ : syracuseStep 21803843 = 32705765) B32705765
theorem B58143581 : Blo 2267435 58143581 := bstep (se 3 (by rfl) ⟨10901921, by rfl⟩ : syracuseStep 58143581 = 21803843) B21803843
theorem B38762387 : Blo 2267435 38762387 := bstep (se 1 (by rfl) ⟨29071790, by rfl⟩ : syracuseStep 38762387 = 58143581) B58143581
theorem B25841591 : Blo 2267435 25841591 := bstep (se 1 (by rfl) ⟨19381193, by rfl⟩ : syracuseStep 25841591 = 38762387) B38762387
theorem B17227727 : Blo 2267435 17227727 := bstep (se 1 (by rfl) ⟨12920795, by rfl⟩ : syracuseStep 17227727 = 25841591) B25841591
theorem B11485151 : Blo 2267435 11485151 := bstep (se 1 (by rfl) ⟨8613863, by rfl⟩ : syracuseStep 11485151 = 17227727) B17227727
theorem B7656767 : Blo 2267435 7656767 := bstep (se 1 (by rfl) ⟨5742575, by rfl⟩ : syracuseStep 7656767 = 11485151) B11485151
theorem B5104511 : Blo 2267435 5104511 := bstep (se 1 (by rfl) ⟨3828383, by rfl⟩ : syracuseStep 5104511 = 7656767) B7656767
theorem B3403007 : Blo 2267435 3403007 := bstep (se 1 (by rfl) ⟨2552255, by rfl⟩ : syracuseStep 3403007 = 5104511) B5104511
theorem B2268671 : Blo 2267435 2268671 := bstep (se 1 (by rfl) ⟨1701503, by rfl⟩ : syracuseStep 2268671 = 3403007) B3403007
theorem B3403013 : Blo 2267435 3403013 := bbase (se 4 (by rfl) ⟨319032, by rfl⟩ : syracuseStep 3403013 = 638065) (by norm_num)
theorem B2268675 : Blo 2267435 2268675 := bstep (se 1 (by rfl) ⟨1701506, by rfl⟩ : syracuseStep 2268675 = 3403013) B3403013
theorem B3828397 : Blo 2267435 3828397 := bbase (se 3 (by rfl) ⟨717824, by rfl⟩ : syracuseStep 3828397 = 1435649) (by norm_num)
theorem B5104529 : Blo 2267435 5104529 := bstep (se 2 (by rfl) ⟨1914198, by rfl⟩ : syracuseStep 5104529 = 3828397) B3828397
theorem B3403019 : Blo 2267435 3403019 := bstep (se 1 (by rfl) ⟨2552264, by rfl⟩ : syracuseStep 3403019 = 5104529) B5104529
theorem B2268679 : Blo 2267435 2268679 := bstep (se 1 (by rfl) ⟨1701509, by rfl⟩ : syracuseStep 2268679 = 3403019) B3403019
theorem B2552269 : Blo 2267435 2552269 := bbase (se 3 (by rfl) ⟨478550, by rfl⟩ : syracuseStep 2552269 = 957101) (by norm_num)
theorem B3403025 : Blo 2267435 3403025 := bstep (se 2 (by rfl) ⟨1276134, by rfl⟩ : syracuseStep 3403025 = 2552269) B2552269
theorem B2268683 : Blo 2267435 2268683 := bstep (se 1 (by rfl) ⟨1701512, by rfl⟩ : syracuseStep 2268683 = 3403025) B3403025
theorem B7656821 : Blo 2267435 7656821 := bbase (se 5 (by rfl) ⟨358913, by rfl⟩ : syracuseStep 7656821 = 717827) (by norm_num)
theorem B5104547 : Blo 2267435 5104547 := bstep (se 1 (by rfl) ⟨3828410, by rfl⟩ : syracuseStep 5104547 = 7656821) B7656821
theorem B3403031 : Blo 2267435 3403031 := bstep (se 1 (by rfl) ⟨2552273, by rfl⟩ : syracuseStep 3403031 = 5104547) B5104547
theorem B2268687 : Blo 2267435 2268687 := bstep (se 1 (by rfl) ⟨1701515, by rfl⟩ : syracuseStep 2268687 = 3403031) B3403031
theorem B3403037 : Blo 2267435 3403037 := bbase (se 3 (by rfl) ⟨638069, by rfl⟩ : syracuseStep 3403037 = 1276139) (by norm_num)
theorem B2268691 : Blo 2267435 2268691 := bstep (se 1 (by rfl) ⟨1701518, by rfl⟩ : syracuseStep 2268691 = 3403037) B3403037
theorem B5104565 : Blo 2267435 5104565 := bbase (se 5 (by rfl) ⟨239276, by rfl⟩ : syracuseStep 5104565 = 478553) (by norm_num)
theorem B3403043 : Blo 2267435 3403043 := bstep (se 1 (by rfl) ⟨2552282, by rfl⟩ : syracuseStep 3403043 = 5104565) B5104565
theorem B2268695 : Blo 2267435 2268695 := bstep (se 1 (by rfl) ⟨1701521, by rfl⟩ : syracuseStep 2268695 = 3403043) B3403043
theorem B9198613 : Blo 2267435 9198613 := bbase (se 6 (by rfl) ⟨215592, by rfl⟩ : syracuseStep 9198613 = 431185) (by norm_num)
theorem B12264817 : Blo 2267435 12264817 := bstep (se 2 (by rfl) ⟨4599306, by rfl⟩ : syracuseStep 12264817 = 9198613) B9198613
theorem B16353089 : Blo 2267435 16353089 := bstep (se 2 (by rfl) ⟨6132408, by rfl⟩ : syracuseStep 16353089 = 12264817) B12264817
theorem B10902059 : Blo 2267435 10902059 := bstep (se 1 (by rfl) ⟨8176544, by rfl⟩ : syracuseStep 10902059 = 16353089) B16353089
theorem B7268039 : Blo 2267435 7268039 := bstep (se 1 (by rfl) ⟨5451029, by rfl⟩ : syracuseStep 7268039 = 10902059) B10902059
theorem B4845359 : Blo 2267435 4845359 := bstep (se 1 (by rfl) ⟨3634019, by rfl⟩ : syracuseStep 4845359 = 7268039) B7268039
theorem B12920957 : Blo 2267435 12920957 := bstep (se 3 (by rfl) ⟨2422679, by rfl⟩ : syracuseStep 12920957 = 4845359) B4845359
theorem B8613971 : Blo 2267435 8613971 := bstep (se 1 (by rfl) ⟨6460478, by rfl⟩ : syracuseStep 8613971 = 12920957) B12920957
theorem B5742647 : Blo 2267435 5742647 := bstep (se 1 (by rfl) ⟨4306985, by rfl⟩ : syracuseStep 5742647 = 8613971) B8613971
theorem B3828431 : Blo 2267435 3828431 := bstep (se 1 (by rfl) ⟨2871323, by rfl⟩ : syracuseStep 3828431 = 5742647) B5742647
theorem B2552287 : Blo 2267435 2552287 := bstep (se 1 (by rfl) ⟨1914215, by rfl⟩ : syracuseStep 2552287 = 3828431) B3828431
theorem B3403049 : Blo 2267435 3403049 := bstep (se 2 (by rfl) ⟨1276143, by rfl⟩ : syracuseStep 3403049 = 2552287) B2552287
theorem B2268699 : Blo 2267435 2268699 := bstep (se 1 (by rfl) ⟨1701524, by rfl⟩ : syracuseStep 2268699 = 3403049) B3403049
theorem B9198629 : Blo 2267435 9198629 := bbase (se 4 (by rfl) ⟨862371, by rfl⟩ : syracuseStep 9198629 = 1724743) (by norm_num)
theorem B6132419 : Blo 2267435 6132419 := bstep (se 1 (by rfl) ⟨4599314, by rfl⟩ : syracuseStep 6132419 = 9198629) B9198629
theorem B4088279 : Blo 2267435 4088279 := bstep (se 1 (by rfl) ⟨3066209, by rfl⟩ : syracuseStep 4088279 = 6132419) B6132419
theorem B10902077 : Blo 2267435 10902077 := bstep (se 3 (by rfl) ⟨2044139, by rfl⟩ : syracuseStep 10902077 = 4088279) B4088279
theorem B7268051 : Blo 2267435 7268051 := bstep (se 1 (by rfl) ⟨5451038, by rfl⟩ : syracuseStep 7268051 = 10902077) B10902077
theorem B4845367 : Blo 2267435 4845367 := bstep (se 1 (by rfl) ⟨3634025, by rfl⟩ : syracuseStep 4845367 = 7268051) B7268051
theorem B6460489 : Blo 2267435 6460489 := bstep (se 2 (by rfl) ⟨2422683, by rfl⟩ : syracuseStep 6460489 = 4845367) B4845367
theorem B8613985 : Blo 2267435 8613985 := bstep (se 2 (by rfl) ⟨3230244, by rfl⟩ : syracuseStep 8613985 = 6460489) B6460489
theorem B11485313 : Blo 2267435 11485313 := bstep (se 2 (by rfl) ⟨4306992, by rfl⟩ : syracuseStep 11485313 = 8613985) B8613985
theorem B7656875 : Blo 2267435 7656875 := bstep (se 1 (by rfl) ⟨5742656, by rfl⟩ : syracuseStep 7656875 = 11485313) B11485313
theorem B5104583 : Blo 2267435 5104583 := bstep (se 1 (by rfl) ⟨3828437, by rfl⟩ : syracuseStep 5104583 = 7656875) B7656875
theorem B3403055 : Blo 2267435 3403055 := bstep (se 1 (by rfl) ⟨2552291, by rfl⟩ : syracuseStep 3403055 = 5104583) B5104583
theorem B2268703 : Blo 2267435 2268703 := bstep (se 1 (by rfl) ⟨1701527, by rfl⟩ : syracuseStep 2268703 = 3403055) B3403055
theorem B3403061 : Blo 2267435 3403061 := bbase (se 5 (by rfl) ⟨159518, by rfl⟩ : syracuseStep 3403061 = 319037) (by norm_num)
theorem B2268707 : Blo 2267435 2268707 := bstep (se 1 (by rfl) ⟨1701530, by rfl⟩ : syracuseStep 2268707 = 3403061) B3403061
theorem B5742677 : Blo 2267435 5742677 := bbase (se 8 (by rfl) ⟨33648, by rfl⟩ : syracuseStep 5742677 = 67297) (by norm_num)
theorem B3828451 : Blo 2267435 3828451 := bstep (se 1 (by rfl) ⟨2871338, by rfl⟩ : syracuseStep 3828451 = 5742677) B5742677
theorem B5104601 : Blo 2267435 5104601 := bstep (se 2 (by rfl) ⟨1914225, by rfl⟩ : syracuseStep 5104601 = 3828451) B3828451
theorem B3403067 : Blo 2267435 3403067 := bstep (se 1 (by rfl) ⟨2552300, by rfl⟩ : syracuseStep 3403067 = 5104601) B5104601
theorem B2268711 : Blo 2267435 2268711 := bstep (se 1 (by rfl) ⟨1701533, by rfl⟩ : syracuseStep 2268711 = 3403067) B3403067
theorem B2552305 : Blo 2267435 2552305 := bbase (se 2 (by rfl) ⟨957114, by rfl⟩ : syracuseStep 2552305 = 1914229) (by norm_num)
theorem B3403073 : Blo 2267435 3403073 := bstep (se 2 (by rfl) ⟨1276152, by rfl⟩ : syracuseStep 3403073 = 2552305) B2552305
theorem B2268715 : Blo 2267435 2268715 := bstep (se 1 (by rfl) ⟨1701536, by rfl⟩ : syracuseStep 2268715 = 3403073) B3403073
theorem B5451077 : Blo 2267435 5451077 := bbase (se 4 (by rfl) ⟨511038, by rfl⟩ : syracuseStep 5451077 = 1022077) (by norm_num)
theorem B14536205 : Blo 2267435 14536205 := bstep (se 3 (by rfl) ⟨2725538, by rfl⟩ : syracuseStep 14536205 = 5451077) B5451077
theorem B9690803 : Blo 2267435 9690803 := bstep (se 1 (by rfl) ⟨7268102, by rfl⟩ : syracuseStep 9690803 = 14536205) B14536205
theorem B6460535 : Blo 2267435 6460535 := bstep (se 1 (by rfl) ⟨4845401, by rfl⟩ : syracuseStep 6460535 = 9690803) B9690803
theorem B4307023 : Blo 2267435 4307023 := bstep (se 1 (by rfl) ⟨3230267, by rfl⟩ : syracuseStep 4307023 = 6460535) B6460535
theorem B5742697 : Blo 2267435 5742697 := bstep (se 2 (by rfl) ⟨2153511, by rfl⟩ : syracuseStep 5742697 = 4307023) B4307023
theorem B7656929 : Blo 2267435 7656929 := bstep (se 2 (by rfl) ⟨2871348, by rfl⟩ : syracuseStep 7656929 = 5742697) B5742697
theorem B5104619 : Blo 2267435 5104619 := bstep (se 1 (by rfl) ⟨3828464, by rfl⟩ : syracuseStep 5104619 = 7656929) B7656929
theorem B3403079 : Blo 2267435 3403079 := bstep (se 1 (by rfl) ⟨2552309, by rfl⟩ : syracuseStep 3403079 = 5104619) B5104619
theorem B2268719 : Blo 2267435 2268719 := bstep (se 1 (by rfl) ⟨1701539, by rfl⟩ : syracuseStep 2268719 = 3403079) B3403079
theorem B3403085 : Blo 2267435 3403085 := bbase (se 3 (by rfl) ⟨638078, by rfl⟩ : syracuseStep 3403085 = 1276157) (by norm_num)
theorem B2268723 : Blo 2267435 2268723 := bstep (se 1 (by rfl) ⟨1701542, by rfl⟩ : syracuseStep 2268723 = 3403085) B3403085
theorem B5104637 : Blo 2267435 5104637 := bbase (se 3 (by rfl) ⟨957119, by rfl⟩ : syracuseStep 5104637 = 1914239) (by norm_num)
theorem B3403091 : Blo 2267435 3403091 := bstep (se 1 (by rfl) ⟨2552318, by rfl⟩ : syracuseStep 3403091 = 5104637) B5104637
theorem B2268727 : Blo 2267435 2268727 := bstep (se 1 (by rfl) ⟨1701545, by rfl⟩ : syracuseStep 2268727 = 3403091) B3403091
theorem B3828485 : Blo 2267435 3828485 := bbase (se 4 (by rfl) ⟨358920, by rfl⟩ : syracuseStep 3828485 = 717841) (by norm_num)
theorem B2552323 : Blo 2267435 2552323 := bstep (se 1 (by rfl) ⟨1914242, by rfl⟩ : syracuseStep 2552323 = 3828485) B3828485
theorem B3403097 : Blo 2267435 3403097 := bstep (se 2 (by rfl) ⟨1276161, by rfl⟩ : syracuseStep 3403097 = 2552323) B2552323
theorem B2268731 : Blo 2267435 2268731 := bstep (se 1 (by rfl) ⟨1701548, by rfl⟩ : syracuseStep 2268731 = 3403097) B3403097
theorem B17228213 : Blo 2267435 17228213 := bbase (se 5 (by rfl) ⟨807572, by rfl⟩ : syracuseStep 17228213 = 1615145) (by norm_num)
theorem B11485475 : Blo 2267435 11485475 := bstep (se 1 (by rfl) ⟨8614106, by rfl⟩ : syracuseStep 11485475 = 17228213) B17228213
theorem B7656983 : Blo 2267435 7656983 := bstep (se 1 (by rfl) ⟨5742737, by rfl⟩ : syracuseStep 7656983 = 11485475) B11485475
theorem B5104655 : Blo 2267435 5104655 := bstep (se 1 (by rfl) ⟨3828491, by rfl⟩ : syracuseStep 5104655 = 7656983) B7656983
theorem B3403103 : Blo 2267435 3403103 := bstep (se 1 (by rfl) ⟨2552327, by rfl⟩ : syracuseStep 3403103 = 5104655) B5104655
theorem B2268735 : Blo 2267435 2268735 := bstep (se 1 (by rfl) ⟨1701551, by rfl⟩ : syracuseStep 2268735 = 3403103) B3403103
theorem B3403109 : Blo 2267435 3403109 := bbase (se 4 (by rfl) ⟨319041, by rfl⟩ : syracuseStep 3403109 = 638083) (by norm_num)
theorem B2268739 : Blo 2267435 2268739 := bstep (se 1 (by rfl) ⟨1701554, by rfl⟩ : syracuseStep 2268739 = 3403109) B3403109
theorem B4307069 : Blo 2267435 4307069 := bbase (se 3 (by rfl) ⟨807575, by rfl⟩ : syracuseStep 4307069 = 1615151) (by norm_num)
theorem B2871379 : Blo 2267435 2871379 := bstep (se 1 (by rfl) ⟨2153534, by rfl⟩ : syracuseStep 2871379 = 4307069) B4307069
theorem B3828505 : Blo 2267435 3828505 := bstep (se 2 (by rfl) ⟨1435689, by rfl⟩ : syracuseStep 3828505 = 2871379) B2871379
theorem B5104673 : Blo 2267435 5104673 := bstep (se 2 (by rfl) ⟨1914252, by rfl⟩ : syracuseStep 5104673 = 3828505) B3828505
theorem B3403115 : Blo 2267435 3403115 := bstep (se 1 (by rfl) ⟨2552336, by rfl⟩ : syracuseStep 3403115 = 5104673) B5104673
theorem B2268743 : Blo 2267435 2268743 := bstep (se 1 (by rfl) ⟨1701557, by rfl⟩ : syracuseStep 2268743 = 3403115) B3403115
theorem B2552341 : Blo 2267435 2552341 := bbase (se 6 (by rfl) ⟨59820, by rfl⟩ : syracuseStep 2552341 = 119641) (by norm_num)
theorem B3403121 : Blo 2267435 3403121 := bstep (se 2 (by rfl) ⟨1276170, by rfl⟩ : syracuseStep 3403121 = 2552341) B2552341
theorem B2268747 : Blo 2267435 2268747 := bstep (se 1 (by rfl) ⟨1701560, by rfl⟩ : syracuseStep 2268747 = 3403121) B3403121
theorem B2871389 : Blo 2267435 2871389 := bbase (se 3 (by rfl) ⟨538385, by rfl⟩ : syracuseStep 2871389 = 1076771) (by norm_num)
theorem B7657037 : Blo 2267435 7657037 := bstep (se 3 (by rfl) ⟨1435694, by rfl⟩ : syracuseStep 7657037 = 2871389) B2871389
theorem B5104691 : Blo 2267435 5104691 := bstep (se 1 (by rfl) ⟨3828518, by rfl⟩ : syracuseStep 5104691 = 7657037) B7657037
theorem B3403127 : Blo 2267435 3403127 := bstep (se 1 (by rfl) ⟨2552345, by rfl⟩ : syracuseStep 3403127 = 5104691) B5104691
theorem B2268751 : Blo 2267435 2268751 := bstep (se 1 (by rfl) ⟨1701563, by rfl⟩ : syracuseStep 2268751 = 3403127) B3403127
theorem B3403133 : Blo 2267435 3403133 := bbase (se 3 (by rfl) ⟨638087, by rfl⟩ : syracuseStep 3403133 = 1276175) (by norm_num)
theorem B2268755 : Blo 2267435 2268755 := bstep (se 1 (by rfl) ⟨1701566, by rfl⟩ : syracuseStep 2268755 = 3403133) B3403133
theorem B5104709 : Blo 2267435 5104709 := bbase (se 4 (by rfl) ⟨478566, by rfl⟩ : syracuseStep 5104709 = 957133) (by norm_num)
theorem B3403139 : Blo 2267435 3403139 := bstep (se 1 (by rfl) ⟨2552354, by rfl⟩ : syracuseStep 3403139 = 5104709) B5104709
theorem B2268759 : Blo 2267435 2268759 := bstep (se 1 (by rfl) ⟨1701569, by rfl⟩ : syracuseStep 2268759 = 3403139) B3403139
theorem B6460661 : Blo 2267435 6460661 := bbase (se 5 (by rfl) ⟨302843, by rfl⟩ : syracuseStep 6460661 = 605687) (by norm_num)
theorem B4307107 : Blo 2267435 4307107 := bstep (se 1 (by rfl) ⟨3230330, by rfl⟩ : syracuseStep 4307107 = 6460661) B6460661
theorem B5742809 : Blo 2267435 5742809 := bstep (se 2 (by rfl) ⟨2153553, by rfl⟩ : syracuseStep 5742809 = 4307107) B4307107
theorem B3828539 : Blo 2267435 3828539 := bstep (se 1 (by rfl) ⟨2871404, by rfl⟩ : syracuseStep 3828539 = 5742809) B5742809
theorem B2552359 : Blo 2267435 2552359 := bstep (se 1 (by rfl) ⟨1914269, by rfl⟩ : syracuseStep 2552359 = 3828539) B3828539
theorem B3403145 : Blo 2267435 3403145 := bstep (se 2 (by rfl) ⟨1276179, by rfl⟩ : syracuseStep 3403145 = 2552359) B2552359
theorem B2268763 : Blo 2267435 2268763 := bstep (se 1 (by rfl) ⟨1701572, by rfl⟩ : syracuseStep 2268763 = 3403145) B3403145
theorem B11485637 : Blo 2267435 11485637 := bbase (se 4 (by rfl) ⟨1076778, by rfl⟩ : syracuseStep 11485637 = 2153557) (by norm_num)
theorem B7657091 : Blo 2267435 7657091 := bstep (se 1 (by rfl) ⟨5742818, by rfl⟩ : syracuseStep 7657091 = 11485637) B11485637
theorem B5104727 : Blo 2267435 5104727 := bstep (se 1 (by rfl) ⟨3828545, by rfl⟩ : syracuseStep 5104727 = 7657091) B7657091
theorem B3403151 : Blo 2267435 3403151 := bstep (se 1 (by rfl) ⟨2552363, by rfl⟩ : syracuseStep 3403151 = 5104727) B5104727
theorem B2268767 : Blo 2267435 2268767 := bstep (se 1 (by rfl) ⟨1701575, by rfl⟩ : syracuseStep 2268767 = 3403151) B3403151
theorem B3403157 : Blo 2267435 3403157 := bbase (se 6 (by rfl) ⟨79761, by rfl⟩ : syracuseStep 3403157 = 159523) (by norm_num)
theorem B2268771 : Blo 2267435 2268771 := bstep (se 1 (by rfl) ⟨1701578, by rfl⟩ : syracuseStep 2268771 = 3403157) B3403157
theorem B3634141 : Blo 2267435 3634141 := bbase (se 3 (by rfl) ⟨681401, by rfl⟩ : syracuseStep 3634141 = 1362803) (by norm_num)
theorem B4845521 : Blo 2267435 4845521 := bstep (se 2 (by rfl) ⟨1817070, by rfl⟩ : syracuseStep 4845521 = 3634141) B3634141
theorem B12921389 : Blo 2267435 12921389 := bstep (se 3 (by rfl) ⟨2422760, by rfl⟩ : syracuseStep 12921389 = 4845521) B4845521
theorem B8614259 : Blo 2267435 8614259 := bstep (se 1 (by rfl) ⟨6460694, by rfl⟩ : syracuseStep 8614259 = 12921389) B12921389
theorem B5742839 : Blo 2267435 5742839 := bstep (se 1 (by rfl) ⟨4307129, by rfl⟩ : syracuseStep 5742839 = 8614259) B8614259
theorem B3828559 : Blo 2267435 3828559 := bstep (se 1 (by rfl) ⟨2871419, by rfl⟩ : syracuseStep 3828559 = 5742839) B5742839
theorem B5104745 : Blo 2267435 5104745 := bstep (se 2 (by rfl) ⟨1914279, by rfl⟩ : syracuseStep 5104745 = 3828559) B3828559
theorem B3403163 : Blo 2267435 3403163 := bstep (se 1 (by rfl) ⟨2552372, by rfl⟩ : syracuseStep 3403163 = 5104745) B5104745
theorem B2268775 : Blo 2267435 2268775 := bstep (se 1 (by rfl) ⟨1701581, by rfl⟩ : syracuseStep 2268775 = 3403163) B3403163
theorem B2552377 : Blo 2267435 2552377 := bbase (se 2 (by rfl) ⟨957141, by rfl⟩ : syracuseStep 2552377 = 1914283) (by norm_num)
theorem B3403169 : Blo 2267435 3403169 := bstep (se 2 (by rfl) ⟨1276188, by rfl⟩ : syracuseStep 3403169 = 2552377) B2552377
theorem B2268779 : Blo 2267435 2268779 := bstep (se 1 (by rfl) ⟨1701584, by rfl⟩ : syracuseStep 2268779 = 3403169) B3403169
theorem B2422769 : Blo 2267435 2422769 := bbase (se 2 (by rfl) ⟨908538, by rfl⟩ : syracuseStep 2422769 = 1817077) (by norm_num)
theorem B6460717 : Blo 2267435 6460717 := bstep (se 3 (by rfl) ⟨1211384, by rfl⟩ : syracuseStep 6460717 = 2422769) B2422769
theorem B8614289 : Blo 2267435 8614289 := bstep (se 2 (by rfl) ⟨3230358, by rfl⟩ : syracuseStep 8614289 = 6460717) B6460717
theorem B5742859 : Blo 2267435 5742859 := bstep (se 1 (by rfl) ⟨4307144, by rfl⟩ : syracuseStep 5742859 = 8614289) B8614289
theorem B7657145 : Blo 2267435 7657145 := bstep (se 2 (by rfl) ⟨2871429, by rfl⟩ : syracuseStep 7657145 = 5742859) B5742859
theorem B5104763 : Blo 2267435 5104763 := bstep (se 1 (by rfl) ⟨3828572, by rfl⟩ : syracuseStep 5104763 = 7657145) B7657145
theorem B3403175 : Blo 2267435 3403175 := bstep (se 1 (by rfl) ⟨2552381, by rfl⟩ : syracuseStep 3403175 = 5104763) B5104763
theorem B2268783 : Blo 2267435 2268783 := bstep (se 1 (by rfl) ⟨1701587, by rfl⟩ : syracuseStep 2268783 = 3403175) B3403175
theorem B3403181 : Blo 2267435 3403181 := bbase (se 3 (by rfl) ⟨638096, by rfl⟩ : syracuseStep 3403181 = 1276193) (by norm_num)
theorem B2268787 : Blo 2267435 2268787 := bstep (se 1 (by rfl) ⟨1701590, by rfl⟩ : syracuseStep 2268787 = 3403181) B3403181
theorem B5104781 : Blo 2267435 5104781 := bbase (se 3 (by rfl) ⟨957146, by rfl⟩ : syracuseStep 5104781 = 1914293) (by norm_num)
theorem B3403187 : Blo 2267435 3403187 := bstep (se 1 (by rfl) ⟨2552390, by rfl⟩ : syracuseStep 3403187 = 5104781) B5104781
theorem B2268791 : Blo 2267435 2268791 := bstep (se 1 (by rfl) ⟨1701593, by rfl⟩ : syracuseStep 2268791 = 3403187) B3403187
theorem B2871445 : Blo 2267435 2871445 := bbase (se 6 (by rfl) ⟨67299, by rfl⟩ : syracuseStep 2871445 = 134599) (by norm_num)
theorem B3828593 : Blo 2267435 3828593 := bstep (se 2 (by rfl) ⟨1435722, by rfl⟩ : syracuseStep 3828593 = 2871445) B2871445
theorem B2552395 : Blo 2267435 2552395 := bstep (se 1 (by rfl) ⟨1914296, by rfl⟩ : syracuseStep 2552395 = 3828593) B3828593
theorem B3403193 : Blo 2267435 3403193 := bstep (se 2 (by rfl) ⟨1276197, by rfl⟩ : syracuseStep 3403193 = 2552395) B2552395
theorem B2268795 : Blo 2267435 2268795 := bstep (se 1 (by rfl) ⟨1701596, by rfl⟩ : syracuseStep 2268795 = 3403193) B3403193
theorem B6132677 : Blo 2267435 6132677 := bbase (se 4 (by rfl) ⟨574938, by rfl⟩ : syracuseStep 6132677 = 1149877) (by norm_num)
theorem B65415221 : Blo 2267435 65415221 := bstep (se 5 (by rfl) ⟨3066338, by rfl⟩ : syracuseStep 65415221 = 6132677) B6132677
theorem B43610147 : Blo 2267435 43610147 := bstep (se 1 (by rfl) ⟨32707610, by rfl⟩ : syracuseStep 43610147 = 65415221) B65415221
theorem B29073431 : Blo 2267435 29073431 := bstep (se 1 (by rfl) ⟨21805073, by rfl⟩ : syracuseStep 29073431 = 43610147) B43610147
theorem B19382287 : Blo 2267435 19382287 := bstep (se 1 (by rfl) ⟨14536715, by rfl⟩ : syracuseStep 19382287 = 29073431) B29073431
theorem B25843049 : Blo 2267435 25843049 := bstep (se 2 (by rfl) ⟨9691143, by rfl⟩ : syracuseStep 25843049 = 19382287) B19382287
theorem B17228699 : Blo 2267435 17228699 := bstep (se 1 (by rfl) ⟨12921524, by rfl⟩ : syracuseStep 17228699 = 25843049) B25843049
theorem B11485799 : Blo 2267435 11485799 := bstep (se 1 (by rfl) ⟨8614349, by rfl⟩ : syracuseStep 11485799 = 17228699) B17228699
theorem B7657199 : Blo 2267435 7657199 := bstep (se 1 (by rfl) ⟨5742899, by rfl⟩ : syracuseStep 7657199 = 11485799) B11485799
theorem B5104799 : Blo 2267435 5104799 := bstep (se 1 (by rfl) ⟨3828599, by rfl⟩ : syracuseStep 5104799 = 7657199) B7657199
theorem B3403199 : Blo 2267435 3403199 := bstep (se 1 (by rfl) ⟨2552399, by rfl⟩ : syracuseStep 3403199 = 5104799) B5104799
theorem B2268799 : Blo 2267435 2268799 := bstep (se 1 (by rfl) ⟨1701599, by rfl⟩ : syracuseStep 2268799 = 3403199) B3403199
theorem B3403205 : Blo 2267435 3403205 := bbase (se 4 (by rfl) ⟨319050, by rfl⟩ : syracuseStep 3403205 = 638101) (by norm_num)
theorem B2268803 : Blo 2267435 2268803 := bstep (se 1 (by rfl) ⟨1701602, by rfl⟩ : syracuseStep 2268803 = 3403205) B3403205
theorem B3828613 : Blo 2267435 3828613 := bbase (se 4 (by rfl) ⟨358932, by rfl⟩ : syracuseStep 3828613 = 717865) (by norm_num)
theorem B5104817 : Blo 2267435 5104817 := bstep (se 2 (by rfl) ⟨1914306, by rfl⟩ : syracuseStep 5104817 = 3828613) B3828613
theorem B3403211 : Blo 2267435 3403211 := bstep (se 1 (by rfl) ⟨2552408, by rfl⟩ : syracuseStep 3403211 = 5104817) B5104817
theorem B2268807 : Blo 2267435 2268807 := bstep (se 1 (by rfl) ⟨1701605, by rfl⟩ : syracuseStep 2268807 = 3403211) B3403211
theorem B2552413 : Blo 2267435 2552413 := bbase (se 3 (by rfl) ⟨478577, by rfl⟩ : syracuseStep 2552413 = 957155) (by norm_num)
theorem B3403217 : Blo 2267435 3403217 := bstep (se 2 (by rfl) ⟨1276206, by rfl⟩ : syracuseStep 3403217 = 2552413) B2552413
theorem B2268811 : Blo 2267435 2268811 := bstep (se 1 (by rfl) ⟨1701608, by rfl⟩ : syracuseStep 2268811 = 3403217) B3403217
theorem B7657253 : Blo 2267435 7657253 := bbase (se 4 (by rfl) ⟨717867, by rfl⟩ : syracuseStep 7657253 = 1435735) (by norm_num)
theorem B5104835 : Blo 2267435 5104835 := bstep (se 1 (by rfl) ⟨3828626, by rfl⟩ : syracuseStep 5104835 = 7657253) B7657253
theorem B3403223 : Blo 2267435 3403223 := bstep (se 1 (by rfl) ⟨2552417, by rfl⟩ : syracuseStep 3403223 = 5104835) B5104835
theorem B2268815 : Blo 2267435 2268815 := bstep (se 1 (by rfl) ⟨1701611, by rfl⟩ : syracuseStep 2268815 = 3403223) B3403223
theorem B3403229 : Blo 2267435 3403229 := bbase (se 3 (by rfl) ⟨638105, by rfl⟩ : syracuseStep 3403229 = 1276211) (by norm_num)
theorem B2268819 : Blo 2267435 2268819 := bstep (se 1 (by rfl) ⟨1701614, by rfl⟩ : syracuseStep 2268819 = 3403229) B3403229
theorem B5104853 : Blo 2267435 5104853 := bbase (se 7 (by rfl) ⟨59822, by rfl⟩ : syracuseStep 5104853 = 119645) (by norm_num)
theorem B3403235 : Blo 2267435 3403235 := bstep (se 1 (by rfl) ⟨2552426, by rfl⟩ : syracuseStep 3403235 = 5104853) B5104853
theorem B2268823 : Blo 2267435 2268823 := bstep (se 1 (by rfl) ⟨1701617, by rfl⟩ : syracuseStep 2268823 = 3403235) B3403235
theorem B3880885 : Blo 2267435 3880885 := bbase (se 5 (by rfl) ⟨181916, by rfl⟩ : syracuseStep 3880885 = 363833) (by norm_num)
theorem B5174513 : Blo 2267435 5174513 := bstep (se 2 (by rfl) ⟨1940442, by rfl⟩ : syracuseStep 5174513 = 3880885) B3880885
theorem B3449675 : Blo 2267435 3449675 := bstep (se 1 (by rfl) ⟨2587256, by rfl⟩ : syracuseStep 3449675 = 5174513) B5174513
theorem B9199133 : Blo 2267435 9199133 := bstep (se 3 (by rfl) ⟨1724837, by rfl⟩ : syracuseStep 9199133 = 3449675) B3449675
theorem B6132755 : Blo 2267435 6132755 := bstep (se 1 (by rfl) ⟨4599566, by rfl⟩ : syracuseStep 6132755 = 9199133) B9199133
theorem B4088503 : Blo 2267435 4088503 := bstep (se 1 (by rfl) ⟨3066377, by rfl⟩ : syracuseStep 4088503 = 6132755) B6132755
theorem B5451337 : Blo 2267435 5451337 := bstep (se 2 (by rfl) ⟨2044251, by rfl⟩ : syracuseStep 5451337 = 4088503) B4088503
theorem B7268449 : Blo 2267435 7268449 := bstep (se 2 (by rfl) ⟨2725668, by rfl⟩ : syracuseStep 7268449 = 5451337) B5451337
theorem B9691265 : Blo 2267435 9691265 := bstep (se 2 (by rfl) ⟨3634224, by rfl⟩ : syracuseStep 9691265 = 7268449) B7268449
theorem B6460843 : Blo 2267435 6460843 := bstep (se 1 (by rfl) ⟨4845632, by rfl⟩ : syracuseStep 6460843 = 9691265) B9691265
theorem B8614457 : Blo 2267435 8614457 := bstep (se 2 (by rfl) ⟨3230421, by rfl⟩ : syracuseStep 8614457 = 6460843) B6460843
theorem B5742971 : Blo 2267435 5742971 := bstep (se 1 (by rfl) ⟨4307228, by rfl⟩ : syracuseStep 5742971 = 8614457) B8614457
theorem B3828647 : Blo 2267435 3828647 := bstep (se 1 (by rfl) ⟨2871485, by rfl⟩ : syracuseStep 3828647 = 5742971) B5742971
theorem B2552431 : Blo 2267435 2552431 := bstep (se 1 (by rfl) ⟨1914323, by rfl⟩ : syracuseStep 2552431 = 3828647) B3828647
theorem B3403241 : Blo 2267435 3403241 := bstep (se 2 (by rfl) ⟨1276215, by rfl⟩ : syracuseStep 3403241 = 2552431) B2552431
theorem B2268827 : Blo 2267435 2268827 := bstep (se 1 (by rfl) ⟨1701620, by rfl⟩ : syracuseStep 2268827 = 3403241) B3403241
theorem B16354037 : Blo 2267435 16354037 := bbase (se 5 (by rfl) ⟨766595, by rfl⟩ : syracuseStep 16354037 = 1533191) (by norm_num)
theorem B10902691 : Blo 2267435 10902691 := bstep (se 1 (by rfl) ⟨8177018, by rfl⟩ : syracuseStep 10902691 = 16354037) B16354037
theorem B14536921 : Blo 2267435 14536921 := bstep (se 2 (by rfl) ⟨5451345, by rfl⟩ : syracuseStep 14536921 = 10902691) B10902691
theorem B19382561 : Blo 2267435 19382561 := bstep (se 2 (by rfl) ⟨7268460, by rfl⟩ : syracuseStep 19382561 = 14536921) B14536921
theorem B12921707 : Blo 2267435 12921707 := bstep (se 1 (by rfl) ⟨9691280, by rfl⟩ : syracuseStep 12921707 = 19382561) B19382561
theorem B8614471 : Blo 2267435 8614471 := bstep (se 1 (by rfl) ⟨6460853, by rfl⟩ : syracuseStep 8614471 = 12921707) B12921707
theorem B11485961 : Blo 2267435 11485961 := bstep (se 2 (by rfl) ⟨4307235, by rfl⟩ : syracuseStep 11485961 = 8614471) B8614471
theorem B7657307 : Blo 2267435 7657307 := bstep (se 1 (by rfl) ⟨5742980, by rfl⟩ : syracuseStep 7657307 = 11485961) B11485961
theorem B5104871 : Blo 2267435 5104871 := bstep (se 1 (by rfl) ⟨3828653, by rfl⟩ : syracuseStep 5104871 = 7657307) B7657307
theorem B3403247 : Blo 2267435 3403247 := bstep (se 1 (by rfl) ⟨2552435, by rfl⟩ : syracuseStep 3403247 = 5104871) B5104871
theorem B2268831 : Blo 2267435 2268831 := bstep (se 1 (by rfl) ⟨1701623, by rfl⟩ : syracuseStep 2268831 = 3403247) B3403247
theorem B3403253 : Blo 2267435 3403253 := bbase (se 5 (by rfl) ⟨159527, by rfl⟩ : syracuseStep 3403253 = 319055) (by norm_num)
theorem B2268835 : Blo 2267435 2268835 := bstep (se 1 (by rfl) ⟨1701626, by rfl⟩ : syracuseStep 2268835 = 3403253) B3403253
theorem B2422829 : Blo 2267435 2422829 := bbase (se 3 (by rfl) ⟨454280, by rfl⟩ : syracuseStep 2422829 = 908561) (by norm_num)
theorem B6460877 : Blo 2267435 6460877 := bstep (se 3 (by rfl) ⟨1211414, by rfl⟩ : syracuseStep 6460877 = 2422829) B2422829
theorem B4307251 : Blo 2267435 4307251 := bstep (se 1 (by rfl) ⟨3230438, by rfl⟩ : syracuseStep 4307251 = 6460877) B6460877
theorem B5743001 : Blo 2267435 5743001 := bstep (se 2 (by rfl) ⟨2153625, by rfl⟩ : syracuseStep 5743001 = 4307251) B4307251
theorem B3828667 : Blo 2267435 3828667 := bstep (se 1 (by rfl) ⟨2871500, by rfl⟩ : syracuseStep 3828667 = 5743001) B5743001
theorem B5104889 : Blo 2267435 5104889 := bstep (se 2 (by rfl) ⟨1914333, by rfl⟩ : syracuseStep 5104889 = 3828667) B3828667
theorem B3403259 : Blo 2267435 3403259 := bstep (se 1 (by rfl) ⟨2552444, by rfl⟩ : syracuseStep 3403259 = 5104889) B5104889
theorem B2268839 : Blo 2267435 2268839 := bstep (se 1 (by rfl) ⟨1701629, by rfl⟩ : syracuseStep 2268839 = 3403259) B3403259
theorem B2552449 : Blo 2267435 2552449 := bbase (se 2 (by rfl) ⟨957168, by rfl⟩ : syracuseStep 2552449 = 1914337) (by norm_num)
theorem B3403265 : Blo 2267435 3403265 := bstep (se 2 (by rfl) ⟨1276224, by rfl⟩ : syracuseStep 3403265 = 2552449) B2552449
theorem B2268843 : Blo 2267435 2268843 := bstep (se 1 (by rfl) ⟨1701632, by rfl⟩ : syracuseStep 2268843 = 3403265) B3403265
theorem B5743021 : Blo 2267435 5743021 := bbase (se 3 (by rfl) ⟨1076816, by rfl⟩ : syracuseStep 5743021 = 2153633) (by norm_num)
theorem B7657361 : Blo 2267435 7657361 := bstep (se 2 (by rfl) ⟨2871510, by rfl⟩ : syracuseStep 7657361 = 5743021) B5743021
theorem B5104907 : Blo 2267435 5104907 := bstep (se 1 (by rfl) ⟨3828680, by rfl⟩ : syracuseStep 5104907 = 7657361) B7657361
theorem B3403271 : Blo 2267435 3403271 := bstep (se 1 (by rfl) ⟨2552453, by rfl⟩ : syracuseStep 3403271 = 5104907) B5104907
theorem B2268847 : Blo 2267435 2268847 := bstep (se 1 (by rfl) ⟨1701635, by rfl⟩ : syracuseStep 2268847 = 3403271) B3403271
theorem B3403277 : Blo 2267435 3403277 := bbase (se 3 (by rfl) ⟨638114, by rfl⟩ : syracuseStep 3403277 = 1276229) (by norm_num)
theorem B2268851 : Blo 2267435 2268851 := bstep (se 1 (by rfl) ⟨1701638, by rfl⟩ : syracuseStep 2268851 = 3403277) B3403277
theorem B5104925 : Blo 2267435 5104925 := bbase (se 3 (by rfl) ⟨957173, by rfl⟩ : syracuseStep 5104925 = 1914347) (by norm_num)
theorem B3403283 : Blo 2267435 3403283 := bstep (se 1 (by rfl) ⟨2552462, by rfl⟩ : syracuseStep 3403283 = 5104925) B5104925
theorem B2268855 : Blo 2267435 2268855 := bstep (se 1 (by rfl) ⟨1701641, by rfl⟩ : syracuseStep 2268855 = 3403283) B3403283
theorem B3828701 : Blo 2267435 3828701 := bbase (se 3 (by rfl) ⟨717881, by rfl⟩ : syracuseStep 3828701 = 1435763) (by norm_num)
theorem B2552467 : Blo 2267435 2552467 := bstep (se 1 (by rfl) ⟨1914350, by rfl⟩ : syracuseStep 2552467 = 3828701) B3828701
theorem B3403289 : Blo 2267435 3403289 := bstep (se 2 (by rfl) ⟨1276233, by rfl⟩ : syracuseStep 3403289 = 2552467) B2552467
theorem B2268859 : Blo 2267435 2268859 := bstep (se 1 (by rfl) ⟨1701644, by rfl⟩ : syracuseStep 2268859 = 3403289) B3403289
theorem B2587297 : Blo 2267435 2587297 := bbase (se 2 (by rfl) ⟨970236, by rfl⟩ : syracuseStep 2587297 = 1940473) (by norm_num)
theorem B3449729 : Blo 2267435 3449729 := bstep (se 2 (by rfl) ⟨1293648, by rfl⟩ : syracuseStep 3449729 = 2587297) B2587297
theorem B9199277 : Blo 2267435 9199277 := bstep (se 3 (by rfl) ⟨1724864, by rfl⟩ : syracuseStep 9199277 = 3449729) B3449729
theorem B6132851 : Blo 2267435 6132851 := bstep (se 1 (by rfl) ⟨4599638, by rfl⟩ : syracuseStep 6132851 = 9199277) B9199277
theorem B4088567 : Blo 2267435 4088567 := bstep (se 1 (by rfl) ⟨3066425, by rfl⟩ : syracuseStep 4088567 = 6132851) B6132851
theorem B10902845 : Blo 2267435 10902845 := bstep (se 3 (by rfl) ⟨2044283, by rfl⟩ : syracuseStep 10902845 = 4088567) B4088567
theorem B7268563 : Blo 2267435 7268563 := bstep (se 1 (by rfl) ⟨5451422, by rfl⟩ : syracuseStep 7268563 = 10902845) B10902845
theorem B9691417 : Blo 2267435 9691417 := bstep (se 2 (by rfl) ⟨3634281, by rfl⟩ : syracuseStep 9691417 = 7268563) B7268563
theorem B12921889 : Blo 2267435 12921889 := bstep (se 2 (by rfl) ⟨4845708, by rfl⟩ : syracuseStep 12921889 = 9691417) B9691417
theorem B17229185 : Blo 2267435 17229185 := bstep (se 2 (by rfl) ⟨6460944, by rfl⟩ : syracuseStep 17229185 = 12921889) B12921889
theorem B11486123 : Blo 2267435 11486123 := bstep (se 1 (by rfl) ⟨8614592, by rfl⟩ : syracuseStep 11486123 = 17229185) B17229185
theorem B7657415 : Blo 2267435 7657415 := bstep (se 1 (by rfl) ⟨5743061, by rfl⟩ : syracuseStep 7657415 = 11486123) B11486123
theorem B5104943 : Blo 2267435 5104943 := bstep (se 1 (by rfl) ⟨3828707, by rfl⟩ : syracuseStep 5104943 = 7657415) B7657415
theorem B3403295 : Blo 2267435 3403295 := bstep (se 1 (by rfl) ⟨2552471, by rfl⟩ : syracuseStep 3403295 = 5104943) B5104943
theorem B2268863 : Blo 2267435 2268863 := bstep (se 1 (by rfl) ⟨1701647, by rfl⟩ : syracuseStep 2268863 = 3403295) B3403295
theorem B3403301 : Blo 2267435 3403301 := bbase (se 4 (by rfl) ⟨319059, by rfl⟩ : syracuseStep 3403301 = 638119) (by norm_num)
theorem B2268867 : Blo 2267435 2268867 := bstep (se 1 (by rfl) ⟨1701650, by rfl⟩ : syracuseStep 2268867 = 3403301) B3403301
theorem B2871541 : Blo 2267435 2871541 := bbase (se 5 (by rfl) ⟨134603, by rfl⟩ : syracuseStep 2871541 = 269207) (by norm_num)
theorem B3828721 : Blo 2267435 3828721 := bstep (se 2 (by rfl) ⟨1435770, by rfl⟩ : syracuseStep 3828721 = 2871541) B2871541
theorem B5104961 : Blo 2267435 5104961 := bstep (se 2 (by rfl) ⟨1914360, by rfl⟩ : syracuseStep 5104961 = 3828721) B3828721
theorem B3403307 : Blo 2267435 3403307 := bstep (se 1 (by rfl) ⟨2552480, by rfl⟩ : syracuseStep 3403307 = 5104961) B5104961
theorem B2268871 : Blo 2267435 2268871 := bstep (se 1 (by rfl) ⟨1701653, by rfl⟩ : syracuseStep 2268871 = 3403307) B3403307
theorem B2552485 : Blo 2267435 2552485 := bbase (se 4 (by rfl) ⟨239295, by rfl⟩ : syracuseStep 2552485 = 478591) (by norm_num)
theorem B3403313 : Blo 2267435 3403313 := bstep (se 2 (by rfl) ⟨1276242, by rfl⟩ : syracuseStep 3403313 = 2552485) B2552485
theorem B2268875 : Blo 2267435 2268875 := bstep (se 1 (by rfl) ⟨1701656, by rfl⟩ : syracuseStep 2268875 = 3403313) B3403313
theorem B3880973 : Blo 2267435 3880973 := bbase (se 3 (by rfl) ⟨727682, by rfl⟩ : syracuseStep 3880973 = 1455365) (by norm_num)
theorem B10349261 : Blo 2267435 10349261 := bstep (se 3 (by rfl) ⟨1940486, by rfl⟩ : syracuseStep 10349261 = 3880973) B3880973
theorem B6899507 : Blo 2267435 6899507 := bstep (se 1 (by rfl) ⟨5174630, by rfl⟩ : syracuseStep 6899507 = 10349261) B10349261
theorem B4599671 : Blo 2267435 4599671 := bstep (se 1 (by rfl) ⟨3449753, by rfl⟩ : syracuseStep 4599671 = 6899507) B6899507
theorem B49063157 : Blo 2267435 49063157 := bstep (se 5 (by rfl) ⟨2299835, by rfl⟩ : syracuseStep 49063157 = 4599671) B4599671
theorem B32708771 : Blo 2267435 32708771 := bstep (se 1 (by rfl) ⟨24531578, by rfl⟩ : syracuseStep 32708771 = 49063157) B49063157
theorem B21805847 : Blo 2267435 21805847 := bstep (se 1 (by rfl) ⟨16354385, by rfl⟩ : syracuseStep 21805847 = 32708771) B32708771
theorem B14537231 : Blo 2267435 14537231 := bstep (se 1 (by rfl) ⟨10902923, by rfl⟩ : syracuseStep 14537231 = 21805847) B21805847
theorem B9691487 : Blo 2267435 9691487 := bstep (se 1 (by rfl) ⟨7268615, by rfl⟩ : syracuseStep 9691487 = 14537231) B14537231
theorem B6460991 : Blo 2267435 6460991 := bstep (se 1 (by rfl) ⟨4845743, by rfl⟩ : syracuseStep 6460991 = 9691487) B9691487
theorem B4307327 : Blo 2267435 4307327 := bstep (se 1 (by rfl) ⟨3230495, by rfl⟩ : syracuseStep 4307327 = 6460991) B6460991
theorem B2871551 : Blo 2267435 2871551 := bstep (se 1 (by rfl) ⟨2153663, by rfl⟩ : syracuseStep 2871551 = 4307327) B4307327
theorem B7657469 : Blo 2267435 7657469 := bstep (se 3 (by rfl) ⟨1435775, by rfl⟩ : syracuseStep 7657469 = 2871551) B2871551
theorem B5104979 : Blo 2267435 5104979 := bstep (se 1 (by rfl) ⟨3828734, by rfl⟩ : syracuseStep 5104979 = 7657469) B7657469
theorem B3403319 : Blo 2267435 3403319 := bstep (se 1 (by rfl) ⟨2552489, by rfl⟩ : syracuseStep 3403319 = 5104979) B5104979
theorem B2268879 : Blo 2267435 2268879 := bstep (se 1 (by rfl) ⟨1701659, by rfl⟩ : syracuseStep 2268879 = 3403319) B3403319
theorem B3403325 : Blo 2267435 3403325 := bbase (se 3 (by rfl) ⟨638123, by rfl⟩ : syracuseStep 3403325 = 1276247) (by norm_num)
theorem B2268883 : Blo 2267435 2268883 := bstep (se 1 (by rfl) ⟨1701662, by rfl⟩ : syracuseStep 2268883 = 3403325) B3403325
theorem B5104997 : Blo 2267435 5104997 := bbase (se 4 (by rfl) ⟨478593, by rfl⟩ : syracuseStep 5104997 = 957187) (by norm_num)
theorem B3403331 : Blo 2267435 3403331 := bstep (se 1 (by rfl) ⟨2552498, by rfl⟩ : syracuseStep 3403331 = 5104997) B5104997
theorem B2268887 : Blo 2267435 2268887 := bstep (se 1 (by rfl) ⟨1701665, by rfl⟩ : syracuseStep 2268887 = 3403331) B3403331
theorem B5743133 : Blo 2267435 5743133 := bbase (se 3 (by rfl) ⟨1076837, by rfl⟩ : syracuseStep 5743133 = 2153675) (by norm_num)
theorem B3828755 : Blo 2267435 3828755 := bstep (se 1 (by rfl) ⟨2871566, by rfl⟩ : syracuseStep 3828755 = 5743133) B5743133
theorem B2552503 : Blo 2267435 2552503 := bstep (se 1 (by rfl) ⟨1914377, by rfl⟩ : syracuseStep 2552503 = 3828755) B3828755
theorem B3403337 : Blo 2267435 3403337 := bstep (se 2 (by rfl) ⟨1276251, by rfl⟩ : syracuseStep 3403337 = 2552503) B2552503
theorem B2268891 : Blo 2267435 2268891 := bstep (se 1 (by rfl) ⟨1701668, by rfl⟩ : syracuseStep 2268891 = 3403337) B3403337
theorem B4307357 : Blo 2267435 4307357 := bbase (se 3 (by rfl) ⟨807629, by rfl⟩ : syracuseStep 4307357 = 1615259) (by norm_num)
theorem B11486285 : Blo 2267435 11486285 := bstep (se 3 (by rfl) ⟨2153678, by rfl⟩ : syracuseStep 11486285 = 4307357) B4307357
theorem B7657523 : Blo 2267435 7657523 := bstep (se 1 (by rfl) ⟨5743142, by rfl⟩ : syracuseStep 7657523 = 11486285) B11486285
theorem B5105015 : Blo 2267435 5105015 := bstep (se 1 (by rfl) ⟨3828761, by rfl⟩ : syracuseStep 5105015 = 7657523) B7657523
theorem B3403343 : Blo 2267435 3403343 := bstep (se 1 (by rfl) ⟨2552507, by rfl⟩ : syracuseStep 3403343 = 5105015) B5105015
theorem B2268895 : Blo 2267435 2268895 := bstep (se 1 (by rfl) ⟨1701671, by rfl⟩ : syracuseStep 2268895 = 3403343) B3403343
theorem B3403349 : Blo 2267435 3403349 := bbase (se 8 (by rfl) ⟨19941, by rfl⟩ : syracuseStep 3403349 = 39883) (by norm_num)
theorem B2268899 : Blo 2267435 2268899 := bstep (se 1 (by rfl) ⟨1701674, by rfl⟩ : syracuseStep 2268899 = 3403349) B3403349
theorem B9691589 : Blo 2267435 9691589 := bbase (se 4 (by rfl) ⟨908586, by rfl⟩ : syracuseStep 9691589 = 1817173) (by norm_num)
theorem B6461059 : Blo 2267435 6461059 := bstep (se 1 (by rfl) ⟨4845794, by rfl⟩ : syracuseStep 6461059 = 9691589) B9691589
theorem B8614745 : Blo 2267435 8614745 := bstep (se 2 (by rfl) ⟨3230529, by rfl⟩ : syracuseStep 8614745 = 6461059) B6461059
theorem B5743163 : Blo 2267435 5743163 := bstep (se 1 (by rfl) ⟨4307372, by rfl⟩ : syracuseStep 5743163 = 8614745) B8614745
theorem B3828775 : Blo 2267435 3828775 := bstep (se 1 (by rfl) ⟨2871581, by rfl⟩ : syracuseStep 3828775 = 5743163) B5743163
theorem B5105033 : Blo 2267435 5105033 := bstep (se 2 (by rfl) ⟨1914387, by rfl⟩ : syracuseStep 5105033 = 3828775) B3828775
theorem B3403355 : Blo 2267435 3403355 := bstep (se 1 (by rfl) ⟨2552516, by rfl⟩ : syracuseStep 3403355 = 5105033) B5105033
theorem B2268903 : Blo 2267435 2268903 := bstep (se 1 (by rfl) ⟨1701677, by rfl⟩ : syracuseStep 2268903 = 3403355) B3403355
theorem B2552521 : Blo 2267435 2552521 := bbase (se 2 (by rfl) ⟨957195, by rfl⟩ : syracuseStep 2552521 = 1914391) (by norm_num)
theorem B3403361 : Blo 2267435 3403361 := bstep (se 2 (by rfl) ⟨1276260, by rfl⟩ : syracuseStep 3403361 = 2552521) B2552521
theorem B2268907 : Blo 2267435 2268907 := bstep (se 1 (by rfl) ⟨1701680, by rfl⟩ : syracuseStep 2268907 = 3403361) B3403361
theorem B2725769 : Blo 2267435 2725769 := bbase (se 2 (by rfl) ⟨1022163, by rfl⟩ : syracuseStep 2725769 = 2044327) (by norm_num)
theorem B7268717 : Blo 2267435 7268717 := bstep (se 3 (by rfl) ⟨1362884, by rfl⟩ : syracuseStep 7268717 = 2725769) B2725769
theorem B19383245 : Blo 2267435 19383245 := bstep (se 3 (by rfl) ⟨3634358, by rfl⟩ : syracuseStep 19383245 = 7268717) B7268717
theorem B12922163 : Blo 2267435 12922163 := bstep (se 1 (by rfl) ⟨9691622, by rfl⟩ : syracuseStep 12922163 = 19383245) B19383245
theorem B8614775 : Blo 2267435 8614775 := bstep (se 1 (by rfl) ⟨6461081, by rfl⟩ : syracuseStep 8614775 = 12922163) B12922163
theorem B5743183 : Blo 2267435 5743183 := bstep (se 1 (by rfl) ⟨4307387, by rfl⟩ : syracuseStep 5743183 = 8614775) B8614775
theorem B7657577 : Blo 2267435 7657577 := bstep (se 2 (by rfl) ⟨2871591, by rfl⟩ : syracuseStep 7657577 = 5743183) B5743183
theorem B5105051 : Blo 2267435 5105051 := bstep (se 1 (by rfl) ⟨3828788, by rfl⟩ : syracuseStep 5105051 = 7657577) B7657577
theorem B3403367 : Blo 2267435 3403367 := bstep (se 1 (by rfl) ⟨2552525, by rfl⟩ : syracuseStep 3403367 = 5105051) B5105051
theorem B2268911 : Blo 2267435 2268911 := bstep (se 1 (by rfl) ⟨1701683, by rfl⟩ : syracuseStep 2268911 = 3403367) B3403367
theorem B3403373 : Blo 2267435 3403373 := bbase (se 3 (by rfl) ⟨638132, by rfl⟩ : syracuseStep 3403373 = 1276265) (by norm_num)
theorem B2268915 : Blo 2267435 2268915 := bstep (se 1 (by rfl) ⟨1701686, by rfl⟩ : syracuseStep 2268915 = 3403373) B3403373
theorem B5105069 : Blo 2267435 5105069 := bbase (se 3 (by rfl) ⟨957200, by rfl⟩ : syracuseStep 5105069 = 1914401) (by norm_num)
theorem B3403379 : Blo 2267435 3403379 := bstep (se 1 (by rfl) ⟨2552534, by rfl⟩ : syracuseStep 3403379 = 5105069) B5105069
theorem B2268919 : Blo 2267435 2268919 := bstep (se 1 (by rfl) ⟨1701689, by rfl⟩ : syracuseStep 2268919 = 3403379) B3403379
theorem B4088677 : Blo 2267435 4088677 := bbase (se 4 (by rfl) ⟨383313, by rfl⟩ : syracuseStep 4088677 = 766627) (by norm_num)
theorem B5451569 : Blo 2267435 5451569 := bstep (se 2 (by rfl) ⟨2044338, by rfl⟩ : syracuseStep 5451569 = 4088677) B4088677
theorem B3634379 : Blo 2267435 3634379 := bstep (se 1 (by rfl) ⟨2725784, by rfl⟩ : syracuseStep 3634379 = 5451569) B5451569
theorem B2422919 : Blo 2267435 2422919 := bstep (se 1 (by rfl) ⟨1817189, by rfl⟩ : syracuseStep 2422919 = 3634379) B3634379
theorem B6461117 : Blo 2267435 6461117 := bstep (se 3 (by rfl) ⟨1211459, by rfl⟩ : syracuseStep 6461117 = 2422919) B2422919
theorem B4307411 : Blo 2267435 4307411 := bstep (se 1 (by rfl) ⟨3230558, by rfl⟩ : syracuseStep 4307411 = 6461117) B6461117
theorem B2871607 : Blo 2267435 2871607 := bstep (se 1 (by rfl) ⟨2153705, by rfl⟩ : syracuseStep 2871607 = 4307411) B4307411
theorem B3828809 : Blo 2267435 3828809 := bstep (se 2 (by rfl) ⟨1435803, by rfl⟩ : syracuseStep 3828809 = 2871607) B2871607
theorem B2552539 : Blo 2267435 2552539 := bstep (se 1 (by rfl) ⟨1914404, by rfl⟩ : syracuseStep 2552539 = 3828809) B3828809
theorem B3403385 : Blo 2267435 3403385 := bstep (se 2 (by rfl) ⟨1276269, by rfl⟩ : syracuseStep 3403385 = 2552539) B2552539
theorem B2268923 : Blo 2267435 2268923 := bstep (se 1 (by rfl) ⟨1701692, by rfl⟩ : syracuseStep 2268923 = 3403385) B3403385
theorem B6729205 : Blo 2267435 6729205 := bbase (se 5 (by rfl) ⟨315431, by rfl⟩ : syracuseStep 6729205 = 630863) (by norm_num)
theorem B8972273 : Blo 2267435 8972273 := bstep (se 2 (by rfl) ⟨3364602, by rfl⟩ : syracuseStep 8972273 = 6729205) B6729205
theorem B5981515 : Blo 2267435 5981515 := bstep (se 1 (by rfl) ⟨4486136, by rfl⟩ : syracuseStep 5981515 = 8972273) B8972273
theorem B31901413 : Blo 2267435 31901413 := bstep (se 4 (by rfl) ⟨2990757, by rfl⟩ : syracuseStep 31901413 = 5981515) B5981515
theorem B42535217 : Blo 2267435 42535217 := bstep (se 2 (by rfl) ⟨15950706, by rfl⟩ : syracuseStep 42535217 = 31901413) B31901413
theorem B28356811 : Blo 2267435 28356811 := bstep (se 1 (by rfl) ⟨21267608, by rfl⟩ : syracuseStep 28356811 = 42535217) B42535217
theorem B151236325 : Blo 2267435 151236325 := bstep (se 4 (by rfl) ⟨14178405, by rfl⟩ : syracuseStep 151236325 = 28356811) B28356811
theorem B201648433 : Blo 2267435 201648433 := bstep (se 2 (by rfl) ⟨75618162, by rfl⟩ : syracuseStep 201648433 = 151236325) B151236325
theorem B17207332949 : Blo 2267435 17207332949 := bstep (se 8 (by rfl) ⟨100824216, by rfl⟩ : syracuseStep 17207332949 = 201648433) B201648433
theorem B11471555299 : Blo 2267435 11471555299 := bstep (se 1 (by rfl) ⟨8603666474, by rfl⟩ : syracuseStep 11471555299 = 17207332949) B17207332949
theorem B15295407065 : Blo 2267435 15295407065 := bstep (se 2 (by rfl) ⟨5735777649, by rfl⟩ : syracuseStep 15295407065 = 11471555299) B11471555299
theorem B10196938043 : Blo 2267435 10196938043 := bstep (se 1 (by rfl) ⟨7647703532, by rfl⟩ : syracuseStep 10196938043 = 15295407065) B15295407065
theorem B6797958695 : Blo 2267435 6797958695 := bstep (se 1 (by rfl) ⟨5098469021, by rfl⟩ : syracuseStep 6797958695 = 10196938043) B10196938043
theorem B4531972463 : Blo 2267435 4531972463 := bstep (se 1 (by rfl) ⟨3398979347, by rfl⟩ : syracuseStep 4531972463 = 6797958695) B6797958695
theorem B3021314975 : Blo 2267435 3021314975 := bstep (se 1 (by rfl) ⟨2265986231, by rfl⟩ : syracuseStep 3021314975 = 4531972463) B4531972463
theorem B2014209983 : Blo 2267435 2014209983 := bstep (se 1 (by rfl) ⟨1510657487, by rfl⟩ : syracuseStep 2014209983 = 3021314975) B3021314975
theorem B1342806655 : Blo 2267435 1342806655 := bstep (se 1 (by rfl) ⟨1007104991, by rfl⟩ : syracuseStep 1342806655 = 2014209983) B2014209983
theorem B1790408873 : Blo 2267435 1790408873 := bstep (se 2 (by rfl) ⟨671403327, by rfl⟩ : syracuseStep 1790408873 = 1342806655) B1342806655
theorem B4774423661 : Blo 2267435 4774423661 := bstep (se 3 (by rfl) ⟨895204436, by rfl⟩ : syracuseStep 4774423661 = 1790408873) B1790408873
theorem B3182949107 : Blo 2267435 3182949107 := bstep (se 1 (by rfl) ⟨2387211830, by rfl⟩ : syracuseStep 3182949107 = 4774423661) B4774423661
theorem B2121966071 : Blo 2267435 2121966071 := bstep (se 1 (by rfl) ⟨1591474553, by rfl⟩ : syracuseStep 2121966071 = 3182949107) B3182949107
theorem B1414644047 : Blo 2267435 1414644047 := bstep (se 1 (by rfl) ⟨1060983035, by rfl⟩ : syracuseStep 1414644047 = 2121966071) B2121966071
theorem B943096031 : Blo 2267435 943096031 := bstep (se 1 (by rfl) ⟨707322023, by rfl⟩ : syracuseStep 943096031 = 1414644047) B1414644047
theorem B628730687 : Blo 2267435 628730687 := bstep (se 1 (by rfl) ⟨471548015, by rfl⟩ : syracuseStep 628730687 = 943096031) B943096031
theorem B419153791 : Blo 2267435 419153791 := bstep (se 1 (by rfl) ⟨314365343, by rfl⟩ : syracuseStep 419153791 = 628730687) B628730687
theorem B558871721 : Blo 2267435 558871721 := bstep (se 2 (by rfl) ⟨209576895, by rfl⟩ : syracuseStep 558871721 = 419153791) B419153791
theorem B372581147 : Blo 2267435 372581147 := bstep (se 1 (by rfl) ⟨279435860, by rfl⟩ : syracuseStep 372581147 = 558871721) B558871721
theorem B248387431 : Blo 2267435 248387431 := bstep (se 1 (by rfl) ⟨186290573, by rfl⟩ : syracuseStep 248387431 = 372581147) B372581147
theorem B331183241 : Blo 2267435 331183241 := bstep (se 2 (by rfl) ⟨124193715, by rfl⟩ : syracuseStep 331183241 = 248387431) B248387431
theorem B220788827 : Blo 2267435 220788827 := bstep (se 1 (by rfl) ⟨165591620, by rfl⟩ : syracuseStep 220788827 = 331183241) B331183241
theorem B147192551 : Blo 2267435 147192551 := bstep (se 1 (by rfl) ⟨110394413, by rfl⟩ : syracuseStep 147192551 = 220788827) B220788827
theorem B98128367 : Blo 2267435 98128367 := bstep (se 1 (by rfl) ⟨73596275, by rfl⟩ : syracuseStep 98128367 = 147192551) B147192551
theorem B65418911 : Blo 2267435 65418911 := bstep (se 1 (by rfl) ⟨49064183, by rfl⟩ : syracuseStep 65418911 = 98128367) B98128367
theorem B43612607 : Blo 2267435 43612607 := bstep (se 1 (by rfl) ⟨32709455, by rfl⟩ : syracuseStep 43612607 = 65418911) B65418911
theorem B29075071 : Blo 2267435 29075071 := bstep (se 1 (by rfl) ⟨21806303, by rfl⟩ : syracuseStep 29075071 = 43612607) B43612607
theorem B38766761 : Blo 2267435 38766761 := bstep (se 2 (by rfl) ⟨14537535, by rfl⟩ : syracuseStep 38766761 = 29075071) B29075071
theorem B25844507 : Blo 2267435 25844507 := bstep (se 1 (by rfl) ⟨19383380, by rfl⟩ : syracuseStep 25844507 = 38766761) B38766761
theorem B17229671 : Blo 2267435 17229671 := bstep (se 1 (by rfl) ⟨12922253, by rfl⟩ : syracuseStep 17229671 = 25844507) B25844507
theorem B11486447 : Blo 2267435 11486447 := bstep (se 1 (by rfl) ⟨8614835, by rfl⟩ : syracuseStep 11486447 = 17229671) B17229671
theorem B7657631 : Blo 2267435 7657631 := bstep (se 1 (by rfl) ⟨5743223, by rfl⟩ : syracuseStep 7657631 = 11486447) B11486447
theorem B5105087 : Blo 2267435 5105087 := bstep (se 1 (by rfl) ⟨3828815, by rfl⟩ : syracuseStep 5105087 = 7657631) B7657631
theorem B3403391 : Blo 2267435 3403391 := bstep (se 1 (by rfl) ⟨2552543, by rfl⟩ : syracuseStep 3403391 = 5105087) B5105087
theorem B2268927 : Blo 2267435 2268927 := bstep (se 1 (by rfl) ⟨1701695, by rfl⟩ : syracuseStep 2268927 = 3403391) B3403391
theorem B3403397 : Blo 2267435 3403397 := bbase (se 4 (by rfl) ⟨319068, by rfl⟩ : syracuseStep 3403397 = 638137) (by norm_num)
theorem B2268931 : Blo 2267435 2268931 := bstep (se 1 (by rfl) ⟨1701698, by rfl⟩ : syracuseStep 2268931 = 3403397) B3403397
theorem B3828829 : Blo 2267435 3828829 := bbase (se 3 (by rfl) ⟨717905, by rfl⟩ : syracuseStep 3828829 = 1435811) (by norm_num)
theorem B5105105 : Blo 2267435 5105105 := bstep (se 2 (by rfl) ⟨1914414, by rfl⟩ : syracuseStep 5105105 = 3828829) B3828829
theorem B3403403 : Blo 2267435 3403403 := bstep (se 1 (by rfl) ⟨2552552, by rfl⟩ : syracuseStep 3403403 = 5105105) B5105105
theorem B2268935 : Blo 2267435 2268935 := bstep (se 1 (by rfl) ⟨1701701, by rfl⟩ : syracuseStep 2268935 = 3403403) B3403403
theorem B2552557 : Blo 2267435 2552557 := bbase (se 3 (by rfl) ⟨478604, by rfl⟩ : syracuseStep 2552557 = 957209) (by norm_num)
theorem B3403409 : Blo 2267435 3403409 := bstep (se 2 (by rfl) ⟨1276278, by rfl⟩ : syracuseStep 3403409 = 2552557) B2552557
theorem B2268939 : Blo 2267435 2268939 := bstep (se 1 (by rfl) ⟨1701704, by rfl⟩ : syracuseStep 2268939 = 3403409) B3403409
theorem B7657685 : Blo 2267435 7657685 := bbase (se 7 (by rfl) ⟨89738, by rfl⟩ : syracuseStep 7657685 = 179477) (by norm_num)
theorem B5105123 : Blo 2267435 5105123 := bstep (se 1 (by rfl) ⟨3828842, by rfl⟩ : syracuseStep 5105123 = 7657685) B7657685
theorem B3403415 : Blo 2267435 3403415 := bstep (se 1 (by rfl) ⟨2552561, by rfl⟩ : syracuseStep 3403415 = 5105123) B5105123
theorem B2268943 : Blo 2267435 2268943 := bstep (se 1 (by rfl) ⟨1701707, by rfl⟩ : syracuseStep 2268943 = 3403415) B3403415
theorem B3403421 : Blo 2267435 3403421 := bbase (se 3 (by rfl) ⟨638141, by rfl⟩ : syracuseStep 3403421 = 1276283) (by norm_num)
theorem B2268947 : Blo 2267435 2268947 := bstep (se 1 (by rfl) ⟨1701710, by rfl⟩ : syracuseStep 2268947 = 3403421) B3403421
theorem B5105141 : Blo 2267435 5105141 := bbase (se 5 (by rfl) ⟨239303, by rfl⟩ : syracuseStep 5105141 = 478607) (by norm_num)
theorem B3403427 : Blo 2267435 3403427 := bstep (se 1 (by rfl) ⟨2552570, by rfl⟩ : syracuseStep 3403427 = 5105141) B5105141
theorem B2268951 : Blo 2267435 2268951 := bstep (se 1 (by rfl) ⟨1701713, by rfl⟩ : syracuseStep 2268951 = 3403427) B3403427
theorem B5994101 : Blo 2267435 5994101 := bbase (se 5 (by rfl) ⟨280973, by rfl⟩ : syracuseStep 5994101 = 561947) (by norm_num)
theorem B3996067 : Blo 2267435 3996067 := bstep (se 1 (by rfl) ⟨2997050, by rfl⟩ : syracuseStep 3996067 = 5994101) B5994101
theorem B5328089 : Blo 2267435 5328089 := bstep (se 2 (by rfl) ⟨1998033, by rfl⟩ : syracuseStep 5328089 = 3996067) B3996067
theorem B3552059 : Blo 2267435 3552059 := bstep (se 1 (by rfl) ⟨2664044, by rfl⟩ : syracuseStep 3552059 = 5328089) B5328089
theorem B9472157 : Blo 2267435 9472157 := bstep (se 3 (by rfl) ⟨1776029, by rfl⟩ : syracuseStep 9472157 = 3552059) B3552059
theorem B6314771 : Blo 2267435 6314771 := bstep (se 1 (by rfl) ⟨4736078, by rfl⟩ : syracuseStep 6314771 = 9472157) B9472157
theorem B4209847 : Blo 2267435 4209847 := bstep (se 1 (by rfl) ⟨3157385, by rfl⟩ : syracuseStep 4209847 = 6314771) B6314771
theorem B22452517 : Blo 2267435 22452517 := bstep (se 4 (by rfl) ⟨2104923, by rfl⟩ : syracuseStep 22452517 = 4209847) B4209847
theorem B119746757 : Blo 2267435 119746757 := bstep (se 4 (by rfl) ⟨11226258, by rfl⟩ : syracuseStep 119746757 = 22452517) B22452517
theorem B79831171 : Blo 2267435 79831171 := bstep (se 1 (by rfl) ⟨59873378, by rfl⟩ : syracuseStep 79831171 = 119746757) B119746757
theorem B106441561 : Blo 2267435 106441561 := bstep (se 2 (by rfl) ⟨39915585, by rfl⟩ : syracuseStep 106441561 = 79831171) B79831171
theorem B141922081 : Blo 2267435 141922081 := bstep (se 2 (by rfl) ⟨53220780, by rfl⟩ : syracuseStep 141922081 = 106441561) B106441561
theorem B189229441 : Blo 2267435 189229441 := bstep (se 2 (by rfl) ⟨70961040, by rfl⟩ : syracuseStep 189229441 = 141922081) B141922081
theorem B252305921 : Blo 2267435 252305921 := bstep (se 2 (by rfl) ⟨94614720, by rfl⟩ : syracuseStep 252305921 = 189229441) B189229441
theorem B168203947 : Blo 2267435 168203947 := bstep (se 1 (by rfl) ⟨126152960, by rfl⟩ : syracuseStep 168203947 = 252305921) B252305921
theorem B224271929 : Blo 2267435 224271929 := bstep (se 2 (by rfl) ⟨84101973, by rfl⟩ : syracuseStep 224271929 = 168203947) B168203947
theorem B149514619 : Blo 2267435 149514619 := bstep (se 1 (by rfl) ⟨112135964, by rfl⟩ : syracuseStep 149514619 = 224271929) B224271929
theorem B199352825 : Blo 2267435 199352825 := bstep (se 2 (by rfl) ⟨74757309, by rfl⟩ : syracuseStep 199352825 = 149514619) B149514619
theorem B132901883 : Blo 2267435 132901883 := bstep (se 1 (by rfl) ⟨99676412, by rfl⟩ : syracuseStep 132901883 = 199352825) B199352825
theorem B88601255 : Blo 2267435 88601255 := bstep (se 1 (by rfl) ⟨66450941, by rfl⟩ : syracuseStep 88601255 = 132901883) B132901883
theorem B59067503 : Blo 2267435 59067503 := bstep (se 1 (by rfl) ⟨44300627, by rfl⟩ : syracuseStep 59067503 = 88601255) B88601255
theorem B39378335 : Blo 2267435 39378335 := bstep (se 1 (by rfl) ⟨29533751, by rfl⟩ : syracuseStep 39378335 = 59067503) B59067503
theorem B420035573 : Blo 2267435 420035573 := bstep (se 5 (by rfl) ⟨19689167, by rfl⟩ : syracuseStep 420035573 = 39378335) B39378335
theorem B280023715 : Blo 2267435 280023715 := bstep (se 1 (by rfl) ⟨210017786, by rfl⟩ : syracuseStep 280023715 = 420035573) B420035573
theorem B373364953 : Blo 2267435 373364953 := bstep (se 2 (by rfl) ⟨140011857, by rfl⟩ : syracuseStep 373364953 = 280023715) B280023715
theorem B1991279749 : Blo 2267435 1991279749 := bstep (se 4 (by rfl) ⟨186682476, by rfl⟩ : syracuseStep 1991279749 = 373364953) B373364953
theorem B2655039665 : Blo 2267435 2655039665 := bstep (se 2 (by rfl) ⟨995639874, by rfl⟩ : syracuseStep 2655039665 = 1991279749) B1991279749
theorem B7080105773 : Blo 2267435 7080105773 := bstep (se 3 (by rfl) ⟨1327519832, by rfl⟩ : syracuseStep 7080105773 = 2655039665) B2655039665
theorem B4720070515 : Blo 2267435 4720070515 := bstep (se 1 (by rfl) ⟨3540052886, by rfl⟩ : syracuseStep 4720070515 = 7080105773) B7080105773
theorem B6293427353 : Blo 2267435 6293427353 := bstep (se 2 (by rfl) ⟨2360035257, by rfl⟩ : syracuseStep 6293427353 = 4720070515) B4720070515
theorem B4195618235 : Blo 2267435 4195618235 := bstep (se 1 (by rfl) ⟨3146713676, by rfl⟩ : syracuseStep 4195618235 = 6293427353) B6293427353
theorem B2797078823 : Blo 2267435 2797078823 := bstep (se 1 (by rfl) ⟨2097809117, by rfl⟩ : syracuseStep 2797078823 = 4195618235) B4195618235
theorem B1864719215 : Blo 2267435 1864719215 := bstep (se 1 (by rfl) ⟨1398539411, by rfl⟩ : syracuseStep 1864719215 = 2797078823) B2797078823
theorem B1243146143 : Blo 2267435 1243146143 := bstep (se 1 (by rfl) ⟨932359607, by rfl⟩ : syracuseStep 1243146143 = 1864719215) B1864719215
theorem B828764095 : Blo 2267435 828764095 := bstep (se 1 (by rfl) ⟨621573071, by rfl⟩ : syracuseStep 828764095 = 1243146143) B1243146143
theorem B1105018793 : Blo 2267435 1105018793 := bstep (se 2 (by rfl) ⟨414382047, by rfl⟩ : syracuseStep 1105018793 = 828764095) B828764095
theorem B736679195 : Blo 2267435 736679195 := bstep (se 1 (by rfl) ⟨552509396, by rfl⟩ : syracuseStep 736679195 = 1105018793) B1105018793
theorem B491119463 : Blo 2267435 491119463 := bstep (se 1 (by rfl) ⟨368339597, by rfl⟩ : syracuseStep 491119463 = 736679195) B736679195
theorem B327412975 : Blo 2267435 327412975 := bstep (se 1 (by rfl) ⟨245559731, by rfl⟩ : syracuseStep 327412975 = 491119463) B491119463
theorem B436550633 : Blo 2267435 436550633 := bstep (se 2 (by rfl) ⟨163706487, by rfl⟩ : syracuseStep 436550633 = 327412975) B327412975
theorem B291033755 : Blo 2267435 291033755 := bstep (se 1 (by rfl) ⟨218275316, by rfl⟩ : syracuseStep 291033755 = 436550633) B436550633
theorem B194022503 : Blo 2267435 194022503 := bstep (se 1 (by rfl) ⟨145516877, by rfl⟩ : syracuseStep 194022503 = 291033755) B291033755
theorem B129348335 : Blo 2267435 129348335 := bstep (se 1 (by rfl) ⟨97011251, by rfl⟩ : syracuseStep 129348335 = 194022503) B194022503
theorem B86232223 : Blo 2267435 86232223 := bstep (se 1 (by rfl) ⟨64674167, by rfl⟩ : syracuseStep 86232223 = 129348335) B129348335
theorem B114976297 : Blo 2267435 114976297 := bstep (se 2 (by rfl) ⟨43116111, by rfl⟩ : syracuseStep 114976297 = 86232223) B86232223
theorem B153301729 : Blo 2267435 153301729 := bstep (se 2 (by rfl) ⟨57488148, by rfl⟩ : syracuseStep 153301729 = 114976297) B114976297
theorem B204402305 : Blo 2267435 204402305 := bstep (se 2 (by rfl) ⟨76650864, by rfl⟩ : syracuseStep 204402305 = 153301729) B153301729
theorem B545072813 : Blo 2267435 545072813 := bstep (se 3 (by rfl) ⟨102201152, by rfl⟩ : syracuseStep 545072813 = 204402305) B204402305
theorem B363381875 : Blo 2267435 363381875 := bstep (se 1 (by rfl) ⟨272536406, by rfl⟩ : syracuseStep 363381875 = 545072813) B545072813
theorem B242254583 : Blo 2267435 242254583 := bstep (se 1 (by rfl) ⟨181690937, by rfl⟩ : syracuseStep 242254583 = 363381875) B363381875
theorem B161503055 : Blo 2267435 161503055 := bstep (se 1 (by rfl) ⟨121127291, by rfl⟩ : syracuseStep 161503055 = 242254583) B242254583
theorem B107668703 : Blo 2267435 107668703 := bstep (se 1 (by rfl) ⟨80751527, by rfl⟩ : syracuseStep 107668703 = 161503055) B161503055
theorem B71779135 : Blo 2267435 71779135 := bstep (se 1 (by rfl) ⟨53834351, by rfl⟩ : syracuseStep 71779135 = 107668703) B107668703
theorem B95705513 : Blo 2267435 95705513 := bstep (se 2 (by rfl) ⟨35889567, by rfl⟩ : syracuseStep 95705513 = 71779135) B71779135
theorem B63803675 : Blo 2267435 63803675 := bstep (se 1 (by rfl) ⟨47852756, by rfl⟩ : syracuseStep 63803675 = 95705513) B95705513
theorem B42535783 : Blo 2267435 42535783 := bstep (se 1 (by rfl) ⟨31901837, by rfl⟩ : syracuseStep 42535783 = 63803675) B63803675
theorem B56714377 : Blo 2267435 56714377 := bstep (se 2 (by rfl) ⟨21267891, by rfl⟩ : syracuseStep 56714377 = 42535783) B42535783
theorem B75619169 : Blo 2267435 75619169 := bstep (se 2 (by rfl) ⟨28357188, by rfl⟩ : syracuseStep 75619169 = 56714377) B56714377
theorem B50412779 : Blo 2267435 50412779 := bstep (se 1 (by rfl) ⟨37809584, by rfl⟩ : syracuseStep 50412779 = 75619169) B75619169
theorem B33608519 : Blo 2267435 33608519 := bstep (se 1 (by rfl) ⟨25206389, by rfl⟩ : syracuseStep 33608519 = 50412779) B50412779
theorem B22405679 : Blo 2267435 22405679 := bstep (se 1 (by rfl) ⟨16804259, by rfl⟩ : syracuseStep 22405679 = 33608519) B33608519
theorem B14937119 : Blo 2267435 14937119 := bstep (se 1 (by rfl) ⟨11202839, by rfl⟩ : syracuseStep 14937119 = 22405679) B22405679
theorem B9958079 : Blo 2267435 9958079 := bstep (se 1 (by rfl) ⟨7468559, by rfl⟩ : syracuseStep 9958079 = 14937119) B14937119
theorem B6638719 : Blo 2267435 6638719 := bstep (se 1 (by rfl) ⟨4979039, by rfl⟩ : syracuseStep 6638719 = 9958079) B9958079
theorem B8851625 : Blo 2267435 8851625 := bstep (se 2 (by rfl) ⟨3319359, by rfl⟩ : syracuseStep 8851625 = 6638719) B6638719
theorem B5901083 : Blo 2267435 5901083 := bstep (se 1 (by rfl) ⟨4425812, by rfl⟩ : syracuseStep 5901083 = 8851625) B8851625
theorem B3934055 : Blo 2267435 3934055 := bstep (se 1 (by rfl) ⟨2950541, by rfl⟩ : syracuseStep 3934055 = 5901083) B5901083
theorem B2622703 : Blo 2267435 2622703 := bstep (se 1 (by rfl) ⟨1967027, by rfl⟩ : syracuseStep 2622703 = 3934055) B3934055
theorem B3496937 : Blo 2267435 3496937 := bstep (se 2 (by rfl) ⟨1311351, by rfl⟩ : syracuseStep 3496937 = 2622703) B2622703
theorem B37300661 : Blo 2267435 37300661 := bstep (se 5 (by rfl) ⟨1748468, by rfl⟩ : syracuseStep 37300661 = 3496937) B3496937
theorem B24867107 : Blo 2267435 24867107 := bstep (se 1 (by rfl) ⟨18650330, by rfl⟩ : syracuseStep 24867107 = 37300661) B37300661
theorem B16578071 : Blo 2267435 16578071 := bstep (se 1 (by rfl) ⟨12433553, by rfl⟩ : syracuseStep 16578071 = 24867107) B24867107
theorem B11052047 : Blo 2267435 11052047 := bstep (se 1 (by rfl) ⟨8289035, by rfl⟩ : syracuseStep 11052047 = 16578071) B16578071
theorem B7368031 : Blo 2267435 7368031 := bstep (se 1 (by rfl) ⟨5526023, by rfl⟩ : syracuseStep 7368031 = 11052047) B11052047
theorem B9824041 : Blo 2267435 9824041 := bstep (se 2 (by rfl) ⟨3684015, by rfl⟩ : syracuseStep 9824041 = 7368031) B7368031
theorem B13098721 : Blo 2267435 13098721 := bstep (se 2 (by rfl) ⟨4912020, by rfl⟩ : syracuseStep 13098721 = 9824041) B9824041
theorem B17464961 : Blo 2267435 17464961 := bstep (se 2 (by rfl) ⟨6549360, by rfl⟩ : syracuseStep 17464961 = 13098721) B13098721
theorem B11643307 : Blo 2267435 11643307 := bstep (se 1 (by rfl) ⟨8732480, by rfl⟩ : syracuseStep 11643307 = 17464961) B17464961
theorem B62097637 : Blo 2267435 62097637 := bstep (se 4 (by rfl) ⟨5821653, by rfl⟩ : syracuseStep 62097637 = 11643307) B11643307
theorem B82796849 : Blo 2267435 82796849 := bstep (se 2 (by rfl) ⟨31048818, by rfl⟩ : syracuseStep 82796849 = 62097637) B62097637
theorem B55197899 : Blo 2267435 55197899 := bstep (se 1 (by rfl) ⟨41398424, by rfl⟩ : syracuseStep 55197899 = 82796849) B82796849
theorem B36798599 : Blo 2267435 36798599 := bstep (se 1 (by rfl) ⟨27598949, by rfl⟩ : syracuseStep 36798599 = 55197899) B55197899
theorem B24532399 : Blo 2267435 24532399 := bstep (se 1 (by rfl) ⟨18399299, by rfl⟩ : syracuseStep 24532399 = 36798599) B36798599
theorem B32709865 : Blo 2267435 32709865 := bstep (se 2 (by rfl) ⟨12266199, by rfl⟩ : syracuseStep 32709865 = 24532399) B24532399
theorem B43613153 : Blo 2267435 43613153 := bstep (se 2 (by rfl) ⟨16354932, by rfl⟩ : syracuseStep 43613153 = 32709865) B32709865
theorem B29075435 : Blo 2267435 29075435 := bstep (se 1 (by rfl) ⟨21806576, by rfl⟩ : syracuseStep 29075435 = 43613153) B43613153
theorem B19383623 : Blo 2267435 19383623 := bstep (se 1 (by rfl) ⟨14537717, by rfl⟩ : syracuseStep 19383623 = 29075435) B29075435
theorem B12922415 : Blo 2267435 12922415 := bstep (se 1 (by rfl) ⟨9691811, by rfl⟩ : syracuseStep 12922415 = 19383623) B19383623
theorem B8614943 : Blo 2267435 8614943 := bstep (se 1 (by rfl) ⟨6461207, by rfl⟩ : syracuseStep 8614943 = 12922415) B12922415
theorem B5743295 : Blo 2267435 5743295 := bstep (se 1 (by rfl) ⟨4307471, by rfl⟩ : syracuseStep 5743295 = 8614943) B8614943
theorem B3828863 : Blo 2267435 3828863 := bstep (se 1 (by rfl) ⟨2871647, by rfl⟩ : syracuseStep 3828863 = 5743295) B5743295
theorem B2552575 : Blo 2267435 2552575 := bstep (se 1 (by rfl) ⟨1914431, by rfl⟩ : syracuseStep 2552575 = 3828863) B3828863
theorem B3403433 : Blo 2267435 3403433 := bstep (se 2 (by rfl) ⟨1276287, by rfl⟩ : syracuseStep 3403433 = 2552575) B2552575
theorem B2268955 : Blo 2267435 2268955 := bstep (se 1 (by rfl) ⟨1701716, by rfl⟩ : syracuseStep 2268955 = 3403433) B3403433
theorem B2422957 : Blo 2267435 2422957 := bbase (se 3 (by rfl) ⟨454304, by rfl⟩ : syracuseStep 2422957 = 908609) (by norm_num)
theorem B3230609 : Blo 2267435 3230609 := bstep (se 2 (by rfl) ⟨1211478, by rfl⟩ : syracuseStep 3230609 = 2422957) B2422957
theorem B8614957 : Blo 2267435 8614957 := bstep (se 3 (by rfl) ⟨1615304, by rfl⟩ : syracuseStep 8614957 = 3230609) B3230609
theorem B11486609 : Blo 2267435 11486609 := bstep (se 2 (by rfl) ⟨4307478, by rfl⟩ : syracuseStep 11486609 = 8614957) B8614957
theorem B7657739 : Blo 2267435 7657739 := bstep (se 1 (by rfl) ⟨5743304, by rfl⟩ : syracuseStep 7657739 = 11486609) B11486609
theorem B5105159 : Blo 2267435 5105159 := bstep (se 1 (by rfl) ⟨3828869, by rfl⟩ : syracuseStep 5105159 = 7657739) B7657739
theorem B3403439 : Blo 2267435 3403439 := bstep (se 1 (by rfl) ⟨2552579, by rfl⟩ : syracuseStep 3403439 = 5105159) B5105159
theorem B2268959 : Blo 2267435 2268959 := bstep (se 1 (by rfl) ⟨1701719, by rfl⟩ : syracuseStep 2268959 = 3403439) B3403439
theorem B3403445 : Blo 2267435 3403445 := bbase (se 5 (by rfl) ⟨159536, by rfl⟩ : syracuseStep 3403445 = 319073) (by norm_num)
theorem B2268963 : Blo 2267435 2268963 := bstep (se 1 (by rfl) ⟨1701722, by rfl⟩ : syracuseStep 2268963 = 3403445) B3403445
theorem B5743325 : Blo 2267435 5743325 := bbase (se 3 (by rfl) ⟨1076873, by rfl⟩ : syracuseStep 5743325 = 2153747) (by norm_num)
theorem B3828883 : Blo 2267435 3828883 := bstep (se 1 (by rfl) ⟨2871662, by rfl⟩ : syracuseStep 3828883 = 5743325) B5743325
theorem B5105177 : Blo 2267435 5105177 := bstep (se 2 (by rfl) ⟨1914441, by rfl⟩ : syracuseStep 5105177 = 3828883) B3828883
theorem B3403451 : Blo 2267435 3403451 := bstep (se 1 (by rfl) ⟨2552588, by rfl⟩ : syracuseStep 3403451 = 5105177) B5105177
theorem B2268967 : Blo 2267435 2268967 := bstep (se 1 (by rfl) ⟨1701725, by rfl⟩ : syracuseStep 2268967 = 3403451) B3403451
theorem B2552593 : Blo 2267435 2552593 := bbase (se 2 (by rfl) ⟨957222, by rfl⟩ : syracuseStep 2552593 = 1914445) (by norm_num)
theorem B3403457 : Blo 2267435 3403457 := bstep (se 2 (by rfl) ⟨1276296, by rfl⟩ : syracuseStep 3403457 = 2552593) B2552593
theorem B2268971 : Blo 2267435 2268971 := bstep (se 1 (by rfl) ⟨1701728, by rfl⟩ : syracuseStep 2268971 = 3403457) B3403457
theorem B4307509 : Blo 2267435 4307509 := bbase (se 5 (by rfl) ⟨201914, by rfl⟩ : syracuseStep 4307509 = 403829) (by norm_num)
theorem B5743345 : Blo 2267435 5743345 := bstep (se 2 (by rfl) ⟨2153754, by rfl⟩ : syracuseStep 5743345 = 4307509) B4307509
theorem B7657793 : Blo 2267435 7657793 := bstep (se 2 (by rfl) ⟨2871672, by rfl⟩ : syracuseStep 7657793 = 5743345) B5743345
theorem B5105195 : Blo 2267435 5105195 := bstep (se 1 (by rfl) ⟨3828896, by rfl⟩ : syracuseStep 5105195 = 7657793) B7657793
theorem B3403463 : Blo 2267435 3403463 := bstep (se 1 (by rfl) ⟨2552597, by rfl⟩ : syracuseStep 3403463 = 5105195) B5105195
theorem B2268975 : Blo 2267435 2268975 := bstep (se 1 (by rfl) ⟨1701731, by rfl⟩ : syracuseStep 2268975 = 3403463) B3403463
theorem B3403469 : Blo 2267435 3403469 := bbase (se 3 (by rfl) ⟨638150, by rfl⟩ : syracuseStep 3403469 = 1276301) (by norm_num)
theorem B2268979 : Blo 2267435 2268979 := bstep (se 1 (by rfl) ⟨1701734, by rfl⟩ : syracuseStep 2268979 = 3403469) B3403469
theorem B5105213 : Blo 2267435 5105213 := bbase (se 3 (by rfl) ⟨957227, by rfl⟩ : syracuseStep 5105213 = 1914455) (by norm_num)
theorem B3403475 : Blo 2267435 3403475 := bstep (se 1 (by rfl) ⟨2552606, by rfl⟩ : syracuseStep 3403475 = 5105213) B5105213
theorem B2268983 : Blo 2267435 2268983 := bstep (se 1 (by rfl) ⟨1701737, by rfl⟩ : syracuseStep 2268983 = 3403475) B3403475
theorem B3828917 : Blo 2267435 3828917 := bbase (se 5 (by rfl) ⟨179480, by rfl⟩ : syracuseStep 3828917 = 358961) (by norm_num)
theorem B2552611 : Blo 2267435 2552611 := bstep (se 1 (by rfl) ⟨1914458, by rfl⟩ : syracuseStep 2552611 = 3828917) B3828917
theorem B3403481 : Blo 2267435 3403481 := bstep (se 2 (by rfl) ⟨1276305, by rfl⟩ : syracuseStep 3403481 = 2552611) B2552611
theorem B2268987 : Blo 2267435 2268987 := bstep (se 1 (by rfl) ⟨1701740, by rfl⟩ : syracuseStep 2268987 = 3403481) B3403481
theorem B6993989 : Blo 2267435 6993989 := bbase (se 4 (by rfl) ⟨655686, by rfl⟩ : syracuseStep 6993989 = 1311373) (by norm_num)
theorem B4662659 : Blo 2267435 4662659 := bstep (se 1 (by rfl) ⟨3496994, by rfl⟩ : syracuseStep 4662659 = 6993989) B6993989
theorem B3108439 : Blo 2267435 3108439 := bstep (se 1 (by rfl) ⟨2331329, by rfl⟩ : syracuseStep 3108439 = 4662659) B4662659
theorem B16578341 : Blo 2267435 16578341 := bstep (se 4 (by rfl) ⟨1554219, by rfl⟩ : syracuseStep 16578341 = 3108439) B3108439
theorem B11052227 : Blo 2267435 11052227 := bstep (se 1 (by rfl) ⟨8289170, by rfl⟩ : syracuseStep 11052227 = 16578341) B16578341
theorem B29472605 : Blo 2267435 29472605 := bstep (se 3 (by rfl) ⟨5526113, by rfl⟩ : syracuseStep 29472605 = 11052227) B11052227
theorem B19648403 : Blo 2267435 19648403 := bstep (se 1 (by rfl) ⟨14736302, by rfl⟩ : syracuseStep 19648403 = 29472605) B29472605
theorem B13098935 : Blo 2267435 13098935 := bstep (se 1 (by rfl) ⟨9824201, by rfl⟩ : syracuseStep 13098935 = 19648403) B19648403
theorem B8732623 : Blo 2267435 8732623 := bstep (se 1 (by rfl) ⟨6549467, by rfl⟩ : syracuseStep 8732623 = 13098935) B13098935
theorem B11643497 : Blo 2267435 11643497 := bstep (se 2 (by rfl) ⟨4366311, by rfl⟩ : syracuseStep 11643497 = 8732623) B8732623
theorem B7762331 : Blo 2267435 7762331 := bstep (se 1 (by rfl) ⟨5821748, by rfl⟩ : syracuseStep 7762331 = 11643497) B11643497
theorem B5174887 : Blo 2267435 5174887 := bstep (se 1 (by rfl) ⟨3881165, by rfl⟩ : syracuseStep 5174887 = 7762331) B7762331
theorem B6899849 : Blo 2267435 6899849 := bstep (se 2 (by rfl) ⟨2587443, by rfl⟩ : syracuseStep 6899849 = 5174887) B5174887
theorem B4599899 : Blo 2267435 4599899 := bstep (se 1 (by rfl) ⟨3449924, by rfl⟩ : syracuseStep 4599899 = 6899849) B6899849
theorem B3066599 : Blo 2267435 3066599 := bstep (se 1 (by rfl) ⟨2299949, by rfl⟩ : syracuseStep 3066599 = 4599899) B4599899
theorem B8177597 : Blo 2267435 8177597 := bstep (se 3 (by rfl) ⟨1533299, by rfl⟩ : syracuseStep 8177597 = 3066599) B3066599
theorem B5451731 : Blo 2267435 5451731 := bstep (se 1 (by rfl) ⟨4088798, by rfl⟩ : syracuseStep 5451731 = 8177597) B8177597
theorem B3634487 : Blo 2267435 3634487 := bstep (se 1 (by rfl) ⟨2725865, by rfl⟩ : syracuseStep 3634487 = 5451731) B5451731
theorem B2422991 : Blo 2267435 2422991 := bstep (se 1 (by rfl) ⟨1817243, by rfl⟩ : syracuseStep 2422991 = 3634487) B3634487
theorem B6461309 : Blo 2267435 6461309 := bstep (se 3 (by rfl) ⟨1211495, by rfl⟩ : syracuseStep 6461309 = 2422991) B2422991
theorem B17230157 : Blo 2267435 17230157 := bstep (se 3 (by rfl) ⟨3230654, by rfl⟩ : syracuseStep 17230157 = 6461309) B6461309
theorem B11486771 : Blo 2267435 11486771 := bstep (se 1 (by rfl) ⟨8615078, by rfl⟩ : syracuseStep 11486771 = 17230157) B17230157
theorem B7657847 : Blo 2267435 7657847 := bstep (se 1 (by rfl) ⟨5743385, by rfl⟩ : syracuseStep 7657847 = 11486771) B11486771
theorem B5105231 : Blo 2267435 5105231 := bstep (se 1 (by rfl) ⟨3828923, by rfl⟩ : syracuseStep 5105231 = 7657847) B7657847
theorem B3403487 : Blo 2267435 3403487 := bstep (se 1 (by rfl) ⟨2552615, by rfl⟩ : syracuseStep 3403487 = 5105231) B5105231
theorem B2268991 : Blo 2267435 2268991 := bstep (se 1 (by rfl) ⟨1701743, by rfl⟩ : syracuseStep 2268991 = 3403487) B3403487
theorem B3403493 : Blo 2267435 3403493 := bbase (se 4 (by rfl) ⟨319077, by rfl⟩ : syracuseStep 3403493 = 638155) (by norm_num)
theorem B2268995 : Blo 2267435 2268995 := bstep (se 1 (by rfl) ⟨1701746, by rfl⟩ : syracuseStep 2268995 = 3403493) B3403493
theorem B6461333 : Blo 2267435 6461333 := bbase (se 6 (by rfl) ⟨151437, by rfl⟩ : syracuseStep 6461333 = 302875) (by norm_num)
theorem B4307555 : Blo 2267435 4307555 := bstep (se 1 (by rfl) ⟨3230666, by rfl⟩ : syracuseStep 4307555 = 6461333) B6461333
theorem B2871703 : Blo 2267435 2871703 := bstep (se 1 (by rfl) ⟨2153777, by rfl⟩ : syracuseStep 2871703 = 4307555) B4307555
theorem B3828937 : Blo 2267435 3828937 := bstep (se 2 (by rfl) ⟨1435851, by rfl⟩ : syracuseStep 3828937 = 2871703) B2871703
theorem B5105249 : Blo 2267435 5105249 := bstep (se 2 (by rfl) ⟨1914468, by rfl⟩ : syracuseStep 5105249 = 3828937) B3828937
theorem B3403499 : Blo 2267435 3403499 := bstep (se 1 (by rfl) ⟨2552624, by rfl⟩ : syracuseStep 3403499 = 5105249) B5105249
theorem B2268999 : Blo 2267435 2268999 := bstep (se 1 (by rfl) ⟨1701749, by rfl⟩ : syracuseStep 2268999 = 3403499) B3403499
theorem B2552629 : Blo 2267435 2552629 := bbase (se 5 (by rfl) ⟨119654, by rfl⟩ : syracuseStep 2552629 = 239309) (by norm_num)
theorem B3403505 : Blo 2267435 3403505 := bstep (se 2 (by rfl) ⟨1276314, by rfl⟩ : syracuseStep 3403505 = 2552629) B2552629
theorem B2269003 : Blo 2267435 2269003 := bstep (se 1 (by rfl) ⟨1701752, by rfl⟩ : syracuseStep 2269003 = 3403505) B3403505
theorem B2871713 : Blo 2267435 2871713 := bbase (se 2 (by rfl) ⟨1076892, by rfl⟩ : syracuseStep 2871713 = 2153785) (by norm_num)
theorem B7657901 : Blo 2267435 7657901 := bstep (se 3 (by rfl) ⟨1435856, by rfl⟩ : syracuseStep 7657901 = 2871713) B2871713
theorem B5105267 : Blo 2267435 5105267 := bstep (se 1 (by rfl) ⟨3828950, by rfl⟩ : syracuseStep 5105267 = 7657901) B7657901
theorem B3403511 : Blo 2267435 3403511 := bstep (se 1 (by rfl) ⟨2552633, by rfl⟩ : syracuseStep 3403511 = 5105267) B5105267
theorem B2269007 : Blo 2267435 2269007 := bstep (se 1 (by rfl) ⟨1701755, by rfl⟩ : syracuseStep 2269007 = 3403511) B3403511
theorem B3403517 : Blo 2267435 3403517 := bbase (se 3 (by rfl) ⟨638159, by rfl⟩ : syracuseStep 3403517 = 1276319) (by norm_num)
theorem B2269011 : Blo 2267435 2269011 := bstep (se 1 (by rfl) ⟨1701758, by rfl⟩ : syracuseStep 2269011 = 3403517) B3403517
theorem B5105285 : Blo 2267435 5105285 := bbase (se 4 (by rfl) ⟨478620, by rfl⟩ : syracuseStep 5105285 = 957241) (by norm_num)
theorem B3403523 : Blo 2267435 3403523 := bstep (se 1 (by rfl) ⟨2552642, by rfl⟩ : syracuseStep 3403523 = 5105285) B5105285
theorem B2269015 : Blo 2267435 2269015 := bstep (se 1 (by rfl) ⟨1701761, by rfl⟩ : syracuseStep 2269015 = 3403523) B3403523
theorem B12266549 : Blo 2267435 12266549 := bbase (se 5 (by rfl) ⟨574994, by rfl⟩ : syracuseStep 12266549 = 1149989) (by norm_num)
theorem B8177699 : Blo 2267435 8177699 := bstep (se 1 (by rfl) ⟨6133274, by rfl⟩ : syracuseStep 8177699 = 12266549) B12266549
theorem B5451799 : Blo 2267435 5451799 := bstep (se 1 (by rfl) ⟨4088849, by rfl⟩ : syracuseStep 5451799 = 8177699) B8177699
theorem B7269065 : Blo 2267435 7269065 := bstep (se 2 (by rfl) ⟨2725899, by rfl⟩ : syracuseStep 7269065 = 5451799) B5451799
theorem B4846043 : Blo 2267435 4846043 := bstep (se 1 (by rfl) ⟨3634532, by rfl⟩ : syracuseStep 4846043 = 7269065) B7269065
theorem B3230695 : Blo 2267435 3230695 := bstep (se 1 (by rfl) ⟨2423021, by rfl⟩ : syracuseStep 3230695 = 4846043) B4846043
theorem B4307593 : Blo 2267435 4307593 := bstep (se 2 (by rfl) ⟨1615347, by rfl⟩ : syracuseStep 4307593 = 3230695) B3230695
theorem B5743457 : Blo 2267435 5743457 := bstep (se 2 (by rfl) ⟨2153796, by rfl⟩ : syracuseStep 5743457 = 4307593) B4307593
theorem B3828971 : Blo 2267435 3828971 := bstep (se 1 (by rfl) ⟨2871728, by rfl⟩ : syracuseStep 3828971 = 5743457) B5743457
theorem B2552647 : Blo 2267435 2552647 := bstep (se 1 (by rfl) ⟨1914485, by rfl⟩ : syracuseStep 2552647 = 3828971) B3828971
theorem B3403529 : Blo 2267435 3403529 := bstep (se 2 (by rfl) ⟨1276323, by rfl⟩ : syracuseStep 3403529 = 2552647) B2552647
theorem B2269019 : Blo 2267435 2269019 := bstep (se 1 (by rfl) ⟨1701764, by rfl⟩ : syracuseStep 2269019 = 3403529) B3403529
theorem B11486933 : Blo 2267435 11486933 := bbase (se 7 (by rfl) ⟨134612, by rfl⟩ : syracuseStep 11486933 = 269225) (by norm_num)
theorem B7657955 : Blo 2267435 7657955 := bstep (se 1 (by rfl) ⟨5743466, by rfl⟩ : syracuseStep 7657955 = 11486933) B11486933
theorem B5105303 : Blo 2267435 5105303 := bstep (se 1 (by rfl) ⟨3828977, by rfl⟩ : syracuseStep 5105303 = 7657955) B7657955
theorem B3403535 : Blo 2267435 3403535 := bstep (se 1 (by rfl) ⟨2552651, by rfl⟩ : syracuseStep 3403535 = 5105303) B5105303
theorem B2269023 : Blo 2267435 2269023 := bstep (se 1 (by rfl) ⟨1701767, by rfl⟩ : syracuseStep 2269023 = 3403535) B3403535
theorem B3403541 : Blo 2267435 3403541 := bbase (se 6 (by rfl) ⟨79770, by rfl⟩ : syracuseStep 3403541 = 159541) (by norm_num)
theorem B2269027 : Blo 2267435 2269027 := bstep (se 1 (by rfl) ⟨1701770, by rfl⟩ : syracuseStep 2269027 = 3403541) B3403541
theorem B36799829 : Blo 2267435 36799829 := bbase (se 12 (by rfl) ⟨13476, by rfl⟩ : syracuseStep 36799829 = 26953) (by norm_num)
theorem B24533219 : Blo 2267435 24533219 := bstep (se 1 (by rfl) ⟨18399914, by rfl⟩ : syracuseStep 24533219 = 36799829) B36799829
theorem B65421917 : Blo 2267435 65421917 := bstep (se 3 (by rfl) ⟨12266609, by rfl⟩ : syracuseStep 65421917 = 24533219) B24533219
theorem B43614611 : Blo 2267435 43614611 := bstep (se 1 (by rfl) ⟨32710958, by rfl⟩ : syracuseStep 43614611 = 65421917) B65421917
theorem B29076407 : Blo 2267435 29076407 := bstep (se 1 (by rfl) ⟨21807305, by rfl⟩ : syracuseStep 29076407 = 43614611) B43614611
theorem B19384271 : Blo 2267435 19384271 := bstep (se 1 (by rfl) ⟨14538203, by rfl⟩ : syracuseStep 19384271 = 29076407) B29076407
theorem B12922847 : Blo 2267435 12922847 := bstep (se 1 (by rfl) ⟨9692135, by rfl⟩ : syracuseStep 12922847 = 19384271) B19384271
theorem B8615231 : Blo 2267435 8615231 := bstep (se 1 (by rfl) ⟨6461423, by rfl⟩ : syracuseStep 8615231 = 12922847) B12922847
theorem B5743487 : Blo 2267435 5743487 := bstep (se 1 (by rfl) ⟨4307615, by rfl⟩ : syracuseStep 5743487 = 8615231) B8615231
theorem B3828991 : Blo 2267435 3828991 := bstep (se 1 (by rfl) ⟨2871743, by rfl⟩ : syracuseStep 3828991 = 5743487) B5743487
theorem B5105321 : Blo 2267435 5105321 := bstep (se 2 (by rfl) ⟨1914495, by rfl⟩ : syracuseStep 5105321 = 3828991) B3828991
theorem B3403547 : Blo 2267435 3403547 := bstep (se 1 (by rfl) ⟨2552660, by rfl⟩ : syracuseStep 3403547 = 5105321) B5105321
theorem B2269031 : Blo 2267435 2269031 := bstep (se 1 (by rfl) ⟨1701773, by rfl⟩ : syracuseStep 2269031 = 3403547) B3403547
theorem B2552665 : Blo 2267435 2552665 := bbase (se 2 (by rfl) ⟨957249, by rfl⟩ : syracuseStep 2552665 = 1914499) (by norm_num)
theorem B3403553 : Blo 2267435 3403553 := bstep (se 2 (by rfl) ⟨1276332, by rfl⟩ : syracuseStep 3403553 = 2552665) B2552665
theorem B2269035 : Blo 2267435 2269035 := bstep (se 1 (by rfl) ⟨1701776, by rfl⟩ : syracuseStep 2269035 = 3403553) B3403553
theorem B4846085 : Blo 2267435 4846085 := bbase (se 4 (by rfl) ⟨454320, by rfl⟩ : syracuseStep 4846085 = 908641) (by norm_num)
theorem B3230723 : Blo 2267435 3230723 := bstep (se 1 (by rfl) ⟨2423042, by rfl⟩ : syracuseStep 3230723 = 4846085) B4846085
theorem B8615261 : Blo 2267435 8615261 := bstep (se 3 (by rfl) ⟨1615361, by rfl⟩ : syracuseStep 8615261 = 3230723) B3230723
theorem B5743507 : Blo 2267435 5743507 := bstep (se 1 (by rfl) ⟨4307630, by rfl⟩ : syracuseStep 5743507 = 8615261) B8615261
theorem B7658009 : Blo 2267435 7658009 := bstep (se 2 (by rfl) ⟨2871753, by rfl⟩ : syracuseStep 7658009 = 5743507) B5743507
theorem B5105339 : Blo 2267435 5105339 := bstep (se 1 (by rfl) ⟨3829004, by rfl⟩ : syracuseStep 5105339 = 7658009) B7658009
theorem B3403559 : Blo 2267435 3403559 := bstep (se 1 (by rfl) ⟨2552669, by rfl⟩ : syracuseStep 3403559 = 5105339) B5105339
theorem B2269039 : Blo 2267435 2269039 := bstep (se 1 (by rfl) ⟨1701779, by rfl⟩ : syracuseStep 2269039 = 3403559) B3403559
theorem B3403565 : Blo 2267435 3403565 := bbase (se 3 (by rfl) ⟨638168, by rfl⟩ : syracuseStep 3403565 = 1276337) (by norm_num)
theorem B2269043 : Blo 2267435 2269043 := bstep (se 1 (by rfl) ⟨1701782, by rfl⟩ : syracuseStep 2269043 = 3403565) B3403565
theorem B5105357 : Blo 2267435 5105357 := bbase (se 3 (by rfl) ⟨957254, by rfl⟩ : syracuseStep 5105357 = 1914509) (by norm_num)
theorem B3403571 : Blo 2267435 3403571 := bstep (se 1 (by rfl) ⟨2552678, by rfl⟩ : syracuseStep 3403571 = 5105357) B5105357
theorem B2269047 : Blo 2267435 2269047 := bstep (se 1 (by rfl) ⟨1701785, by rfl⟩ : syracuseStep 2269047 = 3403571) B3403571
theorem B2871769 : Blo 2267435 2871769 := bbase (se 2 (by rfl) ⟨1076913, by rfl⟩ : syracuseStep 2871769 = 2153827) (by norm_num)
theorem B3829025 : Blo 2267435 3829025 := bstep (se 2 (by rfl) ⟨1435884, by rfl⟩ : syracuseStep 3829025 = 2871769) B2871769
theorem B2552683 : Blo 2267435 2552683 := bstep (se 1 (by rfl) ⟨1914512, by rfl⟩ : syracuseStep 2552683 = 3829025) B3829025
theorem B3403577 : Blo 2267435 3403577 := bstep (se 2 (by rfl) ⟨1276341, by rfl⟩ : syracuseStep 3403577 = 2552683) B2552683
theorem B2269051 : Blo 2267435 2269051 := bstep (se 1 (by rfl) ⟨1701788, by rfl⟩ : syracuseStep 2269051 = 3403577) B3403577
theorem B3634589 : Blo 2267435 3634589 := bbase (se 3 (by rfl) ⟨681485, by rfl⟩ : syracuseStep 3634589 = 1362971) (by norm_num)
theorem B9692237 : Blo 2267435 9692237 := bstep (se 3 (by rfl) ⟨1817294, by rfl⟩ : syracuseStep 9692237 = 3634589) B3634589
theorem B25845965 : Blo 2267435 25845965 := bstep (se 3 (by rfl) ⟨4846118, by rfl⟩ : syracuseStep 25845965 = 9692237) B9692237
theorem B17230643 : Blo 2267435 17230643 := bstep (se 1 (by rfl) ⟨12922982, by rfl⟩ : syracuseStep 17230643 = 25845965) B25845965
theorem B11487095 : Blo 2267435 11487095 := bstep (se 1 (by rfl) ⟨8615321, by rfl⟩ : syracuseStep 11487095 = 17230643) B17230643
theorem B7658063 : Blo 2267435 7658063 := bstep (se 1 (by rfl) ⟨5743547, by rfl⟩ : syracuseStep 7658063 = 11487095) B11487095
theorem B5105375 : Blo 2267435 5105375 := bstep (se 1 (by rfl) ⟨3829031, by rfl⟩ : syracuseStep 5105375 = 7658063) B7658063
theorem B3403583 : Blo 2267435 3403583 := bstep (se 1 (by rfl) ⟨2552687, by rfl⟩ : syracuseStep 3403583 = 5105375) B5105375
theorem B2269055 : Blo 2267435 2269055 := bstep (se 1 (by rfl) ⟨1701791, by rfl⟩ : syracuseStep 2269055 = 3403583) B3403583
theorem B3403589 : Blo 2267435 3403589 := bbase (se 4 (by rfl) ⟨319086, by rfl⟩ : syracuseStep 3403589 = 638173) (by norm_num)
theorem B2269059 : Blo 2267435 2269059 := bstep (se 1 (by rfl) ⟨1701794, by rfl⟩ : syracuseStep 2269059 = 3403589) B3403589
theorem B3829045 : Blo 2267435 3829045 := bbase (se 5 (by rfl) ⟨179486, by rfl⟩ : syracuseStep 3829045 = 358973) (by norm_num)
theorem B5105393 : Blo 2267435 5105393 := bstep (se 2 (by rfl) ⟨1914522, by rfl⟩ : syracuseStep 5105393 = 3829045) B3829045
theorem B3403595 : Blo 2267435 3403595 := bstep (se 1 (by rfl) ⟨2552696, by rfl⟩ : syracuseStep 3403595 = 5105393) B5105393
theorem B2269063 : Blo 2267435 2269063 := bstep (se 1 (by rfl) ⟨1701797, by rfl⟩ : syracuseStep 2269063 = 3403595) B3403595
theorem B2552701 : Blo 2267435 2552701 := bbase (se 3 (by rfl) ⟨478631, by rfl⟩ : syracuseStep 2552701 = 957263) (by norm_num)
theorem B3403601 : Blo 2267435 3403601 := bstep (se 2 (by rfl) ⟨1276350, by rfl⟩ : syracuseStep 3403601 = 2552701) B2552701
theorem B2269067 : Blo 2267435 2269067 := bstep (se 1 (by rfl) ⟨1701800, by rfl⟩ : syracuseStep 2269067 = 3403601) B3403601
theorem B7658117 : Blo 2267435 7658117 := bbase (se 4 (by rfl) ⟨717948, by rfl⟩ : syracuseStep 7658117 = 1435897) (by norm_num)
theorem B5105411 : Blo 2267435 5105411 := bstep (se 1 (by rfl) ⟨3829058, by rfl⟩ : syracuseStep 5105411 = 7658117) B7658117
theorem B3403607 : Blo 2267435 3403607 := bstep (se 1 (by rfl) ⟨2552705, by rfl⟩ : syracuseStep 3403607 = 5105411) B5105411
theorem B2269071 : Blo 2267435 2269071 := bstep (se 1 (by rfl) ⟨1701803, by rfl⟩ : syracuseStep 2269071 = 3403607) B3403607
theorem B3403613 : Blo 2267435 3403613 := bbase (se 3 (by rfl) ⟨638177, by rfl⟩ : syracuseStep 3403613 = 1276355) (by norm_num)
theorem B2269075 : Blo 2267435 2269075 := bstep (se 1 (by rfl) ⟨1701806, by rfl⟩ : syracuseStep 2269075 = 3403613) B3403613
theorem B5105429 : Blo 2267435 5105429 := bbase (se 6 (by rfl) ⟨119658, by rfl⟩ : syracuseStep 5105429 = 239317) (by norm_num)
theorem B3403619 : Blo 2267435 3403619 := bstep (se 1 (by rfl) ⟨2552714, by rfl⟩ : syracuseStep 3403619 = 5105429) B5105429
theorem B2269079 : Blo 2267435 2269079 := bstep (se 1 (by rfl) ⟨1701809, by rfl⟩ : syracuseStep 2269079 = 3403619) B3403619
theorem B8615429 : Blo 2267435 8615429 := bbase (se 4 (by rfl) ⟨807696, by rfl⟩ : syracuseStep 8615429 = 1615393) (by norm_num)
theorem B5743619 : Blo 2267435 5743619 := bstep (se 1 (by rfl) ⟨4307714, by rfl⟩ : syracuseStep 5743619 = 8615429) B8615429
theorem B3829079 : Blo 2267435 3829079 := bstep (se 1 (by rfl) ⟨2871809, by rfl⟩ : syracuseStep 3829079 = 5743619) B5743619
theorem B2552719 : Blo 2267435 2552719 := bstep (se 1 (by rfl) ⟨1914539, by rfl⟩ : syracuseStep 2552719 = 3829079) B3829079
theorem B3403625 : Blo 2267435 3403625 := bstep (se 2 (by rfl) ⟨1276359, by rfl⟩ : syracuseStep 3403625 = 2552719) B2552719
theorem B2269083 : Blo 2267435 2269083 := bstep (se 1 (by rfl) ⟨1701812, by rfl⟩ : syracuseStep 2269083 = 3403625) B3403625
theorem B4600093 : Blo 2267435 4600093 := bbase (se 3 (by rfl) ⟨862517, by rfl⟩ : syracuseStep 4600093 = 1725035) (by norm_num)
theorem B6133457 : Blo 2267435 6133457 := bstep (se 2 (by rfl) ⟨2300046, by rfl⟩ : syracuseStep 6133457 = 4600093) B4600093
theorem B4088971 : Blo 2267435 4088971 := bstep (se 1 (by rfl) ⟨3066728, by rfl⟩ : syracuseStep 4088971 = 6133457) B6133457
theorem B5451961 : Blo 2267435 5451961 := bstep (se 2 (by rfl) ⟨2044485, by rfl⟩ : syracuseStep 5451961 = 4088971) B4088971
theorem B7269281 : Blo 2267435 7269281 := bstep (se 2 (by rfl) ⟨2725980, by rfl⟩ : syracuseStep 7269281 = 5451961) B5451961
theorem B4846187 : Blo 2267435 4846187 := bstep (se 1 (by rfl) ⟨3634640, by rfl⟩ : syracuseStep 4846187 = 7269281) B7269281
theorem B12923165 : Blo 2267435 12923165 := bstep (se 3 (by rfl) ⟨2423093, by rfl⟩ : syracuseStep 12923165 = 4846187) B4846187
theorem B8615443 : Blo 2267435 8615443 := bstep (se 1 (by rfl) ⟨6461582, by rfl⟩ : syracuseStep 8615443 = 12923165) B12923165
theorem B11487257 : Blo 2267435 11487257 := bstep (se 2 (by rfl) ⟨4307721, by rfl⟩ : syracuseStep 11487257 = 8615443) B8615443
theorem B7658171 : Blo 2267435 7658171 := bstep (se 1 (by rfl) ⟨5743628, by rfl⟩ : syracuseStep 7658171 = 11487257) B11487257
theorem B5105447 : Blo 2267435 5105447 := bstep (se 1 (by rfl) ⟨3829085, by rfl⟩ : syracuseStep 5105447 = 7658171) B7658171
theorem B3403631 : Blo 2267435 3403631 := bstep (se 1 (by rfl) ⟨2552723, by rfl⟩ : syracuseStep 3403631 = 5105447) B5105447
theorem B2269087 : Blo 2267435 2269087 := bstep (se 1 (by rfl) ⟨1701815, by rfl⟩ : syracuseStep 2269087 = 3403631) B3403631
theorem B3403637 : Blo 2267435 3403637 := bbase (se 5 (by rfl) ⟨159545, by rfl⟩ : syracuseStep 3403637 = 319091) (by norm_num)
theorem B2269091 : Blo 2267435 2269091 := bstep (se 1 (by rfl) ⟨1701818, by rfl⟩ : syracuseStep 2269091 = 3403637) B3403637
theorem B4846205 : Blo 2267435 4846205 := bbase (se 3 (by rfl) ⟨908663, by rfl⟩ : syracuseStep 4846205 = 1817327) (by norm_num)
theorem B3230803 : Blo 2267435 3230803 := bstep (se 1 (by rfl) ⟨2423102, by rfl⟩ : syracuseStep 3230803 = 4846205) B4846205
theorem B4307737 : Blo 2267435 4307737 := bstep (se 2 (by rfl) ⟨1615401, by rfl⟩ : syracuseStep 4307737 = 3230803) B3230803
theorem B5743649 : Blo 2267435 5743649 := bstep (se 2 (by rfl) ⟨2153868, by rfl⟩ : syracuseStep 5743649 = 4307737) B4307737
theorem B3829099 : Blo 2267435 3829099 := bstep (se 1 (by rfl) ⟨2871824, by rfl⟩ : syracuseStep 3829099 = 5743649) B5743649
theorem B5105465 : Blo 2267435 5105465 := bstep (se 2 (by rfl) ⟨1914549, by rfl⟩ : syracuseStep 5105465 = 3829099) B3829099
theorem B3403643 : Blo 2267435 3403643 := bstep (se 1 (by rfl) ⟨2552732, by rfl⟩ : syracuseStep 3403643 = 5105465) B5105465
theorem B2269095 : Blo 2267435 2269095 := bstep (se 1 (by rfl) ⟨1701821, by rfl⟩ : syracuseStep 2269095 = 3403643) B3403643
theorem B2552737 : Blo 2267435 2552737 := bbase (se 2 (by rfl) ⟨957276, by rfl⟩ : syracuseStep 2552737 = 1914553) (by norm_num)
theorem B3403649 : Blo 2267435 3403649 := bstep (se 2 (by rfl) ⟨1276368, by rfl⟩ : syracuseStep 3403649 = 2552737) B2552737
theorem B2269099 : Blo 2267435 2269099 := bstep (se 1 (by rfl) ⟨1701824, by rfl⟩ : syracuseStep 2269099 = 3403649) B3403649
theorem B5743669 : Blo 2267435 5743669 := bbase (se 5 (by rfl) ⟨269234, by rfl⟩ : syracuseStep 5743669 = 538469) (by norm_num)
theorem B7658225 : Blo 2267435 7658225 := bstep (se 2 (by rfl) ⟨2871834, by rfl⟩ : syracuseStep 7658225 = 5743669) B5743669
theorem B5105483 : Blo 2267435 5105483 := bstep (se 1 (by rfl) ⟨3829112, by rfl⟩ : syracuseStep 5105483 = 7658225) B7658225
theorem B3403655 : Blo 2267435 3403655 := bstep (se 1 (by rfl) ⟨2552741, by rfl⟩ : syracuseStep 3403655 = 5105483) B5105483
theorem B2269103 : Blo 2267435 2269103 := bstep (se 1 (by rfl) ⟨1701827, by rfl⟩ : syracuseStep 2269103 = 3403655) B3403655
theorem B3403661 : Blo 2267435 3403661 := bbase (se 3 (by rfl) ⟨638186, by rfl⟩ : syracuseStep 3403661 = 1276373) (by norm_num)
theorem B2269107 : Blo 2267435 2269107 := bstep (se 1 (by rfl) ⟨1701830, by rfl⟩ : syracuseStep 2269107 = 3403661) B3403661
theorem B5105501 : Blo 2267435 5105501 := bbase (se 3 (by rfl) ⟨957281, by rfl⟩ : syracuseStep 5105501 = 1914563) (by norm_num)
theorem B3403667 : Blo 2267435 3403667 := bstep (se 1 (by rfl) ⟨2552750, by rfl⟩ : syracuseStep 3403667 = 5105501) B5105501
theorem B2269111 : Blo 2267435 2269111 := bstep (se 1 (by rfl) ⟨1701833, by rfl⟩ : syracuseStep 2269111 = 3403667) B3403667
theorem B3829133 : Blo 2267435 3829133 := bbase (se 3 (by rfl) ⟨717962, by rfl⟩ : syracuseStep 3829133 = 1435925) (by norm_num)
theorem B2552755 : Blo 2267435 2552755 := bstep (se 1 (by rfl) ⟨1914566, by rfl⟩ : syracuseStep 2552755 = 3829133) B3829133
theorem B3403673 : Blo 2267435 3403673 := bstep (se 2 (by rfl) ⟨1276377, by rfl⟩ : syracuseStep 3403673 = 2552755) B2552755
theorem B2269115 : Blo 2267435 2269115 := bstep (se 1 (by rfl) ⟨1701836, by rfl⟩ : syracuseStep 2269115 = 3403673) B3403673
theorem B4600157 : Blo 2267435 4600157 := bbase (se 3 (by rfl) ⟨862529, by rfl⟩ : syracuseStep 4600157 = 1725059) (by norm_num)
theorem B12267085 : Blo 2267435 12267085 := bstep (se 3 (by rfl) ⟨2300078, by rfl⟩ : syracuseStep 12267085 = 4600157) B4600157
theorem B16356113 : Blo 2267435 16356113 := bstep (se 2 (by rfl) ⟨6133542, by rfl⟩ : syracuseStep 16356113 = 12267085) B12267085
theorem B10904075 : Blo 2267435 10904075 := bstep (se 1 (by rfl) ⟨8178056, by rfl⟩ : syracuseStep 10904075 = 16356113) B16356113
theorem B7269383 : Blo 2267435 7269383 := bstep (se 1 (by rfl) ⟨5452037, by rfl⟩ : syracuseStep 7269383 = 10904075) B10904075
theorem B19385021 : Blo 2267435 19385021 := bstep (se 3 (by rfl) ⟨3634691, by rfl⟩ : syracuseStep 19385021 = 7269383) B7269383
theorem B12923347 : Blo 2267435 12923347 := bstep (se 1 (by rfl) ⟨9692510, by rfl⟩ : syracuseStep 12923347 = 19385021) B19385021
theorem B17231129 : Blo 2267435 17231129 := bstep (se 2 (by rfl) ⟨6461673, by rfl⟩ : syracuseStep 17231129 = 12923347) B12923347
theorem B11487419 : Blo 2267435 11487419 := bstep (se 1 (by rfl) ⟨8615564, by rfl⟩ : syracuseStep 11487419 = 17231129) B17231129
theorem B7658279 : Blo 2267435 7658279 := bstep (se 1 (by rfl) ⟨5743709, by rfl⟩ : syracuseStep 7658279 = 11487419) B11487419
theorem B5105519 : Blo 2267435 5105519 := bstep (se 1 (by rfl) ⟨3829139, by rfl⟩ : syracuseStep 5105519 = 7658279) B7658279
theorem B3403679 : Blo 2267435 3403679 := bstep (se 1 (by rfl) ⟨2552759, by rfl⟩ : syracuseStep 3403679 = 5105519) B5105519
theorem B2269119 : Blo 2267435 2269119 := bstep (se 1 (by rfl) ⟨1701839, by rfl⟩ : syracuseStep 2269119 = 3403679) B3403679
theorem B3403685 : Blo 2267435 3403685 := bbase (se 4 (by rfl) ⟨319095, by rfl⟩ : syracuseStep 3403685 = 638191) (by norm_num)
theorem B2269123 : Blo 2267435 2269123 := bstep (se 1 (by rfl) ⟨1701842, by rfl⟩ : syracuseStep 2269123 = 3403685) B3403685
theorem B2871865 : Blo 2267435 2871865 := bbase (se 2 (by rfl) ⟨1076949, by rfl⟩ : syracuseStep 2871865 = 2153899) (by norm_num)
theorem B3829153 : Blo 2267435 3829153 := bstep (se 2 (by rfl) ⟨1435932, by rfl⟩ : syracuseStep 3829153 = 2871865) B2871865
theorem B5105537 : Blo 2267435 5105537 := bstep (se 2 (by rfl) ⟨1914576, by rfl⟩ : syracuseStep 5105537 = 3829153) B3829153
theorem B3403691 : Blo 2267435 3403691 := bstep (se 1 (by rfl) ⟨2552768, by rfl⟩ : syracuseStep 3403691 = 5105537) B5105537
theorem B2269127 : Blo 2267435 2269127 := bstep (se 1 (by rfl) ⟨1701845, by rfl⟩ : syracuseStep 2269127 = 3403691) B3403691
theorem B2552773 : Blo 2267435 2552773 := bbase (se 4 (by rfl) ⟨239322, by rfl⟩ : syracuseStep 2552773 = 478645) (by norm_num)
theorem B3403697 : Blo 2267435 3403697 := bstep (se 2 (by rfl) ⟨1276386, by rfl⟩ : syracuseStep 3403697 = 2552773) B2552773
theorem B2269131 : Blo 2267435 2269131 := bstep (se 1 (by rfl) ⟨1701848, by rfl⟩ : syracuseStep 2269131 = 3403697) B3403697
theorem B4307813 : Blo 2267435 4307813 := bbase (se 4 (by rfl) ⟨403857, by rfl⟩ : syracuseStep 4307813 = 807715) (by norm_num)
theorem B2871875 : Blo 2267435 2871875 := bstep (se 1 (by rfl) ⟨2153906, by rfl⟩ : syracuseStep 2871875 = 4307813) B4307813
theorem B7658333 : Blo 2267435 7658333 := bstep (se 3 (by rfl) ⟨1435937, by rfl⟩ : syracuseStep 7658333 = 2871875) B2871875
theorem B5105555 : Blo 2267435 5105555 := bstep (se 1 (by rfl) ⟨3829166, by rfl⟩ : syracuseStep 5105555 = 7658333) B7658333
theorem B3403703 : Blo 2267435 3403703 := bstep (se 1 (by rfl) ⟨2552777, by rfl⟩ : syracuseStep 3403703 = 5105555) B5105555
theorem B2269135 : Blo 2267435 2269135 := bstep (se 1 (by rfl) ⟨1701851, by rfl⟩ : syracuseStep 2269135 = 3403703) B3403703
theorem B3403709 : Blo 2267435 3403709 := bbase (se 3 (by rfl) ⟨638195, by rfl⟩ : syracuseStep 3403709 = 1276391) (by norm_num)
theorem B2269139 : Blo 2267435 2269139 := bstep (se 1 (by rfl) ⟨1701854, by rfl⟩ : syracuseStep 2269139 = 3403709) B3403709
theorem B5105573 : Blo 2267435 5105573 := bbase (se 4 (by rfl) ⟨478647, by rfl⟩ : syracuseStep 5105573 = 957295) (by norm_num)
theorem B3403715 : Blo 2267435 3403715 := bstep (se 1 (by rfl) ⟨2552786, by rfl⟩ : syracuseStep 3403715 = 5105573) B5105573
theorem B2269143 : Blo 2267435 2269143 := bstep (se 1 (by rfl) ⟨1701857, by rfl⟩ : syracuseStep 2269143 = 3403715) B3403715
theorem B5743781 : Blo 2267435 5743781 := bbase (se 4 (by rfl) ⟨538479, by rfl⟩ : syracuseStep 5743781 = 1076959) (by norm_num)
theorem B3829187 : Blo 2267435 3829187 := bstep (se 1 (by rfl) ⟨2871890, by rfl⟩ : syracuseStep 3829187 = 5743781) B5743781
theorem B2552791 : Blo 2267435 2552791 := bstep (se 1 (by rfl) ⟨1914593, by rfl⟩ : syracuseStep 2552791 = 3829187) B3829187
theorem B3403721 : Blo 2267435 3403721 := bstep (se 2 (by rfl) ⟨1276395, by rfl⟩ : syracuseStep 3403721 = 2552791) B2552791
theorem B2269147 : Blo 2267435 2269147 := bstep (se 1 (by rfl) ⟨1701860, by rfl⟩ : syracuseStep 2269147 = 3403721) B3403721
theorem B6461765 : Blo 2267435 6461765 := bbase (se 4 (by rfl) ⟨605790, by rfl⟩ : syracuseStep 6461765 = 1211581) (by norm_num)
theorem B4307843 : Blo 2267435 4307843 := bstep (se 1 (by rfl) ⟨3230882, by rfl⟩ : syracuseStep 4307843 = 6461765) B6461765
theorem B11487581 : Blo 2267435 11487581 := bstep (se 3 (by rfl) ⟨2153921, by rfl⟩ : syracuseStep 11487581 = 4307843) B4307843
theorem B7658387 : Blo 2267435 7658387 := bstep (se 1 (by rfl) ⟨5743790, by rfl⟩ : syracuseStep 7658387 = 11487581) B11487581
theorem B5105591 : Blo 2267435 5105591 := bstep (se 1 (by rfl) ⟨3829193, by rfl⟩ : syracuseStep 5105591 = 7658387) B7658387
theorem B3403727 : Blo 2267435 3403727 := bstep (se 1 (by rfl) ⟨2552795, by rfl⟩ : syracuseStep 3403727 = 5105591) B5105591
theorem B2269151 : Blo 2267435 2269151 := bstep (se 1 (by rfl) ⟨1701863, by rfl⟩ : syracuseStep 2269151 = 3403727) B3403727
theorem B3403733 : Blo 2267435 3403733 := bbase (se 7 (by rfl) ⟨39887, by rfl⟩ : syracuseStep 3403733 = 79775) (by norm_num)
theorem B2269155 : Blo 2267435 2269155 := bstep (se 1 (by rfl) ⟨1701866, by rfl⟩ : syracuseStep 2269155 = 3403733) B3403733
theorem B8615717 : Blo 2267435 8615717 := bbase (se 4 (by rfl) ⟨807723, by rfl⟩ : syracuseStep 8615717 = 1615447) (by norm_num)
theorem B5743811 : Blo 2267435 5743811 := bstep (se 1 (by rfl) ⟨4307858, by rfl⟩ : syracuseStep 5743811 = 8615717) B8615717
theorem B3829207 : Blo 2267435 3829207 := bstep (se 1 (by rfl) ⟨2871905, by rfl⟩ : syracuseStep 3829207 = 5743811) B5743811
theorem B5105609 : Blo 2267435 5105609 := bstep (se 2 (by rfl) ⟨1914603, by rfl⟩ : syracuseStep 5105609 = 3829207) B3829207
theorem B3403739 : Blo 2267435 3403739 := bstep (se 1 (by rfl) ⟨2552804, by rfl⟩ : syracuseStep 3403739 = 5105609) B5105609
theorem B2269159 : Blo 2267435 2269159 := bstep (se 1 (by rfl) ⟨1701869, by rfl⟩ : syracuseStep 2269159 = 3403739) B3403739
theorem B2552809 : Blo 2267435 2552809 := bbase (se 2 (by rfl) ⟨957303, by rfl⟩ : syracuseStep 2552809 = 1914607) (by norm_num)
theorem B3403745 : Blo 2267435 3403745 := bstep (se 2 (by rfl) ⟨1276404, by rfl⟩ : syracuseStep 3403745 = 2552809) B2552809
theorem B2269163 : Blo 2267435 2269163 := bstep (se 1 (by rfl) ⟨1701872, by rfl⟩ : syracuseStep 2269163 = 3403745) B3403745
theorem B2726077 : Blo 2267435 2726077 := bbase (se 3 (by rfl) ⟨511139, by rfl⟩ : syracuseStep 2726077 = 1022279) (by norm_num)
theorem B3634769 : Blo 2267435 3634769 := bstep (se 2 (by rfl) ⟨1363038, by rfl⟩ : syracuseStep 3634769 = 2726077) B2726077
theorem B2423179 : Blo 2267435 2423179 := bstep (se 1 (by rfl) ⟨1817384, by rfl⟩ : syracuseStep 2423179 = 3634769) B3634769
theorem B12923621 : Blo 2267435 12923621 := bstep (se 4 (by rfl) ⟨1211589, by rfl⟩ : syracuseStep 12923621 = 2423179) B2423179
theorem B8615747 : Blo 2267435 8615747 := bstep (se 1 (by rfl) ⟨6461810, by rfl⟩ : syracuseStep 8615747 = 12923621) B12923621
theorem B5743831 : Blo 2267435 5743831 := bstep (se 1 (by rfl) ⟨4307873, by rfl⟩ : syracuseStep 5743831 = 8615747) B8615747
theorem B7658441 : Blo 2267435 7658441 := bstep (se 2 (by rfl) ⟨2871915, by rfl⟩ : syracuseStep 7658441 = 5743831) B5743831
theorem B5105627 : Blo 2267435 5105627 := bstep (se 1 (by rfl) ⟨3829220, by rfl⟩ : syracuseStep 5105627 = 7658441) B7658441
theorem B3403751 : Blo 2267435 3403751 := bstep (se 1 (by rfl) ⟨2552813, by rfl⟩ : syracuseStep 3403751 = 5105627) B5105627
theorem B2269167 : Blo 2267435 2269167 := bstep (se 1 (by rfl) ⟨1701875, by rfl⟩ : syracuseStep 2269167 = 3403751) B3403751
theorem B3403757 : Blo 2267435 3403757 := bbase (se 3 (by rfl) ⟨638204, by rfl⟩ : syracuseStep 3403757 = 1276409) (by norm_num)
theorem B2269171 : Blo 2267435 2269171 := bstep (se 1 (by rfl) ⟨1701878, by rfl⟩ : syracuseStep 2269171 = 3403757) B3403757
theorem B5105645 : Blo 2267435 5105645 := bbase (se 3 (by rfl) ⟨957308, by rfl⟩ : syracuseStep 5105645 = 1914617) (by norm_num)
theorem B3403763 : Blo 2267435 3403763 := bstep (se 1 (by rfl) ⟨2552822, by rfl⟩ : syracuseStep 3403763 = 5105645) B5105645
theorem B2269175 : Blo 2267435 2269175 := bstep (se 1 (by rfl) ⟨1701881, by rfl⟩ : syracuseStep 2269175 = 3403763) B3403763
theorem B3634789 : Blo 2267435 3634789 := bbase (se 4 (by rfl) ⟨340761, by rfl⟩ : syracuseStep 3634789 = 681523) (by norm_num)
theorem B4846385 : Blo 2267435 4846385 := bstep (se 2 (by rfl) ⟨1817394, by rfl⟩ : syracuseStep 4846385 = 3634789) B3634789
theorem B3230923 : Blo 2267435 3230923 := bstep (se 1 (by rfl) ⟨2423192, by rfl⟩ : syracuseStep 3230923 = 4846385) B4846385
theorem B4307897 : Blo 2267435 4307897 := bstep (se 2 (by rfl) ⟨1615461, by rfl⟩ : syracuseStep 4307897 = 3230923) B3230923
theorem B2871931 : Blo 2267435 2871931 := bstep (se 1 (by rfl) ⟨2153948, by rfl⟩ : syracuseStep 2871931 = 4307897) B4307897
theorem B3829241 : Blo 2267435 3829241 := bstep (se 2 (by rfl) ⟨1435965, by rfl⟩ : syracuseStep 3829241 = 2871931) B2871931
theorem B2552827 : Blo 2267435 2552827 := bstep (se 1 (by rfl) ⟨1914620, by rfl⟩ : syracuseStep 2552827 = 3829241) B3829241
theorem B3403769 : Blo 2267435 3403769 := bstep (se 2 (by rfl) ⟨1276413, by rfl⟩ : syracuseStep 3403769 = 2552827) B2552827
theorem B2269179 : Blo 2267435 2269179 := bstep (se 1 (by rfl) ⟨1701884, by rfl⟩ : syracuseStep 2269179 = 3403769) B3403769
theorem B4144933 : Blo 2267435 4144933 := bbase (se 4 (by rfl) ⟨388587, by rfl⟩ : syracuseStep 4144933 = 777175) (by norm_num)
theorem B5526577 : Blo 2267435 5526577 := bstep (se 2 (by rfl) ⟨2072466, by rfl⟩ : syracuseStep 5526577 = 4144933) B4144933
theorem B7368769 : Blo 2267435 7368769 := bstep (se 2 (by rfl) ⟨2763288, by rfl⟩ : syracuseStep 7368769 = 5526577) B5526577
theorem B39300101 : Blo 2267435 39300101 := bstep (se 4 (by rfl) ⟨3684384, by rfl⟩ : syracuseStep 39300101 = 7368769) B7368769
theorem B419201077 : Blo 2267435 419201077 := bstep (se 5 (by rfl) ⟨19650050, by rfl⟩ : syracuseStep 419201077 = 39300101) B39300101
theorem B558934769 : Blo 2267435 558934769 := bstep (se 2 (by rfl) ⟨209600538, by rfl⟩ : syracuseStep 558934769 = 419201077) B419201077
theorem B372623179 : Blo 2267435 372623179 := bstep (se 1 (by rfl) ⟨279467384, by rfl⟩ : syracuseStep 372623179 = 558934769) B558934769
theorem B496830905 : Blo 2267435 496830905 := bstep (se 2 (by rfl) ⟨186311589, by rfl⟩ : syracuseStep 496830905 = 372623179) B372623179
theorem B331220603 : Blo 2267435 331220603 := bstep (se 1 (by rfl) ⟨248415452, by rfl⟩ : syracuseStep 331220603 = 496830905) B496830905
theorem B220813735 : Blo 2267435 220813735 := bstep (se 1 (by rfl) ⟨165610301, by rfl⟩ : syracuseStep 220813735 = 331220603) B331220603
theorem B294418313 : Blo 2267435 294418313 := bstep (se 2 (by rfl) ⟨110406867, by rfl⟩ : syracuseStep 294418313 = 220813735) B220813735
theorem B196278875 : Blo 2267435 196278875 := bstep (se 1 (by rfl) ⟨147209156, by rfl⟩ : syracuseStep 196278875 = 294418313) B294418313
theorem B130852583 : Blo 2267435 130852583 := bstep (se 1 (by rfl) ⟨98139437, by rfl⟩ : syracuseStep 130852583 = 196278875) B196278875
theorem B87235055 : Blo 2267435 87235055 := bstep (se 1 (by rfl) ⟨65426291, by rfl⟩ : syracuseStep 87235055 = 130852583) B130852583
theorem B58156703 : Blo 2267435 58156703 := bstep (se 1 (by rfl) ⟨43617527, by rfl⟩ : syracuseStep 58156703 = 87235055) B87235055
theorem B38771135 : Blo 2267435 38771135 := bstep (se 1 (by rfl) ⟨29078351, by rfl⟩ : syracuseStep 38771135 = 58156703) B58156703
theorem B25847423 : Blo 2267435 25847423 := bstep (se 1 (by rfl) ⟨19385567, by rfl⟩ : syracuseStep 25847423 = 38771135) B38771135
theorem B17231615 : Blo 2267435 17231615 := bstep (se 1 (by rfl) ⟨12923711, by rfl⟩ : syracuseStep 17231615 = 25847423) B25847423
theorem B11487743 : Blo 2267435 11487743 := bstep (se 1 (by rfl) ⟨8615807, by rfl⟩ : syracuseStep 11487743 = 17231615) B17231615
theorem B7658495 : Blo 2267435 7658495 := bstep (se 1 (by rfl) ⟨5743871, by rfl⟩ : syracuseStep 7658495 = 11487743) B11487743
theorem B5105663 : Blo 2267435 5105663 := bstep (se 1 (by rfl) ⟨3829247, by rfl⟩ : syracuseStep 5105663 = 7658495) B7658495
theorem B3403775 : Blo 2267435 3403775 := bstep (se 1 (by rfl) ⟨2552831, by rfl⟩ : syracuseStep 3403775 = 5105663) B5105663
theorem B2269183 : Blo 2267435 2269183 := bstep (se 1 (by rfl) ⟨1701887, by rfl⟩ : syracuseStep 2269183 = 3403775) B3403775
theorem B3403781 : Blo 2267435 3403781 := bbase (se 4 (by rfl) ⟨319104, by rfl⟩ : syracuseStep 3403781 = 638209) (by norm_num)
theorem B2269187 : Blo 2267435 2269187 := bstep (se 1 (by rfl) ⟨1701890, by rfl⟩ : syracuseStep 2269187 = 3403781) B3403781
theorem B3829261 : Blo 2267435 3829261 := bbase (se 3 (by rfl) ⟨717986, by rfl⟩ : syracuseStep 3829261 = 1435973) (by norm_num)
theorem B5105681 : Blo 2267435 5105681 := bstep (se 2 (by rfl) ⟨1914630, by rfl⟩ : syracuseStep 5105681 = 3829261) B3829261
theorem B3403787 : Blo 2267435 3403787 := bstep (se 1 (by rfl) ⟨2552840, by rfl⟩ : syracuseStep 3403787 = 5105681) B5105681
theorem B2269191 : Blo 2267435 2269191 := bstep (se 1 (by rfl) ⟨1701893, by rfl⟩ : syracuseStep 2269191 = 3403787) B3403787
theorem B2552845 : Blo 2267435 2552845 := bbase (se 3 (by rfl) ⟨478658, by rfl⟩ : syracuseStep 2552845 = 957317) (by norm_num)
theorem B3403793 : Blo 2267435 3403793 := bstep (se 2 (by rfl) ⟨1276422, by rfl⟩ : syracuseStep 3403793 = 2552845) B2552845
theorem B2269195 : Blo 2267435 2269195 := bstep (se 1 (by rfl) ⟨1701896, by rfl⟩ : syracuseStep 2269195 = 3403793) B3403793
theorem B7658549 : Blo 2267435 7658549 := bbase (se 5 (by rfl) ⟨358994, by rfl⟩ : syracuseStep 7658549 = 717989) (by norm_num)
theorem B5105699 : Blo 2267435 5105699 := bstep (se 1 (by rfl) ⟨3829274, by rfl⟩ : syracuseStep 5105699 = 7658549) B7658549
theorem B3403799 : Blo 2267435 3403799 := bstep (se 1 (by rfl) ⟨2552849, by rfl⟩ : syracuseStep 3403799 = 5105699) B5105699
theorem B2269199 : Blo 2267435 2269199 := bstep (se 1 (by rfl) ⟨1701899, by rfl⟩ : syracuseStep 2269199 = 3403799) B3403799
theorem B3403805 : Blo 2267435 3403805 := bbase (se 3 (by rfl) ⟨638213, by rfl⟩ : syracuseStep 3403805 = 1276427) (by norm_num)
theorem B2269203 : Blo 2267435 2269203 := bstep (se 1 (by rfl) ⟨1701902, by rfl⟩ : syracuseStep 2269203 = 3403805) B3403805
theorem B5105717 : Blo 2267435 5105717 := bbase (se 5 (by rfl) ⟨239330, by rfl⟩ : syracuseStep 5105717 = 478661) (by norm_num)
theorem B3403811 : Blo 2267435 3403811 := bstep (se 1 (by rfl) ⟨2552858, by rfl⟩ : syracuseStep 3403811 = 5105717) B5105717
theorem B2269207 : Blo 2267435 2269207 := bstep (se 1 (by rfl) ⟨1701905, by rfl⟩ : syracuseStep 2269207 = 3403811) B3403811
theorem B7976357 : Blo 2267435 7976357 := bbase (se 4 (by rfl) ⟨747783, by rfl⟩ : syracuseStep 7976357 = 1495567) (by norm_num)
theorem B5317571 : Blo 2267435 5317571 := bstep (se 1 (by rfl) ⟨3988178, by rfl⟩ : syracuseStep 5317571 = 7976357) B7976357
theorem B14180189 : Blo 2267435 14180189 := bstep (se 3 (by rfl) ⟨2658785, by rfl⟩ : syracuseStep 14180189 = 5317571) B5317571
theorem B37813837 : Blo 2267435 37813837 := bstep (se 3 (by rfl) ⟨7090094, by rfl⟩ : syracuseStep 37813837 = 14180189) B14180189
theorem B50418449 : Blo 2267435 50418449 := bstep (se 2 (by rfl) ⟨18906918, by rfl⟩ : syracuseStep 50418449 = 37813837) B37813837
theorem B33612299 : Blo 2267435 33612299 := bstep (se 1 (by rfl) ⟨25209224, by rfl⟩ : syracuseStep 33612299 = 50418449) B50418449
theorem B22408199 : Blo 2267435 22408199 := bstep (se 1 (by rfl) ⟨16806149, by rfl⟩ : syracuseStep 22408199 = 33612299) B33612299
theorem B14938799 : Blo 2267435 14938799 := bstep (se 1 (by rfl) ⟨11204099, by rfl⟩ : syracuseStep 14938799 = 22408199) B22408199
theorem B159347189 : Blo 2267435 159347189 := bstep (se 5 (by rfl) ⟨7469399, by rfl⟩ : syracuseStep 159347189 = 14938799) B14938799
theorem B106231459 : Blo 2267435 106231459 := bstep (se 1 (by rfl) ⟨79673594, by rfl⟩ : syracuseStep 106231459 = 159347189) B159347189
theorem B141641945 : Blo 2267435 141641945 := bstep (se 2 (by rfl) ⟨53115729, by rfl⟩ : syracuseStep 141641945 = 106231459) B106231459
theorem B94427963 : Blo 2267435 94427963 := bstep (se 1 (by rfl) ⟨70820972, by rfl⟩ : syracuseStep 94427963 = 141641945) B141641945
theorem B62951975 : Blo 2267435 62951975 := bstep (se 1 (by rfl) ⟨47213981, by rfl⟩ : syracuseStep 62951975 = 94427963) B94427963
theorem B41967983 : Blo 2267435 41967983 := bstep (se 1 (by rfl) ⟨31475987, by rfl⟩ : syracuseStep 41967983 = 62951975) B62951975
theorem B111914621 : Blo 2267435 111914621 := bstep (se 3 (by rfl) ⟨20983991, by rfl⟩ : syracuseStep 111914621 = 41967983) B41967983
theorem B74609747 : Blo 2267435 74609747 := bstep (se 1 (by rfl) ⟨55957310, by rfl⟩ : syracuseStep 74609747 = 111914621) B111914621
theorem B49739831 : Blo 2267435 49739831 := bstep (se 1 (by rfl) ⟨37304873, by rfl⟩ : syracuseStep 49739831 = 74609747) B74609747
theorem B33159887 : Blo 2267435 33159887 := bstep (se 1 (by rfl) ⟨24869915, by rfl⟩ : syracuseStep 33159887 = 49739831) B49739831
theorem B22106591 : Blo 2267435 22106591 := bstep (se 1 (by rfl) ⟨16579943, by rfl⟩ : syracuseStep 22106591 = 33159887) B33159887
theorem B14737727 : Blo 2267435 14737727 := bstep (se 1 (by rfl) ⟨11053295, by rfl⟩ : syracuseStep 14737727 = 22106591) B22106591
theorem B9825151 : Blo 2267435 9825151 := bstep (se 1 (by rfl) ⟨7368863, by rfl⟩ : syracuseStep 9825151 = 14737727) B14737727
theorem B13100201 : Blo 2267435 13100201 := bstep (se 2 (by rfl) ⟨4912575, by rfl⟩ : syracuseStep 13100201 = 9825151) B9825151
theorem B8733467 : Blo 2267435 8733467 := bstep (se 1 (by rfl) ⟨6550100, by rfl⟩ : syracuseStep 8733467 = 13100201) B13100201
theorem B23289245 : Blo 2267435 23289245 := bstep (se 3 (by rfl) ⟨4366733, by rfl⟩ : syracuseStep 23289245 = 8733467) B8733467
theorem B15526163 : Blo 2267435 15526163 := bstep (se 1 (by rfl) ⟨11644622, by rfl⟩ : syracuseStep 15526163 = 23289245) B23289245
theorem B10350775 : Blo 2267435 10350775 := bstep (se 1 (by rfl) ⟨7763081, by rfl⟩ : syracuseStep 10350775 = 15526163) B15526163
theorem B13801033 : Blo 2267435 13801033 := bstep (se 2 (by rfl) ⟨5175387, by rfl⟩ : syracuseStep 13801033 = 10350775) B10350775
theorem B18401377 : Blo 2267435 18401377 := bstep (se 2 (by rfl) ⟨6900516, by rfl⟩ : syracuseStep 18401377 = 13801033) B13801033
theorem B24535169 : Blo 2267435 24535169 := bstep (se 2 (by rfl) ⟨9200688, by rfl⟩ : syracuseStep 24535169 = 18401377) B18401377
theorem B16356779 : Blo 2267435 16356779 := bstep (se 1 (by rfl) ⟨12267584, by rfl⟩ : syracuseStep 16356779 = 24535169) B24535169
theorem B10904519 : Blo 2267435 10904519 := bstep (se 1 (by rfl) ⟨8178389, by rfl⟩ : syracuseStep 10904519 = 16356779) B16356779
theorem B7269679 : Blo 2267435 7269679 := bstep (se 1 (by rfl) ⟨5452259, by rfl⟩ : syracuseStep 7269679 = 10904519) B10904519
theorem B9692905 : Blo 2267435 9692905 := bstep (se 2 (by rfl) ⟨3634839, by rfl⟩ : syracuseStep 9692905 = 7269679) B7269679
theorem B12923873 : Blo 2267435 12923873 := bstep (se 2 (by rfl) ⟨4846452, by rfl⟩ : syracuseStep 12923873 = 9692905) B9692905
theorem B8615915 : Blo 2267435 8615915 := bstep (se 1 (by rfl) ⟨6461936, by rfl⟩ : syracuseStep 8615915 = 12923873) B12923873
theorem B5743943 : Blo 2267435 5743943 := bstep (se 1 (by rfl) ⟨4307957, by rfl⟩ : syracuseStep 5743943 = 8615915) B8615915
theorem B3829295 : Blo 2267435 3829295 := bstep (se 1 (by rfl) ⟨2871971, by rfl⟩ : syracuseStep 3829295 = 5743943) B5743943
theorem B2552863 : Blo 2267435 2552863 := bstep (se 1 (by rfl) ⟨1914647, by rfl⟩ : syracuseStep 2552863 = 3829295) B3829295
theorem B3403817 : Blo 2267435 3403817 := bstep (se 2 (by rfl) ⟨1276431, by rfl⟩ : syracuseStep 3403817 = 2552863) B2552863
theorem B2269211 : Blo 2267435 2269211 := bstep (se 1 (by rfl) ⟨1701908, by rfl⟩ : syracuseStep 2269211 = 3403817) B3403817
theorem B12267605 : Blo 2267435 12267605 := bbase (se 8 (by rfl) ⟨71880, by rfl⟩ : syracuseStep 12267605 = 143761) (by norm_num)
theorem B8178403 : Blo 2267435 8178403 := bstep (se 1 (by rfl) ⟨6133802, by rfl⟩ : syracuseStep 8178403 = 12267605) B12267605
theorem B10904537 : Blo 2267435 10904537 := bstep (se 2 (by rfl) ⟨4089201, by rfl⟩ : syracuseStep 10904537 = 8178403) B8178403
theorem B7269691 : Blo 2267435 7269691 := bstep (se 1 (by rfl) ⟨5452268, by rfl⟩ : syracuseStep 7269691 = 10904537) B10904537
theorem B9692921 : Blo 2267435 9692921 := bstep (se 2 (by rfl) ⟨3634845, by rfl⟩ : syracuseStep 9692921 = 7269691) B7269691
theorem B6461947 : Blo 2267435 6461947 := bstep (se 1 (by rfl) ⟨4846460, by rfl⟩ : syracuseStep 6461947 = 9692921) B9692921
theorem B8615929 : Blo 2267435 8615929 := bstep (se 2 (by rfl) ⟨3230973, by rfl⟩ : syracuseStep 8615929 = 6461947) B6461947
theorem B11487905 : Blo 2267435 11487905 := bstep (se 2 (by rfl) ⟨4307964, by rfl⟩ : syracuseStep 11487905 = 8615929) B8615929
theorem B7658603 : Blo 2267435 7658603 := bstep (se 1 (by rfl) ⟨5743952, by rfl⟩ : syracuseStep 7658603 = 11487905) B11487905
theorem B5105735 : Blo 2267435 5105735 := bstep (se 1 (by rfl) ⟨3829301, by rfl⟩ : syracuseStep 5105735 = 7658603) B7658603
theorem B3403823 : Blo 2267435 3403823 := bstep (se 1 (by rfl) ⟨2552867, by rfl⟩ : syracuseStep 3403823 = 5105735) B5105735
theorem B2269215 : Blo 2267435 2269215 := bstep (se 1 (by rfl) ⟨1701911, by rfl⟩ : syracuseStep 2269215 = 3403823) B3403823
theorem B3403829 : Blo 2267435 3403829 := bbase (se 5 (by rfl) ⟨159554, by rfl⟩ : syracuseStep 3403829 = 319109) (by norm_num)
theorem B2269219 : Blo 2267435 2269219 := bstep (se 1 (by rfl) ⟨1701914, by rfl⟩ : syracuseStep 2269219 = 3403829) B3403829
theorem B5743973 : Blo 2267435 5743973 := bbase (se 4 (by rfl) ⟨538497, by rfl⟩ : syracuseStep 5743973 = 1076995) (by norm_num)
theorem B3829315 : Blo 2267435 3829315 := bstep (se 1 (by rfl) ⟨2871986, by rfl⟩ : syracuseStep 3829315 = 5743973) B5743973
theorem B5105753 : Blo 2267435 5105753 := bstep (se 2 (by rfl) ⟨1914657, by rfl⟩ : syracuseStep 5105753 = 3829315) B3829315
theorem B3403835 : Blo 2267435 3403835 := bstep (se 1 (by rfl) ⟨2552876, by rfl⟩ : syracuseStep 3403835 = 5105753) B5105753
theorem B2269223 : Blo 2267435 2269223 := bstep (se 1 (by rfl) ⟨1701917, by rfl⟩ : syracuseStep 2269223 = 3403835) B3403835
theorem B2552881 : Blo 2267435 2552881 := bbase (se 2 (by rfl) ⟨957330, by rfl⟩ : syracuseStep 2552881 = 1914661) (by norm_num)
theorem B3403841 : Blo 2267435 3403841 := bstep (se 2 (by rfl) ⟨1276440, by rfl⟩ : syracuseStep 3403841 = 2552881) B2552881
theorem B2269227 : Blo 2267435 2269227 := bstep (se 1 (by rfl) ⟨1701920, by rfl⟩ : syracuseStep 2269227 = 3403841) B3403841
theorem B5186261 : Blo 2267435 5186261 := bbase (se 7 (by rfl) ⟨60776, by rfl⟩ : syracuseStep 5186261 = 121553) (by norm_num)
theorem B3457507 : Blo 2267435 3457507 := bstep (se 1 (by rfl) ⟨2593130, by rfl⟩ : syracuseStep 3457507 = 5186261) B5186261
theorem B4610009 : Blo 2267435 4610009 := bstep (se 2 (by rfl) ⟨1728753, by rfl⟩ : syracuseStep 4610009 = 3457507) B3457507
theorem B3073339 : Blo 2267435 3073339 := bstep (se 1 (by rfl) ⟨2305004, by rfl⟩ : syracuseStep 3073339 = 4610009) B4610009
theorem B4097785 : Blo 2267435 4097785 := bstep (se 2 (by rfl) ⟨1536669, by rfl⟩ : syracuseStep 4097785 = 3073339) B3073339
theorem B5463713 : Blo 2267435 5463713 := bstep (se 2 (by rfl) ⟨2048892, by rfl⟩ : syracuseStep 5463713 = 4097785) B4097785
theorem B14569901 : Blo 2267435 14569901 := bstep (se 3 (by rfl) ⟨2731856, by rfl⟩ : syracuseStep 14569901 = 5463713) B5463713
theorem B9713267 : Blo 2267435 9713267 := bstep (se 1 (by rfl) ⟨7284950, by rfl⟩ : syracuseStep 9713267 = 14569901) B14569901
theorem B6475511 : Blo 2267435 6475511 := bstep (se 1 (by rfl) ⟨4856633, by rfl⟩ : syracuseStep 6475511 = 9713267) B9713267
theorem B4317007 : Blo 2267435 4317007 := bstep (se 1 (by rfl) ⟨3237755, by rfl⟩ : syracuseStep 4317007 = 6475511) B6475511
theorem B5756009 : Blo 2267435 5756009 := bstep (se 2 (by rfl) ⟨2158503, by rfl⟩ : syracuseStep 5756009 = 4317007) B4317007
theorem B15349357 : Blo 2267435 15349357 := bstep (se 3 (by rfl) ⟨2878004, by rfl⟩ : syracuseStep 15349357 = 5756009) B5756009
theorem B81863237 : Blo 2267435 81863237 := bstep (se 4 (by rfl) ⟨7674678, by rfl⟩ : syracuseStep 81863237 = 15349357) B15349357
theorem B54575491 : Blo 2267435 54575491 := bstep (se 1 (by rfl) ⟨40931618, by rfl⟩ : syracuseStep 54575491 = 81863237) B81863237
theorem B72767321 : Blo 2267435 72767321 := bstep (se 2 (by rfl) ⟨27287745, by rfl⟩ : syracuseStep 72767321 = 54575491) B54575491
theorem B48511547 : Blo 2267435 48511547 := bstep (se 1 (by rfl) ⟨36383660, by rfl⟩ : syracuseStep 48511547 = 72767321) B72767321
theorem B32341031 : Blo 2267435 32341031 := bstep (se 1 (by rfl) ⟨24255773, by rfl⟩ : syracuseStep 32341031 = 48511547) B48511547
theorem B21560687 : Blo 2267435 21560687 := bstep (se 1 (by rfl) ⟨16170515, by rfl⟩ : syracuseStep 21560687 = 32341031) B32341031
theorem B14373791 : Blo 2267435 14373791 := bstep (se 1 (by rfl) ⟨10780343, by rfl⟩ : syracuseStep 14373791 = 21560687) B21560687
theorem B9582527 : Blo 2267435 9582527 := bstep (se 1 (by rfl) ⟨7186895, by rfl⟩ : syracuseStep 9582527 = 14373791) B14373791
theorem B6388351 : Blo 2267435 6388351 := bstep (se 1 (by rfl) ⟨4791263, by rfl⟩ : syracuseStep 6388351 = 9582527) B9582527
theorem B34071205 : Blo 2267435 34071205 := bstep (se 4 (by rfl) ⟨3194175, by rfl⟩ : syracuseStep 34071205 = 6388351) B6388351
theorem B45428273 : Blo 2267435 45428273 := bstep (se 2 (by rfl) ⟨17035602, by rfl⟩ : syracuseStep 45428273 = 34071205) B34071205
theorem B30285515 : Blo 2267435 30285515 := bstep (se 1 (by rfl) ⟨22714136, by rfl⟩ : syracuseStep 30285515 = 45428273) B45428273
theorem B20190343 : Blo 2267435 20190343 := bstep (se 1 (by rfl) ⟨15142757, by rfl⟩ : syracuseStep 20190343 = 30285515) B30285515
theorem B26920457 : Blo 2267435 26920457 := bstep (se 2 (by rfl) ⟨10095171, by rfl⟩ : syracuseStep 26920457 = 20190343) B20190343
theorem B17946971 : Blo 2267435 17946971 := bstep (se 1 (by rfl) ⟨13460228, by rfl⟩ : syracuseStep 17946971 = 26920457) B26920457
theorem B11964647 : Blo 2267435 11964647 := bstep (se 1 (by rfl) ⟨8973485, by rfl⟩ : syracuseStep 11964647 = 17946971) B17946971
theorem B7976431 : Blo 2267435 7976431 := bstep (se 1 (by rfl) ⟨5982323, by rfl⟩ : syracuseStep 7976431 = 11964647) B11964647
theorem B10635241 : Blo 2267435 10635241 := bstep (se 2 (by rfl) ⟨3988215, by rfl⟩ : syracuseStep 10635241 = 7976431) B7976431
theorem B14180321 : Blo 2267435 14180321 := bstep (se 2 (by rfl) ⟨5317620, by rfl⟩ : syracuseStep 14180321 = 10635241) B10635241
theorem B9453547 : Blo 2267435 9453547 := bstep (se 1 (by rfl) ⟨7090160, by rfl⟩ : syracuseStep 9453547 = 14180321) B14180321
theorem B12604729 : Blo 2267435 12604729 := bstep (se 2 (by rfl) ⟨4726773, by rfl⟩ : syracuseStep 12604729 = 9453547) B9453547
theorem B16806305 : Blo 2267435 16806305 := bstep (se 2 (by rfl) ⟨6302364, by rfl⟩ : syracuseStep 16806305 = 12604729) B12604729
theorem B11204203 : Blo 2267435 11204203 := bstep (se 1 (by rfl) ⟨8403152, by rfl⟩ : syracuseStep 11204203 = 16806305) B16806305
theorem B14938937 : Blo 2267435 14938937 := bstep (se 2 (by rfl) ⟨5602101, by rfl⟩ : syracuseStep 14938937 = 11204203) B11204203
theorem B9959291 : Blo 2267435 9959291 := bstep (se 1 (by rfl) ⟨7469468, by rfl⟩ : syracuseStep 9959291 = 14938937) B14938937
theorem B6639527 : Blo 2267435 6639527 := bstep (se 1 (by rfl) ⟨4979645, by rfl⟩ : syracuseStep 6639527 = 9959291) B9959291
theorem B17705405 : Blo 2267435 17705405 := bstep (se 3 (by rfl) ⟨3319763, by rfl⟩ : syracuseStep 17705405 = 6639527) B6639527
theorem B47214413 : Blo 2267435 47214413 := bstep (se 3 (by rfl) ⟨8852702, by rfl⟩ : syracuseStep 47214413 = 17705405) B17705405
theorem B31476275 : Blo 2267435 31476275 := bstep (se 1 (by rfl) ⟨23607206, by rfl⟩ : syracuseStep 31476275 = 47214413) B47214413
theorem B20984183 : Blo 2267435 20984183 := bstep (se 1 (by rfl) ⟨15738137, by rfl⟩ : syracuseStep 20984183 = 31476275) B31476275
theorem B13989455 : Blo 2267435 13989455 := bstep (se 1 (by rfl) ⟨10492091, by rfl⟩ : syracuseStep 13989455 = 20984183) B20984183
theorem B9326303 : Blo 2267435 9326303 := bstep (se 1 (by rfl) ⟨6994727, by rfl⟩ : syracuseStep 9326303 = 13989455) B13989455
theorem B6217535 : Blo 2267435 6217535 := bstep (se 1 (by rfl) ⟨4663151, by rfl⟩ : syracuseStep 6217535 = 9326303) B9326303
theorem B4145023 : Blo 2267435 4145023 := bstep (se 1 (by rfl) ⟨3108767, by rfl⟩ : syracuseStep 4145023 = 6217535) B6217535
theorem B22106789 : Blo 2267435 22106789 := bstep (se 4 (by rfl) ⟨2072511, by rfl⟩ : syracuseStep 22106789 = 4145023) B4145023
theorem B14737859 : Blo 2267435 14737859 := bstep (se 1 (by rfl) ⟨11053394, by rfl⟩ : syracuseStep 14737859 = 22106789) B22106789
theorem B9825239 : Blo 2267435 9825239 := bstep (se 1 (by rfl) ⟨7368929, by rfl⟩ : syracuseStep 9825239 = 14737859) B14737859
theorem B6550159 : Blo 2267435 6550159 := bstep (se 1 (by rfl) ⟨4912619, by rfl⟩ : syracuseStep 6550159 = 9825239) B9825239
theorem B8733545 : Blo 2267435 8733545 := bstep (se 2 (by rfl) ⟨3275079, by rfl⟩ : syracuseStep 8733545 = 6550159) B6550159
theorem B5822363 : Blo 2267435 5822363 := bstep (se 1 (by rfl) ⟨4366772, by rfl⟩ : syracuseStep 5822363 = 8733545) B8733545
theorem B3881575 : Blo 2267435 3881575 := bstep (se 1 (by rfl) ⟨2911181, by rfl⟩ : syracuseStep 3881575 = 5822363) B5822363
theorem B5175433 : Blo 2267435 5175433 := bstep (se 2 (by rfl) ⟨1940787, by rfl⟩ : syracuseStep 5175433 = 3881575) B3881575
theorem B27602309 : Blo 2267435 27602309 := bstep (se 4 (by rfl) ⟨2587716, by rfl⟩ : syracuseStep 27602309 = 5175433) B5175433
theorem B18401539 : Blo 2267435 18401539 := bstep (se 1 (by rfl) ⟨13801154, by rfl⟩ : syracuseStep 18401539 = 27602309) B27602309
theorem B24535385 : Blo 2267435 24535385 := bstep (se 2 (by rfl) ⟨9200769, by rfl⟩ : syracuseStep 24535385 = 18401539) B18401539
theorem B16356923 : Blo 2267435 16356923 := bstep (se 1 (by rfl) ⟨12267692, by rfl⟩ : syracuseStep 16356923 = 24535385) B24535385
theorem B10904615 : Blo 2267435 10904615 := bstep (se 1 (by rfl) ⟨8178461, by rfl⟩ : syracuseStep 10904615 = 16356923) B16356923
theorem B7269743 : Blo 2267435 7269743 := bstep (se 1 (by rfl) ⟨5452307, by rfl⟩ : syracuseStep 7269743 = 10904615) B10904615
theorem B4846495 : Blo 2267435 4846495 := bstep (se 1 (by rfl) ⟨3634871, by rfl⟩ : syracuseStep 4846495 = 7269743) B7269743
theorem B6461993 : Blo 2267435 6461993 := bstep (se 2 (by rfl) ⟨2423247, by rfl⟩ : syracuseStep 6461993 = 4846495) B4846495
theorem B4307995 : Blo 2267435 4307995 := bstep (se 1 (by rfl) ⟨3230996, by rfl⟩ : syracuseStep 4307995 = 6461993) B6461993
theorem B5743993 : Blo 2267435 5743993 := bstep (se 2 (by rfl) ⟨2153997, by rfl⟩ : syracuseStep 5743993 = 4307995) B4307995
theorem B7658657 : Blo 2267435 7658657 := bstep (se 2 (by rfl) ⟨2871996, by rfl⟩ : syracuseStep 7658657 = 5743993) B5743993
theorem B5105771 : Blo 2267435 5105771 := bstep (se 1 (by rfl) ⟨3829328, by rfl⟩ : syracuseStep 5105771 = 7658657) B7658657
theorem B3403847 : Blo 2267435 3403847 := bstep (se 1 (by rfl) ⟨2552885, by rfl⟩ : syracuseStep 3403847 = 5105771) B5105771
theorem B2269231 : Blo 2267435 2269231 := bstep (se 1 (by rfl) ⟨1701923, by rfl⟩ : syracuseStep 2269231 = 3403847) B3403847
theorem B3403853 : Blo 2267435 3403853 := bbase (se 3 (by rfl) ⟨638222, by rfl⟩ : syracuseStep 3403853 = 1276445) (by norm_num)
theorem B2269235 : Blo 2267435 2269235 := bstep (se 1 (by rfl) ⟨1701926, by rfl⟩ : syracuseStep 2269235 = 3403853) B3403853
theorem B5105789 : Blo 2267435 5105789 := bbase (se 3 (by rfl) ⟨957335, by rfl⟩ : syracuseStep 5105789 = 1914671) (by norm_num)
theorem B3403859 : Blo 2267435 3403859 := bstep (se 1 (by rfl) ⟨2552894, by rfl⟩ : syracuseStep 3403859 = 5105789) B5105789
theorem B2269239 : Blo 2267435 2269239 := bstep (se 1 (by rfl) ⟨1701929, by rfl⟩ : syracuseStep 2269239 = 3403859) B3403859
theorem B3829349 : Blo 2267435 3829349 := bbase (se 4 (by rfl) ⟨359001, by rfl⟩ : syracuseStep 3829349 = 718003) (by norm_num)
theorem B2552899 : Blo 2267435 2552899 := bstep (se 1 (by rfl) ⟨1914674, by rfl⟩ : syracuseStep 2552899 = 3829349) B3829349
theorem B3403865 : Blo 2267435 3403865 := bstep (se 2 (by rfl) ⟨1276449, by rfl⟩ : syracuseStep 3403865 = 2552899) B2552899
theorem B2269243 : Blo 2267435 2269243 := bstep (se 1 (by rfl) ⟨1701932, by rfl⟩ : syracuseStep 2269243 = 3403865) B3403865
theorem B2726173 : Blo 2267435 2726173 := bbase (se 3 (by rfl) ⟨511157, by rfl⟩ : syracuseStep 2726173 = 1022315) (by norm_num)
theorem B3634897 : Blo 2267435 3634897 := bstep (se 2 (by rfl) ⟨1363086, by rfl⟩ : syracuseStep 3634897 = 2726173) B2726173
theorem B4846529 : Blo 2267435 4846529 := bstep (se 2 (by rfl) ⟨1817448, by rfl⟩ : syracuseStep 4846529 = 3634897) B3634897
theorem B3231019 : Blo 2267435 3231019 := bstep (se 1 (by rfl) ⟨2423264, by rfl⟩ : syracuseStep 3231019 = 4846529) B4846529
theorem B17232101 : Blo 2267435 17232101 := bstep (se 4 (by rfl) ⟨1615509, by rfl⟩ : syracuseStep 17232101 = 3231019) B3231019
theorem B11488067 : Blo 2267435 11488067 := bstep (se 1 (by rfl) ⟨8616050, by rfl⟩ : syracuseStep 11488067 = 17232101) B17232101
theorem B7658711 : Blo 2267435 7658711 := bstep (se 1 (by rfl) ⟨5744033, by rfl⟩ : syracuseStep 7658711 = 11488067) B11488067
theorem B5105807 : Blo 2267435 5105807 := bstep (se 1 (by rfl) ⟨3829355, by rfl⟩ : syracuseStep 5105807 = 7658711) B7658711
theorem B3403871 : Blo 2267435 3403871 := bstep (se 1 (by rfl) ⟨2552903, by rfl⟩ : syracuseStep 3403871 = 5105807) B5105807
theorem B2269247 : Blo 2267435 2269247 := bstep (se 1 (by rfl) ⟨1701935, by rfl⟩ : syracuseStep 2269247 = 3403871) B3403871
theorem B3403877 : Blo 2267435 3403877 := bbase (se 4 (by rfl) ⟨319113, by rfl⟩ : syracuseStep 3403877 = 638227) (by norm_num)
theorem B2269251 : Blo 2267435 2269251 := bstep (se 1 (by rfl) ⟨1701938, by rfl⟩ : syracuseStep 2269251 = 3403877) B3403877
theorem B2587745 : Blo 2267435 2587745 := bbase (se 2 (by rfl) ⟨970404, by rfl⟩ : syracuseStep 2587745 = 1940809) (by norm_num)
theorem B6900653 : Blo 2267435 6900653 := bstep (se 3 (by rfl) ⟨1293872, by rfl⟩ : syracuseStep 6900653 = 2587745) B2587745
theorem B4600435 : Blo 2267435 4600435 := bstep (se 1 (by rfl) ⟨3450326, by rfl⟩ : syracuseStep 4600435 = 6900653) B6900653
theorem B6133913 : Blo 2267435 6133913 := bstep (se 2 (by rfl) ⟨2300217, by rfl⟩ : syracuseStep 6133913 = 4600435) B4600435
theorem B4089275 : Blo 2267435 4089275 := bstep (se 1 (by rfl) ⟨3066956, by rfl⟩ : syracuseStep 4089275 = 6133913) B6133913
theorem B2726183 : Blo 2267435 2726183 := bstep (se 1 (by rfl) ⟨2044637, by rfl⟩ : syracuseStep 2726183 = 4089275) B4089275
theorem B7269821 : Blo 2267435 7269821 := bstep (se 3 (by rfl) ⟨1363091, by rfl⟩ : syracuseStep 7269821 = 2726183) B2726183
theorem B4846547 : Blo 2267435 4846547 := bstep (se 1 (by rfl) ⟨3634910, by rfl⟩ : syracuseStep 4846547 = 7269821) B7269821
theorem B3231031 : Blo 2267435 3231031 := bstep (se 1 (by rfl) ⟨2423273, by rfl⟩ : syracuseStep 3231031 = 4846547) B4846547
theorem B4308041 : Blo 2267435 4308041 := bstep (se 2 (by rfl) ⟨1615515, by rfl⟩ : syracuseStep 4308041 = 3231031) B3231031
theorem B2872027 : Blo 2267435 2872027 := bstep (se 1 (by rfl) ⟨2154020, by rfl⟩ : syracuseStep 2872027 = 4308041) B4308041
theorem B3829369 : Blo 2267435 3829369 := bstep (se 2 (by rfl) ⟨1436013, by rfl⟩ : syracuseStep 3829369 = 2872027) B2872027
theorem B5105825 : Blo 2267435 5105825 := bstep (se 2 (by rfl) ⟨1914684, by rfl⟩ : syracuseStep 5105825 = 3829369) B3829369
theorem B3403883 : Blo 2267435 3403883 := bstep (se 1 (by rfl) ⟨2552912, by rfl⟩ : syracuseStep 3403883 = 5105825) B5105825
theorem B2269255 : Blo 2267435 2269255 := bstep (se 1 (by rfl) ⟨1701941, by rfl⟩ : syracuseStep 2269255 = 3403883) B3403883
theorem B2552917 : Blo 2267435 2552917 := bbase (se 8 (by rfl) ⟨14958, by rfl⟩ : syracuseStep 2552917 = 29917) (by norm_num)
theorem B3403889 : Blo 2267435 3403889 := bstep (se 2 (by rfl) ⟨1276458, by rfl⟩ : syracuseStep 3403889 = 2552917) B2552917
theorem B2269259 : Blo 2267435 2269259 := bstep (se 1 (by rfl) ⟨1701944, by rfl⟩ : syracuseStep 2269259 = 3403889) B3403889
theorem B2872037 : Blo 2267435 2872037 := bbase (se 4 (by rfl) ⟨269253, by rfl⟩ : syracuseStep 2872037 = 538507) (by norm_num)
theorem B7658765 : Blo 2267435 7658765 := bstep (se 3 (by rfl) ⟨1436018, by rfl⟩ : syracuseStep 7658765 = 2872037) B2872037
theorem B5105843 : Blo 2267435 5105843 := bstep (se 1 (by rfl) ⟨3829382, by rfl⟩ : syracuseStep 5105843 = 7658765) B7658765
theorem B3403895 : Blo 2267435 3403895 := bstep (se 1 (by rfl) ⟨2552921, by rfl⟩ : syracuseStep 3403895 = 5105843) B5105843
theorem B2269263 : Blo 2267435 2269263 := bstep (se 1 (by rfl) ⟨1701947, by rfl⟩ : syracuseStep 2269263 = 3403895) B3403895
theorem B3403901 : Blo 2267435 3403901 := bbase (se 3 (by rfl) ⟨638231, by rfl⟩ : syracuseStep 3403901 = 1276463) (by norm_num)
theorem B2269267 : Blo 2267435 2269267 := bstep (se 1 (by rfl) ⟨1701950, by rfl⟩ : syracuseStep 2269267 = 3403901) B3403901
theorem B5105861 : Blo 2267435 5105861 := bbase (se 4 (by rfl) ⟨478674, by rfl⟩ : syracuseStep 5105861 = 957349) (by norm_num)
theorem B3403907 : Blo 2267435 3403907 := bstep (se 1 (by rfl) ⟨2552930, by rfl⟩ : syracuseStep 3403907 = 5105861) B5105861
theorem B2269271 : Blo 2267435 2269271 := bstep (se 1 (by rfl) ⟨1701953, by rfl⟩ : syracuseStep 2269271 = 3403907) B3403907
theorem B2456357 : Blo 2267435 2456357 := bbase (se 4 (by rfl) ⟨230283, by rfl⟩ : syracuseStep 2456357 = 460567) (by norm_num)
theorem B26201141 : Blo 2267435 26201141 := bstep (se 5 (by rfl) ⟨1228178, by rfl⟩ : syracuseStep 26201141 = 2456357) B2456357
theorem B17467427 : Blo 2267435 17467427 := bstep (se 1 (by rfl) ⟨13100570, by rfl⟩ : syracuseStep 17467427 = 26201141) B26201141
theorem B46579805 : Blo 2267435 46579805 := bstep (se 3 (by rfl) ⟨8733713, by rfl⟩ : syracuseStep 46579805 = 17467427) B17467427
theorem B31053203 : Blo 2267435 31053203 := bstep (se 1 (by rfl) ⟨23289902, by rfl⟩ : syracuseStep 31053203 = 46579805) B46579805
theorem B20702135 : Blo 2267435 20702135 := bstep (se 1 (by rfl) ⟨15526601, by rfl⟩ : syracuseStep 20702135 = 31053203) B31053203
theorem B13801423 : Blo 2267435 13801423 := bstep (se 1 (by rfl) ⟨10351067, by rfl⟩ : syracuseStep 13801423 = 20702135) B20702135
theorem B18401897 : Blo 2267435 18401897 := bstep (se 2 (by rfl) ⟨6900711, by rfl⟩ : syracuseStep 18401897 = 13801423) B13801423
theorem B12267931 : Blo 2267435 12267931 := bstep (se 1 (by rfl) ⟨9200948, by rfl⟩ : syracuseStep 12267931 = 18401897) B18401897
theorem B16357241 : Blo 2267435 16357241 := bstep (se 2 (by rfl) ⟨6133965, by rfl⟩ : syracuseStep 16357241 = 12267931) B12267931
theorem B10904827 : Blo 2267435 10904827 := bstep (se 1 (by rfl) ⟨8178620, by rfl⟩ : syracuseStep 10904827 = 16357241) B16357241
theorem B14539769 : Blo 2267435 14539769 := bstep (se 2 (by rfl) ⟨5452413, by rfl⟩ : syracuseStep 14539769 = 10904827) B10904827
theorem B9693179 : Blo 2267435 9693179 := bstep (se 1 (by rfl) ⟨7269884, by rfl⟩ : syracuseStep 9693179 = 14539769) B14539769
theorem B6462119 : Blo 2267435 6462119 := bstep (se 1 (by rfl) ⟨4846589, by rfl⟩ : syracuseStep 6462119 = 9693179) B9693179
theorem B4308079 : Blo 2267435 4308079 := bstep (se 1 (by rfl) ⟨3231059, by rfl⟩ : syracuseStep 4308079 = 6462119) B6462119
theorem B5744105 : Blo 2267435 5744105 := bstep (se 2 (by rfl) ⟨2154039, by rfl⟩ : syracuseStep 5744105 = 4308079) B4308079
theorem B3829403 : Blo 2267435 3829403 := bstep (se 1 (by rfl) ⟨2872052, by rfl⟩ : syracuseStep 3829403 = 5744105) B5744105
theorem B2552935 : Blo 2267435 2552935 := bstep (se 1 (by rfl) ⟨1914701, by rfl⟩ : syracuseStep 2552935 = 3829403) B3829403
theorem B3403913 : Blo 2267435 3403913 := bstep (se 2 (by rfl) ⟨1276467, by rfl⟩ : syracuseStep 3403913 = 2552935) B2552935
theorem B2269275 : Blo 2267435 2269275 := bstep (se 1 (by rfl) ⟨1701956, by rfl⟩ : syracuseStep 2269275 = 3403913) B3403913
theorem B11488229 : Blo 2267435 11488229 := bbase (se 4 (by rfl) ⟨1077021, by rfl⟩ : syracuseStep 11488229 = 2154043) (by norm_num)
theorem B7658819 : Blo 2267435 7658819 := bstep (se 1 (by rfl) ⟨5744114, by rfl⟩ : syracuseStep 7658819 = 11488229) B11488229
theorem B5105879 : Blo 2267435 5105879 := bstep (se 1 (by rfl) ⟨3829409, by rfl⟩ : syracuseStep 5105879 = 7658819) B7658819
theorem B3403919 : Blo 2267435 3403919 := bstep (se 1 (by rfl) ⟨2552939, by rfl⟩ : syracuseStep 3403919 = 5105879) B5105879
theorem B2269279 : Blo 2267435 2269279 := bstep (se 1 (by rfl) ⟨1701959, by rfl⟩ : syracuseStep 2269279 = 3403919) B3403919
theorem B3403925 : Blo 2267435 3403925 := bbase (se 6 (by rfl) ⟨79779, by rfl⟩ : syracuseStep 3403925 = 159559) (by norm_num)
theorem B2269283 : Blo 2267435 2269283 := bstep (se 1 (by rfl) ⟨1701962, by rfl⟩ : syracuseStep 2269283 = 3403925) B3403925
theorem B2726221 : Blo 2267435 2726221 := bbase (se 3 (by rfl) ⟨511166, by rfl⟩ : syracuseStep 2726221 = 1022333) (by norm_num)
theorem B3634961 : Blo 2267435 3634961 := bstep (se 2 (by rfl) ⟨1363110, by rfl⟩ : syracuseStep 3634961 = 2726221) B2726221
theorem B9693229 : Blo 2267435 9693229 := bstep (se 3 (by rfl) ⟨1817480, by rfl⟩ : syracuseStep 9693229 = 3634961) B3634961
theorem B12924305 : Blo 2267435 12924305 := bstep (se 2 (by rfl) ⟨4846614, by rfl⟩ : syracuseStep 12924305 = 9693229) B9693229
theorem B8616203 : Blo 2267435 8616203 := bstep (se 1 (by rfl) ⟨6462152, by rfl⟩ : syracuseStep 8616203 = 12924305) B12924305
theorem B5744135 : Blo 2267435 5744135 := bstep (se 1 (by rfl) ⟨4308101, by rfl⟩ : syracuseStep 5744135 = 8616203) B8616203
theorem B3829423 : Blo 2267435 3829423 := bstep (se 1 (by rfl) ⟨2872067, by rfl⟩ : syracuseStep 3829423 = 5744135) B5744135
theorem B5105897 : Blo 2267435 5105897 := bstep (se 2 (by rfl) ⟨1914711, by rfl⟩ : syracuseStep 5105897 = 3829423) B3829423
theorem B3403931 : Blo 2267435 3403931 := bstep (se 1 (by rfl) ⟨2552948, by rfl⟩ : syracuseStep 3403931 = 5105897) B5105897
theorem B2269287 : Blo 2267435 2269287 := bstep (se 1 (by rfl) ⟨1701965, by rfl⟩ : syracuseStep 2269287 = 3403931) B3403931
theorem B2552953 : Blo 2267435 2552953 := bbase (se 2 (by rfl) ⟨957357, by rfl⟩ : syracuseStep 2552953 = 1914715) (by norm_num)
theorem B3403937 : Blo 2267435 3403937 := bstep (se 2 (by rfl) ⟨1276476, by rfl⟩ : syracuseStep 3403937 = 2552953) B2552953
theorem B2269291 : Blo 2267435 2269291 := bstep (se 1 (by rfl) ⟨1701968, by rfl⟩ : syracuseStep 2269291 = 3403937) B3403937
theorem B2300257 : Blo 2267435 2300257 := bbase (se 2 (by rfl) ⟨862596, by rfl⟩ : syracuseStep 2300257 = 1725193) (by norm_num)
theorem B12268037 : Blo 2267435 12268037 := bstep (se 4 (by rfl) ⟨1150128, by rfl⟩ : syracuseStep 12268037 = 2300257) B2300257
theorem B32714765 : Blo 2267435 32714765 := bstep (se 3 (by rfl) ⟨6134018, by rfl⟩ : syracuseStep 32714765 = 12268037) B12268037
theorem B21809843 : Blo 2267435 21809843 := bstep (se 1 (by rfl) ⟨16357382, by rfl⟩ : syracuseStep 21809843 = 32714765) B32714765
theorem B14539895 : Blo 2267435 14539895 := bstep (se 1 (by rfl) ⟨10904921, by rfl⟩ : syracuseStep 14539895 = 21809843) B21809843
theorem B9693263 : Blo 2267435 9693263 := bstep (se 1 (by rfl) ⟨7269947, by rfl⟩ : syracuseStep 9693263 = 14539895) B14539895
theorem B6462175 : Blo 2267435 6462175 := bstep (se 1 (by rfl) ⟨4846631, by rfl⟩ : syracuseStep 6462175 = 9693263) B9693263
theorem B8616233 : Blo 2267435 8616233 := bstep (se 2 (by rfl) ⟨3231087, by rfl⟩ : syracuseStep 8616233 = 6462175) B6462175
theorem B5744155 : Blo 2267435 5744155 := bstep (se 1 (by rfl) ⟨4308116, by rfl⟩ : syracuseStep 5744155 = 8616233) B8616233
theorem B7658873 : Blo 2267435 7658873 := bstep (se 2 (by rfl) ⟨2872077, by rfl⟩ : syracuseStep 7658873 = 5744155) B5744155
theorem B5105915 : Blo 2267435 5105915 := bstep (se 1 (by rfl) ⟨3829436, by rfl⟩ : syracuseStep 5105915 = 7658873) B7658873
theorem B3403943 : Blo 2267435 3403943 := bstep (se 1 (by rfl) ⟨2552957, by rfl⟩ : syracuseStep 3403943 = 5105915) B5105915
theorem B2269295 : Blo 2267435 2269295 := bstep (se 1 (by rfl) ⟨1701971, by rfl⟩ : syracuseStep 2269295 = 3403943) B3403943
theorem B3403949 : Blo 2267435 3403949 := bbase (se 3 (by rfl) ⟨638240, by rfl⟩ : syracuseStep 3403949 = 1276481) (by norm_num)
theorem B2269299 : Blo 2267435 2269299 := bstep (se 1 (by rfl) ⟨1701974, by rfl⟩ : syracuseStep 2269299 = 3403949) B3403949
theorem B5105933 : Blo 2267435 5105933 := bbase (se 3 (by rfl) ⟨957362, by rfl⟩ : syracuseStep 5105933 = 1914725) (by norm_num)
theorem B3403955 : Blo 2267435 3403955 := bstep (se 1 (by rfl) ⟨2552966, by rfl⟩ : syracuseStep 3403955 = 5105933) B5105933
theorem B2269303 : Blo 2267435 2269303 := bstep (se 1 (by rfl) ⟨1701977, by rfl⟩ : syracuseStep 2269303 = 3403955) B3403955
theorem B2872093 : Blo 2267435 2872093 := bbase (se 3 (by rfl) ⟨538517, by rfl⟩ : syracuseStep 2872093 = 1077035) (by norm_num)
theorem B3829457 : Blo 2267435 3829457 := bstep (se 2 (by rfl) ⟨1436046, by rfl⟩ : syracuseStep 3829457 = 2872093) B2872093
theorem B2552971 : Blo 2267435 2552971 := bstep (se 1 (by rfl) ⟨1914728, by rfl⟩ : syracuseStep 2552971 = 3829457) B3829457
theorem B3403961 : Blo 2267435 3403961 := bstep (se 2 (by rfl) ⟨1276485, by rfl⟩ : syracuseStep 3403961 = 2552971) B2552971
theorem B2269307 : Blo 2267435 2269307 := bstep (se 1 (by rfl) ⟨1701980, by rfl⟩ : syracuseStep 2269307 = 3403961) B3403961
theorem B6900821 : Blo 2267435 6900821 := bbase (se 8 (by rfl) ⟨40434, by rfl⟩ : syracuseStep 6900821 = 80869) (by norm_num)
theorem B4600547 : Blo 2267435 4600547 := bstep (se 1 (by rfl) ⟨3450410, by rfl⟩ : syracuseStep 4600547 = 6900821) B6900821
theorem B3067031 : Blo 2267435 3067031 := bstep (se 1 (by rfl) ⟨2300273, by rfl⟩ : syracuseStep 3067031 = 4600547) B4600547
theorem B8178749 : Blo 2267435 8178749 := bstep (se 3 (by rfl) ⟨1533515, by rfl⟩ : syracuseStep 8178749 = 3067031) B3067031
theorem B5452499 : Blo 2267435 5452499 := bstep (se 1 (by rfl) ⟨4089374, by rfl⟩ : syracuseStep 5452499 = 8178749) B8178749
theorem B3634999 : Blo 2267435 3634999 := bstep (se 1 (by rfl) ⟨2726249, by rfl⟩ : syracuseStep 3634999 = 5452499) B5452499
theorem B19386661 : Blo 2267435 19386661 := bstep (se 4 (by rfl) ⟨1817499, by rfl⟩ : syracuseStep 19386661 = 3634999) B3634999
theorem B25848881 : Blo 2267435 25848881 := bstep (se 2 (by rfl) ⟨9693330, by rfl⟩ : syracuseStep 25848881 = 19386661) B19386661
theorem B17232587 : Blo 2267435 17232587 := bstep (se 1 (by rfl) ⟨12924440, by rfl⟩ : syracuseStep 17232587 = 25848881) B25848881
theorem B11488391 : Blo 2267435 11488391 := bstep (se 1 (by rfl) ⟨8616293, by rfl⟩ : syracuseStep 11488391 = 17232587) B17232587
theorem B7658927 : Blo 2267435 7658927 := bstep (se 1 (by rfl) ⟨5744195, by rfl⟩ : syracuseStep 7658927 = 11488391) B11488391
theorem B5105951 : Blo 2267435 5105951 := bstep (se 1 (by rfl) ⟨3829463, by rfl⟩ : syracuseStep 5105951 = 7658927) B7658927
theorem B3403967 : Blo 2267435 3403967 := bstep (se 1 (by rfl) ⟨2552975, by rfl⟩ : syracuseStep 3403967 = 5105951) B5105951
theorem B2269311 : Blo 2267435 2269311 := bstep (se 1 (by rfl) ⟨1701983, by rfl⟩ : syracuseStep 2269311 = 3403967) B3403967
theorem B3403973 : Blo 2267435 3403973 := bbase (se 4 (by rfl) ⟨319122, by rfl⟩ : syracuseStep 3403973 = 638245) (by norm_num)
theorem B2269315 : Blo 2267435 2269315 := bstep (se 1 (by rfl) ⟨1701986, by rfl⟩ : syracuseStep 2269315 = 3403973) B3403973
theorem B3829477 : Blo 2267435 3829477 := bbase (se 4 (by rfl) ⟨359013, by rfl⟩ : syracuseStep 3829477 = 718027) (by norm_num)
theorem B5105969 : Blo 2267435 5105969 := bstep (se 2 (by rfl) ⟨1914738, by rfl⟩ : syracuseStep 5105969 = 3829477) B3829477
theorem B3403979 : Blo 2267435 3403979 := bstep (se 1 (by rfl) ⟨2552984, by rfl⟩ : syracuseStep 3403979 = 5105969) B5105969
theorem B2269319 : Blo 2267435 2269319 := bstep (se 1 (by rfl) ⟨1701989, by rfl⟩ : syracuseStep 2269319 = 3403979) B3403979
theorem B2552989 : Blo 2267435 2552989 := bbase (se 3 (by rfl) ⟨478685, by rfl⟩ : syracuseStep 2552989 = 957371) (by norm_num)
theorem B3403985 : Blo 2267435 3403985 := bstep (se 2 (by rfl) ⟨1276494, by rfl⟩ : syracuseStep 3403985 = 2552989) B2552989
theorem B2269323 : Blo 2267435 2269323 := bstep (se 1 (by rfl) ⟨1701992, by rfl⟩ : syracuseStep 2269323 = 3403985) B3403985
theorem B7658981 : Blo 2267435 7658981 := bbase (se 4 (by rfl) ⟨718029, by rfl⟩ : syracuseStep 7658981 = 1436059) (by norm_num)
theorem B5105987 : Blo 2267435 5105987 := bstep (se 1 (by rfl) ⟨3829490, by rfl⟩ : syracuseStep 5105987 = 7658981) B7658981
theorem B3403991 : Blo 2267435 3403991 := bstep (se 1 (by rfl) ⟨2552993, by rfl⟩ : syracuseStep 3403991 = 5105987) B5105987
theorem B2269327 : Blo 2267435 2269327 := bstep (se 1 (by rfl) ⟨1701995, by rfl⟩ : syracuseStep 2269327 = 3403991) B3403991
theorem B3403997 : Blo 2267435 3403997 := bbase (se 3 (by rfl) ⟨638249, by rfl⟩ : syracuseStep 3403997 = 1276499) (by norm_num)
theorem B2269331 : Blo 2267435 2269331 := bstep (se 1 (by rfl) ⟨1701998, by rfl⟩ : syracuseStep 2269331 = 3403997) B3403997
theorem B5106005 : Blo 2267435 5106005 := bbase (se 10 (by rfl) ⟨7479, by rfl⟩ : syracuseStep 5106005 = 14959) (by norm_num)
theorem B3404003 : Blo 2267435 3404003 := bstep (se 1 (by rfl) ⟨2553002, by rfl⟩ : syracuseStep 3404003 = 5106005) B5106005
theorem B2269335 : Blo 2267435 2269335 := bstep (se 1 (by rfl) ⟨1702001, by rfl⟩ : syracuseStep 2269335 = 3404003) B3404003
theorem B3635045 : Blo 2267435 3635045 := bbase (se 4 (by rfl) ⟨340785, by rfl⟩ : syracuseStep 3635045 = 681571) (by norm_num)
theorem B2423363 : Blo 2267435 2423363 := bstep (se 1 (by rfl) ⟨1817522, by rfl⟩ : syracuseStep 2423363 = 3635045) B3635045
theorem B6462301 : Blo 2267435 6462301 := bstep (se 3 (by rfl) ⟨1211681, by rfl⟩ : syracuseStep 6462301 = 2423363) B2423363
theorem B8616401 : Blo 2267435 8616401 := bstep (se 2 (by rfl) ⟨3231150, by rfl⟩ : syracuseStep 8616401 = 6462301) B6462301
theorem B5744267 : Blo 2267435 5744267 := bstep (se 1 (by rfl) ⟨4308200, by rfl⟩ : syracuseStep 5744267 = 8616401) B8616401
theorem B3829511 : Blo 2267435 3829511 := bstep (se 1 (by rfl) ⟨2872133, by rfl⟩ : syracuseStep 3829511 = 5744267) B5744267
theorem B2553007 : Blo 2267435 2553007 := bstep (se 1 (by rfl) ⟨1914755, by rfl⟩ : syracuseStep 2553007 = 3829511) B3829511
theorem B3404009 : Blo 2267435 3404009 := bstep (se 2 (by rfl) ⟨1276503, by rfl⟩ : syracuseStep 3404009 = 2553007) B2553007
theorem B2269339 : Blo 2267435 2269339 := bstep (se 1 (by rfl) ⟨1702004, by rfl⟩ : syracuseStep 2269339 = 3404009) B3404009
theorem B8733973 : Blo 2267435 8733973 := bbase (se 6 (by rfl) ⟨204702, by rfl⟩ : syracuseStep 8733973 = 409405) (by norm_num)
theorem B11645297 : Blo 2267435 11645297 := bstep (se 2 (by rfl) ⟨4366986, by rfl⟩ : syracuseStep 11645297 = 8733973) B8733973
theorem B7763531 : Blo 2267435 7763531 := bstep (se 1 (by rfl) ⟨5822648, by rfl⟩ : syracuseStep 7763531 = 11645297) B11645297
theorem B82810997 : Blo 2267435 82810997 := bstep (se 5 (by rfl) ⟨3881765, by rfl⟩ : syracuseStep 82810997 = 7763531) B7763531
theorem B55207331 : Blo 2267435 55207331 := bstep (se 1 (by rfl) ⟨41405498, by rfl⟩ : syracuseStep 55207331 = 82810997) B82810997
theorem B36804887 : Blo 2267435 36804887 := bstep (se 1 (by rfl) ⟨27603665, by rfl⟩ : syracuseStep 36804887 = 55207331) B55207331
theorem B24536591 : Blo 2267435 24536591 := bstep (se 1 (by rfl) ⟨18402443, by rfl⟩ : syracuseStep 24536591 = 36804887) B36804887
theorem B16357727 : Blo 2267435 16357727 := bstep (se 1 (by rfl) ⟨12268295, by rfl⟩ : syracuseStep 16357727 = 24536591) B24536591
theorem B43620605 : Blo 2267435 43620605 := bstep (se 3 (by rfl) ⟨8178863, by rfl⟩ : syracuseStep 43620605 = 16357727) B16357727
theorem B29080403 : Blo 2267435 29080403 := bstep (se 1 (by rfl) ⟨21810302, by rfl⟩ : syracuseStep 29080403 = 43620605) B43620605
theorem B19386935 : Blo 2267435 19386935 := bstep (se 1 (by rfl) ⟨14540201, by rfl⟩ : syracuseStep 19386935 = 29080403) B29080403
theorem B12924623 : Blo 2267435 12924623 := bstep (se 1 (by rfl) ⟨9693467, by rfl⟩ : syracuseStep 12924623 = 19386935) B19386935
theorem B8616415 : Blo 2267435 8616415 := bstep (se 1 (by rfl) ⟨6462311, by rfl⟩ : syracuseStep 8616415 = 12924623) B12924623
theorem B11488553 : Blo 2267435 11488553 := bstep (se 2 (by rfl) ⟨4308207, by rfl⟩ : syracuseStep 11488553 = 8616415) B8616415
theorem B7659035 : Blo 2267435 7659035 := bstep (se 1 (by rfl) ⟨5744276, by rfl⟩ : syracuseStep 7659035 = 11488553) B11488553
theorem B5106023 : Blo 2267435 5106023 := bstep (se 1 (by rfl) ⟨3829517, by rfl⟩ : syracuseStep 5106023 = 7659035) B7659035
theorem B3404015 : Blo 2267435 3404015 := bstep (se 1 (by rfl) ⟨2553011, by rfl⟩ : syracuseStep 3404015 = 5106023) B5106023
theorem B2269343 : Blo 2267435 2269343 := bstep (se 1 (by rfl) ⟨1702007, by rfl⟩ : syracuseStep 2269343 = 3404015) B3404015
theorem B3404021 : Blo 2267435 3404021 := bbase (se 5 (by rfl) ⟨159563, by rfl⟩ : syracuseStep 3404021 = 319127) (by norm_num)
theorem B2269347 : Blo 2267435 2269347 := bstep (se 1 (by rfl) ⟨1702010, by rfl⟩ : syracuseStep 2269347 = 3404021) B3404021
theorem B24871445 : Blo 2267435 24871445 := bbase (se 6 (by rfl) ⟨582924, by rfl⟩ : syracuseStep 24871445 = 1165849) (by norm_num)
theorem B16580963 : Blo 2267435 16580963 := bstep (se 1 (by rfl) ⟨12435722, by rfl⟩ : syracuseStep 16580963 = 24871445) B24871445
theorem B44215901 : Blo 2267435 44215901 := bstep (se 3 (by rfl) ⟨8290481, by rfl⟩ : syracuseStep 44215901 = 16580963) B16580963
theorem B29477267 : Blo 2267435 29477267 := bstep (se 1 (by rfl) ⟨22107950, by rfl⟩ : syracuseStep 29477267 = 44215901) B44215901
theorem B19651511 : Blo 2267435 19651511 := bstep (se 1 (by rfl) ⟨14738633, by rfl⟩ : syracuseStep 19651511 = 29477267) B29477267
theorem B52404029 : Blo 2267435 52404029 := bstep (se 3 (by rfl) ⟨9825755, by rfl⟩ : syracuseStep 52404029 = 19651511) B19651511
theorem B34936019 : Blo 2267435 34936019 := bstep (se 1 (by rfl) ⟨26202014, by rfl⟩ : syracuseStep 34936019 = 52404029) B52404029
theorem B23290679 : Blo 2267435 23290679 := bstep (se 1 (by rfl) ⟨17468009, by rfl⟩ : syracuseStep 23290679 = 34936019) B34936019
theorem B62108477 : Blo 2267435 62108477 := bstep (se 3 (by rfl) ⟨11645339, by rfl⟩ : syracuseStep 62108477 = 23290679) B23290679
theorem B41405651 : Blo 2267435 41405651 := bstep (se 1 (by rfl) ⟨31054238, by rfl⟩ : syracuseStep 41405651 = 62108477) B62108477
theorem B27603767 : Blo 2267435 27603767 := bstep (se 1 (by rfl) ⟨20702825, by rfl⟩ : syracuseStep 27603767 = 41405651) B41405651
theorem B73610045 : Blo 2267435 73610045 := bstep (se 3 (by rfl) ⟨13801883, by rfl⟩ : syracuseStep 73610045 = 27603767) B27603767
theorem B49073363 : Blo 2267435 49073363 := bstep (se 1 (by rfl) ⟨36805022, by rfl⟩ : syracuseStep 49073363 = 73610045) B73610045
theorem B32715575 : Blo 2267435 32715575 := bstep (se 1 (by rfl) ⟨24536681, by rfl⟩ : syracuseStep 32715575 = 49073363) B49073363
theorem B21810383 : Blo 2267435 21810383 := bstep (se 1 (by rfl) ⟨16357787, by rfl⟩ : syracuseStep 21810383 = 32715575) B32715575
theorem B14540255 : Blo 2267435 14540255 := bstep (se 1 (by rfl) ⟨10905191, by rfl⟩ : syracuseStep 14540255 = 21810383) B21810383
theorem B9693503 : Blo 2267435 9693503 := bstep (se 1 (by rfl) ⟨7270127, by rfl⟩ : syracuseStep 9693503 = 14540255) B14540255
theorem B6462335 : Blo 2267435 6462335 := bstep (se 1 (by rfl) ⟨4846751, by rfl⟩ : syracuseStep 6462335 = 9693503) B9693503
theorem B4308223 : Blo 2267435 4308223 := bstep (se 1 (by rfl) ⟨3231167, by rfl⟩ : syracuseStep 4308223 = 6462335) B6462335
theorem B5744297 : Blo 2267435 5744297 := bstep (se 2 (by rfl) ⟨2154111, by rfl⟩ : syracuseStep 5744297 = 4308223) B4308223
theorem B3829531 : Blo 2267435 3829531 := bstep (se 1 (by rfl) ⟨2872148, by rfl⟩ : syracuseStep 3829531 = 5744297) B5744297
theorem B5106041 : Blo 2267435 5106041 := bstep (se 2 (by rfl) ⟨1914765, by rfl⟩ : syracuseStep 5106041 = 3829531) B3829531
theorem B3404027 : Blo 2267435 3404027 := bstep (se 1 (by rfl) ⟨2553020, by rfl⟩ : syracuseStep 3404027 = 5106041) B5106041
theorem B2269351 : Blo 2267435 2269351 := bstep (se 1 (by rfl) ⟨1702013, by rfl⟩ : syracuseStep 2269351 = 3404027) B3404027
theorem B2553025 : Blo 2267435 2553025 := bbase (se 2 (by rfl) ⟨957384, by rfl⟩ : syracuseStep 2553025 = 1914769) (by norm_num)
theorem B3404033 : Blo 2267435 3404033 := bstep (se 2 (by rfl) ⟨1276512, by rfl⟩ : syracuseStep 3404033 = 2553025) B2553025
theorem B2269355 : Blo 2267435 2269355 := bstep (se 1 (by rfl) ⟨1702016, by rfl⟩ : syracuseStep 2269355 = 3404033) B3404033
theorem B5744317 : Blo 2267435 5744317 := bbase (se 3 (by rfl) ⟨1077059, by rfl⟩ : syracuseStep 5744317 = 2154119) (by norm_num)
theorem B7659089 : Blo 2267435 7659089 := bstep (se 2 (by rfl) ⟨2872158, by rfl⟩ : syracuseStep 7659089 = 5744317) B5744317
theorem B5106059 : Blo 2267435 5106059 := bstep (se 1 (by rfl) ⟨3829544, by rfl⟩ : syracuseStep 5106059 = 7659089) B7659089
theorem B3404039 : Blo 2267435 3404039 := bstep (se 1 (by rfl) ⟨2553029, by rfl⟩ : syracuseStep 3404039 = 5106059) B5106059
theorem B2269359 : Blo 2267435 2269359 := bstep (se 1 (by rfl) ⟨1702019, by rfl⟩ : syracuseStep 2269359 = 3404039) B3404039
theorem B3404045 : Blo 2267435 3404045 := bbase (se 3 (by rfl) ⟨638258, by rfl⟩ : syracuseStep 3404045 = 1276517) (by norm_num)
theorem B2269363 : Blo 2267435 2269363 := bstep (se 1 (by rfl) ⟨1702022, by rfl⟩ : syracuseStep 2269363 = 3404045) B3404045
theorem B5106077 : Blo 2267435 5106077 := bbase (se 3 (by rfl) ⟨957389, by rfl⟩ : syracuseStep 5106077 = 1914779) (by norm_num)
theorem B3404051 : Blo 2267435 3404051 := bstep (se 1 (by rfl) ⟨2553038, by rfl⟩ : syracuseStep 3404051 = 5106077) B5106077
theorem B2269367 : Blo 2267435 2269367 := bstep (se 1 (by rfl) ⟨1702025, by rfl⟩ : syracuseStep 2269367 = 3404051) B3404051
theorem B3829565 : Blo 2267435 3829565 := bbase (se 3 (by rfl) ⟨718043, by rfl⟩ : syracuseStep 3829565 = 1436087) (by norm_num)
theorem B2553043 : Blo 2267435 2553043 := bstep (se 1 (by rfl) ⟨1914782, by rfl⟩ : syracuseStep 2553043 = 3829565) B3829565
theorem B3404057 : Blo 2267435 3404057 := bstep (se 2 (by rfl) ⟨1276521, by rfl⟩ : syracuseStep 3404057 = 2553043) B2553043
theorem B2269371 : Blo 2267435 2269371 := bstep (se 1 (by rfl) ⟨1702028, by rfl⟩ : syracuseStep 2269371 = 3404057) B3404057
theorem B2423401 : Blo 2267435 2423401 := bbase (se 2 (by rfl) ⟨908775, by rfl⟩ : syracuseStep 2423401 = 1817551) (by norm_num)
theorem B12924805 : Blo 2267435 12924805 := bstep (se 4 (by rfl) ⟨1211700, by rfl⟩ : syracuseStep 12924805 = 2423401) B2423401
theorem B17233073 : Blo 2267435 17233073 := bstep (se 2 (by rfl) ⟨6462402, by rfl⟩ : syracuseStep 17233073 = 12924805) B12924805
theorem B11488715 : Blo 2267435 11488715 := bstep (se 1 (by rfl) ⟨8616536, by rfl⟩ : syracuseStep 11488715 = 17233073) B17233073
theorem B7659143 : Blo 2267435 7659143 := bstep (se 1 (by rfl) ⟨5744357, by rfl⟩ : syracuseStep 7659143 = 11488715) B11488715
theorem B5106095 : Blo 2267435 5106095 := bstep (se 1 (by rfl) ⟨3829571, by rfl⟩ : syracuseStep 5106095 = 7659143) B7659143
theorem B3404063 : Blo 2267435 3404063 := bstep (se 1 (by rfl) ⟨2553047, by rfl⟩ : syracuseStep 3404063 = 5106095) B5106095
theorem B2269375 : Blo 2267435 2269375 := bstep (se 1 (by rfl) ⟨1702031, by rfl⟩ : syracuseStep 2269375 = 3404063) B3404063
theorem B3404069 : Blo 2267435 3404069 := bbase (se 4 (by rfl) ⟨319131, by rfl⟩ : syracuseStep 3404069 = 638263) (by norm_num)
theorem B2269379 : Blo 2267435 2269379 := bstep (se 1 (by rfl) ⟨1702034, by rfl⟩ : syracuseStep 2269379 = 3404069) B3404069
theorem B2872189 : Blo 2267435 2872189 := bbase (se 3 (by rfl) ⟨538535, by rfl⟩ : syracuseStep 2872189 = 1077071) (by norm_num)
theorem B3829585 : Blo 2267435 3829585 := bstep (se 2 (by rfl) ⟨1436094, by rfl⟩ : syracuseStep 3829585 = 2872189) B2872189
theorem B5106113 : Blo 2267435 5106113 := bstep (se 2 (by rfl) ⟨1914792, by rfl⟩ : syracuseStep 5106113 = 3829585) B3829585
theorem B3404075 : Blo 2267435 3404075 := bstep (se 1 (by rfl) ⟨2553056, by rfl⟩ : syracuseStep 3404075 = 5106113) B5106113
theorem B2269383 : Blo 2267435 2269383 := bstep (se 1 (by rfl) ⟨1702037, by rfl⟩ : syracuseStep 2269383 = 3404075) B3404075
theorem B2553061 : Blo 2267435 2553061 := bbase (se 4 (by rfl) ⟨239349, by rfl⟩ : syracuseStep 2553061 = 478699) (by norm_num)
theorem B3404081 : Blo 2267435 3404081 := bstep (se 2 (by rfl) ⟨1276530, by rfl⟩ : syracuseStep 3404081 = 2553061) B2553061
theorem B2269387 : Blo 2267435 2269387 := bstep (se 1 (by rfl) ⟨1702040, by rfl⟩ : syracuseStep 2269387 = 3404081) B3404081
theorem B4846837 : Blo 2267435 4846837 := bbase (se 5 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 4846837 = 454391) (by norm_num)
theorem B6462449 : Blo 2267435 6462449 := bstep (se 2 (by rfl) ⟨2423418, by rfl⟩ : syracuseStep 6462449 = 4846837) B4846837
theorem B4308299 : Blo 2267435 4308299 := bstep (se 1 (by rfl) ⟨3231224, by rfl⟩ : syracuseStep 4308299 = 6462449) B6462449
theorem B2872199 : Blo 2267435 2872199 := bstep (se 1 (by rfl) ⟨2154149, by rfl⟩ : syracuseStep 2872199 = 4308299) B4308299
theorem B7659197 : Blo 2267435 7659197 := bstep (se 3 (by rfl) ⟨1436099, by rfl⟩ : syracuseStep 7659197 = 2872199) B2872199
theorem B5106131 : Blo 2267435 5106131 := bstep (se 1 (by rfl) ⟨3829598, by rfl⟩ : syracuseStep 5106131 = 7659197) B7659197
theorem B3404087 : Blo 2267435 3404087 := bstep (se 1 (by rfl) ⟨2553065, by rfl⟩ : syracuseStep 3404087 = 5106131) B5106131
theorem B2269391 : Blo 2267435 2269391 := bstep (se 1 (by rfl) ⟨1702043, by rfl⟩ : syracuseStep 2269391 = 3404087) B3404087
theorem B3404093 : Blo 2267435 3404093 := bbase (se 3 (by rfl) ⟨638267, by rfl⟩ : syracuseStep 3404093 = 1276535) (by norm_num)
theorem B2269395 : Blo 2267435 2269395 := bstep (se 1 (by rfl) ⟨1702046, by rfl⟩ : syracuseStep 2269395 = 3404093) B3404093
theorem B5106149 : Blo 2267435 5106149 := bbase (se 4 (by rfl) ⟨478701, by rfl⟩ : syracuseStep 5106149 = 957403) (by norm_num)
theorem B3404099 : Blo 2267435 3404099 := bstep (se 1 (by rfl) ⟨2553074, by rfl⟩ : syracuseStep 3404099 = 5106149) B5106149
theorem B2269399 : Blo 2267435 2269399 := bstep (se 1 (by rfl) ⟨1702049, by rfl⟩ : syracuseStep 2269399 = 3404099) B3404099
theorem B5744429 : Blo 2267435 5744429 := bbase (se 3 (by rfl) ⟨1077080, by rfl⟩ : syracuseStep 5744429 = 2154161) (by norm_num)
theorem B3829619 : Blo 2267435 3829619 := bstep (se 1 (by rfl) ⟨2872214, by rfl⟩ : syracuseStep 3829619 = 5744429) B5744429
theorem B2553079 : Blo 2267435 2553079 := bstep (se 1 (by rfl) ⟨1914809, by rfl⟩ : syracuseStep 2553079 = 3829619) B3829619
theorem B3404105 : Blo 2267435 3404105 := bstep (se 2 (by rfl) ⟨1276539, by rfl⟩ : syracuseStep 3404105 = 2553079) B2553079
theorem B2269403 : Blo 2267435 2269403 := bstep (se 1 (by rfl) ⟨1702052, by rfl⟩ : syracuseStep 2269403 = 3404105) B3404105
theorem B10905461 : Blo 2267435 10905461 := bbase (se 5 (by rfl) ⟨511193, by rfl⟩ : syracuseStep 10905461 = 1022387) (by norm_num)
theorem B7270307 : Blo 2267435 7270307 := bstep (se 1 (by rfl) ⟨5452730, by rfl⟩ : syracuseStep 7270307 = 10905461) B10905461
theorem B4846871 : Blo 2267435 4846871 := bstep (se 1 (by rfl) ⟨3635153, by rfl⟩ : syracuseStep 4846871 = 7270307) B7270307
theorem B3231247 : Blo 2267435 3231247 := bstep (se 1 (by rfl) ⟨2423435, by rfl⟩ : syracuseStep 3231247 = 4846871) B4846871
theorem B4308329 : Blo 2267435 4308329 := bstep (se 2 (by rfl) ⟨1615623, by rfl⟩ : syracuseStep 4308329 = 3231247) B3231247
theorem B11488877 : Blo 2267435 11488877 := bstep (se 3 (by rfl) ⟨2154164, by rfl⟩ : syracuseStep 11488877 = 4308329) B4308329
theorem B7659251 : Blo 2267435 7659251 := bstep (se 1 (by rfl) ⟨5744438, by rfl⟩ : syracuseStep 7659251 = 11488877) B11488877
theorem B5106167 : Blo 2267435 5106167 := bstep (se 1 (by rfl) ⟨3829625, by rfl⟩ : syracuseStep 5106167 = 7659251) B7659251
theorem B3404111 : Blo 2267435 3404111 := bstep (se 1 (by rfl) ⟨2553083, by rfl⟩ : syracuseStep 3404111 = 5106167) B5106167
theorem B2269407 : Blo 2267435 2269407 := bstep (se 1 (by rfl) ⟨1702055, by rfl⟩ : syracuseStep 2269407 = 3404111) B3404111
theorem B3404117 : Blo 2267435 3404117 := bbase (se 10 (by rfl) ⟨4986, by rfl⟩ : syracuseStep 3404117 = 9973) (by norm_num)
theorem B2269411 : Blo 2267435 2269411 := bstep (se 1 (by rfl) ⟨1702058, by rfl⟩ : syracuseStep 2269411 = 3404117) B3404117
theorem B6462517 : Blo 2267435 6462517 := bbase (se 5 (by rfl) ⟨302930, by rfl⟩ : syracuseStep 6462517 = 605861) (by norm_num)
theorem B8616689 : Blo 2267435 8616689 := bstep (se 2 (by rfl) ⟨3231258, by rfl⟩ : syracuseStep 8616689 = 6462517) B6462517
theorem B5744459 : Blo 2267435 5744459 := bstep (se 1 (by rfl) ⟨4308344, by rfl⟩ : syracuseStep 5744459 = 8616689) B8616689
theorem B3829639 : Blo 2267435 3829639 := bstep (se 1 (by rfl) ⟨2872229, by rfl⟩ : syracuseStep 3829639 = 5744459) B5744459
theorem B5106185 : Blo 2267435 5106185 := bstep (se 2 (by rfl) ⟨1914819, by rfl⟩ : syracuseStep 5106185 = 3829639) B3829639
theorem B3404123 : Blo 2267435 3404123 := bstep (se 1 (by rfl) ⟨2553092, by rfl⟩ : syracuseStep 3404123 = 5106185) B5106185
theorem B2269415 : Blo 2267435 2269415 := bstep (se 1 (by rfl) ⟨1702061, by rfl⟩ : syracuseStep 2269415 = 3404123) B3404123
theorem B2553097 : Blo 2267435 2553097 := bbase (se 2 (by rfl) ⟨957411, by rfl⟩ : syracuseStep 2553097 = 1914823) (by norm_num)
theorem B3404129 : Blo 2267435 3404129 := bstep (se 2 (by rfl) ⟨1276548, by rfl⟩ : syracuseStep 3404129 = 2553097) B2553097
theorem B2269419 : Blo 2267435 2269419 := bstep (se 1 (by rfl) ⟨1702064, by rfl⟩ : syracuseStep 2269419 = 3404129) B3404129
theorem B29081429 : Blo 2267435 29081429 := bbase (se 9 (by rfl) ⟨85199, by rfl⟩ : syracuseStep 29081429 = 170399) (by norm_num)
theorem B19387619 : Blo 2267435 19387619 := bstep (se 1 (by rfl) ⟨14540714, by rfl⟩ : syracuseStep 19387619 = 29081429) B29081429
theorem B12925079 : Blo 2267435 12925079 := bstep (se 1 (by rfl) ⟨9693809, by rfl⟩ : syracuseStep 12925079 = 19387619) B19387619
theorem B8616719 : Blo 2267435 8616719 := bstep (se 1 (by rfl) ⟨6462539, by rfl⟩ : syracuseStep 8616719 = 12925079) B12925079
theorem B5744479 : Blo 2267435 5744479 := bstep (se 1 (by rfl) ⟨4308359, by rfl⟩ : syracuseStep 5744479 = 8616719) B8616719
theorem B7659305 : Blo 2267435 7659305 := bstep (se 2 (by rfl) ⟨2872239, by rfl⟩ : syracuseStep 7659305 = 5744479) B5744479
theorem B5106203 : Blo 2267435 5106203 := bstep (se 1 (by rfl) ⟨3829652, by rfl⟩ : syracuseStep 5106203 = 7659305) B7659305
theorem B3404135 : Blo 2267435 3404135 := bstep (se 1 (by rfl) ⟨2553101, by rfl⟩ : syracuseStep 3404135 = 5106203) B5106203
theorem B2269423 : Blo 2267435 2269423 := bstep (se 1 (by rfl) ⟨1702067, by rfl⟩ : syracuseStep 2269423 = 3404135) B3404135
theorem B3404141 : Blo 2267435 3404141 := bbase (se 3 (by rfl) ⟨638276, by rfl⟩ : syracuseStep 3404141 = 1276553) (by norm_num)
theorem B2269427 : Blo 2267435 2269427 := bstep (se 1 (by rfl) ⟨1702070, by rfl⟩ : syracuseStep 2269427 = 3404141) B3404141
theorem B5106221 : Blo 2267435 5106221 := bbase (se 3 (by rfl) ⟨957416, by rfl⟩ : syracuseStep 5106221 = 1914833) (by norm_num)
theorem B3404147 : Blo 2267435 3404147 := bstep (se 1 (by rfl) ⟨2553110, by rfl⟩ : syracuseStep 3404147 = 5106221) B5106221
theorem B2269431 : Blo 2267435 2269431 := bstep (se 1 (by rfl) ⟨1702073, by rfl⟩ : syracuseStep 2269431 = 3404147) B3404147
theorem B2331785 : Blo 2267435 2331785 := bbase (se 2 (by rfl) ⟨874419, by rfl⟩ : syracuseStep 2331785 = 1748839) (by norm_num)
theorem B6218093 : Blo 2267435 6218093 := bstep (se 3 (by rfl) ⟨1165892, by rfl⟩ : syracuseStep 6218093 = 2331785) B2331785
theorem B16581581 : Blo 2267435 16581581 := bstep (se 3 (by rfl) ⟨3109046, by rfl⟩ : syracuseStep 16581581 = 6218093) B6218093
theorem B11054387 : Blo 2267435 11054387 := bstep (se 1 (by rfl) ⟨8290790, by rfl⟩ : syracuseStep 11054387 = 16581581) B16581581
theorem B7369591 : Blo 2267435 7369591 := bstep (se 1 (by rfl) ⟨5527193, by rfl⟩ : syracuseStep 7369591 = 11054387) B11054387
theorem B9826121 : Blo 2267435 9826121 := bstep (se 2 (by rfl) ⟨3684795, by rfl⟩ : syracuseStep 9826121 = 7369591) B7369591
theorem B26202989 : Blo 2267435 26202989 := bstep (se 3 (by rfl) ⟨4913060, by rfl⟩ : syracuseStep 26202989 = 9826121) B9826121
theorem B17468659 : Blo 2267435 17468659 := bstep (se 1 (by rfl) ⟨13101494, by rfl⟩ : syracuseStep 17468659 = 26202989) B26202989
theorem B23291545 : Blo 2267435 23291545 := bstep (se 2 (by rfl) ⟨8734329, by rfl⟩ : syracuseStep 23291545 = 17468659) B17468659
theorem B31055393 : Blo 2267435 31055393 := bstep (se 2 (by rfl) ⟨11645772, by rfl⟩ : syracuseStep 31055393 = 23291545) B23291545
theorem B20703595 : Blo 2267435 20703595 := bstep (se 1 (by rfl) ⟨15527696, by rfl⟩ : syracuseStep 20703595 = 31055393) B31055393
theorem B27604793 : Blo 2267435 27604793 := bstep (se 2 (by rfl) ⟨10351797, by rfl⟩ : syracuseStep 27604793 = 20703595) B20703595
theorem B18403195 : Blo 2267435 18403195 := bstep (se 1 (by rfl) ⟨13802396, by rfl⟩ : syracuseStep 18403195 = 27604793) B27604793
theorem B24537593 : Blo 2267435 24537593 := bstep (se 2 (by rfl) ⟨9201597, by rfl⟩ : syracuseStep 24537593 = 18403195) B18403195
theorem B16358395 : Blo 2267435 16358395 := bstep (se 1 (by rfl) ⟨12268796, by rfl⟩ : syracuseStep 16358395 = 24537593) B24537593
theorem B21811193 : Blo 2267435 21811193 := bstep (se 2 (by rfl) ⟨8179197, by rfl⟩ : syracuseStep 21811193 = 16358395) B16358395
theorem B14540795 : Blo 2267435 14540795 := bstep (se 1 (by rfl) ⟨10905596, by rfl⟩ : syracuseStep 14540795 = 21811193) B21811193
theorem B9693863 : Blo 2267435 9693863 := bstep (se 1 (by rfl) ⟨7270397, by rfl⟩ : syracuseStep 9693863 = 14540795) B14540795
theorem B6462575 : Blo 2267435 6462575 := bstep (se 1 (by rfl) ⟨4846931, by rfl⟩ : syracuseStep 6462575 = 9693863) B9693863
theorem B4308383 : Blo 2267435 4308383 := bstep (se 1 (by rfl) ⟨3231287, by rfl⟩ : syracuseStep 4308383 = 6462575) B6462575
theorem B2872255 : Blo 2267435 2872255 := bstep (se 1 (by rfl) ⟨2154191, by rfl⟩ : syracuseStep 2872255 = 4308383) B4308383
theorem B3829673 : Blo 2267435 3829673 := bstep (se 2 (by rfl) ⟨1436127, by rfl⟩ : syracuseStep 3829673 = 2872255) B2872255
theorem B2553115 : Blo 2267435 2553115 := bstep (se 1 (by rfl) ⟨1914836, by rfl⟩ : syracuseStep 2553115 = 3829673) B3829673
theorem B3404153 : Blo 2267435 3404153 := bstep (se 2 (by rfl) ⟨1276557, by rfl⟩ : syracuseStep 3404153 = 2553115) B2553115
theorem B2269435 : Blo 2267435 2269435 := bstep (se 1 (by rfl) ⟨1702076, by rfl⟩ : syracuseStep 2269435 = 3404153) B3404153
theorem C0 (j : ℕ) (h1 : 566858 ≤ j) (h2 : j ≤ 567358) : Blo 2267435 (4 * j + 3) := by
  interval_cases j
  · exact B2267435
  · exact B2267439
  · exact B2267443
  · exact B2267447
  · exact B2267451
  · exact B2267455
  · exact B2267459
  · exact B2267463
  · exact B2267467
  · exact B2267471
  · exact B2267475
  · exact B2267479
  · exact B2267483
  · exact B2267487
  · exact B2267491
  · exact B2267495
  · exact B2267499
  · exact B2267503
  · exact B2267507
  · exact B2267511
  · exact B2267515
  · exact B2267519
  · exact B2267523
  · exact B2267527
  · exact B2267531
  · exact B2267535
  · exact B2267539
  · exact B2267543
  · exact B2267547
  · exact B2267551
  · exact B2267555
  · exact B2267559
  · exact B2267563
  · exact B2267567
  · exact B2267571
  · exact B2267575
  · exact B2267579
  · exact B2267583
  · exact B2267587
  · exact B2267591
  · exact B2267595
  · exact B2267599
  · exact B2267603
  · exact B2267607
  · exact B2267611
  · exact B2267615
  · exact B2267619
  · exact B2267623
  · exact B2267627
  · exact B2267631
  · exact B2267635
  · exact B2267639
  · exact B2267643
  · exact B2267647
  · exact B2267651
  · exact B2267655
  · exact B2267659
  · exact B2267663
  · exact B2267667
  · exact B2267671
  · exact B2267675
  · exact B2267679
  · exact B2267683
  · exact B2267687
  · exact B2267691
  · exact B2267695
  · exact B2267699
  · exact B2267703
  · exact B2267707
  · exact B2267711
  · exact B2267715
  · exact B2267719
  · exact B2267723
  · exact B2267727
  · exact B2267731
  · exact B2267735
  · exact B2267739
  · exact B2267743
  · exact B2267747
  · exact B2267751
  · exact B2267755
  · exact B2267759
  · exact B2267763
  · exact B2267767
  · exact B2267771
  · exact B2267775
  · exact B2267779
  · exact B2267783
  · exact B2267787
  · exact B2267791
  · exact B2267795
  · exact B2267799
  · exact B2267803
  · exact B2267807
  · exact B2267811
  · exact B2267815
  · exact B2267819
  · exact B2267823
  · exact B2267827
  · exact B2267831
  · exact B2267835
  · exact B2267839
  · exact B2267843
  · exact B2267847
  · exact B2267851
  · exact B2267855
  · exact B2267859
  · exact B2267863
  · exact B2267867
  · exact B2267871
  · exact B2267875
  · exact B2267879
  · exact B2267883
  · exact B2267887
  · exact B2267891
  · exact B2267895
  · exact B2267899
  · exact B2267903
  · exact B2267907
  · exact B2267911
  · exact B2267915
  · exact B2267919
  · exact B2267923
  · exact B2267927
  · exact B2267931
  · exact B2267935
  · exact B2267939
  · exact B2267943
  · exact B2267947
  · exact B2267951
  · exact B2267955
  · exact B2267959
  · exact B2267963
  · exact B2267967
  · exact B2267971
  · exact B2267975
  · exact B2267979
  · exact B2267983
  · exact B2267987
  · exact B2267991
  · exact B2267995
  · exact B2267999
  · exact B2268003
  · exact B2268007
  · exact B2268011
  · exact B2268015
  · exact B2268019
  · exact B2268023
  · exact B2268027
  · exact B2268031
  · exact B2268035
  · exact B2268039
  · exact B2268043
  · exact B2268047
  · exact B2268051
  · exact B2268055
  · exact B2268059
  · exact B2268063
  · exact B2268067
  · exact B2268071
  · exact B2268075
  · exact B2268079
  · exact B2268083
  · exact B2268087
  · exact B2268091
  · exact B2268095
  · exact B2268099
  · exact B2268103
  · exact B2268107
  · exact B2268111
  · exact B2268115
  · exact B2268119
  · exact B2268123
  · exact B2268127
  · exact B2268131
  · exact B2268135
  · exact B2268139
  · exact B2268143
  · exact B2268147
  · exact B2268151
  · exact B2268155
  · exact B2268159
  · exact B2268163
  · exact B2268167
  · exact B2268171
  · exact B2268175
  · exact B2268179
  · exact B2268183
  · exact B2268187
  · exact B2268191
  · exact B2268195
  · exact B2268199
  · exact B2268203
  · exact B2268207
  · exact B2268211
  · exact B2268215
  · exact B2268219
  · exact B2268223
  · exact B2268227
  · exact B2268231
  · exact B2268235
  · exact B2268239
  · exact B2268243
  · exact B2268247
  · exact B2268251
  · exact B2268255
  · exact B2268259
  · exact B2268263
  · exact B2268267
  · exact B2268271
  · exact B2268275
  · exact B2268279
  · exact B2268283
  · exact B2268287
  · exact B2268291
  · exact B2268295
  · exact B2268299
  · exact B2268303
  · exact B2268307
  · exact B2268311
  · exact B2268315
  · exact B2268319
  · exact B2268323
  · exact B2268327
  · exact B2268331
  · exact B2268335
  · exact B2268339
  · exact B2268343
  · exact B2268347
  · exact B2268351
  · exact B2268355
  · exact B2268359
  · exact B2268363
  · exact B2268367
  · exact B2268371
  · exact B2268375
  · exact B2268379
  · exact B2268383
  · exact B2268387
  · exact B2268391
  · exact B2268395
  · exact B2268399
  · exact B2268403
  · exact B2268407
  · exact B2268411
  · exact B2268415
  · exact B2268419
  · exact B2268423
  · exact B2268427
  · exact B2268431
  · exact B2268435
  · exact B2268439
  · exact B2268443
  · exact B2268447
  · exact B2268451
  · exact B2268455
  · exact B2268459
  · exact B2268463
  · exact B2268467
  · exact B2268471
  · exact B2268475
  · exact B2268479
  · exact B2268483
  · exact B2268487
  · exact B2268491
  · exact B2268495
  · exact B2268499
  · exact B2268503
  · exact B2268507
  · exact B2268511
  · exact B2268515
  · exact B2268519
  · exact B2268523
  · exact B2268527
  · exact B2268531
  · exact B2268535
  · exact B2268539
  · exact B2268543
  · exact B2268547
  · exact B2268551
  · exact B2268555
  · exact B2268559
  · exact B2268563
  · exact B2268567
  · exact B2268571
  · exact B2268575
  · exact B2268579
  · exact B2268583
  · exact B2268587
  · exact B2268591
  · exact B2268595
  · exact B2268599
  · exact B2268603
  · exact B2268607
  · exact B2268611
  · exact B2268615
  · exact B2268619
  · exact B2268623
  · exact B2268627
  · exact B2268631
  · exact B2268635
  · exact B2268639
  · exact B2268643
  · exact B2268647
  · exact B2268651
  · exact B2268655
  · exact B2268659
  · exact B2268663
  · exact B2268667
  · exact B2268671
  · exact B2268675
  · exact B2268679
  · exact B2268683
  · exact B2268687
  · exact B2268691
  · exact B2268695
  · exact B2268699
  · exact B2268703
  · exact B2268707
  · exact B2268711
  · exact B2268715
  · exact B2268719
  · exact B2268723
  · exact B2268727
  · exact B2268731
  · exact B2268735
  · exact B2268739
  · exact B2268743
  · exact B2268747
  · exact B2268751
  · exact B2268755
  · exact B2268759
  · exact B2268763
  · exact B2268767
  · exact B2268771
  · exact B2268775
  · exact B2268779
  · exact B2268783
  · exact B2268787
  · exact B2268791
  · exact B2268795
  · exact B2268799
  · exact B2268803
  · exact B2268807
  · exact B2268811
  · exact B2268815
  · exact B2268819
  · exact B2268823
  · exact B2268827
  · exact B2268831
  · exact B2268835
  · exact B2268839
  · exact B2268843
  · exact B2268847
  · exact B2268851
  · exact B2268855
  · exact B2268859
  · exact B2268863
  · exact B2268867
  · exact B2268871
  · exact B2268875
  · exact B2268879
  · exact B2268883
  · exact B2268887
  · exact B2268891
  · exact B2268895
  · exact B2268899
  · exact B2268903
  · exact B2268907
  · exact B2268911
  · exact B2268915
  · exact B2268919
  · exact B2268923
  · exact B2268927
  · exact B2268931
  · exact B2268935
  · exact B2268939
  · exact B2268943
  · exact B2268947
  · exact B2268951
  · exact B2268955
  · exact B2268959
  · exact B2268963
  · exact B2268967
  · exact B2268971
  · exact B2268975
  · exact B2268979
  · exact B2268983
  · exact B2268987
  · exact B2268991
  · exact B2268995
  · exact B2268999
  · exact B2269003
  · exact B2269007
  · exact B2269011
  · exact B2269015
  · exact B2269019
  · exact B2269023
  · exact B2269027
  · exact B2269031
  · exact B2269035
  · exact B2269039
  · exact B2269043
  · exact B2269047
  · exact B2269051
  · exact B2269055
  · exact B2269059
  · exact B2269063
  · exact B2269067
  · exact B2269071
  · exact B2269075
  · exact B2269079
  · exact B2269083
  · exact B2269087
  · exact B2269091
  · exact B2269095
  · exact B2269099
  · exact B2269103
  · exact B2269107
  · exact B2269111
  · exact B2269115
  · exact B2269119
  · exact B2269123
  · exact B2269127
  · exact B2269131
  · exact B2269135
  · exact B2269139
  · exact B2269143
  · exact B2269147
  · exact B2269151
  · exact B2269155
  · exact B2269159
  · exact B2269163
  · exact B2269167
  · exact B2269171
  · exact B2269175
  · exact B2269179
  · exact B2269183
  · exact B2269187
  · exact B2269191
  · exact B2269195
  · exact B2269199
  · exact B2269203
  · exact B2269207
  · exact B2269211
  · exact B2269215
  · exact B2269219
  · exact B2269223
  · exact B2269227
  · exact B2269231
  · exact B2269235
  · exact B2269239
  · exact B2269243
  · exact B2269247
  · exact B2269251
  · exact B2269255
  · exact B2269259
  · exact B2269263
  · exact B2269267
  · exact B2269271
  · exact B2269275
  · exact B2269279
  · exact B2269283
  · exact B2269287
  · exact B2269291
  · exact B2269295
  · exact B2269299
  · exact B2269303
  · exact B2269307
  · exact B2269311
  · exact B2269315
  · exact B2269319
  · exact B2269323
  · exact B2269327
  · exact B2269331
  · exact B2269335
  · exact B2269339
  · exact B2269343
  · exact B2269347
  · exact B2269351
  · exact B2269355
  · exact B2269359
  · exact B2269363
  · exact B2269367
  · exact B2269371
  · exact B2269375
  · exact B2269379
  · exact B2269383
  · exact B2269387
  · exact B2269391
  · exact B2269395
  · exact B2269399
  · exact B2269403
  · exact B2269407
  · exact B2269411
  · exact B2269415
  · exact B2269419
  · exact B2269423
  · exact B2269427
  · exact B2269431
  · exact B2269435
theorem solution (m : ℕ) (hlo : 2267435 ≤ m) (hhi : m ≤ 2269435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 566858 ≤ j := by omega
    have hj2 : j ≤ 567358 := by omega
    have hb : Blo 2267435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
